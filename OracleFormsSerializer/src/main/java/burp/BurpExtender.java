package burp;

import java.awt.Component;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Base64;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.regex.Pattern;
import java.util.regex.PatternSyntaxException;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.io.PrintWriter;
import java.nio.*;
import java.io.*;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;

import oracle.forms.engine.FormsDispatcher;
import oracle.forms.engine.FormsMessage;
import oracle.forms.engine.Message;

public class BurpExtender implements IBurpExtender, IMessageEditorTabFactory, IScannerInsertionPointProvider, IHttpListener
{
    private PrintWriter stdout;
    private IBurpExtenderCallbacks callbacks;
    private IExtensionHelpers helpers;
    private byte[] clientKey=null;
    private byte[] serverKey=null;
    private byte[] rc4Key=new byte[5];
    private int[] reqSeedBuf=null;
    private int[] reqIndexVars=null;
    private int[] respSeedBuf=null;
    private int[] respIndexVars=null;
    private static String[] as=new String[256];

    // Automatic match/replace state.
    private final CopyOnWriteArrayList<MatchReplaceRule> mrRules=new CopyOnWriteArrayList<MatchReplaceRule>();
    private volatile boolean matchReplaceEnabled=false;
    private static final String MR_RULES_SETTING="oracle_forms_mr_rules";
    private static final String MR_ENABLED_SETTING="oracle_forms_mr_enabled";

    // Global boolean policy for requests (responses cannot be re-serialised).
    // Applies to every Boolean property in the message tree. Independent of the
    // match/replace rule table, but gated by the master enable switch along with
    // the rest of the engine; the dropdown's "Leave unchanged" is its own off state.
    private static final int BOOL_NONE=0, BOOL_FLIP=1, BOOL_TRUE=2, BOOL_FALSE=3;
    private static final String[] BOOL_MODE_LABELS={
        "Leave unchanged", "Flip all (true<->false)", "Set all to true", "Set all to false"};
    private volatile int boolRequestMode=BOOL_NONE;
    private static final String BOOL_MODE_SETTING="oracle_forms_bool_mode";

    // Extension options.
    private volatile boolean debugEnabled=false;
    private static final String DEBUG_SETTING="oracle_forms_debug";
    private volatile boolean frmHighlightEnabled=true;
    private static final String FRM_HIGHLIGHT_SETTING="oracle_forms_frm_highlight";
    private static final Pattern FRM_ERROR_PATTERN=Pattern.compile("(?:FRM|ORA)-\\d+");

    // Scope for the modifying transforms (match/replace + boolean policy). The
    // FRM/ORA highlight is read-only recon and is NOT gated by this.
    private static final int SCOPE_ALL=0, SCOPE_SUITE=1, SCOPE_CUSTOM=2;
    private static final String[] SCOPE_MODE_LABELS={
        "All Forms traffic (ignore scope)", "Burp Target scope only", "Custom URL regex"};
    private volatile int scopeMode=SCOPE_ALL;
    private volatile String scopeCustomRegex="";
    private volatile Pattern scopeCustomPattern=null; // compiled cache of scopeCustomRegex
    private static final String SCOPE_MODE_SETTING="oracle_forms_scope_mode";
    private static final String SCOPE_REGEX_SETTING="oracle_forms_scope_regex";

    // Verbose trace output; silenced unless the user enables debug in the tab.
    private void debug(String s){
        if (debugEnabled){
            stdout.println(s);
        }
    }

    @Override
    public void registerExtenderCallbacks(IBurpExtenderCallbacks callbacks)
    {   
        // keep a reference to our callbacks object
        this.callbacks = callbacks;
        helpers = callbacks.getHelpers();
        
        stdout = new PrintWriter(callbacks.getStdout(), true);
        stdout.println("Oracle Forms Serializer loaded");
        
        // set our extension name
        callbacks.setExtensionName("Oracle Forms Serializer");
        
        //callbacks.registerProxyListener(this);
        callbacks.registerMessageEditorTabFactory(this);
        callbacks.registerMessageEditorTabFactory(new OracleFormsTreeTabFactory()); // structured tree view (editable on editable surfaces)
        callbacks.registerScannerInsertionPointProvider(this);
        callbacks.registerHttpListener(this);

        // Automatic match/replace: restore persisted rules and add the config tab.
        loadMatchReplaceSettings();
        callbacks.addSuiteTab(new OracleFormsMatchReplaceTab());
    }
    
    public boolean gotKey(){
        return this.clientKey!=null && this.serverKey!=null;
    }
    
    public static String byteArrayToHex(byte[] a) {
        StringBuilder sb = new StringBuilder(a.length * 2);
        for(byte b: a)
            sb.append(String.format("%02x", b & 0xff));
        return sb.toString();
    }

    // Decode a validated even-length hex string to bytes (inverse of
    // byteArrayToHex). Callers must validate/strip the input first.
    static byte[] hexToBytes(String hex){
        int n=hex.length()/2;
        byte[] out=new byte[n];
        for (int i=0;i<n;i++){
            out[i]=(byte)Integer.parseInt(hex.substring(2*i, 2*i+2), 16);
        }
        return out;
    }

    private String messageToString(Message m){
        StringBuilder ret=new StringBuilder();
        /*if (m.isDeltaMessage()){
            ret.append("Delta message, Delta Index: "+m.getDeltaIndex()+"\n");    
        }*/
        
        for (int i=0;i<m.size();i++){
            ret.append("Property "+i+": "+m.getPropertyAt(i)+" Type: "+m.getPropertyTypeAt(i)+"\n");
            if (m.getValueAt(i)==null){
                ret.append("--- Value: null\n");
            }else{
                ret.append("--- Value: "+ m.getValueAt(i).toString()+"\n");
                if (m.getValueAt(i) instanceof Message){
                    ret.append(">>> Begin recursive print\n");
                    ret.append(messageToString((Message)m.getValueAt(i)));
                    ret.append("\n<<< End recursive print\n");
                }
            }
        }
        return ret.toString();
    }

    // Message.readDetails() leaves string-table back-references as
    // oracle.forms.engine.IndexTag placeholders instead of resolving them to
    // String objects. Message.writeDetails() cannot serialise an IndexTag and
    // throws "Attempt to write out an object of type oracle.forms.engine.IndexTag".
    // Responses (unlike short requests) are full of these references, including
    // inside nested Messages, so before re-serialising we walk the whole tree
    // and replace every IndexTag with the concrete string it resolves to
    // (IndexTag.toString() yields that string, which is why the read-only dump
    // shows correct values). The single shared FormsDispatcher then rebuilds
    // proper back-references on the way out.
    private int resolveIndexTags(Message m){
        int resolved=0;
        for (int i=0;i<m.size();i++){
            Object v=m.getValueAt(i);
            if (v==null){
                continue;
            }
            if (v instanceof Message){
                resolved+=resolveIndexTags((Message)v); // nested message
            }else if ("oracle.forms.engine.IndexTag".equals(v.getClass().getName())){
                m.setValueAt(i, v.toString());
                resolved++;
            }
        }
        return resolved;
    }

    // On-the-wire bytes of a String literal in the Forms stream: a 2-byte
    // big-endian length followed by the modified-UTF-8 bytes, exactly as
    // DataOutput.writeUTF() (readDetails reads them with readUTF, which is why
    // plain string literals already round-trip for requests). We use this to
    // find and replace a literal in the raw body without re-serialising.
    static byte[] utfBytes(String s) throws IOException {
        ByteArrayOutputStream b=new ByteArrayOutputStream();
        DataOutputStream d=new DataOutputStream(b);
        d.writeUTF(s);
        d.flush();
        return b.toByteArray();
    }

    // First index of needle in haystack at or after `from`, or -1.
    static int indexOf(byte[] haystack, byte[] needle, int from){
        if (needle.length==0 || needle.length>haystack.length){
            return -1;
        }
        outer:
        for (int i=Math.max(from,0); i<=haystack.length-needle.length; i++){
            for (int j=0;j<needle.length;j++){
                if (haystack[i+j]!=needle[j]){
                    continue outer;
                }
            }
            return i;
        }
        return -1;
    }

    // Recursively collect every editable String (type 1) and Integer (type 3)
    // leaf under `m`, keyed by its full path so values nested inside other
    // Message objects are addressable too: e.g. string_49_3_2 means message 49
    // -> property 3 (a nested Message) -> property 2 (a String). `prefix` is the
    // accumulated "_<index>" path of the parents, starting as "_<messageId>" at
    // the top level. Keys stay backward compatible: a top-level string at
    // message 12 property 5 is still string_12_5.
    private void collectStrings(Message m, String prefix,
                               java.util.Map<String,String> strings,
                               java.util.Map<String,Integer> ints,
                               java.util.Map<String,Boolean> bools){
        for (int i=0;i<m.size();i++){
            Object v=m.getValueAt(i);
            if (v==null){
                continue;
            }
            if (v instanceof Message){
                collectStrings((Message)v, prefix+"_"+i, strings, ints, bools); // descend into nested Message
            }else if (v instanceof Boolean){
                // Detect by value type, not the numeric property-type code:
                // the value round-trips through writeDetails as a Boolean.
                bools.put("bool"+prefix+"_"+i, (Boolean)v);
            }else if (m.getPropertyTypeAt(i)==1){
                strings.put("string"+prefix+"_"+i, v.toString());
            }else if (m.getPropertyTypeAt(i)==3){
                try{
                    ints.put("int"+prefix+"_"+i, Integer.valueOf(v.toString()));
                }catch(NumberFormatException nfe){}
            }
        }
    }

    // Mirror of collectStrings for the write side: walk the same message tree
    // with the same key scheme and push edited values back onto it via
    // setValueAt, descending into nested Messages. Only values the user
    // actually changed are written, to avoid needless re-encoding.
    private void applyEdits(Message m, String prefix,
                           java.util.Map<String,String> paramStrings,
                           java.util.Map<String,Integer> paramInts,
                           java.util.Map<String,Boolean> paramBools, PrintWriter stdout){
        for (int i=0;i<m.size();i++){
            Object v=m.getValueAt(i);
            if (v instanceof Message){
                applyEdits((Message)v, prefix+"_"+i, paramStrings, paramInts, paramBools, stdout); // descend into nested Message
            }else if (v instanceof Boolean){
                String key="bool"+prefix+"_"+i;
                if (paramBools.containsKey(key)){
                    Boolean newVal=paramBools.get(key);
                    if (!newVal.equals(v)){
                        debug("[+] Setting Boolean value for "+key+" -> "+newVal);
                        m.setValueAt(i, newVal);
                    }
                }
            }else if (m.getPropertyTypeAt(i)==1){
                String key="string"+prefix+"_"+i;
                if (paramStrings.containsKey(key)){
                    String newVal=paramStrings.get(key);
                    if (v==null || !newVal.equals(v.toString())){
                        debug("[+] Setting String value for "+key);
                        m.setValueAt(i, newVal);
                    }
                }
            }else if (m.getPropertyTypeAt(i)==3){
                String key="int"+prefix+"_"+i;
                if (paramInts.containsKey(key)){
                    Integer newVal=paramInts.get(key);
                    if (v==null || !newVal.toString().equals(v.toString())){
                        debug("[+] Setting Integer value for "+key);
                        m.setValueAt(i, newVal);
                    }
                }
            }
        }
    }

    // ---------------------------------------------------------------------
    // Automatic match/replace for Forms string/integer values.
    // ---------------------------------------------------------------------

    static class MatchReplaceRule {
        boolean enabled=true;
        boolean isString=true; // true=String (regex), false=Integer (exact value)
        String scope="both";   // "request" | "response" | "both"
        String match="";
        String replace="";

        MatchReplaceRule(){}
        MatchReplaceRule(boolean enabled, boolean isString, String scope, String match, String replace){
            this.enabled=enabled;
            this.isString=isString;
            this.scope=scope;
            this.match=match;
            this.replace=replace;
        }
        boolean appliesTo(boolean request){
            if (!enabled){
                return false;
            }
            if ("both".equals(scope)){
                return true;
            }
            return request ? "request".equals(scope) : "response".equals(scope);
        }
    }

    private boolean hasApplicableRules(boolean request){
        if (!matchReplaceEnabled){
            return false;
        }
        for (MatchReplaceRule r: mrRules){
            if (r.appliesTo(request)){
                return true;
            }
        }
        return false;
    }

    private boolean hasEnabledIntResponseRule(){
        for (MatchReplaceRule r: mrRules){
            if (!r.isString && r.appliesTo(false)){
                return true;
            }
        }
        return false;
    }

    // Apply every in-scope enabled String (regex) rule to a value, in order.
    private String applyStringRules(String value, boolean request){
        if (value==null){
            return null;
        }
        String out=value;
        for (MatchReplaceRule r: mrRules){
            if (!r.isString || !r.appliesTo(request)){
                continue;
            }
            try{
                out=Pattern.compile(r.match).matcher(out).replaceAll(r.replace);
            }catch(PatternSyntaxException pse){
                stdout.println("[!] Invalid regex in match/replace rule (\""+r.match+"\"), skipping: "+pse.getMessage());
            }catch(RuntimeException rte){
                stdout.println("[!] match/replace rule failed for \""+r.match+"\": "+rte);
            }
        }
        return out;
    }

    // Apply in-scope enabled Integer (exact) rules; returns the replacement for
    // the first matching rule, otherwise the original value.
    private int applyIntRules(int value, boolean request){
        for (MatchReplaceRule r: mrRules){
            if (r.isString || !r.appliesTo(request)){
                continue;
            }
            try{
                if (Integer.parseInt(r.match.trim())==value){
                    return Integer.parseInt(r.replace.trim());
                }
            }catch(NumberFormatException nfe){
                stdout.println("[!] Invalid integer in match/replace rule (match=\""+r.match+"\", replace=\""+r.replace+"\"), skipping");
            }
        }
        return value;
    }

    // Recursively apply request-scope rules to a message's string/int leaves,
    // descending into nested Messages. Returns the number of values changed.
    private int applyMatchReplaceToMessage(Message m){
        int changes=0;
        for (int i=0;i<m.size();i++){
            Object v=m.getValueAt(i);
            if (v instanceof Message){
                changes+=applyMatchReplaceToMessage((Message)v);
            }else if (v!=null && m.getPropertyTypeAt(i)==1){
                String orig=v.toString();
                String repl=applyStringRules(orig, true);
                if (repl!=null && !repl.equals(orig)){
                    debug("[*] Forms match/replace: request string \""+orig+"\" -> \""+repl+"\"");
                    m.setValueAt(i, repl);
                    changes++;
                }
            }else if (v!=null && m.getPropertyTypeAt(i)==3){
                try{
                    int iv=Integer.parseInt(v.toString());
                    int repl=applyIntRules(iv, true);
                    if (repl!=iv){
                        debug("[*] Forms match/replace: request int "+iv+" -> "+repl);
                        m.setValueAt(i, Integer.valueOf(repl));
                        changes++;
                    }
                }catch(NumberFormatException nfe){}
            }
        }
        return changes;
    }

    // Whether the global boolean policy should run on requests. Gated by both
    // the master enable switch and a non-"Leave unchanged" dropdown selection,
    // so the master switch governs booleans along with the rest of the engine.
    private boolean boolPolicyActive(){
        return matchReplaceEnabled && boolRequestMode!=BOOL_NONE;
    }

    // Recompile the custom-scope regex after it changes. Empty regex disables
    // custom matching (pattern stays null -> matches nothing); an invalid regex
    // is logged and also leaves the pattern null.
    private void recompileScopePattern(){
        String r=scopeCustomRegex;
        if (r==null || r.isEmpty()){
            scopeCustomPattern=null;
            return;
        }
        try{
            scopeCustomPattern=Pattern.compile(r);
        }catch(PatternSyntaxException pse){
            scopeCustomPattern=null;
            stdout.println("[!] Invalid custom scope regex (\""+r+"\"), matching nothing: "+pse.getMessage());
        }
    }

    // Whether this URL may be modified by the transforms. The FRM/ORA highlight
    // does NOT call this (it stays global). Custom mode with an empty/invalid
    // regex matches nothing until a valid regex is entered.
    private boolean allowedByScope(java.net.URL url){
        switch(scopeMode){
            case SCOPE_SUITE:  return callbacks.isInScope(url);
            case SCOPE_CUSTOM: return customScopeMatches(url);
            default:           return true; // SCOPE_ALL
        }
    }

    // Match the custom regex against the request URL. Burp's
    // IRequestInfo.getUrl() includes an explicit port (e.g.
    // https://host:443/...), which breaks intuitive patterns like
    // "https://host/forms.*". So we test the raw URL and, when the port is the
    // scheme default (80/443), also a form with that port stripped, matching if
    // EITHER hits. Uses find() (substring match).
    private boolean customScopeMatches(java.net.URL url){
        Pattern p=scopeCustomPattern;
        if (p==null){
            return false;
        }
        String full=url.toString();
        boolean hit=p.matcher(full).find();
        if (!hit){
            String stripped=stripDefaultPort(url);
            if (stripped!=null && !stripped.equals(full)){
                hit=p.matcher(stripped).find();
            }
        }
        debug("[scope] custom regex vs \""+full+"\" -> "+hit);
        return hit;
    }

    // "https://host:443/path" -> "https://host/path" (and :80 for http). Returns
    // null when there is no explicit port or it is not the scheme default.
    private static String stripDefaultPort(java.net.URL u){
        int port=u.getPort();
        if (port<0){
            return null;
        }
        String proto=u.getProtocol();
        boolean isDefault=("https".equalsIgnoreCase(proto) && port==443)
                        || ("http".equalsIgnoreCase(proto) && port==80);
        if (!isDefault){
            return null;
        }
        try{
            return new java.net.URL(proto, u.getHost(), -1, u.getFile()).toString();
        }catch(java.net.MalformedURLException e){
            return null;
        }
    }

    // Apply the global boolean policy (flip / force true / force false) to every
    // Boolean property in the tree, descending into nested Messages. Booleans are
    // detected by value type, so no property-type code is needed. Returns the
    // number of values changed.
    private int applyBoolPolicy(Message m){
        if (boolRequestMode==BOOL_NONE){
            return 0;
        }
        int changes=0;
        for (int i=0;i<m.size();i++){
            Object v=m.getValueAt(i);
            if (v instanceof Message){
                changes+=applyBoolPolicy((Message)v);
            }else if (v instanceof Boolean){
                boolean cur=((Boolean)v).booleanValue();
                boolean nv;
                switch(boolRequestMode){
                    case BOOL_FLIP:  nv=!cur;  break;
                    case BOOL_TRUE:  nv=true;  break;
                    case BOOL_FALSE: nv=false; break;
                    default:         nv=cur;
                }
                if (nv!=cur){
                    debug("[*] Forms boolean policy: "+cur+" -> "+nv);
                    m.setValueAt(i, Boolean.valueOf(nv));
                    changes++;
                }
            }
        }
        return changes;
    }

    // Collect the distinct string values present anywhere in a message tree.
    private void collectStringValues(Message m, Set<String> out){
        for (int i=0;i<m.size();i++){
            Object v=m.getValueAt(i);
            if (v==null){
                continue;
            }
            if (v instanceof Message){
                collectStringValues((Message)v, out);
            }else if (m.getPropertyTypeAt(i)==1){
                out.add(v.toString());
            }
        }
    }

    // Requests can be re-serialised: apply rules to the parsed messages and
    // re-encode with one shared dispatcher. Returns the new body, or null if
    // nothing changed / re-serialisation failed (leave the request untouched).
    private byte[] transformRequestBody(byte[] body){
        String[] localAs=new String[256];
        ByteArrayInputStream bis=new ByteArrayInputStream(body);
        DataInputStream dis=new DataInputStream(bis);
        ByteArrayOutputStream baos=new ByteArrayOutputStream();
        DataOutputStream dos=new DataOutputStream(baos);
        FormsDispatcher dispatcher=new FormsDispatcher();
        Message m;
        int totalChanges=0;
        try{
            while((m=Message.readDetails(dis,localAs))!=null){
                totalChanges+=applyMatchReplaceToMessage(m);
                totalChanges+=applyBoolPolicy(m);
                resolveIndexTags(m);
                m.writeDetails(dispatcher, dos);
            }
        }catch(EOFException eofe){
            // normal-ish end of stream
        }catch(IOException e){
            stdout.println("[!] Forms match/replace request IOException, leaving unchanged: "+e);
            return null;
        }catch(RuntimeException re){
            stdout.println("[!] Forms match/replace request re-serialisation failed, leaving unchanged: "+re);
            return null;
        }
        if (totalChanges==0){
            return null;
        }
        try{
            dos.writeByte(-16);
            dos.writeByte(0x01);
        }catch(IOException e){
            return null;
        }
        return baos.toByteArray();
    }

    // Responses cannot be re-serialised (see patchResponseBody()). Apply string
    // rules by byte-patching each changed literal in place. Returns the new
    // body, or null if nothing changed.
    private byte[] transformResponseBody(byte[] body){
        Set<String> values=new LinkedHashSet<String>();
        String[] localAs=new String[256];
        try{
            ByteArrayInputStream bis=new ByteArrayInputStream(body);
            DataInputStream dis=new DataInputStream(bis);
            Message m;
            while((m=Message.readDetails(dis,localAs))!=null){
                collectStringValues(m, values);
            }
        }catch(EOFException eofe){
            // normal-ish end of stream
        }catch(Exception e){
            stdout.println("[!] Forms match/replace: failed to parse response, leaving unchanged: "+e);
            return null;
        }
        byte[] patched=body;
        int changes=0;
        for (String oldV: values){
            String newV=applyStringRules(oldV, false);
            if (newV==null || newV.equals(oldV)){
                continue;
            }
            try{
                byte[] before=patched;
                patched=replaceAll(patched, utfBytes(oldV), utfBytes(newV));
                if (patched!=before){
                    changes++;
                    debug("[*] Forms match/replace: response string \""+oldV+"\" -> \""+newV+"\"");
                }
            }catch(IOException ioe){
                stdout.println("[!] Forms match/replace: failed to encode replacement for \""+oldV+"\"");
            }
        }
        if (hasEnabledIntResponseRule()){
            debug("[*] Forms match/replace: integer rules are not applied to responses (skipped).");
        }
        if (changes==0){
            return null;
        }
        return patched;
    }

    // Replace every non-overlapping occurrence of needle with rep. Returns the
    // same array reference if needle is absent (so callers can detect no-op).
    static byte[] replaceAll(byte[] hay, byte[] needle, byte[] rep){
        int idx=indexOf(hay, needle, 0);
        if (idx<0){
            return hay;
        }
        ByteArrayOutputStream out=new ByteArrayOutputStream();
        int pos=0;
        while (idx>=0){
            out.write(hay, pos, idx-pos);
            out.write(rep, 0, rep.length);
            pos=idx+needle.length;
            idx=indexOf(hay, needle, pos);
        }
        out.write(hay, pos, hay.length-pos);
        return out.toByteArray();
    }

    private static String getHeaderValue(List<String> headers, String name){
        for (String h: headers){
            int c=h.indexOf(':');
            if (c>0 && h.substring(0,c).trim().equalsIgnoreCase(name)){
                return h.substring(c+1).trim();
            }
        }
        return null;
    }

    private void loadMatchReplaceSettings(){
        try{
            matchReplaceEnabled="true".equals(callbacks.loadExtensionSetting(MR_ENABLED_SETTING));
            debugEnabled="true".equals(callbacks.loadExtensionSetting(DEBUG_SETTING));
            frmHighlightEnabled=!"false".equals(callbacks.loadExtensionSetting(FRM_HIGHLIGHT_SETTING)); // default on
            try{
                String bm=callbacks.loadExtensionSetting(BOOL_MODE_SETTING);
                int parsed=(bm==null||bm.isEmpty())?BOOL_NONE:Integer.parseInt(bm.trim());
                boolRequestMode=(parsed>=BOOL_NONE && parsed<=BOOL_FALSE)?parsed:BOOL_NONE;
            }catch(NumberFormatException nfe){
                boolRequestMode=BOOL_NONE;
            }
            try{
                String sm=callbacks.loadExtensionSetting(SCOPE_MODE_SETTING);
                int parsed=(sm==null||sm.isEmpty())?SCOPE_ALL:Integer.parseInt(sm.trim());
                scopeMode=(parsed>=SCOPE_ALL && parsed<=SCOPE_CUSTOM)?parsed:SCOPE_ALL;
            }catch(NumberFormatException nfe){
                scopeMode=SCOPE_ALL;
            }
            String sr=callbacks.loadExtensionSetting(SCOPE_REGEX_SETTING);
            scopeCustomRegex=(sr==null)?"":sr;
            recompileScopePattern();
            String data=callbacks.loadExtensionSetting(MR_RULES_SETTING);
            mrRules.clear();
            if (data!=null && !data.isEmpty()){
                for (String line: data.split("\n")){
                    if (line.trim().isEmpty()){
                        continue;
                    }
                    String[] f=line.split("\\|", -1);
                    if (f.length!=5){
                        continue;
                    }
                    mrRules.add(new MatchReplaceRule("1".equals(f[0]), "1".equals(f[1]), b64d(f[2]), b64d(f[3]), b64d(f[4])));
                }
            }
        }catch(Exception e){
            stdout.println("[!] Failed to load match/replace settings: "+e);
        }
    }

    void saveMatchReplaceSettings(){
        try{
            StringBuilder sb=new StringBuilder();
            for (MatchReplaceRule r: mrRules){
                sb.append(r.enabled?"1":"0").append("|")
                  .append(r.isString?"1":"0").append("|")
                  .append(b64e(r.scope)).append("|")
                  .append(b64e(r.match)).append("|")
                  .append(b64e(r.replace)).append("\n");
            }
            callbacks.saveExtensionSetting(MR_RULES_SETTING, sb.toString());
            callbacks.saveExtensionSetting(MR_ENABLED_SETTING, matchReplaceEnabled?"true":"false");
            callbacks.saveExtensionSetting(DEBUG_SETTING, debugEnabled?"true":"false");
            callbacks.saveExtensionSetting(FRM_HIGHLIGHT_SETTING, frmHighlightEnabled?"true":"false");
            callbacks.saveExtensionSetting(BOOL_MODE_SETTING, Integer.toString(boolRequestMode));
            callbacks.saveExtensionSetting(SCOPE_MODE_SETTING, Integer.toString(scopeMode));
            callbacks.saveExtensionSetting(SCOPE_REGEX_SETTING, scopeCustomRegex);
        }catch(Exception e){
            stdout.println("[!] Failed to save match/replace settings: "+e);
        }
    }

    private static String b64e(String s){
        return Base64.getEncoder().encodeToString(s==null ? new byte[0] : s.getBytes(java.nio.charset.StandardCharsets.UTF_8));
    }
    private static String b64d(String s){
        try{
            return new String(Base64.getDecoder().decode(s), java.nio.charset.StandardCharsets.UTF_8);
        }catch(Exception e){
            return "";
        }
    }

    @Override
    public void processHttpMessage(int toolFlag, boolean messageIsRequest, IHttpRequestResponse messageInfo){
        if(!messageIsRequest){  // We don't care if it's not a request
            processResponse(messageInfo);
            return;
        }

        byte[] msg=messageInfo.getRequest();
        IRequestInfo rInfo=helpers.analyzeRequest(messageInfo);

        if (rInfo.getUrl().toString().indexOf("/lservlet") == -1 || !"POST".equalsIgnoreCase(rInfo.getMethod())){ // We don't care if it's not a POST for Forms
            return;
        }

        byte[] handshakeBody=Arrays.copyOfRange(msg, rInfo.getBodyOffset(), rInfo.getBodyOffset() + 4);
        if (Arrays.equals(handshakeBody, new byte[] {0x47, 0x44, 0x61, 0x79} )){ // We don't care about the intial handshake
            debug("Ignoring handshake in HTTP Listener");
            return;
        }

        byte[] handshakeBody1=Arrays.copyOfRange(msg, rInfo.getBodyOffset(), rInfo.getBodyOffset() + 8);
        if (Arrays.equals(handshakeBody1, new byte[] {0x4e, 0x55, 0x4c, 0x4c, 0x50, 0x4f, 0x53, 0x54} )){ // We don't care about NULLPOSTs
            debug("Ignoring NULLPOST in HTTP Listener");
            return;
        }


        byte[] body=Arrays.copyOfRange(msg, rInfo.getBodyOffset(), msg.length);
        
        if (body.length == 0){ // We don't care about empty bodies
            return;
        }

        String[] as=new String[256];
        ByteArrayInputStream bis=new ByteArrayInputStream(body);
        DataInputStream dis=new DataInputStream(bis);
        Message m;

        try{
            if (body[body.length-2] != (byte)0xf0){
                throw new IllegalArgumentException("Illegal close Message detected!");
            }
            while((m=Message.readDetails(dis,as))!=null){}
        }catch(Exception e){
            stdout.println("Caught exception while decoding Forms HTTP request! Redirecting to localhost...");
            stdout.println(e.getMessage());
            messageInfo.setHttpService(helpers.buildHttpService("127.0.0.1",65535,false));
            return; // don't attempt match/replace on a body we couldn't decode
        }

        // Automatic match/replace and/or global boolean policy on the
        // (validated) request body, subject to the configured scope.
        if ((hasApplicableRules(true) || boolPolicyActive()) && allowedByScope(rInfo.getUrl())){
            try{
                byte[] newBody=transformRequestBody(body);
                if (newBody!=null){
                    messageInfo.setRequest(helpers.buildHttpMessage(rInfo.getHeaders(), newBody));
                    stdout.println("[*] Forms match/replace applied to request");
                }else{
                    debug("[*] Forms match/replace: no request rule matched this message");
                }
            }catch(RuntimeException re){
                stdout.println("[!] Forms match/replace request error, left unchanged: "+re);
            }
        }
    }

    // Response direction of processHttpMessage(): highlight FRM/ORA errors and
    // apply string match/replace to Forms responses (byte-patched, since
    // responses cannot be re-serialised).
    private void processResponse(IHttpRequestResponse messageInfo){
        boolean mrActive=hasApplicableRules(false);
        if (!frmHighlightEnabled && !mrActive){
            return; // nothing to do
        }
        byte[] resp=messageInfo.getResponse();
        if (resp==null){
            return;
        }
        // Only Forms responses: the originating request targets /lservlet and
        // the response is the binary Forms stream.
        IRequestInfo reqInfo=helpers.analyzeRequest(messageInfo);
        if (reqInfo.getUrl().toString().indexOf("/lservlet") == -1){
            return;
        }
        IResponseInfo respInfo=helpers.analyzeResponse(resp);
        String ct=getHeaderValue(respInfo.getHeaders(), "content-type");
        if (ct==null || ct.toLowerCase().indexOf("application/octet-stream")==-1){
            return;
        }
        byte[] body=Arrays.copyOfRange(resp, respInfo.getBodyOffset(), resp.length);
        if (body.length==0){
            return;
        }

        if (frmHighlightEnabled){
            highlightFormsErrors(messageInfo, body); // read-only recon, stays global (not scope-gated)
        }

        if (mrActive && allowedByScope(reqInfo.getUrl())){
            try{
                byte[] newBody=transformResponseBody(body);
                if (newBody!=null){
                    messageInfo.setResponse(helpers.buildHttpMessage(respInfo.getHeaders(), newBody));
                    stdout.println("[*] Forms match/replace applied to response");
                }
            }catch(RuntimeException re){
                stdout.println("[!] Forms match/replace response error, left unchanged: "+re);
            }
        }
    }

    // Flag Forms responses that carry FRM-/ORA- error codes. The error strings
    // are ASCII in the serialized body, so a regex over the raw bytes finds them
    // without a full parse. Sets a red history highlight + comment and raises an
    // alert, so authorization checks (e.g. FRM-41084) stand out during recon.
    private void highlightFormsErrors(IHttpRequestResponse messageInfo, byte[] body){
        String text=new String(body, java.nio.charset.StandardCharsets.ISO_8859_1);
        java.util.regex.Matcher mch=FRM_ERROR_PATTERN.matcher(text);
        LinkedHashSet<String> codes=new LinkedHashSet<String>();
        while (mch.find()){
            codes.add(mch.group());
        }
        if (codes.isEmpty()){
            return;
        }
        StringBuilder sb=new StringBuilder();
        for (String c: codes){
            if (sb.length()>0){
                sb.append(", ");
            }
            sb.append(c);
        }
        String joined=sb.toString();
        messageInfo.setHighlight("red");
        String existing=messageInfo.getComment();
        if (existing==null || existing.isEmpty()){
            messageInfo.setComment(joined);
        }else if (existing.indexOf(joined)==-1){
            messageInfo.setComment(existing+" | "+joined);
        }
        stdout.println("[*] Oracle Forms error(s) in response: "+joined);
        callbacks.issueAlert("Oracle Forms error in response: "+joined);
    }

    // Re-serialise a request body with the given edits applied. Shared by the
    // param tab and the tree tab. Returns originalMessage unchanged if
    // re-serialisation fails (so Burp never gets a corrupt/truncated body).
    byte[] reserializeRequestBody(byte[] body, List<String> httpHeaders,
            java.util.Map<String,String> paramStrings, java.util.Map<String,Integer> paramInts,
            java.util.Map<String,Boolean> paramBools, byte[] originalMessage){
        String[] as=new String[256];
        ByteArrayInputStream bis=new ByteArrayInputStream(body);
        DataInputStream dis=new DataInputStream(bis);
        int m_id=0;
        ByteArrayOutputStream baos=new ByteArrayOutputStream();
        DataOutputStream dos=new DataOutputStream(baos);
        Message m;
        // One dispatcher for the whole stream so the write-side string-reference
        // table stays in sync (see the long note previously in getMessage()).
        FormsDispatcher dispatcher=new FormsDispatcher();
        boolean serialisationFailed=false;
        try{
            debug("[*] Enter stream parser");
            while((m=Message.readDetails(dis,as))!=null){
                debug("[*] Message start, ID: "+m_id+ " size: "+m.size());
                applyEdits(m, "_"+m_id, paramStrings, paramInts, paramBools, stdout);
                int resolved=resolveIndexTags(m);
                if (resolved>0){
                    debug("[*] Resolved "+resolved+" IndexTag reference(s) before writing message "+m_id);
                }
                m.writeDetails(dispatcher, dos);
                m_id++;
            }
        }catch(EOFException eofe){
            debug("\nReached EOF in reserializeRequestBody()");
        }catch(IOException e){
            stdout.println("Message IOException");
            e.printStackTrace(stdout);
        }catch(RuntimeException re){
            // e.g. an IndexTag that could not be resolved. Forward the original
            // message untouched rather than a corrupt body.
            stdout.println("[!] Re-serialisation failed at message "+m_id+", forwarding original message unchanged:");
            re.printStackTrace(stdout);
            serialisationFailed=true;
        }
        if (serialisationFailed){
            return originalMessage;
        }
        try{
            dos.writeByte(-16);
            dos.writeByte(0x01);
            return helpers.buildHttpMessage(httpHeaders, baos.toByteArray());
        }catch(IOException e){
            stdout.println("Message IOException - last bytes");
            e.printStackTrace(stdout);
            return null;
        }
    }

    // Apply string edits to a response by patching the raw body in place instead
    // of re-serialising it (frmall.jar is the CLIENT library, so writeDetails()
    // cannot re-emit server-only constructs). Shared by both editor tabs. Returns
    // originalMessage on parse failure. Integer/boolean edits are not applied to
    // responses (ambiguous to locate by value); changed ints are logged.
    byte[] patchResponseBody(byte[] body, List<String> httpHeaders,
            java.util.Map<String,String> paramStrings, java.util.Map<String,Integer> paramInts,
            byte[] originalMessage){
        HashMap<String,String> origStrings=new HashMap<String,String>();
        HashMap<String,Integer> origInts=new HashMap<String,Integer>();
        String[] as=new String[256];
        try{
            ByteArrayInputStream bis=new ByteArrayInputStream(body);
            DataInputStream dis=new DataInputStream(bis);
            Message m;
            int m_id=0;
            while((m=Message.readDetails(dis,as))!=null){
                collectStrings(m, "_"+m_id, origStrings, origInts, new HashMap<String,Boolean>()); // same recursive keys as the editable surface
                m_id++;
            }
        }catch(EOFException eofe){
            // normal end of stream
        }catch(Exception e){
            stdout.println("[!] Failed to parse original response body for patching; forwarding unchanged:");
            e.printStackTrace(stdout);
            return originalMessage;
        }

        byte[] patched=body;
        int changes=0;
        for (String key: paramStrings.keySet()){
            String newV=paramStrings.get(key);
            String oldV=origStrings.get(key);
            if (oldV==null || oldV.equals(newV)){
                continue; // unknown key or value untouched by the user
            }
            try{
                byte[] oldPat=utfBytes(oldV);
                byte[] newPat=utfBytes(newV);
                int idx=indexOf(patched, oldPat, 0);
                if (idx<0){
                    stdout.println("[!] Could not locate literal bytes for "+key+" (\""+oldV+"\") in the response body; this edit was skipped.");
                    stdout.println("[!] The value is probably stored with an encoding this patcher does not recognise. Body hex follows so the format can be analysed:");
                    stdout.println(byteArrayToHex(patched));
                    continue;
                }
                if (indexOf(patched, oldPat, idx+oldPat.length)>=0){
                    stdout.println("[!] Literal for "+key+" (\""+oldV+"\") occurs more than once; patching first occurrence at offset "+idx+" only.");
                }
                byte[] nb=new byte[patched.length-oldPat.length+newPat.length];
                System.arraycopy(patched,0,nb,0,idx);
                System.arraycopy(newPat,0,nb,idx,newPat.length);
                System.arraycopy(patched,idx+oldPat.length,nb,idx+newPat.length,patched.length-(idx+oldPat.length));
                patched=nb;
                changes++;
                stdout.println("[+] Patched "+key+": \""+oldV+"\" -> \""+newV+"\" at body offset "+idx);
            }catch(IOException ioe){
                stdout.println("[!] Failed to encode replacement for "+key+"; edit skipped.");
                ioe.printStackTrace(stdout);
            }
        }

        int intEdits=0;
        for (String key: paramInts.keySet()){
            Integer newV=paramInts.get(key);
            Integer oldV=origInts.get(key);
            if (oldV!=null && !oldV.equals(newV)){
                intEdits++;
            }
        }
        if (intEdits>0){
            stdout.println("[*] Note: integer edits are not supported for responses (ambiguous to locate by value); "+intEdits+" changed int field(s) ignored.");
        }

        stdout.println("[*] Response patch complete: "+changes+" string(s) changed, new body length "+patched.length);
        return helpers.buildHttpMessage(httpHeaders, patched);
    }

    @Override
    public IMessageEditorTab createNewInstance(IMessageEditorController controller, boolean editable)
    {
        // create a new instance of our custom editor tab
        return new OracleFormsInputTab(controller, editable);
    }

    class OracleFormsInputTab implements IMessageEditorTab
    {
        private boolean editable;
        private ITextEditor txtInput;
        private byte[] currentMessage;
        private boolean currentIsRequest = true;

        public OracleFormsInputTab(IMessageEditorController controller, boolean editable)
        {
            this.editable = editable;

            // create an instance of Burp's text editor, to display our deserialized data
            txtInput = callbacks.createTextEditor();
            txtInput.setEditable(editable);
        }

        //
        // implement IMessageEditorTab
        //

        @Override
        public String getTabCaption()
        {
            return "Oracle Forms";
        }

        @Override
        public Component getUiComponent()
        {
            return txtInput.getComponent();
        }

        @Override
        public boolean isEnabled(byte[] content, boolean isRequest)
        {
            return true;
        }

        @Override
        public void setMessage(byte[] content, boolean isRequest)
        {
            if (content == null)
            {
                // clear our display
                txtInput.setText(null);
                txtInput.setEditable(false);
                return;
            }


            PrintWriter stdout = new PrintWriter(callbacks.getStdout(), true);

            // Work out where the serialized Forms body starts. Requests and
            // responses share the same Message framing, but the HTTP framing
            // must be parsed with the matching analyzer.
            int bodyOffset;
            java.net.URL surfaceUrl;
            if (isRequest){
                IRequestInfo rInfo=helpers.analyzeRequest(helpers.buildHttpService("dummyhost",1234,false),content);
                bodyOffset=rInfo.getBodyOffset();
                surfaceUrl=rInfo.getUrl();
            }else{
                IResponseInfo rInfo=helpers.analyzeResponse(content);
                bodyOffset=rInfo.getBodyOffset();
                surfaceUrl=null; // responses have no URL; use a placeholder below
            }

            byte[] body=Arrays.copyOfRange(content, bodyOffset, content.length);
            String[] as=new String[256];
            ByteArrayInputStream bis=new ByteArrayInputStream(body);
            DataInputStream dis=new DataInputStream(bis);
            Message m;

            // Responses are only editable where Burp offers an editable editor
            // (e.g. Proxy intercept). Everywhere else (Proxy history, Repeater
            // response pane) keep the richer read-only recursive dump.
            if(!isRequest && !editable){
                try{
                    StringBuilder sb=new StringBuilder();

                    while((m=Message.readDetails(dis,as))!=null){
                        sb.append(messageToString(m));
                        sb.append("\n+++ Message +++\n");
                    }
                    txtInput.setText(sb.toString().getBytes());
                    txtInput.setEditable(false);
                }catch(EOFException eofe){
                    debug("\nReached EOFin setMessage()");
                }catch(IOException e){
                    stdout.println("Message IOException");
                    e.printStackTrace(stdout);
                }catch(IllegalArgumentException iae){
                    stdout.println("Message response IllegalArgumentException");
                    iae.printStackTrace(stdout);
                }
            }else
            {
                if (surfaceUrl==null){
                    try{
                        surfaceUrl=new java.net.URL("http://oracle-forms-response/lservlet");
                    }catch(java.net.MalformedURLException mue){
                        stdout.println("Could not build placeholder URL for response surface");
                    }
                }
                byte[] dummyRequest=helpers.buildHttpRequest(surfaceUrl); // [TODO] POST plz
                int m_id=0;

                try{
                    // Expose strings/ints nested inside other Message objects
                    // too, for both requests and responses. getMessage() applies
                    // the same recursive keys back onto the message tree.
                    java.util.LinkedHashMap<String,String> strings=new java.util.LinkedHashMap<String,String>();
                    java.util.LinkedHashMap<String,Integer> ints=new java.util.LinkedHashMap<String,Integer>();
                    java.util.LinkedHashMap<String,Boolean> bools=new java.util.LinkedHashMap<String,Boolean>();
                    while((m=Message.readDetails(dis,as))!=null){
                        collectStrings(m, "_"+m_id, strings, ints, bools);
                        m_id++;
                    }
                    for (java.util.Map.Entry<String,String> e: strings.entrySet()){
                        dummyRequest=helpers.addParameter(dummyRequest, helpers.buildParameter(e.getKey(), helpers.urlEncode(e.getValue()), IParameter.PARAM_BODY));
                    }
                    for (java.util.Map.Entry<String,Integer> e: ints.entrySet()){
                        dummyRequest=helpers.addParameter(dummyRequest, helpers.buildParameter(e.getKey(), e.getValue().toString(), IParameter.PARAM_BODY));
                    }
                    // Booleans are only re-applied on the request re-serialisation
                    // path (responses cannot be re-serialised), so expose an
                    // editable true/false field only for requests. Flip one to
                    // switch that property in the forwarded request.
                    if (isRequest){
                        for (java.util.Map.Entry<String,Boolean> e: bools.entrySet()){
                            dummyRequest=helpers.addParameter(dummyRequest, helpers.buildParameter(e.getKey(), e.getValue().toString(), IParameter.PARAM_BODY));
                        }
                    }
                    dummyRequest=helpers.addParameter(dummyRequest, helpers.buildParameter("bytestream", byteArrayToHex(body), IParameter.PARAM_BODY));
                    // Show only the body (the editable params + bytestream=), not the
                    // synthetic HTTP request line/headers buildHttpRequest produced:
                    // those headers are never honoured (getMessage rebuilds with the
                    // real message headers), so displaying them is just misleading.
                    IRequestInfo dummyInfo=helpers.analyzeRequest(dummyRequest);
                    byte[] paramsOnly=Arrays.copyOfRange(dummyRequest, dummyInfo.getBodyOffset(), dummyRequest.length);
                    // One parameter per line for readability. Values are URL-encoded,
                    // so '&' only separates params (never appears inside a value),
                    // making this reversible in getMessage().
                    String display=new String(paramsOnly, java.nio.charset.StandardCharsets.ISO_8859_1).replace("&", "\n");
                    txtInput.setText(display.getBytes(java.nio.charset.StandardCharsets.ISO_8859_1));
                    txtInput.setEditable(editable);
                }catch(EOFException eofe){
                    debug("\nReached EOFin setMessage()");
                }catch(IOException e){
                    stdout.println("Message IOException");
                    e.printStackTrace(stdout);
                }catch(IllegalArgumentException iae){
                    stdout.println("Message IllegalArgumentException in setMessage()");
                    iae.printStackTrace(stdout);
                }
            }

            // remember the displayed content
            currentMessage = content;
            currentIsRequest = isRequest;
        }

        @Override
        public byte[] getMessage()
        {

            PrintWriter stdout = new PrintWriter(callbacks.getStdout(), true);
            debug("[*] Setting message from dummy POST");

            // The editor now shows only the parameter body (no request line or
            // headers), so wrap it back into a minimal request before parsing the
            // body params. The synthetic wrapper is thrown away; only the params
            // are read.
            // Editor shows one param per line; rejoin into an &-separated body (no
            // literal '&'/newline exists inside URL-encoded values) before wrapping.
            String shownText=new String(txtInput.getText(), java.nio.charset.StandardCharsets.ISO_8859_1);
            byte[] shownBody=shownText.replace("\r","").replace("\n","&").getBytes(java.nio.charset.StandardCharsets.ISO_8859_1);
            byte[] wrapped=helpers.buildHttpMessage(
                    java.util.Arrays.asList("POST / HTTP/1.1", "Content-Type: application/x-www-form-urlencoded"),
                    shownBody);
            IRequestInfo dummyRequest=helpers.analyzeRequest(wrapped);
            HashMap<String,String> paramStrings=new HashMap<String,String>(); // Not necessarily optimal, but code is nicer...
            HashMap<String,Integer> paramInts=new HashMap<String,Integer>();
            HashMap<String,Boolean> paramBools=new HashMap<String,Boolean>();
            ArrayList<String> invalidInts=new ArrayList<String>();
            ArrayList<String> invalidBools=new ArrayList<String>();
            String overrideHex=null; // raw plain-byte body override (edited "bytestream=" param)
            for (IParameter p: dummyRequest.getParameters()){
                if (p.getName().equals("bytestream")){
                    overrideHex=p.getValue();
                }else if (p.getName().startsWith("string_")){
                    debug("[+] Found string parameter: "+p.getName()+"="+p.getValue().toString());
                    paramStrings.put(p.getName(), helpers.urlDecode(p.getValue()));
                }else if(p.getName().startsWith("int_")){
                    debug("[+] Found int parameter: "+p.getName()+"="+p.getValue().toString());
                    try{
                        paramInts.put(p.getName(), Integer.parseInt(p.getValue().trim()));
                    }catch(NumberFormatException nfe){
                        stdout.println("[!] Non-integer value for "+p.getName()+": \""+p.getValue()+"\"");
                        invalidInts.add(p.getName()+" = \""+p.getValue()+"\"");
                    }
                }else if(p.getName().startsWith("bool_")){
                    debug("[+] Found bool parameter: "+p.getName()+"="+p.getValue().toString());
                    String raw=helpers.urlDecode(p.getValue()).trim();
                    if ("true".equalsIgnoreCase(raw)){
                        paramBools.put(p.getName(), Boolean.TRUE);
                    }else if ("false".equalsIgnoreCase(raw)){
                        paramBools.put(p.getName(), Boolean.FALSE);
                    }else{
                        stdout.println("[!] Non-boolean value for "+p.getName()+": \""+p.getValue()+"\"");
                        invalidBools.add(p.getName()+" = \""+p.getValue()+"\"");
                    }
                }
            }

            int bodyOffset;
            List<String> httpHeaders;
            if (currentIsRequest){
                IRequestInfo rInfo=helpers.analyzeRequest(currentMessage);
                bodyOffset=rInfo.getBodyOffset();
                httpHeaders=rInfo.getHeaders();
            }else{
                IResponseInfo rInfo=helpers.analyzeResponse(currentMessage);
                bodyOffset=rInfo.getBodyOffset();
                httpHeaders=rInfo.getHeaders();
            }
            byte[] body=Arrays.copyOfRange(currentMessage, bodyOffset, currentMessage.length);

            // Plain-byte override: if the user edited the
            // "bytestream=<hex>" parameter, use those bytes verbatim as the body
            // (no serialisation, no patching, no field logic), for both requests
            // and responses. This wins over string_/int_/bool_ edits. Evaluated
            // before the invalid-field dialog so a pure byte override is not
            // interrupted by unrelated field warnings.
            if (overrideHex!=null){
                String edited=helpers.urlDecode(overrideHex).replaceAll("\\s","");
                if (!edited.equalsIgnoreCase(byteArrayToHex(body))){ // user actually changed it
                    if (edited.matches("[0-9A-Fa-f]*") && edited.length()%2==0){
                        byte[] raw=hexToBytes(edited);
                        stdout.println("[*] Plain byte override: body replaced with "+raw.length
                                +" user-supplied bytes (field edits ignored)");
                        return helpers.buildHttpMessage(httpHeaders, raw);
                    }
                    // Invalid hex: warn and fall through to normal field handling.
                    String warn="The 'bytestream=' override hex is invalid (needs an even count "
                            +"of hex digits, 0-9/a-f only). Raw override skipped; field edits still apply.";
                    callbacks.issueAlert(warn);
                    javax.swing.JOptionPane.showMessageDialog(txtInput.getComponent(), warn,
                            "Oracle Forms Serializer - invalid override hex", javax.swing.JOptionPane.ERROR_MESSAGE);
                }
            }

            // Don't silently drop bad field input: tell the user which fields
            // could not be applied (modal dialog + Burp alert). Invalid fields
            // keep their original value; other edits still apply.
            if (!invalidInts.isEmpty() || !invalidBools.isEmpty()){
                StringBuilder sb=new StringBuilder();
                sb.append("These field(s) had invalid input and were NOT applied:\n\n");
                for (String s: invalidInts){
                    sb.append("    - integer ").append(s).append("   (needs a whole number, e.g. 123)\n");
                }
                for (String s: invalidBools){
                    sb.append("    - boolean ").append(s).append("   (needs true or false)\n");
                }
                sb.append("\nThey keep their original value; any other edits are still applied.");
                String warning=sb.toString();
                callbacks.issueAlert(warning);
                javax.swing.JOptionPane.showMessageDialog(txtInput.getComponent(), warning,
                        "Oracle Forms Serializer - invalid integer input", javax.swing.JOptionPane.ERROR_MESSAGE);
            }

            // Responses cannot be re-serialised: frmall.jar is the CLIENT
            // library, so Message.writeDetails() only knows how to emit
            // request-side constructs. Server->client messages carry types the
            // client merely decodes and never re-encodes (IndexTag, DeleteMask,
            // delta masks, ...), so writeDetails throws on them. Instead we
            // patch the edited string(s) directly into the original response
            // bytes and leave everything else untouched.
            if (!currentIsRequest){
                return patchResponseBody(body, httpHeaders, paramStrings, paramInts, currentMessage);
            }
            return reserializeRequestBody(body, httpHeaders, paramStrings, paramInts, paramBools, currentMessage);
        }

        @Override
        public boolean isModified()
        {
            return txtInput.isTextModified();
        }

        @Override
        public byte[] getSelectedData()
        {
            return txtInput.getSelectedText();
        }
    }

    @Override
    public List<IScannerInsertionPoint> getInsertionPoints(
            IHttpRequestResponse baseRequestResponse) {
        
        List<IScannerInsertionPoint> insertionPoints=new ArrayList<IScannerInsertionPoint>();
        byte[] msg=baseRequestResponse.getRequest();
        IRequestInfo rInfo=helpers.analyzeRequest(msg);
        byte[] body=Arrays.copyOfRange(msg, rInfo.getBodyOffset(), msg.length);

        try{
            Message m;
            
            ByteArrayInputStream bis=new ByteArrayInputStream(body);
            DataInputStream dis=new DataInputStream(bis);
            ArrayList<Message> messages=new ArrayList<Message>();
            
            while((m=Message.readDetails(dis,as))!=null){
                debug("Adding message as potential insertion point");
                messages.add(m);
            }
            for (int i=0;i<messages.size();i++){
                Message mi=messages.get(i);
                for (int j=0;j<mi.size();j++){
                    if (mi.getPropertyTypeAt(j)==1){ // String property
                        insertionPoints.add(new OracleFormsInsertionPoint(baseRequestResponse.getRequest(),messages, i, j));
                    } 
                }
            }
        }catch(EOFException eofe){
                debug("\nReached EOF in getInsertionPoints()");
        }catch(IOException e){
            stdout.println("Scanner Message IOException");
        }catch(IllegalArgumentException iae){
            stdout.println("Scanner Message IllegalArgumentException");
        }
        debug("Supplied "+insertionPoints.size()+" insertion points");
        return insertionPoints;
    }
    class OracleFormsInsertionPoint implements IScannerInsertionPoint{
        private int propId=0;
        private int msgId=0;

        private ArrayList<Message> messages=new ArrayList<Message>();
        private byte[] baseRequest=null;
        
        public OracleFormsInsertionPoint(byte[] baseRequest,ArrayList<Message> messages, int msgId, int propId){
            this.messages=messages;
            this.msgId=msgId;
            this.propId=propId;
            this.baseRequest=baseRequest;
        }
        
        @Override
        public String getInsertionPointName() {
            return "Oracle Forms insertion point";
        }

        @Override
        public String getBaseValue() {
            return messages.get(msgId).getValueAt(propId).toString();
        }

        @Override
        public byte[] buildRequest(byte[] payload) {
            
            debug("buildRequest called");
            IRequestInfo rInfo=helpers.analyzeRequest(this.baseRequest);
            //messages.get(msgId).setValueAt(propId, new String(payload));

            ByteArrayOutputStream baos=new ByteArrayOutputStream();
            DataOutputStream dos=new DataOutputStream(baos);
            
            FormsDispatcher dispatcher=new FormsDispatcher();
            try{
                for (int i=0;i<messages.size();i++){
                    Message m=messages.get(i);
                    if (i == msgId){
                        m.setValueAt(propId, new String(payload));
                    }
                    resolveIndexTags(m); // convert string-table back-references so writeDetails can serialise them
                    m.writeDetails(dispatcher, dos); // single dispatcher: keep the string table in sync across the stream
                }
            }catch(EOFException eofe){
                debug("\nReached EOF in buildRequest");
            }catch(IOException ioe){
                stdout.println("IOExceltion while building scanner request!");
                ioe.printStackTrace(stdout);
                return null;
            }
            try{
                dos.writeByte(-16);
                dos.writeByte(0x01);
                dos.flush();
            }catch(IOException ioe){
                stdout.println("IOExceltion (last bytes) while building scanner request!");
                ioe.printStackTrace(stdout);
                return null;
            }
            byte[] res=baos.toByteArray();
            debug("Scanner request built: "+byteArrayToHex(res));
            return helpers.buildHttpMessage(rInfo.getHeaders(), baos.toByteArray());
        }

        @Override
        public int[] getPayloadOffsets(byte[] payload) {
            return null;
        }

        @Override
        public byte getInsertionPointType() {
            debug("Insertion Point Type queried");
            return INS_PARAM_BODY;
        }

    }

    // Config UI for automatic match/replace. A Burp suite tab with a rule
    // table, an Add/Edit dialog, and a master on/off switch. Rules persist via
    // saveExtensionSetting()/loadExtensionSetting().
    class OracleFormsMatchReplaceTab implements ITab {
        private final javax.swing.JPanel panel;
        private final MRTableModel model;

        OracleFormsMatchReplaceTab(){
            panel=new javax.swing.JPanel(new java.awt.BorderLayout());

            // Options panel (vertical): each checkbox writes its flag + persists.
            // The master switch is the single on/off for the whole engine (rules
            // AND the boolean policy), so make it visually stand out: bold,
            // enlarged, and in its own bordered banner above the other options.
            final javax.swing.JCheckBox master=new javax.swing.JCheckBox("Enable Oracle Forms match/replace  (master switch — rules + boolean policy)", matchReplaceEnabled);
            master.setToolTipText("Master on/off for all automatic Forms processing: match/replace rules and the boolean policy below.");
            java.awt.Font masterFont=master.getFont();
            master.setFont(masterFont.deriveFont(java.awt.Font.BOLD, masterFont.getSize2D()+3f));
            master.addActionListener(new java.awt.event.ActionListener(){
                public void actionPerformed(java.awt.event.ActionEvent e){
                    matchReplaceEnabled=master.isSelected();
                    saveMatchReplaceSettings();
                }
            });
            javax.swing.JPanel masterBanner=new javax.swing.JPanel(new java.awt.FlowLayout(java.awt.FlowLayout.LEFT, 6, 6));
            masterBanner.setBorder(javax.swing.BorderFactory.createCompoundBorder(
                    javax.swing.BorderFactory.createEmptyBorder(6,6,6,6),
                    javax.swing.BorderFactory.createEtchedBorder()));
            masterBanner.add(master);
            final javax.swing.JCheckBox frmBox=new javax.swing.JCheckBox("Highlight FRM/ORA errors in responses", frmHighlightEnabled);
            frmBox.addActionListener(new java.awt.event.ActionListener(){
                public void actionPerformed(java.awt.event.ActionEvent e){
                    frmHighlightEnabled=frmBox.isSelected();
                    saveMatchReplaceSettings();
                }
            });
            final javax.swing.JCheckBox debugBox=new javax.swing.JCheckBox("Show debug output in extension output", debugEnabled);
            debugBox.addActionListener(new java.awt.event.ActionListener(){
                public void actionPerformed(java.awt.event.ActionEvent e){
                    debugEnabled=debugBox.isSelected();
                    saveMatchReplaceSettings();
                }
            });
            // Global boolean policy for requests: a single dropdown applied to
            // every Boolean property. Gated by the master switch above.
            final javax.swing.JComboBox<String> boolMode=new javax.swing.JComboBox<String>(BOOL_MODE_LABELS);
            boolMode.setToolTipText("Applies to every boolean in Forms requests. Requires the master switch above to be enabled.");
            boolMode.setSelectedIndex(boolRequestMode);
            boolMode.setMaximumSize(boolMode.getPreferredSize());
            boolMode.addActionListener(new java.awt.event.ActionListener(){
                public void actionPerformed(java.awt.event.ActionEvent e){
                    boolRequestMode=boolMode.getSelectedIndex();
                    saveMatchReplaceSettings();
                }
            });
            javax.swing.JPanel boolRow=new javax.swing.JPanel(new java.awt.FlowLayout(java.awt.FlowLayout.LEFT, 0, 0));
            boolRow.setAlignmentX(java.awt.Component.LEFT_ALIGNMENT);
            boolRow.add(new javax.swing.JLabel("Booleans in requests: "));
            boolRow.add(boolMode);

            // Scope for the modifying transforms (match/replace + boolean policy):
            // all traffic / Burp Target scope / a custom URL regex. The regex
            // field is enabled only in Custom mode. FRM/ORA highlighting is not
            // affected by this and always runs on all Forms responses.
            final javax.swing.JTextField scopeRegexField=new javax.swing.JTextField(scopeCustomRegex, 24);
            scopeRegexField.setEnabled(scopeMode==SCOPE_CUSTOM);
            scopeRegexField.setToolTipText("Java regex matched (find) against the request URL. The scheme default port (:80/:443) is optional in your pattern; non-default ports appear in the URL. Enable debug output to log the exact URL tested.");
            final javax.swing.JComboBox<String> scopeCombo=new javax.swing.JComboBox<String>(SCOPE_MODE_LABELS);
            scopeCombo.setToolTipText("Which Forms traffic match/replace and the boolean policy apply to. FRM/ORA highlighting always runs on all Forms responses.");
            scopeCombo.setSelectedIndex(scopeMode);
            scopeCombo.setMaximumSize(scopeCombo.getPreferredSize());
            scopeCombo.addActionListener(new java.awt.event.ActionListener(){
                public void actionPerformed(java.awt.event.ActionEvent e){
                    scopeMode=scopeCombo.getSelectedIndex();
                    scopeRegexField.setEnabled(scopeMode==SCOPE_CUSTOM);
                    saveMatchReplaceSettings();
                }
            });
            scopeRegexField.getDocument().addDocumentListener(new javax.swing.event.DocumentListener(){
                private void update(){
                    scopeCustomRegex=scopeRegexField.getText();
                    recompileScopePattern();
                    saveMatchReplaceSettings();
                }
                public void insertUpdate(javax.swing.event.DocumentEvent e){ update(); }
                public void removeUpdate(javax.swing.event.DocumentEvent e){ update(); }
                public void changedUpdate(javax.swing.event.DocumentEvent e){ update(); }
            });
            javax.swing.JPanel scopeRow=new javax.swing.JPanel(new java.awt.FlowLayout(java.awt.FlowLayout.LEFT, 0, 0));
            scopeRow.setAlignmentX(java.awt.Component.LEFT_ALIGNMENT);
            scopeRow.add(new javax.swing.JLabel("Apply match/replace & boolean policy to: "));
            scopeRow.add(scopeCombo);
            javax.swing.JPanel scopeRegexRow=new javax.swing.JPanel(new java.awt.FlowLayout(java.awt.FlowLayout.LEFT, 0, 0));
            scopeRegexRow.setAlignmentX(java.awt.Component.LEFT_ALIGNMENT);
            scopeRegexRow.add(new javax.swing.JLabel("Custom URL regex: "));
            scopeRegexRow.add(scopeRegexField);

            javax.swing.JPanel top=new javax.swing.JPanel();
            top.setLayout(new javax.swing.BoxLayout(top, javax.swing.BoxLayout.Y_AXIS));
            top.setBorder(javax.swing.BorderFactory.createTitledBorder("Options"));
            top.add(frmBox);
            top.add(debugBox);
            top.add(boolRow);
            top.add(scopeRow);
            top.add(scopeRegexRow);

            // Master banner on top, secondary options below it.
            javax.swing.JPanel north=new javax.swing.JPanel();
            north.setLayout(new javax.swing.BoxLayout(north, javax.swing.BoxLayout.Y_AXIS));
            masterBanner.setAlignmentX(java.awt.Component.LEFT_ALIGNMENT);
            top.setAlignmentX(java.awt.Component.LEFT_ALIGNMENT);
            north.add(masterBanner);
            north.add(top);
            panel.add(north, java.awt.BorderLayout.NORTH);

            model=new MRTableModel();
            final javax.swing.JTable table=new javax.swing.JTable(model);
            table.setFillsViewportHeight(true);
            panel.add(new javax.swing.JScrollPane(table), java.awt.BorderLayout.CENTER);

            javax.swing.JPanel buttons=new javax.swing.JPanel(new java.awt.FlowLayout(java.awt.FlowLayout.LEFT));
            javax.swing.JButton add=new javax.swing.JButton("Add");
            javax.swing.JButton edit=new javax.swing.JButton("Edit");
            javax.swing.JButton remove=new javax.swing.JButton("Remove");
            buttons.add(add);
            buttons.add(edit);
            buttons.add(remove);
            panel.add(buttons, java.awt.BorderLayout.SOUTH);

            add.addActionListener(new java.awt.event.ActionListener(){
                public void actionPerformed(java.awt.event.ActionEvent e){
                    MatchReplaceRule r=editRuleDialog(new MatchReplaceRule(true, true, "both", "", ""));
                    if (r!=null){
                        mrRules.add(r);
                        model.fireTableDataChanged();
                        saveMatchReplaceSettings();
                    }
                }
            });
            edit.addActionListener(new java.awt.event.ActionListener(){
                public void actionPerformed(java.awt.event.ActionEvent e){
                    int row=table.getSelectedRow();
                    if (row<0 || row>=mrRules.size()){
                        return;
                    }
                    MatchReplaceRule cur=mrRules.get(row);
                    MatchReplaceRule r=editRuleDialog(new MatchReplaceRule(cur.enabled, cur.isString, cur.scope, cur.match, cur.replace));
                    if (r!=null){
                        mrRules.set(row, r);
                        model.fireTableDataChanged();
                        saveMatchReplaceSettings();
                    }
                }
            });
            remove.addActionListener(new java.awt.event.ActionListener(){
                public void actionPerformed(java.awt.event.ActionEvent e){
                    int row=table.getSelectedRow();
                    if (row<0 || row>=mrRules.size()){
                        return;
                    }
                    mrRules.remove(row);
                    model.fireTableDataChanged();
                    saveMatchReplaceSettings();
                }
            });

            callbacks.customizeUiComponent(panel);
        }

        @Override
        public String getTabCaption(){
            return "Oracle Forms M/R";
        }

        @Override
        public Component getUiComponent(){
            return panel;
        }

        // Modal Add/Edit dialog. Returns the edited rule, or null if cancelled
        // or the input was invalid and the user gave up.
        private MatchReplaceRule editRuleDialog(MatchReplaceRule seed){
            javax.swing.JComboBox<String> type=new javax.swing.JComboBox<String>(new String[]{"String (regex)","Integer (exact)"});
            type.setSelectedIndex(seed.isString?0:1);
            javax.swing.JComboBox<String> scope=new javax.swing.JComboBox<String>(new String[]{"both","request","response"});
            scope.setSelectedItem(seed.scope);
            javax.swing.JTextField match=new javax.swing.JTextField(seed.match, 24);
            javax.swing.JTextField replace=new javax.swing.JTextField(seed.replace, 24);
            javax.swing.JCheckBox enabled=new javax.swing.JCheckBox("Enabled", seed.enabled);

            javax.swing.JPanel form=new javax.swing.JPanel(new java.awt.GridLayout(0,2,4,4));
            form.add(new javax.swing.JLabel("Type:"));
            form.add(type);
            form.add(new javax.swing.JLabel("Scope:"));
            form.add(scope);
            form.add(new javax.swing.JLabel("Match (regex for String):"));
            form.add(match);
            form.add(new javax.swing.JLabel("Replace:"));
            form.add(replace);
            form.add(new javax.swing.JLabel(""));
            form.add(enabled);

            while (true){
                int res=javax.swing.JOptionPane.showConfirmDialog(panel, form, "Match/Replace rule",
                        javax.swing.JOptionPane.OK_CANCEL_OPTION, javax.swing.JOptionPane.PLAIN_MESSAGE);
                if (res!=javax.swing.JOptionPane.OK_OPTION){
                    return null;
                }
                boolean isString=type.getSelectedIndex()==0;
                String matchVal=match.getText();
                String replaceVal=replace.getText();
                if (isString){
                    try{
                        Pattern.compile(matchVal);
                    }catch(PatternSyntaxException pse){
                        javax.swing.JOptionPane.showMessageDialog(panel, "Invalid regular expression:\n"+pse.getMessage(),
                                "Invalid regex", javax.swing.JOptionPane.ERROR_MESSAGE);
                        continue;
                    }
                }else{
                    try{
                        Integer.parseInt(matchVal.trim());
                        Integer.parseInt(replaceVal.trim());
                    }catch(NumberFormatException nfe){
                        javax.swing.JOptionPane.showMessageDialog(panel, "Integer rules need whole numbers in both Match and Replace.",
                                "Invalid integer", javax.swing.JOptionPane.ERROR_MESSAGE);
                        continue;
                    }
                }
                return new MatchReplaceRule(enabled.isSelected(), isString, (String)scope.getSelectedItem(), matchVal, replaceVal);
            }
        }

        class MRTableModel extends javax.swing.table.AbstractTableModel {
            private final String[] cols={"Enabled","Type","Scope","Match","Replace"};
            @Override public int getRowCount(){ return mrRules.size(); }
            @Override public int getColumnCount(){ return cols.length; }
            @Override public String getColumnName(int c){ return cols[c]; }
            @Override public Class<?> getColumnClass(int c){ return c==0 ? Boolean.class : String.class; }
            @Override public boolean isCellEditable(int r, int c){ return c==0; }
            @Override public Object getValueAt(int r, int c){
                if (r<0 || r>=mrRules.size()){
                    return null;
                }
                MatchReplaceRule rule=mrRules.get(r);
                switch(c){
                    case 0: return rule.enabled;
                    case 1: return rule.isString?"String (regex)":"Integer";
                    case 2: return rule.scope;
                    case 3: return rule.match;
                    case 4: return rule.replace;
                }
                return null;
            }
            @Override public void setValueAt(Object val, int r, int c){
                if (c==0 && r>=0 && r<mrRules.size()){
                    mrRules.get(r).enabled=Boolean.TRUE.equals(val);
                    saveMatchReplaceSettings();
                    fireTableRowsUpdated(r, r);
                }
            }
        }
    }

    // Factory for the read-only structured tree view tab.
    class OracleFormsTreeTabFactory implements IMessageEditorTabFactory {
        @Override
        public IMessageEditorTab createNewInstance(IMessageEditorController controller, boolean editable){
            return new OracleFormsTreeTab(editable);
        }
    }

    // A message-editor tab that renders the deserialized Forms message as a JTree
    // (messages -> properties -> nested messages), with a filter box and a
    // right-click "show raw hex". On editable surfaces, leaf values can be edited
    // (double-click, or select + right-click "Edit value..."); edits forward
    // through the same serialization as the param tab (re-serialise requests,
    // byte-patch response strings).
    class OracleFormsTreeTab implements IMessageEditorTab {
        private final boolean editable;
        private final javax.swing.JPanel component;
        private final javax.swing.JTree tree;
        private final javax.swing.JTextField filterField;
        private byte[] currentMessage;
        private byte[] currentBody;
        private boolean currentIsRequest=true;
        // Accumulated edits (same key scheme as collectStrings/applyEdits) and a
        // dirty flag; cleared on setMessage.
        private final HashMap<String,String> paramStrings=new HashMap<String,String>();
        private final HashMap<String,Integer> paramInts=new HashMap<String,Integer>();
        private final HashMap<String,Boolean> paramBools=new HashMap<String,Boolean>();
        private boolean modified=false;

        OracleFormsTreeTab(boolean editable){
            this.editable=editable;
            component=new javax.swing.JPanel(new java.awt.BorderLayout());

            filterField=new javax.swing.JTextField();
            javax.swing.JPanel top=new javax.swing.JPanel(new java.awt.BorderLayout());
            top.add(new javax.swing.JLabel(" Filter: "), java.awt.BorderLayout.WEST);
            top.add(filterField, java.awt.BorderLayout.CENTER);
            component.add(top, java.awt.BorderLayout.NORTH);

            tree=new javax.swing.JTree(new javax.swing.tree.DefaultMutableTreeNode("No message"));
            component.add(new javax.swing.JScrollPane(tree), java.awt.BorderLayout.CENTER);

            filterField.getDocument().addDocumentListener(new javax.swing.event.DocumentListener(){
                public void insertUpdate(javax.swing.event.DocumentEvent e){ rebuild(); }
                public void removeUpdate(javax.swing.event.DocumentEvent e){ rebuild(); }
                public void changedUpdate(javax.swing.event.DocumentEvent e){ rebuild(); }
            });

            final javax.swing.JPopupMenu menu=new javax.swing.JPopupMenu();
            javax.swing.JMenuItem copyItem=new javax.swing.JMenuItem("Copy node text");
            javax.swing.JMenuItem hexItem=new javax.swing.JMenuItem("Show raw hex of body");
            menu.add(copyItem);
            menu.add(hexItem);
            copyItem.addActionListener(new java.awt.event.ActionListener(){
                public void actionPerformed(java.awt.event.ActionEvent e){
                    Object sel=tree.getLastSelectedPathComponent();
                    if (sel!=null){
                        java.awt.Toolkit.getDefaultToolkit().getSystemClipboard()
                            .setContents(new java.awt.datatransfer.StringSelection(sel.toString()), null);
                    }
                }
            });
            hexItem.addActionListener(new java.awt.event.ActionListener(){
                public void actionPerformed(java.awt.event.ActionEvent e){
                    String hex=currentBody==null ? "" : byteArrayToHex(currentBody);
                    javax.swing.JTextArea ta=new javax.swing.JTextArea(hex, 12, 64);
                    ta.setLineWrap(true);
                    ta.setEditable(false);
                    javax.swing.JOptionPane.showMessageDialog(component, new javax.swing.JScrollPane(ta),
                            "Raw Forms body hex", javax.swing.JOptionPane.PLAIN_MESSAGE);
                }
            });
            javax.swing.JMenuItem editItem=new javax.swing.JMenuItem("Edit value...");
            menu.add(editItem);
            editItem.addActionListener(new java.awt.event.ActionListener(){
                public void actionPerformed(java.awt.event.ActionEvent e){ editSelectedLeaf(); }
            });
            tree.setComponentPopupMenu(menu);

            // Double-click an editable leaf to edit it in place.
            tree.addMouseListener(new java.awt.event.MouseAdapter(){
                public void mousePressed(java.awt.event.MouseEvent e){
                    if (e.getClickCount()==2){
                        javax.swing.tree.TreePath p=tree.getPathForLocation(e.getX(), e.getY());
                        if (p!=null){
                            tree.setSelectionPath(p);
                            editSelectedLeaf();
                        }
                    }
                }
            });

            callbacks.customizeUiComponent(component);
        }

        @Override
        public String getTabCaption(){ return "Oracle Forms Tree"; }
        @Override
        public java.awt.Component getUiComponent(){ return component; }
        @Override
        public boolean isEnabled(byte[] content, boolean isRequest){ return true; }
        @Override
        public boolean isModified(){ return modified; }
        @Override
        public byte[] getSelectedData(){ return null; }
        @Override
        public byte[] getMessage(){
            if (!editable || !modified || currentMessage==null){
                return currentMessage;
            }
            List<String> httpHeaders=currentIsRequest
                ? helpers.analyzeRequest(currentMessage).getHeaders()
                : helpers.analyzeResponse(currentMessage).getHeaders();
            // currentBody is the original (unedited) body captured in setMessage().
            return currentIsRequest
                ? reserializeRequestBody(currentBody, httpHeaders, paramStrings, paramInts, paramBools, currentMessage)
                : patchResponseBody(currentBody, httpHeaders, paramStrings, paramInts, currentMessage);
        }

        @Override
        public void setMessage(byte[] content, boolean isRequest){
            currentMessage=content;
            currentIsRequest=isRequest;
            // A new message display starts with a clean edit set.
            paramStrings.clear(); paramInts.clear(); paramBools.clear();
            modified=false;
            if (content==null){
                currentBody=null;
                tree.setModel(new javax.swing.tree.DefaultTreeModel(new javax.swing.tree.DefaultMutableTreeNode("No message")));
                return;
            }
            int bodyOffset;
            if (isRequest){
                bodyOffset=helpers.analyzeRequest(helpers.buildHttpService("dummyhost",1234,false),content).getBodyOffset();
            }else{
                bodyOffset=helpers.analyzeResponse(content).getBodyOffset();
            }
            currentBody=Arrays.copyOfRange(content, bodyOffset, content.length);
            rebuild();
        }

        private void rebuild(){
            javax.swing.tree.DefaultMutableTreeNode root=
                new javax.swing.tree.DefaultMutableTreeNode("Oracle Forms "+(currentIsRequest?"request":"response"));
            if (currentBody!=null){
                try{
                    String[] as=new String[256];
                    ByteArrayInputStream bis=new ByteArrayInputStream(currentBody);
                    DataInputStream dis=new DataInputStream(bis);
                    Message m;
                    int idx=0;
                    while((m=Message.readDetails(dis,as))!=null){
                        root.add(buildMessageNode(m, "Message "+idx+" (size "+m.size()+")", "_"+idx));
                        idx++;
                    }
                }catch(EOFException eofe){
                    // normal end of stream
                }catch(Exception ex){
                    root.add(new javax.swing.tree.DefaultMutableTreeNode("[parse error: "+ex+"]"));
                }
            }
            String f=filterField.getText().trim().toLowerCase();
            if (!f.isEmpty()){
                filterTree(root, f);
            }
            tree.setModel(new javax.swing.tree.DefaultTreeModel(root));
            for (int i=0;i<tree.getRowCount();i++){
                tree.expandRow(i);
            }
        }

        private javax.swing.tree.DefaultMutableTreeNode buildMessageNode(Message m, String label, String path){
            javax.swing.tree.DefaultMutableTreeNode node=new javax.swing.tree.DefaultMutableTreeNode(label);
            for (int i=0;i<m.size();i++){
                Object v=m.getValueAt(i);
                int t=m.getPropertyTypeAt(i);
                Object propId=m.getPropertyAt(i);
                if (v instanceof Message){
                    node.add(buildMessageNode((Message)v, "Property "+i+" [id="+propId+"] (nested message)", path+"_"+i));
                }else{
                    String tlabel=(t==1?"String":(t==3?"Integer":(v instanceof Boolean?"Boolean":"type"+t)));
                    // Editable leaves: String (type 1), Integer (type 3), Boolean;
                    // keyed like collectStrings so the shared write-back finds them.
                    String keyPrefix=(t==1?"string":(t==3?"int":(v instanceof Boolean?"bool":null)));
                    if (keyPrefix!=null){
                        String key=keyPrefix+path+"_"+i;
                        String labelPrefix=(t==3?"[int] ":"")+"Property "+i+" [id="+propId+"] "+tlabel+": ";
                        EditableTreeLeaf leaf=new EditableTreeLeaf(key, labelPrefix, editedValueFor(key, v));
                        leaf.edited=paramStrings.containsKey(key)||paramInts.containsKey(key)||paramBools.containsKey(key);
                        node.add(leaf);
                    }else{
                        String val=(v==null?"null":v.toString());
                        node.add(new javax.swing.tree.DefaultMutableTreeNode(
                            "Property "+i+" [id="+propId+"] "+tlabel+": "+val));
                    }
                }
            }
            return node;
        }

        // The value to display for a leaf: the pending edit if any, else the
        // original parsed value. Keeps edits visible across filter rebuilds.
        private Object editedValueFor(String key, Object orig){
            if (paramStrings.containsKey(key)) return paramStrings.get(key);
            if (paramInts.containsKey(key)) return paramInts.get(key);
            if (paramBools.containsKey(key)) return paramBools.get(key);
            return orig;
        }

        // Edit the selected editable leaf via a type-appropriate dialog and record
        // the change in the edit maps. Responses only byte-patch strings, so int/
        // bool leaves are not editable there.
        private void editSelectedLeaf(){
            if (!editable){
                return;
            }
            Object sel=tree.getLastSelectedPathComponent();
            if (!(sel instanceof EditableTreeLeaf)){
                return;
            }
            EditableTreeLeaf leaf=(EditableTreeLeaf)sel;
            boolean isInt=leaf.key.startsWith("int");
            boolean isBool=leaf.key.startsWith("bool");
            if (!currentIsRequest && !leaf.key.startsWith("string")){
                javax.swing.JOptionPane.showMessageDialog(component,
                    "Only String values are editable on responses (integers/booleans can't be byte-patched).",
                    "Not editable", javax.swing.JOptionPane.INFORMATION_MESSAGE);
                return;
            }
            if (isBool){
                int r=javax.swing.JOptionPane.showConfirmDialog(component,
                    "Set boolean value to TRUE?  (No = false)", "Edit boolean",
                    javax.swing.JOptionPane.YES_NO_CANCEL_OPTION);
                if (r!=javax.swing.JOptionPane.YES_OPTION && r!=javax.swing.JOptionPane.NO_OPTION){
                    return;
                }
                Boolean nv=(r==javax.swing.JOptionPane.YES_OPTION);
                paramBools.put(leaf.key, nv);
                leaf.value=nv;
            }else{
                String cur=(leaf.value==null?"":leaf.value.toString());
                String input=(String)javax.swing.JOptionPane.showInputDialog(component,
                    "New value for "+leaf.key+":", "Edit value",
                    javax.swing.JOptionPane.PLAIN_MESSAGE, null, null, cur);
                if (input==null){
                    return; // cancelled
                }
                if (isInt){
                    try{
                        Integer nv=Integer.valueOf(input.trim());
                        paramInts.put(leaf.key, nv);
                        leaf.value=nv;
                    }catch(NumberFormatException nfe){
                        javax.swing.JOptionPane.showMessageDialog(component,
                            "\""+input+"\" is not a whole number.", "Invalid integer",
                            javax.swing.JOptionPane.ERROR_MESSAGE);
                        return;
                    }
                }else{
                    paramStrings.put(leaf.key, input);
                    leaf.value=input;
                }
            }
            leaf.edited=true;
            modified=true;
            ((javax.swing.tree.DefaultTreeModel)tree.getModel()).nodeChanged(leaf);
        }

        // Tree leaf carrying the edit key + label so its value can be edited in
        // place. toString() renders "<label prefix><value>[ (edited)]".
        class EditableTreeLeaf extends javax.swing.tree.DefaultMutableTreeNode {
            final String key;
            final String labelPrefix;
            Object value;
            boolean edited=false;
            EditableTreeLeaf(String key, String labelPrefix, Object value){
                this.key=key; this.labelPrefix=labelPrefix; this.value=value;
            }
            @Override public String toString(){
                return labelPrefix+(value==null?"null":value.toString())+(edited?"   (edited)":"");
            }
        }

        // Prune the tree to nodes whose label (or a descendant's) contains the
        // filter. Returns true if the node was kept.
        private boolean filterTree(javax.swing.tree.DefaultMutableTreeNode node, String filterLower){
            boolean selfMatch=node.toString().toLowerCase().contains(filterLower);
            java.util.List<javax.swing.tree.DefaultMutableTreeNode> children=new ArrayList<javax.swing.tree.DefaultMutableTreeNode>();
            for (int i=0;i<node.getChildCount();i++){
                children.add((javax.swing.tree.DefaultMutableTreeNode)node.getChildAt(i));
            }
            boolean anyChildKept=false;
            for (javax.swing.tree.DefaultMutableTreeNode c: children){
                if (filterTree(c, filterLower)){
                    anyChildKept=true;
                }else{
                    node.remove(c);
                }
            }
            return selfMatch || anyChildKept;
        }
    }
}
