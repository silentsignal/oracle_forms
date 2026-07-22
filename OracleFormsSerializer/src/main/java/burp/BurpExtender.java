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

    // Extension options.
    private volatile boolean debugEnabled=false;
    private static final String DEBUG_SETTING="oracle_forms_debug";
    private volatile boolean frmHighlightEnabled=true;
    private static final String FRM_HIGHLIGHT_SETTING="oracle_forms_frm_highlight";
    private static final Pattern FRM_ERROR_PATTERN=Pattern.compile("(?:FRM|ORA)-\\d+");

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
        callbacks.registerMessageEditorTabFactory(new OracleFormsTreeTabFactory()); // read-only structured tree view
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
                               java.util.Map<String,Integer> ints){
        for (int i=0;i<m.size();i++){
            Object v=m.getValueAt(i);
            if (v==null){
                continue;
            }
            if (v instanceof Message){
                collectStrings((Message)v, prefix+"_"+i, strings, ints); // descend into nested Message
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
                           java.util.Map<String,Integer> paramInts, PrintWriter stdout){
        for (int i=0;i<m.size();i++){
            Object v=m.getValueAt(i);
            if (v instanceof Message){
                applyEdits((Message)v, prefix+"_"+i, paramStrings, paramInts, stdout); // descend into nested Message
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

    // Responses cannot be re-serialised (see patchResponse()). Apply string
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

        // Automatic match/replace on the (validated) request body.
        if (hasApplicableRules(true)){
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
            highlightFormsErrors(messageInfo, body);
        }

        if (mrActive){
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
                    while((m=Message.readDetails(dis,as))!=null){
                        collectStrings(m, "_"+m_id, strings, ints);
                        m_id++;
                    }
                    for (java.util.Map.Entry<String,String> e: strings.entrySet()){
                        dummyRequest=helpers.addParameter(dummyRequest, helpers.buildParameter(e.getKey(), helpers.urlEncode(e.getValue()), IParameter.PARAM_BODY));
                    }
                    for (java.util.Map.Entry<String,Integer> e: ints.entrySet()){
                        dummyRequest=helpers.addParameter(dummyRequest, helpers.buildParameter(e.getKey(), e.getValue().toString(), IParameter.PARAM_BODY));
                    }
                    dummyRequest=helpers.addParameter(dummyRequest, helpers.buildParameter("original", byteArrayToHex(body), IParameter.PARAM_BODY));
                    txtInput.setText(dummyRequest);
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

            IRequestInfo dummyRequest=helpers.analyzeRequest(txtInput.getText());
            HashMap<String,String> paramStrings=new HashMap<String,String>(); // Not necessarily optimal, but code is nicer...
            HashMap<String,Integer> paramInts=new HashMap<String,Integer>();
            ArrayList<String> invalidInts=new ArrayList<String>();
            for (IParameter p: dummyRequest.getParameters()){
                if (p.getName().startsWith("string_")){
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
                }
            }

            // Don't silently drop bad integer input: tell the user which fields
            // could not be applied, both as a modal dialog (so it is impossible
            // to miss when forwarding) and as a Burp alert (persistent record).
            // The invalid fields keep their original value; any other edits in
            // the message are still applied.
            if (!invalidInts.isEmpty()){
                StringBuilder sb=new StringBuilder();
                sb.append("These integer field(s) do not contain a valid whole number and were NOT applied:\n\n");
                for (String s: invalidInts){
                    sb.append("    - ").append(s).append("\n");
                }
                sb.append("\nThey keep their original value. Enter a valid integer (e.g. 123) to change them.");
                String warning=sb.toString();
                callbacks.issueAlert(warning);
                javax.swing.JOptionPane.showMessageDialog(txtInput.getComponent(), warning,
                        "Oracle Forms Serializer - invalid integer input", javax.swing.JOptionPane.ERROR_MESSAGE);
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

            // Responses cannot be re-serialised: frmall.jar is the CLIENT
            // library, so Message.writeDetails() only knows how to emit
            // request-side constructs. Server->client messages carry types the
            // client merely decodes and never re-encodes (IndexTag, DeleteMask,
            // delta masks, ...), so writeDetails throws on them. Instead we
            // patch the edited string(s) directly into the original response
            // bytes and leave everything else untouched.
            if (!currentIsRequest){
                return patchResponse(body, httpHeaders, paramStrings, paramInts, stdout);
            }

            String[] as=new String[256];
            ByteArrayInputStream bis=new ByteArrayInputStream(body);
            DataInputStream dis=new DataInputStream(bis);
            int m_id=0;
            ByteArrayOutputStream baos=new ByteArrayOutputStream();
            DataOutputStream dos=new DataOutputStream(baos);
            Message m;
            // The Forms string table (the shared `as` array on the read side)
            // accumulates across EVERY message in the stream: repeated strings
            // are sent as 1-byte back-references into it. The write side keeps
            // its mirror of that table inside a single FormsDispatcher, so the
            // dispatcher must also live for the whole stream. A fresh
            // dispatcher per message resets the table and desynchronises
            // multi-message streams (i.e. responses), yielding a corrupt stream
            // that crashes the client and no longer re-deserialises. Requests
            // only got away with the old per-message dispatcher because they
            // are short.
            FormsDispatcher dispatcher=new FormsDispatcher();
            boolean serialisationFailed=false;
            try{
                debug("[*] Enter stream parser");
                while((m=Message.readDetails(dis,as))!=null){
                    debug("[*] Message start, ID: "+m_id+ " size: "+m.size());
                    // Apply edits recursively so strings/ints nested inside other
                    // Message objects are updated too, not just top-level ones.
                    // Only genuinely changed values are re-set (see applyEdits).
                    applyEdits(m, "_"+m_id, paramStrings, paramInts, stdout);
                    int resolved=resolveIndexTags(m);
                    if (resolved>0){
                        debug("[*] Resolved "+resolved+" IndexTag reference(s) before writing message "+m_id);
                    }
                    m.writeDetails(dispatcher, dos);
                    m_id++;
                }

            }catch(EOFException eofe){
                debug("\nReached EOF in getMessage()");
            }catch(IOException e){
                stdout.println("Message IOException");
                e.printStackTrace(stdout);
            }catch(RuntimeException re){
                // e.g. an IndexTag that could not be resolved. Rather than hand
                // Burp a truncated/corrupt body (which crashes the client and
                // breaks history rendering), forward the original message
                // untouched and make the failure visible.
                stdout.println("[!] Re-serialisation failed at message "+m_id+", forwarding original message unchanged:");
                re.printStackTrace(stdout);
                serialisationFailed=true;
            }
            if (serialisationFailed){
                return currentMessage;
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

        // Apply string edits to a response by patching the raw body in place
        // instead of re-serialising it (see getMessage() for why re-serialising
        // responses is impossible). We re-parse the original body only to learn
        // each editable property's original value, then find that literal's
        // writeUTF bytes in the body and swap in the new value's bytes. String
        // references are index-based, so changing a literal's length keeps the
        // rest of the stream valid.
        private byte[] patchResponse(byte[] body, List<String> httpHeaders,
                                     HashMap<String,String> paramStrings,
                                     HashMap<String,Integer> paramInts, PrintWriter stdout)
        {
            HashMap<String,String> origStrings=new HashMap<String,String>();
            HashMap<String,Integer> origInts=new HashMap<String,Integer>();
            String[] as=new String[256];
            try{
                ByteArrayInputStream bis=new ByteArrayInputStream(body);
                DataInputStream dis=new DataInputStream(bis);
                Message m;
                int m_id=0;
                while((m=Message.readDetails(dis,as))!=null){
                    collectStrings(m, "_"+m_id, origStrings, origInts); // same recursive keys as the editable surface
                    m_id++;
                }
            }catch(EOFException eofe){
                // normal end of stream
            }catch(Exception e){
                stdout.println("[!] Failed to parse original response body for patching; forwarding unchanged:");
                e.printStackTrace(stdout);
                return currentMessage;
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
            final javax.swing.JCheckBox master=new javax.swing.JCheckBox("Enable Oracle Forms match/replace", matchReplaceEnabled);
            master.addActionListener(new java.awt.event.ActionListener(){
                public void actionPerformed(java.awt.event.ActionEvent e){
                    matchReplaceEnabled=master.isSelected();
                    saveMatchReplaceSettings();
                }
            });
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
            javax.swing.JPanel top=new javax.swing.JPanel();
            top.setLayout(new javax.swing.BoxLayout(top, javax.swing.BoxLayout.Y_AXIS));
            top.setBorder(javax.swing.BorderFactory.createTitledBorder("Options"));
            top.add(master);
            top.add(frmBox);
            top.add(debugBox);
            panel.add(top, java.awt.BorderLayout.NORTH);

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
            return new OracleFormsTreeTab();
        }
    }

    // A read-only message-editor tab that renders the deserialized Forms message
    // as a JTree (messages -> properties -> nested messages), with a filter box
    // and a right-click "show raw hex". Recon aid for spotting object/menu IDs
    // and hidden items. Never modifies the message.
    class OracleFormsTreeTab implements IMessageEditorTab {
        private final javax.swing.JPanel component;
        private final javax.swing.JTree tree;
        private final javax.swing.JTextField filterField;
        private byte[] currentMessage;
        private byte[] currentBody;
        private boolean currentIsRequest=true;

        OracleFormsTreeTab(){
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
            tree.setComponentPopupMenu(menu);

            callbacks.customizeUiComponent(component);
        }

        @Override
        public String getTabCaption(){ return "Oracle Forms Tree"; }
        @Override
        public java.awt.Component getUiComponent(){ return component; }
        @Override
        public boolean isEnabled(byte[] content, boolean isRequest){ return true; }
        @Override
        public boolean isModified(){ return false; }
        @Override
        public byte[] getSelectedData(){ return null; }
        @Override
        public byte[] getMessage(){ return currentMessage; } // read-only

        @Override
        public void setMessage(byte[] content, boolean isRequest){
            currentMessage=content;
            currentIsRequest=isRequest;
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
                        root.add(buildMessageNode(m, "Message "+idx+" (size "+m.size()+")"));
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

        private javax.swing.tree.DefaultMutableTreeNode buildMessageNode(Message m, String label){
            javax.swing.tree.DefaultMutableTreeNode node=new javax.swing.tree.DefaultMutableTreeNode(label);
            for (int i=0;i<m.size();i++){
                Object v=m.getValueAt(i);
                int t=m.getPropertyTypeAt(i);
                Object propId=m.getPropertyAt(i);
                if (v instanceof Message){
                    node.add(buildMessageNode((Message)v, "Property "+i+" [id="+propId+"] (nested message)"));
                }else{
                    String tlabel=(t==1?"String":(t==3?"Integer":"type"+t));
                    String prefix=(t==3?"[int] ":"");
                    String val=(v==null?"null":v.toString());
                    node.add(new javax.swing.tree.DefaultMutableTreeNode(
                        prefix+"Property "+i+" [id="+propId+"] "+tlabel+": "+val));
                }
            }
            return node;
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
