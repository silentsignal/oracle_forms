package burp;

import java.awt.Component;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
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
        callbacks.registerScannerInsertionPointProvider(this);
        callbacks.registerHttpListener(this);
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
    // Before re-serialising we walk the whole tree and replace every IndexTag
    // with the concrete string it resolves to (IndexTag.toString() yields that
    // string). The single shared FormsDispatcher then rebuilds proper
    // back-references on the way out.
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
    // DataOutput.writeUTF() (readDetails reads them with readUTF). We use this
    // to find and replace a literal in the raw body without re-serialising.
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

    @Override
    public void processHttpMessage(int toolFlag, boolean messageIsRequest, IHttpRequestResponse messageInfo){
        if(!messageIsRequest){  // We don't care if it's not a request
            return;
        }

        byte[] msg=messageInfo.getRequest();
        IRequestInfo rInfo=helpers.analyzeRequest(messageInfo);

        if (rInfo.getUrl().toString().indexOf("/lservlet") == -1 || rInfo.getMethod() != "POST"){ // We don't care if it's not a POST for Forms
            return; 
        }

        byte[] handshakeBody=Arrays.copyOfRange(msg, rInfo.getBodyOffset(), rInfo.getBodyOffset() + 4);
        if (Arrays.equals(handshakeBody, new byte[] {0x47, 0x44, 0x61, 0x79} )){ // We don't care about the intial handshake
            stdout.println("Ignoring handshake in HTTP Listener");
            return;
        }

        byte[] handshakeBody1=Arrays.copyOfRange(msg, rInfo.getBodyOffset(), rInfo.getBodyOffset() + 8);
        if (Arrays.equals(handshakeBody1, new byte[] {0x4e, 0x55, 0x4c, 0x4c, 0x50, 0x4f, 0x53, 0x54} )){ // We don't care about NULLPOSTs
            stdout.println("Ignoring NULLPOST in HTTP Listener");
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
        }
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
                    stdout.println("\nReached EOFin setMessage()");
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
                    while((m=Message.readDetails(dis,as))!=null){
                        for (int i=0;i<m.size();i++){
                            IParameter param;
                            switch(m.getPropertyTypeAt(i)){
                                case 1: // String
                                    param=helpers.buildParameter(String.format("string_%d_%d",m_id,i), helpers.urlEncode(m.getValueAt(i).toString()), IParameter.PARAM_BODY);
                                    dummyRequest=helpers.addParameter(dummyRequest, param);
                                    break;
                                case 3: // Integer
                                    param=helpers.buildParameter(String.format("int_%d_%d",m_id,i), m.getValueAt(i).toString(), IParameter.PARAM_BODY);
                                    dummyRequest=helpers.addParameter(dummyRequest, param);
                                    break;
                            }
                        }
                        m_id++;
                    }
                    dummyRequest=helpers.addParameter(dummyRequest, helpers.buildParameter("original", byteArrayToHex(body), IParameter.PARAM_BODY));
                    txtInput.setText(dummyRequest);
                    txtInput.setEditable(editable);
                }catch(EOFException eofe){
                    stdout.println("\nReached EOFin setMessage()");
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
            stdout.println("[*] Setting message from dummy POST");

            IRequestInfo dummyRequest=helpers.analyzeRequest(txtInput.getText());
            HashMap<String,String> paramStrings=new HashMap<String,String>(); // Not necessarily optimal, but code is nicer...
            HashMap<String,Integer> paramInts=new HashMap<String,Integer>(); 
            for (IParameter p: dummyRequest.getParameters()){
                if (p.getName().startsWith("string_")){
                    stdout.println("[+] Found string parameter: "+p.getName()+"="+p.getValue().toString());
                    paramStrings.put(p.getName(), helpers.urlDecode(p.getValue()));
                }else if(p.getName().startsWith("int_")){
                    stdout.println("[+] Found int parameter: "+p.getName()+"="+p.getValue().toString());
                    paramInts.put(p.getName(), Integer.parseInt(p.getValue()));
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
            // dispatcher must also live for the whole stream. A fresh dispatcher
            // per message resets the table and desynchronises multi-message
            // streams, yielding a corrupt stream. It only worked before because
            // the messages here are short.
            FormsDispatcher dispatcher=new FormsDispatcher();
            boolean serialisationFailed=false;
            try{
                stdout.println("[*] Enter stream parser");
                while((m=Message.readDetails(dis,as))!=null){
                    stdout.println("[*] Message start, ID: "+m_id+ " size: "+m.size());
                    for (int i=0;i<m.size();i++){
                        stdout.println("[*] Property type at "+i+" is "+m.getPropertyTypeAt(i));
                        if (m.getPropertyTypeAt(i) == 1){
                            String stringKey=String.format("string_%d_%d",m_id,i);
                            if (paramStrings.containsKey(stringKey)){
                                String newVal=paramStrings.get(stringKey);
                                Object origVal=m.getValueAt(i);
                                // Only touch values the user actually changed.
                                if (origVal==null || !newVal.equals(origVal.toString())){
                                    stdout.println("[+] Setting String value for "+stringKey);
                                    m.setValueAt(i, newVal);
                                }
                            }
                        }
                        else if (m.getPropertyTypeAt(i) == 3){
                            String intKey=String.format("int_%d_%d",m_id,i);
                            if (paramInts.containsKey(intKey)){
                                Integer newVal=paramInts.get(intKey);
                                Object origVal=m.getValueAt(i);
                                if (origVal==null || !newVal.toString().equals(origVal.toString())){
                                    stdout.println("[+] Setting Integer value for "+intKey);
                                    m.setValueAt(i, newVal);
                                }
                            }
                        }
                    }
                    resolveIndexTags(m);
                    m.writeDetails(dispatcher, dos);
                    m_id++;
                }

            }catch(EOFException eofe){
                stdout.println("\nReached EOF in getMessage()");
            }catch(IOException e){
                stdout.println("Message IOException");
                e.printStackTrace(stdout);
            }catch(RuntimeException re){
                // e.g. an IndexTag that could not be resolved. Rather than hand
                // Burp a truncated/corrupt body, forward the original message
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
                    for (int i=0;i<m.size();i++){
                        Object v=m.getValueAt(i);
                        if (v==null){
                            continue;
                        }
                        if (m.getPropertyTypeAt(i)==1){
                            origStrings.put(String.format("string_%d_%d",m_id,i), v.toString());
                        }else if (m.getPropertyTypeAt(i)==3){
                            try{
                                origInts.put(String.format("int_%d_%d",m_id,i), Integer.valueOf(v.toString()));
                            }catch(NumberFormatException nfe){}
                        }
                    }
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
                stdout.println("Adding message as potential insertion point");
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
                stdout.println("\nReached EOF in getInsertionPoints()");
        }catch(IOException e){
            stdout.println("Scanner Message IOException");
        }catch(IllegalArgumentException iae){
            stdout.println("Scanner Message IllegalArgumentException");
        }
        stdout.println("Supplied "+insertionPoints.size()+" insertion points");
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
            
            stdout.println("buildRequest called");
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
                stdout.println("\nReached EOF in buildRequest");
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
            stdout.println("Scanner request built: "+byteArrayToHex(res));
            return helpers.buildHttpMessage(rInfo.getHeaders(), baos.toByteArray());
        }

        @Override
        public int[] getPayloadOffsets(byte[] payload) {
            return null;
        }

        @Override
        public byte getInsertionPointType() {
            stdout.println("Insertion Point Type queried");
            return INS_PARAM_BODY;
        }
        
    }
}
