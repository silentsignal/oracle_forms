package burp;

import oracle.forms.engine.Message;

import java.io.PrintWriter;
import java.util.ArrayList;

public class OFSMessage {
    private Integer[] intProperties;
    private String[] stringProperties;
    private Boolean[] booleanProperties;
    private OFSMessage[] messageProperties;
    private OFSMessage(Integer[] intp, String[] stringp, Boolean[] boolp, OFSMessage[] msgp){
        intProperties=intp;
        stringProperties=stringp;
        booleanProperties=boolp;
        messageProperties=msgp;
    }
    public static OFSMessage createOFSMessage(Message msg, IBurpExtenderCallbacks callbacks){
        PrintWriter stdout = new PrintWriter(callbacks.getStdout(), true);
        stdout.println("[*] OFSMessage createOFSMessage");
        ArrayList<Integer> intarr=new ArrayList<Integer>();
        ArrayList<String> strarr=new ArrayList<String>();
        ArrayList<Boolean> boolarr=new ArrayList<Boolean>();
        ArrayList<OFSMessage> msgarr=new ArrayList<OFSMessage>();
        for (int i=0;i<msg.size();i++){
            int type = msg.getPropertyTypeAt(i);
            stdout.println("  [*] Property "+i+": "+msg.getValueAt(i)+" Type: "+type+"\n");
            if (type == 3){
                intarr.add((Integer)msg.getValueAt(i));
            }else{
                intarr.add(null);
            }
            if (type == 1){
                strarr.add(msg.getValueAt(i).toString());
            }else{
                strarr.add(null);
            }
            if (type == 13){
                if (msg.getValueAt(i).toString() == "true"){
                    boolarr.add(Boolean.TRUE);
                }else{
                    boolarr.add(Boolean.FALSE);
                }
            }else{
                boolarr.add(null);
            }
            if (type==8 && msg.getValueAt(i) instanceof Message){
                msgarr.add(OFSMessage.createOFSMessage((Message)msg.getValueAt(i), callbacks));
            }else{
                msgarr.add(null);
            }
        }
        Integer[] intp=new Integer[intarr.size()];
        String[] strp=new String[strarr.size()];
        Boolean[] boolp=new Boolean[boolarr.size()];
        OFSMessage[] msgp=new OFSMessage[msgarr.size()];

        return new OFSMessage(intarr.toArray(intp), strarr.toArray(strp), boolarr.toArray(boolp), msgarr.toArray(msgp));
    }
}
