//program for client application 
import java.rmi.*; 
import java.io.*;
import java.util.*; 

public class Client
{ 
    static boolean debug  = true;
    public static void main(String args[]) 
    { 
        try
        { 
            String connectpath = "rmi://" + args[0] + ":" + args[1] + "/geeksforgeeks";
            if (debug) { System.out.println("connecting to: " 
                    + "|" + connectpath + "|"); }
            IGraph g = 
                (IGraph)Naming.lookup(connectpath);
            BufferedReader br = 
                new BufferedReader(new InputStreamReader(System.in));

            String str;
            while((str=br.readLine())!=null && str.length()!=0) {
                String []words = str.split(" ");
                if (words[0].equals("add_graph")) {
                    if (debug) { System.out.println("ADDING graph"); }
                    g.addGraph(words[1], 
                            Integer.parseInt(words[2]));
                }
                else if (words[0].equals("add_edge")) {
                    if (debug) { System.out.println("ADDING edge"); }
                    g.addEdge(words[1], 
                            Integer.parseInt(words[2]),
                            Integer.parseInt(words[3]),
                            Integer.parseInt(words[4]));
                    g.addEdge(words[1], 
                            Integer.parseInt(words[3]),
                            Integer.parseInt(words[2]),
                            Integer.parseInt(words[4]));
                }
                else if (words[0].equals("get_mst")) {
                    int totalw = g.getMST(words[1]);
                    System.out.println(totalw);
                }

            }
        } 
        catch(Exception ae) 
        { 
            System.out.println(ae); 
            ae.printStackTrace(System.out);

        } 
    } 
} 
