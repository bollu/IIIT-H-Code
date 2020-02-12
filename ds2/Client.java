//program for client application 
import java.rmi.*; 
import java.io.*;
import java.util.*; 

public class Client
{ 
    public static void main(String args[]) 
    { 
        String answer,q="Reflection in JavaXX"; 
        try
        { 

            IGraph g = 
                (IGraph)Naming.lookup("rmi://localhost:1900"+ 
                                      "/geeksforgeeks"); 
            BufferedReader br = 
                new BufferedReader(new InputStreamReader(System.in));

            String str;
            while((str=br.readLine())!=null && str.length()!=0) {
                String []words = str.split(" ");
                if (words[0].equals("add_graph")) {
                    System.out.println("ADDING graph");
                    g.addGraph(words[1], 
                            Integer.parseInt(words[2]));
                }
                else if (words[0].equals("add_edge")) {
                    System.out.println("ADDING edge");
                    g.addEdge(words[1], 
                            Integer.parseInt(words[2]),
                            Integer.parseInt(words[3]),
                            Integer.parseInt(words[4]));
                }
                else if (words[0].equals("get_mst")) {
                    List<VertexPair> vs = g.getMST(words[1]);
                    System.out.println("GET mst");
                }

            }


            // lookup method to find reference of remote object 
            // IGraph g = 
            //     (IGraph)Naming.lookup("rmi://localhost:1900"+ 
            //                           "/geeksforgeeks"); 
            // answer = g.query(q); 
            // System.out.println("Q: " + q + "|A: " + answer);
        } 
        catch(Exception ae) 
        { 
            System.out.println(ae); 
        } 
    } 
} 
