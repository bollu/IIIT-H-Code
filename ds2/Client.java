//program for client application 
import java.rmi.*; 
public class Client
{ 
    public static void main(String args[]) 
    { 
        String answer,q="Reflection in JavaXX"; 
        try
        { 
            // lookup method to find reference of remote object 
            IGraph g = 
                (IGraph)Naming.lookup("rmi://localhost:1900"+ 
                                      "/geeksforgeeks"); 
            answer = g.query(q); 
            System.out.println("Q: " + q + "|A: " + answer);
        } 
        catch(Exception ae) 
        { 
            System.out.println(ae); 
        } 
    } 
} 

