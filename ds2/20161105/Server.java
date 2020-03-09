//program for server application 
import java.rmi.*; 
import java.rmi.registry.*; 
public class Server 
{ 
    public static void main(String args[]) 
    { 
        try
        { 
            // Create an object of the interface 
            // implementation class 
            Graph g = new Graph(); 
  
            // rmiregistry within the server JVM with 
            // port number 1900 
            System.out.println("connecting to port: |" + args[0] + "|");
            LocateRegistry.createRegistry(Integer.parseInt(args[0])); 
  
            // Binds the remote object by the name 
            // geeksforgeeks 
            Naming.rebind("rmi://0.0.0.0:" + args[0] +  "/geeksforgeeks", g); 
        } 
        catch(Exception ae) 
        { 
            System.out.println(ae); 
        } 
    } 
} 

