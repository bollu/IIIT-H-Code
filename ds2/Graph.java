// Java program to implement the Search interface 
import java.rmi.*; 
import java.rmi.server.*; 
public class Graph extends UnicastRemoteObject 
                         implements IGraph 
{ 
    // Default constructor to throw RemoteException 
    // from its parent constructor 
    Graph() throws RemoteException 
    { 
        super(); 
    } 
  
    // Implementation of the query interface 
    public String query(String search) 
                       throws RemoteException 
    { 
        String result; 
        if (search.equals("Reflection in Java")) 
            result = "Found"; 
        else
            result = "Not Found"; 
  
        return result; 
    } 
} 

