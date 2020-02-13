// Java program to implement the Search interface 
import java.rmi.*; 
import java.rmi.server.*; 
public class SearchQuery extends UnicastRemoteObject 
                         implements Search 
{ 
    // Default constructor to throw RemoteException 
    // from its parent constructor 
    SearchQuery() throws RemoteException 
    { 
        super(); 
        System.out.println("CONSTRUCTING SEARCH QUERY");
        System.out.println("CONSTRUCTING SEARCH QUERY");
        System.out.println("CONSTRUCTING SEARCH QUERY");
        System.out.println("CONSTRUCTING SEARCH QUERY");
        System.out.println("CONSTRUCTING SEARCH QUERY");
    } 
  
    // Implementation of the query interface 
    public String query(String search) 
                       throws RemoteException 
    { 
        String result; 
        System.out.println("IN QUERY...");
        System.out.println("IN QUERY...");
        System.out.println("IN QUERY...");
        System.out.println("IN QUERY...");
        System.out.println("IN QUERY...");
        if (search.equals("Reflection in Java")) 
            result = "Found"; 
        else
            result = "Not Found"; 
  
        System.out.println("RETURNING RESULT");
        System.out.println("RETURNING RESULT");
        System.out.println("RETURNING RESULT");
        System.out.println("RETURNING RESULT");
        System.out.println("RETURNING RESULT");
        return result; 
    } 
} 
