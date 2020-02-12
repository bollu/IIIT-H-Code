// Java program to implement the Search interface 
import java.rmi.*; 
import java.rmi.server.*; 
import java.util.*; 
public class Graph 
    extends UnicastRemoteObject 
    implements IGraph 
{ 
    Map<String, List<VertexPair>> graph2edges;

    // Default constructor to throw RemoteException 
    // from its parent constructor 
    Graph() throws RemoteException 
    { 
        super(); 
        graph2edges = new HashMap<>();
    } 
  
    // Implementation of the query interface 
    public String query(String search) 
                       throws RemoteException { 
        String result; 
        if (search.equals("Reflection in Java")) 
            result = "Found"; 
        else
            result = "Not Found"; 
  
        return result; 
    } 

    public void addGraph(String n) 
            throws RemoteException {
            graph2edges.put(n, new ArrayList<VertexPair>());
    }
    
    public void addEdge(String n, int u, int v, int w) 
            throws RemoteException {
            List<VertexPair> g = graph2edges.get(n);
            g.add(new VertexPair(u, v, w));
    }

    public List<VertexPair> getMST(String n) 
            throws RemoteException { 
            return new ArrayList<VertexPair>();
    }
} 

