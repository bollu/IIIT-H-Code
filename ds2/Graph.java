// Java program to implement the Search interface 
import java.rmi.*; 
import java.rmi.server.*; 
import java.util.*; 

public class Graph 
    extends UnicastRemoteObject 
    implements IGraph 
{ 
    Map<String, List<VertexPair>> graph2edges;
    Map<String, Integer> graph2nvertex;

    // Default constructor to throw RemoteException 
    // from its parent constructor 
    Graph() throws RemoteException 
    { 
        super(); 
        graph2edges = new HashMap<>();
        graph2nvertex = new HashMap<>();
    } 
  
    public void addGraph(String name, int n) 
            throws RemoteException {
            graph2edges.put(name, new ArrayList<VertexPair>());
            graph2nvertex.put(name, n);
    }
    
    public void addEdge(String n, int u, int v, int w) 
            throws RemoteException {
            List<VertexPair> g = graph2edges.get(n);
            g.add(new VertexPair(u, v, w));
    }

    public List<VertexPair> getMST(String n) 
            throws RemoteException { 
            List<VertexPair> g = graph2edges.get(n);
            return g;
            
    }
} 

