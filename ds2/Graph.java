// Java program to implement the Search interface 
import java.rmi.*; 
import java.rmi.server.*; 
import java.util.*; 

public class Graph 
    extends UnicastRemoteObject 
    implements IGraph 
{ 
    Map<String, Map<Integer, List<VertexPair>>> graph2adj;
    Map<String, Integer> graph2nvertex;

    // Default constructor to throw RemoteException 
    // from its parent constructor 
    Graph() throws RemoteException 
    { 
        super(); 
        graph2adj = new HashMap<>();
        graph2nvertex = new HashMap<>();
    } 
  
    public void addGraph(String name, int n) 
            throws RemoteException {
            Map<Integer, List<VertexPair>> adj = new HashMap<>();
            for(int i = 1; i <= n; ++i) {
                adj.put(i, new ArrayList<VertexPair>());
            }


            graph2adj.put(name, adj);
            graph2nvertex.put(name, n);
    }
    
    public void addEdge(String n, int u, int v, int w) 
            throws RemoteException {
            Map<Integer, List<VertexPair>> adj = graph2adj.get(n);
            List<VertexPair> adju = adj.get(u);
            adju.add(new VertexPair(u, v, w));
            adj.put(u, adju);
            graph2adj.put(n, adj);
    }

    public List<VertexPair> getMST(String n) 
            throws RemoteException { 
            Map<Integer, List<VertexPair>> adj = graph2adj.get(n);

            int totalw = 0;
            int nvseen = 0;

            Set<Integer> vseen = new HashSet<>();
            List<VertexPair> mst = new ArrayList<>();
            PriorityQueue<VertexPair> q = new PriorityQueue<>();

            // we need to keep track of how much data we have _now_.
            // spurious edge so we include the first vertex.
            q.add(new VertexPair(1, 1, 0));
            while (!q.isEmpty()) {
                // get closest vertex
                VertexPair e = q.remove();
                // only care about "_ -> v" vertex
                if (vseen.contains(e.v)) { continue; }
                vseen.add(e.v);

                nvseen += 1;
                totalw += e.w;


                // add whole adjacency list of v
                List<VertexPair> vadj = adj.get(e.v);
                for (int i = 0; i < vadj.size(); ++i) { // u -> v
                    q.add(vadj.get(i));
                }

                // add the current edge into the mst.
                mst.add(e);
            }

            if (nvseen < graph2nvertex.get(n)) { 
                totalw = -1;
            } 

            System.out.println("totalw: " + Integer.toString(totalw) + "|nvseen: " + 
                    Integer.toString(nvseen));

            // return totalw;
            return mst;
            
    }
} 

