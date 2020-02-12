// Creating a Search interface 
import java.rmi.*; 
import java.util.*; 

public interface IGraph extends Remote 
{ 
    // Declaring the method prototype 
    public void addGraph(String name, int n) 
            throws RemoteException;
    public void addEdge(String n, int u, int v, int w) 
            throws RemoteException;
    public List<VertexPair> getMST(String n) 
            throws RemoteException;
} 

