//program for server application 
import java.rmi.*; 
import java.rmi.server.*; 
import java.rmi.registry.*; 
import java.io.*;
public class SearchServer 
{ 
	public static void main(String args[])  throws Exception
	{ 
        System.getProperties().put("java.rmi.server.logCalls","true");

        if (System.getSecurityManager() == null) {
            System.setSecurityManager(new SecurityManager());
        }


		try
		{ 
            FileOutputStream logFile = new FileOutputStream("/tmp/ds2-assign-log.txt");
            RemoteServer.setLog(logFile);
			// Create an object of the interface 
			// implementation class 
            System.out.println("LAUNCHING SERVER");
			Search obj = new SearchQuery(); 

			// rmiregistry within the server JVM with 
			// port number 1900 
            System.out.println("REGISTERING");
			Registry registry = LocateRegistry.createRegistry(1900); 

			// Binds the remote object by the name 
			// geeksforgeeks 
            System.out.println("REBINDING");
			registry.rebind("rmi://0.0.0.0:1900"+ 
						"/geeksforgeeks",obj); 
		} 
		catch(Exception ae) 
		{ 
			System.out.println(ae); 
            throw ae;
		} 
	} 
} 
