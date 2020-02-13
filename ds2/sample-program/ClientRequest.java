//program for client application 
import java.rmi.*; 
public class ClientRequest 
{ 
	public static void main(String args[]) 
	{ 
		String answer,value="Reflection in Java"; 
        if (System.getSecurityManager() == null) {
            System.setSecurityManager(new SecurityManager());
        }

		try
		{ 
			// lookup method to find reference of remote object 
            System.out.println("Sending the Request");
			Search access = 
				(Search)Naming.lookup("rmi://10.42.0.1:1900"+ 
									"/geeksforgeeKs"); 
            System.out.println("Sent the Request");
			answer = access.query(value); 
			System.out.println("Article on " + value + 
							" " + answer+" at GeeksforGeeks"); 
		} 
		catch(Exception ae) 
		{ 
			System.out.println(ae); 
		} 
	} 
} 
