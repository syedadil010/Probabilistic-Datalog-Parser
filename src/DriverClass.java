import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;



public class DriverClass {
	
	public static void main(String args[]) throws NumberFormatException, IOException
	{
		
		JDatalog seminaive=new JDatalog();
		Naive_Jdatalog naive=new Naive_Jdatalog();
		BufferedReader br=new BufferedReader(new InputStreamReader(System.in));
		
		System.out.println("Enter 1 for naive 2 for seminaive");
		
	
		
		int num=Integer.parseInt(br.readLine());
		switch(num)
		{
		case 1:
			{
				naive.startup_naive(args);
			    break;
			}
		case 2:
		{
			    seminaive.startup_seminaive(args);
			    break;
		}
		default:
			   System.out.println("Please enter either 1 for naive or 2 for seminaive");
		}
		
		
		
		
	}

}
