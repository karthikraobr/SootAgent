package Intercept.HelloWorldAgent;

import java.util.Random;

/**
 * Hello world!
 *
 */
public class App 
{
	private static int getRandomInt() {
		Random random = new Random();
		return random.nextInt(100);
	}
    public static void main( String[] args )
    {
        System.out.println( "Hello World!" );
        int random = getRandomInt();
        if(random>0) {
        	random++;
        }
    }
}
