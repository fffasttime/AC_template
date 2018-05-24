import java.math.BigDecimal;  
import java.math.BigInteger;  
import java.text.DecimalFormat;  
import java.util.Scanner;  
public class Main    
{    
    public static void main(String args[])    
    {  
        Scanner sca = new Scanner(System.in);  
        BigInteger a,b;  
        int c;//为小数设置精度  
        char op;//运算符  
        String s;  
        while(sca.hasNext()){  
            a = sca.nextBigInteger();  
            s = sca.next();  
            op = s.charAt(0);  
            b = sca.nextBigInteger();  
            if(op == '+')  
                System.out.println(a.add(b));  
            else if(op == '-')  
                System.out.println(a.subtract(b));  
            else if(op == '*')  
                System.out.println(a.multiply(b));  
            else{  
                BigDecimal t1,t2,eps;  
                String s1,s2,temp;  
                s1 = a.toString();  
                s2 = b.toString();  
                t1 = new BigDecimal(s1);  
                t2 = new BigDecimal(s2);  
                c = sca.nextInt();  
                eps = t1.divide(t2,c,4);  
                //System.out.println(a + " " + b + " " + c);    
                //System.out.println(t1.doubleValue() + " " + t2.doubleValue() + " " + c);  
                System.out.print(a.divide(b) +" "+ a.mod(b)+" ");  
                if(c != 0){  
                    temp = "0.";  
                    for(int i = 0; i < c; i++)  
                        temp += "0";  
                    DecimalFormat gd = new DecimalFormat(temp);  
                    System.out.println(gd.format(eps));  
                }  
                else  
                    System.out.println(eps);  
            }  
        }  
    }  
}  
