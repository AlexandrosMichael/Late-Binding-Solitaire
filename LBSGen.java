import java.util.Random ;

/*
 *  Generate instances of Late Binding Solitaire.
 */
public class LBSGen {

  public static void main (String[] args) {
    if (args.length != 2) {
      System.out.println("usage: java LBSGen n seed") ;
      return ;
    }
    
    int n = Integer.parseInt(args[0]) ;
    int seed = Integer.parseInt(args[1]) ;
    
    int[] cards = new int[52] ;
    for (int i = 0; i < 52; i++) {
      cards[i] = i ;
    }
    
    // Choose the sequence uniformly at random
    // NB random.nextInt(k) gives a value in range 0..k-1
    Random random = new Random(seed) ;
    for (int i = 0; i < n-1; i++) {
      int temp = cards[i] ;
      int index = i+random.nextInt(52-i) ;
      cards[i] = cards[index] ;
      cards[index] = temp ;
    }
    
    // output
    System.out.println("$ LBS instance with n = "+n+", seed = "+seed) ;
    System.out.print("letting cards be [") ;
    for (int i = 0; i < n; i++) {
      System.out.print(cards[i]) ;
      if (i < n-1)
        System.out.print(",") ;
    }
    System.out.println("]") ;
  }
}
