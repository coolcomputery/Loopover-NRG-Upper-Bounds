import java.util.*;
import java.math.BigInteger;
public class LoopoverNRGLowerBound {
    private static int lower_bound(int N) {
        int[] S=new int[N/2+1];
        for (int i=1; i<=N/2; i++)
            S[i]=2*i==N?1:2;
        List<BigInteger[]> dp=new ArrayList<>();
        //dp(m,k)=# canonical move sequences w/ m moves, k syllables, first syllable is horizontal
        //dp(0,0)=1
        //dp(m,k)=SUM_{n=1 to len(S)-1} dp(m-n,k-1)*S[n]
        //let T(m)=# canonical move seq.s w/ <=m moves
        //then T(m)=1+2*(SUM_{1<=k<=n<=m} dp(n,k))
        BigInteger tot=BigInteger.ONE, target=BigInteger.ONE;
        for (int i=2; i<=N*N; i++)
            target=target.multiply(new BigInteger(""+i));
        target=target.divide(new BigInteger("2"));
        for (int m=0;; m++) {
            BigInteger[] row=new BigInteger[m+1];
            dp.add(row);
            for (int k=0; k<=m; k++) {
                if (k==0)
                    row[0]=m==0?BigInteger.ONE:BigInteger.ZERO;
                else {
                    row[k]=BigInteger.ZERO;
                    for (int n=1; n<=m && n<S.length; n++)
                        if (m-n>=k-1)
                            row[k]=row[k].add(dp.get(m-n)[k-1].multiply(new BigInteger(""+S[n])));
                }
                if (m>0)
                    tot=tot.add(row[k].multiply(new BigInteger("2")));
            }
            if (tot.compareTo(target)>=0) {
                return m;
            }
        }
    }
    public static void main(String[] args) {
        for (int N=4; N<=20; N++)
            System.out.printf("%3d%5d%n",N,lower_bound(N));
    }
}
