import java.util.*;
public class LoopoverNRGAlgorithmFinder {
    private static int mod(int n, int k) {
        return (n%k+k)%k;
    }
    private static int N;
    private static long st;
    private static int amt, bscr, streak;
    private static int[] seq;
    private static int dr, dc;
    private static Map<String,int[][]> results;
    private static void dfs(int idx) {
        //System.out.println(idx);
        if (idx==seq.length) {
            //System.out.println(Arrays.toString(freq));
            if (dr==0&&dc==0) {
                StringBuilder tmp=new StringBuilder();
                for (int i=0; i<seq.length; i++)
                    tmp.append(LoopoverNRGSetup.dirNames[seq[i]]);
                String alg=LoopoverNRGSetup.reduced(N,tmp.toString());
                int[][] ret=LoopoverNRGSetup.effect(N,alg);
                int scr=ret[0].length;
                if (scr<=bscr&&scr>0) {
                    if (scr<bscr) {
                        bscr=scr;
                        results.clear();
                    }
                    results.put(alg,ret);
                }
                amt++;
                if (amt%10_000_000==0)
                    System.out.println("#checked="+amt+", time="+(System.currentTimeMillis()-st));
            }
            return;
        }
        for (int m=0; m<4; m++)
        if (idx==0||(m!=(seq[idx-1]+2)%4&&(m!=seq[idx-1]||streak+1<=N/2))) {
            seq[idx]=m;
            int dr0=dr, dc0=dc;
            if (m==0) dr=mod(dr+1,N);
            else if (m==2) dr=mod(dr-1,N);
            else if (m==1) dc=mod(dc+1,N);
            else dc=mod(dc-1,N);
            int streak0=streak;
            streak=idx>0&&m==seq[idx-1]?(streak+1):1;
            dfs(idx+1);
            seq[idx]=-1;
            dr=dr0; dc=dc0;
            streak=streak0;
        }
    }
    private static void blobs(int K) {
        amt=0;
        bscr=Integer.MAX_VALUE;
        results=new HashMap<>();
        seq=new int[K]; Arrays.fill(seq,-1);
        dfs(0);
        System.out.println("#blobs="+amt);
        System.out.println("bscr="+bscr);
    }
    public static void main(String[] args) {
        N=4;
        for (int L=1; L<=24; L++) {
            System.out.println("L="+L);
            st=System.currentTimeMillis();
            blobs(L);
            Set<String> primaryAlgs=new HashSet<>(), seen=new HashSet<>();
            for (String alg:results.keySet())
                if (!seen.contains(alg)) {
                    primaryAlgs.add(alg);
                    for (int b=0; b<16; b++)
                        seen.add(LoopoverNRGSetup.transformed(alg,b));
                }
            System.out.println(primaryAlgs);
            System.out.println("time="+(System.currentTimeMillis()-st));
        }
    }
}
