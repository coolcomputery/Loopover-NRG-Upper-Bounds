import java.util.*;
public class LoopoverNRGAlgorithmFinder {
    private static int[] seq, freq;
    private static void dfs(int idx, List<String> out) {
        //System.out.println(idx);
        if (idx==seq.length) {
            //System.out.println(Arrays.toString(freq));
            if (freq[0]==freq[2]&&freq[1]==freq[3]) {
                StringBuilder tmp=new StringBuilder();
                for (int i=0; i<seq.length; i++)
                    tmp.append(LoopoverNRGSetupBFS.dirNames[seq[i]]);
                out.add(tmp.toString());
            }
            return;
        }
        for (int m=0; m<4; m++)
        if (idx==0||m!=(seq[idx-1]+2)%4) {
            seq[idx]=m;
            freq[m]++;
            dfs(idx+1,out);
            seq[idx]=-1;
            freq[m]--;
        }
    }
    private static List<String> blobs(int K) {
        List<String> out=new ArrayList<>();
        seq=new int[K]; Arrays.fill(seq,-1);
        freq=new int[4];
        dfs(0,out);
        return out;
    }
    public static void main(String[] args) {
        long st=System.currentTimeMillis();
        int N=6, KA=10, KB=10;
        System.out.printf("N=%d,KA=%d,KB=%d%n",N,KA,KB);
        List<String> blobsA=blobs(KA), blobsB=blobs(KB);
        Map<String,int[][]> results=new HashMap<>();
        for (String a:blobsA)
        for (String b:blobsB) {
            String alg=LoopoverNRGSetupBFS.comm(a,b);
            int[][] ret=LoopoverNRGSetupBFS.effect(N,alg);
            if (ret[0].length<=4&&ret[0].length>0)
                results.put(alg,ret);
        }
        Set<String> primaryAlgs=new HashSet<>(), seen=new HashSet<>();
        for (String alg:results.keySet())
        if (!seen.contains(alg)) {
            primaryAlgs.add(alg);
            for (int b=0; b<16; b++)
                seen.add(LoopoverNRGSetupBFS.transformed(alg,b));
        }
        System.out.println(primaryAlgs);
        for (int K=3; K<=4; K++) {
            System.out.println("\nK="+K);
            for (String alg:primaryAlgs)
            if (results.get(alg)[0].length==K) {
                String A=alg.substring(0,KA),
                        B=alg.substring(KA,KA+KB);
                System.out.println("comm(\""+A+"\",\""+B+"\"),");
            }
            for (String alg:primaryAlgs) {
                int[] locs=results.get(alg)[0];
                if (locs.length==K) {
                    for (int loc:locs) {
                        int r=loc/N, c=loc%N;
                        if (r>N/2) r-=N; if (c>N/2) c-=N;
                        System.out.print("("+r+","+c+"),");
                    }
                    System.out.println();
                }
            }
        }
        System.out.println("time="+(System.currentTimeMillis()-st));
    }
}
