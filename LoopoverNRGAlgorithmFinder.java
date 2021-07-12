import java.util.*;
public class LoopoverNRGAlgorithmFinder {
    //a "blob" in a NxN Loopover NRG board is a move sequence that has no net displacement on the gripped piece
    //a "strict blob" is a blob with the additional constraint that all rows and all columns have no "net shift"
    private static int mod(int n, int k) {
        return (n%k+k)%k;
    }
    private static int N, K;
    private static long st, mark0=10_000, mark, stage;
    private static int bscr;
    private static long ncalls, amt;
    private static int[] syllLens;
    private static int[] rshift, cshift;
    private static Map<String,int[][]> results;
    //WLOG assume the first syllable is horizontal
    private static void dfs(int idx, int tlen, int dr, int dc) {
        if (System.currentTimeMillis()-st>=mark) {
            stage++;
            mark=(long)(mark0*Math.exp(Math.sqrt(stage)));
            System.out.printf("%10.3f%12d%12d%n",(System.currentTimeMillis()-st)/1000.0,ncalls,amt);
        }
        //tlen=current length of move sequence that syllLens[0:idx] represents
        ncalls++;
        if (Math.min(dr,N-dr)+Math.min(dc,N-dc)>K-tlen)
            //gripped piece is too far to bring back to beginning in enough moves
            return;
        int mincost=0;
        for (int r=0; r<N; r++)
            mincost+=Math.min(rshift[r],N-rshift[r]);
        for (int c=0; c<N; c++)
            mincost+=Math.min(cshift[c],N-cshift[c]);
        if (mincost>K-tlen) //not enough moves available to unshift all rows and columns
            return;
        //System.out.println(tlen);
        if (tlen==K) {
            //System.out.println(Arrays.toString(freq));
            if (dr==0&&dc==0) {
                boolean good=true;
                for (int r=0; r<N&&good; r++) if (rshift[r]!=0) good=false;
                for (int c=0; c<N&&good; c++) if (cshift[c]!=0) good=false;
                if (good) {
                    StringBuilder tmp=new StringBuilder();
                    for (int i=0; i<idx; i++) {
                        int reps=Math.abs(syllLens[i]);
                        for (int rep=0; rep<reps; rep++)
                            tmp.append(i%2==0?(syllLens[i]>0?'R':'L'):(syllLens[i]>0?'D':'U'));
                    }
                    String alg=tmp.toString();
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
            }
            return;
        }
        for (int offset=1; offset<N; offset++) {
            int len=Math.min(offset,N-offset);
            //WLOG first syllable moves gripped piece to the right
            if (tlen+len<=K&&(idx>0||offset<=N-offset)) {
                syllLens[idx]=offset<=N-offset?len:(-len);
                if (idx%2==0) { //horizontal syllable
                    rshift[dr]=mod(rshift[dr]+offset,N);
                    dfs(idx+1,tlen+len,dr,mod(dc+offset,N));
                    rshift[dr]=mod(rshift[dr]-offset,N);
                }
                else { //vertical syllable
                    cshift[dc]=mod(cshift[dc]+offset,N);
                    dfs(idx+1,tlen+len,mod(dr+offset,N),dc);
                    cshift[dc]=mod(cshift[dc]-offset,N);
                }
            }
        }
    }
    private static void blobs(int K) {
        amt=0;
        bscr=Integer.MAX_VALUE;
        results=new HashMap<>();
        syllLens=new int[K];
        ncalls=0;
        LoopoverNRGAlgorithmFinder.K=K;
        rshift=new int[N]; cshift=new int[N];
        mark=mark0;
        stage =0;
        dfs(0,0,0,0);
        System.out.println("#dfs() calls="+ncalls);
        System.out.println("#strict blobs="+amt);
        System.out.println("bscr="+bscr);
    }
    public static void main(String[] args) {
        N=5;
        for (int L=30; L<=32; L++) {
            System.out.println("L="+L);
            st=System.currentTimeMillis();
            blobs(L);
            Set<String> primaryAlgs=new HashSet<>(), seen=new HashSet<>();
            for (String alg:results.keySet()) {
                String red=LoopoverNRGSetup.reduced(N,alg);
                if (!seen.contains(red)) {
                    primaryAlgs.add(red);
                    for (int i=0; i<red.length(); i++) {
                        StringBuilder s=new StringBuilder();
                        //count rotated/reflected/inverted versions of an algorithm to be equivalent
                        for (int k=0; k<red.length(); k++)
                            s.append(red.charAt((k+i)%red.length()));
                        for (int b=0; b<16; b++)
                            seen.add(LoopoverNRGSetup.reduced(N,LoopoverNRGSetup.transformed(s.toString(),b)));
                    }
                }
            }
            System.out.println(primaryAlgs);
            System.out.println("time="+(System.currentTimeMillis()-st));
        }
    }
}
