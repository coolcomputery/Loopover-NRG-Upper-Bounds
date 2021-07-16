import java.util.*;
public class LoopoverNRGAlgorithmFinder {
    //a "blob" in a NxN Loopover NRG board is a move sequence that has no net displacement on the gripped piece
    //a "strict blob" is a blob with the additional constraint that all rows and all columns have no "net shift"
    private static int mod(int n, int k) {
        return (n%k+k)%k;
    }
    private static final Comparator<String> algcomp=new Comparator<String>() {
        @Override
        public int compare(String o1, String o2) {
            return o1.length()==o2.length()?o1.compareTo(o2):o1.length()-o2.length();
        }
    };
    private static int N, K;
    private static long st, mark0=10_000, mark, stage;
    private static int shiftsum;
    private static long ncalls;
    private static int[] syllLens;
    private static int[] rshift, cshift;
    private static Map<Integer,Map<String,int[][]>> results;
    //WLOG assume the first syllable is horizontal
    private static void dfs(int idx, int tlen, int dr, int dc) {
        if (System.currentTimeMillis()-st>=mark) {
            stage++;
            mark=(long)(mark0*Math.exp(Math.sqrt(stage)));
            System.out.printf("%10.3f%12d%12d%n",(System.currentTimeMillis()-st)/1000.0,ncalls,results.get(4).size());
        }
        //tlen=current length of move sequence that syllLens[0:idx] represents
        //idx%2==0: we want current syllable to be horizontal; ==1: we want it to be vertical
        ncalls++;
        if (Math.min(dr,N-dr)+Math.min(dc,N-dc)>K-tlen)
            //gripped piece is too far to bring back to beginning in enough moves
            return;
        if (shiftsum>K-tlen) //not enough moves available to unshift all rows and columns
            return;
        //System.out.println(tlen);
        //every move seequence can have its moves rotated s.t. the first and last syllables are of different types
        if (idx%2==0&&dr==0&&dc==0) {
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
                if (results.containsKey(scr))
                    results.get(scr).put(alg,ret);
            }
        }
        if (tlen==K)
            return;
        for (int offset=1; offset<N; offset++) {
            int len=Math.min(offset,N-offset);
            //WLOG first syllable moves gripped piece right <=N/2 units
            //WLOG second syllable moves gripped piece down <=N/2 units
            if (tlen+len<=K&&(idx>1||offset<=N-offset)) {
                syllLens[idx]=offset<=N-offset?len:(-len);
                int mincost0=shiftsum;
                if (idx%2==0) { //horizontal syllable
                    shiftsum-=Math.min(rshift[dr],N-rshift[dr]);
                    rshift[dr]=mod(rshift[dr]+offset,N);
                    shiftsum+=Math.min(rshift[dr],N-rshift[dr]);
                    dfs(idx+1,tlen+len,dr,mod(dc+offset,N));
                    rshift[dr]=mod(rshift[dr]-offset,N);
                }
                else { //vertical syllable
                    shiftsum-=Math.min(cshift[dc],N-cshift[dc]);
                    cshift[dc]=mod(cshift[dc]+offset,N);
                    shiftsum+=Math.min(cshift[dc],N-cshift[dc]);
                    dfs(idx+1,tlen+len,mod(dr+offset,N),dc);
                    cshift[dc]=mod(cshift[dc]-offset,N);
                }
                shiftsum=mincost0;
            }
        }
    }
    private static void blobs(int K) {
        results=new HashMap<>();
        results.put(4,new HashMap<>());
        syllLens=new int[K];
        ncalls=0;
        LoopoverNRGAlgorithmFinder.K=K;
        rshift=new int[N]; cshift=new int[N];
        mark=mark0;
        stage=0;
        dfs(0,0,0,0);
        System.out.println("#dfs() calls="+ncalls);
        System.out.println("#strict blobs with score 4="+results.get(4).size());
    }
    public static TreeSet<String> primaryAlgs(int N, Collection<String> algs) {
        TreeSet<String> primaryAlgs=new TreeSet<>(algcomp), seen=new TreeSet<>(algcomp);
        for (String alg:algs) {
            String red=LoopoverNRGSetup.canonical(N,alg);
            if (!seen.contains(red)) {
                TreeSet<String> group=new TreeSet<>(algcomp);
                for (int i=0; i<red.length(); i++) {
                    StringBuilder s=new StringBuilder();
                    //count rotated/reflected/inverted versions of an algorithm to be equivalent
                    for (int k=0; k<red.length(); k++)
                        s.append(red.charAt((k+i)%red.length()));
                    for (int b=0; b<16; b++)
                        group.add(LoopoverNRGSetup.canonical(N,LoopoverNRGSetup.transformed(s.toString(),b)));
                }
                primaryAlgs.add(group.first());
                seen.addAll(group);
            }
        }
        System.out.println("total # algs incl symmetries="+seen.size());
        return primaryAlgs;
    }
    public static void main(String[] args) {
        N=5;
        for (int L=32; L<=32; L++) {
            System.out.println("L="+L);
            st=System.currentTimeMillis();
            blobs(L);
            Set<String> algs=primaryAlgs(N,results.get(4).keySet());
            System.out.println(algs);
            System.out.println("num="+algs.size());
            System.out.println("time="+(System.currentTimeMillis()-st));
        }
    }
}
