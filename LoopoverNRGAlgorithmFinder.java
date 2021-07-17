import java.util.*;
public class LoopoverNRGAlgorithmFinder {
    //a "blob" in a NxN Loopover NRG board is a move sequence that has no net displacement on the gripped piece
    //a "strict blob" is a blob with the additional constraint that all rows and all columns have no "net shift"
    private static final Comparator<String> algcomp=new Comparator<String>() {
        @Override
        public int compare(String o1, String o2) {
            return o1.length()==o2.length()?o1.compareTo(o2):o1.length()-o2.length();
        }
    };
    private static String form="%10.3f%16d%16d%16d%n";
    private static int N, K;
    private static long st, mark0=10_000, mark, stage;
    private static int shiftsum;
    private static long ncalls, amt;
    private static int[] syllLens;
    private static int[] rshift, cshift;
    private static Map<Integer,Map<String,int[][]>> results;
    //WLOG assume the first syllable is horizontal
    private static void dfs(int idx, int tlen, int dr, int dc) {
        if (System.currentTimeMillis()-st>=mark) {
            stage++;
            mark=(long)(mark0*Math.pow(stage,2.5));
            System.out.printf(form,(System.currentTimeMillis()-st)/1000.0,ncalls,amt,results.get(4).size());
        }
        //tlen=current length of move sequence that syllLens[0:idx] represents
        //idx%2==0: we want current syllable to be horizontal; ==1: we want it to be vertical
        ncalls++;
        if (shiftsum>K-tlen||Math.min(dr,N-dr)+Math.min(dc,N-dc)>K-tlen)
            //gripped piece is too far to bring back to beginning in enough moves
            //or there are not enough moves available to unshift all rows and columns
            return;
        //for two move sequences A and B, define "A similar to B" == "A ~ B" == there exists move sequence S s.t. A=S*B*inv(S)
        //we only want to find a set of move sequences that are mutually not similar to each other
        //for move sequence A=[A[0],...A[K-1]], define (A<<a)=[A[a],...A[K-1],A[0],...A[a-1]]
        //then A ~ (A<<a) for all A, a
        //therefore WLOG we only need to search for move sequences whose first and last syllables are of different types
        //               vvvvvvvv
        if (shiftsum==0&&idx%2==0&&dr==0&&dc==0) {
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
            amt++;
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
                    int r0=rshift[dr];
                    shiftsum-=Math.min(r0,N-r0);
                    rshift[dr]=(r0+offset)%N;
                    shiftsum+=Math.min(rshift[dr],N-rshift[dr]);
                    dfs(idx+1,tlen+len,dr,(dc+offset)%N);
                    rshift[dr]=r0;
                }
                else { //vertical syllable
                    int c0=cshift[dc];
                    shiftsum-=Math.min(c0,N-c0);
                    cshift[dc]=(c0+offset)%N;
                    shiftsum+=Math.min(cshift[dc],N-cshift[dc]);
                    dfs(idx+1,tlen+len,(dr+offset)%N,dc);
                    cshift[dc]=c0;
                }
                shiftsum=mincost0;
            }
        }
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
        K=32;
        System.out.printf("N=%d,K=%d%n",N,K);
        st=System.currentTimeMillis();
        results=new HashMap<>();
        results.put(4,new HashMap<>());
        syllLens=new int[K];
        ncalls=amt=0;
        rshift=new int[N]; cshift=new int[N];
        mark=mark0;
        stage=1;
        dfs(0,0,0,0);
        System.out.printf(form,(System.currentTimeMillis()-st)/1000.0,ncalls,amt,results.get(4).size());
        Set<String> algs=primaryAlgs(N,results.get(4).keySet());
        System.out.println(algs);
        System.out.println("num="+algs.size());
        System.out.println("time="+(System.currentTimeMillis()-st));
    }
}
