import java.util.*;
/**
 * consider a NxN NRG Loopover board with a binary matrix A
 * where the piece at location (r,c) is solved iff A[r][c]==false
 * and the gripped piece is solved and at (gr,gc)
 * we say that we are currently at the "state" A
 * furthermore, we want to go from state A to state B
 *  where B is another matrix satisfying (!A[r][c]-->!B[r][c]) for all r,c
 *      i.e. if A[r][c]==false then B[r][c] must also be false
 * we will restrict ourselves to solving every scramble with 3-cycles and 2,2-cycles (more generally, blobs)
 * additionally, we never make any already solved pieces become unsolved, except when in the process of performing a blob
 *  i.e. after each blob, all (r,c) s.t. A[r][c]==true are still in their solved positions
 */
public class LoopoverNRGCycleDijkstra {
    private static int mod(int n, int k) {
        return (n%k+k)%k;
    }
    private static String inv(String mvs) {
        StringBuilder out=new StringBuilder();
        for (int i=mvs.length()-1; i>-1; i--) {
            char c=mvs.charAt(i);
            out.append(c=='D'?'U':c=='R'?'L':c=='U'?'D':'R');
        }
        return out.toString();
    }
    public static String mvseqStr(List<int[]> S) {
        StringBuilder str=new StringBuilder();
        for (int[] m:S)
            str.append(" ").append(m[0]==0?"R":"C").append(m[1]).append(m[2]==1?"":m[2]==-1?"'":("("+m[2]+")"));
        return str.toString();
    }
    public static boolean[][] tobmat(String[] rows) {
        boolean[][] out=new boolean[rows.length][rows[0].length()];
        for (int i=0; i<out.length; i++)
        for (int j=0; j<rows[i].length(); j++) {
            char c=rows[i].charAt(j);
            if (c=='0') out[i][j]=false;
            else if (c=='1') out[i][j]=true;
            else throw new RuntimeException("Not parseable as a binary matrix.");
        }
        return out;
    }
    private int R, C;
    private int Nfree;
    private int[] tofree, freeto;
    public int K;
    //BFS stuff
    public int ncombos;
    private int[] depth, par, blobi;
    private List<String> blobs;
    public int D, diam;
    public LoopoverNRGCycleDijkstra(int gr, int gc, String A, String B) {
        this(gr,gc,tobmat(A.split(",")),tobmat(B.split(",")));
    }
    private LoopoverNRGCycleDijkstra(int gr, int gc, boolean[][] A, boolean[][] B) {
        long st=System.currentTimeMillis();
        R=A.length; C=A[0].length;
        if (R!=C) throw new RuntimeException("Only square board sizes allowed."); //need to refactor LoopoverNRGSetup before I can remove this constraint
        if (R!=B.length||C!=B[0].length) throw new RuntimeException("Mismatch in dimensions.");
        if (A[gr][gc]) throw new RuntimeException("Gripped piece not marked as solved.");
        for (int r=0; r<R; r++) for (int c=0; c<C; c++)
            if (!A[r][c]&&B[r][c]) throw new RuntimeException("Set of solved pieces in A does not subset set of solved pieces in B.");
        Nfree=0; tofree=new int[R*C]; freeto=new int[R*C];
        for (int r=0; r<R; r++) for (int c=0; c<C; c++) if (A[r][c]) {
            tofree[r*C+c]=Nfree;
            freeto[Nfree]=r*C+c;
            Nfree++;
        }
        freeto=Arrays.copyOfRange(freeto,0,Nfree);
        for (int r=0; r<R; r++) {
            for (int c=0; c<C; c++)
                System.out.printf("%4s",
                        r==gr&&c==gc?"*":
                                (A[r][c]?
                                ((B[r][c]?"":"'"))+tofree[r*C+c]
                                :"X")
                        //X: locked; ': piece that this BFS tree tries to solve; *: gripped piece
                );
            System.out.println();
        }
        blobs=new ArrayList<>(); List<int[]> blobactions=new ArrayList<>();
        LoopoverNRGSetup[] bfss={LoopoverNRGSetup.cyc3bfs(R), LoopoverNRGSetup.swap22bfs(R)};
        for (LoopoverNRGSetup bfs:bfss) if (bfs!=null) { //table of all possible 3-cycle algorithms we will need
            int offset=blobs.size();
            int T=bfs.tP.length; //the number of pieces that will be cycled
            for (int rep=0; rep<Math.pow(Nfree,T); rep++) {
                blobs.add(null);
                blobactions.add(null);
            }
            int[] P=bfs.tP;
            int[] tuple=new int[T];
            while (tuple[T-1]<Nfree) {
                boolean good=true;
                for (int i=0; i<T&&good; i++)
                    for (int j=0; j<i&&good; j++)
                        if (tuple[i]==tuple[j]) good=false;
                if (good) {
                    int i=tupleCode(tuple);
                    {
                        int[] tl=new int[T]; for (int ii=0; ii<T; ii++) tl[ii]=freeto[tuple[ii]];
                        blobs.set(offset+i,bfs.sol(tl,gr,gc));
                    }
                    int[] action=new int[Nfree];
                    for (int k=0; k<Nfree; k++) action[k]=k;
                    for (int p=0; p<T; p++)
                        action[tuple[p]]=tuple[P[p]];
                    //applying the move sequence bfs.sol(tl,gr,gc) moves the k-th free location to the action[k]-th free location
                    blobactions.set(offset+i,action);
                }
                tuple[0]++;
                for (int ti=0; ti<T-1&&tuple[ti]==Nfree; ti++) {
                    tuple[ti]=0;
                    tuple[ti+1]++;
                }
            }
        }
        //BFS
        K=0; int[] solvedscrm=new int[R*C];
        for (int r=0; r<R; r++) for (int c=0; c<C; c++) if (A[r][c]&&!B[r][c]) solvedscrm[K++]=tofree[r*C+c];
        long tmp=1;
        for (int rep=0; rep<K; rep++)
            tmp*=Nfree-rep;
        if (tmp>400_000_000) throw new RuntimeException("Too many combos: "+tmp);
        ncombos=(int)tmp;
        depth=new int[ncombos]; Arrays.fill(depth,Integer.MAX_VALUE); par=new int[ncombos]; blobi=new int[ncombos];
        System.out.println("ncombos="+ncombos);
        List<Set<Integer>> fronts=new ArrayList<>(); fronts.add(new HashSet<>());
        int solvedcode=comboCode(Arrays.copyOfRange(solvedscrm,0,K));
        fronts.get(0).add(solvedcode);
        depth[solvedcode]=0; par[solvedcode]=-1; blobi[solvedcode]=-1;
        int reached=0;
        for (D=0, diam=0; D<fronts.size(); D++)
        if (fronts.get(D)!=null&&fronts.get(D).size()>0) {
            diam=Math.max(diam,D);
            System.out.println(D+":"+fronts.get(D).size());
            reached+=fronts.get(D).size();
            for (int f:fronts.get(D)) {
                int[] scrm=codeCombo(f);
                for (int ci = 0; ci< blobs.size(); ci++) if (blobactions.get(ci)!=null) {
                    int nf=comboCode(scrm,blobactions.get(ci));
                    int ndepth=depth[f]+ blobs.get(ci).length();
                    if (ndepth<depth[nf]) {
                        if (depth[nf]!=Integer.MAX_VALUE)
                            fronts.get(depth[nf]).remove(nf);
                        depth[nf]=ndepth;
                        par[nf]=f;
                        blobi[nf]=ci;
                        while (ndepth>=fronts.size()) fronts.add(null);
                        if (fronts.get(ndepth)==null) fronts.set(ndepth,new HashSet<>());
                        fronts.get(ndepth).add(nf);
                    }
                }
            }
        }
        System.out.println("# combos reached="+reached);
        if (reached!=ncombos) System.out.println("Warning: ncombos="+ncombos+"!=reached="+reached+" (could be the result of parity restriction).");
        System.out.println("diameter="+diam);
        System.out.println("BFS time (ms)="+(System.currentTimeMillis()-st));
    }
    private int tupleCode(int[] vs) {
        int out=0;
        for (int i=0, pow=1; i<vs.length; i++, pow*=Nfree)
            out+=vs[i]*pow;
        return out;
    }
    private int comboCode(int[] A) {
        int[] P=new int[Nfree];
        for (int i=0; i<Nfree; i++) P[i]=i;
        int[] L=P.clone();
        int out=0;
        for (int i=Nfree-1, pow=1; i>=Nfree-K; i--) {
            //swap idxs i and L[A[i-(N-K)]] in P
            int j=L[A[i-(Nfree-K)]];
            int pi=P[i];//, pj=P[j];
            //P[i]=pj; //<--idx i will never be touched again
            P[j]=pi;
            L[pi]=j;
            //L[pj]=i;
            //J_i==j
            out+=pow*j;
            pow*=i+1;
        }
        return out;
    }
    private int comboCode(int[] A, int[] f) {
        int[] P=new int[Nfree];
        for (int i=0; i<Nfree; i++) P[i]=i;
        int[] L=P.clone();
        int out=0;
        for (int i=Nfree-1, pow=1; i>=Nfree-K; i--) {
            int j=L[f[A[i-(Nfree-K)]]];
            int pi=P[i];
            P[j]=pi;
            L[pi]=j;
            out+=pow*j;
            pow*=i+1;
        }
        return out;
    }
    private int[] codeCombo(int code) {
        int[] P=new int[Nfree];
        for (int i=0; i<Nfree; i++) P[i]=i;
        for (int v=Nfree; v>Nfree-K; v--) {
            int i=v-1, j=code%v;
            code/=v;
            int pi=P[i]; P[i]=P[j]; P[j]=pi;
        }
        int[] out=new int[K];
        System.arraycopy(P,Nfree-K,out,0,K);
        return out;
    }
    public String solveseq(int code) {
        if (depth[code]==Integer.MAX_VALUE)
            throw new RuntimeException("No solution.");
        StringBuilder out=new StringBuilder();
        for (int c=code; depth[c]>0; c=par[c])
            out.append(inv(blobs.get(blobi[c]))).append(" ");
        return out.toString();
    }
    public String solveseq(int[] scramble) {
        return solveseq(comboCode(scramble));
    }
    private String test() {
        int[] tscrm=new int[K];
        for (int i=0; i<K; i++) tscrm[i]=(i+1)%K;
        if (K%2==0) {
            int tmp=tscrm[0]; tscrm[0]=tscrm[1]; tscrm[1]=tmp;
        }
        System.out.println("test array: "+Arrays.toString(tscrm));
        return solveseq(tscrm);
    }
    public static void main(String[] args) {
        //4x4 NRG, JKL NOP already solved (takes at most 24 moves)
        System.out.println(new LoopoverNRGCycleDijkstra(0,0,"0111,1111,1000,1000","0000,0000,0000,0000").test()); //solve BCD EFGH I M

        //5x5 NRG, LMNO QRST VWXY already solved (takes at most 21+24+66=111 moves)
        System.out.println(new LoopoverNRGCycleDijkstra(0,0,"01111,11111,10000,10000,10000","01111,01111,00000,00000,00000").test()); //solve F K P U
        System.out.println(new LoopoverNRGCycleDijkstra(0,0,"01111,01111,00000,00000,00000","00000,00000,00000,00000,00000").test()); //solve BCDE GHIJ
    }
}
