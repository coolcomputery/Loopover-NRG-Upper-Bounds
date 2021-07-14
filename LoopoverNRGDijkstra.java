import java.util.*;
/**
 * consider a NxN NRG Loopover board with a binary matrix A
 * where the piece at location (r,c) is solved iff A[r][c]==false
 * and the gripped piece is solved and at (gr,gc)
 * we say that we are currently at the "state" A
 * furthermore, we want to go from state A to state B
 *  where B is another matrix satisfying (!A[r][c]-->!B[r][c]) for all r,c
 *      i.e. if A[r][c]==false then B[r][c] must also be false
 * we will restrict ourselves to solving every scramble with 3-cycles, 2,2-cycles (more generally, blobs),
 *      and single moves that by themselves do not move any already solved pieces
 * we never make move any already solved pieces, except during the process of performing a blob
 *  i.e. after each blob and each single move, all (r,c) s.t. A[r][c]==true are still in their solved positions
 */
public class LoopoverNRGDijkstra {
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
    private int F; //F=number of locations that are not locked
    private int[] tofree, freeto; //freeto[f]=l=location of the f-th unlocked location; tofree[l]=f
    public int K;
    //BFS stuff
    public int ncombos;
    private int[] depth, par;
    private String[] step;
    public int D, diam;
    public LoopoverNRGDijkstra(int gr, int gc, String A, String B) {
        this(gr,gc,tobmat(A.split(",")),tobmat(B.split(",")));
    }
    private LoopoverNRGDijkstra(int gr, int gc, boolean[][] A, boolean[][] B) {
        this(gr,gc,A,B,null);
    }
    private LoopoverNRGDijkstra(int gr, int gc, boolean[][] A, boolean[][] B, LoopoverNRGSetup[] bfss) {
        long st=System.currentTimeMillis();
        R=A.length; C=A[0].length;
        if (R!=C) throw new RuntimeException("Only square board sizes allowed."); //need to refactor LoopoverNRGSetup before I can remove this constraint
        if (R!=B.length||C!=B[0].length) throw new RuntimeException("Mismatch in dimensions.");
        if (!A[gr][gc]) throw new RuntimeException("Gripped pieces locked at starting state.");
        //TODO: DEAL WITH STRICT/NONSTRICT DIJKSTRA'S
        for (int r=0; r<R; r++) for (int c=0; c<C; c++)
            if (!A[r][c]&&B[r][c]) throw new RuntimeException("Set of solved pieces in A does not subset set of solved pieces in B.");
        F=0; tofree=new int[R*C]; freeto=new int[R*C];
        for (int r=0; r<R; r++) for (int c=0; c<C; c++) if (A[r][c]) {
            tofree[r*C+c]=F;
            freeto[F]=r*C+c;
            F++;
        }
        freeto=Arrays.copyOfRange(freeto,0,F);
        for (int r=0; r<R; r++) {
            for (int c=0; c<C; c++)
                System.out.printf("%4s",
                                A[r][c]?
                                ((B[r][c]?(r==gr&&c==gc?"g":""):(r==gr&&c==gc?"G":"'")))+tofree[r*C+c]
                                :"X"
                        //X: locked
                        //': piece that this BFS tree tries to solve
                        //g: gripped piece, does not have to go to home position
                        //G: gripped piece, has to go to home position
                );
            System.out.println();
        }
        boolean[] rfree=new boolean[R], cfree=new boolean[C];
        Arrays.fill(rfree,true); Arrays.fill(cfree,true);
        for (int r=0; r<R; r++) for (int c=0; c<C; c++) if (!A[r][c]) rfree[r]=cfree[c]=false;
        int M=2*R+2*C;
        int[][] mvactions=new int[M][]; {
            //mvactions[m][i]=free loc. that i-th free loc. will go to after the m-th move is applied
            //mv [0,mr,s] --> idx=mr*2+(s+1)/2
            for (int mr=0; mr<R; mr++) if (rfree[mr])
                for (int s=-1; s<=1; s+=2) {
                    int idx=mr*2+(s+1)/2;
                    mvactions[idx]=new int[F];
                    for (int i=0; i<F; i++) {
                        int r=freeto[i]/C, c=freeto[i]%C;
                        mvactions[idx][i]=tofree[r*C+(r==mr?mod(c+s,C):c)];
                    }
                }
            //mv [1,mc,s] --> idx=2*R+mc*2+(s+1)/2
            for (int mc=0; mc<C; mc++) if (cfree[mc])
                for (int s=-1; s<=1; s+=2) {
                    int idx=2*R+mc*2+(s+1)/2;
                    mvactions[idx]=new int[F];
                    for (int i=0; i<F; i++) {
                        int r=freeto[i]/C, c=freeto[i]%C;
                        mvactions[idx][i]=tofree[(c==mc?mod(r+s,R):r)*C+c];
                    }
                }
        }

        //BFS
        K=1;
        for (int r=0; r<R; r++) for (int c=0; c<C; c++) if ((r!=gr||c!=gc)&&A[r][c]&&!B[r][c]) K++;
        long tmp=1;
        for (int rep=0; rep<K; rep++)
            tmp*=F-rep;
        if (tmp>400_000_000) throw new RuntimeException("Too many combos: "+tmp);
        ncombos=(int)tmp;
        System.out.println("ncombos="+ncombos);
        depth=new int[ncombos]; Arrays.fill(depth,Integer.MAX_VALUE); par=new int[ncombos]; step=new String[ncombos];
        List<List<Integer>> fronts=new ArrayList<>(); fronts.add(new ArrayList<>());
        for (int gl=0; gl<R*C; gl++)
            if (B[gr][gc]?(B[gl/C][gl%C]):(gl==gr*C+gc)) {
                int[] solvedscrm=new int[R*C]; solvedscrm[0]=tofree[gl];
                for (int r=0, i=1; r<R; r++) for (int c=0; c<C; c++) if ((r!=gr||c!=gc)&&A[r][c]&&!B[r][c])
                    solvedscrm[i++]=tofree[r*C+c];
                solvedscrm=Arrays.copyOfRange(solvedscrm,0,K);
                System.out.println(Arrays.toString(solvedscrm));
                int solvedcode=comboCode(solvedscrm);
                fronts.get(0).add(solvedcode);
                depth[solvedcode]=0; par[solvedcode]=-1; step[solvedcode]=null;
            }
        boolean[] visited=new boolean[ncombos];
        int reached=0;
        if (bfss==null) bfss=new LoopoverNRGSetup[] {LoopoverNRGSetup.cyc3bfs(R), LoopoverNRGSetup.swap22bfs(R)};
        for (D=0, diam=0; D<fronts.size(); D++)
        if (fronts.get(D)!=null&&fronts.get(D).size()>0) {
            int fsz=0;
            for (int f:fronts.get(D)) if (!visited[f]) {
                fsz++;
                visited[f]=true;
                int[] scrm=codeCombo(f);
                int lr=freeto[scrm[0]]/C, lc=freeto[scrm[0]]%C;
                int[] mvis={lr*2,lr*2+1,2*R+lc*2,2*R+lc*2+1};
                for (int mvi:mvis) if (mvactions[mvi]!=null) {
                    int nf=comboCode(scrm,mvactions[mvi]);
                    int ndepth=depth[f]+1;
                    if (ndepth<depth[nf]) {
                        depth[nf]=ndepth;
                        par[nf]=f;
                        step[nf]=mvi<2*R?(mvi%2==0?"L":"R"):(mvi%2==0?"U":"D");
                        while (ndepth>=fronts.size()) fronts.add(null);
                        if (fronts.get(ndepth)==null) fronts.set(ndepth,new ArrayList<>());
                        fronts.get(ndepth).add(nf);
                    }
                }
                for (LoopoverNRGSetup bfs:bfss) if (bfs!=null) {
                    int nP=bfs.tP.length;
                    int[] tuple=new int[nP];
                    //we want to cycle the pieces at locations freeto[scrm[tuple[i]+1]]
                    while (tuple[nP-1]<K-1) {
                        boolean good=true;
                        for (int i=0; i<nP; i++)
                            for (int j=0; j<i; j++)
                                if (tuple[i]==tuple[j]) good=false;
                        if (good) {
                            int[] L=new int[nP];
                            for (int i=0; i<nP; i++)
                                L[i]=freeto[scrm[tuple[i]+1]];
                            int[] nscrm=scrm.clone();
                            for (int i=0; i<nP; i++)
                                nscrm[tuple[i]+1]=scrm[tuple[bfs.tP[i]]+1];
                            int nf=comboCode(nscrm);
                            int ndepth=depth[f]+bfs.cost(L,lr,lc);
                            if (ndepth<depth[nf]) {
                                depth[nf]=ndepth;
                                par[nf]=f;
                                step[nf]=bfs.sol(L,lr,lc);
                                while (ndepth>=fronts.size()) fronts.add(null);
                                if (fronts.get(ndepth)==null) fronts.set(ndepth,new ArrayList<>());
                                fronts.get(ndepth).add(nf);
                            }
                        }
                        tuple[0]++;
                        for (int i=0; i<nP-1&&tuple[i]==K-1; i++) {
                            tuple[i]=0;
                            tuple[i+1]++;
                        }
                    }
                }
            }
            if (fsz>0) {
                System.out.println(D+":"+fsz);
                diam=Math.max(diam,D);
            }
            reached+=fsz;
        }
        System.out.println("# combos reached="+reached);
        if (reached!=ncombos) System.out.println("Warning: ncombos="+ncombos+"!=reached="+reached+" (could be the result of parity restriction).");
        System.out.println("diameter="+diam);
        System.out.println("BFS time (ms)="+(System.currentTimeMillis()-st));
    }
    private int comboCode(int[] A) {
        int[] P=new int[F];
        for (int i=0; i<F; i++) P[i]=i;
        int[] L=P.clone();
        int out=0;
        for (int i=F-1, pow=1; i>=F-K; i--) {
            //swap idxs i and L[A[i-(N-K)]] in P
            int j=L[A[i-(F-K)]];
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
        int[] P=new int[F];
        for (int i=0; i<F; i++) P[i]=i;
        int[] L=P.clone();
        int out=0;
        for (int i=F-1, pow=1; i>=F-K; i--) {
            int j=L[f[A[i-(F-K)]]];
            int pi=P[i];
            P[j]=pi;
            L[pi]=j;
            out+=pow*j;
            pow*=i+1;
        }
        return out;
    }
    private int[] codeCombo(int code) {
        int[] P=new int[F];
        for (int i=0; i<F; i++) P[i]=i;
        for (int v=F; v>F-K; v--) {
            int i=v-1, j=code%v;
            code/=v;
            int pi=P[i]; P[i]=P[j]; P[j]=pi;
        }
        int[] out=new int[K];
        System.arraycopy(P,F-K,out,0,K);
        return out;
    }
    public String solveseq(int code) {
        if (depth[code]==Integer.MAX_VALUE)
            throw new RuntimeException("No solution.");
        StringBuilder out=new StringBuilder();
        for (int c=code; depth[c]>0; c=par[c])
            out.append(inv(step[c])).append(" ");
        return out.toString();
    }
    public String solveseq(int[] scramble) {
        return solveseq(comboCode(scramble));
    }
    public static void main(String[] args) {
        System.out.println(new LoopoverNRGDijkstra(0,0,"1010,1111,1010,1010,","0000,0000,0000,0000")
                .solveseq(new int[] {9,8,7,6,5,4,3,2,1,0}));
        //^^^ will solve the following scramble:
        /*
        O.M.
        KIHG
        F.E.
        C.A.

        (with all pieces shown):
        OBMD
        KIHG
        FJEL
        CNAP

        output: RRURRURRDRRDRRURRURRDRRD RUURRUURRUURRUUR D D R DRDLLDDLLDDLLDDLLDLU RDRRURRURRDRRDRRURRURRDR R U
         */
    }
}
