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
    private int R, C, grippedPc;
    private int F; //F=number of locations that are not locked
    private int[] tofree, freeto; //freeto[f]=l=location of the f-th unlocked location; tofree[l]=f
    public int K;
    //BFS stuff
    public int ncombos;
    private LoopoverNRGSetup[] bfss;
    private int[] depth, par, tuplecode;
    public int diam;
    public LoopoverNRGDijkstra(int gr, int gc, String A, String B) {
        this(gr,gc,tobmat(A.split(",")),tobmat(B.split(",")));
    }
    public LoopoverNRGDijkstra(int gr, int gc, String A, String B, LoopoverNRGSetup[] bfss) {
        this(gr,gc,tobmat(A.split(",")),tobmat(B.split(",")),bfss);
    }
    private LoopoverNRGDijkstra(int gr, int gc, boolean[][] A, boolean[][] B) {
        this(gr,gc,A,B,null);
    }
    private LoopoverNRGDijkstra(int gr, int gc, boolean[][] A, boolean[][] B, LoopoverNRGSetup[] bfss) {
        long st=System.currentTimeMillis();
        R=A.length; C=A[0].length; grippedPc=gr*C+gc;
        if (R!=C) throw new RuntimeException("Only square board sizes allowed."); //need to refactor LoopoverNRGSetup before I can remove this constraint
        if (R!=B.length||C!=B[0].length) throw new RuntimeException("Mismatch in dimensions.");
        if (!A[gr][gc]) throw new RuntimeException("Gripped pieces locked at starting state.");
        for (int r=0; r<R; r++) for (int c=0; c<C; c++)
            if (!A[r][c]&&B[r][c]) throw new RuntimeException("Set of solved pieces in A does not subset set of solved pieces in B.");
        boolean[] rfree=new boolean[R], cfree=new boolean[C];
        Arrays.fill(rfree,true); Arrays.fill(cfree,true);
        for (int r=0; r<R; r++) for (int c=0; c<C; c++) if (!A[r][c]) rfree[r]=cfree[c]=false;
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
        depth=new int[ncombos]; Arrays.fill(depth,Integer.MAX_VALUE); par=new int[ncombos]; tuplecode=new int[ncombos];
        System.out.print("list of allowed positions for gripped piece after solving:"); {
            //gripped piece must be in a position after solving that is reachable to home position under state B
            boolean[] Brf=new boolean[R], Bcf=new boolean[C]; Arrays.fill(Brf,true); Arrays.fill(Bcf,true);
            for (int r=0; r<R; r++) for (int c=0; c<C; c++) if (!B[r][c]) Brf[r]=Bcf[c]=false;
            for (int gl=0; gl<R*C; gl++)
                if ((B[gr][gc]&&(Brf[gl/C]||Bcf[gl%C]))||gl==gr*C+gc) {
                    int[] solvedscrm=new int[K]; solvedscrm[0]=tofree[gl];
                    for (int r=0, i=1; r<R; r++) for (int c=0; c<C; c++) if ((r!=gr||c!=gc)&&A[r][c]&&!B[r][c])
                        solvedscrm[i++]=tofree[r*C+c];
                    System.out.print(" "+solvedscrm[0]);
                    int solvedcode=comboCode(solvedscrm);
                    depth[solvedcode]=0; par[solvedcode]=-1;
                }
        } System.out.println();
        int reached=0;
        if (bfss==null) bfss=new LoopoverNRGSetup[] {LoopoverNRGSetup.cyc3(R), LoopoverNRGSetup.cyc2n2(R)};
        this.bfss=bfss;
        List<List<int[][]>> cycleInfos=new ArrayList<>();
        for (int bfsi=0; bfsi<bfss.length; bfsi++)
            if (bfss[bfsi]==null) cycleInfos.add(null);
            else {
                cycleInfos.add(new ArrayList<>());
                LoopoverNRGSetup bfs=bfss[bfsi];
                int nP=bfs.tP.length;
                int[] tuple=new int[nP];
                //we want to cycle the pieces at locations freeto[tuple[i]]
                while (tuple[nP-1]<F) {
                    boolean good=true;
                    for (int i=0; i<nP; i++)
                        for (int j=0; j<i; j++)
                            if (tuple[i]==tuple[j]) good=false;
                    if (good) {
                        int[] L=new int[nP];
                        for (int i=0; i<nP; i++)
                            L[i]=freeto[tuple[i]];
                        int[] action=new int[F];
                        for (int i=0; i<F; i++) action[i]=i;
                        for (int i=0; i<nP; i++) action[tofree[L[i]]]=tofree[L[bfs.tP[i]]];
                        cycleInfos.get(bfsi).add(new int[][] {L,action});
                    }
                    tuple[0]++;
                    for (int i=0; i<nP-1&&tuple[i]==F; i++) {
                        tuple[i]=0;
                        tuple[i+1]++;
                    }
                }
            }
        diam=0;
        for (int D=0;; D++) {
            boolean finished=true;
            int fsz=0;
            for (int f=0; f<ncombos; f++)
                if (depth[f]>D&&depth[f]!=Integer.MAX_VALUE) finished=false;
                else if (depth[f]==D) {
                    fsz++;
                    finished=false;
                    int[] scrm=codeCombo(f);
                    int lr=freeto[scrm[0]]/C, lc=freeto[scrm[0]]%C;
                    int[] mvis={lr*2,lr*2+1,2*R+lc*2,2*R+lc*2+1};
                    for (int mvi:mvis) if (mvactions[mvi]!=null) {
                        int nf=comboCode(scrm,mvactions[mvi]);
                        int ndepth=depth[f]+1;
                        if (ndepth<depth[nf]) {
                            depth[nf]=ndepth;
                            par[nf]=f;
                            tuplecode[nf]=(mvi<2*R?(mvi%2==0?0:1):(mvi%2==0?2:3))*(bfss.length+1);
                        }
                    }
                    for (int bfsi=0; bfsi<bfss.length; bfsi++) if (bfss[bfsi]!=null) {
                        LoopoverNRGSetup bfs=bfss[bfsi];
                        for (int[][] cycinfo:cycleInfos.get(bfsi)) if (cycinfo[1][scrm[0]]==scrm[0]) {
                            int[] L=cycinfo[0], action=cycinfo[1];
                            int nf=comboCode(scrm,action);
                            int tcode=bfs.tupleCode(L,lr,lc);
                            int ndepth=depth[f]+bfs.cost(tcode);
                            if (ndepth<depth[nf]) {
                                depth[nf]=ndepth;
                                par[nf]=f;
                                tuplecode[nf]=tcode*(bfss.length+1)+bfsi+1;
                            }
                        }
                    }
                }
            if (fsz>0) {
                System.out.print((D>0?" ":"")+D+":"+fsz);
                diam=Math.max(diam,D);
            }
            reached+=fsz;
            if (finished) break;
        }
        System.out.println("\n# combos reached="+reached);
        if (reached!=ncombos) System.out.println("Warning: ncombos="+ncombos+"!=reached="+reached+" (could be the result of a restriction on parity or reachable locations of the gripped piece).");
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
        for (int c=code; depth[c]>0; c=par[c]) {
            int i=tuplecode[c];
            int bfsi=i%(bfss.length+1)-1; i/=bfss.length+1;
            out.append(inv(
                    bfsi==-1?(new String[] {"L","R","U","D"}[i]):
                            bfss[bfsi].sol(i)
            )).append(" ");
        }
        return out.toString();
    }
    public String test() {
        for (int code=0; code<ncombos; code++) if (depth[code]!=Integer.MAX_VALUE) {
            int[] scrm=codeCombo(code);
            System.out.println("tscrm="+Arrays.toString(scrm));
            int[] targets=null;
            for (int c=0; c<ncombos; c++) if (depth[c]==0) {
                int[] t=codeCombo(c);
                if (freeto[t[0]]==grippedPc) {
                    targets=t;
                    break;
                }
            }
            int[] board=new int[R*C]; Arrays.fill(board,-1);
            for (int k=0; k<K; k++)
                board[freeto[scrm[k]]]=freeto[targets[k]];
            System.out.println("test scramble to solve");
            for (int r=0; r<R; r++) {
                for (int c=0; c<C; c++) {
                    int pc=board[r*C+c];
                    System.out.print(pc==-1?".":(char)('A'+pc));
                }
                System.out.println();
            }
            return solveseq(code);
        }
        return null;
    }
    public static void main(String[] args) {
        int N=5;
        LoopoverNRGSetup[] bfss=new LoopoverNRGSetup[] {LoopoverNRGSetup.cyc3(N), LoopoverNRGSetup.cyc2n2(N)};
        for (LoopoverNRGSetup bfs:bfss) LoopoverNRGSetup.verify(bfs);
        boolean[][] state0=tobmat("00000,01110,01110,01110,00000".split(",")),
                state1=tobmat("00000,00000,00000,00000,00000".split(","));
        System.out.println(new LoopoverNRGDijkstra(2,2,state0,state1,bfss).test());
    }
}
