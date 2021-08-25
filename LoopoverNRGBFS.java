import java.util.*;
public class LoopoverNRGBFS {
    private static int mod(int n, int k) {
        return (n%k+k)%k;
    }
    private static boolean[] mask(String s) {
        boolean[] out=new boolean[s.length()];
        for (int i=0; i<s.length(); i++)
            out[i]=s.charAt(i)=='1';
        return out;
    }
    public static boolean[][] parse(String s) {
        String[] rows=s.split(",");
        if (rows.length>1) {
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
        else {
            String[] pcs=s.split("x");
            if (pcs.length!=2) throw new RuntimeException("Not in 2 pieces: "+s);
            return new boolean[][] {mask(pcs[0]),mask(pcs[1])};
        }
    }
    private int R, C, grippedPc;
    private int F;
    private boolean[][] rcfree;
    private boolean free(int r, int c) {
        return rcfree[0][r]||rcfree[1][c];
    }
    private int[] tofree, freeto;
    public int K;
    //BFS stuff
    private int M;
    private int[][] mvactions;
    public int ncombos;
    private long[] data;
    public List<int[]> fronts;
    public int D;
    //c-->(depth,move from parent combo to c,parent combo)
    private long compressed(int depth, int parent, int move) {
        return ((long)depth*M+move)*ncombos+parent;
    }
    public int depth(int code) {
        return data[code]==-1?-1:(int)(data[code]/ncombos/M);
    }
    private int par(int code) {
        return data[code]==-1?-1:(int)(data[code]%ncombos);
    }
    private int mvi(int code) {
        return data[code]==-1?-1:(int)((data[code]/ncombos)%M);
    }
    public LoopoverNRGBFS(int R, int C, int gr, int gc, String state0, String state1) {
        //RxC NRG Loopover, gripped piece at (gr,gc) when board is solved
        //constraints: if A=# free rows at start state and B=#free clms at start state, then (A>=2&&B>=3)||(A>=3&&B>=2) must be satisfied
        //strict: all scrambles must be solved with gripped piece moved to where it should be in the solved board
        //nonstrict: gripped piece can be anywhere as long as all other pieces that need to be solved are solved
        this.R=R; this.C=C;
        grippedPc=gr*C+gc;
        boolean[][] nfree=parse(state1);
        if (state1.indexOf('x')!=-1) {
            boolean[][] tmp=new boolean[R][C];
            for (int i=0; i<R; i++)
                for (int j=0; j<C; j++) tmp[i][j]=nfree[0][i]||nfree[1][j];
            nfree=tmp;
        }
        System.out.println(R+"x"+C+": "+state0+" --> "+state1);
        long st=System.currentTimeMillis();
        rcfree=parse(state0);
        if (!free(gr,gc))
            throw new RuntimeException("Gripped piece is locked.");
        tofree=new int[R*C]; freeto=new int[R*C]; F=0;
        for (int r=0; r<R; r++)
            for (int c=0; c<C; c++)
                if (free(r,c)) {
                    tofree[r*C+c]=F;
                    freeto[F]=r*C+c;
                    F++;
                }
                else tofree[r*C+c]=-1;
        freeto=Arrays.copyOfRange(freeto,0,F);
        for (int r=0; r<R; r++) {
            for (int c=0; c<C; c++)
                System.out.printf("%4s",
                        free(r,c)?
                                ((r==gr&&c==gc?"*":(nfree[r][c]?"":"'"))
                                        +tofree[r*C+c])
                                :"X"
                        //X: locked; ': piece that this BFS tree tries to solve; *: gripped piece
                );
            System.out.println();
        }
        M=2*R+2*C;
        mvactions=new int[M][]; {
            //mvactions[m][i]=free loc. that i-th free loc. will go to after the m-th move is applied
            int idx=0;
            for (int mr=0; mr<R; mr++)
                for (int s=-1; s<=1; s+=2) {
                    if (rcfree[0][mr]) {
                        mvactions[idx]=new int[F];
                        for (int i=0; i<F; i++) {
                            int r=freeto[i]/C, c=freeto[i]%C;
                            mvactions[idx][i]=tofree[r*C+(r==mr?mod(c+s,C):c)];
                        }
                    }
                    else mvactions[idx]=null;
                    idx++;
                }
            for (int mc=0; mc<C; mc++)
                for (int s=-1; s<=1; s+=2) {
                    if (rcfree[1][mc]) {
                        mvactions[idx]=new int[F];
                        for (int i=0; i<F; i++) {
                            int r=freeto[i]/C, c=freeto[i]%C;
                            mvactions[idx][i]=tofree[(c==mc?mod(r+s,R):r)*C+c];
                        }
                    }
                    else mvactions[idx]=null;
                    idx++;
                }
        }
        K=0;
        for (int r=0; r<R; r++) for (int c=0; c<C; c++)
            if ((free(r,c)&&!nfree[r][c])||(r==gr&&c==gc)) //include gripped piece
                K++;
        {
            long tmp=1;
            for (int rep=0; rep<K; rep++) tmp*=F-rep;
            if (tmp>400_000_000) throw new RuntimeException("Too many combinations to handle.");
            ncombos=(int)tmp;
            System.out.println("ncombos="+ncombos);
        }
        //BFS
        data=new long[ncombos]; Arrays.fill(data,-1);
        fronts=new ArrayList<>();
        {
            int[] target=new int[K-1];
            for (int r=0, idx=0; r<R; r++) for (int c=0; c<C; c++)
                if ((free(r,c)&&!nfree[r][c])&&!(r==gr&&c==gc))
                    target[idx++]=tofree[r*C+c];
            boolean[] rnfree=new boolean[R], cnfree=new boolean[C];
            Arrays.fill(rnfree,true); Arrays.fill(cnfree,true);
            for (int r=0; r<R; r++) for (int c=0; c<C; c++) if (!nfree[r][c]) rnfree[r]=cnfree[c]=false;
            boolean existsrfree=false, existscfree=false;
            for (boolean v:rnfree) if (v) existsrfree=true;
            for (boolean v:cnfree) if (v) existscfree=true;
            System.out.println("allowed final locations of gripped piece (marked with *):");
            for (int grow=0; grow<R; grow++) {
                for (int gclm=0; gclm<C; gclm++)
                    System.out.print(!free(grow,gclm)?"X":
                            (nfree[gr][gc]?
                            (existsrfree&&existscfree?(rnfree[grow]||cnfree[gclm]):
                                    ((gclm==gc||rnfree[gr])&&(grow==gr||cnfree[gc]))):
                            (grow==gr&&gclm==gc))?"*":".");
                System.out.println();
            }
            List<Integer> solvedcodes=new ArrayList<>();
            for (int grow=0; grow<R; grow++) for (int gclm=0; gclm<C; gclm++)
                if (nfree[gr][gc]?
                        (existsrfree&&existscfree?(rnfree[grow]||cnfree[gclm]):
                                ((gclm==gc||rnfree[gr])&&(grow==gr||cnfree[gc]))):
                        (grow==gr&&gclm==gc)) {
                    int[] solvedscrm=new int[K]; solvedscrm[0]=tofree[grow*C+gclm];
                    System.arraycopy(target,0,solvedscrm,1,K-1);
                    //System.out.println(Arrays.toString(solvedscrm));
                    System.out.println(Arrays.toString(solvedscrm));
                    int solvedscrmcode=comboCode(solvedscrm);
                    solvedcodes.add(solvedscrmcode);
                    data[solvedscrmcode]=0;
                }
            fronts.add(new int[solvedcodes.size()]);
            for (int i=0; i<fronts.get(0).length; i++)
                fronts.get(0)[i]=solvedcodes.get(i);
        }
        int[] nfront=new int[ncombos];
        int reached=0;
        for (D=0;; D++) {
            if (fronts.get(D).length==0) break;
            reached+=fronts.get(D).length;
            int sz=0;
            for (int f:fronts.get(D)) {
                int[] scrm=codeCombo(f);
                int mr=freeto[scrm[0]]/C, mc=freeto[scrm[0]]%C;
                int[] mvlist=new int[] {mr*2,mr*2+1,2*R+mc*2,2*R+mc*2+1};
                int invprevmv=D==0?-1:(mvi(f)^1);
                for (int mi:mvlist)
                    if (mvactions[mi]!=null&&mi!=invprevmv) {
                        int nf=comboCode(scrm,mvactions[mi]);
                        if (data[nf]==-1) {
                            data[nf]=compressed(D+1,f,mi);
                            nfront[sz++]=nf;
                        }
                    }
            }
            System.out.println(D+":"+fronts.get(D).length);
            fronts.add(new int[sz]);
            System.arraycopy(nfront,0,fronts.get(D+1),0,sz);
        }
        System.out.println("#reached="+reached);
        if (reached!=ncombos)
            System.out.printf("WARNING: reached=%d!=ncombos=%d%n",reached,ncombos);
        System.out.println("D="+D);
        System.out.println("total time="+(System.currentTimeMillis()-st));
    }
    /*
    encoding ordered combinations
    A[0]...A[K-1], 0<=A[i]<N, all A[i] distinct
    possible to transform permutation [0...N-1] into [....|A]
    using a sequence of swaps (i,J_i) for i=N-1 to N-K inclusive
      --> encode A as J_(N-1)+N*(J_(N-2)+(N-1)*(...+(N-K+2)*J_(N-K)...)
    for this program, N=Nfree, K=K
    */
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
        if (data[code]==-1)
            throw new RuntimeException("No solution.");
        StringBuilder out=new StringBuilder();
        for (int c=code; depth(c)>0; c=par(c)) {
            int mi=mvi(c);
            out.append(mi<2*R?(mi%2==0?"R":"L"):(mi%2==0?"D":"U"));
        }
        return out.toString();
    }
    public String test() {
        for (int code=0; code<ncombos; code++) if (data[code]!=-1) {
            int[] scrm=codeCombo(code);
            System.out.println("tscrm="+Arrays.toString(scrm));
            int[] targets=null;
            for (int c:fronts.get(0)) {
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
        long st=System.currentTimeMillis();
        String[] states={"11111x11111","01110x01110","01110x00010"};
        for (int i=0; i<states.length-1; i++)
            System.out.println(new LoopoverNRGBFS(5,5,2,2,states[i],states[i+1]).test());
        System.out.println("time="+(System.currentTimeMillis()-st));
    }
}
