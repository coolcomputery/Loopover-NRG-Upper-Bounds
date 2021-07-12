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
    private int R, C;
    private int Nfree;
    private boolean[][] rcfree;
    private boolean free(int r, int c) {
        return rcfree[0][r]||rcfree[1][c];
    }
    private int[] tofree, freeto;
    public int K;
    //BFS stuff
    private int M;
    private int[][] mvactions, mvs;
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
    public LoopoverNRGBFS(int R, int C, int gr, int gc, String state0, String state1, boolean strict) {
        //RxC NRG Loopover, gripped piece at (gr,gc) when board is solved
        //constraints: if A=# free rows at start state and B=#free clms at start state, then (A>=2&&B>=3)||(A>=3&&B>=2) must be satisfied
        //strict: all scrambles must be solved with gripped piece moved to where it should be in the solved board
        //nonstrict: gripped piece can be anywhere as long as all other pieces that need to be solved are solved
        this.R=R; this.C=C;
        boolean[][] enstatemat=parse(state1);
        if (state1.indexOf('x')!=-1) {
            boolean[][] tmp=new boolean[R][C];
            for (int i=0; i<R; i++)
                for (int j=0; j<C; j++) tmp[i][j]=enstatemat[0][i]||enstatemat[1][j];
            enstatemat=tmp;
        }
        System.out.println(R+"x"+C+": "+state0+" --> "+state1+" "+(strict?"strict":"nonstrict"));
        long st=System.currentTimeMillis();
        rcfree=parse(state0);
        if (!free(gr,gc))
            throw new RuntimeException("Gripped piece is locked.");
        tofree=new int[R*C]; freeto=new int[R*C];
        Nfree=0;
        for (int r=0; r<R; r++)
            for (int c=0; c<C; c++)
                if (free(r,c)) {
                    tofree[r*C+c]=Nfree;
                    freeto[Nfree]=r*C+c;
                    Nfree++;
                }
                else tofree[r*C+c]=-1;
        for (int r=0; r<R; r++) {
            for (int c=0; c<C; c++)
                System.out.printf("%4s",
                        free(r,c)?
                                ((r==gr&&c==gc?"*":(enstatemat[r][c]?"":"'"))
                                        +tofree[r*C+c])
                                :"X"
                        //X: locked; ': piece that this BFS tree tries to solve; *: gripped piece
                );
            System.out.println();
        }
        M=2*R+2*C;
        mvactions=new int[M][]; mvs=new int[M][]; {
            //mvactions[m][i]=free loc. that i-th free loc. will go to after the m-th move is applied
            //mv [0,mr,s] --> idx=mr*2+(s+1)/2
            int idx=0;
            for (int mr=0; mr<R; mr++)
            for (int s=-1; s<=1; s+=2) {
                mvs[idx]=new int[] {0,mr,s};
                mvactions[idx]=new int[Nfree];
                for (int r=0; r<R; r++)
                    for (int c=0; c<C; c++)
                        if (free(r,c))
                            mvactions[idx][tofree[r*C+c]]=tofree[r*C+(r==mr?mod(c+s,C):c)];
                idx++;
            }
            //mv [1,mc,s] --> idx=2*R+mc*2+(s+1)/2
            for (int mc=0; mc<C; mc++)
            for (int s=-1; s<=1; s+=2) {
                mvs[idx]=new int[] {1,mc,s};
                mvactions[idx]=new int[Nfree];
                for (int r=0; r<R; r++)
                    for (int c=0; c<C; c++)
                        if (free(r,c))
                            mvactions[idx][tofree[r*C+c]]=tofree[(c==mc?mod(r+s,R):r)*C+c];
                idx++;
            }
        }
        K=1; //include gripped piece
        for (int r=0; r<R; r++)
            for (int c=0; c<C; c++)
                if (free(r,c)&&!enstatemat[r][c])
                    K++;
        {
            long tmp=1;
            for (int rep=0; rep<K; rep++) tmp*=Nfree-rep;
            if (tmp>400_000_000) throw new RuntimeException("Too many combinations to handle.");
            ncombos=(int)tmp;
            System.out.println("ncombos="+ncombos);
        }
        //BFS
        data=new long[ncombos]; Arrays.fill(data,-1);
        fronts=new ArrayList<>();
        {
            List<Integer> solvedcodes=new ArrayList<>();
            for (int grow=0; grow<R; grow++)
            for (int gclm=0; gclm<C; gclm++)
            if (strict?(grow==gr&&gclm==gc):enstatemat[grow][gclm]) {
                int[] solvedscrm=new int[K];
                solvedscrm[0]=tofree[grow*C+gclm];
                for (int r=0, idx=1; r<R; r++)
                    for (int c=0; c<C; c++)
                        if (free(r,c)&&!enstatemat[r][c])
                            solvedscrm[idx++]=tofree[r*C+c];
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
                int[] mvlist=rcfree[0][mr]?
                                (rcfree[1][mc]?new int[] {mr*2,mr*2+1,2*R+mc*2,2*R+mc*2+1}:new int[] {mr*2,mr*2+1}):
                        rcfree[1][mc]?new int[] {2*R+mc*2,2*R+mc*2+1}:new int[] {};
                int invprevmv=D==0?-1:(mvi(f)^1);
                for (int mi:mvlist)
                if (mi!=invprevmv) {
                    int nf=comboCode(scrm,mvactions[mi]);
                    if (data[nf]==-1) {
                        data[nf]=compressed(D+1,f,mi);
                        nfront[sz++]=nf;
                    }
                }
            }
            System.out.print((D>0?" ":"")+D+":"+fronts.get(D).length);
            fronts.add(new int[sz]);
            System.arraycopy(nfront,0,fronts.get(D+1),0,sz);
        }
        System.out.println("\n#reached="+reached);
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
    public List<int[]> solvemvs(int code) {
        List<int[]> out=new ArrayList<>();
        for (int c=code; depth(c)>0; c=par(c)) {
            int[] mv=mvs[mvi(c)];
            out.add(new int[] {mv[0],mv[1],-mv[2]});
        }
        return out;
    }
    public List<int[]> solvemvs(int[] scramble) {
        return solvemvs(comboCode(scramble));
    }
    public static String mvseqStr(List<int[]> S) {
        StringBuilder str=new StringBuilder();
        for (int[] m:S)
            str.append(" ").append(m[0]==0?"R":"C").append(m[1]).append(m[2]==1?"":m[2]==-1?"'":("("+m[2]+")"));
        return str.toString();
    }
    public static void main(String[] args) {
        long st=System.currentTimeMillis();
        System.out.println(mvseqStr(new LoopoverNRGBFS(4,4,0,0,"1111x1111","1100x1000",true).solvemvs(new int[] {6,5,4,3,2,1,0})));
        System.out.println("time="+(System.currentTimeMillis()-st));
    }
}
