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
    private int R, C;
    private int Nfree;
    private boolean[] Rfree, Cfree;
    private int[] tofree, freeto;
    public int K;
    private int[] solvedscrm;
    private int solvedscrmcode;
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
    public LoopoverNRGBFS(int R, int C, int gr, int gc, String rf0, String cf0, String rf1, String cf1) {
        //RxC NRG Loopover, gripped piece at (gr,gc) when board is solved
        long st=System.currentTimeMillis();
        this.R=R; this.C=C;
        Rfree=mask(rf0); Cfree=mask(cf0);
        if (!Rfree[gr]&&!Cfree[gc])
            throw new RuntimeException("Gripped piece is locked.");
        tofree=new int[R*C]; freeto=new int[R*C];
        Nfree=0;
        for (int r=0; r<R; r++)
            for (int c=0; c<C; c++)
                if (Rfree[r]||Cfree[c]) {
                    tofree[r*C+c]=Nfree;
                    freeto[Nfree]=r*C+c;
                    Nfree++;
                }
                else tofree[r*C+c]=-1;
        boolean[] Rnfree=mask(rf1), Cnfree=mask(cf1);
        for (int r=0; r<R; r++) {
            for (int c=0; c<C; c++)
                System.out.printf("%4s",
                        (r==gr&&c==gc?"*":Rfree[r]||Cfree[c]?(Rnfree[r]||Cnfree[c]?"":"'"):"X")
                        //X: locked; ': piece that this BFS tree tries to solve; *: gripped piece
                        +tofree[r*C+c]
                );
            System.out.println();
        }
        K=1; //include gripped piece
        for (int r=0; r<R; r++)
            for (int c=0; c<C; c++)
                if ((Rfree[r]||Cfree[c])&&!(Rnfree[r]||Cnfree[c]))
                    K++;
        solvedscrm=new int[K];
        solvedscrm[0]=tofree[gr*C+gc];
        for (int r=0, idx=1; r<R; r++)
            for (int c=0; c<C; c++)
                if ((Rfree[r]||Cfree[c])&&!(Rnfree[r]||Cnfree[c]))
                    solvedscrm[idx++]=tofree[r*C+c];
        System.out.println(Arrays.toString(solvedscrm));
        {
            long tmp=1;
            for (int rep=0; rep<K; rep++) tmp*=Nfree-rep;
            if (tmp>400_000_000) throw new RuntimeException("Too many combinations to handle.");
            ncombos=(int)tmp;
        }
        System.out.println("ncombos="+ncombos);
        M=0;
        for (boolean b:Rfree) if (b) M+=2;
        for (boolean b:Cfree) if (b) M+=2;
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
                        if (Rfree[r]||Cfree[c])
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
                        if (Rfree[r]||Cfree[c])
                            mvactions[idx][tofree[r*C+c]]=tofree[(c==mc?mod(r+s,R):r)*C+c];
                idx++;
            }
        }
        //BFS
        data=new long[ncombos]; Arrays.fill(data,-1);
        fronts=new ArrayList<>();
        solvedscrmcode=comboCode(solvedscrm);
        fronts.add(new int[] {solvedscrmcode});
        data[solvedscrmcode]=0;
        int[] nfront=new int[ncombos];
        int reached=0, returningreached=0;
        //a state is "returning" if it keeps the gripped piece at where it is supposed to be
        //TODO: DISTINGUISH SCRAMBLES BASED ON WHETHER THEY PRESERVE GRIPPED PIECE'S SOLVED LOCATION
        for (D=0;; D++) {
            if (fronts.get(D).length==0) break;
            reached+=fronts.get(D).length;
            int nreturning=0, sz=0;
            for (int f:fronts.get(D)) {
                int[] scrm=codeCombo(f);
                if (scrm[0]==solvedscrm[0]) nreturning++;
                int mr=freeto[scrm[0]]/C, mc=freeto[scrm[0]]%C;
                int[] mvlist={mr*2,mr*2+1,2*R+mc*2,2*R+mc*2+1};
                for (int mi:mvlist) {
                    int nf=comboCode(scrm,mvactions[mi]);
                    if (data[nf]==-1) {
                        data[nf]=compressed(D+1,f,mi);
                        nfront[sz++]=nf;
                    }
                }
            }
            returningreached+=nreturning;
            System.out.println((D)+":"+fronts.get(D).length+","+nreturning);
            fronts.add(new int[sz]);
            System.arraycopy(nfront,0,fronts.get(D+1),0,sz);
        }
        System.out.println("#reached="+reached+", #returningreached="+returningreached);
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
        for (int c=code; c!=solvedscrmcode; c=par(c)) {
            int[] mv=mvs[mvi(c)];
            out.add(new int[] {mv[0],mv[1],-mv[2]});
        }
        return out;
    }
    public static String mvseqStr(List<int[]> S) {
        StringBuilder str=new StringBuilder();
        for (int[] m:S)
            str.append(" ").append(m[0]==0?"R":"C").append(m[1]).append(m[2]==1?"":m[2]==-1?"'":("("+m[2]+")"));
        return str.toString();
    }
    public static void main(String[] args) {
        LoopoverNRGBFS t=new LoopoverNRGBFS(4,4,0,0,"1111","1111","1100","1100"); //GN=27
        System.out.println(mvseqStr(t.solvemvs(t.comboCode(new int[] {6,1,2,3,4}))));
    }
}
