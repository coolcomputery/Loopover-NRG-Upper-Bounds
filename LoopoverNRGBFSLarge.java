import java.util.*;
import java.io.*;
public class LoopoverNRGBFSLarge {
    private static int mod(int n, int k) {
        return (n%k+k)%k;
    }
    private static boolean[] mask(String s) {
        boolean[] out=new boolean[s.length()];
        for (int i=0; i<s.length(); i++)
            out[i]=s.charAt(i)=='1';
        return out;
    }
    private static StringBuilder bb95j(long n, int len) { //BACKWARDS base 95
        StringBuilder tmp=new StringBuilder();
        while (n>0) {
            tmp.append((char)(n%95+32));
            n/=95;
        }
        while (tmp.length()<len) tmp.append(' ');
        return tmp;
    }
    private static StringBuilder bb95(long n) { //BACKWARDS base 95
        if (n==0) return new StringBuilder(" ");
        StringBuilder tmp=new StringBuilder();
        while (n>0) {
            tmp.append((char)(n%95+32));
            n/=95;
        }
        return tmp;
    }
    private static long num(String bb95) {
        long out=0;
        for (int i=bb95.length()-1; i>-1; i--)
            out=out*95+(bb95.charAt(i)-32);
        return out;
    }
    //define absolute indexing as mapping coordinate (r,c) to index r*C+c
    //every scramble is represented by an array L[], where piece i is at location L[i]
    private String folder;
    private int R, C;
    private int Nfree;
    private boolean[] Rfree, Cfree, Rnfree, Cnfree;
    //a location (r,c) is free iff Rfree[r]||Cfree[c]
    private int[] tofree, freeto;
    //tofree[r*C+c]=i, where free location (r,c) is assigned to index i
    public int K;
    private int[] solvedscrm;
    private long solvedscrmcode;
    private int[][] mvactions, mvs;
    private int M;
    public long ncombos;
    //bfs stuff
    private long[] visited;
    public int D;
    private int codelen, mvilen;
    private void add(long n) {
        visited[(int)(n/64)]|=1L<<(n%64);
    }
    private boolean contains(long n) {
        return (visited[(int)(n/64)]&(1L<<(n%64)))!=0;
    }
    public LoopoverNRGBFSLarge(int R, int C, String rf0, String cf0, String rf1, String cf1) {
        folder=R+"x"+C+"-"+rf0+"x"+cf0+"-"+rf1+"x"+cf1+"\\";
        System.out.println(folder);
        new File(folder).mkdir();
        this.R=R; this.C=C;
        Rfree=mask(rf0); Cfree=mask(cf0);
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
        for (int r=0; r<R; r++) {
            for (int c=0; c<C; c++)
                System.out.printf("%3d",tofree[r*C+c]);
            System.out.println();
        }
        Rnfree=mask(rf1); Cnfree=mask(cf1);
        K=1; //include gripped piece
        for (int r=0; r<R; r++)
            for (int c=0; c<C; c++)
                if ((Rfree[r]||Cfree[c])&&!(Rnfree[r]||Cnfree[c]))
                    K++;
        ncombos=1;
        for (int rep=0; rep<K; rep++) ncombos*=Nfree-rep;
        System.out.println("ncombos="+ncombos);
        if (ncombos/64>400_000_000) throw new RuntimeException("Too many combinations to handle.");
        codelen=bb95(ncombos).length();
        mvilen=bb95(M).length();
        System.out.println("every combo represented with "+ codelen +" characters");
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
    }
    public void bfs(int gr, int gc, boolean strict) throws IOException {
        visited=new long[(int)(ncombos/64+1)];
        PrintWriter fout=new PrintWriter(new FileWriter(folder+"0.txt")); {
            for (int grow=0; grow<R; grow++)
            for (int gclm=0; gclm<C; gclm++)
            if (strict?(grow==gr&&gclm==gc):(Rnfree[grow]&&Cnfree[gclm])) {
                int[] solvedscrm=new int[K];
                solvedscrm[0]=tofree[grow*C+gclm];
                for (int r=0, idx=1; r<R; r++)
                    for (int c=0; c<C; c++)
                        if ((Rfree[r]||Cfree[c])&&!(Rnfree[r]||Cnfree[c]))
                            solvedscrm[idx++]=tofree[r*C+c];
                long solvedscrmcode=comboCode(solvedscrm);
                add(solvedscrmcode);
                fout.print(bb95j(solvedscrmcode,codelen).append(bb95j(0,mvilen)));
            }
            fout.close();
        }
        int reached=0;
        for (D=0;; D++) {
            BufferedReader fin=new BufferedReader(new FileReader(folder+D+".txt"));
            fout=new PrintWriter(new FileWriter(folder+(D+1)+".txt"));
            StringBuilder toPrint=new StringBuilder();
            long sz=0;
            while (true) {
                StringBuilder code=new StringBuilder();
                for (int i=0; i<codelen; i++) {
                    int r=fin.read();
                    if (r==-1) break;
                    code.append((char)r);
                }
                if (code.length()==0) break;
                if (code.length()!=codelen) throw new RuntimeException("\""+code+"\".length()!="+codelen);
                sz++;
                long f=num(code.toString());
                int[] scrm=codeCombo(f);
                StringBuilder mvibb95=new StringBuilder();
                for (int i=0; i<mvilen; i++)
                    mvibb95.append((char)fin.read());
                int mr=freeto[scrm[0]]/C, mc=freeto[scrm[0]]%C;
                int[] mvlist=Rfree[mr]?
                        (Cfree[mc]?new int[] {mr*2,mr*2+1,2*R+mc*2,2*R+mc*2+1}:new int[] {mr*2,mr*2+1}):
                        Cfree[mc]?new int[] {2*R+mc*2,2*R+mc*2+1}:new int[] {};
                int invprevmv=D==0?-1:((int)num(mvibb95.toString())^1);
                for (int mi:mvlist)
                    if (mi!=invprevmv) {
                        long nf=comboCode(scrm,mvactions[mi]);
                        if (!contains(nf)) {
                            add(nf);
                            toPrint.append(bb95j(nf,codelen)).append(bb95j(mi,mvilen));
                            sz++;
                            if (sz%1000_000==0) {
                                fout.print(toPrint);
                                toPrint=new StringBuilder();
                            }
                        }
                    }
            }
            if (sz==0) break;
            System.out.println(D+":"+sz);
        }
        System.out.println("\n#reached="+reached);
        if (reached!=ncombos)
            System.out.printf("WARNING: reached=%d!=ncombos=%d%n",reached,ncombos);
        System.out.println("D="+D);
    }
    private long comboCode(int[] A) {
        int[] P=new int[Nfree];
        for (int i=0; i<Nfree; i++) P[i]=i;
        int[] L=P.clone();
        long out=0, pow=1;
        for (int i=Nfree-1; i>=Nfree-K; i--) {
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
    private long comboCode(int[] A, int[] f) {
        int[] P=new int[Nfree];
        for (int i=0; i<Nfree; i++) P[i]=i;
        int[] L=P.clone();
        long out=0, pow=1;
        for (int i=Nfree-1; i>=Nfree-K; i--) {
            int j=L[f[A[i-(Nfree-K)]]];
            int pi=P[i];
            P[j]=pi;
            L[pi]=j;
            out+=pow*j;
            pow*=i+1;
        }
        return out;
    }
    private int[] codeCombo(long code) {
        int[] P=new int[Nfree];
        for (int i=0; i<Nfree; i++) P[i]=i;
        for (int v=Nfree; v>Nfree-K; v--) {
            int i=v-1, j=(int)(code%v);
            code/=v;
            int pi=P[i]; P[i]=P[j]; P[j]=pi;
        }
        int[] out=new int[K];
        System.arraycopy(P,Nfree-K,out,0,K);
        return out;
    }
    public static void main(String[] args) {
        long st=System.currentTimeMillis();
        new LoopoverNRGBFS(5,5,0,0,"11111","11111","11001","11001",false);
        System.out.println("time="+(System.currentTimeMillis()-st));
    }
}
