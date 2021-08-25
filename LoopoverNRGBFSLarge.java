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
    //define absolute indexing as mapping coordinate (r,c) to index r*C+c
    //every scramble is represented by an array L[], where piece i is at location L[i]
    private String folder;
    private int R, C, gr, gc;
    private int F;
    private boolean[][] rcfree, nfree;
    private boolean strict;
    private boolean free(int r, int c) {
        return rcfree[0][r]||rcfree[1][c];
    }
    private int[] tofree, freeto;
    //tofree[r*C+c]=i, where free location (r,c) is assigned to index i
    public int K;
    private int[][] mvactions;
    private int M;
    public long ncombos;
    //bfs stuff
    private long[] visited;
    public int D;
    private void add(long n) {
        visited[(int)(n/64)]|=1L<<(n%64);
    }
    private boolean contains(long n) {
        return (visited[(int)(n/64)]&(1L<<(n%64)))!=0;
    }
    public LoopoverNRGBFSLarge(int R, int C, int gr, int gc, String state0, String state1, boolean strict) {
        folder=R+"x"+C+"NRG("+gr+","+gc+")-"+state0+"-"+state1+(strict?" STRICT":"")+"/";
        System.out.println(folder);
        new File(folder).mkdir();
        this.R=R; this.C=C; this.gr=gr; this.gc=gc; this.strict=strict;
        nfree=parse(state1);
        if (state1.indexOf('x')!=-1) {
            boolean[][] tmp=new boolean[R][C];
            for (int i=0; i<R; i++)
                for (int j=0; j<C; j++) tmp[i][j]=nfree[0][i]||nfree[1][j];
            nfree=tmp;
        }
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
    }
    public void bfs() throws IOException {
        long st=System.currentTimeMillis();
        ncombos=1;
        for (int rep=0; rep<K; rep++) ncombos*=F-rep;
        System.out.println("ncombos="+ncombos);
        if (ncombos/64>400_000_000) throw new RuntimeException("Too many combinations to handle.");
        visited=new long[(int)(ncombos/64+1)];
        int chunk=bb95(ncombos*M).length();
        System.out.println("every combo represented with "+chunk+" character(s)");
        {
            PrintWriter fout=new PrintWriter(new FileWriter(folder+"0.txt"));
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
            List<Integer> grEnds=new ArrayList<>();
            for (int grow=0; grow<R; grow++) {
                for (int gclm=0; gclm<C; gclm++) {
                    boolean good=strict?(grow==gr&&gclm==gc):
                            (nfree[gr][gc]?
                                    (existsrfree&&existscfree?(rnfree[grow]||cnfree[gclm]):
                                            ((gclm==gc||rnfree[gr])&&(grow==gr||cnfree[gc]))):
                                    (grow==gr&&gclm==gc));
                    if (good)
                        grEnds.add(grow*C+gclm);
                    System.out.print(!free(grow,gclm)?"X":
                            good?"*":".");
                }
                System.out.println();
            }
            for (int gloc:grEnds) {
                int[] solvedscrm=new int[K]; solvedscrm[0]=tofree[gloc];
                System.arraycopy(target,0,solvedscrm,1,K-1);
                long solvedscrmcode=comboCode(solvedscrm);
                add(solvedscrmcode);
                fout.print(bb95j(solvedscrmcode*M, chunk));
            }
            fout.close();
        }
        int reached=0;
        for (D=0;; D++) {
            BufferedReader fin=new BufferedReader(new FileReader(folder+D+".txt"));
            PrintWriter fout=new PrintWriter(new FileWriter(folder+(D+1)+".txt"));
            StringBuilder toPrint=new StringBuilder();
            long fsz=0, sz=0;
            while (true) {
                StringBuilder info=new StringBuilder();
                for (int i = 0; i< chunk; i++) {
                    int r=fin.read();
                    if (r==-1) break;
                    info.append((char)r);
                }
                if (info.length()==0) break;
                if (info.length()!=chunk) throw new RuntimeException("\""+info+"\".length()!="+ chunk);
                fsz++;
                long fm=num(info.toString()); int[] scrm=codeCombo(fm/M); int mvi=(int)(fm%M);
                int mr=freeto[scrm[0]]/C, mc=freeto[scrm[0]]%C;
                int[] mvlist=new int[] {mr*2,mr*2+1,2*R+mc*2,2*R+mc*2+1};
                int invprevmv=D==0?-1:(mvi^1);
                for (int mi:mvlist)
                    if (mvactions[mi]!=null&&mi!=invprevmv) {
                        long nf=comboCode(scrm,mvactions[mi]);
                        if (!contains(nf)) {
                            add(nf);
                            toPrint.append(bb95j(nf*M+mi,chunk));
                            sz++;
                            if (sz%1000_000==0) {
                                fout.print(toPrint);
                                toPrint=new StringBuilder();
                            }
                        }
                    }
            }
            fout.print(toPrint);
            fout.close();
            System.out.println(D+":"+fsz);
            reached+=fsz;
            if (sz==0) break;
        }
        System.out.println("\n#reached="+reached);
        if (reached!=ncombos)
            System.out.printf("WARNING: reached=%d!=ncombos=%d%n",reached,ncombos);
        System.out.println("D="+D);
        System.out.println("total time="+(System.currentTimeMillis()-st));
    }
    private long comboCode(int[] A) {
        int[] P=new int[F];
        for (int i = 0; i< F; i++) P[i]=i;
        int[] L=P.clone();
        long out=0, pow=1;
        for (int i = F -1; i>= F -K; i--) {
            //swap idxs i and L[A[i-(N-K)]] in P
            int j=L[A[i-(F -K)]];
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
        int[] P=new int[F];
        for (int i = 0; i< F; i++) P[i]=i;
        int[] L=P.clone();
        long out=0, pow=1;
        for (int i =F-1; i>=F-K; i--) {
            int j=L[f[A[i-(F-K)]]];
            int pi=P[i];
            P[j]=pi;
            L[pi]=j;
            out+=pow*j;
            pow*=i+1;
        }
        return out;
    }
    private int[] codeCombo(long code) {
        int[] P=new int[F];
        for (int i = 0; i< F; i++) P[i]=i;
        for (int v = F; v>F-K; v--) {
            int i=v-1, j=(int)(code%v);
            code/=v;
            int pi=P[i]; P[i]=P[j]; P[j]=pi;
        }
        int[] out=new int[K];
        System.arraycopy(P,F-K,out,0,K);
        return out;
    }
    public static void main(String[] args) throws IOException {
        long st=System.currentTimeMillis();
        new LoopoverNRGBFSLarge(5,5,2,2,"01110x01110","01110x00010",false).bfs();
        new LoopoverNRGBFSLarge(5,5,2,2,"01110x01110","01110x00010",true).bfs();
        new LoopoverNRGBFSLarge(5,5,2,2,"01110x01110","01110x00000",true).bfs();
        System.out.println("time="+(System.currentTimeMillis()-st));
    }
}
