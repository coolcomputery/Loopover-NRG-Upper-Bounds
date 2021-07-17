import java.util.*;
public class LoopoverNRGSetup {
    public static final char[] dirNames={'D','R','U','L'};
    private static int mod(int n, int k) {
        return (n%k+k)%k;
    }
    public static List<int[]> perms(int N) {
        List<int[]> out=new ArrayList<>();
        if (N==1) out.add(new int[] {0});
        else {
            List<int[]> help=perms(N-1);
            for (int[] h:help)
            for (int i=0; i<N; i++) {
                int[] p=new int[N];
                System.arraycopy(h,0,p,0,i);
                p[i]=N-1;
                if (i<N-1) System.arraycopy(h,i,p,i+1,N-1-i);
                out.add(p);
            }
        }
        return out;
    }
    public static class Board {
        int N;
        int[][] board;
        int lr, lc;
        StringBuilder mvs;
        private int loc(int pc) {
            for (int i=0; i<N*N; i++)
                if (board[i/N][i%N]==pc)
                    return i;
            return -1;
        }
        Board(int N, int gr, int gc) {
            this.N=N;
            board=new int[N][N];
            for (int i=0; i<N*N; i++)
                board[i/N][i%N]=i;
            int loc=loc(gr*N+gc);
            lr=loc/N; lc=loc%N;
            mvs=new StringBuilder();
        }
        private void move(int type, int shift) {
            shift=mod(shift,N);
            if (shift>N/2) shift-=N;
            char c;
            if (type==0) {
                int[] T=new int[N];
                for (int j=0; j<N; j++) T[j]=board[lr][j];
                for (int j=0; j<N; j++) board[lr][mod(j+shift,N)]=T[j];
                c=shift<0?'L':'R';
                lc=mod(lc+shift,N);
            }
            else if (type==1) {
                int[] T=new int[N];
                for (int i=0; i<N; i++) T[i]=board[i][lc];
                for (int i=0; i<N; i++) board[mod(i+shift,N)][lc]=T[i];
                c=shift<0?'U':'D';
                lr=mod(lr+shift,N);
            }
            else throw new RuntimeException();
            for (int rep=0; rep<Math.abs(shift); rep++)
                mvs.append(c);
        }
        private void move(String mvs) {
            for (int i=0; i<mvs.length(); i++) {
                char c=mvs.charAt(i);
                if (c=='D') move(1,1);
                else if (c=='R') move(0,1);
                else if (c=='U') move(1,-1);
                else if (c=='L') move(0,-1);
                else throw new RuntimeException();
            }
        }
        private String display() {
            StringBuilder str=new StringBuilder();
            for (int[] r:board) {
                for (int v:r)
                    str.append((N*N<=26?(char)(v+'A'):String.format("%3d",v)));
                str.append("\n");
            }
            return str.toString();
        }
    }
    private static String inv(String mvs) {
        StringBuilder out=new StringBuilder();
        for (int i=mvs.length()-1; i>-1; i--) {
            char c=mvs.charAt(i);
            out.append(c=='D'?'U':c=='R'?'L':c=='U'?'D':'R');
        }
        return out.toString();
    }
    public static String comm(String A, String B) {
        return A+B+inv(A)+inv(B);
    }
    private static String transf(String mvs, int type) {
        if (type<0||type>=4) throw new RuntimeException("invalid transformation type: "+type);
        if (type==3) return inv(mvs);
        StringBuilder out=new StringBuilder();
        for (int i=0; i<mvs.length(); i++) {
            char mv=mvs.charAt(i);
            out.append(
                    type==0?(mv=='L'?'R':mv=='R'?'L':mv): //reflect board left-right
                    type==1?(mv=='U'?'D':mv=='D'?'U':mv): //reflect board top-down
                            (mv=='D'?'R':mv=='R'?'D':mv=='U'?'L':'U') //transpose board
            );
        }
        return out.toString();
    }
    public static String transformed(String alg, int b) {
        String ret=alg;
        for (int t=0; t<4; t++)
            if((b&(1<<t))!=0)
                ret=transf(ret,t);
        return ret;
    }
    public static int[][] effect(int N, String alg) {
        //return {L,tP}
        //where L is an array of locations on the NxN board
        //and the algorithm moves the piece from location L[i] to location L[tP[i]] for each i
        Board bd=new Board(N,0,0);
        bd.move(alg);
        int[] perm=new int[N*N];
        //perm[i]=location that the piece at location i goes to
        for (int i=0; i<N*N; i++) {
            int pc=bd.board[i/N][i%N];
            perm[pc]=i;
        }
        int[] toMovedLocs=new int[N*N]; Arrays.fill(toMovedLocs,-1);
        List<Integer> movedLocs=new ArrayList<>();
        for (int i=0; i<N*N; i++)
        if (perm[i]!=i) {
            toMovedLocs[i]=movedLocs.size();
            movedLocs.add(i);
        }
        int K=movedLocs.size();
        int[] L=new int[K];
        for (int i=0; i<K; i++) L[i]=movedLocs.get(i);
        int[] P=new int[K];
        for (int i=0; i<K; i++)
            P[i]=toMovedLocs[perm[L[i]]];
        return new int[][] {L,P};
    }
    public static String canonical(int N, String alg) {
        //remove redundant moves from alg
        StringBuilder str=new StringBuilder();
        for (int i=0; i<alg.length(); i++)
            if (str.length()>0&&inv(""+str.charAt(str.length()-1)).equals(""+alg.charAt(i)))
                str.deleteCharAt(str.length()-1);
            else
                str.append(alg.charAt(i));
        StringBuilder out=new StringBuilder();
        for (int i=0; i<str.length();) {
            int j=i;
            while (j<str.length()&&str.charAt(i)==str.charAt(j))
                j++;
            int len=(j-i)%N;
            char mv=str.charAt(i);
            if (len>N/2) {
                len=N-len;
                mv=inv(""+mv).charAt(0);
            }
            else if (2*len==N)
                mv=mv=='L'?'R':mv=='U'?'D':mv;
            for (int k=0; k<len; k++)
                out.append(mv);
            i=j;
        }
        return out.toString();
    }

    //start of BFS part
    private int N, V, K;
    public int[] tP;
    private String[] algs, sols;
    private List<List<int[]>> ptsetss;
    public int diam;
    private int code(int[] vs) {
        //map every tuple of K int.s in range [0,V) to a number
        int out=0;
        for (int i=0, pow=1; i<K; i++, pow*=V)
            out+=vs[i]*pow;
        return out;
    }
    private int[] decode(int code) {
        int[] out=new int[K];
        for (int i=0; i<K; i++, code/=V)
            out[i]=code%V;
        return out;
    }
    public LoopoverNRGSetup(int N, Collection<String> algs_init, int[] tP) {
        this.N=N; V=N*N;
        this.tP=tP;
        {
            Set<String> tmp=new TreeSet<>(new Comparator<String>() {
                @Override
                public int compare(String o1, String o2) {
                    return o1.length()==o2.length()?o1.compareTo(o2):o1.length()-o2.length();
                }
            });
            //include inverses and reflections of the initial algorithms
            for (String alg_init:algs_init) {
                String red=canonical(N,alg_init);
                //say two move sequences A,B are similar if there exists a move sequence S s.t. A=S B inv(S)
                //then if A and B are blobs, they cycle the same number of pieces in the same fashion
                //  i.e. if A is a 3-cycle, then so is B; if a is a 2,2-cycle, then so is B
                //for A=[A[0], A[1], ... A[K-1]], define (A<<a) to be [A[a], A[a+1], ... A[K-1], A[0], ..., A[a-1]]
                //then A is similar to (A<<a) for all A,a
                //we want to rotate A s.t. the beginning and end moves are not both horizontal or both vertical
                //this is so that for any S, canonical(S+A+inv(S)).length() >= canonical(A).length()
                while (red.length()>1) {
                    char s=red.charAt(0), e=red.charAt(red.length()-1);
                    boolean sh=s=='R'||s=='L', eh=e=='R'||e=='L';
                    if (sh==eh)
                        red=canonical(N,red.substring(1)+""+s);
                    else break;
                }
                for (int b=0; b<16; b++) {
                    String ret=canonical(N,transformed(red,b));
                    tmp.add(ret);
                }
            }
            //System.out.println("# algs after rotations/inverses/reflections="+tmp.size());
            this.algs=new String[tmp.size()];
            int i=0;
            for (String s:tmp) algs[i++]=s;
        }
        K=tP.length;
        ptsetss=new ArrayList<>();
        List<int[]> Qs=perms(K);
        for (int i=0; i<algs.length; i++) {
            int[][] effect=effect(N,algs[i]);
            int[] L=effect[0], P=effect[1];
            if (K!=L.length)
                throw new RuntimeException("Mismatch in # changed pieces: "+Arrays.toString(L)+".length!="+K);
            //(L,P) describes the permutation action "location L[i] --> location L[P[i]] for all i"
            //convert L to L' s.t. (L,P) and (L',tP) describe equivalent permutation actions
            //find all Q s.t. "L[i]-->L[P[i]] for all i" == "L[Q[i]]-->L[Q[tP[i]] for all i"
            //--> find all Q s.t. "i-->P[i]" == "Q[i]-->Q[tP[i]]"
            //--> find all Q s.t. P[Q[i]]=Q[tP[i]] for all i
            ptsetss.add(new ArrayList<>());
            for (int[] Q:Qs) {
                boolean match=true;
                for (int k=0; k<K && match; k++)
                    if (P[Q[k]]!=Q[tP[k]]) match=false;
                if (match) {
                    int[] ptset=new int[K];
                    for (int k=0; k<K; k++) ptset[k]=L[Q[k]];
                    ptsetss.get(i).add(ptset);
                }
            }
            //System.out.print(algs[i]); for (int[] ptset:ptsetss.get(i)) System.out.print(" "+Arrays.toString(ptset)); System.out.println();
            if (ptsetss.get(i).size()==0)
                throw new RuntimeException("Incongruent permutations: "+Arrays.toString(P)+"!=tP="+Arrays.toString(tP));
        }
        search();
    }
    private void search() {
        long sttime=System.currentTimeMillis();
        int AMT=1; for (int rep=0; rep<K; rep++) AMT*=V;
        sols=new String[AMT];
        long expreached=1;
        for (int rep=0; rep<K; rep++) expreached*=N*N-1-rep;
        class Pc {
            int code; String sol, orig;
            Pc(int c, String s, String o) {
                code=c;
                sol=s;
                orig=o;
            }
            public String toString() {
                return code+","+sol+","+orig;
            }
        }
        Set<String> seen=new HashSet<>();
        List<List<Pc>> fronts=new ArrayList<>();
        for (int ai=0; ai<algs.length; ai++) {
            String a=algs[ai];
            int c=a.length();
            //System.out.println(a);
            for (int[] ptset:ptsetss.get(ai)) {
                int code=code(ptset);
                sols[code]=a;
                while (c>=fronts.size()) fronts.add(new ArrayList<>());
                fronts.get(c).add(new Pc(code,a,a));
            }
        }
        for (int co=0; co<fronts.size(); co++) if (fronts.get(co).size()>0) {
            List<Pc> front=fronts.get(co);
            int fsz=0;
            for (int fi=0; fi<front.size(); fi++) {
                /*if (front.get(fi).sol.equals("LURULDRDDLDRULURULURDLDDRDLURU"))
                    System.out.println(front.get(fi)+" co="+co+"; ...="+sols[front.get(fi).code].length());*/
                if (sols[front.get(fi).code].length()==co&&!seen.contains(front.get(fi).toString())) {
                    fsz++;
                    seen.add(front.get(fi).toString());
                    int f=front.get(fi).code;
                    int[] locs=decode(f);
                    for (int d=0; d<4; d++) { //D, R, U, L
                        int shift=d/2==0?-1:1; //imagine moving the gripped piece in direction d
                        //then relative to the gripped piece, all other pieces move in the opposite direction
                        int[] nlocs=new int[locs.length];
                        for (int i=0; i<locs.length; i++) {
                            int r=locs[i]/N, c=locs[i]%N;
                            if (d%2==0) {
                                if (c!=0) r=mod(r-shift,N);
                            }
                            else {
                                if (r!=0) c=mod(c-shift,N);
                            }
                            nlocs[i]=r*N+c;
                        }
                        String nalg=canonical(N,(""+dirNames[d])+front.get(fi).sol+(""+dirNames[(d+2)%4]));
                        int nco=nalg.length();
                        int code=code(nlocs);
                        if (sols[code]==null||nco<=sols[code].length()) {
                            if (nco<co&&(sols[code]==null||nco<sols[code].length()))
                                throw new RuntimeException("Negative-weight edge in configuration graph: "
                                        +front.get(fi).sol+" --> "+nalg+" (orig="+front.get(fi).orig+") (code="+code+")");
                            //^^^only throw this exception if we actually try traversing a negative-weight edge
                            if (sols[code]==null||nco<sols[code].length())
                                sols[code]=nalg;
                            /*if (nalg.equals("LLURULDRDDLDRULURULURDLDDRDLURUR"))
                                System.out.println(sols[code]+" "+code);*/
                            if (nco==co) {
                                front.add(new Pc(code,nalg,front.get(fi).orig));
                                //System.out.println(sols[f]+" --> "+nalg);
                            }
                            else {
                                while (nco>=fronts.size()) fronts.add(new ArrayList<>());
                                fronts.get(nco).add(new Pc(code,nalg,front.get(fi).orig));
                            }
                        }
                    }
                }
            }
            System.out.print(" "+co+":"+fsz);
        }
        System.out.println();
        diam=0;
        for (int code=0; code<AMT; code++)
            if (sols[code]!=null) diam=Math.max(diam,sols[code].length());
        int[] freq=new int[diam+1];
        for (int code=0; code<AMT; code++) if (sols[code]!=null) freq[sols[code].length()]++;
        System.out.println("final distribution:");
        for (int d=0; d<=diam; d++) if (freq[d]>0) System.out.print(" "+d+":"+freq[d]);
        int reached=0; for (int v:freq) reached+=v;
        if (reached!=expreached) throw new RuntimeException("Unexpected # of nodes reached: "+reached+" instead of "+expreached);
        System.out.printf("\nN=%d,tP=%s,diameter=%d,BFS time=%d%n",N,Arrays.toString(tP),diam,(System.currentTimeMillis()-sttime));
    }
    //end of BFS part

    //L[] is an array of locations on the board
    public int tupleCode(int[] L, int lr, int lc) {
        if (L.length!=K) throw new RuntimeException("Mismatch in number of pieces: "+L.length+"!="+K);
        int[] nL=new int[K];
        for (int i=0; i<K; i++) nL[i]=mod(L[i]/N-lr,N)*N+mod(L[i]%N-lc,N);
        return code(nL);
    }
    public int cost(int v) {
        return sols[v]==null?-1:sols[v].length();
    }
    public int cost(int[] L, int lr, int lc) {
        return cost(tupleCode(L,lr,lc));
    }
    public String sol(int v) {
        return sols[v];
    }
    public String sol(int[] L, int lr, int lc) {
        return sol(tupleCode(L,lr,lc));
    }
    public static LoopoverNRGSetup cyc3(int N) {
        List<String> algs=new ArrayList<>();
        if (N>=4)
            algs.add("RDLUURDLDLURDRULLDRUULDRDRULDLUR"); //32-move 3-cycle
        if (N==5)
            algs.add("DDLDLDRULURRUURULDRDLDLLDRDLURURURULURDL");
        else if (N>5)
            algs.addAll(Arrays.asList(
                    "DDDDLDRULURUUULDRDLURDDLDRDLURUUULDRULUR",
                    "DDDDLDRULURUUURDLDRULDDLDRDLURUUURDLURUL"
            ));
        if (N%2==0) {
            for (int height=1; height<=N/2; height++) {
                StringBuilder rd=new StringBuilder();
                for (int r=0; r<N/2; r++) rd.append('R');
                for (int r=0; r<height; r++) rd.append('D');
                StringBuilder alg=new StringBuilder();
                alg.append(rd).append(rd);
                if (height<N/2)
                    for (int i=0; i<N+2*height; i++)
                        alg.append(inv(""+alg.charAt(i)));
                alg.append(alg);
                algs.add(alg.toString());
            }
        }
        return algs.size()>0?
                new LoopoverNRGSetup(N,algs,new int[] {1,2,0}):
                null;
    }
    public static LoopoverNRGSetup cyc2n2(int N) {
        if (N<5) return null;
        List<String> algs=new ArrayList<>(Arrays.asList(
                "DDLDRULURULURDLDDRDLURULURULDR",
                "DDLDLURDRUURDLDLUULDRDRUURULDLUR",
                "DDLDRULURURULDRDLLDRDLURURULURDL",
                "DLDLDRURULULDRDLURDRULDRDLULURUR"
        ));
        if (N==5)
            algs.addAll(Arrays.asList(
                    "DDLDLURDRDDRDRULDLDDLULDRURURURDLUL",
                    "DDLDRDLURDDLURDLDRDDLDRULURULURULDR",
                    "DDLDRDLURDDRULDRDLDDLDRULURURULURDL",
                    "DDLDLDRULURRUULDRDLURDLLDRDLURURULDRULUR",
                    "DDLDLDRULURRUULURDLDRDLLDRDLURURULURULDR"
            ));
        else if (N==6)
            algs.addAll(Arrays.asList(
                    "DDLDRDDLURDDLDRDDLURDDLDRDDLUR, DDLDRULURULURDLDDRDLURULURULDR, DDDLDRULURUULURDDLDDRDLURULURUULDR, DDDLDRULURUURULDDRDLLDRDLURURULUURDL, DDLDDLDRULURURUULDRDDLLDRDLURURUULUR, DDDLDLURDRDDRDRULDLDDDLULDRURUURURDLUL, DDDLDRDLURDDLURDDLDRDDLDRULURULURUULDR, DDDLDRDLURDDLURDLDRDDDLDRULURUULURULDR, DDDLDRDLURDDRULDDRDLDDLDRULURURULUURDL, DDDLDRDLURDDRULDRDLDDDLDRULURUURULURDL, DDDLDDRULUURUULDRDLURDLDDRDLUURUULDRULUR, DDDLDDRULUURUULURDLDRDLDDRDLUURUULURULDR, DDDLDDRULUURUURDLDRULDLDDRDLUURUURDLURUL, DDDLDDRULUURUURULDRDLDLDDRDLUURUURULURDL, DDDLDLLURDRRDDRURDLULULLULDRRURDDRDRULDL, DDDLDLURDRDDRRURDLLULULULDRURDDRDRRULDLL, DDLDLDRULURRUULDRDLURDLLDRDLURURULDRULUR".split(", ")
            ));
        else
            algs.addAll(Arrays.asList(
                    "DDLDRULURULURDLDDRDLURULURULDR, DDDDLDRUULURUULDRDDDDLURUULDRUULUR, DDDLDRULURUULURDDLDDRDLURULURUULDR, DDDLDRULURUURULDDRDLLDRDLURURULUURDL, DDLDDLDRULURURUULDRDDLLDRDLURURUULUR, DDDDLDRUULURUULURDDLDDRDDLURUULURUULDR, DDDLDDRULUURUULURDDLDDDRDLUURULURUULDR, DDDDLDRUULURUURULDDRDLLDRDDLURUURULUURDL, DDDDLULDRURUUURDRULDLDDLDLURDRUUURURDLUL, DDDDLURULDRUUULDRDLURDDLURDLDRUUULDRULUR, DDDDLURULDRUUURDLDRULDDLURDLDRUUURDLURUL, DDDLDDRULUURUULDRDLURDLDDRDLUURUULDRULUR, DDDLDDRULUURUURDLDRULDLDDRDLUURUURDLURUL, DDDLDDRULUURUURULDDRDLLDDRDLUURURULUURDL, DDDLLULDRRURUURDRULDLDLDLLURDRRUURURDLUL, DDDLULDRURUURDRRULDLLDLDLURDRUURRURDLLUL, DDLDDLDDRULUURURUULDRDDLLDDRDLUURURUULUR, DDLDLDRULURRUULDRDLURDLLDRDLURURULDRULUR".split(", ")
            ));
        return new LoopoverNRGSetup(N,algs,new int[] {1,0,3,2});
    }
    public static void verify(LoopoverNRGSetup bfs) {
        if (bfs==null) return;
        long st=System.currentTimeMillis();
        int N=bfs.N, K=bfs.K;
        int[] perm=bfs.tP;
        //test every ordered tuple of K tiles in an NxN board, without the gripped piece
        int[] att=new int[K];
        int lr=N/2, lc=N/2;
        int[] opens=new int[N*N-1];
        for (int i=0, id=0; i<N*N; i++) {
            if (i!=lr*N+lc) {
                opens[id]=i;
                id++;
            }
        }
        int diam=0;
        while (att[K-1]<N*N-1) {
            boolean norepeat=true;
            for (int i=0; i<K; i++)
                for (int j=0; j<i; j++)
                    if (att[i]==att[j]) norepeat=false;
            if (norepeat) {
                int[] permd_locs=new int[K]; for (int i=0; i<K; i++) permd_locs[i]=opens[att[i]];
                String sol=bfs.sol(permd_locs,lr,lc);
                diam=Math.max(diam,sol.length());
                Board b=new Board(N,lr,lc);
                b.move(sol);
                int[] loc=new int[N*N];
                for (int i=0; i<N*N; i++)
                    loc[b.board[i/N][i%N]]=i;
                int[] expected=new int[N*N];
                for (int i=0; i<N*N; i++)
                    expected[i]=i;
                for (int i=0; i<K; i++)
                    expected[permd_locs[i]]=permd_locs[perm[i]];
                boolean match=true;
                for (int i=0; i<N*N && match; i++)
                    if (loc[i]!=expected[i])
                        match=false;
                if (!match) {
                    System.out.println("!!!ERROR!!!");
                    System.out.println("sol="+sol);
                    System.out.println("tP="+Arrays.toString(perm)
                            +",permd_locs="+Arrays.toString(permd_locs)
                            +"\n"+b.display());
                    return;
                }
            }
            att[0]++;
            for (int i=0; i<K-1 && att[i]==N*N-1; i++) {
                att[i]=0;
                att[i+1]++;
            }
        }
        if (diam!=bfs.diam)
            System.out.println("!!!MISMATCH: verifier's observed diameter="+diam);
        System.out.println("verification time="+(System.currentTimeMillis()-st));
    }
    public static void main(String[] args) {
        for (int N=4; N<=6; N++) {
            verify(cyc3(N));
            verify(cyc2n2(N));
        }
    }
}
