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
            Set<String> tmp=new HashSet<>();
            //include inverses, reflections, and move sequence rotations of the initial algorithms
            for (String alg_init:algs_init) {
                String red=canonical(N,alg_init);
                //every rotated version of a X-cycle is another X-cycle
                //to see why, let a X-cycle algorithm consist of moves M=[M[0]...M[L-1]]
                //then any rotated version M[a]...M[L-1] M[0]...M[a-1] can be written as S M S^-1,
                //where S=inv([M[0]...M[a-1]])
                //i.e. every rotated version of M is M combined with some setup moves
                //we make these rotated versions of these algorithms ahead of time in order to avoid
                //  a ConcurrentModificationException later on (i.e. we avoid traversing 0-length edges in our graph)
                //System.out.println(alg_init+"-->"+red);
                for (int i=0; i<red.length(); i++) {
                    StringBuilder s=new StringBuilder();
                    for (int k=0; k<red.length(); k++)
                        s.append(red.charAt((k+i)%red.length()));
                    for (int b=0; b<16; b++) {
                        String ret=canonical(N,transformed(s.toString(),b));
                        tmp.add(ret);
                    }
                }
            }
            System.out.println("# algs after rotations/inverses/reflections="+tmp.size());
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
        bfs();
    }
    private void bfs() {
        long sttime=System.currentTimeMillis();
        int AMT=1; for (int rep=0; rep<K; rep++) AMT*=V;
        sols=new String[AMT];
        List<Set<Integer>> tuplesAtCost=new ArrayList<>();
        for (int ai=0; ai<algs.length; ai++) {
            String alg=algs[ai];
            int c=alg.length();
            for (int[] ptset:ptsetss.get(ai)) {
                int code=code(ptset);
                if (sols[code]==null||c<sols[code].length()) {
                    if (sols[code]!=null)
                        tuplesAtCost.get(sols[code].length()).remove(code);
                    sols[code]=alg;
                    while (c>=tuplesAtCost.size()) tuplesAtCost.add(new HashSet<>());
                    tuplesAtCost.get(c).add(code);
                }
            }
        }
        diam=0;
        long reached=0;
        for (int co=0; co<tuplesAtCost.size(); co++) //Dijkstra's algorithm
        if (tuplesAtCost.get(co).size()>0) {
            System.out.println(co+":"+tuplesAtCost.get(co).size());
            reached+=tuplesAtCost.get(co).size();
            diam=Math.max(diam,co);
            for (int f:tuplesAtCost.get(co)) {
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
                    String nalg=canonical(N,(""+dirNames[d])+sols[f]+(""+dirNames[(d+2)%4]));
                    int nco=nalg.length();
                    int code=code(nlocs);
                    if (sols[code]==null||nco<sols[code].length()) {
                        if (nco<co) throw new RuntimeException("Negative-weight edge in configuration graph: "+sols[f]+" --> "+nalg);
                        //^^^only throw this exception if we actually try traversing a negative-weight edge
                        if (sols[code]!=null)
                            tuplesAtCost.get(sols[code].length()).remove(code);
                        sols[code]=nalg;
                        while (nco>=tuplesAtCost.size()) tuplesAtCost.add(new HashSet<>());
                        tuplesAtCost.get(nco).add(code);
                    }
                }
            }
            tuplesAtCost.set(co,null);
        }
        long expreached=1;
        for (int rep=0; rep<K; rep++) expreached*=N*N-1-rep;
        if (reached!=expreached) throw new RuntimeException("Unexpected # of nodes reached: "+reached+" instead of "+expreached);
        System.out.printf("K=%d,diameter=%d,BFS time=%d%n",K,diam,(System.currentTimeMillis()-sttime));
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
    //a "blob" is a move sequence that leads to no net displacement in the gripped piece
    public static LoopoverNRGSetup cyc3bfs(int N) {
        //3-cycle: pt 0 --> pt 1 --> pt 2 --> pt0
        List<String> algs=new ArrayList<>();
        if (N>=4)
            algs.add("RDLUURDLDLURDRULLDRUULDRDRULDLUR"); //32-move 3-cycle
        //below commutators found by brute-force search of all 3-cycles comm(A,B) for length-10 blobs A, B
        if (N==5)
            algs.addAll(Arrays.asList(
                    comm("RDRURDLULL","ULULDRURDD"),
                    comm("UURDRULDLD","LLDLURDRUR"),
                    comm("LLDLURDRUR","URURDLULDD"),
                    comm("LLDRDLURUR","URULURDLDD")
            ));
        else if (N>5)
            algs.addAll(Arrays.asList(
                    comm("LURDLULDRR","RRURDLULDL"),
                    comm("RDRURDLULL","LDRULDLURR"),
                    comm("LLURDRULDR","RURDRULDLL"),
                    comm("LULDLURDRR","RRDLULDRUL"),
                    comm("DDLDRULURU","UULDRDLURD"),
                    comm("DDRULURDLU","UULURDLDRD"),
                    comm("LULDLURDRR","RDLURDRULL"),
                    comm("UURULDRDLD","DLURDLDRUU")
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
    public static LoopoverNRGSetup swap22bfs(int N) {
        //double swapper: pt 0 <--> pt 1, pt 2 <--> pt 3
        if (N>=5) {
            //below commutators found by brute-force search of all 2,2-cycle strict blobs
            List<String> algs=Arrays.asList(
                    "DDLDRULURULURDLDDRDLURULURULDR",
                    "DDLDLURDRUURDLDLUULDRDRUURULDLUR",
                    "DDLDRULURURULDRDLLDRDLURURULURDL",
                    "DLDLDRURULULDRDLURDRULDRDLULURUR"
            );
            if (N==5)
                algs.addAll(Arrays.asList(
                        comm("UULDRDLURD","LDLDRULURR"),
                        comm("LDLULDRURR","DRDRULDLUU"),
                        comm("LDLDRULURR","RURULDRDLL"),
                        comm("RRULURDLDL","DRDLDRULUU"),
                        comm("LLURDRULDR","UURDRULDLD"),
                        comm("LDRULDLURR","RDLURDRULL"),
                        comm("LDRULDLURR","DRDRULDLUU"),
                        comm("RRDRULDLUL","DLDLURDRUU"),
                        comm("LLDRDLURUR","UULURDLDRD"),
                        comm("LLURULDRDR","LLDRDLURUR"),
                        comm("UURDLDRULD","DDRULURDLU"),
                        comm("RRDLDRULUL","LLURULDRDR"),
                        comm("DDLURULDRU","UURDLDRULD"),
                        comm("DDRURDLULU","LDRULDLURR"),
                        comm("DDLULDRURU","DRDRULDLUU"),
                        comm("LURDLULDRR","RDLURDRULL"),
                        comm("UULDLURDRD","DRDRULDLUU"),
                        comm("UULDRDLURD","DRULDRDLUU"),
                        comm("RRDLULDRUL","LDRULDLURR"),
                        comm("DRDRULDLUU","DLDLURDRUU")
                ));
            else if (N==6)
                algs.addAll(Arrays.asList(
                        comm("DDLURULDRU","URUULDRDDL"),
                        comm("RURDRULDLL","RDLULLDRUR"),
                        comm("UULDLURDRD","DRRURDLLUL"),
                        comm("URUULDRDDL","DRDLDRULUU"),
                        comm("LLDRDLURUR","ULUURDLDDR"),
                        comm("ULDDRDLUUR","UULURDLDRD"),
                        comm("URUULDRDDL","DLDRDLURUU"),
                        comm("DDLULDRURU","UURDRULDLD"),
                        comm("URURDLULDD","LULLDRURRD"),
                        comm("URULURDLDD","DDRDLURULU"),
                        comm("LDRULDLURR","DRDRULDLUU"),
                        comm("UULURDLDRD","DDRDLURULU"),
                        comm("ULDRDDLURU","UURULDRDLD"),
                        comm("RDRDLURULL","LULURDLDRR"),
                        comm("DDRURDLULU","LDRULDLURR"),
                        comm("DRDLDRULUU","RUULURDDLD"),
                        comm("LDLLURDRRU","LDRRURDLLU"),
                        comm("DRDRULDLUU","LLDLURRDRU"),
                        comm("URRDRULLDL","ULULDRURDD"),
                        comm("DDLDRULURU","UULURDDLDR"),
                        comm("RULUURDLDD","DLDRDLURUU"),
                        comm("URRDLULLDR","LDLULDRURR"),
                        comm("UULDRDLURD","DRULDRDLUU"),
                        comm("DLDLURDRUU","UURDRULDLD"),
                        comm("LURRDRULLD","LULDLURDRR"),
                        comm("LDLULDRURR","URRDRULLDL"),
                        comm("LLULDRRURD","UURDRULDLD"),
                        comm("LLDLURDRUR","RURDLLULDR"),
                        comm("LDDRULUURD","UULURDLDRD"),
                        comm("LULDRRURDL","RDRURDLULL"),
                        comm("RRULDLLURD","ULDLLURDRR"),
                        comm("URDLURULDD","RDDLDRUULU"),
                        comm("LLDRURDLUR","RRULDLURDL"),
                        comm("UURDLDDRUL","DDRDLUURUL"),
                        comm("ULURULDRDD","DRDLDRULUU"),
                        comm("UURDLDRULD","RDRDLURULL"),
                        comm("ULLDRURRDL","RURDRULDLL"),
                        comm("DLURDLDRUU","URDLURULDD"),
                        comm("DLLULDRRUR","RRULDLURDL"),
                        comm("RUULURDDLD","RRDLDRULUL"),
                        comm("LDDRDLUURU","UURULDRDLD"),
                        comm("LULDLURDRR","LURDRRULDL"),
                        comm("ULDLLURDRR","RRDRULDLUL"),
                        comm("DLDLURDRUU","URRDRULLDL"),
                        comm("RRDRULDLUL","LULLDRURRD"),
                        comm("RDLUURULDD","DDRDLUURUL"),
                        comm("RURRDLULLD","DLDLURDRUU"),
                        comm("LLULDRURDR","RURDLLULDR"),
                        comm("DRULLDLURR","DRURRDLULL"),
                        comm("RRDRULLDLU","ULULDRURDD"),
                        comm("RRULURDLDL","DDLDRUULUR"),
                        comm("RULUURDLDD","RDRDLURULL"),
                        comm("ULDDRDLUUR","UURULDRDLD"),
                        comm("DRDDLURUUL","UURDLDRULD"),
                        comm("LLURDRULDR","RRULDLURDL"),
                        comm("DRDDLURUUL","UURULDRDLD"),
                        comm("RRDLULDRUL","DDLULDRURU"),
                        comm("DRRULDLLUR","LLULDRURDR"),
                        comm("UULURDDLDR","DLDRDLURUU"),
                        comm("DDLDRUULUR","UURULDRDLD"),
                        comm("ULDRULURDD","DLURDLDRUU"),
                        comm("RRULURDLDL","DLDDRULUUR"),
                        comm("UULURDLDRD","DDLDRULURU"),
                        comm("RDRURDLULL","LLULDRRURD"),
                        comm("UURULDRDLD","URDLDDRULU"),
                        comm("LLULDRURDR","URRDRULLDL"),
                        comm("URRDRULLDL","RULLDLURRD"),
                        comm("DRDLDRULUU","RULUURDLDD"),
                        comm("RDLDDRULUU","LULURDLDRR"),
                        comm("RDLURDRULL","LLDRURDLUR"),
                        comm("LDRDDLURUU","RRULURDLDL"),
                        comm("ULURULDRDD","DLDRUULURD"),
                        comm("LDRRURDLLU","LULDLURDRR"),
                        comm("URDLURULDD","DRDDLURUUL"),
                        comm("DLLURDRRUL","DRRURDLLUL"),
                        comm("URURDLULDD","UULDLURDRD"),
                        comm("LULURDLDRR","LDLDRULURR"),
                        comm("LURUULDRDD","LLDRDLURUR"),
                        comm("DLDDRULUUR","LUURDLDDRU"),
                        comm("URRDRULLDL","LDRULDLURR"),
                        comm("ULUURDLDDR","DRULDRDLUU"),
                        comm("UULDLURDRD","UURDRULDLD"),
                        comm("DDRDLURULU","ULURULDRDD"),
                        comm("URDRRULDLL","LLULDRURDR"),
                        comm("RURDRULDLL","LULDLURDRR"),
                        comm("UURDLDRULD","RDDLDRUULU")
                ));
            else
                algs.addAll(Arrays.asList(
                        comm("DDLURULDRU","URUULDRDDL"),
                        comm("RURDRULDLL","RDLULLDRUR"),
                        comm("UULDLURDRD","DRRURDLLUL"),
                        comm("LLDRDLURUR","ULUURDLDDR"),
                        comm("URDRRULDLL","DLULLDRURR"),
                        comm("ULDDRDLUUR","UULURDLDRD"),
                        comm("URUULDRDDL","DRDDLURUUL"),
                        comm("DDLULDRURU","UURDRULDLD"),
                        comm("URDRRULDLL","DLLULDRRUR"),
                        comm("URURDLULDD","LULLDRURRD"),
                        comm("LDRULDLURR","DRDRULDLUU"),
                        comm("ULDRDDLURU","UURULDRDLD"),
                        comm("RDRDLURULL","LULURDLDRR"),
                        comm("DDLDRUULUR","UURULDDRDL"),
                        comm("DDRURDLULU","LDRULDLURR"),
                        comm("URUULDRDDL","LDRDDLURUU"),
                        comm("LDLLURDRRU","LDRRURDLLU"),
                        comm("LLULDRRURD","DRURRDLULL"),
                        comm("DRDRULDLUU","LLDLURRDRU"),
                        comm("URRDRULLDL","ULULDRURDD"),
                        comm("URRDLULLDR","LDLULDRURR"),
                        comm("UULDRDLURD","DRULDRDLUU"),
                        comm("DLDLURDRUU","UURDRULDLD"),
                        comm("LURRDRULLD","LULDLURDRR"),
                        comm("LLULDRRURD","UURDRULDLD"),
                        comm("RRURDLLULD","LULLDRURRD"),
                        comm("LLDLURDRUR","RURDLLULDR"),
                        comm("LDDRULUURD","UULURDLDRD"),
                        comm("LULDRRURDL","RDRURDLULL"),
                        comm("ULDLLURDRR","RRURDLLULD"),
                        comm("RRULDLLURD","ULDLLURDRR"),
                        comm("URDLURULDD","RDDLDRUULU"),
                        comm("LLDRURDLUR","RRULDLURDL"),
                        comm("UURDLDDRUL","DDRDLUURUL"),
                        comm("UURDLDRULD","RDRDLURULL"),
                        comm("RULUURDLDD","RDLDDRULUU"),
                        comm("ULLDRURRDL","RURDRULDLL"),
                        comm("DLURDLDRUU","URDLURULDD"),
                        comm("DLLULDRRUR","RRULDLURDL"),
                        comm("RUULURDDLD","RRDLDRULUL"),
                        comm("LDDRDLUURU","LUURULDDRD"),
                        comm("RRDRULLDLU","LLDLURRDRU"),
                        comm("DLLULDRRUR","RRDRULLDLU"),
                        comm("LULDLURDRR","LURDRRULDL"),
                        comm("DLDLURDRUU","URRDRULLDL"),
                        comm("LDDRDLUURU","RUULURDDLD"),
                        comm("RDLUURULDD","DDRDLUURUL"),
                        comm("RURRDLULLD","DLDLURDRUU"),
                        comm("LLULDRURDR","RURDLLULDR"),
                        comm("DRULLDLURR","DRURRDLULL"),
                        comm("RRDRULLDLU","ULULDRURDD"),
                        comm("RRULURDLDL","DDLDRUULUR"),
                        comm("LULLDRURRD","URRDRULLDL"),
                        comm("RULUURDLDD","RDRDLURULL"),
                        comm("ULDDRDLUUR","UURULDRDLD"),
                        comm("DRDDLURUUL","UURDLDRULD"),
                        comm("LLURDRULDR","RRULDLURDL"),
                        comm("RUULURDDLD","DDLDRUULUR"),
                        comm("RRDLULDRUL","DDLULDRURU"),
                        comm("DRRULDLLUR","LLULDRURDR"),
                        comm("ULDRULURDD","DLURDLDRUU"),
                        comm("RRULURDLDL","DLDDRULUUR"),
                        comm("UURULDRDLD","URDLDDRULU"),
                        comm("URRDRULLDL","RULLDLURRD"),
                        comm("RDLDDRULUU","LULURDLDRR"),
                        comm("RDLURDRULL","LLDRURDLUR"),
                        comm("LDRDDLURUU","RRULURDLDL"),
                        comm("ULURULDRDD","DLDRUULURD"),
                        comm("LDRRURDLLU","LULDLURDRR"),
                        comm("URDLURULDD","DRDDLURUUL"),
                        comm("LLULDRRURD","RDRRULDLLU"),
                        comm("DLLURDRRUL","DRRURDLLUL"),
                        comm("RULUURDLDD","RDDLDRUULU"),
                        comm("URURDLULDD","UULDLURDRD"),
                        comm("LULURDLDRR","LDLDRULURR"),
                        comm("URUULDRDDL","RDLDDRULUU"),
                        comm("LURUULDRDD","LLDRDLURUR"),
                        comm("DLDDRULUUR","LUURDLDDRU"),
                        comm("URRDRULLDL","LDRULDLURR"),
                        comm("ULUURDLDDR","DRULDRDLUU"),
                        comm("UULDLURDRD","UURDRULDLD"),
                        comm("LULLDRURRD","RDRRULDLLU"),
                        comm("LDLLURDRRU","URRDRULLDL"),
                        comm("UURDLDRULD","RDDLDRUULU")
                ));
            return new LoopoverNRGSetup(N,algs,new int[] {1,0,3,2});
        }
        return null;
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
        int[] P={1,0,3,2};
        List<String> comms=Arrays.asList(
                "DDLDRULURULURDLDDRDLURULURULDR",
                "DDLDLURDRUURDLDLUULDRDRUURULDLUR",
                "DDLDRULURURULDRDLLDRDLURURULURDL",
                "DLDLDRURULULDRDLURDRULDRDLULURUR",
                comm("UULDRDLURD","LDLDRULURR"),
                comm("LDLULDRURR","DRDRULDLUU"),
                comm("LDLDRULURR","RURULDRDLL"),
                comm("RRULURDLDL","DRDLDRULUU"),
                comm("LLURDRULDR","UURDRULDLD"),
                comm("LDRULDLURR","RDLURDRULL"),
                comm("LDRULDLURR","DRDRULDLUU"),
                comm("RRDRULDLUL","DLDLURDRUU"),
                comm("LLDRDLURUR","UULURDLDRD"),
                comm("LLURULDRDR","LLDRDLURUR"),
                comm("UURDLDRULD","DDRULURDLU"),
                comm("RRDLDRULUL","LLURULDRDR"),
                comm("DDLURULDRU","UURDLDRULD"),
                comm("DDRURDLULU","LDRULDLURR"),
                comm("DDLULDRURU","DRDRULDLUU"),
                comm("LURDLULDRR","RDLURDRULL"),
                comm("UULDLURDRD","DRDRULDLUU"),
                comm("UULDRDLURD","DRULDRDLUU"),
                comm("RRDLULDRUL","LDRULDLURR"),
                comm("DRDRULDLUU","DLDLURDRUU")
        );
        System.out.println(LoopoverNRGAlgorithmFinder.primaryAlgs(5,comms).get(0));
        LoopoverNRGSetup[] bfss={
                new LoopoverNRGSetup(5,comms,P),
                new LoopoverNRGSetup(5,LoopoverNRGAlgorithmFinder.primaryAlgs(5,comms).get(0),P)
        };
        for (LoopoverNRGSetup bfs:bfss) verify(bfs);
        for (int code=0; code<bfss[0].sols.length; code++) {
            int[] costs=new int[bfss.length];
            for (int i=0; i<bfss.length; i++) costs[i]=bfss[i].cost(code);
            if (costs[0]!=costs[1]) {
                for (LoopoverNRGSetup bfs:bfss)
                    System.out.println(bfs.sol(code));
                throw new RuntimeException("Mismatch: tuple="+Arrays.toString(bfss[0].decode(code))
                        +" costs="+Arrays.toString(costs));
            }
        }
    }
}
