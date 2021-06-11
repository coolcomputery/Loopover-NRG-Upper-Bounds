import java.util.*;
public class LoopoverNRGCommutatorSetupFinder {
    private static final char[] dirNames={'D','R','U','L'};
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
    private static String comm(String A, String B) {
        return A+B+inv(A)+inv(B);
    }
    private static char transf(char mv, int type) {
        if (type==0) return mv=='L'?'R':mv=='R'?'L':mv; //reflect left-right
        else if (type==1) return mv=='U'?'D':mv=='D'?'U':mv; //reflect top-down
        else if (type==2) return mv=='D'?'R':mv=='R'?'D':mv=='U'?'L':'U';
        else throw new RuntimeException("invalid transformation type: "+type);
    }
    private static String transf(String mvs, int type) {
        StringBuilder out=new StringBuilder();
        for (int i=0; i<mvs.length(); i++)
            out.append(transf(mvs.charAt(i),type));
        return out.toString();
    }
    private static int[] transf(int[] loc, int type) {
        if (type==0) return new int[] {loc[0],-loc[1]};
        else if (type==1) return new int[] {-loc[0],loc[1]};
        else if (type==2) return new int[] {loc[1],loc[0]};
        else throw new RuntimeException("invalid transformation type: "+type);
    }
    private static class SetupFinder {
        private int N, V, K;
        private int[] perm;
        private int[] par, root, cost;
        private String[] tcycs;
        private int diam;
        int code(int[] vs) {
            int out=0;
            for (int i=0, pow=1; i<K; i++, pow*=V)
                out+=vs[i]*pow;
            return out;
        }
        int[] decode(int code) {
            int[] out=new int[K];
            for (int i=0; i<K; i++, code/=V)
                out[i]=code%V;
            return out;
        }
        SetupFinder(int N, List<int[][]> ptsets, List<String> algs, int[] perm) {
            if (ptsets.size()!=algs.size()) throw new RuntimeException();
            int[][][] a0=new int[ptsets.size()][][];
            String[] a1=new String[algs.size()];
            for (int i=0; i<ptsets.size(); i++) {
                a0[i]=ptsets.get(i);
                a1[i]=algs.get(i);
            }
            init(N,a0,a1,perm);
        }
        SetupFinder(int N, int[][][] ptsets, String[] algs, int[] perm) {
            init(N,ptsets,algs,perm);
        }
        private void init(int N, int[][][] ptsets, String[] algs, int[] perm) {
            long sttime=System.currentTimeMillis();
            this.N=N;
            this.perm=perm.clone(); //perm[i] is s.t. location i move to location perm[i]
            K=perm.length;
            //runs in O(N^(2K)) time
            //the graph of reachable states of pieces + gripped piece is translation-symmetric
            //--> if all pieces, including the gripped piece, are translated by the same displacement,
            //  that does not affect the shortest setup move sequence to a valid commutator position
            //--> therefore we only need to care about the offset of each permuted piece relative to the gripped piece
            V=N*N;
            int AMT=1; for (int rep=0; rep<K; rep++) AMT*=V;
            par=new int[AMT];
            cost=new int[AMT];
            Arrays.fill(cost,-1);
            tcycs=new String[8*ptsets.length];
            root=new int[AMT];
            class AList {
                int[] A;
                int sz;
                AList(int n) {
                    A=new int[n];
                    sz=n;
                }
                void resize(int n) {
                    int[] tmp=new int[n];
                    System.arraycopy(A,0,tmp,0,Math.min(A.length,n));
                    A=tmp;
                    sz=Math.min(sz,n);
                }
                int at(int i) {
                    if (i>=sz) throw new RuntimeException();
                    return A[i];
                }
                void add(int v) {
                    if (sz>=A.length)
                        resize(Math.max(1,A.length*2));
                    A[sz++]=v;
                }
            }
            AList[] vertsAtCost;
            {
                int maxcost=0; for (String alg:algs) maxcost=Math.max(maxcost,alg.length());
                vertsAtCost=new AList[2*AMT+maxcost+1];
                //for (int i=0; i<vertsAtCost.length; i++) vertsAtCost[i]=new AList(0);
            }
            for (int ai=0; ai<ptsets.length; ai++) {
                int[][] pts=ptsets[ai];
                String alg=algs[ai];
                int c=alg.length();
                if (vertsAtCost[c]==null) vertsAtCost[c]=new AList(8);
                else vertsAtCost[c].resize(vertsAtCost[c].sz+8);
                for (int b=0; b<8; b++) {
                    //add the 8 dihedral symmetries of the commutators
                    String tcyc=alg;
                    for (int t=0; t<3; t++)
                        if ((b&(1<<t))!=0)
                            tcyc=transf(tcyc,t);
                    tcycs[8*ai+b]=tcyc;
                    int[] tlocs=new int[K];
                    for (int i=0; i<K; i++) {
                        int[] tpt=pts[i];
                        for (int t=0; t<3; t++)
                            if ((b&(1<<t))!=0)
                                tpt=transf(tpt,t);
                        tlocs[i]=mod(tpt[0],N)*N+mod(tpt[1],N);
                    }
                    int st=code(tlocs);
                    par[st]=root[st]=-1-(8*ai+b);
                    cost[st]=c;
                    vertsAtCost[c].add(st);
                }
            }
            diam=0;
            for (int co=0; co<vertsAtCost.length; co++) //optimized Dijkstra's
            if (vertsAtCost[co]!=null) {
                diam=Math.max(diam,co);
                for (int fi=0; fi<vertsAtCost[co].sz; fi++) {
                    int f=vertsAtCost[co].at(fi);
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
                        int code=code(nlocs);
                        if (cost[code]==-1) {
                            par[code]=f*4+d;
                            root[code]=root[f];
                            cost[code]=co+2;
                            if (vertsAtCost[cost[code]]==null) vertsAtCost[cost[code]]=new AList(1);
                            vertsAtCost[cost[code]].add(code);
                        }
                    }
                }
            }
            System.out.printf("K=%d,diameter=%d,BFS time=%d%n",K,diam,(System.currentTimeMillis()-sttime));
        }
        //L[] is an array of locations on the board
        private String[] actionsol(int[] L, int lr, int lc) {
            if (L.length!=K) throw new RuntimeException("Mismatch in number of pieces: "+L.length+"!="+K);
            StringBuilder out=new StringBuilder();
            int[] nL=new int[K];
            for (int i=0; i<K; i++) nL[i]=mod(L[i]/N-lr,N)*N+mod(L[i]%N-lc,N);
            int v=code(nL);
            for (; par[v]>-1; v=par[v]/4)
                out.append(dirNames[par[v]%4]);
            if (par[v]!=root[v]) throw new RuntimeException();
            return new String[] {out.toString(),tcycs[-1-par[v]]};
        }
    }
    private static SetupFinder cyc3bfs(int N) {
        //3-cycle: pt 0 --> pt 1 --> pt 2 --> pt0
        List<int[][]> ptsets=new ArrayList<>();
        List<String> algs=new ArrayList<>();
        if (N==5) {
            ptsets.add(new int[][] {{-2,-2},{-2,2},{-2,-1}});
            algs.add(comm("RURULDRDLL","DDLDRULURU"));
        }
        else if (N>5) {
            ptsets.add(new int[][] {{-2,2},{2,-1},{0,1}});
            algs.add(comm("LURDLULDRR","RRDRULDLUL"));
        }
        //both commutators above discovered by orucsoraihc#4626 on https://discord.com/channels/526598754791587850/532371042367438848/578774719302467595
        if (N%2==0) {
            StringBuilder rd=new StringBuilder(), lu=new StringBuilder();
            for (int r=0; r<N/2; r++) {
                rd.append('R'); lu.append('L');
            }
            for (int r=0; r<N/2; r++) {
                rd.append('D'); lu.append('U');
            }
            StringBuilder alg=new StringBuilder();
            alg.append(rd).append(lu);
            alg.append(alg);
            ptsets.add(new int[][] {{0,N/2},{N/2,N/2},{N/2,0}});
            algs.add(alg.toString());
            //don't know who discovered this other commutator
        }
        return ptsets.size()>0?
                new SetupFinder(N,ptsets,algs,new int[] {1,2,0}):
                null;
    }
    private static SetupFinder swap22bfs(int N) {
        //double swapper: pt 0 <--> pt 1, pt 2 <--> pt 3
        if (N>=5) {
            String a8="URULDRDL", b8="DLDRULUR";
            return new SetupFinder(N,
                            new int[][][] {
                                    {{0,-1},{-1,-1},{0,1},{1,1}}, //discovered by orucsoraihc#4626
                                    {{1,-2},{-1,-1},{0,1},{0,2}}, //discovered by me
                                    {{1,-2},{0,-1},{0,1},{-1,2}}, //discovered by me
                            },
                            new String[] {comm(a8,b8),comm(a8,inv(b8)),comm(inv(a8),inv(b8))},
                            new int[] {1,0,3,2}
                    );
        }
        return null;
    }
    private static class Board {
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
    private static void verify(int N, SetupFinder bfs) {
        long st=System.currentTimeMillis();
        int K=bfs.K;
        int[] perm=bfs.perm;
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
                String[] info=bfs.actionsol(permd_locs,lr,lc);
                String sol=info[0]+info[1]+inv(info[0]);
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
                    System.out.println("info="+Arrays.toString(info));
                    System.out.println("sol="+sol);
                    System.out.println("perm="+Arrays.toString(perm)
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
        int Nlo=4, Nhi=10;
        int[] S3=new int[Nhi-Nlo+1], S4=new int[Nhi-Nlo+1];
        for (int N=Nlo; N<=Nhi; N++) {
            System.out.println("N="+N);
            SetupFinder bfs3=cyc3bfs(N);
            if (bfs3==null) S3[N-Nlo]=-1;
            else {
                //verify(N,bfs3);
                S3[N-Nlo]=bfs3.diam;
            }
            SetupFinder bfs4=swap22bfs(N);
            if (bfs4==null) S4[N-Nlo]=-1;
            else {
                //verify(N,bfs4);
                S4[N-Nlo]=bfs4.diam;
            }
        }
        String form="%3s%4s%4s%n";
        System.out.printf(form,"N","S3","S4");
        for (int N=Nlo; N<=Nhi; N++)
            System.out.printf(form,N,S3[N-Nlo],S4[N-Nlo]);
    }
}
