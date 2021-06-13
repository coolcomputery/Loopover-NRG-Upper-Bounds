import java.util.*;
//brute force BFS all permutations of a NxN NRG board
public class LoopoverNRGBFS {
    private static int mod(int n, int k) {
        return (n%k+k)%k;
    }
    //locs describes a permutation where tile i is at location locs[i]
    private static String code(int[] locs) {
        return Arrays.toString(locs);
    }
    private static String display(int[] locs, int N) {
        int[][] perm=new int[N][N];
        for (int i=0; i<N*N; i++)
            perm[locs[i]/N][locs[i]%N]=i;
        StringBuilder out=new StringBuilder();
        for (int[] r:perm) {
            for (int v:r) out.append((char)('A'+v));
            out.append("\n");
        }
        return out.toString();
    }
    private static void bfs(int N) {
        System.out.println("BFS of "+N+"x"+N+"nrg");
        int[] id=new int[N*N]; for (int i=0; i<N*N; i++) id[i]=i;
        Set<String> seen=new HashSet<>();
        seen.add(code(id));
        int gripped_tile=(N/2)*N+(N/2);
        List<int[]> front=new ArrayList<>();
        List<String> sols=new ArrayList<>();
        front.add(id); sols.add("");
        int diam=0;
        int tot=0;
        for (int depth=0; front.size()>0; depth++) {
            diam=depth;
            tot+=front.size();
            System.out.println(depth+":"+front.size());
            //for (int fi=0; fi<front.size(); fi++) System.out.println(sols.get(fi)+"\n"+display(front.get(fi),N));
            List<int[]> nfront=new ArrayList<>();
            List<String> nsols=new ArrayList<>();
            for (int fi=0; fi<front.size(); fi++) {
                int[] locs=front.get(fi);
                for (int d=0; d<4; d++) {
                    int gr=locs[gripped_tile]/N, gc=locs[gripped_tile]%N;
                    int[] nlocs=locs.clone();
                    for (int i=0; i<N*N; i++) {
                        int r=locs[i]/N, c=locs[i]%N;
                        if (d==0) {
                            if (c==gc)
                                nlocs[i]=mod(r+1,N)*N+c;
                        }
                        else if (d==1) {
                            if (r==gr)
                                nlocs[i]=r*N+mod(c+1,N);
                        }
                        else if (d==2) {
                            if (c==gc)
                                nlocs[i]=mod(r-1,N)*N+c;
                        }
                        else {
                            if (r==gr)
                                nlocs[i]=r*N+mod(c-1,N);
                        }
                    }
                    String ncode=code(nlocs);
                    if (!seen.contains(ncode)) {
                        seen.add(ncode);
                        nfront.add(nlocs);
                        nsols.add(sols.get(fi)+d);
                    }
                }
            }
            front=nfront;
            sols=nsols;
        }
        System.out.println("diam="+diam);
        System.out.println("total perms="+tot);
    }
    public static void main(String[] args) {
        bfs(3);
        bfs(4);
    }
}
