import java.util.*;
public class LoopoverNRGUpper {
    private static int upper(int N, LoopoverNRGSetupBFS bfs3, LoopoverNRGSetupBFS bfs4, List<Integer> toSolve) {
        //solve one/two pcs at a time, in some arbitrary order
        //assume gripped piece is already solved
        int gr=0, gc=0;
        int out=0;
        int T=toSolve.size();
        if (bfs4==null)
            for (int ti=0; ti<T-2; ti++) {
                int t=toSolve.get(ti);
                int worst=0;
                for (int ci=ti+1; ci<T; ci++) {
                    int cur=toSolve.get(ci);
                    //assume the piece that should be at loc. t is currently at loc. cur
                    int best=Integer.MAX_VALUE;
                    //find the best third piece to use
                    //  so that we can move cur to t using a 3-cycle
                    for (int ri=ti+1; ri<T; ri++)
                        if (ri!=ci)
                            //3-cycle: cur-->t-->third-->cur
                            best=Math.min(best,bfs3.cost(new int[] {cur,t,toSolve.get(ri)},gr,gc));
                    worst=Math.max(worst,best);
                }
                out+=worst;
            }
        else {
            for (int ti=0; ti<T-2; ti+=2)
            if (ti==T-3) {
                int t=toSolve.get(ti);
                int worst=0;
                for (int ci=ti+1; ci<T; ci++) {
                    int cur=toSolve.get(ci);
                    int best=Integer.MAX_VALUE;
                    for (int ri=ti+1; ri<T; ri++)
                    if (ri!=ci)
                        best=Math.min(best,bfs3.cost(new int[] {cur,t,toSolve.get(ri)},gr,gc));
                    worst=Math.max(worst,best);
                }
                out+=worst;
            }
            else {
                int ta=toSolve.get(ti), tb=toSolve.get(ti+1);
                int worst=0;
                //when neither a nor b @ ta or tb
                for (int ai=ti+2; ai<T; ai++)
                for (int bi=ti+2; bi<T; bi++)
                if (ai!=bi) {
                    int a=toSolve.get(ai), b=toSolve.get(bi);
                    worst=Math.max(worst,bfs4.cost(new int[] {a,ta,b,tb},gr,gc)); //a-->ta, b-->tb
                }
                //when a @ tb and b @ ta
                {
                    int best=Integer.MAX_VALUE;
                    for (int ai=ti+2; ai<T; ai++)
                    for (int bi=ti+2; bi<T; bi++)
                    if (ai!=bi) {
                        int a=toSolve.get(ai), b=toSolve.get(bi);
                        best=Math.min(best,bfs4.cost(new int[] {a,b,ta,tb},gr,gc)); //a<-->b, ta<-->tb
                    }
                    worst=Math.max(worst,best);
                }
                //when a @ tb xor b @ ta
                for (int ri=ti+2; ri<T; ri++) {
                    int r=toSolve.get(ri);
                    worst=Math.max(worst,
                            Math.max(
                                    bfs3.cost(new int[] {r,ta,tb},gr,gc),
                                    bfs3.cost(new int[] {r,tb,ta},gr,gc)
                            )
                    );
                }
                //when a @ ta xor b @ tb
                if (ti==T-4) {
                    //when a @ ta
                    for (int xi=ti+2; xi<T; xi++) {
                        int x=toSolve.get(xi); //b @ x
                        int best=Integer.MAX_VALUE;
                        for (int yi=ti+2; yi<T; yi++)
                        if (xi!=yi)
                            best=Math.min(best,bfs3.cost(new int[] {x,tb,toSolve.get(yi)},gr,gc));
                        worst=Math.max(worst,best);
                    }
                    //when b @ tb
                    for (int xi=ti+2; xi<T; xi++) {
                        int x=toSolve.get(xi); //a @ x
                        int best=Integer.MAX_VALUE;
                        for (int yi=ti+2; yi<T; yi++)
                            if (xi!=yi)
                                best=Math.min(best,bfs3.cost(new int[] {x,ta,toSolve.get(yi)},gr,gc));
                        worst=Math.max(worst,best);
                    }
                }
                else {
                    //when a @ ta
                    for (int xi=ti+2; xi<T; xi++) {
                        int x=toSolve.get(xi); //b @ x
                        int best=Integer.MAX_VALUE;
                        for (int yi=ti+2; yi<T; yi++)
                        if (xi!=yi)
                        for (int zi=ti+2; zi<T; zi++)
                        if (zi!=xi&&zi!=yi)
                            best=Math.min(best,bfs4.cost(new int[] {x,tb,toSolve.get(yi),toSolve.get(zi)},gr,gc));
                        worst=Math.max(worst,best);
                    }
                    //when b @ tb
                    for (int xi=ti+2; xi<T; xi++) {
                        int x=toSolve.get(xi); //a @ x
                        int best=Integer.MAX_VALUE;
                        for (int yi=ti+2; yi<T; yi++)
                        if (xi!=yi)
                        for (int zi=ti+2; zi<T; zi++)
                        if (zi!=xi&&zi!=yi)
                                best=Math.min(best,bfs4.cost(new int[] {x,ta,toSolve.get(yi),toSolve.get(zi)},gr,gc));
                        worst=Math.max(worst,best);
                    }
                }
                out+=worst;
            }
        }
        return out+2*(N/2);
    }
    public static void main(String[] args) {
        int N=5;
        System.out.println("N="+N);
        LoopoverNRGSetupBFS bfs3=LoopoverNRGSetupBFS.cyc3bfs(N),
                bfs4=LoopoverNRGSetupBFS.swap22bfs(N);
        //assume gripped piece is pc 0
        List<Integer> toSolve=new ArrayList<>();
        for (int i=1; i<N*N; i++) toSolve.add(i);
        int T=toSolve.size();
        //anneal on list of pieces toSolve
        long NREPS=10000;
        double TEMP0=5;
        int scr=upper(N,bfs3,bfs4,toSolve);
        SplittableRandom rnd=new SplittableRandom(1);
        for (long reps=0, accn=0;; reps++) {
            double temp=TEMP0*(1.0-reps/(double)NREPS);
            if (reps%1000==0)
                System.out.printf("%8d%8d%4d %.10f%n",reps,accn,scr,temp);
            if (reps==NREPS) break;
            int i=rnd.nextInt(T), j=rnd.nextInt(T-1); if (j>=i) j++;
            int ti=toSolve.get(i), tj=toSolve.get(j);
            toSolve.set(i,tj);
            toSolve.set(j,ti);
            int nscr=upper(N,bfs3,bfs4,toSolve);
            if (nscr<=scr||rnd.nextDouble()<Math.exp((scr-nscr)/temp)) {
                scr=nscr;
                accn++;
            }
            else {
                toSolve.set(i,ti);
                toSolve.set(j,tj);
            }
        }
        System.out.println(toSolve);
    }
}
