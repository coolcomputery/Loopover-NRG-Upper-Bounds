import java.util.*;
public class LoopoverNRGUpper {
    private int N, gr, gc;
    private LoopoverNRGSetup bfs3, bfs4;
    public LoopoverNRGUpper(int N, int gr, int gc) {
        this.N=N; this.gr=gr; this.gc=gc;
        bfs3=LoopoverNRGSetup.cyc3bfs(N);
        bfs4=LoopoverNRGSetup.swap22bfs(N);
    }
    private int upper(List<Integer> toSolve) {
        //solve one/two pcs at a time, in some arbitrary order
        //assume gripped piece is already solved
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
                            //3-cycle: cur-->t-->toSolve.get(ri)-->cur
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
                    worst=Math.max(worst,bfs4.cost(new int[] {a,ta,b,tb},gr,gc));
                }
                //when a @ tb and b @ ta
                {
                    int best=Integer.MAX_VALUE;
                    for (int ai=ti+2; ai<T; ai++)
                    for (int bi=ti+2; bi<T; bi++)
                    if (ai!=bi) {
                        int a=toSolve.get(ai), b=toSolve.get(bi);
                        best=Math.min(best,bfs4.cost(new int[] {a,b,ta,tb},gr,gc));
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
        return out;
    }
    private int[][] SAupper(List<Integer> pcsToSolve, long NREPS, double TEMP0) {
        long st=System.currentTimeMillis();
        System.out.println("N="+N);
        //assume gripped piece is pc 0
        SplittableRandom rnd=new SplittableRandom(1);
        List<Integer> toSolve=new ArrayList<>(pcsToSolve);
        int T=toSolve.size();
        System.out.println("T="+T);
        //shuffle
        for (int i=T-1; i>0; i--) {
            int j=rnd.nextInt(i+1), tmp=toSolve.get(i);
            toSolve.set(i,toSolve.get(j));
            toSolve.set(j,tmp);
        }
        //anneal on list of pieces to solve
        //do fewer SA iterations for larger N because iterations become very slow as N increases
        System.out.println("NREPS="+NREPS);
        int scr=upper(toSolve);
        int bscr=scr;
        List<Integer> bestTS=new ArrayList<>(toSolve);
        String form="%8s%8s%6s %s%n";
        System.out.printf(form,"REPS","ACCN","GN","temp");
        for (long reps=0, accn=0;; reps++) {
            double temp=TEMP0*(1.0-reps/(double)NREPS);
            if (reps==NREPS||reps%(NREPS/10)==0)
                System.out.printf(form,reps,accn,scr,temp);
            if (reps==NREPS) break;
            int i=rnd.nextInt(T), j=rnd.nextInt(T-1); if (j>=i) j++;
            int ti=toSolve.get(i), tj=toSolve.get(j);
            toSolve.set(i,tj);
            toSolve.set(j,ti);
            int nscr=upper(toSolve);
            if (nscr<=scr||rnd.nextDouble()<Math.exp((scr-nscr)/temp)) {
                scr=nscr;
                if (scr<bscr) {
                    bscr=scr;
                    bestTS=new ArrayList<>(toSolve);
                }
                accn++;
            }
            else {
                toSolve.set(i,ti);
                toSolve.set(j,tj);
            }
        }
        System.out.println("bestScr="+bscr+", best list of pieces to solve="+bestTS);
        System.out.println("SA time="+(System.currentTimeMillis()-st));
        int[] tmp=new int[bestTS.size()];
        for (int i=0; i<tmp.length; i++)
            tmp[i]=bestTS.get(i);
        int s3=bfs3.diam, s4=bfs4==null?2*s3:bfs4.diam;
        int simplescr=Math.max(s3+(T-3)/2*Math.min(s3,s4),s4+(T-4)/2*Math.min(s3,s4));
        System.out.println("simplescr="+simplescr);
        return new int[][] {{Math.min(bscr,simplescr)},tmp};
    }
    private static boolean[] mask(String s) {
        boolean[] out=new boolean[s.length()];
        for (int i=0; i<s.length(); i++)
            out[i]=s.charAt(i)=='1';
        return out;
    }
    private int blockUpper(String[] Rfrees, String[] Cfrees, long NREPS, double TEMP0) {
        //must leave 2 rows and 2 columns free at the end
        int T=Rfrees.length-1;
        LoopoverNRGBFS[] trees=new LoopoverNRGBFS[T];
        for (int si=0; si<T; si++)
            trees[si]=new LoopoverNRGBFS(N,N,gr,gc,Rfrees[si],Cfrees[si],Rfrees[si+1],Cfrees[si+1]);
        boolean[] fRfree=mask(Rfrees[T]), fCfree=mask(Cfrees[T]);
        List<Integer> toSolve=new ArrayList<>();
        for (int i=0; i<N*N; i++)
            if ((i/N!=gr||i%N!=gc)&&(fRfree[i/N]||fCfree[i%N]))
                toSolve.add(i);
        int[][] ret=SAupper(toSolve,NREPS,TEMP0);
        int out=0;
        System.out.print("GN<=");
        for (int t=0; t<=T; t++) {
            int v=t==0?(trees[t].D-1):t<T?(trees[t].Dreturning-1):ret[0][0];
            System.out.print((t==0?"":"+")+v);
            out+=v;
        }
        System.out.println("="+out);
        return out;
    }
    public static void main(String[] args) {
        new LoopoverNRGUpper(4,0,0).blockUpper(
                new String[] {"1111","1100"},
                new String[] {"1111","1100"},
                1000000,1
        );
        new LoopoverNRGUpper(5,0,0).blockUpper( //0x0->2x2->3x3
                new String[] {"11111","11001","11000"},
                new String[] {"11111","11001","11000"},
                100000,1
        );
        new LoopoverNRGUpper(6,0,0).blockUpper( //0x0->2x2->2x4->3x4->4x4
                new String[] {"111111","110011","110011","110001","110000"},
                new String[] {"111111","110011","110000","110000","110000"},
                10000,1
        );
    }
}
