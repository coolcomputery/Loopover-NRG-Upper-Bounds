public class LoopoverNRGUpper {
    public static void main(String[] args) {
        int Nlo=4, Nhi=10;
        int[] S3=new int[Nhi-Nlo+1], S4=new int[Nhi-Nlo+1];
        for (int N=Nlo; N<=Nhi; N++) {
            System.out.println("N="+N);
            LoopoverNRGSetupBFS bfs3=LoopoverNRGSetupBFS.cyc3bfs(N);
            if (bfs3==null) S3[N-Nlo]=-1;
            else S3[N-Nlo]=bfs3.diam;
            LoopoverNRGSetupBFS bfs4=LoopoverNRGSetupBFS.swap22bfs(N);
            if (bfs4==null) S4[N-Nlo]=2*S3[N-Nlo];
            else S4[N-Nlo]=bfs4.diam;
        }
        String form="%3s%4s%4s%n";
        System.out.printf(form,"N","S3","S4");
        for (int N=Nlo; N<=Nhi; N++)
            System.out.printf(form,N,S3[N-Nlo],S4[N-Nlo]);
        String form2="%3s%30s%n";
        System.out.printf(form2,"N","God's number upper bound");
        for (int N=Nlo; N<=Nhi; N++) {
            int s3=S3[N-Nlo], s4=S4[N-Nlo];
            int[] Wrow=new int[N*N];
            Wrow[3]=s3; Wrow[4]=s4;
            for (int K=5; K<=N*N-1; K++) {
                Wrow[K]=Wrow[K-2]+Math.min(s3,s4);
                if (K%4==0 && Wrow[K]<K/4*s4)
                    throw new RuntimeException();
            }
            int worst=0;
            for (int K=3; K<=N*N-1; K++) worst=Math.max(worst,Wrow[K]);
            worst+=2*(int)Math.floor(N/2);
            System.out.printf(form2,N,worst);
        }
    }
}
