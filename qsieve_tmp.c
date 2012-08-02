#include <gmp.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h> 

#define SSIZE 100000    /* Maximum sieve size            */
#define PSIZE 200000
#define TRUE 1
#define FALSE 0

typedef struct
{
    int *PRIMES;
    int NTRY;
} pinfo;

mpz_t N,TA,D,R,V,P,X,Y,DG,IG,A,B,TB,TC,TD;
mpz_t *x,*y,*z,*w;
unsigned int **EE,**G;
int *epr,*r1,*r2,*rp,*b,*pr,*e,*hash;
unsigned char *logp,*sieve;
int mm,mlf,jj,nbts,nlp,lp,hmod,hmod2;
char partial;
pinfo *qsieve;
int qsieve_powmod(int x, int n, int m);
int qsieve_getsize(mpz_t x);
void qsieve_muladddiv(mpz_t x, mpz_t y, mpz_t z, mpz_t w, mpz_t q, mpz_t r);
int qsieve_outnum(mpz_t x, FILE *fout);
void qsieve_divide(mpz_t x, mpz_t y, mpz_t z);
int qsieve_compare(mpz_t x, mpz_t y);
int qsieve_getinvers(int x, int y);
int qsieve_sqrmp(int x, int m);
void qsieve_gprime(int maxp);

pinfo *gmpinit(int nd, int nb)
{
    pinfo *t;
    t = (pinfo *)malloc(sizeof(pinfo));
    t -> NTRY = 20;
    return t;
}

int qsieve_powmod(int x, int n, int m)
{
    long long ans = 1;
    long long t = x;
    while(n > 0)
    {
        if(n & 1) ans = (ans * t) % m;
        t = (t * t) % m;
        n >>= 1;
    }
    return (int)ans;
}

int qsieve_getsize(mpz_t x)
{
    int t;
    t = mpz_get_si(x);
    if(mpz_fits_slong_p(x)) return t;
    return (t<0 ? -0x7FFFFFFF : +0x7FFFFFFF);
}

void qsieve_muladddiv(mpz_t x, mpz_t y, mpz_t z, mpz_t w, mpz_t q, mpz_t r)
{
    mpz_mul(TB, x, y);
    if(x != z && y != z) mpz_add(TB, TB, z);
    if(q != r) mpz_tdiv_r(r, TB, w);
    if(w != q) qsieve_divide(TB, w, q);
}

int qsieve_outnum(mpz_t x, FILE *fout)
{
    int t = mpz_out_str(fout, 10, x);
    puts("");
    fflush(stdout);
    return t;
}


void qsieve_divide(mpz_t x, mpz_t y, mpz_t z)
{
    if(x != z) mpz_tdiv_r(TD, x, y);
    if(y != z) mpz_tdiv_q(TC, x, y);
    if(x != z) if(TD!=x) mpz_set(x, TD);
    if(y != z) if(TC!=z) mpz_set(z, TC);
}

int qsieve_compare(mpz_t x, mpz_t y)
{
    int t = mpz_cmp(x, y);
    if(t > 0) return 1;
    if(t < 0) return -1;
    return 0;
}

int qsieve_getinvers(int x, int y)
{
    if(x == 0) return y;
    mpz_set_si(TB, x);
    mpz_set_si(TC, y);
    mpz_invert(TD, TB, TC);
    return qsieve_getsize(TD);
}

int qsieve_sqrmp(int x, int m)
{
    long long i;
    for(i=0; i<m; i++) if(i*i%m == x) return (int) i;
    return 0;
}

void qsieve_gprime(int maxp)
{
    char *vis;
    int i, j, k = 0;
    static flag = 0;
    if(flag) return;
    flag = 1;
    vis = (char *)malloc(PSIZE);
    memset(vis, 0, PSIZE);
    for(i=2; i<PSIZE; i++)
    {
        if(vis[i] == 0)
        {
            k ++;
            if(i<40000) for(j=i*i; j<PSIZE; j+=i) vis[j] = 1;
        }
    }
    qsieve->PRIMES = (int *)malloc(k*sizeof(int));
    k = 0;
    for(i=2; i<PSIZE; i++)
    {
        if(vis[i] == 0)
        {
            qsieve->PRIMES[k] = i;
            k ++;
        }
    }
    free(vis);
    if(qsieve->PRIMES[k-1] < maxp)
    {
        printf("QSIEVE ERROR: NUMBER IS TOO LARGE\n");
        fflush(stdout);
        exit(0);
    }
}

void* qsieve_alloc(int len, int qsieve_getsize)
{
    void *p = malloc(len * qsieve_getsize);
    memset(p, 0, len*qsieve_getsize);
    return p;
}

int qsieve_extgcd(mpz_t x, mpz_t y, mpz_t xd, mpz_t yd, mpz_t z)
{
    mpz_gcdext(TD, TB, TC, x, y);
    while(qsieve_getsize(TB) < 0)
    {
        mpz_add(TB, TB, y);
        mpz_sub(TC, TC, x);
    }
    if(z != xd && z != yd) if(TD!=z) mpz_set(z, TD);
    if(xd != yd)
    {
        if(TB!=xd) mpz_set(xd, TB);
        if(TC!=yd) mpz_set(yd, TC);
    }
    else
    {
        if(TB!=xd) mpz_set(xd, TB);
    }
    return qsieve_getsize(TD);
}

int knuth(int mm,int *epr,mpz_t N,mpz_t D)
{
    double dp, fks, top = -10.0;
    char found = FALSE;
    int i, j, bk=0, nk=0, kk, r, p;
    static int K[]={0,1,2,3,5,6,7,10,11,13,14,15,17,0};
    epr[0]=1;
    epr[1]=2;
    do
    {
        kk=K[++nk];
        if(kk==0)
        {
            kk=K[bk];
            found=TRUE;
        }
        mpz_mul_si(D, N, kk);
        fks=log(2.0)/2.0;
        r=mpz_tdiv_r_ui(TB, D, 8);
        if(r==1) fks*=4.0;
        if(r==5) fks*=2.0;
        fks-=log((double)kk)/2.0;
        i=0;
        j=1;
        while(j<mm)
        {
            p=qsieve->PRIMES[++i];
            r=mpz_tdiv_r_ui(TB, D, p);
            if(qsieve_powmod(r,(p-1)/2,p)<=1)
            {
                epr[++j]=p;
                dp=(double)p;
                if(kk%p==0) fks+=log(dp)/dp;
                else fks+=2*log(dp)/(dp-1.0);
            }
        }
        if(fks>top)
        {
            top=fks;
            bk=nk;
        }
    } while(!found);
    return kk;
}

char factored(long lptr,mpz_t T)
{
    char facted = FALSE;
    int i,j,r,st;
    partial = FALSE;
    for(j=1;j<=mm;j++)
    {
        r=(int)(lptr%epr[j]);
        if(r<0) r+=epr[j];
        if(r!=r1[j] && r!=r2[j]) continue;
        while(mpz_tdiv_q_ui(X, T, epr[j])==0)
        {
            e[j]++;
            if(X!=T) mpz_set(T, X);
        }
        st=qsieve_getsize(T);
        if(st==1)
        {
           facted=TRUE;
           break;
        }
        if(qsieve_getsize(X)<=epr[j])
        {
            if(st>=0x7FFFFFFF || (st/epr[mm])>(1+mlf/50)) break;
            if(st<=epr[mm])
                for(i=j;i<=mm;i++)
                if(st==epr[i])
                {
                    e[i]++;
                    facted=TRUE;
                    break;
                }
            if(facted) break;
            lp=st;
            partial=TRUE;
            facted=TRUE;
            break;
        }
    }
    return facted;
}

char gotcha(void)
{
    int r,j,i,k,n,rb,had,hp;
    unsigned int t;
    char found;
    found=TRUE;
    if(partial)
    {
        had=lp%hmod;
        while(1)
        {
            hp=hash[had];
            if(hp<0)
            {
                found=FALSE;
                break;
            }
            if(pr[hp]==lp) break;
            had=(had+(hmod2-lp%hmod2))%hmod;
        }
        if(!found && nlp>=mlf) return FALSE;
    }
    if(P!=X) mpz_set(X, P);
    mpz_set_si(Y, 1);
    for(k=1;k<=mm;k++)
    {
        if(e[k]<2) continue;
        r=e[k]/2;
        e[k]%=2;
        mpz_ui_pow_ui(TA, epr[k], r);
        mpz_mul(Y, TA, Y);
    }

    if(partial)
    {
        if(!found)
        {
            hash[had]=nlp;
            pr[nlp]=lp;
            if(X!=z[nlp]) mpz_set(z[nlp], X);
            if(Y!=w[nlp]) mpz_set(w[nlp], Y);
            for(n=0,rb=0,j=0;j<=mm;j++)
            {
                G[nlp][n]|=((e[j]&1)<<rb);
                if(++rb==nbts) n++,rb=0;
            }
            nlp++;
        }
        if(found)
        {
            printf("\b\b\b\b\b\b*");
            fflush(stdout);
            qsieve_muladddiv(X,z[hp],X,N,N,X);
            qsieve_muladddiv(Y,w[hp],Y,N,N,Y);
            for(n=0,rb=0,j=0;j<=mm;j++)
            {
                t=(G[hp][n]>>rb);
                e[j]+=(t&1);
                if(e[j]==2)
                {
                    mpz_mul_si(Y, Y, epr[j]);
                    qsieve_divide(Y,N,N);
                    e[j]=0;
                }
                if(++rb==nbts) n++,rb=0;
            }
            mpz_mul_si(Y, Y, lp);
            qsieve_divide(Y,N,N);
        }
    }
    else
    {
        printf("\b\b\b\b\b\b ");
        fflush(stdout);
    }
    if(found)
    {
        for(k=mm;k>=0;k--)
        {
            if(e[k]%2==0) continue;
            if(b[k]<0)
            {
                found=FALSE;
                break;
            }
            i=b[k];
            qsieve_muladddiv(X,x[i],X,N,N,X);
            qsieve_muladddiv(Y,y[i],Y,N,N,Y);
            for(n=0,rb=0,j=0;j<=mm;j++)
            {
                t=(EE[i][n]>>rb);
                e[j]+=(t&1);
                if(++rb==nbts) n++,rb=0;
            }
        }
        for(j=0;j<=mm;j++)
        {
            if(e[j]<2) continue;
            mpz_set_si(TA, epr[j]);
            (mpz_set_si(TB, e[j]/2),mpz_powm_sec(TA, TA, TB, N));
            qsieve_muladddiv(Y,TA,Y,N,N,Y);
        }
        if(!found)
        {
            b[k]=jj;
            if(X!=x[jj]) mpz_set(x[jj], X);
            if(Y!=y[jj]) mpz_set(y[jj], Y);
            for(n=0,rb=0,j=0;j<=mm;j++)
            {
                EE[jj][n]|=((e[j]&1)<<rb);
                if(++rb==nbts) n++,rb=0;
            }
            jj++;
            printf("%5d",jj);
        }
    }

    if(found)
    {
        printf("\ntrying...\n");
        mpz_add(TA, X, Y);
        if(qsieve_compare(X,Y)==0 || qsieve_compare(TA,N)==0) found=FALSE;
        if(!found) printf("working... %5d",jj);
    }
    return found;
}

int initv(void)
{
    int i,d,pak,k,maxp;
    double dp;

    mpz_init(N);
    mpz_init(TA);
    mpz_init(D);
    mpz_init(R);
    mpz_init(V);
    mpz_init(P);
    mpz_init(X);
    mpz_init(Y);
    mpz_init(DG);
    mpz_init(IG);
    mpz_init(A);
    mpz_init(B);
    mpz_init(TB);
    mpz_init(TC);
    mpz_init(TD);

    nbts=8*sizeof(int);

    printf("input number to be factored N= \n");
    d=mpz_inp_str(N, stdin, 10);
    if((mpz_probab_prime_p(N, qsieve->NTRY) ? TRUE : FALSE))
    {
        printf("this number is prime!\n");
        return (-1);
    }

    if(d<8) mm=d;
    else mm=25;
    if(d>20) mm=(d*d*d*d)/4096;

    dp=(double)2*(double)(mm+100);
    maxp=(int)(dp*(log(dp*log(dp))));
    qsieve_gprime(maxp);

    epr=(int *)qsieve_alloc(mm+1,sizeof(int));

    k=knuth(mm,epr,N,D);

    if(mpz_root(R, D, 2))
    {
        printf("%dN is a perfect square!\n",k);
        printf("factors are\n");
        if((mpz_probab_prime_p(R, qsieve->NTRY) ? TRUE : FALSE)) printf("prime factor     ");
        else printf("composite factor ");
        qsieve_outnum(R,stdout);
        qsieve_divide(N,R,N);
        if((mpz_probab_prime_p(N, qsieve->NTRY) ? TRUE : FALSE)) printf("prime factor     ");
        else printf("composite factor ");
        qsieve_outnum(N,stdout);
        return (-1);
    }

    printf("using multiplier k= %d\n",k);
    printf("and %d small primes as factor base\n",mm);
    qsieve_gprime(0);

    mlf=2*mm;

    r1=(int *)qsieve_alloc((mm+1),sizeof(int));
    r2=(int *)qsieve_alloc((mm+1),sizeof(int));
    rp=(int *)qsieve_alloc((mm+1),sizeof(int));
    b=(int *)qsieve_alloc((mm+1),sizeof(int));
    e=(int *)qsieve_alloc((mm+1),sizeof(int));

    logp=(unsigned char *)qsieve_alloc(mm+1,1);

    pr=(int *)qsieve_alloc((mlf+1),sizeof(int));
    hash=(int *)qsieve_alloc((2*mlf+1),sizeof(int));

    sieve=(unsigned char *)qsieve_alloc(SSIZE+1,1);

    x=(mpz_t *)qsieve_alloc(mm+1,sizeof(mpz_t));
    y=(mpz_t *)qsieve_alloc(mm+1,sizeof(mpz_t));
    z=(mpz_t *)qsieve_alloc(mlf+1,sizeof(mpz_t));
    w=(mpz_t *)qsieve_alloc(mlf+1,sizeof(mpz_t));

    for(i=0;i<=mm;i++)
    {
        mpz_init(x[i]);
        mpz_init(y[i]);
    }
    for(i=0;i<=mlf;i++)
    {
        mpz_init(z[i]);
        mpz_init(w[i]);
    }

    EE=(unsigned int **)qsieve_alloc(mm+1,sizeof(unsigned int *));
    G=(unsigned int **)qsieve_alloc(mlf+1,sizeof(unsigned int *));

    pak=1+mm/(8*sizeof(int));
    for(i=0;i<=mm;i++)
    {
        b[i]=(-1);
        EE[i]=(unsigned int *)qsieve_alloc(pak,sizeof(int));
    }

    for(i=0;i<=mlf;i++)
        G[i]=(unsigned int *)qsieve_alloc(pak,sizeof(int));
    return 1;
}

int main()
{
    unsigned int i,j,a,*SV;
    unsigned char logpi;
    int k,S,r,s1,s2,s,NS,logm,ptr,threshold,epri;
    long M,la,lptr;

    qsieve=gmpinit(-36,0);

    if(initv()<0) return 0;

    hmod=2*mlf+1;
    mpz_set_si(TA, hmod);
    while(!(mpz_probab_prime_p(TA, qsieve->NTRY) ? TRUE : FALSE)) mpz_sub_ui(TA, TA, 2);
    hmod=qsieve_getsize(TA);
    hmod2=hmod-2;
    for(k=0;k<hmod;k++) hash[k]=(-1);

    M=50*(long)mm;
    NS=(int)(M/SSIZE);
    if(M%SSIZE!=0) NS++;
    M=SSIZE*(long)NS;
    logm=0;
    la=M;
    while((la/=2)>0) logm++;
    rp[0]=logp[0]=0;
    for(k=1;k<=mm;k++)
    {
        r=mpz_tdiv_q_ui(TA, D, epr[k]);
        rp[k]=qsieve_sqrmp(r,epr[k]);
        logp[k]=0;
        r=epr[k];
        while((r/=2)>0) logp[k]++;
    }

    r=mpz_tdiv_q_ui(TA, D, 8);
    if(r==5) logp[1]++;
    if(r==1) logp[1]+=2;

    threshold=logm+mpz_sizeinbase(R, 2)-2*logp[mm];

    jj=0;
    nlp=0;
    mpz_mul_si(DG, D, 2);
    mpz_root(DG, DG, 2);

    mpz_set_si(TA, M);
    qsieve_divide(DG,TA,DG);
    mpz_root(DG, DG, 2);
    if(mpz_tdiv_q_ui(TA, DG, 2)==0) mpz_add_ui(DG, DG, 1);
    if(mpz_tdiv_q_ui(TA, DG, 4)==1) mpz_add_ui(DG, DG, 2);
    printf("working...     0");

    while(1)
    {
        r=qsieve->NTRY;
        qsieve->NTRY=1;
        do
        {
            do {
               mpz_add_ui(DG, DG, 4);
            } while(!(mpz_probab_prime_p(DG, qsieve->NTRY) ? TRUE : FALSE));
            mpz_sub_ui(TA, DG, 1);
            mpz_tdiv_q_ui(TA, TA, 2);
            mpz_powm_sec(TA, D, TA, DG);
        } while(qsieve_getsize(TA)!=1);
        qsieve->NTRY=r;
        mpz_add_ui(TA, DG, 1);
        mpz_tdiv_q_ui(TA, TA, 4);
        mpz_powm_sec(B, D, TA, DG);
        mpz_neg(TA, D);
        qsieve_muladddiv(B,B,TA,DG,TA,TA);
        mpz_neg(TA, TA);

        mpz_mul_si(A, B, 2);
        qsieve_extgcd(A,DG,A,A,A);
        qsieve_muladddiv(A,TA,TA,DG,DG,A);
        mpz_mul(TA, A, DG);
        mpz_add(B, B, TA);
        mpz_mul(A, DG, DG);
        qsieve_extgcd(DG,D,IG,IG,IG);
        
        r1[0]=r2[0]=0;
        for(k=1;k<=mm;k++)
        {
            s=mpz_tdiv_q_ui(TA, B, epr[k]);
            r=mpz_tdiv_q_ui(TA, A, epr[k]);
            r=qsieve_getinvers(r,epr[k]);

            s1=(epr[k]-s+rp[k]);
            s2=(epr[k]-s+epr[k]-rp[k]);
            if(s1 > s2)
            {
                int t = s1;
                s1 = s2;
                s2 = t;
            }
            r1[k]=((int)((((long long)(s1))*((long long)(r))) % ((long long)(epr[k]))));
            r2[k]=((int)((((long long)(s2))*((long long)(r))) % ((long long)(epr[k]))));
        }
        
        for(ptr=(-NS);ptr<NS;ptr++)
        {
            la=(long)ptr*SSIZE;
            SV=(unsigned int *)sieve;
            for(i=0; i<SSIZE/sizeof(int); i++) *SV++=0;
            for(k=1; k<=mm; k++)
            {
                epri=epr[k];
                logpi=logp[k];
                r=(int)(la%epri);
                s1=(r1[k]-r)%epri;
                if(s1<0) s1+=epri;
                s2=(r2[k]-r)%epri;
                if(s2<0) s2+=epri;

                for(j=s1;j<SSIZE;j+=epri) sieve[j]+=logpi;
                if(s1==s2) continue;
                for(j=s2;j<SSIZE;j+=epri) sieve[j]+=logpi;
            }

            for(a=0;a<SSIZE;a++)
            {
                if(sieve[a]<threshold) continue;
                lptr=la+a;
                mpz_set_si(TA, lptr);
                S=0;
                mpz_mul(TA, A, TA);
                mpz_add(TA, TA, B);
                qsieve_muladddiv(TA,IG,TA,D,D,P);
                if(qsieve_getsize(P)<0) mpz_add(P, P, D);
                qsieve_muladddiv(P,P,P,D,D,V);
                mpz_abs(TA, TA);
                if(qsieve_compare(TA,R)<0) S=1;
                if(S==1) mpz_sub(V, D, V);
                if(V!=TA) mpz_set(TA, V);
                e[0]=S;
                for(k=1;k<=mm;k++) e[k]=0;
                if(!factored(lptr,TA)) continue;
                if(gotcha())
                {
                    (mpz_gcd(P, TA, N),qsieve_getsize(P));
                    printf("factors are\n");
                    if((mpz_probab_prime_p(P, qsieve->NTRY) ? TRUE : FALSE)) printf("prime factor     ");
                    else printf("composite factor ");
                    qsieve_outnum(P,stdout);
                    qsieve_divide(N,P,N);
                    if((mpz_probab_prime_p(N, qsieve->NTRY) ? TRUE : FALSE)) printf("prime factor     ");
                    else printf("composite factor ");
                    qsieve_outnum(N,stdout);
                    return 0;
                }
            }
        }
    }
    return 0;
}
