/*
 *   Program to factor big numbers using Pomerance-Silverman-Montgomery  
 *   multiple polynomial quadratic sieve.
 *   See "The Multiple Polynomial Quadratic Sieve", R.D. Silverman,
 *   Math. Comp. Vol. 48, 177, Jan. 1987, pp329-339
 */

#include <gmp.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h> 

#define SSIZE 100000    /* Maximum sieve size            */

#define PSIZE 200000

#define forever while(1)
#define TRUE 1
#define FALSE 0
typedef mpz_t big;
typedef char BOOL;
#define MR_TOOBIG 0x7FFFFFFF
typedef struct
{
    int *PRIMES;
    int NTRY;
} miracl;

static big NN,TT,DD,RR,VV,PP,XX,YY,DG,IG,AA,BB,IIA,IIB,IIC;
static big *x,*y,*z,*w;
static unsigned int **EE,**G;
static int *epr,*r1,*r2,*rp,*b,*pr,*e,*hash;
static unsigned char *logp,*sieve;
static int mm,mlf,jj,nbts,nlp,lp,hmod,hmod2;
static BOOL partial;
static miracl *mip;


void premult(big x, int n, big z);
int subdiv(big x, int n, big z);
int remain(big x, int n);
int spmd(int x, int n, int m);
void copy(big x, big y);
int size(big x);
void convert(int n, big x);
void expint(int a, int n, big x);
void mad(big x, big y, big z, big w, big q, big r);
int cotnum(big x, FILE *fout);
int cinnum(big x, FILE *fin);
void divide(big x, big y, big z);
void add(big x, big y, big z);
int egcd(big x, big y, big z);
BOOL isprime(big x);
void subtract(big x, big y, big z);
int compare(big x, big y);
void absol(big x, big y);
void multiply(big x, big y, big z);
void lgconv(long n, big x);
int invers(int x, int y);
int sqrmp(int x, int m);
void gprime(int maxp);
void incr(big x, int n, big z);
void decr(big x, int n, big z);
BOOL nroot(big x, int n, big w);
void negify(big x, big y);
int logb2(big x);
void powmod(big x, big y, big n, big w);

miracl *mirsys(int nd, int nb)
{
    miracl *t;
    t = (miracl *)malloc(sizeof(miracl));
    t -> NTRY = 10;
    return t;
}

void premult(big x, int n, big z)
{
    mpz_mul_si(z, x, n);
}

int subdiv(big x, int n, big z)
{
    return mpz_tdiv_q_ui(z, x, n);
}

int remain(big x, int n)
{
    return mpz_tdiv_r_ui(IIA, x, n);
}

int spmd(int x, int n, int m)
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

void copy(big x, big y)
{
    //mpz_set(IIA, x);
    //mpz_set(y, IIA);
    mpz_set(y, x);
}

int size(big x)
{
    int t;
    t = mpz_get_si(x);
    if(mpz_fits_slong_p(x)) return t;
    return (t<0 ? -MR_TOOBIG : +MR_TOOBIG);
}

void convert(int n, big x)
{
    mpz_set_si(x, n);
}

void expint(int a, int n, big x)
{
    mpz_ui_pow_ui(x, a, n);
}

void mad(big x, big y, big z, big w, big q, big r)
{
    multiply(x, y, IIA);
    if(x != z && y != z) add(IIA, z, IIA);
        
    if(w != q)
    {
        divide(IIA, w, q);
    }
    if(q != r)
    {
        mpz_tdiv_r(r, IIA, w);
    }
}

int cotnum(big x, FILE *fout)
{
    return mpz_out_str(fout, 10, x);
}

int cinnum(big x, FILE *fin)
{
    return mpz_inp_str(x, fin, 10);
}

void divide(big x, big y, big z)
{
    mpz_tdiv_q(z, x, y);
}

void add(big x, big y, big z)
{
    mpz_add(z, x, y);
}

int egcd(big x, big y, big z)
{
    mpz_gcd(z, x, y);
    return size(z);
}

BOOL isprime(big x)
{
    return mpz_probab_prime_p(x, mip->NTRY);
}

void subtract(big x, big y, big z)
{
    mpz_sub(z, x, y);
}

int compare(big x, big y)
{
    int t;
    t = mpz_cmp(x, y);
    if(t > 0) return 1;
    if(t < 0) return -1;
    return 0;
}

void absol(big x, big y)
{
    mpz_abs(y, x);
}

void multiply(big x, big y, big z)
{
    mpz_mul(z, x, y);
}

void lgconv(long n, big x)
{
    convert(n, x);
}

int invers(int x, int y)
{
    convert(x, IIA);
    convert(y, IIB);
    mpz_invert(IIC, IIA, IIB);
    return size(IIC);
}

int sqrmp(int x, int m)
{
    /*
    convert(x, IIA);
    convert(m, IIB);
    mpz_sqrt(IIA, IIA);
    mpz_tdiv_r(IIC, IIA, IIB);
    return size(IIC);
    */
    long long i;
    for(i=0; i<m; i++)
    {
        if(i*i%m == x) return (int) i;
    }
    return 0;
}

void gprime(int maxp)
{
    char *vis;
    int i, j, k = 0;
    vis = (char *)malloc(PSIZE);
    memset(vis, 0, PSIZE);
    for(i=2; i<PSIZE; i++)
    {
        if(vis[i] == 0)
        {
            k ++;
            if(i<40000)
                for(j=i*i; j<PSIZE; j+=i) vis[j] = 1;
        }
    }
    mip->PRIMES = (int *)malloc(k*sizeof(int));
    k = 0;
    for(i=2; i<PSIZE; i++)
    {
        if(vis[i] == 0)
        {
            mip->PRIMES[k] = i;
            k ++;
        }
    }
    free(vis);
    if(mip->PRIMES[k-1] < maxp)
    {
        printf("ERROR\n");
        fflush(stdout);
        exit(0);
    }
}

void incr(big x, int n, big z)
{
    mpz_add_ui(z, x, n);
}

void decr(big x, int n, big z)
{
    mpz_sub_ui(z, x, n);
}

BOOL nroot(big x, int n, big w)
{
    mpz_root(w, x, n);
}

void negify(big x, big y)
{
    mpz_neg(y, x);
}

int logb2(big x)
{
    return mpz_sizeinbase(x, 2);
}

void powmod(big x, big y, big n, big w)
{
    mpz_powm_sec(w, x, y, n);
}

void* mr_alloc(int len, int size)
{
    return malloc(len * size);
}

void power(big x, long n, big z, big w)
{
    convert(n, IIA);
    powmod(x, IIA, z, w);
}

int xgcd(big x, big y, big xd, big yd, big z)
{
    mpz_gcdext(IIC, IIA, IIB,  x, y);
    while(size(IIA) < 0)
    {
        add(IIA, y, IIA);
        subtract(IIB, x, IIB);
    }
    if(z != xd && z != yd) copy(IIC, z);
    if(xd != yd)
    {
        copy(IIA, xd);
        copy(IIB, yd);
    }
    else
    {
        //add(IIA, IIB, IIA);
        copy(IIA, xd);
    }
    //mpz_gcdext(z, xd, yd, x, y);
    return size(IIC);
}

int smul(int x, int y, int n)
{
    return (int)((((long long)x)*((long long)y)) % ((long long)n));
}
int knuth(int mm,int *epr,big N,big D)
{ /* Input number to be factored N and find best multiplier k  *
   * for use over a factor base epr[] of size mm.  Set D=k.N.  */
    double dp,fks,top;
    BOOL found;
    int i,j,bk,nk,kk,r,p;
    static int K[]={0,1,2,3,5,6,7,10,11,13,14,15,17,0};
    top=(-10.0e0);
    found=FALSE;
    nk=0;
    bk=0;
    epr[0]=1;
    epr[1]=2;
    do
    { /* search for best Knuth-Schroepel multiplier */
        kk=K[++nk];
        if (kk==0)
        { /* finished */
            kk=K[bk];
            found=TRUE;
        }
        premult(N,kk,D);
        fks=log(2.0e0)/(2.0e0);
        r=remain(D,8);
        if (r==1) fks*=(4.0e0);
        if (r==5) fks*=(2.0e0);
        fks-=log((double)kk)/(2.0e0);
        i=0;
        j=1;
        while (j<mm)
        { /* select small primes */
            p=mip->PRIMES[++i];
            r=remain(D,p);
            if (spmd(r,(p-1)/2,p)<=1)
            { /* use only if Jacobi symbol = 0 or 1 */
                epr[++j]=p;
                dp=(double)p;
                if (kk%p==0) fks+=log(dp)/dp;
                else         fks+=2*log(dp)/(dp-1.0e0);
            }
        }
        if (fks>top)
        { /* find biggest fks */
            top=fks;
            bk=nk;
        }
    } while (!found);
    return kk;
}

BOOL factored(long lptr,big T)
{ /* factor quadratic residue */
    BOOL facted;
    int i,j,r,st;  
    partial=FALSE;
    facted=FALSE;
    for (j=1;j<=mm;j++)
    { /* now attempt complete factorisation of T */
        r=(int)(lptr%epr[j]);
        if (r<0) r+=epr[j];
        if (r!=r1[j] && r!=r2[j]) continue;
        while (subdiv(T,epr[j],XX)==0)
        { /* cast out epr[j] */
            e[j]++;
            copy(XX,T);
        }
        st=size(T);
        if (st==1)
        {
           facted=TRUE;
           break;
        }
        if (size(XX)<=epr[j])
        { /* st is prime < epr[mm]^2 */
            if (st>=MR_TOOBIG || (st/epr[mm])>(1+mlf/50)) break;
            if (st<=epr[mm])
                for (i=j;i<=mm;i++)
                if (st==epr[i])
                {
                    e[i]++;
                    facted=TRUE;
                    break;
                }
            if (facted) break;
            lp=st;  /* factored with large prime */
            partial=TRUE;
            facted=TRUE;
            break;
        }
    }
    return facted;
}

BOOL gotcha(void)
{ /* use new factorisation */
    int r,j,i,k,n,rb,had,hp;
    unsigned int t;
    BOOL found;
    found=TRUE;
    if (partial)
    { /* check partial factorisation for usefulness */
        had=lp%hmod;
        forever
        { /* hash search for matching large prime */
            hp=hash[had];
            if (hp<0)
            { /* failed to find match */
                found=FALSE;
                break;
            }
            if (pr[hp]==lp) break; /* hash hit! */
            had=(had+(hmod2-lp%hmod2))%hmod;
        }
        if (!found && nlp>=mlf) return FALSE;
    }
    copy(PP,XX);
    convert(1,YY);
    for (k=1;k<=mm;k++)
    { /* build up square part in YY  *
       * reducing e[k] to 0s and 1s */
        if (e[k]<2) continue;
        r=e[k]/2;
        e[k]%=2;
        expint(epr[k],r,TT);
        multiply(TT,YY,YY);
    }
/* debug only 
	printf("\nX= ");
    cotnum(XX,stdout);
	printf("Y= ");
    cotnum(YY,stdout);
    if (e[0]==1) printf("-1");
    else printf("1");
    for (k=1;k<=mm;k++)
    {
        if (e[k]==0) continue;
        printf(".%d",epr[k]);
    }
    if (partial) printf(".%d\n",lp);
    else printf("\n");
*/
    if (partial)
    { /* factored with large prime */
        if (!found)
        { /* store new partial factorization */
            hash[had]=nlp;
            pr[nlp]=lp;
            copy(XX,z[nlp]);
            copy(YY,w[nlp]);
            for (n=0,rb=0,j=0;j<=mm;j++)
            {
                G[nlp][n]|=((e[j]&1)<<rb);
                if (++rb==nbts) n++,rb=0;
            }
            nlp++;
        }
        if (found)
        { /* match found so use as factorization */
            printf("\b\b\b\b\b\b*");
            fflush(stdout);
            mad(XX,z[hp],XX,NN,NN,XX);
            mad(YY,w[hp],YY,NN,NN,YY);
            for (n=0,rb=0,j=0;j<=mm;j++)
            {
                t=(G[hp][n]>>rb);
                e[j]+=(t&1);
                if (e[j]==2)
                {
                    premult(YY,epr[j],YY);
                    divide(YY,NN,NN);
                    e[j]=0;
                }
                if (++rb==nbts) n++,rb=0;
            }
            premult(YY,lp,YY);
            divide(YY,NN,NN);
        }
    }
    else 
    {
        printf("\b\b\b\b\b\b ");
        fflush(stdout);
    }
    if (found)
    {
        for (k=mm;k>=0;k--)
        { /* use new factorization in search for solution */
            if (e[k]%2==0) continue;
            if (b[k]<0)
            { /* no solution this time */
                found=FALSE;
                break;
            }
            i=b[k];
            mad(XX,x[i],XX,NN,NN,XX);    /* This is very inefficient -  */
            mad(YY,y[i],YY,NN,NN,YY);    /* There must be a better way! */
            for (n=0,rb=0,j=0;j<=mm;j++)
            { /* Gaussian elimination */
                t=(EE[i][n]>>rb);
                e[j]+=(t&1);
                if (++rb==nbts) n++,rb=0;
            }
        }
        for (j=0;j<=mm;j++)
        { /* update YY */
            if (e[j]<2) continue;
            convert(epr[j],TT);
            power(TT,e[j]/2,NN,TT);
            mad(YY,TT,YY,NN,NN,YY);
        }
        if (!found)
        { /* store details in E, x and y for later */
            b[k]=jj;
            copy(XX,x[jj]);
            copy(YY,y[jj]);
            for (n=0,rb=0,j=0;j<=mm;j++)
            {
                EE[jj][n]|=((e[j]&1)<<rb);
                if (++rb==nbts) n++,rb=0;
            }
            jj++;
            printf("%5d",jj);
        }
    }
/*
    for (i=0;i<mm;i++)
    {
        for (j=0;j<1+mm/(8*sizeof(int));j++)
        {
            printf("%x",EE[i][j]);
        }
        printf("\n");
    }
*/
    if (found)
    { /* check for false alarm */
        printf("\ntrying...\n");
        add(XX,YY,TT);
        if (compare(XX,YY)==0 || compare(TT,NN)==0) found=FALSE;
        if (!found) printf("working... %5d",jj);
    }
    return found;
}

int initv(void)
{ /* initialize big numbers and arrays */
    int i,j,d,pak,k,maxp;
    double dp;

    NN=mirvar(0); 
    TT=mirvar(0);
    DD=mirvar(0);
    RR=mirvar(0);
    VV=mirvar(0);
    PP=mirvar(0);
    XX=mirvar(0);
    YY=mirvar(0);
    DG=mirvar(0);
    IG=mirvar(0);
    AA=mirvar(0);
    BB=mirvar(0);

    nbts=8*sizeof(int);

    printf("input number to be factored N= \n");
    d=cinnum(NN,stdin);
    if (isprime(NN))
    {
        printf("this number is prime!\n");
        return (-1);
    }

/* determine mm - optimal size of factor base */

    if (d<8) mm=d;
    else  mm=25;
    if (d>20) mm=(d*d*d*d)/4096;

/* only half the primes (on average) wil be used, so generate twice as
   many (+ a bit for luck) */

    dp=(double)2*(double)(mm+100);  /* number of primes to generate */
    maxp=(int)(dp*(log(dp*log(dp)))); /* Rossers upper bound */
    gprime(maxp);

    epr=(int *)mr_alloc(mm+1,sizeof(int));
  
    k=knuth(mm,epr,NN,DD);

    if (nroot(DD,2,RR))
    {
        printf("%dN is a perfect square!\n",k);
        printf("factors are\n");
        if (isprime(RR)) printf("prime factor     ");
        else             printf("composite factor ");
        cotnum(RR,stdout);
        divide(NN,RR,NN);
        if (isprime(NN)) printf("prime factor     ");
        else             printf("composite factor ");
        cotnum(NN,stdout);
        return (-1);
    }

    printf("using multiplier k= %d\n",k);
    printf("and %d small primes as factor base\n",mm);
    gprime(0);   /* reclaim PRIMES space */

    mlf=2*mm;

/* now get space for arrays */

    r1=(int *)mr_alloc((mm+1),sizeof(int));
    r2=(int *)mr_alloc((mm+1),sizeof(int));
    rp=(int *)mr_alloc((mm+1),sizeof(int));
    b=(int *)mr_alloc((mm+1),sizeof(int));
    e=(int *)mr_alloc((mm+1),sizeof(int));

    logp=(unsigned char *)mr_alloc(mm+1,1);

    pr=(int *)mr_alloc((mlf+1),sizeof(int));
    hash=(int *)mr_alloc((2*mlf+1),sizeof(int));

    sieve=(unsigned char *)mr_alloc(SSIZE+1,1); 

    x=(big *)mr_alloc(mm+1,sizeof(big *));
    y=(big *)mr_alloc(mm+1,sizeof(big *));
    z=(big *)mr_alloc(mlf+1,sizeof(big *));
    w=(big *)mr_alloc(mlf+1,sizeof(big *));

    for (i=0;i<=mm;i++)
    {
        mpz_init(x[i]);//x[i]=mirvar(0);
        mpz_init(y[i]);//y[i]=mirvar(0);
    }
    for (i=0;i<=mlf;i++)
    {
        mpz_init(z[i]);//z[i]=mirvar(0);
        mpz_init(w[i]);//w[i]=mirvar(0);
    }

    EE=(unsigned int **)mr_alloc(mm+1,sizeof(unsigned int *));
    G=(unsigned int **)mr_alloc(mlf+1,sizeof(unsigned int *));
    
    pak=1+mm/(8*sizeof(int));
    for (i=0;i<=mm;i++)
    { 
        b[i]=(-1);
        EE[i]=(unsigned int *)mr_alloc(pak,sizeof(int));
    }

    for (i=0;i<=mlf;i++)
        G[i]=(unsigned int *)mr_alloc(pak,sizeof(int));
    return 1;
}
 
int main()
{ /* factoring via quadratic sieve */
    unsigned int i,j,a,*SV;
    unsigned char logpi;
    int k,S,r,s1,s2,s,NS,logm,ptr,threshold,epri;
    long M,la,lptr;
#ifndef MR_FULLWIDTH
    mip=mirsys(-36,0);
#else
    mip=mirsys(-36,MAXBASE);
#endif
    if (initv()<0) return 0;

    hmod=2*mlf+1;               /* set up hash table */
    convert(hmod,TT);
    while (!isprime(TT)) decr(TT,2,TT);
    hmod=size(TT);
    hmod2=hmod-2;
    for (k=0;k<hmod;k++) hash[k]=(-1);

    M=50*(long)mm;
    NS=(int)(M/SSIZE);
    if (M%SSIZE!=0) NS++;
    M=SSIZE*(long)NS;
    logm=0;
    la=M;
    while ((la/=2)>0) logm++;   /* logm = log(M) */
    rp[0]=logp[0]=0;
    for (k=1;k<=mm;k++)
    { /* find root mod each prime, and approx log of each prime */
        r=subdiv(DD,epr[k],TT);
        printf("(%d %d)", r, epr[k]);
        rp[k]=sqrmp(r,epr[k]);
        logp[k]=0;
        r=epr[k];
        while((r/=2)>0) logp[k]++;
    }
    /*
    for(k=1; k<=mm; k++)
    {
        printf("%d ", rp[k]);
    }
    printf("  ***\n");
    fflush(stdout);
    */
    r=subdiv(DD,8,TT);    /* take special care of 2 */
    if (r==5) logp[1]++;
    if (r==1) logp[1]+=2;

    threshold=logm+logb2(RR)-2*logp[mm];

    jj=0;
    nlp=0;
    premult(DD,2,DG);
    nroot(DG,2,DG);
    
    lgconv(M,TT);
    divide(DG,TT,DG);
    nroot(DG,2,DG);
    if (subdiv(DG,2,TT)==0) incr(DG,1,DG);
    if (subdiv(DG,4,TT)==1) incr(DG,2,DG);
    printf("working...     0");

    forever
    { /* try a new polynomial */
        r=mip->NTRY;
        mip->NTRY=1;         /* speed up search for prime */
        do
        { /* looking for suitable prime DG = 3 mod 4 */
            do {
               incr(DG,4,DG);
            } while(!isprime(DG));
            decr(DG,1,TT);
            subdiv(TT,2,TT);
            powmod(DD,TT,DG,TT);  /* check D is quad residue */
        } while (size(TT)!=1);
        mip->NTRY=r;
        incr(DG,1,TT);
        subdiv(TT,4,TT);
        powmod(DD,TT,DG,BB);
        //cotnum(BB, stdout); fflush(stdout);
        negify(DD,TT);
        mad(BB,BB,TT,DG,TT,TT);
        negify(TT,TT);
        
        premult(BB,2,AA);
        cotnum(AA, stdout); printf("\n"); fflush(stdout);
        cotnum(DG, stdout); printf("\n"); fflush(stdout);
        xgcd(AA,DG,AA,AA,AA);
        cotnum(AA, stdout); printf("\n"); fflush(stdout);
        mad(AA,TT,TT,DG,DG,AA);
        cotnum(AA, stdout); printf("\n"); fflush(stdout);
        //cotnum(TT, stdout); printf("\n"); fflush(stdout);
        multiply(AA,DG,TT);
        //cotnum(AA, stdout); printf("\n"); fflush(stdout);
        //cotnum(DG, stdout); printf("\n"); fflush(stdout);
        //cotnum(TT, stdout); printf("\n"); fflush(stdout);
        add(BB,TT,BB);        /* BB^2 = DD mod DG^2 */
        multiply(DG,DG,AA);   /* AA = DG*DG         */
        xgcd(DG,DD,IG,IG,IG); /* IG = 1/DG mod DD  */
        cotnum(AA, stdout); fflush(stdout);
        cotnum(BB, stdout); fflush(stdout);
        //cotnum(DG, stdout); fflush(stdout);
        //cotnum(DD, stdout); fflush(stdout);
        cotnum(TT, stdout); fflush(stdout);
        cotnum(IG, stdout); fflush(stdout);
        
        r1[0]=r2[0]=0;
        for (k=1;k<=mm;k++) 
        { /* find roots of quadratic mod each prime */
            s=subdiv(BB,epr[k],TT);
            r=subdiv(AA,epr[k],TT);
            printf("(%d ", r);
            r=invers(r,epr[k]);     /* r = 1/AA mod p */
            
            printf("%d %d %d) ", s, r, epr[k]); fflush(stdout);
            
            s1=(epr[k]-s+rp[k]);
            s2=(epr[k]-s+epr[k]-rp[k]);
            printf("[%d %d] ", s1, s2);
            r1[k]=smul(s1,r,epr[k]);
            r2[k]=smul(s2,r,epr[k]);
        }

        for(k=1; k<=mm; k++)
        {
            printf("%d ", r1[k]);
            fflush(stdout);
        }
        puts("");
        for(k=1; k<=mm; k++)
        {
            printf("%d ", r2[k]);
            fflush(stdout);
        }
        puts("");
        if(r2[mm] != 8 && r2[mm] != 0) while(1);
        
        for (ptr=(-NS);ptr<NS;ptr++)
        { /* sieve over next period */
            la=(long)ptr*SSIZE;
            SV=(unsigned int *)sieve;
            for (i=0;i<SSIZE/sizeof(int);i++) *SV++=0;
            for (k=1;k<=mm;k++)
            { /* sieving with each prime */
                epri=epr[k];
                logpi=logp[k];
                r=(int)(la%epri);
                s1=(r1[k]-r)%epri;
                if (s1<0) s1+=epri;
                s2=(r2[k]-r)%epri;
                if (s2<0) s2+=epri;

            /* these loops are time-critical */
   
                for (j=s1;j<SSIZE;j+=epri) sieve[j]+=logpi;
                if (s1==s2) continue;
                for (j=s2;j<SSIZE;j+=epri) sieve[j]+=logpi;
            }

            for (a=0;a<SSIZE;a++)
            { /* main loop - look for fully factored residues */
                if (sieve[a]<threshold) continue;
                lptr=la+a;
                lgconv(lptr,TT);
                S=0;
                multiply(AA,TT,TT);           /* TT = AAx + BB      */
                add(TT,BB,TT);
                mad(TT,IG,TT,DD,DD,PP);       /* PP = (AAx + BB)/G  */
                if (size(PP)<0) add(PP,DD,PP);
                mad(PP,PP,PP,DD,DD,VV);       /* VV = PP^2 mod kN  */
                absol(TT,TT);
                if (compare(TT,RR)<0) S=1;    /* check for -ve VV */
                if (S==1) subtract(DD,VV,VV);
                copy(VV,TT);
                e[0]=S;
                for (k=1;k<=mm;k++) e[k]=0;
                if (!factored(lptr,TT)) continue;
                if (gotcha())
                { /* factors found! */
                    egcd(TT,NN,PP);
                    printf("factors are\n");
                    if (isprime(PP)) printf("prime factor     ");
                    else          printf("composite factor ");
                    cotnum(PP,stdout);
                    divide(NN,PP,NN);
                    if (isprime(NN)) printf("prime factor     ");
                    else          printf("composite factor ");
                    cotnum(NN,stdout);
                    return 0;
                }
            }
        }
    }
    return 0;
}


