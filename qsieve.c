/*
 *   Program to factor big numbers using Pomerance-Silverman-Montgomery  
 *   multiple polynomial quadratic sieve.
 *   See "The Multiple Polynomial Quadratic Sieve", R.D. Silverman,
 *   Math. Comp. Vol. 48, 177, Jan. 1987, pp329-339
 */

#include <stdio.h>
#include <stdlib.h>
#include <math.h> 
#include "miracl.h"

#define SSIZE 100000    /* Maximum sieve size            */

static big NN,TT,DD,RR,VV,PP,XX,YY,DG,IG,AA,BB;
static big *x,*y,*z,*w;
static unsigned int **EE,**G;
static int *epr,*r1,*r2,*rp,*b,*pr,*e,*hash;
static unsigned char *logp,*sieve;
static int mm,mlf,jj,nbts,nlp,lp,hmod,hmod2;
static BOOL partial;
static miracl *mip;

int knuth(int mm,int *epr,big N,big D)
{ /* Input number to be factored N and find best multiplier k  *
   * for use over a factor base epr[] of size mm.  Set D=k.N.  */
    double dp,fks,top;
    BOOL found;
    int i,j,bk,nk,kk,r,p;
    static int K[]={0,1,2,3,5,6,7,10,11,13,14,15,17,0}; //kk取遍K数组
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
        { /* finished */ // 把最大的估计值对应的部分再进行一次求素数而不是直接return
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
        while (j<mm) // 求kk*N的前mm个质数，在这些质数下勒让德符号是0 or 1阿
        { /* select small primes */
            p=mip->PRIMES[++i];
            r=remain(D,p);
            if (spmd(r,(p-1)/2,p)<=1) //勒让德符号
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
    partial=FALSE; // 被分成两部分
    facted=FALSE; // 可以分解
    for (j=1;j<=mm;j++)
    { /* now attempt complete factorisation of T */
        r=(int)(lptr%epr[j]);
        if (r<0) r+=epr[j]; 		/*暂时上下文相关*/
        if (r!=r1[j] && r!=r2[j]) continue;
        while (subdiv(T,epr[j],XX)==0) // XX = T/epr[j]，尝试对 T 用 epr[j] 做质因数分解
        { /* cast out epr[j] */
            e[j]++; //指数+1
            copy(XX,T); //T = XX，继续做
        }
        st=size(T);// 如果T fits in int那么 st 存的就是 T，否则是一个MAX
        if (st==1) // 被当前的epr[j]分解成1了
        {
           facted=TRUE;
           break; // 直接返回true了
        }
        if (size(XX)<=epr[j]) // XX 保存的是最后一次 T/epr[j] 的结果，尽管epr[j]可能不整除 T
        { /* st is prime < epr[mm]^2 */ // 如果成功进了这一步，那么循环一定被break了
            if (st>=MR_TOOBIG || (st/epr[mm])>(1+mlf/50)) break;
            if (st<=epr[mm])
                for (i=j;i<=mm;i++)
                if (st==epr[i])		/* 这部分是想说当前剩下的数比 epr中最大的那个要小，那么就找找看后面的*/
                {
                    e[i]++;
                    facted=TRUE;
                    break;
                }
            if (facted) break;
            lp=st;  /* factored with large prime */ // lp是个全局变量
            partial=TRUE; // 说明被部分分解了
            facted=TRUE;
            break;
        }
    }
    return facted;
}

BOOL gotcha(void) // 进这个过程，前提一定是factored返回true了
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
    copy(PP,XX);	// XX = PP
    convert(1,YY);	// YY=1 
    for (k=1;k<=mm;k++)
    { /* build up square part in YY  *
       * reducing e[k] to 0s and 1s */
        if (e[k]<2) continue;
        r=e[k]/2;	// 开根号
        e[k]%=2;	// 模2给异或方程组用
        expint(epr[k],r,TT); 
        multiply(TT,YY,YY); // YY = YY * epr[k]的r次方，把这一侧的数字乘出来
    }

    if (partial)
    { /* factored with large prime */ // 在构造异或方程组吧
        if (!found)
        { /* store new partial factorization */
            hash[had]=nlp;
            pr[nlp]=lp;
            copy(XX,z[nlp]);
            copy(YY,w[nlp]);
            for (n=0,rb=0,j=0;j<=mm;j++)
            {
                G[nlp][n]|=((e[j]&1)<<rb); // 压位，为了速度
                if (++rb==nbts) n++,rb=0;  // 压nbts=32位
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
    d=cinnum(NN,stdin); /* NN是待分解的整数 */
    if (isprime(NN))
    {
        printf("this number is prime!\n");
        return (-1);
    }

/* determine mm - optimal size of factor base */

    if (d<8) mm=d; /* mm: 因子基的理想大小 */
    else  mm=25;
    if (d>20) mm=(d*d*d*d)/4096;

/* only half the primes (on average) wil be used, so generate twice as
   many (+ a bit for luck) */

    dp=(double)2*(double)(mm+100);  /* number of primes to generate */ /* dp:生成素数的数量 +100 *2均是为了更加保险 */
    maxp=(int)(dp*(log(dp*log(dp)))); /* Rossers upper bound */ /* 罗素上界* maxp:生成素数大小的上界 */
    gprime(maxp);

    epr=(int *)mr_alloc(mm+1,sizeof(int));
  
    k=knuth(mm,epr,NN,DD);

    if (nroot(DD,2,RR)) /* 是完全平方数直接返回 */
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
        x[i]=mirvar(0);
        y[i]=mirvar(0);
    }
    for (i=0;i<=mlf;i++)
    {
        z[i]=mirvar(0);
        w[i]=mirvar(0);
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
    convert(hmod,TT); /* 令TT=hmod */
    while (!isprime(TT)) decr(TT,2,TT); /* TT:=不大于TT的素数 */
    hmod=size(TT); /* 令hmod=TT */
    hmod2=hmod-2;
    for (k=0;k<hmod;k++) hash[k]=(-1);

    M=50*(long)mm;
    NS=(int)(M/SSIZE);
    if (M%SSIZE!=0) NS++;
    M=SSIZE*(long)NS; /* 以上四行做了一件事情:  M:=(50*mm+SSIZE-1)/SSIZE*SSIZE 即M为不小于50*mm的SSIZE的倍数中最小的 */
    logm=0;
    la=M;
    while ((la/=2)>0) logm++;   /* logm = log(M) */ /* 以2为底 */
    rp[0]=logp[0]=0;
    for (k=1;k<=mm;k++)
    { /* find root mod each prime, and approx log of each prime */
        r=subdiv(DD,epr[k],TT); /* TT是临时变量 r=DD mod epr[k] */
        rp[k]=sqrmp(r,epr[k]); /* rp[k] = sqrt(r) mod epr[k] = sqrt(DD mod epr[k]) mod epr[k]*/
        logp[k]=0;
        r=epr[k];
        while((r/=2)>0) logp[k]++;
    }
    r=subdiv(DD,8,TT);    /* take special care of 2 */
    if (r==5) logp[1]++;
    if (r==1) logp[1]+=2;

    threshold=logm+logb2(RR)-2*logp[mm];

    jj=0;
    nlp=0;

    premult(DD,2,DG); 
    nroot(DG,2,DG); /* 以上两行: DG=sqrt(DD*2) */
    
    lgconv(M,TT);
    divide(DG,TT,DG);
    nroot(DG,2,DG); /* 以上三行: DG=sqrt(DG/M) */
    if (subdiv(DG,2,TT)==0) incr(DG,1,DG); /* DG若可整除2，则自增1 */
    if (subdiv(DG,4,TT)==1) incr(DG,2,DG); /* DG若模4余1，则自增2 */ /* 实际上这两行是令DG等于不小余DG的数中模4余3的最小的数 */

    printf("working...     0");

    forever
    { /* try a new polynomial */
        r=mip->NTRY; 
        mip->NTRY=1;         /* speed up search for prime */ /* 将素数测试次数改为1，以提高速度 */
        do
        { /* looking for suitable prime DG = 3 mod 4 */
            do {
               incr(DG,4,DG);
            } while(!isprime(DG));
            decr(DG,1,TT);
            subdiv(TT,2,TT); /* 以上两行: TT=(DG-1)/2 其中DG是素数 */
            powmod(DD,TT,DG,TT);  /* check D is quad residue */ /* TT=DD^TT mod DG */
        } while (size(TT)!=1); /* 如果DD是二次剩余，则停止 */
        mip->NTRY=r; /* 恢复默认的素数测试次数 */
        incr(DG,1,TT);
        subdiv(TT,4,TT);
        powmod(DD,TT,DG,BB); /* 以上三行: BB=DD^((DG+1)/4) mod DG */
        negify(DD,TT); 
        mad(BB,BB,TT,DG,TT,TT);
        negify(TT,TT); /* 以上三行: TT=-(BB*BB-DD)/DG */
        premult(BB,2,AA); /* AA=2*BB */
        xgcd(AA,DG,AA,AA,AA); /* AA = 1/AA mod DG */
        mad(AA,TT,TT,DG,DG,AA); /* AA = AA*TT mod DG */
        multiply(AA,DG,TT); /* TT=AA*DG */
        add(BB,TT,BB);         /* BB^2 = DD mod DG^2 */
        multiply(DG,DG,AA);    /* AA = DG*DG         */
        xgcd(DG,DD,IG,IG,IG);  /* IG = 1/DG mod DD  */

        r1[0]=r2[0]=0;
        for (k=1;k<=mm;k++) 
        { /* find roots of quadratic mod each prime */
            s=subdiv(BB,epr[k],TT); // TT = BB / epr[k], s = BB mod epr[k]
            r=subdiv(AA,epr[k],TT); // TT = AA / epr[k], r = AA mod epr[k]
            r=invers(r,epr[k]);     // r = 1/r mod epr[k]
            s1=(epr[k]-s+rp[k]);
            s2=(epr[k]-s+epr[k]-rp[k]);
            r1[k]=smul(s1,r,epr[k]); // r1[k] = s1 * r (mod epr[k])
            r2[k]=smul(s2,r,epr[k]); // r2[k] = s2 * r (mod epr[k])
        }

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

