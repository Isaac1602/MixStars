/*******Version del codigo para estrellas mixtas con potencial cuatico **********/
/*******En unidades fermionicas, Version 1 kapa=epsi^(2(1-gama))K ***********/
/************************************************************************************/
#include <stdio.h>
#include "nrutil.v2.c"
#include "nrutil.v2.h"
#include <math.h>
/* Approximate square root of the machine precision*/
#define EPS       1.0e-14

/*ESTE PROGRAMA GENERA LOS DATOS INICILAES PARA UNA ESTRELLA DE BOSONES 
GENERA LOS SIGUIENTES ARCHIVOS
ISO.DAT X,PHI,PSI,ALPHA,PHI', PSI', ALPHA' EN UNA GRID UNIFORME
LASTFILE.DAT X,PHI,PSI,ALPHA,PHI', PSI', ALPHA' EN UNA GRID UNIFORME CON INTERVALO HDESEADO */
/*ULTIMA MODIFICACION 13-MARZO-2009 HASTA AHORITA ES EL MEJOR */

/* A small number se usa en LUDCMP*/
#define TINY      1.0e-20

/* Constantes usadas en la funcion LNSRCH*/
#define ALF       1.0e-4
#define TOLX      1.0e-7 

/* Se usa para calcular stpmax usado en LNSRCH*/
#define STPMX    100.0

/* Usadas en NEWT*/
#define MAXITS    2000
#define TOLF      1.0e-12
#define TOLMIN    1.0e-12
/*#define TOLF      1.0e-6
#define TOLMIN    1.0e-8*/

#define FREERETURN {free_vector(f,1,n);free_vector(xold,1,n);\
        free_vector(fdv,1,n);free_vector(g,1,n);free_matrix(jac,1,n,1,n);\
        free_ivector(indx,1,n);return;}
#define PI (acos(-1.0))
/**************************************************************************/

/* N2: dimension de v y f, numero de condiciones iniciales faltantes */
#define N2        1
#define L         0.0    

/**************************************************************************/
/* No de pasos en la integracion del shooting*/

#define NSTEP 6000
/*5000
7500*/
/*Tolerancia para el valor de la presión en el shooting*/

#define tolerancia 1.0e-8
#define tol 1.0e-08
FILE *fpmu;

int TailNSTEP;
int NSTEPhdeseado;
long double lambda;
/* No. de ecuaciones a integrar*/
int nvar;
long double *f,*vout;
/* y: matriz con columnas las variables y renglones los pasos de integracion
xx: vector con pasos de integracion*/
long double **y,*xx;
long double **tailedy,*tailedxx;
long double **polary;
long double **iso;
long double **ymin,*xxmin;
long double *vmin;
long double **lasty,*interx;
/* nrfuncv es la funcion que actualiza las condiciones iniciales, integra y evalua el vector de funciones f. Se utiliza en fminx donde se obtiene 1/2 f.f*/
void (*nrfuncv)(int n, long double v[], long double f[]);
/* Variables externas */
long double x1, x2;
long double h;
int j_tail;
long double hmin;
long double hdeseado;
long double c1;
long double c2;
/* Variables para las cantidades caracteristicas de la configuracion de campo escalar*/
long double R_99, NoPartF,NoPartB,Mass,BindingE; 
long double R_tail, NoPart_tail, M_tail,BindingE_tail,phi_tail;
long double omega;
long double cct;

long double phi0,rho0,gama,kapa,*mu,p_0,R_starb,R_starf,primkapa,m,*rho,*rho_iso,*epsilon,x_final,eta;
long double atms,*Eniso1,*Eniso2,*ddfac,mu0;
long double epsi,emu, mb,mbf; //cantiades para las unidades fermionicas
/*****************************************************************************/
void load(long double x1, long double v[], long double y[])
     /* Conciciones iniciales. */
{
  y[1] = 1.0;     //a(0)=1.0
  y[2] = 1.0;     //alpha(0)=1.0
  y[3] = phi0;    //phi(0)=phi_0 parametro libre
  y[4] = 0.0;     //phi'(0)=0.0 
  y[5] = v[1];    //valor inicial (guess) para omega
  y[6] = pow((4.0*PI),1.0-gama)*kapa*pow(rho0,gama); //valor inicial de la presion
  y[7] = 0.0;     //valor inicial para el número de bosones N_B
  y[8] = 0.0;     //valor inicial para el número de bosones N_F
}

void score(long double xf, long double y[], long double f[])
     /* Vector f.   */
{
  /*f[1] = y[1];*/
  f[1] = y[3]*(sqrt(1.-y[5]*y[5]/(y[1]*y[1]*y[2]*y[2]))+1./(xf*xf))+y[4];
  //printf("phi=%14.8Le a=%14.8Le alpha=%14.8Le omega=%14.8Le f1=%14.8Le\n",y[3],y[1],y[2],y[5],f[1]);
}

void derivs(long double x, long double y[], long double dydx[])
{
  long double rhot,phi,phip,pres,a,alpha,omega;
  
  a = y[1];
  alpha = y[2];
  phi = y[3];
  phip = y[4];
  omega = y[5];
  pres= y[6];
    
  rhot = 0.0;
  
  if(y[6]>0.0) {
      
    //rhot= pow(y[6]/kapa,1.0/gama);
    rhot= pow(1/(4.0*PI),(1.0/gama-1.0))*pow(pres/kapa,1.0/gama);
      
    dydx[1] = 0.5*a*((1.0-a*a)/x + a*a*x*((omega*omega/(alpha*alpha)+1.0+0.5*lambda*phi*phi)*phi*phi*emu*emu + phip*phip/(a*a) + 2.0*(rhot + pres/(gama - 1.0))));
    dydx[2] = 0.5*alpha*((a*a-1.0)/x + a*a*x*((omega*omega/(alpha*alpha)-1.0-0.5*lambda*phi*phi)*phi*phi*emu*emu + phip*phip/(a*a) + 2.0*pres));
    dydx[3] = phip;
    dydx[4] = a*a*phi*emu*emu*(1.0-omega*omega/(alpha*alpha)+lambda*phi*phi) - phip*(2.0/x+dydx[2]/alpha-dydx[1]/a);
    dydx[5] = 0;
    dydx[6] = -(rhot+ pres/(gama - 1.0) + pres)*dydx[2]/alpha;
    dydx[7] = omega*a*phi*phi*x*x/alpha; //estas son las correctas
    dydx[8] = x*x*a*rhot; //estas son las correctas
    
  }
  
  else
    {
      dydx[1] = 0.5*a*((1.0-a*a)/x + a*a*x*((omega*omega/(alpha*alpha)+1.0+0.5*lambda*phi*phi)*phi*phi*emu*emu + phip*phip/(a*a) + 2.0*(rhot + pres/(gama - 1.0))));
      dydx[2] = 0.5*alpha*((a*a-1.0)/x + a*a*x*((omega*omega/(alpha*alpha)-1.0-0.5*lambda*phi*phi)*phi*phi*emu*emu + phip*phip/(a*a) + 2.0*pres));
      dydx[3] = phip;
      dydx[4] = a*a*phi*emu*emu*(1.0-omega*omega/(alpha*alpha)+lambda*phi*phi) - phip*(2.0/x+dydx[2]/alpha-dydx[1]/a);
      dydx[5] = 0;
      dydx[6] =  -100.0*pres;
      dydx[7] = omega*a*phi*phi*x*x/alpha; //estas son las correctas
      dydx[8] = x*x*a*rhot; //estas son las correctas
    
      // printf("%14.8Le %14.8Le \n",dydx[8],y[8]);
    }
}
/*****************************************************************************/



void rk4(long double y[],long double dydt[],int n,long double x,long double h,long double yout[],
         void (*derivs)(long double,long double [],long double []))
{ 
  int i;
  long double xh,hh,h6,*dym,*dyt,*yt;

  dym = vector(1,n);
  dyt = vector(1,n);
  yt  = vector(1,n);
  hh  = h*0.5;
  h6  = h/6.0;
  xh  = x+hh;

  for (i = 1;i <= n;i++){
    yt[i] = y[i]+hh*dydt[i];
//    if(yt[7]<tolerancia) yt[7]=0.0;
  }
  (*derivs)(xh,yt,dyt);
  for (i = 1;i <= n;i++){
    yt[i] = y[i]+hh*dyt[i];
//    if(yt[7]<tolerancia) yt[7]=0.0;
  }

  (*derivs)(xh,yt,dym);
  for (i = 1; i <= n; i++){
    yt[i] = y[i]+h*dym[i]; 
//    if(yt[7]<tolerancia) yt[7]=0.0;
    dym[i] += dyt[i];
  }

  (*derivs)(x+h,yt,dyt);
  for (i = 1;i <= n;i++){
    yout[i] = y[i]+h6*(dydt[i]+dyt[i]+2.0*dym[i]);  
//    if(yt[7]<tolerancia) yt[7]=0.0;
  }
  free_vector(yt,1,n);
  free_vector(dyt,1,n);
  free_vector(dym,1,n);
}

 
void rkdumb(long double vstart[], int nvar, long double x1, long double x2, int nstep,
        void (*derivs)(long double, long double [], long double []))
{
        void rk4(long double y[], long double dydx[], int n, long double x, long double h, long double yout[],
                void (*derivs)(long double, long double [], long double []));
        int i,k;
        long double x;
        /*long double x,h;*/
        /*
        long double *v,*vout,*dv;
        */
        long double *v,*dv;
        v=vector(1,nvar);
        /* 
        vout=vector(1,nvar);
        */
        dv=vector(1,nvar);
        for (i=1;i<=nvar;i++) {
                v[i]=vstart[i];
                y[i][1]=v[i];
        }
        xx[1]=x1;
        x=x1;
        h=(x2-x1)/nstep;
        printf(" h= %14.8Le\n",h);
        for (k=1;k<=nstep;k++) {
          (*derivs)(x,v,dv); 
          rk4(v,dv,nvar,x,h,vout,derivs);
          if ((long double)(x+h) == x) nrerror("Step size too small in routine rkdumb");
         
          x += h;
          xx[k+1]=x;
          for (i=1;i<=nvar;i++) {
            v[i]=vout[i];
            y[i][k+1]=v[i];
          }
          
        }
        free_vector(dv,1,nvar);
        free_vector(v,1,nvar);

}
/*void shoot(int n, long double v[], long double f[])*/
void shoot(int n, long double v[], long double f[])
{
  void derivs(long double x, long double y[], long double dydx[]);
  void load(long double x1, long double v[], long double y[]);
  void rkdumb(long double vstart[], int nvar, long double x1, long double x2, int nstep,
              void (*derivs)(long double, long double [], long double []));
  void rk4(long double y[],long double dydt[],int n,long double x,long double h,long double yout[],
           void (*derivs)(long double,long double [],long double []));
  void score(long double xf, long double y[], long double f[]);
  long double *vstart;

  vstart = vector(1,nvar);

  load(x1,v,vstart);
  rkdumb(vstart,nvar,x1,x2,NSTEP,derivs);
  score(x2,vout,f);
  free_vector(vstart,1,nvar);
}

void fdjac(int n, long double x[], long double fvec[], long double **df,
        void (*vecfunc)(int, long double [], long double []))
{
        int i,j;
        long double l,temp, *faqui;
        faqui=vector(1,n);
        for (j=1;j<=n;j++) {
                temp=x[j];
                l=EPS*fabsl(temp);
                if (l == 0.0) l=EPS;
                x[j]=temp+l;
                l=x[j]-temp;
                (*vecfunc)(n,x,faqui);
                x[j]=temp;
                for (i=1;i<=n;i++) df[i][j]=(faqui[i]-fvec[i])/l;
        }
        free_vector(faqui,1,n);
}

void ludcmp(long double **a, int n, int *indx, long double *d)
{
        int i,imax,j,k;
        long double big,dum,sum,temp;
        long double *vv;

        vv=vector(1,n);
        *d=1.0;
        for (i=1;i<=n;i++) {
                big=0.0;
                for (j=1;j<=n;j++)
                        if ((temp=fabsl(a[i][j])) > big) big=temp;
                if (big == 0.0) nrerror("Singular matrix in routine ludcmp");
                vv[i]=1.0/big;
        }
        for (j=1;j<=n;j++) {
                for (i=1;i<j;i++) {
                        sum=a[i][j];
                        for (k=1;k<i;k++) sum -= a[i][k]*a[k][j];
                        a[i][j]=sum;
                }
                big=0.0;
                for (i=j;i<=n;i++) {
                        sum=a[i][j];
                        for (k=1;k<j;k++)
                                sum -= a[i][k]*a[k][j];
                        a[i][j]=sum;
                        if ( (dum=vv[i]*fabsl(sum)) >= big) {
                                big=dum;
                                imax=i;
                        }
                }
                if (j != imax) {
                        for (k=1;k<=n;k++) {
                                dum=a[imax][k];
                                a[imax][k]=a[j][k];
                                a[j][k]=dum;
                        }
                        *d = -(*d);
                        vv[imax]=vv[j];
                }
                indx[j]=imax;
                if (a[j][j] == 0.0) a[j][j]=TINY;
                if (j != n) {
                        dum=1.0/(a[j][j]);
                        for (i=j+1;i<=n;i++) a[i][j] *= dum;
                }
        }
        free_vector(vv,1,n);
}

void lubksb(long double **a, int n, int *indx, long double b[])
{
int i,ii=0,ip,j;
        long double sum;

        for (i=1;i<=n;i++) {
                ip=indx[i];
                sum=b[ip];
                b[ip]=b[i];
                if (ii)
                        for (j=ii;j<=i-1;j++) sum -= a[i][j]*b[j];
                else if (sum) ii=i;
                b[i]=sum;
        }
        for (i=n;i>=1;i--) {
                sum=b[i];
                for (j=i+1;j<=n;j++) sum -= a[i][j]*b[j];
                b[i]=sum/a[i][i];
        }
}

long double fminx(long double x[])
{
        int i;
        long double sum;

        (*nrfuncv)(N2,x,f);
        for (sum=0.0,i=1;i<=N2;i++) sum += SQR(f[i]);
        return 0.5*sum;
}

void lnsrch(int n, long double xold[], long double fold, long double g[], long double p[], long double x[],
        long double *f, long double stpmax, int *check, long double (*func)(long double []))
{
        int i;
        long double a,alam,alam2,alamin,b,disc,f2,rhs1,rhs2,slope,sum,temp,
                test,tmplam;

        *check=0;
        for (sum=0.0,i=1;i<=n;i++) sum += p[i]*p[i];
        sum=sqrt(sum);
        if (sum > stpmax)
                for (i=1;i<=n;i++) p[i] *= stpmax/sum;
        for (slope=0.0,i=1;i<=n;i++)
                slope += g[i]*p[i];
        if (slope >= 0.0) nrerror("Roundoff problem in lnsrch.");
        test=0.0;
        for (i=1;i<=n;i++) {
                temp=fabsl(p[i])/FMAX(fabsl(xold[i]),1.0);
                if (temp > test) test=temp;
        }
        alamin=TOLX/test;
        alam=1.0;
        for (;;) {
                for (i=1;i<=n;i++) x[i]=xold[i]+alam*p[i];
                *f=(*func)(x);
                if (alam < alamin) {
                        for (i=1;i<=n;i++) x[i]=xold[i];
                        *check=1;
                        return;
                } else if (*f <= fold+ALF*alam*slope) return;
                else {
                        if (alam == 1.0)
                                tmplam = -slope/(2.0*(*f-fold-slope));
                        else {
                                rhs1 = *f-fold-alam*slope;
                                rhs2=f2-fold-alam2*slope;
                                a=(rhs1/(alam*alam)-rhs2/(alam2*alam2))/(alam-alam2);
                                b=(-alam2*rhs1/(alam*alam)+alam*rhs2/(alam2*alam2))/(alam-alam2);
                                if (a == 0.0) tmplam = -slope/(2.0*b);
                                else {
                                        disc=b*b-3.0*a*slope;
                                        if (disc < 0.0) tmplam=0.5*alam;
                                        else if (b <= 0.0) tmplam=(-b+sqrt(disc))/(3.0*a);
                                        else tmplam=-slope/(b+sqrt(disc));
                                }
                                if (tmplam > 0.5*alam)
                                        tmplam=0.5*alam;
                        }
                }
                alam2=alam;
                f2 = *f;
                alam=FMAX(tmplam,0.1*alam);
        }
}
void newt(long double x[], int n, int *check,
        void (*vecfunc)(int, long double [], long double []))
{
        void fdjac(int n, long double x[], long double fvec[], long double **df,
                void (*vecfunc)(int, long double [], long double []));
        long double fminx(long double x[]);
        void lnsrch(int n, long double xold[], long double fold, long double g[], long double p[], long double x[],
                 long double *f, long double stpmax, int *check, long double (*func)(long double []));
        void lubksb(long double **a, int n, int *indx, long double b[]);
        void ludcmp(long double **a, int n, int *indx, long double *d);

        int i,its,j,*indx;
        long double d,den,minf,minfold,stpmax,sum,temp,test,**jac,*g,*fdv,*xold;
        /*
        int i,its,j,*indx;
        long double d,den,f,fold,stpmax,sum,temp,test,**fjac,*g,*p,*xold;
        */
        indx=ivector(1,n);
        jac=matrix(1,n,1,n);
        g=vector(1,n);
        fdv=vector(1,n);
        xold=vector(1,n);
        f=vector(1,n);
        /*
        nn=n;
        */
        nrfuncv=vecfunc;
        minf=fminx(x);
        printf("minf=%14.8Le\n",minf);
        test=0.0;
        for (i=1;i<=n;i++)
                if (fabsl(f[i]) > test) test=fabsl(f[i]);
        printf("test=%14.8Le\n",test);
        if (test < 0.01*TOLF) {
                *check=0;
                FREERETURN
        }
        for (sum=0.0,i=1;i<=n;i++) sum += SQR(x[i]);
        stpmax=STPMX*FMAX(sqrt(sum),(long double)n);
        for (its=1;its<=MAXITS;its++) {
                fdjac(n,x,f,jac,vecfunc);
                for (i=1;i<=n;i++) {
                        for (sum=0.0,j=1;j<=n;j++) sum += jac[j][i]*f[j];
                        g[i]=sum;
                }
                for (i=1;i<=n;i++) xold[i]=x[i];
                minfold=minf;
                for (i=1;i<=n;i++) fdv[i] = -f[i];
                ludcmp(jac,n,indx,&d);
                lubksb(jac,n,indx,fdv);
                lnsrch(n,xold,minfold,g,fdv,x,&minf,stpmax,check,fminx);
                test=0.0;
                for (i=1;i<=n;i++)
                        if (fabsl(f[i]) > test) test=fabsl(f[i]);
                if (test < TOLF) {
                        *check=0;
                        FREERETURN
                }
                if (*check) {
                        test=0.0;
                        den=FMAX(minf,0.5*n);
                        for (i=1;i<=n;i++) {
                                temp=fabsl(g[i])*FMAX(fabsl(x[i]),1.0)/den;
                                if (temp > test) test=temp;
                        }
                        *check=(test < TOLMIN ? 1 : 0);
                        FREERETURN
                }
                test=0.0;
                for (i=1;i<=n;i++) {
                        temp=(fabsl(x[i]-xold[i]))/FMAX(fabsl(x[i]),1.0);
                        if (temp > test) test=temp;
                }
                if (test < TOLX) FREERETURN
        }
        nrerror("MAXITS exceeded in newt");
}
int characquantities(long double **yy, long double x[], long double vv[])
{
  int j;
  int j_tailestrella;
  long double M_r;
  
  M_r=0.0;
  /****  M_x = x/2*(1-1/(a*a))   R_99*/
  for (j=1; j<=NSTEP ; j+=1){
    M_r=x[j]/2.0*(1.-1./(yy[1][j]*yy[1][j]));
    if (M_r/(1./2.*x[NSTEP+1]*(1.-1./(yy[1][NSTEP+1]*yy[1][NSTEP+1]))) < 0.99) R_99 = x[j];
  } 
  /****  No Part y radio de la estrella de bosones*/
  NoPartB = yy[7][NSTEP+1];
  
  for(j=NSTEP;j>=1;j--)
    if(yy[7][j+1]/NoPartB > 0.95) R_starb=x[j];
  
  /****  No Part y radio de la estrella de fermiones*/  
  NoPartF = yy[8][NSTEP+1];
  
  for(j=NSTEP;j>=1;j--)
    if(yy[8][j+1]/NoPartF > 0.95) R_starf=x[j]; 
  
  
  /**** Mass total*/
  Mass = 1./2.*x[NSTEP+1]*(1.-1./(yy[1][NSTEP+1]*yy[1][NSTEP+1]));
  
  /**** j_tail:Lugar en el que cambia de signo la No_Part'', el campo empieza a crecer*/
  j_tailestrella=NSTEP+1;
  
  printf("j_tail= %d\n",j_tailestrella);
  printf("x(tailM)= %14.8Le\n",x[j_tailestrella]);
  printf("a=%14.8Le\n",yy[1][j_tailestrella]);
  
  
  /**** Masa elegida segun j_tail*/
  M_tail = .5*x[j_tailestrella]*(1.-1./(yy[1][j_tailestrella]*yy[1][j_tailestrella]));
  printf("Mass_tail= %14.8Le\n",M_tail);
  
  /**** Campo escalar minimo*/
  phi_tail = yy[3][j_tailestrella];
  
  printf("phi(jtail)= %14.8Le\n",phi_tail);
  
  /**** Radio de la config segun jtail*/
  R_tail=x[j_tailestrella];
  /**** cct: Reescalamiento de N*/
  cct = yy[2][j_tailestrella]*yy[1][j_tailestrella];
  /**** omega*/
  omega = vv[1]/cct;
  return j_tailestrella;
}

int tailer(long double **yy, long double x[], long double vv[],long double hm)
{
  int j;
  int tailj;
  long double taildx,xtail,S;

  
  taildx = hm;

/****  tailj=j_tail-360;*/

  tailj=j_tail;
  S = hm*(TailNSTEP-j_tail);


/**** Extension de las componentes metricas*/
  for(j=1;j<=j_tail;j++) {
    tailedy[1][j]=yy[1][j];
    tailedy[2][j]=yy[2][j];
  }

 for(j=1;j<=TailNSTEP-j_tail;j++) {
    xtail=x[j_tail]+taildx;
    tailedy[1][j_tail+j]=1./sqrt(1.-2.*M_tail/xtail);
    tailedy[2][j_tail+j]=sqrt(1.-2*M_tail/xtail)*cct;
    taildx +=hm;
  }
  
/**** Extension del campo y su derivada*/
  for (j=1;j<=tailj;j++) {
    tailedy[3][j]=yy[3][j];
    tailedy[4][j]=yy[4][j];
  }

  for(j=1; j<=TailNSTEP-tailj; j++){
    xtail=x[tailj]+taildx;
    tailedy[3][tailj+j]=0.0;
    tailedy[4][tailj+j]=0.0;
    //tailedy[3][tailj+j]=yy[3][tailj]*x[tailj]/xtail*exp(sqrt(1.-omega*omega)*(x[tailj]-xtail));
    //tailedy[4][tailj+j]=yy[4][tailj]*(x[tailj]/xtail)*(x[tailj]/xtail)*(1.+xtail*sqrt(1.-omega*omega))/(1.+x[tailj]*sqrt(1.-omega*omega))*exp(sqrt(1.-omega*omega)*(x[tailj]-xtail));
    taildx +=hm;
      }
 

  /**** Extension de la presion, mu y la densidad del fluido*/
  for (j=1;j<=tailj;j++) {
    tailedy[5][j]=yy[6][j]; //presion
    
    if(tailedy[5][j]>0)
      {
          tailedy[6][j]= pow(1/(4.0*PI),1.0/gama-1.0)*pow(tailedy[5][j]/kapa,1.0/gama); //rho (densidad del fluido perfecto)
          tailedy[7][j]= tailedy[6][j] + tailedy[5][j]/(gama-1.0); //mu (rho(1+epsilon)
       // tailedy[6][j]= pow(tailedy[5][j]/kapa,1.0/gama); //rho (densidad del fluido perfecto)
       // tailedy[7][j]= tailedy[6][j] + tailedy[5][j]/(gama-1.0); //mu (rho(1+epsilon)
      }
    else
      {
        tailedy[6][j]=0.0;
        tailedy[7][j]=0.0;
      }
  }

  
  for(j=1; j<=TailNSTEP-tailj; j++){
    tailedy[5][tailj+j]=0.0;
    tailedy[6][tailj+j]=0.0;
    tailedy[7][tailj+j]=0.0;
  }

    /****Se elige el valor de rho como el máximo entre el valor numérico y atmsxrho0 *****/
    for(j=1;j<=TailNSTEP;j++) {
        tailedy[6][j]=fmax(tailedy[6][j],atms*rho0);
        tailedy[5][j]=pow(4.0*PI,1.0 - gama)*kapa*pow(tailedy[6][j],gama);
        tailedy[7][j]=tailedy[6][j]+(tailedy[5][j]/(gama-1.0));
        //printf("rho=%14.8Le pres=%14.8Le\n", tailedy[6][j],tailedy[5][j]);
        }
   
    
  /**** Extension de la coordenada x */
  for(j=1;j<=NSTEP+1;j++)tailedxx[j]=x[j];
  
  taildx = hm;
  
  for(j=1;j<=TailNSTEP-(NSTEP+1);j++){
    xtail=x[NSTEP+1]+taildx;
    tailedxx[NSTEP+1+j]=xtail;
    taildx +=hm;
  }

   
  /**** Campos en coordenadas Polares*/
  for(j=1;j<=TailNSTEP;j++){
    polary[1][j]=tailedy[1][j];       //funcion metrica radial a(x)
    polary[2][j]=tailedy[2][j]/cct;   //funcion metrica temporal alpha(r)
    polary[3][j]=tailedy[3][j];       //campo escalar phi(x)
    polary[4][j]=tailedy[4][j];       //derivada del campo escalar phi'(x)
    polary[5][j]=tailedy[5][j];       //presion del fluido p(x)
    polary[6][j]=tailedy[6][j];       //densidad del fluido rho(x)
    polary[7][j]=tailedy[7][j];       //funcion mu(x)
   
  }
  
  return 0;
}

/******************************************************************/
/*********Calculo de las constricciones del sistema ***************/
/******************************************************************/

int constraint(long double **yy, long double x[], long double vv[])
{
  long double *a, *alpha, *phi, *p,*a_i,*alpha_i,*phi_i,*p_i;
  long double *da,*dl,*dp,*ddp,*d2a,*d2l,*tta,*ttl,*TT,*Enp,*tta1,*ttl1,*TT1,*pdda,*pddl,*z_b1,*z_b2;
  long double *pda,*pdl,*pdp,*pddp,*pkka,*pkkl,*ptt,*pttl,*pTT,*Eni;
  FILE *ifpc,*ifpcp,*ifpc2,*ifpc3,*ifpc4,*fp1,*fpz;
  int j;
  
  ifpc = fopen("Aconstraintbosfer.dat", "w");
  ifpcp = fopen("AconstraintPbosfer.dat", "w");
  ifpc2 = fopen("Aconstraintbosfer1.dat","w");
  ifpc3 = fopen("Aconstraintbosfer2.dat","w");
  ifpc4 = fopen("Aconstraintderivadas.dat","w");
  fp1 = fopen("inicialdata.dat","w");
  fpz = fopen("shiftbos0.63.dat","w");

  

  a = vector(1,NSTEP+1);
  alpha = vector(1,NSTEP+1);
  phi = vector(1,NSTEP+1);
  p = vector(1,NSTEP+1);
  da = vector(1,NSTEP+1);
  dl = vector(1,NSTEP+1);
  dp = vector(1,NSTEP+1);
  ddp= vector(1,NSTEP+1);
  tta = vector(1,NSTEP+1);
  tta1 = vector(1,NSTEP+1); 
  ttl= vector(1,NSTEP+1);
  ttl1 = vector(1,NSTEP+1);
  TT = vector(1,NSTEP+1);
  TT1 = vector(1,NSTEP+1);
  Enp = vector(1,NSTEP+1);
  
  
  a_i = vector(1,TailNSTEP);
  alpha_i = vector(1,TailNSTEP);
  phi_i = vector(1,TailNSTEP);
  p_i= vector(1,TailNSTEP);
  pda = vector(1,TailNSTEP);
  pdl = vector(1,TailNSTEP);
  pdp = vector(1,TailNSTEP);
  pddp= vector(1,TailNSTEP);
  pkka= vector(1,TailNSTEP);
  pkkl= vector(1,TailNSTEP);
  ptt = vector(1,TailNSTEP);  
  pttl= vector(1,TailNSTEP);
  pTT = vector(1,TailNSTEP);
  Eni = vector(1,TailNSTEP);
  d2a = vector(1,TailNSTEP);
  d2l = vector(1,TailNSTEP);
  pdda = vector(1,TailNSTEP);
  pddl = vector(1,TailNSTEP);
  z_b1 = vector(1,TailNSTEP);
  z_b2 = vector(1,TailNSTEP);
 
 

  for(j=1;j<=NSTEP+1;j++){
    a[j] = yy[1][j];
    alpha[j] = yy[2][j];
    phi[j] = yy[3][j];
    p[j] = yy[6][j];
    }
  
  mu0=0.0;
  /**** Derivadas del campo y las componentes metricas del shooting*/
  for (j=2;j<=NSTEP;j++)da[j]=(yy[1][j+1]-yy[1][j-1])/(x[j+1]-x[j-1]);
  for (j=2;j<=NSTEP;j++)dl[j]=(yy[2][j+1]-yy[2][j-1])/(x[j+1]-x[j-1]);
  for (j=2;j<=NSTEP;j++)dp[j]=(yy[3][j+1]-yy[3][j-1])/(x[j+1]-x[j-1]);
  for (j=2;j<=NSTEP;j++)ddp[j]=(yy[3][j+1]-2.*yy[3][j]+yy[3][j-1])/((x[j]-x[j-1])*(x[j]-x[j-1]));

    for(j=2; j<=NSTEP;j++)
    fprintf(ifpc2,"%14.8Le %14.8Le %14.8Le %14.8Le\n",x[j],dp[j],yy[4][j],dp[j]-yy[4][j]);
  
  /**** Terminos de las ecuaciones con los resultados del shooting */
      
  for (j=2;j<=NSTEP;j++){
    if(yy[6][j]>0.0) mu0 = pow(m*m/(4.0*PI),(1.0/gama-1.0))*pow(yy[6][j]/kapa,1.0/gama) + y[6][j]/(gama-1.0); 
    
    tta[j] = 0.5*a[j]*((1.0-a[j]*a[j])/x[j]+a[j]*a[j]*x[j]*((vv[1]*vv[1]/(alpha[j]*alpha[j])+1.0+0.5*lambda*phi[j]*phi[j])*phi[j]*phi[j]+dp[j]*dp[j]/(a[j]*a[j])+2.0*mu0));
    ttl[j]  = 0.5*alpha[j]*((a[j]*a[j]-1.0)/x[j] + a[j]*a[j]*x[j]*((vv[1]*vv[1]/(alpha[j]*alpha[j])-1.0-0.5*lambda*phi[j]*phi[j])*phi[j]*phi[j] + dp[j]*dp[j]/(a[j]*a[j])+2.0*p[j]));
    fprintf(ifpc,"%14.8Le %14.8Le %14.8Le %14.8Le %14.8Le %14.8Le %14.8Le\n",x[j],da[j],dl[j],tta[j],ttl[j],da[j]-tta[j],dl[j]-ttl[j]);
    }
    
    
    /*****este término no se para que lo defini *********************************/
    //    Enp[j] = 2.0*da[j]/(x[j]*yy[3][j]*yy[3][j]*yy[3][j]) + 1.0/(x[j]*x[j]) - 1.0/(x[j]*x[j]*yy[3][j]*yy[3][j]) - 4.0*PI*((vv[1]*vv[1]/(yy[4][j]*yy[4][j])+1.0)*yy[1][j]*yy[1][j]+ yy[2][j]*yy[2][j]/(yy[3][j]*yy[3][j]) +2.0* mu0);
    
    //    fprintf(ifpc2,"%14.8Le %14.8Le %14.8Le %14.8Le %14.8Le\n",x[j],Enp[j], 4.0*da[j]/(x[j]*yy[3][j]*yy[3][j]*yy[3][j]) + 2.0/(x[j]*x[j]) - 2.0/(x[j]*x[j]*yy[3][j]*yy[3][j]), 8.0*PI*yy[1][j]*yy[1][j]*(1.0/(yy[3][j]*yy[3][j])+1.0),8.0*PI*mu0);
    /***************************************************************************/
    
  for (j=2;j<=NSTEP;j++)
    {
      if(yy[6][j]>0.0) mu0 = pow(m*m/(4.0*PI),(1.0/gama-1.0))*pow(yy[6][j]/kapa,1.0/gama) + y[6][j]/(gama-1.0);
      
      TT[j]=ddp[j]+yy[1][j]*yy[1][j]*yy[3][j]*((vv[1]*vv[1])/(yy[2][j]*yy[2][j])-1.0-lambda*yy[3][j]*yy[3][j])+dp[j]*(1.0/x[j]+yy[1][j]*yy[1][j]/x[j]-yy[1][j]*yy[1][j]*x[j]*((1.0+0.5*lambda*yy[3][j]*yy[3][j])*yy[3][j]*yy[3][j]+mu0-yy[6][j]));
      
      TT1[j]=ddp[j]+yy[1][j]*yy[1][j]*yy[3][j]*((vv[1]*vv[1])/(yy[2][j]*yy[2][j])-1.0-lambda*yy[3][j]*yy[3][j])+dp[j]*(dl[j]/yy[2][j]-da[j]/yy[1][j]+2.0/x[j]);
       }
  
  // for (j=2;j<=NSTEP;j++)
  // fprintf(ifpc,"%14.8Le %14.8Le %14.8Le %14.8Le %14.8Le\n",x[j],tta[j],ttl[j],TT[j],TT1[j]);
    
  
   
  /**** Derivadas del campo y las componentes metricas extendidas*/
  
  for(j=2;j<=TailNSTEP-1;j++)pda[j]=(polary[1][j+1]-polary[1][j-1])/(tailedxx[j+1]-tailedxx[j-1]); //primera derivada de a
  for(j=2;j<=TailNSTEP-1;j++)pdl[j]=(polary[2][j+1]-polary[2][j-1])/(tailedxx[j+1]-tailedxx[j-1]); //primera derivada de alpha
  for(j=2;j<=TailNSTEP-1;j++)pdp[j]=(polary[3][j+1]-polary[3][j-1])/(tailedxx[j+1]-tailedxx[j-1]); //primera derivada de phi
  for(j=2;j<=TailNSTEP-1;j++)pddl[j]=(polary[2][j+1]-2.*polary[2][j]+polary[2][j-1])/((tailedxx[j+1]-tailedxx[j])*(tailedxx[j+1]-tailedxx[j]));//segunda derivada de alpha
  for(j=2;j<=TailNSTEP-1;j++)pddp[j]=(polary[3][j+1]-2.*polary[3][j]+polary[3][j-1])/((tailedxx[j+1]-tailedxx[j])*(tailedxx[j+1]-tailedxx[j]));//segunda derivada de phi

  /**** Terminos de las ecuaciones ****/
  for (j=2;j<=TailNSTEP-1;j++)ptt[j]=0.5*polary[1][j]*((1.0-polary[1][j]*polary[1][j])/tailedxx[j]+tailedxx[j]*(polary[1][j]*polary[1][j]*((omega*omega/(polary[2][j]*polary[2][j])+1.0+0.5*lambda*polary[3][j]*polary[3][j])*polary[3][j]*polary[3][j]+2.*polary[7][j])+pdp[j]*pdp[j]));
    
  for (j=2;j<=TailNSTEP-1;j++)pttl[j]=0.5*polary[2][j]*((polary[1][j]*polary[1][j]-1.0)/tailedxx[j]+tailedxx[j]*(polary[1][j]*polary[1][j]*((omega*omega/(polary[2][j]*polary[2][j])-1.0-0.5*lambda*polary[3][j]*polary[3][j])*polary[3][j]*polary[3][j]+2*polary[5][j])+pdp[j]*pdp[j]));

  //imprimiendo los valores de x, a, alpha, da, dalpha, ddalpha.
  for(j=2;j<=TailNSTEP-1;j++)
    fprintf(fp1,"%14.8Le %14.8Le %14.8Le %14.8Le %14.8Le  %14.8Le %14.8Le  %14.8Le\n",tailedxx[j],polary[1][j],polary[2][j],ptt[j],pttl[j],pddl[j],pda[j],pdl[j]);

  /*****calculando el redshitf z=sqrt(r*dalpha/(alpha^2(alpha-r*dalpha))) ****/
  for(j=2;j<=TailNSTEP-1;j++){
    //z_b1[j]=sqrt((tailedxx[j]*pdl[j])/(polary[2][j]*polary[2][j]*(polary[2][j]-tailedxx[j]*pdl[j])));
    z_b1[j]=sqrt(tailedxx[j]*pttl[j]/(polary[2][j]*polary[2][j]*(polary[2][j]-tailedxx[j]*pttl[j])));

    fprintf(fpz,"%14.8Le  %14.8Le\n",tailedxx[j], z_b1[j]);
  }
    
  
  
  /**** Terminos de las ecuaciones */
  
  //for (j=2;j<=TailNSTEP-1;j++)pkka[j]=pda[j]+0.5*polary[1][j]/tailedxx[j]*(polary[1][j]*polary[1][j]-1.);
  //for (j=2;j<=TailNSTEP-1;j++)pkkl[j]=pdl[j]+0.5*polary[2][j]/tailedxx[j]*(1.-polary[1][j]*polary[1][j]);
  
  //for (j=2;j<=TailNSTEP-1;j++)ptt[j]=0.5*polary[1][j]*tailedxx[j]*(polary[1][j]*polary[1][j]*((omega*omega/(polary[2][j]*polary[2][j])+1.0+0.5*lambda*polary[3][j]*polary[3][j])*polary[3][j]*polary[3][j]+2.*polary[7][j])+pdp[j]*pdp[j]);
    
  //for (j=2;j<=TailNSTEP-1;j++)pttl[j]=0.5*polary[2][j]*tailedxx[j]*(polary[1][j]*polary[1][j]*((omega*omega/(polary[2][j]*polary[2][j])-1.0-0.5*lambda*polary[3][j]*polary[3][j])*polary[3][j]*polary[3][j]+2*polary[5][j])+pdp[j]*pdp[j]);
  
  for (j=2;j<=TailNSTEP-1;j++)pTT[j] = pddp[j]-polary[1][j]*polary[1][j]*polary[3][j]*(1.0-(omega*omega)/(polary[2][j]*polary[2][j])+lambda*polary[3][j]*polary[3][j])+pdp[j]/tailedxx[j]*(1.0+polary[1][j]*polary[1][j]-tailedxx[j]*tailedxx[j]*polary[1][j]*polary[1][j]*((1.0+0.5*lambda*polary[3][j]*polary[3][j])*polary[3][j]*polary[3][j]-polary[5][j]+polary[7][j]));

    
  //pTT[j]=pddp[j]-4.0*PI*tailedxx[j]*polary[3][j]*polary[3][j]*polary[1][j]*polary[1][j]*pdp[j]+pdp[j]/tailedxx[j]-pdp[j]*(polary[3][j]*polary[3][j])/tailedxx[j]+4.0*PI*polary[3][j]*polary[3][j]*tailedxx[j]*(polary[7][j]-polary[5][j])+polary[3][j]*polary[3][j]*(omega*omega/(polary[4][j]*polary[4][j])-1.)*polary[1][j];
  
//  for(j=2;j<=TailNSTEP-1;j++)
//    Eni[j] = 2.0*pda[j]/(tailedxx[j]*polary[3][j]*polary[3][j]*polary[3][j]) +1.0/(tailedxx[j]*tailedxx[j]) - 1.0/(tailedxx[j]*tailedxx[j]*polary[3][j]*polary[3][j]) - 4.0*PI*((omega*omega/(polary[4][j]*polary[4][j])+1.0)*polary[1][j]*polary[1][j] + polary[2][j]*polary[2][j]/(polary[3][j]*polary[3][j]) + 2.0*polary[7][j]);
      
/**** Impresion en archivos*/

  /*  ifpc="Aconstraint.dat*/
//  for (j=2;j<=NSTEP;j++)
//    fprintf(ifpc,"%14.8Le %14.8Le %14.8Le %14.8Le %14.8Le %14.8Le %14.8Le %14.8Le %14.8Le\n",xx[j],TT[j],kka[j]-tt[j],kkl[j]-ttl[j],kka[j],tt[j],kkl[j],ttl[j],Enp[j]);


//imprimiendo las derivadas diferencias finitas y ecuacion.
  
  /*  ifpcp =AconstraintP.dat*/
  //for (j=2;j<=TailNSTEP-1;j++)
  //fprintf(ifpcp,"%14.8Le %14.8Le %14.8Le %14.8Le %14.8Le %14.8Le %14.8Le %14.8Le\n",tailedxx[j],pTT[j],pkka[j]-ptt[j],pkkl[j]-pttl[j],pkka[j],ptt[j],pkkl[j],pttl[j]);

// for (j=2;j<=TailNSTEP-1;j++)
//   fprintf(ifpc3,"%14.8Le %14.8Le %14.8Le %14.8Le %14.8Le\n",tailedxx[j],Eni[j],4.0*pda[j]/(tailedxx[j]*polary[3][j]*polary[3][j]*polary[3][j]) +2.0/(tailedxx[j]*tailedxx[j]) - 2.0/(tailedxx[j]*tailedxx[j]*polary[3][j]*polary[3][j]), 8.0*PI*polary[1][j]*polary[1][j]*(1.0/(polary[3][j]*polary[3][j]) + 1.0), 8.0*PI*polary[7][j]);
   

//  fclose(ifpc);
//  fclose(ifpcp);

//  free_vector(da,1,NSTEP+1);
//  free_vector(dl,1,NSTEP+1);
//  free_vector(dp,1,NSTEP+1);  
//  free_vector(kka,1,NSTEP+1);
//  free_vector(kkl,1,NSTEP+1);
//  free_vector(tt,1,NSTEP+1);  
//  free_vector(ttl,1,NSTEP+1);
//  free_vector(TT,1,NSTEP+1);
//  free_vector(pda,1,TailNSTEP);
//  free_vector(pdl,1,TailNSTEP);
//  free_vector(pdp,1,TailNSTEP);  
//  free_vector(pkka,1,TailNSTEP);
//  free_vector(pkkl,1,TailNSTEP);
//  free_vector(ptt,1,TailNSTEP);  
//  free_vector(pttl,1,TailNSTEP);
//  free_vector(pTT,1,TailNSTEP);

  return 0;
}


/*********************** */

int printfiles(void)
{
  int j,i;
  long double pii,*d_alpha,*d_a,*d_p, *d2_phi, *d2_alpha, *d22_alpha,*red_z,*d_alphadf,*d2_alphadf;
  FILE *fpnon,*ifm,*ifp2,*fp3;
    
    //printf("entro a printfile\n");
    
  pii=acos(-1.0);

  d_alpha = vector(0,TailNSTEP);
  d_a = vector(0,TailNSTEP);
  d_p = vector(0,TailNSTEP);
  d2_phi = vector(0,TailNSTEP);
  d2_alpha = vector(0, TailNSTEP);
  d22_alpha = vector(0, TailNSTEP);
  red_z = vector(0, TailNSTEP);
  d_alphadf = vector(0,TailNSTEP);
  d2_alphadf = vector(0,TailNSTEP);
  
  
    //printf("defino los archivos para imprimir\n");
    
  ifp2 = fopen("perfiles_rho0_001190.dat","w");
  //ifm = fopen("datos.dat","w");
 //fpar=fopen("tablaparbosones.dat","a");
  //fpnon=fopen("noparticulas.dat","w");
    
   
  /**ifm = fopen("datos.dat","w");*/
  //for (j=1; j<=NSTEP ; j+=1)
  //fprintf(ifm,"%14.8Le %14.8Le %14.8Le %14.8Le %14.8Le %14.8Le %14.8Le\n",xxmin[j],ymin[1][j],ymin[2][j],ymin[3][j],ymin[4][j],ymin[5][j],ymin[6][j]);
 

  /** ifp2 = polar.dat */
  //fprintf(ifp2,"   %cx_i\t\t %ca\t\t%calpha\t\t%caphi\t\t%cphip\n",'#','#','#','#','#','#','#','#');

  //definiendo la derivada de la funcion metrica alpha, a
  //polary[2][0]=polary[2][1];

    //printf("comienzo a imprimir datos\n");
    
     //imprimiendo x, a, alpha, phi, phi', p, rho, mu en fp2, x, a, alpha, a', alpha' en fpe
  for (j=2;j<=TailNSTEP-1;j++)
    {
      fprintf(ifp2,"%14.8Le %14.8Le %14.8Le %14.8Le %14.8Le %14.8Le %14.8Le %14.8Le \n",tailedxx[j],polary[1][j],polary[2][j],polary[3][j],polary[4][j],polary[5][j],polary[6][j],polary[7][j]);
    } 
     
   // printf("termino de imprimir en ifp2\n");
  /*No de particulas*/
  //for(j=1;j<=NSTEP;j++)
  // fprintf(fpnon,"%14.8Le %14.8Le %14.8Le\n",tailedxx[j],y[7][j+1],y[8][j+1]);
 
  
    //printf("cierro archivos\n");
 
  fclose(ifp2);
  //fclose(ifm);
  //fclose(fpar);
  //fclose(fpnon);

  // printf("salimos de prinftile?\n");
  return 0;
}

int main(void)
{
    int i,j,k,m;
    int check;
    long double *v,dex,xf, Omega0;
    long double f1, f1min,f2,f2min,f3,f3min;
    long double mpl;
    FILE *ifq, *ifpar;
    
    
    int jt;
    

    rho0= 0.0;
    
    for(m=0;m<=200;m++)
    {
        phi0=m*0.001;
    
        printf("m=%d\n",m);
            //definición de parametros iniciales
            x2 = 1.000005;
            dex = 0.1;
            xf = 150.000005;
            Omega0 = 1.0;
            atms = 1.0e-12;
            
            //Parametros de autointeraccion y politroica
            lambda = 50.0;
            kapa = 5.6e04;
            gama = 2.8;
            
            //datos para las unidades femionicas
            mpl = 2.1779e-08; //masa de Planck
            mbf = 1.0e-12; //masa del boson en unidades fisicas (eV)
            epsi = 9.196e37; //valor del parametro epsilon para las unidades fermionicas
            emu = 1.0; //producto del parametro epsilon y la masa de boson en eV
            mb = mbf/1.223533e28; //masa numerica del boson en términos de mbf y m_pl en eV.
    
        
        
        nvar = 8;
        R_99 = 0.0;
        R_starb = 0.0;
        NoPartB = 0.0;
        R_starf = 0.0;
        NoPartF = 0.0;
        
        Mass = 0.0;
        M_tail = 0.0;
        NoPart_tail = 0.0;
        BindingE_tail = 0.0;
        phi_tail = 0.0;
        R_tail = 0.0;
        
        omega = 0.0;
        cct = 0.0;
        
        j_tail = 0;
        x1=0.000005;
        h=0.0;
        
        ifpar= fopen("tablabosones_L_EM.dat","a");
        
        v = vector(1,N2);
        vout = vector(1,nvar);
        xx = vector(1,NSTEP+1);
        y = matrix (1,nvar,1,NSTEP+1);
        
        vmin = vector(1,N2);
        xxmin = vector(1,NSTEP+1);
        ymin = matrix (1,nvar,1,NSTEP+1);
        
        f2min=10.0;
        
        v[1] = Omega0;
        
        while (x2 <= xf){
            printf("x2=%14.8Le m=%d\n",x2,m);
            newt(v,N2,&check,shoot);
            if (check)printf("shoot failed, bad initial guess \n");
            characquantities(y,xx,v);
            
            f2=((y[1][NSTEP+1]-y[1][NSTEP-1])/(xx[NSTEP+1]-xx[NSTEP-1]))*y[2][NSTEP+1]+((y[2][NSTEP+1]-y[2][NSTEP-1])/(xx[NSTEP+1]-xx[NSTEP-1]))*y[1][NSTEP+1];
            
            printf("f2= %14.8Le\n",f2);
            
            if(fabsl(f2)<=f2min){
                for(j=1; j<=NSTEP+1; j++)xxmin[j]=xx[j];
                for(i=1; i<=nvar; i++){
                    for(j=1; j<=NSTEP+1; j++)ymin[i][j]=y[i][j];
                }
                vmin[1]=v[1];
                hmin=h;
                f2min=fabsl(f2);
                printf("aqui calculo hmin=%14.8Le\n",hmin);
            }
            printf("v[1]= %14.8Le \n",v[1]);
            x2 +=dex;
            printf("------------------------->1 \n");
        }
        printf("-------------------------> 2\n");
        characquantities(ymin,xxmin,vmin);
        j_tail=NSTEP+1;
        
        TailNSTEP=(int) (300.0/hmin);
        printf("TailNSTEP= %d hmin=%14.8Le\n", TailNSTEP, hmin);
        
        
        tailedxx = vector(1,TailNSTEP);
        tailedy = matrix (1,7,1,TailNSTEP);
        polary = matrix (1,7,1,TailNSTEP);
        
        printf("entramos a la funcion tailer\n");
        tailer(ymin,xxmin,vmin,hmin);
        
        //constraint(ymin,xxmin,vmin);
        
        fprintf(ifpar,"%14.8Le %14.8Le %14.8Le %14.8Le %14.8Le %14.8Le %14.8Le %14.8Le %14.8Le %14.8Le %14.8Le %14.8Le %14.8Le \n",rho0,phi0,M_tail,R_99,R_starb,R_starf,NoPartB,NoPartF,omega,lambda,kapa,gama, emu);
        
        printfiles();
        
        
        printf("R_starb=%14.8Le\n",R_starb);
        printf("R_starf=%14.8Le\n",R_starf);
        printf("R_99=%14.8Le\n",R_99);
        printf("NoB=%14.8Le\n",NoPartB);
        printf("NoF=%14.8Le\n",NoPartF);
        printf("omega=%14.8Le\n",omega);
        
        
        
        free_vector(v,1,N2);
        free_vector(vout,1,nvar);
        free_vector(xx,1,NSTEP+1);
        free_vector(tailedxx,1,TailNSTEP);
        free_matrix(y,1,nvar,1,NSTEP+1);
        free_matrix(tailedy,1,7,1,TailNSTEP);
        free_matrix(polary,1,7,1,TailNSTEP);
        free_vector(vmin,1,N2);
        free_vector(xxmin,1,NSTEP+1);
        free_matrix(ymin,1,nvar,1,NSTEP+1);
        
        fclose(ifpar);
        
        printf("**********************************************************\n");
        printf("----------------------------------------------------------\n");
        
    }//se cierra el ciclo para rho
    
    
    printf("llego hasta el final?\n");
    return 0;
}


