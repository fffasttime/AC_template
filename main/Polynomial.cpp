#include "base.cpp"

namespace Polynomial{
//Attention: n indicates number of coeffs, so deg F[x]=n-1, not n
namespace FFT
{
typedef complex<double> cd;
const int maxl=(1<<20)+1;
const double pi=3.14159265358979;
int rev[maxl];
void get_rev(int bit){
	for (int i=0;i<(1<<bit);i++)
		rev[i]=(rev[i>>1]>>1)|((i&1)<<(bit-1));
}
void fft(cd a[], int n, int dft){
	for(int i=0;i<n;i++) if(i<rev[i]) swap(a[i],a[rev[i]]);
	for (int s=1;s<n;s<<=1){
		cd wn=exp(cd(0,pi*dft/s));
		for (int j=0;j<n;j+=s<<1){
			cd wnk(1,0);
			for (int k=j;k<j+s;k++){
				cd x=a[k],y=wnk*a[k+s];
				a[k]=x+y;
				a[k+s]=x-y;
				wnk*=wn;
			}
		}
	}
	if (dft==-1) for (int i=0;i<n;i++) a[i]/=n;
}
ll G=3,P=998244353;
void ntt(ll *a, int n, int dft){
	for(int i=0;i<n;i++) if(i<rev[i]) swap(a[i],a[rev[i]]);
	for (int s=1;s<n;s<<=1){
		ll wn=qpow(G,dft==1?(P-1)/s/2:P-1-(P-1)/s/2,P);
		for (int j=0;j<n;j+=s<<1){
			ll wnk=1;
			for (int k=j;k<j+s;k++){
				ll x=a[k],y=wnk*a[k+s]%P;
				a[k]=(x+y)%P; //merge
				a[k+s]=(x-y+P)%P;
				wnk=wnk*wn%P;
			}
		}
	}
	if (dft==-1) {
		ll inv=qpow(n,P-2,P);
		for (int i=0;i<n;i++) a[i]=a[i]*inv%P;
	}
}
void conv(cd *fa, cd *fb, int s, cd *ret){
	static cd a[maxl],b[maxl];
	memcpy(a,fa,sizeof(cd)*s); memcpy(b,fb,sizeof(cd)*s);
	fft(a,s,1); fft(b,s,1);
	for (int i=0;i<s;i++) a[i]*=b[i];
	fft(a,s,-1);
	memcpy(ret,a,sizeof(cd)*s);
}
void conv(ll *fa, ll *fb, int s, ll *ret){
	static ll a[maxl],b[maxl];
	memcpy(a,fa,sizeof(ll)*s); memcpy(b,fb,sizeof(ll)*s);
	ntt(a,s,1); ntt(b,s,1);
	for (int i=0;i<s;i++) a[i]*=b[i];
	ntt(a,s,-1);
	memcpy(ret,a,sizeof(ll)*s);
}
int ans[maxl],_;
char s1[100010],s2[100010];
//fast mul
void base10_mul(){
	static cd a[maxl],b[maxl];
	scanf("%s%s",s1,s2);
	int l1=strlen(s1),l2=strlen(s2);
	int s=2,bit=1;
	for (bit=1;(1<<bit)<l1+l2-1;bit++)s<<=1;
	for (int i=0;i<l1;i++) a[i]=s1[l1-i-1]-'0';
	for (int i=0;i<l2;i++) b[i]=s2[l2-i-1]-'0';
	conv(a,b,s,a);
	for (int i=0;i<s;i++) cout<<a[i]<<' '; cout<<'\n';
	for (int i=0;i<s;i++){
		ans[i]+=a[i].real();
		ans[i+1]+=ans[i]/10;
		ans[i]%=10;
	}
	int i;
	for (i=l1+l2;!ans[i]&&i>=0;i--);
	if (i==-1) printf("0");
	for (;i>=0;i--) printf("%d",ans[i]);
	putchar('\n');
}

//C[x]=A[x]*B[x], convolve only
void poly_mul(ll *A, ll *B, int n, ll *C){
	int s=2,bit=1;
    for (bit=1;(1<<bit)<n<<1;bit++)s<<=1; //size n*2
    fill(A+n,A+s,0); fill(B+n,B+s,0);
    get_rev(bit);
    conv(A,B,s,C);
}
void poly_add(ll *A, ll *B, int n, ll *C){
	for (int i=0;i<n;i++) 
		C[i]=(A[i]+B[i])%P;
}
void poly_sub(ll *A, ll *B, int n, ll *C){
	for (int i=0;i<n;i++) 
		C[i]=(A[i]-B[i]+P)%P;
}

#ifdef NO_COMPILE  //3 module ntt version
const ll p=1000000007,P1=1004535809,P2=998244353,P3=469762049;
void poly_mul(ll *A, ll *B, int n, ll *C){
	static ll res[3][maxl];
	int s=2,bit=1;
    for (bit=1;(1<<bit)<n<<1;bit++)s<<=1; //size n*2
    get_rev(bit);
    conv<P1>(A,B,n,res[0]);
    conv<P2>(A,B,n,res[1]);
    conv<P3>(A,B,n,res[2]);
    ll M=P1*P2;
    for (int i=0;i<s;i++){ //merge
    	ll A=(qmul(res[0][i]*P2%M,inv(P2%P1,P1),M)+
			qmul(res[1][i]*P1%M,inv(P1%P2,P2),M))%M;
		ll K=(res[2][i]-A%P3+P3)*inv(M%P3,P3)%P3;
		C[i]=(qmul(K%p,M%p,p)+A)%p;
    }
}
//input A[x], A[x]*B[x]=1 (mod x^n)
void poly_inv(ll *A, ll *B, int n){
    if (n==1) {B[0]=qpow(A[0],p-2,p); return;} //constant element
    poly_inv(A,B,n+1>>1); //divide
    int s=2,bit=1;
    for (bit=1;s<n<<1;bit++)s<<=1; //size n*2
    static ll ta[maxl];//A(x)((2-B(x)A(x))B(x))=1(mod x^2)
    poly_mul(A,B,n,ta);
    for (int i=1;i<s;i++) ta[i]=p-ta[i];
    ta[0]=(2+p-ta[0])%p;
    poly_mul(ta,B,n,B);
    //for (int i=0;i<s;i++)cout<<B[i]<<' '; cout<<'\n';
}
#endif

//input A[x], A[x]*B[x]=1 (mod x^n)
void poly_inv(ll *A, ll *B, int n){
	if (n==1) {B[0]=qpow(A[0],P-2,P); return;} //constant element
	poly_inv(A,B,n+1>>1); //divide
    int s=2,bit=1;
    for (bit=1;(1<<bit)<n<<1;bit++)s<<=1; //size n*2
    get_rev(bit);
    static ll ta[maxl];
    copy(A,A+n,ta); fill(ta+n,ta+s,0);
	ntt(ta,s,1); ntt(B,s,1);
    for (int i=0;i<s;i++) //A(x)(2B(x)-B(x)^2A(x))=1(mod x^2)
    	B[i]=(2-ta[i]*B[i]%P+P)%P*B[i]%P;  
    ntt(B,s,-1); fill(B+n,B+s,0);
    //for (int i=0;i<s;i++)cout<<B[i]<<' '; cout<<'\n';
}

//A[x]=Q[x]*B[x]+R[x], (deg R[x]<deg B[x], deg Q[x]<n-m+1)
void poly_div(ll *A, ll *B, int n, int m, ll *Q, ll *R){
	//conclusion: Qr[x] = Ar[x] * poly_inv(Br[x]) (mod x^(n-m+1))
	static ll X[maxl], Y[maxl], tmp[maxl];
	memset(X,0,sizeof X); memset(Y,0,sizeof Y); memset(tmp,0,sizeof tmp);
	copy(A,A+n,X); copy(B,B+m,Y);
	reverse(X,X+n); reverse(Y,Y+m);
	poly_inv(Y,tmp,n-m+1); 
	poly_mul(X,tmp,n-m+1,Q);
	fill(Q+n-m+1,Q+n,0), reverse(Q,Q+n-m+1);
    copy(A,A+n,X), copy(B,B+m,Y);
    poly_mul(Y,Q,n,tmp), poly_sub(X,tmp,n,R);
	fill(R+m-1,R+n,0);
}

//B[x]=intergrate A[x]dx,  deg B[x] = deg A[x] + 1
void poly_int(ll *A, ll *B, ll n){
	B[0]=0; //constant C
	for (int i=1;i<=n;i++)
		B[i]=A[i-1]*qpow(i,P-2,P)%P;
}
//B[x]=A'[x],  deg B[x] = deg A[x] - 1
void poly_deriv(ll *A, ll *B, ll n){
	B[n-1]=0;
	for (int i=0;i<n-1;i++)
		B[i]=A[i+1]*(i+1)%P;
}

//B[x]=ln A[x]=int(B'[x])=int(A'[x]/A[x])  (mod x^n)
void poly_ln(ll *A, ll *B, ll n){
	static ll X[maxl], Y[maxl], tmp[maxl];
	memset(X,0,sizeof X); memset(Y,0,sizeof Y); memset(tmp,0,sizeof tmp);
	copy(A,A+n,X); poly_deriv(X,Y,n); 
	poly_inv(X,tmp,n); copy(tmp,tmp+n,X); 
	poly_mul(X,Y,n,tmp); poly_int(tmp,B,n);
}

//Fnew[x]=Fb[x](1-ln(Fb[x])+A[x]), O(nlogn)
void poly_exp(ll *A, ll *B, int n) {
    if (n==1) {B[0]=1;return;}
    static ll tmp[maxl]; memset(tmp,0,sizeof tmp);
    poly_exp(A,B,n+1>>1);fill(B+(n+1>>1),B+n,0);
    poly_ln(B,tmp,n); poly_sub(A,tmp,n,tmp);
    poly_mul(tmp,B,n,tmp); poly_add(B,tmp,n,B);
}

//B[x]=sqrt(A[x])=exp(0.5*ln(A[x]))
void poly_sqrt(ll *A, ll *B, int n) {
    static ll tmp[maxl]; memset(tmp,0,sizeof tmp);
	poly_ln(A,tmp,n);
	for (int i=0;i<n;i++) tmp[i]=tmp[i]*qpow(2,P-2,P)%P;
    poly_exp(tmp,B,n);
}

//deleted, please use poly_mul(3 module version) instead
const ll P1=1004535809,P2=998244353,P3=469762049;
ll res[3][maxl];
//conv a sequence with mod p, while p<P1*P2*P3
void conv_mod(){
	static ll a[maxl],b[maxl];
	int l1,l2; ll p;
    rd(l1); rd(l2); l1++; l2++;
    int s=2,bit=1;
    for (bit=1;(1<<bit)<l1+l2-1;bit++)s<<=1;
	get_rev(bit);
    int r; rd(r); p=r;
    for (int i=0;i<l1;i++) rd(r),a[i]=r;
    for (int i=0;i<l2;i++) rd(r),b[i]=r;
    G=3,P=P1; conv(a,b,s,res[0]);
    G=3,P=P2; conv(a,b,s,res[1]);
    G=3,P=P3; conv(a,b,s,res[2]);
    ll M=P1*P2;
    for (int i=0;i<l1+l2-1;i++){ //merge
    	//printf("%lld %lld %lld \n",res[0][i],res[1][i],res[2][i]);
    	ll A=(qmul(res[0][i]*P2%M,inv(P2%P1,P1),M)+
			qmul(res[1][i]*P1%M,inv(P1%P2,P2),M))%M;
		ll K=(res[2][i]-A%P3+P3)*inv(M%P3,P3)%P3;
		//cout<<A<<' '<<K<<' ';
		printf("%lld ", (qmul(K%p,M%p,p)+A)%p);
    }
}
} //namespace FFT

const int maxn=2010;
ll x[maxn],y[maxn];
int n;
//O(n^2) get single point value
//if xi between 1~n, we can optimize it to O(n)
//if xi not in 1~n, we can still preprocess PIj (ki-x[j]+p)%p, 
//  then get multi point value in O(max(n^2,nm))
ll LangrangeInter(ll k, ll p){
    ll sum=0;
    for (int i=0;i<n;i++){
        ll s0=1;
        for (int j=0;j<n;j++)
            if (i!=j) s0=s0*(x[i]-x[j]+p)%p;
        s0=qpow(s0,p-2,p);
        for (int j=0;j<n;j++)
            if (i!=j) s0=s0*(k-x[j]+p)%p;
        sum=(sum+y[i]*s0)%p;
    }
	return sum;
}

namespace FWT{
int N,P,inv2;
const int maxl=1<<18+1;
void fwt_or(int *a,int opt){
    for(int i=1;i<N;i<<=1)
        for(int p=i<<1,j=0;j<N;j+=p)
            for(int k=0;k<i;++k)
                if(opt==1) a[i+j+k]=(a[j+k]+a[i+j+k])%P;
                else a[i+j+k]=(a[i+j+k]+P-a[j+k])%P;
}
void fwt_and(int *a,int opt){
    for(int i=1;i<N;i<<=1)
        for(int p=i<<1,j=0;j<N;j+=p)
            for(int k=0;k<i;++k)
                if(opt==1) a[j+k]=(a[j+k]+a[i+j+k])%P;
                else a[j+k]=(a[j+k]+P-a[i+j+k])%P;
}
void fwt_xor(int *a,int opt){
    for(int i=1;i<N;i<<=1)
        for(int p=i<<1,j=0;j<N;j+=p)
            for(int k=0;k<i;++k){
                int X=a[j+k],Y=a[i+j+k];
                a[j+k]=(X+Y)%P,a[i+j+k]=(X+P-Y)%P;
                if(opt==-1) a[j+k]=(ll)a[j+k]*inv2%P,a[i+j+k]=(ll)a[i+j+k]*inv2%P;
            }
}
void bit_conv(int *fa, int *fb, int *c){
	static int a[maxl],b[maxl];
	memcpy(a,fa,sizeof(int)*N); memcpy(b,fb,sizeof(int)*N);
	fwt_xor(a,1); fwt_xor(b,1);
	for (int i=0;i<N;i++) a[i]=a[i]*b[i]%P;
	fwt_xor(a,-1);
	memcpy(c,a,sizeof(int)*N);
}
}
}

