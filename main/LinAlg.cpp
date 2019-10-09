#include "base.cpp"

namespace LinAlg{
const int maxn=1010,maxm=1010;
double a[maxn][maxm],b[maxn][maxn],ans[maxn];
int n,m;
const int eps=1e-7;
//require m=n+1 and only one solution
bool gauss_solve(){
	for (int i=0;i<n;i++){
		int maxl=i;
		for (int j=i+1;j<n;j++)
			if (fabs(a[j][i])>fabs(a[maxl][i])) maxl=j;
		if (maxl!=i) swap(a[i],a[maxl]);
		if (fabs(a[i][i])<eps) return 0; //no solution or infinity solution 
		for (int j=i+1;j<n;j++){
			double r=a[j][i]/a[i][i];
			for (int k=i;k<m;k++)
				a[j][k]-=r*a[i][k];
		}
		double r=a[i][i];
		for (int k=i;k<m;k++) a[i][k]/=r;
	}
	for (int i=n-1;i>=0;i--){
		ans[i]=a[i][n];
		for (int j=i+1;j<n;j++)
			ans[i]-=a[i][j]*ans[j];
	}
	return 1;
}
//n*n matrix
bool matinv(){
	memset(b,0,sizeof(b));
	for (int i=0;i<n;i++) b[i][i]=1;	
	for (int i=0;i<n;i++){
		int maxl=i;
		for (int j=i+1;j<n;j++)
			if (fabs(a[j][i])>fabs(a[maxl][i])) maxl=j;
		if (i!=maxl) swap(a[i],a[maxl]),swap(b[i],b[maxl]);
		if (fabs(a[i][i])<eps) return 0; //No trivil
		double r=a[i][i];
		for (int k=0;k<n;k++) a[i][k]/=r,b[i][k]/=r; //k start from 0
		for (int j=i+1;j<n;j++){
			double r=a[j][i]/a[i][i];
			for (int k=0;k<n;k++) //k start from 0
				a[j][k]-=r*a[i][k], b[j][k]-=r*b[i][k];
		}
	}
	return 1;
}
double det(){
	double ans=1;
	for (int i=0;i<n;i++){
		int maxl=i;
		for (int j=i+1;j<n;j++)
			if (fabs(a[j][i])>fabs(a[maxl][i])) maxl=j;
		if (i!=maxl) swap(a[i],a[maxl]),ans=-ans;
		if (fabs(a[i][i])<eps) return 0;
		for (int j=i+1;j<n;j++){
			double r=a[j][i]/a[i][i];
			for (int k=i;k<n;k++)
				a[j][k]-=r*a[i][k];
		}
	}
	for (int i=0;i<n;i++) ans*=a[i][i];
	return ans;
}
int matrank(){
	int l=0; //real line
	for (int i=0;i<m;i++){ //i: col start pos
		int maxl=l;
		for (int j=l+1;j<n;j++)
			if (fabs(a[j][i])>fabs(a[maxl][i])) maxl=j;
		if (l!=maxl) swap(a[l],a[maxl]);
		if (fabs(a[l][i])<eps) continue;
		for (int j=l+1;j<n;j++){
			double r=a[j][i]/a[l][i];
			for (int k=i;k<m;k++)
				a[j][k]-=r*a[i][k];
		}
		l++;
	}
	return l;
}
const ll p=19260817; //const is faster than normal variable
//int det with mod
//used by Matrix-Tree theorem
//M-T theo: a[i][i]=deg i, a[i][j]=-cnt(i->j), n=|vertex|-1
ll detint(ll **a){
	ll ans=1;
	for (int i=0;i<n;i++) for (int j=0;j<n;j++) if (a[i][j]<0) a[i][j]+=p;
	for (int i=0;i<n;i++){
		int maxl=i;
		for (int j=i;j<n;j++)
			if (a[j][i]) {maxl=j;break;}
		if (i!=maxl) swap(a[i],a[maxl]), ans=P-ans;
		if (a[i][i]==0) return 0;
		ans=ans*a[i][i]%p;   //[i] Here update ans before set a[i][i] to 1
		int v=inv(a[i][i],p);
		for (int j=i;j<m;j++) a[i][j]=a[i][j]*v%p;
		for (int j=i+1;j<n;j++){
			ll r1=a[j][i];
			if (!r1) continue;
			for (int k=i;k<n;k++)
				a[j][k]=(a[j][k]-r1*a[i][k]%p+p)%p;
		}
	}
	return ans;
}
//matinv with mod
//require m=2*n, result is a[i][(0..n-1)+n]
bool matinv_int(ll **a){
	m=2*n;
	//a[i][(0..n-1)+n]=0; //set to 0 when necessary
	for (int i=0;i<n;i++) a[i][i+n]=1;	
	for (int i=0;i<n;i++){
		int maxl=i;
		for (int j=i;j<n;j++)
			if (a[j][i]) {maxl=j;break;}
		if (i!=maxl) swap(a[i],a[maxl]);
		if (a[i][i]==0) return 0;
		int v=inv(a[i][i],p);
		for (int j=i;j<m;j++) a[i][j]=a[i][j]*v%p;
		for (int j=0;j<n;j++){
			if (!a[j][i] || j==i) continue;
			ll r1=a[j][i];
			for (int k=i;k<m;k++)
				a[j][k]=(a[j][k]-r1*a[i][k]%p+p)%p;
		}
	}
	return 1;
}
#ifdef NO_COMPILE
int n,m,p;
//solve linear equ in module p
//not require m=n+1, get a possible solution ans[0..m-1)
bool gauss_solve_int(){  //similar as matrank
	int l=0; //real line
	for (int i=0;i<m;i++){ //i: col start pos
		int maxl=l;
		for (int j=l;j<n;j++)
			if (a[j][i]) {maxl=j;break;}
		if (maxl!=l) swap(a[l],a[maxl]);
		if (!a[l][i]) continue; //next col
		int v=inv(a[l][i],p);
		for (int j=i;j<m;j++) a[l][j]=a[l][j]*v%p;
		for (int j=l+1;j<n;j++){
			if (!a[j][i]) continue;
			int r1=a[j][i];
			for (int k=i;k<m;k++)
				a[j][k]=(a[j][k]-r1*a[l][k]%p+p)%p;
		}
		l++;
	} //now l is rank of matrix
	int last=m-1,cur;
	for (int i=l-1;i>=0;i--){
		for (cur=0;cur<m-1 && !a[i][cur];cur++); //first no zero column
		int t=a[i][m-1]; 
		for (int j=last;j<m-1;j++) t=(t-a[i][j]*ans[j]%p+p)%p;
		for (last--;last>cur;last--) //any solution, set to 0
			ans[last]=0; //,t=(t-a[i][j]*ans[last]%p+p)%p; when ans[last] is not 0
		if (cur==m-1 && t) return 0; //no solution
		ans[cur]=t; //a[i][cur]=1, so ans[cur]=t
		last=cur;
	}
	return 1;
}
#endif
}

