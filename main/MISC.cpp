#include "base.cpp"

namespace FasterTrick{
	
const int P=1e9+7;
//if (x<0) x+=p;
//example: r=(x-y+P)%P  -->  r=reduce(x-y)
//         r=(x+y)%P    -->  r=reduce(x+y-P)
inline int reduce_p(int x){ //[!] require signed value
	return x+(x>>31)&P;
}

ui bit_rev(ui v){
	v = ((v >> 1) & 0x55555555) | ((v & 0x55555555) << 1);
	v = ((v >> 2) & 0x33333333) | ((v & 0x33333333) << 2);
	v = ((v >> 4) & 0x0F0F0F0F) | ((v & 0x0F0F0F0F) << 4);
	v = ((v >> 8) & 0x00FF00FF) | ((v & 0x00FF00FF) << 8);
	v = ( v >> 16             ) | ( v               << 16);
	return v;
}
typedef unsigned long long ull;
ull bit_rev(ull v){
	v = ((v >> 1) & 0x5555555555555555) | ((v & 0x5555555555555555) << 1);
	v = ((v >> 2) & 0x3333333333333333) | ((v & 0x3333333333333333) << 2);
	v = ((v >> 4) & 0x0F0F0F0F0F0F0F0F) | ((v & 0x0F0F0F0F0F0F0F0F) << 4);
	v = ((v >> 8) & 0x00FF00FF00FF00FF) | ((v & 0x00FF00FF00FF00FF) << 8);
	v = ((v >> 16)& 0x0000FFFF0000FFFF) | ((v & 0x0000FFFF0000FFFF) << 16);
	v = ( v >> 32 ) | ( v << 32 );
	return v;
}

}

namespace DateTime{

int gettime(int h, int m, int s){
	return h*3600+m*60+s;
}

bool isleapyear(int y){
	//if (y<0) return isleapyear(-y-1);
	//if (y%3200==0) return y%172800==0; 
	return y%4==0 && y%100 || y%400==0;
}

int mm[13]={0,31,28,31,30,31,30,31,31,30,31,30,31};
//get day diff from 0000/01/01 (BC 0001y), but require y>0
int getday(int y, int m, int d){
	if (m<3) y--,m+=12;
	return (d+30*m+3*(m+1)/5+y*365+y/4-y/100+y/400)-33;
}
//inverse function of getday()
void getdate(int d0, int &y, int &m, int &d){
	int y1=(d0)/146097;
	int y2=(d0-1-y1*146097)/36524;
	int y3=(d0-1-y1*146097-y2*36524)/1461;
	y=y1*400+y2*100+y3*4+(d0-1-y1*146097-y2*36524-y3*1461)/365;
	d=d0-y*365-(y-1)/4+(y-1)/100-(y-1)/400; m=1;
	if (y%4==0&&y%100||y%400==0) mm[2]++;
	while (d-mm[m]>0) d-=mm[m++];
	if (y%4==0&&y%100||y%400==0) mm[2]--;
}

//get week by date,1 for Monday
//[!] Because 1582/10/05~1582/10/14 is not existed
// the formula is correct after that day
int getweek(int y, int m, int d){
	if (m<3) y--,m+=12;
	return (d+2*m+3*(m+1)/5+y+y/4-y/100+y/400+1)%7;
}

}

namespace scannerLine{
const int maxn=100010;
struct Line{
	double l,r,h; int c;
	bool operator<(const Line &v) const{
		return h<v.h;
	}
}li[maxn];
int lic;

#define lc u+u+1
#define rc u+u+2
double len[maxn<<2]; int cnt[maxn<<2];
double x[maxn<<1]; int xc;

void calc(int u, int l, int r){
	if (cnt[u])
		len[u]=x[r]-x[l];
	else if (l==r-1)
		len[u]=0;
	else
		len[u]=len[lc]+len[rc];
}
void add(int u, int l, int r, int cl, int cr, int c){
	if (cl<=l && cr>=r){
		cnt[u]+=c;
		calc(u,l,r);
		return;
	}
	int mid=l+r>>1;
	if (cl<mid) add(lc,l,mid,cl,cr,c);
	if (cr>mid) add(rc,mid,r,cl,cr,c);
	calc(u,l,r);
}

double x0[maxn],y0[maxn],x1[maxn],y1[maxn];
void rectInt(int n){
	xc=lic=0;
	memset(len,0,sizeof(len));
	memset(cnt,0,sizeof(cnt));
	for (int i=0;i<n;i++){
		double x1,y1,x2,y2;
		scanf("%lf%lf%lf%lf",&x1,&y1,&x2,&y2);
		x[xc++]=x1; x[xc++]=x2;
		li[lic++]=(Line){x1,x2,y1,1};
		li[lic++]=(Line){x1,x2,y2,-1};
	}
	sort(li,li+lic);
	sort(x,x+xc);
	double ans=0,last=0;
	for (int i=0;i<lic;i++){
		int l=lower_bound(x,x+xc,li[i].l)-x;
		int r=lower_bound(x,x+xc,li[i].r)-x;
		add(0,0,xc,l,r,li[i].c);
		ans+=len[0]*(li[i+1].h-li[i].h);
		//sum of lenth on sx
		//ans+=fabs(len[0]-last); last=len[0];
	}
	printf("%.2f\n",ans);
}
#undef lc
#undef rc
}
}

//O(nlogn)
namespace HFMT{
const int maxn=30;

//finally tn is the root of tree
int a[maxn],ch[maxn<<1][2],n,tn; //idx from 1..n
int sum[maxn<<1]; //not very necessary
//input  a[1..n]:frequency of each character, n: |character|
//result ch[maxn<<1][2], the path to leaf node is the encoding of input char
void build(){
	priority_queue<PII> qu;
	for (int i=1;i<=n;i++) qu.emplace(-a[i],i),sum[i]=a[i];
	tn=n;
	while (qu.size()>1){
		int x1=qu.top().first, p1=qu.top().second;
		qu.pop();
		int x2=qu.top().first, p2=qu.top().second;
		qu.pop();
		ch[++tn][0]=p1; ch[tn][1]=p2;
		sum[tn]=-x1-x2;
		qu.emplace(x1+x2, tn);
	}
}
int len[maxn];
//dfs: debug, and label lenth of encode after
void dfs(int u=tn, int deep=0){
	if (!u) return;
	if (u<=n) len[u]=deep;
	dfs(ch[u][1],deep+1);
	//for (int i=0;i<deep;i++) printf("  "); printf("%d\n",sum[u]);
	dfs(ch[u][0],deep+1);
}
};

namespace KDT{
const int N=1000010, inf=0x3f3f3f3f;
int n,m,K,rt,ans;

//s[]:tree node  p[2]:2-d coord of leaf node  x[2]:min(LB) coord of a subspace  y[2]:max(RT) coord
struct Node{
	int p[2],x[2],y[2];
	bool operator<(const Node &v)const{
		return p[K]<v.p[K];
	}
}a[N],s[N],q;
int ch[N][2];
#define lc ch[u][0]
#define rc ch[u][1]
void upd(int u){
	inc(i,2){
		if (lc) s[u].x[i]=min(s[u].x[i],s[lc].x[i]),
				s[u].y[i]=max(s[u].y[i],s[lc].y[i]);
		if (rc) s[u].x[i]=min(s[u].x[i],s[rc].x[i]),
				s[u].y[i]=max(s[u].y[i],s[rc].y[i]);
	}
}
void add(int u, Node &t){
	inc(i,2) s[u].x[i]=s[u].y[i]=s[u].p[i]=t.p[i];
}
int disL1Min(int u, Node &t){ //min L1 dis to a Rect of in_tree node
	int ret=0;
	inc(i,2) 
		if (t.p[i]>s[u].y[i]) ret+=t.p[i]-s[u].y[i];
		else if (t.p[i]<s[u].x[i]) ret+=s[u].x[i]-t.p[i];
	return ret;
}
int disL1Max(int u, Node &t){
	int ret=0;
	inc(i,2) ret+=max(abs(t.p[i]-s[u].x[i]),abs(t.p[i]-s[u].y[i]));
	return ret;
}
int sqr(int a){
	return a*a;
}
int disL2Min(int u, Node &t){
	int ret=0;
	inc(i,2) 
		if (t.p[i]>s[u].y[i]) ret+=sqr(t.p[i]-s[u].y[i]);
		else if (t.p[i]<s[u].x[i]) ret+=sqr(t.p[i]-s[u].x[i]);
	return ret;
}
int disL2Max(int u, Node &t){ //max coord dis
	int ret=0;
	inc(i,2) ret+=max(sqr(t.p[i]-s[u].x[i]),sqr(t.p[i]-s[u].y[i]));
	return ret;
}
void build(int &u, int l, int r, int cur){ //O(nlogn)
	u=l+r>>1; K=cur;
	nth_element(a+l,a+u,a+r+1);
	add(u,a[u]);
	if (l<u) build(lc,l,u-1,cur^1);
	if (r>u) build(rc,u+1,r,cur^1);
	upd(u);
}
//Maybe we need to rebuild the tree after unbalanced insert
void ins(int u, int cur){  
	if (q.p[cur]<s[u].p[cur])
		if (lc) ins(lc,cur^1);
		else lc=++n,add(n,q);
	else
		if (rc) ins(rc,cur^1);
		else rc=++n,add(n,q);
	upd(u);
}
void ask(int u){
	ans=min(ans,abs(s[u].p[0]-q.p[0])+abs(s[u].p[1]-q.p[1])); //L1 dis
	int dl=lc?disL1Min(lc,q):inf, dr=rc?disL1Min(rc,q):inf;
	//int dl=lc?disL1Max(lc,q):0, dr=rc?disL1Max(rc,q):0;
	if (dl<dr){ //trim branch, swap > < when search max dis point
		if (dl<ans) ask(lc);
		if (dr<ans) ask(rc);
	}
	else{
		if (dr<ans) ask(rc);
		if (dl<ans) ask(lc);
	}
}
//minDisPoint (L1 dis) with ins operate
//each query asks one nearest point of a giving coord
int main(){
	scanf("%d%d",&n,&m);
	for (int i=1;i<=n;i++) scanf("%d%d",&a[i].p[0],&a[i].p[1]);
	build(rt,1,n,0);
	while (m--){
		int k; scanf("%d%d%d",&k,&q.p[0],&q.p[1]);
		if (k==1) ins(rt,0);
		else{
			ans=inf; ask(rt);
			printf("%d\n",ans);
		}
	}
	return 0;
}
#undef lc
#undef rc
}

namespace SquareTransform{
const int N=100;
typedef int Arr[N][N];int n;
void cp(Arr to,Arr from){inc(i,n)inc(j,n) to[i][j]=from[i][j];}
Arr _t;
//clockwise 90 deg
void rot(Arr a){
	inc(i,n)inc(j,n) _t[j][n-i-1]=a[i][j];
	cp(a,_t);
}
//LR flip
void flip(Arr a){
	inc(i,n)inc(j,n) _t[i][n-j-1]=a[i][j];
	cp(a,_t);
}
bool same(Arr a, Arr b){
	inc(i,n) inc(j,n) if (a[i][j]!=b[i][j]) return 0;
	return 1;
}
}
