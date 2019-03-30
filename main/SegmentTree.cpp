#include "base.cpp"

namespace TreeArr{
//WARN: index of tr[] statrs from 1
const int maxn=100010;
int tr[maxn]; int n;
void add(int p, int x){for(;p<=n;p+=p&-p)tr[p]+=x;}
ll sum(int p){ll ret=0;for(;p;p-=p&-p)ret+=tr[p];return ret;}

//section add and section sum version, section [l,r]
template <typename X>    
struct tree_array{    
    struct tree_array_single{    
        X tr[maxn];    
        void add(int p,X x){for(;p<=n;p+=p&-p)tr[p]+=x;}    
        X sum(int p){ll ret=0;for(;p;p-=p&-p)ret+=tr[p];return ret;}    
    }T1,T2;    
    void add(int p,X x){T1.add(p,x);T2.add(p,p*x);}      
    X sum(int p){return (p+1)*T1.sum(p)-T2.sum(p);}
public:
    void update(int l,int r,int x){add(l,x);add(r+1,-x);}  
    X query(int l,int r){return sum(r)-sum(l-1);}    
};
}

namespace SEGT{
const int MAXN=100010;

ll sum[MAXN<<2], tadd[MAXN<<2], tmul[MAXN<<2], a[MAXN];
ll n,m,p;
#define lc u+u+1
#define rc u+u+2
void build(int u, int l, int r){
	tmul[u]=1;
	if (l==r-1){
		sum[u]=a[l];
		return;
	}
	int mid=l+r>>1;
	build(lc,l,mid); build(rc,mid,r);
	sum[u]=(sum[lc]+sum[rc])%p;
}
void upd(int u, int l, int r){
	int mid=l+r>>1;
	sum[lc]*=tmul[u]; sum[lc]+=(mid-l)*tadd[u]; sum[lc]%=p;
	sum[rc]*=tmul[u]; sum[rc]+=(r-mid)*tadd[u]; sum[rc]%=p;
	tadd[lc]*=tmul[u]; tadd[lc]+=tadd[u]; tadd[lc]%=p;
	tmul[lc]*=tmul[u]; tmul[lc]%=p;
	tadd[rc]*=tmul[u]; tadd[rc]+=tadd[u]; tadd[rc]%=p;
	tmul[rc]*=tmul[u]; tmul[rc]%=p;
	tadd[u]=0; tmul[u]=1;
}
void mul(int u, int l, int r, int cl, int cr, ll c){
	if (cl<=l && cr>=r){
		tadd[u]*=c; tadd[u]%=p;
		tmul[u]*=c; tmul[u]%=p;
		sum[u]*=c; sum[u]%=p;
		return;
	}
	if (tadd[u] || tmul[u]!=1) upd(u,l,r);
	int mid=l+r>>1;
	if (cl<mid) mul(lc,l,mid,cl,cr,c);
	if (cr>mid) mul(rc,mid,r,cl,cr,c);
	sum[u]=(sum[lc]+sum[rc])%p;
}
void add(int u, int l, int r, int cl, int cr, ll c){
	if (cl<=l && cr>=r){
		tadd[u]+=c; tadd[u]%=p;
		sum[u]+=c*(r-l)%p; sum[u]%=p;
		return;
	}
	if (tadd[u] || tmul[u]!=1) upd(u,l,r);
	int mid=l+r>>1;
	if (cl<mid) add(lc,l,mid,cl,cr,c);
	if (cr>mid) add(rc,mid,r,cl,cr,c);
	sum[u]=(sum[lc]+sum[rc])%p;
}
ll ask(int u, int l, int r, int cl, int cr){
	if (cl<=l && cr>=r) return sum[u];
	if (tadd[u] || tmul[u]!=1) upd(u,l,r);
	int mid=l+r>>1;
	ll ret=0;
	if (cl<mid) ret+=ask(lc,l,mid,cl,cr);
	if (cr>mid) ret+=ask(rc,mid,r,cl,cr);
	return ret%p;
}
ll pointask(int u, int l, int r, int q){
	if (l==r-1) return sum[u];
	if (tadd[u] || tmul[u]!=1) upd(u,l,r);
	int mid=l+r>>1;
	if (q<mid) return pointask(lc,l,mid,q);
	return pointask(u,mid,r,q);
}

#undef lc
#undef rc

}


namespace FSEGT{
const int maxn=200010;
int sum[maxn<<5], root[maxn], lc[maxn<<5], rc[maxn<<5],trcnt;
int a[maxn],b[maxn];

void build(int &u, int l, int r){
	u=trcnt++;
	if (l==r-1) return;
	int mid=l+r>>1;
	build(lc[u],l,mid); build(rc[u],mid,r);
}
int mod(int u, int l, int r, int c){
	int v=trcnt++;
	lc[v]=lc[u]; rc[v]=rc[u]; sum[v]=sum[u]+1;
	if (l==r-1) return v;
	int mid=l+r>>1;
	if (c<mid) lc[v]=mod(lc[v],l,mid,c);
	else rc[v]=mod(rc[v],mid,r,c);
	return v;
}
int query(int u, int v, int l, int r, int q){
	int mid=l+r>>1, x=sum[lc[v]]-sum[lc[u]];
	if (l==r-1) return l;
	if (x>=q) return query(lc[u],lc[v],l,mid,q);
	return query(rc[u],rc[v],mid,r,q-x);
}
//ask: [l,r) kth number
int main(){
	int n,m;
	cin>>n>>m;
	for (int i=0;i<n;i++)
		scanf("%d", a+i),b[i]=a[i];
	sort(b,b+n);
	int n1=unique(b,b+n)-b;
	build(root[0],0,n1);
	for (int i=0;i<n;i++){
		int q=lower_bound(b,b+n1,a[i])-b;
		root[i+1]=mod(root[i],0,n1,q);
	}
	for (int i=0;i<m;i++){
		int l,r,q;
		scanf("%d%d%d",&l,&r,&q);
		printf("%d\n",b[query(root[l-1],root[r],0,n1,q)]);
	}
	return 0;
}
}

