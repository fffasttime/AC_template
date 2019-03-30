#include "base.cpp"

namespace Treap{
//TT: an ordered struct
typedef int TT;
const int maxn=100001;
struct Node{
	//x: number, s: sum size of cur and subtree, cnt: cnt of cur num
	Node *c[2];
	TT x;
	int s,r,cnt;
	Node(TT _x){c[0]=c[1]=0;s=cnt=1;x=_x;r=rand();}
	Node(){};
}tree[maxn<<1];
#define lc u->c[0]
#define rc u->c[1]
#define lcs (lc?lc->s:0)
#define rcs (rc?rc->s:0)
int trcnt=0;
Node *open(TT x){
	tree[trcnt++]=Node(x);
	return tree+trcnt-1;
}
void upd(Node *u){
	u->s=lcs+rcs+u->cnt;
	//more updates...
}
//rt: set lc to root
void rot(Node* &u, int d){ //0 lt, 1 rt
	Node *t=u->c[d^1]; u->c[d^1]=t->c[d]; t->c[d]=u;
	t->s=u->s; upd(u); u=t;
}
void ins(Node* &u, TT x){
	if (!u){u=open(x);return;}
	if (x==u->x) {u->cnt++;u->s++; return;}
	int d=x>u->x; u->s++;
	ins(u->c[d],x);
	if (u->c[d]->r>u->r) rot(u,d^1);
}
void delx(Node* &u, TT x){
	if (!u) return;
	if (x==u->x){
		if (u->cnt>1) u->cnt--, u->s--;
		else if (!lc || !rc) u=max(lc,rc);
		else{
			rot(u,lc->r>rc->r);
			u->s--,delx(u->c[u->x<x],x);
		}
	}
	else u->s--,delx(u->c[u->x<x],x);
}
int rk(Node *u, TT x){
	if (!u) return 0;
	if (u->x==x) return lcs + 1;
	if (u->x<x) return lcs + u->cnt + rk(rc,x);
	else return rk(lc, x);
}
//get point by element
Node* findx(Node *u, TT x){
	if (!u) return 0;
	if (x==u->x) return u;
	return findx(u->c[u->x<x],x);
}
//get point by rank
//r=(1~tree_size)
Node* findr(Node *u, int r){
	if (!u) return 0;
	if (r<=lcs) return findr(lc,r);
	r-=lcs;
	if (r<=u->cnt) return u;
	r-=u->cnt;
	return findr(rc,r);
}
TT pred(Node *u, TT x){
	if (!u) return -0x3f3f3f3f;
	if (u->x<x) return max(u->x,pred(rc,x));
	else return pred(lc,x);
}
TT succ(Node *u, TT x){
	if (!u) return 0x3f3f3f3f;
	if (x<u->x) return min(u->x,succ(lc,x));
	else return succ(rc,x);
}
void dfs(Node *u, int deep=0){
	if (lc) dfs(lc,deep+1);
	for (int i=0;i<deep;i++) cout<<"   ";
	cout<<u->x<<' '<<u->s<<'\n';
	if (rc) dfs(rc,deep+1);
}
void caller(){
	Node *root=0;
	int T;cin>>T;
	while (T--)	{
		int c,x; scanf("%d%d",&c,&x);
		if (c==1) ins(root,x);
		if (c==2) delx(root,x);
		if (c==3) cout<<rk(root,x)<<'\n';
		if (c==4) cout<<findr(root,x)->x<<'\n';
		if (c==5) cout<<pred(root,x)<<'\n';
		if (c==6) cout<<succ(root,x)<<'\n';
		//dfs(root),cout<<'\n';
	}
}
#undef lc
#undef rc
#undef lcs
#undef rcs
}
namespace Splay{
const int maxn=100010;

int val[maxn],siz[maxn],ch[maxn][2],pa[maxn],cnt[maxn];
bool rev[maxn];
int root,trcnt;
#define lc ch[u][0]
#define rc ch[u][1]
//pushup
void upd(int u){
	siz[u]=cnt[u]+siz[lc]+siz[rc];
}
//lazy tags
void pushdown(int u){
	if (rev[u]){
		rev[lc]^=1;rev[rc]^=1;
		swap(lc,rc);
		rev[u]=0;
	}
}
void rot(int u, int c){
	int p=pa[u];
	ch[p][!c]=ch[u][c];
	pa[ch[u][c]]=p; pa[u]=pa[p];
	if (pa[u]) ch[pa[p]][ch[pa[p]][1]==p]=u;
	ch[u][c]=p; pa[p]=u;
	upd(p); upd(u);
}
//u->under s
void splay(int u, int s){
	while (pa[u]!=s){
		int p=pa[u],pp=pa[p];
		if (pp==s) rot(u,ch[p][0]==u);
		else{
			int c=(ch[pp][0]==p);
			if (ch[p][c]==u) rot(u,!c); else rot(p,c);
			rot(u,c);
		}
	}
	if (s==0) root=u;
}
//rank k->under s
void rk(int k, int s=0){
	int u=root;
	assert(k>=1 && k<=siz[root]);
	while (1){
		pushdown(u);
		if (k<=siz[lc]) u=lc;
		else if (k>siz[lc]+cnt[u]) k-=siz[lc]+cnt[u],u=rc;
		else break;
	}
	splay(u,s);
}
//x->under s
void fi(int x, int s=0){
	int u=root,p;
	while (x!=val[u] && u)
		p=u,u=ch[u][x>val[u]];
	if (u && x==val[u]) splay(u,s);
	else if (!u) splay(p,s);
}

#ifdef NO_COMPILE
//memory restricted open
int avail[maxn],avac;
void open(int &u, int x){
	u=avail[--avac];
	lc=rc=pa[u]=0;
	siz[u]=cnt[u]=1;
	val[u]=x;
}
void pre(){
	for (int i=1;i<maxn;i++) 
		avail[avac++]=maxn-i;
	open(root, -10086); // in section problem, add virtual point is convenient
	int r; open(r, -10086);
	ch[root][1]=r; pa[r]=root;
	upd(root);
}
void release(int u){
	if (!u) return;
	release(lc);
	release(rc);
	avail[avac++]=u;
}
#endif
void open(int &u, int x){
	u=++trcnt;
	lc=rc=pa[u]=0;
	siz[u]=cnt[u]=1;
	val[u]=x;
}
//root, value, parent
void ins(int &u, int x, int p){
	if (!u) open(u,x),pa[u]=p;
	else if (val[u]==x) cnt[u]++,siz[u]++;
	if (!u || val[u]==x){splay(u,0);return;}
	ins(ch[u][val[u]<x],x,u);
	upd(u);
}
//delete root
void del_(){
	int u=root;
	if (rc){
		root=rc; rk(1,0); //right, though it's hard to understand
		ch[root][0]=lc;
		if (ch[root][0]) pa[ch[root][0]]=root;
	}
	else root=lc;
	pa[root]=0;
	upd(root);
}
void del(int x){
	fi(x,0);
	if (val[root]==x)
		if (cnt[root]>1) cnt[root]--,siz[root]--;
		else del_();
}
int pred(int u, int x){
	if (!u) return -0x3f3f3f3f;
	if (val[u]<x) return max(val[u],pred(rc,x));
	return pred(lc,x);
}
int succ(int u, int x){
	if (!u) return 0x3f3f3f3f;
	if (x<val[u]) return min(val[u],succ(lc,x));
	return succ(rc,x);
}
//90 degree rotate debug print
void debug(int u=root, int deep=0){
	if (!u) return;
	debug(rc, deep+1);
	for (int i=0;i<deep;i++) cout<<"  ";
	cout<<val[u]<<' '<<siz[u]<<'\n';
	debug(lc, deep+1);
}
int n,m;
void dfs(int u){
	if (!u) return;
	pushdown(u);
	dfs(lc);
	if (val[u]>0 && val[u]<=n) cout<<val[u]<<' ';
	dfs(rc);
}
void mian(){
	int T; cin>>T;
	while (T--){
		int c,x; scanf("%d%d",&c,&x);
		if (c==1)
			ins(root,x,0);
		else if (c==2)
			del(x);
		else if (c==3){ //get rk of x
			fi(x,0); 
			cout<<siz[ch[root][0]]+1<<'\n';
		}
		else if (c==4){ //get k th
			rk(x,0);
			cout<<val[root]<<'\n';
		}
		else if (c==5){ //pred
			ins(root,x,0);
			rk(siz[ch[root][0]],0);
			cout<<val[root]<<'\n';
			del(x);
		}
		else if (c==6){ //succ
			ins(root,x,0);
			rk(siz[ch[root][0]]+cnt[root]+1,0);
			cout<<val[root]<<'\n';
			del(x);
		}
		//debug(root,0);
	}
}
int main(){ //reverse
	cin>>n>>m;
	for (int i=0;i<=n+1;i++) ins(root,i,0);
	for (int i=0;i<m;i++){
		int l,r; scanf("%d%d",&l,&r);
		rk(l,0); rk(r+2,root);
		rev[ch[ch[root][1]][0]]^=1;
		//debug(root,0);
	}
	dfs(root); putchar('\n');
	return 0;
}
#undef lc
#undef rc
}
namespace NRTreap{
const int maxn=100010;
typedef int TT;
struct Node{
	Node *c[2];
	TT x;
	int s, r;
	bool rev;
}tree[maxn<<1];
typedef pair<Node *,Node *> PD;
int trcnt;
Node *root;
Node *open(int x){
	tree[trcnt++]=(Node){0,0,x,1,rand(),0};
	return tree+trcnt-1;
}
#define lc u->c[0]
#define rc u->c[1]
#define lcs (lc?lc->s:0)
#define rcs (rc?rc->s:0)
void upd(Node *u){
	u->s=lcs+rcs+1;
}
void pushdown(Node *u){
	if (u->rev){
		if (lc) lc->rev^=1;
		if (rc) rc->rev^=1;
		swap(lc,rc);
		u->rev=0;
	}
}
Node *merge(Node *u, Node *v){
	if (!u || !v) return max(u,v);
	pushdown(u); pushdown(v);
	if (u->r<v->r) {rc=merge(rc,v);upd(u);return u;}
	else {v->c[0]=merge(u,v->c[0]);upd(v);return v;} 
}
PD split(Node *u, int k){
	if (!u) return MP((Node *)0,(Node *)0);
	pushdown(u);
	PD t;
	if (k<=lcs){
		t=split(lc,k);
		lc=t.second;
		upd(u);
		t.second=u;
	}
	else{
		t=split(rc,k-lcs-1);
		rc=t.first;
		upd(u);
		t.first=u;
	}
	return t;
}
int rk(Node *u, TT x){
	if (!u) return 0;
	if (u->x<x) return lcs + 1 + rk(rc,x);
	else return rk(lc, x);
}
int findr(Node *u, int r){
	if (!u) return 0;
	if (r<=lcs) return findr(lc,r);	r-=lcs;
	if (r==1) return u->x; r--;
	return findr(rc,r);
}
void ins(TT x){
	int k=rk(root,x);
	PD t=split(root,k);
	Node *u=open(x);
    root=merge(t.first,merge(u,t.second));
}
//t1.second is deleted
void del(TT x){
	int k=rk(root,x);
	PD t1=split(root,k),t2=split(t1.second,1);
	root=merge(t1.first,t2.second);
}
void debug(Node *u, int deep=0){
	if (lc) debug(lc,deep+1);
	for (int i=0;i<deep;i++) cout<<"   ";
	cout<<u->x<<' '<<u->s<<' '<<u->rev<<'\n';
	if (rc) debug(rc,deep+1);
}
int n;
void dfs(Node *u){
	if (!u) return;
	pushdown(u);
	dfs(lc);
	if (u->x>0 && u->x<=n) cout<<u->x<<' ';
	dfs(rc);
}
int mian(){
	int T;cin>>T;
	while (T--)	{
		int c,x; scanf("%d%d",&c,&x);
		if (c==1) ins(x);
		if (c==2) del(x);
		if (c==3) cout<<rk(root,x)+1<<'\n';
		if (c==4) cout<<findr(root,x)<<'\n';
		if (c==5) cout<<findr(root,rk(root,x))<<'\n';
		if (c==6) cout<<findr(root,rk(root,x+1)+1)<<'\n';
		//dfs(root),cout<<'\n';
	}
	return 0;
}
int main(){ //reverse
	int m;cin>>n>>m;
	for (int i=0;i<=n+1;i++) ins(i);
	for (int i=0;i<m;i++){
		int l,r; scanf("%d%d",&l,&r);
		PD x=split(root,l);
		PD y=split(x.second,r-l+1);
		y.first->rev^=1;
		root=merge(x.first,merge(y.first,y.second));
		//dfs(root); putchar('\n');
		//debug(root);
	}
	dfs(root); putchar('\n');
	return 0;
}
#undef lc
#undef rc
}

