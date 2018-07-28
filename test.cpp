#include <bits/stdc++.h>
using namespace std;

#define inc(i,n) for (int i=0;i<n;i++)
#define inc_(i,n) for (int i=1;i<=n;i++)
#define dec(i,n) for (int i=n-1;i>=0;i--)
#define fo(i,a,b) for (int i=a;i<b;i++)
#define forr(i,b,a) for (int i=b-1;i>=a;i--)
#define MP make_pair
#define PII pair<int,int>
#define MS(a,x) memset(a,x,sizeof(a))

const int maxn=100010,alpha=26;

struct Node{
	int l,num; bool vis;
	Node *p, *tr[alpha];
	//vector<Node *> ch;
	void set(int _l){l=_l;memset(tr,0,sizeof(tr));p=0;num=1;vis=0;/*ch.clear();*/}
}nodes[maxn<<1];
int nodec;
Node *root;
Node *open(int l){
	nodes[nodec++].set(l);
	return nodes+nodec-1;
}
void build(char *s){
	nodec=0;
	Node *cur;
	int sl=strlen(s);
	cur=root=open(0);
	for (int i=0;i<sl;i++){
		int x=s[i]-'a';
		Node *p=cur;
		cur=open(i+1);
		for (;p && !p->tr[x];p=p->p)
			p->tr[x]=cur;
		if (!p) cur->p=root;
		else{
			Node *q=p->tr[x];
			if (p->l+1==q->l) cur->p=q;
			else{
				Node *r=open(-1); r[0]=q[0]; r->l=p->l+1;
				q->p=r; cur->p=r; r->num=0;
				for (;p && p->tr[x]==q;p=p->p) p->tr[x]=r;
			}
		}
	}
}

int pos(Node *u, char *s){
	if (*s==0) return u->l;
	if (!u->tr[*s-'a']) return -1;
	return pos(u->tr[*s-'a'],s+1);
}
int cnt(Node *u, char *s){
	if (*s==0) return u->num;
	if (!u->tr[*s-'a']) return 0;
	return cnt(u->tr[*s-'a'],s+1);
}
bool vis[maxn];
void dfs0(Node *u){
	u->vis=1;
	for (int i=0;i<alpha;i++)
		if (u->tr[i] && !u->tr[i]->vis)
			dfs0(u->tr[i]);
	if (u->p) u->p->num+=u->num;
}
char ss[maxn];
void dfs1(Node *u, int deep=0){
	ss[deep]=0;
	inc(i,deep) cout<<"  "; cout<<ss<<' '<<u->num<<'\n';
	for (int i=0;i<alpha;i++)
		if (u->tr[i])
			ss[deep]='a'+i,dfs1(u->tr[i],deep+1);
}
char s0[maxn],ts[100];
int t[maxn],r[maxn];
int main(){
	scanf("%s",s0);
	int s0l=strlen(s0);
	build(s0);
	//dfs0(root);
	inc(i,nodec) t[nodes[i].l]++;
	fo(i,1,s0l+1) t[i]+=t[i-1];
	inc(i,nodec) r[--t[nodes[i].l]]=i;
	forr(i,nodec,1) nodes[r[i]].p->num+=nodes[r[i]].num;
	dfs1(root);
	while (~scanf("%s",ts)){
		cout<<cnt(root,ts)<<'\n';
	}
	return 0;
}
