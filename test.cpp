#include <bits/stdc++.h>
using namespace std;

const int maxn=100010,alpha=26;

struct Node{
	int l,num; bool vis;
	Node *p, *tr[alpha];
	vector<Node *> ch;
	Node (int _l):l(_l){memset(tr,0,sizeof(tr));p=0;num=1;vis=0;}
};

Node *root;

void build(char *s){
	Node *cur;
	int sl=strlen(s);
	cur=root=new Node(0);
	for (int i=0;i<sl;i++){
		int x=s[i]-'a';
		Node *p=cur;
		cur=new Node(i+1);
		for (;p && !p->tr[x];p=p->p)
			p->tr[x]=cur;
		if (!p) cur->p=root;
		else{
			Node *q=p->tr[x];
			if (p->l+1==q->l) cur->p=q;
			else{
				Node *r=new Node(-1); r[0]=q[0]; r->l=p->l+1;
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
char s0[maxn],ts[100];

int main(){
	scanf("%s",s0);
	build(s0);
	dfs0(root);
	while (~scanf("%s",ts)){
		cout<<cnt(root,ts)<<'\n';
	}
	return 0;
}
