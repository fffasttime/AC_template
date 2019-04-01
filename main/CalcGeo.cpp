#include "base.cpp"

namespace CalcGeo{

typedef double db;
const db PI=acos(-1);
const db eps=1e-10, inf=1e12;

int sgn(db x){
	if (x<=-eps) return -1;
	return x>=eps;
}
bool eq(db x){return fabs(x)<eps;}

#define Vec const vec &
#define Point const point &
struct vec{
	db x,y;
	vec():x(0),y(0){}
	vec(db x, db y):x(x),y(y){}
	vec(db theta):x(cos(theta)),y(sin(theta)){}
	
	bool operator==(Vec v) const{return eq(x-v.x) && eq(y-v.y);}
	db ang() const{return atan2(y,x);}
	
	vec operator+(Vec v) const{return vec(x+v.x,y+v.y);}
	vec operator-(Vec v) const{return vec(x-v.x,y-v.y);}
	vec operator*(db a) const{return vec(x*a,y*a);}
	vec operator/(db a) const{return vec(x/a,y/a);}
	
	//dot
	db operator|(Vec v) const{return x*v.x+y*v.y;}
	//cross
	db operator&(Vec v) const{return x*v.y-y*v.x;}
	//len
	db operator!() const{return sqrt(x*x+y*y);}
	
	bool operator<(Vec v) const{return x==v.x?y<v.y:x<v.x;}
	vec rot(db rad) const{return vec(x*cos(rad)-y*sin(rad), x*sin(rad)+y*cos(rad));}
	vec l90() const{return vec(-y,x);}
	vec r90() const{return vec(y,-x);}
	vec vert() const{ //l90 and standard
		db l=!*this;
		return vec(-y/l,x/l);
	}
	friend ostream& operator<<(ostream &o, Vec v){
		o<<v.x<<' '<<v.y;
		return o;
	}
};
typedef vec point;

db angle(Vec a, Vec b){return atan2(fabs(a&b,a|b));}
db area2(Point a, Point b, Point c){return b-a & c-a;}

//Line: P=P0+t*vp
// Segment: 0<=t<=1
//intersection point of line P and Q
point lineInt(Point p, Vec vp, Point q, Vec vq){
	db t=(vq & p-q)/(vp&vq);
	return p+vp*t;
}
//distance of p to line A-B
db lineDis(Point p, Point a, Point b){
	vec v1=b-a;
	return fabs(v1 & p-a)/!v1;
}
db segDis(Point p, Point a, Point b){
	if (a==b) return !(a-p);
	vec v1=b-a,v2=p-a,v3=p-b;
	if ((v1|v2)<0) return !v2;
	else if ((v1|v3)>0) return !v3;
	else return fabs(v1&v2)/!v1;
}
point lineProj(Point p, Point a, Point b){
	vec v=b-a;
	return a+v*(v|p-a)/(v|v);
}

//point is on line
bool onLine(Point p, Point a, Point b){return eq(p-a&b-a);}
//point on seg [a,b]
bool onSeg(Point p, Point a, Point b){return onLine(p,a,b) && sgn(a-p|b-p)<=0;}

//fast test before segment cross, 0 indicate the segment are not cross 
bool rectCover(Point a1, Point a2, Point b1, Point b2){return 
	min(a1.x,a2.x)<=max(b1.x,b2.x)+eps &&
	min(b1.x,b2.x)<=max(a1.x,a2.x)+eps &&
	min(a1.y,a2.y)<=max(b1.y,b2.y)+eps &&
	min(b1.y,b2.y)<=max(a1.y,a2.y)+eps;
}
//test if segment is cross
int segCross(Point a1, Point a2, Point b1, Point b2){
	if (!rectCover(a1,a2,b1,b2)) return 0;
	db c1=sgn(a2-a1&b1-a1), c2=sgn(a2-a1&b2-a1);
	db c3=sgn(b2-b1&a1-b1), c4=sgn(b2-b1&a2-b1);
	if (c1*c2>0 || c3*c4>0) //no cross
		return 0; 
	if (c1==0 && c2==0||c3==0 && c4==0) //segment on same line
		return -1; 
	if (c1*c2<0 && c3*c4<0) return 1; //normal cross
	return 2; //a point on line
}

struct circle{
	point c;
	double r;
	circle(Point c, db r):c(c),r(r){}
	circle(Point p1, Point p2):c((p1+p2)/2),r(!(p1-p2)/2){}
	circle(Point p1, Point p2, Point p3){
		c=(p1+lineInt(p2,(p2-p1).l90(),p3,(p3-p1).l90()))/2;
		r=!(p1-c);
	}
	point angle(db theta){return c+point(theta)*r;}
};

//point in or on circle
bool inCir(point p, circle c){return sgn(!(c.c-p)-c.r)<=0;}

//return -1,0,1,2, ans[2]
int cirCross(circle A, circle B, point *ans){
	db d=!(A.c-B.c);
	if (eq(d)){
		if (eq(A.r-B.r)) return -1; //same circle
		return 0; //same center
	}
	if (sgn(A.r+B.r-d)<0) return 0; //too far
	db a=(B.c-A.c).ang();
	db da=acos((A.r*A.r+d*d-B.r*B.r)/(2*A.r*d));
	ans[0]=A.angle(a-da),ans[1]=A.angle(a+da);
	if (ans[0]==ans[1]) return 1; //tang
	return 2; //normal inter
}

//get tangent lines from point p
//return  ans[2] : tangent point 
int cirTang(Point p, circle c, point *ans){
	db d=!(c.c-p);
	if (sgn(d-c.r)<0) return 0;
	if (eq(d-c.r)){
		ans[0] = p;
		return 1;
	}
	db base=(p-c.c).ang();
	db ang=acos(c.r/d);
	ans[0]=c.angle(base-ang);
	ans[1]=c.angle(base+ang);
	return 2;
}

//get cir-cir common tangent line
//return  a[4],b[4] : tangent point on circle
//cnt maybe -1(same), 0(in), 1(in tangent), 2(cross), 3(out tangent), 4(out) 
int cirTang(circle A, circle B, point *a, point *b){
	int cnt=0;
	if (A.c==B.c && eq(A.r-B.r)) return -1;
	if (A.r<B.r) swap(A,B),swap(a,b);
	db d=!(A.c-B.c);
	db diff=A.r-B.r, sum=A.r+B.r;
	if (sgn(d-diff)<0) return 0;
	db base=(B.c-A.c).ang();
	if (eq(d-diff)){
		a[0] = A.angle(base);
		b[0] = a[0];
		return 1;
	}
	db ang=acos((A.r-B.r)/d);
	//in common tangent
	a[cnt]=A.angle(base+ang); b[cnt++]=B.angle(base+ang);
	a[cnt]=A.angle(base-ang); b[cnt++]=B.angle(base-ang);
	if (eq(d-sum)){
		a[cnt] = A.angle(base);
		b[cnt] = a[cnt];
		cnt++;
	} else if (sgn(d-sum)>0){ //out common tangent
		ang=acos((A.r+B.r)/d);
		a[cnt]=A.angle(base+ang); b[cnt++]=B.angle(PI+base+ang); 
		a[cnt]=A.angle(base-ang); b[cnt++]=B.angle(PI+base-ang); 
	}
	return cnt;
}

//line A-B cross circle c point
//return  ans[2] : cross or tangent point
int lineInt(Point a, Point b, circle c, point *ans){
	vec v=b-a, u=a-c.c;
	db e=v|v, f=v|u*2, g=(u|u)-c.r*c.r;
	db delta=f*f-4*e*g;
	if (delta<0) return 0;
	if (eq(delta)) return ans[0]=a-v*(f/2/e),1;
	db t1=(-f-sqrt(delta))/(2*e);
	db t2=(-f+sqrt(delta))/(2*e);
	ans[0]=a+v*t1;
	ans[1]=a+v*t2;
	return 2;
}
//seg A-B cross circle c point
//return  ans[2] : cross or tangent point
int segInt(Point a, Point b, circle c, point *ans){
	vec v=b-a, u=a-c.c;
	db e=v|v, f=v|u*2, g=(u|u)-c.r*c.r;
	db delta=f*f-4*e*g;
	if (delta<0) return 0;
	if (eq(delta)){
		db t=f/2/e;
		if (sgn(t)>=0 && sgn(t-1)<=0) return ans[0]=a-v*t,1;
		return 0;
	}
	db t1=(-f-sqrt(delta))/(2*e);
	db t2=(-f+sqrt(delta))/(2*e);
	point a1=a+v*t1, a2=a+v*t2;
	int cnt=0;
	if (sgn(t1)>=0 && sgn(t1-1)<=0) ans[cnt++]=a1;
	if (sgn(t2)>=0 && sgn(t2-1)<=0) ans[cnt++]=a2;
	return cnt;
}

//point is in or on polygon
//return  1(in), 0(out), -1(on border)
int inPoly(point p, point *poly, int n){
	int w=0;
	for (int i=0;i<n;i++){
		if (onSeg(p,poly[i],poly[(i+1)%n])) 
			return -1;
		int k=sgn(poly[(i+1)%n]-poly[i] & p-poly[i]);
		int d1=sgn(poly[i].y-p.y);
		int d2=sgn(poly[(i+1)%n].y-p.y);
		if (k>0 && d1<=0 && d2>0) w++;
		if (k<0 && d2<=0 && d1>0) w--;
	}
	return w!=0;
}
//test segment strict in poly, 0 out/border, 1 in
//if point at border regard as in poly, 
// the condition is (any segCross(...)==1) && (online<2 || the line short an epsilon still in poly)   
bool inPoly(point p1, point p2, point *poly, int n){
	if (!inPoly(p1,poly,n) || !inPoly(p2,poly,n)) return 0;
	for (int i=0;i<n;i++)
		if (segCross(p1,p2,poly[i],poly[(i+1)%n]))
			return 0;
	return 1;
}

// [!] Require simple polygon, the result will be strange
db polyArea(point *p, int n){
	db sum=0;
	for (int i=1;i<n-1;i++)
		sum+=area2(p[0],p[i+1],p[i]);
	return fabs(sum)/2;
}
// convex hull, Andrew algo
// return  ans[m]
int convex(point *p, int n, point *ans){
	sort(p,p+n);
	int m=0;
	for (int i=0;i<n;i++){
		while (m>1 && (ans[m-1]-ans[m-2]&p[i]-ans[m-2])<=0) m--;
		ans[m++]=p[i];
	}
	int k=m;
	for (int i=n-2;i>=0;i--){
		while (m>k && (ans[m-1]-ans[m-2]&p[i]-ans[m-2])<=0) m--;
		ans[m++]=p[i];
	}
	if (n>1) m--; //p[0]==p[m]
	return m;
}

struct Line{
	point p; vec v;
	Line(){}
	Line(Point p, Vec v):p(p),v(v){}
	bool operator<(const Line &L) const{return v.ang()<L.v.ang();}
};

//line l is left than point p
bool onleft(Line &l, point p){return sgn(l.v&p-l.p)>0;}
const int maxp=1001;
Line Q[maxp<<1]; //deque
point T[maxp<<1]; //temp ans
//intersection of right side half plane, return clockwise polygon point
//[!] The result area can't be unlimited.
//You can add 'inf' edges to make sure that. Then
// if a result point is 'inf' then the real result is unlimited.
int halfplaneInt(Line *l, int n, point *ans){
	sort(l,l+n); //[!] This operation changed input
	int head=0,tail=0;
	Q[0]=l[0];
	for (int i=1;i<n;i++){
		while (head<tail && !onleft(l[i],T[tail-1])) tail--;
		while (head<tail && !onleft(l[i],T[head])) head++;
		Q[++tail]=l[i];
		if (eq(Q[tail].v&Q[tail-1].v)){
			--tail;
			if (onleft(Q[tail],l[i].p)) Q[tail]=l[i];
		}
		if (head<tail) 
			T[tail-1]=lineInt(Q[tail-1].p,Q[tail-1].v,Q[tail].p,Q[tail].v);		
	}
	while (head<tail && !onleft(Q[head],T[tail])) tail--; 
	if (head>=tail-1) return 0;  //m<3, no available area
	T[tail]=lineInt(Q[head].p,Q[head].v,Q[tail].p,Q[tail].v); //head cross tail
	int m=0;
	for (int i=head;i<=tail;i++) ans[m++]=T[i];
	return m;
}

//---complex---

//sector a~b of radius r
db secArea(point a, point b, db r){
	db ang=a.ang()-b.ang();
	while (sgn(ang)<=0) ang+=2*PI;
	while (sgn(ang-2*PI)>0) ang-=2*PI;
	ang=min(ang, 2*PI-ang);
	return r*r*ang/2;
}
db triArea(point p1, point p2){return fabs(p1&p2)/2;}
//intersection area of circle C and triangle P1-P2-C
db tri_cirArea(point p1, point p2, circle c){
	db r=c.r;
	p1=p1-c.c; p2=p2-c.c;
	c.c=vec(0,0);
	point p[2];
	if (sgn(!p1-r)<0){
		if (sgn(!p2-r)<0) return triArea(p1,p2);
		segInt(p1,p2,c,p);
		return triArea(p1,p[0]) + secArea(p[0],p2,r);
	}
	if (sgn(!p2-r)<0){
		segInt(p1,p2,c,p);
		return secArea(p1,p[0],r) + triArea(p[0],p2);
	}
	int pc=segInt(p1,p2,c,p);
	if (pc==2) return secArea(p1,p[0],r)+triArea(p[0],p[1])+secArea(p[1],p2,r);
	return secArea(p1,p2,r);	
}
//intersection area of polygon P and circle C
db poly_cirArea(point *p, int n, circle c){
	db ans=0;
	for (int i=0;i<n;i++){
		db d=sgn(p[i]-c.c & p[(i+1)%n]-c.c);
		ans+=d*tri_cirArea(p[i],p[(i+1)%n],c);
	}
	return fabs(ans);
}

//min circle corver point set p
//average O(n)
circle mincirCover(point *p, int n){
    random_shuffle(p,p+n); //[!] This operation changed input
    circle c(p[0],0);
    for (int i=1;i<n;i++)
        if (sgn(!(c.c-p[i])-c.r)>0){
            c=circle(p[i],0);
            for (int j=0;j<i;j++)
                if (sgn(!(c.c-p[j])-c.r)>0){
                    c=circle(p[i],p[j]);
                    for (int k=0;k<j;k++)
                        if (sgn(!(c.c-p[k])-c.r)>0)
                            c=circle(p[i],p[j],p[k]);
                }
        }
    return c;
}

const int maxn=100010;
//max dis point pair on poly
// farthest point pair on plane
db polyDiam(point *p0, int n0){
	static point p[maxn];
	int n=convex(p0,n0,p); //[!] p0 changed
	p[n]=p[0];
	int opp=1; db ans=!(p[0]-p[1]);
	for (int i=0;i<n;i++){
		while (area2(p[i],p[i+1],p[opp+1])>area2(p[i],p[i+1],p[opp])) opp=(opp+1)%n;
		ans=max(ans, max(!(p[opp]-p[i]),!(p[opp]-p[i+1])));
	}
	return ans;
}
//min dis between parallel lines clip polygon
db polyWidth(point *p0, int n0){
	static point p[maxn];
	int n=convex(p0,n0,p); //[!] p0 changed
	p[n]=p[0];
	int opp=1; db ans=1e10;
	for (int i=0;i<n;i++){
		while (area2(p[i],p[i+1],p[opp+1])>area2(p[i],p[i+1],p[opp])) opp=(opp+1)%n;
		ans=min(ans, lineDis(p[opp],p[i],p[i+1]));
	}
	return ans;
}

void test(){
	vec a(1.2,2.5);
	vec b(1.4,1.3);
	vec c(1,2),vc(0,1);
	vec d(3,1),vd(-3,1.5);
	vec ep(eps/2,-eps/2);
	cout<<a+b<<" expect 2.6 3.8\n";
	cout<<a-b<<" expect -0.2 1.2\n";
	cout<<a*2<<" expect 2.4 5\n";
	cout<<b/2<<" expect 0.7 0.65\n";
	cout<<(a|b)<<" expect 4.93\n";
	cout<<(a&b)<<" expect -1.94\n";
	cout<<(b&a)<<" expect 1.94\n";
	cout<<(a==b)<<" expect 0\n";
	cout<<(a==a+ep)<<" expect 1\n";
	cout<<!a<<" expect 2.77308\n";
	cout<<(a|a)<<" expect 7.69\n";
	cout<<(c.ang())<<" expect 1.10715\n";
	cout<<(c.rot(PI/2))<<" expect -2 1\n";
	cout<<(c.rot(-PI/2))<<" expect 2 -1\n";
	cout<<c.vert()<<" expect -0.8944 0.4472\n";
	cout<<angle(c,d)<<" expect "<<c.ang()-d.ang()<<'\n';
	cout<<lineInt(c,vc,d,vd)<<" expect 1 2\n";
	cout<<lineInt(d,vd,c,vc)<<" expect 1 2\n";
	cout<<lineDis(point(0,0),d,vec(0,2.5))<<" expect 2.23607\n";
	cout<<segDis(point(0,0),d,vec(0,2.5))<<" expect 2.23607\n";
	cout<<segDis(point(0,5),d,vec(0,2.5))<<" expect 2.5\n";
	cout<<lineProj(point(0,0),d,vec(4,0))<<" expect 2 2\n";
	
	cout<<onLine(point(2,2),d,vec(4,0))<<" expect 1\n";
	cout<<onSeg(point(2,2),d,vec(4,0))<<" expect 0\n";
	cout<<onSeg(point(3.5,0.5),d,vec(4,0))<<" expect 1\n";
	cout<<onSeg(point(4,0),d,vec(4,0))<<" expect 1\n";
	
	cout<<segCross(point(2,2),point(0,0),d,vec(0,4))<<" expect 2\n";
	cout<<segCross(point(3,3),point(0,0),d,vec(0,4))<<" expect 1\n";
	cout<<segCross(point(0,4),point(0,0),d,vec(0,4))<<" expect 2\n";
	cout<<segCross(point(1,1),point(0,0),d,vec(0,4))<<" expect 0\n";
	cout<<segCross(point(2,2),point(-1,5),d,vec(0,4))<<" expect -1\n";
	cout<<segCross(point(0,4),point(-1,5),d,vec(0,4))<<" expect 2\n";
	
	point ans[2];
	circle c1(point(0,1),1),c2(point(0,0),1);
	cout<<cirCross(c1,c2,ans)<<" expect 2\n";
	cout<<ans[0]<<' '<<ans[1]<<" expect -0.866 0.5 0.866 0.5\n";
	
	c1=circle(point(0,1),1),c2=c1;
	cout<<cirCross(c1,c2,ans)<<" expect -1\n";
	
	c1=circle(point(0,1),1),c2=circle(point(4,4),1);
	cout<<cirCross(c1,c2,ans)<<" expect 0\n";
	
	c1=circle(point(0,1),1),c2=circle(point(0,0),2);
	cout<<cirCross(c1,c2,ans)<<" expect 1\n";
	cout<<ans[0]<<" expect 0 2\n";
	
	cout<<cirTang(vec(0,0),c1,ans)<<" expect 1\n";
	cout<<ans[0]<<" expect 0 0\n";
	
	cout<<cirTang(vec(1,0),c1,ans)<<" expect 2\n";
	cout<<ans[0]<<' '<<ans[1]<<" expect 1 1 0 0 or 0 0 1 1\n";
	
	c1=circle(point(0,0),2);
	cout<<cirTang(vec(-4,0),c1,ans)<<" expect 2\n";
	cout<<ans[0]<<' '<<ans[1]<<" expect -1 1.73205 -1 -1.73205\n";
	
	cout<<lineInt(vec(-4,4),vec(4,-4),c1, ans)<<" expect 2\n";
	cout<<ans[0]<<' '<<ans[1]<<" expect -1.414 1.414 1.414 -1.414\n";
	
	//cout<<segInt(vec(0,0),vec(4,0),c1)<<" expect 2 0\n";
	//cout<<segInt(vec(4,0),vec(0,0),c1)<<" expect 2 0\n";
	
	c2=circle(point(0,-1),1);
	point xa[4],xb[4];
	cout<<cirTang(c1,c2,xa,xb)<<" expect 1\n";
	cout<<xa[0]<<' '<<xb[0]<<" expect 0 -2 0 -2\n";
	
	c2=circle(point(2,2),2);
	cout<<cirTang(c1,c2,xa,xb)<<" expect 2\n";
	cout<<xa[0]<<' '<<xb[0]<<' '<<xa[1]<<' '<<xb[1]<<" expect -1.414 1.414 0.586 3.414 1.414 -1.414 3.414 0.586\n";
	
	c2=circle(point(4,0),2);
	cout<<cirTang(c1,c2,xa,xb)<<" expect 3\n";
	cout<<xa[0]<<' '<<xb[0]<<' '<<xa[1]<<' '<<xb[1]<<' '<<xa[2]<<' '<<xb[2]<<
		" expect 0 2 4 2 0 -2 4 -2 2 0\n";
	
	c1=circle(point(-2,0),sqrt(2));c2=circle(point(2,0),sqrt(2));
	cout<<cirTang(c1,c2,xa,xb)<<" expect 4\n";
	cout<<xa[2]<<' '<<xb[2]<<' '<<xa[3]<<' '<<xb[3]<<" expect -1 1 1 -1 -1 -1 1 1\n";
	
	a=vec(PI*0.75);
	cout<<a<<" expect -0.707 0.707\n";
	
	c1=circle(point(0,0),point(1,2));
	cout<<c1.c<<' '<<c1.r<<" expect 0.5 1 1.118\n";

	c1=circle(point(0,2),point(0,0),point(1,1));
	cout<<c1.c<<' '<<c1.r<<" expect 0 1 1\n";
	c1=circle(point(0,2),point(1,sqrt(3)),point(-sqrt(3),-1));
	cout<<c1.c<<' '<<c1.r<<" expect 0 0 2\n";
	
	point poly[4]={{-1,0},{2,1},{1,0},{2,-1}};
	cout<<inPoly({0,0},poly,4)<<' '<<inPoly({-2,0},poly,4)<<' '<<inPoly({1,0},poly,4)<<" expect 1 0 -1\n";
	cout<<inPoly({0,-0.5},poly,4)<<' '<<inPoly({1,0.2},poly,4)<<' '<<inPoly({1.5,0.2},poly,4)<<" expect 0 1 0\n";
	cout<<inPoly({1.5,0.5},poly,4)<<' '<<polyArea(poly,4)<<" expect -1 2\n";
	
	point aa[4];
	point polyt[4]={{-1,0},{2,1},{1,0},{2,-1}};
	cout<<convex(polyt,4,aa)<<" expect 3\n";
	
	cout<<mincirCover(polyt,4).c<<" expect "<<circle(poly[0],poly[1],poly[3]).c<<'\n';
	cout<<mincirCover(polyt,4).r<<" expect "<<circle(poly[0],poly[1],poly[3]).r<<'\n';
	
	cout<<poly_cirArea(poly, 4, {{0,0},1})<<" expect ???\n";
}
}
int main(){
	CalcGeo::test();
}