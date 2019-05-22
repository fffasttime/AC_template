#include "base.cpp"

namespace CalcGeo{

typedef double db;
const db PI=acos(-1);
const db eps=1e-10, inf=1e12;

bool eq(db x){return fabs(x)<eps;}
int sgn(db x){
	if (x<=-eps) return -1;
	return x>=eps;
}

#define Vec const vec &
#define Point const point &
struct vec{
	db x,y;
	vec():x(0),y(0){}
	vec(db x, db y):x(x),y(y){} //[i] init-list is easier to use in c++1x
	vec(db theta):x(cos(theta)),y(sin(theta)){}

	bool operator==(Vec v) const{return eq(x-v.x) && eq(y-v.y);}
	db ang() const{return atan2(y,x);}
	
	vec operator+(Vec v) const{return vec(x+v.x,y+v.y);}
	vec operator-(Vec v) const{return vec(x-v.x,y-v.y);}
	vec operator*(db a) const{return vec(x*a,y*a);}
	vec operator/(db a) const{return vec(x/a,y/a);}
	
	db operator|(Vec v) const{return x*v.x+y*v.y;} //dot
	db operator&(Vec v) const{return x*v.y-y*v.x;} //cross
	db operator!() const{return sqrt(x*x+y*y);}    //len
	
	bool operator<(Vec v) const{return x==v.x?y<v.y:x<v.x;}
	//rotate countclockwise
	vec std() const{return *this/!*this;}
	vec rot(db rad) const{return vec(x*cos(rad)-y*sin(rad), x*sin(rad)+y*cos(rad));}
	vec l90() const{return vec(-y,x);}
	vec r90() const{return vec(y,-x);}
	vec vert() const{return (*this).l90().std();}  //l90 and standard
	
	friend ostream& operator<<(ostream &o, Vec v){return o<<v.x<<','<<v.y;}
};
typedef vec point;

//cmp2 sort by angle without atan2
// angle range [-pi,pi)
bool cmp2(Vec a, Vec b){
	int d1=sgn(a.y),d2=sgn(b.y);
	if (d1^d2) return d1<d2;
	if (d2==0) return a.x<b.x;
	return (a&b)>0;
}

db angle(Vec a, Vec b){return fabs(atan2(a&b,a|b));}
db cross(Point a, Point b, Point c){return b-a & c-a;}
db dot(Point a, Point b, Point c){return b-a | c-a;}

//cosine theory
db angle(db a, db b, db c){return acos((a*a+b*b-c*c)/(2*a*b));}

//Line: P=P0+t*vp
// Segment: 0<=t<=1
//intersection point of line P and Q
point lineInt(Point p, Vec vp, Point q, Vec vq){
	db t=(vq & p-q)/(vp&vq);
	return p+vp*t;
}
//point projection on line A+tV
point lineProj(Point p, Point s, Vec v){
	return s+v*(v|p-s)/(v|v);
}
//symmetric point of P about line A+tV
point symmetric(Point p, Point s, Vec v){
	return lineProj(p,s,v)*2-p;
}
//distance of p to line A+tV
db lineDis(Point p, Point s, Vec v){
	return fabs(v & p-s)/!v;
}
//distance of p to segment A+tV
db segDis(Point p, Point s, Vec v){
	if (eq(!v)) return !(s-p); //a point
	vec v2=p-s,v3=p-s-v;
	if ((v|v2)<0) return !v2;
	else if ((v|v3)>0) return !v3;
	return fabs(v&v2)/!v;
}
//distance of seg A-B and seg C-D
db segDis(Point a, Point b, Point c, Point d){
	vec u=b-a, v=d-c;
	return min(min(segDis(c,a,u),segDis(d,a,u)),min(segDis(a,c,v),segDis(b,c,v)));
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
//test if segment A1-A2 B1-B2 is cross
int segCross(Point a1, Point a2, Point b1, Point b2){
	if (!rectCover(a1,a2,b1,b2)) return 0; //not necessary
	db c1=sgn(a2-a1&b1-a1), c2=sgn(a2-a1&b2-a1);
	db c3=sgn(b2-b1&a1-b1), c4=sgn(b2-b1&a2-b1);
	if (c1*c2>0 || c3*c4>0) //no cross
		return 0; 
	if (c1==0 && c2==0||c3==0 && c4==0) //segment on same line
		return -1; 
	if (c1*c2<0 && c3*c4<0) return 1; //normal cross
	return 2; //a point on line
}

//#define const line& Line

struct line{
	point p; vec v;
	line(){}
	line(Point p, db ang):p(p),v(ang){}
	//ax+by+c=0
	line(db a, db b, db c){
		if (eq(b)) p=point(-c/a,0), v=vec(0,1);
		else p=point(0,-c/b),v=vec(1,-a/b);
	}
	line(Point p, Vec v):p(p),v(v){}
	bool operator<(const line &l) const{return v.ang()<l.v.ang();}
};


struct circle{
	point c; db r;
	
	circle(){}
	circle(Point c, db r):c(c),r(r){}
	circle(Point p1, Point p2):c((p1+p2)/2),r(!(p1-p2)/2){}
	//circle passing point P1P2P3
	circle(Point p1, Point p2, Point p3){ //[!] p1,p2,p3 should not on same line
		//c=(p1+lineInt(p2,(p2-p1).l90(),p3,(p3-p1).l90()))/2; //this impl not good
		vec B=p2-p1,C=p3-p1; db D=B&C*2;
		c=vec(C.y*(B|B)-B.y*(C|C),B.x*(C|C)-C.x*(B|B))/D+p1;
		r=!(p1-c);
	}
	//inscribed cricle of triangle P1P2P3
	circle(Point p1, Point p2, Point p3, bool _){
		db x=!(p2-p3),y=!(p3-p1),z=!(p1-p2);
		c=(p1*x+p2*y+p3*z)/(x+y+z);
		r=lineDis(c,p1,p2-p1);
	}
	point angle(db theta){return c+point(theta)*r;}

	bool operator==(const circle &v) const{return c==v.c && eq(r-v.r);}
};


//point in or on circle
bool inCir(Point p, circle c){return sgn(!(c.c-p)-c.r)<=0;}

//return -1,0,1,2, ans[2]
int cirCross(circle A, circle B, point *ans){
	db d=!(A.c-B.c);
	if (eq(d)){
		if (eq(A.r-B.r)) return -1; //same circle
		return 0; //same center
	}
	if (sgn(d-fabs(A.r-B.r))<0) return 0; //inside
	if (sgn(A.r+B.r-d)<0) return 0; //too far
	db a=(B.c-A.c).ang();
	db da=angle(A.r,d,B.r);
	ans[0]=A.angle(a-da),ans[1]=A.angle(a+da);
	if (eq(da) || eq(da-PI)) return 1; //tang
	return 2; //normal inter
}

//get tangent points on circle from point p
//return  ans[2] : tangent point 
int cirTang(Point p, circle c, point *ans){
	db d=!(c.c-p);
	if (sgn(d-c.r)<0) return 0;
	if (eq(d-c.r)){ //[!] notice this time ans[0]-p0 not a line
		ans[0] = p; //ans[0]=(p-c.c).vert()+p; //to get a line
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
	db t1=(-f-sqrt(delta))/(2*e); //[i] t1 is closer to a because f<0
	db t2=(-f+sqrt(delta))/(2*e);
	point a1=a+v*t1, a2=a+v*t2;
	int cnt=0;
	if (sgn(t1)>=0 && sgn(t1-1)<=0) ans[cnt++]=a1;
	if (sgn(t2)>=0 && sgn(t2-1)<=0) ans[cnt++]=a2;
	return cnt;
}

//insection area of two circle a and b
//!-- test
db cirIntArea(circle a, circle b){
	db d=!(a.c-b.c);
	if (sgn(d-a.r-b.r)>=0) return 0; // too far
	if (sgn(d-fabs(a.r-b.r)<=0)) return PI*min(a.r,b.r)*min(a.r,b.r); //inside
	db hf=(a.r+b.r+d)/2;
	db s=-2*sqrt(hf*(hf-a.r)*(hf-b.r)*(hf-d));
	s+=angle(a.r,d,b.r)*a.r*a.r;
	s+=angle(b.r,d,a.r)*b.r*b.r;
	return s;
}

//UVA12304 get circles with radius r and other conditions
//circle passing A and B with radius r
// return ans[2]: center circle
int getCir(Point a, Point b, db r, point *ans){
	//circle A(a,r),B(b,r); return cirCross(A,B,r); //another implement
	db d=!(a-b)/2;
	if (sgn(d-r)<0) return 0;
	vec v=(b-a)/2;
	if (eq(d-r)) return ans[0]=a+v,1;
	ans[0]=a+v+v.vert()*sqrt(r*r-d*d);
	ans[1]=a+v-v.vert()*sqrt(r*r-d*d);
	return 2;
}
//circle with radius r passing point A and tangent with line P
int getCir(Point a, Point p, vec vp, db r, point *ans){
	if (eq(vp&a-p)){ //special judge point A on line P
		ans[0]=p+vp.vert()*r;
		ans[1]=p-vp.vert()*r;
		return 2;
	}
	//implement by line-cir-intersection 
	//point p1=p+vp.vert()*sgn(vp&a-p)*r; 
	//return lineInt(p1,p1+vp,circle(a,r));
	//independent implement
	point p0=lineProj(a,p,vp); db d=!(a-p0);
	if (sgn(2*r-d)<0) return 0;
	if (eq(2*r-d)) return ans[0]=(a+p0)/2,1;
	point p1=p0+vp.vert()*sgn(vp&a-p)*r;
	d-=r; d=sqrt(r*r-d*d);
	vp=vp.std()*d;
	ans[0]=p1+vp;
	ans[1]=p1-vp;
	return 2;
}
//circle with radius r and tangent with non-parallel line P and Q
int getCir(point p, vec vp, point q, vec vq, db r, point *ans){
	vec mvp=vp.vert()*r; //move dir
	vec mvq=vq.vert()*r;
	ans[0]=lineInt(p-mvp,vp,q-mvq,vq);
	ans[1]=lineInt(p-mvp,vp,q+mvq,vq);
	ans[2]=lineInt(p+mvp,vp,q-mvq,vq);
	ans[3]=lineInt(p+mvp,vp,q+mvq,vq);
	return 4;
}
//circle with radius r and tangent with disjoint circle c1 and c2
int getCir(circle c1, circle c2, db r, point *ans){
	return cirCross(circle(c1.c,c1.r+r),circle(c2.c,c2.r+r),ans);
}

//inverse circle C by  circle P with radius 1
circle inverseCir(Point p, circle c){
	db d=!(c.c-p);
	if (eq(c.r-d)) //get a line
		return circle(vec(inf,inf),inf);
	db d2=1/(d+c.r);
	db d1=1/(d-c.r);
	vec v=c.c-p; v=v/!v;
	return circle(p+v*(d1+d2)/2,(d1-d2)/2);
}
circle inverseCir(Point p, Point s, Vec v){
	point t=lineProj(p,s,v);
	db r=0.5/!(t-p); //radius
	return circle(p+(t-p)/!(t-p)*r,r);
}

//--poly--

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
bool inPoly(point p1, point p2, point *poly, int n){
	if (!inPoly(p1,poly,n) || !inPoly(p2,poly,n)) return 0;
	for (int i=0;i<n;i++)
		if (segCross(p1,p2,poly[i],poly[(i+1)%n]))
			return 0;
	return 1;
}
//point at border regard as in poly
const db epr=1e-5; //[!] epr should larger than eps*tan(angle(segment and poly-edge))
bool inPoly2(point p1, point p2, point *poly, int n){
	if (inPoly(p1*epr+p2*(1-epr),poly,n)==0 || inPoly(p2*epr+p1*(1-epr),poly,n)==0) return 0;
	for (int i=0;i<n;i++)
		if (segCross(p1,p2,poly[i],poly[(i+1)%n])==1)
			return 0;
	return 1;
}
bool outPoly(point p1, point p2, point *poly, int n){
	if (inPoly(p1,poly,n) || inPoly(p2,poly,n)) return 0;
	for (int i=0;i<n;i++)
		if (segCross(p1,p2,poly[i],poly[(i+1)%n]))
			return 0;
	return 1;
}
bool outPoly2(point p1, point p2, point *poly, int n){
	if (inPoly(p1*epr+p2*(1-epr),poly,n)==1 || inPoly(p2*epr+p1*(1-epr),poly,n)==1) return 0;
	for (int i=0;i<n;i++)
		if (segCross(p1,p2,poly[i],poly[(i+1)%n])==1)
			return 0;
	return 1;
}

// [!] Require simple polygon, or the result will be strange
db polyArea(point *p, int n){
	db sum=0;
	for (int i=1;i<n-1;i++)
		sum+=cross(p[0],p[i+1],p[i]);
	return fabs(sum)/2;
}

point polyBaryCenter(point *p, int n){
	point ret(0,0);
	for (int i=1;i<n-1;i++)
		ret=ret+(p[0]+p[i]+p[i+1])/3;
	return ret;
}

//convex hull, Andrew algo
// return  ans[m]
int convex(point *p, int n, point *ans){
	sort(p,p+n);
	n=unique(p,p+n)-p;
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

//test point P strictly in convex polygon, o(nlogn)
bool inConvex(point *p, int n, point q){ //require countclockwise convex hull
	if (sgn(cross(p[0],q,p[1]))>=0 || sgn(cross(p[0],p[n-1],q))>=0) return 0;
	int l=1,r=n-1;
	while (l<r-1){
		int m=l+r>>1;
		if (cross(p[0],p[m],q)>0) l=m;
		else r=m;
	}
	return sgn(cross(p[l],p[r],q))>0;
}

//cut convex polygon by line A, return right side of remain poly
int convexCut(point *p, int n, point a, vec v, point *ans){
	int c=0;
	for (int i=0;i<n;i++){
		int d1=sgn(v&p[i]-a);
		int d2=sgn(v&p[(i+1)%n]-a);
		if (d1>=0) ans[c++]=p[i];
		if (d1*d2<0) ans[c++]=lineInt(a,v,p[i],p[(i+1)%n]-p[i]); //cut
	}
	return c;
}

//weather point p is lefter than line l
bool onleft(point p, const line &l){return sgn(l.v&p-l.p)>0;}
const int maxp=1001;
line Q[maxp<<1]; //deque of lines
point T[maxp<<1]; //deque of points(result)
//intersection of left side half plane, return countclockwise polygon point
//[!] The result area can't be unlimited.
int halfplaneInt(line *l, int n, point *ans){
	sort(l,l+n); //[!] This operation changed input
	int head=0,tail=0; //rangeof Q:[head,tail] ; range of T: [head, tail)
	Q[0]=l[0];
	for (int i=1;i<n;i++){
		while (head<tail && !onleft(T[tail-1],l[i])) tail--;
		while (head<tail && !onleft(T[head],l[i])) head++;
		Q[++tail]=l[i];
		if (eq(Q[tail].v&Q[tail-1].v)){ //same direction
			--tail;
			if (onleft(l[i].p,l[i])) Q[tail]=l[i]; //replace righter line
		}
		if (head<tail) //get point
			T[tail-1]=lineInt(Q[tail-1].p,Q[tail-1].v,Q[tail].p,Q[tail].v);		
	}
	while (head<tail && !onleft(T[tail-1],Q[head])) tail--; 
	if (head>=tail-1) return 0;  //m<3, no available area
	T[tail]=lineInt(Q[head].p,Q[head].v,Q[tail].p,Q[tail].v); //head cross tail
	int m=0;
	for (int i=head;i<=tail;i++) ans[m++]=T[i];
	return m;
}
//half plane intersection with unlimted space judge
int halfplaneInt_(line *l, int n, point *ans){ //[!] array l should have 4 extra space
	l[n]=line(point(-inf,-inf),vec(1,0));
	l[n+1]=line(point(inf,-inf),vec(0,1));
	l[n+2]=line(point(inf,inf),vec(-1,0));
	l[n+3]=line(point(-inf,inf),vec(0,-1));
	int ret=halfplaneInt(l,n+4,ans);
	for (int i=0;i<ret;i++)
		if (fabs(ans[i].x)>inf/2 || fabs(ans[i].y)>inf/2)
			return -1; //unlimited
	return ret;
}

//--rotating stuck--

const int maxn=100010;
//max dis point pair on poly
// (farthest point pair on plane)
db polyDiam(point *p0, int n0){
	static point p[maxn];
	int n=convex(p0,n0,p); //[!] p0 changed
	p[n]=p[0];
	int opp=1; db ans=!(p[0]-p[1]);
	for (int i=0;i<n;i++){
		while (cross(p[i],p[i+1],p[opp+1])>cross(p[i],p[i+1],p[opp])) opp=(opp+1)%n;
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
		while (cross(p[i],p[i+1],p[opp+1])>cross(p[i],p[i+1],p[opp])) opp=(opp+1)%n;
		ans=min(ans, lineDis(p[opp],p[i],p[i+1]-p[i]));
	}
	return ans;
}
//min rectangle area cover polygon
db minRectCover(point *p0, int n0){
	static point p[maxn];
	int n=convex(p0,n0,p); //[!] p0 changed
	if (n<3) return 0;
	p[n]=p[0];
	db ans=-1;
	int h=1,r=1,l;
	for (int i=0;i<n;i++){
		while (cross(p[i],p[i+1],p[h+1])-cross(p[i],p[i+1],p[h])>=0) h=(h+1)%n; //farest
		while (dot(p[i],p[i+1],p[r+1])-dot(p[i],p[i+1],p[r])>=0) r=(r+1)%n; //rightest
		if (i==0) l=h;
		while (dot(p[i],p[i+1],p[l+1])-dot(p[i],p[i+1],p[l])<=0) l=(l+1)%n; //leftest
		db t=p[i+1]-p[i]|p[i+1]-p[i];
		db s=cross(p[i],p[i+1],p[h])*(dot(p[i],p[i+1],p[r])-dot(p[i],p[i+1],p[l]))/t; //rect area
		//min circumference of rectangle
		//db c=2*(cross(p[i],p[i+1],p[h])+dot(p[i],p[i+1],p[r])-dot(p[i],p[i+1],p[l]))/!(p[i+1]-p[i]);
		if (ans<0 || ans>s) ans=s;
	}
	return ans;
}
//minimum convex hull distanse (actually what support vector machine do on plane)
//[!] require non-cross countclockwise convex hull
db minConvexDis(point *p, int n, point *q, int m){ 
	p[n]=p[0]; q[n]=q[0];
	db ans=inf; int r=0;
	for (int i=1;i<m;i++)
		if (cross(p[0],p[1],q[i])>cross(p[0],p[1],q[r]))
			r=i;
	for (int i=0;i<n;i++){
		while (cross(p[i],p[i+1],q[r+1])>cross(p[i],p[i+1],q[r])){
			r=(r+1)%m;
			ans=min(ans,segDis(p[i],p[i+1],q[r],q[r+1]));
		}
	}
	return ans;
}
//inner common tangent line of two convex hull, O(n+m)
//return one of tangent line (postion in input array)
//[!] require non-corss countclockwise convex hull)
pair<int,int> convexInnerTang(point *p, int n, point *q, int m){ 
	p[n]=p[0]; q[n]=q[0];
	int r=0;
	for (int i=1;i<m;i++)
		if (cross(p[0],p[1],q[i])>cross(p[0],p[1],q[r]))
			r=i;
	for (int i=0;i<n;i++){
		while (cross(p[i],p[i+1],q[r+1])>cross(p[i],p[i+1],q[r])){
			r=(r+1)%m;
			if (cross(p[(i+n-1)%n],p[i],q[r])>=0 && cross(p[i],p[i+1],q[r])<0 &&
				cross(q[(r+m-1)%m],q[r],p[i])>=0 && cross(q[r],q[r+1],p[i])<0) //change here to get another tangent line
				return {i,r};
		}
	}
	throw;
}

//---complex---

//sector a~b of radius r
db secArea(point a, point b, db r){return r*r*angle(a,b)/2;}
db triArea(point p1, point p2){return fabs(p1&p2)/2;}
//intersection area of circle C and triangle P1-P2-C
db tri_cirArea(point p1, point p2, circle c){
	db r=c.r;
	p1=p1-c.c; p2=p2-c.c;
	c.c=vec(0,0);
	point p[2];
	if (sgn(!p1-r)<0){ //p1 in circle
		if (sgn(!p2-r)<0) return triArea(p1,p2);
		segInt(p1,p2,c,p);
		return triArea(p1,p[0])+secArea(p[0],p2,r);
	}
	if (sgn(!p2-r)<0){ //p2 in circle
		segInt(p1,p2,c,p);
		return secArea(p1,p[0],r)+triArea(p[0],p2);
	}
	int pc=segInt(p1,p2,c,p);
	if (pc==2) return secArea(p1,p[0],r)+triArea(p[0],p[1])+secArea(p[1],p2,r);
	return secArea(p1,p2,r);	
}
//intersection area of polygon P and circle C
db poly_cirArea(point *p, int n, circle c){
	db ans=0;
	for (int i=0;i<n;i++){
		db d=sgn(cross(c.c,p[i],p[(i+1)%n]));
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


//union area of circles
namespace Circles{
	const int N=1010; //O(n^2log(n))
	circle c[N];
	db ans[N],pre[N];
	int n;
	//remove inside or same circles
	void init(){ //[!] c[N] changed
		sort(c,c+n,[](const circle &a, const circle &b){return a.c==b.c?a.r<b.r:a.c<b.c;});
		n=unique(c,c+n)-c; //use circle::operator==
	}
	db arcarea(db rad, db r){return 0.5*r*r*(rad-sin(rad));}
	//union area of circles
	// ans[1] is union area
	// ans[i]-ans[i+1] is k times intersection area; [!] the circles should be unique
	db areaunion(){
		memset(ans,0,sizeof ans);
		vector<pair<db,int>> v; //int 1: start of section | -1: end of section
		init(); //delete inside; [!] should NOT init() when get k-times intersection
		for (int i=0;i<n;i++){
			v.clear();
			v.emplace_back(-PI,1); //default [-PI,PI] full circle
			v.emplace_back(PI,-1); 
			for (int j=0;j<n;j++) //label arc secions
				if (i^j){
					point q=c[j].c-c[i].c;
					db d=!q, x=c[i].r, y=c[j].r;
					if (sgn(d+x-y)<=0){ //cover by circle[j]
						v.emplace_back(-PI,1);
						v.emplace_back(PI,-1);
						continue;
					}
					if (sgn(d-x+y)<=0) continue; //cover circle[j]
					if (sgn(d-x-y)>0) continue; //too far
					db base=q.ang(), ang=angle(x,d,y);
					db a0=base-ang;	if (sgn(a0+PI)<0) a0+=2*PI;
					db a1=base+ang; if (sgn(a1-PI)>0) a1-=2*PI;
					v.emplace_back(a0,1);
					if (sgn(a0-a1)>0){ //arc across 180 degree
						v.emplace_back(PI,-1);
						v.emplace_back(-PI,1);
					}
					v.emplace_back(a1,-1);
				}
			sort(v.begin(),v.end());
			int cur=0;
			for (auto &a:v){ //point
				if (cur && sgn(a.first-pre[cur])){
					ans[cur]+=arcarea(a.first-pre[cur],c[i].r); //arcarea
					ans[cur]+=(c[i].angle(pre[cur])&c[i].angle(a.first))/2; //piece of center polygon area(signed)
				}
				cur+=a.second;
				pre[cur]=a.first;
			}
		}
		//for (int i=1;i<n;i++)
		//	ans[i]-=ans[i+1];
		return ans[1];
	}
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
	cout<<lineDis(point(0,0),d,vec(0,2.5)-d)<<" expect 2.23607\n";
	cout<<segDis(point(0,0),d,vec(0,2.5)-d)<<" expect 2.23607\n";
	cout<<segDis(point(0,5),d,vec(0,2.5)-d)<<" expect 2.5\n";
	cout<<lineProj(point(0,0),d,vec(4,0)-d)<<" expect 2 2\n";
	
	cout<<onLine(point(2,2),d,vec(4,0))<<" expect 1\n";
	cout<<onSeg(point(2,2),d,vec(4,0))<<" expect 0\n";
	cout<<onSeg(point(3.5,0.5),d,vec(4,0))<<" expect 1\n";
	cout<<onSeg(point(4,0),d,vec(4,0))<<" expect 1\n";
	
	cout<<segCross(point(2,2),point(0,0),d,vec(0,4))<<" expect 2\n";
	cout<<segCross(point(3,3),point(0,0),d,vec(0,4))<<" expect 1\n";
	cout<<segCross(point(0,4),point(0,0),d,vec(0,4))<<" expect 2\n";
	cout<<segCross(point(1,1),point(0,0),d,vec(0,4))<<" expect 0\n";
	cout<<segCross(point(2,2),point(-1,5),d,vec(0,4))<<" expect -1\n";
	cout<<segCross(point(0,4),point(-1,5),d,vec(0,4))<<" expect -1\n";
	
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

	{
	using namespace Circles;
	n=2;
	Circles::c[0]=circle(vec(0,0),1);
	Circles::c[1]=circle(vec(0,1),1);
	areaunion();
	cout<<Circles::ans[1]<<" expect 5.048156\n";
	}
}
}
#include <iomanip>
using namespace std;
int main(){
	using namespace CalcGeo;
	test();
}
