#include "base.cpp"

namespace Geo3D{

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
	db x,y,z;
	vec():x(0),y(0){}
	vec(db x, db y, db z):x(x),y(y),z(z){}
	vec(db theta):x(cos(theta)),y(sin(theta)){}

	bool operator==(Vec v) const{return eq(x-v.x) && eq(y-v.y) && eq(z-v.z);}
	
	vec operator+(Vec v) const{return vec(x+v.x,y+v.y,z+v.z);}
	vec operator-(Vec v) const{return vec(x-v.x,y-v.y,z-v.z);}
	vec operator*(db a) const{return vec(x*a,y*a,z*a);}
	vec operator/(db a) const{return vec(x/a,y/a,z/a);}
	
	//dot
	db operator|(Vec v) const{return x*v.x+y*v.y+z*v.z;}
	//cross
	vec operator&(Vec v) const{return vec(y*v.z-z*v.y,z*v.x-x*v.z,x*v.y-y*v.x);}
	//len
	db operator!() const{return sqrt(x*x+y*y+z*z);}
	
	friend ostream& operator<<(ostream &o, Vec v){
		o<<v.x<<','<<v.y<<','<<v.z;
		return o;
	}
};
typedef vec point;

db angle(Vec a, Vec b){return atan2(!(a&b),a|b);}
vec cross(Point a, Point b, Point c){return b-a & c-a;}
db dot(Point a, Point b, Point c){return b-a | c-a;}

//mixed product
db volume6(Point a, Point b, Point c, Point d){
	return b-a&c-a|d-a;
}

//point projection on line S+tV
point lineProj(Point p, Point s, Vec v){
	return s+v*(v|p-s)/(v|v);
}
//symmetric point of P about line S+tV
point symmetric(Point p, Point s, Vec v){
	return lineProj(p,s,v)*2-p;
}
//distance of p to line S+tV
db lineDis(Point p, Point s, Vec v){
	return !(v & p-s)/!v;
}
//distance of p to segment S+tV
db segDis(Point p, Point s, Vec v){
	if (eq(!v)) return !(s-p); //single point
	vec v2=p-s,v3=p-s-v;
	if ((v|v2)<0) return !v2;
	else if ((v|v3)>0) return !v3;
	return !(v&v2)/!v;
}
//distance of seg A-B and seg C-D
db segDis(Point a, Point b, Point c, Point d){
	vec u=b-a, v=d-c;
	return min(min(segDis(c,a,u),segDis(d,a,u)),min(segDis(a,c,v),segDis(b,c,v)));
}
//point is on line
bool onLine(Point p, Point a, Point b){return eq(!(p-a&b-a));}
//point on seg [a,b]
bool onSeg(Point p, Point a, Point b){return eq(!(p-a&b-a)) && sgn(a-p|b-p)<=0;}

//rot point P by line S+tV ang rads countclockwise
point rot(Point p, Point s, Vec v, db ang){
	if (eq(!(v&p-s))) return p;
	point f1=v&p-s;
	point f2=f1&v;
	db d=!f1/!v;
	f1=f1/!f1*d; 
	f2=f2/!f2*d;
	return p-f2+f1*cos(ang)-f2*sin(ang);
}

struct plane{
	point p;
	vec v; //normal vector
	plane(){}
	plane(Point p, Vec v):p(p),v(v){}
	plane(Point a, Point b, Point c):p(a),v(cross(a,b,c)){}
	//ax+by+cz+d=0
	plane(db a, db b, db c, db d){
		v=vec(a,b,c);
		if (sgn(a)) p=point((-d-c-b)/a,1,1);
		else if (sgn(b)) p=point(1,(-d-c-a)/b,1);
		else p=point(1,1,(-d,-a,-b)/c);
	}
};
//point is on plane
bool onPlane(Point p, plane f){
	return eq(dot(f.p,p,f.v));
}
//line s cross plane f
int lineInt(point s, vec v, plane f, point &ans){
	db d=v|f.v;
	if (eq(d)) return 0; //parallel
	ans=s-v/d*(s|f.v);
	return 1;
}
//porjection of point p on plane f
point planeProj(point p, plane f){
	point ans;
	lineInt(p,f.v,f,ans);
	return ans;
}
//plane a cross plane b, get a line
int planeInt(plane a, plane b, point &s, point &v){
	v=a.v&b.v;
	if (eq(!v)) return 0;
	point t=a.v&v;
	s=a.p+t/fabs(b.v|t)*(b.v|b.p-a.p);
	return 1;
}

struct sphere{
	point o; db r;
	sphere(){}
	sphere(Point o, db r):o(o),r(r){}
	sphere(Point a, Point b):o((a+b)/2),r(!(a-b)/2){}
	//min sphere passing point A,B,C
	sphere(Point a, Point b, Point c){ //[!] a,b,c should not on same line
		vec h1=b-a,h2=c-a,h3=cross(a,b,c); //three plane intersection
		point m1=(a+b)/2,m2=(a+c)/2;
		db d1=h1|m1,d2=h2|m2,d3=h3|a,t; //ax+by+cz=d
		if (fabs(h1.x)<fabs(h2.x)) swap(h1,h2),swap(d1,d2); //gauss
		if (fabs(h1.x)<fabs(h3.x)) swap(h1,h3),swap(d1,d3);
		if (sgn(h2.x)) t=h1.x/h2.x, h2=h1-h2*t, d2=d1-d2*t;
		if (sgn(h3.x)) t=h1.x/h3.x, h3=h1-h3*t, d3=d1-d3*t;
		
		if (fabs(h2.y)<fabs(h3.y)) swap(h2,h3),swap(d2,d3);
		if (sgn(h3.y)) t=h2.y/h3.y, h3=h2-h3*t, d3=d2-d3*t;
		o.z=d3/h3.z;
		o.y=(d2-o.z*h2.z)/h2.y;
		o.x=(d1-o.z*h1.z-o.y*h1.y)/h1.x;
		r=!(a-o);
	}
	//sphere on passing A,B,C,D
	sphere(Point a, Point b, Point c, Point d){ //[!] a,b,c should not collinear or coplanear
		vec h1=b-a,h2=c-a,h3=d-a; //three plane intersection
		point m1=(a+b)/2,m2=(a+c)/2,m3=(a+d)/2;
		db d1=h1|m1,d2=h2|m2,d3=h3|m3,t; //ax+by+cz=d
		if (fabs(h1.x)<fabs(h2.x)) swap(h1,h2),swap(d1,d2); //gauss
		if (fabs(h1.x)<fabs(h3.x)) swap(h1,h3),swap(d1,d3);
		if (sgn(h2.x)) t=h1.x/h2.x, h2=h1-h2*t, d2=d1-d2*t;
		if (sgn(h3.x)) t=h1.x/h3.x, h3=h1-h3*t, d3=d1-d3*t;
		
		if (fabs(h2.y)<fabs(h3.y)) swap(h2,h3),swap(d2,d3);
		if (sgn(h3.y)) t=h2.y/h3.y, h3=h2-h3*t, d3=d2-d3*t;
		o.z=d3/h3.z;
		o.y=(d2-o.z*h2.z)/h2.y;
		o.x=(d1-o.z*h1.z-o.y*h1.y)/h1.x;
		r=!(a-o);
	}
};

//convex hull 3D
namespace CH3D{

const int N=1010; //O(n^2)
point p[N];
struct face{
	int v[3]; //index on p
};
vector<face> ans;
bool vis[N][N];
void convex(int n){
	vector<face> nxt;
	//make first face not collineration; [!] point p changed
	for (int i=2;i<n;i++) if (sgn(!cross(p[0],p[1],p[i]))){swap(p[2],p[i]);break;}
	for (int i=3;i<n;i++) if (sgn(volume6(p[0],p[1],p[2],p[i]))) {swap(p[3],p[i]);break;}
	if (eq(volume6(p[0],p[1],p[2],p[3]))) return; //all on same line
	ans.push_back((face){{1,2,0}}); 
	ans.push_back((face){{2,1,0}}); //another direction. algo will select one auto.
	for (int i=3;i<n;i++){ //adding points
		nxt.clear();
		for (auto &f:ans){ //remove visable face
			bool see=sgn(volume6(p[f.v[0]],p[f.v[1]],p[f.v[2]],p[i]))>=0; //assume coplanear face visable, so previous coplanear point will be deleted
			if (!see) nxt.push_back(f);
			for (int k=0;k<3;k++) vis[f.v[k]][f.v[(k+1)%3]]=see; //label edges
		}
		if (nxt.size()==ans.size()) continue;
		for (auto &f:ans)
			for (int k=0;k<3;k++){
				int a=f.v[k],b=f.v[(k+1)%3];
				if (!vis[b][a] && vis[a][b])
					nxt.push_back((face){{a,b,i}}),vis[a][b]=1;
			}
		ans.swap(nxt);//update to ans
	}
}

//--polyhedron--

db volume(){
	db sum=0;
	for (auto &f:ans)
		sum+=volume6(p[0],p[f.v[0]],p[f.v[1]],p[f.v[2]]);
	return fabs(sum/6);
}
point barycenter(){
	point s(0,0,0);
	db sum=0;
	for (auto &f:ans){
		db v=volume6(p[0],p[f.v[0]],p[f.v[1]],p[f.v[2]]);
		sum+=v;
		s=s+(p[0]+p[f.v[0]]+p[f.v[1]]+p[f.v[2]])/4*v;
	}
	return s/sum;
}

}// namespace CH3D

void test(){
	point p1(0,0,0),p2(1,0,0),p3(0,1,0),p4(0,0,1);
	printf("%f expected 1\n",volume6(p1,p2,p3,p4));
	cout<<rot(p3,p1,p2,PI/4)<<" expect 0,-0.707,-0.707\n";
	plane f(p1,vec(1,1,1));
	vec ans;
	lineInt(p4,p3+p2,f,ans);
	cout<<ans<<" expect -0.5,-0.5,1\n";
	cout<<planeProj(p4,f)<<" expect -0.3333,-0.3333,0.6667\n";
	point pv;
	planeInt(f,plane(p2,p2),ans,pv);
	cout<<ans<<' '<<pv<<" expect 1,-0.5,-0.5 0,k,-k\n";
	sphere ball(p1,p2,p3);
	cout<<ball.o<<' '<<ball.r<<" expect 0.5,0.5,0 0.707\n";
	ball=sphere(p1,p2,p3,p4);
	cout<<ball.o<<' '<<ball.r<<" expect 0.5,0.5,0.5 0.866\n";

	{
		using namespace CH3D;
		inc(i,2) inc(j,2) inc(k,2) p[i*4+j*2+k]=vec(i,j,k);
		convex(8);
		for (auto &f:CH3D::ans)
			cout<<p[f.v[0]]<<' '<<p[f.v[1]]<<' '<<p[f.v[2]]<<'\n';

		cout<<volume()<<" expect 1\n";
		cout<<barycenter()<<" expect 0.5,0.5,0.5\n";

	}
}

} //end namespace Geo3D

int main(){
	Geo3D::test();
	return 0;
}
