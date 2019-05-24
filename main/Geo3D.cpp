#include "base.cpp"

namespace Geo3D{

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
	db x,y,z;
	vec():x(0),y(0){}
	vec(db x, db y, db z):x(x),y(y),z(z){}
	vec(db theta):x(cos(theta)),y(sin(theta)){}

	bool operator==(Vec v) const{return eq(x-v.x) && eq(y-v.y) && eq(z-v.z);}
	
	vec operator+(Vec v) const{return vec(x+v.x,y+v.y,z+v.z);}
	vec operator-(Vec v) const{return vec(x-v.x,y-v.y,z-v.z);}
	vec operator*(db a) const{return vec(x*a,y*a,z*a);}
	vec operator/(db a) const{return vec(x/a,y/a,z/a);}
	
	db operator|(Vec v) const{return x*v.x+y*v.y+z*v.z;} //dot
	vec operator&(Vec v) const{return vec(y*v.z-z*v.y,z*v.x-x*v.z,x*v.y-y*v.x);} //cross
	db operator!() const{return sqrt(x*x+y*y+z*z);} //len
	
	friend ostream& operator<<(ostream &o, Vec v){
		o<<v.x<<','<<v.y<<','<<v.z;
		return o;
	}
};
typedef vec point;

db angle(Vec a, Vec b){return atan2(!(a&b),a|b);}
vec cross(Point a, Point b, Point c){return b-a & c-a;}
db dot(Point a, Point b, Point c){return b-a | c-a;}

//mixtured product; 6-times directed volume
db vol6(Point a, Point b, Point c, Point d){
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

//rot point P by line S+tV ang rads clockwise(see from s to t)
point rot(Point p, Point s, Vec v, db ang){
	if (eq(!(v&p-s))) return p;
	point f1=v&p-s;
	point f2=f1&v;
	f1=f1/!v; 
	f2=f2/!f2*!f1;
	return p-f2+f1*sin(ang)+f2*cos(ang);
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
		else p=point(1,1,(-d-a-b)/c);
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
	ans=s+v/d*(f.p-s|f.v);
	return 1;
}
//porjection of point p on plane f
point planeProj(point p, plane f){
	db d=f.v|f.v;
	return p+f.v/d*(f.p-p|f.v);
}
//plane a cross plane b, get a line
int planeInt(plane a, plane b, point &s, point &v){
	v=a.v&b.v;
	if (eq(!v)) return 0; //parallel
	point t=a.v&v;
	s=a.p+t/fabs(b.v|t)*(b.v|b.p-a.p); //s is cent pos
	return 1;
}

//area of triangle on unit sphere
db angle3d_sptri(Point x, Point y, Point z){
	vec a=x&y,b=y&z,c=x&z;
	return angle(a,b)+angle(b,c)+angle(a,c)-PI;
}
//triangle projection on unit sphere
db angle3d_tri(Point x, Point y, Point z){
	db a=angle(x,y),b=angle(y,z),c=angle(x,z);
	db s=(a+b+c)/2;
	return 4*atan(sqrt(tan(s/2)*tan(s/2-a/2)*tan(s/2-b/2)*tan(s/2-c/2)));
}

struct sphere{
	point o; db r;
	sphere(){}
	sphere(Point o, db r):o(o),r(r){}
	sphere(Point a, Point b):o((a+b)/2),r(!(a-b)/2){}
	//min sphere passing point A,B,C
	//[!] a,b,c should not on same line
	sphere(Point a, Point b, Point c){ 
		vec h1=b-a,h2=c-a,h3=b&c; //three plane intersection
		vec g=vec(h1|h1,h2|h2,0)/2;   //ax+by+cz=g
		vec g1=vec(h1.x,h2.x,h3.x); //transfer
		vec g2=vec(h1.y,h2.y,h3.y);
		vec g3=vec(h1.z,h2.z,h3.z);
		db s=g1&g2|g3;              //Cramer's Rule
		o=vec(g&g2|g3,g1&g|g3,g1&g2|g)/s + a; 
		r=!(a-o);
	}
	 //[!] a,b,c,d should not collinear or coplanear
	sphere(Point a, Point b, Point c, Point d){
		vec h1=b-a,h2=c-a,h3=d-a; //three plane intersection
		vec g=vec(h1|h1,h2|h2,h3|h3)/2;   //ax+by+cz=g
		vec g1=vec(h1.x,h2.x,h3.x); //transfer
		vec g2=vec(h1.y,h2.y,h3.y);
		vec g3=vec(h1.z,h2.z,h3.z);
		db s=g1&g2|g3;              //Cramer's Rule
		o=vec(g&g2|g3,g1&g|g3,g1&g2|g)/s + a; 
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
void convex(int n){ //[i] as result, cross(p[v[0]],p[v[1]],p[v[2]]) towards outside of poly
	vector<face> nxt;
	//make first face not collineration; [!] point p changed
	for (int i=2;i<n;i++) if (sgn(!cross(p[0],p[1],p[i]))){swap(p[2],p[i]);break;}
	for (int i=3;i<n;i++) if (sgn(vol6(p[0],p[1],p[2],p[i]))) {swap(p[3],p[i]);break;}
	if (eq(vol6(p[0],p[1],p[2],p[3]))) return; //all on same line
	ans.push_back((face){{1,2,0}}); 
	ans.push_back((face){{2,1,0}}); //another direction. algo will select one auto.
	for (int i=3;i<n;i++){ //adding points
		nxt.clear();
		for (auto &f:ans){ //remove visable face
			bool see=sgn(vol6(p[f.v[0]],p[f.v[1]],p[f.v[2]],p[i]))>=0; //assume coplanear face visable, so previous coplanear point will be deleted
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

db volume(){ //[!] the input face should towards same side
	db sum=0;
	for (auto &f:ans)
		sum+=vol6(p[0],p[f.v[0]],p[f.v[1]],p[f.v[2]]);
	return fabs(sum/6);
}
point barycenter(){ //[!] the input face should towards same side
	point s(0,0,0);
	db sum=0;
	for (auto &f:ans){
		db v=vol6(p[0],p[f.v[0]],p[f.v[1]],p[f.v[2]]);
		sum+=v;
		s=s+(p[0]+p[f.v[0]]+p[f.v[1]]+p[f.v[2]])/4*v;
	}
	return s/sum;
}

//point s is in or on polygon
//return  1(in), 0(out), -1(on border)
/*
int inPoly(Point s){ //[!] the input face should towards outside
	auto rdi=[](){return rand()%10+1;};
start:
	vec v=vec(rdi(),rdi(),rdi());
	int w=0;
	for (auto &f: ans){
		point cp;
		int ret=lineInt(s,v,plane(p[f.v[0]],p[f.v[1]],p[f.v[2]]),cp);
		if (!ret || sgn(cp-s|v)<0) continue;
		int s1=sgn(!cross(p[f.v[0]],p[f.v[1]],cp)); //TODO : bug here
		int s2=sgn(!cross(p[f.v[0]],cp,p[f.v[2]])); //how to test point in 3d triangle?
		int s3=sgn(!cross(p[f.v[1]],cp,p[f.v[0]]));
		int s4=sgn(!cross(p[f.v[1]],p[f.v[2]],cp));
		if (s1==1 && s2==1 && s3==1 && s4==1){
			if (sgn(cp-s|v)==0) return -1;
			w+=sgn(vol6(p[f.v[0]],p[f.v[1]],p[f.v[2]],s));
		}
		if ((s1||s2||s3||s4) == 0){
			if (sgn(cp-s|v)==0) return -1;
			goto start;
		}
	}
	return w!=0;
}
*/
//another impl, return sum of angle3d
db inPoly2(Point s){
	db w=0;
	for (auto &f: ans) 
		w+=sgn(vol6(s,p[f.v[0]],p[f.v[1]],p[f.v[2]]))*angle3d_tri(p[f.v[0]]-s,p[f.v[1]]-s,p[f.v[2]]-s);
	return w;
}

}// namespace CH3D

void test(){
	point p1(0,0,0),p2(1,0,0),p3(0,1,0),p4(0,0,1);
	printf("%f expected 1\n",vol6(p1,p2,p3,p4));
	cout<<rot(p3,p1,p2,PI/4)<<" expect 0,0.707,0.707\n";
	cout<<rot(p3,p1,p2,-PI/4)<<" expect 0,0.707,-0.707\n";
	cout<<rot(p3,p1,p2,PI/2)<<" expect 0,0,1\n";
	cout<<rot(p3,p1,p2,PI)<<" expect 0,-1,0\n";
	plane f(p1,vec(1,1,1));
	vec ans;
	lineInt(p4,p1-p3-p2,f,ans);
	cout<<ans<<" expect -0.5,-0.5,1\n";
	cout<<planeProj(p4,f)<<" expect -0.3333,-0.3333,0.6667\n";
	point pv;
	planeInt(f,plane(p2,p2),ans,pv);
	cout<<ans<<' '<<pv<<" expect 1,0.5,0.5 0,k,-k\n";
	sphere ball({1,1,0},p2,p3);
	cout<<ball.o<<' '<<ball.r<<" expect 0.5,0.5,0 0.707\n";
	ball=sphere({1,1,1},{1,0,1},{0,1,1},{1,1,0});
	cout<<ball.o<<' '<<ball.r<<" expect 0.5,0.5,0.5 0.866\n";
	
	{
		using namespace CH3D;
		inc(i,2) inc(j,2) inc(k,2) p[i*4+j*2+k]=vec(i,j,k);
		convex(8);
		for (auto &f:CH3D::ans)
			cout<<p[f.v[0]]<<' '<<p[f.v[1]]<<' '<<p[f.v[2]]<<'\n';

		cout<<volume()<<" expect 1\n";
		cout<<barycenter()<<" expect 0.5,0.5,0.5\n";

		cout<<inPoly({0.5,0.5,0.5})<<" expect 1\n";
		cout<<inPoly({0,0.5,0.5})<<" expect -1\n";
		cout<<inPoly({1.5,0.5,0.5})<<" expect 0\n";
		
		cout<<inPoly2({0.5,0.5,0.5})<<" expect 4*pi\n";
	}
}

} //end namespace Geo3D

int main(){
	Geo3D::test();
	return 0;
}
