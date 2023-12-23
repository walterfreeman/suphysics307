/**********************************************
anim.c, simple animation routine using OpenGL/GLUT
Written by Walter Freeman

Compile (on Linux) with
gcc anim.c -lGL -lGLU -lglut -lm

Compile (on Mac) with
gcc anim.c -framework GLUT -framework OpenGL -framework Cocoa
**********************************************/

//#include <GL/glew.h>
//#include <GL/glut.h>      // for Linux
//#include <GL/freeglut.h>      // for Linux
//#include <GL/glext.h>      // for Linux
#include <GLUT/glut.h>       // for Macs 
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include "vector.h"
#include <unistd.h>
#include <string.h>

#define timing_hack 0
// #define ANIM_FONT GLUT_BITMAP_HELVETICA_18
#define NB 500
#define BL 10000

int f_bufsize=8192;
int d_bufsize=8192;
vector trail[BL][NB];
double *d_buffer;
float *f_buffer;
int spherecounter=0;
int force_2d_frame=0;
void* ANIM_FONT = GLUT_BITMAP_HELVETICA_18;
int sunlight=0;
int traillen[NB]={BL};
int rbl[NB]={0};
int rbocc[NB]={0};
int circfaces=12;
int window_size_override=0;
char textbuf[40];
int window_size=800,window_size_x=800,window_size_y=800;
double scale=4.25, lastscale=4.25, scale2, vdist2;
int fpsdisplay=1;
int update=0;
int help=0;
int need_guesses=1;
float spec=1;
int lmx=-1,lmy=-1;
double mcurx, mcury;
double fps=60;
double lastdraw=0;
vector center(0,0,0), fcenter(0,0,0), center2,sunvec(0,0,0);
int axes=0;
int track=0; // are we currently following the user's mouse movement?
double tx,ty,tz=0;
float modmat[16], invmodmat[16], projmat[16], invprojmat[16];
double contrast=1;
double vdist=12, lastvdist=12;
int ctog=1;
double theta=M_PI/4,phi=0,psi=4*M_PI/3;
double theta2=M_PI/4;
double phi2=0;
double xocenter,yocenter,zocenter;
double psi2=4*M_PI/3;
double costheta=1,sintheta=0,cosphi=0,sinphi=1,cospsi=1,sinpsi=0;
int td=0;   // flag for 3D mode
int adef=1; // flag for whether or not we should just use the default preference for axes (off in 3d, on in 2d)
int inverse=0;
double gx=0.5,gy=0.4,gz=0.3;
double red=1;
double green=1;
double blue=1;
double globalgamma=1;

void save_config(void);
void load_config(void);


vector rotate_arb(vector v, vector a, double th)
{
  vector res; res.x=res.y=res.z=0;
  a=normalize(a);


  res.x += v.x * (cos(th) + a.x*a.x*(1-cos(th)));
  res.y += v.y * (cos(th) + a.y*a.y*(1-cos(th)));
  res.z += v.z * (cos(th) + a.z*a.z*(1-cos(th)));

  res.x += v.y * (a.x*a.y*(1-cos(th)) - a.z * sin(th));
  res.y += v.z * (a.y*a.z*(1-cos(th)) - a.x * sin(th));
  res.z += v.x * (a.z*a.x*(1-cos(th)) - a.y * sin(th));

  res.x += v.z * (a.x*a.z*(1-cos(th)) + a.y * sin(th));
  res.y += v.x * (a.y*a.x*(1-cos(th)) + a.z * sin(th));
  res.z += v.y * (a.z*a.y*(1-cos(th)) + a.x * sin(th));


  return res;
}


bool gluInvertMatrix(const float m[16], float invOut[16])
{
    float inv[16], det;
    int i;

    inv[0] = m[5]  * m[10] * m[15] - 
             m[5]  * m[11] * m[14] - 
             m[9]  * m[6]  * m[15] + 
             m[9]  * m[7]  * m[14] +
             m[13] * m[6]  * m[11] - 
             m[13] * m[7]  * m[10];

    inv[4] = -m[4]  * m[10] * m[15] + 
              m[4]  * m[11] * m[14] + 
              m[8]  * m[6]  * m[15] - 
              m[8]  * m[7]  * m[14] - 
              m[12] * m[6]  * m[11] + 
              m[12] * m[7]  * m[10];

    inv[8] = m[4]  * m[9] * m[15] - 
             m[4]  * m[11] * m[13] - 
             m[8]  * m[5] * m[15] + 
             m[8]  * m[7] * m[13] + 
             m[12] * m[5] * m[11] - 
             m[12] * m[7] * m[9];

    inv[12] = -m[4]  * m[9] * m[14] + 
               m[4]  * m[10] * m[13] +
               m[8]  * m[5] * m[14] - 
               m[8]  * m[6] * m[13] - 
               m[12] * m[5] * m[10] + 
               m[12] * m[6] * m[9];

    inv[1] = -m[1]  * m[10] * m[15] + 
              m[1]  * m[11] * m[14] + 
              m[9]  * m[2] * m[15] - 
              m[9]  * m[3] * m[14] - 
              m[13] * m[2] * m[11] + 
              m[13] * m[3] * m[10];

    inv[5] = m[0]  * m[10] * m[15] - 
             m[0]  * m[11] * m[14] - 
             m[8]  * m[2] * m[15] + 
             m[8]  * m[3] * m[14] + 
             m[12] * m[2] * m[11] - 
             m[12] * m[3] * m[10];

    inv[9] = -m[0]  * m[9] * m[15] + 
              m[0]  * m[11] * m[13] + 
              m[8]  * m[1] * m[15] - 
              m[8]  * m[3] * m[13] - 
              m[12] * m[1] * m[11] + 
              m[12] * m[3] * m[9];

    inv[13] = m[0]  * m[9] * m[14] - 
              m[0]  * m[10] * m[13] - 
              m[8]  * m[1] * m[14] + 
              m[8]  * m[2] * m[13] + 
              m[12] * m[1] * m[10] - 
              m[12] * m[2] * m[9];

    inv[2] = m[1]  * m[6] * m[15] - 
             m[1]  * m[7] * m[14] - 
             m[5]  * m[2] * m[15] + 
             m[5]  * m[3] * m[14] + 
             m[13] * m[2] * m[7] - 
             m[13] * m[3] * m[6];

    inv[6] = -m[0]  * m[6] * m[15] + 
              m[0]  * m[7] * m[14] + 
              m[4]  * m[2] * m[15] - 
              m[4]  * m[3] * m[14] - 
              m[12] * m[2] * m[7] + 
              m[12] * m[3] * m[6];

    inv[10] = m[0]  * m[5] * m[15] - 
              m[0]  * m[7] * m[13] - 
              m[4]  * m[1] * m[15] + 
              m[4]  * m[3] * m[13] + 
              m[12] * m[1] * m[7] - 
              m[12] * m[3] * m[5];

    inv[14] = -m[0]  * m[5] * m[14] + 
               m[0]  * m[6] * m[13] + 
               m[4]  * m[1] * m[14] - 
               m[4]  * m[2] * m[13] - 
               m[12] * m[1] * m[6] + 
               m[12] * m[2] * m[5];

    inv[3] = -m[1] * m[6] * m[11] + 
              m[1] * m[7] * m[10] + 
              m[5] * m[2] * m[11] - 
              m[5] * m[3] * m[10] - 
              m[9] * m[2] * m[7] + 
              m[9] * m[3] * m[6];

    inv[7] = m[0] * m[6] * m[11] - 
             m[0] * m[7] * m[10] - 
             m[4] * m[2] * m[11] + 
             m[4] * m[3] * m[10] + 
             m[8] * m[2] * m[7] - 
             m[8] * m[3] * m[6];

    inv[11] = -m[0] * m[5] * m[11] + 
               m[0] * m[7] * m[9] + 
               m[4] * m[1] * m[11] - 
               m[4] * m[3] * m[9] - 
               m[8] * m[1] * m[7] + 
               m[8] * m[3] * m[5];

    inv[15] = m[0] * m[5] * m[10] - 
              m[0] * m[6] * m[9] - 
              m[4] * m[1] * m[10] + 
              m[4] * m[2] * m[9] + 
              m[8] * m[1] * m[6] - 
              m[8] * m[2] * m[5];

    det = m[0] * inv[0] + m[1] * inv[4] + m[2] * inv[8] + m[3] * inv[12];

    if (det == 0)
        return false;

    det = 1.0 / det;

    for (i = 0; i < 16; i++)
        invOut[i] = inv[i] * det;

    return true;
}

void rotate (float v1[], GLfloat mmat[])
{
  float v2[3];
  v2[0] = v1[0] * mmat[0] + v1[1] * mmat[4] + v1[2] * mmat[8];
  v2[1] = v1[0] * mmat[1] + v1[1] * mmat[5] + v1[2] * mmat[9];
  v2[2] = v1[0] * mmat[2] + v1[1] * mmat[6] + v1[2] * mmat[10];
  v1[0]=v2[0];
  v1[1]=v2[1];
  v1[2]=v2[2];
}

vector rotate(vector v1, GLfloat mmat[])
{
  vector v2;
  v2.x = v1.x * mmat[0] + v1.y * mmat[4] + v1.z * mmat[8];
  v2.y = v1.x * mmat[1] + v1.y * mmat[5] + v1.z * mmat[9];
  v2.z = v1.x * mmat[2] + v1.y * mmat[6] + v1.z * mmat[10];
  return v2;
}
void sphere_face(vector c, double r, vector v1, vector v2, vector v3, int l)
{
  vector temp;
//  if (drand48() > 0.5) {temp=v1; v1=v2; v2=temp;}
//  temp=v1; v1=v2; v2=temp;
  glColor4f(v1.x/2+0.5,v1.y/2+0.5,v1.z/2+0.5,1);
  if (l==0)
  {
    glBegin(GL_TRIANGLES);
      glNormal3d(v1.x,v1.y,v1.z);
//      printf("set normal to %e,%e,%e at %e,%e,%e\n",v1.x,v1.y,v1.z,r*v1.x+c.x, r*v1.y+c.y, r*v1.z+c.z);
//      glNormal3d(1,1,1);
      glVertex3d(r*v1.x+c.x, r*v1.y+c.y, r*v1.z+c.z);
      glNormal3d(v2.x,v2.y,v2.z);
//      printf("set normal to %e,%e,%e at %e,%e,%e\n",v2.x,v2.y,v2.z,r*v2.x+c.x, r*v2.y+c.y, r*v2.z+c.z);
      glVertex3d(r*v2.x+c.x, r*v2.y+c.y, r*v2.z+c.z);
      glNormal3d(v3.x,v3.y,v3.z);
//      printf("set normal to %e,%e,%e at %e,%e,%e\n",v3.x,v3.y,v3.z,r*v3.x+c.x, r*v3.y+c.y, r*v3.z+c.z);
      glVertex3d(r*v3.x+c.x, r*v3.y+c.y, r*v3.z+c.z);
   glEnd();
  }
  else
  {
    sphere_face (c, r, normalize((v1+v2)/2), normalize((v1+v3)/2), normalize((v2+v3)/2),l-1);
    sphere_face (c, r, normalize((v1)/2), normalize((v1+v3)/2), normalize((v2+v1)/2),l-1);
    sphere_face (c, r, normalize((v2)/2), normalize((v1+v2)/2), normalize((v2+v3)/2),l-1);
    sphere_face (c, r, normalize((v1+v3)/2),  normalize((v3)/2), normalize((v2+v3)/2),l-1);
  }
}
void recurse_sphere(vector c, double r, int l)
{
  static vector xh(1,0,0);
  static vector yh(0,1,0);
  static vector zh(0,0,1);
  vector v1(xh);
  vector v2(yh);
  vector v3(-1*xh);
  vector v4(-1*yh);
  vector v5(zh);
  vector v6(-1*zh);
  sphere_face(c, r, v4, v1, v5, l);
  sphere_face(c, r, v1, v2, v5, l);
  sphere_face(c, r, v2, v3, v5, l);
  sphere_face(c, r, v3, v4, v5, l);
  sphere_face(c, r, v1, v4, v6, l);
  sphere_face(c, r, v2, v1, v6, l);
  sphere_face(c, r, v3, v2, v6, l);
  sphere_face(c, r, v4, v3, v6, l);
}

void vvert(vector v)
{
  glVertex3f(v.x, v.y, v.z);
}


void clamp(float &v)
{
  if (v > 1) v=1;
  if (v < 0) v=0;
}

void myColor4f(float r, float g, float b, float a)
{
//  a=pow(a,1/contrast);
  float col[]={r,g,b,a};
  clamp(r); clamp(g); clamp(b); clamp(a);
  float invcol[]={1.0f-(g+b)*0.5f,1.0f-(b+r)*0.5f,1.0f-(g+r)*0.5f,a};
  float spec[]={sqrt(r)/2,sqrt(g)/2,sqrt(b)/2,a};
  float amb[]={(float)r*0.2f, (float)g*0.2f, (float)b*0.2f};
  if (inverse == 0)
    glMaterialfv(GL_FRONT_AND_BACK, GL_DIFFUSE, col);
  else
    glMaterialfv(GL_FRONT_AND_BACK, GL_DIFFUSE, invcol);
  
  glMaterialfv(GL_FRONT_AND_BACK, GL_SPECULAR, spec);
  glMaterialfv(GL_FRONT_AND_BACK, GL_AMBIENT, amb);
  if (inverse == 0) glColor4f(r,g,b,a);
  if (inverse == 1) glColor4f(1-(g+b)*0.5,1-(b+r)*0.5,1-(g+r)*0.5,a);
}

void transform(double x, double y, double z, double *X, double *Y, double *Z);
void transform(vector v1, vector v2);

/*
void renderBitmapStringTry(double x, double y, double z, void *font, char *string) 
{  
  glDisable(GL_LIGHTING);
  glMatrixMode(GL_PROJECTION);
  glPushMatrix();
  glLoadIdentity();
  gluOrtho2D(-1.0, 1.0, -1.0, 1.0);
  glMatrixMode(GL_MODELVIEW);
  glPushMatrix();
  glLoadIdentity();
 
  glRasterPos3f(x,y,z);
  glutBitmapString(font, (unsigned char*)string);
  glPopMatrix();
  glMatrixMode(GL_PROJECTION);
  glPopMatrix();
  glEnable(GL_LIGHTING);
}
*/

void renderBitmapString(double x, double y, double z, void *font, char *string) 
{  
  glDisable(GL_LIGHTING);
  char *c;
  glMatrixMode(GL_PROJECTION);
  glPushMatrix();
  glLoadIdentity();
  gluOrtho2D(-1.0, 1.0, -1.0, 1.0);
  glMatrixMode(GL_MODELVIEW);
  glPushMatrix();
  glLoadIdentity();
//  v=rotate(v,invmodmat);
//  v=rotate(v,invprojmat);
 
  glRasterPos3f(x,y,z);
  for (c=string; *c != '\0'; c++) {
    glutBitmapCharacter(font, *c);
  }
  glPopMatrix();
  glMatrixMode(GL_PROJECTION);
  glPopMatrix();
  
  // crude fix
  glMatrixMode(GL_PROJECTION);
     glLoadIdentity();
     gluPerspective(2*atan(scale/vdist)*180/M_PI, 1.0, scale/10, scale*100);
     glMatrixMode(GL_MODELVIEW);
     glLoadIdentity();
     gluLookAt(center.x, center.y, vdist+center.z, center.x, center.y, center.z, 0.0, 1.0, 0.0);

     glRotated(phi*180/3.14159, 1, 0, 0);
     glRotated(theta*180/3.14159, 0, 1, 0);
     glRotated(psi*180/3.14159, 0, 0, 1);
     glEnable(GL_LIGHTING);
}

void renderBitmapString3(double x, double y, double z, void *font, char *string) 
{  
    char *c;
    glRasterPos3f(x, y,z);
    for (c=string; *c != '\0'; c++) {
	glutBitmapCharacter(font, *c);
    }
}

void ring(const vector cent, const vector normal, const double r1, const double r2, const int seg1, const int seg2)
{
        static GLfloat white[]={1.f, 1.f, 1.f, 1.f};
    
    float ambient[4]={(float)red*0.2f,(float)green*0.2f,(float)blue*0.2f,(float)globalgamma*0.0f};
    float diffuse[4]={(float)red*10,(float)green*10,(float)blue*10,(float)globalgamma * 5};
     glMaterialfv(GL_FRONT_AND_BACK, GL_SPECULAR,white);
    glMaterialfv(GL_FRONT_AND_BACK, GL_AMBIENT,ambient);
    glMaterialfv(GL_FRONT_AND_BACK, GL_DIFFUSE,diffuse);
    float shine=60.0;
    glMaterialfv(GL_FRONT_AND_BACK, GL_SHININESS, &shine);
//    printf("ring: seg1 = %d seg2 = %d\n",seg1,seg2);
    vector norm = normalize(normal);
    double th1, th2;
    vector v = normalize(norm^vector(0.234523, 0.435612, 0.934852));
//    printf("v = (%e, %e, %e)\n",v.x,v.y,v.z);
    vector v1s = v * r1;
    vector v2s = v * r2;


    double ts12 = M_PI*2 / (seg1 * seg2);
    double ts2 = M_PI*2 / seg2;
    double ts1 = M_PI*2 / seg1;
//    printf("angle steps: %e %e %e\n",ts12,ts2,ts1);
    glBegin(GL_TRIANGLE_STRIP);
    vector p,pold, v1, v2, forward;
    double angle1, angle2;
    for (int i=0; i<=seg1*seg2; i++)
    {
	angle1 = i * ts12;
	angle2 = i * ts2;

//	printf("angle1 = %e angle2 = %e (first)\n",angle1,angle2);
	v1 = rotate_arb(v1s, norm, angle1);
        forward = normalize(v1^norm);
	v2 = rotate_arb(v1, forward, angle2) * (r2/r1);

	p = cent + v1 + v2;
	glNormal3f(v2.x,v2.y,v2.z);
	glVertex3f(p.x,p.y,p.z);


        angle1 = (i+1) * ts12 + ts1;
	angle2 = (i+1)*ts2;

	v1 = rotate_arb(v1s, norm, angle1);
        forward = normalize(v1^norm);
	v2 = rotate_arb(v1, forward, angle2) * (r2/r1);


 
	p = cent + v1 + v2;
        
	glNormal3f(v2.x,v2.y,v2.z);
	glVertex3f(p.x,p.y,p.z);
    }
    glEnd();
}






void transform(double x, double y, double z, double *X, double *Y, double *Z)
{
    double xc,yc,zc;
    *X=x;
    *Y=y;
    *Z=z;

}

vector transform(vector v)
{
    vector v2;
    transform(v.x,v.y,v.z,&v2.x,&v2.y,&v2.z);
    return v2;
}

double orderofmagnitude(double v)
{
    if (v == 0.0) return(0.0);
    if (v >= 1.0 && v <= 2.0) return(1.0);
    if (v > 2.0 && v<=5.0) return (2.0);
    if (v > 5.0 && v<=10.0) return (5.0);
    if (v < 1.0) return (orderofmagnitude(v*10.0)*0.1);
    if (v > 10.0) return (orderofmagnitude(v*0.1)*10.0);
    return 0;
}
void lin (double x1,double y1,double x2,double y2)
{
    glVertex3f(x1,y1,0);
    glVertex3f(x2,y2,0);
}

void lin3(vector p1, vector p2)
{
    static vector t1, t2;
    t1=transform(p1);
    t2=transform(p2);
    vvert(t1);  
    vvert(t2);
}

void lin3(double x, double y, double z, double X, double Y, double Z)
{
    lin3(vector(x,y,z),vector(X,Y,Z));
}

double roundnearest(double v,double a)
{
    return(a*floor(v/a+.5));
}

double roundup(double v,double a)
{
    return(a*ceil(v/a+.5));
}
double rounddown(double v,double a)
{
    return(a*floor(v/a+.5));
}


void draw_framelines(void)
{
    glMatrixMode(GL_MODELVIEW);
    glPushMatrix();
    glLoadIdentity();
    glMatrixMode(GL_PROJECTION);
    glPushMatrix();
    glLoadIdentity();
    gluOrtho2D(-1.0, 1.0, -1.0, 1.0);

    glDisable(GL_LIGHTING);
    static char num[40];
    myColor4f(.5,.5,.5,1);
    glBegin(GL_LINES);
    lin(-.8,-.8,-.8,.8);
    lin(-.8,.8,.8,.8);
    lin(.8,.8,.8,-.8);
    lin(.8,-.8,-.8,-.8);

    glEnd(); 

    double spacing=orderofmagnitude(scale/3);
    for(double x=rounddown(center.x-scale,spacing);x<roundup(center.x+scale,spacing);x+=spacing)
    {
	if (fabs(x) < spacing*.001) x=0;
	glBegin(GL_LINES);
	snprintf(num,40,"%.6g",x);
	if ((x-center.x)/scale > -.801 && (x-center.x)/scale < .801)
	    lin((x-center.x)/scale,-.8,(x-center.x)/scale,-.75);
	glEnd();

	if ((x-center.x)/scale > -.801 && (x-center.x)/scale < .801)
	    renderBitmapString3((x-center.x)/scale,-.9,0,ANIM_FONT,num);
    }

    for(double y=rounddown(center.y-scale,spacing);y<roundup(center.y+scale,spacing);y+=spacing)
    {
	if (fabs(y) < spacing*.001) y=0;
	glBegin(GL_LINES);
	sprintf(num,"%.6g",y);
	if ((y-center.y)/scale > -.801 && (y-center.y)/scale < .801)
	    lin(-.8,(y-center.y)/scale,-.75,(y-center.y)/scale);
	glEnd();

	if ((y-center.y)/scale > -.801 && (y-center.y)/scale < .801)
	    renderBitmapString3(-.9,(y-center.y)/scale,0,ANIM_FONT,num);

    }
    glEnable(GL_LIGHTING);
    glPopMatrix();
}

vector rotx(vector v, double ang)
{
    //  ang *=180/M_PI;
    return vector (v.x, v.y*cos(ang)-v.z*sin(ang), v.z*cos(ang)+v.y*sin(ang));
}

vector roty(vector v, double ang)
{
    //  ang *=180/M_PI;
    return vector (v.x*cos(ang)+v.z*sin(ang), v.y, v.z*cos(ang)-v.x*sin(ang));
}
vector rotz(vector v, double ang)
{
    //  ang *=180/M_PI;
    return vector (v.x*cos(ang)-v.y*sin(ang), v.y*cos(ang)+v.x*sin(ang),v.z);
}


vector brot(vector v1)
{
    return rotate(rotate(v1,modmat),projmat);
}


void swap (vector &a, vector &b)
{
    vector temp=a;
    a=b;
    b=temp;
}

void setnormal(double x1, double y1, double z1, double x2, double y2, double z2, double x3, double y3, double z3)
{
    int f=-1;
    vector v1=vector (x1, y1, z1);
    vector v2=vector (x2, y2, z2);
    vector v3=vector (x3, y3, z3);
    vector nrm1 = f*normalize((v1-v2)^(v1-v3));
    if (rotate(rotate(nrm1,invmodmat),invprojmat).z > 0) nrm1=nrm1*-1;
    glNormal3d(nrm1.x, nrm1.y, nrm1.z);
}

void triangle(const vector v1, const vector v2, const vector v3, double f)
{
    static GLfloat white[]={1.f, 1.f, 1.f, 1.f};
    static vector nrm1,nrm2;
    nrm1=f*normalize((v1-v2)^(v1-v3));
    if (rotate(rotate(nrm1,invmodmat),invprojmat).z < 0) nrm1=nrm1*-1;
    if (rotate(rotate(nrm2,invmodmat),invprojmat).z < 0) nrm2=nrm2*-1;
    glNormal3d(nrm1.x, nrm1.y, nrm1.z);
    myColor4f(red/2,green/2,blue/2,1);
    float shine=50.0;
    glMaterialfv(GL_FRONT_AND_BACK, GL_SHININESS, &shine);
    glBegin(GL_TRIANGLES);
    glVertex3f(v1.x,v1.y,v1.z);
    glVertex3f(v2.x,v2.y,v2.z);
    glVertex3f(v3.x,v3.y,v3.z);
    glEnd();
}


void quad(const vector v1, const vector v2, const vector v3, const vector v4, double f)
{
    static GLfloat white[]={1.f, 1.f, 1.f, 1.f};
    static vector nrm1,nrm2;
    nrm1=f*normalize((v1-v2)^(v1-v3));
    nrm2=f*normalize((v4-v1)^(v4-v3));
    //    if (rotate(rotate(nrm1,invmodmat),invprojmat).z < 0) nrm1=nrm1*-1;
    //    if (rotate(rotate(nrm2,invmodmat),invprojmat).z < 0) nrm2=nrm2*-1;
    glNormal3d(nrm1.x, nrm1.y, nrm1.z);
    myColor4f(red/2,green/2,blue/2,1);
    float shine=50.0;
    glMaterialfv(GL_FRONT_AND_BACK, GL_SHININESS, &shine);
    glBegin(GL_TRIANGLE_STRIP);
    glVertex3f(v1.x,v1.y,v1.z);
    glVertex3f(v2.x,v2.y,v2.z);
    glVertex3f(v4.x,v4.y,v4.z);
    glVertex3f(v3.x,v3.y,v3.z);

    //    glNormal3d(nrm2.x, nrm2.y, nrm2.z);
    //    glVertex3f(v1.x,v1.y,v1.z);
    //    glVertex3f(v3.x,v3.y,v3.z);
    //    glVertex3f(v4.x,v4.y,v4.z);
    glEnd();

    myColor4f(red,green,blue,1);

    glBegin(GL_LINES);
    //    if (nrm1.z < 0) nrm1 = nrm1*-1; // point them toward sun
    //    if (nrm2.z < 0) nrm2 = nrm2*-1; // point them toward sun

    glNormal3d(nrm1.x, nrm1.y, nrm1.z);
    lin3(v1, v2);
    lin3(v2, v3);
    glNormal3d(nrm2.x, nrm2.y, nrm2.z);
    lin3(v3, v4);
    lin3(v4, v1);
    glEnd();

}

void draw_xy_framelines(void)
{
    glDisable(GL_LIGHTING);
    char num[40];
    double boxsize=lastscale*0.67;
    myColor4f(.5,.5,.5,1);
    //   glTranslatef    (fcenter.x, fcenter.y, fcenter.z);
    //    glutSolidSphere(0.4, 12, 12);
    //    glTranslatef    (-fcenter.x, -fcenter.y, -fcenter.z);
    //   printf("projection matrix follows:\n");
    //   for (int i=0;i<16;i++) {printf("%.3f ",projmat[i]); if (i%4==3) printf("\n");} printf("\n\n");
    //   printf("modelview matrix follows:\n");
    //   for (int i=0;i<16;i++) {printf("%.3f ",modmat[i]); if (i%4==3) printf("\n");} printf("\n\n");
    //    printf("!fcenter before rotation is (%.2f, %.2f, %.2f)\n",fcenter.x, fcenter.y, fcenter.z);
    fcenter=rotate(fcenter, invmodmat);
    //    printf("!fcenter after rotation is (%.2f, %.2f, %.2f)\n",fcenter.x, fcenter.y, fcenter.z);
    //    recurse_sphere (fcenter,0.5,3);
    glBegin(GL_LINES);
    vector v1(-boxsize+fcenter.x,-boxsize+fcenter.y,fcenter.z);
    vector v2(-boxsize+fcenter.x, boxsize+fcenter.y,fcenter.z);
    vector v3( boxsize+fcenter.x, boxsize+fcenter.y,fcenter.z);
    vector v4( boxsize+fcenter.x,-boxsize+fcenter.y,fcenter.z);

    //   lin3(v1,v7);
    //   lin3(v3,v5);
    //   lin3(v2,v8);
    //   lin3(v4,v6);

    lin3(v1,v2);
    lin3(v2,v3);
    lin3(v3,v4);
    lin3(v4,v1);
    glEnd(); 
    double spacing=orderofmagnitude(scale/3);
    for(double x=rounddown(fcenter.x-boxsize,spacing);x<roundup(fcenter.x+boxsize,spacing);x+=spacing)
    {
	if (fabs(x) < spacing*.001) x=0;
	snprintf(num,40,"% .6g",x);
	if (x > fcenter.x-boxsize && x < fcenter.x+boxsize)
	{
	    glBegin(GL_LINES);
	    lin3(x,boxsize+fcenter.y,fcenter.z,x,boxsize*0.96+fcenter.y,fcenter.z);
	    lin3(x,boxsize+fcenter.y,fcenter.z,x,boxsize+fcenter.y,fcenter.z);
	    lin3(x,boxsize+fcenter.y,fcenter.z,x,boxsize*0.96+fcenter.y,fcenter.z);
	    lin3(x,boxsize+fcenter.y,fcenter.z,x,boxsize+fcenter.y,fcenter.z);
	    lin3(x,-boxsize+fcenter.y,fcenter.z,x,-boxsize*0.96+fcenter.y,fcenter.z);
	    lin3(x,-boxsize+fcenter.y,fcenter.z,x,-boxsize+fcenter.y,fcenter.z);
	    lin3(x,-boxsize+fcenter.y,fcenter.z,x,-boxsize*0.96+fcenter.y,fcenter.z);
	    lin3(x,-boxsize+fcenter.y,fcenter.z,x,-boxsize+fcenter.y,fcenter.z);
	    glEnd(); 
	    renderBitmapString3(x-boxsize*(0.04*strlen(num)-0.04),-boxsize*1.12+fcenter.y,fcenter.z,ANIM_FONT,num);
	}
    }
    for(double y=rounddown(fcenter.y-boxsize,spacing);y<roundup(fcenter.y+boxsize,spacing);y+=spacing)
    {
	if (fabs(y) < spacing*.001) y=0;
	snprintf(num,40,"% .6g",y);
	if (y > fcenter.y-boxsize && y < fcenter.y+boxsize)
	{
	    glBegin(GL_LINES);
	    lin3(boxsize+fcenter.x,y,fcenter.z,boxsize*0.96+fcenter.x,y,fcenter.z);
	    lin3(boxsize+fcenter.x,y,fcenter.z,boxsize+fcenter.x,y,fcenter.z);
	    lin3(-boxsize+fcenter.x,y,fcenter.z,-boxsize*0.96+fcenter.x,y,fcenter.z);
	    lin3(-boxsize+fcenter.x,y,fcenter.z,-boxsize+fcenter.x,y,fcenter.z);
	    lin3(boxsize+fcenter.x,y,fcenter.z,boxsize*0.96+fcenter.x,y,fcenter.z);
	    lin3(boxsize+fcenter.x,y,fcenter.z,boxsize+fcenter.x,y,fcenter.z);
	    lin3(-boxsize+fcenter.x,y,fcenter.z,-boxsize*0.96+fcenter.x,y,fcenter.z);
	    lin3(-boxsize+fcenter.x,y,fcenter.z,-boxsize+fcenter.x,y,fcenter.z);
	    glEnd(); 
	    renderBitmapString3(-boxsize*1.12+fcenter.x,y-boxsize*0.03,fcenter.z,ANIM_FONT,num);
	}
    }/*
	for(double z=rounddown(fcenter.z-boxsize,spacing);z<roundup(fcenter.z+boxsize,spacing);z+=spacing)
	{
	if (fabs(z) < spacing*.001) z=0;
	snprintf(num,40,"%.6g",z);
	if (z > fcenter.z-boxsize && z < fcenter.z+boxsize)
	{
	glBegin(GL_LINES);
	lin3(boxsize+fcenter.x,boxsize+fcenter.y,z,boxsize*0.96+fcenter.x,boxsize+fcenter.y,z);
	lin3(boxsize+fcenter.x,boxsize+fcenter.y,z,boxsize+fcenter.x,boxsize*0.96+fcenter.y,z);
	lin3(boxsize+fcenter.x,-boxsize+fcenter.y,z,boxsize*0.96+fcenter.x,-boxsize+fcenter.y,z);
	lin3(boxsize+fcenter.x,-boxsize+fcenter.y,z,boxsize+fcenter.x,-boxsize*0.96+fcenter.y,z);
	lin3(-boxsize+fcenter.x,boxsize+fcenter.y,z,-boxsize*0.96+fcenter.x,boxsize+fcenter.y,z);
	lin3(-boxsize+fcenter.x,boxsize+fcenter.y,z,-boxsize+fcenter.x,boxsize*0.96+fcenter.y,z);
	lin3(-boxsize+fcenter.x,-boxsize+fcenter.y,z,-boxsize*0.96+fcenter.x,-boxsize+fcenter.y,z);
	lin3(-boxsize+fcenter.x,-boxsize+fcenter.y,z,-boxsize+fcenter.x,-boxsize*0.96+fcenter.y,z);
	glEnd(); 
	renderBitmapString3(-boxsize*1.04+fcenter.x,-boxsize*1.04+fcenter.y,z,ANIM_FONT,num);
	}
	}*/
    glEnable(GL_LIGHTING);
}

void draw_3d_framelines(void)
{
    glDisable(GL_LIGHTING);
    char num[40];
    double boxsize=lastscale*0.67;
    myColor4f(.5,.5,.5,1);
    //   glTranslatef    (fcenter.x, fcenter.y, fcenter.z);
    //    glutSolidSphere(0.4, 12, 12);
    //    glTranslatef    (-fcenter.x, -fcenter.y, -fcenter.z);
    //   printf("projection matrix follows:\n");
    //   for (int i=0;i<16;i++) {printf("%.3f ",projmat[i]); if (i%4==3) printf("\n");} printf("\n\n");
    //   printf("modelview matrix follows:\n");
    //   for (int i=0;i<16;i++) {printf("%.3f ",modmat[i]); if (i%4==3) printf("\n");} printf("\n\n");
    //    printf("!fcenter before rotation is (%.2f, %.2f, %.2f)\n",fcenter.x, fcenter.y, fcenter.z);
    fcenter=rotate(fcenter, invmodmat);
    //    printf("!fcenter after rotation is (%.2f, %.2f, %.2f)\n",fcenter.x, fcenter.y, fcenter.z);
    //    recurse_sphere (fcenter,0.5,3);
    glBegin(GL_LINES);
    vector v1(-boxsize+fcenter.x,-boxsize+fcenter.y,-boxsize+fcenter.z);
    vector v2(-boxsize+fcenter.x, boxsize+fcenter.y,-boxsize+fcenter.z);
    vector v3( boxsize+fcenter.x, boxsize+fcenter.y,-boxsize+fcenter.z);
    vector v4( boxsize+fcenter.x,-boxsize+fcenter.y,-boxsize+fcenter.z);
    vector v5(-boxsize+fcenter.x,-boxsize+fcenter.y, boxsize+fcenter.z);
    vector v6(-boxsize+fcenter.x, boxsize+fcenter.y, boxsize+fcenter.z);
    vector v7( boxsize+fcenter.x, boxsize+fcenter.y, boxsize+fcenter.z);
    vector v8( boxsize+fcenter.x,-boxsize+fcenter.y, boxsize+fcenter.z);

    //   lin3(v1,v7);
    //   lin3(v3,v5);
    //   lin3(v2,v8);
    //   lin3(v4,v6);

    lin3(v1,v2);
    lin3(v2,v3);
    lin3(v3,v4);
    lin3(v4,v1);
    lin3(v5,v6);
    lin3(v6,v7);
    lin3(v7,v8);
    lin3(v8,v5);
    lin3(v1,v5);
    lin3(v2,v6);
    lin3(v3,v7);
    lin3(v4,v8);
    glEnd(); 
    double spacing=orderofmagnitude(scale/3);
    for(double x=rounddown(fcenter.x-boxsize,spacing);x<roundup(fcenter.x+boxsize,spacing);x+=spacing)
    {
	if (fabs(x) < spacing*.001) x=0;
	snprintf(num,40,"%.6g",x);
	if (x > fcenter.x-boxsize && x < fcenter.x+boxsize)
	{
	    glBegin(GL_LINES);
	    lin3(x,boxsize+fcenter.y,-boxsize+fcenter.z,x,boxsize*0.96+fcenter.y,-boxsize+fcenter.z);
	    lin3(x,boxsize+fcenter.y,-boxsize+fcenter.z,x,boxsize+fcenter.y,-boxsize*0.96+fcenter.z);
	    lin3(x,boxsize+fcenter.y,boxsize+fcenter.z,x,boxsize*0.96+fcenter.y,boxsize+fcenter.z);
	    lin3(x,boxsize+fcenter.y,boxsize+fcenter.z,x,boxsize+fcenter.y,boxsize*0.96+fcenter.z);
	    lin3(x,-boxsize+fcenter.y,boxsize+fcenter.z,x,-boxsize*0.96+fcenter.y,boxsize+fcenter.z);
	    lin3(x,-boxsize+fcenter.y,boxsize+fcenter.z,x,-boxsize+fcenter.y,boxsize*0.96+fcenter.z);
	    lin3(x,-boxsize+fcenter.y,-boxsize+fcenter.z,x,-boxsize*0.96+fcenter.y,-boxsize+fcenter.z);
	    lin3(x,-boxsize+fcenter.y,-boxsize+fcenter.z,x,-boxsize+fcenter.y,-boxsize*0.96+fcenter.z);
	    glEnd(); 
	    renderBitmapString3(x,-boxsize*1.04+fcenter.y,-boxsize*1.04+fcenter.z,ANIM_FONT,num);
	}
    }
    for(double y=rounddown(fcenter.y-boxsize,spacing);y<roundup(fcenter.y+boxsize,spacing);y+=spacing)
    {
	if (fabs(y) < spacing*.001) y=0;
	snprintf(num,40,"%.6g",y);
	if (y > fcenter.y-boxsize && y < fcenter.y+boxsize)
	{
	    glBegin(GL_LINES);
	    lin3(boxsize+fcenter.x,y,boxsize+fcenter.z,boxsize*0.96+fcenter.x,y,boxsize+fcenter.z);
	    lin3(boxsize+fcenter.x,y,boxsize+fcenter.z,boxsize+fcenter.x,y,boxsize*0.96+fcenter.z);
	    lin3(-boxsize+fcenter.x,y,boxsize+fcenter.z,-boxsize*0.96+fcenter.x,y,boxsize+fcenter.z);
	    lin3(-boxsize+fcenter.x,y,boxsize+fcenter.z,-boxsize+fcenter.x,y,boxsize*0.96+fcenter.z);
	    lin3(boxsize+fcenter.x,y,-boxsize+fcenter.z,boxsize*0.96+fcenter.x,y,-boxsize+fcenter.z);
	    lin3(boxsize+fcenter.x,y,-boxsize+fcenter.z,boxsize+fcenter.x,y,-boxsize*0.96+fcenter.z);
	    lin3(-boxsize+fcenter.x,y,-boxsize+fcenter.z,-boxsize*0.96+fcenter.x,y,-boxsize+fcenter.z);
	    lin3(-boxsize+fcenter.x,y,-boxsize+fcenter.z,-boxsize+fcenter.x,y,-boxsize*0.96+fcenter.z);
	    glEnd(); 
	    renderBitmapString3(-boxsize*1.04+fcenter.x,y,-boxsize*1.04+fcenter.z,ANIM_FONT,num);
	}
    }
    for(double z=rounddown(fcenter.z-boxsize,spacing);z<roundup(fcenter.z+boxsize,spacing);z+=spacing)
    {
	if (fabs(z) < spacing*.001) z=0;
	snprintf(num,40,"%.6g",z);
	if (z > fcenter.z-boxsize && z < fcenter.z+boxsize)
	{
	    glBegin(GL_LINES);
	    lin3(boxsize+fcenter.x,boxsize+fcenter.y,z,boxsize*0.96+fcenter.x,boxsize+fcenter.y,z);
	    lin3(boxsize+fcenter.x,boxsize+fcenter.y,z,boxsize+fcenter.x,boxsize*0.96+fcenter.y,z);
	    lin3(boxsize+fcenter.x,-boxsize+fcenter.y,z,boxsize*0.96+fcenter.x,-boxsize+fcenter.y,z);
	    lin3(boxsize+fcenter.x,-boxsize+fcenter.y,z,boxsize+fcenter.x,-boxsize*0.96+fcenter.y,z);
	    lin3(-boxsize+fcenter.x,boxsize+fcenter.y,z,-boxsize*0.96+fcenter.x,boxsize+fcenter.y,z);
	    lin3(-boxsize+fcenter.x,boxsize+fcenter.y,z,-boxsize+fcenter.x,boxsize*0.96+fcenter.y,z);
	    lin3(-boxsize+fcenter.x,-boxsize+fcenter.y,z,-boxsize*0.96+fcenter.x,-boxsize+fcenter.y,z);
	    lin3(-boxsize+fcenter.x,-boxsize+fcenter.y,z,-boxsize+fcenter.x,-boxsize*0.96+fcenter.y,z);
	    glEnd(); 
	    renderBitmapString3(-boxsize*1.04+fcenter.x,-boxsize*1.04+fcenter.y,z,ANIM_FONT,num);
	}
    }
    glEnable(GL_LIGHTING);
}

void mouse_track(void)
{
    static double mx, my, mz;
    static double x,y,z,gtx,gty,gtz,sep,sep2;
    mx=((double)lmx/window_size_x-0.5)*2;
    my=-((double)lmy/window_size_y-0.5)*2;
    mz=0;
    while (need_guesses == 1)
    {
	transform(gx,gy,gz,&x,&y,&z);
	sep=(x-mx)*(x-mx) + (y-my)*(y-my) + (z-mz)*(z-mz);

	gtx=gx+(drand48()-0.5)*scale*0.01;
	gty=gy+(drand48()-0.5)*scale*0.01;
	gtz=gz+(drand48()-0.5)*scale*0.01;
	transform(gtx,gty,gtz,&x,&y,&z);
	sep2=(x-mx)*(x-mx) + (y-my)*(y-my) + (z-mz)*(z-mz);
	if (sep2<sep) {gx=gtx; gy=gty; gz=gtz;}  
	if (sep < 1.0/window_size) need_guesses=0;
	update=1;
    }

    if (track == 1)
	while (1)
	{
	    transform(tx,ty,tz,&x,&y,&z);
	    sep=(x-mx)*(x-mx) + (y-my)*(y-my) + (z-mz)*(z-mz);
	    gtx=(drand48()-0.5)*scale*0.01;
	    gty=(drand48()-0.5)*scale*0.01;
	    gtz=(drand48()-0.5)*scale*0.01;
	    fcenter.x+=gtx;
	    fcenter.y+=gty;
	    fcenter.z+=gtz;
	    transform(tx,ty,tz,&x,&y,&z);
	    sep2=(x-mx)*(x-mx) + (y-my)*(y-my) + (z-mz)*(z-mz);
	    //    printf("tracking: mouse coords % g, % g, % g; guess coords % g, % g, % g\n",mx,my,mz,x,y,z);
	    //    printf("tracking: old separation %f, new one %f\n",sep2, sep);
	    if (sep2 > sep)
	    {
		fcenter.x-=gtx;
		fcenter.y-=gty;
		fcenter.z-=gtz;
	    }
	    if (sep < 1.0/window_size) break;
	}
} 

void disp(void)
{
}

void sphere(vector cent, float r)
{
    static GLfloat white[]={0.4f, 0.4f, 0.4f, 0.4f};
    spherecounter++;
    float curcolor[4]={(float)red,(float)green,(float)blue,(float)globalgamma};
    glMaterialfv(GL_FRONT_AND_BACK, GL_SPECULAR,white);
    glMaterialfv(GL_FRONT_AND_BACK, GL_DIFFUSE,curcolor);
    float shine=30.0;
    glMaterialfv(GL_FRONT_AND_BACK, GL_SHININESS, &shine);
    glMatrixMode(GL_MODELVIEW);
    glTranslatef    (cent.x, cent.y, cent.z);
    glutSolidSphere(r, circfaces, circfaces); 
    glTranslatef    (-cent.x, -cent.y, -cent.z);
}

void draw_trail(int b)
{
    glNormal3f(0,0,1);
    glBegin(GL_LINE_STRIP);
    for (int i=0; i<rbocc[b]; i++)
    {
	if (i > 2*traillen[b]) break;
	double bright=exp(-(float)i/traillen[b]);
	myColor4f(red,green,blue,bright);
	int j=(rbl[b]-i+BL)%BL;
	vvert(trail[j][b]);
    }
    glEnd();
    rbl[b]=(rbl[b]+1)%BL;

}

void idle(void)
{
    //  printf(" -- START OF IDLE t=%d--\n",glutGet(GLUT_ELAPSED_TIME));
    static int n,i, num_lines=9;
    static int warmup=1;
    static int decimals;
    static double angle;
    static double r;
    static double zavg;
    static int nframes=0;
    static int totaltime=0;
    //  static double xc,yc,zc,x,y,z,xc1,xc2,yc1,yc2,zc1,zc2;
    static double x,y,z;
    static double mx,my,mz,gtx,gty,gtz;
    static double waittime=10;
    static double spacing;
    static double x1,y1,x2,y2;
    //  printf("Allocated %d buffers of length %d\n",NB,BL);
    static char c;
    static char num[200];
    static char line2[300];
    static char gifname[300]="anim.gif";
    static int frameskip=1;
    static char* line;
    static int lastframe=0;
    static int frametime;
    static double framerate;
    static double sep,sep2;
    static double boxsize;
    static double ang;
    static short int dummy;
    static int gifframe=0;
    static vector v1, v2, v1t, v2t, v3, v4, v3t, v4t;

    if (warmup) // flush one frame at start; this could be done better...
    {
	warmup--;
	line=(char *)malloc(sizeof(char)*301);
	line[0]='F';
    }
    else 
    {
	if (fgets(line,299,stdin) == NULL) {} // to make the compiler happy; we don't really care
	if (feof(stdin)) {usleep(10000);return;}
    }
    if (line[0] == '!') { // bypass
	printf("%s",&line[1]);
	return;
    }

    if (!strncmp(line,"c3 ",3)) { // 3d circle
	td=1;
	vector cent;	
	sscanf(&line[3],"%lf %lf %lf %lf",&cent.x,&cent.y,&cent.z,&r);
	sphere(cent,r);
    }
    else if (!strncmp(line,"ulc3 ",5)) { // 3d circle
	td=1;
	vector cent;	
	sscanf(&line[5],"%lf %lf %lf %lf",&cent.x,&cent.y,&cent.z,&r);
	glDisable(GL_LIGHTING);
	sphere(cent,r);
	glEnable(GL_LIGHTING);
    }
    else if (!strncmp(line,"C ",2)) { //just set color
	sscanf(&line[2],"%lf %lf %lf",&red,&green,&blue);
	myColor4f(red,green,blue,1);
    }    
    else if (!strncmp(line,"C4 ",3)) { //just set color with alpha
	float alpha;
	sscanf(&line[3],"%lf %lf %lf %f",&red,&green,&blue,&alpha);
	myColor4f(red,green,blue,alpha);
    }
    else if (!strncmp(line,"fc3 ",3)) { // 3d circle, done by hand with recursion
	td=1;
	//    myColor4f(red,green,blue,1);
	static GLfloat white[]={1.f, 1.f, 1.f, 1.f};

	vector cent;	
	sscanf(&line[3],"%lf %lf %lf %lf",&cent.x,&cent.y,&cent.z,&r);
	float curcolor[4]={(float)red,(float)green,(float)blue,1};
	glMaterialfv(GL_FRONT_AND_BACK, GL_SPECULAR,white);
	glMaterialfv(GL_FRONT_AND_BACK, GL_DIFFUSE,curcolor);
	float shine=30.0;
	glMaterialfv(GL_FRONT_AND_BACK, GL_SHININESS, &shine);
	recurse_sphere(cent,r,1);
	rotate(cent,invmodmat); 
    }

    else if (!strncmp(line,"center3",7))
    {
	sscanf(&line[8],"%lf %lf %lf",&center.x,&center.y,&center.z);
	//    fprintf (stderr,"Center set to %e, %e, %e\n",center.x,center.y,center.z);
	center2=center;
    }
    else if (!strncmp(line,"l ",2)) { // line, no color specified
	sscanf(&line[2],"%lf %lf %lf %lf",&v1.x,&v1.y,&v2.x,&v2.y);
	glBegin(GL_LINES);
	lin(v1.x,v1.y,v2.x,v2.y);
	glEnd();
    }

    else if (!strncmp(line,"erase ",6))
    {
	int b;
	sscanf(&line[7],"%d",&b);
	rbocc[b]=0;
	rbl[b]=0; 
    }
    else if (!strncmp(line,"force2dframe",12))
    {
	force_2d_frame=1;
	printf("Forcing 2D framelines\n");
    }
    else if (!strncmp(line,"lightfrom ",10))
    {
	int b;
	sscanf(&line[10],"%lf %lf %lf",&sunvec.x,&sunvec.y,&sunvec.z);
    }


    else if (!strncmp(line,"ct3 ",4))
    {
	spherecounter++;
	td=1;

	int b;
	sscanf(&line[4],"%d %lf %lf %lf %lf",&b,&v1.x,&v1.y,&v1.z,&r);
	if (b < NB) 
	{
	    trail[rbl[b]][b] = v1;
	    if (rbocc[b]<BL) rbocc[b]++;
	    draw_trail(b);
	}
	sphere(v1,r);
    }

    else if (!strncmp(line,"cleartrail ",11))
    {
	int b;
	sscanf(&line[11],"%d",&b);
	rbocc[b]=rbl[b]=0;
    }

    else if (!strncmp(line,"ct ",3))
    {
	spherecounter++;

	int b;
	sscanf(&line[3],"%d %lf %lf %lf",&b,&v1.x,&v1.y,&r);
	v1.z = 0;
	if (b < NB) 
	{
	    trail[rbl[b]][b] = v1;
	    if (rbocc[b]<BL) rbocc[b]++;
	    draw_trail(b);
	}
	sphere(v1,r);
    }
    else if (line[0] == 'l' && line[1] == '3' && line[2] == ' ') 
    { // 3d line
	td=1;
	sscanf(&line[3],"%lf %lf %lf %lf %lf %lf",&v1.x,&v1.y,&v1.z,&v2.x,&v2.y,&v2.z);
	if (!sunlight) glNormal3f(0,0,1);
	else glNormal3f(sunvec.x-v1.x, sunvec.y-v1.y, sunvec.z-v1.z);
	glBegin(GL_LINES);
	vvert(v1);
	vvert(v2);
	glEnd();
    }
    else if (!strncmp(line, "q3 ",3)) {
	td=1;
	// we need four vectors here
	sscanf(&line[3],"%lf %lf %lf %lf %lf %lf %lf %lf %lf %lf %lf %lf",&v1.x,&v1.y,&v1.z,&v2.x,&v2.y,&v2.z

		,&v3.x,&v3.y,&v3.z,&v4.x,&v4.y,&v4.z);
	quad(v1,v2,v3,v4,1);
    }

    else if (!strncmp(line,"trl ",4))
    {
	int b,l;
	sscanf(&line[4],"%d %d",&b,&l);
	traillen[b]=l;
    }

    else if (!strncmp(line,"T ",2)) // text, not 3d, fixed in viewport
    {
	sscanf(&line[1],"%lf %lf",&x,&y);
	if (fgets(line2,300,stdin) == NULL) {}
	//    myColor4f(red,green,blue,1);
	glDisable(GL_LIGHTING);
	renderBitmapString(x,y,0,ANIM_FONT,line2);
	glEnable(GL_LIGHTING);
    }
    else if (line[0] == 't' && line[1] == '3')
    {
	vector v,vt;
	td=1;
	sscanf(&line[2],"%lf %lf %lf",&v.x,&v.y,&v.z);
	vt=transform(v);
	if (ctog)      myColor4f(red,green,blue,1);
	if (fgets(line2,300,stdin) == NULL) {}

//	glColor3f(1.,1.,1.);
	glDisable(GL_LIGHTING);
	//  renderBitmapString3(v.x,v.y,v.z,GLUT_BITMAP_TIMES_ROMAN_24,line2);
	renderBitmapString3(v.x,v.y,v.z,ANIM_FONT,line2);
	glEnable(GL_LIGHTING);
    }

    else if (line[0] == 't' && line[1] == ' ') // text, not 3d, scales with viewport
    {
	sscanf(&line[1],"%lf %lf",&x,&y);
	x -= center.x; y -= center.y;
	if (fgets(line2,300,stdin) == NULL) {}
	glDisable(GL_LIGHTING);
	renderBitmapString(x/scale,y/scale,0,ANIM_FONT,line2);
	glEnable(GL_LIGHTING);
	//    renderBitmapString(x/scale,y/scale,0,GLUT_BITMAP_TIMES_ROMAN_24,line2);
    }

    else if (line[0] == 'A') { // toggle gridlines
	sscanf(&line[1],"%d",&axes);
    }

    else if (!strncmp(line, "S ",2)) {
	double desired_scale;
	sscanf(&line[1],"%lf", &desired_scale); 
	vdist2 *= desired_scale/scale2;
	scale2=desired_scale; 
    }
    else if (!strncmp(line, "VD ",3)) {
	sscanf(&line[2],"%lf", &vdist2); 
    }

    else if (!strncmp(line, "grid ",5)) {
	// Parameters: <x1> <y1> <z1> <x2> <y2> <z2> <Nx> <Ny>
	// followed by Nx*Ny floats in binary form (not doubles!) that are RGB values for grid points
	double x1, y1, z1, x2, y2, z2;
	int Nx, Ny;
	sscanf(&line[5],"%lf %lf %lf %lf %lf %lf %d %d",&x1, &y1, &z1, &x2, &y2, &z2, &Nx, &Ny);
	if (Nx*Ny*3 > f_bufsize)
	{
	    f_bufsize = Nx*Ny*3;
	    f_buffer = (float *)realloc(f_buffer, f_bufsize*sizeof(float));
	}
	fread(f_buffer, Nx*Ny*3, sizeof(float), stdin);
	double xstep = (x2-x1)/Nx;
	double ystep = (y2-y1)/Ny;
	for (int i=0; i<Nx; i++)
	    for (int j=0; j<Ny; j++)
	    {
		double x=x1+xstep*i;
		double y=y1+ystep*j;
		vector v1(x,y,z1),
		       v2(x+xstep,y,z1),
		       v3(x+xstep,y+ystep,z1),
		       v4(x,y+ystep,z2);
		red   = f_buffer[(i*Nx+j)*3];
		green = f_buffer[(i*Nx+j)*3+1];
		blue  = f_buffer[(i*Nx+j)*3+2];
		quad(v1, v2, v3, v4, 1);
	    }
    }
    else if (!strncmp(line, "ring ",5)) {
	vector cent, normal;
	double rad, thick;
	int n1, n2;

	sscanf(&line[5],"%lf %lf %lf %lf %lf %lf %lf %lf %d %d",&cent.x,&cent.y,&cent.z,&normal.x,&normal.y,&normal.z,&rad, &thick, &n1, &n2);
	ring(cent,normal,rad,thick, n1, n2);
    }

    else if (!strncmp(line, "manylines ",10)) {
	// Parameters: <N>
	// followed by 6N doubles in binary form that are endpoints for lines
	int N;
	sscanf(&line[10],"%d",&N);
	if (N*6 > d_bufsize)
	{
	    d_bufsize = N*6;
	    d_buffer = (double *)realloc(d_buffer, d_bufsize*sizeof(double));
	}
	fread(d_buffer, N*6, sizeof(double), stdin);

	if (!sunlight) glNormal3f(0,0,1);
	else glNormal3f(sunvec.x-v1.x, sunvec.y-v1.y, sunvec.z-v1.z);

	glColor4f(red,green,blue,1);
	glBegin(GL_LINES);

	for (int i=0; i<N; i++)
	{
	    glVertex3f(d_buffer[i*6], d_buffer[i*6+1], d_buffer[i*6+2]);
	    glVertex3f(d_buffer[i*6+3], d_buffer[i*6+4], d_buffer[i*6+5]);
	}
	glEnd();
    }

    else if (!strncmp(line, "manycoloredtriangles ",21)) {
	// Parameters: <N> <gamma>
	// followed by 27N doubles in binary form that are vertices of triangles, the normals at those vertices, and the colors at those vertices
	int N;
	double gamma;
	sscanf(&line[21],"%d %lf",&N,&gamma);
	if (N*27 > d_bufsize)
	{
	    d_bufsize = N*27;
	    d_buffer = (double *)realloc(d_buffer, d_bufsize*sizeof(double));
	}
	fread(d_buffer, N*27, sizeof(double), stdin);
	float shine=20.0;
	glMaterialfv(GL_FRONT_AND_BACK, GL_SHININESS, &shine);

	glBegin(GL_TRIANGLES);

	for (int i=0; i<N; i++)
	{
	    //setnormal(d_buffer[i*21], d_buffer[i*21+1], d_buffer[i*21+2],d_buffer[i*21+3], d_buffer[i*21+4], d_buffer[i*21+5],d_buffer[i*21+6], d_buffer[i*21+7], d_buffer[i*21+8]);
	    for (int j=0; j<3; j++)
	    {
		myColor4f (d_buffer[i*27 + j*9 + 6]*2, d_buffer[i*27 + j*9 + 7]*2, d_buffer[i*27 + j*9 + 8]*2, gamma);
		vector v = vector(d_buffer[i*27 + j*9 + 3], d_buffer[i*27 + j*9 + 4], d_buffer[i*27 + j*9 + 5]);
		if (rotate(rotate(v,invmodmat),invprojmat).z < 0) v=v*-1;
		glNormal3d(v.x,v.y,v.z);
		glVertex3d(d_buffer[i*27 + j*9 + 0], d_buffer[i*27 + j*9 + 1], d_buffer[i*27 + j*9 + 2]);
	    }
	}
	glEnd();
    }
    else if (!strncmp(line, "manycoloredlines ",17)) {
	// Parameters: <N> <gamma>
	// followed by 9N doubles in binary form that are endpoints for colored lines
	int N;
	double gamma;
	sscanf(&line[17],"%d %lf",&N,&gamma);
//	printf("anim is reading %d lines with gamma %lf\n",N,gamma);
	if (N*9 > d_bufsize)
	{
	    d_bufsize = N*9;
	    d_buffer = (double *)realloc(d_buffer, d_bufsize*sizeof(double));
	}
	fread(d_buffer, N*9, sizeof(double), stdin);

	if (!sunlight) glNormal3f(0,0,1);
	else glNormal3f(sunvec.x-v1.x, sunvec.y-v1.y, sunvec.z-v1.z);
	//     glColor4f(0.0,1.0,0.0,1.0);
	glBegin(GL_LINES);

	for (int i=0; i<N; i++)
	{
//	    	      printf("color: %e %e %e\n",d_buffer[i*9+6], d_buffer[i*9+7], d_buffer[i*9+8]);
	    myColor4f(d_buffer[i*9+6], d_buffer[i*9+7], d_buffer[i*9+8],gamma);
//	    printf("coords: %e %e %e - %e %e %e\n",d_buffer[i*9], d_buffer[i*9+1], d_buffer[i*9+2],d_buffer[i*9+3], d_buffer[i*9+4], d_buffer[i*9+5]);
	    glVertex3f(d_buffer[i*9], d_buffer[i*9+1], d_buffer[i*9+2]);
	    glVertex3f(d_buffer[i*9+3], d_buffer[i*9+4], d_buffer[i*9+5]);
	}
	glEnd();
    }
    else if (!strncmp(line, "edtvisualize ",13)) {
	// Parameters: <N> <gamma>
	// followed by 21N doubles in binary form:
	// central point xyz
	// five neighbors xyz
	// color rgb
	int N;
	double gamma;
	sscanf(&line[13],"%d %lf",&N,&gamma);
	if (N*21 > d_bufsize)
	{
	    d_bufsize = N*21;
	    d_buffer = (double *)realloc(d_buffer, d_bufsize*sizeof(double));
	}
	fread(d_buffer, N*21, sizeof(double), stdin);

	//     if (!sunlight) glNormal3f(0,0,1);
	//     else glNormal3f(sunvec.x-v1.x, sunvec.y-v1.y, sunvec.z-v1.z);
	//     glColor4f(0.0,1.0,0.0,1.0);

	float shine=40.0;
	glMaterialfv(GL_FRONT_AND_BACK, GL_SHININESS, &shine);

	for (int i=0; i<N; i++)
	{
	    myColor4f(d_buffer[i*21+18], d_buffer[i*21+19], d_buffer[i*21+20],gamma);
	    glBegin(GL_TRIANGLE_FAN);
	    glVertex3f(d_buffer[i*21], d_buffer[i*21+1], d_buffer[i*21+2]);
	    glVertex3f(d_buffer[i*21+3], d_buffer[i*21+4], d_buffer[i*21+5]);
	    setnormal(d_buffer[i*21], d_buffer[i*21+1], d_buffer[i*21+2],d_buffer[i*21+3], d_buffer[i*21+4], d_buffer[i*21+5],d_buffer[i*21+6], d_buffer[i*21+7], d_buffer[i*21+8]);
	    glVertex3f(d_buffer[i*21+6], d_buffer[i*21+7], d_buffer[i*21+8]);
	    setnormal(d_buffer[i*21], d_buffer[i*21+1], d_buffer[i*21+2],d_buffer[i*21+9], d_buffer[i*21+10], d_buffer[i*21+11],d_buffer[i*21+6], d_buffer[i*21+7], d_buffer[i*21+8]);

	    glVertex3f(d_buffer[i*21+9], d_buffer[i*21+10], d_buffer[i*21+11]);
	    setnormal(d_buffer[i*21], d_buffer[i*21+1], d_buffer[i*21+2],d_buffer[i*21+9], d_buffer[i*21+10], d_buffer[i*21+11],d_buffer[i*21+12], d_buffer[i*21+13], d_buffer[i*21+14]);
	    glVertex3f(d_buffer[i*21+12], d_buffer[i*21+13], d_buffer[i*21+14]);
	    setnormal(d_buffer[i*21], d_buffer[i*21+1], d_buffer[i*21+2],d_buffer[i*21+15], d_buffer[i*21+16], d_buffer[i*21+17],d_buffer[i*21+12], d_buffer[i*21+13], d_buffer[i*21+14]);
	    glVertex3f(d_buffer[i*21+15], d_buffer[i*21+16], d_buffer[i*21+17]);
	    setnormal(d_buffer[i*21], d_buffer[i*21+1], d_buffer[i*21+2],d_buffer[i*21+15], d_buffer[i*21+16], d_buffer[i*21+17],d_buffer[i*21+3], d_buffer[i*21+4], d_buffer[i*21+5]);
	    glVertex3f(d_buffer[i*21+3], d_buffer[i*21+4], d_buffer[i*21+5]);
	    glEnd();
	}
    }


    else if (!strncmp(line, "manyballs ",10)) {
	// Parameters: <N>
	// followed by 4N doubles in binary form that are positions and radii for spheres
	int N;
	td=1;
	sscanf(&line[10],"%d",&N);
	if (N*4 > d_bufsize)
	{
	    d_bufsize = N*4;
	    d_buffer = (double *)realloc(d_buffer, d_bufsize*sizeof(double));
	}
	fread(d_buffer, N*4, sizeof(double), stdin);

	if (!sunlight) glNormal3f(0,0,1);
	else glNormal3f(sunvec.x-v1.x, sunvec.y-v1.y, sunvec.z-v1.z);

	glColor4f(red,green,blue,1);

	for (int i=0; i<N; i++)
	{
	    sphere(vector(d_buffer[i*4], d_buffer[i*4+1], d_buffer[i*4+2]),d_buffer[i*4+3]);
	}

    }
    else if (!strncmp(line, "manycoloredballs ",17)) {
	// Parameters: <N>
	// followed by 7N doubles in binary form that are position, radius, RGB for spheres
	int N;
	td=1;
	sscanf(&line[17],"%d %lf",&N,&globalgamma);
	if (N*7 > d_bufsize)
	{
	    d_bufsize = N*7;
	    d_buffer = (double *)realloc(d_buffer, d_bufsize*sizeof(double));
	}
	fread(d_buffer, N*7, sizeof(double), stdin);

	if (!sunlight) glNormal3f(0,0,1);
	else glNormal3f(sunvec.x-v1.x, sunvec.y-v1.y, sunvec.z-v1.z);


	for (int i=0; i<N; i++)
	{
	    red=d_buffer[i*7+4]; green=d_buffer[i*7+5]; blue=d_buffer[i*7+6]; 
	    sphere(vector(d_buffer[i*7], d_buffer[i*7+1], d_buffer[i*7+2]),d_buffer[i*7+3]);
	}

    }







    else if (!strncmp(line, "tr ",3)) { // triangle
	td=1;
	sscanf(&line[3],"%lf %lf %lf %lf %lf %lf %lf %lf %lf",&v1.x,&v1.y,&v1.z,&v2.x,&v2.y,&v2.z

		,&v3.x,&v3.y,&v3.z);
	triangle(v1,v2,v3,1);
    }
    else if (!strncmp(line,"rotatepsi ",10))
    {
	sscanf(&line[9],"%lf",&ang);
	psi2+=ang; update=1;
    }  
    else if (!strncmp(line,"rotatephi ",10))
    {
	sscanf(&line[9],"%lf",&ang);
	phi2+=ang; update=1;
    }  
    else if (!strncmp(line,"rotatetheta ",12))
    {
	sscanf(&line[11],"%lf",&ang);
	theta2+=ang; update=1;
    }
    else if (!strncmp(line,"c ",2)) { // circle
	sscanf(line,"%c %lf %lf %lf",&c,&x1,&y1,&r);
	if (1)
	{
	    num_lines=sqrt(window_size*r/scale)*2+4;
	    glBegin(GL_LINES);
	    glVertex3f((x1+r), (y1),0);
	    for (i=0;i<num_lines;i++)
	    {
		angle = i*2*M_PI/num_lines;
		glVertex3f((x1+cos(angle)*r), (y1+sin(angle)*r),0);
		glVertex3f((x1+cos(angle)*r), (y1+sin(angle)*r),0);
	    }
	    glVertex3f((x1+r), (y1),0);
	    glEnd();
	}
    }
    else if (!strncmp(line,"c3 ",3))
    {

	int b;
	sscanf(&line[4],"%d %lf %lf %lf",&b,&v1.x,&v1.y,&r);
         num_lines=sqrt(window_size*r/scale)*2+4;
            glBegin(GL_LINES);
            glVertex3f((x1+r), (y1),0);
            for (i=0;i<num_lines;i++)
            {
                angle = i*2*M_PI/num_lines;
                glVertex3f((x1+cos(angle)*r), (y1+sin(angle)*r),0);
                glVertex3f((x1+cos(angle)*r), (y1+sin(angle)*r),0);
            }   
            glVertex3f((x1+r), (y1),0);
            glEnd();

	
		if (b < NB) 
	{
	    trail[rbl[b]][b] = v1;
	    if (rbocc[b]<BL) rbocc[b]++;
	    draw_trail(b);
	}
    }


    else if (!strncmp(line,"font small",10))
    {
	ANIM_FONT = GLUT_BITMAP_HELVETICA_10;
    }

    else if (!strncmp(line,"font medium",11))
    {
	ANIM_FONT = GLUT_BITMAP_HELVETICA_12;
    }

    else if (!strncmp(line,"font large",10))
    {
	ANIM_FONT = GLUT_BITMAP_HELVETICA_18;
    }




    else if (!strncmp(line,"endgif",6))
    {
	if (line[7] != 32 && line[9] != 13 && line[7] != 0)
	{
	    // there's a filename; see if it ends in .gif or not 
	    if (!strncmp(line+strlen(line)-5, ".gif",4))
	    {
		line[strlen(line)-1]='\0';
		snprintf(gifname,200,"%s",line+7);
	    }
	    else
	    {
		line[strlen(line)-1]='\0';
		snprintf(gifname,200,"%s.gif",line+7);
	    }
	}
	else
	{
	    snprintf(gifname,200,"animout.gif");
	}
	printf("Making animated gif with name %s\n",gifname);

	char command[256];
	snprintf(command,255,"convert gifframe*.png %s",gifname);
	fprintf(stderr,"Running command %s to create gif -- please be patient...\n",command);
	int errcode=system(command);
	if (errcode == 0) fprintf(stderr,"Done making animated gif\n");
	else fprintf(stderr,"Error making animated gif -- do you have imagemagick installed?\n");
	errcode=system("rm gifframe*.png");
	fprintf(stderr,"Trying to optimize image...\n");
	snprintf(command,255,"gifsicle -i %s --colors 64 --dither --optimize=3 -o tempnameanim.gif",gifname);
	errcode=system(command);
	if (errcode == 0) 
	{
	    //      snprintf(command,255,"mv tempnameanim.gif %s",gifname);
	    //      errcode=system(command);
	    fprintf(stderr,"... image optimized\n");
	}
	else 
	    fprintf(stderr,"Error optimizing animated gif -- do you have gifsicle installed?\n");
	gifframe=0;
    }
    else if (line[0] == 'Q') {
	fflush(stdout); exit(0);
    }
    else if (line[0] == 'F') {
	if (line[1] == 'G') // we should add this frame to the animated gif we're going to make
	{
	    char framename[50];
	    snprintf(framename, 49, "gifframe%06d.png",gifframe);
	    gifframe++;
	}

	spherecounter++;
	//  circfaces = 10 * pow(2,log10(10000.0/spherecounter));
	if (circfaces < 4) circfaces = 4;
	if (circfaces > 24) circfaces = 24;
	//  spherecounter=0;   
	if (((axes || adef) && td == 0)) 
	{
	    draw_framelines();
	}
	else if (force_2d_frame)
	{
	    draw_xy_framelines();
	}
	// draw frame, 3D
	else if (axes && td) 
	{
	    draw_3d_framelines();
	}
	vdist=vdist2;
	scale=scale2;
	center=center2;
	theta=(theta*0.9+theta2*0.1);
	phi=(phi*0.9+phi2*0.1);
	psi=(psi*0.9+psi2*0.1);
	myColor4f(red,green,blue,1);     
	glutSwapBuffers(); 
	glClear(GL_COLOR_BUFFER_BIT);
	glClear(GL_DEPTH_BUFFER_BIT);
	framerate = 1000/(glutGet(GLUT_ELAPSED_TIME)-lastdraw);
	lastdraw=glutGet(GLUT_ELAPSED_TIME);
	if (update) save_config();
	// set up matrix

	if (td)
	{ 
	    glMatrixMode(GL_PROJECTION); 
	    glLoadIdentity(); 
	    gluPerspective(2*atan(scale/vdist)*180/M_PI, 1.0, scale/10, scale*100); 
	    glMatrixMode(GL_MODELVIEW);
	    glLoadIdentity(); 

	    //     printf("Looking from %e %e %e to %e %e %e\n",center.x,center.y,center.z+vdist,center.x,center.y,center.z);
	    gluLookAt(center.x, center.y, vdist+center.z, center.x, center.y, center.z, 0.0, 1.0, 0.0);

	    glRotated(phi*180/3.14159, 1, 0, 0);
	    glRotated(theta*180/3.14159, 0, 1, 0);
	    glRotated(psi*180/3.14159, 0, 0, 1);

	    glGetFloatv(GL_PROJECTION_MATRIX, projmat);
	    glGetFloatv(GL_MODELVIEW_MATRIX, modmat);
	    gluInvertMatrix(modmat, invmodmat); 
	    gluInvertMatrix(projmat, invprojmat); 



	    float lightpos0[] = {0., 1, 1, 0.}; 
	    float lightcoldiffuse0[] = {0.8, 0.8, 0.8, 1.};
	    float lightcolspecular0[] = {0.5, 0.6, 0.7, 1.};
	    float lightcolambient0[] = {0.0, 0.0, 0.0, 1};
	    float lightpos1[] = {0., 0.3, 1, 0.}; 
	    float lightcolambient1[] = {0.0, 0.0, 0.0, 1};
	    float lightcoldiffuse1[] = {0.5, 0.4, 0.3, 1.}; 
	    float lightcolspecular1[] = {0., 0., 0., 0.0}; 

	    if (sunlight)
	    {
		lightpos0[0] = lightpos1[0] = sunvec.x;
		lightpos0[1] = lightpos1[1] = sunvec.y;
		lightpos0[2] = lightpos1[2] = sunvec.z;
		lightpos0[3] = lightpos1[3] = 1.;
		lightcolspecular0[0] = 0.5;
		lightcolspecular0[1] = 0.5;
		lightcolspecular0[2] = 0.5;
		lightcolspecular0[3] = 1;
		lightcoldiffuse0[0] = 1;
		lightcoldiffuse0[1] = 0.9;
		lightcoldiffuse0[2] = 0.8;
		lightcoldiffuse0[3] = 1;
		lightcoldiffuse1[0] = 0; 
		lightcoldiffuse1[1] = 0; 
		lightcoldiffuse1[2] = 0; 
		lightcoldiffuse1[3] = 0; 
		lightcolambient1[0] = -0.15; 
		lightcolambient1[1] = -0.15; 
		lightcolambient1[2] = -0.15; 
		lightcolambient1[3] = -0.15; 

	    }

	    glLightfv(GL_LIGHT0, GL_POSITION, lightpos0);
	    glLightfv(GL_LIGHT0, GL_SPECULAR, lightcolspecular0);
	    glLightfv(GL_LIGHT0, GL_DIFFUSE, lightcoldiffuse0);
	    glLightfv(GL_LIGHT0, GL_AMBIENT, lightcolambient0);

	    rotate(lightpos1,invmodmat);
	    glLightfv(GL_LIGHT1, GL_POSITION, lightpos1);
	    glLightfv(GL_LIGHT1, GL_SPECULAR, lightcolspecular1);
	    glLightfv(GL_LIGHT1, GL_DIFFUSE, lightcoldiffuse1);
	    glLightfv(GL_LIGHT1, GL_AMBIENT, lightcolambient1);
	    fcenter=center;
	}
	else
	{
	    glMatrixMode(GL_PROJECTION);
	    glLoadIdentity();
	    glMatrixMode(GL_MODELVIEW);
	    glLoadIdentity();

	    gluOrtho2D(center.x-scale, center.x+scale, center.y-scale, center.y+scale);
	    float lightpos0[] = {0., 0.3, 1, 0.};
	    float lightcoldiffuse0[] = {0.8, 0.8, 0.8, 1.};
	    float lightcolspecular0[] = {0.5, 0.6, 0.7, 1.};
	    float lightcolambient0[] = {0.0, 0.0, 0.0, 1};
	    glLightfv(GL_LIGHT0, GL_POSITION, lightpos0);
	    glLightfv(GL_LIGHT0, GL_SPECULAR, lightcolspecular0);
	    glLightfv(GL_LIGHT0, GL_DIFFUSE, lightcoldiffuse0);
	    glLightfv(GL_LIGHT0, GL_AMBIENT, lightcolambient0);
	}
	//   rotate(fcenter,modmat);


	lastvdist=vdist; lastscale=scale; // remember how big the box is so
	//   we can properly draw the axes next time
	frametime=glutGet(GLUT_ELAPSED_TIME)-lastframe;
	lastframe=glutGet(GLUT_ELAPSED_TIME);
	totaltime+=frametime;
	nframes++;
	//  printf(" -- FRAME DRAWN: %d ms, %.2f ms average--\n",frametime,(float)totaltime/nframes);
	//  usleep(100);
    }
    //  else
    //  {
    //    printf("anim: I didn't understand line %s\n",line);
    //  }

    //  printf(" -- END OF IDLE t=%d--\n",glutGet(GLUT_ELAPSED_TIME));
}



void mouse(int button, int state,int x, int y)
{
    if (button == 4) {scale2 *= 1.03; vdist2 *= 1.03;}
    if (button == 3) {scale2 /= 1.03; vdist2 /= 1.03;}
    if (button == 0 && state == GLUT_DOWN) {track=1; lmx=x; lmy=y;}
    if (button == 0 && state == GLUT_UP) {track=0;} 
}

void track_mouse(int x, int y)
{
    lmx=x;
    lmy=y;
    need_guesses=1;
}

void move_mouse(int x, int y)
{
    center2.x -= 2*(x - lmx) * scale2/window_size; 
    center2.y += 2*(y - lmy) * scale2/window_size; 
    lmx = x;
    lmy = y;
}

void resize(int w, int h)
{
    window_size_x=w;
    window_size_y=h;
    if (h>w) window_size=h; else window_size=w;
    glViewport(0,0,w,h);
}

void keyb(unsigned char key, int x, int y)
{

    if (key == 'Q') {save_config(); exit(0);}
    if (key == 'A') {axes=1-axes; adef=0; update=1;}
    if (key == 'S') {sunlight = 1-sunlight;}
    if (key == 'F') {fpsdisplay = 1-fpsdisplay; update=1;}
    if (key == 'n') {circfaces++; if (circfaces>15) circfaces=15; update=1; fprintf(stderr,"circfaces -> %d\n",circfaces);}
    if (key == 'm') {circfaces--; if (circfaces<4) circfaces=4; update=1;fprintf(stderr,"circfaces -> %d\n",circfaces);}
    if (td) {
	if (key == 'q') {theta2 += 0.03; update=1;}
	if (key == 'e') {theta2 -= 0.03; update=1;}
	if (key == 'w') {phi2   += 0.03; update=1;}
	if (key == 's') {phi2   -= 0.03; update=1;}
	if (key == 'a') {psi2   += 0.03; update=1;}
	if (key == 'd') {psi2   -= 0.03; update=1;}
	if (key == '-') {vdist2 *= 1.02; scale2 *= 1.02; update=1;}
	if (key == '=') {vdist2 /= 1.02; scale2 /= 1.02; update=1;}
	if (key == '+') {vdist2 /= 1.02; update=1;}
	if (key == '_') {vdist2 *= 1.02; update=1;}
    }
    else
    {
	if (key == '=') {vdist2 /= 1.02; scale2 /= 1.02; update=1;}
	if (key == '-') {vdist2 *= 1.02; scale2 *= 1.02; update=1;}
	if (key == 'a') {center2.x += 0.02*scale2;update=1;}
	if (key == 's') {center2.y += 0.02*scale2;update=1;}
	if (key == 'd') {center2.x -= 0.02*scale2;update=1;}
	if (key == 'w') {center2.y -= 0.02*scale2;update=1;}
    }

    if (key == 'I') {inverse=1-inverse; glClearColor(inverse, inverse, inverse, 1.0); if (inverse) contrast*3; else contrast/3; update=1;}
    if (key == 'C') {ctog = 1-ctog;update=1;}
    if (key == 'H') {help = 1-help;update=1;}
    if (key == 'h') {help = 1-help;update=1;}
}

void save_config(void)
{
    FILE *fp;
    fp=fopen(".animrc2","w");
    fprintf(fp,"%d %d %lf %lf\n",axes,fpsdisplay,contrast,scale);
    fprintf(fp,"%lf %lf %lf %lf\n",theta2,phi2,psi2,vdist);
    fprintf(fp,"%lf %lf\n",center.x,center.y);
    fprintf(fp,"%d %d %d\n",inverse,ctog,help);
    fprintf(fp,"%d %d %d\n",window_size,glutGet(GLUT_WINDOW_X),glutGet(GLUT_WINDOW_Y));
    update=0;
    fclose(fp);
}

void load_config(void)
{
    glutInitWindowPosition(0,0);
    int offsetx=1, offsety=26;
    int winx, winy;
    FILE *fp;
    fp=fopen(".animrc2","r");
    if (!fp) {window_size=640; glutInitWindowSize(window_size,window_size); return;}
    if (fscanf(fp,"%d %d %lf %lf\n",&axes,&fpsdisplay,&contrast,&scale) == 0) {axes=1; fpsdisplay=0; contrast=1; scale=4;}
    if (fscanf(fp,"%lf %lf %lf %lf\n",&theta2,&phi2,&psi2,&vdist) == 0) {theta2=phi2=psi2=0; vdist=15;}
    theta=theta2;
    phi=phi2;
    psi=psi2;
    if (fscanf(fp,"%lf %lf\n",&center.x,&center.y) == 0) {center=vector(0,0,0);}
    if (fscanf(fp,"%d %d %d\n",&inverse,&ctog,&help) == 0) {inverse=0; ctog=0; help=0;}
    if (inverse) printf("Inverse set to %d\n",inverse);
    if (inverse) contrast*3;
    if (fscanf(fp,"%d %d %d\n",&window_size,&winx,&winy) == 0) 
    {
	window_size=800; 
	glutInitWindowPosition(64,64);
    }
    else
    {
	winx -= offsetx; winy-=offsety;
	glutInitWindowPosition(winx,winy);
    }
    fclose(fp);

    if (window_size_override) window_size = window_size_override;
    glutInitWindowSize(window_size,window_size);
}



int main(int argc, char **argv)
{
    fprintf(stderr,"anim v. 2.01\n");
    center=vector(0,0,0);
    theta2=0;
    psi2=0;
    phi2=0;
    theta=theta2;
    psi=psi2;
    phi=phi2;
    d_buffer = (double *) malloc (sizeof(double) * d_bufsize);
    f_buffer = (float *) malloc (sizeof(float) * f_bufsize);


    if (argc == 2)
    {
	sscanf(argv[1],"%d",&window_size_override);
    }
    //INITIALIZATION
    glutInit(&argc, argv);

    //set rgba and double buffering  
    glutInitDisplayMode(GLUT_RGBA | GLUT_DOUBLE |  GLUT_MULTISAMPLE | GLUT_DEPTH);
    load_config();

    //set window size and position and title
    glutCreateWindow("anim");

    //SET CALLBACKS
    glutDisplayFunc(disp);
    glutKeyboardFunc(keyb);
    glutIdleFunc(idle);
    glutMouseFunc(mouse);
    glutPassiveMotionFunc(track_mouse);
    glutMotionFunc(move_mouse);
    glutReshapeFunc(resize);
    //DO OPENGL INIT
    glEnable(GL_BLEND);
    glEnable(GL_MULTISAMPLE);
    glBlendFunc(GL_SRC_ALPHA,GL_ONE_MINUS_SRC_ALPHA);
    glClearColor(0.0, 0.0, 0.0, 1.0);

    glMatrixMode(GL_PROJECTION);
    glLoadIdentity();
    glDepthMask(GL_TRUE);
    glClearDepth(1.0f);
    glEnable(GL_DEPTH_TEST);
    glDepthFunc(GL_LEQUAL);

    glEnable(GL_LIGHTING);
    glEnable(GL_LIGHT0);
    glEnable(GL_LIGHT1);
    glLightModeli(GL_LIGHT_MODEL_TWO_SIDE, GL_TRUE);  

    scale2=scale;
    vdist2=vdist;
    center2=center;
    glEnable(GL_FRAMEBUFFER_SRGB); 
    if (inverse)
    {
	glClearColor(inverse, inverse, inverse, 1.0);
    }
    for (int i=0; i<NB; i++) traillen[i]=BL; 
    glutMainLoop();
}
