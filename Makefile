all: anim membrane-demo

anim: anim.c vector.h makepng.c makepng.h
	g++ makepng.c anim.c -lGL -lGLU -lglut -lGLEW -lpng -lm -o anim -O3

anim-mac: anim-mac.c
	g++ anim-mac.c -framework GLUT -framework OpenGL -framework Cocoa -o anim -I/usr/local/include/

membrane-demo: membrane.C
	g++ membrane.C -O4 -o membrane-demo

install:
	cp anim /usr/local/bin/
	cp plot /usr/local/bin/
