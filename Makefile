all: 6hole 6hole-cube

6hole: 6hole.c
	gcc 6hole.c -std=c99 -O2 -o 6hole

6hole-cube: 6hole-cube.c
	gcc 6hole-cube.c -std=c99 -O2 -o 6hole-cube

clean:
	rm 6hole 6hole-cube
