default: libmemory.so random

libmemory.so: memory.c mem.s support.c
	gcc -Werror -shared -O3 -fPIC -o libmemory.so mem.s memory.c support.c -lpthread

random: RandomGraph.c
	gcc -O3 -L`pwd` -Wl,-rpath=`pwd` -o random RandomGraph.c -lmemory

run:
	/usr/bin/time -v ./random

clean:
	rm libmemory.so random

