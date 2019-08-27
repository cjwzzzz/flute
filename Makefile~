
CC = g++ -g -std=c++0x
CFLAGS = -O3 -I.

SRC     =  flute.cpp mst2.cpp heap.cpp dist.cpp dl.cpp err.cpp neighbors.cpp
OBJ     = $(SRC:.cpp=.o)

all: flute-data 

flute-data: flute-data.cpp ${OBJ}
	$(CC) $(CFLAGS) -o flute-data flute-data.cpp ${OBJ} -lm
clean:
	rm -f *.o core*
