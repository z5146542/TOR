CC = gcc
CFLAGS = -DCERTIFYING shortest_path_checker.c

all: run

run_normal: main main2 main3
	$(CC) shortest_path_checker.c main.c -o main
	$(CC) shortest_path_checker.c main2.c -o main2
	$(CC) shortest_path_checker.c main3.c -o main3
	@echo "Test 1:"; time ./main
	@echo "Test 2:"; time ./main2
	@echo "Test 3:"; time ./main3

run: main main2 main3
	@echo "Test 1:"; time ./main
	@echo "Test 2:"; time ./main2
	@echo "Test 3:"; time ./main3

run_overflow:
	$(CC) -DOVERFLOWING $(CFLAGS) main3.c -o main3
	@echo "Test overflow (should fail):"; time ./main3

clean:
	rm main main2 main3
