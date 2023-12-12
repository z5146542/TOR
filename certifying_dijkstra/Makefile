CC = gcc
CFLAGS = shortest_path_checker.c

all:
	$(CC) $(CFLAGS) main.c -o main
	$(CC) $(CFLAGS) main2.c -o main2
	$(CC) $(CFLAGS) main3.c -o main3
	$(CC) -DCERTIFYING $(CFLAGS) main.c -o main_cert
	$(CC) -DCERTIFYING $(CFLAGS) main2.c -o main2_cert
	$(CC) -DCERTIFYING $(CFLAGS) main3.c -o main3_cert

run_normal: main main2 main3
	@echo "Test 1:"; time ./main
	@echo "Test 2:"; time ./main2
	@echo "Test 3:"; time ./main3

run_certifying: main_cert main2_cert main3_cert
	@echo "Test 1:"; time ./main_cert
	@echo "Test 2:"; time ./main2_cert
	@echo "Test 3:"; time ./main3_cert

run_overflow:
	$(CC) -DCERTIFYING -DOVERFLOWING $(CFLAGS) main3.c -o main3_cert_overflow
	@echo "Test overflow (should fail):"; time ./main3_cert_overflow

clean:
	rm main main2 main3 main_cert main2_cert main3_cert main3_cert_overflow
