# Basic Instructions:
This directory comprises basic test suites for the checker algorithm, along
with a basic implementation of the SSSP certifying algorithm.
For now, there are three test cases, one is a very basic graph, the second
is a large K5 graph, and the third is a large linked list. Instructions on
compiling and running is given below
-`make` : Compiles both the normal and certifying variant of the test suites.
-`make run_normal` : runs the standard Dijkstra's algorithm on the three test cases
-`make run_certifying` : runs the certifying Dijkstra's algorithm on the three test cases, where the checker then verifies and returns the correctness of the output
-`make run_overflow` : runs a variant of the third test case where the test fails due to integer overflow -- which is expected behaviour.
-`make clean` : cleans everything
