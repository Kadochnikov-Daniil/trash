#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>

double myFunc(double);

int main()
{	
	double unit = M_PI/180;
	double finalTime = 0.0;
	int iterations = 40;
	struct timespec start, stop;
	double *nsecs = (double *)malloc(iterations * sizeof(double));
	
	for(int n = 0; n < iterations; n++) 
	{
		clock_gettime(CLOCK_MONOTONIC, &start);

		for (int i = -360; i < 361; i++) 
			myFunc(unit*i);

		clock_gettime(CLOCK_MONOTONIC, &stop);
		
		nsecs[n] = 1000000000 * (double)(stop.tv_sec - start.tv_sec) + (double)(stop.tv_nsec - start.tv_nsec);
	}
	
	for(int n = 1; n < iterations; n++)
	{
		printf ("Тест %d, время %lf нс\n", n, nsecs[n]);
		finalTime += nsecs[n];
	}
	
	finalTime = finalTime / iterations;
	free(nsecs);
	
	printf ("Среднее затраченное время: %lf нс\n",finalTime);
	return 0;
}
