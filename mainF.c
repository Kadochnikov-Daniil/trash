#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>

int main()
{	
	double unit = M_PI/180;
	double input;
	int iterations = 100000;
	double result;
	double *nsecs = (double *)malloc(722 * sizeof(double));
	double finalTime = 0.0;
	struct timespec start, stop;
	for (int i = -361; i < 361; i++) 
	{
		input = unit*i;
		clock_gettime(CLOCK_MONOTONIC, &start);

		for(int n = 0; n < iterations; n++) 
			result = sin(input);

		clock_gettime(CLOCK_MONOTONIC, &stop);
		
		nsecs[i + 361] = 1000000000 * (double)(stop.tv_sec - start.tv_sec) + (double)(stop.tv_nsec - start.tv_nsec);
	}
	FILE *output;
  	char name[] = "result.txt";
  	if ((output = fopen(name, "a")) == NULL)
  	{
    		printf("Не удалось открыть файл");
    		return 0;
  	}
  	
	for(int n = 1; n < 722; n++)
	{
		fprintf(output, "%d - %lf\n", n - 361, nsecs[n]);
		finalTime += nsecs[n];
	}
	
	finalTime = finalTime / (iterations * 721);
	fprintf(output, "Среднее затраченное время %lf\n\n", finalTime);
	
	fclose(output);
	free(nsecs);
	
	return 0;
}
