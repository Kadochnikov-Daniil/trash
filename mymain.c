#include <stdio.h>
#include <math.h>

double myFunc(double);

int main(void)
{
	double n = M_PI;
	double maxVal = 0;
	double mySinRes;
	double muslRes;

	for (double x=-720;x<721;x+=1)
	{
		mySinRes = myFunc(M_PI*x/180);
		muslRes = sin(M_PI*x/180);
		printf ("sin(%lf): musl %lf; mySin %lf\n", x, muslRes, mySinRes);
		maxVal = fmax(maxVal, fabs(muslRes - mySinRes));
	}
	printf ("Result %.10lf\n", maxVal);
	
	double x = 1.0 / 0.0;
    	printf("%lf\n", myFunc(x));
    	double y = log (0);
    	printf("%lf\n", myFunc(y));
    	double z = sqrt (-1);
    	printf("%lf\n", myFunc(z));

	return 0;
}
