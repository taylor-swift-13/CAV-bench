#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include <stdio.h>
#include "verification_stdlib.h"
#include "verification_list.h"

float p004_mean_absolute_deviation(float* numbers, int numbers_size){
    float sum=0;
    float avg,msum,mavg;
    int i=0;
    for (i=0;i<numbers_size;i++)
        sum+=numbers[i];
    avg=sum/numbers_size;
    msum=0;
    for (i=0;i<numbers_size;i++)
        msum+=abs(numbers[i]-avg);
    return msum/numbers_size;
}
