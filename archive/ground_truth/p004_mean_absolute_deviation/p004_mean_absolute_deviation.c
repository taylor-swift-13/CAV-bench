/*
For a given vector of input numbers, calculate Mean Absolute Deviation
around the mean of this dataset.
Mean Absolute Deviation is the average absolute difference between each
element && a centerpoint (mean in this case):
MAD = average | x - x_mean |
>>> mean_absolute_deviation({1.0, 2.0, 3.0, 4.0})
1.0
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "float_array_def.h"

/*@ Extern Coq (problem_4_pre_fp32 : list fp32 -> Prop)
               (problem_4_spec_fp32 : list fp32 -> fp32 -> Prop) */
/*@ Import Coq Require Import p004_mean_absolute_deviation */

float mean_absolute_deviation(float* numbers, int numbers_size)
/*@ With l
    Require 0 < numbers_size && numbers_size < INT_MAX &&
            Zlength(l) == numbers_size &&
            problem_4_pre_fp32(l) &&
            FloatArray::full(numbers, numbers_size, l)
    Ensure problem_4_spec_fp32(l, __return) &&
           FloatArray::full(numbers, numbers_size, l)
*/
{
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
