/*
Check if in given vector of numbers, are any two numbers closer to each other than
given threshold.
>>> has_close_elements({1.0, 2.0, 3.0}, 0.5)
false
>>> has_close_elements({1.0, 2.8, 3.0, 4.0, 5.0, 2.0}, 0.3)
true
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "float_array_def.h"

/*@ Extern Coq
      (problem_0_pre_fp32 : fp32 -> Prop)
      (problem_0_spec_fp32 : list fp32 -> fp32 -> Z -> Prop)
*/
/*@ Import Coq Require Import p000_has_close_elements */

int has_close_elements(float* numbers, int numbers_size, float threshold)
/*@ With l
    Require 0 <= numbers_size && numbers_size < INT_MAX &&
            Zlength(l) == numbers_size &&
            problem_0_pre_fp32(threshold) &&
            (forall (k: Z), (0 <= k && k < numbers_size) =>
                fp32_isFinite(Znth(k, l, fp32(0.0)))) &&
            FloatArray::full(numbers, numbers_size, l)
    Ensure problem_0_spec_fp32(l, threshold@pre, __return) &&
           FloatArray::full(numbers, numbers_size, l)
*/
{
    int i,j;

    for (i=0;i<numbers_size;i++)
    for (j=i+1;j<numbers_size;j++)
    if (abs(numbers[i]-numbers[j])<threshold)
    return 1;

    return 0;
}
