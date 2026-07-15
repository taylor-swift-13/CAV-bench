/*
Return median of elements in the vector l.
>>> median({3, 1, 2, 4, 5})
3
>>> median({-10, 4, 6, 1000, 10, 20})
15.0
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "float_array_def.h"

/*@ Extern Coq (problem_47_pre_fp32 : list fp32 -> Prop)
               (problem_47_spec_fp32 : list fp32 -> list fp32 -> fp32 -> Prop) */
/*@ Import Coq Require Import p047_median */

static int cmp_float(const void* a, const void* b){
    float fa = *(const float*)a;
    float fb = *(const float*)b;
    return (fa > fb) - (fa < fb);
}

float median(float* l, int l_size)
/*@ With input
    Require 0 < l_size && l_size < INT_MAX &&
            Zlength(input) == l_size &&
            problem_47_pre_fp32(input) &&
            FloatArray::full(l, l_size, input)
    Ensure exists sorted,
           problem_47_spec_fp32(input, sorted, __return) &&
           FloatArray::full(l, l_size, sorted)
*/
{
    qsort(l, l_size, sizeof(float), cmp_float);
    if (l_size%2==1) return l[l_size/2];
    return 0.5*(l[l_size/2]+l[l_size/2-1]);
}
