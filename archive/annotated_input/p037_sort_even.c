/*
This function takes a vector l && returns a vector l' such that
l' is identical to l in the odd indicies, while its values at the even indicies are equal
to the values of the even indicies of l, but sorted.
>>> sort_even({1, 2, 3})
{1, 2, 3}
>>> sort_even({5, 6, 3, 4})
{3, 6, 5, 4}
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "float_array_def.h"

/*@ Extern Coq (problem_37_pre_fp32 : list fp32 -> Prop)
               (problem_37_spec_fp32 : list fp32 -> list fp32 -> Prop) */
/*@ Import Coq Require Import p037_sort_even */

typedef struct {
    float* data;
    int size;
} FloatArray;

FloatArray *malloc_float_array_struct()
/*@ Require emp
    Ensure __return != 0 &&
           undef_data_at(&(__return -> data)) *
           undef_data_at(&(__return -> size))
*/;

float *malloc_float_array(int size)
/*@ Require 0 <= size && size < INT_MAX && emp
    Ensure __return != 0 && FloatArray::undef_full(__return, size)
*/;

void free_float_array(float *array, int size)
/*@ With contents
    Require 0 <= size && size < INT_MAX &&
            Zlength(contents) == size && FloatArray::full(array, size, contents)
    Ensure emp
*/;


static int cmp_float(const void* a, const void* b) {
    float x = *(const float*)a;
    float y = *(const float*)b;
    return (x > y) - (x < y);
}

FloatArray *sort_even(const float* l, int l_size)
/*@ With input
    Require 0 <= l_size && l_size < INT_MAX &&
            Zlength(input) == l_size &&
            problem_37_pre_fp32(input) &&
            FloatArray::full(l, l_size, input)
    Ensure exists data size,
      __return != 0 &&
      FloatArray::full(l, l_size, input) *
      data_at(&(__return -> data), data) *
      data_at(&(__return -> size), size) *
      (((data == 0) && (size == 0) && emp) ||
       (exists output,
          (data != 0) && (size == l_size) &&
          Zlength(output) == l_size &&
          problem_37_spec_fp32(input, output) &&
          FloatArray::full(data, l_size, output)))
*/
{
    FloatArray *out = malloc_float_array_struct();
    float* even;
    int even_size = (l_size + 1) / 2;
    out->size = l_size;
    out->data = malloc_float_array(l_size);
    if (out->data == 0) {
        out->size = 0;
        return out;
    }
    even = malloc_float_array(even_size);
    if (even == 0) {
        free_float_array(out->data, l_size);
        out->data = 0;
        out->size = 0;
        return out;
    }
    for (int i=0;i*2<l_size;i++)
        even[i] = l[i*2];
    qsort(even, (size_t)even_size, sizeof(float), cmp_float);
    for (int i=0;i<l_size;i++)
    {
        if (i%2==0) out->data[i] = even[i/2];
        if (i%2==1) out->data[i] = l[i];
    }
    free_float_array(even, even_size);
    return out;
}
