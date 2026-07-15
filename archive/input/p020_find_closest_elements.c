/*
From a supplied vector of numbers (of length at least two) select && return two that are the closest to each
other && return them in order (smaller number, larger number).
>>> find_closest_elements({1.0, 2.0, 3.0, 4.0, 5.0, 2.2})
(2.0, 2.2)
>>> find_closest_elements({1.0, 2.0, 3.0, 4.0, 5.0, 2.0})
(2.0, 2.0)
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "float_array_def.h"

/*@ Extern Coq (problem_20_pre_fp32 : list fp32 -> Prop)
               (problem_20_spec_fp32 : list fp32 -> list fp32 -> Prop) */
/*@ Import Coq Require Import p020_find_closest_elements */

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


FloatArray *find_closest_elements(const float* numbers, int numbers_size)
/*@ With input
    Require 2 <= numbers_size && numbers_size < INT_MAX &&
            Zlength(input) == numbers_size &&
            problem_20_pre_fp32(input) &&
            FloatArray::full(numbers, numbers_size, input)
    Ensure exists data size,
      __return != 0 &&
      FloatArray::full(numbers, numbers_size, input) *
      data_at(&(__return -> data), data) *
      data_at(&(__return -> size), size) *
      (((data == 0) && (size == 0) && emp) ||
       (exists output,
          (data != 0) && (size == 2) &&
          Zlength(output) == 2 &&
          problem_20_spec_fp32(input, output) &&
          FloatArray::full(data, 2, output)))
*/
{
    FloatArray *out = malloc_float_array_struct();
    out->data = malloc_float_array(2);
    out->size = 2;

    if (out->data == 0) {
        out->size = 0;
        return out;
    }

    out->data[0] = numbers[0];
    out->data[1] = numbers[1];
    for (int i=0;i<numbers_size;i++)
    for (int j=i+1;j<numbers_size;j++)
        if (fabsf(numbers[i]-numbers[j]) < fabsf(out->data[0]-out->data[1])) {
            out->data[0] = numbers[i];
            out->data[1] = numbers[j];
        }
    if (out->data[0] > out->data[1]) {
        float t = out->data[0];
        out->data[0] = out->data[1];
        out->data[1] = t;
    }
    return out;
}
