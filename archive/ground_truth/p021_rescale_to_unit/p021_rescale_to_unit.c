/*
Given vector of numbers (of at least two elements), apply a linear transform to that vector,
such that the smallest number will become 0 && the largest will become 1
>>> rescale_to_unit({1.0, 2.0, 3.0, 4.0, 5.0})
{0.0, 0.25, 0.5, 0.75, 1.0}
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "float_array_def.h"

/*@ Extern Coq (problem_21_pre_fp32 : list fp32 -> Prop)
               (problem_21_spec_fp32 : list fp32 -> list fp32 -> Prop) */
/*@ Import Coq Require Import p021_rescale_to_unit */

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


FloatArray *rescale_to_unit(const float* numbers, int numbers_size)
/*@ With input
    Require 2 <= numbers_size && numbers_size < INT_MAX &&
            Zlength(input) == numbers_size &&
            problem_21_pre_fp32(input) &&
            FloatArray::full(numbers, numbers_size, input)
    Ensure exists data size,
      __return != 0 &&
      FloatArray::full(numbers, numbers_size, input) *
      data_at(&(__return -> data), data) *
      data_at(&(__return -> size), size) *
      (((data == 0) && (size == 0) && emp) ||
       (exists output,
          (data != 0) && (size == numbers_size) &&
          Zlength(output) == numbers_size &&
          problem_21_spec_fp32(input, output) &&
          FloatArray::full(data, numbers_size, output)))
*/
{
    float min=100000,max=-100000;
    FloatArray *out = malloc_float_array_struct();
    out->data = malloc_float_array(numbers_size);
    out->size = numbers_size;
    if (out->data == 0) {
        out->size = 0;
        return out;
    }

    for (int i=0;i<numbers_size;i++)
        {
            if (numbers[i]<min) min=numbers[i];
            if (numbers[i]>max) max=numbers[i];
        }
    if (max == min) {
        for (int i = 0; i < numbers_size; i++) {
            out->data[i] = 0.0f;
        }
        return out;
    }

    for (int i=0;i<numbers_size;i++)
        out->data[i]=(numbers[i]-min)/(max-min);
    return out;
}
