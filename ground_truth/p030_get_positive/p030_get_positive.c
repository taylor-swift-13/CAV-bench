/*
Return only positive numbers in the vector.
>>> get_positive({-1, 2, -4, 5, 6})
{2, 5, 6}
>>> get_positive({5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10})
{5, 3, 2, 3, 9, 123, 1}
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_30_pre_z : list Z -> Prop)
               (problem_30_spec_z : list Z -> list Z -> Prop)
               (problem_30_prefix_z : list Z -> Z -> list Z -> Prop) */
/*@ Import Coq Require Import p030_get_positive */

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray *malloc_int_array_struct()
/*@ Require emp
    Ensure __return != 0 &&
           undef_data_at(&(__return -> data)) *
           undef_data_at(&(__return -> size))
*/;

int *malloc_int_array(int size)
/*@ Require 0 <= size && size < INT_MAX && emp
    Ensure __return != 0 && IntArray::undef_full(__return, size)
*/;

IntArray *get_positive(const int* l, int l_size)
/*@ With input
    Require 0 <= l_size && l_size < INT_MAX &&
            Zlength(input) == l_size &&
            problem_30_pre_z(input) &&
            IntArray::full(l, l_size, input)
    Ensure exists data size,
      __return != 0 &&
      IntArray::full(l, l_size, input) *
      data_at(&(__return -> data), data) *
      data_at(&(__return -> size), size) *
      (((data == 0) && (size == 0) && emp) ||
       (exists output,
          (data != 0) && 0 <= size && size <= l_size &&
          Zlength(output) == size &&
          problem_30_spec_z(input, output) &&
          IntArray::seg(data, 0, size, output) *
          IntArray::undef_seg(data, size, l_size)))
*/
{
    IntArray *out = malloc_int_array_struct();
    out->size = 0;
    out->data = malloc_int_array(l_size);
    if (out->data == 0) {
        return out;
    }
    int *data = out->data;
    int output_size = 0;
    int i;
    /*@ Inv Assert
        exists output,
        l == l@pre && l_size == l_size@pre && out != 0 && data != 0 &&
        l_size < INT_MAX && Zlength(input) == l_size &&
        0 <= i && i <= l_size && 0 <= output_size && output_size <= i &&
        Zlength(output) == output_size && problem_30_pre_z(input) &&
        problem_30_prefix_z(input, i, output) &&
        data_at(&(out -> data), data) * data_at(&(out -> size), 0) *
        IntArray::full(l, l_size, input) *
        IntArray::seg(data, 0, output_size, output) *
        IntArray::undef_seg(data, output_size, l_size)
    */
    for (i=0;i<l_size;i++)
        if (l[i]>0) {
            data[output_size] = l[i];
            output_size += 1;
        }
    out->size = output_size;
    return out;
}
