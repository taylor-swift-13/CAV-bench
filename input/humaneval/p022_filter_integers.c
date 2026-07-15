/* Filter a heterogeneous sequence, retaining its integer elements in order.
   The C boundary encodes each dynamic value by a tag plus its integer payload. */
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_22_pre_c : list Z -> list Z -> Prop)
               (problem_22_spec_c : list Z -> list Z -> list Z -> Prop)
               (problem_22_prefix_c : list Z -> list Z -> Z -> list Z -> Prop) */
/*@ Import Coq Require Import p022_filter_integers */

typedef enum { PY_INT = 0, PY_DOUBLE = 1, PY_STRING = 2 } PyType;

typedef struct {
    int *data;
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

IntArray *filter_integers(const int *types, const int *int_values, int values_size)
/*@ With tags values
    Require 0 <= values_size && values_size < INT_MAX &&
            Zlength(tags) == values_size &&
            Zlength(values) == values_size &&
            problem_22_pre_c(tags, values) &&
            IntArray::full(types, values_size, tags) *
            IntArray::full(int_values, values_size, values)
    Ensure exists data size,
      __return != 0 &&
      IntArray::full(types, values_size, tags) *
      IntArray::full(int_values, values_size, values) *
      data_at(&(__return -> data), data) *
      data_at(&(__return -> size), size) *
      (((data == 0) && (size == 0) && emp) ||
       (exists output,
          data != 0 && 0 <= size && size <= values_size &&
          Zlength(output) == size &&
          problem_22_spec_c(tags, values, output) &&
          IntArray::seg(data, 0, size, output) *
          IntArray::undef_seg(data, size, values_size)))
*/
{
    IntArray *out = malloc_int_array_struct();
    out->size = 0;
    out->data = malloc_int_array(values_size);
    if (out->data == 0) return out;
    int *data = out->data;
    int output_size = 0;
    int i;
    for (i = 0; i < values_size; ++i) {
        if (types[i] == PY_INT) {
            data[output_size] = int_values[i];
            output_size += 1;
        }
    }
    out->size = output_size;
    return out;
}
