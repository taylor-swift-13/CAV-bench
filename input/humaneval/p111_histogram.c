/* Return every non-space character having maximal frequency. */
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"
#include "int_array_def.h"
#include "string.h"

/*@ Extern Coq (problem_111_pre_z : list Z -> Prop)
               (problem_111_spec_z : list Z -> list Z -> list Z -> Prop)
               (problem_111_scan_state_z : list Z -> Z -> list Z -> Z -> Prop)
               (problem_111_output_prefix_z : list Z -> Z -> Z -> list Z -> list Z -> Prop) */
/*@ Import Coq Require Import p111_histogram */

typedef struct {
    char *keys;
    int *values;
    int size;
} CharIntMap;

CharIntMap *malloc_char_int_map_struct()
/*@ Require emp
    Ensure __return != 0 &&
           undef_data_at(&(__return -> keys)) *
           undef_data_at(&(__return -> values)) *
           undef_data_at(&(__return -> size))
*/;

char *malloc_char_array(int size)
/*@ Require 0 <= size && size < INT_MAX && emp
    Ensure __return != 0 && CharArray::undef_full(__return, size)
*/;

int *malloc_int_array(int size)
/*@ Require 0 <= size && size < INT_MAX && emp
    Ensure __return != 0 && IntArray::undef_full(__return, size)
*/;

CharIntMap *histogram(const char *test)
/*@ With input
    Require valid_string(input) && string_length(input) < INT_MAX &&
            (forall (k : Z), (0 <= k && k < string_length(input)) =>
                (0 <= Znth(k, input, 0) && Znth(k, input, 0) < 256)) &&
            problem_111_pre_z(input) && store_string(test, input)
    Ensure exists keys values size,
      __return != 0 && store_string(test, input) *
      data_at(&(__return -> keys), keys) *
      data_at(&(__return -> values), values) *
      data_at(&(__return -> size), size) *
      (((keys == 0 || values == 0) && size == 0 && emp) ||
       (exists key_list value_list,
          keys != 0 && values != 0 && 0 <= size && size <= 256 &&
          Zlength(key_list) == size && Zlength(value_list) == size &&
          problem_111_spec_z(input, key_list, value_list) &&
          CharArray::seg(keys, 0, size, key_list) *
          CharArray::undef_seg(keys, size, 256) *
          IntArray::seg(values, 0, size, value_list) *
          IntArray::undef_seg(values, size, 256)))
*/
{
    int count[256];
    CharIntMap *out = malloc_char_int_map_struct();
    int max = 0;
    char *keys = malloc_char_array(256);
    int *values = malloc_int_array(256);
    out->keys = keys;
    out->values = values;
    out->size = 0;
    int size = 0;
    int i;
    for (i = 0; i < 256; ++i) {
        count[i] = 0;
    }
    for (i = 0; test[i] != '\0'; ++i) {
        if (test[i] != ' ') {
            int current = test[i];
            if (0 <= current && current < 256) {
                count[current] += 1;
                if (count[current] > max) max = count[current];
            }
        }
    }
    int ch;
    for (ch = 0; ch < 256; ++ch) {
        if (count[ch] == max && max > 0) {
            keys[size] = (char)ch;
            values[size] = count[ch];
            size += 1;
        }
    }
    out->size = size;
    return out;
}
