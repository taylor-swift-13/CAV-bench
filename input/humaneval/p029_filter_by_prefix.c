/*
Filter an input vector of strings only for ones that start with a given prefix.
>>> filter_by_prefix({}, "a")
{}
>>> filter_by_prefix({"abc", "bcd", "cde", "vector"}, "a")
{"abc", "vector"}
*/
#include "ptr_array2_def.h"
#include "string.h"

/*@ Extern Coq (problem_29_pre_z: list (list Z) -> Prop)
               (problem_29_spec_z: list (list Z) -> list Z -> list (list Z) -> Prop)
               (rows_well_formed_29: list (list Z) -> Z -> Prop)
               (row_payload_z_29: list Z -> list Z)
               (row_len_z_29: list Z -> Z)
               (prefix_match_z_29: list Z -> list Z -> Prop)
               (filter_prefix_state_29: list (list Z) -> list Z -> Z -> list (list Z) -> Prop)
               (Znth: {A} -> Z -> list A -> A -> A)
               (Zlength: {A} -> list A -> Z)
*/
/*@ Import Coq Require Import p029_filter_by_prefix */

typedef struct {
    char** data;
    int size;
} StrArray;

StrArray *malloc_str_array_struct()
/*@ Require emp
    Ensure __return != 0 &&
           undef_data_at(&(__return -> data)) *
           undef_data_at(&(__return -> size))
*/;

char **malloc_char_ptr_array(int size)
/*@ Require 0 <= size && size < INT_MAX && emp
    Ensure __return != 0 && PtrArray::undef_full(__return, size)
*/;

StrArray *filter_by_prefix(char** strings, int strings_size, char* prefix)
/*@ With rows prefix_l
    Require
      0 <= strings_size && strings_size <= 100 &&
      rows_well_formed_29(rows, strings_size) &&
      valid_string(prefix_l) &&
      string_length(prefix_l) < INT_MAX &&
      problem_29_pre_z(rows) &&
      CharPtrArray2::full(strings, strings_size, rows) *
      store_string(prefix, prefix_l)
    Ensure exists data output_rows output_ptrs output_size,
      __return != 0 &&
      0 <= output_size && output_size <= strings_size &&
      output_size == Zlength(output_rows) &&
      output_size == Zlength(output_ptrs) &&
      problem_29_spec_z(rows, prefix_l, output_rows) &&
      data_at(&(__return -> data), data) *
      data_at(&(__return -> size), output_size) *
      CharPtrArray2::full(strings, strings_size, rows) *
      store_string(prefix, prefix_l) *
      PtrArray::seg(data, 0, output_size, output_ptrs) *
      PtrArray::undef_seg(data, output_size, strings_size)
*/
{
    int plen = (int)strlen(prefix) ;
    StrArray *out = malloc_str_array_struct();
    out->size = 0;
    out->data = malloc_char_ptr_array(strings_size);
    char **data = out->data;
    int output_size = 0;
    int cmp = 0;
    char *cur = 0;

    for (int i=0;i<strings_size;i++) {

        cur = strings[i];

        cmp = strncmp(cur, prefix, plen) ;
        if (cmp == 0) {

            data[output_size] = cur;
            output_size = output_size + 1;

        } else {

        }
    }
    out->size = output_size;
    return out;
}
