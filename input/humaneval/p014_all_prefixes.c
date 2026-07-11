/*
Return vector of all prefixes from shortest to longest of the input string
>>> all_prefixes("abc")
{"a", "ab", "abc"}
*/
#include "ptr_array2_def.h"
#include "string.h"

/*@ Extern Coq (problem_14_pre_z: list Z -> Prop)
               (problem_14_spec_z: list Z -> list (list Z) -> Prop)
               (prefix_rows_state_14: list Z -> Z -> list (list Z) -> Prop)
               (prefix_row_payload_14: list Z -> Z -> list Z)
               (prefix_row_14: list Z -> Z -> list Z)
               (prefix_rows_heap_14: list Z -> list (list Z) -> Assertion)
               (valid_prefixes_14: list Z -> Prop)
               (Zlength: {A} -> list A -> Z)
*/
/*@ Import Coq Require Import p014_all_prefixes */

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

char *malloc_char_array(int size)
/*@ Require size > 0 && size < INT_MAX && emp
    Ensure __return != 0 && CharArray::undef_full(__return, size)
*/;

StrArray *all_prefixes(char* str)
/*@ With str_l
    Require
      valid_string(str_l) &&
      valid_prefixes_14(str_l) &&
      string_length(str_l) <= 100 &&
      problem_14_pre_z(str_l) &&
      store_string(str, str_l)
    Ensure exists data output_rows output_ptrs,
      __return != 0 &&
      data != 0 &&
      Zlength(output_rows) == string_length(str_l) &&
      Zlength(output_ptrs) == string_length(str_l) &&
      problem_14_spec_z(str_l, output_rows) &&
      data_at(&(__return -> data), data) *
      data_at(&(__return -> size), string_length(str_l)) *
      store_string(str, str_l) *
      PtrArray::seg(data, 0, string_length(str_l), output_ptrs) *
      prefix_rows_heap_14(output_ptrs, output_rows)
*/
{
    int n = (int)strlen(str) ;
    StrArray *out = malloc_str_array_struct();
    out->size = n;
    out->data = malloc_char_ptr_array(n);
    char **data = out->data;
    char *cur = 0;

    for (int i=0;i<n;i++)
    {
        cur = malloc_char_array(i + 2);

        memcpy(cur, str, i + 1) ;

        cur[i+1] = '\0';

        data[i] = cur;

    }

    return out;
}
