/*
Concatenate vector of strings into a single string
>>> concatenate({})
""
>>> concatenate({"a", "b", "c"})
"abc"
*/
#include "ptr_array2_def.h"
#include "string.h"

/*@ Extern Coq (problem_28_pre_z: list (list Z) -> Prop)
               (problem_28_spec_z: list (list Z) -> list Z -> Prop)
               (rows_well_formed_28: list (list Z) -> Z -> Prop)
               (row_payload_z_28: list Z -> list Z)
               (row_len_z_28: list Z -> Z)
               (total_prefix_state_28: list (list Z) -> Z -> Z -> Prop)
               (copy_prefix_state_28: list (list Z) -> Z -> Z -> list Z -> Prop)
               (concat_prefix_payload_28: list (list Z) -> Z -> list Z)
               (concat_prefix_len_28: list (list Z) -> Z -> Z)
               (Znth: {A} -> Z -> list A -> A -> A)
               (Zlength: {A} -> list A -> Z)
*/
/*@ Import Coq Require Import p028_concatenate */

char *malloc_char_array(int n)
/*@ Require n > 0 && n < INT_MAX && emp
    Ensure __return != 0 && CharArray::undef_full(__return, n)
*/
;

char* concatenate(char** strings, int strings_size)
/*@ With rows
    Require
      0 <= strings_size && strings_size <= 100 &&
      rows_well_formed_28(rows, strings_size) &&
      (forall (p: Z), (0 <= p && p <= strings_size) =>
        (concat_prefix_len_28(rows, p) + 1 < INT_MAX)) &&
      problem_28_pre_z(rows) &&
      CharPtrArray2::full(strings, strings_size, rows)
    Ensure exists out_l,
      problem_28_spec_z(rows, out_l) &&
      CharPtrArray2::full(strings, strings_size, rows) *
      CharArray::full(__return, Zlength(out_l) + 1, app(out_l, cons(0, nil)))
*/
{
    int total = 1;
    char* out = 0;
    int k = 0;
    int len0 = 0;
    int len = 0;
    char *cur = 0;

    for (int i=0;i<strings_size;i++) {

        cur = strings[i];

        len0 = (int)strlen(cur) ;

        total += len0;

    }
    out = malloc_char_array(total);

    for (int i=0;i<strings_size;i++) {

        cur = strings[i];

        len = (int)strlen(cur) ;

        memcpy(out + k, cur, len) ;
        k += len;

    }

    out[k] = '\0';

    return out;
}
