/*
Write a function that accepts a vector of strings as a parameter,
deletes the strings that have odd lengths from it,
&& returns the resulted vector with a sorted order,
The vector is always a vector of strings && never a vector of numbers,
&& it may contain duplicates.
The order of the vector should be ascending by length of each word, && you
should return the vector sorted by that rule.
If two words have the same length, sort the vector alphabetically.
The function should return a vector of strings in sorted order.
You may assume that all words will have the same length.
For example:
assert vector_sort({"aa", "a", "aaa"}) => {"aa"}
assert vector_sort({"ab", "a", "aaa", "cd"}) => {"ab", "cd"}
*/
#include "ptr_array2_def.h"
#include "string.h"

/*@ Extern Coq (problem_149_pre_z: list (list Z) -> Prop)
               (problem_149_spec_z: list (list Z) -> list (list Z) -> Prop)
               (rows_well_formed_149: list (list Z) -> Z -> Prop)
               (row_payload_z_149: list Z -> list Z)
               (filter_even_prefix_149: list (list Z) -> Z -> list (list Z))
               (filter_even_state_149: list (list Z) -> Z -> list (list Z) -> Prop)
               (filter_even_step_keep_149:
                  list (list Z) -> Z -> list (list Z) -> Prop)
               (filter_even_step_take_149:
                  list (list Z) -> Z -> list (list Z) -> list (list Z) -> Prop)
               (string_rows_sorted: list (list Z) -> Prop)
               (Permutation: list (list Z) -> list (list Z) -> Prop)
               (rows_length: list (list Z) -> Z)
               (ptrs_length: list Z -> Z)
               (problem_149_spec_z_of_sorted_filter:
                  list (list Z) -> list (list Z) -> list (list Z) -> Prop)
               (problem_149_spec_z_of_sorted_prefix:
                  list (list Z) -> list (list Z) -> Prop)
               (Znth: {A} -> Z -> list A -> A -> A)
               (Zlength: {A} -> list A -> Z)
*/
/*@ Import Coq Require Import p149_sorted_list_sum */

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
    Ensure __return != 0 && PtrArray::undef_seg(__return, 0, size)
*/;

int cmp_word(const void *a, const void *b)
{
    const char *x = *(const char **)a;
    const char *y = *(const char **)b;
    int lx = (int)strlen(x);
    int ly = (int)strlen(y);
    if (lx != ly) {
        return lx - ly;
    }
    return strcmp(x, y);
}

void qsort(char **base, int nmemb, int elem_size,
           int (*compar)(const void *, const void *))
/*@ With l ptrs capacity
    Require
      base != 0 &&
      0 <= nmemb && nmemb <= capacity && capacity < INT_MAX &&
      elem_size == sizeof(char *) &&
      nmemb == rows_length(l) &&
      nmemb == ptrs_length(ptrs) &&
      PtrArray::seg(base, 0, nmemb, ptrs) *
      PtrArray::undef_seg(base, nmemb, capacity)
    Ensure exists sorted_rows, exists sorted_ptrs,
      nmemb == rows_length(sorted_rows) &&
      nmemb == ptrs_length(sorted_ptrs) &&
      string_rows_sorted(sorted_rows) &&
      Permutation(l, sorted_rows) &&
      PtrArray::seg(base, 0, nmemb, sorted_ptrs) *
      PtrArray::undef_seg(base, nmemb, capacity)
*/;

StrArray *sorted_list_sum(char** lst, int lst_size)
/*@ With rows
    Require
      0 <= lst_size && lst_size <= 100 &&
      rows_well_formed_149(rows, lst_size) &&
      problem_149_pre_z(rows) &&
      CharPtrArray2::full(lst, lst_size, rows)
    Ensure exists data output_rows output_ptrs output_size,
      __return != 0 &&
      data != 0 &&
      0 <= output_size && output_size <= lst_size &&
      output_size == Zlength(output_rows) &&
      output_size == Zlength(output_ptrs) &&
      problem_149_spec_z(rows, output_rows) &&
      data_at(&(__return -> data), data) *
      data_at(&(__return -> size), output_size) *
      CharPtrArray2::full(lst, lst_size, rows) *
      PtrArray::seg(data, 0, output_size, output_ptrs) *
      PtrArray::undef_seg(data, output_size, lst_size)
*/
{
    StrArray *out = malloc_str_array_struct();
    out->size = 0;
    out->data = malloc_char_ptr_array(lst_size);
    char **data = out->data;
    int output_size = 0;
    char *cur = 0;
    int len = 0;

    for (int i = 0; i < lst_size; i++) {

        cur = lst[i];

        len = (int)strlen(cur) ;
        if (len % 2 == 0) {

            data[output_size] = cur;
            output_size = output_size + 1;

        } else {

        }
    }

    qsort(data, output_size, sizeof(char *), cmp_word)
      ;

    out->size = output_size;

    return out;
}
