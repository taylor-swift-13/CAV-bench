/*
You will be given a string of words separated by commas || spaces. Your task is
to split the string into words && return a vector of the words.

For example:
words_string("Hi, my name is John") == {"Hi", "my", "name", "is", "John"}
words_string("One, two, three, four, five, six") == {"One", 'two", 'three", "four", "five", 'six"}
*/
#include "ptr_array2_def.h"
#include "string.h"

/*@ Extern Coq (problem_101_pre_z: list Z -> Prop)
               (problem_101_spec_z: list Z -> list (list Z) -> Prop)
               (split_scan_state_101: list Z -> Z -> Z -> list (list Z) -> Prop)
               (split_scan_current_101: list Z -> Z -> list Z)
               (word_payload_101: list Z -> Z -> Z -> list Z)
               (word_row_101: list Z -> Z -> Z -> list Z)
               (words_rows_heap_101: list Z -> list (list Z) -> Assertion)
               (words_output_rows_101: list Z -> list (list Z))
               (valid_words_input_101: list Z -> Prop)
               (is_delim_z_101: Z -> bool)
               (true: bool) (false: bool)
               (c_string: list Z -> list Z)
               (Zlength: {A} -> list A -> Z)
*/
/*@ Import Coq Require Import p101_words_string */

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

StrArray *words_string(char *s)
/*@ With str_l
    Require
      valid_string(str_l) &&
      all_ascii(str_l) &&
      valid_words_input_101(str_l) &&
      string_length(str_l) + 2 < INT_MAX &&
      problem_101_pre_z(str_l) &&
      store_string(s, str_l)
    Ensure exists data output_rows output_ptrs,
      __return != 0 &&
      data != 0 &&
      Zlength(output_rows) <= string_length(str_l) + 1 &&
      Zlength(output_ptrs) == Zlength(output_rows) &&
      problem_101_spec_z(str_l, output_rows) &&
      data_at(&(__return -> data), data) *
      data_at(&(__return -> size), Zlength(output_rows)) *
      store_string(s, str_l) *
      PtrArray::seg(data, 0, Zlength(output_rows), output_ptrs) *
      PtrArray::undef_seg(data, Zlength(output_rows), string_length(str_l) + 1) *
      words_rows_heap_101(output_ptrs, output_rows)
*/
{
    int start = -1;
    int out_size = 0;
    int n = (int)strlen(s) ;
    StrArray *out = malloc_str_array_struct();
    out->size = 0;
    out->data = malloc_char_ptr_array(n + 1);
    char **data = out->data;
    int ch = 0;
    int len = 0;
    char *w = 0;

    for (int i = 0; i < n; i++) {
        ch = s[i];
        if (ch == 32 || ch == 44) {
            if (start >= 0) {
                len = i - start;
                w = malloc_char_array(len + 1);

                for (int k = 0; k < len; k++) {
                    w[k] = s[start + k];
                }
                w[len] = '\0';

                data[out_size] = w;
                out_size++;
                out->size = out_size;
                start = -1;

            } else {

            }
        } else {
            if (start < 0) {
                start = i;
            }

        }
    }
    if (start >= 0) {
        len = n - start;
        w = malloc_char_array(len + 1);

        for (int k = 0; k < len; k++) {
            w[k] = s[start + k];
        }
        w[len] = '\0';
        data[out_size] = w;
        out_size++;
        out->size = out_size;
        start = -1;
    }

    return out;
}
