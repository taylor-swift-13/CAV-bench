/*
Task
We are given two strings s && c, you have to deleted all the characters in s that are equal to any character in c
then check if the result string is palindrome.
A string is called palindrome if it reads the same backward as forward.
You should return a vector containing the result string && "True"/"False" for the check.
Example
For s = "abcde", c = "ae", the result should be ("bcd","False")
For s = "abcdef", c = "b"  the result should be ("acdef","False")
For s = "abcdedcba", c = "ab", the result should be ("cdedc","True")
*/
#include "ptr_array2_def.h"
#include "string.h"

/*@ Extern Coq (problem_112_pre_z: list Z -> list Z -> Prop)
               (problem_112_spec_z: list Z -> list Z -> list (list Z) -> Prop)
               (valid_reverse_delete_input_112: list Z -> list Z -> Prop)
               (filter_prefix_state_112: list Z -> list Z -> Z -> list Z -> Prop)
               (palindrome_scan_state_112: list Z -> Z -> Z -> Prop)
               (reverse_delete_rows_112: list Z -> list Z -> list (list Z))
               (bool_row_112: bool -> list Z)
               (pal_bool_112: list Z -> bool)
               (char_in_z_112: Z -> list Z -> Prop)
               (strchr_result: list Z -> Z -> Z -> Z -> Prop)
               (c_string: list Z -> list Z)
               (true: bool) (false: bool)
               (Zlength: {A} -> list A -> Z)
*/
/*@ Import Coq Require Import p112_reverse_delete */

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

char *malloc_true_row()
/*@ Require emp
    Ensure __return != 0 && CharArray::full(__return, 5, bool_row_112(true))
*/;

char *malloc_false_row()
/*@ Require emp
    Ensure __return != 0 && CharArray::full(__return, 6, bool_row_112(false))
*/;

StrArray *reverse_delete(char* s, char* c)
/*@ With s_l c_l
    Require
      valid_string(s_l) &&
      valid_string(c_l) &&
      valid_reverse_delete_input_112(s_l, c_l) &&
      string_length(s_l) + 2 < INT_MAX &&
      string_length(c_l) < INT_MAX &&
      problem_112_pre_z(s_l, c_l) &&
      store_string(s, s_l) *
      store_string(c, c_l)
    Ensure exists data output_rows output_ptrs,
      __return != 0 &&
      data != 0 &&
      Zlength(output_rows) == 2 &&
      Zlength(output_ptrs) == 2 &&
      output_rows == reverse_delete_rows_112(s_l, c_l) &&
      problem_112_spec_z(s_l, c_l, output_rows) &&
      data_at(&(__return -> data), data) *
      data_at(&(__return -> size), 2) *
      store_string(s, s_l) *
      store_string(c, c_l) *
	      PtrArray::seg(data, 0, 2, output_ptrs) *
	      CharArray::full(Znth(0, output_ptrs, 0), Zlength(Znth(0, output_rows, nil)), Znth(0, output_rows, nil)) *
	      CharArray::undef_seg(Znth(0, output_ptrs, 0), Zlength(Znth(0, output_rows, nil)), string_length(s_l) + 1) *
	      CharArray::full(Znth(1, output_ptrs, 0), Zlength(Znth(1, output_rows, nil)), Znth(1, output_rows, nil))
*/
{
    int n = (int)strlen(s) ;
    int k = 0;
    int pal = 1;
    int ch = 0;
    char *hit = 0;
    char *filtered = malloc_char_array(n + 1);
    StrArray *out = malloc_str_array_struct();
    out->size = 2;
    out->data = malloc_char_ptr_array(2);
    char **data = out->data;

    for (int i=0;i<n;i++) {
        ch = s[i];
        hit = strchr(c, ch) ;
        if (hit == 0) {
            filtered[k] = ch;
            k++;

        } else {

        }
    }
    filtered[k] = '\0';

    for (int i=0;i<k/2;i++) {
        if (filtered[i] != filtered[k-1-i]) {
            pal = 0;
            break;
        }
    }

    data[0] = filtered;

	char *truth = 0;
	if (pal) {
	    truth = malloc_true_row();

	    data[1] = truth;
	} else {
	    truth = malloc_false_row();

        data[1] = truth;
    }

    return out;
}
