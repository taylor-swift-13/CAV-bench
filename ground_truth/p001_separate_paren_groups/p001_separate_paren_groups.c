/*
Input to this function is a string containing multiple groups of nested parentheses. Your goal is to
separate those group into separate strings && return the vector of those.
Separate groups are balanced (each open brace is properly closed) && ! nested within each other
Ignore any spaces in the input string.
>>> separate_paren_groups("( ) (( )) (( )( ))")
{"()", "(())", "(()())"}
*/
#include "ptr_array2_def.h"
#include "string.h"

/*@ Extern Coq (problem_1_pre_z: list Z -> Prop)
               (problem_1_spec_z: list Z -> list (list Z) -> Prop)
               (paren_scan_state_1: list Z -> Z -> Z -> Z -> list (list Z) -> Prop)
               (paren_payload_1: list Z -> Z -> Z -> list Z)
               (paren_row_1: list Z -> Z -> Z -> list Z)
               (paren_rows_heap_1: list Z -> list (list Z) -> Assertion)
               (paren_output_rows_1: list Z -> list (list Z))
               (valid_paren_input_1: list Z -> Prop)
               (paren_safe_input_1: list Z -> Prop)
               (Zlength: {A} -> list A -> Z)
*/
/*@ Import Coq Require Import p001_separate_paren_groups */

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

StrArray *separate_paren_groups(char *paren_string)
/*@ With str_l
    Require
      valid_string(str_l) &&
      all_ascii(str_l) &&
      valid_paren_input_1(str_l) &&
      paren_safe_input_1(str_l) &&
      string_length(str_l) + 2 < INT_MAX &&
      problem_1_pre_z(str_l) &&
      store_string(paren_string, str_l)
    Ensure exists data output_rows output_ptrs,
      __return != 0 &&
      data != 0 &&
      0 <= Zlength(output_rows) &&
      Zlength(output_rows) < INT_MAX &&
      Zlength(output_rows) <= string_length(str_l) + 1 &&
      Zlength(output_ptrs) == Zlength(output_rows) &&
      problem_1_spec_z(str_l, output_rows) &&
      data_at(&(__return -> data), data) *
      data_at(&(__return -> size), Zlength(output_rows)) *
      store_string(paren_string, str_l) *
      PtrArray::seg(data, 0, Zlength(output_rows), output_ptrs) *
      PtrArray::undef_seg(data, Zlength(output_rows), string_length(str_l) + 1) *
      paren_rows_heap_1(output_ptrs, output_rows)
*/
{
    int n = (int)strlen(paren_string) /*@ where str = str_l */;
    StrArray *out = malloc_str_array_struct();
    out->size = 0;
    out->data = malloc_char_ptr_array(n + 1);
    char **data = out->data;
    int out_size = 0;
    int level = 0;
    int start = -1;
    int ch = 0;
    int len = 0;
    /*@ Inv Assert
      exists output_rows output_ptrs,
      0 <= i && i <= n &&
      n == string_length(str_l) &&
      paren_string == paren_string@pre &&
      out != 0 &&
      data != 0 &&
      0 <= out_size && out_size <= i &&
      out_size == Zlength(output_rows) &&
      Zlength(output_ptrs) == out_size &&
      0 <= level && level <= i &&
      -1 <= start && start < i &&
      0 <= ch && ch <= 127 &&
      0 <= len && len < INT_MAX &&
      valid_string(str_l) &&
      all_ascii(str_l) &&
      valid_paren_input_1(str_l) &&
      paren_safe_input_1(str_l) &&
      string_length(str_l) + 2 < INT_MAX &&
      problem_1_pre_z(str_l) &&
      paren_scan_state_1(str_l, i, level, start, output_rows) &&
      data_at(&(out -> data), data) *
      data_at(&(out -> size), Zlength(output_rows)) *
      store_string(paren_string@pre, str_l) *
      PtrArray::seg(data, 0, Zlength(output_rows), output_ptrs) *
      PtrArray::undef_seg(data, Zlength(output_rows), string_length(str_l) + 1) *
      paren_rows_heap_1(output_ptrs, output_rows)
    */
    for (int i = 0; i < n; i++) {
        ch = paren_string[i];
        if (ch == 40) {
            if (level == 0) {
                start = i;
            }
            level = level + 1;
            /*@ Assert
              exists output_rows output_ptrs,
              0 <= i && i < n &&
              n == string_length(str_l) &&
              paren_string == paren_string@pre &&
              out != 0 &&
              data != 0 &&
              0 <= out_size && out_size <= i &&
              out_size == Zlength(output_rows) &&
              Zlength(output_ptrs) == out_size &&
              ch == 40 &&
              0 <= level && level <= i + 1 &&
              0 <= start && start <= i &&
              0 <= ch && ch <= 127 &&
              0 <= len && len < INT_MAX &&
              valid_string(str_l) &&
              all_ascii(str_l) &&
              valid_paren_input_1(str_l) &&
              paren_safe_input_1(str_l) &&
              string_length(str_l) + 2 < INT_MAX &&
              problem_1_pre_z(str_l) &&
              paren_scan_state_1(str_l, i + 1, level, start, output_rows) &&
              data_at(&(out -> data), data) *
              data_at(&(out -> size), out_size) *
              store_string(paren_string@pre, str_l) *
              PtrArray::seg(data, 0, out_size, output_ptrs) *
              PtrArray::undef_seg(data, out_size, n + 1) *
              paren_rows_heap_1(output_ptrs, output_rows)
            */
        } else {
            if (ch == 41) {
                level = level - 1;
                if (level == 0) {
                    len = i - start + 1;
                    char *row = malloc_char_array(len + 1);
                    /*@ Inv Assert
                      exists output_rows output_ptrs,
                      0 <= i && i < n &&
                      n == string_length(str_l) &&
                      paren_string == paren_string@pre &&
                      out != 0 &&
                      data != 0 &&
                      row != 0 &&
                      0 <= out_size && out_size <= i &&
                      out_size == Zlength(output_rows) &&
                      Zlength(output_ptrs) == out_size &&
                      ch == 41 &&
                      ch == Znth(i, c_string(str_l), 0) &&
                      level == 0 &&
                      0 <= start && start <= i &&
                      len == i - start + 1 &&
                      0 <= k && k <= len &&
                      valid_string(str_l) &&
                      all_ascii(str_l) &&
                      valid_paren_input_1(str_l) &&
                      paren_safe_input_1(str_l) &&
                      string_length(str_l) + 2 < INT_MAX &&
                      problem_1_pre_z(str_l) &&
                      paren_scan_state_1(str_l, i, 1, start, output_rows) &&
                      Zlength(paren_payload_1(str_l, start, i + 1)) == len &&
                      data_at(&(out -> data), data) *
                      data_at(&(out -> size), out_size) *
                      store_string(paren_string@pre, str_l) *
                      PtrArray::seg(data, 0, out_size, output_ptrs) *
                      PtrArray::undef_seg(data, out_size, n + 1) *
                      paren_rows_heap_1(output_ptrs, output_rows) *
                      CharArray::full(row, k, paren_payload_1(str_l, start, start + k)) *
                      CharArray::undef_seg(row, k, len + 1)
                    */
                    for (int k = 0; k < len; k++) {
                        row[k] = paren_string[start + k];
                    }
                    row[len] = '\0';
                    /*@ Assert
                      exists output_rows output_ptrs,
                      0 <= i && i < n &&
                      n == string_length(str_l) &&
                      paren_string == paren_string@pre &&
                      out != 0 &&
                      data != 0 &&
                      row != 0 &&
                      0 <= out_size && out_size <= i &&
                      out_size == Zlength(output_rows) &&
                      Zlength(output_ptrs) == out_size &&
                      ch == 41 &&
                      ch == Znth(i, c_string(str_l), 0) &&
                      level == 0 &&
                      0 <= start && start <= i &&
                      len == i - start + 1 &&
                      valid_string(str_l) &&
                      all_ascii(str_l) &&
                      valid_paren_input_1(str_l) &&
                      paren_safe_input_1(str_l) &&
                      string_length(str_l) + 2 < INT_MAX &&
                      problem_1_pre_z(str_l) &&
                      paren_scan_state_1(str_l, i, 1, start, output_rows) &&
                      data_at(&(out -> data), data) *
                      data_at(&(out -> size), out_size) *
                      store_string(paren_string@pre, str_l) *
                      PtrArray::seg(data, 0, out_size, output_ptrs) *
                      PtrArray::undef_seg(data, out_size, n + 1) *
                      paren_rows_heap_1(output_ptrs, output_rows) *
                      CharArray::full(row, len + 1, paren_row_1(str_l, start, i + 1))
                    */
                    data[out_size] = row;
                    out_size++;
                    out->size = out_size;
                    start = -1;
                    /*@ Assert
                      exists output_rows output_ptrs,
                      0 <= i && i < n &&
                      n == string_length(str_l) &&
                      paren_string == paren_string@pre &&
                      out != 0 &&
                      data != 0 &&
                      row != 0 &&
                      0 <= out_size && out_size <= i + 1 &&
                      out_size == Zlength(output_rows) &&
                      Zlength(output_ptrs) == out_size &&
                      ch == 41 &&
                      ch == Znth(i, c_string(str_l), 0) &&
                      level == 0 &&
                      start == -1 &&
                      0 <= len && len < INT_MAX &&
                      valid_string(str_l) &&
                      all_ascii(str_l) &&
                      valid_paren_input_1(str_l) &&
                      paren_safe_input_1(str_l) &&
                      string_length(str_l) + 2 < INT_MAX &&
                      problem_1_pre_z(str_l) &&
                      paren_scan_state_1(str_l, i + 1, level, start, output_rows) &&
                      data_at(&(out -> data), data) *
                      data_at(&(out -> size), out_size) *
                      store_string(paren_string@pre, str_l) *
                      PtrArray::seg(data, 0, out_size, output_ptrs) *
                      PtrArray::undef_seg(data, out_size, n + 1) *
                      paren_rows_heap_1(output_ptrs, output_rows)
                    */
                } else {
                    /*@ Assert
                      exists output_rows output_ptrs,
                      0 <= i && i < n &&
                      n == string_length(str_l) &&
                      paren_string == paren_string@pre &&
                      out != 0 &&
                      data != 0 &&
                      0 <= out_size && out_size <= i &&
                      out_size == Zlength(output_rows) &&
                      Zlength(output_ptrs) == out_size &&
                      ch == 41 &&
                      0 < level && level <= i &&
                      0 <= start && start < i &&
                      0 <= ch && ch <= 127 &&
                      0 <= len && len < INT_MAX &&
                      valid_string(str_l) &&
                      all_ascii(str_l) &&
                      valid_paren_input_1(str_l) &&
                      paren_safe_input_1(str_l) &&
                      string_length(str_l) + 2 < INT_MAX &&
                      problem_1_pre_z(str_l) &&
                      paren_scan_state_1(str_l, i + 1, level, start, output_rows) &&
                      data_at(&(out -> data), data) *
                      data_at(&(out -> size), out_size) *
                      store_string(paren_string@pre, str_l) *
                      PtrArray::seg(data, 0, out_size, output_ptrs) *
                      PtrArray::undef_seg(data, out_size, n + 1) *
                      paren_rows_heap_1(output_ptrs, output_rows)
                    */
                }
            } else {
                /*@ Assert
                  exists output_rows output_ptrs,
                  0 <= i && i < n &&
                  n == string_length(str_l) &&
                  paren_string == paren_string@pre &&
                  out != 0 &&
                  data != 0 &&
                  0 <= out_size && out_size <= i &&
                  out_size == Zlength(output_rows) &&
                  Zlength(output_ptrs) == out_size &&
                  ch == 32 &&
                  0 <= level && level <= i &&
                  -1 <= start && start < i &&
                  0 <= ch && ch <= 127 &&
                  0 <= len && len < INT_MAX &&
                  valid_string(str_l) &&
                  all_ascii(str_l) &&
                  valid_paren_input_1(str_l) &&
                  paren_safe_input_1(str_l) &&
                  string_length(str_l) + 2 < INT_MAX &&
                  problem_1_pre_z(str_l) &&
                  paren_scan_state_1(str_l, i + 1, level, start, output_rows) &&
                  data_at(&(out -> data), data) *
                  data_at(&(out -> size), out_size) *
                  store_string(paren_string@pre, str_l) *
                  PtrArray::seg(data, 0, out_size, output_ptrs) *
                  PtrArray::undef_seg(data, out_size, n + 1) *
                  paren_rows_heap_1(output_ptrs, output_rows)
                */
            }
        }
    }
    /*@ Assert
      exists output_rows output_ptrs,
      n == string_length(str_l) &&
      paren_string == paren_string@pre &&
      out != 0 &&
      out == out &&
      data != 0 &&
      data == data &&
      0 <= out_size && out_size <= n + 1 &&
      out_size < INT_MAX &&
      out_size == Zlength(output_rows) &&
      Zlength(output_rows) <= string_length(str_l) + 1 &&
      Zlength(output_rows) < INT_MAX &&
      Zlength(output_ptrs) == out_size &&
      Zlength(output_ptrs) == Zlength(output_rows) &&
      level == 0 &&
      start == -1 &&
      0 <= ch && ch <= 127 &&
      0 <= len && len < INT_MAX &&
      valid_string(str_l) &&
      all_ascii(str_l) &&
      valid_paren_input_1(str_l) &&
      paren_safe_input_1(str_l) &&
      string_length(str_l) + 2 < INT_MAX &&
      problem_1_pre_z(str_l) &&
      output_rows == paren_output_rows_1(str_l) &&
      problem_1_spec_z(str_l, output_rows) &&
      data_at(&(out -> data), data) *
      data_at(&(out -> size), Zlength(output_rows)) *
      store_string(paren_string@pre, str_l) *
      PtrArray::seg(data, 0, Zlength(output_rows), output_ptrs) *
      PtrArray::undef_seg(data, Zlength(output_rows), string_length(str_l) + 1) *
      paren_rows_heap_1(output_ptrs, output_rows)
    */
    return out;
}
