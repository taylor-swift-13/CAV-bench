/*
Given a string s && a natural number n, you have been tasked to implement
a function that returns a vector of all words from string s that contain exactly
n consonants, in order these words appear in the string s.
If the string s is empty then the function should return an empty vector.
Note: you may assume the input string contains only letters && spaces.
*/
#include "ptr_array2_def.h"
#include "string.h"

/*@ Extern Coq (problem_117_pre_z: list Z -> Prop)
               (problem_117_spec_z: list Z -> Z -> list (list Z) -> Prop)
               (select_scan_state_117: list Z -> Z -> Z -> Z -> Z -> list (list Z) -> Prop)
               (select_current_117: list Z -> Z -> Z -> list Z)
               (word_payload_117: list Z -> Z -> Z -> list Z)
               (word_row_117: list Z -> Z -> Z -> list Z)
               (select_words_rows_heap_117: list Z -> list (list Z) -> Assertion)
               (select_output_rows_117: list Z -> Z -> list (list Z))
               (valid_select_words_input_117: list Z -> Prop)
               (is_space_z_117: Z -> bool)
               (is_letter_z_117: Z -> bool)
               (is_vowel_z_117: Z -> bool)
               (is_consonant_z_117: Z -> bool)
               (count_consonants_z_117: list Z -> Z)
               (true: bool) (false: bool)
               (c_string: list Z -> list Z)
               (Zlength: {A} -> list A -> Z)
*/
/*@ Import Coq Require Import p117_select_words */

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

int is_consonant_char(int ch)
/*@ Require
      0 <= ch && ch <= 127
    Ensure
      0 <= __return && __return <= 1 &&
      ((__return == 1 && is_consonant_z_117(ch) == true) ||
       (__return == 0 && is_consonant_z_117(ch) == false))
*/
{
    if (((ch >= 65 && ch <= 90) || (ch >= 97 && ch <= 122)) &&
        !(ch == 65 || ch == 69 || ch == 73 || ch == 79 || ch == 85 ||
          ch == 97 || ch == 101 || ch == 105 || ch == 111 || ch == 117)) {
        return 1;
    }
    return 0;
}

StrArray *select_words(char *s, int need)
/*@ With str_l
    Require
      0 <= need && need < INT_MAX &&
      valid_string(str_l) &&
      all_ascii(str_l) &&
      valid_select_words_input_117(str_l) &&
      string_length(str_l) + 2 < INT_MAX &&
      problem_117_pre_z(str_l) &&
      store_string(s, str_l)
    Ensure exists data output_rows output_ptrs,
      __return != 0 &&
      data != 0 &&
      Zlength(output_rows) <= string_length(str_l) + 1 &&
      Zlength(output_ptrs) == Zlength(output_rows) &&
      problem_117_spec_z(str_l, need, output_rows) &&
      data_at(&(__return -> data), data) *
      data_at(&(__return -> size), Zlength(output_rows)) *
      store_string(s, str_l) *
      PtrArray::seg(data, 0, Zlength(output_rows), output_ptrs) *
      PtrArray::undef_seg(data, Zlength(output_rows), string_length(str_l) + 1) *
      select_words_rows_heap_117(output_ptrs, output_rows)
*/
{
    int start = -1;
    int out_size = 0;
    int numc = 0;
    int n = (int)strlen(s) /*@ where str = str_l */;
    StrArray *out = malloc_str_array_struct();
    out->size = 0;
    out->data = malloc_char_ptr_array(n + 1);
    char **data = out->data;
    int ch = 0;
    int len = 0;
    int addc = 0;
    char *w = 0;

    /*@ Inv Assert
      exists output_rows output_ptrs,
      0 <= i && i <= n &&
      n == string_length(str_l) &&
      s == s@pre &&
      out != 0 &&
      data != 0 &&
      w == w &&
      0 <= out_size && out_size <= i &&
      out_size == Zlength(output_rows) &&
      Zlength(output_ptrs) == out_size &&
      -1 <= start && start < i &&
      0 <= numc && numc <= i &&
      0 <= ch && ch <= 127 &&
      0 <= len && len < INT_MAX &&
      0 <= addc && addc <= 1 &&
      0 <= need && need < INT_MAX &&
      need == need@pre &&
      valid_string(str_l) &&
      all_ascii(str_l) &&
      valid_select_words_input_117(str_l) &&
      string_length(str_l) + 2 < INT_MAX &&
      problem_117_pre_z(str_l) &&
      select_scan_state_117(str_l, i, start, numc, need, output_rows) &&
      data_at(&(out -> data), data) *
      data_at(&(out -> size), out_size) *
      store_string(s@pre, str_l) *
      PtrArray::seg(data, 0, out_size, output_ptrs) *
      PtrArray::undef_seg(data, out_size, n + 1) *
      select_words_rows_heap_117(output_ptrs, output_rows)
    */
    for (int i = 0; i < n; i++) {
        ch = s[i];
        if (ch == 32) {
            if (start >= 0) {
                if (numc == need) {
                    len = i - start;
                    w = malloc_char_array(len + 1);
                    /*@ Inv Assert
                      exists output_rows output_ptrs,
                      0 <= i && i < n &&
                      n == string_length(str_l) &&
                      s == s@pre &&
                      out != 0 &&
                      data != 0 &&
                      w != 0 &&
                      0 <= out_size && out_size <= i &&
                      out_size == Zlength(output_rows) &&
                      Zlength(output_ptrs) == out_size &&
                      0 <= start && start < i &&
                      len == i - start &&
                      ch == Znth(i, c_string(str_l), 0) &&
                      is_space_z_117(ch) == true &&
                      numc == need &&
                      numc == count_consonants_z_117(word_payload_117(str_l, start, i)) &&
                      0 <= ch && ch <= 127 &&
                      0 <= k && k <= len &&
                      0 <= addc && addc <= 1 &&
                      0 <= need && need < INT_MAX &&
                      need == need@pre &&
                      valid_string(str_l) &&
                      all_ascii(str_l) &&
                      valid_select_words_input_117(str_l) &&
                      string_length(str_l) + 2 < INT_MAX &&
                      problem_117_pre_z(str_l) &&
                      select_scan_state_117(str_l, i, start, numc, need, output_rows) &&
                      select_current_117(str_l, i, need) == word_payload_117(str_l, start, i) &&
                      Zlength(word_payload_117(str_l, start, i)) == len &&
                      data_at(&(out -> data), data) *
                      data_at(&(out -> size), out_size) *
                      store_string(s@pre, str_l) *
                      PtrArray::seg(data, 0, out_size, output_ptrs) *
                      PtrArray::undef_seg(data, out_size, n + 1) *
                      select_words_rows_heap_117(output_ptrs, output_rows) *
                      CharArray::full(w, k, word_payload_117(str_l, start, start + k)) *
                      CharArray::undef_seg(w, k, len + 1)
                    */
                    for (int k = 0; k < len; k++) {
                        w[k] = s[start + k];
                    }
                    w[len] = '\0';
                    /*@ Assert
                      exists output_rows output_ptrs,
                      0 <= i && i < n &&
                      n == string_length(str_l) &&
                      s == s@pre &&
                      out != 0 &&
                      data != 0 &&
                      w != 0 &&
                      0 <= out_size && out_size <= i &&
                      out_size == Zlength(output_rows) &&
                      Zlength(output_ptrs) == out_size &&
                      0 <= start && start < i &&
                      len == i - start &&
                      ch == Znth(i, c_string(str_l), 0) &&
                      is_space_z_117(ch) == true &&
                      numc == need &&
                      0 <= ch && ch <= 127 &&
                      0 <= addc && addc <= 1 &&
                      0 <= need && need < INT_MAX &&
                      need == need@pre &&
                      valid_string(str_l) &&
                      all_ascii(str_l) &&
                      valid_select_words_input_117(str_l) &&
                      string_length(str_l) + 2 < INT_MAX &&
                      problem_117_pre_z(str_l) &&
                      select_scan_state_117(str_l, i, start, numc, need, output_rows) &&
                      select_current_117(str_l, i, need) == word_payload_117(str_l, start, i) &&
                      data_at(&(out -> data), data) *
                      data_at(&(out -> size), out_size) *
                      store_string(s@pre, str_l) *
                      PtrArray::seg(data, 0, out_size, output_ptrs) *
                      PtrArray::undef_seg(data, out_size, n + 1) *
                      select_words_rows_heap_117(output_ptrs, output_rows) *
                      CharArray::full(w, len + 1, word_row_117(str_l, start, i))
                    */
                    data[out_size] = w;
                    out_size++;
                    out->size = out_size;
                    start = -1;
                    numc = 0;
                    /*@ Assert
                      exists output_rows output_ptrs,
                      0 <= i && i < n &&
                      n == string_length(str_l) &&
                      s == s@pre &&
                      out != 0 &&
                      data != 0 &&
                      w != 0 &&
                      0 <= out_size && out_size <= i + 1 &&
                      out_size == Zlength(output_rows) &&
                      Zlength(output_ptrs) == out_size &&
                      start == -1 &&
                      numc == 0 &&
                      is_space_z_117(ch) == true &&
                      0 <= ch && ch <= 127 &&
                      0 <= len && len < INT_MAX &&
                      0 <= addc && addc <= 1 &&
                      0 <= need && need < INT_MAX &&
                      need == need@pre &&
                      valid_string(str_l) &&
                      all_ascii(str_l) &&
                      valid_select_words_input_117(str_l) &&
                      string_length(str_l) + 2 < INT_MAX &&
                      problem_117_pre_z(str_l) &&
                      select_scan_state_117(str_l, i + 1, start, numc, need, output_rows) &&
                      data_at(&(out -> data), data) *
                      data_at(&(out -> size), out_size) *
                      store_string(s@pre, str_l) *
                      PtrArray::seg(data, 0, out_size, output_ptrs) *
                      PtrArray::undef_seg(data, out_size, n + 1) *
                      select_words_rows_heap_117(output_ptrs, output_rows)
                    */
                } else {
                    start = -1;
                    numc = 0;
                    /*@ Assert
                      exists output_rows output_ptrs,
                      0 <= i && i < n &&
                      n == string_length(str_l) &&
                      s == s@pre &&
                      out != 0 &&
                      data != 0 &&
                      w == w &&
                      0 <= out_size && out_size <= i &&
                      out_size == Zlength(output_rows) &&
                      Zlength(output_ptrs) == out_size &&
                      start == -1 &&
                      numc == 0 &&
                      is_space_z_117(ch) == true &&
                      0 <= ch && ch <= 127 &&
                      0 <= len && len < INT_MAX &&
                      0 <= addc && addc <= 1 &&
                      0 <= need && need < INT_MAX &&
                      need == need@pre &&
                      valid_string(str_l) &&
                      all_ascii(str_l) &&
                      valid_select_words_input_117(str_l) &&
                      string_length(str_l) + 2 < INT_MAX &&
                      problem_117_pre_z(str_l) &&
                      select_scan_state_117(str_l, i + 1, start, numc, need, output_rows) &&
                      data_at(&(out -> data), data) *
                      data_at(&(out -> size), out_size) *
                      store_string(s@pre, str_l) *
                      PtrArray::seg(data, 0, out_size, output_ptrs) *
                      PtrArray::undef_seg(data, out_size, n + 1) *
                      select_words_rows_heap_117(output_ptrs, output_rows)
                    */
                }
            } else {
                start = -1;
                numc = 0;
                /*@ Assert
                  exists output_rows output_ptrs,
                  0 <= i && i < n &&
                  n == string_length(str_l) &&
                  s == s@pre &&
                  out != 0 &&
                  data != 0 &&
                  w == w &&
                  0 <= out_size && out_size <= i &&
                  out_size == Zlength(output_rows) &&
                  Zlength(output_ptrs) == out_size &&
                  start == -1 &&
                  numc == 0 &&
                  is_space_z_117(ch) == true &&
                  0 <= ch && ch <= 127 &&
                  0 <= len && len < INT_MAX &&
                  0 <= addc && addc <= 1 &&
                  0 <= need && need < INT_MAX &&
                  need == need@pre &&
                  valid_string(str_l) &&
                  all_ascii(str_l) &&
                  valid_select_words_input_117(str_l) &&
                  string_length(str_l) + 2 < INT_MAX &&
                  problem_117_pre_z(str_l) &&
                  select_scan_state_117(str_l, i + 1, start, numc, need, output_rows) &&
                  data_at(&(out -> data), data) *
                  data_at(&(out -> size), out_size) *
                  store_string(s@pre, str_l) *
                  PtrArray::seg(data, 0, out_size, output_ptrs) *
                  PtrArray::undef_seg(data, out_size, n + 1) *
                  select_words_rows_heap_117(output_ptrs, output_rows)
                */
            }
        } else {
            if (start < 0) {
                start = i;
                numc = 0;
            }
            addc = is_consonant_char(ch);
            if (addc != 0) {
                numc++;
            }
            /*@ Assert
              exists output_rows output_ptrs,
              0 <= i && i < n &&
              n == string_length(str_l) &&
              s == s@pre &&
              out != 0 &&
              data != 0 &&
              w == w &&
              0 <= out_size && out_size <= i &&
              out_size == Zlength(output_rows) &&
              Zlength(output_ptrs) == out_size &&
              0 <= start && start <= i &&
              0 <= numc && numc <= i + 1 &&
              is_space_z_117(ch) == false &&
              numc == count_consonants_z_117(select_current_117(str_l, i + 1, need)) &&
              0 <= ch && ch <= 127 &&
              0 <= len && len < INT_MAX &&
              0 <= addc && addc <= 1 &&
              0 <= need && need < INT_MAX &&
              need == need@pre &&
              valid_string(str_l) &&
              all_ascii(str_l) &&
              valid_select_words_input_117(str_l) &&
              string_length(str_l) + 2 < INT_MAX &&
              problem_117_pre_z(str_l) &&
              select_scan_state_117(str_l, i + 1, start, numc, need, output_rows) &&
              data_at(&(out -> data), data) *
              data_at(&(out -> size), out_size) *
              store_string(s@pre, str_l) *
              PtrArray::seg(data, 0, out_size, output_ptrs) *
              PtrArray::undef_seg(data, out_size, n + 1) *
              select_words_rows_heap_117(output_ptrs, output_rows)
            */
        }
    }
    if (start >= 0) {
        if (numc == need) {
            len = n - start;
            w = malloc_char_array(len + 1);
            /*@ Inv Assert
              exists output_rows output_ptrs,
              n == string_length(str_l) &&
              s == s@pre &&
              out != 0 &&
              data != 0 &&
              w != 0 &&
              0 <= ch && ch <= 127 &&
              0 <= addc && addc <= 1 &&
              0 <= out_size && out_size <= n &&
              out_size == Zlength(output_rows) &&
              Zlength(output_ptrs) == out_size &&
              0 <= start && start < n &&
              len == n - start &&
              numc == need &&
              numc == count_consonants_z_117(word_payload_117(str_l, start, n)) &&
              0 <= k && k <= len &&
              0 <= need && need < INT_MAX &&
              need == need@pre &&
              valid_string(str_l) &&
              all_ascii(str_l) &&
              valid_select_words_input_117(str_l) &&
              string_length(str_l) + 2 < INT_MAX &&
              problem_117_pre_z(str_l) &&
              select_scan_state_117(str_l, n, start, numc, need, output_rows) &&
              select_current_117(str_l, n, need) == word_payload_117(str_l, start, n) &&
              Zlength(word_payload_117(str_l, start, n)) == len &&
              data_at(&(out -> data), data) *
              data_at(&(out -> size), out_size) *
              store_string(s@pre, str_l) *
              PtrArray::seg(data, 0, out_size, output_ptrs) *
              PtrArray::undef_seg(data, out_size, n + 1) *
              select_words_rows_heap_117(output_ptrs, output_rows) *
              CharArray::full(w, k, word_payload_117(str_l, start, start + k)) *
              CharArray::undef_seg(w, k, len + 1)
            */
            for (int k = 0; k < len; k++) {
                w[k] = s[start + k];
            }
            w[len] = '\0';
            data[out_size] = w;
            out_size++;
            out->size = out_size;
            start = -1;
            numc = 0;
        } else {
            start = -1;
            numc = 0;
        }
    }
    /*@ Assert
      exists output_rows output_ptrs,
      n == string_length(str_l) &&
      s == s@pre &&
      out != 0 &&
      data != 0 &&
      w == w &&
      0 <= ch && ch <= 127 &&
      0 <= len && len < INT_MAX &&
      0 <= addc && addc <= 1 &&
      0 <= need && need < INT_MAX &&
      need == need@pre &&
      out_size == Zlength(output_rows) &&
      Zlength(output_ptrs) == out_size &&
      start == -1 &&
      numc == 0 &&
      valid_string(str_l) &&
      all_ascii(str_l) &&
      valid_select_words_input_117(str_l) &&
      string_length(str_l) + 2 < INT_MAX &&
      problem_117_pre_z(str_l) &&
      output_rows == select_output_rows_117(str_l, need) &&
      problem_117_spec_z(str_l, need, output_rows) &&
      data_at(&(out -> data), data) *
      data_at(&(out -> size), out_size) *
      store_string(s@pre, str_l) *
      PtrArray::seg(data, 0, out_size, output_ptrs) *
      PtrArray::undef_seg(data, out_size, n + 1) *
      select_words_rows_heap_117(output_ptrs, output_rows)
    */
    return out;
}
