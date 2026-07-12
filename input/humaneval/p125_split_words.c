/*
Given a string of words, return a vector of words split on whitespace, if no whitespaces exists in the text you
should split on commas ',' if no commas exists you should return a vector with one element, the number of lower-case letters with odd order in the
alphabet, ord("a") = 0, ord("b") = 1, ... ord("z") = 25
Examples
split_words("Hello world!") -> {"Hello", "world!"}
split_words("Hello,world!") -> {"Hello", "world!"}
split_words("abcdef") == {"3"}
*/
#include "ptr_array2_def.h"
#include "string.h"

/*@ Extern Coq (problem_125_pre_z: list Z -> Prop)
               (problem_125_spec_z: list Z -> list (list Z) -> Prop)
               (split_scan_state_125: list Z -> Z -> Z -> Z -> list (list Z) -> Prop)
               (split_scan_current_125: list Z -> Z -> Z -> list Z)
               (word_payload_125: list Z -> Z -> Z -> list Z)
               (word_row_125: list Z -> Z -> Z -> list Z)
               (split_words_rows_heap_125: list Z -> list (list Z) -> Assertion)
               (split_output_rows_125: list Z -> Z -> list (list Z))
               (valid_split_words_input_125: list Z -> Prop)
               (contains_z_125: list Z -> Z -> Prop)
               (contains_zb_125: list Z -> Z -> bool)
               (strchr_result: list Z -> Z -> Z -> Z -> Prop)
               (odd_lower_prefix_125: list Z -> Z -> Z)
               (odd_lower_count_125: list Z -> Z)
               (decimal_write_state_125: Z -> Z -> Z -> Z -> list Z -> Prop)
               (true: bool) (false: bool)
               (c_string: list Z -> list Z)
               (Zlength: {A} -> list A -> Z)
*/
/*@ Import Coq Require Import p125_split_words */

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
/*@ Require emp
    Ensure __return != 0 && CharArray::undef_full(__return, size)
*/;

int decimal_len(int value)
/*@ Require
      0 <= value && value < INT_MAX
    Ensure
      1 <= __return && __return < INT_MAX
*/
{
    if (value >= 1000000000) return 10;
    if (value >= 100000000) return 9;
    if (value >= 10000000) return 8;
    if (value >= 1000000) return 7;
    if (value >= 100000) return 6;
    if (value >= 10000) return 5;
    if (value >= 1000) return 4;
    if (value >= 100) return 3;
    if (value >= 10) return 2;
    return 1;
}

void write_decimal(char *buf, int value, int digits)
/*@ Require
      0 <= value && value < INT_MAX &&
      1 <= digits && digits < INT_MAX &&
      CharArray::undef_full(buf, digits + 1)
    Ensure exists out_l,
      Zlength(out_l) == digits &&
      CharArray::full(buf, digits + 1, c_string(out_l))
*/
{
    int tmp = value;
    int pos = digits - 1;

    while (pos >= 0) {
        buf[pos] = 48 + (tmp % 10);
        tmp = tmp / 10;
        pos--;
    }
    buf[digits] = '\0';
}

StrArray *split_words(char *txt)
/*@ With str_l
    Require
      valid_string(str_l) &&
      all_ascii(str_l) &&
      valid_split_words_input_125(str_l) &&
      string_length(str_l) + 2 < INT_MAX &&
      problem_125_pre_z(str_l) &&
      store_string(txt, str_l)
    Ensure exists data output_rows output_ptrs,
      __return != 0 &&
      data != 0 &&
      Zlength(output_ptrs) == Zlength(output_rows) &&
      Zlength(output_rows) <= string_length(str_l) + 1 &&
      problem_125_spec_z(str_l, output_rows) &&
      data_at(&(__return -> data), data) *
      data_at(&(__return -> size), Zlength(output_rows)) *
      store_string(txt, str_l) *
      PtrArray::seg(data, 0, Zlength(output_rows), output_ptrs) *
      PtrArray::undef_seg(data, Zlength(output_rows), string_length(str_l) + 1) *
      split_words_rows_heap_125(output_ptrs, output_rows)
*/
{
    StrArray *out = 0;
    char **data = 0;
    int n = (int)strlen(txt) ;
    char *space_hit = strchr(txt, 32) ;
    char *comma_hit = strchr(txt, 44) ;
    out = malloc_str_array_struct();
    out->size = 0;
    out->data = malloc_char_ptr_array(n + 1);
    data = out->data;
    if (space_hit != 0 || comma_hit != 0) {
        int sep = (space_hit != 0) ? 32 : 44;
        int start = -1;
        int out_size = 0;
        int ch = 0;
        int len = 0;
        char *w = 0;

        for (int i = 0; i < n; i++) {
            ch = txt[i];
            if (ch == sep) {
                if (start >= 0) {
                    len = i - start;
                    w = malloc_char_array(len + 1);

                    for (int k = 0; k < len; k++) {
                        w[k] = txt[start + k];
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
                w[k] = txt[start + k];
            }
            w[len] = '\0';
            data[out_size] = w;
            out_size++;
            out->size = out_size;
            start = -1;
        }

        return out;
    } else {
        int out_size = 0;
        int len = 0;
        char *w = 0;

        for (int i = 0; i < n; i++) {
            if (txt[i] >= 97 && txt[i] <= 122 && txt[i] % 2 == 0) {
                out_size += 1;
            }
        }
        len = decimal_len(out_size);
        w = malloc_char_array(len + 1);
        write_decimal(w, out_size, len);
        data[0] = w;
        out->size = 1;

        return out;
    }
}
