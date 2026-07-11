/*
Given a vector of strings, where each string consists of only digits, return a vector.
Each element i of the output should be 'the number of odd elements in the
string i of the input." where all the i's should be replaced by the number
of odd digits in the i'th string of the input.

>>> odd_count({"1234567"})
{'the number of odd elements 4n the str4ng 4 of the 4nput."}
>>> odd_count({"3","11111111"})
{'the number of odd elements 1n the str1ng 1 of the 1nput.",
 'the number of odd elements 8n the str8ng 8 of the 8nput."}
*/
#include "ptr_array2_def.h"
#include "string.h"

/*@ Extern Coq (problem_113_pre_z: list (list Z) -> Prop)
               (problem_113_spec_z: list (list Z) -> list (list Z) -> Prop)
               (rows_well_formed_113: list (list Z) -> Z -> Prop)
               (row_payload_z_113: list Z -> list Z)
               (odd_count_state_113: list (list Z) -> Z -> list (list Z) -> Prop)
               (odd_digit_count_prefix_113: list Z -> Z -> Z)
               (odd_digit_count_row_113: list Z -> Z)
               (decimal_digits_113: Z -> list Z)
               (odd_count_row_113: list Z -> list Z)
               (odd_count_rows_113: list (list Z) -> list (list Z))
               (template_literal_113: String)
               (template_fill_state_113: Z -> list Z -> Z -> list Z -> Prop)
               (template_len_113: Z)
               (StringToList: String -> Z -> list Z)
               (StringLength: String -> Z)
               (nil_z_113: list Z)
               (row_at_113: Z -> list (list Z) -> list Z)
               (odd_count_rows_heap_113: list Z -> list (list Z) -> Assertion)
               (LitMap: String -> Z)
               (true: bool) (false: bool)
               (c_string: list Z -> list Z)
               (Znth: {A} -> Z -> list A -> A -> A)
               (Zlength: {A} -> list A -> Z)
*/
/*@ Import Coq Require Import p113_odd_count */

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

int write_decimal(char *buf, int value)
/*@ Require
      0 <= value && value < INT_MAX &&
      Zlength(decimal_digits_113(value)) + 1 < 32 &&
      CharArray::undef_full(buf, 32)
    Ensure
      __return == Zlength(decimal_digits_113(value)) &&
      CharArray::full(buf, __return, decimal_digits_113(value)) *
      CharArray::full(buf + __return * sizeof(char), 1, cons(0, nil)) *
      CharArray::undef_seg(buf, __return + 1, 32)
*/;

StrArray *odd_count(char** lst, int lst_size)
/*@ With rows
    Require
      0 <= lst_size && lst_size <= 100 &&
      rows_well_formed_113(rows, lst_size) &&
      (forall (p: Z), (0 <= p && p < lst_size) =>
        (Zlength(decimal_digits_113(odd_digit_count_row_113(row_at_113(p, rows)))) + 1 < 32)) &&
      (forall (p: Z), (0 <= p && p < lst_size) =>
        (Zlength(odd_count_row_113(row_at_113(p, rows))) < INT_MAX)) &&
      problem_113_pre_z(rows) &&
      CharPtrArray2::full(lst, lst_size, rows) *
      GlobalStrings(LitMap)
    Ensure exists data output_rows output_ptrs scratch,
      __return != 0 &&
      data != 0 &&
      Zlength(output_rows) == lst_size &&
      Zlength(output_ptrs) == lst_size &&
      output_rows == odd_count_rows_113(rows) &&
      problem_113_spec_z(rows, output_rows) &&
      data_at(&(__return -> data), data) *
      data_at(&(__return -> size), lst_size) *
      CharPtrArray2::full(lst, lst_size, rows) *
      PtrArray::seg(data, 0, lst_size, output_ptrs) *
      odd_count_rows_heap_113(output_ptrs, output_rows) *
      CharArray::undef_full(scratch, 32) *
      GlobalStrings(LitMap)
*/
{
    StrArray *out = malloc_str_array_struct();
    out->size = lst_size;
    out->data = malloc_char_ptr_array(lst_size);
    char **data = out->data;
    char *cur = 0;
    int n = 0;
    int sum = 0;
    int ch = 0;
    int numlen = 0;
    int outlen = 0;
    int k = 0;
    int t = 0;
    const char *tpl = "the number of odd elements in the string i of the input.";
    char *numbuf = malloc_char_array(32);

    for (int i=0;i<lst_size;i++)
        {

            cur = lst[i];
            n = (int)strlen(cur) ;
            sum = 0;

            for (int j=0;j<n;j++)
                {
                    ch = cur[j];
                    if (ch >= 48 && ch <= 57 && ch % 2 == 1)
                        sum += 1;
                }

            numlen = write_decimal(numbuf, sum);
            outlen = 56 + 4 * (numlen - 1);
            char *row_out = malloc_char_array(outlen + 1);
            k = 0;
            t = 0;

            while (t < 56) {
                ch = tpl[t];
                if (ch == 105) {

                    memcpy(row_out + k, numbuf, numlen) ;
                    k += numlen;
                } else {
                    row_out[k] = ch;
                    k += 1;
                }
                t += 1;
            }
            row_out[k] = '\0';
            data[i] = row_out;
        }
    return out;
}
