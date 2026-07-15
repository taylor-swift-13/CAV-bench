/*
Given a string text, return its lowercase MD5 hexadecimal digest.
For the empty string, return the literal "None".
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"
#include "uchar_array_def.h"
#include "string.h"

/*@ Extern Coq
      (problem_162_pre_z : list Z -> Prop)
      (problem_162_spec_z : list Z -> list Z -> Prop)
      (md5_digest_z : list Z -> list Z)
      (md5_digest_ok_z : list Z -> Prop)
      (md5_hex_prefix_z : list Z -> Z -> list Z -> Prop)
      (md5_hex_digit_z : Z -> Z)
*/
/*@ Import Coq Require Import p162_string_to_md5 */

char *malloc_char_array(int size)
/*@ Require 0 <= size && size < INT_MAX && emp
    Ensure __return != 0 && CharArray::undef_full(__return, size)
*/;

int md5_hex_digit_c(int n)
/*@ Require 0 <= n && n < 16 && emp
    Ensure __return == md5_hex_digit_z(n@pre) && emp
*/;

unsigned char *malloc_uchar_array(int size)
/*@ Require 0 <= size && size < INT_MAX && emp
    Ensure __return != 0 && UCharArray::undef_full(__return, size)
*/;

void free_uchar_array(unsigned char *array, int size)
/*@ With contents
    Require 0 <= size && size < INT_MAX &&
            Zlength(contents) == size && UCharArray::full(array, size, contents)
    Ensure emp
*/;

void md5_compute(const char *text, int n, unsigned char *digest)
/*@ With input
    Require store_string(text, input) *
            UCharArray::undef_full(digest, 16)
    Ensure md5_digest_ok_z(input) &&
           store_string(text, input) *
           UCharArray::full(digest, 16, md5_digest_z(input))
*/;

char* string_to_md5(const char* text)
/*@ With input_s
    Require valid_string(input_s) &&
            string_length(input_s) + 1 < INT_MAX &&
            problem_162_pre_z(input_s) &&
            store_string(text, input_s)
    Ensure ((__return == 0) && store_string(text, input_s)) ||
           (exists output_s,
              problem_162_spec_z(input_s, output_s) &&
              store_string(text, input_s) *
              CharArray::full(__return, Zlength(output_s) + 1,
                              app(output_s, cons(0, nil))))
*/;
