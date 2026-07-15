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
*/
{
    if (n < 10) return '0' + n;
    return 'a' + n - 10;
}

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
    Ensure text == text@pre && digest == digest@pre &&
           md5_digest_ok_z(input) && store_string(text, input) *
           UCharArray::full(digest, 16, md5_digest_z(input))
*/;

char* string_to_md5(const char* text)
/*@ With input_s
    Require valid_string(input_s) &&
            string_length(input_s) + 1 < INT_MAX &&
            problem_162_pre_z(input_s) &&
            store_string(text, input_s)
    Ensure ((__return == 0) &&
              (exists preserved_text, store_string(preserved_text, input_s))) ||
           (exists output_s preserved_text,
              problem_162_spec_z(input_s, output_s) &&
              store_string(preserved_text, input_s) *
              CharArray::full(__return, Zlength(output_s) + 1,
                              app(output_s, cons(0, nil))))
*/
{
    unsigned char *md;
    char* out_str;

    if (text[0] != '\0') {
        md = malloc_uchar_array(16);
        md5_compute(text, 0, md);
        out_str = malloc_char_array(33);

        int i;
        /*@ Inv Assert
            exists output,
            0 <= i && i <= 16 &&
            0 < string_length(input_s) &&
            Zlength(md5_digest_z(input_s)) == 16 &&
            (forall (k : Z), (0 <= k && k < 16) =>
                (0 <= Znth(k, md5_digest_z(input_s), 0) &&
                 Znth(k, md5_digest_z(input_s), 0) < 256 &&
                 0 <= Znth(k, md5_digest_z(input_s), 0) / 16 &&
                 Znth(k, md5_digest_z(input_s), 0) / 16 < 16 &&
                 0 <= Znth(k, md5_digest_z(input_s), 0) % 16 &&
                 Znth(k, md5_digest_z(input_s), 0) % 16 < 16)) &&
            Zlength(output) == 2 * i &&
            md5_hex_prefix_z(md5_digest_z(input_s), i, output) &&
            store_string(text, input_s) *
            UCharArray::full(md, 16, md5_digest_z(input_s)) *
            CharArray::seg(out_str, 0, 2 * i, output) *
            CharArray::undef_seg(out_str, 2 * i, 33)
        */
        for (i = 0; i < 16; ++i) {
            int byte = md[i];
            int hi = byte / 16;
            int lo = byte % 16;
            out_str[2 * i] = (char)md5_hex_digit_c(hi);
            out_str[2 * i + 1] = (char)md5_hex_digit_c(lo);
        }
        free_uchar_array(md, 16);
        out_str[32] = '\0';
        return out_str;
    }

    out_str = malloc_char_array(5);
    out_str[0] = 'N';
    out_str[1] = 'o';
    out_str[2] = 'n';
    out_str[3] = 'e';
    out_str[4] = '\0';
    return out_str;
}
