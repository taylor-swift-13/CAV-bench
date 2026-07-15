/*
Input is a space-delimited string of numberals from "zero" to "nine".
Valid choices are "zero", "one", "two", "three", "four", "five", "six",
"seven", "eight" and "nine".
Return the string with numbers sorted from smallest to largest.
>>> sort_numbers("three one five")
"one three five"
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"
#include "ptr_array2_def.h"
#include "string.h"

/*@ Extern Coq (problem_19_pre_z: list Z -> Prop)
               (problem_19_spec_z: list Z -> list Z -> Prop)
               (ascii_range_z: list Z -> Prop)
               (number_word_z: Z -> list Z)
               (number_word_len_z: Z -> Z)
               (token_prefix_z: Z -> Z -> list Z -> list Z)
               (token_unsat_end_z: Z -> Z -> list Z -> Prop)
               (token_sat_start_z: Z -> Z -> list Z -> Prop)
               (token_empty_start_z: Z -> Z -> list Z -> Prop)
               (token_miss_prefix_z: Z -> list Z -> Prop)
               (scan_char_z: Z -> list Z -> Z)
               (scan_counts_z: Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
               (scan_counts_exact_z: Z -> Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
               (output_prefix_z: Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> list Z)
               (output_capacity_prefix_z: Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z)
               (output_prefix_by_input_z: Z -> Z -> list Z -> list Z)
               (output_capacity_prefix_by_input_z: Z -> list Z -> Z)
               (output_used_capacity_prefix_by_input_z: Z -> list Z -> Z)
               (sorted_numbers_output_by_counts_z: Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> list Z)
               (number_words_chars_full_z: Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Assertion)
               (number_words_full: Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Assertion)
               (number_words_missing: Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Assertion) */
/*@ Import Coq Require Import p019_sort_numbers */
/*@ include strategies "number_words_19.strategies" */

char *malloc_char_array(int n)
/*@ Require n > 0 && emp
    Ensure __return != 0 && CharArray::undef_full(__return, n)
*/
;

void free_char_array(char *p, int used, int cap)
/*@ With l
    Require
        p != 0 &&
        0 <= used && used <= cap &&
        Zlength(l) == used &&
        CharArray::full(p, used, l) *
        CharArray::undef_seg(p, used, cap)
    Ensure emp
*/
;

char* sort_numbers(char *numbers)
/*@ With l len
    Require
        0 <= len && len + 1 < INT_MAX &&
        1 + 6 * (len + 1) <= INT_MAX &&
        Zlength(l) == len &&
        valid_string(l) &&
        string_length(l) == len &&
        problem_19_pre_z(l) &&
        ascii_range_z(l) &&
        store_string(numbers, l)
    Ensure exists out_l,
        problem_19_spec_z(l, out_l) &&
        CharArray::full(__return, Zlength(out_l) + 1, app(out_l, cons(0, nil))) *
        store_string(numbers, l)
*/
{
    char w0[5];
    char w1[4];
    char w2[4];
    char w3[6];
    char w4[5];
    char w5[5];
    char w6[4];
    char w7[6];
    char w8[6];
    char w9[5];
    char *words[10];
    char *space_word = 0;
    int count[10];
    int n = strlen(numbers) /*@ where str = l */;
    char *token = 0;
    int tlen = 0;
    int out_len = 1;
    char *out = 0;
    int i = 0;
    int d = 0;
    int j = 0;
    int first = 0;
    int cmp = 0;
    char ch = 0;
    char *word = 0;

    w0[0] = 122; w0[1] = 101; w0[2] = 114; w0[3] = 111; w0[4] = 0;
    w1[0] = 111; w1[1] = 110; w1[2] = 101; w1[3] = 0;
    w2[0] = 116; w2[1] = 119; w2[2] = 111; w2[3] = 0;
    w3[0] = 116; w3[1] = 104; w3[2] = 114; w3[3] = 101; w3[4] = 101; w3[5] = 0;
    w4[0] = 102; w4[1] = 111; w4[2] = 117; w4[3] = 114; w4[4] = 0;
    w5[0] = 102; w5[1] = 105; w5[2] = 118; w5[3] = 101; w5[4] = 0;
	    w6[0] = 115; w6[1] = 105; w6[2] = 120; w6[3] = 0;
	    w7[0] = 115; w7[1] = 101; w7[2] = 118; w7[3] = 101; w7[4] = 110; w7[5] = 0;
	    w8[0] = 101; w8[1] = 105; w8[2] = 103; w8[3] = 104; w8[4] = 116; w8[5] = 0;
	    w9[0] = 110; w9[1] = 105; w9[2] = 110; w9[3] = 101; w9[4] = 0;
	    /*@ Assert
	        numbers == numbers@pre &&
        w0 == w0 && w1 == w1 && w2 == w2 && w3 == w3 && w4 == w4 &&
        w5 == w5 && w6 == w6 && w7 == w7 && w8 == w8 && w9 == w9 &&
        count == count &&
        token == token &&
	        words == words &&
	        word == word &&
	        space_word == space_word &&
	        out == out &&
        n == len &&
        tlen == 0 &&
        out_len == 1 &&
        ch == ch &&
        d == d &&
        j == j &&
        first == first &&
        cmp == cmp &&
        i == i &&
        0 <= len && len + 1 < INT_MAX &&
	        1 + 6 * (len + 1) <= INT_MAX &&
	        Zlength(l) == len &&
	        valid_string(l) &&
	        string_length(l) == len &&
	        problem_19_pre_z(l) &&
	        ascii_range_z(l) &&
	        CharArray::full(numbers, len + 1, app(l, cons(0, nil))) *
	        PtrArray::undef_full(words, 10) *
	        IntArray::undef_full(count, 10) *
	        number_words_chars_full_z(w0, w1, w2, w3, w4, w5, w6, w7, w8, w9)
	    */
	    words[0] = w0; words[1] = w1; words[2] = w2; words[3] = w3; words[4] = w4;
	    words[5] = w5; words[6] = w6; words[7] = w7; words[8] = w8; words[9] = w9;
	    /*@ Assert
	        numbers == numbers@pre &&
        w0 == w0 && w1 == w1 && w2 == w2 && w3 == w3 && w4 == w4 &&
        w5 == w5 && w6 == w6 && w7 == w7 && w8 == w8 && w9 == w9 &&
        count == count &&
        token == token &&
	        words == words &&
	        word == word &&
	        space_word == space_word &&
	        out == out &&
        n == len &&
        tlen == 0 &&
        out_len == 1 &&
        ch == ch &&
        d == d &&
        j == j &&
        first == first &&
        cmp == cmp &&
        i == i &&
        0 <= len && len + 1 < INT_MAX &&
	        1 + 6 * (len + 1) <= INT_MAX &&
	        Zlength(l) == len &&
	        valid_string(l) &&
	        string_length(l) == len &&
	        problem_19_pre_z(l) &&
	        ascii_range_z(l) &&
	        CharArray::full(numbers, len + 1, app(l, cons(0, nil))) *
	        IntArray::undef_full(count, 10) *
	        number_words_full(words, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9)
	    */
	    space_word = malloc_char_array(3);
	    space_word[0] = 32; space_word[1] = 0;
	    /*@ Assert
	        numbers == numbers@pre &&
        w0 == w0 && w1 == w1 && w2 == w2 && w3 == w3 && w4 == w4 &&
        w5 == w5 && w6 == w6 && w7 == w7 && w8 == w8 && w9 == w9 &&
        count == count &&
        token == token &&
        words == words &&
        word == word &&
	        space_word == space_word &&
	        space_word != 0 &&
	        out == out &&
        n == len &&
        tlen == 0 &&
        out_len == 1 &&
        ch == ch &&
        d == d &&
        j == j &&
        first == first &&
        cmp == cmp &&
        i == i &&
        0 <= len && len + 1 < INT_MAX &&
	        1 + 6 * (len + 1) <= INT_MAX &&
	        Zlength(l) == len &&
	        valid_string(l) &&
	        string_length(l) == len &&
	        problem_19_pre_z(l) &&
	        ascii_range_z(l) &&
	        CharArray::full(numbers, len + 1, app(l, cons(0, nil))) *
	        IntArray::undef_full(count, 10) *
	        number_words_full(words, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9) *
	        CharArray::full(space_word, number_word_len_z(10) + 1, app(number_word_z(10), cons(0, nil))) *
	        CharArray::undef_seg(space_word, number_word_len_z(10) + 1, 3)
	    */
	    ch = 0;
    d = 0;
    j = 0;
    first = 0;
    cmp = 0;
    word = 0;
    out = 0;
    token = malloc_char_array(32);

    /*@ Inv Assert
        numbers == numbers@pre &&
        words == words &&
        n == len &&
        0 <= len && len + 1 < INT_MAX &&
        1 + 6 * (len + 1) <= INT_MAX &&
        Zlength(l) == len &&
        valid_string(l) &&
        string_length(l) == len &&
        problem_19_pre_z(l) &&
        ascii_range_z(l) &&
        0 <= i && i <= 10 &&
        token != 0 &&
        space_word != 0 &&
        tlen == 0 &&
        out_len == 1 &&
        out == 0 &&
        d == 0 &&
        j == 0 &&
        first == 0 &&
        cmp == 0 &&
        ch == 0 &&
        word == 0 &&
        number_word_len_z(10) == 1 &&
        Zlength(app(number_word_z(10), cons(0, nil))) == 2 &&
        CharArray::full(numbers, len + 1, app(l, cons(0, nil))) *
        number_words_full(words, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9) *
        CharArray::full(space_word, number_word_len_z(10) + 1, app(number_word_z(10), cons(0, nil))) *
        CharArray::undef_seg(space_word, number_word_len_z(10) + 1, 3) *
        CharArray::undef_full(token, 32) *
        IntArray::seg(count, 0, i, zeros(i)) *
        IntArray::undef_seg(count, i, 10)
    */
    for (i = 0; i < 10; i++) {
        count[i] = 0;
    }

    /*@ Inv Assert
        exists (cnts: list Z),
        numbers == numbers@pre &&
        words == words &&
        n == len &&
        0 <= len && len + 1 < INT_MAX &&
        1 + 6 * (len + 1) <= INT_MAX &&
        Zlength(l) == len &&
        valid_string(l) &&
        string_length(l) == len &&
        problem_19_pre_z(l) &&
        ascii_range_z(l) &&
        0 <= i && i <= n + 1 &&
        token != 0 &&
        space_word != 0 &&
        number_word_len_z(10) == 1 &&
        Zlength(app(number_word_z(10), cons(0, nil))) == 2 &&
        0 <= tlen && tlen < 32 &&
        tlen <= i &&
        0 <= ch && ch <= 127 &&
        0 <= d && d <= 10 &&
        out_len == 1 &&
        out == 0 &&
        0 <= j &&
        j == 0 &&
        0 <= first &&
        first == 0 &&
        cmp == cmp &&
        word == word &&
        Zlength(cnts) == 10 &&
        Zlength(token_prefix_z(i, tlen, l)) == tlen &&
        valid_string(token_prefix_z(i, tlen, l)) &&
        string_length(token_prefix_z(i, tlen, l)) == tlen &&
        string_length(token_prefix_z(i, tlen, l)) < INT_MAX &&
        token_empty_start_z(i, tlen, l) &&
        (tlen < 31 => token_unsat_end_z(i, tlen, l)) &&
        token_sat_start_z(i, tlen, l) &&
        scan_counts_z(i, l,
                      Znth(0, cnts, 0), Znth(1, cnts, 0),
                      Znth(2, cnts, 0), Znth(3, cnts, 0),
                      Znth(4, cnts, 0), Znth(5, cnts, 0),
                      Znth(6, cnts, 0), Znth(7, cnts, 0),
                      Znth(8, cnts, 0), Znth(9, cnts, 0)) &&
        scan_counts_exact_z(i, tlen, l,
                      Znth(0, cnts, 0), Znth(1, cnts, 0),
                      Znth(2, cnts, 0), Znth(3, cnts, 0),
                      Znth(4, cnts, 0), Znth(5, cnts, 0),
                      Znth(6, cnts, 0), Znth(7, cnts, 0),
                      Znth(8, cnts, 0), Znth(9, cnts, 0)) &&
        CharArray::full(numbers, len + 1, app(l, cons(0, nil))) *
        number_words_full(words, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9) *
        CharArray::full(space_word, number_word_len_z(10) + 1, app(number_word_z(10), cons(0, nil))) *
        CharArray::undef_seg(space_word, number_word_len_z(10) + 1, 3) *
        CharArray::full(token, tlen, token_prefix_z(i, tlen, l)) *
        CharArray::undef_seg(token, tlen, 32) *
        IntArray::full(count, 10, cnts)
    */
    for (i = 0; i <= n; i++) {
        if (i < n) {
            ch = numbers[i];
        } else {
            ch = 32;
        }
        if (ch == 32) {
            if (tlen > 0) {
                token[tlen] = 0;
                /*@ Inv Assert
                    exists (cnts: list Z),
                    numbers == numbers@pre &&
                    words == words &&
                    n == len &&
                    0 <= len && len + 1 < INT_MAX &&
                    1 + 6 * (len + 1) <= INT_MAX &&
                    Zlength(l) == len &&
                    valid_string(l) &&
                    string_length(l) == len &&
                    problem_19_pre_z(l) &&
                    ascii_range_z(l) &&
                    0 <= i && i <= n &&
                    token != 0 &&
                    space_word != 0 &&
                    number_word_len_z(10) == 1 &&
                    Zlength(app(number_word_z(10), cons(0, nil))) == 2 &&
                    0 <= tlen && tlen < 32 &&
                    tlen <= i &&
                    0 <= d && d <= 10 &&
                    0 <= Znth(d, cnts, 0) && Znth(d, cnts, 0) <= len + 1 &&
                    out_len == 1 &&
                    out == 0 &&
                    0 <= j &&
                    j == 0 &&
                    0 <= first &&
                    first == 0 &&
                    ch == 32 &&
                    scan_char_z(i, l) == 32 &&
                    0 <= ch && ch <= 127 &&
                    cmp == cmp &&
                    Zlength(cnts) == 10 &&
                    Zlength(token_prefix_z(i, tlen, l)) == tlen &&
                    valid_string(token_prefix_z(i, tlen, l)) &&
                    string_length(token_prefix_z(i, tlen, l)) == tlen &&
                    string_length(token_prefix_z(i, tlen, l)) < INT_MAX &&
                    ((0 <= d && d < 10) =>
                        valid_string(number_word_z(d)) &&
                        string_length(number_word_z(d)) == number_word_len_z(d) &&
                        string_length(number_word_z(d)) < INT_MAX) &&
                    token_empty_start_z(i, tlen, l) &&
                    (tlen < 31 => token_unsat_end_z(i, tlen, l)) &&
                    token_sat_start_z(i, tlen, l) &&
                    token_miss_prefix_z(d, token_prefix_z(i, tlen, l)) &&
                    scan_counts_z(i, l,
                                  Znth(0, cnts, 0), Znth(1, cnts, 0),
                                  Znth(2, cnts, 0), Znth(3, cnts, 0),
                                  Znth(4, cnts, 0), Znth(5, cnts, 0),
                                  Znth(6, cnts, 0), Znth(7, cnts, 0),
                                  Znth(8, cnts, 0), Znth(9, cnts, 0)) &&
                    scan_counts_exact_z(i, tlen, l,
                                  Znth(0, cnts, 0), Znth(1, cnts, 0),
                                  Znth(2, cnts, 0), Znth(3, cnts, 0),
                                  Znth(4, cnts, 0), Znth(5, cnts, 0),
                                  Znth(6, cnts, 0), Znth(7, cnts, 0),
                                  Znth(8, cnts, 0), Znth(9, cnts, 0)) &&
                    word == word &&
                    CharArray::full(numbers, len + 1, app(l, cons(0, nil))) *
                    number_words_full(words, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9) *
                    CharArray::full(space_word, number_word_len_z(10) + 1, app(number_word_z(10), cons(0, nil))) *
                    CharArray::undef_seg(space_word, number_word_len_z(10) + 1, 3) *
                    CharArray::full(token, tlen + 1, app(token_prefix_z(i, tlen, l), cons(0, nil))) *
                    CharArray::undef_seg(token, tlen + 1, 32) *
                    IntArray::full(count, 10, cnts)
                */
                for (d = 0; d < 10; d++) {
                    /*@ Assert
                        exists (cnts: list Z) (word_ptr: Z),
                        numbers == numbers@pre &&
                        words == words &&
                        n == len &&
                        0 <= len && len + 1 < INT_MAX &&
                        1 + 6 * (len + 1) <= INT_MAX &&
                        Zlength(l) == len &&
                        valid_string(l) &&
                        string_length(l) == len &&
                        problem_19_pre_z(l) &&
                        ascii_range_z(l) &&
                        0 <= i && i <= n &&
                        token != 0 &&
                        space_word != 0 &&
                        number_word_len_z(10) == 1 &&
                        Zlength(app(number_word_z(10), cons(0, nil))) == 2 &&
                        0 <= tlen && tlen < 32 && tlen <= i &&
                        0 <= d && d < 10 &&
                        0 <= Znth(d, cnts, 0) &&
                        Znth(d, cnts, 0) <= len + 1 &&
                        out_len == 1 &&
                        out == 0 &&
                        0 <= j &&
                        j == 0 &&
                        0 <= first &&
                        first == 0 &&
                        ch == 32 &&
                        scan_char_z(i, l) == 32 &&
                        0 <= ch && ch <= 127 &&
                        cmp == cmp &&
                        Zlength(cnts) == 10 &&
                        Zlength(token_prefix_z(i, tlen, l)) == tlen &&
                        valid_string(token_prefix_z(i, tlen, l)) &&
                        string_length(token_prefix_z(i, tlen, l)) == tlen &&
                        string_length(token_prefix_z(i, tlen, l)) < INT_MAX &&
                        valid_string(number_word_z(d)) &&
                        string_length(number_word_z(d)) == number_word_len_z(d) &&
                        string_length(number_word_z(d)) < INT_MAX &&
                        token_empty_start_z(i, tlen, l) &&
                        (tlen < 31 => token_unsat_end_z(i, tlen, l)) &&
                        token_sat_start_z(i, tlen, l) &&
                        token_miss_prefix_z(d, token_prefix_z(i, tlen, l)) &&
                        scan_counts_z(i, l,
                                      Znth(0, cnts, 0), Znth(1, cnts, 0),
                                      Znth(2, cnts, 0), Znth(3, cnts, 0),
                                      Znth(4, cnts, 0), Znth(5, cnts, 0),
                                      Znth(6, cnts, 0), Znth(7, cnts, 0),
                                      Znth(8, cnts, 0), Znth(9, cnts, 0)) &&
                        scan_counts_exact_z(i, tlen, l,
                                      Znth(0, cnts, 0), Znth(1, cnts, 0),
                                      Znth(2, cnts, 0), Znth(3, cnts, 0),
                                      Znth(4, cnts, 0), Znth(5, cnts, 0),
                                      Znth(6, cnts, 0), Znth(7, cnts, 0),
                                      Znth(8, cnts, 0), Znth(9, cnts, 0)) &&
                        word == word &&
                        word_ptr == Znth(d, cons(w0, cons(w1, cons(w2, cons(w3, cons(w4, cons(w5, cons(w6, cons(w7, cons(w8, cons(w9, nil)))))))))), 0) &&
                        CharArray::full(numbers, len + 1, app(l, cons(0, nil))) *
                        number_words_full(words, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9) *
                        CharArray::full(space_word, number_word_len_z(10) + 1, app(number_word_z(10), cons(0, nil))) *
                        CharArray::undef_seg(space_word, number_word_len_z(10) + 1, 3) *
                        store_string(token, token_prefix_z(i, tlen, l)) *
                        CharArray::undef_seg(token, tlen + 1, 32) *
                        IntArray::full(count, 10, cnts)
                    */
                    if (d == 0) word = w0;
                    else if (d == 1) word = w1;
                    else if (d == 2) word = w2;
                    else if (d == 3) word = w3;
                    else if (d == 4) word = w4;
                    else if (d == 5) word = w5;
                    else if (d == 6) word = w6;
                    else if (d == 7) word = w7;
                    else if (d == 8) word = w8;
                    else word = w9;
                    /*@ Assert
                        exists (cnts: list Z),
                        numbers == numbers@pre &&
                        words == words &&
                        n == len &&
                        0 <= len && len + 1 < INT_MAX &&
                        1 + 6 * (len + 1) <= INT_MAX &&
                        Zlength(l) == len &&
                        valid_string(l) &&
                        string_length(l) == len &&
                        problem_19_pre_z(l) &&
                        ascii_range_z(l) &&
                        0 <= i && i <= n &&
                        token != 0 &&
                        space_word != 0 &&
                        number_word_len_z(10) == 1 &&
                        Zlength(app(number_word_z(10), cons(0, nil))) == 2 &&
                        0 <= tlen && tlen < 32 &&
                        tlen <= i &&
                        0 <= d && d < 10 &&
                        0 <= Znth(d, cnts, 0) && Znth(d, cnts, 0) <= len + 1 &&
                        out_len == 1 &&
                        out == 0 &&
                        0 <= j &&
                        j == 0 &&
                        0 <= first &&
                        first == 0 &&
                        ch == 32 &&
                        scan_char_z(i, l) == 32 &&
                        0 <= ch && ch <= 127 &&
                        cmp == cmp &&
                        Zlength(cnts) == 10 &&
                        Zlength(token_prefix_z(i, tlen, l)) == tlen &&
                        valid_string(token_prefix_z(i, tlen, l)) &&
                        string_length(token_prefix_z(i, tlen, l)) == tlen &&
                        string_length(token_prefix_z(i, tlen, l)) < INT_MAX &&
                        valid_string(number_word_z(d)) &&
                        string_length(number_word_z(d)) == number_word_len_z(d) &&
                        string_length(number_word_z(d)) < INT_MAX &&
                        token_empty_start_z(i, tlen, l) &&
                        (tlen < 31 => token_unsat_end_z(i, tlen, l)) &&
                        token_sat_start_z(i, tlen, l) &&
                        token_miss_prefix_z(d, token_prefix_z(i, tlen, l)) &&
                        scan_counts_z(i, l,
                                      Znth(0, cnts, 0), Znth(1, cnts, 0),
                                      Znth(2, cnts, 0), Znth(3, cnts, 0),
                                      Znth(4, cnts, 0), Znth(5, cnts, 0),
                                      Znth(6, cnts, 0), Znth(7, cnts, 0),
                                      Znth(8, cnts, 0), Znth(9, cnts, 0)) &&
                        scan_counts_exact_z(i, tlen, l,
                                      Znth(0, cnts, 0), Znth(1, cnts, 0),
                                      Znth(2, cnts, 0), Znth(3, cnts, 0),
                                      Znth(4, cnts, 0), Znth(5, cnts, 0),
                                      Znth(6, cnts, 0), Znth(7, cnts, 0),
                                      Znth(8, cnts, 0), Znth(9, cnts, 0)) &&
                        word == Znth(d, cons(w0, cons(w1, cons(w2, cons(w3, cons(w4, cons(w5, cons(w6, cons(w7, cons(w8, cons(w9, nil)))))))))), 0) &&
                        CharArray::full(numbers, len + 1, app(l, cons(0, nil))) *
                        store(words + (d * sizeof(char *)), char *, word) *
                        number_words_missing(words, d, word, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9) *
                        CharArray::full(space_word, number_word_len_z(10) + 1, app(number_word_z(10), cons(0, nil))) *
                        CharArray::undef_seg(space_word, number_word_len_z(10) + 1, 3) *
                        store_string(token, token_prefix_z(i, tlen, l)) *
                        CharArray::undef_seg(token, tlen + 1, 32) *
                        IntArray::full(count, 10, cnts) *
                        store_string(word, number_word_z(d))
                    */
                    cmp = strcmp(token, word)
                        /*@ where str1 = token_prefix_z(i, tlen, l),
                                  str2 = number_word_z(d) */;
                    if (cmp == 0) {
                        count[d] = count[d] + 1;
                        break;
                    }
                }
                tlen = 0;
            }
        } else if (tlen < 31) {
            token[tlen] = ch;
            tlen = tlen + 1;
        }
    }

    free_char_array(token, tlen, 32)
        /*@ where l = token_prefix_z(i, tlen, l) */;

    /*@ Inv Assert
        exists (cnts: list Z),
        numbers == numbers@pre &&
        w0 == w0 && w1 == w1 && w2 == w2 && w3 == w3 && w4 == w4 &&
        w5 == w5 && w6 == w6 && w7 == w7 && w8 == w8 && w9 == w9 &&
        space_word != 0 &&
        number_word_len_z(10) == 1 &&
        Zlength(app(number_word_z(10), cons(0, nil))) == 2 &&
        count == count &&
        token == token &&
        words == words &&
        word == word &&
        out == out &&
        first == first &&
        n == len &&
        tlen == 0 &&
        token == token &&
        ch == ch &&
        d == d &&
        cmp == cmp &&
        0 <= len && len + 1 < INT_MAX &&
        1 + 6 * (len + 1) <= INT_MAX &&
        Zlength(l) == len &&
        valid_string(l) &&
        string_length(l) == len &&
        problem_19_pre_z(l) &&
        ascii_range_z(l) &&
        Zlength(cnts) == 10 &&
        scan_counts_z(len + 1, l,
                      Znth(0, cnts, 0), Znth(1, cnts, 0),
                      Znth(2, cnts, 0), Znth(3, cnts, 0),
                      Znth(4, cnts, 0), Znth(5, cnts, 0),
                      Znth(6, cnts, 0), Znth(7, cnts, 0),
                      Znth(8, cnts, 0), Znth(9, cnts, 0)) &&
        scan_counts_exact_z(len + 1, 0, l,
                      Znth(0, cnts, 0), Znth(1, cnts, 0),
                      Znth(2, cnts, 0), Znth(3, cnts, 0),
                      Znth(4, cnts, 0), Znth(5, cnts, 0),
                      Znth(6, cnts, 0), Znth(7, cnts, 0),
                      Znth(8, cnts, 0), Znth(9, cnts, 0)) &&
        0 <= i && i <= 10 &&
        ((0 <= i && i < 10) =>
            valid_string(number_word_z(i)) &&
            string_length(number_word_z(i)) == number_word_len_z(i) &&
            string_length(number_word_z(i)) < INT_MAX) &&
        1 <= out_len &&
        out_len == output_capacity_prefix_by_input_z(i, l) &&
        0 <= Znth(i, cnts, 0) &&
        number_word_len_z(i) + 1 <= INT_MAX &&
        INT_MIN <= number_word_len_z(i) + 1 &&
        out_len + Znth(i, cnts, 0) * (number_word_len_z(i) + 1) <= INT_MAX &&
        CharArray::full(numbers, len + 1, app(l, cons(0, nil))) *
        number_words_full(words, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9) *
        CharArray::full(space_word, number_word_len_z(10) + 1, app(number_word_z(10), cons(0, nil))) *
        CharArray::undef_seg(space_word, number_word_len_z(10) + 1, 3) *
        data_at(&j, 0) *
        IntArray::full(count, 10, cnts)
    */
    for (i = 0; i < 10; i++) {
        /*@ Assert
            exists (cnts: list Z) (word_ptr: Z),
            numbers == numbers@pre &&
            w0 == w0 && w1 == w1 && w2 == w2 && w3 == w3 && w4 == w4 &&
            w5 == w5 && w6 == w6 && w7 == w7 && w8 == w8 && w9 == w9 &&
            space_word != 0 &&
            number_word_len_z(10) == 1 &&
            Zlength(app(number_word_z(10), cons(0, nil))) == 2 &&
            count == count &&
            token == token &&
            words == words &&
            word == word &&
            word_ptr == Znth(i, cons(w0, cons(w1, cons(w2, cons(w3, cons(w4, cons(w5, cons(w6, cons(w7, cons(w8, cons(w9, nil)))))))))), 0) &&
            out == out &&
            first == first &&
            n == len &&
            tlen == 0 &&
            token == token &&
            ch == ch &&
            d == d &&
            cmp == cmp &&
            0 <= len && len + 1 < INT_MAX &&
            1 + 6 * (len + 1) <= INT_MAX &&
            Zlength(l) == len &&
            valid_string(l) &&
            string_length(l) == len &&
            problem_19_pre_z(l) &&
            ascii_range_z(l) &&
            Zlength(cnts) == 10 &&
            scan_counts_z(len + 1, l,
                          Znth(0, cnts, 0), Znth(1, cnts, 0),
                          Znth(2, cnts, 0), Znth(3, cnts, 0),
                          Znth(4, cnts, 0), Znth(5, cnts, 0),
                          Znth(6, cnts, 0), Znth(7, cnts, 0),
                          Znth(8, cnts, 0), Znth(9, cnts, 0)) &&
            scan_counts_exact_z(len + 1, 0, l,
                          Znth(0, cnts, 0), Znth(1, cnts, 0),
                          Znth(2, cnts, 0), Znth(3, cnts, 0),
                          Znth(4, cnts, 0), Znth(5, cnts, 0),
                          Znth(6, cnts, 0), Znth(7, cnts, 0),
                          Znth(8, cnts, 0), Znth(9, cnts, 0)) &&
            0 <= i && i < 10 &&
            valid_string(number_word_z(i)) &&
            string_length(number_word_z(i)) == number_word_len_z(i) &&
            string_length(number_word_z(i)) < INT_MAX &&
            1 <= out_len &&
            out_len == output_capacity_prefix_by_input_z(i, l) &&
            0 <= Znth(i, cnts, 0) &&
            number_word_len_z(i) + 1 <= INT_MAX &&
            INT_MIN <= number_word_len_z(i) + 1 &&
            out_len + Znth(i, cnts, 0) * (number_word_len_z(i) + 1) <= INT_MAX &&
            CharArray::full(numbers, len + 1, app(l, cons(0, nil))) *
            number_words_full(words, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9) *
            CharArray::full(space_word, number_word_len_z(10) + 1, app(number_word_z(10), cons(0, nil))) *
            CharArray::undef_seg(space_word, number_word_len_z(10) + 1, 3) *
            data_at(&j, 0) *
            IntArray::full(count, 10, cnts)
        */
        if (i == 0) word = w0;
        else if (i == 1) word = w1;
        else if (i == 2) word = w2;
        else if (i == 3) word = w3;
        else if (i == 4) word = w4;
        else if (i == 5) word = w5;
        else if (i == 6) word = w6;
        else if (i == 7) word = w7;
        else if (i == 8) word = w8;
        else word = w9;
        /*@ Assert
            exists (cnts: list Z),
            numbers == numbers@pre &&
            w0 == w0 && w1 == w1 && w2 == w2 && w3 == w3 && w4 == w4 &&
            w5 == w5 && w6 == w6 && w7 == w7 && w8 == w8 && w9 == w9 &&
            space_word != 0 &&
            number_word_len_z(10) == 1 &&
            Zlength(app(number_word_z(10), cons(0, nil))) == 2 &&
            count == count &&
            token == token &&
            words == words &&
            word == Znth(i, cons(w0, cons(w1, cons(w2, cons(w3, cons(w4, cons(w5, cons(w6, cons(w7, cons(w8, cons(w9, nil)))))))))), 0) &&
            out == out &&
            first == first &&
            n == len &&
            tlen == 0 &&
            token == token &&
            ch == ch &&
            d == d &&
            cmp == cmp &&
            0 <= len && len + 1 < INT_MAX &&
            1 + 6 * (len + 1) <= INT_MAX &&
            Zlength(l) == len &&
            valid_string(l) &&
            string_length(l) == len &&
            problem_19_pre_z(l) &&
            ascii_range_z(l) &&
            Zlength(cnts) == 10 &&
            scan_counts_z(len + 1, l,
                          Znth(0, cnts, 0), Znth(1, cnts, 0),
                          Znth(2, cnts, 0), Znth(3, cnts, 0),
                          Znth(4, cnts, 0), Znth(5, cnts, 0),
                          Znth(6, cnts, 0), Znth(7, cnts, 0),
                          Znth(8, cnts, 0), Znth(9, cnts, 0)) &&
            scan_counts_exact_z(len + 1, 0, l,
                          Znth(0, cnts, 0), Znth(1, cnts, 0),
                          Znth(2, cnts, 0), Znth(3, cnts, 0),
                          Znth(4, cnts, 0), Znth(5, cnts, 0),
                          Znth(6, cnts, 0), Znth(7, cnts, 0),
                          Znth(8, cnts, 0), Znth(9, cnts, 0)) &&
            0 <= i && i < 10 &&
            valid_string(number_word_z(i)) &&
            string_length(number_word_z(i)) == number_word_len_z(i) &&
            string_length(number_word_z(i)) < INT_MAX &&
            1 <= out_len &&
            out_len == output_capacity_prefix_by_input_z(i, l) &&
            0 <= Znth(i, cnts, 0) &&
            number_word_len_z(i) + 1 <= INT_MAX &&
            INT_MIN <= number_word_len_z(i) + 1 &&
            out_len + Znth(i, cnts, 0) * (number_word_len_z(i) + 1) <= INT_MAX &&
            CharArray::full(numbers, len + 1, app(l, cons(0, nil))) *
            store(words + (i * sizeof(char *)), char *, word) *
            number_words_missing(words, i, word, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9) *
            store_string(word, number_word_z(i)) *
            CharArray::full(space_word, number_word_len_z(10) + 1, app(number_word_z(10), cons(0, nil))) *
            CharArray::undef_seg(space_word, number_word_len_z(10) + 1, 3) *
            data_at(&j, 0) *
            IntArray::full(count, 10, cnts)
        */
        out_len = out_len + count[i] *
            (strlen(word) /*@ where str = number_word_z(i) */ + 1);
    }
    if (out_len > 1) {
        out_len = out_len - 1;
    }

    out = malloc_char_array(out_len);
    out[0] = 0;
    first = 1;

    /*@ Inv Assert
        exists (cnts: list Z),
        numbers == numbers@pre &&
        w0 == w0 && w1 == w1 && w2 == w2 && w3 == w3 && w4 == w4 &&
        w5 == w5 && w6 == w6 && w7 == w7 && w8 == w8 && w9 == w9 &&
        space_word != 0 &&
        number_word_len_z(10) == 1 &&
        Zlength(app(number_word_z(10), cons(0, nil))) == 2 &&
        count == count &&
        token == token &&
        words == words &&
        word == word &&
        out != 0 &&
        n == len &&
        tlen == 0 &&
        token == token &&
        ch == ch &&
        d == d &&
        cmp == cmp &&
        0 <= len && len + 1 < INT_MAX &&
        1 + 6 * (len + 1) <= INT_MAX &&
        Zlength(l) == len &&
        valid_string(l) &&
        string_length(l) == len &&
        problem_19_pre_z(l) &&
        ascii_range_z(l) &&
        1 <= out_len &&
        Zlength(cnts) == 10 &&
        scan_counts_z(len + 1, l,
                      Znth(0, cnts, 0), Znth(1, cnts, 0),
                      Znth(2, cnts, 0), Znth(3, cnts, 0),
                      Znth(4, cnts, 0), Znth(5, cnts, 0),
                      Znth(6, cnts, 0), Znth(7, cnts, 0),
                      Znth(8, cnts, 0), Znth(9, cnts, 0)) &&
        scan_counts_exact_z(len + 1, 0, l,
                      Znth(0, cnts, 0), Znth(1, cnts, 0),
                      Znth(2, cnts, 0), Znth(3, cnts, 0),
                      Znth(4, cnts, 0), Znth(5, cnts, 0),
                      Znth(6, cnts, 0), Znth(7, cnts, 0),
                      Znth(8, cnts, 0), Znth(9, cnts, 0)) &&
        0 <= i && i <= 10 &&
        0 <= j &&
        0 <= first && first <= 1 &&
        (first == 0 => 0 < Zlength(output_prefix_by_input_z(i, 0, l))) &&
        (first != 0 => Zlength(output_prefix_by_input_z(i, 0, l)) == 0) &&
        out_len == output_used_capacity_prefix_by_input_z(10, l) &&
        Zlength(output_prefix_by_input_z(i, 0, l)) + 1 <= out_len &&
        CharArray::full(numbers, len + 1, app(l, cons(0, nil))) *
        number_words_full(words, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9) *
        CharArray::full(space_word, number_word_len_z(10) + 1, app(number_word_z(10), cons(0, nil))) *
        CharArray::undef_seg(space_word, number_word_len_z(10) + 1, 3) *
        IntArray::full(count, 10, cnts) *
        CharArray::full(out,
                        Zlength(output_prefix_by_input_z(i, 0, l)) + 1,
                        app(output_prefix_by_input_z(i, 0, l), cons(0, nil))) *
        CharArray::undef_seg(out,
                        Zlength(output_prefix_by_input_z(i, 0, l)) + 1, out_len)
    */
    for (i = 0; i < 10; i++) {
        /*@ Assert
            exists (cnts: list Z) (word_ptr: Z),
            numbers == numbers@pre &&
            w0 == w0 && w1 == w1 && w2 == w2 && w3 == w3 && w4 == w4 &&
            w5 == w5 && w6 == w6 && w7 == w7 && w8 == w8 && w9 == w9 &&
            space_word != 0 &&
            number_word_len_z(10) == 1 &&
            Zlength(app(number_word_z(10), cons(0, nil))) == 2 &&
            count == count &&
            token == token &&
            words == words &&
            word == word &&
            word_ptr == Znth(i, cons(w0, cons(w1, cons(w2, cons(w3, cons(w4, cons(w5, cons(w6, cons(w7, cons(w8, cons(w9, nil)))))))))), 0) &&
            out != 0 &&
            n == len &&
            tlen == 0 &&
            token == token &&
            ch == ch &&
            d == d &&
            cmp == cmp &&
            0 <= len && len + 1 < INT_MAX &&
            1 + 6 * (len + 1) <= INT_MAX &&
            Zlength(l) == len &&
            valid_string(l) &&
            string_length(l) == len &&
            problem_19_pre_z(l) &&
            ascii_range_z(l) &&
            1 <= out_len &&
            Zlength(cnts) == 10 &&
            scan_counts_z(len + 1, l,
                          Znth(0, cnts, 0), Znth(1, cnts, 0),
                          Znth(2, cnts, 0), Znth(3, cnts, 0),
                          Znth(4, cnts, 0), Znth(5, cnts, 0),
                          Znth(6, cnts, 0), Znth(7, cnts, 0),
                          Znth(8, cnts, 0), Znth(9, cnts, 0)) &&
            scan_counts_exact_z(len + 1, 0, l,
                          Znth(0, cnts, 0), Znth(1, cnts, 0),
                          Znth(2, cnts, 0), Znth(3, cnts, 0),
                          Znth(4, cnts, 0), Znth(5, cnts, 0),
                          Znth(6, cnts, 0), Znth(7, cnts, 0),
                          Znth(8, cnts, 0), Znth(9, cnts, 0)) &&
            0 <= i && i < 10 &&
            0 <= j &&
            0 <= first && first <= 1 &&
            (first == 0 => 0 < Zlength(output_prefix_by_input_z(i, 0, l))) &&
            (first != 0 => Zlength(output_prefix_by_input_z(i, 0, l)) == 0) &&
            out_len == output_used_capacity_prefix_by_input_z(10, l) &&
            Zlength(output_prefix_by_input_z(i, 0, l)) + 1 <= out_len &&
            valid_string(number_word_z(i)) &&
            string_length(number_word_z(i)) == number_word_len_z(i) &&
            string_length(number_word_z(i)) < INT_MAX &&
            CharArray::full(numbers, len + 1, app(l, cons(0, nil))) *
            number_words_full(words, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9) *
            CharArray::full(space_word, number_word_len_z(10) + 1, app(number_word_z(10), cons(0, nil))) *
            CharArray::undef_seg(space_word, number_word_len_z(10) + 1, 3) *
            IntArray::full(count, 10, cnts) *
            CharArray::full(out,
                            Zlength(output_prefix_by_input_z(i, 0, l)) + 1,
                            app(output_prefix_by_input_z(i, 0, l), cons(0, nil))) *
            CharArray::undef_seg(out,
                            Zlength(output_prefix_by_input_z(i, 0, l)) + 1, out_len)
        */
        if (i == 0) word = w0;
        else if (i == 1) word = w1;
        else if (i == 2) word = w2;
        else if (i == 3) word = w3;
        else if (i == 4) word = w4;
        else if (i == 5) word = w5;
        else if (i == 6) word = w6;
        else if (i == 7) word = w7;
        else if (i == 8) word = w8;
        else word = w9;
        /*@ Inv Assert
            exists (cnts: list Z),
            numbers == numbers@pre &&
            w0 == w0 && w1 == w1 && w2 == w2 && w3 == w3 && w4 == w4 &&
            w5 == w5 && w6 == w6 && w7 == w7 && w8 == w8 && w9 == w9 &&
            space_word != 0 &&
        number_word_len_z(10) == 1 &&
        Zlength(app(number_word_z(10), cons(0, nil))) == 2 &&
            count == count &&
            token == token &&
            words == words &&
            out != 0 &&
            n == len &&
            tlen == 0 &&
            token == token &&
            ch == ch &&
            d == d &&
            cmp == cmp &&
            0 <= len && len + 1 < INT_MAX &&
            1 + 6 * (len + 1) <= INT_MAX &&
            Zlength(l) == len &&
            valid_string(l) &&
            string_length(l) == len &&
            problem_19_pre_z(l) &&
            ascii_range_z(l) &&
            1 <= out_len &&
            Zlength(cnts) == 10 &&
            scan_counts_z(len + 1, l,
                          Znth(0, cnts, 0), Znth(1, cnts, 0),
                          Znth(2, cnts, 0), Znth(3, cnts, 0),
                          Znth(4, cnts, 0), Znth(5, cnts, 0),
                          Znth(6, cnts, 0), Znth(7, cnts, 0),
                          Znth(8, cnts, 0), Znth(9, cnts, 0)) &&
            scan_counts_exact_z(len + 1, 0, l,
                          Znth(0, cnts, 0), Znth(1, cnts, 0),
                          Znth(2, cnts, 0), Znth(3, cnts, 0),
                          Znth(4, cnts, 0), Znth(5, cnts, 0),
                          Znth(6, cnts, 0), Znth(7, cnts, 0),
                          Znth(8, cnts, 0), Znth(9, cnts, 0)) &&
            0 <= i && i < 10 &&
            0 <= j && j <= Znth(i, cnts, 0) &&
            0 <= first && first <= 1 &&
            (first == 0 => 0 < Zlength(output_prefix_by_input_z(i, j, l))) &&
            (first != 0 => Zlength(output_prefix_by_input_z(i, j, l)) == 0) &&
            out_len == output_used_capacity_prefix_by_input_z(10, l) &&
            valid_string(output_prefix_by_input_z(i, j, l)) &&
            string_length(output_prefix_by_input_z(i, j, l)) ==
                Zlength(output_prefix_by_input_z(i, j, l)) &&
            Zlength(output_prefix_by_input_z(i, j, l)) + 1 <= out_len &&
            valid_string(number_word_z(10)) &&
            string_length(number_word_z(10)) == number_word_len_z(10) &&
            string_length(number_word_z(10)) < INT_MAX &&
            valid_string(number_word_z(i)) &&
            string_length(number_word_z(i)) == number_word_len_z(i) &&
            string_length(number_word_z(i)) < INT_MAX &&
            CharArray::full(numbers, len + 1, app(l, cons(0, nil))) *
            store(words + (i * sizeof(char *)), char *, word) *
            number_words_missing(words, i, word, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9) *
            CharArray::full(space_word, number_word_len_z(10) + 1, app(number_word_z(10), cons(0, nil))) *
            CharArray::undef_seg(space_word, number_word_len_z(10) + 1, 3) *
            IntArray::full(count, 10, cnts) *
            CharArray::full(out,
                            Zlength(output_prefix_by_input_z(i, j, l)) + 1,
                            app(output_prefix_by_input_z(i, j, l), cons(0, nil))) *
            CharArray::undef_seg(out,
                            Zlength(output_prefix_by_input_z(i, j, l)) + 1, out_len) *
            CharArray::full(word, number_word_len_z(i) + 1, app(number_word_z(i), cons(0, nil)))
        */
        for (j = 0; j < count[i]; j++) {
            if (first == 0) {
                /*@ Assert
                    exists (cnts: list Z),
                    numbers == numbers@pre &&
                    count == count &&
                    words == words &&
                    out != 0 &&
                    space_word != 0 &&
                    word == word &&
                    token == token &&
                    tlen == 0 &&
                    ch == ch &&
                    d == d &&
                    cmp == cmp &&
                    n == len &&
                    0 <= len && len + 1 < INT_MAX &&
                    1 + 6 * (len + 1) <= INT_MAX &&
                    Zlength(l) == len &&
                    valid_string(l) &&
                    string_length(l) == len &&
                    problem_19_pre_z(l) &&
                    ascii_range_z(l) &&
                    1 <= out_len &&
                    Zlength(cnts) == 10 &&
                    scan_counts_z(len + 1, l,
                                  Znth(0, cnts, 0), Znth(1, cnts, 0),
                                  Znth(2, cnts, 0), Znth(3, cnts, 0),
                                  Znth(4, cnts, 0), Znth(5, cnts, 0),
                                  Znth(6, cnts, 0), Znth(7, cnts, 0),
                                  Znth(8, cnts, 0), Znth(9, cnts, 0)) &&
                    scan_counts_exact_z(len + 1, 0, l,
                                  Znth(0, cnts, 0), Znth(1, cnts, 0),
                                  Znth(2, cnts, 0), Znth(3, cnts, 0),
                                  Znth(4, cnts, 0), Znth(5, cnts, 0),
                                  Znth(6, cnts, 0), Znth(7, cnts, 0),
                                  Znth(8, cnts, 0), Znth(9, cnts, 0)) &&
                    0 <= i && i < 10 &&
                    0 <= j && j < Znth(i, cnts, 0) &&
                    first == 0 &&
                    0 < Zlength(output_prefix_by_input_z(i, j, l)) &&
                    out_len == output_used_capacity_prefix_by_input_z(10, l) &&
                    valid_string(output_prefix_by_input_z(i, j, l)) &&
                    string_length(output_prefix_by_input_z(i, j, l)) ==
                        Zlength(output_prefix_by_input_z(i, j, l)) &&
                    valid_string(number_word_z(10)) &&
                    string_length(number_word_z(10)) == number_word_len_z(10) &&
                    string_length(number_word_z(10)) < INT_MAX &&
                    string_length(output_prefix_by_input_z(i, j, l)) +
                        string_length(number_word_z(10)) + 1 < INT_MAX &&
                    Zlength(output_prefix_by_input_z(i, j, l)) + number_word_len_z(10) + 1 <= out_len &&
                    CharArray::full(numbers, len + 1, app(l, cons(0, nil))) *
                    store(words + (i * sizeof(char *)), char *, word) *
                    number_words_missing(words, i, word, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9) *
                    store_string(space_word, number_word_z(10)) *
                    CharArray::undef_seg(space_word, number_word_len_z(10) + 1, 3) *
                    IntArray::full(count, 10, cnts) *
                    store_string(out, output_prefix_by_input_z(i, j, l)) *
                    CharArray::undef_seg(out,
                        Zlength(output_prefix_by_input_z(i, j, l)) + 1,
                        Zlength(output_prefix_by_input_z(i, j, l)) + number_word_len_z(10) + 1) *
                    CharArray::undef_seg(out,
                        Zlength(output_prefix_by_input_z(i, j, l)) + number_word_len_z(10) + 1,
                        out_len) *
                    CharArray::full(word, number_word_len_z(i) + 1, app(number_word_z(i), cons(0, nil)))
                */
                strcat(out, space_word)
                    /*@ where dst_str = output_prefix_by_input_z(i, j, l),
                              src_str = number_word_z(10) */;
                /*@ Assert
                    exists (cnts: list Z),
                    numbers == numbers@pre &&
                    count == count &&
                    words == words &&
                    out != 0 &&
                    space_word != 0 &&
                    word == word &&
                    token == token &&
                    tlen == 0 &&
                    ch == ch &&
                    d == d &&
                    cmp == cmp &&
                    n == len &&
                    0 <= len && len + 1 < INT_MAX &&
                    1 + 6 * (len + 1) <= INT_MAX &&
                    Zlength(l) == len &&
                    valid_string(l) &&
                    string_length(l) == len &&
                    problem_19_pre_z(l) &&
                    ascii_range_z(l) &&
                    1 <= out_len &&
                    Zlength(cnts) == 10 &&
                    scan_counts_z(len + 1, l,
                                  Znth(0, cnts, 0), Znth(1, cnts, 0),
                                  Znth(2, cnts, 0), Znth(3, cnts, 0),
                                  Znth(4, cnts, 0), Znth(5, cnts, 0),
                                  Znth(6, cnts, 0), Znth(7, cnts, 0),
                                  Znth(8, cnts, 0), Znth(9, cnts, 0)) &&
                    scan_counts_exact_z(len + 1, 0, l,
                                  Znth(0, cnts, 0), Znth(1, cnts, 0),
                                  Znth(2, cnts, 0), Znth(3, cnts, 0),
                                  Znth(4, cnts, 0), Znth(5, cnts, 0),
                                  Znth(6, cnts, 0), Znth(7, cnts, 0),
                                  Znth(8, cnts, 0), Znth(9, cnts, 0)) &&
                    0 <= i && i < 10 &&
                    0 <= j && j < Znth(i, cnts, 0) &&
                    first == 0 &&
                    0 < Zlength(output_prefix_by_input_z(i, j, l)) &&
                    out_len == output_used_capacity_prefix_by_input_z(10, l) &&
                    valid_string(number_word_z(i)) &&
                    string_length(number_word_z(i)) == number_word_len_z(i) &&
                    string_length(number_word_z(i)) < INT_MAX &&
                    valid_string(app(output_prefix_by_input_z(i, j, l), number_word_z(10))) &&
                    string_length(app(output_prefix_by_input_z(i, j, l), number_word_z(10))) ==
                        Zlength(output_prefix_by_input_z(i, j, l)) + number_word_len_z(10) &&
                    string_length(app(output_prefix_by_input_z(i, j, l), number_word_z(10))) +
                        string_length(number_word_z(i)) + 1 < INT_MAX &&
                    Zlength(output_prefix_by_input_z(i, j, l)) + number_word_len_z(10) +
                        number_word_len_z(i) + 1 <= out_len &&
                    CharArray::full(numbers, len + 1, app(l, cons(0, nil))) *
                    store(words + (i * sizeof(char *)), char *, word) *
                    number_words_missing(words, i, word, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9) *
                    store_string(space_word, number_word_z(10)) *
                    CharArray::undef_seg(space_word, number_word_len_z(10) + 1, 3) *
                    IntArray::full(count, 10, cnts) *
                    store_string(out, app(output_prefix_by_input_z(i, j, l), number_word_z(10))) *
                    CharArray::undef_seg(out,
                        Zlength(output_prefix_by_input_z(i, j, l)) + number_word_len_z(10) + 1,
                        Zlength(output_prefix_by_input_z(i, j, l)) + number_word_len_z(10) +
                            number_word_len_z(i) + 1) *
                    CharArray::undef_seg(out,
                        Zlength(output_prefix_by_input_z(i, j, l)) + number_word_len_z(10) +
                            number_word_len_z(i) + 1,
                        out_len) *
                    store_string(word, number_word_z(i))
                */
                strcat(out, word)
                    /*@ where dst_str = app(output_prefix_by_input_z(i, j, l),
                                          number_word_z(10)),
                              src_str = number_word_z(i) */;
            } else {
                /*@ Assert
                    exists (cnts: list Z),
                    numbers == numbers@pre &&
                    count == count &&
                    words == words &&
                    out != 0 &&
                    space_word != 0 &&
                    word == word &&
                    token == token &&
                    tlen == 0 &&
                    ch == ch &&
                    d == d &&
                    cmp == cmp &&
                    n == len &&
                    0 <= len && len + 1 < INT_MAX &&
                    1 + 6 * (len + 1) <= INT_MAX &&
                    Zlength(l) == len &&
                    valid_string(l) &&
                    string_length(l) == len &&
                    problem_19_pre_z(l) &&
                    ascii_range_z(l) &&
                    1 <= out_len &&
                    Zlength(cnts) == 10 &&
                    scan_counts_z(len + 1, l,
                                  Znth(0, cnts, 0), Znth(1, cnts, 0),
                                  Znth(2, cnts, 0), Znth(3, cnts, 0),
                                  Znth(4, cnts, 0), Znth(5, cnts, 0),
                                  Znth(6, cnts, 0), Znth(7, cnts, 0),
                                  Znth(8, cnts, 0), Znth(9, cnts, 0)) &&
                    scan_counts_exact_z(len + 1, 0, l,
                                  Znth(0, cnts, 0), Znth(1, cnts, 0),
                                  Znth(2, cnts, 0), Znth(3, cnts, 0),
                                  Znth(4, cnts, 0), Znth(5, cnts, 0),
                                  Znth(6, cnts, 0), Znth(7, cnts, 0),
                                  Znth(8, cnts, 0), Znth(9, cnts, 0)) &&
                    0 <= i && i < 10 &&
                    0 <= j && j < Znth(i, cnts, 0) &&
                    first != 0 &&
                    Zlength(output_prefix_by_input_z(i, j, l)) == 0 &&
                    out_len == output_used_capacity_prefix_by_input_z(10, l) &&
                    valid_string(output_prefix_by_input_z(i, j, l)) &&
                    string_length(output_prefix_by_input_z(i, j, l)) ==
                        Zlength(output_prefix_by_input_z(i, j, l)) &&
                    valid_string(number_word_z(i)) &&
                    string_length(number_word_z(i)) == number_word_len_z(i) &&
                    string_length(number_word_z(i)) < INT_MAX &&
                    string_length(output_prefix_by_input_z(i, j, l)) +
                        string_length(number_word_z(i)) + 1 < INT_MAX &&
                    Zlength(output_prefix_by_input_z(i, j, l)) + number_word_len_z(i) + 1 <= out_len &&
                    CharArray::full(numbers, len + 1, app(l, cons(0, nil))) *
                    store(words + (i * sizeof(char *)), char *, word) *
                    number_words_missing(words, i, word, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9) *
                    CharArray::full(space_word, number_word_len_z(10) + 1, app(number_word_z(10), cons(0, nil))) *
                    CharArray::undef_seg(space_word, number_word_len_z(10) + 1, 3) *
                    IntArray::full(count, 10, cnts) *
                    store_string(out, output_prefix_by_input_z(i, j, l)) *
                    CharArray::undef_seg(out,
                        Zlength(output_prefix_by_input_z(i, j, l)) + 1,
                        Zlength(output_prefix_by_input_z(i, j, l)) + number_word_len_z(i) + 1) *
                    CharArray::undef_seg(out,
                        Zlength(output_prefix_by_input_z(i, j, l)) + number_word_len_z(i) + 1,
                        out_len) *
                    store_string(word, number_word_z(i))
                */
                strcat(out, word)
                    /*@ where dst_str = output_prefix_by_input_z(i, j, l),
                              src_str = number_word_z(i) */;
            }
            first = 0;
        }
    }
    free_char_array(space_word, 2, 3)
        /*@ where l = app(number_word_z(10), cons(0, nil)) */;
    /*@ Assert
        exists (cnts: list Z),
        numbers == numbers@pre &&
        w0 == w0 && w1 == w1 && w2 == w2 && w3 == w3 && w4 == w4 &&
        w5 == w5 && w6 == w6 && w7 == w7 && w8 == w8 && w9 == w9 &&
        count == count &&
        token == token &&
        words == words &&
        word == word &&
        space_word == space_word &&
        out != 0 &&
        out_len == out_len &&
        n == len &&
        tlen == 0 &&
        ch == ch &&
        d == d &&
        j == j &&
        first == first &&
        cmp == cmp &&
        i == 10 &&
        0 <= len && len + 1 < INT_MAX &&
        1 + 6 * (len + 1) <= INT_MAX &&
        Zlength(l) == len &&
        valid_string(l) &&
        string_length(l) == len &&
        problem_19_pre_z(l) &&
        ascii_range_z(l) &&
        Zlength(cnts) == 10 &&
        1 <= out_len &&
        out_len == output_used_capacity_prefix_by_input_z(10, l) &&
        Zlength(output_prefix_by_input_z(10, 0, l)) + 1 == out_len &&
        CharArray::full(numbers, len + 1, app(l, cons(0, nil))) *
        PtrArray::full(words, 10, cons(w0, cons(w1, cons(w2, cons(w3, cons(w4, cons(w5, cons(w6, cons(w7, cons(w8, cons(w9, nil))))))))))) *
        CharArray::full(w0, 5, app(number_word_z(0), cons(0, nil))) *
        CharArray::full(w1, 4, app(number_word_z(1), cons(0, nil))) *
        CharArray::full(w2, 4, app(number_word_z(2), cons(0, nil))) *
        CharArray::full(w3, 6, app(number_word_z(3), cons(0, nil))) *
        CharArray::full(w4, 5, app(number_word_z(4), cons(0, nil))) *
        CharArray::full(w5, 5, app(number_word_z(5), cons(0, nil))) *
        CharArray::full(w6, 4, app(number_word_z(6), cons(0, nil))) *
        CharArray::full(w7, 6, app(number_word_z(7), cons(0, nil))) *
        CharArray::full(w8, 6, app(number_word_z(8), cons(0, nil))) *
        CharArray::full(w9, 5, app(number_word_z(9), cons(0, nil))) *
        IntArray::full(count, 10, cnts) *
        CharArray::full(out,
                        Zlength(output_prefix_by_input_z(10, 0, l)) + 1,
                        app(output_prefix_by_input_z(10, 0, l), cons(0, nil)))
    */
    return out;
}
p
