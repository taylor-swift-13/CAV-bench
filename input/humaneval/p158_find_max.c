/*
Write a function that accepts a vector of strings.
The vector contains different words. Return the word with maximum number
of unique characters. If multiple strings have maximum number of unique
characters, return the one which comes first in lexicographical order.

find_max({"name", "of", 'string"}) == 'string"
find_max({"name", "enam", "game"}) == "enam"
find_max({"aaaaaaa", "bb" ,"cc"}) == "aaaaaaa"
*/
#include "ptr_array2_def.h"
#include "int_array_def.h"
#include "string.h"

/*@ Extern Coq (problem_158_pre_z: list (list Z) -> Prop)
               (problem_158_spec_z: list (list Z) -> Z -> Prop)
               (rows_well_formed_158: list (list Z) -> Z -> Prop)
               (row_payload_z_158: list Z -> list Z)
               (row_unique_count_z_158: list Z -> Z)
               (count_scan_state_158: list Z -> Z -> list Z -> Z -> Prop)
               (best_prefix_state_158: list (list Z) -> Z -> Z -> Z -> Prop)
               (reset_prefix_state_158: Z -> list Z -> Prop)
               (strcmp_negative_158: list Z -> list Z -> Z -> Prop)
               (char_ptr_array2_missing_two_158:
                  Z -> Z -> Z -> Z -> Z -> Z -> list (list Z) -> Assertion)
               (Znth: {A} -> Z -> list A -> A -> A)
               (Zlength: {A} -> list A -> Z)
               (zeros: Z -> list Z)
*/
/*@ Import Coq Require Import p158_find_max */

char* find_max(char** words, int words_size)
/*@ With rows
    Require
      0 < words_size && words_size <= 100 &&
      rows_well_formed_158(rows, words_size) &&
      problem_158_pre_z(rows) &&
      CharPtrArray2::full(words, words_size, rows)
    Ensure exists best_idx row_ptr,
      0 <= best_idx && best_idx < words_size &&
      __return == row_ptr &&
      problem_158_spec_z(rows, best_idx) &&
      CharPtrArray2::missing_i(words, words_size, best_idx, row_ptr, rows) *
      data_at(words + best_idx * sizeof(char *), char *, row_ptr) *
      CharArray::full(row_ptr, Zlength(Znth(best_idx, rows, nil)), Znth(best_idx, rows, nil))
*/
{
    char* max;
    char* cur;
    int seen[128];
    int maxu;
    int unique;
    int cmp;
    int best_idx;
    int i;
    int j;
    int k;
    int len;
    int ch;

    max = words[0];
    maxu = 0;
    unique = 0;
    cmp = 0;
    best_idx = 0;
    cur = 0;
    i = 0;
    j = 0;
    len = 0;
    ch = 0;

    k = 0;

    while (k < 128) {
        seen[k] = 0;
        k = k + 1;
    }

    i = 0;

    while (i < words_size) {

        k = 0;

        while (k < 128) {
            seen[k] = 0;
            k = k + 1;
        }

        cur = words[i];

        len = (int)strlen(cur) ;
        unique = 0;
        j = 0;
        ch = 0;

        while (j < len) {
            ch = cur[j];

            if (seen[ch] == 0) {
                seen[ch] = 1;
                unique = unique + 1;
            }
            j = j + 1;
        }

        if (unique > maxu) {
            max = cur;
            maxu = unique;
            best_idx = i;
        } else {
            if (unique == maxu && i != best_idx) {

                max = words[best_idx];

                cmp = strcmp(cur, max)
                  ;

                if (cmp < 0) {
                    max = cur;
                    best_idx = i;
                }
            }
        }

        i = i + 1;
    }

    max = words[best_idx];

    return max;
}
