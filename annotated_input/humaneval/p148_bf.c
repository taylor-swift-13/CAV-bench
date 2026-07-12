/*
There are eight planets in our solar system: the closerst to the Sun
is Mercury, the next one is Venus, then Earth, Mars, Jupiter, Saturn,
Uranus, Neptune.
Write a function that takes two planet names as strings planet1 && planet2.
The function should return a vector containing all planets whose orbits are
located between the orbit of planet1 && the orbit of planet2, sorted by
the proximity to the sun.
The function should return an empty vector if planet1 || planet2
are ! correct planet names.
Examples
bf("Jupiter", "Neptune") ==> {"Saturn", "Uranus"}
bf("Earth", "Mercury") ==> {"Venus"}
bf("Mercury", "Uranus") ==> {"Venus", "Earth", "Mars", "Jupiter", "Saturn"}
*/
#include "ptr_array2_def.h"
#include "string.h"

/*@ Extern Coq (problem_148_pre_z: list Z -> list Z -> Prop)
               (problem_148_spec_z: list Z -> list Z -> list (list Z) -> Prop)
               (planet_payload_148: Z -> list Z)
               (planet_literal_148: Z -> String)
               (planet_ptr_148: (String -> Z) -> Z -> Z)
               (planet_index_z_148: list Z -> Z)
               (planet_scan_state_148: list Z -> Z -> Z -> Prop)
               (planet_min_index_148: Z -> Z -> Z)
               (planet_max_index_148: Z -> Z -> Z)
               (planet_between_rows_148: Z -> Z -> list (list Z))
               (planet_between_ptrs_148: (String -> Z) -> Z -> Z -> list Z)
               (output_state_148: (String -> Z) -> Z -> Z -> Z -> list (list Z) -> list Z -> Prop)
               (strcmp_eq_payload_148: list Z -> list Z -> Z -> Prop)
               (lit_payload_148: String -> list Z)
               (all_planet_literals_148: list String)
               (planet_payloads_string_safe_148: Prop)
               (planet_literals_heap_148: (String -> Z) -> Assertion)
               (LitMap: String -> Z)
               (Zlength: {A} -> list A -> Z)
*/
/*@ Import Coq Require Import p148_bf */

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

StrArray *bf(char* planet1, char* planet2)
/*@ With p1 p2
    Require
      valid_string(p1) && valid_string(p2) &&
      string_length(p1) < INT_MAX &&
      string_length(p2) < INT_MAX &&
      problem_148_pre_z(p1, p2) &&
      store_string(planet1, p1) *
      store_string(planet2, p2) *
      GlobalStrings(LitMap)
    Ensure exists data output_rows output_ptrs output_size,
      __return != 0 &&
      data != 0 &&
      0 <= output_size && output_size <= 6 &&
      output_size == Zlength(output_rows) &&
      output_size == Zlength(output_ptrs) &&
      output_rows == planet_between_rows_148(planet_index_z_148(p1), planet_index_z_148(p2)) &&
      output_ptrs == planet_between_ptrs_148(LitMap, planet_index_z_148(p1), planet_index_z_148(p2)) &&
      problem_148_spec_z(p1, p2, output_rows) &&
      data_at(&(__return -> data), data) *
      data_at(&(__return -> size), output_size) *
      store_string(planet1, p1) *
      store_string(planet2, p2) *
      PtrArray::seg(data, 0, output_size, output_ptrs) *
      PtrArray::undef_seg(data, output_size, 6) *
      planet_literals_heap_148(LitMap)
*/
{
    char *mercury = "Mercury";
    char *venus = "Venus";
    char *earth = "Earth";
    char *mars = "Mars";
    char *jupiter = "Jupiter";
    char *saturn = "Saturn";
    char *uranus = "Uranus";
    char *neptune = "Neptune";
    /*@ Assert
      mercury == planet_ptr_148(LitMap, 0) &&
      venus == planet_ptr_148(LitMap, 1) &&
      earth == planet_ptr_148(LitMap, 2) &&
      mars == planet_ptr_148(LitMap, 3) &&
      jupiter == planet_ptr_148(LitMap, 4) &&
      saturn == planet_ptr_148(LitMap, 5) &&
      uranus == planet_ptr_148(LitMap, 6) &&
      neptune == planet_ptr_148(LitMap, 7) &&
      planet1 == planet1@pre &&
      planet2 == planet2@pre &&
      valid_string(p1) &&
      valid_string(p2) &&
      string_length(p1) < INT_MAX &&
      string_length(p2) < INT_MAX &&
      planet_payloads_string_safe_148 &&
      store_string(planet1@pre, p1) *
      store_string(planet2@pre, p2) *
      planet_literals_heap_148(LitMap)
    */
    StrArray *out = malloc_str_array_struct();
    out->data = malloc_char_ptr_array(6);
    char **data = out->data;
    int out_size = 0;
    int pos1 = -1;
    int pos2 = -1;
    int cmp = 0;
    int m = 0;
    int lo = -1;
    int hi = -1;
    char *cur = 0;

    /*@ Inv Assert
      0 <= m && m <= 8 &&
      -1 <= pos1 && pos1 <= 7 &&
      -1 <= pos2 && pos2 <= 7 &&
      planet_scan_state_148(p1, m, pos1) &&
      planet_scan_state_148(p2, m, pos2) &&
      out_size == 0 &&
      lo == -1 &&
      hi == -1 &&
      cur == cur &&
      mercury == planet_ptr_148(LitMap, 0) &&
      venus == planet_ptr_148(LitMap, 1) &&
      earth == planet_ptr_148(LitMap, 2) &&
      mars == planet_ptr_148(LitMap, 3) &&
      jupiter == planet_ptr_148(LitMap, 4) &&
      saturn == planet_ptr_148(LitMap, 5) &&
      uranus == planet_ptr_148(LitMap, 6) &&
      neptune == planet_ptr_148(LitMap, 7) &&
      planet1 == planet1@pre &&
      planet2 == planet2@pre &&
      out != 0 &&
      data != 0 &&
      valid_string(p1) &&
      valid_string(p2) &&
      string_length(p1) < INT_MAX &&
      string_length(p2) < INT_MAX &&
      planet_payloads_string_safe_148 &&
      store_string(planet1@pre, p1) *
      store_string(planet2@pre, p2) *
      planet_literals_heap_148(LitMap) *
      undef_data_at(&cmp) *
      data_at(&(out -> data), data) *
      undef_data_at(&(out -> size)) *
      PtrArray::undef_full(data, 6)
    */
    for (m = 0; m < 8; m++) {
        /*@ Assert
          0 <= m && m < 8 &&
          -1 <= pos1 && pos1 <= 7 &&
          -1 <= pos2 && pos2 <= 7 &&
          planet_scan_state_148(p1, m, pos1) &&
          planet_scan_state_148(p2, m, pos2) &&
          out_size == 0 &&
          lo == -1 &&
          hi == -1 &&
          cur == cur &&
          mercury == planet_ptr_148(LitMap, 0) &&
          venus == planet_ptr_148(LitMap, 1) &&
          earth == planet_ptr_148(LitMap, 2) &&
          mars == planet_ptr_148(LitMap, 3) &&
          jupiter == planet_ptr_148(LitMap, 4) &&
          saturn == planet_ptr_148(LitMap, 5) &&
          uranus == planet_ptr_148(LitMap, 6) &&
          neptune == planet_ptr_148(LitMap, 7) &&
          planet1 == planet1@pre &&
          planet2 == planet2@pre &&
          out != 0 &&
          data != 0 &&
          valid_string(p1) &&
          valid_string(p2) &&
          string_length(p1) < INT_MAX &&
          string_length(p2) < INT_MAX &&
          planet_payloads_string_safe_148 &&
          store_string(planet1@pre, p1) *
          store_string(planet2@pre, p2) *
          store_string(mercury, planet_payload_148(0)) *
          store_string(venus, planet_payload_148(1)) *
          store_string(earth, planet_payload_148(2)) *
          store_string(mars, planet_payload_148(3)) *
          store_string(jupiter, planet_payload_148(4)) *
          store_string(saturn, planet_payload_148(5)) *
          store_string(uranus, planet_payload_148(6)) *
          store_string(neptune, planet_payload_148(7)) *
          GlobalStrings_missing(LitMap, all_planet_literals_148) *
          undef_data_at(&cmp) *
          data_at(&(out -> data), data) *
          undef_data_at(&(out -> size)) *
          PtrArray::undef_full(data, 6)
        */
        if (m == 0) {
            cmp = strcmp(mercury, planet1) /*@ where str1 = planet_payload_148(0), str2 = p1 */;
            if (cmp == 0) pos1 = m;
            cmp = strcmp(mercury, planet2) /*@ where str1 = planet_payload_148(0), str2 = p2 */;
            if (cmp == 0) pos2 = m;
        } else if (m == 1) {
            cmp = strcmp(venus, planet1) /*@ where str1 = planet_payload_148(1), str2 = p1 */;
            if (cmp == 0) pos1 = m;
            cmp = strcmp(venus, planet2) /*@ where str1 = planet_payload_148(1), str2 = p2 */;
            if (cmp == 0) pos2 = m;
        } else if (m == 2) {
            cmp = strcmp(earth, planet1) /*@ where str1 = planet_payload_148(2), str2 = p1 */;
            if (cmp == 0) pos1 = m;
            cmp = strcmp(earth, planet2) /*@ where str1 = planet_payload_148(2), str2 = p2 */;
            if (cmp == 0) pos2 = m;
        } else if (m == 3) {
            cmp = strcmp(mars, planet1) /*@ where str1 = planet_payload_148(3), str2 = p1 */;
            if (cmp == 0) pos1 = m;
            cmp = strcmp(mars, planet2) /*@ where str1 = planet_payload_148(3), str2 = p2 */;
            if (cmp == 0) pos2 = m;
        } else if (m == 4) {
            cmp = strcmp(jupiter, planet1) /*@ where str1 = planet_payload_148(4), str2 = p1 */;
            if (cmp == 0) pos1 = m;
            cmp = strcmp(jupiter, planet2) /*@ where str1 = planet_payload_148(4), str2 = p2 */;
            if (cmp == 0) pos2 = m;
        } else if (m == 5) {
            cmp = strcmp(saturn, planet1) /*@ where str1 = planet_payload_148(5), str2 = p1 */;
            if (cmp == 0) pos1 = m;
            cmp = strcmp(saturn, planet2) /*@ where str1 = planet_payload_148(5), str2 = p2 */;
            if (cmp == 0) pos2 = m;
        } else if (m == 6) {
            cmp = strcmp(uranus, planet1) /*@ where str1 = planet_payload_148(6), str2 = p1 */;
            if (cmp == 0) pos1 = m;
            cmp = strcmp(uranus, planet2) /*@ where str1 = planet_payload_148(6), str2 = p2 */;
            if (cmp == 0) pos2 = m;
        } else {
            cmp = strcmp(neptune, planet1) /*@ where str1 = planet_payload_148(7), str2 = p1 */;
            if (cmp == 0) pos1 = m;
            cmp = strcmp(neptune, planet2) /*@ where str1 = planet_payload_148(7), str2 = p2 */;
            if (cmp == 0) pos2 = m;
        }
        /*@ Assert
          0 <= m && m < 8 &&
          -1 <= pos1 && pos1 <= 7 &&
          -1 <= pos2 && pos2 <= 7 &&
          planet_scan_state_148(p1, m + 1, pos1) &&
          planet_scan_state_148(p2, m + 1, pos2) &&
          out_size == 0 &&
          lo == -1 &&
          hi == -1 &&
          cur == cur &&
          mercury == planet_ptr_148(LitMap, 0) &&
          venus == planet_ptr_148(LitMap, 1) &&
          earth == planet_ptr_148(LitMap, 2) &&
          mars == planet_ptr_148(LitMap, 3) &&
          jupiter == planet_ptr_148(LitMap, 4) &&
          saturn == planet_ptr_148(LitMap, 5) &&
          uranus == planet_ptr_148(LitMap, 6) &&
          neptune == planet_ptr_148(LitMap, 7) &&
          planet1 == planet1@pre &&
          planet2 == planet2@pre &&
          out != 0 &&
          data != 0 &&
          valid_string(p1) &&
          valid_string(p2) &&
          string_length(p1) < INT_MAX &&
          string_length(p2) < INT_MAX &&
          planet_payloads_string_safe_148 &&
          store_string(planet1@pre, p1) *
          store_string(planet2@pre, p2) *
          planet_literals_heap_148(LitMap) *
          undef_data_at(&cmp) *
          data_at(&(out -> data), data) *
          undef_data_at(&(out -> size)) *
          PtrArray::undef_full(data, 6)
        */
    }

    if (pos1 == -1 || pos2 == -1) {
        out->size = 0;
        return out;
    }

    lo = pos1;
    hi = pos2;
    if (lo > hi) {
        int tmp = lo;
        lo = hi;
        hi = tmp;
    }

    /*@ Inv Assert
      exists output_rows output_ptrs,
      lo <= m && m <= hi + 1 &&
      lo < m &&
      0 <= lo && lo <= 7 &&
      0 <= hi && hi <= 7 &&
      pos1 == planet_index_z_148(p1) &&
      pos2 == planet_index_z_148(p2) &&
      lo == planet_min_index_148(planet_index_z_148(p1), planet_index_z_148(p2)) &&
      hi == planet_max_index_148(planet_index_z_148(p1), planet_index_z_148(p2)) &&
      0 <= out_size && out_size <= 6 &&
      out_size == Zlength(output_ptrs) &&
      output_state_148(LitMap, lo, hi, m - 1, output_rows, output_ptrs) &&
      cur == cur &&
      mercury == planet_ptr_148(LitMap, 0) &&
      venus == planet_ptr_148(LitMap, 1) &&
      earth == planet_ptr_148(LitMap, 2) &&
      mars == planet_ptr_148(LitMap, 3) &&
      jupiter == planet_ptr_148(LitMap, 4) &&
      saturn == planet_ptr_148(LitMap, 5) &&
      uranus == planet_ptr_148(LitMap, 6) &&
      neptune == planet_ptr_148(LitMap, 7) &&
      planet1 == planet1@pre &&
      planet2 == planet2@pre &&
      out != 0 &&
      data != 0 &&
      valid_string(p1) &&
      valid_string(p2) &&
      string_length(p1) < INT_MAX &&
      string_length(p2) < INT_MAX &&
      planet_payloads_string_safe_148 &&
      store_string(planet1@pre, p1) *
      store_string(planet2@pre, p2) *
      planet_literals_heap_148(LitMap) *
      undef_data_at(&cmp) *
      data_at(&(out -> data), data) *
      undef_data_at(&(out -> size)) *
      PtrArray::seg(data, 0, out_size, output_ptrs) *
      PtrArray::undef_seg(data, out_size, 6)
    */
    for (m = lo + 1; m < hi; m++) {
        cur = venus;
        if (m == 2) cur = earth;
        if (m == 3) cur = mars;
        if (m == 4) cur = jupiter;
        if (m == 5) cur = saturn;
        if (m == 6) cur = uranus;
        /*@ Assert
          exists output_rows output_ptrs,
          lo <= m && m < hi &&
          lo < m &&
          0 <= lo && lo <= 7 &&
          0 <= hi && hi <= 7 &&
          pos1 == planet_index_z_148(p1) &&
          pos2 == planet_index_z_148(p2) &&
          lo == planet_min_index_148(planet_index_z_148(p1), planet_index_z_148(p2)) &&
          hi == planet_max_index_148(planet_index_z_148(p1), planet_index_z_148(p2)) &&
          0 <= out_size && out_size < 6 &&
          out_size == Zlength(output_ptrs) &&
          cur == planet_ptr_148(LitMap, m) &&
          output_state_148(LitMap, lo, hi, m - 1, output_rows, output_ptrs) &&
          mercury == planet_ptr_148(LitMap, 0) &&
          venus == planet_ptr_148(LitMap, 1) &&
          earth == planet_ptr_148(LitMap, 2) &&
          mars == planet_ptr_148(LitMap, 3) &&
          jupiter == planet_ptr_148(LitMap, 4) &&
          saturn == planet_ptr_148(LitMap, 5) &&
          uranus == planet_ptr_148(LitMap, 6) &&
          neptune == planet_ptr_148(LitMap, 7) &&
          planet1 == planet1@pre &&
          planet2 == planet2@pre &&
          out != 0 &&
          data != 0 &&
          valid_string(p1) &&
          valid_string(p2) &&
          string_length(p1) < INT_MAX &&
          string_length(p2) < INT_MAX &&
          planet_payloads_string_safe_148 &&
          store_string(planet1@pre, p1) *
          store_string(planet2@pre, p2) *
          planet_literals_heap_148(LitMap) *
          undef_data_at(&cmp) *
          data_at(&(out -> data), data) *
          undef_data_at(&(out -> size)) *
          PtrArray::seg(data, 0, out_size, output_ptrs) *
          PtrArray::undef_seg(data, out_size, 6)
        */
        data[out_size] = cur;
        out_size++;
        /*@ Assert
          exists output_rows output_ptrs,
          lo <= m && m < hi &&
          lo < m &&
          0 <= lo && lo <= 7 &&
          0 <= hi && hi <= 7 &&
          pos1 == planet_index_z_148(p1) &&
          pos2 == planet_index_z_148(p2) &&
          lo == planet_min_index_148(planet_index_z_148(p1), planet_index_z_148(p2)) &&
          hi == planet_max_index_148(planet_index_z_148(p1), planet_index_z_148(p2)) &&
          0 <= out_size && out_size <= 6 &&
          out_size == Zlength(output_ptrs) &&
          output_state_148(LitMap, lo, hi, m, output_rows, output_ptrs) &&
          cur == planet_ptr_148(LitMap, m) &&
          mercury == planet_ptr_148(LitMap, 0) &&
          venus == planet_ptr_148(LitMap, 1) &&
          earth == planet_ptr_148(LitMap, 2) &&
          mars == planet_ptr_148(LitMap, 3) &&
          jupiter == planet_ptr_148(LitMap, 4) &&
          saturn == planet_ptr_148(LitMap, 5) &&
          uranus == planet_ptr_148(LitMap, 6) &&
          neptune == planet_ptr_148(LitMap, 7) &&
          planet1 == planet1@pre &&
          planet2 == planet2@pre &&
          out != 0 &&
          data != 0 &&
          valid_string(p1) &&
          valid_string(p2) &&
          string_length(p1) < INT_MAX &&
          string_length(p2) < INT_MAX &&
          planet_payloads_string_safe_148 &&
          store_string(planet1@pre, p1) *
          store_string(planet2@pre, p2) *
          planet_literals_heap_148(LitMap) *
          undef_data_at(&cmp) *
          data_at(&(out -> data), data) *
          undef_data_at(&(out -> size)) *
          PtrArray::seg(data, 0, out_size, output_ptrs) *
          PtrArray::undef_seg(data, out_size, 6)
        */
    }
    out->size = out_size;
    return out;
}
