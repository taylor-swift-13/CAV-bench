/*
Given a vector of integers, sort the integers that are between 1 && 9 inclusive,
reverse the resulting vector, && then replace each digit by its corresponding name from
"One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine".

For example:
  arr = {2, 1, 1, 4, 5, 8, 2, 3}
        -> sort arr -> {1, 1, 2, 2, 3, 4, 5, 8}
        -> reverse arr -> {8, 5, 4, 3, 2, 2, 1, 1}
  return {"Eight", "Five", "Four", "Three", "Two", "Two", "One", "One"}

  If the vector is empty, return an empty vector:
  arr = {}
  return {}

  If the vector has any strange number ignore it:
  arr = {1, -1 , 55}
        -> sort arr -> {-1, 1, 55}
        -> reverse arr -> {55, 1, -1}
  return = {"One"}
*/
#include "ptr_array2_def.h"
#include "int_array_def.h"
#include "string.h"

/*@ Extern Coq (problem_105_pre_z: list Z -> Prop)
               (problem_105_spec_z: list Z -> list (list Z) -> Prop)
               (copy_prefix_105: list Z -> Z -> list Z)
               (sorted_int_list_by: Z -> list Z -> Prop)
               (Permutation: list Z -> list Z -> Prop)
               (int_range_list_105: list Z -> Prop)
               (digit_payload_105: Z -> list Z)
               (digit_literal_105: Z -> String)
               (digit_ptr_105: (String -> Z) -> Z -> Z)
               (digit_words_between_105: list Z -> Z -> Z -> list (list Z))
               (digit_ptrs_between_105: (String -> Z) -> list Z -> Z -> Z -> list Z)
               (output_state_105: (String -> Z) -> list Z -> Z -> list (list Z) -> list Z -> Prop)
               (digit_payloads_string_safe_105: Prop)
               (digit_literals_heap_105: (String -> Z) -> Assertion)
               (problem_105_spec_z_of_output_state: list Z -> list Z -> list (list Z) -> (String -> Z) -> list Z -> Prop)
               (LitMap: String -> Z)
               (Zlength: {A} -> list A -> Z)
*/
/*@ Import Coq Require Import p105_by_length */

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

int *malloc_int_array(int size)
/*@ Require size >= 0 && size < INT_MAX
    Ensure __return != 0 && IntArray::undef_full(__return, size)
*/;

void free_int_array(int *array, int size)
/*@ Require
      exists l,
      array != 0 &&
      0 <= size && size < INT_MAX &&
      size == Zlength(l) &&
      IntArray::full(array, size, l)
    Ensure emp
*/;

void sort_int_array(int *array, int init_size, int size, int ascending)
/*@ With l
    Require
      array != 0 &&
      init_size == Zlength(l) &&
      0 <= init_size && init_size <= size &&
      0 <= size && size < INT_MAX &&
      IntArray::seg(array, 0, init_size, l) *
      IntArray::undef_seg(array, init_size, size)
    Ensure
      exists sorted_l sorted_full_l,
      init_size == Zlength(sorted_l) &&
      size == Zlength(sorted_full_l) &&
      0 <= init_size && init_size <= size &&
      0 <= size && size < INT_MAX &&
      sublist(0, init_size, sorted_full_l) == sorted_l &&
      sorted_int_list_by(ascending, sorted_l) &&
      Permutation(l, sorted_l) &&
      IntArray::full(array, size, sorted_full_l)
*/;

StrArray *by_length(int *arr, int arr_size)
/*@ With input_l
    Require
      arr != 0 &&
      0 <= arr_size && arr_size < INT_MAX &&
      arr_size == Zlength(input_l) &&
      problem_105_pre_z(input_l) &&
      IntArray::full(arr, arr_size, input_l) *
      GlobalStrings(LitMap)
    Ensure exists data output_rows output_ptrs output_size,
      __return != 0 &&
      data != 0 &&
      0 <= output_size && output_size <= arr_size &&
      output_size == Zlength(output_rows) &&
      output_size == Zlength(output_ptrs) &&
      problem_105_spec_z(input_l, output_rows) &&
      data_at(&(__return -> data), data) *
      data_at(&(__return -> size), output_size) *
      IntArray::full(arr, arr_size, input_l) *
      PtrArray::seg(data, 0, output_size, output_ptrs) *
      PtrArray::undef_seg(data, output_size, arr_size) *
      digit_literals_heap_105(LitMap)
*/
{
  char *one = "One";
  char *two = "Two";
  char *three = "Three";
  char *four = "Four";
  char *five = "Five";
  char *six = "Six";
  char *seven = "Seven";
  char *eight = "Eight";
  char *nine = "Nine";
  /*@ Assert
      one == digit_ptr_105(LitMap, 1) &&
      two == digit_ptr_105(LitMap, 2) &&
      three == digit_ptr_105(LitMap, 3) &&
      four == digit_ptr_105(LitMap, 4) &&
      five == digit_ptr_105(LitMap, 5) &&
      six == digit_ptr_105(LitMap, 6) &&
      seven == digit_ptr_105(LitMap, 7) &&
      eight == digit_ptr_105(LitMap, 8) &&
      nine == digit_ptr_105(LitMap, 9) &&
      arr == arr@pre &&
      arr_size == arr_size@pre &&
      arr != 0 &&
      0 <= arr_size && arr_size < INT_MAX &&
      arr_size == Zlength(input_l) &&
      problem_105_pre_z(input_l) &&
      digit_payloads_string_safe_105 &&
      IntArray::full(arr@pre, arr_size@pre, input_l) *
      digit_literals_heap_105(LitMap)
  */
  StrArray *out = malloc_str_array_struct();
  out->size = 0;
  out->data = malloc_char_ptr_array(arr_size);
  char **data = out->data;
  int *tmp = malloc_int_array(arr_size);
  int out_size = 0;
  int i;

  /*@ Inv Assert
      exists tmp_l,
      one == digit_ptr_105(LitMap, 1) &&
      two == digit_ptr_105(LitMap, 2) &&
      three == digit_ptr_105(LitMap, 3) &&
      four == digit_ptr_105(LitMap, 4) &&
      five == digit_ptr_105(LitMap, 5) &&
      six == digit_ptr_105(LitMap, 6) &&
      seven == digit_ptr_105(LitMap, 7) &&
      eight == digit_ptr_105(LitMap, 8) &&
      nine == digit_ptr_105(LitMap, 9) &&
      arr == arr@pre &&
      arr_size == arr_size@pre &&
      out != 0 &&
      data != 0 &&
      tmp != 0 &&
      out_size == 0 &&
      arr != 0 &&
      0 <= arr_size && arr_size < INT_MAX &&
      arr_size == Zlength(input_l) &&
      problem_105_pre_z(input_l) &&
      digit_payloads_string_safe_105 &&
      0 <= i && i <= arr_size &&
      i == Zlength(tmp_l) &&
      tmp_l == copy_prefix_105(input_l, i) &&
      IntArray::full(arr@pre, arr_size@pre, input_l) *
      data_at(&(out -> data), data) *
      data_at(&(out -> size), 0) *
      PtrArray::undef_full(data, arr_size) *
      IntArray::seg(tmp, 0, i, tmp_l) *
      IntArray::undef_seg(tmp, i, arr_size) *
      digit_literals_heap_105(LitMap)
  */
  for (i = 0; i < arr_size; i++) {
    tmp[i] = arr[i];
  }

  /*@ Assert
      one == digit_ptr_105(LitMap, 1) &&
      two == digit_ptr_105(LitMap, 2) &&
      three == digit_ptr_105(LitMap, 3) &&
      four == digit_ptr_105(LitMap, 4) &&
      five == digit_ptr_105(LitMap, 5) &&
      six == digit_ptr_105(LitMap, 6) &&
      seven == digit_ptr_105(LitMap, 7) &&
      eight == digit_ptr_105(LitMap, 8) &&
      nine == digit_ptr_105(LitMap, 9) &&
      arr == arr@pre &&
      arr_size == arr_size@pre &&
      out != 0 &&
      data != 0 &&
      tmp != 0 &&
      out_size == 0 &&
      arr != 0 &&
      0 <= arr_size && arr_size < INT_MAX &&
      arr_size == Zlength(input_l) &&
      problem_105_pre_z(input_l) &&
      digit_payloads_string_safe_105 &&
      IntArray::full(arr@pre, arr_size@pre, input_l) *
      data_at(&i, arr_size) *
      data_at(&(out -> data), data) *
      data_at(&(out -> size), 0) *
      PtrArray::undef_full(data, arr_size) *
      IntArray::seg(tmp, 0, arr_size, input_l) *
      IntArray::undef_seg(tmp, arr_size, arr_size) *
      digit_literals_heap_105(LitMap)
  */
  sort_int_array(tmp, arr_size, arr_size, 1);

  /*@ Assert
      exists sorted_l,
      one == digit_ptr_105(LitMap, 1) &&
      two == digit_ptr_105(LitMap, 2) &&
      three == digit_ptr_105(LitMap, 3) &&
      four == digit_ptr_105(LitMap, 4) &&
      five == digit_ptr_105(LitMap, 5) &&
      six == digit_ptr_105(LitMap, 6) &&
      seven == digit_ptr_105(LitMap, 7) &&
      eight == digit_ptr_105(LitMap, 8) &&
      nine == digit_ptr_105(LitMap, 9) &&
      arr == arr@pre &&
      arr_size == arr_size@pre &&
      out != 0 &&
      data != 0 &&
      tmp != 0 &&
      out_size == 0 &&
      arr != 0 &&
      0 <= arr_size && arr_size < INT_MAX &&
      arr_size == Zlength(input_l) &&
      arr_size == Zlength(sorted_l) &&
      problem_105_pre_z(input_l) &&
      sorted_int_list_by(1, sorted_l) &&
      Permutation(input_l, sorted_l) &&
      int_range_list_105(sorted_l) &&
      digit_payloads_string_safe_105 &&
      IntArray::full(arr@pre, arr_size@pre, input_l) *
      data_at(&i, arr_size) *
      data_at(&(out -> data), data) *
      data_at(&(out -> size), 0) *
      PtrArray::undef_full(data, arr_size) *
      IntArray::full(tmp, arr_size, sorted_l) *
      digit_literals_heap_105(LitMap)
  */

  int d = 0;
  /*@ Inv Assert
      exists sorted_l output_rows output_ptrs,
      one == digit_ptr_105(LitMap, 1) &&
      two == digit_ptr_105(LitMap, 2) &&
      three == digit_ptr_105(LitMap, 3) &&
      four == digit_ptr_105(LitMap, 4) &&
      five == digit_ptr_105(LitMap, 5) &&
      six == digit_ptr_105(LitMap, 6) &&
      seven == digit_ptr_105(LitMap, 7) &&
      eight == digit_ptr_105(LitMap, 8) &&
      nine == digit_ptr_105(LitMap, 9) &&
      arr == arr@pre &&
      arr_size == arr_size@pre &&
      out != 0 &&
      data != 0 &&
      tmp != 0 &&
      arr != 0 &&
      0 <= arr_size && arr_size < INT_MAX &&
      arr_size == Zlength(input_l) &&
      arr_size == Zlength(sorted_l) &&
      problem_105_pre_z(input_l) &&
      sorted_int_list_by(1, sorted_l) &&
      Permutation(input_l, sorted_l) &&
      int_range_list_105(sorted_l) &&
      digit_payloads_string_safe_105 &&
      d == d &&
      i == i &&
      0 <= k && k <= arr_size &&
      output_state_105(LitMap, sorted_l, k, output_rows, output_ptrs) &&
      out_size == Zlength(output_rows) &&
      out_size == Zlength(output_ptrs) &&
      0 <= out_size && out_size <= k &&
      output_ptrs == digit_ptrs_between_105(LitMap, sorted_l, arr_size - k, arr_size) &&
      IntArray::full(arr@pre, arr_size@pre, input_l) *
      data_at(&(out -> data), data) *
      data_at(&(out -> size), out_size) *
      PtrArray::seg(data, 0, Zlength(output_ptrs), output_ptrs) *
      PtrArray::undef_seg(data, Zlength(output_ptrs), arr_size) *
      IntArray::full(tmp, arr_size, sorted_l) *
      digit_literals_heap_105(LitMap)
  */
  for (int k = 0; k < arr_size; k++) {
    i = arr_size - 1 - k;
    /*@ Assert
        exists sorted_l output_rows output_ptrs,
        one == digit_ptr_105(LitMap, 1) &&
        two == digit_ptr_105(LitMap, 2) &&
        three == digit_ptr_105(LitMap, 3) &&
        four == digit_ptr_105(LitMap, 4) &&
        five == digit_ptr_105(LitMap, 5) &&
        six == digit_ptr_105(LitMap, 6) &&
        seven == digit_ptr_105(LitMap, 7) &&
        eight == digit_ptr_105(LitMap, 8) &&
        nine == digit_ptr_105(LitMap, 9) &&
        arr == arr@pre &&
        arr_size == arr_size@pre &&
        out != 0 &&
        data != 0 &&
        tmp != 0 &&
        arr != 0 &&
        0 <= arr_size && arr_size < INT_MAX &&
        arr_size == Zlength(input_l) &&
        arr_size == Zlength(sorted_l) &&
        problem_105_pre_z(input_l) &&
        sorted_int_list_by(1, sorted_l) &&
        Permutation(input_l, sorted_l) &&
        int_range_list_105(sorted_l) &&
        digit_payloads_string_safe_105 &&
        d == d &&
        i == i &&
        0 <= k && k < arr_size &&
        0 <= arr_size - 1 - k && arr_size - 1 - k < arr_size &&
        0 <= i && i < arr_size &&
        i == arr_size - 1 - k &&
        INT_MIN <= Znth(arr_size - 1 - k, sorted_l, 0) &&
        Znth(arr_size - 1 - k, sorted_l, 0) <= INT_MAX &&
        output_state_105(LitMap, sorted_l, k, output_rows, output_ptrs) &&
        out_size == Zlength(output_rows) &&
        out_size == Zlength(output_ptrs) &&
        0 <= out_size && out_size <= k &&
        output_ptrs == digit_ptrs_between_105(LitMap, sorted_l, arr_size - k, arr_size) &&
        IntArray::full(arr@pre, arr_size@pre, input_l) *
        data_at(&(out -> data), data) *
        data_at(&(out -> size), out_size) *
        PtrArray::seg(data, 0, Zlength(output_ptrs), output_ptrs) *
        PtrArray::undef_seg(data, Zlength(output_ptrs), arr_size) *
        IntArray::missing_i(tmp, i, 0, arr_size, sorted_l) *
        store(tmp + i * sizeof(int), int, Znth(i, sorted_l, 0)) *
        digit_literals_heap_105(LitMap)
    */
    d = tmp[i];
    /*@ Assert
        exists sorted_l output_rows output_ptrs,
        one == digit_ptr_105(LitMap, 1) &&
        two == digit_ptr_105(LitMap, 2) &&
        three == digit_ptr_105(LitMap, 3) &&
        four == digit_ptr_105(LitMap, 4) &&
        five == digit_ptr_105(LitMap, 5) &&
        six == digit_ptr_105(LitMap, 6) &&
        seven == digit_ptr_105(LitMap, 7) &&
        eight == digit_ptr_105(LitMap, 8) &&
        nine == digit_ptr_105(LitMap, 9) &&
        arr == arr@pre &&
        arr_size == arr_size@pre &&
        out != 0 &&
        data != 0 &&
        tmp != 0 &&
        arr != 0 &&
        0 <= arr_size && arr_size < INT_MAX &&
        arr_size == Zlength(input_l) &&
        arr_size == Zlength(sorted_l) &&
        problem_105_pre_z(input_l) &&
        sorted_int_list_by(1, sorted_l) &&
        Permutation(input_l, sorted_l) &&
        int_range_list_105(sorted_l) &&
        digit_payloads_string_safe_105 &&
        d == d &&
        i == i &&
        0 <= k && k < arr_size &&
        0 <= i && i < arr_size &&
        i == arr_size - 1 - k &&
        INT_MIN <= d && d <= INT_MAX &&
        output_state_105(LitMap, sorted_l, k, output_rows, output_ptrs) &&
        out_size == Zlength(output_rows) &&
        out_size == Zlength(output_ptrs) &&
        0 <= out_size && out_size <= k &&
        output_ptrs == digit_ptrs_between_105(LitMap, sorted_l, arr_size - k, arr_size) &&
        d == Znth(i, sorted_l, 0) &&
        IntArray::full(arr@pre, arr_size@pre, input_l) *
        data_at(&(out -> data), data) *
        data_at(&(out -> size), out_size) *
        PtrArray::seg(data, 0, Zlength(output_ptrs), output_ptrs) *
        PtrArray::undef_seg(data, Zlength(output_ptrs), arr_size) *
        IntArray::full(tmp, arr_size, sorted_l) *
        digit_literals_heap_105(LitMap)
    */
    if (d >= 1 && d <= 9) {
      if (d == 1) {
        data[out_size] = one;
      } else if (d == 2) {
        data[out_size] = two;
      } else if (d == 3) {
        data[out_size] = three;
      } else if (d == 4) {
        data[out_size] = four;
      } else if (d == 5) {
        data[out_size] = five;
      } else if (d == 6) {
        data[out_size] = six;
      } else if (d == 7) {
        data[out_size] = seven;
      } else if (d == 8) {
        data[out_size] = eight;
      } else {
        data[out_size] = nine;
      }
      out_size++;
      out->size = out_size;
    }
    /*@ Assert
        exists sorted_l output_rows output_ptrs,
        one == digit_ptr_105(LitMap, 1) &&
        two == digit_ptr_105(LitMap, 2) &&
        three == digit_ptr_105(LitMap, 3) &&
        four == digit_ptr_105(LitMap, 4) &&
        five == digit_ptr_105(LitMap, 5) &&
        six == digit_ptr_105(LitMap, 6) &&
        seven == digit_ptr_105(LitMap, 7) &&
        eight == digit_ptr_105(LitMap, 8) &&
        nine == digit_ptr_105(LitMap, 9) &&
        arr == arr@pre &&
        arr_size == arr_size@pre &&
        out != 0 &&
        data != 0 &&
        tmp != 0 &&
        arr != 0 &&
        0 <= arr_size && arr_size < INT_MAX &&
        arr_size == Zlength(input_l) &&
        arr_size == Zlength(sorted_l) &&
        problem_105_pre_z(input_l) &&
        sorted_int_list_by(1, sorted_l) &&
        Permutation(input_l, sorted_l) &&
        int_range_list_105(sorted_l) &&
        digit_payloads_string_safe_105 &&
        d == d &&
        i == i &&
        0 <= k && k < arr_size &&
        output_state_105(LitMap, sorted_l, k + 1, output_rows, output_ptrs) &&
        out_size == Zlength(output_rows) &&
        out_size == Zlength(output_ptrs) &&
        0 <= out_size && out_size <= k + 1 &&
        output_ptrs == digit_ptrs_between_105(LitMap, sorted_l, arr_size - (k + 1), arr_size) &&
        IntArray::full(arr@pre, arr_size@pre, input_l) *
        data_at(&(out -> data), data) *
        data_at(&(out -> size), out_size) *
        PtrArray::seg(data, 0, Zlength(output_ptrs), output_ptrs) *
        PtrArray::undef_seg(data, Zlength(output_ptrs), arr_size) *
        IntArray::full(tmp, arr_size, sorted_l) *
        digit_literals_heap_105(LitMap)
    */
  }

  /*@ Assert
      exists sorted_l output_rows output_ptrs,
      one == digit_ptr_105(LitMap, 1) &&
      two == digit_ptr_105(LitMap, 2) &&
      three == digit_ptr_105(LitMap, 3) &&
      four == digit_ptr_105(LitMap, 4) &&
      five == digit_ptr_105(LitMap, 5) &&
      six == digit_ptr_105(LitMap, 6) &&
      seven == digit_ptr_105(LitMap, 7) &&
      eight == digit_ptr_105(LitMap, 8) &&
      nine == digit_ptr_105(LitMap, 9) &&
      arr == arr@pre &&
      arr_size == arr_size@pre &&
      out != 0 &&
      data != 0 &&
      tmp != 0 &&
      arr != 0 &&
      0 <= arr_size && arr_size < INT_MAX &&
      arr_size == Zlength(input_l) &&
      arr_size == Zlength(sorted_l) &&
      problem_105_pre_z(input_l) &&
      sorted_int_list_by(1, sorted_l) &&
      Permutation(input_l, sorted_l) &&
      int_range_list_105(sorted_l) &&
      d == d &&
      i == i &&
      output_state_105(LitMap, sorted_l, arr_size, output_rows, output_ptrs) &&
      problem_105_spec_z_of_output_state(input_l, sorted_l, output_rows, LitMap, output_ptrs) &&
      out_size == Zlength(output_rows) &&
      out_size == Zlength(output_ptrs) &&
      0 <= out_size && out_size <= arr_size &&
      IntArray::full(arr@pre, arr_size@pre, input_l) *
      data_at(&(out -> data), data) *
      data_at(&(out -> size), out_size) *
      PtrArray::seg(data, 0, Zlength(output_ptrs), output_ptrs) *
      PtrArray::undef_seg(data, Zlength(output_ptrs), arr_size) *
      IntArray::full(tmp, arr_size, sorted_l) *
      digit_literals_heap_105(LitMap)
  */
  free_int_array(tmp, arr_size);
  /*@ Assert
      exists sorted_l output_rows output_ptrs,
      one == digit_ptr_105(LitMap, 1) &&
      two == digit_ptr_105(LitMap, 2) &&
      three == digit_ptr_105(LitMap, 3) &&
      four == digit_ptr_105(LitMap, 4) &&
      five == digit_ptr_105(LitMap, 5) &&
      six == digit_ptr_105(LitMap, 6) &&
      seven == digit_ptr_105(LitMap, 7) &&
      eight == digit_ptr_105(LitMap, 8) &&
      nine == digit_ptr_105(LitMap, 9) &&
      arr == arr@pre &&
      arr_size == arr_size@pre &&
      out != 0 &&
      data != 0 &&
      tmp == tmp &&
      arr != 0 &&
      0 <= arr_size && arr_size < INT_MAX &&
      arr_size == Zlength(input_l) &&
      arr_size == Zlength(sorted_l) &&
      problem_105_pre_z(input_l) &&
      sorted_int_list_by(1, sorted_l) &&
      Permutation(input_l, sorted_l) &&
      int_range_list_105(sorted_l) &&
      d == d &&
      i == i &&
      output_state_105(LitMap, sorted_l, arr_size, output_rows, output_ptrs) &&
      problem_105_spec_z_of_output_state(input_l, sorted_l, output_rows, LitMap, output_ptrs) &&
      out_size == Zlength(output_rows) &&
      out_size == Zlength(output_ptrs) &&
      0 <= out_size && out_size <= arr_size &&
      IntArray::full(arr@pre, arr_size@pre, input_l) *
      data_at(&(out -> data), data) *
      data_at(&(out -> size), out_size) *
      PtrArray::seg(data, 0, Zlength(output_ptrs), output_ptrs) *
      PtrArray::undef_seg(data, Zlength(output_ptrs), arr_size) *
      digit_literals_heap_105(LitMap)
  */
  return out;
}
