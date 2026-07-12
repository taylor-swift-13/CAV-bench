/*
You are given a 2 dimensional data, as a nested vectors,
which is similar to matrix, however, unlike matrices,
each row may contain a different number of columns.
Given lst, && integer x, find integers x in the vector,
&& return vector of vectors, {{x1, y1}, {x2, y2} ...} such that
each vector is a coordinate - {row, columns}, starting with 0.
Sort coordinates initially by rows in ascending order.
Also, sort coordinates of the row by columns in descending order.

Examples:
get_row({
  {1,2,3,4,5,6},
  {1,2,3,4,1,6},
  {1,2,3,4,5,1}
}, 1) == {{0, 0}, {1, 4}, {1, 0}, {2, 5}, {2, 0}}
get_row({}, 1) == {}
get_row({{}, {1}, {1, 2, 3}}, 3) == {{2, 2}}
*/
#include "int_ptr_array2_def.h"

/*@ Extern Coq (problem_87_pre_z: list (list Z) -> Z -> Prop)
               (problem_87_spec_z: list (list Z) -> Z -> list Z -> Prop)
               (row_sizes_match_87: list (list Z) -> list Z -> Prop)
               (total_cells_prefix_87: list (list Z) -> Z -> Z)
               (prefix_state_87: list (list Z) -> Z -> Z -> list Z -> Prop)
               (scan_state_87: list (list Z) -> Z -> Z -> Z -> list Z -> Prop)
               (Znth: {A} -> Z -> list A -> A -> A)
               (Zlength: {A} -> list A -> Z)
*/
/*@ Import Coq Require Import p087_get_row */

typedef struct {
  int* data;
  int size;
} IntArray;

IntArray *malloc_int_array_struct()
/*@ Require emp
    Ensure __return != 0 &&
           undef_data_at(&(__return -> data)) *
           undef_data_at(&(__return -> size))
*/;

int *malloc_int_array(int size)
/*@ Require size >= 0 && size < INT_MAX
    Ensure __return != 0 && IntArray::undef_full(__return, size)
*/;

IntArray *get_row(int** lst, int* row_sizes, int rows, int x)
/*@ With matrix sizes
    Require
      0 <= rows && rows <= 100 &&
      Zlength(matrix) == rows &&
      Zlength(sizes) == rows &&
      row_sizes_match_87(matrix, sizes) &&
      problem_87_pre_z(matrix, x) &&
      0 <= total_cells_prefix_87(matrix, rows) &&
      total_cells_prefix_87(matrix, rows) * 2 + 2 < INT_MAX &&
      (forall (r: Z), (0 <= r && r < rows) => (0 <= sizes[r] && sizes[r] <= 100)) &&
      (forall (r: Z) (c: Z), (0 <= r && r < rows && 0 <= c && c < sizes[r]) =>
        (INT_MIN <= matrix[r][c] && matrix[r][c] <= INT_MAX)) &&
      IntPtrArray2::full(lst, rows, matrix) *
      IntArray::full(row_sizes, rows, sizes)
    Ensure exists data output_l output_size total,
      __return != 0 &&
      total == total_cells_prefix_87(matrix, rows) &&
      output_size * 2 == Zlength(output_l) &&
      0 <= output_size && output_size <= total + 1 &&
      problem_87_spec_z(matrix, x, output_l) &&
      data_at(&(__return -> data), data) *
      data_at(&(__return -> size), output_size) *
      IntPtrArray2::full(lst, rows, matrix) *
      IntArray::full(row_sizes, rows, sizes) *
      IntArray::seg(data, 0, output_size * 2, output_l) *
      IntArray::undef_seg(data, output_size * 2, total * 2 + 2)
*/
{
  int total = 0;

  for (int i = 0; i < rows; i++) {
    total += row_sizes[i];
  }

  IntArray *out = malloc_int_array_struct();
  out->size = 0;
  out->data = malloc_int_array(total * 2 + 2);
  int *data = out->data;
  int output_size = 0;
  int out_len = 0;

  for (int i = 0; i < rows; i++) {

    for (int j = row_sizes[i] - 1; j >= 0; j -= 1) {
      if (lst[i][j] == x) {

        data[out_len] = i;
        data[out_len + 1] = j;
        out_len += 2;
        output_size += 1;
      }
    }

  }
  out->size = output_size;
  return out;
}
