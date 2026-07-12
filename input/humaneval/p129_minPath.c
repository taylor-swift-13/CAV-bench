/*
Given a grid with N rows && N columns (N >= 2) && a positive integer k,
each cell of the grid contains a value. Every integer in the range {1, N * N}
inclusive appears exactly once on the cells of the grid.

You have to find the minimum path of length k in the grid. You can start
from any cell, && in each step you can move to any of the neighbor cells,
in other words, you can go to cells which share an edge with you current
cell.
Please note that a path of length k means visiting exactly k cells (!
necessarily distinct).
You CANNOT go off the grid.
A path A (of length k) is considered less than a path B (of length k) if
after making the ordered vectors of the values on the cells that A && B go
through (let's call them lst_A && lst_B), lst_A is lexicographically less
than lst_B, in other words, there exist an integer index i (1 <= i <= k)
such that lst_A[i] < lst_B[i] && for any j (1 <= j < i) we have
lst_A[j] = lst_B[j].
It is guaranteed that the answer is unique.
Return an ordered vector of the values on the cells that the minimum path go through.

Examples:

    Input: grid = { {1,2,3}, {4,5,6}, {7,8,9}}, k = 3
    Output: {1, 2, 1}

    Input: grid = { {5,9,3}, {4,1,6}, {7,8,2}}, k = 1
    Output: {1}
*/
#include "int_ptr_array2_def.h"

/*@ Extern Coq (problem_129_pre_z: list (list Z) -> Z -> Prop)
               (problem_129_spec_z: list (list Z) -> Z -> list Z -> Prop)
               (one_pos_z_129: list (list Z) -> Z -> Z -> Prop)
               (find_one_scan_state_129: list (list Z) -> Z -> Z -> Z -> Z -> Z -> Prop)
               (find_one_state_129: list (list Z) -> Z -> Z -> Z -> Z -> Z -> Prop)
               (checked_neighbor_min_129: list (list Z) -> Z -> Z -> Z -> Z -> Z -> Prop)
               (min_neighbor_state_129: list (list Z) -> Z -> Z -> Z -> Z -> Prop)
               (output_prefix_129: Z -> Z -> Z -> list Z -> Prop)
               (output_value_129: Z -> Z -> Z)
               (Znth: {A} -> Z -> list A -> A -> A)
               (Zlength: {A} -> list A -> Z)
*/
/*@ Import Coq Require Import p129_minPath */

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

IntArray *minPath(int** grid, int n, int k)
/*@ With rows one_x one_y
    Require
        2 <= n && n <= 100 &&
        1 <= k && k < INT_MAX &&
        n * n < INT_MAX &&
        Zlength(rows) == n &&
        problem_129_pre_z(rows, k) &&
        (forall (r: Z), (0 <= r && r < n) => (Zlength(rows[r]) == n)) &&
        (forall (r: Z) (c: Z), (0 <= r && r < n && 0 <= c && c < n) =>
            (1 <= rows[r][c] && rows[r][c] <= n * n)) &&
        0 <= one_x && one_x < n &&
        0 <= one_y && one_y < n &&
        rows[one_x][one_y] == 1 &&
        IntPtrArray2::full(grid, n, rows)
    Ensure
        exists data output_l minv,
        __return != 0 &&
        1 <= minv && minv <= n * n &&
        problem_129_spec_z(rows, k, output_l) &&
        data_at(&(__return -> data), data) *
        data_at(&(__return -> size), k) *
        IntPtrArray2::full(grid, n, rows) *
        IntArray::full(data, k, output_l)
*/
{
    int x, y;
    IntArray *out = malloc_int_array_struct();
    out->size = k;
    out->data = malloc_int_array(k);
    int *data = out->data;
    x = 0;
    y = 0;

    for (int i = 0; i < n; i++) {

        for (int j = 0; j < n; j++) {
            if (grid[i][j] == 1) {
                x = i;
                y = j;
            }
        }

    }

    int min = n * n;

    if (x > 0) {

        if (grid[x - 1][y] < min) min = grid[x - 1][y];

    }
    if (x < n - 1) {

        if (grid[x + 1][y] < min) min = grid[x + 1][y];

    }
    if (y > 0) {

        if (grid[x][y - 1] < min) min = grid[x][y - 1];

    }
    if (y < n - 1) {

        if (grid[x][y + 1] < min) min = grid[x][y + 1];

    }

    int t = 0;

    while (t < k) {
        if (t % 2 == 0) data[t] = 1;
        else data[t] = min;
        t++;
    }
    return out;
}
