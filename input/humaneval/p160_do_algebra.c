/*
Given two vectors operator, && operand. The first vector has basic algebra operations, &&
the second vector is a vector of integers. Use the two given vectors to build the algebric
expression && return the evaluation of this expression.

The basic algebra operations:
Addition ( + )
Subtraction ( - )
Multiplication ( * )
Floor division ( // )
Exponentiation ( ** )

Example:
operator{"+", "*", "-"}
vector = {2, 3, 4, 5}
result = 2 + 3 * 4 - 5
=> result = 9

Note:
    The length of operator vector is equal to the length of operand vector minus one.
    Operand is a vector of of non-negative integers.
    Operator vector has at least one operator, && operand vector has at least two operands.

*/
#include "ptr_array2_def.h"
#include "int_array_def.h"
#include "string.h"

/*@ Extern Coq (problem_160_pre_z: list (list Z) -> list Z -> Prop)
               (problem_160_spec_z: list (list Z) -> list Z -> Z -> Prop)
               (operator_rows_well_formed_160: list (list Z) -> Z -> Prop)
               (operator_payload_valid_160: list Z -> Prop)
               (operator_code_payload_160: list Z -> Z)
               (operator_codes_160: list (list Z) -> list Z)
               (row_payload_z_160: list Z -> list Z)
               (do_algebra_safe_160: list (list Z) -> list Z -> Prop)
               (eval_range_160: list Z -> list Z -> Z -> Z -> Z)
               (eval_range_safe_160: list Z -> list Z -> Z -> Z -> Prop)
               (find_addsub_prefix_160: list Z -> Z -> Z -> Z)
               (find_muldiv_prefix_160: list Z -> Z -> Z -> Z)
               (find_pow_left_prefix_160: list Z -> Z -> Z -> Z)
               (pow_prefix_safe_160: Z -> Z -> Prop)
               (Zpow_160: Z -> Z -> Z)
               (Zlength: {A} -> list A -> Z)
               (Znth: {A} -> Z -> list A -> A -> A)
*/
/*@ Import Coq Require Import p160_do_algebra */

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

int operator_code(char *op)
/*@ With payload
    Require
      operator_payload_valid_160(payload) &&
      store_string(op, payload)
    Ensure
      __return == operator_code_payload_160(payload) &&
      store_string(op, payload)
*/
{
    if (op[0] == 42) {
        if (op[1] == 42) return 4;
        return 2;
    }
    if (op[0] == 47) return 3;
    if (op[0] == 43) return 0;
    return 1;
}

int int_pow(int base, int exp)
/*@ Require
      0 <= exp && exp < INT_MAX &&
      pow_prefix_safe_160(base, exp) &&
      emp
    Ensure
      __return == Zpow_160(base, exp) &&
      emp
*/
{
    int result = 1;

    for (int i = 0; i < exp; i++) {
        result *= base;
    }
    return result;
}

int eval_range(int *ops, int ops_size, int *nums, int nums_size, int lo, int hi)
/*@ With ops_l nums_l
    Require
      ops_size == Zlength(ops_l) &&
      nums_size == Zlength(nums_l) &&
      ops_size + 1 == nums_size &&
      0 <= lo && lo <= hi && hi < nums_size &&
      eval_range_safe_160(ops_l, nums_l, lo, hi) &&
      IntArray::full(ops, ops_size, ops_l) *
      IntArray::full(nums, nums_size, nums_l)
    Ensure
      __return == eval_range_160(ops_l, nums_l, lo, hi) &&
      IntArray::full(ops, ops_size, ops_l) *
      IntArray::full(nums, nums_size, nums_l)
*/
{
    if (lo == hi) {
        return nums[lo];
    }

    int idx = -1;

    for (int i = lo; i < hi; i++) {
        if (ops[i] == 0 || ops[i] == 1) {
            idx = i;
        }
    }
    if (idx != -1) {
        int left = eval_range(ops, ops_size, nums, nums_size, lo, idx)
          ;
        int right = eval_range(ops, ops_size, nums, nums_size, idx + 1, hi)
          ;
        if (ops[idx] == 0) {
            return left + right;
        } else {
            return left - right;
        }
    }

    idx = -1;

    for (int i = lo; i < hi; i++) {
        if (ops[i] == 2 || ops[i] == 3) {
            idx = i;
        }
    }
    if (idx != -1) {
        int left = eval_range(ops, ops_size, nums, nums_size, lo, idx)
          ;
        int right = eval_range(ops, ops_size, nums, nums_size, idx + 1, hi)
          ;
        if (ops[idx] == 2) {
            return left * right;
        } else {
            return left / right;
        }
    }

    idx = -1;

    for (int i = lo; i < hi; i++) {
        if (idx == -1 && ops[i] == 4) {
            idx = i;
        }
    }
    if (idx != -1) {
        int left = eval_range(ops, ops_size, nums, nums_size, lo, idx)
          ;
        int right = eval_range(ops, ops_size, nums, nums_size, idx + 1, hi)
          ;
        return int_pow(left, right);
    }

    return 0;
}

int do_algebra(char** operato, int operato_size, int* operand, int operand_size)
/*@ With rows operands
    Require
      0 < operato_size && operato_size < INT_MAX &&
      operand_size == operato_size + 1 &&
      operand_size < INT_MAX &&
      operator_rows_well_formed_160(rows, operato_size) &&
      problem_160_pre_z(rows, operands) &&
      do_algebra_safe_160(rows, operands) &&
      CharPtrArray2::full(operato, operato_size, rows) *
      IntArray::full(operand, operand_size, operands)
    Ensure
      problem_160_spec_z(rows, operands, __return) &&
      CharPtrArray2::full(operato, operato_size, rows) *
      IntArray::full(operand, operand_size, operands)
*/
{
    int* ops;
    char* cur_op = 0;

    ops = malloc_int_array(operato_size);
    if (ops == 0) {
        return 0;
    }

    for (int i = 0; i < operato_size; i++) {

        cur_op = operato[i];

        ops[i] = operator_code(cur_op)
          ;
    }

    int ans = eval_range(ops, operato_size, operand, operand_size, 0, operand_size - 1)
      ;

    free_int_array(ops, operato_size);

    return ans;

}
