/*
xs are coefficients of a polynomial. find_zero finds an x such that poly(x) = 0.
The input has a nonempty even number of coefficients and a nonzero leading
coefficient, as required by the HumanEval task.
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "double_array_def.h"

/*@ Extern Coq
      (problem_32_pre_fp64 : list fp64 -> Prop)
      (problem_32_eval_fp64 : list fp64 -> fp64 -> fp64 -> Prop)
      (problem_32_spec_fp64 : list fp64 -> fp64 -> Prop)
*/
/*@ Import Coq Require Import p032_find_zero */

double poly(double* xs, int xs_size, double x)
/*@ With coeffs
    Require 0 <= xs_size && xs_size < INT_MAX &&
            Zlength(coeffs) == xs_size &&
            fp64_isFinite(x) &&
            DoubleArray::full(xs, xs_size, coeffs)
    Ensure problem_32_eval_fp64(coeffs, x@pre, __return) &&
           DoubleArray::full(xs, xs_size, coeffs)
*/
{
    double sum = 0;
    int i;
    for (i = 0; i < xs_size; i++) {
        sum += xs[i] * pow(x, i);
    }
    return sum;
}

double find_zero(double* xs, int xs_size)
/*@ With coeffs
    Require 0 < xs_size && xs_size < INT_MAX &&
            Zlength(coeffs) == xs_size &&
            problem_32_pre_fp64(coeffs) &&
            DoubleArray::full(xs, xs_size, coeffs)
    Ensure problem_32_spec_fp64(coeffs, __return) &&
           DoubleArray::full(xs, xs_size, coeffs)
*/
{
    double ans = 0;
    double value = poly(xs, xs_size, ans);
    while (fabs(value) > 1e-6) {
        double driv = 0;
        for (int i = 1; i < xs_size; i++) {
            driv += xs[i] * pow(ans, i - 1) * i;
        }
        ans = ans - value / driv;
        value = poly(xs, xs_size, ans);
    }
    return ans;
}
