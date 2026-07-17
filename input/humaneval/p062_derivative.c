/* Exact integer-coefficient boundary for polynomial differentiation. */
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_62_pre_z : list Z -> Prop)
               (problem_62_spec_z : list Z -> list Z -> Prop)
               (problem_62_prefix_z : list Z -> Z -> list Z -> Prop) */
/*@ Import Coq Require Import p062_derivative */

int derivative(const int* xs, int xs_size, int* out)
/*@ With input
    Require 1 <= xs_size && xs_size < INT_MAX &&
            Zlength(input) == xs_size && problem_62_pre_z(input) &&
            IntArray::full(xs, xs_size, input) *
            IntArray::undef_full(out, xs_size - 1)
    Ensure exists output,
            __return == xs_size - 1 && Zlength(output) == __return &&
            problem_62_spec_z(input, output) &&
            IntArray::full(xs, xs_size, input) *
            IntArray::full(out, __return, output)
*/
{
    int i;
    for (i = 1; i < xs_size; ++i) {
        out[i - 1] = i * xs[i];
    }
    return xs_size - 1;
}
