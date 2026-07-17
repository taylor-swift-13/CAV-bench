/* Return whether a nonempty integer array is monotone in either direction. */
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_57_pre_z : list Z -> Prop)
               (problem_57_spec_z : list Z -> Z -> Prop)
               (problem_57_prefix_z : list Z -> Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import p057_monotonic */

int monotonic(const int* l, int l_size)
/*@ With input
    Require 1 <= l_size && l_size < INT_MAX &&
            Zlength(input) == l_size && problem_57_pre_z(input) &&
            IntArray::full(l, l_size, input)
    Ensure problem_57_spec_z(input, __return) &&
           IntArray::full(l, l_size, input)
*/
{
    int incr = 1;
    int decr = 1;
    int i;
    for (i = 1; i < l_size; ++i) {
        if (l[i] < l[i - 1]) incr = 0;
        if (l[i] > l[i - 1]) decr = 0;
    }
    if (incr == 1 || decr == 1) return 1;
    return 0;
}
