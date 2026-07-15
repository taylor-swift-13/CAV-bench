/*
Return maximum element in the vector.
>>> max_element({1, 2, 3})
3
>>> max_element({5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10})
123
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_35_pre : list Z -> Prop)
               (problem_35_spec : list Z -> Z -> Prop)
               (problem_35_prefix : list Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import p035_max_element */

int max_element(int* l, int l_size)
/*@ With xs
    Require 0 < l_size && l_size < INT_MAX &&
            Zlength(xs) == l_size &&
            problem_35_pre(xs) &&
            IntArray::full(l, l_size, xs)
    Ensure problem_35_spec(xs, __return) &&
           IntArray::full(l, l_size, xs)
*/
{
  int current = l[0];
  int i;
  for (i=1;i<l_size;i++)
    if (current<l[i]) current=l[i];
  return current;

}
