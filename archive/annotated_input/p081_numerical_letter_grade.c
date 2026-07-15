/* Convert GPAs in [0,4] to the letter grades defined by HumanEval 81. */
#include "verification_stdlib.h"
#include "verification_list.h"
#include "float_array_def.h"
#include "ptr_array2_def.h"
#include "string.h"

/*@ Extern Coq (problem_81_pre_fp32 : list fp32 -> Prop)
               (problem_81_output_ptrs : (String -> Z) -> list fp32 -> list Z -> Prop)
               (GlobalStrings : (String -> Z) -> Assertion) */
/*@ Import Coq Require Import p081_numerical_letter_grade */

typedef struct {
    const char **data;
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

StrArray *numerical_letter_grade(const float *grades, int grades_size)
/*@ With input (LitMap : String -> Z)
    Require 0 <= grades_size && grades_size < INT_MAX &&
            Zlength(input) == grades_size &&
            problem_81_pre_fp32(input) &&
            FloatArray::full(grades, grades_size, input) *
            GlobalStrings(LitMap)
    Ensure exists data size,
      __return != 0 &&
      FloatArray::full(grades, grades_size, input) *
      GlobalStrings(LitMap) *
      data_at(&(__return -> data), data) *
      data_at(&(__return -> size), size) *
      (((data == 0) && (size == 0) && emp) ||
       (exists output,
          data != 0 && size == grades_size &&
          Zlength(output) == size &&
          problem_81_output_ptrs(LitMap, input, output) &&
          PtrArray::full(data, size, output)))
*/
{
    StrArray *out = malloc_str_array_struct();
    out->size = grades_size;
    out->data = (const char **)malloc_char_ptr_array(grades_size);
    if (out->data == 0) {
        out->size = 0;
        return out;
    }
    for (int i = 0; i < grades_size; ++i) {
        if (grades[i] >= 4.0f) out->data[i] = "A+";
        else if (grades[i] > 3.7f) out->data[i] = "A";
        else if (grades[i] > 3.3f) out->data[i] = "A-";
        else if (grades[i] > 3.0f) out->data[i] = "B+";
        else if (grades[i] > 2.7f) out->data[i] = "B";
        else if (grades[i] > 2.3f) out->data[i] = "B-";
        else if (grades[i] > 2.0f) out->data[i] = "C+";
        else if (grades[i] > 1.7f) out->data[i] = "C";
        else if (grades[i] > 1.3f) out->data[i] = "C-";
        else if (grades[i] > 1.0f) out->data[i] = "D+";
        else if (grades[i] > 0.7f) out->data[i] = "D";
        else if (grades[i] > 0.0f) out->data[i] = "D-";
        else out->data[i] = "E";
    }
    return out;
}
