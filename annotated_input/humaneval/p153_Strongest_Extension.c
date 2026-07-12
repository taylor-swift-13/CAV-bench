/*
You will be given the name of a class (a string) && a vector of extensions.
The extensions are to be used to load additional classes to the class. The
strength of the extension is as follows: Let CAP be the number of the uppercase
letters in the extension's name, && let SM be the number of lowercase letters
in the extension's name, the strength is given by the fraction CAP - SM.
You should find the strongest extension && return a string in this
format: ClassName.StrongestExtensionName.
If there are two || more extensions with the same strength, you should
choose the one that comes first in the vector.
For example, if you are given "Slices" as the class && a vector of the
extensions: {"SErviNGSliCes", "Cheese", "StuFfed"} then you should
return "Slices.SErviNGSliCes" since "SErviNGSliCes" is the strongest extension
(its strength is -1).
Example:
for Strongest_Extension("my_class", {"AA", "Be", "CC"}) == "my_class.AA"
*/
#include "ptr_array2_def.h"
#include "string.h"

/*@ Extern Coq (problem_153_pre_z: list Z -> list (list Z) -> Prop)
               (problem_153_spec_z: list Z -> list (list Z) -> list Z -> Prop)
               (rows_well_formed_153: list (list Z) -> Z -> Prop)
               (row_payload_z_153: list Z -> list Z)
               (row_len_z_153: list Z -> Z)
               (extension_strength_z: list Z -> Z)
               (strength_scan_state_153: list Z -> Z -> Z -> Prop)
               (best_prefix_state_153: list (list Z) -> Z -> Z -> Z -> Prop)
               (output_payload_153: list Z -> list Z -> list Z)
               (output_len_safe_153: list Z -> list (list Z) -> Z -> Prop)
               (Znth: {A} -> Z -> list A -> A -> A)
               (Zlength: {A} -> list A -> Z)
*/
/*@ Import Coq Require Import p153_Strongest_Extension */

char *malloc_char_array(int n)
/*@ Require n > 0 && n < INT_MAX && emp
    Ensure __return != 0 && CharArray::undef_full(__return, n)
*/
;

int extension_strength(char *s)
/*@ With str
    Require
      valid_string(str) &&
      string_length(str) <= 100 &&
      string_length(str) < INT_MAX &&
      store_string(s, str)
    Ensure
      __return == extension_strength_z(str) &&
      store_string(s, str)
*/
{
    int n = (int)strlen(s) /*@ where str = str */;
    int strength = 0;
    int j = 0;
    int chr = 0;
    /*@ Inv Assert
      0 <= j && j <= n &&
      n == string_length(str) &&
      s == s@pre &&
      string_length(str) <= 100 &&
      valid_string(str) &&
      strength_scan_state_153(str, j, strength) &&
      0 <= chr && chr <= 127 &&
      store_string(s, str)
    */
    while (j < n) {
        chr = s[j];
        /*@ Assert
          0 <= j && j < n &&
          n == string_length(str) &&
          s == s@pre &&
          string_length(str) <= 100 &&
          valid_string(str) &&
          0 <= chr && chr <= 127 &&
          chr == Znth(j, str, 0) &&
          strength_scan_state_153(str, j, strength) &&
          store_string(s, str)
        */
        if (chr >= 65) {
            if (chr <= 90) {
                strength = strength + 1;
            }
        }
        if (chr >= 97) {
            if (chr <= 122) {
                strength = strength - 1;
            }
        }
        j = j + 1;
        /*@ Assert
          0 <= j && j <= n &&
          n == string_length(str) &&
          s == s@pre &&
          string_length(str) <= 100 &&
          valid_string(str) &&
          0 <= chr && chr <= 127 &&
          strength_scan_state_153(str, j, strength) &&
          store_string(s, str)
        */
    }
    return strength;
}

char* Strongest_Extension(char* class_name, char** extensions, int extensions_size)
/*@ With class_l rows
    Require
      0 < extensions_size && extensions_size <= 100 &&
      valid_string(class_l) &&
      string_length(class_l) <= 100 &&
      rows_well_formed_153(rows, extensions_size) &&
      output_len_safe_153(class_l, rows, extensions_size) &&
      problem_153_pre_z(class_l, rows) &&
      store_string(class_name, class_l) *
      CharPtrArray2::full(extensions, extensions_size, rows)
    Ensure exists out_l,
      problem_153_spec_z(class_l, rows, out_l) &&
      store_string(class_name, class_l) *
      CharPtrArray2::full(extensions, extensions_size, rows) *
      store_string(__return, out_l)
*/
{
	char* strongest;
	char* cur;
	int max;
	int strength;
	int best_idx;
	int i;

	strongest = 0;
	cur = 0;
	max = 0;
	strength = 0;
	best_idx = 0;
	i = 0;
    /*@ Assert
      exists row_ptr,
      0 < extensions_size@pre && extensions_size@pre <= 100 &&
      extensions_size == extensions_size@pre &&
      extensions == extensions@pre &&
      class_name == class_name@pre &&
      strongest == 0 &&
      cur == 0 &&
      max == 0 &&
      strength == 0 &&
      best_idx == 0 &&
      i == 0 &&
      valid_string(class_l) &&
      string_length(class_l) <= 100 &&
      rows_well_formed_153(rows, extensions_size@pre) &&
      output_len_safe_153(class_l, rows, extensions_size@pre) &&
      problem_153_pre_z(class_l, rows) &&
      valid_string(row_payload_z_153(Znth(0, rows, nil))) &&
      string_length(row_payload_z_153(Znth(0, rows, nil))) <= 100 &&
      string_length(row_payload_z_153(Znth(0, rows, nil))) < INT_MAX &&
      CharPtrArray2::missing_i(extensions@pre, extensions_size@pre, 0, row_ptr, rows) *
      data_at(extensions@pre + 0 * sizeof(char *), char *, row_ptr) *
      store_string(row_ptr, row_payload_z_153(Znth(0, rows, nil))) *
      store_string(class_name@pre, class_l)
    */
    strongest = extensions[0];
    /*@ Assert
      exists row_ptr,
      0 < extensions_size@pre && extensions_size@pre <= 100 &&
      extensions_size == extensions_size@pre &&
      extensions == extensions@pre &&
      class_name == class_name@pre &&
      strongest == row_ptr &&
      cur == 0 &&
      max == 0 &&
      strength == 0 &&
      best_idx == 0 &&
      i == 0 &&
      valid_string(class_l) &&
      string_length(class_l) <= 100 &&
      rows_well_formed_153(rows, extensions_size@pre) &&
      output_len_safe_153(class_l, rows, extensions_size@pre) &&
      problem_153_pre_z(class_l, rows) &&
      valid_string(row_payload_z_153(Znth(0, rows, nil))) &&
      string_length(row_payload_z_153(Znth(0, rows, nil))) <= 100 &&
      string_length(row_payload_z_153(Znth(0, rows, nil))) < INT_MAX &&
      CharPtrArray2::missing_i(extensions@pre, extensions_size@pre, 0, row_ptr, rows) *
      data_at(extensions@pre + 0 * sizeof(char *), char *, row_ptr) *
      store_string(strongest, row_payload_z_153(Znth(0, rows, nil))) *
      store_string(class_name@pre, class_l)
    */
    max = extension_strength(strongest)
      /*@ where str = row_payload_z_153(Znth(0, rows, nil)) */;
    /*@ Assert
      0 < extensions_size@pre && extensions_size@pre <= 100 &&
	      extensions_size == extensions_size@pre &&
	      extensions == extensions@pre &&
	      class_name == class_name@pre &&
	      max == extension_strength_z(row_payload_z_153(Znth(0, rows, nil))) &&
	      strongest == strongest &&
      cur == 0 &&
      strength == 0 &&
      best_idx == 0 &&
      i == 0 &&
      valid_string(class_l) &&
      string_length(class_l) <= 100 &&
      rows_well_formed_153(rows, extensions_size@pre) &&
      output_len_safe_153(class_l, rows, extensions_size@pre) &&
      problem_153_pre_z(class_l, rows) &&
      CharPtrArray2::full(extensions@pre, extensions_size@pre, rows) *
      store_string(class_name@pre, class_l)
    */
    i = 1;
    /*@ Inv Assert
      1 <= i && i <= extensions_size@pre &&
      0 < extensions_size@pre && extensions_size@pre <= 100 &&
	      extensions_size == extensions_size@pre &&
	      extensions == extensions@pre &&
	      class_name == class_name@pre &&
	      best_idx == best_idx &&
      0 <= best_idx && best_idx < i &&
      strongest == strongest &&
      cur == cur &&
      strength == strength &&
      max == max &&
      valid_string(class_l) &&
      string_length(class_l) <= 100 &&
      rows_well_formed_153(rows, extensions_size@pre) &&
      output_len_safe_153(class_l, rows, extensions_size@pre) &&
      problem_153_pre_z(class_l, rows) &&
	      best_prefix_state_153(rows, i, best_idx, max) &&
	      CharPtrArray2::full(extensions@pre, extensions_size@pre, rows) *
	      store_string(class_name@pre, class_l)
    */
    while (i < extensions_size) {
        /*@ Assert
          exists row_ptr,
          1 <= i && i < extensions_size@pre &&
          0 < extensions_size@pre && extensions_size@pre <= 100 &&
	          extensions_size == extensions_size@pre &&
	          extensions == extensions@pre &&
	          class_name == class_name@pre &&
	          cur == cur &&
          strongest == strongest &&
          strength == strength &&
          0 <= best_idx && best_idx < i &&
          max == max &&
          valid_string(class_l) &&
          string_length(class_l) <= 100 &&
          rows_well_formed_153(rows, extensions_size@pre) &&
          output_len_safe_153(class_l, rows, extensions_size@pre) &&
          problem_153_pre_z(class_l, rows) &&
          best_prefix_state_153(rows, i, best_idx, max) &&
          valid_string(row_payload_z_153(Znth(i, rows, nil))) &&
          string_length(row_payload_z_153(Znth(i, rows, nil))) <= 100 &&
          string_length(row_payload_z_153(Znth(i, rows, nil))) < INT_MAX &&
          CharPtrArray2::missing_i(extensions@pre, extensions_size@pre, i, row_ptr, rows) *
	          data_at(extensions@pre + i * sizeof(char *), char *, row_ptr) *
	          store_string(row_ptr, row_payload_z_153(Znth(i, rows, nil))) *
	      store_string(class_name@pre, class_l)
        */
        cur = extensions[i];
        /*@ Assert
          exists row_ptr,
          1 <= i && i < extensions_size@pre &&
          0 < extensions_size@pre && extensions_size@pre <= 100 &&
	          extensions_size == extensions_size@pre &&
	          extensions == extensions@pre &&
	          class_name == class_name@pre &&
	          cur == row_ptr &&
          strongest == strongest &&
          strength == strength &&
          0 <= best_idx && best_idx < i &&
          max == max &&
          valid_string(class_l) &&
          string_length(class_l) <= 100 &&
          rows_well_formed_153(rows, extensions_size@pre) &&
          output_len_safe_153(class_l, rows, extensions_size@pre) &&
          problem_153_pre_z(class_l, rows) &&
          best_prefix_state_153(rows, i, best_idx, max) &&
          valid_string(row_payload_z_153(Znth(i, rows, nil))) &&
          string_length(row_payload_z_153(Znth(i, rows, nil))) <= 100 &&
          string_length(row_payload_z_153(Znth(i, rows, nil))) < INT_MAX &&
          CharPtrArray2::missing_i(extensions@pre, extensions_size@pre, i, row_ptr, rows) *
	          data_at(extensions@pre + i * sizeof(char *), char *, row_ptr) *
	          store_string(cur, row_payload_z_153(Znth(i, rows, nil))) *
	      store_string(class_name@pre, class_l)
        */
        strength = extension_strength(cur)
          /*@ where str = row_payload_z_153(Znth(i, rows, nil)) */;
        /*@ Assert
          1 <= i && i < extensions_size@pre &&
          0 < extensions_size@pre && extensions_size@pre <= 100 &&
	          extensions_size == extensions_size@pre &&
	          extensions == extensions@pre &&
	          class_name == class_name@pre &&
	          strongest == strongest &&
          cur == cur &&
          strength == extension_strength_z(row_payload_z_153(Znth(i, rows, nil))) &&
          0 <= best_idx && best_idx < i &&
          max == max &&
          valid_string(class_l) &&
          string_length(class_l) <= 100 &&
          rows_well_formed_153(rows, extensions_size@pre) &&
          output_len_safe_153(class_l, rows, extensions_size@pre) &&
          problem_153_pre_z(class_l, rows) &&
	          best_prefix_state_153(rows, i, best_idx, max) &&
	          CharPtrArray2::full(extensions@pre, extensions_size@pre, rows) *
	      store_string(class_name@pre, class_l)
        */
        if (strength > max) {
            max = strength;
            best_idx = i;
        }
        /*@ Assert
          1 <= i && i < extensions_size@pre &&
          0 < extensions_size@pre && extensions_size@pre <= 100 &&
		          extensions_size == extensions_size@pre &&
		          extensions == extensions@pre &&
		          class_name == class_name@pre &&
	          strongest == strongest &&
	          cur == cur &&
	          strength == strength &&
	          max == max &&
		          0 <= best_idx && best_idx <= i &&
          valid_string(class_l) &&
          string_length(class_l) <= 100 &&
          rows_well_formed_153(rows, extensions_size@pre) &&
          output_len_safe_153(class_l, rows, extensions_size@pre) &&
          problem_153_pre_z(class_l, rows) &&
	          best_prefix_state_153(rows, i + 1, best_idx, max) &&
	          CharPtrArray2::full(extensions@pre, extensions_size@pre, rows) *
	      store_string(class_name@pre, class_l)
        */
        i = i + 1;
    }

    /*@ Assert
      exists row_ptr,
      0 <= best_idx && best_idx < extensions_size@pre &&
      extensions_size == extensions_size@pre &&
      extensions == extensions@pre &&
      class_name == class_name@pre &&
      strongest == strongest &&
      cur == cur &&
      strength == strength &&
      max == max &&
      valid_string(class_l) &&
      string_length(class_l) <= 100 &&
      rows_well_formed_153(rows, extensions_size@pre) &&
      output_len_safe_153(class_l, rows, extensions_size@pre) &&
      problem_153_pre_z(class_l, rows) &&
      best_prefix_state_153(rows, extensions_size@pre, best_idx, max) &&
      valid_string(row_payload_z_153(Znth(best_idx, rows, nil))) &&
      string_length(row_payload_z_153(Znth(best_idx, rows, nil))) <= 100 &&
      string_length(row_payload_z_153(Znth(best_idx, rows, nil))) < INT_MAX &&
      CharPtrArray2::missing_i(extensions@pre, extensions_size@pre, best_idx, row_ptr, rows) *
	      data_at(extensions@pre + best_idx * sizeof(char *), char *, row_ptr) *
	      store_string(row_ptr, row_payload_z_153(Znth(best_idx, rows, nil))) *
		      store_string(class_name@pre, class_l) *
	      data_at(&i, int, i)
	    */
	    strongest = extensions[best_idx];
	    char* out;
	    int n1;
	    int n2;
	    out = 0;
	    n1 = 0;
	    n2 = 0;
	    /*@ Assert
	      exists row_ptr,
	      0 <= best_idx && best_idx < extensions_size@pre &&
      extensions_size == extensions_size@pre &&
      extensions == extensions@pre &&
	      class_name == class_name@pre &&
	      strongest == row_ptr &&
	      cur == cur &&
	      out == 0 &&
	      strength == strength &&
	      max == max &&
	      n1 == 0 &&
	      n2 == 0 &&
	      valid_string(class_l) &&
      string_length(class_l) <= 100 &&
      rows_well_formed_153(rows, extensions_size@pre) &&
      output_len_safe_153(class_l, rows, extensions_size@pre) &&
      problem_153_pre_z(class_l, rows) &&
      best_prefix_state_153(rows, extensions_size@pre, best_idx, max) &&
      valid_string(row_payload_z_153(Znth(best_idx, rows, nil))) &&
      string_length(row_payload_z_153(Znth(best_idx, rows, nil))) <= 100 &&
      string_length(row_payload_z_153(Znth(best_idx, rows, nil))) < INT_MAX &&
      CharPtrArray2::missing_i(extensions@pre, extensions_size@pre, best_idx, row_ptr, rows) *
	      data_at(extensions@pre + best_idx * sizeof(char *), char *, row_ptr) *
	      store_string(strongest, row_payload_z_153(Znth(best_idx, rows, nil))) *
		      store_string(class_name@pre, class_l) *
	      data_at(&i, int, i)
    */
    n1 = (int)strlen(class_name) /*@ where str = class_l */;
    /*@ Assert
      exists row_ptr,
      0 <= best_idx && best_idx < extensions_size@pre &&
      n1 == string_length(class_l) &&
      extensions_size == extensions_size@pre &&
      extensions == extensions@pre &&
      class_name == class_name@pre &&
	      strongest == row_ptr &&
	      cur == cur &&
	      out == 0 &&
	      strength == strength &&
	      max == max &&
	      n2 == 0 &&
	      valid_string(class_l) &&
      string_length(class_l) <= 100 &&
      rows_well_formed_153(rows, extensions_size@pre) &&
      output_len_safe_153(class_l, rows, extensions_size@pre) &&
      problem_153_pre_z(class_l, rows) &&
      best_prefix_state_153(rows, extensions_size@pre, best_idx, max) &&
      valid_string(row_payload_z_153(Znth(best_idx, rows, nil))) &&
      string_length(row_payload_z_153(Znth(best_idx, rows, nil))) <= 100 &&
      string_length(row_payload_z_153(Znth(best_idx, rows, nil))) < INT_MAX &&
      CharPtrArray2::missing_i(extensions@pre, extensions_size@pre, best_idx, row_ptr, rows) *
	      data_at(extensions@pre + best_idx * sizeof(char *), char *, row_ptr) *
	      store_string(strongest, row_payload_z_153(Znth(best_idx, rows, nil))) *
		      store_string(class_name@pre, class_l) *
	      data_at(&i, int, i)
    */
    n2 = (int)strlen(strongest)
      /*@ where str = row_payload_z_153(Znth(best_idx, rows, nil)) */;
    out = malloc_char_array(n1 + n2 + 2);
    /*@ Assert
      exists row_ptr,
      0 <= best_idx && best_idx < extensions_size@pre &&
      n1 == string_length(class_l) &&
      n2 == row_len_z_153(Znth(best_idx, rows, nil)) &&
      n1 + n2 + 2 < INT_MAX &&
      extensions_size == extensions_size@pre &&
      extensions == extensions@pre &&
	      class_name == class_name@pre &&
	      out != 0 &&
	      strongest == row_ptr &&
	      cur == cur &&
	      strength == strength &&
	      valid_string(class_l) &&
      all_ascii(class_l) &&
      Zlength(class_l) == n1 &&
      0 <= n1 && n1 < INT_MAX &&
      valid_string(row_payload_z_153(Znth(best_idx, rows, nil))) &&
      rows_well_formed_153(rows, extensions_size@pre) &&
      output_len_safe_153(class_l, rows, extensions_size@pre) &&
      problem_153_pre_z(class_l, rows) &&
      best_prefix_state_153(rows, extensions_size@pre, best_idx, max) &&
      CharPtrArray2::missing_i(extensions@pre, extensions_size@pre, best_idx, row_ptr, rows) *
      data_at(extensions@pre + best_idx * sizeof(char *), char *, row_ptr) *
	      store_string(strongest, row_payload_z_153(Znth(best_idx, rows, nil))) *
	      CharArray::full(class_name@pre, n1, class_l) *
	      CharArray::seg(class_name@pre, n1, n1 + 1, cons(0, nil)) *
	      CharArray::undef_full(out, n1) *
	      CharArray::undef_seg(out, n1, n1 + n2 + 2) *
	      data_at(&i, int, i)
    */
    memcpy(out, class_name, n1) /*@ where bytes = class_l */;
    /*@ Assert
      exists row_ptr,
      0 <= best_idx && best_idx < extensions_size@pre &&
      n1 == string_length(class_l) &&
      n2 == row_len_z_153(Znth(best_idx, rows, nil)) &&
      extensions_size == extensions_size@pre &&
      extensions == extensions@pre &&
      class_name == class_name@pre &&
	      0 <= n2 &&
	      out != 0 &&
	      strongest == row_ptr &&
	      cur == cur &&
	      strength == strength &&
	      max == max &&
	      valid_string(class_l) &&
      valid_string(row_payload_z_153(Znth(best_idx, rows, nil))) &&
      rows_well_formed_153(rows, extensions_size@pre) &&
      output_len_safe_153(class_l, rows, extensions_size@pre) &&
      problem_153_pre_z(class_l, rows) &&
      best_prefix_state_153(rows, extensions_size@pre, best_idx, max) &&
      CharPtrArray2::missing_i(extensions@pre, extensions_size@pre, best_idx, row_ptr, rows) *
      data_at(extensions@pre + best_idx * sizeof(char *), char *, row_ptr) *
      store_string(strongest, row_payload_z_153(Znth(best_idx, rows, nil))) *
	      store_string(class_name@pre, class_l) *
	      CharArray::full(out, n1, class_l) *
	      CharArray::undef_seg(out, n1, n1 + 1) *
	      CharArray::undef_seg(out, n1 + 1, n1 + n2 + 2) *
	      data_at(&i, int, i)
    */
    out[n1] = '.';
    /*@ Assert
      exists row_ptr,
      0 <= best_idx && best_idx < extensions_size@pre &&
      n1 == string_length(class_l) &&
      n2 == row_len_z_153(Znth(best_idx, rows, nil)) &&
      extensions_size == extensions_size@pre &&
      extensions == extensions@pre &&
      class_name == class_name@pre &&
	      0 <= n2 && n2 < INT_MAX &&
	      out != 0 &&
	      strongest == row_ptr &&
	      cur == cur &&
	      strength == strength &&
	      max == max &&
	      valid_string(class_l) &&
      valid_string(row_payload_z_153(Znth(best_idx, rows, nil))) &&
      all_ascii(row_payload_z_153(Znth(best_idx, rows, nil))) &&
      Zlength(row_payload_z_153(Znth(best_idx, rows, nil))) == n2 &&
      rows_well_formed_153(rows, extensions_size@pre) &&
      output_len_safe_153(class_l, rows, extensions_size@pre) &&
      problem_153_pre_z(class_l, rows) &&
      best_prefix_state_153(rows, extensions_size@pre, best_idx, max) &&
      CharPtrArray2::missing_i(extensions@pre, extensions_size@pre, best_idx, row_ptr, rows) *
      data_at(extensions@pre + best_idx * sizeof(char *), char *, row_ptr) *
      CharArray::full(strongest, n2, row_payload_z_153(Znth(best_idx, rows, nil))) *
      CharArray::seg(strongest, n2, n2 + 1, cons(0, nil)) *
	      store_string(class_name@pre, class_l) *
	      CharArray::full(out, n1 + 1, app(class_l, cons(46, nil))) *
	      CharArray::undef_full(out + (n1 + 1) * sizeof(char), n2) *
	      CharArray::undef_seg(out, n1 + n2 + 1, n1 + n2 + 2) *
	      data_at(&i, int, i)
    */
    memcpy(out + (n1 + 1), strongest, n2)
      /*@ where bytes = row_payload_z_153(Znth(best_idx, rows, nil)) */;
    /*@ Assert
      exists row_ptr,
      0 <= best_idx && best_idx < extensions_size@pre &&
      n1 == string_length(class_l) &&
	      n2 == row_len_z_153(Znth(best_idx, rows, nil)) &&
      extensions_size == extensions_size@pre &&
      extensions == extensions@pre &&
      class_name == class_name@pre &&
	      out != 0 &&
	      strongest == row_ptr &&
	      cur == cur &&
	      strength == strength &&
	      max == max &&
	      valid_string(class_l) &&
      valid_string(row_payload_z_153(Znth(best_idx, rows, nil))) &&
      rows_well_formed_153(rows, extensions_size@pre) &&
      output_len_safe_153(class_l, rows, extensions_size@pre) &&
      problem_153_pre_z(class_l, rows) &&
      best_prefix_state_153(rows, extensions_size@pre, best_idx, max) &&
      CharPtrArray2::missing_i(extensions@pre, extensions_size@pre, best_idx, row_ptr, rows) *
      data_at(extensions@pre + best_idx * sizeof(char *), char *, row_ptr) *
      store_string(strongest, row_payload_z_153(Znth(best_idx, rows, nil))) *
	      store_string(class_name@pre, class_l) *
	      CharArray::full(out, n1 + n2 + 1,
	        app(app(class_l, cons(46, nil)), row_payload_z_153(Znth(best_idx, rows, nil)))) *
	      CharArray::undef_seg(out, n1 + n2 + 1, n1 + n2 + 2) *
	      data_at(&i, int, i)
    */
    out[n1 + n2 + 1] = '\0';
    /*@ Assert
      exists row_ptr out_l,
      0 <= best_idx && best_idx < extensions_size@pre &&
      out_l == output_payload_153(class_l, row_payload_z_153(Znth(best_idx, rows, nil))) &&
      out != 0 &&
      extensions_size == extensions_size@pre &&
      extensions == extensions@pre &&
      class_name == class_name@pre &&
      strongest == row_ptr &&
      n1 == string_length(class_l) &&
      n2 == row_len_z_153(Znth(best_idx, rows, nil)) &&
      cur == cur &&
      strength == strength &&
      max == max &&
	      0 <= best_idx && best_idx < extensions_size@pre &&
      rows_well_formed_153(rows, extensions_size@pre) &&
      problem_153_pre_z(class_l, rows) &&
      best_prefix_state_153(rows, extensions_size@pre, best_idx, max) &&
      problem_153_spec_z(class_l, rows, out_l) &&
      CharPtrArray2::missing_i(extensions@pre, extensions_size@pre, best_idx, row_ptr, rows) *
	      data_at(extensions@pre + best_idx * sizeof(char *), char *, row_ptr) *
	      store_string(strongest, row_payload_z_153(Znth(best_idx, rows, nil))) *
	      store_string(class_name@pre, class_l) *
	      store_string(out, out_l) *
	      data_at(&i, int, i)
    */
    return out;
}
