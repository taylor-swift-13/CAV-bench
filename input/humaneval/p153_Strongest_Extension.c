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
    int n = (int)strlen(s) ;
    int strength = 0;
    int j = 0;
    int chr = 0;

    while (j < n) {
        chr = s[j];

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

    strongest = extensions[0];

    max = extension_strength(strongest)
      ;

    i = 1;

    while (i < extensions_size) {

        cur = extensions[i];

        strength = extension_strength(cur)
          ;

        if (strength > max) {
            max = strength;
            best_idx = i;
        }

        i = i + 1;
    }

	    strongest = extensions[best_idx];
	    char* out;
	    int n1;
	    int n2;
	    out = 0;
	    n1 = 0;
	    n2 = 0;

    n1 = (int)strlen(class_name) ;

    n2 = (int)strlen(strongest)
      ;
    out = malloc_char_array(n1 + n2 + 2);

    memcpy(out, class_name, n1) ;

    out[n1] = '.';

    memcpy(out + (n1 + 1), strongest, n2)
      ;

    out[n1 + n2 + 1] = '\0';

    return out;
}
