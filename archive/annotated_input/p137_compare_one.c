/* Compare tagged integer, binary64, or decimal-string values. */
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"
#include "string.h"

/*@ Extern Coq (problem_137_pre_c : Z -> Z -> fp64 -> list Z ->
                                    Z -> Z -> fp64 -> list Z -> Prop)
               (problem_137_result_c : (String -> Z) ->
                    Z -> Z -> fp64 -> list Z -> Z ->
                    Z -> Z -> fp64 -> list Z -> Z ->
                    Z -> Z -> fp64 -> Z -> Prop)
               (GlobalStrings : (String -> Z) -> Assertion) */
/*@ Import Coq Require Import p137_compare_one */

typedef enum { ANY_INT = 0, ANY_DOUBLE = 1, ANY_STRING = 2 } AnyType;

typedef struct {
    int type;
    int i;
    double d;
    const char *s;
} AnyValue;

AnyValue *malloc_any_value_struct()
/*@ Require emp
    Ensure __return != 0 &&
           undef_data_at(&(__return -> type)) *
           undef_data_at(&(__return -> i)) *
           undef_data_at(&(__return -> d)) *
           undef_data_at(&(__return -> s))
*/;

static double any_to_double(int type, int i, double d, const char *s) {
    if (type == ANY_INT) return (double)i;
    if (type == ANY_DOUBLE) return d;
    {
        char buf[128];
        int k = 0;
        for (int j = 0; s[j] != '\0' && k < 127; ++j) {
            buf[k] = (s[j] == ',') ? '.' : s[j];
            k += 1;
        }
        buf[k] = '\0';
        return atof(buf);
    }
}

AnyValue *compare_one(int atype, int ai, double ad, const char *as,
                      int btype, int bi, double bd, const char *bs)
/*@ With atext btext (LitMap : String -> Z)
    Require valid_string(atext) && valid_string(btext) &&
            string_length(atext) < 127 && string_length(btext) < 127 &&
            problem_137_pre_c(atype, ai, ad, atext,
                              btype, bi, bd, btext) &&
            store_string(as, atext) * store_string(bs, btext) *
            GlobalStrings(LitMap)
    Ensure exists otype oi od os,
      __return != 0 &&
      problem_137_result_c(LitMap,
          atype, ai, ad, atext, as,
          btype, bi, bd, btext, bs,
          otype, oi, od, os) &&
      data_at(&(__return -> type), otype) *
      data_at(&(__return -> i), oi) *
      data_at(&(__return -> d), od) *
      data_at(&(__return -> s), os) *
      store_string(as, atext) * store_string(bs, btext) *
      GlobalStrings(LitMap)
*/
{
    double numa = any_to_double(atype, ai, ad, as);
    double numb = any_to_double(btype, bi, bd, bs);
    AnyValue *out = malloc_any_value_struct();
    if (numa == numb) {
        out->type = ANY_STRING;
        out->s = "None";
        out->i = 0;
        out->d = 0.0;
    } else if (numa < numb) {
        out->type = btype; out->i = bi; out->d = bd; out->s = bs;
    } else {
        out->type = atype; out->i = ai; out->d = ad; out->s = as;
    }
    return out;
}
