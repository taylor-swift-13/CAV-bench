#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include <stdio.h>
#include "verification_stdlib.h"
#include "verification_list.h"

typedef enum {
    ANY_INT,
    ANY_DOUBLE,
    ANY_STRING
} AnyType;

typedef struct {
    AnyType type;
    int i;
    double d;
    const char* s;
} AnyValue;

static double any_to_double(AnyValue v) {
    if (v.type == ANY_INT) return (double)v.i;
    if (v.type == ANY_DOUBLE) return v.d;
    {
        char buf[128];
        int k = 0;
        for (int i = 0; v.s[i] != '\0' && k < 127; i++) {
            buf[k++] = (v.s[i] == ',') ? '.' : v.s[i];
        }
        buf[k] = '\0';
        return atof(buf);
    }
}

AnyValue p137_compare_one(AnyValue a,AnyValue b){
    double  numa = any_to_double(a),numb = any_to_double(b);
    AnyValue out;
    if (numa==numb) {
        out.type = ANY_STRING;
        out.s = "None";
        out.i = 0;
        out.d = 0.0;
        return out;
    }
    if (numa<numb) return b;
    return a;
}
