#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include <stdio.h>
#include "verification_stdlib.h"
#include "verification_list.h"

typedef enum {
    PY_INT,
    PY_DOUBLE,
    PY_STRING
} PyType;

typedef struct {
    PyType type;
    int i;
    double d;
    const char* s;
} PyValue;

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray p022_filter_integers(const PyValue* values, int values_size){
    IntArray out;
    out.size = 0;
    out.data = (int*)malloc((size_t)values_size * sizeof(int));
    if (out.data == NULL) return out;
    for (int i=0;i<values_size;i++)
    {
        if (values[i].type == PY_INT)
            out.data[out.size++] = values[i].i;
    }
    return out;
}
