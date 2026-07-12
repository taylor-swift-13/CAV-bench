#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include <stdio.h>
#include "verification_stdlib.h"
#include "verification_list.h"

typedef struct {
    float* data;
    int size;
} FloatArray;

FloatArray p062_derivative(const float* xs, int xs_size){
    FloatArray out;
    out.size = xs_size > 0 ? xs_size - 1 : 0;
    out.data = (float*)malloc((size_t)out.size * sizeof(float));
    if (out.data == NULL && out.size > 0) {
        out.size = 0;
        return out;
    }
    for (int i=1;i<xs_size;i++)
        out.data[i-1] = i*xs[i];
    return out;
}
