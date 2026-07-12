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

FloatArray p030_get_positive(const float* l, int l_size){
    FloatArray out;
    out.size = 0;
    out.data = (float*)malloc((size_t)l_size * sizeof(float));
    if (out.data == NULL) {
        return out;
    }
    for (int i=0;i<l_size;i++)
        if (l[i]>0) out.data[out.size++] = l[i];
    return out;
}
