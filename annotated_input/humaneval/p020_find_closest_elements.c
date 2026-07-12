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

FloatArray p020_find_closest_elements(const float* numbers, int numbers_size){
    FloatArray out;
    out.data = (float*)malloc(2 * sizeof(float));
    out.size = 2;

    if (out.data == NULL) {
        out.size = 0;
        return out;
    }

    out.data[0] = numbers[0];
    out.data[1] = numbers[1];
    for (int i=0;i<numbers_size;i++)
    for (int j=i+1;j<numbers_size;j++)
        if (fabsf(numbers[i]-numbers[j]) < fabsf(out.data[0]-out.data[1])) {
            out.data[0] = numbers[i];
            out.data[1] = numbers[j];
        }
    if (out.data[0] > out.data[1]) {
        float t = out.data[0];
        out.data[0] = out.data[1];
        out.data[1] = t;
    }
    return out;
}
