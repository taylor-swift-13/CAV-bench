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

FloatArray p021_rescale_to_unit(const float* numbers, int numbers_size){
    float min=100000,max=-100000;
    FloatArray out;
    out.data = (float*)malloc((size_t)numbers_size * sizeof(float));
    out.size = numbers_size;
    if (out.data == NULL) {
        out.size = 0;
        return out;
    }

    for (int i=0;i<numbers_size;i++)
        {
            if (numbers[i]<min) min=numbers[i];
            if (numbers[i]>max) max=numbers[i];
        }
    if (max == min) {
        for (int i = 0; i < numbers_size; i++) {
            out.data[i] = 0.0f;
        }
        return out;
    }

    for (int i=0;i<numbers_size;i++)
        out.data[i]=(numbers[i]-min)/(max-min);
    return out;
}
