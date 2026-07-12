#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include <stdio.h>
#include "verification_stdlib.h"
#include "verification_list.h"

static int cmp_float(const void* a, const void* b){
    float fa = *(const float*)a;
    float fb = *(const float*)b;
    return (fa > fb) - (fa < fb);
}

float p047_median(float* l, int l_size){
    qsort(l, (size_t)l_size, sizeof(float), cmp_float);
    if (l_size%2==1) return l[l_size/2];
    return 0.5*(l[l_size/2]+l[l_size/2-1]);
}
