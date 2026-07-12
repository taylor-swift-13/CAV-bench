#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include <stdio.h>
#include "verification_stdlib.h"
#include "verification_list.h"

bool p000_has_close_elements(float* numbers, int numbers_size, float threshold){
    int i,j;

    for (i=0;i<numbers_size;i++)
    for (j=i+1;j<numbers_size;j++)
    if (abs(numbers[i]-numbers[j])<threshold)
    return true;

    return false;
}
