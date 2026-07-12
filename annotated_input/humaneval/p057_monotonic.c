#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include <stdio.h>
#include "verification_stdlib.h"
#include "verification_list.h"

bool p057_monotonic(float* l, int l_size){
    int incr,decr;
    incr=0;decr=0;
    for (int i=1;i<l_size;i++)
    {
        if (l[i]>l[i-1]) incr=1;
        if (l[i]<l[i-1]) decr=1;
    }
    if (incr+decr==2) return false;
    return true;
}
