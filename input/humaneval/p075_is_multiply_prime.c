#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include <stdio.h>
#include "verification_stdlib.h"
#include "verification_list.h"

bool p075_is_multiply_prime(int a){
    int num=0;
    for (int i=2;i*i<=a;i++)
    while (a%i==0 && a>i)
    {
        a=a/i;
        num+=1;
    }
    if (num==2) return true;
    return false;
}
