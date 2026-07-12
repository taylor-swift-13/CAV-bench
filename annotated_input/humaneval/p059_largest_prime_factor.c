#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include <stdio.h>
#include "verification_stdlib.h"
#include "verification_list.h"

int p059_largest_prime_factor(int n){
    for (int i=2;i*i<=n;i++)
    while (n%i==0 && n>i)  n=n/i;
    return n;
}
