#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include <stdio.h>
#include "verification_stdlib.h"
#include "verification_list.h"

int p097_multiply(int a, int b){
    return (abs(a)%10)*(abs(b)%10);
}
