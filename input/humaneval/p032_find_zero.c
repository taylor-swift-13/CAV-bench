#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include <stdio.h>
#include "verification_stdlib.h"
#include "verification_list.h"

double he_external_pow(double x, double y)
/*@ Require emp
    Ensure he_pow_spec(x, y, __return)
*/;
