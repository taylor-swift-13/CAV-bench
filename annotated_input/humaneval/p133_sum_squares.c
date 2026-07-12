#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include <stdio.h>
#include "verification_stdlib.h"
#include "verification_list.h"

int he_external_ceil(double x)
/*@ Require emp
    Ensure he_ceil_spec(x, __return)
*/;
