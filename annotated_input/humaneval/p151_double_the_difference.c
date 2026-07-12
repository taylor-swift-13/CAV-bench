#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include <stdio.h>
#include "verification_stdlib.h"
#include "verification_list.h"

int he_external_round(double x)
/*@ Require emp
    Ensure he_round_spec(x, __return)
*/;
