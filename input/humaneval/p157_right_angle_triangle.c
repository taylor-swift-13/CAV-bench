#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include <stdio.h>
#include "verification_stdlib.h"
#include "verification_list.h"

bool p157_right_angle_triangle(float a, float b, float c){
    if (abs(a*a+b*b-c*c)<1e-4 || abs(a*a+c*c-b*b)<1e-4 || abs(b*b+c*c-a*a)<1e-4) return true;
    return false;
}
