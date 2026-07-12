#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include <stdio.h>
#include "verification_stdlib.h"
#include "verification_list.h"

float p035_max_element(float* l, int l_size){
  float max=-10000;
  for (int i=0;i<l_size;i++)
  if (max<l[i]) max=l[i];
  return max;

}
