#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include <stdio.h>
#include "verification_stdlib.h"
#include "verification_list.h"

typedef struct {
  const char** data;
  int size;
} StrArray;

StrArray p081_numerical_letter_grade(const float* grades, int grades_size){
  StrArray out;
  out.size = grades_size;
  out.data = (const char**)malloc((size_t)grades_size * sizeof(const char*));
  if (out.data == NULL) {
    out.size = 0;
    return out;
  }
    for (int i=0;i<grades_size;i++)
    {
    if (grades[i]>=3.9999) out.data[i] = "A+";
    else if (grades[i]>3.7001) out.data[i] = "A";
    else if (grades[i]>3.3001) out.data[i] = "A-";
    else if (grades[i]>3.0001) out.data[i] = "B+";
    else if (grades[i]>2.7001) out.data[i] = "B";
    else if (grades[i]>2.3001) out.data[i] = "B-";
    else if (grades[i]>2.0001) out.data[i] = "C+";
    else if (grades[i]>1.7001) out.data[i] = "C";
    else if (grades[i]>1.3001) out.data[i] = "C-";
    else if (grades[i]>1.0001) out.data[i] = "D+";
    else if (grades[i]>0.7001) out.data[i] = "D";
    else if (grades[i]>0.0001) out.data[i] = "D-";
    else out.data[i] = "E";
    }
    return out;
}
