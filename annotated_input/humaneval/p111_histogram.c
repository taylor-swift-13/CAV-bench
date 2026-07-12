#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include <stdio.h>
#include "verification_stdlib.h"
#include "verification_list.h"

typedef struct {
    char* keys;
    int* values;
    int size;
} CharIntMap;

CharIntMap p111_histogram(const char* test){
    int count[256] = {0};
    CharIntMap out;
    int max=0;
    out.keys = (char*)malloc(256);
    out.values = (int*)malloc(256 * sizeof(int));
    out.size = 0;
    if (out.keys == NULL || out.values == NULL) {
        free(out.keys);
        free(out.values);
        out.keys = NULL;
        out.values = NULL;
        out.size = 0;
        return out;
    }

    for (int i=0;test[i]!='\0';i++)
        if (test[i]!=' ')
        {
            unsigned char ch = (unsigned char)test[i];
            count[ch]+=1;
            if (count[ch]>max) max=count[ch];
        }

    for (int ch=0; ch<256; ch++) {
        if (count[ch] == max && max > 0) {
            out.keys[out.size] = (char)ch;
            out.values[out.size] = count[ch];
            out.size += 1;
        }
    }
    return out;
}
