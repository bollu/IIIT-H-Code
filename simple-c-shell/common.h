#pragma once


//copied neat idea from ISL library! 
//returns a new block of memory
#define give
//takes a block of memory and frees it
#define take

typedef enum boolean{
    FALSE = 0,
    TRUE = 1
} boolean;

#define KNRM  "\x1B[0m"
#define KRED  "\x1B[31m"
#define KGRN  "\x1B[32m"
#define KYEL  "\x1B[33m"
#define KBLU  "\x1B[34m"
#define KMAG  "\x1B[35m"
#define KCYN  "\x1B[36m"
#define KWHT  "\x1B[37m"


typedef struct List {
    void *data;
    struct List *next;
} List;


void list_add(List **head, void *data);

