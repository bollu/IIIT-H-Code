#include <stdio.h>
#include <pthread.h>
#include <memory.h>
#include <stdlib.h>
#include <unistd.h>
#include <assert.h>
#include <math.h>

typedef int EVMId;
typedef int RobotId;
struct Booth {
    pthread_mutex_t mutex;
    EVMId free_evm;
    RobotId free_robots;
}


int main() {
    return 0;
    int x;
}
