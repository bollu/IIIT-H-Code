#include <stdio.h>
#include <pthread.h>
#include <memory.h>
#include <stdlib.h>
#include <unistd.h>
#include <assert.h>
#include <math.h>

pthread_mutex_t mutex;

int *g_circbuf;
int g_size = 0;
int g_total_size = 0;


int g_bufread = -1;
int g_bufwrite = -1;

void init_queue(int total_size) {
    g_total_size = total_size;
    g_size = 0;
    g_circbuf = (int*)(malloc(total_size * sizeof(int)));
    g_bufread = g_bufwrite = 0;
    
}

void nosync_write_queue(int value) {
    assert (g_total_size > 0);
    assert(g_size >= 0);

    g_size++;
    if (g_size > g_total_size) { g_size = g_total_size; }

    g_circbuf[g_bufwrite] = value;
    g_bufwrite = (g_bufwrite + 1) % g_total_size;
} 


int nosync_read_queue(int *out) {
    assert (g_total_size > 0);
    assert (g_size >= 0);
    
    if(g_size == 0) { 
        *out = -1;
        return -1; 
    }
    else {
        g_size--;
        *out = g_circbuf[g_bufread];
        g_bufread = (g_bufread + 1) % g_total_size;
        return 0;
    }

}

void sync_write_queue(int newvalue) {
     pthread_mutex_lock(&mutex);
     nosync_write_queue(newvalue);
     pthread_mutex_unlock(&mutex);
};

int sync_read_queue(int *out){
    pthread_mutex_lock(&mutex);
    int ret = nosync_read_queue(out);
    pthread_mutex_unlock(&mutex);
    return ret;
};


const int CONSUMER_SLEEP_TIME = 1e6 + 1e3;
void *consumer_fn(void *data) {
    while(1) {
        usleep(CONSUMER_SLEEP_TIME);
        printf("---\n");
        printf("consumer: trying to consume..\n");

        int out;
        int ret = sync_read_queue(&out);

        if (ret == 0) {
            printf("consumer: consumed %d | ret: %d\n", out, ret);
        } else {
            printf("consumer: no data in queue\n");
        }
    }
    return NULL;
};

const int PRODUCER_SLEEP_TIME = 1e6;
void *producer_fn(void *data) {
    while(1) {
        printf("---\n");
        int value = rand() % 10;
        printf("producer: starting production |%d|..\n", value);
        sync_write_queue(value);
        printf("done production\n");
        usleep(PRODUCER_SLEEP_TIME);
    }
}
int main() {
    int n = 0;
    printf("num threads: "); scanf("%d", &n);
    init_queue(20);

    if (n < 1) {
        printf("enter num threads > 1. exiting");
        return 1;
    }


    pthread_mutex_init(&mutex, NULL);
    
    pthread_t producer;
    pthread_t *consumers = (pthread_t*)malloc(sizeof(pthread_t) * n);

    pthread_create(&producer, NULL, producer_fn, NULL);

    
    for(int i = 1; i < n; i++) {
        pthread_create(&consumers[i], NULL, consumer_fn, NULL);
    }


    while(1) {}
    return 0;
}
