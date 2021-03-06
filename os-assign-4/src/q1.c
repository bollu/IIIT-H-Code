#include <stdio.h>
#include <pthread.h>
#include <memory.h>
#include <stdlib.h>
#include <unistd.h>
#include <assert.h>
#include <math.h>

pthread_mutex_t mutex;

typedef struct Produce {
    int reads;
    int value;
} Produce;

Produce produce_new_undefined() {
    Produce p;
    p.reads = -1;
    p.value = -42;
    return p;
}

Produce produce_new(int value) {
    Produce p;
    p.reads = 0;
    p.value = value;
    return p;
}

typedef struct CircBuf {
    Produce *buf;
    int total_size;
} CircBuf;

CircBuf circbuf_new(int total_size) {
    CircBuf c;
    c.total_size = total_size;

    c.buf = (Produce *)malloc(sizeof(Produce) * total_size);
    for(int i = 0; i < total_size; i++) {
        c.buf[i] = produce_new_undefined();
    }

    return c;
}


typedef struct Consumer {
    int id;
    int read_index;
    int num_consumers;
    CircBuf *circbuf;
} Consumer;

Consumer consumer_new(int id, int num_consumers, CircBuf *circbuf) {
    Consumer c;
    c.id = id;
    c.read_index = 0;
    c.num_consumers = num_consumers;
    c.circbuf = circbuf;
    return c;
}

typedef struct Producer {
    int write_index;
    int num_consumers;
    CircBuf *circbuf;
} Producer;

Producer producer_new(int num_consumers, CircBuf *circbuf) {
    Producer p;
    p.write_index = 0;
    p.num_consumers = num_consumers;
    p.circbuf = circbuf;

    return p;
}

int nosync_write_queue(Producer *p, int value) {
    assert (p != NULL);

    Produce *produce = &p->circbuf->buf[p->write_index];
    if (produce->reads == p->num_consumers || 
            produce->reads == -1) {
        *produce = produce_new(value);

        p->write_index++;
        p->write_index %= p->circbuf->total_size;
        return 0;
    } else {
        return -1;
    }
} 


int nosync_read_queue(Consumer *c, int *out) {
    Produce *produce = &c->circbuf->buf[c->read_index];
    if (produce->reads != -1 && produce->reads < c->num_consumers) {
        assert (produce->reads >= 0 && produce->reads <= c->num_consumers);

        *out = produce->value;
        produce->reads++;
        
        assert (produce->reads >= 0 && produce->reads <= c->num_consumers);

        c->read_index++;
        c->read_index %= c->circbuf->total_size;
        return 0;
    } 
    else {
        return -1;
    }

}

int sync_write_queue(Producer *p, int value) {
     //pthread_mutex_lock(&mutex);
     int ret = nosync_write_queue(p, value);
     //pthread_mutex_unlock(&mutex);
     return ret;
};

int sync_read_queue(Consumer *c, int *out) {
    //pthread_mutex_lock(&mutex);
    int ret = nosync_read_queue(c, out);
    //pthread_mutex_unlock(&mutex);
    return ret;
};

void circbuf_debug_print(const CircBuf *circbuf) {
    printf("CIRCBUF: ");
    printf("|");

    for(int i = 0; i < circbuf->total_size; i++) {
        Produce p = circbuf->buf[i];
        printf("r(%d) v(%d) | ", p.reads, p.value);
    }
    printf("\n");
}



const int CONSUMER_SLEEP_TIME = 1e6;
void *consumer_fn(void *vdata) {
    Consumer *c = (Consumer *)vdata;

    while(1) {
        usleep(rand() % (CONSUMER_SLEEP_TIME / 2));

        pthread_mutex_lock(&mutex);
        circbuf_debug_print(c->circbuf);

        printf("CONSUMER(%d): i: %d| reading...", c->id, c->read_index);

        int out;
        int ret = sync_read_queue(c, &out);

        if (ret == 0) {
            printf(" !consumed %d\n", out);
        } else {
            printf(" !no data\n");
        }
        circbuf_debug_print(c->circbuf);
        pthread_mutex_unlock(&mutex);

        usleep(rand() % (CONSUMER_SLEEP_TIME / 2));
    }
    return NULL;
};

const int PRODUCER_SLEEP_TIME = 1e6;

void producer_debug_print(Producer *p) {
    printf("PRODUCER i: %d | num_consumers: %d \n", p->write_index,
            p->num_consumers);
    circbuf_debug_print(p->circbuf);
}

void *producer_fn(void *vdata) {
    Producer *p = (Producer *)vdata;
    while(1) {
        usleep(rand() % (PRODUCER_SLEEP_TIME / 2));

        pthread_mutex_lock(&mutex);
        circbuf_debug_print(p->circbuf);

        int value = rand() % 10;
        printf("PRODUCER: i: %d | producing: %d..", p->write_index, value);
        int ret = sync_write_queue(p,value);

        if (ret == 0) {
            printf(" !produced %d\n", value);
        } else {
            printf(" !buffer full\n");
        }
        
        circbuf_debug_print(p->circbuf);
        pthread_mutex_unlock(&mutex);

        usleep(rand() % (PRODUCER_SLEEP_TIME / 2));
    }
}
int main() {
    int num_consumers = 0;
    printf("num consumers: "); scanf("%d", &num_consumers);

    if (num_consumers < 1) {
        printf("enter num consumers >= 1");
        return 1;
    }

    int circbuf_size;
    printf("size of circular buffer: "); scanf("%d", &circbuf_size);
    CircBuf circbuf = circbuf_new(circbuf_size);


    pthread_mutex_init(&mutex, NULL);
    pthread_t prodthread;
    Producer producer = producer_new(num_consumers, &circbuf);

    pthread_create(&prodthread, NULL, producer_fn, &producer);
    pthread_t *cthreads = (pthread_t*)malloc(sizeof(pthread_t) * num_consumers);
    Consumer *consumer = (Consumer*)malloc(sizeof(Consumer) * num_consumers);

    
    for(int i = 0; i < num_consumers; i++) {
        consumer[i] = consumer_new(i, num_consumers, &circbuf);
        pthread_create(&cthreads[i], NULL, consumer_fn, &consumer[i]);
    }


    while(1) {}
    return 0;
}
