//TODO: clear shared memory properly
#include <stdio.h>
#include <pthread.h>
#include <memory.h>
#include <stdlib.h>
#include <unistd.h>
#include <assert.h>
#include <math.h>
#include <sys/ipc.h> 
#include <sys/shm.h> 
#include <sys/wait.h>

const int debug = 0;
pthread_mutex_t mutex;


void mergesort_fn(int *data, int begin, int end);

int alloc_and_attach_shared_mem(int size, int *shmid, int **data) {
    const int USER_RW = 00400 | 00200;
    const int GROUP_RW = 00040 | 00020;

    assert (shmid != NULL);
    assert (data != NULL);
    assert (*data == NULL);


    *shmid = shmget (IPC_PRIVATE, size * sizeof(int), IPC_CREAT | IPC_EXCL | USER_RW | GROUP_RW);
    if (*shmid == -1) {
        perror("shmget failed");
        return -1;
    }

    *data = shmat(*shmid, (void *)0, 0);
    if (*data ==  (int *)-1) {
        perror("shmat failed");
        return -1;
    } else if (debug) {
        printf("data attached at: %p\n", *data);
    }

    return 1;

}


/*
 * remember, this function is working on the child arary of size
*/
void selection_sort(int *data, int size) {
    for(int i = 0; i < size; i++) {
        for(int j = 0; j < size - 1; j++) {
            if (data[j] > data[j + 1]) {
                int temp = data[j];
                data[j] = data[j + 1];
                data[j + 1] = temp;
            }
        }
    }
    /*
    for(int i = begin; i < end; i++) {
        int min = 
    }*/
}

void merge(int *data, int size, int *c1data, int l1, int *c2data, int l2) {
    int p1 = 0, p2 = 0;
    int di = 0;

    assert(size == l1 + l2);

    while(p1 < l1 && p2 < l2) {
        if(c1data[p1] < c2data[p2]) {
            data[di++] = c1data[p1++];
        } else {
            data[di++] = c2data[p2++];
        }

    }

    while(p1 < l1) {
        data[di++] = c1data[p1++];
    }

    while(p2 < l2) {
        data[di++] = c2data[p2++];
    }

    //assert(di == end);

};
int spawn_mergesort_child(int shmid, int begin, int end) {
    int pid = fork();
    if (pid == -1) {
        perror ("*** ERROR unable to fork() ***");
        abort();
    }
    else if (pid == 0) {
        //child
        int *data = shmat(shmid, (int *)0, 0);
        if (data == (int *)-1) {
            perror("*** ERROR shmat failed ***");
            abort();
        }
        mergesort_fn(data, begin, end);
        //detach once used
        shmdt(data);
        abort();
    } else {
        assert(pid > 0);
        return pid;
    }

    assert (0 && "code should never reach here");
};

#define PRINT_MERGE_PREAMBLE { if (debug) { printf("begin: %d | end: %d | ", begin, end); } } ;

void mergesort_fn(int *data, int begin, int end) {
    if (debug) {
        printf("\n==begin: %d | end: %d | START==\n", begin, end);
    }

    const int size = end - begin;
    if (size < 5) {
        if (debug) {
            PRINT_MERGE_PREAMBLE
            printf("selection sorting...\n");
        }
        selection_sort(data, size);

        if (debug) {
            for(int i = 0; i < size; i++) {
                printf("%d ", data[i]);
            }
            printf("\n");
        }
    }
    else {
        if (debug) {
            PRINT_MERGE_PREAMBLE
            printf("recursing...\n");
        }

        int mid = (begin + end) / 2;
        int childpids[2];
        
        int *halves[2];
        int shmid[2];
        int sizes[2] = {mid - begin, end - mid};
        assert(sizes[0] + sizes[1] == size);

        for(int i = 0; i < 2; i++) {
            halves[i] = NULL;
            if(alloc_and_attach_shared_mem(sizes[i], &shmid[i], &halves[i]) == -1) {
                printf("***ERROR unable to allocate shared memory***\n");
                abort();
            };
        }

        for(int i = begin; i < mid; i++) {
            halves[0][i - begin] = data[i - begin];
        }
        for(int i = mid; i < end; i++) {
            halves[1][i - mid] = data[i - begin];
        }
    
        childpids[0] = spawn_mergesort_child(shmid[0], begin, mid);
        childpids[1] = spawn_mergesort_child(shmid[1], mid, end);

        if (debug) {
            PRINT_MERGE_PREAMBLE
            printf("waiting for child...\n");
        }

        for(int i = 0; i < 2; i++) {
            waitpid(childpids[i], NULL, 0);
        };

        merge(data, size, halves[0], sizes[0], halves[1], sizes[1]);

        for(int i = 0; i < 2; i++) {
            shmdt(halves[i]);
            shmctl(shmid[i], IPC_RMID, NULL);
        };

        if (debug) {
            PRINT_MERGE_PREAMBLE
            printf("merged: \n");
            for(int i = 0; i < size; i++) {
                printf("%d ", data[i]);
            }
        }
    }

    if (debug) {
        PRINT_MERGE_PREAMBLE
        printf("END==\n");
    }
}



int main() {
    printf("size of array: ");
    int n;
    scanf("%d", &n);
    
    int shmid;
    int *data;
    if(alloc_and_attach_shared_mem(n, &shmid, &data) == -1) {
        printf("*** ERROR unable to allocate shared memory.***");
        return 1;
    }

    printf("array values: ");
    for(int i = 0; i < n; i++) {
        scanf("%d", &data[i]);
    }

    mergesort_fn(data, 0, n);

    printf("\nMAIN: sorted: ");
    for(int i = 0; i < n; i++) {
        printf("%d ", data[i]);
    }

    shmdt(data);
    shmctl(shmid, IPC_RMID, NULL);

}
