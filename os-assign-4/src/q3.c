#include <stdio.h>
#include <pthread.h>
#include <memory.h>
#include <stdlib.h>
#include <unistd.h>
#include <assert.h>
#include <math.h>

typedef int EVMId;
typedef int RobotId;
static const int R = 200;
static const int E = 200;

struct Booth;
typedef struct Booth Booth;

typedef enum Bool {
    False = 0,
    True = 1,
} Bool;

typedef struct Evm {
    int id;
    int nslots;
    int noccupied;
    Booth *booth;
} Evm;

Evm evm_new(int id, int nslots, Booth *booth) {
    Evm evm;
    evm.id = id;
    evm.nslots = nslots;
    evm.noccupied = 0;
    evm.booth = booth;
    return evm;
}


typedef struct Robot {
    int id;

    int voterid;

    Evm *assigned_evm;

    Booth *booth;
} Robot;

Robot robot_new(int id, Booth *booth) {
    Robot r;
    r.id = id;
    r.booth = booth;
    r.assigned_evm = NULL;
    r.voterid = -1;
    return r;
}

struct Booth {
    pthread_mutex_t mutex;
    Evm evms[E];
    int nevms;
    Evm *free_evm;

    Robot robots[R];
    int nrobots;

    int n_unassigned_voters;
    int n_votes_to_cast;
};

Booth booth_new(int nevms, int nrobots, int n_unassigned_voters) {
    Booth booth;
    pthread_mutex_init(&booth.mutex, NULL);
    booth.free_evm = 0;
    booth.nevms = nevms;
    booth.nrobots = nrobots;
    booth.n_unassigned_voters = n_unassigned_voters;
    booth.n_votes_to_cast = n_unassigned_voters;

    return booth;
}

void booth_lock(Booth *booth) {
    pthread_mutex_lock(&booth->mutex);
}


void booth_unlock(Booth *booth) {
    pthread_mutex_unlock(&booth->mutex);
}

int booth_get_voter(Booth *booth) {
    assert (booth->n_unassigned_voters >= 0);
    if (booth->n_unassigned_voters == 0) {
        return -1;
    }

    booth_lock(booth);
    int voterid = booth->n_unassigned_voters;
    booth->n_unassigned_voters--;
    booth_unlock(booth);
    return voterid;
}


const int EVM_SLEEP_TIME = 0;
void polling_ready_evm(Booth *booth, Evm *evm) {
    assert(booth != NULL);

    while(1) {
        booth_lock(booth);

        if (evm->noccupied == evm->nslots) {
            booth_unlock(booth);
            return;
        }

        if (booth->free_evm == NULL) {
            booth->free_evm = evm;
            booth_unlock(booth);
            return;
        }

        booth_unlock(booth);
        usleep(EVM_SLEEP_TIME);
    }
}

Evm* voter_wait_for_evm(Booth *booth) {
    while(1) { 
        booth_lock(booth);

        //allocate a slot and return
        Evm *free_evm = booth->free_evm;
        if (free_evm != NULL) {
            assert(free_evm->noccupied >= 0);
            assert(free_evm->noccupied < free_evm->nslots);

            free_evm->noccupied++;

            if (free_evm->noccupied == free_evm->nslots) {
                booth->free_evm = NULL;
            }

            booth_unlock(booth);
            return free_evm;
        }

        booth_unlock(booth);
    }

    assert(False && "should never reach here");
}

void voter_in_slot(Booth *booth, Robot *r) {
    booth_lock(booth);

    assert(r->assigned_evm != NULL);
    printf("VOTE: robot %d | voter  %d | evm %d\n", r->id,
            r->voterid, r->assigned_evm->id);
    r->assigned_evm->noccupied--;
    r->assigned_evm = NULL;
    
    booth->n_votes_to_cast--;
    booth_unlock(booth);
    return;
}


void* robot_fn(void *data) {
    Robot *r = (Robot *)data;

    Booth *booth = r->booth;

    while(1) {
        r->voterid = booth_get_voter(booth);
    
        //no more voters present
        if (r->voterid == -1) {
            return NULL;
        }

        printf("ROBOT %d <= voter %d\n", r->id, r->voterid);
        r->assigned_evm = voter_wait_for_evm(booth);
        voter_in_slot(booth, r);
    }

    return NULL;
}

void* evm_fn(void *data) {
    Evm *e = (Evm *)data;

    while(e->booth->n_votes_to_cast > 0) {

        assert(e->noccupied >= 0 && e->noccupied <= e->nslots);

        if(e->noccupied < e->nslots) {
            polling_ready_evm(e->booth, e);
            printf("EVM: %d  | free\n", e->id);
        } else {
            //printf("EVM: %d | fully occupied\n", e->id);
        }

    }
    return NULL;
};


int main() {
    int nevms = 100;
    int nrobots = 100;
    int n_unassigned_voters = 100;

    assert (nevms < E);
    assert (nrobots < R);

    Booth booth = booth_new(nevms, nrobots, n_unassigned_voters);
    
    const int nslots = 1;
    for(int i = 0; i < nevms; i++) {
        booth.evms[i] = evm_new(i, nslots, &booth);
        pthread_t thread;
        pthread_create(&thread, NULL, &evm_fn, &booth.evms[i]);
    }

    for(int i = 0; i < nrobots; i++) {
        booth.robots[i] = robot_new(i, &booth);
        pthread_t thread;
        pthread_create(&thread, NULL, &robot_fn, &booth.robots[i]);
    }

    while(booth.n_votes_to_cast > 0) {};
}
