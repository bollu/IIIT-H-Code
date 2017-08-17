#include "common.h"

List *_list_new(void *data) {
    List *l = (List *)malloc(sizeof(List));
    l->data = data;
    l->next = NULL;
    return l;
}

void list_add(List **head, void *data) {
    assert(head != NULL);
    if (*head == NULL) {
        *head = _list_new(data);
        return;
    } else {
        List *end = *head;
        while(end->next != NULL) { end = end->next; }
        end->next = _list_new(data);
    }

}

