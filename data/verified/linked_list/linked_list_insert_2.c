#include <stdio.h>
#include <stdlib.h>

struct Node {
    void *data;
    struct Node *next;
};

void insert(struct Node *head, void *data)
__CPROVER_requires(head != NULL)
__CPROVER_requires(__CPROVER_is_fresh(data, sizeof(void *)))
__CPROVER_ensures(head != NULL)
__CPROVER_ensures(__CPROVER_old(head) != NULL)
__CPROVER_ensures(__CPROVER_old(head)->next != NULL || __CPROVER_old(head)->next == __CPROVER_old(__CPROVER_old(head)->next))
__CPROVER_ensures(__CPROVER_old(head)->next != NULL ==> __CPROVER_old(head)->next->data == data)
{
    struct Node *node = malloc(sizeof(struct Node));
    node->data = data;
    node->next = NULL;

    struct Node *curr = head;
    while (curr->next != NULL)
    {
        curr = curr->next;
    }
    curr->next = node;
}

int len(struct Node *head)
{
    int size = 0;
    struct Node *curr = head;
    while (curr != NULL)
    {
        size++;
        curr = curr->next;
    }
    return size;
}

void* get(struct Node *head, int index)
{
    int i = 0;
    struct Node *curr = head;
    while (i != index)
    {
        i++;
        curr = curr->next;
    }
    return curr->data;
}
