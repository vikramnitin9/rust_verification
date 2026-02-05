#include <stdio.h>
#include <stdlib.h>

struct Node {
    void *data;
    struct Node *next;
};

void insert(struct Node *head, void *data)
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
__CPROVER_requires(head != NULL)
__CPROVER_requires(index >= 0)
__CPROVER_requires(index < len(head))
__CPROVER_ensures(__CPROVER_return_value == ((struct Node *)get(head, index))->data)
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
