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

void print_list(struct Node *head)
{
    struct Node *curr = head;
    while (curr != NULL)
    {
        printf("%s", curr->data);
        if (curr->next != NULL)
        {
            printf("->");
        }
        curr = curr->next;
    }
    printf("->NULL\n");
}


int main()
{
    struct Node *head = malloc(sizeof(struct Node));
    head->data = "Hello";
    head->next = NULL;

    printf("Length of list (before insertion): %d\n", len(head));
    printf("Inserting value %s into list\n", "SECOND");
    insert(head, "SECOND");
    printf("Length of list (after insertion): %d\n", len(head));
    printf("Element %d of list: %s\n", 0, (char *) get(head, 0));
    printf("Element %d of list: %s\n", 1, (char *) get(head, 1));
    print_list(head);
}