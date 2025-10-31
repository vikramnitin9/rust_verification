#include<stdio.h>

void b()
{

}

int a(int x)
{
    b();
    return 1;
}

void recursive_function()
{
    recursive_function();
}

int main()
{
    a(1);
    b();
    recursive_function();
    return 0;
}