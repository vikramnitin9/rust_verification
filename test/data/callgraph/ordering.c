void a()
{

}

void b()
{

}

void c()
{
    b();
}

void d()
{
    b();
    a();
    c();
}

int main()
{
    d();
    return 0;
}