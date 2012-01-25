#include<stdio.h>

int main()
{
    write(1, "I come!\n", 8);
    sleep(12);
    write(1, "I died!\n", 8);
    return 0;
}
