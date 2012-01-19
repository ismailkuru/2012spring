// ===================================================================
// 
//       Filename:  quickshell.c
// 
//    Description:  simple shell program
// 
//        Version:  1.0
//        Created:  01/17/2012 20:33:30
//       Revision:  none
//       Compiler:  gcc
// 
//         Author:  Zi Yan (yz), yanzi@cis.upenn.edu
//        Company:  
// 
// ===================================================================
#include <stdio.h>
#include <stdlib.h>
#include <signal.h>
#include <unistd.h>

void signalarm();
pid_t child;
static state = 0;

int main()
{
    int read_t;
    char buf[512];
    int err;
    int status;

    signal(SIGALRM, signalarm);


    while(1)
    {
        //prompt
        write(1, ">", 1);

        read_t = read(1, buf, 512);

        child = fork();

        if (child == 0)
        {
            //child
            buf[read_t - 1] = 0;
            err = execl(buf, buf, NULL);
	    if (err != 0)
            {
		alarm(0);
                write(1, "execute file error!\n", 20);
                exit(1);
            }
            exit(0);
        }
        else
        {
            //father
            alarm(2);
            wait(&status);
            alarm(0);

            if (status != 0)
                continue;
            switch (state) 
            {
                case 0://< 2 second
                    {
                        write(1, "Wow, that was fast!\n", 20);
                        break;
                    }
                case 1:// 2 second < < 5 second
                    {
                        write(1, "That wasn't very fast\n", 22);
                        break;
                    }
                case 2:// 5 second < < 10 second
                    {
                        write(1, "What took so long?\n", 19);
                        break;
                    }
                case 3:// > 10 second
                    {
                        break;
                    }
            }
            state = 0;
        }

    }
    return 0;

}

void signalarm()
{
    //0-- 2 second, 1-- 5 second, 2-- 10 second
    switch (state)
    {
        case 0:
            {
                state++;
                alarm(3);
                break;
            }
        case 1:
            {
                write(1, "This is taking much too long!\n", 31);
                state++;
                alarm(5);
                break;
            }
        case 2:
            {
                write(1, "I've had enough of this!\n", 25);
                state++;
                kill(child, SIGKILL);
                break;
            }
    }
}
