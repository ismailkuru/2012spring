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
//state indicating how and when the child dies
static state = 0;

int main()
{
    int read_t;
    int write_t;
    char buf[512];
    int err;
    int status;

    //set up alarm signal call back function
    signal(SIGALRM, signalarm);


    while(1)
    {
        //reset state
        state = 0;

        //prompt
        write(STDOUT_FILENO, ">", 1);

        //get user input from standard output, at most 512 chars
        read_t = read(STDIN_FILENO, buf, 512);
        if (read_t == -1)
        {
            write(STDERR_FILENO, "can't read msg!\n", 16);
            _exit(1);
        }

        //get EOF
        if (read_t == 0)
            break;

        child = fork();
        if (child == -1)
        {
            write(STDERR_FILENO, "can't fork a child!\n", 20);
            _exit(1);
        }

        if (child == 0)
        {
            //child
            //remove last newline symbol
            buf[read_t - 1] = 0;
            //execute corresponding command or file
            err = execl(buf, buf, NULL);
            if (err != 0)
            {
                write(STDERR_FILENO, "execute file error!\n", 20);
                _exit(1);
            }
            _exit(0);
        }
        else
        {
            //father
            //set first alarm
            alarm(2);
            //wait for child's death
            wait(&status);
            //cancel alarm, because this round is over
            alarm(0);

            //child abnormally exit, skip msg printing
            if (status != 0)
                continue;
            //print msg according to the state which inidicates the used time
            switch (state) 
            {
                case 0://< 2 second
                    {
                        write(STDOUT_FILENO, "Wow, that was fast!\n", 20);
                        break;
                    }
                case 1:// 2 second < < 5 second
                    {
                        write(STDOUT_FILENO, "That wasn't very fast\n", 22);
                        break;
                    }
                case 2:// 5 second < < 10 second
                    {
                        write(STDOUT_FILENO, "What took so long?\n", 19);
                        break;
                    }
                case 3:// > 10 second
                    {
                        break;
                    }
                default:
                    {
                        write(STDOUT_FILENO, 
                              "internal error: unexpected state!\n", 34);
                    }
            }
        }

    }
    return 0;

}

void signalarm()
{
    //state value:0-- 2 second, 1-- 5 second, 
    //            2-- 10 second, 3-- child is murdered 
    switch (state)
    {
        case 0:
            {
                state++;
                //set alarm incrementally
                alarm(3);
                break;
            }
        case 1:
            {
                write(STDOUT_FILENO, "This is taking much too long!\n", 31);
                state++;
                //set alarm incrementally
                alarm(5);
                break;
            }
        case 2:
            {
                write(STDOUT_FILENO, "I've had enough of this!\n", 25);
                state++;
                kill(child, SIGKILL);
                break;
            }
        default:
            {
                write(STDOUT_FILENO, 
                      "internal error: unexpected state!\n", 34);

            }
    }
}
