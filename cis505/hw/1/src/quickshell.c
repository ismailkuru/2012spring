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
//         Author:  Zi Yan (yz), zi.yan@gmx.com
//        Company:  
// 
// ===================================================================
#include <stdio.h>

int main()
{
    //1. read name of file to run
    //2. check existance of the file
    //3. fork 
    //4a. for child, exec the file
    //4b. for father, set alarm(10), and start = times(NULL)
    //5. for father, wait(&status)
    //6. for father, after wait, end = times(NULL) to get child's ending time,
    //   cancel alarm promptly by using alarm(0)
    //7. calculate elapse = end - start, print message according to elapse
    //8. go back to 1
    //
    //For alarm signal, once it is goes off, kill child, and print message

}
