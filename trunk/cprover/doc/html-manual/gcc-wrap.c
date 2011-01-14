#include <string.h>
#include <unistd.h>
#include <sys/types.h>
#include <errno.h>
#include <stdio.h>
#include <sys/wait.h>
#include <stdlib.h>

void run(const char *what, char *const argv[])
{
  pid_t childpid; /* variable to store the child's pid */
  int retval;     /* child process: user-provided return code */

  /* now create new process */
  childpid = fork();
    
  if(childpid>=0) /* fork succeeded */
  {
    if(childpid==0) /* fork() returns 0 to the child process */
    {
      execvp(what, argv);
      /* usually no return */
      fprintf(stderr, "execp %s failed\n", what);
      exit(1);
    }
    else /* fork() returns new pid to the parent process */
    {
      int status;     /* parent process: child's exit status */
      wait(&status); /* wait for child to exit, and store its status */
      int code=WEXITSTATUS(status);
      if(code!=0) exit(code);
    }
  }
  else /* fork returns -1 on failure */
  {
    perror("fork failed"); /* display error message */
    exit(1);
  }
}
 
int main(int argc, char * const argv[])
{
  // do original call
  run("gcc", argv);
  
  // now do preprocessing call
  char **new_argv=malloc(sizeof(char *)*(argc+1));
  
  _Bool compile=0;
  _Bool assemble=0;
  _Bool next_is_o=0;
  
  unsigned i;

  for(i=0; i<argc; i++)
  {
    char *arg=argv[i];

    if(next_is_o)
    {
      char *tmp=malloc(strlen(arg)+strlen(".i"));
      strcpy(tmp, arg);
      strcat(tmp, ".i");
      arg=tmp;
      next_is_o=0;
    }
    else if(strcmp(arg, "-c")==0)
    {
      arg="-E";
      compile=1;
    }
    else if(strcmp(arg, "-o")==0)
    {
      next_is_o=1;
    }
    else if(strcmp(arg, "-D__ASSEMBLY__")==0)
    {
      assemble=1;
    }

    new_argv[i]=arg;
  }
  
  new_argv[argc]=NULL;
  
  if(compile && !assemble)
  {
    run("gcc", new_argv);
  }
    
  return 0;
}
