#include <stdio.h>
#include <stdlib.h>

#include <unistd.h>
#include <string.h>
#include <assert.h>
#include <errno.h>

#include <sys/types.h>
#include <sys/wait.h>
#include <sys/stat.h> 
#include <fcntl.h>
#include <signal.h>

#include "parser.h"
#include "context.h"
#include "common.h"


//TODO: This is stateful, need to clean this up dude
void repl_print_prompt(const Context *ctx) {

    char *tilded_dirpath = context_tildefy_directory(ctx, ctx->cwd);
    printf(KGRN "%s" KWHT "@%s:" KBLU "%s" KWHT ">", tilded_dirpath, ctx->username, ctx->hostname);
    free(tilded_dirpath);
}


//holy memory juggling batman :/
give char* get_process_end_string(const Process *p, int status) {
    char SUCCESS_EXIT_STR[] = "Clean exit";
    char COREDUMP_EXIT_STR[] = "Core dumped";
    char SIGNAL_EXIT_STR[] = "Died due to signal";
    char UNKNOWN_EXIT_STR[] = "Unknown exit. check get_process_status_str.";


    char signal_str[1024] = "\0";
    if (WIFEXITED(status)) {
        sprintf(signal_str, "%s", SUCCESS_EXIT_STR);
    }
    else if (WIFSIGNALED(status)) {
        if (WCOREDUMP(status)) {
            sprintf(signal_str, "%s", COREDUMP_EXIT_STR);
        }
        else {
            sprintf(signal_str, "%s(%d)", SIGNAL_EXIT_STR, WTERMSIG(status));
        }

    }
    else {
        sprintf(signal_str, "%s", UNKNOWN_EXIT_STR);
    }

    char *dest = malloc(sizeof(char) * 1024);
    sprintf(dest, "Process [%s] with pid [%d] ended. Exit: %s\n",
            p->pname, p->pid, signal_str);

    assert(dest != NULL);

    return dest;

}

//TODO: clean up. This is doing both printing and
//cleaning up the linked list
void repl_print_ended_jobs(Context *ctx) {
    for (Process *p = ctx->background_jobs; p != NULL; p = p->next) {

        int status;
        static const int options = WNOHANG;
        pid_t result = waitpid(- p->pid, &status, options);

        if (result == -1) {
            //this is aclled when the process has nothing to wait for
            if (errno != ECHILD) {
                assert(FALSE && "unexpected failure of waitpid");
            }
        }

        if (result == -1 || result != 0) {
            p->done = TRUE;
        }

        if (result != 0) {
            char *process_end_str = get_process_end_string(p, status);
            assert(process_end_str != NULL);
            printf("%s", process_end_str);
        }
    }
}

void clear_ended_jobs(Context *ctx) {

    //find the new head of the linked list
    Process *curr_head = ctx->background_jobs;
    while (curr_head != NULL && curr_head->done) {
        Process *to_free = curr_head;
        curr_head = curr_head->next;
        free(to_free);
    };

    ctx->background_jobs = curr_head;

    //traverse the linked list destroying cleared processes
    for(Process *curr = ctx->background_jobs; curr != NULL; curr = curr->next) {
        if (curr->next != NULL && curr->next->done) {
            Process *to_free = curr->next;
            curr->next = curr->next->next;
            //HACK!
            //process_delete(to_free);
            free(to_free);
        }
    }
}


int does_process_exist(int pid) {
    return kill(pid, 0) == 0;
}

void update_stopped_jobs(Context *context) {
    if (context->debug_mode) {
        printf("***updating stopped jobs***\n");
    }

    {
        //go through the stopped processes, removing the ones
        //that don't exist
        Process *prev = NULL;
        for (Process *p = context->stopped_jobs; p != NULL;)
        {
            Process *const next = p->next;
            if (!does_process_exist(p->pid) || p->done == TRUE) {
                if (context->debug_mode) {
                    printf("\t[%s]:[%d] DOES NOT exist\n", p->pname, p->pid);
                }
                process_delete(p);
                free(p);

                if (prev == NULL) {
                    context->stopped_jobs = next;
                } else {
                    prev->next = next;
                }
                p = next;            
            }
            else {
                if (context->debug_mode) {
                    printf("\t[%s]:[%d] exists\n", p->pname, p->pid);
                }
                prev = p;
                p = next;
            }
        }
    }   

    //go through foreground jobs, removing the ones that
    //don't exist (i.e, have ended) and pushing the ones that
    //have stopped into the stopped queue
    Process *prev = NULL;
    for(Process *p = context->foreground_jobs; p != NULL;) {
        if (context->debug_mode) {
            printf("\tchecking job: [%d]:[%s]\n", p->pid, p->pname);
        }
        Process *const next = p->next;

        //process does not exist
        if (!does_process_exist(p->pid)) {
            if (context->debug_mode) {
                printf("\t\tdoes not exist\n");
            }
            process_delete(p);
            free(p);

        } 
        //process exists, is stopped
        else {
            if (context->debug_mode) {
                printf("\t\tstopped\n");
            }
            context_add_stopped_job(context, p);
        }

        //remove process from list
        if (prev == NULL) {
            context->foreground_jobs = next;
        } else {
            prev->next = next;
        }

        p = next;
    }

    if (context->debug_mode) {
        printf("***stopped jobs:***\n");

        for(Process *p = context->stopped_jobs; p != NULL; p = p->next) {
            printf("[%d]:[%s]\n", p->pid, p->pname);
        }
    }

};

static const int WRITE_PIPE_INDEX = 1; static const int READ_PIPE_INDEX = 0;


//returns the pid of the launched process, or -1 if no process was
//launched
int single_command_launch(const Command *command, int *pipe_back, int *pipe_forward, const Context *context){
    pid_t pid = fork();

    if (pid == 0) {
        /* CHILD */
        //reset signal handlers
        signal(SIGINT,  SIG_DFL);   // ctrl-c
        signal(SIGTSTP, SIG_DFL);  // ctrl-z
        signal(SIGCHLD, SIG_DFL);  //);  // Terminated or stopped child

        //we need to pull input from our back
        if (pipe_back != NULL) {
            if (context->debug_mode) {
                printf("\n>%s: pipe back\n", command->args[0]);
            }
            dup2(pipe_back[READ_PIPE_INDEX], STDIN_FILENO);
            close(pipe_back[WRITE_PIPE_INDEX]);
            close(pipe_back[READ_PIPE_INDEX]);
        }

        //we need to push to our front
        if (pipe_forward != NULL) {
            if (context->debug_mode) {
                printf("\n>%s: pipe forward\n", command->args[0]);
            }

            dup2(pipe_forward[WRITE_PIPE_INDEX], STDOUT_FILENO);
            close(pipe_forward[WRITE_PIPE_INDEX]);
        }

        // IO redirection
        if (command->redirect_output_path) {
            int flags = 0;

            //open file correctly based on
            //redirection needed or not
            if (command->append_redirect_output == 1) {
                flags = O_CREAT | O_APPEND | O_WRONLY;
            }
            else {
                flags = O_CREAT | O_TRUNC | O_WRONLY;
            }
            assert (flags != 0);

            int fd = open(command->redirect_output_path, flags, 0600);
            if (fd == -1) {
                perror("REDIRECTION ERROR: ");
                abort();
                return -1;
            }
            
            //replace stdout
            dup2(fd, STDOUT_FILENO); 
            close(fd);
        }
        if (command->redirect_input_path) {
            //open read file
            int fd = open(command->redirect_input_path, O_RDONLY);
            if (fd == -1) {
                perror("REDIRECTION ERROR: ");
                abort();
                return -1;
            }
            
            //replace stdin
            dup2(fd, STDIN_FILENO); 
            close(fd);
        }

        // child process
        if (execvp(command->args[0], command->args) == -1) {
            perror("failed to run command");
            abort();
            return -1;
        }



    } else if (pid < 0) {
        perror("unable to fork child");
        abort();
        return -1;
    } 
    // Parent process
    return pid;
};


void wait_for_process_start(Process *p) {
    int status;
    pid_t pid;

    do {
        pid = waitpid (WAIT_ANY, &status, WUNTRACED);
    } while (pid == -1);
}

void wait_for_process_termination(Process *p) {
    int wpid;
    int status;
    wpid = waitpid(- p->pid, &status, WUNTRACED);

    if (!WIFEXITED(status)) {
        char *process_end_str = get_process_end_string(p, status);
        assert(process_end_str != NULL);
        free(process_end_str);
    }
};

int repl_launch(const Command *command, int *prev_pipe_filedesc, Context *context) {
    assert (command != NULL);

    static const int N = 1024; //max number of things that can be pipes
    int pipe_filedesc[N][2];

    int count = 0;

    for(const Command *c = command; c != NULL; c = c->pipe, count++) {
        //generate a pair of input and output pipes
        pipe(pipe_filedesc[count]);
    }

    int pgid = -1;

    int launch_count = 0;
    for(const Command *c = command; c != NULL; c = c->pipe, launch_count++) {
        int *pipe_back = NULL;
        int *pipe_forward = NULL;

        if (launch_count > 0) {
            pipe_back = pipe_filedesc[launch_count - 1];
        } 

        if (launch_count < count - 1) {
            pipe_forward = pipe_filedesc[launch_count];
        }

        int pid = single_command_launch(c, pipe_back, pipe_forward, context);

        if (pid != -1) {
            //figure out why this assert is failing
            assert(pid > 0 && "process is legal child");
            //make pgid the id of the first child process launched
            if (pgid == -1) { pgid = pid; }
            if (context->debug_mode) {
                printf("pgid: %d | pid: %d\n", pgid, pid);
            }

            //move child into custom process group
            assert (pgid != -1);
            if (setpgid(pid, pgid) == -1) {
                perror("setpgid returned -1");
                assert(FALSE && "setpgid failed");
            };

            Process *p = process_new(pid, context->next_jobid, command);
            context->next_jobid += 1;
            
            //in a series of piped commands, only add the first command
            if (launch_count == 0) {
                if (command->background)
                {
                    context_add_background_job(context, p);
                } else {
                    context_add_foreground_job(context, p);
                }
            }

        } else {
            perror("unable to launch process");
            return -1;
        }

        if (pipe_back != NULL) {
            close(pipe_back[WRITE_PIPE_INDEX]);
        }
    }


    //launch separate process group
    assert (pgid != -1);
    if (-1 == tcsetpgrp(STDIN_FILENO, pgid)) {
        perror("tcsetpgrp failed");
        assert(FALSE && "tcsetpgrp failed");
    } 

    //wait for process and print status of all foreground jobs
    for(Process *p = context->foreground_jobs; p != NULL;) { 
        wait_for_process_termination(p);
        Process *next = p->next;
        p = next;
    }

    return 1;
}

int repl_quit(Context *ctx) {
    ctx->should_quit = TRUE;
    return 0;
}

int repl_cd(const Command *command) {
    if (command->num_args != 1) {
        return -1;
    }

    int status = chdir(command->args[0]);

    if (status == 0) {
        return 0;
    }
    else{
        assert(status == -1);
        fprintf(stderr, "\n[cd %s] failed. ", command->args[0]);
        if (errno == EACCES) {
            fprintf(stderr, "Search denied to path\n");
        }
        else if (errno == EFAULT) {
            fprintf(stderr, "Path is outside process space\n");
        }
        else if (errno == EIO) {
            fprintf(stderr, "I/O error occured when reading filesystem\n");
        }
        else if (errno == ELOOP) {
            fprintf(stderr, "Too many symbolic links encountered\n");
        }
        else if (errno == ENAMETOOLONG) {
            fprintf(stderr, "Path too long");
        }
        else if (errno == ENOENT) {
            fprintf(stderr, "Directory does not exist\n");
        }
        else if (errno == ENOTDIR) {
            fprintf(stderr, "Some part of path is not a directory\n");
        }
        else {
            fprintf(stderr, "Unknown failure. status: %d. Please report this!\n", status);
        }
    }

    return -1;
};


int repl_pwd(const Command *command, const Context *context) {
    if (command->num_args != 0) {
        return -1;
    }
    printf("%s\n", context->cwd);
    return 0;
};

int repl_echo(const Command *command) {
    for(int i = 0; i < command->num_args; i++) {
        printf("%s", command->args[i]);
    }
    printf("\n");
    return 0;
}

int repl_pinfo(const Command *command, const Context *context) {

    int pid = -1;
    if (command->num_args > 1) {
        printf("usage: pinfo [pid of process]\n");
        return -1;
    } else if (command->num_args == 0){
        pid = getpid();
    }
    else {
        assert (command->num_args == 1);
        pid = atoi(command->args[0]);
    }

    printf("pid: %d", pid);

    char stat_filepath[1024];
    sprintf(stat_filepath, "/proc/%d/stat", pid);

    FILE *stat_file = fopen(stat_filepath, "r");
    char data[2048];
    fread(data, 1, 2048, stat_file);

    //ignore the first result (the PID)
    strtok(data, " ");
    const char *pname = strtok(NULL, " ");
    printf("\nname: %s", pname);
    const char *pstatus = strtok(NULL, " ");
    printf("\nstatus: %s", pstatus);
    printf("\n");

    return 0;
}

int repl_fg(const Command *command, Context *context) {
    if (command->num_args != 1) {
        printf("usage: fg <command-jobid>\n");

        return -1;
    }

    assert(command->num_args == 1);
    char *endptr = NULL;
    const long int jobid = strtol(command->args[0], &endptr, 10);

    if (endptr == command->args[0]) {
        printf("invalid jobid given: %s\n", endptr);
    } else {
        //first look in stopped jobs
        Process *prev = NULL;
        for(Process *p = context->stopped_jobs; p != NULL;) {
            Process *const next = p->next;
            if(p->jobid == jobid) {
                printf("found child process [%s] with jobid[%d]. "
                        "Continuing...\n", p->pname, p->jobid);

                //remove job from stopped jobs
                if (prev == NULL) {
                    context->stopped_jobs = next;
                } else {
                    prev->next = next;
                }

                //FIXME: pull info from process
                const int is_background = 0;
                //TODO: this needs to be delicate
                //add to the current chain
                if (is_background) {
                    context_add_background_job(context, p);
                } else {
                    context_add_foreground_job(context, p);
                }

                //launch separate process group
                kill(- p->pid, SIGCONT);

                //give terminal access
                if (-1 == tcsetpgrp(STDIN_FILENO, p->pid)) {
                    perror("tcsetpgrp failed");
                    assert(FALSE && "tcsetpgrp failed");
                } 
                

                //wait for termination if this is the foreground process
                if (!is_background) {
                    wait_for_process_termination(p);
                }
                return 0;

            }
            else {
                if (context->debug_mode) {
                    printf("process jobid[%d]:name[%s]"
                    " is not the correct one.\n",
                        p->jobid, p->pname);
                }

                prev = p;
                p = next;
            }
        }

        //could not find a process
        printf("unable to find job with jobid: [%ld]\n", jobid);
    }

    return 0;
}


int repl_listjobs(const Command *command, const Context *context) {
    printf(KBLU "\n***background***\n" KNRM );
    for(Process *p = context->background_jobs; p != NULL; p = p->next) {
        assert(p->pname != NULL);
        printf("job:[%d] pid:[%d] name:[%s]\n", p->jobid, p->pid, p->pname);
    }

    printf(KBLU "\n***stopped***\n" KNRM);
    for(Process *p = context->stopped_jobs; p != NULL; p = p->next) {
        assert(p != NULL);
        assert(p->pname != NULL);
        printf("job:[%d] pid:[%d] name:[%s]\n", p->jobid, p->pid, p->pname);
    }

    return 0;
}

int repl_killallbg(const Command *command, const Context *context) {
    printf(KBLU "***killing background jobs***" KNRM "\n");

    for (Process *p = context->background_jobs; p != NULL; p = p->next)
    {
        if (kill(p->pid, SIGKILL) == 0) {
            p->done = TRUE;
            printf("killed" KGRN "job:[%d] pid:[%d] name:[%s]" KNRM "\n", p->jobid, p->pid, p->pname);
        } else {
            perror("unable to kill process");
        }
    }


    printf(KBLU "***killing stopped jobs***" KNRM "\n");
    for(Process *p = context->stopped_jobs; p != NULL; p = p->next) {
        if (kill(p->pid, SIGKILL) == 0) {
            p->done = TRUE;
             printf("killed" KGRN "job:[%d] pid:[%d] name:[%s]" KNRM "\n", p->jobid, p->pid, p->pname);
        } else {
            printf("failed to kill "
            KGRN "job:[%d] pid:[%d] name:[%s]" KNRM "\n", p->jobid, p->pid, p->pname);
            perror("unable to kill process");
        }
    }

    

    return 0;
}

int repl_sendsig(const Command *command, const Context *context) {
    if (command->num_args != 2) {
        printf(KRED "usage: sendsig <jobid> <signal>\n" KNRM);
        return -1;
    }

    char *endptr = NULL;
    const long int jobid = strtol(command->args[0], &endptr, 10);
    
    //error out 
    if (endptr == command->args[0]) {
        printf(KRED "invalid jobid given: %s\n" KNRM, endptr);
        return -1;
    }

    const long int signal = strtol(command->args[1], &endptr, 10);
    if (endptr == command->args[1]) {
        printf(KRED "invalid signal given: %s\n" KNRM, endptr);
        return -1;
    }

    Process *target = NULL;
    for (Process *p = context->background_jobs; p != NULL; p = p->next)
    {
        if (p->jobid == jobid) {
            target = p;
            break;
        }
    }
    if (target == NULL){
        for (Process *p = context->stopped_jobs; p != NULL; p = p->next) {
            if (p->jobid == jobid) {
                target = p;
                break;
            }
        }
    }

    if (target == NULL) {
        printf(KRED "unable to find job with id: [%ld]\n" KNRM, jobid);
        return 0;
    }
    else {
        
        printf("sending signal"KGRN"[%ld]"KNRM" to process "
            KGRN"job:[%d] pid:[%d] name: [%s]"KNRM"...\n", signal, target->jobid, target->pid, target->pname);

        if (kill(target->pid, signal) == -1) {
            perror(KRED "signal send failed\n" KNRM);
        } else {
            printf("successfully sent signal");
        }
    }
    
    return 0;
}

void repl_eval(const Command *command, Context *context) {
    switch(command->type) {
        case COMMAND_TYPE_LAUNCH:
            repl_launch(command, NULL, context);
            break;
        case COMMAND_TYPE_CD:
            repl_cd(command);
            break;
        case COMMAND_TYPE_PWD:
            repl_pwd(command, context);
            break;
        case COMMAND_TYPE_ECHO:
            repl_echo(command);
            break;
        case COMMAND_TYPE_EXIT:
            repl_quit(context);
            break;
        case COMMAND_TYPE_PINFO:
            repl_pinfo(command, context);
            break;
        case COMMAND_TYPE_FG:
            repl_fg(command, context);
            break;
        case COMMAND_TYPE_LISTJOBS:
            repl_listjobs(command, context);
            break;
        case COMMAND_TYPE_KILLALLBG:
            repl_killallbg(command, context);
            break;
        case COMMAND_TYPE_SENDSIG:
            repl_sendsig(command, context);
            break;
        };
}

void repl_shutdown(const Context *context) {
    printf("\nGoodbye %s", context->username);
}

Context *g_ctx;

void sigint_handler(int status) {
    if (g_ctx->debug_mode) {
        printf("\n>received SIGINT\n");
    }
}
void sigtstp_handler(int status) {
    printf("\n>RECEIVED SIGTSTP\n");
    return;
}
void sigchld_handler(int status) {
    if (g_ctx->debug_mode) {
        printf("\n>received SIGCHLD\n");
    }
}
void sigquit_handler(int status) { 
    if (g_ctx->debug_mode) {
        printf("\n>received SIGQUIT\n");
    }
}

int main(int argc, char **argv) {

    signal(SIGINT,  sigint_handler);   // ctrl-rtc
    signal(SIGTSTP, sigtstp_handler);  // ctrl-z
    signal(SIGCHLD, sigchld_handler);  // Terminated or stopped child
    
    g_ctx = context_new();
    //
    // This one provides a clean way to kill the shell
    //
    //signal(SIGQUIT, sigquit_handler); 

    if (argc >= 2) {
        if (!strcmp(argv[1], "--debug") || !strcmp(argv[1], "-d")) {
            g_ctx->debug_mode = TRUE;
        }
    }
    context_update(g_ctx);

    while(TRUE) {
        repl_print_ended_jobs(g_ctx);
        clear_ended_jobs(g_ctx);
        update_stopped_jobs(g_ctx);
        repl_print_prompt(g_ctx);


        signal(SIGTTOU, SIG_IGN);
        if(tcsetpgrp(STDIN_FILENO, getpgid(0)) == -1) {
            perror("unable to gain control of STDIN_FILENO");
        }
        signal(SIGTTOU, SIG_DFL);

        int status = 1; char *error_message = NULL;
        Command *commands = repl_read(g_ctx, &status, &error_message);

        if (status == -1) {
            assert(error_message != NULL);
            printf("error: %s\n", error_message);
        } else {

            for(Command *c = commands; c != NULL; c = c->next) {
                if (g_ctx->debug_mode) {
                    printf("***debug command info: \n***");
                    command_print(c);
                    printf("\n");
                }
                repl_eval(c, g_ctx);
                context_update(g_ctx);
            }

            for(Command *curr = commands, *next = NULL; curr != NULL;) {
                next = curr->next;
                command_delete(curr);
                free(curr);
                curr = next;
            }


            if(g_ctx->should_quit) {
                break;
            }
        }
    }
    repl_shutdown(g_ctx);
    return 0;
}
