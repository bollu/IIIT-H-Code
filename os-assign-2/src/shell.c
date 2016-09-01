#include <stdio.h>
#include <stdlib.h>

#include <unistd.h>
#include <string.h>
#include <assert.h>
#include <errno.h>

#include <sys/types.h>
#include <sys/wait.h>


#include "parser.h"
#include "context.h"
#include "common.h"

//TODO: This is stateful, need to clean this up dude
void repl_print_prompt(const Context *ctx) {

    char *tilded_dirpath = context_tildefy_directory(ctx, ctx->cwd);
    printf(KGRN "%s" KWHT "@%s:" KBLU "%s" KWHT ">", tilded_dirpath, ctx->username, ctx->hostname);
    free(tilded_dirpath);
}


/* Grammar of REPL syntax  (in EBNF)
 * This can be parsed properly using recursive-descent, but let's strtok for now
 * Expr := ";" | "&" | Command | Command ";" Expr 
 * Command := <name> <args>* <"&">?
 */


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


//
//TODO: clean up. This is doing both printing and
//cleaning up the linked list
void repl_print_ended_jobs(Context *ctx) {

    for (Process *p = ctx->jobs; p != NULL; p = p->next) {

        int status;
        static const int options = WNOHANG;
        pid_t result = waitpid(p->pid, &status, options);

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
    Process *curr_head = ctx->jobs;
    while (curr_head != NULL && curr_head->done) {
        Process *to_free = curr_head;
        curr_head = curr_head->next;
        free(to_free);
    };
    
    ctx->jobs = curr_head;

    //traverse the linked list destroying cleared processes
    for(Process *curr = ctx->jobs; curr != NULL; curr = curr->next) {
        if (curr->next != NULL && curr->next->done) {
            Process *to_free = curr->next;
            curr->next = curr->next->next;
            process_delete(to_free);
            free(to_free);
        }
    }
}




int repl_launch(const Command *command, Context *context) {
    pid_t pid, wpid;

    pid = fork();
    if (pid == 0) {
        // child process
        if (execvp(command->args[0], command->args) == -1) {
            perror("failed to run command");
        }
        exit(EXIT_FAILURE);
    } else if (pid < 0) {
        perror("unable to fork child");
    } 
    // Parent process
    else {
        Process *p = process_new(pid, command);
        if(command->background) {
            context_add_job(context, p);
        }
        //for a foreground process, only display info
        //if some sort of fuckery happens
        else {
            int status;
            wpid = waitpid(pid, &status, WUNTRACED);


            if (!WIFEXITED(status)) {
                char *process_end_str = get_process_end_string(p, status);
                assert(process_end_str != NULL);
                printf("%s", process_end_str);
                free(process_end_str);
            }
        } 
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
void repl_eval(const Command *command, Context *context) {
    switch(command->type) {
        case COMMAND_TYPE_LAUNCH:
            repl_launch(command, context);
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
    };

}

void repl_shutdown(const Context *context) {
    printf("\nGoodbye %s", context->username);
}

int main(int argc, char **argv) {
    Context *ctx = context_new();
    context_update(ctx);

    while(TRUE) {
        repl_print_ended_jobs(ctx);
        clear_ended_jobs(ctx);
        repl_print_prompt(ctx);

        Command *commands = repl_read(ctx);
        
        for(Command *c = commands; c != NULL; c = c->next) {
            repl_eval(c, ctx);
            context_update(ctx);
        }

        for(Command *curr = commands, *next = NULL; curr != NULL;) {
            next = curr->next;
            command_delete(curr);
            free(curr);
            curr = next;
        }


        if(ctx->should_quit) {
            break;
        }


    }
    repl_shutdown(ctx);
    return 0;
}
