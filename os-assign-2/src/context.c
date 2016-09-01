#include "common.h"
#include "parser.h"

give Process* process_new(int pid, const Command *command) {
    Process *p = (Process *)malloc(sizeof(Process));
    p->pid = pid;
    p->next = NULL;
    p->done = FALSE;


    assert (command->type == COMMAND_TYPE_LAUNCH && 
            command->num_args > 0 &&
            command->args[0] != NULL);
    
    p->pname =(char *)malloc(strlen(command->args[0]));
    strcpy(p->pname, command->args[0]);

    return p;
}

void process_delete(take Process *p) {
    free(p->pname);
}


/* *** Context Impl *** */
Context *context_new() {
    Context *ctx = (Context*)malloc(sizeof(Context));
    ctx->should_quit = FALSE;
    ctx->username[0] = ctx->hostname[0] = ctx->cwd[0] = '\0';
    ctx->debug_mode = FALSE;

    
    getcwd(ctx->homedir, MAX_HOMEDIR_LENGTH); 
    context_update(ctx);
    return ctx;
}

void context_update(Context *context) {
    getcwd(context->cwd, MAX_CWD_LENGTH); 
    gethostname(context->hostname, MAX_HOSTNAME_LENGTH);
    strncpy(context->username, getlogin(), MAX_USERNAME_LENGTH);
}

void context_add_job(Context *context, Process *p) {
    if (context->jobs == NULL) {
        context->jobs = p;
    }  else {
        Process *last = context->jobs;
        for(; last->next != NULL; last = last->next){};
        last->next = p;
    }
}
/* *** Command Implementation *** */

/* *** REPL Implementation *** */

give char* context_tildefy_directory(const Context *ctx, const char *dirpath) {
   char *substr = strstr(dirpath, ctx->homedir);

   if (substr != NULL) {
       //skip the home path
       substr += strlen(ctx->homedir);
       char *new_dirpath = malloc(strlen("~") + strlen(substr) + 1);
       sprintf(new_dirpath, "~%s", substr);

       return new_dirpath;
   } else {
        char *new_dirpath = malloc(strlen(dirpath) + 1);
        strcpy(new_dirpath, dirpath);
        
        return new_dirpath;
   }
}
