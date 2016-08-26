#include <stdio.h>
#include <stdlib.h>



#include <unistd.h>
#include <string.h>
#include <assert.h>
#include <errno.h>

//copied neat idea from ISL library! 
//returns a new block of memory
#define give
//takes a block of memory and frees it
#define take

typedef enum boolean{
    FALSE = 0,
    TRUE = 1
} boolean;


struct Process;

/* *** Context *** */
static const int MAX_CWD_LENGTH = 1024 * 20;
static const int MAX_HOMEDIR_LENGTH = 1024 * 20;
static const int MAX_USERNAME_LENGTH = 1024 * 20;
static const int MAX_HOSTNAME_LENGTH = 1024 * 20;
typedef struct  {
    char cwd[MAX_CWD_LENGTH];
    char username[MAX_USERNAME_LENGTH];
    char hostname[MAX_HOSTNAME_LENGTH];
    char homedir[MAX_HOMEDIR_LENGTH];
    boolean should_quit;
    boolean debug_mode;
    struct Process *jobs;

} Context;

Context *context_new();
void context_update(Context *context);
boolean context_should_quit(const Context *ctx);


/* *** Command *** */
typedef enum CommandType{
    COMMAND_TYPE_CD,
    COMMAND_TYPE_PWD,
    COMMAND_TYPE_EXIT,
    COMMAND_TYPE_LAUNCH,
    COMMAND_TYPE_PINFO,

} CommandType;
//TODO: this is pretty hacky, fix this
static const int COMMAND_TOTAL_ARGS_LENGTH = 1024;

typedef struct Command {
    CommandType type;
    char *args[COMMAND_TOTAL_ARGS_LENGTH];
    int num_args;
    int background;
    struct Command *next;
} Command;


/* *** Process *** */
typedef struct Process {
    int pid;
    struct Process *next;
    char *pname;
} Process;


give Process* process_new(int pid, const Command *command) {
    Process *p = (Process *)malloc(sizeof(Process));
    p->pid = pid;
    p->next = NULL;


    assert (command->type == COMMAND_TYPE_LAUNCH && 
            command->num_args > 0 &&
            command->args[0] != NULL);
    
    p->pname =(char *)malloc(strlen(command->args[0]));
    strcpy(p->pname, command->args[0]);

    return p;
}


give Command* command_new(CommandType type) {
    Command *command = (Command*)malloc(sizeof(Command));
    command->next = NULL;
    command->type = type;
    command->num_args = 0;
    command->background = 0;
    return command;
}

void command_delete(Command *command) {
    for(int i = 0; i < command->num_args; i++) {
        free(command->args[i]);
    }
}

void command_make_background(Command *command) {
    command->background = 1;
}

void command_add_arg(give Command *command, const char *arg) {
    assert(command->num_args < COMMAND_TOTAL_ARGS_LENGTH);
    command->args[command->num_args] = malloc(strlen(arg) + 1);
    strcpy(command->args[command->num_args], arg);
    command->num_args++;
}


void command_print(Command *c) {
    printf("c[");
    switch(c->type) {
        case COMMAND_TYPE_CD:
            printf("cd: "); break;

        case COMMAND_TYPE_PWD:
            printf("pwd: "); break;

        case COMMAND_TYPE_EXIT:
            printf("exit: "); break;

        case COMMAND_TYPE_LAUNCH:
            printf("launch: "); break;

        case COMMAND_TYPE_PINFO:
            printf("pinfo: "); break;
    }
    for(int i = 0; i < c->num_args; i++) {
        printf("%s ", c->args[i]);
    }
    printf("]");
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

//TODO: This is stateful, need to clean this up dude
void repl_print_prompt(const Context *ctx) {

    char *tilded_dirpath = context_tildefy_directory(ctx, ctx->cwd);
    printf("%s@%s:%s>", tilded_dirpath, ctx->username, ctx->hostname);
    free(tilded_dirpath);
}


give char* read_single_line(boolean *should_quit) {
    assert(should_quit != NULL);

    static const int BUFFER_BLOCK_SIZE = 1024;
    int buffer_block_multiple = 1;


    char *output = (char*)malloc(sizeof(char) * BUFFER_BLOCK_SIZE);
    int buffer_pos = 0;

    while(1) {
        int c = getchar();
        if (c == EOF) {
            *should_quit = TRUE;
            break;
        }
        else if (c == '\n' || c == '\0') {
            break;
        } else {
            if (buffer_pos == buffer_block_multiple * BUFFER_BLOCK_SIZE) {
                buffer_block_multiple++;
                output = realloc(output, 
                        sizeof(char) * BUFFER_BLOCK_SIZE * buffer_block_multiple);
            }

            output[buffer_pos++] = c;
            
        }
    }

    output[buffer_pos] = '\0';
    return output;

}

typedef enum {
    TOKEN_TYPE_SEMICOLON = 1,
    TOKEN_TYPE_AMPERSAND,
    TOKEN_TYPE_WORD,
} TokenType;

typedef struct Token {
    TokenType type;
    char *string;
    struct Token *next;
} Token;

//TODO: implement proper linked list support

give Token* token_new_semicolon() {
    Token *t = (Token*)malloc(sizeof(Token));
    t->type = TOKEN_TYPE_SEMICOLON;
    t->string = NULL;
    t->next = NULL;
    return t;
}

give Token* token_new_ampersand() {
    Token *t = (Token*)malloc(sizeof(Token));
    t->type = TOKEN_TYPE_AMPERSAND;
    t->string = NULL;
    t->next = NULL;
    return t;
}

give Token* token_new_word(char *word) {
    assert(word != NULL);
    Token *t = (Token*)malloc(sizeof(Token));
    t->type = TOKEN_TYPE_WORD;
    t->string = word;
    t->next = NULL;
    return t;
}

void token_delete(Token *t) {
    free(t->string);
}


void token_print(Token t) {
    if (t.type == TOKEN_TYPE_SEMICOLON) {
        printf("t[;]");
    }
    else if (t.type == TOKEN_TYPE_WORD) {
        printf("t[%s]", t.string);
    }
}


int is_char_whitespace(char c) {
    return c == ' ' || c == '\n' || c == '\t';
}

int is_char_token_symbol(char c) {
    return c == ';' || c == '&';
}




give Token* tokenize_line(char *line) {
    Token *head = NULL;
    Token *current = NULL;


    int i = 0;
    while(i < strlen(line)) {
        while(i < strlen(line) && is_char_whitespace(line[i])) {
            i++;
        }

        //if we have reached the end of the tokens, break
        if (i == strlen(line)) {
            break;
        }

        else if (line[i] == ';') {
            i++;
            Token *new = token_new_semicolon();
            if (current) {
                current->next = new;
                current = current->next;
            } else {
                head = current = new;
            }
        }
        else if (line[i] == '&') {
            i++;
            Token *new = token_new_ampersand();
            if (current) {
                current->next = new;
                current = current->next;
            } else {
                head = current = new;
            }
        }
        else {
            const int prev_pos = i;
            while(i < strlen(line) && !is_char_whitespace(line[i]) &&
                    !is_char_token_symbol(line[i])) {
                i++;
            }

            const int word_len = i - prev_pos;
            char *word_buf = (char *)malloc(sizeof(char) * (word_len + 1));
            //TODO: write a function that takes a slice out of it
            for(int j = 0; j < word_len; j++) { word_buf[j] = line[prev_pos + j]; }
            word_buf[word_len] = '\0';

            Token *new = token_new_word(word_buf);
            if (current) {
                current->next = new;
                current = current->next;
            } else {
                head = current = new;
            }
        }
    }
    return head;
    
};


/* Grammar of REPL syntax  (in EBNF)
 * This can be parsed properly using recursive-descent, but let's strtok for now
 * Expr := ";" | "&" | Command | Command ";" Expr 
 * Command := <name> <args>* <"&">?
 */

Token *parse_command(Token *head, Command **result);
Token *parse_expr(Token *head, Command **result);

Token *parse_expr(Token *head, Command **result) {
    if (head == NULL) {
        *result = NULL;
    }
    //empty ";" | empty "&
    else if (head->type == TOKEN_TYPE_SEMICOLON || head->type == TOKEN_TYPE_AMPERSAND) {
        *result = NULL;
    }
    //Command ";" Expr | Command 
    else {
        head = parse_command(head, *result == NULL ? result : &((*result)->next));

        //Command ":" Expr
        if (head != NULL && head->type == TOKEN_TYPE_SEMICOLON) {
            head = head->next;
            head = parse_expr(head, *result == NULL ? result : &((*result)->next));
        } 
    }
    return head;
};

Token *parse_command(Token *head, Command **result) {
    assert (head != NULL);
    assert (head->type != TOKEN_TYPE_SEMICOLON);
    assert (head->type != TOKEN_TYPE_AMPERSAND);


    
    assert (*result == NULL);
    if (!strcmp(head->string, "pwd")) {
        *result = command_new(COMMAND_TYPE_PWD);
        head = head->next;
    }
    else if (!strcmp(head->string, "cd")) {
        *result = command_new(COMMAND_TYPE_CD);
        head = head->next;
    }
    else if (!strcmp(head->string, "cd")) {
        *result = command_new(COMMAND_TYPE_PINFO);
        head = head->next;
    }
    else if (!strcmp(head->string, "exit") ||
             !strcmp(head->string, "quit")) {
        *result = command_new(COMMAND_TYPE_EXIT);
        head = head->next;
    }
    else {
        *result = command_new(COMMAND_TYPE_LAUNCH);
    }

    assert (*result != NULL);
    while(head != NULL && head->type != TOKEN_TYPE_SEMICOLON) {
        if (head->type == TOKEN_TYPE_AMPERSAND) {
            head = head->next;
            command_make_background(*result);
            break;
        } else {
            command_add_arg((*result), head->string);
            head = head->next;
        }
    }

    return head;

};


//holy memory juggling batman :/
give char* get_process_end_string(const Process *p, int status) {
    char SUCCESS_EXIT_STR[] = "Clean exit";
    char COREDUMP_EXIT_STR[] = "Core dumped";
    char SIGNAL_EXIT_STR[] = "Died due to signal";
    char UNKNOWN_EXIT_STR[] = "Unknown exit. check get_process_status_str.";


    char *signal_str;
    if (WIFEXITED(status)) {
        asprintf(&signal_str, "%s", SUCCESS_EXIT_STR);
    }
    else if (WIFSIGNALED(status)) {
        if (WCOREDUMP(status)) {
            asprintf(&signal_str, "%s", COREDUMP_EXIT_STR);
        }
        else {
            asprintf(&signal_str, "%s(%d)", SIGNAL_EXIT_STR, WTERMSIG(status));
        }

    }
    else {
        asprintf(&signal_str, "%s", UNKNOWN_EXIT_STR);
    }

    char *dest = NULL;
    asprintf(&dest, "Process [%s] with pid [%d] ended. Exit: %s",
            p->pname, p->pid, signal_str);
    
    assert(dest != NULL);
    free(signal_str);

    return dest;

}


//
//TODO: clean up. This is doing both printing and
//cleaning up the linked list
void repl_print_ended_jobs(Context *ctx) {

    Process *prev = NULL;
    for (Process *p = ctx->jobs; p != NULL; prev = p, p = p->next) {

        int status;
        pid_t result = waitpid(p->pid, &status, WNOHANG);

        assert(result != -1 && "error on trying to get child process status");

        if (result == 0) {
            printf("\n%s with pid [%d] still running.", p->pname, p->pid);
        }
        else if (result != 0) {
            char *process_end_str = get_process_end_string(p, status);
            assert(process_end_str != NULL);
            printf("%s", process_end_str);

            //remove a job if it is done
            if (prev == NULL) {
                ctx->jobs = p->next;
            } else {
                prev->next = p->next;
            }
        }
    }
}


give char* tilde_expand_path(const char *toexpand, const char *homedir) {

    static const int MAX_BUF_LEN = 1024 * 10;
    char *expanded_buf = (char *)malloc(sizeof(char) * MAX_BUF_LEN);
    
    char *new  = expanded_buf;
    for (const char *original = toexpand; *original != '\0'; original++) {
        assert (new - expanded_buf < MAX_BUF_LEN);

        if (*original == '~') {
            strcpy(new, homedir);
            new += strlen(homedir);
        } else {
            *new = *original;
            new++;
        }
    }

    *new = '\0';
    return expanded_buf;

}

give Command* repl_read(Context *ctx){

    char *line = read_single_line(&(ctx->should_quit));
    Token *tokens = tokenize_line(line);
    
    //tilde expand
    for (Token *curr = tokens; curr != NULL; curr = curr->next) {
        if(curr->type == TOKEN_TYPE_WORD) {
            char *new_str = tilde_expand_path(curr->string, ctx->homedir);
            free(curr->string);
            curr->string = new_str;
        }
    }
    free(line);

    if (ctx->debug_mode) {
        for(Token *t = tokens; t != NULL; t = t->next) {
            token_print(*t);
        }
    }

    Command *commands = NULL;
    parse_expr(tokens, &commands);

    for(Token *curr = tokens, *next = NULL; curr != NULL;) {
        next = curr->next;
        token_delete(curr);
        free(curr);
        curr = next;
    }

    return commands;

};



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
        printf("\n[cd %s] failed. ", command->args[0]);
        if (errno == EACCES) {
            printf("Search denied to path");
        }
        else if (errno == EFAULT) {
            printf("Path is outside process space");
        }
        else if (errno == EIO) {
            printf("I/O error occured when reading filesystem");
        }
        else if (errno == ELOOP) {
            printf("Too many symbolic links encountered");
        }
        else if (errno == ENAMETOOLONG) {
            printf("Path too long");
        }
        else if (errno == ENOENT) {
            printf("Directory does not exist");
        }
        else if (errno == ENOTDIR) {
            printf("Some part of path is not a directory");
        }
        else {
            printf("Unknown failure. status: %d. Please report this!", status);
        }
    }

    return -1;
};


int repl_pwd(const Command *command, const Context *context) {
    if (command->num_args != 0) {
        return -1;
    }
    printf("%s", context->cwd);
    return 0;
};

int repl_pinfo(const Context *context) {
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
        case COMMAND_TYPE_EXIT:
            repl_quit(context);
            break;
        case COMMAND_TYPE_PINFO:
            repl_pinfo(context);
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
