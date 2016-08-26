#include <stdio.h>
#include <stdlib.h>


#include <unistd.h>
#include <string.h>
#include <assert.h>

//copied neat idea from ISL library! 
//returns a new block of memory
#define give
//takes a block of memory and frees it
#define take

typedef enum boolean{
    FALSE = 0,
    TRUE = 1
} boolean;

/* *** Context *** */
static const int MAX_CWD_LENGTH = 1024 * 20;
static const int MAX_USERNAME_LENGTH = 1024 * 20;
static const int MAX_HOSTNAME_LENGTH = 1024 * 20;
typedef struct  {
    char cwd[MAX_CWD_LENGTH];
    char username[MAX_USERNAME_LENGTH];
    char hostname[MAX_HOSTNAME_LENGTH];
    boolean should_quit;
    boolean debug_mode;
    Process *background_jobs;

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
    //the command that was used to launch this process
    Command *command;
} Process;


Process* process_new(int pid, Command *command) {
    Process *p = (Process *)malloc(sizeof(Process));
    p->pid = pid;
    p->next = NULL;
    p->command = command
    return p;
}


Command* command_new(CommandType type) {
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
    return ctx;
}

void context_update(Context *context) {
    getcwd(context->cwd, MAX_CWD_LENGTH); 
    gethostname(context->hostname, MAX_HOSTNAME_LENGTH);
    strncpy(context->username, getlogin(), MAX_USERNAME_LENGTH);
}

void context_add_background_job(Context *context, Process *p) {
    if (context->background_jobs == NULL) {
        context->background_jobs = p;
    }  else {
        Process *last = context->background_jobs;
        for(; last->next != NULL; last = last->next){};
        last->next = p;
    }
}
/* *** Command Implementation *** */

/* *** REPL Implementation *** */

give char* context_tildefy_directory(const Context *ctx, const char *dirpath) {
   char *substr = substr(dirpath, ctx->cwd);

   if (substr != NULL) {
       char *new_dirpath = malloc("~/" + strlen(substr) + 1);
       sprintf(new_dirpath, "~/%s", substr);

       return new_dirpath;
   } else {
        char *new_dirpath = malloc(strlen(dirpath + 1);
        strcpy(new_dirpath, dirpath);
        
        return new_dirpath;
   }
}

void repl_print_prompt(const Context *ctx) {

    const char *tilded_dirpath = context_tildefy_directory(ctx, ctx->cwd);
    printf("\n%s@%s:%s>", context_tildefy_directory(ctx, tilded_dirpath),
        ctx->username, ctx->hostname);
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

Token* token_new_semicolon() {
    Token *t = (Token*)malloc(sizeof(Token));
    t->type = TOKEN_TYPE_SEMICOLON;
    t->string = NULL;
    t->next = NULL;
    return t;
}

Token* token_new_ampersand() {
    Token *t = (Token*)malloc(sizeof(Token));
    t->type = TOKEN_TYPE_AMPERSAND;
    t->string = NULL;
    t->next = NULL;
    return t;
}

Token* token_new_word(char *word) {
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

void repl_print_ended_jobs(Context *ctx) {

    Process *prev = NULL;
    for (Process *p = ctx->background_jobs; p != NULL; prev = p, p = p->next) {
        int status;
        pid_t result = waitpid(p->pid, &status, WNOHANG);
        assert(result != -1 && "error on trying to get child process status");
        if (result == 0) {
            printf("\nchild process [%d] still running.", p->pid);
        }
        if (result != 0) {
            printf("\nchild process [%d] ended, Result: [%d]", p->pid, result);

            //remove a job if it is done
            if (prev == NULL) {
                ctx->background_jobs = p->next;
            } else {
                prev->next = p->next;
            }
        }
    }
}

give Command* repl_read(Context *ctx){

    repl_print_ended_jobs(ctx);
    repl_print_prompt(ctx);
    char *line = read_single_line(&(ctx->should_quit));
    Token *tokens = tokenize_line(line);
    free(line);

    if (ctx->debug_mode) {
        for(Token *t = tokens; t != NULL; t = t->next) {
            token_print(*t);
        }
    }

    Command *commands = NULL;
    parse_expr(tokens, &commands);

    //free the Tokens linked list
    Token *curr = tokens, *next = NULL;
    while(curr != NULL) {
        next = curr->next;
        token_delete(curr);
        free(curr);
        curr = next;
    
    }
    //free the last token as well
    free(prev);


    return commands;

};



int repl_launch(const Command *command, Context *context) {
    pid_t pid, wpid;
    int status;

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
        if (command->background) {
            Process *p = process_new(pid, command);
            context_add_background_job(context, p);
        }
        else {
            wpid = waitpid(pid, &status, WUNTRACED);
            /*
            do {
                waitpid (pid, NULL, 0);
            } while (!WIFEXITED(status) && !WIFSIGNALED(status));
            */
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

    chdir(command->args[0]);
    return 0;
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
        Command *commands = repl_read(ctx);
        
        if(ctx->should_quit) {
            break;
        }

        for(Command *c = commands; c != NULL; c = c->next) {
            context_update(ctx);
            repl_eval(c, ctx);
        }

    }
    repl_shutdown(ctx);
    return 0;
}
