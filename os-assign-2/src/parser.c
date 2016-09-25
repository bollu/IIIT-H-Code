#include <stdio.h>
#include <stdlib.h>

#include <unistd.h>
#include <string.h>
#include <assert.h>
#include <errno.h>

#include "parser.h"
#include "context.h"
#include "common.h"

void command_make_background(Command *command);
void command_add_arg(give Command *command, const char *arg);

typedef enum {
    TOKEN_TYPE_SEMICOLON = 1,
    TOKEN_TYPE_AMPERSAND,
    TOKEN_TYPE_WORD,
    TOKEN_TYPE_PIPE,
    TOKEN_TYPE_REDIRECT_OUTPUT,
    TOKEN_TYPE_REDIRECT_APPEND_OUTPUT,
    TOKEN_TYPE_REDIRECT_INPUT
} TokenType;

typedef struct Token {
    TokenType type;
    char *string;
    struct Token *next;
} Token;

give Command* command_new(CommandType type) {
    Command *command = (Command*)malloc(sizeof(Command));
    command->next = NULL;
    command->type = type;
    command->num_args = 0;
    command->background = 0;
    command->pipe = NULL;
    command->redirect_input_path = NULL;
    command->redirect_output_path = NULL;
    command->append_redirect_output = 0;

    for(int i = 0; i < COMMAND_TOTAL_ARGS_LENGTH; i++) {
        command->args[i] = NULL;
    }
    return command;
}

void command_delete(Command *command) {
    for(int i = 0; i < command->num_args; i++) {
        free(command->args[i]);
    }
    //TODO: are there more things to free? f*ck C, I want
    //smart pointers :(
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
    printf("command[");
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

        case COMMAND_TYPE_ECHO:
            printf("echo: "); break;

        case COMMAND_TYPE_LISTJOBS:
            printf("listjobs: "); break;

        case COMMAND_TYPE_FG:
            printf("fg: "); break;

        case COMMAND_TYPE_KILLALLBG:
            printf("killallbg: "); break;
    }
    for(int i = 0; i < c->num_args; i++) {
        printf("%s ", c->args[i]);
    }
    if (c->redirect_input_path) {
        printf("\nredir-input: %s", c->redirect_input_path);
    }
    if (c->redirect_output_path) {
        printf("\nredir-output: %s", c->redirect_output_path);
    }
    if (c->pipe) {
        printf("\npipe: ");
        command_print(c->pipe);
    }
    printf("\n]");
}



Token *parse_command(Token *head, Command **result, int *status, 
        give char** error_message);
Token *parse_expr(Token *head, Command **result, int *status,
        give char **error_message);


/* Grammar of REPL syntax  (in EBNF)
 * This can be parsed properly using recursive-descent, but let's strtok for now
 * Expr := ";" | "&" | Command | Command ";" Expr 
 * Command := <name> <args>* ["&"]? ["|" Command]? [">" outfilepath]? ["<" infilepath]?
 */

Token *parse_expr(Token *head, Command **result, int *status,
        give char **error_message) {
    if (head == NULL) {
        *result = NULL;
    }
    //empty ";" | empty "&"
    else if (head->type == TOKEN_TYPE_SEMICOLON || head->type == TOKEN_TYPE_AMPERSAND) {
        *result = NULL;
    }
    //Command ";" Expr | Command 
    else {
        head = parse_command(head, *result == NULL ? result : &((*result)->next),
                             status, error_message);
        if (*status == -1) {
            return NULL;
        }

        //Command ":" Expr
        if (head != NULL && head->type == TOKEN_TYPE_SEMICOLON) {
            head = head->next;
            head = parse_expr(head, *result == NULL ? result : &((*result)->next),
                              status, error_message);

            if (*status == -1) {
                return NULL;
            }

        } 
    }
    return head;
};

//status: 1 => success
//status: -1 => failure
Token *parse_command(Token *head, Command **result, int *status, 
        give char** message) {

    assert (head != NULL);
    *status = 1;
    
    assert(result != NULL);
    assert (*result == NULL);

    switch(head->type) {
        case TOKEN_TYPE_SEMICOLON:
        case TOKEN_TYPE_AMPERSAND:
            assert (FALSE && "should be consumed by the expression parser");
            return head;
            
        case TOKEN_TYPE_PIPE:
        case TOKEN_TYPE_REDIRECT_OUTPUT:
        case TOKEN_TYPE_REDIRECT_APPEND_OUTPUT:
        case TOKEN_TYPE_REDIRECT_INPUT:
            *status = -1;
            *message = (char *)malloc(sizeof(char) * 1024);
            sprintf(*message, "no command given to act on");
            return head;
            break;

        case TOKEN_TYPE_WORD:
            if (!strcmp(head->string, "pwd")) {
                *result = command_new(COMMAND_TYPE_PWD);
                head = head->next;
            }
            else if (!strcmp(head->string, "cd")) {
                *result = command_new(COMMAND_TYPE_CD);
                head = head->next;
            }
            else if (!strcmp(head->string, "echo")) {
                *result = command_new(COMMAND_TYPE_ECHO);
                head = head->next;
            }
            else if (!strcmp(head->string, "pinfo")) {
                *result = command_new(COMMAND_TYPE_PINFO);
                head = head->next;
            }
            else if (!strcmp(head->string, "listjobs")) {
                *result = command_new(COMMAND_TYPE_LISTJOBS);
                head = head->next;
            }

            else if (!strcmp(head->string, "killallbg")) {
                *result = command_new(COMMAND_TYPE_KILLALLBG);
                head = head->next;
            }
            else if (!strcmp(head->string, "fg")) {
                *result = command_new(COMMAND_TYPE_FG);
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
            break;
    }

    assert (*result != NULL);
    while(head != NULL && head->type != TOKEN_TYPE_SEMICOLON) {
        
        if (head->type == TOKEN_TYPE_AMPERSAND) {
            head = head->next;
            command_make_background(*result);
            break;
        } else if (head->type == TOKEN_TYPE_REDIRECT_INPUT ||
                   head->type == TOKEN_TYPE_REDIRECT_OUTPUT ||
                   head->type == TOKEN_TYPE_REDIRECT_APPEND_OUTPUT){

            if (head->type == TOKEN_TYPE_REDIRECT_INPUT &&
                (*result)->redirect_input_path != NULL) {
                *status = -1;
                *message = (char*)(malloc(1024 * sizeof(char)));
                sprintf(*message, "input already redirected to: %s",
                        (*result)->redirect_input_path);
                return head;
            }

            if (head->type == TOKEN_TYPE_REDIRECT_OUTPUT &&
                (*result)->redirect_output_path != NULL) {
                *status = -1;
                *message = (char*)(malloc(1024 * sizeof(char)));
                sprintf(*message, "Output already redirected to: %s",
                        (*result)->redirect_output_path);
                return head;
            }

            const TokenType redirect_type = head->type;

            head = head->next;
            if (head == NULL || head->type != TOKEN_TYPE_WORD) {
                *status = -1;
                *message = (char*)(malloc(1024 * sizeof(char)));
                //HACK: change command structure to store command name
                //separately, so I can use it for proper error reporting
                sprintf(*message, "parse error: no redirection file given.");
                return head;
            } 

            char **out = NULL;
            const char *redirect_filename = head->string;

            if (redirect_type == TOKEN_TYPE_REDIRECT_INPUT) {
                out = &((*result)->redirect_input_path);
            }
            else if (redirect_type == TOKEN_TYPE_REDIRECT_APPEND_OUTPUT) {
                out = &((*result)->redirect_output_path);
                (*result)->append_redirect_output = 1;
            }
            else if (redirect_type == TOKEN_TYPE_REDIRECT_OUTPUT) {
                out = &((*result)->redirect_output_path);
                (*result)->append_redirect_output = 0;
            } else {
                assert(FALSE && "ERROR: unknown redirect_type.");
            }

            *out = (char*) malloc(strlen(redirect_filename) + 1);
            assert(out != NULL);
            assert(*out != NULL);
            strcpy(*out, redirect_filename);

            head = head->next;
            
        } 
        else if (head->type == TOKEN_TYPE_PIPE) {
            head = head->next;
            if (head == NULL) {
                *status = -1;
                
                *message = (char*)(malloc(1024 * sizeof(char)));
                sprintf(*message, "parse error: no program given to pipe into");
                return NULL;
            
            } else {
                head = parse_command(head, &((*result)->pipe), status, message);
                if (*status == -1) {
                    return NULL;
                }
            }
        }
        else if (head->type == TOKEN_TYPE_WORD){
            command_add_arg((*result), head->string);
            head = head->next;
        } else {
            assert (FALSE && "got unknown token type during parse_command");
        }
    }

    return head;

};


//TODO: implement proper linked list support

give Token *_token_new_empty() {
    Token *t = (Token*)malloc(sizeof(Token));
    t->type = TOKEN_TYPE_SEMICOLON;
    t->string = NULL;
    t->next = NULL;
    return t;
}
give Token* token_new_semicolon() {
    Token *t = _token_new_empty();
    t->type = TOKEN_TYPE_SEMICOLON;
    return t;
}


give Token* token_new_ampersand() {
    Token *t = (Token*)malloc(sizeof(Token));
    t->type = TOKEN_TYPE_AMPERSAND;
    return t;
}

give Token* token_new_word(char *word) {
    assert(word != NULL);
    Token *t = _token_new_empty();
    t->type = TOKEN_TYPE_WORD;
    t->string = word;
    return t;
}

give Token* token_new_pipe() {
    Token *t = _token_new_empty();
    t->type = TOKEN_TYPE_PIPE;
    return t;
}

give Token* token_new_redirect_out() {
    Token *t = _token_new_empty();
    t->type = TOKEN_TYPE_REDIRECT_OUTPUT;
    return t;
}


give Token* token_new_redirect_append_out() {
    Token *t = _token_new_empty();
    t->type = TOKEN_TYPE_REDIRECT_APPEND_OUTPUT;
    return t;
}

give Token* token_new_redirect_in() {
    Token *t = _token_new_empty();
    t->type = TOKEN_TYPE_REDIRECT_INPUT;
    return t;
}


void token_delete(Token *t) {
    free(t->string);
}


void token_print(Token t) {
    switch(t.type) {
        case TOKEN_TYPE_SEMICOLON:
            printf("t[;]"); break;
        case TOKEN_TYPE_WORD:
            printf("t[%s]", t.string); break;
        case TOKEN_TYPE_AMPERSAND:
            printf("t[&]"); break;
        case TOKEN_TYPE_PIPE:
            printf("t[|]"); break;
        case TOKEN_TYPE_REDIRECT_OUTPUT:
            printf("t[>]"); break;
        case TOKEN_TYPE_REDIRECT_APPEND_OUTPUT:
            printf("t[>>]"); break;
        case TOKEN_TYPE_REDIRECT_INPUT:
            printf("t[<]"); break;
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

        else if (line[i] == ';' || line[i] == '&' || line[i] == '|' ||
                line[i] == '>' || line[i] == '<') {
            char op = line[i];
            i++;
            Token *new = NULL;
            if (op == ';') { new =  token_new_semicolon(); }
            else if (op == '&') { new = token_new_ampersand(); }
            else if (op == '|') { new = token_new_pipe(); }
            else if (op == '>') { 
                //1 lookahead for >>
                if (i  < strlen(line) && line[i] == '>') {
                    i++;
                    new = token_new_redirect_append_out();
                } else {
                    new = token_new_redirect_out();
                }
            }
            else if (op == '<') { new = token_new_redirect_in(); }
            else { assert(FALSE && "should not reach here: found symbol"
                          "that has no associated token"); }


            assert(new != NULL && "no token created");

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


give Command* repl_read(Context *ctx, int *status, char **message){

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
        printf("\ndebug token list: ");
        for(Token *t = tokens; t != NULL; t = t->next) {
            token_print(*t);
            printf(" ");
        }
        printf("\n");
    }

    Command *commands = NULL;
    parse_expr(tokens, &commands, status, message);

    for(Token *curr = tokens, *next = NULL; curr != NULL;) {
        next = curr->next;
        token_delete(curr);
        free(curr);
        curr = next;
    }
    
    if (*status == -1) {
        return NULL;
    }

    return commands;
};
