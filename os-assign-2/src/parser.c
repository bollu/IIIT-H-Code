#include <stdio.h>
#include <stdlib.h>

#include <unistd.h>
#include <string.h>
#include <assert.h>
#include <errno.h>

#include "parser.h"
#include "context.h"
#include "common.h"

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

        case COMMAND_TYPE_ECHO:
            printf("echo: "); break;
    }
    for(int i = 0; i < c->num_args; i++) {
        printf("%s ", c->args[i]);
    }
    printf("]");
}

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
    else if (!strcmp(head->string, "echo")) {
        *result = command_new(COMMAND_TYPE_ECHO);
        head = head->next;
    }
    else if (!strcmp(head->string, "pinfo")) {
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



    