#pragma once
#include <stdio.h>
#include <stdlib.h>

#include <unistd.h>
#include <string.h>
#include <assert.h>
#include <errno.h>

#include "context.h"
#include "common.h"

typedef enum CommandType{
    COMMAND_TYPE_CD,
    COMMAND_TYPE_EXIT,
    COMMAND_TYPE_LAUNCH,
    COMMAND_TYPE_PINFO,
    
    COMMAND_TYPE_LISTJOBS,
    COMMAND_TYPE_SENDSIG,
    COMMAND_TYPE_FG,
    COMMAND_TYPE_KILLALLBG,

} CommandType;
//TODO: this is pretty hacky, fix this
static const int COMMAND_TOTAL_ARGS_LENGTH = 1024;

typedef struct Command {
    CommandType type;
    char *args[COMMAND_TOTAL_ARGS_LENGTH];
    int num_args;
    int background;
    struct Command *next;


    char *redirect_input_path;
    char *redirect_output_path;
    int append_redirect_output;
    //Redirect *redirects[COMMAND_TOTAL_REDIRECTS];
    struct Command *pipe;

    int id;
} Command;

void parser_init();
give Command* command_new(CommandType type);
void command_delete(Command *command);
void command_print(Command *c);
give Command* repl_read(Context *ctx, char *repl_prompt_str, int *status, char **message);
