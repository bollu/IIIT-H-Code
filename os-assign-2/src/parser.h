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
    COMMAND_TYPE_PWD,
    COMMAND_TYPE_EXIT,
    COMMAND_TYPE_LAUNCH,
    COMMAND_TYPE_PINFO,
    COMMAND_TYPE_ECHO,

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
    //Redirect *redirects[COMMAND_TOTAL_REDIRECTS];
    struct Command *pipe;
} Command;


give Command* command_new(CommandType type);
void command_delete(Command *command);
void command_print(Command *c);
give Command* repl_read(Context *ctx, int *status, char **message);
