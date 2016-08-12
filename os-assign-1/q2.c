//for malloc and free
#include <stdlib.h>
#include <assert.h>

#include <string.h>

// mkdir
#include <sys/stat.h>

// open, close
#include <fcntl.h>
//read, write, seek
#include <sys/types.h>
#include <sys/uio.h>
#include <unistd.h>

#define min(x, y) ((x) < (y)  ? (x) : (y))
static const size_t READ_BLOCK_SIZE = 1024 * 1024 * 20;
char in_buffer[READ_BLOCK_SIZE];
char out_buffer[READ_BLOCK_SIZE];

typedef int FILE_DESC;
void debug_printf(const char *str) {
    write(1, str, strlen(str));
}

void error_print(const char *str) {
    write(2, str, strlen(str));
}


int check_assign_folder_exists(const char *foldername) {
    struct stat s;
    if (stat(foldername, &s)) {
        return S_ISDIR(s.st_mode);
    }
    return 0;
}

FILE_DESC open_out_file(const char* outfile_name) {
    if (!check_assign_folder_exists("Assignment")) {
         error_print("ERROR: unable to find folder Assignment/ in"
                     " current working directory. Maybe folder already"
                      " exists? If so, please delete it\n");
         return -1;
    };

    char *outpath = (char *)malloc(strlen("Assignment/") + strlen(outfile_name) + 1);
    outpath[0]= '\0';
    strcat(outpath, "Assignment/");
    strcat(outpath, outfile_name);

    const FILE_DESC outfile = open(outpath, O_RDONLY);
    free(outpath);

    return outfile;
}

FILE_DESC open_input_file(const char *input_filepath) {
    const FILE_DESC inputfile = open(input_filepath, O_RDONLY);
    return inputfile;
}

void print_file_permissions(const FILE_DESC file) {
    error_print("\n*** User Permissions ***\n");
    error_print("\n*** Group Permissions ***")
    error_print("\n*** Others Permissions ***")
    
};


void reverse_buffer(char *buf, size_t len) {
    for (size_t i = 0; i < len / 2; i++) {
        char temp = buf[i];
        buf[i] = buf[len - 1 - i];
        buf[len - 1 - i] = temp;
    }
}

int read_block_reverse(FILE_DESC file, const char *buffer, size_t reading_size) {
    lseek(inputfile, -reading_size, SEEK_CUR);
    const size_t bytes_read = read(file, buffer, reading_size);
    //rewind whatever youve read
    assert(bytes_read == reading_size);

    if (!bytes_read == reading_size) {
        return -1;
    };

    lseek(inputfile, -bytes_read, SEEK_CUR);

    return 1;
}


int read_block_forward(FILE_DESC file, const char *buffer, size_t reading_size) {
    const size_t bytes_read = read(file, buffer, reading_size);
    assert(bytes_read == reading_size);

    if (!bytes_read == reading_size) {
        return -1;
    };
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 2) {
        error_print("ERROR: Need input file path and out file path as command line parameter."
                    "\nUSAGE: progname <infile path> <outfile path>"
                    "\nQuitting...");
        return 1;
    }
    const FILE_DESC inputfile = open_input_file(argv[1]);
    //create out file
    const FILE_DESC outputfile = open_file(argv[2]);

    if (inputfile == -1) {
        error_print("ERROR: unable to open input file...");
        return 1;
    }
    
    if (outputfile == -1) {
        error_print("ERROR: unable to open output file...");
        return 1;
    }
    //go to end
    const size_t TOTAL_BYTES = lseek(inputfile, 0, SEEK_END);

    const size_t BYTES_OUTFILE = lseek(outputfile, 0, SEEK_END);
    lseek(outputfile, 0, SEEK_SET);

    if (TOTAL_BYTES != BYES_OUTFILE) {
        error_print("input and output files have different sizes. Invalid");
        return -1;
    }
    
    size_t to_read = TOTAL_BYTES;
    while (to_read > 0) {
        size_t reading_size = min(to_read, READ_BLOCK_SIZE);
        if(!read_block_reverse(inputfile, in_buffer, reading_size)) {
            error_print("read invalid number of bytes from input file");
            return 1;
        };
       if(!read_block_forwarrd(outputfile, out_buffer, reading_size)) {
            error_print("read invalid number of bytes from output file");
            return 1;
       }

        to_read -= reading_size;
        
        int i = strlen(in_buffer);

        int files_match = 1;
        for(int i = 0;  i < reading_size; i++) {
            if(in_buffer[i] != out_buffer[reading_size - 1 - i]) {
                files_match = 0;
                break;
            }
        }
    }

    if (files_match) {
        error_print("* Input same as output: True");
    }
    else {
        error_print("* Input same as output: False");
    }

    print_file_permissions(outfile);


    close(inputfile);
    close(outputfile);


    return  0;
}
