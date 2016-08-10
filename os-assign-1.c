//for malloc and free
#include <stdlib.h>

#include <stdio.h>
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
static const size_t READ_BLOCK_SIZE = 10 * 1024;
char buffer[READ_BLOCK_SIZE];

typedef int FILE_DESC;
void debug_printf(const char *str) {
    write(1, str, strlen(str));
}

void error_printf(const char *str) {
    write(2, str, strlen(str));
}

FILE_DESC create_output_file(const char* outfile_name) {
    if (mkdir("Assignment", 0777) == -1) {
         error_printf("unable to create assignment folder");
         return -1;
    };
    char *outpath = (char *)malloc(strlen("Assignment/") + strlen(outfile_name) + 1);
    sprintf(outpath, "Assignment/%s", outfile_name);
    const FILE_DESC outfile = open(outpath, O_WRONLY | O_CREAT | O_TRUNC);
    fchmod(outfile, 0777);

    free(outpath);

    return outfile;
}

FILE_DESC open_input_file(const char *input_filepath) {
    const FILE_DESC inputfile = open(input_filepath, O_RDONLY);
    return inputfile;
}

void reverse_buffer(char *buf, int len) {
    for (int i = 0; i < len / 2; i++) {
        char temp = buf[i];
        buf[i] = buf[len - 1 - i];
        buf[len - 1 - i] = temp;
    }
}
int main(int argc, char **argv) {
    if (argc < 2) {
        error_printf("ERROR: Need input file path and out file path as command line parameter."
                    "\nUSAGE: progname <infile path> <outfile path>"
                    "\nQuitting...");
        return 1;
    }
    const FILE_DESC inputfile = open_input_file(argv[1]);
    //create out file
    const FILE_DESC outputfile = create_output_file(argv[2]);

    if (inputfile == -1) {
        error_printf("ERROR: unable to open input file...");
    }
    
    if (outputfile == -1) {
        error_printf("ERROR: unable to open output file...");
    }
    //go to start
    lseek(inputfile, SEEK_SET, 0);
    //go to end of file
    const int offset_in_bytes = lseek(inputfile, SEEK_END, 0);
    if(offset_in_bytes == -1) {
        error_printf("ERROR: unable to seek to end of file");
        return 1;
    }
    printf("offset in bytes: %d", offset_in_bytes);
    
    int bytes_left = offset_in_bytes;
    while (bytes_left > 0) {
        int bytes_to_read = min(bytes_left, READ_BLOCK_SIZE);
        //rewind by BYTES_TO_READ
        lseek(inputfile, SEEK_CUR, -bytes_to_read);
        
        const int bytes_actually_read = read(inputfile, buffer, READ_BLOCK_SIZE);
        if (bytes_to_read != bytes_actually_read) {
            printf("to read: %d | actually read: %d", bytes_to_read, bytes_actually_read);
            error_printf("ERROR: read less bytes than asked for");
            return 1;
        }
        reverse_buffer(buffer, READ_BLOCK_SIZE);
        bytes_left -= bytes_to_read;

        const int bytes_written = write(outputfile, buffer, bytes_actually_read);
    
        if (bytes_written != bytes_actually_read) {
            error_printf("ERROR: wrote less bytes than asked for");
            return 1;
        }

    }
    close(inputfile);
    close(outputfile);


    return  0;
}
