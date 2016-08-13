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
char buffer[READ_BLOCK_SIZE];

typedef int FILE_DESC;
void debug_printf(const char *str) {
    write(1, str, strlen(str));
}

void error_print(const char *str) {
    write(2, str, strlen(str));
}

FILE_DESC create_output_file(const char* inputfile_name) {
    if (mkdir("Assignment", 0777) == -1) {
         error_print("ERROR: unable to create folder Assignment/. Maybe folder already"
                      " exists? If so, please delete it\n");
         return -1;
    };
    char *outpath = (char *)malloc(strlen("Assignment/output_") + strlen(inputfile_name) + 1);
    outpath[0]= '\0';
    strcat(outpath, "Assignment/output_");
    strcat(outpath, inputfile_name);

    const FILE_DESC outfile = open(outpath, O_WRONLY | O_CREAT | O_TRUNC);
    fchmod(outfile, 0777);
    free(outpath);

    return outfile;
}

FILE_DESC open_input_file(const char *input_filepath) {
    const FILE_DESC inputfile = open(input_filepath, O_RDONLY);
    return inputfile;
}

void reverse_buffer(char *buf, size_t len) {
    for (size_t i = 0; i < len / 2; i++) {
        char temp = buf[i];
        buf[i] = buf[len - 1 - i];
        buf[len - 1 - i] = temp;
    }
}

void allow_only_user_access(FILE_DESC file) {
  fchmod(file, S_IRUSR | S_IWUSR | S_IXUSR);
}

int main(int argc, char **argv) {
    if (argc < 2) {
        error_print("ERROR: Need input file path and out file path as command line parameter."
                    "\nUSAGE: progname <infile name>"
                    "\nQuitting...");
        return 1;
    }
    const FILE_DESC inputfile = open_input_file(argv[1]);
    //create out file
    const FILE_DESC outputfile = create_output_file(argv[1]);

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
    
    size_t to_read = TOTAL_BYTES;
    while (to_read > 0) {
        size_t reading_size = min(to_read, READ_BLOCK_SIZE);
        //go a character back
        lseek(inputfile, -reading_size, SEEK_CUR);
        const size_t bytes_read = read(inputfile, buffer, reading_size);
        //rewind whatever youve read
        assert(bytes_read == reading_size);
        lseek(inputfile, -bytes_read, SEEK_CUR);
        to_read -= bytes_read;
        reverse_buffer(buffer, bytes_read);

        const size_t bytes_written = write(outputfile, buffer, bytes_read);
    
        if (bytes_written != bytes_read) {
            error_print("ERROR: wrote less bytes than asked for");
            return 1;
        }

    }
    close(inputfile);
    // close(outputfile);

    allow_only_user_access(outputfile);


    return  0;
}
