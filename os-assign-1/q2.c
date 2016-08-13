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

void print_string(const char *str) {
    write(1, str, strlen(str));
}

void print_bool(int b) {
    if (b) {
        write(1, "true", 4);
    }
    else {
        write(1, "false", 5);
    }
}


int check_assign_folder_exists(const char *foldername) {
    struct stat s;
    if (stat(foldername, &s) == 0) {
        return S_ISDIR(s.st_mode);
    }
    return 0;
}

FILE_DESC open_output_file(const char* inputfile_name) {
    print_string("\n*** File and Folder Existence ***");
    if (!check_assign_folder_exists("Assignment")) {
        print_string("\n* assignment folder exists: False");
        return -1;
    } else {
        print_string("\n* assignment folder exists: True");
    }

    char *outpath = (char *)malloc(strlen("Assignment/output_") + strlen(inputfile_name) + 1);
    outpath[0]= '\0';
    strcat(outpath, "Assignment/output_");
    strcat(outpath, inputfile_name);


    struct stat s;
    if (stat(outpath, &s) == 0 && S_ISREG(s.st_mode)) {
        print_string("\n* output file exists: True");    
    } else {
        print_string("\n* output file exists: False");
    }

    const FILE_DESC outfile = open(outpath, O_RDONLY);
    free(outpath);

    return outfile;
}

FILE_DESC open_input_file(const char *input_filepath) {
    const FILE_DESC inputfile = open(input_filepath, O_RDONLY);
    return inputfile;
}

void print_file_permissions(const FILE_DESC file) {
    struct stat s;
    if(fstat(file, &s) != 0) {
        print_string("\nERROR: unable to extract file permission "
                " information. Quitting");
        return;
    }
    print_string("\n*** User Permissions ***");
    print_string("\n * Read: "); print_bool(s.st_mode & S_IRUSR);
    print_string("\n * Write: "); print_bool(s.st_mode & S_IWUSR);
    print_string("\n * Read: "); print_bool(s.st_mode & S_IXUSR);

    print_string("\n*** Group Permissions ***");
    print_string("\n * Read: "); print_bool(s.st_mode & S_IRGRP);
    print_string("\n * Write: "); print_bool(s.st_mode & S_IWGRP);
    print_string("\n * Read: "); print_bool(s.st_mode & S_IXGRP);

    print_string("\n*** Others Permissions ***");
    print_string("\n * Read: "); print_bool(s.st_mode & S_IROTH);
    print_string("\n * Write: "); print_bool(s.st_mode & S_IWOTH);
    print_string("\n * Read: "); print_bool(s.st_mode & S_IXOTH);

};


void reverse_buffer(char *buf, size_t len) {
    for (size_t i = 0; i < len / 2; i++) {
        char temp = buf[i];
        buf[i] = buf[len - 1 - i];
        buf[len - 1 - i] = temp;
    }
}

int read_block_reverse(const FILE_DESC file, char *buffer, const size_t reading_size) {
    lseek(file, -reading_size, SEEK_CUR);
    const size_t bytes_read = read(file, buffer, reading_size);
    //rewind whatever youve read
    assert(bytes_read == reading_size);

    if (!(bytes_read == reading_size)) {
        return -1;
    };

    lseek(file, -bytes_read, SEEK_CUR);

    return 1;
}


int read_block_forward(const FILE_DESC file, char *buffer, const size_t reading_size) {
    const size_t bytes_read = read(file, buffer, reading_size);
    assert(bytes_read == reading_size);

    if (!(bytes_read == reading_size)) {
        return -1;
    };
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 2) {
        print_string("\nERROR: Need input file path and out file path as command line parameter."
                "\nUSAGE: progname <infile name>"
                "\nQuitting...");
        return 1;
    }
    const FILE_DESC inputfile = open_input_file(argv[1]);
    //create out file
    const FILE_DESC outputfile = open_output_file(argv[1]);

    if (inputfile == -1) {
        print_string("\nERROR: unable to open input file...");
        return 1;
    }

    if (outputfile == -1) {
        print_string("\nERROR: unable to open output file...");
        return 1;
    }
    //go to end
    const size_t TOTAL_BYTES = lseek(inputfile, 0, SEEK_END);

    const size_t BYTES_OUTFILE = lseek(outputfile, 0, SEEK_END);
    lseek(outputfile, 0, SEEK_SET);

    if (TOTAL_BYTES != BYTES_OUTFILE) {
        print_string("\n* Input same as output: False (different sizes)");
    } else {
        size_t to_read = TOTAL_BYTES;
        int files_match = 1;
        while (to_read > 0) {
            size_t reading_size = min(to_read, READ_BLOCK_SIZE);
            if(!read_block_reverse(inputfile, in_buffer, reading_size)) {
                print_string("read invalid number of bytes from input file");
                return 1;
            };
            if(!read_block_forward(outputfile, out_buffer, reading_size)) {
                print_string("read invalid number of bytes from output file");
                return 1;
            }

            to_read -= reading_size;

            int files_match = 1;
            for(int i = 0;  i < reading_size; i++) {
                if(in_buffer[i] != out_buffer[reading_size - 1 - i]) {
                    files_match = 0;
                    break;
                }
            }
        }

        print_string("\n*** Input Output Comparison ***");
        if (files_match) {
            print_string("\n* Input same as output: True");
        }
        else {
            print_string("\n* Input same as output: False");
        }

    }

    close(inputfile);


    print_file_permissions(outputfile);
    close(outputfile);




    return  0;
}
