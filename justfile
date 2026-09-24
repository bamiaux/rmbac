gcc_command := 'gcc -std=c11 -O3 -march=native -DNDEBUG -Wall -Wextra -Wpedantic -Werror rumba.c -o rumba-c'

build:
    {{gcc_command}}

test: build
    ./rumba-c --self-test

corpus: build
    ./rumba-c --corpus third_party/dataset

clean:
    rm -f rumba-c
