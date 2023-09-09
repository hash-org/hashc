gperf -F ', 0' -t -j1 -i 1 -g -o -N is_hash_keyword -k'1,3,$' ./keywords/hash.gperf --output-file=./keywords/hash.c
