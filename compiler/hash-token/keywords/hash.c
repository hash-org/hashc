/* ANSI-C code produced by gperf version 3.1 */
/* Command-line: gperf -F ', 0' -t -j1 -i 1 -g -o -N is_hash_keyword -k'1,3,$' --output-file=./keywords/hash.c ./keywords/hash.gperf  */

#if !((' ' == 32) && ('!' == 33) && ('"' == 34) && ('#' == 35) \
      && ('%' == 37) && ('&' == 38) && ('\'' == 39) && ('(' == 40) \
      && (')' == 41) && ('*' == 42) && ('+' == 43) && (',' == 44) \
      && ('-' == 45) && ('.' == 46) && ('/' == 47) && ('0' == 48) \
      && ('1' == 49) && ('2' == 50) && ('3' == 51) && ('4' == 52) \
      && ('5' == 53) && ('6' == 54) && ('7' == 55) && ('8' == 56) \
      && ('9' == 57) && (':' == 58) && (';' == 59) && ('<' == 60) \
      && ('=' == 61) && ('>' == 62) && ('?' == 63) && ('A' == 65) \
      && ('B' == 66) && ('C' == 67) && ('D' == 68) && ('E' == 69) \
      && ('F' == 70) && ('G' == 71) && ('H' == 72) && ('I' == 73) \
      && ('J' == 74) && ('K' == 75) && ('L' == 76) && ('M' == 77) \
      && ('N' == 78) && ('O' == 79) && ('P' == 80) && ('Q' == 81) \
      && ('R' == 82) && ('S' == 83) && ('T' == 84) && ('U' == 85) \
      && ('V' == 86) && ('W' == 87) && ('X' == 88) && ('Y' == 89) \
      && ('Z' == 90) && ('[' == 91) && ('\\' == 92) && (']' == 93) \
      && ('^' == 94) && ('_' == 95) && ('a' == 97) && ('b' == 98) \
      && ('c' == 99) && ('d' == 100) && ('e' == 101) && ('f' == 102) \
      && ('g' == 103) && ('h' == 104) && ('i' == 105) && ('j' == 106) \
      && ('k' == 107) && ('l' == 108) && ('m' == 109) && ('n' == 110) \
      && ('o' == 111) && ('p' == 112) && ('q' == 113) && ('r' == 114) \
      && ('s' == 115) && ('t' == 116) && ('u' == 117) && ('v' == 118) \
      && ('w' == 119) && ('x' == 120) && ('y' == 121) && ('z' == 122) \
      && ('{' == 123) && ('|' == 124) && ('}' == 125) && ('~' == 126))
/* The character set is not based on ISO-646.  */
#error "gperf generated tables don't work with this execution character set. Please report a bug to <bug-gperf@gnu.org>."
#endif

#line 1 "./keywords/hash.gperf"

#include <stddef.h>
#include <string.h>
#line 6 "./keywords/hash.gperf"
struct hash_keyword {
    char *name;
    unsigned char token;
};

#define TOTAL_KEYWORDS 25
#define MIN_WORD_LENGTH 2
#define MAX_WORD_LENGTH 8
#define MIN_HASH_VALUE 8
#define MAX_HASH_VALUE 32
/* maximum key range = 25, duplicates = 0 */

#ifdef __GNUC__
__inline
#else
#ifdef __cplusplus
inline
#endif
#endif
static unsigned int
hash (register const char *str, register size_t len)
{
  static unsigned char asso_values[] =
    {
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33, 33, 20,  9, 10,
       8,  2, 10, 33, 11,  3, 33, 13,  8, 13,
      11,  7,  7, 33,  3,  1,  1,  1, 10,  3,
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33, 33, 33, 33, 33,
      33, 33, 33, 33, 33, 33
    };
  register unsigned int hval = len;

  switch (hval)
    {
      default:
        hval += asso_values[(unsigned char)str[2]];
      /*FALLTHROUGH*/
      case 2:
      case 1:
        hval += asso_values[(unsigned char)str[0]];
        break;
    }
  return hval + asso_values[(unsigned char)str[len - 1]];
}

struct hash_keyword *
is_hash_keyword (register const char *str, register size_t len)
{
  static struct hash_keyword wordlist[] =
    {
      {"", 0}, {"", 0}, {"", 0}, {"", 0}, {"", 0}, {"", 0},
      {"", 0}, {"", 0},
#line 34 "./keywords/hash.gperf"
      {"true", 23},
#line 15 "./keywords/hash.gperf"
      {"else", 4},
#line 28 "./keywords/hash.gperf"
      {"unsafe", 17},
#line 21 "./keywords/hash.gperf"
      {"struct", 10},
#line 26 "./keywords/hash.gperf"
      {"raw", 15},
#line 12 "./keywords/hash.gperf"
      {"while", 1},
#line 35 "./keywords/hash.gperf"
      {"type", 24},
#line 14 "./keywords/hash.gperf"
      {"if", 3},
#line 18 "./keywords/hash.gperf"
      {"in", 7},
#line 25 "./keywords/hash.gperf"
      {"import", 14},
#line 31 "./keywords/hash.gperf"
      {"mut", 20},
#line 11 "./keywords/hash.gperf"
      {"for", 0},
#line 20 "./keywords/hash.gperf"
      {"enum", 9},
#line 24 "./keywords/hash.gperf"
      {"return", 13},
#line 33 "./keywords/hash.gperf"
      {"impl", 22},
#line 17 "./keywords/hash.gperf"
      {"as", 6},
#line 30 "./keywords/hash.gperf"
      {"priv", 19},
#line 27 "./keywords/hash.gperf"
      {"false", 16},
#line 13 "./keywords/hash.gperf"
      {"loop", 2},
#line 19 "./keywords/hash.gperf"
      {"trait", 8},
#line 29 "./keywords/hash.gperf"
      {"pub", 18},
#line 23 "./keywords/hash.gperf"
      {"break", 12},
#line 16 "./keywords/hash.gperf"
      {"match", 5},
#line 22 "./keywords/hash.gperf"
      {"continue", 11},
#line 32 "./keywords/hash.gperf"
      {"mod", 21}
    };

  if (len <= MAX_WORD_LENGTH && len >= MIN_WORD_LENGTH)
    {
      register unsigned int key = hash (str, len);

      if (key <= MAX_HASH_VALUE)
        {
          register const char *s = wordlist[key].name;

          if (*str == *s && !strcmp (str + 1, s + 1))
            return &wordlist[key];
        }
    }
  return 0;
}
