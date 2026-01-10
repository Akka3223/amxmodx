/*  Pawn compiler - Staging buffer and optimizer
 *
 *  The staging buffer
 *  ------------------
 *  The staging buffer allows buffered output of generated code, deletion
 *  of redundant code, optimization by a tinkering process and reversing
 *  the ouput of evaluated expressions (which is used for the reversed
 *  evaluation of arguments in functions).
 *  Initially, stgwrite() writes to the file directly, but after a call to
 *  stgset(TRUE), output is redirected to the buffer. After a call to
 *  stgset(FALSE), stgwrite()'s output is directed to the file again. Thus
 *  only one routine is used for writing to the output, which can be
 *  buffered output or direct output.
 *
 *  staging buffer variables:   stgbuf  - the buffer
 *                              stgidx  - current index in the staging buffer
 *                              staging - if true, write to the staging buffer;
 *                                        if false, write to file directly.
 *
 *  Copyright (c) ITB CompuPhase, 1997-2005
 *
 *  This software is provided "as-is", without any express or implied warranty.
 *  In no event will the authors be held liable for any damages arising from
 *  the use of this software.
 *
 *  Permission is granted to anyone to use this software for any purpose,
 *  including commercial applications, and to alter it and redistribute it
 *  freely, subject to the following restrictions:
 *
 *  1.  The origin of this software must not be misrepresented; you must not
 *      claim that you wrote the original software. If you use this software in
 *      a product, an acknowledgment in the product documentation would be
 *      appreciated but is not required.
 *  2.  Altered source versions must be plainly marked as such, and must not be
 *      misrepresented as being the original software.
 *  3.  This notice may not be removed or altered from any source distribution.
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>     /* for atoi() */
#include <string.h>
#include <ctype.h>
#if defined FORTIFY
  #include "fortify.h"
#endif
#include "sc.h"

#if defined _MSC_VER
  #pragma warning(push)
  #pragma warning(disable:4125)  /* decimal digit terminates octal escape sequence */
#endif

#include "sc7-in.scp"

#if defined _MSC_VER
  #pragma warning(pop)
#endif

static void stgstring(char *start,char *end);
static void stgopt(char *start,char *end);


/* Grow the staging buffer in larger chunks to reduce realloc frequency
 * during heavy writes. Keep a reasonable cap to avoid runaway growth. */
#define sSTG_GROW   8192
#define sSTG_MAX    32768
/* Flush chunk limit for direct-output buffering (non-staging).
 * When the buffer grows past this size, flush up to the last newline
 * to keep memory use bounded while preserving line integrity. */
#define OUTBUF_FLUSH_LIMIT 16384
/* If a newline-terminated fragment is smaller than this threshold and
 * there is pending buffered output, append then flush once instead of
 * doing a flush + direct write (reduces syscall count on small tails). */
#define SMALL_TAIL_BATCH 64

/* Localized restart heuristic removed; stgopt() always restarts from buffer head. */

static char *stgbuf = NULL;
static int stgmax = 0;  /* current size of the staging buffer */
/* Track current length of the non-staging output buffer to avoid
 * repeated strlen() calls and quadratic concatenation cost.
 */
static int outbuf_len = 0;
/* Track start offset of pending direct-output buffer to avoid memmove
 * when flushing up to the last newline. */
static int outbuf_start = 0;
/* Track the last newline position within the current non-staging buffer
 * to avoid scanning the entire buffer when partially flushing.
 * -1 means 'no newline tracked'. */
static int outbuf_last_nl = -1;

#define CHECK_STGBUFFER(index) if ((int)(index)>=stgmax) grow_stgbuffer((index)+1)

static void grow_stgbuffer(int requiredsize)
{
  char *p;
  int clear = stgbuf==NULL;     /* if previously none, empty buffer explicitly */

  assert(stgmax<requiredsize);
  /* if the staging buffer (holding intermediate code for one line) grows
   * over a few kBytes, there is probably a run-away expression
   */
  if (requiredsize>sSTG_MAX)
    error(102,"staging buffer");    /* staging buffer overflow (fatal error) */
  stgmax=requiredsize+sSTG_GROW;
  if (stgbuf!=NULL)
    p=(char *)realloc(stgbuf,stgmax*sizeof(char));
  else
    p=(char *)malloc(stgmax*sizeof(char));
  if (p==NULL)
    error(102,"staging buffer");    /* staging buffer overflow (fatal error) */
  stgbuf=p;
  if (clear)
    *stgbuf='\0';
}

SC_FUNC void stgbuffer_cleanup(void)
{
  if (stgbuf!=NULL) {
    free(stgbuf);
    stgbuf=NULL;
    stgmax=0;
  } /* if */
}

/* the variables "stgidx" and "staging" are declared in "scvars.c" */

/*  stgmark
 *
 *  Copies a mark into the staging buffer. At this moment there are three
 *  possible marks:
 *     sSTARTREORDER    identifies the beginning of a series of expression
 *                      strings that must be written to the output file in
 *                      reordered order
 *    sENDREORDER       identifies the end of 'reverse evaluation'
 *    sEXPRSTART + idx  only valid within a block that is evaluated in
 *                      reordered order, it identifies the start of an
 *                      expression; the "idx" value is the argument position
 *
 *  Global references: stgidx  (altered)
 *                     stgbuf  (altered)
 *                     staging (referred to only)
 */
SC_FUNC void stgmark(char mark)
{
  if (staging) {
    CHECK_STGBUFFER(stgidx);
    stgbuf[stgidx++]=mark;
  } /* if */
}

static int filewrite(char *str)
{
  if (sc_status==statWRITE)
    return pc_writeasm(outf,str);
  return TRUE;
}

static int filewrite_len(char *str,int len)
{
  if (sc_status==statWRITE)
    return pc_writeasm_len(outf,str,len);
  return TRUE;
}

/*  stgwrite
 *
 *  Writes the string "st" to the staging buffer or to the output file. In the
 *  case of writing to the staging buffer, the terminating byte of zero is
 *  copied too, but... the optimizer can only work on complete lines (not on
 *  fractions of it. Therefore if the string is staged, if the last character
 *  written to the buffer is a '\0' and the previous-to-last is not a '\n',
 *  the string is concatenated to the last string in the buffer (the '\0' is
 *  overwritten). This also means an '\n' used in the middle of a string isn't
 *  recognized and could give wrong results with the optimizer.
 *  Even when writing to the output file directly, all strings are buffered
 *  until a whole line is complete.
 *
 *  Global references: stgidx  (altered)
 *                     stgbuf  (altered)
 *                     staging (referred to only)
 */
SC_FUNC void stgwrite(const char *st)
{
  CHECK_STGBUFFER(0);
  if (staging) {
    if (stgidx>=2 && stgbuf[stgidx-1]=='\0' && stgbuf[stgidx-2]!='\n')
      stgidx-=1;                       /* overwrite last '\0' */
    size_t slen = strlen(st);
    CHECK_STGBUFFER(stgidx + (int)slen + 1);
    memcpy(stgbuf + stgidx, st, slen);
    stgidx += (int)slen;
    stgbuf[stgidx++]='\0';
  } else {
    size_t slen = strlen(st);
    /* If incoming fragment ends with a newline, prefer direct writes.
     * - When buffer is empty: write the fragment directly.
     * - When buffer has pending data: flush pending buffer, then write
     *   the fragment directly, avoiding an extra memcpy into stgbuf. */
    if (slen > 0 && st[slen - 1] == '\n') {
      if (outbuf_len == 0) {
        filewrite_len((char*)st,(int)slen);
        g_outbuf_direct_lines++;
        g_outbuf_bytes_flushed += (unsigned long)slen;
        return;
      } else {
        /* If the tail is small, append then flush once; else do flush+direct. */
        if ((int)slen <= SMALL_TAIL_BATCH) {
          CHECK_STGBUFFER(outbuf_len + (int)slen + 1);
          memcpy(stgbuf + outbuf_len, st, slen);
          outbuf_len += (int)slen;
          stgbuf[outbuf_len] = '\0';
          /* update last newline to the end of the buffer */
          outbuf_last_nl = outbuf_len - 1;
          filewrite_len(stgbuf + outbuf_start, outbuf_len - outbuf_start);
          g_outbuf_flush_on_newline++;
          g_outbuf_bytes_flushed += (unsigned long)(outbuf_len - outbuf_start);
          outbuf_len = 0;
          outbuf_start = 0;
          outbuf_last_nl = -1;
          stgbuf[0] = '\0';
          return;
        } else {
          /* Flush existing pending buffer segment, then write the tail. */
          filewrite_len(stgbuf + outbuf_start, outbuf_len - outbuf_start);
          g_outbuf_flush_on_newline++;
          g_outbuf_bytes_flushed += (unsigned long)(outbuf_len - outbuf_start);
          filewrite_len((char*)st,(int)slen);
          g_outbuf_bytes_flushed += (unsigned long)slen;
          outbuf_len = 0;
          outbuf_start = 0;
          outbuf_last_nl = -1;
          stgbuf[0] = '\0';
          return;
        }
      }
    }
    CHECK_STGBUFFER(outbuf_len + (int)slen + 1);
    memcpy(stgbuf + outbuf_len, st, slen);
    /* Track last newline in the newly appended fragment to avoid full scans. */
    if (slen > 0) {
      int base = outbuf_len;
      const char *p = st;
      /* scan backwards for efficiency to find the last newline in the fragment */
      for (int i = (int)slen - 1; i >= 0; --i) {
        if (p[i] == '\n') { outbuf_last_nl = base + i; break; }
      }
    }
    outbuf_len += (int)slen;
    stgbuf[outbuf_len] = '\0';
    if (outbuf_len > 0 && stgbuf[outbuf_len - 1] == '\n') {
      /* Flush the full pending buffer segment without shifting remainder. */
      filewrite_len(stgbuf + outbuf_start, outbuf_len - outbuf_start);
      g_outbuf_flush_on_newline++;
      g_outbuf_bytes_flushed += (unsigned long)(outbuf_len - outbuf_start);
      outbuf_len = 0;
      outbuf_start = 0;
      outbuf_last_nl = -1;
      stgbuf[0] = '\0';
    } else if (outbuf_len >= OUTBUF_FLUSH_LIMIT) {
      /* Find the last newline and flush up to it, preserving the remainder. */
      int pos = outbuf_last_nl;
      if (pos < outbuf_start) {
        /* fallback: last newline unknown or before start, scan buffer tail */
        pos = outbuf_len - 1;
        while (pos >= outbuf_start && stgbuf[pos] != '\n')
          pos--;
      }
      if (pos >= 0) {
        /* Temporarily terminate after newline, flush, then advance start. */
        char save = stgbuf[pos + 1];
        stgbuf[pos + 1] = '\0';
        filewrite_len(stgbuf + outbuf_start, (pos + 1) - outbuf_start);
        g_outbuf_partial_flushes++;
        g_outbuf_bytes_flushed += (unsigned long)((pos + 1) - outbuf_start);
        stgbuf[pos + 1] = save;
        outbuf_start = pos + 1;
        if (outbuf_last_nl < outbuf_start)
          outbuf_last_nl = -1;
      }
    }
  }
}

/*  stgout
 *
 *  Writes the staging buffer to the output file via stgstring() (for
 *  reversing expressions in the buffer) and stgopt() (for optimizing). It
 *  resets "stgidx".
 *
 *  Global references: stgidx  (altered)
 *                     stgbuf  (referred to only)
 *                     staging (referred to only)
 */
SC_FUNC void stgout(int index)
{
  if (!staging)
    return;
  stgstring(&stgbuf[index],&stgbuf[stgidx]);
  stgidx=index;
}

typedef struct {
  char *start,*end;
} argstack;

/*  stgstring
 *
 *  Analyses whether code strings should be output to the file as they appear
 *  in the staging buffer or whether portions of it should be re-ordered.
 *  Re-ordering takes place in function argument lists; Pawn passes arguments
 *  to functions from right to left. When arguments are "named" rather than
 *  positional, the order in the source stream is indeterminate.
 *  This function calls itself recursively in case it needs to re-order code
 *  strings, and it uses a private stack (or list) to mark the start and the
 *  end of expressions in their correct (reversed) order.
 *  In any case, stgstring() sends a block as large as possible to the
 *  optimizer stgopt().
 *
 *  In "reorder" mode, each set of code strings must start with the token
 *  sEXPRSTART, even the first. If the token sSTARTREORDER is represented
 *  by '[', sENDREORDER by ']' and sEXPRSTART by '|' the following applies:
 *     '[]...'     valid, but useless; no output
 *     '[|...]     valid, but useless; only one string
 *     '[|...|...] valid and usefull
 *     '[...|...]  invalid, first string doesn't start with '|'
 *     '[|...|]    invalid
 */
static void stgstring(char *start,char *end)
{
  char *ptr;
  int nest,argc,arg;
  argstack *stack;

  while (start<end) {
    if (*start==sSTARTREORDER) {
      start+=1;         /* skip token */
      /* allocate a argstack with sMAXARGS items */
      stack=(argstack *)malloc(sMAXARGS*sizeof(argstack));
      if (stack==NULL)
        error(103);     /* insufficient memory */
      nest=1;           /* nesting counter */
      argc=0;           /* argument counter */
      arg=-1;           /* argument index; no valid argument yet */
      do {
        switch (*start) {
        case sSTARTREORDER:
          nest++;
          start++;
          break;
        case sENDREORDER:
          nest--;
          start++;
          break;
        default:
          if ((*start & sEXPRSTART)==sEXPRSTART) {
            if (nest==1) {
              if (arg>=0)
                stack[arg].end=start-1; /* finish previous argument */
              arg=(unsigned char)*start - sEXPRSTART;
              stack[arg].start=start+1;
              if (arg>=argc)
                argc=arg+1;
            } /* if */
            start++;
          } else {
            start+=strlen(start)+1;
          } /* if */
        } /* switch */
      } while (nest); /* enddo */
      if (arg>=0)
        stack[arg].end=start-1;   /* finish previous argument */
      while (argc>0) {
        argc--;
        stgstring(stack[argc].start,stack[argc].end);
      } /* while */
      free(stack);
    } else {
      ptr=start;
      while (ptr<end && *ptr!=sSTARTREORDER)
        ptr+=strlen(ptr)+1;
      stgopt(start,ptr);
      start=ptr;
    } /* if */
  } /* while */
}

/*  stgdel
 *
 *  Scraps code from the staging buffer by resetting "stgidx" to "index".
 *
 *  Global references: stgidx (altered)
 *                     staging (reffered to only)
 */
SC_FUNC void stgdel(int index,cell code_index)
{
  if (staging) {
    stgidx=index;
    code_idx=code_index;
  } /* if */
}

SC_FUNC int stgget(int *index,cell *code_index)
{
  if (staging) {
    *index=stgidx;
    *code_index=code_idx;
  } /* if */
  return staging;
}

/*  stgset
 *
 *  Sets staging on or off. If it's turned off, the staging buffer must be
 *  initialized to an empty string. If it's turned on, the routine makes sure
 *  the index ("stgidx") is set to 0 (it should already be 0).
 *
 *  Global references: staging  (altered)
 *                     stgidx   (altered)
 *                     stgbuf   (contents altered)
 */
SC_FUNC void stgset(int onoff)
{
  staging=onoff;
  if (staging){
    assert(stgidx==0);
    stgidx=0;
    CHECK_STGBUFFER(stgidx);
    /* write any contents that may be put in the buffer by stgwrite()
     * when "staging" was 0
     */
    if (outbuf_len > 0) {
      filewrite_len(stgbuf + outbuf_start, outbuf_len - outbuf_start);
      outbuf_len = 0;
      outbuf_start = 0;
      outbuf_last_nl = -1;
    }
  } /* if */
  stgbuf[0]='\0';
}

/* phopt_init
 * Initialize all sequence strings of the peehole optimizer. The strings
 * are embedded in the .EXE file in compressed format, here we expand
 * them (and allocate memory for the sequences).
 */
static SEQUENCE *sequences = sequences_cmp;
/* Branchless lowercase helper to avoid locale-dependent tolower() calls. */
#define LOWER_CHAR(c) ( ((c)>='A' && (c)<='Z') ? (char)((c) + ('a' - 'A')) : (c) )
/* Prefilter: first alphabetic char (lowercased) of each sequence's find
 * pattern to quickly reject impossible matches without calling
 * matchsequence(). Computed in phopt_init(). For patterns that start with
 * non-alphabetic/meta tokens, the entry is 0 (no prefilter).
 */
static unsigned char *seq_first_lower = NULL;
static int sequences_count = 0;
/* Lowercased copy of each 'find' pattern for cheaper case-insensitive
 * comparisons. Meta characters ('%', '!', ' ', '-') are left untouched. */
static char **seq_find_lower = NULL;
/* Reusable scratch buffer for sequence replacements to avoid malloc/free churn. */
static char *repl_scratch = NULL;
static int repl_scratch_size = 0;

SC_FUNC int phopt_init(void)
{
  /* Count sequences */
  int i, j;
  for (i = 0; sequences[i].find != NULL; i++)
    /* nothing */;
  sequences_count = i;
  seq_first_lower = (unsigned char*)malloc((size_t)sequences_count);
  if (seq_first_lower == NULL)
    return FALSE;
  seq_find_lower = (char**)malloc(sizeof(char*) * (size_t)sequences_count);
  if (seq_find_lower == NULL)
    return FALSE;
  /* Compute first alphabetic literal per find-pattern */
  for (i = 0; i < sequences_count; i++) {
    const char *p = sequences[i].find;
    unsigned char c = 0;
    size_t len = strlen(p);
    char *lower = (char*)malloc(len + 1);
    if (!lower)
      return FALSE;
    /* Build lowercase-only copy */
    for (j = 0; p[j] != '\0'; j++) {
      char ch = p[j];
      if ((ch >= 'A' && ch <= 'Z') || (ch >= 'a' && ch <= 'z'))
        lower[j] = LOWER_CHAR(ch);
      else
        lower[j] = ch;
    }
    lower[len] = '\0';
    seq_find_lower[i] = lower;
    for (j = 0; p[j] != '\0'; j++) {
      char ch = p[j];
      if ((ch >= 'A' && ch <= 'Z') || (ch >= 'a' && ch <= 'z')) {
        c = (unsigned char)LOWER_CHAR(ch);
        break;
      }
      /* stop early on meta that implies non-literal start */
      if (ch == '%' || ch == '!' || ch == ' ' || ch == '-')
        break;
    }
    seq_first_lower[i] = c; /* 0 means 'no prefilter' */
  }
  return TRUE;
}

SC_FUNC int phopt_cleanup(void)
{
  if (seq_first_lower) {
    free(seq_first_lower);
    seq_first_lower = NULL;
  }
  if (seq_find_lower) {
    for (int i = 0; i < sequences_count; i++)
      free(seq_find_lower[i]);
    free(seq_find_lower);
    seq_find_lower = NULL;
  }
  if (repl_scratch) {
    free(repl_scratch);
    repl_scratch = NULL;
    repl_scratch_size = 0;
  }
  return FALSE;
}

#define MAX_OPT_VARS    4
#define MAX_OPT_CAT     4       /* max. values that are concatenated */
#if sNAMEMAX > (PAWN_CELL_SIZE/4) * MAX_OPT_CAT
  #define MAX_ALIAS       sNAMEMAX
#else
  #define MAX_ALIAS       (PAWN_CELL_SIZE/4) * MAX_OPT_CAT
#endif

  /* Fast ASCII checks to avoid function calls in hot loops. */
  static inline int is_alpha_fast(char c) {
    return (c>='A' && c<='Z') || (c>='a' && c<='z');
  }
  static inline int is_digit_fast(char c) {
    return (c>='0' && c<='9');
  }
  static inline int is_alphanum_fast(char c) {
    return is_alpha_fast(c) || is_digit_fast(c) || c=='_';
  }
  static inline int is_alias_char(char c) {
    return c=='-' || c=='+' || is_alphanum_fast(c);
  }

static int matchsequence(const char *start,const char *end,const char *pattern,
                         char symbols[MAX_OPT_VARS][MAX_ALIAS+1],
                         int alias_len[MAX_OPT_VARS],
                         int *match_length)
{
  int var,i;
  const char *start_org=start;
  cell value;
  char *ptr;

  *match_length=0;
  for (var=0; var<MAX_OPT_VARS; var++) {
    symbols[var][0]='\0';
    alias_len[var]=0;
  }

  while (*start=='\t' || *start==' ')
    start++;
  while (*pattern) {
    if (start>=end)
      return FALSE;
    /* Fast path: consume contiguous literal characters until a meta token. */
    if (*pattern!='%' && *pattern!='!' && *pattern!=' ' && *pattern!='-') {
      const char *pl = pattern;
      const char *s = start;
      while (s<end) {
        char cp = *pl;
        if (!cp || cp=='%' || cp=='!' || cp==' ' || cp=='-')
          break;
        char cs = *s;
        if (cs != cp) {
          /* Only case-fold when pattern char is alphabetic (already lowered). */
          if ((cp >= 'a' && cp <= 'z')) {
            if (LOWER_CHAR(cs) != cp)
              return FALSE;
          } else {
            return FALSE;
          }
        }
        s++; pl++;
      }
      start = s;
      pattern = pl;
      continue;
    }
    switch (*pattern) {
    case '%':   /* new "symbol" */
      pattern++;
      assert(isdigit(*pattern));
      var = (*pattern - '0') - 1; /* single digit 1..4 */
      assert(var>=0 && var<MAX_OPT_VARS);
      assert(*start=='-' || is_alphanum_fast(*start));
      {
        const char *p = start;
        while (p<end && is_alias_char(*p))
          p++;
        i = (int)(p - start);
        if (i > MAX_ALIAS)
          i = MAX_ALIAS;
        if (symbols[var][0] != '\0') {
          if (alias_len[var] != i || memcmp(symbols[var], start, (size_t)i) != 0)
            return FALSE; /* symbols should be identical */
        } else {
          memcpy(symbols[var], start, (size_t)i);
          symbols[var][i] = '\0';
          alias_len[var] = i;
        }
        start = p;
      }
      break;
    case '-':
      value=-strtol(pattern+1,(char **)&pattern,16);
      ptr=itoh((ucell)value);
      while (*ptr!='\0') {
        /* itoh() emits lowercase hex; avoid redundant LOWER_CHAR() on ptr */
        if (LOWER_CHAR(*start) != *ptr)
          return FALSE;
        start++;
        ptr++;
      } /* while */
      pattern--;  /* there is an increment following at the end of the loop */
      break;
    case ' ':
      if (*start!='\t' && *start!=' ')
        return FALSE;
      /* guard bounds for both space and tab */
      while (start<end && (*start=='\t' || *start==' '))
        start++;
      break;
    case '!':
      while (start<end && (*start=='\t' || *start==' '))
        start++;                /* skip trailing white space */
      if (*start!='\n')
        return FALSE;
      assert(*(start+1)=='\0');
      start+=2;                 /* skip '\n' and '\0' */
      if (*(pattern+1)!='\0') {
        /* skip leading whitespace of next instruction; guard end before deref */
        while (start<end && (*start=='\t' || *start==' '))
          start++;
      }
      break;
    default:
      {
        char cp = *pattern;
        char cs = *start;
        if (cs != cp) {
          if ((cp >= 'a' && cp <= 'z')) {
            if (LOWER_CHAR(cs) != cp)
              return FALSE;
          } else {
            return FALSE;
          }
        }
      }
      start++;
    } /* switch */
    pattern++;
  } /* while */

  *match_length=(int)(start-start_org);
  return TRUE;
}


static char *replacesequence(const char *pattern,
                             char symbols[MAX_OPT_VARS][MAX_ALIAS+1],
                             int alias_len[MAX_OPT_VARS],
                             int *repl_length)
{
  const char *lptr;
  int var;
  char *buffer;

  /* calculate the length of the new buffer
   * this is the length of the pattern plus the length of all symbols (note
   * that the same symbol may occur multiple times in the pattern) plus
   * line endings and startings ('\t' to start a line and '\n\0' to end one)
   */
  assert(repl_length!=NULL);
  *repl_length=0;
  lptr=pattern;
  while (*lptr) {
    switch (*lptr) {
    case '%':
      lptr++;           /* skip '%' */
      assert(isdigit(*lptr));
      var = (*lptr - '0') - 1; /* single digit 1..4 */
      assert(var>=0 && var<MAX_OPT_VARS);
      assert(symbols[var][0]!='\0');    /* variable should be defined */
      *repl_length+=alias_len[var];
      break;
    case '!':
      *repl_length+=3;  /* '\t', '\n' & '\0' */
      break;
    default:
      *repl_length+=1;
    } /* switch */
    lptr++;
  } /* while */

  /* allocate or grow a reusable scratch buffer */
  if (repl_scratch_size < *repl_length) {
    char *nbuf = (char*)realloc(repl_scratch, *repl_length);
    if (!nbuf)
      return (char*)error(103);
    repl_scratch = nbuf;
    repl_scratch_size = *repl_length;
  }
  buffer = repl_scratch;

  /* replace the pattern into this temporary buffer */
  char *ptr=buffer;
  *ptr++='\t';         /* the "replace" patterns do not have tabs */
  while (*pattern) {
    assert((int)(ptr-buffer)<*repl_length);
    switch (*pattern) {
    case '%':
      /* write out the symbol */
      pattern++;
      assert(isdigit(*pattern));
      var = (*pattern - '0') - 1; /* single digit 1..4 */
      assert(var>=0 && var<MAX_OPT_VARS);
      assert(symbols[var][0]!='\0');    /* variable should be defined */
      memcpy(ptr, symbols[var], (size_t)alias_len[var]);
      ptr+=alias_len[var];
      break;
    case '!':
      /* finish the line, optionally start the next line with an indent */
      *ptr++='\n';
      *ptr++='\0';
      if (*(pattern+1)!='\0')
        *ptr++='\t';
      break;
    default:
      *ptr++=*pattern;
    } /* switch */
    pattern++;
  } /* while */

  assert((int)(ptr-buffer)==*repl_length);
  return buffer;
}

static void strreplace(char *dest,char *replace,int sub_length,int repl_length,int dest_length)
{
  int offset=sub_length-repl_length;
  if (offset>0) {               /* delete a section */
    memmove(dest,dest+offset,dest_length-offset);
  } else if (offset<0) {        /* insert a section */
    memmove(dest-offset, dest, dest_length);
  } /* if */
  memcpy(dest, replace, repl_length);
}

/*  stgopt
 *
 *  Optimizes the staging buffer by checking for series of instructions that
 *  can be coded more compact. The routine expects the lines in the staging
 *  buffer to be separated with '\n' and '\0' characters.
 *
 *  The longest sequences should probably be checked first.
 */

static void stgopt(char *start,char *end)
{
  char symbols[MAX_OPT_VARS][MAX_ALIAS+1];
  int alias_len[MAX_OPT_VARS];
  int seq,match_length,repl_length;
  int matches;
  char *debut=start;
  /* Heuristic removed: no localized restart, keep behavior simple & fast. */

  assert(sequences!=NULL);
  /* do not match anything if debug-level is maximum */
  if ((sc_debug & sNOOPTIMIZE)==0 && sc_status==statWRITE) {
    do {
      matches=0;
      start=debut;
      while (start<end) {
        seq=0;
        /* Compute start's first alphabetic character once for all sequence checks. */
        const char *slead = start;
        while (slead<end && (*slead=='\t' || *slead==' '))
          slead++;
        unsigned char cs = 0;
        if (slead < end) {
          char ch = *slead;
          if ((ch >= 'A' && ch <= 'Z') || (ch >= 'a' && ch <= 'z'))
            cs = (unsigned char)LOWER_CHAR(ch);
        }
        while (sequences[seq].find!=NULL) {
          assert(seq>=0);
          /* Quick reject: compare first alphabetic char of the instruction
           * against the precomputed first-letter filter of the pattern. If
           * the pattern expects a letter and the instruction doesn't start
           * with one, skip it too. */
          if (seq_first_lower) {
            unsigned char fl = seq_first_lower[seq];
            if (fl != 0) {
              if (cs == 0 || fl != cs) {
                seq++;
                continue;
              }
            }
          }
          if (matchsequence(start,end,seq_find_lower ? seq_find_lower[seq] : sequences[seq].find,symbols,alias_len,&match_length)) {
            char *replace=replacesequence(sequences[seq].replace,symbols,alias_len,&repl_length);
            /* If the replacement is bigger than the original section, we may need
             * to "grow" the staging buffer. This is quite complex, due to the
             * re-ordering of expressions that can also happen in the staging
             * buffer. In addition, it should not happen: the peephole optimizer
             * must replace sequences with *shorter* sequences, not longer ones.
             * So, I simply forbid sequences that are longer than the ones they
             * are meant to replace.
             */
            assert(match_length>=repl_length);
            if (match_length>=repl_length) {
              strreplace(start,replace,match_length,repl_length,(int)(end-start));
              end-=match_length-repl_length;
              code_idx-=sequences[seq].savesize;
              /* restart search for matches at the beginning of this line */
              seq=0;
              matches++;
              /* localized restart heuristic removed */
            } else {
              /* actually, we should never get here (match_length<repl_length) */
              assert(0);
              seq++;
            } /* if */
          } else {
            seq++;
          } /* if */
        } /* while */
        assert(sequences[seq].find==NULL);
        while (*start++ != '\0') { /* to next string */ }
      } /* while (start<end) */
      /* Always restart from buffer head; no localized restart. */
    } while (matches>0);
  } /* if ((sc_debug & sNOOPTIMIZE)==0 && sc_status==statWRITE) */

  for (start=debut; start<end;) {
    filewrite(start);
    while (*start++ != '\0') { /* to next string */ }
  }
}

#undef SCPACK_TABLE
