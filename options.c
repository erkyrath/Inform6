/* ------------------------------------------------------------------------- */
/*   "options" : Compiler options and memory settings                        */
/*                                                                           */
/*   Part of Inform 6.43                                                     */
/*   copyright (c) Graham Nelson 1993 - 2024                                 */
/*                                                                           */
/* ------------------------------------------------------------------------- */

#include "header.h"

/* ### Notes: 
   set_memory_sizes() is default-setting, so that will move to options table.
   Eliminate adjust_memory_sizes(). If we make $LIST smarter, we don't need it.
   select_target() handles a lot of bounds and mod checking. This is called after all option setting (including !%). Rework this to call the master option-grabber (table to vars).

   INDIV_PROP_START is handled inconsistently.
   SERIAL is a six-character string. (And not in $LIST?)
   A couple of Glulx options are rounded up mod 256.
   Same Glulx options are defined as int32.
   NUM_ATTR_BYTES is rounded up 3 mod 4.
   MAX_ABBREVS, MAX_DYNAMIC_STRINGS fight in Z-code.
 ### */

/* What platform does this option apply to? */
enum optionuse {
    OPTUSE_ALL         = 0,  /* all targets */
    OPTUSE_ZCODE       = 1,  /* Z-code only */
    OPTUSE_GLULX       = 2,  /* Glulx only */
    OPTUSE_OBSOLETE_I5 = 5,  /* obsolete Inform 5 option */
    OPTUSE_OBSOLETE_I6 = 6,  /* obsolete Inform 6 option */
};

/* What are the requirements for this option's value?
   (Note that, at present, no option can have a negative value.)
*/
enum optionlimit {
    OPTLIM_ANY         = 0,  /* any non-negative value */
    OPTLIM_TOMAX       = 1,  /* zero to N inclusive */
    OPTLIM_TOMAXZONLY  = 2,  /* zero to N inclusive in Z-code; unlimited in Glulx */
    OPTLIM_MUL256      = 3,  /* any, round up to a multiple of 256 */
};

typedef struct optionlimit_s {
    enum optionlimit limittype;
    int32 maxval;
} optionlimitt;

typedef struct platformval_s {
    int32 z;
    int32 g;
} platformval;

/* Macros for initializing a platformval compactly. */
#define DEFAULTVAL(v) { (v), (v) }
#define DEFAULTVALS(z, g) { (z), (g) }

/* Grab the appropriate part of a platformval. */
#define SELECTVAL(i) (glulx_mode ? alloptions[i].val.g : alloptions[i].val.z)

/* The main option structure. */
typedef struct optiont_s {
    char *name;
    char *desc;
    enum optionuse use;
    optionlimitt limit;
    platformval val;
    int precedence;
} optiont;

/* Enum for referring to individual options. This doesn't include obsolete
   options, because we never have to refer to those.
   
   Must match the order of alloptions[], which is the order of the $LIST
   in the old options system, which was not very systematic. */
enum optionindex {
    OPT_MAX_ABBREVS               = 0,
    OPT_NUM_ATTR_BYTES            = 1,
    OPT_DICT_WORD_SIZE            = 2,
    OPT_DICT_CHAR_SIZE            = 3,
    OPT_GRAMMAR_VERSION           = 4,
    OPT_GRAMMAR_META_FLAG         = 5,
    OPT_MAX_DYNAMIC_STRINGS       = 6,
    OPT_HASH_TAB_SIZE             = 7,
    OPT_ZCODE_HEADER_EXT_WORDS    = 8,
    OPT_ZCODE_HEADER_FLAGS_3      = 9,
    OPT_ZCODE_FILE_END_PADDING    = 10,
    OPT_ZCODE_LESS_DICT_DATA      = 11,
    OPT_ZCODE_MAX_INLINE_STRING   = 12,
    OPT_INDIV_PROP_START          = 13,
    OPT_MEMORY_MAP_EXTENSION      = 14,
    OPT_GLULX_OBJECT_EXT_BYTES    = 15,
    OPT_MAX_STACK_SIZE            = 16,
    OPT_TRANSCRIPT_FORMAT         = 17,
    OPT_WARN_UNUSED_ROUTINES      = 18,
    OPT_OMIT_UNUSED_ROUTINES      = 19,
    OPT_STRIP_UNREACHABLE_LABELS  = 20,
    OPT_OMIT_SYMBOL_TABLE         = 21,
    OPT_DICT_IMPLICIT_SINGULAR    = 22,
    OPT_DICT_TRUNCATE_FLAG        = 23,
    OPT_LONG_DICT_FLAG_BUG        = 24,
    OPT_SERIAL                    = 25,
    OPT_OPTIONS_COUNT             = 26, /* terminator */
};

static optiont alloptions[] = {
    {
        "MAX_ABBREVS",
        "\
  MAX_ABBREVS is the maximum number of declared abbreviations.  It is not \n\
  allowed to exceed 96 in Z-code. (This is not meaningful in Glulx, where \n\
  there is no limit on abbreviations.)\n",
        OPTUSE_ZCODE,
        { OPTLIM_TOMAX, 96 },
        DEFAULTVAL(64),
    },
    {
        "NUM_ATTR_BYTES",
        "\
  NUM_ATTR_BYTES is the space used to store attribute flags. Each byte \n\
  stores eight attributes. In Z-code this is always 6 (only 4 are used in \n\
  v3 games). In Glulx it can be any number which is a multiple of four, \n\
  plus three.\n",
        OPTUSE_GLULX,
        /* We could have a special OPTLIM_3MOD4 here, but we don't.
           We'll fix up the value at set_compile_variables() time. */
        { OPTLIM_ANY },
        DEFAULTVALS(6, 7),
    },
    {
        "DICT_WORD_SIZE",
        "\
  DICT_WORD_SIZE is the number of characters in a dictionary word. In \n\
  Z-code this is always 6 (only 4 are used in v3 games). In Glulx it \n\
  can be any number.\n",
        OPTUSE_GLULX,
        { OPTLIM_ANY },
        DEFAULTVALS(6, 9),
    },
    {
        "DICT_CHAR_SIZE",
        "\
  DICT_CHAR_SIZE is the byte size of one character in the dictionary. \n\
  (This is only meaningful in Glulx, since Z-code has compressed dictionary \n\
  words.) It can be either 1 (the default) or 4 (to enable full Unicode \n\
  input.)\n",
        OPTUSE_GLULX,
        /* We could have a special OPTLIM_1OR4 here, but we don't. If the
           user selects 0/2/3, we'll fix it at set_compile_variables()
           time. */
        { OPTLIM_TOMAX, 4 },
        DEFAULTVAL(1),
    },
    {
        "GRAMMAR_VERSION",
        "\
  GRAMMAR_VERSION defines the table format for the verb grammar. 2 is \n\
  the Inform standard. 1 is an older version based on Infocom's format. \n\
  The default is 1 in Z-code, 2 in Glulx.\n",
        OPTUSE_ALL,
        { OPTLIM_ANY }, /* limited in set_grammar_version() */
        DEFAULTVALS(1, 2),
    },
    {
        "GRAMMAR_META_FLAG",
        "\
  GRAMMAR_META_FLAG indicates actions which have the 'meta' flag by \n\
  ensure that their values are <= #largest_meta_action. This allows \n\
  individual actions to be marked 'meta', rather than relying on dict \n\
  word flags.\n",
        OPTUSE_ALL,
        { OPTLIM_TOMAX, 1 },
        DEFAULTVAL(0),
    },
    {
        "MAX_DYNAMIC_STRINGS",
        "\
  MAX_DYNAMIC_STRINGS is the maximum number of string substitution variables \n\
  (\"@00\" or \"@(0)\").  It is not allowed to exceed 96 in Z-code.\n",
        OPTUSE_ALL,
        /* This is a special case because it's meaningful on both platforms,
           but only limited in Z-code. */
        { OPTLIM_TOMAXZONLY, 96 },
        DEFAULTVALS(32, 100),
    },
    {
        "HASH_TAB_SIZE",
        "\
  HASH_TAB_SIZE is the size of the hash tables used for the heaviest \n\
  symbols banks.\n",
        OPTUSE_ALL,
        { OPTLIM_ANY },
        DEFAULTVAL(512),
    },
    {
        "ZCODE_HEADER_EXT_WORDS",
        "\
  ZCODE_HEADER_EXT_WORDS is the number of words in the Z-code header \n\
  extension table (Z-Spec 1.0). The -W switch also sets this. It defaults \n\
  to 3, but can be set higher. (It can be set lower if no Unicode \n\
  translation table is created.)\n",
        OPTUSE_ZCODE,
        { OPTLIM_ANY },
        /* Backwards-compatible behavior: allow for a unicode table
           whether we need one or not. The user can set this to zero if
           there's no unicode table. */
        DEFAULTVAL(3),
    },
    {
        "ZCODE_HEADER_FLAGS_3",
        "\
  ZCODE_HEADER_FLAGS_3 is the value to store in the Flags 3 word of the \n\
  header extension table (Z-Spec 1.1).\n",
        OPTUSE_ZCODE,
        { OPTLIM_ANY },
        DEFAULTVAL(0),
    },
    {
        "ZCODE_FILE_END_PADDING",
        "\
  ZCODE_FILE_END_PADDING, if set, pads the game file length to a multiple \n\
  of 512 bytes. (Z-code only.)\n",
        OPTUSE_ZCODE,
        { OPTLIM_ANY },
        DEFAULTVAL(1),
    },
    {
        "ZCODE_LESS_DICT_DATA",
        "\
  ZCODE_LESS_DICT_DATA, if set, provides each dict word with two data bytes \n\
  rather than three. (Z-code only.)\n",
        OPTUSE_ZCODE,
        { OPTLIM_ANY },
        DEFAULTVAL(0),
    },
    {
        "ZCODE_MAX_INLINE_STRING",
        "\
  ZCODE_MAX_INLINE_STRING is the length beyond which string literals cannot \n\
  be inlined in assembly opcodes. (Z-code only.)\n",
        OPTUSE_ZCODE,
        { OPTLIM_ANY },
        DEFAULTVAL(32),
    },
    {
        "INDIV_PROP_START",
        "\
  Properties 1 to INDIV_PROP_START-1 are common properties; individual \n\
  properties are numbered INDIV_PROP_START and up.\n",
        OPTUSE_ALL,
        { OPTLIM_ANY },
        DEFAULTVALS(64, 256),
    },
    {
        "MEMORY_MAP_EXTENSION",
        "\
  MEMORY_MAP_EXTENSION is the number of bytes (all zeroes) to map into \n\
  memory after the game file. (Glulx only)\n",
        OPTUSE_GLULX,
        { OPTLIM_MUL256 },
        DEFAULTVAL(0),
    },
    {
        "GLULX_OBJECT_EXT_BYTES",
        "\
  GLULX_OBJECT_EXT_BYTES is an amount of additional space to add to each \n\
  object record. It is initialized to zero bytes, and the game is free to \n\
  use it as desired. (This is only meaningful in Glulx, since Z-code \n\
  specifies the object structure.)\n",
        OPTUSE_GLULX,
        { OPTLIM_ANY },
        DEFAULTVAL(0),
    },
    {
        "MAX_STACK_SIZE",
        "\
  MAX_STACK_SIZE is the maximum size (in bytes) of the interpreter stack \n\
  during gameplay. (Glulx only)\n",
        OPTUSE_GLULX,
        { OPTLIM_MUL256 },
        /* We estimate the default Glulx stack size at 4096. That's about
           enough for 90 nested function calls with 8 locals each -- the
           same capacity as the Z-Spec's suggestion for Z-machine stack
           size. Note that Inform 7 wants more stack; I7-generated code
           sets MAX_STACK_SIZE to 65536 by default. */
        DEFAULTVAL(4096),
    },
    {
        "TRANSCRIPT_FORMAT",
        "\
  TRANSCRIPT_FORMAT, if set to 1, adjusts the gametext.txt transcript for \n\
  easier machine processing; each line will be prefixed by its context.\n",
        OPTUSE_ALL,
        { OPTLIM_TOMAX, 1 },
        DEFAULTVAL(0),
    },
    {
        "WARN_UNUSED_ROUTINES",
        "\
  WARN_UNUSED_ROUTINES, if set to 2, will display a warning for each \n\
  routine in the game file which is never called. (This includes \n\
  routines called only from uncalled routines, etc.) If set to 1, will warn \n\
  only about functions in game code, not in the system library.\n",
        OPTUSE_ALL,
        { OPTLIM_TOMAX, 2 },
        DEFAULTVAL(0),
    },
    {
        "OMIT_UNUSED_ROUTINES",
        "\
  OMIT_UNUSED_ROUTINES, if set to 1, will avoid compiling unused routines \n\
  into the game file.\n",
        OPTUSE_ALL,
        { OPTLIM_TOMAX, 1 },
        DEFAULTVAL(0),
    },
    {
        "STRIP_UNREACHABLE_LABELS",
        "\
  STRIP_UNREACHABLE_LABELS, if set to 1, will skip labels in unreachable \n\
  statements. Jumping to a skipped label is an error. If 0, all labels \n\
  will be compiled, at the cost of less optimized code. The default is 1.\n",
        OPTUSE_ALL,
        { OPTLIM_TOMAX, 1 },
        DEFAULTVAL(1),
    },
    {
        "OMIT_SYMBOL_TABLE",
        "\
  OMIT_SYMBOL_TABLE, if set to 1, will skip compiling debug symbol names \n\
  into the game file.\n",
        OPTUSE_ALL,
        { OPTLIM_TOMAX, 1 },
        DEFAULTVAL(0),
    },
    {
        "DICT_IMPLICIT_SINGULAR",
        "\
  DICT_IMPLICIT_SINGULAR, if set to 1, will cause dict words in noun \n\
  context to have the '//s' flag if the '//p' flag is not set.\n",
        OPTUSE_ALL,
        { OPTLIM_TOMAX, 1 },
        DEFAULTVAL(0),
    },
    {
        "DICT_TRUNCATE_FLAG",
        "\
  DICT_TRUNCATE_FLAG, if set to 1, will set bit 6 of a dict word if the \n\
  word is truncated (extends beyond DICT_WORD_SIZE). If 0, bit 6 will be \n\
  set for verbs (legacy behavior). \n",
        OPTUSE_ALL,
        { OPTLIM_TOMAX, 1 },
        DEFAULTVAL(0),
    },
    {
        "LONG_DICT_FLAG_BUG",
        "\
  LONG_DICT_FLAG_BUG, if set to 0, will fix the old bug which ignores \n\
  the '//p' flag in long dictionary words. If 1, the buggy behavior is \n\
  retained.\n",
        OPTUSE_ALL,
        { OPTLIM_TOMAX, 1 },
        DEFAULTVAL(1),
    },
    {
        "SERIAL",
        "\
  SERIAL, if set, will be used as the six digit serial number written into \n\
  the header of the output file.\n",
        OPTUSE_ALL,
        { OPTLIM_TOMAX, 999999 },
        DEFAULTVAL(0),
    },
    
    /* obsolete options run past OPT_OPTIONS_COUNT */
    {
        "BUFFER_LENGTH",
        NULL, OPTUSE_OBSOLETE_I5,
    },
    {
        "MAX_BANK_SIZE",
        NULL, OPTUSE_OBSOLETE_I5,
    },
    {
        "BANK_CHUNK_SIZE",
        NULL, OPTUSE_OBSOLETE_I5,
    },
    {
        "MAX_OLDEPTH",
        NULL, OPTUSE_OBSOLETE_I5,
    },
    {
        "MAX_ROUTINES",
        NULL, OPTUSE_OBSOLETE_I5,
    },
    {
        "MAX_GCONSTANTS",
        NULL, OPTUSE_OBSOLETE_I5,
    },
    {
        "MAX_FORWARD_REFS",
        NULL, OPTUSE_OBSOLETE_I5,
    },
    {
        "STACK_SIZE",
        NULL, OPTUSE_OBSOLETE_I5,
    },
    {
        "STACK_LONG_SLOTS",
        NULL, OPTUSE_OBSOLETE_I5,
    },
    {
        "STACK_SHORT_LENGTH",
        NULL, OPTUSE_OBSOLETE_I5,
    },
    {
        "MAX_QTEXT_SIZE",
        NULL, OPTUSE_OBSOLETE_I6,
    },
    {
        "MAX_SYMBOLS",
        NULL, OPTUSE_OBSOLETE_I6,
    },
    {
        "SYMBOLS_CHUNK_SIZE",
        NULL, OPTUSE_OBSOLETE_I6,
    },
    {
        "MAX_OBJECTS",
        NULL, OPTUSE_OBSOLETE_I6,
    },
    {
        "MAX_ACTIONS",
        NULL, OPTUSE_OBSOLETE_I6,
    },
    {
        "MAX_ADJECTIVES",
        NULL, OPTUSE_OBSOLETE_I6,
    },
    {
        "MAX_DICT_ENTRIES",
        NULL, OPTUSE_OBSOLETE_I6,
    },
    {
        "MAX_STATIC_DATA",
        NULL, OPTUSE_OBSOLETE_I6,
    },
    {
        "MAX_PROP_TABLE_SIZE",
        NULL, OPTUSE_OBSOLETE_I6,
    },
    {
        "MAX_ARRAYS",
        NULL, OPTUSE_OBSOLETE_I6,
    },
    {
        "MAX_EXPRESSION_NODES",
        NULL, OPTUSE_OBSOLETE_I6,
    },
    {
        "MAX_VERBS",
        NULL, OPTUSE_OBSOLETE_I6,
    },
    {
        "MAX_VERBSPACE",
        NULL, OPTUSE_OBSOLETE_I6,
    },
    {
        "MAX_LABELS",
        NULL, OPTUSE_OBSOLETE_I6,
    },
    {
        "MAX_LINESPACE",
        NULL, OPTUSE_OBSOLETE_I6,
    },
    {
        "MAX_NUM_STATIC_STRINGS",
        NULL, OPTUSE_OBSOLETE_I6,
    },
    {
        "MAX_STATIC_STRINGS",
        NULL, OPTUSE_OBSOLETE_I6,
    },
    {
        "MAX_ZCODE_SIZE",
        NULL, OPTUSE_OBSOLETE_I6,
    },
    {
        "MAX_LINK_DATA_SIZE",
        NULL, OPTUSE_OBSOLETE_I6,
    },
    {
        "MAX_LOW_STRINGS",
        NULL, OPTUSE_OBSOLETE_I6,
    },
    {
        "MAX_TRANSCRIPT_SIZE",
        NULL, OPTUSE_OBSOLETE_I6,
    },
    {
        "MAX_CLASSES",
        NULL, OPTUSE_OBSOLETE_I6,
    },
    {
        "MAX_INCLUSION_DEPTH",
        NULL, OPTUSE_OBSOLETE_I6,
    },
    {
        "MAX_SOURCE_FILES",
        NULL, OPTUSE_OBSOLETE_I6,
    },
    {
        "MAX_INDIV_PROP_TABLE_SIZE",
        NULL, OPTUSE_OBSOLETE_I6,
    },
    {
        "MAX_OBJ_PROP_TABLE_SIZE",
        NULL, OPTUSE_OBSOLETE_I6,
    },
    {
        "MAX_OBJ_PROP_COUNT",
        NULL, OPTUSE_OBSOLETE_I6,
    },
    {
        "MAX_LOCAL_VARIABLES",
        NULL, OPTUSE_OBSOLETE_I6,
    },
    {
        "MAX_GLOBAL_VARIABLES",
        NULL, OPTUSE_OBSOLETE_I6,
    },
    {
        "ALLOC_CHUNK_SIZE",
        NULL, OPTUSE_OBSOLETE_I6,
    },
    {
        "MAX_UNICODE_CHARS",
        NULL, OPTUSE_OBSOLETE_I6,
    },
    {
        NULL, /* terminator */
    },
};

/* Find an option entry by name (including obsolete options).
*/
static optiont *find_option(char *str)
{
    int ix;
    for (ix=0; alloptions[ix].name; ix++) {
        if (strcmp(str, alloptions[ix].name) == 0)
            return &alloptions[ix];
    }
    return NULL;
}

/* Prepare the options module for use.
*/
extern void prepare_compiler_options(void)
{
    int ix;

    /* Set fields in the alloptions[] table that weren't statically
       initialized above. */
    for (ix=0; alloptions[ix].name; ix++) {
        alloptions[ix].precedence = DEFAULT_OPTPREC;
    }

    /* Apply all the Z-machine default values. We're not using them yet;
       compilation won't begin for a while. We just want to set consistent
       starting values in case some stray bit of code refers to a compiler
       variable early. */
    apply_compiler_options();
}

/* Set an option to a given value.

   We will enforce option limits (minima, maxima, multiple-of-N) before
   setting the value.
   
   The precedence value indicates where the option came from. Higher
   precedence sources (command line) override lower precedence (header
   comments).

   Note that we do not necessarily know whether the target is Z-code
   or Glulx when this is called. The option structure has two values,
   perhaps differing; we will set both.
 */
extern void set_compiler_option(char *str, int32 val, int prec)
{
    optiont *opt = find_option(str);
    if (!opt) {
        printf("No such memory setting as \"%s\"\n", str);
        return;
    }
    if (opt->use == OPTUSE_OBSOLETE_I5) {
        if (!nowarnings_switch)
            printf("The Inform 5 memory setting \"%s\" has been withdrawn.\n", str);
        return;
    }
    if (opt->use == OPTUSE_OBSOLETE_I6) {
        if (!nowarnings_switch)
            printf("The Inform 6 memory setting \"%s\" is no longer needed and has been withdrawn.\n", str);
        return;
    }

    if (prec < opt->precedence) {
        /* Already set at a higher level. */
        return;
    }
    opt->precedence = prec;

    switch (opt->limit.limittype) {
    case OPTLIM_TOMAXZONLY:
        /* This is a special case; we apply the max only on one platform
           and return immediately. */
        if (val < 0)
            val = 0;
        opt->val.g = val;
        if (val > opt->limit.maxval)
            val = opt->limit.maxval;
        opt->val.z = val;
        return;
    case OPTLIM_TOMAX:
        if (val < 0)
            val = 0;
        if (val > opt->limit.maxval)
            val = opt->limit.maxval;
        break;
    case OPTLIM_MUL256:
        if (val < 0)
            val = 0;
        val = (val + 0xFF) & (~0xFF);
        break;
    case OPTLIM_ANY:
    default:
        break;
    }

    opt->val.z = val;
    opt->val.g = val;
}

/* Display all the options (for $LIST), assuming the current target platform
   (glulx_mode).
*/
extern void list_compiler_options(void)
{
    int ix;
    
    printf("+--------------------------------------+\n");
    printf("|  %25s = %-7s |\n", "Compiler option", "Value");
    printf("+--------------------------------------+\n");

    for (ix=0; alloptions[ix].name; ix++) {
        int32 val = SELECTVAL(ix);
        enum optionuse use = alloptions[ix].use;
        /* Skip all the obsolete options. */
        if (use == OPTUSE_OBSOLETE_I5 || use == OPTUSE_OBSOLETE_I6)
            continue;
        /* Also skip wrong-platform options. */
        if (!glulx_mode) {
            if (use == OPTUSE_GLULX)
                continue;
        }
        else {
            if (use == OPTUSE_ZCODE)
                continue;
        }
        /* Don't display the serial number; it's not really a setting. */
        if (ix == OPT_SERIAL)
            continue;
        printf("|  %25s = %-7d |\n", alloptions[ix].name, val);
    }

    printf("+--------------------------------------+\n");
}

/* Display help for a compiler option.
*/
extern void explain_compiler_option(char *str)
{
    optiont *opt = find_option(str);
    if (!opt) {
        printf("No such memory setting as \"%s\"\n", str);
        return;
    }
    if (opt->use == OPTUSE_OBSOLETE_I5) {
        printf("The Inform 5 memory setting \"%s\" has been withdrawn.\n", str);
        return;
    }
    if (opt->use == OPTUSE_OBSOLETE_I6) {
        printf("The Inform 6 memory setting \"%s\" is no longer needed and has been withdrawn.\n", str);
        return;
    }
    if (!opt->desc) {
        printf("(no documentation)");
        return;
    }
    
    printf("\n%s", opt->desc);
    if (opt->val.z == opt->val.g) {
        printf("\n  (currently: %d)\n", opt->val.z);
    }
    else {
        printf("\n  (currently: %d for Z-code, %d for Glulx)\n", opt->val.z, opt->val.g);
    }
}

/* Apply the options to our compiler variables. At this point we *do*
   know the target platform (glulx_mode is TRUE or FALSE) and all
   options have valid values.
*/
extern void apply_compiler_options(void)
{
    MAX_ABBREVS = SELECTVAL(OPT_MAX_ABBREVS);
    NUM_ATTR_BYTES = SELECTVAL(OPT_NUM_ATTR_BYTES);
    DICT_WORD_SIZE = SELECTVAL(OPT_DICT_WORD_SIZE);
    DICT_CHAR_SIZE = SELECTVAL(OPT_DICT_CHAR_SIZE);
    GRAMMAR_META_FLAG = SELECTVAL(OPT_GRAMMAR_META_FLAG);
    MAX_DYNAMIC_STRINGS = SELECTVAL(OPT_MAX_DYNAMIC_STRINGS);
    HASH_TAB_SIZE = SELECTVAL(OPT_HASH_TAB_SIZE);
    ZCODE_HEADER_EXT_WORDS = SELECTVAL(OPT_ZCODE_HEADER_EXT_WORDS);
    ZCODE_HEADER_FLAGS_3 = SELECTVAL(OPT_ZCODE_HEADER_FLAGS_3);
    ZCODE_FILE_END_PADDING = SELECTVAL(OPT_ZCODE_FILE_END_PADDING);
    ZCODE_LESS_DICT_DATA = SELECTVAL(OPT_ZCODE_LESS_DICT_DATA);
    ZCODE_MAX_INLINE_STRING = SELECTVAL(OPT_ZCODE_MAX_INLINE_STRING);
    INDIV_PROP_START = SELECTVAL(OPT_INDIV_PROP_START);
    MEMORY_MAP_EXTENSION = SELECTVAL(OPT_MEMORY_MAP_EXTENSION);
    GLULX_OBJECT_EXT_BYTES = SELECTVAL(OPT_GLULX_OBJECT_EXT_BYTES);
    MAX_STACK_SIZE = SELECTVAL(OPT_MAX_STACK_SIZE);
    TRANSCRIPT_FORMAT = SELECTVAL(OPT_TRANSCRIPT_FORMAT);
    WARN_UNUSED_ROUTINES = SELECTVAL(OPT_WARN_UNUSED_ROUTINES);
    OMIT_UNUSED_ROUTINES = SELECTVAL(OPT_OMIT_UNUSED_ROUTINES);
    STRIP_UNREACHABLE_LABELS = SELECTVAL(OPT_STRIP_UNREACHABLE_LABELS);
    OMIT_SYMBOL_TABLE = SELECTVAL(OPT_OMIT_SYMBOL_TABLE);
    DICT_IMPLICIT_SINGULAR = SELECTVAL(OPT_DICT_IMPLICIT_SINGULAR);
    DICT_TRUNCATE_FLAG = SELECTVAL(OPT_DICT_TRUNCATE_FLAG);
    LONG_DICT_FLAG_BUG = SELECTVAL(OPT_LONG_DICT_FLAG_BUG);

    /* Grammar version: this will be handled later, in verbs_begin_pass(). */

    /* Serial number: only set it if a non-default value has been given. */
    if (alloptions[OPT_SERIAL].precedence > DEFAULT_OPTPREC) {
        int32 val = SELECTVAL(OPT_SERIAL);
        sprintf(serial_code_buffer,"%06d", val);
        serial_code_given_in_program = TRUE;
    }
}

/* This option is handled a bit differently, so we have an accessor
   for it. */
extern int32 get_grammar_version_option(void)
{
    return SELECTVAL(OPT_GRAMMAR_VERSION);
}
