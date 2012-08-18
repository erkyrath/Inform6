/* ------------------------------------------------------------------------- */
/*   "veneer" : Compiling the run-time "veneer" of any routines invoked      */
/*              by the compiler (e.g. DefArt) which the program doesn't      */
/*              provide                                                      */
/*                                                                           */
/*   Part of Inform 6.40                                                     */
/*   copyright (c) Graham Nelson 1993 - 2006                                 */
/*   Reformated Feb06 by Roger Firth                                         */
/*                                                                           */
/* ------------------------------------------------------------------------- */

#include "header.h"

int veneer_mode;                      /*  Is the code currently being
                                          compiled from the veneer?          */

extern void compile_initial_routine(void) {

    /*  The first routine present in memory in any Inform game, beginning
        at the code area start position, always has 0 local variables
        (since the interpreter begins execution with an empty stack frame):
        and it must "quit" rather than "return".

        In order not to impose these restrictions on "Main", we compile a
        trivial routine consisting of a call to "Main" followed by "quit".   */

    int32 j;
    assembly_operand AO; dbgl null_dbgl;
    null_dbgl.b1 = 0; null_dbgl.b2 = 0; null_dbgl.b3 = 0; null_dbgl.cc = 0;

    j = symbol_index("Main__", -1);
    assign_symbol(j,
        assemble_routine_header(0, FALSE, "Main__", &null_dbgl, FALSE, j),
        ROUTINE_T);
    sflags[j] |= SYSTEM_SFLAG + USED_SFLAG;
    if (trace_fns_setting==3) sflags[j] |= STAR_SFLAG;

    if (!glulx_mode) {

        AO.value = 0; AO.type = LONG_CONSTANT_OT; AO.marker = MAIN_MV;

        sequence_point_follows = FALSE;

        assemblez_call_1(AO);
        assemblez_0(quit_zc);

    }
    else {

        AO.value = 0; AO.type = CONSTANT_OT; AO.marker = MAIN_MV;

        sequence_point_follows = FALSE;

        assembleg_3(call_gc, AO, zero_operand, zero_operand);
        assembleg_1(return_gc, zero_operand);

    }

    assemble_routine_end(FALSE, &null_dbgl);
}

/* ------------------------------------------------------------------------- */
/*   The rest of the veneer is applied at the end of the pass, as required.  */
/* ------------------------------------------------------------------------- */

static int veneer_routine_needs_compilation[VENEER_ROUTINES];
int32 veneer_routine_address[VENEER_ROUTINES];
static int veneer_symbols_base;

#define VR_UNUSED      0
#define VR_CALLED      1
#define VR_COMPILED    2

typedef struct VeneerRoutine_s {
    char *name;
    char *source;
} VeneerRoutine;

static char *veneer_source_area;

static VeneerRoutine VRs_z[VENEER_ROUTINES] = { /* veneer routines for Z-code */

/*  Box__Routine:
    The only veneer routine used in the implementation of an actual statement
    ("box", of course), written in a hybrid of Inform and assembly language.
    Note the transcription of the box text to the transcript output stream
    (-1, or $FFFF). */

  {"Box__Routine",
   "maxw table   n w w2 line lc t;\
    n = table-->0;\
    @add n 6 -> sp;\
    @split_window sp;\
    @set_window 1;\
    w = $0021->0;\
    if (w == 0) w = 80;\
    w2 = (w - maxw) / 2;\
    style reverse;\
    @sub w2 2 -> w;\
    line = 5;\
    lc = 1;\
    @set_cursor 4 w;\
    spaces maxw + 4;\
    do {\
        @set_cursor line w;\
        spaces maxw + 4;\
        @set_cursor line w2;\
        t = table-->lc;\
        if (t) print (string) t;\
        line++; lc++;\
    } until (lc > n);\
    @set_cursor line w;\
    spaces maxw + 4;\
    @buffer_mode 1;\
    style roman;\
    @set_window 0;\
    @split_window 1;\
    @output_stream -1;\
    print \"[ \";\
    lc = 1;\
    do {\
        w = table-->lc;\
        if (w) print (string) w;\
        lc++;\
        if (lc > n) { print \"]^^\"; break; }\
        print \"^  \";\
    } until (false);\
    @output_stream 1;\
  ]"},

/*  This batch of routines is expected to be defined (rather better) by the
    Inform library: these minimal forms here are provided to prevent tiny
    non-library-using programs from failing to compile when certain legal
    syntaxes (such as <<Action a b>>;) are used. */

  {"R_Process",
   "a b c d;\
    print \"Action <\", a, \" \", b, \" \", c, \" \", d, \">^\";\
  ]"},

  {"DefArt",
   "obj;\
    print \"the \", obj;\
  ]"},

  {"InDefArt",
   "obj;\
    print \"a \", obj;\
  ]"},

  {"CDefArt",
   "obj;\
    print \"The \", obj;\
  ]"},

  {"CInDefArt",
   "obj;\
    print \"A \", obj;\
  ]"},

  {"PrintShortName",
   "obj;\
    switch (metaclass(obj)) {\
      0:            print \"nothing\";\
      Object,Class: @print_obj obj;\
      Routine:      print \"(routine at \", obj, \")\";\
      String:       print \"(string at \", obj, \")\";\
    }\
  ]"},

  {"EnglishNumber",
   "obj;\
    print obj;\
  ]"},

  {"Print__PName",
   "id   p size cla i;\
    cla = #classes_table-->(id & $00FF);\
    if ((id & $C000) && cla <= (#largest_object-255) && cla > 0 && cla in Class) {\
        print (name) cla, \"::\";\
        if ((id & $8000) == 0) id = (id & $3F00) / $100;\
        else {\
            id = (id & $7F00) / $100;\
            i = cla.3;\
            while (i-->0 && id > 0) {\
                i = i + i->2 + 3;\
                id--;\
            }\
            id = (i-->0) & $7FFF;\
        }\
    }\
    p = #identifiers_table;\
    size = p-->0;\
    if (id <= 0 || id >= size || p-->id == 0) print \"<number \", id, \">\";\
    else print (string) p-->id;\
  ]"},

/*  The remaining routines make up the run-time half of the object orientation
    system, and need never be present for Inform 5 programs. */

/*  WV__Pr:
    Write a value to the property for the given object having the given
    identifier. */

  {"WV__Pr",
   "obj id value   x;\
    x = obj..&id;\
    if (x == 0) return RT__Err(\"write to\", obj, id);\
    #Ifdef INFIX;\
    if (obj has infix__watching || (debug_flag & 15)) RT__TrPS(obj, id, value);\
    #Ifnot; #Ifdef DEBUG;\
    if (debug_flag & 15) RT__TrPS(obj, id, value);\
    #Endif; #Endif;\
    x-->0 = value;\
  ]"},

/*  RV__Pr:
    Read a value from the property for the given object having the given
    identifier. */

  {"RV__Pr",
   "obj id   x;\
    x = obj..&id;\
    if (x == 0) {\
        if (id > 0 && id < 64 && obj.#id <= WORDSIZE) return obj.id;\
        return RT__Err(\"read\", obj, id);\
    }\
    return x-->0;\
  ]"},

/*  CA__Pr:
    Call, that is, print-or-run-or-read, a property: this exactly implements
    obj..prop(...). Note that classes (members of Class) have 5 built-in
    properties inherited from Class: create, recreate, destroy, remaining
    and copy. Implementing these here prevents the need for a full metaclass
    inheritance scheme. */

  {"CA__Pr",
   "obj id   a b c d e f x y z s s2 n m;\
    if (obj < 1 || obj > (#largest_object-255)) {\
        switch (Z__Region(obj)) {\
          2:\
            if (id == call) return obj(a, b, c, d, e, f);\
            jump Call__Error;\
          3:\
            if (id == print) print_ret (string) obj;\
            if (id == print_to_array) {\
                @output_stream 3 a; @print_paddr obj; @output_stream -3;\
                return a-->0;\
             }\
             jump Call__Error;\
        }\
        jump Call__Error;\
    }\
    #Iftrue (#version_number == 4);\
    y = 6;\
    #Ifnot;\
    @check_arg_count 3 ?~A__x; y++;\
    @check_arg_count 4 ?~A__x; y++;\
    @check_arg_count 5 ?~A__x; y++;\
    @check_arg_count 6 ?~A__x; y++;\
    @check_arg_count 7 ?~A__x; y++;\
    @check_arg_count 8 ?~A__x; y++;\
  .A__x;\
    #Endif;\
    #Ifdef INFIX;\
    if (obj has infix__watching) n = 1;\
    #Endif;\
    #Ifdef DEBUG;\
    if (debug_flag & 1) n = 1;\
    #Endif;\
    if (n == 1) {\
        #Ifdef DEBUG;\
        n = debug_flag & 1;\
        debug_flag = debug_flag - n;\
        #Endif;\
        if (VerboseDebugMessages(obj, id)) {\
            print \"[ ~\", (name) obj, \"~.\", (property) id, \"(\";\
            switch (y) {\
              1: print a;\
              2: print a, \",\", b;\
              3: print a, \",\", b, \",\", c;\
              4: print a, \",\", b, \",\", c, \",\", d;\
              5: print a, \",\", b, \",\", c, \",\", d, \",\", e;\
              6: print a, \",\", b, \",\", c, \",\", d, \",\", e, \",\", f;\
            }\
            print \") ]^\";\
        }\
        #Ifdef DEBUG;\
        debug_flag = debug_flag + n;\
        #Endif;\
    }\
    if (id > 0 && id < 64) {\
        x = obj.&id;\
        if (x == 0) { x = $000A-->0 + 2*(id-1); n = 2; }\
        else n = obj.#id;\
    }\
    else {\
        if (id >= 64 && id < 69 && obj in Class) return Cl__Ms(obj, id, y, a, b, c, d);\
        x = obj..&id;\
        if (x == 0) {\
          .Call__Error;\
            return RT__Err(\"send message\", obj, id);\
        }\
        n = 0->(x-1);\
        if ((id&$C000) == $4000) {\
            switch (n&$00C0) {\
                0:   n = 1;\
                $40: n = 2;\
                $80: n = n & $003F;\
            }\
        }\
    }\
    for ( : 2*m<n : m++) {\
        if (x-->m == $FFFF) rfalse;\
        switch (Z__Region(x-->m)) {\
          2:\
            s = sender; sender = self; self = obj; s2 = sw__var;\
            #Ifdef LibSerial;\
            if (id == life) sw__var = reason_code;\
            else            sw__var = action;\
            #Endif;\
            switch (y) {\
              0: z = (x-->m)();\
              1: z = (x-->m)(a);\
              2: z = (x-->m)(a, b);\
              3: z = (x-->m)(a, b, c);\
              4: z = (x-->m)(a, b, c, d);\
              5: z = (x-->m)(a, b, c, d, e);\
              6: z = (x-->m)(a, b, c, d, e, f);\
            }\
            self = sender; sender = s; sw__var = s2;\
            if (z) return z;\
          3:\
            print_ret (string) x-->m;\
          default:\
            return x-->m;\
        }\
    }\
    rfalse;\
  ]"},

/*  IB__Pr:
    ++(individual property). */

  {"IB__Pr",
   "obj id   x;\
    x = obj..&id;\
    if (x == 0) return RT__Err(\"increment\", obj, id);\
    #Ifdef INFIX;\
    if (obj has infix__watching || (debug_flag & 15)) RT__TrPS(obj, id, (x-->0)+1);\
    #Ifnot; #Ifdef DEBUG;\
    if (debug_flag & 15) RT__TrPS(obj, id, (x-->0)+1);\
    #Endif; #Endif;\
    return ++(x-->0);\
  ]"},

/*  IA__Pr:
    (individual property)++. */

  {"IA__Pr",
   "obj id   x;\
    x = obj..&id;\
    if (x == 0) return RT__Err(\"increment\", obj, id);\
    #Ifdef INFIX;\
    if (obj has infix__watching || (debug_flag & 15)) RT__TrPS(obj, id, (x-->0)+1);\
    #Ifnot; #Ifdef DEBUG;\
    if (debug_flag & 15) RT__TrPS(obj, id, (x-->0)+1);\
    #Endif; #Endif;\
    return (x-->0)++;\
  ]"},

/*  DB__Pr:
    --(individual property). */

  {"DB__Pr",
   "obj id   x;\
    x = obj..&id;\
    if (x == 0) return RT__Err(\"decrement\", obj, id);\
    #Ifdef INFIX;\
    if (obj has infix__watching || (debug_flag & 15)) RT__TrPS(obj, id, (x-->0)-1);\
    #Ifnot; #Ifdef DEBUG;\
    if (debug_flag & 15) RT__TrPS(obj, id, (x-->0)-1);\
    #Endif; #Endif;\
    return --(x-->0);\
  ]"},

/*  DA__Pr:
    (individual property)--. */

  {"DA__Pr",
   "obj id   x;\
    x = obj..&id;\
    if (x == 0) return RT__Err(\"decrement\", obj, id);\
    #Ifdef INFIX;\
    if (obj has infix__watching || (debug_flag & 15)) RT__TrPS(obj, id, (x-->0)-1);\
    #Ifnot; #Ifdef DEBUG;\
    if (debug_flag & 15) RT__TrPS(obj, id, (x-->0)-1);\
    #Endif; #Endif;\
    return (x-->0)--;\
  ]"},

/*  RA__Pr:
    Read the address of a property value for a given object, returning 0 if it
    doesn't provide this individual property. */

  {"RA__Pr",
   "obj id   i otherid cla;\
    if (obj == 0) rfalse;\
    if (id > 0 && id < 64) return obj.&id;\
    if (id & $8000) {\
        cla = #classes_table-->(id & $00FF);\
        if (cla > (#largest_object-255) || cla < 1 || cla notin Class) rfalse;\
        if (cla.&3 == 0) rfalse;\
        if (~~obj ofclass cla) rfalse;\
        id = (id & $7F00) / $100;\
        i = cla.3;\
        while (id > 0) {\
            id--;\
            i = i + i->2 + 3;\
        }\
        return i+3;\
    }\
    if (id & $4000) {\
        cla = #classes_table-->(id & $00FF);\
        if (cla > (#largest_object-255) || cla < 1 || cla notin Class) rfalse;\
        id = (id & $3F00) / $100;\
        if (~~obj ofclass cla) rfalse;\
        i = $000A-->0;\
        if (cla == 2) return i + 2*id - 2;\
        i = 0-->((i+124+cla*14) / 2);\
        i = CP__Tab(i + 2*(0->i) + 1, -1) + 6;\
        return CP__Tab(i, id);\
    }\
    if (obj.&3 == 0) rfalse;\
    if (obj in 1) {\
        if (id < 64 || id >= 72) rfalse;\
    }\
    if (self == obj) otherid = id | $8000;\
    i = obj.3;\
    while (i-->0) {\
        if (i-->0 == id or otherid) return i+3;\
        i = i + i->2 + 3;\
    }\
    rfalse;\
  ]"},

/*  RL__Pr:
    Read the property length of an individual property value, returning 0 if it
    isn't provided by the given object. */

  {"RL__Pr",
   "obj id   x;\
    if (id > 0 && id < 64) return obj.#id;\
    x = obj..&id;\
    if (x == 0) rfalse;\
    if ((id & $C000) == $4000) {\
        switch (((x-1)->0) & $C0) {\
          0:   return 1;\
          $40: return 2;\
          $80: return ((x-1)->0) & $3F;\
        }\
    }\
    return (x-1)->0;\
  ]"},

/*  RA__Sc:
    Implement the "superclass" (::) operator, returning an id. */

  {"RA__Sc",
   "cla id   otherid i j k;\
    if (cla notin 1 && cla > 4) {\
        RT__Err(\"be a '::' superclass\", cla, -1);\
        rfalse;\
    }\
    if (self ofclass cla) otherid = id | $8000;\
    for (j=0 : #classes_table-->j : j++) {\
        if (cla == #classes_table-->j) {\
            if (id < 64) return $4000 + id*$100 + j;\
            if (cla.&3 == 0) break;\
            i = cla.3;\
            while (i-->0) {\
                if (i-->0 == id or otherid) return $8000 + k*$100 + j;\
                i = i + i->2 + 3;\
                k++;\
            }\
            break;\
        }\
    }\
    RT__Err(\"make use of\", cla, id);\
    rfalse;\
  ]"},

/*  OP__Pr:
    Test whether or not given object provides individual property with the
    given identifier code. */

  {"OP__Pr",
   "obj id;\
    if (obj < 1 || obj > (#largest_object-255)) {\
        if (id ~= print or print_to_array or call) rfalse;\
        switch (Z__Region(obj)) {\
          2: if (id == call) rtrue;\
          3: if (id == print or print_to_array) rtrue;\
        }\
        rfalse;\
    }\
    if (id < 64) {\
        if (obj.&id) rtrue;\
        rfalse;\
    }\
    if (obj..&id) rtrue;\
    if (id < 72 && obj in 1) rtrue;\
    rfalse;\
  ]"},

/*  OC__Cl:
    Test whether or not given object is of the given class. */

  {"OC__Cl",
   "obj cla   j a n;\
    if (obj < 1 || obj > (#largest_object-255)) {\
        if (cla ~= 3 or 4) rfalse;\
        if (Z__Region(obj) == cla-1) rtrue;\
        rfalse;\
    }\
    if (cla == 1) {\
        if (obj in 1 || obj < 5) rtrue;\
        rfalse;\
    }\
    else {\
        if (cla == 2) {\
            if (obj in 1 || obj < 5) rfalse;\
            rtrue;\
        }\
        else {\
            if (cla == 3 or 4) rfalse;\
        }\
    }\
    if (cla notin 1) { RT__Err(\"apply 'ofclass' for\", cla, -1); rfalse; }\
    @get_prop_addr obj 2 -> a;\
    if (a == 0) rfalse;\
    @get_prop_len a -> n;\
    for (j=0 : j<n/WORDSIZE : j++) {\
        if (a-->j == cla) rtrue;\
    }\
    rfalse;\
  ]"},

/*  Copy__Primitive:
    Routine to "deep copy" objects. */

  {"Copy__Primitive",
   "obj1 obj2   a1 a2 n m l size id;\
    for (n=0 : n<48 : n++) {\
        if (obj2 has n) give obj1 n;\
        else            give obj1 ~n;\
    }\
    for (n=1 : n<64 : n++) {\
        if (n ~= 2 or 3) {\
            a1 = obj1.&n; a2 = obj2.&n; size = obj1.#n;\
            if (a1 && a2 && size == obj2.#n) {\
                for (m=0 : m<size : m++) a1->m = a2->m;\
            }\
        }\
    }\
    if (obj1.&3 == 0 || obj2.&3 == 0) return;\
    for (n=obj2.3 : n-->0 : n=n+size+3) {\
        id = n-->0;\
        size = n->2;\
        for (m=obj1.3 : m-->0 : m=m+(m->2)+3) {\
            if ((id & $7FFF == (m-->0) & $7FFF) && size == m->2)\
                for (l=3 : l<size+3 : l++) m->l = n->l;\
        }\
    }\
  ]"},

/*  RT__Err:
    For run-time errors occurring in the above: e.g., an attempt to write to
    a non-existent individual property. */

  {"RT__Err",
    /* for array access errors (crime == 28 to 31) under version 3
       obj       => index into the array,
       id        => size of the array,
       temp_var3 => type of the array,
       temp_var4 => name of the array */
   "crime obj id   size p q;\
    #Iftrue (#version_number == 3);\
    size = temp_var3;\
    p = temp_var4;\
    #Endif;\
    print \"^[** Programming error: \";\
    if (crime < 0) jump RErr;\
    if (crime == 1) {\
        print \"class \";\
        @print_obj obj;\
        \": 'create' can have 0 to 3 parameters only **]\";\
    }\
    if (crime == 36)\
        \"tried to print (object) on something not an \", \"object or class **]\";\
    if (crime == 35)\
        \"tried to print (string) on something not a \", \"string **]\";\
    if (crime == 34)\
        \"tried to print (address) on something not the \", \"byte address of a string **]\";\
    if (crime == 33)\
        \"tried to print (char) \", obj, \", which is not a valid ZSCII character code for output **]\";\
    if (crime == 32)\
        \"objectloop broken because the object \", (name) obj, \" was moved while the loop passed through it **]\";\
    if (crime < 32) {\
        print \"tried to \";\
        if (crime >= 28) {\
            if (crime == 28 or 29) print \"read from \";\
            else                   print \"write to \";\
            if (crime == 29 or 31) print \"-\";\
            print \"->\", obj, \" in the\";\
            switch (size&7) {\
              0,1:                    q = 0;\
              2:   print \" string\"; q = 1;\
              3:   print \" table\";  q = 1;\
              4:   print \" buffer\"; q = WORDSIZE;\
            }\
            if (size&16) print\" (->)\";\
            if (size&8)  print\" (-->)\";\
            if (size&128) {\
                if ((p->-1)&$7F > $40) p = (p->-1)&$3F;\
                else                   p = p->-2-(p->-1&$80);\
                print \" property ~\", (property) p;\
                id--;\
            }\
            else\
                print \" array ~\", (string) #array_names_offset-->p;\
            \"~, which has entries \", q, \" up to \",id,\" **]\";\
        }\
        if (crime >= 24 && crime <= 27) {\
            if (crime <= 25) print \"read\";\
            else             print \"write\";\
            print \" outside memory using \";\
            switch (crime) {\
              24,26: \"-> **]\";\
              25,27: \"--> **]\";\
            }\
        }\
        if (crime < 4) print \"test \";\
        else\
            if (crime < 12 || crime > 20) print \"find the \";\
            else\
                if (crime < 14) print \"use \";\
        if (crime == 20) \"divide by zero **]\";\
        print \"~\";\
        switch (crime) {\
           2: print \"in~ or ~notin\";\
           3: print \"has~ or ~hasnt\";\
           4: print \"parent\";\
           5: print \"eldest\";\
           6: print \"child\";\
           7: print \"younger\";\
           8: print \"sibling\";\
           9: print \"children\";\
          10: print \"youngest\";\
          11: print \"elder\";\
          12: print \"objectloop\";\
          13: print \"}~ at end of ~objectloop\";\
          14: \"give~ an attribute to \", (name) obj, \" **]\";\
          15: \"remove~ \", (name) obj, \" **]\";\
          16,17,18:\
            print \"move~ \", (name) obj, \" to \", (name) id;\
            if (crime == 18) {\
                print \", which would make a loop: \",(name) obj;\
                p = id;\
                if (p == obj) p = obj;\
                else\
                    do {\
                        print \" in \", (name) p;\
                        p = parent(p);\
                    } until (p == obj);\
                \" in \", (name) p, \" **]\";\
            }\
            \" **]\";\
          19: \"give~ or test ~has~ or ~hasnt~ with a non-attribute on the object \", (name) obj, \" **]\";\
          21: print \".&\";\
          22: print \".#\";\
          23: print \".\";\
        }\
        \"~ of \", (name) obj, \" **]\";\
    }\
  .RErr;\
    if (obj >= 0 && obj <= (#largest_object-255)) {\
        if (obj && obj in Class) print \"class \";\
        if (obj) @print_obj obj;\
        else     print \"nothing\";\
        print\" \";\
    }\
    print \"(object number \", obj, \") \";\
    if (id < 0) print \"is not of class \", (name) -id;\
    else\
        if (size) print \"has a property \", (property) id, \", but it is longer than 2 bytes so you cannot use ~.~\";\
        else {\
            print \" has no property \", (property) id;\
            p = #identifiers_table;\
            size = p-->0;\
            if (id < 0 || id >= size) print \" (and nor has any other object)\";\
        }\
    print \" to \", (string) crime, \" **]^\";\
  ]"},

/*  Z__Region:
    Determine whether a value is:
        1  an object number
        2  a code address
        3  a string address
        0  none of the above. */

  {"Z__Region",
   "addr   top;\
    if (addr == 0 or -1) rfalse;\
    top = addr;\
    #Iftrue (#version_number == 6) || (#version_number == 7);\
    @log_shift addr $FFFF -> top;\
    #Endif;\
    if (Unsigned__Compare(top, $001A-->0) >= 0) rfalse;\
    if (addr >= 1 && addr <= (#largest_object-255)) rtrue;\
    #Iftrue #oddeven_packing;\
    @test addr 1 ?~NotString;\
    if (Unsigned__Compare(addr, #strings_offset) < 0) rfalse;\
    return 3;\
  .NotString;\
    if (Unsigned__Compare(addr, #code_offset) < 0) rfalse;\
    return 2;\
    #Ifnot;\
    if (Unsigned__Compare(addr, #strings_offset) >= 0) return 3;\
    if (Unsigned__Compare(addr, #code_offset) >= 0) return 2;\
    rfalse;\
    #Endif;\
  ]"},

/*  Unsigned__Compare:
    Returns 1 if x>y, 0 if x=y, -1 if x<y. */

  {"Unsigned__Compare",
   "x y   u v;\
    if (x == y) return 0;\
    if (x < 0 && y >= 0) return 1;\
    if (x >= 0 && y < 0) return -1;\
    u = x & $7FFF; v = y & $7FFF;\
    if (u > v) return 1;\
    return -1;\
  ]"},

/*  Meta__class:
    Returns the metaclass of an object. */

  {"Meta__class",
   "obj;\
    switch (Z__Region(obj)) {\
      2: return Routine;\
      3: return String;\
      1: if (obj in 1 || obj < 5) return Class;\
         return Object;\
    }\
    rfalse;\
  ]"},

/*  CP__Tab:
    Searches a common property table for the given identifier, thus imitating
    the get_prop_addr opcode. Returns 0 if not provided, except: if the
    identifier supplied is -1, then returns the address of the first byte
    after the table. */

  {"CP__Tab",
   "x id   n l;\
    while ((n = 0->x) ~= 0) {\
        if (n & $80) { x++; l = (0->x) & $3F; }\
        else {\
            if (n & $40) l = 2; else l = 1;\
        }\
        x++;\
        if ((n & $3F) == id) return x;\
        x = x + l;\
    }\
    if (id < 0) return x+1;\
    rfalse;\
  ]"},

/*  Cl__Ms:
    The five message-receiving properties of Classes. */

  {"Cl__Ms",
   "obj id y   a b c d x;\
    switch (id) {\
      create:\
        if (children(obj) <= 1) rfalse;\
        x = child(obj);\
        remove x;\
        if (x provides create) {\
            if (y == 0) x..create();\
            if (y == 1) x..create(a);\
            if (y == 2) x..create(a, b);\
            if (y > 3)  RT__Err(1, obj);\
            if (y >= 3) x..create(a, b, c);\
        }\
        return x;\
      recreate:\
        if (~~a ofclass obj) {\
            RT__Err(\"recreate\", a, -obj);\
            rfalse;\
        }\
        Copy__Primitive(a, child(obj));\
        if (a provides create) {\
            if (y == 1) a..create();\
            if (y == 2) a..create(b);\
            if (y == 3) a..create(b, c);\
            if (y > 4)  RT__Err(1, obj);\
            if (y >= 4) a..create(b, c, d);\
        }\
        rfalse;\
      destroy:\
        if (~~a ofclass obj) {\
            RT__Err(\"destroy\", a, -obj);\
            rfalse;\
        }\
        if (a provides destroy) a..destroy();\
        Copy__Primitive(a, child(obj));\
        move a to obj;\
        rfalse;\
      remaining:\
        return children(obj)-1;\
      copy:\
        if (~~a ofclass obj) {\
            RT__Err(\"copy\", a, -obj);\
            rfalse;\
        }\
        if (~~b ofclass obj) {\
            RT__Err(\"copy\", b, -obj);\
            rfalse;\
        }\
        Copy__Primitive(a, b);\
        rfalse;\
    }\
  ]"},

/*  RT__ChT:
    Run-time check that a proposed object "move" is legal. Cause error and
    do nothing if not; otherwise move. */

  {"RT__ChT",
   "obj1 obj2   x;\
    if (obj1 < 5 || obj1 > (#largest_object-255) || obj1 in 1) return RT__Err(16, obj1, obj2);\
    if (obj2 < 5 || obj2 > (#largest_object-255) || obj2 in 1) return RT__Err(17, obj1, obj2);\
    x = obj2;\
    while (x) {\
        if (x == obj1) return RT__Err(18, obj1, obj2);\
        x = parent(x);\
    }\
    #Ifdef INFIX;\
    if (obj1 has infix__watching || obj2 has infix__watching || (debug_flag & 15))\
        print \"[ Moving ~\", (name) obj1, \"~ to ~\", (name) obj2, \"~ ]^\";\
    #Ifnot; #Ifdef DEBUG;\
    if (debug_flag & 15) print \"[ Moving ~\", (name) obj1, \"~ to ~\", (name) obj2, \"~ ]^\";\
    #Endif; #Endif;\
    @insert_obj obj1 obj2;\
  ]"},

/*  RT__ChR:
    Run-time check that a proposed object "remove" is legal. Cause error and
    do nothing if not; otherwise remove. */

  {"RT__ChR",
   "obj;\
    if (obj in 1 || obj < 5 || obj > (#largest_object-255)) return RT__Err(15, obj);\
    #Ifdef INFIX;\
    if (obj has infix__watching || (debug_flag & 15)) print \"[ Removing ~\", (name) obj, \"~ ]^\";\
    #Ifnot; #Ifdef DEBUG;\
    if (debug_flag & 15) print \"[ Removing ~\", (name) obj, \"~ ]^\";\
    #Endif; #Endif;\
    @remove_obj obj;\
  ]"},

/*  RT__ChG:
    Run-time check that a proposed attr "give" is legal. Cause error and
    do nothing if not; otherwise give. */

  {"RT__ChG",
   "obj a;\
    if (obj in 1 || obj < 5 || obj > (#largest_object-255)) return RT__Err(14, obj);\
    if (a < 0 || a >= 48) return RT__Err(19, obj);\
    if (obj has a) return;\
    #Ifdef INFIX;\
    if (a ~= workflag && (obj has infix__watching || (debug_flag & 15)))\
        print \"[ Giving ~\", (name) obj, \"~ \", (DebugAttribute) a, \" ]^\";\
    #Ifnot; #Ifdef DEBUG;\
    if (a ~= workflag && debug_flag & 15)\
        print \"[ Giving ~\", (name) obj, \"~ \", (DebugAttribute) a, \" ]^\";\
    #Endif; #Endif;\
    @set_attr obj a;\
  ]"},

/*  RT__ChGt:
    Run-time check that a proposed attr "give ~" is legal. Cause error and
    do nothing if not; otherwise give. */

  {"RT__ChGt",
   "obj a;\
    if (obj in 1 || obj < 5 || obj > (#largest_object-255)) return RT__Err(14, obj);\
    if (a < 0 || a >= 48) return RT__Err(19, obj);\
    if (obj hasnt a) return;\
    #Ifdef INFIX;\
    if (a ~= workflag && (obj has infix__watching || (debug_flag & 15)))\
        print \"[ Giving ~\", (name) obj, \"~ @@126\", (DebugAttribute) a, \" ]^\";\
    #Ifnot; #Ifdef DEBUG;\
    if (a ~= workflag && debug_flag & 15)\
        print \"[ Giving ~\", (name) obj, \"~ @@126\", (DebugAttribute) a, \" ]^\";\
    #Endif; #Endif;\
    @clear_attr obj a;\
  ]"},

/*  RT__ChPS:
    Run-time check that a proposed property "set" is legal. Cause error and
    do nothing if not; otherwise make it. */

  {"RT__ChPS",
   "obj prop val   size;\
    if (obj in 1 || obj < 5 || obj > (#largest_object-255) || obj.&prop == 0 || (size=obj.#prop) > 2 )\
        return RT__Err(\"set\", obj, prop, size);\
    @put_prop obj prop val;\
    #Ifdef INFIX;\
    if (obj has infix__watching || (debug_flag & 15)) RT__TrPS(obj, prop, val);\
    #Ifnot; #Ifdef DEBUG;\
    if (debug_flag & 15) RT__TrPS(obj, prop, val);\
    #Endif; #Endif;\
    return val;\
  ]"},

/*  RT__ChPR:
    Run-time check that a proposed property "read" is legal. Cause error and
    return 0 if not; otherwise read it. */

  {"RT__ChPR",
   "obj prop val   size;\
    if (obj < 5 || obj > (#largest_object-255) || (size=obj.#prop) > 2) {\
        RT__Err(\"read\", obj, prop, size);\
        obj = 2;\
    }\
    @get_prop obj prop -> val;\
    return val;\
  ]"},

/*  RT__TrPS:
    Trace property settings. */

  {"RT__TrPS",
   "obj prop val;\
    if (VerboseDebugMessages(obj, prop)) {\
        print \"[ Setting ~\", (name) obj, \"~.\", (property) prop, \" to \", val, \" ]^\";\
    }\
  ]"},

/*  RT__ChLDB:
    Run-time check that it's safe to load a byte, and return the byte. */

  {"RT__ChLDB",
   "base offset   a val;\
    a = base + offset;\
    if (Unsigned__Compare(a, #readable_memory_offset) >= 0) return RT__Err(24);\
    @loadb base offset -> val;\
    return val;\
  ]"},

/*  RT__ChLDW:
    Run-time check that it's safe to load a word, and return the word. */

  {"RT__ChLDW",
   "base offset   a val;\
    a = base + WORDSIZE*offset;\
    if (Unsigned__Compare(a, #readable_memory_offset) >= 0) return RT__Err(25);\
    @loadw base offset -> val;\
    return val;\
  ]"},

/*  RT__ChSTB:
    Run-time check that it's safe to store a byte, and store it. */

  {"RT__ChSTB",
   "base offset val   a flag;\
    a = base + offset;\
    if (Unsigned__Compare(a, #array__start) >= 0 && Unsigned__Compare(a,#array__end) < 0) flag = true;\
    else\
        if (Unsigned__Compare(a, #cpv__start)>= 0 && Unsigned__Compare(a, #cpv__end) < 0) flag = true;\
        else\
            if (Unsigned__Compare(a, #ipv__start) >= 0 && Unsigned__Compare(a, #ipv__end) < 0) flag = true;\
            else\
                if (a == $0011) flag = true;\
    if (flag == false) return RT__Err(26);\
    @storeb base offset val;\
  ]"},

/*  RT__ChSTW:
    Run-time check that it's safe to store a word, and store it. */

  {"RT__ChSTW",
   "base offset val   a flag;\
    a = base + WORDSIZE*offset;\
    if (Unsigned__Compare(a, #array__start) >= 0 && Unsigned__Compare(a, #array__end) < 0) flag = true;\
    else\
        if (Unsigned__Compare(a, #cpv__start) >= 0 && Unsigned__Compare(a, #cpv__end) < 0) flag = true;\
        else\
            if (Unsigned__Compare(a, #ipv__start) >= 0 && Unsigned__Compare(a, #ipv__end) < 0) flag = true;\
            else\
                if (a == $0010) flag = true;\
    if (flag == false) return RT__Err(27);\
    @storew base offset val;\
  ]"},

/*  RT__ChLDPrB:
    Run-time check that it's safe to load a byte property and return the
    byte. */

  {"RT__ChLDPrB",
   "base offset   a val;\
    if (~~base) return RT__Err(24);\
    if ((base->-1)&$7F > $40) a = 2;\
    else { a = (base->-1) & 63; if (a == 0) a = 64; }\
    if (offset >= 0 && offset < a) {\
        @loadb base offset -> val;\
        return val;\
    }\
    RT__Err(28, offset, a, 128, base);\
  ]"},

/*  RT__ChLDPrW:
    Run-time check that it's safe to load a word property and return the
    word. */

  {"RT__ChLDPrW",
   "base offset   a val;\
    if (~~base) return RT__Err(25);\
    if ((base->-1)&$7F > $40) a = 2;\
    else { a = (base->-1) & 63; if (a == 0) a = 64; }\
    if (offset >= 0 && offset < a/WORDSIZE) {\
        @loadw base offset -> val;\
        return val;\
    }\
    RT__Err(29, offset, a/WORDSIZE, 128, base);\
  ]"},

/*  RT__ChSTPrB:
    Run-time check that it's safe to store a byte property and store it. */

  {"RT__ChSTPrB",
   "base offset val   a;\
    if (~~base) return RT__Err(26);\
    if ((base->-1)&$7F > $40) a = 2;\
    else { a = (base->-1) & 63; if (a == 0) a = 64; }\
    if (offset >= 0 && offset < a) {\
        @storeb base offset val;\
        return;\
    }\
    RT__Err(30, offset, a, 128, base);\
  ]"},

/*  RT__ChSTPrW:
    Run-time check that it's safe to store a word property and store it. */

  {"RT__ChSTPrW",
   "base offset val   a;\
    if (~~base) return RT__Err(27);\
    if ((base->-1)&$7F > $40) a = 2;\
    else { a = (base->-1) & 63; if (a == 0) a = 64; }\
    if (offset >= 0 && offset < a/WORDSIZE) {\
        @storew base offset val;\
        return;\
    }\
    RT__Err(31, offset, a/WORDSIZE, 128, base);\
  ]"},

/*  RT__ChPrintC:
    Run-time check that it's safe to print (char) and do so. */

  {"RT__ChPrintC",
   "c;\
    if (~~(c == 0 or 9 or 11 or 13 || (c >= 32  && c <= 126) || (c >= 155 && c <= 251)))\
        return RT__Err(33, c);\
    @print_char c;\
  ]"},

/*  RT__ChPrintA:
    Run-time check that it's safe to print (address) and do so. */

  {"RT__ChPrintA",
   "a;\
    if (Unsigned__Compare(a, #readable_memory_offset) >= 0) return RT__Err(34);\
    @print_addr a;\
  ]"},

/*  RT__ChPrintS:
    Run-time check that it's safe to print (string) and do so. */

  {"RT__ChPrintS",
   "a;\
    if (Z__Region(a) ~= 3) return RT__Err(35);\
    @print_paddr a;\
  ]"},

/*  RT__ChPrintO:
    Run-time check that it's safe to print (object) and do so. */

  {"RT__ChPrintO",
   "a;\
    if (Z__Region(a) ~= 1) return RT__Err(36);\
    @print_obj a;\
  ]"},

/*  AssertFailed:
    Handle run-time assertion failure. */

  {"AssertFailed",
   "file lhi llo;\
    print \"^[** Assertion failed at line \";\
    if (lhi > 0) {\
        print lhi;\
        if (llo < 1000) print \"0\";\
        if (llo < 100)  print \"0\";\
        if (llo < 10)   print \"0\";\
    }\
    print llo, \" in file ~\", (string) file, \"~ **]^\";\
  ]"},

/*  VerboseDebugMessages:
    Optionally suppress debugging messages for Library objects. */

  {"VerboseDebugMessages",
   "obj prop;\
    #Ifdef DEBUG;\
    if (debug_flag & $0080) rtrue;\
    if (obj == LibraryExtensions or LibraryMessages or InformParser or InformLibrary) rfalse;\
    if (obj in LibraryExtensions or Compass) rfalse;\
    #Endif;\
    prop = obj;\
    rtrue;\
  ]"}

}; /* End of VRs_z -- veneer routines for Z-code */

static VeneerRoutine VRs_g[VENEER_ROUTINES] = { /* veneer routines for Glulx */

/*  Box__Routine:
    Display the given array of text as a box quote. This is a very simple
    implementation; the library should provide a fancier version. */

  {"Box__Routine",
   "maxwid arr   ix;\
    maxwid = 0;\
    glk($0086, 7);\
    for (ix=0 : ix<arr-->0 : ix++) {\
        print (string) arr-->(ix+1);\
        new_line;\
    }\
    glk($0086, 0);\
  ]"},

/*  This batch of routines is expected to be defined (rather better) by the
    Inform library: these minimal forms here are provided to prevent tiny
    non-library-using programs from failing to compile when certain legal
    syntaxes (such as <<Action a b>>;) are used. */

  {"R_Process",
   "a b c d;\
    print \"Action <\", a, \" \", b, \" \", c, \" \", d, \">^\";\
  ]"},

  {"DefArt",
   "obj;\
    print \"the \", obj;\
  ]"},

  {"InDefArt",
   "obj;\
    print \"a \", obj;\
  ]"},

  {"CDefArt",
   "obj;\
    print \"The \", obj;\
  ]"},

  {"CInDefArt",
   "obj;\
    print \"A \", obj;\
  ]"},

  {"PrintShortName",
   "obj   q;\
    switch (metaclass(obj)) {\
      0:            print \"nothing\";\
      Object,Class: q = obj-->3; @streamstr q;\
      Routine:      print \"(routine at \", obj, \")\";\
      String:       print \"(string at \", obj, \")\";\
    }\
  ]"},

  {"EnglishNumber",
   "obj;\
    print obj;\
  ]"},

/*  Print__PName:
    Print the name of a property. */

  {"Print__PName",
   "prop   ptab cla maxcom minind maxind str;\
    if (prop & $FFFF0000) {\
        cla = #classes_table-->(prop & $FFFF);\
        print (name) cla, \"::\";\
        @ushiftr prop 16 prop;\
    }\
    ptab = #identifiers_table;\
    maxcom = ptab-->1;\
    minind = INDIV_PROP_START;\
    maxind = minind + ptab-->3;\
    str = 0;\
    if (prop >= 0 && prop < maxcom) str = (ptab-->0)-->prop;\
    else\
        if (prop >= minind && prop < maxind) str = (ptab-->2)-->(prop-minind);\
     if (str) print (string) str;\
     else     print \"<number \", prop, \">\";\
  ]"},

/*  The remaining routines make up the run-time half of the object orientation
    system, and need never be present for Inform 5 programs. */

/*  WV__Pr:
    Write a value to the property for the given object. */

  {"WV__Pr",
   "obj id val   addr;\
    addr = obj.&id;\
    if (addr == 0) { RT__Err(\"write\", obj, id); rfalse; }\
    addr-->0 = val;\
    rfalse;\
  ]"},

/*  RV__Pr:
    Read a value to the property for the given object. */

  {"RV__Pr",
   "obj id   addr;\
    addr = obj.&id;\
    if (addr == 0) {\
        if (id > 0 && id < INDIV_PROP_START) return #cpv__start-->id;\
        RT__Err(\"read\", obj, id);\
        rfalse;\
    }\
    return addr-->0;\
  ]"},

/*  CA__Pr:
    Call, that is, print-or-run-or-read, a property: this exactly implements
    obj..prop(...). Note that classes (members of Class) have five built-in
    properties inherited from Class: create, recreate, destroy, remaining
    and copy. Implementing these here prevents the need for a full metaclass
    inheritance scheme. */

  {"CA__Pr",
   "_vararg_count obj id   zr z s s2 addr len m n val;\
    @copy sp obj;\
    @copy sp id;\
    _vararg_count = _vararg_count - 2;\
    zr = Z__Region(obj);\
    if (zr == 2) {\
        if (id == call) {\
            @call obj _vararg_count z;\
            return z;\
        }\
        jump Call__Error;\
     }\
     if (zr == 3) {\
        if (id == print) {\
            @streamstr obj;\
            @streamchar 10;\
            rtrue;\
        }\
        if (id == print_to_array) {\
            if (_vararg_count >= 2) {\
                @copy sp m;\
                @copy sp len;\
            }\
            else {\
                @copy sp m;\
                len = $7FFFFFFF;\
            }\
            s2 = glk($0048);\
            s = glk($0043, m+4, len-4, 1, 0);\
            if (s) {\
                glk($0047, s);\
                @streamstr obj;\
                glk($0047, s2);\
                @copy $FFFFFFFF sp;\
                @copy s sp;\
                @glk $0044 2 0;\
                @copy sp len;\
                @copy sp 0;\
                m-->0 = len;\
                return len;\
            }\
            rfalse;\
        }\
        jump Call__Error;\
    }\
    if (zr ~= 1) jump Call__Error;\
    #Ifdef INFIX;\
    if (obj has infix__watching) n = 1;\
    #Endif;\
    #Ifdef DEBUG; #Ifdef InformLibrary;\
    if (debug_flag & 1 ~= 0) n = 1;\
    #Endif; #Endif;\
    if (n == 1) {\
        #Ifdef DEBUG_FLAG;\
        n = debug_flag & 1;\
        debug_flag = debug_flag - n;\
        #Endif;\
        if (VerboseDebugMessages(obj, id)) {\
            print \"[ ~\", (name) obj, \"~.\", (property) id, \"(\";\
            @stkcopy _vararg_count;\
            for (val=0 : val<_vararg_count : val++) {\
                if (val) print \", \";\
                @streamnum sp;\
            }\
            print \") ]^\";\
        }\
        #Ifdef DEBUG_FLAG;\
        debug_flag = debug_flag + n;\
        #Endif;\
    }\
    if (obj in Class) {\
        switch (id) {\
          remaining:\
            return Cl__Ms(obj, id);\
          copy:\
            @copy sp m;\
            @copy sp val;\
            return Cl__Ms(obj, id, m, val);\
          create,destroy,recreate:\
            m = _vararg_count+2;\
            @copy id sp;\
            @copy obj sp;\
            @call Cl__Ms m val;\
            return val;\
        }\
    }\
    addr = obj.&id;\
    if (addr == 0) {\
        if (id > 0 && id < INDIV_PROP_START) {\
            addr = #cpv__start + 4*id;\
            len = 4;\
        }\
        else jump Call__Error;\
    }\
    else\
        len = obj.#id;\
    for (m=0 : 4*m<len : m++) {\
        val = addr-->m;\
        if (val == -1) rfalse;\
        switch (Z__Region(val)) {\
          2:\
            s = sender; sender = self; self = obj; s2 = sw__var;\
            #Ifdef LibSerial;\
            if (id == life) sw__var = reason_code;\
            else            sw__var = action;\
            #Endif;\
            @stkcopy _vararg_count;\
            @call val _vararg_count z;\
            self = sender; sender = s; sw__var = s2;\
            if (z) return z;\
          3:\
            @streamstr val;\
            new_line;\
            rtrue;\
          default:\
            return val;\
        }\
    }\
    rfalse;\
  .Call__Error;\
    RT__Err(\"send message\", obj, id);\
    rfalse;\
  ]"},

/*  IB__Pr:
    ++(individual property). */

  {"IB__Pr",
   "obj id   x;\
    x = obj.&id;\
    if (x == 0) return RT__Err(\"increment\", obj, id);\
    #Ifdef INFIX;\
    if (obj has infix__watching || (debug_flag & 15)) RT__TrPS(obj, id, (x-->0)+1);\
    #Ifnot; #Ifdef DEBUG;\
    if (debug_flag & 15) RT__TrPS(obj, id, (x-->0)+1);\
    #Endif; #Endif;\
    return ++(x-->0);\
  ]"},

/*  IA__Pr:
    (individual property)++. */

  {"IA__Pr",
   "obj id   x;\
    x = obj.&id;\
    if (x == 0) return RT__Err(\"increment\", obj, id);\
    #Ifdef INFIX;\
    if (obj has infix__watching || (debug_flag & 15)) RT__TrPS(obj, id, (x-->0)+1);\
    #Ifnot; #Ifdef DEBUG;\
    if (debug_flag & 15) RT__TrPS(obj, id, (x-->0)+1);\
    #Endif; #Endif;\
    return (x-->0)++;\
  ]"},

/*  DB__Pr:
    --(individual property). */

  {"DB__Pr",
   "obj id   x;\
    x = obj.&id;\
    if (x == 0) return RT__Err(\"decrement\", obj, id);\
    #Ifdef INFIX;\
    if (obj has infix__watching || (debug_flag & 15)) RT__TrPS(obj, id, (x-->0)-1);\
    #Ifnot; #Ifdef DEBUG;\
    if (debug_flag & 15) RT__TrPS(obj, id, (x-->0)-1);\
    #Endif; #Endif;\
    return --(x-->0);\
  ]"},

/*  DA__Pr:
    (individual property)--. */

  {"DA__Pr",
   "obj id   x;\
    x = obj.&id;\
    if (x == 0) return RT__Err(\"decrement\", obj, id);\
    #Ifdef INFIX;\
    if (obj has infix__watching || (debug_flag & 15)) RT__TrPS(obj, id, (x-->0)-1);\
    #Ifnot; #Ifdef DEBUG;\
    if (debug_flag & 15) RT__TrPS(obj, id, (x-->0)-1);\
    #Endif; #Endif;\
    return (x-->0)--;\
  ]"},

/*  RA__Pr:
    Read the property address of a given property value. Returns zero if it
    isn't provided by the object. This understands all the same concerns as
    RL__Pr(). */

  {"RA__Pr",
   "obj id   cla prop ix;\
    if (id & $FFFF0000) {\
        cla = #classes_table-->(id & $FFFF);\
        if (~~obj ofclass cla) return 0;\
        @ushiftr id 16 id;\
        obj = cla;\
    }\
    prop = CP__Tab(obj, id);\
    if (prop == 0) return 0;\
    if (obj in Class && cla == 0) {\
        if (id < INDIV_PROP_START || id >= INDIV_PROP_START+8) return 0;\
    }\
    if (self ~= obj) {\
        @aloadbit prop 72 ix;\
        if (ix) return 0;\
    }\
    return prop-->1;\
  ]"},

/*  RL__Pr:
    Read the property length of a given property value. Returns zero if it
    isn't provided by the object. This understands inherited values (of the
    form class::prop) as well as simple property ids and the special
    metaclass methods. It also knows that private properties can only be read
    if (self == obj). */

  {"RL__Pr",
   "obj id   cla prop ix;\
    if (id & $FFFF0000) {\
        cla = #classes_table-->(id & $FFFF);\
        if (~~obj ofclass cla) return 0;\
        @ushiftr id 16 id;\
        obj = cla;\
    }\
    prop = CP__Tab(obj, id);\
    if (prop == 0) return 0;\
    if (obj in Class && cla == 0) {\
        if (id < INDIV_PROP_START || id >= INDIV_PROP_START+8) return 0;\
    }\
    if (self ~= obj) {\
        @aloadbit prop 72 ix;\
        if (ix) return 0;\
    }\
    @aloads prop 1 ix;\
    return WORDSIZE * ix;\
  ]"},

/*  RA__Sc:
    Implement the "superclass" (::) operator. This returns a compound
    property identifier, which is a 32-bit value. */

  {"RA__Sc",
   "cla id   j;\
    if ((cla notin Class) && (cla ~= Class or String or Routine or Object)) {\
        RT__Err(\"be a '::' superclass\", cla, -1);\
        rfalse;\
    }\
    for (j=0 : #classes_table-->j : j++) {\
        if (cla == #classes_table-->j) return (id * $10000 + j);\
    }\
    RT__Err(\"make use of\", cla, id);\
    rfalse;\
  ]"},

/*  OP__Pr:
    Test whether the given object provides the given property. This winds up
    calling RA__Pr(). */

  {"OP__Pr",
   "obj id   zr;\
    zr = Z__Region(obj);\
    if (zr == 3) {\
        if (id == print or print_to_array) rtrue;\
        rfalse;\
    }\
    if (zr == 2) {\
        if (id == call) rtrue;\
        rfalse;\
    }\
    if (zr ~= 1) rfalse;\
    if (id >= INDIV_PROP_START && id < INDIV_PROP_START+8) {\
        if (obj in Class) rtrue;\
    }\
    if (obj.&id) rtrue;\
    rfalse;\
  ]"},

/*  OC__Cl:
    Test whether the given object is of the given class (implements the OfClass
    operator). */

  {"OC__Cl",
   "obj cla   zr jx inlist inlistlen;\
    zr = Z__Region(obj);\
    if (zr == 3) {\
        if (cla == String) rtrue;\
        rfalse;\
    }\
    if (zr == 2) {\
        if (cla == Routine) rtrue;\
        rfalse;\
    }\
    if (zr ~= 1) rfalse;\
    if (cla == Class) {\
        if (obj in Class || obj == Class or String or Routine or Object) rtrue;\
        rfalse;\
    }\
    if (cla == Object) {\
        if (obj in Class || obj == Class or String or Routine or Object) rfalse;\
        rtrue;\
    }\
    if (cla == String or Routine) rfalse;\
    if (cla notin Class) { RT__Err(\"apply 'ofclass' for\", cla, -1); rfalse; }\
    inlist = obj.&2;\
    if (inlist == 0) rfalse;\
    inlistlen = (obj.#2) / WORDSIZE;\
    for (jx=0 : jx<inlistlen : jx++) if (inlist-->jx == cla) rtrue;\
    rfalse;\
  ]"},

/*  Copy__Primitive:
    Routine to "deep copy" objects. */

  {"Copy__Primitive",
   "obj1 obj2   p1 p2 pcount i j propid proplen val pa1 pa2;\
    for (i=1 : i<=NUM_ATTR_BYTES : i++) obj1->i = obj2->i;\
    p2 = obj2-->4;\
    pcount = p2-->0;\
    p2 = p2 + 4;\
    for (i=0 : i<pcount : i++) {\
        @aloads p2 0 propid;\
        @aloads p2 1 proplen;\
        p1 = CP__Tab(obj1, propid);\
        if (p1) {\
            @aloads p1 1 val;\
            if (proplen == val) {\
                @aloads p2 4 val;\
                @astores p1 4 val;\
                pa1 = p1-->1;\
                pa2 = p2-->1;\
                for (j=0 : j<proplen : j++) pa1-->j = pa2-->j;\
            }\
        }\
        p2 = p2+10;\
    }\
  ]"},

/*  RT__Err:
    For run-time errors occurring in the above: e.g., an attempt to write to
    a non-existent individual property. */

  {"RT__Err",
   "crime obj id   size p q;\
    print \"^[** Programming error: \";\
    if (crime<0) jump RErr;\
    if (crime==1) {\
        print \"class \";\
        q = obj-->3;\
        @streamstr q;\
        \": 'create' can have 0 to 3 parameters only **]\";\
    }\
    if (crime == 40)\
        \"tried to change printing variable \", obj, \"; must be 0 to \", #dynam_string_table-->0-1, \" **]\";\
    if (crime == 36)\
        \"tried to print (object) on something not an \", \"object or class **]\";\
    if (crime == 35)\
        \"tried to print (string) on something not a \", \"string **]\";\
    if (crime == 34)\
        \"tried to print (address) on something not the \", \"address of a dict word **]\";\
    if (crime == 33)\
        \"tried to print (char) \", obj, \", which is not a valid Glk character code for output **]\";\
    if (crime == 32)\
        \"objectloop broken because the object \", (name) obj, \" was moved while the loop passed through it **]\";\
    if (crime < 32) {\
        print \"tried to \";\
        if (crime >= 28) {\
            if (crime == 28 or 29) print \"read from \";\
            else                   print \"write to \";\
            if (crime == 29 or 31) print \"-\";\
            print \"->\", obj, \" in the\";\
            switch (size&7) {\
              0,1:                    q = 0;\
              2:   print \" string\"; q = 1;\
              3:   print \" table\";  q = 1;\
              4:   print \" buffer\"; q = WORDSIZE;\
            }\
            if (size&16) print \" (->)\";\
            if (size&8)  print \" (-->)\";\
            \" array ~\", (string) #array_names_offset-->p, \"~, which has entries \", q, \" up to \",id,\" **]\";\
        }\
        if (crime >= 24 && crime <= 27) {\
            if (crime <= 25) print \"read\";\
            else             print \"write\";\
            print \" outside memory using \";\
            switch (crime) {\
              24,26: \"-> **]\";\
              25,27: \"--> **]\";\
            }\
        }\
        if (crime < 4) print \"test \";\
        else\
            if (crime < 12 || crime > 20) print \"find the \";\
            else\
                if (crime < 14) print \"use \";\
        if (crime == 20) \"divide by zero **]\";\
        print \"~\";\
        switch (crime) {\
           2: print \"in~ or ~notin\";\
           3: print \"has~ or ~hasnt\";\
           4: print \"parent\";\
           5: print \"eldest\";\
           6: print \"child\";\
           7: print \"younger\";\
           8: print \"sibling\";\
           9: print \"children\";\
          10: print \"youngest\";\
          11: print \"elder\";\
          12: print \"objectloop\";\
          13: print \"}~ at end of ~objectloop\";\
          14: \"give~ an attribute to \", (name) obj, \" **]\";\
          15: \"remove~ \", (name) obj, \" **]\";\
          16,17,18:\
            print \"move~ \", (name) obj, \" to \", (name) id;\
            if (crime == 18) {\
                print \", which would make a loop: \",(name) obj;\
                p = id;\
                if (p == obj) p = obj;\
                else\
                    do {\
                        print \" in \", (name) p;\
                        p = parent(p);\
                    } until (p == obj);\
                \" in \", (name) p, \" **]\";\
            }\
            \" **]\";\
          19: \"give~ or test ~has~ or ~hasnt~ with a non-attribute on the object \",(name) obj,\" **]\";\
          21: print \".&\";\
          22: print \".#\";\
          23: print \".\";\
        }\
        \"~ of \", (name) obj, \" **]\";\
    }\
  .RErr;\
    if (obj == 0 || obj->0 >= $70 && obj->0 <= $7F) {\
        if (obj && obj in Class) print \"class \";\
        if (obj) print (object) obj;\
        else     print \"nothing\";\
        print\" \";\
    }\
    print \"(object number \", obj, \") \";\
    if (id < 0) print \"is not of class \", (name) -id;\
    else {\
        print \" has no property \", (property) id;\
        p = #identifiers_table;\
        size = INDIV_PROP_START + p-->3;\
        if (id < 0 || id >= size) print \" (and nor has any other object)\";\
    }\
    print \" to \", (string) crime, \" **]^\";\
  ]"},

/*  Z__Region:
    Determines whether a value is:
        1  an object number
        2  a code address
        3  a string address
        0  none of the above. */

  {"Z__Region",
   "addr   tb endmem;\
    if (addr < 36) rfalse;\
    @getmemsize endmem;\
    @jgeu addr endmem?outrange;\
    tb = addr->0;\
    if (tb >= $E0) return 3;\
    if (tb >= $C0) return 2;\
    if (tb >= $70 && tb <= $7F && addr >= (0-->2)) return 1;\
  .outrange;\
    rfalse;\
  ]"},

/*  Unsigned__Compare:
    returns 1 if x>y, 0 if x=y, -1 if x<y. */

  {"Unsigned__Compare",
   "x y   u v;\
    if (x == y) return 0;\
    if (x < 0 && y >= 0) return 1;\
    if (x >= 0 && y < 0) return -1;\
    u = x & $7FFFFFFF; v = y & $7FFFFFFF;\
    if (u > v) return 1;\
    return -1;\
  ]"},

/*  Meta__class:
    returns the metaclass of an object. */

  {"Meta__class",
   "obj;\
    switch (Z__Region(obj)) {\
      2: return Routine;\
      3: return String;\
      1: if (obj in Class || obj == Class or String or Routine or Object) return Class;\
         return Object;\
    }\
    rfalse;\
  ]"},

/*  CP__Tab:
    Search a property table for the given identifier. The definition here is a
    bit different from the Z-code veneer. This just searches the property table
    of obj for an entry with the given identifier. It return the address of the
    property entry, or 0 if nothing found. (Remember that the value returned is
    not the address of the property *data*; it's the structure which contains
    the address/length/flags.) */

  {"CP__Tab",
   "obj id   otab max res;\
    if (Z__Region(obj) ~=1 ) { RT__Err(23, obj); rfalse; }\
    otab = obj-->4;\
    if (otab == 0) return 0;\
    max = otab-->0;\
    otab = otab + WORDSIZE;\
    @binarysearch id 2 otab 10 max 0 0 res;\
    return res;\
  ]"},

/*  Cl__Ms:
    Implements the five message-receiving properties of Classes. */

  {"Cl__Ms",
   "_vararg_count obj id   a b x y;\
    @copy sp obj;\
    @copy sp id;\
    _vararg_count = _vararg_count - 2;\
    switch (id) {\
      create:\
        if (children(obj) <= 1) rfalse;\
        x = child(obj);\
        remove x;\
        if (x provides create) {\
            @copy create sp;\
            @copy x sp;\
            y = _vararg_count + 2;\
            @call CA__Pr y 0;\
        }\
        return x;\
      recreate:\
        @copy sp a;\
        _vararg_count--;\
        if (~~a ofclass obj) { RT__Err(\"recreate\", a, -obj); rfalse; }\
        if (a provides destroy) a.destroy();\
        Copy__Primitive(a, child(obj));\
        if (a provides create) {\
            @copy create sp;\
            @copy a sp;\
            y = _vararg_count + 2;\
            @call CA__Pr y 0;\
        }\
        rfalse;\
      destroy:\
        @copy sp a;\
        _vararg_count--;\
        if (~~(a ofclass obj)) { RT__Err(\"destroy\", a, -obj); rfalse; }\
        if (a provides destroy) a.destroy();\
        Copy__Primitive(a, child(obj));\
        move a to obj;\
        rfalse;\
      remaining:\
        return children(obj)-1;\
      copy:\
        @copy sp a;\
        @copy sp b;\
        _vararg_count = _vararg_count - 2;\
        if (~~a ofclass obj) { RT__Err(\"copy\", a, -obj); rfalse; }\
        if (~~b ofclass obj) { RT__Err(\"copy\", b, -obj); rfalse; }\
        Copy__Primitive(a, b);\
        rfalse;\
    }\
  ]"},

/*  RT__ChT:
    Run-time check that a proposed object "move" is legal. Cause error and
    do nothing if not; otherwise move. */

  {"RT__ChT",
   "obj1 obj2   ix;\
    if (obj1 == 0 || Z__Region(obj1) ~= 1 ||\
       (obj1 == Class or String or Routine or Object) || obj1 in Class) return RT__Err(16, obj1, obj2);\
    if (obj2 == 0 || Z__Region(obj2) ~= 1 ||\
       (obj2 == Class or String or Routine or Object) || obj2 in Class) return RT__Err(17, obj1, obj2);\
    ix = obj2;\
    while (ix ~= 0) {\
        if (ix == obj1) return RT__Err(18, obj1, obj2);\
        ix = parent(ix);\
    }\
    #Ifdef INFIX;\
    if (obj1 has infix__watching || obj2 has infix__watching || (debug_flag & 15))\
        print \"[ Moving ~\", (name) obj1, \"~ to ~\", (name) obj2, \"~ ]^\";\
    #Ifnot; #Ifdef DEBUG;\
    if (debug_flag & 15)\
        print \"[ Moving ~\", (name) obj1, \"~ to ~\", (name) obj2, \"~ ]^\";\
    #Endif; #Endif;\
    OB__Move(obj1, obj2);\
  ]"},

/*  RT__ChR:
    Run-time check that a proposed object "remove" is legal. Cause error and
    do nothing if not; otherwise remove. */

  {"RT__ChR",
   "obj;\
    if (obj == 0 || Z__Region(obj) ~= 1 ||\
       (obj == Class or String or Routine or Object) || obj in Class) return RT__Err(15, obj);\
    #Ifdef INFIX;\
    if (obj has infix__watching || (debug_flag & 15)) print \"[ Removing ~\", (name) obj, \"~ ]^\";\
    #Ifnot; #Ifdef DEBUG;\
    if (debug_flag & 15) print \"[ Removing ~\", (name) obj, \"~ ]^\";\
    #Endif; #Endif;\
    OB__Remove(obj);\
  ]"},

/*  RT__ChG:
    Run-time check that a proposed attr "give" is legal. Cause error and
    do nothing if not; otherwise give. */

  {"RT__ChG",
   "obj   a;\
    if (obj == 0 || Z__Region(obj) ~= 1 ||\
       (obj == Class or String or Routine or Object) || obj in Class) return RT__Err(14, obj);\
    if (a < 0 || a >= NUM_ATTR_BYTES*8) return RT__Err(19, obj);\
    if (obj has a) return;\
    #Ifdef INFIX;\
    if (a ~= workflag && (obj has infix__watching || (debug_flag & 15)))\
        print \"[ Giving ~\", (name) obj, \"~ \", (DebugAttribute) a, \" ]^\";\
    #Ifnot; #Ifdef DEBUG;\
    if (a ~= workflag && debug_flag & 15)\
        print \"[ Giving ~\", (name) obj, \"~ \", (DebugAttribute) a, \" ]^\";\
    #Endif; #Endif;\
    give obj a;\
  ]"},

/*  RT__ChGt:
    Run-time check that a proposed attr "give ~" is legal. Cause error and
    do nothing if not; otherwise give. */

  {"RT__ChGt",
   "obj   a;\
    if (obj == 0 || Z__Region(obj) ~= 1 ||\
       (obj == Class or String or Routine or Object) || obj in Class) return RT__Err(14, obj);\
    if (a < 0 || a >= NUM_ATTR_BYTES*8) return RT__Err(19, obj);\
    if (obj hasnt a) return;\
    #Ifdef INFIX;\
    if (a ~= workflag && (obj has infix__watching || (debug_flag & 15)))\
        print \"[ Giving ~\", (name) obj, \"~ @@126\", (DebugAttribute) a, \" ]^\";\
    #Ifnot; #Ifdef DEBUG;\
    if (a ~= workflag && debug_flag & 15)\
        print \"[ Giving ~\", (name) obj, \"~ @@126\", (DebugAttribute) a, \" ]^\";\
    #Endif; #Endif;\
    give obj ~a;\
  ]"},

/*  RT__ChPS:
    Run-time check that a proposed property "set" is legal. Cause error and
    do nothing if not; otherwise make it. */

  {"RT__ChPS",
   "obj prop val   res;\
    if (obj == 0 || Z__Region(obj) ~= 1 ||\
       (obj == Class or String or Routine or Object) || obj in Class) return RT__Err(\"set\", obj, prop);\
    res = WV__Pr(obj, prop, val);\
    #Ifdef INFIX;\
    if (obj has infix__watching || (debug_flag & 15)) RT__TrPS(obj, prop, val);\
    #Ifnot; #Ifdef DEBUG;\
    if (debug_flag & 15) RT__TrPS(obj, prop, val);\
    #Endif; #Endif;\
    return res;\
  ]"},

/*  RT__ChPR:
    Run-time check that a proposed property "read" is legal. Cause error and
    return zero if not; otherwise read it. */

  {"RT__ChPR",
   "obj prop;\
    if (obj == 0 || Z__Region(obj) ~= 1 ||\
       (obj == Class or String or Routine or Object)) {\
        RT__Err(\"read\", obj, prop);\
        obj = 2;\
    }\
    return RV__Pr(obj, prop);\
  ]"},

/*  RT__TrPS:
    Trace property settings. */

  {"RT__TrPS",
   "obj prop val;\
    if (VerboseDebugMessages(obj, prop)) {\
        print \"[ Setting ~\", (name) obj, \"~.\", (property) prop, \" to \", val, \" ]^\";\
    }\
  ]"},

/*  RT__ChLDB:
    Run-time check that it's safe to load a byte and return the byte. */

  {"RT__ChLDB",
   "base offset   a b val;\
    a = base + offset;\
    @getmemsize b;\
    if (Unsigned__Compare(a, b) >= 0) return RT__Err(24);\
    @aloadb base offset val;\
    return val;\
  ]"},

/*  RT__ChLDW:
    Run-time check that it's safe to load a word and return the word. */

  {"RT__ChLDW",
   "base offset   a b val;\
    a = base + WORDSIZE*offset;\
    @getmemsize b;\
    if (Unsigned__Compare(a, b) >= 0) return RT__Err(25);\
    @aload base offset val;\
    return val;\
  ]"},

/*  RT__ChSTB:
    Run-time check that it's safe to store a byte and store it. */

  {"RT__ChSTB",
   "base offset val   a b;\
    a = base + offset;\
    @getmemsize b;\
    if (Unsigned__Compare(a, b) >= 0) jump ChSTB_Fail;\
    @aload 0 2 b;\
    if (Unsigned__Compare(a, b) < 0) jump ChSTB_Fail;\
    @astoreb base offset val;\
    return;\
  .ChSTB_Fail;\
    return RT__Err(26);\
  ]"},

/*  RT__ChSTW:
    Run-time check that it's safe to store a word and store it. */

  {"RT__ChSTW",
   "base offset val   a b;\
    a = base + WORDSIZE*offset;\
    @getmemsize b;\
    if (Unsigned__Compare(a, b) >= 0) jump ChSTW_Fail;\
    @aload 0 2 b;\
    if (Unsigned__Compare(a, b) < 0) jump ChSTW_Fail;\
    @astore base offset val;\
    return;\
  .ChSTW_Fail;\
    return RT__Err(27);\
  ]"},

/*  RT__ChLDPrB:
    Run-time check that it's safe to load a byte property and return the byte. */

  {"RT__ChLDPrB",
   "base offset   a b val;\
    a = base + offset;\
    @getmemsize b;\
    if (Unsigned__Compare(a, b) >= 0) return RT__Err(24);\
    @aloadb base offset val;\
    return val;\
  ]"},

/*  RT__ChLDPrW:
    Run-time check that it's safe to load a word property and return the word. */

  {"RT__ChLDPrW",
   "base offset   a b val;\
    a = base + WORDSIZE*offset;\
    @getmemsize b;\
    if (Unsigned__Compare(a, b) >= 0) return RT__Err(25);\
    @aload base offset val;\
    return val;\
  ]"},

/*  RT__ChSTPrB:
    Run-time check that it's safe to store a byte property and store it. */

  {"RT__ChSTPrB",
   "base offset val   a b;\
    a = base + offset;\
    @getmemsize b;\
    if (Unsigned__Compare(a, b) >= 0) jump ChSTPrB_Fail;\
    @aload 0 2 b;\
    if (Unsigned__Compare(a, b) < 0) jump ChSTPrB_Fail;\
    @astoreb base offset val;\
    return;\
  .ChSTPrB_Fail;\
    return RT__Err(26);\
  ]"},

/*  RT__ChSTPrW:
    Run-time check that it's safe to store a word property and store it. */

  {"RT__ChSTPrW",
   "base offset val   a b;\
    a = base + WORDSIZE*offset;\
    @getmemsize b;\
    if (Unsigned__Compare(a, b) >= 0) jump ChSTPrW_Fail;\
    @aload 0 2 b;\
    if (Unsigned__Compare(a, b) < 0) jump ChSTPrW_Fail;\
    @astore base offset val;\
    return;\
  .ChSTPrW_Fail;\
    return RT__Err(27);\
  ]"},

/*  RT__ChPrintC:
    Run-time check that it's safe to print (char) and do so. */

  {"RT__ChPrintC",
   "c;\
    if (c < 10 || (c > 10 && c < 32) || (c > 126 && c < 160) || c > 255) return RT__Err(33, c);\
    @streamchar c;\
  ]"},

/*  RT__ChPrintA:
    Run-time check that it's safe to print (address) and do so. */

  {"RT__ChPrintA",
   "addr   endmem;\
    if (addr < 36) return RT__Err(34);\
    @getmemsize endmem;\
    if (Unsigned__Compare(addr, endmem) >= 0) return RT__Err(34);\
    if (addr->0 ~= $60) return RT__Err(34);\
    Print__Addr(addr);\
  ]"},

/*  RT__ChPrintS:
    Run-time check that it's safe to print (string) and do so. */

  {"RT__ChPrintS",
   "str;\
    if (Z__Region(str) ~= 3) return RT__Err(35);\
    @streamstr str;\
  ]"},

/*  RT__ChPrintO:
    Run-time check that it's safe to print (object) and do so. */

  {"RT__ChPrintO",
   "obj;\
    if (Z__Region(obj) ~= 1) return RT__Err(36);\
    @aload obj 3 sp;\
    @streamstr sp;\
  ]"},

/*  AssertFailed:
    Handle runtime assertion failure. */

  {"AssertFailed",
   "file line;\
    print \"^[** Assertion failed at line \";\
    print line, \" in file ~\", (string) file, \"~ **]^\";\
  ]"},

/*  VerboseDebugMessages:
    Optionally suppress debugging messages for Library objects. */

  {"VerboseDebugMessages",
   "obj prop;\
    #Ifdef DEBUG;\
    if (debug_flag & $0080) rtrue;\
    if (obj == LibraryExtensions or LibraryMessages or InformParser or InformLibrary) rfalse;\
    if (obj in LibraryExtensions or Compass) rfalse;\
    #Endif;\
    prop = obj;\
    rtrue;\
  ]"},

/*  OB__Move:
    Move an object within the object tree. This does no more error checking
    than the Z-code "move" opcode. */

  {"OB__Move",
   "obj dest   par chi sib;\
    par = obj-->5;\
    if (par) {\
        chi = par-->7;\
        if (chi == obj) par-->7 = obj-->6;\
        else {\
            while (true) {\
                sib = chi-->6;\
                if (sib == obj) break;\
                chi = sib;\
            }\
            chi-->6 = obj-->6;\
        }\
    }\
    obj-->6 = dest-->7;\
    obj-->5 = dest;\
    dest-->7 = obj;\
    rfalse;\
  ]"},

/*  OB__Remove:
    Remove an object from the tree. This does no more error checking than
    the Z-code "remove" opcode.
    -->5 is parent; -->6 is sibling; -->7 is child. */

  {"OB__Remove",
   "obj   par chi sib;\
    par = obj-->5;\
    if (par == 0) rfalse;\
    chi = par-->7;\
    if (chi == obj) par-->7 = obj-->6;\
    else {\
        while (1) {\
            sib = chi-->6;\
            if (sib == obj) break;\
            chi = sib;\
        }\
        chi-->6 = obj-->6;\
    }\
    obj-->6 = 0;\
    obj-->5 = 0;\
    rfalse;\
  ]"},

/*  Print__Addr:
    Handle the print (address) statement. In Glulx, this behaves differently
    than on the Z-machine; it can *only* print dictionary words. */

  {"Print__Addr",
   "addr   ix ch;\
    if (addr->0 ~= $60) {\
        print \"(\", addr, \": not dict word)\";\
        return;\
    }\
    for (ix=1 : ix<=DICT_WORD_SIZE : ix++) {\
        ch = addr->ix;\
        if (ch == 0) return;\
        print (char) ch;\
    }\
  ]"},

/*  Glk__Wrap:
    This is a wrapper for the @glk opcode. It just passes all its arguments
    into the Glk dispatcher, and returns the Glk call result. */

  {"Glk__Wrap",
   "_vararg_count callid   retval;\
    @copy sp callid;\
    _vararg_count = _vararg_count - 1;\
    @glk callid _vararg_count retval;\
    return retval;\
  ]"},

/*  Dynam__String:
    Set dynamic string (printing variable) num to the given val, which can be
    any string or function. */

  {"Dynam__String",
   "num val;\
    if (num < 0 || num >= #dynam_string_table-->0) return RT__Err(40, num);\
    (#dynam_string_table)-->(num+1) = val;\
  ]"}

}; /* End of VRs_g -- veneer routines for Glulx */


static void mark_as_needed_z(int code) {
    ASSERT_ZCODE();
    if (veneer_routine_needs_compilation[code] == VR_UNUSED) {
        veneer_routine_needs_compilation[code] = VR_CALLED;
        /* Here each routine must mark every veneer routine it explicitly
           calls as needed */
        switch (code) {
          case WV__Pr_VR:
            mark_as_needed_z(RT__TrPS_VR);
            mark_as_needed_z(RT__Err_VR);
            return;
          case RV__Pr_VR:
            mark_as_needed_z(RT__Err_VR);
            return;
          case CA__Pr_VR:
            mark_as_needed_z(Z__Region_VR);
            mark_as_needed_z(Cl__Ms_VR);
            mark_as_needed_z(RT__Err_VR);
            mark_as_needed_z(VerboseDebugMessages_VR);
            return;
          case IB__Pr_VR:
          case IA__Pr_VR:
          case DB__Pr_VR:
          case DA__Pr_VR:
            mark_as_needed_z(RT__Err_VR);
            mark_as_needed_z(RT__TrPS_VR);
            return;
          case RA__Pr_VR:
            mark_as_needed_z(CP__Tab_VR);
            return;
          case RA__Sc_VR:
            mark_as_needed_z(RT__Err_VR);
            return;
          case OP__Pr_VR:
            mark_as_needed_z(Z__Region_VR);
            return;
          case OC__Cl_VR:
            mark_as_needed_z(Z__Region_VR);
            mark_as_needed_z(RT__Err_VR);
            return;
          case Z__Region_VR:
            mark_as_needed_z(Unsigned__Compare_VR);
            return;
          case Metaclass_VR:
            mark_as_needed_z(Z__Region_VR);
            return;
          case Cl__Ms_VR:
            mark_as_needed_z(RT__Err_VR);
            mark_as_needed_z(Copy__Primitive_VR);
            return;
          case RT__ChR_VR:
          case RT__ChT_VR:
          case RT__ChG_VR:
          case RT__ChGt_VR:
          case RT__ChPR_VR:
          case RT__ChLDPrB_VR:
          case RT__ChLDPrW_VR:
          case RT__ChSTPrB_VR:
          case RT__ChSTPrW_VR:
            mark_as_needed_z(RT__Err_VR);
            return;
          case RT__ChPS_VR:
            mark_as_needed_z(RT__Err_VR);
            mark_as_needed_z(RT__TrPS_VR);
            return;
          case RT__ChLDB_VR:
          case RT__ChLDW_VR:
          case RT__ChSTB_VR:
          case RT__ChSTW_VR:
            mark_as_needed_z(Unsigned__Compare_VR);
            mark_as_needed_z(RT__Err_VR);
            return;
          case RT__ChPrintC_VR:
            mark_as_needed_z(RT__Err_VR);
            return;
          case RT__ChPrintA_VR:
            mark_as_needed_z(Unsigned__Compare_VR);
            mark_as_needed_z(RT__Err_VR);
            return;
          case RT__ChPrintS_VR:
          case RT__ChPrintO_VR:
            mark_as_needed_z(RT__Err_VR);
            mark_as_needed_z(Z__Region_VR);
            return;
          case RT__TrPS_VR:
            mark_as_needed_z(VerboseDebugMessages_VR);
            return;
        }
    }
}

static void mark_as_needed_g(int code) {
    ASSERT_GLULX();
    if (veneer_routine_needs_compilation[code] == VR_UNUSED) {
        veneer_routine_needs_compilation[code] = VR_CALLED;
        /* Here each routine must mark every veneer routine it explicitly
           calls as needed */
        switch (code) {
          case PrintShortName_VR:
            mark_as_needed_g(Metaclass_VR);
            return;
          case Print__Pname_VR:
            mark_as_needed_g(PrintShortName_VR);
            return;
          case WV__Pr_VR:
            mark_as_needed_g(RA__Pr_VR);
            mark_as_needed_g(RT__TrPS_VR);
            mark_as_needed_g(RT__Err_VR);
            return;
          case RV__Pr_VR:
            mark_as_needed_g(RA__Pr_VR);
            mark_as_needed_g(RT__Err_VR);
            return;
          case CA__Pr_VR:
            mark_as_needed_g(RA__Pr_VR);
            mark_as_needed_g(RL__Pr_VR);
            mark_as_needed_g(PrintShortName_VR);
            mark_as_needed_g(Print__Pname_VR);
            mark_as_needed_g(Z__Region_VR);
            mark_as_needed_g(Cl__Ms_VR);
            mark_as_needed_g(Glk__Wrap_VR);
            mark_as_needed_g(RT__Err_VR);
            mark_as_needed_g(VerboseDebugMessages_VR);
            return;
          case IB__Pr_VR:
          case IA__Pr_VR:
          case DB__Pr_VR:
          case DA__Pr_VR:
            mark_as_needed_g(RT__Err_VR);
            mark_as_needed_g(RT__TrPS_VR);
            return;
          case RA__Pr_VR:
            mark_as_needed_g(OC__Cl_VR);
            mark_as_needed_g(CP__Tab_VR);
            return;
          case RL__Pr_VR:
            mark_as_needed_g(OC__Cl_VR);
            mark_as_needed_g(CP__Tab_VR);
            return;
          case RA__Sc_VR:
            mark_as_needed_g(OC__Cl_VR);
            mark_as_needed_g(RT__Err_VR);
            return;
          case OP__Pr_VR:
            mark_as_needed_g(RA__Pr_VR);
            mark_as_needed_g(Z__Region_VR);
            return;
          case OC__Cl_VR:
            mark_as_needed_g(RA__Pr_VR);
            mark_as_needed_g(RL__Pr_VR);
            mark_as_needed_g(Z__Region_VR);
            mark_as_needed_g(RT__Err_VR);
            return;
          case Copy__Primitive_VR:
            mark_as_needed_g(CP__Tab_VR);
            return;
          case Z__Region_VR:
            mark_as_needed_g(Unsigned__Compare_VR);
            return;
          case CP__Tab_VR:
          case Metaclass_VR:
            mark_as_needed_g(Z__Region_VR);
            return;
          case Cl__Ms_VR:
            mark_as_needed_g(OC__Cl_VR);
            mark_as_needed_g(OP__Pr_VR);
            mark_as_needed_g(RT__Err_VR);
            mark_as_needed_g(Copy__Primitive_VR);
            mark_as_needed_g(OB__Remove_VR);
            mark_as_needed_g(OB__Move_VR);
            return;
          case RT__ChG_VR:
          case RT__ChGt_VR:
            mark_as_needed_g(RT__Err_VR);
            return;
          case RT__ChR_VR:
            mark_as_needed_g(RT__Err_VR);
            mark_as_needed_g(Z__Region_VR);
            mark_as_needed_g(OB__Remove_VR);
            return;
          case RT__ChT_VR:
            mark_as_needed_g(RT__Err_VR);
            mark_as_needed_g(Z__Region_VR);
            mark_as_needed_g(OB__Move_VR);
            return;
          case RT__ChPS_VR:
            mark_as_needed_g(RT__Err_VR);
            mark_as_needed_g(RT__TrPS_VR);
            mark_as_needed_g(WV__Pr_VR);
            return;
          case RT__ChPR_VR:
            mark_as_needed_g(RT__Err_VR);
            mark_as_needed_g(RV__Pr_VR); return;
          case RT__ChLDB_VR:
          case RT__ChLDW_VR:
          case RT__ChSTB_VR:
          case RT__ChSTW_VR:
            mark_as_needed_g(Unsigned__Compare_VR);
            mark_as_needed_g(RT__Err_VR);
            return;
          case RT__ChPrintC_VR:
            mark_as_needed_g(RT__Err_VR);
            return;
          case RT__ChPrintA_VR:
            mark_as_needed_g(Unsigned__Compare_VR);
            mark_as_needed_g(RT__Err_VR);
            mark_as_needed_g(Print__Addr_VR);
            return;
          case RT__ChPrintS_VR:
          case RT__ChPrintO_VR:
            mark_as_needed_g(RT__Err_VR);
            mark_as_needed_g(Z__Region_VR);
            return;
          case Print__Addr_VR:
            mark_as_needed_g(RT__Err_VR);
            return;
          case Dynam__String_VR:
            mark_as_needed_g(RT__Err_VR);
            return;
          case RT__TrPS_VR:
            mark_as_needed_g(VerboseDebugMessages_VR);
            return;
        }
    }
}

extern assembly_operand veneer_routine(int code) {
    assembly_operand AO;
    if (!glulx_mode) {
        AO.type = LONG_CONSTANT_OT;
        AO.marker = VROUTINE_MV;
        AO.value = code;
        mark_as_needed_z(code);
    }
    else {
        AO.type = CONSTANT_OT;
        AO.marker = VROUTINE_MV;
        AO.value = code;
        mark_as_needed_g(code);
    }
    return(AO);
}

static void compile_symbol_table_routine(void) {
    int32 j, nl, arrays_l, routines_l, constants_l;
    assembly_operand AO, AO2, AO3; dbgl null_dbgl;
    null_dbgl.b1 = 0; null_dbgl.b2 = 0; null_dbgl.b3 = 0; null_dbgl.cc = 0;

    veneer_mode = TRUE; j = symbol_index("Symb__Tab", -1);
    local_variables.keywords[0] = "type"; /* ensure no _vararg_count header */
    local_variables.keywords[1] = "value";
    construct_local_variable_tables();
    assign_symbol(j,
        assemble_routine_header(2, FALSE, "Symb__Tab", &null_dbgl, FALSE, j),
        ROUTINE_T);
    restart_lexer("", "Symb__Tab");

    sflags[j] |= SYSTEM_SFLAG + USED_SFLAG;
    if (trace_fns_setting==3) sflags[j] |= STAR_SFLAG;

    if (!glulx_mode) { /* symbol table for Z-code */

        if (define_INFIX_switch == FALSE) {
            assemblez_0(rfalse_zc);
            variable_usage[1] = TRUE;
            variable_usage[2] = TRUE;
            assemble_routine_end(FALSE, &null_dbgl);
            veneer_mode = FALSE;
            return;
        }

        AO.value = 1; AO.type = VARIABLE_OT; AO.marker = 0;
        AO2.type = SHORT_CONSTANT_OT; AO2.marker = 0;
        AO3.type = LONG_CONSTANT_OT; AO3.marker = 0;

        arrays_l = next_label++;
        routines_l = next_label++;
        constants_l = next_label++;

        sequence_point_follows = FALSE;
        AO2.value = 1;
        assemblez_2_branch(je_zc, AO, AO2, arrays_l, TRUE);
        sequence_point_follows = FALSE;
        AO2.value = 2;
        assemblez_2_branch(je_zc, AO, AO2, routines_l, TRUE);
        sequence_point_follows = FALSE;
        AO2.value = 3;
        assemblez_2_branch(je_zc, AO, AO2, constants_l, TRUE);
        sequence_point_follows = FALSE;
        assemblez_0(rtrue_zc);

        assemble_label_no(arrays_l);
        AO.value = 2;
        for (j=0; j<no_arrays; j++) {
            AO2.value = j;
            if (AO2.value<256) AO2.type = SHORT_CONSTANT_OT;
            else AO2.type = LONG_CONSTANT_OT;
            nl = next_label++;
            sequence_point_follows = FALSE;
            assemblez_2_branch(je_zc, AO, AO2, nl, FALSE);
            AO3.value = array_sizes[j];
            AO3.marker = 0;
            assemblez_store(temp_var2, AO3);
            AO3.value = array_types[j];
            if (sflags[array_symbols[j]] & (INSF_SFLAG+SYSTEM_SFLAG))
                AO3.value = AO3.value + 16;
            AO3.marker = 0;
            assemblez_store(temp_var3, AO3);
            AO3.value = svals[array_symbols[j]];
            AO3.marker = ARRAY_MV;
            assemblez_1(ret_zc, AO3);
            assemble_label_no(nl);
        }
        sequence_point_follows = FALSE;
        assemblez_0(rtrue_zc);
        assemble_label_no(routines_l);
        for (j=0; j<no_named_routines; j++) {
            AO2.value = j;
            if (AO2.value<256) AO2.type = SHORT_CONSTANT_OT;
            else AO2.type = LONG_CONSTANT_OT;
            nl = next_label++;
            sequence_point_follows = FALSE;
            assemblez_2_branch(je_zc, AO, AO2, nl, FALSE);
            AO3.value = 0;
            if (sflags[named_routine_symbols[j]]
                & (INSF_SFLAG+SYSTEM_SFLAG)) AO3.value = 16;
            AO3.marker = 0;
            assemblez_store(temp_var3, AO3);
            AO3.value = svals[named_routine_symbols[j]];
            AO3.marker = IROUTINE_MV;
            assemblez_1(ret_zc, AO3);
            assemble_label_no(nl);
        }
        sequence_point_follows = FALSE;
        assemblez_0(rtrue_zc);

        assemble_label_no(constants_l);
        for (j=0, no_named_constants=0; j<no_symbols; j++) {
            if (((stypes[j] == OBJECT_T) || (stypes[j] == CLASS_T)
              || (stypes[j] == CONSTANT_T))
              && ((sflags[j] & (UNKNOWN_SFLAG+ACTION_SFLAG))==0)) {
                AO2.value = no_named_constants++;
                if (AO2.value<256) AO2.type = SHORT_CONSTANT_OT;
                else AO2.type = LONG_CONSTANT_OT;
                nl = next_label++;
                sequence_point_follows = FALSE;
                assemblez_2_branch(je_zc, AO, AO2, nl, FALSE);
                AO3.value = 0;
                if (stypes[j] == OBJECT_T) AO3.value = 2;
                if (stypes[j] == CLASS_T) AO3.value = 1;
                if (sflags[j] & (INSF_SFLAG+SYSTEM_SFLAG))
                    AO3.value = AO3.value + 16;
                AO3.marker = 0;
                assemblez_store(temp_var3, AO3);
                AO3.value = j;
                AO3.marker = SYMBOL_MV;
                assemblez_1(ret_zc, AO3);
                assemble_label_no(nl);
            }
        }
        no_named_constants = 0; AO3.marker = 0;

        sequence_point_follows = FALSE;
        assemblez_0(rfalse_zc);
        variable_usage[1] = TRUE;
        variable_usage[2] = TRUE;
        assemble_routine_end(FALSE, &null_dbgl);
        veneer_mode = FALSE;

    }
    else { /* symbol table for Glulx */

        if (define_INFIX_switch == FALSE) {
            assembleg_1(return_gc, zero_operand);
            variable_usage[1] = TRUE;
            variable_usage[2] = TRUE;
            assemble_routine_end(FALSE, &null_dbgl);
            veneer_mode = FALSE;
            return;
        }

        AO.value = 1; AO.type = LOCALVAR_OT; AO.marker = 0;
        AO2.type = BYTECONSTANT_OT; AO2.marker = 0;
        AO3.type = CONSTANT_OT; AO3.marker = 0;

        arrays_l = next_label++;
        routines_l = next_label++;
        constants_l = next_label++;

        sequence_point_follows = FALSE;
        AO2.value = 1;
        assembleg_2_branch(jeq_gc, AO, AO2, arrays_l);
        sequence_point_follows = FALSE;
        AO2.value = 2;
        assembleg_2_branch(jeq_gc, AO, AO2, routines_l);
        sequence_point_follows = FALSE;
        AO2.value = 3;
        assembleg_2_branch(jeq_gc, AO, AO2, constants_l);
        sequence_point_follows = FALSE;
        assembleg_1(return_gc, one_operand);

        assemble_label_no(arrays_l);
        AO.value = 2;
        for (j=0; j<no_arrays; j++) {
            AO2.value = j;
            if (AO2.value<128) AO2.type = BYTECONSTANT_OT;
            else if (AO2.value<32768) AO2.type = HALFCONSTANT_OT;
            else AO2.type = CONSTANT_OT;
            nl = next_label++;
            sequence_point_follows = FALSE;
            assembleg_2_branch(jne_gc, AO, AO2, nl);
            AO3.value = array_sizes[j];
            AO3.marker = 0;
            assembleg_store(temp_var2, AO3);
            AO3.value = array_types[j];
            if (sflags[array_symbols[j]] & (INSF_SFLAG+SYSTEM_SFLAG))
                AO3.value = AO3.value + 16;
            AO3.marker = 0;
            assembleg_store(temp_var3, AO3);
            AO3.value = svals[array_symbols[j]];
            AO3.marker = ARRAY_MV;
            assembleg_1(return_gc, AO3);
            assemble_label_no(nl);
        }
        sequence_point_follows = FALSE;
        assembleg_1(return_gc, one_operand);

        assemble_label_no(routines_l);
        for (j=0; j<no_named_routines; j++) {
            AO2.value = j;
            if (AO2.value<128) AO2.type = BYTECONSTANT_OT;
            else if (AO2.value<32768) AO2.type = HALFCONSTANT_OT;
            else AO2.type = CONSTANT_OT;
            nl = next_label++;
            sequence_point_follows = FALSE;
            assembleg_2_branch(jne_gc, AO, AO2, nl);
            AO3.value = 0;
            if (sflags[named_routine_symbols[j]]
                & (INSF_SFLAG+SYSTEM_SFLAG)) AO3.value = 16;
            AO3.marker = 0;
            assembleg_store(temp_var3, AO3);
            AO3.value = svals[named_routine_symbols[j]];
            AO3.marker = IROUTINE_MV;
            assembleg_1(return_gc, AO3);
            assemble_label_no(nl);
        }
        sequence_point_follows = FALSE;
        assembleg_1(return_gc, one_operand);

        assemble_label_no(constants_l);
        for (j=0, no_named_constants=0; j<no_symbols; j++) {
            if (((stypes[j] == OBJECT_T) || (stypes[j] == CLASS_T)
              || (stypes[j] == CONSTANT_T))
              && ((sflags[j] & (UNKNOWN_SFLAG+ACTION_SFLAG))==0)) {
                AO2.value = no_named_constants++;
                if (AO2.value<128) AO2.type = BYTECONSTANT_OT;
                else if (AO2.value<32768) AO2.type = HALFCONSTANT_OT;
                else AO2.type = CONSTANT_OT;
                nl = next_label++;
                sequence_point_follows = FALSE;
                assembleg_2_branch(jne_gc, AO, AO2, nl);
                AO3.value = 0;
                if (stypes[j] == OBJECT_T) AO3.value = 2;
                if (stypes[j] == CLASS_T) AO3.value = 1;
                if (sflags[j] & (INSF_SFLAG+SYSTEM_SFLAG))
                    AO3.value = AO3.value + 16;
                AO3.marker = 0;
                assembleg_store(temp_var3, AO3);
                AO3.value = j;
                AO3.marker = SYMBOL_MV;
                assembleg_1(return_gc, AO3);
                assemble_label_no(nl);
            }
        }
        no_named_constants = 0; AO3.marker = 0;

        sequence_point_follows = FALSE;
        assembleg_1(return_gc, zero_operand);
        variable_usage[1] = TRUE;
        variable_usage[2] = TRUE;
        assemble_routine_end(FALSE, &null_dbgl);
        veneer_mode = FALSE;

    }
}

extern void compile_veneer(void) {
    int i, j, try_veneer_again;
    VeneerRoutine *VRs;

    if (module_switch) return;

    VRs = (!glulx_mode) ? VRs_z : VRs_g;

    /*  Called at the end of the pass to insert as much of the veneer as is
        needed and not elsewhere compiled.  */

    veneer_symbols_base = no_symbols;

    /*  for (i=0; i<VENEER_ROUTINES; i++)
        printf("%s %d\n", VRs[i].name,
            strlen(VRs[i].source)); */

    try_veneer_again = TRUE;
    while (try_veneer_again) {
        try_veneer_again = FALSE;
        for (i=0; i<VENEER_ROUTINES; i++) {
            if (veneer_routine_needs_compilation[i] == VR_CALLED) {
                j = symbol_index(VRs[i].name, -1);
                if (sflags[j] & UNKNOWN_SFLAG) {
                    veneer_mode = TRUE;
                    strcpy(veneer_source_area, VRs[i].source);
                    assign_symbol(j,
                        parse_routine(veneer_source_area, FALSE,
                            VRs[i].name, TRUE, j),
                        ROUTINE_T);
                    veneer_mode = FALSE;
                    if (trace_fns_setting==3) sflags[j] |= STAR_SFLAG;
                }
                else {
                    if (stypes[j] != ROUTINE_T)
                error_named("The following name is reserved by Inform for its \
own use as a routine name; you can use it as a routine name yourself (to \
override the standard definition) but cannot use it for anything else:",
                        VRs[i].name);
                    else
                        sflags[j] |= USED_SFLAG;
                }
                veneer_routine_address[i] = svals[j];
                veneer_routine_needs_compilation[i] = VR_COMPILED;
                try_veneer_again = TRUE;
            }
        }
    }

    make_objectloop_lists();
    compile_symbol_table_routine();
}

/* ========================================================================= */
/*   Data structure management routines                                      */
/* ------------------------------------------------------------------------- */

extern void init_veneer_vars(void) {
}

extern void veneer_begin_pass(void) {
    int i;
    veneer_mode = FALSE;
    for (i=0; i<VENEER_ROUTINES; i++) {
        veneer_routine_needs_compilation[i] = VR_UNUSED;
        veneer_routine_address[i] = 0;
    }
}

extern void veneer_allocate_arrays(void) {
    veneer_source_area = my_malloc(16384, "veneer source code area");
}

extern void veneer_free_arrays(void) {
    my_free(&veneer_source_area, "veneer source code area");
}

/* ========================================================================= */
