#include <stdbool.h>

struct isla_source;
typedef struct isla_source isla_source;

/**
 * Isla symbolically executes the intermediate representation (IR) produced by Sail. This function
 * loads the source for that IR from a text file.
 *
 * @param path The path for the file. Must only contain valid UTF-8 characters.
 *
 * @return A pointer to an ::isla_source object. This is a parsed representation of the IR. Various
 * other objects created via this API will hold pointers into this object, so it must not be freed
 * until all objects derived from it have themselves been freed. Returns NULL if any error occurs
 * when loading and parsing the source.
 */
isla_source *isla_source_load(const char *path);

/**
 * Free an ::isla_source object created via isla_source_load(). See the documentation for that
 * function for information about when this function should be called.
 */
void isla_source_free(isla_source *source);

struct isla_symtab;
typedef struct isla_symtab isla_symtab;

/**
 * Create a new IR symbol table
 */
isla_symtab *isla_symtab_new(void);

void isla_symtab_free(isla_symtab *symtab);

struct isla_ir;
typedef struct isla_ir isla_ir;

/**
 * This function takes the IR source and interns the symbols contained within into the given symbol
 * table, and performs various required modifications to the IR before we can use it for symbolic
 * execution.
 *
 * @param symtab This symbol table must be a fresh symbol table created by isla_symtab_new()
 *
 * @param source The source IR
 *
 * @param optimistic This parameter controls how we handle assertions in the IR. If it is true, then
 * we optimistically assume that all assertions succeed, converting them to SMTLIB asserts for each
 * path that goes through that assertion. Note that this still checks if the assertion can possibly
 * succeed (i.e. is satisfiable). If an assertion is unsatisfiable then it will still fail. If this
 * parameter is false we fail if it is possible for an assertion to fail.
 *
 * @return Returns NULL if either of the input pointers are themselves NULL.
 */
isla_ir *isla_symtab_intern(isla_symtab *symtab, const isla_source *source, const bool optimistic);

/**
 * Free an ::isla_ir object
 */
void isla_ir_free(isla_ir *ir);

struct isla_shared_state;
typedef struct isla_shared_state isla_shared_state;

isla_shared_state *isla_shared_state_new(isla_symtab *symtab, const isla_ir *ir);

void isla_shared_state_free(isla_shared_state *shared_state);
