#include <z3++.h>

#if 0  // Hack to get cffi to include this
struct _Z3_app;
struct _Z3_context;
struct _Z3_model;

typedef struct _Z3_context * Z3_context;
typedef struct _Z3_app * Z3_app;
typedef struct _Z3_model * Z3_model;
#endif /* 0 */

struct buflen {
  ssize_t len;
  char* buf;
};

extern void patch_global_context(Z3_context m_ctx);
extern struct buflen call_strengthen(Z3_app f, Z3_model model, bool debug);
