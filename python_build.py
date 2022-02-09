import cffi
ffi_builder = cffi.FFI()

with open("pythonfuncs.h") as f:
    data = ''.join(l for l in f if not l.startswith('#'))
    ffi_builder.embedding_api(data)

ffi_builder.set_source("pythonfuncs", r"""
#include "pythonfuncs.h"
""")

ffi_builder.embedding_init_code(r"""
import sys
import os
sys.path.append('./python/')
if 'VIRTUAL_ENV' in os.environ:
    sys.path.append(f"{os.environ['VIRTUAL_ENV']}/site-packages")
from pythonfuncs import ffi, lib
import pythonfuncs
import formula_strengthener

def intptr(ptr):
    return int(ffi.cast("intptr_t", ptr))

keep_in_memory = None

@ffi.def_extern()
def patch_global_context(ctx):
    formula_strengthener.patch_z3_context(intptr(ctx))

@ffi.def_extern()
def call_strengthen(f, model, isAUF, debug):
    global keep_in_memory
    out = ffi.from_buffer(formula_strengthener.strengthen_wrapper(intptr(f), intptr(model), isAUF, debug))
    # keep until just the next call to leak less
    keep_in_memory = out
    return (len(out), out)
""")

ffi_builder.emit_c_code("pythonfuncs.c")
