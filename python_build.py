import cffi
ffi_builder = cffi.FFI()

with open("pythonfuncs.h") as f:
    data = ''.join(l for l in f if not l.startswith('#'))
    ffi_builder.embedding_api(data)

ffi_builder.set_source("pythonfuncs", r"""
#include "pythonfuncs.h"
""")

ffi_builder.embedding_init_code(r"""
import z3
import sys
sys.path.append('./python/')
import formula_strengthener
from pythonfuncs import ffi, lib

def intptr(ptr):
    return int(ffi.cast("intptr_t", ptr))

keep_in_memory = set()

@ffi.def_extern()
def patch_global_context(ctx):
    formula_strengthener.patch_z3_context(intptr(ctx))

@ffi.def_extern()
def call_strengthen(f, model):
    global keep_in_memory
    out = ffi.from_buffer(formula_strengthener.strengthen_wrapper(intptr(f), intptr(model)))
    keep_in_memory.add(out)
    return (len(out), out)
""")

ffi_builder.emit_c_code("pythonfuncs.c")
