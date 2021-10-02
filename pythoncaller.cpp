#define PY_SSIZE_T_CLEAN

#include <Python.h>
#include <z3++.h>

#include <iostream>

void initialize_python() {
  Py_Initialize();

  // Add current directory to path
  PyObject *sys = PyImport_ImportModule("sys");
  PyObject *sys_path = PyObject_GetAttrString(sys, "path");
  PyList_Append(sys_path, PyUnicode_FromString("./python/"));
}

void finalize_python() { Py_Finalize(); }

PyObject *get_formula_strengthener_module() {
  return PyImport_ImportModule("formula_strengthener");
}

PyObject *get_z3_module() { return PyImport_ImportModule("z3"); }

void patch_global_context(Z3_context ctx) {
  PyObject *m = get_formula_strengthener_module();
  assert(m);
  PyObject *patch_func = PyObject_GetAttrString(m, "patch_z3_context");
  assert(patch_func);
  // It doesn't look like it but it's a pointer, thanks Microsoft
  PyObject *res = PyObject_CallOneArg(patch_func, PyLong_FromVoidPtr(ctx));
  assert(res);
  Py_DECREF(res);
}

void call_strengthen(Z3_app f, Z3_model model) {
  PyObject *m = get_formula_strengthener_module();
  PyObject *func = PyObject_GetAttrString(m, "strengthen_wrapper");
  assert(func);
  PyObject *res = PyObject_CallFunctionObjArgs(func, PyLong_FromVoidPtr(f),
                                               PyLong_FromVoidPtr(model), NULL);
  PyErr_Print();
  assert(res);
  Py_DECREF(res);
}
