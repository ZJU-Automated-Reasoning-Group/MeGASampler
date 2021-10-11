void initialize_python();
void finalize_python();
void patch_global_context(Z3_context m_ctx);
void call_strengthen(Z3_app f, Z3_model model, bool debug);
