// Lean compiler output
// Module: Measurement.Chapter3.Constructions
// Imports: public import Init public import Std public import Measurement.Chapter3.ZFC
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* lp_measurement_Measurement_rhoTilde__const___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_measurement_Measurement_rhoTilde__id___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_measurement_Measurement_rhoTilde__id___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_measurement_Measurement_rhoTilde__const___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_measurement_Measurement_rhoTilde__const(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_measurement_Measurement_rhoTilde__const___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_measurement_Measurement_rhoTilde__id(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_measurement_Measurement_rhoTilde__id___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_measurement_Measurement_rhoTilde__id(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_measurement_Measurement_rhoTilde__id___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_measurement_Measurement_rhoTilde__id___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_measurement_Measurement_rhoTilde__id(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_measurement_Measurement_rhoTilde__id___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_measurement_Measurement_rhoTilde__id___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_measurement_Measurement_rhoTilde__const(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_measurement_Measurement_rhoTilde__const___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_measurement_Measurement_rhoTilde__const___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_measurement_Measurement_rhoTilde__const(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_measurement_Measurement_rhoTilde__const___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_measurement_Measurement_rhoTilde__const___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Std(uint8_t builtin);
lean_object* initialize_measurement_Measurement_Chapter3_ZFC(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_measurement_Measurement_Chapter3_Constructions(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_measurement_Measurement_Chapter3_ZFC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
