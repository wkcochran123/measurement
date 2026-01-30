// Lean compiler output
// Module: Measurement.Chapter2.Definitions
// Imports: public import Init public import Std public import Measurement.Chapter2.Constructions
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
lean_object* lp_measurement_Measurement_Ledger_toEnum___redArg(lean_object*);
lean_object* lp_measurement_Measurement_Ledger_index___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_measurement_Measurement_Instrument_instrumentRefinement___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_measurement_Measurement_Instrument_domainRefinement___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_measurement_Measurement_Instrument_domainRefinement(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_measurement_Measurement_Instrument_instrumentRefinement___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_measurement_Measurement_Instrument_search___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_measurement_Measurement_Instrument_instrumentRefinement(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_measurement_Measurement_Instrument_search___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_measurement_Measurement_Instrument_search(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_measurement_Measurement_Instrument_search___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_measurement_Measurement_Instrument_instrumentRefinement___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_measurement_Measurement_Instrument_domainRefinement___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lp_measurement_Measurement_Ledger_toEnum___redArg(x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_measurement_Measurement_Instrument_domainRefinement(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_measurement_Measurement_Instrument_domainRefinement___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_measurement_Measurement_Instrument_instrumentRefinement___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_3);
lean_inc(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_measurement_Measurement_Instrument_instrumentRefinement(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_measurement_Measurement_Instrument_instrumentRefinement___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_measurement_Measurement_Instrument_instrumentRefinement___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_measurement_Measurement_Instrument_instrumentRefinement(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_measurement_Measurement_Instrument_instrumentRefinement___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_measurement_Measurement_Instrument_instrumentRefinement___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_measurement_Measurement_Instrument_search___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lp_measurement_Measurement_Ledger_index___redArg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_measurement_Measurement_Instrument_search(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_measurement_Measurement_Instrument_search___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_measurement_Measurement_Instrument_search___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_measurement_Measurement_Instrument_search(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_measurement_Measurement_Instrument_search___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_measurement_Measurement_Instrument_search___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Std(uint8_t builtin);
lean_object* initialize_measurement_Measurement_Chapter2_Constructions(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_measurement_Measurement_Chapter2_Definitions(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_measurement_Measurement_Chapter2_Constructions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
