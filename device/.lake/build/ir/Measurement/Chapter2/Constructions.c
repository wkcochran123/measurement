// Lean compiler output
// Module: Measurement.Chapter2.Constructions
// Imports: public import Init public import Measurement.Chapter2.ZFC
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
LEAN_EXPORT lean_object* lp_measurement_Measurement_DecomposingMap_00_u03b6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_measurement_Measurement_DecomposingMap_00_u03b6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_measurement_Measurement_SymbolMap_inv___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_measurement_Measurement_DecomposingMap_ofZips___redArg(lean_object*, lean_object*);
lean_object* lp_measurement_Measurement_Enumeration_nth___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_measurement_Measurement_SymbolMap_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_measurement_Measurement_SymbolMap_inv(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_measurement_Measurement_DecomposingMap_ofZips(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_measurement_Measurement_DecomposingMap_00_u03b6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_measurement_Measurement_Enumeration_zip(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_measurement_Measurement_Enumeration_zip___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_measurement_Measurement_SymbolMap_map(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_measurement_Measurement_DecomposingMap_00_u03b6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_measurement_Measurement_SymbolMap_map___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_measurement_Measurement_SymbolMap_map(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_measurement_Measurement_SymbolMap_map___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_measurement_Measurement_SymbolMap_inv___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lp_mathlib_Equiv_symm___redArg(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = lean_apply_1(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_measurement_Measurement_SymbolMap_inv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_measurement_Measurement_SymbolMap_inv___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_measurement_Measurement_Enumeration_zip___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec_ref(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_8);
x_10 = lp_measurement_Measurement_Enumeration_zip___redArg(x_7, x_9);
lean_ctor_set(x_2, 1, x_10);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_12);
x_14 = lp_measurement_Measurement_Enumeration_zip___redArg(x_11, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_1);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_20 = x_2;
} else {
 lean_dec_ref(x_2);
 x_20 = lean_box(0);
}
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_18);
x_22 = lp_measurement_Measurement_Enumeration_zip___redArg(x_17, x_19);
if (lean_is_scalar(x_20)) {
 x_23 = lean_alloc_ctor(1, 2, 0);
} else {
 x_23 = x_20;
}
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_measurement_Measurement_Enumeration_zip(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_measurement_Measurement_Enumeration_zip___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_measurement_Measurement_DecomposingMap_00_u03b6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_measurement_Measurement_Enumeration_nth___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_measurement_Measurement_DecomposingMap_00_u03b6___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_measurement_Measurement_Enumeration_nth___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_measurement_Measurement_DecomposingMap_00_u03b6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_measurement_Measurement_DecomposingMap_00_u03b6(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_measurement_Measurement_DecomposingMap_00_u03b6___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_measurement_Measurement_DecomposingMap_00_u03b6___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_measurement_Measurement_DecomposingMap_ofZips(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_measurement_Measurement_Enumeration_zip___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_measurement_Measurement_DecomposingMap_ofZips___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_measurement_Measurement_Enumeration_zip___redArg(x_1, x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_measurement_Measurement_Chapter2_ZFC(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_measurement_Measurement_Chapter2_Constructions(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_measurement_Measurement_Chapter2_ZFC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
