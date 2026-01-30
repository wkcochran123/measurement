// Lean compiler output
// Module: Measurement.Chapter1.Propositions
// Imports: public import Init public import Measurement.Chapter1.Axioms
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
static lean_object* lp_measurement_Measurement_ledgerOfNaturalNumbers___closed__0;
LEAN_EXPORT lean_object* lp_measurement_Measurement_ledgerOfNaturalNumbers_aux(lean_object*);
LEAN_EXPORT lean_object* lp_measurement_Measurement_ledgerOfNaturalNumbers;
LEAN_EXPORT lean_object* lp_measurement_Measurement_ledgerOfNaturalNumbers_aux___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_measurement_Measurement_trivialEnumeration___lam__0___boxed(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* lp_measurement_Measurement_ledgerOfNaturalNumbers___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_measurement_Measurement_trivialEnumeration___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_measurement_Measurement_trivialEnumeration;
LEAN_EXPORT lean_object* lp_measurement_Measurement_trivialEnumeration___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_measurement_Measurement_trivialEnumeration___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_measurement_Measurement_trivialEnumeration___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_lp_measurement_Measurement_trivialEnumeration() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lp_measurement_Measurement_trivialEnumeration___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_measurement_Measurement_ledgerOfNaturalNumbers_aux(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 1)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_1, x_5);
x_7 = lp_measurement_Measurement_ledgerOfNaturalNumbers_aux(x_6);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* lp_measurement_Measurement_ledgerOfNaturalNumbers_aux___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_measurement_Measurement_ledgerOfNaturalNumbers_aux(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_lp_measurement_Measurement_ledgerOfNaturalNumbers___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lp_measurement_Measurement_ledgerOfNaturalNumbers_aux(x_1);
return x_2;
}
}
static lean_object* _init_lp_measurement_Measurement_ledgerOfNaturalNumbers___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lp_measurement_Measurement_ledgerOfNaturalNumbers___closed__0;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_measurement_Measurement_ledgerOfNaturalNumbers() {
_start:
{
lean_object* x_1; 
x_1 = lp_measurement_Measurement_ledgerOfNaturalNumbers___closed__1;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_measurement_Measurement_Chapter1_Axioms(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_measurement_Measurement_Chapter1_Propositions(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_measurement_Measurement_Chapter1_Axioms(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_measurement_Measurement_trivialEnumeration = _init_lp_measurement_Measurement_trivialEnumeration();
lean_mark_persistent(lp_measurement_Measurement_trivialEnumeration);
lp_measurement_Measurement_ledgerOfNaturalNumbers___closed__0 = _init_lp_measurement_Measurement_ledgerOfNaturalNumbers___closed__0();
lean_mark_persistent(lp_measurement_Measurement_ledgerOfNaturalNumbers___closed__0);
lp_measurement_Measurement_ledgerOfNaturalNumbers___closed__1 = _init_lp_measurement_Measurement_ledgerOfNaturalNumbers___closed__1();
lean_mark_persistent(lp_measurement_Measurement_ledgerOfNaturalNumbers___closed__1);
lp_measurement_Measurement_ledgerOfNaturalNumbers = _init_lp_measurement_Measurement_ledgerOfNaturalNumbers();
lean_mark_persistent(lp_measurement_Measurement_ledgerOfNaturalNumbers);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
