// Lean compiler output
// Module: Perceptron.Definitions
// Imports: public import Init public import Mathlib.Data.Finset.Basic public import Mathlib.Tactic
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
uint8_t l_Rat_instDecidableLe(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_sign(lean_object*);
LEAN_EXPORT lean_object* l_Multiset_sum___at___00Finset_sum___at___00dot_spec__0_spec__0(lean_object*);
lean_object* l_Multiset_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_max__norm__sq(lean_object*, lean_object*);
lean_object* l_Fin_snoc___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_cast___at___00Tactic_NormNum_evalRealSqrt_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_zero__vec___boxed(lean_object*, lean_object*);
static lean_object* l_sign___closed__1;
LEAN_EXPORT lean_object* l_augment___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_margin(lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_mul(lean_object*, lean_object*);
lean_object* l_Rat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_dot(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_dot___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_sign___closed__0;
LEAN_EXPORT lean_object* l_Finset_sum___at___00dot_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_zero__vec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_norm__sq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00max__norm__sq_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_norm__sq___lam__0(lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
LEAN_EXPORT lean_object* l_LabeledPoint_ctorIdx___boxed(lean_object*, lean_object*);
static lean_object* l_Multiset_sum___at___00Finset_sum___at___00dot_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l_augment(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LabeledPoint_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Multiset_sum___at___00Finset_sum___at___00dot_spec__0_spec__0___lam__0(lean_object*, lean_object*);
lean_object* l_Rat_neg(lean_object*);
LEAN_EXPORT lean_object* l_Finset_sum___at___00dot_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LabeledPoint_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LabeledPoint_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_LabeledPoint_ctorIdx(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Multiset_sum___at___00Finset_sum___at___00dot_spec__0_spec__0___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Rat_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Multiset_sum___at___00Finset_sum___at___00dot_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Nat_cast___at___00Tactic_NormNum_evalRealSqrt_spec__4(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Multiset_sum___at___00Finset_sum___at___00dot_spec__0_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Multiset_sum___at___00Finset_sum___at___00dot_spec__0_spec__0___lam__0), 2, 0);
x_3 = l_Multiset_sum___at___00Finset_sum___at___00dot_spec__0_spec__0___closed__0;
x_4 = l_List_foldrTR___redArg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Finset_sum___at___00dot_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Multiset_map___redArg(x_2, x_1);
x_4 = l_Multiset_sum___at___00Finset_sum___at___00dot_spec__0_spec__0(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Finset_sum___at___00dot_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Finset_sum___at___00dot_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_dot___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_3);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_1(x_2, x_3);
x_6 = l_Rat_mul(x_4, x_5);
lean_dec_ref(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_dot(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_dot___lam__0), 3, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = l_List_finRange(x_1);
x_6 = l_Finset_sum___at___00dot_spec__0___redArg(x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_norm__sq___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_apply_1(x_1, x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_Rat_pow(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_norm__sq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_norm__sq___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_List_finRange(x_1);
x_5 = l_Finset_sum___at___00dot_spec__0___redArg(x_4, x_3);
return x_5;
}
}
static lean_object* _init_l_sign___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Nat_cast___at___00Tactic_NormNum_evalRealSqrt_spec__4(x_1);
return x_2;
}
}
static lean_object* _init_l_sign___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_sign___closed__0;
x_2 = l_Rat_neg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_sign(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Multiset_sum___at___00Finset_sum___at___00dot_spec__0_spec__0___closed__0;
x_3 = l_Rat_instDecidableLe(x_2, x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = l_sign___closed__1;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = l_sign___closed__0;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_augment(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_sign___closed__0;
x_5 = l_Fin_snoc___redArg(x_1, x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_augment___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_augment(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_margin(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_5);
lean_dec_ref(x_3);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_1, x_6);
x_8 = lean_alloc_closure((void*)(l_augment___boxed), 3, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_4);
x_9 = l_dot(x_7, x_2, x_8);
x_10 = l_Rat_mul(x_5, x_9);
lean_dec_ref(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00max__norm__sq_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_6);
lean_dec(x_4);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_1, x_7);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_augment___boxed), 3, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_6);
x_10 = l_norm__sq(x_8, x_9);
lean_inc_ref(x_10);
lean_inc_ref(x_2);
x_11 = l_Rat_instDecidableLe(x_2, x_10);
if (x_11 == 0)
{
lean_dec_ref(x_10);
x_3 = x_5;
goto _start;
}
else
{
lean_dec_ref(x_2);
x_2 = x_10;
x_3 = x_5;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_max__norm__sq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Multiset_sum___at___00Finset_sum___at___00dot_spec__0_spec__0___closed__0;
x_4 = l_List_foldl___at___00max__norm__sq_spec__0(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_zero__vec(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Multiset_sum___at___00Finset_sum___at___00dot_spec__0_spec__0___closed__0;
return x_3;
}
}
LEAN_EXPORT lean_object* l_zero__vec___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_zero__vec(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Mathlib_Data_Finset_Basic(uint8_t builtin);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Perceptron_Definitions(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Finset_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Multiset_sum___at___00Finset_sum___at___00dot_spec__0_spec__0___closed__0 = _init_l_Multiset_sum___at___00Finset_sum___at___00dot_spec__0_spec__0___closed__0();
lean_mark_persistent(l_Multiset_sum___at___00Finset_sum___at___00dot_spec__0_spec__0___closed__0);
l_sign___closed__0 = _init_l_sign___closed__0();
lean_mark_persistent(l_sign___closed__0);
l_sign___closed__1 = _init_l_sign___closed__1();
lean_mark_persistent(l_sign___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
