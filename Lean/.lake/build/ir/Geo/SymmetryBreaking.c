// Lean compiler output
// Module: Geo.SymmetryBreaking
// Imports: Init Std.Data.List.Lemmas Mathlib.Tactic Mathlib.Data.Matrix.Basic Mathlib.Algebra.Algebra.Basic Geo.PlaneGeometry
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
LEAN_EXPORT lean_object* l_pt__to__vec(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Mathlib_Data_Real_Basic_0__Real_zero;
LEAN_EXPORT lean_object* l_pt__transform(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_transform__points___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Geo_SymmetryBreaking_0__WithBot_unbot_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_pt__transform__2___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Matrix_dotProduct___at_pt__transform__2___spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Geo_SymmetryBreaking_0__List_isEmpty_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1157_(lean_object*, lean_object*);
static lean_object* l_pt__to__vec___closed__2;
LEAN_EXPORT lean_object* l_vec__to__pt(lean_object*);
static lean_object* l_translation__matrix___closed__3;
LEAN_EXPORT lean_object* l_Matrix_dotProduct___at_pt__transform__2___spec__1___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_transform__points(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_pt__transform__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_pt__to__vec___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Multiset_sum___at_pt__transform__2___spec__3___closed__1;
lean_object* l_Multiset_map___rarg(lean_object*, lean_object*);
lean_object* l_Matrix_vecEmpty___boxed(lean_object*, lean_object*);
extern lean_object* l___private_Mathlib_Data_Real_Basic_0__Real_one;
LEAN_EXPORT lean_object* l___private_Geo_SymmetryBreaking_0__List_isEmpty_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Geo_SymmetryBreaking_0__List_get_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_translation__matrix___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Multiset_sum___at_pt__transform__2___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Finset_sum___at_pt__transform__2___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_pt__transform__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Geo_SymmetryBreaking_0__List_get_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_translation__matrix___closed__1;
LEAN_EXPORT lean_object* l___private_Geo_SymmetryBreaking_0__WithBot_unbot_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Geo_SymmetryBreaking_0__List_get_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_827_(lean_object*, lean_object*);
lean_object* l_Fin_cases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l_translation__matrix___closed__2;
LEAN_EXPORT lean_object* l_translation__matrix(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldrTR___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_pt__to__vec___closed__3;
lean_object* l_List_finRange(lean_object*);
static lean_object* l_pt__to__vec___closed__1;
LEAN_EXPORT lean_object* l_Matrix_dotProduct___at_pt__transform__2___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Geo_SymmetryBreaking_0__List_isEmpty_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Matrix_vecCons___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_pt__transform__2___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_pt__transform(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_3 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_4 = lean_apply_2(x_2, x_3, x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_inc(x_5);
x_6 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1157_(x_4, x_5);
x_7 = lean_unsigned_to_nat(1u);
lean_inc(x_2);
x_8 = lean_apply_2(x_2, x_3, x_7);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
lean_inc(x_9);
x_10 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1157_(x_8, x_9);
x_11 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_827_(x_6, x_10);
x_12 = lean_unsigned_to_nat(2u);
lean_inc(x_2);
x_13 = lean_apply_2(x_2, x_3, x_12);
x_14 = l___private_Mathlib_Data_Real_Basic_0__Real_one;
x_15 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1157_(x_13, x_14);
x_16 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_827_(x_11, x_15);
lean_inc(x_2);
x_17 = lean_apply_2(x_2, x_7, x_3);
x_18 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1157_(x_17, x_5);
lean_inc(x_2);
x_19 = lean_apply_2(x_2, x_7, x_7);
x_20 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1157_(x_19, x_9);
x_21 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_827_(x_18, x_20);
x_22 = lean_apply_2(x_2, x_7, x_12);
x_23 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1157_(x_22, x_14);
x_24 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_827_(x_21, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
static lean_object* _init_l_pt__to__vec___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Matrix_vecEmpty___boxed), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_pt__to__vec___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_Mathlib_Data_Real_Basic_0__Real_one;
x_3 = l_pt__to__vec___closed__1;
x_4 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_pt__to__vec___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_pt__to__vec___closed__2;
x_3 = l_pt__to__vec___closed__1;
x_4 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_pt__to__vec(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_pt__to__vec___closed__1;
x_7 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_4);
lean_closure_set(x_7, 2, x_6);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_9, 0, x_5);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_pt__to__vec___closed__3;
x_12 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_9);
lean_closure_set(x_12, 2, x_11);
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Fin_cases(x_13, lean_box(0), x_7, x_12, x_2);
lean_dec(x_7);
x_15 = lean_apply_1(x_14, x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_pt__to__vec___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_pt__to__vec(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_vec__to__pt(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_3 = lean_apply_2(x_1, x_2, x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_apply_2(x_1, x_4, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
static lean_object* _init_l_Multiset_sum___at_pt__transform__2___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_827_), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Multiset_sum___at_pt__transform__2___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Multiset_sum___at_pt__transform__2___spec__3___closed__1;
x_3 = l___private_Mathlib_Data_Real_Basic_0__Real_zero;
x_4 = l_List_foldrTR___rarg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Finset_sum___at_pt__transform__2___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Multiset_map___rarg(x_2, x_1);
x_4 = lean_alloc_closure((void*)(l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_827_), 2, 0);
x_5 = l___private_Mathlib_Data_Real_Basic_0__Real_zero;
x_6 = l_List_foldrTR___rarg(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Matrix_dotProduct___at_pt__transform__2___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_3);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_1(x_2, x_3);
x_6 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1157_(x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Matrix_dotProduct___at_pt__transform__2___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_List_finRange(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Matrix_dotProduct___at_pt__transform__2___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Matrix_dotProduct___at_pt__transform__2___spec__1___lambda__1), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = l_Matrix_dotProduct___at_pt__transform__2___spec__1___closed__1;
x_5 = l_Finset_sum___at_pt__transform__2___spec__2(x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_pt__transform__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_pt__to__vec(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_pt__transform__2___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_apply_1(x_1, x_3);
x_6 = lean_alloc_closure((void*)(l_pt__transform__2___lambda__1___boxed), 3, 2);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_4);
x_7 = l_Matrix_dotProduct___at_pt__transform__2___spec__1(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_pt__transform__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_pt__transform__2___lambda__2), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
x_4 = l_vec__to__pt(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_pt__transform__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_pt__transform__2___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_transform__points___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_8 = l_pt__transform(x_6, x_1);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_8);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
x_12 = l_pt__transform(x_10, x_1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_transform__points(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_List_mapTR_loop___at_transform__points___spec__1(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Geo_SymmetryBreaking_0__List_isEmpty_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_3, x_4, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Geo_SymmetryBreaking_0__List_isEmpty_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Geo_SymmetryBreaking_0__List_isEmpty_match__1_splitter___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Geo_SymmetryBreaking_0__List_isEmpty_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Geo_SymmetryBreaking_0__List_isEmpty_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_translation__matrix___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l___private_Mathlib_Data_Real_Basic_0__Real_zero;
x_3 = l_pt__to__vec___closed__2;
x_4 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_translation__matrix___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l___private_Mathlib_Data_Real_Basic_0__Real_zero;
x_3 = l_translation__matrix___closed__1;
x_4 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_translation__matrix___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_translation__matrix___closed__2;
x_3 = l_pt__to__vec___closed__1;
x_4 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_translation__matrix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_pt__to__vec___closed__1;
x_7 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_1);
lean_closure_set(x_7, 2, x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = l___private_Mathlib_Data_Real_Basic_0__Real_zero;
x_10 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_9);
lean_closure_set(x_10, 2, x_7);
x_11 = lean_unsigned_to_nat(2u);
x_12 = l___private_Mathlib_Data_Real_Basic_0__Real_one;
x_13 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
lean_closure_set(x_13, 2, x_10);
x_14 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_14, 0, x_5);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_6);
x_15 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_15, 0, x_8);
lean_closure_set(x_15, 1, x_12);
lean_closure_set(x_15, 2, x_14);
x_16 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_16, 0, x_11);
lean_closure_set(x_16, 1, x_9);
lean_closure_set(x_16, 2, x_15);
x_17 = l_translation__matrix___closed__3;
x_18 = lean_alloc_closure((void*)(l_Matrix_vecCons___rarg___boxed), 4, 3);
lean_closure_set(x_18, 0, x_8);
lean_closure_set(x_18, 1, x_16);
lean_closure_set(x_18, 2, x_17);
x_19 = l_Fin_cases(x_11, lean_box(0), x_13, x_18, x_3);
lean_dec(x_13);
x_20 = lean_apply_1(x_19, x_4);
return x_20;
}
}
LEAN_EXPORT lean_object* l_translation__matrix___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_translation__matrix(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Geo_SymmetryBreaking_0__WithBot_unbot_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_4);
x_5 = lean_apply_1(x_3, lean_box(0));
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_2(x_4, x_6, lean_box(0));
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Geo_SymmetryBreaking_0__WithBot_unbot_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Geo_SymmetryBreaking_0__WithBot_unbot_match__1_splitter___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Geo_SymmetryBreaking_0__List_get_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_2, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_2, x_9);
x_11 = lean_apply_4(x_4, x_5, x_6, x_10, lean_box(0));
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_4);
x_12 = lean_apply_3(x_3, x_5, x_6, lean_box(0));
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Geo_SymmetryBreaking_0__List_get_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Geo_SymmetryBreaking_0__List_get_match__1_splitter___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Geo_SymmetryBreaking_0__List_get_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Geo_SymmetryBreaking_0__List_get_match__1_splitter___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_List_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Matrix_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_Algebra_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Geo_PlaneGeometry(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Geo_SymmetryBreaking(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_List_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Matrix_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_Algebra_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Geo_PlaneGeometry(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_pt__to__vec___closed__1 = _init_l_pt__to__vec___closed__1();
lean_mark_persistent(l_pt__to__vec___closed__1);
l_pt__to__vec___closed__2 = _init_l_pt__to__vec___closed__2();
lean_mark_persistent(l_pt__to__vec___closed__2);
l_pt__to__vec___closed__3 = _init_l_pt__to__vec___closed__3();
lean_mark_persistent(l_pt__to__vec___closed__3);
l_Multiset_sum___at_pt__transform__2___spec__3___closed__1 = _init_l_Multiset_sum___at_pt__transform__2___spec__3___closed__1();
lean_mark_persistent(l_Multiset_sum___at_pt__transform__2___spec__3___closed__1);
l_Matrix_dotProduct___at_pt__transform__2___spec__1___closed__1 = _init_l_Matrix_dotProduct___at_pt__transform__2___spec__1___closed__1();
lean_mark_persistent(l_Matrix_dotProduct___at_pt__transform__2___spec__1___closed__1);
l_translation__matrix___closed__1 = _init_l_translation__matrix___closed__1();
lean_mark_persistent(l_translation__matrix___closed__1);
l_translation__matrix___closed__2 = _init_l_translation__matrix___closed__2();
lean_mark_persistent(l_translation__matrix___closed__2);
l_translation__matrix___closed__3 = _init_l_translation__matrix___closed__3();
lean_mark_persistent(l_translation__matrix___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
