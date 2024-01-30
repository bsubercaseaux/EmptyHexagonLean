// Lean compiler output
// Module: Geo.Point
// Imports: Init Mathlib.Tactic Mathlib.Data.Matrix.Basic Mathlib.Algebra.Algebra.Basic
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
LEAN_EXPORT lean_object* l_determinant__pts(lean_object*, lean_object*, lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1157_(lean_object*, lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1004_(lean_object*, lean_object*);
lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_827_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_determinant__pts(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_5);
lean_inc(x_4);
x_6 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1157_(x_4, x_5);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_8);
lean_inc(x_7);
x_9 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1157_(x_7, x_8);
x_10 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_827_(x_6, x_9);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
lean_inc(x_12);
lean_inc(x_11);
x_13 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1157_(x_11, x_12);
x_14 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_827_(x_10, x_13);
x_15 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1157_(x_12, x_7);
x_16 = lean_alloc_closure((void*)(l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1004_), 2, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_827_(x_14, x_16);
x_18 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1157_(x_5, x_11);
x_19 = lean_alloc_closure((void*)(l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1004_), 2, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_827_(x_17, x_19);
x_21 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1157_(x_8, x_4);
x_22 = lean_alloc_closure((void*)(l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_1004_), 2, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_827_(x_20, x_22);
return x_23;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Matrix_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_Algebra_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Geo_Point(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
