import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Algebra.Basic
import Geo.Point

namespace Geo

namespace Point

noncomputable def slope (p1 p2 : Point) : Real :=
  (p2.y - p1.y) / (p2.x - p1.x)

theorem slope_lt_iff_lt {a b c : Point} (hS : Sorted₃ a b c) :
    slope a b < slope a c ↔ slope a b < slope b c := by
  unfold slope
  have hab := hS.h₁
  have hbc := hS.h₂
  set dy_ac := c.y - a.y
  set dy_bc := c.y - b.y
  set dy_ab := b.y - a.y
  set dx_ac := c.x - a.x
  set dx_bc := c.x - b.x
  set dx_ab := b.x - a.x

  have decompose_dy_ac : dy_ac = dy_bc + dy_ab := by ring_nf
  have decompose_dx_ac : dx_ac = dx_bc + dx_ab := by ring_nf

  have dx_ab_pos : 0 < dx_ab := by simp; linarith
  have dx_bc_pos : 0 < dx_bc := by simp; linarith
  have dx_ab_dx_bc_pos : 0 < dx_bc + dx_ab := by simp; linarith

  calc
    _ ↔ dy_ab / dx_ab < (dy_bc + dy_ab) / (dx_bc + dx_ab) := by rw [decompose_dy_ac, decompose_dx_ac]
    _ ↔ dy_ab * (dx_bc + dx_ab) < (dy_bc + dy_ab) * dx_ab := by rw [div_lt_div_iff dx_ab_pos dx_ab_dx_bc_pos]
    _ ↔ dy_ab * dx_bc < dy_bc * dx_ab := by rw [mul_add, add_mul]; field_simp
    _ ↔ dy_ab / dx_ab < dy_bc / dx_bc := by rw [div_lt_div_iff dx_ab_pos dx_bc_pos]

theorem slope_lt_iff_lt' {a b c : Point} (hS : Sorted₃ a b c) :
   slope a c < slope b c ↔ slope a b < slope b c := by
    unfold slope
    have hab := hS.h₁
    have hbc := hS.h₂
    set dy_ac := c.y - a.y
    set dy_bc := c.y - b.y
    set dy_ab := b.y - a.y
    set dx_ac := c.x - a.x
    set dx_bc := c.x - b.x
    set dx_ab := b.x - a.x

    have decompose_dy_ac : dy_ac = dy_bc + dy_ab := by ring_nf
    have decompose_dx_ac : dx_ac = dx_bc + dx_ab := by ring_nf

    have dx_ab_pos : 0 < dx_ab := by simp; linarith
    have dx_bc_pos : 0 < dx_bc := by simp; linarith
    have dx_ab_dx_bc_pos : 0 < dx_bc + dx_ab := by simp; linarith
    calc
      _ ↔ (dy_bc + dy_ab) / (dx_bc + dx_ab) < dy_bc / dx_bc := by rw [decompose_dy_ac, decompose_dx_ac]
      _ ↔ (dy_bc + dy_ab) * dx_bc < dy_bc * (dx_bc + dx_ab) := by rw [div_lt_div_iff  dx_ab_dx_bc_pos dx_bc_pos]
      _ ↔ dy_bc * dx_bc + dy_ab * dx_bc < dy_bc * dx_bc + dy_bc * dx_ab := by ring_nf
      _ ↔ dy_ab * dx_bc < dy_bc * dx_ab := by simp
      _ ↔ dy_ab / dx_ab < dy_bc / dx_bc := by rw [div_lt_div_iff dx_ab_pos dx_bc_pos]

  theorem slope_gt_iff_gt {a b c : Point} (hS : Sorted₃ a b c) :
    slope a b > slope a c ↔ slope a b > slope b c := by
    sorry

  theorem slope_gt_iff_gt' {a b c : Point} (hS : Sorted₃ a b c) :
    slope a c > slope b c ↔ slope a b > slope b c := by
    sorry

end Point
