import Geo.Definitions.CanonicalPoints
import Geo.Definitions.PtInTriangle
import Geo.Definitions.Structures
import Geo.Definitions.OrientationProperties
import Geo.Definitions.Orientations
import Geo.Gon.Encoding
import Geo.KGon.Assn
import Geo.KGon.Arc

namespace Geo.CanonicalPoints
open List Classical Point
attribute [-simp] getElem_fin

theorem isArc.exists_arc {w : CanonicalPoints} {a b c : Fin w.rlen}
    (ab : a < b) (bc : b < c) (H : isArc w o sz a b c) :
    ∃ l, l.length = sz ∧ Arc w o (a.succ :: l ++ [b.succ, c.succ]) := by
  match sz, H with
  | 0, H => exact ⟨[], rfl, .cons ab.succ₂ H (.one bc.succ₂)⟩
  | l+1, ⟨bc, d, ad, db, h1, h2⟩ =>
    let ⟨l, eq, h1'⟩ := h1.exists_arc ad db
    exact ⟨_, by simp [eq], .concat h1' bc h2⟩

theorem satisfies_arc2 {w : CanonicalPoints} {a b : Fin w.rlen}
    (ab : a < b) (H : (arc2 o sz a b).eval (w.toPropAssn false)) :
    ∃ l, l.length = sz ∧ Arc w o (a.succ :: l ++ [b.succ]) := by
  unfold arc2 at H; split at H
  · exact ⟨[], rfl, .one ab.succ₂⟩
  · simp at H; let ⟨c, ⟨ac, cb⟩, H'⟩ := H
    have ac : a < c := Nat.lt_of_le_of_lt (Nat.le_add_right ..) ac
    have ⟨l, eq, hl⟩ := ((eval_arc _ ac cb).1 H').exists_arc ac cb
    exact ⟨l ++ [c.succ], by simp [eq], by simpa using hl⟩

theorem satisfies_noKGon2Arc {w : CanonicalPoints}
    (H : ∀ a b : Fin w.rlen, ∀ l1 l2, l1.length = sz1 → l2.length = sz2 →
      Arc w .ccw (a.succ :: l1 ++ [b.succ]) → ¬Arc w .cw (a.succ :: l2 ++ [b.succ])) :
    (noKGon2Arc w.rlen sz1 sz2).eval (w.toPropAssn false) := by
  simp [noKGon2Arc]; intro a b ab h1 h2
  have ab : a < b := Nat.lt_of_le_of_lt (Nat.le_add_right ..) (Nat.add_assoc .. ▸ ab)
  have ⟨l1, h11, h12⟩ := satisfies_arc2 ab h1
  have ⟨l2, h21, h22⟩ := satisfies_arc2 ab h2
  exact H _ _ _ _ h11 h21 h12 h22

theorem hasConvex_of_σCCWPoints {w : CanonicalPoints} {l : List (Fin w.length)} (k3 : 3 ≤ k)
    (H : σCCWPoints (l.map (w[·]))) (eq : l.length = k) : σHasConvexKGon k w.toFinset := by
  refine (σHasConvexKGon_iff_HasConvexKGon w.gp).2
    ⟨(l.map (w[·])).toFinset, Eq.trans ?_ eq, ?_, H.convex⟩
  · show List.length _ = _; rw [dedup_eq_self.2, length_map]
    apply H.gp.nodup; rwa [length_map, eq]
  · simp [mem_points_iff]

theorem satisfies_gonEncoding (w : CanonicalPoints) (k : Nat) :
    ¬σHasConvexKGon k w.toFinset →
    (gonEncoding k w.rlen).eval (w.toPropAssn false) := by
  simp [gonEncoding, satisfies_baseEncoding, satisfies_signotopeClauses2,
    satisfies_arcDefClausesUpTo, noGonClauses]
  intro noholes k0
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' k0
  rw [show k+3-3 = k by rfl, show k+3-2 = k+1 by rfl]
  refine ⟨?_, fun ⟨sz1, hsz⟩ => ?_⟩ <;> refine satisfies_noKGon2Arc fun a b l1 l2 h1 h2 h3 h4 => ?_
  · have := Arc.join (l₁ := a.succ::l1) (l₂ := []) h3.cons_0 (.one (Nat.succ_pos _))
    exact noholes <| hasConvex_of_σCCWPoints (Nat.le_add_left ..) this (by simp [h1])
  · exact noholes <| hasConvex_of_σCCWPoints (Nat.le_add_left ..) (Arc.join h3 h4)
      (by simp [h1, h2]; omega)

end CanonicalPoints
