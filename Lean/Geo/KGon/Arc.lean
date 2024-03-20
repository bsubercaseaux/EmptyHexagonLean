import Geo.Definitions.CanonicalPoints
import Geo.Definitions.OrientationProperties

namespace Geo
open List CanonicalPoints

attribute [-simp] getElem_fin

inductive Arc (w : CanonicalPoints) (o : Orientation) : List (Fin w.length) → Prop where
  | one : a < b → Arc w o [a, b]
  | cons : a < b → σ w[a] w[b] w[c] = o → Arc w o (b::c::l) → Arc w o (a::b::c::l)

theorem Arc.one' {w o} {a b : Fin w.rlen} (h : a < b) : Arc w o [a.succ, b.succ] := .one h.succ₂

theorem Arc.cons' {w o} {a b c : Fin w.rlen} {l} (h1 : a < b) (h2 : σ w+[a] w+[b] w+[c] = o) :
    Arc w o (b.succ::c.succ::l) → Arc w o (a.succ::b.succ::c.succ::l) :=
  .cons h1.succ₂ h2

theorem Arc.concat {w o} {a : Fin w.length} {b c : Fin w.rlen}
    {l} (h1 : Arc w o (l ++ [a, b.succ])) (bc : b < c) (h2 : σ w[a] w+[b] w+[c] = o) :
    Arc w o (l ++ [a] ++ [b.succ, c.succ]) := by
  generalize eq : l ++ [a, b.succ] = l' at h1
  induction h1 generalizing l with
  | one ab =>
    cases l <;> [cases eq; simpa using congrArg List.length eq]
    exact .cons ab h2 (.one bc.succ₂)
  | cons ab abc h IH =>
    cases l <;> [cases eq; injection eq with eq1 eq]
    subst eq1; specialize IH eq
    rename_i x l
    match l with
    | [] | [_] | _::_::_ => cases eq; exact .cons ab abc IH

theorem Arc.sorted (H : Arc w o l) : l.Sorted (·<·) := by
  apply chain'_iff_pairwise.1
  induction H with
  | one ab => simp [*]
  | cons ab _ _ IH => exact .cons ab IH

theorem Arc.head_lt (H : Arc w o (a::b::l)) : a < b := by
  have := H.sorted; simp at this; simp [this]

theorem Arc.cons_0 {a : Fin w.rlen}
    (H : Arc w .ccw (a.succ :: l)) : Arc w .ccw (0 :: a.succ :: l) := by
  cases l with | nil => cases H | cons b l => ?_
  obtain rfl | ⟨b, rfl⟩ := b.eq_zero_or_eq_succ
  · cases H.head_lt
  · exact .cons (Nat.succ_pos _) (w.σ_0 (Fin.succ_lt_succ_iff.1 H.head_lt)) H

theorem Arc.pairwise {a b c : Fin w.length} (ab : a < b) (abc : σ w[a] w[b] w[c] = o)
    (H : Arc w o (b::c::l)) : (b::c::l).Pairwise (σ w[a] w[·] w[·] = o) := by
  generalize eq : b::c::l = l' at H ⊢
  induction H generalizing b c l with cases eq
  | one _ => simp [abc]
  | @cons b c d l bc bcd h IH =>
    have .cons ce de := h.sorted; have cd := ce _ (.head _)
    have sorted := w.sorted₄ ab bc cd; have gp := w.gp₄ ab bc cd
    match o with
    | .collinear => cases (w.gp₃ ab bc).σ_ne abc
    | .ccw =>
      have IH := IH (ab.trans bc) (σ_prop₁ sorted gp abc bcd) rfl
      refine .cons ?_ IH; let .cons IH1 IH2 := IH
      refine forall_mem_cons.2 ⟨abc, fun e he => ?_⟩
      exact σ_prop₂ (w.sorted₄ ab bc (ce _ he)) (w.gp₄ ab bc (ce _ he)) abc (IH1 _ he)
    | .cw =>
      have IH := IH (ab.trans bc) (σ_prop₃ sorted gp abc bcd) rfl
      refine .cons ?_ IH; let .cons IH1 IH2 := IH
      refine forall_mem_cons.2 ⟨abc, fun e he => ?_⟩
      exact σ_prop₄ (w.sorted₄ ab bc (ce _ he)) (w.gp₄ ab bc (ce _ he)) abc (IH1 _ he)

theorem Arc.ccw (H : Arc w .ccw l) : σCCWPoints (l.map (w[·])) := by
  induction H with
  | one _ => simp [σCCWPoints]
  | @cons a b c l ab abc h IH => exact ⟨pairwise_map.2 (h.pairwise ab abc), IH⟩

theorem Arc.cw (H : Arc w .cw l) : σCCWPoints (l.reverse.map (w[·])) := by
  induction H with
  | one _ => simp [σCCWPoints]
  | @cons a b c l ab abc h IH =>
    rw [reverse_cons, map_append, σCCWPoints_append]
    refine ⟨IH, ?_⟩; simp [σCCWPoints, pairwise_map, pairwise_append, pairwise_reverse]
    have := (h.pairwise ab abc).imp fun {b c} h => show σ w[c] w[b] w[a] = .ccw by
      rw [σ_perm₁, ← σ_perm₂, σ_perm₁, h]; rfl
    simp at this; simp (config := {contextual := true}) [this]

theorem Arc.join (H1 : Arc w .ccw (a::l₁++[b])) (H2 : Arc w .cw (a::l₂++[b])) :
    σCCWPoints ((a::l₁++b::l₂.reverse).map (w[·])) := by
  have C1 := H1.ccw; have C2 := H2.cw
  have S1 := H1.sorted; have S2 := H2.sorted; simp [Sorted, -cons_append, pairwise_append] at S1 S2
  rw [show reverse (a :: l₂ ++ [b]) = b :: reverse l₂ ++ [a] by simp] at C2
  rw [map_append, σCCWPoints_append] at C1 C2 ⊢
  refine ⟨C1.1, C2.1, ?_⟩
  simp only [σCCWPoints, pairwise_map, Pairwise.nil, map_cons, mem_cons,
    mem_map, pairwise_cons, not_mem_nil, IsEmpty.forall_iff, implies_true,
    mem_singleton, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, true_and,
    pairwise_reverse, mem_reverse, forall_eq_or_imp, and_true] at C1 C2 ⊢
  obtain ⟨⟨A1, -⟩, A3, A4⟩ := C1; obtain ⟨⟨B1, -⟩, B3, B4⟩ := C2
  have ne {c e} (hc : c ∈ l₁) (he : e ∈ l₂) : c ≠ e := by
    rintro rfl; have := A3 _ hc; rw [σ_perm₁, ← σ_perm₂, σ_perm₁, B3 _ he] at this; cases this
  have O {c e} (hc : c ∈ l₁) (he : e ∈ l₂) : σ w[a] w[c] w[e] = .ccw ∧ σ w[c] w[b] w[e] = .ccw := by
    obtain ce | ec := lt_or_gt_of_ne (ne hc he)
    · have sorted := w.sorted₄ (S1.1.1 _ hc) ce (S2.2.2 _ he)
      have gp := w.gp₄ (S1.1.1 _ hc) ce (S2.2.2 _ he)
      constructor
      · rw [gp.gp₁.σ_iff'.1 fun h => ?_]
        have := σ_prop₄ sorted gp h (by rw [σ_perm₁, ← σ_perm₂, σ_perm₁, B3 _ he]; rfl)
        rw [A3 _ hc] at this; cases this
      · rw [σ_perm₂, gp.gp₄.σ_iff.1 fun h => ?_]; rfl
        have := σ_prop₂' sorted gp (A3 _ hc) h
        rw [σ_perm₁, ← σ_perm₂, σ_perm₁, B3 _ he] at this; cases this
    · have sorted := w.sorted₄ (S2.1.1 _ he) ec (S1.2.2 _ hc)
      have gp := w.gp₄ (S2.1.1 _ he) ec (S1.2.2 _ hc)
      constructor
      · rw [σ_perm₂, gp.gp₁.σ_iff.1 fun h => ?_]; rfl
        have := σ_prop₂ sorted gp h (A3 _ hc)
        rw [σ_perm₁, ← σ_perm₂, σ_perm₁, B3 _ he] at this; cases this
      · rw [σ_perm₂, ← σ_perm₁, gp.gp₄.σ_iff'.1 fun h => ?_]
        have := σ_prop₄' sorted gp (by rw [σ_perm₁, ← σ_perm₂, σ_perm₁, B3 _ he]; rfl) h
        rw [A3 _ hc] at this; cases this
  refine ⟨⟨⟨fun e he => ?_, B4.imp <| Eq.trans (by rw [σ_perm₁, ← σ_perm₂])⟩,
    fun c hc => ⟨fun e he => (O hc he).2, ?_⟩⟩, ⟨A3, A4⟩,
    fun e he => ⟨fun c hc => (O hc he).1, ?_⟩⟩
  · rw [σ_perm₁, ← σ_perm₂, B3 _ he]
  · refine (Pairwise.and_mem.1 <| S2.1.2.and B1).imp₂ (fun e f ⟨he, hf, ef, bfe⟩ aef => ?_) B4
    rw [σ_perm₁, ← σ_perm₂, σ_perm₁] at aef
    have ⟨acf, cbf⟩ := O hc hf
    obtain ce | ec := lt_or_gt_of_ne (ne hc he)
    · have sorted := w.sorted₄ (S1.1.1 _ hc) ce ef
      have gp := w.gp₄ (S1.1.1 _ hc) ce ef
      rw [σ_perm₂, gp.gp₄.σ_iff.1 fun h => ?_]; rfl
      rw [σ_prop₁ sorted gp (O hc he).1 h] at aef; cases aef
    obtain cf | fc := lt_or_gt_of_ne (ne hc hf)
    · have sorted := w.sorted₄ (S2.1.1 _ he) ec cf
      have gp := w.gp₄ (S2.1.1 _ he) ec cf
      rw [σ_perm₂, ← σ_perm₁, gp.gp₄.σ_iff'.1 fun h => ?_]
      rw [σ_prop₄' sorted gp (neg_inj.1 <| aef ▸ rfl) h] at acf; cases acf
    · have sorted := w.sorted₄ ef fc (S1.2.2 _ hc)
      have gp := w.gp₄ ef fc (S1.2.2 _ hc)
      rw [σ_perm₂, ← σ_perm₁, σ_perm₂, gp.gp₁.σ_iff.1 fun h => ?_]; rfl
      rw [σ_perm₂, ← σ_perm₁, σ_perm₂,
        σ_prop₁' sorted gp h (by rw [σ_perm₁, ← σ_perm₂, cbf])] at bfe; cases bfe
  · refine (Pairwise.and_mem.1 <| S1.1.2.and A1).imp₂ (fun c d ⟨hc, hd, cd, acd⟩ cdb => ?_) A4
    have ⟨ade, dbe⟩ := O hd he
    obtain de | ed := lt_or_gt_of_ne (ne hd he)
    · have sorted := w.sorted₄ cd de (S2.2.2 _ he)
      have gp := w.gp₄ cd de (S2.2.2 _ he)
      rw [gp.gp₁.σ_iff'.1 fun h => ?_]
      rw [σ_prop₃' sorted gp h (by rw [σ_perm₂, dbe]; rfl)] at cdb; cases cdb
    obtain ce | ec := lt_or_gt_of_ne (ne hc he)
    · have sorted := w.sorted₄ (S1.1.1 _ hc) ce ed
      have gp := w.gp₄ (S1.1.1 _ hc) ce ed
      rw [σ_perm₂, gp.gp₄.σ_iff.1 fun h => ?_]; rfl
      rw [σ_perm₂, σ_prop₂' sorted gp acd h] at ade; cases ade
    · have sorted := w.sorted₄ (S2.1.1 _ he) ec cd
      have gp := w.gp₄ (S2.1.1 _ he) ec cd
      rw [σ_perm₂, ← σ_perm₁, gp.gp₄.σ_iff'.1 fun h => ?_]
      rw [σ_prop₃ sorted gp (by rw [σ_perm₂, (O hc he).1]; rfl) h] at acd; cases acd

end Geo
