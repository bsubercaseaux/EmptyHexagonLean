import Geo.Orientations

namespace Geo

def RevLexMid (F : Fin n → Prop) (a b : Fin n) (acc : Prop) : Prop :=
  if h : a < b then
    RevLexMid F
        ⟨a + 1, Nat.lt_of_le_of_lt h b.2⟩
        ⟨b - 1, Nat.lt_of_le_of_lt (Nat.sub_le ..) b.2⟩ <|
      (F a ∧ ¬F b) ∨ (F b → F a) ∧ acc
  else
    acc

theorem RevLexMid_total (F : Fin n → Prop) (hb : b = a.rev) (H : acc ∨ acc') :
    RevLexMid F a b acc ∨ RevLexMid (F ·.rev) a b acc' := by
  unfold RevLexMid; split <;> [rename_i h; exact H]
  apply RevLexMid_total
  · simp [Fin.rev, hb]; omega
  · subst hb; simp
    by_cases F a <;> by_cases F (Fin.rev a) <;> simp [*]

def RevLexMid3 (F : Fin n → Fin n → Fin n → Prop) : Prop :=
  ∀ h : 3 ≤ n,
    RevLexMid (n := n - 2) ⟨0, by omega⟩ ⟨n-3, by omega⟩ True
      (F := fun ⟨i, _⟩ => F ⟨i, by omega⟩ ⟨i+1, by omega⟩ ⟨i+2, by omega⟩)

theorem RevLexMid3_total (F : Fin n → Fin n → Fin n → Prop) :
    RevLexMid3 F ∨ RevLexMid3 fun a b c => F c.rev b.rev a.rev := by
  by_cases h : 3 ≤ n <;> [skip; exact .inl (h.elim ·)]
  cases RevLexMid_total
    (n := n - 2) (a := ⟨0, by omega⟩) (b := ⟨n-3, by omega⟩) (acc := True) (acc' := True)
    (F := fun ⟨i, _⟩ => F ⟨i, by omega⟩ ⟨i+1, by omega⟩ ⟨i+2, by omega⟩)
    (by simp [Fin.rev]; omega)
    (.inl trivial)
  with
  | inl H => exact .inl fun _ => H
  | inr H =>
    refine .inr fun _ => ?_
    convert H; split; rename_i i hi
    simp [Fin.rev]; apply Iff.of_eq; congr 2 <;> omega

def σRevLex (l : List Point) : Prop :=
  RevLexMid3 fun a b c : Fin l.length => σ l[a] l[b] l[c] = .ccw

def flipX (pt : Point) : Point := ![-pt.x, pt.y]

theorem σ_flipX : σ (flipX a) (flipX b) (flipX c) = -σ a b c := by
  simp [flipX, σ, Point.det_eq, ← Orientation.ofReal_neg]
  congr 1; ring

theorem σRevLex_total (l : List Point) : σRevLex l ∨ σRevLex (l.reverse.map flipX) := by
  unfold σRevLex
  refine (RevLexMid3_total _).imp_right fun h => ?_
  have get_eq_getD := fun l i hn => (List.getD_eq_get (α := Point) (d := 0) (n := i) l hn).symm
  simp [List.getElem_eq_get, get_eq_getD] at h ⊢
  generalize e1 : l.length = n at h
  generalize e2 : (l.reverse.map flipX).length = n' at h
  simp [e1] at e2; subst n'
  with_reducible convert h using 5
  simp [List.getD_eq_get, List.get_reverse'', Fin.isLt, e1]
  simp [Fin.rev, get_eq_getD, e1, σ_flipX]
  rw [σ_perm₂, σ_perm₁, σ_perm₂, neg_neg, neg_neg]
