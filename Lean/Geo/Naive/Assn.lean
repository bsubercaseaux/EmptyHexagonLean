import Geo.Definitions.CanonicalPoints
import Geo.Definitions.PtInTriangle
import Geo.Definitions.Structures
import Geo.Definitions.OrientationProperties
import Geo.Orientations
import Geo.Naive.Encoding
import Geo.KGon.Assn

namespace Geo.CanonicalPoints
open List Classical Point
attribute [-simp] getElem_fin

def isKHole1 (w : CanonicalPoints) (s : Finset (Fin w.length)) (b c : Fin w.length) :=
  ∀ᵉ (a ∈ s), a < b → σIsEmptyTriangleFor w[a] w[b] w[c] w.toFinset

def isKHole2 (w : CanonicalPoints) (s : Finset (Fin w.length)) (c : Fin w.length) :=
  ∀ᵉ (b ∈ s), b < c → isKHole1 w s b c

def isKHole (w : CanonicalPoints) (s : Finset (Fin w.length)) := ∀ᵉ (c ∈ s), isKHole2 w s c

theorem satisfies_noKHoleClausesCore {w : CanonicalPoints}
    {k i G1 G2} (T : Finset (Fin w.length)) (hh : isKHole w T)
    (hT1 : ∀ x ∈ T, x.1 ≤ i)
    (hs : ∀ s, s.card = k → (∀ x ∈ s, i < x.1) → ¬isKHole w (T ∪ s))
    (hG1 : ∀ b c, i ≤ b.1 → b < c → (G1 b c).eval w.toPropAssn → isKHole1 w T b.succ c.succ)
    (hG2 : ∀ c, i ≤ c.1 → (G2 c).eval w.toPropAssn → isKHole2 w T c.succ) :
    (noKHoleClausesCore w.rlen k i G1 G2).eval w.toPropAssn := by
  rw [noKHoleClausesCore]; split_ifs with k0
  · simp; intro hi
    constructor
    · intro h1
      let i' : Fin w.rlen := ⟨i, hi⟩
      refine satisfies_noKHoleClausesCore (insert i'.succ T) ?_ ?_ (fun s sz hs' => ?_) ?_ ?_
      · intro c hc b hb bc a ha ab
        simp (config := {zeta := false}) at ha hb hc
        have : c ≤ i'.succ := by obtain rfl | hc := hc <;> [rfl; exact Nat.le_succ_of_le (hT1 _ hc)]
        have ha := ha.resolve_left <| ne_of_lt <| lt_of_lt_of_le (ab.trans bc) this
        have hb' := lt_of_lt_of_le bc this
        have hb := hb.resolve_left <| ne_of_lt hb'
        obtain rfl | hc := hc
        · exact hG2 i' le_rfl h1 b hb hb' a ha ab
        · exact hh _ hc _ hb bc _ ha ab
      · simp; exact fun x hx => Nat.le_succ_of_le (hT1 _ hx)
      · rw [Finset.insert_union, ← Finset.union_insert]
        apply hs
        · rw [Finset.card_insert_of_not_mem, sz, Nat.sub_add_cancel k0]
          exact fun h => lt_irrefl _ (hs' _ h)
        · simp; exact fun x hx => Nat.le_of_lt (hs' _ hx)
      · simp (config := {zeta := false}); intro b c ib bc h1 h2 a ha ab
        obtain rfl | ha := Finset.mem_insert.1 ha
        · exact h1
        · exact hG1 b c (Nat.le_of_lt ib) bc h2 _ ha ab
      · simp (config := {zeta := false}); intro c ic h1 h2 b hb bc a ha ab
        simp (config := {zeta := false}) at ha hb
        have : b ≤ i'.succ := by obtain rfl | hb := hb <;> [rfl; exact Nat.le_succ_of_le (hT1 _ hb)]
        have ha := ha.resolve_left <| ne_of_lt <| lt_of_lt_of_le ab this
        obtain rfl | hb := hb
        · exact hG1 i' _ le_rfl ic h1 _ ha ab
        · exact hG2 _ (Nat.le_of_lt ic) h2 _ hb bc _ ha ab
    · exact satisfies_noKHoleClausesCore T hh
        (fun x hx => Nat.le_succ_of_le (hT1 _ hx))
        (fun s sz hs' => hs _ sz fun x hx => Nat.le_of_lt (hs' _ hx))
        (fun b c ib => hG1 _ _ (Nat.le_of_lt ib))
        (fun c ic => hG2 _ (Nat.le_of_lt ic))
  · simp at k0; simp [k0, hh] at hs
termination_by w.rlen - i
decreasing_by all_goals decreasing_with omega

theorem satisfies_naiveEncoding (w : CanonicalPoints) (k : Nat) :
    ¬σHasEmptyKGon k w.toFinset →
    (naiveEncoding k w.rlen).eval w.toPropAssn := by
  simp [naiveEncoding, satisfies_baseEncoding, satisfies_signotopeClauses2,
    satisfies_holeDefClauses0, noKHoleClauses]
  intro noholes k0
  have (s) (hs : s.card = k) : ¬isKHole w s := fun hn => by
    refine noholes ⟨s.map ⟨(w[·]), fun i j => w.eq_iff'.1⟩, by simp [hs], ?_⟩
    simp [Set.subset_def, w.mem_toFinset_iff, w.eq_iff']
    intro a ha b hb c hc ab ac bc
    have nd : Nodup [a, b, c] := by simp [*]
    have : ∀ x ∈ [a, b, c], x ∈ s := by simp [*]
    have ⟨l, lp, ls⟩ : ∃ l : List _, l.Perm [a, b, c] ∧ l.Sorted (· < ·) :=
      ⟨[a,b,c].mergeSort (· ≤ ·), perm_mergeSort ..,
        (sorted_mergeSort ..).imp₂ (fun _ _ => lt_of_le_of_ne) ((perm_mergeSort ..).nodup_iff.2 nd)⟩
    have : ∀ x ∈ l, x ∈ s := fun x h => this _ (lp.subset h)
    match l, lp.length_eq with | [a', b', c'], _ => ?_
    simp at ls this
    exact (σIsEmptyTriangleFor.perm (lp.map (w[·]))).1 <|
      hn _ this.2.2 _ this.2.1 ls.2 _ this.1 ls.1.1
  constructor
  · apply satisfies_noKHoleClausesCore {0} ?_ (by simp) (fun s sz hs => this _ ?_)
    · simp [isKHole1]
    · simp [isKHole2, isKHole1]
    · simp [isKHole, isKHole1, isKHole2]
    · rw [← Finset.insert_eq, Finset.card_insert_of_not_mem, sz, Nat.sub_add_cancel k0]
      exact fun h => lt_irrefl _ (hs _ h)
  · apply satisfies_noKHoleClausesCore ∅ ?_ (by simp) (fun s hs => by simp [this _ hs])
    · simp [isKHole1]
    · simp [isKHole2, isKHole1]
    · simp [isKHole]

end CanonicalPoints
