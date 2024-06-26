import Std.Data.List.Lemmas
import Geo.Definitions.Orientations
import Geo.Definitions.SigmaEquiv

namespace Geo
open scoped List

structure σEmbed (S T : List Point) where
  f : Point → Point
  perm : S.map f ~ T
  parity : Bool := false
  σ_eq : ∀ p q r, p ∈ S → q ∈ S → r ∈ S → σ (f p) (f q) (f r) = parity ^^^ σ p q r

infix:50 " ≼σ " => σEmbed

namespace σEmbed

theorem mem_iff (σ : S ≼σ T) : y ∈ T ↔ ∃ x ∈ S, σ.f x = y :=
  σ.perm.mem_iff.symm.trans (by simp)

theorem mem (σ : S ≼σ T) (h : x ∈ S) : σ.f x ∈ T := σ.mem_iff.2 ⟨_, h, rfl⟩

def permRight (σ : S ≼σ T) (h : T ~ T') : S ≼σ T' :=
  { σ with perm := σ.perm.trans h }

def permLeft (σ : S ≼σ T) (h : S ~ S') : S' ≼σ T :=
  { σ with perm := (h.symm.map _).trans σ.perm, σ_eq := by simpa [h.symm.mem_iff] using σ.σ_eq }

def range (σ : S ≼σ T) : List Point := S.map σ.f

theorem length_eq (σ : S ≼σ T) : S.length = T.length := by simp [← σ.perm.length_eq]

def refl (S : List Point) : S ≼σ S := ⟨id, by simp, false, by simp⟩

def trans (f : S ≼σ T) (g : T ≼σ U) : S ≼σ U := by
  refine ⟨g.f ∘ f.f, ?_, xor f.parity g.parity, fun p q r hp hq hr => ?_⟩
  · simpa using (f.perm.map _).trans g.perm
  · simp [f.σ_eq _ _ _ hp hq hr, g.σ_eq _ _ _ (f.mem hp) (f.mem hq) (f.mem hr), Bool.xor_comm]

theorem nodup_of (e : S ≼σ T) : T.Nodup → S.Nodup :=
  fun h => List.Nodup.of_map _ (e.perm.nodup_iff.mpr h)

open Classical

theorem bijOn (f : S ≼σ T) (h : T.Nodup) : Set.BijOn f.f S.toFinset T.toFinset := by
  refine ⟨?_, ?_, ?_⟩
  . intro a ha
    simp only [List.coe_toFinset, Set.mem_setOf_eq] at ha ⊢
    apply f.mem_iff.mpr
    use a, ha
  . intro a ha b hb eq
    simp only [List.coe_toFinset, Set.mem_setOf_eq] at ha hb
    by_contra ne
    exact (List.pairwise_map.1 (f.perm.nodup_iff.2 h)).forall (fun _ _ => Ne.symm) ha hb ne eq
  · intro b hb
    simp only [List.coe_toFinset, Set.mem_setOf_eq] at hb ⊢
    exact f.mem_iff.1 hb

noncomputable def toEquiv (f : S ≼σ T) (h : T.Nodup) : S.toFinset ≃σ T.toFinset where
  f := f.f
  bij' := f.bijOn h
  parity := f.parity
  σ_eq' := by
    intro _ ha _ hb _ hc
    simp only [List.coe_toFinset, Set.mem_setOf_eq] at ha hb hc
    simp [f.σ_eq _ _ _ ha hb hc]

end σEmbed

def OrientationProperty' (P : List Point → Prop) :=
  ∀ {{S T}}, S ≼σ T → (P S ↔ P T)

theorem OrientationProperty'.not : OrientationProperty' P → OrientationProperty' (¬P ·) :=
  fun h _ _ hσ => not_congr (h hσ)

theorem OrientationProperty'.gp : OrientationProperty' Point.ListInGenPos := fun S T f => by
  rw [← Point.ListInGenPos.perm f.perm]
  simp only [Point.ListInGenPos, ← List.mem_sublists, List.sublists_map]
  simp [Point.InGenPos₃.iff_ne_collinear, -IsEmpty.forall_iff]
  constructor
  · intro | H, _, _, _, [p',q',r'], sl, rfl => ?_
    have := sl.subset; simp at this
    rw [f.σ_eq _ _ _ this.1 this.2.1 this.2.2]
    simp [H sl]
  · intro H p q r sl
    have := sl.subset; simp at this
    rw [← Orientation.xor_eq_collinear f.parity, ← f.σ_eq _ _ _ this.1 this.2.1 this.2.2]; exact H _ sl rfl
