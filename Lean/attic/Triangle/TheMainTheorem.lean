import Geo.PointsToWB.SymmetryBreakingNew
import Geo.Definitions.SigmaEquiv
import Geo.Definitions.OrientationProperties

import Geo.Triangle.WBAssn
import Geo.Triangle.Encoding

namespace Geo

def HasEmptyTriangle : Set Point → Prop := HasEmptyKGon 3

theorem HasEmptyTriangle.iff (S : Set Point) :
    HasEmptyTriangle S ↔
    ∃ᵉ (a ∈ S) (b ∈ S) (c ∈ S), Point.InGenPos₃ a b c ∧
      ∀ s ∈ S \ {a,b,c}, ¬PtInTriangle s a b c := by
  simp [HasEmptyTriangle, HasEmptyKGon, PtInTriangle]
  constructor
  · intro ⟨s, h1, h2, h3, h4⟩
    match s, s.exists_mk with | _, ⟨[a,b,c], h1, rfl⟩ => ?_
    have s_eq : (Finset.mk (Multiset.ofList [a,b,c]) h1 : Set _) = {a, b, c} := by ext; simp
    simp [not_or, Set.subset_def] at h1 h2 h3 ⊢
    refine ⟨a, h2.1, b, h2.2.1, c, h2.2.2, ConvexIndep.triangle_iff.1 h3, ?_⟩
    simpa [not_or, EmptyShapeIn, s_eq] using h4
  · intro ⟨a, ha, b, hb, c, hc, h1, h2⟩
    let s : Finset Point := ⟨[a,b,c], by simp [h1.ne₁, h1.ne₂, h1.ne₃]⟩
    have s_eq : s = {a,b,c} := by ext; simp
    refine ⟨s, rfl, ?_, ConvexIndep.triangle_iff.2 h1, ?_⟩
    · simp [Set.subset_def, ha, hb, hc]
    · simpa [s_eq, EmptyShapeIn] using h2

open LeanSAT.Model.PropFun in
theorem EmptyTriangle10TheoremLists (pts : List Point) (gp : Point.PointListInGeneralPosition pts) (h : pts.length = 10) :
    HasEmptyTriangle pts.toFinset := by
  by_contra h'
  have noσtri : ¬σHasEmptyTriangle pts.toFinset := mt (σHasEmptyTriangle_iff_HasEmptyTriangle gp).1 h'
  have ⟨w, ⟨hw⟩⟩ := @symmetry_breaking pts (h ▸ by decide) gp
  have noσtri' : ¬σHasEmptyTriangle w.toFinset :=
    OrientationProperty_σHasEmptyTriangle.not (hw.toEquiv w.nodup) noσtri
  have len10 : w.length = 10 := hw.length_eq.symm.trans h
  have := cnfUnsat
  rw [LeanSAT.Encode.VEncCNF.toICnf_equisatisfiable, ← len10] at this
  apply this
  exact ⟨_, w.satisfies_noHoles noσtri'⟩

/- 'Geo.EmptyTriangle10TheoremLists' depends on axioms: [propext, Classical.choice, Quot.sound, Geo.cnfUnsat] -/
#print axioms EmptyTriangle10TheoremLists
