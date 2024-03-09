import Geo.Definitions.WBPoints
import Geo.Definitions.PtInTriangle
import Geo.Definitions.Structures
import Geo.Definitions.OrientationProperties
import Geo.Orientations
import Geo.Hexagon.EncodingNew
import Geo.NGon.WBAssnNew

namespace Geo.WBPoints
open List Classical LeanSAT.Model PropFun Point
attribute [-simp] getElem_fin

theorem satisfies_capDef (w : WBPoints) {a b c d : Fin (length w)}
    (ab : a < b) (bc : b < c) (cd : c < d) : (capDef a b c d).eval w.toPropAssn := by
  simp [capDef, isCap]; intro h1 h2
  exact ⟨_, ab, bc, cd, (w.gp₃ ab bc).σ_iff.1 h1, (w.gp₃ bc cd).σ_iff.1 h2⟩

theorem satisfies_capDef2 (w : WBPoints) {a c d : Fin (length w)} :
    (capDef2 a c d).eval w.toPropAssn := by
  simp [capDef2, isCap]; intro b ab bc cd h1 h2
  have gp := w.gp₄ ab bc cd
  exact gp.gp₃.σ_iff.2 <| σ_prop₃ (w.sorted₄ ab bc cd) gp h1 h2

theorem satisfies_cupDef (w : WBPoints) {a b c d : Fin (length w)}
    (ab : a < b) (bc : b < c) (cd : c < d) : (cupDef a b c d).eval w.toPropAssn := by
  simp [cupDef, isCap]; intro h1 h2
  exact ⟨_, ab, bc, cd, h1, h2⟩

theorem satisfies_cupDef2 (w : WBPoints) {a c d : Fin (length w)} :
    (cupDef2 a c d).eval w.toPropAssn := by
  simp [cupDef2, isCap]; intro b ab bc cd h1 h2
  exact σ_prop₁ (w.sorted₄ ab bc cd) (w.gp₄ ab bc cd) h1 h2

theorem satisfies_capFDef (w : WBPoints) {a b c d : Fin (length w)} (bc : b < c) (cd : c < d)
    (hh : σIsEmptyTriangleFor w[a] w[b] w[d] w.toFinset) : (capFDef a b c d).eval w.toPropAssn := by
  simp [capFDef, isCapF]; intro h1 h2
  exact ⟨cd, _, h2, (w.gp₃ bc cd).σ_iff.1 h1, hh⟩

inductive Arc (w : WBPoints) (o : Orientation) : List (Fin (length w)) → Prop where
  | one : a < b → Arc w o [a, b]
  | cons : a < b → σ w[a] w[b] w[c] = o → Arc w o (b::c::l) → Arc w o (a::b::c::l)

theorem Arc.sorted (H : Arc w o l) : l.Sorted (·<·) := by
  apply chain'_iff_pairwise.1
  induction H with
  | one ab => simp [*]
  | cons ab _ _ IH => exact .cons ab IH

theorem Arc.head_lt (H : Arc w o (a::b::l)) : a < b := by
  have := H.sorted; simp at this; simp [this]

theorem Arc.pairwise {a b c : Fin w.length} (ab : a < b) (abc : σ w[a] w[b] w[c] = o)
    (H : Arc w o (b::c::l)) : (b::c::l).Pairwise (σ w[a] w[·] w[·] = o) := by
  generalize eq : b::c::l = l' at H ⊢
  induction H generalizing b c l with cases eq
  | one _ => simp [abc]
  | @cons b c d l bc bcd h IH =>
    have .cons ce de := h.sorted; have cd := ce _ (.head _)
    have sorted := w.sorted₄ ab bc cd; have gp := w.gp₄ ab bc cd
    match o with
    | .Collinear => cases (w.gp₃ ab bc).σ_ne abc
    | .CCW =>
      have IH := IH (ab.trans bc) (σ_prop₁ sorted gp abc bcd) rfl
      refine .cons ?_ IH; let .cons IH1 IH2 := IH
      refine forall_mem_cons.2 ⟨abc, fun e he => ?_⟩
      exact σ_prop₂ (w.sorted₄ ab bc (ce _ he)) (w.gp₄ ab bc (ce _ he)) abc (IH1 _ he)
    | .CW =>
      have IH := IH (ab.trans bc) (σ_prop₃ sorted gp abc bcd) rfl
      refine .cons ?_ IH; let .cons IH1 IH2 := IH
      refine forall_mem_cons.2 ⟨abc, fun e he => ?_⟩
      exact σ_prop₄ (w.sorted₄ ab bc (ce _ he)) (w.gp₄ ab bc (ce _ he)) abc (IH1 _ he)

theorem Arc.ccw (H : Arc w .CCW l) : σCCWPoints (l.map (w[·])) := by
  induction H with
  | one _ => simp [σCCWPoints]
  | @cons a b c l ab abc h IH => exact ⟨pairwise_map.2 (h.pairwise ab abc), IH⟩

theorem Arc.cw (H : Arc w .CW l) : σCCWPoints (l.reverse.map (w[·])) := by
  induction H with
  | one _ => simp [σCCWPoints]
  | @cons a b c l ab abc h IH =>
    rw [reverse_cons, map_append, σCCWPoints_append]
    refine ⟨IH, ?_⟩; simp [σCCWPoints, pairwise_map, pairwise_append, pairwise_reverse]
    have := (h.pairwise ab abc).imp fun {b c} h => show σ w[c] w[b] w[a] = .CCW by
      rw [σ_perm₁, ← σ_perm₂, σ_perm₁, h]; rfl
    simp at this; simp (config := {contextual := true}) [this]

theorem Arc.join (H1 : Arc w .CCW (a::l₁++[b])) (H2 : Arc w .CW (a::l₂++[b])) :
    σCCWPoints ((a::l₁++b::l₂.reverse).map (w[·])) := by
  have C1 := H1.ccw; have C2 := H2.cw
  have S1 := H1.sorted; have S2 := H2.sorted; simp [Sorted, -cons_append, pairwise_append] at S1 S2
  rw [show reverse (a :: l₂ ++ [b]) = b :: reverse l₂ ++ [a] by simp] at C2
  rw [map_append, σCCWPoints_append] at C1 C2 ⊢
  refine ⟨C1.1, C2.1, ?_⟩; simp [σCCWPoints, pairwise_map, pairwise_reverse] at C1 C2 ⊢
  have ⟨⟨A1, A2⟩, A3, A4⟩ := C1
  have ⟨⟨B1, B2⟩, B3, B4⟩ := C2
  refine ⟨⟨⟨fun d hd => ?_, B4.imp <| Eq.trans ?_⟩,
    fun c hc => ⟨fun d hd => ?_, ?_⟩⟩, ⟨A3, A4⟩, fun d hd => ⟨fun c hc => ?_, ?_⟩⟩
  · rw [σ_perm₁, ← σ_perm₂, B3 _ hd]
  · rw [σ_perm₁, ← σ_perm₂]
  · obtain cd | rfl | dc := lt_trichotomy c d
    · have sorted := w.sorted₄ (S1.1.1 _ hc) cd (S2.2.2 _ hd)
      have gp := w.gp₄ (S1.1.1 _ hc) cd (S2.2.2 _ hd)
      rw [σ_perm₂, gp.gp₄.σ_iff.1 fun h => ?_]; rfl
      have := σ_prop₂' sorted gp (A3 _ hc) h
      rw [σ_perm₁, ← σ_perm₂, σ_perm₁, B3 _ hd] at this; cases this
    · have := A3 _ hc
      rw [σ_perm₁, ← σ_perm₂, σ_perm₁, B3 _ hd] at this; cases this
    · have sorted := w.sorted₄ (S2.1.1 _ hd) dc (S1.2.2 _ hc)
      have gp := w.gp₄ (S2.1.1 _ hd) dc (S1.2.2 _ hc)
      rw [σ_perm₂, ← σ_perm₁, gp.gp₄.σ_iff'.1 fun h => ?_]
      have := σ_prop₄' sorted gp (by rw [σ_perm₁, ← σ_perm₂, σ_perm₁, B3 _ hd]; rfl) h
      rw [A3 _ hc] at this; cases this
  · sorry
  · obtain cd | rfl | dc := lt_trichotomy c d
    · have sorted := w.sorted₄ (S1.1.1 _ hc) cd (S2.2.2 _ hd)
      have gp := w.gp₄ (S1.1.1 _ hc) cd (S2.2.2 _ hd)
      rw [gp.gp₁.σ_iff'.1 fun h => ?_]
      have := σ_prop₄ sorted gp h (by rw [σ_perm₁, ← σ_perm₂, σ_perm₁, B3 _ hd]; rfl)
      rw [A3 _ hc] at this; cases this
    · have := A3 _ hc
      rw [σ_perm₁, ← σ_perm₂, σ_perm₁, B3 _ hd] at this; cases this
    · have sorted := w.sorted₄ (S2.1.1 _ hd) dc (S1.2.2 _ hc)
      have gp := w.gp₄ (S2.1.1 _ hd) dc (S1.2.2 _ hc)
      rw [σ_perm₂, gp.gp₁.σ_iff.1 fun h => ?_]; rfl
      have := σ_prop₂ sorted gp h (A3 _ hc)
      rw [σ_perm₁, ← σ_perm₂, σ_perm₁, B3 _ hd] at this; cases this
  · sorry

theorem of_5hole {w : WBPoints}
    {a b c d e : Fin (length w)}
    (ha : (0 : Fin (w.rest.length+1)) < a) (ab : a < b) (bc : b < c) (cd : c < d) (de : d < e)
    (ace : σIsEmptyTriangleFor w[a] w[c] w[e] w.toFinset)
    (abc : σ w[a] w[b] w[c] = .CCW)
    (bcd : σ w[b] w[c] w[d] = .CCW)
    (cde : σ w[c] w[d] w[e] = .CCW) : σHasEmptyNGon 6 w.toFinset := by
  have ae := ab.trans <| bc.trans <| cd.trans de
  have ⟨i, hi1, hi2, hi3, hi4⟩ := σIsEmptyTriangleFor_exists w.gp ⟨_, .swap .., w.sublist ha ae⟩
  obtain ⟨i, rfl⟩ := mem_points_iff.1 hi1
  obtain eq | hi := hi3
  · cases w.eq_iff'.1 eq
    have := w.σ_0 ha ab
    sorry
  sorry

theorem satisfies_no6Hole3Below {w : WBPoints} (hw : ¬σHasEmptyNGon 6 w.toFinset)
    {a c d e : Fin (length w)}
    (ha : (0 : Fin (w.rest.length+1)) < a) (de : d < e)
    (ace : σIsEmptyTriangleFor w[a] w[c] w[e] w.toFinset) :
    (no6Hole3Below a c d e).eval w.toPropAssn := by
  simp [no6Hole3Below]; intro ⟨b, ab, bc, cd, abc, bcd⟩ cde
  exact hw <| of_5hole ha ab bc cd de ace abc bcd cde

theorem satisfies_no6Hole4Above {w : WBPoints} (hw : ¬σHasEmptyNGon 6 w.toFinset)
    {a d e f : Fin (length w)}
    (ha : (0 : Fin (w.rest.length+1)) < a) (ef : e < f) :
    (no6Hole4Above a d e f).eval w.toPropAssn := by
  simp [no6Hole4Above]; intro ⟨de, c, ⟨b, ab, bc, cd, abc, bcd⟩, cde, ace⟩
  refine (w.gp₃ de ef).σ_iff'.1 fun def_ => ?_
  sorry

theorem satisfies_no6Hole2Below {w : WBPoints} (hw : ¬σHasEmptyNGon 6 w.toFinset)
    {a c e f : Fin (length w)}
    (ha : (0 : Fin (w.rest.length+1)) < a) (ce : c ≠ e) :
    (no6Hole2Below a c f e).eval w.toPropAssn := by
  simp [no6Hole2Below]; intro ⟨b, ab, bc, cf, abc, bcd⟩ ⟨d, ad, de, ef, ade, def_⟩ hh
  split_ifs at hh with ce <;> simp at hh
  · sorry
  · replace ce := lt_of_le_of_ne (not_lt.1 ce) (Ne.symm ‹_›)
    sorry

theorem satisfies_no6Hole1Below {w : WBPoints} (hw : ¬σHasEmptyNGon 6 w.toFinset)
    {a d e f : Fin (length w)}
    (ha : (0 : Fin (w.rest.length+1)) < a) (df : d < f) (ae : a < e) (ef : e < f) (de : d ≠ e) :
    (no6Hole1Below a d f e).eval w.toPropAssn := by
  simp [no6Hole1Below]; intro ⟨df, c, ⟨b, ab, bc, cd, abc, bcd⟩, cdf, acf⟩ aef
  sorry

theorem satisfies_hexagonEncoding (w : WBPoints) (hw : ¬σHasEmptyNGon 6 w.toFinset) :
    (hexagonEncoding w.length).eval w.toPropAssn := by
  simp [hexagonEncoding, satisfies_baseEncoding, no6HoleClauses1, no6HoleClauses2, no6HoleClauses3]
  refine ⟨
    fun a ha b ab c bc d cd => ⟨?_, ?_, fun _ => ⟨fun hh => ⟨?_, ?_⟩, fun _ => ?_⟩⟩,
    fun a _ b _ c _ => ⟨?_, ?_⟩,
    fun a ha b _ c bc p ap pc bp => ⟨fun _ _ => ?_, fun _ => ?_⟩⟩
  · with_reducible exact satisfies_capDef w ab bc cd
  · with_reducible exact satisfies_cupDef w ab bc cd
  · with_reducible exact satisfies_capFDef w bc cd hh
  · with_reducible exact satisfies_no6Hole3Below hw ha cd hh
  · with_reducible exact satisfies_no6Hole4Above hw ha cd
  · with_reducible exact satisfies_capDef2 w
  · with_reducible exact satisfies_cupDef2 w
  · with_reducible exact satisfies_no6Hole2Below hw ha bp
  · with_reducible exact satisfies_no6Hole1Below hw ha bc ap pc bp

end WBPoints
