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
  refine ⟨C1.1, C2.1, ?_⟩
  simp only [σCCWPoints, pairwise_map, Pairwise.nil, map_cons, mem_cons,
    mem_map, pairwise_cons, not_mem_nil, IsEmpty.forall_iff, implies_true,
    mem_singleton, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, true_and,
    pairwise_reverse, mem_reverse, forall_eq_or_imp, and_true] at C1 C2 ⊢
  obtain ⟨⟨A1, -⟩, A3, A4⟩ := C1; obtain ⟨⟨B1, -⟩, B3, B4⟩ := C2
  have ne {c e} (hc : c ∈ l₁) (he : e ∈ l₂) : c ≠ e := by
    rintro rfl; have := A3 _ hc; rw [σ_perm₁, ← σ_perm₂, σ_perm₁, B3 _ he] at this; cases this
  have O {c e} (hc : c ∈ l₁) (he : e ∈ l₂) : σ w[a] w[c] w[e] = .CCW ∧ σ w[c] w[b] w[e] = .CCW := by
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
    obtain ce | ec := lt_or_gt_of_ne (ne hc he)
    obtain de | ed := lt_or_gt_of_ne (ne hd he)
    · have sorted := w.sorted₄ cd de (S2.2.2 _ he)
      have gp := w.gp₄ cd de (S2.2.2 _ he)
      rw [gp.gp₁.σ_iff'.1 fun h => ?_]
      rw [σ_prop₃' sorted gp h (by rw [σ_perm₂, dbe]; rfl)] at cdb; cases cdb
    · have sorted := w.sorted₄ (S1.1.1 _ hc) ce ed
      have gp := w.gp₄ (S1.1.1 _ hc) ce ed
      rw [σ_perm₂, gp.gp₄.σ_iff.1 fun h => ?_]; rfl
      rw [σ_perm₂, σ_prop₂' sorted gp acd h] at ade; cases ade
    · have sorted := w.sorted₄ (S2.1.1 _ he) ec cd
      have gp := w.gp₄ (S2.1.1 _ he) ec cd
      rw [σ_perm₂, ← σ_perm₁, gp.gp₄.σ_iff'.1 fun h => ?_]
      rw [σ_prop₃ sorted gp (by rw [σ_perm₂, (O hc he).1]; rfl) h] at acd; cases acd

theorem of_5hole {w : WBPoints} {a b c d e : Fin (length w)}
    (ha : (0 : Fin (w.rest.length+1)) < a) (ab : a < b) (bc : b < c) (cd : c < d) (de : d < e)
    (ace : σIsEmptyTriangleFor w[a] w[c] w[e] w.toFinset)
    (abc : σ w[a] w[b] w[c] = .CCW)
    (bcd : σ w[b] w[c] w[d] = .CCW)
    (cde : σ w[c] w[d] w[e] = .CCW) : σHasEmptyNGon 6 w.toFinset := by
  refine σCCWPoints.emptyHexagon' ?_ w.gp ace (subset_map w [(0:Fin (_+1)), a, b, c, d, e])
  refine Arc.join (l₁ := [a,b,c,d]) (l₂ := [])
    (.cons ha (w.σ_0 ha ab) <| .cons ab abc <| .cons bc bcd <| .cons cd cde <| .one de)
    (.one <| ha.trans <| ab.trans <| bc.trans <| cd.trans de)

theorem satisfies_no6Hole3Below {w : WBPoints} (hw : ¬σHasEmptyNGon 6 w.toFinset)
    {a c d e : Fin (length w)} (ha : (0 : Fin (w.rest.length+1)) < a) (de : d < e)
    (ace : σIsEmptyTriangleFor w[a] w[c] w[e] w.toFinset) :
    (no6Hole3Below a c d e).eval w.toPropAssn := by
  simp [no6Hole3Below]; intro ⟨b, ab, bc, cd, abc, bcd⟩ cde
  exact hw <| of_5hole ha ab bc cd de ace abc bcd cde

theorem satisfies_no6Hole4Above {w : WBPoints} (hw : ¬σHasEmptyNGon 6 w.toFinset)
    {a d e f : Fin (length w)} (ef : e < f) :
    (no6Hole4Above a d e f).eval w.toPropAssn := by
  simp [no6Hole4Above]; intro ⟨de, c, ⟨b, ab, bc, cd, abc, bcd⟩, cde, ace⟩
  refine (w.gp₃ de ef).σ_iff'.1 fun def_ => ?_
  refine hw <| (σCCWPoints.cycle (l₂ := [_, _, _, _, _]) ?_).emptyHexagon'
    w.gp ace.perm₂.perm₁.perm₂ (subset_map w [f, e, d, c, b, a])
  exact Arc.join (l₁ := []) (l₂ := [b,c,d,e])
    (.one <| ab.trans <| bc.trans <| cd.trans <| de.trans ef)
    (.cons ab abc <| .cons bc bcd <| .cons cd cde <| .cons de def_ <| .one ef)

theorem satisfies_no6Hole2Below {w : WBPoints} (hw : ¬σHasEmptyNGon 6 w.toFinset)
    {a c e f : Fin (length w)} :
    (no6Hole2Below a c f e).eval w.toPropAssn := by
  simp [no6Hole2Below]; intro ⟨b, ab, bc, cf, abc, bcd⟩ ⟨d, ad, de, ef, ade, def_⟩ hh
  have := Arc.join (l₁ := [b,c]) (l₂ := [d,e])
    (.cons ab abc <| .cons bc bcd <| .one cf)
    (.cons ad ade <| .cons de def_ <| .one ef)
  refine hw <| this.emptyHexagon w.gp ?_ (subset_map w [a, b, c, f, e, d])
  split_ifs at hh with ce <;> simp at hh <;> [exact hh; exact hh.perm₂]

theorem satisfies_no6Hole1Below {w : WBPoints} (hw : ¬σHasEmptyNGon 6 w.toFinset)
    {a d e f : Fin (length w)} (ae : a < e) (ef : e < f) :
    (no6Hole1Below a d f e).eval w.toPropAssn := by
  simp [no6Hole1Below]; intro ⟨df, c, ⟨b, ab, bc, cd, abc, bcd⟩, cdf, acf⟩ aef
  have := Arc.join (l₁ := [e]) (l₂ := [b,c,d])
    (.cons ae aef <| .one ef)
    (.cons ab abc <| .cons bc bcd <| .cons cd cdf <| .one df)
  refine hw <| this.emptyHexagon w.gp acf.perm₂ (subset_map w [a, e, f, d, c, b])

theorem satisfies_hexagonEncoding (w : WBPoints) (hw : ¬σHasEmptyNGon 6 w.toFinset) :
    (hexagonEncoding w.length).eval w.toPropAssn := by
  simp [hexagonEncoding, satisfies_baseEncoding, no6HoleClauses1, no6HoleClauses2, no6HoleClauses3]
  refine ⟨
    fun a ha b ab c bc d cd => ⟨?_, ?_, fun _ => ⟨fun hh => ⟨?_, ?_⟩, fun _ => ?_⟩⟩,
    fun a _ b _ c _ => ⟨?_, ?_⟩,
    fun a _ b _ c _ p ap pc _ => ⟨fun _ _ => ?_, fun _ => ?_⟩⟩
  · with_reducible exact satisfies_capDef w ab bc cd
  · with_reducible exact satisfies_cupDef w ab bc cd
  · with_reducible exact satisfies_capFDef w bc cd hh
  · with_reducible exact satisfies_no6Hole3Below hw ha cd hh
  · with_reducible exact satisfies_no6Hole4Above hw cd
  · with_reducible exact satisfies_capDef2 w
  · with_reducible exact satisfies_cupDef2 w
  · with_reducible exact satisfies_no6Hole2Below hw
  · with_reducible exact satisfies_no6Hole1Below hw ap pc

end WBPoints
