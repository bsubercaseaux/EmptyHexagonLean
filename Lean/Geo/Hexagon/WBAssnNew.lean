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

theorem satisfies_no6Hole3Below {w : WBPoints} (hw : ¬σHasEmptyNGon 6 w.toFinset)
    {a c d e : Fin (length w)}
    (ha : (0 : Fin (w.rest.length+1)) < a) (de : d < e)
    (ace : σIsEmptyTriangleFor w[a] w[c] w[e] w.toFinset) :
    (no6Hole3Below a c d e).eval w.toPropAssn := by
  simp [no6Hole3Below]; intro ⟨b, ab, bc, cd, abc, bcd⟩ cde
  sorry

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
