import Geo.Definitions.CanonicalPoints
import Geo.Definitions.PtInTriangle
import Geo.Definitions.Structures
import Geo.Definitions.OrientationProperties
import Geo.Orientations
import Geo.Hexagon.Encoding
import Geo.Hexagon.Arc
import Geo.KGon.Assn

namespace Geo.CanonicalPoints
open List Classical LeanSAT.Model PropFun Point
attribute [-simp] getElem_fin

theorem satisfies_capDef (w : CanonicalPoints) {a b c d : Fin (length w)}
    (ab : a < b) (bc : b < c) (cd : c < d) : (capDef a b c d).eval w.toPropAssn := by
  simp [capDef, isCap]; intro h1 h2
  exact ⟨_, ab, bc, cd, (w.gp₃ ab bc).σ_iff.1 h1, (w.gp₃ bc cd).σ_iff.1 h2⟩

theorem satisfies_capDef2 (w : CanonicalPoints) {a c d : Fin (length w)} :
    (capDef2 a c d).eval w.toPropAssn := by
  simp [capDef2, isCap]; intro b ab bc cd h1 h2
  have gp := w.gp₄ ab bc cd
  exact gp.gp₃.σ_iff.2 <| σ_prop₃ (w.sorted₄ ab bc cd) gp h1 h2

theorem satisfies_cupDef (w : CanonicalPoints) {a b c d : Fin (length w)}
    (ab : a < b) (bc : b < c) (cd : c < d) : (cupDef a b c d).eval w.toPropAssn := by
  simp [cupDef, isCap]; intro h1 h2
  exact ⟨_, ab, bc, cd, h1, h2⟩

theorem satisfies_cupDef2 (w : CanonicalPoints) {a c d : Fin (length w)} :
    (cupDef2 a c d).eval w.toPropAssn := by
  simp [cupDef2, isCap]; intro b ab bc cd h1 h2
  exact σ_prop₁ (w.sorted₄ ab bc cd) (w.gp₄ ab bc cd) h1 h2

theorem satisfies_capFDef (w : CanonicalPoints) {a b c d : Fin (length w)} (bc : b < c) (cd : c < d)
    (hh : σIsEmptyTriangleFor w[a] w[b] w[d] w.toFinset) : (capFDef a b c d).eval w.toPropAssn := by
  simp [capFDef, isCapF]; intro h1 h2
  exact ⟨cd, _, h2, (w.gp₃ bc cd).σ_iff.1 h1, hh⟩

theorem satisfies_no6Hole3Below {w : CanonicalPoints} (hw : ¬σHasEmptyKGon 6 w.toFinset)
    {a c d e : Fin (length w)} (ha : (0 : Fin (w.rest.length+1)) < a) (de : d < e)
    (ace : σIsEmptyTriangleFor w[a] w[c] w[e] w.toFinset) :
    (no6Hole3Below a c d e).eval w.toPropAssn := by
  simp [no6Hole3Below]; intro ⟨b, ab, bc, cd, abc, bcd⟩ cde
  refine hw <| σCCWPoints.emptyHexagon' ?_ w.gp ace (subset_map w [(0:Fin (_+1)), a, b, c, d, e])
  exact Arc.join (l₁ := [a,b,c,d]) (l₂ := [])
    (.cons ha (w.σ_0 ha ab) <| .cons ab abc <| .cons bc bcd <| .cons cd cde <| .one de)
    (.one <| ha.trans <| ab.trans <| bc.trans <| cd.trans de)

theorem satisfies_no6Hole4Above {w : CanonicalPoints} (hw : ¬σHasEmptyKGon 6 w.toFinset)
    {a d e f : Fin (length w)} (ef : e < f) :
    (no6Hole4Above a d e f).eval w.toPropAssn := by
  simp [no6Hole4Above]; intro ⟨de, c, ⟨b, ab, bc, cd, abc, bcd⟩, cde, ace⟩
  refine (w.gp₃ de ef).σ_iff'.1 fun def_ => ?_
  refine hw <| (σCCWPoints.cycle (l₂ := [_, _, _, _, _]) ?_).emptyHexagon'
    w.gp ace.perm₂.perm₁.perm₂ (subset_map w [f, e, d, c, b, a])
  exact Arc.join (l₁ := []) (l₂ := [b,c,d,e])
    (.one <| ab.trans <| bc.trans <| cd.trans <| de.trans ef)
    (.cons ab abc <| .cons bc bcd <| .cons cd cde <| .cons de def_ <| .one ef)

theorem satisfies_no6Hole2Below {w : CanonicalPoints} (hw : ¬σHasEmptyKGon 6 w.toFinset)
    {a c e f : Fin (length w)} :
    (no6Hole2Below a c f e).eval w.toPropAssn := by
  simp [no6Hole2Below]; intro ⟨b, ab, bc, cf, abc, bcd⟩ ⟨d, ad, de, ef, ade, def_⟩ hh
  have := Arc.join (l₁ := [b,c]) (l₂ := [d,e])
    (.cons ab abc <| .cons bc bcd <| .one cf)
    (.cons ad ade <| .cons de def_ <| .one ef)
  refine hw <| this.emptyHexagon w.gp ?_ (subset_map w [a, b, c, f, e, d])
  split_ifs at hh with ce <;> simp at hh <;> [exact hh; exact hh.perm₂]

theorem satisfies_no6Hole1Below {w : CanonicalPoints} (hw : ¬σHasEmptyKGon 6 w.toFinset)
    {a d e f : Fin (length w)} (ae : a < e) (ef : e < f) :
    (no6Hole1Below a d f e).eval w.toPropAssn := by
  simp [no6Hole1Below]; intro ⟨df, c, ⟨b, ab, bc, cd, abc, bcd⟩, cdf, acf⟩ aef
  have := Arc.join (l₁ := [e]) (l₂ := [b,c,d])
    (.cons ae aef <| .one ef)
    (.cons ab abc <| .cons bc bcd <| .cons cd cdf <| .one df)
  refine hw <| this.emptyHexagon w.gp acf.perm₂ (subset_map w [a, e, f, d, c, b])

theorem satisfies_hexagonEncoding (w : CanonicalPoints) (hw : ¬σHasEmptyKGon 6 w.toFinset) :
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

end CanonicalPoints
