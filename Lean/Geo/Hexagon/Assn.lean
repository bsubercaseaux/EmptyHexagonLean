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

theorem satisfies_no6Hole3Below {w : CanonicalPoints} (hw : ¬σHasEmptyKGon 6 w.toFinset)
    {a c d e : Fin w.rlen} (de : d < e) :
    (no6Hole3Below a c d e).eval w.toPropAssn := by
  simp [no6Hole3Below]; intro ace ⟨b, ab, bc, cd, abc, bcd⟩ cde
  refine hw <| σCCWPoints.emptyHexagon' ?_ w.gp ace
    (subset_map w [0, a.succ, b.succ, c.succ, d.succ, e.succ])
  exact Arc.join (l₁ := [_,_,_,_]) (l₂ := [])
    (.cons (Fin.succ_pos _) (w.σ_0 ab) <|
      .cons' ab abc <| .cons' bc bcd <| .cons' cd cde <| .one' de)
    (.one <| Fin.succ_pos _)

theorem satisfies_no6Hole4Above {w : CanonicalPoints} (hw : ¬σHasEmptyKGon 6 w.toFinset)
    {a d e f : Fin w.rlen} (ef : e < f) :
    (no6Hole4Above a d e f).eval w.toPropAssn := by
  simp [no6Hole4Above]; intro ⟨de, c, ⟨b, ab, bc, cd, abc, bcd⟩, cde, ace⟩
  refine (w.gp₃' de ef).σ_iff'.1 fun def_ => ?_
  refine hw <| (σCCWPoints.cycle (l₂ := [_, _, _, _, _]) ?_).emptyHexagon'
    w.gp ace.perm₂.perm₁.perm₂ (subset_map' w [f, e, d, c, b, a])
  exact Arc.join (l₁ := []) (l₂ := [_,_,_,_])
    (.one' <| ab.trans <| bc.trans <| cd.trans <| de.trans ef)
    (.cons' ab abc <| .cons' bc bcd <| .cons' cd cde <| .cons' de def_ <| .one' ef)

theorem satisfies_no6Hole2Below {w : CanonicalPoints} (hw : ¬σHasEmptyKGon 6 w.toFinset)
    {a c e f : Fin w.rlen} :
    (no6Hole2Below a c f e).eval w.toPropAssn := by
  simp [no6Hole2Below]; intro ⟨b, ab, bc, cf, abc, bcd⟩ ⟨d, ad, de, ef, ade, def_⟩ hh
  have := Arc.join (l₁ := [_,_]) (l₂ := [_,_])
    (.cons' ab abc <| .cons' bc bcd <| .one' cf)
    (.cons' ad ade <| .cons' de def_ <| .one' ef)
  refine hw <| this.emptyHexagon w.gp ?_ (subset_map' w [a, b, c, f, e, d])
  split_ifs at hh with ce <;> simp at hh <;> [exact hh; exact hh.perm₂]

theorem satisfies_no6Hole1Below {w : CanonicalPoints} (hw : ¬σHasEmptyKGon 6 w.toFinset)
    {a d e f : Fin w.rlen} (ae : a < e) (ef : e < f) :
    (no6Hole1Below a d f e).eval w.toPropAssn := by
  simp [no6Hole1Below]; intro ⟨df, c, ⟨b, ab, bc, cd, abc, bcd⟩, cdf, acf⟩ aef
  have := Arc.join (l₁ := [_]) (l₂ := [_,_,_])
    (.cons' ae aef <| .one' ef)
    (.cons' ab abc <| .cons' bc bcd <| .cons' cd cdf <| .one' df)
  refine hw <| this.emptyHexagon w.gp acf.perm₂ (subset_map' w [a, e, f, d, c, b])

theorem satisfies_hexagonEncoding (w : CanonicalPoints) (hw : ¬σHasEmptyKGon 6 w.toFinset) :
    (hexagonEncoding w.rlen).eval w.toPropAssn := by with_reducible
  simp [hexagonEncoding, satisfies_baseKGonEncoding, no6HoleClauses1, no6HoleClauses2]
  refine ⟨
    fun a b _ c _ d cd => ⟨?_, fun _ => ?_⟩,
    fun a b _ c _ p ap pc _ => ⟨fun _ => ?_, fun _ => ?_⟩⟩
  · exact satisfies_no6Hole3Below hw cd
  · exact satisfies_no6Hole4Above hw cd
  · exact satisfies_no6Hole2Below hw
  · exact satisfies_no6Hole1Below hw ap pc

end CanonicalPoints
