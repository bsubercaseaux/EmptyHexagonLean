import Geo.Definitions.CanonicalPoints
import Geo.Definitions.PtInTriangle
import Geo.Definitions.Structures
import Geo.Definitions.OrientationProperties
import Geo.Definitions.Orientations
import Geo.Hexagon.Encoding
import Geo.KGon.Arc
import Geo.KGon.Assn

namespace Geo.CanonicalPoints
open List Classical LeanSAT.Model PropFun Point
attribute [-simp] getElem_fin

theorem satisfies_no6Hole3Below {w : CanonicalPoints} (hw : ¬σHasEmptyKGonIf 6 holes w.toFinset)
    {a c d e : Fin w.rlen} (de : d < e) :
    (no6Hole3Below holes a c d e).eval (w.toPropAssn holes) := by
  simp [no6Hole3Below, -not_forall]
  intro ⟨cd, b, ab, bc, abc, bcd⟩ cde ace
  refine hw <| σCCWPoints.emptyHexagonIf' ?ccwp w.gp ace
    (subset_map w [0, a.succ, b.succ, c.succ, d.succ, e.succ])
  case ccwp =>
    exact Arc.join (l₁ := [_,_,_,_]) (l₂ := [])
      (.cons (Fin.succ_pos _) (w.σ_0 ab) <|
        .cons' ab abc <| .cons' bc bcd <| .cons' cd cde <| .one' de)
      (.one <| Fin.succ_pos _)

theorem satisfies_no6Hole4Above {w : CanonicalPoints} (hw : ¬σHasEmptyKGonIf 6 holes w.toFinset)
    {a d e f : Fin w.rlen} (ef : e < f) :
    (no6Hole4Above a d e f).eval (w.toPropAssn holes) := by
  simp [no6Hole4Above]; intro ⟨de, c, ⟨cd, b, ab, bc, abc, bcd⟩, cde, ace⟩
  refine (w.gp₃' de ef).σ_iff'.1 fun def_ => ?_
  refine hw <| (σCCWPoints.cycle (l₂ := [_, _, _, _, _]) ?_).emptyHexagonIf'
    w.gp (ace · |>.perm₂.perm₁.perm₂) (subset_map' w [f, e, d, c, b, a])
  exact Arc.join (l₁ := []) (l₂ := [_,_,_,_])
    (.one' <| ab.trans <| bc.trans <| cd.trans <| de.trans ef)
    (.cons' ab abc <| .cons' bc bcd <| .cons' cd cde <| .cons' de def_ <| .one' ef)

theorem satisfies_no6Hole2Below {w : CanonicalPoints} (hw : ¬σHasEmptyKGonIf 6 holes w.toFinset)
    {a c e f : Fin w.rlen} :
    (no6Hole2Below holes a c f e).eval (w.toPropAssn holes) := by
  simp [no6Hole2Below]; intro ⟨cf, b, ab, bc, abc, bcd⟩ ⟨ef, d, ad, de, ade, def_⟩
  refine not_imp.1 fun hh => ?_
  have := Arc.join (l₁ := [_,_]) (l₂ := [_,_])
    (.cons' ab abc <| .cons' bc bcd <| .one' cf)
    (.cons' ad ade <| .cons' de def_ <| .one' ef)
  refine hw <| this.emptyHexagonIf w.gp (fun h => ?_) (subset_map' w [a, b, c, f, e, d])
  split_ifs at hh with ce <;> simp [Var.hole] at hh <;> [exact hh h h; exact (hh h h).perm₂]

theorem satisfies_no6Hole1Below {w : CanonicalPoints} (hw : ¬σHasEmptyKGonIf 6 holes w.toFinset)
    {a d e p : Fin w.rlen} (ap : a < p) (pf : p < e) :
    (no6Hole1Below a d e p).eval (w.toPropAssn holes) := by
  simp [no6Hole1Below]; intro ⟨de, c, ⟨cd, b, ab, bc, abc, bcd⟩, cde, ace⟩ ape
  have := Arc.join (l₁ := [_]) (l₂ := [_,_,_])
    (.cons' ap ape <| .one' pf)
    (.cons' ab abc <| .cons' bc bcd <| .cons' cd cde <| .one' de)
  refine hw <| this.emptyHexagonIf w.gp (ace · |>.perm₂) (subset_map' w [a, p, e, d, c, b])

theorem satisfies_hexagonEncoding (w : CanonicalPoints) (hw : ¬σHasEmptyKGonIf 6 holes w.toFinset) :
    (hexagonEncoding w.rlen holes).eval (w.toPropAssn holes) := by with_reducible
  simp [hexagonEncoding, satisfies_baseEncoding, satisfies_arcDefClauses1,
    satisfies_arcDefClauses2, satisfies_capFDefClauses, no6HoleClauses1, no6HoleClauses2]
  refine ⟨
    fun a b _ c _ d cd => ⟨?_, fun _ => ?_⟩,
    fun a b _ c _ p ap pc _ => ⟨fun _ => ?_, fun _ => ?_⟩⟩
  · exact satisfies_no6Hole3Below hw cd
  · exact satisfies_no6Hole4Above hw cd
  · exact satisfies_no6Hole2Below hw
  · exact satisfies_no6Hole1Below hw ap pc

end CanonicalPoints
