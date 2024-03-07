import Geo.Definitions.WBPoints
import Geo.Definitions.PtInTriangle
import Geo.Definitions.Structures
import Geo.Definitions.OrientationProperties
import Geo.Orientations
import Geo.Triangle.EncodingNew
import Geo.NGon.WBAssnNew

namespace Geo.WBPoints
open List
open Classical

open LeanSAT.Model PropFun

open Point

theorem satisfies_triangleEncoding (w : WBPoints) :
    ¬σHasEmptyTriangle w.toFinset →
    (triangleEncoding w.length).eval w.toPropAssn := by
  simp [triangleEncoding, satisfies_baseEncoding, noHoleClauses,
    σIsEmptyTriangleFor, mem_toFinset_iff, σHasEmptyTriangle]
  intro noholes a b hab c hbc
  exact noholes a b (ne_of_lt hab <| w.eq_iff.1 <| · ▸ rfl)
                  c (ne_of_lt (hab.trans hbc) <| w.eq_iff.1 <| · ▸ rfl)
                    (ne_of_lt hbc <| w.eq_iff.1 <| · ▸ rfl)

end WBPoints
