import Geo.Definitions.CanonicalPoints
import Geo.Definitions.PtInTriangle
import Geo.Definitions.Structures
import Geo.Definitions.OrientationProperties
import Geo.Orientations
import Geo.Triangle.Encoding
import Geo.KGon.Assn

namespace Geo.CanonicalPoints
open List Classical Point
attribute [-simp] getElem_fin

theorem satisfies_triangleEncoding (w : CanonicalPoints) :
    ¬σHasEmptyKGon 3 w.toFinset →
    (triangleEncoding w.rlen).eval w.toPropAssn := by
  simp [triangleEncoding, satisfies_baseEncoding, noHoleClauses]
  intro noholes a b ab c bc h
  refine noholes <| (σHasEmptyKGon_3_iff w.gp).2
    ⟨w+[a], w+[b], w+[c], (w.sublist ab.succ₂ bc.succ₂).subperm, h⟩

end CanonicalPoints
