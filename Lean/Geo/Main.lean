import Geo.PlaneGeometry
import Geo.SymmetryBreaking
import Geo.Slope
import Geo.Point

structure EmptyCovexHexagon (a b c d e f: Point) : Prop :=
  --


theorem EmptyHexagonTheorem (pts: List Point)
  (h: List.length pts ≥ 30) :
  ∃ (a b c d e f: Fin (List.length pts)),
  EmptyCovexHexagon (pts.get a)
                    (pts.get b)
                    (pts.get c)
                    (pts.get d)
                    (pts.get e)
                    (pts.get f) := by sorry
