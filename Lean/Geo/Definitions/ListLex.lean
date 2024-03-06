import Geo.Orientations

namespace Geo

noncomputable def adjacentOrientations : List Point → List Orientation
  | a :: b :: l => go a b l
  | _ => []
where
  go a b
  | [] => []
  | c :: l => σ a b c :: go b c l

theorem adjacentOrientations_reverse :
    adjacentOrientations pts.reverse = (adjacentOrientations pts).reverse.map .neg := sorry

def ListLex (l1 l2 : List Orientation) : Prop := sorry

def ListLexSelf (l : List Orientation) : Prop := ListLex l l.reverse
