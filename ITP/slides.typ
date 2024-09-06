#import "@preview/touying:0.5.2": *
#import "@preview/cetz:0.2.2"
#import themes.university: *

// Some slides adapted from https://www.cs.cmu.edu/~mheule/talks/6hole-TACAS.pdf

#show: university-theme.with(
  config-info(
    title: [Formal Verification of the Empty Hexagon Number],
    author: [
      Bernardo Subercaseaux, Wojciech Nawrocki, James Gallicchio,\
      Cayden Codel, *Mario Carneiro*, Marijn J. H. Heule
    ],
    date: [
      Interactive Theorem Proving | September 9th, 2024\
      Tbilisi, Georgia
    ],
    institution: [Carnegie Mellon University, USA]
  )
)

#title-slide()

== Empty $k$-gons

Fix a set $S$ of points on the plane.
A *$k$-hole* is a convex $k$-gon with no point of $S$ in its interior.

#components.side-by-side(
  cetz.canvas(length: 33%, {
    import cetz.draw: *
    set-style(circle: (fill: blue, stroke: none, radius: 0.05))
    on-layer(1, {
      circle((angle: 0deg, radius: 1), name: "a")
      circle((angle: 72deg, radius: 1), name: "b")
      circle((angle: 144deg, radius: 1), name: "c")
      circle((angle: 216deg, radius: 1), name: "d")
      circle((angle: 290deg, radius: 1), name: "e")
      circle((angle: 30deg, radius: 1.5), fill: black)
      circle((angle: 240deg, radius: 1.5), fill: black)
    })
    line("a", "b", "c", "d", "e", "a", fill: green)
    content((0, -1.5), "5-hole ✔")
    content((0, -2.0), "convex 5-gon ✔")
  }),
  cetz.canvas(length: 33%, {
    import cetz.draw: *
    set-style(circle: (fill: blue, stroke: none, radius: 0.05))
    on-layer(1, {
      circle((angle: 0deg, radius: 1), name: "a")
      circle((angle: 120deg, radius: 1), name: "b")
      circle((angle: 180deg, radius: 0.2), name: "c")
      circle((angle: 240deg, radius: 1), name: "d")
      circle((angle: 200deg, radius: 1.2), fill: black)
    })
    line("a", "b", "c", "d", "a")
    content((0, -1.5), "4-hole ✘")
    content((0, -2.0), "convex 4-gon ✘")
  }),
  cetz.canvas(length: 33%, {
    import cetz.draw: *
    set-style(circle: (fill: blue, stroke: none, radius: 0.05))
    on-layer(1, {
      circle((angle: 0deg, radius: 1), name: "a")
      circle((angle: 120deg, radius: 1), name: "b")
      circle((angle: 240deg, radius: 1), name: "c")
      circle((angle: 30deg, radius: 0.2), fill: black)
    })
    line("a", "b", "c", "a")
    content((0, -1.5), "3-hole ✘")
    content((0, -2.0), "convex 3-gon ✔")
  }),
)

== Empty 4-gons

#slide(repeat: 10, self => [
  #let (uncover,) = utils.methods(self)

  *Theorem* (Klein 1932). // WN: I don't think a citation exists for this
  Every 5 points in the plane, no three collinear,
  contain a 4-hole. #pause

  _Proof._ By cases on the size of the convex hull: 5, 4, or 3 points.

  #components.side-by-side(
    uncover("3-", context align(center, cetz.canvas(length: 33%, {
      import cetz.draw: *

      set-style(circle: (fill: blue, stroke: none, radius: 0.05))
      on-layer(1, {
        circle((angle: 0deg, radius: 1), name: "a")
        circle((angle: 72deg, radius: 1), name: "b")
        circle((angle: 144deg, radius: 1), name: "c")
        circle((angle: 216deg, radius: 1), name: "d")
        circle((angle: 290deg, radius: 1), name: "e")
      })
      line("a", "b", "c", "d", "e", "a")
      if 4 <= self.subslide {
        line("a", "b", "c", "d", "a", fill: green)
      }
    }))),
    uncover("5-", context align(center, cetz.canvas(length: 33%, {
      import cetz.draw: *

      set-style(circle: (fill: blue, stroke: none, radius: 0.05))
      on-layer(1, {
        circle((angle: 0deg, radius: 1), name: "a")
        circle((angle: 90deg, radius: 1), name: "b")
        circle((angle: 180deg, radius: 1), name: "c")
        circle((angle: 270deg, radius: 1), name: "d")
        circle((angle: 60deg, radius: 0.5), name: "x")
      })
      line("a", "b", "c", "d", "a")
      if 7 <= self.subslide {
        line("a", "d", "c", "x", "a", fill: green)
      }
      if 6 <= self.subslide {
        line((angle: 0deg, radius: 1.5), (angle: 180deg, radius: 1.5), stroke: blue)
      }
    }))),
    uncover("8-10", context align(center, cetz.canvas(length: 33%, {
      import cetz.draw: *

      set-style(circle: (fill: blue, stroke: none, radius: 0.05))
      let xθ = 20deg
      let yθ = xθ + 180deg
      on-layer(1, {
        circle((angle: 0deg, radius: 1), name: "a")
        circle((angle: 120deg, radius: 1), name: "b")
        circle((angle: 240deg, radius: 1), name: "c")
        circle((angle: xθ, radius: 0.3), name: "x")
        circle((angle: yθ, radius: 0.3), name: "y")
      })
      line("a", "b", "c", "a")
      if 10 <= self.subslide {
        line("a", "x", "y", "c", "a", fill: green)
      }
      if 9 <= self.subslide {
        line((angle: xθ, radius: 1.5), (angle: yθ, radius: 1.5), stroke: blue)
      }
    })))
  )
])

== The Happy Ending Problem

*Theorem* @35erdos_combinatorial_problem_geometry.
For a fixed $k$, every _sufficiently large_ set of points,
no three collinear, contains a convex $k$-gon.

What about _$k$-holes_?

*Theorem* @hortonSetsNoEmpty1983.
For any $k ≥ 7$, there exist arbitrarily large sets of points,
no three collinear, containing no $k$-holes.

The $k$-th *hole number* $h(k)$ is the least number
such that any set of $h(k)$ points,
no three collinear,
necessarily contains a $k$-hole.

Horton ⇒ $h(7) = h(8) = … = ∞$

== The Complete Story

- $h(3) ≤ 3$ (trivial) ✔
- $h(4) ≤ 5$ (Klein 1932) ✔
- $h(5) ≤ 10$ @Harborth1978 ✔
- *$bold(h(6) ≤ 30)$ @24heule_happy_ending_empty_hexagon_every_set_30_points* ✔
- $29 < h(6)$ @03overmars_finding_sets_points_empty_convex_6_gons ✔

We formally verified all the above results using $L∃∀N$.
// TODO(WN): Should we stress more that
// verifying Heule/Scheucher was the hard part; and
// the other upper bounds follow from the encoding with not much effort; and
// then we also verified the pointset checker to establish lower bounds.

Upper bounds via reduction to SAT.

Lower bounds by checking explicit sets of points.

== SAT-Solving Mathematics

- *Reduction.* Show that the mathematical theorem of interest is true
  if a concrete propositional formula φ is unsatisfiable.
- *Solving.* Show that φ is indeed unsatisfiable using a SAT solver.

*Solving* is reliable, reproducible, and trustworthy:
formal proof systems (DRAT) and verified proof checkers (`cake_lpr`).

*Reduction* is problem-specific, and involves complex transformations:
focus of our work.

== Reduction from Geometry to SAT

#set text(size: 23pt)
1. Any set of points, no three collinear,
   can be transformed into a _canonical form_
   without removing $k$-holes.
   ```lean
  theorem symmetry_breaking {l : List Point} :
    3 ≤ l.length → Point.ListInGenPos l →
    ∃ w : CanonicalPoints, l ≼σ w.points
  ```
2. $n$ points in canonical form with no $k$-holes
   induce a propositional assignment that satisfies $φ_n$.
  ```lean
  theorem satisfies_hexagonEncoding (w : CanonicalPoints) :
      ¬σHasEmptyKGon 6 w.toFinset →
      w.toPropAssn ⊨ hexagonEncoding w.rlen
  ```
3. $φ_30$ is unsatisfiable.
  ```lean
  axiom unsat_6hole_cnf : (Geo.hexagonCNF (rlen := 30-1)).isUnsat
  ```

// TODO: Marijn describes the entire encoding. Should we,
// or should we focus more on the verification;
// for example our adjusted symmetry breaking?

== Lower Bounds

Checker checker
// TODO: Say something about pointset checker verification

== Final Theorem

#rect(height: 100%)[
#set text(size: 24pt)
```lean
axiom unsat_6hole_cnf : (Geo.hexagonCNF (rlen := 30-1)).isUnsat

theorem holeNumber_6 : holeNumber 6 = 30 :=
  le_antisymm (hole_6_theorem' unsat_6hole_cnf) (hole_lower_bound [
    (1, 1260),  (16, 743),  (22, 531),  (37, 0),    (306, 592),
    (310, 531), (366, 552), (371, 487), (374, 525), (392, 575),
    (396, 613), (410, 539), (416, 550), (426, 526), (434, 552),
    (436, 535), (446, 565), (449, 518), (450, 498), (453, 542),
    (458, 526), (489, 537), (492, 502), (496, 579), (516, 467),
    (552, 502), (754, 697), (777, 194), (1259, 320)
  ])
```
]

== Bibliography

#bibliography("main.bib", style: "chicago-author-date")