#import "@preview/touying:0.5.2": *
#import "@preview/cetz:0.2.2"
#import themes.metropolis: *

// Many slides adapted from https://www.cs.cmu.edu/~mheule/talks/6hole-TACAS.pdf

#let config = (
  aspect-ratio: "16-9",
  // config-common(handout: true),
  ..config-info(
    title: [Formal Verification of the Empty Hexagon Number],
    author: [
      Bernardo Subercaseaux¹, Wojciech Nawrocki¹, James Gallicchio¹,\
      Cayden Codel¹, *Mario Carneiro*#h(0em)¹, Marijn J. H. Heule¹
    ],
    date: [
      _Interactive Theorem Proving_ | September 9th, 2024\
      Tbilisi, Georgia
    ],
    institution: [¹ Carnegie Mellon University, USA]
  ),
  ..config-colors(
    primary: rgb("#eb811b"),
    primary-light: rgb("#d6c6b7"),
    secondary: rgb("#23373b"),
    neutral-lightest: rgb("#fafafa"),
    neutral-dark: rgb("#23373b"),
    neutral-darkest: rgb("#23373b"),
  )
)
#show: metropolis-theme.with(config)
#set text(size: 23pt)

#title-slide()

// WN: I think this should be first slide, not the 9-pt example;
// it is really confusing to look at a pointset
// without knowing what kind of structure one is looking for.

== Empty $k$-gons

Fix a set $S$ of points on the plane, _no three collinear_.
A *$bold(k)$-hole* is a convex $k$-gon with no point of $S$ in its interior.

// PERTURB THE POINTS
#align(center, components.side-by-side(
  cetz.canvas(length: 33%, {
    import cetz.draw: *
    set-style(circle: (fill: config.colors.neutral-darkest, stroke: none, radius: 0.05))
    on-layer(1, {
      circle((angle: 0deg, radius: 1), name: "a")
      circle((angle: 72deg, radius: 1), name: "b")
      circle((angle: 144deg, radius: 1), name: "c")
      circle((angle: 216deg, radius: 1), name: "d")
      circle((angle: 290deg, radius: 1), name: "e")
      circle((angle: 30deg, radius: 1.5))
      circle((angle: 240deg, radius: 1.5))
    })
    line("a", "b", "c", "d", "e", "a", fill: config.colors.primary.transparentize(20%))
    content((0, -1.5), "5-hole ✔")
    content((0, -2.0), "convex 5-gon ✔")
  }),
  cetz.canvas(length: 33%, {
    import cetz.draw: *
    set-style(circle: (fill: config.colors.neutral-darkest, stroke: none, radius: 0.05))
    on-layer(1, {
      circle((angle: 0deg, radius: 1), name: "a")
      circle((angle: 120deg, radius: 1), name: "b")
      circle((angle: 180deg, radius: 0.2), name: "c")
      circle((angle: 240deg, radius: 1), name: "d")
      circle((angle: 200deg, radius: 1.2))
    })
    line("a", "b", "c", "d", "a", fill: config.colors.primary-light.transparentize(20%))
    content((0, -1.5), "4-hole ✘")
    content((0, -2.0), "convex 4-gon ✘")
  }),
  cetz.canvas(length: 33%, {
    import cetz.draw: *
    set-style(circle: (fill: config.colors.neutral-darkest, stroke: none, radius: 0.05))
    on-layer(1, {
      circle((angle: 0deg, radius: 1), name: "a")
      circle((angle: 120deg, radius: 1), name: "b")
      circle((angle: 240deg, radius: 1), name: "c")
      circle((angle: 30deg, radius: 0.2))
    })
    line("a", "b", "c", "a", fill: config.colors.primary-light.transparentize(20%))
    content((0, -1.5), "3-hole ✘")
    content((0, -2.0), "convex 3-gon ✔")
  }),
))

// TOOO: speaker note: our points are never collinear

== 5 points must contain a 4-hole

#slide(repeat: 10, self => [
  #let (uncover,) = utils.methods(self)

  *Theorem* (Klein 1932). // WN: I don't think a citation exists for this
  Every 5 points in the plane contain a 4-hole. #pause

  _Proof._ By cases on the size of the convex hull.

  #components.side-by-side(
    uncover("3-", align(center, cetz.canvas(length: 33%, {
      import cetz.draw: *

      set-style(circle: (fill: config.colors.neutral-darkest, stroke: none, radius: 0.05))
      on-layer(1, {
        circle((angle: 0deg, radius: 1), name: "a")
        circle((angle: 72deg, radius: 1), name: "b")
        circle((angle: 144deg, radius: 1), name: "c")
        circle((angle: 216deg, radius: 1), name: "d")
        circle((angle: 290deg, radius: 1), name: "e")
      })
      line("a", "b", "c", "d", "e", "a")
      if 4 <= self.subslide {
        line("a", "b", "c", "d", "a", fill: config.colors.primary.transparentize(20%))
      }
    }))),
    uncover("5-", align(center, cetz.canvas(length: 33%, {
      import cetz.draw: *

      set-style(circle: (fill: config.colors.neutral-darkest, stroke: none, radius: 0.05))
      on-layer(1, {
        circle((angle: 0deg, radius: 1), name: "a")
        circle((angle: 90deg, radius: 1), name: "b")
        circle((angle: 180deg, radius: 1), name: "c")
        circle((angle: 270deg, radius: 1), name: "d")
        circle((angle: 60deg, radius: 0.5), name: "x")
      })
      line("a", "b", "c", "d", "a")
      if 7 <= self.subslide {
        line("a", "d", "c", "x", "a", fill: config.colors.primary.transparentize(20%))
      }
      if 6 <= self.subslide {
        line((angle: 0deg, radius: 1.5), (angle: 180deg, radius: 1.5), stroke: config.colors.primary)
      }
    }))),
    uncover("8-10", align(center, cetz.canvas(length: 33%, {
      import cetz.draw: *

      set-style(circle: (fill: config.colors.neutral-darkest, stroke: none, radius: 0.05))
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
      if 9 <= self.subslide {
        line((angle: xθ, radius: 1.5), (angle: yθ, radius: 1.5), stroke: config.colors.primary)
      }
      if 10 <= self.subslide {
        line("a", "x", "y", "c", "a", fill: config.colors.primary.transparentize(20%))
      }
    })))
  )
])

== 9 points with no 5-holes

#slide(
    // Hide header by making it background-coloured
    // config: config-colors(secondary: config.colors.neutral-lightest),
    align: center+horizon,
    repeat: 4,
    self => cetz.canvas({
  import cetz.draw: *
  set-style(circle: (fill: config.colors.neutral-darkest, stroke: none, radius: 1.2))
  scale(.1)
  on-layer(1, {
    let pts = (
      (1,  0,  "a"),
      (100, 0, "b"),
      (51, 88, "c"),

      (30, 40, "d"),
      (49, 10, "e"),
      (70, 40, "f"),

      (45, 26, "g"),
      (55, 26, "h"),
      (50, 35, "i"),
    )

    for (x, y, n) in pts {
      circle((x, y), name: n)
    }
  })
  if self.subslide > 1 {
    line("a", "b", "c", "a")
    line("d", "e", "f", "d")
    line("g", "h", "i", "g")
  }
  if self.subslide == 3 {
    line("a", "e", "h", "i", "d", "a", fill: config.colors.primary-light.transparentize(20%))
    content((25, -10), [5-hole ✘])
    content((25, -20), [convex 5-gon ✔])
  }
  if self.subslide == 4 {
    line("d", "e", "b", "h", "g", "d", fill: config.colors.primary-light.transparentize(20%))
    content((75, -10), [convex 5-gon ✘])
  }
}))

/////////// DONE ABOVE
/////////// WORK AREA BELOW

== The Happy Ending Problem

// TODO(WN): make #pause-gray gray out the things that came before

$g(k) =$ least $n$ s.t. any set of $n$ points must contain a *convex $bold(k)$-gon*

$h(k) =$ least $n$ s.t. any set of $n$ points must contain a *$bold(k)$-hole* #pause

We just showed $h(4) ≤ 5$ and $9 < h(5)$. #pause

*Theorem* @35erdos_combinatorial_problem_geometry.
For a fixed $k$, every _sufficiently large_ set of points contains a convex $k$-gon.
So all $g(k)$ are finite. #pause

*Theorem* @hortonSetsNoEmpty1983.
For any $k ≥ 7$, there exist arbitrarily large sets of points containing no $k$-holes.
So $h(7) = h(8) = … = ∞$.

== Known tight bounds

#table(
  columns: (auto, auto),
  inset: 5pt,
  stroke: none,
  [$h(3) = 3$ (trivial)],
  [$g(3) = 3$ (trivial)],
  [$h(4) = 5$ (Klein 1932)],
  [$g(4) = 5$ (Klein 1932)],
  [$h(5) = 10$ @Harborth1978],
  // TODO: see https://en.wikipedia.org/wiki/Happy_ending_problem#cite_note-4
  [$g(5) = 9$ (CITATION NEEDED)],
  [*$bold(h(6) = 30)$ @03overmars_finding_sets_points_empty_convex_6_gons @24heule_happy_ending_empty_hexagon_every_set_30_points*],
  [$g(6) = 17$ @szekeres_peters_2006],
) #pause

We formally verified all the above in $L∃∀N$. #pause

Upper bounds by combinatorial reduction to SAT. #pause

#[
#set par(first-line-indent: 1em, hanging-indent: 1em)
▸ We focused on $h(6)$.\ #pause
▸ $g(6)$ previously verified in Isabelle/HOL @10maric_formal_verification_modern_sat_solver_shallow_embedding_isabelle_hol.\ #pause
▸ Efficient SAT encoding of Heule & Scheucher speeds up $g(6)$ verification. #pause
]

Lower bounds by checking explicit sets of points.
  // TODO: Is this the first verification of the hole-tester algo?

== SAT-solving mathematics

*Reduction.* Show that a mathematical theorem is true
if a propositional formula φ is unsatisfiable.

*Solving.* Show that φ is indeed unsatisfiable using a SAT solver. #pause

▸ Solving is reliable, reproducible, and trustworthy:
formal proof systems (DRAT) and verified proof checkers (`cake_lpr`). #pause

▸ But reduction is problem-specific, and involves complex transformations:
_focus of our work_.

== Reduction from geometry to SAT

// TODO: make text shorter

// TODO(WN): pauses for the list
#set text(size: 23pt)
1. Points can be put in _canonical form_
   without removing $k$-holes.
   ```lean
   theorem symmetry_breaking {l : List Point} :
     3 ≤ l.length → PointsInGenPos l →
     ∃ w : CanonicalPoints, l ≼σ w.points
   ```
2. $n$ points in canonical form with no $6$-holes
   induce a propositional assignment that satisfies $φ_n$.
   ```lean
   theorem satisfies_hexagonEncoding {w : CanonicalPoints} :
     ¬σHasEmptyKGon 6 w → w.toPropAssn ⊨ Geo.hexagonCNF w.len
   ```
3. But $φ_30$ is unsatisfiable.
   ```lean
   axiom unsat_6hole_cnf : (Geo.hexagonCNF 30).isUnsat
   ```

== 1. Symmetry breaking

// TODO: add teh content

The sequence of six steps from Fig. 5
(transformation into `CanonicalPoints`);
make it an animation.


== 2. SAT encoding

// TODO: add teh content

- Introduce $σ$ variables
- Show scary picture of full encoding (?)
- Talk about cap-cup clauses; copy slide 14/21 from Marijn

== 3. Running the SAT solver

// TODO: add teh content

How many clauses, how long it took, cluster compute amount (from 'Running the CNF')

== Lower bounds

// TODO(MARIO): put someting in this slide, without describing the algorithm
// TODO(Bernardo): draw pictures of the algorithm

$cal(O)("sth")$ time, $cal(O)("sth")$ space algorithm @90dobkin_searching_empty_convex_polygons

We verified it, and used it to check the lower bounds.

== Final theorem

#[
#set text(size: 24pt)
```lean
axiom unsat_6hole_cnf : (Geo.hexagonCNF 30).isUnsat

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

#bibliography("main.bib", style: "chicago-author-date", title: none)