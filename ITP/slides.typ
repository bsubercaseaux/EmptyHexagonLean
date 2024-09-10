#import "@preview/touying:0.5.2": *
#import "@preview/cetz:0.2.2"
#import themes.metropolis: *

// Like cetz.draw.grid, but allows independently specifying
// where the grid lines should be placed (`from`, `to`),
// and how far they should extend (`froml`, `tol`).
#let grid2(from, to, froml, tol, step: 1, ..style) = {
  import cetz.draw: line
  let (fx, fy) = from
  let (tx, ty) = to
  let (flx, fly) = froml
  let (tlx, tly) = tol
  assert(fx <= tx)
  assert(fy <= ty)
  assert(flx <= tlx)
  assert(fly <= tly)
  assert(flx <= fx)
  assert(tx <= tlx)
  assert(fly <= fy)
  assert(ty <= tly)
  let eps = 0.000000000001
  let x = fx
  while x <= tx + eps {
    line((x, fly), (x, tly), ..style)
    x += step
  }

  let y = fy
  while y <= ty + eps {
    line((flx, y), (tlx, y), ..style)
    y += step
  }
}

#let lean = "Lean"
#let thin = h(3em/18)

// Many slides adapted from https://www.cs.cmu.edu/~mheule/talks/6hole-TACAS.pdf

#let config = (
  aspect-ratio: "16-9",
  // config-common(handout: true),
  ..config-info(
    title: [Formal Verification of the Empty Hexagon Number],
    author: [
      Bernardo Subercaseaux¹, Wojciech Nawrocki¹, James Gallicchio¹,\
      Cayden Codel¹, #underline[Mario Carneiro]#h(0em)¹, Marijn J. H. Heule¹
    ],
    date: [
      _Interactive Theorem Proving_ | September 9th, 2024\
      Tbilisi, Georgia
    ],
    institution: [¹ Carnegie Mellon University, USA]
  ),
  ..config-colors(
    primary: rgb("#fb912b"),
    primary-light: rgb("#d6c6b7"),
    secondary: rgb("#fafafa"),
    neutral-lightest: rgb("#13272b"),
    neutral-dark: rgb("#fafafa"),
    neutral-darkest: rgb("#fafafa"),
  )
)
#show: metropolis-theme.with(config)
#set text(size: 23pt)
#set raw(theme: "Monokai Dark.tmTheme")

#title-slide()

// WN: I think this should be first slide, not the 9-pt example;
// it is really confusing to look at a pointset
// without knowing what kind of structure one is looking for.

== Empty $k$-gons

Fix a set $S$ of points on the plane, _no three collinear_.
A *$bold(k)$-hole* is a convex $k$-gon with no point of $S$ in its interior.

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
    line("a", "b", "c", "d", "e", "a", fill: config.colors.primary.transparentize(20%), stroke: config.colors.primary)
    content((0, -1.5), "5-hole ✔")
    content((0, -2.0), "convex 5-gon ✔")
  }),
  cetz.canvas(length: 33%, {
    import cetz.draw: *
    set-style(circle: (fill: config.colors.neutral-darkest, stroke: none, radius: 0.05))
    on-layer(1, {
      circle((angle: 1deg, radius: 1), name: "a")
      circle((angle: 120deg, radius: 1), name: "b")
      circle((angle: 180deg, radius: 0.2), name: "c")
      circle((angle: 240deg, radius: 1), name: "d")
      circle((angle: 200deg, radius: 1.2))
    })
    line("a", "b", "c", "d", "a", fill: config.colors.primary-light.transparentize(20%), stroke: config.colors.primary-light)
    content((0, -1.5), "4-hole ✘")
    content((0, -2.0), "convex 4-gon ✘")
  }),
  cetz.canvas(length: 33%, {
    import cetz.draw: *
    set-style(circle: (fill: config.colors.neutral-darkest, stroke: none, radius: 0.05))
    on-layer(1, {
      circle((angle: 359deg, radius: 1), name: "a")
      circle((angle: 120deg, radius: 1), name: "b")
      circle((angle: 240deg, radius: 1), name: "c")
      circle((angle: 30deg, radius: 0.2))
    })
    line("a", "b", "c", "a", fill: config.colors.primary-light.transparentize(20%), stroke: config.colors.primary-light)
    content((0, -1.5), "3-hole ✘")
    content((0, -2.0), "convex 3-gon ✔")
  }),
))

// TOOO: speaker note: our points are never collinear

== 5 points must contain a 4-hole

#slide(repeat: 10, self => [
  #let (uncover,) = utils.methods(self)

  *Theorem* (Klein 1932). // WN: I don't think a citation exists for this
  Every set of 5 points in the plane contains a 4-hole. #pause

  _Proof._ By cases on the size of the convex hull.

  #components.side-by-side(
    uncover("3-", align(center, cetz.canvas(length: 33%, {
      import cetz.draw: *

      set-style(circle: (fill: config.colors.neutral-darkest, stroke: none, radius: 0.05),
      line: (stroke: config.colors.neutral-darkest))
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

      set-style(circle: (fill: config.colors.neutral-darkest, stroke: none, radius: 0.05),
      line: (stroke: config.colors.neutral-darkest))
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
        line((angle: 0deg, radius: 1.5), (angle: 180deg, radius: 1.5), stroke: (paint: config.colors.primary, thickness: 1.5pt, dash: "dashed"))
      }
    }))),
    uncover("8-10", align(center, cetz.canvas(length: 33%, {
      import cetz.draw: *

      set-style(circle: (fill: config.colors.neutral-darkest, stroke: none, radius: 0.05),
      line: (stroke: config.colors.neutral-darkest))
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
        line((angle: xθ, radius: 1.5), (angle: yθ, radius: 1.5), stroke: (paint: config.colors.primary, thickness: 1.5pt, dash: "dashed"))
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
  set-style(circle: (fill: config.colors.neutral-darkest, stroke: none, radius: 1.2),
  line: (stroke: config.colors.neutral-darkest))
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

== The Happy Ending Problem

#slide(
  config: config-methods(cover: utils.semi-transparent-cover.with(alpha: 85%)),
  self => [
    // WN: Not sure about this uncover dance..
    #uncover("1, 3, 5", [$g(k) =$ least $n$ s.t. any set of $n$ points must contain a *convex $bold(k)$-gon*])

    #uncover("1, 2, 4, 5", [$h(k) =$ least $n$ s.t. any set of $n$ points must contain a *$bold(k)$-hole*])

    #uncover("2, 5", [We just showed $h(4) ≤ 5$ and $9 < h(5)$])

    #uncover("3, 5", [
      *Theorem* @35erdos_combinatorial_problem_geometry.
      For a fixed $k$, every _sufficiently large_ set of points contains a convex $k$-gon.
      So all $g(k)$ are finite.
    ])

    #uncover("4, 5", [
      *Theorem* @hortonSetsNoEmpty1983.
      For any $k ≥ 7$, there exist arbitrarily large sets of points containing no $k$-holes.
      So $h(7) = h(8) = … = ∞$.
    ])
  ]
)

== Known tight bounds

// TODO: This slide is too wordy

#table(
  columns: (auto, auto),
  inset: 5pt,
  stroke: none,
  [$h(3) = 3$ (trivial)],
  [$g(3) = 3$ (trivial)],
  [$h(4) = 5$ (Klein 1932)],
  [$g(4) = 5$ (Klein 1932)],
  [$h(5) = 10$ @Harborth1978],
  [$g(5) = 9$ (Makai 1930s)],
  [*$bold(h(6) = 30)$ @03overmars_finding_sets_points_empty_convex_6_gons @24heule_happy_ending_empty_hexagon_every_set_30_points*],
  [$g(6) = 17$ @szekeres_peters_2006],
) #pause

We formally verified all the above in #lean. #pause

Upper bounds by combinatorial reduction to SAT. #pause

#[
#set par(first-line-indent: 1em, hanging-indent: 1em)
▸ We focused on $h(6)$.\ #pause
▸ $g(6)$ previously verified in Isabelle/HOL @19maric_fast_formal_proof_erdos_szekeres_conjecture_convex_polygons_most_six_points.\ #pause
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

#slide(
  config: config-methods(cover: (self: none, body) => box(scale(x: 0%, body))),
  self => [
    #set text(size: 23pt)
    1. Discretize from continuous coordinates in $ℝ²$ to boolean variables. #pause
    2. Points can be put in _canonical form_
       without removing $k$-holes.
       ```lean
       theorem symmetry_breaking {l : List Point} :
         3 ≤ l.length → PointsInGenPos l →
         ∃ w : CanonicalPoints, l ≼σ w.points
       ``` #pause
    3. $n$ points in canonical form with no $6$-holes
       induce a propositional assignment that satisfies $φ_n$.
       ```lean
       theorem satisfies_hexagonEncoding {w : CanonicalPoints} :
         ¬σHasEmptyKGon 6 w → w.toPropAssn ⊨ Geo.hexagonCNF w.len
       ``` #pause
    4. But $φ_30$ is unsatisfiable.
       ```lean
       axiom unsat_6hole_cnf : (Geo.hexagonCNF 30).isUnsat
       ```
  ]
)

== Discretization with triple-orientations

#let fig = align(center, cetz.canvas({
  import cetz.draw: *
  set-style(circle: (fill: config.colors.neutral-darkest, stroke: none, radius: 0.1))
  scale(3.2)

  on-layer(1, {
    let pts = (
      (0, 0, "p"), (1, 1, "s"), (2, 1, "q"), (1.2, 2, "r"), (1.8, 1.8, "t")
    )
    for (x, y, n) in pts {
      circle((x, y), name: n)
      content((x, y+0.015), [#set text(fill: config.colors.neutral-lightest, size: 20pt); $#n$])
    }
  })

  let (cg, cb, cr) = (green, blue, red).map(c => c.desaturate(20%))
  line("p", "r", "q", stroke: cg, mark: (end: "stealth", fill: cg))
  line("p", "s", "t", stroke: cb, mark: (end: "stealth", fill: cb))
  line("r", "s", "q", stroke: cr, mark: (end: "stealth", fill: cr))
}))

#components.side-by-side(
  columns: (1fr, 18em),
  fig,
  [
    $ σ(p,r,q) &= 1  &("clockwise") \
      σ(p,s,t) &= 0  &("collinear") \
      σ(r,s,q) &= -1#h(1em) &("counter-clockwise") $
  ]
) #pause

#align(center, [
  $∃$ $k$-hole ⇔ a propositional formula over $σ(a,b,c)$ is satisfiable
])

// WN: I think cap-cup here would be too deep into the weeds

== Symmetry breaking

#slide(repeat: 6, align: center+horizon, self => [
  #let fig = cetz.canvas({
    import cetz.draw: *
    let pts = (
      ((-1.3, 0.25), (-1.3, 0.9), (-0.7, -0.45), (-0.35, 0.35), (-0.35, -0.8), (0.6, 0.5), (0.9, -0.6), (1.4, 1.1), (0.6, -1.1),),
      ((-1.09601563215555, -0.7424619411597272), (-1.5556349648261614, -0.28284245828783905), (-0.17677682816699475, -0.8131727694796578), (-0.49497474683057663, 8.087761060870946e-08), (0.3181979186635819, -0.8131728503572684), (0.07071080521204193, 0.7778174477512475), (1.0606602064416402, 0.21213186104679588), (0.21213232320457065, 1.767766918304512), (1.202081470247393, -0.3535535870103234),),
      ((0.4596193326706113, -0.45961948287188814), (0.0, 0.0), (1.3788581366591666, -0.5303303111918187), (1.0606602179955846, 0.28284253916544966), (1.8738328834897433, -0.5303303920694293), (1.6263457700382034, 1.0606599060390867), (2.6162951712678018, 0.4949743193346349), (1.767767288030732, 2.0506093765923508), (2.7577164350735544, -0.07071112872248436),),
      ((-1.00000032679495, 2.1757135283877527), (0, 3.85), (-0.3846155721840648, 0.7252377698715973), (0.2666664916498519, 0.9428090005013866), (-0.2830190444100679, 0.5336655199142649), (0.6521736801480853, 0.6148753963780468), (0.1891890199433349, 0.3822198699068886), (1.1599996167350177, 0.5656853177286622), (-0.025641189145902285, 0.3626188636662086),),
      ((-1.00000032679495, 2.1757135283877527), (-1.2, 3.85), (-0.3846155721840648, 0.7252377698715973), (0.2666664916498519, 0.9428090005013866), (-0.2830190444100679, 0.5336655199142649), (0.6521736801480853, 0.6148753963780468), (0.1891890199433349, 0.3822198699068886), (1.1599996167350177, 0.5656853177286622), (-0.025641189145902285, 0.3626188636662086),),
      ((-1.2, 3.85), (-1.00000032679495, 2.1757135283877527), (-0.3846155721840648, 0.7252377698715973), (-0.2830190444100679, 0.5336655199142649), (-0.025641189145902285, 0.3626188636662086), (0.1891890199433349, 0.3822198699068886), (0.2666664916498519, 0.9428090005013866), (0.6521736801480853, 0.6148753963780468), (1.1599996167350177, 0.5656853177286622),),
    )
    let extents = (
      ((-1.7, -1.3), (1.7, 2.3)),
      ((-1.7, -1.3), (1.7, 2.3)),
      ((-0.7, -1.3), (3.1, 2.3)),
      ((-1.2, -0.2), (2.4, 2.9)),
      ((-1.5, -0.2), (2.4, 3.7)),
      ((-1.5, -0.2), (2.4, 3.7)),
    )
    let regions = (
      (("1", "3", "4", "2", "1"), ("3", "5", "9", "7", "6", "4", "3"), ("6", "7", "8", "6"), ("2", "4", "6", "8", "2"),),
      (("1", "3", "4", "2", "1"), ("3", "5", "9", "7", "6", "4", "3"), ("6", "7", "8", "6"), ("2", "4", "6", "8", "2"),),
      (("1", "3", "4", "2", "1"), ("3", "5", "9", "7", "6", "4", "3"), ("6", "7", "8", "6"), ("2", "4", "6", "8", "2"),),
      (("1", "3", "4", "b", "a", "1"), ("3", "5", "9", "7", "6", "4", "3"), ("6", "7", "8", "6"), ("4", "6", "8", "c", "b", "4"),),
      (("1", "3", "4", "2", "1"), ("3", "5", "9", "7", "6", "4", "3"), ("6", "7", "8", "6"), ("2", "4", "6", "8", "2"),),
      (("1", "2", "3", "7", "1"), ("3", "4", "5", "6", "8", "7", "3"), ("6", "9", "8", "6"), ("7", "8", "9", "1", "7"),),
    )

    scale(3.2)

    // Grid and axes
    let ((efx, efy), (etx, ety)) = extents.at(self.subslide - 1)
    on-layer(-1, {
      grid2(
        (calc.ceil(efx), calc.ceil(efy)), (calc.floor(etx), calc.floor(ety)),
        (efx, efy), (etx, ety),
        stroke: (thickness: 0.2pt, paint: config.colors.secondary.transparentize(50%), dash: "dashed"))
    })
    set-style(line: (stroke: (paint: config.colors.neutral-darkest, thickness: 1.5pt)))
    line((efx, 0), (etx, 0), mark: (end: "stealth", fill: config.colors.neutral-darkest))
    line((0, efy), (0, ety), mark: (end: "stealth", fill: config.colors.neutral-darkest))
    content((etx -0.18, -0.2), $x$)
    content((0.2, ety -0.1), $y$)

    // Points
    on-layer(1, {
      set-style(circle: (fill: config.colors.neutral-darkest, stroke: none, radius: 0.1))
      for (n, (x, y)) in pts.at(self.subslide - 1).enumerate(start: 1) {
        if self.subslide == 4 and n == 2 {
          // Point at infinity gets special color
          circle((x, y), name: str(n), fill: config.colors.primary)
        } else {
          circle((x, y), name: str(n))
        }
        content((x, y), [#set text(fill: config.colors.neutral-lightest, size: 20pt); #str(n)])
      }
    })

    // Convex regions
    on-layer(-1, {
      set-style(line: (stroke: none))
      let colors = (red, orange, blue, green).map(c => c.transparentize(30%))
      // Extra convex regions at infinity
      if self.subslide == 4 {
        circle((-1.00000032679495, 2.7), name: "a", radius: 0)
        circle((0.2666664916498519, 2.7), name: "b", radius: 0)
        circle((1.1599996167350177, 2.7), name: "c", radius: 0)
        circle((-0.1, 3.4), name: "x", radius: 0)
        circle((0, 3.4), name: "y", radius: 0)
        circle((0.1, 3.4), name: "z", radius: 0)
        line("x", "y", "2", "x", fill: colors.at(0))
        line("y", "z", "2", "y", fill: colors.at(3))
        line("a", "x", stroke: (thickness: 2pt, dash: "dotted", paint: colors.at(0)))
        line("b", "y", stroke: (thickness: 2pt, dash: "dotted", paint: colors.at(0)))
        line("c", "z", stroke: (thickness: 2pt, dash: "dotted", paint: colors.at(3)))
      }

      for (r, c) in regions.at(self.subslide - 1).zip(colors) {
        line(..r, fill: c)
      }
    })

    // Equal-x marker lines
    if self.subslide == 1 {
      let ((_, yf), (_, yt)) = extents.at(0)
      let (x4, _) = pts.at(0).at(3)
      let (x6, _) = pts.at(0).at(5)
      set-style(line: (stroke: (thickness: 2pt, dash: "dashed", paint: red)))
      line((x4, yf), (x4, yt))
      line((x6, yf), (x6, yt))
    }
  })

  #let captions = (
    [Starting set of points.],
    [Rotation ensures distinct $x$.],
    [Translate leftmost point to $(0,0)$.\
    Ensures nonnegative $x$.],
    [Map $(x,y) ↦ (y/x, 1/x)$.],
    [Bring point at $∞$ back.],
    [Relabel in order of increasing $x$.],
  )

  #components.side-by-side(
    columns: (15em, 1fr),
    captions.at(self.subslide - 1),
    fig,
  )
])

// TODO: Maybe rm this slide? It's not adding much
== Symmetry breaking: result

Points now in normal form. #pause

Normalization drastically reduces search space for SAT solver. #pause

```lean
structure CanonicalPoints where
  leftmost : Point
  rest : List Point
  sorted' : (leftmost :: rest).Sorted (·.x < ·.x)
  gp' : ListInGenPos (leftmost :: rest)
  oriented : rest.Pairwise (σ leftmost · · = .ccw)
  lex : σRevLex rest
```

== Running the SAT solver

CNF formula produced directly from executable #lean definition. #pause

To verify $h(6) ≤ 30$:\ #pause
▸ CNF with 65#(thin)092 variables and 436#(thin)523 clauses\ #pause
▸ partitioned into 312#(thin)418 subproblems\ #pause
▸ each subproblem solved by CaDiCaL 1.9.5\ #pause
▸ unsatisfiability proofs checked on-the-fly by `cake_lpr`\ #pause
▸ 25#(thin)876.5 CPU hours on Bridges 2 cluster of Pittsburgh Supercomputing Center

== Lower bounds

To prove theorems of the form $n <= h(k)$, we must show that there is a set of $n-1$ points with no $k$-holes.

Naive solution is $cal(O)(n^(k+1)log k)$ time.

We verified an $cal(O)(n^3)$ algorithm from\ @90dobkin_searching_empty_convex_polygons.

#slide(align: center+horizon, repeat: 7, self => cetz.canvas({
  import cetz.draw: *

  let radius = 0.2
  set-style(circle: (fill: config.colors.neutral-darkest, stroke: none, radius: radius))
  set-style(line: (stroke: (thickness: 3pt)))
  let pts = (
    ((-9, -2), (-5, 7)),
    ((7, -4), (18, -3), (16, 0), (12, 1), (23, 3), (11, 3), (17, 8), (9, 5), (2, 4))
  )
  let (left, right) = pts.map(pts => pts.map(((x, y)) => (x/2,y)))
  let chain = (0, 3, 5, 7, 8).map(i => right.at(i))
  for (x, y) in left {
    circle((x, y), radius: if self.subslide > 1 { 0.15 } else { radius })
  }
  if self.subslide == 7 {
    line(..((0,0), ..chain), fill: aqua.transparentize(30%), stroke: none)
  }
  if self.subslide > 1 {
    line((0, -4), (0, 8), stroke: (dash: "dashed", paint: config.colors.neutral-darkest))
  }
  if self.subslide == 5 {
    line(right.at(0), right.at(3), stroke: (dash: "dashed", paint: aqua, thickness: 4pt))
    line(right.at(4), right.at(7), stroke: (dash: "dashed", paint: red, thickness: 4pt))
  }
  if self.subslide == 6 {
    line(..chain, stroke: (dash: "dashed", paint: aqua, thickness: 4pt))
  }
  for (n, (x, y)) in ((0,0), ..right).enumerate() {
    if self.subslide > 3 {
      let (nx, ny) = if n < right.len() { right.at(n) } else { (0, 0) }
      let thick = if self.subslide == 6 and n == 8 { 1pt } else { 4pt }
      line((x, y), (nx, ny), stroke: (paint: config.colors.neutral-darkest, thickness: thick))
    }
    if n != 0 {
      if self.subslide == 3 {
        line((x, y), (0, 0), stroke: (paint: config.colors.neutral-darkest))
      }
      circle((x, y), name: str(n), radius: if self.subslide > 1 { 0.3 } else { radius })
      if self.subslide > 2 {
        content((x, y), [#set text(fill: config.colors.neutral-lightest, size: 20pt); #str(n)])
      }
    }
  }
  circle((0, 0), name: "p", radius: if self.subslide > 1 { 0.4 } else { radius })
  if self.subslide > 1 {
    content((0, .13 /* HACK */), [#set text(fill: config.colors.neutral-lightest, size: 20pt); $p$])
  }
}))


== Final theorem

#[
#set text(size: 24pt)
```lean
axiom unsat_6hole_cnf : (Geo.hexagonCNF 30).isUnsat

theorem holeNumber_6 : holeNumber 6 = 30 :=
  le_antisymm
   (hole_6_theorem' unsat_6hole_cnf)
   (hole_lower_bound [
    (1, 1260),  (16, 743),  (22, 531),  (37, 0),    (306, 592),
    (310, 531), (366, 552), (371, 487), (374, 525), (392, 575),
    (396, 613), (410, 539), (416, 550), (426, 526), (434, 552),
    (436, 535), (446, 565), (449, 518), (450, 498), (453, 542),
    (458, 526), (489, 537), (492, 502), (496, 579), (516, 467),
    (552, 502), (754, 697), (777, 194), (1259, 320)])
```
]

#slide(
    // Hide header by making it background-coloured
    // config: config-colors(secondary: config.colors.neutral-lightest),
    align: center+horizon,
    repeat: 2,
    self => cetz.canvas({
  import cetz.draw: *
  set-style(circle: (fill: config.colors.neutral-darkest, stroke: none, radius: 1.2),
  line: (stroke: config.colors.neutral-darkest))
  scale(.1)
  let pts = (
    (1.2, ((1-10, 1260+10), (37-10, 0-10), (1259+10, 320))),
    (1.2, ((16, 743), (22, 531), (777, 194), (754, 697))),
    (1.2, ((306, 592), (310, 531), (371, 487), (516, 467), (552, 502), (496, 579), (396, 613))),
    (1.0, ((366, 552), (374, 525), (450, 498), (492, 502), (489, 537), (446, 565), (392, 575))),
    (0.8, ((410, 539), (426, 526), (449, 518), (458, 526), (453, 542), (434, 552), (416, 550))),
    (0.9, ((436, 535),)),
  )
  on-layer(1, {
    for (i, (radius, cycle)) in pts.enumerate() {
      for (j, (x, y)) in cycle.enumerate() {
        circle(((y+x/4)/5, x/11), radius: radius, name: str(i)+"-"+str(j))
      }
    }
  })
  if self.subslide > 1 {
    for (i, (_, cycle)) in pts.enumerate() {
      let cycle = range(cycle.len())
      cycle.push(0)
      line(..cycle.map(x => str(i)+"-"+str(x)))
    }
  }
}))

== Bibliography

#bibliography("main.bib", style: "chicago-author-date", title: none)
