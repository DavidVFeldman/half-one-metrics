# Half-One Metrics and the Vertices of the Metric Body

David Victor Feldman (University of New Hampshire) and Eric R. Kehoe (Zoetis, Inc.)

Companion repository for the paper *Half-One Metrics and the Vertices of the Metric Body:
Density, Enumeration, and Angle*. The paper asks how much of the metric body — the polytope
of pseudometrics bounded by 1 on n points — the half-one metrics account for, in three
inequivalent senses: among themselves (a theorem: the proportion of half-one metrics that
are extreme tends to 1), among all vertices (an exact census for n ≤ 6: 19, 259, 27263),
and by exterior solid angle (a conjecture, with the supporting experiment reported).

## Layout

- `paper/` — the article (`paper4.tex`, `paper4.pdf`) and its figures.
- `lean/` — a Lean 4 formalization (`HalfOne`), verifying the paper's structural theorems
  and census counts; see `lean/LEDGER.md` for the item-by-item status and axiom map, and
  the paper's introduction for the precise scope. Requires the toolchain in
  `lean/lean-toolchain` and Mathlib as pinned in `lean/lake-manifest.json`; build with
  `lake exe cache get && lake build` inside `lean/`.
- `verify/` — the conventional computations: exhaustive enumeration of extreme half-one
  metrics through n = 8 in independent implementations, the vertex census machinery,
  Monte Carlo sampling for the deficit and the exterior-angle experiment, and the scripts
  behind every table in the paper.

## Verification summary

Every theorem of the formalization compiles with no `sorry` and axioms
`propext`, `Classical.choice`, `Quot.sound`, with one disclosed exception: the census
counts at n = 6 and n = 7 are established by Lean's compiled evaluator (`native_decide`),
which additionally trusts the compiler (`Lean.ofReduceBool`, `Lean.trustCompiler`). The
counts at n ≤ 5 are kernel-checked. The extremality criterion for half-one metrics is the
companion paper's theorem and is quoted, not reproved; the formal census counts graphs
satisfying the combinatorial predicate (no bipartite component of the edge graph).

The Lean development was produced jointly with Aristotle (Harmonic); see
`lean/ARISTOTLE.md`.

## Companion papers

This is Paper IV of a four-paper series extracted from E. R. Kehoe's dissertation
(*Pseudometrics, the Complex of Ultrametrics, and Iterated Cycle Structures*, University of
New Hampshire, 2019, scholars.unh.edu/dissertation/2451).
