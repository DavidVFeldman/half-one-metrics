# LEDGER.md — Paper IV formalization, Rounds 1–5

Reconstructed from a full audit of the returned tree (the tarball referenced this file but
did not contain it). Statement fidelity was checked line-by-line against the commission's
master file; every commissioned statement below is verbatim except where a discrepancy is
explicitly recorded. "closed" claims below are claims about the returned source; the
compiled + `#print axioms` confirmation happens on the commissioning side and is what this
ledger is for.

Axiom baseline: `propext`, `Classical.choice`, `Quot.sound` (clean).

| item | theorem | status | axioms beyond baseline | notes |
|---|---|---|---|---|
| R1.1 | `adj_symm`, `adj_irrefl`, `gammaAdj_symm` | closed | — | `HalfOne/Basic.lean` |
| R1.2 | `pert_bound` | closed | — | statement verbatim |
| R1.3 | `pert_additive` | closed | — | verbatim |
| R1.4 | `one_degeneracy` | closed | — | verbatim |
| R1.5 | `twins_iff_isolated` | closed | — | verbatim |
| R1.6 | `twins_not_good` | closed | — | verbatim |
| R1.7 | `qlevel_feasible_count` | closed | — | verbatim; closed-form sum, not induction |
| R2.1 | `upper_half` | closed | — | verbatim; single-coordinate perturbation as planned |
| R2.2 | `value_sets` | closed | — | verbatim; handles the `IsEmpty (Edge n)` corner the commission missed |
| R3.1 | `walkCount_pos_iff` | closed | — | verbatim |
| R3.2 | `good_iff_goodWalk` | closed | — | verbatim; proved via a parity double-cover (`parityGraph`), cleaner than the commissioned parity-coloring plan |
| R3.3 | `odd_walk_bound` | closed | — | verbatim; via the SHARPER `odd_walk_bound_two` (bound 2·#nodes), commission's 3·#nodes derived from it |
| R3.4 | `goodB_correct` | closed | — | verbatim spec; implementation replaced per commission §0.4 by a bitmask parity-BFS (`goodBM` on `graphMask`), correctness chain `goodB_eq` → `piter_spec` |
| R3.5 | `census4`, `census5` | closed | — | kernel `decide +kernel` |
| R3.6 | `census6` | closed-with-disclosure | `Lean.ofReduceBool` | `native_decide`; kernel `decide` fails at the ENUMERATION (`Multiset.pi` reduction overflows), not the checker — consistent with commission trap 4 |
| R3.7 | `census7` | reported | (was `sorry`) | stretch; not proved. Removed from the default build in this repair pass so `lake build` is sorry-free; statement preserved in a comment. `HalfOne/Fast.lean` was built as the intended vehicle (`census_eq_countPow` + `goodBMfast`) but the final `native_decide` was not committed |
| R4.1 | `twin_count_single` | closed | — | verbatim; via generic `card_filter_of_extension` (`HalfOne/Counting.lean`) |
| R4.2 | `twin_count_shared` | closed | — | verbatim; from `twin_count_shared_gen` |
| R4.3 | `twin_count_disjoint` | closed | — | verbatim; from `twin_count_disjoint_gen` |
| R4.4 | `twin_bound` | closed | — | verbatim; Bonferroni assembled through `twin_count_pair` |
| R5.1 | `density_implication` | **closed, hypothesis corrected** | — | see below |
| — | `density_implication_Mended_false` | closed (falsification) | — | see below |
| — | `census4_good` … `census6_good` | closed / closed-with-disclosure | as parent census | the `Good`-form restatements in the master file |

## The R5 report: the commissioned statement was false, and the commission was at fault

The commissioned `Mended` read

    ∀ j k, adj G i j → adj G i k → j ≠ k → ∀ (hij : _) (hik : _), GReach …

with the two binder types elided. They elaborate to `j < i` and `k < i` — so `Mended G i`
constrains only pairs of neighbours *smaller than* `i`, a much weaker condition than
intended. Aristotle:

1. proved the literal statement **false** (`density_implication_Mended_false`) with a
   five-point counterexample — triangle {0,1,2} plus pendants {2,3}, {2,4} — which is
   connected, has a claw at 2, satisfies the botched `Mended` for every vertex, and is not
   `Good` because the edge {0,1} is Γ-isolated;
2. defined the intended hypothesis `MendedAt` (any two half-length edges through `i` are
   Γ-co-component) in `Defs.lean`;
3. proved `density_implication` with `MendedAt`.

Every property of the counterexample was re-verified independently in Python on the
commissioning side, including the decisive one: the counterexample **fails genuine
mending** (edges {0,1} and {0,2} at vertex 0 lie in different Γ-components). So the
falsification indicts only the commission's Lean encoding — trap 2 of the commission,
which flagged exactly these dependent binders and licensed a restatement — and not the
paper. The paper's prose definition of mending is `MendedAt`; thm:density is untouched.

This is the "report rather than repair" protocol operating as designed, with the report
carried, unusually and correctly, as a theorem.

## Repairs applied on the commissioning side (this pass)

1. `census7` (`sorry`) and its dependent `census7_good` removed from the default build;
   statements preserved in comments. `lake build` of the returned tree was red only because
   of this sorry; nothing else in the tree is incomplete.
2. This LEDGER.md written (the returned tree referenced it but did not include it).
3. `HalfOne/Fast.lean` is imported by nothing but is inside the build globs; it compiles
   (it exists to serve R3.7) and is retained for the next round.

## Residue for a next round, if wanted

- R3.7 via `Fast`: `census7 := by rw [census_eq_countPow]; native_decide` (or the
  `goodBMfast` composition), closed-with-disclosure at best. Optional: n = 7 is already
  double-computed conventionally and the paper's warrant labels do not change.
- Upgrading `census6` to kernel: would need a `Fintype (HGraph 6)` enumeration that kernel-
  reduces (e.g. `Fin (2^15)` + the proved bijection `maskGraph`/`graphMask` already in
  `Fast.lean`/`Checker.lean`). Half a round of work; only the disclosure line changes.
- Round 6 of the commission (probability bounds of thm:density; `prop:descent`) remains
  uncommissioned.

# Round 6

Executed against `ROUND6_COMMISSION.md`.  Axiom baseline unchanged: `propext`,
`Classical.choice`, `Quot.sound`.  Timings are wall clock on the build machine,
measured by elaborating each theorem in a file of its own that imports
`HalfOne.Checker` and `HalfOne.Fast`; the import-only baseline for such a file is
**20 s**, which is included in the raw figures below and subtracted in the "net"
column.

## Tier A — the integrated census

| item | theorem / task | status | axioms beyond baseline | notes |
|---|---|---|---|---|
| A1 | `lake build` as shipped | **reported** | — | The tree as shipped did **not** build: `HalfOne/Census.lean` carried `theorem census7 … := by sorry`, contrary to the commission's "the tree as shipped has no sorries". Everything else compiled. Reported, then repaired under A1′ below |
| A1′ | `census7` | **closed-with-disclosure** | `Lean.ofReduceBool`, `Lean.trustCompiler` | `HalfOne/Census.lean` now imports `HalfOne.Fast` and proves `census7 := by rw [census_eq_fast]; native_decide`. This is the residue item flagged at the end of Round 5, taken with the `census_eq_fast` route |
| A1a | `census4` (`decide +kernel`) | closed | — | 16 s raw / **≈ 0 s net** (within measurement noise of the import baseline) |
| A1b | `census5` (`decide +kernel`) | closed | — | 337 s raw / **≈ 317 s net** |
| A1c | `census6` (`native_decide`) | closed-with-disclosure | `Lean.ofReduceBool`, `Lean.trustCompiler` | 192 s raw / **≈ 172 s net** |
| A1d | `census7` (`census_eq_fast` + `native_decide`) | closed-with-disclosure | `Lean.ofReduceBool`, `Lean.trustCompiler` | 132 s raw / **≈ 112 s net** |
| — | `HalfOne.Census` module, cold build | — | — | 503 s before A1′, **644 s** after (the module carries all four census theorems) |
| A2 | `#print axioms` sweep | closed | see right | Baseline only for `census4`, `census5`, `census4_good`, `census5_good`, `goodB_correct`, `density_implication`, `upper_half`, `value_sets`, `twin_bound`, `qlevel_feasible_count`. Baseline + `Lean.ofReduceBool`, `Lean.trustCompiler` for `census6`, `census7`, `census6_good`, `census7_good` — exactly the expectation, except that the disclosure covers `census6`/`census6_good` too (as Round 3 already recorded) and that `Lean.trustCompiler` accompanies `Lean.ofReduceBool` in this toolchain |
| A3 | kernel fallback for `census6` | not needed | — | `census6` was already `native_decide` in the shipped tree; no kernel run was attempted, no fallback taken |
| A4 | `bench/Y.lean` | untouched | — | No `bench/` directory exists in the shipped tree; nothing was touched. The root-level `Y.lean`, `K5.lean`, `K6.lean`, `N7.lean` are outside the build globs and were also left untouched |

## Tier B — the three counting bounds behind thm:density

Build integration choice (recorded per the commission): `Round6.lean` was **moved
to `HalfOne/Round6.lean` and imported from the master file** `HalfOne.lean`
(rather than extending the globs). A second new module, `HalfOne/Blocks.lean`,
holds the generic engine the commission anticipated: `card_split`, `card_indep`
(`#(p ∧ q) · 2^|α| = #p · #q`), `local_bound`, and `block_bound` — a product
bound over an arbitrary family of pairwise disjoint coordinate blocks, which is
the per-block generalization of the Round 4 extension counter. All Tier B
statements are verbatim as commissioned.

| item | theorem | status | axioms beyond baseline | notes |
|---|---|---|---|---|
| B1a | `clawB_iff` | closed | `propext`, `Quot.sound` only | decidable claw predicate matches `Claw` |
| B1b | `claw_bound` | closed | — | `16^⌊n/4⌋ · #{¬Claw} ≤ 15^⌊n/4⌋ · 2^m`, via `block_bound` over the ⌊n/4⌋ blocks `{4t,…,4t+3}` and the exact per-block count `block_claw_density` (60 of 64 internal assignments), witnessed by the four centre stars |
| B2a | `mendedAt_of_witnesses` | closed | — | deterministic link; two Γ-steps through `{i,l}`, discharges into `density_implication`'s `MendedAt` hypothesis |
| B2b | `mend_bound_triple` | closed | — | per-`l` product count over the `n−3` dedicated coordinate triples, factor 7/8 each |
| B2c | `mend_bound` | closed | — | union over ordered triples with the generous `n³` |
| B3a | `gconn_of_vconn` | closed | — | proved **with** the commissioned minimum-degree hypothesis `hmin` present; the proof does not use it, so the pre-authorized `conn_bound'` variant was **not** taken. The hypothesis is kept (statement fidelity) and the redundancy is noted in the docstring |
| B3b | `conn_bound` | closed | — | cut counting: `card_crossE`, `card_noCross`, `exists_cut_of_not_vconn`, union bound over `Finset.Icc 1 (n/2)`. `hn : 1 ≤ n` is kept but unused |
| B4 | `density_deficit_bound` | closed | — | contrapositive of `density_implication` plus `Finset.card_union_le`; the right-hand side is the commissioned **three**-term one — the isolated-vertex NOTE's pre-authorized fourth term was **not** needed, since the minimum-degree condition sits inside the third term. `hn : 4 ≤ n` is kept but unused |

Whole-tree verification after Tier B: `lake build` green, **no `sorry` anywhere**
in the library; the only remaining linter warnings are the three unused-variable
warnings forced by keeping the commissioned hypotheses `hmin`, `hn`, `hn`.

## Tier C — stretch

| item | theorem / task | status | axioms beyond baseline | notes |
|---|---|---|---|---|
| C1 | `prop:descent` API (`HalfOne/Descent.lean`) | **closed** | — | Designed as data, as asked, and both statements proved |
| C1a | `pullback_extreme` | closed | — | the pullback of a positive-definite vertex is a vertex |
| C1b | `exists_descent_of_extreme` | closed | — | every vertex is the pullback of a positive-definite vertex along its own zero-partition |
| C2 | kernel `census7` | not commissioned | — | not attempted; the A1d disclosure stands |

### C1 design report

The API is

    structure Descent (n k : ℕ) where
      proj : Fin n → Fin k
      sect : Fin k → Fin n
      proj_sect : ∀ a, proj (sect a) = a

    def comap (s : Fin m → Fin n) (d : DVec n) : DVec m := fun e => dOf d (s e.1.1) (s e.1.2)
    def pullback (D : Descent n k) (d : DVec k) : DVec n := comap D.proj d
    def PosDef (d : DVec k) : Prop := ∀ a b, a ≠ b → 0 < dOf d a b

There was essentially **no design friction**, and the reason is worth recording:
transport is `comap` along an arbitrary index map, and *both* directions of the
descent are instances of it — the pullback is `comap` along `proj`, the descent of
a vector is `comap` along `sect`. Everything else is then a one-line computation
with `dOf`: `dOf_comap`, `comap_add`, `comap_sub`, `comap_zero`, `inBody_comap`
(the body is preserved by transport along *any* map, once the triangle inequality
is restated without its distinctness side conditions as `dOf_triangle_all`), and
`comap_sect_pullback : comap D.sect (pullback D d) = d`, which is the section
identity and immediately gives injectivity of `pullback`. No `Quotient.lift`,
`Quotient.ind`, or `Setoid` ever appears.

Two facts found in the course of the proofs, both worth carrying back to the
paper's phrasing of `prop:descent`:

1. **Positive definiteness is not needed for the pullback direction.** The
   hypothesis is kept in `pullback_extreme` because the commission asks for it,
   but the proof never uses it. What does the work is that the pullback assigns
   distance `0` inside each fibre: a perturbation `ε` of `pullback D d` therefore
   has `dOf ε i j = 0` whenever `proj i = proj j` (both signs of the body
   constraint pin it), and then the triangle inequality forces `ε` to be constant
   along fibres, so `ε` is itself a pullback and descends. Positive definiteness
   is what makes the descent in statement 2 *canonical*, not what makes statement
   1 true.
2. The zero-partition is built without `Quotient`: `zclass`/`zrep` (least element
   of the zero class, `Finset.min'`), the representative set `zreps`, and
   `Finset.orderIsoOfFin` to index it by `Fin (zreps d).card`. Transitivity of
   "distance 0" is `dOf_zero_trans`, an immediate consequence of the triangle
   inequality and nonnegativity, so `zrep` is idempotent and `dOf_zrep_zrep`
   ("replacing both endpoints by representatives does not change the distance")
   is what makes `pullback (zdescent hb) (comap sect d) = d` hold.

## Resolution of the earlier "(pending build confirmation)" markers

The shipped `LEDGER.md` for Rounds 1–5 carries no rows literally marked
"(pending build confirmation)"; the closest thing is the R3.7 row (`census7`,
reported, carried as a `sorry`) and the repair note that `HalfOne/Fast.lean` is
imported by nothing. Both are now resolved: `census7` is closed-with-disclosure
(row A1′) and `HalfOne/Fast.lean` is imported by `HalfOne/Census.lean`. Every
other Rounds 1–5 row is confirmed by the green whole-tree build of this round;
no earlier row was rewritten.

# Integration coda (commissioning side, after Round 6)

## Handoff diagnosis

Rounds 2 and 6 both ran on Aristotle's own workspace tree; the commissioning-side
integration tarballs arrived as opaque attachments and were never expanded. Round 6 read
`ROUND6_COMMISSION.md` and `Round6.lean` out of the attachment and executed them faithfully,
so the divergence cost almost nothing — but it explains two oddities in the summary:
"the tree as shipped did not build" (true of Aristotle's tree, which still carried the
`census7` sorry my integration had removed) and "no bench/ directory exists" (ditto).
For future rounds: the tarball must be expanded over the workspace before the round starts,
or the round's base must be stated in the commission.

## Residue, all optional

1. `census4`/`census5` are proved by kernel `decide` over the ORIGINAL Finset enumeration
   (16 s and 337 s raw), not through `census_eq_fast`. Green, clean axioms; the bridge
   route would merely be faster. No action needed.
2. `census6` remains `native_decide` (closed-with-disclosure). The kernel-through-bridge
   attempt (`attic/K6.lean`, from Round 2) was never compiled under a recorded budget.
   A future micro-round may swap `census6`'s tactic to `rw [census_eq_fast]; decide +kernel`
   with the standing 30-minute fallback; success would make `census7` the sole disclosure
   in the campaign. Purely cosmetic for the paper, whose warrant labels do not change.
3. The Round-2 staging files are preserved in `attic/`, outside the build globs.
   `attic/Y.lean` carries a top-level `#eval` benchmark; do not add it to the build.

## Final axiom map (per Aristotle's Round 6 sweep)

Baseline (`propext`, `Classical.choice`, `Quot.sound`): everything, except
`census6`, `census7`, `census6_good`, `census7_good`, which add `Lean.ofReduceBool` and
`Lean.trustCompiler` (`native_decide`). No `sorryAx` anywhere in the tree.
