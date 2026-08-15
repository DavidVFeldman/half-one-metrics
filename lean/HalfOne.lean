/-
  HalfOne.lean — Paper IV formalization campaign, master file.

  Everything is stated over ℚ; no real numbers appear anywhere.
  For build hygiene the development is split into modules, all re-exported
  here; the definitions and the commissioned statements are unchanged.

    `HalfOne.Defs`     §1, §2, §3, §5, §7, §8 — every definition
    `HalfOne.Basic`    R1.1  `adj_symm`, `adj_irrefl`, `gammaAdj_symm`
    `HalfOne.Walks`    R3.1–R3.3  `walkCount_pos_iff`, `good_iff_goodWalk`,
                       `odd_walk_bound`
    `HalfOne.Checker`  R3.4  the executable checker `goodB` and `goodB_correct`
    `HalfOne.Census`   R3.5–R3.7  `census4`, `census5`, `census6`, `census7`
    `HalfOne.Metric`   R1.2–R1.4, R2  `pert_bound`, `pert_additive`,
                       `one_degeneracy`, `upper_half`, `value_sets`
    `HalfOne.Twins`    R1.5, R1.6, R4  `twins_iff_isolated`, `twins_not_good`,
                       `twin_count_single`, `twin_count_shared`,
                       `twin_count_disjoint`, `twin_bound`
    `HalfOne.Density`  R5  `density_implication`
    `HalfOne.QLevel`   R1.7  `qlevel_feasible_count`
    `HalfOne.Blocks`   Round 6  generic independent-block counting
    `HalfOne.Round6`   Round 6, Tier B  `claw_bound`, `mend_bound`,
                       `conn_bound`, `density_deficit_bound`
    `HalfOne.Descent`  Round 6, Tier C1  the descent API for `prop:descent`:
                       `Descent`, `pullback`, `pullback_extreme`,
                       `exists_descent_of_extreme`

  Round assignments and traps: see ARISTOTLE_COMMISSION.md; the ledger of what
  is closed, closed-with-disclosure, or reported is in LEDGER.md.
  Nothing in this file is axiomatized.  The bridge from the combinatorial
  predicate `Good` to polytope extremality is Corollary 3.22 of the companion
  paper and is intentionally OUT OF SCOPE here; see the commission, §0.
-/

import HalfOne.Defs
import HalfOne.Basic
import HalfOne.Walks
import HalfOne.Checker
import HalfOne.Census
import HalfOne.Metric
import HalfOne.Twins
import HalfOne.TwinCount
import HalfOne.Density
import HalfOne.QLevel
import HalfOne.Blocks
import HalfOne.Round6
import HalfOne.Descent

namespace HalfOne

/-! ### §4  The census, restated for the mathematical predicate `Good`

These are the forms the paper quotes: the number of half-length graphs whose
Γ has no bipartite component.  They follow from the `goodB` census together
with `goodB_correct`. -/

open Classical in
theorem census4_good :
    (Finset.univ.filter (fun G : HGraph 4 => Good G)).card = 5 := by
  have h : (Finset.univ.filter (fun G : HGraph 4 => Good G))
      = Finset.univ.filter (fun G : HGraph 4 => goodB G) := by
    ext G; simp [goodB_correct G]
  rw [h, census4]

open Classical in
theorem census5_good :
    (Finset.univ.filter (fun G : HGraph 5 => Good G)).card = 168 := by
  have h : (Finset.univ.filter (fun G : HGraph 5 => Good G))
      = Finset.univ.filter (fun G : HGraph 5 => goodB G) := by
    ext G; simp [goodB_correct G]
  rw [h, census5]

open Classical in
theorem census6_good :
    (Finset.univ.filter (fun G : HGraph 6 => Good G)).card = 12326 := by
  have h : (Finset.univ.filter (fun G : HGraph 6 => Good G))
      = Finset.univ.filter (fun G : HGraph 6 => goodB G) := by
    ext G; simp [goodB_correct G]
  rw [h, census6]

open Classical in
theorem census7_good :
    (Finset.univ.filter (fun G : HGraph 7 => Good G)).card = 1309868 := by
  have h : (Finset.univ.filter (fun G : HGraph 7 => Good G))
      = Finset.univ.filter (fun G : HGraph 7 => goodB G) := by
    ext G; simp [goodB_correct G]
  rw [h, census7]

end HalfOne
