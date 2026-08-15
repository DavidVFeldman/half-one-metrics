/-
  HalfOne/Census.lean — §4, Round 3.5–3.7: the census theorems.

  `goodB_correct` (in `HalfOne.Checker`) turns each of these into a statement
  about the mathematical predicate `Good`; the `Good`-forms `census4_good`, …
  are in the master file `HalfOne.lean`.

  ALL FOUR counts route through `census_eq_fast` (`HalfOne.Fast`), which
  replaces the `Finset.univ : Finset (HGraph n)` enumeration — whose kernel
  reduction through `Multiset.pi` is both slow and memory-hungry (it OOM-killed
  a 7 GB CI runner at n = 5) — by a flat loop over the `2 ^ C(n,2)` bitmasks.
  The tactics for n = 4, 5 are exactly Aristotle's Round-2 staging file
  `attic/K5.lean`.

  Axiom status (commission §0.3):
  * `census4`, `census5` — kernel `decide` on the bitmask loop.  Clean
    `#print axioms` (`propext`, `Classical.choice`, `Quot.sound` only).
  * `census6`, `census7` — `native_decide` on the bitmask loop:
    CLOSED-WITH-DISCLOSURE, `Lean.ofReduceBool` (and `Lean.trustCompiler`)
    appear in `#print axioms`.  A kernel attempt for `census6` is staged in
    `attic/K6.lean` and remains optional (LEDGER.md, integration coda §2).

  CI fallback, pre-authorized: if `census5`'s kernel `decide` still exceeds
  the runner's budget, replace its tactic by `native_decide` and move the
  theorem to the disclosure list in LEDGER.md.  Do not fight the runner.
-/

import HalfOne.Checker
import HalfOne.Fast

namespace HalfOne

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

/-- |ex(H₄)| = 5.  Kernel `decide` through the bitmask bridge. -/
theorem census4 : (Finset.univ.filter (fun G : HGraph 4 => goodB G)).card = 5 := by
  rw [census_eq_fast]; decide +kernel

/-- |ex(H₅)| = 168.  Kernel `decide` through the bitmask bridge. -/
theorem census5 : (Finset.univ.filter (fun G : HGraph 5 => goodB G)).card = 168 := by
  rw [census_eq_fast]; decide +kernel

/-- |ex(H₆)| = 12326.  `native_decide`: closed-with-disclosure, the compiler
    axiom `Lean.ofReduceBool` appears in `#print axioms census6`. -/
theorem census6 : (Finset.univ.filter (fun G : HGraph 6 => goodB G)).card = 12326 := by
  rw [census_eq_fast]
  native_decide

/-- |ex(H₇)| = 1309868.  `native_decide` on the bitmask loop of `census_eq_fast`:
    closed-with-disclosure, `Lean.ofReduceBool` appears in `#print axioms census7`. -/
theorem census7 : (Finset.univ.filter (fun G : HGraph 7 => goodB G)).card = 1309868 := by
  rw [census_eq_fast]
  native_decide

end HalfOne
