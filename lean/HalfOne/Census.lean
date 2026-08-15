/-
  HalfOne/Census.lean — §4, Round 3.5–3.7: the census theorems.

  `goodB_correct` (in `HalfOne.Checker`) turns each of these into a statement
  about the mathematical predicate `Good`; the `Good`-forms `census4_good`, …
  are in the master file `HalfOne.lean`.

  Axiom status (commission §0.3):
  * `census4`, `census5` — kernel `decide`.  Clean `#print axioms`
    (`propext`, `Classical.choice`, `Quot.sound` only).
  * `census6` — `native_decide`, hence `Lean.ofReduceBool` is imported.
    This is CLOSED-WITH-DISCLOSURE, not closed.  Kernel `decide` is not
    available here: it is the *enumeration* that fails, not the checker —
    `Finset.univ : Finset (HGraph 6)` goes through `Multiset.pi`, and kernel
    reduction of that term overflows the stack already for the constantly
    false predicate.  See LEDGER.md.
  * `census7` — `native_decide` through `census_eq_fast` (`HalfOne.Fast`),
    which replaces the `Multiset.pi` enumeration by a loop over the `2 ^ 21`
    bitmasks.  Also CLOSED-WITH-DISCLOSURE (`Lean.ofReduceBool`).
-/

import HalfOne.Checker
import HalfOne.Fast

namespace HalfOne

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

/-- |ex(H₄)| = 5.  Kernel `decide`. -/
theorem census4 : (Finset.univ.filter (fun G : HGraph 4 => goodB G)).card = 5 := by
  decide +kernel

/-- |ex(H₅)| = 168.  Kernel `decide`. -/
theorem census5 : (Finset.univ.filter (fun G : HGraph 5 => goodB G)).card = 168 := by
  decide +kernel

/-- |ex(H₆)| = 12326.  `native_decide`: closed-with-disclosure, the compiler
    axiom `Lean.ofReduceBool` appears in `#print axioms census6`. -/
theorem census6 : (Finset.univ.filter (fun G : HGraph 6 => goodB G)).card = 12326 := by
  native_decide

/-- |ex(H₇)| = 1309868.  `native_decide` on the bitmask loop of `census_eq_fast`:
    closed-with-disclosure, `Lean.ofReduceBool` appears in `#print axioms census7`. -/
theorem census7 : (Finset.univ.filter (fun G : HGraph 7 => goodB G)).card = 1309868 := by
  rw [census_eq_fast]
  native_decide

end HalfOne
