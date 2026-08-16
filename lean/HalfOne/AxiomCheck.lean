/-
  AxiomCheck.lean — compiled axiom audit (checklist §4).
  CI parses the `#print axioms` output of this file; the allowlist is
  propext, Classical.choice, Quot.sound everywhere, plus Lean.ofReduceBool
  and Lean.trustCompiler on census6/census7 (and their Good-forms) only.
-/
import HalfOne

open HalfOne

#print axioms adj_symm
#print axioms pert_bound
#print axioms pert_additive
#print axioms one_degeneracy
#print axioms upper_half
#print axioms value_sets
#print axioms twins_iff_isolated
#print axioms twins_not_good
#print axioms twin_count_single
#print axioms twin_count_shared
#print axioms twin_count_disjoint
#print axioms twin_bound
#print axioms qlevel_feasible_count
#print axioms walkCount_pos_iff
#print axioms good_iff_goodWalk
#print axioms odd_walk_bound
#print axioms goodB_correct
#print axioms census4
#print axioms census5
#print axioms census6
#print axioms census7
#print axioms census4_good
#print axioms census5_good
#print axioms census6_good
#print axioms census7_good
#print axioms density_implication
#print axioms clawB_iff
#print axioms claw_bound
#print axioms mendedAt_of_witnesses
#print axioms mend_bound_triple
#print axioms mend_bound
#print axioms gconn_of_vconn
#print axioms conn_bound
#print axioms density_deficit_bound
#print axioms pullback_extreme
#print axioms exists_descent_of_extreme
