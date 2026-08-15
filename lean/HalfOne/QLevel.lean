/-
  HalfOne/QLevel.lean — §9, Round 1.7: the q-level feasibility identity.

  The count of feasible triples over `{0, …, q−1}` is `(q³ + q)/2`.  The proof
  is by complementation: a triple fails at most one of the three triangle
  inequalities, each failure set has `∑_{a<q} a(a+1)/2` elements, and
  `3 ∑_{a<q} a(a+1) + q = q³`.
-/

import HalfOne.Defs

namespace HalfOne

open Finset

/-- Pairs from `range q × range q` whose sum is exactly `a`: there are `a+1`
    of them as soon as `a < q`. -/
private theorem card_pairs_sum_eq (q a : ℕ) (h : a < q) :
    ((range q ×ˢ range q).filter (fun p => p.1 + p.2 = a)).card = a + 1 := by
  rw [show a + 1 = (range (a + 1)).card from (card_range _).symm]
  refine Finset.card_nbij' Prod.fst (fun b => (b, a - b)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [coe_filter, Set.mem_setOf_eq, mem_product, mem_range] at hp
    simp only [coe_range, Set.mem_Iio]
    omega
  · intro b hb
    simp only [coe_range, Set.mem_Iio] at hb
    simp only [coe_filter, Set.mem_setOf_eq, mem_product, mem_range]
    omega
  · intro p hp
    simp only [coe_filter, Set.mem_setOf_eq, mem_product, mem_range] at hp
    have : a - p.1 = p.2 := by omega
    simp [this]
  · intro b _
    rfl

/-- Pairs from `range q × range q` with sum `< a`: twice the count is
    `a(a+1)`. -/
private theorem two_card_pairs_sum_lt (q : ℕ) :
    ∀ a ≤ q, 2 * ((range q ×ˢ range q).filter (fun p => p.1 + p.2 < a)).card = a * (a + 1) := by
  intro a
  induction a with
  | zero => intro _; simp
  | succ a ih =>
      intro hle
      have hlt : a < q := by omega
      have hsplit : ((range q ×ˢ range q).filter (fun p => p.1 + p.2 < a + 1))
          = ((range q ×ˢ range q).filter (fun p => p.1 + p.2 < a))
            ∪ ((range q ×ˢ range q).filter (fun p => p.1 + p.2 = a)) := by
        rw [← Finset.filter_or]
        apply Finset.filter_congr
        intro p _
        omega
      have hdisj : Disjoint ((range q ×ˢ range q).filter (fun p => p.1 + p.2 < a))
          ((range q ×ˢ range q).filter (fun p => p.1 + p.2 = a)) := by
        rw [Finset.disjoint_left]
        intro p hp hp'
        simp only [mem_filter] at hp hp'
        omega
      rw [hsplit, Finset.card_union_of_disjoint hdisj, card_pairs_sum_eq q a hlt]
      have := ih (by omega)
      ring_nf
      ring_nf at this
      omega

/-- `3 ∑_{a<q} a(a+1) + q = q³`. -/
private theorem three_sum_add (q : ℕ) : 3 * (∑ a ∈ range q, a * (a + 1)) + q = q ^ 3 := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Finset.sum_range_succ]
      have h : (q + 1) ^ 3 = q ^ 3 + 3 * (q * (q + 1)) + 1 := by ring
      rw [h, ← ih]
      ring

/-- The common cardinality of the three failure sets. -/
private noncomputable def failCount (q : ℕ) : ℕ :=
  ∑ a ∈ range q, ((range q ×ˢ range q).filter (fun p => p.1 + p.2 < a)).card

private theorem two_failCount (q : ℕ) : 2 * failCount q = ∑ a ∈ range q, a * (a + 1) := by
  rw [failCount, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  exact two_card_pairs_sum_lt q a (le_of_lt (mem_range.mp ha))

/-- prop:Pq in counting form: the number of feasible triples over levels
    {0, …, q−1} is (q³ + q)/2, i.e. 2·#feasible = q³ + q. -/
theorem qlevel_feasible_count (q : ℕ) :
    2 * ((Finset.range q ×ˢ Finset.range q ×ˢ Finset.range q).filter
      (fun t => t.1 ≤ t.2.1 + t.2.2 ∧ t.2.1 ≤ t.1 + t.2.2 ∧ t.2.2 ≤ t.1 + t.2.1)).card
      = q ^ 3 + q := by
  classical
  have hcardA : (range q ×ˢ range q ×ˢ range q).card = q ^ 3 := by
    simp [Finset.card_product]; ring
  have hc1 : ((range q ×ˢ range q ×ˢ range q).filter
      (fun t => t.2.1 + t.2.2 < t.1)).card = failCount q := by
    rw [Finset.card_filter, Finset.sum_product, failCount]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.card_filter]
  have hc2 : ((range q ×ˢ range q ×ˢ range q).filter
      (fun t => t.1 + t.2.2 < t.2.1)).card = failCount q := by
    rw [Finset.card_filter, Finset.sum_product, failCount]
    have h : ∀ a : ℕ, (∑ y ∈ range q ×ˢ range q, if a + y.2 < y.1 then 1 else 0)
        = ∑ b ∈ range q, ∑ c ∈ range q, if a + c < b then 1 else 0 := by
      intro a; rw [Finset.sum_product]
    simp only [h]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.card_filter, Finset.sum_product]
  have hc3 : ((range q ×ˢ range q ×ˢ range q).filter
      (fun t => t.1 + t.2.1 < t.2.2)).card = failCount q := by
    rw [Finset.card_filter, Finset.sum_product, failCount]
    have h : ∀ a : ℕ, (∑ y ∈ range q ×ˢ range q, if a + y.1 < y.2 then 1 else 0)
        = ∑ c ∈ range q, ∑ b ∈ range q, if a + b < c then 1 else 0 := by
      intro a; rw [Finset.sum_product, Finset.sum_comm]
    simp only [h]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.card_filter, Finset.sum_product]
  have hneg : (range q ×ˢ range q ×ˢ range q).filter
      (fun t => ¬ (t.1 ≤ t.2.1 + t.2.2 ∧ t.2.1 ≤ t.1 + t.2.2 ∧ t.2.2 ≤ t.1 + t.2.1))
      = ((range q ×ˢ range q ×ˢ range q).filter (fun t => t.2.1 + t.2.2 < t.1))
        ∪ ((range q ×ˢ range q ×ˢ range q).filter (fun t => t.1 + t.2.2 < t.2.1))
        ∪ ((range q ×ˢ range q ×ˢ range q).filter (fun t => t.1 + t.2.1 < t.2.2)) := by
    rw [← Finset.filter_or, ← Finset.filter_or]
    apply Finset.filter_congr
    intro t _
    omega
  have hd12 : Disjoint ((range q ×ˢ range q ×ˢ range q).filter (fun t => t.2.1 + t.2.2 < t.1))
      ((range q ×ˢ range q ×ˢ range q).filter (fun t => t.1 + t.2.2 < t.2.1)) := by
    rw [Finset.disjoint_left]; intro t ht ht'
    rw [Finset.mem_filter] at ht ht'
    omega
  have hd3 : Disjoint
      (((range q ×ˢ range q ×ˢ range q).filter (fun t => t.2.1 + t.2.2 < t.1))
        ∪ ((range q ×ˢ range q ×ˢ range q).filter (fun t => t.1 + t.2.2 < t.2.1)))
      ((range q ×ˢ range q ×ˢ range q).filter (fun t => t.1 + t.2.1 < t.2.2)) := by
    rw [Finset.disjoint_left]; intro t ht ht'
    rw [Finset.mem_filter] at ht'
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at ht
    omega
  have hsum : ((range q ×ˢ range q ×ˢ range q).filter
      (fun t => ¬ (t.1 ≤ t.2.1 + t.2.2 ∧ t.2.1 ≤ t.1 + t.2.2 ∧ t.2.2 ≤ t.1 + t.2.1))).card
      = failCount q + failCount q + failCount q := by
    rw [hneg, Finset.card_union_of_disjoint hd3, Finset.card_union_of_disjoint hd12,
      hc1, hc2, hc3]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := range q ×ˢ range q ×ˢ range q)
    (p := fun t : ℕ × ℕ × ℕ => t.1 ≤ t.2.1 + t.2.2 ∧ t.2.1 ≤ t.1 + t.2.2 ∧ t.2.2 ≤ t.1 + t.2.1)
  have hfin : 3 * (∑ a ∈ range q, a * (a + 1)) + q = q ^ 3 := three_sum_add q
  have h2f := two_failCount q
  rw [hsum, hcardA] at hsplit
  omega

end HalfOne
