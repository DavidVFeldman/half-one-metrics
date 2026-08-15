/-
  HalfOne/Walks.lean — §2–§3 walk theory:
  the classical equivalence `good_iff_goodWalk`, the matrix-power description
  `walkCount_pos_iff`, and the length bound `odd_walk_bound`.

  The bound is obtained by transporting Γ-walks to walks in the *parity double*
  of Γ (a `SimpleGraph` on `Edge n × Bool`), where an odd closed walk at `e`
  becomes a walk from `(e, false)` to `(e, true)`; Mathlib's `Walk.bypass`
  then produces a path, whose length is below the number of vertices.
-/

import HalfOne.Basic

namespace HalfOne

variable {n : ℕ} {G : HGraph n}

/-- Parity of a successor, as a `Bool` identity. -/
theorem decide_odd_succ (m : ℕ) : (decide (Odd (m + 1))) = !(decide (Odd m)) := by
  by_cases h : Odd m
  · have h' : ¬ Odd (m + 1) := by rw [Nat.odd_add_one]; exact not_not_intro h
    simp [h, h']
  · have h' : Odd (m + 1) := by rw [Nat.odd_add_one]; exact h
    simp [h, h']

/-! ### Elementary walk combinators -/

theorem GWalk.snoc {e f g : Edge n} {ℓ : ℕ} (w : GWalk G e f ℓ)
    (h : gammaAdj G f g = true) : GWalk G e g (ℓ + 1) := by
  induction w with
  | nil x => exact GWalk.cons h (GWalk.nil g)
  | cons hxy _ ih => exact GWalk.cons hxy (ih h)

theorem GWalk.append {e f g : Edge n} {a b : ℕ} (w₁ : GWalk G e f a)
    (w₂ : GWalk G f g b) : GWalk G e g (a + b) := by
  induction w₁ with
  | nil x => simpa using w₂
  | @cons x y z ℓ hxy _ ih =>
      have h : ℓ + 1 + b = (ℓ + b) + 1 := by omega
      rw [h]
      exact GWalk.cons hxy (ih w₂)

theorem GWalk.reverse {e f : Edge n} {ℓ : ℕ} (w : GWalk G e f ℓ) : GWalk G f e ℓ := by
  induction w with
  | nil x => exact GWalk.nil x
  | cons hxy _ ih => exact ih.snoc ((gammaAdj_symm G _ _) ▸ hxy)

theorem GWalk.zero_iff {e f : Edge n} : GWalk G e f 0 ↔ e = f := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact GWalk.nil e

theorem GWalk.succ_iff {e g : Edge n} {ℓ : ℕ} :
    GWalk G e g (ℓ + 1) ↔ ∃ f, gammaAdj G e f = true ∧ GWalk G f g ℓ := by
  constructor
  · intro h; cases h with
    | cons hxy w => exact ⟨_, hxy, w⟩
  · rintro ⟨f, hf, w⟩; exact GWalk.cons hf w

/-! ### R3.1  The matrix-power description -/

theorem walkCount_pos_iff (G : HGraph n) (ℓ : ℕ) (e f : Edge n) :
    0 < walkCount G ℓ e f ↔ GWalk G e f ℓ := by
  induction ℓ generalizing e with
  | zero =>
      simp only [walkCount, GWalk.zero_iff]
      by_cases h : e = f <;> simp [h]
  | succ ℓ ih =>
      rw [walkCount, GWalk.succ_iff]
      rw [Nat.pos_iff_ne_zero, Ne, Finset.sum_eq_zero_iff]
      push_neg
      constructor
      · rintro ⟨g, -, hg⟩
        by_cases hga : gammaAdj G e g = true
        · exact ⟨g, hga, (ih g).mp (Nat.pos_of_ne_zero (by simpa [hga] using hg))⟩
        · simp [hga] at hg
      · rintro ⟨g, hga, hw⟩
        refine ⟨g, Finset.mem_univ g, ?_⟩
        simp only [hga, if_true]
        exact Nat.pos_iff_ne_zero.mp ((ih g).mpr hw)

/-! ### R3.2  The classical equivalence -/

open Classical in
theorem good_iff_goodWalk (G : HGraph n) : Good G ↔ GoodWalk G := by
  constructor
  · -- Good → GoodWalk
    intro hG e he
    by_contra hodd
    push_neg at hodd
    -- no odd closed walk at `e`: parity of walk length from `e` is well defined
    have wd : ∀ (f : Edge n) (a b : ℕ), GWalk G e f a → GWalk G e f b → (Odd a ↔ Odd b) := by
      intro f a b ha hb
      have hw : GWalk G e e (a + b) := ha.append hb.reverse
      have hab : Even (a + b) := by
        rw [← Nat.not_odd_iff_even]; exact fun h => hodd (a + b) h hw
      have h := Nat.even_add.mp hab
      constructor
      · intro hao
        rw [← Nat.not_even_iff_odd] at hao ⊢
        exact fun hbe => hao (h.mpr hbe)
      · intro hbo
        rw [← Nat.not_even_iff_odd] at hbo ⊢
        exact fun hae => hbo (h.mp hae)
    refine hG e he
      ⟨fun f => if h : GReach G e f then decide (Odd (Classical.choose h)) else false, ?_⟩
    intro f g hf hg hfg
    have hfg' : GWalk G f g 1 := GWalk.cons hfg (GWalk.nil g)
    have haf := Classical.choose_spec hf
    have hag := Classical.choose_spec hg
    have h1 : GWalk G e g (Classical.choose hf + 1) := haf.append hfg'
    have h2 : Odd (Classical.choose hg) ↔ Odd (Classical.choose hf + 1) :=
      wd g _ _ hag h1
    simp only [dif_pos hf, dif_pos hg, ne_eq, decide_eq_decide]
    rw [h2]
    rw [Nat.odd_add_one]
    tauto
  · -- GoodWalk → Good
    intro hW e he hbip
    obtain ⟨c, hc⟩ := hbip
    obtain ⟨ℓ, hodd, hwalk⟩ := hW e he
    -- colours alternate along walks starting at `e`
    have key : ∀ (m : ℕ) (a b : Edge n), GReach G e a → GWalk G a b m →
        c b = xor (decide (Odd m)) (c a) := by
      intro m
      induction m with
      | zero =>
          intro a b _ w
          rw [GWalk.zero_iff.mp w]
          simp
      | succ m ih =>
          intro a b hra w
          obtain ⟨f, hf, w'⟩ := GWalk.succ_iff.mp w
          have hrf : GReach G e f := by
            obtain ⟨t, ht⟩ := hra
            exact ⟨t + 1, ht.snoc hf⟩
          have hne : c f ≠ c a := (hc a f hra hrf hf).symm
          have hcf : c f = !(c a) := by
            revert hne; cases c f <;> cases c a <;> simp
          rw [ih f b hrf w', hcf, decide_odd_succ]
          generalize decide (Odd m) = t
          cases t <;> cases c a <;> rfl
    have hfin := key ℓ e e ⟨0, GWalk.nil e⟩ hwalk
    rw [decide_eq_true hodd] at hfin
    revert hfin; cases c e <;> simp

/-! ### The parity double of Γ -/

/-- The parity double of the Γ-graph: vertices are (Γ-node, parity) pairs. -/
def parityGraph (G : HGraph n) : SimpleGraph (Edge n × Bool) where
  Adj x y := gammaAdj G x.1 y.1 = true ∧ x.2 ≠ y.2
  symm := by
    rintro x y ⟨h1, h2⟩
    exact ⟨by rw [gammaAdj_symm]; exact h1, h2.symm⟩
  loopless := ⟨by rintro x ⟨-, h2⟩; exact h2 rfl⟩

theorem gwalk_reachable {e f : Edge n} {ℓ : ℕ} (w : GWalk G e f ℓ) (b : Bool) :
    (parityGraph G).Reachable (e, b) (f, xor b (decide (Odd ℓ))) := by
  induction w generalizing b with
  | nil x =>
      have h0 : (decide (Odd 0)) = false := by simp
      rw [h0, Bool.xor_false]
  | @cons x y z ℓ hxy _ ih =>
      have step : (parityGraph G).Adj (x, b) (y, !b) := ⟨hxy, by cases b <;> simp⟩
      have heq : xor b (decide (Odd (ℓ + 1))) = xor (!b) (decide (Odd ℓ)) := by
        rw [decide_odd_succ]
        generalize decide (Odd ℓ) = t
        cases t <;> cases b <;> rfl
      rw [heq]
      exact SimpleGraph.Reachable.trans (SimpleGraph.Adj.reachable step) (ih (!b))

theorem walk_to_gwalk {x y : Edge n × Bool} (p : (parityGraph G).Walk x y) :
    GWalk G x.1 y.1 p.length ∧ y.2 = xor x.2 (decide (Odd p.length)) := by
  induction p with
  | nil =>
      refine ⟨GWalk.nil _, ?_⟩
      simp
  | @cons u v w h q ih =>
      obtain ⟨hg, hb⟩ := ih
      obtain ⟨hadj, hne⟩ := h
      refine ⟨GWalk.cons hadj hg, ?_⟩
      have hv : v.2 = !u.2 := by revert hne; cases u.2 <;> cases v.2 <;> simp
      rw [SimpleGraph.Walk.length_cons, hb, hv, decide_odd_succ]
      generalize decide (Odd q.length) = t
      cases t <;> cases u.2 <;> rfl

/-! ### R3.3  The length bound -/

/-- Sharper form of the bound actually proved: `2 · #Edge n` suffices. -/
theorem odd_walk_bound_two (G : HGraph n) (e : Edge n)
    (h : ∃ ℓ, Odd ℓ ∧ GWalk G e e ℓ) :
    ∃ ℓ, Odd ℓ ∧ ℓ < 2 * Fintype.card (Edge n) ∧ GWalk G e e ℓ := by
  obtain ⟨ℓ, hodd, hw⟩ := h
  have hr : (parityGraph G).Reachable (e, false) (e, true) := by
    have hre := gwalk_reachable hw false
    rwa [decide_eq_true hodd, Bool.false_xor] at hre
  obtain ⟨p⟩ := hr
  have hpath : p.bypass.IsPath := p.bypass_isPath
  have hlt : p.bypass.length < Fintype.card (Edge n × Bool) := hpath.length_lt
  obtain ⟨hgw, hpar⟩ := walk_to_gwalk p.bypass
  simp only at hgw hpar
  refine ⟨p.bypass.length, ?_, ?_, hgw⟩
  · by_contra hno
    rw [decide_eq_false hno, Bool.false_xor] at hpar
    exact Bool.noConfusion hpar
  · have hcard : Fintype.card (Edge n × Bool) = 2 * Fintype.card (Edge n) := by
      rw [Fintype.card_prod, Fintype.card_bool, Nat.mul_comm]
    omega

theorem odd_walk_bound (G : HGraph n) (e : Edge n)
    (h : ∃ ℓ, Odd ℓ ∧ GWalk G e e ℓ) :
    ∃ ℓ, Odd ℓ ∧ ℓ < 3 * Fintype.card (Edge n) ∧ GWalk G e e ℓ := by
  obtain ⟨ℓ, hodd, hlt, hw⟩ := odd_walk_bound_two G e h
  exact ⟨ℓ, hodd, by omega, hw⟩

end HalfOne
