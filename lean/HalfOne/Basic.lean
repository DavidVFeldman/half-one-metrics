/-
  HalfOne/Basic.lean — Round 1.1: the symmetry/irreflexivity lemmas for the
  adjacency lookups.
-/

import HalfOne.Defs

namespace HalfOne

theorem adj_symm {n : ℕ} (G : HGraph n) (i j : Fin n) : adj G i j = adj G j i := by
  unfold adj
  rcases lt_trichotomy i j with h | h | h
  · rw [dif_pos h, dif_neg (asymm h), dif_pos h]
  · subst h; rw [dif_neg (lt_irrefl i), dif_neg (lt_irrefl i)]
  · rw [dif_neg (asymm h), dif_pos h, dif_pos h]

theorem adj_irrefl {n : ℕ} (G : HGraph n) (i : Fin n) : adj G i i = false := by
  unfold adj
  rw [dif_neg (lt_irrefl i), dif_neg (lt_irrefl i)]

theorem gammaAdj_symm {n : ℕ} (G : HGraph n) (e f : Edge n) :
    gammaAdj G e f = gammaAdj G f e := by
  have hne : (decide (f ≠ e)) = (decide (e ≠ f)) := decide_eq_decide.mpr ne_comm
  have h1 : (decide (f.1.1 = e.1.1)) = (decide (e.1.1 = f.1.1)) :=
    decide_eq_decide.mpr eq_comm
  have h2 : (decide (f.1.1 = e.1.2)) = (decide (e.1.2 = f.1.1)) :=
    decide_eq_decide.mpr eq_comm
  have h3 : (decide (f.1.2 = e.1.1)) = (decide (e.1.1 = f.1.2)) :=
    decide_eq_decide.mpr eq_comm
  have h4 : (decide (f.1.2 = e.1.2)) = (decide (e.1.2 = f.1.2)) :=
    decide_eq_decide.mpr eq_comm
  unfold gammaAdj
  rw [hne, h1, h2, h3, h4, adj_symm G f.1.2 e.1.2, adj_symm G f.1.2 e.1.1,
    adj_symm G f.1.1 e.1.2, adj_symm G f.1.1 e.1.1]
  generalize G e = a
  generalize G f = b
  generalize decide (e ≠ f) = c
  generalize decide (e.1.1 = f.1.1) = p1
  generalize decide (e.1.2 = f.1.1) = p2
  generalize decide (e.1.1 = f.1.2) = p3
  generalize decide (e.1.2 = f.1.2) = p4
  generalize adj G e.1.2 f.1.2 = q1
  generalize adj G e.1.1 f.1.2 = q2
  generalize adj G e.1.2 f.1.1 = q3
  generalize adj G e.1.1 f.1.1 = q4
  revert a b c p1 p2 p3 p4 q1 q2 q3 q4
  decide

/-- `gammaAdj` is irreflexive. -/
theorem gammaAdj_irrefl {n : ℕ} (G : HGraph n) (e : Edge n) :
    gammaAdj G e e = false := by
  unfold gammaAdj; simp

theorem gammaAdj_left {n : ℕ} {G : HGraph n} {e f : Edge n}
    (h : gammaAdj G e f = true) : G e = true := by
  unfold gammaAdj at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1

theorem gammaAdj_right {n : ℕ} {G : HGraph n} {e f : Edge n}
    (h : gammaAdj G e f = true) : G f = true := by
  unfold gammaAdj at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.2

theorem gammaAdj_ne {n : ℕ} {G : HGraph n} {e f : Edge n}
    (h : gammaAdj G e f = true) : e ≠ f := by
  unfold gammaAdj at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

end HalfOne
