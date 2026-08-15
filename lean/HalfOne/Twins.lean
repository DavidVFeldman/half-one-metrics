/-
  HalfOne/Twins.lean — §7:
  Round 1.5 (`twins_iff_isolated`) and 1.6 (`twins_not_good`).
  The Round 4 counting lemmas are in `HalfOne.TwinCount`.
-/

import HalfOne.Walks

namespace HalfOne

variable {n : ℕ}

theorem adj_of_lt (G : HGraph n) {i j : Fin n} (h : i < j) :
    adj G i j = G ⟨(i, j), h⟩ := by
  unfold adj; rw [dif_pos h]

/-- If `k` is adjacent to `a` but not to `b`, then the edge `{a,k}` is a
    Γ-neighbour of `{a,b}`. -/
private theorem gamma_nbr_left {a b k : Fin n} {G : HGraph n} (hab : a < b)
    (hka : k ≠ a) (hkb : k ≠ b) (he : G ⟨(a, b), hab⟩ = true)
    (hak : adj G a k = true) (hbk : adj G b k = false) :
    ∃ f, gammaAdj G ⟨(a, b), hab⟩ f = true := by
  rcases lt_trichotomy a k with h | h | h
  · refine ⟨⟨(a, k), h⟩, ?_⟩
    have hGf : G ⟨(a, k), h⟩ = true := by rw [← adj_of_lt G h]; exact hak
    have hne : (⟨(a, b), hab⟩ : Edge n) ≠ ⟨(a, k), h⟩ := by
      intro hEq
      exact hkb (congrArg (fun z : Edge n => z.1.2) hEq).symm
    simp [gammaAdj, he, hGf, hne, hbk]
  · exact absurd h.symm hka
  · refine ⟨⟨(k, a), h⟩, ?_⟩
    have hGf : G ⟨(k, a), h⟩ = true := by rw [← adj_of_lt G h, adj_symm]; exact hak
    have hne : (⟨(a, b), hab⟩ : Edge n) ≠ ⟨(k, a), h⟩ := by
      intro hEq
      exact hka (congrArg (fun z : Edge n => z.1.1) hEq).symm
    simp [gammaAdj, he, hGf, hne, hbk]

/-- Mirror image of `gamma_nbr_left`. -/
private theorem gamma_nbr_right {a b k : Fin n} {G : HGraph n} (hab : a < b)
    (hka : k ≠ a) (hkb : k ≠ b) (he : G ⟨(a, b), hab⟩ = true)
    (hbk : adj G b k = true) (hak : adj G a k = false) :
    ∃ f, gammaAdj G ⟨(a, b), hab⟩ f = true := by
  rcases lt_trichotomy b k with h | h | h
  · refine ⟨⟨(b, k), h⟩, ?_⟩
    have hGf : G ⟨(b, k), h⟩ = true := by rw [← adj_of_lt G h]; exact hbk
    have hne : (⟨(a, b), hab⟩ : Edge n) ≠ ⟨(b, k), h⟩ := by
      intro hEq
      exact (Fin.ne_of_lt hab) (congrArg (fun z : Edge n => z.1.1) hEq)
    simp [gammaAdj, he, hGf, hne, hak]
  · exact absurd h.symm hkb
  · refine ⟨⟨(k, b), h⟩, ?_⟩
    have hGf : G ⟨(k, b), h⟩ = true := by rw [← adj_of_lt G h, adj_symm]; exact hbk
    have hne : (⟨(a, b), hab⟩ : Edge n) ≠ ⟨(k, b), h⟩ := by
      intro hEq
      exact hka (congrArg (fun z : Edge n => z.1.1) hEq).symm
    simp [gammaAdj, he, hGf, hne, hak]

/-- prop:twins.  An edge is an isolated Γ-node iff its endpoints are true
    twins. -/
theorem twins_iff_isolated (G : HGraph n) (e : Edge n) (he : G e = true) :
    (∀ f, gammaAdj G e f = false) ↔ TrueTwins G e := by
  obtain ⟨⟨a, b⟩, hab⟩ := e
  simp only [TrueTwins] at *
  constructor
  · -- isolated ⇒ twins
    intro hiso
    refine ⟨he, ?_⟩
    intro k hka hkb
    have hcon : ¬ ∃ f, gammaAdj G ⟨(a, b), hab⟩ f = true := by
      rintro ⟨f, hf⟩
      rw [hiso f] at hf
      exact Bool.noConfusion hf
    cases hA : adj G a k <;> cases hB : adj G b k
    · rfl
    · exact absurd (gamma_nbr_right hab hka hkb he hB hA) hcon
    · exact absurd (gamma_nbr_left hab hka hkb he hA hB) hcon
    · rfl
  · -- twins ⇒ isolated
    rintro ⟨-, htw⟩ f
    rw [Bool.eq_false_iff]
    intro hcon
    have hGf : G f = true := gammaAdj_right hcon
    have hne : (⟨(a, b), hab⟩ : Edge n) ≠ f := gammaAdj_ne hcon
    rw [gammaAdj] at hcon
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      Bool.not_eq_true'] at hcon
    obtain ⟨-, hcases⟩ := hcon
    obtain ⟨⟨c, d⟩, hcd⟩ := f
    simp only at hcases hne hGf
    have hGcd : adj G c d = true := by rw [adj_of_lt G hcd]; exact hGf
    rcases hcases with ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩
    · -- a = c
      subst h1
      have hda : d ≠ a := (Fin.ne_of_lt hcd).symm
      have hdb : d ≠ b := by
        intro hEq; subst hEq; exact hne rfl
      have := htw d hda hdb
      rw [hGcd] at this
      rw [← this] at h2
      exact Bool.noConfusion h2
    · -- a = d
      subst h1
      have hca : c ≠ a := Fin.ne_of_lt hcd
      have hcb : c ≠ b := by
        intro hEq; subst hEq; exact absurd hab (asymm hcd)
      have := htw c hca hcb
      rw [adj_symm G a c, hGcd] at this
      rw [← this] at h2
      exact Bool.noConfusion h2
    · -- b = c
      subst h1
      have hda : d ≠ a := Fin.ne_of_gt (lt_trans hab hcd)
      have hdb : d ≠ b := (Fin.ne_of_lt hcd).symm
      have := htw d hda hdb
      rw [hGcd] at this
      rw [this] at h2
      exact Bool.noConfusion h2
    · -- b = d
      subst h1
      have hca : c ≠ a := by
        intro hEq; subst hEq; exact hne rfl
      have hcb : c ≠ b := Fin.ne_of_lt hcd
      have := htw c hca hcb
      rw [adj_symm G b c, hGcd] at this
      rw [this] at h2
      exact Bool.noConfusion h2

/-- An isolated Γ-node is the only node reachable from itself. -/
theorem eq_of_isolated {G : HGraph n} {e f : Edge n} (hiso : ∀ g, gammaAdj G e g = false)
    {ℓ : ℕ} (w : GWalk G e f ℓ) : f = e := by
  cases w with
  | nil => rfl
  | cons hxy _ => exact absurd hxy (by rw [hiso]; simp)

/-- A twin pair is a bipartite (isolated) component, so the graph is not good. -/
theorem twins_not_good {n : ℕ} {G : HGraph n} {e : Edge n}
    (h : TrueTwins G e) : ¬ Good G := by
  intro hgood
  have he : G e = true := h.1
  have hiso : ∀ f, gammaAdj G e f = false := (twins_iff_isolated G e he).mpr h
  refine hgood e he ⟨fun _ => true, ?_⟩
  intro f g hf hg hfg
  obtain ⟨ℓ₁, w₁⟩ := hf
  obtain ⟨ℓ₂, w₂⟩ := hg
  rw [eq_of_isolated hiso w₁, eq_of_isolated hiso w₂] at hfg
  rw [hiso e] at hfg
  exact absurd hfg (by simp)

end HalfOne
