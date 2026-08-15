/-
  HalfOne/Metric.lean — §5 and §6:
  Round 1.2 (`pert_bound`), 1.3 (`pert_additive`), 1.4 (`one_degeneracy`),
  Round 2.1 (`upper_half`), 2.2 (`value_sets`).

  Everything is over ℚ.
-/

import HalfOne.Defs

namespace HalfOne

variable {n : ℕ}

/-! ### Elementary properties of the symmetric lookup `dOf` -/

theorem dOf_self (d : DVec n) (i : Fin n) : dOf d i i = 0 := by
  unfold dOf; rw [dif_neg (lt_irrefl i), dif_neg (lt_irrefl i)]

theorem dOf_symm (d : DVec n) (i j : Fin n) : dOf d i j = dOf d j i := by
  unfold dOf
  rcases lt_trichotomy i j with h | h | h
  · rw [dif_pos h, dif_neg (asymm h), dif_pos h]
  · subst h; rw [dif_neg (lt_irrefl i), dif_neg (lt_irrefl i)]
  · rw [dif_neg (asymm h), dif_pos h, dif_pos h]

theorem dOf_add (d ε : DVec n) (i j : Fin n) :
    dOf (fun e => d e + ε e) i j = dOf d i j + dOf ε i j := by
  unfold dOf
  rcases lt_trichotomy i j with h | h | h
  · rw [dif_pos h, dif_pos h, dif_pos h]
  · subst h; simp [lt_irrefl]
  · rw [dif_neg (asymm h), dif_neg (asymm h), dif_neg (asymm h), dif_pos h, dif_pos h, dif_pos h]

theorem dOf_sub (d ε : DVec n) (i j : Fin n) :
    dOf (fun e => d e - ε e) i j = dOf d i j - dOf ε i j := by
  unfold dOf
  rcases lt_trichotomy i j with h | h | h
  · rw [dif_pos h, dif_pos h, dif_pos h]
  · subst h; simp [lt_irrefl]
  · rw [dif_neg (asymm h), dif_neg (asymm h), dif_neg (asymm h), dif_pos h, dif_pos h, dif_pos h]

theorem dOf_smul (c : ℚ) (d : DVec n) (i j : Fin n) :
    dOf (fun e => c * d e) i j = c * dOf d i j := by
  unfold dOf
  rcases lt_trichotomy i j with h | h | h
  · rw [dif_pos h, dif_pos h]
  · subst h; simp [lt_irrefl]
  · rw [dif_neg (asymm h), dif_neg (asymm h), dif_pos h, dif_pos h]

/-- For distinct endpoints, `dOf` is a coordinate of the vector. -/
theorem dOf_eq_coord (d : DVec n) {i j : Fin n} (h : i ≠ j) : ∃ f : Edge n, dOf d i j = d f := by
  unfold dOf
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact ⟨⟨(i, j), hlt⟩, by rw [dif_pos hlt]⟩
  · exact absurd heq h
  · exact ⟨⟨(j, i), hgt⟩, by rw [dif_neg (asymm hgt), dif_pos hgt]⟩

/-- The value of a one-coordinate perturbation on a pair: either zero, or the
    perturbation size, and then the pair carries the coordinate `e`. -/
theorem dOf_single (d : DVec n) (e : Edge n) (δ : ℚ) {i j : Fin n} (hij : i ≠ j) :
    dOf (fun f => if f = e then δ else 0) i j = 0 ∨
      (dOf (fun f => if f = e then δ else 0) i j = δ ∧ dOf d i j = d e) := by
  unfold dOf
  rcases lt_trichotomy i j with hlt | heq | hgt
  · rw [dif_pos hlt, dif_pos hlt]
    by_cases h : (⟨(i, j), hlt⟩ : Edge n) = e
    · exact Or.inr ⟨by simp [h], by rw [h]⟩
    · exact Or.inl (by simp [h])
  · exact absurd heq hij
  · rw [dif_neg (asymm hgt), dif_pos hgt, dif_neg (asymm hgt), dif_pos hgt]
    by_cases h : (⟨(j, i), hgt⟩ : Edge n) = e
    · exact Or.inr ⟨by simp [h], by rw [h]⟩
    · exact Or.inl (by simp [h])

/-! ### R1.2, R1.3  The perturbation lemma -/

/-- lem:pert (i): `|ε| ≤ min(d, 1−d)` pointwise. -/
theorem pert_bound {n : ℕ} {d ε : DVec n}
    (hplus : InBody (fun e => d e + ε e)) (hminus : InBody (fun e => d e - ε e)) :
    ∀ e, |ε e| ≤ min (d e) (1 - d e) := by
  intro e
  obtain ⟨hp0, hp1⟩ := hplus.1 e
  obtain ⟨hm0, hm1⟩ := hminus.1 e
  dsimp only at hp0 hp1 hm0 hm1
  rw [abs_le, neg_le, le_min_iff, le_min_iff]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-- lem:pert (ii): additivity of the perturbation on degenerate triangles. -/
theorem pert_additive {n : ℕ} {d ε : DVec n}
    (hplus : InBody (fun e => d e + ε e)) (hminus : InBody (fun e => d e - ε e))
    {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hdeg : dOf d i k = dOf d i j + dOf d j k) :
    dOf ε i k = dOf ε i j + dOf ε j k := by
  have hp := hplus.2 i j k hij hjk hik
  have hm := hminus.2 i j k hij hjk hik
  rw [dOf_add, dOf_add, dOf_add] at hp
  rw [dOf_sub, dOf_sub, dOf_sub] at hm
  linarith

/-! ### R1.4  At most one degeneracy -/

/-- prop:onedegen.  A strictly positive metric has at most one degenerate
    ordered triangle on any triple. -/
theorem one_degeneracy {n : ℕ} {d : DVec n} (hb : InBody d)
    (hpos : ∀ e, 0 < d e) {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (h₁ : dOf d i k = dOf d i j + dOf d j k)
    (h₂ : dOf d i j = dOf d i k + dOf d k j) : False := by
  obtain ⟨f, hf⟩ := dOf_eq_coord d hjk
  have hjk0 : 0 < dOf d j k := by rw [hf]; exact hpos f
  have hkj : dOf d k j = dOf d j k := dOf_symm d k j
  rw [hkj] at h₂
  linarith

/-! ### R2.1  The upper-half theorem -/

/-- The single-coordinate perturbation keeps the body, when all values are in
    `[½, 1]` and the coordinate `e` is strictly between. -/
private theorem inBody_single {n : ℕ} {d : DVec n} (hb : InBody d)
    (hlo : ∀ f, (1 : ℚ)/2 ≤ d f) (e : Edge n) (δ : ℚ)
    (hδ0 : 0 < δ) (hd1 : 2 * δ ≤ d e - 1/2) (hd2 : 2 * δ ≤ 1 - d e)
    (σ : ℚ) (hσ : σ = 1 ∨ σ = -1) :
    InBody (fun f => d f + σ * (if f = e then δ else 0)) := by
  have hde1 : d e ≤ 1 := (hb.1 e).2
  constructor
  · intro f
    dsimp only
    by_cases h : f = e
    · rw [if_pos h, h]
      rcases hσ with rfl | rfl <;> constructor <;> linarith [hlo e]
    · rw [if_neg h]
      have hf := hb.1 f
      constructor <;> [linarith [hf.1]; linarith [hf.2]]
  · intro i j k hij hjk hik
    have htri := hb.2 i j k hij hjk hik
    have hbij := dOf_eq_coord d hij
    have hbjk := dOf_eq_coord d hjk
    have hbik := dOf_eq_coord d hik
    obtain ⟨f1, hf1⟩ := hbij
    obtain ⟨f2, hf2⟩ := hbjk
    obtain ⟨f3, hf3⟩ := hbik
    have b1 : (1:ℚ)/2 ≤ dOf d i j := by rw [hf1]; exact hlo f1
    have b2 : (1:ℚ)/2 ≤ dOf d j k := by rw [hf2]; exact hlo f2
    have b3 : (1:ℚ)/2 ≤ dOf d i k := by rw [hf3]; exact hlo f3
    have c1 : dOf d i j ≤ 1 := by rw [hf1]; exact (hb.1 f1).2
    have c2 : dOf d j k ≤ 1 := by rw [hf2]; exact (hb.1 f2).2
    have c3 : dOf d i k ≤ 1 := by rw [hf3]; exact (hb.1 f3).2
    have hsplit : ∀ x y : Fin n, x ≠ y →
        dOf (fun f => d f + σ * (if f = e then δ else 0)) x y
          = dOf d x y + σ * dOf (fun f : Edge n => if f = e then δ else 0) x y := by
      intro x y _
      rw [show (fun f => d f + σ * (if f = e then δ else 0))
            = (fun f => d f + (fun g : Edge n => σ * (if g = e then δ else 0)) f) from rfl,
        dOf_add,
        show (fun g : Edge n => σ * (if g = e then δ else 0))
            = (fun g : Edge n => σ * ((fun h : Edge n => if h = e then δ else 0) g)) from rfl,
        dOf_smul]
    rw [hsplit i k hik, hsplit i j hij, hsplit j k hjk]
    rcases dOf_single d e δ hij with e1 | ⟨e1, e1'⟩ <;>
      rcases dOf_single d e δ hjk with e2 | ⟨e2, e2'⟩ <;>
      rcases dOf_single d e δ hik with e3 | ⟨e3, e3'⟩ <;>
      rw [e1, e2, e3] <;> rcases hσ with rfl | rfl <;> linarith

/-- thm:upperhalf.  A vertex of the body with all distances ≥ ½ is half-one. -/
theorem upper_half {n : ℕ} {d : DVec n} (hx : Extreme d)
    (hlo : ∀ e, (1 : ℚ)/2 ≤ d e) : ∀ e, d e = 1/2 ∨ d e = 1 := by
  obtain ⟨hb, hext⟩ := hx
  intro e
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hde1 : d e ≤ 1 := (hb.1 e).2
  have hlt : d e < 1 := lt_of_le_of_ne hde1 h2
  have hgt : (1:ℚ)/2 < d e := lt_of_le_of_ne (hlo e) (Ne.symm h1)
  set δ : ℚ := min (d e - 1/2) (1 - d e) / 2 with hδdef
  have hδ0 : 0 < δ := by
    rw [hδdef]
    have : (0:ℚ) < min (d e - 1/2) (1 - d e) := lt_min (by linarith) (by linarith)
    linarith
  have hd1 : 2 * δ ≤ d e - 1/2 := by
    rw [hδdef]; have := min_le_left (d e - 1/2) (1 - d e); linarith
  have hd2 : 2 * δ ≤ 1 - d e := by
    rw [hδdef]; have := min_le_right (d e - 1/2) (1 - d e); linarith
  have hp := inBody_single hb hlo e δ hδ0 hd1 hd2 1 (Or.inl rfl)
  have hm := inBody_single hb hlo e δ hδ0 hd1 hd2 (-1) (Or.inr rfl)
  have hpe : InBody (fun f => d f + (if f = e then δ else 0)) := by
    simpa using hp
  have hme : InBody (fun f => d f - (if f = e then δ else 0)) := by
    have : (fun f : Edge n => d f - (if f = e then δ else 0))
        = (fun f : Edge n => d f + (-1) * (if f = e then δ else 0)) := by
      funext f; ring
    rw [this]; exact hm
  have := hext (fun f => if f = e then δ else 0) hpe hme e
  rw [if_pos rfl] at this
  exact absurd this (ne_of_gt hδ0)

/-! ### R2.2  The value-set corollary -/

/-- cor:valuesets.  If every value of `d` lies in a set `V ⊆ (0,1]` with
    2·inf ≥ sup (stated pointwise: any two values `a`, `b` attained satisfy
    2a ≥ b), then extremality forces values in {½, 1}. -/
theorem value_sets {n : ℕ} {d : DVec n} (hx : Extreme d)
    (hpos : ∀ e, 0 < d e)
    (hV : ∀ e f, 2 * d e ≥ d f) : ∀ e, d e = 1/2 ∨ d e = 1 := by
  obtain ⟨hb, hext⟩ := hx
  by_cases hempty : IsEmpty (Edge n)
  · exact fun e => (hempty.false e).elim
  · rw [not_isEmpty_iff] at hempty
    -- the maximum value is attained
    obtain ⟨em, -, hem⟩ :=
      Finset.exists_max_image (Finset.univ : Finset (Edge n)) d
        ⟨hempty.some, Finset.mem_univ _⟩
    have hmax : ∀ f, d f ≤ d em := fun f => hem f (Finset.mem_univ f)
    have hem1 : d em = 1 := by
      by_contra hne
      have hlt : d em < 1 := lt_of_le_of_ne (hb.1 em).2 hne
      set c : ℚ := min 1 ((1 - d em) / d em) with hc
      have hdm0 : 0 < d em := hpos em
      have hc0 : 0 < c := by
        rw [hc]
        exact lt_min one_pos (div_pos (by linarith) hdm0)
      have hc1 : c ≤ 1 := min_le_left _ _
      have hcbound : ∀ f, (1 + c) * d f ≤ 1 := by
        intro f
        have h2 : c ≤ (1 - d em) / d em := min_le_right _ _
        have h3 : c * d em ≤ 1 - d em := by
          rw [le_div_iff₀ hdm0] at h2; linarith
        have h4 : d f ≤ d em := hmax f
        nlinarith [hpos f, hc0.le]
      have hp : InBody (fun f => d f + c * d f) := by
        constructor
        · intro f
          constructor
          · nlinarith [hpos f, hc0.le]
          · have := hcbound f; linarith
        · intro i j k hij hjk hik
          have htri := hb.2 i j k hij hjk hik
          have hs : ∀ x y : Fin n, dOf (fun f => d f + c * d f) x y = (1 + c) * dOf d x y := by
            intro x y
            rw [show (fun f : Edge n => d f + c * d f) = (fun f : Edge n => (1 + c) * d f) from
              by funext f; ring, dOf_smul]
          rw [hs, hs, hs]
          nlinarith [hc0.le]
      have hm : InBody (fun f => d f - c * d f) := by
        constructor
        · intro f
          constructor
          · nlinarith [hpos f, hc1]
          · have := (hb.1 f).2; nlinarith [hpos f, hc0.le]
        · intro i j k hij hjk hik
          have htri := hb.2 i j k hij hjk hik
          have hs : ∀ x y : Fin n, dOf (fun f => d f - c * d f) x y = (1 - c) * dOf d x y := by
            intro x y
            rw [show (fun f : Edge n => d f - c * d f) = (fun f : Edge n => (1 - c) * d f) from
              by funext f; ring, dOf_smul]
          rw [hs, hs, hs]
          nlinarith [hc1]
      have := hext (fun f => c * d f) hp hm em
      have hdm := hpos em
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (ne_of_gt hc0)
      · exact absurd h (ne_of_gt hdm)
    have hlo : ∀ f, (1:ℚ)/2 ≤ d f := by
      intro f
      have := hV f em
      rw [hem1] at this
      linarith
    exact upper_half ⟨hb, hext⟩ hlo

end HalfOne
