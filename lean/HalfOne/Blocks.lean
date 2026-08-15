/-
  HalfOne/Blocks.lean — generic "independent coordinate blocks" counting.

  Round 6 needs, several times over, the following pattern: a Boolean event on
  `α → Bool` that depends only on the coordinates of a finite set `T`, and a
  family of such events attached to pairwise disjoint coordinate blocks.  The
  counts then multiply.  Everything here is stated with exact natural-number
  arithmetic (no division, no probability): a density `c / N` is written
  `N * card ≤ c * 2 ^ (Fintype.card α)`.

  * `card_supported`  — `#{G supported on T} = 2 ^ #T`;
  * `card_split`      — the product decomposition along `T` / `Tᶜ`;
  * `card_indep`      — `#(p ∧ q) * 2^|α| = #p * #q` for `T`-local `q` and
                        `Tᶜ`-local `p`;
  * `local_count`     — `2^#T * #q = #Q₀ * 2^|α|`, with `Q₀` the `q`-satisfying
                        assignments supported on `T`;
  * `local_bound`     — its inequality form;
  * `block_bound`     — the product bound over pairwise disjoint blocks.
-/

import HalfOne.Counting

namespace HalfOne

open Finset

section Blocks

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The restriction of `G` to `T`, zero elsewhere. -/
def onT (T : Finset α) (G : α → Bool) : α → Bool := fun x => if x ∈ T then G x else false

/-- The restriction of `G` to the complement of `T`, zero on `T`. -/
def offT (T : Finset α) (G : α → Bool) : α → Bool := fun x => if x ∈ T then false else G x

/-- Assignments supported on `T` number `2 ^ #T`. -/
theorem card_supported (T : Finset α) :
    (univ.filter (fun G : α → Bool => ∀ x ∉ T, G x = false)).card = 2 ^ T.card := by
  refine card_filter_of_extension _ T (fun H => onT T H) ?_ ?_ ?_ ?_
  · intro H x hx; simp [onT, hx]
  · intro H x hx; simp [onT, hx]
  · intro G hG; funext x
    by_cases hx : x ∈ T
    · simp [onT, hx]
    · simp [onT, hx, hG x hx]
  · intro H H' h; funext x
    by_cases hx : x ∈ T
    · simp [onT, hx, h x hx]
    · simp [onT, hx]

/-- Assignments supported off `T` number `2 ^ #Tᶜ`. -/
theorem card_cosupported (T : Finset α) :
    (univ.filter (fun G : α → Bool => ∀ x ∈ T, G x = false)).card = 2 ^ (Tᶜ).card := by
  have := card_supported (Tᶜ)
  simpa using this

/-- Product decomposition: an event that is the conjunction of a `Tᶜ`-local
    event `p` and a `T`-local event `q` counts as the product of the two
    supported counts. -/
theorem card_split (T : Finset α) (p q : (α → Bool) → Bool)
    (hp : ∀ G H : α → Bool, (∀ x ∉ T, G x = H x) → p G = p H)
    (hq : ∀ G H : α → Bool, (∀ x ∈ T, G x = H x) → q G = q H) :
    (univ.filter (fun G : α → Bool => p G = true ∧ q G = true)).card
      = (univ.filter (fun G : α → Bool => q G = true ∧ ∀ x ∉ T, G x = false)).card
        * (univ.filter (fun G : α → Bool => p G = true ∧ ∀ x ∈ T, G x = false)).card := by
  rw [← Finset.card_product]
  refine Finset.card_nbij' (fun G => (onT T G, offT T G))
    (fun ab => fun x => if x ∈ T then ab.1 x else ab.2 x) ?_ ?_ ?_ ?_
  · rintro G hG
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hG
    simp only [Finset.coe_product, Set.mem_prod, mem_coe, mem_filter, mem_univ, true_and]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [hq (onT T G) G (by intro x hx; simp [onT, hx])]; exact hG.2
    · intro x hx; simp [onT, hx]
    · rw [hp (offT T G) G (by intro x hx; simp [offT, hx])]; exact hG.1
    · intro x hx; simp [offT, hx]
  · rintro ⟨a, b⟩ hab
    simp only [Finset.coe_product, Set.mem_prod, mem_coe, mem_filter, mem_univ, true_and] at hab
    obtain ⟨⟨ha, ha0⟩, hb, hb0⟩ := hab
    simp only [mem_coe, mem_filter, mem_univ, true_and]
    constructor
    · rw [hp _ b (by intro x hx; simp [hx])]; exact hb
    · rw [hq _ a (by intro x hx; simp [hx])]; exact ha
  · intro G hG
    funext x; by_cases hx : x ∈ T <;> simp [onT, offT, hx]
  · rintro ⟨a, b⟩ hab
    simp only [Finset.coe_product, Set.mem_prod, mem_coe, mem_filter, mem_univ, true_and] at hab
    obtain ⟨⟨ha, ha0⟩, hb, hb0⟩ := hab
    ext x
    · by_cases hx : x ∈ T
      · simp [onT, hx]
      · simp [onT, hx, ha0 x hx]
    · by_cases hx : x ∈ T
      · simp [offT, hx, hb0 x hx]
      · simp [offT, hx]

/-- Independence: a `Tᶜ`-local event and a `T`-local event are independent. -/
theorem card_indep (T : Finset α) (p q : (α → Bool) → Bool)
    (hp : ∀ G H : α → Bool, (∀ x ∉ T, G x = H x) → p G = p H)
    (hq : ∀ G H : α → Bool, (∀ x ∈ T, G x = H x) → q G = q H) :
    (univ.filter (fun G : α → Bool => p G = true ∧ q G = true)).card
        * 2 ^ (Fintype.card α)
      = (univ.filter (fun G : α → Bool => p G = true)).card
        * (univ.filter (fun G : α → Bool => q G = true)).card := by
  have h1 := card_split T p q hp hq
  have h2 := card_split T (fun _ => true) q (by intro G H h; rfl) hq
  have h3 := card_split T p (fun _ => true) hp (by intro G H h; rfl)
  simp only [true_and, and_true] at h2 h3
  rw [card_cosupported T] at h2
  rw [card_supported T] at h3
  have hc : T.card + (Tᶜ).card = Fintype.card α := by rw [Finset.card_add_card_compl]
  rw [h1, h2, h3, ← hc, pow_add]
  ring

/-- The count of a `T`-local event, in terms of its supported assignments. -/
theorem local_count (T : Finset α) (q : (α → Bool) → Bool)
    (hq : ∀ G H : α → Bool, (∀ x ∈ T, G x = H x) → q G = q H) :
    2 ^ T.card * (univ.filter (fun G : α → Bool => q G = true)).card
      = (univ.filter (fun G : α → Bool => q G = true ∧ ∀ x ∉ T, G x = false)).card
        * 2 ^ (Fintype.card α) := by
  have h2 := card_split T (fun _ => true) q (by intro G H h; rfl) hq
  simp only [true_and] at h2
  rw [card_cosupported T] at h2
  have hc : T.card + (Tᶜ).card = Fintype.card α := by rw [Finset.card_add_card_compl]
  rw [h2, ← hc, pow_add]
  ring

/-- Density form of `local_count`: if at least `d` of the `2 ^ #T` assignments
    supported on `T` violate the `T`-local event `q`, then `q` has density at
    most `(2 ^ #T − d) / 2 ^ #T`. -/
theorem local_bound (T : Finset α) (q : (α → Bool) → Bool)
    (hq : ∀ G H : α → Bool, (∀ x ∈ T, G x = H x) → q G = q H)
    (d : ℕ)
    (hd : d ≤ (univ.filter (fun G : α → Bool => q G = false ∧ ∀ x ∉ T, G x = false)).card) :
    2 ^ T.card * (univ.filter (fun G : α → Bool => q G = true)).card
      ≤ (2 ^ T.card - d) * 2 ^ (Fintype.card α) := by
  rw [local_count T q hq]
  refine Nat.mul_le_mul_right _ ?_
  have hpart := Finset.card_filter_add_card_filter_not
    (s := univ.filter (fun G : α → Bool => ∀ x ∉ T, G x = false))
    (p := fun G : α → Bool => q G = true)
  rw [Finset.filter_filter, Finset.filter_filter] at hpart
  have e1 : (univ.filter (fun G : α → Bool => (∀ x ∉ T, G x = false) ∧ q G = true)).card
      = (univ.filter (fun G : α → Bool => q G = true ∧ ∀ x ∉ T, G x = false)).card := by
    congr 1; apply Finset.filter_congr; intro G _; simp [and_comm]
  have e2 : (univ.filter (fun G : α → Bool => (∀ x ∉ T, G x = false) ∧ ¬ (q G = true))).card
      = (univ.filter (fun G : α → Bool => q G = false ∧ ∀ x ∉ T, G x = false)).card := by
    congr 1; apply Finset.filter_congr; intro G _
    simp [and_comm, Bool.not_eq_true]
  rw [e1, e2, card_supported T] at hpart
  omega

variable {ι : Type*} [DecidableEq ι]

/-- The product bound over pairwise disjoint coordinate blocks: if each block
    event `q t` is local to `B t`, the blocks are pairwise disjoint, and each
    event has density at most `c / N`, then the conjunction has density at most
    `(c / N) ^ #I`. -/
theorem block_bound (I : Finset ι) (B : ι → Finset α) (q : ι → (α → Bool) → Bool)
    (hdisj : ∀ s ∈ I, ∀ t ∈ I, s ≠ t → Disjoint (B s) (B t))
    (hloc : ∀ t ∈ I, ∀ G H : α → Bool, (∀ x ∈ B t, G x = H x) → q t G = q t H)
    (N c : ℕ)
    (hb : ∀ t ∈ I, N * (univ.filter (fun G : α → Bool => q t G = true)).card
            ≤ c * 2 ^ (Fintype.card α)) :
    N ^ I.card * (univ.filter (fun G : α → Bool => ∀ t ∈ I, q t G = true)).card
      ≤ c ^ I.card * 2 ^ (Fintype.card α) := by
  classical
  revert hdisj hloc hb
  induction I using Finset.induction_on with
  | empty =>
      intro _ _ _
      simp [Finset.card_univ]
  | insert t₀ I' ht₀ ih =>
      intro hdisj hloc hb
      set p : (α → Bool) → Bool := fun G => decide (∀ t ∈ I', q t G = true) with hpdef
      have hmem : ∀ t ∈ I', t ∈ insert t₀ I' := fun t h => Finset.mem_insert_of_mem h
      have hp : ∀ G H : α → Bool, (∀ x ∉ B t₀, G x = H x) → p G = p H := by
        intro G H hGH
        have hq' : ∀ t ∈ I', q t G = q t H := by
          intro t htI'
          refine hloc t (hmem t htI') G H ?_
          intro x hx
          refine hGH x ?_
          intro hx0
          have hd := hdisj t (hmem t htI') t₀ (Finset.mem_insert_self t₀ I')
            (by rintro rfl; exact ht₀ htI')
          exact (Finset.disjoint_left.mp hd hx) hx0
        simp only [hpdef, decide_eq_decide]
        constructor
        · intro h t ht; rw [← hq' t ht]; exact h t ht
        · intro h t ht; rw [hq' t ht]; exact h t ht
      have hfilter : (univ.filter (fun G : α → Bool => ∀ t ∈ insert t₀ I', q t G = true))
          = univ.filter (fun G : α → Bool => p G = true ∧ q t₀ G = true) := by
        apply Finset.filter_congr
        intro G _
        simp only [hpdef, decide_eq_true_eq, Finset.forall_mem_insert]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
        · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
      have hpfilter : (univ.filter (fun G : α → Bool => p G = true))
          = univ.filter (fun G : α → Bool => ∀ t ∈ I', q t G = true) := by
        apply Finset.filter_congr; intro G _; simp [hpdef]
      have hind := card_indep (B t₀) p (q t₀) hp
        (hloc t₀ (Finset.mem_insert_self t₀ I'))
      rw [hpfilter] at hind
      have ihb := ih (fun s hs t ht hst => hdisj s (hmem s hs) t (hmem t ht) hst)
        (fun t ht => hloc t (hmem t ht)) (fun t ht => hb t (hmem t ht))
      have hb0 := hb t₀ (Finset.mem_insert_self t₀ I')
      rw [Finset.card_insert_of_notMem ht₀, hfilter]
      set X := (univ.filter (fun G : α → Bool => p G = true ∧ q t₀ G = true)).card
      set P := (univ.filter (fun G : α → Bool => ∀ t ∈ I', q t G = true)).card
      set Q := (univ.filter (fun G : α → Bool => q t₀ G = true)).card
      set M := 2 ^ (Fintype.card α) with hM
      have hMpos : 0 < M := Nat.two_pow_pos _
      have h1 : (N ^ (I'.card + 1) * X) * M = (N ^ I'.card * P) * (N * Q) := by
        have hXM : X * M = P * Q := hind
        calc (N ^ (I'.card + 1) * X) * M = N ^ I'.card * N * (X * M) := by ring
        _ = N ^ I'.card * N * (P * Q) := by rw [hXM]
        _ = (N ^ I'.card * P) * (N * Q) := by ring
      have h3 : (N ^ (I'.card + 1) * X) * M ≤ (c ^ (I'.card + 1) * M) * M := by
        rw [h1]
        calc (N ^ I'.card * P) * (N * Q) ≤ (c ^ I'.card * M) * (c * M) :=
              Nat.mul_le_mul ihb hb0
        _ = (c ^ (I'.card + 1) * M) * M := by ring
      exact Nat.le_of_mul_le_mul_right h3 hMpos

end Blocks

end HalfOne
