/-
  HalfOne/Counting.lean — generic counting infrastructure used by Round 4.

  The twin counts of §7 all have the same shape: a set `T` of *free* edge
  coordinates together with a rule that reconstructs the whole graph from its
  restriction to `T`.  `card_filter_of_extension` turns such a description into
  the count `2 ^ #T`.  The two star-counting lemmas compute `#T` in the cases
  needed there.
-/

import HalfOne.Basic

namespace HalfOne

open Finset

/-! ### A generic "free coordinates" count -/

/-- If the objects satisfying `P` are exactly the ones produced by a fixed
    extension rule `ext` from their restriction to the coordinate set `T`,
    then there are `2 ^ #T` of them. -/
theorem card_filter_of_extension {α : Type*} [Fintype α] [DecidableEq α]
    (P : (α → Bool) → Prop) [DecidablePred P] (T : Finset α)
    (ext : (α → Bool) → (α → Bool))
    (h1 : ∀ H, P (ext H))
    (h2 : ∀ H, ∀ x ∈ T, ext H x = H x)
    (h3 : ∀ G, P G → ext G = G)
    (h4 : ∀ H H', (∀ x ∈ T, H x = H' x) → ext H = ext H') :
    (Finset.univ.filter P).card = 2 ^ T.card := by
  classical
  have hcard : (2 : ℕ) ^ T.card = (Finset.univ : Finset (↥T → Bool)).card := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_coe, Fintype.card_bool]
  rw [hcard]
  refine Finset.card_nbij' (fun G => fun y : ↥T => G y)
    (fun H => ext (fun x => if h : x ∈ T then H ⟨x, h⟩ else false)) ?_ ?_ ?_ ?_
  · intro G _; simp
  · intro H _
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
    exact h1 _
  · intro G hG
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hG
    have hE : ext (fun x => if h : x ∈ T then G x else false) = ext G := by
      apply h4; intro x hx; simp [hx]
    show ext (fun x => if h : x ∈ T then G x else false) = G
    rw [hE, h3 G hG]
  · intro H _
    funext y
    have := h2 (fun x => if h : x ∈ T then H ⟨x, h⟩ else false) y y.2
    simpa using this

/-! ### Edges from unordered pairs -/

/-- The edge joining two distinct vertices. -/
def edgeOf {n : ℕ} (a b : Fin n) (h : a ≠ b) : Edge n :=
  if hab : a < b then ⟨(a, b), hab⟩ else ⟨(b, a), lt_of_le_of_ne (not_lt.mp hab) (Ne.symm h)⟩

theorem adj_eq_edgeOf {n : ℕ} (G : HGraph n) (a b : Fin n) (h : a ≠ b) :
    adj G a b = G (edgeOf a b h) := by
  unfold adj edgeOf
  by_cases hab : a < b
  · simp [hab]
  · have hba : b < a := lt_of_le_of_ne (not_lt.mp hab) (Ne.symm h)
    simp [hab, hba]

theorem edgeOf_comm {n : ℕ} (a b : Fin n) (h : a ≠ b) :
    edgeOf a b h = edgeOf b a (Ne.symm h) := by
  unfold edgeOf
  by_cases hab : a < b
  · have : ¬ b < a := by omega
    simp [hab, this]
  · have hba : b < a := lt_of_le_of_ne (not_lt.mp hab) (Ne.symm h)
    simp [hab, hba]

@[simp] theorem edgeOf_eta {n : ℕ} (f : Edge n) :
    edgeOf f.1.1 f.1.2 (ne_of_lt f.2) = f := by
  unfold edgeOf
  simp [f.2]

theorem apply_eq_adj {n : ℕ} (G : HGraph n) (f : Edge n) :
    G f = adj G f.1.1 f.1.2 := by
  rw [adj_eq_edgeOf G f.1.1 f.1.2 (ne_of_lt f.2), edgeOf_eta]

theorem edgeOf_fst_lt {n : ℕ} {a b : Fin n} (h : a ≠ b) (hab : a < b) :
    edgeOf a b h = ⟨(a, b), hab⟩ := by
  simp [edgeOf, hab]

/-- An edge is determined by its (unordered) endpoints. -/
theorem edge_eq_of_mem {n : ℕ} {f : Edge n} {a b : Fin n} (h : a ≠ b)
    (h1 : f.1.1 = a ∨ f.1.1 = b) (h2 : f.1.2 = a ∨ f.1.2 = b) :
    f = edgeOf a b h := by
  have hlt := f.2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exfalso; rw [h1, h2] at hlt; exact absurd hlt (lt_irrefl a)
  · have hab : a < b := by rw [← h1, ← h2]; exact hlt
    rw [edgeOf_fst_lt h hab]
    apply Subtype.ext
    simp [Prod.ext_iff, h1, h2]
  · have hba : b < a := by rw [← h1, ← h2]; exact hlt
    rw [edgeOf_comm, edgeOf_fst_lt (Ne.symm h) hba]
    apply Subtype.ext
    simp [Prod.ext_iff, h1, h2]
  · exfalso; rw [h1, h2] at hlt; exact absurd hlt (lt_irrefl b)

/-- Two edges with the same endpoints are equal. -/
theorem edge_ext {n : ℕ} {f g : Edge n} (h1 : f.1.1 = g.1.1) (h2 : f.1.2 = g.1.2) : f = g := by
  apply Subtype.ext
  simp [Prod.ext_iff, h1, h2]

/-- The endpoints of `edgeOf a b`, in one order or the other. -/
theorem edgeOf_endpoints {n : ℕ} (a b : Fin n) (h : a ≠ b) :
    ((edgeOf a b h).1.1 = a ∧ (edgeOf a b h).1.2 = b) ∨
      ((edgeOf a b h).1.1 = b ∧ (edgeOf a b h).1.2 = a) := by
  by_cases hab : a < b
  · left; rw [edgeOf_fst_lt h hab]; exact ⟨rfl, rfl⟩
  · right
    rw [edgeOf_comm, edgeOf_fst_lt (Ne.symm h) (lt_of_le_of_ne (not_lt.mp hab) (Ne.symm h))]
    exact ⟨rfl, rfl⟩

/-- `TrueTwins` for the edge `{u,v}`, stated symmetrically in `u` and `v`. -/
theorem trueTwins_edgeOf_iff {n : ℕ} (G : HGraph n) (u v : Fin n) (huv : u ≠ v) :
    TrueTwins G (edgeOf u v huv) ↔
      (adj G u v = true ∧ ∀ p : Fin n, p ≠ u → p ≠ v → adj G u p = adj G v p) := by
  have hval : G (edgeOf u v huv) = adj G u v := (adj_eq_edgeOf G u v huv).symm
  rcases edgeOf_endpoints u v huv with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · constructor
    · rintro ⟨h1, h2⟩
      refine ⟨hval ▸ h1, fun p hpu hpv => ?_⟩
      have := h2 p (by rw [ha]; exact hpu) (by rw [hb]; exact hpv)
      rwa [ha, hb] at this
    · rintro ⟨h1, h2⟩
      refine ⟨hval ▸ h1, fun p hp1 hp2 => ?_⟩
      rw [ha, hb]
      exact h2 p (by rw [← ha]; exact hp1) (by rw [← hb]; exact hp2)
  · constructor
    · rintro ⟨h1, h2⟩
      refine ⟨hval ▸ h1, fun p hpu hpv => ?_⟩
      have := h2 p (by rw [ha]; exact hpv) (by rw [hb]; exact hpu)
      rw [ha, hb] at this
      exact this.symm
    · rintro ⟨h1, h2⟩
      refine ⟨hval ▸ h1, fun p hp1 hp2 => ?_⟩
      rw [ha, hb]
      exact (h2 p (by rw [← hb]; exact hp2) (by rw [← ha]; exact hp1)).symm

/-! ### A Bonferroni bound -/

/-- Bonferroni (uniform form): if all pairwise intersections have at most `c`
    elements, the union is at least `∑ |A e| − C(#I, 2)·c`. -/
theorem sum_card_le_card_biUnion_add {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (A : ι → Finset α) (c : ℕ)
    (hc : ∀ e ∈ I, ∀ f ∈ I, e ≠ f → (A e ∩ A f).card ≤ c) :
    ∑ e ∈ I, (A e).card ≤ (I.biUnion A).card + (I.card).choose 2 * c := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert a I' ha ih =>
      have hih : ∑ e ∈ I', (A e).card ≤ (I'.biUnion A).card + (I'.card).choose 2 * c :=
        ih (fun e he f hf hef => hc e (Finset.mem_insert_of_mem he) f
          (Finset.mem_insert_of_mem hf) hef)
      have hinter : A a ∩ I'.biUnion A = I'.biUnion (fun e => A a ∩ A e) :=
        Finset.inter_biUnion (A a) I' A
      have hle : (A a ∩ I'.biUnion A).card ≤ I'.card * c := by
        rw [hinter]
        refine le_trans (Finset.card_biUnion_le) ?_
        calc ∑ e ∈ I', (A a ∩ A e).card ≤ ∑ _e ∈ I', c := by
              refine Finset.sum_le_sum fun e he => ?_
              exact hc a (Finset.mem_insert_self a I') e (Finset.mem_insert_of_mem he)
                (fun hE => ha (hE ▸ he))
          _ = I'.card * c := by rw [Finset.sum_const, smul_eq_mul]
      have hunion : ((insert a I').biUnion A).card + (A a ∩ I'.biUnion A).card
          = (A a).card + (I'.biUnion A).card := by
        rw [Finset.biUnion_insert]
        exact Finset.card_union_add_card_inter _ _
      have hsum : ∑ e ∈ insert a I', (A e).card = (A a).card + ∑ e ∈ I', (A e).card :=
        Finset.sum_insert ha
      have hchoose : (insert a I').card.choose 2 = I'.card.choose 2 + I'.card := by
        rw [Finset.card_insert_of_notMem ha, Nat.choose_succ_succ]
        simp [Nat.choose_one_right, Nat.add_comm]
      rw [hsum, hchoose, Nat.add_mul]
      omega

/-- Two `edgeOf`s with matching endpoints agree. -/
theorem edgeOf_congr {n : ℕ} {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d)
    (h1 : a = c) (h2 : b = d) : edgeOf a b hab = edgeOf c d hcd := by
  subst h1; subst h2; rfl

/-- Two `edgeOf`s with swapped matching endpoints agree. -/
theorem edgeOf_congr_swap {n : ℕ} {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d)
    (h1 : a = d) (h2 : b = c) : edgeOf a b hab = edgeOf c d hcd := by
  rw [edgeOf_comm a b hab]
  exact edgeOf_congr (Ne.symm hab) hcd h2 h1

/-! ### Star counts -/

/-- The star at `i` has `n − 1` edges. -/
theorem card_star {n : ℕ} (i : Fin n) :
    (univ.filter (fun f : Edge n => f.1.1 = i ∨ f.1.2 = i)).card = n - 1 := by
  classical
  have hE : ((univ : Finset (Fin n)).erase i).card = n - 1 := by
    rw [Finset.card_erase_of_mem (mem_univ i), Finset.card_univ, Fintype.card_fin]
  rw [← hE]
  refine Finset.card_bij (fun f _ => if f.1.1 = i then f.1.2 else f.1.1) ?_ ?_ ?_
  · intro f hf
    simp only [mem_filter, mem_univ, true_and] at hf
    simp only [Finset.mem_erase, mem_univ, and_true]
    have hlt := f.2
    by_cases h : f.1.1 = i
    · rw [if_pos h]
      intro hc
      rw [h, hc] at hlt
      exact absurd hlt (lt_irrefl i)
    · rw [if_neg h]
      exact h
  · intro f hf g hg hfg
    simp only [mem_filter, mem_univ, true_and] at hf hg
    have hf2 := f.2
    have hg2 := g.2
    dsimp only at hfg
    by_cases h1 : f.1.1 = i <;> by_cases h2 : g.1.1 = i
    · rw [if_pos h1, if_pos h2] at hfg
      have hne : i ≠ f.1.2 := by rw [← h1]; exact ne_of_lt hf2
      have e1 : f = edgeOf i f.1.2 hne :=
        edge_eq_of_mem hne (Or.inl h1) (Or.inr rfl)
      have e2 : g = edgeOf i f.1.2 hne :=
        edge_eq_of_mem hne (Or.inl h2) (Or.inr hfg.symm)
      rw [e1, e2]
    · rw [if_pos h1, if_neg h2] at hfg
      have hgi : g.1.2 = i := hg.resolve_left h2
      exfalso
      rw [h1] at hf2
      rw [hgi] at hg2
      rw [hfg] at hf2
      exact lt_asymm hf2 hg2
    · rw [if_neg h1, if_pos h2] at hfg
      have hfi : f.1.2 = i := hf.resolve_left h1
      exfalso
      rw [h2] at hg2
      rw [hfi] at hf2
      rw [← hfg] at hg2
      exact lt_asymm hf2 hg2
    · rw [if_neg h1, if_neg h2] at hfg
      have hfi : f.1.2 = i := hf.resolve_left h1
      have hgi : g.1.2 = i := hg.resolve_left h2
      have hne : i ≠ f.1.1 := by rw [← hfi]; exact (ne_of_lt hf2).symm
      have e1 : f = edgeOf i f.1.1 hne :=
        edge_eq_of_mem hne (Or.inr rfl) (Or.inl hfi)
      have e2 : g = edgeOf i f.1.1 hne :=
        edge_eq_of_mem hne (Or.inr hfg.symm) (Or.inl hgi)
      rw [e1, e2]
  · intro k hk
    simp only [Finset.mem_erase, mem_univ, and_true] at hk
    refine ⟨edgeOf i k (Ne.symm hk), ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and]
      by_cases hik : i < k
      · left; rw [edgeOf_fst_lt (Ne.symm hk) hik]
      · have hki : k < i := lt_of_le_of_ne (not_lt.mp hik) hk
        right
        rw [edgeOf_comm, edgeOf_fst_lt hk hki]
    · dsimp only
      by_cases hik : i < k
      · rw [edgeOf_fst_lt (Ne.symm hk) hik]
        simp
      · have hki : k < i := lt_of_le_of_ne (not_lt.mp hik) hk
        rw [edgeOf_comm, edgeOf_fst_lt hk hki]
        simp [hk]

/-- The union of the stars at two distinct vertices has `2n − 3` edges. -/
theorem card_bistar {n : ℕ} (i k : Fin n) (hik : i ≠ k) :
    (univ.filter (fun f : Edge n =>
      (f.1.1 = i ∨ f.1.2 = i) ∨ (f.1.1 = k ∨ f.1.2 = k))).card = 2 * n - 3 := by
  classical
  have hn : 2 ≤ n := by omega
  have hunion := Finset.filter_or (fun f : Edge n => f.1.1 = i ∨ f.1.2 = i)
    (fun f : Edge n => f.1.1 = k ∨ f.1.2 = k) univ
  have hinter : (univ.filter (fun f : Edge n => f.1.1 = i ∨ f.1.2 = i))
      ∩ (univ.filter (fun f : Edge n => f.1.1 = k ∨ f.1.2 = k)) = {edgeOf i k hik} := by
    ext f
    simp only [Finset.mem_inter, mem_filter, mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      refine edge_eq_of_mem hik ?_ ?_
      · rcases h1 with h1 | h1
        · exact Or.inl h1
        · rcases h2 with h2 | h2
          · exact Or.inr h2
          · exact absurd (h1.symm.trans h2) hik
      · rcases h1 with h1 | h1
        · rcases h2 with h2 | h2
          · exact absurd (h1.symm.trans h2) hik
          · exact Or.inr h2
        · exact Or.inl h1
    · rintro rfl
      by_cases hlt : i < k
      · rw [edgeOf_fst_lt hik hlt]
        exact ⟨Or.inl rfl, Or.inr rfl⟩
      · have hki : k < i := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hik)
        rw [edgeOf_comm, edgeOf_fst_lt (Ne.symm hik) hki]
        exact ⟨Or.inr rfl, Or.inl rfl⟩
  have hcards := Finset.card_union_add_card_inter
    (univ.filter (fun f : Edge n => f.1.1 = i ∨ f.1.2 = i))
    (univ.filter (fun f : Edge n => f.1.1 = k ∨ f.1.2 = k))
  rw [hinter, Finset.card_singleton, card_star, card_star] at hcards
  rw [hunion]
  omega

/-- The edges avoiding a vertex. -/
theorem card_costar {n : ℕ} (i : Fin n) :
    (univ.filter (fun f : Edge n => ¬ (f.1.1 = i ∨ f.1.2 = i))).card + (n - 1)
      = Fintype.card (Edge n) := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Edge n)))
    (fun f : Edge n => f.1.1 = i ∨ f.1.2 = i)
  rw [card_star, Finset.card_univ] at h
  omega

/-- The edges avoiding two distinct vertices. -/
theorem card_cobistar {n : ℕ} (i k : Fin n) (hik : i ≠ k) :
    (univ.filter (fun f : Edge n =>
      ¬ ((f.1.1 = i ∨ f.1.2 = i) ∨ (f.1.1 = k ∨ f.1.2 = k)))).card + (2 * n - 3)
      = Fintype.card (Edge n) := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Edge n)))
    (fun f : Edge n => (f.1.1 = i ∨ f.1.2 = i) ∨ (f.1.1 = k ∨ f.1.2 = k))
  rw [card_bistar i k hik, Finset.card_univ] at h
  omega

end HalfOne
