/-
  HalfOne/Fast.lean — an evaluation-friendly reformulation of the census.

  `goodBM` (in `HalfOne.Checker`) is the checker whose correctness is proved;
  it is, however, written for clarity, not for speed: it rebuilds the Γ-table
  once per Γ-node, and it always runs the full `2 * #edges` parity iterations.
  `goodBMfast` performs exactly the same computation with the table hoisted out
  of the loop and with the parity iteration stopped at the first fixed point;
  `goodBMfast_eq` proves the two agree.

  The second half of the file replaces the enumeration `Finset.univ :
  Finset (HGraph n)` — which materialises `2 ^ C(n,2)` closures through
  `Multiset.pi` — by a loop over the bitmasks below `2 ^ C(n,2)`, which is what
  makes the larger censuses computable at all.
-/

import HalfOne.Checker

namespace HalfOne

open Finset

variable {n : ℕ}

/-! ### Parity iteration with early exit -/

theorem piter_succ_comm (tbl : List (ℕ × ℕ)) (k : ℕ) (S : ℕ × ℕ) :
    piter tbl (k + 1) S = piter tbl k (pstep tbl S) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [piter, ih, piter]

theorem piter_fixed {tbl : List (ℕ × ℕ)} {S : ℕ × ℕ} (h : pstep tbl S = S) (k : ℕ) :
    piter tbl k S = S := by
  induction k with
  | zero => rfl
  | succ k ih => rw [piter, ih, h]

/-- `piter` with an early exit at the first fixed point. -/
def piterE (tbl : List (ℕ × ℕ)) : ℕ → (ℕ × ℕ) → ℕ × ℕ
  | 0, S => S
  | k + 1, S => let S' := pstep tbl S; if S' = S then S else piterE tbl k S'

theorem piterE_eq (tbl : List (ℕ × ℕ)) (k : ℕ) (S : ℕ × ℕ) :
    piterE tbl k S = piter tbl k S := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih =>
      have hE : piterE tbl (k + 1) S
          = if pstep tbl S = S then S else piterE tbl k (pstep tbl S) := rfl
      rw [hE, piter_succ_comm]
      by_cases h : pstep tbl S = S
      · rw [if_pos h, h, piter_fixed h]
      · rw [if_neg h, ih]

/-! ### Arithmetic-only replacements for the index functions

`eidx` and `pidx` call `Nat.choose`, whose unary recursion is evaluated once
per Γ-adjacency test — several hundred times per graph.  The variants below
use `j * (j - 1) / 2` instead, and compare edges through their indices rather
than through `DecidableEq (Edge n)`. -/

/-- `eidx`, without `Nat.choose`. -/
def eidxF {n : ℕ} (e : Edge n) : ℕ := e.1.2.val * (e.1.2.val - 1) / 2 + e.1.1.val

theorem eidxF_eq {n : ℕ} (e : Edge n) : eidxF e = eidx e := by
  unfold eidxF eidx
  rw [Nat.choose_two_right]

/-- `adjM`, without `Nat.choose`. -/
def adjMF {n : ℕ} (msk : ℕ) (i j : Fin n) : Bool :=
  if i.val = j.val then false
  else if i.val < j.val then msk.testBit (j.val * (j.val - 1) / 2 + i.val)
  else msk.testBit (i.val * (i.val - 1) / 2 + j.val)

theorem adjMF_eq {n : ℕ} (msk : ℕ) (i j : Fin n) : adjMF msk i j = adjM msk i j := by
  unfold adjMF adjM pidx
  by_cases h : i = j
  · subst h; simp
  · have hv : i.val ≠ j.val := fun hc => h (Fin.ext hc)
    rw [if_neg hv, if_neg h, Nat.choose_two_right, Nat.choose_two_right]
    by_cases hlt : i.val < j.val <;> simp [hlt]

/-- `gammaAdjM`, without `Nat.choose` and without `DecidableEq (Edge n)`. -/
def gammaAdjMF {n : ℕ} (msk : ℕ) (e f : Edge n) : Bool :=
  msk.testBit (eidxF e) && msk.testBit (eidxF f) && (eidxF e != eidxF f) &&
  ( (e.1.1.val == f.1.1.val && !(adjMF msk e.1.2 f.1.2)) ||
    (e.1.1.val == f.1.2.val && !(adjMF msk e.1.2 f.1.1)) ||
    (e.1.2.val == f.1.1.val && !(adjMF msk e.1.1 f.1.2)) ||
    (e.1.2.val == f.1.2.val && !(adjMF msk e.1.1 f.1.1)) )

theorem gammaAdjMF_eq {n : ℕ} (msk : ℕ) (e f : Edge n) :
    gammaAdjMF msk e f = gammaAdjM msk e f := by
  have hne : (eidx e != eidx f) = decide (e ≠ f) := by
    by_cases h : e = f
    · subst h; simp
    · have hx : eidx e ≠ eidx f := fun hc => h (eidx_inj hc)
      simp [h, hx]
  have hval : ∀ a b : Fin n, (a.val == b.val) = decide (a = b) := by
    intro a b
    by_cases h : a = b
    · subst h; simp
    · have hx : a.val ≠ b.val := fun hc => h (Fin.ext hc)
      simp [h, hx]
  unfold gammaAdjMF gammaAdjM
  rw [eidxF_eq, eidxF_eq, hne, hval, hval, hval, hval,
    adjMF_eq, adjMF_eq, adjMF_eq, adjMF_eq]

/-! ### The hoisted checker -/

/-- The checker of `HalfOne.Checker`, computed efficiently: the edge list and
    the Γ-table are built once per graph, the index arithmetic avoids
    `Nat.choose`, and the parity iteration stops as soon as it stabilises. -/
def goodBMfast (n : ℕ) (msk : ℕ) : Bool :=
  let el := edgeList n
  let L := el.length
  let tbl := el.map (fun e =>
    (eidxF e, (el.filter (fun f => gammaAdjMF msk e f)).foldr
      (fun f a => 2 ^ (eidxF f) ||| a) 0))
  (el.filter (fun e => msk.testBit (eidxF e))).all fun e =>
    (piterE tbl (2 * L) (2 ^ (eidxF e), 0)).2.testBit (eidxF e)

theorem goodBMfast_eq (n : ℕ) (msk : ℕ) : goodBMfast n msk = goodBM n msk := by
  have hfil : ∀ e : Edge n, (edgeList n).filter (fun f => gammaAdjMF msk e f)
      = (edgeList n).filter (fun f => gammaAdjM msk e f) :=
    fun e => List.filter_congr fun f _ => by rw [gammaAdjMF_eq]
  unfold goodBMfast goodBM gammaTableM gammaNbrMaskM
  simp only [piterE_eq, eidxF_eq, hfil]
  rfl

/-! ### Graphs from bitmasks -/

/-- The graph read off a bitmask. -/
def maskGraph (n : ℕ) (m : ℕ) : HGraph n := fun e => m.testBit (eidx e)

theorem maskGraph_graphMask (G : HGraph n) : maskGraph n (graphMask G) = G :=
  funext fun e => testBit_graphMask G e

theorem eidx_lt (e : Edge n) : eidx e < n.choose 2 := by
  have h1 : e.1.1.val < e.1.2.val := e.2
  have h2 : e.1.2.val + 1 ≤ n := e.1.2.isLt
  have h3 : (e.1.2.val + 1).choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 h2
  have h4 : (e.1.2.val + 1).choose 2 = e.1.2.val.choose 2 + e.1.2.val := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_comm]
  unfold eidx
  omega

theorem maskOf_lt (l : List (Edge n)) : maskOf l < 2 ^ n.choose 2 := by
  induction l with
  | nil => simp [maskOf]
  | cons e l ih =>
      have h1 : 2 ^ eidx e < 2 ^ n.choose 2 := Nat.pow_lt_pow_right (by norm_num) (eidx_lt e)
      have : maskOf (e :: l) = 2 ^ eidx e ||| maskOf l := rfl
      rw [this]
      exact Nat.or_lt_two_pow h1 ih

theorem graphMask_lt (G : HGraph n) : graphMask G < 2 ^ n.choose 2 :=
  maskOf_lt _

/-! ### Counting without materialising the graphs -/

/-- Tail-recursive count of the `m < N` with `p m`. -/
def countBelowAux (p : ℕ → Bool) : ℕ → ℕ → ℕ
  | 0, acc => acc
  | k + 1, acc => countBelowAux p k (acc + if p k then 1 else 0)

theorem countBelowAux_eq (p : ℕ → Bool) (N acc : ℕ) :
    countBelowAux p N acc = acc + ((Finset.range N).filter (fun m => p m = true)).card := by
  induction N generalizing acc with
  | zero => simp [countBelowAux]
  | succ N ih =>
      rw [countBelowAux, ih, Finset.range_add_one, Finset.filter_insert]
      by_cases h : p N = true
      · rw [if_pos h, if_pos h,
          Finset.card_insert_of_notMem (by simp : N ∉ (Finset.range N).filter (fun m => p m = true))]
        omega
      · rw [if_neg h, if_neg h]
        omega

/-- Divide-and-conquer count of the `m ∈ [lo, lo + 2 ^ k)` with `p m`.  Unlike
    `countBelowAux`, its recursion depth is `k`, not `2 ^ k`, which is what the
    kernel evaluator needs. -/
def countPow (p : ℕ → Bool) (lo : ℕ) : ℕ → ℕ
  | 0 => if p lo then 1 else 0
  | k + 1 => countPow p lo k + countPow p (lo + 2 ^ k) k

theorem countPow_eq (p : ℕ → Bool) (k : ℕ) : ∀ lo : ℕ,
    countPow p lo k = ((Finset.Ico lo (lo + 2 ^ k)).filter (fun m => p m = true)).card := by
  induction k with
  | zero =>
      intro lo
      rw [countPow, pow_zero, Nat.Ico_succ_singleton, Finset.filter_singleton]
      by_cases h : p lo = true
      · rw [if_pos h, if_pos h, Finset.card_singleton]
      · rw [if_neg h, if_neg h, Finset.card_empty]
  | succ k ih =>
      intro lo
      have h2 : (2 : ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
      have hsplit : Finset.Ico lo (lo + 2 ^ k) ∪ Finset.Ico (lo + 2 ^ k) (lo + 2 ^ k + 2 ^ k)
          = Finset.Ico lo (lo + 2 ^ k + 2 ^ k) :=
        Finset.Ico_union_Ico_eq_Ico (Nat.le_add_right _ _) (Nat.le_add_right _ _)
      have hdisj : Disjoint (Finset.Ico lo (lo + 2 ^ k))
          (Finset.Ico (lo + 2 ^ k) (lo + 2 ^ k + 2 ^ k)) :=
        Finset.Ico_disjoint_Ico_consecutive _ _ _
      rw [countPow, ih lo, ih (lo + 2 ^ k), h2, ← Nat.add_assoc, ← hsplit,
        Finset.filter_union,
        Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj)]

/-- The census as a loop over bitmasks: a graph is recovered from its mask, and
    a mask below `2 ^ C(n,2)` that is the mask of its own graph comes from a
    unique graph. -/
theorem census_eq_countBelow (n : ℕ) :
    (Finset.univ.filter (fun G : HGraph n => goodB G)).card
      = countBelowAux
          (fun m => goodBMfast n m && (graphMask (maskGraph n m) == m))
          (2 ^ n.choose 2) 0 := by
  classical
  rw [countBelowAux_eq, Nat.zero_add]
  refine Finset.card_nbij' (fun G => graphMask G) (fun m => maskGraph n m) ?_ ?_ ?_ ?_
  · intro G hG
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hG ⊢
    refine ⟨Finset.mem_range.mpr (graphMask_lt G), ?_⟩
    rw [Bool.and_eq_true, goodBMfast_eq, maskGraph_graphMask, beq_iff_eq]
    exact ⟨hG, rfl⟩
  · intro m hm
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hm
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
    obtain ⟨-, hm2⟩ := hm
    rw [Bool.and_eq_true, beq_iff_eq] at hm2
    rw [goodB, hm2.2, ← goodBMfast_eq]
    exact hm2.1
  · intro G _
    exact maskGraph_graphMask G
  · intro m hm
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hm
    obtain ⟨-, hm2⟩ := hm
    rw [Bool.and_eq_true, beq_iff_eq] at hm2
    exact hm2.2

theorem census_eq_countPow (n : ℕ) :
    (Finset.univ.filter (fun G : HGraph n => goodB G)).card
      = countPow
          (fun m => goodBMfast n m && (graphMask (maskGraph n m) == m))
          0 (n.choose 2) := by
  rw [census_eq_countBelow, countBelowAux_eq, countPow_eq, Nat.zero_add, Nat.zero_add,
    ← Finset.range_eq_Ico]


/-! ### The static candidate table -/


theorem testBit_maskOf' (l : List (Edge n)) (i : ℕ) :
    (maskOf l).testBit i = l.any (fun f => decide (eidx f = i)) := by
  induction l with
  | nil => simp [maskOf]
  | cons e l ih =>
      rw [maskOf, List.foldr_cons, Nat.testBit_or, Nat.testBit_two_pow]
      rw [show l.foldr (fun e a => 2 ^ (eidx e) ||| a) 0 = maskOf l from rfl, ih]
      simp [List.any_cons]

/-- The index of the "opposite" pair of two distinct edges sharing exactly one
    endpoint; `none` when they are equal or share no endpoint. -/
def oppIdx {n : ℕ} (e f : Edge n) : Option ℕ :=
  if e.1.1 = f.1.1 then (if e.1.2 = f.1.2 then none else some (pidx e.1.2 f.1.2))
  else if e.1.1 = f.1.2 then some (pidx e.1.2 f.1.1)
  else if e.1.2 = f.1.1 then some (pidx e.1.1 f.1.2)
  else if e.1.2 = f.1.2 then some (pidx e.1.1 f.1.1)
  else none

theorem gammaAdjM_oppIdx (msk : ℕ) (e f : Edge n) :
    gammaAdjM msk e f
      = (msk.testBit (eidx e) && msk.testBit (eidx f) &&
          (match oppIdx e f with | none => false | some c => !msk.testBit c)) := by
  obtain ⟨⟨a, b⟩, hab⟩ := e
  obtain ⟨⟨c, d⟩, hcd⟩ := f
  have hab' : a.val < b.val := hab
  have hcd' : c.val < d.val := hcd
  simp only [gammaAdjM, oppIdx, adjM]
  by_cases hac : a = c
  · subst hac
    by_cases hbd : b = d
    · subst hbd; simp
    · have h1 : ¬ (a = d) := by intro h; subst h; omega
      have h2 : ¬ (b = a) := by intro h; subst h; omega
      have hne : (⟨(a, b), hab⟩ : Edge n) ≠ ⟨(a, d), hcd⟩ := by
        intro h; exact hbd (congrArg (fun x => x.1.2) h)
      simp [hbd, h1, h2, hne, Ne.symm h2]
  · by_cases had : a = d
    · subst had
      have hbc : ¬ (b = c) := by intro h; subst h; omega
      have hba : ¬ (b = a) := by intro h; subst h; omega
      have hne : (⟨(a, b), hab⟩ : Edge n) ≠ ⟨(c, a), hcd⟩ := by
        intro h; exact hac (congrArg (fun x => x.1.1) h)
      simp [hac, hbc, hba, hne, Ne.symm hbc]
    · by_cases hbc : b = c
      · subst hbc
        have h1 : ¬ (b = d) := by intro h; subst h; omega
        have hne : (⟨(a, b), hab⟩ : Edge n) ≠ ⟨(b, d), hcd⟩ := by
          intro h; exact hac (congrArg (fun x => x.1.1) h)
        simp [hac, had, h1, hne]
      · by_cases hbd : b = d
        · subst hbd
          have hne : (⟨(a, b), hab⟩ : Edge n) ≠ ⟨(c, b), hcd⟩ := by
            intro h; exact hac (congrArg (fun x => x.1.1) h)
          simp [hac, had, hbc, hne]
        · have hne : (⟨(a, b), hab⟩ : Edge n) ≠ ⟨(c, d), hcd⟩ := by
            intro h; exact hac (congrArg (fun x => x.1.1) h)
          simp [hac, had, hbc, hbd, hne]

namespace Aux

theorem any_filter {α} (l : List α) (p q : α → Bool) :
    (l.filter p).any q = l.any (fun x => p x && q x) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      by_cases h : p a = true
      · rw [List.filter_cons_of_pos h, List.any_cons, ih, List.any_cons, h]; simp
      · simp only [Bool.not_eq_true] at h
        rw [List.filter_cons_of_neg (by simp [h]), ih, List.any_cons, h]; simp

theorem any_filterMap_ite {α} (l : List α) (g : α → ℕ × ℕ) (P : α → Bool) (q : ℕ × ℕ → Bool) :
    (l.filterMap (fun a => if P a then some (g a) else none)).any q
      = l.any (fun a => P a && q (g a)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      by_cases h : P a = true
      · rw [List.filterMap_cons_some (by rw [if_pos h]), List.any_cons, ih,
          List.any_cons, h]; simp
      · simp only [Bool.not_eq_true] at h
        rw [List.filterMap_cons_none (by rw [if_neg (by simp [h])]), ih, List.any_cons, h]; simp

theorem any_filterMap_optionMap {α} (l : List α) (o : α → Option ℕ) (g : α → ℕ → ℕ × ℕ)
    (q : ℕ × ℕ → Bool) :
    (l.filterMap (fun a => (o a).map (g a))).any q
      = l.any (fun a => match o a with | none => false | some c => q (g a c)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      cases h : o a with
      | none => rw [List.filterMap_cons_none (by rw [h]; rfl), ih, List.any_cons, h]; simp
      | some c =>
          rw [List.filterMap_cons_some (by rw [h]; rfl), List.any_cons, ih,
            List.any_cons, h]

end Aux

theorem Aux.and_any {α} (b : Bool) (l : List α) (p : α → Bool) :
    (b && l.any p) = l.any (fun x => b && p x) := by
  cases b <;> simp

theorem Aux.all_filterMap_ite {α} (l : List α) (g : α → ℕ × ℕ) (P : α → Bool)
    (q : ℕ × ℕ → Bool) :
    (l.filterMap (fun a => if P a then some (g a) else none)).all q
      = (l.filter P).all (fun a => q (g a)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      by_cases h : P a = true
      · rw [List.filterMap_cons_some (by rw [if_pos h]), List.all_cons, ih,
          List.filter_cons_of_pos h, List.all_cons]
      · simp only [Bool.not_eq_true] at h
        rw [List.filterMap_cons_none (by rw [if_neg (by simp [h])]), ih,
          List.filter_cons_of_neg (by simp [h])]

/-- Static Γ-candidate list of an edge: every edge sharing exactly one endpoint
    with it, together with the index of the opposite pair. -/
def candOf {n : ℕ} (e : Edge n) : List (ℕ × ℕ) :=
  (edgeList n).filterMap (fun f => (oppIdx e f).map (fun c => (eidx f, c)))

/-- The static candidate table: depends on `n` only. -/
def candList (n : ℕ) : List (ℕ × List (ℕ × ℕ)) :=
  (edgeList n).map (fun e => (eidx e, candOf e))

/-- The Γ-neighbour mask of an edge, read off its candidate list. -/
def nbrOfCand (msk : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | q :: cs =>
      if msk.testBit q.1 && !msk.testBit q.2 then 2 ^ q.1 ||| nbrOfCand msk cs
      else nbrOfCand msk cs

theorem testBit_nbrOfCand (msk : ℕ) (cs : List (ℕ × ℕ)) (i : ℕ) :
    (nbrOfCand msk cs).testBit i
      = cs.any (fun q => (msk.testBit q.1 && !msk.testBit q.2) && decide (q.1 = i)) := by
  induction cs with
  | nil => simp [nbrOfCand]
  | cons q cs ih =>
      rw [nbrOfCand, List.any_cons]
      by_cases h : (msk.testBit q.1 && !msk.testBit q.2) = true
      · rw [if_pos h, Nat.testBit_or, Nat.testBit_two_pow, ih, h]; simp
      · simp only [Bool.not_eq_true] at h
        rw [if_neg (by simp [h]), ih, h]; simp

/-- The Γ-adjacency table of a mask, built from the static candidate table;
    only the edges present in the mask get an entry. -/
def tblOfCand (msk : ℕ) (cl : List (ℕ × List (ℕ × ℕ))) : List (ℕ × ℕ) :=
  cl.filterMap (fun p => if msk.testBit p.1 then some (p.1, nbrOfCand msk p.2) else none)

theorem testBit_gammaNbrMaskM (msk i : ℕ) (e : Edge n) :
    (gammaNbrMaskM n msk e).testBit i
      = (msk.testBit (eidx e) && (nbrOfCand msk (candOf e)).testBit i) := by
  rw [gammaNbrMaskM, testBit_maskOf', Aux.any_filter, testBit_nbrOfCand, candOf,
    Aux.any_filterMap_optionMap, Aux.and_any]
  congr 1
  funext f
  rw [gammaAdjM_oppIdx]
  cases h : oppIdx e f with
  | none => simp
  | some c =>
      simp only [h]
      cases msk.testBit (eidx e) <;> cases msk.testBit (eidx f) <;>
        cases msk.testBit c <;> simp


theorem any_tblOfCand (msk src i : ℕ) :
    ((tblOfCand msk (candList n)).any fun p => src.testBit p.1 && p.2.testBit i)
      = ((gammaTableM n msk).any fun p => src.testBit p.1 && p.2.testBit i) := by
  rw [tblOfCand, candList, List.filterMap_map, gammaTableM, List.any_map]
  rw [show ((fun p : ℕ × List (ℕ × ℕ) =>
        if msk.testBit p.1 then some (p.1, nbrOfCand msk p.2) else none) ∘
        (fun e : Edge n => (eidx e, candOf e)))
      = (fun e : Edge n =>
        if msk.testBit (eidx e) then some (eidx e, nbrOfCand msk (candOf e)) else none) from rfl]
  rw [Aux.any_filterMap_ite (edgeList n) (fun e => (eidx e, nbrOfCand msk (candOf e)))
    (fun e => msk.testBit (eidx e)) (fun p => src.testBit p.1 && p.2.testBit i)]
  congr 1
  funext e
  simp only [Function.comp_apply, testBit_gammaNbrMaskM]
  cases msk.testBit (eidx e) <;> cases src.testBit (eidx e) <;> simp

theorem orStep_tblOfCand (msk src init : ℕ) :
    orStep (tblOfCand msk (candList n)) src init = orStep (gammaTableM n msk) src init :=
  Nat.eq_of_testBit_eq fun i => by
    rw [testBit_orStep, testBit_orStep, any_tblOfCand]

theorem piter_tblOfCand (msk : ℕ) (k : ℕ) (S : ℕ × ℕ) :
    piter (tblOfCand msk (candList n)) k S = piter (gammaTableM n msk) k S := by
  induction k with
  | zero => rfl
  | succ k ih => rw [piter, piter, ih, pstep, pstep, orStep_tblOfCand, orStep_tblOfCand]

/-- The census checker with the static candidate table: the Γ-table is built
    from `candList n`, which does not depend on the mask, and only the edges
    present in the mask get a table entry. -/
def goodBC (n : ℕ) (msk : ℕ) : Bool :=
  let tbl := tblOfCand msk (candList n)
  let L := (edgeList n).length
  tbl.all fun p => (piterE tbl (2 * L) (2 ^ p.1, 0)).2.testBit p.1

theorem goodBC_eq (n : ℕ) (msk : ℕ) : goodBC n msk = goodBM n msk := by
  show (tblOfCand msk (candList n)).all
      (fun p => (piterE (tblOfCand msk (candList n)) (2 * (edgeList n).length)
        (2 ^ p.1, 0)).2.testBit p.1) = _
  rw [tblOfCand, candList, List.filterMap_map]
  rw [show ((fun p : ℕ × List (ℕ × ℕ) =>
        if msk.testBit p.1 then some (p.1, nbrOfCand msk p.2) else none) ∘
        (fun e : Edge n => (eidx e, candOf e)))
      = (fun e : Edge n =>
        if msk.testBit (eidx e) then some (eidx e, nbrOfCand msk (candOf e)) else none) from rfl]
  rw [Aux.all_filterMap_ite (edgeList n) (fun e => (eidx e, nbrOfCand msk (candOf e)))
    (fun e => msk.testBit (eidx e))]
  rw [goodBM]
  have hpi : ∀ (k : ℕ) (S : ℕ × ℕ),
      piter ((edgeList n).filterMap (fun e =>
        if msk.testBit (eidx e) then some (eidx e, nbrOfCand msk (candOf e)) else none)) k S
        = piter (gammaTableM n msk) k S := by
    intro k S
    rw [← piter_tblOfCand (n := n) msk k S, tblOfCand, candList, List.filterMap_map]
    rfl
  congr 1
  funext e
  simp only [piterE_eq, hpi]




/-! ### The canonicity test, cheaply -/

/-- The mask of all edges: a static datum. -/
def fullMask (n : ℕ) : ℕ := maskOf (edgeList n)

theorem graphMask_maskGraph (n : ℕ) (m : ℕ) :
    graphMask (maskGraph n m) = m &&& fullMask n := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [graphMask, testBit_maskOf', Aux.any_filter, Nat.testBit_and, fullMask,
    testBit_maskOf', Aux.and_any]
  congr 1
  funext f
  by_cases h : eidx f = i
  · subst h; simp [maskGraph]
  · simp [h]

/-! ### The scan with component skipping -/

/-- Scan the table entries, checking that each Γ-node lies on an odd closed
    walk, but skipping the nodes already reached from an earlier node whose
    component was found to be non-bipartite. -/
def scanG (tbl : List (ℕ × ℕ)) (k : ℕ) : List (ℕ × ℕ) → ℕ → Bool
  | [], _ => true
  | p :: rest, done =>
      if done.testBit p.1 then scanG tbl k rest done
      else
        let S := piterE tbl k (2 ^ p.1, 0)
        if S.2.testBit p.1 then scanG tbl k rest (done ||| S.1 ||| S.2) else false

/-- The census checker: static candidate table, one table entry per present
    edge, one parity search per Γ-component. -/
def goodBS (cl : List (ℕ × List (ℕ × ℕ))) (L : ℕ) (msk : ℕ) : Bool :=
  let tbl := tblOfCand msk cl
  scanG tbl (2 * L) tbl 0

section Spec

variable (G : HGraph n)

theorem piterE_spec_odd (e f : Edge n) :
    (piterE (tblOfCand (graphMask G) (candList n)) (2 * (edgeList n).length)
        (2 ^ (eidx e), 0)).2.testBit (eidx f) = true
      ↔ ∃ ℓ ≤ 2 * (edgeList n).length, GWalk G e f ℓ ∧ Odd ℓ := by
  rw [piterE_eq, piter_tblOfCand, gammaTableM_graphMask]
  exact (piter_spec G e _).2 f

theorem piterE_spec_even (e f : Edge n) :
    (piterE (tblOfCand (graphMask G) (candList n)) (2 * (edgeList n).length)
        (2 ^ (eidx e), 0)).1.testBit (eidx f) = true
      ↔ ∃ ℓ ≤ 2 * (edgeList n).length, GWalk G e f ℓ ∧ Even ℓ := by
  rw [piterE_eq, piter_tblOfCand, gammaTableM_graphMask]
  exact (piter_spec G e _).1 f

/-- An odd closed walk at `e` together with a walk from `e` to `f` gives an odd
    closed walk at `f`. -/
theorem odd_closed_transfer {e f : Edge n} {a b : ℕ}
    (hw : GWalk G e f a) (hb : Odd b) (hc : GWalk G e e b) :
    ∃ ℓ, Odd ℓ ∧ GWalk G f f ℓ := by
  refine ⟨a + b + a, ?_, ((hw.reverse.append hc).append hw)⟩
  obtain ⟨t, ht⟩ := hb
  exact ⟨a + t, by omega⟩

theorem scanG_sound (l : List (ℕ × ℕ)) : ∀ done : ℕ,
    (∀ p ∈ l, ∃ f : Edge n, eidx f = p.1) →
    (∀ f : Edge n, done.testBit (eidx f) = true → ∃ ℓ, Odd ℓ ∧ GWalk G f f ℓ) →
    scanG (tblOfCand (graphMask G) (candList n)) (2 * (edgeList n).length) l done = true →
    ∀ p ∈ l, ∀ f : Edge n, eidx f = p.1 → ∃ ℓ, Odd ℓ ∧ GWalk G f f ℓ := by
  induction l with
  | nil => intro done _ _ _ p hp; exact absurd hp (List.not_mem_nil)
  | cons p rest ih =>
      intro done hex hdone h
      obtain ⟨r, hr⟩ := hex p List.mem_cons_self
      have hrest : ∀ q ∈ rest, ∃ f : Edge n, eidx f = q.1 :=
        fun q hq => hex q (List.mem_cons_of_mem _ hq)
      simp only [scanG] at h
      by_cases hd : done.testBit p.1 = true
      · rw [if_pos hd] at h
        intro q hq f hf
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hdone f (hf ▸ hd)
        · exact ih done hrest hdone h q hq f hf
      · simp only [Bool.not_eq_true] at hd
        rw [if_neg (by simp [hd])] at h
        set S := piterE (tblOfCand (graphMask G) (candList n))
          (2 * (edgeList n).length) (2 ^ p.1, 0) with hSdef
        by_cases hs : S.2.testBit p.1 = true
        · rw [if_pos hs] at h
          have hroot : ∃ ℓ, Odd ℓ ∧ GWalk G r r ℓ := by
            have h2 : S.2.testBit (eidx r) = true := by rw [hr]; exact hs
            rw [hSdef, ← hr] at h2
            obtain ⟨ℓ, -, hw, ho⟩ := (piterE_spec_odd G r r).mp h2
            exact ⟨ℓ, ho, hw⟩
          obtain ⟨ℓr, hor, hwr⟩ := hroot
          have hnew : ∀ f : Edge n, (done ||| S.1 ||| S.2).testBit (eidx f) = true →
              ∃ ℓ, Odd ℓ ∧ GWalk G f f ℓ := by
            intro f hf
            rw [Nat.testBit_or, Nat.testBit_or] at hf
            rcases Bool.or_eq_true_iff.mp hf with hf' | hf2
            · rcases Bool.or_eq_true_iff.mp hf' with hf1 | hfe
              · exact hdone f hf1
              · rw [hSdef, ← hr] at hfe
                obtain ⟨ℓ, -, hw, -⟩ := (piterE_spec_even G r f).mp hfe
                exact odd_closed_transfer G hw hor hwr
            · rw [hSdef, ← hr] at hf2
              obtain ⟨ℓ, -, hw, -⟩ := (piterE_spec_odd G r f).mp hf2
              exact odd_closed_transfer G hw hor hwr
          intro q hq g hg
          rcases List.mem_cons.mp hq with rfl | hq
          · have hgr : g = r := eidx_inj (by rw [hg, hr])
            subst hgr
            exact ⟨ℓr, hor, hwr⟩
          · exact ih _ hrest hnew h q hq g hg
        · simp only [Bool.not_eq_true] at hs
          rw [if_neg (by simp [hs])] at h
          exact absurd h (by simp)

theorem scanG_complete (l : List (ℕ × ℕ)) : ∀ done : ℕ,
    (∀ p ∈ l, ∃ f : Edge n, eidx f = p.1) →
    (∀ p ∈ l, ∀ f : Edge n, eidx f = p.1 → ∃ ℓ, Odd ℓ ∧ GWalk G f f ℓ) →
    scanG (tblOfCand (graphMask G) (candList n)) (2 * (edgeList n).length) l done = true := by
  induction l with
  | nil => intro done _ _; rfl
  | cons p rest ih =>
      intro done hex hl
      have hrest : ∀ q ∈ rest, ∃ f : Edge n, eidx f = q.1 :=
        fun q hq => hex q (List.mem_cons_of_mem _ hq)
      have hlrest : ∀ q ∈ rest, ∀ f : Edge n, eidx f = q.1 → ∃ ℓ, Odd ℓ ∧ GWalk G f f ℓ :=
        fun q hq => hl q (List.mem_cons_of_mem _ hq)
      simp only [scanG]
      by_cases hd : done.testBit p.1 = true
      · rw [if_pos hd]; exact ih done hrest hlrest
      · simp only [Bool.not_eq_true] at hd
        rw [if_neg (by simp [hd])]
        obtain ⟨r, hr⟩ := hex p List.mem_cons_self
        obtain ⟨ℓ, ho, hw⟩ := hl p List.mem_cons_self r hr
        obtain ⟨ℓ', ho', hlt, hw'⟩ := odd_walk_bound_two G r ⟨ℓ, ho, hw⟩
        have hcard := card_le_edgeList_length n
        have hs : (piterE (tblOfCand (graphMask G) (candList n))
            (2 * (edgeList n).length) (2 ^ p.1, 0)).2.testBit p.1 = true := by
          rw [← hr]
          exact (piterE_spec_odd G r r).mpr ⟨ℓ', by omega, hw', ho'⟩
        rw [if_pos hs]
        exact ih _ hrest hlrest

/-! ### The table entries are exactly the present edges -/

theorem mem_tblOfCand_graphMask (p : ℕ × ℕ) :
    p ∈ tblOfCand (graphMask G) (candList n) ↔
      ∃ e : Edge n, G e = true ∧ p = (eidx e, nbrOfCand (graphMask G) (candOf e)) := by
  rw [tblOfCand, candList, List.filterMap_map]
  constructor
  · intro hp
    obtain ⟨e, -, he⟩ := List.mem_filterMap.mp hp
    by_cases hb : (graphMask G).testBit (eidx e) = true
    · rw [Function.comp_apply, if_pos hb] at he
      exact ⟨e, by rwa [testBit_graphMask] at hb, (Option.some_inj.mp he).symm⟩
    · simp only [Bool.not_eq_true] at hb
      rw [Function.comp_apply, if_neg (by simp [hb])] at he
      exact absurd he (by simp)
  · rintro ⟨e, he, rfl⟩
    refine List.mem_filterMap.mpr ⟨e, mem_edgeList e, ?_⟩
    rw [Function.comp_apply, if_pos (by rw [testBit_graphMask]; exact he)]

theorem goodBS_eq (G : HGraph n) :
    goodBS (candList n) (edgeList n).length (graphMask G) = goodB G := by
  have hiff : goodBS (candList n) (edgeList n).length (graphMask G) = true ↔ GoodWalk G := by
    constructor
    · intro h e he
      refine scanG_sound G _ 0 ?_ ?_ h (eidx e, nbrOfCand (graphMask G) (candOf e))
        ((mem_tblOfCand_graphMask G _).mpr ⟨e, he, rfl⟩) e rfl
      · intro p hp
        obtain ⟨f, -, rfl⟩ := (mem_tblOfCand_graphMask G p).mp hp
        exact ⟨f, rfl⟩
      · intro f hf; simp at hf
    · intro h
      refine scanG_complete G _ 0 ?_ ?_
      · intro p hp
        obtain ⟨f, -, rfl⟩ := (mem_tblOfCand_graphMask G p).mp hp
        exact ⟨f, rfl⟩
      · intro p hp f hf
        obtain ⟨g, hg, rfl⟩ := (mem_tblOfCand_graphMask G p).mp hp
        have : f = g := eidx_inj hf
        subst this
        exact h f hg
  have h2 : goodB G = true ↔ GoodWalk G := by
    rw [goodB_correct, good_iff_goodWalk]
  rw [Bool.eq_iff_iff, hiff, h2]

end Spec

/-- The census as a loop over bitmasks, with the fast checker: this is the form
    the census theorems evaluate.  The candidate table, the edge count and the
    full mask are computed once, outside the loop. -/
theorem census_eq_fast (n : ℕ) :
    (Finset.univ.filter (fun G : HGraph n => goodB G)).card
      = (let cl := candList n
         let L := (edgeList n).length
         let F := fullMask n
         countPow (fun m => (m &&& F == m) && goodBS cl L m) 0 (n.choose 2)) := by
  show _ = countPow (fun m => (m &&& fullMask n == m) &&
      goodBS (candList n) (edgeList n).length m) 0 (n.choose 2)
  classical
  rw [countPow_eq, Nat.zero_add, ← Finset.range_eq_Ico]
  refine Finset.card_nbij' (fun G => graphMask G) (fun m => maskGraph n m) ?_ ?_ ?_ ?_
  · intro G hG
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hG ⊢
    refine ⟨Finset.mem_range.mpr (graphMask_lt G), ?_⟩
    have hcan : graphMask G &&& fullMask n = graphMask G := by
      rw [← graphMask_maskGraph, maskGraph_graphMask]
    rw [Bool.and_eq_true, beq_iff_eq, goodBS_eq]
    exact ⟨hcan, hG⟩
  · intro m hm
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hm
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
    obtain ⟨-, hm2⟩ := hm
    rw [Bool.and_eq_true, beq_iff_eq] at hm2
    have hcan : graphMask (maskGraph n m) = m := by rw [graphMask_maskGraph]; exact hm2.1
    rw [← goodBS_eq, hcan]
    exact hm2.2
  · intro G _
    exact maskGraph_graphMask G
  · intro m hm
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hm
    obtain ⟨-, hm2⟩ := hm
    rw [Bool.and_eq_true, beq_iff_eq] at hm2
    show graphMask (maskGraph n m) = m
    rw [graphMask_maskGraph]
    exact hm2.1


end HalfOne
