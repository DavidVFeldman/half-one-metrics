/-
  HalfOne/Checker.lean — §3, Round 3.4: the executable checker and its
  correctness theorem `goodB_correct`.

  Implementation note (permitted by §0.4 of the commission).  The naive
  `walkCount` recursion is exponential under kernel reduction, so the checker
  executed here is a *parity breadth-first closure* carried out on `Nat`
  bitmasks, for which the kernel has GMP-accelerated primitives.  The
  specification `Good` is untouched, and `goodB_correct` is proved for the
  implementation that is actually executed by the census theorems.

  The bitmask indexing uses the triangular index `eidx ⟨(i,j),_⟩ = C(j,2) + i`,
  which is injective; injectivity is all the correctness argument needs.
-/

import HalfOne.Walks

namespace HalfOne

variable {n : ℕ}

/-! ### Indexing edges by a natural number -/

/-- Triangular index of an edge: `⟨(i,j), i<j⟩ ↦ C(j,2) + i`. -/
def eidx {n : ℕ} (e : Edge n) : ℕ := Nat.choose e.1.2.val 2 + e.1.1.val

private theorem choose_two_succ (j : ℕ) : (j + 1).choose 2 = j.choose 2 + j := by
  rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_comm]

theorem eidx_inj {n : ℕ} : Function.Injective (eidx (n := n)) := by
  intro e f hef
  have hbound : ∀ g : Edge n, eidx g < (g.1.2.val + 1).choose 2 := by
    intro g
    have : g.1.1.val < g.1.2.val := g.2
    rw [choose_two_succ]
    unfold eidx
    omega
  have key : ∀ g g' : Edge n, g.1.2.val < g'.1.2.val → eidx g < eidx g' := by
    intro g g' h
    have h1 : eidx g < (g.1.2.val + 1).choose 2 := hbound g
    have h2 : (g.1.2.val + 1).choose 2 ≤ (g'.1.2.val).choose 2 :=
      Nat.choose_le_choose 2 h
    have h3 : (g'.1.2.val).choose 2 ≤ eidx g' := by unfold eidx; omega
    omega
  rcases lt_trichotomy e.1.2.val f.1.2.val with h | h | h
  · exact absurd hef (Nat.ne_of_lt (key e f h))
  · have h1 : e.1.1.val = f.1.1.val := by
      unfold eidx at hef; rw [h] at hef; omega
    apply Subtype.ext
    apply Prod.ext
    · exact Fin.ext h1
    · exact Fin.ext h
  · exact absurd hef.symm (Nat.ne_of_lt (key f e h))

/-! ### The explicit list of edges -/

/-- Explicit enumeration of `Edge n`. -/
def edgeList (n : ℕ) : List (Edge n) :=
  (List.finRange n).flatMap fun j =>
    (List.finRange n).filterMap fun i => if h : i < j then some ⟨(i, j), h⟩ else none

theorem mem_edgeList (e : Edge n) : e ∈ edgeList n := by
  obtain ⟨⟨i, j⟩, h⟩ := e
  rw [edgeList, List.mem_flatMap]
  refine ⟨j, List.mem_finRange j, ?_⟩
  rw [List.mem_filterMap]
  exact ⟨i, List.mem_finRange i, by rw [dif_pos h]⟩

theorem card_le_edgeList_length (n : ℕ) :
    Fintype.card (Edge n) ≤ (edgeList n).length := by
  classical
  have h : (Finset.univ : Finset (Edge n)) ⊆ (edgeList n).toFinset := by
    intro e _
    exact List.mem_toFinset.mpr (mem_edgeList e)
  calc Fintype.card (Edge n) = (Finset.univ : Finset (Edge n)).card := rfl
    _ ≤ (edgeList n).toFinset.card := Finset.card_le_card h
    _ ≤ (edgeList n).length := List.toFinset_card_le _

/-! ### Bitmasks -/

/-- The bitmask of a list of edges. -/
def maskOf {n : ℕ} (l : List (Edge n)) : ℕ :=
  l.foldr (fun e a => 2 ^ (eidx e) ||| a) 0

theorem testBit_maskOf {n : ℕ} (l : List (Edge n)) (f : Edge n) :
    (maskOf l).testBit (eidx f) = decide (f ∈ l) := by
  induction l with
  | nil => simp [maskOf]
  | cons e l ih =>
      rw [maskOf, List.foldr_cons, Nat.testBit_or, Nat.testBit_two_pow]
      rw [show l.foldr (fun e a => 2 ^ (eidx e) ||| a) 0 = maskOf l from rfl, ih]
      have : (decide (eidx e = eidx f)) = decide (f = e) := by
        by_cases h : f = e
        · simp [h]
        · simp only [h, decide_false, decide_eq_false_iff_not]
          exact fun hc => h (eidx_inj hc).symm
      rw [this]
      simp [List.mem_cons]

/-! ### The parity closure -/

/-- Neighbour mask of `e` in Γ. -/
def gammaNbrMask (G : HGraph n) (e : Edge n) : ℕ :=
  maskOf ((edgeList n).filter (fun f => gammaAdj G e f))

/-- The adjacency table: one `(index, neighbour mask)` pair per edge. -/
def gammaTable (G : HGraph n) : List (ℕ × ℕ) :=
  (edgeList n).map (fun e => (eidx e, gammaNbrMask G e))

/-- One relaxation: OR in the neighbour masks of everything in `src`. -/
def orStep (tbl : List (ℕ × ℕ)) (src : ℕ) (init : ℕ) : ℕ :=
  tbl.foldl (fun a p => if src.testBit p.1 then a ||| p.2 else a) init

/-- One parity step: even-reachable and odd-reachable sets grow from each other. -/
def pstep (tbl : List (ℕ × ℕ)) (S : ℕ × ℕ) : ℕ × ℕ :=
  (orStep tbl S.2 S.1, orStep tbl S.1 S.2)

/-- `k` parity steps. -/
def piter (tbl : List (ℕ × ℕ)) : ℕ → (ℕ × ℕ) → ℕ × ℕ
  | 0, S => S
  | k + 1, S => pstep tbl (piter tbl k S)

/-! ### Reading the graph off a single bitmask

A `HGraph n` produced by `Finset.univ` enumeration is a deeply nested closure,
and every application of it costs a linear search with `DecidableEq (Edge n)`.
The checker therefore packs the graph into one `Nat` (one application per
edge) and afterwards only uses GMP-accelerated bit operations. -/

/-- The whole graph, packed into one bitmask. -/
def graphMask {n : ℕ} (G : HGraph n) : ℕ :=
  maskOf ((edgeList n).filter (fun e => G e))

theorem testBit_graphMask {n : ℕ} (G : HGraph n) (e : Edge n) :
    (graphMask G).testBit (eidx e) = G e := by
  rw [graphMask, testBit_maskOf]
  by_cases h : G e = true
  · simp [List.mem_filter, mem_edgeList e, h]
  · simp only [Bool.not_eq_true] at h
    simp [List.mem_filter, h]

/-- Index of the unordered pair `{i, j}` (junk when `i = j`). -/
def pidx {n : ℕ} (i j : Fin n) : ℕ :=
  if i.val < j.val then Nat.choose j.val 2 + i.val else Nat.choose i.val 2 + j.val

/-- Adjacency read off a bitmask. -/
def adjM {n : ℕ} (msk : ℕ) (i j : Fin n) : Bool :=
  if i = j then false else msk.testBit (pidx i j)

theorem adjM_graphMask {n : ℕ} (G : HGraph n) (i j : Fin n) :
    adjM (graphMask G) i j = adj G i j := by
  unfold adjM adj
  rcases lt_trichotomy i j with h | h | h
  · rw [if_neg (Fin.ne_of_lt h), dif_pos h, pidx, if_pos (show i.val < j.val from h)]
    exact testBit_graphMask G ⟨(i, j), h⟩
  · rw [if_pos h]; subst h; rw [dif_neg (lt_irrefl i), dif_neg (lt_irrefl i)]
  · rw [if_neg (Fin.ne_of_gt h), dif_neg (asymm h), dif_pos h, pidx,
      if_neg (show ¬ (i.val < j.val) from Nat.not_lt.mpr (le_of_lt h))]
    exact testBit_graphMask G ⟨(j, i), h⟩

/-- Γ-adjacency read off a bitmask. -/
def gammaAdjM {n : ℕ} (msk : ℕ) (e f : Edge n) : Bool :=
  msk.testBit (eidx e) && msk.testBit (eidx f) && (e ≠ f) &&
  ( (e.1.1 = f.1.1 && !(adjM msk e.1.2 f.1.2)) ||
    (e.1.1 = f.1.2 && !(adjM msk e.1.2 f.1.1)) ||
    (e.1.2 = f.1.1 && !(adjM msk e.1.1 f.1.2)) ||
    (e.1.2 = f.1.2 && !(adjM msk e.1.1 f.1.1)) )

theorem gammaAdjM_graphMask {n : ℕ} (G : HGraph n) (e f : Edge n) :
    gammaAdjM (graphMask G) e f = gammaAdj G e f := by
  unfold gammaAdjM gammaAdj
  rw [testBit_graphMask, testBit_graphMask, adjM_graphMask, adjM_graphMask,
    adjM_graphMask, adjM_graphMask]

/-- Neighbour mask, computed from the packed graph. -/
def gammaNbrMaskM (n : ℕ) (msk : ℕ) (e : Edge n) : ℕ :=
  maskOf ((edgeList n).filter (fun f => gammaAdjM msk e f))

/-- The adjacency table, computed from the packed graph. -/
def gammaTableM (n : ℕ) (msk : ℕ) : List (ℕ × ℕ) :=
  (edgeList n).map (fun e => (eidx e, gammaNbrMaskM n msk e))

theorem gammaTableM_graphMask {n : ℕ} (G : HGraph n) :
    gammaTableM n (graphMask G) = gammaTable G := by
  unfold gammaTableM gammaTable gammaNbrMaskM gammaNbrMask
  refine List.map_congr_left fun e _ => ?_
  congr 2
  exact List.filter_congr fun f _ => by rw [gammaAdjM_graphMask]

/-- The executable checker, on a packed graph. -/
def goodBM (n : ℕ) (msk : ℕ) : Bool :=
  ((edgeList n).filter (fun e => msk.testBit (eidx e))).all fun e =>
    (piter (gammaTableM n msk) (2 * (edgeList n).length) (2 ^ (eidx e), 0)).2.testBit (eidx e)

/-- The executable checker: every Γ-node reaches itself with odd parity. -/
def goodB {n : ℕ} (G : HGraph n) : Bool := goodBM n (graphMask G)

theorem goodB_eq {n : ℕ} (G : HGraph n) :
    goodB G =
      ((edgeList n).filter (fun e => G e)).all fun e =>
        (piter (gammaTable G) (2 * (edgeList n).length) (2 ^ (eidx e), 0)).2.testBit (eidx e) := by
  rw [goodB, goodBM, gammaTableM_graphMask]
  congr 1
  exact List.filter_congr fun e _ => by rw [testBit_graphMask]

/-! ### Correctness -/

theorem testBit_orStep (tbl : List (ℕ × ℕ)) (src init i : ℕ) :
    (orStep tbl src init).testBit i
      = (init.testBit i || tbl.any fun p => src.testBit p.1 && p.2.testBit i) := by
  unfold orStep
  induction tbl generalizing init with
  | nil => simp
  | cons p tbl ih =>
      rw [List.foldl_cons, ih, List.any_cons]
      by_cases h : src.testBit p.1
      · rw [if_pos h, Nat.testBit_or]
        simp [h, Bool.or_assoc]
      · rw [if_neg h]
        simp [h]

/-- A walk in Γ that ends with a step. -/
theorem GWalk.snoc_iff {G : HGraph n} {e f : Edge n} {m : ℕ} :
    GWalk G e f (m + 1) ↔ ∃ g, GWalk G e g m ∧ gammaAdj G g f = true := by
  constructor
  · intro h
    obtain ⟨g, hg, w⟩ := GWalk.succ_iff.mp h.reverse
    exact ⟨g, w.reverse, by rw [gammaAdj_symm]; exact hg⟩
  · rintro ⟨g, w, h⟩
    exact w.snoc h

theorem gammaTable_any_iff {G : HGraph n} (src : ℕ) (f : Edge n) :
    ((gammaTable G).any fun p => src.testBit p.1 && p.2.testBit (eidx f)) = true
      ↔ ∃ g : Edge n, src.testBit (eidx g) = true ∧ gammaAdj G g f = true := by
  rw [List.any_eq_true]
  simp only [gammaTable, List.mem_map, Bool.and_eq_true]
  constructor
  · rintro ⟨-, ⟨g, -, rfl⟩, hs, hm⟩
    refine ⟨g, hs, ?_⟩
    rw [gammaNbrMask, testBit_maskOf] at hm
    simpa using (List.mem_filter.mp (by simpa using hm)).2
  · rintro ⟨g, hs, ha⟩
    refine ⟨(eidx g, gammaNbrMask G g), ⟨g, mem_edgeList g, rfl⟩, hs, ?_⟩
    rw [gammaNbrMask, testBit_maskOf]
    simp only [decide_eq_true_eq]
    exact List.mem_filter.mpr ⟨mem_edgeList f, by simpa using ha⟩

/-- The invariant of the parity closure. -/
theorem piter_spec (G : HGraph n) (e : Edge n) (k : ℕ) :
    (∀ f : Edge n,
      (piter (gammaTable G) k (2 ^ (eidx e), 0)).1.testBit (eidx f) = true ↔
        ∃ ℓ ≤ k, GWalk G e f ℓ ∧ Even ℓ) ∧
    (∀ f : Edge n,
      (piter (gammaTable G) k (2 ^ (eidx e), 0)).2.testBit (eidx f) = true ↔
        ∃ ℓ ≤ k, GWalk G e f ℓ ∧ Odd ℓ) := by
  induction k with
  | zero =>
      constructor
      · intro f
        simp only [piter, Nat.testBit_two_pow, decide_eq_true_eq]
        constructor
        · intro h
          exact ⟨0, le_refl 0, GWalk.zero_iff.mpr (eidx_inj h), ⟨0, rfl⟩⟩
        · rintro ⟨ℓ, hℓ, hw, -⟩
          have : ℓ = 0 := Nat.le_zero.mp hℓ
          subst this
          rw [GWalk.zero_iff.mp hw]
      · intro f
        simp only [piter, Nat.zero_testBit]
        constructor
        · intro h; exact absurd h (by simp)
        · rintro ⟨ℓ, hℓ, hw, ho⟩
          have : ℓ = 0 := Nat.le_zero.mp hℓ
          subst this
          exact absurd ho (by simp)
  | succ k ih =>
      obtain ⟨ihe, iho⟩ := ih
      set S := piter (gammaTable G) k (2 ^ (eidx e), 0) with hS
      have hstep : piter (gammaTable G) (k + 1) (2 ^ (eidx e), 0)
          = pstep (gammaTable G) S := rfl
      constructor
      · intro f
        rw [hstep, pstep, testBit_orStep, Bool.or_eq_true, gammaTable_any_iff, ihe f]
        constructor
        · rintro (⟨ℓ, hℓ, hw, hp⟩ | ⟨g, hg, hgf⟩)
          · exact ⟨ℓ, by omega, hw, hp⟩
          · obtain ⟨ℓ, hℓ, hw, hp⟩ := (iho g).mp hg
            exact ⟨ℓ + 1, by omega, hw.snoc hgf,
              Nat.even_add_one.mpr (Nat.not_even_iff_odd.mpr hp)⟩
        · rintro ⟨ℓ, hℓ, hw, hp⟩
          rcases Nat.lt_or_ge ℓ (k + 1) with h | h
          · exact Or.inl ⟨ℓ, by omega, hw, hp⟩
          · have hlk : ℓ = k + 1 := by omega
            subst hlk
            obtain ⟨g, hw', hgf⟩ := GWalk.snoc_iff.mp hw
            refine Or.inr ⟨g, (iho g).mpr ⟨k, le_refl k, hw', ?_⟩, hgf⟩
            rcases Nat.even_or_odd k with hk | hk
            · exact absurd hp (by simp [Nat.even_add_one, hk])
            · exact hk
      · intro f
        rw [hstep, pstep, testBit_orStep, Bool.or_eq_true, gammaTable_any_iff, iho f]
        constructor
        · rintro (⟨ℓ, hℓ, hw, hp⟩ | ⟨g, hg, hgf⟩)
          · exact ⟨ℓ, by omega, hw, hp⟩
          · obtain ⟨ℓ, hℓ, hw, hp⟩ := (ihe g).mp hg
            exact ⟨ℓ + 1, by omega, hw.snoc hgf,
              Nat.odd_add_one.mpr (Nat.not_odd_iff_even.mpr hp)⟩
        · rintro ⟨ℓ, hℓ, hw, hp⟩
          rcases Nat.lt_or_ge ℓ (k + 1) with h | h
          · exact Or.inl ⟨ℓ, by omega, hw, hp⟩
          · have hlk : ℓ = k + 1 := by omega
            subst hlk
            obtain ⟨g, hw', hgf⟩ := GWalk.snoc_iff.mp hw
            refine Or.inr ⟨g, (ihe g).mpr ⟨k, le_refl k, hw', ?_⟩, hgf⟩
            rcases Nat.even_or_odd k with hk | hk
            · exact hk
            · exact absurd hp (by simp [Nat.odd_add_one, hk])

/-- The checker meets its specification. -/
theorem goodB_correct {n : ℕ} (G : HGraph n) : goodB G = true ↔ Good G := by
  rw [good_iff_goodWalk]
  constructor
  · intro h e he
    rw [goodB_eq, List.all_eq_true] at h
    have hmem : e ∈ (edgeList n).filter (fun e => G e) :=
      List.mem_filter.mpr ⟨mem_edgeList e, by simpa using he⟩
    have := (piter_spec G e (2 * (edgeList n).length)).2 e
    obtain ⟨ℓ, -, hw, ho⟩ := this.mp (h e hmem)
    exact ⟨ℓ, ho, hw⟩
  · intro h
    rw [goodB_eq, List.all_eq_true]
    intro e hmem
    have he : G e = true := by simpa using (List.mem_filter.mp hmem).2
    obtain ⟨ℓ, ho, hlt, hw⟩ := odd_walk_bound_two G e (h e he)
    have hcard := card_le_edgeList_length n
    exact ((piter_spec G e (2 * (edgeList n).length)).2 e).mpr ⟨ℓ, by omega, hw, ho⟩

end HalfOne
