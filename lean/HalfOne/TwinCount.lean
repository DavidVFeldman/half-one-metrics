/-
  HalfOne/TwinCount.lean — §7, Round 4: the exact twin counts and the
  Bonferroni bound `twin_bound`.
-/

import HalfOne.Twins
import HalfOne.Counting

namespace HalfOne

open Finset

/-- Exact count: graphs in which a FIXED pair is a true twin pair.
    (n − 1 constrained coordinates; the rest free.)

    The hypothesis `2 ≤ n` is part of the commissioned statement; it is not
    needed for the proof (an edge can only exist when `2 ≤ n`). -/
theorem twin_count_single (n : ℕ) (e : Edge n) (hn : 2 ≤ n) :
    (Finset.univ.filter (fun G : HGraph n => TrueTwins G e)).card
      = 2 ^ (Fintype.card (Edge n) - (n - 1)) := by
  classical
  have hji : e.1.2 ≠ e.1.1 := ne_of_gt e.2
  set T : Finset (Edge n) :=
    univ.filter (fun f : Edge n => ¬ (f.1.1 = e.1.1 ∨ f.1.2 = e.1.1)) with hTdef
  have hTcard : T.card = Fintype.card (Edge n) - (n - 1) := by
    have h := card_costar (n := n) e.1.1
    rw [hTdef]
    omega
  set ext : HGraph n → HGraph n := fun H f =>
    if f = e then true
    else if f.1.1 = e.1.1 then adj H e.1.2 f.1.2
    else if f.1.2 = e.1.1 then adj H e.1.2 f.1.1
    else H f with hext
  have hmemT : ∀ g : Edge n, g.1.1 ≠ e.1.1 → g.1.2 ≠ e.1.1 → g ∈ T := by
    intro g h1 h2
    rw [hTdef, mem_filter]
    exact ⟨mem_univ _, by push_neg; exact ⟨h1, h2⟩⟩
  -- the edge `{e.1.2, k}` avoids `e.1.1` whenever `k ≠ e.1.1`
  have hedgeT : ∀ k : Fin n, ∀ hk : e.1.2 ≠ k, k ≠ e.1.1 → edgeOf e.1.2 k hk ∈ T := by
    intro k hk hk1
    apply hmemT
    · rcases edgeOf_endpoints e.1.2 k hk with ⟨ha, _⟩ | ⟨ha, _⟩
      · rw [ha]; exact hji
      · rw [ha]; exact hk1
    · rcases edgeOf_endpoints e.1.2 k hk with ⟨_, hb⟩ | ⟨_, hb⟩
      · rw [hb]; exact hk1
      · rw [hb]; exact hji
  have hout : ∀ (H : HGraph n) (f : Edge n), f.1.1 ≠ e.1.1 → f.1.2 ≠ e.1.1 →
      ext H f = H f := by
    intro H f h1 h2
    have hne : f ≠ e := by intro h; rw [h] at h1; exact h1 rfl
    simp only [hext, if_neg hne, if_neg h1, if_neg h2]
  have hkey : ∀ (H : HGraph n) (k : Fin n), k ≠ e.1.1 → k ≠ e.1.2 →
      adj (ext H) e.1.1 k = adj H e.1.2 k := by
    intro H k hk1 hk2
    rw [adj_eq_edgeOf _ _ _ (Ne.symm hk1)]
    rcases edgeOf_endpoints e.1.1 k (Ne.symm hk1) with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have hne : edgeOf e.1.1 k (Ne.symm hk1) ≠ e := by
        intro h; rw [h] at hb; exact hk2 hb.symm
      simp only [hext]
      rw [if_neg hne, if_pos ha, hb]
    · have hne : edgeOf e.1.1 k (Ne.symm hk1) ≠ e := by
        intro h; rw [h] at ha; exact hk1 ha.symm
      have hne1 : ¬ ((edgeOf e.1.1 k (Ne.symm hk1)).1.1 = e.1.1) := by
        rw [ha]; exact hk1
      simp only [hext]
      rw [if_neg hne, if_neg hne1, if_pos hb, ha]
  have hkey2 : ∀ (H : HGraph n) (k : Fin n), k ≠ e.1.1 → k ≠ e.1.2 →
      adj (ext H) e.1.2 k = adj H e.1.2 k := by
    intro H k hk1 hk2
    rw [adj_eq_edgeOf (ext H) _ _ (Ne.symm hk2), adj_eq_edgeOf H _ _ (Ne.symm hk2)]
    apply hout
    · rcases edgeOf_endpoints e.1.2 k (Ne.symm hk2) with ⟨ha, _⟩ | ⟨ha, _⟩
      · rw [ha]; exact hji
      · rw [ha]; exact hk1
    · rcases edgeOf_endpoints e.1.2 k (Ne.symm hk2) with ⟨_, hb⟩ | ⟨_, hb⟩
      · rw [hb]; exact hk1
      · rw [hb]; exact hji
  rw [← hTcard]
  refine card_filter_of_extension (fun G : HGraph n => TrueTwins G e) T ext ?_ ?_ ?_ ?_
  · intro H
    refine ⟨?_, ?_⟩
    · simp only [hext, if_pos rfl]
    · intro k hk1 hk2
      rw [hkey H k hk1 hk2, hkey2 H k hk1 hk2]
  · intro H x hx
    rw [hTdef, mem_filter] at hx
    push_neg at hx
    exact hout H x hx.2.1 hx.2.2
  · intro G hG
    funext f
    by_cases hfe : f = e
    · rw [hfe]
      simp only [hext, if_pos rfl]
      exact hG.1.symm
    · by_cases h1 : f.1.1 = e.1.1
      · have hf2i : f.1.2 ≠ e.1.1 := by rw [← h1]; exact f.2.ne'
        have hf2j : f.1.2 ≠ e.1.2 := fun h => hfe (edge_ext h1 h)
        simp only [hext, if_neg hfe, if_pos h1]
        rw [← hG.2 f.1.2 hf2i hf2j, apply_eq_adj G f, h1]
      · by_cases h2 : f.1.2 = e.1.1
        · have hf1j : f.1.1 ≠ e.1.2 := by
            have h3 := f.2
            rw [h2] at h3
            intro hc
            rw [hc] at h3
            exact absurd (h3.trans e.2) (lt_irrefl _)
          simp only [hext, if_neg hfe, if_neg h1, if_pos h2]
          rw [← hG.2 f.1.1 h1 hf1j, apply_eq_adj G f, h2, adj_symm G f.1.1 e.1.1]
        · simp only [hext, if_neg hfe, if_neg h1, if_neg h2]
  · intro H H' hHH'
    have hadj : ∀ k : Fin n, k ≠ e.1.1 → k ≠ e.1.2 → adj H e.1.2 k = adj H' e.1.2 k := by
      intro k hk1 hk2
      rw [adj_eq_edgeOf H _ _ (Ne.symm hk2), adj_eq_edgeOf H' _ _ (Ne.symm hk2)]
      exact hHH' _ (hedgeT k (Ne.symm hk2) hk1)
    funext f
    by_cases hfe : f = e
    · simp only [hext, if_pos hfe]
    · by_cases h1 : f.1.1 = e.1.1
      · have hf2i : f.1.2 ≠ e.1.1 := by rw [← h1]; exact f.2.ne'
        have hf2j : f.1.2 ≠ e.1.2 := fun h => hfe (edge_ext h1 h)
        simp only [hext, if_neg hfe, if_pos h1]
        exact hadj f.1.2 hf2i hf2j
      · by_cases h2 : f.1.2 = e.1.1
        · have hf1j : f.1.1 ≠ e.1.2 := by
            have h3 := f.2
            rw [h2] at h3
            intro hc
            rw [hc] at h3
            exact absurd (h3.trans e.2) (lt_irrefl _)
          simp only [hext, if_neg hfe, if_neg h1, if_pos h2]
          exact hadj f.1.1 h1 hf1j
        · simp only [hext, if_neg hfe, if_neg h1, if_neg h2]
          exact hHH' f (hmemT f h1 h2)

/-- Exact count, shared-vertex intersection, general form: the two edges
    `{i,j}` and `{i,k}` share the vertex `i`.  The two twin conditions force
    all three pairs among i,j,k present and triple agreement outside:
    2n − 3 constrained coordinates. -/
theorem twin_count_shared_gen (n : ℕ) (i j k : Fin n)
    (hijne : i ≠ j) (hikne : i ≠ k) (hjk : j ≠ k) :
    (Finset.univ.filter (fun G : HGraph n =>
        TrueTwins G (edgeOf i j hijne) ∧ TrueTwins G (edgeOf i k hikne))).card
      = 2 ^ (Fintype.card (Edge n) - (2 * n - 3)) := by
  classical
  set T : Finset (Edge n) := univ.filter (fun g : Edge n =>
    ¬ ((g.1.1 = i ∨ g.1.2 = i) ∨ (g.1.1 = k ∨ g.1.2 = k))) with hTdef
  have hTcard : T.card = Fintype.card (Edge n) - (2 * n - 3) := by
    have h := card_cobistar (n := n) i k hikne
    rw [hTdef]
    omega
  set ext : HGraph n → HGraph n := fun H g =>
    if ((g.1.1 = i ∨ g.1.1 = j ∨ g.1.1 = k) ∧ (g.1.2 = i ∨ g.1.2 = j ∨ g.1.2 = k)) then true
    else if (g.1.1 = i ∨ g.1.1 = k) then adj H j g.1.2
    else if (g.1.2 = i ∨ g.1.2 = k) then adj H j g.1.1
    else H g with hext
  have hmemT : ∀ g : Edge n, ¬(g.1.1 = i ∨ g.1.1 = k) → ¬(g.1.2 = i ∨ g.1.2 = k) → g ∈ T := by
    intro g h1 h2
    rw [hTdef, mem_filter]
    refine ⟨mem_univ _, ?_⟩
    rintro ((h | h) | (h | h))
    · exact h1 (Or.inl h)
    · exact h2 (Or.inl h)
    · exact h1 (Or.inr h)
    · exact h2 (Or.inr h)
  have hjik : ¬(j = i ∨ j = k) := by
    rintro (h | h)
    · exact hijne h.symm
    · exact hjk h
  have hedgeT : ∀ (p : Fin n) (hp : j ≠ p), p ≠ i → p ≠ k → edgeOf j p hp ∈ T := by
    intro p hp hpi hpk
    have hpn : ¬(p = i ∨ p = k) := by
      rintro (h | h)
      · exact hpi h
      · exact hpk h
    refine hmemT _ ?_ ?_
    · rcases edgeOf_endpoints j p hp with ⟨ha, _⟩ | ⟨ha, _⟩ <;> rw [ha]
      · exact hjik
      · exact hpn
    · rcases edgeOf_endpoints j p hp with ⟨_, hb⟩ | ⟨_, hb⟩ <;> rw [hb]
      · exact hpn
      · exact hjik
  -- the four shapes of `ext`
  have S1 : ∀ (H : HGraph n) (g : Edge n), (g.1.1 = i ∨ g.1.1 = j ∨ g.1.1 = k) →
      (g.1.2 = i ∨ g.1.2 = j ∨ g.1.2 = k) → ext H g = true := by
    intro H g h1 h2
    simp only [hext]
    rw [if_pos ⟨h1, h2⟩]
  have S2 : ∀ (H : HGraph n) (g : Edge n), (g.1.1 = i ∨ g.1.1 = k) →
      ¬(g.1.2 = i ∨ g.1.2 = j ∨ g.1.2 = k) → ext H g = adj H j g.1.2 := by
    intro H g h1 h2
    have hc : ¬ ((g.1.1 = i ∨ g.1.1 = j ∨ g.1.1 = k) ∧
        (g.1.2 = i ∨ g.1.2 = j ∨ g.1.2 = k)) := fun hc => h2 hc.2
    simp only [hext]
    rw [if_neg hc, if_pos h1]
  have S3 : ∀ (H : HGraph n) (g : Edge n), ¬(g.1.1 = i ∨ g.1.1 = j ∨ g.1.1 = k) →
      (g.1.2 = i ∨ g.1.2 = k) → ext H g = adj H j g.1.1 := by
    intro H g h1 h2
    have hc : ¬ ((g.1.1 = i ∨ g.1.1 = j ∨ g.1.1 = k) ∧
        (g.1.2 = i ∨ g.1.2 = j ∨ g.1.2 = k)) := fun hc => h1 hc.1
    have hc2 : ¬ (g.1.1 = i ∨ g.1.1 = k) := by
      rintro (h | h)
      · exact h1 (Or.inl h)
      · exact h1 (Or.inr (Or.inr h))
    simp only [hext]
    rw [if_neg hc, if_neg hc2, if_pos h2]
  have S4 : ∀ (H : HGraph n) (g : Edge n), ¬(g.1.1 = i ∨ g.1.1 = k) →
      ¬(g.1.2 = i ∨ g.1.2 = k) → ext H g = H g := by
    intro H g h1 h2
    have hne : g.1.1 ≠ g.1.2 := ne_of_lt g.2
    have hc : ¬ ((g.1.1 = i ∨ g.1.1 = j ∨ g.1.1 = k) ∧
        (g.1.2 = i ∨ g.1.2 = j ∨ g.1.2 = k)) := by
      rintro ⟨ha, hb⟩
      have ha' : g.1.1 = j := by
        rcases ha with h | h | h
        · exact absurd (Or.inl h) h1
        · exact h
        · exact absurd (Or.inr h) h1
      have hb' : g.1.2 = j := by
        rcases hb with h | h | h
        · exact absurd (Or.inl h) h2
        · exact h
        · exact absurd (Or.inr h) h2
      exact hne (ha'.trans hb'.symm)
    simp only [hext]
    rw [if_neg hc, if_neg h1, if_neg h2]
  -- the same three shapes at the level of `adj`
  have A1 : ∀ (H : HGraph n) (x y : Fin n), x ≠ y → (x = i ∨ x = j ∨ x = k) →
      (y = i ∨ y = j ∨ y = k) → adj (ext H) x y = true := by
    intro H x y hxy hx hy
    rw [adj_eq_edgeOf _ _ _ hxy]
    rcases edgeOf_endpoints x y hxy with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact S1 H _ (by rw [ha]; exact hx) (by rw [hb]; exact hy)
    · exact S1 H _ (by rw [ha]; exact hy) (by rw [hb]; exact hx)
  have A2 : ∀ (H : HGraph n) (x y : Fin n), x ≠ y → (x = i ∨ x = k) →
      ¬(y = i ∨ y = j ∨ y = k) → adj (ext H) x y = adj H j y := by
    intro H x y hxy hx hy
    rw [adj_eq_edgeOf _ _ _ hxy]
    rcases edgeOf_endpoints x y hxy with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [S2 H _ (by rw [ha]; exact hx) (by rw [hb]; exact hy), hb]
    · rw [S3 H _ (by rw [ha]; exact hy) (by rw [hb]; exact hx), ha]
  have A3 : ∀ (H : HGraph n) (x y : Fin n), x ≠ y → ¬(x = i ∨ x = k) → ¬(y = i ∨ y = k) →
      adj (ext H) x y = adj H x y := by
    intro H x y hxy hx hy
    rw [adj_eq_edgeOf (ext H) _ _ hxy, adj_eq_edgeOf H _ _ hxy]
    rcases edgeOf_endpoints x y hxy with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact S4 H _ (by rw [ha]; exact hx) (by rw [hb]; exact hy)
    · exact S4 H _ (by rw [ha]; exact hy) (by rw [hb]; exact hx)
  rw [← hTcard]
  refine card_filter_of_extension _ T ext ?_ ?_ ?_ ?_
  · intro H
    refine ⟨(trueTwins_edgeOf_iff (ext H) i j hijne).mpr
        ⟨A1 H i j hijne (Or.inl rfl) (Or.inr (Or.inl rfl)), ?_⟩,
      (trueTwins_edgeOf_iff (ext H) i k hikne).mpr
        ⟨A1 H i k hikne (Or.inl rfl) (Or.inr (Or.inr rfl)), ?_⟩⟩
    · intro p hpi hpj
      by_cases hpk : p = k
      · subst hpk
        rw [A1 H i p hikne (Or.inl rfl) (Or.inr (Or.inr rfl)),
          A1 H j p hjk (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))]
      · have hp : ¬(p = i ∨ p = j ∨ p = k) := by
          rintro (h | h | h)
          · exact hpi h
          · exact hpj h
          · exact hpk h
        rw [A2 H i p (Ne.symm hpi) (Or.inl rfl) hp,
          A3 H j p (Ne.symm hpj) hjik (by
            rintro (h | h)
            · exact hpi h
            · exact hpk h)]
    · intro p hpi hpk
      by_cases hpj : p = j
      · subst hpj
        rw [A1 H i p hijne (Or.inl rfl) (Or.inr (Or.inl rfl)),
          A1 H k p (Ne.symm hjk) (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl))]
      · have hp : ¬(p = i ∨ p = j ∨ p = k) := by
          rintro (h | h | h)
          · exact hpi h
          · exact hpj h
          · exact hpk h
        rw [A2 H i p (Ne.symm hpi) (Or.inl rfl) hp,
          A2 H k p (Ne.symm hpk) (Or.inr rfl) hp]
  · intro H x hx
    rw [hTdef, mem_filter] at hx
    refine S4 H x ?_ ?_
    · rintro (h | h)
      · exact hx.2 (Or.inl (Or.inl h))
      · exact hx.2 (Or.inr (Or.inl h))
    · rintro (h | h)
      · exact hx.2 (Or.inl (Or.inr h))
      · exact hx.2 (Or.inr (Or.inr h))
  · rintro G ⟨ht1, ht2⟩
    obtain ⟨hGe, hGe2⟩ := (trueTwins_edgeOf_iff G i j hijne).mp ht1
    obtain ⟨hGf, hGf2⟩ := (trueTwins_edgeOf_iff G i k hikne).mp ht2
    funext g
    by_cases c0 : (g.1.1 = i ∨ g.1.1 = j ∨ g.1.1 = k) ∧ (g.1.2 = i ∨ g.1.2 = j ∨ g.1.2 = k)
    · rw [S1 G g c0.1 c0.2]
      symm
      rw [apply_eq_adj G g]
      have hne : g.1.1 ≠ g.1.2 := ne_of_lt g.2
      rcases c0.1 with h1 | h1 | h1 <;> rcases c0.2 with h2 | h2 | h2
      · exact absurd (h1.trans h2.symm) hne
      · rw [h1, h2]; exact hGe
      · rw [h1, h2]; exact hGf
      · rw [h1, h2, adj_symm G j i]; exact hGe
      · exact absurd (h1.trans h2.symm) hne
      · rw [h1, h2, ← hGe2 k (Ne.symm hikne) (Ne.symm hjk)]; exact hGf
      · rw [h1, h2, adj_symm G k i]; exact hGf
      · rw [h1, h2, adj_symm G k j, ← hGe2 k (Ne.symm hikne) (Ne.symm hjk)]; exact hGf
      · exact absurd (h1.trans h2.symm) hne
    · by_cases c1 : g.1.1 = i ∨ g.1.1 = k
      · have hA : g.1.1 = i ∨ g.1.1 = j ∨ g.1.1 = k := by
          rcases c1 with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        have hc2 : ¬(g.1.2 = i ∨ g.1.2 = j ∨ g.1.2 = k) := fun h => c0 ⟨hA, h⟩
        rw [S2 G g c1 hc2]
        have hp1 : g.1.2 ≠ i := fun h => hc2 (Or.inl h)
        have hp2 : g.1.2 ≠ j := fun h => hc2 (Or.inr (Or.inl h))
        have hp3 : g.1.2 ≠ k := fun h => hc2 (Or.inr (Or.inr h))
        rcases c1 with hx | hx
        · rw [apply_eq_adj G g, hx, hGe2 g.1.2 hp1 hp2]
        · rw [apply_eq_adj G g, hx, ← hGf2 g.1.2 hp1 hp3, hGe2 g.1.2 hp1 hp2]
      · by_cases c2 : g.1.2 = i ∨ g.1.2 = k
        · have hB : g.1.2 = i ∨ g.1.2 = j ∨ g.1.2 = k := by
            rcases c2 with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inr h)
          have hc1 : ¬(g.1.1 = i ∨ g.1.1 = j ∨ g.1.1 = k) := by
            rintro (h | h | h)
            · exact c1 (Or.inl h)
            · exact c0 ⟨Or.inr (Or.inl h), hB⟩
            · exact c1 (Or.inr h)
          rw [S3 G g hc1 c2]
          have hp1 : g.1.1 ≠ i := fun h => hc1 (Or.inl h)
          have hp2 : g.1.1 ≠ j := fun h => hc1 (Or.inr (Or.inl h))
          have hp3 : g.1.1 ≠ k := fun h => hc1 (Or.inr (Or.inr h))
          rcases c2 with hy | hy
          · rw [apply_eq_adj G g, hy, adj_symm G g.1.1 i, hGe2 g.1.1 hp1 hp2]
          · rw [apply_eq_adj G g, hy, adj_symm G g.1.1 k,
              ← hGf2 g.1.1 hp1 hp3, hGe2 g.1.1 hp1 hp2]
        · rw [S4 G g c1 c2]
  · intro H H' hHH'
    funext g
    by_cases c0 : (g.1.1 = i ∨ g.1.1 = j ∨ g.1.1 = k) ∧ (g.1.2 = i ∨ g.1.2 = j ∨ g.1.2 = k)
    · rw [S1 H g c0.1 c0.2, S1 H' g c0.1 c0.2]
    · by_cases c1 : g.1.1 = i ∨ g.1.1 = k
      · have hA : g.1.1 = i ∨ g.1.1 = j ∨ g.1.1 = k := by
          rcases c1 with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        have hc2 : ¬(g.1.2 = i ∨ g.1.2 = j ∨ g.1.2 = k) := fun h => c0 ⟨hA, h⟩
        have hne : j ≠ g.1.2 := fun h => hc2 (Or.inr (Or.inl h.symm))
        rw [S2 H g c1 hc2, S2 H' g c1 hc2, adj_eq_edgeOf H j g.1.2 hne,
          adj_eq_edgeOf H' j g.1.2 hne]
        exact hHH' _ (hedgeT g.1.2 hne (fun h => hc2 (Or.inl h))
          (fun h => hc2 (Or.inr (Or.inr h))))
      · by_cases c2 : g.1.2 = i ∨ g.1.2 = k
        · have hB : g.1.2 = i ∨ g.1.2 = j ∨ g.1.2 = k := by
            rcases c2 with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inr h)
          have hc1 : ¬(g.1.1 = i ∨ g.1.1 = j ∨ g.1.1 = k) := by
            rintro (h | h | h)
            · exact c1 (Or.inl h)
            · exact c0 ⟨Or.inr (Or.inl h), hB⟩
            · exact c1 (Or.inr h)
          have hne : j ≠ g.1.1 := fun h => hc1 (Or.inr (Or.inl h.symm))
          rw [S3 H g hc1 c2, S3 H' g hc1 c2, adj_eq_edgeOf H j g.1.1 hne,
            adj_eq_edgeOf H' j g.1.1 hne]
          exact hHH' _ (hedgeT g.1.1 hne (fun h => hc1 (Or.inl h))
            (fun h => hc1 (Or.inr (Or.inr h))))
        · rw [S4 H g c1 c2, S4 H' g c1 c2]
          exact hHH' g (hmemT g c1 c2)

/-- Exact count, shared-vertex intersection: e = {i,j}, f = {i,k}. -/
theorem twin_count_shared (n : ℕ) (i j k : Fin n)
    (hij : i < j) (hik : i < k) (hjk : j ≠ k) :
    (Finset.univ.filter (fun G : HGraph n =>
        TrueTwins G ⟨(i, j), hij⟩ ∧ TrueTwins G ⟨(i, k), hik⟩)).card
      = 2 ^ (Fintype.card (Edge n) - (2 * n - 3)) := by
  rw [← edgeOf_fst_lt (ne_of_lt hij) hij, ← edgeOf_fst_lt (ne_of_lt hik) hik]
  exact twin_count_shared_gen n i j k (ne_of_lt hij) (ne_of_lt hik) hjk

/-- Exact count, disjoint intersection, general form: `{i,j}` and `{k,l}` are
    two disjoint edges.  Again 2n − 3 constrained coordinates (two base pairs,
    2(n−4) outside agreements, 3 of the 4 crossing bits). -/
theorem twin_count_disjoint_gen (n : ℕ) (i j k l : Fin n)
    (hijne : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hklne : k ≠ l) :
    (Finset.univ.filter (fun G : HGraph n =>
        TrueTwins G (edgeOf i j hijne) ∧ TrueTwins G (edgeOf k l hklne))).card
      = 2 ^ (Fintype.card (Edge n) - (2 * n - 3)) := by
  classical
  have hjik : ¬(j = i ∨ j = k) := by
    rintro (h1 | h1)
    · exact hijne h1.symm
    · exact hjk h1
  have hlik : ¬(l = i ∨ l = k) := by
    rintro (h1 | h1)
    · exact hil h1.symm
    · exact hklne h1.symm
  set T : Finset (Edge n) := univ.filter (fun g : Edge n =>
    ¬ ((g.1.1 = i ∨ g.1.2 = i) ∨ (g.1.1 = k ∨ g.1.2 = k))) with hTdef
  have hTcard : T.card = Fintype.card (Edge n) - (2 * n - 3) := by
    have hc := card_cobistar (n := n) i k hik
    rw [hTdef]
    omega
  set ext : HGraph n → HGraph n := fun H g =>
    if (g.1.1 = i ∧ g.1.2 = j) ∨ (g.1.1 = j ∧ g.1.2 = i) then true
    else if (g.1.1 = k ∧ g.1.2 = l) ∨ (g.1.1 = l ∧ g.1.2 = k) then true
    else if ((g.1.1 = i ∨ g.1.1 = j ∨ g.1.1 = k ∨ g.1.1 = l) ∧
             (g.1.2 = i ∨ g.1.2 = j ∨ g.1.2 = k ∨ g.1.2 = l) ∧
             (g.1.1 = i ∨ g.1.1 = k ∨ g.1.2 = i ∨ g.1.2 = k)) then adj H j l
    else if g.1.1 = i then adj H j g.1.2
    else if g.1.2 = i then adj H j g.1.1
    else if g.1.1 = k then adj H l g.1.2
    else if g.1.2 = k then adj H l g.1.1
    else H g with hext
  -- the eight shapes of `ext`
  have S1 : ∀ (H : HGraph n) (c : Edge n),
      ((c.1.1 = i ∧ c.1.2 = j) ∨ (c.1.1 = j ∧ c.1.2 = i)) → ext H c = true := by
    intro H c hc; simp only [hext]; rw [if_pos hc]
  have S2 : ∀ (H : HGraph n) (c : Edge n),
      ¬((c.1.1 = i ∧ c.1.2 = j) ∨ (c.1.1 = j ∧ c.1.2 = i)) →
      ((c.1.1 = k ∧ c.1.2 = l) ∨ (c.1.1 = l ∧ c.1.2 = k)) → ext H c = true := by
    intro H c h1 hc; simp only [hext]; rw [if_neg h1, if_pos hc]
  have S3 : ∀ (H : HGraph n) (c : Edge n),
      ¬((c.1.1 = i ∧ c.1.2 = j) ∨ (c.1.1 = j ∧ c.1.2 = i)) →
      ¬((c.1.1 = k ∧ c.1.2 = l) ∨ (c.1.1 = l ∧ c.1.2 = k)) →
      ((c.1.1 = i ∨ c.1.1 = j ∨ c.1.1 = k ∨ c.1.1 = l) ∧
       (c.1.2 = i ∨ c.1.2 = j ∨ c.1.2 = k ∨ c.1.2 = l) ∧
       (c.1.1 = i ∨ c.1.1 = k ∨ c.1.2 = i ∨ c.1.2 = k)) → ext H c = adj H j l := by
    intro H c h1 h2 hc; simp only [hext]; rw [if_neg h1, if_neg h2, if_pos hc]
  have S4 : ∀ (H : HGraph n) (c : Edge n),
      ¬((c.1.1 = i ∧ c.1.2 = j) ∨ (c.1.1 = j ∧ c.1.2 = i)) →
      ¬((c.1.1 = k ∧ c.1.2 = l) ∨ (c.1.1 = l ∧ c.1.2 = k)) →
      ¬((c.1.1 = i ∨ c.1.1 = j ∨ c.1.1 = k ∨ c.1.1 = l) ∧
        (c.1.2 = i ∨ c.1.2 = j ∨ c.1.2 = k ∨ c.1.2 = l) ∧
        (c.1.1 = i ∨ c.1.1 = k ∨ c.1.2 = i ∨ c.1.2 = k)) →
      c.1.1 = i → ext H c = adj H j c.1.2 := by
    intro H c h1 h2 h3 hc; simp only [hext]; rw [if_neg h1, if_neg h2, if_neg h3, if_pos hc]
  have S5 : ∀ (H : HGraph n) (c : Edge n),
      ¬((c.1.1 = i ∧ c.1.2 = j) ∨ (c.1.1 = j ∧ c.1.2 = i)) →
      ¬((c.1.1 = k ∧ c.1.2 = l) ∨ (c.1.1 = l ∧ c.1.2 = k)) →
      ¬((c.1.1 = i ∨ c.1.1 = j ∨ c.1.1 = k ∨ c.1.1 = l) ∧
        (c.1.2 = i ∨ c.1.2 = j ∨ c.1.2 = k ∨ c.1.2 = l) ∧
        (c.1.1 = i ∨ c.1.1 = k ∨ c.1.2 = i ∨ c.1.2 = k)) →
      ¬(c.1.1 = i) → c.1.2 = i → ext H c = adj H j c.1.1 := by
    intro H c h1 h2 h3 h4 hc
    simp only [hext]; rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos hc]
  have S6 : ∀ (H : HGraph n) (c : Edge n),
      ¬((c.1.1 = i ∧ c.1.2 = j) ∨ (c.1.1 = j ∧ c.1.2 = i)) →
      ¬((c.1.1 = k ∧ c.1.2 = l) ∨ (c.1.1 = l ∧ c.1.2 = k)) →
      ¬((c.1.1 = i ∨ c.1.1 = j ∨ c.1.1 = k ∨ c.1.1 = l) ∧
        (c.1.2 = i ∨ c.1.2 = j ∨ c.1.2 = k ∨ c.1.2 = l) ∧
        (c.1.1 = i ∨ c.1.1 = k ∨ c.1.2 = i ∨ c.1.2 = k)) →
      ¬(c.1.1 = i) → ¬(c.1.2 = i) → c.1.1 = k → ext H c = adj H l c.1.2 := by
    intro H c h1 h2 h3 h4 h5 hc
    simp only [hext]; rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos hc]
  have S7 : ∀ (H : HGraph n) (c : Edge n),
      ¬((c.1.1 = i ∧ c.1.2 = j) ∨ (c.1.1 = j ∧ c.1.2 = i)) →
      ¬((c.1.1 = k ∧ c.1.2 = l) ∨ (c.1.1 = l ∧ c.1.2 = k)) →
      ¬((c.1.1 = i ∨ c.1.1 = j ∨ c.1.1 = k ∨ c.1.1 = l) ∧
        (c.1.2 = i ∨ c.1.2 = j ∨ c.1.2 = k ∨ c.1.2 = l) ∧
        (c.1.1 = i ∨ c.1.1 = k ∨ c.1.2 = i ∨ c.1.2 = k)) →
      ¬(c.1.1 = i) → ¬(c.1.2 = i) → ¬(c.1.1 = k) → c.1.2 = k →
      ext H c = adj H l c.1.1 := by
    intro H c h1 h2 h3 h4 h5 h6 hc
    simp only [hext]
    rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_pos hc]
  have S8 : ∀ (H : HGraph n) (c : Edge n),
      ¬((c.1.1 = i ∧ c.1.2 = j) ∨ (c.1.1 = j ∧ c.1.2 = i)) →
      ¬((c.1.1 = k ∧ c.1.2 = l) ∨ (c.1.1 = l ∧ c.1.2 = k)) →
      ¬((c.1.1 = i ∨ c.1.1 = j ∨ c.1.1 = k ∨ c.1.1 = l) ∧
        (c.1.2 = i ∨ c.1.2 = j ∨ c.1.2 = k ∨ c.1.2 = l) ∧
        (c.1.1 = i ∨ c.1.1 = k ∨ c.1.2 = i ∨ c.1.2 = k)) →
      ¬(c.1.1 = i) → ¬(c.1.2 = i) → ¬(c.1.1 = k) → ¬(c.1.2 = k) →
      ext H c = H c := by
    intro H c h1 h2 h3 h4 h5 h6 h7
    simp only [hext]
    rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7]
  -- convenient derived shapes
  have S8' : ∀ (H : HGraph n) (c : Edge n), ¬(c.1.1 = i ∨ c.1.1 = k) →
      ¬(c.1.2 = i ∨ c.1.2 = k) → ext H c = H c := by
    intro H c hx hy
    refine S8 H c ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rintro (⟨u, _⟩ | ⟨_, u⟩)
      · exact hx (Or.inl u)
      · exact hy (Or.inl u)
    · rintro (⟨u, _⟩ | ⟨_, u⟩)
      · exact hx (Or.inr u)
      · exact hy (Or.inr u)
    · rintro ⟨_, _, u⟩
      rcases u with u | u | u | u
      · exact hx (Or.inl u)
      · exact hx (Or.inr u)
      · exact hy (Or.inl u)
      · exact hy (Or.inr u)
    · exact fun u => hx (Or.inl u)
    · exact fun u => hy (Or.inl u)
    · exact fun u => hx (Or.inr u)
    · exact fun u => hy (Or.inr u)
  have S4' : ∀ (H : HGraph n) (c : Edge n), c.1.1 = i →
      ¬(c.1.2 = i ∨ c.1.2 = j ∨ c.1.2 = k ∨ c.1.2 = l) → ext H c = adj H j c.1.2 := by
    intro H c hx hy
    refine S4 H c ?_ ?_ ?_ hx
    · rintro (⟨_, u⟩ | ⟨u, _⟩)
      · exact hy (Or.inr (Or.inl u))
      · exact hijne (hx.symm.trans u)
    · rintro (⟨u, _⟩ | ⟨u, _⟩)
      · exact hik (hx.symm.trans u)
      · exact hil (hx.symm.trans u)
    · rintro ⟨_, u, _⟩
      exact hy u
  have S5' : ∀ (H : HGraph n) (c : Edge n), c.1.2 = i →
      ¬(c.1.1 = i ∨ c.1.1 = j ∨ c.1.1 = k ∨ c.1.1 = l) → ext H c = adj H j c.1.1 := by
    intro H c hy hx
    refine S5 H c ?_ ?_ ?_ ?_ hy
    · rintro (⟨u, _⟩ | ⟨u, _⟩)
      · exact hx (Or.inl u)
      · exact hx (Or.inr (Or.inl u))
    · rintro (⟨u, _⟩ | ⟨u, _⟩)
      · exact hx (Or.inr (Or.inr (Or.inl u)))
      · exact hx (Or.inr (Or.inr (Or.inr u)))
    · rintro ⟨u, _, _⟩
      exact hx u
    · exact fun u => hx (Or.inl u)
  have S6' : ∀ (H : HGraph n) (c : Edge n), c.1.1 = k →
      ¬(c.1.2 = i ∨ c.1.2 = j ∨ c.1.2 = k ∨ c.1.2 = l) → ext H c = adj H l c.1.2 := by
    intro H c hx hy
    refine S6 H c ?_ ?_ ?_ ?_ ?_ hx
    · rintro (⟨u, _⟩ | ⟨u, _⟩)
      · exact hik (u.symm.trans hx)
      · exact hjk (u.symm.trans hx)
    · rintro (⟨_, u⟩ | ⟨u, _⟩)
      · exact hy (Or.inr (Or.inr (Or.inr u)))
      · exact hklne (hx.symm.trans u)
    · rintro ⟨_, u, _⟩
      exact hy u
    · exact fun u => hik (u.symm.trans hx)
    · exact fun u => hy (Or.inl u)
  have S7' : ∀ (H : HGraph n) (c : Edge n), c.1.2 = k →
      ¬(c.1.1 = i ∨ c.1.1 = j ∨ c.1.1 = k ∨ c.1.1 = l) → ext H c = adj H l c.1.1 := by
    intro H c hy hx
    refine S7 H c ?_ ?_ ?_ ?_ ?_ ?_ hy
    · rintro (⟨u, _⟩ | ⟨u, _⟩)
      · exact hx (Or.inl u)
      · exact hx (Or.inr (Or.inl u))
    · rintro (⟨u, _⟩ | ⟨u, _⟩)
      · exact hx (Or.inr (Or.inr (Or.inl u)))
      · exact hx (Or.inr (Or.inr (Or.inr u)))
    · rintro ⟨u, _, _⟩
      exact hx u
    · exact fun u => hx (Or.inl u)
    · exact fun u => hik (u.symm.trans hy)
    · exact fun u => hx (Or.inr (Or.inr (Or.inl u)))
  -- membership in the free set
  have hmemT : ∀ c : Edge n, ¬(c.1.1 = i ∨ c.1.1 = k) → ¬(c.1.2 = i ∨ c.1.2 = k) → c ∈ T := by
    intro c h1 h2
    rw [hTdef, mem_filter]
    refine ⟨mem_univ _, ?_⟩
    rintro ((u | u) | (u | u))
    · exact h1 (Or.inl u)
    · exact h2 (Or.inl u)
    · exact h1 (Or.inr u)
    · exact h2 (Or.inr u)
  have hedgeT : ∀ (x y : Fin n) (hxy : x ≠ y), ¬(x = i ∨ x = k) → ¬(y = i ∨ y = k) →
      edgeOf x y hxy ∈ T := by
    intro x y hxy hx hy
    refine hmemT _ ?_ ?_
    · rcases edgeOf_endpoints x y hxy with ⟨ha, _⟩ | ⟨ha, _⟩ <;> rw [ha]
      · exact hx
      · exact hy
    · rcases edgeOf_endpoints x y hxy with ⟨_, hb⟩ | ⟨_, hb⟩ <;> rw [hb]
      · exact hy
      · exact hx
  -- adjacency-level shapes
  have Bout : ∀ (H : HGraph n) (x y : Fin n) (hxy : x ≠ y), ¬(x = i ∨ x = k) →
      ¬(y = i ∨ y = k) → adj (ext H) x y = adj H x y := by
    intro H x y hxy hx hy
    rw [adj_eq_edgeOf (ext H) x y hxy, adj_eq_edgeOf H x y hxy]
    rcases edgeOf_endpoints x y hxy with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact S8' H _ (by rw [ha]; exact hx) (by rw [hb]; exact hy)
    · exact S8' H _ (by rw [ha]; exact hy) (by rw [hb]; exact hx)
  have Bi : ∀ (H : HGraph n) (x y : Fin n) (hxy : x ≠ y), x = i →
      ¬(y = i ∨ y = j ∨ y = k ∨ y = l) → adj (ext H) x y = adj H j y := by
    intro H x y hxy hx hy
    rw [adj_eq_edgeOf (ext H) x y hxy]
    rcases edgeOf_endpoints x y hxy with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [S4' H _ (by rw [ha]; exact hx) (by rw [hb]; exact hy), hb]
    · rw [S5' H _ (by rw [hb]; exact hx) (by rw [ha]; exact hy), ha]
  have Bk : ∀ (H : HGraph n) (x y : Fin n) (hxy : x ≠ y), x = k →
      ¬(y = i ∨ y = j ∨ y = k ∨ y = l) → adj (ext H) x y = adj H l y := by
    intro H x y hxy hx hy
    rw [adj_eq_edgeOf (ext H) x y hxy]
    rcases edgeOf_endpoints x y hxy with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [S6' H _ (by rw [ha]; exact hx) (by rw [hb]; exact hy), hb]
    · rw [S7' H _ (by rw [hb]; exact hx) (by rw [ha]; exact hy), ha]
  have B3 : ∀ (H : HGraph n) (x y : Fin n) (hxy : x ≠ y),
      (x = i ∨ x = j ∨ x = k ∨ x = l) → (y = i ∨ y = j ∨ y = k ∨ y = l) →
      ¬((x = i ∧ y = j) ∨ (x = j ∧ y = i)) →
      ¬((x = k ∧ y = l) ∨ (x = l ∧ y = k)) →
      (x = i ∨ x = k ∨ y = i ∨ y = k) → adj (ext H) x y = adj H j l := by
    intro H x y hxy hx hy hp1 hp2 hone
    rw [adj_eq_edgeOf (ext H) x y hxy]
    rcases edgeOf_endpoints x y hxy with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact S3 H _ (by rw [ha, hb]; exact hp1) (by rw [ha, hb]; exact hp2)
        ⟨by rw [ha]; exact hx, by rw [hb]; exact hy, by rw [ha, hb]; exact hone⟩
    · refine S3 H _ ?_ ?_ ⟨by rw [ha]; exact hy, by rw [hb]; exact hx, ?_⟩
      · rw [ha, hb]
        rintro (⟨u, v⟩ | ⟨u, v⟩)
        · exact hp1 (Or.inr ⟨v, u⟩)
        · exact hp1 (Or.inl ⟨v, u⟩)
      · rw [ha, hb]
        rintro (⟨u, v⟩ | ⟨u, v⟩)
        · exact hp2 (Or.inr ⟨v, u⟩)
        · exact hp2 (Or.inl ⟨v, u⟩)
      · rw [ha, hb]
        rcases hone with u | u | u | u
        · exact Or.inr (Or.inr (Or.inl u))
        · exact Or.inr (Or.inr (Or.inr u))
        · exact Or.inl u
        · exact Or.inr (Or.inl u)
  have Aij : ∀ H : HGraph n, adj (ext H) i j = true := by
    intro H
    rw [adj_eq_edgeOf (ext H) i j hijne]
    rcases edgeOf_endpoints i j hijne with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact S1 H _ (Or.inl ⟨ha, hb⟩)
    · exact S1 H _ (Or.inr ⟨ha, hb⟩)
  have Akl : ∀ H : HGraph n, adj (ext H) k l = true := by
    intro H
    rw [adj_eq_edgeOf (ext H) k l hklne]
    rcases edgeOf_endpoints k l hklne with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · refine S2 H _ ?_ (Or.inl ⟨ha, hb⟩)
      rintro (⟨u, _⟩ | ⟨u, _⟩)
      · exact hik (u.symm.trans ha)
      · exact hjk (u.symm.trans ha)
    · refine S2 H _ ?_ (Or.inr ⟨ha, hb⟩)
      rintro (⟨u, _⟩ | ⟨u, _⟩)
      · exact hil (u.symm.trans ha)
      · exact hjl (u.symm.trans ha)
  rw [← hTcard]
  refine card_filter_of_extension _ T ext ?_ ?_ ?_ ?_
  · intro H
    refine ⟨(trueTwins_edgeOf_iff (ext H) i j hijne).mpr ⟨Aij H, ?_⟩,
      (trueTwins_edgeOf_iff (ext H) k l hklne).mpr ⟨Akl H, ?_⟩⟩
    · intro p hpi hpj
      by_cases hpk : p = k
      · rw [hpk]
        rw [B3 H i k hik (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl)))
            (by rintro (⟨_, u⟩ | ⟨u, _⟩); exacts [hjk u.symm, hijne u])
            (by rintro (⟨u, _⟩ | ⟨u, _⟩); exacts [hik u, hil u]) (Or.inl rfl),
          B3 H j k hjk (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl)))
            (by rintro (⟨u, _⟩ | ⟨_, u⟩); exacts [hijne u.symm, hik u.symm])
            (by rintro (⟨u, _⟩ | ⟨u, _⟩); exacts [hjk u, hjl u])
            (Or.inr (Or.inr (Or.inr rfl)))]
      · by_cases hpl : p = l
        · rw [hpl]
          rw [B3 H i l hil (Or.inl rfl) (Or.inr (Or.inr (Or.inr rfl)))
              (by rintro (⟨_, u⟩ | ⟨u, _⟩); exacts [hjl u.symm, hijne u])
              (by rintro (⟨u, _⟩ | ⟨u, _⟩); exacts [hik u, hil u]) (Or.inl rfl),
            Bout H j l hjl hjik hlik]
        · have hq : ¬(p = i ∨ p = j ∨ p = k ∨ p = l) := by
            rintro (u | u | u | u)
            · exact hpi u
            · exact hpj u
            · exact hpk u
            · exact hpl u
          rw [Bi H i p (Ne.symm hpi) rfl hq,
            Bout H j p (Ne.symm hpj) hjik (by
              rintro (u | u)
              · exact hpi u
              · exact hpk u)]
    · intro p hpk hpl
      by_cases hpi : p = i
      · rw [hpi]
        rw [B3 H k i (Ne.symm hik) (Or.inr (Or.inr (Or.inl rfl))) (Or.inl rfl)
            (by rintro (⟨u, _⟩ | ⟨u, _⟩); exacts [hik u.symm, hjk u.symm])
            (by rintro (⟨_, u⟩ | ⟨_, u⟩); exacts [hil u, hik u])
            (Or.inr (Or.inl rfl)),
          B3 H l i (Ne.symm hil) (Or.inr (Or.inr (Or.inr rfl))) (Or.inl rfl)
            (by rintro (⟨u, _⟩ | ⟨u, _⟩); exacts [hil u.symm, hjl u.symm])
            (by rintro (⟨u, _⟩ | ⟨_, u⟩); exacts [hklne u.symm, hik u])
            (Or.inr (Or.inr (Or.inl rfl)))]
      · by_cases hpj : p = j
        · rw [hpj]
          rw [B3 H k j (Ne.symm hjk) (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inl rfl))
              (by rintro (⟨u, _⟩ | ⟨u, _⟩); exacts [hik u.symm, hjk u.symm])
              (by rintro (⟨_, u⟩ | ⟨u, _⟩); exacts [hjl u, hklne u])
              (Or.inr (Or.inl rfl)),
            Bout H l j (Ne.symm hjl) hlik hjik, adj_symm H l j]
        · have hq : ¬(p = i ∨ p = j ∨ p = k ∨ p = l) := by
            rintro (u | u | u | u)
            · exact hpi u
            · exact hpj u
            · exact hpk u
            · exact hpl u
          rw [Bk H k p (Ne.symm hpk) rfl hq,
            Bout H l p (Ne.symm hpl) hlik (by
              rintro (u | u)
              · exact hpi u
              · exact hpk u)]
  · intro H x hx
    rw [hTdef, mem_filter] at hx
    refine S8' H x ?_ ?_
    · rintro (u | u)
      · exact hx.2 (Or.inl (Or.inl u))
      · exact hx.2 (Or.inr (Or.inl u))
    · rintro (u | u)
      · exact hx.2 (Or.inl (Or.inr u))
      · exact hx.2 (Or.inr (Or.inr u))
  · rintro G ⟨ht1, ht2⟩
    obtain ⟨hGe, hGe2⟩ := (trueTwins_edgeOf_iff G i j hijne).mp ht1
    obtain ⟨hGf, hGf2⟩ := (trueTwins_edgeOf_iff G k l hklne).mp ht2
    have hikv : adj G i k = adj G j l := by
      rw [hGe2 k (Ne.symm hik) (Ne.symm hjk), adj_symm G j k, hGf2 j hjk hjl, adj_symm G l j]
    have hilv : adj G i l = adj G j l := hGe2 l (Ne.symm hil) (Ne.symm hjl)
    have hjkv : adj G j k = adj G j l := by
      rw [adj_symm G j k, hGf2 j hjk hjl, adj_symm G l j]
    have hkey : ∀ x y : Fin n, x ≠ y →
        (x = i ∨ x = j ∨ x = k ∨ x = l) → (y = i ∨ y = j ∨ y = k ∨ y = l) →
        ¬((x = i ∧ y = j) ∨ (x = j ∧ y = i)) →
        ¬((x = k ∧ y = l) ∨ (x = l ∧ y = k)) →
        (x = i ∨ x = k ∨ y = i ∨ y = k) → adj G x y = adj G j l := by
      intro x y hxy hx hy hp1 hp2 hone
      rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy
      · exact absurd (hx.trans hy.symm) hxy
      · exact absurd (Or.inl ⟨hx, hy⟩) hp1
      · rw [hx, hy]; exact hikv
      · rw [hx, hy]; exact hilv
      · exact absurd (Or.inr ⟨hx, hy⟩) hp1
      · exact absurd (hx.trans hy.symm) hxy
      · rw [hx, hy]; exact hjkv
      · exfalso
        rcases hone with u | u | u | u
        · exact hijne (hx.symm.trans u).symm
        · exact hjk (hx.symm.trans u)
        · exact hil (hy.symm.trans u).symm
        · exact hklne (hy.symm.trans u).symm
      · rw [hx, hy, adj_symm G k i]; exact hikv
      · rw [hx, hy, adj_symm G k j]; exact hjkv
      · exact absurd (hx.trans hy.symm) hxy
      · exact absurd (Or.inl ⟨hx, hy⟩) hp2
      · rw [hx, hy, adj_symm G l i]; exact hilv
      · exfalso
        rcases hone with u | u | u | u
        · exact hil (hx.symm.trans u).symm
        · exact hklne (hx.symm.trans u).symm
        · exact hijne (hy.symm.trans u).symm
        · exact hjk (hy.symm.trans u)
      · exact absurd (Or.inr ⟨hx, hy⟩) hp2
      · exact absurd (hx.trans hy.symm) hxy
    funext g
    by_cases c1 : (g.1.1 = i ∧ g.1.2 = j) ∨ (g.1.1 = j ∧ g.1.2 = i)
    · rw [S1 G g c1]
      symm
      rw [apply_eq_adj G g]
      rcases c1 with ⟨u, v⟩ | ⟨u, v⟩
      · rw [u, v]; exact hGe
      · rw [u, v, adj_symm G j i]; exact hGe
    · by_cases c2 : (g.1.1 = k ∧ g.1.2 = l) ∨ (g.1.1 = l ∧ g.1.2 = k)
      · rw [S2 G g c1 c2]
        symm
        rw [apply_eq_adj G g]
        rcases c2 with ⟨u, v⟩ | ⟨u, v⟩
        · rw [u, v]; exact hGf
        · rw [u, v, adj_symm G l k]; exact hGf
      · by_cases c3 : (g.1.1 = i ∨ g.1.1 = j ∨ g.1.1 = k ∨ g.1.1 = l) ∧
            (g.1.2 = i ∨ g.1.2 = j ∨ g.1.2 = k ∨ g.1.2 = l) ∧
            (g.1.1 = i ∨ g.1.1 = k ∨ g.1.2 = i ∨ g.1.2 = k)
        · rw [S3 G g c1 c2 c3, apply_eq_adj G g]
          exact (hkey g.1.1 g.1.2 (ne_of_lt g.2) c3.1 c3.2.1 c1 c2 c3.2.2).symm
        · by_cases c4 : g.1.1 = i
          · have hq : ¬(g.1.2 = i ∨ g.1.2 = j ∨ g.1.2 = k ∨ g.1.2 = l) :=
              fun hq => c3 ⟨Or.inl c4, hq, Or.inl c4⟩
            rw [S4 G g c1 c2 c3 c4, apply_eq_adj G g, c4]
            exact (hGe2 g.1.2 (fun u => hq (Or.inl u)) (fun u => hq (Or.inr (Or.inl u)))).symm
          · by_cases c5 : g.1.2 = i
            · have hq : ¬(g.1.1 = i ∨ g.1.1 = j ∨ g.1.1 = k ∨ g.1.1 = l) :=
                fun hq => c3 ⟨hq, Or.inl c5, Or.inr (Or.inr (Or.inl c5))⟩
              rw [S5 G g c1 c2 c3 c4 c5, apply_eq_adj G g, c5, adj_symm G g.1.1 i]
              exact (hGe2 g.1.1 (fun u => hq (Or.inl u)) (fun u => hq (Or.inr (Or.inl u)))).symm
            · by_cases c6 : g.1.1 = k
              · have hq : ¬(g.1.2 = i ∨ g.1.2 = j ∨ g.1.2 = k ∨ g.1.2 = l) :=
                  fun hq => c3 ⟨Or.inr (Or.inr (Or.inl c6)), hq, Or.inr (Or.inl c6)⟩
                rw [S6 G g c1 c2 c3 c4 c5 c6, apply_eq_adj G g, c6]
                exact (hGf2 g.1.2 (fun u => hq (Or.inr (Or.inr (Or.inl u))))
                  (fun u => hq (Or.inr (Or.inr (Or.inr u))))).symm
              · by_cases c7 : g.1.2 = k
                · have hq : ¬(g.1.1 = i ∨ g.1.1 = j ∨ g.1.1 = k ∨ g.1.1 = l) :=
                    fun hq => c3 ⟨hq, Or.inr (Or.inr (Or.inl c7)),
                      Or.inr (Or.inr (Or.inr c7))⟩
                  rw [S7 G g c1 c2 c3 c4 c5 c6 c7, apply_eq_adj G g, c7,
                    adj_symm G g.1.1 k]
                  exact (hGf2 g.1.1 (fun u => hq (Or.inr (Or.inr (Or.inl u))))
                    (fun u => hq (Or.inr (Or.inr (Or.inr u))))).symm
                · rw [S8 G g c1 c2 c3 c4 c5 c6 c7]
  · intro H H' hHH'
    funext g
    by_cases c1 : (g.1.1 = i ∧ g.1.2 = j) ∨ (g.1.1 = j ∧ g.1.2 = i)
    · rw [S1 H g c1, S1 H' g c1]
    · by_cases c2 : (g.1.1 = k ∧ g.1.2 = l) ∨ (g.1.1 = l ∧ g.1.2 = k)
      · rw [S2 H g c1 c2, S2 H' g c1 c2]
      · by_cases c3 : (g.1.1 = i ∨ g.1.1 = j ∨ g.1.1 = k ∨ g.1.1 = l) ∧
            (g.1.2 = i ∨ g.1.2 = j ∨ g.1.2 = k ∨ g.1.2 = l) ∧
            (g.1.1 = i ∨ g.1.1 = k ∨ g.1.2 = i ∨ g.1.2 = k)
        · rw [S3 H g c1 c2 c3, S3 H' g c1 c2 c3, adj_eq_edgeOf H j l hjl,
            adj_eq_edgeOf H' j l hjl]
          exact hHH' _ (hedgeT j l hjl hjik hlik)
        · by_cases c4 : g.1.1 = i
          · have hq : ¬(g.1.2 = i ∨ g.1.2 = j ∨ g.1.2 = k ∨ g.1.2 = l) :=
              fun hq => c3 ⟨Or.inl c4, hq, Or.inl c4⟩
            have hne : j ≠ g.1.2 := fun u => hq (Or.inr (Or.inl u.symm))
            rw [S4 H g c1 c2 c3 c4, S4 H' g c1 c2 c3 c4, adj_eq_edgeOf H j g.1.2 hne,
              adj_eq_edgeOf H' j g.1.2 hne]
            exact hHH' _ (hedgeT j g.1.2 hne hjik (by
              rintro (u | u)
              · exact hq (Or.inl u)
              · exact hq (Or.inr (Or.inr (Or.inl u)))))
          · by_cases c5 : g.1.2 = i
            · have hq : ¬(g.1.1 = i ∨ g.1.1 = j ∨ g.1.1 = k ∨ g.1.1 = l) :=
                fun hq => c3 ⟨hq, Or.inl c5, Or.inr (Or.inr (Or.inl c5))⟩
              have hne : j ≠ g.1.1 := fun u => hq (Or.inr (Or.inl u.symm))
              rw [S5 H g c1 c2 c3 c4 c5, S5 H' g c1 c2 c3 c4 c5,
                adj_eq_edgeOf H j g.1.1 hne, adj_eq_edgeOf H' j g.1.1 hne]
              exact hHH' _ (hedgeT j g.1.1 hne hjik (by
                rintro (u | u)
                · exact hq (Or.inl u)
                · exact hq (Or.inr (Or.inr (Or.inl u)))))
            · by_cases c6 : g.1.1 = k
              · have hq : ¬(g.1.2 = i ∨ g.1.2 = j ∨ g.1.2 = k ∨ g.1.2 = l) :=
                  fun hq => c3 ⟨Or.inr (Or.inr (Or.inl c6)), hq, Or.inr (Or.inl c6)⟩
                have hne : l ≠ g.1.2 := fun u => hq (Or.inr (Or.inr (Or.inr u.symm)))
                rw [S6 H g c1 c2 c3 c4 c5 c6, S6 H' g c1 c2 c3 c4 c5 c6,
                  adj_eq_edgeOf H l g.1.2 hne, adj_eq_edgeOf H' l g.1.2 hne]
                exact hHH' _ (hedgeT l g.1.2 hne hlik (by
                  rintro (u | u)
                  · exact hq (Or.inl u)
                  · exact hq (Or.inr (Or.inr (Or.inl u)))))
              · by_cases c7 : g.1.2 = k
                · have hq : ¬(g.1.1 = i ∨ g.1.1 = j ∨ g.1.1 = k ∨ g.1.1 = l) :=
                    fun hq => c3 ⟨hq, Or.inr (Or.inr (Or.inl c7)),
                      Or.inr (Or.inr (Or.inr c7))⟩
                  have hne : l ≠ g.1.1 := fun u => hq (Or.inr (Or.inr (Or.inr u.symm)))
                  rw [S7 H g c1 c2 c3 c4 c5 c6 c7, S7 H' g c1 c2 c3 c4 c5 c6 c7,
                    adj_eq_edgeOf H l g.1.1 hne, adj_eq_edgeOf H' l g.1.1 hne]
                  exact hHH' _ (hedgeT l g.1.1 hne hlik (by
                    rintro (u | u)
                    · exact hq (Or.inl u)
                    · exact hq (Or.inr (Or.inr (Or.inl u)))))
                · rw [S8 H g c1 c2 c3 c4 c5 c6 c7, S8 H' g c1 c2 c3 c4 c5 c6 c7]
                  refine hHH' g (hmemT g ?_ ?_)
                  · rintro (u | u)
                    · exact c4 u
                    · exact c6 u
                  · rintro (u | u)
                    · exact c5 u
                    · exact c7 u

/-- Exact count, disjoint intersection: e = {i,j}, f = {k,l} with
    `{i,j} ∩ {k,l} = ∅`. -/
theorem twin_count_disjoint (n : ℕ) (i j k l : Fin n)
    (hij : i < j) (hkl : k < l)
    (h : ({i, j} : Finset (Fin n)) ∩ {k, l} = ∅) :
    (Finset.univ.filter (fun G : HGraph n =>
        TrueTwins G ⟨(i, j), hij⟩ ∧ TrueTwins G ⟨(k, l), hkl⟩)).card
      = 2 ^ (Fintype.card (Edge n) - (2 * n - 3)) := by
  have hdisj : ∀ x : Fin n, (x = i ∨ x = j) → (x = k ∨ x = l) → False := by
    intro x h1 h2
    have hx : x ∈ ({i, j} : Finset (Fin n)) ∩ {k, l} := by
      refine Finset.mem_inter.mpr ⟨?_, ?_⟩
      · rcases h1 with h1 | h1 <;> simp [h1]
      · rcases h2 with h2 | h2 <;> simp [h2]
    rw [h] at hx
    simp at hx
  rw [← edgeOf_fst_lt (ne_of_lt hij) hij, ← edgeOf_fst_lt (ne_of_lt hkl) hkl]
  exact twin_count_disjoint_gen n i j k l (ne_of_lt hij)
    (fun hc => hdisj i (Or.inl rfl) (Or.inl hc))
    (fun hc => hdisj i (Or.inl rfl) (Or.inr hc))
    (fun hc => hdisj j (Or.inr rfl) (Or.inl hc))
    (fun hc => hdisj j (Or.inr rfl) (Or.inr hc)) (ne_of_lt hkl)

/-- Rewriting the two edges of a twin-pair count. -/
private theorem card_twin_pair_congr {n : ℕ} (p q p' q' : Edge n) (h1 : p = p') (h2 : q = q') :
    (Finset.univ.filter (fun G : HGraph n => TrueTwins G p ∧ TrueTwins G q)).card
      = (Finset.univ.filter (fun G : HGraph n => TrueTwins G p' ∧ TrueTwins G q')).card := by
  subst h1; subst h2; rfl

/-- Any two distinct edges — sharing a vertex or not — have the same twin-pair
    count `2 ^ (m − (2n − 3))`. -/
theorem twin_count_pair (n : ℕ) (e f : Edge n) (hef : e ≠ f) :
    (Finset.univ.filter (fun G : HGraph n => TrueTwins G e ∧ TrueTwins G f)).card
      = 2 ^ (Fintype.card (Edge n) - (2 * n - 3)) := by
  classical
  have haux : ∀ (a b c d : Fin n) (hab : a ≠ b) (hcd : c ≠ d),
      edgeOf a b hab ≠ edgeOf c d hcd →
      (Finset.univ.filter (fun G : HGraph n =>
          TrueTwins G (edgeOf a b hab) ∧ TrueTwins G (edgeOf c d hcd))).card
        = 2 ^ (Fintype.card (Edge n) - (2 * n - 3)) := by
    intro a b c d hab hcd hne
    by_cases h1 : a = c
    · have had : a ≠ d := by rw [h1]; exact hcd
      have hbd : b ≠ d := fun hc => hne (edgeOf_congr hab hcd h1 hc)
      rw [card_twin_pair_congr (edgeOf a b hab) (edgeOf c d hcd) (edgeOf a b hab)
        (edgeOf a d had) rfl (edgeOf_congr had hcd h1 rfl).symm]
      exact twin_count_shared_gen n a b d hab had hbd
    · by_cases h2 : a = d
      · have hac : a ≠ c := h1
        have hbc : b ≠ c := fun hc => hne (edgeOf_congr_swap hab hcd h2 hc)
        rw [card_twin_pair_congr (edgeOf a b hab) (edgeOf c d hcd) (edgeOf a b hab)
          (edgeOf a c hac) rfl (edgeOf_congr_swap hac hcd h2 rfl).symm]
        exact twin_count_shared_gen n a b c hab hac hbc
      · by_cases h3 : b = c
        · have hbd : b ≠ d := by rw [h3]; exact hcd
          rw [card_twin_pair_congr (edgeOf a b hab) (edgeOf c d hcd)
            (edgeOf b a (Ne.symm hab)) (edgeOf b d hbd) (edgeOf_comm a b hab)
            (edgeOf_congr hbd hcd h3 rfl).symm]
          exact twin_count_shared_gen n b a d (Ne.symm hab) hbd h2
        · by_cases h4 : b = d
          · rw [card_twin_pair_congr (edgeOf a b hab) (edgeOf c d hcd)
              (edgeOf b a (Ne.symm hab)) (edgeOf b c h3) (edgeOf_comm a b hab)
              (edgeOf_congr_swap h3 hcd h4 rfl).symm]
            exact twin_count_shared_gen n b a c (Ne.symm hab) h3 h1
          · exact twin_count_disjoint_gen n a b c d hab h1 h2 h3 h4 hcd
  rw [card_twin_pair_congr e f (edgeOf e.1.1 e.1.2 (ne_of_lt e.2))
    (edgeOf f.1.1 f.1.2 (ne_of_lt f.2)) (edgeOf_eta e).symm (edgeOf_eta f).symm]
  exact haux _ _ _ _ _ _ (by rw [edgeOf_eta, edgeOf_eta]; exact hef)

/-- thm:twinbound, counting form (Bonferroni).  With m = #Edge n:
    #{G : some twin pair} ≥ C(n,2)·2^{m−(n−1)} − C(C(n,2),2)·2^{m−(2n−3)}. -/
theorem twin_bound (n : ℕ) (hn : 4 ≤ n) :
    (Finset.univ.filter (fun G : HGraph n => ∃ e, TrueTwins G e)).card
      ≥ Fintype.card (Edge n) * 2 ^ (Fintype.card (Edge n) - (n - 1))
        - (Fintype.card (Edge n)).choose 2 * 2 ^ (Fintype.card (Edge n) - (2 * n - 3)) := by
  classical
  set A : Edge n → Finset (HGraph n) :=
    fun e => Finset.univ.filter (fun G : HGraph n => TrueTwins G e) with hA
  have hbi : (Finset.univ : Finset (Edge n)).biUnion A
      = Finset.univ.filter (fun G : HGraph n => ∃ e, TrueTwins G e) := by
    ext G
    simp [hA]
  have hpair : ∀ e ∈ (Finset.univ : Finset (Edge n)), ∀ f ∈ (Finset.univ : Finset (Edge n)),
      e ≠ f → (A e ∩ A f).card ≤ 2 ^ (Fintype.card (Edge n) - (2 * n - 3)) := by
    intro e _ f _ hef
    have hEq : A e ∩ A f
        = Finset.univ.filter (fun G : HGraph n => TrueTwins G e ∧ TrueTwins G f) := by
      ext G
      simp [hA]
    rw [hEq, twin_count_pair n e f hef]
  have hsum : ∑ e : Edge n, (A e).card
      = Fintype.card (Edge n) * 2 ^ (Fintype.card (Edge n) - (n - 1)) := by
    have hone : ∀ e : Edge n, (A e).card = 2 ^ (Fintype.card (Edge n) - (n - 1)) :=
      fun e => twin_count_single n e (by omega)
    rw [Finset.sum_congr rfl (fun e _ => hone e), Finset.sum_const, Finset.card_univ,
      smul_eq_mul]
  have hB := sum_card_le_card_biUnion_add (Finset.univ : Finset (Edge n)) A
    (2 ^ (Fintype.card (Edge n) - (2 * n - 3))) hpair
  rw [hsum, hbi, Finset.card_univ] at hB
  omega

end HalfOne
