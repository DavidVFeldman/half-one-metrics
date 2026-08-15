/-
  Round6.lean — Tier B statements for the Round 6 commission.

  The three counting bounds behind thm:density, stated as EXACT integer
  cardinality inequalities over the finite set of graphs (no probability, no
  division, no reals), plus the deterministic links that connect each event to
  the hypotheses of `density_implication`, and the assembled union bound.

  Conventions as in `HalfOne.Defs`.  m abbreviates `Fintype.card (Edge n)`
  throughout; the paper's probabilities are these cardinalities over 2^m.

  Sanity anchors, verified by exhaustive enumeration during drafting:
    · a fixed 4-set spans an induced claw for exactly 4 of the 2^6 assignments
      of its internal bits;
    · at n = 4:  16^1 · #{no claw} = 960 = 15^1 · 2^6   (equality: n/4 uses one block);
    · at n = 5:  16^1 · #{no claw} = 12304 ≤ 15360 = 15^1 · 2^10.
-/

import HalfOne.Density
import HalfOne.Blocks

namespace HalfOne

open Finset

/- Several of the events counted below (`Good`, `VConn`, …) quantify over
    walk lengths and are not decidable by unification; the classical instance
    is used, at priority 0, so that the genuinely decidable events keep their
    computable instances. -/
attribute [local instance 0] Classical.propDecidable

variable {n : ℕ}

/-! ### Edge bookkeeping used by the block decompositions -/

/-- Two `edgeOf`s agree exactly when their endpoint pairs agree. -/
theorem edgeOf_eq_iff {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) :
    edgeOf a b hab = edgeOf c d hcd ↔ ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) := by
  constructor
  · intro h
    have e1 : (edgeOf a b hab).1.1 = (edgeOf c d hcd).1.1 := by rw [h]
    have e2 : (edgeOf a b hab).1.2 = (edgeOf c d hcd).1.2 := by rw [h]
    rcases edgeOf_endpoints a b hab with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases edgeOf_endpoints c d hcd with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
        rw [h1, h3] at e1 <;> rw [h2, h4] at e2 <;> tauto
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact edgeOf_comm a b hab

/-! ### B1  The claw bound -/

/-- Decidable claw predicate (same content as `Claw`). -/
def ClawB (G : HGraph n) : Bool :=
  decide (∃ i j k l : Fin n, [i,j,k,l].Nodup ∧
    adj G i j = true ∧ adj G i k = true ∧ adj G i l = true ∧
    adj G j k = false ∧ adj G j l = false ∧ adj G k l = false)

theorem clawB_iff (G : HGraph n) : ClawB G = true ↔ Claw G := by
  rw [ClawB, decide_eq_true_iff]
  rfl

/-- The claw event localized to the block `{4t, 4t+1, 4t+2, 4t+3}`: an induced
    claw all four of whose vertices lie in block `t`. -/
def ClawIn (G : HGraph n) (t : ℕ) : Prop :=
  ∃ i j k l : Fin n, i.val / 4 = t ∧ j.val / 4 = t ∧ k.val / 4 = t ∧ l.val / 4 = t ∧
    [i,j,k,l].Nodup ∧
    adj G i j = true ∧ adj G i k = true ∧ adj G i l = true ∧
    adj G j k = false ∧ adj G j l = false ∧ adj G k l = false

instance (G : HGraph n) (t : ℕ) : Decidable (ClawIn G t) := by
  unfold ClawIn; infer_instance

/-- Block `t` spans no induced claw. -/
def clawFreeB (G : HGraph n) (t : ℕ) : Bool := !(decide (ClawIn G t))

/-- The internal coordinates of block `t`. -/
def blockE (n t : ℕ) : Finset (Edge n) :=
  univ.filter (fun e => e.1.1.val / 4 = t ∧ e.1.2.val / 4 = t)

theorem mem_blockE {t : ℕ} {e : Edge n} :
    e ∈ blockE n t ↔ (e.1.1.val / 4 = t ∧ e.1.2.val / 4 = t) := by
  simp [blockE]

theorem blockE_disjoint (s t : ℕ) (hst : s ≠ t) : Disjoint (blockE n s) (blockE n t) := by
  rw [Finset.disjoint_left]
  intro e h1 h2
  rw [mem_blockE] at h1 h2
  exact hst (h1.1.symm.trans h2.1)

/-- `clawFreeB · t` depends only on the coordinates of block `t`. -/
theorem clawFreeB_local (t : ℕ) (G H : HGraph n) (h : ∀ x ∈ blockE n t, G x = H x) :
    clawFreeB G t = clawFreeB H t := by
  have hadj : ∀ (G H : HGraph n), (∀ x ∈ blockE n t, G x = H x) →
      ∀ x y : Fin n, x.val / 4 = t → y.val / 4 = t → x ≠ y → adj G x y = adj H x y := by
    intro G H h x y hx hy hxy
    rw [adj_eq_edgeOf G x y hxy, adj_eq_edgeOf H x y hxy]
    refine h _ ?_
    rw [mem_blockE]
    rcases edgeOf_endpoints x y hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;>
      exact ⟨by assumption, by assumption⟩
  have main : ∀ (G H : HGraph n), (∀ x ∈ blockE n t, G x = H x) → ClawIn G t → ClawIn H t := by
    rintro G H hGH ⟨i, j, k, l, hi, hj, hk, hl, hnd, e1, e2, e3, e4, e5, e6⟩
    have hnd' := hnd
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, and_true,
      not_or, not_false_iff] at hnd'
    obtain ⟨⟨hij, hik, hil⟩, ⟨hjk, hjl⟩, hkl⟩ := hnd'
    refine ⟨i, j, k, l, hi, hj, hk, hl, hnd, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← hadj G H hGH i j hi hj hij]; exact e1
    · rw [← hadj G H hGH i k hi hk hik]; exact e2
    · rw [← hadj G H hGH i l hi hl hil]; exact e3
    · rw [← hadj G H hGH j k hj hk hjk]; exact e4
    · rw [← hadj G H hGH j l hj hl hjl]; exact e5
    · rw [← hadj G H hGH k l hk hl hkl]; exact e6
  have hiff : ClawIn G t ↔ ClawIn H t :=
    ⟨main G H h, main H G (fun x hx => (h x hx).symm)⟩
  unfold clawFreeB
  congr 1
  exact decide_eq_decide.mpr hiff

/-- A full block has exactly six internal coordinates. -/
theorem card_blockE (n t : ℕ) (ht : 4 * t + 3 < n) : (blockE n t).card = 6 := by
  classical
  set a : Fin n := ⟨4*t, by omega⟩ with ha
  set b : Fin n := ⟨4*t+1, by omega⟩ with hb
  set c : Fin n := ⟨4*t+2, by omega⟩ with hc
  set d : Fin n := ⟨4*t+3, by omega⟩ with hd
  have hab : a ≠ b := by simp [ha, hb, Fin.ext_iff]
  have hac : a ≠ c := by simp [ha, hc, Fin.ext_iff]
  have had : a ≠ d := by simp [ha, hd, Fin.ext_iff]
  have hbc : b ≠ c := by simp [hb, hc, Fin.ext_iff]
  have hbd : b ≠ d := by simp [hb, hd, Fin.ext_iff]
  have hcd : c ≠ d := by simp [hc, hd, Fin.ext_iff]
  have hset : blockE n t = ({edgeOf a b hab, edgeOf a c hac, edgeOf a d had,
      edgeOf b c hbc, edgeOf b d hbd, edgeOf c d hcd} : Finset (Edge n)) := by
    have key : ∀ (x y : Fin n) (hxy : x ≠ y) (e : Edge n),
        e.1.1 = x → e.1.2 = y → e = edgeOf x y hxy :=
      fun x y hxy e h1 h2 => edge_eq_of_mem hxy (Or.inl h1) (Or.inr h2)
    have hgen : ∀ (x y : Fin n) (hxy : x ≠ y), x.val / 4 = t → y.val / 4 = t →
        edgeOf x y hxy ∈ blockE n t := by
      intro x y hxy hx hy
      rw [mem_blockE]
      rcases edgeOf_endpoints x y hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;>
        exact ⟨by omega, by omega⟩
    ext e
    constructor
    · intro he
      rw [mem_blockE] at he
      obtain ⟨h1, h2⟩ := he
      have hlt : e.1.1.val < e.1.2.val := e.2
      have hu : e.1.1.val = 4*t ∨ e.1.1.val = 4*t+1 ∨ e.1.1.val = 4*t+2 ∨ e.1.1.val = 4*t+3 := by
        omega
      have hv : e.1.2.val = 4*t ∨ e.1.2.val = 4*t+1 ∨ e.1.2.val = 4*t+2 ∨ e.1.2.val = 4*t+3 := by
        omega
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases hu with hu | hu | hu | hu <;> rcases hv with hv | hv | hv | hv <;>
        first
          | (exfalso; omega)
          | exact Or.inl (key _ _ _ _ (Fin.ext hu) (Fin.ext hv))
          | exact Or.inr (Or.inl (key _ _ _ _ (Fin.ext hu) (Fin.ext hv)))
          | exact Or.inr (Or.inr (Or.inl (key _ _ _ _ (Fin.ext hu) (Fin.ext hv))))
          | exact Or.inr (Or.inr (Or.inr (Or.inl (key _ _ _ _ (Fin.ext hu) (Fin.ext hv)))))
          | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (key _ _ _ _ (Fin.ext hu) (Fin.ext hv))))))
          | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (key _ _ _ _ (Fin.ext hu) (Fin.ext hv))))))
    · intro he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hgen _ _ _ (by simp only [ha, hb, hc, Fin.val_mk]; omega)
          (by simp only [hb, hc, hd, Fin.val_mk]; omega)
  rw [hset]
  simp [Finset.card_insert_of_notMem, Finset.mem_insert, edgeOf_eq_iff, ha, hb, hc, hd, Fin.ext_iff]

/-- The star at `a` inside `{a,b,c,d}`: the three edges at `a` are half-length,
    everything else is unital. -/
def starG (a b c d : Fin n) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) : HGraph n :=
  fun e => decide (e = edgeOf a b hab ∨ e = edgeOf a c hac ∨ e = edgeOf a d had)

theorem starG_apply (a b c d : Fin n) (h1 : a ≠ b) (h2 : a ≠ c) (h3 : a ≠ d) (e : Edge n) :
    starG a b c d h1 h2 h3 e = true ↔
      (e = edgeOf a b h1 ∨ e = edgeOf a c h2 ∨ e = edgeOf a d h3) := by
  rw [starG, decide_eq_true_iff]

theorem starG_adj_spoke1 (a b c d : Fin n) (h1 : a ≠ b) (h2 : a ≠ c) (h3 : a ≠ d) :
    adj (starG a b c d h1 h2 h3) a b = true := by
  rw [adj_eq_edgeOf _ a b h1, starG_apply]
  exact Or.inl rfl

theorem starG_adj_spoke2 (a b c d : Fin n) (h1 : a ≠ b) (h2 : a ≠ c) (h3 : a ≠ d) :
    adj (starG a b c d h1 h2 h3) a c = true := by
  rw [adj_eq_edgeOf _ a c h2, starG_apply]
  exact Or.inr (Or.inl rfl)

theorem starG_adj_spoke3 (a b c d : Fin n) (h1 : a ≠ b) (h2 : a ≠ c) (h3 : a ≠ d) :
    adj (starG a b c d h1 h2 h3) a d = true := by
  rw [adj_eq_edgeOf _ a d h3, starG_apply]
  exact Or.inr (Or.inr rfl)

/-- Every half-length edge of the star passes through its centre. -/
theorem starG_adj_off (a b c d x y : Fin n) (h1 : a ≠ b) (h2 : a ≠ c) (h3 : a ≠ d)
    (hxy : x ≠ y) (hx : x ≠ a) (hy : y ≠ a) :
    adj (starG a b c d h1 h2 h3) x y = false := by
  rw [adj_eq_edgeOf _ x y hxy]
  rcases Bool.eq_false_or_eq_true (starG a b c d h1 h2 h3 (edgeOf x y hxy)) with h | h
  · exfalso
    rw [starG_apply] at h
    rcases h with h | h | h <;> rw [edgeOf_eq_iff] at h <;> rcases h with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact hx e1
    · exact hy e2
    · exact hx e1
    · exact hy e2
    · exact hx e1
    · exact hy e2
  · exact h

theorem starG_supported (a b c d : Fin n) (h1 : a ≠ b) (h2 : a ≠ c) (h3 : a ≠ d)
    (T : Finset (Edge n)) (hb : edgeOf a b h1 ∈ T) (hc : edgeOf a c h2 ∈ T)
    (hd : edgeOf a d h3 ∈ T) :
    ∀ x ∉ T, starG a b c d h1 h2 h3 x = false := by
  intro x hx
  rcases Bool.eq_false_or_eq_true (starG a b c d h1 h2 h3 x) with h | h
  · exfalso
    rw [starG_apply] at h
    rcases h with rfl | rfl | rfl
    · exact hx hb
    · exact hx hc
    · exact hx hd
  · exact h

theorem clawIn_starG (t : ℕ) (a b c d : Fin n) (h1 : a ≠ b) (h2 : a ≠ c) (h3 : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ha : a.val / 4 = t) (hb : b.val / 4 = t) (hc : c.val / 4 = t) (hd : d.val / 4 = t) :
    ClawIn (starG a b c d h1 h2 h3) t := by
  refine ⟨a, b, c, d, ha, hb, hc, hd, ?_, starG_adj_spoke1 a b c d h1 h2 h3,
    starG_adj_spoke2 a b c d h1 h2 h3, starG_adj_spoke3 a b c d h1 h2 h3,
    starG_adj_off a b c d b c h1 h2 h3 hbc (Ne.symm h1) (Ne.symm h2),
    starG_adj_off a b c d b d h1 h2 h3 hbd (Ne.symm h1) (Ne.symm h3),
    starG_adj_off a b c d c d h1 h2 h3 hcd (Ne.symm h2) (Ne.symm h3)⟩
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, and_true,
    not_or]
  exact ⟨⟨h1, h2, h3, not_false⟩, ⟨hbc, hbd, not_false⟩, ⟨hcd, not_false⟩, not_false⟩

theorem hgraph_ne_of_adj {F H : HGraph n} {x y : Fin n}
    (h1 : adj F x y = true) (h2 : adj H x y = false) : F ≠ H := by
  intro hFH
  rw [hFH, h2] at h1
  exact Bool.noConfusion h1

/-- The per-block density: at most 60 of the 64 internal assignments of a full
    block avoid an induced claw inside the block. -/
theorem block_claw_density (n t : ℕ) (ht : 4 * t + 3 < n) :
    64 * (univ.filter (fun G : HGraph n => clawFreeB G t = true)).card
      ≤ 60 * 2 ^ (Fintype.card (Edge n)) := by
  classical
  set a : Fin n := ⟨4*t, by omega⟩ with ha
  set b : Fin n := ⟨4*t+1, by omega⟩ with hb
  set c : Fin n := ⟨4*t+2, by omega⟩ with hc
  set d : Fin n := ⟨4*t+3, by omega⟩ with hd
  have hab : a ≠ b := by simp [ha, hb, Fin.ext_iff]
  have hac : a ≠ c := by simp [ha, hc, Fin.ext_iff]
  have had : a ≠ d := by simp [ha, hd, Fin.ext_iff]
  have hbc : b ≠ c := by simp [hb, hc, Fin.ext_iff]
  have hbd : b ≠ d := by simp [hb, hd, Fin.ext_iff]
  have hcd : c ≠ d := by simp [hc, hd, Fin.ext_iff]
  have hva : a.val / 4 = t := by simp only [ha, Fin.val_mk]; omega
  have hvb : b.val / 4 = t := by simp only [hb, Fin.val_mk]; omega
  have hvc : c.val / 4 = t := by simp only [hc, Fin.val_mk]; omega
  have hvd : d.val / 4 = t := by simp only [hd, Fin.val_mk]; omega
  have hmemE : ∀ (x y : Fin n) (hxy : x ≠ y), x.val / 4 = t → y.val / 4 = t →
      edgeOf x y hxy ∈ blockE n t := by
    intro x y hxy hx hy
    rw [mem_blockE]
    rcases edgeOf_endpoints x y hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;>
      exact ⟨by assumption, by assumption⟩
  have hbad : ∀ F : HGraph n, ClawIn F t → clawFreeB F t = false := by
    intro F h
    simp only [clawFreeB, decide_eq_true h, Bool.not_true]
  -- the four stars of the block
  have hne_ab : starG a b c d hab hac had ≠ starG b a c d (Ne.symm hab) hbc hbd :=
    hgraph_ne_of_adj (starG_adj_spoke2 a b c d hab hac had)
      (starG_adj_off b a c d a c (Ne.symm hab) hbc hbd hac hab (Ne.symm hbc))
  have hne_ac : starG a b c d hab hac had ≠ starG c a b d (Ne.symm hac) (Ne.symm hbc) hcd :=
    hgraph_ne_of_adj (starG_adj_spoke1 a b c d hab hac had)
      (starG_adj_off c a b d a b (Ne.symm hac) (Ne.symm hbc) hcd hab hac hbc)
  have hne_ad : starG a b c d hab hac had ≠ starG d a b c (Ne.symm had) (Ne.symm hbd) (Ne.symm hcd) :=
    hgraph_ne_of_adj (starG_adj_spoke1 a b c d hab hac had)
      (starG_adj_off d a b c a b (Ne.symm had) (Ne.symm hbd) (Ne.symm hcd) hab had hbd)
  have hne_bc : starG b a c d (Ne.symm hab) hbc hbd ≠ starG c a b d (Ne.symm hac) (Ne.symm hbc) hcd :=
    hgraph_ne_of_adj (starG_adj_spoke1 b a c d (Ne.symm hab) hbc hbd)
      (starG_adj_off c a b d b a (Ne.symm hac) (Ne.symm hbc) hcd (Ne.symm hab) hbc hac)
  have hne_bd : starG b a c d (Ne.symm hab) hbc hbd ≠ starG d a b c (Ne.symm had) (Ne.symm hbd) (Ne.symm hcd) :=
    hgraph_ne_of_adj (starG_adj_spoke1 b a c d (Ne.symm hab) hbc hbd)
      (starG_adj_off d a b c b a (Ne.symm had) (Ne.symm hbd) (Ne.symm hcd) (Ne.symm hab) hbd had)
  have hne_cd : starG c a b d (Ne.symm hac) (Ne.symm hbc) hcd ≠ starG d a b c (Ne.symm had) (Ne.symm hbd) (Ne.symm hcd) :=
    hgraph_ne_of_adj (starG_adj_spoke1 c a b d (Ne.symm hac) (Ne.symm hbc) hcd)
      (starG_adj_off d a b c c a (Ne.symm had) (Ne.symm hbd) (Ne.symm hcd) (Ne.symm hac) hcd had)
  have hin : ({starG a b c d hab hac had, starG b a c d (Ne.symm hab) hbc hbd,
      starG c a b d (Ne.symm hac) (Ne.symm hbc) hcd,
      starG d a b c (Ne.symm had) (Ne.symm hbd) (Ne.symm hcd)} : Finset (HGraph n)) ⊆
      univ.filter (fun G : HGraph n =>
        clawFreeB G t = false ∧ ∀ x ∉ blockE n t, G x = false) := by
    intro F hF
    simp only [Finset.mem_insert, Finset.mem_singleton] at hF
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hF with rfl | rfl | rfl | rfl
    · exact ⟨hbad _ (clawIn_starG t a b c d hab hac had hbc hbd hcd hva hvb hvc hvd),
        starG_supported a b c d hab hac had (blockE n t) (hmemE a b hab hva hvb)
          (hmemE a c hac hva hvc) (hmemE a d had hva hvd)⟩
    · exact ⟨hbad _ (clawIn_starG t b a c d (Ne.symm hab) hbc hbd hac had hcd hvb hva hvc hvd),
        starG_supported b a c d (Ne.symm hab) hbc hbd (blockE n t)
          (hmemE b a (Ne.symm hab) hvb hva) (hmemE b c hbc hvb hvc) (hmemE b d hbd hvb hvd)⟩
    · exact ⟨hbad _ (clawIn_starG t c a b d (Ne.symm hac) (Ne.symm hbc) hcd hab had hbd
          hvc hva hvb hvd),
        starG_supported c a b d (Ne.symm hac) (Ne.symm hbc) hcd (blockE n t)
          (hmemE c a (Ne.symm hac) hvc hva) (hmemE c b (Ne.symm hbc) hvc hvb)
          (hmemE c d hcd hvc hvd)⟩
    · exact ⟨hbad _ (clawIn_starG t d a b c (Ne.symm had) (Ne.symm hbd) (Ne.symm hcd)
          hab hac hbc hvd hva hvb hvc),
        starG_supported d a b c (Ne.symm had) (Ne.symm hbd) (Ne.symm hcd) (blockE n t)
          (hmemE d a (Ne.symm had) hvd hva) (hmemE d b (Ne.symm hbd) hvd hvb)
          (hmemE d c (Ne.symm hcd) hvd hvc)⟩
  have hcard4 : ({starG a b c d hab hac had, starG b a c d (Ne.symm hab) hbc hbd,
      starG c a b d (Ne.symm hac) (Ne.symm hbc) hcd,
      starG d a b c (Ne.symm had) (Ne.symm hbd) (Ne.symm hcd)} : Finset (HGraph n)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hne_ab, hne_ac, hne_ad]),
      Finset.card_insert_of_notMem (by simp [hne_bc, hne_bd]),
      Finset.card_insert_of_notMem (by simp [hne_cd]), Finset.card_singleton]
  have hd4 : 4 ≤ (univ.filter (fun G : HGraph n =>
      clawFreeB G t = false ∧ ∀ x ∉ blockE n t, G x = false)).card := by
    rw [← hcard4]
    exact Finset.card_le_card hin
  have hbb := local_bound (blockE n t) (fun G => clawFreeB G t)
    (fun G H hGH => clawFreeB_local t G H hGH) 4 hd4
  rw [card_blockE n t ht] at hbb
  norm_num at hbb
  exact hbb

/-- B1.  Graphs with no induced claw are exponentially rare:
    16^⌊n/4⌋ · #{G : ¬Claw G} ≤ 15^⌊n/4⌋ · 2^m. -/
theorem claw_bound (n : ℕ) :
    16 ^ (n / 4) * (univ.filter (fun G : HGraph n => ¬ Claw G)).card
      ≤ 15 ^ (n / 4) * 2 ^ (Fintype.card (Edge n)) := by
  have hbb := block_bound (Finset.range (n / 4)) (blockE n)
    (fun t (G : HGraph n) => clawFreeB G t)
    (fun s _ t _ hst => blockE_disjoint s t hst)
    (fun t _ G H h => clawFreeB_local t G H h) 64 60
    (fun t ht => block_claw_density n t (by
      rw [Finset.mem_range] at ht
      have h4 : n / 4 * 4 ≤ n := Nat.div_mul_le_self n 4
      omega))
  rw [Finset.card_range] at hbb
  dsimp only at hbb
  have hsub : univ.filter (fun G : HGraph n => ¬ Claw G) ⊆
      univ.filter (fun G : HGraph n => ∀ t ∈ Finset.range (n / 4), clawFreeB G t = true) := by
    intro G hG
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hG ⊢
    intro t _
    have hno : ¬ ClawIn G t := by
      rintro ⟨i, j, k, l, -, -, -, -, hnd, e1, e2, e3, e4, e5, e6⟩
      exact hG ⟨i, j, k, l, hnd, e1, e2, e3, e4, e5, e6⟩
    rw [clawFreeB, decide_eq_false hno, Bool.not_false]
  have h1 : 64 ^ (n / 4) * (univ.filter (fun G : HGraph n => ¬ Claw G)).card
      ≤ 60 ^ (n / 4) * 2 ^ (Fintype.card (Edge n)) := by
    refine le_trans (Nat.mul_le_mul_left _ (Finset.card_le_card hsub)) ?_
    convert hbb using 3
    ext G
    simp only [Finset.mem_filter]
  have e64 : (64 : ℕ) ^ (n / 4) = 4 ^ (n / 4) * 16 ^ (n / 4) := by
    rw [← Nat.mul_pow]
  have e60 : (60 : ℕ) ^ (n / 4) = 4 ^ (n / 4) * 15 ^ (n / 4) := by
    rw [← Nat.mul_pow]
  rw [e64, e60, mul_assoc, mul_assoc] at h1
  exact Nat.le_of_mul_le_mul_left h1 (pow_pos (by norm_num) _)

/-! ### B2  The mending bound -/

/-- `l` is a mending witness for the ordered spoke pair `(i; j, k)`:
    `{i,l}` half-length, `{j,l}` unital, `{k,l}` unital. -/
def MendWitness (G : HGraph n) (i j k l : Fin n) : Prop :=
  adj G i l = true ∧ adj G j l = false ∧ adj G k l = false

/-- Deterministic link: a witness makes the two spokes Γ-co-component
    (two Γ-steps through `{i,l}`), and hence witnesses everywhere give
    `MendedAt` everywhere. -/
theorem mendedAt_of_witnesses (G : HGraph n)
    (h : ∀ i j k : Fin n, i ≠ j → i ≠ k → j ≠ k →
      adj G i j = true → adj G i k = true →
      ∃ l : Fin n, l ≠ i ∧ l ≠ j ∧ l ≠ k ∧ MendWitness G i j k l) :
    ∀ i, MendedAt G i := by
  intro i e f he hf hei hfi
  -- name the far endpoints of `e` and `f`
  obtain ⟨j, hj, hej⟩ : ∃ (j : Fin n) (hj : i ≠ j), e = edgeOf i j hj := by
    rcases hei with hei | hei
    · have hj : i ≠ e.1.2 := by rw [← hei]; exact ne_of_lt e.2
      exact ⟨e.1.2, hj, edge_eq_of_mem hj (Or.inl hei) (Or.inr rfl)⟩
    · have hj : i ≠ e.1.1 := by rw [← hei]; exact (ne_of_lt e.2).symm
      exact ⟨e.1.1, hj, edge_eq_of_mem hj (Or.inr rfl) (Or.inl hei)⟩
  obtain ⟨k, hk, hfk⟩ : ∃ (k : Fin n) (hk : i ≠ k), f = edgeOf i k hk := by
    rcases hfi with hfi | hfi
    · have hk : i ≠ f.1.2 := by rw [← hfi]; exact ne_of_lt f.2
      exact ⟨f.1.2, hk, edge_eq_of_mem hk (Or.inl hfi) (Or.inr rfl)⟩
    · have hk : i ≠ f.1.1 := by rw [← hfi]; exact (ne_of_lt f.2).symm
      exact ⟨f.1.1, hk, edge_eq_of_mem hk (Or.inr rfl) (Or.inl hfi)⟩
  subst hej; subst hfk
  by_cases hjk : j = k
  · subst hjk; exact GReach.refl G _
  have hij : adj G i j = true := by rw [adj_eq_edgeOf G i j hj]; exact he
  have hik : adj G i k = true := by rw [adj_eq_edgeOf G i k hk]; exact hf
  obtain ⟨l, hli, hlj, hlk, hwil, hwjl, hwkl⟩ := h i j k hj hk hjk hij hik
  have hil : i ≠ l := (Ne.symm hli)
  have h1 : gammaAdj G (edgeOf i j hj) (edgeOf i l hil) = true :=
    gammaAdj_of_shared G i j l hj hil (Ne.symm hlj) hij hwil hwjl
  have h2 : gammaAdj G (edgeOf i l hil) (edgeOf i k hk) = true := by
    refine gammaAdj_of_shared G i l k hil hk hlk hwil hik ?_
    rw [adj_symm]; exact hwkl
  exact ⟨2, GWalk.cons h1 (GWalk.cons h2 (GWalk.nil _))⟩

/-- The three coordinates dedicated to the witness candidate `l` for the spoke
    pair `(i; j, k)`. -/
def witnessE (i j k l : Fin n) (hli : l ≠ i) (hlj : l ≠ j) (hlk : l ≠ k) : Finset (Edge n) :=
  {edgeOf i l (Ne.symm hli), edgeOf j l (Ne.symm hlj), edgeOf k l (Ne.symm hlk)}

/-- The single-edge graph. -/
def singleG (e : Edge n) : HGraph n := fun f => decide (f = e)

theorem singleG_apply (e f : Edge n) : singleG e f = true ↔ f = e := by
  rw [singleG, decide_eq_true_iff]

theorem singleG_adj_self (x y : Fin n) (h : x ≠ y) :
    adj (singleG (edgeOf x y h)) x y = true := by
  rw [adj_eq_edgeOf _ x y h, singleG_apply]

theorem singleG_adj_ne (e : Edge n) (x y : Fin n) (hxy : x ≠ y) (h : edgeOf x y hxy ≠ e) :
    adj (singleG e) x y = false := by
  rw [adj_eq_edgeOf _ x y hxy]
  rcases Bool.eq_false_or_eq_true (singleG e (edgeOf x y hxy)) with h' | h'
  · exact absurd ((singleG_apply e _).mp h') h
  · exact h'

instance decidableMendWitness (G : HGraph n) (i j k l : Fin n) :
    Decidable (MendWitness G i j k l) := by
  unfold MendWitness; infer_instance

/-- `l` fails to be a mending witness for the spoke pair `(i; j, k)`. -/
def witFreeB (G : HGraph n) (i j k l : Fin n) : Bool := !(decide (MendWitness G i j k l))

theorem mem_witnessE_fst (i j k l : Fin n) (hli : l ≠ i) (hlj : l ≠ j) (hlk : l ≠ k) :
    edgeOf i l (Ne.symm hli) ∈ witnessE i j k l hli hlj hlk := by
  simp [witnessE]

theorem witFreeB_local (i j k l : Fin n) (hli : l ≠ i) (hlj : l ≠ j) (hlk : l ≠ k)
    (G H : HGraph n) (h : ∀ x ∈ witnessE i j k l hli hlj hlk, G x = H x) :
    witFreeB G i j k l = witFreeB H i j k l := by
  have e1 : adj G i l = adj H i l := by
    rw [adj_eq_edgeOf G i l (Ne.symm hli), adj_eq_edgeOf H i l (Ne.symm hli)]
    exact h _ (by simp [witnessE])
  have e2 : adj G j l = adj H j l := by
    rw [adj_eq_edgeOf G j l (Ne.symm hlj), adj_eq_edgeOf H j l (Ne.symm hlj)]
    exact h _ (by simp [witnessE])
  have e3 : adj G k l = adj H k l := by
    rw [adj_eq_edgeOf G k l (Ne.symm hlk), adj_eq_edgeOf H k l (Ne.symm hlk)]
    exact h _ (by simp [witnessE])
  have hiff : MendWitness G i j k l ↔ MendWitness H i j k l := by
    rw [MendWitness, MendWitness, e1, e2, e3]
  unfold witFreeB
  congr 1
  exact decide_eq_decide.mpr hiff

theorem card_witnessE (i j k l : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hli : l ≠ i) (hlj : l ≠ j) (hlk : l ≠ k) :
    (witnessE i j k l hli hlj hlk).card = 3 := by
  have hne1 : edgeOf i l (Ne.symm hli) ≠ edgeOf j l (Ne.symm hlj) := by
    rw [Ne, edgeOf_eq_iff]
    rintro (⟨h1, -⟩ | ⟨h1, -⟩)
    · exact hij h1
    · exact hli h1.symm
  have hne2 : edgeOf i l (Ne.symm hli) ≠ edgeOf k l (Ne.symm hlk) := by
    rw [Ne, edgeOf_eq_iff]
    rintro (⟨h1, -⟩ | ⟨h1, -⟩)
    · exact hik h1
    · exact hli h1.symm
  have hne3 : edgeOf j l (Ne.symm hlj) ≠ edgeOf k l (Ne.symm hlk) := by
    rw [Ne, edgeOf_eq_iff]
    rintro (⟨h1, -⟩ | ⟨h1, -⟩)
    · exact hjk h1
    · exact hlj h1.symm
  rw [witnessE, Finset.card_insert_of_notMem (by simp [hne1, hne2]),
    Finset.card_insert_of_notMem (by simp [hne3]), Finset.card_singleton]

/-- The per-`l` density: exactly one of the eight assignments of the three
    coordinates `{i,l}, {j,l}, {k,l}` makes `l` a witness. -/
theorem witFree_density (n : ℕ) (i j k l : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hli : l ≠ i) (hlj : l ≠ j) (hlk : l ≠ k) :
    8 * (univ.filter (fun G : HGraph n => witFreeB G i j k l = true)).card
      ≤ 7 * 2 ^ (Fintype.card (Edge n)) := by
  have hW : MendWitness (singleG (edgeOf i l (Ne.symm hli))) i j k l := by
    refine ⟨singleG_adj_self i l (Ne.symm hli), ?_, ?_⟩
    · refine singleG_adj_ne _ j l (Ne.symm hlj) ?_
      rw [Ne, edgeOf_eq_iff]
      rintro (⟨h1, -⟩ | ⟨h1, -⟩)
      · exact hij h1.symm
      · exact hlj h1.symm
    · refine singleG_adj_ne _ k l (Ne.symm hlk) ?_
      rw [Ne, edgeOf_eq_iff]
      rintro (⟨h1, -⟩ | ⟨h1, -⟩)
      · exact hik h1.symm
      · exact hlk h1.symm
  have hbad : 1 ≤ (univ.filter (fun G : HGraph n =>
      witFreeB G i j k l = false ∧ ∀ x ∉ witnessE i j k l hli hlj hlk, G x = false)).card := by
    have hsub : ({singleG (edgeOf i l (Ne.symm hli))} : Finset (HGraph n)) ⊆
        univ.filter (fun G : HGraph n =>
          witFreeB G i j k l = false ∧ ∀ x ∉ witnessE i j k l hli hlj hlk, G x = false) := by
      intro F hF
      simp only [Finset.mem_singleton] at hF
      subst hF
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨by simp only [witFreeB, decide_eq_true hW, Bool.not_true], ?_⟩
      intro x hx
      rcases Bool.eq_false_or_eq_true (singleG (edgeOf i l (Ne.symm hli)) x) with h | h
      · exact absurd ((singleG_apply _ _).mp h ▸ mem_witnessE_fst i j k l hli hlj hlk) hx
      · exact h
    have := Finset.card_le_card hsub
    simpa using this
  have hbb := local_bound (witnessE i j k l hli hlj hlk) (fun G => witFreeB G i j k l)
    (fun G H hGH => witFreeB_local i j k l hli hlj hlk G H hGH) 1 hbad
  rw [card_witnessE i j k l hij hik hjk hli hlj hlk] at hbb
  norm_num at hbb
  exact hbb

theorem witnessE_disjoint (i j k s t : Fin n) (hsi : s ≠ i) (hsj : s ≠ j) (hsk : s ≠ k)
    (hti : t ≠ i) (htj : t ≠ j) (htk : t ≠ k) (hst : s ≠ t) :
    Disjoint (witnessE i j k s hsi hsj hsk) (witnessE i j k t hti htj htk) := by
  rw [Finset.disjoint_left]
  intro e he he'
  simp only [witnessE, Finset.mem_insert, Finset.mem_singleton] at he he'
  rcases he with rfl | rfl | rfl <;> rcases he' with h | h | h <;>
    rw [edgeOf_eq_iff] at h <;> rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      first
        | exact hst h2
        | exact hsi h2
        | exact hsj h2
        | exact hsk h2

/-- B2, single-triple count: for FIXED distinct `i, j, k`, the graphs with no
    mending witness for `(i; j, k)` number at most (7/8)^(n−3) of all. -/
theorem mend_bound_triple (n : ℕ) (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    8 ^ (n - 3) * (univ.filter (fun G : HGraph n =>
        ¬ ∃ l : Fin n, l ≠ i ∧ l ≠ j ∧ l ≠ k ∧ MendWitness G i j k l)).card
      ≤ 7 ^ (n - 3) * 2 ^ (Fintype.card (Edge n)) := by
  have hmemI : ∀ l : Fin n, l ∈ (univ \ ({i, j, k} : Finset (Fin n))) ↔
      (l ≠ i ∧ l ≠ j ∧ l ≠ k) := by
    intro l
    simp [not_or]
  have hbb := block_bound (univ \ ({i, j, k} : Finset (Fin n)))
    (fun l => if h : l ≠ i ∧ l ≠ j ∧ l ≠ k then witnessE i j k l h.1 h.2.1 h.2.2 else ∅)
    (fun l (G : HGraph n) => witFreeB G i j k l)
    (fun s hs t ht hst => by
      obtain ⟨hsi, hsj, hsk⟩ := (hmemI s).mp hs
      obtain ⟨hti, htj, htk⟩ := (hmemI t).mp ht
      dsimp only
      rw [dif_pos ⟨hsi, hsj, hsk⟩, dif_pos ⟨hti, htj, htk⟩]
      exact witnessE_disjoint i j k s t hsi hsj hsk hti htj htk hst)
    (fun l hl G H hGH => by
      obtain ⟨hli, hlj, hlk⟩ := (hmemI l).mp hl
      refine witFreeB_local i j k l hli hlj hlk G H ?_
      intro x hx
      refine hGH x ?_
      dsimp only
      rw [dif_pos ⟨hli, hlj, hlk⟩]
      exact hx)
    8 7
    (fun l hl => by
      obtain ⟨hli, hlj, hlk⟩ := (hmemI l).mp hl
      exact witFree_density n i j k l hij hik hjk hli hlj hlk)
  have hcardI : (univ \ ({i, j, k} : Finset (Fin n))).card = n - 3 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    congr 1
    rw [Finset.card_insert_of_notMem (by simp [hij, hik]),
      Finset.card_insert_of_notMem (by simp [hjk]), Finset.card_singleton]
  rw [hcardI] at hbb
  dsimp only at hbb
  have hsub : (univ.filter (fun G : HGraph n =>
      ¬ ∃ l : Fin n, l ≠ i ∧ l ≠ j ∧ l ≠ k ∧ MendWitness G i j k l)) ⊆
      univ.filter (fun G : HGraph n =>
        ∀ l ∈ (univ \ ({i, j, k} : Finset (Fin n))), witFreeB G i j k l = true) := by
    intro G hG
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hG ⊢
    intro l hl
    obtain ⟨hli, hlj, hlk⟩ := (hmemI l).mp hl
    have hno : ¬ MendWitness G i j k l := fun hw => hG ⟨l, hli, hlj, hlk, hw⟩
    rw [witFreeB, decide_eq_false hno, Bool.not_false]
  refine le_trans (Nat.mul_le_mul_left _ (Finset.card_le_card hsub)) ?_
  convert hbb using 3
  ext G
  simp only [Finset.mem_filter]

/-- B2, union over triples: at most n³ · (7/8)^(n−3) · 2^m graphs have SOME
    unwitnessed triple. -/
theorem mend_bound (n : ℕ) :
    8 ^ (n - 3) * (univ.filter (fun G : HGraph n =>
        ¬ ∀ i j k : Fin n, i ≠ j → i ≠ k → j ≠ k →
          adj G i j = true → adj G i k = true →
          ∃ l : Fin n, l ≠ i ∧ l ≠ j ∧ l ≠ k ∧ MendWitness G i j k l)).card
      ≤ n ^ 3 * 7 ^ (n - 3) * 2 ^ (Fintype.card (Edge n)) := by
  classical
  set D : Finset (Fin n × Fin n × Fin n) :=
    univ.filter (fun p => p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2) with hD
  set F : (Fin n × Fin n × Fin n) → Finset (HGraph n) := fun p =>
    univ.filter (fun G : HGraph n =>
      ¬ ∃ l : Fin n, l ≠ p.1 ∧ l ≠ p.2.1 ∧ l ≠ p.2.2 ∧ MendWitness G p.1 p.2.1 p.2.2 l) with hF
  have hsub : (univ.filter (fun G : HGraph n =>
      ¬ ∀ i j k : Fin n, i ≠ j → i ≠ k → j ≠ k →
        adj G i j = true → adj G i k = true →
        ∃ l : Fin n, l ≠ i ∧ l ≠ j ∧ l ≠ k ∧ MendWitness G i j k l)) ⊆ D.biUnion F := by
    intro G hG
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hG
    push_neg at hG
    obtain ⟨i, j, k, hij, hik, hjk, -, -, hno⟩ := hG
    rw [Finset.mem_biUnion]
    refine ⟨(i, j, k), ?_, ?_⟩
    · simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hij, hik, hjk⟩
    · simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and]
      push_neg
      exact hno
  have hcardD : D.card ≤ n ^ 3 := by
    have h1 : D.card ≤ Fintype.card (Fin n × Fin n × Fin n) := Finset.card_le_univ D
    simp only [Fintype.card_prod, Fintype.card_fin] at h1
    calc D.card ≤ n * (n * n) := h1
    _ = n ^ 3 := by ring
  calc 8 ^ (n - 3) * (univ.filter (fun G : HGraph n =>
        ¬ ∀ i j k : Fin n, i ≠ j → i ≠ k → j ≠ k →
          adj G i j = true → adj G i k = true →
          ∃ l : Fin n, l ≠ i ∧ l ≠ j ∧ l ≠ k ∧ MendWitness G i j k l)).card
      ≤ 8 ^ (n - 3) * (D.biUnion F).card :=
        Nat.mul_le_mul_left _ (Finset.card_le_card hsub)
    _ ≤ 8 ^ (n - 3) * ∑ p ∈ D, (F p).card :=
        Nat.mul_le_mul_left _ Finset.card_biUnion_le
    _ = ∑ p ∈ D, 8 ^ (n - 3) * (F p).card := by rw [Finset.mul_sum]
    _ ≤ ∑ p ∈ D, 7 ^ (n - 3) * 2 ^ (Fintype.card (Edge n)) := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        exact mend_bound_triple n p.1 p.2.1 p.2.2 hp.1 hp.2.1 hp.2.2
    _ = D.card * (7 ^ (n - 3) * 2 ^ (Fintype.card (Edge n))) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ n ^ 3 * (7 ^ (n - 3) * 2 ^ (Fintype.card (Edge n))) :=
        Nat.mul_le_mul_right _ hcardD
    _ = n ^ 3 * 7 ^ (n - 3) * 2 ^ (Fintype.card (Edge n)) := by ring

/-! ### B3  The connectivity bound -/

/-- Vertex connectivity of the half-length graph. -/
def VConn (G : HGraph n) : Prop :=
  ∀ i j : Fin n,
    Relation.ReflTransGen (fun a b : Fin n => adj G a b = true) i j

/-- Deterministic link: vertex connectivity implies edge connectivity `GConn`.
    (The minimum-degree hypothesis `hmin` is part of the commissioned
    statement; the proof does not need it — a vertex path between the
    endpoints of two half-length edges already lifts to an edge walk.) -/
theorem gconn_of_vconn (G : HGraph n) (h : VConn G)
    (hmin : ∀ i : Fin n, ∃ j, adj G i j = true) : GConn G := by
  set R : Edge n → Edge n → Prop := fun a b => G a = true ∧ G b = true ∧ a ≠ b ∧
    (a.1.1 = b.1.1 ∨ a.1.1 = b.1.2 ∨ a.1.2 = b.1.1 ∨ a.1.2 = b.1.2) with hR
  -- two half-length edges through a common vertex are one `R`-step apart
  have share : ∀ (g g' : Edge n) (v : Fin n), G g = true → G g' = true →
      (g.1.1 = v ∨ g.1.2 = v) → (g'.1.1 = v ∨ g'.1.2 = v) →
      Relation.ReflTransGen R g g' := by
    intro g g' v hg hg' hgv hg'v
    by_cases hgg : g = g'
    · subst hgg; exact Relation.ReflTransGen.refl
    refine Relation.ReflTransGen.single ⟨hg, hg', hgg, ?_⟩
    rcases hgv with hgv | hgv <;> rcases hg'v with hg'v | hg'v
    · exact Or.inl (hgv.trans hg'v.symm)
    · exact Or.inr (Or.inl (hgv.trans hg'v.symm))
    · exact Or.inr (Or.inr (Or.inl (hgv.trans hg'v.symm)))
    · exact Or.inr (Or.inr (Or.inr (hgv.trans hg'v.symm)))
  -- a vertex path lifts to an `R`-walk
  have key : ∀ u v : Fin n, Relation.ReflTransGen (fun a b : Fin n => adj G a b = true) u v →
      ∀ e : Edge n, G e = true → (e.1.1 = u ∨ e.1.2 = u) →
      ∃ g : Edge n, G g = true ∧ (g.1.1 = v ∨ g.1.2 = v) ∧ Relation.ReflTransGen R e g := by
    intro u v hp
    induction hp with
    | refl => intro e he heu; exact ⟨e, he, heu, Relation.ReflTransGen.refl⟩
    | @tail b c hub hbc ih =>
        intro e he heu
        obtain ⟨g, hg, hgb, hwalk⟩ := ih e he heu
        have hbcne : b ≠ c := by
          intro hcon; subst hcon; rw [adj_irrefl] at hbc; exact Bool.noConfusion hbc
        have hg' : G (edgeOf b c hbcne) = true := by
          rw [← adj_eq_edgeOf G b c hbcne]; exact hbc
        have hb : (edgeOf b c hbcne).1.1 = b ∨ (edgeOf b c hbcne).1.2 = b := by
          rcases edgeOf_endpoints b c hbcne with ⟨h1, -⟩ | ⟨-, h2⟩
          · exact Or.inl h1
          · exact Or.inr h2
        have hc : (edgeOf b c hbcne).1.1 = c ∨ (edgeOf b c hbcne).1.2 = c := by
          rcases edgeOf_endpoints b c hbcne with ⟨-, h2⟩ | ⟨h1, -⟩
          · exact Or.inr h2
          · exact Or.inl h1
        exact ⟨edgeOf b c hbcne, hg', hc,
          hwalk.trans (share g (edgeOf b c hbcne) b hg hg' hgb hb)⟩
  intro e f he hf
  obtain ⟨g, hg, hgf, hwalk⟩ := key e.1.1 f.1.1 (h e.1.1 f.1.1) e he (Or.inl rfl)
  exact hwalk.trans (share g f f.1.1 hg hf hgf (Or.inl rfl))

/-- The coordinates crossing the cut `S`. -/
def crossE (S : Finset (Fin n)) : Finset (Edge n) :=
  univ.filter (fun e => (e.1.1 ∈ S ∧ e.1.2 ∉ S) ∨ (e.1.1 ∉ S ∧ e.1.2 ∈ S))

theorem card_crossE (S : Finset (Fin n)) :
    (crossE S).card = S.card * (n - S.card) := by
  classical
  have hc : (Sᶜ).card = n - S.card := by
    rw [Finset.card_compl]; simp
  rw [← hc, ← Finset.card_product]
  refine Finset.card_bij
    (fun e _ => if e.1.1 ∈ S then (e.1.1, e.1.2) else (e.1.2, e.1.1)) ?_ ?_ ?_
  · intro e he
    rw [crossE, Finset.mem_filter] at he
    rcases he.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp [h1, Finset.mem_product, h2]
    · simp [h1, Finset.mem_product, h2]
  · intro e he f hf hef
    dsimp only at hef
    rw [crossE, Finset.mem_filter] at he hf
    rcases he.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hf.2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · rw [if_pos h1, if_pos h3, Prod.mk.injEq] at hef
      exact edge_ext hef.1 hef.2
    · rw [if_pos h1, if_neg h3, Prod.mk.injEq] at hef
      exfalso
      have h5 : e.1.1 < e.1.2 := e.2
      rw [hef.1, hef.2] at h5
      exact absurd h5 (not_lt.mpr (le_of_lt f.2))
    · rw [if_neg h1, if_pos h3, Prod.mk.injEq] at hef
      exfalso
      have h5 : e.1.1 < e.1.2 := e.2
      rw [hef.1, hef.2] at h5
      exact absurd h5 (not_lt.mpr (le_of_lt f.2))
    · rw [if_neg h1, if_neg h3, Prod.mk.injEq] at hef
      exact edge_ext hef.2 hef.1
  · rintro ⟨a, b⟩ hab
    rw [Finset.mem_product] at hab
    obtain ⟨ha, hb⟩ := hab
    simp only [Finset.mem_compl] at hb
    have hne : a ≠ b := by rintro rfl; exact hb ha
    refine ⟨edgeOf a b hne, ?_, ?_⟩
    · rw [crossE, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases edgeOf_endpoints a b hne with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by rw [h1]; exact ha, by rw [h2]; exact hb⟩
      · exact Or.inr ⟨by rw [h1]; exact hb, by rw [h2]; exact ha⟩
    · rcases edgeOf_endpoints a b hne with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hcond : (edgeOf a b hne).1.1 ∈ S := by rw [h1]; exact ha
        simp only [if_pos hcond]
        rw [h1, h2]
      · have hcond : (edgeOf a b hne).1.1 ∉ S := by rw [h1]; exact hb
        simp only [if_neg hcond]
        rw [h1, h2]

/-- The graphs with no half-length edge across the cut `S`. -/
theorem card_noCross (S : Finset (Fin n)) :
    (univ.filter (fun G : HGraph n => ∀ e ∈ crossE S, G e = false)).card
      = 2 ^ (Fintype.card (Edge n) - S.card * (n - S.card)) := by
  classical
  have h1 : (univ.filter (fun G : HGraph n => ∀ e ∈ crossE S, G e = false))
      = univ.filter (fun G : HGraph n => ∀ x ∉ (crossE S)ᶜ, G x = false) := by
    apply Finset.filter_congr
    intro G _
    simp
  rw [h1, card_supported, Finset.card_compl, card_crossE]

/-- A disconnected graph has a cut of size between `1` and `n/2` with no
    half-length edge across it. -/
theorem exists_cut_of_not_vconn (G : HGraph n) (hG : ¬ VConn G) :
    ∃ S : Finset (Fin n), 1 ≤ S.card ∧ S.card ≤ n / 2 ∧ ∀ e ∈ crossE S, G e = false := by
  classical
  rw [VConn] at hG
  push_neg at hG
  obtain ⟨i, j, hij⟩ := hG
  set Reach : Fin n → Prop := fun b =>
    Relation.ReflTransGen (fun a b : Fin n => adj G a b = true) i b with hReach
  set S₀ : Finset (Fin n) := univ.filter (fun b => Reach b) with hS₀
  have hiS : i ∈ S₀ := by
    simp only [hS₀, hReach, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Relation.ReflTransGen.refl
  have hjS : j ∉ S₀ := by
    simp only [hS₀, hReach, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hij
  have hclosed : ∀ u v : Fin n, u ∈ S₀ → v ∉ S₀ → adj G u v = false := by
    intro u v hu hv
    by_contra hcon
    rw [Bool.not_eq_false] at hcon
    apply hv
    simp only [hS₀, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    exact Relation.ReflTransGen.tail hu hcon
  have hnocross : ∀ (S : Finset (Fin n)), (∀ u v : Fin n, u ∈ S → v ∉ S → adj G u v = false) →
      ∀ e ∈ crossE S, G e = false := by
    intro S hS e he
    rw [crossE, Finset.mem_filter] at he
    rw [apply_eq_adj G e]
    rcases he.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hS _ _ h1 h2
    · rw [adj_symm]; exact hS _ _ h2 h1
  have hScard : 1 ≤ S₀.card := Finset.card_pos.mpr ⟨i, hiS⟩
  have hScard' : S₀.card ≤ n - 1 := by
    have : S₀ ⊆ univ.erase j := by
      intro x hx
      exact Finset.mem_erase.mpr ⟨by rintro rfl; exact hjS hx, Finset.mem_univ x⟩
    have h2 := Finset.card_le_card this
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin] at h2
    exact h2
  by_cases hhalf : S₀.card ≤ n / 2
  · exact ⟨S₀, hScard, hhalf, hnocross S₀ hclosed⟩
  · refine ⟨S₀ᶜ, ?_, ?_, hnocross _ ?_⟩
    · rw [Finset.card_compl, Fintype.card_fin]
      omega
    · rw [Finset.card_compl, Fintype.card_fin]
      omega
    · intro u v hu hv
      rw [Finset.mem_compl] at hu
      rw [Finset.mem_compl, not_not] at hv
      rw [adj_symm]
      exact hclosed v u hv hu

/-- B3: cut counting.  (`hn : 1 ≤ n` is part of the commissioned statement and
    is kept; the proof does not use it — for `n = 0` the left-hand side is `0`.) -/
theorem conn_bound (n : ℕ) (hn : 1 ≤ n) :
    (univ.filter (fun G : HGraph n => ¬ VConn G)).card
      ≤ ∑ k ∈ Finset.Icc 1 (n / 2),
          (n.choose k) * 2 ^ (Fintype.card (Edge n) - k * (n - k)) := by
  classical
  have hsub : univ.filter (fun G : HGraph n => ¬ VConn G) ⊆
      (Finset.Icc 1 (n / 2)).biUnion (fun k =>
        (Finset.powersetCard k (univ : Finset (Fin n))).biUnion (fun S =>
          univ.filter (fun G : HGraph n => ∀ e ∈ crossE S, G e = false))) := by
    intro G hG
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hG
    obtain ⟨S, h1, h2, h3⟩ := exists_cut_of_not_vconn G hG
    simp only [Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_powersetCard,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨S.card, ⟨h1, h2⟩, S, ⟨Finset.subset_univ S, rfl⟩, h3⟩
  calc (univ.filter (fun G : HGraph n => ¬ VConn G)).card
      ≤ ((Finset.Icc 1 (n / 2)).biUnion (fun k =>
          (Finset.powersetCard k (univ : Finset (Fin n))).biUnion (fun S =>
            univ.filter (fun G : HGraph n => ∀ e ∈ crossE S, G e = false)))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ k ∈ Finset.Icc 1 (n / 2),
          ((Finset.powersetCard k (univ : Finset (Fin n))).biUnion (fun S =>
            univ.filter (fun G : HGraph n => ∀ e ∈ crossE S, G e = false))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ k ∈ Finset.Icc 1 (n / 2), ∑ S ∈ Finset.powersetCard k (univ : Finset (Fin n)),
          (univ.filter (fun G : HGraph n => ∀ e ∈ crossE S, G e = false)).card :=
        Finset.sum_le_sum (fun k _ => Finset.card_biUnion_le)
    _ = ∑ k ∈ Finset.Icc 1 (n / 2), (n.choose k) *
          2 ^ (Fintype.card (Edge n) - k * (n - k)) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.sum_congr rfl (fun S hS => ?_), Finset.sum_const,
          Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        rw [Finset.mem_powersetCard] at hS
        rw [card_noCross, hS.2]

/-! ### B4  The assembled deficit bound -/

/-- The union bound assembling B1–B3 with `density_implication`.  (`hn : 4 ≤ n`
    is part of the commissioned statement and is kept; the proof does not use
    it.  The isolated-vertex NOTE's pre-authorized fourth term was not needed
    either: the minimum-degree condition is absorbed into the third term.) -/
theorem density_deficit_bound (n : ℕ) (hn : 4 ≤ n) :
    16 ^ (n / 4) * 8 ^ (n - 3) *
      (2 ^ (Fintype.card (Edge n))
        - (univ.filter (fun G : HGraph n => Good G)).card)
      ≤ 16 ^ (n / 4) * 8 ^ (n - 3) *
          ((univ.filter (fun G : HGraph n => ¬ Claw G)).card
            + (univ.filter (fun G : HGraph n =>
                ¬ ∀ i j k : Fin n, i ≠ j → i ≠ k → j ≠ k →
                  adj G i j = true → adj G i k = true →
                  ∃ l, l ≠ i ∧ l ≠ j ∧ l ≠ k ∧ MendWitness G i j k l)).card
            + (univ.filter (fun G : HGraph n => ¬ (VConn G ∧
                ∀ i : Fin n, ∃ j, adj G i j = true))).card) := by
  refine Nat.mul_le_mul_left _ ?_
  set A := univ.filter (fun G : HGraph n => ¬ Claw G) with hA
  set B := univ.filter (fun G : HGraph n =>
      ¬ ∀ i j k : Fin n, i ≠ j → i ≠ k → j ≠ k →
        adj G i j = true → adj G i k = true →
        ∃ l, l ≠ i ∧ l ≠ j ∧ l ≠ k ∧ MendWitness G i j k l) with hB
  set C := univ.filter (fun G : HGraph n =>
      ¬ (VConn G ∧ ∀ i : Fin n, ∃ j, adj G i j = true)) with hC
  have hsub : univ.filter (fun G : HGraph n => ¬ Good G) ⊆ A ∪ B ∪ C := by
    intro G hG
    simp only [hA, hB, hC, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and] at hG ⊢
    by_contra hcon
    push_neg at hcon
    obtain ⟨⟨hclaw, hwit⟩, hconn⟩ := hcon
    exact hG (density_implication G (gconn_of_vconn G hconn.1 hconn.2)
      (mendedAt_of_witnesses G hwit) hclaw)
  have hcards : (univ.filter (fun G : HGraph n => ¬ Good G)).card
      ≤ A.card + B.card + C.card := by
    calc (univ.filter (fun G : HGraph n => ¬ Good G)).card ≤ (A ∪ B ∪ C).card :=
          Finset.card_le_card hsub
    _ ≤ (A ∪ B).card + C.card := Finset.card_union_le _ _
    _ ≤ A.card + B.card + C.card := by
        exact Nat.add_le_add_right (Finset.card_union_le _ _) _
  have hpart : (univ.filter (fun G : HGraph n => Good G)).card
      + (univ.filter (fun G : HGraph n => ¬ Good G)).card = 2 ^ (Fintype.card (Edge n)) := by
    rw [Finset.card_filter_add_card_filter_not]
    simp [Finset.card_univ]
  omega

end HalfOne
