/-
  HalfOne/Density.lean — §8, Round 5: the deterministic implication behind
  thm:density.

  The commissioned statement was

    theorem density_implication {n : ℕ} (G : HGraph n)
      (hconn : GConn G) (hmend : ∀ i, Mended G i) (hclaw : Claw G) : Good G

  with `Mended` as in `HalfOne.Defs`.  As literally elaborated, the two
  anonymous binders `(hij : _) (hik : _)` of `Mended` have types `j < i` and
  `k < i`, so `Mended G i` only constrains neighbours of `i` that are smaller
  than `i`, and the implication is **false**: `density_implication_Mended_false`
  below exhibits an explicit five-point counterexample.  The intended
  hypothesis is `MendedAt` (see `HalfOne.Defs`), and with it the implication
  holds: `density_implication`.
-/

import HalfOne.Walks
import HalfOne.Counting

namespace HalfOne

variable {n : ℕ} {G : HGraph n}

/-! ### Γ-reachability is an equivalence relation -/

theorem GReach.refl (G : HGraph n) (e : Edge n) : GReach G e e := ⟨0, GWalk.nil e⟩

theorem GReach.trans {e f g : Edge n} (h₁ : GReach G e f) (h₂ : GReach G f g) :
    GReach G e g := by
  obtain ⟨a, wa⟩ := h₁
  obtain ⟨b, wb⟩ := h₂
  exact ⟨a + b, wa.append wb⟩

theorem GReach.symm {e f : Edge n} (h : GReach G e f) : GReach G f e := by
  obtain ⟨a, wa⟩ := h
  exact ⟨a, wa.reverse⟩

/-! ### Γ-adjacency of two edges sharing a vertex -/

/-- Two half-length edges through `u`, whose other endpoints `v`, `w` are
    distinct and unital, are Γ-adjacent. -/
theorem gammaAdj_of_shared (G : HGraph n) (u v w : Fin n) (huv : u ≠ v) (huw : u ≠ w)
    (hvw : v ≠ w)
    (h1 : adj G u v = true) (h2 : adj G u w = true) (h3 : adj G v w = false) :
    gammaAdj G (edgeOf u v huv) (edgeOf u w huw) = true := by
  have hGe : G (edgeOf u v huv) = true := by rw [← adj_eq_edgeOf G u v huv]; exact h1
  have hGf : G (edgeOf u w huw) = true := by rw [← adj_eq_edgeOf G u w huw]; exact h2
  have hne : edgeOf u v huv ≠ edgeOf u w huw := by
    intro h
    have e1 : (edgeOf u v huv).1.1 = (edgeOf u w huw).1.1 := by rw [h]
    have e2 : (edgeOf u v huv).1.2 = (edgeOf u w huw).1.2 := by rw [h]
    rcases edgeOf_endpoints u v huv with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
      rcases edgeOf_endpoints u w huw with ⟨hc, hd⟩ | ⟨hc, hd⟩ <;>
        rw [ha, hc] at e1 <;> rw [hb, hd] at e2 <;> simp_all
  unfold gammaAdj
  rcases edgeOf_endpoints u v huv with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
    rcases edgeOf_endpoints u w huw with ⟨hc, hd⟩ | ⟨hc, hd⟩ <;>
      simp [hGe, hGf, hne, ha, hb, hc, hd, h3]

/-! ### From the claw to an odd closed Γ-walk -/

/-- A claw at `i` with leaves `j, k, l` produces a Γ-triangle, hence a closed
    Γ-walk of length 3 at the edge `{i,j}`. -/
theorem claw_triangle (G : HGraph n) {i j k l : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk' : j ≠ k) (hjl' : j ≠ l) (hkl' : k ≠ l)
    (h1 : adj G i j = true) (h2 : adj G i k = true) (h3 : adj G i l = true)
    (hjk : adj G j k = false) (hjl : adj G j l = false) (hkl : adj G k l = false) :
    GWalk G (edgeOf i j hij) (edgeOf i j hij) 3 := by
  have a1 : gammaAdj G (edgeOf i j hij) (edgeOf i k hik) = true :=
    gammaAdj_of_shared G i j k hij hik hjk' h1 h2 hjk
  have a2 : gammaAdj G (edgeOf i k hik) (edgeOf i l hil) = true :=
    gammaAdj_of_shared G i k l hik hil hkl' h2 h3 hkl
  have a3 : gammaAdj G (edgeOf i l hil) (edgeOf i j hij) = true := by
    rw [gammaAdj_symm]
    exact gammaAdj_of_shared G i j l hij hil hjl' h1 h3 hjl
  exact GWalk.cons a1 (GWalk.cons a2 (GWalk.cons a3 (GWalk.nil _)))

/-- Transporting an odd closed walk along a Γ-path. -/
theorem odd_closed_of_reach {e a : Edge n} (hr : GReach G e a)
    (h : ∃ ℓ, Odd ℓ ∧ GWalk G a a ℓ) : ∃ ℓ, Odd ℓ ∧ GWalk G e e ℓ := by
  obtain ⟨m, w⟩ := hr
  obtain ⟨ℓ, hodd, wa⟩ := h
  refine ⟨m + (ℓ + m), ?_, w.append (wa.append w.reverse)⟩
  obtain ⟨t, ht⟩ := hodd
  exact ⟨m + t, by omega⟩

/-! ### Connectivity plus mending gives Γ-connectivity -/

/-- One step of a `GConn` chain is a Γ-reachability step, given mending. -/
theorem reach_of_step (G : HGraph n) (hmend : ∀ i, MendedAt G i) {a b : Edge n}
    (h : G a = true ∧ G b = true ∧ a ≠ b ∧
      (a.1.1 = b.1.1 ∨ a.1.1 = b.1.2 ∨ a.1.2 = b.1.1 ∨ a.1.2 = b.1.2)) :
    GReach G a b := by
  obtain ⟨ha, hb, -, hshare⟩ := h
  rcases hshare with hs | hs | hs | hs
  · exact hmend b.1.1 a b ha hb (Or.inl hs) (Or.inl rfl)
  · exact hmend b.1.2 a b ha hb (Or.inl hs) (Or.inr rfl)
  · exact hmend b.1.1 a b ha hb (Or.inr hs) (Or.inl rfl)
  · exact hmend b.1.2 a b ha hb (Or.inr hs) (Or.inr rfl)

theorem reach_of_gconn (G : HGraph n) (hconn : GConn G) (hmend : ∀ i, MendedAt G i)
    {e f : Edge n} (he : G e = true) (hf : G f = true) : GReach G e f := by
  have h := hconn e f he hf
  clear hf
  induction h with
  | refl => exact GReach.refl G e
  | tail _ hstep ih => exact GReach.trans ih (reach_of_step G hmend hstep)

/-! ### R5  The density implication -/

/-- The heart of thm:density, deterministic form: connectivity + universal
    mending (in the corrected sense `MendedAt`) + a claw force `Good`. -/
theorem density_implication {n : ℕ} (G : HGraph n)
    (hconn : GConn G) (hmend : ∀ i, MendedAt G i) (hclaw : Claw G) : Good G := by
  rw [good_iff_goodWalk]
  obtain ⟨i, j, k, l, hnodup, h1, h2, h3, hjk, hjl, hkl⟩ := hclaw
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, and_true,
    not_or, not_false_iff] at hnodup
  obtain ⟨⟨hij, hik, hil⟩, ⟨hjk', hjl'⟩, hkl'⟩ := hnodup
  have htri : GWalk G (edgeOf i j hij) (edgeOf i j hij) 3 :=
    claw_triangle G hij hik hil hjk' hjl' hkl' h1 h2 h3 hjk hjl hkl
  have hA : G (edgeOf i j hij) = true := by rw [← adj_eq_edgeOf G i j hij]; exact h1
  intro e he
  exact odd_closed_of_reach (reach_of_gconn G hconn hmend he hA) ⟨3, ⟨1, rfl⟩, htri⟩

/-! ### The literal reading of `Mended` is too weak -/

/-- A Γ-isolated node reaches nothing but itself. -/
theorem reach_isolated {e f : Edge n} (h : ∀ x, gammaAdj G e x = false)
    (hr : GReach G e f) : f = e := by
  obtain ⟨ℓ, w⟩ := hr
  cases w with
  | nil => rfl
  | cons hxy _ => rw [h] at hxy; exact absurd hxy (by simp)

/-- The five-point counterexample: the triangle `{0,1,2}` together with the two
    pendant edges `{2,3}` and `{2,4}`.  It is connected, it has a claw at `2`
    (leaves `0`, `3`, `4`), and it satisfies `Mended` as literally elaborated —
    the only pair of neighbours `j, k < i` of a vertex `i` with both `{i,j}` and
    `{i,k}` half-length is `i = 2`, `{j,k} = {0,1}`, and those two edges are
    joined in Γ through `{2,3}`.  But the edge `{0,1}` is Γ-isolated, so its
    component is bipartite and the graph is not `Good`. -/
def cexG : HGraph 5 := fun e =>
  decide (((e.1.1 : ℕ), (e.1.2 : ℕ)) ∈ ([(0,1), (0,2), (1,2), (2,3), (2,4)] : List (ℕ × ℕ)))

/-- The edge `{0,1}` of the counterexample; it is Γ-isolated. -/
def cexE01 : Edge 5 := ⟨(0, 1), by decide⟩
/-- The edge `{0,2}` of the counterexample. -/
def cexE02 : Edge 5 := ⟨(0, 2), by decide⟩
/-- The edge `{1,2}` of the counterexample. -/
def cexE12 : Edge 5 := ⟨(1, 2), by decide⟩
/-- The edge `{2,3}` of the counterexample. -/
def cexE23 : Edge 5 := ⟨(2, 3), by decide⟩

theorem cex_reach : GReach cexG cexE02 cexE12 :=
  ⟨2, GWalk.cons (f := cexE23) (by decide) (GWalk.cons (by decide) (GWalk.nil _))⟩

theorem cex_reach' : GReach cexG cexE12 cexE02 := GReach.symm cex_reach

theorem cex_claw : Claw cexG :=
  ⟨2, 0, 3, 4, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem cex_mended : ∀ i, Mended cexG i := by
  intro i j k h1 h2 hjk hij hik
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first
      | exact absurd hij (by decide)
      | exact absurd hik (by decide)
      | exact absurd hjk (by decide)
      | exact absurd h1 (by decide)
      | exact absurd h2 (by decide)
      | (show GReach cexG cexE02 cexE12; exact cex_reach)
      | (show GReach cexG cexE12 cexE02; exact cex_reach')

theorem cex_conn : GConn cexG := by
  set R : Edge 5 → Edge 5 → Prop := fun a b => cexG a = true ∧ cexG b = true ∧ a ≠ b ∧
    (a.1.1 = b.1.1 ∨ a.1.1 = b.1.2 ∨ a.1.2 = b.1.1 ∨ a.1.2 = b.1.2) with hR
  have hsymm : Symmetric R := by
    rintro a b ⟨h1, h2, h3, h4⟩
    exact ⟨h2, h1, h3.symm, by tauto⟩
  have key : ∀ e : Edge 5, cexG e = true → Relation.ReflTransGen R e cexE02 := by
    intro e he
    have hm : e ∈ (Finset.univ : Finset (Edge 5)) := Finset.mem_univ e
    rw [hR]
    fin_cases hm <;>
      first
        | exact absurd he (by decide)
        | exact Relation.ReflTransGen.refl
        | exact Relation.ReflTransGen.single (by decide)
  intro e f he hf
  exact Relation.ReflTransGen.trans (key e he)
    (Relation.ReflTransGen.symmetric hsymm (key f hf))

/-- With `Mended` read literally, the density implication fails. -/
theorem density_implication_Mended_false :
    ¬ (∀ (n : ℕ) (G : HGraph n), GConn G → (∀ i, Mended G i) → Claw G → Good G) := by
  intro h
  have hgood := h 5 cexG cex_conn cex_mended cex_claw
  refine hgood cexE01 (by decide) ⟨fun _ => false, ?_⟩
  intro f g hf hg hfg
  exfalso
  have hiso : ∀ x, gammaAdj cexG cexE01 x = false := by decide
  rw [reach_isolated hiso hf, reach_isolated hiso hg, gammaAdj_irrefl] at hfg
  exact Bool.noConfusion hfg

end HalfOne
