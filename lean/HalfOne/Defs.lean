/-
  HalfOne/Defs.lean — all definitions of the Paper IV formalization.

  Everything is stated over ℚ; no real numbers appear anywhere.
  The definitions are exactly those of the commission's master file; the
  theorems about them live in the topic modules
  (`HalfOne.Basic`, `HalfOne.Walks`, `HalfOne.Checker`, `HalfOne.Census`,
   `HalfOne.Metric`, `HalfOne.Twins`, `HalfOne.Density`, `HalfOne.QLevel`)
  and are all re-exported by `HalfOne.lean`.
-/

import Mathlib

namespace HalfOne

/-! ### §1  Edges and graphs -/

/-- The edge set of the complete graph on `Fin n`: ordered pairs `i < j`. -/
def Edge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

instance (n : ℕ) : DecidableEq (Edge n) := by unfold Edge; infer_instance
instance (n : ℕ) : Fintype (Edge n) := by unfold Edge; infer_instance

/-- A half-length graph on `n` points: which pairs are at distance ½.
    `G e = true` means edge `e` is half-length (a node of Γ);
    `G e = false` means unital. -/
abbrev HGraph (n : ℕ) := Edge n → Bool

instance (n : ℕ) : Fintype (HGraph n) := by infer_instance

/-- Symmetric adjacency lookup for `i ≠ j`. -/
def adj {n : ℕ} (G : HGraph n) (i j : Fin n) : Bool :=
  if h : i < j then G ⟨(i, j), h⟩
  else if h' : j < i then G ⟨(j, i), h'⟩
  else false

/-- Γ-adjacency between two half-length edges (Proposition prop:halfonegamma of
    the paper, taken as the definition here): `e` and `f` are adjacent in Γ
    exactly when both are half-length, they share exactly one endpoint, and the
    pair of remaining endpoints is unital. -/
def gammaAdj {n : ℕ} (G : HGraph n) (e f : Edge n) : Bool :=
  G e && G f && (e ≠ f) &&
  ( -- shared endpoint u with remainders p, q, and (p,q) unital:
    (e.1.1 = f.1.1 && !(adj G e.1.2 f.1.2)) ||
    (e.1.1 = f.1.2 && !(adj G e.1.2 f.1.1)) ||
    (e.1.2 = f.1.1 && !(adj G e.1.1 f.1.2)) ||
    (e.1.2 = f.1.2 && !(adj G e.1.1 f.1.1)) )

/-! ### §2  The good predicate -/

/-- Walks in Γ of a given length, as an inductive predicate. -/
inductive GWalk {n : ℕ} (G : HGraph n) : Edge n → Edge n → ℕ → Prop
  | nil (e : Edge n) : GWalk G e e 0
  | cons {e f g : Edge n} {ℓ : ℕ} :
      gammaAdj G e f = true → GWalk G f g ℓ → GWalk G e g (ℓ + 1)

/-- `e` and `f` are in the same Γ-component. -/
def GReach {n : ℕ} (G : HGraph n) (e f : Edge n) : Prop := ∃ ℓ, GWalk G e f ℓ

/-- A component is bipartite iff it admits a proper 2-coloring.  The paper's
    criterion says a half-one metric is extreme iff NO component of Γ is
    bipartite; `Good` is that condition.  An isolated node is a bipartite
    component (color it either way), and `Good` correctly rejects it: a
    coloring exists trivially. -/
def ComponentBipartite {n : ℕ} (G : HGraph n) (e : Edge n) : Prop :=
  ∃ c : Edge n → Bool, ∀ f g : Edge n,
    GReach G e f → GReach G e g → gammaAdj G f g = true → c f ≠ c g

def Good {n : ℕ} (G : HGraph n) : Prop :=
  ∀ e : Edge n, G e = true → ¬ ComponentBipartite G e

/-- Equivalent form used by the checker: every Γ-node admits an odd closed
    walk (within its component, automatically). -/
def GoodWalk {n : ℕ} (G : HGraph n) : Prop :=
  ∀ e : Edge n, G e = true → ∃ ℓ, Odd ℓ ∧ GWalk G e e ℓ

/-! ### §3  The checker -/

/-- Number of Γ-walks of length `ℓ` from `e` to `f`, by matrix recursion.
    Values in ℕ; only positivity is ever used. -/
def walkCount {n : ℕ} (G : HGraph n) : ℕ → Edge n → Edge n → ℕ
  | 0,     e, f => if e = f then 1 else 0
  | ℓ + 1, e, f => ∑ g : Edge n, (if gammaAdj G e g = true then walkCount G ℓ g f else 0)

/-! ### §5  The metric body over ℚ -/

/-- Distance vectors. -/
abbrev DVec (n : ℕ) := Edge n → ℚ

/-- Symmetric lookup. -/
def dOf {n : ℕ} (d : DVec n) (i j : Fin n) : ℚ :=
  if h : i < j then d ⟨(i, j), h⟩ else if h' : j < i then d ⟨(j, i), h'⟩ else 0

/-- Membership in the metric body: bounds and all triangle inequalities. -/
def InBody {n : ℕ} (d : DVec n) : Prop :=
  (∀ e, 0 ≤ d e ∧ d e ≤ 1) ∧
  ∀ i j k : Fin n, i ≠ j → j ≠ k → i ≠ k →
    dOf d i k ≤ dOf d i j + dOf d j k

/-- Extremality, in perturbation form: the only symmetric perturbation keeping
    both `d + ε` and `d − ε` in the body is zero. -/
def Extreme {n : ℕ} (d : DVec n) : Prop :=
  InBody d ∧ ∀ ε : DVec n, InBody (fun e => d e + ε e) → InBody (fun e => d e - ε e) →
    ∀ e, ε e = 0

/-! ### §7  Twins -/

/-- True twin pair in the half-length graph. -/
def TrueTwins {n : ℕ} (G : HGraph n) (e : Edge n) : Prop :=
  G e = true ∧ ∀ k : Fin n, k ≠ e.1.1 → k ≠ e.1.2 →
    adj G e.1.1 k = adj G e.1.2 k

instance decidableTrueTwins {n : ℕ} (G : HGraph n) (e : Edge n) :
    Decidable (TrueTwins G e) := by
  unfold TrueTwins; infer_instance

/-! ### §8  Density -/

/-- `i` is mended: any two half-length edges at `i` lie in one Γ-component. -/
def Mended {n : ℕ} (G : HGraph n) (i : Fin n) : Prop :=
  ∀ j k : Fin n, adj G i j = true → adj G i k = true → j ≠ k →
    ∀ (hij : _) (hik : _),
      GReach G (if h : i < j then ⟨(i,j),h⟩ else ⟨(j,i), hij⟩)
               (if h : i < k then ⟨(i,k),h⟩ else ⟨(k,i), hik⟩)

/-- Mending, corrected form.  In `Mended` above, the two anonymous proof
    arguments `(hij : _) (hik : _)` elaborate to `j < i` and `k < i`, so that
    definition only constrains pairs of neighbours that are *smaller* than `i`;
    with that reading the density implication is false (see
    `HalfOne.density_implication_Mended_false`).  `MendedAt` is the intended
    statement: any two half-length edges through `i` lie in one Γ-component. -/
def MendedAt {n : ℕ} (G : HGraph n) (i : Fin n) : Prop :=
  ∀ e f : Edge n, G e = true → G f = true →
    (e.1.1 = i ∨ e.1.2 = i) → (f.1.1 = i ∨ f.1.2 = i) → GReach G e f

/-- Induced claw at `i`: three neighbours pairwise non-adjacent. -/
def Claw {n : ℕ} (G : HGraph n) : Prop :=
  ∃ i j k l : Fin n, [i,j,k,l].Nodup ∧
    adj G i j = true ∧ adj G i k = true ∧ adj G i l = true ∧
    adj G j k = false ∧ adj G j l = false ∧ adj G k l = false

/-- Connectivity of the half-length graph itself. -/
def GConn {n : ℕ} (G : HGraph n) : Prop :=
  ∀ e f : Edge n, G e = true → G f = true →
    -- e and f joined by a walk of half-length edges sharing endpoints:
    Relation.ReflTransGen
      (fun a b : Edge n => G a = true ∧ G b = true ∧ a ≠ b ∧
        (a.1.1 = b.1.1 ∨ a.1.1 = b.1.2 ∨ a.1.2 = b.1.1 ∨ a.1.2 = b.1.2)) e f

end HalfOne
