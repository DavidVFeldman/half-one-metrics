/-
  HalfOne/Descent.lean — Round 6, Tier C1: the descent API for `prop:descent`.

  The commission asks for the quotient step of `prop:descent` to be designed as
  *data* rather than as a Lean `Quotient`: a surjection `π : Fin n → Fin k`
  presented together with a section, a `pullback` operation on distance vectors,
  and the two statements

    * the pullback of a positive-definite vertex is a vertex, and
    * every vertex is the pullback of a positive-definite vertex along its own
      zero-partition.

  Both statements are proved here.  The design note recorded in LEDGER.md:
  presenting the quotient as `Descent n k` (a projection with a section) is what
  makes the development friction-free — every transfer lemma below is a
  computation with `dOf`, and no `Quotient.lift`/`Quotient.ind` ever appears.
-/

import HalfOne.Metric

namespace HalfOne

variable {n k m : ℕ}

/-! ### Elementary consequences of `InBody` -/

/-- Distances read off a body point are nonnegative. -/
theorem dOf_nonneg {d : DVec n} (hb : InBody d) (i j : Fin n) : 0 ≤ dOf d i j := by
  rcases eq_or_ne i j with rfl | h
  · rw [dOf_self]
  · obtain ⟨f, hf⟩ := dOf_eq_coord d h
    rw [hf]; exact (hb.1 f).1

/-- Distances read off a body point are at most one. -/
theorem dOf_le_one {d : DVec n} (hb : InBody d) (i j : Fin n) : dOf d i j ≤ 1 := by
  rcases eq_or_ne i j with rfl | h
  · rw [dOf_self]; norm_num
  · obtain ⟨f, hf⟩ := dOf_eq_coord d h
    rw [hf]; exact (hb.1 f).2

/-- The triangle inequality of `InBody`, with the distinctness hypotheses removed. -/
theorem dOf_triangle_all {d : DVec n} (hb : InBody d) (i j l : Fin n) :
    dOf d i l ≤ dOf d i j + dOf d j l := by
  rcases eq_or_ne i j with rfl | hij
  · rw [dOf_self, zero_add]
  rcases eq_or_ne j l with rfl | hjl
  · rw [dOf_self, add_zero]
  rcases eq_or_ne i l with rfl | hil
  · rw [dOf_self]
    exact add_nonneg (dOf_nonneg hb _ _) (dOf_nonneg hb _ _)
  · exact hb.2 i j l hij hjl hil

/-- Zero distance is transitive on a body point. -/
theorem dOf_zero_trans {d : DVec n} (hb : InBody d) {i j l : Fin n}
    (h1 : dOf d i j = 0) (h2 : dOf d j l = 0) : dOf d i l = 0 :=
  le_antisymm (by simpa [h1, h2] using dOf_triangle_all hb i j l) (dOf_nonneg hb i l)

/-! ### The descent data -/

/-- A presentation of a quotient of `Fin n` with `k` classes as *data*: a
    projection together with a section.  `proj_sect` makes `proj` surjective and
    `sect` injective. -/
structure Descent (n k : ℕ) where
  /-- The projection onto the quotient. -/
  proj : Fin n → Fin k
  /-- A choice of class representative. -/
  sect : Fin k → Fin n
  /-- The section identity. -/
  proj_sect : ∀ a, proj (sect a) = a

namespace Descent

theorem proj_surjective (D : Descent n k) : Function.Surjective D.proj :=
  fun a => ⟨D.sect a, D.proj_sect a⟩

theorem sect_injective (D : Descent n k) : Function.Injective D.sect := by
  intro a b h
  rw [← D.proj_sect a, ← D.proj_sect b, h]

end Descent

/-- Transport of a distance vector along an arbitrary map of index sets.  Both
    the pullback along a projection and the restriction along a section are
    instances. -/
def comap (s : Fin m → Fin n) (d : DVec n) : DVec m :=
  fun e => dOf d (s e.1.1) (s e.1.2)

/-- The pullback of a distance vector along a descent. -/
def pullback (D : Descent n k) (d : DVec k) : DVec n := comap D.proj d

/-- `dOf` on an ordered pair is the corresponding coordinate. -/
theorem dOf_of_lt (d : DVec n) {i j : Fin n} (h : i < j) :
    dOf d i j = d ⟨(i, j), h⟩ := by
  unfold dOf; rw [dif_pos h]

/-- `dOf` at the endpoints of an edge is the coordinate at that edge. -/
theorem dOf_edge (d : DVec n) (f : Edge n) : dOf d f.1.1 f.1.2 = d f := by
  rw [dOf_of_lt d f.2]
  exact congrArg d (Subtype.ext rfl)

/-- Distances in a transported vector are the transported distances. -/
theorem dOf_comap (s : Fin m → Fin n) (d : DVec n) (a b : Fin m) :
    dOf (comap s d) a b = dOf d (s a) (s b) := by
  rcases lt_trichotomy a b with h | rfl | h
  · rw [dOf_of_lt _ h]; rfl
  · rw [dOf_self, dOf_self]
  · rw [dOf_symm (comap s d), dOf_of_lt _ h, dOf_symm d]; rfl

theorem dOf_pullback (D : Descent n k) (d : DVec k) (i j : Fin n) :
    dOf (pullback D d) i j = dOf d (D.proj i) (D.proj j) :=
  dOf_comap _ _ _ _

theorem comap_add (s : Fin m → Fin n) (d e : DVec n) :
    comap s (fun f => d f + e f) = fun f => comap s d f + comap s e f := by
  funext f; simp only [comap, dOf_add]

theorem comap_sub (s : Fin m → Fin n) (d e : DVec n) :
    comap s (fun f => d f - e f) = fun f => comap s d f - comap s e f := by
  funext f; simp only [comap, dOf_sub]

theorem comap_zero (s : Fin m → Fin n) : comap s (fun _ => (0 : ℚ)) = fun _ => (0 : ℚ) := by
  funext f
  show dOf (fun _ => (0 : ℚ)) _ _ = 0
  unfold dOf; split <;> [rfl; split] <;> rfl

theorem pullback_add (D : Descent n k) (d e : DVec k) :
    pullback D (fun f => d f + e f) = fun i => pullback D d i + pullback D e i :=
  comap_add _ _ _

theorem pullback_sub (D : Descent n k) (d e : DVec k) :
    pullback D (fun f => d f - e f) = fun i => pullback D d i - pullback D e i :=
  comap_sub _ _ _

/-- Transport preserves membership in the metric body. -/
theorem inBody_comap {d : DVec n} (hb : InBody d) (s : Fin m → Fin n) :
    InBody (comap s d) := by
  refine ⟨fun e => ⟨?_, ?_⟩, ?_⟩
  · exact dOf_nonneg hb _ _
  · exact dOf_le_one hb _ _
  · intro a b c _ _ _
    rw [dOf_comap, dOf_comap, dOf_comap]
    exact dOf_triangle_all hb _ _ _

/-- Restricting a pullback along the section recovers the original vector. -/
theorem comap_sect_pullback (D : Descent n k) (d : DVec k) :
    comap D.sect (pullback D d) = d := by
  funext f
  rw [comap, dOf_pullback, D.proj_sect, D.proj_sect, dOf_edge]

/-- The pullback map is injective. -/
theorem pullback_injective (D : Descent n k) : Function.Injective (pullback D) := by
  intro d e h
  rw [← comap_sect_pullback D d, ← comap_sect_pullback D e, h]

/-- Positive definiteness: distinct points are at positive distance. -/
def PosDef (d : DVec k) : Prop := ∀ a b : Fin k, a ≠ b → 0 < dOf d a b

/-! ### C1, statement 1: the pullback of a vertex is a vertex -/

/-- Coordinates of a perturbation vanish inside a fibre. -/
private theorem perturb_zero_in_fibre {D : Descent n k} {d : DVec k} {ε : DVec n}
    (hp : InBody (fun e => pullback D d e + ε e))
    (hm : InBody (fun e => pullback D d e - ε e))
    {i j : Fin n} (hij : D.proj i = D.proj j) : dOf ε i j = 0 := by
  have h0 : dOf (pullback D d) i j = 0 := by rw [dOf_pullback, hij, dOf_self]
  have hp' := dOf_nonneg hp i j
  have hm' := dOf_nonneg hm i j
  rw [dOf_add, h0, zero_add] at hp'
  rw [dOf_sub, h0, zero_sub, neg_nonneg] at hm'
  exact le_antisymm hm' hp'

/-- A perturbation is constant along fibres. -/
private theorem perturb_fibre_const {D : Descent n k} {d : DVec k} {ε : DVec n}
    (hp : InBody (fun e => pullback D d e + ε e))
    (hm : InBody (fun e => pullback D d e - ε e))
    {i i' : Fin n} (hii : D.proj i = D.proj i') (j : Fin n) :
    dOf ε i j = dOf ε i' j := by
  set δ : DVec n := fun e => pullback D d e + ε e with hδ
  have hzero : dOf δ i i' = 0 := by
    rw [hδ, dOf_add, dOf_pullback, hii, dOf_self, zero_add,
      perturb_zero_in_fibre hp hm hii]
  have h1 : dOf δ i j ≤ dOf δ i' j := by
    have := dOf_triangle_all hp i i' j
    rw [hzero] at this; simpa using this
  have h2 : dOf δ i' j ≤ dOf δ i j := by
    have := dOf_triangle_all hp i' i j
    have hzero' : dOf δ i' i = 0 := by rw [dOf_symm]; exact hzero
    rw [hzero'] at this; simpa using this
  have heq : dOf δ i j = dOf δ i' j := le_antisymm h1 h2
  rw [hδ, dOf_add, dOf_add, dOf_pullback, dOf_pullback, hii] at heq
  exact add_left_cancel heq

/-- **C1, statement 1.**  The pullback of a positive-definite vertex of the
    metric body on `k` points is a vertex of the metric body on `n` points.

    The positive-definiteness hypothesis is the one the commission asks for; the
    proof does not use it (extremality alone suffices, because the zero
    coordinates created by the pullback pin the perturbation to zero inside each
    fibre). -/
theorem pullback_extreme (D : Descent n k) {d : DVec k} (hx : Extreme d)
    (_hpos : PosDef d) : Extreme (pullback D d) := by
  refine ⟨inBody_comap hx.1 _, ?_⟩
  intro ε hp hm e
  set ε' : DVec k := comap D.sect ε with hε'
  have hdesc : pullback D ε' = ε := by
    funext f
    have h1 : dOf ε (D.sect (D.proj f.1.1)) (D.sect (D.proj f.1.2))
        = dOf ε f.1.1 f.1.2 := by
      have ha : D.proj (D.sect (D.proj f.1.1)) = D.proj f.1.1 := D.proj_sect _
      have hb : D.proj (D.sect (D.proj f.1.2)) = D.proj f.1.2 := D.proj_sect _
      calc dOf ε (D.sect (D.proj f.1.1)) (D.sect (D.proj f.1.2))
          = dOf ε f.1.1 (D.sect (D.proj f.1.2)) :=
            perturb_fibre_const hp hm ha _
        _ = dOf ε (D.sect (D.proj f.1.2)) f.1.1 := dOf_symm _ _ _
        _ = dOf ε f.1.2 f.1.1 := perturb_fibre_const hp hm hb _
        _ = dOf ε f.1.1 f.1.2 := dOf_symm _ _ _
    rw [pullback, comap, hε', dOf_comap, h1, dOf_edge]
  -- the descended perturbation keeps `d` in the body both ways
  have hp' : InBody (fun f => d f + ε' f) := by
    have : (fun f => d f + ε' f) = comap D.sect (fun e => pullback D d e + ε e) := by
      rw [comap_add, comap_sect_pullback, ← hε']
    rw [this]; exact inBody_comap hp _
  have hm' : InBody (fun f => d f - ε' f) := by
    have : (fun f => d f - ε' f) = comap D.sect (fun e => pullback D d e - ε e) := by
      rw [comap_sub, comap_sect_pullback, ← hε']
    rw [this]; exact inBody_comap hm _
  have hzero : ε' = fun _ => (0 : ℚ) := funext (hx.2 ε' hp' hm')
  have : ε = fun _ => (0 : ℚ) := by
    rw [← hdesc, hzero, pullback, comap_zero]
  rw [this]

/-! ### C1, statement 2: every vertex is a pullback along its own zero-partition -/

section ZeroPartition

variable {d : DVec n}

/-- The zero class of `i`: all points at distance `0` from `i`. -/
def zclass (d : DVec n) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => dOf d i j = 0)

theorem self_mem_zclass (d : DVec n) (i : Fin n) : i ∈ zclass d i := by
  simp [zclass, dOf_self]

/-- The chosen representative of the zero class of `i`: its least element. -/
def zrep (d : DVec n) (i : Fin n) : Fin n :=
  (zclass d i).min' ⟨i, self_mem_zclass d i⟩

theorem dOf_zrep (d : DVec n) (i : Fin n) : dOf d i (zrep d i) = 0 := by
  have := (zclass d i).min'_mem ⟨i, self_mem_zclass d i⟩
  simpa [zclass] using this

theorem zclass_eq_of_zero (hb : InBody d) {i j : Fin n} (h : dOf d i j = 0) :
    zclass d i = zclass d j := by
  have hji : dOf d j i = 0 := by rw [dOf_symm]; exact h
  ext l
  simp only [zclass, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hl; exact dOf_zero_trans hb hji hl
  · intro hl; exact dOf_zero_trans hb h hl

theorem zrep_eq_of_zero (hb : InBody d) {i j : Fin n} (h : dOf d i j = 0) :
    zrep d i = zrep d j := by
  unfold zrep; congr 1
  exact zclass_eq_of_zero hb h

theorem zrep_idem (hb : InBody d) (i : Fin n) : zrep d (zrep d i) = zrep d i :=
  (zrep_eq_of_zero hb (dOf_zrep d i)).symm

theorem zero_of_zrep_eq (hb : InBody d) {i j : Fin n} (h : zrep d i = zrep d j) :
    dOf d i j = 0 := by
  have h1 : dOf d i (zrep d i) = 0 := dOf_zrep d i
  have h2 : dOf d (zrep d i) j = 0 := by
    rw [h, dOf_symm]; exact dOf_zrep d j
  exact dOf_zero_trans hb h1 h2

/-- Distances are unchanged when both endpoints are replaced by representatives. -/
theorem dOf_zrep_zrep (hb : InBody d) (i j : Fin n) :
    dOf d (zrep d i) (zrep d j) = dOf d i j := by
  have hi : dOf d i (zrep d i) = 0 := dOf_zrep d i
  have hj : dOf d j (zrep d j) = 0 := dOf_zrep d j
  have hi' : dOf d (zrep d i) i = 0 := by rw [dOf_symm]; exact hi
  have hj' : dOf d (zrep d j) j = 0 := by rw [dOf_symm]; exact hj
  refine le_antisymm ?_ ?_
  · calc dOf d (zrep d i) (zrep d j)
        ≤ dOf d (zrep d i) i + dOf d i (zrep d j) := dOf_triangle_all hb _ _ _
      _ = dOf d i (zrep d j) := by rw [hi', zero_add]
      _ ≤ dOf d i j + dOf d j (zrep d j) := dOf_triangle_all hb _ _ _
      _ = dOf d i j := by rw [hj, add_zero]
  · calc dOf d i j
        ≤ dOf d i (zrep d i) + dOf d (zrep d i) j := dOf_triangle_all hb _ _ _
      _ = dOf d (zrep d i) j := by rw [hi, zero_add]
      _ ≤ dOf d (zrep d i) (zrep d j) + dOf d (zrep d j) j := dOf_triangle_all hb _ _ _
      _ = dOf d (zrep d i) (zrep d j) := by rw [hj', add_zero]

/-- The set of representatives of the zero-partition of `d`. -/
def zreps (d : DVec n) : Finset (Fin n) := Finset.image (zrep d) Finset.univ

theorem zrep_mem_zreps (d : DVec n) (i : Fin n) : zrep d i ∈ zreps d := by
  simp [zreps]

theorem zrep_of_mem_zreps (hb : InBody d) {x : Fin n} (hx : x ∈ zreps d) :
    zrep d x = x := by
  simp only [zreps, Finset.mem_image, Finset.mem_univ, true_and] at hx
  obtain ⟨i, hi⟩ := hx
  rw [← hi, zrep_idem hb]

/-- The zero-partition of a body point, presented as descent data. -/
def zdescent (hb : InBody d) : Descent n (zreps d).card where
  proj := fun i => ((zreps d).orderIsoOfFin rfl).symm ⟨zrep d i, zrep_mem_zreps d i⟩
  sect := fun a => (((zreps d).orderIsoOfFin rfl) a : Fin n)
  proj_sect := by
    intro a
    have hmem : (((zreps d).orderIsoOfFin rfl) a : Fin n) ∈ zreps d :=
      (((zreps d).orderIsoOfFin rfl) a).2
    have : zrep d (((zreps d).orderIsoOfFin rfl) a : Fin n)
        = (((zreps d).orderIsoOfFin rfl) a : Fin n) := zrep_of_mem_zreps hb hmem
    simp only [this]
    exact (((zreps d).orderIsoOfFin rfl).symm_apply_apply a)

theorem zdescent_sect_proj (hb : InBody d) (i : Fin n) :
    (zdescent hb).sect ((zdescent hb).proj i) = zrep d i := by
  show ((((zreps d).orderIsoOfFin rfl) (((zreps d).orderIsoOfFin rfl).symm
    ⟨zrep d i, zrep_mem_zreps d i⟩)) : Fin n) = zrep d i
  rw [OrderIso.apply_symm_apply]

/-- The pullback along the zero-partition descent of the restriction of `d`
    recovers `d`. -/
theorem pullback_zdescent (hb : InBody d) :
    pullback (zdescent hb) (comap (zdescent hb).sect d) = d := by
  funext e
  have h1 : dOf d (zrep d e.1.1) (zrep d e.1.2) = dOf d e.1.1 e.1.2 :=
    dOf_zrep_zrep hb _ _
  rw [pullback, comap, dOf_comap, zdescent_sect_proj, zdescent_sect_proj, h1, dOf_edge]

/-- **C1, statement 2.**  Every vertex of the metric body is the pullback, along
    the descent given by its own zero-partition, of a positive-definite vertex. -/
theorem exists_descent_of_extreme {d : DVec n} (hx : Extreme d) :
    ∃ (k : ℕ) (D : Descent n k) (d' : DVec k),
      PosDef d' ∧ Extreme d' ∧ pullback D d' = d := by
  classical
  set D := zdescent hx.1 with hD
  refine ⟨(zreps d).card, D, comap D.sect d, ?_, ?_, ?_⟩
  · -- positive definiteness
    intro a b hab
    rcases lt_or_eq_of_le (dOf_nonneg (inBody_comap hx.1 D.sect) a b) with h | h
    · exact h
    · exfalso
      rw [dOf_comap] at h
      have hz : dOf d (D.sect a) (D.sect b) = 0 := h.symm
      have := zrep_eq_of_zero hx.1 hz
      rw [zrep_of_mem_zreps hx.1 (by
            have : D.sect a = (((zreps d).orderIsoOfFin rfl) a : Fin n) := rfl
            rw [this]; exact (((zreps d).orderIsoOfFin rfl) a).2),
          zrep_of_mem_zreps hx.1 (by
            have : D.sect b = (((zreps d).orderIsoOfFin rfl) b : Fin n) := rfl
            rw [this]; exact (((zreps d).orderIsoOfFin rfl) b).2)] at this
      exact hab (D.sect_injective this)
  · -- extremality of the descended vector
    refine ⟨inBody_comap hx.1 _, ?_⟩
    intro e' hp hm f
    have hpull : pullback D (comap D.sect d) = d := pullback_zdescent hx.1
    have hp2 : InBody (fun i => d i + pullback D e' i) := by
      have : (fun i => d i + pullback D e' i)
          = pullback D (fun f => comap D.sect d f + e' f) := by
        rw [pullback_add, hpull]
      rw [this, pullback]; exact inBody_comap hp _
    have hm2 : InBody (fun i => d i - pullback D e' i) := by
      have : (fun i => d i - pullback D e' i)
          = pullback D (fun f => comap D.sect d f - e' f) := by
        rw [pullback_sub, hpull]
      rw [this, pullback]; exact inBody_comap hm _
    have hzero : pullback D e' = fun _ => (0 : ℚ) := funext (hx.2 _ hp2 hm2)
    have : e' = fun _ => (0 : ℚ) := by
      rw [← comap_sect_pullback D e', hzero, comap_zero]
    rw [this]
  · exact pullback_zdescent hx.1

end ZeroPartition

end HalfOne
