/-
Authors: Gonzalo Martínez-Fernández
-/

import FreeProducts.Counterexamples.Auxiliary
import FreeProducts.AVLvsVL.Coproducts.Equivalences
import BanLat.Atom

/-!
# Local projectivity does not imply free embeddability

Every finitely generated sublattice of the finite-range real sequences is projective,
but the whole lattice embeds into no free vector lattice. Infinitely many disjoint
components of its constant-one sequence obstruct such an embedding.
-/

noncomputable section

universe u

namespace VectorLattice.Counterexamples

/-- Real sequences with finite range. -/
def finiteRangeSequences : VectorSublattice (ℕ → ℝ) where
  carrier := {f | (Set.range f).Finite}
  zero_mem' := Set.finite_range_const
  add_mem' := fun {f g} hf hg ↦ (Set.Finite.image2 (· + ·) hf hg).subset
    (fun _ ⟨k, hk⟩ ↦ ⟨f k, ⟨k, rfl⟩, g k, ⟨k, rfl⟩, hk⟩)
  smul_mem' := fun r f hf ↦ (hf.image (r • ·)).subset
    (fun _ ⟨k, hk⟩ ↦ ⟨f k, ⟨k, rfl⟩, hk⟩)
  sup_mem' := fun {f g} hf hg ↦ (Set.Finite.image2 (· ⊔ ·) hf hg).subset
    (fun _ ⟨k, hk⟩ ↦ ⟨f k, ⟨k, rfl⟩, g k, ⟨k, rfl⟩, hk⟩)

/-- Elements of a finitely generated sequence sublattice are constant on the common fibers of
its generators. -/
private lemma generated_sequence_fibre_eq
    (S : VectorSublattice finiteRangeSequences) {n : ℕ} (g : Fin n → S)
    (hg : VectorSublattice.generated (Set.range g) = ⊤) (f : S) {k l : ℕ}
    (h : ∀ i, (g i).val.val k = (g i).val.val l) : f.val.val k = f.val.val l := by
  let D : VectorSublattice S :=
    { carrier := {a | a.val.val k = a.val.val l}
      zero_mem' := rfl
      add_mem' := fun ha hb ↦ congrArg₂ (· + ·) ha hb
      smul_mem' := fun r _ ha ↦ congrArg (r • ·) ha
      sup_mem' := fun ha hb ↦ congrArg₂ (· ⊔ ·) ha hb }
  have hD : VectorSublattice.generated (Set.range g) ≤ D :=
    VectorSublattice.generated_le (fun _ ⟨i, hi⟩ ↦ hi ▸ h i)
  exact hD (hg.symm ▸ show f ∈ (⊤ : VectorSublattice S) from trivial)

/-- A finitely generated sublattice of finite-range sequences is finite dimensional. -/
private lemma finiteRange_fg_finiteDimensional
    (S : VectorSublattice finiteRangeSequences) (hS : IsFinitelyGenerated S) :
    FiniteDimensional ℝ S := by
  classical
  obtain ⟨n, g, hg⟩ := hS
  let (i : Fin n) : Fintype (Set.range (g i).val.val) := (g i).val.property.fintype
  let p (k : ℕ) : (i : Fin n) → Set.range (g i).val.val := fun i ↦ ⟨_, k, rfl⟩
  let sample (b : Set.range p) : ℕ := Classical.choose b.property
  let E : S →ₗ[ℝ] (Set.range p → ℝ) :=
    { toFun := fun f b ↦ f.val.val (sample b)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  refine FiniteDimensional.of_injective E (fun f h hfh ↦ ?_)
  refine Subtype.ext (Subtype.ext (funext (fun k ↦ ?_)))
  have hs : ∀ i, (g i).val.val (sample ⟨p k, k, rfl⟩) = (g i).val.val k :=
    fun i ↦ congrArg (fun b ↦ (b i).val)
      (Classical.choose_spec (show p k ∈ Set.range p from ⟨k, rfl⟩))
  exact (generated_sequence_fibre_eq S g hg f hs).symm.trans
    ((congrFun hfh ⟨p k, k, rfl⟩).trans (generated_sequence_fibre_eq S g hg h hs))

/-- A positive free-lattice bump concentrated near one coordinate direction, used to embed
finite coordinate lattices. -/
private def coordinateBump {n : ℕ} (i : Fin n) : FVL (Fin n) :=
  (2 • FVL.of i - ∑ j, |FVL.of j|)⁺

/-- The coordinate bump is the positive part of twice the selected coordinate minus the sum of
all absolute coordinates. -/
private lemma coordinateBump_apply {n : ℕ} (i : Fin n) (x : Fin n → ℝ) :
    coordinateBump i x = max (2 * x i - ∑ j, |x j|) 0 := by
  simp [coordinateBump, posPart_def, abs, FVL.coordinate, Finset.sum_apply]

/-- Bumps associated with distinct coordinates are disjoint. -/
private lemma coordinateBump_disjoint (n : ℕ) :
    Pairwise (fun i j : Fin n ↦ IsVLDisjoint (coordinateBump i) (coordinateBump j)) := by
  intro i j hij
  refine isVLDisjoint_of_inf_eq_zero (Subtype.ext (funext (fun x ↦ ?_)))
  change min (coordinateBump i x) (coordinateBump j x) = 0
  have hs : |x i| + |x j| ≤ ∑ k, |x k| :=
    Finset.add_le_sum (fun k _ ↦ abs_nonneg (x k))
      (Finset.mem_univ i) (Finset.mem_univ j) hij
  by_cases hi : 2 * x i ≤ ∑ k, |x k|
  · simp [coordinateBump_apply, max_eq_right (sub_nonpos.mpr hi)]
  · have hj : 2 * x j ≤ ∑ k, |x k| := by linarith [le_abs_self (x i), le_abs_self (x j)]
    simp [coordinateBump_apply, max_eq_right (sub_nonpos.mpr hj)]

/-- At the coordinate unit vectors, a bump takes value one on its own vector and zero on the
others. -/
private lemma coordinateBump_single {n : ℕ} (i j : Fin n) :
    coordinateBump i (Pi.single j 1) = if i = j then 1 else 0 := by
  by_cases hij : i = j <;>
    norm_num [coordinateBump_apply, Pi.single_apply, hij, apply_ite]

/-- The coordinatewise lattice of n real coordinates embeds into the free lattice on n
generators. -/
private lemma finite_coordinates_free_embedding (n : ℕ) :
    ∃ T : VecLatHom (Fin n → ℝ) (FVL (Fin n)), Function.Injective T := by
  let L : (Fin n → ℝ) →ₗ[ℝ] FVL (Fin n) :=
    ∑ i, (LinearMap.proj i).smulRight (coordinateBump i)
  have hL : ∀ x, L |x| = |L x| := by
    intro x
    have hb : ∀ i : Fin n, |coordinateBump i| = coordinateBump i :=
      fun i ↦ abs_of_nonneg (posPart_nonneg _)
    simpa [L, hb] using
      (abs_sum_of_pairwise_isVLDisjoint (α := x) (coordinateBump_disjoint n)).symm
  refine ⟨VecLatHom.ofAbs L hL, fun x y h ↦ funext (fun i ↦ ?_)⟩
  change L x = L y at h
  simpa [L, Finset.sum_apply, coordinateBump_single] using
    congrArg (fun f : FVL (Fin n) ↦ f (Pi.single i 1)) h

/-- Every finitely generated sublattice of the finite-range sequences is projective. -/
theorem finiteRangeSequences_locally_projective
    (S : VectorSublattice finiteRangeSequences) (hS : IsFinitelyGenerated S) :
    IsProjective S := by
  let : IsVLArchimedean S := ⟨fun {x y} h k ↦
    IsVLArchimedean.le_zero_of_forall_nsmul_le (fun n ↦ h n k)⟩
  let : FiniteDimensional ℝ S := finiteRange_fg_finiteDimensional S hS
  obtain ⟨n, ⟨e⟩⟩ := (finiteDimensional_iff_latticeIso_pi (X := S)).mp inferInstance
  obtain ⟨T, hT⟩ := finite_coordinates_free_embedding n
  exact ((finitely_generated_archimedean_tfae S hS).out 2 3).mp
    (show ∃ (α : Type) (R : VecLatHom S (FVL α)), Function.Injective R from
      ⟨Fin n, T.comp e.toVecLatHom, hT.comp e.toLinearEquiv.injective⟩)

/-- Every free lattice function depends on finitely many coordinates and has a finite lattice
normal form in them. -/
private lemma fvl_normal_form {α : Type*} (f : FVL α) :
    ∃ (n : ℕ) (a : Fin n → α) (N : LLexpr.NormalForm n),
      ∀ x : α → ℝ, N.eval (fun i ↦ x (a i)) = f x := by
  have hf := f.property
  change f.val ∈ (VectorSublattice.generated (Set.range (FVL.coordinate : α → _)) :
    Set (FVL.FunctionSpace α)) at hf
  rw [LLexpr.generated_eq_iUnion_combinations] at hf
  simp only [Set.mem_iUnion, LLexpr.combinations, Set.mem_range] at hf
  obtain ⟨n, y, e, he⟩ := hf
  choose a ha using fun i ↦ (y i).property
  refine ⟨n, a, e.normalize, fun x ↦ ?_⟩
  rw [LLexpr.normalize_eval, ← he]
  clear he
  induction e <;> simp_all [LLexpr.eval, Function.comp_def, ← ha, FVL.coordinate]

/-- The positivity set of a free lattice function is a finite union of convex sets. -/
private lemma fvl_positive_convex_cover {α : Type*} (f : FVL α) :
    ∃ (k : ℕ) (s : Fin k → Set (α → ℝ)),
      (∀ i, Convex ℝ (s i)) ∧ ∀ x, 0 < f x ↔ ∃ i, x ∈ s i := by
  classical
  obtain ⟨n, a, N, hN⟩ := fvl_normal_form f
  let L (c : Fin n → ℝ) : (α → ℝ) →ₗ[ℝ] ℝ := ∑ j, c j • LinearMap.proj (a j)
  refine ⟨N.pos.coeffs.card, fun i ↦ {x | ∀ d : N.neg.coeffs,
    0 < (L (N.pos.coeffs.equivFin.symm i).val - L d.val) x}, ?_, ?_⟩
  · exact fun i ↦ by
      simpa only [Set.ofPred_forall] using convex_iInter (fun d : N.neg.coeffs ↦
        convex_halfSpace_gt (L (N.pos.coeffs.equivFin.symm i).val - L d.val).isLinear 0)
  · intro x
    simp only [Set.mem_ofPred_eq, ← hN x, LLexpr.NormalForm.eval,
      LLexpr.SupLinearCombination.eval, LinearMap.sub_apply, sub_pos,
      Finset.lt_sup'_iff, Finset.sup'_lt_iff]
    rw [← N.pos.coeffs.equivFin.symm.surjective.exists
      (p := fun c : N.pos.coeffs ↦ ∀ d : N.neg.coeffs, L d.val x < L c.val x)]
    simp [L, Fintype.linearCombination_apply]

/-- For a continuous component of a positive function, the ratio to that function is constant
on each connected positive region. -/
private lemma component_ratio_constant {X : Type*} [TopologicalSpace X]
    (e w : X → ℝ) (he : Continuous e) (hw : Continuous w)
    {s : Set X} (hs : IsPreconnected s) (hpos : ∀ x ∈ s, 0 < e x)
    (hcomp : ∀ x, min (w x) (e x - w x) = 0) {x y : X} (hx : x ∈ s) (hy : y ∈ s) :
    w x / e x = w y / e y := by
  refine hs.constant_of_mapsTo (Set.toFinite ({0, 1} : Set ℝ)).isDiscrete
    (hw.continuousOn.div he.continuousOn (fun z hz ↦ (hpos z hz).ne')) ?_ hx hy
  exact fun z hz ↦ (min_choice (w z) (e z - w z)).elim
    (fun h ↦ Or.inl ((congrArg (· / e z) (h.symm.trans (hcomp z))).trans (zero_div _)))
    (fun h ↦ Or.inr ((congrArg (· / e z)
      (sub_eq_zero.mp (h.symm.trans (hcomp z))).symm).trans (div_self (hpos z hz).ne')))

/-- Finitely many test points detect whether a component of a fixed free-lattice element is
zero. -/
private lemma fvl_component_test_points {α : Type*} (e : FVL α) :
    ∃ (k : ℕ) (p : Fin k → α → ℝ), ∀ w : FVL α,
      0 ≤ w → w ≤ e → w ⊓ (e - w) = 0 → (∀ i, w (p i) = 0) → w = 0 := by
  classical
  obtain ⟨k, s, hs, he⟩ := fvl_positive_convex_cover e
  let p (i : Fin k) : α → ℝ := if h : (s i).Nonempty then h.choose else 0
  have hp (i : Fin k) (hi : (s i).Nonempty) : p i ∈ s i := by
    simpa only [p, dite_eq_left hi] using hi.choose_spec
  refine ⟨k, p, fun w hw hwe hcomp hwp ↦ Subtype.ext (funext (fun x ↦ ?_))⟩
  by_cases hx : 0 < e x
  · obtain ⟨i, hi⟩ := (he x).mp hx
    have hr := component_ratio_constant e w (fvl_continuous e) (fvl_continuous w)
      (hs i).isPreconnected (fun y hy ↦ (he y).mpr ⟨i, hy⟩)
      (fun y ↦ congrArg (fun f : FVL α ↦ f y) hcomp) hi (hp i ⟨x, hi⟩)
    simpa [hwp i, hx.ne'] using hr
  · exact le_antisymm ((hwe x).trans (le_of_not_gt hx)) (hw x)

/-- The constant-one sequence in the lattice of finite-range sequences. -/
private def finiteRangeUnit : finiteRangeSequences :=
  ⟨fun _ ↦ 1, Set.finite_range_const⟩

/-- The coordinate unit sequence in the finite-range sequence lattice. -/
private def finiteRangeBasis (n : ℕ) : finiteRangeSequences :=
  ⟨fun k ↦ if k = n then 1 else 0,
    Set.finite_range_ite Set.finite_range_const Set.finite_range_const⟩

/-- Every coordinate unit sequence is a positive component of the constant-one sequence. -/
private lemma finiteRangeBasis_component (n : ℕ) :
    0 ≤ finiteRangeBasis n ∧ finiteRangeBasis n ≤ finiteRangeUnit ∧
      finiteRangeBasis n ⊓ (finiteRangeUnit - finiteRangeBasis n) = 0 := by
  refine ⟨fun k ↦ ?_, fun k ↦ ?_, Subtype.ext (funext (fun k ↦ ?_))⟩
  all_goals by_cases hk : k = n <;> simp [finiteRangeBasis, finiteRangeUnit, hk]

/-- Distinct coordinate unit sequences are disjoint. -/
private lemma finiteRangeBasis_disjoint {n m : ℕ} (hnm : n ≠ m) :
    finiteRangeBasis n ⊓ finiteRangeBasis m = 0 := by
  refine Subtype.ext (funext (fun k ↦ ?_))
  by_cases hk : k = n <;> by_cases hl : k = m <;> simp_all [finiteRangeBasis]

/-- A free lattice element cannot have infinitely many pairwise disjoint nonzero components. -/
private lemma finite_disjoint_fvl_components {α ι : Type*} (e : FVL α) (w : ι → FVL α)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ e ∧ w i ⊓ (e - w i) = 0 ∧ w i ≠ 0)
    (hdisj : Pairwise (fun i j ↦ w i ⊓ w j = 0)) : Finite ι := by
  classical
  obtain ⟨k, p, hp⟩ := fvl_component_test_points e
  have hex (i : ι) : ∃ j, w i (p j) ≠ 0 := not_forall.mp (fun h ↦
    (hw i).2.2.2 (hp (w i) (hw i).1 (hw i).2.1 (hw i).2.2.1 h))
  choose code hcode using hex
  refine Finite.of_injective code (fun i j hij ↦ ?_)
  by_contra hne
  have hzero : min (w i (p (code i))) (w j (p (code i))) = 0 :=
    congrArg (fun f : FVL α ↦ f (p (code i))) (hdisj hne)
  exact (min_choice (w i (p (code i))) (w j (p (code i)))).elim
    (fun h ↦ hcode i (h.symm.trans hzero))
    (fun h ↦ hcode j ((congrArg (fun c ↦ w j (p c)) hij).symm.trans (h.symm.trans hzero)))

/-- The finite-range sequences do not embed into any free vector lattice. -/
theorem finiteRangeSequences_not_free_embeddable (α : Type u) :
    ¬ ∃ T : VecLatHom finiteRangeSequences (FVL α), Function.Injective T := by
  rintro ⟨T, hT⟩
  refine (finite_disjoint_fvl_components (T finiteRangeUnit) (fun n ↦ T (finiteRangeBasis n))
    (fun n ↦ ?_) (fun n m hnm ↦ ?_)).false
  · obtain ⟨hn, hne, hc⟩ := finiteRangeBasis_component n
    refine ⟨T.map_nonneg hn, T.monotone hne, ?_, fun hz ↦ ?_⟩
    · simpa only [map_inf, map_sub, map_zero] using congrArg T hc
    · have hval := congrArg (fun f : finiteRangeSequences ↦ f.val n)
        (hT (hz.trans (map_zero T).symm))
      norm_num [finiteRangeBasis] at hval
  · simpa only [map_inf, map_zero] using congrArg T (finiteRangeBasis_disjoint hnm)

end VectorLattice.Counterexamples
