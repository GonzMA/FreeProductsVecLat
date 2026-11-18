/-
Authors: Gonzalo Martínez-Fernández
-/

import BanLat.Free.FVL
import BanLat.AMSpace.Characters
import BanLat.Convergences.Uniform
import BanLat.Quotient
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Module.ULift

/-!
# Free vector lattices as piecewise-linear functions

Continuous, positively homogeneous finite linear selectors are precisely the functions
in a finitely generated free vector lattice. Evaluation, substitution, finite generation
and quotient helpers support the cone constructions.
-/

universe u

namespace VectorLattice.ConeRepresentation

open scoped Topology

/-- Near a point, a continuous selector can only choose branches that agree with it
at that point. -/
private lemma locally_active {k : ℕ} (f : ℝ → ℝ) (g : Fin k → ℝ → ℝ)
    (hf : Continuous f) (hg : ∀ i, Continuous (g i)) (x : ℝ) :
    ∀ᶠ y in 𝓝 x, ∀ i, f y = g i y → f x = g i x := by
  apply Filter.eventually_all.mpr
  intro i
  by_cases h : f x = g i x
  · exact Filter.Eventually.of_forall (fun _ _ ↦ h)
  · have hnear : ∀ᶠ y in 𝓝 x, f y ≠ g i y := (isOpen_ne_fun hf (hg i)).mem_nhds h
    exact hnear.mono (fun _ hy heq ↦ (hy heq).elim)

/-- A continuous choice among finitely many affine functions has one branch lying above its left
endpoint value and below its right endpoint value. -/
private lemma affine_selection_pair {k : ℕ} (a b : Fin k → ℝ) (f : ℝ → ℝ)
    (hf : Continuous f)
    (hsel : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ i, f t = (1 - t) * a i + t * b i) :
    ∃ i, f 0 ≤ a i ∧ b i ≤ f 1 := by
  by_contra hnot
  have hbad (i : Fin k) (hi : f 0 ≤ a i) : f 1 < b i :=
    lt_of_not_ge (fun h ↦ hnot ⟨i, hi, h⟩)
  let g (i : Fin k) (t : ℝ) := (1 - t) * a i + t * b i
  have hg (i : Fin k) : Continuous (g i) := by fun_prop
  have hloc : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, f t = g i t → f 0 = g i 0 :=
    (locally_active f g hf hg 0).filter_mono nhdsWithin_le_nhds
  obtain ⟨s, hs, hactive⟩ :=
    (Filter.Eventually.and (Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)) hloc).exists
  let F (t : ℝ) := (f t - (1 - t) * f 0) / t
  have hFs : f 1 < F s := by
    obtain ⟨i, hi⟩ := hsel s ⟨hs.1.le, hs.2.le⟩
    have ha : f 0 = a i := by
      simpa only [g, sub_zero, one_mul, zero_mul, add_zero] using hactive i hi
    have hb := hbad i ha.le
    change f 1 < (f s - (1 - s) * f 0) / s
    rw [lt_div_iff₀ hs.1, hi, ha]
    nlinarith [mul_pos hs.1 (sub_pos.mpr hb)]
  have hF : ContinuousOn F (Set.Icc s 1) := by
    apply (hf.continuousOn.sub
      ((continuous_const.sub continuous_id).mul continuous_const).continuousOn).div
      continuous_id.continuousOn
    exact fun t ht ↦ ne_of_gt (hs.1.trans_le ht.1)
  obtain ⟨c, hc, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr hs.2.le) hF
  have hFc : F c ≤ f 1 := by
    simpa only [Set.mem_ofPred_eq, F, sub_self, zero_mul, sub_zero, div_one] using
      hmin ⟨hs.2.le, le_rfl⟩
  have hsc : s < c := lt_of_le_of_ne hc.1 (fun h ↦ (not_le_of_gt hFs) (h ▸ hFc))
  have hlocc : ∀ᶠ t in 𝓝[<] c, ∀ i, f t = g i t → f c = g i c :=
    (locally_active f g hf hg c).filter_mono nhdsWithin_le_nhds
  obtain ⟨t, ht, htactive⟩ := (Filter.Eventually.and (Ioo_mem_nhdsLT hsc) hlocc).exists
  have htpos : 0 < t := hs.1.trans ht.1
  have hcpos : 0 < c := hs.1.trans hsc
  obtain ⟨i, hi⟩ := hsel t ⟨htpos.le, ht.2.le.trans hc.2⟩
  have hic : f c = (1 - c) * a i + c * b i := htactive i hi
  have hmin' : F c ≤ F t := hmin ⟨ht.1.le, ht.2.le.trans hc.2⟩
  have hai : f 0 ≤ a i := by
    change (f c - (1 - c) * f 0) / c ≤ (f t - (1 - t) * f 0) / t at hmin'
    rw [div_le_div_iff₀ hcpos htpos, hi, hic] at hmin'
    by_contra hn
    nlinarith [mul_pos (sub_pos.mpr ht.2) (sub_pos.mpr (lt_of_not_ge hn))]
  have hb := hbad i hai
  have hbound : (1 - c) * a i + c * b i - (1 - c) * f 0 ≤ f 1 * c :=
    (div_le_iff₀ hcpos).mp (by simpa only [F, hic] using hFc)
  nlinarith [mul_nonneg (sub_nonneg.mpr hc.2) (sub_nonneg.mpr hai),
    mul_pos hcpos (sub_pos.mpr hb)]

/-- For two points, some selected linear form bounds the function from above at the first point
and from below at the second. -/
private lemma linear_selection_pair {n k : ℕ} (forms : Fin k → (Fin n → ℝ) →ₗ[ℝ] ℝ)
    (f : (Fin n → ℝ) → ℝ) (hf : Continuous f) (hsel : ∀ x, ∃ i, f x = forms i x)
    (x y : Fin n → ℝ) : ∃ i, f x ≤ forms i x ∧ forms i y ≤ f y := by
  let p (t : ℝ) := (1 - t) • x + t • y
  have hp : Continuous p := by fun_prop
  have hs (t : ℝ) (_ : t ∈ Set.Icc (0 : ℝ) 1) :
      ∃ i, (f ∘ p) t = (1 - t) * forms i x + t * forms i y := by
    obtain ⟨i, hi⟩ := hsel (p t)
    exact ⟨i, hi.trans (by simp only [p, map_add, map_smul, smul_eq_mul])⟩
  simpa only [Function.comp_apply, p, sub_zero, one_smul, zero_smul, add_zero, sub_self,
    zero_add] using affine_selection_pair (fun i ↦ forms i x) (fun i ↦ forms i y) (f ∘ p)
      (hf.comp hp) hs

/-- At each point, a finite infimum of the given functions touches the target function
from below. -/
private lemma finite_inf_support {n k : ℕ} (g : Fin k → (Fin n → ℝ) → ℝ)
    (f : (Fin n → ℝ) → ℝ)
    (hpair : ∀ x y, ∃ i, f x ≤ g i x ∧ g i y ≤ f y) (x : Fin n → ℝ) :
    ∃ h ∈ infClosure (Set.range g), h ≤ f ∧ h x = f x := by
  classical
  let s := Finset.univ.filter (fun i ↦ f x ≤ g i x)
  have hs : s.Nonempty := by
    obtain ⟨i, hi, _⟩ := hpair x x
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  let h := s.inf' hs g
  have hle : h ≤ f := by
    intro y
    obtain ⟨i, hi, hiy⟩ := hpair x y
    exact ((Finset.inf'_le g (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)) y).trans hiy
  refine ⟨h, finsetInf'_mem_infClosure hs (fun i _ ↦ ⟨i, rfl⟩), hle, le_antisymm (hle x) ?_⟩
  change f x ≤ s.inf' hs g x
  rw [Finset.inf'_apply]
  exact Finset.le_inf' hs _ (fun i hi ↦ (Finset.mem_filter.mp hi).2)

/-- The pairwise comparison property expresses the target using finite lattice operations, placing
it in the given sublattice. -/
private lemma finite_lattice_envelope {n k : ℕ}
    (S : VectorSublattice ((Fin n → ℝ) → ℝ)) (g : Fin k → (Fin n → ℝ) → ℝ)
    (hg : ∀ i, g i ∈ S) (f : (Fin n → ℝ) → ℝ)
    (hpair : ∀ x y, ∃ i, f x ≤ g i x ∧ g i y ≤ f y) : f ∈ S := by
  classical
  let s := {h | h ∈ infClosure (Set.range g) ∧ h ≤ f}
  have hs : s.Finite := (Set.finite_range g).infClosure.subset (fun _ h ↦ h.1)
  have hlocal (x : Fin n → ℝ) : ∃ h ∈ s, h x = f x := by
    obtain ⟨h, hh, hle, heq⟩ := finite_inf_support g f hpair x
    exact ⟨h, ⟨hh, hle⟩, heq⟩
  have hne : hs.toFinset.Nonempty := by
    obtain ⟨h, hh, _⟩ := hlocal 0
    exact ⟨h, hs.mem_toFinset.mpr hh⟩
  let H := hs.toFinset.sup' hne id
  have hH : H = f := by
    apply le_antisymm
    · exact Finset.sup'_le hne id (fun h hh ↦ (hs.mem_toFinset.mp hh).2)
    · intro x
      obtain ⟨h, hh, heq⟩ := hlocal x
      exact heq ▸ (Finset.le_sup' id (hs.mem_toFinset.mpr hh)) x
  rw [← hH]
  apply S.isSublattice.supClosed.finsetSup'_mem hne
  intro h hh
  exact infClosure_min (Set.range_subset_iff.mpr hg) S.isSublattice.infClosed
    (hs.mem_toFinset.mp hh).1

/-- Every real linear form belongs to the free vector lattice generated by the coordinate
functions. -/
private lemma linear_form_mem {n : ℕ} (l : (Fin n → ℝ) →ₗ[ℝ] ℝ) :
    (l : (Fin n → ℝ) → ℝ) ∈ FVL.concreteSublattice (Fin n) := by
  classical
  let c (i : Fin n) := l (fun j ↦ if i = j then 1 else 0)
  have heq : (l : (Fin n → ℝ) → ℝ) = ∑ i, c i • FVL.coordinate i := by
    funext x
    simpa only [Finset.sum_apply, Pi.smul_apply, FVL.coordinate, smul_eq_mul, mul_comm] using
      l.pi_apply_eq_sum_univ x
  rw [heq]
  exact (FVL.concreteSublattice (Fin n)).toSubmodule.sum_mem (fun i _ ↦
    (FVL.concreteSublattice (Fin n)).smul_mem _
      (VectorSublattice.subset_generated _ ⟨i, rfl⟩))

/-- A continuous function that chooses among finitely many linear forms belongs to the concrete
free vector lattice. -/
private lemma linear_selection_mem {n k : ℕ} (forms : Fin k → (Fin n → ℝ) →ₗ[ℝ] ℝ)
    (f : (Fin n → ℝ) → ℝ) (hf : Continuous f) (hsel : ∀ x, ∃ i, f x = forms i x) :
    f ∈ FVL.concreteSublattice (Fin n) := by
  exact finite_lattice_envelope _ (fun i ↦ forms i) (fun i ↦ linear_form_mem (forms i)) f
    (linear_selection_pair forms f hf hsel)

/-- Evaluating a finite vector lattice expression gives a continuous function of its coordinates. -/
private lemma expression_continuous {n : ℕ} (a : LLexpr n) :
    Continuous (fun x : Fin n → ℝ ↦ LLexpr.eval x a) := by
  exact a.rec continuous_const (fun i ↦ continuous_apply i)
    (fun _ _ hf hg ↦ hf.add hg) (fun r _ hf ↦ hf.const_smul r)
    (fun _ _ hf hg ↦ hf.sup hg) (fun _ _ hf hg ↦ hf.inf hg)

/-- Evaluation of a vector lattice expression commutes with multiplication of all coordinates by a
nonnegative scalar. -/
private lemma expression_homogeneous {n : ℕ} (a : LLexpr n) (r : ℝ) (hr : 0 ≤ r)
    (x : Fin n → ℝ) : LLexpr.eval (r • x) a = r * LLexpr.eval x a := by
  let T : VecLatHom ℝ ℝ := VecLatHom.ofAbs (r • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) (by
    intro y
    change r * |y| = |r * y|
    rw [abs_mul, abs_of_nonneg hr])
  exact (LLexpr.map_eval T x a).symm

/-- A finite vector lattice expression agrees pointwise with one of finitely many linear forms. -/
private lemma expression_finite_forms {n : ℕ} (a : LLexpr n) :
    ∃ (k : ℕ) (forms : Fin k → (Fin n → ℝ) →ₗ[ℝ] ℝ),
      ∀ x, ∃ i, LLexpr.eval x a = forms i x := by
  classical
  let N := a.normalize
  let I := ↥N.pos.coeffs × ↥N.neg.coeffs
  let L (c : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ i, c i • LinearMap.proj i
  let forms (j : I) := L j.1.val - L j.2.val
  refine ⟨Fintype.card I, fun i ↦ forms ((Fintype.equivFin I).symm i), ?_⟩
  intro x
  obtain ⟨p, hp, hep⟩ := Finset.exists_mem_eq_sup' N.pos.nonempty (Fintype.linearCombination ℝ x)
  obtain ⟨q, hq, heq⟩ := Finset.exists_mem_eq_sup' N.neg.nonempty (Fintype.linearCombination ℝ x)
  refine ⟨(Fintype.equivFin I) (⟨p, hp⟩, ⟨q, hq⟩), ?_⟩
  change LLexpr.eval x a = forms ((Fintype.equivFin I).symm
    ((Fintype.equivFin I) (⟨p, hp⟩, ⟨q, hq⟩))) x
  rw [Equiv.symm_apply_apply, ← LLexpr.normalize_eval x a]
  change N.pos.eval x - N.neg.eval x = (L p - L q) x
  rw [LLexpr.SupLinearCombination.eval, LLexpr.SupLinearCombination.eval, hep, heq]
  simp [L, Fintype.linearCombination_apply]

/-- Evaluating an expression in coordinate functions and then at a point equals evaluating it
directly on that point's coordinates. -/
private lemma expression_apply {n : ℕ} (a : LLexpr n) (x : Fin n → ℝ) :
    LLexpr.eval FVL.coordinate a x = LLexpr.eval x a := by
  induction a <;> simp_all [LLexpr.eval, FVL.coordinate]

/-- Concrete free vector lattice functions are continuous, positively homogeneous, and pointwise
selections of finitely many linear forms. -/
private lemma free_function_properties {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hf : f ∈ FVL.concreteSublattice (Fin n)) :
    Continuous f ∧ (∀ r : ℝ, 0 ≤ r → ∀ x, f (r • x) = r * f x) ∧
      ∃ (k : ℕ) (forms : Fin k → (Fin n → ℝ) →ₗ[ℝ] ℝ),
        ∀ x, ∃ i, f x = forms i x := by
  change f ∈ (VectorSublattice.generated (Set.range (FVL.coordinate : Fin n → _)) : Set _) at hf
  rw [LLexpr.generated_range_eq_combinations] at hf
  obtain ⟨a, rfl⟩ := hf
  have heq : LLexpr.eval (FVL.coordinate : Fin n → _) a =
      (fun x : Fin n → ℝ ↦ LLexpr.eval x a) := funext (expression_apply a)
  rw [heq]
  exact ⟨expression_continuous a, expression_homogeneous a, expression_finite_forms a⟩

/-- Free vector lattice functions are exactly continuous positively homogeneous
functions that select pointwise from finitely many real linear forms. -/
theorem mem_free_iff {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    f ∈ FVL.concreteSublattice (Fin n) ↔
      Continuous f ∧
      (∀ (r : ℝ), 0 ≤ r → ∀ x, f (r • x) = r * f x) ∧
      ∃ (k : ℕ) (forms : Fin k → (Fin n → ℝ) →ₗ[ℝ] ℝ),
        ∀ x, ∃ i, f x = forms i x := by
  constructor
  · exact free_function_properties f
  · rintro ⟨hf, _, k, forms, hsel⟩
    exact linear_selection_mem forms f hf hsel

/-- The scalar free extension at a coordinate tuple is evaluation at that tuple. -/
lemma free_lift_apply {α : Type*} (x : α → ℝ) (f : FVL α) :
    FVL.lift x f = f x := by
  let ev : VecLatHom (FVL α) ℝ :=
    { toFun := fun g ↦ g x
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      map_sup' := fun _ _ ↦ rfl
      map_inf' := fun _ _ ↦ rfl }
  exact DFunLike.congr_fun (FVL.lift_unique x ev (fun _ ↦ rfl)).symm f

/-- Free substitution evaluates a function at the tuple of substituted free functions. -/
lemma free_substitution_apply {n m : ℕ} (g : Fin n → FVL (Fin m))
    (f : FVL (Fin n)) (x : Fin m → ℝ) :
    FVL.lift g f x = f (fun i ↦ g i x) := by
  have h : (FVL.lift x).comp (FVL.lift g) = FVL.lift (fun i ↦ g i x) := by
    apply FVL.hom_ext
    intro i
    simp only [VecLatHom.comp_apply, FVL.lift_of, free_lift_apply]
  exact (free_lift_apply x (FVL.lift g f)).symm.trans
    ((DFunLike.congr_fun h f).trans (free_lift_apply _ f))

/-- Relabeling free generators acts on functions by precomposing the coordinate tuple with the
index map. -/
lemma free_map_apply {n m : ℕ} (a : Fin n → Fin m) (f : FVL (Fin n))
    (x : Fin m → ℝ) : FVL.map a f x = f (x ∘ a) := by
  have h : (FVL.lift x).comp (FVL.map a) = FVL.lift (x ∘ a) := by
    apply FVL.hom_ext
    exact fun i ↦ by simp [VecLatHom.comp_apply, FVL.map_of, FVL.lift_of]
  exact (free_lift_apply x (FVL.map a f)).symm.trans
    ((DFunLike.congr_fun h f).trans (free_lift_apply (x ∘ a) f))

end VectorLattice.ConeRepresentation

namespace VectorLattice

variable (X : Type u) [AddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [VectorLattice X]

open ConeRepresentation

/-- Changing the type universe preserves compatibility of addition with the lattice order. -/
private instance uliftOrderedAddMonoid {A : Type*} [AddCommGroup A] [Lattice A]
    [IsOrderedAddMonoid A] : IsOrderedAddMonoid (ULift.{u} A) where
  add_le_add_left a b hab c :=
    show a.down + c.down ≤ b.down + c.down from
      IsOrderedAddMonoid.add_le_add_left a.down b.down hab c.down

/-- Transports a vector lattice structure to the same elements in a larger type universe. -/
private noncomputable instance uliftVectorLattice {A : Type*} [AddCommGroup A] [Lattice A]
    [IsOrderedAddMonoid A] [VectorLattice A] : VectorLattice (ULift.{u} A) where
  smul_le_smul_of_nonneg_left := fun {r} hr {a b} hab ↦
    show r • a.down ≤ r • b.down from
      smul_le_smul_of_nonneg_left (show a.down ≤ b.down from hab) hr

/-- The universe-lifted lattice is equivalent to the original vector lattice. -/
noncomputable def uliftEquiv (A : Type*) [AddCommGroup A] [Lattice A]
    [IsOrderedAddMonoid A] [VectorLattice A] : VecLatEquiv (ULift.{u} A) A :=
  { ULift.moduleEquiv with
    map_sup' := fun _ _ ↦ rfl
    map_inf' := fun _ _ ↦ rfl }

/-- A lattice admitting an embedding into an Archimedean lattice is itself Archimedean. -/
lemma archimedean_of_injective {A B : Type*}
    [AddCommGroup A] [Lattice A] [IsOrderedAddMonoid A] [VectorLattice A]
    [AddCommGroup B] [Lattice B] [IsOrderedAddMonoid B] [VectorLattice B]
    [IsVLArchimedean B] (T : VecLatHom A B) (hT : Function.Injective T) : IsVLArchimedean A := by
  refine ⟨fun {x y} h ↦ T.le_of_map_le hT ?_⟩
  rw [map_zero]
  apply IsVLArchimedean.le_zero_of_forall_nsmul_le (y := T y)
  intro n
  simpa only [map_nsmul] using T.monotone (h n)

/-- Vector lattice equivalences preserve and reflect the Archimedean property. -/
lemma archimedean_equiv_iff {A B : Type*}
    [AddCommGroup A] [Lattice A] [IsOrderedAddMonoid A] [VectorLattice A]
    [AddCommGroup B] [Lattice B] [IsOrderedAddMonoid B] [VectorLattice B]
    (e : VecLatEquiv A B) : IsVLArchimedean A ↔ IsVLArchimedean B := by
  constructor
  · intro h
    let := h
    exact archimedean_of_injective e.symm.toVecLatHom e.toLinearEquiv.symm.injective
  · intro h
    let := h
    exact archimedean_of_injective e.toVecLatHom e.toLinearEquiv.injective

/-- Homomorphisms agreeing on a finite generating family agree everywhere. -/
lemma hom_ext_finite_generators {Y : Type*} [AddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] [VectorLattice Y] {n : ℕ} (g : Fin n → X)
    (hg : VectorSublattice.generated (Set.range g) = ⊤) (S T : VecLatHom X Y)
    (h : ∀ i, S (g i) = T (g i)) : S = T := by
  apply DFunLike.ext
  intro x
  obtain ⟨e, rfl⟩ : ∃ e : LLexpr n, LLexpr.eval g e = x :=
    (LLexpr.generated_range_eq_combinations g).le (hg.symm ▸ VectorSublattice.mem_top)
  rw [LLexpr.map_eval, LLexpr.map_eval]
  exact congrArg (fun v : Fin n → Y ↦ LLexpr.eval v e) (funext h)

/-- A generating family induces a surjective homomorphism from its free vector lattice. -/
lemma lift_surjective_of_generators {n : ℕ} (g : Fin n → X)
    (hg : VectorSublattice.generated (Set.range g) = ⊤) : Function.Surjective (FVL.lift g) := by
  intro x
  obtain ⟨e, rfl⟩ : ∃ e : LLexpr n, LLexpr.eval g e = x :=
    (LLexpr.generated_range_eq_combinations g).le (hg.symm ▸ VectorSublattice.mem_top)
  refine ⟨LLexpr.eval FVL.of e, ?_⟩
  rw [LLexpr.map_eval]
  simp only [FVL.lift_of]

/-- The images of the free generators generate the target of a surjective free-lattice
homomorphism. -/
lemma generated_range_of_surjective_free {n : ℕ} (T : VecLatHom (FVL (Fin n)) X)
    (hT : Function.Surjective T) :
    VectorSublattice.generated (Set.range (fun i ↦ T (FVL.of i))) = ⊤ := by
  let G := VectorSublattice.generated (Set.range (fun i ↦ T (FVL.of i)))
  let g (i : Fin n) : G := ⟨T (FVL.of i), VectorSublattice.subset_generated _ ⟨i, rfl⟩⟩
  have h : G.subtype.comp (FVL.lift g) = T :=
    FVL.hom_ext (fun i ↦ by simp only [VecLatHom.comp_apply, FVL.lift_of]; rfl)
  apply le_antisymm (fun _ _ ↦ VectorSublattice.mem_top)
  intro x _
  obtain ⟨f, rfl⟩ := hT x
  exact (DFunLike.congr_fun h f) ▸ (FVL.lift g f).property

/-- A surjective lattice homomorphism identifies its target with the quotient by its kernel
ideal. -/
lemma quotient_ker_equiv {A B : Type*}
    [AddCommGroup A] [Lattice A] [IsOrderedAddMonoid A] [VectorLattice A]
    [AddCommGroup B] [Lattice B] [IsOrderedAddMonoid B] [VectorLattice B]
    (T : VecLatHom A B) (hT : Function.Surjective T) :
    ∃ e : VecLatEquiv (A ⧸ (OrderIdeal.ofKerVecLatHom T).toSubmodule) B,
      ∀ x, e ((OrderIdeal.ofKerVecLatHom T).mkQ x) = T x := by
  let e := T.toLinearMap.quotKerEquivOfSurjective hT
  refine ⟨{ e with map_sup' := ?_, map_inf' := ?_ }, fun _ ↦ rfl⟩
  · intro x y
    obtain ⟨a, rfl⟩ := (OrderIdeal.ofKerVecLatHom T).toSubmodule.mkQ_surjective x
    obtain ⟨b, rfl⟩ := (OrderIdeal.ofKerVecLatHom T).toSubmodule.mkQ_surjective y
    exact map_sup T a b
  · intro x y
    obtain ⟨a, rfl⟩ := (OrderIdeal.ofKerVecLatHom T).toSubmodule.mkQ_surjective x
    obtain ⟨b, rfl⟩ := (OrderIdeal.ofKerVecLatHom T).toSubmodule.mkQ_surjective y
    exact map_inf T a b

end VectorLattice
