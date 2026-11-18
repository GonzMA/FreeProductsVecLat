/-
Authors: Gonzalo Martínez-Fernández
-/

import FreeProducts.BanachLattice.Stability
import BanLat.OrderDense

/-!
# A generated sublattice that is not order dense

In the countable Banach free product of free Banach lattices over the real line, the
modulus of a geometrically weighted series generates a nonzero closed ideal whose
intersection with the algebraically generated vector sublattice is zero. In particular,
that generated sublattice is not order dense.
-/

noncomputable section

universe u

namespace VectorLattice.Counterexamples

/-- The modulus of a geometric series using all the canonical free generators. -/
def geometricElement (P : BanachLattice.FreeProduct (fun _ : ℕ ↦ FBL ℝ)) : P.Carrier :=
  |∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) • P.inclusion n (FBL.of (1 : ℝ))|

/-- The geometrically weighted series of canonical free-product generators is summable. -/
private lemma geometric_series_summable
    (P : BanachLattice.FreeProduct (fun _ : ℕ ↦ FBL ℝ)) :
    Summable (fun n : ℕ ↦ (1 / 2 : ℝ) ^ (n + 1) •
      P.inclusion n (FBL.of (1 : ℝ))) := by
  refine (summable_geometric_two.comp_injective (add_left_injective 1)).of_norm_bounded
    (fun n ↦ ?_)
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity :
    0 ≤ (1 / 2 : ℝ) ^ (n + 1)), Function.comp_apply, FBL.norm_of, norm_one, mul_one] using
    mul_le_mul_of_nonneg_left
      ((P.inclusion n).le_of_opNorm_le (P.inclusion_contractive n) (FBL.of (1 : ℝ)))
      (by positivity : 0 ≤ (1 / 2 : ℝ) ^ (n + 1))

/-- Any uniformly bounded sequence of target vectors determines a lattice homomorphism on the
countable free product of one-generator free Banach lattices. -/
private lemma freeProduct_generator_extension
    (P : BanachLattice.FreeProduct (fun _ : ℕ ↦ FBL ℝ))
    {Y : Type} [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [BanachLattice Y]
    (x : ℕ → Y) (M : ℝ) (hM : 0 ≤ M) (hx : ∀ n, ‖x n‖ ≤ M) :
    ∃ S : P.Carrier →L[ℝ] Y, IsVecLatHom S ∧
      ∀ n, S (P.inclusion n (FBL.of (1 : ℝ))) = x n := by
  let T (n : ℕ) : ℝ →L[ℝ] Y := (ContinuousLinearMap.id ℝ ℝ).smulRight (x n)
  have hnorm : ∀ n, ‖FBL.liftContinuousLinearMap (T n)‖ ≤ M := fun n ↦ by
    simpa [FBL.norm_lift, T, ContinuousLinearMap.norm_smulRight_apply] using hx n
  obtain ⟨S, ⟨hS, hST, -⟩, -⟩ := P.exists_unique_extension Y
    (fun n ↦ FBL.liftContinuousLinearMap (T n)) (fun n ↦ (FBL.lift (T n)).isVecLatHom)
    M hM hnorm
  exact ⟨S, hS, fun n ↦ (hST n _).trans ((FBL.lift_of (T n) 1).trans (one_smul ℝ _))⟩

/-- A continuous lattice homomorphism killing an element also kills its closed principal
ideal. -/
private lemma map_zero_on_closed_principal {X Y : Type*}
    [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [BanachLattice X]
    [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [BanachLattice Y]
    (T : X →L[ℝ] Y) (hT : IsVecLatHom T) (a : X) (ha : T a = 0) :
    ∀ x ∈ (OrderIdeal.principal a).topologicalClosure, T x = 0 := by
  have hker : (OrderIdeal.principal a).toSubmodule ≤ T.ker := by
    change OrderIdeal.principal a ≤ OrderIdeal.ofKerVecLatHom (hT.mk' T)
    rw [OrderIdeal.principal_eq_generated_abs]
    exact OrderIdeal.generated_le (Set.singleton_subset_iff.mpr
      (((hT.mk' T).map_abs a).trans ((congrArg abs ha).trans abs_zero)))
  exact fun _ hx ↦ Submodule.topologicalClosure_minimal _ hker T.isClosed_ker hx

/-- A homomorphism on the free Banach lattice over the real line is determined by the image of
its canonical unit generator. -/
private lemma fbl_real_hom_ext {Y : Type*} [NormedAddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] [BanachLattice Y] (S T : VecLatHom (FBL ℝ) Y)
    (h : S (FBL.of (1 : ℝ)) = T (FBL.of (1 : ℝ))) : S = T := by
  have hof (r : ℝ) : FBL.of r = r • FBL.of (1 : ℝ) :=
    (congrArg FBL.of (smul_eq_mul r 1 |>.trans (mul_one r)).symm).trans
      (map_smul (FBL.ofLinear (E := ℝ)) r 1)
  let L : ℝ →L[ℝ] Y := (ContinuousLinearMap.id ℝ ℝ).smulRight (S (FBL.of (1 : ℝ)))
  refine (FBL.lift_unique L S ?_).trans (FBL.lift_unique L T ?_).symm
  · exact fun r ↦ (congrArg S (hof r)).trans (map_smul S r _)
  · exact fun r ↦ (congrArg T (hof r)).trans
      ((map_smul T r _).trans (congrArg (r • ·) h.symm))

/-- Evaluates a weighted series supported on a finite set and one additional correction
coordinate. -/
private lemma finite_correction_tsum {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (w : ℕ → ℝ) (g : ℕ → Y) (s : Finset ℕ) (m : ℕ) (hm : m ∉ s) (v : Y) :
    (∑' n, w n • (if n ∈ s then g n else if n = m then v else 0)) =
      w m • v + ∑ n ∈ s, w n • g n := by
  rw [tsum_eq_sum (s := insert m s) (fun n hn ↦ ?_)]
  · rw [Finset.sum_insert hm, ite_eq_right hm, ite_eq_left rfl]
    exact congrArg (w m • v + ·)
      (Finset.sum_congr rfl (fun n hn ↦ congrArg (w n • ·) (ite_eq_left hn)))
  · simp only [Finset.mem_insert, not_or] at hn
    simp [hn.1, hn.2]

/-- The geometric element is strictly positive, so its closed principal ideal is nonzero. -/
private lemma geometricElement_pos
    (P : BanachLattice.FreeProduct (fun _ : ℕ ↦ FBL ℝ)) : 0 < geometricElement P := by
  obtain ⟨R, hR, hgen⟩ := freeProduct_generator_extension P (fun _ ↦ (1 : ℝ))
    1 zero_le_one (fun _ ↦ (norm_one : ‖(1 : ℝ)‖ = 1).le)
  have hsum : R (∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) •
      P.inclusion n (FBL.of (1 : ℝ))) = 1 := by
    rw [R.map_tsum (geometric_series_summable P)]
    simp_rw [map_smul, hgen, smul_eq_mul, mul_one, pow_succ]
    norm_num [tsum_mul_right, tsum_geometric_two]
  refine lt_of_le_of_ne (abs_nonneg _) (fun hz ↦ ?_)
  exact one_ne_zero (hsum.symm.trans
    ((congrArg R ((abs_eq_zero_iff_zero _).mp hz.symm)).trans (map_zero R)))

/-- Scalar evaluations separate points of the countable free product through its concrete
realization as the free Banach lattice over the summable real sequences. -/
private lemma countable_product_scalar_separate
    (P : BanachLattice.FreeProduct (fun _ : ℕ ↦ FBL ℝ)) (f : P.Carrier)
    (hf : ∀ R : P.Carrier →L[ℝ] ℝ, IsVecLatHom R → R f = 0) : f = 0 := by
  obtain ⟨e⟩ := BanachLattice.nonempty_fbl_l1_equiv_freeProduct (fun _ : ℕ ↦ ℝ) P
  suffices h : e.symm f = 0 from e.symm.toLinearIsometryEquiv.injective
    (h.trans (map_zero e.symm.toVecLatEquiv.toVecLatHom).symm)
  refine Subtype.ext (Subtype.ext (DFunLike.ext _ _ (fun φ ↦ ?_)))
  let ev : VecLatHom (FBL (lp (fun _ : ℕ ↦ ℝ) 1)) ℝ :=
    { toFun := fun g ↦ g φ
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      map_sup' := fun _ _ ↦ rfl
      map_inf' := fun _ _ ↦ rfl }
  exact hf ⟨(ev.comp e.symm.toVecLatEquiv.toVecLatHom).toLinearMap,
    Positive.continuous (Positive.monotone_iff.mp
      (ev.comp e.symm.toVecLatEquiv.toVecLatHom).monotone)⟩
        (ev.comp e.symm.toVecLatEquiv.toVecLatHom).isVecLatHom

/-- Finitely prescribed scalar coordinates and one correction coordinate define a bounded
scalar evaluation on the countable free product. -/
private lemma finite_scalar_extension
    (P : BanachLattice.FreeProduct (fun _ : ℕ ↦ FBL ℝ))
    (s : Finset ℕ) (m : ℕ) (α : ℕ → ℝ) (v : ℝ) :
    ∃ R : P.Carrier →L[ℝ] ℝ, IsVecLatHom R ∧ ∀ n,
      R (P.inclusion n (FBL.of (1 : ℝ))) = if n ∈ s then α n else if n = m then v else 0 := by
  refine freeProduct_generator_extension P _ (max (∑ n ∈ s, ‖α n‖) ‖v‖)
    ((norm_nonneg v).trans (le_max_right _ _)) ?_
  intro n
  split_ifs with hn hnm
  · exact (Finset.single_le_sum (fun i _ ↦ norm_nonneg (α i)) hn).trans (le_max_left _ _)
  · exact le_max_right _ _
  · exact (norm_zero : ‖(0 : ℝ)‖ = 0).le.trans ((norm_nonneg v).trans (le_max_right _ _))

/-- Arbitrary finite scalar coordinates can be completed by one unused coordinate to a
bounded evaluation in the zero set of the geometric element. -/
private lemma finite_scalar_zero_set
    (P : BanachLattice.FreeProduct (fun _ : ℕ ↦ FBL ℝ)) (s : Finset ℕ) (α : ℕ → ℝ) :
    ∃ R : P.Carrier →L[ℝ] ℝ, IsVecLatHom R ∧
      (∀ n ∈ s, R (P.inclusion n (FBL.of (1 : ℝ))) = α n) ∧ R (geometricElement P) = 0 := by
  let m := s.sup id + 1
  have hm : m ∉ s := fun hm ↦ (Nat.not_succ_le_self _) (Finset.le_sup (f := id) hm)
  let v := -(((1 / 2 : ℝ) ^ (m + 1))⁻¹ • ∑ n ∈ s, (1 / 2 : ℝ) ^ (n + 1) • α n)
  obtain ⟨R, hR, hgen⟩ := finite_scalar_extension P s m α v
  refine ⟨R, hR, fun n hn ↦ (hgen n).trans (ite_eq_left hn), ?_⟩
  change (hR.mk' R) |∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) •
    P.inclusion n (FBL.of (1 : ℝ))| = 0
  rw [(hR.mk' R).map_abs]
  change |R (∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) • P.inclusion n (FBL.of (1 : ℝ)))| = 0
  rw [R.map_tsum (geometric_series_summable P)]
  simp_rw [map_smul, hgen]
  rw [finite_correction_tsum _ _ s m hm v]
  simp [v]

/-- A nonzero closed principal ideal can meet the generated sublattice only at zero. -/
theorem countable_freeProduct_closed_ideal_disjoint
    (P : BanachLattice.FreeProduct (fun _ : ℕ ↦ FBL ℝ)) :
    0 < geometricElement P ∧
      ∀ f ∈ P.generated,
        f ∈ (OrderIdeal.principal (geometricElement P)).topologicalClosure → f = 0 := by
  refine ⟨geometricElement_pos P, fun f hf hcl ↦ ?_⟩
  apply countable_product_scalar_separate P f
  intro R hR
  obtain ⟨n, i, x, e, he⟩ := P.exists_expression ⟨f, hf⟩
  obtain ⟨S, hS, hcoord, hzero⟩ := finite_scalar_zero_set P (Finset.univ.image i)
    (fun k ↦ R (P.inclusion k (FBL.of (1 : ℝ))))
  have hSR (j : Fin n) : S (P.inclusion (i j) (x j)) = R (P.inclusion (i j) (x j)) :=
    DFunLike.congr_fun (fbl_real_hom_ext
      ((hS.mk' S).comp ((P.inclusion_isVecLatHom (i j)).mk' (P.inclusion (i j))))
      ((hR.mk' R).comp ((P.inclusion_isVecLatHom (i j)).mk' (P.inclusion (i j))))
      (hcoord (i j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩))) (x j)
  have hSf : S f = R f := (congrArg S he).trans
    ((LLexpr.map_eval (hS.mk' S) _ e).trans
      ((congrArg (fun a ↦ LLexpr.eval a e) (funext hSR)).trans
        ((LLexpr.map_eval (hR.mk' R) _ e).symm.trans (congrArg R he).symm)))
  exact hSf.symm.trans (map_zero_on_closed_principal S hS _ hzero f hcl)

/-- The generated sublattice of a countable Banach free product need not be order dense. -/
theorem countable_freeProduct_not_orderDense
    (P : BanachLattice.FreeProduct (fun _ : ℕ ↦ FBL ℝ)) :
    ¬ P.generated.IsOrderDense := by
  intro hdense
  obtain ⟨hpos, hdisj⟩ := countable_freeProduct_closed_ideal_disjoint P
  obtain ⟨f, hf, hfp, hfle⟩ := hdense hpos
  exact hfp.ne' (hdisj f hf (subset_closure
    ((OrderIdeal.principal (geometricElement P)).solid
      (OrderIdeal.self_mem_principal _) hfp.le hfle)))

end VectorLattice.Counterexamples
