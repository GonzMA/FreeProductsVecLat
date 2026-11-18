/-
Authors: Gonzalo Martínez-Fernández
-/

import FreeProducts.AVLvsVL.Coproducts.Models
import FreeProducts.AVLvsVL.Classical.PolyhedralGeometry

/-!
# When the ordinary coproduct is Archimedean

The two coproduct models agree exactly when the factor-relation ideal equals the
vanishing ideal of the product cone. A polyhedral covering condition characterizes this
equality; it holds whenever the first cone is polyhedral.
-/

universe u

namespace VectorLattice

variable (X : Type u) [AddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [VectorLattice X]

open ConeRepresentation

/-- When the relation quotient is Archimedean, its cone-product representation intertwines
the quotient map with restriction to the product cone. -/
private lemma archimedean_cone_product_quotient_equiv {n m : ℕ}
    (C : ClosedCone n) (D : ClosedCone m) [IsVLArchimedean (ConeProductQuotient C D)] :
    ∃ e : VecLatEquiv (ConeProductQuotient C D) (ConeFunctions (productCone C D)),
      e.toVecLatHom.comp (productRelationsIdeal C D).mkQVecLatHom =
        FVL.lift (coordinate (productCone C D)) := by
  obtain ⟨A, B, hA, hB⟩ := cone_product_inclusions C D
  let P : ArchimedeanFreeProduct (binaryFamily (ConeFunctions C) (ConeFunctions D)) :=
    { Carrier := ConeProductQuotient C D
      inclusion := fun | ⟨false⟩ => A | ⟨true⟩ => B
      universal := by
        exact fun Z _ _ _ _ _ T ↦
          let ⟨R, hR, hu⟩ := cone_product_universal C D A B hA hB (T ⟨false⟩) (T ⟨true⟩)
          ⟨R, (fun
            | ⟨false⟩, x => DFunLike.congr_fun hR.1 x
            | ⟨true⟩, x => DFunLike.congr_fun hR.2 x),
            fun S hS ↦ hu S ⟨DFunLike.ext _ _ (hS ⟨false⟩),
              DFunLike.ext _ _ (hS ⟨true⟩)⟩⟩ }
  obtain ⟨e, hC, hD⟩ := P.exists_cone_product_equiv C D VecLatEquiv.refl VecLatEquiv.refl
  refine ⟨e, FVL.hom_ext (Fin.addCases ?_ ?_)⟩
  · intro i
    simp only [VecLatHom.comp_apply, OrderIdeal.mkQVecLatHom_apply, ← hA, FVL.lift_of]
    exact Subtype.ext (funext (hC (coordinate C i)))
  · intro j
    simp only [VecLatHom.comp_apply, OrderIdeal.mkQVecLatHom_apply, ← hB, FVL.lift_of]
    exact Subtype.ext (funext (hD (coordinate D j)))

/-- If the product-relation quotient is Archimedean, every function vanishing on the product
cone is already a product relation. -/
private lemma vanishing_le_of_archimedean_product_quotient {n m : ℕ}
    (C : ClosedCone n) (D : ClosedCone m) [IsVLArchimedean (ConeProductQuotient C D)] :
    vanishingIdeal (productCone C D) ≤ productRelationsIdeal C D := by
  obtain ⟨e, he⟩ := archimedean_cone_product_quotient_equiv C D
  intro f hf
  apply (Submodule.Quotient.mk_eq_zero (productRelationsIdeal C D).toSubmodule).mp
  apply e.toLinearEquiv.injective
  rw [map_zero]
  exact (DFunLike.congr_fun he f).trans
    (Subtype.ext (funext (fun x ↦ (coneRestriction_apply (productCone C D) f x).trans
      ((mem_vanishingIdeal _ _).mp hf _ x.property))))

/-- The product-relation quotient is Archimedean exactly when its relation ideal contains the
vanishing ideal of the product cone. -/
private lemma archimedean_product_quotient_iff {n m : ℕ} (C : ClosedCone n) (D : ClosedCone m) :
    IsVLArchimedean (ConeProductQuotient C D) ↔
      vanishingIdeal (productCone C D) ≤ productRelationsIdeal C D := by
  constructor
  · intro h
    let := h
    exact vanishing_le_of_archimedean_product_quotient C D
  · intro h
    have hJ : productRelationsIdeal C D = vanishingIdeal (productCone C D) :=
      le_antisymm (productRelationsIdeal_le_vanishingIdeal C D) h
    obtain ⟨e, _⟩ := cone_quotient_equiv (productCone C D)
    have he : IsVLArchimedean
        (FVL (Fin (n + m)) ⧸ (vanishingIdeal (productCone C D)).toSubmodule) :=
      archimedean_of_injective e.toVecLatHom e.toLinearEquiv.injective
    have htransport (J : OrderIdeal (FVL (Fin (n + m))))
        (hJ : J = vanishingIdeal (productCone C D)) :
        IsVLArchimedean (FVL (Fin (n + m)) ⧸ J.toSubmodule) := by
      subst J
      exact he
    exact htransport _ hJ

end VectorLattice

namespace VectorLattice.ConeRepresentation

/-- Every open polyhedral cone avoiding the product is covered by
polyhedral cylinders avoiding the respective factors. -/
def HasPolyhedralCover {n m : ℕ} (C : ClosedCone n) (D : ClosedCone m) : Prop :=
  ∀ W : Set (Fin (n + m) → ℝ), IsOpenPolyhedralCone W →
    Disjoint W (productCone C D).carrier →
    ∃ (U : Set (Fin n → ℝ)) (V : Set (Fin m → ℝ)),
      IsOpenPolyhedralCone U ∧ IsOpenPolyhedralCone V ∧
      Disjoint U C.carrier ∧ Disjoint V D.carrier ∧
      ∀ z ∈ W,
        (fun i : Fin n ↦ z (i.castAdd m)) ∈ U ∨
        (fun j : Fin m ↦ z (j.natAdd n)) ∈ V

/-- If all functions vanishing on the product cone are product relations, the cones satisfy
the polyhedral covering condition. -/
private lemma polyhedralCover_of_vanishingIdeal_le {n m : ℕ}
    (C : ClosedCone n) (D : ClosedCone m)
    (hle : vanishingIdeal (productCone C D) ≤ productRelationsIdeal C D) :
    HasPolyhedralCover C D := by
  intro W hW hdisj
  obtain ⟨h, _, rfl⟩ := isOpenPolyhedralCone_iff_support.mp hW
  obtain ⟨f, g, hf, hg, hf0, hg0, hbound⟩ := productRelations_majorant C D
    (hle ((mem_vanishingIdeal_iff_disjoint_support _ _).mpr hdisj))
  refine ⟨Function.support f, Function.support g,
    isOpenPolyhedralCone_iff_support.mpr ⟨f, hf0, rfl⟩,
    isOpenPolyhedralCone_iff_support.mpr ⟨g, hg0, rfl⟩,
    (mem_vanishingIdeal_iff_disjoint_support _ _).mp hf,
    (mem_vanishingIdeal_iff_disjoint_support _ _).mp hg, ?_⟩
  intro z hz
  by_contra! hn
  have hb : |h z| ≤ FVL.map (fun i ↦ i.castAdd m) f z +
      FVL.map (fun j ↦ j.natAdd n) g z := hbound z
  simp only [free_map_apply, Function.comp_def,
    Function.notMem_support.mp hn.1, Function.notMem_support.mp hn.2,
    zero_add] at hb
  exact (not_le_of_gt (abs_pos.mpr hz)) hb

/-- The polyhedral covering condition makes every function vanishing on the product cone
belong to the product relation ideal. -/
private lemma vanishingIdeal_le_of_polyhedralCover {n m : ℕ}
    (C : ClosedCone n) (D : ClosedCone m) (hcover : HasPolyhedralCover C D) :
    vanishingIdeal (productCone C D) ≤ productRelationsIdeal C D := by
  intro h hh
  obtain ⟨U, V, hU, hV, hUC, hVD, hUV⟩ := hcover (Function.support |h|)
    (isOpenPolyhedralCone_iff_support.mpr ⟨|h|, abs_nonneg _, rfl⟩)
    ((mem_vanishingIdeal_iff_disjoint_support _ _).mp
      ((vanishingIdeal (productCone C D)).abs_mem hh))
  obtain ⟨f, hf0, rfl⟩ := isOpenPolyhedralCone_iff_support.mp hU
  obtain ⟨g, hg0, rfl⟩ := isOpenPolyhedralCone_iff_support.mp hV
  have hf : FVL.map (fun i : Fin n ↦ i.castAdd m) f ∈ productRelationsIdeal C D :=
    OrderIdeal.subset_generated _ (Or.inl
      ⟨f, (mem_vanishingIdeal_iff_disjoint_support _ _).mpr hUC, rfl⟩)
  have hg : FVL.map (fun j : Fin m ↦ j.natAdd n) g ∈ productRelationsIdeal C D :=
    OrderIdeal.subset_generated _ (Or.inr
      ⟨g, (mem_vanishingIdeal_iff_disjoint_support _ _).mpr hVD, rfl⟩)
  apply ideal_mem_of_support_subset _ ((productRelationsIdeal C D).add_mem hf hg)
  intro z hz
  change FVL.map (fun i ↦ i.castAdd m) f z + FVL.map (fun j ↦ j.natAdd n) g z ≠ 0
  rw [free_map_apply, free_map_apply]
  rcases hUV z (abs_ne_zero.mpr hz) with hz' | hz'
  · exact ne_of_gt (add_pos_of_pos_of_nonneg
      (lt_of_le_of_ne (hf0 _) (Ne.symm hz')) (hg0 _))
  · exact ne_of_gt (add_pos_of_nonneg_of_pos (hf0 _)
      (lt_of_le_of_ne (hg0 _) (Ne.symm hz')))


/-- Product vanishing relations are generated by the factor relations
exactly when the polyhedral covering condition holds. -/
theorem vanishingIdeal_le_productRelationsIdeal_iff {n m : ℕ}
    (C : ClosedCone n) (D : ClosedCone m) :
    vanishingIdeal (productCone C D) ≤ productRelationsIdeal C D ↔
      HasPolyhedralCover C D := by
  exact ⟨polyhedralCover_of_vanishingIdeal_le C D, vanishingIdeal_le_of_polyhedralCover C D⟩

/-- A nonzero linear form nonnegative on an open set must be strictly positive throughout that
set. -/
private lemma linear_pos_on_open {n : ℕ} {s : Set (Fin n → ℝ)} (hs : IsOpen s)
    (L : (Fin n → ℝ) →ₗ[ℝ] ℝ) (hL : L ≠ 0) (h : ∀ x ∈ s, 0 ≤ L x) :
    ∀ x ∈ s, 0 < L x := by
  have hopen : IsOpenMap L := L.isOpenMap_of_finiteDimensional (LinearMap.surjective hL)
  have hi : interior (L ⁻¹' Set.Ici 0) = L ⁻¹' Set.Ioi 0 := by
    rw [← hopen.preimage_interior_eq_interior_preimage L.continuous_of_finiteDimensional,
      interior_Ici]
  have hsub : s ⊆ interior (L ⁻¹' Set.Ici 0) := hs.subset_interior_iff.mpr h
  rwa [hi] at hsub

/-- An open set defined by finitely many strict and non-strict homogeneous inequalities is
open polyhedral if it excludes zero. -/
private lemma openPolyhedral_of_mixed_inequalities {n : ℕ} {ι κ : Type*}
    [Finite ι] [Finite κ] (L : ι → (Fin n → ℝ) →ₗ[ℝ] ℝ)
    (M : κ → (Fin n → ℝ) →ₗ[ℝ] ℝ)
    (hopen : IsOpen {x | (∀ i, 0 ≤ L i x) ∧ ∀ j, 0 < M j x})
    (hzero : (0 : Fin n → ℝ) ∉ {x | (∀ i, 0 ≤ L i x) ∧ ∀ j, 0 < M j x}) :
    IsOpenPolyhedralCone {x | (∀ i, 0 ≤ L i x) ∧ ∀ j, 0 < M j x} := by
  classical
  obtain ⟨j, _⟩ : ∃ j, ¬ 0 < M j 0 := not_forall.mp (fun h ↦ hzero ⟨by simp, h⟩)
  let I := {i // L i ≠ 0} ⊕ κ
  let : Nonempty I := ⟨.inr j⟩
  let := Fintype.ofFinite I
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Fintype.card_pos (α := I)))
  let e : I ≃ Fin (r + 1) := (Fintype.equivFin I).trans (finCongr hr)
  let forms : I → (Fin n → ℝ) →ₗ[ℝ] ℝ := Sum.elim (fun i ↦ L i.val) M
  refine ⟨1, fun _ ↦ r, fun _ k ↦ forms (e.symm k), Set.ext fun x ↦ ?_⟩
  simp only [Set.mem_ofPred_eq, exists_const]
  rw [← e.symm.surjective.forall (p := fun i ↦ 0 < forms i x)]
  constructor
  · intro hx
    rintro (i | j)
    · exact linear_pos_on_open hopen (L i.val) i.property (fun y hy ↦ hy.1 i.val) x hx
    · exact hx.2 j
  · intro hx
    refine ⟨fun i ↦ ?_, fun j ↦ hx (.inr j)⟩
    by_cases hi : L i = 0
    · simp [hi]
    · exact (hx (.inl ⟨i, hi⟩)).le

/-- Projection along a positive scalar variable is open polyhedral when the resulting set is
open and excludes zero. -/
private lemma openPolyhedral_positive_scalar {n : ℕ} {ι : Type*} [Finite ι]
    (a : ι → ℝ) (b : ι → (Fin n → ℝ) →ₗ[ℝ] ℝ)
    (hopen : IsOpen {y | ∃ t : ℝ, 0 < t ∧ ∀ i, 0 ≤ a i * t + b i y})
    (hzero : (0 : Fin n → ℝ) ∉ {y | ∃ t : ℝ, 0 < t ∧ ∀ i, 0 ≤ a i * t + b i y}) :
    IsOpenPolyhedralCone {y | ∃ t : ℝ, 0 < t ∧ ∀ i, 0 ≤ a i * t + b i y} := by
  let I := {i // a i = 0} ⊕ ({i // 0 < a i} × {i // a i < 0})
  let L : I → (Fin n → ℝ) →ₗ[ℝ] ℝ := Sum.elim (fun i ↦ b i.val)
    (fun p ↦ a p.1.val • b p.2.val - a p.2.val • b p.1.val)
  let M : {i // a i < 0} → (Fin n → ℝ) →ₗ[ℝ] ℝ := fun i ↦ b i.val
  have heq : {y | ∃ t : ℝ, 0 < t ∧ ∀ i, 0 ≤ a i * t + b i y} =
      {y | (∀ i, 0 ≤ L i y) ∧ ∀ j, 0 < M j y} := by
    ext y
    rw [Set.mem_ofPred_eq, positive_scalar_inequalities_iff]
    simp only [Set.mem_ofPred_eq, I, L, M, Sum.forall, Prod.forall, Subtype.forall,
      Sum.elim_inl, Sum.elim_inr, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    constructor
    · rintro ⟨hz, hp, hn⟩
      exact ⟨⟨hz, fun i hi j hj ↦ hp i j hi hj⟩, hn⟩
    · rintro ⟨⟨hz, hp⟩, hn⟩
      exact ⟨hz, fun i j hi hj ↦ hp i hi j hj, hn⟩
  rw [heq] at hopen hzero ⊢
  exact openPolyhedral_of_mixed_inequalities L M hopen hzero

/-- Finitely many strictly positive real numbers admit a common strictly positive lower bound. -/
private lemma exists_pos_le_finite {ι : Type*} [Finite ι] (f : ι → ℝ)
    (hf : ∀ i, 0 < f i) : ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε ≤ f i := by
  let s := insert (1 : ℝ) (Set.range f)
  have hs : s.Finite := (Set.finite_range f).insert 1
  refine ⟨sInf s, (hs.lt_csInf_iff (Set.insert_nonempty 1 _)).mpr ?_,
    fun i ↦ csInf_le hs.bddBelow (Or.inr ⟨i, rfl⟩)⟩
  rintro z (rfl | ⟨i, rfl⟩)
  · exact zero_lt_one
  · exact hf i

/-- A mixed strict and non-strict linear inequality system has open polyhedral projection when
zero is excluded from that projection. -/
private lemma openPolyhedral_projection_piece {n m : ℕ} {ι κ : Type*}
    [Finite ι] [Finite κ] (L : ι → (Fin n → ℝ) →ₗ[ℝ] ℝ)
    (A : κ → (Fin n → ℝ) →ₗ[ℝ] ℝ) (B : κ → (Fin m → ℝ) →ₗ[ℝ] ℝ)
    (hzero : ¬ ∃ x, (∀ i, 0 ≤ L i x) ∧ ∀ j, 0 < A j x + B j 0) :
    IsOpenPolyhedralCone {y | ∃ x, (∀ i, 0 ≤ L i x) ∧ ∀ j, 0 < A j x + B j y} := by
  classical
  let H : ι ⊕ κ → (Fin n → ℝ) →ₗ[ℝ] ℝ := Sum.elim L A
  let K : ι ⊕ κ → (ℝ × (Fin m → ℝ)) →ₗ[ℝ] ℝ := Sum.elim (fun _ ↦ 0)
    (fun j ↦ (B j).comp (LinearMap.snd ℝ ℝ _) - LinearMap.fst ℝ ℝ _)
  have hH (i : ι ⊕ κ) (x : Fin n → ℝ) :
      H i x = ∑ j, H i (Pi.single j 1) * x j := by
    simpa only [map_sum, map_smul, smul_eq_mul, mul_comm]
      using congrArg (H i) (pi_eq_sum_univ' x)
  obtain ⟨k, forms, hforms⟩ := projected_linear_inequalities
    (fun i j ↦ H i (Pi.single j 1)) K
  let a (j : Fin k) := forms j (1, 0)
  let b (j : Fin k) := (forms j).comp (LinearMap.inr ℝ ℝ (Fin m → ℝ))
  have hab (j : Fin k) (t : ℝ) (y : Fin m → ℝ) :
      forms j (t, y) = a j * t + b j y := by
    calc
      forms j (t, y) = forms j (t • ((1, 0) : ℝ × (Fin m → ℝ)) + (0, y)) := by
        congr 1
        ext <;> simp
      _ = a j * t + b j y := by
        rw [map_add, map_smul]
        exact congrArg (fun z ↦ z + forms j (0, y)) (mul_comm t (a j))
  have heq : {y | ∃ x, (∀ i, 0 ≤ L i x) ∧ ∀ j, 0 < A j x + B j y} =
      {y | ∃ t : ℝ, 0 < t ∧ ∀ j, 0 ≤ a j * t + b j y} := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      obtain ⟨t, ht, ht'⟩ := exists_pos_le_finite _ hxy
      refine ⟨t, ht, fun j ↦ ?_⟩
      rw [← hab]
      apply (hforms (t, y)).mp ?_ j
      refine ⟨x, fun i ↦ ?_⟩
      rw [← hH]
      rcases i with i | i
      · simpa [H, K] using hx i
      · simpa [H, K, sub_eq_add_neg, add_assoc] using sub_nonneg.mpr (ht' i)
    · rintro ⟨t, ht, hy⟩
      obtain ⟨x, hx⟩ := (hforms (t, y)).mpr (fun j ↦ by rw [hab]; exact hy j)
      refine ⟨x, fun i ↦ ?_, fun j ↦ ?_⟩
      · have hi := hx (.inl i)
        rw [← hH] at hi
        simpa [H, K] using hi
      · have hj : 0 ≤ A j x + B j y - t := by
          have hj := hx (.inr j)
          rw [← hH] at hj
          simpa [H, K, sub_eq_add_neg, add_assoc] using hj
        linarith
  have hopen : IsOpen {y | ∃ x, (∀ i, 0 ≤ L i x) ∧ ∀ j, 0 < A j x + B j y} := by
    simp only [Set.ofPred_exists]
    apply isOpen_iUnion
    intro x
    by_cases hx : ∀ i, 0 ≤ L i x
    · simp only [hx, forall_true_iff, true_and, Set.ofPred_forall]
      exact isOpen_iInter_of_finite (fun j ↦ isOpen_lt continuous_const
        (continuous_const.add (B j).continuous_of_finiteDimensional))
    · simpa only [hx, false_and, Set.ofPred_false] using isOpen_empty
  rw [heq]
  exact openPolyhedral_positive_scalar a b (heq ▸ hopen) (heq ▸ hzero)

/-- A finite union of open polyhedral cones is an open polyhedral cone. -/
private lemma openPolyhedral_finite_union {n : ℕ} {ι : Type*} [Finite ι]
    (s : ι → Set (Fin n → ℝ)) (hs : ∀ i, IsOpenPolyhedralCone (s i)) :
    IsOpenPolyhedralCone (⋃ i, s i) := by
  classical
  let := Fintype.ofFinite ι
  choose f hf hfs using fun i ↦ exists_nonneg_positive_set (hs i)
  convert isOpenPolyhedralCone_positive (∑ i, f i) using 1
  ext x
  simp only [Set.mem_iUnion, hfs, Set.mem_ofPred_eq]
  change (∃ i, 0 < f i x) ↔
    0 < (FVL.concreteSublattice (Fin n)).toSubmodule.subtype (∑ i, f i) x
  simp only [map_sum, Finset.sum_apply, Submodule.subtype_apply]
  rw [Finset.sum_pos_iff_of_nonneg (fun i _ ↦ hf i x)]
  simp

/-- Projecting an open polyhedral relation over a closed polyhedral cone preserves open
polyhedrality when the projection excludes zero. -/
private lemma openPolyhedral_projection {n m : ℕ} {C : Set (Fin n → ℝ)}
    {W : Set (Fin (n + m) → ℝ)} (hC : IsClosedPolyhedralCone C)
    (hW : IsOpenPolyhedralCone W) (hzero : ¬ ∃ x ∈ C, Fin.append x 0 ∈ W) :
    IsOpenPolyhedralCone {y | ∃ x ∈ C, Fin.append x y ∈ W} := by
  classical
  rcases hC with ⟨k, cones, hcones, rfl⟩
  rcases hW with ⟨q, r, forms, rfl⟩
  choose sets hsets using hcones
  let left : (Fin n → ℝ) →ₗ[ℝ] (Fin (n + m) → ℝ) :=
    LinearMap.pi (Fin.append (fun i ↦ LinearMap.proj i) (fun _ ↦ 0))
  let right : (Fin m → ℝ) →ₗ[ℝ] (Fin (n + m) → ℝ) :=
    LinearMap.pi (Fin.append (fun _ ↦ 0) (fun j ↦ LinearMap.proj j))
  have happend (x : Fin n → ℝ) (y : Fin m → ℝ) :
      left x + right y = Fin.append x y := by
    ext i
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) i <;> simp [left, right]
  have hmem (i : Fin k) (x : Fin n → ℝ) :
      x ∈ cones i ↔ ∀ l : ↥(sets i), 0 ≤ l.val x := by
    rw [← hsets]
    simp [PointedCone.mem_dual, Subtype.forall]
  let P (p : Fin k × Fin q) : Set (Fin m → ℝ) :=
    {y | ∃ x, (∀ l : ↥(sets p.1), 0 ≤ l.val x) ∧
      ∀ j, 0 < (forms p.2 j).comp left x + (forms p.2 j).comp right y}
  have hP (p : Fin k × Fin q) : IsOpenPolyhedralCone (P p) := by
    apply openPolyhedral_projection_piece
    rintro ⟨x, hx, hxy⟩
    apply hzero
    refine ⟨x, Set.mem_iUnion.mpr ⟨p.1, (hmem _ _).mpr hx⟩, p.2, fun j ↦ ?_⟩
    rw [← happend, map_add]
    exact hxy j
  convert openPolyhedral_finite_union P hP using 1
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, P, Prod.exists]
  constructor
  · rintro ⟨x, ⟨i, hi⟩, j, hj⟩
    refine ⟨i, j, x, (hmem _ _).mp hi, fun l ↦ ?_⟩
    simpa only [LinearMap.comp_apply, ← map_add, happend] using hj l
  · rintro ⟨i, j, x, hx, hxy⟩
    refine ⟨x, ⟨i, (hmem _ _).mpr hx⟩, j, fun l ↦ ?_⟩
    simpa only [LinearMap.comp_apply, ← map_add, happend] using hxy l

/-- A closed polyhedral cone satisfies the covering condition
with every closed cone. -/
theorem hasPolyhedralCover_of_polyhedral {n m : ℕ}
    (C : ClosedCone n) (D : ClosedCone m)
    (hC : IsClosedPolyhedralCone C.carrier) :
    HasPolyhedralCover C D := by
  intro W hW hdisj
  let V : Set (Fin m → ℝ) := {y | ∃ x ∈ C.carrier, Fin.append x y ∈ W}
  have hVD : Disjoint V D.carrier := by
    apply Set.disjoint_left.mpr
    rintro y ⟨x, hx, hxy⟩ hy
    apply Set.disjoint_left.mp hdisj hxy
    simpa only [productCone, Set.mem_ofPred_eq, Fin.append_left, Fin.append_right] using ⟨hx, hy⟩
  refine ⟨C.carrierᶜ, V, openPolyhedral_compl_of_closedPolyhedral hC C.zero_mem,
    openPolyhedral_projection hC hW (fun h ↦ Set.disjoint_left.mp hVD h D.zero_mem),
    disjoint_compl_left, hVD, fun z hz ↦ ?_⟩
  by_cases hx : (fun i : Fin n ↦ z (i.castAdd m)) ∈ C.carrier
  · exact Or.inr ⟨_, hx, Fin.append_castAdd_natAdd.symm ▸ hz⟩
  · exact Or.inl hx

end VectorLattice.ConeRepresentation

namespace VectorLattice

variable (X : Type u) [AddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [VectorLattice X]

open ConeRepresentation

/-- A free product of cone function lattices is Archimedean exactly when the
two cones admit a polyhedral cover. -/
lemma binary_cone_product_archimedean_iff {E : ULift.{u} Bool → Type u}
    [∀ i, AddCommGroup (E i)] [∀ i, Lattice (E i)]
    [∀ i, IsOrderedAddMonoid (E i)] [∀ i, VectorLattice (E i)] (P : FreeProduct E)
    {n m : ℕ} (C : ClosedCone n) (D : ClosedCone m)
    (eC : VecLatEquiv (E ⟨false⟩) (ConeFunctions C))
    (eD : VecLatEquiv (E ⟨true⟩) (ConeFunctions D)) :
    IsVLArchimedean P.Carrier ↔ HasPolyhedralCover C D := by
  obtain ⟨e⟩ := binary_cone_product_equiv P C D eC eD
  exact (archimedean_equiv_iff e).trans ((archimedean_product_quotient_iff C D).trans
    (vanishingIdeal_le_productRelationsIdeal_iff C D))

end VectorLattice
