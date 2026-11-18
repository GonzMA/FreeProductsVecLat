/-
Authors: Gonzalo Martínez-Fernández
-/

import FreeProducts.Archimedean.Archimedeanization
import FreeProducts.BanachLattice.Join
import FreeProducts.TensorProducts.Banach

/-!
# Archimedean free products and order-unit representations

Archimedean free products exist and are uniquely determined by their universal
property. Their factor inclusions are injective and generate the whole lattice.
Order-unit completions, dense continuous-function representations, and extension
results provide the tools for studying embeddings of these free products.
-/

universe u v

namespace VectorLattice

/-- A vector sublattice of an Archimedean vector lattice is Archimedean. -/
private instance sublatticeArchimedean {X : Type u} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] [IsVLArchimedean X] (A : VectorSublattice X) :
    IsVLArchimedean A := ⟨fun {x y} h ↦
      IsVLArchimedean.le_zero_of_forall_nsmul_le (x := x.val) (y := y.val) h⟩

section FreeProducts

variable {I : Type u} (E : I → Type u)
  [∀ i, AddCommGroup (E i)] [∀ i, Lattice (E i)]
  [∀ i, IsOrderedAddMonoid (E i)] [∀ i, VectorLattice (E i)]
  [∀ i, IsVLArchimedean (E i)]

/-- An Archimedean free product extends every family of homomorphisms
uniquely to each Archimedean target. -/
structure ArchimedeanFreeProduct [∀ i, IsVLArchimedean (E i)] where
  Carrier : Type u
  [addCommGroup : AddCommGroup Carrier]
  [lattice : Lattice Carrier]
  [isOrderedAddMonoid : IsOrderedAddMonoid Carrier]
  [vectorLattice : VectorLattice Carrier]
  [isVLArchimedean : IsVLArchimedean Carrier]
  inclusion : ∀ i, VecLatHom (E i) Carrier
  universal :
    ∀ (Y : Type u) [AddCommGroup Y] [Lattice Y]
      [IsOrderedAddMonoid Y] [VectorLattice Y] [IsVLArchimedean Y]
      (T : ∀ i, VecLatHom (E i) Y),
      ∃! S : VecLatHom Carrier Y,
        ∀ i x, S (inclusion i x) = T i x

attribute [instance] ArchimedeanFreeProduct.addCommGroup
  ArchimedeanFreeProduct.lattice ArchimedeanFreeProduct.isOrderedAddMonoid
  ArchimedeanFreeProduct.vectorLattice ArchimedeanFreeProduct.isVLArchimedean

/-- Archimedeanization of an ordinary free product, with the canonical
factor maps composed with the quotient map. -/
noncomputable def FreeProduct.archimedeanization (P : FreeProduct E) :
    ArchimedeanFreeProduct E where
  Carrier := Archimedeanization P.Carrier
  addCommGroup := inferInstance
  lattice := inferInstance
  isOrderedAddMonoid := inferInstance
  vectorLattice := inferInstance
  isVLArchimedean := inferInstance
  inclusion i := (archimedeanQuotient P.Carrier).comp (P.inclusion i)
  universal := by
    intro Y _ _ _ _ _ T
    obtain ⟨U, hU, huU⟩ := P.universal Y T
    obtain ⟨S, hS, huS⟩ := archimedeanization_universal P.Carrier Y U
    exact ⟨S, fun i x ↦ (DFunLike.congr_fun hS (P.inclusion i x)).trans (hU i x),
      fun R hR ↦ huS R (huU (R.comp (archimedeanQuotient P.Carrier)) hR)⟩

/-- Every family of Archimedean vector lattices has an Archimedean free product. -/
theorem nonempty_archimedeanFreeProduct :
    Nonempty (ArchimedeanFreeProduct E) := by
  exact (nonempty_freeProduct E).map (FreeProduct.archimedeanization E)

variable {E}

/-- Homomorphisms from an Archimedean free product into an Archimedean lattice are determined
by their values on the factors. -/
lemma ArchimedeanFreeProduct.hom_ext (P : ArchimedeanFreeProduct E)
    {W : Type u} [AddCommGroup W] [Lattice W]
    [IsOrderedAddMonoid W] [VectorLattice W] [IsVLArchimedean W]
    {S T : VecLatHom P.Carrier W}
    (h : ∀ i x, S (P.inclusion i x) = T (P.inclusion i x)) : S = T := by
  obtain ⟨R, _, hu⟩ := P.universal W (fun i ↦ S.comp (P.inclusion i))
  exact (hu S (fun _ _ ↦ rfl)).trans (hu T (fun i x ↦ (h i x).symm)).symm

/-- Real-valued homomorphisms from an Archimedean free product are determined by their
restrictions to the factors. -/
lemma ArchimedeanFreeProduct.scalar_hom_ext (P : ArchimedeanFreeProduct E)
    {S T : VecLatHom P.Carrier ℝ}
    (h : ∀ i x, S (P.inclusion i x) = T (P.inclusion i x)) : S = T := by
  let c : VecLatHom ℝ C(PUnit.{u + 1}, ℝ) :=
    { (ContinuousLinearMap.const ℝ PUnit).toLinearMap with
      map_sup' := fun _ _ ↦ rfl
      map_inf' := fun _ _ ↦ rfl }
  have hc := P.hom_ext (S := c.comp S) (T := c.comp T)
    (fun i x ↦ congrArg c (h i x))
  exact DFunLike.ext _ _ (fun x ↦ congrArg (fun f : C(PUnit, ℝ) ↦ f PUnit.unit)
    (DFunLike.congr_fun hc x))

/-- Archimedean free products are uniquely isomorphic by an isomorphism
commuting with the canonical factor maps. -/
theorem ArchimedeanFreeProduct.exists_unique_equiv
    (P Q : ArchimedeanFreeProduct E) :
    ∃! e : VecLatEquiv P.Carrier Q.Carrier,
      ∀ i x, e (P.inclusion i x) = Q.inclusion i x := by
  obtain ⟨f, hf, _⟩ := P.universal Q.Carrier Q.inclusion
  obtain ⟨g, hg, _⟩ := Q.universal P.Carrier P.inclusion
  let e : VecLatEquiv P.Carrier Q.Carrier :=
    { f.toLinearMap with
      invFun := g
      left_inv := DFunLike.congr_fun (P.hom_ext (S := g.comp f) (T := VecLatHom.id)
        (fun i x ↦ (congrArg g (hf i x)).trans (hg i x)))
      right_inv := DFunLike.congr_fun (Q.hom_ext (S := f.comp g) (T := VecLatHom.id)
        (fun i x ↦ (congrArg f (hg i x)).trans (hf i x)))
      map_sup' := f.map_sup'
      map_inf' := f.map_inf' }
  exact ⟨e, hf, fun e' he' ↦ DFunLike.ext _ _ (fun x ↦
    DFunLike.congr_fun (P.hom_ext (S := e'.toVecLatHom) (T := f)
      (fun i x ↦ (he' i x).trans (hf i x).symm)) x)⟩

/-- Every canonical factor map into an Archimedean free product is injective. -/
theorem ArchimedeanFreeProduct.inclusion_injective
    (P : ArchimedeanFreeProduct E) (i : I) :
    Function.Injective (P.inclusion i) := by
  classical
  let T : ∀ j, VecLatHom (E j) (E i) := Function.update
    (fun j ↦ VecLatHom.ofAbs (0 : E j →ₗ[ℝ] E i) (by simp)) i VecLatHom.id
  obtain ⟨R, hR, _⟩ := P.universal (E i) T
  exact (show Function.LeftInverse R (P.inclusion i) from fun x ↦
    (hR i x).trans (DFunLike.congr_fun
      (show T i = VecLatHom.id from Function.update_self _ _ _) x)).injective

/-- If every factor except one is zero, the remaining factor surjects onto the Archimedean
free product. -/
lemma ArchimedeanFreeProduct.inclusion_surjective_of_subsingleton
    (P : ArchimedeanFreeProduct E) (i : I) (h : ∀ j, j ≠ i → Subsingleton (E j)) :
    Function.Surjective (P.inclusion i) := by
  classical
  let T : ∀ j, VecLatHom (E j) (E i) := Function.update
    (fun j ↦ VecLatHom.ofAbs (0 : E j →ₗ[ℝ] E i) (by simp)) i VecLatHom.id
  obtain ⟨R, hR, _⟩ := P.universal (E i) T
  have hi : (P.inclusion i).comp R = VecLatHom.id := by
    apply P.hom_ext
    intro j x
    change P.inclusion i (R (P.inclusion j x)) = P.inclusion j x
    by_cases hji : j = i
    · subst j
      rw [hR]
      exact congrArg (P.inclusion i) (DFunLike.congr_fun
        (show T i = VecLatHom.id from Function.update_self _ _ _) x)
    · let := h j hji
      rw [Subsingleton.elim x 0, map_zero, map_zero, map_zero]
  exact fun z ↦ ⟨R z, DFunLike.congr_fun hi z⟩

/-- For finitely many factors with strong units, the sum of their included units is a strong
unit of the Archimedean free product. -/
lemma ArchimedeanFreeProduct.strongOrderUnit [Fintype I]
    (P : ArchimedeanFreeProduct E) (e : ∀ i, E i) (he : ∀ i, StrongOrderUnit (e i)) :
    StrongOrderUnit (∑ i, P.inclusion i (e i)) := by
  classical
  let w := ∑ i, P.inclusion i (e i)
  have hw : 0 ≤ w := Finset.sum_nonneg (fun i _ ↦ (P.inclusion i).map_nonneg (he i).1)
  have hi (i : I) : P.inclusion i (e i) ≤ w :=
    Finset.single_le_sum (fun j _ ↦ (P.inclusion j).map_nonneg (he j).1) (Finset.mem_univ i)
  let D := (OrderIdeal.principal w).toVectorSublattice
  have hm (i : I) (x : E i) : P.inclusion i x ∈ D := by
    obtain ⟨c, hc, hcx⟩ := (he i).2 x
    refine ⟨c, hc, ?_⟩
    rw [abs_of_nonneg hw, ← (P.inclusion i).map_abs]
    exact ((P.inclusion i).monotone hcx).trans
      (by simpa only [map_smul] using smul_le_smul_of_nonneg_left (hi i) hc)
  let T : ∀ i, VecLatHom (E i) D := fun i ↦
    { (P.inclusion i).toLinearMap.codRestrict D.toSubmodule (hm i) with
      map_sup' := fun x y ↦ Subtype.ext (map_sup (P.inclusion i) x y)
      map_inf' := fun x y ↦ Subtype.ext (map_inf (P.inclusion i) x y) }
  obtain ⟨R, hR, _⟩ := P.universal D T
  have hR' : D.subtype.comp R = VecLatHom.id := P.hom_ext (fun i x ↦
    congrArg Subtype.val (hR i x))
  refine ⟨hw, fun x ↦ ?_⟩
  have hx := (R x).property
  rw [show (R x).val = x from DFunLike.congr_fun hR' x] at hx
  simpa only [OrderIdeal.mem_principal, abs_of_nonneg hw] using
    (show x ∈ OrderIdeal.principal w from hx)

end FreeProducts

section OrderUnitCompletion

open UniformSpace

variable {X : Type u} [NormedAddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [NormedVectorLattice X]

/-- A norm bound by a fixed order unit persists after taking the norm completion. -/
private lemma completion_abs_le_norm_smul {e : X}
    (he : ∀ x : X, |x| ≤ ‖x‖ • e) (z : Completion X) :
    |z| ≤ ‖z‖ • (e : Completion X) := by
  refine Completion.induction_on z
    (isClosed_le (continuous_id.sup continuous_neg)
      (continuous_norm.smul continuous_const)) ?_
  exact fun x ↦ by
    simpa only [coe_toCompletionVecLatHom, coe_abs_completion, Completion.coe_smul,
      Completion.norm_coe] using
      (toCompletionVecLatHom : VecLatHom X (Completion X)).monotone (he x)

/-- The norm equals the order-unit gauge when the unit has norm at most one and dominates each
vector by its norm. -/
private lemma gaugeNorm_eq_norm_of_unit_bound {e : X} (he : 0 ≤ e) (hne : ‖e‖ ≤ 1)
    (hb : ∀ x : X, |x| ≤ ‖x‖ • e) (x : X) : OrderIdeal.gaugeNorm e x = ‖x‖ := by
  refine le_antisymm (OrderIdeal.gaugeNorm_le_of_abs_le e (norm_nonneg x)
    (by simpa only [abs_of_nonneg he] using hb x)) ?_
  have hx : x ∈ OrderIdeal.principal e := ⟨‖x‖, norm_nonneg x,
    by simpa only [abs_of_nonneg he] using hb x⟩
  calc
    ‖x‖ ≤ ‖OrderIdeal.gaugeNorm e x • e‖ := norm_le_norm_of_abs_le_abs
      (by simpa [abs_smul', abs_of_nonneg (OrderIdeal.gaugeNorm_nonneg e x)] using
        OrderIdeal.abs_le_gaugeNorm_smul_abs e hx)
    _ = OrderIdeal.gaugeNorm e x * ‖e‖ := by
      rw [norm_smul, Real.norm_of_nonneg (OrderIdeal.gaugeNorm_nonneg e x)]
    _ ≤ OrderIdeal.gaugeNorm e x * 1 :=
      mul_le_mul_of_nonneg_left hne (OrderIdeal.gaugeNorm_nonneg e x)
    _ = OrderIdeal.gaugeNorm e x := mul_one _

/-- An order-unit normed lattice embeds isometrically and densely into continuous functions on
a nonempty compact Hausdorff space, sending its unit to one. -/
private lemma exists_orderUnit_completion {e : X} (he : 0 < e) (hne : ‖e‖ ≤ 1)
    (hb : ∀ x : X, |x| ≤ ‖x‖ • e) :
    ∃ (K : Type u) (_ : TopologicalSpace K) (_ : CompactSpace K) (_ : T2Space K)
      (_ : Nonempty K) (j : VecLatHom X C(K, ℝ)),
      Isometry j ∧ DenseRange j ∧ j e = 1 := by
  let H := Completion X
  have heH : 0 < (e : H) := by
    simpa only [map_zero, coe_toCompletionVecLatHom] using
      ((toCompletionVecLatHom : VecLatHom X H).monotone.strictMono_of_injective
        (isometry_toCompletionVecLatHom (X := X)).injective) he
  let : IsUniformlyCompleteVectorLattice H :=
    isUniformlyCompleteVectorLattice_of_banachLattice H
  let J := ↥(OrderIdeal.principal (e : H))
  let : NormedAddCommGroup J := OrderIdeal.principalNormedAddCommGroup (e : H)
  let : Lattice J := OrderIdeal.instLatticePrincipal (e : H)
  let : IsOrderedAddMonoid J := OrderIdeal.instIsOrderedAddMonoidPrincipal (e : H)
  let : AMSpaceWithUnit J := OrderIdeal.principalAMSpaceWithUnit heH.le
    (IsUniformlyCompleteVectorLattice.complete_principal (e : H) heH)
  have hnorm (z : J) : ‖z‖ = ‖(z : H)‖ :=
    gaugeNorm_eq_norm_of_unit_bound heH.le
      (by simpa only [Completion.norm_coe] using hne) (completion_abs_le_norm_smul hb) z.val
  let j : VecLatHom X J :=
    { toFun := fun x ↦ ⟨(x : H), ‖(x : H)‖, norm_nonneg _, by
        simpa only [abs_of_nonneg heH.le] using completion_abs_le_norm_smul hb (x : H)⟩
      map_add' := fun x y ↦ Subtype.ext (Completion.coe_add x y)
      map_smul' := fun r x ↦ Subtype.ext (Completion.coe_smul r x)
      map_sup' := fun x y ↦ Subtype.ext (coe_sup_completion x y)
      map_inf' := fun x y ↦ Subtype.ext (coe_inf_completion x y) }
  have : Nontrivial J := ⟨⟨⟨(e : H), OrderIdeal.self_mem_principal _⟩, 0,
    fun h ↦ heH.ne' (congrArg Subtype.val h)⟩⟩
  let k := AMSpaceWithUnit.kakutaniEquiv J
  refine ⟨AMSpaceWithUnit.LatticeCharacter J, inferInstance, inferInstance, inferInstance,
    ⟨(AMSpaceWithUnit.LatticeCharacter.exists_abs_apply_eq_norm (X := J) 0).choose⟩,
    k.toVecLatEquiv.toVecLatHom.comp j, ?_, ?_, ?_⟩
  · exact AddMonoidHomClass.isometry_of_norm _ (fun x ↦
      (k.toLinearIsometryEquiv.norm_map (j x)).trans
        ((hnorm (j x)).trans (Completion.norm_coe x)))
  · refine Metric.denseRange_iff.mpr (fun f ε hε ↦ ?_)
    obtain ⟨x, hx⟩ := Completion.denseRange_coe.exists_dist_lt ((k.symm f).val : H) hε
    refine ⟨x, ?_⟩
    calc
      _ = ‖k.toLinearIsometryEquiv (k.symm f - j x)‖ := by
        exact (dist_eq_norm _ _).trans (congrArg norm ((k.toLinearIsometryEquiv.map_sub _ _).trans
          (congrArg (· - k.toLinearIsometryEquiv (j x))
            (k.toLinearIsometryEquiv.apply_symm_apply f)))).symm
      _ = ‖k.symm f - j x‖ := k.toLinearIsometryEquiv.norm_map _
      _ = dist ((k.symm f).val : H) (x : H) := by
        rw [hnorm, dist_eq_norm]
        rfl
      _ < ε := hx
  · exact AMSpaceWithUnit.kakutaniEquiv_unit (X := J)

end OrderUnitCompletion

section OrderUnitRepresentation

variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X] [IsVLArchimedean X]

omit [IsVLArchimedean X] in
/-- A sublattice generated by finitely many elements has a strong order unit. -/
lemma exists_strongOrderUnit_generated_finset (s : Finset X) :
    ∃ e : VectorSublattice.generated (s : Set X), StrongOrderUnit e := by
  let A := VectorSublattice.generated (s : Set X)
  let e := ∑ x ∈ s, |x|
  have he : 0 ≤ e := Finset.sum_nonneg (fun x _ ↦ abs_nonneg x)
  have heA : e ∈ A := A.toSubmodule.sum_mem (fun x hx ↦
    A.abs_mem (VectorSublattice.subset_generated (s : Set X) hx))
  have hA : A ≤ (OrderIdeal.principal e).toVectorSublattice :=
    VectorSublattice.generated_le (fun x hx ↦ ⟨1, zero_le_one, by
      simpa only [one_smul, abs_of_nonneg he] using
        Finset.single_le_sum (fun y _ ↦ abs_nonneg y) hx⟩)
  refine ⟨⟨e, heA⟩, he, fun x ↦ ?_⟩
  obtain ⟨c, hc, hcx⟩ := hA x.property
  refine ⟨c, hc, ?_⟩
  change |x.val| ≤ c • e
  simpa only [abs_of_nonneg he] using hcx

omit [IsVLArchimedean X] in
/-- A strong order unit in a nontrivial vector lattice is strictly positive. -/
lemma strongOrderUnit_pos [Nontrivial X] {e : X} (he : StrongOrderUnit e) : 0 < e := by
  refine lt_of_le_of_ne he.1 (fun h ↦ ?_)
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  obtain ⟨c, _, hcx⟩ := he.2 x
  rw [← h, smul_zero] at hcx
  exact hx ((abs_eq_zero_iff_zero x).mp (le_antisymm hcx (abs_nonneg x)))

omit [IsVLArchimedean X] in
/-- A homomorphism sending one generating set into another sends the corresponding generated
sublattices into each other. -/
lemma map_mem_generated {Y : Type u} [AddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] [VectorLattice Y] (T : VecLatHom X Y)
    (s : Set X) (t : Set Y) (h : ∀ x ∈ s, T x ∈ t) :
    ∀ x ∈ VectorSublattice.generated s, T x ∈ VectorSublattice.generated t := by
  let A := VectorSublattice.generated t
  let B : VectorSublattice X :=
    { toSubmodule := A.toSubmodule.comap T.toLinearMap
      sup_mem' := fun hx hy ↦ by
        change T (_ ⊔ _) ∈ A
        rw [map_sup]
        exact A.sup_mem hx hy }
  exact VectorSublattice.generated_le (Y := B)
    (fun x hx ↦ VectorSublattice.subset_generated t (h x hx))

/-- An Archimedean lattice with a positive strong order unit has a dense representation in
continuous functions that sends the unit to one. -/
lemma exists_orderUnit_representation {u : X} (hu : StrongOrderUnit u) (hu0 : 0 < u) :
    ∃ (K : Type u) (_ : TopologicalSpace K) (_ : CompactSpace K) (_ : T2Space K)
      (_ : Nonempty K) (j : VecLatHom X C(K, ℝ)),
      Function.Injective j ∧ DenseRange j ∧ j u = 1 := by
  let D := ↥(OrderIdeal.principal u)
  let : NormedAddCommGroup D := OrderIdeal.principalNormedAddCommGroup u
  let : Lattice D := OrderIdeal.instLatticePrincipal u
  let : IsOrderedAddMonoid D := OrderIdeal.instIsOrderedAddMonoidPrincipal u
  let : NormedVectorLattice D := OrderIdeal.principalNormedVectorLattice u
  let d : VecLatHom X D :=
    { toFun := fun x ↦ ⟨x, by
        simpa only [OrderIdeal.mem_principal, abs_of_nonneg hu.1] using hu.2 x⟩
      map_add' := fun _ _ ↦ Subtype.ext rfl
      map_smul' := fun _ _ ↦ Subtype.ext rfl
      map_sup' := fun _ _ ↦ Subtype.ext rfl
      map_inf' := fun _ _ ↦ Subtype.ext rfl }
  have hn : ‖d u‖ ≤ 1 := OrderIdeal.gaugeNorm_le_of_abs_le u zero_le_one
    (by change |u| ≤ (1 : ℝ) • |u|; simp)
  have hb (z : D) : |z| ≤ ‖z‖ • d u := by
    change |z.val| ≤ OrderIdeal.gaugeNorm u z.val • u
    simpa only [abs_of_nonneg hu.1] using OrderIdeal.abs_le_gaugeNorm_smul_abs u z.property
  obtain ⟨K, tK, cK, hK, nK, j, hj, hd, he⟩ :=
    exists_orderUnit_completion (show 0 < d u from hu0) hn hb
  refine ⟨K, tK, cK, hK, nK, j.comp d, hj.injective.comp
    (fun _ _ h ↦ congrArg Subtype.val h), ?_, he⟩
  exact Dense.mono (s₁ := Set.range j) (s₂ := Set.range (j.comp d))
    (fun _ ⟨z, hz⟩ ↦ ⟨z.val, hz⟩) hd

end OrderUnitRepresentation

section OrderUnitExtension

variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X] {K : Type u} [TopologicalSpace K] [CompactSpace K]

/-- A unital embedding into continuous functions bounds each absolute value by the supremum
norm of its image times the unit. -/
lemma abs_le_norm_smul_of_unital_embedding (j : VecLatHom X C(K, ℝ))
    (hj : Function.Injective j) {e : X} (he : j e = 1) (x : X) :
    |x| ≤ ‖j x‖ • e := by
  apply j.le_of_map_le hj
  simp only [j.map_abs, map_smul, he]
  intro t
  change |j x t| ≤ ‖j x‖ * 1
  simpa only [mul_one, Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm (j x) t

/-- A lattice homomorphism is bounded for the norm induced by a unital continuous-function
representation, with bound given by the image of the unit. -/
private lemma norm_bound_of_unital_embedding {Y : Type v} [NormedAddCommGroup Y]
    [Lattice Y] [IsOrderedAddMonoid Y] [NormedVectorLattice Y]
    (j : VecLatHom X C(K, ℝ)) (hj : Function.Injective j)
    {e : X} (he : j e = 1) (T : VecLatHom X Y) (x : X) :
    ‖T x‖ ≤ ‖T e‖ * ‖j x‖ := by
  have h := T.monotone (abs_le_norm_smul_of_unital_embedding j hj he x)
  rw [T.map_abs, map_smul] at h
  calc
    ‖T x‖ ≤ ‖‖j x‖ • T e‖ := norm_le_norm_of_abs_le_abs (h.trans (le_abs_self _))
    _ = ‖T e‖ * ‖j x‖ := by rw [norm_smul, Real.norm_of_nonneg (norm_nonneg _)]; ring

/-- A lattice homomorphism into a complete normed lattice extends continuously from a dense
unital representation to the full function space. -/
private lemma exists_orderUnit_extension {Y : Type v} [NormedAddCommGroup Y]
    [Lattice Y] [IsOrderedAddMonoid Y] [NormedVectorLattice Y] [CompleteSpace Y]
    (j : VecLatHom X C(K, ℝ)) (hj : Function.Injective j) (hd : DenseRange j)
    {e : X} (he : j e = 1) (T : VecLatHom X Y) :
    ∃ S : C(K, ℝ) →L[ℝ] Y, IsVecLatHom S ∧ ∀ x, S (j x) = T x := by
  let S := T.toLinearMap.extendOfNorm j.toLinearMap
  have hS (x : X) : S (j x) = T x := LinearMap.extendOfNorm_eq hd
    ⟨‖T e‖, norm_bound_of_unital_embedding j hj he T⟩ x
  have ha (f : C(K, ℝ)) : S |f| = |S f| := by
    refine hd.induction_on f
      (isClosed_eq (S.continuous.comp (continuous_id.sup continuous_neg))
        (S.continuous.sup S.continuous.neg)) ?_
    intro x
    rw [← j.map_abs, hS, hS, T.map_abs]
  exact ⟨S, (VecLatHom.ofAbs S.toLinearMap ha).isVecLatHom, hS⟩

/-- A dense unital sublattice contains a nonzero positive function below every nonzero
positive continuous function. -/
private lemma exists_pos_le_of_dense_unital (j : VecLatHom X C(K, ℝ)) (hd : DenseRange j)
    {e : X} (he : j e = 1) {f : C(K, ℝ)} (hf : 0 ≤ f) (hf0 : f ≠ 0) :
    ∃ x, 0 ≤ j x ∧ j x ≠ 0 ∧ j x ≤ f := by
  obtain ⟨t, ht⟩ : ∃ t, f t ≠ 0 := by
    by_contra! h
    exact hf0 (ContinuousMap.ext h)
  have ht0 : 0 < f t := lt_of_le_of_ne (hf t) ht.symm
  obtain ⟨x, hx⟩ := hd.exists_dist_lt f (show 0 < f t / 4 by positivity)
  have hc (s : K) : |f s - j x s| < f t / 4 := by
    exact (ContinuousMap.norm_coe_le_norm (f - j x) s).trans_lt
      (by simpa only [dist_eq_norm] using hx)
  refine ⟨(x - (f t / 4) • e) ⊔ 0, ?_, ?_, ?_⟩
  · rw [map_sup, map_zero]
    exact le_sup_right
  · intro hz
    have hz' := DFunLike.congr_fun hz t
    simp only [map_sup, map_sub, map_smul, map_zero, he, ContinuousMap.sup_apply,
      ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
      ContinuousMap.zero_apply, smul_eq_mul, mul_one] at hz'
    have := (abs_lt.mp (hc t)).2
    have := le_sup_left (a := j x t - f t / 4) (b := (0 : ℝ))
    linarith
  · rw [map_sup, map_sub, map_smul, map_zero, he]
    intro s
    change max (j x s - f t / 4 * 1) 0 ≤ f s
    exact max_le (by have := (abs_lt.mp (hc s)).1; linarith) (hf s)

/-- A homomorphism on a continuous-function lattice is injective if its restriction to a dense
unital sublattice is injective. -/
private lemma injective_of_dense_unital_restriction {Y : Type u} [AddCommGroup Y]
    [Lattice Y] [IsOrderedAddMonoid Y] [VectorLattice Y]
    (j : VecLatHom X C(K, ℝ)) (hd : DenseRange j) {e : X} (he : j e = 1)
    (S : VecLatHom C(K, ℝ) Y) (hS : Function.Injective (S.comp j)) :
    Function.Injective S := by
  refine (injective_iff_map_eq_zero S).mpr (fun f hf ↦ ?_)
  by_contra hf0
  obtain ⟨x, hx, hx0, hxf⟩ :=
    exists_pos_le_of_dense_unital j hd he (abs_nonneg f)
      (fun h ↦ hf0 ((abs_eq_zero_iff_zero f).mp h))
  have hz : S (j x) = 0 := le_antisymm
    (by simpa only [S.map_abs, hf, abs_zero] using S.monotone hxf) (S.map_nonneg hx)
  exact hx0 (by
    have hx' : x = 0 := hS (hz.trans (map_zero (S.comp j)).symm)
    rw [hx', map_zero])

/-- An injective homomorphism from a dense unital representation extends to an injective
continuous lattice homomorphism. -/
lemma exists_injective_orderUnit_extension {Y : Type u} [NormedAddCommGroup Y]
    [Lattice Y] [IsOrderedAddMonoid Y] [NormedVectorLattice Y] [CompleteSpace Y]
    (j : VecLatHom X C(K, ℝ)) (hj : Function.Injective j) (hd : DenseRange j)
    {e : X} (he : j e = 1) (T : VecLatHom X Y) (hT : Function.Injective T) :
    ∃ S : C(K, ℝ) →L[ℝ] Y, IsVecLatHom S ∧ Function.Injective S ∧
      ∀ x, S (j x) = T x := by
  obtain ⟨S, hS, hSj⟩ := exists_orderUnit_extension j hj hd he T
  refine ⟨S, hS, injective_of_dense_unital_restriction j hd he (hS.mk' S) ?_, hSj⟩
  intro x y hxy
  apply hT
  exact (hSj x).symm.trans (hxy.trans (hSj y))

end OrderUnitExtension

/-- A normalized scalar character takes a value at least as large as the value of a given
continuous function at some point. -/
private lemma continuousFunction_exists_apply_le_hom {K : Type u} [TopologicalSpace K]
    [CompactSpace K] [Nonempty K] (F : VecLatHom C(K, ℝ) ℝ)
    (hF : F 1 = 1) (f : C(K, ℝ)) : ∃ x, f x ≤ F f := by
  obtain ⟨x, _, hx⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty
    f.continuous.continuousOn
  have hmin : (f x) • (1 : C(K, ℝ)) ≤ f := fun y ↦ by
    simpa using hx (Set.mem_univ y)
  exact ⟨x, by simpa [map_smul, hF] using F.monotone hmin⟩

/-- A normalized scalar character agrees with point evaluation simultaneously on any finite
family of continuous functions. -/
private lemma continuousFunction_exists_eq_hom_on_finset {K : Type u} [TopologicalSpace K]
    [CompactSpace K] [Nonempty K] (F : VecLatHom C(K, ℝ) ℝ) (hF : F 1 = 1)
    (s : Finset C(K, ℝ)) : ∃ x, ∀ f ∈ s, f x = F f := by
  let g : C(K, ℝ) := ∑ f ∈ s, |f - (F f) • 1|
  have hFg : F g = 0 := by
    simp [g, map_sum, F.map_abs, map_sub, map_smul, hF]
  obtain ⟨x, hx⟩ := continuousFunction_exists_apply_le_hom F hF g
  have hzero : (∑ f ∈ s, |f x - F f|) = 0 :=
    le_antisymm (by simpa [g, hFg] using hx)
      (Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _))
  exact ⟨x, fun f hf ↦ sub_eq_zero.mp (abs_eq_zero.mp
    ((Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ abs_nonneg _)).mp hzero f hf))⟩

/-- A normalized real lattice homomorphism on continuous functions is evaluation at a point. -/
private lemma continuousFunction_exists_eq_hom {K : Type u} [TopologicalSpace K]
    [CompactSpace K] [Nonempty K] (F : VecLatHom C(K, ℝ) ℝ) (hF : F 1 = 1) :
    ∃ x, ∀ f, F f = f x := by
  obtain ⟨x, hx⟩ := CompactSpace.iInter_nonempty
    (t := fun f : C(K, ℝ) ↦ {x | f x = F f})
    (fun f ↦ isClosed_eq f.continuous continuous_const)
    (fun s ↦ by
      obtain ⟨x, hx⟩ := continuousFunction_exists_eq_hom_on_finset F hF s
      exact ⟨x, Set.mem_iInter₂.mpr hx⟩)
  exact ⟨x, fun f ↦ (Set.mem_iInter.mp hx f).symm⟩

/-- Every real lattice homomorphism on continuous functions is point evaluation multiplied by
its value on the constant one. -/
private lemma continuousFunction_exists_weighted_eval {K : Type u} [TopologicalSpace K]
    [CompactSpace K] [Nonempty K] (F : VecLatHom C(K, ℝ) ℝ) :
    ∃ x, ∀ f, F f = F 1 * f x := by
  have hpos : 0 ≤ F 1 := F.map_nonneg (fun _ ↦ zero_le_one)
  by_cases hzero : F 1 = 0
  · refine ⟨Classical.arbitrary K, fun f ↦ ?_⟩
    have hbound : |f| ≤ ‖f‖ • (1 : C(K, ℝ)) := fun x ↦ by
      simpa using f.norm_coe_le_norm x
    have hsmall : |F f| ≤ 0 := by
      simpa [F.map_abs, map_smul, hzero] using F.monotone hbound
    simpa [hzero] using abs_nonpos_iff.mp hsmall
  · let G := VecLatHom.ofAbs ((F 1)⁻¹ • F.toLinearMap) (by
      intro f
      change (F 1)⁻¹ * F |f| = |(F 1)⁻¹ * F f|
      rw [F.map_abs, abs_mul, abs_of_nonneg (inv_nonneg.mpr hpos)])
    have hG : G 1 = 1 := inv_mul_cancel₀ hzero
    obtain ⟨x, hx⟩ := continuousFunction_exists_eq_hom G hG
    exact ⟨x, fun f ↦ (inv_mul_eq_iff_eq_mul₀ hzero).mp (hx f)⟩

/-- A scalar character on a dense unital sublattice is a weighted point evaluation in its
continuous-function representation. -/
lemma exists_weighted_eval_of_dense_unital {X K : Type u}
    [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X]
    [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (j : VecLatHom X C(K, ℝ)) (hj : Function.Injective j) (hd : DenseRange j)
    {e : X} (he : j e = 1) (F : VecLatHom X ℝ) :
    ∃ t, ∀ x, F x = F e * j x t := by
  obtain ⟨S, hS, hSj⟩ := exists_orderUnit_extension j hj hd he F
  obtain ⟨t, ht⟩ := continuousFunction_exists_weighted_eval (hS.mk' S)
  refine ⟨t, fun x ↦ ?_⟩
  simpa only [IsVecLatHom.mk'_apply, ← he, hSj] using ht (j x)

section GeneratedRepresentations

variable {I : Type u} {E : I → Type u}
  [∀ i, AddCommGroup (E i)] [∀ i, Lattice (E i)]
  [∀ i, IsOrderedAddMonoid (E i)] [∀ i, VectorLattice (E i)]
  [∀ i, IsVLArchimedean (E i)]
  {Y : Type u} [AddCommGroup Y] [Lattice Y]
  [IsOrderedAddMonoid Y] [VectorLattice Y]

/-- The factor inclusions generate the entire Archimedean free product. -/
private lemma ArchimedeanFreeProduct.mem_generated (P : ArchimedeanFreeProduct E)
    (z : P.Carrier) :
    z ∈ VectorSublattice.generated (Set.range (fun x : Sigma E ↦ P.inclusion x.1 x.2)) := by
  let A := VectorSublattice.generated (Set.range (fun x : Sigma E ↦ P.inclusion x.1 x.2))
  let T (i) : VecLatHom (E i) A :=
    { (P.inclusion i).toLinearMap.codRestrict A.toSubmodule
        (fun x ↦ VectorSublattice.subset_generated _ ⟨⟨i, x⟩, rfl⟩) with
      map_sup' := fun x y ↦ Subtype.ext (map_sup (P.inclusion i) x y)
      map_inf' := fun x y ↦ Subtype.ext (map_inf (P.inclusion i) x y) }
  obtain ⟨R, hR, _⟩ := P.universal A T
  have h : A.subtype.comp R = VecLatHom.id := P.hom_ext (fun i x ↦
    congrArg Subtype.val (hR i x))
  have hz := (R z).property
  rwa [show (R z).val = z from DFunLike.congr_fun h z] at hz

/-- An injective representation of an Archimedean free product identifies it with the
sublattice generated by the represented factors. -/
lemma ArchimedeanFreeProduct.equiv_generated_of_injective
    (P : ArchimedeanFreeProduct E) (j : ∀ i, E i → Y)
    (S : VecLatHom P.Carrier Y) (hS : ∀ i x, S (P.inclusion i x) = j i x)
    (hinj : Function.Injective S) :
    let G := VectorSublattice.generated (Set.range (fun x : Sigma E ↦ j x.1 x.2))
    ∃ e : VecLatEquiv P.Carrier G, ∀ x, (e x : Y) = S x := by
  let G := VectorSublattice.generated (Set.range (fun x : Sigma E ↦ j x.1 x.2))
  have hm (x : P.Carrier) : S x ∈ G :=
    map_mem_generated S (Set.range (fun x : Sigma E ↦ P.inclusion x.1 x.2))
      (Set.range (fun x : Sigma E ↦ j x.1 x.2))
      (fun _ hx ↦ hx.elim (fun a ha ↦
        ⟨a, (hS a.1 a.2).symm.trans (congrArg S ha)⟩)) x (P.mem_generated x)
  let R : VectorSublattice Y := VectorSublattice.ofAbsClosed S.toLinearMap.range
    (fun _ hx ↦ hx.elim (fun x hx ↦ ⟨|x|, (S.map_abs x).trans (congrArg abs hx)⟩))
  have hG : G ≤ R := VectorSublattice.generated_le (fun _ hx ↦ hx.elim
    (fun a ha ↦ ⟨P.inclusion a.1 a.2, (hS a.1 a.2).trans ha⟩))
  exact ⟨{ LinearEquiv.ofBijective (S.toLinearMap.codRestrict G.toSubmodule hm)
      ⟨fun _ _ h ↦ hinj (congrArg Subtype.val h),
        fun y ↦ (hG y.property).elim (fun x hx ↦ ⟨x, Subtype.ext hx⟩)⟩ with
      map_sup' := fun x y ↦ Subtype.ext (map_sup S x y)
      map_inf' := fun x y ↦ Subtype.ext (map_inf S x y) }, fun _ ↦ rfl⟩

end GeneratedRepresentations

section FiniteSubfamilies

variable {I : Type u} {E : I → Type u}
  [∀ i, AddCommGroup (E i)] [∀ i, Lattice (E i)]
  [∀ i, IsOrderedAddMonoid (E i)] [∀ i, VectorLattice (E i)]
  [∀ i, IsVLArchimedean (E i)]

/-- Every element of an Archimedean free product is a finite lattice expression in included
factor elements. -/
private lemma ArchimedeanFreeProduct.exists_expression (P : ArchimedeanFreeProduct E)
    (z : P.Carrier) :
    ∃ (n : ℕ) (i : Fin n → I) (x : ∀ j, E (i j)) (e : LLexpr n),
      z = LLexpr.eval (fun j ↦ P.inclusion (i j) (x j)) e := by
  classical
  have hz := P.mem_generated z
  change z ∈ (VectorSublattice.generated
    (Set.range (fun x : Sigma E ↦ P.inclusion x.1 x.2)) : Set P.Carrier) at hz
  rw [LLexpr.generated_eq_iUnion_combinations] at hz
  simp only [Set.mem_iUnion, LLexpr.combinations, Set.mem_range] at hz
  obtain ⟨n, x, e, he⟩ := hz
  choose y hy using fun j ↦ (x j).property
  exact ⟨n, fun j ↦ (y j).1, fun j ↦ (y j).2, e,
    he.symm.trans (congrArg (fun a : Fin n → P.Carrier ↦ LLexpr.eval a e)
      (funext fun j ↦ (hy j).symm))⟩

/-- Each element of an Archimedean free product comes from a free product of finitely many
factors. -/
lemma ArchimedeanFreeProduct.exists_finite_subfamily_lift (P : ArchimedeanFreeProduct E)
    (z : P.Carrier) :
    ∃ (s : Finset I) (R : ArchimedeanFreeProduct (fun i : s ↦ E i.val))
      (U : VecLatHom R.Carrier P.Carrier),
      (∀ i x, U (R.inclusion i x) = P.inclusion i.val x) ∧ ∃ x, U x = z := by
  classical
  obtain ⟨n, i, x, e, he⟩ := P.exists_expression z
  let s := Finset.univ.image i
  let j (k : Fin n) : s := ⟨i k, Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩⟩
  obtain ⟨R⟩ := nonempty_archimedeanFreeProduct (fun i : s ↦ E i.val)
  obtain ⟨U, hU, _⟩ := R.universal P.Carrier (fun i ↦ P.inclusion i.val)
  refine ⟨s, R, U, hU, LLexpr.eval (fun k ↦ R.inclusion (j k) (x k)) e, ?_⟩
  rw [LLexpr.map_eval]
  exact (congrArg (fun a : Fin n → P.Carrier ↦ LLexpr.eval a e)
    (funext fun k ↦ hU (j k) (x k))).trans he.symm

end FiniteSubfamilies

end VectorLattice
