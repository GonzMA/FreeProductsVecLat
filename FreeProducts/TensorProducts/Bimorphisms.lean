/-
Authors: Gonzalo Martínez-Fernández
-/

import BanLat.Bidual
import BanLat.AMSpace.Kakutani
import BanLat.Operators.Hom
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.UrysohnsLemma

/-!
# Lattice bimorphisms and an auxiliary tensor model

Lattice bimorphisms preserve moduli in both arguments. Principal-ideal restrictions and
scalar separation apply to general vector lattices, with Archimedeanness where required.
For Banach factors, rank-one operators from the first dual into the second bidual provide
an auxiliary nonvanishing bimorphism. Its regular-norm completion supplies the ambient
Banach lattice; this is distinct from the projective tensor completion.
-/

universe u

namespace VectorLattice

section Bimorphisms

variable {E F G : Type u}
  [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [VectorLattice E]
  [AddCommGroup F] [Lattice F] [IsOrderedAddMonoid F] [VectorLattice F]
  [AddCommGroup G] [Lattice G] [IsOrderedAddMonoid G] [VectorLattice G]

/-- A bilinear map is a lattice bimorphism when it preserves absolute values
simultaneously in both arguments. -/
def IsLatticeBimorphism (b : E →ₗ[ℝ] (F →ₗ[ℝ] G)) : Prop :=
  ∀ x y, |b x y| = b |x| |y|

end Bimorphisms

end VectorLattice

namespace BanachLattice.FreeProduct

variable (E F : Type u)
  [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
  [NormedAddCommGroup F] [Lattice F] [IsOrderedAddMonoid F] [BanachLattice F]

/-- A bounded tensor pairing with the lattice and positivity properties
needed for induced free-product embeddings. -/
structure TensorPairing where
  Carrier : Type u
  [normedAddCommGroup : NormedAddCommGroup Carrier]
  [lattice : Lattice Carrier]
  [isOrderedAddMonoid : IsOrderedAddMonoid Carrier]
  [banachLattice : BanachLattice Carrier]
  tmul : E →L[ℝ] (F →L[ℝ] Carrier)
  isVecLatHom_left :
    ∀ y, 0 ≤ y → IsVecLatHom (fun x ↦ tmul x y)
  isVecLatHom_right :
    ∀ x, 0 ≤ x → IsVecLatHom (tmul x)
  tmul_pos :
    ∀ x y, 0 < x → 0 < y → 0 < tmul x y

attribute [instance] TensorPairing.normedAddCommGroup TensorPairing.lattice
  TensorPairing.isOrderedAddMonoid TensorPairing.banachLattice

section Operators

variable {D Z : Type u}
  [NormedAddCommGroup D] [Lattice D] [IsOrderedAddMonoid D] [BanachLattice D]
  [NormedAddCommGroup Z] [ConditionallyCompleteLattice Z]
  [IsOrderedAddMonoid Z] [BanachLattice Z]

/-- Regards an order-bounded operator between the given Banach lattices as a continuous linear
map. -/
private noncomputable def operatorCLM (T : OrderBoundedHom D Z) : D →L[ℝ] Z :=
  ⟨T.toLinearMap, T.isOrderBounded'.continuous⟩

/-- The linear map forgetting order-boundedness and retaining the underlying continuous
operator. -/
private noncomputable def operatorCLMMap : OrderBoundedHom D Z →ₗ[ℝ] (D →L[ℝ] Z) where
  toFun := operatorCLM
  map_add' _ _ := ContinuousLinearMap.ext (fun _ ↦ rfl)
  map_smul' _ _ := ContinuousLinearMap.ext (fun _ ↦ rfl)

/-- Passing to the underlying continuous operator does not identify distinct order-bounded
operators. -/
private lemma operatorCLMMap_injective :
    Function.Injective (operatorCLMMap : OrderBoundedHom D Z →ₗ[ℝ] (D →L[ℝ] Z)) :=
  fun _ _ h ↦ OrderBoundedHom.ext (fun x ↦ DFunLike.congr_fun h x)

end Operators

/-- A common order bound for scalar multiples persists when the scalar reaches the supremum of
a nonempty set. -/
private lemma scalar_isLUB_smul_le
    {Z : Type u} [NormedAddCommGroup Z] [Lattice Z] [IsOrderedAddMonoid Z]
    [BanachLattice Z] {s : Set ℝ} {r : ℝ} (hs : IsLUB s r) (hne : s.Nonempty)
    (y z : Z) (h : ∀ a ∈ s, a • y ≤ z) : r • y ≤ z :=
  (closure_minimal h (isClosed_le (continuous_id.smul continuous_const) continuous_const))
    (hs.mem_closure hne)

section RankOne

variable {D Z : Type u}
  [NormedAddCommGroup D] [Lattice D] [IsOrderedAddMonoid D] [BanachLattice D]
  [NormedAddCommGroup Z] [ConditionallyCompleteLattice Z]
  [IsOrderedAddMonoid Z] [BanachLattice Z]

/-- The rank-one order-bounded operator sending a vector to its value under a functional times
a fixed target vector. -/
private noncomputable def rankOne (a : StrongDual ℝ D) (y : Z) : OrderBoundedHom D Z := by
  refine ⟨a.toLinearMap.smulRight y, ?_⟩
  intro x hx
  obtain ⟨c, hc, hbound⟩ := StrongDual.isOrderBounded a x hx
  refine ⟨c • |y|, smul_nonneg hc (abs_nonneg y), fun z hz ↦ ?_⟩
  simpa only [LinearMap.smulRight_apply, abs_smul'] using
    smul_le_smul_of_nonneg_right (hbound z hz) (abs_nonneg y)

/-- The modulus of a rank-one operator is the rank-one operator formed from the moduli of its
functional and target vector. -/
private lemma rankOne_abs (a : StrongDual ℝ D) (y : Z) :
    |rankOne a y| = rankOne |a| |y| := by
  apply le_antisymm
  · apply OrderBoundedHom.le_iff.mpr
    intro x hx
    refine (OrderBoundedHom.isLUB_abs_apply (f := rankOne a y) hx).2 ?_
    rintro _ ⟨z, hz, rfl⟩
    change |a z • y| ≤ (|a|) x • |y|
    rw [abs_smul']
    exact smul_le_smul_of_nonneg_right
      ((OrderDualSpace.isLUB_abs_apply (φ := StrongDual.toOrderDualSpace a) hx).1
        ⟨z, hz, rfl⟩) (abs_nonneg y)
  · apply OrderBoundedHom.le_iff.mpr
    intro x hx
    have hs := OrderDualSpace.isLUB_abs_apply (φ := StrongDual.toOrderDualSpace a) hx
    change IsLUB {r : ℝ | ∃ z : D, |z| ≤ x ∧ r = |a z|} ((|a|) x) at hs
    refine scalar_isLUB_smul_le hs ⟨0, 0, by simpa using hx, by simp⟩ |y|
      ((|rankOne a y|) x) ?_
    rintro _ ⟨z, hz, rfl⟩
    have h := (OrderBoundedHom.isLUB_abs_apply (f := rankOne a y) hx).1 ⟨z, hz, rfl⟩
    change |a z • y| ≤ _ at h
    simpa only [abs_smul'] using h

end RankOne

/-- For positive order-bounded operators, pointwise order domination implies domination of the
underlying operator norms. -/
private lemma operatorCLM_norm_mono
    {D Z : Type u} [NormedAddCommGroup D] [Lattice D] [IsOrderedAddMonoid D]
    [BanachLattice D] [NormedAddCommGroup Z] [ConditionallyCompleteLattice Z]
    [IsOrderedAddMonoid Z] [BanachLattice Z]
    {T S : OrderBoundedHom D Z} (hT : 0 ≤ T) (hTS : T ≤ S) :
    ‖operatorCLMMap T‖ ≤ ‖operatorCLMMap S‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun x ↦ ?_)
  have hp : Positive T.toLinearMap := fun z hz ↦ by
    change 0 ≤ T z
    exact OrderBoundedHom.le_iff.mp hT z hz
  have hpoint : |T x| ≤ S |x| :=
    (Positive.abs_le_map_abs hp x).trans
      (OrderBoundedHom.le_iff.mp hTS |x| (abs_nonneg x))
  exact (norm_le_norm_of_abs_le_abs (hpoint.trans (le_abs_self _))).trans
    (((operatorCLMMap S).le_opNorm |x|).trans_eq (by rw [norm_abs_eq_norm]))

section RegularNorm

variable {D Z : Type u}
  [NormedAddCommGroup D] [Lattice D] [IsOrderedAddMonoid D] [BanachLattice D]
  [NormedAddCommGroup Z] [ConditionallyCompleteLattice Z]
  [IsOrderedAddMonoid Z] [BanachLattice Z]

/-- The regular operator norm is the operator norm of the modulus of the operator. -/
private noncomputable instance regularOperatorNorm : Norm (OrderBoundedHom D Z) where
  norm T := ‖operatorCLMMap |T|‖

/-- Verifies the norm axioms for the regular operator norm. -/
private lemma regular_operator_norm_core : NormedSpace.Core ℝ (OrderBoundedHom D Z) where
  norm_nonneg T := norm_nonneg (operatorCLMMap |T|)
  norm_smul c T := by
    change ‖operatorCLMMap |c • T|‖ = ‖c‖ * ‖operatorCLMMap |T|‖
    simp only [abs_smul', map_smul, norm_smul, Real.norm_eq_abs, abs_abs]
  norm_triangle T S := by
    refine (operatorCLM_norm_mono (abs_nonneg (T + S)) (abs_add_le T S)).trans ?_
    rw [map_add]
    exact norm_add_le _ _
  norm_eq_zero_iff T := by
    change ‖operatorCLMMap |T|‖ = 0 ↔ T = 0
    constructor
    · intro h
      exact (abs_eq_zero_iff_zero T).mp (operatorCLMMap_injective
        ((norm_eq_zero.mp h).trans (map_zero operatorCLMMap).symm))
    · rintro rfl
      simp only [abs_zero, map_zero, norm_zero]

/-- The regular operator norm makes the order-bounded operators a normed additive group. -/
private noncomputable instance regularOperatorNormedAddCommGroup :
    NormedAddCommGroup (OrderBoundedHom D Z) :=
  NormedAddCommGroup.ofCore regular_operator_norm_core

/-- The regular operator norm is a lattice norm compatible with the real vector structure. -/
private noncomputable instance regularOperatorNormedVectorLattice :
    NormedVectorLattice (OrderBoundedHom D Z) where
  solid {_ _} h := operatorCLM_norm_mono (abs_nonneg _) h
  norm_smul := regular_operator_norm_core.norm_smul

/-- The regular norm of a rank-one operator is the product of the functional norm and vector
norm. -/
private lemma rankOne_norm (a : StrongDual ℝ D) (y : Z) :
    ‖rankOne a y‖ = ‖a‖ * ‖y‖ := by
  change ‖operatorCLMMap |rankOne a y|‖ = ‖a‖ * ‖y‖
  rw [rankOne_abs]
  change ‖ContinuousLinearMap.smulRight |a| |y|‖ = ‖a‖ * ‖y‖
  simp only [ContinuousLinearMap.norm_smulRight_apply, norm_abs_eq_norm]

/-- Packages the rank-one construction as a bilinear map. -/
private noncomputable def rankBilinear :
    StrongDual ℝ D →ₗ[ℝ] Z →ₗ[ℝ] OrderBoundedHom D Z where
  toFun a :=
    { toFun := rankOne a
      map_add' y z := OrderBoundedHom.ext (fun x ↦ smul_add (a x) y z)
      map_smul' c y := OrderBoundedHom.ext (fun x ↦ smul_comm (a x) c y) }
  map_add' a b := LinearMap.ext (fun y ↦
    OrderBoundedHom.ext (fun x ↦ add_smul (a x) (b x) y))
  map_smul' c a := LinearMap.ext (fun y ↦
    OrderBoundedHom.ext (fun x ↦ mul_smul c (a x) y))

/-- The rank-one bilinear map is bounded and hence continuous in the bilinear operator norm. -/
private noncomputable def rankContinuous :
    StrongDual ℝ D →L[ℝ] Z →L[ℝ] OrderBoundedHom D Z :=
  rankBilinear.mkContinuous₂ 1 (fun a y ↦ by
    change ‖rankOne a y‖ ≤ 1 * ‖a‖ * ‖y‖
    simp only [rankOne_norm, one_mul, le_refl])

end RegularNorm

/-- Pairs the factors as rank-one operators using their bidual embeddings, then includes these
operators into their norm completion. -/
private noncomputable def completedPairing :
    E →L[ℝ] F →L[ℝ]
      UniformSpace.Completion (OrderBoundedHom (StrongDual ℝ E) (BidualSpace F)) :=
  (ContinuousLinearMap.compL ℝ F (OrderBoundedHom (StrongDual ℝ E) (BidualSpace F))
    (UniformSpace.Completion (OrderBoundedHom (StrongDual ℝ E) (BidualSpace F)))
    UniformSpace.Completion.toComplₗᵢ.toContinuousLinearMap).comp
    (rankContinuous.bilinearComp (BidualSpace.inclusion (X := E))
      (BidualSpace.inclusion (X := F)))

/-- The completed rank-one pairing has norm equal to the product of the two factor norms. -/
lemma completedPairing_norm (x : E) (y : F) :
    ‖completedPairing E F x y‖ = ‖x‖ * ‖y‖ := by
  change ‖(rankOne (BidualSpace.inclusion x) (BidualSpace.inclusion y) :
    UniformSpace.Completion (OrderBoundedHom (StrongDual ℝ E) (BidualSpace F)))‖ = _
  rw [UniformSpace.Completion.norm_coe, rankOne_norm,
    BidualSpace.norm_inclusion, BidualSpace.norm_inclusion]

/-- Taking absolute values commutes with the completed rank-one pairing. -/
lemma completedPairing_abs (x : E) (y : F) :
    |completedPairing E F x y| = completedPairing E F |x| |y| := by
  change |(rankOne (BidualSpace.inclusion x) (BidualSpace.inclusion y) :
    UniformSpace.Completion (OrderBoundedHom (StrongDual ℝ E) (BidualSpace F)))| =
    (rankOne (BidualSpace.inclusion |x|) (BidualSpace.inclusion |y|) :
      UniformSpace.Completion (OrderBoundedHom (StrongDual ℝ E) (BidualSpace F)))
  rw [← coe_abs_completion, rankOne_abs,
    BidualSpace.inclusion_abs, BidualSpace.inclusion_abs]

/-- Pairing two nonzero vectors in the completed rank-one model gives a nonzero element. -/
lemma completedPairing_ne_zero {x : E} {y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    completedPairing E F x y ≠ 0 := by
  intro h
  have hn := congrArg norm h
  rw [completedPairing_norm, norm_zero] at hn
  exact (mul_ne_zero (norm_ne_zero_iff.mpr hx) (norm_ne_zero_iff.mpr hy)) hn

/-- Packages the completed rank-one construction with the bilinear, lattice, norm, and
nonvanishing properties needed for tensor arguments. -/
noncomputable def rankOnePairing : TensorPairing E F := by
  have hleft (y : F) (hy : 0 ≤ y) : IsVecLatHom (fun x ↦ completedPairing E F x y) := by
    refine (VecLatHom.ofAbs ((completedPairing E F).flip y).toLinearMap (fun x ↦ ?_)).isVecLatHom
    change completedPairing E F |x| y = |completedPairing E F x y|
    simpa only [abs_of_nonneg hy] using (completedPairing_abs E F x y).symm
  have hright (x : E) (hx : 0 ≤ x) : IsVecLatHom (completedPairing E F x) := by
    refine (VecLatHom.ofAbs (completedPairing E F x).toLinearMap (fun y ↦ ?_)).isVecLatHom
    change completedPairing E F x |y| = |completedPairing E F x y|
    simpa only [abs_of_nonneg hx] using (completedPairing_abs E F x y).symm
  refine
    { Carrier := UniformSpace.Completion
        (OrderBoundedHom (StrongDual ℝ E) (BidualSpace F))
      tmul := completedPairing E F
      isVecLatHom_left := hleft
      isVecLatHom_right := hright
      tmul_pos := fun x y hx hy ↦ ?_ }
  exact lt_of_le_of_ne
    (((hleft y hy.le).mk' (fun x ↦ completedPairing E F x y)).map_nonneg hx.le)
    (completedPairing_ne_zero E F (ne_of_gt hx) (ne_of_gt hy)).symm

/-- Every pair of Banach lattices admits such a tensor pairing. -/
theorem nonempty_tensorPairing : Nonempty (TensorPairing E F) := by
  exact ⟨rankOnePairing E F⟩

end BanachLattice.FreeProduct

namespace BanachLattice.FreeProduct.ProjectiveTensor

section ScalarBimorphisms

variable (E F : Type u)
  [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [VectorLattice E]
  [AddCommGroup F] [Lattice F] [IsOrderedAddMonoid F] [VectorLattice F]

/-- For a scalar lattice bimorphism, vanishing at a positive majorant forces vanishing at
every vector it dominates in the second argument. -/
private lemma scalar_bimorphism_zero_of_bound (b : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    (hb : ∀ x y, |b x y| = b |x| |y|) {x : E} {y f : F} {r : ℝ}
    (hf : 0 ≤ f) (hy : |y| ≤ r • f) (hz : b x f = 0) : b x y = 0 := by
  have hp : Positive (b |x|) := by
    intro v hv
    simpa only [abs_abs, abs_of_nonneg hv] using
      (abs_nonneg (b |x| v)).trans_eq (hb |x| v)
  have h := (Positive.monotone_iff.mpr hp) hy
  have hxf : b |x| f = 0 := by
    simpa only [abs_of_nonneg hf, hz, abs_zero] using (hb x f).symm
  rw [← hb x y, map_smul, hxf, smul_zero] at h
  exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))

/-- A scalar lattice bimorphism satisfies the cross-multiplication identity giving local
separation of its two arguments. -/
lemma scalar_bimorphism_factor (b : E →ₗ[ℝ] F →ₗ[ℝ] ℝ)
    (hb : ∀ x y, |b x y| = b |x| |y|) (x e : E) {y f : F} {r : ℝ}
    (hf : 0 ≤ f) (hy : |y| ≤ r • f) (he : b e f ≠ 0) :
    b x y * b e f = b x f * b e y := by
  let c := b x f / b e f
  have hz : b (x - c • e) f = 0 := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    exact sub_eq_zero.mpr (div_mul_cancel₀ (b x f) he).symm
  have h := scalar_bimorphism_zero_of_bound E F b hb hf hy hz
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul] at h
  rw [sub_eq_zero.mp h]
  dsimp [c]
  field_simp

end ScalarBimorphisms

section PrincipalBimorphisms

variable {A B G : Type u}
  [AddCommGroup A] [Lattice A] [IsOrderedAddMonoid A] [VectorLattice A]
  [AddCommGroup B] [Lattice B] [IsOrderedAddMonoid B] [VectorLattice B]
  [AddCommGroup G] [Lattice G] [IsOrderedAddMonoid G] [VectorLattice G]

/-- A lattice bimorphism is nonnegative on pairs of nonnegative vectors. -/
lemma bimorphism_nonneg (b : A →ₗ[ℝ] B →ₗ[ℝ] G)
    (hb : ∀ x y, |b x y| = b |x| |y|) {x : A} {y : B}
    (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ b x y := by
  simpa only [abs_of_nonneg hx, abs_of_nonneg hy] using (abs_nonneg (b x y)).trans_eq (hb x y)

/-- Order bounds on the two arguments give the corresponding product bound on the absolute
value of a lattice bimorphism. -/
private lemma bimorphism_bound (b : A →ₗ[ℝ] B →ₗ[ℝ] G)
    (hb : ∀ x y, |b x y| = b |x| |y|) {x e : A} {y f : B} {r s : ℝ}
    (he : 0 ≤ e) (hr : 0 ≤ r) (hx : |x| ≤ r • e) (hy : |y| ≤ s • f) :
    |b x y| ≤ (r * s) • b e f := by
  have hl : Positive (b.flip |y|) := fun z hz ↦ bimorphism_nonneg b hb hz (abs_nonneg y)
  have hr' : Positive (b e) := fun z hz ↦ bimorphism_nonneg b hb he hz
  have h := (Positive.monotone_iff.mpr hl) hx
  have k := smul_le_smul_of_nonneg_left ((Positive.monotone_iff.mpr hr') hy) hr
  calc
    |b x y| = b |x| |y| := hb x y
    _ ≤ r • b e |y| := by simpa using h
    _ ≤ (r * s) • b e f := by simpa [smul_smul] using k

/-- A lattice bimorphism maps a pair of principal ideals into the ideal generated by the image
of their generators. -/
private lemma bimorphism_mem_principal (b : A →ₗ[ℝ] B →ₗ[ℝ] G)
    (hb : ∀ x y, |b x y| = b |x| |y|) {e : A} {f : B} (he : 0 ≤ e) (hf : 0 ≤ f)
    {x : A} {y : B} (hx : x ∈ OrderIdeal.principal e) (hy : y ∈ OrderIdeal.principal f) :
    b x y ∈ OrderIdeal.principal (b e f) := by
  obtain ⟨r, hr, hx⟩ := OrderIdeal.mem_principal.mp hx
  obtain ⟨s, hs, hy⟩ := OrderIdeal.mem_principal.mp hy
  rw [abs_of_nonneg he] at hx
  rw [abs_of_nonneg hf] at hy
  exact OrderIdeal.mem_principal.mpr ⟨r * s, mul_nonneg hr hs,
    by simpa only [abs_of_nonneg (bimorphism_nonneg b hb he hf)] using
      bimorphism_bound b hb he hr hx hy⟩

/-- Restricts a lattice bimorphism to principal ideals in both arguments and its corresponding
principal target ideal. -/
noncomputable def principalBimorphism (b : A →ₗ[ℝ] B →ₗ[ℝ] G)
    (hb : ∀ x y, |b x y| = b |x| |y|) {e : A} {f : B} (he : 0 ≤ e) (hf : 0 ≤ f) :
    (OrderIdeal.principal e).toVectorSublattice →ₗ[ℝ]
      (OrderIdeal.principal f).toVectorSublattice →ₗ[ℝ]
        (OrderIdeal.principal (b e f)).toVectorSublattice where
  toFun x :=
    { toFun y := ⟨b x.val y.val, bimorphism_mem_principal b hb he hf x.property y.property⟩
      map_add' y z := Subtype.ext (map_add (b x.val) y.val z.val)
      map_smul' c y := Subtype.ext (map_smul (b x.val) c y.val) }
  map_add' x z := LinearMap.ext (fun y ↦ Subtype.ext
    (DFunLike.congr_fun (map_add b x.val z.val) y.val))
  map_smul' c x := LinearMap.ext (fun y ↦ Subtype.ext
    (DFunLike.congr_fun (map_smul b c x.val) y.val))

/-- The principal ideal of a strictly positive vector is nontrivial. -/
lemma principal_nontrivial {e : G} (he : 0 < e) :
    Nontrivial (OrderIdeal.principal e).toVectorSublattice :=
  ⟨⟨⟨e, OrderIdeal.self_mem_principal e⟩, 0,
    fun h ↦ he.ne' (congrArg Subtype.val h)⟩⟩

/-- The principal ideal generated by zero contains only zero. -/
lemma principal_eq_zero {e : G} (he : e = 0)
    (x : (OrderIdeal.principal e).toVectorSublattice) : x = 0 := by
  apply Subtype.ext
  obtain ⟨r, _, hx⟩ := OrderIdeal.mem_principal.mp x.property
  exact (abs_eq_zero_iff_zero x.val).mp
    (le_antisymm (by simpa [he] using hx) (abs_nonneg x.val))

/-- A lattice expression vanishes if all its input vectors vanish. -/
lemma expression_zero_of_variables {n : ℕ} (p : Fin n → G) (a : LLexpr n)
    (hp : ∀ i, p i = 0) : LLexpr.eval p a = 0 := by
  induction a <;> simp_all [LLexpr.eval]

end PrincipalBimorphisms

/-- Any finite family of vectors is contained in a single principal ideal with a nonnegative
generator. -/
lemma exists_principal_family {A : Type u} [AddCommGroup A] [Lattice A]
    [IsOrderedAddMonoid A] [VectorLattice A] {n : ℕ} (p : Fin n → A) :
    ∃ e : A, 0 ≤ e ∧ ∀ i, p i ∈ OrderIdeal.principal e := by
  have he : 0 ≤ ∑ i, |p i| := Finset.sum_nonneg (fun i _ ↦ abs_nonneg (p i))
  refine ⟨∑ i, |p i|, he, fun i ↦ OrderIdeal.mem_principal.mpr ⟨1, zero_le_one, ?_⟩⟩
  simpa only [abs_of_nonneg he, one_smul] using
    Finset.single_le_sum (fun j _ ↦ abs_nonneg (p j)) (Finset.mem_univ i)

section OrderUnitSeparation

variable {D : Type u} [NormedAddCommGroup D] [Lattice D] [IsOrderedAddMonoid D]
  [NormedVectorLattice D]

/-- Embeds an order-unit normed lattice into the principal ideal generated by its unit in the
norm completion. -/
private noncomputable def completionPrincipalEmbedding (e : D) (he : StrongOrderUnit e) :
    VecLatHom D (OrderIdeal.principal (e : UniformSpace.Completion D)).toVectorSublattice := by
  let T : VecLatHom D (UniformSpace.Completion D) := toCompletionVecLatHom
  have hmem (x : D) : T x ∈ OrderIdeal.principal (T e) := by
    obtain ⟨c, hc, hx⟩ := he.2 x
    refine OrderIdeal.mem_principal.mpr ⟨c, hc, ?_⟩
    simpa only [T.map_abs, map_smul, abs_of_nonneg (T.map_nonneg he.1)] using T.monotone hx
  exact { T.toLinearMap.codRestrict (OrderIdeal.principal (T e)).toSubmodule hmem with
    map_sup' := fun x y ↦ Subtype.ext (map_sup T x y)
    map_inf' := fun x y ↦ Subtype.ext (map_inf T x y) }

/-- Normalized scalar characters separate nonzero elements of a normed lattice with a positive
strong unit. -/
private lemma order_unit_separates (e : D) (he : StrongOrderUnit e) (hepos : 0 < e)
    {x : D} (hx : x ≠ 0) : ∃ φ : VecLatHom D ℝ, φ e = 1 ∧ φ x ≠ 0 := by
  let C := UniformSpace.Completion D
  have heC : 0 < (e : C) := by
    simpa only [map_zero, coe_toCompletionVecLatHom] using
      ((toCompletionVecLatHom : VecLatHom D C).monotone.strictMono_of_injective
        (isometry_toCompletionVecLatHom (X := D)).injective) hepos
  let J := (OrderIdeal.principal (e : C)).toVectorSublattice
  let : NormedAddCommGroup J := OrderIdeal.principalNormedAddCommGroup (e : C)
  let : IsUniformlyCompleteVectorLattice C :=
    isUniformlyCompleteVectorLattice_of_banachLattice C
  let : AMSpaceWithUnit J := OrderIdeal.principalAMSpaceWithUnit heC.le
    (IsUniformlyCompleteVectorLattice.complete_principal (e : C) heC)
  let j : VecLatHom D J := completionPrincipalEmbedding e he
  have hjx : j x ≠ 0 := by
    intro h
    exact hx ((isometry_coe_completion (X := D)).injective (congrArg Subtype.val h))
  let : Nontrivial J := ⟨⟨j x, 0, hjx⟩⟩
  obtain ⟨φ, hφ⟩ := AMSpaceWithUnit.LatticeCharacter.exists_abs_apply_eq_norm (X := J) (j x)
  refine ⟨φ.toVecLatHom.comp j, φ.map_unit, ?_⟩
  intro h
  change φ (j x) = 0 at h
  exact hjx (norm_eq_zero.mp (hφ.symm.trans (by rw [h, abs_zero])))

end OrderUnitSeparation

/-- Normalized scalar characters separate nonzero elements of a principal ideal in an
Archimedean lattice. -/
lemma principal_separates {G : Type u} [AddCommGroup G] [Lattice G]
    [IsOrderedAddMonoid G] [VectorLattice G] [IsVLArchimedean G] {e : G} (he : 0 < e)
    {x : (OrderIdeal.principal e).toVectorSublattice} (hx : x ≠ 0) :
    ∃ φ : VecLatHom (OrderIdeal.principal e).toVectorSublattice ℝ,
      φ ⟨e, OrderIdeal.self_mem_principal e⟩ = 1 ∧ φ x ≠ 0 := by
  let P := (OrderIdeal.principal e).toVectorSublattice
  let : NormedAddCommGroup P := OrderIdeal.principalNormedAddCommGroup e
  let : NormedVectorLattice P := OrderIdeal.principalNormedVectorLattice e
  let u : P := ⟨e, OrderIdeal.self_mem_principal e⟩
  have hu : StrongOrderUnit u := by
    refine ⟨he.le, ?_⟩
    intro z
    obtain ⟨c, hc, hz⟩ := OrderIdeal.mem_principal.mp z.property
    refine ⟨c, hc, ?_⟩
    exact (show |z.val| ≤ c • e from by simpa only [abs_of_nonneg he.le] using hz)
  exact order_unit_separates u hu he hx

end BanachLattice.FreeProduct.ProjectiveTensor
