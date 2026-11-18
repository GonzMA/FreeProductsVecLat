/-
Authors: Gonzalo Martínez-Fernández
-/

import FreeProducts.Counterexamples.Auxiliary
import FreeProducts.AVLvsVL.Coproducts.Equivalences
import FreeProducts.BanachLattice.Basic
import BanLat.FunctionalCalculus
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Noninjective comparison for free Banach lattice factors

Free Banach lattices over Euclidean spaces of dimensions two and four have an ordinary
vector lattice free product that is not Archimedean. Cone parametrizations realize the
obstruction inside these factors. Consequently, the canonical comparison from the
ordinary free product into the Banach free product is not injective.
-/

noncomputable section

universe u

namespace VectorLattice.Counterexamples

/-- Free Banach lattices over Euclidean spaces of dimensions two and four. -/
abbrev euclideanFreeBanachFactors (b : Bool) :=
  FBL (EuclideanSpace ℝ (Fin (if b then 4 else 2)))

/-- Continuous positively homogeneous functions on finite-dimensional coordinate space embed
into the corresponding free Banach lattice. -/
private lemma posHom_freeBanach_embedding (n : ℕ) :
    ∃ T : VecLatHom (posHomFunctions n) (FBL (EuclideanSpace ℝ (Fin n))),
      Function.Injective T := by
  let := isUniformlyCompleteVectorLattice_of_banachLattice
    (FBL (EuclideanSpace ℝ (Fin n)))
  refine ⟨PosHomFunction.functionalCalculus (fun i ↦ FBL.of (PiLp.single 2 i 1)),
    fun f g h ↦ PosHomFunction.ext (fun x ↦ ?_)⟩
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    ∑ i, x i • PiLp.proj 2 (fun _ : Fin n ↦ ℝ) i
  let V : VecLatHom (posHomFunctions n) ℝ :=
    { toFun := fun a ↦ a x
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      map_sup' := fun _ _ ↦ rfl
      map_inf' := fun _ _ ↦ rfl }
  let := isUniformlyCompleteVectorLattice_of_banachLattice ℝ
  have hL (i : Fin n) : L (PiLp.single 2 i 1) = x i := by
    simp [L, PiLp.proj_apply, PiLp.single_apply]
  have heq : (FBL.lift L).comp
      (PosHomFunction.functionalCalculus (fun i ↦ FBL.of (PiLp.single 2 i 1))) = V :=
    (PosHomFunction.eq_functionalCalculus_of_map_coordinate x _ (fun i ↦ by
      simp only [VecLatHom.comp_apply, PosHomFunction.functionalCalculus_coordinate,
        FBL.lift_of, hL])).trans
      (PosHomFunction.eq_functionalCalculus_of_map_coordinate x V (fun _ ↦ rfl)).symm
  exact (DFunLike.congr_fun heq f).symm.trans
    ((congrArg (FBL.lift L) h).trans (DFunLike.congr_fun heq g))

/-- The circular cone in three coordinates whose height is the Euclidean norm of its first two
coordinates. -/
private def circularCone : ConeRepresentation.ClosedCone 3 where
  carrier := {x | 0 ≤ x 2 ∧ x 2 ^ 2 = x 0 ^ 2 + x 1 ^ 2}
  isClosed := (isClosed_le continuous_const (continuous_apply 2)).inter
    (isClosed_eq ((continuous_apply 2).pow 2)
      (((continuous_apply 0).pow 2).add ((continuous_apply 1).pow 2)))
  zero_mem := by norm_num
  smul_mem := fun r hr x hx ↦ ⟨mul_nonneg hr hx.1, by
    simpa only [Pi.smul_apply, smul_eq_mul, mul_pow, ← mul_add] using
      congrArg (r ^ 2 * ·) hx.2⟩

/-- Two height-one circular-cone points whose midpoint remains on the cone have the same first
coordinate. -/
private lemma circular_section_eq_first {x y : Fin 3 → ℝ}
    (hx : x ∈ circularCone.carrier) (hy : y ∈ circularCone.carrier)
    (hxy : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y ∈ circularCone.carrier)
    (hx₂ : x 2 = 1) (hy₂ : y 2 = 1) : x 0 = y 0 := by
  have hm : ((1 / 2) * x 2 + (1 / 2) * y 2) ^ 2 =
      ((1 / 2) * x 0 + (1 / 2) * y 0) ^ 2 +
        ((1 / 2) * x 1 + (1 / 2) * y 1) ^ 2 := hxy.2
  have hs : (x 0 - y 0) ^ 2 = 0 := by
    nlinarith [hx.2, hy.2, sq_nonneg (x 1 - y 1)]
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)

/-- The stated square-root parametrization gives points in the height-one circular section. -/
private lemma circular_section_point_mem (t : ℝ) (ht : 0 ≤ 1 - t ^ 2) :
    ![t, Real.sqrt (1 - t ^ 2), 1] ∈ circularCone.carrier := by
  norm_num [circularCone, Real.sq_sqrt ht, Matrix.cons_val_two]

/-- The circular cone is not polyhedral, using the infinitely many points in its circular
section. -/
private lemma circularCone_not_polyhedral :
    ¬ ConeRepresentation.IsClosedPolyhedralCone circularCone.carrier := by
  rintro ⟨k, cones, _, hcones⟩
  let p (t : Set.Icc (0 : ℝ) 1) : Fin 3 → ℝ := ![t, Real.sqrt (1 - t.val ^ 2), 1]
  have hp (t : Set.Icc (0 : ℝ) 1) : p t ∈ circularCone.carrier :=
    circular_section_point_mem t (by nlinarith [t.property.1, t.property.2])
  obtain ⟨index, hindex⟩ := Classical.axiomOfChoice (fun t ↦
    Set.mem_iUnion.mp (hcones ▸ hp t))
  have hinj : Function.Injective index := by
    refine fun s t hst ↦ Subtype.ext (circular_section_eq_first (hp s) (hp t) ?_ rfl rfl)
    exact hcones.symm ▸ Set.mem_iUnion.mpr ⟨index s,
      (cones (index s)).convex (hindex s) (hst.symm ▸ hindex t)
        (by norm_num) (by norm_num) (by norm_num)⟩
  exact (Set.Icc_infinite (zero_lt_one : (0 : ℝ) < 1))
    (Set.finite_coe_iff.mp (Finite.of_injective index hinj))

/-- A cone restriction-lattice function is continuous on the cone. -/
private lemma cone_function_continuous {n : ℕ} {C : ConeRepresentation.ClosedCone n}
    (f : ConeRepresentation.ConeFunctions C) : Continuous f.val := by
  obtain ⟨g, hg⟩ := f.property
  exact ((fvl_continuous g).comp continuous_subtype_val).congr (fun x ↦ (hg x).symm)

/-- A cone restriction-lattice function is homogeneous under nonnegative scalar
multiplication. -/
private lemma cone_function_smul {n : ℕ} {C : ConeRepresentation.ClosedCone n}
    (f : ConeRepresentation.ConeFunctions C) (r : ℝ) (hr : 0 ≤ r) (x : C.carrier) :
    f.val ⟨r • x.val, C.smul_mem r hr x.val x.property⟩ = r * f.val x := by
  obtain ⟨g, hg⟩ := f.property
  exact (hg _).trans (((ConeRepresentation.mem_free_iff g).mp g.property).2.1 r hr x.val
    |>.trans (congrArg (r * ·) (hg x).symm))

/-- Pullback by a continuous homogeneous map to a cone gives a lattice homomorphism into
continuous positively homogeneous functions. -/
private def coneFunctionPullback {n m : ℕ} (C : ConeRepresentation.ClosedCone n)
    (q : (Fin m → ℝ) → C.carrier) (hq : Continuous q)
    (hs : ∀ r : ℝ, 0 ≤ r → ∀ x, (q (r • x)).val = r • (q x).val) :
    VecLatHom (ConeRepresentation.ConeFunctions C) (posHomFunctions m) where
  toFun f := ⟨⟨fun x ↦ f.val (q x), (cone_function_continuous f).comp hq⟩,
    fun r hr x ↦ (congrArg f.val (Subtype.ext (hs r hr x))).trans
      (cone_function_smul f r hr (q x))⟩
  map_add' := fun _ _ ↦ PosHomFunction.ext (fun _ ↦ rfl)
  map_smul' := fun _ _ ↦ PosHomFunction.ext (fun _ ↦ rfl)
  map_sup' := fun _ _ ↦ PosHomFunction.ext (fun _ ↦ rfl)
  map_inf' := fun _ _ ↦ PosHomFunction.ext (fun _ ↦ rfl)

/-- A continuous homogeneous surjection onto a cone embeds its restriction lattice into a
finite-dimensional free Banach lattice. -/
private lemma cone_freeBanach_embedding {n m : ℕ} (C : ConeRepresentation.ClosedCone n)
    (q : (Fin m → ℝ) → C.carrier) (hq : Continuous q)
    (hs : ∀ r : ℝ, 0 ≤ r → ∀ x, (q (r • x)).val = r • (q x).val)
    (honto : Function.Surjective q) :
    ∃ T : VecLatHom (ConeRepresentation.ConeFunctions C)
        (FBL (EuclideanSpace ℝ (Fin m))), Function.Injective T := by
  obtain ⟨T, hT⟩ := posHom_freeBanach_embedding m
  refine ⟨T.comp (coneFunctionPullback C q hq hs), fun f g h ↦
    Subtype.ext (funext (fun y ↦ ?_))⟩
  obtain ⟨x, rfl⟩ := honto y
  exact congrArg (fun a : posHomFunctions m ↦ a x) (hT h)

/-- Parametrizes the circular cone by adjoining the Euclidean radius to a point in the plane. -/
private def circularParam (x : Fin 2 → ℝ) : circularCone.carrier :=
  ⟨![x 0, x 1, Real.sqrt (x 0 ^ 2 + x 1 ^ 2)],
    ⟨Real.sqrt_nonneg _, Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))⟩⟩

/-- The circular-cone parametrization is continuous. -/
private lemma continuous_circularParam : Continuous circularParam := by
  unfold circularParam
  fun_prop

/-- The circular-cone parametrization commutes with nonnegative scalar multiplication. -/
private lemma circularParam_smul (r : ℝ) (hr : 0 ≤ r) (x : Fin 2 → ℝ) :
    (circularParam (r • x)).val = r • (circularParam x).val := by
  ext i
  fin_cases i <;> simp [circularParam, Pi.smul_apply, smul_eq_mul, mul_pow,
    ← mul_add, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr, Matrix.cons_val_two]

/-- Every point of the circular cone is attained by the planar parametrization. -/
private lemma circularParam_surjective : Function.Surjective circularParam := by
  refine fun y ↦ ⟨![y.val 0, y.val 1], Subtype.ext (funext (fun i ↦ ?_))⟩
  fin_cases i <;> simp [circularParam, Matrix.cons_val_two,
    ← y.property.2, Real.sqrt_sq y.property.1]

open scoped Pointwise in
/-- Distance from a closed cone scales linearly under nonnegative dilation. -/
private lemma cone_infDist_smul {n : ℕ} (C : ConeRepresentation.ClosedCone n)
    (r : ℝ) (hr : 0 ≤ r) (x : Fin n → ℝ) :
    Metric.infDist (r • x) C.carrier = r * Metric.infDist x C.carrier := by
  rcases hr.eq_or_lt with rfl | hr
  · simp only [zero_smul, zero_mul, Metric.infDist_zero_of_mem C.zero_mem]
  · have hset : r • C.carrier = C.carrier := Set.Subset.antisymm
      (Set.image_subset_iff.mpr (fun y hy ↦ C.smul_mem r hr.le y hy))
      (fun y hy ↦ ⟨r⁻¹ • y, C.smul_mem r⁻¹ (inv_nonneg.mpr hr.le) y hy,
        smul_inv_smul₀ hr.ne' y⟩)
    simpa only [hset, Real.norm_of_nonneg hr.le] using infDist_smul₀ hr.ne' C.carrier x

/-- The squared Euclidean norm splits into the squared norm of the initial coordinates and the
square of the last coordinate. -/
private lemma euclidean_norm_split {n : ℕ} (z : Fin (n + 1) → ℝ) :
    ‖WithLp.toLp 2 z‖ ^ 2 =
      ‖WithLp.toLp 2 (fun i : Fin n ↦ z i.castSucc)‖ ^ 2 + z (Fin.last n) ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]

/-- Discarding the last coordinate cannot increase the Euclidean norm. -/
private lemma euclidean_norm_prefix_le {n : ℕ} (z : Fin (n + 1) → ℝ) :
    ‖WithLp.toLp 2 (fun i : Fin n ↦ z i.castSucc)‖ ≤ ‖WithLp.toLp 2 z‖ := by
  nlinarith [euclidean_norm_split z, norm_nonneg (WithLp.toLp 2 z),
    norm_nonneg (WithLp.toLp 2 (fun i : Fin n ↦ z i.castSucc)),
    sq_nonneg (z (Fin.last n))]

/-- The homogeneous map used to parametrize the distance-partner cone from its ambient
coordinate space. -/
private def distanceParam {n : ℕ} (C : ConeRepresentation.ClosedCone n)
    (z : Fin (n + 1) → ℝ) : (ConeRepresentation.distancePartner C).carrier :=
  ⟨Fin.snoc (fun i ↦ z i.castSucc)
    (Metric.infDist (fun i : Fin n ↦ z i.castSucc) C.carrier +
      ‖WithLp.toLp 2 (fun i : Fin n ↦ z i.castSucc)‖ - ‖WithLp.toLp 2 z‖), by
    intro y hy
    simpa only [Fin.snoc_last, Fin.snoc_castSucc, add_comm] using
      (sub_le_iff_le_add'.mpr (add_le_add_left (euclidean_norm_prefix_le z)
        (Metric.infDist (fun i : Fin n ↦ z i.castSucc) C.carrier))).trans
          ((Metric.infDist_le_dist_of_mem hy).trans_eq (dist_comm _ _))⟩

/-- The distance-partner parametrization is continuous. -/
private lemma continuous_distanceParam {n : ℕ} (C : ConeRepresentation.ClosedCone n) :
    Continuous (distanceParam C) := by
  unfold distanceParam
  fun_prop

/-- The distance-partner parametrization is positively homogeneous. -/
private lemma distanceParam_smul {n : ℕ} (C : ConeRepresentation.ClosedCone n)
    (r : ℝ) (hr : 0 ≤ r) (z : Fin (n + 1) → ℝ) :
    (distanceParam C (r • z)).val = r • (distanceParam C z).val := by
  ext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  all_goals simp only [distanceParam, Pi.smul_apply, smul_eq_mul,
    Fin.snoc_last, Fin.snoc_castSucc, WithLp.toLp_smul, norm_smul,
    Real.norm_of_nonneg hr, mul_add, mul_sub, sub_left_inj]
  change Metric.infDist (r • (fun j : Fin n ↦ z j.castSucc)) C.carrier +
      ‖WithLp.toLp 2 (r • (fun j : Fin n ↦ z j.castSucc))‖ = _
  rw [cone_infDist_smul C r hr, WithLp.toLp_smul, norm_smul, Real.norm_of_nonneg hr]

/-- Appending the indicated square-root coordinate extends a vector to any prescribed larger
Euclidean norm. -/
private lemma euclidean_norm_snoc_sqrt {n : ℕ} (x : Fin n → ℝ) (R : ℝ)
    (hR : ‖WithLp.toLp 2 x‖ ≤ R) :
    ‖WithLp.toLp 2 (Fin.snoc x (Real.sqrt (R ^ 2 - ‖WithLp.toLp 2 x‖ ^ 2)) :
      Fin (n + 1) → ℝ)‖ = R := by
  have hnonneg : 0 ≤ R ^ 2 - ‖WithLp.toLp 2 x‖ ^ 2 := by
    nlinarith [norm_nonneg (WithLp.toLp 2 x)]
  have hs := euclidean_norm_split
    (Fin.snoc x (Real.sqrt (R ^ 2 - ‖WithLp.toLp 2 x‖ ^ 2)))
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Real.sq_sqrt hnonneg] at hs
  nlinarith [norm_nonneg (WithLp.toLp 2 x), norm_nonneg
    (WithLp.toLp 2 (Fin.snoc x (Real.sqrt (R ^ 2 - ‖WithLp.toLp 2 x‖ ^ 2)) :
      Fin (n + 1) → ℝ))]

/-- A radial coordinate on the distance-partner cone; its level-one section is a closed ball. -/
private def distanceGauge {n : ℕ} (C : ConeRepresentation.ClosedCone n)
    (y : Fin (n + 1) → ℝ) : ℝ :=
  Metric.infDist (fun i : Fin n ↦ y i.castSucc) C.carrier +
    ‖WithLp.toLp 2 (fun i : Fin n ↦ y i.castSucc)‖ - y (Fin.last n)

/-- The radial coordinate scales linearly under positive dilation. -/
private lemma distanceGauge_smul {n : ℕ} (C : ConeRepresentation.ClosedCone n)
    (r : ℝ) (hr : 0 ≤ r) (y : Fin (n + 1) → ℝ) :
    distanceGauge C (r • y) = r * distanceGauge C y := by
  change Metric.infDist (r • (fun i : Fin n ↦ y i.castSucc)) C.carrier +
    ‖WithLp.toLp 2 (r • (fun i : Fin n ↦ y i.castSucc))‖ - r * y (Fin.last n) = _
  rw [cone_infDist_smul C r hr, WithLp.toLp_smul, norm_smul,
    Real.norm_of_nonneg hr, distanceGauge, mul_sub, mul_add]

/-- The radial coordinate dominates the Euclidean radius of the initial coordinates. -/
private lemma prefix_norm_le_distanceGauge {n : ℕ} (C : ConeRepresentation.ClosedCone n)
    (y : (ConeRepresentation.distancePartner C).carrier) :
    ‖WithLp.toLp 2 (fun i : Fin n ↦ y.val i.castSucc)‖ ≤ distanceGauge C y.val := by
  have ht : y.val (Fin.last n) ≤ Metric.infDist (fun i : Fin n ↦ y.val i.castSucc) C.carrier :=
    (Metric.le_infDist ⟨0, C.zero_mem⟩).mpr (fun z hz ↦
      (y.property z hz).trans_eq (dist_comm z _))
  exact (show ‖WithLp.toLp 2 (fun i : Fin n ↦ y.val i.castSucc)‖ ≤
    Metric.infDist (fun i : Fin n ↦ y.val i.castSucc) C.carrier +
      ‖WithLp.toLp 2 (fun i : Fin n ↦ y.val i.castSucc)‖ - y.val (Fin.last n) by linarith)

/-- Only the origin of the distance-partner cone has radial coordinate zero. -/
private lemma distanceGauge_eq_zero {n : ℕ} (C : ConeRepresentation.ClosedCone n)
    (y : (ConeRepresentation.distancePartner C).carrier) (hy : distanceGauge C y.val = 0) :
    y.val = 0 := by
  have hx : (fun i : Fin n ↦ y.val i.castSucc) = 0 :=
    (WithLp.toLp_eq_zero 2).mp (norm_eq_zero.mp
      (le_antisymm ((prefix_norm_le_distanceGauge C y).trans_eq hy) (norm_nonneg _)))
  exact funext (Fin.lastCases
    (by simpa [distanceGauge, hx, Metric.infDist_zero_of_mem C.zero_mem] using hy)
    (fun i ↦ congrFun hx i))

/-- The radial coordinate is strictly positive away from the origin. -/
private lemma distanceGauge_pos {n : ℕ} (C : ConeRepresentation.ClosedCone n)
    (y : (ConeRepresentation.distancePartner C).carrier) (hy : y.val ≠ 0) :
    0 < distanceGauge C y.val := by
  exact lt_of_le_of_ne ((norm_nonneg _).trans (prefix_norm_le_distanceGauge C y))
    (fun h ↦ hy (distanceGauge_eq_zero C y h.symm))

/-- The closed Euclidean ball parametrizes the level-one section of the distance cone. -/
private def distanceBallSection {n : ℕ} (C : ConeRepresentation.ClosedCone n)
    (x : {x : Fin n → ℝ // ‖WithLp.toLp 2 x‖ ≤ 1}) :
    (ConeRepresentation.distancePartner C).carrier :=
  ⟨Fin.snoc x.val (Metric.infDist x.val C.carrier + ‖WithLp.toLp 2 x.val‖ - 1),
    fun z hz ↦ by
      simpa only [Fin.snoc_last, Fin.snoc_castSucc] using
        (show Metric.infDist x.val C.carrier + ‖WithLp.toLp 2 x.val‖ - 1 ≤ dist z x.val by
          linarith [x.property, (Metric.infDist_le_dist_of_mem hz).trans_eq (dist_comm x.val z)])⟩

/-- The ball section has radial coordinate one. -/
private lemma distanceGauge_ballSection {n : ℕ} (C : ConeRepresentation.ClosedCone n)
    (x : {x : Fin n → ℝ // ‖WithLp.toLp 2 x‖ ≤ 1}) :
    distanceGauge C (distanceBallSection C x).val = 1 := by
  simp only [distanceGauge, distanceBallSection, Fin.snoc_castSucc, Fin.snoc_last,
    sub_sub_cancel]

/-- No point of the level-one section is the origin, so radial normalization is defined. -/
private lemma distanceBallSection_norm_pos {n : ℕ} (C : ConeRepresentation.ClosedCone n)
    (x : {x : Fin n → ℝ // ‖WithLp.toLp 2 x‖ ≤ 1}) :
    0 < ‖WithLp.toLp 2 (distanceBallSection C x).val‖ := by
  refine norm_pos_iff.mpr (fun h ↦ one_ne_zero ((distanceGauge_ballSection C x).symm.trans ?_))
  simp only [(WithLp.toLp_eq_zero 2).mp h, distanceGauge, Pi.zero_apply,
    ← Pi.zero_def, WithLp.toLp_zero, norm_zero, Metric.infDist_zero_of_mem C.zero_mem,
    add_zero, sub_zero]

/-- Radial normalization identifies the closed ball with the unit section of the distance cone.
For `x = ρ • u` with `‖u‖₂ = 1` and `ρ > 0`, the formula normalizes
`(u, infDist u C + 1 - ρ⁻¹)`; at the center it gives the south pole. -/
private def distanceBallToSphere {n : ℕ} (C : ConeRepresentation.ClosedCone n)
    (x : {x : Fin n → ℝ // ‖WithLp.toLp 2 x‖ ≤ 1}) :
    {y : (ConeRepresentation.distancePartner C).carrier // ‖WithLp.toLp 2 y.val‖ = 1} :=
  ⟨⟨‖WithLp.toLp 2 (distanceBallSection C x).val‖⁻¹ • (distanceBallSection C x).val,
    (ConeRepresentation.distancePartner C).smul_mem _ (inv_nonneg.mpr (norm_nonneg _))
      _ (distanceBallSection C x).property⟩, by
    rw [WithLp.toLp_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (distanceBallSection_norm_pos C x).ne']⟩

/-- The radial coordinate is positive on the unit section. -/
private lemma distanceGauge_unit_pos {n : ℕ} (C : ConeRepresentation.ClosedCone n)
    (y : {y : (ConeRepresentation.distancePartner C).carrier // ‖WithLp.toLp 2 y.val‖ = 1}) :
    0 < distanceGauge C y.val.val := by
  exact distanceGauge_pos C y.val (fun h ↦ by simpa [h] using y.property)

/-- Dividing the initial coordinates by the radial coordinate gives the inverse ball map. -/
private def distanceSphereToBall {n : ℕ} (C : ConeRepresentation.ClosedCone n)
    (y : {y : (ConeRepresentation.distancePartner C).carrier // ‖WithLp.toLp 2 y.val‖ = 1}) :
    {x : Fin n → ℝ // ‖WithLp.toLp 2 x‖ ≤ 1} :=
  ⟨(distanceGauge C y.val.val)⁻¹ • (fun i ↦ y.val.val i.castSucc), by
    rw [WithLp.toLp_smul, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr (distanceGauge_unit_pos C y).le)]
    exact (mul_le_mul_of_nonneg_left (prefix_norm_le_distanceGauge C y.val)
      (inv_nonneg.mpr (distanceGauge_unit_pos C y).le)).trans_eq
        (inv_mul_cancel₀ (distanceGauge_unit_pos C y).ne')⟩

/-- The radial inverse recovers every point of the closed ball. -/
private lemma distanceSphereToBall_left_inv {n : ℕ} (C : ConeRepresentation.ClosedCone n)
    (x : {x : Fin n → ℝ // ‖WithLp.toLp 2 x‖ ≤ 1}) :
    distanceSphereToBall C (distanceBallToSphere C x) = x := by
  apply Subtype.ext
  change (distanceGauge C (‖WithLp.toLp 2 (distanceBallSection C x).val‖⁻¹ •
    (distanceBallSection C x).val))⁻¹ •
      (‖WithLp.toLp 2 (distanceBallSection C x).val‖⁻¹ •
        (fun i : Fin n ↦ (distanceBallSection C x).val i.castSucc)) = x.val
  rw [distanceGauge_smul C _ (inv_nonneg.mpr (norm_nonneg _)),
    distanceGauge_ballSection, mul_one, inv_inv,
    smul_inv_smul₀ (distanceBallSection_norm_pos C x).ne']
  simp only [distanceBallSection, Fin.snoc_castSucc]

/-- Initial coordinates and the radial coordinate determine an ambient vector. -/
private lemma distanceGauge_ext {n : ℕ} (C : ConeRepresentation.ClosedCone n)
    {y z : Fin (n + 1) → ℝ}
    (hp : (fun i : Fin n ↦ y i.castSucc) = (fun i ↦ z i.castSucc))
    (hg : distanceGauge C y = distanceGauge C z) : y = z := by
  exact funext (Fin.lastCases (sub_right_inj.mp
    ((congrArg (fun p ↦ Metric.infDist p C.carrier + ‖WithLp.toLp 2 p‖ - y (Fin.last n))
      hp).symm.trans hg))
    (fun i ↦ congrFun hp i))

/-- The inverse ball map chooses the unique representative with radial coordinate one. -/
private lemma distanceBallSection_inverse {n : ℕ} (C : ConeRepresentation.ClosedCone n)
    (y : {y : (ConeRepresentation.distancePartner C).carrier // ‖WithLp.toLp 2 y.val‖ = 1}) :
    (distanceBallSection C (distanceSphereToBall C y)).val =
      (distanceGauge C y.val.val)⁻¹ • y.val.val := by
  apply distanceGauge_ext C
  · simp only [distanceBallSection, distanceSphereToBall, Fin.snoc_castSucc, Pi.smul_apply]
  · rw [distanceGauge_ballSection,
      distanceGauge_smul C _ (inv_nonneg.mpr (distanceGauge_unit_pos C y).le),
      inv_mul_cancel₀ (distanceGauge_unit_pos C y).ne']

/-- Normalizing the inverse ball representative recovers the original unit vector. -/
private lemma distanceSphereToBall_right_inv {n : ℕ} (C : ConeRepresentation.ClosedCone n)
    (y : {y : (ConeRepresentation.distancePartner C).carrier // ‖WithLp.toLp 2 y.val‖ = 1}) :
    distanceBallToSphere C (distanceSphereToBall C y) = y := by
  refine Subtype.ext (Subtype.ext ?_)
  change ‖WithLp.toLp 2 (distanceBallSection C (distanceSphereToBall C y)).val‖⁻¹ •
    (distanceBallSection C (distanceSphereToBall C y)).val = y.val.val
  rw [distanceBallSection_inverse, WithLp.toLp_smul, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr (distanceGauge_unit_pos C y).le), y.property,
    mul_one, inv_inv, smul_inv_smul₀ (distanceGauge_unit_pos C y).ne']

/-- The level-one ball parametrization is continuous, including at the center. -/
private lemma continuous_distanceBallSection {n : ℕ} (C : ConeRepresentation.ClosedCone n) :
    Continuous (distanceBallSection C) := by
  unfold distanceBallSection
  fun_prop

/-- The radial coordinate is continuous on the ambient coordinate space. -/
private lemma continuous_distanceGauge {n : ℕ} (C : ConeRepresentation.ClosedCone n) :
    Continuous (distanceGauge C) := by
  unfold distanceGauge
  fun_prop

/-- The unit section of a distance-partner cone is homeomorphic to the closed Euclidean ball. -/
private def distanceBallSphereHomeomorph {n : ℕ} (C : ConeRepresentation.ClosedCone n) :
    {x : Fin n → ℝ // ‖WithLp.toLp 2 x‖ ≤ 1} ≃ₜ
      {y : (ConeRepresentation.distancePartner C).carrier // ‖WithLp.toLp 2 y.val‖ = 1} where
  toFun := distanceBallToSphere C
  invFun := distanceSphereToBall C
  left_inv := distanceSphereToBall_left_inv C
  right_inv := distanceSphereToBall_right_inv C
  continuous_toFun := by
    exact (((((PiLp.continuous_toLp (p := 2) (β := fun _ : Fin (n + 1) ↦ ℝ)).comp
      (continuous_distanceBallSection C).subtype_val).norm).inv₀
      (fun x ↦ (distanceBallSection_norm_pos C x).ne')).smul
        (continuous_distanceBallSection C).subtype_val).subtype_mk _ |>.subtype_mk _
  continuous_invFun := by
    exact ((((continuous_distanceGauge C).comp
      (continuous_subtype_val.comp continuous_subtype_val)).inv₀
        (fun y ↦ (distanceGauge_unit_pos C y).ne')).smul
      (continuous_pi (fun i : Fin n ↦ (continuous_apply i.castSucc).comp
        (continuous_subtype_val.comp continuous_subtype_val)))).subtype_mk _

/-- Projection of the Euclidean unit sphere onto its first coordinates lands in the closed ball. -/
private def euclideanSphereProjection {n : ℕ}
    (z : {z : Fin (n + 1) → ℝ // ‖WithLp.toLp 2 z‖ = 1}) :
    {x : Fin n → ℝ // ‖WithLp.toLp 2 x‖ ≤ 1} :=
  ⟨fun i ↦ z.val i.castSucc, (euclidean_norm_prefix_le z.val).trans_eq z.property⟩

/-- Every point of the closed ball is the projection of a point of the unit sphere. -/
private lemma euclideanSphereProjection_surjective (n : ℕ) :
    Function.Surjective (@euclideanSphereProjection n) := by
  exact fun x ↦ ⟨⟨Fin.snoc x.val (Real.sqrt (1 ^ 2 - ‖WithLp.toLp 2 x.val‖ ^ 2)),
    euclidean_norm_snoc_sqrt x.val 1 x.property⟩,
    Subtype.ext (by simp only [euclideanSphereProjection, Fin.snoc_castSucc])⟩

/-- The sphere maps onto the distance-cone unit section by projection followed by the ball
homeomorphism. -/
private def distanceSphereMap {n : ℕ} (C : ConeRepresentation.ClosedCone n) :
    C({z : Fin (n + 1) → ℝ // ‖WithLp.toLp 2 z‖ = 1},
      {y : (ConeRepresentation.distancePartner C).carrier // ‖WithLp.toLp 2 y.val‖ = 1}) where
  toFun z := distanceBallSphereHomeomorph C (euclideanSphereProjection z)
  continuous_toFun := (distanceBallSphereHomeomorph C).continuous.comp (by
    unfold euclideanSphereProjection
    exact (continuous_pi (fun i : Fin n ↦ (continuous_apply i.castSucc).comp
      (continuous_subtype_val : Continuous
        (fun z : {z : Fin (n + 1) → ℝ // ‖WithLp.toLp 2 z‖ = 1} ↦ z.val)))).subtype_mk _)

/-- Projection and the ball homeomorphism together cover the entire unit section. -/
private lemma distanceSphereMap_surjective {n : ℕ} (C : ConeRepresentation.ClosedCone n) :
    Function.Surjective (distanceSphereMap C) := by
  exact (distanceBallSphereHomeomorph C).surjective.comp (euclideanSphereProjection_surjective n)

/-- On the sphere, the homogeneous formula is the unnormalized ball-section formula. -/
private lemma distanceParam_on_sphere {n : ℕ} (C : ConeRepresentation.ClosedCone n)
    (z : {z : Fin (n + 1) → ℝ // ‖WithLp.toLp 2 z‖ = 1}) :
    (distanceBallSection C (euclideanSphereProjection z)).val = (distanceParam C z.val).val := by
  simp only [distanceBallSection, euclideanSphereProjection, distanceParam, z.property]

/-- Every nonzero cone point has a canonical representative on its Euclidean unit section. -/
private def coneUnitNormalize {n : ℕ} (C : ConeRepresentation.ClosedCone n)
    (y : C.carrier) (hy : y.val ≠ 0) : {y : C.carrier // ‖WithLp.toLp 2 y.val‖ = 1} :=
  ⟨⟨‖WithLp.toLp 2 y.val‖⁻¹ • y.val,
    C.smul_mem _ (inv_nonneg.mpr (norm_nonneg _)) _ y.property⟩, by
    rw [WithLp.toLp_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr ((WithLp.toLp_eq_zero 2).not.mpr hy))]⟩

/-- Covering a cone's unit section by normalized sphere values makes a homogeneous map onto. -/
private lemma homogeneous_surjective_of_sphere_cover {n m : ℕ}
    (C : ConeRepresentation.ClosedCone n) (q : (Fin m → ℝ) → C.carrier)
    (hs : ∀ r : ℝ, 0 ≤ r → ∀ x, (q (r • x)).val = r • (q x).val)
    (hcover : ∀ y : {y : C.carrier // ‖WithLp.toLp 2 y.val‖ = 1},
      ∃ x : {x : Fin m → ℝ // ‖WithLp.toLp 2 x‖ = 1},
        ‖WithLp.toLp 2 (q x.val).val‖⁻¹ • (q x.val).val = y.val.val) :
    Function.Surjective q := by
  intro y
  by_cases hy : y.val = 0
  · exact ⟨0, Subtype.ext ((show (q 0).val = 0 by
      simpa only [zero_smul] using hs 0 le_rfl 0).trans hy.symm)⟩
  · obtain ⟨x, hx⟩ := hcover (coneUnitNormalize C y hy)
    refine ⟨(‖WithLp.toLp 2 y.val‖ * ‖WithLp.toLp 2 (q x.val).val‖⁻¹) • x.val,
      Subtype.ext ?_⟩
    exact (hs _ (mul_nonneg (norm_nonneg _) (inv_nonneg.mpr (norm_nonneg _))) x.val).trans
      ((mul_smul _ _ _).trans ((congrArg (‖WithLp.toLp 2 y.val‖ • ·) hx).trans
        (smul_inv_smul₀ (norm_ne_zero_iff.mpr ((WithLp.toLp_eq_zero 2).not.mpr hy)) y.val)))

/-- The normalized distance map covers the unit section through the ball homeomorphism. -/
private lemma distanceParam_sphere_cover {n : ℕ} (C : ConeRepresentation.ClosedCone n) :
    ∀ y : {y : (ConeRepresentation.distancePartner C).carrier // ‖WithLp.toLp 2 y.val‖ = 1},
      ∃ x : {x : Fin (n + 1) → ℝ // ‖WithLp.toLp 2 x‖ = 1},
        ‖WithLp.toLp 2 (distanceParam C x.val).val‖⁻¹ •
          (distanceParam C x.val).val = y.val.val := by
  exact fun y ↦ (distanceSphereMap_surjective C y).imp (fun z hz ↦
    (congrArg (fun v ↦ ‖WithLp.toLp 2 v‖⁻¹ • v) (distanceParam_on_sphere C z)).symm.trans
      (congrArg (fun v ↦ v.val.val) hz))

/-- A surjection of unit sections gives the cone-function embedding by pullback and radial
extension; the positive radial weight does not affect injectivity. -/
private lemma cone_freeBanach_embedding_from_sphere {n m : ℕ}
    (C : ConeRepresentation.ClosedCone n) (q : (Fin m → ℝ) → C.carrier) (hq : Continuous q)
    (hs : ∀ r : ℝ, 0 ≤ r → ∀ x, (q (r • x)).val = r • (q x).val)
    (hcover : ∀ y : {y : C.carrier // ‖WithLp.toLp 2 y.val‖ = 1},
      ∃ x : {x : Fin m → ℝ // ‖WithLp.toLp 2 x‖ = 1},
        ‖WithLp.toLp 2 (q x.val).val‖⁻¹ • (q x.val).val = y.val.val) :
    ∃ T : VecLatHom (ConeRepresentation.ConeFunctions C)
        (FBL (EuclideanSpace ℝ (Fin m))), Function.Injective T := by
  exact cone_freeBanach_embedding C q hq hs
    (homogeneous_surjective_of_sphere_cover C q hs hcover)

/-- The normalized circular parametrization maps the planar unit circle onto the circular
cone's unit section. -/
private lemma circularParam_sphere_cover :
    ∀ y : {y : circularCone.carrier // ‖WithLp.toLp 2 y.val‖ = 1},
      ∃ x : {x : Fin 2 → ℝ // ‖WithLp.toLp 2 x‖ = 1},
        ‖WithLp.toLp 2 (circularParam x.val).val‖⁻¹ • (circularParam x.val).val = y.val.val := by
  intro y
  obtain ⟨v, hv⟩ := circularParam_surjective y.val
  have hvn : ‖WithLp.toLp 2 v‖ ≠ 0 := by
    intro h
    have hz : y.val.val = 0 := (congrArg Subtype.val hv).symm.trans
      ((congrArg (fun w ↦ (circularParam w).val)
        ((WithLp.toLp_eq_zero 2).mp (norm_eq_zero.mp h))).trans
          (by simpa only [zero_smul] using circularParam_smul 0 le_rfl 0))
    simpa [hz] using y.property
  refine ⟨⟨‖WithLp.toLp 2 v‖⁻¹ • v, by
    rw [WithLp.toLp_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ hvn]⟩, ?_⟩
  change ‖WithLp.toLp 2 (circularParam (‖WithLp.toLp 2 v‖⁻¹ • v)).val‖⁻¹ •
    (circularParam (‖WithLp.toLp 2 v‖⁻¹ • v)).val = y.val.val
  rw [circularParam_smul _ (inv_nonneg.mpr (norm_nonneg _)), hv, WithLp.toLp_smul,
    norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), y.property,
    mul_one, inv_inv, smul_inv_smul₀ hvn]

/-- Reindexes a Boolean free product by a universe-lifted Boolean type. -/
private def liftBoolFreeProduct {E : Bool → Type}
    [∀ i, AddCommGroup (E i)] [∀ i, Lattice (E i)]
    [∀ i, IsOrderedAddMonoid (E i)] [∀ i, VectorLattice (E i)] (P : FreeProduct E) :
    FreeProduct (fun i : ULift Bool ↦ E i.down) where
  Carrier := P.Carrier
  inclusion i := P.inclusion i.down
  universal Y _ _ _ _ T := by
    obtain ⟨S, hS, huniq⟩ := P.universal Y (fun b ↦ T ⟨b⟩)
    exact ⟨S, fun i ↦ hS i.down, fun R hR ↦ huniq R (fun b ↦ hR ⟨b⟩)⟩

/-- The two cones used in the counterexample: the circular cone and its distance partner. -/
private def counterexampleCones (b : Bool) :
    ConeRepresentation.ClosedCone (if b then 4 else 3) :=
  match b with
  | false => circularCone
  | true => ConeRepresentation.distancePartner circularCone

/-- Both counterexample cone lattices embed into the specified finite-dimensional free Banach
lattices. -/
private lemma counterexample_cones_embeddings :
    ∃ T : ∀ b, VecLatHom (ConeRepresentation.ConeFunctions (counterexampleCones b))
      (euclideanFreeBanachFactors b), ∀ b, Function.Injective (T b) := by
  obtain ⟨A, hA⟩ := cone_freeBanach_embedding_from_sphere circularCone circularParam
    continuous_circularParam circularParam_smul circularParam_sphere_cover
  obtain ⟨B, hB⟩ := cone_freeBanach_embedding_from_sphere
    (ConeRepresentation.distancePartner circularCone) (distanceParam circularCone)
    (continuous_distanceParam circularCone) (distanceParam_smul circularCone)
    (distanceParam_sphere_cover circularCone)
  exact ⟨fun b ↦ match b with | false => A | true => B,
    fun b ↦ match b with | false => hA | true => hB⟩

/-- The ordinary free product of these two free Banach lattices is non-Archimedean. -/
theorem freeBanach_pair_not_archimedean (P : FreeProduct euclideanFreeBanachFactors) :
    ¬ IsVLArchimedean P.Carrier := by
  intro hP
  obtain ⟨T, hT⟩ := counterexample_cones_embeddings
  obtain ⟨Q⟩ := nonempty_freeProduct
    (fun b ↦ ConeRepresentation.ConeFunctions (counterexampleCones b))
  obtain ⟨S, hS, _⟩ := Q.universal P.Carrier (fun b ↦ (P.inclusion b).comp (T b))
  have hinj := Q.induced_injective P T hT S hS
  have hQ : IsVLArchimedean Q.Carrier := ⟨fun {x y} h ↦ S.le_of_map_le hinj
    ((hP.le_zero_of_forall_nsmul_le (fun n ↦
      (map_nsmul S n x).symm.le.trans (S.monotone (h n)))).trans_eq (map_zero S).symm)⟩
  apply ConeRepresentation.distancePartner_not_cover circularCone circularCone_not_polyhedral
  have hc := binary_cone_product_archimedean_iff (liftBoolFreeProduct Q)
    circularCone (ConeRepresentation.distancePartner circularCone)
    (VecLatEquiv.refl (X := ConeRepresentation.ConeFunctions circularCone))
    (VecLatEquiv.refl (X := ConeRepresentation.ConeFunctions
      (ConeRepresentation.distancePartner circularCone)))
  exact hc.mp hQ

/-- The canonical map from the ordinary free product into the Banach free product
need not be injective, even for free Banach lattice factors. -/
theorem freeBanach_comparison_not_injective
    (P : FreeProduct euclideanFreeBanachFactors)
    (Q : BanachLattice.FreeProduct euclideanFreeBanachFactors)
    (T : VecLatHom P.Carrier Q.Carrier)
    (_hT : ∀ i x, T (P.inclusion i x) = Q.inclusion i x) :
    ¬ Function.Injective T := by
  intro hinj
  apply freeBanach_pair_not_archimedean P
  refine ⟨fun {x y} h ↦ T.le_of_map_le hinj ?_⟩
  exact (IsVLArchimedean.le_zero_of_forall_nsmul_le (fun n ↦
    (map_nsmul T n x).symm.le.trans (T.monotone (h n)))).trans_eq (map_zero T).symm

end VectorLattice.Counterexamples
