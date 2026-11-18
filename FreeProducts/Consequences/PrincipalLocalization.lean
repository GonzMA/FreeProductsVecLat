/-
Authors: Gonzalo Martínez-Fernández
-/

import FreeProducts.Consequences.NormAndCompletion
import FreeProducts.Consequences.ContinuousFunctionEmbeddings

/-!
# Localization in free products of principal ideals

Every element of a binary Banach lattice free product lies in the image of a free
product of suitable principal ideals with their order-unit norms. Positive majorants
and geometric approximation give the required generators. Injectivity of the maps for
strictly positive generators follows from the existing continuous-function embedding
result through the principal ideals' continuous-function representations.
-/

universe u v

namespace BanachLattice.FreeProduct

section PrincipalIdeals

open scoped Pointwise Topology

attribute [local instance] OrderIdeal.principalNormedAddCommGroup
  OrderIdeal.principalNormedVectorLattice

/-- A principal ideal of a Banach lattice is complete in its order-unit norm. -/
lemma principal_completeSpace
    {Y : Type u} [NormedAddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] [BanachLattice Y]
    (e : Y) (he : 0 ≤ e) :
    @CompleteSpace ↥(OrderIdeal.principalSubmodule e)
      (@PseudoMetricSpace.toUniformSpace _
        (@SeminormedAddCommGroup.toPseudoMetricSpace _
          (@NormedAddCommGroup.toSeminormedAddCommGroup _
            (OrderIdeal.principalNormedAddCommGroup e)))) := by
  rcases he.eq_or_lt with he | he
  · subst e
    have hz (x : ↥(OrderIdeal.principalSubmodule (0 : Y))) : (x : Y) = 0 := by
      obtain ⟨c, _, hc⟩ := x.property
      exact (abs_eq_zero_iff_zero (x : Y)).mp
        (le_antisymm (by simpa only [abs_zero, smul_zero] using hc) (abs_nonneg _))
    let : Subsingleton ↥(OrderIdeal.principalSubmodule (0 : Y)) :=
      ⟨fun x y ↦ Subtype.ext ((hz x).trans (hz y).symm)⟩
    infer_instance
  · exact (isUniformlyCompleteVectorLattice_of_banachLattice Y).complete_principal e he

variable (X : Bool → Type u)
  [∀ b, NormedAddCommGroup (X b)] [∀ b, Lattice (X b)]
  [∀ b, IsOrderedAddMonoid (X b)] [∀ b, BanachLattice (X b)]

/-- Every countable family in a Banach lattice is contained in one principal ideal generated
by a nonnegative element. -/
private lemma exists_principal_containing_countable
    {ι : Type*} {Y : Type u} [Countable ι]
    [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [BanachLattice Y]
    (x : ι → Y) : ∃ u : Y, 0 ≤ u ∧ ∀ i, x i ∈ OrderIdeal.principal u := by
  let : Encodable ι := (nonempty_encodable ι).some
  obtain ⟨s, hs, c, hsc, _⟩ := posSumOfEncodable (zero_lt_one : (0 : ℝ) < 1) ι
  let a (i : ι) := s i / (1 + ‖x i‖)
  have ha (i : ι) : 0 < a i := div_pos (hs i) (by positivity)
  have hmul (i : ι) : a i * (1 + ‖x i‖) = s i := div_mul_cancel₀ _ (by positivity)
  have hnorm (i : ι) : ‖a i • |x i|‖ ≤ s i := by
    rw [norm_smul, Real.norm_of_nonneg (ha i).le, norm_abs_eq_norm]
    nlinarith [hmul i, ha i]
  have hsum : Summable (fun i ↦ a i • |x i|) := hsc.summable.of_norm_bounded hnorm
  let v := ∑' i, a i • |x i|
  have hv : 0 ≤ v := tsum_nonneg (fun i ↦ smul_nonneg (ha i).le (abs_nonneg (x i)))
  refine ⟨v, hv, fun i ↦ ⟨(a i)⁻¹, inv_nonneg.mpr (ha i).le, ?_⟩⟩
  have hle := hsum.le_tsum i (fun j _ ↦ smul_nonneg (ha j).le (abs_nonneg (x j)))
  have h := smul_le_smul_of_nonneg_left hle (inv_nonneg.mpr (ha i).le)
  simp only [smul_smul, inv_mul_cancel₀ (ha i).ne', one_smul] at h
  simpa only [abs_of_nonneg hv] using h

/-- The ambient norm of a principal-ideal element is bounded by its order-unit norm times the
ambient norm of the generator. -/
private lemma principal_coe_norm_bound
    {Y : Type u} [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [BanachLattice Y]
    (u : Y) (x : ↥(OrderIdeal.principalSubmodule u)) : ‖(x : Y)‖ ≤ ‖u‖ * ‖x‖ := by
  have h := OrderIdeal.abs_le_gaugeNorm_smul_abs u x.property
  have hn := norm_le_norm_of_abs_le_abs
    (h.trans_eq (abs_of_nonneg
      (smul_nonneg (OrderIdeal.gaugeNorm_nonneg _ _) (abs_nonneg _))).symm)
  change ‖(x : Y)‖ ≤ ‖u‖ * OrderIdeal.gaugeNorm u (x : Y)
  simpa only [norm_smul, Real.norm_of_nonneg (OrderIdeal.gaugeNorm_nonneg _ _),
    norm_abs_eq_norm, mul_comm] using hn

/-- Constructs the bounded lattice map from a free product of principal ideals into the
original free product. -/
lemma exists_principal_product_map (P : FreeProduct X)
    (u : ∀ b, X b) (hu : ∀ b, 0 ≤ u b) :
    letI : ∀ b, BanachLattice ↥(OrderIdeal.principalSubmodule (u b)) :=
      fun b ↦
        { toNormedVectorLattice := OrderIdeal.principalNormedVectorLattice (u b)
          toCompleteSpace := principal_completeSpace (u b) (hu b) }
    ∃ Q : FreeProduct (fun b ↦ ↥(OrderIdeal.principalSubmodule (u b))),
      ∃ S : Q.Carrier →L[ℝ] P.Carrier, IsVecLatHom S ∧
        ∀ b (x : ↥(OrderIdeal.principalSubmodule (u b))),
          S (Q.inclusion b x) = P.inclusion b (x : X b) := by
  let : ∀ b, BanachLattice ↥(OrderIdeal.principalSubmodule (u b)) :=
    fun b ↦
      { toNormedVectorLattice := OrderIdeal.principalNormedVectorLattice (u b)
        toCompleteSpace := principal_completeSpace (u b) (hu b) }
  let : ∀ b, SeminormedAddCommGroup ↥(OrderIdeal.principalSubmodule (u b)) :=
    fun b ↦ (OrderIdeal.principalNormedAddCommGroup (u b)).toSeminormedAddCommGroup
  let : ∀ b, TopologicalSpace ↥(OrderIdeal.principalSubmodule (u b)) :=
    fun b ↦ (OrderIdeal.principalNormedAddCommGroup (u b)).toUniformSpace.toTopologicalSpace
  obtain ⟨Q⟩ := BanachLattice.nonempty_freeProduct
    (fun b ↦ ↥(OrderIdeal.principalSubmodule (u b)))
  let j (b : Bool) := (P.inclusion b).toLinearMap.comp (OrderIdeal.principalSubmodule (u b)).subtype
  have hbound (b : Bool) (x : ↥(OrderIdeal.principalSubmodule (u b))) :
      ‖j b x‖ ≤ ‖u b‖ * ‖x‖ :=
    (((P.inclusion b).le_of_opNorm_le (P.inclusion_contractive b) (x : X b)).trans_eq
      (one_mul _)).trans (principal_coe_norm_bound (u b) x)
  let V (b : Bool) := (j b).mkContinuous ‖u b‖ (hbound b)
  have hV (b : Bool) : IsVecLatHom (V b) :=
    { map_add := (V b).map_add
      map_smul := (V b).map_smul
      map_sup' := fun x y ↦ (P.inclusion_isVecLatHom b).map_sup' (x : X b) (y : X b)
      map_inf' := fun x y ↦ (P.inclusion_isVecLatHom b).map_inf' (x : X b) (y : X b) }
  have hVnorm (b : Bool) : ‖V b‖ ≤ ‖u b‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (hbound b)
  obtain ⟨S, hS, _⟩ := Q.exists_unique_extension P.Carrier V hV
    (‖u false‖ + ‖u true‖) (add_nonneg (norm_nonneg _) (norm_nonneg _))
    (Bool.rec ((hVnorm false).trans (le_add_of_nonneg_right (norm_nonneg (u true))))
      ((hVnorm true).trans (le_add_of_nonneg_left (norm_nonneg (u false)))))
  exact ⟨Q, S, hS.1, hS.2.1⟩

/-- Replacing both factors by isometrically equivalent Banach lattices preserves the
free-product universal property. -/
private lemma factor_equiv_universal
    {E F : Bool → Type u}
    [∀ b, NormedAddCommGroup (E b)] [∀ b, Lattice (E b)]
    [∀ b, IsOrderedAddMonoid (E b)] [∀ b, BanachLattice (E b)]
    [∀ b, NormedAddCommGroup (F b)] [∀ b, Lattice (F b)]
    [∀ b, IsOrderedAddMonoid (F b)] [∀ b, BanachLattice (F b)]
    (Q : FreeProduct E) (e : ∀ b, BanachLatEquiv (E b) (F b))
    (Y : Type u) [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [BanachLattice Y]
    (T : ∀ b, F b →L[ℝ] Y) (hT : ∀ b, IsVecLatHom (T b))
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ b, ‖T b‖ ≤ M) :
    ∃! R : Q.Carrier →L[ℝ] Y, IsVecLatHom R ∧
      (∀ b y, R (Q.inclusion b ((e b).symm y)) = T b y) ∧ ‖R‖ ≤ M := by
  let V (b : Bool) := (T b).comp (e b).toContinuousLinearEquiv.toContinuousLinearMap
  have hV (b : Bool) : IsVecLatHom (V b) :=
    (((hT b).mk' (T b)).comp (e b).toVecLatEquiv.toVecLatHom).isVecLatHom
  have hn (b : Bool) (x : E b) : ‖V b x‖ ≤ M * ‖x‖ :=
    ((T b).le_opNorm ((e b).toLinearIsometryEquiv x)).trans
      ((mul_le_mul_of_nonneg_right (hbound b) (norm_nonneg _)).trans_eq
        (congrArg (M * ·) ((e b).toLinearIsometryEquiv.norm_map x)))
  obtain ⟨R, hR, huniq⟩ := Q.exists_unique_extension Y V hV M hM
    (fun b ↦ ContinuousLinearMap.opNorm_le_bound _ hM (hn b))
  refine ⟨R, ⟨hR.1, ?_, hR.2.2⟩, ?_⟩
  · exact fun b y ↦ (hR.2.1 b ((e b).symm y)).trans
      (congrArg (T b) ((e b).toLinearIsometryEquiv.apply_symm_apply y))
  · rintro R' ⟨hR', hRT, hnorm⟩
    apply huniq R' ⟨hR', ?_, hnorm⟩
    exact fun b x ↦ (congrArg (fun v : E b ↦ R' (Q.inclusion b v))
      ((e b).toLinearIsometryEquiv.symm_apply_apply x)).symm.trans (hRT b (e b x))

/-- Transports a free-product model along isometric Banach lattice equivalences of the two
factors. -/
noncomputable def freeProductOfFactorEquiv
    {E F : Bool → Type u}
    [∀ b, NormedAddCommGroup (E b)] [∀ b, Lattice (E b)]
    [∀ b, IsOrderedAddMonoid (E b)] [∀ b, BanachLattice (E b)]
    [∀ b, NormedAddCommGroup (F b)] [∀ b, Lattice (F b)]
    [∀ b, IsOrderedAddMonoid (F b)] [∀ b, BanachLattice (F b)]
    (Q : FreeProduct E) (e : ∀ b, BanachLatEquiv (E b) (F b)) : FreeProduct F where
  Carrier := Q.Carrier
  inclusion b := (Q.inclusion b).comp
    (e b).symm.toContinuousLinearEquiv.toContinuousLinearMap
  inclusion_isVecLatHom b :=
    (((Q.inclusion_isVecLatHom b).mk' (Q.inclusion b)).comp
      (e b).symm.toVecLatEquiv.toVecLatHom).isVecLatHom
  inclusion_contractive b := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun f ↦ ((Q.inclusion b).le_of_opNorm_le (Q.inclusion_contractive b)
      ((e b).symm.toLinearIsometryEquiv f)).trans_eq
        (congrArg (1 * ·) ((e b).symm.toLinearIsometryEquiv.norm_map f)))
  universal := fun Y _ _ _ _ V hV M hM hbound ↦
    factor_equiv_universal Q e Y V hV M hM hbound

/-- The induced-map embedding result extends from continuous-function factors to factors
isometrically equivalent to them. -/
private lemma induced_injective_of_factor_equiv
    {E : Bool → Type u}
    [∀ b, NormedAddCommGroup (E b)] [∀ b, Lattice (E b)]
    [∀ b, IsOrderedAddMonoid (E b)] [∀ b, BanachLattice (E b)]
    (K : Bool → Type u) [∀ b, TopologicalSpace (K b)] [∀ b, CompactSpace (K b)]
    [∀ b, T2Space (K b)] [∀ b, Nonempty (K b)]
    (e : ∀ b, BanachLatEquiv (E b) C(K b, ℝ))
    (Q : FreeProduct E) (P : FreeProduct X) (T : ∀ b, E b →L[ℝ] X b)
    (hT : ∀ b, IsVecLatHom (T b)) (hinj : ∀ b, Function.Injective (T b))
    (S : Q.Carrier →L[ℝ] P.Carrier) (hS : IsVecLatHom S)
    (hcomm : ∀ b x, S (Q.inclusion b x) = P.inclusion b (T b x)) :
    Function.Injective S := by
  let C := freeProductOfFactorEquiv Q e
  let U (b : Bool) := (T b).comp (e b).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hU (b : Bool) : IsVecLatHom (U b) :=
    (((hT b).mk' (T b)).comp (e b).symm.toVecLatEquiv.toVecLatHom).isVecLatHom
  have hUinj (b : Bool) : Function.Injective (U b) :=
    (hinj b).comp (e b).symm.toLinearIsometryEquiv.injective
  exact induced_injective_of_continuousFunctions K X C P U hU hUinj S hS
    (fun b f ↦ hcomm b ((e b).symm f))

/-- The canonical free-product map from principal ideals with strictly positive generators is
injective. -/
lemma principal_product_map_injective (P : FreeProduct X)
    (u : ∀ b, X b) (hu : ∀ b, 0 < u b) :
    letI : ∀ b, BanachLattice ↥(OrderIdeal.principalSubmodule (u b)) :=
      fun b ↦
        { toNormedVectorLattice := OrderIdeal.principalNormedVectorLattice (u b)
          toCompleteSpace := principal_completeSpace (u b) (hu b).le }
    ∀ (Q : FreeProduct (fun b ↦ ↥(OrderIdeal.principalSubmodule (u b))))
      (S : Q.Carrier →L[ℝ] P.Carrier), IsVecLatHom S →
      (∀ b (x : ↥(OrderIdeal.principalSubmodule (u b))),
        S (Q.inclusion b x) = P.inclusion b (x : X b)) → Function.Injective S := by
  let : ∀ b, BanachLattice ↥(OrderIdeal.principalSubmodule (u b)) :=
    fun b ↦
      { toNormedVectorLattice := OrderIdeal.principalNormedVectorLattice (u b)
        toCompleteSpace := principal_completeSpace (u b) (hu b).le }
  intro Q S hS hcomm
  let : ∀ b, SeminormedAddCommGroup ↥(OrderIdeal.principalSubmodule (u b)) :=
    fun b ↦ (OrderIdeal.principalNormedAddCommGroup (u b)).toSeminormedAddCommGroup
  let : ∀ b, TopologicalSpace ↥(OrderIdeal.principalSubmodule (u b)) :=
    fun b ↦ (OrderIdeal.principalNormedAddCommGroup (u b)).toUniformSpace.toTopologicalSpace
  let : ∀ b, Nontrivial ↥(OrderIdeal.principalSubmodule (u b)) := fun b ↦
    ⟨⟨0, ⟨u b, OrderIdeal.self_mem_principal (u b)⟩,
      fun h ↦ (ne_of_gt (hu b)) (congrArg Subtype.val h).symm⟩⟩
  let : ∀ b, AMSpaceWithUnit ↥(OrderIdeal.principalSubmodule (u b)) := fun b ↦
    OrderIdeal.principalAMSpaceWithUnit (hu b).le (principal_completeSpace (u b) (hu b).le)
  let K (b : Bool) := AMSpaceWithUnit.LatticeCharacter ↥(OrderIdeal.principalSubmodule (u b))
  have : ∀ b, Nonempty (K b) := fun b ↦
    let ⟨φ, _⟩ := AMSpaceWithUnit.LatticeCharacter.exists_abs_apply_eq_norm
      (X := ↥(OrderIdeal.principalSubmodule (u b))) 0
    ⟨φ⟩
  let e (b : Bool) := AMSpaceWithUnit.kakutaniEquiv ↥(OrderIdeal.principalSubmodule (u b))
  let j (b : Bool) := (OrderIdeal.principalSubmodule (u b)).subtype.mkContinuous ‖u b‖
    (principal_coe_norm_bound (u b))
  have hj (b : Bool) : IsVecLatHom (j b) :=
    { map_add := (j b).map_add
      map_smul := (j b).map_smul
      map_sup' := fun _ _ ↦ rfl
      map_inf' := fun _ _ ↦ rfl }
  exact induced_injective_of_factor_equiv X K e Q P j hj
    (fun _ ↦ Subtype.coe_injective) S hS hcomm

/-- A sequence with geometric norm decay remains summable after multiplication by the
specified geometric weights. -/
private lemma weighted_summable_of_geometric_bound
    {Y : Type u} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (f : ℕ → Y) (c : ℝ) (hf : ∀ n, ‖f n‖ ≤ c * (1 / 4 : ℝ) ^ n) :
    Summable (fun n ↦ (2 : ℝ) ^ n • f n) := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left c) (fun n ↦ ?_)
  rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)]
  refine (mul_le_mul_of_nonneg_left (hf n) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)).trans_eq ?_
  rw [mul_left_comm, ← mul_pow]
  norm_num

/-- A positive term is bounded by a geometric multiple of the weighted sum of all terms. -/
private lemma term_le_geometric_regulator
    {Y : Type u} [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [BanachLattice Y]
    (f : ℕ → Y) (hf : ∀ n, 0 ≤ f n) (hs : Summable (fun n ↦ (2 : ℝ) ^ n • f n))
    (n : ℕ) : f n ≤ (1 / 2 : ℝ) ^ n • ∑' k, (2 : ℝ) ^ k • f k := by
  have hle := hs.le_tsum n (fun k _ ↦ smul_nonneg (by positivity) (hf k))
  have h := smul_le_smul_of_nonneg_left hle
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n)
  simpa only [smul_smul, ← mul_pow, show (1 / 2 : ℝ) * 2 = 1 by norm_num,
    one_pow, one_smul] using h

/-- Approximates any free-product element by generated elements whose successive differences
admit geometrically small positive factor majorants. -/
private lemma exists_geometric_approximation (P : FreeProduct X) (z : P.Carrier) :
    ∃ (g : ℕ → P.generated) (a : ∀ b, ℕ → X b),
      Filter.Tendsto (fun n ↦ (g n : P.Carrier)) Filter.atTop (𝓝 z) ∧
      (∀ b n, 0 ≤ a b n) ∧
      (∀ b n, ‖a b n‖ ≤ 3 * (1 / 4 : ℝ) ^ n) ∧
      (∀ n, |((g (n + 1) - g n : P.generated) : P.Carrier)| ≤
        P.inclusion false (a false n) + P.inclusion true (a true n)) := by
  choose g hmem hg using fun n : ℕ ↦ P.dense_generated.exists_dist_lt z
    (pow_pos (by norm_num : (0 : ℝ) < 1 / 4) n)
  let q (n : ℕ) : P.generated := ⟨g n, hmem n⟩
  have hdiff (n : ℕ) : ‖g (n + 1) - g n‖ ≤ 2 * (1 / 4 : ℝ) ^ n := by
    have h := (dist_triangle (g (n + 1)) z (g n)).trans
      (add_le_add (by simpa only [dist_comm] using (hg (n + 1)).le) (hg n).le)
    rw [dist_eq_norm, pow_succ] at h
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 4) n]
  choose a b ha hb hmajor hab using fun n ↦ exists_norm_majorant X P (q (n + 1) - q n)
    ((1 / 4 : ℝ) ^ n) (pow_pos (by norm_num : (0 : ℝ) < 1 / 4) n)
  have habnorm (n : ℕ) : ‖a n‖ + ‖b n‖ ≤ 3 * (1 / 4 : ℝ) ^ n := by
    have h : ‖a n‖ + ‖b n‖ ≤ ‖g (n + 1) - g n‖ + (1 / 4 : ℝ) ^ n :=
      by simpa only [q, AddSubgroupClass.coe_sub] using hab n
    linarith [hdiff n]
  refine ⟨q, (fun c ↦ Bool.rec (motive := fun c ↦ ℕ → X c) a b c), ?_⟩
  refine ⟨?_, ?_, ?_, hmajor⟩
  · apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ (by
      simpa only [q, dist_comm] using (hg n).le))
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
        (by norm_num : (1 / 4 : ℝ) < 1))
  · intro c n
    exact Bool.rec (motive := fun c ↦
      0 ≤ Bool.rec (motive := fun c ↦ ℕ → X c) a b c n) (ha n) (hb n) c
  · intro c n
    exact Bool.rec (motive := fun c ↦
      ‖Bool.rec (motive := fun c ↦ ℕ → X c) a b c n‖ ≤ 3 * (1 / 4 : ℝ) ^ n)
      ((le_add_of_nonneg_right (norm_nonneg (b n))).trans (habnorm n))
      ((le_add_of_nonneg_left (norm_nonneg (a n))).trans (habnorm n)) c

/-- Chooses a positive principal-ideal generator containing a countable family and giving
geometric order-unit norm bounds for another sequence. -/
lemma exists_principal_sequence_control
    {ι : Type*} [Countable ι] {Y : Type u} [NormedAddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] [BanachLattice Y] [Nontrivial Y]
    (x : ι → Y) (f : ℕ → Y) (hf : ∀ n, 0 ≤ f n)
    (hnorm : ∀ n, ‖f n‖ ≤ 3 * (1 / 4 : ℝ) ^ n) :
    ∃ (u : Y) (_ : 0 < u),
      (∀ i, x i ∈ OrderIdeal.principal u) ∧
      ∀ n, ∃ h : f n ∈ OrderIdeal.principal u,
        ‖(⟨f n, h⟩ : ↥(OrderIdeal.principalSubmodule u))‖ ≤ (1 / 2 : ℝ) ^ n := by
  obtain ⟨v, hv, hx⟩ := exists_principal_containing_countable x
  have hs := weighted_summable_of_geometric_bound f 3 hnorm
  obtain ⟨w, hw⟩ := exists_ne (0 : Y)
  let u := (v ⊔ ∑' n, (2 : ℝ) ^ n • f n) ⊔ |w|
  have hvu : v ≤ u := le_sup_left.trans le_sup_left
  have hu : 0 < u := lt_of_le_of_ne ((abs_nonneg w).trans le_sup_right)
    (fun h ↦ hw ((abs_eq_zero_iff_zero w).mp
      (le_antisymm (le_sup_right.trans h.symm.le) (abs_nonneg w))))
  refine ⟨u, hu, ?_, ?_⟩
  · intro i
    obtain ⟨c, hc, hxc⟩ := hx i
    exact ⟨c, hc, hxc.trans (smul_le_smul_of_nonneg_left
      (by simpa only [abs_of_nonneg hv, abs_of_nonneg hu.le] using hvu) hc)⟩
  · intro n
    have hle : |f n| ≤ (1 / 2 : ℝ) ^ n • |u| := by
      simpa only [abs_of_nonneg (hf n), abs_of_nonneg hu.le] using
        (term_le_geometric_regulator f hf hs n).trans
          (smul_le_smul_of_nonneg_left (le_sup_right.trans le_sup_left)
            (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n))
    exact ⟨⟨(1 / 2 : ℝ) ^ n, by positivity, hle⟩,
      OrderIdeal.gaugeNorm_le_of_abs_le u (by positivity) hle⟩

/-- When both factors are nonzero, every free-product element lifts from a free product of
principal ideals with positive generators. -/
lemma exists_mem_range_principal_freeProduct_nontrivial
    [∀ b, Nontrivial (X b)] (P : FreeProduct X) (z : P.Carrier) :
    ∃ (u : ∀ b, X b) (hu : ∀ b, 0 < u b),
      letI : ∀ b, BanachLattice ↥(OrderIdeal.principalSubmodule (u b)) :=
        fun b ↦
          { toNormedVectorLattice := OrderIdeal.principalNormedVectorLattice (u b)
            toCompleteSpace := principal_completeSpace (u b) (hu b).le }
      ∃ Q : FreeProduct (fun b ↦ ↥(OrderIdeal.principalSubmodule (u b))),
        ∃ S : Q.Carrier →L[ℝ] P.Carrier,
          IsVecLatHom S ∧ Function.Injective S ∧
          (∀ b (x : ↥(OrderIdeal.principalSubmodule (u b))),
            S (Q.inclusion b x) = P.inclusion b (x : X b)) ∧
          z ∈ Set.range S := by
  obtain ⟨g, a, hg, ha, hanorm, hmajor⟩ := exists_geometric_approximation X P z
  choose N i x φ hx using fun n ↦ P.exists_expression (g n)
  let y (b : Bool) (s : Σ n, Fin (N n)) : X b :=
    if h : i s.1 s.2 = b then h ▸ x s.1 s.2 else 0
  choose u hu hy hcontrol using fun b ↦
    exists_principal_sequence_control (y b) (a b) (ha b) (hanorm b)
  let : ∀ b, BanachLattice ↥(OrderIdeal.principalSubmodule (u b)) :=
    fun b ↦
      { toNormedVectorLattice := OrderIdeal.principalNormedVectorLattice (u b)
        toCompleteSpace := principal_completeSpace (u b) (hu b).le }
  obtain ⟨Q, S, hS, hcomm⟩ := exists_principal_product_map X P u (fun b ↦ (hu b).le)
  have hSinj := principal_product_map_injective X P u hu Q S hS hcomm
  let v (n : ℕ) (j : Fin (N n)) : ↥(OrderIdeal.principalSubmodule (u (i n j))) :=
    ⟨x n j, by
      change x n j ∈ OrderIdeal.principal (u (i n j))
      simpa only [y, dite_eq_left rfl] using hy (i n j) ⟨n, j⟩⟩
  let q (n : ℕ) := LLexpr.eval (fun j ↦ Q.inclusion (i n j) (v n j)) (φ n)
  have hq (n : ℕ) : S (q n) = (g n : P.Carrier) := by
    change (hS.mk' S) (LLexpr.eval (fun j ↦ Q.inclusion (i n j) (v n j)) (φ n)) = _
    rw [LLexpr.map_eval]
    simpa only [IsVecLatHom.mk'_apply, hcomm, v] using (hx n).symm
  choose ah ahnorm using hcontrol
  let A (b : Bool) (n : ℕ) : ↥(OrderIdeal.principalSubmodule (u b)) := ⟨a b n, ah b n⟩
  have hmajorQ (n : ℕ) : |q (n + 1) - q n| ≤
      Q.inclusion false (A false n) + Q.inclusion true (A true n) := by
    apply (hS.mk' S).le_of_map_le hSinj
    simpa [VecLatHom.map_abs, IsVecLatHom.mk'_apply, hq, hcomm, A]
      using hmajor n
  have hdiff (n : ℕ) : ‖q (n + 1) - q n‖ ≤ 2 * (1 / 2 : ℝ) ^ n := by
    refine (norm_le_positive_majorant (fun b ↦ ↥(OrderIdeal.principalSubmodule (u b))) Q
      (q (n + 1) - q n) (A false n) (A true n) (ha false n) (ha true n)
      (hmajorQ n)).trans ?_
    exact (add_le_add (ahnorm false n) (ahnorm true n)).trans_eq (two_mul _).symm
  have hc : CauchySeq q := cauchySeq_of_dist_le_of_summable
    (fun n ↦ 2 * (1 / 2 : ℝ) ^ n)
    (fun n ↦ by simpa only [dist_eq_norm'] using hdiff n)
    ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left 2)
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨u, hu, Q, S, hS, hSinj, hcomm, w,
    tendsto_nhds_unique (S.continuous.continuousAt.tendsto.comp hw)
      (by simpa only [Function.comp_def, hq] using hg)⟩

/-- If the other factor is zero, the remaining factor surjects onto the binary free product. -/
lemma inclusion_surjective_of_subsingleton (P : FreeProduct X) (b : Bool)
    (hother : ∀ c, c ≠ b → Subsingleton (X c)) : Function.Surjective (P.inclusion b) := by
  obtain ⟨R, hR, _, hRb, _⟩ := P.exists_retraction b
  have hcomp : (P.inclusion b).comp R = ContinuousLinearMap.id ℝ P.Carrier := by
    apply P.extension_ext
      (((P.inclusion_isVecLatHom b).mk' (P.inclusion b)).comp (hR.mk' R)).isVecLatHom
      (VecLatHom.id : VecLatHom P.Carrier P.Carrier).isVecLatHom
    intro c x
    by_cases h : c = b
    · subst c
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, hRb]
    · let := hother c h
      simp [Subsingleton.elim x 0]
  exact fun z ↦ ⟨R z, DFunLike.congr_fun hcomp z⟩

/-- Every included factor element belongs to the range of a suitable free product of principal
ideals. -/
private lemma factor_mem_principal_range (P : FreeProduct X) (b : Bool) (x : X b) :
    ∃ (u : ∀ b, X b) (hu : ∀ b, 0 ≤ u b),
      letI : ∀ b, BanachLattice ↥(OrderIdeal.principalSubmodule (u b)) :=
        fun b ↦
          { toNormedVectorLattice := OrderIdeal.principalNormedVectorLattice (u b)
            toCompleteSpace := principal_completeSpace (u b) (hu b) }
      ∃ Q : FreeProduct (fun b ↦ ↥(OrderIdeal.principalSubmodule (u b))),
        ∃ S : Q.Carrier →L[ℝ] P.Carrier,
          IsVecLatHom S ∧
          (∀ b (x : ↥(OrderIdeal.principalSubmodule (u b))),
            S (Q.inclusion b x) = P.inclusion b (x : X b)) ∧
          P.inclusion b x ∈ Set.range S := by
  classical
  let u (c : Bool) : X c := if h : b = c then h ▸ |x| else 0
  have hu (c : Bool) : 0 ≤ u c := by
    dsimp only [u]
    split_ifs with h
    · subst c
      exact abs_nonneg x
    · exact le_rfl
  have hx : x ∈ OrderIdeal.principalSubmodule (u b) :=
    ⟨1, zero_le_one, by simp [u]⟩
  let : ∀ c, BanachLattice ↥(OrderIdeal.principalSubmodule (u c)) :=
    fun c ↦
      { toNormedVectorLattice := OrderIdeal.principalNormedVectorLattice (u c)
        toCompleteSpace := principal_completeSpace (u c) (hu c) }
  obtain ⟨Q, S, hS, hcomm⟩ := exists_principal_product_map X P u hu
  exact ⟨u, hu, Q, S, hS, hcomm, Q.inclusion b ⟨x, hx⟩, hcomm b ⟨x, hx⟩⟩

/-- Every element of a Banach lattice free product comes from a free
product of principal ideals equipped with their order-unit norms. -/
theorem exists_mem_range_principal_freeProduct
    (P : FreeProduct X) (z : P.Carrier) :
    ∃ (u : ∀ b, X b) (hu : ∀ b, 0 ≤ u b),
      letI : ∀ b, BanachLattice ↥(OrderIdeal.principalSubmodule (u b)) :=
        fun b ↦
          { toNormedVectorLattice := OrderIdeal.principalNormedVectorLattice (u b)
            toCompleteSpace := principal_completeSpace (u b) (hu b) }
      ∃ Q : FreeProduct (fun b ↦ ↥(OrderIdeal.principalSubmodule (u b))),
        ∃ S : Q.Carrier →L[ℝ] P.Carrier,
          IsVecLatHom S ∧
          (∀ b (x : ↥(OrderIdeal.principalSubmodule (u b))),
            S (Q.inclusion b x) = P.inclusion b (x : X b)) ∧
          z ∈ Set.range S := by
  rcases subsingleton_or_nontrivial (X false) with hfalse | hfalse
  · obtain ⟨x, rfl⟩ := inclusion_surjective_of_subsingleton X P true
      (fun c ↦ Bool.rec (motive := fun c ↦ c ≠ true → Subsingleton (X c))
        (fun _ ↦ hfalse) (fun h ↦ (h rfl).elim) c) z
    exact factor_mem_principal_range X P true x
  · rcases subsingleton_or_nontrivial (X true) with htrue | htrue
    · obtain ⟨x, rfl⟩ := inclusion_surjective_of_subsingleton X P false
        (fun c ↦ Bool.rec (motive := fun c ↦ c ≠ false → Subsingleton (X c))
          (fun h ↦ (h rfl).elim) (fun _ ↦ htrue) c) z
      exact factor_mem_principal_range X P false x
    · let : ∀ b, Nontrivial (X b) := Bool.rec hfalse htrue
      obtain ⟨u, hu, Q, S, hS, _, hcomm, hz⟩ :=
        exists_mem_range_principal_freeProduct_nontrivial X P z
      exact ⟨u, fun b ↦ (hu b).le, Q, S, hS, hcomm, hz⟩

end PrincipalIdeals

end BanachLattice.FreeProduct
