/-
Authors: Gonzalo Martínez-Fernández
-/

import FreeProducts.BanachLattice.Basic
import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# Stability and free Banach lattice models

A Banach lattice free product is projective exactly when its factors are projective.
Free Banach lattices over summable direct sums identify with free products of the
individual free Banach lattices. A binary free product with a free Banach lattice factor
also admits an explicit closed-ideal quotient model.
-/

noncomputable section

open scoped Topology Pointwise

universe u v w

namespace BanachLattice

variable {I : Type v} (E : I → Type u)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, Lattice (E i)]
  [∀ i, IsOrderedAddMonoid (E i)] [∀ i, BanachLattice (E i)]

section Stability

/-- A projective Banach lattice admits lifts through closed-ideal quotients
with arbitrarily small multiplicative loss in operator norm. -/
def IsProjective (X : Type u) [NormedAddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [BanachLattice X] : Prop :=
  ∀ (Z : Type w) [NormedAddCommGroup Z] [Lattice Z]
    [IsOrderedAddMonoid Z] [BanachLattice Z]
    (J : OrderIdeal Z) (hJ : IsClosed (J : Set Z)),
    letI := J.quotientNormedAddCommGroup hJ
    letI := J.quotientBanachLattice hJ
    ∀ (T : X →L[ℝ] Z ⧸ J.toSubmodule), IsVecLatHom T →
      ∀ ε : ℝ, 0 < ε →
        ∃ S : X →L[ℝ] Z, IsVecLatHom S ∧
          (∀ x, J.mkQ (S x) = T x) ∧ ‖S‖ ≤ (1 + ε) * ‖T‖

namespace FreeProduct

/-- A free product is projective when each factor is projective. -/
private lemma isProjective_of_factors (P : FreeProduct E)
    (h : ∀ i, IsProjective.{u, w} (E i)) :
    IsProjective.{max u v, w} P.Carrier := by
  classical
  intro Z _ _ _ _ J hJ
  let := J.quotientNormedAddCommGroup hJ
  let := J.quotientBanachLattice hJ
  intro T hT ε hε
  choose S hS hST hSnorm using fun i ↦
    h i Z J hJ (T.comp (P.inclusion i))
      ((hT.mk' T).comp ((P.inclusion_isVecLatHom i).mk' (P.inclusion i))).isVecLatHom
      ε hε
  obtain ⟨R, ⟨hR, hRT, hRnorm⟩, _⟩ :=
    P.exists_unique_extension Z S hS ((1 + ε) * ‖T‖)
      (mul_nonneg (by positivity) (norm_nonneg T))
      (fun i ↦ (hSnorm i).trans (mul_le_mul_of_nonneg_left
        (norm_comp_inclusion_le P T i) (by positivity)))
  have heq : J.toSubmodule.mkQL.comp R = T :=
    P.extension_ext (J.mkQVecLatHom.comp (hR.mk' R)).isVecLatHom hT
      (fun i x ↦ (congrArg J.mkQ (hRT i x)).trans (hST i x))
  exact ⟨R, hR, DFunLike.congr_fun heq, hRnorm⟩

/-- Every factor of a projective Banach lattice free product is projective, using its
canonical retraction. -/
private lemma isProjective_factor (P : FreeProduct E)
    (h : IsProjective.{max u v, w} P.Carrier) (i : I) :
    IsProjective.{u, w} (E i) := by
  intro Z _ _ _ _ J hJ
  let := J.quotientNormedAddCommGroup hJ
  let := J.quotientBanachLattice hJ
  intro T hT ε hε
  obtain ⟨R, hR, hRnorm, hRi, _⟩ := P.exists_retraction i
  obtain ⟨S, hS, hST, hSnorm⟩ := h Z J hJ (T.comp R)
    ((hT.mk' T).comp (hR.mk' R)).isVecLatHom ε hε
  refine ⟨S.comp (P.inclusion i),
    ((hS.mk' S).comp ((P.inclusion_isVecLatHom i).mk' (P.inclusion i))).isVecLatHom,
    fun x ↦ (hST (P.inclusion i x)).trans (congrArg T (hRi x)), ?_⟩
  exact (norm_comp_inclusion_le P S i).trans (hSnorm.trans
    (mul_le_mul_of_nonneg_left ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_left hRnorm (norm_nonneg T)).trans_eq (mul_one ‖T‖)))
      (by positivity)))

/-- A free product is projective exactly when all its factors are projective. -/
theorem isProjective_iff (P : FreeProduct E) :
    IsProjective.{max u v, w} P.Carrier ↔
      ∀ i, IsProjective.{u, w} (E i) := by
  exact ⟨isProjective_factor E P, isProjective_of_factors E P⟩

end FreeProduct

section FreeBanachLattices

/-- A lattice homomorphism on a free Banach lattice is determined by its values on the
original Banach-space generators. -/
private lemma fbl_ext
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {Y : Type*} [NormedAddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] [BanachLattice Y]
    {S T : FBL V →L[ℝ] Y} (hS : IsVecLatHom S) (hT : IsVecLatHom T)
    (h : ∀ x, S (FBL.of x) = T (FBL.of x)) : S = T := by
  exact ContinuousLinearMap.ext fun z ↦ congrArg (fun R : VecLatHom (FBL V) Y ↦ R z)
    ((FBL.lift_unique (T.comp FBL.ofLinearIsometry.toContinuousLinearMap) (hS.mk' S) h).trans
      (FBL.lift_unique (T.comp FBL.ofLinearIsometry.toContinuousLinearMap)
        (hT.mk' T) (fun _ ↦ rfl)).symm)

variable {A : Type v} (V : A → Type u)
  [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]

/-- The free Banach lattice over an l1 sum has the universal property of the free product of
the free Banach lattices over the summands. -/
private lemma fbl_l1_universal
    {Y : Type w} [NormedAddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] [BanachLattice Y]
    [DecidableEq A] (T : ∀ i, FBL (V i) →L[ℝ] Y)
    (hT : ∀ i, IsVecLatHom (T i)) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ i, ‖T i‖ ≤ M) :
    ∃! S : FBL (lp V 1) →L[ℝ] Y,
      IsVecLatHom S ∧
      (∀ i z, S (FBL.lift (FBL.ofLinearIsometry.toContinuousLinearMap.comp
        (lp.singleContinuousLinearMap ℝ V 1 i)) z) = T i z) ∧ ‖S‖ ≤ M := by
  obtain ⟨R, hR, hRnorm⟩ := exists_l1_extension V
    (fun i ↦ (T i).comp FBL.ofLinearIsometry.toContinuousLinearMap) M hM
    (fun i ↦ ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_left
        FBL.ofLinearIsometry.norm_toContinuousLinearMap_le (norm_nonneg (T i))).trans_eq
        (mul_one ‖T i‖))).trans (hbound i))
  have hcomp (i : A) : (FBL.liftContinuousLinearMap R).comp
      (FBL.liftContinuousLinearMap (FBL.ofLinearIsometry.toContinuousLinearMap.comp
        (lp.singleContinuousLinearMap ℝ V 1 i))) = T i :=
    fbl_ext ((FBL.lift R).comp (FBL.lift
      (FBL.ofLinearIsometry.toContinuousLinearMap.comp
        (lp.singleContinuousLinearMap ℝ V 1 i)))).isVecLatHom (hT i)
      (fun x ↦ by simpa only [ContinuousLinearMap.comp_apply,
        FBL.liftContinuousLinearMap_apply, FBL.lift_of,
        LinearIsometry.coe_toContinuousLinearMap, FBL.ofLinearIsometry_apply,
        lp.singleContinuousLinearMap_apply] using hR i x)
  refine ⟨FBL.liftContinuousLinearMap R,
    ⟨(FBL.lift R).isVecLatHom, fun i ↦ DFunLike.congr_fun (hcomp i),
      (FBL.norm_lift R).trans_le hRnorm⟩, ?_⟩
  rintro S ⟨hS, hST, _⟩
  refine fbl_l1_ext V hS (FBL.lift R).isVecLatHom (fun i x ↦ ?_)
  simpa only [FBL.lift_of, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, FBL.ofLinearIsometry_apply,
    lp.singleContinuousLinearMap_apply, FBL.liftContinuousLinearMap_apply, hR] using
    hST i (FBL.of x)

/-- The free Banach lattice over a summable direct sum is lattice isometric
to the free product of the free Banach lattices over its summands. -/
theorem nonempty_fbl_l1_equiv_freeProduct
    [∀ i, CompleteSpace (V i)]
    (P : FreeProduct (fun i ↦ FBL (V i))) :
    Nonempty (BanachLatEquiv (FBL (lp V 1)) P.Carrier) := by
  classical
  let Q : FreeProduct (fun i ↦ FBL (V i)) :=
    { Carrier := FBL (lp V 1)
      inclusion := fun i ↦ FBL.liftContinuousLinearMap
        (FBL.ofLinearIsometry.toContinuousLinearMap.comp
          (lp.singleContinuousLinearMap ℝ V 1 i))
      inclusion_isVecLatHom := fun i ↦ (FBL.lift _).isVecLatHom
      inclusion_contractive := fun i ↦ (FBL.norm_lift _).trans_le
        (ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x ↦ by
          simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
            FBL.ofLinearIsometry_apply, lp.singleContinuousLinearMap_apply,
            FBL.norm_of, lp.norm_single (by norm_num : (0 : ENNReal) < 1), one_mul, le_refl]))
      universal := fun Y _ _ _ _ T hT M hM hbound ↦ fbl_l1_universal V T hT M hM hbound }
  exact ⟨(Q.exists_unique_equiv P).choose⟩

end FreeBanachLattices

section MixedFreeProduct

/-- Combining two maps on an l1 direct sum preserves their common operator-norm bound. -/
private lemma norm_prod_l1_extension_le
    {A B Y : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : A →L[ℝ] Y) (g : B →L[ℝ] Y)
    (M : ℝ) (hM : 0 ≤ M) (hf : ‖f‖ ≤ M) (hg : ‖g‖ ≤ M) :
    ‖(f.coprod g).comp (WithLp.prodContinuousLinearEquiv 1 ℝ A B).toContinuousLinearMap‖
      ≤ M := by
  refine ContinuousLinearMap.opNorm_le_bound _ hM (fun x ↦ ?_)
  exact (norm_add_le (f x.fst) (g x.snd)).trans
    ((add_le_add (f.le_of_opNorm_le hf x.fst) (g.le_of_opNorm_le hg x.snd)).trans_eq
      ((mul_add M ‖x.fst‖ ‖x.snd‖).symm.trans
        (congrArg (M * ·) (WithLp.prod_norm_eq_of_L1 x).symm)))

variable (X : Bool → Type u)
  [∀ b, NormedAddCommGroup (X b)] [∀ b, Lattice (X b)]
  [∀ b, IsOrderedAddMonoid (X b)] [∀ b, BanachLattice (X b)]
  (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A contractive lattice map on the lattice factor and a contractive linear map on the free
factor extend through the mixed quotient. -/
private lemma mixed_quotient_extension
    (J : OrderIdeal (FBL (WithLp 1 (X false × V))))
    (hJ : IsClosed (J : Set (FBL (WithLp 1 (X false × V)))))
    (hJ_eq : J = (OrderIdeal.generated
      {z | ∃ x : X false, z = |FBL.of (WithLp.toLp 1 (x, (0 : V)))| -
        FBL.of (WithLp.toLp 1 (|x|, (0 : V)))}).topologicalClosure)
    {Y : Type w} [NormedAddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] [BanachLattice Y]
    (f : X false →L[ℝ] Y) (hf : IsVecLatHom f) (g : V →L[ℝ] Y)
    (hfnorm : ‖f‖ ≤ 1) (hgnorm : ‖g‖ ≤ 1) :
    letI := J.quotientNormedAddCommGroup hJ
    letI := J.quotientBanachLattice hJ
    ∃ R : (FBL (WithLp 1 (X false × V)) ⧸ J.toSubmodule) →L[ℝ] Y,
      IsVecLatHom R ∧ ‖R‖ ≤ 1 ∧
        ∀ x v, R (J.mkQ (FBL.of (WithLp.toLp 1 (x, v)))) = f x + g v := by
  let := J.quotientNormedAddCommGroup hJ
  let := J.quotientBanachLattice hJ
  let T := (f.coprod g).comp
    (WithLp.prodContinuousLinearEquiv 1 ℝ (X false) V).toContinuousLinearMap
  have hker : J.toSubmodule ≤ (FBL.liftContinuousLinearMap T).ker := by
    rw [hJ_eq, OrderIdeal.topologicalClosure_toSubmodule]
    refine Submodule.topologicalClosure_minimal _ ?_ (FBL.liftContinuousLinearMap T).isClosed_ker
    change OrderIdeal.generated _ ≤ OrderIdeal.ofKerVecLatHom (FBL.lift T)
    apply OrderIdeal.generated_le
    rintro z ⟨x, rfl⟩
    change FBL.lift T (|FBL.of (WithLp.toLp 1 (x, (0 : V)))| -
      FBL.of (WithLp.toLp 1 (|x|, (0 : V)))) = 0
    simpa [map_sub, (FBL.lift T).map_abs, FBL.lift_of, T] using
      sub_eq_zero.mpr ((hf.mk' f).map_abs x).symm
  exact ⟨J.toSubmodule.liftQL (FBL.liftContinuousLinearMap T) hker,
    (J.liftQVecLatHom (FBL.lift T) hker).isVecLatHom,
    (norm_liftQL_le _ _ _).trans ((FBL.norm_lift T).trans_le
      (norm_prod_l1_extension_le f g 1 zero_le_one hfnorm hgnorm)),
    fun x v ↦ FBL.lift_of T (WithLp.toLp 1 (x, v))⟩

/-- Constructs the two contractive lattice inclusions into the mixed quotient model. -/
private lemma mixed_quotient_factor_maps
    (e : BanachLatEquiv (X true) (FBL V))
    (J : OrderIdeal (FBL (WithLp 1 (X false × V))))
    (hJ : IsClosed (J : Set (FBL (WithLp 1 (X false × V)))))
    (hJ_eq : J = (OrderIdeal.generated
      {z | ∃ x : X false, z = |FBL.of (WithLp.toLp 1 (x, (0 : V)))| -
        FBL.of (WithLp.toLp 1 (|x|, (0 : V)))}).topologicalClosure) :
    letI := J.quotientNormedAddCommGroup hJ
    letI := J.quotientBanachLattice hJ
    ∃ T : ∀ b, X b →L[ℝ] (FBL (WithLp 1 (X false × V)) ⧸ J.toSubmodule),
      (∀ b, IsVecLatHom (T b)) ∧ (∀ b, ‖T b‖ ≤ 1) ∧
      (∀ x, T false x = J.mkQ (FBL.of (WithLp.toLp 1 (x, (0 : V))))) ∧
      (∀ v, T true (e.symm (FBL.of v)) =
        J.mkQ (FBL.of (WithLp.toLp 1 ((0 : X false), v)))) := by
  let := J.quotientNormedAddCommGroup hJ
  let := J.quotientBanachLattice hJ
  let d := J.toSubmodule.mkQL.comp FBL.ofLinearIsometry.toContinuousLinearMap
  let a := d.comp
    ((WithLp.prodContinuousLinearEquiv 1 ℝ (X false) V).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl ℝ (X false) V))
  let b := d.comp
    ((WithLp.prodContinuousLinearEquiv 1 ℝ (X false) V).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inr ℝ (X false) V))
  have ha : IsVecLatHom a :=
    (VecLatHom.ofAbs a.toLinearMap (fun x ↦ by
      change J.mkQ (FBL.of (WithLp.toLp 1 (|x|, (0 : V)))) =
        |J.mkQ (FBL.of (WithLp.toLp 1 (x, (0 : V))))|
      rw [← J.mkQ_abs, eq_comm]
      exact (Submodule.Quotient.eq J.toSubmodule).mpr (by
        rw [hJ_eq]
        exact subset_closure (OrderIdeal.subset_generated _ ⟨x, rfl⟩)))).isVecLatHom
  have hanorm : ‖a‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x ↦
    ((Submodule.Quotient.norm_mk_le (S := J.toSubmodule)
      (FBL.of (WithLp.toLp 1 (x, (0 : V))))).trans_eq
        ((FBL.norm_of _).trans (WithLp.norm_toLp_fst 1 (X false) V x))).trans_eq
          (one_mul ‖x‖).symm)
  have hbnorm : ‖b‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v ↦
    ((Submodule.Quotient.norm_mk_le (S := J.toSubmodule)
      (FBL.of (WithLp.toLp 1 ((0 : X false), v)))).trans_eq
        ((FBL.norm_of _).trans (WithLp.norm_toLp_snd 1 (X false) V v))).trans_eq
          (one_mul ‖v‖).symm)
  let T : ∀ k, X k →L[ℝ] (FBL (WithLp 1 (X false × V)) ⧸ J.toSubmodule) :=
    Bool.rec a ((FBL.liftContinuousLinearMap b).comp
      e.toContinuousLinearEquiv.toContinuousLinearMap)
  refine ⟨T, Bool.rec ha ((FBL.lift b).comp e.toVecLatEquiv.toVecLatHom).isVecLatHom,
    Bool.rec hanorm (ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x ↦
      ((FBL.liftContinuousLinearMap b).le_of_opNorm_le
        ((FBL.norm_lift b).trans_le hbnorm) (e x)).trans_eq
          (congrArg (1 * ·) (e.toLinearIsometryEquiv.norm_map x)))), fun _ ↦ rfl, ?_⟩
  exact fun v ↦ (congrArg (FBL.lift b)
    (e.toLinearIsometryEquiv.apply_symm_apply (FBL.of v))).trans (FBL.lift_of b v)

/-- Maps out of the mixed quotient are determined by their values on its canonical
Banach-space generators. -/
private lemma mixed_quotient_ext
    (J : OrderIdeal (FBL (WithLp 1 (X false × V))))
    (hJ : IsClosed (J : Set (FBL (WithLp 1 (X false × V)))))
    {Y : Type w} [NormedAddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] [BanachLattice Y] :
    letI := J.quotientNormedAddCommGroup hJ
    letI := J.quotientBanachLattice hJ
    ∀ {S T : (FBL (WithLp 1 (X false × V)) ⧸ J.toSubmodule) →L[ℝ] Y},
      IsVecLatHom S → IsVecLatHom T →
      (∀ x v, S (J.mkQ (FBL.of (WithLp.toLp 1 (x, v)))) =
        T (J.mkQ (FBL.of (WithLp.toLp 1 (x, v))))) → S = T := by
  let := J.quotientNormedAddCommGroup hJ
  let := J.quotientBanachLattice hJ
  intro S T hS hT h
  have heq : S.comp J.toSubmodule.mkQL = T.comp J.toSubmodule.mkQL :=
    fbl_ext ((hS.mk' S).comp J.mkQVecLatHom).isVecLatHom
      ((hT.mk' T).comp J.mkQVecLatHom).isVecLatHom (fun z ↦ h z.fst z.snd)
  exact ContinuousLinearMap.ext fun z ↦ (J.toSubmodule.mkQ_surjective z).elim
    (fun x hx ↦ hx ▸ DFunLike.congr_fun heq x)

/-- For a free product with one free Banach factor, agreement on the other factor and the free
generators determines the homomorphism. -/
private lemma mixed_extension_ext (P : FreeProduct X)
    (e : BanachLatEquiv (X true) (FBL V))
    {Y : Type w} [NormedAddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] [BanachLattice Y]
    {S T : P.Carrier →L[ℝ] Y} (hS : IsVecLatHom S) (hT : IsVecLatHom T)
    (hfalse : ∀ x, S (P.inclusion false x) = T (P.inclusion false x))
    (htrue : ∀ v, S (P.inclusion true (e.symm (FBL.of v))) =
      T (P.inclusion true (e.symm (FBL.of v)))) : S = T := by
  let c := (P.inclusion true).comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hc : IsVecLatHom c :=
    (((P.inclusion_isVecLatHom true).mk' (P.inclusion true)).comp
      e.symm.toVecLatEquiv.toVecLatHom).isVecLatHom
  have heq : S.comp c = T.comp c :=
    fbl_ext ((hS.mk' S).comp (hc.mk' c)).isVecLatHom
      ((hT.mk' T).comp (hc.mk' c)).isVecLatHom htrue
  refine P.extension_ext hS hT (Bool.rec hfalse (fun x ↦ ?_))
  exact (congrArg (fun z ↦ S (P.inclusion true z))
    (e.toLinearIsometryEquiv.symm_apply_apply x)).symm.trans
      ((DFunLike.congr_fun heq (e x)).trans (congrArg (fun z ↦ T (P.inclusion true z))
        (e.toLinearIsometryEquiv.symm_apply_apply x)))

/-- Constructs mutually inverse contractive lattice maps between the mixed free product and
its quotient model. -/
private lemma mixed_quotient_inverse_maps (P : FreeProduct X)
    (e : BanachLatEquiv (X true) (FBL V))
    (J : OrderIdeal (FBL (WithLp 1 (X false × V))))
    (hJ : IsClosed (J : Set (FBL (WithLp 1 (X false × V)))))
    (hJ_eq : J = (OrderIdeal.generated
      {z | ∃ x : X false, z = |FBL.of (WithLp.toLp 1 (x, (0 : V)))| -
        FBL.of (WithLp.toLp 1 (|x|, (0 : V)))}).topologicalClosure) :
    letI := J.quotientNormedAddCommGroup hJ
    letI := J.quotientBanachLattice hJ
    ∃ (R : P.Carrier →L[ℝ] (FBL (WithLp 1 (X false × V)) ⧸ J.toSubmodule))
      (S : (FBL (WithLp 1 (X false × V)) ⧸ J.toSubmodule) →L[ℝ] P.Carrier),
      IsVecLatHom R ∧ IsVecLatHom S ∧ ‖R‖ ≤ 1 ∧ ‖S‖ ≤ 1 ∧
        S.comp R = ContinuousLinearMap.id ℝ P.Carrier ∧
        R.comp S = ContinuousLinearMap.id ℝ _ := by
  let := J.quotientNormedAddCommGroup hJ
  let := J.quotientBanachLattice hJ
  obtain ⟨T, hT, hTnorm, hTfalse, hTtrue⟩ :=
    mixed_quotient_factor_maps X V e J hJ hJ_eq
  obtain ⟨R, ⟨hR, hRT, hRnorm⟩, _⟩ := P.exists_unique_extension
    (FBL (WithLp 1 (X false × V)) ⧸ J.toSubmodule) T hT 1 zero_le_one hTnorm
  let g := (P.inclusion true).comp (e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    FBL.ofLinearIsometry.toContinuousLinearMap)
  have hgnorm : ‖g‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v ↦
    ((P.inclusion true).le_of_opNorm_le (P.inclusion_contractive true)
      (e.symm (FBL.of v))).trans_eq
        (congrArg (1 * ·) ((e.symm.toLinearIsometryEquiv.norm_map _).trans (FBL.norm_of v))))
  obtain ⟨S, hS, hSnorm, hST⟩ := mixed_quotient_extension X V J hJ hJ_eq
    (P.inclusion false) (P.inclusion_isVecLatHom false) g (P.inclusion_contractive false) hgnorm
  have hRfalse (x : X false) : R (P.inclusion false x) =
      J.mkQ (FBL.of (WithLp.toLp 1 (x, (0 : V)))) :=
    (hRT false x).trans (hTfalse x)
  have hRtrue (v : V) : R (g v) =
      J.mkQ (FBL.of (WithLp.toLp 1 ((0 : X false), v))) :=
    (hRT true (e.symm (FBL.of v))).trans (hTtrue v)
  have hSR : S.comp R = ContinuousLinearMap.id ℝ P.Carrier :=
    mixed_extension_ext X V P e ((hS.mk' S).comp (hR.mk' R)).isVecLatHom
      (VecLatHom.id : VecLatHom P.Carrier P.Carrier).isVecLatHom
      (fun x ↦ by simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
        map_zero, add_zero] using
        (congrArg S (hRfalse x)).trans (hST x 0))
      (fun v ↦ by simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
        show ∀ v, g v = P.inclusion true (e.symm (FBL.of v)) from fun _ ↦ rfl,
        map_zero, zero_add] using
        (congrArg S (hRtrue v)).trans (hST 0 v))
  refine ⟨R, S, hR, hS, hRnorm, hSnorm, hSR,
    mixed_quotient_ext X V J hJ ((hR.mk' R).comp (hS.mk' S)).isVecLatHom
      (VecLatHom.id : VecLatHom _ _).isVecLatHom (fun x v ↦ ?_)⟩
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    hST, map_add, hRfalse, hRtrue]
  let d := J.toSubmodule.mkQL.comp FBL.ofLinearIsometry.toContinuousLinearMap
  exact (d.map_add (WithLp.toLp 1 (x, (0 : V)))
    (WithLp.toLp 1 ((0 : X false), v))).symm.trans (congrArg d (by
      simp only [← WithLp.toLp_add, Prod.mk_add_mk, add_zero, zero_add]))

/-- A binary free product with a free Banach lattice factor is the quotient
obtained by imposing the lattice relations of the other factor. -/
theorem nonempty_freeProduct_fbl_equiv_quotient
    [CompleteSpace V]
    (P : FreeProduct X) (e : BanachLatEquiv (X true) (FBL V))
    (J : OrderIdeal (FBL (WithLp 1 (X false × V))))
    (hJ : IsClosed (J : Set (FBL (WithLp 1 (X false × V)))))
    (hJ_eq : J =
      (OrderIdeal.generated
        {z | ∃ x : X false,
          z = |FBL.of (WithLp.toLp 1 (x, (0 : V)))| -
            FBL.of (WithLp.toLp 1 (|x|, (0 : V)))}).topologicalClosure) :
    letI := J.quotientNormedAddCommGroup hJ
    letI := J.quotientBanachLattice hJ
    Nonempty (BanachLatEquiv P.Carrier
      (FBL (WithLp 1 (X false × V)) ⧸ J.toSubmodule)) := by
  let := J.quotientNormedAddCommGroup hJ
  let := J.quotientBanachLattice hJ
  obtain ⟨R, S, hR, _, hRnorm, hSnorm, hSR, hRS⟩ :=
    mixed_quotient_inverse_maps X V P e J hJ hJ_eq
  let e₀ : P.Carrier ≃ₗ[ℝ] (FBL (WithLp 1 (X false × V)) ⧸ J.toSubmodule) :=
    { R.toLinearMap with
      invFun := S
      left_inv := DFunLike.congr_fun hSR
      right_inv := DFunLike.congr_fun hRS }
  exact ⟨{
    LinearIsometryEquiv.ofBounds e₀
      (fun x ↦ (R.le_of_opNorm_le hRnorm x).trans_eq (one_mul ‖x‖))
      (fun y ↦ (S.le_of_opNorm_le hSnorm y).trans_eq (one_mul ‖y‖)) with
    map_sup' := hR.map_sup'
    map_inf' := hR.map_inf' }⟩

end MixedFreeProduct

end Stability

end BanachLattice
