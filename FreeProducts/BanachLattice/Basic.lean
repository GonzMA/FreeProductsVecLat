/-
Authors: Gonzalo Martínez-Fernández
-/

import BanLat.Free.FBL
import BanLat.Operators.Hom
import BanLat.Quotient
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.Seminorm.Basic

/-!
# Free products of Banach lattices

Free products of arbitrary families of Banach lattices exist and extend uniformly
bounded families of lattice homomorphisms without increasing the common norm bound.
The canonical inclusions are isometries and admit contractive lattice retractions.
The generated vector sublattice is dense, and free products are unique up to a canonical
lattice isometry, invariant under reindexing, and compatible with grouping factors.
-/

noncomputable section

open scoped Topology Pointwise

universe u v w

namespace BanachLattice

variable {I : Type v} (E : I → Type u)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, Lattice (E i)]
  [∀ i, IsOrderedAddMonoid (E i)] [∀ i, BanachLattice (E i)]

/-- A free product has contractive canonical lattice homomorphisms and uniquely
extends uniformly bounded families of lattice homomorphisms. -/
structure FreeProduct where
  Carrier : Type (max u v)
  [normedAddCommGroup : NormedAddCommGroup Carrier]
  [lattice : Lattice Carrier]
  [isOrderedAddMonoid : IsOrderedAddMonoid Carrier]
  [banachLattice : BanachLattice Carrier]
  inclusion : ∀ i, E i →L[ℝ] Carrier
  inclusion_isVecLatHom : ∀ i, IsVecLatHom (inclusion i)
  inclusion_contractive : ∀ i, ‖inclusion i‖ ≤ 1
  universal :
    ∀ (Y : Type (max u v)) [NormedAddCommGroup Y] [Lattice Y]
      [IsOrderedAddMonoid Y] [BanachLattice Y]
      (T : ∀ i, E i →L[ℝ] Y),
      (∀ i, IsVecLatHom (T i)) →
      ∀ M : ℝ, 0 ≤ M → (∀ i, ‖T i‖ ≤ M) →
        ∃! S : Carrier →L[ℝ] Y,
          IsVecLatHom S ∧
          (∀ i x, S (inclusion i x) = T i x) ∧ ‖S‖ ≤ M

attribute [instance] FreeProduct.normedAddCommGroup FreeProduct.lattice
  FreeProduct.isOrderedAddMonoid FreeProduct.banachLattice

/-- Descending a bounded linear map through a quotient does not increase its operator norm. -/
lemma norm_liftQL_le
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (J : Submodule ℝ X) (T : X →L[ℝ] Y) (hker : J ≤ T.ker) :
    ‖J.liftQL T hker‖ ≤ ‖T‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) ?_
  intro x
  let f : NormedAddGroupHom X Y :=
    { T.toAddMonoidHom with bound' := ⟨‖T‖, T.le_opNorm⟩ }
  have hf : ∀ z ∈ J.toAddSubgroup, f z = 0 := fun z hz ↦ hker hz
  have hnorm : ‖f‖ ≤ ‖T‖ :=
    NormedAddGroupHom.opNorm_le_bound _ (norm_nonneg T) T.le_opNorm
  exact (QuotientAddGroup.norm_lift_apply_le f hf x).trans
    (mul_le_mul_of_nonneg_right hnorm (norm_nonneg x))

/-- A uniformly bounded family of maps extends to the l1 sum with the same common norm bound. -/
lemma exists_l1_extension {I : Type v} (E : I → Type u)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] [DecidableEq I]
    {Y : Type w} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (T : ∀ i, E i →L[ℝ] Y) (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ i, ‖T i‖ ≤ M) :
    ∃ S : lp E 1 →L[ℝ] Y,
      (∀ i x, S (lp.single 1 i x) = T i x) ∧ ‖S‖ ≤ M := by
  refine ⟨(lp.tsumCLM ℝ I Y).comp (lp.mapCLM 1 T hM hbound), ?_, ?_⟩
  case refine_2 =>
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul lp.norm_tsumCLM_le (lp.norm_mapCLM_le 1 T hM hbound)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul M))
  intro i x
  change (∑' j, T j (lp.single 1 i x j)) = T i x
  simpa only [lp.single_apply_self] using
    (tsum_eq_single i (f := fun j ↦ T j (lp.single 1 i x j))
      (fun j hji ↦ by simp [lp.single_apply, hji]))

/-- The free extension of factor lattice homomorphisms kills the closed ideal imposing the
factor lattice relations. -/
private lemma lift_relation_ideal_le_ker [DecidableEq I]
    {Y : Type w} [NormedAddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] [BanachLattice Y]
    (T : ∀ i, E i →L[ℝ] Y) (hT : ∀ i, IsVecLatHom (T i))
    (S : lp E 1 →L[ℝ] Y) (hS : ∀ i x, S (lp.single 1 i x) = T i x) :
    let relations : Set (FBL (lp E 1)) :=
      {z | ∃ (i : I) (x y : E i), z = FBL.of (lp.single 1 i (x ⊔ y)) -
        (FBL.of (lp.single 1 i x) ⊔ FBL.of (lp.single 1 i y))}
    (OrderIdeal.generated relations).toSubmodule.topologicalClosure ≤
      (FBL.liftContinuousLinearMap S).ker := by
  dsimp only
  refine Submodule.topologicalClosure_minimal _ ?_
    (FBL.liftContinuousLinearMap S).isClosed_ker
  change OrderIdeal.generated _ ≤ OrderIdeal.ofKerVecLatHom (FBL.lift S)
  apply OrderIdeal.generated_le
  rintro z ⟨i, x, y, rfl⟩
  change FBL.lift S (FBL.of (lp.single 1 i (x ⊔ y)) -
    (FBL.of (lp.single 1 i x) ⊔ FBL.of (lp.single 1 i y))) = 0
  simp only [map_sub, map_sup, FBL.lift_of, hS, (hT i).map_sup', sub_self]

/-- Homomorphisms from the free Banach lattice over an l1 sum are determined by the generators
from the individual summands. -/
lemma fbl_l1_ext {I : Type v} (E : I → Type u)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] [DecidableEq I]
    {Y : Type w} [NormedAddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] [BanachLattice Y]
    {S T : FBL (lp E 1) →L[ℝ] Y} (hS : IsVecLatHom S) (hT : IsVecLatHom T)
    (h : ∀ i x, S (FBL.of (lp.single 1 i x)) = T (FBL.of (lp.single 1 i x))) :
    S = T := by
  have hlin : S.comp FBL.ofLinearIsometry.toContinuousLinearMap =
      T.comp FBL.ofLinearIsometry.toContinuousLinearMap := by
    apply lp.ext_continuousLinearMap (by norm_num)
    exact fun i ↦ ContinuousLinearMap.ext fun x ↦ h i x
  have hleft := FBL.lift_unique (S.comp FBL.ofLinearIsometry.toContinuousLinearMap)
    (hS.mk' S) (fun _ ↦ rfl)
  have hright := FBL.lift_unique (T.comp FBL.ofLinearIsometry.toContinuousLinearMap)
    (hT.mk' T) (fun _ ↦ rfl)
  exact ContinuousLinearMap.ext fun z ↦ congrArg (fun R : VecLatHom (FBL (lp E 1)) Y ↦ R z)
    (hleft.trans ((congrArg FBL.lift hlin).trans hright.symm))

/-- The quotient imposing the factor lattice relations satisfies the bounded universal
property of a Banach free product. -/
private lemma quotient_l1_universal [DecidableEq I]
    (J : OrderIdeal (FBL (lp E 1))) (hJ : IsClosed (J : Set (FBL (lp E 1))))
    (hJdef : J = (OrderIdeal.generated
      {z | ∃ (i : I) (x y : E i), z = FBL.of (lp.single 1 i (x ⊔ y)) -
        (FBL.of (lp.single 1 i x) ⊔ FBL.of (lp.single 1 i y))}).topologicalClosure)
    {Y : Type w} [NormedAddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] [BanachLattice Y]
    (T : ∀ i, E i →L[ℝ] Y) (hT : ∀ i, IsVecLatHom (T i))
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ i, ‖T i‖ ≤ M) :
    letI := J.quotientNormedAddCommGroup hJ
    letI := J.quotientBanachLattice hJ
    ∃! S : (FBL (lp E 1) ⧸ J.toSubmodule) →L[ℝ] Y,
      IsVecLatHom S ∧
      (∀ i x, S (J.mkQ (FBL.of (lp.single 1 i x))) = T i x) ∧ ‖S‖ ≤ M := by
  let := J.quotientNormedAddCommGroup hJ
  let := J.quotientBanachLattice hJ
  obtain ⟨R, hR, hRnorm⟩ := exists_l1_extension E T M hM hbound
  have hker : J.toSubmodule ≤ (FBL.liftContinuousLinearMap R).ker := by
    simpa only [hJdef, OrderIdeal.topologicalClosure_toSubmodule] using
      lift_relation_ideal_le_ker E T hT R hR
  refine ⟨J.toSubmodule.liftQL (FBL.liftContinuousLinearMap R) hker, ?_, ?_⟩
  case refine_2 =>
    rintro S ⟨hS, hST, _⟩
    have hcomp : S.comp J.toSubmodule.mkQL = FBL.liftContinuousLinearMap R :=
      fbl_l1_ext E ((hS.mk' S).comp J.mkQVecLatHom).isVecLatHom
        (FBL.lift R).isVecLatHom (fun i x ↦ by
          simpa only [ContinuousLinearMap.comp_apply, Submodule.mkQL_apply,
            FBL.liftContinuousLinearMap_apply, FBL.lift_of, hR] using hST i x)
    ext z
    obtain ⟨x, rfl⟩ := J.toSubmodule.mkQ_surjective z
    exact DFunLike.congr_fun hcomp x
  refine ⟨(J.liftQVecLatHom (FBL.lift R) hker).isVecLatHom, ?_, ?_⟩
  · exact fun i x ↦ (FBL.lift_of R (lp.single 1 i x)).trans (hR i x)
  · exact (norm_liftQL_le _ _ _).trans ((FBL.norm_lift R).trans_le hRnorm)

/-- The canonical factor maps into the quotient preserve suprema because their defects belong
to the defining ideal. -/
private lemma quotient_l1_map_sup [DecidableEq I]
    (J : OrderIdeal (FBL (lp E 1)))
    (hJdef : J = (OrderIdeal.generated
      {z | ∃ (i : I) (x y : E i), z = FBL.of (lp.single 1 i (x ⊔ y)) -
        (FBL.of (lp.single 1 i x) ⊔ FBL.of (lp.single 1 i y))}).topologicalClosure)
    (i : I) (x y : E i) :
    J.mkQ (FBL.of (lp.single 1 i (x ⊔ y))) =
      J.mkQ (FBL.of (lp.single 1 i x)) ⊔ J.mkQ (FBL.of (lp.single 1 i y)) := by
  rw [← J.mkQ_sup]
  apply (Submodule.Quotient.eq J.toSubmodule).mpr
  rw [hJdef]
  exact subset_closure (OrderIdeal.subset_generated _ ⟨i, x, y, rfl⟩)

/-- Constructs a Banach free-product model with the norm-controlled universal property for
targets in an arbitrary universe. -/
private lemma exists_freeProduct_model :
    ∃ P : FreeProduct E,
      ∀ (Y : Type w) [NormedAddCommGroup Y] [Lattice Y]
        [IsOrderedAddMonoid Y] [BanachLattice Y]
        (T : ∀ i, E i →L[ℝ] Y),
        (∀ i, IsVecLatHom (T i)) →
        ∀ M : ℝ, 0 ≤ M → (∀ i, ‖T i‖ ≤ M) →
          ∃! S : P.Carrier →L[ℝ] Y,
            IsVecLatHom S ∧ (∀ i x, S (P.inclusion i x) = T i x) ∧ ‖S‖ ≤ M := by
  classical
  let J₀ : OrderIdeal (FBL (lp E 1)) := OrderIdeal.generated
    {z | ∃ (i : I) (x y : E i), z = FBL.of (lp.single 1 i (x ⊔ y)) -
      (FBL.of (lp.single 1 i x) ⊔ FBL.of (lp.single 1 i y))}
  let J := J₀.topologicalClosure
  have hJ : IsClosed (J : Set (FBL (lp E 1))) := isClosed_closure
  let := J.quotientNormedAddCommGroup hJ
  let := J.quotientBanachLattice hJ
  let ι (i : I) : E i →L[ℝ] (FBL (lp E 1) ⧸ J.toSubmodule) :=
    J.toSubmodule.mkQL.comp
      (FBL.ofLinearIsometry.toContinuousLinearMap.comp (lp.singleContinuousLinearMap ℝ E 1 i))
  have hsup : ∀ i (x y : E i), ι i (x ⊔ y) = ι i x ⊔ ι i y :=
    quotient_l1_map_sup E J rfl
  have hlat : ∀ i, IsVecLatHom (ι i) := fun i ↦
    { map_add := (ι i).map_add
      map_smul := (ι i).map_smul
      map_sup' := hsup i
      map_inf' := fun x y ↦ by
        simpa only [← neg_inf, map_neg, neg_inj] using hsup i (-x) (-y) }
  have hnorm : ∀ i, ‖ι i‖ ≤ 1 := by
    intro i
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
    intro x
    change ‖J.mkQ (FBL.of (lp.single 1 i x))‖ ≤ 1 * ‖x‖
    convert (show ‖(Submodule.Quotient.mk (FBL.of (lp.single 1 i x)) :
        FBL (lp E 1) ⧸ J.toSubmodule)‖ ≤ ‖FBL.of (lp.single 1 i x)‖ from
      Submodule.Quotient.norm_mk_le (S := J.toSubmodule) (FBL.of (lp.single 1 i x))) using 1
    · rfl
    · simp only [FBL.norm_of, lp.norm_single (by norm_num : (0 : ENNReal) < 1), one_mul]
  refine ⟨{
    Carrier := FBL (lp E 1) ⧸ J.toSubmodule
    inclusion := ι
    inclusion_isVecLatHom := hlat
    inclusion_contractive := hnorm
    universal := ?_
  }, ?_⟩
  all_goals
    exact fun Y _ _ _ _ T hT M hM hbound ↦ quotient_l1_universal E J hJ rfl T hT M hM hbound

/-- Every indexed family of Banach lattices has a free product. -/
theorem nonempty_freeProduct : Nonempty (FreeProduct E) := by
  exact ⟨(exists_freeProduct_model.{u, v, 0} E).choose⟩

namespace FreeProduct

variable {E} (P : FreeProduct E)

/-- Restricting a bounded map to a canonical factor cannot increase its norm. -/
lemma norm_comp_inclusion_le
    {Y : Type w} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (S : P.Carrier →L[ℝ] Y) (i : I) : ‖S.comp (P.inclusion i)‖ ≤ ‖S‖ := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_left (P.inclusion_contractive i) (norm_nonneg S)).trans_eq
      (mul_one ‖S‖))

/-- Lattice homomorphisms into a target in the model's universe are determined by their
restrictions to all factors. -/
private lemma extension_ext_same
    {Y : Type (max u v)} [NormedAddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] [BanachLattice Y]
    {S T : P.Carrier →L[ℝ] Y} (hS : IsVecLatHom S) (hT : IsVecLatHom T)
    (h : ∀ i x, S (P.inclusion i x) = T (P.inclusion i x)) : S = T := by
  obtain ⟨R, _, huniq⟩ := P.universal Y (fun i ↦ S.comp (P.inclusion i))
    (fun i ↦ ((hS.mk' S).comp ((P.inclusion_isVecLatHom i).mk' (P.inclusion i))).isVecLatHom)
    (max ‖S‖ ‖T‖) ((norm_nonneg S).trans (le_max_left _ _))
    (fun i ↦ (norm_comp_inclusion_le P S i).trans (le_max_left _ _))
  exact (huniq S ⟨hS, fun _ _ ↦ rfl, le_max_left _ _⟩).trans
    (huniq T ⟨hT, fun i x ↦ (h i x).symm, le_max_right _ _⟩).symm

/-- Maps between free-product models preserving the factor inclusions compose to the identity. -/
private lemma comp_eq_id (Q : FreeProduct E)
    (S : P.Carrier →L[ℝ] Q.Carrier) (T : Q.Carrier →L[ℝ] P.Carrier)
    (hS : IsVecLatHom S) (hT : IsVecLatHom T)
    (hSP : ∀ i x, S (P.inclusion i x) = Q.inclusion i x)
    (hTQ : ∀ i x, T (Q.inclusion i x) = P.inclusion i x) :
    T.comp S = ContinuousLinearMap.id ℝ P.Carrier := by
  apply extension_ext_same P ((hT.mk' T).comp (hS.mk' S)).isVecLatHom
    (VecLatHom.id : VecLatHom P.Carrier P.Carrier).isVecLatHom
  exact fun i x ↦ (congrArg T (hSP i x)).trans (hTQ i x)

/-- The vector sublattice generated by the canonical copies of the factors. -/
def generated : VectorSublattice P.Carrier :=
  VectorSublattice.generated
    (Set.range (fun x : Σ i, E i ↦ P.inclusion x.1 x.2))

/-- The universal extension property also holds for targets in other universes. -/
theorem exists_unique_extension
    (Y : Type w) [NormedAddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] [BanachLattice Y]
    (T : ∀ i, E i →L[ℝ] Y)
    (hT : ∀ i, IsVecLatHom (T i))
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ i, ‖T i‖ ≤ M) :
    ∃! S : P.Carrier →L[ℝ] Y,
      IsVecLatHom S ∧
      (∀ i x, S (P.inclusion i x) = T i x) ∧ ‖S‖ ≤ M := by
  obtain ⟨Q, hQ⟩ := exists_freeProduct_model.{u, v, w} E
  obtain ⟨f, ⟨hf, hfP, hfnorm⟩, _⟩ :=
    P.universal Q.Carrier Q.inclusion Q.inclusion_isVecLatHom 1 zero_le_one
      Q.inclusion_contractive
  obtain ⟨g, ⟨hg, hgQ, hgnorm⟩, _⟩ :=
    Q.universal P.Carrier P.inclusion P.inclusion_isVecLatHom 1 zero_le_one
      P.inclusion_contractive
  have hgf := comp_eq_id P Q f g hf hg hfP hgQ
  obtain ⟨R, ⟨hR, hRT, hRnorm⟩, huniq⟩ := hQ Y T hT M hM hbound
  refine ⟨R.comp f, ⟨((hR.mk' R).comp (hf.mk' f)).isVecLatHom, ?_, ?_⟩, ?_⟩
  case refine_3 =>
    rintro S ⟨hS, hST, hSnorm⟩
    have hcomp : S.comp g = R := huniq _
      ⟨((hS.mk' S).comp (hg.mk' g)).isVecLatHom,
        fun i x ↦ (congrArg S (hgQ i x)).trans (hST i x),
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (((mul_le_mul_of_nonneg_left hgnorm (norm_nonneg S)).trans_eq
            (mul_one ‖S‖)).trans hSnorm)⟩
    simpa only [ContinuousLinearMap.comp_assoc, hgf, ContinuousLinearMap.comp_id] using
      congrArg (fun U ↦ U.comp f) hcomp
  case refine_1 =>
    exact fun i x ↦ (congrArg R (hfP i x)).trans (hRT i x)
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (((mul_le_mul_of_nonneg_left hfnorm (norm_nonneg R)).trans_eq
      (mul_one ‖R‖)).trans hRnorm)

/-- Two free products have a unique lattice isometric equivalence fixing
all canonical copies of the factors. -/
theorem exists_unique_equiv (Q : FreeProduct E) :
    ∃! e : BanachLatEquiv P.Carrier Q.Carrier,
      ∀ i x, e (P.inclusion i x) = Q.inclusion i x := by
  obtain ⟨f, ⟨hf, hfP, hfnorm⟩, _⟩ :=
    P.universal Q.Carrier Q.inclusion Q.inclusion_isVecLatHom 1 zero_le_one
      Q.inclusion_contractive
  obtain ⟨g, ⟨hg, hgQ, hgnorm⟩, _⟩ :=
    Q.universal P.Carrier P.inclusion P.inclusion_isVecLatHom 1 zero_le_one
      P.inclusion_contractive
  let e₀ : P.Carrier ≃ₗ[ℝ] Q.Carrier :=
    { f.toLinearMap with
      invFun := g
      left_inv := DFunLike.congr_fun (comp_eq_id P Q f g hf hg hfP hgQ)
      right_inv := DFunLike.congr_fun (comp_eq_id Q P g f hg hf hgQ hfP) }
  let e : BanachLatEquiv P.Carrier Q.Carrier :=
    { LinearIsometryEquiv.ofBounds e₀
        (fun x ↦ (f.le_of_opNorm_le hfnorm x).trans_eq (one_mul ‖x‖))
        (fun y ↦ (g.le_of_opNorm_le hgnorm y).trans_eq (one_mul ‖y‖)) with
      map_sup' := hf.map_sup'
      map_inf' := hf.map_inf' }
  refine ⟨e, hfP, ?_⟩
  intro e' he'
  have hmap : e'.toContinuousLinearEquiv.toContinuousLinearMap = f :=
    extension_ext_same P e'.toVecLatEquiv.toVecLatHom.isVecLatHom hf
      (fun i x ↦ (he' i x).trans (hfP i x).symm)
  exact DFunLike.ext _ _ (fun x ↦ DFunLike.congr_fun hmap x)

/-- Each canonical factor admits a contractive lattice retraction that vanishes on every other
factor. -/
private lemma factor_retraction (i : I) :
    ∃ R : P.Carrier →L[ℝ] E i,
      IsVecLatHom R ∧ ‖R‖ ≤ 1 ∧
      (∀ x, R (P.inclusion i x) = x) ∧
      (∀ j, j ≠ i → ∀ x, R (P.inclusion j x) = 0) := by
  classical
  let T : ∀ j, E j →L[ℝ] E i := Pi.single i (ContinuousLinearMap.id ℝ (E i))
  have hT (j : I) : IsVecLatHom (T j) := by
    by_cases hji : j = i
    case neg =>
      exact
        { map_add := (T j).map_add
          map_smul := (T j).map_smul
          map_sup' := fun x y ↦ by simp [T, Pi.single_eq_of_ne hji]
          map_inf' := fun x y ↦ by simp [T, Pi.single_eq_of_ne hji] }
    subst j
    simp only [T, Pi.single_eq_same]
    exact (VecLatHom.id : VecLatHom (E i) (E i)).isVecLatHom
  have hbound (j : I) : ‖T j‖ ≤ 1 := by
    by_cases hji : j = i
    case neg => simp [T, Pi.single_eq_of_ne hji]
    subst j
    simpa only [T, Pi.single_eq_same] using
      (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E i))
  obtain ⟨R, ⟨hR, hRT, hRnorm⟩, _⟩ :=
    P.exists_unique_extension (E i) T hT 1 zero_le_one hbound
  refine ⟨R, hR, hRnorm, ?_, ?_⟩
  · simpa [T] using hRT i
  · exact fun j hji x ↦ by simpa [T, Pi.single_eq_of_ne hji] using hRT j x

/-- Each canonical inclusion is an isometry. -/
theorem isometry_inclusion (i : I) :
    Isometry (P.inclusion i) := by
  obtain ⟨R, _, hRnorm, hRi, _⟩ := factor_retraction P i
  apply AddMonoidHomClass.isometry_of_norm (P.inclusion i)
  exact fun x ↦ le_antisymm
    (((P.inclusion i).le_of_opNorm_le (P.inclusion_contractive i) x).trans_eq (one_mul ‖x‖))
    (by simpa only [hRi, one_mul] using R.le_of_opNorm_le hRnorm (P.inclusion i x))

/-- Continuous linear maps out of a free product are determined by their
values on the canonical factors. -/
theorem extension_ext
    {Y : Type w} [NormedAddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] [BanachLattice Y]
    {S T : P.Carrier →L[ℝ] Y}
    (hS : IsVecLatHom S) (hT : IsVecLatHom T)
    (h : ∀ i x, S (P.inclusion i x) = T (P.inclusion i x)) :
    S = T := by
  obtain ⟨R, _, huniq⟩ := P.exists_unique_extension Y (fun i ↦ S.comp (P.inclusion i))
    (fun i ↦ ((hS.mk' S).comp ((P.inclusion_isVecLatHom i).mk' (P.inclusion i))).isVecLatHom)
    (max ‖S‖ ‖T‖) ((norm_nonneg S).trans (le_max_left _ _))
    (fun i ↦ (norm_comp_inclusion_le P S i).trans (le_max_left _ _))
  exact (huniq S ⟨hS, fun _ _ ↦ rfl, le_max_left _ _⟩).trans
    (huniq T ⟨hT, fun i x ↦ (h i x).symm, le_max_right _ _⟩).symm

/-- The extension norm is the supremum of the norms of its restrictions.
The supremum of the empty family is zero. -/
theorem norm_extension
    {Y : Type w} [NormedAddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] [BanachLattice Y]
    (T : ∀ i, E i →L[ℝ] Y) (S : P.Carrier →L[ℝ] Y)
    (hS : IsVecLatHom S)
    (hST : ∀ i x, S (P.inclusion i x) = T i x) :
    ‖S‖ = ⨆ i, ‖T i‖ := by
  have hcomp (i : I) : S.comp (P.inclusion i) = T i := ContinuousLinearMap.ext (hST i)
  have hbound (i : I) : ‖T i‖ ≤ ‖S‖ :=
    (congrArg norm (hcomp i)).symm.trans_le (norm_comp_inclusion_le P S i)
  have hb : BddAbove (Set.range fun i ↦ ‖T i‖) :=
    ⟨‖S‖, Set.forall_mem_range.mpr hbound⟩
  have hnonneg : 0 ≤ ⨆ i, ‖T i‖ := Real.iSup_nonneg (fun i ↦ norm_nonneg (T i))
  obtain ⟨R, ⟨hR, hRT, hRnorm⟩, _⟩ :=
    P.exists_unique_extension Y T
      (fun i ↦ hcomp i ▸
        ((hS.mk' S).comp ((P.inclusion_isVecLatHom i).mk' (P.inclusion i))).isVecLatHom)
      (⨆ i, ‖T i‖) hnonneg (le_ciSup hb)
  exact le_antisymm
    ((congrArg norm (P.extension_ext hS hR
      (fun i x ↦ (hST i x).trans (hRT i x).symm))).trans_le hRnorm)
    (Real.iSup_le hbound (norm_nonneg S))

/-- Every element of the generated sublattice is a finite lattice-linear
expression in elements of the canonical factors. -/
theorem exists_expression (z : P.generated) :
    ∃ (n : ℕ) (i : Fin n → I) (x : ∀ j, E (i j)) (e : LLexpr n),
      (z : P.Carrier) =
        LLexpr.eval (fun j ↦ P.inclusion (i j) (x j)) e := by
  classical
  have hz := z.property
  change (z : P.Carrier) ∈ (VectorSublattice.generated
    (Set.range (fun x : Σ i, E i ↦ P.inclusion x.1 x.2)) : Set P.Carrier) at hz
  rw [LLexpr.generated_eq_iUnion_combinations] at hz
  simp only [Set.mem_iUnion, LLexpr.combinations, Set.mem_range] at hz
  obtain ⟨n, x, e, he⟩ := hz
  choose y hy using fun j ↦ (x j).property
  exact ⟨n, fun j ↦ (y j).1, fun j ↦ (y j).2, e,
    he.symm.trans (congrArg (fun a : Fin n → P.Carrier ↦ LLexpr.eval a e)
      (funext fun j ↦ (hy j).symm))⟩

/-- An extension evaluates lattice-linear expressions by applying the given
maps to their variables. -/
theorem extension_eval
    {Y : Type w} [NormedAddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] [BanachLattice Y]
    (T : ∀ i, E i →L[ℝ] Y) (S : P.Carrier →L[ℝ] Y)
    (hS : IsVecLatHom S)
    (hST : ∀ i x, S (P.inclusion i x) = T i x)
    {n : ℕ} (i : Fin n → I) (x : ∀ j, E (i j)) (e : LLexpr n) :
    S (LLexpr.eval (fun j ↦ P.inclusion (i j) (x j)) e) =
      LLexpr.eval (fun j ↦ T (i j) (x j)) e := by
  simpa only [IsVecLatHom.mk'_apply, hST] using
    LLexpr.map_eval (hS.mk' S) (fun j ↦ P.inclusion (i j) (x j)) e

/-- Reindexing the family by an equivalence preserves the bounded extension property. -/
private lemma reindex_extension {J : Type v} (σ : J ≃ I)
    {Y : Type w} [NormedAddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] [BanachLattice Y]
    (T : ∀ j, E (σ j) →L[ℝ] Y) (hT : ∀ j, IsVecLatHom (T j))
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ j, ‖T j‖ ≤ M) :
    ∃! S : P.Carrier →L[ℝ] Y,
      IsVecLatHom S ∧ (∀ j x, S (P.inclusion (σ j) x) = T j x) ∧ ‖S‖ ≤ M := by
  let T' := Equiv.piCongrLeft (fun i ↦ E i →L[ℝ] Y) σ T
  have hT' (i : I) : IsVecLatHom (T' i) ∧ ‖T' i‖ ≤ M := by
    obtain ⟨j, rfl⟩ := σ.surjective i
    simpa only [T', Equiv.piCongrLeft_apply_apply] using And.intro (hT j) (hbound j)
  obtain ⟨S, ⟨hS, hST, hSnorm⟩, huniq⟩ :=
    P.exists_unique_extension Y T' (fun i ↦ (hT' i).1) M hM (fun i ↦ (hT' i).2)
  refine ⟨S, ⟨hS, fun j x ↦ ?_, hSnorm⟩, ?_⟩
  · simpa only [T', Equiv.piCongrLeft_apply_apply] using hST (σ j) x
  rintro R ⟨hR, hRT, hRnorm⟩
  refine huniq R ⟨hR, fun i x ↦ ?_, hRnorm⟩
  obtain ⟨j, rfl⟩ := σ.surjective i
  simpa only [T', Equiv.piCongrLeft_apply_apply] using hRT j x

/-- Relabeling the factors preserves the free product up to lattice isometry. -/
theorem nonempty_equiv_reindex
    {J : Type v} (σ : J ≃ I)
    (Q : FreeProduct (fun j ↦ E (σ j))) :
    Nonempty (BanachLatEquiv P.Carrier Q.Carrier) := by
  let R : FreeProduct (fun j ↦ E (σ j)) :=
    { Carrier := P.Carrier
      inclusion := fun j ↦ P.inclusion (σ j)
      inclusion_isVecLatHom := fun j ↦ P.inclusion_isVecLatHom (σ j)
      inclusion_contractive := fun j ↦ P.inclusion_contractive (σ j)
      universal := fun Y _ _ _ _ T hT M hM hbound ↦
        reindex_extension P σ T hT M hM hbound }
  exact ⟨(R.exists_unique_equiv Q).choose⟩

/-- The canonical factors generate a dense vector sublattice. -/
theorem dense_generated :
    Dense (P.generated : Set P.Carrier) := by
  let C := P.generated.topologicalClosure
  let := C.banachLatticeCoe P.generated.isClosed_topologicalClosure
  have hmem (i : I) (x : E i) : P.inclusion i x ∈ C :=
    P.generated.le_topologicalClosure
      (VectorSublattice.subset_generated _ ⟨⟨i, x⟩, rfl⟩)
  let T (i : I) : E i →L[ℝ] C := (P.inclusion i).codRestrict C.toSubmodule (hmem i)
  have hT (i : I) : IsVecLatHom (T i) :=
    { map_add := (T i).map_add
      map_smul := (T i).map_smul
      map_sup' := fun x y ↦ Subtype.ext ((P.inclusion_isVecLatHom i).map_sup' x y)
      map_inf' := fun x y ↦ Subtype.ext ((P.inclusion_isVecLatHom i).map_inf' x y) }
  have hbound (i : I) : ‖T i‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      (fun x ↦ (P.inclusion i).le_of_opNorm_le (P.inclusion_contractive i) x)
  obtain ⟨R, ⟨hR, hRT, _⟩, _⟩ := P.exists_unique_extension C T hT 1 zero_le_one hbound
  have heq : C.toSubmodule.subtypeL.comp R = ContinuousLinearMap.id ℝ P.Carrier :=
    P.extension_ext (C.subtype.comp (hR.mk' R)).isVecLatHom
      (VecLatHom.id : VecLatHom P.Carrier P.Carrier).isVecLatHom
      (fun i x ↦ congrArg Subtype.val (hRT i x))
  intro x
  exact (show (R x : P.Carrier) = x from DFunLike.congr_fun heq x) ▸ (R x).property

/-- Each canonical factor has a contractive lattice retraction. -/
theorem exists_retraction (i : I) :
    ∃ R : P.Carrier →L[ℝ] E i,
      IsVecLatHom R ∧ ‖R‖ ≤ 1 ∧
      (∀ x, R (P.inclusion i x) = x) ∧
      (∀ j, j ≠ i → ∀ x, R (P.inclusion j x) = 0) := by
  exact factor_retraction P i

/-- A lattice norm on the generated sublattice making the canonical maps
contractive is bounded above by the free product norm. -/
theorem seminorm_le_norm
    (p : Seminorm ℝ P.generated)
    (hdef : ∀ z, p z = 0 → z = 0)
    (hsolid : ∀ z w, |z| ≤ |w| → p z ≤ p w)
    (hfactor : ∀ i x (z : P.generated),
      (z : P.Carrier) = P.inclusion i x → p z ≤ ‖x‖) :
    ∀ z : P.generated, p z ≤ ‖(z : P.Carrier)‖ := by
  let q : AddGroupNorm P.generated :=
    { p.toAddGroupSeminorm with eq_zero_of_map_eq_zero' := hdef }
  let : NormedAddCommGroup P.generated := q.toNormedAddCommGroup
  let : PseudoMetricSpace P.generated := q.toNormedAddCommGroup.toPseudoMetricSpace
  let : UniformSpace P.generated := q.toNormedAddCommGroup.toUniformSpace
  let : TopologicalSpace P.generated := q.toNormedAddCommGroup.toUniformSpace.toTopologicalSpace
  let : NormedVectorLattice P.generated :=
    { toVectorLattice := inferInstance
      solid := fun {z w} h ↦ hsolid z w h
      norm_smul := fun r z ↦ map_smul_eq_mul p r z }
  let j (i : I) : E i →ₗ[ℝ] P.generated :=
    (P.inclusion i).toLinearMap.codRestrict P.generated.toSubmodule
      (fun x ↦ VectorSublattice.subset_generated _ ⟨⟨i, x⟩, rfl⟩)
  let T (i : I) : E i →L[ℝ] UniformSpace.Completion P.generated :=
    UniformSpace.Completion.toComplₗᵢ.toContinuousLinearMap.comp
      ((j i).mkContinuous 1 (fun x ↦
        (hfactor i x (j i x) rfl).trans_eq (one_mul ‖x‖).symm))
  have hT (i : I) : IsVecLatHom (T i) :=
    (toCompletionVecLatHom.comp
      { j i with
        map_sup' := fun x y ↦ Subtype.ext ((P.inclusion_isVecLatHom i).map_sup' x y)
        map_inf' := fun x y ↦ Subtype.ext ((P.inclusion_isVecLatHom i).map_inf' x y) }).isVecLatHom
  have hbound (i : I) : ‖T i‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x ↦
      (UniformSpace.Completion.norm_coe (j i x)).trans_le
        ((hfactor i x (j i x) rfl).trans_eq (one_mul ‖x‖).symm))
  obtain ⟨R, ⟨hR, hRT, hRnorm⟩, _⟩ :=
    P.exists_unique_extension (UniformSpace.Completion P.generated) T hT 1 zero_le_one hbound
  intro z
  obtain ⟨n, i, x, e, he⟩ := P.exists_expression z
  let a : Fin n → P.generated := fun k ↦ j (i k) (x k)
  have ha : LLexpr.eval a e = z :=
    Subtype.ext ((LLexpr.coe_eval_vectorSublattice P.generated a e).trans he.symm)
  have hRz : R (z : P.Carrier) = (z : UniformSpace.Completion P.generated) :=
    (congrArg R he).trans ((P.extension_eval T R hR hRT i x e).trans
      ((LLexpr.map_eval toCompletionVecLatHom a e).symm.trans
        (congrArg (fun b : P.generated ↦ (b : UniformSpace.Completion P.generated)) ha)))
  exact (UniformSpace.Completion.norm_coe z).symm.trans_le
    ((congrArg norm hRz).symm.trans_le
      ((R.le_of_opNorm_le hRnorm (z : P.Carrier)).trans_eq (one_mul ‖(z : P.Carrier)‖)))


end FreeProduct

section Associativity

variable {J : I → Type v} (F : ∀ i, J i → Type u)
  [∀ i j, NormedAddCommGroup (F i j)] [∀ i j, Lattice (F i j)]
  [∀ i j, IsOrderedAddMonoid (F i j)] [∀ i j, BanachLattice (F i j)]

/-- An iterated free product extends a uniformly bounded family indexed by all inner factors,
proving compatibility with grouping factors. -/
private lemma sigma_extension
    (P : ∀ i, FreeProduct (F i)) (Q : FreeProduct (fun i ↦ (P i).Carrier))
    {Y : Type w} [NormedAddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] [BanachLattice Y]
    (T : ∀ ij : Σ i, J i, F ij.1 ij.2 →L[ℝ] Y) (hT : ∀ ij, IsVecLatHom (T ij))
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ ij, ‖T ij‖ ≤ M) :
    ∃! S : Q.Carrier →L[ℝ] Y,
      IsVecLatHom S ∧
      (∀ i j x, S (Q.inclusion i ((P i).inclusion j x)) = T ⟨i, j⟩ x) ∧ ‖S‖ ≤ M := by
  classical
  choose R hR hRT hRnorm using fun i ↦
    ((P i).exists_unique_extension Y (fun j ↦ T ⟨i, j⟩)
      (fun j ↦ hT ⟨i, j⟩) M hM (fun j ↦ hbound ⟨i, j⟩)).exists
  obtain ⟨S, ⟨hS, hSR, hSnorm⟩, _⟩ := Q.exists_unique_extension Y R hR M hM hRnorm
  refine ⟨S, ⟨hS, fun i j x ↦ (hSR i ((P i).inclusion j x)).trans (hRT i j x), hSnorm⟩, ?_⟩
  rintro U ⟨hU, hUT, _⟩
  have hcomp (i : I) : U.comp (Q.inclusion i) = R i :=
    (P i).extension_ext
      ((hU.mk' U).comp ((Q.inclusion_isVecLatHom i).mk' (Q.inclusion i))).isVecLatHom
      (hR i) (fun j x ↦ (hUT i j x).trans (hRT i j x).symm)
  exact Q.extension_ext hU hS
    (fun i x ↦ (DFunLike.congr_fun (hcomp i) x).trans (hSR i x).symm)

/-- Taking free products in groups gives the free product of the entire family. -/
theorem nonempty_freeProduct_equiv_sigma
    (P : ∀ i, FreeProduct (F i))
    (Q : FreeProduct (fun i ↦ (P i).Carrier))
    (R : FreeProduct (fun ij : Σ i, J i ↦ F ij.1 ij.2)) :
    Nonempty (BanachLatEquiv Q.Carrier R.Carrier) := by
  let S : FreeProduct (fun ij : Σ i, J i ↦ F ij.1 ij.2) :=
    { Carrier := Q.Carrier
      inclusion := fun ij ↦ (Q.inclusion ij.1).comp ((P ij.1).inclusion ij.2)
      inclusion_isVecLatHom := fun ij ↦
        (((Q.inclusion_isVecLatHom ij.1).mk' (Q.inclusion ij.1)).comp
          (((P ij.1).inclusion_isVecLatHom ij.2).mk'
            ((P ij.1).inclusion ij.2))).isVecLatHom
      inclusion_contractive := fun ij ↦
        (FreeProduct.norm_comp_inclusion_le (P ij.1) (Q.inclusion ij.1) ij.2).trans
          (Q.inclusion_contractive ij.1)
      universal := fun Y _ _ _ _ T hT M hM hbound ↦ by
        simpa only [Sigma.forall, ContinuousLinearMap.comp_apply] using
          sigma_extension F P Q T hT M hM hbound }
  exact ⟨(S.exists_unique_equiv R).choose⟩

end Associativity

end BanachLattice
