/-
Authors: Gonzalo Martínez-Fernández
-/

import BanLat.Free.FVL
import BanLat.Quotient
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Order.Monoid.Prod

/-!
# Free products of vector lattices

Universal properties and existence of free products and pushouts in vector lattices,
uniqueness of free products, injectivity of their factor inclusions, and compatibility
with quotients.
-/

open scoped DirectSum

universe u

namespace VectorLattice

/-- A linear map freely generates a vector lattice when every linear map
from its domain extends uniquely to a vector lattice homomorphism. -/
def IsFreeOver {V A : Type u} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup A] [Lattice A] [IsOrderedAddMonoid A] [VectorLattice A]
    (j : V →ₗ[ℝ] A) : Prop :=
  ∀ (Y : Type u) [AddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] [VectorLattice Y] (T : V →ₗ[ℝ] Y),
    ∃! S : VecLatHom A Y, ∀ x, S (j x) = T x

section FreeProducts

variable {I : Type u} (E : I → Type u)
  [∀ i, AddCommGroup (E i)] [∀ i, Lattice (E i)]
  [∀ i, IsOrderedAddMonoid (E i)] [∀ i, VectorLattice (E i)]

/-- A free product extends every family of vector lattice homomorphisms
uniquely through its canonical maps. -/
structure FreeProduct where
  Carrier : Type u
  [addCommGroup : AddCommGroup Carrier]
  [lattice : Lattice Carrier]
  [isOrderedAddMonoid : IsOrderedAddMonoid Carrier]
  [vectorLattice : VectorLattice Carrier]
  inclusion : ∀ i, VecLatHom (E i) Carrier
  universal :
    ∀ (Y : Type u) [AddCommGroup Y] [Lattice Y]
      [IsOrderedAddMonoid Y] [VectorLattice Y]
      (T : ∀ i, VecLatHom (E i) Y),
      ∃! S : VecLatHom Carrier Y,
        ∀ i x, S (inclusion i x) = T i x

attribute [instance] FreeProduct.addCommGroup FreeProduct.lattice
  FreeProduct.isOrderedAddMonoid FreeProduct.vectorLattice

/-- A quotient of the free lattice has the required extension property whenever its relations
are killed by every compatible family of factor maps. -/
private lemma freeProduct_quotient_universal (J : OrderIdeal (FVL (Sigma E)))
    (j : ∀ i, VecLatHom (E i) (FVL (Sigma E) ⧸ J.toSubmodule))
    (hj : ∀ i x, j i x = J.mkQ (FVL.of ⟨i, x⟩))
    {Y : Type u} [AddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] [VectorLattice Y] (T : ∀ i, VecLatHom (E i) Y)
    (hker : J.toSubmodule ≤
      LinearMap.ker (FVL.lift (fun z : Sigma E ↦ T z.1 z.2)).toLinearMap) :
    ∃! S : VecLatHom (FVL (Sigma E) ⧸ J.toSubmodule) Y,
      ∀ i x, S (j i x) = T i x := by
  refine ⟨J.liftQVecLatHom (FVL.lift (fun z : Sigma E ↦ T z.1 z.2)) hker, ?_, ?_⟩
  case refine_1 =>
    exact fun i x ↦ (congrArg
      (J.liftQVecLatHom (FVL.lift (fun z : Sigma E ↦ T z.1 z.2)) hker) (hj i x)).trans
        (FVL.lift_of (fun z : Sigma E ↦ T z.1 z.2) ⟨i, x⟩)
  intro S hS
  have hcomp : S.comp J.mkQVecLatHom = FVL.lift (fun z : Sigma E ↦ T z.1 z.2) :=
    FVL.lift_unique _ _ (fun z ↦ (congrArg S (hj z.1 z.2).symm).trans (hS z.1 z.2))
  refine DFunLike.ext _ _ (fun z ↦ ?_)
  obtain ⟨x, rfl⟩ := J.toSubmodule.mkQ_surjective z
  exact DFunLike.congr_fun hcomp x

/-- Constructs relations enforcing addition, scalar multiplication, and absolute values within
each factor, and shows every factor homomorphism respects them. -/
private lemma exists_freeProduct_relations :
    ∃ J : OrderIdeal (FVL (Sigma E)),
      (∀ i (x y : E i), J.mkQ (FVL.of ⟨i, x + y⟩) =
        J.mkQ (FVL.of ⟨i, x⟩) + J.mkQ (FVL.of ⟨i, y⟩)) ∧
      (∀ i (r : ℝ) (x : E i), J.mkQ (FVL.of ⟨i, r • x⟩) =
        r • J.mkQ (FVL.of ⟨i, x⟩)) ∧
      (∀ i (x : E i), J.mkQ (FVL.of ⟨i, |x|⟩) = |J.mkQ (FVL.of ⟨i, x⟩)|) ∧
      ∀ (Y : Type u) [AddCommGroup Y] [Lattice Y]
        [IsOrderedAddMonoid Y] [VectorLattice Y] (T : ∀ i, VecLatHom (E i) Y),
        J.toSubmodule ≤ LinearMap.ker
          (FVL.lift (fun z : Sigma E ↦ T z.1 z.2)).toLinearMap := by
  let s : Set (FVL (Sigma E)) := {z |
    (∃ (i : I) (x y : E i),
      z = FVL.of ⟨i, x + y⟩ - (FVL.of ⟨i, x⟩ + FVL.of ⟨i, y⟩)) ∨
    (∃ (i : I) (r : ℝ) (x : E i), z = FVL.of ⟨i, r • x⟩ - r • FVL.of ⟨i, x⟩) ∨
    (∃ (i : I) (x : E i), z = FVL.of ⟨i, |x|⟩ - |FVL.of ⟨i, x⟩|)}
  let J := OrderIdeal.generated s
  refine ⟨J, ?_, ?_, ?_, ?_⟩
  case refine_1 =>
    exact fun i x y ↦ ((Submodule.Quotient.eq J.toSubmodule).mpr
      (OrderIdeal.subset_generated s (Or.inl ⟨i, x, y, rfl⟩))).trans
        (map_add J.mkQ (FVL.of (⟨i, x⟩ : Sigma E)) (FVL.of (⟨i, y⟩ : Sigma E)))
  case refine_2 =>
    exact fun i r x ↦ ((Submodule.Quotient.eq J.toSubmodule).mpr
      (OrderIdeal.subset_generated s (Or.inr (Or.inl ⟨i, r, x, rfl⟩)))).trans
        (map_smul J.mkQ r (FVL.of (⟨i, x⟩ : Sigma E)))
  case refine_3 =>
    exact fun i x ↦ ((Submodule.Quotient.eq J.toSubmodule).mpr
      (OrderIdeal.subset_generated s (Or.inr (Or.inr ⟨i, x, rfl⟩)))).trans
        (J.mkQ_abs (FVL.of (⟨i, x⟩ : Sigma E)))
  intro Y _ _ _ _ T
  refine OrderIdeal.generated_le (J := OrderIdeal.ofKerVecLatHom
    (FVL.lift (fun z : Sigma E ↦ T z.1 z.2))) ?_
  rintro z (⟨i, x, y, rfl⟩ | ⟨i, r, x, rfl⟩ | ⟨i, x, rfl⟩)
  all_goals change (FVL.lift (fun z : Sigma E ↦ T z.1 z.2)) _ = 0
  all_goals simp [map_sub, map_add, map_smul, VecLatHom.map_abs]

/-- Every family of vector lattices has a free product. -/
theorem nonempty_freeProduct : Nonempty (FreeProduct E) := by
  obtain ⟨J, hadd, hsmul, habs, hker⟩ := exists_freeProduct_relations E
  let j : ∀ i, VecLatHom (E i) (FVL (Sigma E) ⧸ J.toSubmodule) := fun i ↦
    VecLatHom.ofAbs
      { toFun := fun x ↦ J.mkQ (FVL.of ⟨i, x⟩)
        map_add' := hadd i
        map_smul' := hsmul i } (habs i)
  exact ⟨{ Carrier := FVL (Sigma E) ⧸ J.toSubmodule
           inclusion := j
           universal := fun Y _ _ _ _ T ↦
             freeProduct_quotient_universal E J j (fun _ _ ↦ rfl) T (hker Y T) }⟩

namespace FreeProduct

variable {E} (P Q : FreeProduct E)

/-- Two homomorphisms from a free product agree if they agree on every factor inclusion. -/
lemma hom_ext {W : Type u} [AddCommGroup W] [Lattice W]
    [IsOrderedAddMonoid W] [VectorLattice W] {S T : VecLatHom P.Carrier W}
    (h : ∀ i x, S (P.inclusion i x) = T (P.inclusion i x)) : S = T := by
  obtain ⟨R, _, hu⟩ := P.universal W (fun i ↦ S.comp (P.inclusion i))
  exact (hu S (fun _ _ ↦ rfl)).trans (hu T (fun i x ↦ (h i x).symm)).symm

/-- Maps between two free products that preserve the factor inclusions compose to the
identity. -/
private lemma comp_eq_id (f : VecLatHom P.Carrier Q.Carrier)
    (g : VecLatHom Q.Carrier P.Carrier)
    (hf : ∀ i x, f (P.inclusion i x) = Q.inclusion i x)
    (hg : ∀ i x, g (Q.inclusion i x) = P.inclusion i x) :
    g.comp f = VecLatHom.id := by
  exact hom_ext P (fun i x ↦ (congrArg g (hf i x)).trans (hg i x))

/-- Free products are uniquely isomorphic by an isomorphism commuting
with the canonical maps. -/
theorem exists_unique_equiv :
    ∃! e : VecLatEquiv P.Carrier Q.Carrier,
      ∀ i x, e (P.inclusion i x) = Q.inclusion i x := by
  obtain ⟨f, hf, _⟩ := P.universal Q.Carrier Q.inclusion
  obtain ⟨g, hg, _⟩ := Q.universal P.Carrier P.inclusion
  let e : VecLatEquiv P.Carrier Q.Carrier :=
    { f.toLinearMap with
      invFun := g
      left_inv := DFunLike.congr_fun (comp_eq_id P Q f g hf hg)
      right_inv := DFunLike.congr_fun (comp_eq_id Q P g f hg hf)
      map_sup' := f.map_sup'
      map_inf' := f.map_inf' }
  refine ⟨e, hf, fun e' he' ↦ DFunLike.ext _ _ ?_⟩
  exact fun x ↦ DFunLike.congr_fun (hom_ext P (S := e'.toVecLatHom) (T := f)
    (fun i x ↦ (he' i x).trans (hf i x).symm)) x

/-- Every canonical map into a free product is injective. -/
theorem inclusion_injective (i : I) :
    Function.Injective (P.inclusion i) := by
  classical
  let T : ∀ j, VecLatHom (E j) (E i) := Function.update
    (fun j ↦ VecLatHom.ofAbs (0 : E j →ₗ[ℝ] E i) (by simp)) i VecLatHom.id
  obtain ⟨R, hR, _⟩ := P.universal (E i) T
  have hRi : T i = VecLatHom.id := Function.update_self _ _ _
  exact (show Function.LeftInverse R (P.inclusion i) from fun x ↦
    (hR i x).trans ((DFunLike.congr_fun hRi x).trans rfl)).injective

/-- A free product of freely generated vector lattices is freely generated
by the algebraic direct sum of their generating vector spaces. -/
theorem isFreeOver_directSum [DecidableEq I]
    (V : I → Type u) [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℝ (V i)]
    (j : ∀ i, V i →ₗ[ℝ] E i) (hj : ∀ i, IsFreeOver (j i)) :
    IsFreeOver (DirectSum.toModule ℝ I P.Carrier
      (fun i ↦ (P.inclusion i).toLinearMap.comp (j i))) := by
  intro Y _ _ _ _ T
  choose S hS huS using fun i ↦ hj i Y (T.comp (DirectSum.lof ℝ I V i))
  obtain ⟨R, hR, _⟩ := P.universal Y S
  refine ⟨R, ?_, ?_⟩
  case refine_2 =>
    intro R' hR'
    refine hom_ext P (fun i x ↦ (DFunLike.congr_fun
      (huS i (R'.comp (P.inclusion i)) (fun v ↦ ?_)) x).trans (hR i x).symm)
    change R' ((P.inclusion i).toLinearMap (j i v)) = T (DirectSum.lof ℝ I V i v)
    simpa only [DirectSum.toModule_lof, LinearMap.comp_apply] using
      hR' (DirectSum.lof ℝ I V i v)
  have h : R.toLinearMap.comp (DirectSum.toModule ℝ I P.Carrier
      (fun i ↦ (P.inclusion i).toLinearMap.comp (j i))) = T := by
    refine DirectSum.linearMap_ext ℝ (fun i ↦ LinearMap.ext (fun v ↦ ?_))
    simp only [LinearMap.comp_apply, DirectSum.toModule_lof]
    exact (hR i (j i v)).trans (hS i v)
  exact fun x ↦ DFunLike.congr_fun h x

/-- Quotienting by the ideal generated by the factor ideals kills each of those ideals on its
own factor. -/
private lemma quotient_factor_kernel (J : ∀ i, OrderIdeal (E i)) (i : I) :
    let K := OrderIdeal.generated (⋃ i, P.inclusion i '' (J i : Set (E i)))
    (J i).toSubmodule ≤ LinearMap.ker (K.mkQVecLatHom.comp (P.inclusion i)).toLinearMap := by
  dsimp only
  intro x hx
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (OrderIdeal.subset_generated _ (Set.mem_iUnion.mpr ⟨i, ⟨x, hx, rfl⟩⟩))

/-- A homomorphism vanishing on every factor ideal vanishes on the ideal they generate in the
free product. -/
private lemma generated_images_le_ker (J : ∀ i, OrderIdeal (E i))
    {W : Type u} [AddCommGroup W] [Lattice W] [IsOrderedAddMonoid W] [VectorLattice W]
    (U : VecLatHom P.Carrier W) (hU : ∀ i x, x ∈ J i → U (P.inclusion i x) = 0) :
    OrderIdeal.generated (⋃ i, P.inclusion i '' (J i : Set (E i))) ≤
      OrderIdeal.ofKerVecLatHom U := by
  exact OrderIdeal.generated_le (fun z hz ↦ (Set.mem_iUnion.mp hz).elim
    (fun i ⟨x, hx, hxz⟩ ↦ hxz ▸ hU i x hx))

/-- The quotient by the generated factor ideals has the universal property of the free product
of the factor quotients. -/
private lemma quotient_universal (J : ∀ i, OrderIdeal (E i))
    {W : Type u} [AddCommGroup W] [Lattice W] [IsOrderedAddMonoid W] [VectorLattice W]
    (T : ∀ i, VecLatHom (E i ⧸ (J i).toSubmodule) W) :
    let K := OrderIdeal.generated (⋃ i, P.inclusion i '' (J i : Set (E i)))
    let q := fun i ↦ (J i).liftQVecLatHom (K.mkQVecLatHom.comp (P.inclusion i))
      (quotient_factor_kernel P J i)
    ∃! R : VecLatHom (P.Carrier ⧸ K.toSubmodule) W,
      ∀ i x, R (q i x) = T i x := by
  intro K q
  obtain ⟨U, hU, _⟩ := P.universal W (fun i ↦ (T i).comp (J i).mkQVecLatHom)
  have hker : K.toSubmodule ≤ LinearMap.ker U.toLinearMap :=
    generated_images_le_ker P J U (fun i x hx ↦ (hU i x).trans
      ((congrArg (T i) ((Submodule.Quotient.mk_eq_zero (J i).toSubmodule).mpr hx)).trans
        (map_zero _)))
  refine ⟨K.liftQVecLatHom U hker, ?_, fun R hR ↦ ?_⟩
  case refine_2 =>
    have hcomp : R.comp K.mkQVecLatHom = U := hom_ext P
      (fun i x ↦ (hR i ((J i).mkQ x)).trans (hU i x).symm)
    refine DFunLike.ext _ _ (fun z ↦ ?_)
    obtain ⟨x, rfl⟩ := K.toSubmodule.mkQ_surjective z
    exact DFunLike.congr_fun hcomp x
  intro i z
  obtain ⟨x, rfl⟩ := (J i).toSubmodule.mkQ_surjective z
  exact hU i x

/-- Taking the free product of ideal quotients agrees with quotienting
the free product by the ideal generated by the images of those ideals. -/
theorem exists_quotient_equiv (J : ∀ i, OrderIdeal (E i))
    (Q : FreeProduct (fun i ↦ E i ⧸ (J i).toSubmodule)) :
    let K : OrderIdeal P.Carrier :=
      OrderIdeal.generated (⋃ i, P.inclusion i '' (J i : Set (E i)))
    ∃ e : VecLatEquiv Q.Carrier (P.Carrier ⧸ K.toSubmodule),
      ∀ i x, e (Q.inclusion i ((J i).mkQ x)) =
        K.mkQ (P.inclusion i x) := by
  intro K
  let R : FreeProduct (fun i ↦ E i ⧸ (J i).toSubmodule) :=
    { Carrier := P.Carrier ⧸ K.toSubmodule
      inclusion := fun i ↦ (J i).liftQVecLatHom
        (K.mkQVecLatHom.comp (P.inclusion i)) (quotient_factor_kernel P J i)
      universal := fun W _ _ _ _ T ↦ quotient_universal P J T }
  obtain ⟨e, he, _⟩ := Q.exists_unique_equiv R
  exact ⟨e, fun i x ↦ he i ((J i).mkQ x)⟩

end FreeProduct

end FreeProducts

section Pushouts

variable {X Y Z : Type u}
  [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X]
  [AddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [VectorLattice Y]
  [AddCommGroup Z] [Lattice Z] [IsOrderedAddMonoid Z] [VectorLattice Z]

/-- A push-out is a universal commutative square of vector lattice
homomorphisms with a prescribed common domain. -/
structure Pushout (f : VecLatHom Z X) (g : VecLatHom Z Y) where
  Carrier : Type u
  [addCommGroup : AddCommGroup Carrier]
  [lattice : Lattice Carrier]
  [isOrderedAddMonoid : IsOrderedAddMonoid Carrier]
  [vectorLattice : VectorLattice Carrier]
  left : VecLatHom X Carrier
  right : VecLatHom Y Carrier
  comm : left.comp f = right.comp g
  universal :
    ∀ (W : Type u) [AddCommGroup W] [Lattice W]
      [IsOrderedAddMonoid W] [VectorLattice W]
      (a : VecLatHom X W) (b : VecLatHom Y W),
      a.comp f = b.comp g →
        ∃! R : VecLatHom Carrier W,
          R.comp left = a ∧ R.comp right = b

attribute [instance] Pushout.addCommGroup Pushout.lattice
  Pushout.isOrderedAddMonoid Pushout.vectorLattice

/-- The quotient by the ideal generated by the differences of two homomorphisms identifies
their values. -/
private lemma quotient_identifies {A : Type u} [AddCommGroup A] [Lattice A]
    [IsOrderedAddMonoid A] [VectorLattice A] (a b : VecLatHom Z A) :
    let J := OrderIdeal.generated (Set.range (fun z ↦ a z - b z))
    J.mkQVecLatHom.comp a = J.mkQVecLatHom.comp b := by
  intro J
  refine DFunLike.ext _ _ (fun z ↦ sub_eq_zero.mp ?_)
  change J.mkQ (a z) - J.mkQ (b z) = 0
  rw [← map_sub]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (OrderIdeal.subset_generated _ ⟨z, rfl⟩)

/-- A homomorphism equalizing two maps kills the ideal generated by their differences. -/
private lemma coequalizer_kernel {A W : Type u} [AddCommGroup A] [Lattice A]
    [IsOrderedAddMonoid A] [VectorLattice A] [AddCommGroup W] [Lattice W]
    [IsOrderedAddMonoid W] [VectorLattice W] (a b : VecLatHom Z A)
    (U : VecLatHom A W) (h : ∀ z, U (a z) = U (b z)) :
    OrderIdeal.generated (Set.range (fun z ↦ a z - b z)) ≤ OrderIdeal.ofKerVecLatHom U := by
  exact OrderIdeal.generated_le (fun z ⟨x, hxz⟩ ↦ hxz ▸
    (map_sub U (a x) (b x)).trans (sub_eq_zero.mpr (h x)))

section

variable {E : ULift.{u} Bool → Type u} [∀ i, AddCommGroup (E i)] [∀ i, Lattice (E i)]
  [∀ i, IsOrderedAddMonoid (E i)] [∀ i, VectorLattice (E i)] (P : FreeProduct E)

/-- The quotient identifying the common-domain images satisfies the universal property of the
pushout. -/
private lemma pushout_quotient_universal
    (f : VecLatHom Z (E ⟨false⟩)) (g : VecLatHom Z (E ⟨true⟩))
    {W : Type u} [AddCommGroup W] [Lattice W] [IsOrderedAddMonoid W] [VectorLattice W]
    (a : VecLatHom (E ⟨false⟩) W) (b : VecLatHom (E ⟨true⟩) W)
    (hab : a.comp f = b.comp g) :
    let J := OrderIdeal.generated (Set.range
      (fun z ↦ P.inclusion ⟨false⟩ (f z) - P.inclusion ⟨true⟩ (g z)))
    ∃! R : VecLatHom (P.Carrier ⧸ J.toSubmodule) W,
      R.comp (J.mkQVecLatHom.comp (P.inclusion ⟨false⟩)) = a ∧
        R.comp (J.mkQVecLatHom.comp (P.inclusion ⟨true⟩)) = b := by
  intro J
  let T : ∀ i, VecLatHom (E i) W := fun i ↦ match i with
    | ⟨false⟩ => a
    | ⟨true⟩ => b
  obtain ⟨U, hU, _⟩ := P.universal W T
  have hker : J.toSubmodule ≤ LinearMap.ker U.toLinearMap :=
    coequalizer_kernel ((P.inclusion ⟨false⟩).comp f) ((P.inclusion ⟨true⟩).comp g) U
      (fun z ↦ (hU ⟨false⟩ (f z)).trans
        ((DFunLike.congr_fun hab z).trans (hU ⟨true⟩ (g z)).symm))
  refine ⟨J.liftQVecLatHom U hker,
    ⟨DFunLike.ext _ _ (fun x ↦ hU ⟨false⟩ x),
      DFunLike.ext _ _ (fun x ↦ hU ⟨true⟩ x)⟩, fun R hR ↦ ?_⟩
  have hcomp : R.comp J.mkQVecLatHom = U := FreeProduct.hom_ext P (fun i ↦ match i with
    | ⟨false⟩ => fun x ↦ (DFunLike.congr_fun hR.1 x).trans (hU ⟨false⟩ x).symm
    | ⟨true⟩ => fun x ↦ (DFunLike.congr_fun hR.2 x).trans (hU ⟨true⟩ x).symm)
  refine DFunLike.ext _ _ (fun z ↦ ?_)
  obtain ⟨x, rfl⟩ := J.toSubmodule.mkQ_surjective z
  exact DFunLike.congr_fun hcomp x

/-- Constructs a pushout by quotienting the free product of the two target lattices. -/
private lemma nonempty_pushout_of_freeProduct (P : FreeProduct E)
    (f : VecLatHom Z (E ⟨false⟩)) (g : VecLatHom Z (E ⟨true⟩)) :
    Nonempty (Pushout f g) := by
  let J := OrderIdeal.generated (Set.range
    (fun z ↦ P.inclusion ⟨false⟩ (f z) - P.inclusion ⟨true⟩ (g z)))
  exact ⟨{ Carrier := P.Carrier ⧸ J.toSubmodule
           left := J.mkQVecLatHom.comp (P.inclusion ⟨false⟩)
           right := J.mkQVecLatHom.comp (P.inclusion ⟨true⟩)
           comm := quotient_identifies ((P.inclusion ⟨false⟩).comp f)
             ((P.inclusion ⟨true⟩).comp g)
           universal := fun W _ _ _ _ a b hab ↦
             pushout_quotient_universal P f g a b hab }⟩

end

/-- Every pair of vector lattice homomorphisms with a common domain
has a push-out. -/
theorem nonempty_pushout (f : VecLatHom Z X) (g : VecLatHom Z Y) :
    Nonempty (Pushout f g) := by
  let E : ULift.{u} Bool → Type u := fun i ↦ Bool.rec X Y i.down
  let addInst : ∀ i, AddCommGroup (E i) := fun
    | ⟨false⟩ => inferInstanceAs (AddCommGroup X)
    | ⟨true⟩ => inferInstanceAs (AddCommGroup Y)
  let latInst : ∀ i, Lattice (E i) := fun
    | ⟨false⟩ => inferInstanceAs (Lattice X)
    | ⟨true⟩ => inferInstanceAs (Lattice Y)
  let ordInst : ∀ i, @IsOrderedAddMonoid (E i) (addInst i).toAddCommMonoid
      (latInst i).toPartialOrder.toPreorder := fun
    | ⟨false⟩ => inferInstance
    | ⟨true⟩ => inferInstance
  let vecInst : ∀ i, @VectorLattice (E i) (addInst i) (latInst i) (ordInst i) := fun
    | ⟨false⟩ => inferInstance
    | ⟨true⟩ => inferInstance
  obtain ⟨P⟩ := @nonempty_freeProduct _ E addInst latInst ordInst vecInst
  exact @nonempty_pushout_of_freeProduct Z _ _ _ _ E addInst latInst ordInst vecInst P f g

end Pushouts

end VectorLattice
