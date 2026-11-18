/-
Authors: Gonzalo Martínez-Fernández
-/

import FreeProducts.AVLvsVL.Classical.ConeRepresentation
import Mathlib.CategoryTheory.Equivalence

/-!
# Contravariant duality for closed cones

Cone maps act by pullback on restriction lattices. This gives a dual equivalence
with finitely generated Archimedean vector lattices.
-/

universe u

namespace VectorLattice.ConeRepresentation

/-- A cone map whose coordinates extend to ambient free vector lattice functions. -/
structure ConeMap {m n : ℕ} (C : ClosedCone m) (D : ClosedCone n) where
  toFun : C.carrier → D.carrier
  coordinate_mem :
    ∀ i : Fin n, (fun x : C.carrier ↦ (toFun x).val i) ∈ restrictionSublattice C

/-- Composing a restriction-lattice function with a cone map gives another restriction-lattice
function. -/
private lemma restriction_comp_mem {m n : ℕ} {C : ClosedCone m} {D : ClosedCone n}
    (q : ConeMap C D) (f : ConeFunctions D) :
    (fun x ↦ f.val (q.toFun x)) ∈ restrictionSublattice C := by
  obtain ⟨g, hg⟩ := f.property
  choose a ha using q.coordinate_mem
  refine ⟨FVL.lift a g, ?_⟩
  intro x
  rw [free_substitution_apply]
  exact (hg (q.toFun x)).trans (congrArg g (funext (fun i ↦ ha i x)))

/-- Pullback along a cone map is a vector lattice homomorphism. -/
noncomputable def pullback {m n : ℕ} {C : ClosedCone m} {D : ClosedCone n}
    (q : ConeMap C D) : VecLatHom (ConeFunctions D) (ConeFunctions C) where
  toFun f := ⟨fun x ↦ f.val (q.toFun x), restriction_comp_mem q f⟩
  map_add' := by exact fun _ _ ↦ Subtype.ext rfl
  map_smul' := by exact fun _ _ ↦ Subtype.ext rfl
  map_sup' := by exact fun _ _ ↦ Subtype.ext rfl
  map_inf' := by exact fun _ _ ↦ Subtype.ext rfl

/-- Every vector lattice homomorphism between restriction lattices is pullback
along a unique cone map, in the opposite direction. -/
theorem exists_unique_pullback {m n : ℕ} (C : ClosedCone m) (D : ClosedCone n)
    (T : VecLatHom (ConeFunctions D) (ConeFunctions C)) :
    ∃! q : ConeMap C D, pullback q = T := by
  classical
  let ev (x : C.carrier) : VecLatHom (ConeFunctions C) ℝ :=
    { toFun := fun f ↦ f.val x
      map_add' := by exact fun _ _ ↦ rfl
      map_smul' := by exact fun _ _ ↦ rfl
      map_sup' := by exact fun _ _ ↦ rfl
      map_inf' := by exact fun _ _ ↦ rfl }
  choose q hq using fun x : C.carrier ↦ exists_evaluation D ((ev x).comp T)
  have hcoord (i : Fin n) : (fun x : C.carrier ↦ (q x).val i) = (T (coordinate D i)).val := by
    funext x
    exact (hq x (coordinate D i)).symm
  let Q : ConeMap C D := ⟨q, fun i ↦ hcoord i ▸ (T (coordinate D i)).property⟩
  refine ⟨Q, ?_, ?_⟩
  · apply DFunLike.ext
    exact fun f ↦ Subtype.ext (funext (fun x ↦ (hq x f).symm))
  · intro R hR
    have heq : R.toFun = Q.toFun := by
      funext x
      apply Subtype.ext
      funext i
      have h := congrArg (fun S : VecLatHom (ConeFunctions D) (ConeFunctions C) ↦
        (S (coordinate D i)).val x) hR
      exact h.trans (hq x (coordinate D i))
    cases R
    congr 1

end VectorLattice.ConeRepresentation

noncomputable section

open CategoryTheory

namespace VectorLattice.ConeRepresentation

/-- A closed cone in a finite-dimensional real coordinate space. -/
structure BundledCone where
  dim : ℕ
  cone : ClosedCone dim

/-- Closed cones with maps whose coordinates belong to the restriction lattice. -/
instance : Category BundledCone where
  Hom C D := ConeMap C.cone D.cone
  id C := ⟨id, fun i ↦ (coordinate C.cone i).property⟩
  comp f g := ⟨g.toFun ∘ f.toFun, fun i ↦
    (pullback f ⟨fun x ↦ (g.toFun x).val i, g.coordinate_mem i⟩).property⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- A finitely generated Archimedean real vector lattice. -/
structure FinitelyGeneratedArchimedeanLattice where
  Carrier : Type
  [addCommGroup : AddCommGroup Carrier]
  [lattice : Lattice Carrier]
  [isOrderedAddMonoid : IsOrderedAddMonoid Carrier]
  [vectorLattice : VectorLattice Carrier]
  [archimedean : IsVLArchimedean Carrier]
  finite_generation : IsFinitelyGenerated Carrier

attribute [instance] FinitelyGeneratedArchimedeanLattice.addCommGroup
  FinitelyGeneratedArchimedeanLattice.lattice
  FinitelyGeneratedArchimedeanLattice.isOrderedAddMonoid
  FinitelyGeneratedArchimedeanLattice.vectorLattice
  FinitelyGeneratedArchimedeanLattice.archimedean

/-- Finitely generated Archimedean lattices with all vector lattice homomorphisms. -/
instance : Category FinitelyGeneratedArchimedeanLattice where
  Hom X Y := VecLatHom X.Carrier Y.Carrier
  id _ := VecLatHom.id
  comp f g := g.comp f
  id_comp _ := DFunLike.ext _ _ (fun _ ↦ rfl)
  comp_id _ := DFunLike.ext _ _ (fun _ ↦ rfl)
  assoc _ _ _ := DFunLike.ext _ _ (fun _ ↦ rfl)

/-- Restriction lattices on objects and pullback on morphisms form a contravariant functor. -/
def coneFunctionsFunctor : BundledConeᵒᵖ ⥤ FinitelyGeneratedArchimedeanLattice where
  obj C :=
    { Carrier := ConeFunctions C.unop.cone
      finite_generation := ⟨C.unop.dim, coordinate C.unop.cone,
        generated_range_coordinate C.unop.cone⟩ }
  map f := pullback f.unop
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Every finitely generated Archimedean lattice is isomorphic to a cone restriction lattice. -/
instance : coneFunctionsFunctor.EssSurj where
  mem_essImage X := by
    obtain ⟨n, g, hg⟩ := X.finite_generation
    obtain ⟨C, e, -⟩ := exists_cone_representation X.Carrier g hg
    exact ⟨Opposite.op ⟨n, C⟩, ⟨
      { hom := e.symm.toVecLatHom
        inv := e.toVecLatHom
        hom_inv_id := show e.toVecLatHom.comp e.symm.toVecLatHom = VecLatHom.id from
          DFunLike.ext _ _ (fun x ↦ e.toLinearEquiv.apply_symm_apply x)
        inv_hom_id := show e.symm.toVecLatHom.comp e.toVecLatHom = VecLatHom.id from
          DFunLike.ext _ _ (fun x ↦ e.toLinearEquiv.symm_apply_apply x) }⟩⟩

/-- Every homomorphism between cone restriction lattices is a pullback. -/
instance : coneFunctionsFunctor.Full where
  map_surjective {X Y} T := by
    obtain ⟨q, hq, -⟩ := exists_unique_pullback Y.unop.cone X.unop.cone T
    exact ⟨(show Y.unop ⟶ X.unop from q).op, hq⟩

/-- A cone map is determined by its pullback homomorphism. -/
instance : coneFunctionsFunctor.Faithful where
  map_injective {X Y} f _ h := Quiver.Hom.unop_inj
    ((exists_unique_pullback Y.unop.cone X.unop.cone (pullback f.unop)).unique rfl h.symm)

/-- Restriction lattices give an equivalence from the opposite category of closed cones. -/
instance : coneFunctionsFunctor.IsEquivalence where

/-- Closed cones and finitely generated Archimedean real vector lattices are dual categories. -/
def coneDuality : BundledConeᵒᵖ ≌ FinitelyGeneratedArchimedeanLattice :=
  coneFunctionsFunctor.asEquivalence

end VectorLattice.ConeRepresentation
