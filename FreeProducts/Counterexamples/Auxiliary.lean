/-
Authors: Gonzalo Martínez-Fernández
-/

import FreeProducts.VectorLattice.Amalgamation

/-!
# Shared tools for counterexamples

Continuity of concrete free-lattice functions and injectivity of the right pushout map
provide common tools for the examples. Products with the real line carry their
coordinatewise vector lattice structure.
-/

noncomputable section

universe u

namespace VectorLattice.Counterexamples

/-- The product of a vector lattice with the real line carries the coordinatewise vector
lattice structure. -/
private instance prodRealVectorLattice (X : Type u) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] : VectorLattice (X × ℝ) where

/-- The right canonical map of a vector lattice pushout is injective when the opposite input
map is injective. -/
lemma pushout_right_injective
    {X Y A : Type u}
    [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X]
    [AddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [VectorLattice Y]
    [AddCommGroup A] [Lattice A] [IsOrderedAddMonoid A] [VectorLattice A]
    {f : VecLatHom A X} {g : VecLatHom A Y} (P : Pushout f g)
    (hf : Function.Injective f) : Function.Injective P.right := by
  let Q : Pushout g f :=
    { Carrier := P.Carrier
      left := P.right
      right := P.left
      comm := P.comm.symm
      universal := by
        intro W _ _ _ _ a b h
        obtain ⟨R, hR, huniq⟩ := P.universal W b a h.symm
        exact ⟨R, hR.symm, fun S hS ↦ huniq S hS.symm⟩ }
  exact Q.left_injective hf

/-- A concrete free vector lattice function is continuous. -/
lemma fvl_continuous {α : Type*} (f : FVL α) : Continuous f := by
  let C : VectorSublattice (FVL.FunctionSpace α) :=
    { carrier := {g | Continuous g}
      zero_mem' := continuous_const
      add_mem' := fun hg hh ↦ hg.add hh
      smul_mem' := fun r _ hg ↦ hg.const_smul r
      sup_mem' := fun hg hh ↦ hg.max hh }
  exact VectorSublattice.generated_le (s := Set.range (FVL.coordinate : α → _)) (Y := C)
    (fun _ ⟨a, ha⟩ ↦ ha ▸ continuous_apply a) f.property

end VectorLattice.Counterexamples
