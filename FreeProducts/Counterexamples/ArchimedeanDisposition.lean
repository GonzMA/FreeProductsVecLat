/-
Authors: Gonzalo Martínez-Fernández
-/

import FreeProducts.Counterexamples.CountableSpectrumPushout
import Mathlib.Algebra.Module.ULift

/-!
# Failure of universal disposition in Archimedean targets

No Archimedean vector lattice has universal disposition even when the ambient lattices
in the extension problem are Archimedean with countable prime spectra. The obstruction
comes from the incompatible sequence-lattice amalgam.
-/

noncomputable section

universe u

namespace VectorLattice.Counterexamples

open VectorLattice.CountableSpectra

/-- Changing the type universe preserves the order-compatible additive structure. -/
private instance liftedOrderedAddMonoid {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] : IsOrderedAddMonoid (ULift.{u} X) where
  add_le_add_left a b hab c :=
    show a.down + c.down ≤ b.down + c.down from
      IsOrderedAddMonoid.add_le_add_left a.down b.down hab c.down

/-- Changing the type universe preserves the vector lattice structure. -/
private instance liftedVectorLattice {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] : VectorLattice (ULift.{u} X) where
  smul_le_smul_of_nonneg_left := fun {r} hr {a b} hab ↦
    show r • a.down ≤ r • b.down from smul_le_smul_of_nonneg_left hab hr

/-- Identifies a universe-lifted vector lattice with its original lattice. -/
private def liftedEquiv (X : Type*) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] : VecLatEquiv (ULift.{u} X) X :=
  { ULift.moduleEquiv with
    map_sup' := fun _ _ ↦ rfl
    map_inf' := fun _ _ ↦ rfl }

/-- The Archimedean property is preserved under a change of type universe. -/
private instance liftedArchimedean {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] [IsVLArchimedean X] :
    IsVLArchimedean (ULift.{u} X) where
  le_zero_of_forall_nsmul_le := fun {x y} h ↦ show x.down ≤ 0 from
    IsVLArchimedean.le_zero_of_forall_nsmul_le (y := y.down) h

/-- Every vector sublattice of real sequences with pointwise order is Archimedean. -/
private instance sequenceSublatticeArchimedean (S : VectorSublattice (ℕ → ℝ)) :
    IsVLArchimedean S :=
  ⟨fun {_ _} h k ↦ IsVLArchimedean.le_zero_of_forall_nsmul_le (fun n ↦ h n k)⟩

/-- The product of the eventually constant lattice with the real line is Archimedean. -/
private instance eventuallyConstantProdArchimedean :
    IsVLArchimedean (eventuallyConstant × ℝ) :=
  ⟨fun {_ _} h ↦
    ⟨IsVLArchimedean.le_zero_of_forall_nsmul_le (fun n ↦ (h n).1),
      IsVLArchimedean.le_zero_of_forall_nsmul_le (fun n ↦ (h n).2)⟩⟩

/-- The eventually constant sublattice inside the universe-lifted eventually affine lattice. -/
private def liftedConstantSublattice : VectorSublattice (ULift.{u} eventuallyAffine) where
  toSubmodule := eventuallyConstant.toSubmodule.comap
    (eventuallyAffine.subtype.toLinearMap.comp (liftedEquiv _).toLinearEquiv.toLinearMap)
  sup_mem' := fun hx hy ↦ eventuallyConstant.sup_mem hx hy

/-- Identifies the lifted eventually constant sublattice with the original eventually constant
lattice. -/
private def liftedConstantEquiv : VecLatEquiv liftedConstantSublattice.{u} eventuallyConstant where
  toFun x := ⟨x.val.down.val, x.property⟩
  invFun x := ⟨ULift.up (VectorSublattice.inclusion
    eventuallyConstant_le_eventuallyAffine x), x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

/-- No Archimedean lattice has universal disposition even for Archimedean
ambient lattices with countable prime spectra. -/
theorem archimedean_not_universalDisposition
    (Z : Type u) [AddCommGroup Z] [Lattice Z] [IsOrderedAddMonoid Z]
    [VectorLattice Z] [IsVLArchimedean Z] :
    ¬ (∀ (B : Type u) [AddCommGroup B] [Lattice B] [IsOrderedAddMonoid B]
        [VectorLattice B] [IsVLArchimedean B], (properPrimeIdeals B).Countable →
          ∀ (A : VectorSublattice B) (T : VecLatHom A Z), Function.Injective T →
            ∃ S : VecLatHom B Z, Function.Injective S ∧ ∀ a, S a.val = T a) := by
  intro h
  obtain ⟨j, hj⟩ := embedding_of_extension_from_bot
    (h (ULift.{u} (eventuallyConstant × ℝ))
      (countable_spectrum_of_equiv (liftedEquiv _) sequence_lattices_countable_spectrum.2.2.1) ⊥)
  obtain ⟨g, hg, hgi, -⟩ := exists_countable_spectrum_nonarchimedean_pushout
  let j₀ := j.comp (liftedEquiv _).symm.toVecLatHom
  have hj₀ : Function.Injective j₀ := hj.comp (liftedEquiv _).toLinearEquiv.symm.injective
  obtain ⟨S, -, hS⟩ := h (ULift.{u} eventuallyAffine)
    (countable_spectrum_of_equiv (liftedEquiv _) sequence_lattices_countable_spectrum.2.1)
    liftedConstantSublattice ((j₀.comp g).comp liftedConstantEquiv.toVecLatHom)
    ((hj₀.comp hgi).comp liftedConstantEquiv.toLinearEquiv.injective)
  exact affine_amalgam_not_injective Z (S.comp (liftedEquiv _).symm.toVecLatHom) j₀
    (fun a ↦ (hS (liftedConstantEquiv.symm a)).trans (congrArg j₀ (hg a))) hj₀

end VectorLattice.Counterexamples
