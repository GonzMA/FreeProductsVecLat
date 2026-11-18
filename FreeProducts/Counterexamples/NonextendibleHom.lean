/-
Authors: Gonzalo Martínez-Fernández
-/

import FreeProducts.Counterexamples.SequenceLattices

/-!
# A homomorphism with no Archimedean extension

A positive multiple of the eventual-value homomorphism cannot extend from eventually
constant sequences to eventually affine sequences in a nonzero Archimedean target.
Both domain lattices are Archimedean and have countable proper prime spectra.
-/

noncomputable section

universe u

namespace VectorLattice.Counterexamples

open VectorLattice.CountableSpectra

/-- Extending a scalar multiple of the eventual-value map to eventually affine sequences
forces all natural multiples of that vector to be bounded above. -/
private lemma affine_extension_bounded
    (Z : Type u) [AddCommGroup Z] [Lattice Z] [IsOrderedAddMonoid Z]
    [VectorLattice Z] (z : Z) (S : VecLatHom eventuallyAffine Z)
    (hS : ∀ a : eventuallyConstant,
      S (VectorSublattice.inclusion eventuallyConstant_le_eventuallyAffine a) =
        eventualValue a • z) :
    ∃ y : Z, ∀ n : ℕ, n • z ≤ y := by
  let b : eventuallyAffine := ⟨fun k ↦ (k : ℝ),
    0, 1, 0, fun k _ ↦ ((zero_add _).trans (one_mul (k : ℝ))).symm⟩
  refine ⟨S b, fun n ↦ ?_⟩
  let a : eventuallyConstant := ⟨fun k ↦ min (k : ℝ) (n : ℝ),
    ⟨(n : ℝ), n, fun k hk ↦ min_eq_right (Nat.cast_le.mpr hk)⟩⟩
  have ha : eventualValue a = (n : ℝ) := eventualValue_eq_of_eventually_constant a
    (N := n) (fun k hk ↦ min_eq_right (Nat.cast_le.mpr hk))
  simpa only [hS a, ha, Nat.cast_smul_eq_nsmul] using
    S.monotone (show VectorSublattice.inclusion eventuallyConstant_le_eventuallyAffine a ≤ b
      from fun k ↦ min_le_left _ _)

/-- Nonzero Archimedean targets admit homomorphisms that do not extend,
even when both domain lattices are Archimedean with countable spectra. -/
theorem archimedean_nonextendible_hom
    (Z : Type u) [AddCommGroup Z] [Lattice Z] [IsOrderedAddMonoid Z]
    [VectorLattice Z] [IsVLArchimedean Z] (z : Z) (hz : 0 < z) :
    ∃ T : VecLatHom eventuallyConstant Z,
      (∀ a, T a = eventualValue a • z) ∧
      ¬ ∃ S : VecLatHom eventuallyAffine Z,
        S.comp (VectorSublattice.inclusion eventuallyConstant_le_eventuallyAffine) = T := by
  let T : VecLatHom eventuallyConstant Z :=
    { toLinearMap := eventualValue.toLinearMap.smulRight z
      map_sup' := fun a b ↦ (congrArg (· • z) (map_sup eventualValue a b)).trans
        (sup_smul_nonneg z _ _ hz.le)
      map_inf' := fun a b ↦ (congrArg (· • z) (map_inf eventualValue a b)).trans
        (inf_smul_nonneg z _ _ hz.le) }
  refine ⟨T, fun _ ↦ rfl, ?_⟩
  rintro ⟨S, hS⟩
  obtain ⟨y, hy⟩ := affine_extension_bounded Z z S (fun a ↦ DFunLike.congr_fun hS a)
  exact hz.ne' (IsVLArchimedean.eq_zero_of_nonneg_of_forall_nsmul_le hz.le hy)

end VectorLattice.Counterexamples
