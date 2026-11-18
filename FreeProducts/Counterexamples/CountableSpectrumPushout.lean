/-
Authors: Gonzalo Martínez-Fernández
-/

import FreeProducts.Counterexamples.SequenceLattices

/-!
# A non-Archimedean pushout from countable-spectrum lattices

Eventually affine sequences and eventually constant sequences with an extra real
coordinate give an injective amalgamation problem with countable prime spectra. Its
ordinary pushout is non-Archimedean, and its Archimedean quotient collapses a nonzero
vector in a canonical factor.
-/

noncomputable section

universe u

namespace VectorLattice.Counterexamples

open VectorLattice.CountableSpectra

/-- A compatible amalgam of the affine and augmented constant sequence lattices bounds all
multiples of the extra scalar coordinate. -/
private lemma affine_amalgam_bounded
    (Z : Type u) [AddCommGroup Z] [Lattice Z] [IsOrderedAddMonoid Z]
    [VectorLattice Z]
    (T₁ : VecLatHom eventuallyAffine Z) (T₂ : VecLatHom (eventuallyConstant × ℝ) Z)
    (hcomm : ∀ a : eventuallyConstant,
      T₁ (VectorSublattice.inclusion eventuallyConstant_le_eventuallyAffine a) =
        T₂ (a, eventualValue a)) :
    ∃ y : Z, ∀ n : ℕ, n • T₂ (0, 1) ≤ y := by
  let b : eventuallyAffine := ⟨fun k ↦ (k : ℝ),
    0, 1, 0, fun k _ ↦ ((zero_add _).trans (one_mul (k : ℝ))).symm⟩
  refine ⟨T₁ b, fun n ↦ ?_⟩
  let a : eventuallyConstant := ⟨fun k ↦ min (k : ℝ) (n : ℝ),
    ⟨(n : ℝ), n, fun k hk ↦ min_eq_right (Nat.cast_le.mpr hk)⟩⟩
  have ha : eventualValue a = (n : ℝ) := eventualValue_eq_of_eventually_constant a
    (N := n) (fun k hk ↦ min_eq_right (Nat.cast_le.mpr hk))
  have hn : n • T₂ (0, 1) = T₂ (0, (n : ℝ)) :=
    (map_nsmul T₂ n (0, 1)).symm.trans (congrArg T₂
      (Prod.ext (nsmul_zero n) ((nsmul_eq_mul n (1 : ℝ)).trans (mul_one _))))
  exact hn.trans_le
    ((T₂.monotone
      ⟨fun k ↦ le_min (Nat.cast_nonneg k) (Nat.cast_nonneg n), ha.symm.le⟩).trans
      ((hcomm a).symm.trans_le (T₁.monotone (fun k ↦ min_le_left _ _))))

/-- In an Archimedean target, compatibility of this amalgam forces the augmented
constant-sequence map to fail injectivity. -/
lemma affine_amalgam_not_injective
    (Z : Type u) [AddCommGroup Z] [Lattice Z] [IsOrderedAddMonoid Z]
    [VectorLattice Z] [IsVLArchimedean Z]
    (T₁ : VecLatHom eventuallyAffine Z) (T₂ : VecLatHom (eventuallyConstant × ℝ) Z)
    (hcomm : ∀ a : eventuallyConstant,
      T₁ (VectorSublattice.inclusion eventuallyConstant_le_eventuallyAffine a) =
        T₂ (a, eventualValue a)) :
    ¬ Function.Injective T₂ := by
  obtain ⟨y, hy⟩ := affine_amalgam_bounded Z T₁ T₂ hcomm
  have hz : T₂ (0, 1) = 0 :=
    IsVLArchimedean.eq_zero_of_nonneg_of_forall_nsmul_le
      (T₂.map_nonneg ⟨le_rfl, zero_le_one⟩) hy
  exact fun hinj ↦ one_ne_zero (congrArg Prod.snd
    (hinj (hz.trans (map_zero T₂).symm)))

/-- Even Archimedean lattices with countable spectra can force a non-Archimedean pushout
and a noninjective canonical map after Archimedeanization. -/
theorem exists_countable_spectrum_nonarchimedean_pushout :
    ∃ g : VecLatHom eventuallyConstant (eventuallyConstant × ℝ),
      (∀ a, g a = (a, eventualValue a)) ∧ Function.Injective g ∧
      ∀ P : Pushout
          (VectorSublattice.inclusion eventuallyConstant_le_eventuallyAffine) g,
        ¬ IsVLArchimedean P.Carrier ∧
        ¬ Function.Injective ((archimedeanQuotient P.Carrier).comp P.right) := by
  let g : VecLatHom eventuallyConstant (eventuallyConstant × ℝ) :=
    { toFun := fun a ↦ (a, eventualValue a)
      map_add' := fun a b ↦ Prod.ext rfl (map_add eventualValue a b)
      map_smul' := fun c a ↦ Prod.ext rfl (map_smul eventualValue c a)
      map_sup' := fun a b ↦ Prod.ext rfl (map_sup eventualValue a b)
      map_inf' := fun a b ↦ Prod.ext rfl (map_inf eventualValue a b) }
  refine ⟨g, fun _ ↦ rfl, fun _ _ h ↦ congrArg Prod.fst h, fun P ↦ ?_⟩
  exact ⟨fun _ ↦
    affine_amalgam_not_injective P.Carrier P.left P.right
      (fun a ↦ DFunLike.congr_fun P.comm a)
      (pushout_right_injective P
        (VectorSublattice.inclusion_injective eventuallyConstant_le_eventuallyAffine)),
    affine_amalgam_not_injective _
      ((archimedeanQuotient P.Carrier).comp P.left)
      ((archimedeanQuotient P.Carrier).comp P.right)
      (fun a ↦ congrArg (archimedeanQuotient P.Carrier)
        (DFunLike.congr_fun P.comm a))⟩

end VectorLattice.Counterexamples
