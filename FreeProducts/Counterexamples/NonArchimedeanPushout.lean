/-
Authors: Gonzalo Martínez-Fernández
-/

import FreeProducts.Counterexamples.SequenceLattices

/-!
# An injective amalgam with a non-Archimedean pushout

Eventually constant sequences map into all real sequences and into their product with
an extra real coordinate. Every compatible Archimedean amalgam kills that coordinate,
so the ordinary pushout is non-Archimedean and Archimedeanization loses injectivity.
-/

noncomputable section

universe u

namespace VectorLattice.Counterexamples

open VectorLattice.CountableSpectra

/-- Compatibility of the two sequence maps bounds every natural multiple of the extra scalar
coordinate by the image of the increasing sequence. -/
private lemma amalgam_nsmul_bound
    (Z : Type u) [AddCommGroup Z] [Lattice Z] [IsOrderedAddMonoid Z]
    [VectorLattice Z]
    (T₁ : VecLatHom (ℕ → ℝ) Z) (T₂ : VecLatHom ((ℕ → ℝ) × ℝ) Z)
    (hcomm : ∀ a : eventuallyConstant, T₁ a.val = T₂ (a.val, eventualValue a)) :
    ∀ n : ℕ, n • T₂ (0, 1) ≤ T₁ (fun k ↦ (k : ℝ)) := by
  intro n
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

/-- A commutative square into an Archimedean lattice collapses the extra coordinate. -/
theorem archimedean_amalgam_kills_extra_coordinate
    (Z : Type u) [AddCommGroup Z] [Lattice Z] [IsOrderedAddMonoid Z]
    [VectorLattice Z] [IsVLArchimedean Z]
    (T₁ : VecLatHom (ℕ → ℝ) Z) (T₂ : VecLatHom ((ℕ → ℝ) × ℝ) Z)
    (hcomm : ∀ a : eventuallyConstant, T₁ a.val = T₂ (a.val, eventualValue a)) :
    T₂ (0, 1) = 0 ∧ ¬ Function.Injective T₂ := by
  have hz : T₂ (0, 1) = 0 :=
    IsVLArchimedean.eq_zero_of_nonneg_of_forall_nsmul_le
      (T₂.map_nonneg ⟨le_rfl, zero_le_one⟩) (amalgam_nsmul_bound Z T₁ T₂ hcomm)
  exact ⟨hz, fun hinj ↦ one_ne_zero (congrArg Prod.snd
    (hinj (hz.trans (map_zero T₂).symm)))⟩

/-- Injective maps between Archimedean lattices can have a non-Archimedean pushout,
whose Archimedeanization loses injectivity of a canonical map. -/
theorem exists_nonarchimedean_pushout :
    ∃ g : VecLatHom eventuallyConstant ((ℕ → ℝ) × ℝ),
      (∀ a, g a = (a.val, eventualValue a)) ∧ Function.Injective g ∧
      ∀ P : Pushout eventuallyConstant.subtype g,
        ¬ IsVLArchimedean P.Carrier ∧
        ¬ Function.Injective ((archimedeanQuotient P.Carrier).comp P.right) := by
  let g : VecLatHom eventuallyConstant ((ℕ → ℝ) × ℝ) :=
    { toFun := fun a ↦ (a.val, eventualValue a)
      map_add' := fun a b ↦ Prod.ext rfl (map_add eventualValue a b)
      map_smul' := fun c a ↦ Prod.ext rfl (map_smul eventualValue c a)
      map_sup' := fun a b ↦ Prod.ext rfl (map_sup eventualValue a b)
      map_inf' := fun a b ↦ Prod.ext rfl (map_inf eventualValue a b) }
  refine ⟨g, fun _ ↦ rfl, fun _ _ h ↦ Subtype.ext (congrArg Prod.fst h), fun P ↦ ?_⟩
  exact ⟨fun _ ↦
    (archimedean_amalgam_kills_extra_coordinate P.Carrier P.left P.right
      (fun a ↦ DFunLike.congr_fun P.comm a)).2
      (pushout_right_injective P eventuallyConstant.subtype_injective),
    (archimedean_amalgam_kills_extra_coordinate _
      ((archimedeanQuotient P.Carrier).comp P.left)
      ((archimedeanQuotient P.Carrier).comp P.right)
      (fun a ↦ congrArg (archimedeanQuotient P.Carrier)
        (DFunLike.congr_fun P.comm a))).2⟩

end VectorLattice.Counterexamples
