/-
Authors: Gonzalo Martínez-Fernández
-/

import FreeProducts.CountableSpectra.Basic
import FreeProducts.VectorLattice.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# A free product with uncountable prime spectrum

The ordinary free product of two real lines has at least continuum many proper prime
ideals, although each factor has a singleton proper prime spectrum. Scalar characters
with distinct positive ratios distinguish the resulting prime kernels.
-/

noncomputable section

universe u

namespace VectorLattice.Counterexamples

open VectorLattice.CountableSpectra

/-- The free product of two real lines admits a scalar character with any prescribed
nonnegative ratio of generator values. -/
private lemma exists_real_pair_character (P : FreeProduct (fun _ : Bool ↦ ℝ))
    (t : ℝ) (ht : 0 ≤ t) :
    ∃ φ : VecLatHom P.Carrier ℝ,
      φ (P.inclusion false 1) = 1 ∧ φ (P.inclusion true 1) = t := by
  let H : VecLatHom ℝ ℝ :=
    { toLinearMap := (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight t
      map_sup' := fun a b ↦ sup_smul_nonneg t a b ht
      map_inf' := fun a b ↦ inf_smul_nonneg t a b ht }
  obtain ⟨φ, hφ, _⟩ := P.universal ℝ (fun b ↦ if b then H else VecLatHom.id)
  exact ⟨φ, hφ false 1, (hφ true 1).trans (one_smul ℝ t)⟩

/-- Two factors with singleton prime spectra can have a free product
with at least continuum many proper primes. -/
theorem real_pair_uncountable_spectrum (P : FreeProduct (fun _ : Bool ↦ ℝ)) :
    Cardinal.continuum ≤ Cardinal.mk ↥(properPrimeIdeals P.Carrier) := by
  choose φ hφ₁ hφ₂ using fun r : ℝ ↦
    exists_real_pair_character P (Real.exp r) (Real.exp_pos r).le
  let J (r : ℝ) : properPrimeIdeals P.Carrier :=
    ⟨OrderIdeal.ofKerVecLatHom (φ r),
      normalized_character_kernel_prime (φ r) (P.inclusion false 1) (hφ₁ r)⟩
  rw [← Cardinal.mk_real]
  refine Cardinal.mk_le_of_injective (f := J) (fun r s hrs ↦ ?_)
  have hw : P.inclusion true 1 - Real.exp r • P.inclusion false 1 ∈ (J r).val := by
    change (φ r) (P.inclusion true 1 - Real.exp r • P.inclusion false 1) = 0
    simp only [map_sub, map_smul, hφ₁, hφ₂, smul_eq_mul, mul_one, sub_self]
  have hw' : (φ s) (P.inclusion true 1 - Real.exp r • P.inclusion false 1) = 0 :=
    show P.inclusion true 1 - Real.exp r • P.inclusion false 1 ∈ (J s).val from hrs ▸ hw
  suffices s = r from this.symm
  simpa only [map_sub, map_smul, hφ₁, hφ₂, smul_eq_mul, mul_one,
    sub_eq_zero, Real.exp_eq_exp] using hw'

end VectorLattice.Counterexamples
