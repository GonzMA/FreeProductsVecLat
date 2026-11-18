/-
Authors: Gonzalo Martínez-Fernández
-/

import FreeProducts.CountableSpectra.Ultrapowers

/-!
# Relative injectivity without universal disposition

The hyperreals are injective for the countable-prime extension problem but do not have
the corresponding universal disposition. Total order prevents a lattice embedding of
the coordinatewise real plane.
-/

noncomputable section

universe u

namespace VectorLattice.Counterexamples

open VectorLattice.CountableSpectra

/-- The coordinatewise real plane cannot embed as a lattice into the totally ordered
hyperreals. -/
private lemma no_real_pair_embedding_hyperreal :
    ¬ ∃ T : VecLatHom (Bool → ℝ) Hyperreal, Function.Injective T := by
  rintro ⟨T, hT⟩
  rcases le_total (T (Pi.single false 1)) (T (Pi.single true 1)) with h | h
  · have hfalse := T.le_of_map_le hT h false
    norm_num [Pi.single_apply] at hfalse
  · have htrue := T.le_of_map_le hT h true
    norm_num [Pi.single_apply] at htrue

/-- A totally ordered ultrapower is relatively injective but lacks universal disposition. -/
theorem hyperreal_injective_not_universalDisposition :
    IsCountablePrimeInjective Hyperreal ∧
      ¬ HasCountablePrimeUniversalDisposition Hyperreal := by
  refine ⟨?_, fun h ↦ no_real_pair_embedding_hyperreal ?_⟩
  · exact hyperreal_isCountablePrimeInjective
  · exact embedding_of_extension_from_bot (h (Bool → ℝ) (finite_pi_spectrum Bool).countable ⊥)

end VectorLattice.Counterexamples
