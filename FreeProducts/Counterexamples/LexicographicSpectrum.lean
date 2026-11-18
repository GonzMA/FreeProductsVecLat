/-
Authors: Gonzalo Martínez-Fernández
-/

import FreeProducts.CountableSpectra.Basic
import Mathlib.Algebra.Order.Group.PiLex
import Mathlib.Algebra.Order.Module.Synonym

/-!
# Countable prime spectrum without countable generation

Lexicographically ordered real sequences have countably many proper prime ideals and
real vector-space dimension continuum. Hence countable prime spectrum does not imply
countable generation as a vector lattice.
-/

noncomputable section

universe u

namespace VectorLattice.Counterexamples

open VectorLattice.CountableSpectra

/-- Real sequences with lexicographic order form a vector lattice. -/
private instance lexSequenceVectorLattice : VectorLattice (Lex (ℕ → ℝ)) where
  toModule := inferInstance
  smul_le_smul_of_nonneg_left := by
    intro a ha x y hxy
    rcases ha.eq_or_lt with rfl | ha
    · simp only [zero_smul, le_refl]
    · rcases hxy with rfl | ⟨i, hi, hlt⟩
      · exact le_rfl
      · exact Or.inr ⟨i, fun j hj ↦ congrArg (a * ·) (hi j hj),
          mul_lt_mul_of_pos_left hlt ha⟩

/-- An ideal containing a sequence with first nonzero coordinate n contains every sequence
vanishing before coordinate n. -/
private lemma lex_mem_of_initial_zeros (J : OrderIdeal (Lex (ℕ → ℝ)))
    {z x : Lex (ℕ → ℝ)} {n : ℕ} (hz : z ∈ J) (hzn : z n ≠ 0)
    (hz0 : ∀ k < n, z k = 0) (hx0 : ∀ k < n, x k = 0) : x ∈ J := by
  let w : Lex (ℕ → ℝ) := ((|x n| + 1) / z n) • z
  have hw0 : ∀ k < n, w k = 0 :=
    fun k hk ↦ (congrArg (((|x n| + 1) / z n) * ·) (hz0 k hk)).trans (mul_zero _)
  have hwn : w n = |x n| + 1 := div_mul_cancel₀ _ hzn
  have hxw : x ≤ w := Or.inr ⟨n, fun k hk ↦ (hx0 k hk).trans (hw0 k hk).symm,
    ((le_abs_self (x n)).trans_lt (lt_add_one _)).trans_eq hwn.symm⟩
  have hnxw : -x ≤ w := Or.inr ⟨n,
    fun k hk ↦ ((congrArg Neg.neg (hx0 k hk)).trans neg_zero).trans (hw0 k hk).symm,
    ((neg_le_abs (x n)).trans_lt (lt_add_one _)).trans_eq hwn.symm⟩
  exact J.mem_of_abs_mem (J.solid (J.smul_mem _ hz) (abs_nonneg x) (sup_le hxw hnxw))

/-- Every ideal of the lexicographic sequence lattice is either zero or the space of sequences
vanishing on an initial finite segment. -/
private lemma lex_ideal_classification (J : OrderIdeal (Lex (ℕ → ℝ))) :
    ∃ c : Option ℕ, ∀ x : Lex (ℕ → ℝ), x ∈ J ↔
      match c with
      | none => x = 0
      | some n => ∀ k < n, x k = 0 := by
  classical
  by_cases hex : ∃ n : ℕ, ∃ z ∈ J, z n ≠ 0
  · obtain ⟨z, hz, hzn⟩ := Nat.find_spec hex
    have hmin : ∀ x ∈ J, ∀ k < Nat.find hex, x k = 0 :=
      fun x hx k hk ↦ Classical.byContradiction (fun h ↦ Nat.find_min hex hk ⟨x, hx, h⟩)
    exact ⟨some (Nat.find hex), fun x ↦
      ⟨hmin x, lex_mem_of_initial_zeros J hz hzn (hmin z hz)⟩⟩
  · refine ⟨none, fun x ↦ ⟨fun hx ↦ ?_, fun hx ↦ hx.symm ▸ J.zero_mem⟩⟩
    exact funext (fun k ↦ Classical.byContradiction (fun h ↦ hex ⟨k, x, hx, h⟩))

/-- The real vector-space dimension of the lexicographic sequence lattice is continuum. -/
private lemma lex_sequences_rank :
    Module.rank ℝ (Lex (ℕ → ℝ)) = Cardinal.continuum := by
  have hlin : LinearIndependent ℝ (fun r : ℝ ↦ toLex (fun n : ℕ ↦ r ^ n)) :=
    (linearIndependent_monoidHom (Multiplicative ℕ) ℝ).comp
      (powersHom ℝ) (powersHom ℝ).injective
  refine le_antisymm ?_ (Cardinal.mk_real ▸ hlin.cardinal_le_rank)
  refine (rank_le_card ℝ (Lex (ℕ → ℝ))).trans_eq ?_
  change Cardinal.mk (ℕ → ℝ) = Cardinal.continuum
  simp only [Cardinal.mk_arrow, Cardinal.mk_real, Cardinal.mk_nat, Cardinal.lift_id,
    Cardinal.continuum_power_aleph0]

/-- Lexicographically ordered real sequences have countable prime spectrum
and real dimension continuum. -/
theorem lex_sequences_countable_spectrum :
    (properPrimeIdeals (Lex (ℕ → ℝ))).Countable ∧
      Module.rank ℝ (Lex (ℕ → ℝ)) = Cardinal.continuum := by
  choose code hcode using lex_ideal_classification
  have hinj : Function.Injective code := fun J K h ↦ SetLike.ext (fun x ↦
    (hcode J x).trans (h.symm ▸ (hcode K x).symm))
  let : Countable (OrderIdeal (Lex (ℕ → ℝ))) := hinj.countable
  exact ⟨Set.to_countable _, lex_sequences_rank⟩

/-- Countable prime spectrum does not imply countable lattice generation. -/
theorem lex_sequences_not_countably_generated
    (s : Set (Lex (ℕ → ℝ))) (hs : s.Countable) :
    VectorSublattice.generated s ≠ ⊤ := by
  intro hgen
  let D : VectorSublattice (Lex (ℕ → ℝ)) :=
    { toSubmodule := Submodule.span ℝ s
      sup_mem' := fun {x y} hx hy ↦
        (max_choice x y).elim (fun h ↦ h.symm ▸ hx) (fun h ↦ h.symm ▸ hy) }
  have hD : VectorSublattice.generated s ≤ D :=
    VectorSublattice.generated_le Submodule.subset_span
  have hspan : Submodule.span ℝ s = ⊤ := top_unique
    (fun x _ ↦ hD (hgen.symm ▸ show x ∈ (⊤ : VectorSublattice _) from trivial))
  have hcard := (rank_span_le (R := ℝ) s).trans
    (Cardinal.le_aleph0_iff_set_countable.mpr hs)
  rw [hspan, rank_top, lex_sequences_rank] at hcard
  exact Cardinal.aleph0_lt_continuum.not_ge hcard

end VectorLattice.Counterexamples
