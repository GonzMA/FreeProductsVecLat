/-
Authors: Gonzalo Martínez-Fernández
-/

import FreeProducts.CountableSpectra.OrderedExtension
import Mathlib.Analysis.Real.Hyperreal

/-!
# Ordered real ultrapowers

Ordered real ultrapowers over nonprincipal ultrafilters have countable interpolation
and cardinality continuum. The ordered extension theorem gives relative injectivity,
including the hyperreal case.
-/

noncomputable section

universe u v w

namespace VectorLattice.CountableSpectra

/-- Real sequences modulo equality on an ultrafilter, ordered coordinatewise. -/
abbrev OrderedUltrapower (U : Ultrafilter ℕ) := Filter.Germ (U : Filter ℕ) ℝ

/-- The ordered ultrapower carries its coordinatewise real vector lattice structure. -/
instance orderedUltrapowerVectorLattice (U : Ultrafilter ℕ) :
    VectorLattice (OrderedUltrapower U) where
  toModule := inferInstanceAs
    (Module ℝ (Filter.Germ (U : Filter ℕ) ℝ))
  smul_le_smul_of_nonneg_left := by
    intro a ha x y hxy
    refine Filter.Germ.inductionOn₂ x y
      (p := fun x y ↦ x ≤ y → a • x ≤ a • y) (fun f g hfg ↦ ?_) hxy
    exact hfg.mono (fun n hn ↦ mul_le_mul_of_nonneg_left hn ha)

/-- The hyperreals inherit the real vector lattice structure of their ultrapower. -/
instance hyperrealVectorLattice : VectorLattice Hyperreal :=
  orderedUltrapowerVectorLattice (Filter.hyperfilter ℕ)

/-- Choose a sequence that eventually satisfies every finite level of an increasing family of
constraints. -/
private lemma diagonal_eventual_choice {Y : Type*} [Nonempty Y]
    (F : Filter ℕ) (hF : F ≤ Filter.atTop) (p : ℕ → ℕ → Y → Prop)
    (hmono : ∀ i j, i ≤ j → ∀ n y, p j n y → p i n y)
    (hex : ∀ m, ∀ᶠ n in F, ∃ y, p m n y) :
    ∃ z : ℕ → Y, ∀ m, ∀ᶠ n in F, p m n (z n) := by
  classical
  let k (n : ℕ) := Nat.findGreatest (fun m ↦ ∃ y, p m n y) n
  let z (n : ℕ) := if h : ∃ y, p (k n) n y then h.choose else Classical.arbitrary Y
  refine ⟨z, fun m ↦ ?_⟩
  filter_upwards [hF (Filter.eventually_ge_atTop m), hex m] with n hmn hn
  have hk : ∃ y, p (k n) n y :=
    Nat.findGreatest_spec (P := fun m ↦ ∃ y, p m n y) hmn hn
  exact hmono m (k n) (Nat.le_findGreatest (P := fun m ↦ ∃ y, p m n y) hmn hn) n (z n)
    (by simpa only [z, dite_eq_left hk] using hk.choose_spec)

/-- Two finite lists of real numbers with every lower value below every upper value admit a
strict interpolant. -/
private lemma real_prefix_interpolation (a b : ℕ → ℝ) (m : ℕ)
    (hab : ∀ i ≤ m, ∀ j ≤ m, a i < b j) :
    ∃ t : ℝ, ∀ i ≤ m, a i < t ∧ t < b i := by
  let s := Finset.range (m + 1)
  have hs : s.Nonempty := ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ m)⟩
  have hgap : s.sup' hs a < s.inf' hs b := by
    simpa only [Finset.sup'_lt_iff, Finset.lt_inf'_iff, Finset.mem_range,
      Nat.lt_succ_iff, s] using fun j hj i hi ↦ hab i hi j hj
  obtain ⟨t, ht₁, ht₂⟩ := exists_between hgap
  exact ⟨t, fun i hi ↦
    ⟨(Finset.le_sup' a (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))).trans_lt ht₁,
      ht₂.trans_le (Finset.inf'_le b (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)))⟩⟩

/-- Eventual separation of two sequences gives eventual interpolation between each pair of
finite prefixes. -/
private lemma eventual_prefix_interpolation (A B : ℕ → ℕ → ℝ) (F : Filter ℕ)
    (hAB : ∀ i j, ∀ᶠ n in F, A i n < B j n) (m : ℕ) :
    ∀ᶠ n in F, ∃ t : ℝ, ∀ i ≤ m, A i n < t ∧ t < B i n := by
  have hall : ∀ᶠ n in F, ∀ i j : Fin (m + 1), A i n < B j n :=
    Filter.eventually_all.mpr (fun i ↦ Filter.eventually_all.mpr (fun j ↦ hAB i j))
  exact hall.mono (fun n hn ↦ real_prefix_interpolation (fun i ↦ A i n) (fun i ↦ B i n)
    m (fun i hi j hj ↦ hn ⟨i, Nat.lt_succ_of_le hi⟩ ⟨j, Nat.lt_succ_of_le hj⟩))

section UltrapowerInterpolation

variable (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ Filter.atTop)

/-- Every element of the ordered ultrapower is represented by a sequence of real numbers. -/
private lemma ultrapower_ofFun_surjective :
    Function.Surjective (Filter.Germ.ofFun : (ℕ → ℝ) → OrderedUltrapower U) :=
  Quot.exists_rep

include hU

/-- Two countable sequences that are strictly separated in the ultrapower admit a common
strict interpolant. -/
private lemma ultrapower_sequence_interpolation (a b : ℕ → OrderedUltrapower U)
    (hab : ∀ i j, a i < b j) : ∃ z : OrderedUltrapower U, ∀ i, a i < z ∧ z < b i := by
  choose A hA using fun i ↦ ultrapower_ofFun_surjective U (a i)
  choose B hB using fun i ↦ ultrapower_ofFun_surjective U (b i)
  have hAB (i j : ℕ) : ∀ᶠ n in U, A i n < B j n :=
    Filter.Germ.coe_lt.mp ((hA i).trans_lt ((hab i j).trans_eq (hB j).symm))
  obtain ⟨z, hz⟩ := diagonal_eventual_choice (U) hU
    (fun m n t ↦ ∀ i ≤ m, A i n < t ∧ t < B i n)
    (fun i j hij n t h k hk ↦ h k (hk.trans hij))
    (eventual_prefix_interpolation A B (U) hAB)
  exact ⟨Filter.Germ.ofFun (l := (U : Filter ℕ)) z, fun i ↦
    ⟨(hA i).symm.trans_lt (Filter.Germ.coe_lt.mpr
      ((hz i).mono (fun n hn ↦ (hn i le_rfl).1))),
      (Filter.Germ.coe_lt.mpr ((hz i).mono (fun n hn ↦ (hn i le_rfl).2))).trans_eq
        (hB i)⟩⟩

/-- Every sequence in the ultrapower has a strict upper bound. -/
private lemma ultrapower_sequence_upper_bound (a : ℕ → OrderedUltrapower U) :
    ∃ z : OrderedUltrapower U, ∀ i, a i < z := by
  choose A hA using fun i ↦ ultrapower_ofFun_surjective U (a i)
  let z (n : ℕ) := (Finset.range (n + 1)).sup'
    ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n)⟩ (fun i ↦ A i n) + 1
  refine ⟨Filter.Germ.ofFun (l := (U : Filter ℕ)) z, fun i ↦ (hA i).symm.trans_lt
    (Filter.Germ.coe_lt.mpr ?_)⟩
  exact Filter.Eventually.mono (hU (Filter.eventually_ge_atTop i)) (fun n hn ↦
    (Finset.le_sup' (fun j ↦ A j n) (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))).trans_lt
      (lt_add_one _))

/-- Every countable subset of the ultrapower has a strict upper bound. -/
private lemma ultrapower_countable_upper_bound (L : Set (OrderedUltrapower U)) (hL : L.Countable) :
    ∃ z : OrderedUltrapower U, ∀ l ∈ L, l < z := by
  rcases L.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, fun l hl ↦ False.elim hl⟩
  · obtain ⟨a, rfl⟩ := hL.exists_eq_range hne
    obtain ⟨z, hz⟩ := ultrapower_sequence_upper_bound U hU a
    exact ⟨z, fun _ ⟨i, hi⟩ ↦ hi ▸ hz i⟩

/-- Every countable subset of the ultrapower has a strict lower bound. -/
private lemma ultrapower_countable_lower_bound (R : Set (OrderedUltrapower U)) (hR : R.Countable) :
    ∃ z : OrderedUltrapower U, ∀ r ∈ R, z < r := by
  obtain ⟨z, hz⟩ := ultrapower_countable_upper_bound U hU (Neg.neg '' R) (hR.image Neg.neg)
  exact ⟨-z, fun r hr ↦ neg_lt.mp (hz (-r) ⟨r, hr, rfl⟩)⟩

/-- Any two strictly separated countable subsets of the ultrapower admit a strict interpolant,
including when either set is empty. -/
private lemma ultrapower_countable_interpolation (L R : Set (OrderedUltrapower U))
    (hL : L.Countable) (hR : R.Countable) (hLR : ∀ l ∈ L, ∀ r ∈ R, l < r) :
    ∃ z : OrderedUltrapower U, (∀ l ∈ L, l < z) ∧ ∀ r ∈ R, z < r := by
  rcases L.eq_empty_or_nonempty with hLe | hLn
  · obtain ⟨z, hz⟩ := ultrapower_countable_lower_bound U hU R hR
    exact ⟨z, fun l hl ↦ by simp only [hLe, Set.mem_empty_iff_false] at hl, hz⟩
  · rcases R.eq_empty_or_nonempty with hRe | hRn
    · obtain ⟨z, hz⟩ := ultrapower_countable_upper_bound U hU L hL
      exact ⟨z, hz, fun r hr ↦ by simp only [hRe, Set.mem_empty_iff_false] at hr⟩
    · obtain ⟨a, ha⟩ := hL.exists_eq_range hLn
      obtain ⟨b, hb⟩ := hR.exists_eq_range hRn
      obtain ⟨z, hz⟩ := ultrapower_sequence_interpolation U hU a b
        (fun i j ↦ hLR (a i) (ha ▸ Set.mem_range_self i) (b j) (hb ▸ Set.mem_range_self j))
      exact ⟨z, fun l hl ↦ (Set.mem_range.mp (show l ∈ Set.range a from ha ▸ hl)).elim
        (fun i hi ↦ hi ▸ (hz i).1),
        fun r hr ↦ (Set.mem_range.mp (show r ∈ Set.range b from hb ▸ hr)).elim
          (fun i hi ↦ hi ▸ (hz i).2)⟩

end UltrapowerInterpolation

/-- Ordered real ultrapowers over nonprincipal ultrafilters have countable interpolation. -/
theorem orderedUltrapower_hasCountableInterpolation (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ Filter.cofinite) :
    HasCountableInterpolation (OrderedUltrapower U) := by
  exact ultrapower_countable_interpolation U (hU.trans_eq Nat.cofinite_eq_atTop)

/-- Every ordered real ultrapower over the natural numbers has cardinality continuum. -/
theorem orderedUltrapower_cardinal (U : Ultrafilter ℕ) :
    Cardinal.mk (OrderedUltrapower U) = Cardinal.continuum := by
  refine le_antisymm ?_ (Cardinal.mk_real.symm.trans_le
    (Cardinal.mk_le_of_injective (f := fun r : ℝ ↦ (↑r : OrderedUltrapower U))
      (fun _ _ h ↦ Filter.Germ.const_inj.mp h)))
  simpa only [Cardinal.mk_arrow, Cardinal.mk_real, Cardinal.mk_nat, Cardinal.lift_id,
    Cardinal.continuum_power_aleph0] using
      Cardinal.mk_le_of_surjective (ultrapower_ofFun_surjective U)

/-- Ordered real ultrapowers over nonprincipal ultrafilters are countable-prime-injective. -/
theorem orderedUltrapower_isCountablePrimeInjective (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ Filter.cofinite) :
    IsCountablePrimeInjective (OrderedUltrapower U) := by
  exact isCountablePrimeInjective_of_countableInterpolation
    (orderedUltrapower_hasCountableInterpolation U hU)

/-- The hyperreal vector lattice is countable-prime-injective. -/
theorem hyperreal_isCountablePrimeInjective : IsCountablePrimeInjective Hyperreal := by
  exact isCountablePrimeInjective_of_countableInterpolation
    (ultrapower_countable_interpolation (Filter.hyperfilter ℕ) Nat.hyperfilter_le_atTop)

end VectorLattice.CountableSpectra
