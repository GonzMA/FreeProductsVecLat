/-
Authors: Gonzalo Martínez-Fernández
-/

import FreeProducts.CountableSpectra.Basic
import Mathlib.LinearAlgebra.LinearPMap

/-!
# Countable cuts and ordered extension

Countably many Archimedean classes give countable descriptions of cuts.
Interpolation in the target extends ordered embeddings; passing through prime
quotients then gives relative injectivity and a more general extension criterion.
-/

noncomputable section

universe u v w

namespace VectorLattice.CountableSpectra

/-- Countable strictly separated sets admit a point strictly between them. -/
def HasCountableInterpolation (Y : Type*) [Preorder Y] : Prop :=
  ∀ L R : Set Y, L.Countable → R.Countable →
    (∀ l ∈ L, ∀ r ∈ R, l < r) →
      ∃ z, (∀ l ∈ L, l < z) ∧ ∀ r ∈ R, z < r

section CountableCuts

variable {V : Type*} [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V]
  [VectorLattice V]

attribute [local instance] PosSMulMono.toPosSMulStrictMono

/-- If a residual vector has maximal Archimedean class among the differences from a
sublattice, its class is not represented by a nonzero element of that sublattice. -/
private lemma maximal_difference_class_not_in_subspace (D : VectorSublattice V)
    {b d₀ u : V} (hd₀ : d₀ ∈ D)
    (hmax : ∀ d ∈ D, ArchimedeanClass.mk (b - d) ≤ ArchimedeanClass.mk (b - d₀))
    (huD : u ∈ D) (hu : u ≠ 0) :
    ArchimedeanClass.mk (b - d₀) ≠ ArchimedeanClass.mk u := by
  intro heq
  obtain ⟨a, ha⟩ := exists_scalar_remainder_higher_class (abs_pos.mpr hu)
    (by simpa only [ArchimedeanClass.mk_abs] using heq.symm.le)
  have hbound := hmax (d₀ + a • |u|) (D.add_mem hd₀ (D.smul_mem a (D.abs_mem huD)))
  exact ha.not_ge (by
    simpa only [ArchimedeanClass.mk_abs, sub_add_eq_sub_sub, heq] using hbound)

/-- Choose countably many positive vectors representing all nonzero Archimedean classes
occurring in a sublattice. -/
private lemma countable_positive_class_representatives [Countable (ArchimedeanClass V)]
    (D : VectorSublattice V) :
    ∃ S : Set V, S.Countable ∧ S ⊆ D ∧ (∀ u ∈ S, 0 < u) ∧
      ∀ d ∈ D, d ≠ 0 → ∃ u ∈ S, ArchimedeanClass.mk u = ArchimedeanClass.mk d := by
  let C := {c : ArchimedeanClass V | ∃ u ∈ D, 0 < u ∧ ArchimedeanClass.mk u = c}
  choose r hrD hrpos hrclass using fun c : C ↦ c.property
  refine ⟨Set.range r, Set.countable_range r, Set.range_subset_iff.mpr hrD,
    Set.forall_mem_range.mpr hrpos, fun d hd hd₀ ↦ ?_⟩
  let c : C := ⟨ArchimedeanClass.mk d,
    |d|, D.abs_mem hd, abs_pos.mpr hd₀, ArchimedeanClass.mk_abs d⟩
  exact ⟨r c, Set.mem_range_self c, hrclass c⟩

omit [VectorLattice V] in
/-- A sufficiently large integer multiple of a representative supplies an intermediate lower
bound between positive vectors of different classes. -/
private lemma class_representative_lower_bound {w d u : V}
    (hd : 0 < d) (hdw : d < w) (hu : 0 < u)
    (hud : ArchimedeanClass.mk u = ArchimedeanClass.mk d)
    (hwd : ArchimedeanClass.mk w ≠ ArchimedeanClass.mk d) :
    ∃ n : ℕ, d ≤ n • u ∧ n • u < w := by
  have hclass : ArchimedeanClass.mk w < ArchimedeanClass.mk d :=
    lt_of_le_of_ne (ArchimedeanClass.mk_antitoneOn hd.le (hd.trans hdw).le hdw.le) hwd
  obtain ⟨n, hn⟩ := ArchimedeanClass.mk_le_mk.mp hud.le
  exact ⟨n, by simpa only [abs_of_pos hd, abs_of_pos hu] using hn,
    by simpa only [abs_of_pos hu, abs_of_pos (hd.trans hdw)] using
      ArchimedeanClass.mk_lt_mk.mp (hclass.trans_eq hud.symm) n⟩

/-- A sufficiently small reciprocal integer multiple of a representative supplies an
intermediate upper bound between positive vectors of different classes. -/
private lemma class_representative_upper_bound {w d u : V}
    (hw : 0 < w) (hwd : w < d) (hu : 0 < u)
    (hud : ArchimedeanClass.mk u = ArchimedeanClass.mk d)
    (hdw : ArchimedeanClass.mk d ≠ ArchimedeanClass.mk w) :
    ∃ n : ℕ, 0 < n ∧ w < (n : ℝ)⁻¹ • u ∧ (n : ℝ)⁻¹ • u ≤ d := by
  obtain ⟨n, hn⟩ := ArchimedeanClass.mk_le_mk.mp hud.ge
  have hn' : u ≤ (n : ℝ) • d := by
    simpa only [abs_of_pos hu, abs_of_pos (hw.trans hwd), Nat.cast_smul_eq_nsmul] using hn
  have hpos : 0 < ((n + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_succ n)
  refine ⟨n + 1, Nat.zero_lt_succ n, ?_, ?_⟩
  · apply ArchimedeanClass.lt_of_mk_lt_mk_of_nonneg
      (hpos := smul_nonneg (inv_nonneg.mpr hpos.le) hu.le)
    simpa only [ArchimedeanClass.mk_smul u (inv_ne_zero hpos.ne'), hud] using
      lt_of_le_of_ne (ArchimedeanClass.mk_antitoneOn hw.le (hw.trans hwd).le hwd.le) hdw
  · exact (inv_smul_le_iff_of_pos hpos).mpr (hn'.trans
      (smul_le_smul_of_nonneg_right (Nat.cast_le.mpr (Nat.le_succ n)) (hw.trans hwd).le))

/-- A cut has countable cofinal and coinitial subsets in the given sublattice. -/
def HasCountableCutPoints (D : VectorSublattice V) (w : V) : Prop :=
  ∃ T : Set V, T.Countable ∧ T ⊆ D ∧
    (∀ d ∈ D, d < w → ∃ t ∈ T, d ≤ t ∧ t < w) ∧
    (∀ d ∈ D, w < d → ∃ t ∈ T, w < t ∧ t ≤ d)

/-- A positive vector whose Archimedean class is absent from a sublattice admits countable
sets determining its lower and upper cuts in that sublattice. -/
private lemma countable_cut_points_new_class [Countable (ArchimedeanClass V)]
    (D : VectorSublattice V) {w : V} (hw : 0 < w)
    (hnew : ∀ d ∈ D, d ≠ 0 → ArchimedeanClass.mk w ≠ ArchimedeanClass.mk d) :
    HasCountableCutPoints D w := by
  obtain ⟨S, hSc, hSD, hSpos, hSrepr⟩ := countable_positive_class_representatives D
  let T := insert (0 : V) (Set.image2 (fun (q : ℚ) (u : V) ↦ (q : ℝ) • u) Set.univ S)
  refine ⟨T, ((Set.countable_univ.image2 hSc _).insert 0), ?_, ?_, ?_⟩
  · rintro d (rfl | ⟨q, -, u, hu, rfl⟩)
    · exact D.zero_mem
    · exact D.smul_mem q (hSD hu)
  · intro d hd hdw
    rcases le_or_gt d 0 with hd₀ | hd₀
    · exact ⟨0, Or.inl rfl, hd₀, hw⟩
    · obtain ⟨u, hu, hud⟩ := hSrepr d hd hd₀.ne'
      obtain ⟨n, hdn, hnw⟩ := class_representative_lower_bound hd₀ hdw (hSpos u hu) hud
        (hnew d hd hd₀.ne')
      exact ⟨n • u, Or.inr ⟨(n : ℚ), Set.mem_univ _, u, hu,
        by simp only [Rat.cast_natCast, Nat.cast_smul_eq_nsmul]⟩, hdn, hnw⟩
  · intro d hd hwd
    obtain ⟨u, hu, hud⟩ := hSrepr d hd (hw.trans hwd).ne'
    obtain ⟨n, -, hwn, hnd⟩ := class_representative_upper_bound hw hwd (hSpos u hu) hud
      (hnew d hd (hw.trans hwd).ne').symm
    exact ⟨(n : ℝ)⁻¹ • u, Or.inr ⟨(n : ℚ)⁻¹, Set.mem_univ _, u, hu,
      by simp only [Rat.cast_inv, Rat.cast_natCast]⟩, hwn, hnd⟩

/-- Negation transfers countable descriptions of the lower and upper cuts of a vector. -/
private lemma countable_cut_points_neg (D : VectorSublattice V) {w : V}
    (h : HasCountableCutPoints D (-w)) : HasCountableCutPoints D w := by
  obtain ⟨T, hTc, hTD, hlow, hupp⟩ := h
  refine ⟨Neg.neg '' T, hTc.image _, ?_, ?_, ?_⟩
  · exact Set.image_subset_iff.mpr (fun t ht ↦ D.neg_mem (hTD ht))
  · intro d hd hdw
    obtain ⟨t, ht, hwt, htd⟩ := hupp (-d) (D.neg_mem hd) (neg_lt_neg hdw)
    exact ⟨-t, ⟨t, ht, rfl⟩, le_neg.mpr htd, neg_lt.mp hwt⟩
  · intro d hd hwd
    obtain ⟨t, ht, hdt, htw⟩ := hlow (-d) (D.neg_mem hd) (neg_lt_neg hwd)
    exact ⟨-t, ⟨t, ht, rfl⟩, lt_neg.mp htw, neg_le.mp hdt⟩

/-- Translation by a sublattice element transfers countable descriptions of a vector's cuts. -/
private lemma countable_cut_points_translate (D : VectorSublattice V) {a b : V}
    (ha : a ∈ D) (h : HasCountableCutPoints D (b - a)) : HasCountableCutPoints D b := by
  obtain ⟨T, hTc, hTD, hlow, hupp⟩ := h
  refine ⟨(fun t ↦ t + a) '' T, hTc.image _, ?_, ?_, ?_⟩
  · exact Set.image_subset_iff.mpr (fun t ht ↦ D.add_mem (hTD ht) ha)
  · intro d hd hdb
    obtain ⟨t, ht, hdt, htb⟩ := hlow (d - a) (D.sub_mem hd ha) (sub_lt_sub_right hdb a)
    exact ⟨t + a, ⟨t, ht, rfl⟩, sub_le_iff_le_add.mp hdt, lt_sub_iff_add_lt.mp htb⟩
  · intro d hd hbd
    obtain ⟨t, ht, hbt, htd⟩ := hupp (d - a) (D.sub_mem hd ha) (sub_lt_sub_right hbd a)
    exact ⟨t + a, ⟨t, ht, rfl⟩, sub_lt_iff_lt_add.mp hbt, le_sub_iff_add_le.mp htd⟩

/-- A maximal residual Archimedean class yields countable sets determining the cuts of a
vector over a sublattice. -/
private lemma countable_cut_points_of_maximal_class [Countable (ArchimedeanClass V)]
    (D : VectorSublattice V) {b d₀ : V} (hb : b ∉ D) (hd₀ : d₀ ∈ D)
    (hmax : ∀ d ∈ D, ArchimedeanClass.mk (b - d) ≤ ArchimedeanClass.mk (b - d₀)) :
    HasCountableCutPoints D b := by
  apply countable_cut_points_translate D hd₀
  have hne : b - d₀ ≠ 0 := fun h ↦ hb ((sub_eq_zero.mp h).symm ▸ hd₀)
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · apply countable_cut_points_neg D
    exact countable_cut_points_new_class D (neg_pos.mpr hneg) (fun d hd hdne ↦ by
      simpa only [ArchimedeanClass.mk_neg] using
        maximal_difference_class_not_in_subspace D hd₀ hmax hd hdne)
  · exact countable_cut_points_new_class D hpos
      (fun d hd hdne ↦ maximal_difference_class_not_in_subspace D hd₀ hmax hd hdne)

omit [VectorLattice V] in
/-- If one residual has strictly higher class than another, the difference of their sublattice
terms has the class of the lower residual. -/
private lemma difference_class_of_closer {b d e : V}
    (h : ArchimedeanClass.mk (b - d) < ArchimedeanClass.mk (b - e)) :
    ArchimedeanClass.mk (e - d) = ArchimedeanClass.mk (b - d) := by
  have heq : e - d = (b - d) - (b - e) := by abel
  exact heq ▸ ArchimedeanClass.mk_sub_eq_mk_left h

/-- An improvement in residual class bounds the original error by twice the absolute
difference of the approximants. -/
private lemma closer_difference_abs_bound {b d e : V}
    (h : ArchimedeanClass.mk (b - d) < ArchimedeanClass.mk (b - e)) :
    |b - d| < (2 : ℝ) • |e - d| := by
  have hsmall : |b - e| < |e - d| := by
    simpa only [one_nsmul] using ArchimedeanClass.mk_lt_mk.mp
      ((difference_class_of_closer h).trans_lt h) 1
  calc
    |b - d| = |(e - d) + (b - e)| := by congr 1; abel
    _ ≤ |e - d| + |b - e| := abs_add_le _ _
    _ < |e - d| + |e - d| := add_lt_add_of_le_of_lt le_rfl hsmall
    _ = (2 : ℝ) • |e - d| := (two_smul ℝ _).symm

/-- An improvement in residual class gives explicit lower and upper bounds for the vector
using sublattice elements. -/
private lemma closer_cut_bounds {b d e : V}
    (h : ArchimedeanClass.mk (b - d) < ArchimedeanClass.mk (b - e)) :
    d - (2 : ℝ) • |e - d| < b ∧ b < d + (2 : ℝ) • |e - d| := by
  have hsmall := abs_lt.mp (closer_difference_abs_bound h)
  exact ⟨by simpa only [sub_eq_add_neg, add_comm] using lt_sub_iff_add_lt.mp hsmall.1,
    by simpa only [add_comm] using sub_lt_iff_lt_add.mp hsmall.2⟩

/-- The explicit lower and upper bounds have residual classes at least as high as the original
residual class. -/
private lemma closer_cut_classes {b d e : V}
    (h : ArchimedeanClass.mk (b - d) < ArchimedeanClass.mk (b - e)) :
    ArchimedeanClass.mk (b - d) ≤ ArchimedeanClass.mk (b - (d - (2 : ℝ) • |e - d|)) ∧
      ArchimedeanClass.mk (b - d) ≤ ArchimedeanClass.mk ((d + (2 : ℝ) • |e - d|) - b) := by
  have hc : ArchimedeanClass.mk ((2 : ℝ) • |e - d|) = ArchimedeanClass.mk (b - d) := by
    rw [ArchimedeanClass.mk_smul _ (by norm_num : (2 : ℝ) ≠ 0),
      ArchimedeanClass.mk_abs, difference_class_of_closer h]
  constructor
  · convert ArchimedeanClass.mk_left_le_mk_add hc.symm.le using 2; abel
  · convert ArchimedeanClass.mk_right_le_mk_sub hc.symm.le using 2; abel

/-- A nonempty countable linear order without a greatest element has a strictly increasing
cofinal sequence. -/
private lemma exists_strictMono_cofinal_sequence (C : Type*) [LinearOrder C]
    [Countable C] [Nonempty C] [NoMaxOrder C] :
    ∃ f : ℕ → C, StrictMono f ∧ ∀ c, ∃ n, c < f n := by
  obtain ⟨f, hf⟩ := Filter.exists_seq_tendsto (Filter.atTop : Filter C)
  obtain ⟨g, hg, hfg⟩ := Filter.strictMono_subseq_of_tendsto_atTop hf
  exact ⟨f ∘ g, hfg, fun c ↦ ((hf.comp hg.tendsto_atTop).eventually_gt_atTop c).exists⟩

/-- When the residual classes have no maximum, choose sublattice approximants with strictly
increasing, cofinal residual classes. -/
private lemma cofinal_difference_sequence [Countable (ArchimedeanClass V)]
    (D : VectorSublattice V) (b : V)
    (hno : ∀ d ∈ D, ∃ e ∈ D, ArchimedeanClass.mk (b - d) < ArchimedeanClass.mk (b - e)) :
    ∃ d : ℕ → V, (∀ n, d n ∈ D) ∧ StrictMono (fun n ↦ ArchimedeanClass.mk (b - d n)) ∧
      ∀ x ∈ D, ∃ n, ArchimedeanClass.mk (b - x) < ArchimedeanClass.mk (b - d n) := by
  let C := Set.range (fun d : D ↦ ArchimedeanClass.mk (b - d.val))
  let : Nonempty C := ⟨⟨_, Set.mem_range_self (0 : D)⟩⟩
  let : NoMaxOrder C := ⟨fun c ↦ by
    obtain ⟨d, hd⟩ := c.property
    obtain ⟨e, he, hde⟩ := hno d.val d.property
    exact ⟨⟨_, ⟨⟨e, he⟩, rfl⟩⟩, hd.symm.trans_lt hde⟩⟩
  obtain ⟨f, hf, hfc⟩ := exists_strictMono_cofinal_sequence C
  choose d hd using fun n ↦ (f n).property
  refine ⟨fun n ↦ (d n).val, fun n ↦ (d n).property,
    fun i j hij ↦ (hd i).trans_lt
      ((show (f i).val < (f j).val from hf hij).trans_eq (hd j).symm), fun x hx ↦ ?_⟩
  obtain ⟨n, hn⟩ := hfc ⟨_, Set.mem_range_self (⟨x, hx⟩ : D)⟩
  exact ⟨n, (show ArchimedeanClass.mk (b - x) < (f n).val from hn).trans_eq (hd n).symm⟩

/-- The absence of a maximal residual class still yields countable sets determining the cuts
of a vector over a sublattice. -/
private lemma countable_cut_points_of_no_maximal_class [Countable (ArchimedeanClass V)]
    (D : VectorSublattice V) (b : V)
    (hno : ∀ d ∈ D, ∃ e ∈ D, ArchimedeanClass.mk (b - d) < ArchimedeanClass.mk (b - e)) :
    HasCountableCutPoints D b := by
  obtain ⟨d, hd, hm, hc⟩ := cofinal_difference_sequence D b hno
  let r (n : ℕ) := (2 : ℝ) • |d (n + 1) - d n|
  have hr (n : ℕ) : r n ∈ D := D.smul_mem 2 (D.abs_mem (D.sub_mem (hd (n + 1)) (hd n)))
  have hbds (n : ℕ) : d n - r n < b ∧ b < d n + r n :=
    closer_cut_bounds (hm (Nat.lt_succ_self n))
  refine ⟨Set.range (fun n ↦ d n - r n) ∪ Set.range (fun n ↦ d n + r n),
    (Set.countable_range _).union (Set.countable_range _), ?_, ?_, ?_⟩
  · exact Set.union_subset (Set.range_subset_iff.mpr (fun n ↦ D.sub_mem (hd n) (hr n)))
      (Set.range_subset_iff.mpr (fun n ↦ D.add_mem (hd n) (hr n)))
  · intro x hx hxb
    obtain ⟨n, hn⟩ := hc x hx
    have hdist : b - (d n - r n) < b - x :=
      ArchimedeanClass.lt_of_mk_lt_mk_of_nonneg
        (hn.trans_le (closer_cut_classes (hm (Nat.lt_succ_self n))).1) (sub_nonneg.mpr hxb.le)
    exact ⟨d n - r n, Or.inl (Set.mem_range_self n),
      (sub_lt_sub_iff_left b).mp hdist |>.le, (hbds n).1⟩
  · intro x hx hbx
    obtain ⟨n, hn⟩ := hc x hx
    have hdist : d n + r n - b < x - b :=
      ArchimedeanClass.lt_of_mk_lt_mk_of_nonneg
        ((ArchimedeanClass.mk_sub_comm x b).trans_lt
          (hn.trans_le (closer_cut_classes (hm (Nat.lt_succ_self n))).2))
        (sub_nonneg.mpr hbx.le)
    exact ⟨d n + r n, Or.inr (Set.mem_range_self n), (hbds n).2,
      (sub_lt_sub_iff_right b).mp hdist |>.le⟩

/-- Countably many Archimedean classes give countable cuts over every sublattice. -/
theorem countable_cut_points [Countable (ArchimedeanClass V)]
    (D : VectorSublattice V) {b : V} (hb : b ∉ D) : HasCountableCutPoints D b := by
  by_cases hm : ∃ d₀ ∈ D, ∀ d ∈ D,
      ArchimedeanClass.mk (b - d) ≤ ArchimedeanClass.mk (b - d₀)
  · obtain ⟨d₀, hd₀, hmax⟩ := hm
    exact countable_cut_points_of_maximal_class D hb hd₀ hmax
  · push Not at hm
    exact countable_cut_points_of_no_maximal_class D b hm

variable {Y : Type*} [AddCommGroup Y] [LinearOrder Y]
  [IsOrderedAddMonoid Y] [VectorLattice Y]

omit [AddCommGroup Y] [IsOrderedAddMonoid Y] [VectorLattice Y] in
/-- Countable interpolation in the target supplies a value for a new vector that respects all
lower and upper constraints from a partial order embedding. -/
private lemma value_for_cut [Countable (ArchimedeanClass V)]
    (hY : HasCountableInterpolation Y)
    (D : VectorSublattice V) (f : D → Y) (hf : StrictMono f) {b : V} (hb : b ∉ D) :
    ∃ z : Y, (∀ d : D, d.val < b → f d < z) ∧ ∀ d : D, b < d.val → z < f d := by
  obtain ⟨T, hTc, hTD, hlow, hupp⟩ := countable_cut_points D hb
  let L : Set D := {d | d.val ∈ T ∧ d.val < b}
  let R : Set D := {d | d.val ∈ T ∧ b < d.val}
  have hT : (Subtype.val ⁻¹' T : Set D).Countable := hTc.preimage Subtype.val_injective
  have hLR : ∀ l ∈ f '' L, ∀ r ∈ f '' R, l < r := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact hf (hx.2.trans hy.2)
  obtain ⟨z, hL, hR⟩ := hY (f '' L) (f '' R)
    ((hT.mono (fun _ (h : _ ∈ L) ↦ h.1)).image f)
    ((hT.mono (fun _ (h : _ ∈ R) ↦ h.1)).image f) hLR
  refine ⟨z, ?_, ?_⟩
  · intro d hd
    obtain ⟨t, ht, hdt, htb⟩ := hlow d.val d.property hd
    exact (hf.monotone (show d ≤ (⟨t, hTD ht⟩ : D) from hdt)).trans_lt
      (hL _ ⟨⟨t, hTD ht⟩, ⟨ht, htb⟩, rfl⟩)
  · intro d hd
    obtain ⟨t, ht, hbt, htd⟩ := hupp d.val d.property hd
    exact (hR _ ⟨⟨t, hTD ht⟩, ⟨ht, hbt⟩, rfl⟩).trans_le
      (hf.monotone (show (⟨t, hTD ht⟩ : D) ≤ d from htd))

/-- A linear subspace of a totally ordered vector lattice, regarded as a vector sublattice. -/
def submoduleSublattice (D : Submodule ℝ V) : VectorSublattice V where
  toSubmodule := D
  sup_mem' {x y} hx hy := (max_choice x y).elim (fun h ↦ h.symm ▸ hx) (fun h ↦ h.symm ▸ hy)

/-- The lower-cut constraints ensure positivity of the extended linear map on combinations
with positive coefficient of the new vector. -/
private lemma extension_positive_coefficient (D : Submodule ℝ V) (f : D →ₗ[ℝ] Y)
    {b : V} {z : Y} (hL : ∀ d : D, d.val < b → f d < z)
    {c : ℝ} (hc : 0 < c) (d : D) (hpos : 0 < d.val + c • b) : 0 < f d + c • z := by
  have hcmp : (c⁻¹ • (-d) : D).val < b :=
    (inv_smul_lt_iff_of_pos hc).mpr
      (neg_lt_iff_pos_add.mpr (by simpa only [add_comm] using hpos))
  have hcmp' : c⁻¹ • (-f d) < z := by simpa only [map_smul, map_neg] using hL _ hcmp
  simpa only [add_comm] using neg_lt_iff_pos_add.mp ((inv_smul_lt_iff_of_pos hc).mp hcmp')

/-- The upper-cut constraints ensure positivity of the extended linear map on combinations
with negative coefficient of the new vector. -/
private lemma extension_negative_coefficient (D : Submodule ℝ V) (f : D →ₗ[ℝ] Y)
    {b : V} {z : Y} (hR : ∀ d : D, b < d.val → z < f d)
    {c : ℝ} (hc : c < 0) (d : D) (hpos : 0 < d.val + c • b) : 0 < f d + c • z := by
  have hcmp : b < ((-c)⁻¹ • d : D).val :=
    (lt_inv_smul_iff_of_pos (neg_pos.mpr hc)).mpr
      (sub_pos.mp (by simpa only [neg_smul, sub_neg_eq_add] using hpos))
  have hcmp' : z < (-c)⁻¹ • f d := by simpa only [map_smul] using hR _ hcmp
  simpa only [neg_smul, sub_neg_eq_add] using
    sub_pos.mpr ((lt_inv_smul_iff_of_pos (neg_pos.mpr hc)).mp hcmp')

/-- Assigning a cut-compatible value to one new vector extends a strictly monotone partial
linear map to its enlarged domain. -/
private lemma strictMono_supSpanSingleton (f : V →ₗ.[ℝ] Y) (hf : StrictMono f)
    {b : V} {z : Y} (hb : b ∉ f.domain)
    (hL : ∀ d : f.domain, d.val < b → f d < z)
    (hR : ∀ d : f.domain, b < d.val → z < f d) :
    StrictMono (f.supSpanSingleton b z hb) := by
  apply (strictMono_iff_map_pos (f.supSpanSingleton b z hb).toFun).mpr
  rintro ⟨x, hx⟩ hpos
  obtain ⟨d, hd, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [LinearPMap.toFun_eq_coe, f.supSpanSingleton_apply_mk b z hb d hd c]
  rcases lt_trichotomy c 0 with hc | rfl | hc
  · exact extension_negative_coefficient f.domain f.toFun hR hc ⟨d, hd⟩ hpos
  · have hdpos : 0 < d := by
      simpa only [zero_smul, add_zero] using (show 0 < d + (0 : ℝ) • b from hpos)
    simpa only [map_zero, zero_smul, add_zero, LinearPMap.toFun_eq_coe] using
      (strictMono_iff_map_pos f.toFun).mp hf ⟨d, hd⟩ hdpos
  · exact extension_positive_coefficient f.domain f.toFun hL hc ⟨d, hd⟩ hpos

/-- A strictly monotone partial linear map with a proper domain has a strictly larger such
extension when the target has countable interpolation. -/
private lemma exists_larger_ordered_partial_map [Countable (ArchimedeanClass V)]
    (hY : HasCountableInterpolation Y)
    (f : V →ₗ.[ℝ] Y) (hf : StrictMono f) {b : V} (hb : b ∉ f.domain) :
    ∃ g : V →ₗ.[ℝ] Y, f < g ∧ StrictMono g := by
  obtain ⟨z, hL, hR⟩ := value_for_cut hY (submoduleSublattice f.domain) f hf hb
  have hle : f ≤ f.supSpanSingleton b z hb := f.left_le_sup _ _
  exact ⟨_, lt_of_le_not_ge hle (fun h ↦ hb
    (h.1 (Submodule.mem_sup_right (Submodule.mem_span_singleton_self b)))),
    strictMono_supSpanSingleton f hf hb hL hR⟩

/-- The union of a nonempty directed family of strictly monotone partial linear maps is
strictly monotone. -/
lemma strictMono_sSup_partial {Z : Type*}
    [AddCommGroup Z] [Lattice Z] [IsOrderedAddMonoid Z] [VectorLattice Z]
    (C : Set (V →ₗ.[ℝ] Z))
    (hC : DirectedOn (· ≤ ·) C) (hne : C.Nonempty) (hmono : ∀ f ∈ C, StrictMono f) :
    StrictMono (LinearPMap.sSup C hC) := by
  apply (strictMono_iff_map_pos (LinearPMap.sSup C hC).toFun).mpr
  intro x hx
  obtain ⟨f, hf, hxf⟩ := (LinearPMap.mem_domain_sSup_iff hne hC).mp x.property
  have heq : (LinearPMap.sSup C hC).toFun x = f ⟨x.val, hxf⟩ :=
    ((LinearPMap.le_sSup hC hf).2 rfl).symm
  simpa only [heq, LinearPMap.toFun_eq_coe] using
    (strictMono_iff_map_pos f.toFun).mp (hmono f hf) ⟨x.val, hxf⟩ hx

/-- A maximality argument extends a strictly monotone partial linear map to the whole totally
ordered vector lattice. -/
private lemma ordered_partial_map_extension [Countable (ArchimedeanClass V)]
    (hY : HasCountableInterpolation Y)
    (f : V →ₗ.[ℝ] Y) (hf : StrictMono f) :
    ∃ g : V →ₗ.[ℝ] Y, f ≤ g ∧ StrictMono g ∧ g.domain = ⊤ := by
  obtain ⟨g, hfg, hg, hmax⟩ := zorn_le_nonempty₀ {g : V →ₗ.[ℝ] Y | StrictMono g}
    (by
      intro C hCS hC k hk
      exact ⟨LinearPMap.sSup C hC.directedOn,
        strictMono_sSup_partial C hC.directedOn ⟨k, hk⟩ (fun g hg ↦ hCS hg),
        fun g hg ↦ LinearPMap.le_sSup hC.directedOn hg⟩) f hf
  refine ⟨g, hfg, hg, top_unique (fun b _ ↦ ?_)⟩
  by_contra hb
  obtain ⟨g', hgg', hg'⟩ := exists_larger_ordered_partial_map hY g hg hb
  exact hgg'.not_ge (hmax hg' hgg'.le)

/-- Ordered embeddings into a countably interpolating chain extend from sublattices. -/
theorem ordered_lattice_embedding_extension [Countable (ArchimedeanClass V)]
    (hY : HasCountableInterpolation Y)
    (D : VectorSublattice V) (f : VecLatHom D Y) (hf : Function.Injective f) :
    ∃ g : VecLatHom V Y, Function.Injective g ∧ ∀ d : D, g d.val = f d := by
  have hf' : StrictMono f := f.monotone.strictMono_of_injective hf
  obtain ⟨g, hfg, hg, hdom⟩ :=
    ordered_partial_map_extension hY (⟨D.toSubmodule, f.toLinearMap⟩ : V →ₗ.[ℝ] Y) hf'
  let G : V →ₗ[ℝ] Y := g.toFun.comp
    ((LinearMap.id : V →ₗ[ℝ] V).codRestrict g.domain
      (fun x ↦ hdom.ge (show x ∈ (⊤ : Submodule ℝ V) from Submodule.mem_top)))
  have hG : StrictMono G := fun _ _ hxy ↦ hg hxy
  exact ⟨{ toLinearMap := G
           map_sup' := hG.monotone.map_sup
           map_inf' := hG.monotone.map_inf }, hG.injective, fun d ↦ (hfg.2 rfl).symm⟩

/-- An injective lattice homomorphism into a countably interpolating target extends along the
given embedding into a totally ordered vector lattice. -/
private lemma ordered_embedding_extension_map [Countable (ArchimedeanClass V)]
    (hY : HasCountableInterpolation Y)
    {U : Type*} [AddCommGroup U] [Lattice U] [IsOrderedAddMonoid U] [VectorLattice U]
    (f : VecLatHom U V) (hf : Function.Injective f)
    (T : VecLatHom U Y) (hT : Function.Injective T) :
    ∃ S : VecLatHom V Y, ∀ u, S (f u) = T u := by
  let D := VectorSublattice.ofAbsClosed f.toLinearMap.range
    (fun y ⟨x, hx⟩ ↦ ⟨|x|, (f.map_abs x).trans (congrArg abs hx)⟩)
  let e : VecLatEquiv U D :=
    { LinearEquiv.ofInjective f.toLinearMap hf with
      map_sup' := fun x y ↦ Subtype.ext (f.map_sup' x y)
      map_inf' := fun x y ↦ Subtype.ext (f.map_inf' x y) }
  obtain ⟨S, -, hS⟩ := ordered_lattice_embedding_extension hY D
    (T.comp e.symm.toVecLatHom) (hT.comp e.toLinearEquiv.symm.injective)
  exact ⟨S, fun u ↦ (hS (e u)).trans
    (congrArg T (e.toLinearEquiv.symm_apply_apply u))⟩

end CountableCuts

/-- Extend through a prime quotient whose Archimedean classes are countable and whose
restriction to the sublattice is the kernel. -/
private lemma extension_through_prime_of_countable_classes
    {Y : Type*} [AddCommGroup Y] [LinearOrder Y]
    [IsOrderedAddMonoid Y] [VectorLattice Y]
    (hY : HasCountableInterpolation Y)
    {B : Type*} [AddCommGroup B] [Lattice B] [IsOrderedAddMonoid B] [VectorLattice B]
    (A : VectorSublattice B)
    (T : VecLatHom A Y) (Q : OrderIdeal B) (hQ : Q.IsPrime)
    (hclasses :
      letI := Classical.propDecidable
      letI := (OrderIdeal.isTotal_quotient_iff_isPrime Q).mpr hQ
      letI := Lattice.toLinearOrder (B ⧸ Q.toSubmodule)
      Countable (ArchimedeanClass (B ⧸ Q.toSubmodule)))
    (hker : ∀ a : A, a.val ∈ Q ↔ T a = 0) :
    ∃ S : VecLatHom B Y, ∀ a : A, S a.val = T a := by
  classical
  let := (OrderIdeal.isTotal_quotient_iff_isPrime Q).mpr hQ
  let := Lattice.toLinearOrder (B ⧸ Q.toSubmodule)
  let := hclasses
  let P := OrderIdeal.ofKerVecLatHom T
  let q := Q.mkQVecLatHom.comp A.subtype
  have hk : P.toSubmodule = LinearMap.ker q.toLinearMap :=
    Submodule.ext (fun a ↦ ((hker a).symm.trans (Submodule.Quotient.mk_eq_zero _).symm))
  let F := P.liftQVecLatHom q hk.le
  have hF : Function.Injective F := LinearMap.ker_eq_bot.mp
    (Submodule.ker_liftQ_eq_bot P.toSubmodule q.toLinearMap hk.le hk.ge)
  let H := P.liftQVecLatHom T le_rfl
  have hH : Function.Injective H := LinearMap.ker_eq_bot.mp
    (Submodule.ker_liftQ_eq_bot P.toSubmodule T.toLinearMap le_rfl le_rfl)
  obtain ⟨S, hS⟩ := ordered_embedding_extension_map hY F hF H hH
  exact ⟨S.comp Q.mkQVecLatHom, fun a ↦ hS (P.mkQ a)⟩

/-- Extend a homomorphism through a prime quotient of the ambient lattice when the prime ideal
restricts to its kernel. -/
private lemma extension_through_prime
    {Y : Type*} [AddCommGroup Y] [LinearOrder Y]
    [IsOrderedAddMonoid Y] [VectorLattice Y]
    (hY : HasCountableInterpolation Y)
    {B : Type*} [AddCommGroup B] [Lattice B] [IsOrderedAddMonoid B] [VectorLattice B]
    (hB : (properPrimeIdeals B).Countable) (A : VectorSublattice B)
    (T : VecLatHom A Y) (Q : OrderIdeal B) (hQ : Q.IsPrime)
    (hker : ∀ a : A, a.val ∈ Q ↔ T a = 0) :
    ∃ S : VecLatHom B Y, ∀ a : A, S a.val = T a := by
  classical
  let := (OrderIdeal.isTotal_quotient_iff_isPrime Q).mpr hQ
  let := Lattice.toLinearOrder (B ⧸ Q.toSubmodule)
  exact extension_through_prime_of_countable_classes hY A T Q hQ
    (countable_classes_of_countable_spectrum
      (countable_spectrum_of_surjective Q.mkQVecLatHom Q.toSubmodule.mkQ_surjective hB)) hker

/-- A totally ordered lattice with countable interpolation is countable-prime-injective. -/
theorem isCountablePrimeInjective_of_countableInterpolation
    {Y : Type u} [AddCommGroup Y] [LinearOrder Y]
    [IsOrderedAddMonoid Y] [VectorLattice Y]
    (hY : HasCountableInterpolation Y) : IsCountablePrimeInjective Y := by
  intro B _ _ _ _ hB A T
  have hP : (OrderIdeal.ofKerVecLatHom T).IsPrime := by
    intro a b hab
    have hzero : min (T a) (T b) = 0 :=
      (map_inf T a b).symm.trans ((congrArg T hab).trans (map_zero T))
    exact (min_choice (T a) (T b)).elim
      (fun h ↦ Or.inl (h.symm.trans hzero)) (fun h ↦ Or.inr (h.symm.trans hzero))
  obtain ⟨Q, hQ, hQA⟩ := OrderIdeal.exists_prime_extension A
    (OrderIdeal.ofKerVecLatHom T) hP
  exact extension_through_prime hY hB A T Q hQ hQA

/-- Homomorphisms into a countably interpolating chain extend when every proper prime
quotient of the ambient lattice has countably many Archimedean classes. -/
theorem exists_extension_of_countable_prime_quotient_classes
    {Y B : Type u} [AddCommGroup Y] [LinearOrder Y]
    [IsOrderedAddMonoid Y] [VectorLattice Y]
    [AddCommGroup B] [Lattice B] [IsOrderedAddMonoid B] [VectorLattice B]
    (hY : HasCountableInterpolation Y)
    (hB : ∀ (Q : OrderIdeal B) (hQ : Q ∈ properPrimeIdeals B),
      letI := Classical.propDecidable
      letI := (OrderIdeal.isTotal_quotient_iff_isPrime Q).mpr hQ.2
      letI := Lattice.toLinearOrder (B ⧸ Q.toSubmodule)
      Countable (ArchimedeanClass (B ⧸ Q.toSubmodule)))
    (A : VectorSublattice B) (T : VecLatHom A Y) :
    ∃ S : VecLatHom B Y, ∀ a : A, S a.val = T a := by
  classical
  by_cases hz : ∀ a, T a = 0
  · exact ⟨VecLatHom.ofAbs 0 (fun _ ↦ abs_zero.symm), fun a ↦ (hz a).symm⟩
  have hP : (OrderIdeal.ofKerVecLatHom T).IsPrime := fun a b hab ↦
    (min_choice (T a) (T b)).elim
      (fun h ↦ Or.inl (h.symm.trans
        ((map_inf T a b).symm.trans ((congrArg T hab).trans (map_zero T)))))
      (fun h ↦ Or.inr (h.symm.trans
        ((map_inf T a b).symm.trans ((congrArg T hab).trans (map_zero T)))))
  obtain ⟨Q, hQ, hQA⟩ := proper_prime_extension A
    ⟨OrderIdeal.ofKerVecLatHom T,
      ⟨fun h ↦ hz (fun a ↦ show a ∈ OrderIdeal.ofKerVecLatHom T from
        h.symm ▸ OrderIdeal.mem_top), hP⟩⟩
  exact extension_through_prime_of_countable_classes hY A T Q hQ.2 (hB Q hQ) hQA

end VectorLattice.CountableSpectra
