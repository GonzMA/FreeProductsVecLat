/-
Authors: Gonzalo Martínez-Fernández
-/

import FreeProducts.VectorLattice.PrimeIdeals
import BanLat.Pi
import Mathlib.Algebra.Order.Module.Archimedean
import Mathlib.Analysis.Real.Cardinality
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.SetTheory.Cardinal.Continuum

/-!
# Prime spectra and cardinal bounds

Proper prime spectra define relative injectivity and universal disposition.
Their behavior under sublattices, quotients and equivalences relates countable spectra
to Archimedean classes and bounds the size of the lattice by the continuum.
-/

noncomputable section

universe u v w

namespace VectorLattice.CountableSpectra

/-- The spectrum consists of proper prime order ideals. -/
def properPrimeIdeals (X : Type u) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] : Set (OrderIdeal X) :=
  {J | J ≠ ⊤ ∧ J.IsPrime}

/-- The kernel of a normalized real character is a proper prime ideal. -/
lemma normalized_character_kernel_prime
    {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X]
    (φ : VecLatHom X ℝ) (u : X) (hu : φ u = 1) :
    OrderIdeal.ofKerVecLatHom φ ∈ properPrimeIdeals X := by
  constructor
  · intro htop
    have hzero : φ u = 0 :=
      show u ∈ OrderIdeal.ofKerVecLatHom φ from
        htop.symm ▸ show u ∈ (⊤ : OrderIdeal X) from trivial
    exact one_ne_zero (hu.symm.trans hzero)
  · intro a b hab
    have hzero : min (φ a) (φ b) = 0 :=
      (map_inf φ a b).symm.trans ((congrArg φ hab).trans (map_zero φ))
    exact (min_choice (φ a) (φ b)).elim
      (fun h ↦ Or.inl (h.symm.trans hzero)) (fun h ↦ Or.inr (h.symm.trans hzero))

/-- A proper ideal in a finite coordinate lattice must omit at least one coordinate unit. -/
private lemma pi_prime_has_missing_coordinate {ι : Type*} [Finite ι] [DecidableEq ι]
    (J : OrderIdeal (ι → ℝ)) (hJ : J ≠ ⊤) :
    ∃ i, Pi.single i 1 ∉ J := by
  classical
  let := Fintype.ofFinite ι
  by_contra! h
  refine hJ (top_unique (fun x _ ↦ ?_))
  have hsum : (∑ i, x i • Pi.single i (1 : ℝ)) ∈ J :=
    J.toSubmodule.sum_mem (fun i _ ↦ J.smul_mem _ (h i))
  simpa only [← Pi.single_smul, smul_eq_mul, mul_one, Finset.univ_sum_single] using hsum

/-- A prime ideal missing a coordinate unit is that coordinate kernel. -/
lemma pi_prime_mem_iff {ι : Type*} [DecidableEq ι]
    (J : OrderIdeal (ι → ℝ)) (hprime : J.IsPrime) (i : ι)
    (hi : Pi.single i 1 ∉ J) (x : ι → ℝ) : x ∈ J ↔ x i = 0 := by
  constructor
  · intro hx
    by_contra hxi
    refine hi ((J.toSubmodule.smul_mem_iff (abs_pos.mpr hxi).ne').mp
      (J.solid (J.abs_mem hx)
        (smul_nonneg (abs_nonneg (x i)) (Pi.single_nonneg.mpr zero_le_one)) ?_))
    intro j
    by_cases hji : j = i <;> simp [hji]
  · intro hxi
    refine J.mem_of_abs_mem ((hprime |x| (Pi.single i 1) ?_).resolve_right hi)
    ext j
    by_cases hji : j = i <;> simp [hji, hxi]

/-- A finite coordinate lattice has finite proper prime spectrum. -/
lemma finite_pi_spectrum (ι : Type*) [Finite ι] :
    (properPrimeIdeals (ι → ℝ)).Finite := by
  classical
  choose code hcode using fun J : properPrimeIdeals (ι → ℝ) ↦
    pi_prime_has_missing_coordinate J.val J.property.1
  have hinj : Function.Injective code := fun J K h ↦ Subtype.ext (SetLike.ext (fun x ↦
    (pi_prime_mem_iff J.val J.property.2 (code J) (hcode J) x).trans
      (h.symm ▸ (pi_prime_mem_iff K.val K.property.2 (code K) (hcode K) x).symm)))
  let : Finite (properPrimeIdeals (ι → ℝ)) := Finite.of_injective code hinj
  exact Set.toFinite _

/-- The inverse image of an order ideal under a lattice homomorphism. -/
def idealPreimage {X Y : Type*}
    [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X]
    [AddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [VectorLattice Y]
    (T : VecLatHom X Y) (J : OrderIdeal Y) : OrderIdeal X :=
  OrderIdeal.ofSolid (J.toSubmodule.comap T.toLinearMap)
    (fun _ _ hx hle ↦ J.mem_of_abs_le_abs hx
      ((T.map_abs _).symm.le.trans ((T.monotone hle).trans_eq (T.map_abs _))))

/-- Pulling an ideal back along a vector lattice equivalence preserves being proper and prime. -/
private lemma idealPreimage_properPrime {X Y : Type*}
    [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X]
    [AddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [VectorLattice Y]
    (e : VecLatEquiv X Y) (J : OrderIdeal Y) (hJ : J ∈ properPrimeIdeals Y) :
    idealPreimage e.toVecLatHom J ∈ properPrimeIdeals X := by
  constructor
  · intro htop
    refine hJ.1 (top_unique (fun y _ ↦ ?_))
    obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective y
    exact show x ∈ idealPreimage e.toVecLatHom J from
      htop.symm ▸ show x ∈ (⊤ : OrderIdeal X) from trivial
  · exact fun a b hab ↦ hJ.2 (e a) (e b) (e.toVecLatHom.map_disjoint hab)

/-- A surjective lattice homomorphism determines each target ideal uniquely by its inverse
image. -/
private lemma idealPreimage_injective {X Y : Type*}
    [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X]
    [AddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [VectorLattice Y]
    (T : VecLatHom X Y) (hT : Function.Surjective T) :
    Function.Injective (idealPreimage T) := by
  intro J K h
  refine SetLike.ext (fun y ↦ ?_)
  obtain ⟨x, rfl⟩ := hT y
  exact (congrArg (fun I : OrderIdeal X ↦ x ∈ I) h).to_iff

/-- Lattice equivalences preserve finiteness of the proper prime spectrum. -/
lemma finite_spectrum_of_equiv {X Y : Type*}
    [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X]
    [AddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [VectorLattice Y]
    (e : VecLatEquiv X Y) (hY : (properPrimeIdeals Y).Finite) :
    (properPrimeIdeals X).Finite := by
  let F (J : properPrimeIdeals X) : properPrimeIdeals Y :=
    ⟨idealPreimage e.symm.toVecLatHom J.val, idealPreimage_properPrime e.symm J.val J.property⟩
  have hF : Function.Injective F := fun J K h ↦ Subtype.ext
    (idealPreimage_injective e.symm.toVecLatHom e.toLinearEquiv.symm.surjective
      (congrArg Subtype.val h))
  let := hY.to_subtype
  let : Finite (properPrimeIdeals X) := Finite.of_injective F hF
  exact Set.toFinite _

/-- Every homomorphism from a sublattice of a lattice with countable spectrum extends. -/
def IsCountablePrimeInjective (Z : Type u) [AddCommGroup Z] [Lattice Z]
    [IsOrderedAddMonoid Z] [VectorLattice Z] : Prop :=
  ∀ (B : Type u) [AddCommGroup B] [Lattice B] [IsOrderedAddMonoid B] [VectorLattice B],
    (properPrimeIdeals B).Countable →
      ∀ (A : VectorSublattice B) (T : VecLatHom A Z),
        ∃ S : VecLatHom B Z, ∀ a, S a.val = T a

/-- Every embedding from a sublattice of a lattice with countable spectrum
extends to an embedding of the whole lattice. -/
def HasCountablePrimeUniversalDisposition (Z : Type u) [AddCommGroup Z] [Lattice Z]
    [IsOrderedAddMonoid Z] [VectorLattice Z] : Prop :=
  ∀ (B : Type u) [AddCommGroup B] [Lattice B] [IsOrderedAddMonoid B] [VectorLattice B],
    (properPrimeIdeals B).Countable →
      ∀ (A : VectorSublattice B) (T : VecLatHom A Z), Function.Injective T →
        ∃ S : VecLatHom B Z, Function.Injective S ∧ ∀ a, S a.val = T a

/-- The inverse image of a proper prime ideal under a surjective lattice homomorphism is
proper and prime. -/
private lemma idealPreimage_properPrime_of_surjective {X Y : Type*}
    [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X]
    [AddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [VectorLattice Y]
    (T : VecLatHom X Y) (hT : Function.Surjective T)
    (J : OrderIdeal Y) (hJ : J ∈ properPrimeIdeals Y) :
    idealPreimage T J ∈ properPrimeIdeals X := by
  refine ⟨?_, fun a b hab ↦ hJ.2 (T a) (T b) (T.map_disjoint hab)⟩
  intro htop
  refine hJ.1 (top_unique (fun y _ ↦ ?_))
  obtain ⟨x, rfl⟩ := hT y
  exact show x ∈ idealPreimage T J from
    htop.symm ▸ show x ∈ (⊤ : OrderIdeal X) from trivial

/-- A surjective lattice homomorphism cannot increase the size of the proper prime spectrum. -/
theorem spectrum_cardinal_le_of_surjective {X Y : Type u}
    [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X]
    [AddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [VectorLattice Y]
    (T : VecLatHom X Y) (hT : Function.Surjective T) :
    Cardinal.mk ↥(properPrimeIdeals Y) ≤ Cardinal.mk ↥(properPrimeIdeals X) := by
  exact Cardinal.mk_le_of_injective
    (f := fun J : properPrimeIdeals Y ↦
      (⟨idealPreimage T J.val, idealPreimage_properPrime_of_surjective T hT J.val J.property⟩ :
        properPrimeIdeals X))
    (fun _ _ h ↦ Subtype.ext (idealPreimage_injective T hT (congrArg Subtype.val h)))

/-- Surjective lattice homomorphisms preserve countability of the proper prime spectrum. -/
lemma countable_spectrum_of_surjective {X Y : Type*}
    [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X]
    [AddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [VectorLattice Y]
    (T : VecLatHom X Y) (hT : Function.Surjective T)
    (hX : (properPrimeIdeals X).Countable) : (properPrimeIdeals Y).Countable := by
  let F (J : properPrimeIdeals Y) : properPrimeIdeals X :=
    ⟨idealPreimage T J.val, idealPreimage_properPrime_of_surjective T hT J.val J.property⟩
  have hF : Function.Injective F := fun J K h ↦ Subtype.ext
    (idealPreimage_injective T hT (congrArg Subtype.val h))
  let := hX.to_subtype
  exact hF.countable

/-- Every proper prime ideal of a vector sublattice extends to a proper prime ideal of the
ambient vector lattice. -/
lemma proper_prime_extension {B : Type*}
    [AddCommGroup B] [Lattice B] [IsOrderedAddMonoid B] [VectorLattice B]
    (A : VectorSublattice B) (J : properPrimeIdeals A) :
    ∃ Q : OrderIdeal B, Q ∈ properPrimeIdeals B ∧ ∀ a : A, a.val ∈ Q ↔ a ∈ J.val := by
  obtain ⟨Q, hQ, hQA⟩ := OrderIdeal.exists_prime_extension A J.val J.property.2
  exact ⟨Q, ⟨fun ht ↦ J.property.1 (top_unique (fun a _ ↦ (hQA a).mp
    (ht.symm ▸ show a.val ∈ (⊤ : OrderIdeal B) from trivial))), hQ⟩, hQA⟩

/-- A sublattice has no more proper prime ideals than its ambient lattice. -/
theorem spectrum_cardinal_sublattice {B : Type*}
    [AddCommGroup B] [Lattice B] [IsOrderedAddMonoid B] [VectorLattice B]
    (A : VectorSublattice B) :
    Cardinal.mk ↥(properPrimeIdeals A) ≤ Cardinal.mk ↥(properPrimeIdeals B) := by
  choose Q hQ hQA using proper_prime_extension A
  let F (J : properPrimeIdeals A) : properPrimeIdeals B := ⟨Q J, hQ J⟩
  have hF : Function.Injective F := fun J K h ↦ Subtype.ext (SetLike.ext (fun a ↦
    (hQA J a).symm.trans ((congrArg (fun I : OrderIdeal B ↦ a.val ∈ I)
      (congrArg Subtype.val h)).to_iff.trans (hQA K a))))
  exact Cardinal.mk_le_of_injective hF

/-- A sublattice inherits countability of the proper prime spectrum. -/
lemma countable_spectrum_sublattice {B : Type*}
    [AddCommGroup B] [Lattice B] [IsOrderedAddMonoid B] [VectorLattice B]
    (A : VectorSublattice B) (hB : (properPrimeIdeals B).Countable) :
    (properPrimeIdeals A).Countable := by
  exact Cardinal.le_aleph0_iff_set_countable.mp ((spectrum_cardinal_sublattice A).trans
    (Cardinal.le_aleph0_iff_set_countable.mpr hB))

/-- A lattice embedding cannot decrease the size of the proper prime spectrum. -/
theorem spectrum_cardinal_le_of_injective {X Y : Type u}
    [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X]
    [AddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [VectorLattice Y]
    (f : VecLatHom X Y) (hf : Function.Injective f) :
    Cardinal.mk ↥(properPrimeIdeals X) ≤ Cardinal.mk ↥(properPrimeIdeals Y) := by
  let D := VectorSublattice.ofAbsClosed f.toLinearMap.range
    (fun y ⟨x, hx⟩ ↦ ⟨|x|, (f.map_abs x).trans (congrArg abs hx)⟩)
  let e : VecLatEquiv X D :=
    { LinearEquiv.ofInjective f.toLinearMap hf with
      map_sup' := fun x y ↦ Subtype.ext (f.map_sup' x y)
      map_inf' := fun x y ↦ Subtype.ext (f.map_inf' x y) }
  exact (spectrum_cardinal_le_of_surjective e.symm.toVecLatHom
    e.toLinearEquiv.symm.surjective).trans (spectrum_cardinal_sublattice D)

/-- A lattice embedding transfers countability of the spectrum to its domain. -/
lemma countable_spectrum_of_injective {X Y : Type*}
    [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X]
    [AddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [VectorLattice Y]
    (f : VecLatHom X Y) (hf : Function.Injective f) (hY : (properPrimeIdeals Y).Countable) :
    (properPrimeIdeals X).Countable := by
  let D := VectorSublattice.ofAbsClosed f.toLinearMap.range
    (fun y ⟨x, hx⟩ ↦ ⟨|x|, (f.map_abs x).trans (congrArg abs hx)⟩)
  let e : VecLatEquiv X D :=
    { LinearEquiv.ofInjective f.toLinearMap hf with
      map_sup' := fun x y ↦ Subtype.ext (f.map_sup' x y)
      map_inf' := fun x y ↦ Subtype.ext (f.map_inf' x y) }
  exact countable_spectrum_of_surjective e.symm.toVecLatHom e.toLinearEquiv.symm.surjective
    (countable_spectrum_sublattice D hY)

/-- Lattice equivalences preserve countability of the proper prime spectrum. -/
lemma countable_spectrum_of_equiv {X Y : Type*}
    [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X]
    [AddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [VectorLattice Y]
    (e : VecLatEquiv X Y) (hY : (properPrimeIdeals Y).Countable) :
    (properPrimeIdeals X).Countable := by
  let F (J : properPrimeIdeals X) : properPrimeIdeals Y :=
    ⟨idealPreimage e.symm.toVecLatHom J.val, idealPreimage_properPrime e.symm J.val J.property⟩
  have hF : Function.Injective F := fun J K h ↦ Subtype.ext
    (idealPreimage_injective e.symm.toVecLatHom e.toLinearEquiv.symm.surjective
      (congrArg Subtype.val h))
  let := hY.to_subtype
  exact hF.countable

section CountableCuts

variable {V : Type*} [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V]
  [VectorLattice V]

/-- The ideal consisting of zero and the vectors whose Archimedean class is strictly above the
chosen finite class. -/
private def classIdeal (c : FiniteArchimedeanClass V) : OrderIdeal V :=
  OrderIdeal.ofSolid (FiniteArchimedeanClass.ball ℝ c) (by
    intro x y hx hy
    rw [FiniteArchimedeanClass.mem_ball_iff] at hx ⊢
    intro hy0
    have hx0 : x ≠ 0 := abs_pos.mp ((abs_pos.mpr hy0).trans_le hy)
    exact (hx hx0).trans_le (ArchimedeanClass.mk_le_mk_of_abs hy))

/-- The ideal associated with a finite Archimedean class is proper and prime. -/
private lemma classIdeal_properPrime (c : FiniteArchimedeanClass V) :
    classIdeal c ∈ properPrimeIdeals V := by
  refine ⟨?_, ?_⟩
  · induction c using FiniteArchimedeanClass.ind with
    | mk a ha =>
      intro ht
      have hm : a ∈ FiniteArchimedeanClass.ball ℝ (FiniteArchimedeanClass.mk a ha) :=
        show a ∈ classIdeal (FiniteArchimedeanClass.mk a ha) from ht ▸ OrderIdeal.mem_top
      exact lt_irrefl _ ((FiniteArchimedeanClass.mem_ball_iff ℝ).mp hm ha)
  · intro a b hab
    exact (min_choice a b).elim
      (fun h ↦ Or.inl ((h.symm.trans hab).symm ▸ (classIdeal c).zero_mem))
      (fun h ↦ Or.inr ((h.symm.trans hab).symm ▸ (classIdeal c).zero_mem))

/-- Distinct finite Archimedean classes determine distinct ideals. -/
private lemma classIdeal_injective : Function.Injective (classIdeal (V := V)) := by
  exact fun a b h ↦ (FiniteArchimedeanClass.ball_strictAnti ℝ).injective
    (congrArg (fun J : OrderIdeal V ↦ J.toSubmodule) h)

/-- The nonzero Archimedean classes inject into the proper prime spectrum of a chain. -/
theorem archimedeanClasses_cardinal_le_spectrum :
    Cardinal.mk (FiniteArchimedeanClass V) ≤ Cardinal.mk ↥(properPrimeIdeals V) := by
  exact Cardinal.mk_le_of_injective
    (f := fun c ↦ (⟨classIdeal c, classIdeal_properPrime c⟩ : properPrimeIdeals V))
    (fun _ _ h ↦ classIdeal_injective (congrArg Subtype.val h))

/-- Countable prime spectrum gives countably many Archimedean classes in a chain. -/
theorem countable_classes_of_countable_spectrum
    (hV : (properPrimeIdeals V).Countable) : Countable (ArchimedeanClass V) := by
  let := hV.to_subtype
  have hinj : Function.Injective (fun c : FiniteArchimedeanClass V ↦
      (⟨classIdeal c, classIdeal_properPrime c⟩ : properPrimeIdeals V)) := by
    intro a b h
    exact classIdeal_injective (congrArg Subtype.val h)
  let : Countable (FiniteArchimedeanClass V) := hinj.countable
  exact (FiniteArchimedeanClass.withTopOrderIso V).symm.injective.countable

attribute [local instance] PosSMulMono.toPosSMulStrictMono

/-- The real scalars whose multiples of a positive vector lie below the given vector form a
nonempty set bounded above, under the stated comparison of classes. -/
private lemma scalar_cut_bounded {u w : V} (hu : 0 < u)
    (huw : ArchimedeanClass.mk u ≤ ArchimedeanClass.mk w) :
    {s : ℝ | s • u ≤ w}.Nonempty ∧ BddAbove {s : ℝ | s • u ≤ w} := by
  obtain ⟨n, hn⟩ := ArchimedeanClass.mk_le_mk.mp huw
  have hn' : |w| ≤ (n : ℝ) • u := by
    simpa only [abs_of_pos hu, Nat.cast_smul_eq_nsmul] using hn
  exact ⟨⟨-(n : ℝ), by simpa only [Set.mem_ofPred_eq, neg_smul] using
    (neg_le_neg hn').trans (neg_abs_le w)⟩,
    ⟨n, fun s hs ↦ le_of_smul_le_smul_right ((hs.trans (le_abs_self w)).trans hn') hu⟩⟩

/-- Approximate the scalar cut of a vector by a real coefficient, with arbitrarily small
errors measured against a positive vector. -/
private lemma scalar_cut_approximation {u w : V} (hu : 0 < u)
    (huw : ArchimedeanClass.mk u ≤ ArchimedeanClass.mk w) :
    ∃ a : ℝ, ∀ ε > 0, (a - ε) • u < w ∧ w < (a + ε) • u := by
  obtain ⟨hne, hbdd⟩ := scalar_cut_bounded hu huw
  refine ⟨sSup {s : ℝ | s • u ≤ w}, fun ε hε ↦ ⟨?_, ?_⟩⟩
  · obtain ⟨s, hs, hsa⟩ := exists_lt_of_lt_csSup hne (sub_lt_self _ hε)
    exact (smul_lt_smul_of_pos_right hsa hu).trans_le hs
  · exact lt_of_not_ge (fun h ↦ (not_le_of_gt (lt_add_of_pos_right _ hε))
      (le_csSup hbdd h))

/-- Subtracting a suitable scalar multiple of a positive vector leaves a remainder smaller in
absolute value than every positive multiple of that vector. -/
private lemma scalar_remainder_small {u w : V} (hu : 0 < u)
    (huw : ArchimedeanClass.mk u ≤ ArchimedeanClass.mk w) :
    ∃ a : ℝ, ∀ ε : ℝ, 0 < ε → |w - a • u| < ε • u := by
  obtain ⟨a, ha⟩ := scalar_cut_approximation hu huw
  refine ⟨a, fun ε hε ↦ abs_lt.mpr ⟨?_, ?_⟩⟩
  · exact lt_sub_iff_add_lt.mpr (by
      simpa only [sub_smul, sub_eq_add_neg, add_smul, neg_smul, add_comm] using (ha ε hε).1)
  · exact sub_lt_iff_lt_add.mpr (by simpa only [add_smul, add_comm] using (ha ε hε).2)

/-- A vector smaller in absolute value than every positive multiple of a positive vector has
strictly higher Archimedean class. -/
private lemma class_lt_of_small {u v : V} (hu : 0 < u)
    (h : ∀ ε : ℝ, 0 < ε → |v| < ε • u) :
    ArchimedeanClass.mk u < ArchimedeanClass.mk v := by
  refine ArchimedeanClass.mk_lt_mk.mpr (fun n ↦ ?_)
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hs := smul_lt_smul_of_pos_left (h ((n : ℝ) + 1)⁻¹ (inv_pos.mpr hn)) hn
  calc
    n • |v| ≤ ((n : ℝ) + 1) • |v| := by
      simpa only [add_smul, one_smul, Nat.cast_smul_eq_nsmul] using
        (le_add_of_nonneg_right (abs_nonneg v) : n • |v| ≤ n • |v| + |v|)
    _ < |u| := by simpa only [smul_inv_smul₀ hn.ne', abs_of_pos hu] using hs

/-- Subtract a suitable scalar multiple of a positive vector so that the remainder has
strictly higher Archimedean class than that positive vector. -/
lemma exists_scalar_remainder_higher_class {u w : V} (hu : 0 < u)
    (huw : ArchimedeanClass.mk u ≤ ArchimedeanClass.mk w) :
    ∃ a : ℝ, ArchimedeanClass.mk u < ArchimedeanClass.mk (w - a • u) := by
  obtain ⟨a, ha⟩ := scalar_remainder_small hu huw
  exact ⟨a, class_lt_of_small hu ha⟩

/-- For each finite Archimedean class, choose a linear functional that is nonzero on every
vector in that class. -/
private lemma exists_class_functional (c : FiniteArchimedeanClass V) :
    ∃ f : V →ₗ[ℝ] ℝ, ∀ x : V, ArchimedeanClass.mk x = c.val → f x ≠ 0 := by
  induction c using FiniteArchimedeanClass.ind with
  | mk u hu =>
    have hnot : |u| ∉ FiniteArchimedeanClass.ball ℝ (FiniteArchimedeanClass.mk u hu) :=
      fun h ↦ (not_lt_of_ge (ArchimedeanClass.mk_abs u).le)
        (show ArchimedeanClass.mk u < ArchimedeanClass.mk |u| from
          (FiniteArchimedeanClass.mem_ball_iff ℝ).mp h (abs_pos.mpr hu).ne')
    obtain ⟨f, hfu, hker⟩ := Submodule.exists_le_ker_of_notMem hnot
    refine ⟨f, fun x hx hzero ↦ ?_⟩
    obtain ⟨a, ha⟩ := exists_scalar_remainder_higher_class (abs_pos.mpr hu)
      ((ArchimedeanClass.mk_abs u).trans hx.symm).le
    have hrem : f (x - a • |u|) = 0 := hker
      ((FiniteArchimedeanClass.mem_ball_iff ℝ).mpr
        (fun _ ↦ (ArchimedeanClass.mk_abs u).symm.trans_lt ha))
    have ha0 : a = 0 := by
      simpa only [map_sub, map_smul, hzero, zero_sub, neg_eq_zero, smul_eq_mul,
        mul_eq_zero, hfu, or_false] using hrem
    simp only [ha0, zero_smul, sub_zero, ArchimedeanClass.mk_abs, hx,
      FiniteArchimedeanClass.val_mk, lt_self_iff_false] at ha

/-- The functionals associated with finite Archimedean classes give an injective linear map
into a space of real-valued functions. -/
private lemma exists_class_coordinates :
    ∃ F : V →ₗ[ℝ] (FiniteArchimedeanClass V → ℝ), Function.Injective F := by
  choose f hf using exists_class_functional (V := V)
  exact ⟨LinearMap.pi f, (injective_iff_map_eq_zero (LinearMap.pi f)).mpr
    (fun x hx ↦ Classical.byContradiction (fun hne ↦
      hf (FiniteArchimedeanClass.mk x hne) x rfl (congrFun hx _)))⟩

/-- A totally ordered real vector space has size at most continuum to the number of its classes. -/
theorem cardinal_le_power_archimedeanClasses :
    Cardinal.mk V ≤ Cardinal.continuum ^ Cardinal.mk (FiniteArchimedeanClass V) := by
  obtain ⟨F, hF⟩ := exists_class_coordinates (V := V)
  simpa only [Cardinal.mk_arrow, Cardinal.mk_real, Cardinal.lift_continuum,
    Cardinal.lift_id'] using Cardinal.mk_le_of_injective hF

/-- A totally ordered vector lattice with countably many proper prime ideals has cardinality
at most the continuum. -/
private lemma chain_cardinal_le_continuum (hV : (properPrimeIdeals V).Countable) :
    Cardinal.mk V ≤ Cardinal.continuum := by
  exact (cardinal_le_power_archimedeanClasses (V := V)).trans
    ((Cardinal.power_le_power_left Cardinal.continuum_ne_zero
      ((archimedeanClasses_cardinal_le_spectrum (V := V)).trans
      (Cardinal.le_aleph0_iff_set_countable.mpr hV))).trans_eq
        Cardinal.continuum_power_aleph0)

end CountableCuts

section Cardinality

variable {X : Type u} [AddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [VectorLattice X]

/-- A quotient by a proper prime ideal of a lattice with countable spectrum has cardinality at
most the continuum. -/
private lemma prime_quotient_cardinal_le_continuum
    (hX : (properPrimeIdeals X).Countable) (J : properPrimeIdeals X) :
    Cardinal.mk (X ⧸ J.val.toSubmodule) ≤ Cardinal.continuum := by
  classical
  let := (OrderIdeal.isTotal_quotient_iff_isPrime J.val).mpr J.property.2
  let := Lattice.toLinearOrder (X ⧸ J.val.toSubmodule)
  exact chain_cardinal_le_continuum (countable_spectrum_of_surjective
    J.val.mkQVecLatHom J.val.toSubmodule.mkQ_surjective hX)

/-- For every nonzero vector, a sublattice containing its absolute value admits a real-valued
lattice homomorphism that takes that absolute value to one. -/
private lemma exists_sublattice_character {x : X} (hx : x ≠ 0) :
    ∃ (D : VectorSublattice X) (φ : VecLatHom D ℝ) (y : D), y.val = |x| ∧ φ y = 1 := by
  let T : VecLatHom ℝ X :=
    { toLinearMap := (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight |x|
      map_sup' := fun a b ↦ sup_smul_nonneg |x| a b (abs_nonneg x)
      map_inf' := fun a b ↦ inf_smul_nonneg |x| a b (abs_nonneg x) }
  let D := VectorSublattice.ofAbsClosed T.toLinearMap.range
    (fun y ⟨a, ha⟩ ↦ ⟨|a|, (T.map_abs a).trans (congrArg abs ha)⟩)
  let e : VecLatEquiv ℝ D :=
    { LinearEquiv.ofInjective T.toLinearMap
        (smul_left_injective ℝ ((abs_eq_zero_iff_zero x).not.mpr hx)) with
      map_sup' := fun a b ↦ Subtype.ext (T.map_sup' a b)
      map_inf' := fun a b ↦ Subtype.ext (T.map_inf' a b) }
  exact ⟨D, e.symm.toVecLatHom, e 1, one_smul ℝ |x|,
    e.toLinearEquiv.symm_apply_apply 1⟩

/-- Every nonzero vector is omitted by some proper prime ideal. -/
private lemma exists_proper_prime_not_mem {x : X} (hx : x ≠ 0) :
    ∃ J : properPrimeIdeals X, x ∉ J.val := by
  obtain ⟨D, φ, y, hy, hφ⟩ := exists_sublattice_character hx
  obtain ⟨J, hJ, hJD⟩ := proper_prime_extension D
    ⟨OrderIdeal.ofKerVecLatHom φ, normalized_character_kernel_prime φ y hφ⟩
  exact ⟨⟨J, hJ⟩, fun hxJ ↦ one_ne_zero (hφ.symm.trans
    (show φ y = 0 from (hJD y).mp (hy.symm ▸ J.abs_mem hxJ)))⟩

/-- The canonical map into the product of all proper prime quotients is injective. -/
private lemma prime_quotient_family_injective :
    Function.Injective (fun x : X ↦ fun J : properPrimeIdeals X ↦ J.val.mkQ x) := by
  exact fun x y h ↦ sub_eq_zero.mp (Classical.byContradiction (fun hne ↦
    (exists_proper_prime_not_mem hne).elim (fun J hJ ↦
      hJ ((Submodule.Quotient.mk_eq_zero J.val.toSubmodule).mp
        ((map_sub J.val.mkQ x y).trans (sub_eq_zero.mpr (congrFun h J)))))))

/-- A real vector lattice with countable proper prime spectrum has size at most continuum. -/
theorem cardinal_le_continuum (hX : (properPrimeIdeals X).Countable) :
    Cardinal.mk X ≤ Cardinal.continuum := by
  calc
    Cardinal.mk X ≤ Cardinal.mk (∀ J : properPrimeIdeals X, X ⧸ J.val.toSubmodule) :=
      Cardinal.mk_le_of_injective prime_quotient_family_injective
    _ = Cardinal.prod (fun J : properPrimeIdeals X ↦ Cardinal.mk (X ⧸ J.val.toSubmodule)) :=
      Cardinal.mk_pi _
    _ ≤ Cardinal.prod (fun _ : properPrimeIdeals X ↦ Cardinal.continuum) :=
      Cardinal.prod_le_prod _ _ (prime_quotient_cardinal_le_continuum hX)
    _ = Cardinal.continuum ^ Cardinal.mk ↥(properPrimeIdeals X) := Cardinal.prod_const' _ _
    _ ≤ Cardinal.continuum :=
      (Cardinal.power_le_power_left Cardinal.continuum_ne_zero
        (Cardinal.le_aleph0_iff_set_countable.mpr hX)).trans_eq Cardinal.continuum_power_aleph0

/-- Generating an ideal in an ambient lattice introduces no new elements in the sublattice. -/
theorem mem_generated_ideal_iff (Y : VectorSublattice X) (J : OrderIdeal Y) (y : Y) :
    y.val ∈ OrderIdeal.generated (Subtype.val '' (J : Set Y)) ↔ y ∈ J := by
  refine ⟨fun hy ↦ ?_, fun hy ↦ OrderIdeal.subset_generated _ ⟨y, hy, rfl⟩⟩
  obtain ⟨t, c, ht, _, hle⟩ := OrderIdeal.mem_generated_iff.mp hy
  have hs : ∑ x ∈ t, c x • |x| ∈ J.toSubmodule.map Y.toSubmodule.subtype :=
    Submodule.sum_mem _ (fun x hx ↦ (ht x hx).elim (fun p hp ↦ hp.2 ▸
      ⟨c p.val • |p|, J.smul_mem _ (J.abs_mem hp.1), rfl⟩))
  exact hs.elim (fun p hp ↦ J.mem_of_abs_mem (J.solid hp.1 (abs_nonneg y)
    (show |y.val| ≤ p.val from hle.trans_eq hp.2.symm)))

end Cardinality

/-- Extending an embedding of the zero sublattice gives an embedding of the lattice. -/
lemma embedding_of_extension_from_bot {X Y : Type*}
    [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X]
    [AddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [VectorLattice Y]
    (h : ∀ T : VecLatHom (⊥ : VectorSublattice X) Y, Function.Injective T →
      ∃ S : VecLatHom X Y, Function.Injective S ∧ ∀ a, S a.val = T a) :
    ∃ S : VecLatHom X Y, Function.Injective S := by
  let T : VecLatHom (⊥ : VectorSublattice X) Y :=
    { toLinearMap := 0
      map_sup' := fun _ _ ↦ (sup_idem (0 : Y)).symm
      map_inf' := fun _ _ ↦ (inf_idem (0 : Y)).symm }
  obtain ⟨S, hS, -⟩ := h T (fun a b _ ↦ Subtype.ext
    ((VectorSublattice.mem_bot.mp a.property).trans
      (VectorSublattice.mem_bot.mp b.property).symm))
  exact ⟨S, hS⟩

/-- Every nonzero real vector lattice has cardinality at least continuum. -/
theorem continuum_le_cardinal_of_nontrivial (Z : Type u)
    [AddCommGroup Z] [Lattice Z] [IsOrderedAddMonoid Z] [VectorLattice Z] [Nontrivial Z] :
    Cardinal.continuum ≤ Cardinal.mk Z := by
  obtain ⟨z, hz⟩ := exists_ne (0 : Z)
  have hinj : Function.Injective (fun r : ULift.{u} ℝ ↦ r.down • z) :=
    (smul_left_injective ℝ hz).comp ULift.down_injective
  simpa only [Cardinal.mk_uLift, Cardinal.mk_real, Cardinal.lift_continuum] using
    Cardinal.mk_le_of_injective hinj

/-- The number of proper prime ideals is at most the cardinality of the powerset of the
lattice. -/
lemma spectrum_cardinal_le_powerset (X : Type u) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] :
    Cardinal.mk (properPrimeIdeals X) ≤ 2 ^ Cardinal.mk X := by
  have hi : Function.Injective (fun J : properPrimeIdeals X ↦ (J.val : Set X)) :=
    fun _ _ h ↦ Subtype.ext (SetLike.coe_injective h)
  simpa only [Cardinal.mk_set] using Cardinal.mk_le_of_injective hi

end VectorLattice.CountableSpectra
