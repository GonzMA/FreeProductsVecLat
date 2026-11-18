/-
Authors: Gonzalo Martínez-Fernández
-/

import FreeProducts.CountableSpectra.OrderedExtension
import Mathlib.Algebra.Order.Group.PiLex
import Mathlib.Algebra.Order.Module.Synonym

/-!
# Colexicographic lattices and their spectra

Finitely supported real functions with the colexicographic order provide explicit
models of prime spectra. Countably indexed models embed in relatively injective
lattices, and ideals of well-ordered models are classified by cuts of the index set.
-/

noncomputable section

universe u v w

namespace VectorLattice.CountableSpectra

/-- Finitely supported real functions form a vector lattice in reverse lexicographic order. -/
instance colexFinsuppVectorLattice (ι : Type*) [LinearOrder ι] :
    VectorLattice (Lex (ιᵒᵈ →₀ ℝ)) where
  toModule := inferInstance
  smul_le_smul_of_nonneg_left := by
    intro a ha x y hxy
    rcases ha.eq_or_lt with rfl | ha
    · simp only [zero_smul, le_refl]
    · rcases hxy with hxy | ⟨i, hi, hlt⟩
      · exact (congrArg (fun z : ιᵒᵈ →₀ ℝ ↦ a • toLex z)
          (DFunLike.coe_injective hxy)).le
      · exact Or.inr ⟨i, fun j hj ↦ congrArg (a * ·) (hi j hj),
          mul_lt_mul_of_pos_left hlt ha⟩

/-- A positive colexicographic vector with a nonzero coordinate at or above a chosen index
dominates that coordinate unit up to a scalar factor. -/
private lemma colex_single_dominated {ι : Type*} [LinearOrder ι]
    (k : ι) {x : Lex (ιᵒᵈ →₀ ℝ)} (hx : 0 < x)
    (hk : ∃ j : ι, k ≤ j ∧ (ofLex x) j ≠ 0) :
    ∃ r : ℝ, (toLex (Finsupp.single k 1) : Lex (ιᵒᵈ →₀ ℝ)) ≤ r • x := by
  obtain ⟨i, hi, hxi⟩ := hx
  have hki : k ≤ (i : ι) := by
    obtain ⟨j, hkj, hj⟩ := hk
    exact hkj.trans (le_of_not_gt (fun hij ↦ hj (hi j hij).symm))
  refine ⟨2 / (ofLex x) i, Or.inr ⟨i, ?_, ?_⟩⟩
  · intro j hj
    change Finsupp.single k (1 : ℝ) (OrderDual.ofDual j) = (2 / (ofLex x) i) * (ofLex x) j
    have hkj : k < OrderDual.ofDual j := lt_of_le_of_lt hki hj
    simp [hkj.ne, ← hi j hj]
  · change Finsupp.single k (1 : ℝ) (OrderDual.ofDual i) < (2 / (ofLex x) i) * (ofLex x) i
    norm_num only [div_mul_cancel₀ _ (ne_of_gt hxi), Finsupp.single_apply]
    split_ifs <;> norm_num

/-- Every positive colexicographic vector dominates the bottom coordinate unit up to a scalar
factor. -/
private lemma colex_bot_dominated {ι : Type*} [LinearOrder ι] [OrderBot ι]
    {x : Lex (ιᵒᵈ →₀ ℝ)} (hx : 0 < x) :
    ∃ r : ℝ, (toLex (Finsupp.single (⊥ : ι) 1) : Lex (ιᵒᵈ →₀ ℝ)) ≤ r • x := by
  exact colex_single_dominated ⊥ hx
    (hx.elim (fun i hi ↦ ⟨i, bot_le, hi.2.ne'⟩))

/-- A homomorphism on a colexicographic sublattice containing the bottom coordinate unit is
injective if it sends that unit to a positive vector. -/
lemma colex_stage_map_injective {ι Z : Type*} [LinearOrder ι] [OrderBot ι]
    [AddCommGroup Z] [Lattice Z] [IsOrderedAddMonoid Z] [VectorLattice Z]
    (D : VectorSublattice (Lex (ιᵒᵈ →₀ ℝ)))
    (hb : toLex (Finsupp.single (⊥ : ι) 1) ∈ D)
    (T : VecLatHom D Z) (hT : 0 < T ⟨toLex (Finsupp.single (⊥ : ι) 1), hb⟩) :
    Function.Injective T := by
  refine (injective_iff_map_eq_zero T.toLinearMap).mpr (fun x hx ↦ ?_)
  by_contra hne
  obtain ⟨r, hr⟩ := colex_bot_dominated (abs_pos.mpr
    (show x.val ≠ 0 from fun h ↦ hne (Subtype.ext h)))
  apply hT.not_ge
  change T x = 0 at hx
  simpa only [map_smul, T.map_abs, hx, abs_zero, smul_zero] using
    T.monotone (show (⟨toLex (Finsupp.single (⊥ : ι) 1), hb⟩ : D) ≤ r • |x| from hr)

/-- Relative injectivity for countable spectra extends a lattice homomorphism along an
arbitrary embedding into a lattice with countable spectrum. -/
lemma countable_injective_extend_map {X : Type*} {Y Z : Type u}
    [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X]
    [AddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [VectorLattice Y]
    [AddCommGroup Z] [Lattice Z] [IsOrderedAddMonoid Z] [VectorLattice Z]
    (hZ : IsCountablePrimeInjective Z) (hY : (properPrimeIdeals Y).Countable)
    (f : VecLatHom X Y) (hf : Function.Injective f) (T : VecLatHom X Z) :
    ∃ S : VecLatHom Y Z, ∀ x, S (f x) = T x := by
  let D := VectorSublattice.ofAbsClosed f.toLinearMap.range
    (fun y ⟨x, hx⟩ ↦ ⟨|x|, (f.map_abs x).trans (congrArg abs hx)⟩)
  let e : VecLatEquiv X D :=
    { LinearEquiv.ofInjective f.toLinearMap hf with
      map_sup' := fun x y ↦ Subtype.ext (f.map_sup' x y)
      map_inf' := fun x y ↦ Subtype.ext (f.map_inf' x y) }
  obtain ⟨S, hS⟩ := hZ Y hY D (T.comp e.symm.toVecLatHom)
  exact ⟨S, fun x ↦ (hS (e x)).trans
    (congrArg T (e.toLinearEquiv.symm_apply_apply x))⟩

/-- The finite colexicographic stage supported on the bottom index and an initial finite list
of indices. -/
def colexStage {ι : Type*} [LinearOrder ι] [OrderBot ι] (e : ℕ → ι) (n : ℕ) :
    VectorSublattice (Lex (ιᵒᵈ →₀ ℝ)) :=
  submoduleSublattice (Finsupp.supported ℝ ℝ (insert (⊥ : ι) (e '' Set.Iio n)))

/-- The finite colexicographic stages increase as the list of allowed indices grows. -/
private lemma colexStage_mono {ι : Type*} [LinearOrder ι] [OrderBot ι] (e : ℕ → ι) :
    Monotone (colexStage e) := by
  exact fun m n hmn x hx ↦ hx.trans
    (Set.insert_subset_insert (Set.image_mono (Set.Iio_subset_Iio hmn)))

/-- Each finite colexicographic stage is finite dimensional. -/
private instance colexStage_finiteDimensional {ι : Type*} [LinearOrder ι] [OrderBot ι]
    (e : ℕ → ι) (n : ℕ) : FiniteDimensional ℝ (colexStage e n) := by
  have hs : (insert (⊥ : ι) (e '' Set.Iio n)).Finite :=
    ((Set.finite_Iio n).image e).insert _
  let := hs.to_subtype
  exact (Finsupp.supportedEquivFinsupp (R := ℝ) (M := ℝ)
    (insert (⊥ : ι) (e '' Set.Iio n))).symm.finiteDimensional

/-- A surjective enumeration of the indices makes the finite stages cover the whole
colexicographic lattice. -/
private lemma colexStage_cover {ι : Type*} [LinearOrder ι] [OrderBot ι]
    (e : ℕ → ι) (he : Function.Surjective e) (x : Lex (ιᵒᵈ →₀ ℝ)) :
    ∃ n, x ∈ colexStage e n := by
  classical
  let k (i : ι) : ℕ := (he i).choose
  refine ⟨(ofLex x).support.sup (fun i ↦ k i + 1), fun i hi ↦
    Or.inr ⟨k i, ?_, (he i).choose_spec⟩⟩
  exact (Nat.lt_succ_self (k i)).trans_le (Finset.le_sup (f := fun i ↦ k i + 1) hi)

/-- Every finite stage contains the bottom coordinate unit. -/
lemma colexStage_bot_mem {ι : Type*} [LinearOrder ι] [OrderBot ι]
    (e : ℕ → ι) (n : ℕ) : toLex (Finsupp.single (⊥ : ι) 1) ∈ colexStage e n :=
  Finsupp.single_mem_supported ℝ 1 (Set.mem_insert _ _)

/-- A nonnegative vector in the initial stage has a nonnegative bottom coordinate. -/
private lemma colexStage_zero_coeff_nonneg {ι : Type*} [LinearOrder ι] [OrderBot ι]
    (e : ℕ → ι) (x : colexStage e 0) (hx : 0 ≤ x) : 0 ≤ (ofLex x.val) (⊥ : ι) := by
  by_contra hneg
  have hs : ∀ i : ι, i ≠ ⊥ → (ofLex x.val) i = 0 := by
    exact fun i hi ↦ (Finsupp.mem_supported' ℝ (ofLex x.val)).mp x.property i
      (by
        change i ∉ (insert (⊥ : ι) (e '' Set.Iio 0) : Set ι)
        simpa using hi)
  exact hx.not_gt ⟨(⊥ : ι), fun j hj ↦ hs j (show (⊥ : ι) < j from hj).ne',
    lt_of_not_ge hneg⟩

/-- The homomorphism from the initial one-dimensional stage sending its coordinate unit to the
prescribed nonnegative vector. -/
lemma colexStage_initial_map {ι Z : Type*} [LinearOrder ι] [OrderBot ι]
    [AddCommGroup Z] [Lattice Z] [IsOrderedAddMonoid Z] [VectorLattice Z]
    (e : ℕ → ι) (z : Z) (hz : 0 ≤ z) :
    ∃ T : VecLatHom (colexStage e 0) Z,
      T ⟨toLex (Finsupp.single (⊥ : ι) 1), colexStage_bot_mem e 0⟩ = z := by
  let L : colexStage e 0 →ₗ[ℝ] ℝ :=
    (Finsupp.lapply (R := ℝ) (M := ℝ) (⊥ : ι)).domRestrict (colexStage e 0).toSubmodule
  let G := L.smulRight z
  have hG : Monotone G := (monotone_iff_map_nonneg G).mpr
    (fun x hx ↦ smul_nonneg (colexStage_zero_coeff_nonneg e x hx) hz)
  refine ⟨{ toLinearMap := G
            map_sup' := hG.map_sup
            map_inf' := hG.map_inf }, ?_⟩
  change Finsupp.single (⊥ : ι) (1 : ℝ) (⊥ : ι) • z = z
  simp only [Finsupp.single_eq_same, one_smul]

/-- Any two ideals in a totally ordered vector lattice are comparable by inclusion. -/
private lemma ordered_ideals_le_total {V : Type*}
    [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [VectorLattice V]
    (J K : OrderIdeal V) : J ≤ K ∨ K ≤ J := by
  by_cases h : J ≤ K
  · exact Or.inl h
  · obtain ⟨x, hx, hxK⟩ := Set.not_subset.mp h
    refine Or.inr (fun y hy ↦ ?_)
    exact (le_total |y| |x|).elim (J.mem_of_abs_le_abs hx)
      (fun hxy ↦ (hxK (K.mem_of_abs_le_abs hy hxy)).elim)

/-- A finite-dimensional totally ordered vector lattice has countable spectrum. -/
lemma finiteDimensional_ordered_countable_spectrum {V : Type*}
    [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [VectorLattice V]
    [FiniteDimensional ℝ V] : (properPrimeIdeals V).Countable := by
  have hinj : Function.Injective (fun J : OrderIdeal V ↦ Module.finrank ℝ J.toSubmodule) :=
    fun J K h ↦ OrderIdeal.toSubmodule_injective ((ordered_ideals_le_total J K).elim
      (fun hJK ↦ Submodule.eq_of_le_of_finrank_eq hJK h)
      (fun hKJ ↦ (Submodule.eq_of_le_of_finrank_eq hKJ h.symm).symm))
  let : Countable (OrderIdeal V) := hinj.countable
  exact Set.to_countable _

/-- Extend an initial homomorphism along an increasing sequence of sublattices with countable
spectra, keeping all stage maps compatible. -/
private lemma compatible_stage_maps {V Z : Type u}
    [AddCommGroup V] [Lattice V] [IsOrderedAddMonoid V] [VectorLattice V]
    [AddCommGroup Z] [Lattice Z] [IsOrderedAddMonoid Z] [VectorLattice Z]
    (hZ : IsCountablePrimeInjective Z) (D : ℕ → VectorSublattice V) (hD : Monotone D)
    (hDc : ∀ n, (properPrimeIdeals (D n)).Countable) (T₀ : VecLatHom (D 0) Z) :
    ∃ T : ∀ n, VecLatHom (D n) Z, T 0 = T₀ ∧
      ∀ n x, T (n + 1) (VectorSublattice.inclusion (hD (Nat.le_succ n)) x) = T n x := by
  have hex (n : ℕ) (T : VecLatHom (D n) Z) :=
    countable_injective_extend_map hZ (hDc (n + 1))
      (VectorSublattice.inclusion (hD (Nat.le_succ n)))
      (VectorSublattice.inclusion_injective _) T
  let T : ∀ n, VecLatHom (D n) Z := Nat.rec T₀ (fun n T ↦ (hex n T).choose)
  exact ⟨T, rfl, fun n ↦ (hex n (T n)).choose_spec⟩

/-- Compatible injective homomorphisms on an increasing cover of a totally ordered vector
lattice combine into one embedding. -/
private lemma ordered_stage_union {V Z : Type*}
    [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V] [VectorLattice V]
    [AddCommGroup Z] [Lattice Z] [IsOrderedAddMonoid Z] [VectorLattice Z]
    (D : ℕ → VectorSublattice V) (hD : Monotone D) (hcover : ∀ x, ∃ n, x ∈ D n)
    (T : ∀ n, VecLatHom (D n) Z) (hTi : ∀ n, Function.Injective (T n))
    (hnext : ∀ n x,
      T (n + 1) (VectorSublattice.inclusion (hD (Nat.le_succ n)) x) = T n x) :
    ∃ S : VecLatHom V Z, Function.Injective S ∧ ∀ n x, S x.val = T n x := by
  let f (n : ℕ) : V →ₗ.[ℝ] Z := ⟨(D n).toSubmodule, (T n).toLinearMap⟩
  have hf : Monotone f := monotone_nat_of_le_succ (fun n ↦
    ⟨hD (Nat.le_succ n), fun {x y} hxy ↦ (hnext n x).symm.trans
      (congrArg (T (n + 1)) (Subtype.ext hxy))⟩)
  have hC : DirectedOn (· ≤ ·) (Set.range f) := hf.directed_le.directedOn_range
  let g := LinearPMap.sSup (Set.range f) hC
  have hmem (x : V) : x ∈ g.domain := (hcover x).elim (fun n hn ↦
    (LinearPMap.le_sSup hC (Set.mem_range_self n)).1 hn)
  have hg : StrictMono g := strictMono_sSup_partial (Set.range f) hC (Set.range_nonempty f)
    (fun _ ⟨n, hn⟩ ↦ hn ▸ (T n).monotone.strictMono_of_injective (hTi n))
  let G := g.toFun.comp ((LinearMap.id : V →ₗ[ℝ] V).codRestrict g.domain hmem)
  have hG : StrictMono G := fun _ _ hxy ↦ hg hxy
  exact ⟨{ toLinearMap := G
           map_sup' := hG.monotone.map_sup
           map_inf' := hG.monotone.map_inf }, hG.injective,
    fun n _ ↦ ((LinearPMap.le_sSup hC (Set.mem_range_self n)).2 rfl).symm⟩

/-- Embed a countably indexed colexicographic lattice into a relatively injective lattice
while prescribing the positive image of the bottom coordinate unit. -/
lemma colex_embeds_countable_injective {ι Z : Type u}
    [LinearOrder ι] [OrderBot ι] [Countable ι]
    [AddCommGroup Z] [Lattice Z] [IsOrderedAddMonoid Z] [VectorLattice Z]
    (hZ : IsCountablePrimeInjective Z) (z : Z) (hz : 0 < z) :
    ∃ S : VecLatHom (Lex (ιᵒᵈ →₀ ℝ)) Z, Function.Injective S ∧
      S (toLex (Finsupp.single (⊥ : ι) 1)) = z := by
  obtain ⟨e, he⟩ := exists_surjective_nat ι
  obtain ⟨T₀, hT₀⟩ := colexStage_initial_map e z hz.le
  obtain ⟨T, hTzero, hnext⟩ := compatible_stage_maps hZ (colexStage e) (colexStage_mono e)
    (fun _ ↦ finiteDimensional_ordered_countable_spectrum) T₀
  have hbot : ∀ n, T n ⟨toLex (Finsupp.single (⊥ : ι) 1), colexStage_bot_mem e n⟩ = z :=
    Nat.rec (hTzero.symm ▸ hT₀) (fun n hn ↦
      (hnext n ⟨toLex (Finsupp.single (⊥ : ι) 1), colexStage_bot_mem e n⟩).trans hn)
  obtain ⟨S, hS, hST⟩ := ordered_stage_union (colexStage e) (colexStage_mono e)
    (colexStage_cover e he) T (fun n ↦ colex_stage_map_injective _
      (colexStage_bot_mem e n) (T n) ((hbot n).symm ▸ hz)) hnext
  exact ⟨S, hS, (hST 0 ⟨_, colexStage_bot_mem e 0⟩).trans (hbot 0)⟩

/-- Vectors supported in a lower set of colexicographic indices form a solid set. -/
lemma colex_supported_solid {ι : Type*} [LinearOrder ι]
    (s : Set ι) (hs : IsLowerSet s) {x y : Lex (ιᵒᵈ →₀ ℝ)}
    (hx : ofLex x ∈ Finsupp.supported ℝ ℝ s) (hy0 : 0 ≤ y) (hyx : y ≤ x) :
    ofLex y ∈ Finsupp.supported ℝ ℝ s := by
  by_contra hy
  obtain ⟨j, hj, hjs⟩ := Set.not_subset.mp hy
  have hne : y ≠ 0 := fun h ↦ hy (h.symm ▸ (Finsupp.supported ℝ ℝ s).zero_mem)
  obtain ⟨i, hi, hip⟩ := lt_of_le_of_ne hy0 hne.symm
  have hji : j ≤ (i : ι) := le_of_not_gt (fun hij ↦
    (Finsupp.mem_support_iff.mp hj) (hi j hij).symm)
  have hxzero (k : ι) (hik : OrderDual.ofDual i ≤ k) : (ofLex x) k = 0 :=
    (Finsupp.mem_supported' ℝ _).mp hx k (fun hk ↦ hjs (hs (hji.trans hik) hk))
  exact hyx.not_gt ⟨i, fun k hk ↦ (hxzero k hk.le).trans (hi k hk),
    (hxzero i le_rfl).trans_lt hip⟩

/-- The ideal of colexicographic vectors supported in a specified lower set of indices. -/
def colexCutIdeal {ι : Type*} [LinearOrder ι] (s : Set ι) (hs : IsLowerSet s) :
    OrderIdeal (Lex (ιᵒᵈ →₀ ℝ)) where
  toVectorSublattice := submoduleSublattice (Finsupp.supported ℝ ℝ s)
  solid' := colex_supported_solid s hs

/-- A coordinate unit belongs to a support ideal exactly when its index belongs to the
defining lower set. -/
lemma colexCutIdeal_single_mem_iff {ι : Type*} [LinearOrder ι]
    (s : Set ι) (hs : IsLowerSet s) (i : ι) :
    toLex (Finsupp.single i 1) ∈ colexCutIdeal s hs ↔ i ∈ s := by
  change Finsupp.single i (1 : ℝ) ∈ Finsupp.supported ℝ ℝ s ↔ i ∈ s
  simp only [Finsupp.mem_supported, Finsupp.support_single _ one_ne_zero,
    Finset.coe_singleton, Set.singleton_subset_iff]

/-- A support ideal is proper and prime when some index lies outside its defining lower set. -/
private lemma colexCutIdeal_properPrime {ι : Type*} [LinearOrder ι]
    (s : Set ι) (hs : IsLowerSet s) (i : ι) (hi : i ∉ s) :
    colexCutIdeal s hs ∈ properPrimeIdeals (Lex (ιᵒᵈ →₀ ℝ)) := by
  refine ⟨?_, ?_⟩
  · exact fun ht ↦ hi ((colexCutIdeal_single_mem_iff s hs i).mp
      (ht.symm ▸ show toLex (Finsupp.single i 1) ∈ (⊤ : OrderIdeal (Lex (ιᵒᵈ →₀ ℝ)))
        from trivial))
  · intro a b hab
    exact (min_choice a b).elim
      (fun h ↦ Or.inl ((h.symm.trans hab).symm ▸ (colexCutIdeal s hs).zero_mem))
      (fun h ↦ Or.inr ((h.symm.trans hab).symm ▸ (colexCutIdeal s hs).zero_mem))

/-- The rational unit interval, lifted to the required universe, used to index a
colexicographic lattice. -/
abbrev rationalInterval := ULift.{u} (Set.Icc (0 : ℚ) 1)

/-- The rational interval has the zero endpoint as its bottom element. -/
private instance rationalIntervalOrderBot : OrderBot rationalInterval where
  bot := ⟨⟨0, le_rfl, zero_le_one⟩⟩
  bot_le x := x.down.property.1

/-- The ideal of colexicographic vectors supported on rational indices strictly below a real
cut. -/
private def rationalCutIdeal (t : ℝ) :
    OrderIdeal (Lex (rationalIntervalᵒᵈ →₀ ℝ)) :=
  colexCutIdeal {i | (i.down.val : ℝ) < t}
    (fun a b hle ht ↦ (show (b.down.val : ℝ) ≤ (a.down.val : ℝ) from
      Rat.cast_le.mpr hle).trans_lt ht)

/-- A coordinate unit belongs to the rational cut ideal exactly when its rational index lies
below the cut. -/
private lemma rationalCutIdeal_single_mem_iff (t : ℝ) (i : rationalInterval) :
    toLex (Finsupp.single i 1) ∈ rationalCutIdeal t ↔ (i.down.val : ℝ) < t :=
  colexCutIdeal_single_mem_iff _ _ i

/-- A rational cut at or below one defines a proper prime ideal. -/
private lemma rationalCutIdeal_properPrime (t : ℝ) (ht : t ≤ 1) :
    rationalCutIdeal t ∈ properPrimeIdeals (Lex (rationalIntervalᵒᵈ →₀ ℝ)) := by
  refine colexCutIdeal_properPrime _ _ ⟨⟨1, zero_le_one, le_rfl⟩⟩ ?_
  simpa only [Set.mem_ofPred_eq, Rat.cast_one] using not_lt_of_ge ht

/-- Increasing the cut strictly within the real unit interval strictly increases the rational
cut ideal. -/
private lemma rationalCutIdeal_strictMono :
    StrictMono (fun t : Set.Ioo (0 : ℝ) 1 ↦ rationalCutIdeal.{u} t.val) := by
  intro s t hst
  refine lt_of_le_not_ge ?_ ?_
  · exact fun x hx i hi ↦ (show (i.down.val : ℝ) < s.val from hx hi).trans hst
  · intro hts
    obtain ⟨q, hsq, hqt⟩ := exists_rat_btwn (show s.val < t.val from hst)
    let i : rationalInterval.{u} := ⟨⟨q,
      by exact_mod_cast (s.property.1.trans hsq).le,
      by exact_mod_cast (hqt.trans t.property.2).le⟩⟩
    exact hsq.not_gt ((rationalCutIdeal_single_mem_iff s.val i).mp
      (hts ((rationalCutIdeal_single_mem_iff t.val i).mpr hqt)))

/-- The colexicographic lattice indexed by the rational interval has at least continuum many
proper prime ideals. -/
lemma rational_colex_spectrum_cardinal :
    Cardinal.continuum ≤
      Cardinal.mk ↥(properPrimeIdeals (Lex (rationalInterval.{u}ᵒᵈ →₀ ℝ))) := by
  let F (t : ULift.{u} (Set.Ioo (0 : ℝ) 1)) :
      properPrimeIdeals (Lex (rationalInterval.{u}ᵒᵈ →₀ ℝ)) :=
    ⟨rationalCutIdeal t.down.val, rationalCutIdeal_properPrime t.down.val t.down.property.2.le⟩
  have hF : Function.Injective F := fun s t h ↦ ULift.ext
    (rationalCutIdeal_strictMono.injective (congrArg Subtype.val h))
  simpa only [Cardinal.mk_uLift, Cardinal.mk_Ioo_real (zero_lt_one : (0 : ℝ) < 1),
    Cardinal.lift_continuum] using Cardinal.mk_le_of_injective hF

/-- Every scalar multiple of a lower coordinate unit lies strictly below a higher coordinate
unit in colexicographic order. -/
lemma colex_smul_single_lt_single {ι : Type*} [LinearOrder ι]
    {i j : ι} (hij : i < j) (r : ℝ) :
    r • (toLex (Finsupp.single i 1) : Lex (ιᵒᵈ →₀ ℝ)) <
      toLex (Finsupp.single j 1) := by
  refine ⟨j, ?_, ?_⟩
  · exact fun k hk ↦ by
      change r * Finsupp.single i (1 : ℝ) (OrderDual.ofDual k) =
        Finsupp.single j (1 : ℝ) (OrderDual.ofDual k)
      have hjk : j < OrderDual.ofDual k := hk
      simp [(hij.trans hjk).ne, hjk.ne]
  · change r * Finsupp.single i (1 : ℝ) j < Finsupp.single j (1 : ℝ) j
    simp [hij.ne]

/-- Every coordinate unit is strictly positive in colexicographic order. -/
lemma colex_single_pos {ι : Type*} [LinearOrder ι] (i : ι) :
    (0 : Lex (ιᵒᵈ →₀ ℝ)) < toLex (Finsupp.single i 1) := by
  refine ⟨i, ?_, ?_⟩
  · exact fun j hj ↦ by
      change 0 = Finsupp.single i (1 : ℝ) (OrderDual.ofDual j)
      simp [(show i < OrderDual.ofDual j from hj).ne]
  · change 0 < Finsupp.single i (1 : ℝ) i
    simp only [Finsupp.single_eq_same, zero_lt_one]

/-- An ideal containing a colexicographic vector contains the coordinate unit at every index
in its support. -/
lemma colex_coordinate_mem {ι : Type*} [LinearOrder ι]
    (J : OrderIdeal (Lex (ιᵒᵈ →₀ ℝ))) {x : Lex (ιᵒᵈ →₀ ℝ)} (hx : x ∈ J)
    (k : ι) (hk : (ofLex x) k ≠ 0) : toLex (Finsupp.single k 1) ∈ J := by
  have hax : (ofLex |x|) k ≠ 0 := by
    rcases le_total 0 x with h | h
    · simpa only [abs_of_nonneg h] using hk
    · rw [abs_of_nonpos h]
      change -((ofLex x) k) ≠ 0
      exact neg_ne_zero.mpr hk
  obtain ⟨r, hr⟩ := colex_single_dominated k
    (abs_pos.mpr (fun h ↦ hk (congrArg (fun y : Lex (ιᵒᵈ →₀ ℝ) ↦ (ofLex y) k) h)))
    ⟨k, le_rfl, hax⟩
  exact J.solid (J.smul_mem r (J.abs_mem hx)) (colex_single_pos k).le hr

/-- If an ideal contains the coordinate units throughout a vector's support, it contains the
vector. -/
lemma colex_mem_of_coordinates {ι : Type*} [LinearOrder ι]
    (J : OrderIdeal (Lex (ιᵒᵈ →₀ ℝ))) (x : Lex (ιᵒᵈ →₀ ℝ))
    (hx : ∀ k : ι, (ofLex x) k ≠ 0 → toLex (Finsupp.single k 1) ∈ J) : x ∈ J := by
  have hsum : x = ∑ k ∈ (ofLex x).support,
      (ofLex x) k • (toLex (Finsupp.single k 1) : Lex (ιᵒᵈ →₀ ℝ)) := by
    change ofLex x = ∑ k ∈ (ofLex x).support, (ofLex x) k • Finsupp.single k 1
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    exact (Finsupp.sum_single (ofLex x)).symm
  exact hsum.symm ▸ J.toSubmodule.sum_mem
    (fun k hk ↦ J.smul_mem _ (hx k (Finsupp.mem_support_iff.mp hk)))

/-- The indices of the coordinate units belonging to a colexicographic ideal form a lower set. -/
lemma colex_coordinates_lower {ι : Type*} [LinearOrder ι]
    (J : OrderIdeal (Lex (ιᵒᵈ →₀ ℝ))) :
    IsLowerSet {k : ι | toLex (Finsupp.single k 1) ∈ J} := by
  intro i j hij hj
  rcases hij.lt_or_eq with hij | rfl
  · refine J.solid hj (colex_single_pos j).le ?_
    have hlt := colex_smul_single_lt_single hij 1
    rw [one_smul] at hlt
    exact Or.inr hlt
  · exact hj

/-- A colexicographic ideal is determined by the coordinate units it contains. -/
private lemma colex_coordinates_injective {ι : Type*} [LinearOrder ι] :
    Function.Injective (fun J : OrderIdeal (Lex (ιᵒᵈ →₀ ℝ)) ↦
      {k : ι | toLex (Finsupp.single k 1) ∈ J}) := by
  intro J K h
  refine SetLike.ext (fun x ↦ ⟨?_, ?_⟩)
  · exact fun hx ↦ colex_mem_of_coordinates K x (fun k hk ↦
      (Set.ext_iff.mp h k).mp (colex_coordinate_mem J hx k hk))
  · exact fun hx ↦ colex_mem_of_coordinates J x (fun k hk ↦
      (Set.ext_iff.mp h k).mpr (colex_coordinate_mem K hx k hk))

/-- A colexicographic lattice on a countable well-ordered index set has countable spectrum. -/
private lemma colex_countable_spectrum (ι : Type*) [LinearOrder ι]
    [WellFoundedLT ι] [Countable ι] : (properPrimeIdeals (Lex (ιᵒᵈ →₀ ℝ))).Countable := by
  let f (J : OrderIdeal (Lex (ιᵒᵈ →₀ ℝ))) : Set ι :=
    {k | toLex (Finsupp.single k 1) ∈ J}
  have hrange : Set.range f ⊆ insert Set.univ (Set.range (Set.Iio : ι → Set ι)) := by
    rintro _ ⟨J, rfl⟩
    exact (colex_coordinates_lower J).eq_univ_or_Iio.imp id
      (fun ⟨i, hi⟩ ↦ ⟨i, hi.symm⟩)
  have hcount : (Set.range f).Countable :=
    ((Set.countable_range (Set.Iio : ι → Set ι)).insert Set.univ).mono hrange
  let := hcount.to_subtype
  let : Countable (OrderIdeal (Lex (ιᵒᵈ →₀ ℝ))) :=
    (Equiv.ofInjective f colex_coordinates_injective).injective.countable
  exact Set.to_countable _

/-- Restricting coordinates identifies a supported colexicographic sublattice with the
colexicographic lattice indexed by its allowed coordinates. -/
private def colexRestrictionEquiv {ι : Type*} [LinearOrder ι] (s : Set ι) :
    VecLatEquiv (submoduleSublattice (V := Lex (ιᵒᵈ →₀ ℝ))
      (Finsupp.supported ℝ ℝ s)) (Lex (sᵒᵈ →₀ ℝ)) := by
  let e := Finsupp.supportedEquivFinsupp (R := ℝ) (M := ℝ) s
  have hm : StrictMono (fun x : submoduleSublattice (V := Lex (ιᵒᵈ →₀ ℝ))
      (Finsupp.supported ℝ ℝ s) ↦ (toLex (e x) : Lex (sᵒᵈ →₀ ℝ))) := by
    intro x y hxy
    obtain ⟨i, hi, hlt⟩ := hxy
    have his : OrderDual.ofDual i ∈ s := by
      by_contra hn
      exact hlt.ne ((Finsupp.mem_supported' ℝ _).mp x.property i hn |>.trans
        ((Finsupp.mem_supported' ℝ _).mp y.property i hn).symm)
    exact ⟨⟨i, his⟩, fun j hj ↦ hi j.val hj, hlt⟩
  exact { e with map_sup' := hm.monotone.map_sup, map_inf' := hm.monotone.map_inf }

/-- Every proper ideal of a well-ordered colexicographic lattice is the support ideal of a
strict initial segment. -/
private lemma colex_ideal_eq_cut {ι : Type*} [LinearOrder ι] [WellFoundedLT ι]
    (J : OrderIdeal (Lex (ιᵒᵈ →₀ ℝ))) (hJ : J ≠ ⊤) :
    ∃ i : ι, J = colexCutIdeal (Set.Iio i) (isLowerSet_Iio i) := by
  rcases (colex_coordinates_lower J).eq_univ_or_Iio with h | ⟨i, hi⟩
  · exact (hJ (top_unique (fun x _ ↦ colex_mem_of_coordinates J x
      (fun k _ ↦ (Set.ext_iff.mp h k).mpr (Set.mem_univ k))))).elim
  · refine ⟨i, colex_coordinates_injective ?_⟩
    exact hi.trans (Set.ext (fun k ↦
      (colexCutIdeal_single_mem_iff (Set.Iio i) (isLowerSet_Iio i) k).symm))

/-- The proper prime spectrum of a well-ordered colexicographic sum has the size of its index. -/
theorem colex_spectrum_cardinal (ι : Type u) [LinearOrder ι] [WellFoundedLT ι] :
    Cardinal.mk ↥(properPrimeIdeals (Lex (ιᵒᵈ →₀ ℝ))) = Cardinal.mk ι := by
  let F (i : ι) : properPrimeIdeals (Lex (ιᵒᵈ →₀ ℝ)) :=
    ⟨colexCutIdeal (Set.Iio i) (isLowerSet_Iio i),
      colexCutIdeal_properPrime _ _ i (lt_irrefl i)⟩
  refine (Cardinal.mk_congr (Equiv.ofBijective F ⟨?_, ?_⟩)).symm
  · intro i j hij
    apply Set.Iio_injective
    exact Set.ext (fun k ↦ (colexCutIdeal_single_mem_iff _ (isLowerSet_Iio i) k).symm.trans
      ((congrArg (fun P : properPrimeIdeals (Lex (ιᵒᵈ →₀ ℝ)) ↦
        toLex (Finsupp.single k 1) ∈ P.val) hij).to_iff.trans
        (colexCutIdeal_single_mem_iff _ (isLowerSet_Iio j) k)))
  · exact fun J ↦ (colex_ideal_eq_cut J.val J.property.1).imp
      (fun _ hi ↦ Subtype.ext hi.symm)

/-- The sublattice supported on a countable subset of well-ordered indices has countable
spectrum. -/
lemma colex_supported_countable_spectrum {ι : Type*} [LinearOrder ι]
    [WellFoundedLT ι] (s : Set ι) (hs : s.Countable) :
    (properPrimeIdeals (submoduleSublattice (V := Lex (ιᵒᵈ →₀ ℝ))
      (Finsupp.supported ℝ ℝ s))).Countable := by
  let := hs.to_subtype
  exact countable_spectrum_of_equiv (colexRestrictionEquiv s) (colex_countable_spectrum s)

end VectorLattice.CountableSpectra
