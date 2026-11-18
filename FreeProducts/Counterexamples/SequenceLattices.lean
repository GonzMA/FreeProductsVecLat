/-
Authors: Gonzalo Martínez-Fernández
-/

import FreeProducts.Counterexamples.Auxiliary
import FreeProducts.CountableSpectra.Basic
import FreeProducts.AVLvsVL.Coproducts.Equivalences

/-!
# Sequence lattices for extension counterexamples

Eventually constant and eventually affine real sequences form the common domains of
several extension and amalgamation obstructions. Their proper prime ideals are described
explicitly, their spectra are countable, and the eventually affine lattice is finitely
generated. The eventual-value homomorphism supplies the boundary data for the examples.
-/

noncomputable section

universe u

namespace VectorLattice.Counterexamples

open VectorLattice.CountableSpectra

/-- Real sequences that are eventually constant. -/
def eventuallyConstant : VectorSublattice (ℕ → ℝ) where
  carrier := {f | ∃ c : ℝ, ∃ N : ℕ, ∀ n ≥ N, f n = c}
  zero_mem' := ⟨0, 0, fun _ _ ↦ rfl⟩
  add_mem' := fun ⟨c, N, hf⟩ ⟨d, M, hg⟩ ↦
    ⟨c + d, max N M, fun k hk ↦ congrArg₂ (· + ·)
      (hf k ((le_max_left _ _).trans hk)) (hg k ((le_max_right _ _).trans hk))⟩
  smul_mem' := fun r _ ⟨c, N, hf⟩ ↦
    ⟨r • c, N, fun k hk ↦ congrArg (r • ·) (hf k hk)⟩
  sup_mem' := fun ⟨c, N, hf⟩ ⟨d, M, hg⟩ ↦
    ⟨c ⊔ d, max N M, fun k hk ↦ congrArg₂ (· ⊔ ·)
      (hf k ((le_max_left _ _).trans hk)) (hg k ((le_max_right _ _).trans hk))⟩

/-- The chosen eventual value agrees with any constant value attained on a tail of the
sequence. -/
private lemma chosen_eventual_value_eq (a : eventuallyConstant)
    {c : ℝ} {N : ℕ} (ha : ∀ n ≥ N, a.val n = c) : Classical.choose a.property = c := by
  obtain ⟨M, hM⟩ := Classical.choose_spec a.property
  exact (hM (max M N) (le_max_left _ _)).symm.trans (ha (max M N) (le_max_right _ _))

/-- A pointwise binary operation on eventually constant sequences acts on their eventual
values by the same operation. -/
private lemma chosen_eventual_value_map₂ (f : ℝ → ℝ → ℝ)
    (a b c : eventuallyConstant) (hc : ∀ n, c.val n = f (a.val n) (b.val n)) :
    Classical.choose c.property =
      f (Classical.choose a.property) (Classical.choose b.property) := by
  obtain ⟨N, hN⟩ := Classical.choose_spec a.property
  obtain ⟨M, hM⟩ := Classical.choose_spec b.property
  exact chosen_eventual_value_eq c (N := max N M) (fun n hn ↦
    (hc n).trans (congrArg₂ f (hN n ((le_max_left _ _).trans hn))
      (hM n ((le_max_right _ _).trans hn))))

/-- The eventual value of an eventually constant sequence. -/
def eventualValue : VecLatHom eventuallyConstant ℝ where
  toFun f := Classical.choose f.property
  map_add' := fun a b ↦ chosen_eventual_value_map₂ (· + ·) a b (a + b) (fun _ ↦ rfl)
  map_smul' := fun r a ↦
    chosen_eventual_value_map₂ (fun x _ ↦ r • x) a a (r • a) (fun _ ↦ rfl)
  map_sup' := fun a b ↦ chosen_eventual_value_map₂ (· ⊔ ·) a b (a ⊔ b) (fun _ ↦ rfl)
  map_inf' := fun a b ↦ chosen_eventual_value_map₂ (· ⊓ ·) a b (a ⊓ b) (fun _ ↦ rfl)

/-- The eventual-value homomorphism returns the constant value of any tail. -/
lemma eventualValue_eq_of_eventually_constant (a : eventuallyConstant)
    {c : ℝ} {N : ℕ} (ha : ∀ n ≥ N, a.val n = c) : eventualValue a = c := by
  exact chosen_eventual_value_eq a ha

/-- An affine sequence with smaller slope is eventually bounded above by one with larger
slope. -/
private lemma affine_le_eventually (a b c d : ℝ) (hbd : b < d) :
    ∃ N : ℕ, ∀ n ≥ N, a + b * (n : ℝ) ≤ c + d * (n : ℝ) := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((a - c) / (d - b))
  refine ⟨N, fun n hn ↦ ?_⟩
  nlinarith [(div_lt_iff₀ (sub_pos.mpr hbd)).mp
    (hN.trans_le (Nat.cast_le.mpr hn))]

/-- The maximum of two affine sequences is affine on a sufficiently late tail. -/
private lemma max_affine_eventually_affine (a b c d : ℝ) :
    ∃ e f : ℝ, ∃ N : ℕ,
      ∀ n ≥ N, max (a + b * (n : ℝ)) (c + d * (n : ℝ)) = e + f * (n : ℝ) := by
  rcases lt_trichotomy b d with h | rfl | h
  · obtain ⟨N, hN⟩ := affine_le_eventually a b c d h
    exact ⟨c, d, N, fun n hn ↦ max_eq_right (hN n hn)⟩
  · exact ⟨max a c, b, 0, fun n _ ↦ max_add_add_right a c (b * (n : ℝ))⟩
  · obtain ⟨N, hN⟩ := affine_le_eventually c d a b h
    exact ⟨a, b, N, fun n hn ↦ max_eq_left (hN n hn)⟩

/-- Real sequences that are eventually affine in their index. -/
def eventuallyAffine : VectorSublattice (ℕ → ℝ) where
  carrier := {f | ∃ a b : ℝ, ∃ N : ℕ, ∀ n ≥ N, f n = a + b * (n : ℝ)}
  zero_mem' := ⟨0, 0, 0, fun _ _ ↦ ((zero_add _).trans (zero_mul _)).symm⟩
  add_mem' := by
    rintro f g ⟨a, b, N, hf⟩ ⟨c, d, M, hg⟩
    refine ⟨a + c, b + d, max N M, fun n hn ↦ ?_⟩
    simpa only [Pi.add_apply, hf n ((le_max_left _ _).trans hn),
      hg n ((le_max_right _ _).trans hn), add_mul] using
      add_add_add_comm a (b * (n : ℝ)) c (d * (n : ℝ))
  smul_mem' := by
    rintro r f ⟨a, b, N, hf⟩
    exact ⟨r * a, r * b, N, fun n hn ↦
      (congrArg (r * ·) (hf n hn)).trans
        ((mul_add _ _ _).trans (congrArg (r * a + ·) (mul_assoc _ _ _).symm))⟩
  sup_mem' := by
    rintro f g ⟨a, b, N, hf⟩ ⟨c, d, M, hg⟩
    obtain ⟨e, t, K, hK⟩ := max_affine_eventually_affine a b c d
    exact ⟨e, t, max (max N M) K, fun n hn ↦
      (congrArg₂ max
        (hf n ((le_max_left N M).trans ((le_max_left _ K).trans hn)))
        (hg n ((le_max_right N M).trans ((le_max_left _ K).trans hn)))).trans
        (hK n ((le_max_right _ K).trans hn))⟩

/-- Eventually constant sequences form a sublattice of the eventually affine sequences. -/
theorem eventuallyConstant_le_eventuallyAffine :
    eventuallyConstant ≤ eventuallyAffine := by
  rintro f ⟨c, N, hf⟩
  exact ⟨c, 0, N, fun n hn ↦ (hf n hn).trans
    ((congrArg (c + ·) (zero_mul (n : ℝ))).trans (add_zero c)).symm⟩

/-- The coordinate unit sequence, regarded as an eventually constant sequence. -/
private def sequenceBasis (n : ℕ) : eventuallyConstant :=
  ⟨Pi.single n 1, 0, n + 1, fun _ hk ↦
    Pi.single_eq_of_ne (ne_of_gt ((Nat.lt_succ_self n).trans_le hk)) 1⟩

/-- A linear subspace containing every coordinate unit sequence contains every eventually zero
sequence. -/
private lemma sequence_finite_support_mem
    (Y : VectorSublattice (ℕ → ℝ)) (M : Submodule ℝ Y) (b : ℕ → Y)
    (hb : ∀ n, (b n).val = Pi.single n 1) (hM : ∀ n, b n ∈ M)
    (x : Y) {N : ℕ} (hx : ∀ n ≥ N, x.val n = 0) : x ∈ M := by
  have hsum : (∑ i ∈ Finset.range N, x.val i • b i) ∈ M :=
    M.sum_mem (fun i _ ↦ M.smul_mem _ (hM i))
  suffices heq : (∑ i ∈ Finset.range N, x.val i • b i) = x from heq ▸ hsum
  refine Subtype.ext (funext (fun k ↦ ?_))
  by_cases hk : k < N
  · simp [hb, Finset.sum_apply, Pi.single_apply, hk]
  · simp [hb, Finset.sum_apply, Pi.single_apply, hk, hx k (Nat.le_of_not_gt hk)]

/-- A prime ideal omitting a coordinate unit consists exactly of the sequences vanishing at
that coordinate. -/
private lemma sequence_prime_mem_iff
    (Y : VectorSublattice (ℕ → ℝ)) (J : OrderIdeal Y) (hJ : J.IsPrime)
    (i : ℕ) (e : Y) (he : e.val = Pi.single i 1) (hi : e ∉ J) (x : Y) :
    x ∈ J ↔ x.val i = 0 := by
  obtain ⟨K, hK, hres⟩ := OrderIdeal.exists_prime_extension Y J hJ
  have hiK : Pi.single i 1 ∉ K := fun h ↦ hi ((hres e).mp (he.symm ▸ h))
  exact (hres x).symm.trans (pi_prime_mem_iff K hK i hiK x.val)

/-- A proper ideal containing the kernel of a scalar character equals that kernel. -/
private lemma proper_ideal_eq_character_kernel
    {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X]
    (J : OrderIdeal X) (hJ : J ≠ ⊤) (φ : VecLatHom X ℝ)
    (hker : ∀ x, φ x = 0 → x ∈ J) (x : X) : x ∈ J ↔ φ x = 0 := by
  refine ⟨fun hx ↦ ?_, hker x⟩
  by_contra hφx
  refine hJ (top_unique (fun y _ ↦ ?_))
  have hzero : φ (y - (φ y / φ x) • x) = 0 := by
    simp only [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hφx, sub_self]
  exact sub_add_cancel y ((φ y / φ x) • x) ▸
    J.add_mem (hker _ hzero) (J.smul_mem _ hx)

/-- Every proper prime of the eventually constant lattice is a coordinate kernel or the kernel
of the eventual-value map. -/
private lemma eventuallyConstant_prime_classification (J : OrderIdeal eventuallyConstant)
    (hJ : J ∈ properPrimeIdeals eventuallyConstant) :
    ∃ c : Option ℕ, ∀ x : eventuallyConstant, x ∈ J ↔
      match c with
      | none => eventualValue x = 0
      | some n => x.val n = 0 := by
  classical
  by_cases hex : ∃ i, sequenceBasis i ∉ J
  · obtain ⟨i, hi⟩ := hex
    exact ⟨some i,
      sequence_prime_mem_iff eventuallyConstant J hJ.2 i (sequenceBasis i) rfl hi⟩
  · have hall : ∀ i, sequenceBasis i ∈ J :=
      fun i ↦ Classical.byContradiction (fun hi ↦ hex ⟨i, hi⟩)
    refine ⟨none, proper_ideal_eq_character_kernel J hJ.1 eventualValue (fun x hx ↦ ?_)⟩
    obtain ⟨N, hN⟩ := Classical.choose_spec x.property
    exact sequence_finite_support_mem eventuallyConstant J.toSubmodule sequenceBasis
      (fun _ ↦ rfl) hall x (N := N) (fun n hn ↦ (hN n hn).trans hx)

/-- The eventually constant sequence lattice has countably many proper prime ideals. -/
private lemma eventuallyConstant_countable_spectrum :
    (properPrimeIdeals eventuallyConstant).Countable := by
  choose code hcode using fun J : properPrimeIdeals eventuallyConstant ↦
    eventuallyConstant_prime_classification J.val J.property
  have hinj : Function.Injective code := fun J K h ↦ Subtype.ext (SetLike.ext (fun x ↦
    (hcode J x).trans (h.symm ▸ (hcode K x).symm)))
  exact hinj.countable

/-- An eventually affine sequence with nonzero slope dominates the absolute value of any other
eventually affine sequence after scalar multiplication on a tail. -/
private lemma affine_eventual_domination (f g : eventuallyAffine)
    {a b : ℝ} {N : ℕ} (hf : ∀ k ≥ N, f.val k = a + b * (k : ℝ)) (hb : b ≠ 0) :
    ∃ t : ℝ, ∃ K : ℕ, ∀ k ≥ K, |g.val k| ≤ t * f.val k := by
  obtain ⟨c, d, M, hg⟩ := g.property
  have htb : ((|d| + 1) / b) * b = |d| + 1 := div_mul_cancel₀ _ hb
  obtain ⟨K, hK⟩ := affine_le_eventually c d (((|d| + 1) / b) * a) (|d| + 1)
    ((le_abs_self d).trans_lt (lt_add_one _))
  obtain ⟨L, hL⟩ := affine_le_eventually (-c) (-d) (((|d| + 1) / b) * a) (|d| + 1)
    ((neg_le_abs d).trans_lt (lt_add_one _))
  refine ⟨(|d| + 1) / b, max (max N M) (max K L), fun k hk ↦ ?_⟩
  rw [hf k (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk),
    hg k (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk),
    mul_add, ← mul_assoc, htb]
  exact abs_le.mpr ⟨by
    linarith [hL k (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk)],
    hK k (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk)⟩

/-- An ideal containing all coordinate units and an element with nonzero eventual slope is the
entire eventually affine lattice. -/
private lemma affine_ideal_eq_top_of_nonzero_slope (J : OrderIdeal eventuallyAffine)
    (hall : ∀ n, VectorSublattice.inclusion eventuallyConstant_le_eventuallyAffine
      (sequenceBasis n) ∈ J) (f : eventuallyAffine) (hfJ : f ∈ J)
    {a b : ℝ} {N : ℕ} (hf : ∀ k ≥ N, f.val k = a + b * (k : ℝ)) (hb : b ≠ 0) :
    J = ⊤ := by
  refine top_unique (fun g _ ↦ ?_)
  obtain ⟨t, K, hK⟩ := affine_eventual_domination f g hf hb
  have he : (|g| - t • f)⁺ ∈ J := sequence_finite_support_mem eventuallyAffine
    J.toSubmodule (fun n ↦ VectorSublattice.inclusion
      eventuallyConstant_le_eventuallyAffine (sequenceBasis n)) (fun _ ↦ rfl) hall
    _ (N := K) (fun k hk ↦ max_eq_right (sub_nonpos.mpr (hK k hk)))
  exact J.mem_of_abs_mem (J.solid (J.add_mem he (J.smul_mem t hfJ)) (abs_nonneg g)
    (sub_le_iff_le_add.mp le_sup_left))

/-- A proper ideal containing all coordinate units can contain only eventually constant
sequences. -/
private lemma affine_proper_ideal_mem_eventuallyConstant (J : OrderIdeal eventuallyAffine)
    (hJ : J ≠ ⊤) (hall : ∀ n, VectorSublattice.inclusion
      eventuallyConstant_le_eventuallyAffine (sequenceBasis n) ∈ J)
    (x : eventuallyAffine) (hx : x ∈ J) : x.val ∈ eventuallyConstant := by
  obtain ⟨a, b, N, hN⟩ := x.property
  have hb : b = 0 := Classical.byContradiction (fun hb ↦
    hJ (affine_ideal_eq_top_of_nonzero_slope J hall x hx hN hb))
  exact ⟨a, N, fun k hk ↦ by simpa only [hb, zero_mul, add_zero] using hN k hk⟩

/-- A proper ideal of eventually affine sequences containing every coordinate unit is either
the eventually zero ideal or the eventually constant ideal. -/
private lemma affine_ideal_classification (J : OrderIdeal eventuallyAffine) (hJ : J ≠ ⊤)
    (hall : ∀ n, VectorSublattice.inclusion eventuallyConstant_le_eventuallyAffine
      (sequenceBasis n) ∈ J) :
    ∃ c : Bool, ∀ x : eventuallyAffine, x ∈ J ↔
      if c then x.val ∈ eventuallyConstant else ∃ N, ∀ k ≥ N, x.val k = 0 := by
  let I := idealPreimage
    (VectorSublattice.inclusion eventuallyConstant_le_eventuallyAffine) J
  by_cases hI : I = ⊤
  · refine ⟨true, fun x ↦ ⟨affine_proper_ideal_mem_eventuallyConstant J hJ hall x,
      fun hx ↦ show (⟨x.val, hx⟩ : eventuallyConstant) ∈ I from ?_⟩⟩
    exact hI.symm ▸ show (⟨x.val, hx⟩ : eventuallyConstant) ∈
      (⊤ : OrderIdeal eventuallyConstant) from trivial
  · have hker : ∀ x : eventuallyConstant, eventualValue x = 0 → x ∈ I := by
      intro x hx
      obtain ⟨N, hN⟩ := Classical.choose_spec x.property
      exact sequence_finite_support_mem eventuallyConstant I.toSubmodule sequenceBasis
        (fun _ ↦ rfl) hall x (N := N) (fun k hk ↦ (hN k hk).trans hx)
    refine ⟨false, fun x ↦ ⟨fun hx ↦ ?_, ?_⟩⟩
    · let y : eventuallyConstant :=
        ⟨x.val, affine_proper_ideal_mem_eventuallyConstant J hJ hall x hx⟩
      obtain ⟨N, hN⟩ := Classical.choose_spec y.property
      exact ⟨N, fun k hk ↦ (hN k hk).trans
        ((proper_ideal_eq_character_kernel I hI eventualValue hker y).mp hx)⟩
    · exact fun ⟨N, hN⟩ ↦ sequence_finite_support_mem eventuallyAffine J.toSubmodule
        (fun n ↦ VectorSublattice.inclusion eventuallyConstant_le_eventuallyAffine
          (sequenceBasis n)) (fun _ ↦ rfl) hall x (N := N) hN

/-- Every proper prime in the eventually affine lattice is a coordinate kernel, the eventually
zero ideal, or the eventually constant ideal. -/
private lemma eventuallyAffine_prime_classification (J : OrderIdeal eventuallyAffine)
    (hJ : J ∈ properPrimeIdeals eventuallyAffine) :
    ∃ c : ℕ ⊕ Bool, ∀ x : eventuallyAffine, x ∈ J ↔
      match c with
      | .inl n => x.val n = 0
      | .inr b => if b then x.val ∈ eventuallyConstant else ∃ N, ∀ k ≥ N, x.val k = 0 := by
  classical
  by_cases hex : ∃ n, VectorSublattice.inclusion eventuallyConstant_le_eventuallyAffine
      (sequenceBasis n) ∉ J
  · obtain ⟨n, hn⟩ := hex
    exact ⟨.inl n, sequence_prime_mem_iff eventuallyAffine J hJ.2 n
      (VectorSublattice.inclusion eventuallyConstant_le_eventuallyAffine (sequenceBasis n))
      rfl hn⟩
  · obtain ⟨b, hb⟩ := affine_ideal_classification J hJ.1
      (fun n ↦ Classical.byContradiction (fun hn ↦ hex ⟨n, hn⟩))
    exact ⟨.inr b, hb⟩

/-- The eventually affine sequence lattice has countably many proper prime ideals. -/
private lemma eventuallyAffine_countable_spectrum :
    (properPrimeIdeals eventuallyAffine).Countable := by
  choose code hcode using fun J : properPrimeIdeals eventuallyAffine ↦
    eventuallyAffine_prime_classification J.val J.property
  have hinj : Function.Injective code := fun J K h ↦ Subtype.ext (SetLike.ext (fun x ↦
    (hcode J x).trans (h.symm ▸ (hcode K x).symm)))
  exact hinj.countable

/-- Adjoining one real coordinate to an eventually constant sequence gives a lattice
equivalent to the eventually constant sequence lattice. -/
private def eventuallyConstantProdEquiv :
    VecLatEquiv (eventuallyConstant × ℝ) eventuallyConstant := by
  refine
    { toFun := fun x ↦ ⟨fun n ↦ match n with | 0 => x.2 | n + 1 => x.1.val n, ?_⟩
      invFun := fun x ↦ (⟨fun n ↦ x.val (n + 1), ?_⟩, x.val 0)
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_
      map_smul' := ?_
      map_sup' := ?_
      map_inf' := ?_ }
  case refine_1 =>
    obtain ⟨c, N, hN⟩ := x.1.property
    exact ⟨c, N + 1, fun n ↦ match n with
      | 0 => fun h ↦ False.elim (Nat.not_succ_le_zero N h)
      | k + 1 => fun h ↦ hN k (Nat.le_of_succ_le_succ h)⟩
  case refine_2 | refine_3 | refine_7 | refine_8 =>
    exact fun _ _ ↦ Subtype.ext (funext (fun n ↦ Nat.casesOn n rfl (fun _ ↦ rfl)))
  case refine_4 =>
    obtain ⟨c, N, hN⟩ := x.property
    exact ⟨c, N, fun n hn ↦ hN (n + 1) (hn.trans (Nat.le_succ n))⟩
  case refine_5 => exact fun _ ↦ rfl
  case refine_6 =>
    exact fun _ ↦ Subtype.ext (funext (fun n ↦ Nat.casesOn n rfl (fun _ ↦ rfl)))

/-- The globally affine sequence with the specified constant term and slope. -/
private def affineSequence (a b : ℝ) : eventuallyAffine :=
  ⟨fun k ↦ a + b * (k : ℝ), a, b, 0, fun _ _ ↦ rfl⟩

/-- Each coordinate unit is a positive-part lattice expression in the constant-one and
identity sequences. -/
private lemma sequenceBasis_eq_affine_posPart (n : ℕ) :
    VectorSublattice.inclusion eventuallyConstant_le_eventuallyAffine (sequenceBasis n) =
      (affineSequence 1 0 - |affineSequence 0 1 - (n : ℝ) • affineSequence 1 0|)⁺ := by
  refine Subtype.ext (funext (fun k ↦ ?_))
  change (Pi.single n 1 : ℕ → ℝ) k = max ((1 + 0 * (k : ℝ)) -
    |(0 + 1 * (k : ℝ)) - (n : ℝ) * (1 + 0 * (k : ℝ))|) 0
  simp only [zero_mul, add_zero, one_mul, zero_add, mul_one]
  rcases lt_trichotomy k n with h | rfl | h
  · have hh : (k : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt h
    exact (Pi.single_eq_of_ne h.ne 1).trans
      (max_eq_right (by linarith [neg_le_abs ((k : ℝ) - n)])).symm
  · simp
  · have hh : (n : ℝ) + 1 ≤ k := by exact_mod_cast Nat.succ_le_of_lt h
    exact (Pi.single_eq_of_ne h.ne' 1).trans
      (max_eq_right (by linarith [le_abs_self ((k : ℝ) - n)])).symm

/-- The constant-one sequence and the identity sequence generate the entire eventually affine
lattice. -/
private lemma affine_sublattice_eq_top (S : VectorSublattice eventuallyAffine)
    (h1 : affineSequence 1 0 ∈ S) (hb : affineSequence 0 1 ∈ S) : S = ⊤ := by
  have he : ∀ n, VectorSublattice.inclusion eventuallyConstant_le_eventuallyAffine
      (sequenceBasis n) ∈ S := fun n ↦ (sequenceBasis_eq_affine_posPart n).symm ▸
    S.posPart_mem (S.sub_mem h1 (S.abs_mem (S.sub_mem hb (S.smul_mem (n : ℝ) h1))))
  refine SetLike.ext (fun x ↦ ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩)
  obtain ⟨a, b, N, hN⟩ := x.property
  have hlin : a • affineSequence 1 0 + b • affineSequence 0 1 ∈ S :=
    S.add_mem (S.smul_mem a h1) (S.smul_mem b hb)
  have hres : x - (a • affineSequence 1 0 + b • affineSequence 0 1) ∈ S :=
    sequence_finite_support_mem eventuallyAffine S.toSubmodule
      (fun n ↦ VectorSublattice.inclusion eventuallyConstant_le_eventuallyAffine
        (sequenceBasis n)) (fun _ ↦ rfl) he _ (N := N) (fun k hk ↦ ?_)
  · exact sub_add_cancel x _ ▸ S.add_mem hres hlin
  change x.val k - (a * (1 + 0 * (k : ℝ)) + b * (0 + 1 * (k : ℝ))) = 0
  simp [hN k hk]

/-- The eventually affine lattice is finitely generated. -/
private lemma eventuallyAffine_finitely_generated : IsFinitelyGenerated eventuallyAffine := by
  let g : Fin 2 → eventuallyAffine := fun i ↦
    if i = 0 then affineSequence 1 0 else affineSequence 0 1
  refine ⟨2, g, affine_sublattice_eq_top _
    (VectorSublattice.subset_generated _ ⟨0, ?_⟩)
    (VectorSublattice.subset_generated _ ⟨1, ?_⟩)⟩
  all_goals simp [g]

/-- The sequence lattices used in the extension obstruction have countable spectra. -/
theorem sequence_lattices_countable_spectrum :
    (properPrimeIdeals eventuallyConstant).Countable ∧
      (properPrimeIdeals eventuallyAffine).Countable ∧
      (properPrimeIdeals (eventuallyConstant × ℝ)).Countable ∧
      IsFinitelyGenerated eventuallyAffine := by
  exact ⟨eventuallyConstant_countable_spectrum, eventuallyAffine_countable_spectrum,
    countable_spectrum_of_equiv eventuallyConstantProdEquiv eventuallyConstant_countable_spectrum,
    eventuallyAffine_finitely_generated⟩

/-- The ideal of sequences in a sublattice that vanish at a specified coordinate. -/
def sequenceCoordinateIdeal (S : VectorSublattice (ℕ → ℝ)) (n : ℕ) : OrderIdeal S :=
  OrderIdeal.ofKerVecLatHom
    { toFun := fun x ↦ x.val n
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      map_sup' := fun _ _ ↦ rfl
      map_inf' := fun _ _ ↦ rfl }

/-- The ideal of sequences in a sublattice that vanish eventually. -/
def eventuallyZeroIdeal (S : VectorSublattice (ℕ → ℝ)) : OrderIdeal S :=
  OrderIdeal.ofSolid
    { carrier := {x | ∃ N, ∀ n ≥ N, x.val n = 0}
      zero_mem' := ⟨0, fun _ _ ↦ rfl⟩
      add_mem' := fun ⟨N, hx⟩ ⟨M, hy⟩ ↦
        ⟨max N M, fun n hn ↦ (congrArg₂ (· + ·)
          (hx n ((le_max_left _ _).trans hn))
          (hy n ((le_max_right _ _).trans hn))).trans (zero_add 0)⟩
      smul_mem' := fun r _ ⟨N, hx⟩ ↦
        ⟨N, fun n hn ↦ (congrArg (r * ·) (hx n hn)).trans (mul_zero r)⟩ }
    (fun _ _ ⟨N, hx⟩ hxy ↦ ⟨N, fun n hn ↦ abs_eq_zero.mp
      (le_antisymm ((hxy n).trans_eq ((congrArg abs (hx n hn)).trans abs_zero))
        (abs_nonneg _))⟩)

/-- An eventually affine sequence dominated in absolute value by an eventually constant
sequence must itself be eventually constant. -/
private lemma affine_mem_constant_of_abs_le (x y : eventuallyAffine)
    (hx : x.val ∈ eventuallyConstant) (hxy : |y| ≤ |x|) :
    y.val ∈ eventuallyConstant := by
  obtain ⟨a, b, N, hy⟩ := y.property
  suffices hb : b = 0 from
    ⟨a, N, fun n hn ↦ by simpa only [hb, zero_mul, add_zero] using hy n hn⟩
  by_contra hb
  obtain ⟨t, K, hK⟩ := affine_eventual_domination y (affineSequence 0 1) hy hb
  obtain ⟨c, M, hM⟩ := hx
  obtain ⟨n, hn⟩ := exists_nat_gt (|t| * |c|)
  let k := max (max K M) n
  have hk : (k : ℝ) ≤ t * y.val k := by
    simpa only [affineSequence, one_mul, zero_add,
      abs_of_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      using hK k ((le_max_left K M).trans (le_max_left _ _))
  exact (not_le_of_gt hn) ((Nat.cast_le.mpr (le_max_right (max K M) n)).trans
    (hk.trans (((le_abs_self (t * y.val k)).trans_eq (abs_mul _ _)).trans
      ((mul_le_mul_of_nonneg_left (hxy k) (abs_nonneg t)).trans_eq
        (congrArg (fun z ↦ |t| * |z|) (hM k
          ((le_max_right K M).trans (le_max_left _ _))))))))

/-- The ideal of eventually constant sequences inside the eventually affine lattice. -/
def eventuallyConstantIdeal : OrderIdeal eventuallyAffine :=
  OrderIdeal.ofSolid
    (eventuallyConstant.toSubmodule.comap eventuallyAffine.subtype.toLinearMap)
    affine_mem_constant_of_abs_le

/-- A coordinate kernel is a proper prime ideal whenever the sequence sublattice contains the
constant-one sequence. -/
private lemma coordinate_ideal_mem_spectrum (S : VectorSublattice (ℕ → ℝ))
    (hS : (fun _ ↦ (1 : ℝ)) ∈ S) (n : ℕ) :
    sequenceCoordinateIdeal S n ∈ properPrimeIdeals S := by
  exact normalized_character_kernel_prime _ ⟨fun _ ↦ 1, hS⟩ rfl

/-- In the eventually constant lattice, the eventually zero ideal is exactly the kernel of the
eventual-value homomorphism. -/
private lemma constant_zero_ideal_eq_kernel :
    eventuallyZeroIdeal eventuallyConstant = OrderIdeal.ofKerVecLatHom eventualValue := by
  refine SetLike.ext (fun x ↦ ?_)
  refine ⟨fun ⟨N, hx⟩ ↦ eventualValue_eq_of_eventually_constant x hx, fun hx ↦ ?_⟩
  obtain ⟨N, hN⟩ := Classical.choose_spec x.property
  exact ⟨N, fun n hn ↦ (hN n hn).trans hx⟩

/-- The eventually zero ideal is proper and prime in the eventually constant lattice. -/
private lemma constant_zero_ideal_mem_spectrum :
    eventuallyZeroIdeal eventuallyConstant ∈ properPrimeIdeals eventuallyConstant := by
  rw [constant_zero_ideal_eq_kernel]
  exact normalized_character_kernel_prime eventualValue ⟨fun _ ↦ 1, 1, 0, fun _ _ ↦ rfl⟩
    (eventualValue_eq_of_eventually_constant _ (N := 0) (fun _ _ ↦ rfl))

/-- An eventually affine sequence is either zero on a tail or nonzero at every point of a
tail. -/
private lemma affine_tail_dichotomy (f : eventuallyAffine) :
    (∃ N, ∀ n ≥ N, f.val n = 0) ∨ (∃ N, ∀ n ≥ N, f.val n ≠ 0) := by
  obtain ⟨a, b, N, hf⟩ := f.property
  by_cases hb : b = 0
  · by_cases ha : a = 0
    · exact Or.inl ⟨N, fun n hn ↦ by simpa [ha, hb] using hf n hn⟩
    · exact Or.inr ⟨N, fun n hn hzero ↦ ha (by simpa [hb, hzero] using (hf n hn).symm)⟩
  · obtain ⟨t, K, hK⟩ := affine_eventual_domination f (affineSequence 1 0) hf hb
    exact Or.inr ⟨K, fun n hn hzero ↦ (not_le_of_gt (zero_lt_one : (0 : ℝ) < 1))
      (by simpa [affineSequence, hzero] using hK n hn)⟩

/-- The eventually zero ideal is proper and prime in the eventually affine lattice. -/
private lemma affine_zero_ideal_mem_spectrum :
    eventuallyZeroIdeal eventuallyAffine ∈ properPrimeIdeals eventuallyAffine := by
  refine ⟨?_, fun f g hfg ↦ ?_⟩
  · intro htop
    obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, (affineSequence 1 0).val n = 0 :=
      show affineSequence 1 0 ∈ eventuallyZeroIdeal eventuallyAffine from
        htop.symm ▸ show affineSequence 1 0 ∈ (⊤ : OrderIdeal eventuallyAffine) from trivial
    exact (one_ne_zero : (1 : ℝ) ≠ 0) (by simpa [affineSequence] using hN N le_rfl)
  · rcases affine_tail_dichotomy f with hf | ⟨N, hf⟩
    · exact Or.inl hf
    · exact Or.inr ⟨N, fun n hn ↦ (min_choice (f.val n) (g.val n)).elim
        (fun h ↦ False.elim (hf n hn (h.symm.trans (congrArg (fun z ↦ z.val n) hfg))))
        (fun h ↦ h.symm.trans (congrArg (fun z ↦ z.val n) hfg))⟩

/-- The eventually constant sequences form a proper prime ideal in the eventually affine
lattice. -/
private lemma constant_ideal_mem_affine_spectrum :
    eventuallyConstantIdeal ∈ properPrimeIdeals eventuallyAffine := by
  refine ⟨?_, fun f g hfg ↦ (affine_zero_ideal_mem_spectrum.2 f g hfg).imp
    (fun ⟨N, hN⟩ ↦ ⟨0, N, hN⟩) (fun ⟨N, hN⟩ ↦ ⟨0, N, hN⟩)⟩
  intro htop
  obtain ⟨c, N, hN⟩ : (affineSequence 0 1).val ∈ eventuallyConstant :=
    show affineSequence 0 1 ∈ eventuallyConstantIdeal from
      htop.symm ▸ show affineSequence 0 1 ∈ (⊤ : OrderIdeal eventuallyAffine) from trivial
  exact (Nat.cast_injective (R := ℝ)).ne (Nat.ne_add_one N)
    (by simpa [affineSequence] using (hN N le_rfl).trans (hN (N + 1) (Nat.le_succ N)).symm)

/-- The proper prime ideals of eventually affine sequences are the coordinate kernels,
the eventually zero sequences, and the eventually constant sequences. -/
theorem eventuallyAffine_spectrum :
    properPrimeIdeals eventuallyAffine =
      Set.range (sequenceCoordinateIdeal eventuallyAffine) ∪
        {eventuallyZeroIdeal eventuallyAffine, eventuallyConstantIdeal} := by
  refine Set.ext (fun J ↦ ⟨fun hJ ↦ ?_, fun hJ ↦ ?_⟩)
  · obtain ⟨c, hc⟩ := eventuallyAffine_prime_classification J hJ
    rcases c with n | (_ | _)
    · exact Or.inl ⟨n, SetLike.ext (fun x ↦ (hc x).symm)⟩
    · exact Or.inr (Or.inl (SetLike.ext hc))
    · exact Or.inr (Or.inr (SetLike.ext hc))
  · exact hJ.elim
      (fun ⟨n, hn⟩ ↦ hn ▸ coordinate_ideal_mem_spectrum eventuallyAffine
        ⟨1, 0, 0, fun _ _ ↦ by simp⟩ n)
      (fun h ↦ h.elim (fun h ↦ h.symm ▸ affine_zero_ideal_mem_spectrum)
        (fun h ↦ h.symm ▸ constant_ideal_mem_affine_spectrum))

/-- The proper prime ideals of eventually constant sequences are the coordinate
kernels and the eventually zero sequences. -/
theorem eventuallyConstant_spectrum :
    properPrimeIdeals eventuallyConstant =
      Set.range (sequenceCoordinateIdeal eventuallyConstant) ∪
        {eventuallyZeroIdeal eventuallyConstant} := by
  refine Set.ext (fun J ↦ ⟨fun hJ ↦ ?_, fun hJ ↦ ?_⟩)
  · obtain ⟨c, hc⟩ := eventuallyConstant_prime_classification J hJ
    rcases c with _ | n
    · exact Or.inr ((SetLike.ext hc : J = OrderIdeal.ofKerVecLatHom eventualValue).trans
        constant_zero_ideal_eq_kernel.symm)
    · exact Or.inl ⟨n, SetLike.ext (fun x ↦ (hc x).symm)⟩
  · exact hJ.elim
      (fun ⟨n, hn⟩ ↦ hn ▸ coordinate_ideal_mem_spectrum eventuallyConstant
        ⟨1, 0, fun _ _ ↦ rfl⟩ n)
      (fun h ↦ h.symm ▸ constant_zero_ideal_mem_spectrum)

end VectorLattice.Counterexamples
