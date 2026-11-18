/-
Authors: Gonzalo Martínez-Fernández
-/

import FreeProducts.AVLvsVL.Classical.PolyhedralGeometry

/-!
# Retractions onto polyhedral cones

Retractions onto sign cells combine to give a piecewise-linear retraction onto a closed
polyhedral cone. Pullback then splits the restriction homomorphism.
-/

universe u

namespace VectorLattice.ConeRepresentation

/-- Realizes a linear form as an element of the free vector lattice on its coordinates. -/
private noncomputable def freeLinearForm {n : ℕ} (L : (Fin n → ℝ) →ₗ[ℝ] ℝ) : FVL (Fin n) :=
  ⟨L, (mem_free_iff _).mpr ⟨L.continuous_of_finiteDimensional,
    fun t _ x ↦ L.map_smul t x, 1, fun _ ↦ L, fun _ ↦ ⟨0, rfl⟩⟩⟩

/-- Subtracting a controlled scalar multiple preserves the non-strict sign of a real number;
this is the scalar estimate for the cell retraction. -/
private lemma subtract_scaled_preserves_sign {a b d : ℝ} (hd : 0 < d) (hab : d ≤ b / a) :
    (0 ≤ b → 0 ≤ b - d * a) ∧ (b ≤ 0 → b - d * a ≤ 0) := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · have h := (le_div_iff_of_neg ha).mp hab
    exact ⟨fun hb ↦ ((mul_neg_of_pos_of_neg hd ha).not_ge (hb.trans h)).elim,
      fun _ ↦ sub_nonpos.mpr h⟩
  · exact (hd.not_ge (by simpa only [ha, div_zero] using hab)).elim
  · have h := (le_div_iff₀ ha).mp hab
    exact ⟨fun _ ↦ sub_nonneg.mpr h,
      fun hb ↦ ((mul_pos hd ha).not_ge (h.trans hb)).elim⟩

/-- Constructs a free-function retraction onto the complement of a sign cell, preserving all
non-strict signs of the defining linear forms. -/
private lemma exists_sign_cell_retraction {n : ℕ} {ι : Type*} [Finite ι]
    (L : ι → (Fin n → ℝ) →ₗ[ℝ] ℝ) (a : Fin n → ℝ) (ha : ∃ i, L i a ≠ 0) :
    ∃ g : Fin n → FVL (Fin n),
      (∀ x, (¬ ∀ i, L i a ≠ 0 → 0 < L i x / L i a) → (fun j ↦ g j x) = x) ∧
      (∀ x, ¬ ∀ i, L i a ≠ 0 → 0 < L i (fun j ↦ g j x) / L i a) ∧
      ∀ x i, (0 ≤ L i x → 0 ≤ L i (fun j ↦ g j x)) ∧
        (L i x ≤ 0 → L i (fun j ↦ g j x) ≤ 0) := by
  classical
  let J := {i // L i a ≠ 0}
  let : Nonempty J := ⟨⟨ha.choose, ha.choose_spec⟩⟩
  let := Fintype.ofFinite J
  let l (i : J) : FVL (Fin n) := (L i.val a)⁻¹ • freeLinearForm (L i.val)
  let d : FVL (Fin n) := Finset.univ.inf' Finset.univ_nonempty l ⊔ 0
  let g (j : Fin n) := FVL.of j - a j • d
  have hmin (x : Fin n → ℝ) : ∃ j : J,
      (∀ i : J, L j.val x / L j.val a ≤ L i.val x / L i.val a) ∧
        d x = max (L j.val x / L j.val a) 0 := by
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf'
      (Finset.univ_nonempty : (Finset.univ : Finset J).Nonempty)
      (fun i : J ↦ L i.val x / L i.val a)
    refine ⟨j, fun i ↦ hj.symm.trans_le (Finset.inf'_le _ (Finset.mem_univ i)), ?_⟩
    rw [← free_lift_apply x d]
    simpa only [d, map_sup, map_finset_inf', map_zero, Function.comp_def, l, map_smul,
      free_lift_apply, freeLinearForm, smul_eq_mul, div_eq_mul_inv, mul_comm]
      using congrArg (fun t ↦ max t 0) hj
  have hg (x : Fin n → ℝ) : (fun j ↦ g j x) = x - d x • a :=
    funext (fun j ↦ congrArg (fun r ↦ x j - r) (mul_comm (a j) (d x)))
  have hLg (x : Fin n → ℝ) (i : ι) :
      L i (fun j ↦ g j x) = L i x - d x * L i a := by
    rw [hg, map_sub, map_smul, smul_eq_mul]
  refine ⟨g, ?_, ?_, ?_⟩
  · intro x hx
    push Not at hx
    obtain ⟨i, hi, hi'⟩ := hx
    obtain ⟨j, hj, hd⟩ := hmin x
    have hd0 : d x = 0 := hd.trans (max_eq_right ((hj ⟨i, hi⟩).trans hi'))
    simp only [hg, hd0, zero_smul, sub_zero]
  · intro x hx
    obtain ⟨j, _, hj⟩ := hmin x
    have h := hx j.val j.property
    rw [hLg, sub_div, mul_div_cancel_right₀ _ j.property, hj] at h
    exact (sub_nonpos.mpr (le_max_left _ _)).not_gt h
  · intro x i
    rw [hLg]
    by_cases hi : L i a = 0
    · simp [hi]
    · obtain ⟨j, hj, hd⟩ := hmin x
      rcases lt_or_ge 0 (L j.val x / L j.val a) with hpos | hnonpos
      · rw [max_eq_left hpos.le] at hd
        exact subtract_scaled_preserves_sign (hd.symm ▸ hpos) (hd.symm ▸ hj ⟨i, hi⟩)
      · rw [max_eq_right hnonpos] at hd
        simp [hd]

/-- A map preserving the non-strict signs of the defining forms preserves the complement of
the selected sign cell. -/
private lemma sign_preserving_cell_compl {n : ℕ} {ι : Type*}
    (L : ι → (Fin n → ℝ) →ₗ[ℝ] ℝ) (a x y : Fin n → ℝ)
    (hxy : ∀ i, (0 ≤ L i x → 0 ≤ L i y) ∧ (L i x ≤ 0 → L i y ≤ 0))
    (hx : ¬ ∀ i, L i a ≠ 0 → 0 < L i x / L i a) :
    ¬ ∀ i, L i a ≠ 0 → 0 < L i y / L i a := by
  push Not at hx ⊢
  obtain ⟨i, hi, hx⟩ := hx
  refine ⟨i, hi, ?_⟩
  rcases lt_or_gt_of_ne hi with ha | ha
  · have hx' : 0 ≤ L i x := by simpa using (div_le_iff_of_neg ha).mp hx
    exact div_nonpos_of_nonneg_of_nonpos ((hxy i).1 hx') ha.le
  · have hx' : L i x ≤ 0 := by simpa using (div_le_iff₀ ha).mp hx
    exact div_nonpos_of_nonpos_of_nonneg ((hxy i).2 hx') ha.le

/-- Combines finitely many sign-cell retractions into a retraction avoiding every selected
cell while preserving the defining signs. -/
private lemma exists_finite_cell_retraction {n : ℕ} {ι κ : Type*} [Finite ι]
    (L : ι → (Fin n → ℝ) →ₗ[ℝ] ℝ) (a : κ → Fin n → ℝ) (s : Finset κ)
    (ha : ∀ k ∈ s, ∃ i, L i (a k) ≠ 0) :
    ∃ g : Fin n → FVL (Fin n),
      (∀ x, (∀ k ∈ s, ¬ ∀ i, L i (a k) ≠ 0 → 0 < L i x / L i (a k)) →
        (fun j ↦ g j x) = x) ∧
      (∀ x k, k ∈ s → ¬ ∀ i, L i (a k) ≠ 0 → 0 < L i (fun j ↦ g j x) / L i (a k)) ∧
      ∀ x i, (0 ≤ L i x → 0 ≤ L i (fun j ↦ g j x)) ∧
        (L i x ≤ 0 → L i (fun j ↦ g j x) ≤ 0) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨FVL.of, by simp [FVL.of_apply]⟩
  | @insert k s hk ih =>
    obtain ⟨f, hf, hfout, hfsign⟩ := ih (fun j hj ↦ ha j (Finset.mem_insert_of_mem hj))
    obtain ⟨q, hq, hqout, hqsign⟩ := exists_sign_cell_retraction L (a k)
      (ha k (Finset.mem_insert_self _ _))
    refine ⟨fun i ↦ FVL.lift f (q i), ?_, ?_, ?_⟩
    all_goals simp only [free_substitution_apply]
    · intro x hx
      rw [hf x (fun j hj ↦ hx j (Finset.mem_insert_of_mem hj))]
      exact hq x (hx k (Finset.mem_insert_self _ _))
    · intro x j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hqout _
      · exact sign_preserving_cell_compl L (a j) _ _ (hqsign _)
          (hfout x j hj)
    · exact fun x i ↦ ⟨fun hx ↦ (hqsign _ i).1 ((hfsign x i).1 hx),
        fun hx ↦ (hqsign _ i).2 ((hfsign x i).2 hx)⟩

/-- The complement of an open polyhedral cone is a retract of the ambient space by a map with
free lattice function coordinates. -/
private lemma exists_polyhedral_retraction {n : ℕ} {s : Set (Fin n → ℝ)}
    (hs : IsOpenPolyhedralCone s) : ∃ g : Fin n → FVL (Fin n),
      (∀ x ∉ s, (fun j ↦ g j x) = x) ∧ ∀ x, (fun j ↦ g j x) ∉ s := by
  classical
  rcases hs with ⟨k, r, forms, rfl⟩
  let I := Σ i : Fin k, Fin (r i + 1)
  let L (i : I) := forms i.1 i.2
  let pattern (x : Fin n → ℝ) : I → Bool × Bool :=
    fun i ↦ (decide (0 < L i x), decide (L i x < 0))
  let P := {p : I → Bool × Bool // ∃ x, (∃ i, ∀ j, 0 < forms i j x) ∧ pattern x = p}
  let a (p : P) : Fin n → ℝ := p.property.choose
  have ha (p : P) : ∃ i, ∀ j, 0 < forms i j (a p) := p.property.choose_spec.1
  have hapat (p : P) : pattern (a p) = p.val := p.property.choose_spec.2
  have hnonzero (p : P) : ∃ i : I, L i (a p) ≠ 0 := by
    obtain ⟨i, hi⟩ := ha p
    exact ⟨⟨i, 0⟩, ne_of_gt (hi 0)⟩
  have hsub (p : P) (x : Fin n → ℝ)
      (hx : ∀ i : I, L i (a p) ≠ 0 → 0 < L i x / L i (a p)) :
      ∃ i, ∀ j, 0 < forms i j x := by
    obtain ⟨i, hi⟩ := ha p
    exact ⟨i, fun j ↦ (div_pos_iff_of_pos_right (hi j)).mp
      (hx ⟨i, j⟩ (ne_of_gt (hi j)))⟩
  have hcover (x : Fin n → ℝ) (hx : ∃ i, ∀ j, 0 < forms i j x) :
      ∃ p : P, ∀ i : I, L i (a p) ≠ 0 → 0 < L i x / L i (a p) := by
    let p : P := ⟨pattern x, x, hx, rfl⟩
    refine ⟨p, fun i hi ↦ ?_⟩
    have hsign : (0 < L i (a p) ↔ 0 < L i x) ∧ (L i (a p) < 0 ↔ L i x < 0) := by
      simpa only [pattern, p, Prod.mk.injEq, decide_eq_decide] using congrFun (hapat p) i
    rcases lt_or_gt_of_ne hi with hneg | hpos
    · exact div_pos_of_neg_of_neg (hsign.2.mp hneg) hneg
    · exact div_pos (hsign.1.mp hpos) hpos
  obtain ⟨g, hfix, hout, _⟩ := exists_finite_cell_retraction L a Finset.univ
    (fun p _ ↦ hnonzero p)
  refine ⟨g, fun x hx ↦ hfix x (fun p _ hp ↦ hx (hsub p x hp)), fun x hx ↦ ?_⟩
  obtain ⟨p, hp⟩ := hcover _ hx
  exact hout x p (Finset.mem_univ _) hp

/-- Restriction to a closed polyhedral cone admits a lattice-homomorphic right inverse into
the ambient free lattice. -/
lemma polyhedral_restriction_splits {n : ℕ} (C : ClosedCone n)
    (hC : IsClosedPolyhedralCone C.carrier) :
    ∃ R : VecLatHom (ConeFunctions C) (FVL (Fin n)),
      ∀ f, FVL.lift (coordinate C) (R f) = f := by
  obtain ⟨g, hfix, hout⟩ := exists_polyhedral_retraction
    (openPolyhedral_compl_of_closedPolyhedral hC C.zero_mem)
  have hmem (x : Fin n → ℝ) : (fun j ↦ g j x) ∈ C.carrier := by
    simpa only [Set.mem_compl_iff, not_not] using hout x
  let r (x : Fin n → ℝ) : C.carrier := ⟨fun j ↦ g j x, hmem x⟩
  have hr (x : C.carrier) : r x.val = x :=
    Subtype.ext (hfix x.val (not_not.mpr x.property))
  have hfree (f : ConeFunctions C) : (fun x ↦ f.val (r x)) ∈ FVL.concreteSublattice (Fin n) := by
    obtain ⟨F, hF⟩ := f.property
    have heq : (fun x ↦ f.val (r x)) = (FVL.lift g F).val :=
      funext (fun x ↦ (hF (r x)).trans (free_substitution_apply g F x).symm)
    rw [heq]
    exact (FVL.lift g F).property
  let R : VecLatHom (ConeFunctions C) (FVL (Fin n)) :=
    { toFun := fun f ↦ ⟨fun x ↦ f.val (r x), hfree f⟩
      map_add' := fun _ _ ↦ Subtype.ext rfl
      map_smul' := fun _ _ ↦ Subtype.ext rfl
      map_sup' := fun _ _ ↦ Subtype.ext rfl
      map_inf' := fun _ _ ↦ Subtype.ext rfl }
  refine ⟨R, fun f ↦ Subtype.ext (funext fun x ↦ ?_)⟩
  rw [coneRestriction_apply]
  exact congrArg f.val (hr x)

end VectorLattice.ConeRepresentation
