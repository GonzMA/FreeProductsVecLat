/-
Authors: Gonzalo Martínez-Fernández
-/

import FreeProducts.AVLvsVL.Classical.ConeRepresentation
import Mathlib.Geometry.Convex.Cone.DualFinite

/-!
# Polyhedral cones and supports of free functions

Finite linear inequalities describe open and closed polyhedral cones. Their supports,
linear images, complements and closures provide the geometry used in restriction lattices.
-/

universe u

namespace VectorLattice.ConeRepresentation

/-- A finite union of closed convex cones defined by finitely many
homogeneous linear inequalities. -/
def IsClosedPolyhedralCone {n : ℕ} (s : Set (Fin n → ℝ)) : Prop :=
  ∃ (k : ℕ) (cones : Fin k → PointedCone ℝ (Fin n → ℝ)),
    (∀ i, (cones i).DualFG .id) ∧
      s = ⋃ i, (cones i : Set (Fin n → ℝ))

/-- A finite union of intersections of nonempty finite families of
strict homogeneous linear inequalities. -/
def IsOpenPolyhedralCone {n : ℕ} (s : Set (Fin n → ℝ)) : Prop :=
  ∃ (k : ℕ) (r : Fin k → ℕ)
    (forms : ∀ i, Fin (r i + 1) → (Fin n → ℝ) →ₗ[ℝ] ℝ),
    s = {x | ∃ i, ∀ j, 0 < forms i j x}

/-- Two finite families of real lower and upper bounds admit a common intermediate value when
every lower bound is below every upper bound. -/
private lemma exists_between_finite_families {ι κ : Type*} [Finite ι] [Finite κ]
    (a : ι → ℝ) (b : κ → ℝ) (hab : ∀ i j, a i ≤ b j) :
    ∃ t : ℝ, (∀ i, a i ≤ t) ∧ ∀ j, t ≤ b j := by
  obtain ⟨B, hB⟩ := (Set.finite_range b).bddBelow
  refine ⟨sSup (insert B (Set.range a)),
    fun i ↦ le_csSup ((Set.finite_range a).insert B).bddAbove (Or.inr ⟨i, rfl⟩),
    fun j ↦ csSup_le (Set.insert_nonempty B _) ?_⟩
  rintro z (rfl | ⟨i, rfl⟩)
  · exact hB ⟨j, rfl⟩
  · exact hab i j

/-- Every finitely generated free lattice function admits a finite lattice normal form. -/
private lemma free_normal_form {n : ℕ} (f : FVL (Fin n)) :
    ∃ N : LLexpr.NormalForm n, ∀ x, N.eval x = f x := by
  obtain ⟨a, ha⟩ : ∃ a : LLexpr n,
      LLexpr.eval (FVL.coordinate : Fin n → _) a = f.val :=
    (LLexpr.generated_range_eq_combinations FVL.coordinate).le f.property
  refine ⟨a.normalize, fun x ↦ ?_⟩
  rw [LLexpr.normalize_eval, ← ha]
  clear ha
  induction a <;> simp_all [LLexpr.eval, FVL.coordinate]

/-- The strict positivity set of a free lattice function is an open polyhedral cone. -/
lemma isOpenPolyhedralCone_positive {n : ℕ} (f : FVL (Fin n)) :
    IsOpenPolyhedralCone {x | 0 < f x} := by
  classical
  obtain ⟨N, heval⟩ := free_normal_form f
  obtain ⟨r, hr⟩ : ∃ r, N.neg.coeffs.card = r + 1 :=
    Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Finset.card_pos.mpr N.neg.nonempty))
  let L (c : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ i, c i • LinearMap.proj i
  refine ⟨N.pos.coeffs.card, fun _ ↦ r,
    fun i j ↦ L (N.pos.coeffs.equivFin.symm i).val -
      L ((Finset.equivFinOfCardEq hr).symm j).val, Set.ext fun x ↦ ?_⟩
  simp only [Set.mem_ofPred_eq, ← heval x,
    LLexpr.NormalForm.eval, LLexpr.SupLinearCombination.eval, LinearMap.sub_apply,
    sub_pos, Finset.lt_sup'_iff, Finset.sup'_lt_iff]
  rw [N.pos.coeffs.equivFin.surjective.exists]
  simp_rw [(Finset.equivFinOfCardEq hr).surjective.forall]
  simp [L, Fintype.linearCombination_apply]

/-- Every open polyhedral cone is the strict positivity set of a nonnegative free lattice
function. -/
lemma exists_nonneg_positive_set {n : ℕ} {s : Set (Fin n → ℝ)}
    (hs : IsOpenPolyhedralCone s) :
    ∃ f : FVL (Fin n), 0 ≤ f ∧ s = {x | 0 < f x} := by
  rcases hs with ⟨k, r, forms, rfl⟩
  let l (i : Fin k) (j : Fin (r i + 1)) : FVL (Fin n) :=
    ⟨forms i j, (mem_free_iff _).mpr ⟨(forms i j).continuous_of_finiteDimensional,
      fun t _ x ↦ (forms i j).map_smul t x,
      1, fun _ ↦ forms i j, fun _ ↦ ⟨0, rfl⟩⟩⟩
  let g (i : Fin k) := Finset.univ.inf' Finset.univ_nonempty (l i) ⊔ 0
  refine ⟨∑ i, g i, Finset.sum_nonneg (fun i _ ↦ le_sup_right), Set.ext fun x ↦ ?_⟩
  change (∃ i, ∀ j, 0 < forms i j x) ↔
    0 < (FVL.concreteSublattice (Fin n)).toSubmodule.subtype (∑ i, g i) x
  simp only [map_sum, Finset.sum_apply, Submodule.subtype_apply]
  rw [Finset.sum_pos_iff_of_nonneg (fun i _ ↦ show 0 ≤ g i x from le_max_right _ _)]
  simp only [Finset.mem_univ, true_and, g, VectorSublattice.coe_sup, Pi.sup_apply,
    lt_sup_iff]
  change (∃ i, ∀ j, 0 < forms i j x) ↔ ∃ i,
    0 < (FVL.concreteSublattice (Fin n)).subtype
      (Finset.univ.inf' Finset.univ_nonempty (l i)) x ∨ 0 < (0 : ℝ)
  simp [map_finset_inf', Finset.inf'_apply, Finset.lt_inf'_iff, l]

/-- Open polyhedral cones are exactly the supports of nonnegative free lattice functions. -/
lemma isOpenPolyhedralCone_iff_support {n : ℕ} {s : Set (Fin n → ℝ)} :
    IsOpenPolyhedralCone s ↔ ∃ f : FVL (Fin n), 0 ≤ f ∧ s = Function.support f := by
  refine ⟨fun hs ↦ ?_, ?_⟩
  · obtain ⟨f, hf, hs⟩ := exists_nonneg_positive_set hs
    exact ⟨f, hf, hs.trans (Set.ext fun x ↦
      ⟨fun h ↦ ne_of_gt h, fun h ↦ lt_of_le_of_ne (hf x) (Ne.symm h)⟩)⟩
  · rintro ⟨f, hf, rfl⟩
    exact (Set.ext fun x ↦ ⟨fun h ↦ ne_of_gt h,
      fun h ↦ lt_of_le_of_ne (hf x) (Ne.symm h)⟩ :
      {x | 0 < f x} = Function.support f) ▸ isOpenPolyhedralCone_positive f

/-- Eliminates one real variable from finitely many non-strict linear inequalities by
comparing all lower and upper bounds. -/
private lemma scalar_inequalities_iff {ι : Type*} [Finite ι] (a b : ι → ℝ) :
    (∃ t : ℝ, ∀ i, 0 ≤ a i * t + b i) ↔
      (∀ i, a i = 0 → 0 ≤ b i) ∧
      ∀ i j, 0 < a i → a j < 0 → 0 ≤ a i * b j - a j * b i := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨fun i hi ↦ by simpa only [hi, zero_mul, zero_add] using ht i,
      fun i j hi hj ↦ ?_⟩
    nlinarith [mul_nonneg hi.le (ht j), mul_nonneg (neg_nonneg.mpr hj.le) (ht i)]
  · rintro ⟨hzero, hpair⟩
    have hbounds (i : {i // 0 < a i}) (j : {j // a j < 0}) :
        -b i.val / a i.val ≤ b j.val / (-a j.val) := by
      apply (div_le_div_iff₀ i.property (neg_pos.mpr j.property)).mpr
      nlinarith [hpair i.val j.val i.property j.property]
    obtain ⟨t, htL, htU⟩ := exists_between_finite_families _ _ hbounds
    refine ⟨t, fun i ↦ ?_⟩
    rcases lt_trichotomy (a i) 0 with hi | hi | hi
    · have hi' := (le_div_iff₀ (neg_pos.mpr hi)).mp (htU ⟨i, hi⟩)
      nlinarith
    · simpa only [hi, zero_mul, zero_add] using hzero i hi
    · have hi' := (div_le_iff₀ hi).mp (htL ⟨i, hi⟩)
      nlinarith

/-- Eliminates a strictly positive real variable from finitely many non-strict linear
inequalities, recording the additional positivity conditions. -/
lemma positive_scalar_inequalities_iff {ι : Type*} [Finite ι] (a b : ι → ℝ) :
    (∃ t : ℝ, 0 < t ∧ ∀ i, 0 ≤ a i * t + b i) ↔
      (∀ i, a i = 0 → 0 ≤ b i) ∧
      (∀ i j, 0 < a i → a j < 0 → 0 ≤ a i * b j - a j * b i) ∧
      ∀ i, a i < 0 → 0 < b i := by
  constructor
  · rintro ⟨t, ht, h⟩
    have hw := (scalar_inequalities_iff a b).mp ⟨t, h⟩
    refine ⟨hw.1, hw.2, fun i hi ↦ ?_⟩
    nlinarith [h i, mul_neg_of_neg_of_pos hi ht]
  · rintro ⟨hzero, hpair, hneg⟩
    let u (i : {i // a i < 0}) := b i.val / (-a i.val)
    let s := insert (1 : ℝ) (Set.range u)
    have hs : s.Finite := (Set.finite_range u).insert 1
    have hsne : s.Nonempty := Set.insert_nonempty 1 _
    have hε : 0 < sInf s := (hs.lt_csInf_iff hsne).mpr (by
      rintro z (rfl | ⟨i, rfl⟩)
      · exact zero_lt_one
      · exact div_pos (hneg i.val i.property) (neg_pos.mpr i.property))
    obtain ⟨t, ht⟩ := (scalar_inequalities_iff a b).mpr ⟨hzero, hpair⟩
    refine ⟨max t (sInf s), hε.trans_le (le_max_right _ _), fun i ↦ ?_⟩
    rcases lt_or_ge (a i) 0 with hi | hi
    · have hbound : sInf s ≤ u ⟨i, hi⟩ := csInf_le hs.bddBelow (Or.inr ⟨⟨i, hi⟩, rfl⟩)
      have hεi := (le_div_iff₀ (neg_pos.mpr hi)).mp hbound
      rcases le_total t (sInf s) with h | h
      · rw [max_eq_right h]
        dsimp [u] at hεi
        nlinarith
      · simpa only [max_eq_left h] using ht i
    · have := mul_le_mul_of_nonneg_left (le_max_left t (sInf s)) hi
      linarith [ht i]

/-- Projection of a finite homogeneous linear inequality system is again described by finitely
many homogeneous linear inequalities. -/
lemma projected_linear_inequalities {Y : Type*} [AddCommGroup Y] [Module ℝ Y]
    {n : ℕ} {ι : Type*} [Finite ι] (a : ι → Fin n → ℝ) (b : ι → Y →ₗ[ℝ] ℝ) :
    ∃ (k : ℕ) (forms : Fin k → Y →ₗ[ℝ] ℝ), ∀ y,
      (∃ x : Fin n → ℝ, ∀ i, 0 ≤ ∑ j, a i j * x j + b i y) ↔
        ∀ j, 0 ≤ forms j y := by
  classical
  induction n generalizing ι with
  | zero =>
    let := Fintype.ofFinite ι
    refine ⟨Fintype.card ι, fun j ↦ b ((Fintype.equivFin ι).symm j), fun y ↦ ?_⟩
    simpa using ((Fintype.equivFin ι).symm.surjective.forall
      (p := fun i ↦ 0 ≤ b i y))
  | succ n ih =>
    let I := {i : ι // a i 0 = 0} ⊕
      ({i : ι // 0 < a i 0} × {j : ι // a j 0 < 0})
    let A : I → Fin n → ℝ := Sum.elim
      (fun i j ↦ a i.val j.succ)
      (fun p j ↦ a p.1.val 0 * a p.2.val j.succ - a p.2.val 0 * a p.1.val j.succ)
    let B : I → Y →ₗ[ℝ] ℝ := Sum.elim (fun i ↦ b i.val)
      (fun p ↦ a p.1.val 0 • b p.2.val - a p.2.val 0 • b p.1.val)
    obtain ⟨k, forms, hforms⟩ := ih A B
    refine ⟨k, forms, fun y ↦ ?_⟩
    rw [← hforms]
    simp only [Fin.exists_fin_succ_pi, Fin.sum_univ_succ,
      Fin.cons_zero, Fin.cons_succ, add_assoc]
    rw [exists_comm]
    refine exists_congr fun x ↦ ?_
    rw [scalar_inequalities_iff]
    simp only [I, Sum.forall, Prod.forall, Subtype.forall, A, B,
      Sum.elim_inl, Sum.elim_inr, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, sub_mul, Finset.sum_sub_distrib,
      mul_assoc, ← Finset.mul_sum, mul_add, sub_add_sub_comm]
    exact and_congr Iff.rfl ⟨fun h i hi j hj ↦ h i j hi hj,
      fun h i j hi hj ↦ h i hi j hj⟩

/-- A closed polyhedral cone is topologically closed. -/
private lemma closedPolyhedral_isClosed {n : ℕ} {s : Set (Fin n → ℝ)}
    (hs : IsClosedPolyhedralCone s) : IsClosed s := by
  rcases hs with ⟨k, cones, hcones, rfl⟩
  apply isClosed_iUnion_of_finite
  intro i
  obtain ⟨forms, hforms⟩ := hcones i
  rw [← hforms]
  change IsClosed {x | ∀ f ∈ forms, 0 ≤ f x}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter (fun f ↦ isClosed_iInter (fun _ ↦
    isClosed_le continuous_const f.continuous_of_finiteDimensional))

/-- A finite union of closed polyhedral cones is a closed polyhedral cone. -/
private lemma closedPolyhedral_finite_union {n : ℕ} {ι : Type*} [Finite ι]
    (s : ι → Set (Fin n → ℝ)) (hs : ∀ i, IsClosedPolyhedralCone (s i)) :
    IsClosedPolyhedralCone (⋃ i, s i) := by
  classical
  let := Fintype.ofFinite ι
  choose k cones hcones heq using hs
  let I := Σ i, Fin (k i)
  let e := (Fintype.equivFin I).symm
  refine ⟨Fintype.card I, fun j ↦ cones (e j).1 (e j).2,
    fun j ↦ hcones (e j).1 (e j).2, Set.ext fun x ↦ ?_⟩
  simp only [Set.mem_iUnion, heq]
  rw [← e.surjective.exists (p := fun p : I ↦ x ∈ (cones p.1 p.2 : Set (Fin n → ℝ)))]
  exact ⟨fun ⟨i, j, h⟩ ↦ ⟨⟨i, j⟩, h⟩, fun ⟨⟨i, j⟩, h⟩ ↦ ⟨i, j, h⟩⟩

/-- Projecting a set defined by finitely many homogeneous linear inequalities produces a
closed polyhedral cone. -/
private lemma closedPolyhedral_projected_linear_maps {n m : ℕ} {ι : Type*} [Finite ι]
    (L : ι → (Fin n → ℝ) →ₗ[ℝ] ℝ) (b : ι → (Fin m → ℝ) →ₗ[ℝ] ℝ) :
    IsClosedPolyhedralCone {y | ∃ x : Fin n → ℝ, ∀ i, 0 ≤ L i x + b i y} := by
  have hL (i : ι) (x : Fin n → ℝ) : L i x = ∑ j, L i (Pi.single j 1) * x j := by
    simpa only [map_sum, map_smul, smul_eq_mul, mul_comm]
      using congrArg (L i) (pi_eq_sum_univ' x)
  obtain ⟨k, forms, hforms⟩ := projected_linear_inequalities
    (fun i j ↦ L i (Pi.single j 1)) b
  refine ⟨1, fun _ ↦ PointedCone.dual .id (Set.range forms),
    fun _ ↦ PointedCone.DualFG.dual_of_finite .id (Set.finite_range forms), ?_⟩
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_const, SetLike.mem_coe,
    PointedCone.mem_dual, Set.forall_mem_range, LinearMap.id_apply]
  rw [← hforms]
  exact exists_congr (fun x ↦ forall_congr' (fun i ↦ by rw [hL]))

/-- A linear image of a tuple of finite suprema of linear forms has closed polyhedral range. -/
private lemma closedPolyhedral_linear_image_suprema {n k m : ℕ}
    (s : Fin k → LLexpr.SupLinearCombination n)
    (T : (Fin k → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    IsClosedPolyhedralCone (Set.range (fun x : Fin n → ℝ ↦ T (fun i ↦ (s i).eval x))) := by
  classical
  let L : (Fin n → ℝ) → (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    (Fintype.bilinearCombination ℝ ℝ).flip
  let C := ∀ i, ↥(s i).coeffs
  let J := (Σ i, ↥(s i).coeffs) ⊕ (Fin m × Bool)
  let V (c : C) : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ) := LinearMap.pi (fun i ↦ L (c i).val)
  let H (c : C) : J → (Fin n → ℝ) →ₗ[ℝ] ℝ := Sum.elim
    (fun p ↦ L (c p.1).val - L p.2.val)
    (fun p ↦ cond p.2 ((LinearMap.proj p.1).comp (T.comp (V c)))
      (-((LinearMap.proj p.1).comp (T.comp (V c)))))
  let b : J → (Fin m → ℝ) →ₗ[ℝ] ℝ := Sum.elim (fun _ ↦ 0)
    (fun p ↦ cond p.2 (-LinearMap.proj p.1) (LinearMap.proj p.1))
  suffices heq : Set.range (fun x : Fin n → ℝ ↦ T (fun i ↦ (s i).eval x)) =
      ⋃ c : C, {y | ∃ x : Fin n → ℝ, ∀ j, 0 ≤ H c j x + b j y} from
    heq.symm ▸ closedPolyhedral_finite_union _
      (fun c ↦ closedPolyhedral_projected_linear_maps (H c) b)
  ext y
  simp only [Set.mem_range, Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, rfl⟩
    have hc (i : Fin k) : ∃ c : ↥(s i).coeffs, (s i).eval x = L c.val x :=
      let ⟨c, hc, heq⟩ := Finset.exists_mem_eq_sup' (s i).nonempty
        (Fintype.linearCombination ℝ x)
      ⟨⟨c, hc⟩, heq⟩
    choose c hc using hc
    have hV : V c x = (fun i ↦ (s i).eval x) := funext (fun i ↦ (hc i).symm)
    refine ⟨c, x, ?_⟩
    rintro (⟨i, d⟩ | ⟨j, _ | _⟩)
    · change 0 ≤ L (c i).val x - L d.val x + 0
      exact add_nonneg (sub_nonneg.mpr
        ((Finset.le_sup' (Fintype.linearCombination ℝ x) d.property).trans_eq (hc i))) le_rfl
    · simp [H, b, hV]
    · simp [H, b, hV]
  · rintro ⟨c, x, hx⟩
    have hs (i : Fin k) : (s i).eval x = L (c i).val x := by
      apply le_antisymm
      · refine Finset.sup'_le (s i).nonempty _ (fun d hd ↦ ?_)
        exact sub_nonneg.mp (show 0 ≤ L (c i).val x - L d x from
          by simpa only [H, b, Sum.elim_inl, LinearMap.sub_apply, LinearMap.zero_apply, add_zero]
            using hx (.inl ⟨i, ⟨d, hd⟩⟩))
      · exact Finset.le_sup' (Fintype.linearCombination ℝ x) (c i).property
    refine ⟨x, funext fun j ↦ ?_⟩
    rw [show (fun i ↦ (s i).eval x) = V c x from funext hs]
    have hp : 0 ≤ T (V c x) j + -y j := hx (.inr (j, true))
    have hn : 0 ≤ -(T (V c x) j) + y j := hx (.inr (j, false))
    linarith

/-- The joint range of finitely many free lattice functions is a closed polyhedral cone. -/
lemma closedPolyhedral_range {n m : ℕ} (g : Fin m → FVL (Fin n)) :
    IsClosedPolyhedralCone (Set.range (fun x : Fin n → ℝ ↦ fun i ↦ g i x)) := by
  choose N hN using fun i ↦ free_normal_form (g i)
  let s : Fin (m + m) → LLexpr.SupLinearCombination n :=
    Fin.append (fun i ↦ (N i).pos) (fun i ↦ (N i).neg)
  let p (j : Fin (m + m)) : (Fin (m + m) → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj j
  let T : (Fin (m + m) → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
    LinearMap.pi (fun i ↦ p (i.castAdd m) - p (i.natAdd m))
  have heval (x : Fin n → ℝ) : T (fun i ↦ (s i).eval x) = (fun i ↦ g i x) := by
    funext i
    change (s (i.castAdd m)).eval x - (s (i.natAdd m)).eval x = g i x
    simpa only [s, Fin.append_left, Fin.append_right, LLexpr.NormalForm.eval] using hN i x
  simpa only [heval] using closedPolyhedral_linear_image_suprema s T

/-- The joint range of a pair of free lattice functions is closed. -/
private lemma isClosed_pair_range {n : ℕ} (f g : FVL (Fin n)) :
    IsClosed (Set.range (fun x : Fin n → ℝ ↦ ![f x, g x])) := by
  convert closedPolyhedral_isClosed (closedPolyhedral_range ![f, g]) using 1
  congr 1
  funext x i
  fin_cases i <;> rfl

/-- In a finitely generated free lattice, inclusion of supports implies domination of absolute
values by a nonnegative scalar. -/
private lemma support_domination {n : ℕ} (f g : FVL (Fin n))
    (hfg : Function.support f ⊆ Function.support g) :
    ∃ c : ℝ, 0 ≤ c ∧ |f| ≤ c • |g| := by
  have hz : ![(1 : ℝ), 0] ∉ Set.range (fun x : Fin n → ℝ ↦ ![|f x|, |g x|]) := by
    rintro ⟨x, hx⟩
    have hx0 : |f x| = 1 := congrFun hx 0
    have hx1 : |g x| = 0 := congrFun hx 1
    exact hfg (abs_pos.mp (hx0.symm ▸ zero_lt_one)) (abs_eq_zero.mp hx1)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp
    (isClosed_pair_range |f| |g|).isOpen_compl _ hz
  refine ⟨ε⁻¹, inv_nonneg.mpr hε.le, fun x ↦ ?_⟩
  change |f x| ≤ ε⁻¹ * |g x|
  by_contra! hx
  have hfpos : 0 < |f x| := (mul_nonneg (inv_nonneg.mpr hε.le) (abs_nonneg _)).trans_lt hx
  have hsmall : |f x|⁻¹ * |g x| < ε :=
    (inv_mul_lt_iff₀ hfpos).mpr (by simpa only [mul_comm] using (inv_mul_lt_iff₀ hε).mp hx)
  have hscale (v : FVL (Fin n)) : |v (|f x|⁻¹ • x)| = |f x|⁻¹ * |v x| :=
    ((mem_free_iff _).mp (|v|).property).2.1 _ (inv_nonneg.mpr hfpos.le) x
  refine hball (show ![|f (|f x|⁻¹ • x)|, |g (|f x|⁻¹ • x)|] ∈
    Metric.ball ![1, 0] ε from ?_) ⟨|f x|⁻¹ • x, rfl⟩
  apply (dist_pi_lt_iff hε).mpr
  intro j
  fin_cases j
  · simpa [hscale, hfpos.ne'] using hε
  · simpa [Real.dist_eq, hscale, abs_mul] using hsmall

/-- An ideal contains any free function whose support is contained in the support of one of
its elements. -/
lemma ideal_mem_of_support_subset {n : ℕ} (J : OrderIdeal (FVL (Fin n)))
    {f g : FVL (Fin n)} (hg : g ∈ J)
    (hfg : Function.support f ⊆ Function.support g) : f ∈ J := by
  obtain ⟨c, _, hbound⟩ := support_domination f g hfg
  exact J.mem_of_abs_mem (J.solid (J.smul_mem c (J.abs_mem hg)) (abs_nonneg _) hbound)

/-- The complement of an open polyhedral cone is a closed polyhedral cone. -/
lemma closedPolyhedral_compl_of_openPolyhedral {n : ℕ}
    {s : Set (Fin n → ℝ)} (hs : IsOpenPolyhedralCone s) :
    IsClosedPolyhedralCone sᶜ := by
  classical
  rcases hs with ⟨k, r, forms, rfl⟩
  let I := ∀ i : Fin k, Fin (r i + 1)
  let cones (c : I) : PointedCone ℝ (Fin n → ℝ) :=
    PointedCone.dual .id (Set.range (fun i ↦ -forms i (c i)))
  refine ⟨Fintype.card I, fun j ↦ cones ((Fintype.equivFin I).symm j),
    fun j ↦ PointedCone.DualFG.dual_of_finite .id
      (Set.finite_range (fun i ↦ -forms i (((Fintype.equivFin I).symm j) i))),
    Set.ext fun x ↦ ?_⟩
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [(Fintype.equivFin I).surjective.exists]
  simp only [Equiv.symm_apply_apply, cones, SetLike.mem_coe, PointedCone.mem_dual,
    Set.forall_mem_range, LinearMap.id_apply, LinearMap.neg_apply, neg_nonneg,
    not_exists, not_forall, not_lt]
  exact Classical.skolem

/-- The complement of a closed polyhedral cone containing zero is an open polyhedral cone. -/
lemma openPolyhedral_compl_of_closedPolyhedral {n : ℕ}
    {s : Set (Fin n → ℝ)} (hs : IsClosedPolyhedralCone s) (hzero : 0 ∈ s) :
    IsOpenPolyhedralCone sᶜ := by
  classical
  rcases hs with ⟨k, cones, hcones, hs⟩
  obtain ⟨i, _⟩ := Set.mem_iUnion.mp (hs ▸ hzero)
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Nat.zero_lt_of_lt i.isLt))
  choose sets hsets using hcones
  let I := ∀ i : Fin (r + 1), ↥(sets i)
  refine ⟨Fintype.card I, fun _ ↦ r,
    fun j i ↦ -(((Fintype.equivFin I).symm j) i).val, Set.ext fun x ↦ ?_⟩
  simp only [hs, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq,
    ← hsets, SetLike.mem_coe, PointedCone.mem_dual, LinearMap.id_apply,
    LinearMap.neg_apply, neg_pos, not_exists, not_forall, not_le]
  rw [(Fintype.equivFin I).surjective.exists]
  simpa only [Equiv.symm_apply_apply, Subtype.exists] using
    (Classical.skolem : (∀ i, ∃ c : ↥(sets i), c.val x < 0) ↔
      ∃ c : I, ∀ i, (c i).val x < 0)

/-- The closure of a nonempty region of finitely many strict homogeneous inequalities is
obtained by replacing them with non-strict inequalities. -/
private lemma closure_strict_inequalities {n : ℕ} {ι : Type*} [Finite ι]
    (L : ι → (Fin n → ℝ) →ₗ[ℝ] ℝ) (hne : {x | ∀ i, 0 < L i x}.Nonempty) :
    closure {x | ∀ i, 0 < L i x} = {x | ∀ i, 0 ≤ L i x} := by
  apply subset_antisymm
  · refine closure_minimal (t := {x | ∀ i, 0 ≤ L i x}) (fun x hx i ↦ (hx i).le) ?_
    simpa only [Set.ofPred_forall] using isClosed_iInter
      (fun i ↦ isClosed_le continuous_const (L i).continuous_of_finiteDimensional)
  · obtain ⟨x, hx⟩ := hne
    intro y hy
    have hcont : Continuous (fun t : ℝ ↦ y + t • x) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hzero : (0 : ℝ) ∈ closure (Set.Ioi 0) := by simp
    have hcl := mem_closure_image hcont.continuousAt hzero
    have hsub : (fun t : ℝ ↦ y + t • x) '' Set.Ioi 0 ⊆ {z | ∀ i, 0 < L i z} := by
      rintro _ ⟨t, ht, rfl⟩ i
      simpa only [map_add, map_smul, smul_eq_mul] using
        add_pos_of_nonneg_of_pos (hy i) (mul_pos ht (hx i))
    simpa only [zero_smul, add_zero] using closure_mono hsub hcl

/-- The closure of an open polyhedral cone is closed polyhedral. -/
lemma closedPolyhedral_closure {n : ℕ} {s : Set (Fin n → ℝ)}
    (hs : IsOpenPolyhedralCone s) : IsClosedPolyhedralCone (closure s) := by
  classical
  rcases hs with ⟨k, r, forms, rfl⟩
  let I := {i : Fin k // {x | ∀ j, 0 < forms i j x}.Nonempty}
  let cones (i : I) : PointedCone ℝ (Fin n → ℝ) :=
    PointedCone.dual .id (Set.range (forms i.val))
  refine ⟨Fintype.card I, fun j ↦ cones ((Fintype.equivFin I).symm j),
    fun j ↦ PointedCone.DualFG.dual_of_finite .id
      (Set.finite_range (forms (((Fintype.equivFin I).symm j).val))), ?_⟩
  rw [show {x | ∃ i, ∀ j, 0 < forms i j x} = ⋃ i, {x | ∀ j, 0 < forms i j x} by
    ext x; simp, closure_iUnion_of_finite]
  ext x
  simp only [Set.mem_iUnion]
  rw [(Fintype.equivFin I).surjective.exists]
  simp only [Equiv.symm_apply_apply, cones, SetLike.mem_coe, PointedCone.mem_dual,
    Set.forall_mem_range, LinearMap.id_apply]
  constructor
  · rintro ⟨i, hi⟩
    have hne : {x | ∀ j, 0 < forms i j x}.Nonempty :=
      closure_nonempty_iff.mp ⟨x, hi⟩
    rw [closure_strict_inequalities (forms i) hne] at hi
    exact ⟨⟨i, hne⟩, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i.val, (closure_strict_inequalities (forms i.val) i.property).symm ▸ hi⟩

/-- The inverse image of a closed polyhedral cone under a linear map is closed polyhedral. -/
lemma closedPolyhedral_preimage {n m : ℕ} {s : Set (Fin m → ℝ)}
    (hs : IsClosedPolyhedralCone s) (T : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    IsClosedPolyhedralCone (T ⁻¹' s) := by
  classical
  rcases hs with ⟨k, cones, hcones, rfl⟩
  choose sets hsets using hcones
  refine ⟨k, fun i ↦ PointedCone.dual .id ((sets i).image (fun f ↦ f.comp T)),
    fun i ↦ PointedCone.DualFG.dual_of_finset .id ((sets i).image (fun f ↦ f.comp T)), ?_⟩
  ext x
  simp only [Set.mem_preimage, Set.mem_iUnion, SetLike.mem_coe, ← hsets,
    PointedCone.mem_dual, LinearMap.id_apply, Finset.coe_image, Set.forall_mem_image,
    LinearMap.comp_apply]

end VectorLattice.ConeRepresentation
