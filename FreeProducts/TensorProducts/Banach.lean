/-
Authors: Gonzalo Martínez-Fernández
-/

import FreeProducts.TensorProducts.Archimedean

/-!
# Projective Banach lattice tensor products

The Archimedean tensor core of two Banach lattices carries the projective lattice norm,
defined by positive elementary-tensor majorants and their norm costs. Completing this
norm gives `Tensor`. Order approximation makes the span of elementary tensors dense;
every bounded positive bilinear map then extends uniquely to a positive operator with
the same norm. `tensorProduct` bundles this universal property, and `tensorPairing`
provides the pairing used in the free-product constructions.
-/

universe u

namespace VectorLattice.TensorProduct

/-! ### The projective lattice norm -/

variable {E F : Type u}
  [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
  [NormedAddCommGroup F] [Lattice F] [IsOrderedAddMonoid F] [BanachLattice F]
variable (P : VectorLattice.TensorProduct E F)

/-- The projective lattice norm is obtained from positive elementary-tensor
majorants and their total norm cost. -/
noncomputable def projectiveNorm (u : P.Carrier) : ℝ :=
  sInf {r : ℝ | ∃ (n : ℕ) (x : Fin n → E) (y : Fin n → F),
    (∀ i, 0 ≤ x i) ∧ (∀ i, 0 ≤ y i) ∧
    |u| ≤ ∑ i, P.tmul (x i) (y i) ∧ r = ∑ i, ‖x i‖ * ‖y i‖}

end VectorLattice.TensorProduct

namespace BanachLattice

section Projective

variable (E F : Type u)
  [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
  [NormedAddCommGroup F] [Lattice F] [IsOrderedAddMonoid F] [BanachLattice F]

/-- A Fremlin projective tensor product universally linearizes bounded positive
bilinear maps by positive operators, preserving their norms. -/
structure TensorProduct where
  Carrier : Type u
  [normedAddCommGroup : NormedAddCommGroup Carrier]
  [lattice : Lattice Carrier]
  [isOrderedAddMonoid : IsOrderedAddMonoid Carrier]
  [banachLattice : BanachLattice Carrier]
  tmul : E →ₗ[ℝ] (F →ₗ[ℝ] Carrier)
  tmul_isLatticeBimorphism : VectorLattice.IsLatticeBimorphism tmul
  norm_tmul_le : ∀ x y, ‖tmul x y‖ ≤ ‖x‖ * ‖y‖
  dense_span_tmul :
    Dense (Submodule.span ℝ
      (Set.range (fun p : E × F ↦ tmul p.1 p.2)) : Set Carrier)
  universal :
    ∀ (G : Type u) [NormedAddCommGroup G] [Lattice G]
      [IsOrderedAddMonoid G] [BanachLattice G]
      (b : E →L[ℝ] (F →L[ℝ] G)),
      (∀ x y, 0 ≤ x → 0 ≤ y → 0 ≤ b x y) →
      ∃! T : Carrier →L[ℝ] G,
        Positive T.toLinearMap ∧
        (∀ x y, T (tmul x y) = b x y) ∧ ‖T‖ = ‖b‖

attribute [instance] TensorProduct.normedAddCommGroup TensorProduct.lattice
  TensorProduct.isOrderedAddMonoid TensorProduct.banachLattice

namespace TensorProduct

variable {E F}
variable {G H : Type u}
  [NormedAddCommGroup G] [Lattice G] [IsOrderedAddMonoid G] [BanachLattice G]
  [NormedAddCommGroup H] [Lattice H] [IsOrderedAddMonoid H] [BanachLattice H]
variable (P : TensorProduct E F)

/-- The extension of a bounded positive bilinear map. -/
noncomputable def lift (b : E →L[ℝ] (F →L[ℝ] G))
    (hb : ∀ x y, 0 ≤ x → 0 ≤ y → 0 ≤ b x y) : P.Carrier →L[ℝ] G :=
  Classical.choose (P.universal G b hb)

end TensorProduct

end Projective

end BanachLattice

namespace BanachLattice.FreeProduct

variable (E F : Type u)
  [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [BanachLattice E]
  [NormedAddCommGroup F] [Lattice F] [IsOrderedAddMonoid F] [BanachLattice F]

namespace ProjectiveTensor

/-- The projective lattice norm, defined by costs of positive elementary majorants. -/
noncomputable instance instNorm : Norm (Core E F) where
  norm z := (algebraicTensor E F).projectiveNorm z

/-- A finite elementary-tensor majorant bounds the ambient norm by the sum of products of the
factor norms. -/
private lemma core_norm_le_cost (z : Core E F) {n : ℕ} (x : Fin n → E) (y : Fin n → F)
    (h : |z| ≤ ∑ i, coreTmul E F (x i) (y i)) :
    ‖coreInclusion E F z‖ ≤ ∑ i, ‖x i‖ * ‖y i‖ := by
  have hb := (coreInclusion E F).monotone h
  rw [(coreInclusion E F).map_abs, map_sum] at hb
  have hn := norm_le_norm_of_abs_le_abs (hb.trans (le_abs_self _))
  refine (hn.trans (norm_sum_le _ _)).trans_eq ?_
  exact Finset.sum_congr rfl (fun i _ ↦ completedPairing_norm E F (x i) (y i))

/-- The possible sums of factor-norm products in positive elementary-tensor majorants of a
core element. -/
private def tensorCosts (z : Core E F) : Set ℝ :=
  {r | ∃ (n : ℕ) (x : Fin n → E) (y : Fin n → F),
    (∀ i, 0 ≤ x i) ∧ (∀ i, 0 ≤ y i) ∧
    |z| ≤ ∑ i, coreTmul E F (x i) (y i) ∧ r = ∑ i, ‖x i‖ * ‖y i‖}

/-- Every tensor-majorant cost is nonnegative. -/
private lemma cost_nonneg {z : Core E F} {r : ℝ} (h : r ∈ tensorCosts E F z) :
    0 ≤ r := by
  obtain ⟨n, x, y, _, _, _, rfl⟩ := h
  exact Finset.sum_nonneg (fun i _ ↦ mul_nonneg (norm_nonneg (x i)) (norm_nonneg (y i)))

/-- The product of the factor norms is an admissible cost for an elementary tensor. -/
private lemma cost_tmul (x : E) (y : F) :
    ‖x‖ * ‖y‖ ∈ tensorCosts E F (coreTmul E F x y) := by
  refine ⟨1, fun _ ↦ |x|, fun _ ↦ |y|, fun _ ↦ abs_nonneg x,
    fun _ ↦ abs_nonneg y, ?_, ?_⟩
  · simp only [Fin.sum_univ_one]
    exact (show |coreTmul E F x y| = coreTmul E F |x| |y| from
      Subtype.ext (completedPairing_abs E F x y)).le
  · simp only [Fin.sum_univ_one, norm_abs_eq_norm]

/-- The projective lattice norm of an elementary tensor is the product of the factor norms. -/
private lemma core_tmul_norm (x : E) (y : F) :
    ‖coreTmul E F x y‖ = ‖x‖ * ‖y‖ := by
  change sInf (tensorCosts E F (coreTmul E F x y)) = ‖x‖ * ‖y‖
  refine le_antisymm (csInf_le ⟨0, fun _ h ↦ cost_nonneg E F h⟩ (cost_tmul E F x y))
    (le_csInf ⟨_, cost_tmul E F x y⟩ ?_)
  rintro r ⟨n, a, b, _, _, h, rfl⟩
  exact (completedPairing_norm E F x y).symm.trans_le
    (core_norm_le_cost E F (coreTmul E F x y) a b h)

/-- The concrete pairing of two nonnegative elements is nonnegative. -/
private lemma pairing_nonneg {x : E} {y : F} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ (rankOnePairing E F).tmul x y :=
  (((rankOnePairing E F).isVecLatHom_left y hy).mk'
    (fun x ↦ (rankOnePairing E F).tmul x y)).map_nonneg hx

/-- The sum of two positive elementary pairings is bounded by the pairing of the sums of their
factors. -/
private lemma pairing_add_le {x u : E} {y v : F}
    (hx : 0 ≤ x) (hu : 0 ≤ u) (hy : 0 ≤ y) (hv : 0 ≤ v) :
    (rankOnePairing E F).tmul x y + (rankOnePairing E F).tmul u v ≤
      (rankOnePairing E F).tmul (x + u) (y + v) := by
  simp only [map_add, add_apply]
  exact add_le_add (le_add_of_nonneg_right (pairing_nonneg E F hu hy))
    (le_add_of_nonneg_left (pairing_nonneg E F hx hv))

/-- The order ideal of elements dominated by a single pairing of positive vectors. -/
private noncomputable def majorantIdeal : OrderIdeal (rankOnePairing E F).Carrier := by
  refine OrderIdeal.ofSolid
    { carrier := {z | ∃ (x : E) (y : F), 0 ≤ x ∧ 0 ≤ y ∧
        |z| ≤ (rankOnePairing E F).tmul x y}
      zero_mem' := ?_
      add_mem' := ?_
      smul_mem' := ?_ } ?_
  · rintro z w ⟨x, y, hx, hy, hz⟩ ⟨u, v, hu, hv, hw⟩
    exact ⟨x + u, y + v, add_nonneg hx hu, add_nonneg hy hv,
      (abs_add_le z w).trans ((add_le_add hz hw).trans (pairing_add_le E F hx hu hy hv))⟩
  · exact ⟨0, 0, le_rfl, le_rfl, by simp⟩
  · rintro c z ⟨x, y, hx, hy, hz⟩
    refine ⟨|c| • x, y, smul_nonneg (abs_nonneg c) hx, hy, ?_⟩
    simpa only [abs_smul', map_smul, smul_apply] using
      smul_le_smul_of_nonneg_left hz (abs_nonneg c)
  · rintro z w ⟨x, y, hx, hy, hz⟩ hw
    exact ⟨x, y, hx, hy, hw.trans hz⟩

/-- Every tensor-core element admits a finite positive tensor majorant and therefore has a
nonempty cost set. -/
private lemma costs_nonempty (z : Core E F) : (tensorCosts E F z).Nonempty := by
  have hle : coreSublattice E F ≤ (majorantIdeal E F).toVectorSublattice := by
    apply VectorSublattice.generated_le
    rintro _ ⟨⟨x, y⟩, rfl⟩
    exact ⟨|x|, |y|, abs_nonneg x, abs_nonneg y, (completedPairing_abs E F x y).le⟩
  obtain ⟨x, y, hx, hy, h⟩ := hle (z : coreSublattice E F).property
  refine ⟨‖x‖ * ‖y‖, 1, fun _ ↦ x, fun _ ↦ y, fun _ ↦ hx, fun _ ↦ hy, ?_, ?_⟩
  · simp only [Fin.sum_univ_one]
    exact h
  · simp only [Fin.sum_univ_one]

/-- The projective lattice norm is bounded by each admissible tensor-majorant cost. -/
private lemma norm_le_cost {z : Core E F} {r : ℝ} (h : r ∈ tensorCosts E F z) :
    ‖z‖ ≤ r :=
  csInf_le ⟨0, fun _ hr ↦ cost_nonneg E F hr⟩ h

/-- The infimum defining the projective lattice norm is nonnegative. -/
private lemma projective_norm_nonneg (z : Core E F) : 0 ≤ ‖z‖ :=
  le_csInf (costs_nonempty E F z) (fun _ h ↦ cost_nonneg E F h)

/-- The projective lattice norm of zero is zero. -/
private lemma projective_norm_zero : ‖(0 : Core E F)‖ = 0 := by
  simpa only [map_zero, LinearMap.zero_apply, norm_zero, zero_mul] using core_tmul_norm E F 0 0

/-- The projective lattice norm dominates the norm inherited from the concrete rank-one model. -/
private lemma ambient_norm_le (z : Core E F) : ‖coreInclusion E F z‖ ≤ ‖z‖ := by
  refine le_csInf (costs_nonempty E F z) ?_
  rintro r ⟨n, x, y, _, _, h, rfl⟩
  exact core_norm_le_cost E F z x y h

/-- The projective lattice norm is monotone under domination of absolute values. -/
private lemma projective_norm_mono {z w : Core E F} (h : |z| ≤ |w|) : ‖z‖ ≤ ‖w‖ := by
  refine le_csInf (costs_nonempty E F w) ?_
  rintro r ⟨n, x, y, hx, hy, hw, rfl⟩
  exact norm_le_cost E F ⟨n, x, y, hx, hy, h.trans hw, rfl⟩

/-- Scaling a tensor element scales an admissible majorant cost by the absolute value of the
scalar. -/
private lemma cost_smul (c : ℝ) {z : Core E F} {r : ℝ}
    (h : r ∈ tensorCosts E F z) : |c| * r ∈ tensorCosts E F (c • z) := by
  obtain ⟨n, x, y, hx, hy, hz, rfl⟩ := h
  refine ⟨n, fun i ↦ |c| • x i, y,
    fun i ↦ smul_nonneg (abs_nonneg c) (hx i), hy, ?_, ?_⟩
  · simpa only [abs_smul', Finset.smul_sum, map_smul, LinearMap.smul_apply] using
      smul_le_smul_of_nonneg_left hz (abs_nonneg c)
  · simp only [norm_smul, Real.norm_eq_abs, abs_abs, mul_assoc, Finset.mul_sum]

/-- The projective norm of a scalar multiple is at most the absolute scalar times the original
norm. -/
private lemma projective_norm_smul_le (c : ℝ) (z : Core E F) :
    ‖c • z‖ ≤ |c| * ‖z‖ := by
  by_cases hc : c = 0
  · simp only [hc, zero_smul, projective_norm_zero, abs_zero, zero_mul, le_refl]
  · have hpos := abs_pos.mpr hc
    apply (div_le_iff₀' hpos).mp
    refine le_csInf (costs_nonempty E F z) ?_
    exact fun r hr ↦ (div_le_iff₀' hpos).mpr (norm_le_cost E F (cost_smul E F c hr))

/-- The projective lattice norm is absolutely homogeneous. -/
private lemma projective_norm_smul (c : ℝ) (z : Core E F) :
    ‖c • z‖ = ‖c‖ * ‖z‖ := by
  by_cases hc : c = 0
  · simp only [hc, zero_smul, projective_norm_zero, norm_zero, zero_mul]
  · rw [Real.norm_eq_abs]
    refine le_antisymm (projective_norm_smul_le E F c z) ?_
    have h := mul_le_mul_of_nonneg_left (projective_norm_smul_le E F c⁻¹ (c • z))
      (abs_nonneg c)
    simpa only [inv_smul_smul₀ hc, abs_inv, ← mul_assoc,
      mul_inv_cancel₀ (abs_ne_zero.mpr hc), one_mul] using h

/-- Admissible costs for two elements add to an admissible cost for their sum. -/
private lemma cost_add {z w : Core E F} {r s : ℝ}
    (hr : r ∈ tensorCosts E F z) (hs : s ∈ tensorCosts E F w) :
    r + s ∈ tensorCosts E F (z + w) := by
  obtain ⟨n, x, y, hx, hy, hz, rfl⟩ := hr
  obtain ⟨m, a, b, ha, hb, hw, rfl⟩ := hs
  refine ⟨n + m, Fin.append x a, Fin.append y b, ?_, ?_, ?_, ?_⟩
  · exact Fin.addCases (fun i ↦ by simpa using hx i) (fun i ↦ by simpa using ha i)
  · exact Fin.addCases (fun i ↦ by simpa using hy i) (fun i ↦ by simpa using hb i)
  · simpa [Fin.sum_univ_add] using (abs_add_le z w).trans (add_le_add hz hw)
  · simp [Fin.sum_univ_add]

/-- The projective lattice norm satisfies the triangle inequality. -/
private lemma projective_norm_add_le (z w : Core E F) : ‖z + w‖ ≤ ‖z‖ + ‖w‖ := by
  apply (sub_le_iff_le_add).mp
  refine le_csInf (costs_nonempty E F z) ?_
  intro r hr
  rw [sub_le_comm]
  refine le_csInf (costs_nonempty E F w) ?_
  exact fun s hs ↦ (sub_le_iff_le_add').mpr (norm_le_cost E F (cost_add E F hr hs))

/-- Collects definiteness, homogeneity, and the triangle inequality into the normed-space
axioms for the tensor core. -/
private theorem projective_norm_core : NormedSpace.Core ℝ (Core E F) where
  norm_nonneg := projective_norm_nonneg E F
  norm_smul := projective_norm_smul E F
  norm_triangle := projective_norm_add_le E F
  norm_eq_zero_iff z := by
    constructor
    · intro hz
      have h := (ambient_norm_le E F z).trans_eq hz
      exact Subtype.ext (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))
    · rintro rfl
      exact projective_norm_zero E F

/-- The metric induced by the projective lattice norm. -/
noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (Core E F) :=
  NormedAddCommGroup.ofCore (projective_norm_core E F)

/-- The projective norm is compatible with the vector lattice structure. -/
noncomputable instance instNormedVectorLattice : NormedVectorLattice (Core E F) where
  solid {_ _} h := projective_norm_mono E F h
  norm_smul := projective_norm_smul E F

/-- The Banach lattice tensor product is the completion for the projective lattice norm. -/
abbrev Tensor := UniformSpace.Completion (Core E F)

/-- The canonical bilinear map into the projective completion. -/
noncomputable def tmul : E →L[ℝ] F →L[ℝ] Tensor E F :=
  ((coreTmul E F).compr₂
    UniformSpace.Completion.toComplₗᵢ.toLinearMap).mkContinuous₂ 1 (by
      intro x y
      change ‖(coreTmul E F x y : UniformSpace.Completion (Core E F))‖ ≤ 1 * ‖x‖ * ‖y‖
      simp only [UniformSpace.Completion.norm_coe, core_tmul_norm, one_mul, le_refl])

/-- Elementary tensors have the product of their factors' norms. -/
theorem norm_tmul (x : E) (y : F) :
    ‖tmul E F x y‖ = ‖x‖ * ‖y‖ := by
  change ‖(coreTmul E F x y : UniformSpace.Completion (Core E F))‖ = ‖x‖ * ‖y‖
  rw [UniformSpace.Completion.norm_coe, core_tmul_norm]

/-- The canonical bilinear map preserves absolute values in both factors. -/
theorem abs_tmul (x : E) (y : F) :
    |tmul E F x y| = tmul E F |x| |y| := by
  change |(coreTmul E F x y : UniformSpace.Completion (Core E F))| =
    (coreTmul E F |x| |y| : UniformSpace.Completion (Core E F))
  rw [← coe_abs_completion]
  exact congrArg (fun z : Core E F ↦ (z : UniformSpace.Completion (Core E F)))
    (Subtype.ext (completedPairing_abs E F x y))

/-- The completion inclusion sends linear combinations of core elementary tensors to linear
combinations of completed elementary tensors. -/
private lemma coe_mem_span_tmul {z : Core E F}
    (hz : z ∈ Submodule.span ℝ
      (Set.range (fun p : E × F ↦ coreTmul E F p.1 p.2))) :
    (z : Tensor E F) ∈ Submodule.span ℝ
      (Set.range (fun p : E × F ↦ tmul E F p.1 p.2)) := by
  let e := (UniformSpace.Completion.toComplₗᵢ : Core E F →ₗᵢ[ℝ] Tensor E F).toLinearMap
  have h : Submodule.span ℝ (Set.range (fun p : E × F ↦ coreTmul E F p.1 p.2)) ≤
      (Submodule.span ℝ (Set.range (fun p : E × F ↦ tmul E F p.1 p.2))).comap e := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x, y⟩, rfl⟩
    exact Submodule.subset_span ⟨(x, y), rfl⟩
  exact h hz

/-- Approximation in order by elementary-tensor linear combinations implies norm-closure
membership in the completed tensor space. -/
private lemma mem_closure_of_order_approx (z c : Core E F)
    (h : ∀ δ : ℝ, δ > 0 → ∃ w ∈ Submodule.span ℝ
      (Set.range (fun p : E × F ↦ coreTmul E F p.1 p.2)), |z - w| ≤ δ • c) :
    (z : Tensor E F) ∈ closure (Submodule.span ℝ
      (Set.range (fun p : E × F ↦ tmul E F p.1 p.2)) : Set (Tensor E F)) := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have hc : 0 < ‖c‖ + 1 := by positivity
  obtain ⟨w, hw, hzw⟩ := h (ε / (‖c‖ + 1)) (div_pos hε hc)
  refine ⟨w, coe_mem_span_tmul E F hw, ?_⟩
  rw [UniformSpace.Completion.dist_eq, dist_eq_norm]
  have hn := norm_le_norm_of_abs_le_abs (hzw.trans (le_abs_self _))
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hε hc)] at hn
  have heq := div_mul_cancel₀ ε (ne_of_gt hc)
  nlinarith [div_pos hε hc]

/-- Elementary tensors linearly span a dense subspace of the completion. -/
theorem dense_span_tmul :
    Dense (Submodule.span ℝ
      (Set.range (fun p : E × F ↦ tmul E F p.1 p.2)) : Set (Tensor E F)) := by
  have happrox (z : Core E F) : ∃ x : E, ∃ y : F, 0 ≤ x ∧ 0 ≤ y ∧
      ∀ δ : ℝ, 0 < δ → ∃ w ∈ Submodule.span ℝ
        (Set.range (fun p : E × F ↦ coreTmul E F p.1 p.2)),
          |z - w| ≤ δ • coreTmul E F x y := core_order_approx E F z
  intro z
  induction z using UniformSpace.Completion.induction_on
  · exact isClosed_closure
  · rename_i z
    obtain ⟨x, y, _, _, h⟩ := happrox z
    exact mem_closure_of_order_approx E F z (coreTmul E F x y) h

section PositiveExtension

variable {G : Type u} [NormedAddCommGroup G] [Lattice G]
  [IsOrderedAddMonoid G] [BanachLattice G]

/-- A positive linearization on the core is bounded by the bilinear norm times any admissible
tensor cost. -/
private lemma core_linearization_cost
    (b : E →L[ℝ] F →L[ℝ] G) (T : Core E F →ₗ[ℝ] G) (hT : Positive T)
    (hTb : ∀ x y, T (coreTmul E F x y) = b x y)
    {z : Core E F} {r : ℝ} (hr : r ∈ tensorCosts E F z) :
    ‖T z‖ ≤ ‖b‖ * r := by
  obtain ⟨n, x, y, _, _, hz, rfl⟩ := hr
  have h := (Positive.abs_le_map_abs hT z).trans ((Positive.monotone_iff.mpr hT) hz)
  simp only [map_sum, hTb] at h
  refine ((norm_le_norm_of_abs_le_abs (h.trans (le_abs_self _))).trans
    (norm_sum_le _ _)).trans ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ ↦ (b.le_opNorm₂ (x i) (y i)).trans_eq
    (mul_assoc _ _ _))

/-- A positive core linearization has norm bound given by the norm of the original bounded
bilinear map. -/
private lemma core_linearization_bound
    (b : E →L[ℝ] F →L[ℝ] G) (T : Core E F →ₗ[ℝ] G) (hT : Positive T)
    (hTb : ∀ x y, T (coreTmul E F x y) = b x y) (z : Core E F) :
    ‖T z‖ ≤ ‖b‖ * ‖z‖ := by
  by_cases hb : ‖b‖ = 0
  · obtain ⟨r, hr⟩ := costs_nonempty E F z
    simpa only [hb, zero_mul] using core_linearization_cost E F b T hT hTb hr
  · have hpos : 0 < ‖b‖ := lt_of_le_of_ne (norm_nonneg b) (Ne.symm hb)
    apply (div_le_iff₀' hpos).mp
    refine le_csInf (costs_nonempty E F z) ?_
    exact fun r hr ↦ (div_le_iff₀' hpos).mpr (core_linearization_cost E F b T hT hTb hr)

/-- A continuous map on the completed tensor space is positive if it is positive on the dense
core. -/
private lemma positive_of_positive_on_core (U : Tensor E F →L[ℝ] G)
    (hU : ∀ z : Core E F, 0 ≤ z → 0 ≤ U z) : Positive U.toLinearMap := by
  have h (z : Tensor E F) : 0 ≤ U |z| := by
    induction z using UniformSpace.Completion.induction_on
    · exact isClosed_le continuous_const
        (U.continuous.comp NormedVectorLattice.lipschitzWith_abs.continuous)
    · rename_i z
      rw [← coe_abs_completion]
      exact hU |z| (abs_nonneg z)
  exact fun z hz ↦ (abs_of_nonneg hz) ▸ h z

/-- A positive core linearization extends uniquely to the completed tensor space, preserving
positivity and the bilinear operator norm. -/
private lemma exists_unique_completion_extension
    (b : E →L[ℝ] F →L[ℝ] G) (T : Core E F →ₗ[ℝ] G) (hT : Positive T)
    (hTb : ∀ x y, T (coreTmul E F x y) = b x y) :
    ∃! U : Tensor E F →L[ℝ] G,
      Positive U.toLinearMap ∧
      (∀ x y, U (tmul E F x y) = b x y) ∧ ‖U‖ = ‖b‖ := by
  let e := (UniformSpace.Completion.toComplₗᵢ : Core E F →ₗᵢ[ℝ] Tensor E F).toLinearMap
  let U := T.extendOfNorm e
  have he : DenseRange e := UniformSpace.Completion.denseRange_coe
  have hbound (z : Core E F) : ‖T z‖ ≤ ‖b‖ * ‖e z‖ := by
    simpa only [e, LinearIsometry.coe_toLinearMap, LinearIsometry.norm_map] using
      core_linearization_bound E F b T hT hTb z
  have hU (z : Core E F) : U (e z) = T z :=
    LinearMap.extendOfNorm_eq he ⟨‖b‖, hbound⟩ z
  have hnorm : ‖U‖ ≤ ‖b‖ := LinearMap.opNorm_extendOfNorm_le he (norm_nonneg b) hbound
  have htmul (x : E) (y : F) : U (tmul E F x y) = b x y :=
    (hU (coreTmul E F x y)).trans (hTb x y)
  refine ⟨U, ⟨?_, htmul, le_antisymm hnorm ?_⟩, ?_⟩
  · exact positive_of_positive_on_core E F U (fun z hz ↦ (hU z).symm ▸ hT z hz)
  · apply b.opNorm_le_bound (norm_nonneg U)
    intro x
    apply (b x).opNorm_le_bound (mul_nonneg (norm_nonneg U) (norm_nonneg x))
    intro y
    rw [← htmul x y]
    exact (U.le_opNorm _).trans_eq (by rw [norm_tmul, mul_assoc])
  · intro S hS
    apply ContinuousLinearMap.ext_on (dense_span_tmul E F)
    rintro _ ⟨⟨x, y⟩, rfl⟩
    exact (hS.2.1 x y).trans (htmul x y).symm

end PositiveExtension

section PositiveApproximation

variable {K L : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [TopologicalSpace L] [CompactSpace L] [T2Space L]

/-- A convex weighted average of scalar approximations retains their common error bound. -/
private lemma weighted_average_error {m : ℕ} (a δ : ℝ) (c w : Fin m → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hs : ∑ j, w j = 1)
    (hc : ∀ j, w j ≠ 0 → |a - c j| ≤ δ) : |a - ∑ j, c j * w j| ≤ δ := by
  have heq : a - ∑ j, c j * w j = ∑ j, (a - c j) * w j := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hs, mul_one]
  rw [heq]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    ∑ j, |(a - c j) * w j| ≤ ∑ j, δ * w j := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hzero : w j = 0
      · simp only [hzero, mul_zero, abs_zero, le_refl]
      · simpa only [abs_mul, abs_of_nonneg (hw j)] using
          mul_le_mul_of_nonneg_right (hc j hzero) (hw j)
    _ = δ := by rw [← Finset.mul_sum, hs, mul_one]

/-- A finite family of continuous functions admits simultaneous approximation by positive
sampling operators with finitely many sample points. -/
private lemma exists_positive_sampling {n : ℕ} (f : Fin n → C(K, ℝ))
    {δ : ℝ} (hδ : 0 < δ) : ∃ (m : ℕ) (k : Fin m → K) (u : Fin m → C(K, ℝ)),
    (∀ j, 0 ≤ u j) ∧ ∀ i, ‖f i - ∑ j, f i (k j) • u j‖ ≤ δ := by
  classical
  let U (k : K) := ⋂ i, {x | |f i x - f i k| < δ}
  have hU (k : K) : IsOpen (U k) := isOpen_iInter_of_finite (fun i ↦
    isOpen_lt (((f i).continuous.sub continuous_const).abs) continuous_const)
  have hcover : Set.univ ⊆ ⋃ k, U k := fun x _ ↦ Set.mem_iUnion.mpr
    ⟨x, Set.mem_iInter.mpr (fun i ↦ by
      simpa only [Set.mem_ofPred_eq, sub_self, abs_zero] using hδ)⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  let m := Fintype.card ↥s
  let k : Fin m → K := fun j ↦ ((Fintype.equivFin ↥s).symm j).val
  have hcover' : Set.univ ⊆ ⋃ j, U (k j) := by
    intro x hx
    obtain ⟨t, ht, hxU⟩ := Set.mem_iUnion₂.mp (hs hx)
    refine Set.mem_iUnion.mpr ⟨(Fintype.equivFin ↥s) ⟨t, ht⟩, ?_⟩
    simpa only [k, Equiv.symm_apply_apply] using hxU
  obtain ⟨u, husupp, hsum, hbounds, _⟩ := exists_continuous_sum_one_of_isOpen_isCompact
    (fun j ↦ hU (k j)) isCompact_univ hcover'
  refine ⟨m, k, u, fun j x ↦ (hbounds j x).1, ?_⟩
  intro i
  apply (ContinuousMap.norm_le _ hδ.le).mpr
  intro x
  simp only [ContinuousMap.sub_apply, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul, Real.norm_eq_abs]
  refine weighted_average_error (f i x) δ (fun j ↦ f i (k j)) (fun j ↦ u j x)
    (fun j ↦ (hbounds j x).1) ?_ ?_
  · simpa only [Finset.sum_apply, Pi.one_apply] using hsum (Set.mem_univ x)
  · intro j hj
    exact le_of_lt (Set.mem_iInter.mp (husupp j (subset_tsupport _ hj)) i)

omit [T2Space L] in
/-- A positive bounded bilinear map on continuous-function spaces preserves positivity of
finite sums whose scalar product functions are pointwise nonnegative. -/
private lemma positive_sum_of_pointwise {G : Type u} [NormedAddCommGroup G] [Lattice G]
    [IsOrderedAddMonoid G] [BanachLattice G]
    (b : C(K, ℝ) →L[ℝ] C(L, ℝ) →L[ℝ] G)
    (hb : ∀ f g, 0 ≤ f → 0 ≤ g → 0 ≤ b f g)
    {n : ℕ} (f : Fin n → C(K, ℝ)) (g : Fin n → C(L, ℝ))
    (h : ∀ k l, 0 ≤ ∑ i, f i k * g i l) : 0 ≤ ∑ i, b (f i) (g i) := by
  apply (isClosed_Ici : IsClosed (Set.Ici (0 : G))).closure_subset
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let C := ‖b‖ * ∑ i, ‖g i‖
  have hC : 0 ≤ C := mul_nonneg (norm_nonneg b) (Finset.sum_nonneg (fun i _ ↦ norm_nonneg (g i)))
  let δ := ε / (C + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨m, k, u, hu, happrox⟩ := exists_positive_sampling f hδ
  let v := ∑ j, b (u j) (∑ i, f i (k j) • g i)
  have hv : 0 ≤ v := Finset.sum_nonneg (fun j _ ↦ hb _ _ (hu j)
    (fun l ↦ show 0 ≤ (∑ i, f i (k j) • g i) l from by
      simpa only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul] using h (k j) l))
  have herr : ‖(∑ i, b (f i) (g i)) - v‖ ≤ δ * C := by
    have hv' : v = ∑ i, b (∑ j, f i (k j) • u j) (g i) := by
      simp only [v, map_sum, map_smul, sum_apply, smul_apply]
      exact Finset.sum_comm
    have heq (i : Fin n) : b (f i) (g i) - b (∑ j, f i (k j) • u j) (g i) =
        b (f i - ∑ j, f i (k j) • u j) (g i) := by simp only [map_sub, sub_apply]
    rw [hv', ← Finset.sum_sub_distrib]
    simp_rw [heq]
    apply (norm_sum_le _ _).trans
    calc
      ∑ i, ‖b (f i - ∑ j, f i (k j) • u j) (g i)‖ ≤ ∑ i, ‖b‖ * δ * ‖g i‖ :=
        Finset.sum_le_sum (fun i _ ↦ (b.le_opNorm₂ _ _).trans
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (happrox i) (norm_nonneg b))
            (norm_nonneg (g i))))
      _ = δ * C := by
        rw [← Finset.mul_sum]
        exact (mul_assoc _ _ _).trans (mul_left_comm _ _ _)
  refine ⟨v, hv, ?_⟩
  rw [dist_eq_norm]
  have hδε : δ * (C + 1) = ε := div_mul_cancel₀ ε (ne_of_gt (by positivity : 0 < C + 1))
  exact herr.trans_lt (by nlinarith)

end PositiveApproximation

section PositiveCharacters

variable {D Z W : Type u}
  [NormedAddCommGroup D] [Lattice D] [IsOrderedAddMonoid D] [AMSpaceWithUnit D]
  [NormedAddCommGroup Z] [Lattice Z] [IsOrderedAddMonoid Z] [AMSpaceWithUnit Z]
  [NormedAddCommGroup W] [Lattice W] [IsOrderedAddMonoid W] [AMSpaceWithUnit W]

/-- For unital AM-spaces, positivity under every pair of characters implies positivity after
any positive bounded bilinear map. -/
private lemma am_positive_sum [Nontrivial D] [Nontrivial Z]
    {G : Type u} [NormedAddCommGroup G] [Lattice G] [IsOrderedAddMonoid G] [BanachLattice G]
    (b : D →L[ℝ] Z →L[ℝ] G) (hb : ∀ x y, 0 ≤ x → 0 ≤ y → 0 ≤ b x y)
    {n : ℕ} (x : Fin n → D) (y : Fin n → Z)
    (h : ∀ (φ : AMSpaceWithUnit.LatticeCharacter D) (ψ : AMSpaceWithUnit.LatticeCharacter Z),
      0 ≤ ∑ i, φ (x i) * ψ (y i)) : 0 ≤ ∑ i, b (x i) (y i) := by
  let J := AMSpaceWithUnit.kakutaniEquiv D
  let K := AMSpaceWithUnit.kakutaniEquiv Z
  let iD := J.symm.toContinuousLinearEquiv.toContinuousLinearMap
  let iZ := K.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hD (x : D) : iD (J x) = x := J.toLinearIsometryEquiv.symm_apply_apply x
  have hZ (y : Z) : iZ (K y) = y := K.toLinearIsometryEquiv.symm_apply_apply y
  have hb' : ∀ f g, 0 ≤ f → 0 ≤ g → 0 ≤ (b.bilinearComp iD iZ) f g :=
    fun f g hf hg ↦ hb _ _ (J.symm.toVecLatEquiv.toVecLatHom.map_nonneg hf)
      (K.symm.toVecLatEquiv.toVecLatHom.map_nonneg hg)
  simpa only [ContinuousLinearMap.bilinearComp_apply, hD, hZ] using
    positive_sum_of_pointwise (b.bilinearComp iD iZ) hb' (fun i ↦ J (x i)) (fun i ↦ K (y i)) h

/-- A positive sum under a nonvanishing unital lattice bimorphism is nonnegative when
evaluated by any pair of factor characters. -/
private lemma scalar_sum_nonneg [Nontrivial D] [Nontrivial Z] [Nontrivial W]
    (b : D →ₗ[ℝ] Z →ₗ[ℝ] W) (hb : ∀ x y, |b x y| = b |x| |y|)
    (hu : b AMSpaceWithUnit.unit AMSpaceWithUnit.unit = AMSpaceWithUnit.unit)
    (hbi : ∀ x y, x ≠ 0 → y ≠ 0 → b x y ≠ 0)
    {n : ℕ} (x : Fin n → D) (y : Fin n → Z) (h : 0 ≤ ∑ i, b (x i) (y i))
    (φ : AMSpaceWithUnit.LatticeCharacter D) (ψ : AMSpaceWithUnit.LatticeCharacter Z) :
    0 ≤ ∑ i, φ (x i) * ψ (y i) := by
  obtain ⟨χ, hχ⟩ := character_pair_surjective b hb hu hbi (φ, ψ)
  have heq (i : Fin n) : χ.toVecLatHom (b (x i) (y i)) = φ (x i) * ψ (y i) :=
    (character_pair_apply b hb hu χ (x i) (y i)).trans (by rw [hχ])
  simpa only [map_sum, heq] using χ.toVecLatHom.map_nonneg h

end PositiveCharacters

/-- On principal ideals, positivity of a finite sum under a nonvanishing lattice bimorphism
transfers to every positive bounded bilinear map. -/
private lemma local_positive_sum {H G : Type u}
    [NormedAddCommGroup H] [Lattice H] [IsOrderedAddMonoid H] [BanachLattice H]
    [NormedAddCommGroup G] [Lattice G] [IsOrderedAddMonoid G] [BanachLattice G]
    (b : E →ₗ[ℝ] F →ₗ[ℝ] H) (hb : ∀ x y, |b x y| = b |x| |y|)
    (hbi : ∀ x y, x ≠ 0 → y ≠ 0 → b x y ≠ 0)
    (c : E →L[ℝ] F →L[ℝ] G) (hc : ∀ x y, 0 ≤ x → 0 ≤ y → 0 ≤ c x y)
    {e : E} {f : F} (he : 0 < e) (hf : 0 < f)
    {n : ℕ} (p : Fin n → (OrderIdeal.principal e).toVectorSublattice ×
      (OrderIdeal.principal f).toVectorSublattice)
    (h : 0 ≤ ∑ i, b (p i).1.val (p i).2.val) :
    0 ≤ ∑ i, c (p i).1.val (p i).2.val := by
  let D := (OrderIdeal.principal e).toVectorSublattice
  let Z := (OrderIdeal.principal f).toVectorSublattice
  let : NormedAddCommGroup D := OrderIdeal.principalNormedAddCommGroup e
  let : NormedAddCommGroup Z := OrderIdeal.principalNormedAddCommGroup f
  let : AMSpaceWithUnit D := OrderIdeal.principalAMSpaceWithUnit he.le
    (@IsUniformlyCompleteVectorLattice.complete_principal E _ _ _ _
      (isUniformlyCompleteVectorLattice_of_banachLattice E) e he)
  let : AMSpaceWithUnit Z := OrderIdeal.principalAMSpaceWithUnit hf.le
    (@IsUniformlyCompleteVectorLattice.complete_principal F _ _ _ _
      (isUniformlyCompleteVectorLattice_of_banachLattice F) f hf)
  have hbef : 0 < b e f := lt_of_le_of_ne (bimorphism_nonneg b hb he.le hf.le)
    (Ne.symm (hbi e f he.ne' hf.ne'))
  let W := (OrderIdeal.principal (b e f)).toVectorSublattice
  let : NormedAddCommGroup W := OrderIdeal.principalNormedAddCommGroup (b e f)
  let : AMSpaceWithUnit W := OrderIdeal.principalAMSpaceWithUnit hbef.le
    (@IsUniformlyCompleteVectorLattice.complete_principal H _ _ _ _
      (isUniformlyCompleteVectorLattice_of_banachLattice H) (b e f) hbef)
  let : Nontrivial D := principal_nontrivial he
  let : Nontrivial Z := principal_nontrivial hf
  let : Nontrivial W := principal_nontrivial hbef
  let B : D →ₗ[ℝ] Z →ₗ[ℝ] W := principalBimorphism b hb he.le hf.le
  have hB : ∀ x y, |B x y| = B |x| |y| := fun x y ↦ Subtype.ext (hb x.val y.val)
  have hBi : ∀ x y, x ≠ 0 → y ≠ 0 → B x y ≠ 0 :=
    fun x y hx hy h ↦ hbi x.val y.val (fun h ↦ hx (Subtype.ext h))
      (fun h ↦ hy (Subtype.ext h)) (congrArg Subtype.val h)
  have hlocal : 0 ≤ ∑ i, B (p i).1 (p i).2 := by
    change 0 ≤ W.subtype (∑ i, B (p i).1 (p i).2)
    rw [map_sum]
    exact h
  let : TopologicalSpace D := @UniformSpace.toTopologicalSpace D
    (@PseudoMetricSpace.toUniformSpace D
      (OrderIdeal.principalNormedAddCommGroup e).toSeminormedAddCommGroup.toPseudoMetricSpace)
  let iD : D →L[ℝ] E :=
    { (OrderIdeal.principal e).toVectorSublattice.subtype.toLinearMap with
      cont := Positive.continuous (fun x hx ↦ hx) }
  let : TopologicalSpace Z := @UniformSpace.toTopologicalSpace Z
    (@PseudoMetricSpace.toUniformSpace Z
      (OrderIdeal.principalNormedAddCommGroup f).toSeminormedAddCommGroup.toPseudoMetricSpace)
  let iZ : Z →L[ℝ] F :=
    { (OrderIdeal.principal f).toVectorSublattice.subtype.toLinearMap with
      cont := Positive.continuous (fun y hy ↦ hy) }
  exact am_positive_sum (c.bilinearComp iD iZ) (fun x y hx hy ↦ hc x.val y.val hx hy)
    (fun i ↦ (p i).1) (fun i ↦ (p i).2)
    (scalar_sum_nonneg B hB rfl hBi (fun i ↦ (p i).1) (fun i ↦ (p i).2) hlocal)

/-- A positive bounded bilinear map preserves positivity of finite sums of elementary tensors
in the core. -/
private lemma core_sum_nonneg {G : Type u} [NormedAddCommGroup G] [Lattice G]
    [IsOrderedAddMonoid G] [BanachLattice G]
    (b : E →L[ℝ] F →L[ℝ] G) (hb : ∀ x y, 0 ≤ x → 0 ≤ y → 0 ≤ b x y)
    {n : ℕ} (x : Fin n → E) (y : Fin n → F)
    (h : 0 ≤ ∑ i, coreTmul E F (x i) (y i)) : 0 ≤ ∑ i, b (x i) (y i) := by
  obtain ⟨e, he, hx⟩ := exists_principal_family x
  obtain ⟨f, hf, hy⟩ := exists_principal_family y
  let p : Fin n → (OrderIdeal.principal e).toVectorSublattice ×
      (OrderIdeal.principal f).toVectorSublattice := fun i ↦ (⟨x i, hx i⟩, ⟨y i, hy i⟩)
  by_cases he0 : e = 0
  · have hx0 (i : Fin n) : x i = 0 :=
      congrArg Subtype.val (principal_eq_zero he0 (p i).1)
    simp only [hx0, map_zero, zero_apply, Finset.sum_const_zero, le_refl]
  · by_cases hf0 : f = 0
    · have hy0 (i : Fin n) : y i = 0 :=
        congrArg Subtype.val (principal_eq_zero hf0 (p i).2)
      simp only [hy0, map_zero, Finset.sum_const_zero, le_refl]
    · let B := (coreTmul E F).compr₂ (coreInclusion E F).toLinearMap
      apply local_positive_sum E F B (completedPairing_abs E F)
        (fun _ _ ↦ completedPairing_ne_zero E F) b hb
        (lt_of_le_of_ne he (Ne.symm he0)) (lt_of_le_of_ne hf (Ne.symm hf0)) p
      change 0 ≤ ∑ i, (coreInclusion E F) (coreTmul E F (x i) (y i))
      simpa only [map_sum] using (coreInclusion E F).map_nonneg h

/-- The canonical linear map from the algebraic tensor product into the tensor core. -/
private noncomputable def tensorSpanMap : _root_.TensorProduct ℝ E F →ₗ[ℝ] Core E F :=
  _root_.TensorProduct.lift (coreTmul E F)

/-- The algebraic linearization of a positive bilinear map is nonnegative whenever the
corresponding core tensor is nonnegative. -/
private lemma algebraic_image_nonneg {G : Type u} [NormedAddCommGroup G] [Lattice G]
    [IsOrderedAddMonoid G] [BanachLattice G]
    (b : E →L[ℝ] F →L[ℝ] G) (hb : ∀ x y, 0 ≤ x → 0 ≤ y → 0 ≤ b x y)
    (z : _root_.TensorProduct ℝ E F) (hz : 0 ≤ tensorSpanMap E F z) :
    0 ≤ _root_.TensorProduct.lift b.toLinearMap₁₂ z := by
  obtain ⟨n, x, y, rfl⟩ := _root_.TensorProduct.exists_sum_tmul_eq z
  simp only [tensorSpanMap, map_sum, _root_.TensorProduct.lift.tmul] at hz ⊢
  exact core_sum_nonneg E F b hb x y hz

/-- The algebraic linearization respects the order inherited from its image in the tensor
core. -/
private lemma algebraic_image_mono {G : Type u} [NormedAddCommGroup G] [Lattice G]
    [IsOrderedAddMonoid G] [BanachLattice G]
    (b : E →L[ℝ] F →L[ℝ] G) (hb : ∀ x y, 0 ≤ x → 0 ≤ y → 0 ≤ b x y)
    {z w : _root_.TensorProduct ℝ E F} (h : tensorSpanMap E F z ≤ tensorSpanMap E F w) :
    _root_.TensorProduct.lift b.toLinearMap₁₂ z ≤ _root_.TensorProduct.lift b.toLinearMap₁₂ w := by
  have hp := algebraic_image_nonneg E F b hb (w - z)
    (by simpa only [map_sub] using sub_nonneg.mpr h)
  simpa only [map_sub, sub_nonneg] using hp

/-- An algebraic linearization is bounded by the bilinear norm times any admissible cost of
its image in the core. -/
private lemma algebraic_image_cost {G : Type u} [NormedAddCommGroup G] [Lattice G]
    [IsOrderedAddMonoid G] [BanachLattice G]
    (b : E →L[ℝ] F →L[ℝ] G) (hb : ∀ x y, 0 ≤ x → 0 ≤ y → 0 ≤ b x y)
    (z : _root_.TensorProduct ℝ E F) {r : ℝ} (hr : r ∈ tensorCosts E F (tensorSpanMap E F z)) :
    ‖_root_.TensorProduct.lift b.toLinearMap₁₂ z‖ ≤ ‖b‖ * r := by
  obtain ⟨n, x, y, _, _, hz, rfl⟩ := hr
  let T := _root_.TensorProduct.lift b.toLinearMap₁₂
  let v := ∑ i, _root_.TensorProduct.tmul ℝ (x i) (y i)
  have hw : |tensorSpanMap E F z| ≤ tensorSpanMap E F v := by
    simpa only [tensorSpanMap, v, map_sum, _root_.TensorProduct.lift.tmul] using hz
  have hp := algebraic_image_mono E F b hb ((le_abs_self _).trans hw)
  have hn := algebraic_image_mono E F b hb (z := -z) (w := v)
    (by simpa only [map_neg] using (neg_le_abs (tensorSpanMap E F z)).trans hw)
  have ht : |T z| ≤ T v := abs_le'.mpr ⟨hp, by simpa only [map_neg] using hn⟩
  have hnorm := norm_le_norm_of_abs_le_abs (ht.trans (le_abs_self _))
  simp only [T, v, map_sum, _root_.TensorProduct.lift.tmul] at hnorm
  refine (hnorm.trans (norm_sum_le _ _)).trans ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ ↦ (b.le_opNorm₂ (x i) (y i)).trans_eq (mul_assoc _ _ _))

/-- The algebraic linearization is bounded by the bilinear norm times the projective norm of
its core image. -/
private lemma algebraic_image_bound {G : Type u} [NormedAddCommGroup G] [Lattice G]
    [IsOrderedAddMonoid G] [BanachLattice G]
    (b : E →L[ℝ] F →L[ℝ] G) (hb : ∀ x y, 0 ≤ x → 0 ≤ y → 0 ≤ b x y)
    (z : _root_.TensorProduct ℝ E F) :
    ‖_root_.TensorProduct.lift b.toLinearMap₁₂ z‖ ≤ ‖b‖ * ‖tensorSpanMap E F z‖ := by
  by_cases hzero : ‖b‖ = 0
  · obtain ⟨r, hr⟩ := costs_nonempty E F (tensorSpanMap E F z)
    simpa only [hzero, zero_mul] using algebraic_image_cost E F b hb z hr
  · have hpos : 0 < ‖b‖ := lt_of_le_of_ne (norm_nonneg b) (Ne.symm hzero)
    apply (div_le_iff₀' hpos).mp
    refine le_csInf (costs_nonempty E F (tensorSpanMap E F z)) ?_
    exact fun r hr ↦ (div_le_iff₀' hpos).mpr (algebraic_image_cost E F b hb z hr)

/-- Every positive core element is a norm limit of positive elements in the linear span of
elementary tensors. -/
private lemma core_nonneg_mem_closure {z : Core E F} (hz : 0 ≤ z) :
    z ∈ closure ((Submodule.span ℝ
      (Set.range (fun p : E × F ↦ coreTmul E F p.1 p.2)) : Set (Core E F)) ∩ Set.Ici 0) := by
  obtain ⟨e, f, _, _, ha⟩ := core_order_approx E F z
  let t := coreTmul E F e f
  let S := Submodule.span ℝ (Set.range (fun p : E × F ↦ coreTmul E F p.1 p.2))
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have hden : 0 < 2 * (‖t‖ + 1) := by positivity
  let δ := ε / (2 * (‖t‖ + 1))
  have hδ : 0 < δ := div_pos hε hden
  obtain ⟨w, hw, herr⟩ := ha δ hδ
  have ht : t ∈ S := Submodule.subset_span ⟨(e, f), rfl⟩
  have hpos : 0 ≤ w + δ • t :=
    hz.trans (sub_le_iff_le_add'.mp ((le_abs_self _).trans herr))
  refine ⟨w + δ • t, ⟨S.add_mem hw (S.smul_mem δ ht), hpos⟩, ?_⟩
  have hn : ‖z - w‖ ≤ δ * ‖t‖ := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hδ] using
      norm_le_norm_of_abs_le_abs (herr.trans (le_abs_self _))
  have hnd : ‖δ • t‖ = δ * ‖t‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
  have hd : dist z (w + δ • t) ≤ 2 * δ * ‖t‖ := by
    rw [dist_eq_norm, show z - (w + δ • t) = (z - w) - δ • t by abel]
    calc
      ‖(z - w) - δ • t‖ ≤ ‖z - w‖ + ‖δ • t‖ := norm_sub_le _ _
      _ ≤ δ * ‖t‖ + δ * ‖t‖ := add_le_add hn hnd.le
      _ = 2 * δ * ‖t‖ := by ring
  have hδε : δ * (2 * (‖t‖ + 1)) = ε := div_mul_cancel₀ ε (ne_of_gt hden)
  exact hd.trans_lt (by nlinarith)

/-- The linear span of elementary tensors is norm dense in the tensor core. -/
private lemma core_span_dense :
    Dense (Submodule.span ℝ (Set.range (fun p : E × F ↦ coreTmul E F p.1 p.2)) :
      Set (Core E F)) := by
  let S := Submodule.span ℝ (Set.range (fun p : E × F ↦ coreTmul E F p.1 p.2))
  have hp (z : Core E F) (hz : 0 ≤ z) : z ∈ S.topologicalClosure :=
    closure_mono Set.inter_subset_left (core_nonneg_mem_closure E F hz)
  intro z
  have h := S.topologicalClosure.sub_mem
    (hp z⁺ (posPart_nonneg z)) (hp z⁻ (negPart_nonneg z))
  change z⁺ - z⁻ ∈ closure (S : Set (Core E F)) at h
  simpa only [posPart_sub_negPart] using h

/-- The image of the algebraic tensor product in the core is precisely the linear span of
elementary tensors. -/
private lemma range_tensorSpanMap :
    LinearMap.range (tensorSpanMap E F) =
      Submodule.span ℝ (Set.range (fun p : E × F ↦ coreTmul E F p.1 p.2)) := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    obtain ⟨n, x, y, rfl⟩ := _root_.TensorProduct.exists_sum_tmul_eq z
    simp only [tensorSpanMap, map_sum, _root_.TensorProduct.lift.tmul]
    exact Submodule.sum_mem _ (fun i _ ↦ Submodule.subset_span ⟨(x i, y i), rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨x, y⟩, rfl⟩
    exact ⟨_root_.TensorProduct.tmul ℝ x y, rfl⟩

/-- Every positive bounded bilinear map admits a positive linearization on the whole tensor
core. -/
private lemma core_positive_linearization {G : Type u} [NormedAddCommGroup G] [Lattice G]
    [IsOrderedAddMonoid G] [BanachLattice G]
    (b : E →L[ℝ] F →L[ℝ] G) (hb : ∀ x y, 0 ≤ x → 0 ≤ y → 0 ≤ b x y) :
    ∃ T : Core E F →ₗ[ℝ] G, Positive T ∧ ∀ x y, T (coreTmul E F x y) = b x y := by
  let Φ := _root_.TensorProduct.lift b.toLinearMap₁₂
  let Γ := tensorSpanMap E F
  let U := Φ.extendOfNorm Γ
  have hdense : DenseRange Γ := by
    change Dense (LinearMap.range (tensorSpanMap E F) : Set (Core E F))
    rw [range_tensorSpanMap]
    exact core_span_dense E F
  have hbound (v : _root_.TensorProduct ℝ E F) : ‖Φ v‖ ≤ ‖b‖ * ‖Γ v‖ :=
    algebraic_image_bound E F b hb v
  have hU (v : _root_.TensorProduct ℝ E F) : U (Γ v) = Φ v :=
    LinearMap.extendOfNorm_eq hdense ⟨‖b‖, hbound⟩ v
  refine ⟨U.toLinearMap, ?_, ?_⟩
  · have hclosed : IsClosed {z : Core E F | 0 ≤ U z} :=
      isClosed_le continuous_const U.continuous
    have hcontains : (Submodule.span ℝ
        (Set.range (fun p : E × F ↦ coreTmul E F p.1 p.2)) : Set (Core E F)) ∩
          Set.Ici 0 ⊆ {z : Core E F | 0 ≤ U z} := by
      intro z hz
      have hzr : z ∈ LinearMap.range Γ := by
        rw [range_tensorSpanMap]
        exact hz.1
      obtain ⟨v, rfl⟩ := hzr
      change 0 ≤ U (Γ v)
      rw [hU]
      exact algebraic_image_nonneg E F b hb v hz.2
    exact fun z hz ↦ (closure_minimal hcontains hclosed) (core_nonneg_mem_closure E F hz)
  · intro x y
    exact hU (_root_.TensorProduct.tmul ℝ x y)

/-- Bounded positive bilinear maps extend uniquely to positive operators,
with the same norm. -/
theorem exists_unique_positive_extension
    (G : Type u) [NormedAddCommGroup G] [Lattice G]
    [IsOrderedAddMonoid G] [BanachLattice G]
    (b : E →L[ℝ] F →L[ℝ] G)
    (hb : ∀ x y, 0 ≤ x → 0 ≤ y → 0 ≤ b x y) :
    ∃! T : Tensor E F →L[ℝ] G,
      Positive T.toLinearMap ∧
      (∀ x y, T (tmul E F x y) = b x y) ∧ ‖T‖ = ‖b‖ := by
  obtain ⟨T, hT, hTb⟩ := core_positive_linearization E F b hb
  exact exists_unique_completion_extension E F b T hT hTb

/-- The completed construction, bundled with its tensor universal property. -/
noncomputable def tensorProduct : BanachLattice.TensorProduct E F where
  Carrier := Tensor E F
  tmul := (tmul E F).toLinearMap₁₂
  tmul_isLatticeBimorphism := abs_tmul E F
  norm_tmul_le x y := (norm_tmul E F x y).le
  dense_span_tmul := dense_span_tmul E F
  universal := exists_unique_positive_extension E F

/-- The canonical tensor product supplies the pairing used in free-product embeddings. -/
noncomputable def tensorPairing : TensorPairing E F where
  Carrier := Tensor E F
  tmul := tmul E F
  isVecLatHom_left y hy := by
    refine (VecLatHom.ofAbs ((tmul E F).flip y).toLinearMap ?_).isVecLatHom
    intro x
    change tmul E F |x| y = |tmul E F x y|
    simpa only [abs_of_nonneg hy] using (abs_tmul E F x y).symm
  isVecLatHom_right x hx := by
    refine (VecLatHom.ofAbs ((tmul E F) x).toLinearMap ?_).isVecLatHom
    intro y
    change tmul E F x |y| = |tmul E F x y|
    simpa only [abs_of_nonneg hx] using (abs_tmul E F x y).symm
  tmul_pos x y hx hy := by
    have habs : |tmul E F x y| = tmul E F x y := by
      simpa only [abs_of_nonneg hx.le, abs_of_nonneg hy.le] using abs_tmul E F x y
    refine lt_of_le_of_ne (habs ▸ abs_nonneg _) ?_
    intro h
    have hn := congrArg norm h
    rw [norm_zero, norm_tmul] at hn
    exact (mul_ne_zero (norm_ne_zero_iff.mpr (ne_of_gt hx))
      (norm_ne_zero_iff.mpr (ne_of_gt hy))) hn.symm

end ProjectiveTensor

end BanachLattice.FreeProduct
