/-
Authors: Gonzalo Martínez-Fernández
-/

import FreeProducts.BanachLattice.Basic
import BanLat.AMSpace.Kakutani
import BanLat.Examples.CofK.Basic
import BanLat.OrderUnit
import BanLat.OrderDense
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Separation.CompletelyRegular

/-!
# The join representation of binary free products

The topological join of two nonempty compact Hausdorff spaces models the binary free
product of their continuous-function lattices. The sum of the two canonical units is a
strong order unit. An explicit homeomorphism identifies normalized scalar lattice
homomorphisms with points of the join. Transporting continuous functions through this
homeomorphism and the representation of the complete principal ideal gives the lattice
equivalence. Positive majorants describe the free-product norm explicitly.
-/

noncomputable section

open scoped Topology Pointwise

universe u v w

namespace BanachLattice

variable {I : Type v} (E : I → Type u)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, Lattice (E i)]
  [∀ i, IsOrderedAddMonoid (E i)] [∀ i, BanachLattice (E i)]

namespace FreeProduct

section Join

variable (K L : Type u) [TopologicalSpace K] [TopologicalSpace L]

/-- The join identifies the unused coordinate at each endpoint of the interval. -/
def joinSetoid : Setoid (K × L × Set.Icc (0 : ℝ) 1) where
  r p q :=
    p.2.2 = q.2.2 ∧
      ((p.2.2 : ℝ) = 1 ∨ p.1 = q.1) ∧
      ((p.2.2 : ℝ) = 0 ∨ p.2.1 = q.2.1)
  iseqv := by
    refine ⟨fun p ↦ ⟨rfl, Or.inr rfl, Or.inr rfl⟩, ?_, ?_⟩
    all_goals aesop

/-- The topological join, with the quotient topology. -/
def Join :=
  Quotient (joinSetoid K L)

/-- The canonical quotient map to the join. -/
def joinMk (x : K) (y : L) (t : Set.Icc (0 : ℝ) 1) : Join K L :=
  Quotient.mk (joinSetoid K L) (x, y, t)

/-- The join carries the quotient topology. -/
instance instTopologicalSpaceJoin : TopologicalSpace (Join K L) :=
  inferInstanceAs (TopologicalSpace (Quotient (joinSetoid K L)))

/-- Interpolation of continuous functions on the two factors of the join. -/
def interpolate (f : C(K, ℝ)) (g : C(L, ℝ)) : C(Join K L, ℝ) where
  toFun := Quotient.lift
    (fun p : K × L × Set.Icc (0 : ℝ) 1 ↦
      (1 - (p.2.2 : ℝ)) * f p.1 + (p.2.2 : ℝ) * g p.2.1)
    (by
      rintro p q ⟨ht, hx, hy⟩
      rcases hx with hx | hx <;> rcases hy with hy | hy <;> simp_all)
  continuous_toFun := by
    apply continuous_quot_lift
    fun_prop

/-- Interpolation has its prescribed value on representatives of join points. -/
theorem interpolate_joinMk
    (f : C(K, ℝ)) (g : C(L, ℝ))
    (x : K) (y : L) (t : Set.Icc (0 : ℝ) 1) :
    interpolate K L f g (joinMk K L x y t) =
      (1 - (t : ℝ)) * f x + (t : ℝ) * g y := rfl

variable [CompactSpace K] [CompactSpace L] [T2Space K] [T2Space L]

/-- The join of compact spaces is compact. -/
instance instCompactSpaceJoin : CompactSpace (Join K L) := by
  exact inferInstanceAs (CompactSpace (Quotient (joinSetoid K L)))

/-- Real continuous functions separate points of a compact Hausdorff space. -/
private lemma eq_of_continuousMap_apply_eq {X : Type u} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] {x y : X} (h : ∀ f : C(X, ℝ), f x = f y) : x = y := by
  by_contra hxy
  obtain ⟨f, hf, hne⟩ := separatesPoints_continuous_of_t35Space hxy
  exact hne (h ⟨f, hf⟩)

/-- Interpolating pairs of continuous functions separates points of the join. -/
private lemma join_eq_of_interpolate_eq {p q : Join K L}
    (h : ∀ (f : C(K, ℝ)) (g : C(L, ℝ)),
      interpolate K L f g p = interpolate K L f g q) : p = q := by
  induction p using Quotient.inductionOn with
  | h p =>
    induction q using Quotient.inductionOn with
    | h q =>
      change ∀ (f : C(K, ℝ)) (g : C(L, ℝ)),
        (1 - (p.2.2 : ℝ)) * f p.1 + (p.2.2 : ℝ) * g p.2.1 =
          (1 - (q.2.2 : ℝ)) * f q.1 + (q.2.2 : ℝ) * g q.2.1 at h
      have ht := h 0 1
      change (1 - (p.2.2 : ℝ)) * 0 + (p.2.2 : ℝ) * 1 =
        (1 - (q.2.2 : ℝ)) * 0 + (q.2.2 : ℝ) * 1 at ht
      simp only [mul_zero, mul_one, zero_add] at ht
      refine Quotient.sound ⟨Subtype.ext ht, ?_, ?_⟩
      · by_cases hp : (p.2.2 : ℝ) = 1
        · exact Or.inl hp
        · right
          apply eq_of_continuousMap_apply_eq
          exact fun f ↦ mul_left_cancel₀ (sub_ne_zero.mpr (Ne.symm hp))
            (by simpa [ht] using h f 0)
      · by_cases hp : (p.2.2 : ℝ) = 0
        · exact Or.inl hp
        · right
          apply eq_of_continuousMap_apply_eq
          exact fun g ↦ mul_left_cancel₀ hp
            (by simpa [ht] using h 0 g)

/-- The join of compact Hausdorff spaces is Hausdorff. -/
instance instT2SpaceJoin : T2Space (Join K L) :=
  T2Space.of_injective_continuous
    (f := fun p (fg : C(K, ℝ) × C(L, ℝ)) ↦ interpolate K L fg.1 fg.2 p)
    (fun _ _ h ↦ join_eq_of_interpolate_eq K L (fun f g ↦ congrFun h (f, g)))
    (continuous_pi (fun fg ↦ (interpolate K L fg.1 fg.2).continuous))


end Join

/-- A normalized scalar character bounds a given continuous function from above at some point. -/
private lemma exists_apply_le_hom {X : Type u} [TopologicalSpace X]
    [CompactSpace X] [Nonempty X] (F : VecLatHom C(X, ℝ) ℝ)
    (hF : F 1 = 1) (f : C(X, ℝ)) : ∃ x, f x ≤ F f := by
  obtain ⟨x, _, hx⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty)
    f.continuous.continuousOn
  have hmin : (f x) • (1 : C(X, ℝ)) ≤ f := fun y ↦ by
    simpa using hx (Set.mem_univ y)
  exact ⟨x, by simpa [map_smul, hF] using F.monotone hmin⟩

/-- A normalized character agrees with point evaluation on any prescribed finite family of
continuous functions. -/
private lemma exists_eq_hom_on_finset {X : Type u} [TopologicalSpace X]
    [CompactSpace X] [Nonempty X] (F : VecLatHom C(X, ℝ) ℝ) (hF : F 1 = 1)
    (s : Finset C(X, ℝ)) : ∃ x, ∀ f ∈ s, f x = F f := by
  let g : C(X, ℝ) := ∑ f ∈ s, |f - (F f) • 1|
  have hFg : F g = 0 := by
    simp [g, map_sum, F.map_abs, map_sub, map_smul, hF]
  obtain ⟨x, hx⟩ := exists_apply_le_hom F hF g
  have hzero : (∑ f ∈ s, |f x - F f|) = 0 :=
    le_antisymm (by simpa [g, hFg] using hx)
      (Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _))
  exact ⟨x, fun f hf ↦ sub_eq_zero.mp (abs_eq_zero.mp
    ((Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ abs_nonneg _)).mp hzero f hf))⟩

/-- A real lattice homomorphism taking the constant one to one is evaluation at a point. -/
private lemma exists_eq_hom {X : Type u} [TopologicalSpace X]
    [CompactSpace X] [Nonempty X] (F : VecLatHom C(X, ℝ) ℝ) (hF : F 1 = 1) :
    ∃ x, ∀ f, F f = f x := by
  obtain ⟨x, hx⟩ := CompactSpace.iInter_nonempty
    (t := fun f : C(X, ℝ) ↦ {x | f x = F f})
    (fun f ↦ isClosed_eq f.continuous continuous_const)
    (fun s ↦ by
      obtain ⟨x, hx⟩ := exists_eq_hom_on_finset F hF s
      exact ⟨x, Set.mem_iInter₂.mpr hx⟩)
  exact ⟨x, fun f ↦ (Set.mem_iInter.mp hx f).symm⟩

/-- Every scalar lattice homomorphism on continuous functions is a weighted point evaluation. -/
private lemma exists_weighted_eval {X : Type u} [TopologicalSpace X]
    [CompactSpace X] [Nonempty X] (F : VecLatHom C(X, ℝ) ℝ) :
    ∃ x, ∀ f, F f = F 1 * f x := by
  have hpos : 0 ≤ F 1 := F.map_nonneg (fun _ ↦ zero_le_one)
  by_cases hzero : F 1 = 0
  · refine ⟨Classical.arbitrary X, fun f ↦ ?_⟩
    have hbound : |f| ≤ ‖f‖ • (1 : C(X, ℝ)) := fun x ↦ by
      simpa using f.norm_coe_le_norm x
    have hsmall : |F f| ≤ 0 := by
      simpa [F.map_abs, map_smul, hzero] using F.monotone hbound
    simpa [hzero] using abs_nonpos_iff.mp hsmall
  · let G := VecLatHom.ofAbs ((F 1)⁻¹ • F.toLinearMap) (by
      intro f
      change (F 1)⁻¹ * F |f| = |(F 1)⁻¹ * F f|
      rw [F.map_abs, abs_mul, abs_of_nonneg (inv_nonneg.mpr hpos)])
    have hG : G 1 = 1 := inv_mul_cancel₀ hzero
    obtain ⟨x, hx⟩ := exists_eq_hom G hG
    exact ⟨x, fun f ↦ (inv_mul_eq_iff_eq_mul₀ hzero).mp (hx f)⟩

section ContinuousFunctions

variable (K : Bool → Type u)
  [∀ b, TopologicalSpace (K b)] [∀ b, CompactSpace (K b)]
  [∀ b, T2Space (K b)] [∀ b, Nonempty (K b)]
  (P : FreeProduct (fun b ↦ C(K b, ℝ)))

omit [∀ b, T2Space (K b)] [∀ b, Nonempty (K b)] in
/-- A positive element giving the norm domination on both factors gives the same domination
throughout their Banach free product. -/
private lemma abs_le_norm_smul_of_factor_bound {e : P.Carrier} (he : 0 ≤ e)
    (hbound : ∀ b (f : C(K b, ℝ)), |P.inclusion b f| ≤ ‖f‖ • e) :
    ∀ z : P.Carrier, |z| ≤ ‖z‖ • e := by
  have hg : P.generated ≤ (OrderIdeal.principal e).toVectorSublattice := by
    apply VectorSublattice.generated_le
    rintro _ ⟨⟨b, f⟩, rfl⟩
    exact ⟨‖f‖, norm_nonneg _, by simpa only [abs_of_nonneg he] using hbound b f⟩
  let p : Seminorm ℝ P.generated := Seminorm.of
    (fun z ↦ OrderIdeal.gaugeNorm e (z : P.Carrier))
    (fun z w ↦ OrderIdeal.gaugeNorm_add_le e (hg z.2) (hg w.2))
    (fun r z ↦ OrderIdeal.gaugeNorm_smul e r (z : P.Carrier))
  have hp := P.seminorm_le_norm p
    (fun z hz ↦ Subtype.ext ((OrderIdeal.gaugeNorm_eq_zero_iff e (hg z.2)).mp hz))
    (fun z w h ↦ OrderIdeal.gaugeNorm_mono_abs e (hg w.2) h)
    (fun b f z hz ↦ OrderIdeal.gaugeNorm_le_of_abs_le e (norm_nonneg f)
      (by simpa only [hz, abs_of_nonneg he] using hbound b f))
  have hb (z : P.generated) : |(z : P.Carrier)| ≤ ‖(z : P.Carrier)‖ • e :=
    (OrderIdeal.abs_le_gaugeNorm_smul_abs e (hg z.2)).trans
      (by rw [abs_of_nonneg he]
          exact smul_le_smul_of_nonneg_right (hp z) he)
  exact P.dense_generated.induction (fun z hz ↦ hb ⟨z, hz⟩)
    (isClosed_le NormedVectorLattice.lipschitzWith_abs.continuous
      (continuous_norm.smul continuous_const))

omit [∀ b, T2Space (K b)] [∀ b, Nonempty (K b)] in
/-- An included continuous function is dominated in absolute value by its supremum norm times
the included constant one. -/
private lemma inclusion_abs_le_norm_smul_one (b : Bool) (f : C(K b, ℝ)) :
    |P.inclusion b f| ≤ ‖f‖ • P.inclusion b 1 := by
  calc
    |P.inclusion b f| = P.inclusion b |f| :=
      (((P.inclusion_isVecLatHom b).mk' (P.inclusion b)).map_abs f).symm
    _ ≤ ‖f‖ • P.inclusion b 1 :=
      (((P.inclusion_isVecLatHom b).mk' (P.inclusion b)).monotone
        (show |f| ≤ ‖f‖ • (1 : C(K b, ℝ)) from fun x ↦ by
          simpa using f.norm_coe_le_norm x)).trans_eq
        ((P.inclusion b).map_smul ‖f‖ 1)

omit [∀ b, T2Space (K b)] [∀ b, Nonempty (K b)] in
/-- The sum of the included constant functions dominates every element by its free-product
norm. -/
private lemma abs_le_norm_smul_join_unit :
    ∀ z : P.Carrier, |z| ≤ ‖z‖ • (P.inclusion false 1 + P.inclusion true 1) := by
  have hpos (b : Bool) : 0 ≤ P.inclusion b 1 :=
    ((P.inclusion_isVecLatHom b).mk' (P.inclusion b)).map_nonneg
      (show (0 : C(K b, ℝ)) ≤ 1 from fun _ ↦ zero_le_one)
  have hle (b : Bool) : P.inclusion b 1 ≤ P.inclusion false 1 + P.inclusion true 1 := by
    cases b
    · exact le_add_of_nonneg_right (hpos true)
    · exact le_add_of_nonneg_left (hpos false)
  exact abs_le_norm_smul_of_factor_bound K P (add_nonneg (hpos false) (hpos true))
    (fun b f ↦ (inclusion_abs_le_norm_smul_one K P b f).trans
      (smul_le_smul_of_nonneg_left (hle b) (norm_nonneg f)))


omit [∀ b, T2Space (K b)] [∀ b, Nonempty (K b)] in
/-- The sum of the two canonical constant functions is a strong order unit. -/
theorem strongOrderUnit_inclusion_one_add :
    StrongOrderUnit (P.inclusion false 1 + P.inclusion true 1) := by
  have hpos (b : Bool) : 0 ≤ P.inclusion b 1 :=
    ((P.inclusion_isVecLatHom b).mk' (P.inclusion b)).map_nonneg (fun _ ↦ zero_le_one)
  exact ⟨add_nonneg (hpos false) (hpos true), fun z ↦
    ⟨‖z‖, norm_nonneg z, abs_le_norm_smul_join_unit K P z⟩⟩

omit [∀ b, T2Space (K b)] [∀ b, Nonempty (K b)] in
/-- The supremum norm of a join interpolation is at most the sum of the two function norms. -/
private lemma norm_interpolate_le (f : C(K false, ℝ)) (g : C(K true, ℝ)) :
    ‖interpolate (K false) (K true) f g‖ ≤ ‖f‖ + ‖g‖ := by
  apply (ContinuousMap.norm_le _ (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro q
  induction q using Quotient.inductionOn with
  | h q =>
    change ‖(1 - (q.2.2 : ℝ)) * f q.1 + (q.2.2 : ℝ) * g q.2.1‖ ≤ ‖f‖ + ‖g‖
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    all_goals rw [norm_mul, Real.norm_eq_abs]
    · exact (mul_le_of_le_one_left (norm_nonneg _) (abs_le.mpr
        ⟨by linarith [q.2.2.2.2], by linarith [q.2.2.2.1]⟩)).trans (f.norm_coe_le_norm _)
    · exact (mul_le_of_le_one_left (norm_nonneg _) (abs_le.mpr
        ⟨by linarith [q.2.2.2.1], q.2.2.2.2⟩)).trans (g.norm_coe_le_norm _)

omit [∀ b, T2Space (K b)] [∀ b, Nonempty (K b)] in
/-- Constructs the contractive lattice map to functions on the join with the prescribed
interpolated factor inclusions. -/
private lemma exists_join_extension :
    ∃ S : P.Carrier →L[ℝ] C(Join (K false) (K true), ℝ),
      IsVecLatHom S ∧ ‖S‖ ≤ 1 ∧
      (∀ f, S (P.inclusion false f) = interpolate (K false) (K true) f 0) ∧
      (∀ g, S (P.inclusion true g) = interpolate (K false) (K true) 0 g) := by
  let A : C(K false, ℝ) →ₗ[ℝ] C(Join (K false) (K true), ℝ) :=
    { toFun := fun f ↦ interpolate (K false) (K true) f 0
      map_add' := by
        intro f g
        ext q
        induction q using Quotient.inductionOn with
        | h q =>
          change (1 - (q.2.2 : ℝ)) * (f q.1 + g q.1) + (q.2.2 : ℝ) * 0 =
            ((1 - (q.2.2 : ℝ)) * f q.1 + (q.2.2 : ℝ) * 0) +
              ((1 - (q.2.2 : ℝ)) * g q.1 + (q.2.2 : ℝ) * 0)
          ring
      map_smul' := fun r f ↦ ContinuousMap.ext (fun q ↦
        Quotient.inductionOn q (fun q ↦ by
          change (1 - (q.2.2 : ℝ)) * (r * f q.1) + (q.2.2 : ℝ) * 0 =
            r * ((1 - (q.2.2 : ℝ)) * f q.1 + (q.2.2 : ℝ) * 0)
          ring)) }
  let B : C(K true, ℝ) →ₗ[ℝ] C(Join (K false) (K true), ℝ) :=
    { toFun := fun g ↦ interpolate (K false) (K true) 0 g
      map_add' := fun f g ↦ ContinuousMap.ext (fun q ↦
        Quotient.inductionOn q (fun q ↦ by
          change (1 - (q.2.2 : ℝ)) * 0 + (q.2.2 : ℝ) * (f q.2.1 + g q.2.1) =
            ((1 - (q.2.2 : ℝ)) * 0 + (q.2.2 : ℝ) * f q.2.1) +
              ((1 - (q.2.2 : ℝ)) * 0 + (q.2.2 : ℝ) * g q.2.1)
          ring))
      map_smul' := fun r f ↦ ContinuousMap.ext (fun q ↦
        Quotient.inductionOn q (fun q ↦ by
          change (1 - (q.2.2 : ℝ)) * 0 + (q.2.2 : ℝ) * (r * f q.2.1) =
            r * ((1 - (q.2.2 : ℝ)) * 0 + (q.2.2 : ℝ) * f q.2.1)
          ring)) }
  let T : ∀ b, C(K b, ℝ) →L[ℝ] C(Join (K false) (K true), ℝ) := fun b ↦
    match b with
    | false => A.mkContinuous 1 (fun f ↦ (norm_interpolate_le K f 0).trans_eq (by simp))
    | true => B.mkContinuous 1 (fun g ↦ (norm_interpolate_le K 0 g).trans_eq (by simp))
  have hT (b : Bool) : IsVecLatHom (T b) := by
    apply IsVecLatHom.of_abs
      { map_add := (T b).map_add, map_smul := (T b).map_smul }
    intro f
    ext q
    induction q using Quotient.inductionOn with
    | h q =>
      cases b
      · change (1 - (q.2.2 : ℝ)) * |f q.1| + (q.2.2 : ℝ) * 0 =
          |(1 - (q.2.2 : ℝ)) * f q.1 + (q.2.2 : ℝ) * 0|
        simp [abs_mul, abs_of_nonneg (sub_nonneg.mpr q.2.2.2.2)]
      · change (1 - (q.2.2 : ℝ)) * 0 + (q.2.2 : ℝ) * |f q.2.1| =
          |(1 - (q.2.2 : ℝ)) * 0 + (q.2.2 : ℝ) * f q.2.1|
        simp [abs_mul, abs_of_nonneg q.2.2.2.1]
  have hbound (b : Bool) : ‖T b‖ ≤ 1 := by
    cases b
    · exact LinearMap.mkContinuous_norm_le _ zero_le_one _
    · exact LinearMap.mkContinuous_norm_le _ zero_le_one _
  obtain ⟨S, ⟨hS, hST, hSnorm⟩, _⟩ :=
    P.exists_unique_extension _ T hT 1 zero_le_one hbound
  exact ⟨S, hS, hSnorm, hST false, hST true⟩

omit [∀ b, T2Space (K b)] in
/-- A scalar character normalized at the sum of the factor units is evaluation at a point of
the join. -/
private lemma scalar_eq_join_eval
    (S : P.Carrier →L[ℝ] C(Join (K false) (K true), ℝ)) (hS : IsVecLatHom S)
    (hleft : ∀ f, S (P.inclusion false f) = interpolate (K false) (K true) f 0)
    (hright : ∀ g, S (P.inclusion true g) = interpolate (K false) (K true) 0 g)
    (F : P.Carrier →L[ℝ] ℝ) (hF : IsVecLatHom F)
    (hunit : F (P.inclusion false 1 + P.inclusion true 1) = 1) :
    ∃ q, ∀ z, F z = S z q := by
  let G := hF.mk' F
  let j (b : Bool) := (P.inclusion_isVecLatHom b).mk' (P.inclusion b)
  obtain ⟨x, hx⟩ := exists_weighted_eval (G.comp (j false))
  obtain ⟨y, hy⟩ := exists_weighted_eval (G.comp (j true))
  have hpos (b : Bool) : 0 ≤ F (P.inclusion b 1) :=
    (G.comp (j b)).map_nonneg (fun _ ↦ zero_le_one)
  have hsum : F (P.inclusion false 1) + F (P.inclusion true 1) = 1 :=
    ((F.map_add _ _).symm).trans hunit
  let t : Set.Icc (0 : ℝ) 1 :=
    ⟨F (P.inclusion true 1), hpos true, by linarith [hpos false]⟩
  let q := joinMk (K false) (K true) x y t
  let H := (ContinuousMap.evalCLM ℝ q).comp S
  have hH : IsVecLatHom H :=
    { map_add := H.map_add
      map_smul := H.map_smul
      map_sup' := fun z w ↦ congrArg (fun f : C(Join (K false) (K true), ℝ) ↦ f q)
        (hS.map_sup' z w)
      map_inf' := fun z w ↦ congrArg (fun f : C(Join (K false) (K true), ℝ) ↦ f q)
        (hS.map_inf' z w) }
  have hfactor (b : Bool) (f : C(K b, ℝ)) : F (P.inclusion b f) = H (P.inclusion b f) := by
    cases b
    · change F (P.inclusion false f) = S (P.inclusion false f) q
      rw [hleft]
      change F (P.inclusion false f) =
        (1 - F (P.inclusion true 1)) * f x + F (P.inclusion true 1) * 0
      have hcoeff : F (P.inclusion false 1) = 1 - F (P.inclusion true 1) := by linarith
      simpa only [hcoeff, mul_zero, add_zero] using
        (show F (P.inclusion false f) = F (P.inclusion false 1) * f x from hx f)
    · change F (P.inclusion true f) = S (P.inclusion true f) q
      rw [hright]
      exact (show F (P.inclusion true f) = F (P.inclusion true 1) * f y from hy f).trans
        (by simp [q, interpolate_joinMk, t])
  exact ⟨q, fun z ↦ DFunLike.congr_fun (P.extension_ext hF hH hfactor) z⟩

/-- Scalar lattice homomorphisms normalized at the sum of the two canonical units. -/
def JoinCharacter :=
  {F : VecLatHom P.Carrier ℝ // F (P.inclusion false 1 + P.inclusion true 1) = 1}

/-- Normalized characters carry the topology of pointwise convergence. -/
instance instTopologicalSpaceJoinCharacter : TopologicalSpace (JoinCharacter K P) :=
  TopologicalSpace.induced (fun F : JoinCharacter K P ↦ (F.val : P.Carrier → ℝ))
    Pi.topologicalSpace

/-- Point evaluations separate normalized characters. -/
instance instT2SpaceJoinCharacter : T2Space (JoinCharacter K P) :=
  T2Space.of_injective_continuous
    (f := fun F : JoinCharacter K P ↦ (F.val : P.Carrier → ℝ))
    (fun _ _ h ↦ Subtype.ext (DFunLike.coe_injective h)) continuous_induced_dom

omit [∀ b, T2Space (K b)] [∀ b, Nonempty (K b)] in
private lemma join_extension_interpolate
    (S : P.Carrier →L[ℝ] C(Join (K false) (K true), ℝ))
    (hleft : ∀ f, S (P.inclusion false f) = interpolate (K false) (K true) f 0)
    (hright : ∀ g, S (P.inclusion true g) = interpolate (K false) (K true) 0 g)
    (f : C(K false, ℝ)) (g : C(K true, ℝ)) :
    S (P.inclusion false f + P.inclusion true g) =
      interpolate (K false) (K true) f g := by
  rw [S.map_add, hleft, hright]
  exact ContinuousMap.ext (fun q ↦ Quotient.inductionOn q (fun q ↦ by
    change ((1 - (q.2.2 : ℝ)) * f q.1 + (q.2.2 : ℝ) * 0) +
      ((1 - (q.2.2 : ℝ)) * 0 + (q.2.2 : ℝ) * g q.2.1) =
        (1 - (q.2.2 : ℝ)) * f q.1 + (q.2.2 : ℝ) * g q.2.1
    ring))

private def joinCharacterOfPoint
    (S : P.Carrier →L[ℝ] C(Join (K false) (K true), ℝ)) (hS : IsVecLatHom S)
    (hleft : ∀ f, S (P.inclusion false f) = interpolate (K false) (K true) f 0)
    (hright : ∀ g, S (P.inclusion true g) = interpolate (K false) (K true) 0 g)
    (q : Join (K false) (K true)) : JoinCharacter K P :=
  ⟨{ toLinearMap := ((ContinuousMap.evalCLM ℝ q).comp S).toLinearMap
     map_sup' := fun z w ↦ congrArg (fun f : C(Join (K false) (K true), ℝ) ↦ f q)
       (hS.map_sup' z w)
     map_inf' := fun z w ↦ congrArg (fun f : C(Join (K false) (K true), ℝ) ↦ f q)
       (hS.map_inf' z w) },
    (congrArg (fun f : C(Join (K false) (K true), ℝ) ↦ f q)
      (join_extension_interpolate K P S hleft hright 1 1)).trans
      (Quotient.inductionOn q (fun p ↦
        show (1 - (p.2.2 : ℝ)) * 1 + (p.2.2 : ℝ) * 1 = 1 from by simp))⟩

omit [∀ b, T2Space (K b)] [∀ b, Nonempty (K b)] in
private lemma continuous_joinCharacterOfPoint
    (S : P.Carrier →L[ℝ] C(Join (K false) (K true), ℝ)) (hS : IsVecLatHom S)
    (hleft : ∀ f, S (P.inclusion false f) = interpolate (K false) (K true) f 0)
    (hright : ∀ g, S (P.inclusion true g) = interpolate (K false) (K true) 0 g) :
    Continuous (joinCharacterOfPoint K P S hS hleft hright) :=
  continuous_induced_rng.mpr (continuous_pi (fun z ↦ (S z).continuous))

omit [∀ b, Nonempty (K b)] in
private lemma joinCharacterOfPoint_injective
    (S : P.Carrier →L[ℝ] C(Join (K false) (K true), ℝ)) (hS : IsVecLatHom S)
    (hleft : ∀ f, S (P.inclusion false f) = interpolate (K false) (K true) f 0)
    (hright : ∀ g, S (P.inclusion true g) = interpolate (K false) (K true) 0 g) :
    Function.Injective (joinCharacterOfPoint K P S hS hleft hright) :=
  fun p q h ↦ join_eq_of_interpolate_eq (K false) (K true) (fun f g ↦
    (congrArg (fun k : C(Join (K false) (K true), ℝ) ↦ k p)
      (join_extension_interpolate K P S hleft hright f g)).symm.trans
      ((congrArg (fun F : JoinCharacter K P ↦
        F.val (P.inclusion false f + P.inclusion true g)) h).trans
        (congrArg (fun k : C(Join (K false) (K true), ℝ) ↦ k q)
          (join_extension_interpolate K P S hleft hright f g))))

omit [∀ b, T2Space (K b)] in
private lemma joinCharacterOfPoint_surjective
    (S : P.Carrier →L[ℝ] C(Join (K false) (K true), ℝ)) (hS : IsVecLatHom S)
    (hleft : ∀ f, S (P.inclusion false f) = interpolate (K false) (K true) f 0)
    (hright : ∀ g, S (P.inclusion true g) = interpolate (K false) (K true) 0 g) :
    Function.Surjective (joinCharacterOfPoint K P S hS hleft hright) :=
  fun F ↦ (scalar_eq_join_eval K P S hS hleft hright
    { toLinearMap := F.val.toLinearMap
      cont := Positive.continuous (Positive.monotone_iff.mp F.val.monotone) }
    F.val.isVecLatHom F.property).elim (fun q hq ↦
      ⟨q, Subtype.ext (DFunLike.ext _ _ (fun z ↦ (hq z).symm))⟩)

private def joinCharacterHomeomorphOfExtension
    (S : P.Carrier →L[ℝ] C(Join (K false) (K true), ℝ)) (hS : IsVecLatHom S)
    (hleft : ∀ f, S (P.inclusion false f) = interpolate (K false) (K true) f 0)
    (hright : ∀ g, S (P.inclusion true g) = interpolate (K false) (K true) 0 g) :
    Join (K false) (K true) ≃ₜ JoinCharacter K P :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (joinCharacterOfPoint K P S hS hleft hright)
      ⟨joinCharacterOfPoint_injective K P S hS hleft hright,
        joinCharacterOfPoint_surjective K P S hS hleft hright⟩)
    (continuous_joinCharacterOfPoint K P S hS hleft hright)

/-- The normalized scalar character space of the free product is homeomorphic to the join. -/
def joinCharacterHomeomorph : JoinCharacter K P ≃ₜ Join (K false) (K true) :=
  let S := (exists_join_extension K P).choose
  let hS := (exists_join_extension K P).choose_spec
  (joinCharacterHomeomorphOfExtension K P S hS.1 hS.2.2.1 hS.2.2.2).symm

/-- The character associated with a join point restricts to the weighted point evaluations
on the two canonical factors. -/
theorem joinCharacterHomeomorph_symm_apply_inclusions
    (x : K false) (y : K true) (t : Set.Icc (0 : ℝ) 1)
    (f : C(K false, ℝ)) (g : C(K true, ℝ)) :
    ((joinCharacterHomeomorph K P).symm (joinMk (K false) (K true) x y t)).val
      (P.inclusion false f + P.inclusion true g) = (1 - (t : ℝ)) * f x + (t : ℝ) * g y :=
  congrArg (fun k : C(Join (K false) (K true), ℝ) ↦ k (joinMk _ _ x y t))
    (join_extension_interpolate K P (exists_join_extension K P).choose
      (exists_join_extension K P).choose_spec.2.2.1
      (exists_join_extension K P).choose_spec.2.2.2 f g)

omit [∀ b, T2Space (K b)] in
/-- The sum of the two included constant functions is strictly positive. -/
private lemma inclusion_sum_pos : 0 < P.inclusion false 1 + P.inclusion true 1 := by
  have hpos (b : Bool) : 0 ≤ P.inclusion b 1 :=
    ((P.inclusion_isVecLatHom b).mk' (P.inclusion b)).map_nonneg (fun _ ↦ zero_le_one)
  have hne : P.inclusion false 1 ≠ 0 := by
    intro h
    have heq := (P.isometry_inclusion false).injective
      (h.trans ((P.inclusion false).map_zero).symm)
    exact one_ne_zero heq
  exact lt_of_lt_of_le (lt_of_le_of_ne (hpos false) hne.symm)
    (le_add_of_nonneg_right (hpos true))

omit [∀ b, T2Space (K b)] in
/-- The free-product norm is at most twice the supremum norm in the join representation. -/
private lemma norm_le_two_mul_join
    (S : P.Carrier →L[ℝ] C(Join (K false) (K true), ℝ)) (hS : IsVecLatHom S)
    (hleft : ∀ f, S (P.inclusion false f) = interpolate (K false) (K true) f 0)
    (hright : ∀ g, S (P.inclusion true g) = interpolate (K false) (K true) 0 g) :
    ∀ z, ‖z‖ ≤ 2 * ‖S z‖ := by
  let e := P.inclusion false 1 + P.inclusion true 1
  have he : 0 < e := inclusion_sum_pos K P
  have hmem (z : P.Carrier) : z ∈ OrderIdeal.principal e :=
    ((OrderIdeal.strongOrderUnit_iff_principal_eq_top.mp
      (strongOrderUnit_inclusion_one_add K P)).2.symm ▸
      (show z ∈ (⊤ : OrderIdeal P.Carrier) from OrderIdeal.mem_top))
  let := OrderIdeal.principalNormedAddCommGroup e
  let : Lattice ↥(OrderIdeal.principal e) := OrderIdeal.instLatticePrincipal e
  let : IsOrderedAddMonoid ↥(OrderIdeal.principal e) :=
    OrderIdeal.instIsOrderedAddMonoidPrincipal e
  let : IsUniformlyCompleteVectorLattice P.Carrier :=
    isUniformlyCompleteVectorLattice_of_banachLattice P.Carrier
  let : AMSpaceWithUnit ↥(OrderIdeal.principal e) :=
    OrderIdeal.principalAMSpaceWithUnit he.le
      (IsUniformlyCompleteVectorLattice.complete_principal e he)
  have : Nontrivial ↥(OrderIdeal.principal e) :=
    ⟨⟨⟨e, OrderIdeal.self_mem_principal e⟩, 0,
      fun h ↦ (ne_of_gt he) (congrArg Subtype.val h)⟩⟩
  let j : VecLatHom P.Carrier ↥(OrderIdeal.principal e) :=
    { toLinearMap := (LinearMap.id : P.Carrier →ₗ[ℝ] P.Carrier).codRestrict
        (OrderIdeal.principal e).toSubmodule hmem
      map_sup' := fun _ _ ↦ Subtype.ext rfl
      map_inf' := fun _ _ ↦ Subtype.ext rfl }
  intro z
  obtain ⟨φ, hφ⟩ := AMSpaceWithUnit.LatticeCharacter.exists_abs_apply_eq_norm
    (X := ↥(OrderIdeal.principal e)) (j z)
  let G := φ.toVecLatHom.comp j
  let F : P.Carrier →L[ℝ] ℝ :=
    { toLinearMap := G.toLinearMap
      cont := Positive.continuous (Positive.monotone_iff.mp G.monotone) }
  obtain ⟨q, hq⟩ := scalar_eq_join_eval K P S hS hleft hright F G.isVecLatHom φ.map_unit
  have hgauge : OrderIdeal.gaugeNorm e z ≤ ‖S z‖ :=
    calc
      OrderIdeal.gaugeNorm e z = |F z| := hφ.symm
      _ = |S z q| := congrArg abs (hq z)
      _ ≤ ‖S z‖ := by simpa only [Real.norm_eq_abs] using (S z).norm_coe_le_norm q
  have hnorm (b : Bool) : ‖P.inclusion b 1‖ ≤ 1 :=
    ((P.inclusion b).le_of_opNorm_le (P.inclusion_contractive b) 1).trans_eq (by simp)
  have henorm : ‖e‖ ≤ 2 := (norm_add_le _ _).trans
    ((add_le_add (hnorm false) (hnorm true)).trans_eq (by norm_num))
  calc
    ‖z‖ ≤ ‖OrderIdeal.gaugeNorm e z • |e|‖ :=
      norm_le_norm_of_abs_le_abs
        ((OrderIdeal.abs_le_gaugeNorm_smul_abs e (hmem z)).trans_eq
          (abs_of_nonneg (smul_nonneg (OrderIdeal.gaugeNorm_nonneg e z) (abs_nonneg e))).symm)
    _ = OrderIdeal.gaugeNorm e z * ‖e‖ := by
      rw [norm_smul, Real.norm_of_nonneg (OrderIdeal.gaugeNorm_nonneg e z), norm_abs_eq_norm]
    _ ≤ ‖S z‖ * 2 := mul_le_mul hgauge henorm (norm_nonneg e) (norm_nonneg _)
    _ = 2 * ‖S z‖ := mul_comm _ _

/-- Transporting continuous functions through the character homeomorphism and the
principal-ideal representation gives surjectivity. -/
private lemma join_map_surjective
    (S : P.Carrier →L[ℝ] C(Join (K false) (K true), ℝ)) (hS : IsVecLatHom S)
    (hleft : ∀ f, S (P.inclusion false f) = interpolate (K false) (K true) f 0)
    (hright : ∀ g, S (P.inclusion true g) = interpolate (K false) (K true) 0 g) :
    Function.Surjective S := by
  let e := P.inclusion false 1 + P.inclusion true 1
  have he : 0 < e := inclusion_sum_pos K P
  have hmem (z : P.Carrier) : z ∈ OrderIdeal.principal e :=
    ((OrderIdeal.strongOrderUnit_iff_principal_eq_top.mp
      (strongOrderUnit_inclusion_one_add K P)).2.symm ▸
      (show z ∈ (⊤ : OrderIdeal P.Carrier) from OrderIdeal.mem_top))
  let := OrderIdeal.principalNormedAddCommGroup e
  let : Lattice ↥(OrderIdeal.principal e) := OrderIdeal.instLatticePrincipal e
  let : IsOrderedAddMonoid ↥(OrderIdeal.principal e) :=
    OrderIdeal.instIsOrderedAddMonoidPrincipal e
  let : IsUniformlyCompleteVectorLattice P.Carrier :=
    isUniformlyCompleteVectorLattice_of_banachLattice P.Carrier
  let : AMSpaceWithUnit ↥(OrderIdeal.principal e) :=
    OrderIdeal.principalAMSpaceWithUnit he.le
      (IsUniformlyCompleteVectorLattice.complete_principal e he)
  let j : VecLatHom P.Carrier ↥(OrderIdeal.principal e) :=
    { toLinearMap := (LinearMap.id : P.Carrier →ₗ[ℝ] P.Carrier).codRestrict
        (OrderIdeal.principal e).toSubmodule hmem
      map_sup' := fun _ _ ↦ Subtype.ext rfl
      map_inf' := fun _ _ ↦ Subtype.ext rfl }
  let h := joinCharacterHomeomorphOfExtension K P S hS hleft hright
  let r (φ : AMSpaceWithUnit.LatticeCharacter ↥(OrderIdeal.principal e)) :
      JoinCharacter K P := ⟨φ.toVecLatHom.comp j, φ.map_unit⟩
  have hr : Continuous r := continuous_induced_rng.mpr (continuous_pi (fun z ↦
    AMSpaceWithUnit.LatticeCharacter.continuous_eval _ (j z)))
  intro f
  let g : C(AMSpaceWithUnit.LatticeCharacter ↥(OrderIdeal.principal e), ℝ) :=
    ⟨fun φ ↦ f (h.symm (r φ)), f.continuous.comp (h.symm.continuous.comp hr)⟩
  let R := OrderIdeal.principalKakutaniEquiv he
  refine ⟨(R.symm g).val, ContinuousMap.ext (fun q ↦ ?_)⟩
  let φ : AMSpaceWithUnit.LatticeCharacter ↥(OrderIdeal.principal e) :=
    { toVecLatHom := (h q).val.comp (OrderIdeal.principal e).toVectorSublattice.subtype
      map_unit := (h q).property }
  have hφ : r φ = h q := Subtype.ext (DFunLike.ext _ _ (fun _ ↦ rfl))
  exact (show S (R.symm g).val q = f (h.symm (r φ)) from
    congrArg (fun k : C(AMSpaceWithUnit.LatticeCharacter ↥(OrderIdeal.principal e), ℝ) ↦ k φ)
      (R.apply_symm_apply g)).trans
    (congrArg f ((congrArg h.symm hφ).trans (h.symm_apply_apply q)))

/-- The canonical map from the free product onto continuous functions on the join is
bijective. -/
private lemma join_map_bijective
    (S : P.Carrier →L[ℝ] C(Join (K false) (K true), ℝ)) (hS : IsVecLatHom S)
    (hleft : ∀ f, S (P.inclusion false f) = interpolate (K false) (K true) f 0)
    (hright : ∀ g, S (P.inclusion true g) = interpolate (K false) (K true) 0 g) :
    Function.Bijective S := by
  have hbound := norm_le_two_mul_join K P S hS hleft hright
  have hanti : AntilipschitzWith 2 S := by
    apply AntilipschitzWith.of_le_mul_dist
    exact fun z w ↦ by simpa only [dist_eq_norm, map_sub, NNReal.coe_ofNat] using hbound (z - w)
  exact ⟨hanti.injective, join_map_surjective K P S hS hleft hright⟩

omit [∀ b, T2Space (K b)] in
/-- Domination by nonnegative multiples of the two factor units bounds the norm by the sum of
those coefficients. -/
private lemma norm_le_of_abs_le_majorant {z : P.Carrier} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hz : |z| ≤ a • P.inclusion false 1 + b • P.inclusion true 1) : ‖z‖ ≤ a + b := by
  have hpos (i : Bool) : 0 ≤ P.inclusion i 1 :=
    ((P.inclusion_isVecLatHom i).mk' (P.inclusion i)).map_nonneg (fun _ ↦ zero_le_one)
  have hnorm (i : Bool) : ‖P.inclusion i 1‖ ≤ 1 :=
    ((P.inclusion i).le_of_opNorm_le (P.inclusion_contractive i) 1).trans_eq (by simp)
  calc
    ‖z‖ ≤ ‖a • P.inclusion false 1 + b • P.inclusion true 1‖ :=
      norm_le_norm_of_abs_le_abs (hz.trans_eq
        (abs_of_nonneg (add_nonneg (smul_nonneg ha (hpos false))
          (smul_nonneg hb (hpos true)))).symm)
    _ ≤ ‖a • P.inclusion false 1‖ + ‖b • P.inclusion true 1‖ := norm_add_le _ _
    _ = a * ‖P.inclusion false 1‖ + b * ‖P.inclusion true 1‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    _ ≤ a + b := by nlinarith [hnorm false, hnorm true]

omit [∀ b, T2Space (K b)] [∀ b, Nonempty (K b)] in
/-- The set defined by two-unit majorants of total coefficient at most one is balanced. -/
private lemma majorant_ball_balanced (u : Bool → P.Carrier) :
    Balanced ℝ {w : P.Carrier | ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a + b ≤ 1 ∧
      |w| ≤ a • u false + b • u true} := by
  intro c hc w hw
  rcases hw with ⟨v, ⟨a, b, ha, hb, hab, hv⟩, rfl⟩
  refine ⟨|c| * a, |c| * b, mul_nonneg (abs_nonneg _) ha,
    mul_nonneg (abs_nonneg _) hb, ?_, ?_⟩
  · have hc' : |c| ≤ 1 := hc
    nlinarith [mul_le_mul hc' hab (add_nonneg ha hb) zero_le_one]
  · calc
      |c • v| = |c| • |v| := abs_smul' v c
      _ ≤ |c| • (a • u false + b • u true) :=
        smul_le_smul_of_nonneg_left hv (abs_nonneg _)
      _ = (|c| * a) • u false + (|c| * b) • u true := by rw [smul_add, smul_smul, smul_smul]

omit [∀ b, T2Space (K b)] [∀ b, Nonempty (K b)] in
/-- The set defined by two-unit majorants of total coefficient at most one is convex. -/
private lemma majorant_ball_convex (u : Bool → P.Carrier) :
    Convex ℝ {w : P.Carrier | ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a + b ≤ 1 ∧
      |w| ≤ a • u false + b • u true} := by
  rintro x ⟨ax, bx, hax, hbx, habx, hx⟩ y ⟨ay, by', hay, hby, haby, hy⟩ s t hs ht hst
  refine ⟨s * ax + t * ay, s * bx + t * by',
    add_nonneg (mul_nonneg hs hax) (mul_nonneg ht hay),
    add_nonneg (mul_nonneg hs hbx) (mul_nonneg ht hby), ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left habx hs, mul_le_mul_of_nonneg_left haby ht]
  · calc
      |s • x + t • y| ≤ |s • x| + |t • y| := abs_add_le _ _
      _ = s • |x| + t • |y| := by rw [abs_smul', abs_smul', abs_of_nonneg hs, abs_of_nonneg ht]
      _ ≤ s • (ax • u false + bx • u true) + t • (ay • u false + by' • u true) :=
        add_le_add (smul_le_smul_of_nonneg_left hx hs) (smul_le_smul_of_nonneg_left hy ht)
      _ = (s * ax + t * ay) • u false + (s * bx + t * by') • u true := by
        simp only [smul_add, smul_smul, add_smul]
        abel

omit [∀ b, T2Space (K b)] [∀ b, Nonempty (K b)] in
/-- Scaling the majorant set by a positive scalar scales the allowed sum of its two
coefficients. -/
private lemma mem_smul_majorant_ball (u : Bool → P.Carrier)
    (r : ℝ) (hr : 0 < r) (w : P.Carrier) :
    w ∈ r • {v : P.Carrier | ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a + b ≤ 1 ∧
      |v| ≤ a • u false + b • u true} ↔
      ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a + b ≤ r ∧ |w| ≤ a • u false + b • u true := by
  constructor
  · rintro ⟨v, ⟨a, b, ha, hb, hab, hv⟩, rfl⟩
    refine ⟨r * a, r * b, mul_nonneg hr.le ha, mul_nonneg hr.le hb, ?_, ?_⟩
    · nlinarith [mul_le_mul_of_nonneg_left hab hr.le]
    · calc
        |r • v| = r • |v| := by rw [abs_smul', abs_of_nonneg hr.le]
        _ ≤ r • (a • u false + b • u true) := smul_le_smul_of_nonneg_left hv hr.le
        _ = (r * a) • u false + (r * b) • u true := by rw [smul_add, smul_smul, smul_smul]
  · rintro ⟨a, b, ha, hb, hab, hw⟩
    refine ⟨r⁻¹ • w, ⟨r⁻¹ * a, r⁻¹ * b, mul_nonneg (inv_nonneg.mpr hr.le) ha,
      mul_nonneg (inv_nonneg.mpr hr.le) hb, ?_, ?_⟩, ?_⟩
    · calc
        r⁻¹ * a + r⁻¹ * b = r⁻¹ * (a + b) := (mul_add _ _ _).symm
        _ ≤ r⁻¹ * r := mul_le_mul_of_nonneg_left hab (inv_nonneg.mpr hr.le)
        _ = 1 := inv_mul_cancel₀ hr.ne'
    · calc
        |r⁻¹ • w| = r⁻¹ • |w| := by rw [abs_smul', abs_of_nonneg (inv_nonneg.mpr hr.le)]
        _ ≤ r⁻¹ • (a • u false + b • u true) :=
          smul_le_smul_of_nonneg_left hw (inv_nonneg.mpr hr.le)
        _ = (r⁻¹ * a) • u false + (r⁻¹ * b) • u true := by rw [smul_add, smul_smul, smul_smul]
    · simp [smul_smul, hr.ne']

omit [∀ b, T2Space (K b)] in
/-- The free-product norm is the infimum of the coefficient sums of all two-unit majorants. -/
private lemma norm_eq_inf_majorants (z : P.Carrier) :
    ‖z‖ = sInf {r : ℝ | ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ r = a + b ∧
      |z| ≤ a • P.inclusion false 1 + b • P.inclusion true 1} := by
  let u (b : Bool) := P.inclusion b 1
  let B : Set P.Carrier := {w | ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a + b ≤ 1 ∧
    |w| ≤ a • u false + b • u true}
  have hpos (b : Bool) : 0 ≤ u b :=
    ((P.inclusion_isVecLatHom b).mk' (P.inclusion b)).map_nonneg (fun _ ↦ zero_le_one)
  have hBn : B ⊆ Metric.closedBall 0 1 := by
    rintro w ⟨a, b, ha, hb, hab, hw⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      (norm_le_of_abs_le_majorant K P ha hb hw).trans hab
  have hBnhds : B ∈ 𝓝 (0 : P.Carrier) := by
    apply Metric.mem_nhds_iff.mpr
    refine ⟨1 / 2, by norm_num, fun w hw ↦ ⟨‖w‖, ‖w‖, norm_nonneg _, norm_nonneg _, ?_, ?_⟩⟩
    · have hw' : ‖w‖ < 1 / 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hw
      linarith
    · simpa only [smul_add, u] using abs_le_norm_smul_join_unit K P w
  have hBbal : Balanced ℝ B := majorant_ball_balanced K P u
  have hBconv : Convex ℝ B := majorant_ball_convex K P u
  have hscaled (r : ℝ) (hr : 0 < r) (w : P.Carrier) :
      w ∈ r • B ↔ ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a + b ≤ r ∧
        |w| ≤ a • u false + b • u true := mem_smul_majorant_ball K P u r hr w
  have hAbs : Absorbent ℝ B := absorbent_nhds_zero hBnhds
  let p : Seminorm ℝ P.Carrier := gaugeSeminorm hBbal hBconv hAbs
  have hlow (w : P.Carrier) : ‖w‖ ≤ p w :=
    (div_one ‖w‖).symm.trans_le (le_gauge_of_subset_closedBall hAbs zero_le_one hBn)
  have hsolid (x y : P.Carrier) (hxy : |x| ≤ |y|) : p x ≤ p y := by
    apply le_of_forall_gt
    intro r hr
    obtain ⟨s, hs, hsr, hy⟩ := exists_lt_of_gauge_lt hAbs hr
    rcases (hscaled s hs y).mp hy with ⟨a, b, ha, hb, hab, hy⟩
    exact (gauge_le_of_mem hs.le ((hscaled s hs x).mpr
      ⟨a, b, ha, hb, hab, hxy.trans hy⟩)).trans_lt hsr
  have hBu (i : Bool) : u i ∈ B := by
    cases i
    · exact ⟨1, 0, zero_le_one, le_rfl, by norm_num,
        by simp only [one_smul, zero_smul, add_zero, abs_of_nonneg (hpos false), le_refl]⟩
    · exact ⟨0, 1, le_rfl, zero_le_one, by norm_num,
        by simp only [one_smul, zero_smul, zero_add, abs_of_nonneg (hpos true), le_refl]⟩
  have hfactor (i : Bool) (f : C(K i, ℝ)) : p (P.inclusion i f) ≤ ‖f‖ := by
    calc
      p (P.inclusion i f) ≤ p (‖f‖ • u i) := hsolid _ _
        ((inclusion_abs_le_norm_smul_one K P i f).trans_eq
          (abs_of_nonneg (smul_nonneg (norm_nonneg f) (hpos i))).symm)
      _ = ‖f‖ * p (u i) := by rw [map_smul_eq_mul, Real.norm_of_nonneg (norm_nonneg f)]
      _ ≤ ‖f‖ := mul_le_of_le_one_right (norm_nonneg f) (gauge_le_one_of_mem (hBu i))
  have hpgen := P.seminorm_le_norm (p.comp P.generated.toSubmodule.subtype)
    (fun w hw ↦ Subtype.ext (norm_eq_zero.mp
      (le_antisymm ((hlow w).trans_eq hw) (norm_nonneg _))))
    (fun x y hxy ↦ hsolid x y hxy)
    (fun i f w hw ↦ (congrArg p hw).le.trans (hfactor i f))
  have hpcont : Continuous p := continuous_gauge hBconv hBnhds
  have hupper : ∀ w : P.Carrier, p w ≤ ‖w‖ :=
    P.dense_generated.induction (fun w hw ↦ hpgen ⟨w, hw⟩)
      (isClosed_le hpcont continuous_norm)
  let R : Set ℝ := {r | ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ r = a + b ∧
    |z| ≤ a • u false + b • u true}
  have hRne : R.Nonempty := ⟨‖z‖ + ‖z‖, ‖z‖, ‖z‖, norm_nonneg _, norm_nonneg _, rfl,
    by simpa only [smul_add, u] using abs_le_norm_smul_join_unit K P z⟩
  have hRbdd : BddBelow R := ⟨0, fun _ ⟨a, b, ha, hb, hr, _⟩ ↦ hr ▸ add_nonneg ha hb⟩
  change ‖z‖ = sInf R
  apply le_antisymm
  · exact le_csInf hRne (fun r ⟨a, b, ha, hb, hr, hz⟩ ↦
      (norm_le_of_abs_le_majorant K P ha hb hz).trans_eq hr.symm)
  · apply le_of_forall_gt
    intro r hr
    obtain ⟨s, hs, hsr, hz⟩ := exists_lt_of_gauge_lt hAbs ((hupper z).trans_lt hr)
    rcases (hscaled s hs z).mp hz with ⟨a, b, ha, hb, hab, hz⟩
    exact (csInf_le hRbdd ⟨a, b, ha, hb, rfl, hz⟩).trans_lt (hab.trans_lt hsr)

omit [∀ b, T2Space (K b)] [∀ b, Nonempty (K b)] in
/-- Under the join representation, two-unit domination is exactly the pointwise bound by the
corresponding affine interpolation of the coefficients. -/
private lemma join_majorant_iff
    (e : VecLatEquiv P.Carrier C(Join (K false) (K true), ℝ))
    (hleft : ∀ f, e (P.inclusion false f) = interpolate (K false) (K true) f 0)
    (hright : ∀ g, e (P.inclusion true g) = interpolate (K false) (K true) 0 g)
    (z : P.Carrier) (a b : ℝ) :
    |z| ≤ a • P.inclusion false 1 + b • P.inclusion true 1 ↔
      ∀ x y t, |e z (joinMk (K false) (K true) x y t)| ≤
        (1 - (t : ℝ)) * a + (t : ℝ) * b := by
  let E := e.toVecLatHom
  have hvalue (x : K false) (y : K true) (t : Set.Icc (0 : ℝ) 1) :
      E (a • P.inclusion false 1 + b • P.inclusion true 1)
          (joinMk (K false) (K true) x y t) = (1 - (t : ℝ)) * a + (t : ℝ) * b := by
    rw [map_add, map_smul, map_smul]
    change a * e (P.inclusion false 1) (joinMk (K false) (K true) x y t) +
      b * e (P.inclusion true 1) (joinMk (K false) (K true) x y t) = _
    rw [hleft, hright]
    simp [interpolate_joinMk, mul_comm]
  constructor
  · intro hz x y t
    exact ((congrArg (fun f : C(Join (K false) (K true), ℝ) ↦
      f (joinMk (K false) (K true) x y t)) (E.map_abs z)).symm.le.trans
        (E.monotone hz (joinMk (K false) (K true) x y t))).trans_eq (hvalue x y t)
  · intro h
    apply E.le_of_map_le e.toLinearEquiv.injective
    intro q
    induction q using Quotient.inductionOn with
    | h q =>
      exact (congrArg (fun f : C(Join (K false) (K true), ℝ) ↦ f ⟦q⟧) (E.map_abs z)).le.trans
        ((h q.1 q.2.1 q.2.2).trans_eq (hvalue q.1 q.2.1 q.2.2).symm)

/-- The binary free product of continuous-function lattices is lattice
isomorphic to the continuous functions on the join, with its explicit norm. -/
theorem exists_join_equiv :
    ∃ e : VecLatEquiv P.Carrier C(Join (K false) (K true), ℝ),
      (∀ f, e (P.inclusion false f) =
        interpolate (K false) (K true) f 0) ∧
      (∀ g, e (P.inclusion true g) =
        interpolate (K false) (K true) 0 g) ∧
      (∀ z, ‖e z‖ ≤ ‖z‖ ∧ ‖z‖ ≤ 2 * ‖e z‖) ∧
      (∀ f : C(Join (K false) (K true), ℝ),
        ‖e.symm f‖ =
          sInf {r : ℝ | ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ r = a + b ∧
            ∀ (x : K false) (y : K true) (t : Set.Icc (0 : ℝ) 1),
              |f (joinMk (K false) (K true) x y t)| ≤
                (1 - (t : ℝ)) * a + (t : ℝ) * b}) := by
  obtain ⟨S, hS, hSnorm, hleft, hright⟩ := exists_join_extension K P
  let e : VecLatEquiv P.Carrier C(Join (K false) (K true), ℝ) :=
    { LinearEquiv.ofBijective S.toLinearMap (join_map_bijective K P S hS hleft hright) with
      map_sup' := hS.map_sup'
      map_inf' := hS.map_inf' }
  refine ⟨e, hleft, hright, fun z ↦ ⟨?_, ?_⟩, ?_⟩
  · exact (S.le_of_opNorm_le hSnorm z).trans_eq (one_mul _)
  · exact norm_le_two_mul_join K P S hS hleft hright z
  · intro f
    rw [norm_eq_inf_majorants K P (e.symm f)]
    congr 1
    ext r
    simp only [Set.mem_ofPred_eq, join_majorant_iff K P e hleft hright,
      show e (e.symm f) = f from e.toLinearEquiv.apply_symm_apply f]

end ContinuousFunctions

end FreeProduct

end BanachLattice
