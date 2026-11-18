/-
Authors: Gonzalo Martínez-Fernández
-/

import FreeProducts.BanachLattice.Join
import BanLat.OrderDense

/-!
# Order properties for continuous-function factors

The join representation of a binary Banach free product transfers order density from
the factor sublattices to the product. Supported positive functions on the join also
show that the canonical inclusions preserve infima equal to zero.
-/

universe u v

namespace BanachLattice.FreeProduct

section ContinuousFunctionOrderProperties

open scoped Topology Pointwise

/-- An order dense function sublattice contains a nonzero positive function supported in any
nonempty open set. -/
private lemma exists_orderDense_supported {K : Type*} [TopologicalSpace K]
    [CompactSpace K] [T2Space K] (D : VectorSublattice C(K, ℝ))
    (hD : D.IsOrderDense) {U : Set K} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ f ∈ D, (0 : C(K, ℝ)) < f ∧ Function.support f ⊆ U := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨g, hg0, hg1, hg⟩ := exists_continuous_zero_one_of_isClosed hU.isClosed_compl
    (isClosed_singleton : IsClosed ({x} : Set K))
    (Set.disjoint_singleton_right.mpr (not_not.mpr hx))
  have hgpos : (0 : C(K, ℝ)) < g := lt_of_le_of_ne (fun y ↦ (hg y).1)
    (fun h ↦ zero_ne_one ((congrArg (fun f : C(K, ℝ) ↦ f x) h).trans
      (hg1 (Set.mem_singleton x))))
  obtain ⟨f, hfD, hfpos, hfg⟩ := hD hgpos
  exact ⟨f, hfD, hfpos, fun y hy ↦ not_not.mp (fun hyU ↦
    hy (le_antisymm ((hfg y).trans_eq (hg0 hyU)) (hfpos.le y)))⟩

/-- The open interior of the unit interval is dense in the closed interval. -/
private lemma dense_interval_interior :
    Dense (Set.Ioo (⊥ : Set.Icc (0 : ℝ) 1) ⊤) := by
  rw [dense_iff_closure_eq, closure_Ioo bot_ne_top]
  exact Set.Icc_bot_top

/-- A nonzero positive function on the join is positive at a point whose interval coordinate
is strictly between zero and one. -/
private lemma exists_pos_interior_join {K L : Type u}
    [TopologicalSpace K] [TopologicalSpace L] (h : C(Join K L, ℝ)) (hh : 0 < h) :
    ∃ (x : K) (y : L) (t : Set.Icc (0 : ℝ) 1),
      0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧ 0 < h (joinMk K L x y t) := by
  obtain ⟨q, hq⟩ := not_forall.mp (show ¬ ∀ q, h q ≤ 0 from fun hle ↦ hh.not_ge hle)
  obtain ⟨⟨x, y, t⟩, rfl⟩ := Quotient.exists_rep q
  have hc : Continuous (fun s : Set.Icc (0 : ℝ) 1 ↦ h (joinMk K L x y s)) :=
    h.continuous.comp (continuous_quotient_mk'.comp
      (continuous_const.prodMk (continuous_const.prodMk continuous_id)))
  obtain ⟨s, hs, hpos⟩ := dense_interval_interior.exists_mem_open
    (isOpen_lt continuous_const hc) ⟨t, lt_of_not_ge hq⟩
  exact ⟨x, y, s, hs.1, hs.2, hpos⟩

/-- A nonzero positive join function is uniformly bounded below by a positive number on a
nonempty open product box. -/
private lemma exists_positive_join_box {K L : Type u}
    [TopologicalSpace K] [TopologicalSpace L] (h : C(Join K L, ℝ)) (hh : 0 < h) :
    ∃ (U : Set K) (V : Set L) (a b : Set.Icc (0 : ℝ) 1) (ε : ℝ),
      IsOpen U ∧ U.Nonempty ∧ IsOpen V ∧ V.Nonempty ∧ a < b ∧ 0 < ε ∧
      ∀ x ∈ U, ∀ y ∈ V, ∀ t ∈ Set.Ioo a b, ε < h (joinMk K L x y t) := by
  obtain ⟨x, y, t, ht0, ht1, ht⟩ := exists_pos_interior_join h hh
  have hc : Continuous (fun p : K × L × Set.Icc (0 : ℝ) 1 ↦
      h (joinMk K L p.1 p.2.1 p.2.2)) := h.continuous.comp continuous_quotient_mk'
  have hmem : {p : K × L × Set.Icc (0 : ℝ) 1 |
      h (joinMk K L x y t) / 2 < h (joinMk K L p.1 p.2.1 p.2.2)} ∈ 𝓝 (x, y, t) :=
    (isOpen_lt continuous_const hc).mem_nhds (half_lt_self ht)
  obtain ⟨U, W, hU, hx, hW, hyt, hUW⟩ := mem_nhds_prod_iff'.mp hmem
  obtain ⟨V, J, hV, hy, hJ, htJ, hVJ⟩ := mem_nhds_prod_iff'.mp (hW.mem_nhds hyt)
  obtain ⟨a, b, hab, hsub⟩ := (mem_nhds_iff_exists_Ioo_subset'
    (show ∃ s : Set.Icc (0 : ℝ) 1, s < t from ⟨⊥, ht0⟩)
    (show ∃ s : Set.Icc (0 : ℝ) 1, t < s from ⟨⊤, ht1⟩)).mp (hJ.mem_nhds htJ)
  exact ⟨U, V, a, b, h (joinMk K L x y t) / 2, hU, ⟨x, hx⟩, hV, ⟨y, hy⟩,
    hab.1.trans hab.2, half_pos ht,
    fun x hx y hy s hs ↦ hUW (a := (x, y, s)) ⟨hx, hVJ (a := (y, s)) ⟨hy, hsub hs⟩⟩⟩

/-- An order dense function sublattice contains a positive function supported in a prescribed
open set and attaining the value one there. -/
private lemma exists_orderDense_normalized {K : Type*} [TopologicalSpace K]
    [CompactSpace K] [T2Space K] (D : VectorSublattice C(K, ℝ))
    (hD : D.IsOrderDense) {U : Set K} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ f ∈ D, (0 : C(K, ℝ)) ≤ f ∧ Function.support f ⊆ U ∧ ∃ x ∈ U, f x = 1 := by
  obtain ⟨g, hgD, hg, hsupp⟩ := exists_orderDense_supported D hD hU hne
  obtain ⟨x, hx⟩ := not_forall.mp (show ¬ ∀ x, g x ≤ 0 from fun hle ↦ hg.not_ge hle)
  refine ⟨(g x)⁻¹ • g, D.smul_mem _ hgD,
    (fun y ↦ mul_nonneg (inv_nonneg.mpr (lt_of_not_ge hx).le) (hg.le y)), ?_,
    x, hsupp (ne_of_gt (lt_of_not_ge hx)), ?_⟩
  · exact fun y hy ↦ hsupp (right_ne_zero_of_mul hy)
  · exact inv_mul_cancel₀ (ne_of_gt (lt_of_not_ge hx))

/-- Constructs a nonnegative lattice tent from the two factor functions, positive near the
selected points and locally confined to the specified interval. -/
private lemma exists_join_tent {K L : Type u}
    [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [TopologicalSpace L] [CompactSpace L] [T2Space L]
    (G : VectorSublattice C(Join K L, ℝ)) (f : C(K, ℝ)) (g : C(L, ℝ))
    (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hF : interpolate K L f 0 ∈ G) (hH : interpolate K L 0 g ∈ G)
    {x : K} {y : L} (hfx : f x = 1) (hgy : g y = 1)
    {a b : ℝ} {t : Set.Icc (0 : ℝ) 1}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hat : a < (t : ℝ)) (htb : (t : ℝ) < b) :
    ∃ w ∈ G, (0 : C(Join K L, ℝ)) ≤ w ∧
      ∃ (U : Set K) (V : Set L), IsOpen U ∧ x ∈ U ∧ IsOpen V ∧ y ∈ V ∧
        (∀ x' ∈ U, ∀ y' ∈ V, 0 < w (joinMk K L x' y' t)) ∧
        (∀ x' ∈ U, ∀ y' ∈ V, ∀ s : Set.Icc (0 : ℝ) 1,
          0 < w (joinMk K L x' y' s) → a < (s : ℝ) ∧ (s : ℝ) < b) := by
  let c := (a + (t : ℝ)) / 2
  let d := ((t : ℝ) + b) / 2
  let w : C(Join K L, ℝ) :=
    ((d • interpolate K L f 0 - (1 - d) • interpolate K L 0 g) ⊓
      ((1 - c) • interpolate K L 0 g - c • interpolate K L f 0)) ⊔ 0
  refine ⟨w, G.sup_mem (G.inf_mem (G.sub_mem (G.smul_mem d hF) (G.smul_mem (1 - d) hH))
    (G.sub_mem (G.smul_mem (1 - c) hH) (G.smul_mem c hF))) G.zero_mem, le_sup_right, ?_⟩
  let O : Set (K × L) := {p |
    d * ((1 - b) * f p.1) - (1 - d) * (b * g p.2) < 0 ∧
    (1 - c) * (a * g p.2) - c * ((1 - a) * f p.1) < 0 ∧
    0 < d * ((1 - (t : ℝ)) * f p.1) - (1 - d) * ((t : ℝ) * g p.2) ∧
    0 < (1 - c) * ((t : ℝ) * g p.2) - c * ((1 - (t : ℝ)) * f p.1)}
  have hO : IsOpen O := by
    have h₁ : IsOpen {p : K × L |
        d * ((1 - b) * f p.1) - (1 - d) * (b * g p.2) < 0} :=
      isOpen_lt (by fun_prop) continuous_const
    have h₂ : IsOpen {p : K × L |
        (1 - c) * (a * g p.2) - c * ((1 - a) * f p.1) < 0} :=
      isOpen_lt (by fun_prop) continuous_const
    have h₃ : IsOpen {p : K × L |
        0 < d * ((1 - (t : ℝ)) * f p.1) - (1 - d) * ((t : ℝ) * g p.2)} :=
      isOpen_lt continuous_const (by fun_prop)
    have h₄ : IsOpen {p : K × L |
        0 < (1 - c) * ((t : ℝ) * g p.2) - c * ((1 - (t : ℝ)) * f p.1)} :=
      isOpen_lt continuous_const (by fun_prop)
    exact h₁.inter (h₂.inter (h₃.inter h₄))
  have hxy : (x, y) ∈ O := by
    simp only [O, Set.mem_ofPred_eq, hfx, hgy, mul_one]
    dsimp [c, d]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  obtain ⟨U, V, hU, hxU, hV, hyV, hUV⟩ := mem_nhds_prod_iff'.mp (hO.mem_nhds hxy)
  have hw (x' : K) (y' : L) (s : Set.Icc (0 : ℝ) 1) :
      0 < w (joinMk K L x' y' s) ↔
        0 < d * ((1 - (s : ℝ)) * f x') - (1 - d) * ((s : ℝ) * g y') ∧
        0 < (1 - c) * ((s : ℝ) * g y') - c * ((1 - (s : ℝ)) * f x') := by
    simp [w, interpolate_joinMk]
  refine ⟨U, V, hU, hxU, hV, hyV,
    fun x' hx' y' hy' ↦ (hw x' y' t).mpr
      (hUV (a := (x', y')) ⟨hx', hy'⟩).2.2, ?_⟩
  intro x' hx' y' hy' s hs
  have hcd : 0 ≤ c ∧ c ≤ 1 ∧ 0 ≤ d ∧ d ≤ 1 := by
    dsimp [c, d]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  have hslopes : 0 ≤ c * f x' + (1 - c) * g y' ∧
      0 ≤ d * f x' + (1 - d) * g y' :=
    ⟨add_nonneg (mul_nonneg hcd.1 (hf x'))
      (mul_nonneg (sub_nonneg.mpr hcd.2.1) (hg y')),
     add_nonneg (mul_nonneg hcd.2.2.1 (hf x'))
      (mul_nonneg (sub_nonneg.mpr hcd.2.2.2) (hg y'))⟩
  constructor <;> by_contra! h
  · nlinarith only [(hUV (a := (x', y')) ⟨hx', hy'⟩).2.1,
      (hw x' y' s).mp hs |>.2,
      mul_nonneg (sub_nonneg.mpr h) hslopes.1]
  · nlinarith only [(hUV (a := (x', y')) ⟨hx', hy'⟩).1,
      (hw x' y' s).mp hs |>.1,
      mul_nonneg (sub_nonneg.mpr h) hslopes.2]

/-- Order dense factor sublattices generate a nonzero positive join function supported inside
any prescribed nonempty open product box. -/
private lemma exists_join_supported {K L : Type u}
    [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [TopologicalSpace L] [CompactSpace L] [T2Space L]
    (D : VectorSublattice C(K, ℝ)) (E : VectorSublattice C(L, ℝ))
    (hD : D.IsOrderDense) (hE : E.IsOrderDense)
    (G : VectorSublattice C(Join K L, ℝ))
    (hDG : ∀ f ∈ D, interpolate K L f 0 ∈ G)
    (hEG : ∀ g ∈ E, interpolate K L 0 g ∈ G)
    {U : Set K} {V : Set L} (hU : IsOpen U) (hneU : U.Nonempty)
    (hV : IsOpen V) (hneV : V.Nonempty)
    {a b : Set.Icc (0 : ℝ) 1} (hab : a < b) :
    ∃ w ∈ G, (0 : C(Join K L, ℝ)) < w ∧
      ∀ x y s, 0 < w (joinMk K L x y s) → x ∈ U ∧ y ∈ V ∧ s ∈ Set.Ioo a b := by
  obtain ⟨f, hfD, hf, _, x, hxU, hfx⟩ := exists_orderDense_normalized D hD hU hneU
  obtain ⟨g, hgE, hg, _, y, hyV, hgy⟩ := exists_orderDense_normalized E hE hV hneV
  obtain ⟨t, hat, htb⟩ := exists_between hab
  obtain ⟨w, hwG, hw, U', V', hU', hxU', hV', hyV', hpos, hsupp⟩ :=
    exists_join_tent G f g hf hg (hDG f hfD) (hEG g hgE) hfx hgy a.property.1
      b.property.2 hat htb
  obtain ⟨f', hf'D, hf', hf'supp, x', hx', hfx'⟩ :=
    exists_orderDense_normalized D hD (hU.inter hU') ⟨x, hxU, hxU'⟩
  obtain ⟨g', hg'E, hg', hg'supp, y', hy', hgy'⟩ :=
    exists_orderDense_normalized E hE (hV.inter hV') ⟨y, hyV, hyV'⟩
  let z := interpolate K L f' 0 ⊓ interpolate K L 0 g' ⊓ w
  have hz : 0 ≤ z := by
    intro q
    induction q using Quotient.inductionOn with
    | h p =>
      rcases p with ⟨x, y, s⟩
      change 0 ≤ z (joinMk K L x y s)
      simp only [z, ContinuousMap.inf_apply, interpolate_joinMk,
        ContinuousMap.zero_apply, mul_zero, add_zero, zero_add]
      exact le_inf (le_inf (mul_nonneg (sub_nonneg.mpr s.property.2) (hf' x))
        (mul_nonneg s.property.1 (hg' y))) (hw _)
  have hzpos : 0 < z (joinMk K L x' y' t) := by
    simpa [z, interpolate_joinMk, hfx', hgy'] using
      lt_min (lt_min (sub_pos.mpr ((show (t : ℝ) < b from htb).trans_le b.property.2))
        (a.property.1.trans_lt (show (a : ℝ) < t from hat))) (hpos x' hx'.2 y' hy'.2)
  refine ⟨z, G.inf_mem (G.inf_mem (hDG f' hf'D) (hEG g' hg'E)) hwG,
    lt_of_le_of_ne hz (fun heq ↦ hzpos.ne (congrArg (fun q : C(Join K L, ℝ) ↦
      q (joinMk K L x' y' t)) heq)), ?_⟩
  intro x y s hs
  have hparts : (0 < (1 - (s : ℝ)) * f' x ∧ 0 < (s : ℝ) * g' y) ∧
      0 < w (joinMk K L x y s) := by
    simpa [z, interpolate_joinMk] using hs
  obtain ⟨hx, hx'⟩ := hf'supp (right_ne_zero_of_mul hparts.1.1.ne')
  obtain ⟨hy, hy'⟩ := hg'supp (right_ne_zero_of_mul hparts.1.2.ne')
  exact ⟨hx, hy, hsupp x hx' y hy' s hparts.2⟩

/-- The join sublattice generated by order dense sublattices of the two factors is order dense
in all continuous join functions. -/
private lemma orderDense_join {K L : Type u}
    [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [TopologicalSpace L] [CompactSpace L] [T2Space L]
    (D : VectorSublattice C(K, ℝ)) (E : VectorSublattice C(L, ℝ))
    (hD : D.IsOrderDense) (hE : E.IsOrderDense)
    (G : VectorSublattice C(Join K L, ℝ))
    (hDG : ∀ f ∈ D, interpolate K L f 0 ∈ G)
    (hEG : ∀ g ∈ E, interpolate K L 0 g ∈ G) : G.IsOrderDense := by
  intro h hh
  obtain ⟨U, V, a, b, ε, hU, hneU, hV, hneV, hab, hε, hbox⟩ :=
    exists_positive_join_box h hh
  obtain ⟨w, hwG, hw, hsupp⟩ :=
    exists_join_supported D E hD hE G hDG hEG hU hneU hV hneV hab
  have hscale : 0 < ε / (‖w‖ + 1) := div_pos hε (by positivity)
  refine ⟨(ε / (‖w‖ + 1)) • w, G.smul_mem _ hwG,
    lt_of_le_of_ne (fun q ↦ mul_nonneg hscale.le (hw.le q))
      (Ne.symm (smul_ne_zero hscale.ne' hw.ne')), ?_⟩
  intro q
  change ε / (‖w‖ + 1) * w q ≤ h q
  by_cases hq : 0 < w q
  · have hbound : ε / (‖w‖ + 1) * w q ≤ ε := calc
      _ ≤ ε / (‖w‖ + 1) * (‖w‖ + 1) :=
        mul_le_mul_of_nonneg_left ((w.apply_le_norm q).trans (le_add_of_nonneg_right zero_le_one))
          hscale.le
      _ = ε := div_mul_cancel₀ _ (by positivity)
    obtain ⟨⟨x, y, s⟩, rfl⟩ := Quotient.exists_rep q
    exact hbound.trans (hbox x (hsupp x y s hq).1 y (hsupp x y s hq).2.1 s
      (hsupp x y s hq).2.2).le
  · simpa only [le_antisymm (le_of_not_gt hq) (hw.le q), mul_zero] using
      (show 0 ≤ h q from hh.le q)

/-- A sublattice containing order dense sublattices of both continuous-function
factors is order dense in their Banach lattice free product. -/
theorem orderDense_of_continuousFunctions (K : Bool → Type u)
    [∀ i, TopologicalSpace (K i)] [∀ i, CompactSpace (K i)]
    [∀ i, T2Space (K i)] [∀ i, Nonempty (K i)]
    (P : FreeProduct (fun i ↦ C(K i, ℝ)))
    (D : ∀ i, VectorSublattice C(K i, ℝ)) (hD : ∀ i, (D i).IsOrderDense)
    (G : VectorSublattice P.Carrier)
    (hG : ∀ i f, f ∈ D i → P.inclusion i f ∈ G) : G.IsOrderDense := by
  obtain ⟨e, hleft, hright, _⟩ := exists_join_equiv K P
  let H : VectorSublattice C(Join (K false) (K true), ℝ) :=
    { G.toSubmodule.comap e.symm.toLinearMap with
      sup_mem' := fun hf hg ↦ by
        change e.symm.toVecLatHom (_ ⊔ _) ∈ G
        rw [map_sup]
        exact G.sup_mem hf hg }
  have hH : H.IsOrderDense := orderDense_join (D false) (D true) (hD false) (hD true) H
    (fun f hf ↦ by
      change e.symm (interpolate (K false) (K true) f 0) ∈ G
      rw [← hleft]
      change e.toLinearEquiv.symm (e.toLinearEquiv (P.inclusion false f)) ∈ G
      simpa only [LinearEquiv.symm_apply_apply] using hG false f hf)
    (fun g hg ↦ by
      change e.symm (interpolate (K false) (K true) 0 g) ∈ G
      rw [← hright]
      change e.toLinearEquiv.symm (e.toLinearEquiv (P.inclusion true g)) ∈ G
      simpa only [LinearEquiv.symm_apply_apply] using hG true g hg)
  intro z hz
  have hez : 0 < e z := by
    change 0 < e.toVecLatHom z
    simpa only [map_zero] using
      (e.toVecLatHom.monotone.strictMono_of_injective e.toLinearEquiv.injective hz)
  obtain ⟨f, hfH, hf, hfz⟩ := hH hez
  refine ⟨e.symm f, hfH, ?_, ?_⟩
  · change 0 < e.symm.toVecLatHom f
    simpa only [map_zero] using
      (e.symm.toVecLatHom.monotone.strictMono_of_injective e.symm.toLinearEquiv.injective hf)
  · exact (e.symm.toVecLatHom.monotone hfz).trans_eq (e.toLinearEquiv.symm_apply_apply z)

/-- A family of continuous functions with infimum zero takes arbitrarily small values
somewhere in each nonempty open set. -/
private lemma exists_small_of_isGLB_zero {K : Type u} {ι : Type v}
    [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (f : ι → C(K, ℝ)) (hzero : IsGLB (Set.range f) 0)
    {U : Set K} (hU : IsOpen U) (hne : U.Nonempty) {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ U, ∃ i, f i x < ε := by
  classical
  by_contra! h
  obtain ⟨x, hx⟩ := hne
  obtain ⟨g, hg0, hg1, hg⟩ := exists_continuous_zero_one_of_isClosed hU.isClosed_compl
    (isClosed_singleton : IsClosed ({x} : Set K))
    (Set.disjoint_singleton_right.mpr (not_not.mpr hx))
  have hle : ε • g ≤ (0 : C(K, ℝ)) := hzero.2 (by
    rintro _ ⟨i, rfl⟩ y
    exact if hy : y ∈ U then
      (mul_le_of_le_one_right hε.le (hg y).2).trans (h y hy i)
    else by
      change ε * g y ≤ f i y
      simpa only [hg0 hy, Pi.zero_apply, mul_zero] using
        (show 0 ≤ f i y from hzero.1 ⟨i, rfl⟩ y))
  exact hε.not_ge (by
    simpa only [hg1 (Set.mem_singleton x), Pi.one_apply, mul_one] using
      (show ε * g x ≤ 0 from hle x))

/-- No nonzero positive join function can lie below every left-factor interpolation of a
family with infimum zero. -/
private lemma not_pos_of_le_left_interpolate {K L : Type u} {ι : Type v}
    [TopologicalSpace K] [CompactSpace K] [T2Space K] [TopologicalSpace L]
    (f : ι → C(K, ℝ)) (hzero : IsGLB (Set.range f) 0)
    (g : C(Join K L, ℝ)) (hbound : ∀ i, g ≤ interpolate K L (f i) 0) : ¬ 0 < g := by
  intro hg
  obtain ⟨U, V, a, b, ε, hU, hneU, _, ⟨y, hy⟩, hab, hε, hbox⟩ :=
    exists_positive_join_box g hg
  obtain ⟨x, hx, i, hi⟩ := exists_small_of_isGLB_zero f hzero hU hneU hε
  obtain ⟨t, hat, htb⟩ := exists_between hab
  have hle : g (joinMk K L x y t) ≤ (1 - (t : ℝ)) * f i x := by
    simpa only [interpolate_joinMk, ContinuousMap.zero_apply, mul_zero, add_zero] using
      (show g (joinMk K L x y t) ≤ interpolate K L (f i) 0 (joinMk K L x y t) from
        hbound i (joinMk K L x y t))
  exact (hbox x hx y hy t ⟨hat, htb⟩).not_ge
    ((hle.trans (mul_le_of_le_one_left (hzero.1 ⟨i, rfl⟩ x)
      (sub_le_self 1 t.property.1))).trans hi.le)

/-- No nonzero positive join function can lie below every right-factor interpolation of a
family with infimum zero. -/
private lemma not_pos_of_le_right_interpolate {K L : Type u} {ι : Type v}
    [TopologicalSpace K] [TopologicalSpace L] [CompactSpace L] [T2Space L]
    (f : ι → C(L, ℝ)) (hzero : IsGLB (Set.range f) 0)
    (g : C(Join K L, ℝ)) (hbound : ∀ i, g ≤ interpolate K L 0 (f i)) : ¬ 0 < g := by
  intro hg
  obtain ⟨U, V, a, b, ε, _, ⟨x, hx⟩, hV, hneV, hab, hε, hbox⟩ :=
    exists_positive_join_box g hg
  obtain ⟨y, hy, i, hi⟩ := exists_small_of_isGLB_zero f hzero hV hneV hε
  obtain ⟨t, hat, htb⟩ := exists_between hab
  have hle : g (joinMk K L x y t) ≤ (t : ℝ) * f i y := by
    simpa only [interpolate_joinMk, ContinuousMap.zero_apply, mul_zero, zero_add] using
      (show g (joinMk K L x y t) ≤ interpolate K L 0 (f i) (joinMk K L x y t) from
        hbound i (joinMk K L x y t))
  exact (hbox x hx y hy t ⟨hat, htb⟩).not_ge
    ((hle.trans (mul_le_of_le_one_left (hzero.1 ⟨i, rfl⟩ y) t.property.2)).trans hi.le)

/-- The inclusions of continuous-function factors preserve infima equal to zero. -/
theorem inclusion_regular_of_continuousFunctions (K : Bool → Type u)
    [∀ i, TopologicalSpace (K i)] [∀ i, CompactSpace (K i)]
    [∀ i, T2Space (K i)] [∀ i, Nonempty (K i)]
    (P : FreeProduct (fun i ↦ C(K i, ℝ))) (b : Bool) {ι : Type v}
    (f : ι → C(K b, ℝ)) (hzero : IsGLB (Set.range f) 0) :
    IsGLB (Set.range (fun i ↦ P.inclusion b (f i))) 0 := by
  obtain ⟨e, hleft, hright, _⟩ := exists_join_equiv K P
  have hnonneg : ∀ i, 0 ≤ P.inclusion b (f i) := fun i ↦
    ((P.inclusion_isVecLatHom b).mk' (P.inclusion b)).map_nonneg (hzero.1 ⟨i, rfl⟩)
  refine ⟨fun _ ⟨i, hi⟩ ↦ hi ▸ hnonneg i, fun z hz ↦ ?_⟩
  by_contra h
  have hpos : 0 < e (z ⊔ 0) := by
    change 0 < e.toVecLatHom (z ⊔ 0)
    simpa only [map_zero] using
      (e.toVecLatHom.monotone.strictMono_of_injective e.toLinearEquiv.injective
        (lt_of_le_of_ne le_sup_right (fun heq ↦ h (le_sup_left.trans_eq heq.symm))))
  have hbound : ∀ i, e (z ⊔ 0) ≤ e (P.inclusion b (f i)) := fun i ↦
    e.toVecLatHom.monotone (sup_le (hz ⟨i, rfl⟩) (hnonneg i))
  cases b with
  | false =>
    exact not_pos_of_le_left_interpolate f hzero (e (z ⊔ 0))
      (fun i ↦ (hbound i).trans_eq (hleft (f i))) hpos
  | true =>
    exact not_pos_of_le_right_interpolate f hzero (e (z ⊔ 0))
      (fun i ↦ (hbound i).trans_eq (hright (f i))) hpos

end ContinuousFunctionOrderProperties

end BanachLattice.FreeProduct
