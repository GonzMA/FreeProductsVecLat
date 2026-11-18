/-
Authors: Gonzalo Martínez-Fernández
-/

import FreeProducts.Consequences.PrincipalLocalization
import FreeProducts.Consequences.ContinuousFunctionOrder

/-!
# Order density and regularity for binary free products

Localization in principal ideals transfers the continuous-function order results to
arbitrary pairs of Banach lattices. Sublattices containing order dense sublattices of
both factors are order dense in the free product, and canonical factor inclusions
preserve infima equal to zero.
-/

universe u v

namespace BanachLattice.FreeProduct

section PrincipalIdeals

open scoped Pointwise Topology

attribute [local instance] OrderIdeal.principalNormedAddCommGroup
  OrderIdeal.principalNormedVectorLattice

variable (X : Bool → Type u)
  [∀ b, NormedAddCommGroup (X b)] [∀ b, Lattice (X b)]
  [∀ b, IsOrderedAddMonoid (X b)] [∀ b, BanachLattice (X b)]

/-- A lattice equivalence transports an order dense sublattice to an order dense subset of its
target. -/
private lemma orderDense_preimage_equiv {E F : Type u}
    [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E] [VectorLattice E]
    [AddCommGroup F] [Lattice F] [IsOrderedAddMonoid F] [VectorLattice F]
    (e : VecLatEquiv E F) (D : VectorSublattice E) (hD : D.IsOrderDense) :
    IsOrderDense {y : F | e.symm y ∈ D} := by
  intro f hf
  have hpos : 0 < e.symm.toVecLatHom f := (map_zero e.symm.toVecLatHom) ▸
    (e.symm.toVecLatHom.monotone.strictMono_of_injective
      e.symm.toLinearEquiv.injective hf)
  obtain ⟨x, hx, hxpos, hxf⟩ := hD hpos
  exact ⟨e x, (show e.toLinearEquiv.symm (e.toLinearEquiv x) ∈ D from
      (e.toLinearEquiv.symm_apply_apply x).symm ▸ hx),
    (map_zero e.toVecLatHom) ▸
      e.toVecLatHom.monotone.strictMono_of_injective e.toLinearEquiv.injective hxpos,
    (e.toVecLatHom.monotone hxf).trans_eq (e.toLinearEquiv.apply_symm_apply f)⟩

/-- The order-density result for continuous-function factors transfers through isometric
Banach lattice equivalences of the factors. -/
private lemma orderDense_of_factor_equiv
    (K : Bool → Type u) [∀ b, TopologicalSpace (K b)] [∀ b, CompactSpace (K b)]
    [∀ b, T2Space (K b)] [∀ b, Nonempty (K b)]
    (e : ∀ b, BanachLatEquiv (X b) C(K b, ℝ)) (P : FreeProduct X)
    (D : ∀ b, VectorSublattice (X b)) (hD : ∀ b, (D b).IsOrderDense)
    (G : VectorSublattice P.Carrier)
    (hG : ∀ b x, x ∈ D b → P.inclusion b x ∈ G) : G.IsOrderDense := by
  let D' (b : Bool) : VectorSublattice C(K b, ℝ) :=
    { (D b).toSubmodule.comap (e b).symm.toVecLatEquiv.toLinearMap with
      sup_mem' := fun {f g} hf hg ↦
        (congrArg (fun x : X b ↦ x ∈ D b)
          ((e b).symm.toVecLatEquiv.map_sup' f g)).mpr ((D b).sup_mem hf hg) }
  exact orderDense_of_continuousFunctions K (freeProductOfFactorEquiv P e) D'
    (fun b ↦ orderDense_preimage_equiv (e b).toVecLatEquiv (D b) (hD b)) G
    (fun b f hf ↦ hG b ((e b).symm f) hf)

/-- The free product of principal ideals retains order density from the intersections with the
given order dense factor sublattices. -/
private lemma principal_orderDense
    (u : ∀ b, X b) (hu : ∀ b, 0 < u b)
    (D : ∀ b, VectorSublattice (X b)) (hD : ∀ b, (D b).IsOrderDense) :
    letI : ∀ b, BanachLattice ↥(OrderIdeal.principalSubmodule (u b)) :=
      fun b ↦
        { toNormedVectorLattice := OrderIdeal.principalNormedVectorLattice (u b)
          toCompleteSpace := principal_completeSpace (u b) (hu b).le }
    ∀ (Q : FreeProduct (fun b ↦ ↥(OrderIdeal.principalSubmodule (u b))))
      (G : VectorSublattice Q.Carrier),
      (∀ b (x : ↥(OrderIdeal.principalSubmodule (u b))),
        (x : X b) ∈ D b → Q.inclusion b x ∈ G) → G.IsOrderDense := by
  let : ∀ b, BanachLattice ↥(OrderIdeal.principalSubmodule (u b)) :=
    fun b ↦
      { toNormedVectorLattice := OrderIdeal.principalNormedVectorLattice (u b)
        toCompleteSpace := principal_completeSpace (u b) (hu b).le }
  intro Q G hG
  let D' (b : Bool) : VectorSublattice ↥(OrderIdeal.principalSubmodule (u b)) :=
    { (D b).toSubmodule.comap (OrderIdeal.principalSubmodule (u b)).subtype with
      sup_mem' := fun hf hg ↦ (D b).sup_mem hf hg }
  have hD' (b : Bool) : (D' b).IsOrderDense := by
    intro x hx
    obtain ⟨y, hyD, hy, hyx⟩ := hD b (show 0 < (x : X b) from hx)
    exact ⟨⟨y, (OrderIdeal.principal (u b)).solid x.property hy.le hyx⟩, hyD, hy, hyx⟩
  let : ∀ b, Nontrivial ↥(OrderIdeal.principalSubmodule (u b)) := fun b ↦
    ⟨⟨0, ⟨u b, OrderIdeal.self_mem_principal (u b)⟩,
      fun h ↦ (ne_of_gt (hu b)) (congrArg Subtype.val h).symm⟩⟩
  let : ∀ b, AMSpaceWithUnit ↥(OrderIdeal.principalSubmodule (u b)) := fun b ↦
    OrderIdeal.principalAMSpaceWithUnit (hu b).le (principal_completeSpace (u b) (hu b).le)
  let K (b : Bool) := AMSpaceWithUnit.LatticeCharacter ↥(OrderIdeal.principalSubmodule (u b))
  have : ∀ b, Nonempty (K b) := fun b ↦
    let ⟨φ, _⟩ := AMSpaceWithUnit.LatticeCharacter.exists_abs_apply_eq_norm
      (X := ↥(OrderIdeal.principalSubmodule (u b))) 0
    ⟨φ⟩
  exact orderDense_of_factor_equiv (fun b ↦ ↥(OrderIdeal.principalSubmodule (u b))) K
    (fun b ↦ AMSpaceWithUnit.kakutaniEquiv ↥(OrderIdeal.principalSubmodule (u b)))
    Q D' hD' G hG

/-- For two nonzero Banach factors, a sublattice containing the included order dense factor
sublattices is order dense in the free product. -/
private lemma orderDense_binary_nontrivial [∀ b, Nontrivial (X b)] (P : FreeProduct X)
    (D : ∀ b, VectorSublattice (X b)) (hD : ∀ b, (D b).IsOrderDense)
    (G : VectorSublattice P.Carrier)
    (hG : ∀ b x, x ∈ D b → P.inclusion b x ∈ G) : G.IsOrderDense := by
  intro z hz
  obtain ⟨u, hu, Q, S, hS, hSinj, hcomm, w, rfl⟩ :=
    exists_mem_range_principal_freeProduct_nontrivial X P z
  let : ∀ b, BanachLattice ↥(OrderIdeal.principalSubmodule (u b)) :=
    fun b ↦
      { toNormedVectorLattice := OrderIdeal.principalNormedVectorLattice (u b)
        toCompleteSpace := principal_completeSpace (u b) (hu b).le }
  let H : VectorSublattice Q.Carrier :=
    { G.toSubmodule.comap S.toLinearMap with
      sup_mem' := fun {x y} hx hy ↦
        (congrArg (fun z : P.Carrier ↦ z ∈ G) (hS.map_sup' x y)).mpr (G.sup_mem hx hy) }
  have hH : H.IsOrderDense := principal_orderDense X u hu D hD Q H
    (fun b x hx ↦ (congrArg (fun z : P.Carrier ↦ z ∈ G) (hcomm b x)).mpr (hG b x hx))
  have hw : 0 < w := lt_of_le_not_ge
    ((hS.mk' S).le_of_map_le hSinj ((map_zero S).trans_le hz.le))
    (fun hw0 ↦ hz.not_ge (((hS.mk' S).monotone hw0).trans_eq (map_zero S)))
  obtain ⟨y, hyH, hy, hyw⟩ := hH hw
  exact ⟨S y, hyH, (map_zero (hS.mk' S)) ▸
    (hS.mk' S).monotone.strictMono_of_injective hSinj hy, (hS.mk' S).monotone hyw⟩

/-- Order density in the binary free product follows directly when one factor inclusion is
surjective. -/
private lemma orderDense_binary_of_surjective (P : FreeProduct X) (b : Bool)
    (hsurj : Function.Surjective (P.inclusion b))
    (D : ∀ b, VectorSublattice (X b)) (hD : ∀ b, (D b).IsOrderDense)
    (G : VectorSublattice P.Carrier)
    (hG : ∀ b x, x ∈ D b → P.inclusion b x ∈ G) : G.IsOrderDense := by
  intro z hz
  obtain ⟨x, rfl⟩ := hsurj z
  let T := (P.inclusion_isVecLatHom b).mk' (P.inclusion b)
  have hx : 0 < x := lt_of_le_not_ge
    (T.le_of_map_le (P.isometry_inclusion b).injective ((map_zero T).trans_le hz.le))
    (fun hx0 ↦ hz.not_ge ((T.monotone hx0).trans_eq (map_zero T)))
  obtain ⟨y, hyD, hy, hyx⟩ := hD b hx
  exact ⟨T y, hG b y hyD, (map_zero T) ▸
    T.monotone.strictMono_of_injective (P.isometry_inclusion b).injective hy,
    T.monotone hyx⟩

/-- A sublattice containing order dense sublattices of both factors is order dense
in their Banach lattice free product. -/
theorem orderDense_of_binary (P : FreeProduct X)
    (D : ∀ b, VectorSublattice (X b)) (hD : ∀ b, (D b).IsOrderDense)
    (G : VectorSublattice P.Carrier)
    (hG : ∀ b x, x ∈ D b → P.inclusion b x ∈ G) : G.IsOrderDense := by
  rcases subsingleton_or_nontrivial (X false) with hfalse | hfalse
  · exact orderDense_binary_of_surjective X P true
      (inclusion_surjective_of_subsingleton X P true
        (fun c ↦ Bool.rec (motive := fun c ↦ c ≠ true → Subsingleton (X c))
          (fun _ ↦ hfalse) (fun h ↦ (h rfl).elim) c)) D hD G hG
  · rcases subsingleton_or_nontrivial (X true) with htrue | htrue
    · exact orderDense_binary_of_surjective X P false
        (inclusion_surjective_of_subsingleton X P false
          (fun c ↦ Bool.rec (motive := fun c ↦ c ≠ false → Subsingleton (X c))
            (fun h ↦ (h rfl).elim) (fun _ ↦ htrue) c)) D hD G hG
    · let : ∀ b, Nontrivial (X b) := Bool.rec hfalse htrue
      exact orderDense_binary_nontrivial X P D hD G hG

/-- The regularity of continuous-function factor inclusions transfers through isometric
equivalences of the factors. -/
private lemma inclusion_regular_of_factor_equiv
    (K : Bool → Type u) [∀ b, TopologicalSpace (K b)] [∀ b, CompactSpace (K b)]
    [∀ b, T2Space (K b)] [∀ b, Nonempty (K b)]
    (e : ∀ b, BanachLatEquiv (X b) C(K b, ℝ)) (P : FreeProduct X)
    (b : Bool) {ι : Type v} (f : ι → X b) (hzero : IsGLB (Set.range f) 0) :
    IsGLB (Set.range (fun i ↦ P.inclusion b (f i))) 0 := by
  let o : X b ≃o C(K b, ℝ) :=
    { (e b).toVecLatEquiv.toLinearEquiv.toEquiv with
      map_rel_iff' := fun {x y} ↦
        ⟨(e b).toVecLatEquiv.toVecLatHom.le_of_map_le (e b).toLinearIsometryEquiv.injective,
          fun h ↦ (e b).toVecLatEquiv.toVecLatHom.monotone h⟩ }
  have ho0 : o 0 = 0 := (e b).toVecLatEquiv.toLinearEquiv.map_zero
  have hf : IsGLB (Set.range (fun i ↦ o (f i))) 0 := by
    simpa only [← Set.range_comp', ho0] using o.isGLB_image'.mpr hzero
  have hreg := inclusion_regular_of_continuousFunctions K (freeProductOfFactorEquiv P e)
    b (fun i ↦ o (f i)) hf
  have hfun : (fun i ↦ (freeProductOfFactorEquiv P e).inclusion b (o (f i))) =
      (fun i ↦ P.inclusion b (f i)) := funext (fun i ↦ congrArg (P.inclusion b)
        ((e b).toLinearIsometryEquiv.symm_apply_apply (f i)))
  exact hfun ▸ hreg

/-- Canonical factor inclusions in the free product of principal ideals preserve infimum zero. -/
private lemma principal_inclusion_regular (u : ∀ b, X b) (hu : ∀ b, 0 < u b) :
    letI : ∀ b, BanachLattice ↥(OrderIdeal.principalSubmodule (u b)) :=
      fun b ↦
        { toNormedVectorLattice := OrderIdeal.principalNormedVectorLattice (u b)
          toCompleteSpace := principal_completeSpace (u b) (hu b).le }
    ∀ (Q : FreeProduct (fun b ↦ ↥(OrderIdeal.principalSubmodule (u b)))) (b : Bool)
      {ι : Type v} (f : ι → ↥(OrderIdeal.principalSubmodule (u b))),
      IsGLB (Set.range f) 0 → IsGLB (Set.range (fun i ↦ Q.inclusion b (f i))) 0 := by
  let : ∀ b, BanachLattice ↥(OrderIdeal.principalSubmodule (u b)) :=
    fun b ↦
      { toNormedVectorLattice := OrderIdeal.principalNormedVectorLattice (u b)
        toCompleteSpace := principal_completeSpace (u b) (hu b).le }
  intro Q b ι f hzero
  let : ∀ c, Nontrivial ↥(OrderIdeal.principalSubmodule (u c)) := fun c ↦
    ⟨⟨0, ⟨u c, OrderIdeal.self_mem_principal (u c)⟩,
      fun h ↦ (ne_of_gt (hu c)) (congrArg Subtype.val h).symm⟩⟩
  let : ∀ c, AMSpaceWithUnit ↥(OrderIdeal.principalSubmodule (u c)) := fun c ↦
    OrderIdeal.principalAMSpaceWithUnit (hu c).le (principal_completeSpace (u c) (hu c).le)
  let K (c : Bool) := AMSpaceWithUnit.LatticeCharacter ↥(OrderIdeal.principalSubmodule (u c))
  have : ∀ c, Nonempty (K c) := fun c ↦
    let ⟨φ, _⟩ := AMSpaceWithUnit.LatticeCharacter.exists_abs_apply_eq_norm
      (X := ↥(OrderIdeal.principalSubmodule (u c))) 0
    ⟨φ⟩
  exact inclusion_regular_of_factor_equiv (fun c ↦ ↥(OrderIdeal.principalSubmodule (u c))) K
    (fun c ↦ AMSpaceWithUnit.kakutaniEquiv ↥(OrderIdeal.principalSubmodule (u c)))
    Q b f hzero

/-- In a nonzero Banach lattice, every countable family is contained in a principal ideal with
a strictly positive generator. -/
private lemma exists_pos_principal_containing_countable
    {ι : Type*} [Countable ι] {Y : Type u} [NormedAddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] [BanachLattice Y] [Nontrivial Y] (x : ι → Y) :
    ∃ u : Y, 0 < u ∧ ∀ i, x i ∈ OrderIdeal.principal u := by
  obtain ⟨u, hu, hx, _⟩ := exists_principal_sequence_control x (fun _ ↦ (0 : Y))
    (fun _ ↦ le_rfl) (fun n ↦ (norm_zero : ‖(0 : Y)‖ = 0).le.trans
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (pow_nonneg (by norm_num) n)))
  exact ⟨u, hu, hx⟩

/-- A generated free-product element lifts to principal ideals that also contain prescribed
elements of the two factors. -/
private lemma exists_generated_principal_lift [∀ b, Nontrivial (X b)]
    (P : FreeProduct X) (z : P.generated) (a : ∀ b, X b) :
    ∃ (u : ∀ b, X b) (hu : ∀ b, 0 < u b),
      (∀ b, a b ∈ OrderIdeal.principal (u b)) ∧
      letI : ∀ b, BanachLattice ↥(OrderIdeal.principalSubmodule (u b)) :=
        fun b ↦
          { toNormedVectorLattice := OrderIdeal.principalNormedVectorLattice (u b)
            toCompleteSpace := principal_completeSpace (u b) (hu b).le }
      ∃ (Q : FreeProduct (fun b ↦ ↥(OrderIdeal.principalSubmodule (u b))))
        (S : Q.Carrier →L[ℝ] P.Carrier), IsVecLatHom S ∧ Function.Injective S ∧
        (∀ b (x : ↥(OrderIdeal.principalSubmodule (u b))),
          S (Q.inclusion b x) = P.inclusion b (x : X b)) ∧ (z : P.Carrier) ∈ Set.range S := by
  classical
  obtain ⟨n, i, x, φ, hφ⟩ := P.exists_expression z
  let y (b : Bool) : Option (Fin n) → X b
    | none => a b
    | some j => if h : i j = b then h ▸ x j else 0
  choose u hu hy using fun b ↦ exists_pos_principal_containing_countable (y b)
  let : ∀ b, BanachLattice ↥(OrderIdeal.principalSubmodule (u b)) :=
    fun b ↦
      { toNormedVectorLattice := OrderIdeal.principalNormedVectorLattice (u b)
        toCompleteSpace := principal_completeSpace (u b) (hu b).le }
  obtain ⟨Q, S, hS, hcomm⟩ := exists_principal_product_map X P u (fun b ↦ (hu b).le)
  let v (j : Fin n) : ↥(OrderIdeal.principalSubmodule (u (i j))) :=
    ⟨x j, show x j ∈ OrderIdeal.principal (u (i j)) from
      by simpa only [y, dite_eq_left rfl] using hy (i j) (some j)⟩
  refine ⟨u, hu, (fun b ↦ hy b none), Q, S, hS,
    principal_product_map_injective X P u hu Q S hS hcomm, hcomm,
    LLexpr.eval (fun j ↦ Q.inclusion (i j) (v j)) φ, ?_⟩
  change (hS.mk' S) (LLexpr.eval (fun j ↦ Q.inclusion (i j) (v j)) φ) = (z : P.Carrier)
  rw [LLexpr.map_eval]
  simpa only [IsVecLatHom.mk'_apply, hcomm, v] using hφ.symm

/-- A generated element bounded by every member of an included family with infimum zero must
be nonpositive. -/
private lemma generated_le_zero_of_le_inclusion_nontrivial [∀ b, Nontrivial (X b)]
    (P : FreeProduct X) (b : Bool) {ι : Type v} [Nonempty ι]
    (f : ι → X b) (hzero : IsGLB (Set.range f) 0) (z : P.generated)
    (hz : ∀ i, (z : P.Carrier) ≤ P.inclusion b (f i)) : (z : P.Carrier) ≤ 0 := by
  classical
  let i₀ : ι := Classical.arbitrary ι
  obtain ⟨u, hu, ha, Q, S, hS, hSinj, hcomm, w, hw⟩ :=
    exists_generated_principal_lift X P z (Pi.single b (f i₀))
  let : ∀ c, BanachLattice ↥(OrderIdeal.principalSubmodule (u c)) :=
    fun c ↦
      { toNormedVectorLattice := OrderIdeal.principalNormedVectorLattice (u c)
        toCompleteSpace := principal_completeSpace (u c) (hu c).le }
  have hmem : f i₀ ∈ OrderIdeal.principal (u b) := by
    simpa only [Pi.single_eq_same] using ha b
  let g (i : ι) : ↥(OrderIdeal.principalSubmodule (u b)) :=
    ⟨f i ⊓ f i₀, (OrderIdeal.principal (u b)).solid hmem
      (le_inf (hzero.1 ⟨i, rfl⟩) (hzero.1 ⟨i₀, rfl⟩)) inf_le_right⟩
  have hg : IsGLB (Set.range g) 0 := by
    refine ⟨?_, ?_⟩
    · exact Set.forall_mem_range.mpr (fun i ↦
        le_inf (hzero.1 ⟨i, rfl⟩) (hzero.1 ⟨i₀, rfl⟩))
    · exact fun q hq ↦ hzero.2 (Set.forall_mem_range.mpr (fun i ↦
        (show (q : X b) ≤ f i ⊓ f i₀ from hq ⟨i, rfl⟩).trans inf_le_left))
  have hreg := principal_inclusion_regular X u hu Q b g hg
  have hbound (i : ι) : w ≤ Q.inclusion b (g i) := by
    apply (hS.mk' S).le_of_map_le hSinj
    change S w ≤ S (Q.inclusion b (g i))
    exact (hw.trans_le ((le_inf (hz i) (hz i₀)).trans_eq
      ((P.inclusion_isVecLatHom b).map_inf' (f i) (f i₀)).symm)).trans_eq
        (hcomm b (g i)).symm
  exact hw.symm.trans_le (((hS.mk' S).monotone
    (hreg.2 (Set.forall_mem_range.mpr hbound))).trans_eq (map_zero S))

/-- Canonical inclusions in a binary free product of nonzero Banach lattices preserve infimum
zero. -/
private lemma inclusion_regular_binary_nontrivial [∀ b, Nontrivial (X b)]
    (P : FreeProduct X) (b : Bool) {ι : Type v} [Nonempty ι]
    (f : ι → X b) (hzero : IsGLB (Set.range f) 0) :
    IsGLB (Set.range (fun i ↦ P.inclusion b (f i))) 0 := by
  have hd : P.generated.IsOrderDense := orderDense_of_binary X P (fun _ ↦ ⊤)
    (fun _ ↦ IsOrderDense.univ) P.generated
    (fun c x _ ↦ VectorSublattice.subset_generated _ ⟨⟨c, x⟩, rfl⟩)
  have hnonneg (i : ι) : 0 ≤ P.inclusion b (f i) :=
    ((P.inclusion_isVecLatHom b).mk' (P.inclusion b)).map_nonneg (hzero.1 ⟨i, rfl⟩)
  refine ⟨Set.forall_mem_range.mpr hnonneg, fun z hz ↦ ?_⟩
  by_contra h
  obtain ⟨w, hwG, hw, hwz⟩ := hd (lt_of_le_of_ne le_sup_right
    (fun heq : (0 : P.Carrier) = z ⊔ 0 ↦ h (le_sup_left.trans_eq heq.symm)))
  exact hw.not_ge (generated_le_zero_of_le_inclusion_nontrivial X P b f hzero ⟨w, hwG⟩
    (fun i ↦ hwz.trans (sup_le (hz ⟨i, rfl⟩) (hnonneg i))))

/-- A surjective canonical factor inclusion preserves infimum zero. -/
private lemma inclusion_regular_of_surjective (P : FreeProduct X) (b : Bool)
    (hsurj : Function.Surjective (P.inclusion b)) {ι : Type v}
    (f : ι → X b) (hzero : IsGLB (Set.range f) 0) :
    IsGLB (Set.range (fun i ↦ P.inclusion b (f i))) 0 := by
  let T := (P.inclusion_isVecLatHom b).mk' (P.inclusion b)
  let o : X b ≃o P.Carrier := OrderIso.ofSurjective
    (OrderEmbedding.ofMapLEIff T (fun _ _ ↦
      ⟨T.le_of_map_le (P.isometry_inclusion b).injective, fun h ↦ T.monotone h⟩)) hsurj
  have h : IsGLB (Set.range (fun i ↦ P.inclusion b (f i))) (P.inclusion b 0) :=
    (Set.range_comp' (P.inclusion b) f).symm ▸ o.isGLB_image'.mpr hzero
  simpa only [map_zero] using h

/-- The inclusion of a zero factor preserves infimum zero for every nonempty family. -/
private lemma inclusion_regular_of_subsingleton (P : FreeProduct X) (b : Bool)
    [Subsingleton (X b)] {ι : Type v} [Nonempty ι] (f : ι → X b) :
    IsGLB (Set.range (fun i ↦ P.inclusion b (f i))) 0 := by
  simpa only [Subsingleton.elim (f _) 0, map_zero, Set.range_const] using
    (isGLB_singleton (a := (0 : P.Carrier)))

/-- Canonical inclusions in a binary Banach lattice free product preserve
infima equal to zero. -/
theorem inclusion_regular_of_binary (P : FreeProduct X) (b : Bool)
    {ι : Type v} [Nonempty ι] (f : ι → X b) (hzero : IsGLB (Set.range f) 0) :
    IsGLB (Set.range (fun i ↦ P.inclusion b (f i))) 0 := by
  rcases subsingleton_or_nontrivial (X false) with hfalse | hfalse
  · cases b with
    | false => exact inclusion_regular_of_subsingleton X P false f
    | true =>
      exact inclusion_regular_of_surjective X P true
        (inclusion_surjective_of_subsingleton X P true
          (fun c ↦ Bool.rec (motive := fun c ↦ c ≠ true → Subsingleton (X c))
            (fun _ ↦ hfalse) (fun h ↦ (h rfl).elim) c)) f hzero
  · rcases subsingleton_or_nontrivial (X true) with htrue | htrue
    · cases b with
      | true => exact inclusion_regular_of_subsingleton X P true f
      | false =>
        exact inclusion_regular_of_surjective X P false
          (inclusion_surjective_of_subsingleton X P false
            (fun c ↦ Bool.rec (motive := fun c ↦ c ≠ false → Subsingleton (X c))
              (fun h ↦ (h rfl).elim) (fun _ ↦ htrue) c)) f hzero
    · let : ∀ c, Nontrivial (X c) := Bool.rec hfalse htrue
      exact inclusion_regular_binary_nontrivial X P b f hzero

end PrincipalIdeals

end BanachLattice.FreeProduct
