/-
Authors: Gonzalo Martínez-Fernández
-/

import FreeProducts.Consequences.BinaryOrder

/-!
# Order properties and injectivity for families of factors

Grouping factors reduces order density for finite families to the binary case.
Order dense embeddings of finitely many factors induce regular embeddings of their
Archimedean free products into the Banach free product. For arbitrary families,
canonical inclusions are regular and uniformly bounded injective factor homomorphisms
induce injective maps of Banach free products.
-/

universe u v

namespace BanachLattice.FreeProduct

/-- Encodes two factors as a family indexed by the two Boolean values. -/
private def binaryFamily (X Y : Type u) (b : Bool) : Type u := Bool.rec X Y b

/-- Each member of the two-factor family inherits the normed additive group of its selected
factor. -/
private instance binaryNormedAddCommGroup {X Y : Type u}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] (b : Bool) :
    NormedAddCommGroup (binaryFamily X Y b) := by
  cases b <;> assumption

/-- Each member of the two-factor family inherits the lattice order of its selected factor. -/
private instance binaryLattice {X Y : Type u} [Lattice X] [Lattice Y] (b : Bool) :
    Lattice (binaryFamily X Y b) := by
  cases b <;> assumption

/-- Addition respects the inherited order in each member of the two-factor family. -/
private instance binaryIsOrderedAddMonoid {X Y : Type u}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [Lattice X] [Lattice Y]
    [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y] (b : Bool) :
    IsOrderedAddMonoid (binaryFamily X Y b) := by
  cases b <;> assumption

/-- Each member of the two-factor family inherits its Banach lattice structure. -/
private instance binaryBanachLattice {X Y : Type u}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [Lattice X] [Lattice Y]
    [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y] [BanachLattice X] [BanachLattice Y]
    (b : Bool) : BanachLattice (binaryFamily X Y b) := by
  cases b <;> assumption

variable {I : Type u} {E : I → Type u}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, Lattice (E i)]
  [∀ i, IsOrderedAddMonoid (E i)] [∀ i, BanachLattice (E i)]
  (P : FreeProduct E)

/-- The free product of all factors except one maps contractively into the full free product,
preserving each remaining inclusion. -/
private lemma exists_complement_map (i : I)
    (Q : FreeProduct (fun j : {j : I // j ≠ i} ↦ E j.val)) :
    ∃ U : Q.Carrier →L[ℝ] P.Carrier, IsVecLatHom U ∧ ‖U‖ ≤ 1 ∧
      ∀ j x, U (Q.inclusion j x) = P.inclusion j.val x := by
  obtain ⟨U, ⟨hU, hcomm, hnorm⟩, _⟩ := Q.exists_unique_extension P.Carrier
    (fun j ↦ P.inclusion j.val) (fun j ↦ P.inclusion_isVecLatHom j.val)
    1 zero_le_one (fun j ↦ P.inclusion_contractive j.val)
  exact ⟨U, hU, hnorm, hcomm⟩

/-- The two inclusions obtained by grouping one factor separately from the free product of the
other factors. -/
private def splitInclusion (i : I)
    (Q : FreeProduct (fun j : {j : I // j ≠ i} ↦ E j.val))
    (U : Q.Carrier →L[ℝ] P.Carrier) :
    ∀ b, binaryFamily (E i) Q.Carrier b →L[ℝ] P.Carrier
  | false => P.inclusion i
  | true => U

/-- Grouping one factor against all remaining factors preserves the bounded universal property
of the free product. -/
private lemma split_universal (i : I)
    (Q : FreeProduct (fun j : {j : I // j ≠ i} ↦ E j.val))
    (U : Q.Carrier →L[ℝ] P.Carrier) (hU : IsVecLatHom U)
    (hcomm : ∀ j x, U (Q.inclusion j x) = P.inclusion j.val x)
    (Y : Type u) [NormedAddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] [BanachLattice Y]
    (T : ∀ b, binaryFamily (E i) Q.Carrier b →L[ℝ] Y)
    (hT : ∀ b, IsVecLatHom (T b)) (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ b, ‖T b‖ ≤ M) :
    ∃! S : P.Carrier →L[ℝ] Y, IsVecLatHom S ∧
      (∀ b x, S (splitInclusion P i Q U b x) = T b x) ∧ ‖S‖ ≤ M := by
  classical
  let V (j : I) : E j →L[ℝ] Y :=
    if h : j = i then h ▸ T false else (T true).comp (Q.inclusion ⟨j, h⟩)
  have hV (j : I) : IsVecLatHom (V j) := by
    dsimp only [V]
    split_ifs with h
    · subst j
      exact hT false
    · exact (((hT true).mk' (T true)).comp
        ((Q.inclusion_isVecLatHom ⟨j, h⟩).mk' (Q.inclusion ⟨j, h⟩))).isVecLatHom
  have hVnorm (j : I) : ‖V j‖ ≤ M := by
    dsimp only [V]
    split_ifs with h
    · subst j
      exact hbound false
    · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        ((mul_le_mul (hbound true) (Q.inclusion_contractive ⟨j, h⟩)
          (norm_nonneg _) hM).trans_eq (mul_one M))
  obtain ⟨S, ⟨hS, hSV, hSnorm⟩, _⟩ := P.exists_unique_extension Y V hV M hM hVnorm
  have hSi (x : E i) : S (P.inclusion i x) = T false x := by
    exact (hSV i x).trans (by simp only [V, dite_eq_left rfl]; rfl)
  have hSc (j : {j : I // j ≠ i}) (x : E j.val) :
      S (P.inclusion j.val x) = T true (Q.inclusion j x) := by
    exact (hSV j.val x).trans (by simp only [V, dite_eq_right j.property]; rfl)
  have hSU : S.comp U = T true := Q.extension_ext
    ((hS.mk' S).comp (hU.mk' U)).isVecLatHom (hT true)
    (fun j x ↦ (congrArg S (hcomm j x)).trans (hSc j x))
  refine ⟨S, ⟨hS, ?_, hSnorm⟩, ?_⟩
  · exact fun b ↦ Bool.rec (motive := fun b ↦
      ∀ x, S (splitInclusion P i Q U b x) = T b x) hSi (DFunLike.congr_fun hSU) b
  · rintro R ⟨hR, hRT, _⟩
    apply P.extension_ext hR hS
    intro j x
    by_cases h : j = i
    · subst j
      exact (hRT false x).trans (hSi x).symm
    · exact (congrArg R (hcomm ⟨j, h⟩ x)).symm.trans
        ((hRT true (Q.inclusion ⟨j, h⟩ x)).trans (hSc ⟨j, h⟩ x).symm)

/-- Regards the full free product as a binary free product of one factor and the complementary
free product. -/
private def splitFreeProduct (i : I)
    (Q : FreeProduct (fun j : {j : I // j ≠ i} ↦ E j.val))
    (U : Q.Carrier →L[ℝ] P.Carrier) (hU : IsVecLatHom U) (hnorm : ‖U‖ ≤ 1)
    (hcomm : ∀ j x, U (Q.inclusion j x) = P.inclusion j.val x) :
    FreeProduct (binaryFamily (E i) Q.Carrier) where
  Carrier := P.Carrier
  inclusion := splitInclusion P i Q U
  inclusion_isVecLatHom := fun b ↦ Bool.rec
    (motive := fun b ↦ IsVecLatHom (splitInclusion P i Q U b))
    (P.inclusion_isVecLatHom i) hU b
  inclusion_contractive := fun b ↦ Bool.rec
    (motive := fun b ↦ ‖splitInclusion P i Q U b‖ ≤ 1) (P.inclusion_contractive i) hnorm b
  universal := fun Y _ _ _ _ T hT M hM hbound ↦
    split_universal P i Q U hU hcomm Y T hT M hM hbound

/-- Order density for the complementary free product yields order density after adjoining the
remaining factor. -/
private lemma orderDense_of_complement (i : I)
    (Q : FreeProduct (fun j : {j : I // j ≠ i} ↦ E j.val))
    (D : ∀ j, VectorSublattice (E j)) (hD : ∀ j, (D j).IsOrderDense)
    (G : VectorSublattice P.Carrier)
    (hG : ∀ j x, x ∈ D j → P.inclusion j x ∈ G)
    (hQ : ∀ H : VectorSublattice Q.Carrier,
      (∀ (j : {j : I // j ≠ i}) (x : E j.val),
        x ∈ D j.val → Q.inclusion j x ∈ H) → H.IsOrderDense) : G.IsOrderDense := by
  obtain ⟨U, hU, hnorm, hcomm⟩ := exists_complement_map P i Q
  let H : VectorSublattice Q.Carrier :=
    { G.toSubmodule.comap U.toLinearMap with
      sup_mem' := fun {x y} hx hy ↦
        (congrArg (fun z : P.Carrier ↦ z ∈ G) (hU.map_sup' x y)).mpr (G.sup_mem hx hy) }
  have hH : H.IsOrderDense := hQ H (fun j x hx ↦
    (congrArg (fun z : P.Carrier ↦ z ∈ G) (hcomm j x)).mpr (hG j.val x hx))
  let D' : ∀ b, VectorSublattice (binaryFamily (E i) Q.Carrier b) :=
    fun b ↦ Bool.rec (motive := fun b ↦ VectorSublattice (binaryFamily (E i) Q.Carrier b))
      (D i) H b
  apply orderDense_of_binary _ (splitFreeProduct P i Q U hU hnorm hcomm) D'
    (fun b ↦ Bool.rec (motive := fun b ↦ (D' b).IsOrderDense) (hD i) hH b) G
  exact fun b ↦ Bool.rec (motive := fun b ↦ ∀ x, x ∈ D' b →
    (splitFreeProduct P i Q U hU hnorm hcomm).inclusion b x ∈ G)
      (hG i) (fun _ hx ↦ hx) b

/-- For a finite family, any sublattice containing the images of order dense factor
sublattices is order dense in the free product. -/
private lemma orderDense_of_finite [Finite I]
    (D : ∀ i, VectorSublattice (E i)) (hD : ∀ i, (D i).IsOrderDense)
    (G : VectorSublattice P.Carrier)
    (hG : ∀ i x, x ∈ D i → P.inclusion i x ∈ G) : G.IsOrderDense := by
  classical
  induction hn : Nat.card I using Nat.strong_induction_on generalizing I with
  | h n ih =>
    cases isEmpty_or_nonempty I with
    | inl h =>
      let := h
      have hid : (ContinuousLinearMap.id ℝ P.Carrier) = 0 := P.extension_ext
        (VecLatHom.id : VecLatHom P.Carrier P.Carrier).isVecLatHom
        (VecLatHom.ofAbs 0 (by simp) : VecLatHom P.Carrier P.Carrier).isVecLatHom
        (fun i ↦ isEmptyElim i)
      exact fun z hz ↦ (hz.ne' (DFunLike.congr_fun hid z)).elim
    | inr h =>
      let := h
      let i : I := Classical.arbitrary I
      obtain ⟨Q⟩ := nonempty_freeProduct (fun j : {j : I // j ≠ i} ↦ E j.val)
      apply orderDense_of_complement P i Q D hD G hG
      intro H hH
      let := Fintype.ofFinite I
      refine ih _ ?_ Q (fun j ↦ D j.val) (fun j ↦ hD j.val) H hH rfl
      rw [← hn, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      exact Fintype.card_subtype_lt (fun h ↦ h rfl)

section OrderDenseFactors

variable [Finite I] {F : I → Type u}
  [∀ i, AddCommGroup (F i)] [∀ i, Lattice (F i)]
  [∀ i, IsOrderedAddMonoid (F i)] [∀ i, VectorLattice (F i)]
  [∀ i, IsVLArchimedean (F i)]
  (A : VectorLattice.ArchimedeanFreeProduct F)
  (T : ∀ i, VecLatHom (F i) (E i))
  (hT : ∀ i, Function.Injective (T i))
  (hdense : ∀ i, IsOrderDense (Set.range (T i)))
  (S : VecLatHom A.Carrier P.Carrier)
  (hS : ∀ i x, S (A.inclusion i x) = P.inclusion i (T i x))

include hT hdense hS

omit [Finite I] hdense in
/-- The map from the Archimedean free product induced by embeddings of the factors is
injective in the Banach lattice free product. -/
private lemma archimedean_induced_injective : Function.Injective S := by
  obtain ⟨B⟩ := VectorLattice.nonempty_archimedeanFreeProduct E
  obtain ⟨U, hU, _⟩ := A.universal B.Carrier (fun i ↦ (B.inclusion i).comp (T i))
  obtain ⟨e, he⟩ := B.exists_generated_equiv P
  let V := P.generated.subtype.comp e.toVecLatHom
  have hcomm : S = V.comp U := by
    obtain ⟨_, _, hu⟩ := A.universal P.Carrier
      (fun i ↦ ((P.inclusion_isVecLatHom i).mk' (P.inclusion i)).comp (T i))
    refine (hu S hS).trans (hu (V.comp U) ?_).symm
    intro i x
    change (e (U (A.inclusion i x)) : P.Carrier) = P.inclusion i (T i x)
    rw [hU]
    exact he i (T i x)
  rw [hcomm]
  exact (Subtype.val_injective.comp e.toLinearEquiv.injective).comp
    (A.induced_injective B T hT U hU)

/-- For finitely many order dense embedded factors, the induced map from
their Archimedean free product is injective and has order dense range. -/
theorem archimedean_induced_orderDense :
    Function.Injective S ∧ IsOrderDense (Set.range S) := by
  refine ⟨archimedean_induced_injective P A T hT S hS, ?_⟩
  let D (i : I) : VectorSublattice (E i) :=
    { (T i).toLinearMap.range with
      sup_mem' := fun ⟨x, hx⟩ ⟨y, hy⟩ ↦
        ⟨x ⊔ y, ((T i).map_sup' x y).trans (congrArg₂ (· ⊔ ·) hx hy)⟩ }
  let G : VectorSublattice P.Carrier :=
    { S.toLinearMap.range with
      sup_mem' := fun ⟨x, hx⟩ ⟨y, hy⟩ ↦
        ⟨x ⊔ y, (S.map_sup' x y).trans (congrArg₂ (· ⊔ ·) hx hy)⟩ }
  exact orderDense_of_finite P D hdense G (fun i x ⟨y, hy⟩ ↦
    ⟨A.inclusion i y, (hS i y).trans (congrArg (P.inclusion i) hy)⟩)

/-- The Archimedean free product of finitely many order dense embedded
factors is regular in the Banach lattice free product. -/
theorem archimedean_induced_regular
    {ι : Type v} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {f : ι → A.Carrier} (_hf : Antitone f)
    (hzero : IsGLB (Set.range f) 0) :
    IsGLB (Set.range (fun a ↦ S (f a))) 0 := by
  obtain ⟨hinj, hd⟩ := archimedean_induced_orderDense P A T hT hdense S hS
  refine ⟨?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact S.map_nonneg (hzero.1 ⟨i, rfl⟩)
  · intro y hy
    by_contra hle
    have hypos : 0 < y ⊔ 0 := lt_of_le_of_ne le_sup_right
      (fun heq ↦ hle (le_sup_left.trans_eq heq.symm))
    obtain ⟨_, ⟨z, rfl⟩, hz, hzy⟩ := hd hypos
    have hz0 : z ≤ 0 := hzero.2 (by
      rintro _ ⟨i, rfl⟩
      exact S.le_of_map_le hinj (hzy.trans
        (sup_le (hy ⟨i, rfl⟩) (S.map_nonneg (hzero.1 ⟨i, rfl⟩)))))
    exact hz.not_ge ((S.monotone hz0).trans_eq (map_zero S))

end OrderDenseFactors

/-- Every canonical factor is regular in the Banach lattice free product:
decreasing nets with infimum zero retain infimum zero under inclusion. -/
theorem inclusion_regular (i : I)
    {ι : Type v} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {f : ι → E i} (_hf : Antitone f)
    (hzero : IsGLB (Set.range f) 0) :
    IsGLB (Set.range (fun a ↦ P.inclusion i (f a))) 0 := by
  obtain ⟨Q⟩ := nonempty_freeProduct (fun j : {j : I // j ≠ i} ↦ E j.val)
  obtain ⟨U, hU, hnorm, hcomm⟩ := exists_complement_map P i Q
  exact inclusion_regular_of_binary _ (splitFreeProduct P i Q U hU hnorm hcomm) false f hzero

section Injectivity

variable {F : I → Type u}
  [∀ i, NormedAddCommGroup (F i)] [∀ i, Lattice (F i)]
  [∀ i, IsOrderedAddMonoid (F i)] [∀ i, BanachLattice (F i)]

/-- For finitely many factors, injective lattice homomorphisms induce an injective map of
Banach lattice free products. -/
private lemma induced_injective_finite [Finite I] (Q : FreeProduct F)
    (T : ∀ i, E i →L[ℝ] F i) (hT : ∀ i, IsVecLatHom (T i))
    (hinj : ∀ i, Function.Injective (T i))
    (S : P.Carrier →L[ℝ] Q.Carrier) (hS : IsVecLatHom S)
    (hcomm : ∀ i x, S (P.inclusion i x) = Q.inclusion i (T i x)) :
    Function.Injective S := by
  obtain ⟨A⟩ := VectorLattice.nonempty_archimedeanFreeProduct E
  obtain ⟨V, hV, _⟩ := A.universal P.Carrier
    (fun i ↦ (P.inclusion_isVecLatHom i).mk' (P.inclusion i))
  have hd : IsOrderDense (Set.range V) := (archimedean_induced_orderDense P A
    (fun _ ↦ VecLatHom.id) (fun _ ↦ Function.injective_id)
    (fun _ x hx ↦ ⟨x, ⟨x, rfl⟩, hx, le_rfl⟩) V hV).2
  have hSV : Function.Injective ((hS.mk' S).comp V) :=
    archimedean_induced_injective Q A (fun i ↦ (hT i).mk' (T i)) hinj
      ((hS.mk' S).comp V) (fun i x ↦ (congrArg S (hV i x)).trans (hcomm i x))
  refine (injective_iff_map_eq_zero S).mpr (fun z hz ↦ ?_)
  by_contra hz0
  obtain ⟨_, ⟨a, rfl⟩, ha, haz⟩ := hd (lt_of_le_of_ne (abs_nonneg z)
    (fun h ↦ hz0 ((abs_eq_zero_iff_zero z).mp h.symm)))
  have hSa : S (V a) = 0 := le_antisymm
    (((hS.mk' S).monotone haz).trans_eq
      (((hS.mk' S).map_abs z).trans ((congrArg abs hz).trans abs_zero)))
    ((hS.mk' S).map_nonneg ha.le)
  have ha0 : a = 0 := hSV (hSa.trans (map_zero ((hS.mk' S).comp V)).symm)
  exact ha.ne' ((congrArg V ha0).trans (map_zero V))

/-- A finite subproduct embeds contractively in the full free product and admits a contractive
retraction that kills the other factors. -/
private lemma exists_subfamily_maps (s : Finset I)
    (R : FreeProduct (fun j : s ↦ E j.val)) :
    ∃ (U : R.Carrier →L[ℝ] P.Carrier) (V : P.Carrier →L[ℝ] R.Carrier),
      IsVecLatHom U ∧ IsVecLatHom V ∧ ‖U‖ ≤ 1 ∧ ‖V‖ ≤ 1 ∧
      (∀ j x, U (R.inclusion j x) = P.inclusion j.val x) ∧
      (∀ j x, V (P.inclusion j.val x) = R.inclusion j x) ∧
      (∀ i, i ∉ s → ∀ x, V (P.inclusion i x) = 0) ∧
      ∀ z, V (U z) = z := by
  classical
  obtain ⟨U, ⟨hU, hUcomm, hUnorm⟩, _⟩ := R.exists_unique_extension P.Carrier
    (fun j ↦ P.inclusion j.val) (fun j ↦ P.inclusion_isVecLatHom j.val)
    1 zero_le_one (fun j ↦ P.inclusion_contractive j.val)
  let W (i : I) : E i →L[ℝ] R.Carrier :=
    if hi : i ∈ s then R.inclusion ⟨i, hi⟩ else 0
  have hW (i : I) : IsVecLatHom (W i) := by
    dsimp only [W]
    split_ifs with hi
    · exact R.inclusion_isVecLatHom ⟨i, hi⟩
    · exact (VecLatHom.ofAbs 0 (by simp) : VecLatHom (E i) R.Carrier).isVecLatHom
  have hWnorm (i : I) : ‖W i‖ ≤ 1 := by
    dsimp only [W]
    split_ifs with hi
    · exact R.inclusion_contractive ⟨i, hi⟩
    · simp
  obtain ⟨V, ⟨hV, hVcomm, hVnorm⟩, _⟩ :=
    P.exists_unique_extension R.Carrier W hW 1 zero_le_one hWnorm
  have hselected (j : s) (x : E j.val) :
      V (P.inclusion j.val x) = R.inclusion j x :=
    (hVcomm j.val x).trans (by simp only [W, dite_eq_left j.property])
  have hoff (i : I) (hi : i ∉ s) (x : E i) : V (P.inclusion i x) = 0 :=
    (hVcomm i x).trans (by simp only [W, dite_eq_right hi, zero_apply])
  have hVU : V.comp U = ContinuousLinearMap.id ℝ R.Carrier :=
    R.extension_ext ((hV.mk' V).comp (hU.mk' U)).isVecLatHom VecLatHom.id.isVecLatHom
      (fun j x ↦ (congrArg V (hUcomm j x)).trans (hselected j x))
  exact ⟨U, V, hU, hV, hUnorm, hVnorm, hUcomm, hselected, hoff,
    fun z ↦ DFunLike.congr_fun hVU z⟩

/-- An element in the kernel of the induced free-product map has zero projection onto every
finite subproduct. -/
private lemma finite_projection_eq_zero (Q : FreeProduct F)
    (T : ∀ i, E i →L[ℝ] F i) (hT : ∀ i, IsVecLatHom (T i))
    (hinj : ∀ i, Function.Injective (T i))
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ i, ‖T i‖ ≤ M)
    (S : P.Carrier →L[ℝ] Q.Carrier) (hS : IsVecLatHom S)
    (hcomm : ∀ i x, S (P.inclusion i x) = Q.inclusion i (T i x))
    (s : Finset I) (R : FreeProduct (fun j : s ↦ E j.val))
    (R' : FreeProduct (fun j : s ↦ F j.val))
    (V : P.Carrier →L[ℝ] R.Carrier) (hV : IsVecLatHom V)
    (hVcomm : ∀ j x, V (P.inclusion j.val x) = R.inclusion j x)
    (hVoff : ∀ i, i ∉ s → ∀ x, V (P.inclusion i x) = 0)
    (W : Q.Carrier →L[ℝ] R'.Carrier) (hW : IsVecLatHom W)
    (hWcomm : ∀ j x, W (Q.inclusion j.val x) = R'.inclusion j x)
    (hWoff : ∀ i, i ∉ s → ∀ x, W (Q.inclusion i x) = 0)
    (z : P.Carrier) (hz : S z = 0) : V z = 0 := by
  have hnorm (j : s) : ‖(R'.inclusion j).comp (T j.val)‖ ≤ M :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (R'.inclusion_contractive j) (hbound j.val)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul M))
  obtain ⟨A, ⟨hA, hAcomm, _⟩, _⟩ := R.exists_unique_extension R'.Carrier
    (fun j ↦ (R'.inclusion j).comp (T j.val))
    (fun j ↦ ((R'.inclusion_isVecLatHom j).mk' (R'.inclusion j) |>.comp
      ((hT j.val).mk' (T j.val))).isVecLatHom) M hM hnorm
  have hAinj : Function.Injective A := induced_injective_finite R R'
    (fun j ↦ T j.val) (fun j ↦ hT j.val) (fun j ↦ hinj j.val) A hA hAcomm
  have heq : W.comp S = A.comp V := by
    refine P.extension_ext ((hW.mk' W).comp (hS.mk' S)).isVecLatHom
      ((hA.mk' A).comp (hV.mk' V)).isVecLatHom (fun i x ↦ ?_)
    by_cases hi : i ∈ s
    · exact ((congrArg W (hcomm i x)).trans (hWcomm ⟨i, hi⟩ (T i x))).trans
        ((hAcomm ⟨i, hi⟩ x).symm.trans (congrArg A (hVcomm ⟨i, hi⟩ x)).symm)
    · exact ((congrArg W (hcomm i x)).trans (hWoff i hi (T i x))).trans
        ((congrArg A (hVoff i hi x)).trans (map_zero A)).symm
  exact hAinj (((DFunLike.congr_fun heq z).symm.trans
    ((congrArg W hz).trans (map_zero W))).trans (map_zero A).symm)

/-- Finite-subproduct approximation forces the norm of a kernel element to be bounded by every
positive tolerance. -/
private lemma norm_le_of_mem_kernel (Q : FreeProduct F)
    (T : ∀ i, E i →L[ℝ] F i) (hT : ∀ i, IsVecLatHom (T i))
    (hinj : ∀ i, Function.Injective (T i))
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ i, ‖T i‖ ≤ M)
    (S : P.Carrier →L[ℝ] Q.Carrier) (hS : IsVecLatHom S)
    (hcomm : ∀ i x, S (P.inclusion i x) = Q.inclusion i (T i x))
    (z : P.Carrier) (hz : S z = 0) (ε : ℝ) (hε : 0 < ε) : ‖z‖ ≤ ε := by
  classical
  obtain ⟨v, hvG, hv⟩ := P.dense_generated.exists_dist_lt z (half_pos hε)
  obtain ⟨n, i, x, φ, hφ⟩ := P.exists_expression ⟨v, hvG⟩
  let s : Finset I := Finset.univ.image i
  let j (k : Fin n) : s := ⟨i k, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩⟩
  obtain ⟨R⟩ := nonempty_freeProduct (fun j : s ↦ E j.val)
  obtain ⟨R'⟩ := nonempty_freeProduct (fun j : s ↦ F j.val)
  obtain ⟨U, V, hU, hV, hUnorm, hVnorm, hUcomm, hVcomm, hVoff, hVU⟩ :=
    exists_subfamily_maps P s R
  obtain ⟨_, W, _, hW, _, _, _, hWcomm, hWoff, _⟩ := exists_subfamily_maps Q s R'
  have hVz : V z = 0 := finite_projection_eq_zero P Q T hT hinj M hM hbound S hS hcomm
    s R R' V hV hVcomm hVoff W hW hWcomm hWoff z hz
  let w : R.Carrier := LLexpr.eval (fun k ↦ R.inclusion (j k) (x k)) φ
  have hw : U w = v :=
    (R.extension_eval (fun j ↦ P.inclusion j.val) U hU hUcomm j x φ).trans hφ.symm
  have hfix : U (V v) = v := (congrArg (fun y ↦ U (V y)) hw).symm.trans
    ((congrArg U (hVU w)).trans hw)
  have hproj : V (v - z) = V v := (map_sub V v z).trans (by rw [hVz, sub_zero])
  have hvnorm : ‖v‖ ≤ ‖v - z‖ :=
    (congrArg norm ((congrArg U hproj).trans hfix)).symm.trans_le
      (((U.le_of_opNorm_le hUnorm _).trans_eq (one_mul _)).trans
        ((V.le_of_opNorm_le hVnorm _).trans_eq (one_mul _)))
  have hdiff : ‖v - z‖ < ε / 2 := by simpa only [dist_eq_norm'] using hv
  linarith [norm_le_norm_add_norm_sub v z]

/-- A uniformly bounded family of injective Banach lattice homomorphisms
induces an injective homomorphism between the Banach lattice free products. -/
theorem induced_injective (Q : FreeProduct F)
    (T : ∀ i, E i →L[ℝ] F i)
    (hT : ∀ i, IsVecLatHom (T i))
    (hinj : ∀ i, Function.Injective (T i))
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ i, ‖T i‖ ≤ M)
    (S : P.Carrier →L[ℝ] Q.Carrier) (hS : IsVecLatHom S)
    (hcomm : ∀ i x, S (P.inclusion i x) = Q.inclusion i (T i x)) :
    Function.Injective S := by
  refine (injective_iff_map_eq_zero S).mpr (fun z hz ↦ ?_)
  exact norm_eq_zero.mp (le_antisymm
    (le_of_forall_gt_imp_ge_of_dense (fun ε hε ↦
      norm_le_of_mem_kernel P Q T hT hinj M hM hbound S hS hcomm z hz ε hε))
    (norm_nonneg z))

end Injectivity

end BanachLattice.FreeProduct
