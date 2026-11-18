/-
Authors: Gonzalo Martínez-Fernández
-/

import FreeProducts.Archimedean.Embeddings
import BanLat.OrderDense

/-!
# Banach comparison, norm estimates, and Archimedean completion

Embeddings of Archimedean factors into Banach lattices induce an injective map
from their Archimedean free product to the Banach free product. For Banach factors,
this identifies the Archimedean free product with the generated sublattice, whose
maximal compatible lattice norm completes it to the Banach free product. Positive
factor majorants recover the norm on the binary generated sublattice.
-/

universe u v

namespace VectorLattice

section BinaryBanachEmbeddings

variable {E : ULift.{u} Bool → Type u} {F : Bool → Type u}
  [∀ i, AddCommGroup (E i)] [∀ i, Lattice (E i)]
  [∀ i, IsOrderedAddMonoid (E i)] [∀ i, VectorLattice (E i)]
  [∀ i, IsVLArchimedean (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, Lattice (F i)]
  [∀ i, IsOrderedAddMonoid (F i)] [∀ i, BanachLattice (F i)]

/-- A factor embedding whose range lies in a positive principal ideal factors through
its compact continuous-function representation. -/
private lemma principal_representation_factorization
    {X Y : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [VectorLattice X] [NormedAddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] [BanachLattice Y]
    (T : VecLatHom X Y) (hT : Function.Injective T) (e : Y) (he : 0 < e)
    (hmem : ∀ x, T x ∈ OrderIdeal.principal e) :
    ∃ (K : Type u) (_ : TopologicalSpace K) (_ : CompactSpace K) (_ : T2Space K)
      (_ : Nonempty K) (j : VecLatHom X C(K, ℝ)) (J : C(K, ℝ) →L[ℝ] Y),
      Function.Injective j ∧ IsVecLatHom J ∧ Function.Injective J ∧ ∀ x, J (j x) = T x := by
  let D := ↥(OrderIdeal.principal e)
  let : NormedAddCommGroup D := OrderIdeal.principalNormedAddCommGroup e
  let : Lattice D := OrderIdeal.instLatticePrincipal e
  let : IsOrderedAddMonoid D := OrderIdeal.instIsOrderedAddMonoidPrincipal e
  let : AMSpaceWithUnit D := OrderIdeal.principalAMSpaceWithUnit he.le
    ((isUniformlyCompleteVectorLattice_of_banachLattice Y).complete_principal e he)
  have : Nontrivial D := ⟨⟨0, ⟨e, OrderIdeal.self_mem_principal e⟩,
    fun h ↦ (ne_of_gt he) (congrArg Subtype.val h).symm⟩⟩
  let d : VecLatHom X D :=
    { toFun := fun x ↦ ⟨T x, hmem x⟩
      map_add' := fun x y ↦ Subtype.ext (map_add T x y)
      map_smul' := fun r x ↦ Subtype.ext (map_smul T r x)
      map_sup' := fun x y ↦ Subtype.ext (map_sup T x y)
      map_inf' := fun x y ↦ Subtype.ext (map_inf T x y) }
  let : SeminormedAddCommGroup D :=
    (OrderIdeal.principalNormedAddCommGroup e).toSeminormedAddCommGroup
  let : TopologicalSpace D :=
    (OrderIdeal.principalNormedAddCommGroup e).toMetricSpace.toUniformSpace.toTopologicalSpace
  let k := AMSpaceWithUnit.kakutaniEquiv D
  let l := (OrderIdeal.principal e).toVectorSublattice.subtype.comp
    k.symm.toVecLatEquiv.toVecLatHom
  let J : C(AMSpaceWithUnit.LatticeCharacter D, ℝ) →L[ℝ] Y :=
    ⟨l.toLinearMap, Positive.continuous (Positive.monotone_iff.mp l.monotone)⟩
  have : Nonempty (AMSpaceWithUnit.LatticeCharacter D) :=
    let ⟨φ, _⟩ := AMSpaceWithUnit.LatticeCharacter.exists_abs_apply_eq_norm (X := D) 0
    ⟨φ⟩
  refine ⟨AMSpaceWithUnit.LatticeCharacter D, inferInstance, inferInstance, inferInstance,
    inferInstance, k.toVecLatEquiv.toVecLatHom.comp d, J,
    k.toLinearIsometryEquiv.injective.comp (fun x y h ↦ hT (congrArg Subtype.val h)),
    l.isVecLatHom, Subtype.val_injective.comp k.symm.toLinearIsometryEquiv.injective, ?_⟩
  exact fun x ↦ congrArg Subtype.val (k.toLinearIsometryEquiv.symm_apply_apply (d x))

/-- Embeddings into continuous-function spaces induce an embedding into their Banach
free product, by the Archimedean embedding theorem and the join representation. -/
private lemma ArchimedeanFreeProduct.banach_continuousFunctions_injective
    (P : ArchimedeanFreeProduct E)
    (K : Bool → Type u) [∀ b, TopologicalSpace (K b)] [∀ b, CompactSpace (K b)]
    [∀ b, T2Space (K b)] [∀ b, Nonempty (K b)]
    (j : ∀ b, VecLatHom (E ⟨b⟩) C(K b, ℝ)) (hj : ∀ b, Function.Injective (j b))
    (B : BanachLattice.FreeProduct (fun b ↦ C(K b, ℝ)))
    (U : VecLatHom P.Carrier B.Carrier)
    (hU : ∀ b x, U (P.inclusion ⟨b⟩ x) = B.inclusion b (j b x)) :
    Function.Injective U := by
  obtain ⟨A⟩ := nonempty_archimedeanFreeProduct (fun i : ULift.{u} Bool ↦ C(K i.down, ℝ))
  obtain ⟨W, hW, _⟩ := P.universal A.Carrier (fun i ↦ (A.inclusion i).comp (j i.down))
  obtain ⟨V, hV, _⟩ := A.universal B.Carrier
    (fun i ↦ (B.inclusion_isVecLatHom i.down).mk' (B.inclusion i.down))
  have hVi := A.completion_map_injective K (fun _ ↦ VecLatHom.id)
    (fun _ ↦ Function.injective_id) (fun _ ↦ denseRange_id)
    (fun _ ↦ 1) (fun _ ↦ rfl) B V (fun b ↦ hV ⟨b⟩)
  have hWi := P.induced_injective A (fun i ↦ j i.down) (fun i ↦ hj i.down) W hW
  have hcomp : U = V.comp W := P.hom_ext (fun i x ↦
    (hU i.down x).trans ((congrArg V (hW i x)).trans (hV i (j i.down x))).symm)
  exact fun x y h ↦ hWi (hVi ((DFunLike.congr_fun hcomp x).symm.trans
    (h.trans (DFunLike.congr_fun hcomp y))))

/-- Factor embeddings with strong units take values in complete principal ideals of the
Banach factors. Their continuous-function representations give an injective comparison. -/
private lemma ArchimedeanFreeProduct.banach_injective_via_principal_ideals
    (P : ArchimedeanFreeProduct E) (Q : BanachLattice.FreeProduct F)
    (e : ∀ i, E i) (he : ∀ i, StrongOrderUnit (e i)) (he0 : ∀ i, 0 < e i)
    (T : ∀ b, VecLatHom (E ⟨b⟩) (F b)) (hT : ∀ b, Function.Injective (T b))
    (S : VecLatHom P.Carrier Q.Carrier)
    (hS : ∀ b x, S (P.inclusion ⟨b⟩ x) = Q.inclusion b (T b x)) :
    Function.Injective S := by
  have hpos (b : Bool) : 0 < T b (e ⟨b⟩) :=
    lt_of_le_of_ne ((T b).map_nonneg (he0 ⟨b⟩).le) (fun h ↦
      (ne_of_gt (he0 ⟨b⟩)) (hT b (h.symm.trans (map_zero (T b)).symm)))
  have hmem (b : Bool) (x : E ⟨b⟩) : T b x ∈ OrderIdeal.principal (T b (e ⟨b⟩)) :=
    let ⟨c, hc, hcx⟩ := (he ⟨b⟩).2 x
    ⟨c, hc, by simpa only [VecLatHom.map_abs, map_smul, abs_of_nonneg (hpos b).le] using
      (T b).monotone hcx⟩
  choose K tK cK hK nK j J hj hJ hJi hJx using fun b : Bool ↦
    principal_representation_factorization (T b) (hT b) (T b (e ⟨b⟩)) (hpos b) (hmem b)
  obtain ⟨B⟩ := BanachLattice.nonempty_freeProduct (fun b ↦ C(K b, ℝ))
  obtain ⟨U, hU, _⟩ := P.universal B.Carrier (fun i ↦
    ((B.inclusion_isVecLatHom i.down).mk' (B.inclusion i.down)).comp (j i.down))
  let Rb (b : Bool) := (Q.inclusion b).comp (J b)
  have hRb (b : Bool) : IsVecLatHom (Rb b) :=
    (((Q.inclusion_isVecLatHom b).mk' (Q.inclusion b)).comp ((hJ b).mk' (J b))).isVecLatHom
  obtain ⟨R, ⟨hR, hRx, _⟩, _⟩ := B.exists_unique_extension Q.Carrier Rb hRb
    (max ‖Rb false‖ ‖Rb true‖) ((norm_nonneg (Rb false)).trans (le_max_left _ _))
    (fun b ↦ by
      cases b
      · exact le_max_left _ _
      · exact le_max_right _ _)
  have hRi := BanachLattice.FreeProduct.induced_injective_of_continuousFunctions
    K F B Q J hJ hJi R hR hRx
  have hUi := P.banach_continuousFunctions_injective K j hj B U (fun b ↦ hU ⟨b⟩)
  have hcomp : S = (hR.mk' R).comp U := by
    apply P.hom_ext
    rintro ⟨b⟩ x
    change S (P.inclusion ⟨b⟩ x) = R (U (P.inclusion ⟨b⟩ x))
    rw [hS, hU]
    change Q.inclusion b (T b x) = R (B.inclusion b (j b x))
    rw [hRx]
    exact congrArg (Q.inclusion b) (hJx b x).symm
  exact fun x y hxy ↦ hUi (hRi ((DFunLike.congr_fun hcomp x).symm.trans
    (hxy.trans (DFunLike.congr_fun hcomp y))))

/-- The comparison map into a Banach free product is injective when only one source factor can
be nonzero. -/
private lemma ArchimedeanFreeProduct.banach_injective_of_one_factor
    (P : ArchimedeanFreeProduct E) (Q : BanachLattice.FreeProduct F)
    (T : ∀ b, VecLatHom (E ⟨b⟩) (F b)) (hT : ∀ b, Function.Injective (T b))
    (S : VecLatHom P.Carrier Q.Carrier)
    (hS : ∀ b x, S (P.inclusion ⟨b⟩ x) = Q.inclusion b (T b x))
    (i : Bool) (hi : ∀ j, j ≠ ⟨i⟩ → Subsingleton (E j)) : Function.Injective S := by
  intro x y hxy
  obtain ⟨x, rfl⟩ := P.inclusion_surjective_of_subsingleton ⟨i⟩ hi x
  obtain ⟨y, rfl⟩ := P.inclusion_surjective_of_subsingleton ⟨i⟩ hi y
  exact congrArg (P.inclusion ⟨i⟩) (hT i ((Q.isometry_inclusion i).injective
    ((hS i x).symm.trans (hxy.trans (hS i y)))))

/-- The comparison into a Banach free product is injective for source factors with strong
units, including zero factors. -/
private lemma ArchimedeanFreeProduct.banach_injective_of_units
    (P : ArchimedeanFreeProduct E) (Q : BanachLattice.FreeProduct F)
    (hE : ∀ i, ∃ e : E i, StrongOrderUnit e)
    (T : ∀ b, VecLatHom (E ⟨b⟩) (F b)) (hT : ∀ b, Function.Injective (T b))
    (S : VecLatHom P.Carrier Q.Carrier)
    (hS : ∀ b x, S (P.inclusion ⟨b⟩ x) = Q.inclusion b (T b x)) :
    Function.Injective S := by
  rcases subsingleton_or_nontrivial (E ⟨false⟩) with h₀ | h₀
  · apply P.banach_injective_of_one_factor Q T hT S hS true
    rintro ⟨_ | _⟩ h
    · exact h₀
    · exact (h rfl).elim
  · rcases subsingleton_or_nontrivial (E ⟨true⟩) with h₁ | h₁
    · apply P.banach_injective_of_one_factor Q T hT S hS false
      rintro ⟨_ | _⟩ h
      · exact (h rfl).elim
      · exact h₁
    · have (i : ULift.{u} Bool) : Nontrivial (E i) := by
        rcases i with ⟨_ | _⟩
        · exact h₀
        · exact h₁
      choose e he using hE
      exact P.banach_injective_via_principal_ideals Q e he
        (fun i ↦ strongOrderUnit_pos (he i)) T hT S hS

/-- Embeddings of two Archimedean factors into Banach lattices induce an embedding into their
Banach free product. -/
private lemma ArchimedeanFreeProduct.banach_injective_binary
    (P : ArchimedeanFreeProduct E) (Q : BanachLattice.FreeProduct F)
    (T : ∀ b, VecLatHom (E ⟨b⟩) (F b)) (hT : ∀ b, Function.Injective (T b))
    (S : VecLatHom P.Carrier Q.Carrier)
    (hS : ∀ b x, S (P.inclusion ⟨b⟩ x) = Q.inclusion b (T b x)) :
    Function.Injective S := by
  classical
  let B (d : ∀ i, Finset (E i)) :=
    (nonempty_archimedeanFreeProduct (fun i ↦
      VectorSublattice.generated (d i : Set (E i)))).some
  obtain ⟨U, hU, _, hUc⟩ := P.exists_finite_stage_maps B
  refine (injective_iff_map_eq_zero S).mpr (fun z hz ↦ ?_)
  obtain ⟨d, x, rfl⟩ := hUc z
  -- The finite generators lie in the principal ideals generated by their positive majorants.
  have hSU : Function.Injective (S.comp (U d)) :=
    (B d).banach_injective_of_units Q
      (fun i ↦ exists_strongOrderUnit_generated_finset (d i))
      (fun b ↦ (T b).comp (VectorSublattice.generated (d ⟨b⟩ : Set (E ⟨b⟩))).subtype)
      (fun b ↦ (hT b).comp Subtype.val_injective) (S.comp (U d))
      (fun b y ↦ (congrArg S (hU d ⟨b⟩ y)).trans (hS b y))
  exact (congrArg (U d) (hSU (hz.trans (map_zero (S.comp (U d))).symm))).trans (map_zero _)

end BinaryBanachEmbeddings

/-- Encodes a pair of Banach lattices as a Boolean-indexed family. -/
private def banachBinaryFamily (X Y : Type u) (b : Bool) : Type u := Bool.rec X Y b

/-- Each member of the binary Banach family inherits its normed additive group. -/
private instance banachBinaryNormedAddCommGroup {X Y : Type u}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] (b : Bool) :
    NormedAddCommGroup (banachBinaryFamily X Y b) := by
  cases b <;> assumption

/-- Each member of the binary Banach family inherits its lattice order. -/
private instance banachBinaryLattice {X Y : Type u} [Lattice X] [Lattice Y] (b : Bool) :
    Lattice (banachBinaryFamily X Y b) := by
  cases b <;> assumption

/-- Addition is order compatible in each member of the binary Banach family. -/
private instance banachBinaryIsOrderedAddMonoid {X Y : Type u}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [Lattice X] [Lattice Y]
    [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y] (b : Bool) :
    IsOrderedAddMonoid (banachBinaryFamily X Y b) := by
  cases b <;> assumption

/-- Each member of the binary Banach family has its original Banach lattice structure. -/
private instance banachBinaryBanachLattice {X Y : Type u}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [Lattice X] [Lattice Y]
    [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y] [BanachLattice X] [BanachLattice Y]
    (b : Bool) : BanachLattice (banachBinaryFamily X Y b) := by
  cases b <;> assumption

section BanachEmbeddings

variable {I : Type u} {E F : I → Type u}
  [∀ i, AddCommGroup (E i)] [∀ i, Lattice (E i)]
  [∀ i, IsOrderedAddMonoid (E i)] [∀ i, VectorLattice (E i)]
  [∀ i, IsVLArchimedean (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, Lattice (F i)]
  [∀ i, IsOrderedAddMonoid (F i)] [∀ i, BanachLattice (F i)]

/-- Maps a Banach free product into its binary regrouping, preserving the isolated factor and
the complementary inclusions. -/
private lemma exists_split_banach_map (Q : BanachLattice.FreeProduct F) (i : I)
    (R : BanachLattice.FreeProduct (fun j : {j : I // j ≠ i} ↦ F j.val))
    (C : BanachLattice.FreeProduct (banachBinaryFamily (F i) R.Carrier)) :
    ∃ V : Q.Carrier →L[ℝ] C.Carrier, IsVecLatHom V ∧
      (∀ x, V (Q.inclusion i x) = C.inclusion false x) ∧
      (∀ j : {j : I // j ≠ i}, ∀ x,
        V (Q.inclusion j.val x) = C.inclusion true (R.inclusion j x)) := by
  classical
  let Vj (j : I) : F j →L[ℝ] C.Carrier :=
    if h : j = i then h ▸ C.inclusion false
    else (C.inclusion true).comp (R.inclusion ⟨j, h⟩)
  have hVj (j : I) : IsVecLatHom (Vj j) := by
    dsimp only [Vj]
    split_ifs with h
    · subst j
      exact C.inclusion_isVecLatHom false
    · exact (((C.inclusion_isVecLatHom true).mk' (C.inclusion true)).comp
        ((R.inclusion_isVecLatHom ⟨j, h⟩).mk' (R.inclusion ⟨j, h⟩))).isVecLatHom
  have hVnorm (j : I) : ‖Vj j‖ ≤ 1 := by
    dsimp only [Vj]
    split_ifs with h
    · subst j
      exact C.inclusion_contractive false
    · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        ((mul_le_mul (C.inclusion_contractive true) (R.inclusion_contractive ⟨j, h⟩)
          (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  obtain ⟨V, ⟨hV, hVx, _⟩, _⟩ := Q.exists_unique_extension C.Carrier Vj hVj
    1 zero_le_one hVnorm
  refine ⟨V, hV, ?_, ?_⟩
  · intro x
    exact (hVx i x).trans (by simp only [Vj, dite_eq_left rfl]; rfl)
  · intro j x
    exact (hVx j.val x).trans (by simp only [Vj, dite_eq_right j.property]; rfl)

/-- Injectivity of the complementary comparison map implies injectivity after adding one more
factor to the Banach target. -/
private lemma ArchimedeanFreeProduct.banach_injective_of_complement
    (P : ArchimedeanFreeProduct E) (Q : BanachLattice.FreeProduct F)
    (T : ∀ i, VecLatHom (E i) (F i)) (hT : ∀ i, Function.Injective (T i))
    (S : VecLatHom P.Carrier Q.Carrier)
    (hS : ∀ i x, S (P.inclusion i x) = Q.inclusion i (T i x)) (i : I)
    (R : ArchimedeanFreeProduct (fun j : {j : I // j ≠ i} ↦ E j.val))
    (R' : BanachLattice.FreeProduct (fun j : {j : I // j ≠ i} ↦ F j.val))
    (W : VecLatHom R.Carrier R'.Carrier) (hWi : Function.Injective W)
    (hW : ∀ j x, W (R.inclusion j x) = R'.inclusion j (T j.val x)) :
    Function.Injective S := by
  classical
  obtain ⟨B⟩ := nonempty_archimedeanFreeProduct (binaryFamily (E i) R.Carrier)
  obtain ⟨C⟩ := BanachLattice.nonempty_freeProduct (banachBinaryFamily (F i) R'.Carrier)
  obtain ⟨p, hp, _⟩ := P.exists_unique_equiv (splitProduct i R B)
  obtain ⟨V, hV, hVi, hVc⟩ := exists_split_banach_map Q i R' C
  let Tb : ∀ b, VecLatHom (binaryFamily (E i) R.Carrier ⟨b⟩)
      (banachBinaryFamily (F i) R'.Carrier b) := fun
    | false => T i
    | true => W
  obtain ⟨M, hM, _⟩ := B.universal C.Carrier (fun b ↦
    ((C.inclusion_isVecLatHom b.down).mk' (C.inclusion b.down)).comp (Tb b.down))
  have hMi : Function.Injective M := B.banach_injective_binary C Tb
    (fun b ↦ by
      cases b
      · exact hT i
      · exact hWi) M (fun b ↦ hM ⟨b⟩)
  have hcomm : (hV.mk' V).comp S = M.comp p.toVecLatHom := by
    apply P.hom_ext
    intro j x
    change V (S (P.inclusion j x)) = M (p (P.inclusion j x))
    rw [hS, hp]
    change V (Q.inclusion j (T j x)) = M (splitInclusion i R B j x)
    by_cases hji : j = i
    · subst j
      rw [hVi, splitInclusion, dite_eq_left rfl]
      exact (hM ⟨false⟩ x).symm
    · rw [hVc ⟨j, hji⟩, splitInclusion, dite_eq_right hji]
      exact (congrArg (C.inclusion true) (hW ⟨j, hji⟩ x)).symm.trans
        (hM ⟨true⟩ (R.inclusion ⟨j, hji⟩ x)).symm
  exact fun x y h ↦ p.toLinearEquiv.injective (hMi
    ((DFunLike.congr_fun hcomm x).symm.trans ((congrArg V h).trans
      (DFunLike.congr_fun hcomm y))))

/-- For finitely many factors, the comparison induced by embeddings into Banach lattices is
injective. -/
private lemma ArchimedeanFreeProduct.banach_injective_finite [Finite I]
    (P : ArchimedeanFreeProduct E) (Q : BanachLattice.FreeProduct F)
    (T : ∀ i, VecLatHom (E i) (F i)) (hT : ∀ i, Function.Injective (T i))
    (S : VecLatHom P.Carrier Q.Carrier)
    (hS : ∀ i x, S (P.inclusion i x) = Q.inclusion i (T i x)) :
    Function.Injective S := by
  classical
  induction hn : Nat.card I using Nat.strong_induction_on generalizing I with
  | h n ih =>
    cases isEmpty_or_nonempty I with
    | inl h =>
      let := h
      have hp : (VecLatHom.id : VecLatHom P.Carrier P.Carrier) =
          VecLatHom.ofAbs 0 (by simp) := P.hom_ext (fun i ↦ isEmptyElim i)
      exact fun x y _ ↦ (DFunLike.congr_fun hp x).trans (DFunLike.congr_fun hp y).symm
    | inr h =>
      let := h
      let i : I := Classical.arbitrary I
      obtain ⟨R⟩ := nonempty_archimedeanFreeProduct (fun j : {j : I // j ≠ i} ↦ E j.val)
      obtain ⟨R'⟩ := BanachLattice.nonempty_freeProduct (fun j : {j : I // j ≠ i} ↦ F j.val)
      obtain ⟨W, hW, _⟩ := R.universal R'.Carrier
        (fun j ↦ ((R'.inclusion_isVecLatHom j).mk' (R'.inclusion j)).comp (T j.val))
      apply P.banach_injective_of_complement Q T hT S hS i R R' W ?_ hW
      let := Fintype.ofFinite I
      exact ih _ (by
        rw [← hn, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
        exact Fintype.card_subtype_lt (fun h ↦ h rfl))
        R R' (fun j ↦ T j.val) (fun j ↦ hT j.val) W hW rfl

/-- For any family, embeddings into Banach lattices induce an injective map from the
Archimedean free product to the Banach free product. -/
private lemma ArchimedeanFreeProduct.banach_induced_injective
    (P : ArchimedeanFreeProduct E) (Q : BanachLattice.FreeProduct F)
    (T : ∀ i, VecLatHom (E i) (F i)) (hT : ∀ i, Function.Injective (T i))
    (S : VecLatHom P.Carrier Q.Carrier)
    (hS : ∀ i x, S (P.inclusion i x) = Q.inclusion i (T i x)) :
    Function.Injective S := by
  classical
  refine (injective_iff_map_eq_zero S).mpr (fun z hz ↦ ?_)
  obtain ⟨s, R, U, hU, x, rfl⟩ := P.exists_finite_subfamily_lift z
  obtain ⟨R'⟩ := BanachLattice.nonempty_freeProduct (fun i : s ↦ F i.val)
  obtain ⟨W, hW, _⟩ := R.universal R'.Carrier
    (fun i ↦ ((R'.inclusion_isVecLatHom i).mk' (R'.inclusion i)).comp (T i.val))
  have hWi := R.banach_injective_finite R' (fun i ↦ T i.val) (fun i ↦ hT i.val) W hW
  let Tr (i : I) : F i →L[ℝ] R'.Carrier :=
    if h : i ∈ s then R'.inclusion ⟨i, h⟩ else 0
  have hTr (i : I) : IsVecLatHom (Tr i) := by
    dsimp only [Tr]
    split_ifs with h
    · exact R'.inclusion_isVecLatHom ⟨i, h⟩
    · exact (VecLatHom.ofAbs (0 : F i →ₗ[ℝ] R'.Carrier) (by simp)).isVecLatHom
  have hTrnorm (i : I) : ‖Tr i‖ ≤ 1 := by
    dsimp only [Tr]
    split_ifs with h
    · exact R'.inclusion_contractive ⟨i, h⟩
    · simp only [norm_zero, zero_le_one]
  obtain ⟨V, ⟨hV, hVx, _⟩, _⟩ := Q.exists_unique_extension R'.Carrier Tr hTr
    1 zero_le_one hTrnorm
  have hcomm : (hV.mk' V).comp (S.comp U) = W := by
    apply R.hom_ext
    intro i y
    change V (S (U (R.inclusion i y))) = W (R.inclusion i y)
    rw [hU, hS, hVx, hW]
    dsimp only [Tr]
    rw [dite_eq_left i.property]
    rfl
  have hx : W x = 0 := (DFunLike.congr_fun hcomm x).symm.trans
    ((congrArg V hz).trans (map_zero V))
  exact (congrArg U (hWi (hx.trans (map_zero W).symm))).trans (map_zero U)

/-- The comparison map from the Archimedean free product covers the sublattice generated by
the Banach free-product factors. -/
private lemma generated_subset_range (P : ArchimedeanFreeProduct F)
    (Q : BanachLattice.FreeProduct F) (S : VecLatHom P.Carrier Q.Carrier)
    (hS : ∀ i x, S (P.inclusion i x) = Q.inclusion i x) :
    (Q.generated : Set Q.Carrier) ⊆ Set.range S := by
  let R : VectorSublattice Q.Carrier :=
    { S.toLinearMap.range with
      sup_mem' := by
        rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        exact ⟨x ⊔ y, map_sup S x y⟩ }
  exact (show Q.generated ≤ R from VectorSublattice.generated_le (by
    rintro _ ⟨⟨i, x⟩, rfl⟩
    exact ⟨P.inclusion i x, hS i x⟩))

/-- The Archimedean free product of Banach lattices identifies with the
sublattice generated by their canonical copies in the Banach lattice free product. -/
theorem ArchimedeanFreeProduct.exists_generated_equiv
    (P : ArchimedeanFreeProduct F) (Q : BanachLattice.FreeProduct F) :
    ∃ e : VecLatEquiv P.Carrier Q.generated,
      ∀ i x, (e (P.inclusion i x) : Q.Carrier) = Q.inclusion i x := by
  let j (i : I) : VecLatHom (F i) Q.generated :=
    { (Q.inclusion i).toLinearMap.codRestrict Q.generated.toSubmodule
        (fun x ↦ VectorSublattice.subset_generated _ ⟨⟨i, x⟩, rfl⟩) with
      map_sup' := fun x y ↦ Subtype.ext ((Q.inclusion_isVecLatHom i).map_sup' x y)
      map_inf' := fun x y ↦ Subtype.ext ((Q.inclusion_isVecLatHom i).map_inf' x y) }
  obtain ⟨U, hU, _⟩ := P.universal Q.generated j
  have hcomm (i : I) (x : F i) : (U (P.inclusion i x) : Q.Carrier) = Q.inclusion i x :=
    congrArg Subtype.val (hU i x)
  have hUi : Function.Injective U := Function.Injective.of_comp
    (f := Q.generated.subtype) (P.banach_induced_injective Q (fun _ ↦ VecLatHom.id)
      (fun _ ↦ Function.injective_id) (Q.generated.subtype.comp U) hcomm)
  have hUs : Function.Surjective U := by
    intro z
    obtain ⟨x, hx⟩ := generated_subset_range P Q (Q.generated.subtype.comp U) hcomm z.property
    exact ⟨x, Subtype.ext hx⟩
  exact ⟨{ LinearEquiv.ofBijective U.toLinearMap ⟨hUi, hUs⟩ with
    map_sup' := U.map_sup'
    map_inf' := U.map_inf' }, hcomm⟩

end BanachEmbeddings

end VectorLattice

namespace BanachLattice.FreeProduct

section Completion

variable {I : Type u} {E : I → Type u}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, Lattice (E i)]
  [∀ i, IsOrderedAddMonoid (E i)] [∀ i, BanachLattice (E i)]
  (P : FreeProduct E)

/-- Every lattice seminorm on the generated sublattice that is contractive on the factors is
bounded by the free-product norm. -/
private lemma compatible_seminorm_le_norm (p : Seminorm ℝ P.generated)
    (hsolid : ∀ z w, |z| ≤ |w| → p z ≤ p w)
    (hfactor : ∀ i x (z : P.generated),
      (z : P.Carrier) = P.inclusion i x → p z ≤ ‖x‖) (z : P.generated) :
    p z ≤ ‖(z : P.Carrier)‖ := by
  refine (show p z ≤ (p ⊔ normSeminorm ℝ P.generated) z from le_max_left _ _).trans
    (P.seminorm_le_norm (p ⊔ normSeminorm ℝ P.generated) ?_ ?_ ?_ z)
  · exact fun z hz ↦ norm_eq_zero.mp
      (le_antisymm ((le_max_right (p z) ‖z‖).trans_eq hz) (norm_nonneg z))
  · exact fun z w h ↦ max_le_max (hsolid z w h) (norm_le_norm_of_abs_le_abs h)
  · intro i x z hz
    exact max_le (hfactor i x z hz)
      ((congrArg norm hz).trans_le ((P.isometry_inclusion i).norm_map_of_map_zero
        (map_zero (P.inclusion i)) x).le)

/-- The norm completion of the sublattice generated by the factors is canonically the whole
Banach lattice free product. -/
private lemma generated_completion :
    ∃ Φ : BanachLatEquiv (UniformSpace.Completion P.generated) P.Carrier,
      ∀ z : P.generated, Φ (z : UniformSpace.Completion P.generated) = (z : P.Carrier) := by
  have hd : DenseRange P.generated.subtype := P.dense_generated.denseRange_val
  refine ⟨banachLatEquivCompletionOfDenseIsometry P.generated.subtype (fun _ ↦ rfl) hd, ?_⟩
  exact fun z ↦ UniformSpace.Completion.extension_coe uniformContinuous_subtype_val z

/-- A compatible lattice seminorm on the Archimedean free product is bounded by the norm
transported from the Banach lattice free product. -/
private lemma seminorm_le_of_generated_equiv
    (A : VectorLattice.ArchimedeanFreeProduct E) (e : VecLatEquiv A.Carrier P.generated)
    (he : ∀ i x, (e (A.inclusion i x) : P.Carrier) = P.inclusion i x)
    (p : Seminorm ℝ A.Carrier) (hsolid : ∀ x y, |x| ≤ |y| → p x ≤ p y)
    (hfactor : ∀ i x, p (A.inclusion i x) ≤ ‖x‖) (z : A.Carrier) :
    p z ≤ ‖(e z : P.Carrier)‖ := by
  let q := p.comp e.symm.toLinearMap
  have hqsolid (x y : P.generated) (h : |x| ≤ |y|) : q x ≤ q y := by
    apply hsolid
    exact (e.symm.toVecLatHom.map_abs x).symm.trans_le
      ((e.symm.toVecLatHom.monotone h).trans_eq (e.symm.toVecLatHom.map_abs y))
  have hqfactor (i : I) (x : E i) (w : P.generated)
      (hw : (w : P.Carrier) = P.inclusion i x) : q w ≤ ‖x‖ := by
    have hew : e.toLinearEquiv.symm w = A.inclusion i x :=
      e.toLinearEquiv.symm_apply_eq.mpr (Subtype.ext (hw.trans (he i x).symm))
    change p (e.toLinearEquiv.symm w) ≤ ‖x‖
    simpa only [hew] using hfactor i x
  exact (congrArg p (e.toLinearEquiv.symm_apply_apply z)).symm.trans_le
    (compatible_seminorm_le_norm P q hqsolid hqfactor (e z))

/-- The compatible lattice seminorm values are bounded above, and their supremum is the
transported norm. -/
private lemma norm_eq_sSup_seminorms
    (A : VectorLattice.ArchimedeanFreeProduct E) (e : VecLatEquiv A.Carrier P.generated)
    (he : ∀ i x, (e (A.inclusion i x) : P.Carrier) = P.inclusion i x) (z : A.Carrier) :
    let values : Set ℝ := {r | ∃ p : Seminorm ℝ A.Carrier,
      (∀ x y, |x| ≤ |y| → p x ≤ p y) ∧
      (∀ i x, p (A.inclusion i x) ≤ ‖x‖) ∧ r = p z}
    BddAbove values ∧ ‖(e z : P.Carrier)‖ = sSup values := by
  let p := (normSeminorm ℝ P.generated).comp e.toLinearMap
  have hsolid : ∀ x y, |x| ≤ |y| → p x ≤ p y := by
    intro x y h
    apply norm_le_norm_of_abs_le_abs
    exact (e.toVecLatHom.map_abs x).symm.trans_le
      ((e.toVecLatHom.monotone h).trans_eq (e.toVecLatHom.map_abs y))
  have hfactor (i : I) (x : E i) : p (A.inclusion i x) ≤ ‖x‖ :=
    (congrArg norm (he i x)).trans_le ((P.isometry_inclusion i).norm_map_of_map_zero
      (map_zero (P.inclusion i)) x).le
  have hub : ∀ r, (∃ q : Seminorm ℝ A.Carrier,
      (∀ x y, |x| ≤ |y| → q x ≤ q y) ∧
      (∀ i x, q (A.inclusion i x) ≤ ‖x‖) ∧ r = q z) → r ≤ ‖(e z : P.Carrier)‖ := by
    rintro _ ⟨q, hq, hqi, rfl⟩
    exact seminorm_le_of_generated_equiv P A e he q hq hqi z
  exact ⟨⟨_, hub⟩, le_antisymm (le_csSup ⟨_, hub⟩ ⟨p, hsolid, hfactor, rfl⟩)
    (csSup_le ⟨_, p, hsolid, hfactor, rfl⟩ hub)⟩

/-- The Archimedean free product identifies with the generated sublattice,
whose norm is the maximal compatible lattice seminorm and whose completion
is the Banach lattice free product. -/
theorem archimedean_completion
    (A : VectorLattice.ArchimedeanFreeProduct E) :
    ∃ e : VecLatEquiv A.Carrier P.generated,
      (∀ i x, (e (A.inclusion i x) : P.Carrier) = P.inclusion i x) ∧
      DenseRange (fun z : A.Carrier ↦ (e z : P.Carrier)) ∧
      (∀ z : A.Carrier,
        let values : Set ℝ := {r | ∃ p : Seminorm ℝ A.Carrier,
          (∀ x y, |x| ≤ |y| → p x ≤ p y) ∧
          (∀ i x, p (A.inclusion i x) ≤ ‖x‖) ∧ r = p z}
        BddAbove values ∧ ‖(e z : P.Carrier)‖ = sSup values) ∧
      ∃ Φ : BanachLatEquiv (UniformSpace.Completion P.generated) P.Carrier,
        ∀ z : P.generated,
          Φ (z : UniformSpace.Completion P.generated) = (z : P.Carrier) := by
  obtain ⟨e, he⟩ := A.exists_generated_equiv P
  refine ⟨e, he, ?_, norm_eq_sSup_seminorms P A e he, generated_completion P⟩
  exact P.dense_generated.denseRange_val.comp e.toLinearEquiv.surjective.denseRange
    continuous_subtype_val

end Completion

section Majorants

open scoped Pointwise Topology

variable (X : Bool → Type u)
  [∀ b, NormedAddCommGroup (X b)] [∀ b, Lattice (X b)]
  [∀ b, IsOrderedAddMonoid (X b)] [∀ b, BanachLattice (X b)]

/-- A vector lattice expression evaluates to zero when all its inputs are zero. -/
private lemma expression_eval_zero {n : ℕ} (φ : LLexpr n)
    (Y : Type u) [AddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [VectorLattice Y] :
    LLexpr.eval (fun _ : Fin n ↦ (0 : Y)) φ = 0 := by
  induction φ <;> simp_all [LLexpr.eval]

/-- Every element of the generated sublattice is dominated by a sum of positive elements from
the two factors. -/
private lemma exists_positive_majorant (P : FreeProduct X) (z : P.generated) :
    ∃ (a : X false) (b : X true), 0 ≤ a ∧ 0 ≤ b ∧
      |(z : P.Carrier)| ≤ P.inclusion false a + P.inclusion true b := by
  obtain ⟨n, i, x, φ, hz⟩ := P.exists_expression z
  let y : ∀ b, Fin n → X b := fun b j ↦ if h : i j = b then h ▸ x j else 0
  have hy (j : Fin n) : y (i j) j = x j := by simp only [y, dite_eq_left rfl]
  let a (b : Bool) := ∑ j : Fin n, |y b j|
  have ha (b : Bool) : 0 ≤ a b := Finset.sum_nonneg (fun j _ ↦ abs_nonneg (y b j))
  have hsum (b : Bool) (j : Fin n) : |y b j| ≤ a b :=
    Finset.single_le_sum (fun j _ ↦ abs_nonneg (y b j)) (Finset.mem_univ j)
  let H (b : Bool) := (P.inclusion_isVecLatHom b).mk' (P.inclusion b)
  let w := P.inclusion false (a false) + P.inclusion true (a true)
  have hfactor : ∀ b (v : X b), |v| ≤ a b → |P.inclusion b v| ≤ w := Bool.rec
    (fun v hv ↦ ((H false).map_abs v).symm.le.trans
      (((H false).monotone hv).trans (le_add_of_nonneg_right ((H true).map_nonneg (ha true)))))
    (fun v hv ↦ ((H true).map_abs v).symm.le.trans
      (((H true).monotone hv).trans (le_add_of_nonneg_left ((H false).map_nonneg (ha false)))))
  have hvar (j : Fin n) : |P.inclusion (i j) (x j) - (0 : P.Carrier)| ≤ (1 : ℝ) • w := by
    simpa only [sub_zero, one_smul, hy] using hfactor (i j) (y (i j) j) (hsum (i j) j)
  obtain ⟨c, hc, hbound⟩ := exists_expression_error_bound.{u} φ
  have hdom : |(z : P.Carrier)| ≤ c • w := by
    simpa only [← hz, expression_eval_zero, sub_zero, mul_one] using
      hbound P.Carrier (fun j ↦ P.inclusion (i j) (x j)) (fun _ ↦ 0) w 1 hvar
  refine ⟨c • a false, c • a true, smul_nonneg hc (ha false), smul_nonneg hc (ha true), ?_⟩
  simpa only [w, smul_add, map_smul] using hdom

/-- The elements of the generated sublattice dominated by positive factor elements whose norms
sum to at most one. -/
private def majorantBall (P : FreeProduct X) : Set P.generated :=
  {z | ∃ (a : X false) (b : X true), 0 ≤ a ∧ 0 ≤ b ∧ ‖a‖ + ‖b‖ ≤ 1 ∧
    |(z : P.Carrier)| ≤ P.inclusion false a + P.inclusion true b}

/-- A positive factor majorant bounds the free-product norm by the sum of the two factor
norms. -/
lemma norm_le_positive_majorant (P : FreeProduct X) (z : P.Carrier)
    (a : X false) (b : X true) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hz : |z| ≤ P.inclusion false a + P.inclusion true b) : ‖z‖ ≤ ‖a‖ + ‖b‖ := by
  have hpos : 0 ≤ P.inclusion false a + P.inclusion true b :=
    add_nonneg (((P.inclusion_isVecLatHom false).mk' (P.inclusion false)).map_nonneg ha)
      (((P.inclusion_isVecLatHom true).mk' (P.inclusion true)).map_nonneg hb)
  refine (norm_le_norm_of_abs_le_abs (hz.trans_eq (abs_of_nonneg hpos).symm)).trans
    ((norm_add_le _ _).trans ?_)
  simpa only [one_mul] using add_le_add
    ((P.inclusion false).le_of_opNorm_le (P.inclusion_contractive false) a)
    ((P.inclusion true).le_of_opNorm_le (P.inclusion_contractive true) b)

/-- The factor-majorant unit set is balanced under scalar multiplication of absolute value at
most one. -/
private lemma majorantBall_balanced (P : FreeProduct X) : Balanced ℝ (majorantBall X P) := by
  rintro c hc _ ⟨z, ⟨a, b, ha, hb, hab, hz⟩, rfl⟩
  refine ⟨|c| • a, |c| • b, smul_nonneg (abs_nonneg c) ha,
    smul_nonneg (abs_nonneg c) hb, ?_, ?_⟩
  · simpa only [norm_smul, Real.norm_eq_abs, abs_abs, ← mul_add, one_mul] using
      mul_le_mul hc hab (add_nonneg (norm_nonneg a) (norm_nonneg b)) zero_le_one
  · change |c • (z : P.Carrier)| ≤
      P.inclusion false (|c| • a) + P.inclusion true (|c| • b)
    rw [abs_smul', map_smul, map_smul, ← smul_add]
    exact smul_le_smul_of_nonneg_left hz (abs_nonneg c)

/-- The factor-majorant unit set is convex. -/
private lemma majorantBall_convex (P : FreeProduct X) : Convex ℝ (majorantBall X P) := by
  rintro x ⟨ax, bx, hax, hbx, habx, hx⟩ y ⟨ay, by', hay, hby, haby, hy⟩ s t hs ht hst
  refine ⟨s • ax + t • ay, s • bx + t • by',
    add_nonneg (smul_nonneg hs hax) (smul_nonneg ht hay),
    add_nonneg (smul_nonneg hs hbx) (smul_nonneg ht hby), ?_, ?_⟩
  · have ha : ‖s • ax + t • ay‖ ≤ s * ‖ax‖ + t * ‖ay‖ := by
      simpa only [norm_smul, Real.norm_of_nonneg hs, Real.norm_of_nonneg ht] using
        norm_add_le (s • ax) (t • ay)
    have hb : ‖s • bx + t • by'‖ ≤ s * ‖bx‖ + t * ‖by'‖ := by
      simpa only [norm_smul, Real.norm_of_nonneg hs, Real.norm_of_nonneg ht] using
        norm_add_le (s • bx) (t • by')
    nlinarith [mul_le_mul_of_nonneg_left habx hs, mul_le_mul_of_nonneg_left haby ht]
  · change |s • (x : P.Carrier) + t • (y : P.Carrier)| ≤
      P.inclusion false (s • ax + t • ay) + P.inclusion true (s • bx + t • by')
    have h := abs_add_le (s • (x : P.Carrier)) (t • (y : P.Carrier))
    rw [abs_smul', abs_smul', abs_of_nonneg hs, abs_of_nonneg ht] at h
    refine h.trans ((add_le_add (smul_le_smul_of_nonneg_left hx hs)
      (smul_le_smul_of_nonneg_left hy ht)).trans_eq ?_)
    simp only [map_add, map_smul, smul_add]
    abel

/-- Scaling the majorant unit set is equivalent to scaling the allowed sum of the factor
norms. -/
private lemma mem_smul_majorantBall (P : FreeProduct X) (r : ℝ) (hr : 0 < r)
    (z : P.generated) :
    z ∈ r • majorantBall X P ↔
      ∃ (a : X false) (b : X true), 0 ≤ a ∧ 0 ≤ b ∧ ‖a‖ + ‖b‖ ≤ r ∧
        |(z : P.Carrier)| ≤ P.inclusion false a + P.inclusion true b := by
  constructor
  · rintro ⟨v, ⟨a, b, ha, hb, hab, hv⟩, rfl⟩
    refine ⟨r • a, r • b, smul_nonneg hr.le ha, smul_nonneg hr.le hb, ?_, ?_⟩
    · simpa only [norm_smul, Real.norm_of_nonneg hr.le, ← mul_add] using
        mul_le_of_le_one_right hr.le hab
    · change |r • (v : P.Carrier)| ≤ P.inclusion false (r • a) + P.inclusion true (r • b)
      rw [abs_smul', abs_of_nonneg hr.le, map_smul, map_smul, ← smul_add]
      exact smul_le_smul_of_nonneg_left hv hr.le
  · rintro ⟨a, b, ha, hb, hab, hz⟩
    refine ⟨r⁻¹ • z, ⟨r⁻¹ • a, r⁻¹ • b,
      smul_nonneg (inv_nonneg.mpr hr.le) ha, smul_nonneg (inv_nonneg.mpr hr.le) hb,
      ?_, ?_⟩, ?_⟩
    · simpa only [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le), ← mul_add,
        inv_mul_cancel₀ hr.ne'] using mul_le_mul_of_nonneg_left hab (inv_nonneg.mpr hr.le)
    · change |r⁻¹ • (z : P.Carrier)| ≤
        P.inclusion false (r⁻¹ • a) + P.inclusion true (r⁻¹ • b)
      rw [abs_smul', abs_of_nonneg (inv_nonneg.mpr hr.le), map_smul, map_smul, ← smul_add]
      exact smul_le_smul_of_nonneg_left hz (inv_nonneg.mpr hr.le)
    · simp only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]

/-- Every generated element belongs to a sufficiently large scalar multiple of the majorant
unit set. -/
private lemma majorantBall_absorbent (P : FreeProduct X) : Absorbent ℝ (majorantBall X P) := by
  intro z
  obtain ⟨a, b, ha, hb, hz⟩ := exists_positive_majorant X P z
  let r := ‖a‖ + ‖b‖ + 1
  have hr : 0 < r := by positivity
  have hmem : z ∈ r • majorantBall X P := (mem_smul_majorantBall X P r hr z).mpr
    ⟨a, b, ha, hb, le_add_of_nonneg_right zero_le_one, hz⟩
  exact Absorbs.of_norm ⟨r, fun c hc ↦ Set.singleton_subset_iff.mpr
    ((majorantBall_balanced X P).smul_mono
      (by simpa only [Real.norm_of_nonneg hr.le] using hc) hmem)⟩

/-- The gauge of the majorant set is monotone with respect to domination of absolute values. -/
private lemma majorant_gauge_solid (P : FreeProduct X) (z v : P.generated)
    (hzv : |z| ≤ |v|) : gauge (majorantBall X P) z ≤ gauge (majorantBall X P) v := by
  apply le_of_forall_gt
  intro r hr
  obtain ⟨s, hs, hsr, hv⟩ := exists_lt_of_gauge_lt (majorantBall_absorbent X P) hr
  obtain ⟨a, b, ha, hb, hab, hv⟩ := (mem_smul_majorantBall X P s hs v).mp hv
  exact (gauge_le_of_mem hs.le ((mem_smul_majorantBall X P s hs z).mpr
    ⟨a, b, ha, hb, hab,
      (show |(z : P.Carrier)| ≤ |(v : P.Carrier)| from hzv).trans hv⟩)).trans_lt hsr

/-- The free-product norm is bounded above by the gauge of the majorant set. -/
private lemma norm_le_majorant_gauge (P : FreeProduct X) (z : P.generated) :
    ‖(z : P.Carrier)‖ ≤ gauge (majorantBall X P) z := by
  have hB : majorantBall X P ⊆ Metric.closedBall 0 1 := by
    rintro v ⟨a, b, ha, hb, hab, hv⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    change ‖(v : P.Carrier)‖ ≤ 1
    exact (norm_le_positive_majorant X P v a b ha hb hv).trans hab
  change ‖z‖ ≤ gauge (majorantBall X P) z
  exact (div_one ‖z‖).symm.trans_le
    (le_gauge_of_subset_closedBall (majorantBall_absorbent X P) zero_le_one hB)

/-- On each included factor, the majorant gauge is bounded by the original factor norm. -/
private lemma majorant_gauge_factor (P : FreeProduct X) (b : Bool) (x : X b)
    (z : P.generated) (hz : (z : P.Carrier) = P.inclusion b x) :
    gauge (majorantBall X P) z ≤ ‖x‖ := by
  apply le_of_forall_gt
  intro r hr
  obtain ⟨s, hxs, hsr⟩ := exists_between hr
  have hs : 0 < s := lt_of_le_of_lt (norm_nonneg x) hxs
  refine lt_of_le_of_lt (gauge_le_of_mem hs.le ?_) hsr
  apply (mem_smul_majorantBall X P s hs z).mpr
  cases b with
  | false =>
    refine ⟨|x|, 0, abs_nonneg x, le_rfl, ?_, ?_⟩
    · simpa only [norm_abs_eq_norm, norm_zero, add_zero] using hxs.le
    · rw [hz, map_zero, add_zero]
      exact (((P.inclusion_isVecLatHom false).mk' (P.inclusion false)).map_abs x).symm.le
  | true =>
    refine ⟨0, |x|, le_rfl, abs_nonneg x, ?_, ?_⟩
    · simpa only [norm_zero, norm_abs_eq_norm, zero_add] using hxs.le
    · rw [hz, map_zero, zero_add]
      exact (((P.inclusion_isVecLatHom true).mk' (P.inclusion true)).map_abs x).symm.le

/-- The maximality of the free-product norm bounds the majorant gauge from above by that norm. -/
private lemma majorant_gauge_le_norm (P : FreeProduct X) (z : P.generated) :
    gauge (majorantBall X P) z ≤ ‖(z : P.Carrier)‖ := by
  let p := gaugeSeminorm (majorantBall_balanced X P) (majorantBall_convex X P)
    (majorantBall_absorbent X P)
  exact P.seminorm_le_norm p
    (fun v hv ↦ Subtype.ext (norm_eq_zero.mp (le_antisymm
      ((norm_le_majorant_gauge X P v).trans_eq hv) (norm_nonneg _))))
    (majorant_gauge_solid X P) (majorant_gauge_factor X P) z

/-- Every generated element has a positive factor majorant whose total norm is arbitrarily
close to its free-product norm. -/
lemma exists_norm_majorant (P : FreeProduct X) (z : P.generated)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (a : X false) (b : X true), 0 ≤ a ∧ 0 ≤ b ∧
      |(z : P.Carrier)| ≤ P.inclusion false a + P.inclusion true b ∧
      ‖a‖ + ‖b‖ ≤ ‖(z : P.Carrier)‖ + ε := by
  obtain ⟨r, hr, hrs, hz⟩ := exists_lt_of_gauge_lt (majorantBall_absorbent X P)
    ((majorant_gauge_le_norm X P z).trans_lt (lt_add_of_pos_right _ hε))
  exact let ⟨a, b, ha, hb, hab, hz⟩ := (mem_smul_majorantBall X P r hr z).mp hz
    ⟨a, b, ha, hb, hz, hab.trans hrs.le⟩

end Majorants

end BanachLattice.FreeProduct
