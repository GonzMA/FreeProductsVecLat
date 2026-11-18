/-
Authors: Gonzalo Martínez-Fernández
-/

import FreeProducts.Archimedean.DirectedLimits
import FreeProducts.Consequences.ContinuousFunctionEmbeddings

/-!
# Joins and embeddings of Archimedean free products

Dense unital continuous-function representations give a generated-sublattice model
of binary Archimedean free products on a topological join. This model proves
preservation of embeddings for factors with strong units. Directed approximation
and finite-subfamily reduction extend the result to arbitrary families.
-/

universe u v

namespace VectorLattice

section JoinCharacters

open BanachLattice.FreeProduct

variable {E : ULift.{u} Bool → Type u}
  [∀ i, AddCommGroup (E i)] [∀ i, Lattice (E i)]
  [∀ i, IsOrderedAddMonoid (E i)] [∀ i, VectorLattice (E i)]
  [∀ i, IsVLArchimedean (E i)]
  (K : Bool → Type u) [∀ b, TopologicalSpace (K b)] [∀ b, CompactSpace (K b)]
  [∀ b, Nonempty (K b)] (P : ArchimedeanFreeProduct E)
  (j : ∀ b, VecLatHom (E ⟨b⟩) C(K b, ℝ))
  (hj : ∀ b, Function.Injective (j b)) (hd : ∀ b, DenseRange (j b))
  (e : ∀ b, E ⟨b⟩) (he : ∀ b, j b (e b) = 1)

include hj hd he in
/-- Every scalar character normalized at the sum of the factor units is evaluation at a point
of the join representation. -/
private lemma ArchimedeanFreeProduct.scalar_eq_join_eval
    (S : VecLatHom P.Carrier C(Join (K false) (K true), ℝ))
    (hleft : ∀ x, S (P.inclusion ⟨false⟩ x) = interpolate (K false) (K true) (j false x) 0)
    (hright : ∀ x, S (P.inclusion ⟨true⟩ x) = interpolate (K false) (K true) 0 (j true x))
    (F : VecLatHom P.Carrier ℝ)
    (hunit : F (P.inclusion ⟨false⟩ (e false) + P.inclusion ⟨true⟩ (e true)) = 1) :
    ∃ q, ∀ z, F z = S z q := by
  obtain ⟨x, hx⟩ := exists_weighted_eval_of_dense_unital (j false) (hj false)
    (hd false) (he false) (F.comp (P.inclusion ⟨false⟩))
  obtain ⟨y, hy⟩ := exists_weighted_eval_of_dense_unital (j true) (hj true)
    (hd true) (he true) (F.comp (P.inclusion ⟨true⟩))
  have hpos (b : Bool) : 0 ≤ F (P.inclusion ⟨b⟩ (e b)) :=
    (F.comp (P.inclusion ⟨b⟩)).map_nonneg ((j b).le_of_map_le (hj b)
      (by rw [map_zero, he]; exact fun _ ↦ zero_le_one))
  have hsum : F (P.inclusion ⟨false⟩ (e false)) + F (P.inclusion ⟨true⟩ (e true)) = 1 :=
    ((F.map_add _ _).symm).trans hunit
  let t : Set.Icc (0 : ℝ) 1 :=
    ⟨F (P.inclusion ⟨true⟩ (e true)), hpos true, by linarith [hpos false]⟩
  let q := joinMk (K false) (K true) x y t
  let H : VecLatHom P.Carrier ℝ :=
    { (ContinuousMap.evalCLM ℝ q).toLinearMap.comp S.toLinearMap with
      map_sup' := fun z w ↦ congrArg (fun f : C(Join (K false) (K true), ℝ) ↦ f q)
        (S.map_sup' z w)
      map_inf' := fun z w ↦ congrArg (fun f : C(Join (K false) (K true), ℝ) ↦ f q)
        (S.map_inf' z w) }
  refine ⟨q, fun z ↦ DFunLike.congr_fun (P.scalar_hom_ext (S := F) (T := H) ?_) z⟩
  rintro ⟨b⟩ f
  cases b
  · change F (P.inclusion ⟨false⟩ f) = S (P.inclusion ⟨false⟩ f) q
    rw [hleft]
    change F (P.inclusion ⟨false⟩ f) =
      (1 - F (P.inclusion ⟨true⟩ (e true))) * j false f x +
        F (P.inclusion ⟨true⟩ (e true)) * 0
    have hcoeff : F (P.inclusion ⟨false⟩ (e false)) =
        1 - F (P.inclusion ⟨true⟩ (e true)) := by linarith
    simpa only [VecLatHom.comp_apply, hcoeff, mul_zero, add_zero] using hx f
  · change F (P.inclusion ⟨true⟩ f) = S (P.inclusion ⟨true⟩ f) q
    rw [hright]
    exact (hy f).trans (by simp [q, interpolate_joinMk, t, VecLatHom.comp_apply])

include hj he in
omit [∀ b, Nonempty (K b)] in
/-- The sum of the two included factor units is a strong order unit for the binary Archimedean
free product. -/
private lemma ArchimedeanFreeProduct.join_unit_strongOrderUnit :
    StrongOrderUnit (P.inclusion ⟨false⟩ (e false) + P.inclusion ⟨true⟩ (e true)) := by
  have hu (b : Bool) : StrongOrderUnit (e b) :=
    ⟨(j b).le_of_map_le (hj b) (by rw [map_zero, he]; exact fun _ ↦ zero_le_one),
      fun x ↦ ⟨‖j b x‖, norm_nonneg _, abs_le_norm_smul_of_unital_embedding
        (j b) (hj b) (he b) x⟩⟩
  have hs := P.strongOrderUnit (fun b ↦ e b.down) (fun b ↦ hu b.down)
  rw [Fintype.sum_equiv Equiv.ulift (fun b ↦ P.inclusion b (e b.down))
    (fun b ↦ P.inclusion ⟨b⟩ (e b)) (fun _ ↦ rfl), Fintype.sum_bool, add_comm] at hs
  exact hs

include hj hd he in
/-- The homomorphism realizing the binary Archimedean free product as functions on the join is
injective. -/
private lemma ArchimedeanFreeProduct.join_map_injective
    (S : VecLatHom P.Carrier C(Join (K false) (K true), ℝ))
    (hleft : ∀ x, S (P.inclusion ⟨false⟩ x) = interpolate (K false) (K true) (j false x) 0)
    (hright : ∀ x, S (P.inclusion ⟨true⟩ x) = interpolate (K false) (K true) 0 (j true x)) :
    Function.Injective S := by
  let w := P.inclusion ⟨false⟩ (e false) + P.inclusion ⟨true⟩ (e true)
  have hw := P.join_unit_strongOrderUnit K j hj e he
  have hSw : S w = 1 := by
    rw [map_add, hleft, hright, he, he]
    ext q
    induction q using Quotient.inductionOn with
    | h q =>
      change ((1 - (q.2.2 : ℝ)) * 1 + (q.2.2 : ℝ) * 0) +
        ((1 - (q.2.2 : ℝ)) * 0 + (q.2.2 : ℝ) * 1) = 1
      ring
  let : Nonempty (Join (K false) (K true)) := ⟨joinMk _ _
    (Classical.arbitrary _) (Classical.arbitrary _) ⟨0, le_rfl, zero_le_one⟩⟩
  have hw0 : 0 < w := lt_of_le_of_ne hw.1 (fun h ↦
    one_ne_zero (hSw.symm.trans ((congrArg S h.symm).trans (map_zero S))))
  obtain ⟨L, tL, cL, hL, nL, l, hl, _, hlu⟩ := exists_orderUnit_representation hw hw0
  refine (injective_iff_map_eq_zero S).mpr (fun z hz ↦ hl ?_)
  rw [map_zero]
  apply ContinuousMap.ext
  intro p
  let F : VecLatHom P.Carrier ℝ :=
    { (ContinuousMap.evalCLM ℝ p).toLinearMap.comp l.toLinearMap with
      map_sup' := fun x y ↦ congrArg (fun f : C(L, ℝ) ↦ f p) (l.map_sup' x y)
      map_inf' := fun x y ↦ congrArg (fun f : C(L, ℝ) ↦ f p) (l.map_inf' x y) }
  obtain ⟨q, hq⟩ := P.scalar_eq_join_eval K j hj hd e he S hleft hright F
    (congrArg (fun f : C(L, ℝ) ↦ f p) hlu)
  exact (hq z).trans (congrArg (fun f : C(Join (K false) (K true), ℝ) ↦ f q) hz)

end JoinCharacters

section JoinRepresentation

open BanachLattice.FreeProduct

variable {E : ULift.{u} Bool → Type u}
  [∀ i, AddCommGroup (E i)] [∀ i, Lattice (E i)]
  [∀ i, IsOrderedAddMonoid (E i)] [∀ i, VectorLattice (E i)]
  [∀ i, IsVLArchimedean (E i)]

/-- Dense unital representations of two Archimedean lattices identify their free product
with the sublattice generated by the weighted factor functions on the join. -/
theorem ArchimedeanFreeProduct.exists_join_generated_equiv
    (K : Bool → Type u) [∀ b, TopologicalSpace (K b)] [∀ b, CompactSpace (K b)]
    [∀ b, T2Space (K b)] [∀ b, Nonempty (K b)] (P : ArchimedeanFreeProduct E)
    (j : ∀ b, VecLatHom (E ⟨b⟩) C(K b, ℝ))
    (hj : ∀ b, Function.Injective (j b)) (hd : ∀ b, DenseRange (j b))
    (u : ∀ b, E ⟨b⟩) (hu : ∀ b, j b (u b) = 1) :
    let φ : ∀ i, E i → C(Join (K false) (K true), ℝ) := fun ⟨b⟩ ↦ match b with
      | false => fun x ↦ interpolate (K false) (K true) (j false x) 0
      | true => fun x ↦ interpolate (K false) (K true) 0 (j true x)
    let G := VectorSublattice.generated (Set.range (fun x : Sigma E ↦ φ x.1 x.2))
    ∃ e : VecLatEquiv P.Carrier G, ∀ i x, (e (P.inclusion i x) : C(_, ℝ)) = φ i x := by
  intro φ G
  obtain ⟨B⟩ := BanachLattice.nonempty_freeProduct (fun b ↦ C(K b, ℝ))
  obtain ⟨U, hU, _⟩ := P.universal B.Carrier (fun i ↦
    ((B.inclusion_isVecLatHom i.down).mk' (B.inclusion i.down)).comp (j i.down))
  obtain ⟨r, hr₀, hr₁, _⟩ := BanachLattice.FreeProduct.exists_join_equiv K B
  have hS : ∀ i x, (r.toVecLatHom.comp U) (P.inclusion i x) = φ i x := fun
    | ⟨false⟩, x => (congrArg r (hU ⟨false⟩ x)).trans (hr₀ (j false x))
    | ⟨true⟩, x => (congrArg r (hU ⟨true⟩ x)).trans (hr₁ (j true x))
  obtain ⟨e, he⟩ := P.equiv_generated_of_injective φ (r.toVecLatHom.comp U) hS
    (P.join_map_injective K j hj hd u hu (r.toVecLatHom.comp U) (hS ⟨false⟩) (hS ⟨true⟩))
  exact ⟨e, fun i x ↦ (he (P.inclusion i x)).trans (hS i x)⟩

end JoinRepresentation

section BinaryFreeProducts

open BanachLattice.FreeProduct

variable {E : ULift.{u} Bool → Type u}
  [∀ i, AddCommGroup (E i)] [∀ i, Lattice (E i)]
  [∀ i, IsOrderedAddMonoid (E i)] [∀ i, VectorLattice (E i)]
  [∀ i, IsVLArchimedean (E i)]
  (K : Bool → Type u) [∀ b, TopologicalSpace (K b)] [∀ b, CompactSpace (K b)]
  [∀ b, Nonempty (K b)] (P : ArchimedeanFreeProduct E)
  (j : ∀ b, VecLatHom (E ⟨b⟩) C(K b, ℝ))
  (hj : ∀ b, Function.Injective (j b)) (hd : ∀ b, DenseRange (j b))
  (e : ∀ b, E ⟨b⟩) (he : ∀ b, j b (e b) = 1)

include hj hd he in
/-- The binary Archimedean free product embeds in the Banach free product of the
continuous-function representations of its factors. -/
lemma ArchimedeanFreeProduct.completion_map_injective [∀ b, T2Space (K b)]
    (B : BanachLattice.FreeProduct (fun b ↦ C(K b, ℝ)))
    (U : VecLatHom P.Carrier B.Carrier)
    (hU : ∀ b x, U (P.inclusion ⟨b⟩ x) = B.inclusion b (j b x)) :
    Function.Injective U := by
  obtain ⟨r, hr₀, hr₁, _⟩ := BanachLattice.FreeProduct.exists_join_equiv K B
  exact Function.Injective.of_comp (f := r.toVecLatHom)
    (P.join_map_injective K j hj hd e he (r.toVecLatHom.comp U)
      (fun x ↦ (congrArg r (hU false x)).trans (hr₀ (j false x)))
      (fun x ↦ (congrArg r (hU true x)).trans (hr₁ (j true x))))

include hj hd he in
/-- Continuous-function representations reduce injectivity of the binary induced Archimedean
map to injectivity for Banach free products. -/
private lemma ArchimedeanFreeProduct.induced_injective_of_representations
    [∀ b, T2Space (K b)]
    {F : ULift.{u} Bool → Type u}
    [∀ i, AddCommGroup (F i)] [∀ i, Lattice (F i)]
    [∀ i, IsOrderedAddMonoid (F i)] [∀ i, VectorLattice (F i)]
    [∀ i, IsVLArchimedean (F i)]
    (L : Bool → Type u) [∀ b, TopologicalSpace (L b)] [∀ b, CompactSpace (L b)]
    (Q : ArchimedeanFreeProduct F) (k : ∀ b, VecLatHom (F ⟨b⟩) C(L b, ℝ))
    (hk : ∀ b, Function.Injective (k b))
    (T : ∀ i, VecLatHom (E i) (F i)) (hT : ∀ i, Function.Injective (T i))
    (S : VecLatHom P.Carrier Q.Carrier)
    (hS : ∀ i x, S (P.inclusion i x) = Q.inclusion i (T i x)) :
    Function.Injective S := by
  obtain ⟨B⟩ := BanachLattice.nonempty_freeProduct (fun b ↦ C(K b, ℝ))
  obtain ⟨C⟩ := BanachLattice.nonempty_freeProduct (fun b ↦ C(L b, ℝ))
  obtain ⟨U, hU, _⟩ := P.universal B.Carrier (fun i ↦
    ((B.inclusion_isVecLatHom i.down).mk' (B.inclusion i.down)).comp (j i.down))
  obtain ⟨V, hV, _⟩ := Q.universal C.Carrier (fun i ↦
    ((C.inclusion_isVecLatHom i.down).mk' (C.inclusion i.down)).comp (k i.down))
  choose J hJ hJi hJx using fun b ↦ exists_injective_orderUnit_extension
    (j b) (hj b) (hd b) (he b) ((k b).comp (T ⟨b⟩)) ((hk b).comp (hT ⟨b⟩))
  let Rb (b : Bool) := (C.inclusion b).comp (J b)
  have hRb (b : Bool) : IsVecLatHom (Rb b) :=
    (((C.inclusion_isVecLatHom b).mk' (C.inclusion b)).comp ((hJ b).mk' (J b))).isVecLatHom
  obtain ⟨R, ⟨hR, hRx, _⟩, _⟩ := B.exists_unique_extension C.Carrier Rb hRb
    (max ‖Rb false‖ ‖Rb true‖) ((norm_nonneg (Rb false)).trans (le_max_left _ _))
    (fun b ↦ by
      cases b
      · exact le_max_left _ _
      · exact le_max_right _ _)
  have hRi := BanachLattice.FreeProduct.induced_injective_of_continuousFunctions
    K (fun b ↦ C(L b, ℝ)) B C J hJ hJi R hR hRx
  have hUi := P.completion_map_injective K j hj hd e he B U (fun b ↦ hU ⟨b⟩)
  have hcomp : V.comp S = (hR.mk' R).comp U := by
    apply P.hom_ext
    rintro ⟨b⟩ x
    change V (S (P.inclusion ⟨b⟩ x)) = R (U (P.inclusion ⟨b⟩ x))
    rw [hS, hV, hU]
    change C.inclusion b (k b (T ⟨b⟩ x)) = R (B.inclusion b (j b x))
    rw [hRx]
    exact congrArg (C.inclusion b) (hJx b x).symm
  exact Function.Injective.of_comp (f := V) (fun x y h ↦ hUi (hRi
    ((DFunLike.congr_fun hcomp x).symm.trans (h.trans (DFunLike.congr_fun hcomp y)))))

end BinaryFreeProducts

section BinaryEmbeddings

variable {E F : ULift.{u} Bool → Type u}
  [∀ i, AddCommGroup (E i)] [∀ i, Lattice (E i)]
  [∀ i, IsOrderedAddMonoid (E i)] [∀ i, VectorLattice (E i)]
  [∀ i, IsVLArchimedean (E i)]
  [∀ i, AddCommGroup (F i)] [∀ i, Lattice (F i)]
  [∀ i, IsOrderedAddMonoid (F i)] [∀ i, VectorLattice (F i)]
  [∀ i, IsVLArchimedean (F i)]

/-- The induced map is injective when only one of the two source factors can be nonzero. -/
private lemma ArchimedeanFreeProduct.induced_injective_of_one_factor
    (P : ArchimedeanFreeProduct E) (Q : ArchimedeanFreeProduct F)
    (T : ∀ i, VecLatHom (E i) (F i)) (hT : ∀ i, Function.Injective (T i))
    (S : VecLatHom P.Carrier Q.Carrier)
    (hS : ∀ i x, S (P.inclusion i x) = Q.inclusion i (T i x))
    (i : ULift.{u} Bool) (hi : ∀ j, j ≠ i → Subsingleton (E j)) :
    Function.Injective S := by
  intro x y hxy
  obtain ⟨x, rfl⟩ := P.inclusion_surjective_of_subsingleton i hi x
  obtain ⟨y, rfl⟩ := P.inclusion_surjective_of_subsingleton i hi y
  exact congrArg (P.inclusion i) (hT i ((Q.inclusion_injective i)
    ((hS i x).symm.trans (hxy.trans (hS i y)))))

/-- Embeddings between two pairs of lattices with positive strong units induce an embedding of
their Archimedean free products. -/
private lemma ArchimedeanFreeProduct.induced_injective_of_pos_strongOrderUnits
    (P : ArchimedeanFreeProduct E) (Q : ArchimedeanFreeProduct F)
    (e : ∀ i, E i) (he : ∀ i, StrongOrderUnit (e i)) (he0 : ∀ i, 0 < e i)
    (f : ∀ i, F i) (hf : ∀ i, StrongOrderUnit (f i)) (hf0 : ∀ i, 0 < f i)
    (T : ∀ i, VecLatHom (E i) (F i)) (hT : ∀ i, Function.Injective (T i))
    (S : VecLatHom P.Carrier Q.Carrier)
    (hS : ∀ i x, S (P.inclusion i x) = Q.inclusion i (T i x)) :
    Function.Injective S := by
  choose K tK cK hK nK j hj hd hje using fun b : Bool ↦
    exists_orderUnit_representation (he ⟨b⟩) (he0 ⟨b⟩)
  choose L tL cL hL nL k hk _ _ using fun b : Bool ↦
    exists_orderUnit_representation (hf ⟨b⟩) (hf0 ⟨b⟩)
  exact P.induced_injective_of_representations K j hj hd (fun b ↦ e ⟨b⟩) hje
    L Q k hk T hT S hS

/-- The binary embedding result for lattices with strong units also covers zero factors. -/
private lemma ArchimedeanFreeProduct.induced_injective_of_strongOrderUnits
    (P : ArchimedeanFreeProduct E) (Q : ArchimedeanFreeProduct F)
    (hE : ∀ i, ∃ e : E i, StrongOrderUnit e) (hF : ∀ i, ∃ f : F i, StrongOrderUnit f)
    (T : ∀ i, VecLatHom (E i) (F i)) (hT : ∀ i, Function.Injective (T i))
    (S : VecLatHom P.Carrier Q.Carrier)
    (hS : ∀ i x, S (P.inclusion i x) = Q.inclusion i (T i x)) :
    Function.Injective S := by
  by_cases h₀ : Nontrivial (E ⟨false⟩)
  · let := h₀
    by_cases h₁ : Nontrivial (E ⟨true⟩)
    · let := h₁
      have (i : ULift.{u} Bool) : Nontrivial (E i) := by
        rcases i with ⟨_ | _⟩ <;> infer_instance
      have (i : ULift.{u} Bool) : Nontrivial (F i) := (hT i).nontrivial
      choose e he using hE
      choose f hf using hF
      exact P.induced_injective_of_pos_strongOrderUnits Q e he
        (fun i ↦ strongOrderUnit_pos (he i)) f hf (fun i ↦ strongOrderUnit_pos (hf i)) T hT S hS
    · apply P.induced_injective_of_one_factor Q T hT S hS ⟨false⟩
      rintro ⟨_ | _⟩ h
      · exact (h rfl).elim
      · exact not_nontrivial_iff_subsingleton.mp h₁
  · apply P.induced_injective_of_one_factor Q T hT S hS ⟨true⟩
    rintro ⟨_ | _⟩ h
    · exact not_nontrivial_iff_subsingleton.mp h₀
    · exact (h rfl).elim

/-- Free products of the finitely generated factor sublattices embed in and exhaust the binary
Archimedean free product. -/
lemma ArchimedeanFreeProduct.exists_finite_stage_maps
    (P : ArchimedeanFreeProduct E)
    (B : ∀ d : ∀ i, Finset (E i),
      ArchimedeanFreeProduct (fun i ↦ VectorSublattice.generated (d i : Set (E i)))) :
    ∃ U : ∀ d, VecLatHom (B d).Carrier P.Carrier,
      (∀ d i x, U d ((B d).inclusion i x) = P.inclusion i x) ∧
      (∀ d, Function.Injective (U d)) ∧ ∀ z, ∃ d x, U d x = z := by
  classical
  let A (d : ∀ i, Finset (E i)) (i) := VectorSublattice.generated (d i : Set (E i))
  have hA : Monotone A := fun a b h i ↦ VectorSublattice.generated_le
    (fun _ hx ↦ VectorSublattice.subset_generated (b i : Set (E i)) (h i hx))
  have hc (i) (x : E i) : ∃ d, x ∈ A d i := by
    refine ⟨Function.update (fun _ ↦ ∅) i {x}, ?_⟩
    apply VectorSublattice.subset_generated
    simp
  obtain ⟨f, hdir, hfi⟩ := ArchimedeanFreeProduct.exists_directed_transitions A hA B
  let := hdir
  apply P.exists_directed_stage_maps A hA hc B f ?_ hfi
  intro a b h
  exact (B a).induced_injective_of_strongOrderUnits (B b)
    (fun i ↦ exists_strongOrderUnit_generated_finset (a i))
    (fun i ↦ exists_strongOrderUnit_generated_finset (b i))
    (fun i ↦ VectorSublattice.inclusion (hA h i))
    (fun i ↦ VectorSublattice.inclusion_injective (hA h i)) (f a b h) (hfi a b h)

/-- Injective maps between two arbitrary pairs of Archimedean lattices induce an injective
free-product map. -/
private lemma ArchimedeanFreeProduct.induced_injective_binary
    (P : ArchimedeanFreeProduct E) (Q : ArchimedeanFreeProduct F)
    (T : ∀ i, VecLatHom (E i) (F i)) (hT : ∀ i, Function.Injective (T i))
    (S : VecLatHom P.Carrier Q.Carrier)
    (hS : ∀ i x, S (P.inclusion i x) = Q.inclusion i (T i x)) :
    Function.Injective S := by
  classical
  let B (d : ∀ i, Finset (E i)) :=
    (nonempty_archimedeanFreeProduct (fun i ↦ VectorSublattice.generated (d i : Set (E i)))).some
  let C (d : ∀ i, Finset (F i)) :=
    (nonempty_archimedeanFreeProduct (fun i ↦ VectorSublattice.generated (d i : Set (F i)))).some
  obtain ⟨U, hU, hUi, hUc⟩ := P.exists_finite_stage_maps B
  obtain ⟨V, hV, hVi, _⟩ := Q.exists_finite_stage_maps C
  refine (injective_iff_map_eq_zero S).mpr (fun z hz ↦ ?_)
  obtain ⟨d, x, rfl⟩ := hUc z
  let t (i) := (d i).image (T i)
  have hmem (i) (x : VectorSublattice.generated (d i : Set (E i))) :
      T i x ∈ VectorSublattice.generated (t i : Set (F i)) :=
    map_mem_generated (T i) (d i : Set (E i)) (t i : Set (F i))
      (fun y hy ↦ Finset.mem_image.mpr ⟨y, hy, rfl⟩) x x.property
  let T' (i) : VecLatHom (VectorSublattice.generated (d i : Set (E i)))
      (VectorSublattice.generated (t i : Set (F i))) :=
    { toFun := fun x ↦ ⟨T i x, hmem i x⟩
      map_add' := fun x y ↦ Subtype.ext (map_add (T i) x.val y.val)
      map_smul' := fun r x ↦ Subtype.ext (map_smul (T i) r x.val)
      map_sup' := fun x y ↦ Subtype.ext (map_sup (T i) x.val y.val)
      map_inf' := fun x y ↦ Subtype.ext (map_inf (T i) x.val y.val) }
  obtain ⟨W, hW, _⟩ := (B d).universal (C t).Carrier
    (fun i ↦ ((C t).inclusion i).comp (T' i))
  have hWi := (B d).induced_injective_of_strongOrderUnits (C t)
    (fun i ↦ exists_strongOrderUnit_generated_finset (d i))
    (fun i ↦ exists_strongOrderUnit_generated_finset (t i)) T'
    (fun i _ _ h ↦ Subtype.ext (hT i (congrArg Subtype.val h))) W hW
  have hcomm : S.comp (U d) = (V t).comp W := by
    apply (B d).hom_ext
    intro i y
    change S (U d ((B d).inclusion i y)) = V t (W ((B d).inclusion i y))
    rw [hU, hS, hW]
    exact (hV t i (T' i y)).symm
  have hx : W x = 0 := hVi t ((DFunLike.congr_fun hcomm x).symm.trans
    (hz.trans (map_zero (V t)).symm))
  rw [show x = 0 from hWi (hx.trans (map_zero W).symm), map_zero]

end BinaryEmbeddings

/-- Encodes a pair of lattices as a two-element family in the chosen universe. -/
def binaryFamily (X Y : Type u) (i : ULift.{u} Bool) : Type u := Bool.rec X Y i.down

/-- The selected factor supplies the additive group structure of the binary family. -/
private instance binaryAddCommGroup {X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
    (i : ULift.{u} Bool) : AddCommGroup (binaryFamily X Y i) :=
  match i with
  | ⟨false⟩ => inferInstanceAs (AddCommGroup X)
  | ⟨true⟩ => inferInstanceAs (AddCommGroup Y)

/-- The selected factor supplies the lattice structure of the binary family. -/
private instance binaryLattice {X Y : Type u} [Lattice X] [Lattice Y]
    (i : ULift.{u} Bool) : Lattice (binaryFamily X Y i) :=
  match i with
  | ⟨false⟩ => inferInstanceAs (Lattice X)
  | ⟨true⟩ => inferInstanceAs (Lattice Y)

/-- The binary family inherits compatibility of addition with order from its factors. -/
private instance binaryOrderedAddMonoid {X Y : Type u} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [AddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    (i : ULift.{u} Bool) : IsOrderedAddMonoid (binaryFamily X Y i) :=
  match i with
  | ⟨false⟩ => inferInstanceAs (IsOrderedAddMonoid X)
  | ⟨true⟩ => inferInstanceAs (IsOrderedAddMonoid Y)

/-- The binary family inherits the vector lattice structure of its factors. -/
private instance binaryVectorLattice {X Y : Type u} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] [AddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] [VectorLattice Y]
    (i : ULift.{u} Bool) : VectorLattice (binaryFamily X Y i) :=
  match i with
  | ⟨false⟩ => inferInstanceAs (VectorLattice X)
  | ⟨true⟩ => inferInstanceAs (VectorLattice Y)

/-- The binary family inherits the Archimedean property of its factors. -/
private instance binaryArchimedean {X Y : Type u} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] [IsVLArchimedean X]
    [AddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [VectorLattice Y] [IsVLArchimedean Y]
    (i : ULift.{u} Bool) : IsVLArchimedean (binaryFamily X Y i) :=
  match i with
  | ⟨false⟩ => inferInstanceAs (IsVLArchimedean X)
  | ⟨true⟩ => inferInstanceAs (IsVLArchimedean Y)

section FreeProducts

variable {I : Type u} {E F : I → Type u}
  [∀ i, AddCommGroup (E i)] [∀ i, Lattice (E i)]
  [∀ i, IsOrderedAddMonoid (E i)] [∀ i, VectorLattice (E i)]
  [∀ i, IsVLArchimedean (E i)]
  [∀ i, AddCommGroup (F i)] [∀ i, Lattice (F i)]
  [∀ i, IsOrderedAddMonoid (F i)] [∀ i, VectorLattice (F i)]
  [∀ i, IsVLArchimedean (F i)]

/-- Includes each original factor into the binary product that groups one factor against all
the others. -/
noncomputable def splitInclusion (i : I)
    (R : ArchimedeanFreeProduct (fun j : {j : I // j ≠ i} ↦ E j.val))
    (B : ArchimedeanFreeProduct (binaryFamily (E i) R.Carrier)) (j : I) :
    VecLatHom (E j) B.Carrier := by
  classical
  exact if h : j = i then h ▸ B.inclusion ⟨false⟩
    else (B.inclusion ⟨true⟩).comp (R.inclusion ⟨j, h⟩)

/-- Regrouping one factor and the complementary free product produces an Archimedean free
product of the original family. -/
noncomputable def splitProduct (i : I)
    (R : ArchimedeanFreeProduct (fun j : {j : I // j ≠ i} ↦ E j.val))
    (B : ArchimedeanFreeProduct (binaryFamily (E i) R.Carrier)) :
    ArchimedeanFreeProduct E where
  Carrier := B.Carrier
  inclusion := splitInclusion i R B
  universal := by
    classical
    intro Y _ _ _ _ _ T
    obtain ⟨U, hU, _⟩ := R.universal Y (fun j ↦ T j.val)
    let Tb : ∀ b, VecLatHom (binaryFamily (E i) R.Carrier b) Y := fun
      | ⟨false⟩ => T i
      | ⟨true⟩ => U
    obtain ⟨S, hS, huniq⟩ := B.universal Y Tb
    refine ⟨S, ?_, ?_⟩
    · intro j x
      by_cases hji : j = i
      · subst j
        rw [splitInclusion, dite_eq_left rfl]
        exact hS ⟨false⟩ x
      · rw [splitInclusion, dite_eq_right hji]
        exact (hS ⟨true⟩ (R.inclusion ⟨j, hji⟩ x)).trans (hU ⟨j, hji⟩ x)
    · intro V hV
      apply huniq V
      rintro ⟨_ | _⟩ x
      · have h := hV i x
        rw [splitInclusion, dite_eq_left rfl] at h
        exact h
      · have hVU : V.comp (B.inclusion ⟨true⟩) = U := by
          apply R.hom_ext
          intro j y
          rw [hU]
          have h := hV j.val y
          rw [splitInclusion, dite_eq_right j.property] at h
          exact h
        exact DFunLike.congr_fun hVU x

/-- Injectivity for the complementary subfamily and the binary case imply injectivity after
adjoining the remaining factor. -/
private lemma ArchimedeanFreeProduct.induced_injective_of_complement
    (P : ArchimedeanFreeProduct E) (Q : ArchimedeanFreeProduct F)
    (T : ∀ i, VecLatHom (E i) (F i)) (hT : ∀ i, Function.Injective (T i))
    (S : VecLatHom P.Carrier Q.Carrier)
    (hS : ∀ i x, S (P.inclusion i x) = Q.inclusion i (T i x)) (i : I)
    (R : ArchimedeanFreeProduct (fun j : {j : I // j ≠ i} ↦ E j.val))
    (R' : ArchimedeanFreeProduct (fun j : {j : I // j ≠ i} ↦ F j.val))
    (W : VecLatHom R.Carrier R'.Carrier) (hWi : Function.Injective W)
    (hW : ∀ j x, W (R.inclusion j x) = R'.inclusion j (T j.val x)) :
    Function.Injective S := by
  classical
  obtain ⟨B⟩ := nonempty_archimedeanFreeProduct (binaryFamily (E i) R.Carrier)
  obtain ⟨C⟩ := nonempty_archimedeanFreeProduct (binaryFamily (F i) R'.Carrier)
  obtain ⟨p, hp, _⟩ := P.exists_unique_equiv (splitProduct i R B)
  obtain ⟨q, hq, _⟩ := Q.exists_unique_equiv (splitProduct i R' C)
  let Tb : ∀ b, VecLatHom (binaryFamily (E i) R.Carrier b)
      (binaryFamily (F i) R'.Carrier b) := fun
    | ⟨false⟩ => T i
    | ⟨true⟩ => W
  obtain ⟨M, hM, _⟩ := B.universal C.Carrier (fun b ↦ (C.inclusion b).comp (Tb b))
  have hMi : Function.Injective M := B.induced_injective_binary C Tb
    (fun b ↦ by
      rcases b with ⟨_ | _⟩
      · exact hT i
      · exact hWi) M hM
  have hcomm : q.toVecLatHom.comp S = M.comp p.toVecLatHom := by
    apply P.hom_ext
    intro j x
    change q (S (P.inclusion j x)) = M (p (P.inclusion j x))
    rw [hS, hq, hp]
    change splitInclusion i R' C j (T j x) = M (splitInclusion i R B j x)
    by_cases hji : j = i
    · subst j
      rw [splitInclusion, splitInclusion, dite_eq_left rfl, dite_eq_left rfl]
      exact (hM ⟨false⟩ x).symm
    · rw [splitInclusion, splitInclusion, dite_eq_right hji, dite_eq_right hji]
      change C.inclusion ⟨true⟩ (R'.inclusion ⟨j, hji⟩ (T j x)) =
        M (B.inclusion ⟨true⟩ (R.inclusion ⟨j, hji⟩ x))
      exact (congrArg (C.inclusion ⟨true⟩) (hW ⟨j, hji⟩ x).symm).trans
        (hM ⟨true⟩ (R.inclusion ⟨j, hji⟩ x)).symm
  exact fun x y h ↦ p.toLinearEquiv.injective (hMi
    ((DFunLike.congr_fun hcomm x).symm.trans ((congrArg q h).trans
      (DFunLike.congr_fun hcomm y))))

/-- Embeddings of a finite family of Archimedean lattices induce an embedding of their free
products. -/
private lemma ArchimedeanFreeProduct.induced_injective_finite [Finite I]
    (P : ArchimedeanFreeProduct E) (Q : ArchimedeanFreeProduct F)
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
      obtain ⟨R'⟩ := nonempty_archimedeanFreeProduct (fun j : {j : I // j ≠ i} ↦ F j.val)
      obtain ⟨W, hW, _⟩ := R.universal R'.Carrier
        (fun j ↦ (R'.inclusion j).comp (T j.val))
      apply P.induced_injective_of_complement Q T hT S hS i R R' W ?_ hW
      let := Fintype.ofFinite I
      exact ih _ (by
        rw [← hn, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
        exact Fintype.card_subtype_lt (fun h ↦ h rfl))
        R R' (fun j ↦ T j.val) (fun j ↦ hT j.val) W hW rfl

/-- The induced map is injective on the image of every finite subproduct. -/
private lemma ArchimedeanFreeProduct.induced_injective_on_finite_subfamily
    (P : ArchimedeanFreeProduct E) (Q : ArchimedeanFreeProduct F)
    (T : ∀ i, VecLatHom (E i) (F i)) (hT : ∀ i, Function.Injective (T i))
    (S : VecLatHom P.Carrier Q.Carrier)
    (hS : ∀ i x, S (P.inclusion i x) = Q.inclusion i (T i x))
    (s : Finset I) (R : ArchimedeanFreeProduct (fun i : s ↦ E i.val))
    (U : VecLatHom R.Carrier P.Carrier)
    (hU : ∀ i x, U (R.inclusion i x) = P.inclusion i.val x) :
    Function.Injective (S.comp U) := by
  classical
  obtain ⟨R'⟩ := nonempty_archimedeanFreeProduct (fun i : s ↦ F i.val)
  obtain ⟨W, hW, _⟩ := R.universal R'.Carrier
    (fun i ↦ (R'.inclusion i).comp (T i.val))
  have hWi := R.induced_injective_finite R' (fun i ↦ T i.val) (fun i ↦ hT i.val) W hW
  let Tr (i : I) : VecLatHom (F i) R'.Carrier :=
    if h : i ∈ s then R'.inclusion ⟨i, h⟩ else VecLatHom.ofAbs 0 (by simp)
  obtain ⟨V, hV, _⟩ := Q.universal R'.Carrier Tr
  have hcomm : V.comp (S.comp U) = W := by
    apply R.hom_ext
    intro i x
    change V (S (U (R.inclusion i x))) = W (R.inclusion i x)
    rw [hU, hS, hV, hW]
    dsimp only [Tr]
    rw [dite_eq_left i.property]
    rfl
  exact fun x y h ↦ hWi ((DFunLike.congr_fun hcomm x).symm.trans
    ((congrArg V h).trans (DFunLike.congr_fun hcomm y)))

/-- Injective homomorphisms between factors induce an injective
homomorphism between their Archimedean free products. -/
theorem ArchimedeanFreeProduct.induced_injective
    (P : ArchimedeanFreeProduct E) (Q : ArchimedeanFreeProduct F)
    (T : ∀ i, VecLatHom (E i) (F i))
    (hT : ∀ i, Function.Injective (T i))
    (S : VecLatHom P.Carrier Q.Carrier)
    (hS : ∀ i x, S (P.inclusion i x) = Q.inclusion i (T i x)) :
    Function.Injective S := by
  refine (injective_iff_map_eq_zero S).mpr (fun z hz ↦ ?_)
  obtain ⟨s, R, U, hU, x, rfl⟩ := P.exists_finite_subfamily_lift z
  have hx : x = 0 := P.induced_injective_on_finite_subfamily Q T hT S hS s R U hU
    (hz.trans (map_zero (S.comp U)).symm)
  rw [hx, map_zero]

end FreeProducts

end VectorLattice
