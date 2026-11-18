/-
Authors: Gonzalo Martínez-Fernández
-/

import FreeProducts.VectorLattice.Basic
import FreeProducts.VectorLattice.PrimeIdeals
import FreeProducts.VectorLattice.TotalAmalgamation

/-!
# Amalgamation and preservation of embeddings in vector lattices

Prime ideals and totally ordered amalgams show that pushouts preserve injectivity.
Successive pushouts then show that injective factor maps induce injective maps
between arbitrary free products of vector lattices.
-/

universe u

namespace VectorLattice

section Amalgamation

variable {X Y Z : Type u}
  [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X]
  [AddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [VectorLattice Y]
  [AddCommGroup Z] [Lattice Z] [IsOrderedAddMonoid Z] [VectorLattice Z]

/-- An injective lattice homomorphism identifies its domain with its range sublattice. -/
private lemma exists_range_equiv (g : VecLatHom Z Y) (hg : Function.Injective g) :
    ∃ W : VectorSublattice Y, ∃ e : VecLatEquiv Z W, ∀ z, (e z : Y) = g z := by
  let W := g.range
  let e : VecLatEquiv Z W :=
    { LinearEquiv.ofInjective g.toLinearMap hg with
      map_sup' := fun a b ↦ Subtype.ext (g.map_sup' a b)
      map_inf' := fun a b ↦ Subtype.ext (g.map_inf' a b) }
  exact ⟨W, e, fun _ ↦ rfl⟩

/-- A prime ideal extends along an injective lattice homomorphism with exactly the prescribed
inverse image. -/
private lemma prime_extension_map (g : VecLatHom Z Y) (hg : Function.Injective g)
    (P : OrderIdeal Z) (hP : P.IsPrime) :
    ∃ Q : OrderIdeal Y, Q.IsPrime ∧ ∀ z, g z ∈ Q ↔ z ∈ P := by
  obtain ⟨W, e, he⟩ := exists_range_equiv g hg
  obtain ⟨R, hR, hRP⟩ := OrderIdeal.prime_comap e.symm.toVecLatHom P hP
  obtain ⟨Q, hQ, hQR⟩ := OrderIdeal.exists_prime_extension W R hR
  refine ⟨Q, hQ, fun z ↦ ?_⟩
  have hinv : e.symm.toVecLatHom (e z) = z := e.toLinearEquiv.symm_apply_apply z
  simpa only [he z, hinv] using (hQR (e z)).trans (hRP (e z))

/-- A homomorphism whose inverse image of the target ideal equals the source ideal induces an
embedding of the quotients. -/
private lemma quotient_embedding (f : VecLatHom Z X) (J : OrderIdeal Z) (K : OrderIdeal X)
    (h : ∀ z, f z ∈ K ↔ z ∈ J) :
    ∃ F : VecLatHom (Z ⧸ J.toSubmodule) (X ⧸ K.toSubmodule),
      Function.Injective F ∧ ∀ z, F (J.mkQ z) = K.mkQ (f z) := by
  have hker : J.toSubmodule ≤ LinearMap.ker (K.mkQVecLatHom.comp f).toLinearMap :=
    fun z hz ↦ (Submodule.Quotient.mk_eq_zero _).mpr ((h z).mpr hz)
  let F := J.liftQVecLatHom (K.mkQVecLatHom.comp f) hker
  refine ⟨F, ?_, fun _ ↦ rfl⟩
  refine (injective_iff_map_eq_zero F.toLinearMap).mpr (fun z hz ↦ ?_)
  obtain ⟨x, rfl⟩ := J.toSubmodule.mkQ_surjective z
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    ((h x).mp ((Submodule.Quotient.mk_eq_zero K.toSubmodule).mp hz))

/-- A nonzero left-factor element stays nonzero in a pushout when the opposite input map is
injective. -/
private lemma pushout_nonzero {f : VecLatHom Z X} {g : VecLatHom Z Y}
    (P : Pushout f g) (hg : Function.Injective g) {x : X} (hx : x ≠ 0) : P.left x ≠ 0 := by
  obtain ⟨PX, hPX, hxPX⟩ := OrderIdeal.exists_prime_not_mem hx
  obtain ⟨PZ, hPZ, hZ⟩ := OrderIdeal.prime_comap f PX hPX
  obtain ⟨PY, hPY, hY⟩ := prime_extension_map g hg PZ hPZ
  obtain ⟨F, hF, hFq⟩ := quotient_embedding f PZ PX (fun z ↦ (hZ z).symm)
  obtain ⟨G, hG, hGq⟩ := quotient_embedding g PZ PY hY
  let := (OrderIdeal.isTotal_quotient_iff_isPrime PX).mpr hPX
  let := (OrderIdeal.isTotal_quotient_iff_isPrime PY).mpr hPY
  let := (OrderIdeal.isTotal_quotient_iff_isPrime PZ).mpr hPZ
  obtain ⟨A⟩ := nonempty_totalAmalgam F G hF hG
  let a := A.left.comp PX.mkQVecLatHom
  let b := A.right.comp PY.mkQVecLatHom
  have hcomm : a.comp f = b.comp g := DFunLike.ext _ _ (fun z ↦
    (congrArg A.left (hFq z)).symm.trans
      ((DFunLike.congr_fun A.comm (PZ.mkQ z)).trans (congrArg A.right (hGq z))))
  obtain ⟨R, hR, _⟩ := P.universal A.Carrier a b hcomm
  intro heq
  have hzero : A.left (PX.mkQ x) = 0 :=
    (DFunLike.congr_fun hR.1 x).symm.trans ((congrArg R heq).trans (map_zero R))
  exact hxPX ((Submodule.Quotient.mk_eq_zero PX.toSubmodule).mp
    (A.left_injective (hzero.trans (map_zero A.left).symm)))

/-- In a push-out, injectivity of the map into the second factor implies
injectivity of the canonical map from the first factor. -/
theorem Pushout.left_injective
    {f : VecLatHom Z X} {g : VecLatHom Z Y}
    (P : Pushout f g) (hg : Function.Injective g) :
    Function.Injective P.left := by
  exact (injective_iff_map_eq_zero P.left.toLinearMap).mpr
    (fun x hx ↦ Classical.byContradiction (fun hn ↦ pushout_nonzero P hg hn hx))

end Amalgamation

section Embeddings

variable {I : Type u} {E F : I → Type u}
  [∀ i, AddCommGroup (E i)] [∀ i, Lattice (E i)]
  [∀ i, IsOrderedAddMonoid (E i)] [∀ i, VectorLattice (E i)]
  [∀ i, AddCommGroup (F i)] [∀ i, Lattice (F i)]
  [∀ i, IsOrderedAddMonoid (F i)] [∀ i, VectorLattice (F i)]

/-- An embedding of the original free product together with extensions of the factor maps on a
specified finite set of indices. -/
private structure PartialExtension (P : FreeProduct E)
    (T : ∀ i, VecLatHom (E i) (F i)) (s : Finset I) where
  Carrier : Type u
  [addCommGroup : AddCommGroup Carrier]
  [lattice : Lattice Carrier]
  [isOrderedAddMonoid : IsOrderedAddMonoid Carrier]
  [vectorLattice : VectorLattice Carrier]
  embedding : VecLatHom P.Carrier Carrier
  embedding_injective : Function.Injective embedding
  extension : ∀ i, i ∈ s → VecLatHom (F i) Carrier
  comm : ∀ i (hi : i ∈ s) x, embedding (P.inclusion i x) = extension i hi (T i x)

attribute [instance] PartialExtension.addCommGroup PartialExtension.lattice
  PartialExtension.isOrderedAddMonoid PartialExtension.vectorLattice

/-- The factor inclusions generate every element of a vector lattice free product. -/
private lemma mem_generated_inclusions (P : FreeProduct E) (x : P.Carrier) :
    x ∈ VectorSublattice.generated (Set.range (fun z : Σ i, E i ↦ P.inclusion z.1 z.2)) := by
  let G := VectorSublattice.generated (Set.range (fun z : Σ i, E i ↦ P.inclusion z.1 z.2))
  let T : ∀ i, VecLatHom (E i) G := fun i ↦
    { LinearMap.codRestrict G.toSubmodule (P.inclusion i).toLinearMap
        (fun y ↦ VectorSublattice.subset_generated _ ⟨⟨i, y⟩, rfl⟩) with
      map_sup' := fun a b ↦ Subtype.ext ((P.inclusion i).map_sup' a b)
      map_inf' := fun a b ↦ Subtype.ext ((P.inclusion i).map_inf' a b) }
  obtain ⟨U, hU, _⟩ := P.universal G T
  have hcomp : G.subtype.comp U = VecLatHom.id := FreeProduct.hom_ext P
    (fun i y ↦ congrArg (fun z : G ↦ (z : P.Carrier)) (hU i y))
  have hx : (U x : P.Carrier) = x := DFunLike.congr_fun hcomp x
  exact hx ▸ (U x).property

/-- Every free-product element is the value of a finite vector lattice expression in elements
of the factors. -/
private lemma exists_inclusion_expression (P : FreeProduct E) (x : P.Carrier) :
    ∃ (n : ℕ) (a : Fin n → Σ i, E i) (e : LLexpr n),
      LLexpr.eval (fun k ↦ P.inclusion (a k).1 (a k).2) e = x := by
  have hx := mem_generated_inclusions P x
  change x ∈ (VectorSublattice.generated
    (Set.range (fun z : Σ i, E i ↦ P.inclusion z.1 z.2)) : Set P.Carrier) at hx
  rw [LLexpr.generated_eq_iUnion_combinations] at hx
  simp only [Set.mem_iUnion, LLexpr.combinations, Set.mem_range] at hx
  obtain ⟨n, y, e, he⟩ := hx
  choose a ha using fun k : Fin n ↦ (y k).property
  exact ⟨n, a, e, (congrArg (fun v : Fin n → P.Carrier ↦ LLexpr.eval v e)
    (funext ha)).trans he⟩

/-- A pushout enlarges a partial extension to include one additional injective factor map. -/
private lemma partialExtension_insert [DecidableEq I] {P : FreeProduct E}
    {T : ∀ i, VecLatHom (E i) (F i)} {s : Finset I}
    (D : PartialExtension P T s) (i : I) (hi : Function.Injective (T i)) :
    Nonempty (PartialExtension P T (insert i s)) := by
  obtain ⟨A⟩ := nonempty_pushout (D.embedding.comp (P.inclusion i)) (T i)
  let ext : ∀ j, j ∈ insert i s → VecLatHom (F j) A.Carrier := fun j hj ↦
    if h : j = i then
      Eq.mp (congrArg (fun k ↦ VecLatHom (F k) A.Carrier) h.symm) A.right
    else A.left.comp (D.extension j ((Finset.mem_insert.mp hj).resolve_left h))
  refine ⟨{ Carrier := A.Carrier
            embedding := A.left.comp D.embedding
            embedding_injective := (A.left_injective hi).comp D.embedding_injective
            extension := ext
            comm := fun j hj x ↦ ?_ }⟩
  rcases eq_or_ne j i with rfl | h
  · simpa [ext, VecLatHom.comp_apply] using DFunLike.congr_fun A.comm x
  · simpa only [ext, dite_eq_right h, VecLatHom.comp_apply] using
      congrArg A.left (D.comm j ((Finset.mem_insert.mp hj).resolve_left h) x)

/-- Injective factor maps admit a simultaneous partial extension on every finite set of
indices. -/
private lemma nonempty_partialExtension (P : FreeProduct E)
    (T : ∀ i, VecLatHom (E i) (F i)) (hT : ∀ i, Function.Injective (T i)) (s : Finset I) :
    Nonempty (PartialExtension P T s) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨{ Carrier := P.Carrier
             embedding := VecLatHom.id
             embedding_injective := fun _ _ h ↦ h
             extension := fun i hi ↦ False.elim (Finset.notMem_empty i hi)
             comm := fun i hi ↦ False.elim (Finset.notMem_empty i hi) }⟩
  | insert i s _ ih => exact ih.elim (fun D ↦ partialExtension_insert D i (hT i))

/-- The target free product maps into a partial extension, agreeing with the embedded source
factors on the chosen finite set. -/
private lemma finite_extension_map {P : FreeProduct E}
    {T : ∀ i, VecLatHom (E i) (F i)} {s : Finset I}
    (D : PartialExtension P T s) (Q : FreeProduct F) :
    ∃ R : VecLatHom Q.Carrier D.Carrier,
      ∀ i, i ∈ s → ∀ x, R (Q.inclusion i (T i x)) = D.embedding (P.inclusion i x) := by
  classical
  let U : ∀ i, VecLatHom (F i) D.Carrier := fun i ↦
    if hi : i ∈ s then D.extension i hi else VecLatHom.ofAbs 0 (by simp)
  obtain ⟨R, hR, _⟩ := Q.universal D.Carrier U
  exact ⟨R, fun i hi x ↦ (hR i (T i x)).trans
    (by simpa only [U, dite_eq_left hi] using (D.comm i hi x).symm)⟩

/-- The homomorphism between free products induced by a family of
injective homomorphisms is injective. -/
theorem FreeProduct.induced_injective
    (P : FreeProduct E) (Q : FreeProduct F)
    (T : ∀ i, VecLatHom (E i) (F i))
    (hT : ∀ i, Function.Injective (T i))
    (S : VecLatHom P.Carrier Q.Carrier)
    (hS : ∀ i x, S (P.inclusion i x) = Q.inclusion i (T i x)) :
    Function.Injective S := by
  classical
  refine (injective_iff_map_eq_zero S.toLinearMap).mpr (fun x hx ↦ ?_)
  obtain ⟨n, a, e, rfl⟩ := exists_inclusion_expression P x
  let s : Finset I := Finset.univ.image (fun k ↦ (a k).1)
  obtain ⟨D⟩ := nonempty_partialExtension P T hT s
  obtain ⟨R, hR⟩ := finite_extension_map D Q
  have hv (k : Fin n) : (R.comp S) (P.inclusion (a k).1 (a k).2) =
      D.embedding (P.inclusion (a k).1 (a k).2) :=
    (congrArg R (hS (a k).1 (a k).2)).trans
      (hR (a k).1 (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩) (a k).2)
  let v : Fin n → P.Carrier := fun k ↦ P.inclusion (a k).1 (a k).2
  have heval : (R.comp S) (LLexpr.eval v e) = D.embedding (LLexpr.eval v e) :=
    (LLexpr.map_eval (R.comp S) v e).trans
      ((congrArg (fun w : Fin n → D.Carrier ↦ LLexpr.eval w e) (funext hv)).trans
        (LLexpr.map_eval D.embedding v e).symm)
  exact D.embedding_injective (heval.symm.trans
    (((congrArg R hx).trans (map_zero R)).trans (map_zero D.embedding).symm))

end Embeddings

end VectorLattice
