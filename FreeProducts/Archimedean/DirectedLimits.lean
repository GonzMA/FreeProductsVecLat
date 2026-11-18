/-
Authors: Gonzalo Martínez-Fernández
-/

import FreeProducts.Archimedean.Basic
import Mathlib.Algebra.Colimit.DirectLimit

/-!
# Directed limits of Archimedean vector lattices

Directed limits along embeddings preserve the Archimedean property. Compatible
homomorphisms on directed covers glue uniquely, and directed systems of factor
sublattices reconstruct their free product when the stage transition maps are injective.
-/

universe u v

namespace VectorLattice

section DirectedUnions

variable {D : Type u} [Preorder D] [IsDirectedOrder D]
  {G : D → Type u} [∀ i, AddCommGroup (G i)] [∀ i, Lattice (G i)]
  [∀ i, IsOrderedAddMonoid (G i)] [∀ i, VectorLattice (G i)]
  (f : ∀ i j, i ≤ j → VecLatHom (G i) (G j)) [DirectedSystem G (f · · ·)]

/-- Defines suprema in the direct limit by moving representatives to a common stage. -/
private noncomputable instance directLimitMax : Max (DirectLimit G f) :=
  ⟨DirectLimit.map₂ f f f (fun _ ↦ (· ⊔ ·)) (fun _ _ _ ↦ map_sup _)⟩

/-- Defines infima in the direct limit by moving representatives to a common stage. -/
private noncomputable instance directLimitMin : Min (DirectLimit G f) :=
  ⟨DirectLimit.map₂ f f f (fun _ ↦ (· ⊓ ·)) (fun _ _ _ ↦ map_inf _)⟩

/-- The direct-limit inclusion preserves the supremum of two elements from the same stage. -/
private lemma directLimit_sup (i : D) (x y : G i) :
    (⟦⟨i, x⟩⟧ : DirectLimit G f) ⊔ ⟦⟨i, y⟩⟧ = ⟦⟨i, x ⊔ y⟩⟧ :=
  DirectLimit.map₂_def ..

/-- The direct-limit inclusion preserves the infimum of two elements from the same stage. -/
private lemma directLimit_inf (i : D) (x y : G i) :
    (⟦⟨i, x⟩⟧ : DirectLimit G f) ⊓ ⟦⟨i, y⟩⟧ = ⟦⟨i, x ⊓ y⟩⟧ :=
  DirectLimit.map₂_def ..

/-- The operations induced from the stages make the direct limit a lattice. -/
private noncomputable instance directLimitLattice : Lattice (DirectLimit G f) :=
  Lattice.mk'
    (DirectLimit.induction₂ f (fun _ _ _ ↦ by simp only [directLimit_sup, sup_comm]))
    (DirectLimit.induction₃ f (fun _ _ _ _ ↦ by simp only [directLimit_sup, sup_assoc]))
    (DirectLimit.induction₂ f (fun _ _ _ ↦ by simp only [directLimit_inf, inf_comm]))
    (DirectLimit.induction₃ f (fun _ _ _ _ ↦ by simp only [directLimit_inf, inf_assoc]))
    (DirectLimit.induction₂ f (fun _ _ _ ↦ by simp only [directLimit_sup, directLimit_inf,
      sup_inf_self]))
    (DirectLimit.induction₂ f (fun _ _ _ ↦ by simp only [directLimit_sup, directLimit_inf,
      inf_sup_self]))

variable [Nonempty D]

/-- Addition is compatible with the order induced on the direct limit. -/
private noncomputable instance directLimitOrderedAddMonoid :
    IsOrderedAddMonoid (DirectLimit G f) where
  add_le_add_left a b hab c := by
    have h (a b c : DirectLimit G f) : (a + c) ⊔ (b + c) = (a ⊔ b) + c := by
      induction a, b, c using DirectLimit.induction₃ f with
      | ih i a b c => simp only [DirectLimit.add_def, directLimit_sup, sup_add]
    exact sup_eq_right.mp ((h a b c).trans (congrArg (· + c) (sup_eq_right.mpr hab)))

/-- The direct limit inherits the real vector lattice structure of its stages. -/
private noncomputable instance directLimitVectorLattice : VectorLattice (DirectLimit G f) where
  smul_le_smul_of_nonneg_left := by
    intro r hr a b hab
    have h (a b : DirectLimit G f) : (r • a) ⊔ (r • b) = r • (a ⊔ b) := by
      induction a, b using DirectLimit.induction₂ f with
      | ih i a b => simp only [DirectLimit.smul_def, directLimit_sup, nonneg_smul_sup a b r hr]
    exact sup_eq_right.mp ((h a b).trans (congrArg (r • ·) (sup_eq_right.mpr hab)))

/-- The canonical homomorphism from a stage into a directed limit of vector lattices. -/
noncomputable def directLimitInclusion (i : D) : VecLatHom (G i) (DirectLimit G f) :=
  { DirectLimit.Module.of ℝ D G f i with
    map_sup' := fun x y ↦ (directLimit_sup f i x y).symm
    map_inf' := fun x y ↦ (directLimit_inf f i x y).symm }

/-- A directed limit of Archimedean vector lattices along embeddings is Archimedean. -/
private lemma directLimit_archimedean [∀ i, IsVLArchimedean (G i)]
    (hf : ∀ i j h, Function.Injective (f i j h)) : IsVLArchimedean (DirectLimit G f) := by
  constructor
  intro z w
  induction z, w using DirectLimit.induction₂ f with
  | ih i x y =>
    intro h
    have hi : Function.Injective (directLimitInclusion f i) := DirectLimit.mk_injective f hf i
    have hx : x ≤ 0 := IsVLArchimedean.le_zero_of_forall_nsmul_le (fun n ↦
      (directLimitInclusion f i).le_of_map_le hi
        (by rw [map_nsmul]; exact h n))
    have hxi := (directLimitInclusion f i).monotone hx
    rw [map_zero] at hxi
    exact hxi

/-- Compatible homomorphisms from the stages induce a homomorphism from their directed limit. -/
noncomputable def directLimitLift {Y : Type u} [AddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] [VectorLattice Y] (g : ∀ i, VecLatHom (G i) Y)
    (hg : ∀ i j h x, g j (f i j h x) = g i x) : VecLatHom (DirectLimit G f) Y :=
  { DirectLimit.Module.lift ℝ D G f (fun i ↦ (g i).toLinearMap) hg with
    map_sup' := DirectLimit.induction₂ f (fun i x y ↦ by
      rw [directLimit_sup]
      exact map_sup (g i) x y)
    map_inf' := DirectLimit.induction₂ f (fun i x y ↦ by
      rw [directLimit_inf]
      exact map_inf (g i) x y) }

end DirectedUnions

/-- Compatible homomorphisms on an increasing directed cover of sublattices glue to a
homomorphism on the whole lattice. -/
private lemma exists_glued_hom {D X Y : Type u} [Preorder D] [IsDirectedOrder D]
    [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X]
    [AddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [VectorLattice Y]
    (A : D → VectorSublattice X) (hA : Monotone A) (hc : ∀ x, ∃ i, x ∈ A i)
    (g : ∀ i, VecLatHom (A i) Y)
    (hg : ∀ i j (h : i ≤ j) x, g j (VectorSublattice.inclusion (hA h) x) = g i x) :
    ∃ h : VecLatHom X Y, ∀ i (x : A i), h x = g i x := by
  classical
  choose d hd using hc
  let h (x : X) := g (d x) ⟨x, hd x⟩
  have hs (i : D) (x : A i) : h x = g i x := by
    obtain ⟨k, hdk, hik⟩ := exists_ge_ge (d x) i
    exact (hg (d x) k hdk ⟨x, hd x⟩).symm.trans (hg i k hik x)
  have ha (x y : X) : h (x + y) = h x + h y := by
    obtain ⟨k, hxk, hyk⟩ := exists_ge_ge (d x) (d y)
    let x' : A k := ⟨x, hA hxk (hd x)⟩
    let y' : A k := ⟨y, hA hyk (hd y)⟩
    exact (hs k (x' + y')).trans ((map_add (g k) x' y').trans
      (congrArg₂ (· + ·) (hs k x').symm (hs k y').symm))
  let l : X →ₗ[ℝ] Y :=
    { toFun := h
      map_add' := ha
      map_smul' := fun r x ↦ (hs (d x) (r • (⟨x, hd x⟩ : A (d x)))).trans
        ((map_smul (g (d x)) r ⟨x, hd x⟩).trans (congrArg (r • ·) (hs _ _).symm)) }
  refine ⟨VecLatHom.ofAbs l ?_, hs⟩
  intro x
  exact (hs (d x) |(⟨x, hd x⟩ : A (d x))|).trans
    (((g (d x)).map_abs ⟨x, hd x⟩).trans (congrArg abs (hs _ _).symm))

section FreeProducts

variable {I : Type u} {E : I → Type u}
  [∀ i, AddCommGroup (E i)] [∀ i, Lattice (E i)]
  [∀ i, IsOrderedAddMonoid (E i)] [∀ i, VectorLattice (E i)]
  [∀ i, IsVLArchimedean (E i)]

/-- An increasing family of factor sublattices induces compatible transition maps between
their Archimedean free products. -/
lemma ArchimedeanFreeProduct.exists_directed_transitions
    {D : Type u} [Preorder D]
    (A : D → ∀ i, VectorSublattice (E i)) (hA : Monotone A)
    (B : ∀ d, ArchimedeanFreeProduct (fun i ↦ A d i)) :
    ∃ f : ∀ a b, a ≤ b → VecLatHom (B a).Carrier (B b).Carrier,
      DirectedSystem (fun d ↦ (B d).Carrier) (f · · ·) ∧
      ∀ a b (h : a ≤ b) i x, f a b h ((B a).inclusion i x) =
        (B b).inclusion i (VectorSublattice.inclusion (hA h i) x) := by
  choose f hf _ using fun a b (h : a ≤ b) ↦ (B a).universal (B b).Carrier
    (fun i ↦ ((B b).inclusion i).comp (VectorSublattice.inclusion (hA h i)))
  refine ⟨f, ⟨?_, ?_⟩, hf⟩
  · intro a x
    exact DFunLike.congr_fun ((B a).hom_ext (S := f a a le_rfl) (T := VecLatHom.id)
      (fun i y ↦ hf a a le_rfl i y)) x
  · intro c b a hab hbc x
    apply DFunLike.congr_fun ((B a).hom_ext (S := (f b c hbc).comp (f a b hab))
      (T := f a c (hab.trans hbc)) ?_) x
    intro i y
    change f b c hbc (f a b hab ((B a).inclusion i y)) = _
    rw [hf]
    exact (hf b c hbc i _).trans (hf a c (hab.trans hbc) i y).symm

/-- For a directed cover with injective transition maps, the stage free products embed in the
full free product and exhaust its elements. -/
lemma ArchimedeanFreeProduct.exists_directed_stage_maps
    {D : Type u} [Preorder D] [IsDirectedOrder D] [Nonempty D]
    (A : D → ∀ i, VectorSublattice (E i)) (hA : Monotone A)
    (hc : ∀ i (x : E i), ∃ d, x ∈ A d i)
    (B : ∀ d, ArchimedeanFreeProduct (fun i ↦ A d i))
    (f : ∀ a b, a ≤ b → VecLatHom (B a).Carrier (B b).Carrier)
    [DirectedSystem (fun d ↦ (B d).Carrier) (f · · ·)]
    (hf : ∀ a b h, Function.Injective (f a b h))
    (hfi : ∀ a b (h : a ≤ b) i x,
      f a b h ((B a).inclusion i x) =
        (B b).inclusion i (VectorSublattice.inclusion (hA h i) x))
    (P : ArchimedeanFreeProduct E) :
    ∃ U : ∀ d, VecLatHom (B d).Carrier P.Carrier,
      (∀ d i x, U d ((B d).inclusion i x) = P.inclusion i x) ∧
      (∀ d, Function.Injective (U d)) ∧ ∀ z, ∃ d x, U d x = z := by
  let V := DirectLimit (fun d ↦ (B d).Carrier) f
  let : IsVLArchimedean V := directLimit_archimedean f hf
  let g (i : I) (d : D) := (directLimitInclusion f d).comp ((B d).inclusion i)
  have hg (i : I) (a b : D) (h : a ≤ b) (x : A a i) :
      g i b (VectorSublattice.inclusion (hA h i) x) = g i a x := by
    change (directLimitInclusion f b) ((B b).inclusion i _) =
      (directLimitInclusion f a) ((B a).inclusion i x)
    rw [← hfi a b h i x]
    exact DirectLimit.mk_apply (f := f) a b ((B a).inclusion i x) h
  choose j hj using fun i ↦ exists_glued_hom (fun d ↦ A d i)
    (fun _ _ h ↦ hA h i) (hc i) (g i) (hg i)
  choose U hU _ using fun d ↦ (B d).universal P.Carrier
    (fun i ↦ (P.inclusion i).comp (A d i).subtype)
  have hUf (a b : D) (h : a ≤ b) : (U b).comp (f a b h) = U a := by
    apply (B a).hom_ext
    intro i x
    change U b (f a b h ((B a).inclusion i x)) = U a ((B a).inclusion i x)
    rw [hfi, hU, hU]
    rfl
  let W := directLimitLift f U (fun a b h x ↦ DFunLike.congr_fun (hUf a b h) x)
  obtain ⟨R, hR, _⟩ := P.universal V j
  have hRU (d : D) : R.comp (U d) = directLimitInclusion f d := by
    apply (B d).hom_ext
    intro i x
    change R (U d ((B d).inclusion i x)) = (g i d) x
    rw [hU]
    exact (hR i x).trans (hj i d x)
  have hWR : W.comp R = VecLatHom.id := by
    apply P.hom_ext
    intro i x
    obtain ⟨d, hx⟩ := hc i x
    change W (R (P.inclusion i x)) = P.inclusion i x
    rw [hR, hj i d ⟨x, hx⟩]
    exact hU d i ⟨x, hx⟩
  refine ⟨U, hU, fun d x y hxy ↦ DirectLimit.mk_injective f hf d ?_, ?_⟩
  · exact (DFunLike.congr_fun (hRU d) x).symm.trans
      ((congrArg R hxy).trans (DFunLike.congr_fun (hRU d) y))
  · intro z
    obtain ⟨d, x, hx⟩ := DirectLimit.exists_eq_mk f (R z)
    exact ⟨d, x, (congrArg W hx).symm.trans (DFunLike.congr_fun hWR z)⟩

end FreeProducts

end VectorLattice
