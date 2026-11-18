/-
Authors: Gonzalo Martínez-Fernández
-/

import FreeProducts.VectorLattice.Amalgamation

/-!
# Archimedeanization and universal properties

The quotient by the intersection of uniformly closed order ideals is universal
among Archimedean targets. Applying this construction to vector lattice colimits
and pushouts gives the corresponding universal properties for Archimedean lattices.
-/

universe u v

namespace VectorLattice

section Archimedeanization

variable (X : Type u) [AddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [VectorLattice X]

/-- The intersection of all uniformly closed order ideals. -/
noncomputable def archimedeanIdeal : OrderIdeal X :=
  sInf {J : OrderIdeal X | J.IsUniformlyClosed}

/-- The quotient by the intersection of all uniformly closed ideals. -/
abbrev Archimedeanization :=
  X ⧸ (archimedeanIdeal X).toSubmodule

/-- The ideal defining Archimedeanization is uniformly closed. -/
theorem archimedeanIdeal_isUniformlyClosed :
    (archimedeanIdeal X).IsUniformlyClosed := by
  exact fun x u f hu hf hbound ↦ OrderIdeal.mem_sInf.mpr
    (fun J hJ ↦ hJ x u f hu
      (fun n ↦ OrderIdeal.mem_sInf.mp (hf n) J hJ) hbound)

/-- Archimedeanization is an Archimedean vector lattice. -/
instance instIsVLArchimedeanArchimedeanization :
    IsVLArchimedean (Archimedeanization X) := by
  exact (OrderIdeal.quotient_archimedean_iff_uniformlyClosed _).mpr
    (archimedeanIdeal_isUniformlyClosed X)

/-- The canonical quotient homomorphism to the Archimedeanization. -/
noncomputable def archimedeanQuotient :
    VecLatHom X (Archimedeanization X) :=
  (archimedeanIdeal X).mkQVecLatHom

/-- The canonical Archimedean quotient is surjective. -/
theorem archimedeanQuotient_surjective :
    Function.Surjective (archimedeanQuotient X) := by
  exact Submodule.Quotient.mk_surjective _

/-- The kernel of a lattice homomorphism into an Archimedean lattice is uniformly closed. -/
private lemma ker_isUniformlyClosed
    {Y : Type v} [AddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] [VectorLattice Y] [IsVLArchimedean Y]
    (T : VecLatHom X Y) : (OrderIdeal.ofKerVecLatHom T).IsUniformlyClosed := by
  intro x u f hu hf hb
  suffices h : |T x| ≤ 0 from (abs_eq_zero_iff_zero _).mp (le_antisymm h (abs_nonneg _))
  apply ((isVLArchimedean_iff_isGLB_inv_smul.mp inferInstance) (T u)
    (T.map_nonneg hu)).2
  rintro _ ⟨n, hn, rfl⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  simpa [VecLatHom.map_abs, map_sub, map_smul,
    show T (f k) = 0 from hf k, one_div] using T.monotone (hb k)

/-- Every homomorphism into an Archimedean vector lattice factors
uniquely through the canonical quotient. -/
theorem archimedeanization_universal
    (Y : Type v) [AddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] [VectorLattice Y] [IsVLArchimedean Y]
    (T : VecLatHom X Y) :
    ∃! S : VecLatHom (Archimedeanization X) Y,
      S.comp (archimedeanQuotient X) = T := by
  have hker : (archimedeanIdeal X).toSubmodule ≤ LinearMap.ker T.toLinearMap :=
    fun x hx ↦ OrderIdeal.mem_sInf.mp hx _ (ker_isUniformlyClosed X T)
  refine ⟨(archimedeanIdeal X).liftQVecLatHom T hker, rfl, fun S hS ↦ ?_⟩
  exact DFunLike.ext _ _ ((archimedeanQuotient_surjective X).forall.mpr
    (fun x ↦ DFunLike.congr_fun hS x))

/-- Archimedeanization identifies no distinct vectors exactly when
the original vector lattice is Archimedean. -/
theorem archimedeanQuotient_injective_iff :
    Function.Injective (archimedeanQuotient X) ↔ IsVLArchimedean X := by
  constructor
  · exact fun h ↦ ⟨fun {x y} hb ↦ (archimedeanQuotient X).le_of_map_le h
      (by simpa using
        (IsVLArchimedean.le_zero_of_forall_nsmul_le
          (y := archimedeanQuotient X y)
          (fun n ↦ by simpa using (archimedeanQuotient X).monotone (hb n))))⟩
  · intro h
    obtain ⟨S, hS, _⟩ := archimedeanization_universal X X VecLatHom.id
    exact (show Function.LeftInverse S (archimedeanQuotient X) from
      fun x ↦ DFunLike.congr_fun hS x).injective

end Archimedeanization

section Colimits

variable {I : Type u} (E : I → Type u)
  [∀ i, AddCommGroup (E i)] [∀ i, Lattice (E i)]
  [∀ i, IsOrderedAddMonoid (E i)] [∀ i, VectorLattice (E i)]
  [∀ i, IsVLArchimedean (E i)]

omit [∀ i, IsVLArchimedean (E i)] in
/-- Archimedeanizing a colimit cocone preserves its compatibility
and makes it universal among Archimedean targets. -/
theorem archimedeanization_colimit_universal
    (arrows : ∀ i j, Set (VecLatHom (E i) (E j)))
    (L : Type u) [AddCommGroup L] [Lattice L]
    [IsOrderedAddMonoid L] [VectorLattice L]
    (ι : ∀ i, VecLatHom (E i) L)
    (hι : ∀ i j (f : VecLatHom (E i) (E j)),
      f ∈ arrows i j → (ι j).comp f = ι i)
    (hL : ∀ (Y : Type u) [AddCommGroup Y] [Lattice Y]
      [IsOrderedAddMonoid Y] [VectorLattice Y]
      (T : ∀ i, VecLatHom (E i) Y),
      (∀ i j (f : VecLatHom (E i) (E j)),
        f ∈ arrows i j → (T j).comp f = T i) →
      ∃! S : VecLatHom L Y, ∀ i, S.comp (ι i) = T i) :
    (∀ i j (f : VecLatHom (E i) (E j)),
      f ∈ arrows i j →
        ((archimedeanQuotient L).comp (ι j)).comp f =
          (archimedeanQuotient L).comp (ι i)) ∧
    ∀ (Y : Type u) [AddCommGroup Y] [Lattice Y]
      [IsOrderedAddMonoid Y] [VectorLattice Y] [IsVLArchimedean Y]
      (T : ∀ i, VecLatHom (E i) Y),
      (∀ i j (f : VecLatHom (E i) (E j)),
        f ∈ arrows i j → (T j).comp f = T i) →
      ∃! S : VecLatHom (Archimedeanization L) Y,
        ∀ i, S.comp ((archimedeanQuotient L).comp (ι i)) = T i := by
  refine ⟨fun i j f hf ↦ DFunLike.ext _ _ (fun x ↦
    congrArg (archimedeanQuotient L) (DFunLike.congr_fun (hι i j f hf) x)), ?_⟩
  intro Y _ _ _ _ _ T hT
  obtain ⟨U, hU, huU⟩ := hL Y T hT
  obtain ⟨S, hS, huS⟩ := archimedeanization_universal L Y U
  exact ⟨S, fun i ↦ (congrArg (fun R : VecLatHom L Y ↦ R.comp (ι i)) hS).trans
    (hU i), fun R hR ↦ huS R (huU (R.comp (archimedeanQuotient L)) hR)⟩

end Colimits

section Pushouts

variable {X Y Z : Type u}
  [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X] [IsVLArchimedean X]
  [AddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
  [VectorLattice Y] [IsVLArchimedean Y]
  [AddCommGroup Z] [Lattice Z] [IsOrderedAddMonoid Z]
  [VectorLattice Z] [IsVLArchimedean Z]

omit [IsVLArchimedean X] [IsVLArchimedean Y] [IsVLArchimedean Z] in
/-- Archimedeanizing an ordinary pushout gives a commutative square
with the universal property for Archimedean targets. -/
theorem Pushout.archimedeanization_universal
    (f : VecLatHom Z X) (g : VecLatHom Z Y) (P : Pushout f g) :
    (((archimedeanQuotient P.Carrier).comp P.left).comp f =
      ((archimedeanQuotient P.Carrier).comp P.right).comp g) ∧
    ∀ (W : Type u) [AddCommGroup W] [Lattice W]
      [IsOrderedAddMonoid W] [VectorLattice W] [IsVLArchimedean W]
      (a : VecLatHom X W) (b : VecLatHom Y W),
      a.comp f = b.comp g →
      ∃! S : VecLatHom (Archimedeanization P.Carrier) W,
        S.comp ((archimedeanQuotient P.Carrier).comp P.left) = a ∧
        S.comp ((archimedeanQuotient P.Carrier).comp P.right) = b := by
  refine ⟨DFunLike.ext _ _ (fun z ↦ congrArg (archimedeanQuotient P.Carrier)
    (DFunLike.congr_fun P.comm z)), ?_⟩
  intro W _ _ _ _ _ a b hab
  obtain ⟨U, hU, huU⟩ := P.universal W a b hab
  obtain ⟨S, hS, huS⟩ := VectorLattice.archimedeanization_universal P.Carrier W U
  exact ⟨S, ⟨(congrArg (fun R : VecLatHom P.Carrier W ↦ R.comp P.left) hS).trans hU.1,
    (congrArg (fun R : VecLatHom P.Carrier W ↦ R.comp P.right) hS).trans hU.2⟩,
    fun R hR ↦ huS R (huU (R.comp (archimedeanQuotient P.Carrier)) hR)⟩

end Pushouts

end VectorLattice
