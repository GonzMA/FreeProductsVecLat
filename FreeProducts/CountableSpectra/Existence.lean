/-
Authors: Gonzalo Martínez-Fernández
-/

import FreeProducts.CountableSpectra.TransfiniteConstruction
import FreeProducts.CountableSpectra.InjectiveProperties

/-!
# Existence of extensions with universal disposition

A cardinally bounded family represents the extension problems for small lattices.
Successive amalgamations solve these problems and produce extensions with universal
disposition and relative injectivity, together with explicit cardinal bounds.
-/

noncomputable section

universe u v w

namespace VectorLattice.CountableSpectra

/-- A presentation of a vector lattice inside a lifted copy of the real line, together with a
chosen vector sublattice. -/
private structure SmallLatticePresentation where
  Carrier : Type u
  [addCommGroup : AddCommGroup Carrier]
  [lattice : Lattice Carrier]
  [isOrderedAddMonoid : IsOrderedAddMonoid Carrier]
  [vectorLattice : VectorLattice Carrier]
  embedding : Carrier ↪ ULift.{u} ℝ
  sublattice : VectorSublattice Carrier

attribute [instance] SmallLatticePresentation.addCommGroup SmallLatticePresentation.lattice
  SmallLatticePresentation.isOrderedAddMonoid SmallLatticePresentation.vectorLattice

/-- Encode a presented lattice by its carrier, four operations, and chosen sublattice, all
expressed in the common ambient set. -/
private def SmallLatticePresentation.code (p : SmallLatticePresentation.{u}) :
    Set (ULift.{u} ℝ) ×
      (Fin 4 → ULift.{u} ℝ → ULift.{u} ℝ → ULift.{u} ℝ) × Set (ULift.{u} ℝ) :=
  (Set.range p.embedding, (fun k a b ↦ p.embedding <| match k.val with
    | 0 => Function.invFun p.embedding a + Function.invFun p.embedding b
    | 1 => a.down • Function.invFun p.embedding b
    | 2 => Function.invFun p.embedding a ⊔ Function.invFun p.embedding b
    | _ => Function.invFun p.embedding a ⊓ Function.invFun p.embedding b),
    p.embedding '' (p.sublattice : Set p.Carrier))

/-- Equal presentation codes determine an equivalence of the underlying lattice carriers. -/
private def SmallLatticePresentation.equivOfCodeEq (p q : SmallLatticePresentation.{u})
    (h : p.code = q.code) : p.Carrier ≃ q.Carrier :=
  (Equiv.ofInjective p.embedding p.embedding.injective).trans
    ((Set.equivOfEq (congrArg Prod.fst h)).trans
      (Equiv.ofInjective q.embedding q.embedding.injective).symm)

/-- The carrier equivalence associated with equal codes preserves the coordinates of the
presentation embeddings. -/
private lemma SmallLatticePresentation.embedding_equivOfCodeEq
    (p q : SmallLatticePresentation.{u}) (h : p.code = q.code) (x : p.Carrier) :
    q.embedding (p.equivOfCodeEq q h x) = p.embedding x :=
  Equiv.apply_ofInjective_symm q.embedding.injective _

/-- The chosen inverse of a presentation embedding agrees with the carrier equivalence induced
by equality of codes. -/
private lemma SmallLatticePresentation.invFun_embedding
    (p q : SmallLatticePresentation.{u}) (h : p.code = q.code) (x : p.Carrier) :
    Function.invFun q.embedding (p.embedding x) = p.equivOfCodeEq q h x := by
  rw [← p.embedding_equivOfCodeEq q h x, Function.leftInverse_invFun q.embedding.injective]

/-- Equal presentation codes determine a vector lattice equivalence. -/
private def SmallLatticePresentation.vecLatEquivOfCodeEq
    (p q : SmallLatticePresentation.{u}) (h : p.code = q.code) :
    VecLatEquiv p.Carrier q.Carrier := by
  refine { p.equivOfCodeEq q h with
    map_add' := ?_, map_smul' := ?_, map_sup' := ?_, map_inf' := ?_ } <;>
    intro x y <;> apply q.embedding.injective <;>
    simp only [Equiv.toFun_as_coe, p.embedding_equivOfCodeEq q h]
  · simpa [code, Function.leftInverse_invFun p.embedding.injective x,
      Function.leftInverse_invFun p.embedding.injective y, p.invFun_embedding q h] using
      congrArg (fun c ↦ c.2.1 0 (p.embedding x) (p.embedding y)) h
  · simpa [code, Function.leftInverse_invFun p.embedding.injective y,
      p.invFun_embedding q h] using
      congrArg (fun c ↦ c.2.1 1 (ULift.up x) (p.embedding y)) h
  · simpa [code, Function.leftInverse_invFun p.embedding.injective x,
      Function.leftInverse_invFun p.embedding.injective y, p.invFun_embedding q h] using
      congrArg (fun c ↦ c.2.1 2 (p.embedding x) (p.embedding y)) h
  · simpa [code, Function.leftInverse_invFun p.embedding.injective x,
      Function.leftInverse_invFun p.embedding.injective y, p.invFun_embedding q h] using
      congrArg (fun c ↦ c.2.1 3 (p.embedding x) (p.embedding y)) h

/-- The equivalence induced by equal codes preserves membership in the chosen sublattice. -/
private lemma SmallLatticePresentation.mem_sublattice_equivOfCodeEq
    (p q : SmallLatticePresentation.{u}) (h : p.code = q.code) (x : p.Carrier) :
    p.equivOfCodeEq q h x ∈ q.sublattice ↔ x ∈ p.sublattice := by
  have hm := Set.ext_iff.mp (congrArg (fun c ↦ c.2.2) h) (p.embedding x)
  simp only [code, p.embedding.injective.mem_set_image] at hm
  simpa only [← p.embedding_equivOfCodeEq q h, q.embedding.injective.mem_set_image,
    SetLike.mem_coe] using hm.symm

/-- The set of codes for these lattice presentations has cardinality equal to two to the power
of the continuum. -/
private lemma small_lattice_codes_cardinal :
    Cardinal.mk (Set (ULift.{u} ℝ) ×
      (Fin 4 → ULift.{u} ℝ → ULift.{u} ℝ → ULift.{u} ℝ) × Set (ULift.{u} ℝ)) =
      2 ^ Cardinal.continuum := by
  simp [Cardinal.mk_prod, Cardinal.mk_set, Cardinal.mk_real, ← Cardinal.power_mul,
    Cardinal.power_self_eq Cardinal.aleph0_le_continuum, ← Cardinal.power_add]

/-- Lattices of size at most continuum, together with a chosen sublattice, have a family of
representatives of size at most two to the continuum. -/
theorem exists_small_sublattice_representatives :
    ∃ (ι : Type u) (Y : ι → Type u) (a : ∀ i, AddCommGroup (Y i)) (l : ∀ i, Lattice (Y i)),
      letI := a
      letI := l
      ∃ o : ∀ i, IsOrderedAddMonoid (Y i),
        letI := o
        ∃ v : ∀ i, VectorLattice (Y i),
          letI := v
          ∃ A : ∀ i, VectorSublattice (Y i),
            Cardinal.mk ι ≤ 2 ^ Cardinal.continuum ∧
              (∀ i, Cardinal.mk (Y i) ≤ Cardinal.continuum) ∧
              ∀ (X : Type u) [AddCommGroup X] [Lattice X]
                [IsOrderedAddMonoid X] [VectorLattice X],
                Cardinal.mk X ≤ Cardinal.continuum → ∀ S : VectorSublattice X,
                  ∃ (i : ι) (e : VecLatEquiv X (Y i)), ∀ x, x ∈ S ↔ e x ∈ A i := by
  let rep (i : Set.range SmallLatticePresentation.code) := i.property.choose
  refine ⟨_, fun i ↦ (rep i).Carrier, fun i ↦ (rep i).addCommGroup,
    fun i ↦ (rep i).lattice, fun i ↦ (rep i).isOrderedAddMonoid,
    fun i ↦ (rep i).vectorLattice, fun i ↦ (rep i).sublattice,
    (Cardinal.mk_set_le _).trans_eq small_lattice_codes_cardinal,
    fun i ↦ ?_, ?_⟩
  · simpa only [Cardinal.mk_uLift, Cardinal.mk_real, Cardinal.lift_continuum] using
      (rep i).embedding.cardinal_le
  · intro X _ _ _ _ hX S
    obtain ⟨f⟩ : Nonempty (X ↪ ULift.{u} ℝ) := (Cardinal.le_def _ _).mp
      (by simpa only [Cardinal.mk_uLift, Cardinal.mk_real, Cardinal.lift_continuum] using hX)
    let p : SmallLatticePresentation := { Carrier := X, embedding := f, sublattice := S }
    let i : Set.range SmallLatticePresentation.code := ⟨p.code, p, rfl⟩
    exact ⟨i, p.vecLatEquivOfCodeEq (rep i) i.property.choose_spec.symm,
      fun x ↦ (p.mem_sublattice_equivOfCodeEq (rep i) i.property.choose_spec.symm x).symm⟩

section TransfiniteConstruction

open CategoryTheory CategoryTheory.Limits

/-- Process a cardinally bounded family of extension diagrams over a fixed lattice without
exceeding the carrier cardinality bound. -/
private lemma bounded_process_family {κ : Cardinal.{u}} (hκ : Cardinal.continuum ≤ κ)
    {D : Type u} (hD : Cardinal.mk D ≤ κ)
    (A B : D → BoundedVectorLattice κ) (i : ∀ d, A d ⟶ B d)
    (X : BoundedVectorLattice κ) (f : ∀ d, A d ⟶ X) :
    ∃ Y, ∃ j : X ⟶ Y, ∀ d, ∃ g : B d ⟶ Y, i d ≫ g = f d ≫ j := by
  have hω := Cardinal.aleph0_le_continuum.trans hκ
  let := Cardinal.nonempty_ord_toType (Cardinal.aleph0_pos.trans_le hω).ne'
  let := WellFoundedLT.toOrderBot κ.ord.ToType
  let := Cardinal.noMaxOrder hω
  have hJ : Cardinal.mk κ.ord.ToType ≤ κ := by simp
  let := bounded_hasIteration hω hJ
  let := under_hasIteration (J := κ.ord.ToType) X
  obtain ⟨e⟩ : Nonempty (D ↪ κ.ord.ToType) :=
    (Cardinal.le_def _ _).mp (by simpa using hD)
  let P : D → Under X → Prop := fun d Y ↦ ∃ g : B d ⟶ Y.right,
    i d ≫ g = f d ≫ Y.hom
  have hP : ∀ {Y Z : Under X}, (Y ⟶ Z) → ∀ d, P d Y → P d Z := by
    rintro Y Z h d ⟨g, hg⟩
    exact ⟨g ≫ h.right, by rw [← Category.assoc, hg, Category.assoc, Under.w]⟩
  have hstep : ∀ Y d, ∃ Z, ∃ _ : Y ⟶ Z, P d Z := by
    intro Y d
    obtain ⟨Z, a, b, hab⟩ := bounded_amalgam hκ (i d) (f d ≫ Y.hom)
    exact ⟨Under.mk (Y.hom ≫ b), Under.homMk b rfl, a,
      hab.trans (Category.assoc _ _ _)⟩
  obtain ⟨Y, _, hY⟩ := indexed_iteration_satisfying e P hP hstep (Under.mk (𝟙 X))
  exact ⟨Y.right, Y.hom, hY⟩

/-- There are at most the given cardinally many embeddings from a lattice of size at most the
continuum into a bounded lattice, under the stated cardinal exponent identity. -/
private lemma bounded_hom_cardinal {κ : Cardinal.{u}} (hκ : Cardinal.continuum ≤ κ)
    (hpow : κ ^ Cardinal.continuum = κ) (A X : BoundedVectorLattice κ)
    (hA : Cardinal.mk A.Carrier ≤ Cardinal.continuum) : Cardinal.mk (A ⟶ X) ≤ κ := by
  have hi : Function.Injective (fun f : A ⟶ X ↦ (f.val : A.Carrier → X.Carrier)) :=
    fun _ _ h ↦ Subtype.ext (DFunLike.coe_injective h)
  calc
    _ ≤ Cardinal.mk (A.Carrier → X.Carrier) := Cardinal.mk_le_of_injective hi
    _ = Cardinal.mk X.Carrier ^ Cardinal.mk A.Carrier := by simp
    _ ≤ κ ^ Cardinal.mk A.Carrier := Cardinal.power_le_power_right X.cardinal_le
    _ ≤ κ ^ Cardinal.continuum := Cardinal.power_le_power_left
      (Cardinal.continuum_pos.trans_le hκ).ne' hA
    _ = κ := hpow

/-- Construct one bounded successor lattice that extends every embedding associated with the
chosen family of representatives. -/
private lemma bounded_successor {κ : Cardinal.{u}} (hκ : Cardinal.continuum ≤ κ)
    (hpow : κ ^ Cardinal.continuum = κ) {ι : Type u} (hι : Cardinal.mk ι ≤ κ)
    (A B : ι → BoundedVectorLattice κ) (i : ∀ d, A d ⟶ B d)
    (hA : ∀ d, Cardinal.mk (A d).Carrier ≤ Cardinal.continuum)
    (X : BoundedVectorLattice κ) :
    ∃ Y, ∃ j : X ⟶ Y, ∀ d (f : A d ⟶ X), ∃ g : B d ⟶ Y, i d ≫ g = f ≫ j := by
  have hD : Cardinal.mk (Σ d, A d ⟶ X) ≤ κ := by
    calc
      _ = Cardinal.sum (fun d ↦ Cardinal.mk (A d ⟶ X)) := Cardinal.mk_sigma _
      _ ≤ Cardinal.sum (fun _ : ι ↦ κ) := Cardinal.sum_le_sum _ _
        (fun d ↦ bounded_hom_cardinal hκ hpow (A d) X (hA d))
      _ = Cardinal.mk ι * κ := Cardinal.sum_const' _ _
      _ ≤ κ * κ := mul_le_mul' hι le_rfl
      _ = κ := Cardinal.mul_eq_self (Cardinal.aleph0_le_continuum.trans hκ)
  obtain ⟨Y, j, hj⟩ := bounded_process_family hκ hD
    (fun d ↦ A d.1) (fun d ↦ B d.1) (fun d ↦ i d.1) X (fun d ↦ d.2)
  exact ⟨Y, j, fun d f ↦ hj ⟨d, f⟩⟩

/-- Iterating the successor construction gives a bounded extension with the extension property
for the chosen representative family. -/
private lemma bounded_universal_family {κ : Cardinal.{u}}
    (hκ : 2 ^ Cardinal.continuum ≤ κ) (hpow : κ ^ Cardinal.continuum = κ)
    {ι : Type u} (hι : Cardinal.mk ι ≤ κ)
    (A B : ι → BoundedVectorLattice κ) (i : ∀ d, A d ⟶ B d)
    (hA : ∀ d, Cardinal.mk (A d).Carrier ≤ Cardinal.continuum)
    (X : BoundedVectorLattice κ) :
    ∃ Y, Nonempty (X ⟶ Y) ∧ ∀ d (f : A d ⟶ Y), ∃ g : B d ⟶ Y, i d ≫ g = f := by
  have hc : Cardinal.continuum ≤ κ := (Cardinal.cantor _).le.trans hκ
  let J := (Order.succ Cardinal.continuum : Cardinal.{u}).ord.ToType
  have hreg := Cardinal.isRegular_succ Cardinal.aleph0_le_continuum (c := Cardinal.continuum.{u})
  let : Nonempty J := Cardinal.nonempty_ord_toType hreg.ne_zero
  let := WellFoundedLT.toOrderBot J
  let : NoMaxOrder J := Cardinal.noMaxOrder hreg.aleph0_le
  have hJ : Cardinal.mk J ≤ κ := by
    simpa [J] using (Order.succ_le_of_lt (Cardinal.cantor Cardinal.continuum)).trans hκ
  let := bounded_hasIteration (Cardinal.aleph0_le_continuum.trans hc) hJ
  choose next j hj using bounded_successor hc hpow hι A B i hA
  let Φ : SmallObject.SuccStruct (BoundedVectorLattice κ) := ⟨X, next, j⟩
  refine ⟨Φ.iteration J, ⟨Φ.ιIteration J⟩, fun d f ↦
    iteration_extension (Cardinal.aleph0_le_continuum.trans hc) hJ Φ (i d) ?_
      (fun Y g ↦ hj Y d g) f⟩
  simpa [J, Ordinal.cof_toType, hreg.cof_ord] using
    (hA d).trans_lt (Order.lt_succ Cardinal.continuum)

/-- Transfer an extension property across a vector lattice equivalence that preserves the
chosen sublattices. -/
private lemma transfer_extension {V W U : Type u}
    [AddCommGroup V] [Lattice V] [IsOrderedAddMonoid V] [VectorLattice V]
    [AddCommGroup W] [Lattice W] [IsOrderedAddMonoid W] [VectorLattice W]
    [AddCommGroup U] [Lattice U] [IsOrderedAddMonoid U] [VectorLattice U]
    (S : VectorSublattice V) (T : VectorSublattice W) (e : VecLatEquiv V W)
    (he : ∀ x, x ∈ S ↔ e x ∈ T)
    (hU : ∀ f : VecLatHom T U, Function.Injective f →
      ∃ g : VecLatHom W U, Function.Injective g ∧ ∀ x, g x.val = f x)
    (f : VecLatHom S U) (hf : Function.Injective f) :
    ∃ g : VecLatHom V U, Function.Injective g ∧ ∀ x, g x.val = f x := by
  have hr : ∀ x : T, e.symm x.val ∈ S := fun x ↦ (he _).mpr
    (show e (e.symm x.val) ∈ T from (e.toLinearEquiv.apply_symm_apply x.val).symm ▸ x.property)
  let r : VecLatHom T S :=
    { LinearMap.codRestrict S.toSubmodule
        (e.symm.toVecLatHom.comp T.subtype).toLinearMap hr with
      map_sup' := fun x y ↦ Subtype.ext ((e.symm.toVecLatHom.comp T.subtype).map_sup' x y)
      map_inf' := fun x y ↦ Subtype.ext ((e.symm.toVecLatHom.comp T.subtype).map_inf' x y) }
  have hri : Function.Injective r := fun x y h ↦
    Subtype.ext (e.toLinearEquiv.symm.injective (congrArg Subtype.val h))
  obtain ⟨g, hg, hgf⟩ := hU (f.comp r) (hf.comp hri)
  refine ⟨g.comp e.toVecLatHom, hg.comp e.toLinearEquiv.injective, fun x ↦ ?_⟩
  exact (hgf ⟨e x.val, (he x.val).mp x.property⟩).trans
    (congrArg f (Subtype.ext (e.toLinearEquiv.symm_apply_apply x.val)))

/-- Under the stated cardinal arithmetic assumptions, construct a bounded extension universal
for embeddings of lattices of size at most the continuum. -/
private lemma bounded_universal {κ : Cardinal.{u}}
    (hκ : 2 ^ Cardinal.continuum ≤ κ) (hpow : κ ^ Cardinal.continuum = κ)
    (X : BoundedVectorLattice κ) :
    ∃ U, Nonempty (X ⟶ U) ∧
      ∀ (V : Type u) [AddCommGroup V] [Lattice V] [IsOrderedAddMonoid V] [VectorLattice V],
        Cardinal.mk V ≤ Cardinal.continuum → ∀ (S : VectorSublattice V)
          (f : VecLatHom S U.Carrier), Function.Injective f →
          ∃ g : VecLatHom V U.Carrier, Function.Injective g ∧ ∀ x, g x.val = f x := by
  obtain ⟨ι, V, a, l, o, v, S, hι, hV, hrep⟩ := exists_small_sublattice_representatives.{u}
  let := a
  let := l
  let := o
  let := v
  have hc : Cardinal.continuum ≤ κ := (Cardinal.cantor _).le.trans hκ
  let B : ι → BoundedVectorLattice κ := fun d ↦ ⟨V d, (hV d).trans hc⟩
  let A : ι → BoundedVectorLattice κ := fun d ↦
    ⟨S d, (Cardinal.mk_subtype_le _).trans ((hV d).trans hc)⟩
  let i : ∀ d, A d ⟶ B d := fun d ↦ ⟨(S d).subtype, Subtype.val_injective⟩
  obtain ⟨U, j, hU⟩ := bounded_universal_family hκ hpow (hι.trans hκ) A B i
    (fun d ↦ (Cardinal.mk_subtype_le _).trans (hV d)) X
  refine ⟨U, j, fun W _ _ _ _ hW T f hf ↦ ?_⟩
  obtain ⟨d, e, he⟩ := hrep W hW T
  refine transfer_extension T (S d) e he (fun g hg ↦ ?_) f hf
  obtain ⟨k, hk⟩ := hU d ⟨g, hg⟩
  exact ⟨k.val, k.property, fun x ↦ congrArg (fun m : A d ⟶ U ↦ m.val x) hk⟩

/-- Every vector lattice embeds into a lattice of universal disposition for all lattices of
size at most continuum, with an explicit bound on the size of the extension. -/
theorem exists_small_universalDisposition (X : Type u) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] :
    ∃ (U : Type u) (a : AddCommGroup U) (l : Lattice U),
      letI := a
      letI := l
      ∃ o : IsOrderedAddMonoid U, letI := o
      ∃ v : VectorLattice U, letI := v
      ∃ j : VecLatHom X U, Function.Injective j ∧
        Cardinal.mk U ≤ (max (Cardinal.mk X) (2 ^ Cardinal.continuum)) ^ Cardinal.continuum ∧
        ∀ (V : Type u) [AddCommGroup V] [Lattice V] [IsOrderedAddMonoid V] [VectorLattice V],
          Cardinal.mk V ≤ Cardinal.continuum → ∀ (S : VectorSublattice V)
            (f : VecLatHom S U), Function.Injective f →
            ∃ g : VecLatHom V U, Function.Injective g ∧ ∀ x, g x.val = f x := by
  let κ := (max (Cardinal.mk X) (2 ^ Cardinal.continuum)) ^ Cardinal.continuum
  have hbase : max (Cardinal.mk X) (2 ^ Cardinal.continuum) ≤ κ :=
    Cardinal.self_le_power _ (Cardinal.one_le_aleph0.trans Cardinal.aleph0_le_continuum)
  have hpow : κ ^ Cardinal.continuum = κ := by
    rw [← Cardinal.power_mul, Cardinal.mul_eq_self Cardinal.aleph0_le_continuum]
  obtain ⟨U, ⟨j⟩, hU⟩ := bounded_universal ((le_max_right _ _).trans hbase) hpow
    ⟨X, (le_max_left _ _).trans hbase⟩
  exact ⟨U.Carrier, U.addCommGroup, U.lattice, U.isOrderedAddMonoid, U.vectorLattice,
    j.val, j.property, U.cardinal_le, hU⟩

/-- Every vector lattice embeds into a lattice of countable-prime universal disposition
whose size satisfies the same cardinal bound. -/
theorem exists_countablePrimeUniversalDisposition (X : Type u) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] :
    ∃ (U : Type u) (a : AddCommGroup U) (l : Lattice U),
      letI := a
      letI := l
      ∃ o : IsOrderedAddMonoid U, letI := o
      ∃ v : VectorLattice U, letI := v
      ∃ j : VecLatHom X U, Function.Injective j ∧
        Cardinal.mk U ≤ (max (Cardinal.mk X) (2 ^ Cardinal.continuum)) ^ Cardinal.continuum ∧
        HasCountablePrimeUniversalDisposition U := by
  obtain ⟨U, a, l, o, v, j, hj, hcard, hU⟩ := exists_small_universalDisposition X
  exact ⟨U, a, l, o, v, j, hj, hcard,
    fun V _ _ _ _ hV ↦ hU V (cardinal_le_continuum hV)⟩

/-- Every vector lattice embeds into a countable-prime-injective vector lattice
with an explicit bound on its size. -/
theorem exists_countablePrimeInjective (X : Type u) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] :
    ∃ (U : Type u) (a : AddCommGroup U) (l : Lattice U),
      letI := a
      letI := l
      ∃ o : IsOrderedAddMonoid U, letI := o
      ∃ v : VectorLattice U, letI := v
      ∃ j : VecLatHom X U, Function.Injective j ∧
        Cardinal.mk U ≤ (max (Cardinal.mk X) (2 ^ Cardinal.continuum)) ^ Cardinal.continuum ∧
        IsCountablePrimeInjective U := by
  obtain ⟨U, a, l, o, v, j, hj, hcard, hU⟩ := exists_countablePrimeUniversalDisposition X
  exact ⟨U, a, l, o, v, j, hj, hcard,
    @isCountablePrimeInjective_of_universalDisposition U a l o v hU⟩

/-- There is a nonzero lattice of countable-prime universal disposition of size at most
two to the continuum, with spectrum of size at most two to that cardinal. -/
theorem exists_nontrivial_countablePrimeUniversalDisposition :
    ∃ (U : Type u) (a : AddCommGroup U) (l : Lattice U),
      letI := a
      letI := l
      ∃ o : IsOrderedAddMonoid U, letI := o
      ∃ v : VectorLattice U, letI := v
      Nontrivial U ∧ HasCountablePrimeUniversalDisposition U ∧
        Cardinal.mk U ≤ 2 ^ Cardinal.continuum ∧
        Cardinal.mk (properPrimeIdeals U) ≤ 2 ^ ((2 : Cardinal.{u}) ^ Cardinal.continuum) := by
  obtain ⟨U, a, l, o, v, j, hj, hcard, hU⟩ :=
    exists_countablePrimeUniversalDisposition (ULift.{u} Unit → ℝ)
  have hsize : Cardinal.mk U ≤ 2 ^ Cardinal.continuum := by
    simpa [Cardinal.mk_arrow, Cardinal.mk_real, max_eq_right (Cardinal.cantor _).le,
      ← Cardinal.power_mul, Cardinal.mul_eq_self Cardinal.aleph0_le_continuum] using hcard
  exact ⟨U, a, l, o, v, hj.nontrivial, hU, hsize,
    (@spectrum_cardinal_le_powerset U a l o v).trans
      (Cardinal.power_le_power_left (by norm_num) hsize)⟩

end TransfiniteConstruction

end VectorLattice.CountableSpectra
