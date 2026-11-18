/-
Authors: Gonzalo Martínez-Fernández
-/

import FreeProducts.CountableSpectra.Basic
import FreeProducts.Archimedean.DirectedLimits
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration
import Mathlib.SetTheory.Cardinal.Regular

/-!
# Transfinite construction with cardinal bounds

Cardinally bounded vector lattices and embeddings admit the chain colimits and
amalgamations needed for transfinite constructions. Stable requirements propagate
through the iteration while the size bound is preserved.
-/

noncomputable section

universe u v w

namespace VectorLattice.CountableSpectra

section TransfiniteConstruction

open CategoryTheory CategoryTheory.Limits

/-- Predicates preserved by the iteration maps remain true in the transfinite iteration once
they have been established at the corresponding stages. -/
private lemma iteration_predicates {C : Type v} [Category.{w} C]
    {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    [NoMaxOrder J] [HasIterationOfShape J C]
    (Φ : SmallObject.SuccStruct C) (P : J → C → Prop)
    (hP : ∀ {X Y : C}, (X ⟶ Y) → ∀ j, P j X → P j Y)
    (hstep : ∀ X j, (∀ i, i < j → P i X) → P j (Φ.succ X)) :
    ∀ j, P j (Φ.iteration J) := by
  suffices h : ∀ j, P j ((Φ.iterationFunctor J).obj (Order.succ j)) from
    fun j ↦ hP (colimit.ι _ (Order.succ j)) j (h j)
  intro j
  induction j using WellFoundedLT.induction with
  | ind j ih =>
    refine hP (Φ.iterationFunctorObjSuccIso j (not_isMax j)).inv j
      (hstep ((Φ.iterationFunctor J).obj j) j (fun i hij ↦ ?_))
    exact hP ((Φ.iterationFunctor J).map (homOfLE (Order.succ_le_of_lt hij))) i (ih i hij)

/-- If each requirement can be achieved separately, construct a successor step that achieves
the next requirement while retaining those already established. -/
private lemma requirements_successor {C : Type v} [Category.{w} C]
    {J : Type u} [LinearOrder J] [WellFoundedLT J] (P : J → C → Prop)
    (hP : ∀ {X Y : C}, (X ⟶ Y) → ∀ j, P j X → P j Y)
    (step : ∀ X j, ∃ Y, ∃ _ : X ⟶ Y, P j Y) (X : C) :
    ∃ Y, ∃ _ : X ⟶ Y, ∀ j, (∀ i, i < j → P i X) → P j Y := by
  classical
  by_cases h : ∀ j, P j X
  · exact ⟨X, 𝟙 X, fun j _ ↦ h j⟩
  · obtain ⟨j, hj, hmin⟩ := wellFounded_lt.has_min {j | ¬ P j X} (not_forall.mp h)
    obtain ⟨Y, f, hf⟩ := step X j
    refine ⟨Y, f, fun i hi ↦ ?_⟩
    by_cases hPi : P i X
    · exact hP f i hPi
    · exact (le_of_not_gt (hmin i hPi)).lt_or_eq.elim
        (fun hji ↦ (hj (hi j hji)).elim) (fun hji ↦ hji ▸ hf)

/-- A transfinite iteration produces an object above the starting object satisfying every
indexed requirement that is preserved by further maps. -/
private lemma exists_iteration_satisfying {C : Type v} [Category.{w} C]
    {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    [NoMaxOrder J] [HasIterationOfShape J C]
    (P : J → C → Prop)
    (hP : ∀ {X Y : C}, (X ⟶ Y) → ∀ j, P j X → P j Y)
    (step : ∀ X j, ∃ Y, ∃ _ : X ⟶ Y, P j Y) (X : C) :
    ∃ Y, ∃ _ : X ⟶ Y, ∀ j, P j Y := by
  choose Y f hf using requirements_successor P hP step
  let Φ : SmallObject.SuccStruct C := ⟨X, Y, f⟩
  exact ⟨Φ.iteration J, Φ.ιIteration J, iteration_predicates Φ P hP hf⟩

/-- A vector lattice bundled with a bound on the cardinality of its carrier. -/
structure BoundedVectorLattice (κ : Cardinal.{u}) where
  Carrier : Type u
  [addCommGroup : AddCommGroup Carrier]
  [lattice : Lattice Carrier]
  [isOrderedAddMonoid : IsOrderedAddMonoid Carrier]
  [vectorLattice : VectorLattice Carrier]
  cardinal_le : Cardinal.mk Carrier ≤ κ

attribute [instance] BoundedVectorLattice.addCommGroup BoundedVectorLattice.lattice
  BoundedVectorLattice.isOrderedAddMonoid BoundedVectorLattice.vectorLattice

/-- The category of cardinally bounded vector lattices and injective lattice homomorphisms. -/
private instance boundedVectorLatticeCategory (κ : Cardinal.{u}) :
    Category.{u} (BoundedVectorLattice κ) where
  Hom X Y := {f : VecLatHom X.Carrier Y.Carrier // Function.Injective f}
  id _ := ⟨VecLatHom.id, Function.injective_id⟩
  comp f g := ⟨g.val.comp f.val, g.property.comp f.property⟩
  id_comp _ := Subtype.ext (DFunLike.ext _ _ (fun _ ↦ rfl))
  comp_id _ := Subtype.ext (DFunLike.ext _ _ (fun _ ↦ rfl))
  assoc _ _ _ := Subtype.ext (DFunLike.ext _ _ (fun _ ↦ rfl))

/-- The lattice homomorphism between two comparable stages of a chain of bounded vector
lattices. -/
private def boundedChainMap {κ : Cardinal.{u}} {J : Type u} [Preorder J]
    (F : J ⥤ BoundedVectorLattice κ) (i j : J) (h : i ≤ j) :
    VecLatHom (F.obj i).Carrier (F.obj j).Carrier :=
  (F.map (homOfLE h)).val

/-- The transition maps of a chain satisfy the compatibility laws for a directed system. -/
private instance boundedChainSystem {κ : Cardinal.{u}} {J : Type u} [Preorder J]
    (F : J ⥤ BoundedVectorLattice κ) :
    DirectedSystem (fun j ↦ (F.obj j).Carrier) (boundedChainMap F · · ·) where
  map_self {i} x := congrArg (fun f : F.obj i ⟶ F.obj i ↦ f.val x) (F.map_id i)
  map_map {k _j i} hij hjk x :=
    (congrArg (fun f : F.obj i ⟶ F.obj k ↦ f.val x)
      (F.map_comp (homOfLE hij) (homOfLE hjk))).symm

/-- A direct limit has cardinality at most the given infinite bound when both its stages and
its index set satisfy that bound. -/
private lemma bounded_directLimit_cardinal {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ)
    {J : Type u} [Preorder J] [IsDirectedOrder J] (hJ : Cardinal.mk J ≤ κ)
    (F : J ⥤ BoundedVectorLattice κ) :
    Cardinal.mk (DirectLimit (fun j ↦ (F.obj j).Carrier) (boundedChainMap F)) ≤ κ := by
  calc
    _ ≤ Cardinal.mk (Σ j, (F.obj j).Carrier) := Cardinal.mk_quotient_le
    _ = Cardinal.sum (fun j ↦ Cardinal.mk (F.obj j).Carrier) := Cardinal.mk_sigma _
    _ ≤ Cardinal.sum (fun _ : J ↦ κ) :=
      Cardinal.sum_le_sum _ _ (fun j ↦ (F.obj j).cardinal_le)
    _ = Cardinal.mk J * κ := Cardinal.sum_const' _ _
    _ ≤ κ * κ := mul_le_mul' hJ le_rfl
    _ = κ := Cardinal.mul_eq_self hκ

/-- The direct limit of a chain, bundled with its carrier cardinality bound. -/
private def boundedDirectLimit {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ)
    {J : Type u} [Preorder J] [IsDirectedOrder J] [Nonempty J] (hJ : Cardinal.mk J ≤ κ)
    (F : J ⥤ BoundedVectorLattice κ) : BoundedVectorLattice κ where
  Carrier := DirectLimit (fun j ↦ (F.obj j).Carrier) (boundedChainMap F)
  cardinal_le := bounded_directLimit_cardinal hκ hJ F

/-- The canonical embeddings of a chain into its bounded direct limit form a cocone. -/
private def boundedLimitCocone {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ)
    {J : Type u} [Preorder J] [IsDirectedOrder J] [Nonempty J] (hJ : Cardinal.mk J ≤ κ)
    (F : J ⥤ BoundedVectorLattice κ) : Cocone F where
  pt := boundedDirectLimit hκ hJ F
  ι :=
    { app := fun j ↦ ⟨directLimitInclusion (boundedChainMap F) j,
        DirectLimit.mk_injective (boundedChainMap F)
          (fun _i _j h ↦ (F.map (homOfLE h)).property) j⟩
      naturality := fun {i j} f ↦ Subtype.ext (DFunLike.ext _ _ (fun x ↦
        DirectLimit.mk_apply (f := boundedChainMap F) i j x (leOfHom f))) }

/-- The canonical injective homomorphism from the bounded direct limit into any other cocone. -/
private def boundedLimitDesc {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ)
    {J : Type u} [Preorder J] [IsDirectedOrder J] [Nonempty J] (hJ : Cardinal.mk J ≤ κ)
    (F : J ⥤ BoundedVectorLattice κ) (s : Cocone F) :
    boundedDirectLimit hκ hJ F ⟶ s.pt := by
  refine ⟨directLimitLift (boundedChainMap F) (fun i ↦ (s.ι.app i).val)
    (fun i j h x ↦ congrArg (fun f : F.obj i ⟶ s.pt ↦ f.val x) (s.w (homOfLE h))), ?_⟩
  exact DirectLimit.lift_injective (F := fun i ↦ (F.obj i).Carrier) (C := s.pt.Carrier)
    (boundedChainMap F) (fun i x ↦ (s.ι.app i).val x)
    (fun i _j h x ↦
      (congrArg (fun f : F.obj i ⟶ s.pt ↦ f.val x) (s.w (homOfLE h))).symm)
    (fun i ↦ (s.ι.app i).property)

/-- The bounded direct limit satisfies the colimit universal property. -/
private def boundedColimitCocone {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ)
    {J : Type u} [Preorder J] [IsDirectedOrder J] [Nonempty J] (hJ : Cardinal.mk J ≤ κ)
    (F : J ⥤ BoundedVectorLattice κ) : ColimitCocone F where
  cocone := boundedLimitCocone hκ hJ F
  isColimit :=
    { desc := boundedLimitDesc hκ hJ F
      fac := fun _ _ ↦ Subtype.ext (DFunLike.ext _ _ (fun _ ↦ rfl))
      uniq := by
        refine fun s m hm ↦ Subtype.ext (DFunLike.ext _ _ (fun z ↦ ?_))
        obtain ⟨i, x, rfl⟩ := DirectLimit.exists_eq_mk (boundedChainMap F) z
        exact congrArg (fun f : F.obj i ⟶ s.pt ↦ f.val x) (hm i) }

/-- The category of bounded vector lattices has the indicated directed colimits when the index
sets satisfy the cardinal bound. -/
private lemma bounded_hasColimits {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ)
    {J : Type u} [Preorder J] [IsDirectedOrder J] [Nonempty J] (hJ : Cardinal.mk J ≤ κ) :
    HasColimitsOfShape J (BoundedVectorLattice κ) :=
  ⟨fun F ↦ HasColimit.mk (boundedColimitCocone hκ hJ F)⟩

/-- The required chain iterations exist in the category of bounded vector lattices under the
stated bound on the indexing order. -/
lemma bounded_hasIteration {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ)
    {J : Type u} [LinearOrder J] [Nonempty J] (hJ : Cardinal.mk J ≤ κ) :
    HasIterationOfShape J (BoundedVectorLattice κ) := by
  refine { hasColimitsOfShape := bounded_hasColimits hκ hJ
           hasColimitsOfShape_of_isSuccLimit := ?_ }
  intro j hj
  let := hj.nonempty_Iio.to_subtype
  exact bounded_hasColimits hκ ((Cardinal.mk_set_le _).trans hJ)

/-- The same iterations exist in the category retaining a fixed embedding from the starting
lattice. -/
lemma under_hasIteration {C : Type v} [Category.{w} C]
    {J : Type u} [LinearOrder J] [Nonempty J] [HasIterationOfShape J C] (X : C) :
    HasIterationOfShape J (Under X) := by
  refine { hasColimitsOfShape := inferInstance
           hasColimitsOfShape_of_isSuccLimit := ?_ }
  intro j hj
  let := hj.nonempty_Iio.to_subtype
  let := HasIterationOfShape.hasColimitsOfShape_of_isSuccLimit (C := C) j hj
  infer_instance

/-- Every element of a bounded chain colimit comes from one of its stages. -/
private lemma bounded_colimit_exists_rep {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ)
    {J : Type u} [Preorder J] [IsDirectedOrder J] [Nonempty J] (hJ : Cardinal.mk J ≤ κ)
    (F : J ⥤ BoundedVectorLattice κ) [HasColimit F] (x : (colimit F).Carrier) :
    ∃ i, ∃ y : (F.obj i).Carrier, x = (colimit.ι F i).val y := by
  let e := colimit.isoColimitCocone (boundedColimitCocone hκ hJ F)
  obtain ⟨i, y, hy⟩ := DirectLimit.exists_eq_mk (boundedChainMap F) (e.hom.val x)
  refine ⟨i, y, e.hom.property ?_⟩
  exact hy.trans (congrArg (fun f : F.obj i ⟶ boundedDirectLimit hκ hJ F ↦ f.val y)
    (colimit.isoColimitCocone_ι_hom (boundedColimitCocone hκ hJ F) i)).symm

/-- An embedding whose range lies inside the range of another embedding factors through it. -/
private lemma bounded_factor_of_range {κ : Cardinal.{u}}
    {A B C : BoundedVectorLattice κ} (f : A ⟶ C) (g : B ⟶ C)
    (h : ∀ x, ∃ y, g.val y = f.val x) : ∃ k : A ⟶ B, k ≫ g = f := by
  choose k hk using h
  let L : VecLatHom A.Carrier B.Carrier := by
    refine { toFun := k, map_add' := ?_, map_smul' := ?_, map_sup' := ?_, map_inf' := ?_ } <;>
      intro x y <;> apply g.property <;> simp [hk]
  exact ⟨⟨L, fun x y hxy ↦ f.property
    ((hk x).symm.trans ((congrArg g.val hxy).trans (hk y)))⟩,
    Subtype.ext (DFunLike.ext _ _ hk)⟩

/-- An embedding into a chain colimit factors through a stage when its domain has cardinality
below the cofinality of the chain. -/
private lemma bounded_colimit_factors {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ)
    {J : Type u} [LinearOrder J] [Nonempty J] (hJ : Cardinal.mk J ≤ κ)
    (F : J ⥤ BoundedVectorLattice κ) [HasColimit F]
    (A : BoundedVectorLattice κ) (hA : Cardinal.mk A.Carrier < Order.cof J)
    (f : A ⟶ colimit F) : ∃ j, ∃ g : A ⟶ F.obj j, g ≫ colimit.ι F j = f := by
  choose index y hy using fun x : A.Carrier ↦ bounded_colimit_exists_rep hκ hJ F (f.val x)
  have hnc : ¬ IsCofinal (Set.range index) :=
    fun hc ↦ hA.not_ge ((Order.cof_le hc).trans Cardinal.mk_range_le)
  obtain ⟨j, hj⟩ := not_isCofinal_iff.mp hnc
  refine ⟨j, bounded_factor_of_range f (colimit.ι F j) (fun x ↦ ?_)⟩
  exact ⟨(F.map (homOfLE (hj (index x) ⟨x, rfl⟩).le)).val (y x),
    (congrArg (fun m : F.obj (index x) ⟶ colimit F ↦ m.val (y x))
      (colimit.w F (homOfLE (hj (index x) ⟨x, rfl⟩).le))).trans (hy x).symm⟩

/-- Extensions supplied at successor stages give an extension into the final transfinite
iteration when the domain is small relative to the indexing cofinality. -/
lemma iteration_extension {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ)
    {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    [NoMaxOrder J] (hJ : Cardinal.mk J ≤ κ)
    [HasIterationOfShape J (BoundedVectorLattice κ)]
    (Φ : SmallObject.SuccStruct (BoundedVectorLattice κ))
    {A B : BoundedVectorLattice κ} (i : A ⟶ B)
    (hA : Cardinal.mk A.Carrier < Order.cof J)
    (hstep : ∀ X (f : A ⟶ X), ∃ g : B ⟶ Φ.succ X, i ≫ g = f ≫ Φ.toSucc X)
    (f : A ⟶ Φ.iteration J) : ∃ g : B ⟶ Φ.iteration J, i ≫ g = f := by
  dsimp only [SmallObject.SuccStruct.iteration] at f ⊢
  obtain ⟨j, k, hk⟩ := bounded_colimit_factors hκ hJ (Φ.iterationFunctor J) A hA f
  obtain ⟨g, hg⟩ := hstep _ k
  refine ⟨g ≫ (Φ.iterationFunctorObjSuccIso j (not_isMax j)).inv ≫
    colimit.ι (Φ.iterationFunctor J) (Order.succ j), ?_⟩
  rw [← Category.assoc, hg, Category.assoc, ← Category.assoc (Φ.toSucc _),
    ← Φ.iterationFunctor_map_succ j (not_isMax j)]
  exact (congrArg (k ≫ ·) (colimit.w (Φ.iterationFunctor J)
    (homOfLE (Order.le_succ j)))).trans hk

/-- For each finite arity, the set of lattice normal forms has cardinality at most the
continuum. -/
private lemma normalForm_cardinal (n : ℕ) :
    Cardinal.mk (LLexpr.NormalForm n) ≤ Cardinal.continuum := by
  have hi : Function.Injective (fun N : LLexpr.NormalForm n ↦ (N.pos.coeffs, N.neg.coeffs)) := by
    rintro ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ ⟨⟨r, hr⟩, ⟨s, hs⟩⟩ h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    rfl
  have hc : Cardinal.mk (Finset (Fin n → ℝ)) ≤ Cardinal.continuum :=
    (Cardinal.mk_le_of_surjective List.toFinset_surjective).trans
      ((Cardinal.mk_list_le_max _).trans (max_le Cardinal.aleph0_le_continuum
        (by simpa [Cardinal.mk_arrow, Cardinal.mk_real] using
          Cardinal.power_nat_le (n := n) Cardinal.aleph0_le_continuum)))
  exact (Cardinal.mk_le_of_injective hi).trans (by
    simpa [Cardinal.mk_prod, Cardinal.mul_eq_self Cardinal.aleph0_le_continuum] using
      mul_le_mul' hc hc)

/-- Every element of a generated vector sublattice is obtained by applying a finite lattice
normal form to generators. -/
private lemma generated_normalForm {X : Type u} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (s : Set X)
    (x : VectorSublattice.generated s) :
    ∃ n, ∃ a : Fin n → s, ∃ N : LLexpr.NormalForm n, N.eval ((↑) ∘ a) = x.val := by
  have hx := x.property
  rw [← SetLike.mem_coe, LLexpr.generated_eq_iUnion_combinations] at hx
  simp only [Set.mem_iUnion, LLexpr.combinations, Set.mem_range] at hx
  obtain ⟨n, a, e, he⟩ := hx
  exact ⟨n, a, e.normalize, (LLexpr.normalize_eval _ _).trans he⟩

/-- A vector sublattice generated by at most the given number of elements obeys the same
cardinal bound when that bound is at least the continuum. -/
private lemma generated_cardinal_le {X : Type u} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] {κ : Cardinal.{u}}
    (hκ : Cardinal.continuum ≤ κ) (s : Set X) (hs : Cardinal.mk s ≤ κ) :
    Cardinal.mk (VectorSublattice.generated s) ≤ κ := by
  have hrep : ∀ x : VectorSublattice.generated s,
      ∃ z : Σ m, (Fin m → s) × LLexpr.NormalForm m,
        z.2.2.eval ((↑) ∘ z.2.1) = x.val := fun x ↦
    (generated_normalForm s x).elim (fun n hn ↦ hn.elim (fun a ha ↦
      ha.elim (fun N hN ↦ ⟨⟨n, a, N⟩, hN⟩)))
  choose code hcode using hrep
  have hi : Function.Injective code := by
    intro x y h
    apply Subtype.ext
    rw [← hcode x, ← hcode y, h]
  have hω : Cardinal.aleph0 ≤ κ := Cardinal.aleph0_le_continuum.trans hκ
  have hn : ∀ m, Cardinal.mk ((Fin m → s) × LLexpr.NormalForm m) ≤ κ := by
    intro m
    have hN : Cardinal.lift.{u} (Cardinal.mk (LLexpr.NormalForm m)) ≤ κ :=
      (Cardinal.lift_le.mpr (normalForm_cardinal m)).trans
        ((Cardinal.lift_continuum.le).trans hκ)
    have ha : Cardinal.mk (Fin m → s) ≤ κ := by
      simpa [Cardinal.mk_arrow] using
        (Cardinal.power_le_power_right hs).trans (Cardinal.power_nat_le (n := m) hω)
    simpa [Cardinal.mk_prod, Cardinal.mul_eq_self hω] using mul_le_mul' ha hN
  calc
    _ ≤ Cardinal.mk (Σ m, (Fin m → s) × LLexpr.NormalForm m) :=
      Cardinal.mk_le_of_injective hi
    _ = Cardinal.sum (fun m ↦ Cardinal.mk ((Fin m → s) × LLexpr.NormalForm m)) :=
      Cardinal.mk_sigma _
    _ ≤ Cardinal.sum (fun _ : ℕ ↦ κ) := Cardinal.sum_le_sum _ _ hn
    _ = Cardinal.aleph0 * κ := by simp
    _ ≤ κ * κ := mul_le_mul' hω le_rfl
    _ = κ := Cardinal.mul_eq_self hω

/-- The two factor images generate the vector lattice pushout. -/
private lemma pushout_generated {A B C : BoundedVectorLattice κ}
    {f : VecLatHom A.Carrier B.Carrier} {g : VecLatHom A.Carrier C.Carrier}
    (P : Pushout f g) (x : P.Carrier) :
    x ∈ VectorSublattice.generated (Set.range P.left ∪ Set.range P.right) := by
  let G := VectorSublattice.generated (Set.range P.left ∪ Set.range P.right)
  let a : VecLatHom B.Carrier G :=
    { LinearMap.codRestrict G.toSubmodule P.left.toLinearMap
        (fun y ↦ VectorSublattice.subset_generated _ (Or.inl ⟨y, rfl⟩)) with
      map_sup' := fun y z ↦ Subtype.ext (P.left.map_sup' y z)
      map_inf' := fun y z ↦ Subtype.ext (P.left.map_inf' y z) }
  let b : VecLatHom C.Carrier G :=
    { LinearMap.codRestrict G.toSubmodule P.right.toLinearMap
        (fun y ↦ VectorSublattice.subset_generated _ (Or.inr ⟨y, rfl⟩)) with
      map_sup' := fun y z ↦ Subtype.ext (P.right.map_sup' y z)
      map_inf' := fun y z ↦ Subtype.ext (P.right.map_inf' y z) }
  obtain ⟨R, hR, _⟩ := P.universal G a b
    (DFunLike.ext _ _ (fun z ↦ Subtype.ext (DFunLike.congr_fun P.comm z)))
  have hcomp : G.subtype.comp R = VecLatHom.id :=
    (P.universal P.Carrier P.left P.right P.comm).unique
      ⟨DFunLike.ext _ _ (fun z ↦ congrArg Subtype.val (DFunLike.congr_fun hR.1 z)),
        DFunLike.ext _ _ (fun z ↦ congrArg Subtype.val (DFunLike.congr_fun hR.2 z))⟩
      ⟨rfl, rfl⟩
  exact (show (R x).val = x from DFunLike.congr_fun hcomp x) ▸ (R x).property

/-- A pushout preserves a common cardinality bound on its factors when the bound is at least
the continuum. -/
private lemma pushout_cardinal_le {κ : Cardinal.{u}} (hκ : Cardinal.continuum ≤ κ)
    {A B C : BoundedVectorLattice κ}
    {f : VecLatHom A.Carrier B.Carrier} {g : VecLatHom A.Carrier C.Carrier}
    (P : Pushout f g) : Cardinal.mk P.Carrier ≤ κ := by
  have hs : Cardinal.mk (Set.range P.left ∪ Set.range P.right : Set P.Carrier) ≤ κ :=
    (Cardinal.mk_union_le _ _).trans
      (Cardinal.add_le_of_le (Cardinal.aleph0_le_continuum.trans hκ)
        (Cardinal.mk_range_le.trans B.cardinal_le)
        (Cardinal.mk_range_le.trans C.cardinal_le))
  exact (Cardinal.mk_le_of_injective (f := fun x ↦
    (⟨x, pushout_generated P x⟩ : VectorSublattice.generated
      (Set.range P.left ∪ Set.range P.right)))
    (fun _ _ h ↦ congrArg Subtype.val h)).trans (generated_cardinal_le hκ _ hs)

/-- The right canonical map into a pushout is injective when the opposite input map is
injective. -/
private lemma pushout_right_injective {A B C : BoundedVectorLattice κ}
    {f : VecLatHom A.Carrier B.Carrier} {g : VecLatHom A.Carrier C.Carrier}
    (P : Pushout f g) (hf : Function.Injective f) : Function.Injective P.right := by
  let Q : Pushout g f :=
    { Carrier := P.Carrier
      left := P.right
      right := P.left
      comm := P.comm.symm
      universal := fun W _ _ _ _ a b hab ↦ by
        simpa only [and_comm] using P.universal W b a hab.symm }
  exact Q.left_injective hf

/-- Amalgamate two embeddings while preserving the given cardinality bound on the lattices. -/
lemma bounded_amalgam {κ : Cardinal.{u}} (hκ : Cardinal.continuum ≤ κ)
    {A B C : BoundedVectorLattice κ} (f : A ⟶ B) (g : A ⟶ C) :
    ∃ D, ∃ a : B ⟶ D, ∃ b : C ⟶ D, f ≫ a = g ≫ b := by
  obtain ⟨P⟩ := nonempty_pushout f.val g.val
  exact ⟨⟨P.Carrier, pushout_cardinal_le hκ P⟩,
    ⟨P.left, P.left_injective g.property⟩, ⟨P.right, pushout_right_injective P f.property⟩,
    Subtype.ext P.comm⟩

/-- A transfinite iteration can satisfy a family of stable requirements whose index set embeds
into the chosen iteration order. -/
lemma indexed_iteration_satisfying {C : Type v} [Category.{w} C]
    {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    [NoMaxOrder J] [HasIterationOfShape J C] {D : Type u} (e : D ↪ J)
    (P : D → C → Prop)
    (hP : ∀ {X Y : C}, (X ⟶ Y) → ∀ d, P d X → P d Y)
    (step : ∀ X d, ∃ Y, ∃ _ : X ⟶ Y, P d Y) (X : C) :
    ∃ Y, ∃ _ : X ⟶ Y, ∀ d, P d Y := by
  let Q : J → C → Prop := fun j Y ↦ ∀ d, e d = j → P d Y
  have hstep : ∀ Y j, ∃ Z, ∃ _ : Y ⟶ Z, Q j Z := by
    intro Y j
    by_cases hj : ∃ d, e d = j
    · obtain ⟨d, rfl⟩ := hj
      exact (step Y d).imp (fun Z hZ ↦ hZ.imp
        (fun _ hf d' hd' ↦ (e.injective hd').symm ▸ hf))
    · exact ⟨Y, 𝟙 Y, fun d hd ↦ (hj ⟨d, hd⟩).elim⟩
  obtain ⟨Y, f, hf⟩ := exists_iteration_satisfying Q
    (fun g _ h d hd ↦ hP g d (h d hd)) hstep X
  exact ⟨Y, f, fun d ↦ hf (e d) d rfl⟩

end TransfiniteConstruction

end VectorLattice.CountableSpectra
