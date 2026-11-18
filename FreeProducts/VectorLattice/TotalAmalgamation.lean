/-
Authors: Gonzalo Martínez-Fernández
-/

import BanLat.Quotient
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Geometry.Convex.Cone.Pointed

/-!
# Amalgamation of totally ordered vector lattices

Extending a salient cone to a total order constructs a common totally ordered target
for two embeddings of a common totally ordered vector lattice. The resulting square
commutes and both maps into the target are injective.
-/

universe u

namespace VectorLattice

/-- The supremum of a nonempty chain of salient cones remains salient: it contains no nonzero
vector together with its negative. -/
private lemma cone_sSup_chain_salient {V : Type u} [AddCommGroup V] [Module ℝ V]
    {s : Set (PointedCone ℝ V)} (hne : s.Nonempty) (hc : IsChain (· ≤ ·) s)
    (hs : ∀ C ∈ s, ∀ x ∈ C, -x ∈ C → x = 0) :
    ∀ x ∈ sSup s, -x ∈ sSup s → x = 0 := by
  intro x hx hn
  obtain ⟨C, hC, hCx⟩ := (Submodule.mem_sSup_of_directed hne hc.directedOn).mp hx
  obtain ⟨D, hD, hDn⟩ := (Submodule.mem_sSup_of_directed hne hc.directedOn).mp hn
  obtain ⟨K, hK, hCK, hDK⟩ := hc.directedOn C hC D hD
  exact hs K hK x (hCK hCx) (hDK hDn)

/-- Adjoining the nonnegative ray of a vector preserves salience if the negative vector is
outside the original cone. -/
private lemma cone_sup_ray_salient {V : Type u} [AddCommGroup V] [Module ℝ V]
    (C : PointedCone ℝ V)
    (hC : ∀ x ∈ C, -x ∈ C → x = 0) {v : V} (hv : -v ∉ C) :
    ∀ x ∈ C ⊔ Submodule.span {r : ℝ // 0 ≤ r} ({v} : Set V),
      -x ∈ C ⊔ Submodule.span {r : ℝ // 0 ≤ r} ({v} : Set V) → x = 0 := by
  intro x hx hn
  obtain ⟨a, ha, p, hp, hax⟩ := Submodule.mem_sup.mp hx
  obtain ⟨b, hb, q, hq, hbx⟩ := Submodule.mem_sup.mp hn
  obtain ⟨⟨r, hr⟩, rfl⟩ := Submodule.mem_span_singleton.mp hp
  obtain ⟨⟨s, hs⟩, rfl⟩ := Submodule.mem_span_singleton.mp hq
  have heq : a + b + (r + s) • v = 0 := by
    simpa only [Nonneg.mk_smul, add_smul, add_add_add_comm, add_neg_cancel] using
      congrArg₂ (· + ·) hax hbx
  by_cases hz : r + s = 0
  · obtain ⟨hr0, hs0⟩ := (add_eq_zero_iff_of_nonneg hr hs).mp hz
    simp only [Nonneg.mk_smul, hr0, hs0, zero_smul, add_zero] at hax hbx
    exact hC x (hax ▸ ha) (hbx ▸ hb)
  · have he : a + b = (r + s) • (-v) := by
      simpa only [smul_neg, eq_neg_iff_add_eq_zero] using heq
    exact (hv ((C.smul_mem_iff (lt_of_le_of_ne (add_nonneg hr hs) (Ne.symm hz))).mp
      (he ▸ C.add_mem ha hb))).elim

/-- Every salient cone extends to a salient cone that contains either a vector or its
negative, defining a total order. -/
private lemma exists_total_cone {V : Type u} [AddCommGroup V] [Module ℝ V]
    (C : PointedCone ℝ V) (hC : ∀ x ∈ C, -x ∈ C → x = 0) :
    ∃ D : PointedCone ℝ V, C ≤ D ∧ (∀ x ∈ D, -x ∈ D → x = 0) ∧
      ∀ x, x ∈ D ∨ -x ∈ D := by
  let S : Set (PointedCone ℝ V) := {D | C ≤ D ∧ ∀ x ∈ D, -x ∈ D → x = 0}
  obtain ⟨D, hCD, hD⟩ := zorn_le_nonempty₀ S (by
    intro s hs hc D hD
    exact ⟨sSup s, ⟨(hs hD).1.trans (le_sSup hD),
      cone_sSup_chain_salient ⟨D, hD⟩ hc (fun K hK ↦ (hs hK).2)⟩,
      fun K hK ↦ le_sSup hK⟩) C ⟨le_rfl, hC⟩
  refine ⟨D, hCD, hD.prop.2, fun x ↦ ?_⟩
  by_contra! hx
  have heq : D ⊔ Submodule.span {r : ℝ // 0 ≤ r} ({x} : Set V) = D :=
    hD.eq_of_ge ⟨hCD.trans le_sup_left, cone_sup_ray_salient D hD.prop.2 hx.2⟩ le_sup_left
  exact hx.1 (heq ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self x))

variable {X Y Z : Type u}
  [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X]
  [AddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y] [VectorLattice Y]
  [AddCommGroup Z] [Lattice Z] [IsOrderedAddMonoid Z] [VectorLattice Z]

/-- Describes the kernel of the linear amalgam quotient in terms of pairs arising from the
common domain. -/
private lemma amalgam_mk_eq_zero (f : VecLatHom Z X) (g : VecLatHom Z Y)
    (x : X) (y : Y) :
    (LinearMap.range (f.toLinearMap.prod (-g.toLinearMap))).mkQ (x, y) = 0 ↔
      ∃ z, f z = x ∧ g z = -y := by
  simp [LinearMap.mem_range, LinearMap.prod_apply, Function.prod, neg_eq_iff_eq_neg]
  rfl

/-- Injectivity of the right input map makes the left factor map into the linear amalgam
injective. -/
private lemma amalgam_left_injective (f : VecLatHom Z X) (g : VecLatHom Z Y)
    (hg : Function.Injective g) :
    Function.Injective ((LinearMap.range (f.toLinearMap.prod (-g.toLinearMap))).mkQ.comp
      (LinearMap.inl ℝ X Y)) := by
  refine (injective_iff_map_eq_zero _).mpr ?_
  intro x hx
  obtain ⟨z, hz, hgz⟩ := (amalgam_mk_eq_zero f g x 0).mp hx
  have hz0 : z = 0 := hg (hgz.trans (by simp))
  simpa only [hz0, map_zero] using hz.symm

/-- Injectivity of the left input map makes the right factor map into the linear amalgam
injective. -/
private lemma amalgam_right_injective (f : VecLatHom Z X) (g : VecLatHom Z Y)
    (hf : Function.Injective f) :
    Function.Injective ((LinearMap.range (f.toLinearMap.prod (-g.toLinearMap))).mkQ.comp
      (LinearMap.inr ℝ X Y)) := by
  refine (injective_iff_map_eq_zero _).mpr ?_
  intro y hy
  obtain ⟨z, hfz, hgz⟩ := (amalgam_mk_eq_zero f g 0 y).mp hy
  have hz0 : z = 0 := hf (hfz.trans (map_zero f).symm)
  simpa only [hz0, map_zero, zero_eq_neg] using hgz

/-- With both input maps injective, the linear amalgam quotient kills no nonzero positive
pair. -/
private lemma amalgam_positive_ker (f : VecLatHom Z X) (g : VecLatHom Z Y)
    (hf : Function.Injective f) (hg : Function.Injective g) (p : X × Y)
    (hp : 0 ≤ p)
    (h : (LinearMap.range (f.toLinearMap.prod (-g.toLinearMap))).mkQ p = 0) :
    p = 0 := by
  obtain ⟨z, hfz, hgz⟩ := (amalgam_mk_eq_zero f g p.1 p.2).mp h
  have hz0 : z = 0 := le_antisymm
    (g.le_of_map_le hg (by simpa only [map_zero, hgz] using neg_nonpos.mpr hp.2))
    (f.le_of_map_le hf (by simpa only [map_zero, hfz, Prod.fst_zero] using hp.1))
  exact Prod.ext (hfz.symm.trans (by simp [hz0]))
    (neg_injective (hgz.symm.trans (by simp [hz0])))

/-- The image of a positive cone is salient when the linear map kills no nonzero positive
vector. -/
private lemma map_positive_salient {V W : Type u}
    [AddCommGroup V] [PartialOrder V] [IsOrderedAddMonoid V]
    [Module ℝ V] [PosSMulMono ℝ V] [AddCommGroup W] [Module ℝ W]
    (q : V →ₗ[ℝ] W) (hker : ∀ v, 0 ≤ v → q v = 0 → v = 0) :
    ∀ w ∈ (PointedCone.positive ℝ V).map q,
      -w ∈ (PointedCone.positive ℝ V).map q → w = 0 := by
  rintro w ⟨a, ha, rfl⟩ ⟨b, hb, hbq⟩
  change q b = -q a at hbq
  have hab : a + b = 0 := hker _ (add_nonneg ha hb)
    (by rw [map_add, hbq, add_neg_cancel])
  exact (congrArg q ((add_eq_zero_iff_of_nonneg ha hb).mp hab).1).trans q.map_zero

/-- A salient total cone defines a linear order compatible with addition and nonnegative
scalar multiplication. -/
private lemma linearOrder_of_total_cone {V : Type u} [AddCommGroup V] [Module ℝ V]
    (C : PointedCone ℝ V) (hC : ∀ x ∈ C, -x ∈ C → x = 0)
    (ht : ∀ x, x ∈ C ∨ -x ∈ C) :
    ∃ l : LinearOrder V, letI := l
      IsOrderedAddMonoid V ∧ PosSMulMono ℝ V ∧ ∀ x, 0 ≤ x ↔ x ∈ C := by
  classical
  let po := C.toConvexCone.toPartialOrder C.zero_mem (fun x hx hn hx' ↦ hn (hC x hx hx'))
  let l : LinearOrder V :=
    { po with
      le_total := fun x y ↦ show y - x ∈ C ∨ x - y ∈ C from
        by simpa only [neg_sub] using ht (y - x)
      toDecidableLE := Classical.decRel _ }
  let := l
  refine ⟨l, C.toConvexCone.to_isOrderedAddMonoid C.zero_mem
    (fun x hx hn hx' ↦ hn (hC x hx hx')), ?_, ?_⟩
  · refine ⟨fun {r} hr {x y} hxy ↦ ?_⟩
    change r • y - r • x ∈ C
    simpa only [smul_sub] using C.smul_mem hr (show y - x ∈ C from hxy)
  · exact fun x ↦ show x - 0 ∈ C ↔ x ∈ C by simp only [sub_zero]

/-- A monotone linear map from a totally ordered vector lattice preserves the lattice
operations. -/
private lemma isVecLatHom_of_monotone_total [Std.Total (α := X) (· ≤ ·)]
    (f : X →ₗ[ℝ] Y) (hf : Monotone f) : IsVecLatHom f := by
  classical
  let := Lattice.toLinearOrder X
  exact
    { map_add := f.map_add
      map_smul := f.map_smul
      map_sup' := hf.map_sup
      map_inf' := hf.map_inf }

/-- A totally ordered amalgam embeds two vector lattices into a common
totally ordered vector lattice while identifying their common domain. -/
structure TotalAmalgam (f : VecLatHom Z X) (g : VecLatHom Z Y) where
  Carrier : Type u
  [addCommGroup : AddCommGroup Carrier]
  [lattice : Lattice Carrier]
  [isOrderedAddMonoid : IsOrderedAddMonoid Carrier]
  [vectorLattice : VectorLattice Carrier]
  [isTotal : Std.Total (α := Carrier) (· ≤ ·)]
  left : VecLatHom X Carrier
  right : VecLatHom Y Carrier
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  comm : left.comp f = right.comp g

attribute [instance] TotalAmalgam.addCommGroup TotalAmalgam.lattice
  TotalAmalgam.isOrderedAddMonoid TotalAmalgam.vectorLattice TotalAmalgam.isTotal

/-- Totally ordered vector lattices admit totally ordered amalgams over
injective homomorphisms from a common totally ordered vector lattice. -/
theorem nonempty_totalAmalgam
    [Std.Total (α := X) (· ≤ ·)] [Std.Total (α := Y) (· ≤ ·)]
    [Std.Total (α := Z) (· ≤ ·)]
    (f : VecLatHom Z X) (g : VecLatHom Z Y)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Nonempty (TotalAmalgam f g) := by
  let N := LinearMap.range (f.toLinearMap.prod (-g.toLinearMap))
  obtain ⟨C, hC, hs, ht⟩ := exists_total_cone
    ((PointedCone.positive ℝ (X × Y)).map N.mkQ)
    (map_positive_salient N.mkQ (amalgam_positive_ker f g hf hg))
  obtain ⟨l, ho, hm, hpos⟩ := linearOrder_of_total_cone C hs ht
  let := l
  let := ho
  let := hm
  let : VectorLattice ((X × Y) ⧸ N) := {}
  let a := N.mkQ.comp (LinearMap.inl ℝ X Y)
  let b := N.mkQ.comp (LinearMap.inr ℝ X Y)
  have ha : Positive a := fun x hx ↦ (hpos _).mpr (hC ⟨(x, 0), ⟨hx, le_rfl⟩, rfl⟩)
  have hb : Positive b := fun y hy ↦ (hpos _).mpr (hC ⟨(0, y), ⟨le_rfl, hy⟩, rfl⟩)
  refine ⟨{ Carrier := (X × Y) ⧸ N
            left := VecLatHom.ofIsVecLatHom a
              (isVecLatHom_of_monotone_total a (Positive.monotone_iff.mpr ha))
            right := VecLatHom.ofIsVecLatHom b
              (isVecLatHom_of_monotone_total b (Positive.monotone_iff.mpr hb))
            left_injective := amalgam_left_injective f g hg
            right_injective := amalgam_right_injective f g hf
            comm := ?_ }⟩
  apply DFunLike.ext
  intro z
  change N.mkQ (f z, 0) = N.mkQ (0, g z)
  rw [← sub_eq_zero, ← map_sub]
  simpa only [Prod.mk_sub_mk, sub_zero, zero_sub] using
    (amalgam_mk_eq_zero f g (f z) (-g z)).mpr ⟨z, rfl, (neg_neg _).symm⟩

end VectorLattice
