/-
Authors: Gonzalo Martínez-Fernández
-/

import BanLat.Quotient

/-!
# Prime ideals of vector lattices

Prime ideals characterize totally ordered quotients. They extend from vector sublattices,
pull back along lattice homomorphisms, and separate nonzero elements.
-/

universe u

namespace OrderIdeal

variable {X : Type u} [AddCommGroup X] [Lattice X]
  [IsOrderedAddMonoid X] [VectorLattice X]

/-- An order ideal is prime when the infimum of two elements being zero
forces at least one of them to belong to the ideal. -/
def IsPrime (P : OrderIdeal X) : Prop :=
  ∀ a b : X, a ⊓ b = 0 → a ∈ P ∨ b ∈ P

/-- An ideal quotient is totally ordered exactly when the ideal is prime. -/
theorem isTotal_quotient_iff_isPrime (P : OrderIdeal X) :
    Std.Total (α := X ⧸ P.toSubmodule) (· ≤ ·) ↔ P.IsPrime := by
  constructor
  · intro ht a b hab
    have hzero : P.mkQ a ⊓ P.mkQ b = 0 := by rw [← P.mkQ_inf, hab, map_zero]
    exact (ht.total (P.mkQ a) (P.mkQ b)).elim
      (fun h ↦ Or.inl ((Submodule.Quotient.mk_eq_zero P.toSubmodule).mp
        ((inf_eq_left.mpr h).symm.trans hzero)))
      (fun h ↦ Or.inr ((Submodule.Quotient.mk_eq_zero P.toSubmodule).mp
        ((inf_eq_right.mpr h).symm.trans hzero)))
  · intro hP
    refine ⟨fun a b ↦ ?_⟩
    obtain ⟨x, rfl⟩ := P.toSubmodule.mkQ_surjective a
    obtain ⟨y, rfl⟩ := P.toSubmodule.mkQ_surjective b
    have h : P.mkQ (x - y)⁺ = 0 ∨ P.mkQ (x - y)⁻ = 0 :=
      (hP _ _ (posPart_inf_negPart_eq_zero (x - y))).imp
        (fun h ↦ (Submodule.Quotient.mk_eq_zero P.toSubmodule).mpr h)
        (fun h ↦ (Submodule.Quotient.mk_eq_zero P.toSubmodule).mpr h)
    simpa only [← P.mkQVecLatHom_apply, VecLatHom.map_posPart, VecLatHom.map_negPart,
      posPart_eq_zero, negPart_eq_zero, map_sub, sub_nonpos, sub_nonneg] using h

/-- Restricting a prime ideal to a vector sublattice gives a prime ideal. -/
theorem exists_prime_restriction (Y : VectorSublattice X)
    (P : OrderIdeal X) (hP : P.IsPrime) :
    ∃ Q : OrderIdeal Y, Q.IsPrime ∧
      ∀ y : Y, y ∈ Q ↔ (y : X) ∈ P := by
  refine ⟨OrderIdeal.ofSolid (P.toSubmodule.comap Y.toSubmodule.subtype)
    (fun x y hx hy ↦ P.mem_of_abs_le_abs hx hy), ?_, fun _ ↦ Iff.rfl⟩
  exact fun a b h ↦ hP a b (congrArg (fun y : Y ↦ (y : X)) h)

/-- If an infimum belongs to a prime ideal, at least one of its two operands belongs to that
ideal. -/
private lemma prime_mem_or_mem {P : OrderIdeal X} (hP : P.IsPrime) {a b : X}
    (h : a ⊓ b ∈ P) : a ∈ P ∨ b ∈ P := by
  have hzero : P.mkQ a ⊓ P.mkQ b = 0 :=
    (P.mkQ_inf a b).symm.trans ((Submodule.Quotient.mk_eq_zero P.toSubmodule).mpr h)
  exact ((isTotal_quotient_iff_isPrime P).mpr hP).total (P.mkQ a) (P.mkQ b) |>.elim
    (fun h ↦ Or.inl ((Submodule.Quotient.mk_eq_zero P.toSubmodule).mp
      ((inf_eq_left.mpr h).symm.trans hzero)))
    (fun h ↦ Or.inr ((Submodule.Quotient.mk_eq_zero P.toSubmodule).mp
      ((inf_eq_right.mpr h).symm.trans hzero)))

/-- Modulo an ideal, an element of its sum with a principal ideal is dominated by a
nonnegative multiple of the principal generator. -/
private lemma quotient_abs_le_of_mem_sup_principal (Q : OrderIdeal X) (a : X)
    {x : X} (hx : x ∈ Q ⊔ principal a) :
    ∃ r : ℝ, 0 ≤ r ∧ |Q.mkQ x| ≤ r • |Q.mkQ a| := by
  obtain ⟨q, hq, p, hp, hqp⟩ := Submodule.mem_sup.mp hx
  obtain ⟨r, hr, hpr⟩ := mem_principal.mp hp
  have hq0 : Q.mkQ q = 0 := (Submodule.Quotient.mk_eq_zero Q.toSubmodule).mpr hq
  have hxp : Q.mkQ x = Q.mkQ p := by rw [← hqp, map_add, hq0, zero_add]
  exact ⟨r, hr, (congrArg abs hxp).le.trans
    (by simpa only [mkQVecLatHom_apply, mkQ_abs, map_smul] using
      Q.mkQVecLatHom.monotone hpr)⟩

/-- Adjoining two disjoint principal generators to an ideal makes the infimum of the
corresponding absolute values belong to the original ideal. -/
private lemma inf_abs_mem_of_disjoint (Q : OrderIdeal X) {a b x y : X}
    (hab : a ⊓ b = 0) (hx : x ∈ Q ⊔ principal a) (hy : y ∈ Q ⊔ principal b) :
    |x| ⊓ |y| ∈ Q := by
  obtain ⟨r, hr, hxr⟩ := quotient_abs_le_of_mem_sup_principal Q a hx
  obtain ⟨s, hs, hys⟩ := quotient_abs_le_of_mem_sup_principal Q b hy
  have hd : r • |Q.mkQ a| ⊓ s • |Q.mkQ b| = 0 := by
    simpa only [IsVLDisjoint, abs_smul', abs_of_nonneg hr, abs_of_nonneg hs,
      mkQVecLatHom_apply] using
      ((isVLDisjoint_of_inf_eq_zero (Q.mkQVecLatHom.map_disjoint hab)).smul_left r).smul_right s
  have hzero : |Q.mkQ x| ⊓ |Q.mkQ y| = 0 :=
    le_antisymm ((inf_le_inf hxr hys).trans_eq hd) (le_inf (abs_nonneg _) (abs_nonneg _))
  exact (Submodule.Quotient.mk_eq_zero Q.toSubmodule).mp
    (show Q.mkQ (|x| ⊓ |y|) = 0 from
      by simpa only [Q.mkQ_inf, Q.mkQ_abs] using hzero)

/-- Generating an ambient ideal from an ideal of a sublattice introduces no new elements of
that sublattice. -/
private lemma mem_generated_image (Y : VectorSublattice X) (P : OrderIdeal Y)
    (y : Y) (hy : (y : X) ∈ generated ((↑) '' (P : Set Y))) : y ∈ P := by
  obtain ⟨t, c, ht, _, hle⟩ := mem_generated_iff.mp hy
  have hs : ∑ x ∈ t, c x • |x| ∈ P.toSubmodule.map Y.toSubmodule.subtype := by
    refine Submodule.sum_mem _ (fun x hx ↦ ?_)
    obtain ⟨p, hp, rfl⟩ := ht x hx
    exact ⟨c p • |p|, P.toSubmodule.smul_mem _ (P.abs_mem hp), rfl⟩
  obtain ⟨p, hp, heq⟩ := hs
  exact P.mem_of_abs_mem (P.solid hp (abs_nonneg y)
    (show |(y : X)| ≤ (p : X) from hle.trans_eq heq.symm))

/-- The union of a nonempty chain of order ideals is an order ideal. -/
private lemma exists_ideal_chain_union {s : Set (OrderIdeal X)} (hne : s.Nonempty)
    (hc : IsChain (· ≤ ·) s) :
    ∃ Q : OrderIdeal X, ∀ x, x ∈ Q ↔ ∃ J ∈ s, x ∈ J := by
  have hd : DirectedOn (· ≤ ·) ((fun J : OrderIdeal X ↦ J.toSubmodule) '' s) := by
    rintro _ ⟨J, hJ, rfl⟩ _ ⟨K, hK, rfl⟩
    exact let ⟨L, hL, hJL, hKL⟩ := hc.directedOn J hJ K hK
      ⟨L.toSubmodule, ⟨L, hL, rfl⟩, hJL, hKL⟩
  let M := sSup ((fun J : OrderIdeal X ↦ J.toSubmodule) '' s)
  have hm (x : X) : x ∈ M ↔ ∃ J ∈ s, x ∈ J := by
    exact (Submodule.mem_sSup_of_directed (hne.image _) hd).trans
      ⟨fun ⟨_, ⟨J, hJ, rfl⟩, hx⟩ ↦ ⟨J, hJ, hx⟩,
        fun ⟨J, hJ, hx⟩ ↦ ⟨J.toSubmodule, ⟨J, hJ, rfl⟩, hx⟩⟩
  exact ⟨ofSolid M (fun x y hx hxy ↦ (hm y).mpr
    (let ⟨J, hJ, hxJ⟩ := (hm x).mp hx;
      ⟨J, hJ, J.mem_of_abs_le_abs hxJ hxy⟩)), hm⟩

/-- Enlarging a maximal ideal with prescribed restriction must introduce a sublattice element
outside that restriction. -/
private lemma maximal_restriction_witness (Y : VectorSublattice X) (P : OrderIdeal Y)
    {Q : OrderIdeal X} (hQ : Maximal (fun Q ↦ ∀ y : Y, (y : X) ∈ Q ↔ y ∈ P) Q)
    {a : X} (ha : a ∉ Q) : ∃ y : Y, (y : X) ∈ Q ⊔ principal a ∧ y ∉ P := by
  by_contra! hn
  have heq : Q ⊔ principal a = Q := hQ.eq_of_ge
    (fun y ↦ ⟨hn y, fun hy ↦ (show Q ≤ Q ⊔ principal a from le_sup_left)
      ((hQ.prop y).mpr hy)⟩) le_sup_left
  exact ha (heq ▸ (show a ∈ Q ⊔ principal a from
    (show principal a ≤ Q ⊔ principal a from le_sup_right) (self_mem_principal a)))

/-- An ideal maximal among those restricting to a given prime ideal is itself prime. -/
private lemma maximal_restriction_isPrime (Y : VectorSublattice X) (P : OrderIdeal Y)
    (hP : P.IsPrime) {Q : OrderIdeal X}
    (hQ : Maximal (fun Q ↦ ∀ y : Y, (y : X) ∈ Q ↔ y ∈ P) Q) : Q.IsPrime := by
  intro a b hab
  by_contra! hn
  obtain ⟨y, hy, hyP⟩ := maximal_restriction_witness Y P hQ hn.1
  obtain ⟨z, hz, hzP⟩ := maximal_restriction_witness Y P hQ hn.2
  exact (prime_mem_or_mem hP ((hQ.prop (|y| ⊓ |z|)).mp
    (inf_abs_mem_of_disjoint Q hab hy hz))).elim
      (fun h ↦ hyP (P.mem_of_abs_mem h)) (fun h ↦ hzP (P.mem_of_abs_mem h))

/-- Every prime ideal of a vector sublattice is the restriction of a prime
ideal of the ambient vector lattice. -/
theorem exists_prime_extension (Y : VectorSublattice X)
    (P : OrderIdeal Y) (hP : P.IsPrime) :
    ∃ Q : OrderIdeal X, Q.IsPrime ∧
      ∀ y : Y, (y : X) ∈ Q ↔ y ∈ P := by
  let S : Set (OrderIdeal X) := {Q | ∀ y : Y, (y : X) ∈ Q ↔ y ∈ P}
  have hJ : generated ((↑) '' (P : Set Y)) ∈ S := fun y ↦
    ⟨mem_generated_image Y P y,
      fun hy ↦ subset_generated _ ⟨y, hy, rfl⟩⟩
  have hchain : ∀ s ⊆ S, IsChain (· ≤ ·) s →
      ∀ J ∈ s, ∃ Q ∈ S, ∀ K ∈ s, K ≤ Q := by
    intro s hs hc J hJ
    obtain ⟨Q, hQ⟩ := exists_ideal_chain_union ⟨J, hJ⟩ hc
    refine ⟨Q, fun y ↦ ⟨?_, fun hy ↦ (hQ y).mpr ⟨J, hJ, (hs hJ y).mpr hy⟩⟩,
      fun K hK x hx ↦ (hQ x).mpr ⟨K, hK, hx⟩⟩
    exact fun hy ↦ (hQ y).mp hy |>.elim (fun K ⟨hK, hyK⟩ ↦ (hs hK y).mp hyK)
  obtain ⟨Q, _, hQ⟩ := zorn_le_nonempty₀ S hchain _ hJ
  exact ⟨Q, maximal_restriction_isPrime Y P hP hQ, hQ.prop⟩

/-- Every nonzero vector is omitted by some ideal maximal with that omission property. -/
private lemma exists_maximal_not_mem {x : X} (hx : x ≠ 0) :
    ∃ Q : OrderIdeal X, Maximal (fun Q ↦ x ∉ Q) Q := by
  let S : Set (OrderIdeal X) := {Q | x ∉ Q}
  have hbot : (⊥ : OrderIdeal X) ∈ S := fun h ↦ hx (mem_bot.mp h)
  have hchain : ∀ s ⊆ S, IsChain (· ≤ ·) s →
      ∀ J ∈ s, ∃ Q ∈ S, ∀ K ∈ s, K ≤ Q := by
    intro s hs hc J hJ
    obtain ⟨Q, hQ⟩ := exists_ideal_chain_union ⟨J, hJ⟩ hc
    exact ⟨Q, fun hxQ ↦ ((hQ x).mp hxQ).elim (fun K ⟨hK, hxK⟩ ↦ hs hK hxK),
      fun K hK y hy ↦ (hQ y).mpr ⟨K, hK, hy⟩⟩
  exact (zorn_le_nonempty₀ S hchain ⊥ hbot).imp (fun _ h ↦ h.2)

/-- Adjoining any vector outside such a maximal ideal forces the previously omitted vector
into the enlarged ideal. -/
private lemma maximal_not_mem_sup {x a : X} {Q : OrderIdeal X}
    (hQ : Maximal (fun Q ↦ x ∉ Q) Q) (ha : a ∉ Q) : x ∈ Q ⊔ principal a := by
  by_contra hx
  have heq : Q ⊔ principal a = Q := hQ.eq_of_ge hx le_sup_left
  exact ha (heq ▸ (show a ∈ Q ⊔ principal a from
    (show principal a ≤ Q ⊔ principal a from le_sup_right) (self_mem_principal a)))

/-- Prime ideals separate nonzero vectors: each nonzero vector is omitted by a prime ideal. -/
lemma exists_prime_not_mem {x : X} (hx : x ≠ 0) :
    ∃ Q : OrderIdeal X, Q.IsPrime ∧ x ∉ Q := by
  obtain ⟨Q, hQ⟩ := exists_maximal_not_mem hx
  refine ⟨Q, fun a b hab ↦ ?_, hQ.prop⟩
  by_contra! hn
  have h : |x| ⊓ |x| ∈ Q := inf_abs_mem_of_disjoint Q hab
    (maximal_not_mem_sup hQ hn.1) (maximal_not_mem_sup hQ hn.2)
  exact hQ.prop (Q.mem_of_abs_mem (by simpa only [inf_idem] using h))

/-- The inverse image of a prime ideal under a lattice homomorphism is a prime ideal. -/
lemma prime_comap {Y : Type u} [AddCommGroup Y] [Lattice Y]
    [IsOrderedAddMonoid Y] [VectorLattice Y] (f : VecLatHom X Y)
    (P : OrderIdeal Y) (hP : P.IsPrime) :
    ∃ Q : OrderIdeal X, Q.IsPrime ∧ ∀ x, x ∈ Q ↔ f x ∈ P := by
  refine ⟨ofSolid (P.toSubmodule.comap f.toLinearMap) ?_,
    fun a b hab ↦ hP _ _ (f.map_disjoint hab), fun _ ↦ Iff.rfl⟩
  exact fun x y hx hle ↦ P.mem_of_abs_le_abs (x := f x) (y := f y) hx
    (by simpa only [VecLatHom.map_abs] using f.monotone hle)

end OrderIdeal
