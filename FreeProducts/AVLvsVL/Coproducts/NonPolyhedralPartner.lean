/-
Authors: Gonzalo Martínez-Fernández
-/

import FreeProducts.AVLvsVL.Coproducts.CoveringCriterion

/-!
# A partner witnessing failure of Archimedeanity

The distance to a nonpolyhedral closed cone defines a closed partner cone in one
additional dimension. This pair fails the covering criterion, so its ordinary coproduct
is not Archimedean.
-/

universe u

namespace VectorLattice.ConeRepresentation

/-- The closed cone lying below the distance to `C`. -/
def distancePartner {n : ℕ} (C : ClosedCone n) : ClosedCone (n + 1) where
  carrier := {z | ∀ x ∈ C.carrier, z (Fin.last n) ≤ dist x (fun i ↦ z i.castSucc)}
  isClosed := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun x ↦ isClosed_iInter (fun _ ↦
      isClosed_le (continuous_apply _) (continuous_const.dist
        (continuous_pi (fun i ↦ continuous_apply i.castSucc)))))
  zero_mem := fun _ _ ↦ dist_nonneg
  smul_mem := by
    intro r hr z hz x hx
    rcases hr.eq_or_lt with rfl | hr
    · simp only [zero_smul, Pi.zero_apply]
      exact dist_nonneg
    · have hx' := C.smul_mem r⁻¹ (inv_nonneg.mpr hr.le) x hx
      have h := mul_le_mul_of_nonneg_left (hz (r⁻¹ • x) hx') hr.le
      have hd : r * dist (r⁻¹ • x) (fun i ↦ z i.castSucc) =
          dist x (r • fun i ↦ z i.castSucc) := by
        have hd := dist_smul₀ r (r⁻¹ • x) (fun i ↦ z i.castSucc)
        rw [smul_inv_smul₀ hr.ne', Real.norm_of_nonneg hr.le] at hd
        exact hd.symm
      rw [hd] at h
      exact h

/-- A point lies outside the distance partner exactly when its last coordinate exceeds its
distance from some point of the original cone. -/
private lemma mem_compl_distancePartner {n : ℕ} (C : ClosedCone n) (z : Fin (n + 1) → ℝ) :
    z ∈ (distancePartner C).carrierᶜ ↔
      ∃ x ∈ C.carrier, dist x (fun i ↦ z i.castSucc) < z (Fin.last n) := by
  simp only [distancePartner, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le,
    exists_prop]

/-- The zero-height section of the closure of the partner's complement recovers the original
cone. -/
private lemma distancePartner_closure_section {n : ℕ} (C : ClosedCone n) (y : Fin n → ℝ) :
    Fin.snoc y 0 ∈ closure (distancePartner C).carrierᶜ ↔ y ∈ C.carrier := by
  constructor
  · intro hy
    by_contra hyC
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp C.isClosed.isOpen_compl y hyC
    let S : Set (Fin (n + 1) → ℝ) :=
      {z | ε ≤ dist y (fun i ↦ z i.castSucc) + z (Fin.last n)}
    have hS : IsClosed S := isClosed_le continuous_const
      ((continuous_const.dist (continuous_pi (fun i ↦ continuous_apply i.castSucc))).add
        (continuous_apply _))
    have hsub : (distancePartner C).carrierᶜ ⊆ S := by
      intro z hz
      obtain ⟨x, hx, hxz⟩ := (mem_compl_distancePartner C z).mp hz
      have he : ε ≤ dist y x := le_of_not_gt (fun h ↦ hball (by
        simpa only [Metric.mem_ball, dist_comm] using h) hx)
      have ht := dist_triangle y (fun i ↦ z i.castSucc) x
      rw [dist_comm (fun i ↦ z i.castSucc) x] at ht
      change ε ≤ dist y (fun i ↦ z i.castSucc) + z (Fin.last n)
      linarith
    have hz := closure_minimal hsub hS hy
    have : ε ≤ 0 := by simpa [S] using hz
    exact hε.not_ge this
  · intro hy
    have hcont : Continuous (fun t : ℝ ↦ (Fin.snoc y t : Fin (n + 1) → ℝ)) := by
      apply continuous_pi
      intro i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp only [Fin.snoc_last, Fin.snoc_castSucc]
      · exact continuous_id
      · exact continuous_const
    have hzero : (0 : ℝ) ∈ closure (Set.Ioi 0) := by simp
    apply closure_mono (t := (distancePartner C).carrierᶜ) ?_
      (mem_closure_image hcont.continuousAt hzero)
    rintro _ ⟨t, ht, rfl⟩
    apply (mem_compl_distancePartner C _).mpr
    exact ⟨y, hy, by simpa using ht⟩

/-- For a nonpolyhedral cone, the complement of its distance partner cannot be open
polyhedral. -/
private lemma distancePartner_compl_not_polyhedral {n : ℕ} (C : ClosedCone n)
    (hC : ¬ IsClosedPolyhedralCone C.carrier) :
    ¬ IsOpenPolyhedralCone (distancePartner C).carrierᶜ := by
  intro h
  let T : (Fin n → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) :=
    LinearMap.pi (Fin.snoc (fun i ↦ LinearMap.proj i) 0)
  have hT (x : Fin n → ℝ) : T x = Fin.snoc x 0 := by
    ext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp [T]
  apply hC
  convert closedPolyhedral_preimage (closedPolyhedral_closure h) T using 1
  ext x
  simp only [Set.mem_preimage, hT, distancePartner_closure_section]

/-- A nonempty finite family of strict homogeneous linear inequalities defines an open
polyhedral cone. -/
private lemma openPolyhedral_strict {n : ℕ} {ι : Type*} [Finite ι] [Nonempty ι]
    (L : ι → (Fin n → ℝ) →ₗ[ℝ] ℝ) : IsOpenPolyhedralCone {x | ∀ i, 0 < L i x} := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Fintype.card_pos (α := ι)))
  let e : ι ≃ Fin (r + 1) := (Fintype.equivFin ι).trans (finCongr hr)
  refine ⟨1, fun _ ↦ r, fun _ j ↦ L (e.symm j), Set.ext fun x ↦ ?_⟩
  simpa only [Set.mem_ofPred_eq, exists_const] using
    e.symm.surjective.forall (p := fun i ↦ 0 < L i x)

/-- A strict supremum-distance inequality between two linear maps defines an open polyhedral
cone. -/
private lemma openPolyhedral_dist_lt {k n : ℕ}
    (A B : (Fin k → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (t : (Fin k → ℝ) →ₗ[ℝ] ℝ) :
    IsOpenPolyhedralCone {z | dist (A z) (B z) < t z} := by
  let d (i : Fin n) := (LinearMap.proj i).comp A - (LinearMap.proj i).comp B
  let L : Option (Fin n × Bool) → (Fin k → ℝ) →ₗ[ℝ] ℝ :=
    Option.elim' t (fun p ↦ if p.2 then t + d p.1 else t - d p.1)
  convert openPolyhedral_strict L using 1
  ext z
  constructor
  · intro hz
    have ht : 0 < t z := dist_nonneg.trans_lt hz
    rintro (_ | ⟨i, _ | _⟩)
    · exact ht
    · have hi := (dist_pi_lt_iff ht).mp hz i
      rw [Real.dist_eq, abs_lt] at hi
      change 0 < t z - (A z i - B z i)
      linarith [hi.2]
    · have hi := (dist_pi_lt_iff ht).mp hz i
      rw [Real.dist_eq, abs_lt] at hi
      change 0 < t z + (A z i - B z i)
      linarith [hi.1]
  · intro hz
    have ht : 0 < t z := hz none
    apply (dist_pi_lt_iff ht).mpr
    intro i
    rw [Real.dist_eq, abs_lt]
    have hp : 0 < t z - (A z i - B z i) := hz (some (i, false))
    have hn : 0 < t z + (A z i - B z i) := hz (some (i, true))
    constructor <;> linarith

/-- A nonpolyhedral cone and its distance partner admit no polyhedral cover. -/
lemma distancePartner_not_cover {n : ℕ} (C : ClosedCone n)
    (hC : ¬ IsClosedPolyhedralCone C.carrier) : ¬ HasPolyhedralCover C (distancePartner C) := by
  intro hcover
  let A : (Fin (n + (n + 1)) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    LinearMap.pi (fun i ↦ LinearMap.proj (i.castAdd (n + 1)))
  let B : (Fin (n + (n + 1)) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    LinearMap.pi (fun i ↦ LinearMap.proj (i.castSucc.natAdd n))
  let t : (Fin (n + (n + 1)) → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj ((Fin.last n).natAdd n)
  let W := {z | dist (A z) (B z) < t z}
  have hdisj : Disjoint W (productCone C (distancePartner C)).carrier := by
    apply Set.disjoint_left.mpr
    intro z hz hprod
    exact not_lt_of_ge (hprod.2 _ hprod.1) hz
  obtain ⟨U, V, _, hV, hUC, hVD, hUV⟩ :=
    hcover W (openPolyhedral_dist_lt A B t) hdisj
  apply distancePartner_compl_not_polyhedral C hC
  have heq : V = (distancePartner C).carrierᶜ := by
    apply Set.Subset.antisymm
    · exact fun _ hz ↦ Set.disjoint_left.mp hVD hz
    · intro z hz
      obtain ⟨x, hx, hxz⟩ := (mem_compl_distancePartner C z).mp hz
      have hw : Fin.append x z ∈ W := by
        change dist (fun i ↦ Fin.append x z (i.castAdd (n + 1)))
          (fun i : Fin n ↦ Fin.append x z (i.castSucc.natAdd n)) <
            Fin.append x z ((Fin.last n).natAdd n)
        simpa only [Fin.append_left, Fin.append_right] using hxz
      have h := hUV (Fin.append x z) hw
      simp only [Fin.append_left, Fin.append_right] at h
      exact h.resolve_left (fun hu ↦ Set.disjoint_left.mp hUC hu hx)
  exact heq ▸ hV

/-- A nonpolyhedral closed cone has a partner in one higher dimension
whose product has vanishing relations not generated by the factors. -/
theorem exists_partner_strict_productRelationsIdeal {n : ℕ}
    (C : ClosedCone n) (hC : ¬ IsClosedPolyhedralCone C.carrier) :
    ∃ D : ClosedCone (n + 1),
      productRelationsIdeal C D < vanishingIdeal (productCone C D) := by
  refine ⟨distancePartner C, lt_of_le_not_ge (productRelationsIdeal_le_vanishingIdeal _ _) ?_⟩
  intro h
  exact distancePartner_not_cover C hC ((vanishingIdeal_le_productRelationsIdeal_iff _ _).mp h)

end VectorLattice.ConeRepresentation
