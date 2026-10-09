/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Ideles.RaySubgroup
import SICs.ClassField.Ideles.NormResidues

/-!
# Norm approximation into congruent idèles

A fractional ideal prime to a modulus has a congruent uniformizer idèle, and weak
approximation makes a principal multiple of an extension idèle congruent while its norm
is congruent at the base modulus. The resulting norm residues have the index of the
idèle class norm subgroup.

## The argument

At a prime dividing the modulus, a uniformizer idèle has component one, so its norm
is congruent. For an arbitrary idèle, mixed weak approximation imposes finitely many
open local conditions on a principal multiple, including positivity at real places and
finite ray conditions for both the extension and its norm. The quotient index then follows
from the congruent idèles covering every idèle class and the norm residue quotient.

This follows Childress, *Class Field Theory* (2009), Chapter IV, Exercise 4.23 and
Proposition 5.6(ii).
-/

noncomputable section

open IsDedekindDomain NumberField
open scoped nonZeroDivisors

namespace SIC.IdeleGroup

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- The norm of the uniformizer idèle of an ideal prime to the primes above the modulus is
congruent: its components at the primes of the modulus and at the infinite places are products
of local norms of `1`. -/
theorem norm_ofFractionalIdeal_mem_congruentSubgroup (m : Ideal (𝓞 K))
    {A : (FractionalIdeal (𝓞 L)⁰ L)ˣ}
    (hA : A ∈ FractionalIdeal.primeTo L
      (FinitePlace.placesAbove (K := K) (L := L) (FinitePlace.modulusSupport m))) :
    norm (K := K) (L := L) (ofFractionalIdeal A) ∈ congruentSubgroup Set.univ m := by
  refine (mem_congruentSubgroup_univ_iff m _).mpr ⟨?_, ?_⟩
  · intro v hv
    rw [infiniteComponent_norm_apply]
    simp_rw [infiniteComponent_ofFractionalIdeal]
    simp
  · intro v hv
    rw [finiteComponent_norm_apply]
    apply Subgroup.prod_mem
    intro w _
    let q := FinitePlace.PrimeAbove.place v w
    have hq : q ∈ FinitePlace.placesAbove (K := K) (L := L)
        (FinitePlace.modulusSupport m) :=
      (FinitePlace.mem_placesAbove _ q).mpr
        (FinitePlace.PrimeAbove.below_place v w ▸ FinitePlace.mem_modulusSupport.mpr hv)
    have hcount := (FractionalIdeal.mem_primeTo_iff.mp hA) q hq
    rw [finiteComponent_ofFractionalIdeal, hcount, zpow_zero, map_one]
    exact one_mem _

/-! ### Norm approximation and the index of norm residues -/

/-- The local norm at a finite place can be read at its place below; used by
`exists_mul_mem_congruentSubgroup_norm_mem`. -/
private theorem localNorm_mem_ray_of_below (m : Ideal (𝓞 K))
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] (u : (w.adicCompletion L)ˣ)
    (h : FinitePlace.localNorm (FinitePlace.below (K := K) w) w u ∈
      FinitePlace.rayUnitGroup m (FinitePlace.below (K := K) w)) :
    FinitePlace.localNorm v w u ∈ FinitePlace.rayUnitGroup m v := by
  have e : FinitePlace.below (K := K) w = v := FinitePlace.below_eq_of_liesOver v w
  cases e
  exact h

omit [NumberField K] [NumberField L] in
/-- Positivity of a local norm can be read at its infinite place below; used by
`exists_mul_mem_congruentSubgroup_norm_mem`. -/
private theorem localNorm_pos_of_below (v : InfinitePlace K) (w : InfinitePlace L)
    [w.LiesOver v] (u : w.Completionˣ) (hv : v.IsReal)
    (h : ∀ hw : (InfinitePlace.below (K := K) w).IsReal,
      0 < NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
        ((InfinitePlace.localNorm (InfinitePlace.below (K := K) w) w u :
          (InfinitePlace.below (K := K) w).Completionˣ) :
          (InfinitePlace.below (K := K) w).Completion)) :
    0 < NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
      ((InfinitePlace.localNorm v w u : v.Completionˣ) : v.Completion) := by
  have e : InfinitePlace.below (K := K) w = v :=
    InfinitePlace.below_eq_of_liesOver v w
  cases e
  exact h hv

/-- A fixed implication preserves openness of its consequent; used by
`isOpen_jointFiniteNeighborhood`. -/
private theorem isOpen_imp_mem {X : Type*} [TopologicalSpace X] (P : Prop)
    {s : Set X} (hs : IsOpen s) : IsOpen {x | P → x ∈ s} := by
  by_cases h : P
  · simp only [h, true_implies]
    exact hs
  · simp [h]

/-- The finite places where joint norm approximation imposes local conditions; used by
`exists_joint_local_conditions`. -/
private def jointSupport (m : Ideal (𝓞 K)) (m' : Ideal (𝓞 L)) :
    Finset (HeightOneSpectrum (𝓞 L)) := by
  classical
  exact FinitePlace.placesAbove (K := K) (L := L) (FinitePlace.modulusSupport m) ∪
    FinitePlace.modulusSupport m'

/-- The norm positivity and real positivity conditions at an infinite place; used by
`exists_joint_local_conditions`. -/
private def jointInfiniteNeighborhood (w : InfinitePlace L)
    (z : NumberField.IdeleGroup (𝓞 L) L) : Set w.Completionˣ :=
  {u | ∀ hw : (InfinitePlace.below (K := K) w).IsReal,
    0 < NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
      (((InfinitePlace.localNorm (InfinitePlace.below (K := K) w) w)
        (u * infiniteComponent L w z) :
        (InfinitePlace.below (K := K) w).Completionˣ) :
        (InfinitePlace.below (K := K) w).Completion)} ∩
  {u | ∀ hw : w.IsReal,
    0 < NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
      ((u * infiniteComponent L w z : w.Completionˣ) : w.Completion)}

/-- The norm ray and intrinsic ray conditions at a finite place; used by
`exists_joint_local_conditions`. -/
private def jointFiniteNeighborhood (m : Ideal (𝓞 K)) (m' : Ideal (𝓞 L))
    (z : NumberField.IdeleGroup (𝓞 L) L) (w : jointSupport m m') :
    Set (w.1.adicCompletion L)ˣ :=
  {u | w.1 ∈ FinitePlace.placesAbove (K := K) (L := L) (FinitePlace.modulusSupport m) →
    FinitePlace.localNorm (FinitePlace.below (K := K) w.1) w.1
      (u * finiteComponent L w.1 z) ∈
        FinitePlace.rayUnitGroup m (FinitePlace.below (K := K) w.1)} ∩
  {u | w.1 ∈ FinitePlace.modulusSupport m' →
    u * finiteComponent L w.1 z ∈ FinitePlace.rayUnitGroup m' w.1}

omit [NumberField K] in
/-- The infinite local conditions are open; used by `exists_joint_local_conditions`. -/
private theorem isOpen_jointInfiniteNeighborhood (w : InfinitePlace L)
    (z : NumberField.IdeleGroup (𝓞 L) L) :
    IsOpen (jointInfiniteNeighborhood (K := K) w z) := by
  have hnorm := (InfinitePlace.isOpen_positiveUnitGroup
    (InfinitePlace.below (K := K) w)).preimage
      ((InfinitePlace.continuous_localNorm _ _).comp
        (continuous_id.mul_const (infiniteComponent L w z)))
  have hself := (InfinitePlace.isOpen_positiveUnitGroup w).preimage
    (continuous_id.mul_const (infiniteComponent L w z))
  exact hnorm.inter hself

/-- The finite local conditions are open; used by `exists_joint_local_conditions`. -/
private theorem isOpen_jointFiniteNeighborhood (m : Ideal (𝓞 K)) (m' : Ideal (𝓞 L))
    (z : NumberField.IdeleGroup (𝓞 L) L) (w : jointSupport m m') :
    IsOpen (jointFiniteNeighborhood m m' z w) := by
  have hnorm := isOpen_imp_mem
    (w.1 ∈ FinitePlace.placesAbove (K := K) (L := L) (FinitePlace.modulusSupport m))
    ((FinitePlace.isOpen_rayUnitGroup m (FinitePlace.below (K := K) w.1)).preimage
      ((FinitePlace.continuous_localNorm _ _).comp
        (continuous_id.mul_const (finiteComponent L w.1 z))))
  have hself := isOpen_imp_mem (w.1 ∈ FinitePlace.modulusSupport m')
    ((FinitePlace.isOpen_rayUnitGroup m' w.1).preimage
      (continuous_id.mul_const (finiteComponent L w.1 z)))
  exact hnorm.inter hself

omit [NumberField K] in
/-- The inverse infinite component satisfies the conditions used by
`exists_joint_local_conditions`. -/
private theorem jointInfiniteNeighborhood_nonempty (w : InfinitePlace L)
    (z : NumberField.IdeleGroup (𝓞 L) L) :
    (jointInfiniteNeighborhood (K := K) w z).Nonempty := by
  refine ⟨(infiniteComponent L w z)⁻¹, ?_, ?_⟩
  · intro hw
    simp
  · intro hw
    simp

/-- The inverse finite component satisfies the conditions used by
`exists_joint_local_conditions`. -/
private theorem jointFiniteNeighborhood_nonempty (m : Ideal (𝓞 K)) (m' : Ideal (𝓞 L))
    (z : NumberField.IdeleGroup (𝓞 L) L) (w : jointSupport m m') :
    (jointFiniteNeighborhood m m' z w).Nonempty := by
  refine ⟨(finiteComponent L w.1 z)⁻¹, ?_, ?_⟩
  · intro _
    simp
  · intro _
    simp

/-- Weak approximation provides one global unit satisfying both sets of local conditions; used
by `exists_mul_mem_congruentSubgroup_norm_mem`. -/
private theorem exists_joint_local_conditions (m : Ideal (𝓞 K)) (m' : Ideal (𝓞 L))
    (z : NumberField.IdeleGroup (𝓞 L) L) :
    ∃ b : Lˣ, (∀ w : InfinitePlace L,
      Units.map (algebraMap L w.Completion : L →* w.Completion) b ∈
        jointInfiniteNeighborhood (K := K) w z) ∧
      ∀ w : jointSupport m m',
        Units.map (algebraMap L (w.1.adicCompletion L) : L →* w.1.adicCompletion L) b ∈
          jointFiniteNeighborhood m m' z w := by
  exact exists_units_map_mem_of_isOpen (jointSupport m m')
    (fun w => isOpen_jointInfiniteNeighborhood w z)
    (fun w => isOpen_jointFiniteNeighborhood m m' z w)
    (fun w => jointInfiniteNeighborhood_nonempty w z)
    (fun w => jointFiniteNeighborhood_nonempty m m' z w)

/-- **Joint norm approximation**: every idèle `z` of `L` has a principal multiple $\beta z$ that is
congruent for a modulus `m'` of `L` and whose norm is congruent for a modulus `m` of `K`.
Childress, *Class Field Theory*, Chapter IV, Exercise 4.23, in idèlic form, with the congruence
conditions of `L` added to the open conditions of the approximation. -/
theorem exists_mul_mem_congruentSubgroup_norm_mem (m : Ideal (𝓞 K)) (m' : Ideal (𝓞 L))
    (z : NumberField.IdeleGroup (𝓞 L) L) :
    ∃ b : Lˣ, NumberField.IdeleGroup.unitEmbedding (𝓞 L) L b * z ∈ congruentSubgroup Set.univ m' ∧
      norm (K := K) (L := L) (NumberField.IdeleGroup.unitEmbedding (𝓞 L) L b * z) ∈
        congruentSubgroup Set.univ m := by
  classical
  obtain ⟨b, hbI, hbF⟩ := exists_joint_local_conditions (K := K) (L := L) m m' z
  refine ⟨b, (mem_congruentSubgroup_univ_iff m' _).mpr ⟨?_, ?_⟩,
    (mem_congruentSubgroup_univ_iff m _).mpr ⟨?_, ?_⟩⟩
  · intro w hw
    have hbw := (hbI w).2 hw
    rw [map_mul, infiniteComponent_unitEmbedding, Units.val_mul]
    exact hbw
  · intro w hw
    have hwS : w ∈ FinitePlace.modulusSupport m' := FinitePlace.mem_modulusSupport.mpr hw
    have hwU : w ∈ jointSupport m m' := Finset.mem_union.mpr (Or.inr hwS)
    have hbw := (hbF ⟨w, hwU⟩).2 hwS
    rw [map_mul, finiteComponent_unitEmbedding]
    exact hbw
  · intro v hv
    rw [infiniteComponent_norm_apply]
    rw [Units.coe_prod, map_prod]
    apply Finset.prod_pos
    intro w _
    have : w.1.LiesOver v := w.2
    have hw := (hbI w.1).1
    rw [map_mul, infiniteComponent_unitEmbedding]
    exact localNorm_pos_of_below v w.1 _ hv hw
  · intro v hv
    rw [finiteComponent_norm_apply]
    apply Subgroup.prod_mem
    intro w _
    let q := FinitePlace.PrimeAbove.place v w
    have hbelow : FinitePlace.below (K := K) q = v :=
      FinitePlace.PrimeAbove.below_place v w
    have hqT : q ∈ FinitePlace.placesAbove (K := K) (L := L)
        (FinitePlace.modulusSupport m) :=
      (FinitePlace.mem_placesAbove _ q).mpr
        (hbelow ▸ FinitePlace.mem_modulusSupport.mpr hv)
    have hqU : q ∈ jointSupport m m' := Finset.mem_union.mpr (Or.inl hqT)
    have hw := (hbF ⟨q, hqU⟩).1 hqT
    rw [map_mul, finiteComponent_unitEmbedding]
    exact localNorm_mem_ray_of_below m v q _ hw

/-- **Norm approximation**: every idèle of `L` has a principal multiple whose norm is congruent.
Childress, *Class Field Theory*, Chapter IV, Exercise 4.23, in idèlic form. -/
theorem exists_norm_mul_mem_congruentSubgroup (m : Ideal (𝓞 K))
    (z : NumberField.IdeleGroup (𝓞 L) L) :
    ∃ b : Lˣ, norm (K := K) (L := L) (NumberField.IdeleGroup.unitEmbedding (𝓞 L) L b * z) ∈
      congruentSubgroup Set.univ m := by
  obtain ⟨b, _, hb⟩ := exists_mul_mem_congruentSubgroup_norm_mem (K := K) (L := L) m ⊤ z
  exact ⟨b, hb⟩

/-- The norm residues among congruent idèles have index $[C_K : N_{L/K}C_L]$:
$[J^+_{K,\mathfrak m} : J^+_{K,\mathfrak m}\cap K^\times N_{L/K}J_L] = [C_K : N_{L/K}C_L]$.
Childress, *Class Field Theory*, Chapter IV, proof of Proposition 5.6(ii). -/
theorem relIndex_congruentSubgroup_inf (m : Ideal (𝓞 K)) :
    (congruentSubgroup Set.univ m ⊓ (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔
        (norm (K := K) (L := L)).range)).relIndex (congruentSubgroup Set.univ m) =
      Nat.card (NumberField.IdeleClassGroup (𝓞 K) K ⧸
        (IdeleClassGroup.norm (K := K) (L := L)).range) := by
  let H := congruentSubgroup Set.univ m
  let C := NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔
    (norm (K := K) (L := L)).range
  have hsup : H ⊔ C = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    obtain ⟨a, ha⟩ := exists_unitEmbedding_mul_mem_congruentSubgroup Set.univ m x
    have hp : (NumberField.IdeleGroup.unitEmbedding (𝓞 K) K a)⁻¹ ∈ C :=
      (le_sup_left : NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ≤ C)
        (show (NumberField.IdeleGroup.unitEmbedding (𝓞 K) K a)⁻¹ ∈
        NumberField.IdeleGroup.principalSubgroup (𝓞 K) K from
          ⟨a⁻¹, by simp⟩)
    exact Subgroup.mem_sup.mpr ⟨_, ha, _, hp, by simp [mul_assoc, mul_comm]⟩
  change (H ⊓ C).relIndex H = _
  rw [inf_comm, Subgroup.inf_relIndex_right, ← Subgroup.relIndex_sup_right H C,
    hsup, Subgroup.relIndex_top_right, Subgroup.index_eq_card]
  exact Nat.card_congr (IdeleClassGroup.normResidueEquiv (K := K) (L := L)).toEquiv


end SIC.IdeleGroup
