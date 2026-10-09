/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Reciprocity.GlobalArtinMap

/-!
# The norm group of an S-unit Kummer field

When $\mu_n\subset K$ and `S` contains the primes dividing `n` and represents the ideal classes,
the norm group of $M = K(\sqrt[n]{\mathcal O_{K,S}^\times})$ is the image $\overline E$ in $C_K$
of the idèles that are nth powers at `S` and infinity and units elsewhere.

This module follows Childress, *Class Field Theory* (2009), Chapter VI, Theorem 2.6, with the
roots-of-unity calculation of Neukirch's Bonn Lectures, Chapter III, Proposition 7.7 as a
cross-check. It supplies the Kummer step of the existence theorem
`exists_intermediateField_range_norm_eq`.

## The argument

The Galois group of `M/K` has exponent dividing `n` (`sUnitKummer_aut_pow`), so the global Artin
map kills the nth powers of idèle classes (`IdeleClassGroup.pow_mem_range_norm`). `M/K` is
unramified outside `S` (`ramificationIdx_sUnitKummer`), so the classes of unit idèles away from
`S` are norms (`map_awayUnitSubgroup_le_range_norm`). These two containments give
$\overline E\subseteq\ker\operatorname{Art}_{M/K} =
N_{M/K}C_M$. Both groups have index $n^{|S|+r_1+r_2}$: the first by
`index_powerSubgroup_sup_principal` (Milne's local and principal power indices), the second by
`IdeleClassGroup.index_range_norm` and the Kummer degree (`finrank_sUnitKummer_eq_pow`). So they
are equal. Here `S` lists finite primes and the infinite places are added, as in Childress's
$\#S$.

Childress shows the opposite inclusion directly, from $[J_K:K^\times B] = n^{\#S}$; the index of
$K^\times E$ is the same computation (Milne, *Class Field Theory*, Chapter VII, Lemmas
6.5–6.7). `powerSubgroup_le_range_norm` is not used: it assumes $[M:K]\mid n$, whereas here
$[M:K] = n^{|S|+r_1+r_2}$.
-/

noncomputable section

open IsDedekindDomain NumberField

namespace SIC.IdeleGroup

variable {K : Type*} [Field K] [NumberField K]

/-- The image of the local power subgroup lies in the norm group of the S-unit Kummer field;
this is the containment used by `range_norm_sUnitKummer`. -/
private theorem map_powerSubgroup_le_range_norm {n : ℕ} [NeZero n] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hnS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    (powerSubgroup n S ∅).map
        (QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K)) ≤
      (IdeleClassGroup.norm (K := K) (L := sUnitKummer K n S)).range := by
  let _ : IsAbelianGalois K (sUnitKummer K n S) :=
    sUnitKummer_isAbelianGalois hζ (NeZero.pos n) S
  have hram : FinitePlace.ramifiedSet K (sUnitKummer K n S) ⊆ S := by
    apply (FinitePlace.ramifiedSet_subset_iff S).mpr
    intro w hw
    let _ : w.asIdeal.LiesOver (FinitePlace.below (K := K) w).asIdeal :=
      FinitePlace.liesOver_below w
    exact ramificationIdx_sUnitKummer S (FinitePlace.below (K := K) w) hw
      (fun hp => hw (hnS _ hp)) w
  exact map_powerSubgroup_le S
    (IdeleClassGroup.pow_mem_range_norm (sUnitKummer_aut_pow hζ (NeZero.pos n) S))
    (map_awayUnitSubgroup_le_range_norm S hram)

/-- **Kummer existence**: when $\mu_n\subset K$ and `S` contains the primes dividing `n` and
represents the ideal classes, the norm group of $K(\sqrt[n]{\mathcal O_{K,S}^\times})$ is the
image of the idèles that are nth powers at `S` and infinity and units elsewhere.
Childress, *Class Field Theory*, Chapter VI, Theorem 2.6. -/
theorem range_norm_sUnitKummer {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hnS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hclass : Function.Surjective (sIdealClass (K := K) (L := K) S)) :
    (IdeleClassGroup.norm (K := K) (L := sUnitKummer K n S)).range =
      (powerSubgroup n S ∅).map
        (QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K)) := by
  let _ : IsAbelianGalois K (sUnitKummer K n S) :=
    sUnitKummer_isAbelianGalois hζ (NeZero.pos n) S
  let q := QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K)
  let A := (powerSubgroup n S ∅).map q
  let N := (IdeleClassGroup.norm (K := K) (L := sUnitKummer K n S)).range
  have hAN : A ≤ N := map_powerSubgroup_le_range_norm hζ S hnS
  have hAindex : A.index = n ^ (S.card + Nat.card (InfinitePlace K)) := by
    change ((powerSubgroup n S ∅).map q).index = _
    rw [Subgroup.index_map, QuotientGroup.ker_mk', QuotientGroup.range_mk',
      Subgroup.index_top, mul_one]
    exact index_powerSubgroup_sup_principal hζ (NeZero.pos n) S hnS hclass
  have hNindex : N.index = n ^ (S.card + Nat.card (InfinitePlace K)) := by
    change (IdeleClassGroup.norm (K := K) (L := sUnitKummer K n S)).range.index = _
    rw [IdeleClassGroup.index_range_norm, finrank_sUnitKummer_eq_pow hζ (NeZero.pos n) S]
  exact (SIC.Subgroup.eq_of_le_of_index_eq A N hAN (hAindex.trans hNindex.symm)
    (hNindex.symm ▸ ne_of_gt (pow_pos (NeZero.pos n) _))).symm

end SIC.IdeleGroup
