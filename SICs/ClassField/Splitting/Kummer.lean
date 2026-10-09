/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Splitting.ComplementaryKummer
import SICs.ClassField.Reciprocity.NormGroups

/-!
# Complete splitting through Kummer extensions

If $\mu_n\subset K$, the Galois group of the abelian extension `L/K` has exponent dividing `n`,
and the image of $K_v^\times$ in $C_K$ consists of norms from `L` at a finite place `v`, then `v`
splits completely in `L`.

This module follows Childress, *Class Field Theory* (2009), Chapter VI, Theorem 2.9, at finite
places. It supplies the Kummer case of the prime-degree splitting theorem of
`SICs.ClassField.Splitting.PrimeDegree`.

## The argument

Choose a finite set `S` of primes containing `v`, the primes ramified in `L`, the primes dividing
`n`, and primes representing the ideal classes. Let $B_1$ be the free power subgroup
unrestricted only at `v`, and $M_1$ the Kummer field of the complementary subgroup
$B_2$, unrestricted everywhere except at `v`. Then $N_{M_1/K}C_{M_1}$ is the image of $B_1$
(`range_norm_freePowerKummer`).

The image of $B_1$ lies in $N_{L/K}C_L$ (`map_freePowerSubgroup_le`): `n`th powers of idèle
classes are norms because $\operatorname{Gal}(L/K)$ has exponent dividing `n`, unit idèles away
from `S` are norms because `L/K` is unramified there, and $K_v^\times$ maps into norms by
hypothesis. By the Ordering Theorem (`nonempty_algHom_of_range_norm_le`), `L` embeds in $M_1$ over
`K`. The radicands of $M_1$ are local `n`th powers at `v`, so `v` splits completely in $M_1$
(`finrank_adicCompletion_freePowerKummer`), and local degrees multiply in towers, so `v` splits
completely in `L`.
-/

noncomputable section

open IsDedekindDomain NumberField
open scoped SIC.FinitePlace NumberField.LiesOver SIC.InfinitePlace

namespace SIC

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-! ### Common support and norm containment -/

/-- Chooses the finite support used by `FinitePlace.finrank_eq_one_of_pow_eq_one`. -/
private theorem exists_splitting_kummer_support {n : ℕ} [NeZero n]
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), S₀ ⊆ S ∧
      FinitePlace.ramifiedSet K L ⊆ S ∧
      (∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) ∧
      Function.Surjective (IdeleGroup.sIdealClass (K := K) (L := K) S) := by
  classical
  obtain ⟨S, hS, hnS, hclass⟩ :=
    IdeleGroup.exists_support_sIdealClass (K := K) (L := K) n
      (S₀ ∪ FinitePlace.ramifiedSet K L)
  refine ⟨S, Finset.subset_union_left.trans hS,
    Finset.subset_union_right.trans hS, ?_, ?_⟩
  · intro v hv
    simpa only [FinitePlace.placesAbove_self] using hnS v hv
  · rw [FinitePlace.placesAbove_self] at hclass
    exact hclass

/-- The norm containment of the free-power Kummer field gives the embedding used by
`FinitePlace.finrank_eq_one_of_pow_eq_one`. -/
private theorem nonempty_algHom_freePowerKummer {n : ℕ} [NeZero n] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) [IsAbelianGalois K L]
    (hexp : ∀ σ : L ≃ₐ[K] L, σ ^ n = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hram : FinitePlace.ramifiedSet K L ⊆ S)
    (hnS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hclass : Function.Surjective (IdeleGroup.sIdealClass (K := K) (L := K) S))
    (I : Set (InfinitePlace K)) (T : Set (HeightOneSpectrum (𝓞 K)))
    (hinf : ∀ v ∈ I, (NumberField.IdeleClassGroup.ofCompletion (𝓞 K) K v).range ≤
      (IdeleClassGroup.norm (K := K) (L := L)).range)
    (hfin : ∀ v ∈ S, v ∈ T →
      (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 K) K v).range ≤
        (IdeleClassGroup.norm (K := K) (L := L)).range) :
    Nonempty (L →ₐ[K] IdeleGroup.freePowerKummer K n S Iᶜ Tᶜ) := by
  let M := IdeleGroup.freePowerKummer K n S Iᶜ Tᶜ
  have : IsAbelianGalois K M :=
    IdeleGroup.freePowerKummer_isAbelianGalois hζ S Iᶜ Tᶜ
  apply nonempty_algHom_of_range_norm_le (K := K) (L := L) (M := M)
  rw [show (IdeleClassGroup.norm (K := K) (L := M)).range =
    (IdeleGroup.freePowerSubgroup n S I T).map
      (QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K)) by
    simpa only [M] using IdeleGroup.range_norm_freePowerKummer hζ S hnS hclass I T]
  exact IdeleGroup.map_freePowerSubgroup_le S I T
    (IdeleClassGroup.pow_mem_range_norm hexp)
    (IdeleGroup.map_awayUnitSubgroup_le_range_norm S hram) hinf hfin

/-- **Complete splitting for exponent `n` at a finite place**: if $\mu_n\subset K$, every
automorphism of the abelian extension `L/K` satisfies $\sigma^n = 1$, and the image of
$K_v^\times$ in $C_K$ lies in $N_{L/K}C_L$, then $[L_w:K_v] = 1$ for every `w` above `v`.
Childress, *Class Field Theory*, Chapter VI, Theorem 2.9. -/
theorem FinitePlace.finrank_eq_one_of_pow_eq_one {n : ℕ} [NeZero n] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) [IsAbelianGalois K L] (hexp : ∀ σ : L ≃ₐ[K] L, σ ^ n = 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 K) K v).range ≤
      (IdeleClassGroup.norm (K := K) (L := L)).range)
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] :
    Module.finrank (v.adicCompletion K) (w.adicCompletion L) = 1 := by
  classical
  obtain ⟨S, hSv, hram, hnS, hclass⟩ :=
    exists_splitting_kummer_support (K := K) (L := L) (n := n) {v}
  have hvS : v ∈ S := hSv (Finset.mem_singleton_self v)
  let M := IdeleGroup.freePowerKummer K n S (∅ : Set (InfinitePlace K))ᶜ
    ({v} : Set (HeightOneSpectrum (𝓞 K)))ᶜ
  let _ : IsAbelianGalois K M :=
    IdeleGroup.freePowerKummer_isAbelianGalois hζ S (∅ : Set (InfinitePlace K))ᶜ {v}ᶜ
  obtain ⟨f⟩ := nonempty_algHom_freePowerKummer hζ hexp S hram hnS hclass
    ∅ {v} (by intro t ht; simp at ht) (by intro t _ ht; rcases ht with rfl; exact hv)
  let _ : Algebra L M := f.toRingHom.toAlgebra
  have _ : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  let u₀ : FinitePlace.PrimeAbove (L := M) w := Classical.choice inferInstance
  let u := FinitePlace.PrimeAbove.place w u₀
  let _ : u.asIdeal.LiesOver w.asIdeal := FinitePlace.PrimeAbove.place_liesOver w u₀
  have _ : u.asIdeal.LiesOver v.asIdeal :=
    Ideal.LiesOver.trans u.asIdeal w.asIdeal v.asIdeal
  have hu : Module.finrank (v.adicCompletion K) (u.adicCompletion M) = 1 :=
    IdeleGroup.finrank_adicCompletion_freePowerKummer hζ S
      (∅ : Set (InfinitePlace K))ᶜ {v}ᶜ hvS
      (by simp) u
  exact Nat.eq_one_of_mul_eq_one_right
    ((FinitePlace.finrank_mul_finrank v w u).trans hu)

end SIC
