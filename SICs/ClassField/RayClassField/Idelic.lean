/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Ideles.RayClassComparison
import SICs.ClassField.Splitting.UnramifiedPrimes

/-!
# Ray subgroups as norm groups

The unit idèles away from the support of a modulus are ray idèles for every infinite support,
and a finite abelian extension whose norm group is a ray subgroup of modulus `m` is unramified at
the primes coprime to `m`.

These are the local inputs of the idèlic construction of ray class fields from Childress,
*Class Field Theory* (2009), Chapters V–VI. The first is the
hypothesis of the existence theorem `exists_intermediateField_range_norm_eq` for a ray subgroup;
the second places the primes coprime to `m` outside the ramification set, where the global Artin
map gives Frobenius. Both are used by the narrow ray class field of
`SICs.ClassField.RayClassField.Narrow`.

## The argument

The ray subgroup is a product of local conditions. A unit idèle away from the support of `m` is
one at the infinite places and at the primes dividing `m`, and an integral unit elsewhere, where
the finite condition is the full group of integral units. In particular, for a prime
$\mathfrak p$ coprime to `m`, the integral units at $\mathfrak p$ are ray idèles, so their
classes are norms from `H`, and every prime above $\mathfrak p$ is unramified
(`FinitePlace.ramificationIdx_eq_one_of_map_le_range_norm`).

## References

- Childress, *Class Field Theory* (2009), Chapter VI, Theorems 2.7 and 3.4
-/

noncomputable section

namespace SIC

open IsDedekindDomain NumberField
open scoped SIC.FinitePlace NumberField.LiesOver SIC.InfinitePlace

universe u

variable {K : Type u} [Field K] [NumberField K]

/-! ### Local factors of the ray subgroup

The ray subgroup is a product of local conditions: unit idèles away from the support of the
modulus satisfy them for any infinite support, and at a prime coprime to the modulus the finite
condition is the full group of integral units. -/

/-- The unit idèles away from the support of `m` are ray idèles, for every infinite support `P`:
the existence hypothesis of `exists_intermediateField_range_norm_eq` for the ray subgroups. -/
theorem awayUnitSubgroup_le_rayIdeleSubgroup (P : Set (InfinitePlace K))
    (m : Ideal (𝓞 K)) :
    IdeleGroup.awayUnitSubgroup (FinitePlace.modulusSupport m) ≤
      IdeleGroup.raySubgroup P m := by
  intro x hx
  obtain ⟨hinf, hsupport, hunit⟩ :=
    (IdeleGroup.mem_awayUnitSubgroup (FinitePlace.modulusSupport m) x).mp hx
  apply (IdeleGroup.mem_raySubgroup_iff P m x).mpr
  constructor
  · intro w
    rw [hinf w]
    exact (InfinitePlace.rayUnitGroup P w).one_mem
  · intro v
    by_cases hv : v ∈ FinitePlace.modulusSupport m
    · rw [hsupport v hv]
      exact (FinitePlace.rayUnitGroup m v).one_mem
    · rw [FinitePlace.rayUnitGroup_eq_of_exponent_eq_zero
        (by simpa using (FinitePlace.mem_modulusSupport).not.mp hv)]
      exact hunit v hv

/-- The image of the integral units at a prime coprime to `m` lies in the ray subgroup for every
infinite support `P`; the local input of `rayNorm_ramificationIdx_one`. -/
private theorem map_unitGroup_le_rayIdeleClassSubgroup (P : Set (InfinitePlace K))
    (m : Ideal (𝓞 K)) (v : HeightOneSpectrum (𝓞 K)) (hv : IsCoprime v.asIdeal m) :
    (FinitePlace.unitGroup v).map (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 K) K v) ≤
      IdeleClassGroup.raySubgroup P m := by
  rintro c ⟨x, hx, rfl⟩
  change (NumberField.IdeleGroup.ofAdicCompletion (𝓞 K) K v x :
    NumberField.IdeleClassGroup (𝓞 K) K) ∈ _
  apply (IdeleClassGroup.mem_raySubgroup_iff P m _).mpr
  refine ⟨NumberField.IdeleGroup.ofAdicCompletion (𝓞 K) K v x, ?_, rfl⟩
  apply (IdeleGroup.mem_raySubgroup_iff P m _).mpr
  constructor
  · intro w
    rw [IdeleGroup.infiniteComponent_ofAdicCompletion]
    exact (InfinitePlace.rayUnitGroup P w).one_mem
  · intro w
    by_cases hw : w = v
    · subst w
      rw [IdeleGroup.finiteComponent_ofAdicCompletion_self,
        FinitePlace.rayUnitGroup_eq_of_exponent_eq_zero
          (FinitePlace.modulusExponent_eq_zero_of_isCoprime v hv)]
      exact hx
    · rw [IdeleGroup.finiteComponent_ofAdicCompletion_of_ne K v w hw]
      exact (FinitePlace.rayUnitGroup m w).one_mem

/-! ### Norm-group consequences

The finite ray factors give unramifiedness at the primes away from `m`. -/

/-- A field whose norm group is a ray subgroup of modulus `m` is unramified at the primes coprime
to `m`. Childress, *Class Field Theory*, Chapter VI, Theorem 3.4. -/
theorem rayNorm_ramificationIdx_one (P : Set (InfinitePlace K))
    (m : Ideal (𝓞 K)) {H : Type*} [Field H] [NumberField H] [Algebra K H]
    [IsAbelianGalois K H]
    (hU : (IdeleClassGroup.norm (K := K) (L := H)).range =
      IdeleClassGroup.raySubgroup P m)
    (v : HeightOneSpectrum (𝓞 K)) (hv : IsCoprime v.asIdeal m)
    (w : HeightOneSpectrum (𝓞 H)) [w.asIdeal.LiesOver v.asIdeal] :
    w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  apply FinitePlace.ramificationIdx_eq_one_of_map_le_range_norm v
    (by simpa only [hU] using map_unitGroup_le_rayIdeleClassSubgroup P m v hv) w

/-- A prime ray ideal is outside the finite ramification set of a field whose norm group is a
ray subgroup of modulus `m`; restates `rayNorm_ramificationIdx_one` for
`globalArtin_ofAdicCompletion`. -/
theorem rayNorm_notMem_ramifiedSet (P : Set (InfinitePlace K))
    (m : Ideal (𝓞 K)) {H : Type*} [Field H] [NumberField H] [Algebra K H]
    [IsAbelianGalois K H]
    (hU : (IdeleClassGroup.norm (K := K) (L := H)).range =
      IdeleClassGroup.raySubgroup P m)
    (I : RayIdeal K m) (hI : I.1.IsPrime) :
    (⟨I.1, hI, RayIdeal.ne_bot I⟩ : HeightOneSpectrum (𝓞 K)) ∉
      FinitePlace.ramifiedSet K H := by
  intro hv
  obtain ⟨w, hbelow, hram⟩ := FinitePlace.mem_ramifiedSet.mp hv
  let v : HeightOneSpectrum (𝓞 K) := ⟨I.1, hI, RayIdeal.ne_bot I⟩
  have : w.asIdeal.LiesOver v.asIdeal :=
    ⟨congrArg HeightOneSpectrum.asIdeal hbelow.symm⟩
  exact hram (rayNorm_ramificationIdx_one P m hU v (RayIdeal.isCoprime I) w)

end SIC

end
