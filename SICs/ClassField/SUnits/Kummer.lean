/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.FieldTheory.Kummer.Degree
import SICs.ClassField.Ramification.Kummer
import SICs.ClassField.SUnits.Valuations

/-!
# Kummer extensions of S-units

The S-unit radical extension, its degree, ramification, and containment of cyclic extensions.

This follows Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII, the construction
preceding Lemma 6.2, using Appendix A.1 and A.3.

## The argument

The S-unit group is finitely generated, so adjoining its nth roots gives a finite extension.
The general Kummer construction supplies its roots and its abelian Galois action killed by n
when the base contains a primitive nth root of unity. S-unit power saturation identifies its
degree with the number of intrinsic S-unit power classes. A cyclic extension of degree n has a
single radical generator. Enlarge any prescribed finite set of primes to make its radicand an
S-unit; the corresponding S-unit Kummer extension then contains the original cyclic field.
Outside S and the primes dividing n, the Kummer ramification criterion gives index one.
-/

noncomputable section

open IsDedekindDomain NumberField

namespace SIC.IdeleGroup

variable (K : Type*) [Field K] [NumberField K]

/-! ### The S-unit radical field

Specializing the general radical construction to the finitely generated S-unit subgroup
supplies the finite extension and its automorphism action. -/

/-- The field $K[U(S)^{1/n}]$ in Milne, *Class Field Theory*, Chapter VII,
the construction preceding Lemma 6.2. -/
def sUnitKummer (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IntermediateField K (AlgebraicClosure K) :=
  kummerExtension K n (sUnits (K := K) (L := K) S)

variable {K}


/-- The S-unit radical extension is finite for $n>0$, by finite generation of S-units.
Specializes `kummerExtension_finiteDimensional`. -/
instance sUnitKummer_finiteDimensional (n : ℕ) [NeZero n]
    (S : Finset (HeightOneSpectrum (𝓞 K))) : FiniteDimensional K (sUnitKummer K n S) :=
  kummerExtension_finiteDimensional (NeZero.pos n) (sUnits_fg (L := K) S)

/-- The S-unit Kummer extension of a number field is itself a number field for $n>0$. -/
instance sUnitKummer_numberField (n : ℕ) [NeZero n]
    (S : Finset (HeightOneSpectrum (𝓞 K))) : NumberField (sUnitKummer K n S) :=
  NumberField.of_module_finite K _

/-- Every S-unit acquires an nth root in $K[U(S)^{1/n}]$.
Specializes `exists_root_kummerExtension`. -/
theorem exists_root_sUnitKummer {n : ℕ} (hn : 0 < n)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (b : sUnits (K := K) (L := K) S) :
    ∃ x : sUnitKummer K n S, x ^ n = algebraMap K _ (b.val : K) :=
  exists_root_kummerExtension hn b

/-- The S-unit Kummer extension is abelian Galois when $\mu_n\subset K$.
Specializes `kummerExtension_isAbelianGalois`. -/
theorem sUnitKummer_isAbelianGalois {n : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (hn : 0 < n) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsAbelianGalois K (sUnitKummer K n S) :=
  kummerExtension_isAbelianGalois hζ hn

/-- Every automorphism of the S-unit Kummer extension satisfies $\sigma^n=1$.
Specializes `kummerExtension_aut_pow`. -/
theorem sUnitKummer_aut_pow {n : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (hn : 0 < n) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : Gal((sUnitKummer K n S)/K)) : σ ^ n = 1 :=
  kummerExtension_aut_pow hζ hn σ

/-- The degree $[K[U(S)^{1/n}]:K]$ equals $|U(S)/U(S)^n|$ when $\mu_n\subset K$.
Milne, *Class Field Theory*, Chapter VII, §6, construction preceding Lemma 6.2.
Specializes `kummerExtension_finrank` using `sUnits_power_comap`. -/
theorem finrank_sUnitKummer {n : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ n) (hn : 0 < n)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Module.finrank K (sUnitKummer K n S) =
      Nat.card (sUnits (K := K) (L := K) S ⧸
        (powMonoidHom n : sUnits (K := K) (L := K) S →* sUnits (K := K) (L := K) S).range) := by
  rw [sUnitKummer, kummerExtension_finrank hζ hn (sUnits_fg S), sUnits_power_comap S hn.ne']

/-- The S-unit radical field is unramified at every prime outside $S$ where $n$ is a unit.
Milne, *Class Field Theory*, Chapter VII, Appendix A.5, for the S-unit radical field. -/
theorem ramificationIdx_sUnitKummer {n : ℕ} [NeZero n]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) (hnv : (n : 𝓞 K) ∉ v.asIdeal)
    (w : HeightOneSpectrum (𝓞 (sUnitKummer K n S))) [hvw : w.asIdeal.LiesOver v.asIdeal] :
    w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  refine @ramificationIdx_kummerExtension_eq_one K _ _ n
    (sUnits (K := K) (L := K) S) (sUnits_fg S) v ?_ hnv w ?_
  · intro b
    apply sUnits_valuation_eq_one S b v
    simpa only [FinitePlace.below_self] using hv
  · exact hvw

/-- The S-unit Kummer field has degree $n^{|S|+r_1+r_2}$ when $\mu_n\subset K$.
Milne, *Class Field Theory*, Chapter VII, §6, construction preceding Lemma 6.2. -/
theorem finrank_sUnitKummer_eq_pow {n : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (hn : 0 < n) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Module.finrank K (sUnitKummer K n S) = n ^ (S.card + Nat.card (InfinitePlace K)) := by
  rw [finrank_sUnitKummer hζ hn, card_sUnits_powerQuotient hζ hn]

/-! ### Containing a prescribed cyclic extension

A cyclic radical generator has a radicand supported at finitely many primes. Adding those
primes to the prescribed baseline gives the desired containment of fields. -/

/-- A cyclic extension of degree n with $\mu_n\subset K$ lies in an S-unit Kummer field
after enlarging any prescribed finite set of primes. Milne, *Class Field Theory*, Chapter VII,
the construction
preceding Lemma 6.2 and Appendix A.1. -/
theorem exists_le_sUnitKummer (n : ℕ) {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E]
    [IsGalois K E] [IsCyclic (E ≃ₐ[K] E)] (hdegree : Module.finrank K E = n)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), S₀ ⊆ S ∧ E ≤ sUnitKummer K n S := by
  classical
  have hζ' : (primitiveRoots (Module.finrank K E) K).Nonempty :=
    ⟨ζ, (mem_primitiveRoots Module.finrank_pos).2 (hdegree ▸ hζ)⟩
  obtain ⟨α, ⟨a, ha⟩, hα⟩ := exists_root_adjoin_eq_top_of_isCyclic K E hζ'
  have hα' : IntermediateField.adjoin K {(α : AlgebraicClosure K)} = E := by
    simpa only [IntermediateField.adjoin_map, Set.image_singleton,
      ← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val]
      using! congrArg (IntermediateField.map E.val) hα
  by_cases ha0 : a = 0
  · have hα0 : α = 0 := eq_zero_of_pow_eq_zero (by rw [← ha, ha0, map_zero])
    refine ⟨S₀, Finset.Subset.refl S₀, ?_⟩
    rw [← hα', hα0, ZeroMemClass.coe_zero, IntermediateField.adjoin_zero]
    exact bot_le
  · let u : Kˣ := Units.mk0 a ha0
    obtain ⟨T, hT⟩ := exists_mem_sUnits (K := K) u
    refine ⟨S₀ ∪ T, Finset.subset_union_left, ?_⟩
    rw [← hα', IntermediateField.adjoin_simple_le_iff]
    apply root_mem_kummerExtension
      ⟨u, sUnits_mono (L := K) Finset.subset_union_right hT⟩
    simpa only [map_pow, hdegree, AlgHom.commutes] using! congrArg E.val ha.symm

end SIC.IdeleGroup
