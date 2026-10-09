/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Local.UnitGroups
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Quotients of the integers of a finite completion

The cardinality of a principal quotient of the local integers is the inverse normalized norm.

This supplies the additive index calculation in Milne, *Class Field Theory*, version 4.03
(2020), Chapter VII, Proposition 6.8.

## The argument

The residue field of the completed valuation ring agrees with the residue field of the
original prime. Successive quotients by powers of the maximal ideal have that same
cardinality. Every nonzero principal ideal is a power of the maximal ideal, and the
normalized norm records precisely its exponent.
-/

noncomputable section

open IsDedekindDomain NumberField
open scoped SIC.FinitePlace

namespace SIC.FinitePlace

variable {K : Type*} [Field K] [NumberField K]

/-! ### The residue field

Global integers represent every residue class by the completion approximation theorem.
The valuation of a global integer is unchanged by completion, identifying the kernel. -/

/-- Membership in the completed maximal ideal is the strict norm bound below one. -/
theorem mem_completion_maximalIdeal_iff_norm_lt_one (v : HeightOneSpectrum (𝓞 K))
    (a : v.adicCompletionIntegers K) :
    a ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ↔
      ‖(a : v.adicCompletion K)‖ < 1 :=
  (Valuation.mem_maximalIdeal_iff (v.adicCompletion K) Valued.v).trans
    Valued.toNormedField.norm_lt_one_iff.symm

/-- Reduction from global integers to the completed residue field; used to identify the
residue field in `completionResidueEquiv`. -/
private def completionResidueMap (v : HeightOneSpectrum (𝓞 K)) :
    𝓞 K →+* IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
  (IsLocalRing.residue (v.adicCompletionIntegers K)).comp
    (algebraMap (𝓞 K) (v.adicCompletionIntegers K))

/-- The global-to-local residue map has kernel v. This identifies the kernel needed by
`completionResidueEquiv`. -/
private theorem ker_completionResidueMap (v : HeightOneSpectrum (𝓞 K)) :
    RingHom.ker (completionResidueMap v) = v.asIdeal := by
  ext a
  change IsLocalRing.residue (v.adicCompletionIntegers K)
    (algebraMap (𝓞 K) (v.adicCompletionIntegers K) a) = 0 ↔ a ∈ v.asIdeal
  rw [IsLocalRing.residue_eq_zero_iff, mem_completion_maximalIdeal_iff_norm_lt_one,
    Valued.toNormedField.norm_lt_one_iff]
  change Valued.v (a : v.adicCompletion K) < 1 ↔ _
  rw [v.valuedAdicCompletion_eq_valuation' (a : K), v.valuation_lt_one_iff_mem]

/-- Global integers represent every completed residue class; this is the surjectivity step
in `completionResidueEquiv`. -/
private theorem completionResidueMap_surjective (v : HeightOneSpectrum (𝓞 K)) :
    Function.Surjective (completionResidueMap v) := by
  intro y
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := v.adicCompletionIntegers K) y
  have ha : ‖(a : v.adicCompletion K)‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr a.property
  obtain ⟨c, hc⟩ := exists_integral_approx v ha
  refine ⟨c, ?_⟩
  change IsLocalRing.residue (v.adicCompletionIntegers K)
    (algebraMap (𝓞 K) (v.adicCompletionIntegers K) c) =
      IsLocalRing.residue (v.adicCompletionIntegers K) a
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    mem_completion_maximalIdeal_iff_norm_lt_one]
  have ht : (Ideal.absNorm v.asIdeal : ℝ)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v)
  change ‖algebraMap (𝓞 K) (v.adicCompletion K) c - (a : v.adicCompletion K)‖ < 1
  rw [norm_sub_rev]
  exact hc.trans ht

/-- Completion preserves the residue field at v. This is the residue-field identification
used in the additive index calculation of Milne, *Class Field Theory*, VII, Proposition 6.8. -/
def completionResidueEquiv (v : HeightOneSpectrum (𝓞 K)) :
    (𝓞 K ⧸ v.asIdeal) ≃+* IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
  (Ideal.quotEquivOfEq (ker_completionResidueMap v).symm).trans
    ((completionResidueMap v).quotientKerEquivOfSurjective (completionResidueMap_surjective v))

/-- The residue field of the completed local integers has cardinality Nv. -/
theorem card_completionResidue (v : HeightOneSpectrum (𝓞 K)) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) =
      Ideal.absNorm v.asIdeal := by
  rw [← Nat.card_congr (completionResidueEquiv v).toEquiv]
  rfl

/-! ### Principal ideal quotients

A nonzero local integer is a unit times a power of a uniformizer. Counting successive
residue quotients computes its principal quotient, and the normalized norm gives the same power. -/

/-- A normalized uniformizer has norm $(Nv)^{-1}$; this converts the ideal power count
into the norm expression in `card_quotient_span_eq_norm_inv`. -/
private theorem norm_completion_uniformizer (v : HeightOneSpectrum (𝓞 K))
    (ϖ : v.adicCompletionIntegers K)
    (hϖ : Valued.v (ϖ : v.adicCompletion K) = WithZero.exp (-1 : ℤ)) :
    ‖(ϖ : v.adicCompletion K)‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  rw [NumberField.FinitePlace.norm_def, hϖ,
    WithZeroMulInt.toNNReal_neg_apply (HeightOneSpectrum.absNorm_ne_zero v)
      WithZero.exp_ne_zero]
  change ((Ideal.absNorm v.asIdeal : NNReal) ^ (-1 : ℤ) : ℝ) = _
  simp

/-- For a nonzero local integer $a$, $|\mathcal O_v/a\mathcal O_v|=|a|_v^{-1}$.
This is the additive index used in Milne, *Class Field Theory*, Chapter VII,
proof of Proposition 6.8. -/
theorem card_quotient_span_eq_norm_inv (v : HeightOneSpectrum (𝓞 K))
    (a : v.adicCompletionIntegers K) (ha : a ≠ 0) :
    (Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {a}) : ℝ) =
      ‖(a : v.adicCompletion K)‖⁻¹ := by
  obtain ⟨ϖ, hϖ, hval⟩ := exists_completion_uniformizer v
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have hmax : IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ≠ ⊥ := by
    rw [hϖ.maximalIdeal_eq, ne_eq, Ideal.span_singleton_eq_bot]
    exact hϖ.ne_zero
  have hunit : ‖((u : v.adicCompletionIntegers K) : v.adicCompletion K)‖ = 1 := by
    rw [NumberField.FinitePlace.norm_def]
    have hu := (HeightOneSpectrum.adicCompletionIntegers.integers K v)
      |>.isUnit_iff_valuation_eq_one.mp u.isUnit
    change Valued.v (((u : v.adicCompletionIntegers K) : v.adicCompletion K)) = 1 at hu
    rw [hu, map_one, NNReal.coe_one]
  rw [Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
    ← hϖ.maximalIdeal_eq]
  change ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ m).cardQuot : ℝ) = _
  rw [cardQuot_pow_of_prime hmax, Nat.cast_pow]
  change (Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) : ℝ) ^ m = _
  rw [card_completionResidue]
  change _ = ‖((u : v.adicCompletionIntegers K) : v.adicCompletion K) *
    (ϖ : v.adicCompletion K) ^ m‖⁻¹
  rw [norm_mul, norm_pow, hunit, one_mul, norm_completion_uniformizer v ϖ hval,
    ← inv_pow, inv_inv]

end SIC.FinitePlace
