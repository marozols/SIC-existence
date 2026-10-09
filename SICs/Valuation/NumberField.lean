/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import SICs.Valuation.Extension

/-!
# Valuations of `ℂ` above the primes of an embedded number field

For a number field `L` embedded in `ℂ` by `ι` and a prime `w` of `𝒪_L`, a valuation
`v : ℂ → ℝ≥0` restricting to the `w`-adic valuation; it is at most one on `ι(𝒪_L)` and below one
exactly on `ι(w)`. An element of `L` whose image is integral at every valuation of `ℂ` above a
rational prime is an algebraic integer.

This module connects the valuations of `ℂ` at which the finite quantum dilogarithm satisfies its
congruences (`pseudolatticeDilog_frobenius_split`, `pseudolatticeDilog_valuation_eq_one`) to the
primes of a number field containing its values, at which Frobenius elements act. It supplies the
reciprocity argument of `SICs.Dilogarithm.Reciprocity.RayField`, the identity-class step of
[RW26b, Radchenko, Wheeler (2026b), Section 8, Proposition 4].

## The argument

*Extension.* The `w`-adic valuation of `L` has values in `ℤᵐ⁰`; composing it with the strictly
monotone embedding `ℤᵐ⁰ → ℝ≥0`, `exp(n) ↦ cⁿ` for a constant `c > 1`, gives an equivalent
valuation with real values, and `exists_valuation_comap_eq` extends it along `ι` to `ℂ`.
Equivalent valuations have the same valuation ring and maximal ideal, which on `𝒪_L` are
`𝒪_L` and `w`.

*Integrality.* An element of `L` with nonnegative `w`-adic valuation at every prime `w` lies in
`𝒪_L`. Every `w` contains a rational prime `p`, and the valuation of `ℂ` above `w` has
`v(p) < 1`, so the hypothesis applies to it.
-/

noncomputable section

open IsDedekindDomain NumberField
open scoped NNReal

namespace SIC

variable {L : Type*} [Field L] [NumberField L]

/-! ### The valuation above a prime -/

/-- **A valuation of `ℂ` above a prime of an embedded number field**: for `ι : L → ℂ` and a
prime `w` of `𝒪_L`, a valuation `v : ℂ → ℝ≥0` whose restriction `v ∘ ι` is equivalent to the
`w`-adic valuation of `L`. -/
theorem exists_valuation_complex_isEquiv (ι : L →+* ℂ) (w : HeightOneSpectrum (𝓞 L)) :
    ∃ v : Valuation ℂ ℝ≥0, (v.comap ι).IsEquiv (w.valuation L) := by
  let alg : Algebra L ℂ := ι.toAlgebra
  let e : ℝ≥0 := 2
  have he : 1 < e := by norm_num [e]
  let f := WithZeroMulInt.toNNReal (ne_of_gt (lt_trans zero_lt_one he))
  have hf : StrictMono f := WithZeroMulInt.toNNReal_strictMono he
  let u := (w.valuation L).map f hf.monotone
  obtain ⟨v, hv⟩ := @exists_valuation_comap_eq L ℂ _ _ alg u
  refine ⟨v, ?_⟩
  change v.comap ι = u at hv
  rw [hv]
  exact Valuation.isEquiv_map_self_of_strictMono f hf

/-- A valuation of `ℂ` above a prime `w` of an embedded number field is at most one on the image
of `𝒪_L` and below one exactly on the image of `w`
(`exists_valuation_complex_isEquiv`). -/
theorem exists_valuation_complex_lt_one_iff (ι : L →+* ℂ) (w : HeightOneSpectrum (𝓞 L)) :
    ∃ v : Valuation ℂ ℝ≥0, ∀ a : 𝓞 L, v (ι a) ≤ 1 ∧ (v (ι a) < 1 ↔ a ∈ w.asIdeal) := by
  obtain ⟨v, hv⟩ := exists_valuation_complex_isEquiv ι w
  refine ⟨v, fun a => ⟨?_, ?_⟩⟩
  · exact hv.le_one_iff_le_one.mpr (w.valuation_le_one a)
  · exact hv.lt_one_iff_lt_one.trans (w.valuation_lt_one_iff_mem a)

/-! ### Integrality from valuations -/

/-- **Integrality from the valuations above all primes**: an element `z` of a number field `L`
embedded by `ι` with `v(ι z) ≤ 1` at every valuation `v : ℂ → ℝ≥0` with `v(p) < 1` for a rational
prime `p` is an algebraic integer. -/
theorem isIntegral_of_forall_valuation_le_one (ι : L →+* ℂ) {z : L}
    (hz : ∀ v : Valuation ℂ ℝ≥0, ∀ p : ℕ, p.Prime → v (p : ℂ) < 1 → v (ι z) ≤ 1) :
    IsIntegral ℤ z := by
  have hval : ∀ w : HeightOneSpectrum (𝓞 L), (w.valuation L) z ≤ 1 := by
    intro w
    have : w.asIdeal.IsMaximal := Ideal.isMaximal_of_isPrime_of_ne_bot w.asIdeal w.ne_bot
    obtain ⟨p, _, _, hpw, hp, _⟩ := Ideal.exists_prime_and_absNorm_eq_pow w.asIdeal
    obtain ⟨v, hv⟩ := exists_valuation_complex_isEquiv ι w
    have hwp : (w.valuation L) (p : L) < 1 := by
      simpa using (w.valuation_lt_one_iff_mem (p : 𝓞 L)).mpr hpw
    have hvp : v (p : ℂ) < 1 := by
      have := hv.lt_one_iff_lt_one.mpr hwp
      simpa using this
    exact hv.le_one_iff_le_one.mp (hz v p hp hvp)
  obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one L z hval
  rw [← ha]
  exact NumberField.RingOfIntegers.isIntegral_coe a

end SIC

end
