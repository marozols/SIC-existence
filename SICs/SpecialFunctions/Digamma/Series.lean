/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.Digamma.Asymptotics
import Mathlib.Analysis.Complex.SummableUniformlyOn
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-!
# Holomorphic digamma remainder series

Locally uniform convergence and holomorphy of both remainder sums.

The two remainder series defining Shintani's Barnes coefficients converge locally
uniformly on `ℂ \ (-∞,0]`, as used in [95, Shintani (1977), paragraph 1.6, p. 181].
The ray constant in `SICs.SpecialFunctions.Digamma.Asymptotics` is continuous on
this domain. On a compact subset it has a single upper bound, and the quadratic
remainder estimates therefore give a summable majorant independent of the period.
The holomorphic summands then have holomorphic sums. This justifies continuing
the positive-period coefficient identities by the identity theorem.
-/

noncomputable section

open Complex Set Filter

namespace SIC

/-! ### Locally uniform convergence

Both series use the same compact-set majorant, with constants `3` and `5`.
The corrected digamma estimate only applies past `N ≥ 2 C(τ)`; compactness
makes this cutoff uniform as well.
-/

/-- A quadratic ray estimate with a continuous ray constant gives locally
uniform summability. This supplies both remainder series below. -/
private lemma summableLocallyUniformlyOn_of_digammaRay_bound {f : ℕ → ℂ → ℂ}
    {A : ℝ} (hA : 0 ≤ A)
    (hf : ∀ n tau, tau ∈ Complex.slitPlane →
      2 * digammaRayConstant tau ≤ ((n + 1 : ℕ) : ℝ) →
      ‖f n tau‖ ≤ A * digammaRayConstant tau ^ 3 / (2 * ((n + 1 : ℕ) : ℝ) ^ 2)) :
    SummableLocallyUniformlyOn f Complex.slitPlane := by
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually Complex.isOpen_slitPlane
  intro K hK hKc
  obtain ⟨B, hB⟩ := hKc.bddAbove_image (continuousOn_digammaRayConstant.mono hK)
  let C := max B 1
  have hC (tau : ℂ) (htau : tau ∈ K) : digammaRayConstant tau ≤ C :=
    (hB (mem_image_of_mem _ htau)).trans (le_max_left _ _)
  have hs : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
    exact (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by decide))
  refine ⟨fun n => A * C ^ 3 / 2 * (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹,
    hs.mul_left _, ?_⟩
  have hlarge : ∀ᶠ n : ℕ in atTop, 2 * C ≤ ((n + 1 : ℕ) : ℝ) :=
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).eventually
      (eventually_ge_atTop (2 * C))
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hlarge] with n hn tau htau
  calc
    ‖f n tau‖ ≤ A * digammaRayConstant tau ^ 3 / (2 * ((n + 1 : ℕ) : ℝ) ^ 2) :=
      hf n tau (hK htau) ((mul_le_mul_of_nonneg_left (hC tau htau) (by norm_num)).trans hn)
    _ ≤ A * C ^ 3 / (2 * ((n + 1 : ℕ) : ℝ) ^ 2) := by
      gcongr
      · exact (digammaRayConstant_pos tau (hK htau)).le
      · exact hC tau htau
    _ = _ := by ring

/-- The series `∑ₙ (ψ'(nτ) − (nτ)⁻¹)`, indexed by positive integers,
converges locally uniformly on `ℂ \ (-∞,0]`. This justifies the continuation
of `γ₂₁` in [95, Shintani (1977), paragraph 1.6, p. 181]. -/
theorem summableLocallyUniformlyOn_trigamma_remainder :
    SummableLocallyUniformlyOn (fun n : ℕ => fun tau : ℂ =>
      deriv Complex.digamma (((n + 1 : ℕ) : ℂ) * tau) -
        (((n + 1 : ℕ) : ℂ) * tau)⁻¹) Complex.slitPlane := by
  apply summableLocallyUniformlyOn_of_digammaRay_bound (A := 3) (by norm_num)
  intro n tau htau _
  exact norm_deriv_digamma_mul_sub_inv_le tau htau (n + 1) (Nat.zero_lt_succ n)

/-- The series `∑ₙ (ψ(nτ) − log(nτ) + (2nτ)⁻¹)`, indexed by positive
integers, converges locally uniformly on `ℂ \ (-∞,0]`. This justifies the
continuation of `γ₂₂` in [95, Shintani (1977), paragraph 1.6, p. 181]. -/
theorem summableLocallyUniformlyOn_digamma_remainder :
    SummableLocallyUniformlyOn (fun n : ℕ => fun tau : ℂ =>
      Complex.digamma (((n + 1 : ℕ) : ℂ) * tau) -
        Complex.log (((n + 1 : ℕ) : ℂ) * tau) +
        (((n + 1 : ℕ) : ℂ) * tau)⁻¹ / 2) Complex.slitPlane := by
  apply summableLocallyUniformlyOn_of_digammaRay_bound (A := 5) (by norm_num)
  intro n tau htau hlarge
  exact norm_digamma_mul_sub_log_add_half_inv_le tau htau (n + 1)
    (Nat.zero_lt_succ n) hlarge

/-! ### Holomorphy of the sums

Positive dilations preserve the slit plane. The regularity of the digamma
function, its derivative and the principal logarithm therefore applies to every
summand, and locally uniform convergence preserves holomorphy.
-/

/-- Positive integral dilation preserves the domain of the remainder series.
This supplies the analytic hypotheses in their differentiability proofs. -/
private lemma slitPlane_succ_mul (n : ℕ) (tau : ℂ) (htau : tau ∈ Complex.slitPlane) :
    ((n + 1 : ℕ) : ℂ) * tau ∈ Complex.slitPlane := by
  rcases htau with h | h
  · left
    simpa using mul_pos (Nat.cast_pos.mpr (Nat.zero_lt_succ n) :
      (0 : ℝ) < ((n + 1 : ℕ) : ℝ)) h
  · right
    simpa using mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.add_one_ne_zero n) :
      ((n + 1 : ℕ) : ℝ) ≠ 0) h

/-- The trigamma remainder sum is holomorphic on the slit plane, by
`summableLocallyUniformlyOn_trigamma_remainder`. -/
theorem differentiableOn_tsum_trigamma_remainder :
    DifferentiableOn ℂ (fun tau : ℂ => ∑' n : ℕ,
      (deriv Complex.digamma (((n + 1 : ℕ) : ℂ) * tau) -
        (((n + 1 : ℕ) : ℂ) * tau)⁻¹)) Complex.slitPlane := by
  apply summableLocallyUniformlyOn_trigamma_remainder.differentiableOn Complex.isOpen_slitPlane
  intro n tau htau
  have hz := slitPlane_succ_mul n tau htau
  have hmul := (differentiableAt_id (𝕜 := ℂ) (x := tau)).const_mul (((n + 1 : ℕ) : ℂ))
  exact ((analyticAt_digamma_of_mem_slitPlane _ hz).deriv.differentiableAt.comp tau hmul).sub
    (hmul.inv (Complex.slitPlane_ne_zero hz))

/-- The corrected digamma remainder sum is holomorphic on the slit plane, by
`summableLocallyUniformlyOn_digamma_remainder`. -/
theorem differentiableOn_tsum_digamma_remainder :
    DifferentiableOn ℂ (fun tau : ℂ => ∑' n : ℕ,
      (Complex.digamma (((n + 1 : ℕ) : ℂ) * tau) -
        Complex.log (((n + 1 : ℕ) : ℂ) * tau) +
        (((n + 1 : ℕ) : ℂ) * tau)⁻¹ / 2)) Complex.slitPlane := by
  apply summableLocallyUniformlyOn_digamma_remainder.differentiableOn Complex.isOpen_slitPlane
  intro n tau htau
  have hz := slitPlane_succ_mul n tau htau
  have hmul := (differentiableAt_id (𝕜 := ℂ) (x := tau)).const_mul (((n + 1 : ℕ) : ℂ))
  exact (((analyticAt_digamma_of_mem_slitPlane _ hz).differentiableAt.comp tau hmul).sub
    (hmul.clog hz)).add ((hmul.inv (Complex.slitPlane_ne_zero hz)).div_const 2)

end SIC

end
