/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.BarnesDoubleGamma.Product
import Mathlib.NumberTheory.ZetaValues

/-!
# Horizontal rows of the Barnes double gamma product

Exact gamma evaluations of the axial row and the rows `m+nτ`.

This file follows the proof of [95, Shintani (1977), Proposition 1 on pp. 172–173].
The first rearrangement in that proof evaluates each horizontal row of the genus-two
Weierstrass product in terms of the ordinary gamma function and its first two logarithmic
derivatives. For `a = n tau` with `n ≥ 1` and `tau∈ℂ \ (-∞,0]`, the row identity is

```text
∏_{m≥0} W(z/(a+m)) = Gamma(a)/Gamma(a+z) exp(z psi(a)+z² psi'(a)/2).
```

The finite identity uses Euler's gamma approximant. Its logarithmic and reciprocal-square
corrections converge to `psi(a)` and `psi'(a)`, respectively; absolute convergence of the
Barnes product justifies passing to the row product. When `a+z` is a nonpositive integer,
both sides vanish: the row has a zero factor, and the reciprocal gamma function vanishes.
The axial row is evaluated separately using `psi(1)=-gamma` and the Basel sum
`psi'(1)=pi²/6`. These are the row evaluations used in
`SICs.SpecialFunctions.BarnesDoubleGamma.Normalization`, where the normalization coefficients cancel
in
Shintani's difference-equation calculation.
-/

noncomputable section

open Complex Filter
open scoped Topology

namespace SIC

/-! ### Finite row identities

Separating the rational and exponential factors makes the finite row an exact quotient of
Euler gamma approximants. The two correction sums are precisely the approximants whose limits
were proved in `SICs.SpecialFunctions.Digamma.EulerLimit`.
-/

/-- The rational and exponential parts of a finite row, used by
`barnesGenusTwoFactor_prod_mul_gammaSeq`. -/
private lemma barnesGenusTwoFactor_prod (a z : ℂ) (N : ℕ)
    (ha : ∀ m ∈ Finset.range (N + 1), a + m ≠ 0) :
    (∏ m ∈ Finset.range (N + 1), barnesGenusTwoFactor (z / (a + m))) =
      ((∏ m ∈ Finset.range (N + 1), (a + z + m)) /
        ∏ m ∈ Finset.range (N + 1), (a + m)) *
      Complex.exp (-z * (∑ m ∈ Finset.range (N + 1), (a + m)⁻¹) +
        z ^ 2 / 2 * gammaSeqTrigamma a N) := by
  simp only [barnesGenusTwoFactor, Finset.prod_mul_distrib, ← Complex.exp_sum]
  congr 1
  · rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro m hm
    field_simp [ha m hm]
    ring
  · congr 1
    simp only [gammaSeqTrigamma, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    ring

/-- Multiplying a finite horizontal row by Euler's gamma approximant at `a+z` leaves the
approximant at `a` and its two logarithmic correction terms. This finite identity is used in
`barnesGenusTwoFactor_hasProd_gamma`. -/
private lemma barnesGenusTwoFactor_prod_mul_gammaSeq (a z : ℂ) (N : ℕ) (hN : N ≠ 0)
    (ha : ∀ m ∈ Finset.range (N + 1), a + m ≠ 0)
    (haz : ∀ m ∈ Finset.range (N + 1), a + z + m ≠ 0) :
    (∏ m ∈ Finset.range (N + 1), barnesGenusTwoFactor (z / (a + m))) *
        Complex.GammaSeq (a + z) N =
      Complex.GammaSeq a N * Complex.exp
        (z * gammaSeqLogDeriv a N + z ^ 2 / 2 * gammaSeqTrigamma a N) := by
  have hpa := Finset.prod_ne_zero_iff.mpr ha
  have hpaz := Finset.prod_ne_zero_iff.mpr haz
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  rw [barnesGenusTwoFactor_prod a z N ha]
  simp only [Complex.GammaSeq, Complex.cpow_def_of_ne_zero hNC]
  field_simp [hpa, hpaz]
  rw [← Complex.exp_add]
  conv_rhs => rw [mul_assoc, ← Complex.exp_add, mul_comm]
  congr 2
  unfold gammaSeqLogDeriv
  simp only [one_div]
  ring

/-! ### The infinite row evaluation

The row `a+m` is a subfamily of the cone lattice with periods `(1,a)`. Thus its genus-two
factor deviations are absolutely summable when `a∈ℂ \ (-∞,0]`. Taking limits in the finite identity
gives Shintani's gamma evaluation away from the poles of `Gamma(a+z)`; the zero factors give
the equality at those remaining points as well.
-/

/-- The deviations from `1` in a horizontal genus-two row are absolutely summable when
`a∈ℂ \ (-∞,0]`. This restricts the slit-plane Barnes cone estimate to the row
`m+a`, and justifies the infinite row evaluation `barnesGenusTwoFactor_hasProd_gamma`. -/
lemma summable_norm_barnesGenusTwoFactor_row_sub_one (a z : ℂ) (ha : a ∈ Complex.slitPlane) :
    Summable (fun m : ℕ => ‖barnesGenusTwoFactor (z / (a + m)) - 1‖) := by
  let row : ℕ → BarnesDoubleGammaIndex := fun m => ⟨(m, 1), by simp⟩
  have hrow : Function.Injective row := by
    intro m n h
    exact congrArg (fun p : BarnesDoubleGammaIndex => p.1.1) h
  apply ((summable_norm_barnesDoubleGammaInvFactor_sub_one z a ha).comp_injective
    hrow).congr
  intro m
  rw [Function.comp_apply, barnesDoubleGammaInvFactor_eq_genusTwoFactor]
  simp only [barnesDoubleGammaLatticePoint, row, Nat.cast_one, mul_one, one_mul, add_comm a]

/-- The shared limiting argument for `barnesGenusTwoFactor_hasProd_gamma` and
`barnesGenusTwoFactor_hasProd_axis` away from the poles of `Gamma(a+z)`. -/
private lemma barnesGenusTwoFactor_hasProd_gamma_of_limits (a z : ℂ)
    (ha : ∀ m : ℕ, a + m ≠ 0)
    (hs : Summable (fun m : ℕ => ‖barnesGenusTwoFactor (z / (a + m)) - 1‖))
    (hlog : Tendsto (fun N => gammaSeqLogDeriv a (N + 1)) atTop
      (𝓝 (Complex.digamma a)))
    (htri : Tendsto (fun N => gammaSeqTrigamma a (N + 1)) atTop
      (𝓝 (deriv Complex.digamma a)))
    (haz : ∀ m : ℕ, a + z ≠ -(m : ℂ)) :
    HasProd (fun m : ℕ => barnesGenusTwoFactor (z / (a + m)))
      (Complex.Gamma a / Complex.Gamma (a + z) *
        Complex.exp (z * Complex.digamma a + z ^ 2 / 2 * deriv Complex.digamma a)) := by
  have hp : Multipliable (fun m : ℕ => barnesGenusTwoFactor (z / (a + m))) := by
    simpa using multipliable_one_add_of_summable hs
  have hleft := (hp.hasProd.tendsto_prod_nat.comp (tendsto_add_atTop_nat 2)).mul
    ((Complex.GammaSeq_tendsto_Gamma (a + z)).comp (tendsto_add_atTop_nat 1))
  have hright := ((Complex.GammaSeq_tendsto_Gamma a).comp
    (tendsto_add_atTop_nat 1)).mul
      ((hlog.const_mul z).add (htri.const_mul (z ^ 2 / 2))).cexp
  have heq := tendsto_nhds_unique hleft (hright.congr' <|
    Filter.Eventually.of_forall fun N => by
      simpa only [Function.comp_apply, Nat.add_assoc] using
        (barnesGenusTwoFactor_prod_mul_gammaSeq a z (N + 1) (Nat.add_one_ne_zero N)
          (fun m _ => ha m)
          (fun m _ hm => haz m (eq_neg_of_add_eq_zero_left hm))).symm)
  have hvalue : (∏' m : ℕ, barnesGenusTwoFactor (z / (a + m))) =
      Complex.Gamma a / Complex.Gamma (a + z) *
        Complex.exp (z * Complex.digamma a + z ^ 2 / 2 * deriv Complex.digamma a) := by
    rw [div_mul_eq_mul_div]
    exact (eq_div_iff (Complex.Gamma_ne_zero haz)).mpr heq
  exact hvalue ▸ hp.hasProd

/-- At a pole `a+z=-m` of `Gamma(a+z)`, the `m`th factor of the row vanishes, so the row
product is `0`. This is the zero case shared by `barnesGenusTwoFactor_hasProd_gamma` and
`barnesGenusTwoFactor_hasProd_axis`. -/
private lemma barnesGenusTwoFactor_hasProd_zero (a z : ℂ) (m : ℕ) (hm : a + z = -m)
    (ha : a + m ≠ 0) :
    HasProd (fun n : ℕ => barnesGenusTwoFactor (z / (a + n))) 0 := by
  apply hasProd_zero_of_exists_eq_zero
  refine ⟨m, ?_⟩
  have hz : z = -(a + m) := by linear_combination hm
  rw [barnesGenusTwoFactor, hz, neg_div, div_self ha]
  simp

/-- The horizontal-row identity

```text
∏_{m≥0} W(z/(a+m)) = Gamma(a)/Gamma(a+z) exp(z psi(a)+z² psi'(a)/2),
```

for `a∈ℂ \ (-∞,0]`. This is the exponential form of the row evaluation in
[95, Shintani (1977), proof of Proposition 1 on p. 172], with `a=n omega₂/omega₁` and `z`
replaced by `z/omega₁`; the extension to nonreal period ratios is stated in
[95, Shintani (1977), paragraph 1.6 on p. 181]. At a pole of `Gamma(a+z)`, both the
reciprocal gamma expression and the row product take their entire value `0`. -/
theorem barnesGenusTwoFactor_hasProd_gamma (a z : ℂ) (ha : a ∈ Complex.slitPlane) :
    HasProd (fun m : ℕ => barnesGenusTwoFactor (z / (a + m)))
      (Complex.Gamma a / Complex.Gamma (a + z) *
        Complex.exp (z * Complex.digamma a + z ^ 2 / 2 * deriv Complex.digamma a)) := by
  by_cases haz : ∀ m : ℕ, a + z ≠ -(m : ℂ)
  · exact barnesGenusTwoFactor_hasProd_gamma_of_limits a z
      (fun m hm => by
        rcases ha with h | h
        · have := congrArg Complex.re hm
          simp at this
          linarith [Nat.cast_nonneg (α := ℝ) m]
        · exact h (by simpa using congrArg Complex.im hm))
      (summable_norm_barnesGenusTwoFactor_row_sub_one a z ha)
      (tendsto_gammaSeqLogDeriv_of_mem_slitPlane a ha)
      (tendsto_gammaSeqTrigamma_of_mem_slitPlane a ha) haz
  push Not at haz
  obtain ⟨m, hm⟩ := haz
  rw [hm, Complex.Gamma_neg_nat_eq_zero, div_zero, zero_mul]
  exact barnesGenusTwoFactor_hasProd_zero a z m hm
    fun h => by
      rcases ha with hr | hi
      · have := congrArg Complex.re h
        simp at this
        linarith [Nat.cast_nonneg (α := ℝ) m]
      · exact hi (by simpa using congrArg Complex.im h)

/-! ### The axial row

The row on the positive real axis has the same finite gamma evaluation. Euler's limit at `1`,
`psi(1)=-gamma`, and the Basel sum `psi'(1)=pi²/6` give the remaining row in Shintani's
rearrangement on p. 172.
-/

/-- The Basel sum `∑_{m≥0} 1/(1+m)² = pi²/6` in complex form. This is the index-shifted
complex version of Mathlib's `hasSum_zeta_two`; it evaluates `psi'(1)` in
`deriv_digamma_one` and the quadratic correction to Euler's gamma product in
`SICs.SpecialFunctions.BarnesDoubleGamma.Difference`. -/
lemma hasSum_inv_one_add_natCast_sq :
    HasSum (fun m : ℕ => (1 + (m : ℂ))⁻¹ ^ 2) ((Real.pi : ℂ) ^ 2 / 6) := by
  have h := hasSum_zeta_two.map Complex.ofRealCLM Complex.ofRealCLM.continuous
  have hshift := (hasSum_nat_add_iff' 1).mpr h
  simpa [Function.comp_def, Complex.ofRealCLM_apply, Finset.sum_range_one,
    one_div, inv_pow, add_comm] using hshift

/-- The value `psi'(1)=pi²/6`, used in `barnesGenusTwoFactor_hasProd_axis`, follows from
`tendsto_gammaSeqTrigamma` and the Basel sum `hasSum_inv_one_add_natCast_sq`. -/
private lemma deriv_digamma_one : deriv Complex.digamma 1 = (Real.pi : ℂ) ^ 2 / 6 := by
  have hlim := hasSum_inv_one_add_natCast_sq.tendsto_sum_nat.comp (tendsto_add_atTop_nat 2)
  exact tendsto_nhds_unique (tendsto_gammaSeqTrigamma 1 (by simp))
    (by simpa [gammaSeqTrigamma, Nat.add_assoc, Function.comp_def] using hlim)

/-- The axial-row evaluation

```text
∏_{m≥1} W(z/m) = Gamma(1+z)⁻¹ exp(-gamma z + pi² z²/12).
```

This is the exponential form of the first row calculation in [95, Shintani (1977), proof
of Proposition 1 on p. 172], with `omega₁=1`. It also holds at the zeros of the reciprocal
gamma function. -/
theorem barnesGenusTwoFactor_hasProd_axis (z : ℂ) :
    HasProd (fun m : ℕ => barnesGenusTwoFactor (z / (1 + m)))
      ((Complex.Gamma (1 + z))⁻¹ *
        Complex.exp (-(Real.eulerMascheroniConstant : ℂ) * z +
          (Real.pi : ℂ) ^ 2 * z ^ 2 / 12)) := by
  convert barnesGenusTwoFactor_hasProd_gamma 1 z Complex.one_mem_slitPlane using 1
  rw [Complex.Gamma_one, Complex.digamma_one, deriv_digamma_one, one_div]
  congr 2
  ring

end SIC

end
