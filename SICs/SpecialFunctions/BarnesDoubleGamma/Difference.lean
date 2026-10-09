/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.BarnesDoubleGamma.Normalization

/-!
# The two difference equations for the Barnes double gamma

Both double-gamma difference equations on the slit plane, including gamma poles.

This file follows [95, Shintani (1977), proof of Proposition 1 on p. 173], with periods
`(1,tau)` on the slit plane of paragraph 1.6 on p. 181.
Shifting the normalized horizontal gamma rows by `1`
leaves the ordinary genus-one Euler product. Its value follows from the axial genus-two
product after removing the quadratic exponential by the Basel sum. The remaining
elementary exponentials cancel to give the source's first difference equation.

We multiply the difference equation by the reciprocal gamma function at `z/tau`.
This expresses the identity using entire functions and includes the points where the
source's displayed gamma factor has a pole, without assigning a product to `0` and infinity.

The period-one equation supplies the corresponding double-sine equation in
`SICs.SpecialFunctions.DoubleSine.Gamma`. Period symmetry is
`barnesDoubleGammaInv_symm`. Scaling the rows by the first period and then using this
symmetry proves the second-period equation, following the same proof of Proposition 1.
-/

noncomputable section

open Complex Filter
open scoped Topology

namespace SIC

/-! ### The ordinary gamma product

Shintani recalls Euler's gamma product in the proof of Proposition 1. Here it is obtained
from the already evaluated axial genus-two product by subtracting its quadratic correction.
-/

/-- The quadratic correction to the axial genus-two product sums to `pi² z²/12`.
This rescales the Basel sum `hasSum_inv_one_add_natCast_sq` for `barnesGamma_hasProd_euler`. -/
private lemma barnesGamma_quadratic_hasSum (z : ℂ) :
    HasSum (fun n : ℕ => (z / (1 + n)) ^ 2 / 2)
      ((Real.pi : ℂ) ^ 2 * z ^ 2 / 12) := by
  convert! hasSum_inv_one_add_natCast_sq.mul_left (z ^ 2 / 2) using 1
  · ext n
    ring
  · ring

/-- Euler's product

```text
∏_{n≥1} (1+z/n) exp(-z/n) = Gamma(1+z)⁻¹ exp(-gamma z).
```

This is the exponential form of the gamma product recalled in
[95, Shintani (1977), proof of Proposition 1 on p. 172]. The formula uses reciprocal
gamma, so it holds also at its zeros. -/
lemma barnesGamma_hasProd_euler (z : ℂ) :
    HasProd (fun n : ℕ => (1 + z / (1 + n)) * Complex.exp (-z / (1 + n)))
      ((Complex.Gamma (1 + z))⁻¹ *
        Complex.exp (-(Real.eulerMascheroniConstant : ℂ) * z)) := by
  have hp := (barnesGenusTwoFactor_hasProd_axis z).mul
    (barnesGamma_quadratic_hasSum z).neg.cexp
  convert hp using 1
  · ext n
    simp only [Function.comp_apply, barnesGenusTwoFactor, mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  · rw [mul_assoc, ← Complex.exp_add]
    congr 2
    ring

/-! ### Shifting the normalized rows

The reciprocal-gamma recurrence shifts every normalized row, including a row with a zero
factor. Multiplying these identities and applying Euler's product gives the shift of the
convergent product in `barnesDoubleGammaInv_eq_normalizedRow_tprod`.
-/

/-- The elementary exponential in one normalized row gains `a exp(z/a)` under `z ↦ z+1`.
This isolates the algebra in `barnesDoubleGammaNormalizedRow_add_one`. -/
private lemma barnesDoubleGammaRow_exponential_add_one (a z : ℂ) (ha : a ≠ 0) :
    Complex.exp ((z + 1) * Complex.log a + ((z + 1) ^ 2 - (z + 1)) / (2 * a)) *
        Complex.exp (-z / a) =
      a * Complex.exp (z * Complex.log a + (z ^ 2 - z) / (2 * a)) := by
  calc
    _ = Complex.exp (Complex.log a +
        (z * Complex.log a + (z ^ 2 - z) / (2 * a))) := by
      rw [← Complex.exp_add]
      congr 1
      field_simp
      ring
    _ = _ := by rw [Complex.exp_add, Complex.exp_log ha]

/-- Shifting `R_n(z,tau)` by `1` introduces the reciprocal of its Euler factor:
`R_n(z+1,tau) (1+z/((n+1)tau)) exp(-z/((n+1)tau)) = R_n(z,tau)`.
This is the row calculation in [95, Shintani (1977), proof of Proposition 1 on p. 173],
written without division by a gamma value. -/
lemma barnesDoubleGammaNormalizedRow_add_one (z tau : ℂ) (n : ℕ)
    (htau : tau ≠ 0) :
    barnesDoubleGammaNormalizedRow (z + 1) tau n *
        ((1 + z / (((n + 1 : ℕ) : ℂ) * tau)) *
          Complex.exp (-z / (((n + 1 : ℕ) : ℂ) * tau))) =
      barnesDoubleGammaNormalizedRow z tau n := by
  let a : ℂ := ((n + 1 : ℕ) : ℂ) * tau
  have ha : a ≠ 0 := mul_ne_zero (by exact_mod_cast n.succ_ne_zero) htau
  have hrec := (Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (a + z)).symm
  rw [show a + z + 1 = a + (z + 1) by ring] at hrec
  simp only [barnesDoubleGammaNormalizedRow, mul_assoc (2 : ℂ)]
  change Complex.Gamma a / Complex.Gamma (a + (z + 1)) *
      Complex.exp ((z + 1) * Complex.log a + ((z + 1) ^ 2 - (z + 1)) / (2 * a)) *
        ((1 + z / a) * Complex.exp (-z / a)) =
    Complex.Gamma a / Complex.Gamma (a + z) *
      Complex.exp (z * Complex.log a + (z ^ 2 - z) / (2 * a))
  rw [show (1 + z / a) = (a + z) / a by field_simp]
  simp only [div_eq_mul_inv]
  calc
    _ = Complex.Gamma a * ((a + z) * (Complex.Gamma (a + (z + 1)))⁻¹) * a⁻¹ *
        (Complex.exp ((z + 1) * Complex.log a + ((z + 1) ^ 2 - (z + 1)) / (2 * a)) *
          Complex.exp (-z / a)) := by simp only [div_eq_mul_inv]; ac_rfl
    _ = _ := by rw [hrec, barnesDoubleGammaRow_exponential_add_one a z ha]; field_simp

/-- The normalized row products satisfy

```text
(∏ R_n(z+1,tau)) Gamma(1+z/tau)⁻¹ exp(-gamma z/tau) = ∏ R_n(z,tau).
```

This is the convergent product version of `barnesDoubleGammaNormalizedRow_add_one`,
with its Euler factor evaluated by `barnesGamma_hasProd_euler`. -/
lemma barnesDoubleGammaNormalizedRow_tprod_add_one (z tau : ℂ) (htau : tau ∈ Complex.slitPlane) :
    (∏' n, barnesDoubleGammaNormalizedRow (z + 1) tau n) *
        ((Complex.Gamma (1 + z / tau))⁻¹ *
          Complex.exp (-(Real.eulerMascheroniConstant : ℂ) * (z / tau))) =
      ∏' n, barnesDoubleGammaNormalizedRow z tau n := by
  have htau0 : tau ≠ 0 := Complex.slitPlane_ne_zero htau
  have hp := (multipliable_barnesDoubleGammaNormalizedRow (z + 1) tau htau).hasProd.mul
    (barnesGamma_hasProd_euler (z / tau))
  have hrow : (fun n : ℕ => barnesDoubleGammaNormalizedRow (z + 1) tau n *
      ((1 + z / tau / (1 + n)) * Complex.exp (-(z / tau) / (1 + n)))) =
        barnesDoubleGammaNormalizedRow z tau := by
    funext n
    simpa only [Nat.cast_add, Nat.cast_one, div_div, neg_div, mul_comm tau,
      add_comm (1 : ℂ)] using barnesDoubleGammaNormalizedRow_add_one z tau n htau0
  rw [hrow] at hp
  exact hp.tprod_eq.symm

/-! ### The period-one difference equation

The shift of the ordinary reciprocal gamma factor supplies `z`, while the normalized-row
shift supplies `Gamma(1+z/tau)⁻¹`. Their reciprocal-gamma recurrence leaves only `tau`.
The explicit quadratic normalization absorbs that factor and the Euler exponential.
-/

/-- The quadratic normalization at `z+1` equals its value at `z` times the elementary
period-one multiplier, `tau`, and `exp(-gamma z/tau)`. This is the exponential cancellation
used in `barnesDoubleGammaInv_add_one_mul_inv_Gamma`. -/
private lemma barnesDoubleGamma_normalization_add_one (z tau : ℂ) (htau : tau ≠ 0) :
    Complex.exp (((z + 1) ^ 2 - (z + 1)) *
        (Complex.log tau - (Real.eulerMascheroniConstant : ℂ)) / (2 * tau) +
      (z + 1) * (Complex.log tau - (Real.log (2 * Real.pi) : ℂ)) / 2) =
    tau * Complex.exp ((z ^ 2 - z) *
        (Complex.log tau - (Real.eulerMascheroniConstant : ℂ)) / (2 * tau) +
      z * (Complex.log tau - (Real.log (2 * Real.pi) : ℂ)) / 2) *
      Complex.exp ((z / tau - 1 / 2) * Complex.log tau -
        (Real.log (2 * Real.pi) : ℂ) / 2) *
      Complex.exp (-(Real.eulerMascheroniConstant : ℂ) * (z / tau)) := by
  conv_rhs => lhs; lhs; lhs; rw [← Complex.exp_log htau]
  simp only [← Complex.exp_add]
  congr 1
  field_simp
  ring

/-- The period-one difference equation

```text
Gamma₂(z+1;1,tau)⁻¹ Gamma(z/tau)⁻¹ =
  exp((z/tau-1/2) log(tau) - log(2pi)/2) Gamma₂(z;1,tau)⁻¹.
```

This is the first difference equation of [95, Shintani (1977), Proposition 1 on p. 172],
specialized to periods `(1,tau)`; the extension to nonreal period ratios is stated in
paragraph 1.6 on p. 181. Multiplying through by reciprocal gamma makes the equation valid
at every `z`, including gamma poles. -/
@[source "95, Proposition 1, p. 172 (first difference equation, periods (1, τ))"]
theorem barnesDoubleGammaInv_add_one_mul_inv_Gamma (z tau : ℂ) (htau : tau ∈ Complex.slitPlane) :
    barnesDoubleGammaInv (z + 1) 1 tau * (Complex.Gamma (z / tau))⁻¹ =
      Complex.exp ((z / tau - 1 / 2) * Complex.log tau -
        (Real.log (2 * Real.pi) : ℂ) / 2) * barnesDoubleGammaInv z 1 tau := by
  have htau0 : tau ≠ 0 := Complex.slitPlane_ne_zero htau
  have hrows := barnesDoubleGammaNormalizedRow_tprod_add_one z tau htau
  rw [barnesDoubleGammaInv_eq_normalizedRow_tprod (z + 1) tau htau,
    barnesDoubleGammaInv_eq_normalizedRow_tprod z tau htau,
    barnesDoubleGamma_normalization_add_one z tau htau0,
    Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (z / tau),
    Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one z]
  rw [add_comm (z / tau) 1]
  calc
    _ = Complex.exp ((z / tau - 1 / 2) * Complex.log tau -
          (Real.log (2 * Real.pi) : ℂ) / 2) *
        (z * (Complex.Gamma (z + 1))⁻¹ *
          Complex.exp ((z ^ 2 - z) *
              (Complex.log tau - (Real.eulerMascheroniConstant : ℂ)) / (2 * tau) +
            z * (Complex.log tau - (Real.log (2 * Real.pi) : ℂ)) / 2)) *
        ((∏' n, barnesDoubleGammaNormalizedRow (z + 1) tau n) *
          ((Complex.Gamma (1 + z / tau))⁻¹ *
            Complex.exp (-(Real.eulerMascheroniConstant : ℂ) * (z / tau)))) := by
      field_simp
    _ = _ := by rw [hrows]; ring

/-! ### The second-period difference equation

As in [95, Shintani (1977), proof of Proposition 1, p. 173], interchange the periods.
The scaled cone and normalization reduce the first-period shift for `(τ,1)` to the
proved row equation for `(1,τ⁻¹)`. The logarithmic scaling corrections cancel its
multiplier, leaving `exp(-log(2π)/2)`. The slit plane is preserved by inversion.
-/

/-- Inversion preserves the slit plane, so the scaled row equation applies at `τ⁻¹`
in `barnesDoubleGammaInv_add_tau_mul_inv_Gamma`. -/
private lemma barnesDoubleGamma_inv_mem_slitPlane {tau : ℂ}
    (htau : tau ∈ Complex.slitPlane) : tau⁻¹ ∈ Complex.slitPlane := by
  have hnorm := Complex.normSq_pos.mpr (Complex.slitPlane_ne_zero htau)
  rcases htau with h | h
  · left
    simpa [Complex.inv_re] using div_pos h hnorm
  · right
    simpa [Complex.inv_im] using div_ne_zero (neg_ne_zero.mpr h) hnorm.ne'

/-- The scaled swapped-period product is
`Γ₂(z;τ,1)⁻¹ = τ exp((z²-(τ+1)z)log(τ)/(2τ)) Γ₂(z/τ;1,τ⁻¹)⁻¹`.
This specializes `barnesDoubleGammaInv_rescale` to the second-period calculation. -/
private lemma barnesDoubleGammaInv_swapped_rescale (z tau : ℂ)
    (htau : tau ∈ Complex.slitPlane) :
    barnesDoubleGammaInv z tau 1 = tau *
      Complex.exp ((z ^ 2 - (tau + 1) * z) / (2 * tau) * Complex.log tau) *
      barnesDoubleGammaInv (z / tau) 1 tau⁻¹ := by
  have htau0 := Complex.slitPlane_ne_zero htau
  rw [barnesDoubleGammaInv_rescale z tau 1 htau0 one_ne_zero]
  simp only [one_div, mul_one, inv_one, Complex.log_one,
    Complex.log_inv tau (Complex.slitPlane_arg_ne_pi htau)]
  congr 2
  congr 1
  field_simp
  ring

/-- The second-period equation
`Γ₂(z+τ;1,τ)⁻¹ Γ(z)⁻¹ = exp(-log(2π)/2) Γ₂(z;1,τ)⁻¹`
for `τ∈ℂ \ (-∞,0]` and every complex `z`, including gamma poles.
This is the second difference equation of
[95, Shintani (1977), Proposition 1, p. 172], on the continued domain of
[95, Shintani (1977), paragraph 1.6, p. 181]. -/
@[source "95, Proposition 1, p. 172 (second difference equation, periods (1, τ))"]
theorem barnesDoubleGammaInv_add_tau_mul_inv_Gamma (z tau : ℂ)
    (htau : tau ∈ Complex.slitPlane) :
    barnesDoubleGammaInv (z + tau) 1 tau * (Complex.Gamma z)⁻¹ =
      Complex.exp (-(Real.log (2 * Real.pi) : ℂ) / 2) *
        barnesDoubleGammaInv z 1 tau := by
  have htau0 := Complex.slitPlane_ne_zero htau
  have hrow := barnesDoubleGammaInv_add_one_mul_inv_Gamma (z / tau) tau⁻¹
    (barnesDoubleGamma_inv_mem_slitPlane htau)
  have hshift : (z + tau) / tau = z / tau + 1 := by field_simp
  have hdiv : z / tau / tau⁻¹ = z := by field_simp
  rw [hdiv, Complex.log_inv tau (Complex.slitPlane_arg_ne_pi htau)] at hrow
  have hsym (w : ℂ) : barnesDoubleGammaInv w 1 tau = barnesDoubleGammaInv w tau 1 := by
    simpa using barnesDoubleGammaInv_symm w 1 tau (by norm_num) htau
  rw [hsym (z + tau), hsym z,
    barnesDoubleGammaInv_swapped_rescale (z + tau) tau htau,
    barnesDoubleGammaInv_swapped_rescale z tau htau, hshift, mul_assoc, hrow]
  simp only [← mul_assoc]
  congr 1
  simp only [mul_assoc, ← Complex.exp_add]
  rw [mul_left_comm (Complex.exp _) tau, ← Complex.exp_add]
  congr 2
  field_simp
  ring

/-! ### The normalization at the positive period sum

The normalized rows equal one at `z=1` by the ordinary gamma recurrence. The
second-period equation then evaluates `Γ₂(1+τ)⁻¹`, the constant used in
[95, Shintani (1977), proof of Proposition 5, p. 181].
-/

/-- Each normalized row has `R_n(1,τ)=1`. This evaluates the row product in
`barnesDoubleGammaInv_one`. -/
private lemma barnesDoubleGammaNormalizedRow_one (tau : ℂ)
    (htau : tau ∈ Complex.slitPlane) (n : ℕ) :
    barnesDoubleGammaNormalizedRow 1 tau n = 1 := by
  let a : ℂ := ((n + 1 : ℕ) : ℂ) * tau
  have ha : a ≠ 0 := mul_ne_zero (by exact_mod_cast n.succ_ne_zero)
    (Complex.slitPlane_ne_zero htau)
  have hGamma : Complex.Gamma a ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hm
    have hn : (0 : ℝ) < n + 1 := by positivity
    rcases htau with ht | ht
    · have : 0 < a.re := by simpa [a, mul_re] using mul_pos hn ht
      have : a.re ≤ 0 := by rw [hm]; simp
      linarith
    · have he := congrArg Complex.im hm
      simp [a, mul_im] at he
      exact ht (he.resolve_left (ne_of_gt hn))
  simp only [barnesDoubleGammaNormalizedRow, one_pow, sub_self, zero_div,
    one_mul, add_zero]
  change Complex.Gamma a / Complex.Gamma (a + 1) * Complex.exp (Complex.log a) = 1
  rw [Complex.Gamma_add_one a ha, Complex.exp_log ha]
  field_simp

/-- `Γ₂(1;1,τ)⁻¹ = exp((log τ-log(2π))/2)`, the first evaluation needed for
`barnesDoubleGammaInv_one_add_tau`, obtained from the normalized row formula. -/
lemma barnesDoubleGammaInv_one (tau : ℂ) (htau : tau ∈ Complex.slitPlane) :
    barnesDoubleGammaInv 1 1 tau =
      Complex.exp ((Complex.log tau - (Real.log (2 * Real.pi) : ℂ)) / 2) := by
  rw [barnesDoubleGammaInv_eq_normalizedRow_tprod 1 tau htau]
  simp [barnesDoubleGammaNormalizedRow_one tau htau]

/-- `Γ₂(1+τ;1,τ)⁻¹ = exp(log τ/2-log(2π))`.
This is the exponential form of the normalization `Γ₂(1+τ)=2π/√τ` in
[95, Shintani (1977), proof of Proposition 5, p. 181]. -/
lemma barnesDoubleGammaInv_one_add_tau (tau : ℂ) (htau : tau ∈ Complex.slitPlane) :
    barnesDoubleGammaInv (1 + tau) 1 tau =
      Complex.exp (Complex.log tau / 2 - (Real.log (2 * Real.pi) : ℂ)) := by
  have h := barnesDoubleGammaInv_add_tau_mul_inv_Gamma 1 tau htau
  simpa only [Complex.Gamma_one, inv_one, mul_one, barnesDoubleGammaInv_one tau htau,
    ← Complex.exp_add, show -(Real.log (2 * Real.pi) : ℂ) / 2 +
      (Complex.log tau - (Real.log (2 * Real.pi) : ℂ)) / 2 =
      Complex.log tau / 2 - (Real.log (2 * Real.pi) : ℂ) by ring] using h

end SIC

end
