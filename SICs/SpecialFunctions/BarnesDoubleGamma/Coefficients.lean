/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.Digamma.Series
import SICs.SpecialFunctions.Mellin.TrigammaRemainder
import SICs.SpecialFunctions.Mellin.DigammaRemainder
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Shintani's Barnes double gamma normalization coefficients

Shintani's two normalization series and both symmetries of his Lemma 1.

This file defines the exact digamma series `gamma₂₁` and `gamma₂₂` in
[95, Shintani (1977), equations (1.1)–(1.2)]. The digamma and trigamma ray estimates make
both remainder series absolutely summable when `omega₂/omega₁ ∈ ℂ \ (-∞,0]`. The two series
supply the normalization of the genus-two product in
`SICs.SpecialFunctions.BarnesDoubleGamma.Product`.

Shintani's paragraph 1.6 on p. 181 extends the coefficients from positive periods to
`omega₂/omega₁` not a negative real number. The definitions follow this source normalization,
with the sign inconsistency in (1.2) recorded at `barnesGamma21`.
They are total functions; the `tsum` takes its default
value if the series fails to converge. The convergence theorems cover the full slit plane.
On the positive real axis, the inverse Mellin representations prove convergence of
Shintani's two remainder sums. Their transformations
under `t ↦ t⁻¹` prove both coefficient symmetries, completing the source's proof of Lemma 1
on its original domain. Locally uniform convergence of the defining series gives
holomorphic dependence on the period ratio. The identity theorem then extends both
symmetries to the domain of paragraph 1.6.

The normalized row product and both difference equations are proved in
`SICs.SpecialFunctions.BarnesDoubleGamma.Normalization` and
`SICs.SpecialFunctions.BarnesDoubleGamma.Difference`. The continued symmetries supply
the coefficient identities needed for the second-period equation.
-/

noncomputable section

open Complex Real Set Filter

namespace SIC

/-! ### Shintani's normalization coefficients -/

/-- The series defining Shintani's coefficient `gamma₂₁(omega₁,omega₂)` is absolutely summable
when `omega₂/omega₁ ∈ ℂ \ (-∞,0]`.  This specializes
`summable_deriv_digamma_mul_sub_inv` to the exact ratio form used in
[95, Shintani (1977), equation (1.2) on p. 170]. -/
theorem summable_barnesGamma21Series (omega₁ omega₂ : ℂ)
    (hratio : omega₂ / omega₁ ∈ Complex.slitPlane) :
    Summable (fun n : ℕ =>
      deriv Complex.digamma (((n + 1 : ℕ) : ℂ) * omega₂ / omega₁) -
        omega₁ / (((n + 1 : ℕ) : ℂ) * omega₂)) := by
  have homega₁ := (div_ne_zero_iff.mp (Complex.slitPlane_ne_zero hratio)).2
  have homega₂ := (div_ne_zero_iff.mp (Complex.slitPlane_ne_zero hratio)).1
  apply (summable_deriv_digamma_mul_sub_inv (omega₂ / omega₁) hratio).congr
  intro n
  have hn : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.add_one_ne_zero n
  congr 1
  · ring_nf
  · field_simp [homega₁, homega₂, hn]

/-- Shintani's coefficient `gamma₂₁(omega₁,omega₂)`:

```text
-gamma₂₁ = omega₁⁻² ∑_{n≥1}
    (psi'(n omega₂/omega₁) - omega₁/(n omega₂))
  + pi²/(6 omega₁²) - log(omega₂)/(omega₁ omega₂)
  + gamma/(omega₁ omega₂).
```

Here `psi = Complex.digamma` and `gamma` is Euler's constant. This is
[95, Shintani (1977), paragraph 0-2, p. 167] and
[95, Shintani (1977), proof of Lemma 1, p. 171]. Equation (1.2) on p. 170
prints `-gamma/(omega₁ omega₂)` instead; the definition follows the positive
sign in the introduction and proof. The difference is symmetric in the periods,
so it does not affect Lemma 1, but it does affect the double-gamma normalization.

The `tsum` is the exact published series; `summable_barnesGamma21Series` proves its
convergence throughout the slit plane. If the series fails to converge, the `tsum`
takes Lean's default value `0`. The normalized row product and period-one difference equation
use this coefficient. Positive-period symmetry is `barnesGamma21_symm_of_pos`;
`barnesGamma21_symm` extends it to the slit plane. -/
@[source "95, equation (1.2), p. 170" (symbol := "γ₂₁(ω)")]
noncomputable def barnesGamma21 (omega₁ omega₂ : ℂ) : ℂ :=
  -((omega₁ ^ 2)⁻¹ * ∑' n : ℕ,
      (deriv Complex.digamma (((n + 1 : ℕ) : ℂ) * omega₂ / omega₁) -
        omega₁ / (((n + 1 : ℕ) : ℂ) * omega₂)) +
    π ^ 2 / (6 * omega₁ ^ 2) - Complex.log omega₂ / (omega₁ * omega₂) +
    (Real.eulerMascheroniConstant : ℂ) / (omega₁ * omega₂))

/-! ### Symmetry of the first coefficient

Insert `t=omega₂/omega₁` in the first remainder transformation and multiply by
`omega₁⁻²`. Its correction `t⁻¹ log(t)` changes the logarithmic term from
`log(omega₂)` to `log(omega₁)`. The remaining terms are symmetric. This is
the first part of [95, Shintani (1977), Lemma 1 and its proof, pp. 170–171].
-/

/-- The defining series of `barnesGamma21` at real periods is
`f₁(omega₂/omega₁)`. This rewrites the coefficient for `barnesGamma21_symm_of_pos`. -/
private lemma barnesGamma21_eq_trigammaRemainderSum (omega₁ omega₂ : ℝ) :
    barnesGamma21 omega₁ omega₂ =
      -(((omega₁ : ℂ) ^ 2)⁻¹ * trigammaRemainderSum (omega₂ / omega₁) +
        (Real.pi : ℂ) ^ 2 / (6 * (omega₁ : ℂ) ^ 2) -
        Complex.log omega₂ / ((omega₁ : ℂ) * omega₂) +
        (Real.eulerMascheroniConstant : ℂ) / ((omega₁ : ℂ) * omega₂)) := by
  unfold barnesGamma21 trigammaRemainderSum
  push_cast
  simp only [div_eq_mul_inv, mul_inv, inv_inv, mul_assoc, mul_comm, mul_left_comm]

/-- For positive periods, `gamma₂₁(omega₁,omega₂)=gamma₂₁(omega₂,omega₁)`.
This is the first assertion of [95, Shintani (1977), Lemma 1, p. 170]. -/
@[source "95, Lemma 1, p. 170 (γ₂₁)"]
theorem barnesGamma21_symm_of_pos (omega₁ omega₂ : ℝ) (h₁ : 0 < omega₁) (h₂ : 0 < omega₂) :
    barnesGamma21 omega₁ omega₂ = barnesGamma21 omega₂ omega₁ := by
  have h := trigammaRemainderSum_add_eq (omega₂ / omega₁) (div_pos h₂ h₁)
  rw [inv_div, Real.log_div h₂.ne' h₁.ne'] at h
  push_cast at h
  rw [Complex.ofReal_log h₁.le, Complex.ofReal_log h₂.le] at h
  rw [barnesGamma21_eq_trigammaRemainderSum, barnesGamma21_eq_trigammaRemainderSum]
  have h₁0 := Complex.ofReal_ne_zero.mpr h₁.ne'
  have h₂0 := Complex.ofReal_ne_zero.mpr h₂.ne'
  field_simp at h ⊢
  linear_combination -h

/-! ### The second coefficient

The corrected digamma series defines `gamma₂₂`. Shintani's second remainder
transformation, equation (1.4), gives its positive-period symmetry below.
-/

/-- The series defining Shintani's coefficient `gamma₂₂(omega₁,omega₂)` is absolutely summable
when `omega₂/omega₁ ∈ ℂ \ (-∞,0]`.  This specializes
`summable_digamma_mul_sub_log_add_half_inv` to the exact ratio form used in
[95, Shintani (1977), equation (1.1) on p. 170]. -/
theorem summable_barnesGamma22Series (omega₁ omega₂ : ℂ)
    (hratio : omega₂ / omega₁ ∈ Complex.slitPlane) :
    Summable (fun n : ℕ =>
      Complex.digamma (((n + 1 : ℕ) : ℂ) * omega₂ / omega₁) -
        Complex.log (((n + 1 : ℕ) : ℂ) * omega₂ / omega₁) +
        omega₁ / (2 * ((n + 1 : ℕ) : ℂ) * omega₂)) := by
  have homega₁ := (div_ne_zero_iff.mp (Complex.slitPlane_ne_zero hratio)).2
  have homega₂ := (div_ne_zero_iff.mp (Complex.slitPlane_ne_zero hratio)).1
  apply (summable_digamma_mul_sub_log_add_half_inv (omega₂ / omega₁) hratio).congr
  intro n
  have hn : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.add_one_ne_zero n
  congr 1
  · congr 1 <;> ring_nf
  · field_simp [homega₁, homega₂, hn]

/-- Shintani's coefficient `gamma₂₂(omega₁,omega₂)`:

```text
-gamma₂₂ = omega₁⁻¹ ∑_{n≥1}
    (psi(n omega₂/omega₁) - log(n omega₂/omega₁)
      + omega₁/(2n omega₂))
  + (omega₁⁻¹+omega₂⁻¹)log(omega₁)/2
  - (gamma-log(2pi))/(2omega₁)
  + (omega₁-omega₂)log(omega₂/omega₁)/(2omega₁ omega₂)
  - gamma(omega₁⁻¹+omega₂⁻¹)/2.
```

This is [95, Shintani (1977), equation (1.1)].

The `tsum` is the exact published series; `summable_barnesGamma22Series` proves its
convergence throughout the slit plane. If the series fails to converge, the `tsum` takes
Lean's default value `0`. The normalized row product and period-one difference equation
use this coefficient.
Positive-period symmetry is `barnesGamma22_symm_of_pos`; `barnesGamma22_symm`
extends it to the slit plane. -/
@[source "95, equation (1.1), p. 170" (symbol := "γ₂₂(ω)")]
noncomputable def barnesGamma22 (omega₁ omega₂ : ℂ) : ℂ :=
  -(omega₁⁻¹ * ∑' n : ℕ,
      (Complex.digamma (((n + 1 : ℕ) : ℂ) * omega₂ / omega₁) -
        Complex.log (((n + 1 : ℕ) : ℂ) * omega₂ / omega₁) +
        omega₁ / (2 * ((n + 1 : ℕ) : ℂ) * omega₂)) +
    (omega₁⁻¹ + omega₂⁻¹) * Complex.log omega₁ / 2 -
    ((Real.eulerMascheroniConstant : ℂ) - (Real.log (2 * π) : ℂ)) / (2 * omega₁) +
    (omega₁ - omega₂) / (2 * omega₁ * omega₂) * Complex.log (omega₂ / omega₁) -
    (Real.eulerMascheroniConstant : ℂ) / 2 * (omega₁⁻¹ + omega₂⁻¹))

/-! ### Symmetry of the second coefficient

In equation (1.1), group `f₂(t)+log(2pi)/2-gamma/2-log(t)/2` with
`t=omega₂/omega₁`. Equation (1.4) makes this group invariant after multiplying
by `omega₁⁻¹` and interchanging the periods. The other logarithmic terms are
symmetric directly. This completes [95, Shintani (1977), Lemma 1, pp. 170–171]
on its original positive-period domain.
-/

/-- The series in `gamma₂₂` is `f₂(omega₂/omega₁)`.
This rewrites the coefficient for `barnesGamma22_symm_of_pos`. -/
private lemma barnesGamma22_eq_digammaRemainderSum (omega₁ omega₂ : ℝ) :
    barnesGamma22 omega₁ omega₂ =
      -((omega₁ : ℂ)⁻¹ * digammaRemainderSum (omega₂ / omega₁) +
        ((omega₁ : ℂ)⁻¹ + (omega₂ : ℂ)⁻¹) * Complex.log omega₁ / 2 -
        ((Real.eulerMascheroniConstant : ℂ) - (Real.log (2 * π) : ℂ)) / (2 * omega₁) +
        ((omega₁ : ℂ) - omega₂) / (2 * omega₁ * omega₂) *
          Complex.log ((omega₂ : ℂ) / omega₁) -
        (Real.eulerMascheroniConstant : ℂ) / 2 * ((omega₁ : ℂ)⁻¹ + (omega₂ : ℂ)⁻¹)) := by
  unfold barnesGamma22 digammaRemainderSum
  push_cast
  simp only [div_eq_mul_inv, mul_inv, inv_inv, mul_assoc, mul_comm, mul_left_comm]

/-- For positive real `a,b`, the complex principal logarithm satisfies
`log(a/b)=log(a)-log(b)`. This bridges the real remainder transformation to
the logarithms in `barnesGamma22_symm_of_pos`. -/
private lemma log_div_pos_periods (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Complex.log ((a : ℂ) / b) = Complex.log a - Complex.log b := by
  rw [← Complex.ofReal_div, ← Complex.ofReal_log (div_pos ha hb).le,
    Real.log_div ha.ne' hb.ne', Complex.ofReal_sub,
    Complex.ofReal_log ha.le, Complex.ofReal_log hb.le]

/-- For positive periods, `gamma₂₂(omega₁,omega₂)=gamma₂₂(omega₂,omega₁)`.
This is the second assertion of [95, Shintani (1977), Lemma 1, p. 170]. -/
@[source "95, Lemma 1, p. 170 (γ₂₂)"]
theorem barnesGamma22_symm_of_pos (omega₁ omega₂ : ℝ) (h₁ : 0 < omega₁) (h₂ : 0 < omega₂) :
    barnesGamma22 omega₁ omega₂ = barnesGamma22 omega₂ omega₁ := by
  have h := digammaRemainderSum_add_eq (omega₂ / omega₁) (div_pos h₂ h₁)
  rw [inv_div, Real.log_div h₂.ne' h₁.ne', Real.log_div h₁.ne' h₂.ne'] at h
  push_cast at h
  rw [Complex.ofReal_log h₁.le, Complex.ofReal_log h₂.le] at h
  rw [barnesGamma22_eq_digammaRemainderSum, barnesGamma22_eq_digammaRemainderSum,
    log_div_pos_periods omega₂ omega₁ h₂ h₁, log_div_pos_periods omega₁ omega₂ h₁ h₂,
    Complex.ofReal_log (by positivity : 0 ≤ 2 * π)]
  push_cast
  have h₁0 := Complex.ofReal_ne_zero.mpr h₁.ne'
  have h₂0 := Complex.ofReal_ne_zero.mpr h₂.ne'
  field_simp at h ⊢
  linear_combination -h

/-! ### Analytic continuation of the symmetry identities

The defining series are locally uniformly convergent and holomorphic in the
ratio `ω₂/ω₁` on the slit plane. Their elementary normalization factors are
holomorphic wherever the principal logarithms are defined. With `ω₁>0`
fixed, both orders of the periods therefore give holomorphic functions of
`ω₂` on the same connected slit plane. Their equality on the positive real
axis extends by the identity theorem. This is the continuation of Lemma 1
asserted in [95, Shintani (1977), paragraph 1.6, p. 181].
-/

/-- Write the series in `γ₂₁` as a function of the ratio `ω₂/ω₁`.
This exposes the holomorphic sum for `differentiableAt_barnesGamma21_comp`. -/
private lemma barnesGamma21_eq_tsum_ratio (omega₁ omega₂ : ℂ) :
    barnesGamma21 omega₁ omega₂ =
      -((omega₁ ^ 2)⁻¹ * ∑' n : ℕ,
        (deriv Complex.digamma (((n + 1 : ℕ) : ℂ) * (omega₂ / omega₁)) -
          (((n + 1 : ℕ) : ℂ) * (omega₂ / omega₁))⁻¹) +
        π ^ 2 / (6 * omega₁ ^ 2) - Complex.log omega₂ / (omega₁ * omega₂) +
        (Real.eulerMascheroniConstant : ℂ) / (omega₁ * omega₂)) := by
  simp only [barnesGamma21, div_eq_mul_inv, mul_inv, inv_inv,
    mul_assoc, mul_comm, mul_left_comm]

/-- Write the series in `γ₂₂` as a function of the ratio `ω₂/ω₁`.
This exposes the holomorphic sum for `differentiableAt_barnesGamma22_comp`. -/
private lemma barnesGamma22_eq_tsum_ratio (omega₁ omega₂ : ℂ) :
    barnesGamma22 omega₁ omega₂ =
      -(omega₁⁻¹ * ∑' n : ℕ,
        (Complex.digamma (((n + 1 : ℕ) : ℂ) * (omega₂ / omega₁)) -
          Complex.log (((n + 1 : ℕ) : ℂ) * (omega₂ / omega₁)) +
          (((n + 1 : ℕ) : ℂ) * (omega₂ / omega₁))⁻¹ / 2) +
        (omega₁⁻¹ + omega₂⁻¹) * Complex.log omega₁ / 2 -
        ((Real.eulerMascheroniConstant : ℂ) - (Real.log (2 * π) : ℂ)) / (2 * omega₁) +
        (omega₁ - omega₂) / (2 * omega₁ * omega₂) * Complex.log (omega₂ / omega₁) -
        (Real.eulerMascheroniConstant : ℂ) / 2 * (omega₁⁻¹ + omega₂⁻¹)) := by
  simp only [barnesGamma22, div_eq_mul_inv, mul_inv, inv_inv,
    mul_assoc, mul_comm, mul_left_comm]

/-- Holomorphic periods give a holomorphic `γ₂₁(ω₁,ω₂)` where
`ω₁≠0` and both `ω₂` and `ω₂/ω₁` lie in `ℂ \ (-∞,0]`.
This makes the coefficient continuation in [95, Shintani (1977), paragraph 1.6,
p. 181] explicit, using `differentiableOn_tsum_trigamma_remainder`. -/
theorem differentiableAt_barnesGamma21_comp {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z)
    (hgslit : g z ∈ Complex.slitPlane) (hratio : g z / f z ∈ Complex.slitPlane) :
    DifferentiableAt ℂ (fun w => barnesGamma21 (f w) (g w)) z := by
  have hf0 := (div_ne_zero_iff.mp (Complex.slitPlane_ne_zero hratio)).2
  have hg0 := Complex.slitPlane_ne_zero hgslit
  have hsum := (differentiableOn_tsum_trigamma_remainder.differentiableAt
    (Complex.isOpen_slitPlane.mem_nhds hratio)).comp z (hg.div hf hf0)
  have hquad := (differentiableAt_const (π ^ 2 : ℂ)).div ((hf.pow 2).const_mul 6)
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 hf0))
  have hlog := (hg.clog hgslit).div (hf.mul hg) (mul_ne_zero hf0 hg0)
  have heuler := (differentiableAt_const (Real.eulerMascheroniConstant : ℂ)).div
    (hf.mul hg) (mul_ne_zero hf0 hg0)
  simp_rw [barnesGamma21_eq_tsum_ratio]
  exact (((((hf.pow 2).inv (pow_ne_zero _ hf0)).mul hsum).add hquad |>.sub hlog).add
    heuler).neg

/-- Holomorphic periods give a holomorphic `γ₂₂(ω₁,ω₂)` where
`ω₁` and `ω₂/ω₁` lie in `ℂ \ (-∞,0]`.
This is the regularity needed for the coefficient continuation in
[95, Shintani (1977), paragraph 1.6, p. 181], using
`differentiableOn_tsum_digamma_remainder`. -/
theorem differentiableAt_barnesGamma22_comp {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z)
    (hfslit : f z ∈ Complex.slitPlane) (hratio : g z / f z ∈ Complex.slitPlane) :
    DifferentiableAt ℂ (fun w => barnesGamma22 (f w) (g w)) z := by
  have hf0 := Complex.slitPlane_ne_zero hfslit
  have hg0 := (div_ne_zero_iff.mp (Complex.slitPlane_ne_zero hratio)).1
  have hsum := (differentiableOn_tsum_digamma_remainder.differentiableAt
    (Complex.isOpen_slitPlane.mem_nhds hratio)).comp z (hg.div hf hf0)
  have hinv := (hf.inv hf0).add (hg.inv hg0)
  have hden := (hf.const_mul 2).mul hg
  have hden0 : (2 : ℂ) * f z * g z ≠ 0 := by simp [hf0, hg0]
  have hconstant := (differentiableAt_const
    ((Real.eulerMascheroniConstant : ℂ) - (Real.log (2 * π) : ℂ))).div
    (hf.const_mul 2) (by simp [hf0])
  have hlog := ((hf.sub hg).div hden hden0).mul ((hg.div hf hf0).clog hratio)
  simp_rw [barnesGamma22_eq_tsum_ratio]
  exact ((((((hf.inv hf0).mul hsum).add ((hinv.mul (hf.clog hfslit)).div_const 2)).sub
    hconstant).add hlog).sub (hinv.const_mul ((Real.eulerMascheroniConstant : ℂ) / 2))).neg

/-- Division by a positive real period preserves the slit plane.
This supplies the forward ratio in the coefficient continuation. -/
private lemma slitPlane_div_pos {z : ℂ} (hz : z ∈ Complex.slitPlane)
    {a : ℝ} (ha : 0 < a) : z / a ∈ Complex.slitPlane := by
  rcases hz with h | h
  · left
    simpa using div_pos h ha
  · right
    simpa using div_ne_zero h ha.ne'

/-- The reciprocal ratio `a/z` lies in the slit plane when `a>0` and
`z` lies there. This supplies the swapped ratio in the coefficient continuation. -/
private lemma slitPlane_pos_div {z : ℂ} (hz : z ∈ Complex.slitPlane)
    {a : ℝ} (ha : 0 < a) : (a : ℂ) / z ∈ Complex.slitPlane := by
  have hz0 := Complex.slitPlane_ne_zero hz
  rcases hz with h | h
  · left
    simpa [Complex.div_re] using div_pos (mul_pos ha h) (Complex.normSq_pos.mpr hz0)
  · right
    simpa [Complex.div_im] using div_ne_zero (neg_ne_zero.mpr (mul_ne_zero ha.ne' h))
      (Complex.normSq_pos.mpr hz0).ne'

/-- Holomorphic functions on the slit plane that agree for all positive
real arguments agree throughout the domain. This applies the identity theorem
at the accumulation point `1` for both coefficient symmetries. -/
private lemma eqOn_slitPlane_of_eq_pos {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f Complex.slitPlane)
    (hg : DifferentiableOn ℂ g Complex.slitPlane)
    (hpos : ∀ t : ℝ, 0 < t → f t = g t) : Set.EqOn f g Complex.slitPlane := by
  apply (hf.analyticOnNhd Complex.isOpen_slitPlane).eqOn_of_preconnected_of_mem_closure
    (hg.analyticOnNhd Complex.isOpen_slitPlane)
    (Complex.starConvex_one_slitPlane.isPathConnected Complex.one_mem_slitPlane).isConnected.2
    Complex.one_mem_slitPlane
  have hinv : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hreal : Tendsto (fun n : ℕ => (1 : ℝ) + (((n + 1 : ℕ) : ℝ))⁻¹) atTop
      (nhds 1) := by simpa using tendsto_const_nhds.add hinv
  apply mem_closure_of_tendsto (Complex.continuous_ofReal.tendsto 1 |>.comp hreal)
  filter_upwards with n
  refine ⟨hpos _ (by positivity), ?_⟩
  change ((1 + (((n + 1 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) ≠ 1
  intro h
  have heq := Complex.ofReal_injective h
  have hpos : (0 : ℝ) < (((n + 1 : ℕ) : ℝ))⁻¹ := by positivity
  linarith

/-- For `ω₁>0` and `ω₂∈ℂ \ (-∞,0]`,
`γ₂₁(ω₁,ω₂)=γ₂₁(ω₂,ω₁)`, with principal logarithms.
This is the continuation of the first assertion of Lemma 1 in
[95, Shintani (1977), paragraph 1.6, p. 181], extending
`barnesGamma21_symm_of_pos`. -/
theorem barnesGamma21_symm (omega₁ : ℝ) (omega₂ : ℂ)
    (h₁ : 0 < omega₁) (h₂ : omega₂ ∈ Complex.slitPlane) :
    barnesGamma21 omega₁ omega₂ = barnesGamma21 omega₂ omega₁ := by
  apply eqOn_slitPlane_of_eq_pos (f := barnesGamma21 omega₁)
    (g := fun z => barnesGamma21 z omega₁) ?_ ?_
    (fun t ht => barnesGamma21_symm_of_pos omega₁ t h₁ ht) h₂
  · intro z hz
    exact (differentiableAt_barnesGamma21_comp (differentiableAt_const _) differentiableAt_id
      hz (slitPlane_div_pos hz h₁)).differentiableWithinAt
  · intro z hz
    exact (differentiableAt_barnesGamma21_comp differentiableAt_id (differentiableAt_const _)
      (Complex.ofReal_mem_slitPlane.mpr h₁) (slitPlane_pos_div hz h₁)).differentiableWithinAt

/-- For `ω₁>0` and `ω₂∈ℂ \ (-∞,0]`,
`γ₂₂(ω₁,ω₂)=γ₂₂(ω₂,ω₁)`, with principal logarithms.
This is the continuation of the second assertion of Lemma 1 in
[95, Shintani (1977), paragraph 1.6, p. 181], extending
`barnesGamma22_symm_of_pos`. -/
theorem barnesGamma22_symm (omega₁ : ℝ) (omega₂ : ℂ)
    (h₁ : 0 < omega₁) (h₂ : omega₂ ∈ Complex.slitPlane) :
    barnesGamma22 omega₁ omega₂ = barnesGamma22 omega₂ omega₁ := by
  apply eqOn_slitPlane_of_eq_pos (f := barnesGamma22 omega₁)
    (g := fun z => barnesGamma22 z omega₁) ?_ ?_
    (fun t ht => barnesGamma22_symm_of_pos omega₁ t h₁ ht) h₂
  · intro z hz
    exact (differentiableAt_barnesGamma22_comp (differentiableAt_const _) differentiableAt_id
      (Complex.ofReal_mem_slitPlane.mpr h₁) (slitPlane_div_pos hz h₁)).differentiableWithinAt
  · intro z hz
    exact (differentiableAt_barnesGamma22_comp differentiableAt_id (differentiableAt_const _)
      hz (slitPlane_pos_div hz h₁)).differentiableWithinAt

/-! ### Rescaling the normalization coefficients

The row argument in [95, Shintani (1977), proof of Proposition 1, pp. 172–173]
uses `z/ω₁` and the ratio `ω₂/ω₁`. The series depend only on that ratio;
rescaling the coefficients therefore leaves explicit logarithmic corrections.
These identities retain the principal logarithms separately, without a branch assumption.
-/

/-- Rescaling the quadratic coefficient gives
`ω₁² γ₂₁(ω₁,ω₂) = γ₂₁(1,ω₂/ω₁) + (ω₁/ω₂)(log ω₂-log(ω₂/ω₁))`.
This isolates the quadratic correction in the scaled row calculation of
[95, Shintani (1977), proof of Proposition 1, p. 173]. -/
lemma barnesGamma21_rescale (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    a ^ 2 * barnesGamma21 a b = barnesGamma21 1 (b / a) +
      a / b * (Complex.log b - Complex.log (b / a)) := by
  rw [barnesGamma21_eq_tsum_ratio, barnesGamma21_eq_tsum_ratio]
  simp only [div_one, one_pow, inv_one, one_mul]
  simp only [div_eq_mul_inv, mul_assoc]
  generalize (∑' n : ℕ, (_ : ℂ)) = S
  field_simp
  ring

/-- Rescaling the linear coefficient gives
`ω₁ γ₂₂(ω₁,ω₂) = γ₂₂(1,ω₂/ω₁) - (1+ω₁/ω₂) log(ω₁)/2`.
This isolates the linear correction in the scaled row calculation of
[95, Shintani (1977), proof of Proposition 1, p. 173]. -/
lemma barnesGamma22_rescale (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    a * barnesGamma22 a b = barnesGamma22 1 (b / a) -
      (1 + a / b) * Complex.log a / 2 := by
  rw [barnesGamma22_eq_tsum_ratio, barnesGamma22_eq_tsum_ratio]
  simp only [div_one, inv_one, one_mul, Complex.log_one, mul_zero, zero_div, add_zero]
  simp only [div_eq_mul_inv, mul_assoc]
  generalize (∑' n : ℕ, (_ : ℂ)) = S
  field_simp
  ring

end SIC

end
