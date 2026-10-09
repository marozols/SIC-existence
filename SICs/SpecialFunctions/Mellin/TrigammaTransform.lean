/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.Digamma.EulerLimit
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The Mellin transform of the trigamma tail

The Mellin transform of `ψ'(t)-t⁻²` on `0<Re s<1`.

This file follows the opening of [95, Shintani (1977), proof of Lemma 1 on p. 170].
The substitution `t = x/(1-x)` identifies the Mellin transform of `(1+t)⁻²` with
the beta integral. Scaling gives the transform of `(a+t)⁻²` for every `a>0`.
The reciprocal-square expansion of the trigamma function then permits summation over
positive integers: the integrals of the norms form a convergent `p`-series when
`0 < Re(s) < 1`. This yields the gamma-zeta expression to which Shintani applies
Mellin inversion in equation (1.3).

Mellin inversion and the contour estimates for the subsequent shifts are proved
in `SICs.SpecialFunctions.Mellin.TrigammaInversion`.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology ENNReal

namespace SIC

/-! ### The beta-integral substitution

The map `x ↦ x/(1-x)` carries `(0,1)` bijectively onto the positive real axis.
Its derivative cancels the reciprocal-square denominator in the Mellin integrand.
-/

/-- The beta-integral substitution maps `(0,1)` onto `(0,∞)`.
This supplies the domain change in `hasMellin_one_add_inv_sq`. -/
private lemma betaMellin_image :
    (fun x : ℝ => x / (1 - x)) '' Ioo 0 1 = Ioi 0 := by
  ext t
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact div_pos hx.1 (sub_pos.mpr hx.2)
  · intro ht
    change 0 < t at ht
    have hden : 0 < 1 + t := by linarith
    refine ⟨t / (1 + t), ⟨div_pos ht hden, (div_lt_one hden).mpr ?_⟩, ?_⟩
    · linarith
    · field_simp
      ring

/-- The beta-integral substitution is injective on `(0,1)`.
This supplies the injectivity in `hasMellin_one_add_inv_sq`. -/
private lemma betaMellin_injOn :
    InjOn (fun x : ℝ => x / (1 - x)) (Ioo 0 1) := by
  intro x hx y hy hxy
  have h := (div_eq_div_iff (sub_pos.mpr hx.2).ne'
    (sub_pos.mpr hy.2).ne').mp hxy
  nlinarith

/-- The derivative of the beta-integral substitution is `(1-x)⁻²` on `(0,1)`.
This supplies the Jacobian in `hasMellin_one_add_inv_sq`. -/
private lemma betaMellin_hasDerivAt (x : ℝ) (hx : x ∈ Ioo 0 1) :
    HasDerivAt (fun y : ℝ => y / (1 - y)) ((1 - x)⁻¹ ^ 2) x := by
  convert! (hasDerivAt_id x).div ((hasDerivAt_id x).const_sub 1)
    (sub_pos.mpr hx.2).ne' using 1
  simp [id_eq, inv_pow]

/-- The transformed Mellin integrand is the beta integrand with parameters `s` and `2-s`.
This is the pointwise calculation used in `hasMellin_one_add_inv_sq`. -/
private lemma betaMellin_integrand (s : ℂ) (x : ℝ) (hx : x ∈ Ioo 0 1) :
    |(1 - x)⁻¹ ^ 2| •
        ((↑(x / (1 - x)) : ℂ) ^ (s - 1) * (1 + (↑(x / (1 - x)) : ℂ))⁻¹ ^ 2) =
      (x : ℂ) ^ (s - 1) * (1 - x) ^ ((2 - s) - 1) := by
  have hx1 : 0 < 1 - x := sub_pos.mpr hx.2
  have hx1C : (1 - (x : ℂ)) ≠ 0 := by exact_mod_cast hx1.ne'
  rw [abs_of_nonneg (sq_nonneg _), Complex.real_smul, Complex.ofReal_pow,
    Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div,
    Complex.div_cpow_ofReal_nonneg hx.1.le hx1.le]
  push_cast
  rw [show 2 - s - 1 = -(s - 1) by ring, Complex.cpow_neg]
  field_simp [hx1C]
  ring

/-- The Mellin transform of `(1+t)⁻²` is `Gamma(s) Gamma(2-s)` for `0<Re(s)<2`.
This is the beta-integral case used to prove `hasMellin_add_inv_sq`. -/
private lemma hasMellin_one_add_inv_sq (s : ℂ) (hs : 0 < s.re) (hs2 : s.re < 2) :
    HasMellin (fun t : ℝ => (1 + (t : ℂ))⁻¹ ^ 2) s
      (Complex.Gamma s * Complex.Gamma (2 - s)) := by
  have hs' : 0 < (2 - s).re := by simp only [sub_re, re_ofNat]; linarith
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivWithinAt (fun y : ℝ => y / (1 - y)) ((1 - x)⁻¹ ^ 2) (Ioo 0 1) x :=
    fun x hx => (betaMellin_hasDerivAt x hx).hasDerivWithinAt
  have hbeta := Complex.betaIntegral_convergent hs hs'
  constructor
  · rw [MellinConvergent, ← betaMellin_image,
      integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
        hderiv betaMellin_injOn]
    refine ((hbeta.1.mono_set Ioo_subset_Ioc_self).congr_fun ?_ measurableSet_Ioo)
    intro x hx
    exact (betaMellin_integrand s x hx).symm
  · rw [mellin, ← betaMellin_image,
      integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv betaMellin_injOn]
    simp_rw [smul_eq_mul]
    rw [setIntegral_congr_fun measurableSet_Ioo (betaMellin_integrand s)]
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
      ← Complex.betaIntegral, Complex.betaIntegral_eq_Gamma_mul_div s (2 - s) hs hs']
    norm_num

/-! ### Scaling the reciprocal-square kernel

Scaling the beta integral gives Shintani's integral for `(a+t)⁻²`.
Its full convergence strip is `0<Re(s)<2`; summing over positive integers will
restrict the strip to `0<Re(s)<1`.
-/

/-- Scaling `(1+t)⁻²` by a positive real number gives `(a+t)⁻²`.
This isolates the elementary change in `hasMellin_add_inv_sq`. -/
private lemma add_inv_sq_eq_scaled (a : ℝ) (ha : 0 < a) :
    (fun t : ℝ => ((a : ℂ) + t)⁻¹ ^ 2) =
      fun t : ℝ => (a : ℂ)⁻¹ ^ 2 • (1 + (↑(a⁻¹ * t) : ℂ))⁻¹ ^ 2 := by
  funext t
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  rw [show (a : ℂ) + t = (a : ℂ) * (1 + (↑(a⁻¹ * t) : ℂ)) by
    push_cast; field_simp]
  simp only [mul_inv, mul_pow, smul_eq_mul]

/-- The Mellin transform

```text
∫₀^∞ t^(s-1)/(a+t)² dt = Gamma(s) Gamma(2-s) a^(s-2)
```

is absolutely convergent for `a>0` and `0<Re(s)<2`. This is the elementary integral
at the start of [95, Shintani (1977), proof of Lemma 1 on p. 170], with its full
beta-integral convergence strip. -/
theorem hasMellin_add_inv_sq (a : ℝ) (ha : 0 < a) (s : ℂ)
    (hs : 0 < s.re) (hs2 : s.re < 2) :
    HasMellin (fun t : ℝ => ((a : ℂ) + t)⁻¹ ^ 2) s
      (Complex.Gamma s * Complex.Gamma (2 - s) * (a : ℂ) ^ (s - 2)) := by
  have hbase := hasMellin_one_add_inv_sq s hs hs2
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  rw [add_inv_sq_eq_scaled a ha]
  constructor
  · exact ((MellinConvergent.comp_mul_left (inv_pos.mpr ha)).mpr hbase.1).const_smul _
  · rw [mellin_const_smul,
      mellin_comp_mul_left (fun t : ℝ => (1 + (t : ℂ))⁻¹ ^ 2) s (inv_pos.mpr ha), hbase.2]
    simp only [smul_eq_mul, Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg ha.le,
      Complex.cpow_neg, inv_inv, Complex.cpow_sub _ _ haC, Complex.cpow_ofNat]
    ring

/-! ### Absolute convergence of the integrated series

The norm of a Mellin kernel depends only on `Re(s)`. Evaluating the corresponding
real-parameter beta integral makes the sum of integral norms a shifted `p`-series.
-/

/-- The norm of a reciprocal-square Mellin kernel equals its real-parameter kernel.
This is the pointwise identity used in `integral_norm_mellin_add_inv_sq`. -/
private lemma norm_mellin_add_inv_sq (a : ℝ) (ha : 0 < a) (s : ℂ)
    (t : ℝ) (ht : 0 < t) :
    ‖(t : ℂ) ^ (s - 1) * ((a : ℂ) + t)⁻¹ ^ 2‖ =
      ((t : ℂ) ^ ((s.re : ℂ) - 1) * ((a : ℂ) + t)⁻¹ ^ 2).re := by
  have hat : 0 < a + t := add_pos ha ht
  rw [norm_mul, norm_pow, norm_inv, ← Complex.ofReal_add,
    Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_real,
    Real.norm_of_nonneg hat.le]
  rw [show (s.re : ℂ) - 1 = ((s.re - 1 : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_cpow ht.le, ← Complex.ofReal_inv, ← Complex.ofReal_pow,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  simp only [sub_re, one_re]

/-- The integral of the norm of `t^(s-1)/(a+t)²` is
`Re(Gamma(Re(s)) Gamma(2-Re(s))) a^(Re(s)-2)`.
This evaluates the majorant used in `summable_integral_norm_mellin_inv_sq`. -/
private lemma integral_norm_mellin_add_inv_sq (a : ℝ) (ha : 0 < a) (s : ℂ)
    (hs : 0 < s.re) (hs2 : s.re < 2) :
    (∫ t : ℝ in Ioi 0, ‖(t : ℂ) ^ (s - 1) * ((a : ℂ) + t)⁻¹ ^ 2‖) =
      (Complex.Gamma (s.re : ℂ) * Complex.Gamma (2 - (s.re : ℂ))).re *
        a ^ (s.re - 2) := by
  have hreal := hasMellin_add_inv_sq a ha (s.re : ℂ) (by simpa) (by simpa)
  rw [setIntegral_congr_fun measurableSet_Ioi (norm_mellin_add_inv_sq a ha s)]
  have hint : IntegrableOn (fun t : ℝ =>
      (t : ℂ) ^ ((s.re : ℂ) - 1) * ((a : ℂ) + t)⁻¹ ^ 2) (Ioi 0) := hreal.1
  have hre : (∫ t : ℝ in Ioi 0,
      ((t : ℂ) ^ ((s.re : ℂ) - 1) * ((a : ℂ) + t)⁻¹ ^ 2).re) =
      (∫ t : ℝ in Ioi 0,
        (t : ℂ) ^ ((s.re : ℂ) - 1) * ((a : ℂ) + t)⁻¹ ^ 2).re := by
    simpa only [RCLike.re_to_complex] using integral_re hint
  rw [hre, show (∫ t : ℝ in Ioi 0,
      (t : ℂ) ^ ((s.re : ℂ) - 1) * ((a : ℂ) + t)⁻¹ ^ 2) =
      Complex.Gamma (s.re : ℂ) * Complex.Gamma (2 - (s.re : ℂ)) *
        (a : ℂ) ^ ((s.re : ℂ) - 2) from hreal.2]
  rw [show (s.re : ℂ) - 2 = ((s.re - 2 : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_cpow ha.le, mul_re]
  simp

/-- Summing the integrals of the absolute values of
`t^(s-1)/(n+1+t)²` converges for `0<Re(s)<1`.
This justifies the termwise integral in `hasMellin_trigamma_sub_inv_sq`. -/
private lemma summable_integral_norm_mellin_inv_sq (s : ℂ)
    (hs : 0 < s.re) (hs1 : s.re < 1) :
    Summable (fun n : ℕ => ∫ t : ℝ in Ioi 0,
      ‖(t : ℂ) ^ (s - 1) * (((n + 1 : ℕ) : ℂ) + t)⁻¹ ^ 2‖) := by
  have hp : Summable (fun n : ℕ => (n : ℝ) ^ (s.re - 2)) := by
    rw [Real.summable_nat_rpow]
    linarith
  have hshift : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (s.re - 2)) :=
    (summable_nat_add_iff 1).mpr hp
  apply (hshift.mul_left
    (Complex.Gamma (s.re : ℂ) * Complex.Gamma (2 - (s.re : ℂ))).re).congr
  intro n
  exact (integral_norm_mellin_add_inv_sq ((n + 1 : ℕ) : ℝ)
    (by positivity) s hs (by linarith)).symm

/-- An absolutely summable family of integral norms gives an integrable pointwise sum.
This connects the norm estimate to the convergence assertion in
`hasMellin_trigamma_sub_inv_sq`. -/
private lemma integrable_tsum_of_integral_norm {F : ℕ → ℝ → ℂ} {μ : Measure ℝ}
    (hF : ∀ n, Integrable (F n) μ)
    (hsum : Summable (fun n => ∫ t, ‖F n t‖ ∂μ)) :
    Integrable (fun t => ∑' n, F n t) μ := by
  refine ⟨AEStronglyMeasurable.tsum (fun n => (hF n).aestronglyMeasurable), ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc
    (∫⁻ t, ‖∑' n, F n t‖ₑ ∂μ) ≤ ∫⁻ t, ∑' n, ‖F n t‖ₑ ∂μ :=
      lintegral_mono (fun _ => enorm_tsum_le_tsum_enorm)
    _ = ∑' n, ∫⁻ t, ‖F n t‖ₑ ∂μ :=
      lintegral_tsum (fun n => (hF n).aestronglyMeasurable.enorm)
    _ < ∞ := by
      simp_rw [← ofReal_integral_norm_eq_lintegral_enorm (hF _)]
      exact hsum.tsum_ofReal_lt_top

/-! ### The trigamma transform

Remove the zeroth reciprocal square from the Euler series and integrate the
remaining terms. Their Mellin transforms sum to the Dirichlet series for
`zeta(2-s)`, giving the transform inverted in Shintani's equation (1.3).
-/

/-- The weighted reciprocal-square series sums to
`t^(s-1) (psi'(t)-t⁻²)` on the positive real axis.
This specializes `hasSum_trigamma_series` for `hasMellin_trigamma_sub_inv_sq`. -/
private lemma hasSum_mellin_trigamma_kernel (s : ℂ) (t : ℝ) (ht : 0 < t) :
    HasSum (fun n : ℕ => (t : ℂ) ^ (s - 1) * (((n + 1 : ℕ) : ℂ) + t)⁻¹ ^ 2)
      ((t : ℂ) ^ (s - 1) * (deriv Complex.digamma (t : ℂ) - (t : ℂ)⁻¹ ^ 2)) := by
  have htail := (hasSum_nat_add_iff' 1).mpr
    (hasSum_trigamma_series (t : ℂ) (by simpa))
  simpa only [Finset.sum_range_one, Nat.cast_zero, add_zero, add_comm (t : ℂ), zero_add] using
    htail.mul_left ((t : ℂ) ^ (s - 1))

/-- The integrals of the reciprocal-square Mellin kernels sum to
`zeta(2-s) Gamma(s) Gamma(2-s)` for `0<Re(s)<1`.
This evaluates the termwise integral in `hasMellin_trigamma_sub_inv_sq`. -/
private lemma hasSum_mellin_inv_sq_integrals (s : ℂ) (hs : 0 < s.re) (hs1 : s.re < 1) :
    HasSum (fun n : ℕ => ∫ t : ℝ in Ioi 0,
      (t : ℂ) ^ (s - 1) * (((n + 1 : ℕ) : ℂ) + t)⁻¹ ^ 2)
      (riemannZeta (2 - s) * Complex.Gamma s * Complex.Gamma (2 - s)) := by
  have hs' : 1 < (2 - s).re := by simp only [sub_re, re_ofNat]; linarith
  have hsum : Summable (fun n : ℕ => 1 / (n : ℂ) ^ (2 - s)) :=
    Complex.summable_one_div_nat_cpow.mpr hs'
  have hzeta : HasSum (fun n : ℕ => (((n + 1 : ℕ) : ℂ) ^ (s - 2)))
      (riemannZeta (2 - s)) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs']
    simpa only [show s - 2 = -(2 - s) by ring, Complex.cpow_neg, one_div,
      Nat.cast_add, Nat.cast_one] using ((summable_nat_add_iff 1).mpr hsum).hasSum
  have hterm (n : ℕ) : (∫ t : ℝ in Ioi 0,
      (t : ℂ) ^ (s - 1) * (((n + 1 : ℕ) : ℂ) + t)⁻¹ ^ 2) =
      Complex.Gamma s * Complex.Gamma (2 - s) * (((n + 1 : ℕ) : ℂ) ^ (s - 2)) := by
    simpa only [mellin, smul_eq_mul, Complex.ofReal_natCast] using
      (hasMellin_add_inv_sq ((n + 1 : ℕ) : ℝ) (by positivity) s hs (by linarith)).2
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    (hzeta.mul_left (Complex.Gamma s * Complex.Gamma (2 - s))).congr_fun hterm

/-- The Mellin transform of the trigamma tail is absolutely convergent and equals

```text
∫₀^∞ t^(s-1) (psi'(t)-t⁻²) dt = zeta(2-s) Gamma(s) Gamma(2-s)
```

for `0<Re(s)<1`. This is the forward Mellin-transform identity used in
[95, Shintani (1977), proof of Lemma 1 on p. 170, immediately before equation (1.3)].
The inverse-transform formula and its contour shifts are not part of this statement. -/
theorem hasMellin_trigamma_sub_inv_sq (s : ℂ) (hs : 0 < s.re) (hs1 : s.re < 1) :
    HasMellin (fun t : ℝ => deriv Complex.digamma (t : ℂ) - (t : ℂ)⁻¹ ^ 2) s
      (riemannZeta (2 - s) * Complex.Gamma s * Complex.Gamma (2 - s)) := by
  let F (n : ℕ) (t : ℝ) : ℂ :=
    (t : ℂ) ^ (s - 1) * (((n + 1 : ℕ) : ℂ) + t)⁻¹ ^ 2
  have hint : ∀ n, IntegrableOn (F n) (Ioi 0) := fun n =>
    (hasMellin_add_inv_sq ((n + 1 : ℕ) : ℝ) (by positivity) s hs (by linarith)).1
  have hnorm := summable_integral_norm_mellin_inv_sq s hs hs1
  have heq : EqOn (fun t => ∑' n, F n t)
      (fun t : ℝ => (t : ℂ) ^ (s - 1) *
        (deriv Complex.digamma (t : ℂ) - (t : ℂ)⁻¹ ^ 2)) (Ioi 0) :=
    fun t ht => (hasSum_mellin_trigamma_kernel s t ht).tsum_eq
  constructor
  · exact IntegrableOn.congr_fun (integrable_tsum_of_integral_norm hint hnorm)
      heq measurableSet_Ioi
  · change (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) *
        (deriv Complex.digamma (t : ℂ) - (t : ℂ)⁻¹ ^ 2)) = _
    rw [← setIntegral_congr_fun measurableSet_Ioi heq]
    exact (hasSum_integral_of_summable_integral_norm hint hnorm).unique
      (hasSum_mellin_inv_sq_integrals s hs hs1)

end SIC

end
