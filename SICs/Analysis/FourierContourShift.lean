/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Analysis.StripContour
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Fourier contour shifts for odd kernels

An odd holomorphic kernel with uniform exponential decay on a horizontal strip has a sine
transform represented by a Fourier integral on any higher line in that strip.

This module isolates the elementary Cauchy--Fourier argument used in S. N. M. Ruijsenaars,
*First order analytic difference equations and integrable quantum systems*, J. Math. Phys. 38
(1997), 1069--1146, proof of Proposition III.4, pp. 1096--1097,
[doi:10.1063/1.531809](https://doi.org/10.1063/1.531809), especially equation (3.56). Its first
consumers are the real- and complex-period comparison kernels for the hyperbolic gamma function.

## The argument

Oddness turns the sine transform on the positive half-line into a Fourier integral on the whole
real axis. On the closed strip `0 ≤ Im w ≤ r`, multiplying the kernel by `exp(2iwz)` preserves
holomorphy. The kernel decay `exp(-d|Re w|)` absorbs the Fourier growth
`exp(2|Im z| |Re w|)` when `2|Im z| < d`; it gives absolute convergence on both horizontal
boundaries and makes the two short vertical sides tend to zero. Cauchy's theorem then shifts the
Fourier integral to height `r`. Factoring `exp(2i(u+ir)z)` yields `exp(-2rz)`, and the same
representation gives a uniform norm bound on closed `z`-substrips.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace SIC

/-! ### Elementary exponential integrability

The tail estimate used by every horizontal line is independent of complex analysis.
-/

/-- The exponentially dominated right tail is integrable; used by
`integrable_of_continuous_norm_le_mul_exp_neg_abs`. -/
private lemma integrableOn_Ioi_of_norm_le_mul_exp_neg_abs
    {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} (hf : Continuous f)
    {C d T R : ℝ} (hd : 0 < d) (hR : 0 < R) (hTR : T ≤ R)
    (hbound : ∀ x : ℝ, T ≤ |x| → ‖f x‖ ≤ C * Real.exp (-d * |x|)) :
    IntegrableOn f (Ioi R) := by
  apply Integrable.mono'
    ((integrableOn_exp_mul_Ioi (a := -d) (by linarith) R).const_mul C)
    hf.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hxpos : 0 < x := hR.trans hx
  have hxR : R ≤ |x| := by rw [abs_of_pos hxpos]; exact hx.le
  have hb := hbound x (hTR.trans hxR)
  rw [abs_of_pos hxpos] at hb
  simpa only [neg_mul] using hb

/-- The exponentially dominated left tail is integrable; used by
`integrable_of_continuous_norm_le_mul_exp_neg_abs`. -/
private lemma integrableOn_Iic_of_norm_le_mul_exp_neg_abs
    {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} (hf : Continuous f)
    {C d T R : ℝ} (hd : 0 < d) (hR : 0 < R) (hTR : T ≤ R)
    (hbound : ∀ x : ℝ, T ≤ |x| → ‖f x‖ ≤ C * Real.exp (-d * |x|)) :
    IntegrableOn f (Iic (-R)) := by
  apply Integrable.mono'
    ((integrableOn_exp_mul_Iic (a := d) hd (-R)).const_mul C)
    hf.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
  have hx' : x ≤ -R := hx
  have hxnonpos : x ≤ 0 := hx'.trans (neg_nonpos.mpr hR.le)
  have hxR : R ≤ |x| := by
    rw [abs_of_nonpos hxnonpos]
    simpa using neg_le_neg hx'
  have hb := hbound x (hTR.trans hxR)
  rw [abs_of_nonpos hxnonpos] at hb
  convert hb using 1
  congr 2
  ring

/-- A continuous function on `ℝ` dominated outside a compact interval by
`C exp(-d|x|)`, with `d > 0`, is integrable. -/
theorem integrable_of_continuous_norm_le_mul_exp_neg_abs
    {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} (hf : Continuous f)
    {C d T : ℝ} (hd : 0 < d)
    (hbound : ∀ x : ℝ, T ≤ |x| → ‖f x‖ ≤ C * Real.exp (-d * |x|)) :
    Integrable f := by
  let R := max 1 T
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left 1 T)
  have hTR : T ≤ R := le_max_right 1 T
  have hright := integrableOn_Ioi_of_norm_le_mul_exp_neg_abs
    hf hd hR0 hTR hbound
  have hleft := integrableOn_Iic_of_norm_le_mul_exp_neg_abs
    hf hd hR0 hTR hbound
  have hmid : IntegrableOn f (Icc (-R) R) := hf.integrableOn_Icc
  have hcover : Iic (-R) ∪ Icc (-R) R ∪ Ioi R = univ := by
    ext x
    simp only [mem_union, mem_Iic, mem_Icc, mem_Ioi, mem_univ, iff_true]
    rcases le_total x (-R) with hx | hx
    · exact Or.inl (Or.inl hx)
    · rcases lt_or_ge R x with hx' | hx'
      · exact Or.inr hx'
      · exact Or.inl (Or.inr ⟨hx, hx'⟩)
  simpa [hcover] using (hleft.union hmid).union hright

/-! ### Horizontal Fourier integrability

Continuity and exponential decay on one horizontal line give integrability there. Later, strip
holomorphy and uniform strip decay supply these hypotheses on every horizontal line needed by the
contour shift.
-/

/-- A nonnegative norm bounded by `C exp(t)` forces the coefficient `C` to be nonnegative. -/
private lemma nonneg_coefficient_of_norm_le_mul_exp {E : Type*} [NormedAddCommGroup E]
    {w : E} {C t : ℝ} (h : ‖w‖ ≤ C * Real.exp t) : 0 ≤ C := by
  exact nonneg_of_mul_nonneg_left ((norm_nonneg w).trans h) (Real.exp_pos t)

/-- A kernel differentiable on `0 ≤ Im w ≤ r` restricts continuously to every horizontal
line in that strip. -/
private lemma continuous_horizontal_of_differentiableOn_strip {J : ℂ → ℂ} {r s : ℝ}
    (hJ : DifferentiableOn ℂ J {w : ℂ | 0 ≤ w.im ∧ w.im ≤ r})
    (hs : s ∈ Icc 0 r) :
    Continuous (fun u : ℝ => J (u + s * I)) := by
  have hline : Continuous (fun u : ℝ => (u : ℂ) + (s : ℂ) * I) := by fun_prop
  simpa only [Function.comp_def] using
    hJ.continuousOn.comp_continuous hline (fun u => by
      simpa [Complex.add_im, Complex.mul_im] using hs)

/-- The modulus of the Fourier exponential on a horizontal line. -/
private lemma norm_exp_fourier_horizontal (u s : ℝ) (z : ℂ) :
    ‖Complex.exp (2 * I * ((u : ℂ) + s * I) * z)‖ =
      Real.exp (-2 * s * z.re - 2 * u * z.im) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-- The Fourier exponential on the unshifted real coordinate grows by at most
`exp(2|Im z| |u|)`. -/
private lemma norm_exp_fourier_real_le (u : ℝ) (z : ℂ) :
    ‖Complex.exp (2 * I * (u : ℂ) * z)‖ ≤ Real.exp (2 * |z.im| * |u|) := by
  have hprod : -(u * z.im) ≤ |u| * |z.im| := by
    simpa [abs_mul] using (neg_le_abs (u * z.im))
  rw [show ‖Complex.exp (2 * I * (u : ℂ) * z)‖ = Real.exp (-2 * u * z.im) by
    simpa using norm_exp_fourier_horizontal u 0 z]
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- A continuous exponentially decaying kernel on the line `Im w=s` remains absolutely
integrable after multiplication by the Fourier exponential when `2|Im z| < d`. -/
theorem integrable_fourier_shift_of_exp_decay
    (J : ℂ → ℂ) {C d T s : ℝ}
    (hJ : Continuous (fun u : ℝ => J (u + s * I)))
    (hbound : ∀ x : ℝ, T ≤ |x| →
      ‖J (x + s * I)‖ ≤ C * Real.exp (-d * |x|))
    {z : ℂ} (hz : 2 * |z.im| < d) :
    Integrable (fun u : ℝ => J (u + s * I) * Complex.exp (2 * I * u * z)) := by
  have hC : 0 ≤ C :=
    nonneg_coefficient_of_norm_le_mul_exp (hbound T (le_abs_self T))
  have hcont : Continuous (fun u : ℝ =>
      J (u + s * I) * Complex.exp (2 * I * u * z)) :=
    hJ.mul (by fun_prop)
  refine integrable_of_continuous_norm_le_mul_exp_neg_abs (C := C) (T := T) hcont
    (show 0 < d - 2 * |z.im| by linarith) ?_
  intro u hu
  have hJbound := hbound u hu
  have hexp := norm_exp_fourier_real_le u z
  rw [norm_mul]
  calc
    ‖J (u + s * I)‖ * ‖Complex.exp (2 * I * (u : ℂ) * z)‖ ≤
        C * Real.exp (-d * |u|) * Real.exp (2 * |z.im| * |u|) :=
      mul_le_mul hJbound hexp (norm_nonneg _) (mul_nonneg hC (Real.exp_pos _).le)
    _ = C * Real.exp (-(d - 2 * |z.im|) * |u|) := by
      rw [show -(d - 2 * |z.im|) * |u| =
          -d * |u| + 2 * |z.im| * |u| by ring, Real.exp_add]
      ring

/-- The full Fourier integrand `J(u+is) exp(2i(u+is)z)` is absolutely integrable on every
horizontal line in the strip. -/
private lemma integrable_fourier_horizontal_of_uniform_exp_decay
    (J : ℂ → ℂ) {r C d T : ℝ}
    (hJ : DifferentiableOn ℂ J {w : ℂ | 0 ≤ w.im ∧ w.im ≤ r})
    (hbound : ∀ x : ℝ, T ≤ |x| → ∀ s ∈ Icc 0 r,
      ‖J (x + s * I)‖ ≤ C * Real.exp (-d * |x|))
    {s : ℝ} (hs : s ∈ Icc 0 r) {z : ℂ} (hz : 2 * |z.im| < d) :
    Integrable (fun u : ℝ =>
      J (u + s * I) * Complex.exp (2 * I * (u + s * I) * z)) := by
  have hbase := integrable_fourier_shift_of_exp_decay J
    (continuous_horizontal_of_differentiableOn_strip hJ hs)
    (fun x hx => hbound x hx s hs) hz
  have hexp (u : ℝ) : Complex.exp (2 * I * (u + s * I) * z) =
      Complex.exp (-2 * s * z) * Complex.exp (2 * I * u * z) := by
    rw [← Complex.exp_add]
    congr 1
    ring_nf
    simp
    ring
  apply (hbase.const_mul (Complex.exp (-2 * s * z))).congr
  filter_upwards [] with u
  rw [hexp]
  ring

/-! ### Oddness and the sine transform

Reflection splits the full real-line Fourier integral into the two opposite exponentials on the
positive half-line. Their difference is exactly `2i` times the sine integrand.
-/

/-- Reflection turns a full-line integral into a difference on the positive half-line. -/
private lemma integral_eq_Ioi_sub_of_reflect {F G : ℝ → ℂ}
    (hF : Integrable F) (hG : Integrable G) (hreflect : ∀ u, F (-u) = -G u) :
    (∫ u : ℝ, F u) = ∫ u in Ioi (0 : ℝ), F u - G u := by
  have hleft : ∫ u in Iic (0 : ℝ), F u = -∫ u in Ioi (0 : ℝ), G u := by
    calc
      _ = ∫ u in Ioi (0 : ℝ), F (-u) := by
        simpa only [neg_zero] using (integral_comp_neg_Ioi 0 F).symm
      _ = ∫ u in Ioi (0 : ℝ), -G u :=
        setIntegral_congr_fun measurableSet_Ioi (fun u _ => hreflect u)
      _ = _ := by rw [integral_neg]
  rw [← intervalIntegral.integral_Iic_add_Ioi hF.integrableOn hF.integrableOn,
    hleft, integral_sub hF.integrableOn hG.integrableOn]
  ring

/-- The difference of the opposite Fourier exponentials is `2i` times the sine integrand. -/
private lemma fourier_sub_eq_sin (J : ℂ → ℂ) (u : ℝ) (z : ℂ) :
    J u * Complex.exp (2 * I * u * z) -
      J u * Complex.exp (2 * I * u * (-z)) =
        (2 * I) * (J u * Complex.sin (2 * u * z)) := by
  simp only [Complex.sin]
  ring_nf
  simp
  ring

/-- For an odd kernel, `2i` times the positive-half-line sine transform is its full-line Fourier
transform. -/
private lemma integral_mul_sin_eq_integral_of_odd
    (J : ℂ → ℂ) {C d T : ℝ}
    (hJ : Continuous (fun u : ℝ => J u))
    (hodd : ∀ w : ℂ, J (-w) = -J w)
    (hbound : ∀ x : ℝ, T ≤ |x| → ‖J x‖ ≤ C * Real.exp (-d * |x|))
    {z : ℂ} (hz : 2 * |z.im| < d) :
    2 * I * (∫ u in Ioi (0 : ℝ), J u * Complex.sin (2 * u * z)) =
      ∫ u : ℝ, J u * Complex.exp (2 * I * u * z) := by
  let F (u : ℝ) : ℂ := J u * Complex.exp (2 * I * u * z)
  let G (u : ℝ) : ℂ := J u * Complex.exp (2 * I * u * (-z))
  have hF : Integrable F := by
    simpa [F] using integrable_fourier_shift_of_exp_decay (s := 0) J
      (by simpa using hJ) (fun x hx => by simpa using hbound x hx) hz
  have hzneg : 2 * |(-z).im| < d := by simpa using hz
  have hG : Integrable G := by
    simpa [G] using integrable_fourier_shift_of_exp_decay (s := 0) J
      (by simpa using hJ) (fun x hx => by simpa using hbound x hx) hzneg
  have hreflect (u : ℝ) : F (-u) = -G u := by
    dsimp [F, G]
    push_cast
    rw [hodd]
    rw [show 2 * I * (-(u : ℂ)) * z = 2 * I * (u : ℂ) * (-z) by ring]
    ring
  have hfull := integral_eq_Ioi_sub_of_reflect hF hG hreflect
  rw [show (∫ u : ℝ, J u * Complex.exp (2 * I * u * z)) =
      (∫ u : ℝ, F u) from rfl, hfull]
  rw [show (∫ u in Ioi (0 : ℝ), F u - G u) =
      ∫ u in Ioi (0 : ℝ), (2 * I) * (J u * Complex.sin (2 * u * z)) from
    setIntegral_congr_fun measurableSet_Ioi (fun u _ =>
      show F u - G u = _ from fourier_sub_eq_sin J u z)]
  rw [integral_const_mul]

/-! ### Vanishing vertical sides

On a short vertical side, the Fourier exponential contributes at most
`exp(2r|Re z| + 2|Im z||x|)`. The remaining rate is positive by `2|Im z| < d`.
-/

/-- The Fourier exponential on a vertical side has a uniform bound over `0 ≤ s ≤ r`. -/
private lemma exp_fourier_vertical_le {r x s : ℝ} {z : ℂ} (hs : s ∈ Icc 0 r) :
    Real.exp (-2 * s * z.re - 2 * x * z.im) ≤
      Real.exp (2 * r * |z.re| + 2 * |z.im| * |x|) := by
  have hsr : -(s * z.re) ≤ r * |z.re| := by
    calc
      _ = s * (-z.re) := by ring
      _ ≤ s * |z.re| := mul_le_mul_of_nonneg_left (neg_le_abs z.re) hs.1
      _ ≤ r * |z.re| := mul_le_mul_of_nonneg_right hs.2 (abs_nonneg _)
  have hxr : -(x * z.im) ≤ |x| * |z.im| := by
    simpa [abs_mul] using (neg_le_abs (x * z.im))
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- Kernel decay and Fourier growth combine to the residual rate `d-2|Im z|`. -/
private lemma fourier_vertical_decay_factor (C d r x : ℝ) (z : ℂ) :
    C * Real.exp (-d * |x|) *
        Real.exp (2 * r * |z.re| + 2 * |z.im| * |x|) =
      C * Real.exp (2 * r * |z.re|) *
        Real.exp (-(d - 2 * |z.im|) * |x|) := by
  calc
    _ = C * Real.exp (-d * |x| +
        (2 * r * |z.re| + 2 * |z.im| * |x|)) := by rw [mul_assoc, ← Real.exp_add]
    _ = C * Real.exp (2 * r * |z.re| +
        -(d - 2 * |z.im|) * |x|) := by congr 1; ring_nf
    _ = _ := by rw [Real.exp_add]; ring

/-- Uniform exponential bound on the Fourier integrand along a short vertical side. -/
private lemma norm_fourier_vertical_le
    (J : ℂ → ℂ) {r C d T : ℝ}
    (hbound : ∀ x : ℝ, T ≤ |x| → ∀ s ∈ Icc 0 r,
      ‖J (x + s * I)‖ ≤ C * Real.exp (-d * |x|))
    {z : ℂ} {x s : ℝ} (hx : T ≤ |x|) (hs : s ∈ Icc 0 r) :
    ‖J (x + s * I) * Complex.exp (2 * I * (x + s * I) * z)‖ ≤
      C * Real.exp (2 * r * |z.re|) *
        Real.exp (-(d - 2 * |z.im|) * |x|) := by
  have hJx := hbound x hx s hs
  have hC : 0 ≤ C := nonneg_coefficient_of_norm_le_mul_exp hJx
  have he : Real.exp (-2 * s * z.re - 2 * x * z.im) ≤
      Real.exp (2 * r * |z.re| + 2 * |z.im| * |x|) :=
    exp_fourier_vertical_le hs
  calc
    ‖J (x + s * I) * Complex.exp (2 * I * (x + s * I) * z)‖ =
        ‖J (x + s * I)‖ * Real.exp (-2 * s * z.re - 2 * x * z.im) := by
      rw [norm_mul, norm_exp_fourier_horizontal]
    _ ≤ C * Real.exp (-d * |x|) *
        Real.exp (-2 * s * z.re - 2 * x * z.im) :=
      mul_le_mul_of_nonneg_right hJx (Real.exp_pos _).le
    _ ≤ C * Real.exp (-d * |x|) *
        Real.exp (2 * r * |z.re| + 2 * |z.im| * |x|) :=
      mul_le_mul_of_nonneg_left he (mul_nonneg hC (Real.exp_pos _).le)
    _ = C * Real.exp (2 * r * |z.re|) *
        Real.exp (-(d - 2 * |z.im|) * |x|) :=
      fourier_vertical_decay_factor C d r x z

/-- The Fourier integrals across the two short vertical sides tend to zero at both ends of the
strip. -/
private lemma tendsto_fourier_vertical
    (J : ℂ → ℂ) {r C d T : ℝ} (hr : 0 < r)
    (hbound : ∀ x : ℝ, T ≤ |x| → ∀ s ∈ Icc 0 r,
      ‖J (x + s * I)‖ ≤ C * Real.exp (-d * |x|))
    {z : ℂ} (hz : 2 * |z.im| < d) :
    Tendsto (fun x : ℝ => ∫ s : ℝ in 0..r,
      J (x + s * I) * Complex.exp (2 * I * (x + s * I) * z))
      (cocompact ℝ) (𝓝 0) := by
  have hrate : 0 < d - 2 * |z.im| := by linarith
  let A := C * Real.exp (2 * r * |z.re|)
  have habs : Tendsto (fun x : ℝ => |x|) (cocompact ℝ) atTop := by
    convert (tendsto_norm_cocompact_atTop (E := ℝ)) using 1
  have hh : Tendsto (fun x : ℝ => A * Real.exp (-(d - 2 * |z.im|) * |x|))
      (cocompact ℝ) (𝓝 0) := by
    have hdecay := Real.tendsto_exp_atBot.comp
      (habs.const_mul_atTop_of_neg (by linarith : -(d - 2 * |z.im|) < 0))
    simpa only [Function.comp_apply, mul_zero] using hdecay.const_mul A
  have hfar : ∀ᶠ x : ℝ in cocompact ℝ, T ≤ |x| :=
    habs.eventually (eventually_ge_atTop T)
  apply tendsto_integral_vertical_of_norm_le
    (fun w => J w * Complex.exp (2 * I * w * z)) 0 r
    (fun x => A * Real.exp (-(d - 2 * |z.im|) * |x|)) hh
  filter_upwards [hfar] with x hx
  intro s hs
  have hs' : s ∈ Icc 0 r := by simpa only [uIcc_of_le hr.le] using hs
  exact norm_fourier_vertical_le J hbound hx hs'

/-! ### The odd-kernel Fourier contour shift

Cauchy's theorem moves the full Fourier integral to height `r`; the vertical part of the
exponential then factors as `exp(-2rz)`.
-/

/-- The full Fourier integral moves from the real axis to height `r`. -/
private lemma fourier_integral_shift_of_uniform_exp_decay
    (J : ℂ → ℂ) {r C d T : ℝ} (hr : 0 < r)
    (hJ : DifferentiableOn ℂ J {w : ℂ | 0 ≤ w.im ∧ w.im ≤ r})
    (hbound : ∀ x : ℝ, T ≤ |x| → ∀ s ∈ Icc 0 r,
      ‖J (x + s * I)‖ ≤ C * Real.exp (-d * |x|))
    {z : ℂ} (hz : 2 * |z.im| < d) :
    (∫ u : ℝ, J u * Complex.exp (2 * I * u * z)) =
      ∫ u : ℝ, J (u + r * I) * Complex.exp (2 * I * (u + r * I) * z) := by
  have hs₀ : (0 : ℝ) ∈ Icc 0 r := ⟨le_rfl, hr.le⟩
  have hsr : r ∈ Icc 0 r := ⟨hr.le, le_rfl⟩
  have hg : DifferentiableOn ℂ (fun w => J w * Complex.exp (2 * I * w * z))
      {w : ℂ | 0 ≤ w.im ∧ w.im ≤ r} := hJ.mul (by fun_prop)
  have h₀ : Integrable (fun u : ℝ =>
      J (u + (0 : ℝ) * I) * Complex.exp (2 * I * (u + (0 : ℝ) * I) * z)) :=
    integrable_fourier_horizontal_of_uniform_exp_decay J hJ hbound hs₀ hz
  have hR : Integrable (fun u : ℝ =>
      J (u + r * I) * Complex.exp (2 * I * (u + r * I) * z)) :=
    integrable_fourier_horizontal_of_uniform_exp_decay J hJ hbound hsr hz
  have hshift := integral_horizontal_eq_of_integrable
    (fun w => J w * Complex.exp (2 * I * w * z)) 0 r hr.le hg
    (tendsto_fourier_vertical J hr hbound hz) h₀ hR
  simpa using hshift

/-- Let `J` be odd and holomorphic on `0 ≤ Im w ≤ r`, with the uniform tail bound
`‖J(x+is)‖ ≤ C exp(-d|x|)` there. If `2|Im z| < d`, then

`2i ∫₀^∞ J(u) sin(2uz) du = exp(-2rz) ∫_ℝ J(u+ir) exp(2iuz) du`.

This is the general odd-kernel form of the Cauchy--Fourier shift used in Ruijsenaars (1997),
equation (3.56). -/
theorem integral_mul_sin_eq_exp_mul_integral_of_odd
    (J : ℂ → ℂ) {r C d T : ℝ} (hr : 0 < r)
    (hJ : DifferentiableOn ℂ J {w : ℂ | 0 ≤ w.im ∧ w.im ≤ r})
    (hodd : ∀ w : ℂ, J (-w) = -J w)
    (hbound : ∀ x : ℝ, T ≤ |x| → ∀ s ∈ Icc 0 r,
      ‖J (x + s * I)‖ ≤ C * Real.exp (-d * |x|))
    {z : ℂ} (hz : 2 * |z.im| < d) :
    2 * I * (∫ u in Ioi (0 : ℝ), J u * Complex.sin (2 * u * z)) =
      Complex.exp (-2 * r * z) *
        ∫ u : ℝ, J (u + r * I) * Complex.exp (2 * I * u * z) := by
  have hs₀ : (0 : ℝ) ∈ Icc 0 r := ⟨le_rfl, hr.le⟩
  have hJ₀ : Continuous (fun u : ℝ => J u) := by
    simpa using continuous_horizontal_of_differentiableOn_strip hJ hs₀
  have hexp (u : ℝ) : Complex.exp (2 * I * (u + r * I) * z) =
      Complex.exp (-2 * r * z) * Complex.exp (2 * I * u * z) := by
    rw [← Complex.exp_add]
    congr 1
    ring_nf
    simp
    ring
  calc
    2 * I * (∫ u in Ioi (0 : ℝ), J u * Complex.sin (2 * u * z)) =
        ∫ u : ℝ, J u * Complex.exp (2 * I * u * z) :=
      integral_mul_sin_eq_integral_of_odd J hJ₀ hodd
        (fun x hx => by simpa using hbound x hx 0 hs₀) hz
    _ = ∫ u : ℝ, J (u + r * I) * Complex.exp (2 * I * (u + r * I) * z) :=
      fourier_integral_shift_of_uniform_exp_decay J hr hJ hbound hz
    _ = Complex.exp (-2 * r * z) *
        ∫ u : ℝ, J (u + r * I) * Complex.exp (2 * I * u * z) := by
      simp_rw [hexp]
      rw [← integral_const_mul]
      congr 1
      funext u
      ring

/-! ### Uniform norm bound from a shifted-line majorant

Once the contour identity is known, only an integrable majorant on the shifted line is needed for
the closed-substrip estimate.
-/

/-- A weighted majorant for the shifted kernel also majorizes its Fourier integrand uniformly
when `|Im z| ≤ c`. -/
private lemma norm_shifted_fourier_integrand_le
    (J : ℂ → ℂ) (r c : ℝ) {W : ℝ → ℝ}
    (hW : ∀ u : ℝ, ‖J (u + r * I)‖ * Real.exp (2 * c * |u|) ≤ W u)
    {z : ℂ} (hz : |z.im| ≤ c) (u : ℝ) :
    ‖J (u + r * I) * Complex.exp (2 * I * u * z)‖ ≤ W u := by
  have he : Real.exp (2 * |z.im| * |u|) ≤ Real.exp (2 * c * |u|) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hz (by norm_num)) (abs_nonneg u))
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left ((norm_exp_fourier_real_le u z).trans he)
    (norm_nonneg _)).trans (hW u)

/-- Let `W` be an integrable majorant with
`‖J(u+ir)‖ exp(2c|u|) ≤ W(u)`. If the odd-kernel contour identity holds at `z`, then its sine
transform is at most `(1/2) ∫ W` times `exp(-2r Re z)`. The constant depends only on the supplied
majorant, so the estimate remains uniform when `J` varies under one common `W`. -/
theorem norm_integral_mul_sin_le_of_integrable_majorant
    (J : ℂ → ℂ) (r c : ℝ) (W : ℝ → ℝ) (hWint : Integrable W)
    (hW : ∀ u : ℝ, ‖J (u + r * I)‖ * Real.exp (2 * c * |u|) ≤ W u)
    {z : ℂ} (hz : |z.im| ≤ c)
    (hidentity : 2 * I * (∫ u in Ioi (0 : ℝ), J u * Complex.sin (2 * u * z)) =
      Complex.exp (-2 * r * z) *
        ∫ u : ℝ, J (u + r * I) * Complex.exp (2 * I * u * z)) :
      ‖∫ u in Ioi (0 : ℝ), J u * Complex.sin (2 * u * z)‖ ≤
        (∫ u : ℝ, W u) / 2 * Real.exp (-2 * r * z.re) := by
  have hInt : ‖∫ u : ℝ, J (u + r * I) * Complex.exp (2 * I * u * z)‖ ≤
      ∫ u : ℝ, W u :=
    norm_integral_le_of_norm_le hWint
      (Eventually.of_forall (norm_shifted_fourier_integrand_le J r c hW hz))
  have hnorm : 2 * ‖∫ u in Ioi (0 : ℝ), J u * Complex.sin (2 * u * z)‖ =
      Real.exp (-2 * r * z.re) *
        ‖∫ u : ℝ, J (u + r * I) * Complex.exp (2 * I * u * z)‖ := by
    have h := congrArg norm hidentity
    simpa [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.mul_im] using h
  calc
    ‖∫ u in Ioi (0 : ℝ), J u * Complex.sin (2 * u * z)‖ =
        (Real.exp (-2 * r * z.re) *
          ‖∫ u : ℝ, J (u + r * I) * Complex.exp (2 * I * u * z)‖) / 2 := by
      linarith [hnorm]
    _ ≤ (Real.exp (-2 * r * z.re) * ∫ u : ℝ, W u) / 2 := by
      gcongr
    _ = (∫ u : ℝ, W u) / 2 * Real.exp (-2 * r * z.re) := by ring

end SIC
