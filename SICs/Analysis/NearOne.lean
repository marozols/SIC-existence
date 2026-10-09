/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Elementary norm and exponential estimates

Elementary estimates for quantities close to one and for parameterized complex exponentials.

These estimates control products and inverses through their distance from one. They also include
uniform exponential decay along vertical lines and the elementary threshold used to turn a
decaying error bound into a near-one bound.

## The argument

The product identity `zw - 1 = (z - 1)(w - 1) + (z - 1) + (w - 1)` and the triangle inequality
give the product estimate without requiring the norm of one to equal one. If `w` is within `1/2`
of one, reverse triangle gives `‖w‖ ≥ 1/2`; writing `w⁻¹ - 1 = (1 - w) / w` then gives the inverse
estimate. Finally, the maximum of `t exp(-t)` bounds an exponential tail after its linear
coefficient has been absorbed into `t`.

For a continuously parameterized exponential `exp(A(q)t+B(q))`, a negative limiting real part
of `A` remains uniformly negative near the limiting parameter, while the real part of `B` stays
uniformly bounded above. Since `‖exp z‖ = exp(Re z)`, this gives one positive exponential bound
for all nearby parameters. Multiplication by `i` turns the sign of `Im A` into the required sign
of the real slope on a vertical line. These bounds supply the elementary phase estimates in
[RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`].
-/

open Complex Filter Topology

namespace SIC

/-! ### Norm estimates -/

/-- The modulus of $e(v)=\exp(2\pi i v)$ is $\exp(-2\pi\operatorname{Im}v)$. -/
theorem norm_exp_two_pi_I_mul (v : ℂ) :
    ‖Complex.exp (2 * Real.pi * I * v)‖ = Real.exp (-2 * Real.pi * v.im) := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re]

/-- The error of a product is bounded in terms of the errors of its two factors:
`‖zw - 1‖ ≤ (1 + ‖z - 1‖) ‖w - 1‖ + ‖z - 1‖`. -/
lemma norm_mul_sub_one_le {R : Type*} [SeminormedRing R] (z w : R) :
    ‖z * w - 1‖ ≤ (1 + ‖z - 1‖) * ‖w - 1‖ + ‖z - 1‖ := by
  calc
    ‖z * w - 1‖ = ‖(z - 1) * (w - 1) + (z - 1) + (w - 1)‖ := by
      congr 1
      noncomm_ring
    _ ≤ ‖(z - 1) * (w - 1)‖ + ‖z - 1‖ + ‖w - 1‖ := norm_add₃_le
    _ ≤ ‖z - 1‖ * ‖w - 1‖ + ‖z - 1‖ + ‖w - 1‖ := by
      gcongr
      exact norm_mul_le _ _
    _ = (1 + ‖z - 1‖) * ‖w - 1‖ + ‖z - 1‖ := by ring

/-- Two factors exponentially close to one have a product exponentially close to one at the
minimum of their rates. -/
lemma norm_mul_sub_one_le_of_exponential_bounds {R : Type*} [SeminormedRing R]
    (u v : R) {A B p q y : ℝ} (hp : 0 ≤ p) (hy : 0 ≤ y)
    (hu : ‖u - 1‖ ≤ A * Real.exp (-p * y))
    (hv : ‖v - 1‖ ≤ B * Real.exp (-q * y)) :
    ‖u * v - 1‖ ≤ ((1 + A) * B + A) * Real.exp (-(min p q) * y) := by
  have hA : 0 ≤ A :=
    nonneg_of_mul_nonneg_left ((norm_nonneg (u - 1)).trans hu) (Real.exp_pos _)
  have hB : 0 ≤ B :=
    nonneg_of_mul_nonneg_left ((norm_nonneg (v - 1)).trans hv) (Real.exp_pos _)
  have hep : Real.exp (-p * y) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have huA : ‖u - 1‖ ≤ A := hu.trans (by simpa using mul_le_mul_of_nonneg_left hep hA)
  have hpmin : Real.exp (-p * y) ≤ Real.exp (-(min p q) * y) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_left p q])
  have hqmin : Real.exp (-q * y) ≤ Real.exp (-(min p q) * y) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_right p q])
  calc
    ‖u * v - 1‖ ≤ (1 + ‖u - 1‖) * ‖v - 1‖ + ‖u - 1‖ := norm_mul_sub_one_le u v
    _ ≤ (1 + A) * (B * Real.exp (-q * y)) + A * Real.exp (-p * y) := by gcongr
    _ ≤ (1 + A) * (B * Real.exp (-(min p q) * y)) +
        A * Real.exp (-(min p q) * y) := by gcongr
    _ = ((1 + A) * B + A) * Real.exp (-(min p q) * y) := by ring

/-- An element within `1/2` of one is nonzero, and inversion increases its distance from one by
at most a factor of two. -/
lemma norm_inv_sub_one_le_two_mul_norm_sub_one {R : Type*} [NormedDivisionRing R] (w : R)
    (hw : ‖w - 1‖ ≤ 1 / 2) :
    w ≠ 0 ∧ ‖w⁻¹ - 1‖ ≤ 2 * ‖w - 1‖ := by
  have hrev := norm_sub_norm_le (1 : R) w
  rw [norm_one, norm_sub_rev] at hrev
  have hnorm : 1 / 2 ≤ ‖w‖ := by linarith
  have hwne : w ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hnorm)
  have hinv : w⁻¹ - 1 = (1 - w) / w := by
    rw [div_eq_mul_inv, sub_mul, one_mul, mul_inv_cancel₀ hwne]
  refine ⟨hwne, ?_⟩
  rw [hinv, norm_div, norm_sub_rev]
  calc
    ‖w - 1‖ / ‖w‖ ≤ ‖w - 1‖ / (1 / 2) :=
      div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) hnorm
    _ = 2 * ‖w - 1‖ := by ring

/-- A quotient of two factors within `1/2` of one has norm at most three. -/
lemma norm_div_le_three_of_norm_sub_one_le_half
    {R : Type*} [NormedDivisionRing R] (u v : R)
    (hu : ‖u - 1‖ ≤ 1 / 2) (hv : ‖v - 1‖ ≤ 1 / 2) :
    ‖u / v‖ ≤ 3 := by
  obtain ⟨_, hinv⟩ := norm_inv_sub_one_le_two_mul_norm_sub_one v hv
  have huNorm : ‖u‖ ≤ 3 / 2 := by
    have h := norm_sub_norm_le u 1
    rw [norm_one] at h
    linarith
  have hinvNorm : ‖v⁻¹‖ ≤ 2 := by
    have h := norm_sub_norm_le v⁻¹ 1
    rw [norm_one] at h
    nlinarith
  rw [div_eq_mul_inv]
  calc
    ‖u * v⁻¹‖ ≤ ‖u‖ * ‖v⁻¹‖ := norm_mul_le _ _
    _ ≤ (3 / 2) * 2 := mul_le_mul huNorm hinvNorm (norm_nonneg _) (by norm_num)
    _ = 3 := by norm_num

/-! ### Uniform affine exponential decay

A negative real slope yields decay on the nonnegative real ray. Multiplication by `i` specializes
this to a vertical line, with positive imaginary coefficients decaying upward and negative
imaginary coefficients decaying downward.
-/

/-- A complex exponential with a continuously parameterized negative real slope admits one
uniform exponential bound on the nonnegative ray. -/
theorem exists_norm_exp_affine_ray_le
    {q₀ : ℂ} {A B : ℂ → ℂ} (hA : ContinuousAt A q₀) (hB : ContinuousAt B q₀)
    (hRe : (A q₀).re < 0) :
    ∃ ε C κ : ℝ, 0 < ε ∧ 0 < C ∧ 0 < κ ∧
      ∀ q : ℂ, ‖q - q₀‖ ≤ ε → ∀ t : ℝ, 0 ≤ t →
        ‖Complex.exp (A q * (t : ℂ) + B q)‖ ≤ C * Real.exp (-κ * t) := by
  let κ := -(A q₀).re / 2
  let M := (B q₀).re + 1
  let C := Real.exp M
  have hκ : 0 < κ := by dsimp [κ]; linarith
  have hAre : ContinuousAt (fun q => (A q).re) q₀ :=
    by simpa [Function.comp_def] using Complex.continuous_re.continuousAt.comp hA
  have hBre : ContinuousAt (fun q => (B q).re) q₀ :=
    by simpa [Function.comp_def] using Complex.continuous_re.continuousAt.comp hB
  have hAnear : {q : ℂ | (A q).re < -κ} ∈ 𝓝 q₀ :=
    hAre (Iio_mem_nhds (by dsimp [κ]; linarith))
  have hBnear : {q : ℂ | (B q).re < M} ∈ 𝓝 q₀ :=
    hBre (Iio_mem_nhds (by dsimp [M]; linarith))
  obtain ⟨ε, hε, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (inter_mem hAnear hBnear)
  refine ⟨ε, C, κ, hε, Real.exp_pos M, hκ, fun q hq t ht => ?_⟩
  have hq' := hsub (show q ∈ Metric.closedBall q₀ ε by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hq)
  have hAq : (A q).re < -κ := hq'.1
  have hBq : (B q).re < M := hq'.2
  rw [Complex.norm_exp]
  calc
    Real.exp (A q * (t : ℂ) + B q).re ≤ Real.exp (M - κ * t) := by
      apply Real.exp_le_exp.mpr
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero]
      nlinarith [hAq.le, hBq.le]
    _ = C * Real.exp (-κ * t) := by
      rw [show M - κ * t = M + -κ * t by ring, Real.exp_add]

/-- A vertical affine exponential whose limiting coefficient has positive imaginary part decays
uniformly in nearby parameters as height tends to positive infinity. -/
theorem exists_norm_exp_affine_vertical_le
    {q₀ : ℂ} {A B : ℂ → ℂ} (hA : ContinuousAt A q₀) (hB : ContinuousAt B q₀)
    (hIm : 0 < (A q₀).im) (x : ℝ) :
    ∃ ε C κ : ℝ, 0 < ε ∧ 0 < C ∧ 0 < κ ∧
      ∀ q : ℂ, ‖q - q₀‖ ≤ ε → ∀ t : ℝ, 0 ≤ t →
        ‖Complex.exp (A q * ((x : ℂ) + t * I) + B q)‖ ≤ C * Real.exp (-κ * t) := by
  obtain ⟨ε, C, κ, hε, hC, hκ, hbound⟩ :=
    exists_norm_exp_affine_ray_le
      (A := fun q => A q * I) (B := fun q => A q * (x : ℂ) + B q)
      (hA.mul continuousAt_const) ((hA.mul continuousAt_const).add hB)
      (by simpa [Complex.mul_I_re] using neg_lt_zero.mpr hIm)
  refine ⟨ε, C, κ, hε, hC, hκ, fun q hq t ht => ?_⟩
  have heq : (A q * I) * (t : ℂ) + (A q * (x : ℂ) + B q) =
      A q * ((x : ℂ) + t * I) + B q := by
    ring
  simpa only [heq] using hbound q hq t ht

/-- A vertical affine exponential whose limiting coefficient has negative imaginary part decays
uniformly in nearby parameters as height tends to negative infinity. -/
theorem exists_norm_exp_affine_vertical_le_of_im_neg
    {q₀ : ℂ} {A B : ℂ → ℂ} (hA : ContinuousAt A q₀) (hB : ContinuousAt B q₀)
    (hIm : (A q₀).im < 0) (x : ℝ) :
    ∃ ε C κ : ℝ, 0 < ε ∧ 0 < C ∧ 0 < κ ∧
      ∀ q : ℂ, ‖q - q₀‖ ≤ ε → ∀ t : ℝ, t ≤ 0 →
        ‖Complex.exp (A q * ((x : ℂ) + t * I) + B q)‖ ≤ C * Real.exp (κ * t) := by
  obtain ⟨ε, C, κ, hε, hC, hκ, hbound⟩ :=
    exists_norm_exp_affine_ray_le
      (A := fun q => -(A q * I)) (B := fun q => A q * (x : ℂ) + B q)
      (hA.mul continuousAt_const).neg ((hA.mul continuousAt_const).add hB)
      (by simpa [Complex.mul_I_re] using hIm)
  refine ⟨ε, C, κ, hε, hC, hκ, fun q hq t ht => ?_⟩
  have hb := hbound q hq (-t) (neg_nonneg.mpr ht)
  have harg : -(A q * I) * ((-t : ℝ) : ℂ) + (A q * (x : ℂ) + B q) =
      A q * ((x : ℂ) + t * I) + B q := by
    push_cast
    ring
  have hexp : -κ * -t = κ * t := by ring
  rw [harg, hexp] at hb
  exact hb

/-! ### Exponential thresholds -/

/-- If `2K ≤ κy`, then `2K exp(-κy) ≤ 1`. -/
lemma two_mul_mul_exp_neg_le_one (κ K y : ℝ) (hy : 2 * K ≤ κ * y) :
    2 * K * Real.exp (-κ * y) ≤ 1 := by
  calc
    2 * K * Real.exp (-κ * y) ≤ (κ * y) * Real.exp (-(κ * y)) := by
      rw [show -κ * y = -(κ * y) by ring]
      gcongr
    _ ≤ Real.exp (-1) := Real.mul_exp_neg_le_exp_neg_one (κ * y)
    _ ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)

/-- Two exponentially near-one factors have quotient norm at most three once both errors have
crossed `1/2`. -/
lemma norm_div_le_three_of_exponential_bounds
    {R : Type*} [NormedDivisionRing R] (u v : R) {C₁ κ₁ C₂ κ₂ s : ℝ}
    (hC₁ : 2 * C₁ ≤ κ₁ * s) (hC₂ : 2 * C₂ ≤ κ₂ * s)
    (hu : ‖u - 1‖ ≤ C₁ * Real.exp (-κ₁ * s))
    (hv : ‖v - 1‖ ≤ C₂ * Real.exp (-κ₂ * s)) :
    ‖u / v‖ ≤ 3 := by
  apply norm_div_le_three_of_norm_sub_one_le_half u v
  · exact hu.trans (by nlinarith [two_mul_mul_exp_neg_le_one κ₁ C₁ s hC₁])
  · exact hv.trans (by nlinarith [two_mul_mul_exp_neg_le_one κ₂ C₂ s hC₂])

/-- The ratio of two first-order exponential zeros tends to the ratio of their slopes. -/
theorem tendsto_one_sub_exp_mul_div (a b : ℂ) (hb : b ≠ 0) :
    Tendsto (fun w : ℂ => (1 - Complex.exp (a * w)) / (1 - Complex.exp (b * w)))
      (𝓝[≠] 0) (𝓝 (a / b)) := by
  have hder (c : ℂ) : HasDerivAt (fun w : ℂ => 1 - Complex.exp (c * w)) (-c) 0 := by
    convert ((Complex.hasDerivAt_exp (c * 0)).comp 0
      ((hasDerivAt_id (0 : ℂ)).const_mul c)).const_sub 1 using 1 <;> simp
  have hslope (c : ℂ) : Tendsto (fun w : ℂ => (1 - Complex.exp (c * w)) / w)
      (𝓝[≠] 0) (𝓝 (-c)) := by
    simpa [div_eq_mul_inv, mul_comm] using (hder c).tendsto_slope_zero
  have hlim := (hslope a).div (hslope b) (neg_ne_zero.mpr hb)
  have heq : (fun w : ℂ => (1 - Complex.exp (a * w)) / w /
      ((1 - Complex.exp (b * w)) / w)) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun w : ℂ => (1 - Complex.exp (a * w)) / (1 - Complex.exp (b * w))) := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hwn : w ≠ 0 := by simpa using hw
    simp [div_eq_mul_inv, mul_inv_rev, hwn, mul_assoc, mul_left_comm, mul_comm]
  convert hlim.congr' heq using 1
  · ring_nf

/-! ### Exponential and quotient bounds for a dominant term -/

/-- The faster of two exponential tails is at most half the slower tail above an explicit height. -/
lemma exp_neg_two_pi_le_half_exp_div (r t : ℝ) (hr : 1 < r)
    (ht : Real.log 2 / (2 * Real.pi * (r - 1) / r) ≤ t) :
    Real.exp (-2 * Real.pi * t) ≤ Real.exp (-2 * Real.pi * t / r) / 2 := by
  let δ := 2 * Real.pi * (r - 1) / r
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hδ : 0 < δ := div_pos (mul_pos (by positivity) (sub_pos.mpr hr)) hr0
  have hlog : Real.log 2 ≤ δ * t := by
    simpa [mul_comm] using (div_le_iff₀ hδ).mp ht
  have heq : -2 * Real.pi * t = -2 * Real.pi * t / r - δ * t := by
    dsimp [δ]
    field_simp
    ring_nf
  calc
    Real.exp (-2 * Real.pi * t) = Real.exp (-2 * Real.pi * t / r - δ * t) :=
      congrArg Real.exp heq
    _ ≤ Real.exp (-2 * Real.pi * t / r - Real.log 2) :=
      (Real.exp_le_exp).mpr (by linarith)
    _ = Real.exp (-2 * Real.pi * t / r) / 2 := by
      rw [Real.exp_sub, Real.exp_log (by norm_num)]


/-- The slower of two exponential tails is at most half the faster tail below an explicit height. -/
lemma exp_div_le_half_exp_neg_two_pi (r t : ℝ) (hr : 1 < r)
    (ht : t ≤ -(Real.log 2 / (2 * Real.pi * (r - 1) / r))) :
    Real.exp (-2 * Real.pi * t / r) ≤ Real.exp (-2 * Real.pi * t) / 2 := by
  let δ := 2 * Real.pi * (r - 1) / r
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hδ : 0 < δ := div_pos (mul_pos (by positivity) (sub_pos.mpr hr)) hr0
  have hbound : Real.log 2 / δ ≤ -t := by
    dsimp [δ] at ht ⊢
    linarith
  have hlog : Real.log 2 ≤ δ * (-t) := by
    simpa [mul_comm] using (div_le_iff₀ hδ).mp hbound
  have heq : -2 * Real.pi * t / r = -2 * Real.pi * t - δ * (-t) := by
    dsimp [δ]
    field_simp
    ring_nf
  calc
    Real.exp (-2 * Real.pi * t / r) = Real.exp (-2 * Real.pi * t - δ * (-t)) :=
      congrArg Real.exp heq
    _ ≤ Real.exp (-2 * Real.pi * t - Real.log 2) :=
      (Real.exp_le_exp).mpr (by linarith)
    _ = Real.exp (-2 * Real.pi * t) / 2 := by
      rw [Real.exp_sub, Real.exp_log (by norm_num)]


/-- Bounds a quotient when its first denominator term dominates. -/
lemma norm_one_sub_div_le_four_div_of_first_dominates (a b : ℂ) (ha : 0 < ‖a‖)
    (hb : ‖b‖ ≤ 1) (hba : ‖b‖ ≤ ‖a‖ / 2) :
    ‖(1 - b) / (a - b)‖ ≤ 4 / ‖a‖ := by
  have hden : ‖a‖ / 2 ≤ ‖a - b‖ := by
    have h := norm_sub_norm_le a b
    linarith
  have hden0 : 0 < ‖a - b‖ := lt_of_lt_of_le (by positivity) hden
  have hnum : ‖1 - b‖ ≤ 2 := by
    have h := norm_sub_le (1 : ℂ) b
    norm_num at h
    linarith
  rw [norm_div]
  apply (div_le_iff₀ hden0).mpr
  calc
    ‖1 - b‖ ≤ 2 := hnum
    _ = (4 / ‖a‖) * (‖a‖ / 2) := by field_simp; ring_nf
    _ ≤ (4 / ‖a‖) * ‖a - b‖ := by gcongr


/-- Bounds a quotient when its second denominator term dominates. -/
lemma norm_one_sub_div_le_four_of_second_dominates (a b : ℂ) (hb : 1 ≤ ‖b‖)
    (hab : ‖a‖ ≤ ‖b‖ / 2) :
    ‖(1 - b) / (a - b)‖ ≤ 4 := by
  have hden : ‖b‖ / 2 ≤ ‖a - b‖ := by
    have h := norm_sub_norm_le b a
    rw [norm_sub_rev] at h
    linarith
  have hden0 : 0 < ‖a - b‖ := lt_of_lt_of_le (by positivity) hden
  have hnum : ‖1 - b‖ ≤ 2 * ‖b‖ := by
    have h := norm_sub_le (1 : ℂ) b
    simp only [norm_one] at h
    linarith
  rw [norm_div]
  apply (div_le_iff₀ hden0).mpr
  calc
    ‖1 - b‖ ≤ 2 * ‖b‖ := hnum
    _ = 4 * (‖b‖ / 2) := by ring_nf
    _ ≤ 4 * ‖a - b‖ := by gcongr


end SIC
