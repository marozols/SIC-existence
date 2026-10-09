/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.Faddeev.Divisor
import SICs.SpecialFunctions.HyperbolicGamma.ComplexPeriodAsymptotics
import SICs.SpecialFunctions.QPochhammer.Bounds

/-!
# Complex-period asymptotics of the Faddeev generator

Uniform exponential upper- and normalized lower-sector bounds for the Faddeev generator near
positive real periods, including continuous affine families.

The exact normalization combines the double-sine integral representation of [AFK25,
equation (8.7), `eq:dsintrep`] with the generator of [RW26, Radchenko--Wheeler (2026),
Section 2.1]. The estimate is a project boundary-passage extension of the fixed-real-period
asymptotics in [RW26, Radchenko--Wheeler (2026), Lemma 1, `lem:asymp`]. It follows the
comparison proof of S. N. M.
Ruijsenaars, *First order analytic difference equations and integrable quantum systems*,
J. Math. Phys. 38 (1997), Proposition III.4,
[doi:10.1063/1.531809](https://doi.org/10.1063/1.531809), through
`SICs.SpecialFunctions.HyperbolicGamma.ComplexPeriodAsymptotics`.

## The argument

For `w = -i(z + (1-τ)/2)`, the source-chamber integral formula for the double sine gives

```text
Φ(z;τ) = exp(i R(w,τ)),
R(w,τ) = (i/2)L((τ+1)/2+iw,τ) + πw²/(2τ) + (π/24)(τ+τ⁻¹).
```

If `b₁ ≤ Re z ≤ b₂` lies strictly inside `(-1,τ₀)`, then `|Im w|` stays in one closed
substrip when `τ` is close to `τ₀`, while `Re w = Im z - Im τ/2`. The uniform logarithmic
estimate therefore bounds `R` by `D exp(-κ Im z)`. Finally,
`‖exp(iR)-1‖ ≤ ‖R‖ exp(‖R‖)` converts this into the claimed generator estimate.

For an upper-sector argument, subtracting `⌊Re z-a⌋` puts it in a fixed unit strip. The complex
integer-shift identity expresses the original generator as the strip generator times an inverse
finite $q$-symbol. Uniform lower bounds for the shift phases make that finite factor exponentially
close to one. A complex affine map whose slope approaches a positive real number and whose
intercept stays bounded carries one sufficiently high upper sector into another, so the same
estimate applies uniformly to continuous coefficient families.

For a lower-sector argument, reflection sends `z` to `-z+τ-1` in an upper sector and gives the
normalized generator as the inverse reflected generator. Stable inversion of a quantity within
one half of one then preserves exponential decay. The reflection step uses the actual numerator
and denominator zero-free cones; excluding the whole period lattice would impose an unnecessarily
strong restriction for complex periods. Applying the same positive-real-slope affine geometry to
`-z` transports the normalized lower bound uniformly through continuous affine families.
-/

noncomputable section

open Complex Real Set Filter

namespace SIC

/-! ### Complex-period normalization -/

/-- On the chamber `Re τ > 0` and `-1 < Re z < Re τ`, the Faddeev generator is the
exponential of the normalized complex double-sine logarithmic remainder. This bridges
`shintaniDoubleSineGamma_eq_integral_of_re_pos` with the normalization in
[RW26, Radchenko--Wheeler (2026), Section 2.1]. -/
theorem faddeevS_eq_exp_doubleSineComplexLogRemainder (z τ : ℂ) (hτ : 0 < τ.re)
    (hz : -1 < z.re) (hzτ : z.re < τ.re) :
    let w := -I * (z + (1 - τ) / 2)
    faddeevS z τ = Complex.exp (I * doubleSineComplexLogRemainder w τ) := by
  dsimp only
  let w := -I * (z + (1 - τ) / 2)
  have hlow : 0 < (z + 1).re := by simp; linarith
  have hupper : (z + 1).re < τ.re + 1 := by simp; linarith
  have harg : (τ + 1) / 2 + I * w = z + 1 := by
    dsimp [w]
    rw [← mul_assoc, mul_neg, I_mul_I, neg_neg, one_mul]
    ring_nf
  rw [faddeevS,
    shintaniDoubleSineGamma_eq_integral_of_re_pos
      (z + 1) τ hτ hlow hupper,
    doubleSineComplexIntegral, doubleSineComplexLogRemainder, ← Complex.exp_add, harg]
  congr 1
  unfold faddeevSExpArg
  have hτne : τ ≠ 0 := fun h => by simpa [h] using hτ.ne'
  have hI : (I : ℂ) ^ 2 = -1 := I_sq
  have hI3 : (I : ℂ) ^ 3 = -I := by rw [pow_succ, hI]; ring_nf
  field_simp
  ring_nf
  rw [hI3, hI]
  ring_nf

/-! ### Uniform closed-strip geometry -/

/-- A closed interval strictly inside `(-1,τ₀)` determines a slightly larger closed
hyperbolic-gamma substrip. -/
private lemma exists_faddeevS_logarithmic_substrip {τ₀ b₁ b₂ : ℝ}
    (hb₁ : -1 < b₁) (hb₁₂ : b₁ ≤ b₂) (hb₂ : b₂ < τ₀) :
    ∃ c : ℝ, 0 ≤ c ∧
      max |b₁ + (1 - τ₀) / 2| |b₂ + (1 - τ₀) / 2| < c ∧
      c < (τ₀ + 1) / 2 := by
  let c₀ := max |b₁ + (1 - τ₀) / 2| |b₂ + (1 - τ₀) / 2|
  have hc₀ : c₀ < (τ₀ + 1) / 2 := by
    dsimp [c₀]
    rw [max_lt_iff]
    constructor <;> apply abs_lt.mpr <;> constructor <;> nlinarith
  let c := (c₀ + (τ₀ + 1) / 2) / 2
  have hc₀c : c₀ < c := by dsimp [c]; linarith
  have hc : c < (τ₀ + 1) / 2 := by dsimp [c]; linarith
  have hc₀nonneg : 0 ≤ c₀ :=
    (abs_nonneg (b₁ + (1 - τ₀) / 2)).trans (le_max_left _ _)
  exact ⟨c, hc₀nonneg.trans hc₀c.le, hc₀c, hc⟩

/-- Closeness of the period controls the imaginary part of the transformed generator
argument on the whole closed vertical strip. -/
private lemma faddeevS_logarithmic_argument_im_le {τ₀ b₁ b₂ c ε : ℝ}
    (hc : max |b₁ + (1 - τ₀) / 2| |b₂ + (1 - τ₀) / 2| + ε / 2 ≤ c)
    {τ z : ℂ} (hτ : ‖τ - (τ₀ : ℂ)‖ ≤ ε) (hz : z.re ∈ Icc b₁ b₂) :
    |(-I * (z + (1 - τ) / 2)).im| ≤ c := by
  have hτball : τ ∈ Metric.closedBall (τ₀ : ℂ) ε := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hτ
  have hre : |τ.re - τ₀| ≤ ε := by
    simpa only [Complex.ofReal_re] using abs_re_sub_le_of_mem_closedBall hτball
  have hbase : |z.re + (1 - τ₀) / 2| ≤
      max |b₁ + (1 - τ₀) / 2| |b₂ + (1 - τ₀) / 2| :=
    abs_le_max_abs_abs
      (by simpa [add_comm] using add_le_add_right hz.1 ((1 - τ₀) / 2))
      (by simpa [add_comm] using add_le_add_right hz.2 ((1 - τ₀) / 2))
  rw [show (-I * (z + (1 - τ) / 2)).im = -(z.re + (1 - τ.re) / 2) by
    simp [Complex.mul_im], abs_neg]
  calc
    |z.re + (1 - τ.re) / 2| =
        |(z.re + (1 - τ₀) / 2) + (τ₀ - τ.re) / 2| := by ring_nf
    _ ≤ |z.re + (1 - τ₀) / 2| + |(τ₀ - τ.re) / 2| := abs_add_le _ _
    _ ≤ max |b₁ + (1 - τ₀) / 2| |b₂ + (1 - τ₀) / 2| + ε / 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_sub_comm]
      gcongr
    _ ≤ c := hc

/-- A small complex-period neighborhood preserves the double-sine source chamber and sends
the upper vertical strip to the right half of one fixed logarithmic substrip. -/
private lemma faddeevS_logarithmic_argument_mem_strip {τ₀ b₁ b₂ c ε : ℝ}
    (hτ₀ : 0 < τ₀) (hb₁ : -1 < b₁) (hb₂ : b₂ < τ₀)
    (hε1 : ε ≤ 1) (hετ : ε ≤ τ₀ / 2) (hεb : ε ≤ (τ₀ - b₂) / 2)
    (hc : max |b₁ + (1 - τ₀) / 2| |b₂ + (1 - τ₀) / 2| + ε / 2 ≤ c)
    {τ z : ℂ} (hτ : ‖τ - (τ₀ : ℂ)‖ ≤ ε) (hz : z.re ∈ Icc b₁ b₂)
    (hy : 1 ≤ z.im) :
    let w := -I * (z + (1 - τ) / 2)
    0 < τ.re ∧ -1 < z.re ∧ z.re < τ.re ∧ 0 ≤ w.re ∧ |w.im| ≤ c ∧
      w.re = z.im - τ.im / 2 ∧ |τ.im| ≤ 1 := by
  dsimp only
  let w := -I * (z + (1 - τ) / 2)
  have hτhalf : τ₀ / 2 ≤ τ.re ∧ |τ.im| ≤ 1 :=
    re_ge_and_abs_im_le_of_norm_sub_le hτ (by linarith) hε1
  have hτabove : (τ₀ + b₂) / 2 ≤ τ.re :=
    (re_ge_and_abs_im_le_of_norm_sub_le hτ (by linarith) hε1).1
  have hwre : w.re = z.im - τ.im / 2 := by
    simp [w, Complex.mul_re]
    ring_nf
  have hwimc : |w.im| ≤ c := by
    simpa [w] using faddeevS_logarithmic_argument_im_le hc hτ hz
  refine ⟨?_, hb₁.trans_le hz.1, ?_, ?_, hwimc, hwre, hτhalf.2⟩
  · linarith [hτhalf.1]
  · linarith [hz.2, hτabove]
  · rw [hwre]
    linarith [le_abs_self τ.im, hτhalf.2]

/-- A common positive radius can be chosen below the logarithmic estimate radius and every
geometric margin needed by `exists_norm_faddeevS_sub_one_le_of_re_mem_Icc`. -/
private lemma exists_faddeevS_complex_period_radius {ε₀ τ₀ b₂ c₀ c : ℝ}
    (hε₀ : 0 < ε₀) (hτ₀ : 0 < τ₀) (hb₂ : b₂ < τ₀) (hc : c₀ < c) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ ε₀ ∧ ε ≤ 1 ∧ ε ≤ τ₀ / 2 ∧
      ε ≤ (τ₀ - b₂) / 2 ∧ c₀ + ε / 2 ≤ c := by
  let δτ := min (τ₀ / 2) ((τ₀ - b₂) / 2)
  let δc := min 1 (c - c₀)
  let δ := min δτ δc
  let ε := min ε₀ δ
  have hδτ : 0 < δτ := by dsimp [δτ]; positivity
  have hδc : 0 < δc := by dsimp [δc]; positivity
  have hδ : 0 < δ := lt_min hδτ hδc
  have hε : 0 < ε := lt_min hε₀ hδ
  have hεδ : ε ≤ δ := min_le_right _ _
  refine ⟨ε, hε, min_le_left _ _, ?_, ?_, ?_, ?_⟩
  · exact hεδ.trans (min_le_right _ _) |>.trans (min_le_left _ _)
  · exact hεδ.trans (min_le_left _ _) |>.trans (min_le_left _ _)
  · exact hεδ.trans (min_le_left _ _) |>.trans (min_le_right _ _)
  · have hεc : ε ≤ c - c₀ :=
      hεδ.trans (min_le_right _ _) |>.trans (min_le_right _ _)
    linarith

/-! ### Uniform generator estimate -/

/-- The real part shift `Re w = Im z - Im τ/2` converts logarithmic decay in `w` into
uniform decay in `Im z`. -/
private lemma norm_remainder_le_of_re_eq_im_sub {τ z w E : ℂ} {C κ : ℝ}
    (hκ : 0 ≤ κ) (hwre : w.re = z.im - τ.im / 2)
    (hτim : |τ.im| ≤ 1) (hE : ‖E‖ ≤ C * Real.exp (-κ * w.re)) :
    ‖E‖ ≤ (C * Real.exp (κ / 2)) * Real.exp (-κ * z.im) := by
  have hCmul : 0 ≤ C * Real.exp (-κ * w.re) := (norm_nonneg E).trans hE
  have hC : 0 ≤ C := nonneg_of_mul_nonneg_left hCmul (Real.exp_pos _)
  have hτim' : τ.im ≤ 1 := (le_abs_self τ.im).trans hτim
  calc
    ‖E‖ ≤ C * Real.exp (-κ * w.re) := hE
    _ ≤ C * Real.exp (κ / 2 - κ * z.im) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.exp_le_exp.mpr
      rw [hwre]
      nlinarith
    _ = (C * Real.exp (κ / 2)) * Real.exp (-κ * z.im) := by
      rw [show κ / 2 - κ * z.im = κ / 2 + -κ * z.im by ring_nf, Real.exp_add]
      ring_nf

/-- Exponentiating a uniformly small normalized logarithmic remainder preserves its
exponential decay rate. -/
private lemma norm_exp_I_mul_sub_one_le {z E : ℂ} {D κ : ℝ}
    (hdecay : ‖E‖ ≤ D * Real.exp (-κ * z.im)) (hED : ‖E‖ ≤ D) :
    ‖Complex.exp (I * E) - 1‖ ≤
      (D * Real.exp D) * Real.exp (-κ * z.im) := by
  have hD : 0 ≤ D := (norm_nonneg E).trans hED
  have hexp := Complex.norm_exp_sub_sum_le_norm_mul_exp (I * E) 1
  have hmono : Real.exp ‖E‖ ≤ Real.exp D := Real.exp_le_exp.mpr hED
  calc
    ‖Complex.exp (I * E) - 1‖ ≤ ‖I * E‖ ^ 1 * Real.exp ‖I * E‖ := by
      simpa using hexp
    _ = ‖E‖ * Real.exp ‖E‖ := by simp
    _ ≤ (D * Real.exp (-κ * z.im)) * Real.exp D :=
      mul_le_mul hdecay hmono (Real.exp_pos _).le
        (mul_nonneg hD (Real.exp_pos _).le)
    _ = (D * Real.exp D) * Real.exp (-κ * z.im) := by ring_nf

/-- The logarithmic remainder estimate and the exact generator normalization give the
pointwise generator estimate used in
`exists_norm_faddeevS_sub_one_le_of_re_mem_Icc`. -/
private lemma norm_faddeevS_sub_one_le_of_log_bound {τ z w E : ℂ} {C κ : ℝ}
    (hκ : 0 ≤ κ) (hy : 0 ≤ z.im)
    (hwre : w.re = z.im - τ.im / 2) (hτim : |τ.im| ≤ 1)
    (hE : ‖E‖ ≤ C * Real.exp (-κ * w.re))
    (hrepresentation : faddeevS z τ = Complex.exp (I * E)) :
    ‖faddeevS z τ - 1‖ ≤
      ((C * Real.exp (κ / 2)) * Real.exp (C * Real.exp (κ / 2))) *
        Real.exp (-κ * z.im) := by
  let D := C * Real.exp (κ / 2)
  have hCmul : 0 ≤ C * Real.exp (-κ * w.re) := (norm_nonneg E).trans hE
  have hC : 0 ≤ C := nonneg_of_mul_nonneg_left hCmul (Real.exp_pos _)
  have hD : 0 ≤ D := mul_nonneg hC (Real.exp_nonneg _)
  have hEdecay : ‖E‖ ≤ D * Real.exp (-κ * z.im) := by
    simpa [D] using norm_remainder_le_of_re_eq_im_sub hκ hwre hτim hE
  have hED : ‖E‖ ≤ D := hEdecay.trans (by
    have he : Real.exp (-κ * z.im) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by nlinarith)
    simpa using mul_le_mul_of_nonneg_left he hD)
  rw [hrepresentation]
  simpa [D] using norm_exp_I_mul_sub_one_le hEdecay hED

/-- **New.** Let `τ₀ > 0` and let `[b₁,b₂]` lie inside `(-1,τ₀)`. On a fixed upper tail of
that vertical strip, `Φ_{S,0,0}(z;τ)` tends exponentially to one, uniformly for complex `τ`
near `τ₀`. This is the uniform complex-period boundary-passage extension of the upper clause
of [RW26, Radchenko--Wheeler (2026), Lemma 1, `lem:asymp`]. The proof follows Ruijsenaars
(1997), Proposition III.4, through
`exists_norm_doubleSineComplexLogRemainder_le`. This uniform statement is absent
from the searched [AFK25], [RW26, Radchenko--Wheeler (2026), Lemma 1, `lem:asymp`, and
Appendix A.2], and
Ruijsenaars (1997), Proposition III.4 and its continuation argument. -/
theorem exists_norm_faddeevS_sub_one_le_of_re_mem_Icc {τ₀ b₁ b₂ : ℝ}
    (hτ₀ : 0 < τ₀) (hb₁ : -1 < b₁) (hb₁₂ : b₁ ≤ b₂) (hb₂ : b₂ < τ₀) :
    ∃ ε C κ R : ℝ, 0 < ε ∧ 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ (τ z : ℂ), ‖τ - (τ₀ : ℂ)‖ ≤ ε → z.re ∈ Icc b₁ b₂ → R ≤ z.im →
        ‖faddeevS z τ - 1‖ ≤ C * Real.exp (-κ * z.im) := by
  obtain ⟨c, hc0, hcmax, hc⟩ :=
    exists_faddeevS_logarithmic_substrip hb₁ hb₁₂ hb₂
  obtain ⟨ε₀, C₀, κ, hε₀, hC₀, hκ, hlog⟩ :=
    exists_norm_doubleSineComplexLogRemainder_le hτ₀ hc0 hc
  let c₀ := max |b₁ + (1 - τ₀) / 2| |b₂ + (1 - τ₀) / 2|
  have hc₀c : c₀ < c := by
    change max |b₁ + (1 - τ₀) / 2| |b₂ + (1 - τ₀) / 2| < c
    exact hcmax
  obtain ⟨ε, hε, hε₀', hε1, hετ, hεb, hεc⟩ :=
    exists_faddeevS_complex_period_radius hε₀ hτ₀ hb₂ hc₀c
  let D := C₀ * Real.exp (κ / 2)
  let C := D * Real.exp D
  refine ⟨ε, C, κ, 1, hε, (by dsimp [C, D]; positivity), hκ, by norm_num, ?_⟩
  intro τ z hτ hz hy
  let w := -I * (z + (1 - τ) / 2)
  let E := doubleSineComplexLogRemainder w τ
  obtain ⟨hτre, hzlow, hzup, hwre0, hwim, hwre, hτim⟩ :=
    faddeevS_logarithmic_argument_mem_strip hτ₀ hb₁ hb₂ hε1 hετ hεb
      (by simpa [c₀] using hεc) hτ hz hy
  have hE0 : ‖E‖ ≤ C₀ * Real.exp (-κ * w.re) := by
    simpa [E] using hlog τ w (hτ.trans hε₀') hwre0 hwim
  have hrepresentation : faddeevS z τ = Complex.exp (I * E) := by
    simpa [E, w] using
      faddeevS_eq_exp_doubleSineComplexLogRemainder z τ hτre hzlow hzup
  simpa [C, D] using norm_faddeevS_sub_one_le_of_log_bound
    hκ.le (by linarith) hwre hτim hE0 hrepresentation

/-! ### Combining exponential errors -/

/-- The complex-period integer shift combines a strip estimate and an inverse finite-symbol
estimate at the minimum of their exponential rates. -/
private lemma norm_faddeevS_sub_one_le_of_shift (z w τ : ℂ) (n : ℤ)
    {C D p q y : ℝ} (hp : 0 ≤ p) (hy : 0 ≤ y)
    (hw : w + n = z) (hτ : τ ∈ Complex.slitPlane) (hwi : 0 < w.im)
    (hphase : ∀ j ∈ Ico (min n 0) (max n 0),
      0 < ((w + 1) / τ + (j : ℂ) * τ⁻¹).im)
    (hstrip : ‖faddeevS w τ - 1‖ ≤ C * Real.exp (-p * y))
    (hfin : qPochhammerFin n ((w + 1) / τ) τ⁻¹ ≠ 0 ∧
      ‖(qPochhammerFin n ((w + 1) / τ) τ⁻¹)⁻¹ - 1‖ ≤
        D * Real.exp (-q * y)) :
    ‖faddeevS z τ - 1‖ ≤
      ((1 + C) * D + C) * Real.exp (-(min p q) * y) := by
  let P := qPochhammerFin n ((w + 1) / τ) τ⁻¹
  have hshift := faddeevS_add_intCast_mul_qPochhammerFin_of_pos_im
    w τ hτ hwi n hphase
  have hshift' : faddeevS z τ * P = faddeevS w τ := by
    simpa only [P, hw] using hshift
  have hquot : faddeevS z τ = faddeevS w τ * P⁻¹ := by
    simpa only [P, div_eq_mul_inv] using (eq_div_iff hfin.1).2 hshift'
  rw [hquot]
  exact norm_mul_sub_one_le_of_exponential_bounds _ _ hp hy hstrip hfin.2

/-! ### Upper sectors -/

/-- Uniformly near a positive real period, the floor-shift phases are positive and the inverse
finite symbol differs exponentially from one throughout an upper sector. -/
private lemma exists_floor_shift_factor_bound_near_real_period
    {τ₀ : ℝ} (hτ₀ : 0 < τ₀) (a K : ℝ) :
    ∃ ε D q R : ℝ, 0 < ε ∧ 0 < D ∧ 0 < q ∧ 0 < R ∧
      ∀ (τ z : ℂ), ‖τ - (τ₀ : ℂ)‖ ≤ ε → |z.re| ≤ K * z.im → R ≤ z.im →
        let n : ℤ := ⌊z.re - a⌋; let w : ℂ := z - n
        (∀ j ∈ Ico (min n 0) (max n 0), 0 < ((w + 1) / τ + (j : ℂ) * τ⁻¹).im) ∧
          qPochhammerFin n ((w + 1) / τ) τ⁻¹ ≠ 0 ∧
            ‖(qPochhammerFin n ((w + 1) / τ) τ⁻¹)⁻¹ - 1‖ ≤
              D * Real.exp (-q * z.im) := by
  obtain ⟨ε, c, hε, hc, hphase⟩ := exists_uniform_floor_phase_im_lower_bound hτ₀ a K
  obtain ⟨C, hC, R, hR, hfin⟩ :=
    exists_norm_qPochhammerFin_inv_sub_one_le K (|a| + 1) c hc
  refine ⟨ε, 2 * C, Real.pi * c, max R 1, hε, by positivity, by positivity,
    lt_of_lt_of_le hR (le_max_left _ _), ?_⟩
  intro τ z hτ hz hy
  let n : ℤ := ⌊z.re - a⌋
  let w : ℂ := z - n
  have hyR : R ≤ z.im := (le_max_left R 1).trans hy
  have hy1 : 1 ≤ z.im := (le_max_right R 1).trans hy
  have hf := floor_window_of_abs_re_le z a K hz
  have hp := hphase τ z hτ hy1 hz
  have hP := hfin z.im n ((w + 1) / τ) τ⁻¹ hyR
    (by simpa only [n, add_assoc] using hf.2) (by simpa only [n, w] using hp)
  refine ⟨fun j hj => (mul_pos hc (by linarith)).trans_le (hp j hj), hP.1, ?_⟩
  simpa only [mul_assoc] using hP.2

/-- Exponential convergence on a unit window propagates to the whole upper sector through the
complex-period floor shift and its finite symbol. -/
private lemma exists_norm_faddeevS_sub_one_le_of_window
    {τ₀ a : ℝ} (hτ₀ : 0 < τ₀) (ha : -1 < a) (haτ : a + 1 < τ₀) (K : ℝ) :
    ∃ ε C κ R : ℝ, 0 < ε ∧ 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ (τ z : ℂ), ‖τ - (τ₀ : ℂ)‖ ≤ ε → |z.re| ≤ K * z.im → R ≤ z.im →
        ‖faddeevS z τ - 1‖ ≤ C * Real.exp (-κ * z.im) := by
  obtain ⟨εs, Cs, κs, Rs, hεs, hCs, hκs, hRs, hs⟩ :=
    exists_norm_faddeevS_sub_one_le_of_re_mem_Icc hτ₀ ha (by linarith) haτ
  obtain ⟨εf, D, q, Rf, hεf, hD, hq, hRf, hf⟩ :=
    exists_floor_shift_factor_bound_near_real_period hτ₀ a K
  let ε := min εs (min εf (τ₀ / 2))
  let C := (1 + Cs) * D + Cs
  let κ := min κs q
  let R := max Rs Rf
  refine ⟨ε, C, κ, R, (by dsimp [ε]; positivity), (by dsimp [C]; positivity),
    (by dsimp [κ]; positivity), (by dsimp [R]; positivity), ?_⟩
  intro τ z hτ hz hy
  let n : ℤ := ⌊z.re - a⌋
  let w : ℂ := z - n
  have hw := (floor_window_of_abs_re_le z a K hz).1
  have hfin := hf τ z (hτ.trans ((min_le_right _ _).trans (min_le_left _ _))) hz
    ((le_max_right Rs Rf).trans hy)
  have hstrip : ‖faddeevS w τ - 1‖ ≤ Cs * Real.exp (-κs * z.im) := by
    simpa [w] using hs τ w (hτ.trans (min_le_left _ _)) (by simpa only [n, w] using hw)
      (by simpa [w] using (le_max_left Rs Rf).trans hy)
  apply norm_faddeevS_sub_one_le_of_shift z w τ n hκs.le
    (by linarith [hRs, (le_max_left Rs Rf).trans hy]) (by simp [w, n])
    (Complex.mem_slitPlane_iff.mpr (Or.inl (re_pos_of_norm_sub_le
      ((min_le_right _ _).trans (min_le_right _ _) |>.trans_lt (by linarith)) hτ)))
    (by simpa [w] using hRs.trans_le ((le_max_left Rs Rf).trans hy))
    (by simpa only [n, w] using hfin.1) hstrip
  simpa only [C, κ, n, w] using hfin.2

/-- **New.** For complex periods uniformly near a positive real period, the Faddeev generator
tends exponentially to one in every upper sector. This extends the upper clause of [RW26,
Radchenko--Wheeler (2026), Lemma 1, `lem:asymp`] from a fixed real period by combining the
Ruijsenaars strip estimate with complex-period finite shifts. The uniform neighborhood statement
is absent from the searched [AFK25], [RW26, Radchenko, Wheeler (2026), Appendix A.2,
`app:mod.fad`], and Ruijsenaars (1997), Proposition III.4. -/
theorem exists_norm_faddeevS_sub_one_le_near_real_period {τ₀ : ℝ} (hτ₀ : 0 < τ₀) (K : ℝ) :
    ∃ ε C κ R : ℝ, 0 < ε ∧ 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ (τ z : ℂ), ‖τ - (τ₀ : ℂ)‖ ≤ ε → |z.re| ≤ K * z.im → R ≤ z.im →
        ‖faddeevS z τ - 1‖ ≤ C * Real.exp (-κ * z.im) := by
  exact exists_norm_faddeevS_sub_one_le_of_window hτ₀
    (a := τ₀ / 2 - 1) (by linarith) (by linarith) K

/-! ### Continuous affine families -/

/-- Uniform upper-sector decay is stable under a continuously parameterized affine change of
argument whose limiting slope and period are positive real numbers. This transports
`exists_norm_faddeevS_sub_one_le_near_real_period` to the affine families used by the principal
construction. -/
theorem exists_norm_faddeevS_affine_sub_one_le
    {q₀ : ℂ} {a b t : ℂ → ℂ} {a₀ t₀ : ℝ}
    (ha : ContinuousAt a q₀) (hb : ContinuousAt b q₀) (ht : ContinuousAt t q₀)
    (ha₀ : a q₀ = (a₀ : ℂ)) (ht₀ : t q₀ = (t₀ : ℂ))
    (ha₀pos : 0 < a₀) (ht₀pos : 0 < t₀) (K : ℝ) :
    ∃ ε C κ R : ℝ, 0 < ε ∧ 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ (q z : ℂ), ‖q - q₀‖ ≤ ε → |z.re| ≤ K * z.im → R ≤ z.im →
        ‖faddeevS (a q * z + b q) (t q) - 1‖ ≤ C * Real.exp (-κ * z.im) := by
  obtain ⟨εg, c, L, Rg, hεg, hc, hL, hRg, hgeom⟩ :=
    exists_upperSector_affine_near_parameter ha hb ha₀ ha₀pos K
  obtain ⟨εu, C, κu, Ru, hεu, hC, hκu, hRu, hupper⟩ :=
    exists_norm_faddeevS_sub_one_le_near_real_period ht₀pos L
  obtain ⟨δt, hδt, ht'⟩ := ContinuousAt.exists_norm_sub_le ht hεu
  let ε := min εg δt
  let κ := κu * c
  let R := max Rg (Ru / c)
  refine ⟨ε, C, κ, R, (by dsimp [ε]; positivity), hC, (by dsimp [κ]; positivity),
    (by dsimp [R]; positivity), ?_⟩
  intro q z hq hz hy
  have htq : ‖t q - (t₀ : ℂ)‖ ≤ εu := by
    simpa only [ht₀] using ht' q (hq.trans (min_le_right _ _))
  have hg := hgeom q z (hq.trans (min_le_left _ _)) hz ((le_max_left _ _).trans hy)
  have hbound := hupper (t q) (a q * z + b q) htq hg.2 (by
    have := (div_le_iff₀ hc).mp ((le_max_right Rg (Ru / c)).trans hy)
    nlinarith [hg.1])
  have hexp : -κu * (a q * z + b q).im ≤ -(κu * c) * z.im := by
    nlinarith [hg.1]
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by simpa only [κ] using hexp)) hC.le)

/-! ### Lower sectors -/

/-- On the genuine reflection domain, division by the reflected quadratic exponential is the
inverse generator at the reflected argument. -/
private lemma faddeevS_div_exp_eq_inv (z τ : ℂ) (hτ : τ ≠ 0)
    (hzden : barnesDoubleGammaInv (τ - z) 1 τ ≠ 0)
    (hwden : barnesDoubleGammaInv (z + 1) 1 τ ≠ 0) :
    faddeevS z τ / Complex.exp (-Real.pi * I *
      (z ^ 2 / τ - (1 - τ⁻¹) * z + (τ + τ⁻¹) / 6 - 1 / 2)) =
      (faddeevS (-z + τ - 1) τ)⁻¹ := by
  let E := Complex.exp (-Real.pi * I *
    (z ^ 2 / τ - (1 - τ⁻¹) * z + (τ + τ⁻¹) / 6 - 1 / 2))
  have hwden' : barnesDoubleGammaInv (1 - (-z)) 1 τ ≠ 0 := by
    simpa [sub_eq_add_neg, add_comm] using hwden
  have hzden' : barnesDoubleGammaInv (-z + τ) 1 τ ≠ 0 := by
    simpa [sub_eq_add_neg, add_comm] using hzden
  have hreflect : faddeevS (-z + τ - 1) τ * faddeevS z τ = E := by
    convert faddeevS_mul_neg (-z) τ hτ hwden' hzden' using 1
    · simp
    · dsimp [E]
      congr 1
      ring
  have hwne : faddeevS (-z + τ - 1) τ ≠ 0 := by
    intro hw
    rw [hw, zero_mul] at hreflect
    exact Complex.exp_ne_zero _ hreflect.symm
  change faddeevS z τ / E = (faddeevS (-z + τ - 1) τ)⁻¹
  apply (div_eq_iff (Complex.exp_ne_zero _)).2
  change faddeevS z τ = (faddeevS (-z + τ - 1) τ)⁻¹ * E
  rw [← hreflect]
  simp [hwne]

/-- The reflected argument `-z+τ-1` inherits a uniform exponential upper-sector estimate when
`z` lies in a lower sector and the complex period is near a positive real period. -/
private lemma exists_norm_faddeevS_reflected_sub_one_le
    {τ₀ : ℝ} (hτ₀ : 0 < τ₀) (K : ℝ) :
    ∃ ε C κ R : ℝ, 0 < ε ∧ 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ (τ z : ℂ), ‖τ - (τ₀ : ℂ)‖ ≤ ε → |z.re| ≤ K * (-z.im) → R ≤ -z.im →
        ‖faddeevS (-z + τ - 1) τ - 1‖ ≤ C * Real.exp (-κ * (-z.im)) := by
  obtain ⟨ε, C, κ, R, hε, hC, hκ, hR, hbound⟩ :=
    exists_norm_faddeevS_affine_sub_one_le
      (q₀ := (τ₀ : ℂ)) (a := fun _ => 1) (b := fun τ => τ - 1) (t := id)
      (a₀ := 1) (t₀ := τ₀) continuousAt_const
      (continuousAt_id.sub continuousAt_const) continuousAt_id (by simp) (by simp)
      (by norm_num) hτ₀ K
  refine ⟨ε, C, κ, R, hε, hC, hκ, hR, fun τ z hτ hz hy => ?_⟩
  simpa only [one_mul, id_eq, Complex.neg_re, Complex.neg_im, abs_neg, sub_eq_add_neg,
    add_assoc] using
    hbound τ (-z) hτ (by simpa only [Complex.neg_re, Complex.neg_im, abs_neg] using hz)
      (by simpa only [Complex.neg_im] using hy)

/-- A near-one bound for the reflected generator, together with the genuine lower cone, gives
the normalized lower-sector estimate by reflection and stable inversion. -/
private lemma norm_faddeevS_div_exp_sub_one_le (z τ : ℂ) {C κ y : ℝ}
    (hslit : τ ∈ Complex.slitPlane) (hz : z.im < 0) (hzdiv : (z / τ).im < 0)
    (hdecay : ‖faddeevS (-z + τ - 1) τ - 1‖ ≤ C * Real.exp (-κ * y))
    (hκy : 2 * C ≤ κ * y) :
    ‖faddeevS z τ / Complex.exp (-Real.pi * I *
      (z ^ 2 / τ - (1 - τ⁻¹) * z + (τ + τ⁻¹) / 6 - 1 / 2)) - 1‖ ≤
        2 * C * Real.exp (-κ * y) := by
  let w := -z + τ - 1
  have hdecay' : ‖faddeevS w τ - 1‖ ≤ C * Real.exp (-κ * y) := by
    simpa [w] using hdecay
  have hhalf : ‖faddeevS w τ - 1‖ ≤ 1 / 2 := hdecay'.trans (by
    nlinarith [two_mul_mul_exp_neg_le_one κ C y hκy])
  obtain ⟨_, hinv⟩ := norm_inv_sub_one_le_two_mul_norm_sub_one (faddeevS w τ) hhalf
  have hzden := faddeevS_denominator_ne_zero_of_neg_im z τ hslit hz hzdiv
  have hwden := faddeevS_numerator_ne_zero_of_neg_im z τ hslit hz hzdiv
  have hreflect := faddeevS_div_exp_eq_inv z τ
    (Complex.slitPlane_ne_zero hslit) hzden hwden
  rw [hreflect]
  calc
    ‖(faddeevS w τ)⁻¹ - 1‖ ≤ 2 * ‖faddeevS w τ - 1‖ := hinv
    _ ≤ 2 * (C * Real.exp (-κ * y)) := mul_le_mul_of_nonneg_left hdecay' (by norm_num)
    _ = 2 * C * Real.exp (-κ * y) := by ring

/-- **New.** For complex periods uniformly near a positive real period, the Faddeev generator
divided by its exact reflected quadratic exponential tends exponentially to one in every lower
sector. This is the quantitative reflection consequence of the upper-sector extension of
[RW26, Radchenko--Wheeler (2026), Lemma 1, `lem:asymp`]. The uniform neighborhood statement is
absent from the searched [AFK25], [RW26, Radchenko--Wheeler (2026), Appendix A.2,
`app:mod.fad`], and Ruijsenaars (1997), Proposition III.4. -/
theorem exists_norm_faddeevS_div_exp_sub_one_le
    {τ₀ : ℝ} (hτ₀ : 0 < τ₀) (K : ℝ) :
    ∃ ε C κ R : ℝ, 0 < ε ∧ 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ (τ z : ℂ), ‖τ - (τ₀ : ℂ)‖ ≤ ε → |z.re| ≤ K * (-z.im) → R ≤ -z.im →
        ‖faddeevS z τ / Complex.exp (-Real.pi * I *
          (z ^ 2 / τ - (1 - τ⁻¹) * z + (τ + τ⁻¹) / 6 - 1 / 2)) - 1‖ ≤
            C * Real.exp (-κ * (-z.im)) := by
  obtain ⟨εr, Cr, κ, Rr, hεr, hCr, hκ, hRr, hreflected⟩ :=
    exists_norm_faddeevS_reflected_sub_one_le hτ₀ K
  obtain ⟨εn, cn, hεn, hcn, hn⟩ := exists_uniform_div_im_lower_bound hτ₀ K
  let ε := min εr (min εn (τ₀ / 2))
  let C := 2 * Cr
  let R := max Rr (2 * Cr / κ)
  refine ⟨ε, C, κ, R, (by dsimp [ε]; positivity), (by dsimp [C]; positivity),
    hκ, (by dsimp [R]; positivity), ?_⟩
  intro τ z hτ hz hy
  let y := -z.im
  have hyRr : Rr ≤ y := (le_max_left _ _).trans hy
  have hypos : 0 < y := hRr.trans_le hyRr
  have hdecay := hreflected τ z (hτ.trans (min_le_left _ _)) hz (by simpa [y] using hyRr)
  have hnpos := hn τ (-z) (hτ.trans ((min_le_right _ _).trans (min_le_left _ _)))
    (by simpa [y] using hypos.le) (by simpa [y] using hz)
  have hzdivneg : (z / τ).im < 0 := by
    have := (mul_pos hcn hypos).trans_le (by simpa [y] using hnpos)
    simpa only [neg_div, Complex.neg_im, neg_pos] using this
  have hκy : 2 * Cr ≤ κ * y := by
    have := (div_le_iff₀ hκ).mp ((le_max_right Rr (2 * Cr / κ)).trans hy)
    nlinarith
  have hslit : τ ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (re_pos_of_norm_sub_le
      ((min_le_right _ _).trans (min_le_right _ _) |>.trans_lt (by linarith)) hτ))
  have hzneg : z.im < 0 := by simpa [y] using neg_lt_zero.mpr hypos
  simpa [C, y] using norm_faddeevS_div_exp_sub_one_le z τ hslit hzneg hzdivneg
    (by simpa [y] using hdecay) hκy

/-- Uniform normalized lower-sector decay is stable under a continuously parameterized affine
change of argument whose limiting slope and period are positive real numbers. This transports
`exists_norm_faddeevS_div_exp_sub_one_le` to the affine families used by
the principal construction. -/
theorem exists_norm_faddeevS_affine_div_exp_sub_one_le
    {q₀ : ℂ} {a b t : ℂ → ℂ} {a₀ t₀ : ℝ}
    (ha : ContinuousAt a q₀) (hb : ContinuousAt b q₀) (ht : ContinuousAt t q₀)
    (ha₀ : a q₀ = (a₀ : ℂ)) (ht₀ : t q₀ = (t₀ : ℂ))
    (ha₀pos : 0 < a₀) (ht₀pos : 0 < t₀) (K : ℝ) :
    ∃ ε C κ R : ℝ, 0 < ε ∧ 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ (q z : ℂ), ‖q - q₀‖ ≤ ε → |z.re| ≤ K * (-z.im) → R ≤ -z.im →
        ‖faddeevS (a q * z + b q) (t q) / Complex.exp (-Real.pi * I *
          ((a q * z + b q) ^ 2 / t q - (1 - (t q)⁻¹) * (a q * z + b q) +
            (t q + (t q)⁻¹) / 6 - 1 / 2)) - 1‖ ≤
            C * Real.exp (-κ * (-z.im)) := by
  obtain ⟨εg, c, L, Rg, hεg, hc, hL, hRg, hgeom⟩ :=
    exists_lowerSector_affine_near_parameter ha hb ha₀ ha₀pos K
  obtain ⟨εl, C, κl, Rl, hεl, hC, hκl, hRl, hlower⟩ :=
    exists_norm_faddeevS_div_exp_sub_one_le ht₀pos L
  obtain ⟨δt, hδt, ht'⟩ := ContinuousAt.exists_norm_sub_le ht hεl
  let ε := min εg δt
  let κ := κl * c
  let R := max Rg (Rl / c)
  refine ⟨ε, C, κ, R, (by dsimp [ε]; positivity), hC, (by dsimp [κ]; positivity),
    (by dsimp [R]; positivity), ?_⟩
  intro q z hq hz hy
  have htq : ‖t q - (t₀ : ℂ)‖ ≤ εl := by
    simpa only [ht₀] using ht' q (hq.trans (min_le_right _ _))
  have hg := hgeom q z (hq.trans (min_le_left _ _)) hz ((le_max_left _ _).trans hy)
  have hbound := hlower (t q) (a q * z + b q) htq hg.2 (by
    have := (div_le_iff₀ hc).mp ((le_max_right Rg (Rl / c)).trans hy)
    nlinarith [hg.1])
  have hexp : -κl * (-(a q * z + b q).im) ≤ -(κl * c) * (-z.im) := by
    nlinarith [hg.1]
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by simpa only [κ] using hexp)) hC.le)

end SIC

end
