/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.QPochhammer.Theta

/-!
# Growth of q-products

The Gaussian growth of `ϖ(u,τ)` in the lower half plane, with matching upper and lower bounds.

This module supplies the product estimates behind the kernel bounds of the modular five-term
integral in [RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`], whose convergence the
source attributes to the growth of theta quotients. The growth exponent is
`Γ_τ(u) = π m²/Im τ - π m` with `m = min(Im u, 0)`: it vanishes in the upper half plane and agrees
with the Gaussian exponent `qThetaGrowth` of `θ(u,τ)` in the lower half plane.

## The argument

In the upper half plane `ϖ(u,τ)` is bounded, since `‖ϖ(u,τ) - 1‖` is bounded by a geometric
series, and it is bounded below at any fixed height above the real axis
(`exists_pos_le_norm_qPochhammer_of_le_im`). In the lower half plane
`ϖ(u,τ) = θ(u,τ)/ϖ(τ-u,τ)`, where `τ - u` lies at height at least `Im τ`, so the Gaussian bounds of
`θ` are those of `ϖ` up to constants. Near the real axis both descriptions apply, and `Γ_τ` and the
Gaussian exponent differ there by at most `π Im τ/4`. A lower bound needs a positive distance to
the zeros `k - jτ`; below height `Im τ/2` the other lattice points `k + nτ`, `n ≥ 1`, are at
distance at least `Im τ/2`, so this is the distance to the lattice that the theta bound requires.

For `ϖ(x,τ₁)/ϖ(y,τ₂)`, a lower bound away from the zeros of the denominator and an upper bound
for the numerator give the difference of their Gaussian exponents. Below both half-height lines,
the reflected factors `ϖ(τ₁-x,τ₁)` and `ϖ(τ₂-y,τ₂)` have fixed positive bounds. A comparison of
the two theta products therefore gives a comparison of the q-product quotient, even where both
theta products vanish.
-/

noncomputable section

open Complex Real

namespace SIC

/-! ### The growth exponent

`Γ_τ(u)` depends only on `Im u`. It is continuous, and a shift of the argument by `a` changes it by
`2π Im a min(Im u, 0)/Im τ` up to a bounded error. -/

/-- The growth exponent of `ϖ(u,τ)`: `Γ_τ(u) = π m²/Im τ - π m` with `m = min(Im u, 0)`. It
vanishes in the upper half plane and is the Gaussian exponent of `θ(u,τ)` in the lower one. -/
def qPochhammerGrowth (u τ : ℂ) : ℝ :=
  π * min u.im 0 ^ 2 / τ.im - π * min u.im 0

/-- `Γ_τ(u) = 0` in the closed upper half plane. -/
theorem qPochhammerGrowth_of_nonneg (τ : ℂ) {u : ℂ} (hu : 0 ≤ u.im) :
    qPochhammerGrowth u τ = 0 := by
  simp [qPochhammerGrowth, min_eq_right hu]

/-- `Γ_τ(u)` is the Gaussian exponent of `θ(u,τ)` in the closed lower half plane. -/
theorem qPochhammerGrowth_of_nonpos (τ : ℂ) {u : ℂ} (hu : u.im ≤ 0) :
    qPochhammerGrowth u τ = qThetaGrowth u τ := by
  simp [qPochhammerGrowth, qThetaGrowth, min_eq_left hu]

/-- The theta exponent is at most the growth exponent below height `Im τ`. -/
theorem qThetaGrowth_le_qPochhammerGrowth {τ u : ℂ} (hτ : 0 < τ.im) (hu : u.im ≤ τ.im) :
    qThetaGrowth u τ ≤ qPochhammerGrowth u τ := by
  by_cases h : u.im ≤ 0
  · rw [qPochhammerGrowth_of_nonpos τ h]
  · have h0 : 0 ≤ u.im := le_of_not_ge h
    rw [qPochhammerGrowth_of_nonneg τ h0]
    unfold qThetaGrowth
    rw [sub_le_iff_le_add, zero_add]
    apply (div_le_iff₀ hτ).mpr
    nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le h0) (sub_nonneg.mpr hu)]

/-- The growth exponent exceeds the theta exponent by at most `π Im τ/4`. -/
theorem qPochhammerGrowth_le_qThetaGrowth_add (τ u : ℂ) (hτ : 0 < τ.im) :
    qPochhammerGrowth u τ ≤ qThetaGrowth u τ + π * τ.im / 4 := by
  by_cases h : u.im ≤ 0
  · rw [qPochhammerGrowth_of_nonpos τ h]
    have : 0 ≤ π * τ.im / 4 := by positivity
    linarith
  · have h0 : 0 ≤ u.im := le_of_not_ge h
    rw [qPochhammerGrowth_of_nonneg τ h0]
    unfold qThetaGrowth
    calc
      0 ≤ π * (u.im - τ.im / 2) ^ 2 / τ.im :=
        div_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg _)) hτ.le
      _ = π * u.im ^ 2 / τ.im - π * u.im + π * τ.im / 4 := by
        field_simp
        ring

/-- `Γ_τ(u)` is continuous in `u`. -/
theorem continuous_qPochhammerGrowth (τ : ℂ) : Continuous fun u => qPochhammerGrowth u τ := by
  unfold qPochhammerGrowth
  fun_prop

/-- The real shift estimate when a negative height crosses the axis upward; used by
`qPochhammerGrowth_shift_real`. -/
private lemma qPochhammerGrowth_shift_cross_up (t b m : ℝ) (ht : 0 < t)
    (hm : m ≤ 0) (hmb : 0 ≤ m + b) :
    |(π * 0 ^ 2 / t - π * 0) - (π * m ^ 2 / t - π * m) - 2 * π * b * m / t| ≤
      π * b ^ 2 / t + π * |b| := by
  have hπ : 0 < π := Real.pi_pos
  have hq : 0 < t⁻¹ := inv_pos.mpr ht
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  have hb : 0 ≤ b := by linarith
  have hquadlo : 0 ≤ -m ^ 2 - 2 * b * m := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ -m) (by linarith : 0 ≤ m + 2 * b)]
  have hquadhi : -m ^ 2 - 2 * b * m ≤ b ^ 2 := by
    nlinarith [sq_nonneg (m + b)]
  rw [abs_of_nonneg hb, abs_le]
  constructor <;> nlinarith [mul_nonneg (mul_nonneg hπ.le hq.le) hquadlo,
    mul_nonneg (mul_nonneg hπ.le hq.le) (sub_nonneg.mpr hquadhi)]

/-- The real shift estimate when a positive height crosses the axis downward; used by
`qPochhammerGrowth_shift_real`. -/
private lemma qPochhammerGrowth_shift_cross_down (t b m : ℝ) (ht : 0 < t)
    (hm : 0 ≤ m) (hmb : m + b ≤ 0) :
    |(π * (m + b) ^ 2 / t - π * (m + b)) -
      (π * 0 ^ 2 / t - π * 0) - 2 * π * b * 0 / t| ≤
      π * b ^ 2 / t + π * |b| := by
  have hπ : 0 < π := Real.pi_pos
  have hq : 0 < t⁻¹ := inv_pos.mpr ht
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  have hb : b ≤ 0 := by linarith
  have hylo : b ≤ m + b := by linarith
  have hyhi : (m + b) ^ 2 ≤ b ^ 2 := by
    nlinarith [mul_nonneg hm (by linarith : 0 ≤ -m - 2 * b)]
  rw [abs_of_nonpos hb, abs_le]
  constructor <;> nlinarith [
    mul_nonneg (mul_nonneg hπ.le hq.le) (sq_nonneg (m + b)),
    mul_nonneg (mul_nonneg hπ.le hq.le) (sub_nonneg.mpr hyhi),
    mul_nonneg hπ.le (sub_nonneg.mpr hylo),
    mul_nonneg hπ.le (neg_nonneg.mpr hmb)]

/-- The clipped quadratic changes by its linear term up to a constant; used by
`exists_abs_qPochhammerGrowth_add_sub_le`. -/
private lemma qPochhammerGrowth_shift_real (t b m : ℝ) (ht : 0 < t) :
    |(π * min (m + b) 0 ^ 2 / t - π * min (m + b) 0) -
      (π * min m 0 ^ 2 / t - π * min m 0) - 2 * π * b * min m 0 / t| ≤
      π * b ^ 2 / t + π * |b| := by
  have hπ : 0 < π := Real.pi_pos
  have hq : 0 < t⁻¹ := inv_pos.mpr ht
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  by_cases hm : m ≤ 0 <;> by_cases hmb : m + b ≤ 0
  · rw [min_eq_left hm, min_eq_left hmb]
    rw [abs_le]
    have hquad : 0 ≤ π * b ^ 2 * t⁻¹ :=
      mul_nonneg (mul_nonneg hπ.le (sq_nonneg b)) hq.le
    constructor <;> nlinarith [hquad,
      mul_nonneg hπ.le (sub_nonneg.mpr (le_abs_self b)),
      mul_nonneg hπ.le (sub_nonneg.mpr (neg_le_abs b))]
  · have hmb0 : 0 ≤ m + b := le_of_not_ge hmb
    rw [min_eq_left hm, min_eq_right hmb0]
    exact qPochhammerGrowth_shift_cross_up t b m ht hm hmb0
  · have hm0 : 0 ≤ m := le_of_not_ge hm
    rw [min_eq_right hm0, min_eq_left hmb]
    exact qPochhammerGrowth_shift_cross_down t b m ht hm0 hmb
  · have hm0 : 0 ≤ m := le_of_not_ge hm
    have hmb0 : 0 ≤ m + b := le_of_not_ge hmb
    rw [min_eq_right hm0, min_eq_right hmb0]
    simpa using add_nonneg
      (mul_nonneg (mul_nonneg hπ.le (sq_nonneg b)) hq.le)
      (mul_nonneg hπ.le (abs_nonneg b))

/-- `Γ_τ(u) ≥ 0` for `Im τ > 0`. -/
theorem qPochhammerGrowth_nonneg (τ u : ℂ) (hτ : 0 < τ.im) : 0 ≤ qPochhammerGrowth u τ := by
  dsimp [qPochhammerGrowth]
  have hm : min u.im 0 ≤ 0 := min_le_right _ _
  have hterm : 0 ≤ π * min u.im 0 ^ 2 / τ.im := by positivity
  nlinarith [Real.pi_pos]

/-- On a horizontal strip `|Im u| ≤ M`, `Γ_τ(u) ≤ π M²/Im τ + π M`. -/
theorem qPochhammerGrowth_le_of_abs_im_le (τ u : ℂ) (hτ : 0 < τ.im) {M : ℝ}
    (hu : |u.im| ≤ M) : qPochhammerGrowth u τ ≤ π * M ^ 2 / τ.im + π * M := by
  let v := min u.im 0
  have hM : 0 ≤ M := (abs_nonneg _).trans hu
  have hvlo : -M ≤ v := by
    dsimp [v]
    apply le_min
    · linarith [(abs_le.mp hu).1]
    · linarith
  have hvhi : v ≤ 0 := min_le_right _ _
  have hsq : v ^ 2 ≤ M ^ 2 := by nlinarith
  have hterm : π * v ^ 2 / τ.im ≤ π * M ^ 2 / τ.im := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsq Real.pi_pos.le) hτ.le
  dsimp [qPochhammerGrowth, v]
  nlinarith [Real.pi_pos]

/-- Shifting the argument by `a` changes the growth exponent by `2π Im a min(Im u, 0)/Im τ` up to
a bounded error. -/
theorem exists_abs_qPochhammerGrowth_add_sub_le (a τ : ℂ) (hτ : 0 < τ.im) :
    ∃ C, ∀ u : ℂ, |qPochhammerGrowth (u + a) τ - qPochhammerGrowth u τ -
      2 * π * a.im * min u.im 0 / τ.im| ≤ C := by
  refine ⟨π * a.im ^ 2 / τ.im + π * |a.im|, ?_⟩
  intro u
  simpa only [qPochhammerGrowth, Complex.add_im] using
    qPochhammerGrowth_shift_real τ.im a.im u.im hτ

/-! ### Bounds for `ϖ`

The upper bound holds everywhere; the lower bound away from the zeros `k - jτ`. -/

/-- A uniform upper bound in the upper half plane, used by both Gaussian product bounds. -/
private lemma norm_qPochhammer_le_of_nonneg (τ : ℂ) (hτ : 0 < τ.im)
    (u : ℂ) (hu : 0 ≤ u.im) :
    ‖qPochhammer u τ‖ ≤ Real.exp (1 / (1 - Real.exp (-2 * π * τ.im))) := by
  have hden : 0 < 1 - Real.exp (-2 * π * τ.im) := by
    have hlt : Real.exp (-2 * π * τ.im) < 1 :=
      Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
    linarith
  have hfactor : Real.exp (-2 * π * u.im) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
  have harg : Real.exp (-2 * π * u.im) / (1 - Real.exp (-2 * π * τ.im)) ≤
      1 / (1 - Real.exp (-2 * π * τ.im)) := by
    exact div_le_div_of_nonneg_right hfactor hden.le
  have hnorm : ‖qPochhammer u τ‖ ≤ ‖qPochhammer u τ - 1‖ + 1 := by
    calc
      ‖qPochhammer u τ‖ = ‖(qPochhammer u τ - 1) + 1‖ := by
        congr 1
        abel
      _ ≤ ‖qPochhammer u τ - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = _ := by simp
  have herror := norm_qPochhammer_sub_one_le u τ hτ
  have hexp := Real.exp_le_exp.mpr harg
  linarith

/-- For `Im τ > 0`, `‖ϖ(u,τ)‖ ≤ C exp(Γ_τ(u))` for every `u`. -/
theorem exists_norm_qPochhammer_le_exp (τ : ℂ) (hτ : 0 < τ.im) :
    ∃ C, ∀ u : ℂ, ‖qPochhammer u τ‖ ≤ C * Real.exp (qPochhammerGrowth u τ) := by
  obtain ⟨c₀, hc₀, hbelow⟩ :=
    exists_pos_le_norm_qPochhammer_of_le_im τ hτ τ.im hτ
  obtain ⟨Cθ, habove⟩ := exists_norm_qTheta_le_exp τ hτ
  let M := Real.exp (1 / (1 - Real.exp (-2 * π * τ.im)))
  refine ⟨max M (Cθ / c₀), ?_⟩
  intro u
  by_cases hu : 0 ≤ u.im
  · rw [qPochhammerGrowth_of_nonneg τ hu, Real.exp_zero, mul_one]
    exact (norm_qPochhammer_le_of_nonneg τ hτ u hu).trans (le_max_left _ _)
  · have hu0 : u.im ≤ 0 := le_of_not_ge hu
    have hheight : τ.im ≤ (τ - u).im := by simp [Complex.sub_im]; linarith
    have hprod : ‖qTheta u τ‖ = ‖qPochhammer u τ‖ * ‖qPochhammer (τ - u) τ‖ :=
      by simp [qTheta]
    have hmul : ‖qPochhammer u τ‖ * c₀ ≤
        Cθ * Real.exp (qThetaGrowth u τ) := by
      calc
        _ ≤ ‖qPochhammer u τ‖ * ‖qPochhammer (τ - u) τ‖ :=
          mul_le_mul_of_nonneg_left (hbelow _ hheight) (norm_nonneg _)
        _ = ‖qTheta u τ‖ := hprod.symm
        _ ≤ _ := habove u
    have hdiv : ‖qPochhammer u τ‖ ≤
        (Cθ / c₀) * Real.exp (qThetaGrowth u τ) := by
      rw [div_mul_eq_mul_div]
      exact (le_div_iff₀ hc₀).mpr (by simpa [mul_comm] using hmul)
    rw [qPochhammerGrowth_of_nonpos τ hu0]
    exact hdiv.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.exp_pos _).le)

/-- Below half the period height, distance from the product zeros gives distance from the
entire theta lattice; used by `exists_exp_le_norm_qPochhammer`. -/
private lemma qPochhammer_dist_theta_lattice (τ : ℂ) (hτ : 0 < τ.im)
    (δ : ℝ) (u : ℂ) (hu : u.im ≤ τ.im / 2)
    (hdist : ∀ (k : ℤ) (j : ℕ), δ ≤ ‖u - (k - j * τ)‖) :
    ∀ m n : ℤ, min δ (τ.im / 2) ≤ ‖u - (m + n * τ)‖ := by
  intro m n
  by_cases hn : n ≤ 0
  · cases n with
    | ofNat j =>
      have hj : j = 0 := by
        have hjle : (j : ℤ) ≤ 0 := by simpa only [Int.ofNat_eq_natCast] using hn
        exact (Int.ofNat_le.mp hjle).antisymm (Nat.zero_le j)
      subst j
      exact (min_le_left _ _).trans (by simpa using hdist m 0)
    | negSucc j =>
      calc
        min δ (τ.im / 2) ≤ δ := min_le_left _ _
        _ ≤ ‖u - (m + Int.negSucc j * τ)‖ := by
          simpa only [Int.cast_negSucc, sub_eq_add_neg, neg_mul] using hdist m (j + 1)
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have him : (u - ((m : ℂ) + (n : ℂ) * τ)).im = u.im - (n : ℝ) * τ.im := by
      simp [Complex.sub_im, Complex.add_im, Complex.mul_im]
    have hsep : (u - ((m : ℂ) + (n : ℂ) * τ)).im ≤ -τ.im / 2 := by
      rw [him]
      nlinarith [mul_nonneg (sub_nonneg.mpr hn1) hτ.le]
    have habs : τ.im / 2 ≤ |(u - ((m : ℂ) + (n : ℂ) * τ)).im| := by
      linarith [neg_le_abs (u - ((m : ℂ) + (n : ℂ) * τ)).im]
    exact (min_le_right _ _).trans (habs.trans (Complex.abs_im_le_norm _))

/-- The theta norm is bounded by the q-product norm times the upper-half-plane constant;
used by `norm_qPochhammer_lower_of_le_half`. -/
private lemma qTheta_lower_le_qPochhammer_mul_upper (τ : ℂ) (hτ : 0 < τ.im)
    (δ cθ : ℝ)
    (hθ : ∀ u : ℂ, (∀ m n : ℤ, min δ (τ.im / 2) ≤ ‖u - (m + n * τ)‖) →
      cθ * Real.exp (qThetaGrowth u τ) ≤ ‖qTheta u τ‖)
    (u : ℂ) (hu : u.im ≤ τ.im / 2)
    (hdist : ∀ (k : ℤ) (j : ℕ), δ ≤ ‖u - (k - j * τ)‖) :
    cθ * Real.exp (qThetaGrowth u τ) ≤
      ‖qPochhammer u τ‖ * Real.exp (1 / (1 - Real.exp (-2 * π * τ.im))) := by
  have hheight : 0 ≤ (τ - u).im := by simp [Complex.sub_im]; linarith
  have hden := norm_qPochhammer_le_of_nonneg τ hτ (τ - u) hheight
  calc
    _ ≤ ‖qTheta u τ‖ := hθ u (qPochhammer_dist_theta_lattice τ hτ δ u hu hdist)
    _ = ‖qPochhammer u τ‖ * ‖qPochhammer (τ - u) τ‖ := by simp [qTheta]
    _ ≤ _ := mul_le_mul_of_nonneg_left hden (norm_nonneg _)

/-- The theta lower bound gives the q-product lower bound below half the period height;
used by `exists_exp_le_norm_qPochhammer`. -/
private lemma norm_qPochhammer_lower_of_le_half (τ : ℂ) (hτ : 0 < τ.im)
    (δ cθ : ℝ) (hcθ : 0 < cθ)
    (hθ : ∀ u : ℂ, (∀ m n : ℤ, min δ (τ.im / 2) ≤ ‖u - (m + n * τ)‖) →
      cθ * Real.exp (qThetaGrowth u τ) ≤ ‖qTheta u τ‖)
    (u : ℂ) (hu : u.im ≤ τ.im / 2)
    (hdist : ∀ (k : ℤ) (j : ℕ), δ ≤ ‖u - (k - j * τ)‖) :
    (cθ / (Real.exp (1 / (1 - Real.exp (-2 * π * τ.im))) *
      Real.exp (π * τ.im / 4))) * Real.exp (qPochhammerGrowth u τ) ≤
      ‖qPochhammer u τ‖ := by
  let M := Real.exp (1 / (1 - Real.exp (-2 * π * τ.im)))
  let E := Real.exp (π * τ.im / 4)
  have hM : 0 < M := Real.exp_pos _
  have hE : 0 < E := Real.exp_pos _
  have hmul : cθ * Real.exp (qThetaGrowth u τ) ≤ ‖qPochhammer u τ‖ * M :=
    qTheta_lower_le_qPochhammer_mul_upper τ hτ δ cθ hθ u hu hdist
  have hdiv : cθ * Real.exp (qThetaGrowth u τ) / M ≤ ‖qPochhammer u τ‖ :=
    (div_le_iff₀ hM).mpr (by simpa [mul_comm] using hmul)
  have hgrowth : Real.exp (qPochhammerGrowth u τ) ≤
      Real.exp (qThetaGrowth u τ) * E := by
    calc
      _ ≤ Real.exp (qThetaGrowth u τ + π * τ.im / 4) :=
        Real.exp_le_exp.mpr (qPochhammerGrowth_le_qThetaGrowth_add τ u hτ)
      _ = _ := Real.exp_add _ _
  have hcoeff : 0 ≤ cθ / (M * E) := (div_pos hcθ (mul_pos hM hE)).le
  change (cθ / (M * E)) * Real.exp (qPochhammerGrowth u τ) ≤ _
  calc
    _ ≤ (cθ / (M * E)) * (Real.exp (qThetaGrowth u τ) * E) :=
      mul_le_mul_of_nonneg_left hgrowth hcoeff
    _ = cθ * Real.exp (qThetaGrowth u τ) / M := by
      field_simp
    _ ≤ _ := hdiv

/-- For `Im τ > 0` and `δ > 0`, `‖ϖ(u,τ)‖ ≥ c exp(Γ_τ(u))` with `c > 0` at distance at least `δ`
from the zeros `k - jτ` of `ϖ(·,τ)`. -/
theorem exists_exp_le_norm_qPochhammer (τ : ℂ) (hτ : 0 < τ.im) (δ : ℝ) (hδ : 0 < δ) :
    ∃ c > 0, ∀ u : ℂ, (∀ (k : ℤ) (j : ℕ), δ ≤ ‖u - (k - j * τ)‖) →
      c * Real.exp (qPochhammerGrowth u τ) ≤ ‖qPochhammer u τ‖ := by
  let M := Real.exp (1 / (1 - Real.exp (-2 * π * τ.im)))
  let E := Real.exp (π * τ.im / 4)
  have hhalf : 0 < τ.im / 2 := by positivity
  obtain ⟨c₀, hc₀, hbelow⟩ :=
    exists_pos_le_norm_qPochhammer_of_le_im τ hτ (τ.im / 2) hhalf
  obtain ⟨cθ, hcθ, hθ⟩ :=
    exists_exp_le_norm_qTheta τ hτ (min δ (τ.im / 2)) (lt_min hδ hhalf)
  have hM : 0 < M := Real.exp_pos _
  have hE : 0 < E := Real.exp_pos _
  refine ⟨min c₀ (cθ / (M * E)), lt_min hc₀ (div_pos hcθ (mul_pos hM hE)), ?_⟩
  intro u hdist
  by_cases hu : τ.im / 2 ≤ u.im
  · have hu0 : 0 ≤ u.im := by linarith
    rw [qPochhammerGrowth_of_nonneg τ hu0, Real.exp_zero, mul_one]
    exact (min_le_left _ _).trans (hbelow u hu)
  · have hlow : u.im ≤ τ.im / 2 := le_of_not_ge hu
    exact (mul_le_mul_of_nonneg_right (min_le_right _ _)
      (Real.exp_pos _).le).trans
      (norm_qPochhammer_lower_of_le_half τ hτ δ cθ hcθ hθ u hlow hdist)

/-! ### Quotients of two q-products

Quotients `ϖ(x,τ₁)/ϖ(y,τ₂)` with possibly different periods, as in the modular q-product
`Φ_{γ,n,0}`: away from the zeros of the denominator the two Gaussian bounds combine, and where
both arguments lie below half the height of their periods the quotient is bounded as the
corresponding theta quotient, the two reflected products `ϖ(τ₁-x,τ₁)` and `ϖ(τ₂-y,τ₂)` being
bounded above and below there. The estimates apply with either period in the numerator. -/

/-- Division preserves a norm comparison, including when its denominator vanishes. -/
private lemma norm_div_le_of_norm_le_mul (a b : ℂ) (T : ℝ)
    (hT : 0 ≤ T) (hab : ‖a‖ ≤ T * ‖b‖) : ‖a / b‖ ≤ T := by
  by_cases hb : b = 0
  · simpa [hb] using hT
  · rw [norm_div]
    exact (div_le_iff₀ (norm_pos_iff.mpr hb)).mpr hab

/-- A Gaussian upper bound divided by a positive Gaussian lower bound. -/
private lemma norm_div_le_exp (a b : ℂ) (X Y A c : ℝ)
    (hA : 0 ≤ A) (hc : 0 < c)
    (ha : ‖a‖ ≤ A * Real.exp X) (hb : c * Real.exp Y ≤ ‖b‖) :
    ‖a / b‖ ≤ (A / c) * Real.exp (X - Y) := by
  have hbpos : 0 < ‖b‖ := (mul_pos hc (Real.exp_pos _)).trans_le hb
  rw [norm_div]
  apply (div_le_iff₀ hbpos).mpr
  calc
    ‖a‖ ≤ A * Real.exp X := ha
    _ = ((A / c) * Real.exp (X - Y)) * (c * Real.exp Y) := by
      have hexp : Real.exp (X - Y) * Real.exp Y = Real.exp X := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [← hexp]
      field_simp [ne_of_gt hc]
    _ ≤ ((A / c) * Real.exp (X - Y)) * ‖b‖ :=
      mul_le_mul_of_nonneg_left hb (mul_nonneg (div_nonneg hA hc.le)
        (Real.exp_nonneg _))

/-- The quotient of two q-products is a theta quotient times its reflected factors. -/
private lemma qPochhammer_div_eq_theta_div_mul (x y τ₁ τ₂ : ℂ)
    (hR : qPochhammer (τ₁ - x) τ₁ ≠ 0)
    (hS : qPochhammer (τ₂ - y) τ₂ ≠ 0) :
    qPochhammer x τ₁ / qPochhammer y τ₂ =
      (qTheta x τ₁ / qTheta y τ₂) *
        (qPochhammer (τ₂ - y) τ₂ / qPochhammer (τ₁ - x) τ₁) := by
  by_cases hB : qPochhammer y τ₂ = 0
  · simp [hB, qTheta]
  · simp only [qTheta]
    field_simp [hB, hR, hS]

/-- Above half the period height, a q-product has fixed positive lower and upper bounds. -/
private lemma exists_qPochhammer_half_bounds (τ : ℂ) (hτ : 0 < τ.im) :
    ∃ c > 0, ∃ C > 0, ∀ v : ℂ, τ.im / 2 ≤ v.im →
      c ≤ ‖qPochhammer v τ‖ ∧ ‖qPochhammer v τ‖ ≤ C := by
  obtain ⟨c, hc, hlo⟩ :=
    exists_pos_le_norm_qPochhammer_of_le_im τ hτ (τ.im / 2) (by linarith)
  obtain ⟨C, hhi⟩ := exists_norm_qPochhammer_le_exp τ hτ
  refine ⟨c, hc, max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro v hv
  refine ⟨hlo v hv, ?_⟩
  have hΓ : qPochhammerGrowth v τ = 0 :=
    qPochhammerGrowth_of_nonneg τ (by linarith)
  have hC : ‖qPochhammer v τ‖ ≤ C := by simpa [hΓ] using hhi v
  exact hC.trans (le_max_left _ _)

/-- Reflected-factor bounds turn a theta comparison into a q-product comparison. -/
private lemma norm_qPochhammer_div_le_of_theta_bound (x y τ₁ τ₂ : ℂ)
    (c C K : ℝ) (hc : 0 < c) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hR : c ≤ ‖qPochhammer (τ₁ - x) τ₁‖)
    (hSpos : 0 < ‖qPochhammer (τ₂ - y) τ₂‖)
    (hS : ‖qPochhammer (τ₂ - y) τ₂‖ ≤ C)
    (hθ : ‖qTheta x τ₁‖ ≤
      K * Real.exp (qThetaGrowth x τ₁ - qThetaGrowth y τ₂) * ‖qTheta y τ₂‖) :
    ‖qPochhammer x τ₁ / qPochhammer y τ₂‖ ≤
      (C / c) * K * Real.exp (qThetaGrowth x τ₁ - qThetaGrowth y τ₂) := by
  have hRne := norm_pos_iff.mp (hc.trans_le hR)
  have hSne := norm_pos_iff.mp hSpos
  have hθratio := norm_div_le_of_norm_le_mul _ _ _
    (mul_nonneg hK (Real.exp_nonneg _)) hθ
  have hreflect : ‖qPochhammer (τ₂ - y) τ₂ / qPochhammer (τ₁ - x) τ₁‖ ≤
      C / c := by
    have h := norm_div_le_exp (qPochhammer (τ₂ - y) τ₂)
      (qPochhammer (τ₁ - x) τ₁) 0 0 C c hC hc
      (by simpa using hS) (by simpa using hR)
    simpa using h
  calc
    ‖qPochhammer x τ₁ / qPochhammer y τ₂‖ =
        ‖qTheta x τ₁ / qTheta y τ₂‖ *
          ‖qPochhammer (τ₂ - y) τ₂ / qPochhammer (τ₁ - x) τ₁‖ := by
            rw [qPochhammer_div_eq_theta_div_mul x y τ₁ τ₂ hRne hSne, norm_mul]
    _ ≤ (K * Real.exp (qThetaGrowth x τ₁ - qThetaGrowth y τ₂)) * (C / c) :=
      mul_le_mul hθratio hreflect (norm_nonneg _)
        (mul_nonneg hK (Real.exp_nonneg _))
    _ = _ := by ring

/-- The difference of theta exponents is bounded by that of q-product exponents. -/
private lemma qThetaGrowth_sub_le_qPochhammerGrowth_sub_add (x y τ₁ τ₂ : ℂ)
    (h₁ : 0 < τ₁.im) (h₂ : 0 < τ₂.im) (hx : x.im ≤ τ₁.im) :
    qThetaGrowth x τ₁ - qThetaGrowth y τ₂ ≤
      qPochhammerGrowth x τ₁ - qPochhammerGrowth y τ₂ + π * τ₂.im / 4 := by
  have hθx := qThetaGrowth_le_qPochhammerGrowth h₁ hx
  have hpy := qPochhammerGrowth_le_qThetaGrowth_add τ₂ y h₂
  linarith

/-- For `τ₁, τ₂ ∈ ℍ` and `δ > 0`, at distance at least `δ` from the zeros `k - jτ₂` of the
denominator, `‖ϖ(x,τ₁)/ϖ(y,τ₂)‖ ≤ C exp(Γ_{τ₁}(x) - Γ_{τ₂}(y))`. -/
theorem exists_norm_qPochhammer_div_le_exp (τ₁ τ₂ : ℂ) (h₁ : 0 < τ₁.im) (h₂ : 0 < τ₂.im)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C, ∀ x y : ℂ, (∀ (k : ℤ) (j : ℕ), δ ≤ ‖y - (k - j * τ₂)‖) →
      ‖qPochhammer x τ₁ / qPochhammer y τ₂‖ ≤
        C * Real.exp (qPochhammerGrowth x τ₁ - qPochhammerGrowth y τ₂) := by
  obtain ⟨A, hA⟩ := exists_norm_qPochhammer_le_exp τ₁ h₁
  obtain ⟨c, hc, hlo⟩ := exists_exp_le_norm_qPochhammer τ₂ h₂ δ hδ
  refine ⟨max A 1 / c, ?_⟩
  intro x y hdist
  have hApos : 0 ≤ max A 1 := (le_max_right _ _).trans' zero_le_one
  have hupper : ‖qPochhammer x τ₁‖ ≤
      max A 1 * Real.exp (qPochhammerGrowth x τ₁) :=
    (hA x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.exp_nonneg _))
  exact norm_div_le_exp _ _ _ _ _ _ hApos hc hupper (hlo y hdist)

/-- For `τ₁, τ₂ ∈ ℍ`, where `Im x ≤ Im τ₁/2` and `Im y ≤ Im τ₂/2`, a comparison
`‖θ(x,τ₁)‖ ≤ K exp(Γ̃_{τ₁}(x) - Γ̃_{τ₂}(y)) ‖θ(y,τ₂)‖` of theta products, with
`Γ̃ = qThetaGrowth`, gives `‖ϖ(x,τ₁)/ϖ(y,τ₂)‖ ≤ C K exp(Γ_{τ₁}(x) - Γ_{τ₂}(y))`, with `C` depending
only on the periods. -/
theorem exists_norm_qPochhammer_div_le_of_norm_qTheta_le (τ₁ τ₂ : ℂ) (h₁ : 0 < τ₁.im)
    (h₂ : 0 < τ₂.im) :
    ∃ C, ∀ (K : ℝ) (x y : ℂ), 0 ≤ K → x.im ≤ τ₁.im / 2 → y.im ≤ τ₂.im / 2 →
      ‖qTheta x τ₁‖ ≤ K * Real.exp (qThetaGrowth x τ₁ - qThetaGrowth y τ₂) * ‖qTheta y τ₂‖ →
      ‖qPochhammer x τ₁ / qPochhammer y τ₂‖ ≤
        C * K * Real.exp (qPochhammerGrowth x τ₁ - qPochhammerGrowth y τ₂) := by
  obtain ⟨c₁, hc₁, _, _, h₁bounds⟩ := exists_qPochhammer_half_bounds τ₁ h₁
  obtain ⟨c₂, hc₂, C₂, hC₂, h₂bounds⟩ := exists_qPochhammer_half_bounds τ₂ h₂
  refine ⟨(C₂ / c₁) * Real.exp (π * τ₂.im / 4), ?_⟩
  intro K x y hK hx hy hθ
  have hRheight : τ₁.im / 2 ≤ (τ₁ - x).im := by simp [Complex.sub_im]; linarith
  have hSheight : τ₂.im / 2 ≤ (τ₂ - y).im := by simp [Complex.sub_im]; linarith
  have hR := (h₁bounds (τ₁ - x) hRheight).1
  have hS := (h₂bounds (τ₂ - y) hSheight).2
  have hSpos : 0 < ‖qPochhammer (τ₂ - y) τ₂‖ :=
    hc₂.trans_le (h₂bounds (τ₂ - y) hSheight).1
  have hbound := norm_qPochhammer_div_le_of_theta_bound x y τ₁ τ₂
    c₁ C₂ K hc₁ hC₂.le hK hR hSpos hS hθ
  have hD := qThetaGrowth_sub_le_qPochhammerGrowth_sub_add x y τ₁ τ₂
    h₁ h₂ (by linarith)
  calc
    ‖qPochhammer x τ₁ / qPochhammer y τ₂‖ ≤
        (C₂ / c₁) * K * Real.exp (qThetaGrowth x τ₁ - qThetaGrowth y τ₂) := hbound
    _ ≤ (C₂ / c₁) * K *
        Real.exp (qPochhammerGrowth x τ₁ - qPochhammerGrowth y τ₂ +
          π * τ₂.im / 4) := by
      gcongr
    _ = ((C₂ / c₁) * Real.exp (π * τ₂.im / 4)) * K *
        Real.exp (qPochhammerGrowth x τ₁ - qPochhammerGrowth y τ₂) := by
      rw [Real.exp_add]
      ring

end SIC
