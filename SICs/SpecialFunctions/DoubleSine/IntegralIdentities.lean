/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.DoubleSine.RealIntegral
import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Integral Identities for the Real Double Sine

Frullani and cosine integral evaluations, and `S₂(1;τ,1)=√τ`.

This file evaluates the scalar integrals that supply the period laws in
[AFK25, Appendix D, equations (D.5), `eq:doubleSineQuasiPeriodicity1`, and (D.6),
`eq:doubleSineQuasiPeriodicity2`], and the boundary value `S₂(1; τ, 1) = √τ` used in
[AFK25, Section 8.2]. The real kernel and its convergence are provided by
`SICs.SpecialFunctions.DoubleSine.RealIntegral`; the resulting function identities are proved in
`SICs.SpecialFunctions.DoubleSine.Identities`.

The quasiperiodicity integral is split into a boundary term and a parameter-dependent correction.
A scale-two Frullani difference evaluates the boundary term as `log 2`. Expanding `1/sinh s`
into a geometric series evaluates the correction by ordinary Frullani integrals; the resulting
sum is the logarithm of the Weierstrass cosine product. A second use of the same Frullani
auxiliary gives the boundary-period value. Integrability justifies each splitting and interchange.
-/

noncomputable section

open Real MeasureTheory Set Asymptotics Filter

namespace SIC

/-! ### Integral identity for quasiperiodicity

The analytic core of the double sine quasiperiodicity is the identity

$$I(\alpha) = \int_0^\infty \left(\frac{1}{s^2} - \frac{\cosh(\alpha s)}{s\,\sinh s}\right) ds
= \log\bigl(2\cos(\pi\alpha/2)\bigr)$$

for $|\alpha| < 1$.

The proof splits the integrand as
$I(\alpha) = I(0) + \int_0^\infty (1-\cosh(\alpha s))/(s\sinh s)\,ds$ and evaluates each piece
separately:

1. **Boundary value** (`integral_inv_sq_sub_inv_s_sinh`): $I(0) = \log 2$, by expressing the
   integrand as a scale-two Frullani difference.
2. **Shifted kernel** (`integral_one_sub_cosh_div_s_sinh`): the second piece equals
   $\log\cos(\pi\alpha/2)$, proved via geometric-series expansion, Frullani integrals,
   and the Weierstrass cosine product from `Real.tendsto_euler_sin_prod`.

Two integrability results (`integrableOn_inv_sq_sub_inv_s_sinh`,
`integrableOn_one_sub_cosh_div_s_sinh`) justify the split. -/

/-! #### Geometric series for `1/sinh`

Expanding the reciprocal hyperbolic sine into decaying exponentials turns the shifted-kernel
integral into a summable family of elementary Frullani integrals. -/

/-- Geometric series representation: `1/sinh(s) = 2 Σ_{n≥0} e^{-(2n+1)s}` for `s > 0`.

This follows from the geometric series `Σ r^n = 1/(1-r)` with `r = e^{-2s}`,
multiplied by `2 e^{-s}`. -/
lemma hasSum_exp_inv_sinh {s : ℝ} (hs : 0 < s) :
    HasSum (fun n : ℕ => 2 * rexp (-(2 * ↑n + 1) * s)) (1 / sinh s) := by
  have hr : ‖rexp (-2 * s)‖ < 1 := by
    rw [Real.norm_of_nonneg (le_of_lt (exp_pos _)), exp_lt_one_iff]; linarith
  have hgeo := hasSum_geometric_of_norm_lt_one hr
  have h2 := hgeo.mul_left (2 * rexp (-s))
  have hfun : ∀ n : ℕ, 2 * rexp (-s) * rexp (-2 * s) ^ n =
      2 * rexp (-(2 * ↑n + 1) * s) := by
    intro n; rw [← Real.exp_nat_mul]; simp only [mul_comm, mul_assoc, mul_left_comm]
    congr 1; rw [← exp_add]; congr 1; ring
  simp_rw [hfun] at h2
  suffices h : 2 * rexp (-s) * (1 - rexp (-2 * s))⁻¹ = 1 / sinh s from h ▸ h2
  have hsh : sinh s ≠ 0 := ne_of_gt (sinh_pos_iff.mpr hs)
  have h1 : (1 : ℝ) - rexp (-2 * s) ≠ 0 := by
    have := (exp_lt_one_iff (x := -2 * s)).mpr (by linarith); linarith
  have key : 2 * rexp (-s) * sinh s = 1 - rexp (-2 * s) := by
    rw [sinh_eq]
    have h_prod1 : rexp (-s) * rexp s = 1 := by rw [← exp_add]; simp
    have h_prod2 : rexp (-s) * rexp (-s) = rexp (-2 * s) := by rw [← exp_add]; congr 1; ring
    nlinarith
  have h1' : (1 : ℝ) - rexp (-(2 * s)) ≠ 0 := by rwa [show -(2 * s) = -2 * s from by ring]
  field_simp
  rw [show -(2 * s) = -2 * s from by ring]
  linarith

/-! #### Integrability results

The boundary term and the parameter-dependent correction are proved integrable separately.  This
justifies splitting the quasiperiodicity integral before either term is evaluated. -/

/-- Integrability of `1/s² − 1/(s sinh s)` on `(0, ∞)`.

Near `s = 0`: `(sinh s − s)/(s² sinh s) → 1/6` (bounded). At `s → ∞`: `O(1/s²)` (integrable).
The proof splits at `s = 1` via `IntegrableOn.union`. -/
lemma integrableOn_inv_sq_sub_inv_s_sinh :
    IntegrableOn (fun s => 1 / s ^ 2 - 1 / (s * sinh s)) (Ioi (0 : ℝ)) := by
  -- Key identity: 1/s² - 1/(s sinh s) = -doubleSineKernel(1/2, 1, 1, s)
  have hint : IntegrableOn (doubleSineKernel (1/2) 1 1) (Ioi (0 : ℝ)) :=
    doubleSineKernel_integrableOn_Ioi _ _ _ one_pos one_pos (by norm_num) (by norm_num)
  exact hint.neg.congr ((ae_restrict_mem measurableSet_Ioi).mono (fun s hs => by
    simp only [mem_Ioi] at hs; unfold doubleSineKernel; simp only [Pi.neg_apply, one_mul, mul_one]
    have hs0 : s ≠ 0 := ne_of_gt hs
    have hsh : sinh s ≠ 0 := ne_of_gt (sinh_pos_iff.mpr hs)
    norm_num; field_simp; ring))

/-- Integrability of `(1 − cosh(αs))/(s sinh s)` on `(0, ∞)` for `|α| < 1`.

Near `s = 0`: `−α² s / (2 sinh s) → −α²/2` (bounded). At `s → ∞`: `O(e^{(|α|−1)s}/s) → 0`
(exponentially decaying since `|α| < 1`). -/
lemma integrableOn_one_sub_cosh_div_s_sinh (α : ℝ) (hα : |α| < 1) :
    IntegrableOn (fun s => (1 - cosh (α * s)) / (s * sinh s)) (Ioi (0 : ℝ)) := by
  -- Strategy: (1-cosh(αs))/(s sinh s) = (1/s²-cosh(αs)/(s sinh s)) - (1/s²-1/(s sinh s))
  -- Both pieces are integrable; the first from the kernel difference, the second from above.
  obtain ⟨hα_neg, hα_pos⟩ := abs_lt.mp hα
  set z := (1 - α) / 2 with hz_def
  have hz : 0 < z := by linarith
  have hzu : z < 2 := by linarith
  -- Both kernels K(z+1, 1, 1) and K(z, 1, 1) are integrable on (0, ∞)
  have hint1 : IntegrableOn (doubleSineKernel (z + 1) 1 1) (Ioi (0 : ℝ)) :=
    doubleSineKernel_integrableOn_Ioi _ _ _ one_pos one_pos (by linarith) (by linarith)
  have hint2 : IntegrableOn (doubleSineKernel z 1 1) (Ioi (0 : ℝ)) :=
    doubleSineKernel_integrableOn_Ioi _ _ _ one_pos one_pos hz (by linarith)
  -- Their difference = 2·(1/s² - cosh(αs)/(s sinh s)) by doubleSineKernel_shift_sub
  have h_diff : IntegrableOn
      (fun s => 2 * (1 / s ^ 2 - cosh (α * s) / (s * sinh s))) (Ioi (0 : ℝ)) := by
    exact (hint1.sub hint2).congr ((ae_restrict_mem measurableSet_Ioi).mono (fun s hs => by
      simp only [mem_Ioi] at hs
      simp only [Pi.sub_apply]
      rw [doubleSineKernel_shift_sub z 1 1 s one_pos one_pos hs]
      have hs0 : s ≠ 0 := ne_of_gt hs
      have hsh : sinh s ≠ 0 := ne_of_gt (sinh_pos_iff.mpr hs)
      have hsimp : (1 : ℝ) - 2 * ((1 - α) / 2) = α := by ring
      rw [hsimp, one_mul, mul_comm α s]; field_simp))
  -- 1/s² - cosh(αs)/(s sinh s) is integrable (divide by 2)
  have h_full : IntegrableOn
      (fun s => 1 / s ^ 2 - cosh (α * s) / (s * sinh s)) (Ioi (0 : ℝ)) := by
    have h2 : IntegrableOn (fun s => (2:ℝ)⁻¹ • (2 * (1 / s ^ 2 -
        cosh (α * s) / (s * sinh s)))) (Ioi (0 : ℝ)) := h_diff.smul (2:ℝ)⁻¹
    exact h2.congr (ae_of_all _ (fun s => by simp))
  -- (1-cosh(αs))/(s sinh s) = full integrand - boundary integrand
  exact (h_full.sub integrableOn_inv_sq_sub_inv_s_sinh).congr
    ((ae_restrict_mem measurableSet_Ioi).mono (fun s hs => by
      simp only [mem_Ioi, Pi.sub_apply] at hs ⊢
      have hs0 : s ≠ 0 := ne_of_gt hs
      have hsh : sinh s ≠ 0 := ne_of_gt (sinh_pos_iff.mpr hs)
      field_simp
      ring))

/-! #### Building blocks for the integral identities

Frullani formulas and the Euler sine product provide the scalar evaluations needed to identify
the two integrable pieces with logarithms. -/

/-- The exponential bound `1 − e^{−x} ≤ x`, used for the Frullani integrability. -/
lemma one_sub_exp_neg_le (x : ℝ) : 1 - rexp (-x) ≤ x := by
  linarith [one_sub_le_exp_neg x]

/-- Pointwise bound: `s⁻¹ |e^{−as} − e^{−bs}| ≤ |a−b| e^{−min(a,b)s}` for `s > 0`.
Proved by factoring the difference and using `one_sub_exp_neg_le`. -/
lemma frullani_exp_bound (a b s : ℝ) (hs : 0 < s) :
    s⁻¹ * |rexp (-(a * s)) - rexp (-(b * s))| ≤
    |a - b| * rexp (-(min a b * s)) := by
  rcases le_total a b with hab | hab
  · have h1 : 0 ≤ rexp (-(a * s)) - rexp (-(b * s)) :=
      sub_nonneg.mpr (exp_le_exp.mpr (by nlinarith))
    rw [abs_of_nonneg h1, min_eq_left hab,
        show |a - b| = b - a from by rw [abs_sub_comm, abs_of_nonneg (by linarith)]]
    rw [show rexp (-(a * s)) - rexp (-(b * s)) =
        rexp (-(a * s)) * (1 - rexp (-((b - a) * s))) from by
      rw [mul_sub, mul_one, ← exp_add]; congr 1; ring_nf]
    calc s⁻¹ * (rexp (-(a * s)) * (1 - rexp (-((b - a) * s))))
        ≤ s⁻¹ * (rexp (-(a * s)) * ((b - a) * s)) := by
          gcongr; exact one_sub_exp_neg_le _
      _ = (b - a) * rexp (-(a * s)) := by field_simp
  · have h1 : rexp (-(a * s)) - rexp (-(b * s)) ≤ 0 :=
      sub_nonpos.mpr (exp_le_exp.mpr (by nlinarith))
    rw [abs_of_nonpos h1, min_eq_right hab, abs_of_nonneg (by linarith : a - b ≥ 0)]
    rw [show -(rexp (-(a * s)) - rexp (-(b * s))) =
        rexp (-(b * s)) * (1 - rexp (-((a - b) * s))) from by
      rw [neg_sub, mul_sub, mul_one, ← exp_add]; congr 1; ring_nf]
    calc s⁻¹ * (rexp (-(b * s)) * (1 - rexp (-((a - b) * s))))
        ≤ s⁻¹ * (rexp (-(b * s)) * ((a - b) * s)) := by
          gcongr; exact one_sub_exp_neg_le _
      _ = (a - b) * rexp (-(b * s)) := by field_simp

/-- Integrability of the Frullani integrand `s⁻¹(e^{−as} − e^{−bs})` on `(0,∞)`.
Dominated by `|a−b| e^{−min(a,b)s}` via `frullani_exp_bound`. -/
lemma integrableOn_frullani_exp (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun s => s⁻¹ * (rexp (-(a * s)) - rexp (-(b * s))))
      (Ioi 0) volume := by
  have hmin : 0 < min a b := lt_min ha hb
  apply Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hmin).const_mul |a - b|)
  · apply AEStronglyMeasurable.restrict
    exact (measurable_inv.mul (measurable_exp.comp
      (measurable_const.mul measurable_id).neg |>.sub
      (measurable_exp.comp (measurable_const.mul measurable_id).neg))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    simp only [mem_Ioi] at hs
    calc ‖s⁻¹ * (rexp (-(a * s)) - rexp (-(b * s)))‖
        = s⁻¹ * |rexp (-(a * s)) - rexp (-(b * s))| := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr hs)]
      _ ≤ |a - b| * rexp (-(min a b * s)) := frullani_exp_bound a b s hs
      _ = |a - b| * rexp (-min a b * s) := by ring_nf

/-- **Frullani integral for the exponential function.**
`∫₀^∞ s⁻¹ (e^{-as} − e^{-bs}) ds = log(b/a)` for `a, b > 0`. -/
lemma frullani_exp (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∫ s in Ioi (0 : ℝ), s⁻¹ * (rexp (-(a * s)) - rexp (-(b * s))) =
    Real.log (b / a) := by
  have h := @Frullani.integral_Ioi_eq ℝ _ _ (fun s => rexp (-s)) a b 1 0 _
    ?_ ha hb ?_ ?_ ?_
  · simp only [smul_eq_mul, sub_zero, mul_one] at h; exact h
  · exact (continuous_exp.comp continuous_neg).continuousOn.locallyIntegrableOn
      measurableSet_Ioi
  · rw [show (1 : ℝ) = rexp (-0) from by simp]
    exact (continuous_exp.comp continuous_neg).continuousWithinAt
  · exact tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  · exact integrableOn_frullani_exp a b ha hb

/-- Each summand in the `J(α)` expansion integrates to `log(1 − α²/(2n+1)²)`.
The summand `s⁻¹(2e^{-(2n+1)s} − e^{-(2n+1−α)s} − e^{-(2n+1+α)s})`
splits into two Frullani integrals. -/
lemma integral_summand_J (α : ℝ) (hα : |α| < 1) (n : ℕ) :
    ∫ s in Ioi (0 : ℝ), s⁻¹ * (2 * rexp (-((2 * ↑n + 1) * s)) -
      rexp (-((2 * ↑n + 1 - α) * s)) - rexp (-((2 * ↑n + 1 + α) * s))) =
    Real.log (1 - α ^ 2 / (2 * ↑n + 1) ^ 2) := by
  have hn : (0 : ℝ) < 2 * ↑n + 1 := by positivity
  have hα_abs := abs_lt.mp hα
  have hna : 0 < 2 * (↑n : ℝ) + 1 - α := by linarith
  have hnb : 0 < 2 * (↑n : ℝ) + 1 + α := by linarith
  have intA : IntegrableOn
      (fun s => s⁻¹ * (rexp (-((2 * ↑n + 1) * s)) - rexp (-((2 * ↑n + 1 + α) * s))))
      (Ioi 0) := integrableOn_frullani_exp _ _ hn hnb
  have intB : IntegrableOn
      (fun s => s⁻¹ * (rexp (-((2 * ↑n + 1) * s)) - rexp (-((2 * ↑n + 1 - α) * s))))
      (Ioi 0) := integrableOn_frullani_exp _ _ hn hna
  have hsplit : ∀ s ∈ Ioi (0 : ℝ),
      s⁻¹ * (2 * rexp (-((2 * ↑n + 1) * s)) -
        rexp (-((2 * ↑n + 1 - α) * s)) - rexp (-((2 * ↑n + 1 + α) * s))) =
      s⁻¹ * (rexp (-((2 * ↑n + 1) * s)) - rexp (-((2 * ↑n + 1 + α) * s))) +
      s⁻¹ * (rexp (-((2 * ↑n + 1) * s)) - rexp (-((2 * ↑n + 1 - α) * s))) := by
    intro s _; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hsplit,
      integral_add intA intB,
      frullani_exp _ _ hn hnb, frullani_exp _ _ hn hna,
      ← Real.log_mul (by positivity) (by positivity)]
  congr 1; field_simp; ring

/-- **Weierstrass cosine product**: for `|α| < 1` with `α ≠ 0`,
`cos(πα/2) = lim_{N→∞} ∏_{m<N}(1 − α²/(2m+1)²)`.
Derived from `Real.tendsto_euler_sin_prod` by splitting even/odd factors
and using the double angle formula `sin(πα) = 2 sin(πα/2) cos(πα/2)`. -/
lemma tendsto_weierstrass_cos_prod (α : ℝ) (hα : α ≠ 0) (hα1 : |α| < 1) :
    Tendsto (fun N => ∏ m ∈ Finset.range N,
      (1 - α ^ 2 / (2 * (↑m : ℝ) + 1) ^ 2))
      atTop (nhds (cos (π * α / 2))) := by
  have hsin_ne : sin (π * α / 2) ≠ 0 := by
    rw [sin_ne_zero_iff]; intro n hn
    have hpi : (0 : ℝ) < π := pi_pos
    have hnd : α = 2 * (n : ℝ) := by nlinarith [mul_comm (n : ℝ) π]
    have h_abs_n : |(n : ℝ)| < 1 := by
      have : |2 * (n : ℝ)| < 1 := hnd ▸ hα1
      rw [abs_mul, show |(2 : ℝ)| = 2 from by norm_num] at this; linarith
    have : (n : ℤ) = 0 := by
      have : (n : ℤ) < 1 := by exact_mod_cast (abs_lt.mp h_abs_n).2
      have : -(1 : ℤ) < n := by exact_mod_cast (abs_lt.mp h_abs_n).1
      omega
    rw [this] at hnd; simp only [Int.cast_zero, mul_zero] at hnd; exact hα hnd
  have h2sin_ne : 2 * sin (π * α / 2) ≠ 0 := mul_ne_zero two_ne_zero hsin_ne
  set f : ℕ → ℝ := fun N =>
    ∏ m ∈ Finset.range N, (1 - α ^ 2 / (2 * (↑m : ℝ) + 1) ^ 2)
  set g : ℕ → ℝ := fun N =>
    2 * (π * (α / 2) * ∏ m ∈ Finset.range N,
      (1 - (α / 2) ^ 2 / ((↑m : ℝ) + 1) ^ 2))
  have hg : Tendsto g atTop (nhds (2 * sin (π * α / 2))) := by
    change Tendsto (fun N => 2 * (π * (α / 2) *
        ∏ m ∈ Finset.range N,
          (1 - (α / 2) ^ 2 / ((↑m : ℝ) + 1) ^ 2))) atTop
      (nhds (2 * sin (π * α / 2)))
    have euler_half := tendsto_euler_sin_prod (α / 2)
    rw [show sin (π * (α / 2)) = sin (π * α / 2) from by ring_nf] at euler_half
    exact Tendsto.const_mul 2 euler_half
  have fg_eq : ∀ N, f N * g N =
      π * α * ∏ j ∈ Finset.range (2 * N),
        (1 - α ^ 2 / ((↑j : ℝ) + 1) ^ 2) := by
    intro N
    change (∏ m ∈ Finset.range N,
        (1 - α ^ 2 / (2 * (↑m : ℝ) + 1) ^ 2)) *
      (2 * (π * (α / 2) *
        ∏ m ∈ Finset.range N,
          (1 - (α / 2) ^ 2 / ((↑m : ℝ) + 1) ^ 2))) =
      π * α * ∏ j ∈ Finset.range (2 * N),
        (1 - α ^ 2 / ((↑j : ℝ) + 1) ^ 2)
    have split0 : ∀ (h : ℕ → ℝ), ∏ j ∈ Finset.range (2 * N), h j =
        (∏ m ∈ Finset.range N, h (2 * m)) *
        (∏ m ∈ Finset.range N, h (2 * m + 1)) := by
      intro h; induction N with
      | zero => simp
      | succ n ih =>
        rw [show 2 * (n + 1) = (2 * n + 1) + 1 from by omega]
        rw [Finset.prod_range_succ, Finset.prod_range_succ,
            Finset.prod_range_succ, Finset.prod_range_succ, ih]; ring
    rw [split0]
    simp_rw [show ∀ m : ℕ,
        (1 - α ^ 2 / (((2 * m : ℕ) : ℝ) + 1) ^ 2) =
        (1 - α ^ 2 / (2 * (↑m : ℝ) + 1) ^ 2) from
      fun m => by congr 1; congr 1; push_cast; ring]
    simp_rw [show ∀ m : ℕ,
        (1 - α ^ 2 / (((2 * m + 1 : ℕ) : ℝ) + 1) ^ 2) =
        (1 - (α / 2) ^ 2 / ((↑m : ℝ) + 1) ^ 2) from fun m => by
      have : (↑m : ℝ) + 1 ≠ 0 := by positivity
      have : ((2 * m + 1 : ℕ) : ℝ) + 1 ≠ 0 := by positivity
      field_simp; push_cast; ring]
    ring
  have hfg : Tendsto (fun N => f N * g N) atTop (nhds (sin (π * α))) := by
    simp_rw [fg_eq]
    exact (tendsto_euler_sin_prod α).comp
      (tendsto_atTop_atTop_of_monotone
        (fun a b h => by omega) (fun b => ⟨b, by omega⟩))
  have hdouble : sin (π * α) =
      cos (π * α / 2) * (2 * sin (π * α / 2)) := by
    have h := sin_two_mul (π * α / 2)
    have h2 : 2 * (π * α / 2) = π * α := by ring
    rw [h2] at h; linarith
  rw [hdouble] at hfg
  exact (tendsto_mul_iff_of_ne_zero hg h2sin_ne).mp hfg

/-! #### Boundary Frullani integral

The auxiliary below has cancelling poles at zero and a finite limit at infinity. Its scale-two
Frullani difference evaluates the unshifted scalar integral as `log 2`. -/

/-- The auxiliary function whose scale-two Frullani difference is the boundary integrand. -/
private def boundaryFrullaniAux (x : ℝ) : ℝ :=
  2 / x - cosh (x / 2) / sinh (x / 2)

/-- The Frullani auxiliary tends to zero at the right of zero. The apparent poles cancel:
its numerator is `o(x²)`, while its denominator is asymptotic to `x² / 2`. -/
private lemma boundaryFrullaniAux_tendsto_zero :
    Tendsto boundaryFrullaniAux (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hhalf : Tendsto (fun x : ℝ => x / 2) (nhds 0) (nhds 0) := by
    have h : ContinuousAt (fun x : ℝ => x / 2) 0 := continuousAt_id.div_const 2
    simpa using h.tendsto
  have hsinh : (fun x : ℝ => sinh (x / 2)) ~[nhds 0] (fun x => x / 2) :=
    Real.isEquivalent_sinh.comp_tendsto hhalf
  have hsinh_rem : (fun x : ℝ => 2 * (sinh (x / 2) - x / 2)) =o[nhds 0]
      (fun x => x ^ 2) := by
    have hO := sinh_sub_id_isBigO.comp_tendsto hhalf
    have ho : (fun x : ℝ => (x / 2) ^ 3) =o[nhds 0] (fun x => x ^ 2) := by
      refine ((isLittleO_pow_pow (by omega : 2 < 3) :
        (fun x : ℝ => x ^ 3) =o[nhds 0] (fun x => x ^ 2)).const_mul_left (1 / 8)).congr'
        (Eventually.of_forall fun x => by ring) (Eventually.of_forall fun _ => rfl)
    exact (hO.trans_isLittleO ho).const_mul_left 2
  have hcosh_rem : (fun x : ℝ => x * (cosh (x / 2) - 1)) =o[nhds 0]
      (fun x => x ^ 2) := by
    have hcosh : (fun x : ℝ => cosh (x / 2) - 1) =o[nhds 0] (fun x => x / 2) := by
      refine ((Real.hasDerivAt_cosh 0).isLittleO.comp_tendsto hhalf).congr'
        (Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => by simp)
      simp only [Function.comp_apply, cosh_zero, sinh_zero, smul_eq_mul]
      ring
    have hmul := (isBigO_refl (fun x : ℝ => x) (nhds 0)).mul_isLittleO hcosh
    exact (hmul.const_mul_right (by norm_num : (2 : ℝ) ≠ 0)).congr'
      (Eventually.of_forall fun _ => rfl) (Eventually.of_forall fun x => by ring)
  have hnum : (fun x : ℝ => 2 * sinh (x / 2) - x * cosh (x / 2)) =o[nhds 0]
      (fun x => x ^ 2) := by
    exact (hsinh_rem.sub hcosh_rem).congr' (Eventually.of_forall fun x => by ring)
      (Eventually.of_forall fun _ => rfl)
  have hden : (fun x : ℝ => x * sinh (x / 2)) ~[nhds 0] (fun x => x ^ 2 / 2) := by
    have h := (IsEquivalent.refl (l := nhds 0) (u := fun x : ℝ => x)).mul hsinh
    exact h.congr' (Eventually.of_forall fun x => by simp only [Pi.mul_apply, Pi.sub_apply]; ring)
      (Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring)
  have hratio : Tendsto
      (fun x : ℝ => (2 * sinh (x / 2) - x * cosh (x / 2)) /
        (x * sinh (x / 2))) (nhds 0) (nhds 0) := by
    apply IsLittleO.tendsto_div_nhds_zero
    have hn := hnum.const_mul_right (by norm_num : (1 / 2 : ℝ) ≠ 0)
    exact (hn.congr' (Eventually.of_forall fun _ => rfl)
      (Eventually.of_forall fun x => by ring)).trans_isEquivalent hden.symm
  apply (hratio.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hsh : sinh (x / 2) ≠ 0 := ne_of_gt (sinh_pos_iff.mpr (div_pos hx two_pos))
  simp only [boundaryFrullaniAux]
  field_simp

/-- The Frullani auxiliary tends to `-1` at infinity. -/
private lemma boundaryFrullaniAux_tendsto_atTop :
    Tendsto boundaryFrullaniAux atTop (nhds (-1)) := by
  have hexp : Tendsto (fun x : ℝ => exp (-x)) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have hcoth : Tendsto (fun x : ℝ => cosh (x / 2) / sinh (x / 2)) atTop (nhds 1) := by
    have hquot : Tendsto (fun x : ℝ => (1 + exp (-x)) / (1 - exp (-x))) atTop
        (nhds ((1 + 0) / (1 - 0))) :=
      (tendsto_const_nhds.add hexp).div (tendsto_const_nhds.sub hexp) (by norm_num)
    have heq : Filter.EventuallyEq atTop
        (fun x : ℝ => (1 + exp (-x)) / (1 - exp (-x)))
        (fun x => cosh (x / 2) / sinh (x / 2)) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      have hsh : sinh (x / 2) ≠ 0 := ne_of_gt (sinh_pos_iff.mpr (div_pos hx two_pos))
      change (1 + exp (-x)) / (1 - exp (-x)) = cosh (x / 2) / sinh (x / 2)
      rw [cosh_eq, sinh_eq, exp_neg]
      rw [show exp x = exp (x / 2) * exp (x / 2) by rw [← exp_add]; congr 1; ring,
        exp_neg]
      field_simp [exp_ne_zero]
    simpa using hquot.congr' heq
  have hinv : Tendsto (fun x : ℝ => 2 / x) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.const_mul (2 : ℝ))
  change Tendsto (fun x : ℝ => 2 / x - cosh (x / 2) / sinh (x / 2)) atTop (nhds (-1))
  simpa using hinv.sub hcoth

/-- The Frullani auxiliary is continuous, hence locally integrable, on the positive reals. -/
private lemma boundaryFrullaniAux_continuousOn : ContinuousOn boundaryFrullaniAux (Ioi 0) := by
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hsh : sinh (x / 2) ≠ 0 := ne_of_gt (sinh_pos_iff.mpr (div_pos hx two_pos))
  exact ((continuousAt_const.div continuousAt_id hx0).sub
    ((Real.continuous_cosh.comp (continuous_id.div_const 2)).continuousAt.div
      (Real.continuous_sinh.comp (continuous_id.div_const 2)).continuousAt hsh)).continuousWithinAt

/-- The scale-two difference of the Frullani auxiliary is `1/x - 1/sinh x`. -/
private lemma boundaryFrullaniAux_sub_two_mul (x : ℝ) (hx : 0 < x) :
    boundaryFrullaniAux x - boundaryFrullaniAux (2 * x) = 1 / x - 1 / sinh x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hsh : sinh x ≠ 0 := ne_of_gt (sinh_pos_iff.mpr hx)
  have hsh2 : sinh (x / 2) ≠ 0 := ne_of_gt (sinh_pos_iff.mpr (div_pos hx two_pos))
  have hsinh : sinh x = 2 * sinh (x / 2) * cosh (x / 2) := by
    rw [show x = x / 2 + x / 2 by ring, sinh_add]
    ring_nf
  have hcosh : cosh x = cosh (x / 2) ^ 2 + sinh (x / 2) ^ 2 := by
    rw [show x = x / 2 + x / 2 by ring, cosh_add]
    ring_nf
  simp only [boundaryFrullaniAux, mul_div_cancel_left₀ x two_ne_zero]
  rw [hsinh, hcosh]
  field_simp
  nlinarith [Real.cosh_sq_sub_sinh_sq (x / 2)]

/-- The boundary integrand is the scale-two Frullani difference of `boundaryFrullaniAux`. -/
private lemma boundaryFrullaniAux_integrand (x : ℝ) (hx : 0 < x) :
    1 / x ^ 2 - 1 / (x * sinh x) =
      x⁻¹ • (boundaryFrullaniAux (1 * x) - boundaryFrullaniAux (2 * x)) := by
  simp only [one_mul]
  rw [boundaryFrullaniAux_sub_two_mul x hx]
  simp only [smul_eq_mul]
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hsh : sinh x ≠ 0 := ne_of_gt (sinh_pos_iff.mpr hx)
  field_simp

/-- **Boundary value** `I(0) = log 2`.

$$\int_0^\infty \left(\frac{1}{s^2} - \frac{1}{s\,\sinh s}\right) ds = \log 2.$$

The integrand is the scale-two Frullani difference of `boundaryFrullaniAux`, whose limits at
zero and infinity are respectively `0` and `-1`. -/
lemma integral_inv_sq_sub_inv_s_sinh :
    ∫ s in Ioi (0 : ℝ), (1 / s ^ 2 - 1 / (s * sinh s)) = Real.log 2 := by
  have hloc : LocallyIntegrableOn boundaryFrullaniAux (Ioi 0) :=
    boundaryFrullaniAux_continuousOn.locallyIntegrableOn measurableSet_Ioi
  have hint : IntegrableOn
      (fun x : ℝ => x⁻¹ • (boundaryFrullaniAux (1 * x) - boundaryFrullaniAux (2 * x)))
      (Ioi 0) :=
    integrableOn_inv_sq_sub_inv_s_sinh.congr
      ((ae_restrict_mem measurableSet_Ioi).mono (fun x hx =>
        boundaryFrullaniAux_integrand x hx))
  have h := Frullani.integral_Ioi_eq hloc one_pos two_pos
    boundaryFrullaniAux_tendsto_zero boundaryFrullaniAux_tendsto_atTop hint
  calc
    ∫ s in Ioi (0 : ℝ), (1 / s ^ 2 - 1 / (s * sinh s)) =
        ∫ x in Ioi (0 : ℝ),
          x⁻¹ • (boundaryFrullaniAux (1 * x) - boundaryFrullaniAux (2 * x)) := by
      exact setIntegral_congr_fun measurableSet_Ioi boundaryFrullaniAux_integrand
    _ = Real.log 2 := by simpa [smul_eq_mul] using h

/-! #### Double sine at a boundary period

A normalized Frullani calculation evaluates `S₂(1; τ, 1)`.  This boundary value supplies the
square-root normalization used by the principal-form ghost-overlap formula. -/

/-- At the second period, the double-sine kernel is a Frullani difference of
`boundaryFrullaniAux`.  This is the pointwise identity

`K(ω₂; ω₁, ω₂; t) = t⁻¹ (f(2ω₁t/ω₂) - f(2t))`

after scaling to `ω₂ = 1`; here it is stated in exactly that normalized form. -/
private lemma doubleSineKernel_one_eq_boundaryFrullaniAux (tau : ℝ) (htau : 0 < tau)
    {t : ℝ} (ht : 0 < t) :
    doubleSineKernel 1 tau 1 t =
      t⁻¹ • (boundaryFrullaniAux ((2 * tau) * t) - boundaryFrullaniAux (2 * t)) := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hsinh_t : sinh t ≠ 0 := ne_of_gt (sinh_pos_iff.mpr ht)
  unfold doubleSineKernel boundaryFrullaniAux
  simp only [smul_eq_mul, one_mul, mul_one]
  rw [show (2 * tau * t) / 2 = tau * t by ring,
    show (2 * t) / 2 = t by ring]
  have htaut : tau * t ≠ 0 := mul_ne_zero (ne_of_gt htau) ht0
  have hsinh_taut : sinh (tau * t) ≠ 0 := by
    rw [sinh_ne_zero]
    exact htaut
  rw [show (tau + 1 - 2) * t = (tau - 1) * t by ring]
  have hhyperbolic :
      sinh ((tau - 1) * t) = sinh (tau * t) * cosh t - cosh (tau * t) * sinh t := by
    rw [show (tau - 1) * t = tau * t - t by ring, sinh_sub]
  rw [hhyperbolic]
  field_simp
  ring

/-- The log-integral of the normalized double sine at its second period is
`log(1 / τ)`.  Equivalently, it is `-log τ` for `τ > 0`.

This is the analytic boundary normalization of the Kurokawa--Koyama double sine.  The proof
writes the kernel as a Frullani difference whose auxiliary function tends to `0` at the origin
and to `-1` at infinity. -/
theorem doubleSineLogIntegral_one (tau : ℝ) (htau : 0 < tau) :
    doubleSineLogIntegral 1 tau 1 = Real.log (1 / tau) := by
  have hloc : LocallyIntegrableOn boundaryFrullaniAux (Ioi 0) :=
    boundaryFrullaniAux_continuousOn.locallyIntegrableOn measurableSet_Ioi
  have hkernel : IntegrableOn (doubleSineKernel 1 tau 1) (Ioi (0 : ℝ)) :=
    doubleSineKernel_integrableOn_Ioi 1 tau 1 htau one_pos one_pos (by linarith)
  have hint : IntegrableOn
      (fun t : ℝ => t⁻¹ •
        (boundaryFrullaniAux ((2 * tau) * t) - boundaryFrullaniAux (2 * t)))
      (Ioi 0) :=
    hkernel.congr ((ae_restrict_mem measurableSet_Ioi).mono fun t ht =>
      doubleSineKernel_one_eq_boundaryFrullaniAux tau htau ht)
  have hfrullani := Frullani.integral_Ioi_eq hloc (mul_pos two_pos htau) two_pos
    boundaryFrullaniAux_tendsto_zero boundaryFrullaniAux_tendsto_atTop hint
  unfold doubleSineLogIntegral
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun t ht => doubleSineKernel_one_eq_boundaryFrullaniAux tau htau ht)]
  have hratio : 2 / (2 * tau) = 1 / tau := by field_simp
  simpa [smul_eq_mul, hratio] using hfrullani

/-- **Boundary-period value of the double sine.**  For `τ > 0`,
`S₂(1; τ, 1) = √τ` in the Kurokawa--Koyama convention. Equivalently, by symmetry of `S₂` in its
two periods, `S₂(ω₂; ω₁, ω₂) = √(ω₁/ω₂)`; in the physics convention
`S_b(x) = S₂(x; b, b⁻¹)⁻¹` it reads `S_b(b) = b`.

The value is a short consequence of the difference equations for Barnes' double gamma function
`F(a, z)` in T. Shintani, *On Kronecker limit formula for real quadratic fields*, Proc. Japan
Acad. **52** (1976), 355--358, Proposition 1, where `F(a, ·)` is also stated to be symmetric in
`a = (a₁, a₂)`. Since `F(a, z) ~ z` as `z → 0` and `Γ(z/a₂) ~ a₂/z`, the first of those equations
gives `F(a, a₁) = √(a₂/2π)` in the limit, hence `F(a, a₂) = √(a₁/2π)` by that symmetry, hence
`S₂(a₂; a₁, a₂) = F(a, a₂)/F(a, a₁) = √(a₁/a₂)`.

The proof evaluates the defining integral via `doubleSineLogIntegral_one`. This value is
*not* a consequence of reflection and the double-sine
quasiperiodicity ladder alone: `S₂(z + ω₁) = S₂(z)·S₁(z, ω₂)⁻¹` reads `0/0` at `z = 0`, and the
physics form `S_b(x + b) = 2 sin(πbx) S_b(x)` degenerates likewise at the pole `x = 0`. Shintani's
double-gamma equations escape this because the `Γ(z/a₂)` factor supplies the pole that cancels
`F`'s zero.

A remark this value settles, in S. Koyama and N. Kurokawa, *Zetas and normalized multiple sines*,
Keio University Dept. of Mathematics research report KSTS/RR-04/003 (2002), Remark 1.11: that
remark shows `S₂(2, (1, √2)) / S₂(1, (1, √2)) ∉ ℚ̄` and concludes only that *at least one* of the
two is transcendental. Here `S₂(1, (1, √2)) = 2 ^ (1/4)` is algebraic, so the transcendental one
is `S₂(2, (1, √2)) = 2 ^ (1/4) / (2 sin (π/√2))`. -/
theorem doubleSine_one (tau : ℝ) (htau : 0 < tau) :
    doubleSine 1 tau 1 = Real.sqrt tau := by
  unfold doubleSine
  rw [doubleSineLogIntegral_one tau htau, one_div, Real.log_inv]
  rw [show - -Real.log tau / 2 = Real.log tau / 2 by ring, Real.exp_half,
    Real.exp_log htau]

/-! #### Shifted kernel integral

The geometric expansion of `1/sinh s` turns the parameter-dependent correction into Frullani
integrals. Absolute summability allows termwise integration, and the cosine product sums the
resulting logarithms. -/

/-- The `n`th exponential summand in the geometric-series expansion of the shifted kernel. -/
private def shiftedKernelSeriesSummand (α : ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  s⁻¹ * (2 * rexp (-((2 * ↑n + 1) * s)) - rexp (-((2 * ↑n + 1 - α) * s)) -
    rexp (-((2 * ↑n + 1 + α) * s)))

/-- A shifted-kernel summand factors as `1 - cosh (αs)` times a positive exponential. -/
private lemma shiftedKernelSeriesSummand_factor (α : ℝ) (n : ℕ) (s : ℝ) :
    shiftedKernelSeriesSummand α n s =
      (1 - cosh (α * s)) * (s⁻¹ * (2 * rexp (-((2 * ↑n + 1) * s)))) := by
  unfold shiftedKernelSeriesSummand
  rw [cosh_eq,
    show -((2 * ↑n + 1 - α) * s) = -((2 * ↑n + 1) * s) + α * s by ring,
    show -((2 * ↑n + 1 + α) * s) = -((2 * ↑n + 1) * s) + -(α * s) by ring,
    exp_add, exp_add]
  ring

/-- The shifted-kernel summands sum pointwise to `(1 - cosh (αs)) / (s sinh s)` for `s > 0`. -/
private lemma hasSum_shiftedKernelSeriesSummand (α : ℝ) {s : ℝ} (hs : 0 < s) :
    HasSum (fun n => shiftedKernelSeriesSummand α n s)
      ((1 - cosh (α * s)) / (s * sinh s)) := by
  have h := (hasSum_exp_inv_sinh hs).mul_left ((1 - cosh (α * s)) * s⁻¹)
  have heq : (fun n => shiftedKernelSeriesSummand α n s) = fun (n : ℕ) =>
      (1 - cosh (α * s)) * s⁻¹ * (2 * rexp (-(2 * (n : ℝ) + 1) * s)) := by
    funext n
    rw [shiftedKernelSeriesSummand_factor,
      show -(2 * (n : ℝ) + 1) * s = -((2 * n + 1) * s) by ring]
    ring
  rw [heq, show (1 - cosh (α * s)) / (s * sinh s) =
    (1 - cosh (α * s)) * s⁻¹ * (1 / sinh s) by ring]
  exact h

/-- Every shifted-kernel summand is integrable on the positive half-line when `|α| < 1`. -/
private lemma shiftedKernelSeriesSummand_integrableOn (α : ℝ) (hα : |α| < 1) (n : ℕ) :
    IntegrableOn (shiftedKernelSeriesSummand α n) (Ioi (0 : ℝ)) := by
  obtain ⟨hα_neg, hα_pos⟩ := abs_lt.mp hα
  have hn : (0 : ℝ) < 2 * ↑n + 1 := by positivity
  have hna : 0 < 2 * (↑n : ℝ) + 1 - α := by linarith
  have hnb : 0 < 2 * (↑n : ℝ) + 1 + α := by linarith
  have hsplit : ∀ s ∈ Ioi (0 : ℝ), shiftedKernelSeriesSummand α n s =
      s⁻¹ * (rexp (-((2 * ↑n + 1) * s)) - rexp (-((2 * ↑n + 1 + α) * s))) +
      s⁻¹ * (rexp (-((2 * ↑n + 1) * s)) - rexp (-((2 * ↑n + 1 - α) * s))) := by
    intro s _
    unfold shiftedKernelSeriesSummand
    ring
  exact ((integrableOn_frullani_exp _ _ hn hnb).add
    (integrableOn_frullani_exp _ _ hn hna)).congr
      ((ae_restrict_mem measurableSet_Ioi).mono fun s hs => (hsplit s hs).symm)

/-- A shifted-kernel summand is nonpositive on the positive half-line. -/
private lemma shiftedKernelSeriesSummand_nonpos (α : ℝ) (n : ℕ) {s : ℝ} (hs : 0 < s) :
    shiftedKernelSeriesSummand α n s ≤ 0 := by
  rw [shiftedKernelSeriesSummand_factor]
  exact mul_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr (Real.one_le_cosh (α * s))) (by positivity)

/-- The integral of the norm of a shifted-kernel summand is the negative logarithm of its
odd Weierstrass factor. -/
private lemma integral_norm_shiftedKernelSeriesSummand (α : ℝ) (hα : |α| < 1) (n : ℕ) :
    ∫ s in Ioi (0 : ℝ), ‖shiftedKernelSeriesSummand α n s‖ =
      -Real.log (1 - α ^ 2 / (2 * ↑n + 1) ^ 2) := by
  rw [show (∫ s in Ioi (0 : ℝ), ‖shiftedKernelSeriesSummand α n s‖) =
      ∫ s in Ioi (0 : ℝ), -shiftedKernelSeriesSummand α n s by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    change ‖shiftedKernelSeriesSummand α n s‖ = -shiftedKernelSeriesSummand α n s
    rw [Real.norm_eq_abs, abs_of_nonpos (shiftedKernelSeriesSummand_nonpos α n hs)]]
  rw [integral_neg]
  exact congrArg Neg.neg (integral_summand_J α hα n)

/-- The negative logarithms of the odd Weierstrass factors sum to the negative logarithm of
`cos (πα/2)`. -/
private lemma hasSum_neg_log_oddFactors (α : ℝ) (hα0 : α ≠ 0) (hα : |α| < 1) :
    HasSum (fun n : ℕ => -Real.log (1 - α ^ 2 / (2 * ↑n + 1) ^ 2))
      (-Real.log (cos (π * α / 2))) := by
  have hcos : 0 < cos (π * α / 2) :=
    Real.cos_pos_of_mem_Ioo (by
      obtain ⟨h1, h2⟩ := abs_lt.mp hα
      exact ⟨by nlinarith [pi_pos], by nlinarith [pi_pos]⟩)
  have hterm_pos (n : ℕ) : (0 : ℝ) < 1 - α ^ 2 / (2 * ↑n + 1) ^ 2 := by
    have hα2 : α ^ 2 < 1 := by
      nlinarith [sq_abs α, abs_nonneg α, sq_nonneg (1 - |α|)]
    have : α ^ 2 / (2 * ↑n + 1) ^ 2 < 1 := by
      rw [div_lt_one (by positivity)]
      exact lt_of_lt_of_le hα2 (by nlinarith [show 0 ≤ (n : ℝ) by positivity])
    linarith
  have hneg_nonneg (n : ℕ) :
      0 ≤ -Real.log (1 - α ^ 2 / (2 * ↑n + 1) ^ 2) :=
    neg_nonneg.mpr (Real.log_nonpos (hterm_pos n).le
      (sub_le_self _ (div_nonneg (sq_nonneg α) (sq_nonneg _))))
  rw [hasSum_iff_tendsto_nat_of_nonneg hneg_nonneg]
  have hlog_tendsto : Tendsto
      (fun N => Real.log (∏ n ∈ Finset.range N, (1 - α ^ 2 / (2 * ↑n + 1) ^ 2)))
      atTop (nhds (Real.log (cos (π * α / 2)))) :=
    (Real.continuousAt_log (ne_of_gt hcos)).tendsto.comp
      (tendsto_weierstrass_cos_prod α hα0 hα)
  convert hlog_tendsto.neg using 1
  ext N
  rw [Finset.sum_neg_distrib, Real.log_prod (fun n _ => (hterm_pos n).ne')]

/-- **Integral of the shifted kernel** for `|α| < 1`.

$$\int_0^\infty \frac{1 - \cosh(\alpha s)}{s\,\sinh s}\,ds = \log\cos(\pi\alpha/2).$$

*Proof strategy.* Expand `(1 − cosh(αs))/sinh s` as the geometric series
`Σ_{n≥0}(2e^{-(2n+1)s} − e^{-(2n+1−α)s} − e^{-(2n+1+α)s})`.
Each term is `≤ 0` (since `cosh b ≥ 1`), and the integrals of their norms sum to the
negative logarithm of the odd Weierstrass product, so the series and integral may be interchanged.
Each summand integrates to `log(1 − α²/(2n+1)²)` by the Frullani integral
(`∫₀^∞(e^{-as}−e^{-bs})/s ds = log(b/a)`, proved via Fubini + `integral_exp_mul_Ioi`).
Sum the logarithms via the Weierstrass cosine product
`cos(πα/2) = Π_{n≥0}(1−α²/(2n+1)²)` (derived from `Real.tendsto_euler_sin_prod`
by splitting even/odd factors). -/
lemma integral_one_sub_cosh_div_s_sinh (α : ℝ) (hα : |α| < 1) :
    ∫ s in Ioi (0 : ℝ), (1 - cosh (α * s)) / (s * sinh s) =
    Real.log (cos (π * α / 2)) := by
  by_cases hα0 : α = 0
  · subst α
    simp
  have hlogs := hasSum_neg_log_oddFactors α hα0 hα
  calc
    ∫ s in Ioi (0 : ℝ), (1 - cosh (α * s)) / (s * sinh s) =
        ∫ s in Ioi (0 : ℝ), ∑' n, shiftedKernelSeriesSummand α n s := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      exact (hasSum_shiftedKernelSeriesSummand α hs).tsum_eq.symm
    _ = ∑' n, ∫ s in Ioi (0 : ℝ), shiftedKernelSeriesSummand α n s :=
      (integral_tsum_of_summable_integral_norm
        (shiftedKernelSeriesSummand_integrableOn α hα) (by
          simpa only [integral_norm_shiftedKernelSeriesSummand α hα] using
            hlogs.summable)).symm
    _ = ∑' n : ℕ, Real.log (1 - α ^ 2 / (2 * ↑n + 1) ^ 2) :=
      tsum_congr (integral_summand_J α hα)
    _ = Real.log (cos (π * α / 2)) := by
      simpa only [neg_neg] using hlogs.neg.tsum_eq

/-- **Integral identity for the kernel difference** (assembly from helpers).

For `|α| < 1`:
$$\int_0^\infty \left(\frac{1}{s^2} - \frac{\cosh(\alpha s)}{s\,\sinh s}\right) ds
= \log\bigl(2\cos(\pi\alpha/2)\bigr).$$

Splits the integrand as `(1/s² − 1/(s sinh s)) + (1 − cosh(αs))/(s sinh s)`,
applies `integral_inv_sq_sub_inv_s_sinh` and `integral_one_sub_cosh_div_s_sinh`,
and combines via `Real.log_mul`. -/
lemma integral_inv_sq_sub_cosh_div_sinh (α : ℝ) (hα : |α| < 1) :
    ∫ s in Ioi (0 : ℝ), (1 / s ^ 2 - cosh (α * s) / (s * sinh s)) =
    Real.log (2 * cos (π * α / 2)) := by
  -- Positivity of cos(πα/2)
  have hcos : 0 < cos (π * α / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    obtain ⟨h1, h2⟩ := abs_lt.mp hα
    exact ⟨by nlinarith [pi_pos], by nlinarith [pi_pos]⟩
  -- Split: f(s) = (1/s² − 1/(s sinh s)) + (1 − cosh(αs))/(s sinh s)
  have hsplit : ∀ s ∈ Ioi (0 : ℝ),
      1 / s ^ 2 - cosh (α * s) / (s * sinh s) =
      (1 / s ^ 2 - 1 / (s * sinh s)) + (1 - cosh (α * s)) / (s * sinh s) := by
    intro s hs; simp only [mem_Ioi] at hs
    have hs0 : s ≠ 0 := ne_of_gt hs
    have hsh : sinh s ≠ 0 := ne_of_gt (sinh_pos_iff.mpr hs)
    field_simp; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hsplit,
      integral_add integrableOn_inv_sq_sub_inv_s_sinh
        (integrableOn_one_sub_cosh_div_s_sinh α hα),
      integral_inv_sq_sub_inv_s_sinh,
      integral_one_sub_cosh_div_s_sinh α hα,
      ← Real.log_mul (by positivity : (2 : ℝ) ≠ 0) (ne_of_gt hcos)]

end SIC

end
