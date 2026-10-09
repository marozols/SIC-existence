/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.Faddeev.FiveTerm.Integrability
import SICs.SpecialFunctions.Faddeev.FiveTerm.ParameterDomain
import SICs.Analysis.HolomorphicParametricIntegral

/-!
# Holomorphy of the vertical five-term integral

The vertical five-term integral is holomorphic in its exponential parameter on the convergence
strip.

This module follows the analytic continuation in [RW26, Radchenko, Wheeler (2026), Appendix A.2,
`app:mod.fad`], for the `n = h = 0` upper-half-plane kernel.

## The argument

At fixed contour point, the kernel is a factor independent of `w` times an exponential of a
linear function of `w`, even at totalized removable points. On a small parameter rectangle, its
norm is bounded by the sum of the kernel norms at the four corners. The corners lie in the
convergence strip, so vertical integrability on a line to the right of the shifted left poles that
meets no right pole, with finitely many right poles on its left, makes this sum an integrable local
majorant. The holomorphic parametric integral theorem then gives the continuation.
-/

noncomputable section

open Complex Real Filter MeasureTheory Set Metric
open scoped Topology MatrixGroups

namespace SIC

/-! ### Exponential domination on a parameter rectangle

The real part of an affine phase reaches its maximum at a corner of a rectangle. Summing all
four corner norms avoids choosing a corner measurably as the contour point varies. -/

/-- An affine real function on a rectangle is no larger than its value at some corner; used by
`complex_exp_corner`. -/
private lemma affine_rect_corner (a b u v r : ℝ) (hu : |u| ≤ r) (hv : |v| ≤ r) :
    ∃ s ∈ ({-r, r} : Set ℝ), ∃ t ∈ ({-r, r} : Set ℝ),
      a * u + b * v ≤ a * s + b * t := by
  obtain ⟨huL, huR⟩ := abs_le.mp hu
  obtain ⟨hvL, hvR⟩ := abs_le.mp hv
  rcases le_total 0 a with ha | ha
  · rcases le_total 0 b with hb | hb
    · exact ⟨r, by simp, r, by simp,
        add_le_add (mul_le_mul_of_nonneg_left huR ha)
          (mul_le_mul_of_nonneg_left hvR hb)⟩
    · exact ⟨r, by simp, -r, by simp,
        add_le_add (mul_le_mul_of_nonneg_left huR ha)
          (mul_le_mul_of_nonpos_left hvL hb)⟩
  · rcases le_total 0 b with hb | hb
    · exact ⟨-r, by simp, r, by simp,
        add_le_add (mul_le_mul_of_nonpos_left huL ha)
          (mul_le_mul_of_nonneg_left hvR hb)⟩
    · exact ⟨-r, by simp, -r, by simp,
        add_le_add (mul_le_mul_of_nonpos_left huL ha)
          (mul_le_mul_of_nonpos_left hvL hb)⟩

/-- The real part of a complex linear phase is bounded at a rectangle corner; used by
`complex_norm_exp_rect_bound`. -/
private lemma complex_exp_corner (b w₀ w : ℂ) (r : ℝ)
    (hre : |w.re - w₀.re| ≤ r) (him : |w.im - w₀.im| ≤ r) :
    ∃ s ∈ ({-r, r} : Set ℝ), ∃ t ∈ ({-r, r} : Set ℝ),
      (b * w).re ≤ (b * (w₀ + (s : ℂ) + (t : ℂ) * I)).re := by
  obtain ⟨s, hs, t, ht, h⟩ :=
    affine_rect_corner b.re (-b.im) (w.re - w₀.re) (w.im - w₀.im) r hre him
  refine ⟨s, hs, t, ht, ?_⟩
  simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re,
    Complex.add_im, Complex.ofReal_im, Complex.mul_I_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
  nlinarith [h]

/-- The norm of `a exp(bw)` on a parameter rectangle is bounded by the sum of its four corner
values; used by `norm_kernel_rect_le`. -/
private lemma complex_norm_exp_rect_bound (a b w₀ w : ℂ) (r : ℝ)
    (hre : |w.re - w₀.re| ≤ r) (him : |w.im - w₀.im| ≤ r) :
    ‖a * exp (b * w)‖ ≤
      ‖a * exp (b * (w₀ + ((-r : ℝ) : ℂ) + ((-r : ℝ) : ℂ) * I))‖ +
      ‖a * exp (b * (w₀ + ((-r : ℝ) : ℂ) + (r : ℂ) * I))‖ +
      ‖a * exp (b * (w₀ + (r : ℂ) + ((-r : ℝ) : ℂ) * I))‖ +
      ‖a * exp (b * (w₀ + (r : ℂ) + (r : ℂ) * I))‖ := by
  obtain ⟨s, hs, t, ht, hreal⟩ := complex_exp_corner b w₀ w r hre him
  have hle : ‖a * exp (b * w)‖ ≤
      ‖a * exp (b * (w₀ + (s : ℂ) + (t : ℂ) * I))‖ := by
    simp only [norm_mul, Complex.norm_exp]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hreal) (norm_nonneg _)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
  rcases hs with hs | hs <;> rcases ht with ht | ht <;>
    subst s <;> subst t <;> nlinarith [hle,
      norm_nonneg (a * exp (b * (w₀ + ((-r : ℝ) : ℂ) + ((-r : ℝ) : ℂ) * I))),
      norm_nonneg (a * exp (b * (w₀ + ((-r : ℝ) : ℂ) + (r : ℂ) * I))),
      norm_nonneg (a * exp (b * (w₀ + (r : ℂ) + ((-r : ℝ) : ℂ) * I))),
      norm_nonneg (a * exp (b * (w₀ + (r : ℂ) + (r : ℂ) * I)))]

/-! ### The five-term kernel and the local majorant

Only the exponential phase depends on `w`. This remains true at totalized removable points, so
the rectangle estimate applies on the entire contour without extra nonvanishing hypotheses. -/

/-- The kernel factors as `A(z) exp(B(z)w)` with `A` independent of `w`; used by
`norm_kernel_rect_le`. -/
private lemma kernel_param_eq (γ : SL(2, ℤ)) (ℓ p m : ℤ)
    (w y τ z : ℂ) :
    fiveTermKernelUHP γ ℓ p w y τ m z =
      (faddeevModularUHP γ (m + 1) 0 z τ /
        faddeevModularUHP γ (m + p) 0 (z + y) τ *
        exp (2 * π * I * (ℓ * (z + m * τ)))) *
        exp (2 * π * I *
          ((((γ 1 0 : ℤ) : ℂ) * z + fltDenominator (γ : Mat(2, ℤ)) τ * m) /
          fltDenominator (γ : Mat(2, ℤ)) τ) * w) := by
  unfold fiveTermKernelUHP
  have hphase :
      2 * π * I *
        (((((γ 1 0 : ℤ) : ℂ) * z + fltDenominator (γ : Mat(2, ℤ)) τ * m) * w /
          fltDenominator (γ : Mat(2, ℤ)) τ) + ℓ * (z + m * τ)) =
        2 * π * I * (ℓ * (z + m * τ)) +
          2 * π * I *
            ((((γ 1 0 : ℤ) : ℂ) * z + fltDenominator (γ : Mat(2, ℤ)) τ * m) /
              fltDenominator (γ : Mat(2, ℤ)) τ) * w := by ring
  rw [hphase, Complex.exp_add]
  ring

/-- Four nearby parameter values dominate the kernel norm throughout their rectangle; used by
`exists_integrable_kernel_rect_bound`. -/
private lemma norm_kernel_rect_le (γ : SL(2, ℤ)) (ℓ p m : ℤ)
    (w₀ w y τ z : ℂ) (r : ℝ)
    (hre : |w.re - w₀.re| ≤ r) (him : |w.im - w₀.im| ≤ r) :
    ‖fiveTermKernelUHP γ ℓ p w y τ m z‖ ≤
      ‖fiveTermKernelUHP γ ℓ p
        (w₀ + ((-r : ℝ) : ℂ) + ((-r : ℝ) : ℂ) * I) y τ m z‖ +
      ‖fiveTermKernelUHP γ ℓ p
        (w₀ + ((-r : ℝ) : ℂ) + (r : ℂ) * I) y τ m z‖ +
      ‖fiveTermKernelUHP γ ℓ p
        (w₀ + (r : ℂ) + ((-r : ℝ) : ℂ) * I) y τ m z‖ +
      ‖fiveTermKernelUHP γ ℓ p
        (w₀ + (r : ℂ) + (r : ℂ) * I) y τ m z‖ := by
  simpa only [kernel_param_eq] using
    (complex_norm_exp_rect_bound
      (faddeevModularUHP γ (m + 1) 0 z τ /
        faddeevModularUHP γ (m + p) 0 (z + y) τ *
        exp (2 * π * I * (ℓ * (z + m * τ))))
      (2 * π * I *
        ((((γ 1 0 : ℤ) : ℂ) * z + fltDenominator (γ : Mat(2, ℤ)) τ * m) /
          fltDenominator (γ : Mat(2, ℤ)) τ)) w₀ w r hre him)

/-- A parameter rectangle corner lies within twice its coordinate radius of its center; used by
`exists_rectangle_radius`. -/
private lemma corner_dist_le (w₀ : ℂ) (r s t : ℝ) (hs : |s| ≤ r) (ht : |t| ≤ r) :
    dist (w₀ + (s : ℂ) + (t : ℂ) * I) w₀ ≤ 2 * r := by
  rw [Complex.dist_eq]
  calc
    ‖w₀ + (s : ℂ) + (t : ℂ) * I - w₀‖ = ‖(s : ℂ) + (t : ℂ) * I‖ := by abel_nf
    _ ≤ ‖(s : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
    _ = |s| + |t| := by simp
    _ ≤ 2 * r := by linarith

/-- Every point of an open parameter set has a closed ball whose four rectangle corners remain in
the set; used by `exists_integrable_kernel_rect_bound`. -/
private lemma exists_rectangle_radius {U : Set ℂ} (hU : IsOpen U)
    {w₀ : ℂ} (hw₀ : w₀ ∈ U) :
    ∃ r > 0, closedBall w₀ r ⊆ U ∧
      ∀ s ∈ ({-r, r} : Set ℝ), ∀ t ∈ ({-r, r} : Set ℝ),
        w₀ + (s : ℂ) + (t : ℂ) * I ∈ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU w₀ hw₀
  let r := ε / 4
  have hr : 0 < r := by dsimp [r]; positivity
  refine ⟨r, hr, (closedBall_subset_ball (by dsimp [r]; linarith)).trans hball, ?_⟩
  intro s hs t ht
  have hcorner_abs (u : ℝ) (hu : u ∈ ({-r, r} : Set ℝ)) : |u| ≤ r := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with hu | hu
    · rw [hu, abs_neg, abs_of_nonneg hr.le]
    · rw [hu, abs_of_nonneg hr.le]
  apply hball
  rw [mem_ball]
  exact (corner_dist_le w₀ r s t (hcorner_abs s hs) (hcorner_abs t ht)).trans_lt
    (by dsimp [r]; linarith)

/-- Integrability at the four parameter corners gives a locally uniform majorant for the vertical
five-term kernel; used by `differentiableOn_integral_kernelUHP_of_integrable`. -/
private lemma exists_integrable_kernel_rect_bound
    (γ : SL(2, ℤ)) (ℓ p m : ℤ) (y τ : ℂ) (x : ℝ)
    (hint : ∀ w ∈ fiveTermParameterStrip γ ℓ p y τ,
      Integrable (fun t : ℝ =>
        fiveTermKernelUHP γ ℓ p w y τ m ((x : ℂ) + t * I)))
    (w₀ : ℂ) (hw₀ : w₀ ∈ fiveTermParameterStrip γ ℓ p y τ) :
    ∃ r > 0, closedBall w₀ r ⊆ fiveTermParameterStrip γ ℓ p y τ ∧
      ∃ g : ℝ → ℝ, Integrable g ∧
        ∀ᵐ t : ℝ ∂volume, ∀ w ∈ closedBall w₀ r,
          ‖fiveTermKernelUHP γ ℓ p w y τ m ((x : ℂ) + t * I)‖ ≤ g t := by
  obtain ⟨r, hr, hrU, hcorner⟩ :=
    exists_rectangle_radius (isOpen_fiveTermParameterStrip γ ℓ p y τ) hw₀
  let corner (s q : ℝ) : ℂ := w₀ + (s : ℂ) + (q : ℂ) * I
  let K (s q : ℝ) (t : ℝ) : ℝ :=
    ‖fiveTermKernelUHP γ ℓ p (corner s q) y τ m ((x : ℂ) + t * I)‖
  let g (t : ℝ) := K (-r) (-r) t + K (-r) r t + K r (-r) t + K r r t
  have hK : ∀ s ∈ ({-r, r} : Set ℝ), ∀ q ∈ ({-r, r} : Set ℝ),
      Integrable (K s q) := by
    intro s hs q hq
    exact (hint (corner s q) (hcorner s hs q hq)).norm
  have hg : Integrable g :=
    (((hK (-r) (by simp) (-r) (by simp)).add
      (hK (-r) (by simp) r (by simp))).add
      (hK r (by simp) (-r) (by simp))).add (hK r (by simp) r (by simp))
  refine ⟨r, hr, hrU, g, hg, Filter.Eventually.of_forall ?_⟩
  intro t w hw
  have hre := abs_re_sub_le_of_mem_closedBall hw
  have him : |w.im - w₀.im| ≤ r := by
    have hi := Complex.abs_im_le_norm (w - w₀)
    exact (by simpa only [Complex.sub_im] using hi.trans (mem_closedBall_iff_norm.mp hw))
  exact norm_kernel_rect_le γ ℓ p m w₀ w y τ ((x : ℂ) + t * I) r hre him

/-! ### Holomorphy on the convergence strip

The parameter strip supplies both strict tail decay conditions at each corner. The contour
separation is independent of `w`. -/

/-- The vertical five-term integral is holomorphic whenever its kernel is integrable at every
point of the parameter strip. -/
private lemma differentiableOn_integral_kernelUHP_of_integrable
    (γ : SL(2, ℤ)) (ℓ p m : ℤ) (y τ : ℂ) (hτ : 0 < τ.im) (x : ℝ)
    (hint : ∀ w ∈ fiveTermParameterStrip γ ℓ p y τ,
      Integrable (fun t : ℝ =>
        fiveTermKernelUHP γ ℓ p w y τ m ((x : ℂ) + t * I))) :
    DifferentiableOn ℂ
      (fun w => ∫ t : ℝ, fiveTermKernelUHP γ ℓ p w y τ m ((x : ℂ) + t * I))
      (fiveTermParameterStrip γ ℓ p y τ) := by
  apply differentiableOn_integral_of_locally_bounded
  · intro w hw
    exact ((measurable_fiveTermKernelUHP γ ℓ p w y τ hτ m).comp
      (by fun_prop)).aestronglyMeasurable
  · filter_upwards [] with t
    intro w hw
    unfold fiveTermKernelUHP
    fun_prop
  · intro w hw
    exact exists_integrable_kernel_rect_bound γ ℓ p m y τ x hint w hw

/-- The vertical five-term integral is holomorphic in `w` on the convergence strip when the
line lies to the right of the shifted left poles and meets no genuine right pole; finitely many
right poles may lie to its left. The separation is independent of `w`, and
`integrable_fiveTermKernelUHP_of_regular` supplies the corner majorants.
[RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`, analytic continuation in the
proof of Theorem 3, `thm:5term.mod.fad`]. -/
theorem differentiableOn_integral_fiveTermKernelUHP_of_regular
    (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (ℓ p m : ℤ) (y τ : ℂ)
    (hτ : 0 < τ.im) (he : 0 < (fltDenominator (γ : Mat(2, ℤ)) τ).re)
    (x : ℝ)
    (hxP : ∀ u ∈ faddeevModularUHPPoles γ (m + 1) τ, u.re ≠ x)
    (hxL : (-((m + p : ℤ) : ℝ) * (fltDenominator (γ : Mat(2, ℤ)) τ).re - 1) /
      (γ 1 0 : ℝ) - y.re < x) :
    DifferentiableOn ℂ
      (fun w => ∫ t : ℝ, fiveTermKernelUHP γ ℓ p w y τ m ((x : ℂ) + t * I))
      (fiveTermParameterStrip γ ℓ p y τ) := by
  apply differentiableOn_integral_kernelUHP_of_integrable γ ℓ p m y τ hτ x
  intro w hw
  obtain ⟨hLam, hMu⟩ := hw
  exact integrable_fiveTermKernelUHP_of_regular γ hc ℓ p m w y τ hτ he
    hLam hMu x hxP hxL

end SIC
