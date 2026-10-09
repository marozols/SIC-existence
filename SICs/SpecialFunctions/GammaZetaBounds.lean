/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import SICs.Analysis.RealPowerBounds

/-!
# Gamma and completed-zeta bounds on vertical strips

Gamma and completed-zeta strip estimates, and quadratic decay of `ζ(s)Γ(s)` for `Re s > -1`.

This file collects the estimates for the gamma function and the Riemann zeta function on closed
vertical strips that the Mellin transform and contour-shift arguments of
`SICs.SpecialFunctions.Mellin` consume. They follow [95, Shintani (1977), proof of Lemma 1,
pp. 170--171], where the contour shifts for `f₁` and `f₂` need the integrand to decay along
horizontal segments.

Euler's integral bounds `|Gamma(s)|` by `Gamma(Re(s))` on the right half-plane, and two gamma
recurrences turn this into quadratic decay `|Gamma(s)| ≤ Gamma(Re(s)+2)/|s|²`. The entire part of
completed zeta is a Mellin integral converging for every parameter, so it is bounded on every
closed strip, and adding back its two rational pole terms keeps it bounded away from `0` and `1`.
Legendre's duplication formula `Gamma_R(w) Gamma_R(w+1) = Gamma_C(w)` then writes `zeta(w) Gamma(w)`
as completed zeta times a half-argument gamma factor and an explicit exponential coefficient;
applying the quadratic gamma bound to the half argument gives `|zeta(s) Gamma(s)| ≤ C/(1+Im(s)²)`
on closed strips in `Re(s) > -1` at heights `|Im(s)| ≥ 1`.

## Main results

- `analyticAt_Gamma_of_re_pos`, `norm_Gamma_le_div_norm_sq`: analyticity and quadratic decay of
  gamma on the right half-plane.
- `exists_norm_Gamma_le`: gamma is uniformly bounded on closed strips in `Re(s) > -1` at heights
  `|Im(s)| ≥ 1`.
- `exists_norm_completedRiemannZeta_vertical_le`, `exists_norm_completedRiemannZeta_strip_le`:
  completed zeta is bounded on vertical lines and on strips away from its poles.
- `gammaZetaBound`, `norm_zeta_mul_Gamma_le`: the duplication bound
  `|zeta(w) Gamma(w)| ≤ |Lambda(w)| · D(Re(w))` for `Re(w) > 0`.
- `exists_norm_zeta_mul_Gamma_le`: quadratic strip decay of `zeta(s) Gamma(s)` on closed strips
  in `Re(s) > -1`.
- `exists_norm_zeta_mul_Gamma_mul_reflected_le`: the corresponding decay for the product at
  `s` and a reflected argument `c-s`.

## References

- [95, Shintani (1977), proof of Lemma 1, pp. 170--171]
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace SIC

/-! ### Gamma bounds

Euler's integral bounds gamma by its value at the real part. Two recurrences
then give quadratic decay along vertical lines in the right half-plane.
-/

/-- Euler's integral gives `|Gamma(s)| ≤ Gamma(Re(s))` for `Re(s)>0`.
This supplies the bounds in `norm_Gamma_le_div_norm_sq` and `norm_zeta_mul_Gamma_le`. -/
private lemma norm_Gamma_le_Gamma_re (s : ℂ) (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral, Real.Gamma_eq_integral hs]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_cpow_eq_rpow_re_of_pos ht]
  simp

/-- Gamma is analytic on the right half-plane. This supplies the regularity used
in `verticalIntegrable_Gamma`, `mellinInv_trigamma_sub_inv_sq`, and the residue calculation. -/
lemma analyticAt_Gamma_of_re_pos (s : ℂ) (hs : 0 < s.re) :
    AnalyticAt ℂ Complex.Gamma s := by
  have hdiff : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0 < z.re} := by
    intro z hz
    change 0 < z.re at hz
    apply (Complex.differentiableAt_Gamma z _).differentiableWithinAt
    intro n hn
    have hre := congrArg Complex.re hn
    simp only [neg_re, natCast_re] at hre
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  exact hdiff.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)

/-- Translation by one increases the norm on the right half-plane.
This compares the recurrence denominators in `norm_Gamma_le_div_norm_sq`. -/
private lemma norm_le_norm_add_one (s : ℂ) (hs : 0 ≤ s.re) :
    ‖s‖ ≤ ‖s + 1‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [Complex.sq_norm, Complex.normSq_apply, add_re, one_re, add_im, one_im,
    add_zero]
  nlinarith

/-- Two gamma recurrences give `|Gamma(s)| ≤ Gamma(Re(s)+2)/|s|²` for `Re(s)>0`.
This supplies the decay in `verticalIntegrable_Gamma` and `exists_norm_trigamma_mellin_le`. -/
lemma norm_Gamma_le_div_norm_sq (s : ℂ) (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma (s.re + 2) / ‖s‖ ^ 2 := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [add_re, one_re, zero_re] at this
    linarith
  have hrec : Complex.Gamma (s + 2) = (s + 1) * s * Complex.Gamma s := by
    rw [show s + 2 = (s + 1) + 1 by ring,
      Complex.Gamma_add_one (s + 1) hs1, Complex.Gamma_add_one s hs0]
    ring
  have hbound := norm_Gamma_le_Gamma_re (s + 2) (by simp; linarith)
  rw [hrec, norm_mul, norm_mul] at hbound
  simp only [add_re, re_ofNat] at hbound
  apply (le_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hs0))).mpr
  calc
    ‖Complex.Gamma s‖ * ‖s‖ ^ 2 ≤ ‖s + 1‖ * ‖s‖ * ‖Complex.Gamma s‖ := by
      nlinarith [mul_le_mul_of_nonneg_right (norm_le_norm_add_one s hs.le)
        (mul_nonneg (norm_nonneg s) (norm_nonneg (Complex.Gamma s)))]
    _ ≤ Real.Gamma (s.re + 2) := hbound

/-- Gamma is uniformly bounded on every closed strip in `Re(s)>-1` at heights
`|Im(s)|≥1`. A single recurrence moves to the right half-plane, where Euler's
integral gives the bound. This supplies the digamma contour estimates. -/
theorem exists_norm_Gamma_le (a b : ℝ) (ha : -1 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ |s.im| →
      ‖Complex.Gamma s‖ ≤ C := by
  have hc : ContinuousOn (fun x : ℝ => Real.Gamma (x + 1)) (Icc a b) :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.comp (by fun_prop)
      (fun x hx => show 0 < x + 1 by linarith [hx.1])
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hc
  refine ⟨max C 0, le_max_right _ _, fun s hsa hsb hsi => ?_⟩
  have hn : 1 ≤ ‖s‖ := hsi.trans (Complex.abs_im_le_norm s)
  have hs0 : s ≠ 0 := norm_pos_iff.mp (by linarith)
  have hb := norm_Gamma_le_Gamma_re (s + 1) (by simp; linarith)
  rw [Complex.Gamma_add_one s hs0, norm_mul] at hb
  calc
    ‖Complex.Gamma s‖ ≤ ‖s‖ * ‖Complex.Gamma s‖ := by
      nlinarith [norm_nonneg (Complex.Gamma s)]
    _ ≤ Real.Gamma (s.re + 1) := by simpa using hb
    _ ≤ C := hC (mem_image_of_mem _ ⟨hsa, hsb⟩)
    _ ≤ max C 0 := le_max_left _ _

/-! ### Completed-zeta bounds

The modified-theta integral defining the entire part of completed zeta
converges for every Mellin parameter. Powers on a closed strip are bounded by
the two endpoint powers, giving a uniform bound. Adding back the two rational
pole terms preserves boundedness away from zero and one.
-/

/-- The norm of a Mellin transform on `a≤Re(s)≤b` is bounded by the sum of the
absolute integrals on the two boundary lines. This bounds the theta integral defining
`completedRiemannZeta₀` in `exists_norm_completedRiemannZeta₀_le`. -/
private lemma norm_mellin_le_endpoints {f : ℝ → ℂ} {a b : ℝ}
    (ha : MellinConvergent f (a : ℂ)) (hb : MellinConvergent f (b : ℂ))
    {s : ℂ} (hsa : a ≤ s.re) (hsb : s.re ≤ b) :
    ‖mellin f s‖ ≤
      (∫ t : ℝ in Ioi 0, ‖(t : ℂ) ^ ((a : ℂ) - 1) * f t‖) +
      ∫ t : ℝ in Ioi 0, ‖(t : ℂ) ^ ((b : ℂ) - 1) * f t‖ := by
  have hnorm (t : ℝ) (ht : 0 < t) (z : ℂ) :
      ‖(t : ℂ) ^ (z - 1) * f t‖ = t ^ (z.re - 1) * ‖f t‖ := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
    simp
  have hbound (t : ℝ) (ht : t ∈ Ioi 0) :
      ‖(t : ℂ) ^ (s - 1) * f t‖ ≤
        ‖(t : ℂ) ^ ((a : ℂ) - 1) * f t‖ +
        ‖(t : ℂ) ^ ((b : ℂ) - 1) * f t‖ := by
    simp only [hnorm t ht, ofReal_re]
    rw [← add_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact rpow_le_add_of_le ht (sub_le_sub_right hsa 1) (sub_le_sub_right hsb 1)
  have ha' : IntegrableOn (fun t : ℝ => ‖(t : ℂ) ^ ((a : ℂ) - 1) * f t‖) (Ioi 0) := ha.norm
  have hb' : IntegrableOn (fun t : ℝ => ‖(t : ℂ) ^ ((b : ℂ) - 1) * f t‖) (Ioi 0) := hb.norm
  refine (norm_integral_le_of_norm_le (ha'.add hb') ?_).trans_eq (integral_add ha' hb')
  exact (ae_restrict_mem measurableSet_Ioi).mono hbound

/-- The entire part of completed zeta is bounded on every closed vertical strip.
This follows from its defining, everywhere convergent modified-theta Mellin integral,
and supplies `exists_norm_completedRiemannZeta_strip_le` and its vertical-line version. -/
private lemma exists_norm_completedRiemannZeta₀_le (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖completedRiemannZeta₀ s‖ ≤ C := by
  let P := HurwitzZeta.hurwitzEvenFEPair 0
  let f := P.f_modif
  have hf (x : ℝ) : MellinConvergent f (x : ℂ) :=
    (P.isStrongFEPair_toStrongFEPair.hasMellin (x : ℂ)).1
  let C := (∫ t : ℝ in Ioi 0, ‖(t : ℂ) ^ (((a / 2 : ℝ) : ℂ) - 1) * f t‖) +
    ∫ t : ℝ in Ioi 0, ‖(t : ℂ) ^ (((b / 2 : ℝ) : ℂ) - 1) * f t‖
  refine ⟨C / 2, div_nonneg (add_nonneg (integral_nonneg (fun _ => norm_nonneg _))
    (integral_nonneg (fun _ => norm_nonneg _))) (by norm_num), ?_⟩
  intro s hsa hsb
  change ‖mellin f (s / 2) / 2‖ ≤ C / 2
  rw [norm_div, norm_ofNat]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact norm_mellin_le_endpoints (hf (a / 2)) (hf (b / 2))
    (by simpa using (div_le_div_of_nonneg_right hsa (by norm_num : (0:ℝ) ≤ 2)))
    (by simpa using (div_le_div_of_nonneg_right hsb (by norm_num : (0:ℝ) ≤ 2)))

/-- The defining subtraction of the poles at zero and one gives
`|Lambda(w)| ≤ |Lambda_0(w)| + |w|⁻¹ + |1-w|⁻¹`.
This supplies the completed-zeta vertical and strip bounds. -/
private lemma norm_completedRiemannZeta_le (w : ℂ) :
    ‖completedRiemannZeta w‖ ≤
      ‖completedRiemannZeta₀ w‖ + ‖w‖⁻¹ + ‖1 - w‖⁻¹ := by
  rw [completedRiemannZeta_eq]
  calc
    _ ≤ ‖completedRiemannZeta₀ w - 1 / w‖ + ‖1 / (1 - w)‖ := norm_sub_le _ _
    _ ≤ (‖completedRiemannZeta₀ w‖ + ‖1 / w‖) + ‖1 / (1 - w)‖ := by
      gcongr
      exact norm_sub_le _ _
    _ = _ := by simp [one_div]

/-- Completed zeta is bounded on `Re(w)=x` when `x≠0,1`.
This supplies the bounded factor in `verticalIntegrable_trigamma_mellin`. -/
lemma exists_norm_completedRiemannZeta_vertical_le (x : ℝ)
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    ∃ C : ℝ, ∀ w : ℂ, w.re = x → ‖completedRiemannZeta w‖ ≤ C := by
  obtain ⟨C, _, hC⟩ := exists_norm_completedRiemannZeta₀_le x x
  refine ⟨C + |x|⁻¹ + |1 - x|⁻¹, fun w hw => ?_⟩
  apply (norm_completedRiemannZeta_le w).trans
  gcongr
  · exact hC w (by simp [hw]) (by simp [hw])
  · simpa [hw] using Complex.abs_re_le_norm w
  · simpa [hw] using Complex.abs_re_le_norm (1 - w)

/-- Completed zeta is uniformly bounded on `a≤Re(w)≤b`, `|Im(w)|≥1`.
This supplies the completed-zeta factor in `exists_norm_trigamma_mellin_le`. -/
lemma exists_norm_completedRiemannZeta_strip_le (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, a ≤ w.re → w.re ≤ b → 1 ≤ |w.im| →
      ‖completedRiemannZeta w‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_completedRiemannZeta₀_le a b
  refine ⟨C + 1 + 1, by positivity, fun w hwa hwb hwi => ?_⟩
  apply (norm_completedRiemannZeta_le w).trans
  have hn : 1 ≤ ‖w‖ := hwi.trans (Complex.abs_im_le_norm w)
  have hn' : 1 ≤ ‖1 - w‖ := by
    simpa using hwi.trans (by simpa using Complex.abs_im_le_norm (1 - w))
  have hi := inv_le_one_of_one_le₀ hn
  have hi' := inv_le_one_of_one_le₀ hn'
  linarith [hC w hwa hwb]

/-! ### Gamma duplication

Legendre duplication cancels the gamma denominator in the definition of
completed zeta. Euler's bound controls the remaining half-argument gamma
factor. Thus `zeta(w) Gamma(w)` is bounded on every vertical line
`Re(w)>0`, `Re(w)≠1`, which is what lets one integrable gamma factor control
the whole trigamma transform in `SICs.SpecialFunctions.Mellin.TrigammaInversion`.
-/

/-- Away from the zeros of `Gamma_R(w)`,
`zeta(w) Gamma(w) = Lambda(w) Gamma_R(w+1) (2*pi)^w / 2`, where
`Lambda(w)=pi^(-w/2) Gamma(w/2) zeta(w)` and `Gamma_R(w)=pi^(-w/2) Gamma(w/2)`.
This is Legendre duplication, as `Complex.Gammaℝ_mul_Gammaℝ_add_one`, combined with
`riemannZeta_def_of_ne_zero`; it supplies `norm_zeta_mul_Gamma_le`. -/
private lemma zeta_mul_Gamma_eq_completed (w : ℂ) (hwG : Complex.Gammaℝ w ≠ 0) :
    riemannZeta w * Complex.Gamma w =
      completedRiemannZeta w * Complex.Gammaℝ (w + 1) * (2 * Real.pi : ℂ) ^ w / 2 := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hwG (by simp [Complex.Gammaℝ_def, Complex.Gamma_zero])
  have hp : (2 * Real.pi : ℂ) ≠ 0 := mul_ne_zero two_ne_zero
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hdup := Complex.Gammaℝ_mul_Gammaℝ_add_one w
  rw [Complex.Gammaℂ_def, Complex.cpow_neg] at hdup
  have hg : Complex.Gamma w = Complex.Gammaℝ w * Complex.Gammaℝ (w + 1) *
      (2 * Real.pi : ℂ) ^ w / 2 := by
    rw [hdup]
    field_simp
  rw [riemannZeta_def_of_ne_zero hw0, hg]
  field_simp

/-- The positive-real coefficient
`pi^(-(x+1)/2) Gamma((x+1)/2) (2*pi)^x / 2` in `norm_zeta_mul_Gamma_le`. -/
def gammaZetaBound (x : ℝ) : ℝ :=
  Real.pi ^ (-(x + 1) / 2) * Real.Gamma ((x + 1) / 2) * (2 * Real.pi) ^ x / 2

/-- The coefficient in `norm_zeta_mul_Gamma_le` is nonnegative for `x>-1`. -/
lemma gammaZetaBound_nonneg {x : ℝ} (hx : -1 < x) : 0 ≤ gammaZetaBound x := by
  unfold gammaZetaBound
  exact div_nonneg (mul_nonneg
    (mul_nonneg (by positivity) (Real.Gamma_pos_of_pos (by linarith)).le) (by positivity))
    (by norm_num)

/-- The coefficient in `norm_zeta_mul_Gamma_le` is continuous for `x>-1`. -/
lemma continuousOn_gammaZetaBound : ContinuousOn gammaZetaBound (Ioi (-1)) := by
  unfold gammaZetaBound
  apply ContinuousOn.div_const
  apply ContinuousOn.mul
  · apply ContinuousOn.mul
    · exact (Real.continuous_const_rpow Real.pi_ne_zero).comp_continuousOn (by fun_prop)
    · exact Real.differentiableOn_Gamma_Ioi.continuousOn.comp (by fun_prop)
        (fun x hx => show 0 < (x + 1) / 2 by have hx' : -1 < x := hx; linarith)
  · exact (Real.continuous_const_rpow (by positivity)).continuousOn

/-- Euler's gamma bound applied to `zeta_mul_Gamma_eq_completed` bounds
`|zeta(w) Gamma(w)|` by `|Lambda(w)|` times a coefficient depending only on `Re(w)>0`.
This supplies both vertical convergence and strip decay for the trigamma transform. -/
lemma norm_zeta_mul_Gamma_le (w : ℂ) (hw : 0 < w.re) :
    ‖riemannZeta w * Complex.Gamma w‖ ≤ ‖completedRiemannZeta w‖ * gammaZetaBound w.re := by
  unfold gammaZetaBound
  rw [zeta_mul_Gamma_eq_completed w (Complex.Gammaℝ_ne_zero_of_re_pos hw),
    norm_div, norm_mul, norm_mul,
    Complex.Gammaℝ_def, norm_mul,
    show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), norm_ofNat]
  have hg := norm_Gamma_le_Gamma_re ((w + 1) / 2) (by simp; linarith)
  simp only [div_ofNat_re, add_re, one_re, neg_re] at *
  calc
    _ ≤ ‖completedRiemannZeta w‖ *
        (Real.pi ^ (-(w.re + 1) / 2) * Real.Gamma ((w.re + 1) / 2)) *
        (2 * Real.pi) ^ w.re / 2 := by gcongr
    _ = _ := by ring

/-! ### Decay of the zeta--gamma product

For both remainder transforms, the gamma factors are paired with zeta factors.
Apply the quadratic gamma bound to `Gamma((s+1)/2)` in the duplication identity.
The completed-zeta strip bound and compactness in the real part then give
`|zeta(s) Gamma(s)| ≤ C/(1+Im(s)²)` on closed strips in `Re(s)>-1`,
at heights `|Im(s)|≥1`. This supplies the decay implicit in
[95, Shintani (1977), proof of Lemma 1, p. 171, contour shifts for `f₁` and `f₂`].
-/

/-- The coefficient `D(x)=pi^(-(x+1)/2) Gamma((x+1)/2+2) (2pi)^x/2`, obtained
by applying the quadratic gamma bound to `zeta_mul_Gamma_eq_completed`.
It is used in `norm_zeta_mul_Gamma_le_div_norm_sq`. -/
private def gammaZetaDecayBound (x : ℝ) : ℝ :=
  Real.pi ^ (-(x + 1) / 2) * Real.Gamma ((x + 1) / 2 + 2) * (2 * Real.pi) ^ x / 2

/-- The coefficient `gammaZetaDecayBound` is bounded on compact intervals in
`x>-5`, where its gamma argument is positive, for `exists_norm_zeta_mul_Gamma_le`. -/
private lemma exists_gammaZetaDecayBound_le (a b : ℝ) (ha : -5 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc a b, gammaZetaDecayBound x ≤ C := by
  have hc : ContinuousOn gammaZetaDecayBound (Icc a b) := by
    unfold gammaZetaDecayBound
    apply ContinuousOn.div_const
    apply ContinuousOn.mul
    · apply ContinuousOn.mul
      · exact (Real.continuous_const_rpow Real.pi_ne_zero).comp_continuousOn (by fun_prop)
      · exact Real.differentiableOn_Gamma_Ioi.continuousOn.comp (by fun_prop)
          (fun x hx => show 0 < (x + 1) / 2 + 2 by linarith [hx.1])
    · exact (Real.continuous_const_rpow (by positivity)).continuousOn
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hc
  exact ⟨max C 0, le_max_right _ _, fun x hx =>
    (hC (mem_image_of_mem _ hx)).trans (le_max_left _ _)⟩

/-- Duplication and the quadratic gamma bound give
`|zeta(s) Gamma(s)| ≤ |Lambda(s)| D(Re(s))/|(s+1)/2|²` for `Re(s)>-1`,
away from zeros of `Gamma_R(s)`, where `D=gammaZetaDecayBound`.
This supplies `exists_norm_zeta_mul_Gamma_le`. -/
private lemma norm_zeta_mul_Gamma_le_div_norm_sq (s : ℂ) (hs : -1 < s.re)
    (hsG : Complex.Gammaℝ s ≠ 0) :
    ‖riemannZeta s * Complex.Gamma s‖ ≤
      ‖completedRiemannZeta s‖ * gammaZetaDecayBound s.re / ‖(s + 1) / 2‖ ^ 2 := by
  unfold gammaZetaDecayBound
  rw [zeta_mul_Gamma_eq_completed s hsG, norm_div, norm_mul, norm_mul,
    Complex.Gammaℝ_def, norm_mul,
    show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), norm_ofNat]
  have hg := norm_Gamma_le_div_norm_sq ((s + 1) / 2) (by simp; linarith)
  simp only [div_ofNat_re, add_re, one_re, neg_re] at *
  calc
    _ ≤ ‖completedRiemannZeta s‖ *
        (Real.pi ^ (-(s.re + 1) / 2) *
          (Real.Gamma ((s.re + 1) / 2 + 2) / ‖(s + 1) / 2‖ ^ 2)) *
        (2 * Real.pi) ^ s.re / 2 := by gcongr
    _ = _ := by ring

/-- For `|Im(s)|≥1`, `1+Im(s)²≤8|(s+1)/2|²`.
This compares the half-argument denominator in `exists_norm_zeta_mul_Gamma_le`
with the Cauchy kernel used by the horizontal-limit lemmas. -/
private lemma one_add_im_sq_le_eight_half_norm_sq (s : ℂ) (hs : 1 ≤ |s.im|) :
    1 + s.im ^ 2 ≤ 8 * ‖(s + 1) / 2‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [div_ofNat_re, div_ofNat_im, add_re, add_im, one_re, one_im, add_zero]
  nlinarith [sq_abs s.im, sq_nonneg (|s.im| - 1), sq_nonneg (s.re + 1)]

/-- For `-1<a≤Re(s)≤b` and `|Im(s)|≥1`,
`|zeta(s) Gamma(s)| ≤ C/(1+Im(s)²)` for one strip-dependent constant.
This gives the horizontal decay used in [95, Shintani (1977), proof of Lemma 1,
p. 171, contour transformations of `f₁` and `f₂`], by applying the completed-zeta
bound and gamma duplication to each reflected zeta--gamma pair. -/
theorem exists_norm_zeta_mul_Gamma_le (a b : ℝ) (ha : -1 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ |s.im| →
      ‖riemannZeta s * Complex.Gamma s‖ ≤ C / (1 + s.im ^ 2) := by
  obtain ⟨Cz, hCz0, hCz⟩ := exists_norm_completedRiemannZeta_strip_le a b
  obtain ⟨Cg, hCg0, hCg⟩ := exists_gammaZetaDecayBound_le a b (by linarith)
  refine ⟨8 * Cz * Cg, by positivity, fun s hsa hsb hsi => ?_⟩
  have hs : -1 < s.re := ha.trans_le hsa
  have hsim : s.im ≠ 0 := by intro h; norm_num [h] at hsi
  have hsG : Complex.Gammaℝ s ≠ 0 := by
    rw [ne_eq, Complex.Gammaℝ_eq_zero_iff]
    rintro ⟨n, rfl⟩
    exact hsim (by simp)
  have hG : 0 ≤ gammaZetaDecayBound s.re := by
    unfold gammaZetaDecayBound
    have := (Real.Gamma_pos_of_pos (show 0 < (s.re + 1) / 2 + 2 by linarith)).le
    positivity
  have hd := one_add_im_sq_le_eight_half_norm_sq s hsi
  have hn : 0 < ‖(s + 1) / 2‖ ^ 2 := by nlinarith [sq_nonneg s.im]
  calc
    _ ≤ ‖completedRiemannZeta s‖ * gammaZetaDecayBound s.re / ‖(s + 1) / 2‖ ^ 2 :=
      norm_zeta_mul_Gamma_le_div_norm_sq s hs hsG
    _ ≤ Cz * Cg / ‖(s + 1) / 2‖ ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul (hCz s hsa hsb hsi)
        (hCg _ ⟨hsa, hsb⟩) hG hCz0) hn.le
    _ ≤ 8 * Cz * Cg / (1 + s.im ^ 2) := by
      rw [div_le_div_iff₀ hn (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hd (mul_nonneg hCz0 hCg0)]

/-- The product of two zeta--gamma factors related by `s ↦ c-s` has quadratic
decay on any closed strip on which both applications of
`exists_norm_zeta_mul_Gamma_le` are valid. -/
theorem exists_norm_zeta_mul_Gamma_mul_reflected_le (c a b : ℝ)
    (ha : -1 < a) (hcb : -1 < c - b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ |s.im| →
      ‖(riemannZeta s * Complex.Gamma s) *
        (riemannZeta (c - s) * Complex.Gamma (c - s))‖ ≤ C / (1 + s.im ^ 2) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_norm_zeta_mul_Gamma_le a b ha
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_norm_zeta_mul_Gamma_le (c - b) (c - a) hcb
  refine ⟨C₁ * C₂, mul_nonneg hC₁0 hC₂0, fun s hsa hsb hsi => ?_⟩
  have h₂ : ‖riemannZeta (c - s) * Complex.Gamma (c - s)‖ ≤ C₂ := by
    have h : ‖riemannZeta (c - s) * Complex.Gamma (c - s)‖ ≤
        C₂ / (1 + s.im ^ 2) := by
      simpa using hC₂ (c - s) (by simp; linarith) (by simp; linarith) (by simpa)
    exact h.trans (div_le_self hC₂0 (by nlinarith [sq_nonneg s.im]))
  calc
    _ = ‖riemannZeta s * Complex.Gamma s‖ *
        ‖riemannZeta (c - s) * Complex.Gamma (c - s)‖ := norm_mul _ _
    _ ≤ (C₁ / (1 + s.im ^ 2)) * C₂ :=
      mul_le_mul (hC₁ s hsa hsb hsi) h₂ (norm_nonneg _) (by positivity)
    _ = _ := by ring

end SIC

end
