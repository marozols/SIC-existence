/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.Faddeev.FiveTerm.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Closing-side limits for the upper-half-plane five-term kernel

The three closing sides of the rectangular five-term contour have vanishing integrals.

These are the limits required by [RW26, Radchenko, Wheeler (2026), Appendix A.2,
`app:mod.fad`], in the proof of Theorem 3, `thm:5term.mod.fad`, at `n = h = 0`.

## The argument

On the right side, the kernel has exponential decay in the real coordinate and the segment has
fixed length. On the bottom side, both `z` and `z/ε` are low; its bound has a decaying factor in
the height and an integrable exponential in the real coordinate. On the top side, the exponent
changes slope where `Im(z/ε) = 0`. Its values at the left endpoint and at the change of slope
decay by `Re λ > 0` and `Im(ℓτ+w) > 0`, respectively, while its slope to the right is negative
by `Im((w+y)/ε) > 0`. We absorb a small part of the rightward decay to get one integrable
exponential majorant for the entire horizontal side.

The resulting horizontal bounds are a constant times $e^{-\kappa Y}$, uniformly in their finite
right endpoints; they need no factor growing with $Y$.

The source closes with cones. Rectangles give the same residue calculation and use the uniform
region bounds in `SICs.SpecialFunctions.Faddeev.FiveTerm.Bounds`.
-/

noncomputable section

open Complex Real MeasureTheory Filter
open scoped MatrixGroups
open scoped Topology

namespace SIC

/-! ### Exponential majorants and decay

The bound is uniform in the right endpoint. It only uses a pointwise norm bound, so it does not
require measurability of the kernel. -/

/-- A pointwise bound by $B e^{-as}$ on $[x,X]$, where $a>0$, bounds the interval integral by
$B e^{-ax}/a$; used by the bottom and top limits. -/
private lemma norm_intervalIntegral_le_exp_tail {f : ℝ → ℂ} {x X a B : ℝ}
    (hx : x ≤ X) (ha : 0 < a) (hB : 0 ≤ B)
    (hf : ∀ s ∈ Set.Icc x X, ‖f s‖ ≤ B * Real.exp (-a * s)) :
    ‖∫ s in x..X, f s‖ ≤ B * Real.exp (-a * x) / a := by
  have hi : IntegrableOn (fun s : ℝ => B * Real.exp (-a * s)) (Set.Ioi x) := by
    simpa [IntegrableOn, neg_mul] using
      (integrableOn_exp_mul_Ioi (a := -a) (by linarith) x).const_mul B
  have hab : IntervalIntegrable (fun s : ℝ => B * Real.exp (-a * s)) volume x X :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).2
      (hi.mono_set (Set.Ioc_subset_Ioi_self))
  have hn := intervalIntegral.norm_integral_le_of_norm_le hx
    (ae_of_all _ fun s hs => hf s ⟨hs.1.le, hs.2⟩) hab
  calc
    ‖∫ s in x..X, f s‖ ≤ ∫ s in x..X, B * Real.exp (-a * s) := hn
    _ = ∫ s in Set.Ioc x X, B * Real.exp (-a * s) := intervalIntegral.integral_of_le hx
    _ ≤ ∫ s in Set.Ioi x, B * Real.exp (-a * s) :=
      setIntegral_mono_set hi (ae_of_all _ fun _ => mul_nonneg hB (Real.exp_pos _).le)
        (ae_of_all _ fun _ hs => hs.1)
    _ = B * Real.exp (-a * x) / a := by
      rw [integral_const_mul, show (fun s : ℝ => Real.exp (-a * s)) =
        (fun s : ℝ => Real.exp ((-a) * s)) from rfl,
        integral_exp_mul_Ioi (a := -a) (by linarith)]
      ring

/-- A fixed multiple of an affine exponential tends to zero at increasing heights. -/
private lemma tendsto_const_mul_exp_decay {Y : ℕ → ℝ} (hY : Tendsto Y atTop atTop)
    {κ : ℝ} (hκ : 0 < κ) (D B : ℝ) :
    Tendsto (fun n => B * Real.exp (D - κ * Y n)) atTop (𝓝 0) := by
  have h0 : Tendsto (fun n => Real.exp (-(κ * Y n))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (hY.const_mul_atTop hκ)
  convert h0.const_mul (B * Real.exp D) using 1
  · ext n
    rw [sub_eq_add_neg, Real.exp_add]
    ring
  · simp

/-! ### The right closing side

The strip estimate of `exists_norm_fiveTermKernelUHP_le_right` gives a constant bound
along each finite vertical segment, and its exponential factor tends to zero. -/

/-- On a fixed vertical segment, the right-region norm bound gives exponential decay in the
real coordinate; used by the right closing-side limit. -/
private lemma exists_fiveTermClosing_right_integral_bound (γ : SL(2, ℤ))
    (hc : 0 < γ 1 0) (ℓ p m : ℤ) (w y τ : ℂ) (hτ : 0 < τ.im)
    (a b δ : ℝ) (hδ : 0 < δ) :
    ∃ C R : ℝ, ∀ X ≥ R,
      (∀ t ∈ Set.uIcc a b, ∀ u ∈ faddeevModularUHPPoles γ (m + 1) τ,
        δ ≤ ‖((X : ℂ) + t * I) - u‖) →
      ‖∫ t in a..b,
        fiveTermKernelUHP γ ℓ p w y τ m ((X : ℂ) + t * I)‖ ≤
        C * Real.exp (-2 * π * (γ 1 0 : ℝ) *
          ((w + y) / fltDenominator (γ : Mat(2, ℤ)) τ).im * X) * |b - a| := by
  obtain ⟨C, R, hR⟩ := exists_norm_fiveTermKernelUHP_le_right
    γ hc ℓ p w y τ hτ m δ hδ (max |a| |b|)
  refine ⟨|C|, R, ?_⟩
  intro X hX hp
  apply (intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_).trans
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le) (abs_nonneg _)
  have hab : t ∈ Set.uIcc a b := Set.uIoc_subset_uIcc ht
  have hreal : (((X : ℂ) + t * I)).re = X := by simp
  have him : (((X : ℂ) + t * I)).im = t := by simp
  have htp : |t| ≤ max |a| |b| := by
    rcases (Set.mem_uIcc.mp hab) with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact abs_le.mpr ⟨by linarith [neg_abs_le a, le_max_left |a| |b|],
        by linarith [le_abs_self b, le_max_right |a| |b|]⟩
    · exact abs_le.mpr ⟨by linarith [neg_abs_le b, le_max_right |a| |b|],
        by linarith [le_abs_self a, le_max_left |a| |b|]⟩
  have hb := hR _ (by simpa [hreal] using hX) (by simpa [him] using htp)
    (hp t hab)
  rw [hreal] at hb
  simpa only [neg_mul, mul_assoc] using hb

/-- The integral over a fixed-length right side tends to zero as its real coordinate tends to
$+\infty$. This is the right-side limit in [RW26, Radchenko, Wheeler (2026), Appendix A.2,
`app:mod.fad`] for the kernel in equation (23) at $n=h=0$. -/
theorem tendsto_integral_fiveTermKernelUHP_right (γ : SL(2, ℤ))
    (hc : 0 < γ 1 0) (ℓ p m : ℤ) (w y τ : ℂ) (hτ : 0 < τ.im)
    (a b : ℝ) (X : ℕ → ℝ) (hX : Tendsto X atTop atTop)
    (δ : ℝ) (hδ : 0 < δ)
    (hp : ∀ n, ∀ t ∈ Set.uIcc a b, ∀ u ∈ faddeevModularUHPPoles γ (m + 1) τ,
      δ ≤ ‖((X n : ℂ) + t * I) - u‖)
    (hwy : 0 < ((w + y) / fltDenominator (γ : Mat(2, ℤ)) τ).im) :
    Tendsto (fun n => ∫ t in a..b,
      fiveTermKernelUHP γ ℓ p w y τ m ((X n : ℂ) + t * I)) atTop (𝓝 0) := by
  let k : ℝ := 2 * π * (γ 1 0 : ℝ) *
    ((w + y) / fltDenominator (γ : Mat(2, ℤ)) τ).im
  have hk : 0 < k := by dsimp [k]; positivity
  obtain ⟨C, R, hbound⟩ :=
    exists_fiveTermClosing_right_integral_bound γ hc ℓ p m w y τ hτ a b δ hδ
  have hlim : Tendsto (fun n => C * Real.exp (-k * X n) * |b - a|)
      atTop (𝓝 0) := by
    convert tendsto_const_mul_exp_decay hX hk 0 (C * |b - a|) using 1
    ext n
    simp only [zero_sub]
    ring_nf
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (hX.eventually_ge_atTop R |>.mono fun n hn => hbound (X n) hn (hp n))
    (by simpa only [k, neg_mul, mul_assoc] using hlim)

/-! ### The bottom closing side

At sufficiently negative height, both $z$ and $z/ε$ lie in the lower region. The lower kernel
bound then has a negative height exponent because $\operatorname{Re}\mu<0$, and a decaying
real-coordinate exponent because $\operatorname{Im}\mu>0$. -/

/-- The denominator $ε=j_γ(τ)$ has positive imaginary part when $c>0$ and $τ\in\mathbb H$;
used by the lower geometry and the top transition. -/
private lemma fiveTermClosing_denominator_im_pos (γ : SL(2, ℤ))
    (hc : 0 < γ 1 0) (τ : ℂ) (hτ : 0 < τ.im) :
    0 < (fltDenominator (γ : Mat(2, ℤ)) τ).im := by
  have hc' : (0 : ℝ) < (γ 1 0 : ℝ) := by exact_mod_cast hc
  rw [fltDenominator_im]
  exact mul_pos hc' hτ

/-- For $s\ge x$, both $s-iY$ and $(s-iY)/ε$ are low when $Y$ is sufficiently large;
used by `exists_fiveTermClosing_bottom_integral_bound`. -/
private lemma fiveTermClosing_bottom_geometry (e : ℂ) (x T : ℝ)
    (hr : 0 < e.re) (hi : 0 < e.im) :
    ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, ∀ s ≥ x,
      (s - Y * I : ℂ).im ≤ -T ∧ ((s - Y * I : ℂ) / e).im ≤ -T := by
  have hn : 0 < Complex.normSq e := Complex.normSq_pos.mpr (by
    intro he; simp [he] at hr)
  refine ⟨max T ((Complex.normSq e * T - x * e.im) / e.re), ?_⟩
  intro Y hY s hs
  have hYT : T ≤ Y := (le_max_left _ _).trans hY
  have hYr : (Complex.normSq e * T - x * e.im) / e.re ≤ Y :=
    (le_max_right _ _).trans hY
  have hphase : Complex.normSq e * T ≤ Y * e.re + s * e.im := by
    have := (div_le_iff₀ hr).mp hYr
    nlinarith
  constructor
  · simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, mul_zero, zero_sub, mul_one]
    linarith
  · rw [Complex.div_im]
    simp only [Complex.sub_im, Complex.sub_re, Complex.ofReal_im,
      Complex.ofReal_re, Complex.mul_im, Complex.mul_re, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, zero_sub, sub_zero]
    calc
      _ = (-Y * e.re - s * e.im) / Complex.normSq e := by ring
      _ ≤ -T := (div_le_iff₀ hn).2 (by nlinarith [hphase])

/-- The lower-region phase separates into its height and real-coordinate exponents. -/
private lemma fiveTermClosing_bottom_phase (μ : ℂ) (s Y : ℝ) :
    -2 * π * (μ * ((s : ℂ) - Y * I)).im =
      2 * π * μ.re * Y - (2 * π * μ.im) * s := by
  rw [Complex.mul_im]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, sub_zero, zero_sub]
  ring

/-- Below the lower rows, the horizontal integral has an exponential height factor and an
integrable real-coordinate tail; used by the bottom closing-side limit. -/
private lemma exists_fiveTermClosing_bottom_integral_bound (γ : SL(2, ℤ))
    (hc : 0 < γ 1 0) (ℓ p m : ℤ) (w y τ : ℂ) (hτ : 0 < τ.im)
    (he : 0 < (fltDenominator (γ : Mat(2, ℤ)) τ).re)
    (hwy : 0 < ((w + y) / fltDenominator (γ : Mat(2, ℤ)) τ).im)
    (x : ℝ) :
    let μ : ℂ := ((γ 1 0 : ℤ) : ℂ) * (w + y) /
      fltDenominator (γ : Mat(2, ℤ)) τ + ℓ + p - 1
    ∃ C a Y₀ : ℝ, 0 < a ∧ ∀ Y ≥ Y₀, ∀ X ≥ x,
      ‖∫ s in x..X, fiveTermKernelUHP γ ℓ p w y τ m ((s : ℂ) - Y * I)‖ ≤
        (C * Real.exp (2 * π * μ.re * Y)) * Real.exp (-a * x) / a := by
  intro μ
  let e := fltDenominator (γ : Mat(2, ℤ)) τ
  let a : ℝ := 2 * π * μ.im
  have hc' : (0 : ℝ) < (γ 1 0 : ℝ) := by exact_mod_cast hc
  have hμi : μ.im = (γ 1 0 : ℝ) * ((w + y) / e).im := by
    dsimp [μ, e]
    rw [mul_div_assoc]
    simp [Complex.mul_im]
  have ha : 0 < a := by dsimp [a]; rw [hμi]; positivity
  obtain ⟨C, T, hC⟩ := exists_norm_fiveTermKernelUHP_le_lower
    γ ℓ p w y τ hτ m
  obtain ⟨Y₀, hgeom⟩ := fiveTermClosing_bottom_geometry e x T he
    (fiveTermClosing_denominator_im_pos γ hc τ hτ)
  refine ⟨|C|, a, Y₀, ha, ?_⟩
  intro Y hY X hX
  apply norm_intervalIntegral_le_exp_tail hX ha (mul_nonneg (abs_nonneg _)
    (Real.exp_pos _).le)
  intro s hs
  obtain ⟨hz, hze⟩ := hgeom Y hY s hs.1
  have hb := hC ((s : ℂ) - Y * I) hz hze
  calc
    ‖fiveTermKernelUHP γ ℓ p w y τ m ((s : ℂ) - Y * I)‖
        ≤ C * Real.exp (-2 * π * (μ * ((s : ℂ) - Y * I)).im) := hb
    _ ≤ |C| * Real.exp (-2 * π * (μ * ((s : ℂ) - Y * I)).im) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
    _ = (|C| * Real.exp (2 * π * μ.re * Y)) * Real.exp (-a * s) := by
      rw [fiveTermClosing_bottom_phase, sub_eq_add_neg, Real.exp_add]
      dsimp [a]
      ring_nf

/-- The bottom horizontal integral tends to zero as its height tends to $-\infty$, uniformly
in every finite right endpoint $X\ge x$. This is the lower closing-side limit in [RW26,
Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`] at $n=h=0$. -/
theorem tendsto_integral_fiveTermKernelUHP_bottom (γ : SL(2, ℤ))
    (hc : 0 < γ 1 0) (ℓ p m : ℤ) (w y τ : ℂ) (hτ : 0 < τ.im)
    (he : 0 < (fltDenominator (γ : Mat(2, ℤ)) τ).re)
    (hμ : (((γ 1 0 : ℤ) : ℂ) * (w + y) /
      fltDenominator (γ : Mat(2, ℤ)) τ + ℓ + p - 1).re < 0)
    (hwy : 0 < ((w + y) / fltDenominator (γ : Mat(2, ℤ)) τ).im)
    (x : ℝ) (Y X : ℕ → ℝ) (hY : Tendsto Y atTop atTop)
    (hX : ∀ n, x ≤ X n) :
    Tendsto (fun n => ∫ s in x..X n,
      fiveTermKernelUHP γ ℓ p w y τ m ((s : ℂ) - Y n * I)) atTop (𝓝 0) := by
  let μ : ℂ := ((γ 1 0 : ℤ) : ℂ) * (w + y) /
    fltDenominator (γ : Mat(2, ℤ)) τ + ℓ + p - 1
  obtain ⟨C, a, Y₀, ha, hbound⟩ :=
    exists_fiveTermClosing_bottom_integral_bound γ hc ℓ p m w y τ hτ he hwy x
  have hκ : 0 < -(2 * π * μ.re) :=
    neg_pos.mpr (mul_neg_of_pos_of_neg (by positivity) hμ)
  have hlim : Tendsto (fun n =>
      (C * Real.exp (2 * π * μ.re * Y n)) * Real.exp (-a * x) / a)
      atTop (𝓝 0) := by
    convert tendsto_const_mul_exp_decay hY hκ 0 (C * Real.exp (-a * x) / a)
      using 1
    ext n
    simp only [zero_sub]
    have hex : -(-(2 * π * μ.re) * Y n) = 2 * π * μ.re * Y n := by ring
    rw [hex]
    ring
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (hY.eventually_ge_atTop Y₀ |>.mono fun n hn => hbound (Y n) hn (X n) (hX n)) hlim

/-! ### The top closing side

Above the upper rows of zeros, the top bound has two affine exponents. Their common value at
$s=Y\operatorname{Re}ε/\operatorname{Im}ε$ decays by $\operatorname{Im}(ℓτ+w)>0$; to its right,
the slope is $-2πc\operatorname{Im}((w+y)/ε)<0$. Absorbing part of that slope yields the
uniform $C e^{D-\kappa Y-as}$ envelope for every $s\ge x$, regardless of the sign of
$\operatorname{Im}\lambda$. -/

/-- The phase at the top-side change of slope is
$\operatorname{Re}\lambda+(\operatorname{Re}ε/\operatorname{Im}ε)
\operatorname{Im}\lambda=\operatorname{Im}(ℓτ+w)/\operatorname{Im}τ$;
used by `fiveTermClosing_top_exponent_envelope`. -/
private lemma fiveTermClosing_crossing_rate (γ : SL(2, ℤ))
    (hc : 0 < γ 1 0) (ℓ : ℤ) (w τ : ℂ) (hτ : 0 < τ.im) :
    let e := fltDenominator (γ : Mat(2, ℤ)) τ
    let L : ℂ := ((γ 1 0 : ℤ) : ℂ) * w / e + ℓ
    L.re + L.im * (e.re / e.im) = (ℓ * τ + w).im / τ.im := by
  intro e L
  have hei : e.im = (γ 1 0 : ℝ) * τ.im := fltDenominator_im (γ : Mat(2, ℤ)) τ
  have heipos : 0 < e.im := fiveTermClosing_denominator_im_pos γ hc τ hτ
  have hene : e ≠ 0 := by intro hz; simp [hz] at heipos
  have hprod : L * e = ((γ 1 0 : ℤ) : ℂ) * w + ℓ * e := by
    dsimp [L]
    field_simp [hene]
  have him := congrArg Complex.im hprod
  simp only [Complex.mul_im, Complex.add_im, Complex.intCast_re, Complex.intCast_im,
    zero_mul, add_zero] at him
  have htarget : L.re * e.im + L.im * e.re =
      (γ 1 0 : ℝ) * (ℓ * τ + w).im := by
    calc
      _ = (γ 1 0 : ℝ) * w.im + (ℓ : ℝ) * e.im := him
      _ = (γ 1 0 : ℝ) * (ℓ * τ + w).im := by
        rw [hei]
        simp [Complex.mul_im]
        ring
  have hc' : (γ 1 0 : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  apply (eq_div_iff hτ.ne').2
  calc
    (L.re + L.im * (e.re / e.im)) * τ.im =
        (L.re * e.im + L.im * e.re) / (γ 1 0 : ℝ) := by
      rw [hei]
      field_simp [hτ.ne', hc']
    _ = (ℓ * τ + w).im := by rw [htarget]; field_simp [hc']

/-- The top exponent to the right of the change of slope equals its crossing value plus
$-2πc\operatorname{Im}((w+y)/ε)$ times the distance to the right; used by the top envelope. -/
private lemma fiveTermClosing_top_phase_right (γ : SL(2, ℤ))
    (hc : 0 < γ 1 0) (ℓ : ℤ) (w y τ : ℂ) (hτ : 0 < τ.im) (s Y : ℝ) :
    let e := fltDenominator (γ : Mat(2, ℤ)) τ
    let L : ℂ := ((γ 1 0 : ℤ) : ℂ) * w / e + ℓ
    let z : ℂ := s + Y * I
    (-2 * π * (L * z).im +
        2 * π * (y / e).im * (z / e).im / (flt (γ : Mat(2, ℤ)) τ).im) =
      -2 * π * (L.re + L.im * (e.re / e.im)) * Y -
        (2 * π * (γ 1 0 : ℝ) * ((w + y) / e).im) *
          (s - (e.re / e.im) * Y) := by
  intro e L z
  have hei : e.im = (γ 1 0 : ℝ) * τ.im := fltDenominator_im (γ : Mat(2, ℤ)) τ
  have hLi : L.im = (γ 1 0 : ℝ) * (w / e).im := by
    dsimp [L]
    rw [mul_div_assoc]
    simp [Complex.mul_im]
  have hwy : ((w + y) / e).im = (w / e).im + (y / e).im := by
    rw [add_div, Complex.add_im]
  have hphase := fiveTerm_right_phase γ ℓ w y z τ hτ
  rw [hphase]
  simp only [show z.re = s by simp [z], show z.im = Y by simp [z]]
  rw [hwy, hLi, hei]
  have hc' : (γ 1 0 : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  dsimp only [L, e]
  field_simp [hτ.ne', hc']
  ring

/-- The sign of $\operatorname{Im}((s+iY)/ε)$ changes at
$s=Y\operatorname{Re}ε/\operatorname{Im}ε$; used by the top envelope. -/
private lemma fiveTermClosing_top_quotient_sign (e : ℂ) (he : 0 < e.im) (s Y : ℝ) :
    (s ≤ e.re / e.im * Y → 0 ≤ (((s : ℂ) + Y * I) / e).im) ∧
    (e.re / e.im * Y ≤ s → (((s : ℂ) + Y * I) / e).im ≤ 0) := by
  have hn : 0 < Complex.normSq e := Complex.normSq_pos.mpr (by
    intro hz; simp [hz] at he)
  have hcut : (e.re / e.im * Y) * e.im = e.re * Y := by
    field_simp [he.ne']
  have hdiv : (((s : ℂ) + Y * I) / e).im =
      (Y * e.re - s * e.im) / Complex.normSq e := by
    rw [Complex.div_im]
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
    ring
  constructor
  · intro hs
    rw [hdiv]
    have hprod := mul_le_mul_of_nonneg_right hs he.le
    rw [hcut] at hprod
    exact div_nonneg (by nlinarith) hn.le
  · intro hs
    rw [hdiv]
    have hprod := mul_le_mul_of_nonneg_right hs he.le
    rw [hcut] at hprod
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) hn.le

/-- A small part $a>0$ of the negative rightward slope makes the two affine top exponents
bounded by $D-\kappa Y-as$ for $s\ge x$; used by the top limit. -/
private lemma fiveTermClosing_hinge_envelope (lr li r A h x κ a Y s E : ℝ)
    (hcross : h = lr + li * r) (hY : 0 ≤ Y) (hs : x ≤ s)
    (hκ : 0 ≤ κ) (hκr : κ ≤ π * lr) (hκh : κ ≤ π * h)
    (ha : 0 ≤ a) (haA : a ≤ A) (har : a * |r| ≤ κ)
    (hleft : s ≤ r * Y → E = -2 * π * (li * s + lr * Y))
    (hright : r * Y ≤ s → E = -2 * π * h * Y - A * (s - r * Y)) :
    E ≤ |(a - 2 * π * li) * x| - κ * Y - a * s := by
  have har' : a * r ≤ κ := (mul_le_mul_of_nonneg_left (le_abs_self r) ha).trans har
  have hdec : (-2 * π * h + a * r) * Y ≤ -κ * Y := by
    have hd : 0 ≤ 2 * π * h - a * r - κ := by linarith
    nlinarith [mul_nonneg hd hY]
  have hrewrite : (a - 2 * π * li) * (r * Y) - 2 * π * lr * Y =
      (-2 * π * h + a * r) * Y := by rw [hcross]; ring
  by_cases hsr : s ≤ r * Y
  · rw [hleft hsr]
    by_cases hsign : 0 ≤ a - 2 * π * li
    · have hstep := mul_le_mul_of_nonneg_left hsr hsign
      nlinarith [hstep, hdec, hrewrite, abs_nonneg ((a - 2 * π * li) * x)]
    · have hstep := mul_le_mul_of_nonpos_left hs (le_of_not_ge hsign)
      have hd : 0 ≤ 2 * π * lr - κ := by linarith
      nlinarith [hstep, mul_nonneg hd hY,
        le_abs_self ((a - 2 * π * li) * x)]
  · have hsr' : r * Y ≤ s := le_of_not_ge hsr
    rw [hright hsr']
    have hstep : 0 ≤ (A - a) * (s - r * Y) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [hstep, hdec, abs_nonneg ((a - 2 * π * li) * x)]

/-- Positive height and real-coordinate decay rates can be chosen for either sign of the
left-side slope $\operatorname{Im}\lambda$. -/
private lemma fiveTermClosing_envelope_rates (lr h A r : ℝ)
    (hlr : 0 < lr) (hh : 0 < h) (hA : 0 < A) :
    let κ := min (π * lr) (π * h)
    let a := min (A / 2) (κ / (2 * (1 + |r|)))
    0 < κ ∧ 0 < a ∧ a ≤ A ∧ a * |r| ≤ κ := by
  intro κ a
  have hκ : 0 < κ := lt_min (by positivity) (by positivity)
  have ha : 0 < a := lt_min (by positivity) (by positivity)
  have haA : a ≤ A := (min_le_left _ _).trans (by linarith [hA])
  have har : a * |r| ≤ κ := by
    have hsmall : a * (2 * (1 + |r|)) ≤ κ :=
      (le_div_iff₀ (by positivity : 0 < 2 * (1 + |r|))).mp (min_le_right _ _)
    nlinarith [abs_nonneg r, ha.le]
  exact ⟨hκ, ha, haA, har⟩

/-- The upper-region exponent is bounded by $D-\kappa Y-as$ for every $s\ge x$ and $Y\ge0$.
The estimate uses only $\operatorname{Re}\lambda>0$, $\operatorname{Im}(\ell\tau+w)>0$, and
$\operatorname{Im}((w+y)/ε)>0$; the slope $\operatorname{Im}\lambda$ may have either sign. -/
private lemma fiveTermClosing_top_exponent_envelope (γ : SL(2, ℤ))
    (hc : 0 < γ 1 0) (ℓ : ℤ) (w y τ : ℂ) (hτ : 0 < τ.im)
    (hLam : 0 < ((((γ 1 0 : ℤ) : ℂ) * w /
      fltDenominator (γ : Mat(2, ℤ)) τ + ℓ)).re)
    (hℓ : 0 < (ℓ * τ + w).im)
    (hwy : 0 < ((w + y) / fltDenominator (γ : Mat(2, ℤ)) τ).im)
    (x Y s : ℝ) (hY : 0 ≤ Y) (hs : x ≤ s) :
    let e := fltDenominator (γ : Mat(2, ℤ)) τ
    let L : ℂ := ((γ 1 0 : ℤ) : ℂ) * w / e + ℓ
    let r : ℝ := e.re / e.im
    let h : ℝ := (ℓ * τ + w).im / τ.im
    let A : ℝ := 2 * π * (γ 1 0 : ℝ) * ((w + y) / e).im
    let κ : ℝ := min (π * L.re) (π * h)
    let a : ℝ := min (A / 2) (κ / (2 * (1 + |r|)))
    let D : ℝ := |(a - 2 * π * L.im) * x|
    let z : ℂ := s + Y * I
    let E : ℝ := -2 * π * (L * z).im +
      2 * π * (y / e).im * min (z / e).im 0 / (flt (γ : Mat(2, ℤ)) τ).im
    E ≤ D - κ * Y - a * s := by
  intro e L r h A κ a D z E
  have hc' : (0 : ℝ) < (γ 1 0 : ℝ) := by exact_mod_cast hc
  have hh : 0 < h := div_pos hℓ hτ
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨hκ, ha, haA, har⟩ :=
    fiveTermClosing_envelope_rates L.re h A r hLam hh hA
  have hcross : h = L.re + L.im * r := by
    simpa only [e, L, r, h] using
      (fiveTermClosing_crossing_rate γ hc ℓ w τ hτ).symm
  have hei : 0 < e.im := fiveTermClosing_denominator_im_pos γ hc τ hτ
  obtain ⟨hql, hqr⟩ := fiveTermClosing_top_quotient_sign e hei s Y
  have hzre : z.re = s := by simp [z]
  have hzim : z.im = Y := by simp [z]
  have hleft : s ≤ r * Y → E = -2 * π * (L.im * s + L.re * Y) := by
    intro hsr
    have hq : 0 ≤ (z / e).im := hql hsr
    simp only [E, min_eq_right hq, mul_zero, zero_div, add_zero, Complex.mul_im,
      hzre, hzim]
    ring
  have hright : r * Y ≤ s → E = -2 * π * h * Y - A * (s - r * Y) := by
    intro hsr
    have hq : (z / e).im ≤ 0 := hqr hsr
    simp only [E, min_eq_left hq]
    simpa only [e, L, z, h, A, r, hcross] using
      fiveTermClosing_top_phase_right γ hc ℓ w y τ hτ s Y
  exact fiveTermClosing_hinge_envelope L.re L.im r A h x κ a Y s E
    hcross hY hs hκ.le (min_le_left _ _) (min_le_right _ _)
    ha.le haA har hleft hright

/-- An affine exponent bound gives a positive, factorized exponential majorant. -/
private lemma fiveTermClosing_exp_envelope (C E D κ a Y s : ℝ)
    (hE : E ≤ D - κ * Y - a * s) :
    C * Real.exp E ≤ (|C| * Real.exp (D - κ * Y)) * Real.exp (-a * s) := by
  calc
    C * Real.exp E ≤ |C| * Real.exp E :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
    _ ≤ |C| * Real.exp (D - κ * Y - a * s) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hE) (abs_nonneg _)
    _ = (|C| * Real.exp (D - κ * Y)) * Real.exp (-a * s) := by
      rw [show D - κ * Y - a * s = (D - κ * Y) + -a * s by ring,
        Real.exp_add]
      ring

/-- Above the upper rows, the kernel has the uniform envelope
$C e^{D-\kappa Y-as}$ for $s\ge x$ at sufficiently high pole-free heights. -/
private lemma exists_fiveTermClosing_top_kernel_envelope (γ : SL(2, ℤ))
    (hc : 0 < γ 1 0) (ℓ p m : ℤ) (w y τ : ℂ) (hτ : 0 < τ.im)
    (hLam : 0 < ((((γ 1 0 : ℤ) : ℂ) * w /
      fltDenominator (γ : Mat(2, ℤ)) τ + ℓ)).re)
    (hℓ : 0 < (ℓ * τ + w).im)
    (hwy : 0 < ((w + y) / fltDenominator (γ : Mat(2, ℤ)) τ).im)
    (x δ : ℝ) (hδ : 0 < δ) :
    ∃ C κ a D Y₀ : ℝ, 0 ≤ C ∧ 0 < κ ∧ 0 < a ∧
      ∀ Y ≥ Y₀, ∀ s ≥ x,
        (∀ u ∈ faddeevModularUHPPoles γ (m + 1) τ,
          δ ≤ ‖((s : ℂ) + Y * I) - u‖) →
        ‖fiveTermKernelUHP γ ℓ p w y τ m ((s : ℂ) + Y * I)‖ ≤
          (C * Real.exp (D - κ * Y)) * Real.exp (-a * s) := by
  let e := fltDenominator (γ : Mat(2, ℤ)) τ
  let L : ℂ := ((γ 1 0 : ℤ) : ℂ) * w / e + ℓ
  let r : ℝ := e.re / e.im
  let h : ℝ := (ℓ * τ + w).im / τ.im
  let A : ℝ := 2 * π * (γ 1 0 : ℝ) * ((w + y) / e).im
  let κ : ℝ := min (π * L.re) (π * h)
  let a : ℝ := min (A / 2) (κ / (2 * (1 + |r|)))
  let D : ℝ := |(a - 2 * π * L.im) * x|
  have hc' : (0 : ℝ) < (γ 1 0 : ℝ) := by exact_mod_cast hc
  have hh : 0 < h := div_pos hℓ hτ
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨hκ, ha, _, _⟩ := fiveTermClosing_envelope_rates L.re h A r hLam hh hA
  obtain ⟨C, T, hC⟩ := exists_norm_fiveTermKernelUHP_le_top
    γ ℓ p w y τ hτ m δ hδ
  refine ⟨|C|, κ, a, D, max T 0, abs_nonneg _, hκ, ha, ?_⟩
  intro Y hY s hs hp
  have hYn : 0 ≤ Y := (le_max_right _ _).trans hY
  let z : ℂ := (s : ℂ) + Y * I
  let E : ℝ := -2 * π * (L * z).im +
    2 * π * (y / e).im * min (z / e).im 0 / (flt (γ : Mat(2, ℤ)) τ).im
  have hE : E ≤ D - κ * Y - a * s :=
    fiveTermClosing_top_exponent_envelope γ hc ℓ w y τ hτ hLam hℓ hwy
      x Y s hYn hs
  have hb := hC z (by simpa [z] using (le_max_left _ _).trans hY) hp
  exact hb.trans (fiveTermClosing_exp_envelope C E D κ a Y s hE)

/-- The upper horizontal integral has the uniform bound
$C e^{D-\kappa Y}e^{-ax}/a$ at sufficiently high pole-free heights. -/
private lemma exists_fiveTermClosing_top_integral_bound (γ : SL(2, ℤ))
    (hc : 0 < γ 1 0) (ℓ p m : ℤ) (w y τ : ℂ) (hτ : 0 < τ.im)
    (hLam : 0 < ((((γ 1 0 : ℤ) : ℂ) * w /
      fltDenominator (γ : Mat(2, ℤ)) τ + ℓ)).re)
    (hℓ : 0 < (ℓ * τ + w).im)
    (hwy : 0 < ((w + y) / fltDenominator (γ : Mat(2, ℤ)) τ).im)
    (x δ : ℝ) (hδ : 0 < δ) :
    ∃ C κ a D Y₀ : ℝ, 0 < κ ∧ 0 < a ∧
      ∀ Y ≥ Y₀, ∀ X ≥ x,
        (∀ s ≥ x, ∀ u ∈ faddeevModularUHPPoles γ (m + 1) τ,
          δ ≤ ‖((s : ℂ) + Y * I) - u‖) →
        ‖∫ s in x..X,
          fiveTermKernelUHP γ ℓ p w y τ m ((s : ℂ) + Y * I)‖ ≤
          (C * Real.exp (D - κ * Y)) * Real.exp (-a * x) / a := by
  obtain ⟨C, κ, a, D, Y₀, hC, hκ, ha, hbound⟩ :=
    exists_fiveTermClosing_top_kernel_envelope γ hc ℓ p m w y τ hτ hLam hℓ hwy
      x δ hδ
  refine ⟨C, κ, a, D, Y₀, hκ, ha, ?_⟩
  intro Y hY X hX hp
  apply norm_intervalIntegral_le_exp_tail hX ha
    (mul_nonneg hC (Real.exp_pos _).le)
  intro s hs
  exact hbound Y hY s hs.1 (hp s hs.1)

/-- The upper horizontal integral tends to zero as its height tends to $+\infty$, uniformly
for finite right endpoints $X\ge x$. The pole separation is required only at the chosen top
heights. This is the upper closing-side limit in [RW26, Radchenko, Wheeler (2026), Appendix A.2,
`app:mod.fad`] at $n=h=0$. -/
theorem tendsto_integral_fiveTermKernelUHP_top (γ : SL(2, ℤ))
    (hc : 0 < γ 1 0) (ℓ p m : ℤ) (w y τ : ℂ) (hτ : 0 < τ.im)
    (hLam : 0 < ((((γ 1 0 : ℤ) : ℂ) * w /
      fltDenominator (γ : Mat(2, ℤ)) τ + ℓ)).re)
    (hℓ : 0 < (ℓ * τ + w).im)
    (hwy : 0 < ((w + y) / fltDenominator (γ : Mat(2, ℤ)) τ).im)
    (x : ℝ) (Y X : ℕ → ℝ) (hY : Tendsto Y atTop atTop)
    (hX : ∀ n, x ≤ X n) (δ : ℝ) (hδ : 0 < δ)
    (hp : ∀ n, ∀ s ≥ x, ∀ u ∈ faddeevModularUHPPoles γ (m + 1) τ,
      δ ≤ ‖((s : ℂ) + Y n * I) - u‖) :
    Tendsto (fun n => ∫ s in x..X n,
      fiveTermKernelUHP γ ℓ p w y τ m ((s : ℂ) + Y n * I)) atTop (𝓝 0) := by
  obtain ⟨C, κ, a, D, Y₀, hκ, ha, hbound⟩ :=
    exists_fiveTermClosing_top_integral_bound γ hc ℓ p m w y τ hτ hLam hℓ hwy x δ hδ
  have hlim : Tendsto (fun n =>
      (C * Real.exp (D - κ * Y n)) * Real.exp (-a * x) / a) atTop (𝓝 0) := by
    convert tendsto_const_mul_exp_decay hY hκ D (C * Real.exp (-a * x) / a)
      using 1
    ext n
    ring
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (hY.eventually_ge_atTop Y₀ |>.mono fun n hn => hbound (Y n) hn (X n) (hX n)
      (hp n)) hlim

end SIC
