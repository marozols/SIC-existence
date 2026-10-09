/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.Faddeev.Divisor
import SICs.SpecialFunctions.HyperbolicGamma.Asymptotics
import SICs.SpecialFunctions.QPochhammer.Bounds

/-!
# Asymptotics of the Faddeev generator at real periods

At a positive real period, `Φ_{S,0,0}(z;τ) → 1` as `z → ∞` in any upper sector.

This module proves the upper-sector limit behind [RW26, Radchenko, Wheeler (2026), Lemma 1,
`lem:asymp`] for the generator `Φ_{S,0,0}`, the case `γ = S`, `m = n = 0`, which the source
attributes to GKZ and reduces to the asymptotics of Faddeev's quantum dilogarithm. Those
asymptotics are stated without proof in the source and in J. E. Andersen and R. Kashaev,
*A TQFT from quantum Teichmüller theory*, Comm. Math. Phys. 330 (2014), Appendix A,
arXiv:1109.6295v2; the proof here follows S. N. M. Ruijsenaars, *First order analytic difference
equations and integrable quantum systems*, J. Math. Phys. 38 (1997), Proposition III.4,
[doi:10.1063/1.531809](https://doi.org/10.1063/1.531809), through
`SICs.SpecialFunctions.HyperbolicGamma.Asymptotics`. The sector forms are the bounds on
bounded real translates of vertical rays that the contour integrals of
[RW26, Radchenko, Wheeler (2026), Theorem 3, `thm:5term.mod.fad`] need.

## The argument

With `u = z + (1-τ)/2` and `w = -iu`, the generator is
`Φ(z;τ) = S₂(z+1;1,τ) e^{-X(z,τ)}`, `S₂(z+1;1,τ) = exp(i g(τ,1;w))`, and
`-X(z,τ) = -πiu²/(2τ) + (πi/24)(τ + τ⁻¹) = i(πw²/(2τ) + (π/24)(τ + τ⁻¹))`. Hence
`Φ(z;τ) = exp(i R(w))` with `R(w) = g(τ,1;w) + πw²/(2τ) + (π/24)(τ+τ⁻¹)` on the vertical strip
`-1 < Re z < τ`, where `Re w = Im z` and `Im w = -Re u`. Proposition III.4 makes `R(w)`
exponentially small as `Im z → ∞`, uniformly for `Re z` in a compact subinterval, so
`Φ(z;τ) → 1` there.

The strip has width `τ + 1 > 1`, so every `z` is `z₀ + n` with `n ∈ ℤ` and `Re z₀` in the
unit window `[τ/2 - 1, τ/2]`. The period-one shift gives `Φ(z₀ + n) ϖ_n((z₀+1)/τ, 1/τ) = Φ(z₀)`.
For real `τ` every factor of the finite symbol differs from one by a term of modulus
`δ = e^{-2π Im z/τ}`, so the symbol is within `exp(|n|δ/(1-δ)) - 1` of one. When
`|Re z| ≤ K Im z`, `|n| δ ≤ (K Im z + C) e^{-2π Im z/τ} → 0`, and `Φ(z;τ) → 1` in the sector.
-/

noncomputable section

open Complex Filter Asymptotics Set
open scoped Topology

namespace SIC

/-! ### The generator on its vertical strip

On `-1 < Re z < τ` the double sine is the hyperbolic gamma function, and the exponential
normalization of the generator cancels the quadratic part of its logarithm. -/

/-- On the vertical strip `-1 < Re z < τ`, `Φ_{S,0,0}(z;τ) = exp(i R(w))` with
`w = -i(z + (1-τ)/2)` and `R(w) = g(τ,1;w) + πw²/(2τ) + (π/24)(τ + τ⁻¹)`, where `g` is
Ruijsenaars' logarithm of the hyperbolic gamma function. This combines
`shintaniDoubleSineGamma_eq_exp_hyperbolicGammaLog` with the normalization exponent `X`. -/
theorem faddeevS_eq_exp_hyperbolicGammaLog (z : ℂ) (τ : ℝ) (hτ : 0 < τ) (hz : -1 < z.re)
    (hzτ : z.re < τ) :
    faddeevS z τ = Complex.exp (I * (hyperbolicGammaLog τ 1 (-I * (z + (1 - τ) / 2)) +
      Real.pi * (-I * (z + (1 - τ) / 2)) ^ 2 / (2 * τ) +
        Real.pi / 24 * ((τ : ℂ) + (τ : ℂ)⁻¹))) := by
  have hlow : 0 < (z + 1).re := by simp; linarith
  have hupper : (z + 1).re < τ + 1 := by simp; linarith
  have hw : -I * (z + 1 - ((τ : ℂ) + 1) / 2) =
      -I * (z + (1 - τ) / 2) := by ring
  rw [faddeevS, shintaniDoubleSineGamma_eq_exp_hyperbolicGammaLog
    (z + 1) τ hτ hlow hupper, hw, ← Complex.exp_add]
  congr 1
  unfold faddeevSExpArg
  have hτne : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  have hI : (I : ℂ) ^ 2 = -1 := I_sq
  field_simp
  rw [hI]
  ring

/-- A closed real interval inside `-1 < Re z < τ` gives a closed substrip for the
hyperbolic gamma argument; used by `tendsto_faddeevS_of_re_mem_Icc`. -/
private lemma faddeevS_closed_substrip (τ b₁ b₂ : ℝ)
    (hb₁ : -1 < b₁) (hb₂ : b₂ < τ) (horder : b₁ ≤ b₂) :
    let d := (1 - τ) / 2
    let c := max |b₁ + d| |b₂ + d|
    c < (τ + 1) / 2 ∧
      ∀ z : ℂ, z.re ∈ Icc b₁ b₂ → |(-I * (z + d)).im| ≤ c := by
  dsimp
  let d : ℝ := (1 - τ) / 2
  let c : ℝ := max |b₁ + d| |b₂ + d|
  have hclt : c < (τ + 1) / 2 := by
    dsimp [c, d]
    rw [max_lt_iff]
    constructor <;> apply abs_lt.mpr <;> constructor <;> nlinarith
  refine ⟨hclt, ?_⟩
  intro z hz
  have him : (-I * (z + d)).im = -(z.re + d) := by simp [Complex.mul_im]
  rw [him, abs_neg]
  apply abs_le.mpr
  constructor
  · have hc₁ : -c ≤ b₁ + d :=
      (abs_le.mp (le_max_left |b₁ + d| |b₂ + d|)).1
    linarith [hz.1]
  · have hc₂ : b₂ + d ≤ c :=
      (abs_le.mp (le_max_right |b₁ + d| |b₂ + d|)).2
    linarith [hz.2]

/-- Ruijsenaars' remainder tends to zero on a closed hyperbolic-gamma substrip;
used by `tendsto_faddeevS_of_re_mem_Icc`. -/
private lemma tendsto_hyperbolicGamma_remainder_of_strip {α : Type*} {l : Filter α}
    (w : α → ℂ) (τ c : ℝ) (hτ : 0 < τ) (hc : c < (τ + 1) / 2)
    (hre : Tendsto (fun a => (w a).re) l atTop)
    (him : ∀ᶠ a in l, |(w a).im| ≤ c) :
    Tendsto (fun a => hyperbolicGammaLog τ 1 (w a) +
      Real.pi * (w a) ^ 2 / (2 * τ) +
        Real.pi / 24 * ((τ : ℂ) + (τ : ℂ)⁻¹)) l (𝓝 0) := by
  have hmax : 0 < max τ 1 := lt_of_lt_of_le hτ (le_max_left _ _)
  let ε : ℝ := Real.pi / max τ 1
  have hε : 0 < ε := div_pos Real.pi_pos hmax
  obtain ⟨C, hC⟩ := norm_hyperbolicGammaLog_add_le hτ (by norm_num : (0 : ℝ) < 1)
    hε hc
  have hrate : ε - 2 * Real.pi / max τ 1 < 0 := by
    have heq : ε - 2 * Real.pi / max τ 1 = -ε := by dsimp [ε]; ring
    rw [heq]
    linarith
  have hmajor : Tendsto (fun a => C * Real.exp
      ((ε - 2 * Real.pi / max τ 1) * (w a).re)) l (𝓝 0) := by
    have hbot : Tendsto (fun a => (ε - 2 * Real.pi / max τ 1) * (w a).re)
        l atBot := hre.const_mul_atTop_of_neg hrate
    simpa only [Function.comp_apply, mul_zero] using
      (Real.tendsto_exp_atBot.comp hbot).const_mul C
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply Filter.Tendsto.squeeze' tendsto_const_nhds hmajor
  · exact Filter.Eventually.of_forall fun a => norm_nonneg _
  · filter_upwards [hre.eventually (eventually_ge_atTop 0), him] with a ha hb
    simpa [ε, div_eq_mul_inv, mul_assoc] using hC (w a) ha hb

/-- On a vertical strip `b₁ ≤ Re z ≤ b₂` with `-1 < b₁` and `b₂ < τ`, the generator tends to
one as `Im z → +∞`: the upper clause of [RW26, Radchenko, Wheeler (2026), Lemma 1,
`lem:asymp`] on a strip, from Ruijsenaars (1997), Proposition III.4, through
`faddeevS_eq_exp_hyperbolicGammaLog`. -/
theorem tendsto_faddeevS_of_re_mem_Icc {α : Type*} {l : Filter α} (z : α → ℂ) (τ : ℝ)
    (hτ : 0 < τ) {b₁ b₂ : ℝ} (hb₁ : -1 < b₁) (hb₂ : b₂ < τ)
    (hz : Tendsto (fun a => (z a).im) l atTop)
    (hre : ∀ᶠ a in l, (z a).re ∈ Icc b₁ b₂) :
    Tendsto (fun a => faddeevS (z a) τ) l (𝓝 1) := by
  by_cases horder : b₁ ≤ b₂
  swap
  · have hfalse : ∀ᶠ a in l, False := hre.mono fun _ ha =>
      horder (ha.1.trans ha.2)
    rw [(Filter.eventually_false_iff_eq_bot.mp hfalse)]
    exact Filter.tendsto_bot
  let d : ℝ := (1 - τ) / 2
  let c : ℝ := max |b₁ + d| |b₂ + d|
  obtain ⟨hclt, hgeom⟩ := faddeevS_closed_substrip τ b₁ b₂ hb₁ hb₂ horder
  let w : α → ℂ := fun a => -I * (z a + d)
  let R : α → ℂ := fun a => hyperbolicGammaLog τ 1 (w a) +
    Real.pi * (w a) ^ 2 / (2 * τ) + Real.pi / 24 * ((τ : ℂ) + (τ : ℂ)⁻¹)
  have hwre (a : α) : (w a).re = (z a).im := by simp [w, Complex.mul_re]
  have hR : Tendsto R l (𝓝 0) :=
    tendsto_hyperbolicGamma_remainder_of_strip w τ c hτ hclt
      (by simpa only [hwre] using hz) (hre.mono fun a ha => hgeom (z a) ha)
  have hPhi : ∀ᶠ a in l, faddeevS (z a) τ = Complex.exp (I * R a) :=
    hre.mono fun a ha => by
      rw [faddeevS_eq_exp_hyperbolicGammaLog (z a) τ hτ
        (lt_of_lt_of_le hb₁ ha.1) (lt_of_le_of_lt ha.2 hb₂)]
      congr 1
      simp [R, w, d]
  have hlimit : Tendsto (fun a => Complex.exp (I * R a)) l (𝓝 1) := by
    have hmul : Tendsto (fun a => I * R a) l (𝓝 0) := by
      simpa using tendsto_const_nhds.mul hR
    simpa [Function.comp_def] using
      (Complex.continuous_exp.tendsto 0).comp hmul
  exact hlimit.congr' (Filter.EventuallyEq.symm hPhi)

/-! ### Upper sectors

Integer translation into a unit window of the strip, with the finite real-period
`q`-Pochhammer bound controlling the shift factors. -/

/-- A linear factor is dominated by exponential decay; used by
`tendsto_qPochhammerFin_shift` to control the number of shifts. -/
private lemma tendsto_linear_mul_exp_neg {α : Type*} {l : Filter α} (y : α → ℝ)
    (hy : Tendsto y l atTop) (κ : ℝ) (hκ : 0 < κ) (A B : ℝ) :
    Tendsto (fun a => (A * y a + B) * Real.exp (-κ * y a)) l (𝓝 0) := by
  have hyκ : Tendsto (fun a => κ * y a) l atTop := hy.const_mul_atTop hκ
  have hlinear : Tendsto (fun a => (κ * y a) * Real.exp (-(κ * y a))) l (𝓝 0) := by
    simpa only [pow_one, Function.comp_def] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hyκ
  have hconst : Tendsto (fun a => Real.exp (-(κ * y a))) l (𝓝 0) := by
    simpa only [Function.comp_def] using Real.tendsto_exp_neg_atTop_nhds_zero.comp hyκ
  have hsum := (hlinear.const_mul (A / κ)).add (hconst.const_mul B)
  convert hsum using 1
  · funext a
    field_simp
  · simp

/-- A linearly growing shift count does not affect the finite real-period product
limit; this applies `tendsto_qPochhammerFin_of_im_tendsto_atTop` in
`tendsto_faddeevS_of_abs_re_le`. -/
private lemma tendsto_qPochhammerFin_shift {α : Type*} {l : Filter α}
    (n : α → ℤ) (x : α → ℂ) (y : α → ℝ) (τ K C : ℝ) (hτ : 0 < τ)
    (hy : Tendsto y l atTop) (hxim : ∀ a, (x a).im = y a / τ)
    (hn : ∀ᶠ a in l, |(n a : ℝ)| ≤ K * y a + C) :
    Tendsto (fun a => qPochhammerFin (n a) (x a) (τ⁻¹ : ℝ)) l (𝓝 1) := by
  let η : α → ℝ := fun a => y a / τ
  have hη : Tendsto η l atTop := by
    simpa [η, div_eq_mul_inv, mul_comm] using hy.const_mul_atTop (inv_pos.mpr hτ)
  have hphase : ∀ᶠ a in l, ∀ j ∈ Set.Ico (min (n a) 0) (max (n a) 0),
      η a ≤ (x a + (j : ℂ) * ((τ⁻¹ : ℝ) : ℂ)).im := by
    exact Filter.Eventually.of_forall fun a j _ => by
      simp [η, Complex.mul_im, hxim a]
  have hκ : 0 < 2 * Real.pi / τ :=
    div_pos (mul_pos (by norm_num) Real.pi_pos) hτ
  have hlinear := tendsto_linear_mul_exp_neg y hy (2 * Real.pi / τ) hκ K C
  have hmajor : Tendsto (fun a => (K * y a + C) * Real.exp (-2 * Real.pi * η a))
      l (𝓝 0) := by
    convert hlinear using 1
    funext a
    simp only [η]
    congr 1
    ring_nf
  have hcount : Tendsto (fun a => |(n a : ℝ)| * Real.exp (-2 * Real.pi * η a))
      l (𝓝 0) := by
    apply Filter.Tendsto.squeeze' tendsto_const_nhds hmajor
    · exact Filter.Eventually.of_forall fun a => mul_nonneg (abs_nonneg _) (Real.exp_nonneg _)
    · exact hn.mono fun a ha => mul_le_mul_of_nonneg_right ha (Real.exp_nonneg _)
  exact tendsto_qPochhammerFin_of_im_tendsto_atTop n x
    (fun _ => ((τ⁻¹ : ℝ) : ℂ)) η hη hphase hcount

/-- The translated arguments in the unit window satisfy the strip limit; used by
`tendsto_faddeevS_of_abs_re_le`. -/
private lemma tendsto_faddeevS_floor_window {α : Type*} {l : Filter α}
    (z : α → ℂ) (τ : ℝ) (hτ : 0 < τ) (K : ℝ)
    (hz : Tendsto (fun a => (z a).im) l atTop)
    (hre : ∀ᶠ a in l, |(z a).re| ≤ K * (z a).im) :
    Tendsto (fun a => faddeevS (z a -
      (⌊(z a).re - (τ / 2 - 1)⌋ : ℤ)) τ) l (𝓝 1) := by
  let c₀ : ℝ := τ / 2 - 1
  let n : α → ℤ := fun a => ⌊(z a).re - c₀⌋
  let z₀ : α → ℂ := fun a => z a - n a
  have hwindow : ∀ᶠ a in l, (z₀ a).re ∈ Icc c₀ (c₀ + 1) := hre.mono fun a ha => by
    simpa only [z₀, n] using (floor_window_of_abs_re_le (z a) c₀ K ha).1
  have him₀ (a : α) : (z₀ a).im = (z a).im := by simp [z₀]
  change Tendsto (fun a => faddeevS (z₀ a) τ) l (𝓝 1)
  apply tendsto_faddeevS_of_re_mem_Icc z₀ τ hτ (b₁ := c₀) (b₂ := c₀ + 1)
  · dsimp [c₀]; linarith
  · dsimp [c₀]; linarith
  · simpa only [him₀] using hz
  · exact hwindow

/-- The period-one shift expresses a nonreal value as a quotient by its finite product;
used by `tendsto_faddeevS_of_abs_re_le`. -/
private lemma faddeevS_eq_shift_div (z : ℂ) (τ : ℝ) (hτ : 0 < τ)
    (hz : z.im ≠ 0) (n : ℤ)
    (hP : qPochhammerFin n ((z - n + 1) / τ) (τ⁻¹ : ℝ) ≠ 0) :
    faddeevS z τ = faddeevS (z - n) τ /
      qPochhammerFin n ((z - n + 1) / τ) (τ⁻¹ : ℝ) := by
  have hshift := faddeevS_add_intCast_mul_qPochhammerFin (z - n) τ hτ
    (by simpa using hz) n
  have hzsum : z - (n : ℂ) + n = z := by ring
  apply (eq_div_iff hP).2
  simpa only [hzsum, Complex.ofReal_inv] using hshift

/-- The generator tends to one as `Im z → +∞` with `|Re z| ≤ K Im z`: at a positive real
period, `Φ_{S,0,0}(z;τ) → 1` uniformly in every upper sector, in particular along bounded
real translates of the upward vertical ray and along every ray `0 < arg z < π`. This
extends `tendsto_faddeevS_of_re_mem_Icc` by `faddeevS_add_intCast_mul_qPochhammerFin`. -/
theorem tendsto_faddeevS_of_abs_re_le {α : Type*} {l : Filter α} (z : α → ℂ) (τ : ℝ)
    (hτ : 0 < τ) (K : ℝ) (hz : Tendsto (fun a => (z a).im) l atTop)
    (hre : ∀ᶠ a in l, |(z a).re| ≤ K * (z a).im) :
    Tendsto (fun a => faddeevS (z a) τ) l (𝓝 1) := by
  let c₀ : ℝ := τ / 2 - 1
  let n : α → ℤ := fun a => ⌊(z a).re - c₀⌋
  let z₀ : α → ℂ := fun a => z a - n a
  let x : α → ℂ := fun a => (z₀ a + 1) / τ
  let P : α → ℂ := fun a => qPochhammerFin (n a) (x a) (τ⁻¹ : ℝ)
  have hnabs : ∀ᶠ a in l, |(n a : ℝ)| ≤ K * (z a).im + (|c₀| + 1) :=
    hre.mono fun a ha => by
    simpa only [n, c₀, add_assoc] using (floor_window_of_abs_re_le (z a) c₀ K ha).2
  have him₀ (a : α) : (z₀ a).im = (z a).im := by simp [z₀]
  have hstrip : Tendsto (fun a => faddeevS (z₀ a) τ) l (𝓝 1) :=
    tendsto_faddeevS_floor_window z τ hτ K hz hre
  have hxim (a : α) : (x a).im = (z a).im / τ := by
    simp only [x, Complex.div_ofReal_im, Complex.add_im, Complex.one_im, add_zero, him₀]
  have hP : Tendsto P l (𝓝 1) :=
    tendsto_qPochhammerFin_shift n x (fun a => (z a).im) τ K (|c₀| + 1)
      hτ hz hxim hnabs
  have hdiv : ∀ᶠ a in l, faddeevS (z a) τ = faddeevS (z₀ a) τ / P a := by
    filter_upwards [hz.eventually (eventually_gt_atTop 0),
      hP.eventually_ne (by norm_num : (1 : ℂ) ≠ 0)] with a ha hp
    exact faddeevS_eq_shift_div (z a) τ hτ (by linarith) (n a)
      (by simpa only [P, x, z₀] using hp)
  have hquot : Tendsto (fun a => faddeevS (z₀ a) τ / P a) l (𝓝 1) := by
    simpa [Pi.div_def] using hstrip.div hP (by norm_num : (1 : ℂ) ≠ 0)
  exact hquot.congr' (Filter.EventuallyEq.symm hdiv)

end SIC

end
