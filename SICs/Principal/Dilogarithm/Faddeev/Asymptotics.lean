/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Dilogarithm.Faddeev.Reflection
import SICs.SpecialFunctions.Faddeev.Asymptotics

/-!
# Asymptotics of the principal Faddeev product

The principal product `Φ_{A_d,m,n}(z;ρ_d)` tends to one in every upper sector and is asymptotic
to `(-1)^{m+n} e^{-πid/2} e(Q_{A_d,-m,-n}(-z,ρ_d))` in every lower sector.

This module proves the sector limits of [RW26, Radchenko, Wheeler (2026), Lemma 1, `lem:asymp`]
at `γ = A_d`, `τ = ρ_d`, following its proof: the product formula of Proposition 2(ii),
`prop:prod.id.mod,fad`, equation (20), reduces the upper half plane to the generator, and the
reflection law of Proposition 1, `prop:reflection`, reduces the lower half plane to the upper.
The sector forms supply the bounds along bounded real translates of vertical rays that the
contour integrals of [RW26, Radchenko, Wheeler (2026), Theorem 3, `thm:5term.mod.fad`] need.

## The argument

The three arguments `z/ρ_d² - n`, `z/ρ_d`, and `z + mρ_d` of `principalFaddeev` are
positive real multiples of `z` up to bounded real translations, so each lies in an upper sector
when `z` does, and each generator factor tends to one by `tendsto_faddeevS_of_abs_re_le`.
In a lower sector, the reflection law `principalFaddeev_mul_neg_of_im_ne_zero`
at `(-m, -n)` and `-z` gives
`Φ_{A_d,m,n}(z) Φ_{A_d,1-m,1-n}(-z) = (-1)^{m+n} e^{-πid/2} e(Q_{A_d,-m,-n}(-z))`, and the second
factor on the left tends to one. The source multiplier `μ_{A_d}⁻² = e^{-πid/2}`
does not affect the `O`-bound of Lemma 1.
-/

noncomputable section

open Complex Filter
open scoped Topology

namespace SIC

/-! ### Upper sectors

The real affine sector bound in `SICs.Analysis.Sectors` applies to the three arguments of
`principalFaddeev`. -/

/-- The factor at `z/ρ_d² - n` tends to one in an upper sector; used by
`tendsto_principalFaddeev_of_abs_re_le`. -/
private lemma tendsto_faddeevS_principal_first_argument (d : ℕ) (hd : 3 < d) (n : ℤ)
    {α : Type*} {l : Filter α} (z : α → ℂ) (K : ℝ)
    (hz : Tendsto (fun a => (z a).im) l atTop)
    (hre : ∀ᶠ a in l, |(z a).re| ≤ K * (z a).im) :
    Tendsto (fun a => faddeevS (z a / (principalRoot d : ℂ) ^ 2 - n)
      (principalRoot d)) l (𝓝 1) := by
  let ρ : ℝ := principalRoot d
  have hρ : 0 < ρ := principalRoot_pos d hd
  let w : α → ℂ := fun a => z a / (ρ : ℂ) ^ 2 - n
  have hwim (a : α) : (w a).im = (1 / ρ ^ 2) * (z a).im := by
    simp [w, ← Complex.ofReal_pow, Complex.div_ofReal_im]
    ring
  have hwre (a : α) : (w a).re = (1 / ρ ^ 2) * (z a).re + (-(n : ℝ)) := by
    simp [w, ← Complex.ofReal_pow, Complex.div_ofReal_re]
    ring
  obtain ⟨him, hre'⟩ := upperSector_affine z w (c := 1 / ρ ^ 2) (-(n : ℝ)) K
    (one_div_pos.mpr (pow_pos hρ _)) hwim hwre hz hre
  simpa [w, ρ] using tendsto_faddeevS_of_abs_re_le w ρ hρ (K + 1) him hre'

/-- At the principal period, `Φ_{A_d,m,n}(z;ρ_d) → 1` as `Im z → +∞` with `|Re z| ≤ K Im z`:
the upper clause of [RW26, Radchenko, Wheeler (2026), Lemma 1, `lem:asymp`] at `γ = A_d`, uniform
in every upper sector. Each of the three generator factors tends to one by
`tendsto_faddeevS_of_abs_re_le`. -/
theorem tendsto_principalFaddeev_of_abs_re_le (d : ℕ) (hd : 3 < d) (m n : ℤ)
    {α : Type*} {l : Filter α} (z : α → ℂ) (K : ℝ)
    (hz : Tendsto (fun a => (z a).im) l atTop)
    (hre : ∀ᶠ a in l, |(z a).re| ≤ K * (z a).im) :
    Tendsto (fun a => principalFaddeev d m n (z a)) l (𝓝 1) := by
  let ρ : ℝ := principalRoot d
  have hρ : 0 < ρ := principalRoot_pos d hd
  let w₁ : α → ℂ := fun a => z a / (ρ : ℂ)
  let w₀ : α → ℂ := fun a => z a + m * (ρ : ℂ)
  have hw₁im (a : α) : (w₁ a).im = (1 / ρ) * (z a).im := by
    simp [w₁, Complex.div_ofReal_im]
    ring
  have hw₁re (a : α) : (w₁ a).re = (1 / ρ) * (z a).re + 0 := by
    simp [w₁, Complex.div_ofReal_re]
    ring
  have hw₀im (a : α) : (w₀ a).im = 1 * (z a).im := by simp [w₀]
  have hw₀re (a : α) : (w₀ a).re = 1 * (z a).re + (m : ℝ) * ρ := by
    simp [w₀, Complex.mul_re]
  obtain ⟨h₁im, h₁re⟩ := upperSector_affine z w₁ (c := 1 / ρ) 0 K
    (one_div_pos.mpr hρ) hw₁im hw₁re hz hre
  obtain ⟨h₀im, h₀re⟩ := upperSector_affine z w₀ (c := 1) ((m : ℝ) * ρ) K
    (by norm_num) hw₀im hw₀re hz hre
  have h₂ := tendsto_faddeevS_principal_first_argument d hd n z K hz hre
  have h₁ := tendsto_faddeevS_of_abs_re_le w₁ ρ hρ (K + 1) h₁im h₁re
  have h₀ := tendsto_faddeevS_of_abs_re_le w₀ ρ hρ (K + 1) h₀im h₀re
  simpa [principalFaddeev, w₁, w₀, ρ] using (h₂.mul h₁).mul h₀

/-! ### Lower sectors -/

/-- The reflection law expresses the normalized lower product as the reciprocal
of the product at the reflected argument, away from the real axis. -/
private lemma principalFaddeev_div_exp_eq_inv (d : ℕ) (hd : 3 < d)
    (m n : ℤ) (z : ℂ) (hz : z.im ≠ 0)
    (hP : principalFaddeev d (1 - m) (1 - n) (-z) ≠ 0) :
    principalFaddeev d m n z /
        Complex.exp (2 * Real.pi * I * principalFaddeevReflectionExponent d (-m) (-n) (-z)) =
      ((-1 : ℂ) ^ (m + n) * Complex.exp (-Real.pi * I * (d : ℂ) / 2)) /
        principalFaddeev d (1 - m) (1 - n) (-z) := by
  have hreflection := principalFaddeev_mul_neg_of_im_ne_zero d hd (-m) (-n) (-z)
    (by simpa using hz)
  have hpow : (-1 : ℂ) ^ ((-m) + (-n)) = (-1 : ℂ) ^ (m + n) := by
    rw [← neg_add, zpow_neg, ← inv_zpow]
    norm_num
  rw [hpow] at hreflection
  have he : Complex.exp (2 * Real.pi * I *
      principalFaddeevReflectionExponent d (-m) (-n) (-z)) ≠ 0 :=
    Complex.exp_ne_zero _
  apply (div_eq_div_iff he hP).2
  simpa [sub_eq_add_neg, add_comm, mul_comm] using hreflection

/-- At the principal period, as `Im z → -∞` with `|Re z| ≤ K (-Im z)`,
`Φ_{A_d,m,n}(z;ρ_d) / e(Q_{A_d,-m,-n}(-z,ρ_d)) → (-1)^{m+n} e^{-πid/2}`: the lower clause of
[RW26, Radchenko, Wheeler (2026), Lemma 1, `lem:asymp`] at `γ = A_d`, uniform in every lower
sector, with the constant of the reflection law. -/
theorem tendsto_principalFaddeev_div_exp_of_abs_re_le (d : ℕ) (hd : 3 < d) (m n : ℤ)
    {α : Type*} {l : Filter α} (z : α → ℂ) (K : ℝ)
    (hz : Tendsto (fun a => (z a).im) l atBot)
    (hre : ∀ᶠ a in l, |(z a).re| ≤ K * -(z a).im) :
    Tendsto (fun a => principalFaddeev d m n (z a) /
        Complex.exp (2 * Real.pi * I * principalFaddeevReflectionExponent d (-m) (-n) (-(z a))))
      l (𝓝 ((-1 : ℂ) ^ (m + n) * Complex.exp (-Real.pi * I * (d : ℂ) / 2))) := by
  let w : α → ℂ := fun a => -(z a)
  have hwim : Tendsto (fun a => (w a).im) l atTop := by
    convert Filter.tendsto_neg_atBot_atTop.comp hz using 1
    funext a
    simp [w]
  have hwre : ∀ᶠ a in l, |(w a).re| ≤ K * (w a).im :=
    hre.mono fun a ha => by simpa [w] using ha
  have hP := tendsto_principalFaddeev_of_abs_re_le d hd (1 - m) (1 - n)
    w K hwim hwre
  have hPne : ∀ᶠ a in l, principalFaddeev d (1 - m) (1 - n) (w a) ≠ 0 :=
    hP.eventually (eventually_ne_nhds (by norm_num : (1 : ℂ) ≠ 0))
  have hznonzero : ∀ᶠ a in l, (z a).im ≠ 0 :=
    (hz.eventually (eventually_lt_atBot 0)).mono fun a ha => ne_of_lt ha
  have heq : (fun a => principalFaddeev d m n (z a) /
        Complex.exp (2 * Real.pi * I *
          principalFaddeevReflectionExponent d (-m) (-n) (-(z a)))) =ᶠ[l]
      (fun a => ((-1 : ℂ) ^ (m + n) * Complex.exp (-Real.pi * I * (d : ℂ) / 2)) /
        principalFaddeev d (1 - m) (1 - n) (w a)) := by
    filter_upwards [hznonzero, hPne] with a ha hb
    exact principalFaddeev_div_exp_eq_inv d hd m n (z a) ha hb
  have hlim : Tendsto (fun a =>
      ((-1 : ℂ) ^ (m + n) * Complex.exp (-Real.pi * I * (d : ℂ) / 2)) /
        principalFaddeev d (1 - m) (1 - n) (w a)) l
      (𝓝 ((-1 : ℂ) ^ (m + n) * Complex.exp (-Real.pi * I * (d : ℂ) / 2))) := by
    convert (tendsto_const_nhds.div hP (by norm_num : (1 : ℂ) ≠ 0)) using 1
    simp
  exact hlim.congr' heq.symm

end SIC

end
