/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Dilogarithm.Faddeev.Boundary
import SICs.SpecialFunctions.Faddeev.ComplexPeriodAsymptotics

/-!
# Complex-period asymptotics of the principal Faddeev product

The three-factor expression `principalFaddeevComplex` tends exponentially to one in every
upper sector, while its quotient by the exact reflection exponential does so in every lower
sector, uniformly as its complex period approaches the positive principal root.

These are quantitative boundary-neighborhood extensions of both clauses of [RW26,
Radchenko--Wheeler (2026), Lemma 1, `lem:asymp`] at `A_d`. Equation (20),
`eq:modulartofaddeevCF`, writes the product as three Faddeev generators. Their arguments are
affine in `z`, while their periods and affine coefficients vary continuously with the boundary
parameter. Applying the general complex-period affine estimates to each factor and combining the
three near-one bounds gives the results; in the lower sector, `exp_add` identifies the product of
the three normalizations with `principalFaddeevLowerExponentComplex`. At the principal root they
specialize to quantitative forms accompanying the independently proved real-period sector limits.
-/

noncomputable section

open Complex
open scoped Topology MatrixGroups

namespace SIC

/-! ### Lower-sector normalization

The generator reflection law contributes one quadratic polynomial for each of the three
factors in equation (20). Their sum is kept exact until the numerator and denominator of
the five-term kernel are combined. -/

/-- The logarithm of the lower-sector normalizing exponential for the three-generator
principal product. It is the sum of the three exponents in [RW26, Radchenko, Wheeler (2026),
equation (13), `eq:PhiS.reflection`], at the arguments of equation (20),
`eq:modulartofaddeevCF`. The factor `-πi` is included here, unlike the polynomial
`principalFaddeevReflectionExponent` at the real period. -/
def principalFaddeevLowerExponentComplex (d : ℕ) (m n : ℤ) (z τ : ℂ) : ℂ :=
  let τ₁ := flt (principalU d : Mat(2, ℤ)) τ
  let τ₂ := flt (principalU d : Mat(2, ℤ)) τ₁
  let P := fun v t : ℂ => v ^ 2 / t - (1 - t⁻¹) * v + (t + t⁻¹) / 6 - 1 / 2
  (-Real.pi * I) * (P (z / τ / τ₁ - n) τ₂ + P (z / τ) τ₁ + P (z + m * τ) τ)

/-- The exact lower normalizing exponent is continuous in its complex period at the positive
principal root. -/
theorem continuousAt_principalFaddeevLowerExponentComplex (d : ℕ) (hd : 3 < d)
    (m n : ℤ) (z : ℂ) :
    ContinuousAt (fun τ : ℂ => principalFaddeevLowerExponentComplex d m n z τ)
      (principalRoot d : ℂ) := by
  let U : Mat(2, ℤ) := principalU d
  let ρ : ℂ := principalRoot d
  have hρ : ρ ≠ 0 := ofReal_principalRoot_ne_zero d hd
  have hfix : flt U ρ = ρ := by
    simpa only [U, ρ] using flt_principalU_principalRoot_complex d hd
  have hUρ : flt U ρ ≠ 0 := hfix.symm ▸ hρ
  have hU₂ρ : flt U (flt U ρ) ≠ 0 := by rw [hfix, hfix]; exact hρ
  obtain ⟨hU, hU₂⟩ := continuousAt_principalU_periods d hd
  have hU' : ContinuousAt (flt U) ρ := by simpa only [U, ρ] using hU
  have hU₂' : ContinuousAt (fun τ : ℂ => flt U (flt U τ)) ρ := by
    simpa only [U, ρ] using hU₂
  change ContinuousAt (fun τ : ℂ =>
    let τ₁ := flt U τ
    let τ₂ := flt U τ₁
    let P := fun v t : ℂ => v ^ 2 / t - (1 - t⁻¹) * v + (t + t⁻¹) / 6 - 1 / 2
    (-Real.pi * I) * (P (z / τ / τ₁ - n) τ₂ + P (z / τ) τ₁ + P (z + m * τ) τ)) ρ
  dsimp only
  fun_prop

/-! ### Principal affine data -/

/-- The coefficient of the first generator argument in equation (20) varies continuously at the
principal root. -/
private lemma continuousAt_principal_first_coefficient (d : ℕ) (hd : 3 < d) :
    ContinuousAt (fun τ : ℂ => (1 : ℂ) / τ /
      flt (principalU d : Mat(2, ℤ)) τ) (principalRoot d : ℂ) := by
  let U : Mat(2, ℤ) := principalU d
  let ρ : ℂ := principalRoot d
  have hρ : ρ ≠ 0 := ofReal_principalRoot_ne_zero d hd
  have hτ₁ : ContinuousAt (flt U) ρ := by
    simpa only [U, ρ] using (continuousAt_principalU_periods d hd).1
  have hfix : flt U ρ = ρ := by
    simpa only [U, ρ] using flt_principalU_principalRoot_complex d hd
  apply (continuousAt_const.div continuousAt_id hρ).div hτ₁
  change flt U ρ ≠ 0
  rw [hfix]
  exact hρ

/-- At the principal root, the first generator coefficient is one over the square of the root. -/
private lemma principal_first_coefficient_at_root (d : ℕ) (hd : 3 < d) :
    (1 : ℂ) / (principalRoot d : ℂ) /
      flt (principalU d : Mat(2, ℤ)) (principalRoot d : ℂ) =
        ((1 / principalRoot d ^ 2 : ℝ) : ℂ) := by
  rw [flt_principalU_principalRoot_complex d hd]
  push_cast
  ring

/-- Continuity and fixed-point values for the affine data of the first principal generator
factor. -/
private lemma principal_first_affine_data (d : ℕ) (hd : 3 < d) (n : ℤ) :
    ContinuousAt (fun τ : ℂ => (1 : ℂ) / τ /
      flt (principalU d : Mat(2, ℤ)) τ) (principalRoot d : ℂ) ∧
    ContinuousAt (fun _ : ℂ => -(n : ℂ)) (principalRoot d : ℂ) ∧
    ContinuousAt (fun τ : ℂ => flt (principalU d : Mat(2, ℤ))
      (flt (principalU d : Mat(2, ℤ)) τ)) (principalRoot d : ℂ) ∧
    (1 : ℂ) / (principalRoot d : ℂ) /
      flt (principalU d : Mat(2, ℤ)) (principalRoot d : ℂ) =
        ((1 / principalRoot d ^ 2 : ℝ) : ℂ) ∧
    flt (principalU d : Mat(2, ℤ))
      (flt (principalU d : Mat(2, ℤ)) (principalRoot d : ℂ)) =
        (principalRoot d : ℂ) := by
  have hperiod := continuousAt_principalU_periods d hd
  have hfix := flt_principalU_principalRoot_complex d hd
  exact ⟨continuousAt_principal_first_coefficient d hd, continuousAt_const, hperiod.2,
    principal_first_coefficient_at_root d hd, by rw [hfix, hfix]⟩

/-- Continuity and fixed-point values for the affine data of the middle principal generator
factor. -/
private lemma principal_middle_affine_data (d : ℕ) (hd : 3 < d) :
    ContinuousAt (fun τ : ℂ => (1 : ℂ) / τ) (principalRoot d : ℂ) ∧
    ContinuousAt (fun _ : ℂ => (0 : ℂ)) (principalRoot d : ℂ) ∧
    ContinuousAt (fun τ : ℂ => flt (principalU d : Mat(2, ℤ)) τ)
      (principalRoot d : ℂ) ∧
    (1 : ℂ) / (principalRoot d : ℂ) = (((principalRoot d)⁻¹ : ℝ) : ℂ) ∧
    flt (principalU d : Mat(2, ℤ)) (principalRoot d : ℂ) =
      (principalRoot d : ℂ) := by
  have hρ : (principalRoot d : ℂ) ≠ 0 := ofReal_principalRoot_ne_zero d hd
  exact ⟨continuousAt_const.div continuousAt_id hρ, continuousAt_const,
    (continuousAt_principalU_periods d hd).1, by simp [div_eq_mul_inv],
    flt_principalU_principalRoot_complex d hd⟩

/-- Continuity and fixed-point values for the affine data of the last principal generator
factor. -/
private lemma principal_last_affine_data (d : ℕ) (m : ℤ) :
    ContinuousAt (fun _ : ℂ => (1 : ℂ)) (principalRoot d : ℂ) ∧
    ContinuousAt (fun τ : ℂ => (m : ℂ) * τ) (principalRoot d : ℂ) ∧
    ContinuousAt (id : ℂ → ℂ) (principalRoot d : ℂ) ∧
    (1 : ℂ) = ((1 : ℝ) : ℂ) ∧
    (id : ℂ → ℂ) (principalRoot d : ℂ) = (principalRoot d : ℂ) := by
  exact ⟨continuousAt_const, continuousAt_const.mul continuousAt_id,
    continuousAt_id, by norm_num, rfl⟩

/-! ### The three generator factors -/

/-- The first generator in the principal three-factor expression has a uniform exponential
near-one bound as the complex parameter approaches the principal root. -/
private lemma exists_norm_first_factor_sub_one_le
    (d : ℕ) (hd : 3 < d) (n : ℤ) (K : ℝ) :
    ∃ ε C κ R : ℝ, 0 < ε ∧ 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ (τ z : ℂ), ‖τ - (principalRoot d : ℂ)‖ ≤ ε →
        |z.re| ≤ K * z.im → R ≤ z.im →
        ‖faddeevS (z / τ / flt (principalU d : Mat(2, ℤ)) τ - n)
          (flt (principalU d : Mat(2, ℤ))
            (flt (principalU d : Mat(2, ℤ)) τ)) - 1‖ ≤
          C * Real.exp (-κ * z.im) := by
  obtain ⟨ha, hb, ht, haρ, htρ⟩ := principal_first_affine_data d hd n
  obtain ⟨ε, C, κ, R, hε, hC, hκ, hR, hbound⟩ :=
    exists_norm_faddeevS_affine_sub_one_le ha hb ht haρ htρ
      (one_div_pos.mpr (sq_pos_of_pos (principalRoot_pos d hd)))
      (principalRoot_pos d hd) K
  refine ⟨ε, C, κ, R, hε, hC, hκ, hR, fun τ z hτ hz hy => ?_⟩
  have harg : ((1 : ℂ) / τ / flt (principalU d : Mat(2, ℤ)) τ) * z + -(n : ℂ) =
      z / τ / flt (principalU d : Mat(2, ℤ)) τ - n := by ring
  simpa only [harg] using hbound τ z hτ hz hy

/-- The middle generator in the principal three-factor expression has a uniform exponential
near-one bound as the complex parameter approaches the principal root. -/
private lemma exists_norm_middle_factor_sub_one_le
    (d : ℕ) (hd : 3 < d) (K : ℝ) :
    ∃ ε C κ R : ℝ, 0 < ε ∧ 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ (τ z : ℂ), ‖τ - (principalRoot d : ℂ)‖ ≤ ε →
        |z.re| ≤ K * z.im → R ≤ z.im →
        ‖faddeevS (z / τ) (flt (principalU d : Mat(2, ℤ)) τ) - 1‖ ≤
          C * Real.exp (-κ * z.im) := by
  obtain ⟨ha, hb, ht, haρ, htρ⟩ := principal_middle_affine_data d hd
  obtain ⟨ε, C, κ, R, hε, hC, hκ, hR, hbound⟩ :=
    exists_norm_faddeevS_affine_sub_one_le ha hb ht haρ htρ
      (inv_pos.mpr (principalRoot_pos d hd)) (principalRoot_pos d hd) K
  refine ⟨ε, C, κ, R, hε, hC, hκ, hR, fun τ z hτ hz hy => ?_⟩
  have harg : ((1 : ℂ) / τ) * z + 0 = z / τ := by ring
  simpa only [harg] using hbound τ z hτ hz hy

/-- The last generator in the principal three-factor expression has a uniform exponential
near-one bound as the complex parameter approaches the principal root. -/
private lemma exists_norm_last_factor_sub_one_le
    (d : ℕ) (hd : 3 < d) (m : ℤ) (K : ℝ) :
    ∃ ε C κ R : ℝ, 0 < ε ∧ 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ (τ z : ℂ), ‖τ - (principalRoot d : ℂ)‖ ≤ ε →
        |z.re| ≤ K * z.im → R ≤ z.im →
        ‖faddeevS (z + m * τ) τ - 1‖ ≤ C * Real.exp (-κ * z.im) := by
  obtain ⟨ha, hb, ht, haρ, htρ⟩ := principal_last_affine_data d m
  obtain ⟨ε, C, κ, R, hε, hC, hκ, hR, hbound⟩ :=
    exists_norm_faddeevS_affine_sub_one_le ha hb ht haρ htρ
      (by norm_num) (principalRoot_pos d hd) K
  refine ⟨ε, C, κ, R, hε, hC, hκ, hR, fun τ z hτ hz hy => ?_⟩
  simpa [mul_comm] using hbound τ z hτ hz hy

/-- The normalized first generator in the principal three-factor expression has a uniform
exponential near-one bound in lower sectors. -/
private lemma exists_norm_first_factor_div_exp_sub_one_le
    (d : ℕ) (hd : 3 < d) (n : ℤ) (K : ℝ) :
    ∃ ε C κ R : ℝ, 0 < ε ∧ 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ (τ z : ℂ), ‖τ - (principalRoot d : ℂ)‖ ≤ ε →
        |z.re| ≤ K * (-z.im) → R ≤ -z.im →
        let τ₁ := flt (principalU d : Mat(2, ℤ)) τ
        let τ₂ := flt (principalU d : Mat(2, ℤ)) τ₁
        let v := z / τ / τ₁ - n
        ‖faddeevS v τ₂ / Complex.exp (-Real.pi * I *
          (v ^ 2 / τ₂ - (1 - τ₂⁻¹) * v + (τ₂ + τ₂⁻¹) / 6 - 1 / 2)) - 1‖ ≤
            C * Real.exp (-κ * (-z.im)) := by
  obtain ⟨ha, hb, ht, haρ, htρ⟩ := principal_first_affine_data d hd n
  obtain ⟨ε, C, κ, R, hε, hC, hκ, hR, hbound⟩ :=
    exists_norm_faddeevS_affine_div_exp_sub_one_le
      ha hb ht haρ htρ (one_div_pos.mpr (sq_pos_of_pos (principalRoot_pos d hd)))
      (principalRoot_pos d hd) K
  refine ⟨ε, C, κ, R, hε, hC, hκ, hR, fun τ z hτ hz hy => ?_⟩
  dsimp only
  have harg : ((1 : ℂ) / τ / flt (principalU d : Mat(2, ℤ)) τ) * z + -(n : ℂ) =
      z / τ / flt (principalU d : Mat(2, ℤ)) τ - n := by ring
  simpa only [harg] using hbound τ z hτ hz hy

/-- The normalized middle generator in the principal three-factor expression has a uniform
exponential near-one bound in lower sectors. -/
private lemma exists_norm_middle_factor_div_exp_sub_one_le
    (d : ℕ) (hd : 3 < d) (K : ℝ) :
    ∃ ε C κ R : ℝ, 0 < ε ∧ 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ (τ z : ℂ), ‖τ - (principalRoot d : ℂ)‖ ≤ ε →
        |z.re| ≤ K * (-z.im) → R ≤ -z.im →
        let τ₁ := flt (principalU d : Mat(2, ℤ)) τ
        let v := z / τ
        ‖faddeevS v τ₁ / Complex.exp (-Real.pi * I *
          (v ^ 2 / τ₁ - (1 - τ₁⁻¹) * v + (τ₁ + τ₁⁻¹) / 6 - 1 / 2)) - 1‖ ≤
            C * Real.exp (-κ * (-z.im)) := by
  obtain ⟨ha, hb, ht, haρ, htρ⟩ := principal_middle_affine_data d hd
  obtain ⟨ε, C, κ, R, hε, hC, hκ, hR, hbound⟩ :=
    exists_norm_faddeevS_affine_div_exp_sub_one_le
      ha hb ht haρ htρ (inv_pos.mpr (principalRoot_pos d hd))
      (principalRoot_pos d hd) K
  refine ⟨ε, C, κ, R, hε, hC, hκ, hR, fun τ z hτ hz hy => ?_⟩
  dsimp only
  have harg : ((1 : ℂ) / τ) * z + 0 = z / τ := by ring
  simpa only [harg] using hbound τ z hτ hz hy

/-- The normalized last generator in the principal three-factor expression has a uniform
exponential near-one bound in lower sectors. -/
private lemma exists_norm_last_factor_div_exp_sub_one_le
    (d : ℕ) (hd : 3 < d) (m : ℤ) (K : ℝ) :
    ∃ ε C κ R : ℝ, 0 < ε ∧ 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ (τ z : ℂ), ‖τ - (principalRoot d : ℂ)‖ ≤ ε →
        |z.re| ≤ K * (-z.im) → R ≤ -z.im →
        let v := z + m * τ
        ‖faddeevS v τ / Complex.exp (-Real.pi * I *
          (v ^ 2 / τ - (1 - τ⁻¹) * v + (τ + τ⁻¹) / 6 - 1 / 2)) - 1‖ ≤
          C * Real.exp (-κ * (-z.im)) := by
  obtain ⟨ha, hb, ht, haρ, htρ⟩ := principal_last_affine_data d m
  obtain ⟨ε, C, κ, R, hε, hC, hκ, hR, hbound⟩ :=
    exists_norm_faddeevS_affine_div_exp_sub_one_le
      ha hb ht haρ htρ (by norm_num) (principalRoot_pos d hd) K
  refine ⟨ε, C, κ, R, hε, hC, hκ, hR, fun τ z hτ hz hy => ?_⟩
  dsimp only
  simpa [mul_comm] using hbound τ z hτ hz hy

/-- The normalized principal product is the product of its three individually normalized
generator factors. -/
private lemma faddeevComplex_div_exp_eq_normalized_factors
    (d : ℕ) (m n : ℤ) (z τ : ℂ) :
    let U : Mat(2, ℤ) := principalU d
    let τ₁ := flt U τ
    let τ₂ := flt U τ₁
    let P := fun v t : ℂ => v ^ 2 / t - (1 - t⁻¹) * v + (t + t⁻¹) / 6 - 1 / 2
    principalFaddeevComplex d m n z τ /
        Complex.exp (principalFaddeevLowerExponentComplex d m n z τ) =
      (faddeevS (z / τ / τ₁ - n) τ₂ /
          Complex.exp (-Real.pi * I * P (z / τ / τ₁ - n) τ₂)) *
        (faddeevS (z / τ) τ₁ / Complex.exp (-Real.pi * I * P (z / τ) τ₁)) *
        (faddeevS (z + m * τ) τ /
          Complex.exp (-Real.pi * I * P (z + m * τ) τ)) := by
  dsimp only
  let U : Mat(2, ℤ) := principalU d
  let τ₁ := flt U τ
  let τ₂ := flt U τ₁
  let P := fun v t : ℂ => v ^ 2 / t - (1 - t⁻¹) * v + (t + t⁻¹) / 6 - 1 / 2
  let E₂ := -Real.pi * I * P (z / τ / τ₁ - n) τ₂
  let E₁ := -Real.pi * I * P (z / τ) τ₁
  let E₀ := -Real.pi * I * P (z + m * τ) τ
  change principalFaddeevComplex d m n z τ /
      Complex.exp (principalFaddeevLowerExponentComplex d m n z τ) =
    (faddeevS (z / τ / τ₁ - n) τ₂ / Complex.exp E₂) *
      (faddeevS (z / τ) τ₁ / Complex.exp E₁) *
      (faddeevS (z + m * τ) τ / Complex.exp E₀)
  have hE : principalFaddeevLowerExponentComplex d m n z τ = E₂ + E₁ + E₀ := by
    unfold principalFaddeevLowerExponentComplex
    change -Real.pi * I *
      (P (z / τ / τ₁ - n) τ₂ + P (z / τ) τ₁ + P (z + m * τ) τ) = E₂ + E₁ + E₀
    dsimp only [E₂, E₁, E₀]
    ring
  rw [hE]
  change (faddeevS (z / τ / τ₁ - n) τ₂ * faddeevS (z / τ) τ₁ *
      faddeevS (z + m * τ) τ) / Complex.exp (E₂ + E₁ + E₀) = _
  rw [Complex.exp_add, Complex.exp_add]
  field_simp [Complex.exp_ne_zero]

/-! ### The principal product -/

/-- **New.** Uniformly for complex periods near the positive principal root, the three-factor
principal Faddeev product tends exponentially to one in every upper sector. This is the
quantitative boundary-neighborhood extension of the upper clause of [RW26,
Radchenko--Wheeler (2026), Lemma 1, `lem:asymp`] at `A_d`, obtained from its three generator
factors in equation (20), `eq:modulartofaddeevCF`. Specializes
`exists_norm_faddeevS_affine_sub_one_le` at the three generator factors. The
neighborhood statement is absent from the searched [AFK25] and [RW26, Radchenko, Wheeler (2026),
Appendix A.2, `app:mod.fad`]. -/
theorem exists_norm_principalFaddeevComplex_sub_one_le
    (d : ℕ) (hd : 3 < d) (m n : ℤ) (K : ℝ) :
    ∃ ε C κ R : ℝ, 0 < ε ∧ 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ (τ z : ℂ), ‖τ - (principalRoot d : ℂ)‖ ≤ ε →
        |z.re| ≤ K * z.im → R ≤ z.im →
        ‖principalFaddeevComplex d m n z τ - 1‖ ≤
          C * Real.exp (-κ * z.im) := by
  obtain ⟨ε₂, C₂, κ₂, R₂, hε₂, hC₂, hκ₂, hR₂, h₂⟩ :=
    exists_norm_first_factor_sub_one_le d hd n K
  obtain ⟨ε₁, C₁, κ₁, R₁, hε₁, hC₁, hκ₁, hR₁, h₁⟩ :=
    exists_norm_middle_factor_sub_one_le d hd K
  obtain ⟨ε₀, C₀, κ₀, R₀, hε₀, hC₀, hκ₀, hR₀, h₀⟩ :=
    exists_norm_last_factor_sub_one_le d hd m K
  let ε := min ε₂ (min ε₁ ε₀)
  let C₂₁ := (1 + C₂) * C₁ + C₂
  let C := (1 + C₂₁) * C₀ + C₂₁
  let κ₂₁ := min κ₂ κ₁
  let κ := min κ₂₁ κ₀
  let R := max R₂ (max R₁ R₀)
  refine ⟨ε, C, κ, R, (by dsimp [ε]; positivity), (by dsimp [C, C₂₁]; positivity),
    (by dsimp [κ, κ₂₁]; positivity), (by dsimp [R]; positivity), ?_⟩
  intro τ z hτ hz hy
  have hy0 : 0 ≤ z.im := by
    have : R₂ ≤ z.im := (le_max_left R₂ (max R₁ R₀)).trans hy
    linarith
  have h₂' := h₂ τ z (hτ.trans (min_le_left _ _)) hz
    ((le_max_left R₂ (max R₁ R₀)).trans hy)
  have h₁' := h₁ τ z (hτ.trans ((min_le_right _ _).trans (min_le_left _ _))) hz
    ((le_max_left R₁ R₀).trans (le_max_right R₂ (max R₁ R₀)) |>.trans hy)
  have h₀' := h₀ τ z (hτ.trans ((min_le_right _ _).trans (min_le_right _ _))) hz
    ((le_max_right R₁ R₀).trans (le_max_right R₂ (max R₁ R₀)) |>.trans hy)
  have h₂₁ := norm_mul_sub_one_le_of_exponential_bounds _ _ hκ₂.le hy0 h₂' h₁'
  have h₂₁₀ := norm_mul_sub_one_le_of_exponential_bounds _ _
    (le_min hκ₂.le hκ₁.le) hy0 h₂₁ h₀'
  simpa [principalFaddeevComplex, ε, C, C₂₁, κ, κ₂₁, R] using h₂₁₀

/-- At the principal real period, the complex-period estimate gives a quantitative upper-sector
bound for `principalFaddeev`. Evaluating
`exists_norm_principalFaddeevComplex_sub_one_le` at the root bridges the neighborhood
bound to the independently proved real-period sector limit. -/
theorem exists_norm_principalFaddeev_sub_one_le
    (d : ℕ) (hd : 3 < d) (m n : ℤ) (K : ℝ) :
    ∃ C κ R : ℝ, 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ z : ℂ, |z.re| ≤ K * z.im → R ≤ z.im →
        ‖principalFaddeev d m n z - 1‖ ≤ C * Real.exp (-κ * z.im) := by
  obtain ⟨ε, C, κ, R, hε, hC, hκ, hR, hbound⟩ :=
    exists_norm_principalFaddeevComplex_sub_one_le d hd m n K
  refine ⟨C, κ, R, hC, hκ, hR, fun z hz hy => ?_⟩
  simpa only [principalFaddeevComplex_principalRoot d hd] using
    hbound (principalRoot d) z (by simpa using hε.le) hz hy

/-! ### The normalized lower product -/

/-- **New.** Uniformly for complex periods near the positive principal root, the principal Faddeev
product divided by the exponential of the sum of its three reflection exponents tends
exponentially to one in every lower sector. This is the quantitative lower clause of [RW26,
Radchenko--Wheeler (2026), Lemma 1, `lem:asymp`] applied factorwise to equation (20),
`eq:modulartofaddeevCF`. Specializes
`exists_norm_faddeevS_affine_div_exp_sub_one_le` at the three generator
factors. The complex-period neighborhood statement is absent from the searched [AFK25] and
[RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`]. -/
theorem exists_norm_principalFaddeevComplex_div_exp_sub_one_le
    (d : ℕ) (hd : 3 < d) (m n : ℤ) (K : ℝ) :
    ∃ ε C κ R : ℝ, 0 < ε ∧ 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ (τ z : ℂ), ‖τ - (principalRoot d : ℂ)‖ ≤ ε →
        |z.re| ≤ K * (-z.im) → R ≤ -z.im →
        ‖principalFaddeevComplex d m n z τ /
          Complex.exp (principalFaddeevLowerExponentComplex d m n z τ) - 1‖ ≤
            C * Real.exp (-κ * (-z.im)) := by
  obtain ⟨ε₂, C₂, κ₂, R₂, hε₂, hC₂, hκ₂, hR₂, h₂⟩ :=
    exists_norm_first_factor_div_exp_sub_one_le d hd n K
  obtain ⟨ε₁, C₁, κ₁, R₁, hε₁, hC₁, hκ₁, hR₁, h₁⟩ :=
    exists_norm_middle_factor_div_exp_sub_one_le d hd K
  obtain ⟨ε₀, C₀, κ₀, R₀, hε₀, hC₀, hκ₀, hR₀, h₀⟩ :=
    exists_norm_last_factor_div_exp_sub_one_le d hd m K
  let ε := min ε₂ (min ε₁ ε₀)
  let C₂₁ := (1 + C₂) * C₁ + C₂
  let C := (1 + C₂₁) * C₀ + C₂₁
  let κ₂₁ := min κ₂ κ₁
  let κ := min κ₂₁ κ₀
  let R := max R₂ (max R₁ R₀)
  refine ⟨ε, C, κ, R, (by dsimp [ε]; positivity), (by dsimp [C, C₂₁]; positivity),
    (by dsimp [κ, κ₂₁]; positivity), (by dsimp [R]; positivity), ?_⟩
  intro τ z hτ hz hy
  have hy0 : 0 ≤ -z.im := by
    linarith [hR₂, (le_max_left R₂ (max R₁ R₀)).trans hy]
  have h₂' := h₂ τ z (hτ.trans (min_le_left _ _)) hz
    ((le_max_left R₂ (max R₁ R₀)).trans hy)
  have h₁' := h₁ τ z (hτ.trans ((min_le_right _ _).trans (min_le_left _ _))) hz
    ((le_max_left R₁ R₀).trans (le_max_right R₂ (max R₁ R₀)) |>.trans hy)
  have h₀' := h₀ τ z (hτ.trans ((min_le_right _ _).trans (min_le_right _ _))) hz
    ((le_max_right R₁ R₀).trans (le_max_right R₂ (max R₁ R₀)) |>.trans hy)
  have h₂₁ := norm_mul_sub_one_le_of_exponential_bounds _ _ hκ₂.le hy0 h₂' h₁'
  have h₂₁₀ := norm_mul_sub_one_le_of_exponential_bounds _ _
    (le_min hκ₂.le hκ₁.le) hy0 h₂₁ h₀'
  rw [faddeevComplex_div_exp_eq_normalized_factors]
  simpa only [C, C₂₁, κ, κ₂₁] using h₂₁₀

/-- At the principal real period, the complex-period normalized lower estimate gives a
quantitative lower-sector bound for `principalFaddeev`. This is the fixed-period companion
to the independently proved limit `tendsto_principalFaddeev_div_exp_of_abs_re_le`. -/
theorem exists_norm_principalFaddeev_div_exp_sub_one_le
    (d : ℕ) (hd : 3 < d) (m n : ℤ) (K : ℝ) :
    ∃ C κ R : ℝ, 0 < C ∧ 0 < κ ∧ 0 < R ∧
      ∀ z : ℂ, |z.re| ≤ K * (-z.im) → R ≤ -z.im →
        ‖principalFaddeev d m n z /
          Complex.exp (principalFaddeevLowerExponentComplex d m n z (principalRoot d)) - 1‖ ≤
            C * Real.exp (-κ * (-z.im)) := by
  obtain ⟨ε, C, κ, R, hε, hC, hκ, hR, hbound⟩ :=
    exists_norm_principalFaddeevComplex_div_exp_sub_one_le d hd m n K
  refine ⟨C, κ, R, hC, hκ, hR, fun z hz hy => ?_⟩
  simpa only [principalFaddeevComplex_principalRoot d hd] using
    hbound (principalRoot d) z (by simpa using hε.le) hz hy

end SIC

end
