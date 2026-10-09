/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.Faddeev.Modular
import SICs.SpecialFunctions.QPochhammer.Growth
import SICs.SpecialFunctions.QPochhammer.ThetaModular

/-!
# Growth of the modular q-product on the upper half plane

Gaussian bounds for `Φ_{γ,n,0}(z;τ)` and its inverse away from their genuine poles.

This module quantifies the growth statements in the proof of [RW26, Radchenko, Wheeler (2026),
Theorem 3, `thm:5term.mod.fad`] in Appendix A.2, `app:mod.fad`, for the modular q-product
`Φ_{γ,n,0}(z;τ) = ϖ(z+nτ,τ)/ϖ(z/ε,σ)` of equation (1), `eq:phigam.def`: in the sectors where
both products tend to one it is bounded, and where the asymptotics "are governed by a quotient of
θ-functions" it grows like a quotient of Gaussians. Throughout, `γ ∈ SL₂(ℤ)`, `τ ∈ ℍ`,
`ε = j_γ(τ)`, `σ = γτ`, and `Γ = qPochhammerGrowth`.

## The argument

The numerator vanishes on `ℤ - (n + ℕ)τ` and the denominator on `ε(ℤ - ℕσ)`, both subsets of the
lattice `ℤ + ℤτ = ε(ℤ + ℤσ)`. A common zero is a removable singularity of the quotient, where the
Lean value is the junk value `0`; the others are its poles and zeros. The bound
`‖Φ_{γ,n,0}(z;τ)‖ ≤ C exp(Γ_τ(z+nτ) - Γ_σ(z/ε))` away from the poles follows by applying the
generic quotient estimates of `SICs.SpecialFunctions.QPochhammer.Growth` in three regions.

- If `Im(z/ε) ≥ Im σ/2`, its distance to every denominator zero is at least `Im σ/2`, so
  `exists_norm_qPochhammer_div_le_exp` applies.
- If `Im(z/ε) ≤ Im σ/2` and `Im(z+nτ) ≥ Im τ/2`, the numerator is bounded and `Γ_τ(z+nτ) = 0`.
  A zero of the denominator near `z` is a pole, since a common zero `u` has `Im(u+nτ) ≤ 0`; so
  `denominator_zero_distance` supplies the separation for the same quotient estimate.
- If `Im(z/ε) ≤ Im σ/2` and `Im(z+nτ) ≤ Im τ/2`, the common zeros lie in this region, and both
  products are written in theta form, `ϖ(u,τ) = θ(u,τ)/ϖ(τ-u,τ)`, whose second factors are
  bounded above and below here. The theta comparison `exists_norm_qTheta_le_flt` shifts by `nτ`
  using `norm_qTheta_add_intCast_mul`; then
  `exists_norm_qPochhammer_div_le_of_norm_qTheta_le` gives the q-product bound with no distance
  condition, since the zeros cancel.

For the inverse, the two periods exchange roles, `numerator_zero_distance` supplies separation in
the mixed region, and the theta region uses `exists_norm_qTheta_flt_le`.
-/

noncomputable section

open Complex Real
open scoped MatrixGroups

namespace SIC

/-! ### Growth

The pole and zero sets supply the denominator separation needed for the generic Gaussian
quotient bound. The modular theta comparisons supply the remaining region; translating by `nτ`
changes the theta norm by exactly its Gaussian factor. Constants depend on `γ`, `n`, `τ`, and the
distance `δ` to the poles or zeros. -/

/-- The modular period has positive height and its Jacobi denominator has positive norm. -/
private lemma modular_growth_period_data (γ : SL(2, ℤ)) (τ : ℂ) (hτ : 0 < τ.im) :
    0 < (flt (γ : Mat(2, ℤ)) τ).im ∧
      0 < ‖fltDenominator (γ : Mat(2, ℤ)) τ‖ :=
  ⟨flt_im_pos γ hτ, norm_pos_iff.mpr
    (fltDenominator_ne_zero_of_im_ne_zero γ (ne_of_gt hτ))⟩

/-- A denominator zero stays a definite distance from a point above the numerator's zero rows.
Used by `exists_norm_faddeevModularUHP_le`. -/
private lemma denominator_zero_distance (γ : SL(2, ℤ)) (n : ℤ) (τ : ℂ)
    (hτ : 0 < τ.im) (δ : ℝ) (z : ℂ)
    (hz : τ.im / 2 ≤ (z + n * τ).im)
    (haway : ∀ u ∈ faddeevModularUHPPoles γ n τ, δ ≤ ‖z - u‖)
    (k : ℤ) (j : ℕ) :
    min δ (τ.im / 2) / ‖fltDenominator (γ : Mat(2, ℤ)) τ‖ ≤
      ‖z / fltDenominator (γ : Mat(2, ℤ)) τ -
        ((k : ℂ) - j * flt (γ : Mat(2, ℤ)) τ)‖ := by
  let ε := fltDenominator (γ : Mat(2, ℤ)) τ
  let σ := flt (γ : Mat(2, ℤ)) τ
  let v : ℂ := (k : ℂ) - j * σ
  let u : ℂ := ε * v
  have hε : ε ≠ 0 := fltDenominator_ne_zero_of_im_ne_zero γ (ne_of_gt hτ)
  have hεnorm : 0 < ‖ε‖ := norm_pos_iff.mpr hε
  have hdiv : u / ε = v := by simp [u, hε]
  have hden : qPochhammer (u / ε) σ = 0 := by
    rw [hdiv]
    exact qPochhammer_intCast_sub_natCast_mul_eq_zero k j σ
  have hd : min δ (τ.im / 2) ≤ ‖z - u‖ := by
    by_cases hnum : qPochhammer (u + n * τ) τ = 0
    · have him := im_nonpos_of_qPochhammer_eq_zero hτ hnum
      have hshift : (z - u).im = (z + n * τ).im - (u + n * τ).im := by
        simp only [Complex.sub_im, Complex.add_im]
        ring
      have hheight : τ.im / 2 ≤ (z - u).im := by rw [hshift]; linarith
      exact (min_le_right _ _).trans
        (hheight.trans ((le_abs_self _).trans (Complex.abs_im_le_norm _)))
    · exact (min_le_left _ _).trans
        (haway u ⟨hden, hnum⟩)
  have hscale : ‖z - u‖ = ‖ε‖ * ‖z / ε - v‖ := by
    have heq : z - u = ε * (z / ε - v) := by
      dsimp [u]
      field_simp [hε]
    rw [heq, norm_mul]
  rw [hscale] at hd
  apply (div_le_iff₀ hεnorm).mpr
  simpa [mul_comm] using hd

/-- A numerator zero stays a definite distance from a point above the denominator's zero rows.
Used by `exists_norm_inv_faddeevModularUHP_le`. -/
private lemma numerator_zero_distance (γ : SL(2, ℤ)) (n : ℤ) (τ : ℂ)
    (hτ : 0 < τ.im) (δ : ℝ) (z : ℂ)
    (hz : (flt (γ : Mat(2, ℤ)) τ).im / 2 ≤
      (z / fltDenominator (γ : Mat(2, ℤ)) τ).im)
    (haway : ∀ u ∈ faddeevModularUHPZeros γ n τ, δ ≤ ‖z - u‖)
    (k : ℤ) (j : ℕ) :
    min δ (‖fltDenominator (γ : Mat(2, ℤ)) τ‖ *
      (flt (γ : Mat(2, ℤ)) τ).im / 2) ≤
      ‖z + n * τ - ((k : ℂ) - j * τ)‖ := by
  let ε := fltDenominator (γ : Mat(2, ℤ)) τ
  let σ := flt (γ : Mat(2, ℤ)) τ
  let v : ℂ := (k : ℂ) - j * τ
  let u : ℂ := v - n * τ
  have hε : ε ≠ 0 := fltDenominator_ne_zero_of_im_ne_zero γ (ne_of_gt hτ)
  have hεnorm : 0 < ‖ε‖ := norm_pos_iff.mpr hε
  have hnum : qPochhammer (u + n * τ) τ = 0 := by
    have heq : u + n * τ = v := by dsimp [u]; ring
    rw [heq]
    exact qPochhammer_intCast_sub_natCast_mul_eq_zero k j τ
  have hd : min δ (‖ε‖ * σ.im / 2) ≤ ‖z - u‖ := by
    by_cases hden : qPochhammer (u / ε) σ = 0
    · have him := im_nonpos_of_qPochhammer_eq_zero (flt_im_pos γ hτ) hden
      have hheight : σ.im / 2 ≤ (z / ε - u / ε).im := by
        rw [Complex.sub_im]
        linarith
      have hdist : σ.im / 2 ≤ ‖z / ε - u / ε‖ :=
        hheight.trans ((le_abs_self _).trans (Complex.abs_im_le_norm _))
      have heq : z - u = ε * (z / ε - u / ε) := by
        field_simp [hε]
      rw [heq, norm_mul]
      have hmul := mul_le_mul_of_nonneg_left hdist hεnorm.le
      exact (min_le_right _ _).trans (by nlinarith)
    · exact (min_le_left _ _).trans (haway u ⟨hnum, hden⟩)
  have heq : z + n * τ - v = z - u := by dsimp [u]; ring
  rwa [heq]

/-- A point above half the period height stays that far from every q-product zero. -/
private lemma qPochhammer_zero_distance_of_half_height (τ y : ℂ) (hτ : 0 < τ.im)
    (hy : τ.im / 2 ≤ y.im) (k : ℤ) (j : ℕ) :
    τ.im / 2 ≤ ‖y - ((k : ℂ) - j * τ)‖ := by
  have him : (y - ((k : ℂ) - j * τ)).im = y.im + (j : ℝ) * τ.im := by
    simp [Complex.sub_im, Complex.mul_im]
  have hnonneg : 0 ≤ (j : ℝ) * τ.im := mul_nonneg (Nat.cast_nonneg _) hτ.le
  calc
    τ.im / 2 ≤ (y - ((k : ℂ) - j * τ)).im := by rw [him]; linarith
    _ ≤ |(y - ((k : ℂ) - j * τ)).im| := le_abs_self _
    _ ≤ ‖y - ((k : ℂ) - j * τ)‖ := Complex.abs_im_le_norm _

/-- A theta comparison is unchanged after shifting either argument, once its Gaussian
exponent is shifted with it. -/
private lemma norm_qTheta_shift_comparison (τ₁ τ₂ a a' b b' : ℂ) (B : ℝ)
    (hbase : ‖qTheta a τ₁‖ ≤
      B * Real.exp (qThetaGrowth a τ₁ - qThetaGrowth b τ₂) * ‖qTheta b τ₂‖)
    (ha : ‖qTheta a' τ₁‖ =
      Real.exp (qThetaGrowth a' τ₁ - qThetaGrowth a τ₁) * ‖qTheta a τ₁‖)
    (hb : ‖qTheta b' τ₂‖ =
      Real.exp (qThetaGrowth b' τ₂ - qThetaGrowth b τ₂) * ‖qTheta b τ₂‖) :
    ‖qTheta a' τ₁‖ ≤
      max B 1 * Real.exp (qThetaGrowth a' τ₁ - qThetaGrowth b' τ₂) *
        ‖qTheta b' τ₂‖ := by
  have hbase' : ‖qTheta a τ₁‖ ≤
      max B 1 * Real.exp (qThetaGrowth a τ₁ - qThetaGrowth b τ₂) *
        ‖qTheta b τ₂‖ := by
    calc
      _ ≤ B * Real.exp (qThetaGrowth a τ₁ - qThetaGrowth b τ₂) *
          ‖qTheta b τ₂‖ := hbase
      _ ≤ _ := by gcongr; exact le_max_left _ _
  rw [ha]
  calc
    _ ≤ Real.exp (qThetaGrowth a' τ₁ - qThetaGrowth a τ₁) *
        (max B 1 * Real.exp (qThetaGrowth a τ₁ - qThetaGrowth b τ₂) *
          ‖qTheta b τ₂‖) :=
      mul_le_mul_of_nonneg_left hbase' (Real.exp_nonneg _)
    _ = max B 1 * Real.exp (qThetaGrowth a' τ₁ - qThetaGrowth b' τ₂) *
        ‖qTheta b' τ₂‖ := by
      have hexp : Real.exp (qThetaGrowth a' τ₁ - qThetaGrowth a τ₁) *
          Real.exp (qThetaGrowth a τ₁ - qThetaGrowth b τ₂) =
          Real.exp (qThetaGrowth a' τ₁ - qThetaGrowth b' τ₂) *
            Real.exp (qThetaGrowth b' τ₂ - qThetaGrowth b τ₂) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [hb]
      calc
        _ = max B 1 * (Real.exp (qThetaGrowth a' τ₁ - qThetaGrowth a τ₁) *
            Real.exp (qThetaGrowth a τ₁ - qThetaGrowth b τ₂)) *
            ‖qTheta b τ₂‖ := by ring
        _ = _ := by rw [hexp]; ring

/-- Three height regions reduce a global bound to its two upper regions and theta region. -/
private lemma bound_of_three_height_regions (x y : ℂ) (t₁ t₂ E V C₁ C₂ C₃ : ℝ)
    (hden : t₂ / 2 ≤ y.im → V ≤ C₁ * Real.exp E)
    (hnum : t₁ / 2 ≤ x.im → V ≤ C₂ * Real.exp E)
    (htheta : x.im ≤ t₁ / 2 → y.im ≤ t₂ / 2 → V ≤ C₃ * Real.exp E) :
    V ≤ max C₁ (max C₂ C₃) * Real.exp E := by
  by_cases hy : t₂ / 2 ≤ y.im
  · exact (hden hy).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _))
  · by_cases hx : t₁ / 2 ≤ x.im
    · exact (hnum hx).trans (mul_le_mul_of_nonneg_right
        ((le_max_left _ _).trans (le_max_right _ _)) (Real.exp_nonneg _))
    · exact (htheta (le_of_lt (lt_of_not_ge hx))
        (le_of_lt (lt_of_not_ge hy))).trans (mul_le_mul_of_nonneg_right
          ((le_max_right _ _).trans (le_max_right _ _)) (Real.exp_nonneg _))

/-- Away from its poles, `‖Φ_{γ,n,0}(z;τ)‖ ≤ C exp(Γ_τ(z+nτ) - Γ_σ(z/ε))`, with
`Γ = qPochhammerGrowth`: the growth of the modular q-product of
[RW26, Radchenko, Wheeler (2026), equation (1), `eq:phigam.def`] used in Appendix A.2,
`app:mod.fad`. -/
theorem exists_norm_faddeevModularUHP_le (γ : SL(2, ℤ)) (n : ℤ) (τ : ℂ) (hτ : 0 < τ.im)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C, ∀ z : ℂ, (∀ u ∈ faddeevModularUHPPoles γ n τ, δ ≤ ‖z - u‖) →
      ‖faddeevModularUHP γ n 0 z τ‖ ≤
        C * Real.exp (qPochhammerGrowth (z + n * τ) τ -
          qPochhammerGrowth (z / fltDenominator (γ : Mat(2, ℤ)) τ) (flt (γ : Mat(2, ℤ)) τ)) := by
  let ε := fltDenominator (γ : Mat(2, ℤ)) τ
  let σ := flt (γ : Mat(2, ℤ)) τ
  obtain ⟨hσ, hε⟩ := modular_growth_period_data γ τ hτ
  let d := min δ (τ.im / 2) / ‖ε‖
  have hd : 0 < d := div_pos (lt_min hδ (by positivity)) hε
  obtain ⟨C₁, h₁⟩ := exists_norm_qPochhammer_div_le_exp τ σ hτ hσ (σ.im / 2)
    (by positivity)
  obtain ⟨C₂, h₂⟩ := exists_norm_qPochhammer_div_le_exp τ σ hτ hσ d hd
  obtain ⟨Cq, hq⟩ := exists_norm_qPochhammer_div_le_of_norm_qTheta_le τ σ hτ hσ
  obtain ⟨B, hB⟩ := exists_norm_qTheta_le_flt γ τ hτ
  let K := max B 1
  have hK : 0 ≤ K := le_trans zero_le_one (le_max_right _ _)
  refine ⟨max C₁ (max C₂ (Cq * K)), ?_⟩
  intro z haway
  let x := z + n * τ
  let y := z / ε
  let E := qPochhammerGrowth x τ - qPochhammerGrowth y σ
  apply bound_of_three_height_regions x y τ.im σ.im E
    ‖faddeevModularUHP γ n 0 z τ‖ C₁ C₂ (Cq * K)
  · intro hy
    simpa [faddeevModularUHP] using h₁ x y
      (qPochhammer_zero_distance_of_half_height σ y hσ hy)
  · intro hx
    simpa [faddeevModularUHP] using h₂ x y (by
      intro k j
      exact denominator_zero_distance γ n τ hτ δ z hx haway k j)
  · intro hx hy
    simpa [faddeevModularUHP] using hq K x y hK hx hy
      (norm_qTheta_shift_comparison τ σ z x y y B (hB z)
        (norm_qTheta_add_intCast_mul z τ hτ n) (by simp))

/-- Away from its zeros, `‖Φ_{γ,n,0}(z;τ)⁻¹‖ ≤ C exp(Γ_σ(z/ε) - Γ_τ(z+nτ))`, with
`Γ = qPochhammerGrowth`. At a common zero of the two products the Lean value of `Φ_{γ,n,0}` is
`0`, and so is that of its inverse. -/
theorem exists_norm_inv_faddeevModularUHP_le (γ : SL(2, ℤ)) (n : ℤ) (τ : ℂ) (hτ : 0 < τ.im)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C, ∀ z : ℂ, (∀ u ∈ faddeevModularUHPZeros γ n τ, δ ≤ ‖z - u‖) →
      ‖(faddeevModularUHP γ n 0 z τ)⁻¹‖ ≤
        C * Real.exp (qPochhammerGrowth (z / fltDenominator (γ : Mat(2, ℤ)) τ)
            (flt (γ : Mat(2, ℤ)) τ) - qPochhammerGrowth (z + n * τ) τ) := by
  let ε := fltDenominator (γ : Mat(2, ℤ)) τ
  let σ := flt (γ : Mat(2, ℤ)) τ
  obtain ⟨hσ, hε⟩ := modular_growth_period_data γ τ hτ
  let d := min δ (‖ε‖ * σ.im / 2)
  have hd : 0 < d := lt_min hδ (by positivity)
  obtain ⟨C₁, h₁⟩ := exists_norm_qPochhammer_div_le_exp σ τ hσ hτ (τ.im / 2)
    (by positivity)
  obtain ⟨C₂, h₂⟩ := exists_norm_qPochhammer_div_le_exp σ τ hσ hτ d hd
  obtain ⟨Cq, hq⟩ := exists_norm_qPochhammer_div_le_of_norm_qTheta_le σ τ hσ hτ
  obtain ⟨B, hB⟩ := exists_norm_qTheta_flt_le γ τ hτ
  let K := max B 1
  have hK : 0 ≤ K := le_trans zero_le_one (le_max_right _ _)
  refine ⟨max C₁ (max C₂ (Cq * K)), ?_⟩
  intro z haway
  let x := z + n * τ
  let y := z / ε
  let E := qPochhammerGrowth y σ - qPochhammerGrowth x τ
  apply bound_of_three_height_regions y x σ.im τ.im E
    ‖(faddeevModularUHP γ n 0 z τ)⁻¹‖ C₁ C₂ (Cq * K)
  · intro hx
    simpa [faddeevModularUHP, inv_div] using h₁ y x
      (qPochhammer_zero_distance_of_half_height τ x hτ hx)
  · intro hy
    simpa [faddeevModularUHP, inv_div] using h₂ y x (by
      intro k j
      exact numerator_zero_distance γ n τ hτ δ z hy haway k j)
  · intro hy hx
    simpa [faddeevModularUHP, inv_div] using hq K y x hK hy hx
      (norm_qTheta_shift_comparison σ τ y y z x B (hB z)
        (by simp) (norm_qTheta_add_intCast_mul z τ hτ n))

end SIC
