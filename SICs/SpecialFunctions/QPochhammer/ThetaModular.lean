/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.QPochhammer.Theta
import SICs.SpecialFunctions.QPochhammer.Divisor

/-!
# The theta product under the modular group

A two-sided bound comparing `θ(z/(cτ+d), γτ)` with `θ(z,τ)` for `γ ∈ SL₂(ℤ)`, in norm.

For `γ = (a b; c d) ∈ SL₂(ℤ)`, `τ ∈ ℍ`, `ε = cτ + d`, and `σ = γτ`, the two theta products
`θ(z,τ)` and `θ(z/ε,σ)` have the same zeros, the lattice `ℤ + ℤτ = ε(ℤ + ℤσ)`, all simple.
Classically their quotient is `exp(πi(cz²/ε - z + z/ε))` times a constant, the transformation law of
Jacobi's theta function under `SL₂(ℤ)` (D. Mumford, *Tata Lectures on Theta I*, Birkhäuser (1983),
Chapter I). This module proves the norm form of that law up to bounded factors, which is what the
estimates of the modular five-term integral in [RW26, Radchenko, Wheeler (2026), Appendix A.2,
`app:mod.fad`] use: there "the asymptotics are governed by a quotient of θ-functions", and in the
region where both q-products of the kernel are in theta form their zeros cancel.

## The argument

Use `N_τ(z) = ‖θ(z,τ)‖ exp(-Γ_τ(z))` with `Γ_τ = qThetaGrowth`. The lattice invariance and
global bounds of `N_τ` are proved in `Theta`. Since
`1/ε = a - cσ` and `τ/ε = dσ - b` (`inv_fltDenominator_eq`, `div_fltDenominator_eq`), a lattice
point `k + jτ` divided by `ε` is the lattice point `(ka - jb) + (jd - kc)σ` of `ℤ + ℤσ`, so
`z ↦ N_σ(z/ε)` is invariant under `ℤ + ℤτ` as well. At distance at least `r` from `ℤ + ℤτ`, the
normalized norm bounds, at `τ` and at `σ`,
bound each of `N_τ(z)` and `N_σ(z/ε)` above and below. Near the origin the simple zeros give
`θ(z/ε,σ)/θ(z,τ) → ϖ(σ,σ)²/(ε ϖ(τ,τ)²) ≠ 0` (`tendsto_qTheta_div_self`), so the quotient of the two
normalized norms is bounded above and below on a punctured disk; lattice invariance moves every
point near the lattice into that disk. At the lattice points both theta products vanish, and the
bounds hold trivially.
-/

noncomputable section

open Complex Real Filter
open scoped MatrixGroups Topology

namespace SIC

/-! ### The modular comparison of normalized norms

The lattice identities from `FractionalLinear` transport `N_σ(z/ε)`. Simple zeros compare it
with `N_τ(z)` near lattice points, while global normalized bounds handle distant points. -/

/-- A point far from the original lattice remains far from the transformed
lattice after division by the nonzero Jacobi denominator. -/
private lemma far_div_fltDenominator (γ : SL(2, ℤ)) (τ : ℂ)
    (hε : fltDenominator (γ : Mat(2, ℤ)) τ ≠ 0) (z : ℂ)
    (δ : ℝ) (hfar : ∀ m n : ℤ, δ ≤ ‖z - (m + n * τ)‖) :
    ∀ m n : ℤ,
      δ / ‖fltDenominator (γ : Mat(2, ℤ)) τ‖ ≤
        ‖z / fltDenominator (γ : Mat(2, ℤ)) τ -
          (m + n * flt (γ : Mat(2, ℤ)) τ)‖ := by
  intro m n
  let ε := fltDenominator (γ : Mat(2, ℤ)) τ
  let σ := flt (γ : Mat(2, ℤ)) τ
  have hmul := hfar (m * γ 1 1 + n * γ 0 1) (m * γ 1 0 + n * γ 0 0)
  rw [← fltDenominator_mul_intCast_add_intCast_mul γ τ hε m n] at hmul
  have hε' : ε ≠ 0 := hε
  have hcancel : ε * (z / ε) = z := by field_simp [hε']
  have heq : z - ε * ((m : ℂ) + n * σ) =
      ε * (z / ε - ((m : ℂ) + n * σ)) := by
    rw [mul_sub, hcancel]
  rw [heq, norm_mul] at hmul
  apply (div_le_iff₀ (norm_pos_iff.mpr hε)).2
  simpa only [mul_comm] using hmul

/-- The normalized theta norm has a positive linear slope at the origin; used
by `exists_local_qThetaNormalizedNorm_bounds`. -/
private lemma tendsto_qThetaNormalizedNorm_div_norm (τ : ℂ) (hτ : 0 < τ.im) :
    Tendsto (fun z : ℂ => qThetaNormalizedNorm z τ / ‖z‖) (𝓝[≠] 0)
      (𝓝 ‖-2 * π * I * qPochhammer τ τ ^ 2‖) := by
  have hg : ContinuousAt (fun z : ℂ => Real.exp (-qThetaGrowth z τ)) 0 := by
    unfold qThetaGrowth
    fun_prop
  have h := (tendsto_qTheta_div_self τ hτ).norm.mul
    (hg.tendsto.mono_left nhdsWithin_le_nhds)
  convert h using 1
  · ext z
    simp only [qThetaNormalizedNorm, norm_div]
    ring
  · simp [qThetaGrowth]

/-- Near zero, `qThetaNormalizedNorm` is bounded above and below by positive
multiples of distance to zero; used by the modular comparison. -/
private lemma exists_local_qThetaNormalizedNorm_bounds (τ : ℂ) (hτ : 0 < τ.im) :
    ∃ r > 0, ∃ c > 0, ∃ C > 0, ∀ z : ℂ, ‖z‖ < r →
      c * ‖z‖ ≤ qThetaNormalizedNorm z τ ∧ qThetaNormalizedNorm z τ ≤ C * ‖z‖ := by
  let L : ℝ := ‖-2 * π * I * qPochhammer τ τ ^ 2‖
  have hL : 0 < L := by
    apply norm_pos_iff.mpr
    simp [qPochhammer_tau_ne_zero τ hτ]
  have hlim := tendsto_qThetaNormalizedNorm_div_norm τ hτ
  have hlo : ∀ᶠ z : ℂ in 𝓝[≠] 0, L / 2 < qThetaNormalizedNorm z τ / ‖z‖ :=
    hlim.eventually (lt_mem_nhds (by dsimp [L] at *; linarith))
  have hhi : ∀ᶠ z : ℂ in 𝓝[≠] 0, qThetaNormalizedNorm z τ / ‖z‖ < L + 1 :=
    hlim.eventually (gt_mem_nhds (by linarith))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhdsWithin_iff.mp (hlo.and hhi)
  refine ⟨r, hr, L / 2, by linarith, L + 1, by linarith, ?_⟩
  intro z hz
  by_cases hz0 : z = 0
  · subst z
    have hzero : qTheta 0 τ = 0 :=
      (qTheta_eq_zero_iff 0 τ hτ).mpr ⟨0, 0, by simp⟩
    simp [qThetaNormalizedNorm, hzero]
  · have hmem : z ∈ Metric.ball (0 : ℂ) r ∩ {0}ᶜ := by
      constructor
      · simpa [Metric.mem_ball, dist_eq_norm] using hz
      · simpa using hz0
    obtain ⟨hl, hu⟩ := hball hmem
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    exact ⟨(le_div_iff₀ hn).mp (le_of_lt hl),
      (div_le_iff₀ hn).mp (le_of_lt hu)⟩

/-- The simple zeros at the origin give both modular comparisons on a disk;
used by `exists_modular_qThetaNormalizedNorm_comparison`. -/
private lemma exists_local_modular_comparison (γ : SL(2, ℤ)) (τ : ℂ)
    (hτ : 0 < τ.im) :
    ∃ r > 0, ∃ C₁ C₂ : ℝ, ∀ z : ℂ, ‖z‖ < r →
      qThetaNormalizedNorm (z / fltDenominator (γ : Mat(2, ℤ)) τ)
          (flt (γ : Mat(2, ℤ)) τ) ≤ C₁ * qThetaNormalizedNorm z τ ∧
        qThetaNormalizedNorm z τ ≤ C₂ *
          qThetaNormalizedNorm (z / fltDenominator (γ : Mat(2, ℤ)) τ)
            (flt (γ : Mat(2, ℤ)) τ) := by
  let ε := fltDenominator (γ : Mat(2, ℤ)) τ
  let σ := flt (γ : Mat(2, ℤ)) τ
  have hε : ε ≠ 0 := fltDenominator_ne_zero_of_im_ne_zero γ (ne_of_gt hτ)
  have hE : 0 < ‖ε‖ := norm_pos_iff.mpr hε
  obtain ⟨rτ, hrτ, cτ, hcτ, Cτ, hCτ, hbτ⟩ := exists_local_qThetaNormalizedNorm_bounds τ hτ
  obtain ⟨rσ, hrσ, cσ, hcσ, Cσ, hCσ, hbσ⟩ :=
    exists_local_qThetaNormalizedNorm_bounds σ (flt_im_pos γ hτ)
  refine ⟨min rτ (rσ * ‖ε‖), lt_min hrτ (mul_pos hrσ hE),
    Cσ / (cτ * ‖ε‖), Cτ * ‖ε‖ / cσ, ?_⟩
  intro z hz
  have hzτ := hbτ z (lt_of_lt_of_le hz (min_le_left _ _))
  have hzσ : ‖z / ε‖ < rσ := by
    rw [norm_div]
    exact (div_lt_iff₀ hE).2 (lt_of_lt_of_le hz (min_le_right _ _))
  have hzu := hbσ (z / ε) hzσ
  constructor
  · calc
      qThetaNormalizedNorm (z / ε) σ ≤ Cσ * ‖z / ε‖ := hzu.2
      _ = (Cσ / (cτ * ‖ε‖)) * (cτ * ‖z‖) := by
        rw [norm_div]
        field_simp [ne_of_gt hcτ, ne_of_gt hE]
      _ ≤ (Cσ / (cτ * ‖ε‖)) * qThetaNormalizedNorm z τ :=
        mul_le_mul_of_nonneg_left hzτ.1 (by positivity)
  · calc
      qThetaNormalizedNorm z τ ≤ Cτ * ‖z‖ := hzτ.2
      _ = (Cτ * ‖ε‖ / cσ) * (cσ * ‖z / ε‖) := by
        rw [norm_div]
        field_simp [ne_of_gt hcσ, ne_of_gt hE]
      _ ≤ (Cτ * ‖ε‖ / cσ) * qThetaNormalizedNorm (z / ε) σ :=
        mul_le_mul_of_nonneg_left hzu.1 (by positivity)

/-- The Gaussian bounds compare both normalized norms away from the original
lattice; used by `exists_modular_qThetaNormalizedNorm_comparison`. -/
private lemma exists_far_modular_comparison (γ : SL(2, ℤ)) (τ : ℂ)
    (hτ : 0 < τ.im) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C₁ C₂ : ℝ, ∀ z : ℂ,
      (∀ m n : ℤ, δ ≤ ‖z - (m + n * τ)‖) →
        qThetaNormalizedNorm (z / fltDenominator (γ : Mat(2, ℤ)) τ)
            (flt (γ : Mat(2, ℤ)) τ) ≤ C₁ * qThetaNormalizedNorm z τ ∧
          qThetaNormalizedNorm z τ ≤ C₂ *
            qThetaNormalizedNorm (z / fltDenominator (γ : Mat(2, ℤ)) τ)
              (flt (γ : Mat(2, ℤ)) τ) := by
  let ε := fltDenominator (γ : Mat(2, ℤ)) τ
  let σ := flt (γ : Mat(2, ℤ)) τ
  have hε : ε ≠ 0 := fltDenominator_ne_zero_of_im_ne_zero γ (ne_of_gt hτ)
  have hE : 0 < ‖ε‖ := norm_pos_iff.mpr hε
  obtain ⟨Cτ, _, hupperτ⟩ := exists_qThetaNormalizedNorm_le τ hτ
  obtain ⟨Cσ, _, hupperσ⟩ := exists_qThetaNormalizedNorm_le σ (flt_im_pos γ hτ)
  obtain ⟨cτ, hcτ, hlowerτ⟩ := exists_pos_le_qThetaNormalizedNorm τ hτ δ hδ
  obtain ⟨cσ, hcσ, hlowerσ⟩ :=
    exists_pos_le_qThetaNormalizedNorm σ (flt_im_pos γ hτ) (δ / ‖ε‖)
      (div_pos hδ hE)
  refine ⟨Cσ / cτ, Cτ / cσ, ?_⟩
  intro z hz
  have hzσ := hlowerσ (z / ε) (far_div_fltDenominator γ τ hε z δ hz)
  constructor
  · calc
      qThetaNormalizedNorm (z / ε) σ ≤ Cσ := hupperσ _
      _ = (Cσ / cτ) * cτ := by field_simp [ne_of_gt hcτ]
      _ ≤ (Cσ / cτ) * qThetaNormalizedNorm z τ :=
        mul_le_mul_of_nonneg_left (hlowerτ z hz) (by positivity)
  · calc
      qThetaNormalizedNorm z τ ≤ Cτ := hupperτ z
      _ = (Cτ / cσ) * cσ := by field_simp [ne_of_gt hcσ]
      _ ≤ (Cτ / cσ) * qThetaNormalizedNorm (z / ε) σ :=
        mul_le_mul_of_nonneg_left hzσ (by positivity)

/-- The transformed normalized norm is invariant under the original theta
lattice; used by `exists_modular_qThetaNormalizedNorm_comparison`. -/
private lemma qThetaNormalizedNorm_flt_lattice (γ : SL(2, ℤ)) (τ : ℂ)
    (hτ : 0 < τ.im) (z : ℂ) (m n : ℤ) :
    qThetaNormalizedNorm ((z + (m + n * τ)) /
        fltDenominator (γ : Mat(2, ℤ)) τ) (flt (γ : Mat(2, ℤ)) τ) =
      qThetaNormalizedNorm (z / fltDenominator (γ : Mat(2, ℤ)) τ)
        (flt (γ : Mat(2, ℤ)) τ) := by
  have hε := fltDenominator_ne_zero_of_im_ne_zero γ (ne_of_gt hτ)
  rw [add_div, intCast_add_intCast_mul_div_fltDenominator γ τ hε m n]
  exact qThetaNormalizedNorm_lattice _ _ (flt_im_pos γ hτ) _ _

/-- Lattice invariance transports a local comparison at zero to any nearby
lattice point; used by `exists_modular_qThetaNormalizedNorm_comparison`. -/
private lemma modular_comparison_near_lattice (γ : SL(2, ℤ)) (τ : ℂ)
    (hτ : 0 < τ.im) (r C₁ C₂ : ℝ)
    (hlocal : ∀ w : ℂ, ‖w‖ < r →
      qThetaNormalizedNorm (w / fltDenominator (γ : Mat(2, ℤ)) τ)
          (flt (γ : Mat(2, ℤ)) τ) ≤ C₁ * qThetaNormalizedNorm w τ ∧
        qThetaNormalizedNorm w τ ≤ C₂ * qThetaNormalizedNorm
          (w / fltDenominator (γ : Mat(2, ℤ)) τ)
          (flt (γ : Mat(2, ℤ)) τ))
    (z : ℂ) (m n : ℤ) (hnear : ‖z - (m + n * τ)‖ < r) :
    qThetaNormalizedNorm (z / fltDenominator (γ : Mat(2, ℤ)) τ)
        (flt (γ : Mat(2, ℤ)) τ) ≤ C₁ * qThetaNormalizedNorm z τ ∧
      qThetaNormalizedNorm z τ ≤ C₂ * qThetaNormalizedNorm
        (z / fltDenominator (γ : Mat(2, ℤ)) τ)
        (flt (γ : Mat(2, ℤ)) τ) := by
  let w := z - ((m : ℂ) + n * τ)
  have hzw : z = w + ((m : ℂ) + n * τ) := by dsimp [w]; ring
  have hτinv : qThetaNormalizedNorm z τ = qThetaNormalizedNorm w τ := by
    conv_lhs => rw [hzw]
    exact qThetaNormalizedNorm_lattice w τ hτ m n
  have hσinv : qThetaNormalizedNorm (z / fltDenominator (γ : Mat(2, ℤ)) τ)
      (flt (γ : Mat(2, ℤ)) τ) =
        qThetaNormalizedNorm (w / fltDenominator (γ : Mat(2, ℤ)) τ)
          (flt (γ : Mat(2, ℤ)) τ) := by
    conv_lhs => rw [hzw]
    exact qThetaNormalizedNorm_flt_lattice γ τ hτ w m n
  rw [hτinv, hσinv]
  exact hlocal w hnear

/-- Local simple-zero bounds and global Gaussian bounds give both modular
comparisons for normalized theta norms. -/
private lemma exists_modular_qThetaNormalizedNorm_comparison (γ : SL(2, ℤ)) (τ : ℂ)
    (hτ : 0 < τ.im) :
    ∃ C₁ C₂ : ℝ, ∀ z : ℂ,
      qThetaNormalizedNorm (z / fltDenominator (γ : Mat(2, ℤ)) τ)
          (flt (γ : Mat(2, ℤ)) τ) ≤ C₁ * qThetaNormalizedNorm z τ ∧
        qThetaNormalizedNorm z τ ≤ C₂ *
          qThetaNormalizedNorm (z / fltDenominator (γ : Mat(2, ℤ)) τ)
            (flt (γ : Mat(2, ℤ)) τ) := by
  obtain ⟨r, hr, C₁l, C₂l, hlocal⟩ := exists_local_modular_comparison γ τ hτ
  obtain ⟨C₁f, C₂f, hfar⟩ :=
    exists_far_modular_comparison γ τ hτ (r / 2) (by linarith)
  refine ⟨max C₁l C₁f, max C₂l C₂f, ?_⟩
  intro z
  by_cases hz : ∀ m n : ℤ, r / 2 ≤ ‖z - (m + n * τ)‖
  · obtain ⟨h₁, h₂⟩ := hfar z hz
    exact ⟨h₁.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (qThetaNormalizedNorm_nonneg z τ)),
      h₂.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (qThetaNormalizedNorm_nonneg _ _))⟩
  · have hnear : ∃ m n : ℤ, ‖z - (m + n * τ)‖ < r / 2 := by
      simpa only [not_forall, not_le] using hz
    obtain ⟨m, n, hmn⟩ := hnear
    obtain ⟨h₁, h₂⟩ := modular_comparison_near_lattice γ τ hτ r C₁l C₂l
      hlocal z m n (lt_trans hmn (by linarith))
    exact ⟨h₁.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (qThetaNormalizedNorm_nonneg z τ)),
      h₂.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (qThetaNormalizedNorm_nonneg _ _))⟩

/-- For `γ ∈ SL₂(ℤ)` and `τ ∈ ℍ`, with `ε = j_γ(τ)` and `σ = γτ`,
`‖θ(z/ε,σ)‖ ≤ C exp(Γ_σ(z/ε) - Γ_τ(z)) ‖θ(z,τ)‖` for every `z`, where `Γ = qThetaGrowth`: one half
of the norm form of the transformation law of Jacobi's theta function. -/
theorem exists_norm_qTheta_flt_le (γ : SL(2, ℤ)) (τ : ℂ) (hτ : 0 < τ.im) :
    ∃ C, ∀ z : ℂ,
      ‖qTheta (z / fltDenominator (γ : Mat(2, ℤ)) τ) (flt (γ : Mat(2, ℤ)) τ)‖ ≤
        C * Real.exp (qThetaGrowth (z / fltDenominator (γ : Mat(2, ℤ)) τ)
            (flt (γ : Mat(2, ℤ)) τ) - qThetaGrowth z τ) * ‖qTheta z τ‖ := by
  obtain ⟨C₁, _, h⟩ := exists_modular_qThetaNormalizedNorm_comparison γ τ hτ
  exact ⟨C₁, fun z => norm_qTheta_le_of_normalized_le _ _ _ _ C₁ (h z).1⟩

/-- For `γ ∈ SL₂(ℤ)` and `τ ∈ ℍ`, with `ε = j_γ(τ)` and `σ = γτ`,
`‖θ(z,τ)‖ ≤ C exp(Γ_τ(z) - Γ_σ(z/ε)) ‖θ(z/ε,σ)‖` for every `z`, where `Γ = qThetaGrowth`: the other
half of the norm form of the transformation law of Jacobi's theta function. -/
theorem exists_norm_qTheta_le_flt (γ : SL(2, ℤ)) (τ : ℂ) (hτ : 0 < τ.im) :
    ∃ C, ∀ z : ℂ,
      ‖qTheta z τ‖ ≤
        C * Real.exp (qThetaGrowth z τ - qThetaGrowth (z / fltDenominator (γ : Mat(2, ℤ)) τ)
            (flt (γ : Mat(2, ℤ)) τ)) *
          ‖qTheta (z / fltDenominator (γ : Mat(2, ℤ)) τ) (flt (γ : Mat(2, ℤ)) τ)‖ := by
  obtain ⟨_, C₂, h⟩ := exists_modular_qThetaNormalizedNorm_comparison γ τ hτ
  exact ⟨C₂, fun z => norm_qTheta_le_of_normalized_le _ _ _ _ C₂ (h z).2⟩

end SIC
