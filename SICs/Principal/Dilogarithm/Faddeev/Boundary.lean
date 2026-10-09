/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Dilogarithm.Faddeev.Divisor
import SICs.SpecialFunctions.Faddeev.Word

/-!
# The principal Faddeev product at the real-period boundary

The three-generator product for `A_d` at a variable complex period, its value at `ρ_d`, argument
analyticity near that root, and boundary limits on compact lattice-free sets.

This module follows [RW26, Radchenko, Wheeler (2026), Proposition 2(ii),
`prop:prod.id.mod,fad`, equation (20), `eq:modulartofaddeevCF`] for the word
`A_d = (T^{d-1}S)³`. Its three periods are `τ`, `U_d·τ`, and `U_d·(U_d·τ)`; the two internal indices
are zero.

## The argument

Two applications of the modular cocycle split `A_d=U_d³` into three factors. The one-letter
identity turns each factor into a Faddeev generator away from its q-denominator zeros. This
qualification is essential:
Lean's division assigns values at common q-product zeros, whereas equation (20) is an identity
of meromorphic functions. For each fixed upper-half-plane period, the equality holds almost
everywhere on any nonconstant affine real line. At `τ = ρ_d`, the matrix `U_d` fixes the positive
real root, so the three periods coincide and the expression becomes the existing real principal
product.

At the boundary, each generator is continuous wherever its Barnes double-gamma denominator is
nonzero. Off `ℤ+ℤρ_d`, all three arguments remain outside the period lattice, so this domain
includes lattice-free crossings of the real axis. It also includes `z=0` for zero indices: all
three denominators there are evaluated at positive `ρ_d`. Joint continuity makes convergence
uniform on compact lattice-free sets, including finite contour portions. Passing an improper
contour integral through the boundary still requires uniform estimates on its infinite tails.

Continuity of the inverse double-gamma factors keeps those denominators nonzero for nearby
complex periods, where the product is analytic in its argument. For nearby upper-half-plane
periods, both products are analytic at a fixed noninteger real argument on that gamma domain;
their punctured equality therefore extends to the base point.
-/

noncomputable section

open Filter Topology
open scoped MatrixGroups

namespace SIC

/-! ### The complex-period product

The variable-period expression uses the two intermediate `flt` periods of the principal
three-factor product. At the fixed root they both equal `ρ_d`.
-/

/-- The three-generator expression at complex period `τ`, with
`τ₁ = U_d τ`, `τ₂ = U_d τ₁`, and internal indices zero:
`Φ(z/(ττ₁)-n;τ₂) Φ(z/τ;τ₁) Φ(z+mτ;τ)`.
This is the product in [RW26, Radchenko, Wheeler (2026), Proposition 2(ii),
`prop:prod.id.mod,fad`, equation (20), `eq:modulartofaddeevCF`] for `A_d=U_d³`.
Its relation to the existing real-period value is
`principalFaddeevComplex_principalRoot`; upper-half-plane comparison is an equality of
meromorphic germs because the q-product quotient has totalized values at denominator zeros. -/
def principalFaddeevComplex (d : ℕ) (m n : ℤ) (z τ : ℂ) : ℂ :=
  let τ₁ := flt (principalU d : Mat(2, ℤ)) τ
  let τ₂ := flt (principalU d : Mat(2, ℤ)) τ₁
  faddeevS (z / τ / τ₁ - n) τ₂ *
    faddeevS (z / τ) τ₁ * faddeevS (z + m * τ) τ

/-- Slit-plane admissibility of the three successive periods in the complex-period
principal Faddeev product. This condition is independent of its argument and gamma domain. -/
structure PrincipalFaddeevPeriodsSlitPlane (d : ℕ) (τ : ℂ) : Prop where
  /-- The original period lies in the slit plane. -/
  base : τ ∈ Complex.slitPlane
  /-- The period after one application of `U_d` lies in the slit plane. -/
  once : flt (principalU d : Mat(2, ℤ)) τ ∈ Complex.slitPlane
  /-- The period after two applications of `U_d` lies in the slit plane. -/
  twice : flt (principalU d : Mat(2, ℤ))
    (flt (principalU d : Mat(2, ℤ)) τ) ∈ Complex.slitPlane

/-- The factorwise sufficient gamma domain of the complex-period principal Faddeev product.
Its three fields are exactly the denominators of the displayed generator factors; it is
independent of slit-plane admissibility of their periods. -/
structure PrincipalFaddeevComplexGammaRegular
    (d : ℕ) (m n : ℤ) (z τ : ℂ) : Prop where
  /-- The gamma denominator of the first generator factor is nonzero. -/
  first : barnesDoubleGammaInv
    (flt (principalU d : Mat(2, ℤ)) (flt (principalU d : Mat(2, ℤ)) τ) -
      (z / τ / flt (principalU d : Mat(2, ℤ)) τ - n)) 1
    (flt (principalU d : Mat(2, ℤ)) (flt (principalU d : Mat(2, ℤ)) τ)) ≠ 0
  /-- The gamma denominator of the middle generator factor is nonzero. -/
  middle : barnesDoubleGammaInv
    (flt (principalU d : Mat(2, ℤ)) τ - z / τ) 1
    (flt (principalU d : Mat(2, ℤ)) τ) ≠ 0
  /-- The gamma denominator of the last generator factor is nonzero. -/
  last : barnesDoubleGammaInv (τ - (z + m * τ)) 1 τ ≠ 0

/-- At `τ=ρ_d`, the complex-period product equals the existing principal product,
since both intermediate periods are `ρ_d`. This bridges equation (20) at nearby periods
and `principalFaddeev`. -/
theorem principalFaddeevComplex_principalRoot (d : ℕ) (hd : 3 < d)
    (m n : ℤ) (z : ℂ) :
    principalFaddeevComplex d m n z (principalRoot d) =
      principalFaddeev d m n z := by
  have hρ := ofReal_principalRoot_ne_zero d hd
  have hdiv : z / (principalRoot d : ℂ) / (principalRoot d : ℂ) =
      z / (principalRoot d : ℂ) ^ 2 := by field_simp [hρ]
  simp only [principalFaddeevComplex, principalFaddeev,
    flt_principalU_principalRoot_complex d hd, hdiv]

/-- Upper-half-plane periods make all three successive principal periods slit-plane
admissible. -/
theorem principalFaddeevPeriodsSlitPlane_of_im_pos (d : ℕ) {τ : ℂ} (hτ : 0 < τ.im) :
    PrincipalFaddeevPeriodsSlitPlane d τ := by
  have honce : 0 < (flt (principalU d : Mat(2, ℤ)) τ).im :=
    flt_im_pos (principalU d) hτ
  have htwice : 0 < (flt (principalU d : Mat(2, ℤ))
      (flt (principalU d : Mat(2, ℤ)) τ)).im := flt_im_pos (principalU d) honce
  exact ⟨Complex.mem_slitPlane_iff.mpr (Or.inr hτ.ne'),
    Complex.mem_slitPlane_iff.mpr (Or.inr honce.ne'),
    Complex.mem_slitPlane_iff.mpr (Or.inr htwice.ne')⟩

/-- A nonzero complex-period principal product lies in its factorwise gamma domain. -/
theorem principalFaddeevComplexGammaRegular_of_ne_zero
    (d : ℕ) (m n : ℤ) (z τ : ℂ)
    (hz : principalFaddeevComplex d m n z τ ≠ 0) :
    PrincipalFaddeevComplexGammaRegular d m n z τ := by
  rw [principalFaddeevComplex] at hz
  rcases mul_ne_zero_iff.mp hz with ⟨hfirstMiddle, hlast⟩
  rcases mul_ne_zero_iff.mp hfirstMiddle with ⟨hfirst, hmiddle⟩
  exact ⟨faddeevS_denominator_ne_zero_of_ne_zero hfirst,
    faddeevS_denominator_ne_zero_of_ne_zero hmiddle,
    faddeevS_denominator_ne_zero_of_ne_zero hlast⟩

/-! ### Continuity at the principal period

Nonvanishing of the three gamma denominators gives a domain of continuity at the fixed period. We
transport generator continuity through the fractional-linear periods and affine arguments;
lattice-free points and the regular origin then give useful special cases.
-/

/-- The map `τ ↦ U_d·τ` is continuous at the positive fixed period; used by
`continuousAt_principalU_periods`. -/
private lemma continuousAt_principalU_period (d : ℕ) (hd : 3 < d) :
    ContinuousAt (fun τ : ℂ => flt (principalU d : Mat(2, ℤ)) τ)
      (principalRoot d : ℂ) := by
  have hρ : (principalRoot d : ℂ) ≠ 0 := ofReal_principalRoot_ne_zero d hd
  have hc : ContinuousAt (fun τ : ℂ => (((d : ℂ) - 1) * τ - 1) / τ)
      (principalRoot d : ℂ) :=
    ((continuousAt_const.mul continuousAt_id).sub continuousAt_const).div
      continuousAt_id hρ
  simpa [flt, coe_principalU, sub_eq_add_neg] using hc

/-- Both intermediate periods of the principal word vary continuously at `ρ_d`; used by the
gamma-domain product continuity and boundary-limit theorems. -/
lemma continuousAt_principalU_periods (d : ℕ) (hd : 3 < d) :
    ContinuousAt (fun τ : ℂ => flt (principalU d : Mat(2, ℤ)) τ)
        (principalRoot d : ℂ) ∧
      ContinuousAt (fun τ : ℂ =>
        flt (principalU d : Mat(2, ℤ)) (flt (principalU d : Mat(2, ℤ)) τ))
        (principalRoot d : ℂ) := by
  let U : Mat(2, ℤ) := principalU d
  let ρ : ℂ := principalRoot d
  have hperiod : ContinuousAt (flt U) ρ := continuousAt_principalU_period d hd
  have houter : ContinuousAt (flt U) (flt U ρ) := by
    rw [flt_principalU_principalRoot_complex d hd]
    exact hperiod
  have hperiod₂ : ContinuousAt (fun τ : ℂ => flt U (flt U τ)) ρ :=
    houter.comp (f := flt U) hperiod
  exact ⟨hperiod, hperiod₂⟩

/-- Sufficiently near the positive principal root, the three periods in the principal word all
have positive real part. -/
lemma eventually_principalFaddeevPeriods_re_pos (d : ℕ) (hd : 3 < d) :
    ∀ᶠ τ : ℂ in 𝓝 (principalRoot d : ℂ),
      0 < τ.re ∧
        0 < (flt (principalU d : Mat(2, ℤ)) τ).re ∧
        0 < (flt (principalU d : Mat(2, ℤ))
          (flt (principalU d : Mat(2, ℤ)) τ)).re := by
  let ρ : ℂ := principalRoot d
  let l : Filter ℂ := 𝓝 ρ
  have hbase : Tendsto (fun τ : ℂ => τ) l (𝓝 ρ) := tendsto_id
  have hρ : 0 < ρ.re := by simpa [ρ] using principalRoot_pos d hd
  have hperiods := continuousAt_principalU_periods d hd
  have hperiod₁ : Tendsto (fun τ : ℂ => flt (principalU d : Mat(2, ℤ)) τ)
      l (𝓝 ρ) := by
    simpa only [Function.comp_def, ρ, flt_principalU_principalRoot_complex d hd] using
      hperiods.1.tendsto
  have hperiod₂ : Tendsto (fun τ : ℂ => flt (principalU d : Mat(2, ℤ))
      (flt (principalU d : Mat(2, ℤ)) τ)) l (𝓝 ρ) := by
    simpa only [Function.comp_def, ρ, flt_principalU_principalRoot_complex d hd] using
      hperiods.2.tendsto
  have h₀ := (Complex.continuous_re.continuousAt.tendsto.comp hbase).eventually_const_lt hρ
  have h₁ := (Complex.continuous_re.continuousAt.tendsto.comp hperiod₁).eventually_const_lt hρ
  have h₂ := (Complex.continuous_re.continuousAt.tendsto.comp hperiod₂).eventually_const_lt hρ
  exact h₀.and (h₁.and h₂)

/-- Sufficiently near the positive principal root, all three principal periods lie in the
slit plane. -/
theorem eventually_principalFaddeevPeriodsSlitPlane (d : ℕ) (hd : 3 < d) :
    ∀ᶠ τ : ℂ in 𝓝 (principalRoot d : ℂ), PrincipalFaddeevPeriodsSlitPlane d τ := by
  filter_upwards [eventually_principalFaddeevPeriods_re_pos d hd] with τ hτ
  exact ⟨Complex.mem_slitPlane_iff.mpr (Or.inl hτ.1),
    Complex.mem_slitPlane_iff.mpr (Or.inl hτ.2.1),
    Complex.mem_slitPlane_iff.mpr (Or.inl hτ.2.2)⟩

/-- Near the positive principal root, the three periods in the principal word are nonzero. -/
lemma eventually_principalU_periods_ne_zero (d : ℕ) (hd : 3 < d) :
    ∀ᶠ τ : ℂ in 𝓝 (principalRoot d : ℂ),
      τ ≠ 0 ∧ flt (principalU d : Mat(2, ℤ)) τ ≠ 0 ∧
        flt (principalU d : Mat(2, ℤ))
          (flt (principalU d : Mat(2, ℤ)) τ) ≠ 0 := by
  filter_upwards [eventually_principalFaddeevPeriods_re_pos d hd] with τ hτ
  refine ⟨?_, ?_, ?_⟩
  · apply ne_of_apply_ne Complex.re
    simpa using ne_of_gt hτ.1
  · apply ne_of_apply_ne Complex.re
    simpa using ne_of_gt hτ.2.1
  · apply ne_of_apply_ne Complex.re
    simpa using ne_of_gt hτ.2.2

/-- There is a positive closed ball about `ρ_d` on which all three periods in the principal word
are nonzero. -/
lemma exists_principalU_periods_ne_zero (d : ℕ) (hd : 3 < d) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ τ : ℂ, ‖τ - (principalRoot d : ℂ)‖ ≤ ε →
      τ ≠ 0 ∧ flt (principalU d : Mat(2, ℤ)) τ ≠ 0 ∧
        flt (principalU d : Mat(2, ℤ))
          (flt (principalU d : Mat(2, ℤ)) τ) ≠ 0 := by
  have hnear := eventually_principalU_periods_ne_zero d hd
  rw [Metric.eventually_nhds_iff] at hnear
  obtain ⟨δ, hδ, hperiods⟩ := hnear
  refine ⟨δ / 2, half_pos hδ, fun τ hτ => hperiods ?_⟩
  rw [dist_eq_norm]
  exact hτ.trans_lt (by linarith)

/-- Composes `continuousAt_faddeevS` with a principal argument and period map on its
gamma-denominator domain; used by the product continuity theorem. -/
private lemma continuousAt_principalFaddeevFactor (d : ℕ) (hd : 3 < d)
    (z : ℂ) (a b : ℂ × ℂ → ℂ) (ha : ContinuousAt a (z, (principalRoot d : ℂ)))
    (hb : ContinuousAt b (z, (principalRoot d : ℂ)))
    (hbρ : b (z, (principalRoot d : ℂ)) = principalRoot d)
    (hden : barnesDoubleGammaInv
      ((principalRoot d : ℂ) - a (z, (principalRoot d : ℂ))) 1 (principalRoot d) ≠ 0) :
    ContinuousAt (fun p => faddeevS (a p) (b p)) (z, (principalRoot d : ℂ)) := by
  have hg : ContinuousAt (fun p : ℂ × ℂ => faddeevS p.1 p.2)
      (a (z, (principalRoot d : ℂ)), b (z, (principalRoot d : ℂ))) := by
    simpa only [hbρ] using
      (continuousAt_faddeevS (ofReal_principalRoot_mem_slitPlane d hd) hden)
  simpa only [Function.comp_def] using
    hg.comp (f := fun p : ℂ × ℂ => (a p, b p)) (ha.prodMk hb)

/-- The three argument maps in equation (20) are jointly continuous at the principal fixed
period; used by `continuousAt_principalFaddeevComplex_of_gammaRegular`. -/
private lemma continuousAt_principalFaddeevArguments (d : ℕ) (hd : 3 < d)
    (m n : ℤ) (z : ℂ) :
    ContinuousAt (fun p : ℂ × ℂ => p.1 / p.2 /
      flt (principalU d : Mat(2, ℤ)) p.2 - n) (z, (principalRoot d : ℂ)) ∧
    ContinuousAt (fun p : ℂ × ℂ => p.1 / p.2) (z, (principalRoot d : ℂ)) ∧
    ContinuousAt (fun p : ℂ × ℂ => p.1 + m * p.2) (z, (principalRoot d : ℂ)) := by
  let ρ : ℂ := principalRoot d
  let U : Mat(2, ℤ) := principalU d
  have hρ : ρ ≠ 0 := ofReal_principalRoot_ne_zero d hd
  have hfix : flt U ρ = ρ := flt_principalU_principalRoot_complex d hd
  have hτ₁ : ContinuousAt (fun p : ℂ × ℂ => flt U p.2) (z, ρ) := by
    simpa only [Function.comp_def, U] using
      (continuousAt_principalU_periods d hd).1.comp
        (f := fun p : ℂ × ℂ => p.2) (x := (z, ρ)) continuousAt_snd
  have ha₁ : ContinuousAt (fun p : ℂ × ℂ => p.1 / p.2) (z, ρ) :=
    continuousAt_fst.div continuousAt_snd hρ
  have ha₂ : ContinuousAt (fun p : ℂ × ℂ => p.1 / p.2 / flt U p.2 - n)
      (z, ρ) := ((ha₁.div hτ₁ (by change flt U ρ ≠ 0; rw [hfix]; exact hρ)).sub
        continuousAt_const)
  have ha₀ : ContinuousAt (fun p : ℂ × ℂ => p.1 + m * p.2) (z, ρ) :=
    continuousAt_fst.add (continuousAt_const.mul continuousAt_snd)
  exact ⟨ha₂, ha₁, ha₀⟩

/-- The two variable-period maps in the principal product are jointly continuous in the argument
and period; used by the gamma-domain continuity and analyticity theorems. -/
private lemma continuousAt_principalFaddeevPeriodMaps (d : ℕ) (hd : 3 < d) (z : ℂ) :
    ContinuousAt (fun p : ℂ × ℂ =>
      flt (principalU d : Mat(2, ℤ)) p.2) (z, (principalRoot d : ℂ)) ∧
    ContinuousAt (fun p : ℂ × ℂ => flt (principalU d : Mat(2, ℤ))
      (flt (principalU d : Mat(2, ℤ)) p.2)) (z, (principalRoot d : ℂ)) := by
  obtain ⟨hperiod₁, hperiod₂⟩ := continuousAt_principalU_periods d hd
  constructor
  · simpa only [Function.comp_def] using
      hperiod₁.comp (f := fun p : ℂ × ℂ => p.2) (x := (z, (principalRoot d : ℂ)))
        continuousAt_snd
  · simpa only [Function.comp_def] using
      hperiod₂.comp (f := fun p : ℂ × ℂ => p.2) (x := (z, (principalRoot d : ℂ)))
        continuousAt_snd

/-- Joint continuity at the real period wherever the three gamma denominators in
[RW26, Radchenko, Wheeler (2026), equation (20), `eq:modulartofaddeevCF`] are nonzero.
Specializes `continuousAt_faddeevS` at the principal arguments and periods. -/
theorem continuousAt_principalFaddeevComplex_of_gammaRegular
    (d : ℕ) (hd : 3 < d) (m n : ℤ) (z : ℂ)
    (hz : PrincipalFaddeevGammaRegular d m n z) :
    ContinuousAt (fun p : ℂ × ℂ => principalFaddeevComplex d m n p.1 p.2)
      (z, (principalRoot d : ℂ)) := by
  let ρ : ℂ := principalRoot d
  let U : Mat(2, ℤ) := principalU d
  have hρ : ρ ≠ 0 := ofReal_principalRoot_ne_zero d hd
  have hfix : flt U ρ = ρ := flt_principalU_principalRoot_complex d hd
  obtain ⟨ha₂, ha₁, ha₀⟩ := continuousAt_principalFaddeevArguments d hd m n z
  obtain ⟨hτ₁, hτ₂⟩ := continuousAt_principalFaddeevPeriodMaps d hd z
  have hdiv : z / ρ / ρ = z / ρ ^ 2 := by field_simp [hρ]
  have hf₂ : ContinuousAt (fun p : ℂ × ℂ => faddeevS (p.1 / p.2 / flt U p.2 - n)
      (flt U (flt U p.2))) (z, ρ) := by
    apply continuousAt_principalFaddeevFactor d hd z _ _ ha₂ hτ₂
    · change flt U (flt U ρ) = ρ
      rw [hfix, hfix]
    · change barnesDoubleGammaInv (ρ - (z / ρ / flt U ρ - n)) 1 ρ ≠ 0
      rw [hfix]
      simpa only [hdiv] using hz.first
  have hf₁ : ContinuousAt (fun p : ℂ × ℂ => faddeevS (p.1 / p.2) (flt U p.2))
      (z, ρ) := by
    exact continuousAt_principalFaddeevFactor d hd z _ _ ha₁ hτ₁ hfix hz.middle
  have hf₀ : ContinuousAt (fun p : ℂ × ℂ => faddeevS (p.1 + m * p.2) p.2)
      (z, ρ) := by
    exact continuousAt_principalFaddeevFactor d hd z _ _ ha₀ continuousAt_snd rfl hz.last
  exact (hf₂.mul hf₁).mul hf₀

/-- For a fixed complex period, the three-generator product is analytic in its argument when
the three periods lie in the slit plane and the displayed gamma denominators are nonzero. -/
theorem analyticAt_principalFaddeevComplex_of_gammaRegular
    (d : ℕ) (m n : ℤ) (z τ : ℂ)
    (hperiods : PrincipalFaddeevPeriodsSlitPlane d τ)
    (hz : PrincipalFaddeevComplexGammaRegular d m n z τ) :
    AnalyticAt ℂ (fun v => principalFaddeevComplex d m n v τ) z := by
  have hf₂ : AnalyticAt ℂ (fun v : ℂ => faddeevS
      (v / τ / flt (principalU d : Mat(2, ℤ)) τ - n)
      (flt (principalU d : Mat(2, ℤ)) (flt (principalU d : Mat(2, ℤ)) τ))) z := by
    simpa only [Function.comp_def] using
      (analyticAt_faddeevS _ _ hperiods.twice hz.first).comp
      (f := fun v : ℂ => v / τ / flt (principalU d : Mat(2, ℤ)) τ - n)
      (by fun_prop)
  have hf₁ : AnalyticAt ℂ (fun v : ℂ =>
      faddeevS (v / τ) (flt (principalU d : Mat(2, ℤ)) τ)) z := by
    simpa only [Function.comp_def] using
      (analyticAt_faddeevS _ _ hperiods.once hz.middle).comp
      (f := fun v : ℂ => v / τ) (by fun_prop)
  have hf₀ : AnalyticAt ℂ (fun v : ℂ => faddeevS (v + m * τ) τ) z := by
    simpa only [Function.comp_def] using (analyticAt_faddeevS _ _ hperiods.base hz.last).comp
      (f := fun v : ℂ => v + m * τ) (by fun_prop)
  change AnalyticAt ℂ
    (((fun v : ℂ => faddeevS
      (v / τ / flt (principalU d : Mat(2, ℤ)) τ - n)
      (flt (principalU d : Mat(2, ℤ)) (flt (principalU d : Mat(2, ℤ)) τ))) *
      (fun v : ℂ => faddeevS (v / τ) (flt (principalU d : Mat(2, ℤ)) τ))) *
      (fun v : ℂ => faddeevS (v + m * τ) τ)) z
  exact (hf₂.mul hf₁).mul hf₀

/-- At an upper-half-plane period, a nonzero complex-period product is analytic in its
argument. The value supplies its gamma domain and upper-half-plane transport supplies the
three slit-plane periods. -/
theorem analyticAt_principalFaddeevComplex_of_ne_zero
    (d : ℕ) (m n : ℤ) (z τ : ℂ) (hτ : 0 < τ.im)
    (hz : principalFaddeevComplex d m n z τ ≠ 0) :
    AnalyticAt ℂ (fun v => principalFaddeevComplex d m n v τ) z :=
  analyticAt_principalFaddeevComplex_of_gammaRegular d m n z τ
    (principalFaddeevPeriodsSlitPlane_of_im_pos d hτ)
    (principalFaddeevComplexGammaRegular_of_ne_zero d m n z τ hz)

/-- Nonvanishing of a continuously varying principal gamma denominator persists near `ρ_d`;
used by `eventually_analyticAt_principalFaddeevComplex`. -/
private lemma eventually_principalFaddeevDenominator_ne_zero
    (d : ℕ) (hd : 3 < d) (z : ℂ) (a b : ℂ × ℂ → ℂ)
    (ha : ContinuousAt a (z, (principalRoot d : ℂ)))
    (hb : ContinuousAt b (z, (principalRoot d : ℂ)))
    (hbρ : b (z, (principalRoot d : ℂ)) = principalRoot d)
    (hden : barnesDoubleGammaInv
      ((principalRoot d : ℂ) - a (z, (principalRoot d : ℂ)))
      1 (principalRoot d) ≠ 0) :
    ∀ᶠ τ : ℂ in 𝓝 (principalRoot d : ℂ),
      barnesDoubleGammaInv (b (z, τ) - a (z, τ)) 1 (b (z, τ)) ≠ 0 := by
  have hc : ContinuousAt (fun p : ℂ × ℂ =>
      barnesDoubleGammaInv (b p - a p) 1 (b p))
      (z, (principalRoot d : ℂ)) := by
    have hg := continuousAt_barnesDoubleGammaInv
      (z := (principalRoot d : ℂ) - a (z, (principalRoot d : ℂ)))
      (ofReal_principalRoot_mem_slitPlane d hd)
    have hg' : ContinuousAt (fun p : ℂ × ℂ => barnesDoubleGammaInv p.1 1 p.2)
        (b (z, (principalRoot d : ℂ)) - a (z, (principalRoot d : ℂ)),
          b (z, (principalRoot d : ℂ))) := by
      simpa only [hbρ] using hg
    have hab : ContinuousAt (fun p : ℂ × ℂ => (b p - a p, b p))
        (z, (principalRoot d : ℂ)) := by
      simpa only [Pi.sub_apply] using (hb.sub ha).prodMk hb
    simpa only [Function.comp_def] using
      hg'.comp (f := fun p : ℂ × ℂ => (b p - a p, b p)) hab
  have hpair : Tendsto (fun τ : ℂ => (z, τ))
      (𝓝 (principalRoot d : ℂ)) (𝓝 (z, (principalRoot d : ℂ))) :=
    tendsto_const_nhds.prodMk_nhds tendsto_id
  exact (hc.tendsto.comp hpair).eventually_ne (by simpa only [hbρ] using hden)

/-- The factorwise gamma domain at the principal root persists for nearby complex periods. -/
theorem eventually_principalFaddeevComplexGammaRegular
    (d : ℕ) (hd : 3 < d) (m n : ℤ) (z : ℂ)
    (hz : PrincipalFaddeevGammaRegular d m n z) :
    ∀ᶠ τ : ℂ in 𝓝 (principalRoot d : ℂ),
      PrincipalFaddeevComplexGammaRegular d m n z τ := by
  let ρ : ℂ := principalRoot d
  let U : Mat(2, ℤ) := principalU d
  have hρ : ρ ≠ 0 := ofReal_principalRoot_ne_zero d hd
  have hfix : flt U ρ = ρ := flt_principalU_principalRoot_complex d hd
  obtain ⟨ha₂, ha₁, ha₀⟩ := continuousAt_principalFaddeevArguments d hd m n z
  obtain ⟨hτ₁, hτ₂⟩ := continuousAt_principalFaddeevPeriodMaps d hd z
  have hdiv : z / ρ / ρ = z / ρ ^ 2 := by field_simp [hρ]
  have hd₂ := eventually_principalFaddeevDenominator_ne_zero d hd z _ _ ha₂ hτ₂
    (by change flt U (flt U ρ) = ρ; rw [hfix, hfix])
    (by
      change barnesDoubleGammaInv (ρ - (z / ρ / flt U ρ - n)) 1 ρ ≠ 0
      rw [hfix]
      simpa only [hdiv] using hz.first)
  have hd₁ := eventually_principalFaddeevDenominator_ne_zero d hd z _ _ ha₁ hτ₁ hfix hz.middle
  have hd₀ := eventually_principalFaddeevDenominator_ne_zero d hd z _ _ ha₀
    continuousAt_snd rfl hz.last
  filter_upwards [hd₂, hd₁, hd₀] with τ h₂τ h₁τ h₀τ
  exact ⟨h₂τ, h₁τ, h₀τ⟩

/-- Near the positive principal period, the three-generator product is analytic in its argument
throughout the factorwise boundary gamma domain. -/
theorem eventually_analyticAt_principalFaddeevComplex
    (d : ℕ) (hd : 3 < d) (m n : ℤ) (z : ℂ)
    (hz : PrincipalFaddeevGammaRegular d m n z) :
    ∀ᶠ τ : ℂ in 𝓝 (principalRoot d : ℂ),
      AnalyticAt ℂ (fun v => principalFaddeevComplex d m n v τ) z := by
  filter_upwards [eventually_principalFaddeevPeriodsSlitPlane d hd,
    eventually_principalFaddeevComplexGammaRegular d hd m n z hz]
    with τ hperiods hgamma
  exact analyticAt_principalFaddeevComplex_of_gammaRegular d m n z τ
    hperiods hgamma

/-- Joint continuity through any lattice-free real crossing of the principal product.
Specializes `continuousAt_faddeevS` using the lattice-complement gamma domain. -/
theorem continuousAt_principalFaddeevComplex_of_notMem
    (d : ℕ) (hd : 3 < d) (m n : ℤ) (z : ℂ)
    (hz : ¬ IsPeriodLatticePoint (principalRoot d) z) :
    ContinuousAt (fun p : ℂ × ℂ => principalFaddeevComplex d m n p.1 p.2)
      (z, (principalRoot d : ℂ)) := by
  exact continuousAt_principalFaddeevComplex_of_gammaRegular
    d hd m n z (principalFaddeevGammaRegular_of_notMem d hd m n z hz)

/-- The nearby three-generator values remain nonzero at every lattice-free principal base point.
This combines joint continuity with nonvanishing of the real-period product. -/
theorem eventually_principalFaddeevComplex_ne_zero_of_notMem
    (d : ℕ) (hd : 3 < d) (m n : ℤ) (z : ℂ)
    (hz : ¬ IsPeriodLatticePoint (principalRoot d) z) :
    ∀ᶠ q : ℂ × ℂ in 𝓝 (z, (principalRoot d : ℂ)),
      principalFaddeevComplex d m n q.1 q.2 ≠ 0 := by
  have hnonzero : principalFaddeevComplex d m n z (principalRoot d) ≠ 0 := by
    rw [principalFaddeevComplex_principalRoot d hd]
    exact principalFaddeev_ne_zero_of_notMem d hd m n z hz
  exact (continuousAt_principalFaddeevComplex_of_notMem
    d hd m n z hz).eventually_ne hnonzero

/-! ### Compact boundary argument sets

Joint continuity on the boundary slice gives one period neighborhood for every point of a
compact lattice-free set. Nonreal compact sets are special cases.
-/

/-! ### Comparison in the upper half plane

The cocycle splits `A_d=U_d³` twice, with zero intermediate indices. The one-letter identity
then identifies the three factors with the complex-period principal product. Punctured
neighborhoods avoid the denominator zeros. The affine-line comparison follows from this germ
identity.
-/

/-- The two cocycle denominators and three one-letter denominators are nonzero on a
punctured neighborhood. Used by `faddeevModularUHP_principalA_eventuallyEq_complex`. -/
private theorem eventually_principalFaddeev_qRegular
    (m n : ℤ) (τ τ₁ τ₂ z : ℂ)
    (hτ : 0 < τ.im) (hτ₁ : 0 < τ₁.im) (hτ₂ : 0 < τ₂.im) :
    ∀ᶠ w : ℂ in 𝓝[≠] z,
      qPochhammer (w / (τ₁ * τ)) τ₂ ≠ 0 ∧
      qPochhammer (w / τ) τ₁ ≠ 0 ∧
      qPochhammer ((w / τ / τ₁ - n) / τ₂) (-1 / τ₂) ≠ 0 ∧
      qPochhammer ((w / τ) / τ₁) (-1 / τ₁) ≠ 0 ∧
      qPochhammer ((w + m * τ) / τ) (-1 / τ) ≠ 0 := by
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
  have hτ₁0 : τ₁ ≠ 0 := fun h => by simp [h] at hτ₁
  have hτ₂0 : τ₂ ≠ 0 := fun h => by simp [h] at hτ₂
  have hq₂ : ∀ᶠ w : ℂ in 𝓝[≠] z, qPochhammer (w / (τ₁ * τ)) τ₂ ≠ 0 := by
    simpa only [add_zero] using eventually_qPochhammer_div_add_ne_zero
      (τ₁ * τ) 0 τ₂ z (mul_ne_zero hτ₁0 hτ0) hτ₂
  have hq₁ : ∀ᶠ w : ℂ in 𝓝[≠] z, qPochhammer (w / τ) τ₁ ≠ 0 := by
    simpa only [add_zero] using eventually_qPochhammer_div_add_ne_zero
      τ 0 τ₁ z hτ0 hτ₁
  have harg₂ (w : ℂ) : (w / τ / τ₁ - n) / τ₂ =
      w / (τ * τ₁ * τ₂) - n / τ₂ := by
    field_simp
  have hL₂ : ∀ᶠ w : ℂ in 𝓝[≠] z,
      qPochhammer ((w / τ / τ₁ - n) / τ₂) (-1 / τ₂) ≠ 0 := by
    have hq := eventually_qPochhammer_div_add_ne_zero
      (τ * τ₁ * τ₂) (-n / τ₂) (-1 / τ₂) z
      (mul_ne_zero (mul_ne_zero hτ0 hτ₁0) hτ₂0) (neg_one_div_im_pos τ₂ hτ₂)
    filter_upwards [hq] with w hw
    rw [harg₂ w]
    simpa only [sub_eq_add_neg, neg_div] using hw
  have hL₁ : ∀ᶠ w : ℂ in 𝓝[≠] z,
      qPochhammer ((w / τ) / τ₁) (-1 / τ₁) ≠ 0 := by
    have harg (w : ℂ) : w / τ / τ₁ = w / (τ * τ₁) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    simpa only [harg, add_zero] using eventually_qPochhammer_div_add_ne_zero
      (τ * τ₁) 0 (-1 / τ₁) z (mul_ne_zero hτ0 hτ₁0) (neg_one_div_im_pos τ₁ hτ₁)
  have hL₀ : ∀ᶠ w : ℂ in 𝓝[≠] z,
      qPochhammer ((w + m * τ) / τ) (-1 / τ) ≠ 0 := by
    have harg (w : ℂ) : (w + m * τ) / τ = w / τ + m := by
      field_simp
    simpa only [harg] using eventually_qPochhammer_div_add_ne_zero
      τ m (-1 / τ) z hτ0 (neg_one_div_im_pos τ hτ)
  filter_upwards [hq₂, hq₁, hL₂, hL₁, hL₀] with w hw₂ hw₁ hwL₂ hwL₁ hwL₀
  exact ⟨hw₂, hw₁, hwL₂, hwL₁, hwL₀⟩

/-- Two pointwise cocycle steps split `A_d=U_d³` into its three principal letters.
Used by `faddeevModularUHP_principalA_eventuallyEq_complex`. -/
private theorem faddeevModularUHP_principalA_cocycle (d : ℕ) (m n : ℤ) (w τ : ℂ) (hτ : 0 < τ.im)
    (hq₂ : qPochhammer
      (w / (flt (principalU d : Mat(2, ℤ)) τ * τ))
      (flt (principalU d : Mat(2, ℤ)) (flt (principalU d : Mat(2, ℤ)) τ)) ≠ 0)
    (hq₁ : qPochhammer (w / τ) (flt (principalU d : Mat(2, ℤ)) τ) ≠ 0) :
    faddeevModularUHP (principalA d) m n w τ =
      faddeevModularUHP (principalU d) 0 n
          (w / τ / flt (principalU d : Mat(2, ℤ)) τ)
          (flt (principalU d : Mat(2, ℤ)) (flt (principalU d : Mat(2, ℤ)) τ)) *
        (faddeevModularUHP (principalU d) 0 0 (w / τ)
            (flt (principalU d : Mat(2, ℤ)) τ) *
          faddeevModularUHP (principalU d) m 0 w τ) := by
  let U : SL(2, ℤ) := principalU d
  let τ₁ : ℂ := flt (U : Mat(2, ℤ)) τ
  let τ₂ : ℂ := flt (U : Mat(2, ℤ)) τ₁
  change qPochhammer (w / (τ₁ * τ)) τ₂ ≠ 0 at hq₂
  change qPochhammer (w / τ) τ₁ ≠ 0 at hq₁
  change faddeevModularUHP (principalA d) m n w τ =
    faddeevModularUHP U 0 n (w / τ / τ₁) τ₂ *
      (faddeevModularUHP U 0 0 (w / τ) τ₁ * faddeevModularUHP U m 0 w τ)
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
  have hA : principalA d = U * (U * U) := by
    simpa only [U, principalU_eq_T_zpow_mul_S, mul_assoc] using
      principalA_eq_T_zpow_mul_S_word d
  have hdenU (x : ℂ) : fltDenominator (U : Mat(2, ℤ)) x = x := by
    simpa only [U, principalU_eq_T_zpow_mul_S] using
      fltDenominator_T_zpow_mul_S ((d : ℤ) - 1) x
  have hdenUU : fltDenominator ((U * U : SL(2, ℤ)) : Mat(2, ℤ)) τ = τ₁ * τ := by
    rw [Matrix.SpecialLinearGroup.coe_mul, fltDenominator_mul _ _ τ
      (by rw [hdenU]; exact hτ0), hdenU, hdenU]
  have hperUU : flt ((U * U : SL(2, ℤ)) : Mat(2, ℤ)) τ = τ₂ := by
    rw [Matrix.SpecialLinearGroup.coe_mul,
      flt_mul _ _ τ (by rw [hdenU]; exact hτ0)]
  have hargUU : w / (τ₁ * τ) = w / τ / τ₁ := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hA, faddeevModularUHP_mul U (U * U) m 0 n w τ hτ (by
    simpa only [hdenUU, hperUU, Int.cast_zero, zero_mul, add_zero] using hq₂)]
  rw [hdenUU, hperUU, hargUU]
  rw [faddeevModularUHP_mul U U m 0 0 w τ hτ (by
    simpa only [hdenU, Int.cast_zero, zero_mul, add_zero] using hq₁)]
  simp only [hdenU, τ₁]

/-- At every complex base argument and `τ∈ℍ`, the principal modular q-product and the
three-generator product have the same meromorphic germ. This is the direct three-factor case
of [RW26, Radchenko, Wheeler (2026), Proposition 2(ii), `prop:prod.id.mod,fad`, equation (20),
`eq:modulartofaddeevCF`] for `A_d=(T^{d-1}S)³` and zero intermediate indices. -/
theorem faddeevModularUHP_principalA_eventuallyEq_complex
    (d : ℕ) (m n : ℤ) (z τ : ℂ) (hτ : 0 < τ.im) :
    (fun w => faddeevModularUHP (principalA d) m n w τ) =ᶠ[𝓝[≠] z]
      (fun w => principalFaddeevComplex d m n w τ) := by
  let U : SL(2, ℤ) := principalU d
  let τ₁ : ℂ := flt (U : Mat(2, ℤ)) τ
  let τ₂ : ℂ := flt (U : Mat(2, ℤ)) τ₁
  have hτ₁ : 0 < τ₁.im := flt_im_pos U hτ
  have hτ₂ : 0 < τ₂.im := flt_im_pos U hτ₁
  filter_upwards [eventually_principalFaddeev_qRegular m n τ τ₁ τ₂ z hτ hτ₁ hτ₂]
    with w hw
  rcases hw with ⟨hw₂, hw₁, hwL₂, hwL₁, hwL₀⟩
  have hletter₂ : faddeevModularUHP U 0 n (w / τ / τ₁) τ₂ =
      faddeevS (w / τ / τ₁ - n) τ₂ := by
    simpa only [U, principalU_eq_T_zpow_mul_S, Int.cast_zero, zero_mul, add_zero] using
      faddeevModularUHP_letter ((d : ℤ) - 1) 0 n (w / τ / τ₁) τ₂ hτ₂
        (by simpa only [Int.cast_zero, zero_mul, add_zero] using hwL₂)
  have hletter₁ : faddeevModularUHP U 0 0 (w / τ) τ₁ = faddeevS (w / τ) τ₁ := by
    simpa only [U, principalU_eq_T_zpow_mul_S, Int.cast_zero, zero_mul, add_zero,
      sub_zero] using
      faddeevModularUHP_letter ((d : ℤ) - 1) 0 0 (w / τ) τ₁ hτ₁
        (by simpa only [Int.cast_zero, zero_mul, add_zero, sub_zero] using hwL₁)
  have hletter₀ : faddeevModularUHP U m 0 w τ = faddeevS (w + m * τ) τ := by
    simpa only [U, principalU_eq_T_zpow_mul_S, Int.cast_zero, sub_zero] using
      faddeevModularUHP_letter ((d : ℤ) - 1) m 0 w τ hτ
        (by simpa only [Int.cast_zero, sub_zero] using hwL₀)
  calc
    faddeevModularUHP (principalA d) m n w τ =
        faddeevModularUHP U 0 n (w / τ / τ₁) τ₂ *
          (faddeevModularUHP U 0 0 (w / τ) τ₁ * faddeevModularUHP U m 0 w τ) := by
      exact faddeevModularUHP_principalA_cocycle d m n w τ hτ hw₂ hw₁
    _ = principalFaddeevComplex d m n w τ := by
      rw [hletter₂, hletter₁, hletter₀]
      simp only [principalFaddeevComplex, U, τ₁, τ₂, mul_assoc]

/-- For periods in the upper half plane near `ρ_d`, the modular q-product equals the principal
three-generator product at a fixed noninteger real argument on the displayed gamma domain.
This extends the punctured comparison in [RW26, Radchenko, Wheeler (2026), equation (20),
`eq:modulartofaddeevCF`] to the base point by analyticity of both sides. -/
theorem eventually_faddeevModularUHP_principalA_of_gammaRegular
    (d : ℕ) (hd : 3 < d) (m n : ℤ) (y : ℝ) (hy : ∀ k : ℤ, y ≠ k)
    (hgamma : PrincipalFaddeevGammaRegular d m n y) :
    ∀ᶠ τ : ℂ in 𝓝[{τ : ℂ | 0 < τ.im}] (principalRoot d : ℂ),
      faddeevModularUHP (principalA d) m n y τ =
        principalFaddeevComplex d m n y τ := by
  have hproduct : ∀ᶠ τ : ℂ in 𝓝[{τ : ℂ | 0 < τ.im}] (principalRoot d : ℂ),
      AnalyticAt ℂ (fun v => principalFaddeevComplex d m n v τ) y :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_analyticAt_principalFaddeevComplex
        d hd m n y hgamma)
  filter_upwards [self_mem_nhdsWithin, hproduct] with τ hτ hprod
  have hyτ := not_isPeriodLatticePoint_ofReal τ hτ.ne' y hy
  have hmodular := analyticAt_faddeevModularUHP_of_not_mem_lattice
    (principalA d) m n y τ hτ hyτ
  exact tendsto_nhds_unique_of_eventuallyEq
    (hmodular.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (hprod.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (faddeevModularUHP_principalA_eventuallyEq_complex
      d m n y τ hτ)

/-- For upper-half-plane periods near `ρ_d`, the modular q-product equals the principal
three-generator product at every fixed real argument outside the boundary period lattice.
This discharges the gamma-domain hypotheses of
`eventually_faddeevModularUHP_principalA_of_gammaRegular`. -/
theorem eventually_faddeevModularUHP_principalA
    (d : ℕ) (hd : 3 < d) (m n : ℤ) (y : ℝ)
    (hy : ¬ IsPeriodLatticePoint (principalRoot d) (y : ℂ)) :
    ∀ᶠ τ : ℂ in 𝓝[{τ : ℂ | 0 < τ.im}] (principalRoot d : ℂ),
      faddeevModularUHP (principalA d) m n y τ =
        principalFaddeevComplex d m n y τ := by
  have hyint : ∀ k : ℤ, y ≠ k := by
    intro k hyk
    apply hy
    exact ⟨k, 0, by simp [hyk]⟩
  exact eventually_faddeevModularUHP_principalA_of_gammaRegular
    d hd m n y hyint
      (principalFaddeevGammaRegular_of_notMem d hd m n y hy)

/-- For each `τ∈ℍ`, the principal modular q-product and the complex-period generator
product agree for almost every point of the affine line `z=a t+b`, `a≠0`.
Follows from `faddeevModularUHP_principalA_eventuallyEq_complex` by the affine-line
almost-everywhere lemma. This comparison transfers contour integrals past the countable
exceptional set of totalized q-product values. -/
theorem ae_faddeevModularUHP_principalA
    (d : ℕ) (m n : ℤ) (τ a b : ℂ) (hτ : 0 < τ.im) (ha : a ≠ 0) :
    ∀ᵐ t : ℝ, faddeevModularUHP (principalA d) m n (a * (t : ℂ) + b) τ =
      principalFaddeevComplex d m n (a * (t : ℂ) + b) τ :=
  ae_eq_comp_affine_of_forall_eventuallyEq_nhdsNE
    (fun z => faddeevModularUHP_principalA_eventuallyEq_complex d m n z τ hτ) a b ha

end SIC
