/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.DoubleSine.IntegralIdentities
import SICs.Source

/-!
# Identities of the Barnes Double Sine

Symmetry, reflection, positivity, and quasiperiodicity of the Barnes double sine.

This file proves the symmetry, reflection, positivity, and quasiperiodicity identities of
the Barnes double sine constructed in `SICs.SpecialFunctions.DoubleSine.RealIntegral`.
Kernel symmetries lift through the log-integral and exponential. The period laws follow by
integrating the kernel-difference formula and using the scalar evaluation proved in
`SICs.SpecialFunctions.DoubleSine.IntegralIdentities`; symmetry supplies the second period from
the first. These are the algebraic identities consumed by the Shintani--Faddeev formulas.

The double sine here follows the Kurokawa--Koyama convention. The convention of
[84, Ponsot (2003)], used by the numerical reference implementation [42, Flammia (2024)], is its
reciprocal. [42] calls that reciprocal convention Shintani's, where [AFK25] and [72] give that
name to the Kurokawa--Koyama convention used here. The header of
`SICs.SpecialFunctions.DoubleSine.RealIntegral` explains this conflict and the choice to name
the reciprocal convention after Ponsot.

## References

- [77, Kurokawa, Koyama (2003), Theorem 2.1], whose part (a) is the period shift proved here, for
  the multiple sine function of equation (2.2)
- [72, Kopp (2024), Proposition 4.25, `prop:quasiperiodicity`], the same identity for the double
  sine
- [AFK25, Appendix D, equations (D.5), `eq:doubleSineQuasiPeriodicity1`, and (D.6),
  `eq:doubleSineQuasiPeriodicity2`], the two period shifts in the `ω₂ = 1` shorthand
-/

noncomputable section

open Real MeasureTheory Set Asymptotics Filter

namespace SIC

/-! ### Kernel symmetries -/

/-- The double sine kernel is symmetric in `ω₁` and `ω₂`. -/
lemma doubleSineKernel_comm (z ω₁ ω₂ t : ℝ) :
    doubleSineKernel z ω₁ ω₂ t = doubleSineKernel z ω₂ ω₁ t := by
  unfold doubleSineKernel; ring_nf

/-- The double sine kernel negates under `z ↦ ω₁ + ω₂ − z`. -/
lemma doubleSineKernel_reflect (z ω₁ ω₂ t : ℝ) :
    doubleSineKernel (ω₁ + ω₂ - z) ω₁ ω₂ t = -doubleSineKernel z ω₁ ω₂ t := by
  unfold doubleSineKernel
  rw [show ω₁ + ω₂ - 2 * (ω₁ + ω₂ - z) = -(ω₁ + ω₂ - 2 * z) from by ring,
      show -(ω₁ + ω₂ - 2 * z) * t = -((ω₁ + ω₂ - 2 * z) * t) from by ring, sinh_neg]
  ring

/-! ### Log-integral symmetries -/

/-- The log-integral is symmetric in `ω₁` and `ω₂`. -/
lemma doubleSineLogIntegral_comm (z ω₁ ω₂ : ℝ) :
    doubleSineLogIntegral z ω₁ ω₂ = doubleSineLogIntegral z ω₂ ω₁ := by
  unfold doubleSineLogIntegral; congr 1; ext t; exact doubleSineKernel_comm z ω₁ ω₂ t

/-- The log-integral negates under `z ↦ ω₁ + ω₂ − z`. -/
lemma doubleSineLogIntegral_reflect (z ω₁ ω₂ : ℝ) :
    doubleSineLogIntegral (ω₁ + ω₂ - z) ω₁ ω₂ = -doubleSineLogIntegral z ω₁ ω₂ := by
  unfold doubleSineLogIntegral; simp_rw [doubleSineKernel_reflect]; rw [integral_neg]

/-! ### Proved structural identities

Kernel symmetry and negation lift immediately through the integral and exponential to symmetry
and reflection of the double sine, which is positive as an exponential. -/

/-- The double sine is symmetric in the periods: `S₂(z; ω₁, ω₂) = S₂(z; ω₂, ω₁)`. -/
theorem doubleSine_comm (z ω₁ ω₂ : ℝ) :
    doubleSine z ω₁ ω₂ = doubleSine z ω₂ ω₁ := by
  unfold doubleSine; rw [doubleSineLogIntegral_comm]

/-- **Reflection identity.** `S₂(ω₁ + ω₂ − z) · S₂(z) = 1`.

Immediate from the definition of the multiple sine as a ratio of multiple gamma values,
`S_r(z, ω) = Γ_r(z, ω)⁻¹ Γ_r(|ω| - z, ω)^((-1)^r)`, in [77, Kurokawa, Koyama (2003), eq. (2.2)]:
at `r = 2` that definition is visibly inverted by `z ↦ |ω| - z`. The proof here is instead a
direct consequence of the kernel negation, the two log-integrals summing to zero. -/
theorem doubleSine_mul_reflect (z ω₁ ω₂ : ℝ) :
    doubleSine (ω₁ + ω₂ - z) ω₁ ω₂ * doubleSine z ω₁ ω₂ = 1 := by
  unfold doubleSine
  rw [doubleSineLogIntegral_reflect, ← exp_add]
  simp; ring

/-- The double sine is strictly positive everywhere. This is unconditional: `exp` is positive
regardless of whether the integral converges. -/
theorem doubleSine_pos (z ω₁ ω₂ : ℝ) : 0 < doubleSine z ω₁ ω₂ :=
  exp_pos _

/-- The double sine is nonzero everywhere. -/
theorem doubleSine_ne_zero (z ω₁ ω₂ : ℝ) : doubleSine z ω₁ ω₂ ≠ 0 :=
  ne_of_gt (doubleSine_pos z ω₁ ω₂)

/-! ### Quasiperiodicity

The kernel-difference identity is integrated and evaluated to obtain shifts by either period.
Symmetry supplies the second shift law. -/

/-- **Quasiperiodicity in the first period (Kurokawa–Koyama convention).**

$$S_2(z + \omega_1; \omega_1, \omega_2)
  = \frac{S_2(z; \omega_1, \omega_2)}{2\sin(\pi z / \omega_2)}.$$

This is [77, Kurokawa, Koyama (2003), Theorem 2.1(a), equation (2.4)] at `r = 2` and `i = 1`,
where the general shift law `S_r(z + ω_i) = S_r(z) · S_{r−1}(z, ω(i))⁻¹` drops to the single sine
`S₁(z, ω₂) = 2 sin(πz/ω₂)`. The `ω₂ = 1` specialization is `doubleSine'_quasiperiod_tau`, which
carries the [AFK25] citation.

The proof reduces to `integral_inv_sq_sub_cosh_div_sinh` via:
1. Splitting the log-integral difference using `integral_sub` and integrability.
2. Replacing the kernel difference with `doubleSineKernel_shift_sub`.
3. A change of variables `s = ω₂ t` via `integral_comp_mul_left_Ioi`.

The hypotheses restrict to `0 < z < ω₂`, so both `z` and `z + ω₁` lie in the fundamental
chamber `(0, ω₁ + ω₂)`.

Note on conventions: in Ponsot's convention the period shift *multiplies* by `2 sin(πz/ω₂)`.
Since S₂^Ponsot = 1/S₂, the Kurokawa–Koyama convention used here *divides* by `2 sin(πz/ω₂)`,
as stated. See the header of `SICs.SpecialFunctions.DoubleSine.RealIntegral`. -/
@[source "77, Theorem 2.1(a), p. 843 (r = 2, i = 1, 0 < z < ω₂)"]
theorem doubleSine_quasiperiod_fst (z ω₁ ω₂ : ℝ)
    (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂) (hz : 0 < z) (hzu : z < ω₂) :
    doubleSine (z + ω₁) ω₁ ω₂ = doubleSine z ω₁ ω₂ / (2 * sin (π * z / ω₂)) := by
  -- Positivity of 2 sin(πz/ω₂): since 0 < z/ω₂ < 1, we have 0 < πz/ω₂ < π
  have hsin : 0 < sin (π * z / ω₂) :=
    sin_pos_of_mem_Ioo ⟨by positivity, by rw [div_lt_iff₀ hω₂]; nlinarith [pi_pos]⟩
  have h2sin : (0 : ℝ) < 2 * sin (π * z / ω₂) := by positivity
  -- Reduce to log-integral shift identity
  suffices hlog : doubleSineLogIntegral (z + ω₁) ω₁ ω₂ - doubleSineLogIntegral z ω₁ ω₂ =
      2 * Real.log (2 * sin (π * z / ω₂)) by
    unfold doubleSine
    rw [show -doubleSineLogIntegral (z + ω₁) ω₁ ω₂ / 2 =
        -doubleSineLogIntegral z ω₁ ω₂ / 2 - Real.log (2 * sin (π * z / ω₂)) from by linarith]
    rw [exp_sub, exp_log h2sin]
  -- Integrability of both kernels in the fundamental chamber
  have hint1 : IntegrableOn (doubleSineKernel (z + ω₁) ω₁ ω₂) (Ioi 0) :=
    doubleSineKernel_integrableOn_Ioi _ _ _ hω₁ hω₂ (by linarith) (by linarith)
  have hint2 : IntegrableOn (doubleSineKernel z ω₁ ω₂) (Ioi 0) :=
    doubleSineKernel_integrableOn_Ioi _ _ _ hω₁ hω₂ hz (by linarith)
  -- Log-integral difference = integral of kernel difference
  unfold doubleSineLogIntegral
  rw [← integral_sub hint1 hint2]
  -- Replace kernel difference with simplified form from doubleSineKernel_shift_sub
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => by
    simp only [mem_Ioi] at ht
    exact doubleSineKernel_shift_sub z ω₁ ω₂ t hω₁ hω₂ ht)]
  -- Set up the change of variables s = ω₂ t
  set α := 1 - 2 * z / ω₂ with hα_def
  have hα : |α| < 1 := by
    rw [abs_lt]; constructor
    · have : 2 * z / ω₂ < 2 := by rw [div_lt_iff₀ hω₂]; linarith
      linarith
    · linarith [div_pos (show (0:ℝ) < 2 * z by linarith) hω₂]
  set h : ℝ → ℝ := fun s => 1 / s ^ 2 - cosh (α * s) / (s * sinh s) with hh_def
  -- Pointwise identity: kernel difference = 2ω₂ · h(ω₂t) for t > 0
  have hpw : ∀ t ∈ Ioi (0 : ℝ),
      (2 / (ω₂ * t) - 2 * cosh ((ω₂ - 2 * z) * t) / sinh (ω₂ * t)) / t =
      2 * ω₂ * h (ω₂ * t) := by
    intro t ht; simp only [mem_Ioi, h] at ht ⊢
    have hωne : ω₂ ≠ 0 := ne_of_gt hω₂
    have hωt : ω₂ * t ≠ 0 := ne_of_gt (mul_pos hω₂ ht)
    have hst : sinh (ω₂ * t) ≠ 0 := ne_of_gt (sinh_pos_iff.mpr (mul_pos hω₂ ht))
    have ht0 : t ≠ 0 := ne_of_gt ht
    rw [show (ω₂ - 2 * z) * t = α * (ω₂ * t) from by
      simp only [α]; field_simp]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpw]
  -- Factor out constant: ∫ (2ω₂) · h(ω₂t) dt = (2ω₂) · ∫ h(ω₂t) dt
  rw [integral_const_mul]
  -- Change of variables: ∫ h(ω₂t) dt = ω₂⁻¹ · ∫ h(s) ds
  have hcov := integral_comp_mul_left_Ioi h 0 hω₂
  rw [mul_zero] at hcov
  rw [hcov, smul_eq_mul]
  -- Simplify: (2ω₂) · (ω₂⁻¹ · ∫ h) = 2 · ∫ h
  rw [show 2 * ω₂ * (ω₂⁻¹ * ∫ s in Ioi (0 : ℝ), h s) =
      2 * ∫ s in Ioi (0 : ℝ), h s from by
    rw [mul_assoc 2 ω₂, ← mul_assoc ω₂ ω₂⁻¹, mul_inv_cancel₀ (ne_of_gt hω₂), one_mul]]
  -- Apply the integral identity
  rw [show h = fun s => 1 / s ^ 2 - cosh (α * s) / (s * sinh s) from rfl,
      integral_inv_sq_sub_cosh_div_sinh α hα]
  -- Trigonometric identity: cos(πα/2) = sin(πz/ω₂)
  congr 1; congr 1; congr 1
  rw [show π * α / 2 = π / 2 - π * z / ω₂ from by
    simp only [α]; field_simp]
  exact Real.cos_pi_div_two_sub _

/-- **Quasiperiodicity in the second period (Kurokawa–Koyama convention).**

$$S_2(z + \omega_2; \omega_1, \omega_2)
  = \frac{S_2(z; \omega_1, \omega_2)}{2\sin(\pi z / \omega_1)}.$$

The `i = 2` case of the shift law cited at `doubleSine_quasiperiod_fst`, obtained from it here by
`doubleSine_comm`. -/
theorem doubleSine_quasiperiod_snd (z ω₁ ω₂ : ℝ)
    (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂) (hz : 0 < z) (hzu : z < ω₁) :
    doubleSine (z + ω₂) ω₁ ω₂ = doubleSine z ω₁ ω₂ / (2 * sin (π * z / ω₁)) := by
  rw [doubleSine_comm (z + ω₂), doubleSine_quasiperiod_fst z ω₂ ω₁ hω₂ hω₁ hz hzu,
      doubleSine_comm z]

/-! ### Specialized shorthand for ω₂ = 1

The principal-form ghost overlap formula uses `S₂(z; ρ_d, 1)` exclusively. The following
identities specialize the general period laws using the abbreviation `doubleSine'`. -/

/-- Two-argument quasiperiodicity: `S₂(z + 1, τ) = S₂(z, τ) / (2 sin(πz/τ))`.

This is [AFK25, equation (D.5), `eq:doubleSineQuasiPeriodicity1`]. -/
lemma doubleSine'_quasiperiod_one (z τ : ℝ) (hτ : 0 < τ) (hz : 0 < z) (hzu : z < τ) :
    doubleSine' (z + 1) τ = doubleSine' z τ / (2 * sin (π * z / τ)) :=
  doubleSine_quasiperiod_snd z τ 1 hτ one_pos hz hzu

/-- Two-argument quasiperiodicity: `S₂(z + τ, τ) = S₂(z, τ) / (2 sin(πz))`.

This is [AFK25, equation (D.6), `eq:doubleSineQuasiPeriodicity2`]. -/
lemma doubleSine'_quasiperiod_tau (z τ : ℝ) (hτ : 0 < τ) (hz : 0 < z) (hzu : z < 1) :
    doubleSine' (z + τ) τ = doubleSine' z τ / (2 * sin (π * z)) := by
  have := doubleSine_quasiperiod_fst z τ 1 hτ one_pos hz hzu
  simp only [div_one] at this
  exact this

end SIC

end
