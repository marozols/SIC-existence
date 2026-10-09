/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.NumberTheory.ModularForms.Discriminant
import SICs.Cocycle.Conjugation
import SICs.Cocycle.FixedPointCharacter

/-!
# Boundary values of the eta quotient at a real fixed point

The quotient `η(M·τ)/η(τ)` tends to `μ_M √(j_M(α))` as `τ → α` from the upper half plane, at an
irrational fixed point `α` of `M` with `j_M(α) > 0`; so the period-product quotient at an integral
characteristic `r` with `r₁ > 0` tends to the real cocycle value `ש^r_M(α) = μ_M √(j_M(α))`.

This module supplies the boundary value that [RW26b, Radchenko, Wheeler (2026b), Appendix A,
proof of Proposition 3] uses for the zero orbit: there `Φ_{γ,0,0}(0; τ)` is regularized on the
upper half plane by the eta transformation law and continued to the real fixed point, giving
`μ_γ^{-1} √ε`. In the convention of [72, Kopp (2024), Definition 2.2] the regularized zero class
is the integral characteristic `r = (0, 1)` (the source's `r₂ = 1`), whose period product
`ϖ_{(0,1)}(τ) = ∏_{k ≥ 1}(1 - e(kτ)) = e(-τ/24)η(τ)` has no vanishing factor; its quotient is
[72, Kopp (2024), the subsection on half-integral characteristics, p. 38, `sec:half`]. The
consumer is the
zero-class conductor relation of `SICs.Cocycle.ConductorZeroClass`.

## The argument

*The eta quotient along the Hirzebruch--Jung word.* For `M` with `M₁₀ ≥ 0` and `j_M(α) > 0`, peel
the word `M = T^b S M'` (`hjStep`). Mathlib's transformation laws `η(τ + 1) = e(1/24)η(τ)` and
`η(-1/τ) = (√i)⁻¹ √τ η(τ)` (`eta_comp_eq_csqrt_I_inv`) give
`η(M·τ)/η(τ) = e((b - 3)/24) √(M'·τ) · η(M'·τ)/η(τ)`, and `j_M(τ) = (M'·τ) j_{M'}(τ)`. Along
the walk every visited real point `M'·α` and every Jacobi denominator `j_{M'}(α)` is positive
(`WordSigmaSVisits.period_pos`), so the principal square root is continuous there and
`√(M'·α) √(j_{M'}(α)) = √(j_M(α))`. Induction along the word gives the limit
`e(W(M)/24) √(j_M(α))`, where `W` is the word sum `wordRademacher`; at a fixed point the trace is
positive and `W(M) = Ψ(M)` (`wordRademacher_eq_rademacherInvariant`), so the constant is the eta
multiplier `μ_M = e^{πiΨ(M)/12}`. For `M₁₀ < 0` apply this to `M⁻¹` along `M·τ_k → α`, with
`μ_{M⁻¹} = μ_M⁻¹` and `j_{M⁻¹}(α) = j_M(α)⁻¹`.

*Integral characteristics.* For `r ∈ ℤ²` with `r₁ = n > 0`,
`ϖ_r(τ) = ∏_{k ≥ n}(1 - e(kτ)) = e(-τ/24) η(τ) / ∏_{1 ≤ k < n}(1 - e(kτ))`. The quotient at `M·τ_k`
and `τ_k` is `e((τ_k - M·τ_k)/24)` times the eta quotient times a finite product tending to `1`
(both points tend to `α`, and `1 - e(kα) ≠ 0` since `α` is irrational). The limit
`μ_M √(j_M(α))` is the total cocycle at `r` (`sfModularCocycleRealTotal_integral_of_flt_eq_self`,
the case `r₁ > 0`).
-/

noncomputable section

open Filter
open scoped MatrixGroups

namespace SIC

/-! ### The eta quotient

`η(M·τ)/η(τ) → μ_M √(j_M(α))` along any approach to a real fixed point with positive Jacobi
denominator. -/

/-- The eta product obeys `η(z + b) = exp(πib/12)η(z)` for `b ∈ ℤ`; the translation
letter in `tendsto_eta_word` [72, Kopp (2024), equation (2.7), `eq:etatrans`]. -/
private lemma eta_add_intCast (z : ℂ) (b : ℤ) :
    ModularForm.eta (z + b) =
      Complex.exp (Real.pi * Complex.I / 12 * (b : ℂ)) * ModularForm.eta z := by
  have hq : Function.Periodic.qParam 24 (z + b) =
      Complex.exp (Real.pi * Complex.I / 12 * (b : ℂ)) * Function.Periodic.qParam 24 z := by
    simp only [Function.Periodic.qParam]
    calc
      _ = Complex.exp (Real.pi * Complex.I / 12 * (b : ℂ) +
          2 * Real.pi * Complex.I * z / 24) := by
            congr 1
            norm_num
            ring
      _ = _ := by rw [Complex.exp_add]; simp only [Complex.ofReal_ofNat]
  unfold ModularForm.eta
  rw [hq, mul_assoc]
  congr 1
  congr 1
  apply tprod_congr
  intro n
  congr 1
  rw [ModularForm.eta_q_eq_cexp, ModularForm.eta_q_eq_cexp]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (n + 1) * (z + (b : ℂ)) =
    2 * (Real.pi : ℂ) * Complex.I * (n + 1) * z +
      ((b * (n + 1) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The inversion constant in Mathlib's eta law is `exp(-πi/4)`, the `-3` term of the
word exponent used by `eta_hjStep`. -/
private lemma sqrt_I_inv_eq_exp :
    (Complex.sqrt Complex.I)⁻¹ =
      Complex.exp (Real.pi * Complex.I / 12 * (-3 : ℂ)) := by
  rw [sqrt_eq_exp Complex.I_ne_zero, Complex.log_I, ← Complex.exp_neg]
  congr 1
  ring

/-- The complex Möbius action satisfies `M·τ = -1/(M'·τ) + b` for the `hjStep`
decomposition on the upper half plane; used by `eta_hjStep`. -/
private lemma flt_hjStep_complex (M : SL(2, ℤ)) (τ : ℂ) (hτ : 0 < τ.im) :
    flt (M : Mat(2, ℤ)) τ =
      -1 / flt ((hjStep M).2 : Mat(2, ℤ)) τ + (hjStep M).1 := by
  have hden : fltDenominator ((hjStep M).2 : Mat(2, ℤ)) τ ≠ 0 :=
    fltDenominator_ne_zero_of_im_ne_zero (hjStep M).2 hτ.ne'
  have hSMden : fltDenominator
      ((ModularGroup.S : Mat(2, ℤ)) * ((hjStep M).2 : Mat(2, ℤ))) τ ≠ 0 := by
    change fltDenominator
      ((ModularGroup.S * (hjStep M).2 : SL(2, ℤ)) : Mat(2, ℤ)) τ ≠ 0
    exact fltDenominator_ne_zero_of_im_ne_zero _ hτ.ne'
  rw [hjStep_reconstruct_coe M, flt_mul _ _ τ hSMden,
    flt_T_zpow, flt_mul _ _ τ hden, flt_S]

/-- One Hirzebruch–Jung letter of the eta transformation law [72, Kopp (2024),
equation (2.7), `eq:etatrans`], used by `tendsto_eta_word`. -/
private lemma eta_hjStep (M : SL(2, ℤ)) (τ : ℂ) (hτ : 0 < τ.im) :
    ModularForm.eta (flt (M : Mat(2, ℤ)) τ) =
      Complex.exp (Real.pi * Complex.I / 12 * (((hjStep M).1 - 3 : ℤ) : ℂ)) *
        Complex.sqrt (flt ((hjStep M).2 : Mat(2, ℤ)) τ) *
          ModularForm.eta (flt ((hjStep M).2 : Mat(2, ℤ)) τ) := by
  rw [flt_hjStep_complex M τ hτ, eta_add_intCast]
  have hs := ModularForm.eta_comp_eq_csqrt_I_inv
    (flt_im_pos (hjStep M).2 hτ)
  simp only [Function.comp_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at hs
  have hphase : Complex.exp (Real.pi * Complex.I / 12 * ((hjStep M).1 : ℂ)) *
      Complex.exp (Real.pi * Complex.I / 12 * (-3 : ℂ)) =
      Complex.exp (Real.pi * Complex.I / 12 * (((hjStep M).1 - 3 : ℤ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hs, sqrt_I_inv_eq_exp, ← mul_assoc, hphase]
  ring

/-- At the terminal translation matrix, the eta quotient is the translation multiplier; the
base case of `tendsto_eta_word_aux`. -/
private lemma tendsto_eta_word_terminal {ι : Type*} {l : Filter ι} (tauSeq : ι → ℂ)
    {α : ℝ} {M : SL(2, ℤ)} (h0 : 0 ≤ M 1 0) (hz : M 1 0 = 0)
    (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) α)
    (him : ∀ᶠ k in l, 0 < (tauSeq k).im) :
    Tendsto (fun k => ModularForm.eta (flt (M : Mat(2, ℤ)) (tauSeq k)) /
      ModularForm.eta (tauSeq k)) l
      (nhds (Complex.exp (Real.pi * Complex.I / 12 * (wordRademacher M h0 : ℂ)) *
        ((Real.sqrt (fltDenominator (M : Mat(2, ℤ)) α) : ℝ) : ℂ))) := by
  have hM : M = ModularGroup.T ^ (M 0 1) :=
    eq_T_zpow_of_lowerLeft_eq_zero M hz (topLeft_pos_of_lowerLeft_eq_zero hjac hz)
  rw [fltDenominator_eq_one_of_lowerLeft_eq_zero hz hjac,
    wordRademacher_of_lowerLeft_eq_zero M h0 hz]
  simp only [Real.sqrt_one, Complex.ofReal_one, mul_one]
  apply tendsto_const_nhds.congr'
  filter_upwards [him] with k hk
  have hF : flt (M : Mat(2, ℤ)) (tauSeq k) = tauSeq k + (M 0 1 : ℂ) := by
    conv_lhs => rw [hM]
    exact flt_T_zpow (M 0 1) (tauSeq k)
  rw [hF, eta_add_intCast]
  exact (mul_div_cancel_right₀ _ (ModularForm.eta_ne_zero hk)).symm

/-- The principal complex square root of a transported modulus tends to the positive real
square root of its limit; used in the eta word induction. -/
private lemma tendsto_sqrt_flt_of_pos {ι : Type*} {l : Filter ι} (tauSeq : ι → ℂ)
    {α : ℝ} {N : SL(2, ℤ)}
    (hperiod : 0 < flt (N : Mat(2, ℤ)) α)
    (hjacN : 0 < fltDenominator (N : Mat(2, ℤ)) α)
    (htauT : Tendsto tauSeq l (nhds (α : ℂ))) :
    Tendsto (fun k => Complex.sqrt (flt (N : Mat(2, ℤ)) (tauSeq k))) l
      (nhds ((Real.sqrt (flt (N : Mat(2, ℤ)) α) : ℝ) : ℂ)) := by
  have hdenNC : fltDenominator (N : Mat(2, ℤ)) (α : ℂ) ≠ 0 := by
    rw [← ofReal_fltDenominator]
    exact_mod_cast hjacN.ne'
  have htauN : Tendsto (fun k => flt (N : Mat(2, ℤ)) (tauSeq k)) l
      (nhds ((flt (N : Mat(2, ℤ)) α : ℝ) : ℂ)) := by
    rw [ofReal_flt]
    exact flt_tendsto (N : Mat(2, ℤ)) htauT hdenNC
  have hcont : ContinuousAt Complex.sqrt ((flt (N : Mat(2, ℤ)) α : ℝ) : ℂ) :=
    Complex.continuousAt_sqrt (Or.inl (by
      rw [Complex.ofReal_re]
      exact hperiod.le))
  have h := hcont.tendsto.comp htauN
  have hsqrt_eq : Complex.sqrt (((flt (N : Mat(2, ℤ)) α : ℝ) : ℂ)) =
      ((Real.sqrt (flt (N : Mat(2, ℤ)) α) : ℝ) : ℂ) := by
    rw [Complex.sqrt_of_nonneg (by exact_mod_cast hperiod.le)]
    simp only [Complex.ofReal_re]
  simpa only [Function.comp_def, hsqrt_eq] using h

/-- One eta word letter multiplies the accumulated phase and square root by exactly the
constant prescribed by `wordRademacher` and `fltDenominator_hjStep`. -/
private lemma eta_word_step_constant {M N : SL(2, ℤ)} {α : ℝ}
    (hα : Irrational α) (h0 : 0 ≤ M 1 0) (hz : M 1 0 ≠ 0)
    (hN : (hjStep M).2 = N) (h0N : 0 ≤ N 1 0)
    (hperiod : 0 < flt (N : Mat(2, ℤ)) α) :
    (Complex.exp (Real.pi * Complex.I / 12 * (((hjStep M).1 - 3 : ℤ) : ℂ)) *
      ((Real.sqrt (flt (N : Mat(2, ℤ)) α) : ℝ) : ℂ)) *
        (Complex.exp (Real.pi * Complex.I / 12 * (wordRademacher N h0N : ℂ)) *
          ((Real.sqrt (fltDenominator (N : Mat(2, ℤ)) α) : ℝ) : ℂ)) =
    Complex.exp (Real.pi * Complex.I / 12 * (wordRademacher M h0 : ℂ)) *
      ((Real.sqrt (fltDenominator (M : Mat(2, ℤ)) α) : ℝ) : ℂ) := by
  have hphase :
      Complex.exp (Real.pi * Complex.I / 12 * (((hjStep M).1 - 3 : ℤ) : ℂ)) *
        Complex.exp (Real.pi * Complex.I / 12 * (wordRademacher N h0N : ℂ)) =
      Complex.exp (Real.pi * Complex.I / 12 * (wordRademacher M h0 : ℂ)) := by
    rw [wordRademacher_step h0 hz hN h0N, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hsqrtprod :
      ((Real.sqrt (flt (N : Mat(2, ℤ)) α) : ℝ) : ℂ) *
          ((Real.sqrt (fltDenominator (N : Mat(2, ℤ)) α) : ℝ) : ℂ) =
      ((Real.sqrt (fltDenominator (M : Mat(2, ℤ)) α) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul hperiod.le,
      fltDenominator_hjStep M α hα, hN]
  calc
    _ = (Complex.exp (Real.pi * Complex.I / 12 * (((hjStep M).1 - 3 : ℤ) : ℂ)) *
          Complex.exp (Real.pi * Complex.I / 12 * (wordRademacher N h0N : ℂ))) *
          (((Real.sqrt (flt (N : Mat(2, ℤ)) α) : ℝ) : ℂ) *
            ((Real.sqrt (fltDenominator (N : Mat(2, ℤ)) α) : ℝ) : ℂ)) := by ring
    _ = _ := by rw [hphase, hsqrtprod]

/-- One `hjStep` letter transports an eta quotient limit through its translation and
inversion factors. The word constant is identified separately by `eta_word_step_constant`. -/
private theorem tendsto_eta_word_step {ι : Type*} {l : Filter ι} (tauSeq : ι → ℂ)
    {α : ℝ} {M N : SL(2, ℤ)} (hN : (hjStep M).2 = N)
    (hperiod : 0 < flt (N : Mat(2, ℤ)) α)
    (hjacN : 0 < fltDenominator (N : Mat(2, ℤ)) α)
    (htauT : Tendsto tauSeq l (nhds (α : ℂ))) (him : ∀ᶠ k in l, 0 < (tauSeq k).im)
    {L : ℂ} (hlimN : Tendsto (fun k => ModularForm.eta (flt (N : Mat(2, ℤ)) (tauSeq k)) /
      ModularForm.eta (tauSeq k)) l (nhds L)) :
    Tendsto (fun k => ModularForm.eta (flt (M : Mat(2, ℤ)) (tauSeq k)) /
      ModularForm.eta (tauSeq k)) l
      (nhds ((Complex.exp (Real.pi * Complex.I / 12 * (((hjStep M).1 - 3 : ℤ) : ℂ)) *
        ((Real.sqrt (flt (N : Mat(2, ℤ)) α) : ℝ) : ℂ)) * L)) := by
  have hsqrt := tendsto_sqrt_flt_of_pos tauSeq hperiod hjacN htauT
  have hlimit : Tendsto (fun k =>
      (Complex.exp (Real.pi * Complex.I / 12 * (((hjStep M).1 - 3 : ℤ) : ℂ)) *
        Complex.sqrt (flt (N : Mat(2, ℤ)) (tauSeq k))) *
        (ModularForm.eta (flt (N : Mat(2, ℤ)) (tauSeq k)) /
          ModularForm.eta (tauSeq k))) l
      (nhds ((Complex.exp (Real.pi * Complex.I / 12 * (((hjStep M).1 - 3 : ℤ) : ℂ)) *
        ((Real.sqrt (flt (N : Mat(2, ℤ)) α) : ℝ) : ℂ)) * L)) :=
    (tendsto_const_nhds.mul hsqrt).mul hlimN
  have hpoint : ∀ᶠ k in l,
      ModularForm.eta (flt (M : Mat(2, ℤ)) (tauSeq k)) /
        ModularForm.eta (tauSeq k) =
      (Complex.exp (Real.pi * Complex.I / 12 * (((hjStep M).1 - 3 : ℤ) : ℂ)) *
        Complex.sqrt (flt (N : Mat(2, ℤ)) (tauSeq k))) *
        (ModularForm.eta (flt (N : Mat(2, ℤ)) (tauSeq k)) /
          ModularForm.eta (tauSeq k)) := by
    filter_upwards [him] with k hk
    rw [← hN, eta_hjStep M (tauSeq k) hk]
    ring
  exact hlimit.congr' (hpoint.mono (fun _ h => h.symm))

/-- The bounded induction proving `tendsto_eta_word` along the Hirzebruch–Jung recursion. -/
private theorem tendsto_eta_word_aux {ι : Type*} {l : Filter ι} (tauSeq : ι → ℂ)
    {α : ℝ} (hα : Irrational α) (htauT : Tendsto tauSeq l (nhds (α : ℂ)))
    (him : ∀ᶠ k in l, 0 < (tauSeq k).im) :
    ∀ (n : ℕ) (M : SL(2, ℤ)) (h0 : 0 ≤ M 1 0), (M 1 0).toNat ≤ n →
      (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) α) →
      Tendsto (fun k => ModularForm.eta (flt (M : Mat(2, ℤ)) (tauSeq k)) /
        ModularForm.eta (tauSeq k)) l
        (nhds (Complex.exp (Real.pi * Complex.I / 12 * (wordRademacher M h0 : ℂ)) *
          ((Real.sqrt (fltDenominator (M : Mat(2, ℤ)) α) : ℝ) : ℂ))) := by
  intro n
  induction n with
  | zero =>
      intro M h0 hn hjac
      have hz : M 1 0 = 0 := by omega
      exact tendsto_eta_word_terminal tauSeq h0 hz hjac him
  | succ n ih =>
      intro M h0 hn hjac
      by_cases hz : M 1 0 = 0
      · exact tendsto_eta_word_terminal tauSeq h0 hz hjac him
      have hc : 0 < M 1 0 := h0.lt_of_ne (Ne.symm hz)
      let N := (hjStep M).2
      have hN : (hjStep M).2 = N := rfl
      have h0N : 0 ≤ N 1 0 := by
        rw [← hN, hjStep_snd_lowerLeft]
        exact Int.emod_nonneg _ hc.ne'
      have hltN : N 1 0 < M 1 0 := by
        rw [← hN, hjStep_snd_lowerLeft]
        exact Int.emod_lt_of_pos _ hc
      have hmeas : (N 1 0).toNat ≤ n := by omega
      obtain ⟨hperiod, hjacN⟩ :=
        flt_and_fltDenominator_pos_of_hjStep M α hα hc hjac
      rw [hN] at hperiod hjacN
      have hlimN := ih N h0N hmeas hjacN
      have hstep := tendsto_eta_word_step tauSeq hN hperiod hjacN htauT him hlimN
      rw [← eta_word_step_constant hα h0 hz hN h0N hperiod]
      exact hstep

/-- The eta quotient tends to `exp(πiW(M)/12)√j_M(α)` when `M₁₀ ≥ 0` and
`j_M(α) > 0`, without a fixed-point assumption. The word form of [72, Kopp (2024),
equation (2.7), `eq:etatrans`]. -/
theorem tendsto_eta_word {ι : Type*} {l : Filter ι}
    (tauSeq : ι → ℂ) {α : ℝ} {M : SL(2, ℤ)} (hα : Irrational α)
    (h0 : 0 ≤ M 1 0) (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) α)
    (htauT : Tendsto tauSeq l (nhds (α : ℂ)))
    (him : ∀ᶠ k in l, 0 < (tauSeq k).im) :
    Tendsto (fun k => ModularForm.eta (flt (M : Mat(2, ℤ)) (tauSeq k)) /
      ModularForm.eta (tauSeq k)) l
      (nhds (Complex.exp (Real.pi * Complex.I / 12 * (wordRademacher M h0 : ℂ)) *
        ((Real.sqrt (fltDenominator (M : Mat(2, ℤ)) α) : ℝ) : ℂ))) :=
  tendsto_eta_word_aux tauSeq hα htauT him (M 1 0).toNat M h0 le_rfl hjac

/-- At a positive-trace fixed point, the word exponent is the Rademacher invariant, so
`tendsto_eta_word` has the eta multiplier as its constant. -/
private theorem tendsto_eta_word_fixed {ι : Type*} {l : Filter ι} (tauSeq : ι → ℂ)
    {α : ℝ} {M : SL(2, ℤ)} (hα : Irrational α) (h0 : 0 ≤ M 1 0)
    (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) α)
    (hfix : flt (M : Mat(2, ℤ)) α = α)
    (htauT : Tendsto tauSeq l (nhds (α : ℂ)))
    (him : ∀ᶠ k in l, 0 < (tauSeq k).im) :
    Tendsto (fun k => ModularForm.eta (flt (M : Mat(2, ℤ)) (tauSeq k)) /
      ModularForm.eta (tauSeq k)) l
      (nhds (etaMultiplier M * ((Real.sqrt (fltDenominator (M : Mat(2, ℤ)) α) : ℝ) : ℂ))) := by
  have hlim := tendsto_eta_word tauSeq hα h0 hjac htauT him
  have hw := wordRademacher_eq_rademacherInvariant M h0
    (fun hz => topLeft_pos_of_lowerLeft_eq_zero hjac hz)
    (trace_pos_of_flt_eq_self hfix hjac)
  have hExp : Complex.exp (Real.pi * Complex.I / 12 * (wordRademacher M h0 : ℂ)) =
      etaMultiplier M := by
    rw [etaMultiplier]
    congr 1
    congr 1
    exact_mod_cast hw
  simpa only [hExp] using hlim

/-- At a fixed point with positive Jacobi denominator, inverting the inverse matrix's eta
multiplier and square root gives the original matrix's boundary constant. -/
private lemma eta_inv_constant {M : SL(2, ℤ)} {α : ℝ}
    (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) α)
    (hfix : flt (M : Mat(2, ℤ)) α = α) :
    (etaMultiplier M⁻¹ *
      ((Real.sqrt (fltDenominator ((M⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) α) : ℝ) : ℂ))⁻¹ =
      etaMultiplier M * ((Real.sqrt (fltDenominator (M : Mat(2, ℤ)) α) : ℝ) : ℂ) := by
  have hJ : fltDenominator ((M⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) α =
      (fltDenominator (M : Mat(2, ℤ)) α)⁻¹ :=
    eq_inv_of_mul_eq_one_left
      (fltDenominator_inv_mul_self_of_flt_eq_self hjac.ne' hfix)
  have hμ : etaMultiplier M⁻¹ = (etaMultiplier M)⁻¹ := by
    unfold etaMultiplier
    rw [rademacherInvariant_inv, Rat.cast_neg, ← Complex.exp_neg]
    congr 1
    ring
  rw [hμ, hJ, Real.sqrt_inv]
  simp only [Complex.ofReal_inv, mul_inv_rev, inv_inv]
  ring

/-- The negative-lower-left case of `tendsto_eta_flt_div_eta`, obtained by transporting the
approach through `M` and applying `tendsto_eta_word_fixed` to `M⁻¹`. -/
private theorem tendsto_eta_negative {ι : Type*} {l : Filter ι} (tauSeq : ι → ℂ)
    {α : ℝ} {M : SL(2, ℤ)} (hα : Irrational α)
    (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) α)
    (hfix : flt (M : Mat(2, ℤ)) α = α) (hneg : M 1 0 < 0)
    (htauT : Tendsto tauSeq l (nhds (α : ℂ)))
    (him : ∀ᶠ k in l, 0 < (tauSeq k).im) :
    Tendsto (fun k => ModularForm.eta (flt (M : Mat(2, ℤ)) (tauSeq k)) /
      ModularForm.eta (tauSeq k)) l
      (nhds (etaMultiplier M * ((Real.sqrt (fltDenominator (M : Mat(2, ℤ)) α) : ℝ) : ℂ))) := by
  have h0inv : 0 ≤ (M⁻¹) 1 0 := by rw [SL2Z.lowerLeft_inv]; omega
  have hfixinv := flt_inv_of_flt_eq_self hjac.ne' hfix
  have hJ : fltDenominator ((M⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) α =
      (fltDenominator (M : Mat(2, ℤ)) α)⁻¹ :=
    eq_inv_of_mul_eq_one_left
      (fltDenominator_inv_mul_self_of_flt_eq_self hjac.ne' hfix)
  have hjacinv : 0 < fltDenominator ((M⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) α := by
    rw [hJ]
    exact inv_pos.mpr hjac
  have hdenC : fltDenominator (M : Mat(2, ℤ)) (α : ℂ) ≠ 0 := by
    rw [← ofReal_fltDenominator]
    exact_mod_cast hjac.ne'
  have htauT' : Tendsto (fun k => flt (M : Mat(2, ℤ)) (tauSeq k)) l
      (nhds (α : ℂ)) := by
    convert flt_tendsto (M : Mat(2, ℤ)) htauT hdenC using 1
    rw [← ofReal_flt, hfix]
  have him' : ∀ᶠ k in l, 0 < (flt (M : Mat(2, ℤ)) (tauSeq k)).im := by
    filter_upwards [him] with k hk
    exact flt_im_pos M hk
  have hlimInv := tendsto_eta_word_fixed
    (fun k => flt (M : Mat(2, ℤ)) (tauSeq k)) hα h0inv hjacinv hfixinv htauT' him'
  rw [← eta_inv_constant hjac hfix]
  apply (hlimInv.inv₀ (by
    exact mul_ne_zero (etaMultiplier_ne_zero _) (by
      exact_mod_cast (Real.sqrt_pos.mpr hjacinv).ne'))).congr'
  filter_upwards [him] with k hk
  rw [flt_inv_flt M (tauSeq k)
    (fltDenominator_ne_zero_of_im_ne_zero M hk.ne'), inv_div]

/-- **The eta quotient at a real fixed point**: for `M ∈ SL₂(ℤ)` fixing an irrational `α` with
`j_M(α) > 0`, along any approach `τ_k → α` from the upper half plane,
`η(M·τ_k)/η(τ_k) → μ_M √(j_M(α))`, with `μ_M = e^{πiΨ(M)/12}` the eta multiplier. This is the
eta transformation law [72, Kopp (2024), Section 2.5, `sec:eta`, equation (2.7), `eq:etatrans`],
`η(M·τ) = ψ(M, ε) ε(τ) η(τ)`, passed to the real fixed point, as [RW26b, Radchenko, Wheeler
(2026b), Appendix A, proof of Proposition 3] uses it for the zero orbit. -/
theorem tendsto_eta_flt_div_eta {ι : Type*} {l : Filter ι} (tauSeq : ι → ℂ) {α : ℝ}
    {M : SL(2, ℤ)} (hα : Irrational α) (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) α)
    (hfix : flt (M : Mat(2, ℤ)) α = α) (htauT : Tendsto tauSeq l (nhds (α : ℂ)))
    (him : ∀ᶠ k in l, 0 < (tauSeq k).im) :
    Tendsto (fun k => ModularForm.eta (flt (M : Mat(2, ℤ)) (tauSeq k)) /
        ModularForm.eta (tauSeq k)) l
      (nhds (etaMultiplier M * ((Real.sqrt (fltDenominator (M : Mat(2, ℤ)) α) : ℝ) : ℂ))) := by
  by_cases h0 : 0 ≤ M 1 0
  · exact tendsto_eta_word_fixed tauSeq hα h0 hjac hfix htauT him
  · exact tendsto_eta_negative tauSeq hα hjac hfix (lt_of_not_ge h0) htauT him

/-! ### Integral characteristics with `r₁ > 0`

The period product has no vanishing factor and its quotient is an eta quotient up to factors
tending to `1`. -/

/-- For an integral characteristic with `r₁ = k + 1`, its period product is the eta q-product
after the first `k` factors; used by `sfPeriodProduct_ratio_eq_eta`. -/
private lemma sfPeriodProduct_split {r : Fin 2 → ℚ} (hr : IsIntegralIndex r)
    {k : ℕ} (hk : (r 1).num = (k : ℤ) + 1) (τ : ℂ) (hτ : 0 < τ.im) :
    qPochhammerFin (k : ℤ) τ τ * sfPeriodProduct r τ = qPochhammer τ τ := by
  have harg : fracSymplecticFormRat r τ = τ + (k : ℂ) * τ - ((r 0).num : ℂ) := by
    rw [fracSymplecticFormRat_of_isIntegralIndex hr τ, hk]
    push_cast
    ring
  have hshift : qPochhammer (fracSymplecticFormRat r τ) τ =
      qPochhammer (τ + (k : ℂ) * τ) τ := by
    rw [harg, sub_eq_add_neg]
    simpa only [Int.cast_neg] using
      qPochhammer_add_intCast (τ + (k : ℂ) * τ) τ (-(r 0).num)
  rw [sfPeriodProduct, hshift]
  exact qPochhammerFin_natCast_mul_qPochhammer_add k τ τ hτ

/-- The finite eta q-product at an irrational real argument has no zero factor; used by
`tendsto_finite_eta_ratio`. -/
private lemma finite_eta_ne_zero (k : ℕ) {α : ℝ} (hα : Irrational α) :
    qPochhammerFin (k : ℤ) (α : ℂ) (α : ℂ) ≠ 0 := by
  apply qPochhammerFin_ne_zero_of_forall_ne_int (k : ℤ) α α
  intro j hj m
  have hjpos : (j + 1 : ℤ) ≠ 0 := by rcases hj with ⟨hj0, _⟩ | ⟨_, hjneg⟩ <;> omega
  have hirr : Irrational (((j + 1 : ℤ) : ℝ) * α) :=
    irrational_intCast_mul_iff.mpr ⟨hjpos, hα⟩
  have hne := hirr.ne_int m
  convert hne using 1
  push_cast
  ring

/-- The integral-characteristic quotient equals the eta quotient times the exponential and
finite-factor corrections, as in [72, Kopp (2024), p. 38]. -/
private lemma sfPeriodProduct_ratio_eq_eta {r : Fin 2 → ℚ} (hr : IsIntegralIndex r)
    {k : ℕ} (hk : (r 1).num = (k : ℤ) + 1) (σ τ : ℂ)
    (hσ : 0 < σ.im) (hτ : 0 < τ.im) :
    sfPeriodProduct r σ / sfPeriodProduct r τ =
      Complex.exp (Real.pi * Complex.I * (τ - σ) / 12) *
        (ModularForm.eta σ / ModularForm.eta τ) *
          (qPochhammerFin (k : ℤ) τ τ / qPochhammerFin (k : ℤ) σ σ) := by
  have hsplitσ := sfPeriodProduct_split hr hk σ hσ
  have hsplitτ := sfPeriodProduct_split hr hk τ hτ
  have hQτ := qPochhammer_tau_ne_zero τ hτ
  have hFσ : qPochhammerFin (k : ℤ) σ σ ≠ 0 := by
    intro h
    rw [h] at hsplitσ
    have hQσ := qPochhammer_tau_ne_zero σ hσ
    exact hQσ (by simpa using hsplitσ.symm)
  have hFτ : qPochhammerFin (k : ℤ) τ τ ≠ 0 := by
    intro h
    rw [h] at hsplitτ
    exact hQτ (by simpa using hsplitτ.symm)
  have hPσ : sfPeriodProduct r σ = qPochhammer σ σ / qPochhammerFin (k : ℤ) σ σ := by
    apply (eq_div_iff hFσ).mpr
    simpa only [mul_comm] using hsplitσ
  have hPτ : sfPeriodProduct r τ = qPochhammer τ τ / qPochhammerFin (k : ℤ) τ τ := by
    apply (eq_div_iff hFτ).mpr
    simpa only [mul_comm] using hsplitτ
  rw [hPσ, hPτ, ← qPochhammer_self_div_eq_eta σ τ]
  field_simp [hQτ, hFσ, hFτ]

/-- If two complex approaches tend to the same real point, the eta exponential correction tends
to `1`; used by `tendsto_sfPeriodProduct_div_integral`. -/
private lemma tendsto_eta_exp_correction {ι : Type*} {l : Filter ι}
    {u v : ι → ℂ} {α : ℝ} (hu : Tendsto u l (nhds (α : ℂ)))
    (hv : Tendsto v l (nhds (α : ℂ))) :
    Tendsto (fun j => Complex.exp (Real.pi * Complex.I * (u j - v j) / 12)) l
      (nhds (1 : ℂ)) := by
  have hdiff := hu.sub hv
  have hmul : Tendsto (fun j => Real.pi * Complex.I * (u j - v j) / 12) l
      (nhds (Real.pi * Complex.I * ((α : ℂ) - (α : ℂ)) / 12)) :=
    (tendsto_const_nhds.mul hdiff).div_const (12 : ℂ)
  have hexp := (Complex.continuous_exp.tendsto _).comp hmul
  simpa only [Function.comp_def, sub_self, mul_zero, zero_div, Complex.exp_zero] using hexp

/-- The ratio of the finite eta q-products along two approaches to an irrational point tends to
`1`; used by `tendsto_sfPeriodProduct_div_integral`. -/
private lemma tendsto_finite_eta_ratio {ι : Type*} {l : Filter ι}
    (k : ℕ) {u v : ι → ℂ} {α : ℝ} (hα : Irrational α)
    (hu : Tendsto u l (nhds (α : ℂ))) (hv : Tendsto v l (nhds (α : ℂ))) :
    Tendsto (fun j => qPochhammerFin (k : ℤ) (u j) (u j) /
      qPochhammerFin (k : ℤ) (v j) (v j)) l (nhds (1 : ℂ)) := by
  have hF : qPochhammerFin (k : ℤ) (α : ℂ) (α : ℂ) ≠ 0 := finite_eta_ne_zero k hα
  have hc := continuousAt_qPochhammerFin (k : ℤ) hF
  have hpair := hu.prodMk_nhds hu
  have hFu' := hc.tendsto.comp hpair
  have hFu : Tendsto (fun j => qPochhammerFin (k : ℤ) (u j) (u j)) l
      (nhds (qPochhammerFin (k : ℤ) (α : ℂ) (α : ℂ))) := by
    simpa only [Function.comp_def] using hFu'
  have hFv' := hc.tendsto.comp (hv.prodMk_nhds hv)
  have hFv : Tendsto (fun j => qPochhammerFin (k : ℤ) (v j) (v j)) l
      (nhds (qPochhammerFin (k : ℤ) (α : ℂ) (α : ℂ))) := by
    simpa only [Function.comp_def] using hFv'
  have hratio := hFu.div hFv hF
  change Tendsto (fun j => qPochhammerFin (k : ℤ) (u j) (u j) /
      qPochhammerFin (k : ℤ) (v j) (v j)) l
      (nhds (qPochhammerFin (k : ℤ) (α : ℂ) (α : ℂ) /
        qPochhammerFin (k : ℤ) (α : ℂ) (α : ℂ))) at hratio
  simpa only [div_self hF] using hratio

/-- The integral period-product ratio has the same boundary limit as the eta quotient:
the exponential and finite-factor corrections both tend to `1`. -/
private theorem tendsto_sfPeriodProduct_div_of_eta {ι : Type*} {l : Filter ι}
    (u v : ι → ℂ) {α : ℝ} {r : Fin 2 → ℚ} (hr : IsIntegralIndex r)
    {k : ℕ} (hk : (r 1).num = (k : ℤ) + 1) (hα : Irrational α)
    (hu : Tendsto u l (nhds (α : ℂ))) (hv : Tendsto v l (nhds (α : ℂ)))
    (huim : ∀ᶠ j in l, 0 < (u j).im) (hvim : ∀ᶠ j in l, 0 < (v j).im)
    {L : ℂ} (heta : Tendsto (fun j => ModularForm.eta (v j) / ModularForm.eta (u j)) l
      (nhds L)) :
    Tendsto (fun j => sfPeriodProduct r (v j) / sfPeriodProduct r (u j)) l (nhds L) := by
  let q : ι → ℂ := fun j =>
    Complex.exp (Real.pi * Complex.I * (u j - v j) / 12) *
      (ModularForm.eta (v j) / ModularForm.eta (u j)) *
        (qPochhammerFin (k : ℤ) (u j) (u j) / qPochhammerFin (k : ℤ) (v j) (v j))
  have hlim : Tendsto q l (nhds L) := by
    have h := ((tendsto_eta_exp_correction hu hv).mul heta).mul
      (tendsto_finite_eta_ratio k hα hu hv)
    change Tendsto q l (nhds ((1 : ℂ) * L * 1)) at h
    simpa only [one_mul, mul_one] using h
  have hpoint : ∀ᶠ j in l, sfPeriodProduct r (v j) / sfPeriodProduct r (u j) = q j := by
    filter_upwards [huim, hvim] with j hju hjv
    exact sfPeriodProduct_ratio_eq_eta hr hk _ _ hjv hju
  exact hlim.congr' (hpoint.mono (fun _ h => h.symm))

/-- **The period-product quotient at an integral characteristic**: for `r ∈ ℤ²` with `r₁ > 0`,
`M ∈ SL₂(ℤ)` fixing an irrational `α` with `j_M(α) > 0`, and any approach `τ_k → α` from the upper
half plane, `ϖ_r(M·τ_k)/ϖ_r(τ_k) → ש^r_M(α)`. The companion of `tendsto_sfPeriodProduct_div_total`
for the integral characteristics at which [72, Kopp (2024), Definition 2.2] has no vanishing
factor; at `r = (0, 1)` the quotient is [72, Kopp (2024), p. 38]. -/
theorem tendsto_sfPeriodProduct_div_integral {ι : Type*} {l : Filter ι}
    (tauSeq : ι → ℂ) {α : ℝ} {r : Fin 2 → ℚ} {M : SL(2, ℤ)} (hM : M ∈ gammaSubgroup r)
    (hr : IsIntegralIndex r) (hr1 : 0 < r 1) (hα : Irrational α)
    (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) α) (hfix : flt (M : Mat(2, ℤ)) α = α)
    (htauT : Tendsto tauSeq l (nhds (α : ℂ))) (him : ∀ᶠ k in l, 0 < (tauSeq k).im) :
    Tendsto (fun k => sfPeriodProduct r (flt (M : Mat(2, ℤ)) (tauSeq k)) /
        sfPeriodProduct r (tauSeq k)) l (nhds (sfModularCocycleRealTotal r M hM α)) := by
  let k : ℕ := ((r 1).num - 1).toNat
  have hnum : 0 < (r 1).num := Rat.num_pos.mpr hr1
  have hk : (r 1).num = (k : ℤ) + 1 := by
    dsimp [k]
    rw [Int.toNat_of_nonneg (by omega : 0 ≤ (r 1).num - 1)]
    omega
  have hdenC : fltDenominator (M : Mat(2, ℤ)) (α : ℂ) ≠ 0 := by
    rw [← ofReal_fltDenominator]
    exact_mod_cast hjac.ne'
  have htauT' : Tendsto (fun j => flt (M : Mat(2, ℤ)) (tauSeq j)) l
      (nhds (α : ℂ)) := by
    convert flt_tendsto (M : Mat(2, ℤ)) htauT hdenC using 1
    rw [← ofReal_flt, hfix]
  have him' : ∀ᶠ j in l, 0 < (flt (M : Mat(2, ℤ)) (tauSeq j)).im := by
    filter_upwards [him] with j hj
    exact flt_im_pos M hj
  have heta := tendsto_eta_flt_div_eta tauSeq hα hjac hfix htauT him
  have hlim := tendsto_sfPeriodProduct_div_of_eta tauSeq
    (fun j => flt (M : Mat(2, ℤ)) (tauSeq j)) hr hk hα htauT htauT' him him' heta
  rw [sfModularCocycleRealTotal_integral_of_flt_eq_self hα hr hM hjac hfix,
    ite_eq_left hr1]
  simpa only [etaMultiplier] using hlim

end SIC
