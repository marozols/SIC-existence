/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.ComplexPhase
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.Boundary

/-!
# Uniform complex-period bounds for the principal five-term kernel

The principal five-term kernel has uniform exponential bounds on upper and lower vertical tails
as its complex period approaches the positive real principal root.

This module follows [RW26, Radchenko, Wheeler (2026), Lemma 1, `lem:asymp`, equations (13),
`eq:PhiS.reflection`, (20), `eq:modulartofaddeevCF`, and (23), `eq:5term.int`].

## The argument

On an upper vertical tail, both principal Faddeev products tend uniformly and exponentially to
one. Once their errors are at most `1/2`, their quotient has norm at most three, while the exact
kernel phase supplies the exponential decay. On a lower tail, each product is first divided by
its exact reflection exponential. The same quotient estimate applies, and the quotient of the
two reflection exponentials combines with the original phase to give the reflected phase. Its
quadratic terms cancel, leaving the strictly decaying affine phase established in
`ComplexPhase`.
-/

noncomputable section

open Complex

namespace SIC

/-! ### Exact lower normalization -/

/-- The complex-period five-term kernel is the quotient of the two reflected-normalized
principal products times the reflected phase exponential. -/
lemma principalFiveTermKernelComplex_eq_lower_normalized
    (d : ℕ) (ℓ p m : ℤ) (w y τ z : ℂ) :
    principalFiveTermKernelComplex d ℓ p w y τ m z =
      (principalFaddeevComplex d (m + 1) 0 z τ /
          Complex.exp (principalFaddeevLowerExponentComplex d (m + 1) 0 z τ)) /
        (principalFaddeevComplex d (m + p) 0 (z + y) τ /
          Complex.exp (principalFaddeevLowerExponentComplex d (m + p) 0 (z + y) τ)) *
        Complex.exp (principalFiveTermReflectedPhaseComplex d ℓ p m w y z τ) := by
  let N := principalFaddeevComplex d (m + 1) 0 z τ
  let D := principalFaddeevComplex d (m + p) 0 (z + y) τ
  let E₁ := principalFaddeevLowerExponentComplex d (m + 1) 0 z τ
  let E₂ := principalFaddeevLowerExponentComplex d (m + p) 0 (z + y) τ
  let P := principalFiveTermPhaseComplex d ℓ w m z τ
  change N / D * Complex.exp P =
    (N / Complex.exp E₁) / (D / Complex.exp E₂) *
      Complex.exp (E₁ - E₂ + P)
  rw [show Complex.exp (E₁ - E₂ + P) =
      (Complex.exp E₁ / Complex.exp E₂) * Complex.exp P by
    rw [Complex.exp_add, Complex.exp_sub],
    div_div_div_comm, ← mul_assoc,
    div_mul_cancel₀ _ (div_ne_zero (Complex.exp_ne_zero E₁) (Complex.exp_ne_zero E₂))]

/-! ### Uniformly bounded product ratios -/

/-- On a sufficiently high vertical tail, the quotient of the two complex-period principal
products in the five-term kernel has norm at most three, uniformly near the principal root. -/
private lemma exists_norm_complex_ratio_le_three_upper
    (d : ℕ) (hd : 3 < d) (p m : ℤ) (y x : ℝ) :
    ∃ ε T : ℝ, 0 < ε ∧ 0 < T ∧
      ∀ τ : ℂ, ‖τ - (principalRoot d : ℂ)‖ ≤ ε → ∀ t : ℝ, T ≤ t →
        ‖principalFaddeevComplex d (m + 1) 0 ((x : ℂ) + t * I) τ /
          principalFaddeevComplex d (m + p) 0
            (((x : ℂ) + t * I) + y) τ‖ ≤ 3 := by
  obtain ⟨ε₁, C₁, κ₁, R₁, hε₁, _, hκ₁, _, h₁⟩ :=
    exists_norm_principalFaddeevComplex_sub_one_le d hd (m + 1) 0 1
  obtain ⟨ε₂, C₂, κ₂, R₂, hε₂, _, hκ₂, _, h₂⟩ :=
    exists_norm_principalFaddeevComplex_sub_one_le d hd (m + p) 0 1
  let ε := min ε₁ ε₂
  let T := max 1 (max |x| (max |x + y|
    (max R₁ (max R₂ (max (2 * C₁ / κ₁) (2 * C₂ / κ₂))))))
  refine ⟨ε, T, lt_min hε₁ hε₂,
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun τ hτ t ht => ?_⟩
  have hle (a : ℝ) (ha : a ≤ T) : a ≤ t := ha.trans ht
  have hτ₁ : ‖τ - (principalRoot d : ℂ)‖ ≤ ε₁ := hτ.trans (by simp [ε])
  have hτ₂ : ‖τ - (principalRoot d : ℂ)‖ ≤ ε₂ := hτ.trans (by simp [ε])
  have h₁' := h₁ τ ((x : ℂ) + t * I) hτ₁
    (by simpa using hle |x| (by simp [T])) (by simpa using hle R₁ (by simp [T]))
  have h₂' := h₂ τ (((x : ℂ) + t * I) + y) hτ₂
    (by simpa using hle |x + y| (by simp [T])) (by simpa using hle R₂ (by simp [T]))
  have hC₁ : 2 * C₁ ≤ κ₁ * t := by
    have := (div_le_iff₀ hκ₁).mp (hle (2 * C₁ / κ₁) (by simp [T]))
    nlinarith
  have hC₂ : 2 * C₂ ≤ κ₂ * t := by
    have := (div_le_iff₀ hκ₂).mp (hle (2 * C₂ / κ₂) (by simp [T]))
    nlinarith
  apply norm_div_le_three_of_exponential_bounds _ _ hC₁ hC₂
  · simpa using h₁'
  · simpa using h₂'

/-- On a sufficiently low vertical tail, the quotient of the two reflected-normalized
complex-period principal products has norm at most three, uniformly near the principal root. -/
private lemma exists_norm_complex_ratio_le_three_lower
    (d : ℕ) (hd : 3 < d) (p m : ℤ) (y x : ℝ) :
    ∃ ε T : ℝ, 0 < ε ∧ 0 < T ∧
      ∀ τ : ℂ, ‖τ - (principalRoot d : ℂ)‖ ≤ ε → ∀ t : ℝ, t ≤ -T →
        ‖(principalFaddeevComplex d (m + 1) 0 ((x : ℂ) + t * I) τ /
            Complex.exp (principalFaddeevLowerExponentComplex d (m + 1) 0
              ((x : ℂ) + t * I) τ)) /
          (principalFaddeevComplex d (m + p) 0 (((x : ℂ) + t * I) + y) τ /
            Complex.exp (principalFaddeevLowerExponentComplex d (m + p) 0
              (((x : ℂ) + t * I) + y) τ))‖ ≤ 3 := by
  obtain ⟨ε₁, C₁, κ₁, R₁, hε₁, _, hκ₁, _, h₁⟩ :=
    exists_norm_principalFaddeevComplex_div_exp_sub_one_le d hd (m + 1) 0 1
  obtain ⟨ε₂, C₂, κ₂, R₂, hε₂, _, hκ₂, _, h₂⟩ :=
    exists_norm_principalFaddeevComplex_div_exp_sub_one_le d hd (m + p) 0 1
  let ε := min ε₁ ε₂
  let T := max 1 (max |x| (max |x + y|
    (max R₁ (max R₂ (max (2 * C₁ / κ₁) (2 * C₂ / κ₂))))))
  refine ⟨ε, T, lt_min hε₁ hε₂,
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun τ hτ t ht => ?_⟩
  have hheight : T ≤ -t := by linarith
  have hle (a : ℝ) (ha : a ≤ T) : a ≤ -t := ha.trans hheight
  have hτ₁ : ‖τ - (principalRoot d : ℂ)‖ ≤ ε₁ := hτ.trans (by simp [ε])
  have hτ₂ : ‖τ - (principalRoot d : ℂ)‖ ≤ ε₂ := hτ.trans (by simp [ε])
  have h₁' := h₁ τ ((x : ℂ) + t * I) hτ₁
    (by simpa using hle |x| (by simp [T])) (by simpa using hle R₁ (by simp [T]))
  have h₂' := h₂ τ (((x : ℂ) + t * I) + y) hτ₂
    (by simpa using hle |x + y| (by simp [T])) (by simpa using hle R₂ (by simp [T]))
  have hC₁ : 2 * C₁ ≤ κ₁ * (-t) := by
    have := (div_le_iff₀ hκ₁).mp (hle (2 * C₁ / κ₁) (by simp [T]))
    nlinarith
  have hC₂ : 2 * C₂ ≤ κ₂ * (-t) := by
    have := (div_le_iff₀ hκ₂).mp (hle (2 * C₂ / κ₂) (by simp [T]))
    nlinarith
  apply norm_div_le_three_of_exponential_bounds _ _ hC₁ hC₂
  · simpa using h₁'
  · simpa using h₂'

/-! ### Uniform upper and lower bounds -/

/-- Uniformly for complex periods near the positive principal root, the complex-period
five-term kernel decays exponentially on an upper vertical tail whenever its upper rate is
positive. This combines the upper clause of [RW26, Radchenko, Wheeler (2026), Lemma 1,
`lem:asymp`] with equation (23), `eq:5term.int`. -/
theorem exists_norm_principalFiveTermKernelComplex_upper
    (d : ℕ) (hd : 3 < d) (ℓ p m : ℤ) (w y x : ℝ)
    (hRate : 0 < principalFiveTermUpperRate d ℓ w) :
    ∃ ε C κ T : ℝ, 0 < ε ∧ 0 < C ∧ 0 < κ ∧ 0 < T ∧
      ∀ τ : ℂ, ‖τ - (principalRoot d : ℂ)‖ ≤ ε → ∀ t : ℝ, T ≤ t →
        ‖principalFiveTermKernelComplex d ℓ p w y τ m
          ((x : ℂ) + t * I)‖ ≤ C * Real.exp (-κ * t) := by
  obtain ⟨ε₁, T, hε₁, hT, hratio⟩ :=
    exists_norm_complex_ratio_le_three_upper d hd p m y x
  obtain ⟨ε₂, C, κ, hε₂, hC, hκ, hphase⟩ :=
    exists_norm_exp_principalFiveTermPhaseComplex_le d hd ℓ m w x hRate
  let ε := min ε₁ ε₂
  refine ⟨ε, 3 * C, κ, T, lt_min hε₁ hε₂, mul_pos (by norm_num) hC, hκ, hT,
    fun τ hτ t ht => ?_⟩
  have hratio' := hratio τ (hτ.trans (by simp [ε])) t ht
  have hphase' := hphase τ (hτ.trans (by simp [ε])) t (hT.le.trans ht)
  change ‖principalFaddeevComplex d (m + 1) 0 ((x : ℂ) + t * I) τ /
      principalFaddeevComplex d (m + p) 0 (((x : ℂ) + t * I) + y) τ *
        Complex.exp (principalFiveTermPhaseComplex d ℓ w m ((x : ℂ) + t * I) τ)‖ ≤ _
  rw [norm_mul]
  calc
    _ ≤ 3 * (C * Real.exp (-κ * t)) :=
      mul_le_mul hratio' hphase' (norm_nonneg _) (by norm_num)
    _ = (3 * C) * Real.exp (-κ * t) := by ring

/-- Uniformly for complex periods near the positive principal root, the complex-period
five-term kernel decays exponentially on a lower vertical tail whenever its lower rate is
negative. The exact lower normalizations from Lemma 1 and equations (13), (20) combine into the
reflected phase of equation (23). -/
theorem exists_norm_principalFiveTermKernelComplex_lower
    (d : ℕ) (hd : 3 < d) (ℓ p m : ℤ) (w y x : ℝ)
    (hRate : principalFiveTermLowerRate d ℓ p w y < 0) :
    ∃ ε C κ T : ℝ, 0 < ε ∧ 0 < C ∧ 0 < κ ∧ 0 < T ∧
      ∀ τ : ℂ, ‖τ - (principalRoot d : ℂ)‖ ≤ ε → ∀ t : ℝ, t ≤ -T →
        ‖principalFiveTermKernelComplex d ℓ p w y τ m
          ((x : ℂ) + t * I)‖ ≤ C * Real.exp (κ * t) := by
  obtain ⟨ε₁, T, hε₁, hT, hratio⟩ :=
    exists_norm_complex_ratio_le_three_lower d hd p m y x
  obtain ⟨ε₂, C, κ, hε₂, hC, hκ, hphase⟩ :=
    exists_norm_exp_principalFiveTermReflectedPhaseComplex_le
      d hd ℓ p m w y x hRate
  let ε := min ε₁ ε₂
  refine ⟨ε, 3 * C, κ, T, lt_min hε₁ hε₂, mul_pos (by norm_num) hC, hκ, hT,
    fun τ hτ t ht => ?_⟩
  have hratio' := hratio τ (hτ.trans (by simp [ε])) t ht
  have hphase' := hphase τ (hτ.trans (by simp [ε])) t
    (ht.trans (neg_nonpos.mpr hT.le))
  rw [principalFiveTermKernelComplex_eq_lower_normalized]
  rw [norm_mul]
  calc
    _ ≤ 3 * (C * Real.exp (κ * t)) :=
      mul_le_mul hratio' hphase' (norm_nonneg _) (by norm_num)
    _ = (3 * C) * Real.exp (κ * t) := by ring

end SIC
