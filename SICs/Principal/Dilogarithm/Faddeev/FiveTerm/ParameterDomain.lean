/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.Kernel
import SICs.SpecialFunctions.Faddeev.FiveTerm.ParameterDomain

/-!
# Principal parameters for the five-term integral

At the positive principal period, membership in the five-term parameter strip is exactly the pair
of strict principal convergence-rate conditions.

This module follows the parameter conditions in [RW26, Radchenko, Wheeler (2026), Theorem 3,
`thm:5term.mod.fad`, equation (23), `eq:5term.int`] at `A_d` and `τ=ρ_d`.

## The argument

The Jacobi denominator equals `ρ_d³` at the principal root. Substituting it into the two affine
expressions that define the parameter strip turns them into the principal upper and lower rates.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### Parameters at the principal period

At `τ=ρ_d` the two affine strip expressions are the principal upper and lower rates. -/

/-- At `τ=ρ_d`, the upper parameter-strip expression is the principal upper rate; used by
`mem_fiveTermParameterStrip_principalRoot`. -/
private lemma principalFiveTermUpperParameter_re_principalRoot
    (d : ℕ) (hd : 3 < d) (ℓ : ℤ) (w : ℝ) :
    (((((principalA d) 1 0 : ℤ) : ℂ) * (w : ℂ) /
      fltDenominator (principalA d : Mat(2, ℤ)) (principalRoot d : ℂ) + ℓ)).re =
        principalFiveTermUpperRate d ℓ w := by
  rw [fltDenominator_principalA_principalRoot_complex d hd]
  simp [principalFiveTermUpperRate, coe_principalA, ← Complex.ofReal_pow]

/-- At `τ=ρ_d`, the lower parameter-strip expression is the principal lower rate; used by
`mem_fiveTermParameterStrip_principalRoot`. -/
private lemma principalFiveTermLowerParameter_re_principalRoot
    (d : ℕ) (hd : 3 < d) (ℓ p : ℤ) (w y : ℝ) :
    (((((principalA d) 1 0 : ℤ) : ℂ) * ((w : ℂ) + y) /
      fltDenominator (principalA d : Mat(2, ℤ)) (principalRoot d : ℂ) + ℓ + p - 1)).re =
        principalFiveTermLowerRate d ℓ p w y := by
  rw [fltDenominator_principalA_principalRoot_complex d hd]
  simp [principalFiveTermLowerRate, coe_principalA, ← Complex.ofReal_pow]

/-- At the principal root, membership in the general five-term parameter strip is exactly the
pair of strict principal upper and lower rate conditions. -/
theorem mem_fiveTermParameterStrip_principalRoot
    (d : ℕ) (hd : 3 < d) (ℓ p : ℤ) (w y : ℝ) :
    (w : ℂ) ∈ fiveTermParameterStrip (principalA d) ℓ p y (principalRoot d) ↔
      0 < principalFiveTermUpperRate d ℓ w ∧
        principalFiveTermLowerRate d ℓ p w y < 0 := by
  rw [mem_fiveTermParameterStrip,
    principalFiveTermUpperParameter_re_principalRoot d hd,
    principalFiveTermLowerParameter_re_principalRoot d hd]

end SIC
