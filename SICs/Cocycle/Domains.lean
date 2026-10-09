/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SL2Z.FractionalLinear

/-!
# The domain `D_M` of the Shintani--Faddeev cocycle

The source domain `D_M` and its real-line membership criterion.

This file defines the domain `D_M` of [AFK25, Definition 1.15, `def:sl2ldmndf`] and proves its
real-line membership criterion. The domain removes from `ℂ` the real ray on which
`det(M) · j_M(τ) ≤ 0`, where `j_M(τ) = cτ + d` is the Jacobi denominator `fltDenominator` of
`SICs.SL2Z.FractionalLinear`; every nonreal point is admitted.

For `M ∈ SL₂(ℤ)` the determinant is one, so on the real line membership is exactly positivity of
the Jacobi denominator (`mem_sfDomain_ofReal_iff`).

The domain is shared by the upper-half-plane product quotient (`SICs.Cocycle.UpperHalfPlane`),
the real modular cocycle (`SICs.Cocycle.Modular.Values`, `SICs.Cocycle.Modular.Shifts`), and the
domain facts for associated stabilizers (`SICs.Admissible.StabilizerDomain`). Each of these needs
only the criterion proved here.

## Main declarations

- `sfDomain`: the set `D_M = ℂ \ {τ ∈ ℝ | det(M) · j_M(τ) ≤ 0}`.
- `mem_sfDomain_ofReal_iff`: the real-line criterion `0 < j_M(τ)`.

## References

- [AFK25, Definition 1.15, `def:sl2ldmndf`]
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### The domain

The source states the formula for `M ∈ GL₂(ℤ)`; it makes sense for any integer matrix, which is
the totalization used here. -/

/-- The set given by the formula for the domain `D_M` of the SF Jacobi cocycle:
    `D_M = ℂ \ {τ ∈ ℝ | det(M) · j_M(τ) ≤ 0}`.

    In [AFK25], `M` is required to lie in `GL₂(ℤ)`; the displayed set-valued expression also
    makes sense for an arbitrary integer matrix, which is the harmless totalization used here.
    Roughly: D_M excludes a real ray where the denominator has the wrong sign.
    See [AFK25, Definition 1.15, `def:sl2ldmndf`]. -/
@[source "AFK25, Definition 1.15, p. 9, def:sl2ldmndf" (symbol := "D_M")]
def sfDomain (M : Mat(2, ℤ)) : Set ℂ :=
  {τ : ℂ | τ.im ≠ 0 ∨ 0 < M.det * (fltDenominator M τ).re}

/-! ### The real line

For real arguments, membership is positivity of the Jacobi denominator `fltDenominator`.
This condition ensures positive periods in the word product and holds for associated stabilizers. -/

/-- **`τ ∈ D_M` for real `τ` is positivity of the Jacobi denominator.** `sfDomain`
removes from `D_M` the real ray where `det(M)·j_M(τ) ≤ 0`; for `M ∈ SL₂(ℤ)` the determinant is
`1`, so on the real line the condition is just `j_M(τ) > 0`. -/
theorem mem_sfDomain_ofReal_iff (M : SL(2, ℤ)) (τ : ℝ) :
    ((τ : ℝ) : ℂ) ∈ sfDomain (M : Mat(2, ℤ)) ↔
      0 < fltDenominator (M : Mat(2, ℤ)) τ := by
  simp [sfDomain, ← ofReal_fltDenominator, M.2]

end SIC

end
