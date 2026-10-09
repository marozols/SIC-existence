/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# Irrational real linear relations

Rational and integer coefficient uniqueness for linear expressions at an irrational real point.

This module supplies the elementary irrationality step used by fractional linear transformations
and the period lattice. A rational multiple of an irrational real cannot be rational unless the
coefficient vanishes.

## The argument

If a nonzero rational coefficient multiplied by an irrational real were rational, division by
that coefficient would make the real rational. Applying this to the difference of two lattice
expressions gives uniqueness of their integer coordinates.
-/

namespace SIC

/-! ### Rational and integer coefficients -/

/-- **A rational linear relation at an irrational point is trivial**: if `a·τ = b` with `a` and
`b` rational and `τ` irrational, then `a = 0` and `b = 0`. A nonzero `a` would exhibit `τ = b/a`
as rational, and then `b = 0·τ = 0`. Both conclusions are read off the same relation and are
always used together. This is the common step in the fractional-linear and lattice arguments. -/
theorem ratCast_eq_zero_of_irrational_mul {τ : ℝ} (hτ : Irrational τ) {a b : ℚ}
    (h : (a : ℝ) * τ = (b : ℝ)) : a = 0 ∧ b = 0 := by
  have ha : a = 0 := by
    by_contra ha
    exact (irrational_ratCast_mul_iff.mpr ⟨ha, hτ⟩) ⟨b, h.symm⟩
  exact ⟨ha, by simpa [ha] using h.symm⟩

/-- At irrational real `τ`, the integer coefficients of `m+nτ` are unique. -/
lemma intCast_add_intCast_mul_eq_iff_of_irrational (τ : ℝ) (hirr : Irrational τ)
    (m n m' n' : ℤ) :
    (m : ℂ) + (n : ℂ) * τ = (m' : ℂ) + (n' : ℂ) * τ ↔ m = m' ∧ n = n' := by
  constructor
  · intro h
    have hreal : (m : ℝ) + (n : ℝ) * τ = (m' : ℝ) + (n' : ℝ) * τ := by
      simpa using congrArg Complex.re h
    have hrel : (((n - n' : ℤ) : ℚ) : ℝ) * τ = (((m' - m : ℤ) : ℚ) : ℝ) := by
      push_cast
      linear_combination hreal
    have hn : n = n' := by
      have h := (ratCast_eq_zero_of_irrational_mul hirr hrel).1
      exact sub_eq_zero.mp (by exact_mod_cast h)
    subst n'
    have hm : (m : ℝ) = (m' : ℝ) := by nlinarith [hreal]
    exact ⟨by exact_mod_cast hm, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

end SIC
