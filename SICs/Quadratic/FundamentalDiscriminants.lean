/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.NumberTheory.FundamentalDiscriminant

/-!
# Fundamental Discriminants

The squarefree characterization of fundamental discriminants.

This file isolates the elementary arithmetic notion of a fundamental discriminant used throughout
the real-quadratic parts of the SIC construction. Mathlib's predicate is used directly. Its
squarefree characterization says that `Δ` is
squarefree and congruent to `1` modulo `4`, or is four times a squarefree integer congruent to `2`
or `3` modulo `4`.  Their immediate common consequence is the familiar congruence
`Δ ≡ 0, 1 (mod 4)`.

## Main definitions and results

- `IsFundamentalDiscriminant`: an abbreviation for Mathlib's fundamental-discriminant predicate.
- `isFundamentalDiscriminant_iff_squarefree`: the standard squarefree characterization.
- `IsFundamentalDiscriminant.emod_four`: a fundamental discriminant is `0` or `1` modulo `4`.

## References

- [AFK25, equation (1.33)]
-/

namespace SIC

/-! ### Arithmetic characterization

The characterization keeps the two squarefree alternatives explicit so that consumers can use
the odd and four-divisible cases directly. In the latter case, Mathlib uses `Δ / 4`; divisibility
by `4` identifies this quotient with the existential squarefree integer. The predicate allows
both signs and `1`; applications to real quadratic fields add positivity and nonsquareness
separately.
-/

/-- An integer is a fundamental discriminant when it has the standard squarefree shape:
either it is squarefree and congruent to `1` modulo `4`, or it is four times a squarefree
integer congruent to `2` or `3` modulo `4`.

This is Mathlib's `Int.IsFundamentalDiscr`. It allows both signs and `1`; applications to real
quadratic fields additionally assume positivity and nonsquareness.
See [AFK25, equation (1.33)]. -/
abbrev IsFundamentalDiscriminant (Δ : ℤ) : Prop := Int.IsFundamentalDiscr Δ

/-- A fundamental discriminant is squarefree with `Δ ≡ 1 (mod 4)`, or has the shape `Δ = 4D`
with `D` squarefree and `D ≡ 2, 3 (mod 4)`; see `IsFundamentalDiscriminant` for the source. -/
lemma isFundamentalDiscriminant_iff_squarefree {Δ : ℤ} :
    IsFundamentalDiscriminant Δ ↔
      (Squarefree Δ ∧ Δ % 4 = 1) ∨
        ∃ D : ℤ, Squarefree D ∧ (D % 4 = 2 ∨ D % 4 = 3) ∧ Δ = 4 * D := by
  rw [IsFundamentalDiscriminant, Int.isFundamentalDiscr_iff_squarefree]
  constructor
  · rintro (⟨hmod, hsq⟩ | ⟨hmod, hsq, hres⟩)
    · exact Or.inl ⟨hsq, hmod⟩
    · exact Or.inr ⟨Δ / 4, hsq, hres,
        (Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hmod)).symm⟩
  · rintro (⟨hsq, hmod⟩ | ⟨D, hsq, hres, rfl⟩)
    · exact Or.inl ⟨hmod, hsq⟩
    · exact Or.inr (by simpa using And.intro hsq hres)

/-- A fundamental discriminant is congruent to `0` or `1` modulo `4`. -/
lemma IsFundamentalDiscriminant.emod_four {Δ : ℤ} (h : IsFundamentalDiscriminant Δ) :
    Δ % 4 = 0 ∨ Δ % 4 = 1 :=
  h.emod_four_eq_zero_or_one

end SIC
