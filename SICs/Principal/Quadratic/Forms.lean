/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Quadratic.Forms
import SICs.Quadratic.RankOne

/-!
# The Principal Quadratic Forms for Rank-One SICs

The forms `Q_d = ⟨1,1-d,1⟩`, admissibility, and the bridge to the general rank-one root.

This file isolates the explicit family of binary quadratic forms

`Q_d = ⟨1, 1 - d, 1⟩`

used by the principal-family shortcut to the rank-one case of [AFK25].  Its discriminant is the
radicand attached to the admissible pair `(d, 1)`, and its positive root has a particularly simple
quadratic equation.

The general rank-one layer defines the radicand and the two roots from the tower dimension alone.
This file defines `Q_d`, proves its admissibility and conductor facts, and supplies the bridge from
its abstract `rootPlus` to the general larger root. It does not assert that any explicit
stabilizer is the distinguished generator required by [AFK25, Definition 1.28,
`dfn:AssociatedStabilizers`].

## Main definitions

- `principalOneSICDiscriminant`: the integer `(d + 1)(d - 3)`.
- `principalOneSICForm`: the binary quadratic form `⟨1, 1 - d, 1⟩`.
- `isConductor_principalOneSICForm_of_tower`: the conditional conductor identification supplied
  by the rank-one tower discriminant identity.
- `principalRoot`: the principal alias of the general larger rank-one root.

## References

- [AFK25] Appleby, Flammia, Kopp, arXiv:2501.03970v2, Definitions 1.21 and 1.27
- [AFK25, Definition 4.2, `dfn:discriminantLevelj`, equation (4.1)] and [AFK25, Lemma 4.3,
  `lem:towerbasic`, equation (4.5)] for the discriminant identity motivating this family
-/

noncomputable section

namespace SIC

open BinaryQF

/-! ### The form and its discriminant

The principal form is `Q_d = ⟨1,1-d,1⟩`, with discriminant
`Δ_d = (d+1)(d-3)`. The basic lemmas establish positivity and nonsquareness in the range `d > 3`.
-/

/-- The discriminant `(d + 1)(d - 3)` of `Q_d`. It is the principal-form presentation of the
general `rankOneRadicand`; the expression remains explicit so principal polynomial proofs can
normalize it directly. -/
def principalOneSICDiscriminant (d : ℕ) : ℤ :=
  ((d : ℤ) + 1) * ((d : ℤ) - 3)

/-- The discriminant expression of `Q_d` is the general rank-one radicand. -/
@[simp]
lemma principalOneSICDiscriminant_eq_rankOneRadicand (d : ℕ) :
    principalOneSICDiscriminant d = rankOneRadicand d :=
  rfl

/-- The principal rank-one form `Q_d = ⟨1, 1 - d, 1⟩`. -/
def principalOneSICForm (d : ℕ) : BinaryQF :=
  ⟨1, 1 - (d : ℤ), 1⟩

/-- The discriminant of `Q_d` is `(d + 1)(d - 3)`. -/
@[simp]
lemma disc_principalOneSICForm (d : ℕ) :
    (principalOneSICForm d).disc = principalOneSICDiscriminant d := by
  simp [principalOneSICForm, principalOneSICDiscriminant, BinaryQF.disc, discrim]
  ring

/-- For `d > 3`, the principal rank-one form is primitive, irreducible, and indefinite. -/
lemma isAdmissible_principalOneSICForm (d : ℕ) (hd : d > 3) :
    (principalOneSICForm d).IsAdmissible :=
  isAdmissible_of_disc (by simp [principalOneSICForm, BinaryQF.IsPrimitive])
    (by
      rw [disc_principalOneSICForm, principalOneSICDiscriminant_eq_rankOneRadicand]
      exact rankOneRadicand_pos d hd)
    (by
      rw [disc_principalOneSICForm, principalOneSICDiscriminant_eq_rankOneRadicand]
      exact rankOneRadicand_not_square d hd)

/-! ### Conditional conductor bridge

The order conductor of `Q_d` is related to the quadratic field discriminant through
`Δ_d = f²Δ₀`. The lemma here isolates the hypotheses needed before the exact field model
supplies that equality.
-/

/-- If a positive integer `f_j` and positive fundamental discriminant `Δ₀` satisfy the
rank-one tower identity

`(d + 1)(d - 3) = f_j² Δ₀`,

then `f_j` is a form conductor of `Q_d`. In the rank-one tower, the identity is supplied by
`RealQuadraticUnitData.RankOneLevel.radicand_eq`. This lemma isolates the arithmetic
conversion to `BinaryQF.IsConductor`; it neither constructs nor associates the triple `(K,j,1)`. -/
lemma isConductor_principalOneSICForm_of_tower (d : ℕ) {Δ₀ : ℤ} {f_j : ℕ}
    (hfund : IsFundamentalDiscriminant Δ₀) (hΔ₀ : 0 < Δ₀) (hfj : 0 < f_j)
    (htower : principalOneSICDiscriminant d = (f_j : ℤ) ^ 2 * Δ₀) :
    (principalOneSICForm d).IsConductor Δ₀ f_j := by
  exact ⟨hfund, hΔ₀, hfj, by simpa using htower⟩

/-! ### Explicit roots

The larger real root `ρ_d` of `X²-(d-1)X+1` is the general rank-one root. Its quadratic,
positivity, inverse, and irrationality identities are used in the principal double-sine formulas.
-/

/-- The larger real root `ρ_d` of the principal form. Specializes `rankOneRoot`. -/
def principalRoot (d : ℕ) : ℝ :=
  rankOneRoot d

/-- The plus branch of the quadratic formula for `Q_d` agrees with its explicit principal-family
formula. -/
@[simp]
lemma rootPlus_principalOneSICForm (d : ℕ) :
    (principalOneSICForm d).rootPlus = principalRoot d := by
  simp only [BinaryQF.rootPlus]
  rw [disc_principalOneSICForm]
  simp [principalOneSICForm, principalRoot, rankOneRoot, principalOneSICDiscriminant,
    rankOneRadicand]

/-- The larger root `ρ_d` is irrational in every dimension `d > 3`. Specializes
`BinaryQF.IsAdmissible.rootPlus_irrational` to `Q_d`. -/
lemma principalRoot_irrational (d : ℕ) (hd : d > 3) : Irrational (principalRoot d) := by
  rw [← rootPlus_principalOneSICForm]
  exact BinaryQF.IsAdmissible.rootPlus_irrational (isAdmissible_principalOneSICForm d hd)

/-- The principal root satisfies `ρ_d² - (d - 1)ρ_d + 1 = 0`, by
`rankOneRoot_satisfies_quadratic`. -/
lemma principalRoot_satisfies_quadratic (d : ℕ) (hd : d > 3) :
    principalRoot d ^ 2 - ((d : ℝ) - 1) * principalRoot d + 1 = 0 := by
  simpa [principalRoot] using rankOneRoot_satisfies_quadratic d hd

/-- The complex embedding of `ρ_d` satisfies `ρ_d² - (d-1)ρ_d + 1 = 0`. -/
lemma ofReal_principalRoot_quadratic (d : ℕ) (hd : d > 3) :
    (principalRoot d : ℂ) ^ 2 - ((d : ℂ) - 1) * principalRoot d + 1 = 0 := by
  exact_mod_cast principalRoot_satisfies_quadratic d hd

/-- The principal root is strictly larger than one, by `one_lt_rankOneRoot`. -/
lemma one_lt_principalRoot (d : ℕ) (hd : d > 3) : 1 < principalRoot d := by
  simpa [principalRoot] using one_lt_rankOneRoot d hd

/-- The principal root is positive. -/
lemma principalRoot_pos (d : ℕ) (hd : 3 < d) : 0 < principalRoot d :=
  lt_trans zero_lt_one (one_lt_principalRoot d hd)

/-- The complex embedding of `ρ_d` is nonzero. -/
lemma ofReal_principalRoot_ne_zero (d : ℕ) (hd : 3 < d) :
    (principalRoot d : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (principalRoot_pos d hd))

/-- The complex embedding of `ρ_d` lies in the slit plane. -/
lemma ofReal_principalRoot_mem_slitPlane (d : ℕ) (hd : 3 < d) :
    (principalRoot d : ℂ) ∈ Complex.slitPlane :=
  Complex.ofReal_mem_slitPlane.mpr (principalRoot_pos d hd)

/-- The reciprocal identity `ρ_d⁻¹ = d - 1 - ρ_d` for the principal root. Specializes
`inv_rankOneRoot`. -/
lemma inv_principalRoot (d : ℕ) (hd : d > 3) :
    (principalRoot d)⁻¹ = (d : ℝ) - 1 - principalRoot d := by
  simpa [principalRoot] using inv_rankOneRoot d hd

/-- The complex reciprocal identity `ρ_d⁻¹ = d - 1 - ρ_d`. -/
lemma ofReal_principalRoot_inv (d : ℕ) (hd : d > 3) :
    (principalRoot d : ℂ)⁻¹ = (d : ℂ) - 1 - principalRoot d := by
  exact_mod_cast inv_principalRoot d hd

/-- The principal root and its reciprocal have sum `d - 1`, by `rankOneRoot_add_inv`. -/
lemma principalRoot_add_inv (d : ℕ) (hd : d > 3) :
    principalRoot d + (principalRoot d)⁻¹ = (d : ℝ) - 1 := by
  simpa [principalRoot] using rankOneRoot_add_inv d hd

/-- The complex identity `ρ_d + ρ_d⁻¹ = d - 1`. -/
lemma ofReal_principalRoot_add_inv (d : ℕ) (hd : d > 3) :
    (principalRoot d : ℂ) + (principalRoot d : ℂ)⁻¹ = (d : ℂ) - 1 := by
  exact_mod_cast principalRoot_add_inv d hd

end SIC

end
