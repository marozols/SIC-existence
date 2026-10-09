/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Quadratic.TowerValues
import Mathlib.NumberTheory.Real.Irrational

/-!
# Rank-One Quadratic Roots and Tower Levels

The radicand, roots, and exact level forced by a rank-one tower dimension.

This file isolates the quadratic arithmetic forced by a rank-one tower dimension in [AFK25]. If

`d = ε^j + ε^(-j) + 1`,

then `ε^j` is the larger root of `X² - (d - 1)X + 1`, its conjugate is the reciprocal root, and
the quadratic radicand is `(d + 1)(d - 3)`. These facts depend only on the rank-one dimension
equation, not on the principal binary quadratic form `Q_d`.

The final section connects a norm-one algebraic-integer unit realizing this root to the canonical
dimension tower. It is the field-independent step used by the concrete construction in
`SICs.Quadratic.RankOneFields`.

## Main definitions and results

- `RankOneDimension`: a natural dimension greater than three.
- `rankOneRadicand`: the integer `(d + 1)(d - 3)`.
- `rankOneRoot` and `rankOneConjugateRoot`: the two roots of `X² - (d - 1)X + 1`.
- `RealQuadraticUnitData.exists_rankOneLevel_of_rankOneUnit`: a norm-one unit realizing the
  larger root occurs at an exact rank-one tower level in dimension `d`.

## References

- [AFK25, Definition 1.22, `dfn:fundamentalTotallyPositiveUnit`] and [AFK25, Definition 1.23,
  `dfn:sequenceofconductors`] and [AFK25, Definition 1.24, `dfn:fjrjmdjm`]
- [AFK25, Definition 4.2, `dfn:discriminantLevelj`, equation (4.1)] and [AFK25, Lemma 4.3,
  `lem:towerbasic`, equations (4.4), `eq:towerbasic1`, and (4.5)]
- [AFK25, Theorem 3.20, `thm:dimtowunique`]
-/

noncomputable section

namespace SIC

/-! ### The rank-one quadratic

The radicand and roots below are determined by the trace equation for a rank-one tower level.
Their elementary identities are used both by the concrete fields of
`SICs.Quadratic.RankOneFields` and by the principal form specialization.
-/

/-- A dimension in the nondegenerate rank-one range. -/
abbrev RankOneDimension := {d : ℕ // 3 < d}

/-- A rank-one dimension `d > 3` is nonzero, so dimension-dependent constructions can use the
underlying natural number without a separate `NeZero` hypothesis. -/
instance RankOneDimension.instNeZero (d : RankOneDimension) : NeZero (d : ℕ) :=
  ⟨(lt_trans (by decide : 0 < 3) d.property).ne'⟩

/-- The radicand `(d + 1)(d - 3)` forced by the rank-one dimension equation. This is the
rank-one instance of [AFK25, Definition 4.2, `dfn:discriminantLevelj`, equation (4.1)]. -/
def rankOneRadicand (d : ℕ) : ℤ :=
  ((d : ℤ) + 1) * ((d : ℤ) - 3)

/-- The rank-one radicand is positive in every dimension `d > 3`. -/
lemma rankOneRadicand_pos (d : ℕ) (hd : 3 < d) : 0 < rankOneRadicand d := by
  have h1 : (0 : ℤ) < (d : ℤ) + 1 := by omega
  have h2 : (0 : ℤ) < (d : ℤ) - 3 := by omega
  exact mul_pos h1 h2

/-- The rank-one radicand is not a square in every dimension `d > 3`: it lies strictly between
the consecutive squares `(d - 2)²` and `(d - 1)²`. -/
lemma rankOneRadicand_not_square (d : ℕ) (hd : 3 < d) :
    ¬ IsSquare (rankOneRadicand d) := by
  intro ⟨r, hr⟩
  have hrr : r * r = (d : ℤ) ^ 2 - 2 * (d : ℤ) - 3 := by
    rw [rankOneRadicand] at hr
    nlinarith
  have hlo : ((d : ℤ) - 2) ^ 2 < r * r := by nlinarith
  have hhi : r * r < ((d : ℤ) - 1) ^ 2 := by nlinarith
  have hab1 : (d : ℤ) - 2 ≥ 0 := by omega
  have hab2 : |r| ≥ 0 := abs_nonneg r
  have h1 : (d : ℤ) - 2 < |r| := by
    nlinarith [sq_abs r]
  have h2 : |r| < (d : ℤ) - 1 := by
    nlinarith [sq_abs r, sq_abs ((d : ℤ) - 1)]
  omega

/-- The larger root `ρ_d = (d - 1 + √((d + 1)(d - 3))) / 2` of the rank-one quadratic. -/
def rankOneRoot (d : ℕ) : ℝ :=
  ((d : ℝ) - 1 + Real.sqrt (rankOneRadicand d)) / 2

/-- The conjugate root `ρ'_d = (d - 1 - √((d + 1)(d - 3))) / 2`. -/
def rankOneConjugateRoot (d : ℕ) : ℝ :=
  ((d : ℝ) - 1 - Real.sqrt (rankOneRadicand d)) / 2

/-- The larger rank-one root satisfies `ρ_d² - (d - 1)ρ_d + 1 = 0`. -/
lemma rankOneRoot_satisfies_quadratic (d : ℕ) (hd : 3 < d) :
    rankOneRoot d ^ 2 - ((d : ℝ) - 1) * rankOneRoot d + 1 = 0 := by
  have hdisc : (0 : ℝ) ≤ rankOneRadicand d := by
    exact_mod_cast (le_of_lt (rankOneRadicand_pos d hd))
  have hsqrt := Real.sq_sqrt hdisc
  rw [rankOneRoot]
  have hcast : (rankOneRadicand d : ℝ) = ((d : ℝ) + 1) * ((d : ℝ) - 3) := by
    simp [rankOneRadicand]
  rw [hcast] at hsqrt
  rw [hcast]
  nlinarith

/-- The larger rank-one root is strictly greater than one for `d > 3`. -/
lemma one_lt_rankOneRoot (d : ℕ) (hd : 3 < d) : 1 < rankOneRoot d := by
  have hdreal : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have hsqrt : 0 ≤ Real.sqrt (rankOneRadicand d) := Real.sqrt_nonneg _
  rw [rankOneRoot]
  nlinarith

/-- The two rank-one roots have sum `d - 1`. -/
lemma rankOneRoot_add_conjugate (d : ℕ) :
    rankOneRoot d + rankOneConjugateRoot d = (d : ℝ) - 1 := by
  simp [rankOneRoot, rankOneConjugateRoot]
  ring

/-- The two roots of the monic rank-one quadratic have product one. -/
lemma rankOneRoot_mul_conjugate (d : ℕ) (hd : 3 < d) :
    rankOneRoot d * rankOneConjugateRoot d = 1 := by
  have hquad := rankOneRoot_satisfies_quadratic d hd
  have hsum := rankOneRoot_add_conjugate d
  linear_combination -hquad + rankOneRoot d * hsum

/-- The conjugate rank-one root is the reciprocal of the larger root. -/
lemma rankOneConjugateRoot_eq_inv (d : ℕ) (hd : 3 < d) :
    rankOneConjugateRoot d = (rankOneRoot d)⁻¹ := by
  have hroot : rankOneRoot d ≠ 0 :=
    ne_of_gt (lt_trans Real.zero_lt_one (one_lt_rankOneRoot d hd))
  rw [inv_eq_one_div]
  apply (eq_div_iff hroot).2
  simpa [mul_comm] using rankOneRoot_mul_conjugate d hd

/-- The reciprocal identity `ρ_d⁻¹ = d - 1 - ρ_d`. -/
lemma inv_rankOneRoot (d : ℕ) (hd : 3 < d) :
    (rankOneRoot d)⁻¹ = (d : ℝ) - 1 - rankOneRoot d := by
  rw [← rankOneConjugateRoot_eq_inv d hd]
  simp [rankOneRoot, rankOneConjugateRoot]
  ring

/-- The larger rank-one root and its reciprocal have sum `d - 1`. -/
lemma rankOneRoot_add_inv (d : ℕ) (hd : 3 < d) :
    rankOneRoot d + (rankOneRoot d)⁻¹ = (d : ℝ) - 1 := by
  rw [inv_rankOneRoot d hd]
  ring

namespace RealQuadraticUnitData

/-! ### From a rank-one root unit to an exact tower level

A positive norm-one algebraic-integer unit is a positive power of the selected fundamental unit.
When its real value is `rankOneRoot d`, the root equation identifies the corresponding canonical
dimension with `d`.
-/

/-- If a norm-one algebraic-integer unit realizes `rankOneRoot d` at the selected real place,
then `d` is the canonical dimension at a positive tower index and the unit is the corresponding
power of `ε`.

This is the unit-group step in the forward direction of [AFK25, Theorem 3.20,
`thm:dimtowunique`]. -/
lemma exists_canonicalDimension_eq_of_rankOneUnit
    {d : ℕ} (hd : 3 < d) {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (T : RealQuadraticUnitData K)
    (u : (NumberField.RingOfIntegers K)ˣ)
    (hu_norm : Algebra.norm ℚ (u : K) = 1)
    (hu_root : realEmbeddingAt K T.place (u : K) = rankOneRoot d) :
    ∃ j : ℕ+, T.canonicalDimension j = d ∧ u = T.epsilon ^ (j : ℕ) := by
  have hu_one : 1 < realEmbeddingAt K T.place (u : K) := by
    rw [hu_root]
    exact one_lt_rankOneRoot d hd
  obtain ⟨j, hu⟩ := T.exists_eq_epsilon_pow u hu_norm hu_one
  have hroot : rankOneRoot d = T.epsilonReal ^ (j : ℕ) := by
    rw [← hu_root, hu, NumberField.Units.coe_pow, map_pow]
    rfl
  have hdim : T.IsDimensionTowerValue j d := by
    change (d : ℝ) = T.epsilonReal ^ (j : ℕ) +
      (T.epsilonReal ^ (j : ℕ))⁻¹ + 1
    rw [← hroot]
    linarith [rankOneRoot_add_inv d hd]
  exact ⟨j, (T.canonicalDimension_spec j).unique hdim, hu⟩

/-- A norm-one algebraic-integer realization of `rankOneRoot d` produces an exact rank-one level
in dimension `d`. -/
lemma exists_rankOneLevel_of_rankOneUnit
    {d : ℕ} (hd : 3 < d) {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (T : RealQuadraticUnitData K)
    (u : (NumberField.RingOfIntegers K)ˣ)
    (hu_norm : Algebra.norm ℚ (u : K) = 1)
    (hu_root : realEmbeddingAt K T.place (u : K) = rankOneRoot d) :
    ∃ L : T.RankOneLevel d, u = T.epsilon ^ (L.j : ℕ) := by
  obtain ⟨j, hj, hu⟩ :=
    T.exists_canonicalDimension_eq_of_rankOneUnit hd u hu_norm hu_root
  subst d
  exact ⟨T.canonicalRankOneLevel j, hu⟩

end RealQuadraticUnitData

end SIC

end
