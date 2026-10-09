/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Quadratic.TowerValues

/-!
# Rank and Dimension Grids

The two-index rank/dimension grids of Definition 1.24.

This file constructs the two-index rank grid `r_{j,m}` and dimension grid `d_{j,m}` of [AFK25,
Definition 1.24, `dfn:fjrjmdjm`] over the exact tower data of `SICs.Quadratic.Towers`, completing
the arbitrary-`m` half of what `SICs.Quadratic.TowerValues` builds at `m = 1`.

The paper defines `r_{j,m} = f_{jm}/f_j`, asserting without proof that the quotient is a positive
integer. That assertion is what needs formalizing here: the conductors `f_j` of
`RealQuadraticUnitData.canonicalConductor` are positive integers defined by the oriented real
equation

`f_j √Δ₀ = ε^j - ε^{-j}`,

so `f_{jm}/f_j` is a priori only a positive real. Writing `x = ε^j`, the quotient is the value at
`x` of the `m`-th Chebyshev-like polynomial

`(x^m - x^{-m}) / (x - x^{-1})`,

which satisfies the three-term recursion `g_{m+1} = (x + x^{-1}) g_m - g_{m-1}` with `g_0 = 0`
and `g_1 = 1`. Its coefficients are integral because `x + x^{-1} = Tr(ε^j) = d_j - 1` is an
integer. `rankGridInt` is that recursion, `rankGridInt_mul_epsilonSub` is the closed form it
solves, and `canonicalConductor_mul_eq` transports the closed form through the defining equation
of `f_j` to give the exact integral factorization `f_{jm} = f_j r_{j,m}`.

## Main definitions and results

- `RealQuadraticUnitData.rankGridInt`: the integral three-term recursion for `r_{j,m}`.
- `RealQuadraticUnitData.rankGridInt_mul_epsilonSub`: it solves `r (ε^j - ε^{-j}) = ε^{jm} -
  ε^{-jm}`.
- `RealQuadraticUnitData.rankGrid`: the positive integer `r_{j,m}`.
- `RealQuadraticUnitData.canonicalConductor_mul_eq`: `f_{jm} = f_j r_{j,m}`, so `r_{j,m}` is the
  quotient `f_{jm}/f_j` of [AFK25, Definition 1.24, `dfn:fjrjmdjm`].
- `RealQuadraticUnitData.dimensionGrid`: the natural number `d_{j,m} = r_{j,m+1} + r_{j,m}`.
- `RealQuadraticUnitData.dimensionGrid_one`: `d_{j,1} = d_j`, agreeing with the rank-one value
  `canonicalDimension` already constructed in `SICs.Quadratic.TowerValues`.
- `RealQuadraticUnitData.dimensionGrid_equation`: Theorem 4.20(A)(2),
  `(d_j + 1) r_{j,m} (d_{j,m} - r_{j,m}) = d_{j,m}² - 1`.
- `RealQuadraticUnitData.pow_two_mul_add_one_sub_one_eq_dimensionGrid_mul`: equation (4.90) of
  Lemma 4.23, `z^{2m+1} - 1 = d_{j,m} z^m (z - 1)` for every root `z` of
  `z² = (d_j - 1) z - 1` in a commutative ring.

## References

- [AFK25, Definition 1.23, `dfn:sequenceofconductors`, equation (1.37)]
- [AFK25, Definition 1.24, `dfn:fjrjmdjm`]
- [AFK25, Lemma 4.3, `lem:towerbasic`, equations (4.3)–(4.5)]
- [AFK25, Theorem 4.20, `thm:nrddjmrjm`]
- [AFK25, Lemma 4.23, `lem:dimgridtechres`]
-/

noncomputable section

namespace SIC

namespace RealQuadraticUnitData

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]

/-! ### The integral rank grid

The three-term integer recursion solves the quotient of unit differences
`(ε^{jm} - ε^{-jm}) / (ε^j - ε^{-j})`.  Its integral trace coefficient is what makes the rank grid
arithmetically meaningful. -/

/-- The integral three-term recursion computing `rankGrid`.

`rankGridInt T j m` is intended to be `r_{j,m} = f_{jm}/f_j`, and
`rankGridInt_mul_epsilonSub` proves that it is. The multiplier `dimensionInt j - 1` is
`Tr(ε^j) = ε^j + ε^{-j}`, which is what makes the recursion integral. -/
def rankGridInt (T : RealQuadraticUnitData K) (j : ℕ+) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (m + 2) =>
      (T.dimensionInt (j : ℕ) - 1) * T.rankGridInt j (m + 1) - T.rankGridInt j m

/-- The integral rank-grid recursion starts at `r_{j,0} = 0`. -/
@[simp]
lemma rankGridInt_zero (T : RealQuadraticUnitData K) (j : ℕ+) : T.rankGridInt j 0 = 0 :=
  rfl

/-- The first integral rank-grid value is `r_{j,1} = 1`. -/
@[simp]
lemma rankGridInt_one (T : RealQuadraticUnitData K) (j : ℕ+) : T.rankGridInt j 1 = 1 :=
  rfl

/-- The defining recursion of `rankGridInt`, as a rewriting lemma. -/
lemma rankGridInt_add_two (T : RealQuadraticUnitData K) (j : ℕ+) (m : ℕ) :
    T.rankGridInt j (m + 2) =
      (T.dimensionInt (j : ℕ) - 1) * T.rankGridInt j (m + 1) - T.rankGridInt j m :=
  rfl

/-- The trace multiplier of the recursion is `ε^j + ε^{-j}` at the selected real place. -/
private lemma dimensionInt_sub_one_cast (T : RealQuadraticUnitData K) (j : ℕ+) :
    ((T.dimensionInt (j : ℕ) - 1 : ℤ) : ℝ) =
      T.epsilonReal ^ (j : ℕ) + (T.epsilonReal ^ (j : ℕ))⁻¹ := by
  have h := T.dimensionInt_cast_eq_dimensionValue j
  rw [dimensionValue] at h
  push_cast
  rw [h]
  ring

/-- **The closed form solved by the integral recursion.** At the selected real place,
`r_{j,m} (ε^j - ε^{-j}) = ε^{jm} - ε^{-jm}`. -/
lemma rankGridInt_mul_epsilonSub (T : RealQuadraticUnitData K) (j : ℕ+) (m : ℕ) :
    (T.rankGridInt j m : ℝ) *
        (T.epsilonReal ^ (j : ℕ) - (T.epsilonReal ^ (j : ℕ))⁻¹) =
      (T.epsilonReal ^ (j : ℕ)) ^ m - ((T.epsilonReal ^ (j : ℕ)) ^ m)⁻¹ := by
  have hx : (0 : ℝ) < T.epsilonReal ^ (j : ℕ) := T.epsilonReal_pow_pos j
  have hxne : T.epsilonReal ^ (j : ℕ) ≠ 0 := ne_of_gt hx
  induction m using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more m ih1 ih2 =>
      have hs := T.dimensionInt_sub_one_cast j
      rw [rankGridInt_add_two, Int.cast_sub, Int.cast_mul, hs, sub_mul, mul_assoc, ih2, ih1]
      field_simp
      ring

/-! ### The positive rank grid `r_{j,m}`

Positivity of the unit difference turns the integral recursion into a positive natural number.
The conductor identity then proves that this number is exactly `f_{jm} / f_j` from [AFK25,
Definition 1.24, `dfn:fjrjmdjm`]. -/

/-- `ε^j - ε^{-j}` is positive at every positive index. -/
private lemma epsilonSub_pos (T : RealQuadraticUnitData K) (j : ℕ+) :
    0 < T.epsilonReal ^ (j : ℕ) - (T.epsilonReal ^ (j : ℕ))⁻¹ := by
  have hx : 1 < T.epsilonReal ^ (j : ℕ) := T.one_lt_epsilonReal_pow j
  have hinv : (T.epsilonReal ^ (j : ℕ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx
  linarith

/-- The integral rank-grid value is positive at every positive index `m`. -/
lemma rankGridInt_pos (T : RealQuadraticUnitData K) (j : ℕ+) {m : ℕ} (hm : 0 < m) :
    0 < T.rankGridInt j m := by
  have hx : 1 < T.epsilonReal ^ (j : ℕ) := T.one_lt_epsilonReal_pow j
  have hpow : 1 < (T.epsilonReal ^ (j : ℕ)) ^ m := one_lt_pow₀ hx hm.ne'
  have hinv : ((T.epsilonReal ^ (j : ℕ)) ^ m)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hpow
  have hspec := T.rankGridInt_mul_epsilonSub j m
  have hsub := T.epsilonSub_pos j
  have hreal : (0 : ℝ) < (T.rankGridInt j m : ℝ) := by nlinarith
  exact_mod_cast hreal

/-- The rank grid `r_{j,m}` of [AFK25, Definition 1.24, `dfn:fjrjmdjm`], as a positive integer.

Positivity and integrality are exactly the assertions the paper makes immediately after the
definition; `canonicalConductor_mul_eq` identifies this value with the paper's quotient
`f_{jm}/f_j`. -/
@[source "AFK25, Definition 1.24, p. 14, dfn:fjrjmdjm (rank grid)" (symbol := "r_{j,m}")]
def rankGrid (T : RealQuadraticUnitData K) (j m : ℕ+) : ℕ+ :=
  ⟨(T.rankGridInt j (m : ℕ)).toNat, by
    have h : 0 < T.rankGridInt j (m : ℕ) := T.rankGridInt_pos j m.property
    omega⟩

/-- The rank grid value, cast back to an integer, is the recursion value. -/
lemma rankGrid_coe_int (T : RealQuadraticUnitData K) (j m : ℕ+) :
    ((T.rankGrid j m : ℕ) : ℤ) = T.rankGridInt j (m : ℕ) := by
  have h : 0 < T.rankGridInt j (m : ℕ) := T.rankGridInt_pos j m.property
  change ((T.rankGridInt j (m : ℕ)).toNat : ℤ) = T.rankGridInt j (m : ℕ)
  omega

/-- **The exact integral factorization `f_{jm} = f_j r_{j,m}`.**

This proves the integrality assertion built into `rankGrid`: the conductor `f_j` divides `f_{jm}`
with quotient `r_{j,m}`. It is the factorization used by the bundled triple API. -/
theorem canonicalConductor_mul_eq (T : RealQuadraticUnitData K) (j m : ℕ+) :
    (T.canonicalConductor (j * m) : ℕ) =
      (T.canonicalConductor j : ℕ) * (T.rankGrid j m : ℕ) := by
  have hsqrt : 0 < Real.sqrt (NumberField.discr K) :=
    Real.sqrt_pos.2 (by exact_mod_cast T.discr_pos)
  have hj := T.canonicalConductor_spec j
  have hjm := T.canonicalConductor_spec (j * m)
  change ((T.canonicalConductor j : ℕ) : ℝ) * Real.sqrt (NumberField.discr K) =
    T.epsilonReal ^ (j : ℕ) - (T.epsilonReal ^ (j : ℕ))⁻¹ at hj
  change ((T.canonicalConductor (j * m) : ℕ) : ℝ) * Real.sqrt (NumberField.discr K) =
    T.epsilonReal ^ ((j * m : ℕ+) : ℕ) - (T.epsilonReal ^ ((j * m : ℕ+) : ℕ))⁻¹ at hjm
  have hpow : T.epsilonReal ^ ((j * m : ℕ+) : ℕ) = (T.epsilonReal ^ (j : ℕ)) ^ (m : ℕ) := by
    rw [← pow_mul]
    norm_cast
  have hgrid := T.rankGridInt_mul_epsilonSub j (m : ℕ)
  have hcast : ((T.rankGrid j m : ℕ) : ℝ) = (T.rankGridInt j (m : ℕ) : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ ↦ (z : ℝ)) (T.rankGrid_coe_int j m)
  have hreal : ((T.canonicalConductor (j * m) : ℕ) : ℝ) =
      ((T.canonicalConductor j : ℕ) : ℝ) * ((T.rankGrid j m : ℕ) : ℝ) := by
    apply mul_right_cancel₀ (ne_of_gt hsqrt)
    calc ((T.canonicalConductor (j * m) : ℕ) : ℝ) * Real.sqrt (NumberField.discr K)
        = (T.epsilonReal ^ (j : ℕ)) ^ (m : ℕ) - ((T.epsilonReal ^ (j : ℕ)) ^ (m : ℕ))⁻¹ := by
          rw [hjm, hpow]
      _ = (T.rankGridInt j (m : ℕ) : ℝ) *
            (T.epsilonReal ^ (j : ℕ) - (T.epsilonReal ^ (j : ℕ))⁻¹) := hgrid.symm
      _ = (T.rankGridInt j (m : ℕ) : ℝ) *
            (((T.canonicalConductor j : ℕ) : ℝ) * Real.sqrt (NumberField.discr K)) := by
          rw [hj]
      _ = ((T.canonicalConductor j : ℕ) : ℝ) * ((T.rankGrid j m : ℕ) : ℝ) *
            Real.sqrt (NumberField.discr K) := by
          rw [hcast]; ring
  exact_mod_cast hreal

/-- The conductor `f_j` divides `f_{jm}`. -/
theorem canonicalConductor_dvd (T : RealQuadraticUnitData K) (j m : ℕ+) :
    (T.canonicalConductor j : ℕ) ∣ (T.canonicalConductor (j * m) : ℕ) :=
  ⟨(T.rankGrid j m : ℕ), T.canonicalConductor_mul_eq j m⟩

/-- The rank grid starts at one: `r_{j,1} = 1`, so the tower `m = 1` is the rank-one row. -/
@[simp]
theorem rankGrid_one (T : RealQuadraticUnitData K) (j : ℕ+) : T.rankGrid j 1 = 1 := by
  have h : ((T.rankGrid j 1 : ℕ) : ℤ) = 1 := by
    rw [T.rankGrid_coe_int j 1]
    rfl
  apply Subtype.ext
  change (T.rankGrid j 1 : ℕ) = 1
  exact_mod_cast h

/-- The second rank-grid value is `d_j - 1`, the trace of `ε^j`. -/
theorem rankGrid_two (T : RealQuadraticUnitData K) (j : ℕ+) :
    ((T.rankGrid j 2 : ℕ) : ℤ) = T.dimensionInt (j : ℕ) - 1 := by
  rw [T.rankGrid_coe_int j 2]
  change T.rankGridInt j (0 + 2) = _
  rw [rankGridInt_add_two]
  simp

/-! ### The dimension grid `d_{j,m}`

Adjacent rank values define `d_{j,m} = r_{j,m+1} + r_{j,m}`.  Recurrence identities establish its
rank-one specialization and the arithmetic relations needed by admissible triples. -/

/-- The dimension grid `d_{j,m} = r_{j,m+1} + r_{j,m}` of [AFK25, Definition 1.24, `dfn:fjrjmdjm`].
-/
@[source "AFK25, Definition 1.24, p. 14, dfn:fjrjmdjm (dimension grid)" (symbol := "d_{j,m}")]
def dimensionGrid (T : RealQuadraticUnitData K) (j m : ℕ+) : ℕ :=
  (T.rankGrid j (m + 1) : ℕ) + (T.rankGrid j m : ℕ)

/-- The dimension grid is positive. -/
lemma dimensionGrid_pos (T : RealQuadraticUnitData K) (j m : ℕ+) : 0 < T.dimensionGrid j m := by
  have h : 0 < (T.rankGrid j m : ℕ) := (T.rankGrid j m).property
  unfold dimensionGrid
  omega

/-- **The dimension tower is the first column of the dimension grid:** `d_{j,1} = d_j`, the
rank-one value `canonicalDimension` constructed in `SICs.Quadratic.TowerValues`. -/
theorem dimensionGrid_one (T : RealQuadraticUnitData K) (j : ℕ+) :
    T.dimensionGrid j 1 = T.canonicalDimension j := by
  have hdim := T.canonicalDimension_coe_int j
  have htwo := T.rankGrid_two j
  have : ((T.dimensionGrid j 1 : ℕ) : ℤ) = (T.canonicalDimension j : ℤ) := by
    unfold dimensionGrid
    push_cast
    rw [show ((1 : ℕ+) + 1) = (2 : ℕ+) from rfl, htwo, hdim]
    simp
  exact_mod_cast this

/-- The Cassini identity for the rank-grid recurrence:
`r_{j,m+1}² + r_{j,m}² - (d_j - 1) r_{j,m+1} r_{j,m} = 1`.

This is the elementary recurrence identity behind the admissible-pair equation for every row of
the rank and dimension grids. -/
theorem rankGridInt_cassini (T : RealQuadraticUnitData K) (j : ℕ+) (m : ℕ) :
    T.rankGridInt j (m + 1) ^ 2 + T.rankGridInt j m ^ 2 -
        (T.dimensionInt (j : ℕ) - 1) * T.rankGridInt j (m + 1) *
          T.rankGridInt j m = 1 := by
  induction m with
  | zero => simp [rankGridInt]
  | succ m ih =>
      rw [rankGridInt_add_two]
      ring_nf at ih ⊢
      linear_combination ih

/-- **[AFK25, Theorem 4.20(A), `thm:nrddjmrjm`, clause (2)].** The rank and dimension grids satisfy
`(d_j + 1) r_{j,m} (d_{j,m} - r_{j,m}) = d_{j,m}² - 1`.

This is the arithmetic bridge from the tower grids to the defining equation of `AdmissiblePair`;
the association layer then identifies the pair's integer `n` with `d_j + 1`. -/
@[source "AFK25, Theorem 4.20, p. 56, thm:nrddjmrjm (A)(2)"]
theorem dimensionGrid_equation (T : RealQuadraticUnitData K) (j m : ℕ+) :
    (T.canonicalDimension j + 1) * (T.rankGrid j m : ℕ) *
        (T.dimensionGrid j m - (T.rankGrid j m : ℕ)) =
      (T.dimensionGrid j m) ^ 2 - 1 := by
  have hcassini := T.rankGridInt_cassini j (m : ℕ)
  have hdim : (T.canonicalDimension j : ℤ) = T.dimensionInt (j : ℕ) :=
    Int.toNat_of_nonneg (le_of_lt (lt_trans (by norm_num) (T.dimensionInt_gt_three j)))
  have hr := T.rankGrid_coe_int j m
  have hrnext := T.rankGrid_coe_int j (m + 1)
  have hmnext : ((m + 1 : ℕ+) : ℕ) = (m : ℕ) + 1 := rfl
  have heq :
      ((T.canonicalDimension j + 1 : ℕ) : ℤ) * ((T.rankGrid j m : ℕ) : ℤ) *
          ((T.rankGrid j (m + 1) : ℕ) : ℤ) =
        (((T.rankGrid j (m + 1) : ℕ) : ℤ) + ((T.rankGrid j m : ℕ) : ℤ)) ^ 2 - 1 := by
    push_cast
    rw [hdim, hr, hrnext, hmnext]
    nlinarith [hcassini]
  unfold dimensionGrid
  rw [Nat.add_sub_cancel_right]
  have hsq : 1 ≤ ((T.rankGrid j (m + 1) : ℕ) + (T.rankGrid j m : ℕ)) ^ 2 := by
    exact Nat.one_le_pow _ _ (by positivity)
  zify [hsq]
  exact heq

/-! ### Monotonicity

The coefficient `d_j - 1` in the rank recursion is at least three.  Consequently each rank value
is strictly larger than its predecessor.
-/

/-- Consecutive integral rank-grid values strictly increase: `r_{j,m} < r_{j,m+1}`.

This is the rank half of [AFK25, Proposition 4.19, `prop:rjmdjmord`]. The proof uses the
three-term recursion and `d_j ≥ 4`, rather than the hyperbolic closed form used in the source. -/
theorem rankGridInt_lt_succ (T : RealQuadraticUnitData K) (j : ℕ+) (m : ℕ) :
    T.rankGridInt j m < T.rankGridInt j (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hpos : 0 < T.rankGridInt j (m + 1) := T.rankGridInt_pos j (by omega)
      have hcoef : (2 : ℤ) ≤ T.dimensionInt (j : ℕ) - 2 := by
        have := T.dimensionInt_gt_three j
        omega
      have hmul : 2 * T.rankGridInt j (m + 1) ≤
          (T.dimensionInt (j : ℕ) - 2) * T.rankGridInt j (m + 1) :=
        Int.mul_le_mul_of_nonneg_right hcoef hpos.le
      rw [show m + 1 + 1 = m + 2 by omega, T.rankGridInt_add_two j m]
      nlinarith

/-! ### Closed forms at neighbouring indices

The converse direction of Theorem 4.20 compares the trace and oriented unit difference at a
multiple `jm` with the two neighbours of `r_{j,m}`.  The following two recurrence forms isolate
exactly those comparisons.
-/

/-- For `x = ε^j` and positive `m`,
`(x + x⁻¹) r_{j,m} = r_{j,m+1} + r_{j,m-1}`. -/
lemma epsilonAddInv_mul_rankGridInt (T : RealQuadraticUnitData K) (j m : ℕ+) :
    (T.epsilonReal ^ (j : ℕ) + (T.epsilonReal ^ (j : ℕ))⁻¹) *
        (T.rankGridInt j (m : ℕ) : ℝ) =
      (T.rankGridInt j ((m : ℕ) + 1) : ℝ) +
        (T.rankGridInt j ((m : ℕ) - 1) : ℝ) := by
  have hm : (m : ℕ) - 1 + 1 = (m : ℕ) := Nat.sub_add_cancel m.property
  have hrec := congrArg (fun z : ℤ ↦ (z : ℝ))
    (T.rankGridInt_add_two j ((m : ℕ) - 1))
  push_cast at hrec
  have hmnext : (m : ℕ) - 1 + 2 = (m : ℕ) + 1 := by omega
  rw [hm, hmnext] at hrec
  rw [← T.dimensionInt_sub_one_cast j]
  push_cast
  nlinarith

/-- For `x = ε^j` and positive `m`,
`x^m + x⁻ᵐ = r_{j,m+1} - r_{j,m-1}`.

This is the neighbouring-index companion to `rankGridInt_mul_epsilonSub`; multiplying by the
positive factor `x - x⁻¹` reduces it to that closed form at `m+1` and `m-1`. -/
lemma epsilonPow_add_inv_eq_rankGridInt_sub (T : RealQuadraticUnitData K) (j m : ℕ+) :
    (T.epsilonReal ^ (j : ℕ)) ^ (m : ℕ) +
        ((T.epsilonReal ^ (j : ℕ)) ^ (m : ℕ))⁻¹ =
      (T.rankGridInt j ((m : ℕ) + 1) : ℝ) -
        (T.rankGridInt j ((m : ℕ) - 1) : ℝ) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (m : ℕ) = k + 1 :=
    ⟨(m : ℕ) - 1, by symm; exact Nat.sub_add_cancel m.property⟩
  have hx : T.epsilonReal ^ (j : ℕ) ≠ 0 := ne_of_gt (T.epsilonReal_pow_pos j)
  have hsub : T.epsilonReal ^ (j : ℕ) - (T.epsilonReal ^ (j : ℕ))⁻¹ ≠ 0 :=
    ne_of_gt (T.epsilonSub_pos j)
  apply mul_right_cancel₀ hsub
  rw [sub_mul, T.rankGridInt_mul_epsilonSub j ((m : ℕ) + 1),
    T.rankGridInt_mul_epsilonSub j ((m : ℕ) - 1)]
  rw [hk]
  simp only [Nat.add_sub_cancel]
  field_simp [hx, pow_succ]
  ring

/-! ### Index-doubling identities

The rank recursion has unit determinant, so it satisfies the classical addition formula

`r_{j,a+b+1} = r_{j,a+1} r_{j,b+1} - r_{j,a} r_{j,b}`,

proved below by induction on `b`.  Its diagonal `a = b = m` is the clause
`r_{j,2m+1} = r²_{j,m+1} - r²_{j,m}` of [AFK25, Lemma 4.23, `lem:dimgridtechres`], which factors
through `d_{j,m} = r_{j,m+1} + r_{j,m}` as `r_{j,2m+1} = (r_{j,m+1} - r_{j,m}) d_{j,m}`.  The
neighbouring instance `a = m`, `b = m - 1` evaluates `r_{j,2m}`, and the two together with the
Cassini relation give `rankGridInt_scalar_part`.  These are the grid input to the closed form of
the associated level generator `A_t`, where the doubled index `2m + 1` is the exponent
`A_t = L_{z,t}^{2m+1}`.
-/

/-- The addition formula for the rank recursion:
`r_{j,a+b+1} = r_{j,a+1} r_{j,b+1} - r_{j,a} r_{j,b}`.

This is the standard addition identity for a three-term recursion of unit determinant. It is not
stated in [AFK25]; it is the tool used here for the index-doubling clause of [AFK25, Lemma 4.23,
`lem:dimgridtechres`] and for `rankGridInt_scalar_part`. -/
theorem rankGridInt_add_add_one (T : RealQuadraticUnitData K) (j : ℕ+) (a b : ℕ) :
    T.rankGridInt j (a + b + 1) =
      T.rankGridInt j (a + 1) * T.rankGridInt j (b + 1) -
        T.rankGridInt j a * T.rankGridInt j b := by
  induction b using Nat.twoStepInduction with
  | zero => simp
  | one =>
      have h2 : T.rankGridInt j 2 = T.dimensionInt (j : ℕ) - 1 := by
        rw [show (2 : ℕ) = 0 + 2 from rfl, rankGridInt_add_two]
        simp
      rw [show a + 1 + 1 = a + 2 from rfl, rankGridInt_add_two, h2, rankGridInt_one]
      ring
  | more b ih1 ih2 =>
      rw [show a + (b + 2) + 1 = a + b + 1 + 2 by omega,
        T.rankGridInt_add_two j (a + b + 1), show a + b + 1 + 1 = a + (b + 1) + 1 by omega,
        ih2, ih1, T.rankGridInt_add_two j (b + 1), T.rankGridInt_add_two j b]
      ring

/-- **[AFK25, Lemma 4.23, `lem:dimgridtechres`], the index-doubling clause.**
`r_{j,2m+1} = r²_{j,m+1} - r²_{j,m}`.

The source proves it from the hyperbolic closed form of [AFK25, Proposition 4.18,
`prop:rdtrmstheta`]; here it is the diagonal of `rankGridInt_add_add_one`. -/
@[source "AFK25, Lemma 4.23, p. 58, lem:dimgridtechres (index doubling)"]
theorem rankGridInt_two_mul_add_one (T : RealQuadraticUnitData K) (j : ℕ+) (m : ℕ) :
    T.rankGridInt j (2 * m + 1) =
      T.rankGridInt j (m + 1) ^ 2 - T.rankGridInt j m ^ 2 := by
  rw [show 2 * m + 1 = m + m + 1 by ring, T.rankGridInt_add_add_one j m m]
  ring

/-- The dimension grid, as an integer, is the sum of the two adjacent rank values. -/
lemma dimensionGrid_coe_int (T : RealQuadraticUnitData K) (j m : ℕ+) :
    ((T.dimensionGrid j m : ℕ) : ℤ) =
      T.rankGridInt j ((m : ℕ) + 1) + T.rankGridInt j (m : ℕ) := by
  unfold dimensionGrid
  push_cast
  rw [T.rankGrid_coe_int j (m + 1), T.rankGrid_coe_int j m]
  rfl

/-- The factored form of the index-doubling clause,
`r_{j,2m+1} = (r_{j,m+1} - r_{j,m}) d_{j,m}`, as used in the proof of [AFK25, Lemma 5.5,
`lem:drafjfqp`]. -/
theorem rankGridInt_two_mul_add_one_eq_mul_dimensionGrid (T : RealQuadraticUnitData K)
    (j m : ℕ+) :
    T.rankGridInt j (2 * (m : ℕ) + 1) =
      (T.rankGridInt j ((m : ℕ) + 1) - T.rankGridInt j (m : ℕ)) *
        (T.dimensionGrid j m : ℤ) := by
  rw [T.rankGridInt_two_mul_add_one j (m : ℕ), T.dimensionGrid_coe_int j m]
  ring

/-- The even-index companion to the factored doubling identity:
`r_{j,2m} + 1 = d_{j,m}(r_{j,m} - r_{j,m-1})`. It supplies the scalar coefficient in
`IsAssociatedStabilizerPair.A_sub_one_eq`. -/
theorem rankGridInt_even_add_one_eq (T : RealQuadraticUnitData K)
    (j m : ℕ+) :
    T.rankGridInt j (2 * (m : ℕ)) + 1 =
      (T.dimensionGrid j m : ℤ) *
        (T.rankGridInt j (m : ℕ) - T.rankGridInt j ((m : ℕ) - 1)) := by
  let k := (m : ℕ) - 1
  have hk : (m : ℕ) = k + 1 := by
    dsimp [k]
    exact (Nat.sub_add_cancel m.property).symm
  have hadd := T.rankGridInt_add_add_one j (k + 1) k
  rw [show k + 1 + k + 1 = 2 * (m : ℕ) by omega] at hadd
  have hcas := T.rankGridInt_cassini j k
  have hrec := T.rankGridInt_add_two j k
  rw [T.dimensionGrid_coe_int j m]
  change T.rankGridInt j (2 * (m : ℕ)) + 1 =
      (T.rankGridInt j ((m : ℕ) + 1) + T.rankGridInt j (m : ℕ)) *
      (T.rankGridInt j (m : ℕ) - T.rankGridInt j ((m : ℕ) - 1))
  rw [hadd, hk]
  simp only [Nat.add_sub_cancel]
  linear_combination T.rankGridInt j k * hrec - hcas

/-- The preceding rank-grid value satisfies
`r_{j,m-1} = d_j r_{j,m} - d_{j,m}`. This is the recursion in the form used by
`IsAssociatedStabilizerPair.Lz_pow_m_succ_eq`. -/
theorem rankGridInt_prev_eq (T : RealQuadraticUnitData K) (j m : ℕ+) :
    T.rankGridInt j ((m : ℕ) - 1) =
      T.dimensionInt (j : ℕ) * T.rankGridInt j (m : ℕ) -
        (T.dimensionGrid j m : ℤ) := by
  have hrec := T.rankGridInt_add_two j ((m : ℕ) - 1)
  have hm : 0 < (m : ℕ) := m.property
  have hidx : ((m : ℕ) - 1) + 1 = (m : ℕ) := by omega
  have hidx' : ((m : ℕ) - 1) + 2 = (m : ℕ) + 1 := by omega
  rw [hidx, hidx'] at hrec
  rw [T.dimensionGrid_coe_int j m]
  linear_combination hrec

/-- The shifted-index form of `rankGridInt_scalar_part`, where `m = k + 1` makes the neighbour
`r_{j,m-1} = r_{j,k}` available to the addition formula. -/
private lemma rankGridInt_scalar_part_aux (T : RealQuadraticUnitData K) (j : ℕ+) (k : ℕ) :
    (T.dimensionInt (j : ℕ) - 1) * T.rankGridInt j (2 * (k + 1) + 1) -
        2 * T.rankGridInt j (2 * (k + 1)) - 2 =
      (T.rankGridInt j (k + 2) + T.rankGridInt j (k + 1)) ^ 2 *
        (T.dimensionInt (j : ℕ) - 3) := by
  have hodd : T.rankGridInt j (2 * (k + 1) + 1) =
      T.rankGridInt j (k + 2) ^ 2 - T.rankGridInt j (k + 1) ^ 2 :=
    T.rankGridInt_two_mul_add_one j (k + 1)
  have heven : T.rankGridInt j (2 * (k + 1)) =
      T.rankGridInt j (k + 2) * T.rankGridInt j (k + 1) -
        T.rankGridInt j (k + 1) * T.rankGridInt j k := by
    have h := T.rankGridInt_add_add_one j (k + 1) k
    rwa [show k + 1 + k + 1 = 2 * (k + 1) by omega] at h
  have hstep := T.rankGridInt_add_two j k
  have hcassini : T.rankGridInt j (k + 2) ^ 2 + T.rankGridInt j (k + 1) ^ 2 -
      (T.dimensionInt (j : ℕ) - 1) * T.rankGridInt j (k + 2) * T.rankGridInt j (k + 1) = 1 :=
    T.rankGridInt_cassini j (k + 1)
  rw [hodd, heven]
  linear_combination (2 : ℤ) * hcassini + 2 * T.rankGridInt j (k + 1) * hstep

/-- The scalar identity behind [AFK25, equation (5.26), `eq:amidjmh`, in the proof of
Lemma 5.5, `lem:drafjfqp`]:

`(d_j - 1) r_{j,2m+1} - 2 r_{j,2m} - 2 = d²_{j,m} (d_j - 3)`.

The left-hand side is the trace of `A_t - I`, read off the recursion. The source instead obtains
it as `d_{j(2m+1)} - 3`, from the canonical representation of `ε^{j(2m+1)}`, and evaluates that by
the hyperbolic identities of [AFK25, Proposition 4.18, `prop:rdtrmstheta`]; the proof here uses
the addition formula and the Cassini relation `rankGridInt_cassini` instead, so it needs no
analytic input. -/
theorem rankGridInt_scalar_part (T : RealQuadraticUnitData K) (j m : ℕ+) :
    (T.dimensionInt (j : ℕ) - 1) * T.rankGridInt j (2 * (m : ℕ) + 1) -
        2 * T.rankGridInt j (2 * (m : ℕ)) - 2 =
      (T.dimensionGrid j m : ℤ) ^ 2 * (T.dimensionInt (j : ℕ) - 3) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (m : ℕ) = k + 1 := ⟨(m : ℕ) - 1, by have := m.pos; omega⟩
  rw [T.dimensionGrid_coe_int j m, hk]
  exact T.rankGridInt_scalar_part_aux j k

/-! ### Parities

Reducing the recursion modulo two makes it depend only on the parity of `d_j`.  If `d_j` is odd
the multiplier `d_j - 1` is even and the recursion becomes `r_{m+2} ≡ r_m`, so the residues
alternate, and adding adjacent values makes every `d_{j,m}` odd.  These are the odd-`d_j` parity
clauses of [AFK25, Lemma 4.23, `lem:dimgridtechres`], which the sign analysis of
[AFK25, Lemma 5.5, `lem:drafjfqp`] needs.
-/

/-- The rank recursion modulo two when `d_j` is odd: `r_{m+2} ≡ r_m`. -/
private lemma two_dvd_rankGridInt_sub (T : RealQuadraticUnitData K) (j : ℕ+)
    (hj : (2 : ℤ) ∣ T.dimensionInt (j : ℕ) - 1) (k : ℕ) :
    (2 : ℤ) ∣ T.rankGridInt j (k + 2) - T.rankGridInt j k := by
  obtain ⟨c, hc⟩ := hj
  refine ⟨c * T.rankGridInt j (k + 1) - T.rankGridInt j k, ?_⟩
  rw [rankGridInt_add_two, hc]
  ring

/-- **[AFK25, Lemma 4.23, `lem:dimgridtechres`], the rank parity for odd `d_j`.**
`r_{j,m}` is odd exactly when `m` is odd. -/
@[source "AFK25, Lemma 4.23, p. 58, lem:dimgridtechres (odd d_j, ranks)"]
theorem rankGridInt_emod_two_of_two_dvd_sub_one (T : RealQuadraticUnitData K) (j : ℕ+)
    (hj : (2 : ℤ) ∣ T.dimensionInt (j : ℕ) - 1) (m : ℕ) :
    T.rankGridInt j m % 2 = (m : ℤ) % 2 := by
  induction m using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more m ih1 _ =>
      have hd := T.two_dvd_rankGridInt_sub j hj m
      have hm : ((m + 2 : ℕ) : ℤ) = (m : ℤ) + 2 := by push_cast; ring
      omega

/-- **[AFK25, Lemma 4.23, `lem:dimgridtechres`], the dimension parity for odd `d_j`.**
`d_{j,m}` is odd for every `m`. -/
@[source "AFK25, Lemma 4.23, p. 58, lem:dimgridtechres (odd d_j, dimensions)"]
theorem dimensionGrid_emod_two_of_two_dvd_sub_one (T : RealQuadraticUnitData K) (j m : ℕ+)
    (hj : (2 : ℤ) ∣ T.dimensionInt (j : ℕ) - 1) :
    ((T.dimensionGrid j m : ℕ) : ℤ) % 2 = 1 := by
  rw [T.dimensionGrid_coe_int j m]
  have h1 := T.rankGridInt_emod_two_of_two_dvd_sub_one j hj ((m : ℕ) + 1)
  have h0 := T.rankGridInt_emod_two_of_two_dvd_sub_one j hj (m : ℕ)
  have hm : (((m : ℕ) + 1 : ℕ) : ℤ) = ((m : ℕ) : ℤ) + 1 := by push_cast; ring
  omega

/-! ### The power identity in a commutative ring

Let `z` be an element of a commutative ring with `z² = (d_j - 1) z - 1`, the characteristic
equation of `ε^j` (its trace is `d_j - 1` and its norm `1`) and hence of every image of `ε^j`
under a ring homomorphism, such as its canonical representation. Then the powers of `z` are
the rank-grid combinations `z^{n+1} = r_{j,n+1} z - r_{j,n}`, and consequently

`z^{2m+1} - 1 = d_{j,m} z^m (z - 1)`,

which is [AFK25, Lemma 4.23, `lem:dimgridtechres`, equation (4.90), `eq:epowerminusone`] read for
any such `z`. The source proves it from the hyperbolic closed forms of [AFK25, Proposition 4.18,
`prop:rdtrmstheta`]; here it follows from the index-doubling identity, the addition formula and
the Cassini identity, so it holds verbatim in the order and in the matrix ring. -/

/-- Powers of a root of `z² = (d_j - 1) z - 1` in terms of the rank grid:
`z^{n+1} = r_{j,n+1} z - r_{j,n}`. This is the commutative-ring form of
`SL2Z.pow_succ_eq_smul_sub_smul`; it feeds `pow_two_mul_add_one_sub_one_eq_dimensionGrid_mul`. -/
lemma pow_succ_eq_rankGridInt_mul_sub {R : Type*} [CommRing R] (T : RealQuadraticUnitData K)
    (j : ℕ+) {z : R} (hz : z ^ 2 = ((T.dimensionInt (j : ℕ) - 1 : ℤ) : R) * z - 1) (n : ℕ) :
    z ^ (n + 1) = (T.rankGridInt j (n + 1) : R) * z - (T.rankGridInt j n : R) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, T.rankGridInt_add_two j n]
      push_cast at hz ⊢
      linear_combination (T.rankGridInt j (n + 1) : R) * hz

/-- **[AFK25, Lemma 4.23, `lem:dimgridtechres`, equation (4.90), `eq:epowerminusone`]** for a root
`z` of `z² = (d_j - 1) z - 1` in a commutative ring: `z^{2m+1} - 1 = d_{j,m} z^m (z - 1)`. -/
@[source "AFK25, Lemma 4.23, p. 58, lem:dimgridtechres (equation (4.90))"]
theorem pow_two_mul_add_one_sub_one_eq_dimensionGrid_mul {R : Type*} [CommRing R]
    (T : RealQuadraticUnitData K) (j : ℕ+) {z : R}
    (hz : z ^ 2 = ((T.dimensionInt (j : ℕ) - 1 : ℤ) : R) * z - 1) (m : ℕ+) :
    z ^ (2 * (m : ℕ) + 1) - 1 =
      ((T.dimensionGrid j m : ℕ) : R) * (z ^ (m : ℕ) * (z - 1)) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (m : ℕ) = k + 1 := ⟨(m : ℕ) - 1, by have := m.pos; omega⟩
  have hodd := T.pow_succ_eq_rankGridInt_mul_sub j hz (2 * (m : ℕ))
  have hm := T.pow_succ_eq_rankGridInt_mul_sub j hz k
  have hcoef1 := T.rankGridInt_two_mul_add_one_eq_mul_dimensionGrid j m
  -- `r_{j,2m} + 1 = d_{j,m} (r_{j,m} - r_{j,m-1})`, from the addition formula and Cassini.
  have hcoef2 : T.rankGridInt j (2 * (m : ℕ)) + 1 =
      (T.dimensionGrid j m : ℤ) * (T.rankGridInt j (k + 1) - T.rankGridInt j k) := by
    have hadd := T.rankGridInt_add_add_one j (k + 1) k
    rw [show k + 1 + k + 1 = 2 * (m : ℕ) by omega] at hadd
    have hcas := T.rankGridInt_cassini j k
    have hrec := T.rankGridInt_add_two j k
    rw [T.dimensionGrid_coe_int j m, hadd, hk]
    linear_combination T.rankGridInt j k * hrec - hcas
  have hc1 := congrArg (Int.cast : ℤ → R) hcoef1
  have hc2 := congrArg (Int.cast : ℤ → R) hcoef2
  have hr := congrArg (Int.cast : ℤ → R) (T.rankGridInt_add_two j k)
  push_cast at hc1 hc2 hr hz
  rw [hk] at hc1 hc2 hodd ⊢
  rw [hodd, hm]
  linear_combination z * hc1 - hc2 -
    ((T.dimensionGrid j m : ℕ) : R) * (T.rankGridInt j (k + 1) : R) * hz +
    ((T.dimensionGrid j m : ℕ) : R) * z * hr

end RealQuadraticUnitData

end SIC

end
