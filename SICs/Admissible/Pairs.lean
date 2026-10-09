/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify
import SICs.Source

/-!
# Admissible Pairs

Bundled admissible pairs `(d,r)` with computed `n`.

This file formalizes the geometric side of the dictionary between the geometric and
number-theoretic descriptions of the r-SIC problem. Faithful rank-one triples and tuples are in
`SICs.Admissible.RankOne`; faithful arbitrary-rank triples, their association with pairs, and
admissible tuples are in `SICs.Admissible.Triples`.

## Geometric side

An admissible pair (d,r) satisfies:

- 0 < r < (d-1)/2
- ∃ n > 4: n·r·(d-r) = d²-1

Lean bundles the pair and its conditions in `AdmissiblePair`. Its projection-like `n` is the
computable quotient `(d²-1)/(r(d-r))`; `AdmissiblePair.ofN` proves equivalence with the displayed
existential-witness presentation.

The section "Arithmetic consequences of the defining equation" collects what the Diophantine
equation alone gives: `r < d`, `d > 3`, the equation over `ℤ`, coprimality of `d` with `r` and with
`n`, and the resulting parity facts in even dimensions. Under
[AFK25, Theorem 4.20(B), `thm:nrddjmrjm`] one has `n = d_j + 1`, so these are the paper's
statements about `d_{j,m}`, `r_{j,m}`, and `d_j + 1`; `SICs.Ghost.TwistFunctions` continues them
modulo `d̄`.

The associated field is K = ℚ(√(n(n-4))).

## Pair/triple bijection

[AFK25, Theorem 1.25, `thm:bijectionofadmissibletuples`] gives a bijection between admissible pairs
and admissible triples. `SICs.Admissible.PairTriple` proves that every admissible pair comes from
a triple. Tuples retain a bundled admissible pair and its association proof as their data
interface.

## References

- [AFK25] Appleby, Flammia, Kopp, arXiv:2501.03970v2, Definition 1.21, Theorems 1.25 and
  4.20, Corollary 4.22, and Lemma 4.25
-/

noncomputable section

namespace SIC

/-! ### Admissible pairs

The bundled geometric data store `(d, r)` and the exact Diophantine equation, while defining its
integer `n` canonically as a quotient.  The explicit-witness constructor proves equivalence with
[AFK25, Definition 1.21, `dfn:admissiblePair`]. -/

/-- A bundled admissible pair `(d,r)` from [AFK25, Definition 1.21, `dfn:admissiblePair`].

The integer called `n` in the paper is deliberately not stored: `AdmissiblePair.n` computes its
unique value as `(d² - 1) / (r(d-r))`. The final field asserts exact divisibility, making this
equivalent to the paper's existence of an integer `n > 4` satisfying
`n r (d-r) = d² - 1`, while preventing redundant representations with different `n` data. -/
@[source "AFK25, Definition 1.21, p. 13, dfn:admissiblePair" (symbol := "(d,r)")]
structure AdmissiblePair where
  /-- Ambient dimension. -/
  d : ℕ
  /-- Projector rank. -/
  r : ℕ
  /-- The rank is positive. -/
  rank_pos : 0 < r
  /-- The rank is strictly less than `(d-1)/2`. -/
  rank_lt : 2 * r < d - 1
  /-- The integer computed from `d` and `r` is greater than four. -/
  n_gt_four :
    let n := (d ^ 2 - 1) / (r * (d - r))
    4 < n
  /-- The computed integer satisfies the defining Diophantine equation. -/
  equation :
    let n := (d ^ 2 - 1) / (r * (d - r))
    n * r * (d - r) = d ^ 2 - 1

namespace AdmissiblePair

/-- The canonical integer `n = (d² - 1)/(r(d-r))` attached to an admissible pair.

The structure fields show that this value exceeds four and satisfies
`n r (d-r) = d² - 1`; `n_unique` records that the defining equation determines it uniquely. -/
def n (p : AdmissiblePair) : ℕ :=
  (p.d ^ 2 - 1) / (p.r * (p.d - p.r))

/-- Construct an `AdmissiblePair` from an explicit integer `n > 4` satisfying
`n r (d-r) = d² - 1`, together with the rank bounds. -/
def ofN (d r n : ℕ) (hr : 0 < r) (hbound : 2 * r < d - 1)
    (hn4 : 4 < n) (hn : n * r * (d - r) = d ^ 2 - 1) : AdmissiblePair := by
  have hdr : 0 < d - r := by omega
  have hdenominator : 0 < r * (d - r) := Nat.mul_pos hr hdr
  have hn_eq : (d ^ 2 - 1) / (r * (d - r)) = n := by
    apply Nat.div_eq_of_eq_mul_left hdenominator
    simpa only [Nat.mul_assoc] using hn.symm
  refine ⟨d, r, hr, hbound, ?_, ?_⟩
  · simpa only [hn_eq] using hn4
  · simpa only [hn_eq] using hn

/-- Any natural number satisfying the defining equation of `p` equals its canonical value `p.n`. -/
lemma n_unique (p : AdmissiblePair) (m : ℕ)
    (hm : m * p.r * (p.d - p.r) = p.d ^ 2 - 1) : m = p.n := by
  have hbound := p.rank_lt
  have hdr : 0 < p.d - p.r := by omega
  apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos p.rank_pos hdr)
  simpa only [n, Nat.mul_assoc] using hm.trans p.equation.symm

/-! #### Arithmetic consequences of the defining equation

The results below are the parts of [AFK25, Theorem 4.20, `thm:nrddjmrjm`, Corollary 4.22,
`cor:djmcprjm`, and Lemma 4.25, `lem:djpm1cprimedjm`] that follow from the Diophantine equation `n r
(d - r) = d² - 1` alone, without the rank and dimension grids. Under the bijection of [AFK25,
Theorem 4.20(B), `thm:nrddjmrjm`] the integer `n` is `d_j + 1`, so they are
literally the paper's statements about `d_{j,m}`, `r_{j,m}`, and `d_j + 1`. -/

/-- The rank of an admissible pair is strictly smaller than its dimension. -/
lemma rank_lt_d (p : AdmissiblePair) : p.r < p.d := by
  have := p.rank_pos
  have := p.rank_lt
  omega

/-- Every admissible dimension exceeds three. This follows solely from the rank bounds
`0 < r` and `2r < d - 1` bundled by `AdmissiblePair`, and supplies the standing dimension
hypothesis used by the later constructions. -/
lemma three_lt_d (p : AdmissiblePair) : 3 < p.d := by
  have := p.rank_pos
  have := p.rank_lt
  omega

/-- An admissible dimension is nonzero. -/
instance (p : AdmissiblePair) : NeZero p.d :=
  ⟨by have := p.three_lt_d; omega⟩

/-- The integer `n` of an admissible pair exceeds four, stated without the `let` binder of the
structure field. -/
lemma four_lt_n (p : AdmissiblePair) : 4 < p.n :=
  p.n_gt_four

/-- The defining equation of `AdmissiblePair` over `ℤ`, free of the truncated natural
subtraction used in the structure field. -/
lemma equation_int (p : AdmissiblePair) :
    (p.n : ℤ) * (p.r : ℤ) * ((p.d : ℤ) - (p.r : ℤ)) = (p.d : ℤ) ^ 2 - 1 := by
  have h : p.n * p.r * (p.d - p.r) = p.d ^ 2 - 1 := p.equation
  have hrd : p.r ≤ p.d := p.rank_lt_d.le
  have hd : 1 ≤ p.d ^ 2 := Nat.one_le_pow _ _ (by have := p.three_lt_d; omega)
  zify [hrd, hd] at h
  exact h

/-- The dimension and rank of an admissible pair are coprime.

For pairs arising from the rank and dimension grids, this is [AFK25, Corollary 4.22,
`cor:djmcprjm`]. The proof here derives the stronger pair-level formulation directly from the
defining Diophantine equation, independently of the pair/triple bijection. -/
@[source "AFK25, Corollary 4.22, p. 58, cor:djmcprjm"]
theorem coprime_r_d (p : AdmissiblePair) : Nat.Coprime p.r p.d := by
  have hr : (Nat.gcd p.r p.d : ℤ) ∣ (p.r : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)
  have hd : (Nat.gcd p.r p.d : ℤ) ∣ (p.d : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)
  have h1 : (Nat.gcd p.r p.d : ℤ) ∣ (p.d : ℤ) ^ 2 - 1 :=
    p.equation_int ▸ Dvd.dvd.mul_right (Dvd.dvd.mul_left hr _) _
  have h2 : (Nat.gcd p.r p.d : ℤ) ∣ (p.d : ℤ) ^ 2 := Dvd.dvd.pow hd two_ne_zero
  have h3 : (Nat.gcd p.r p.d : ℤ) ∣ 1 := by simpa using dvd_sub h2 h1
  exact Nat.dvd_one.mp (by exact_mod_cast h3)

/-- The dimension of an admissible pair is coprime to its integer `n`.

Under the pair/triple correspondence, where `n = d_j + 1`, this is the `d_j + 1` half of
[AFK25, Lemma 4.25, `lem:djpm1cprimedjm`]. The proof here again uses only the pair's defining
equation. The `d_j - 1` half needs the grid recursion and is not formalized. -/
@[source "AFK25, Lemma 4.25, p. 60, lem:djpm1cprimedjm (d_j+1)"]
theorem coprime_n_d (p : AdmissiblePair) : Nat.Coprime p.n p.d := by
  have hn : (Nat.gcd p.n p.d : ℤ) ∣ (p.n : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)
  have hd : (Nat.gcd p.n p.d : ℤ) ∣ (p.d : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)
  have h1 : (Nat.gcd p.n p.d : ℤ) ∣ (p.d : ℤ) ^ 2 - 1 :=
    p.equation_int ▸ Dvd.dvd.mul_right (Dvd.dvd.mul_right hn _) _
  have h2 : (Nat.gcd p.n p.d : ℤ) ∣ (p.d : ℤ) ^ 2 := Dvd.dvd.pow hd two_ne_zero
  have h3 : (Nat.gcd p.n p.d : ℤ) ∣ 1 := by simpa using dvd_sub h2 h1
  exact Nat.dvd_one.mp (by exact_mod_cast h3)

/-- In an even admissible dimension the rank is odd.

    [AFK25] deduces this from the rank grid in Lemma 4.23; it already follows from coprimality of
    `r` and `d` (`coprime_r_d`). -/
theorem odd_r_of_even_d (p : AdmissiblePair) (hd : Even p.d) : Odd p.r := by
  rcases Nat.even_or_odd p.r with hr | hr
  · exact absurd (p.coprime_r_d ▸ Nat.dvd_gcd hr.two_dvd hd.two_dvd) (by norm_num)
  · exact hr

/-- In an even admissible dimension the integer `n = d_j + 1` is odd, hence `d_j` is even.

    [AFK25] deduces this from Lemma 4.23; it already follows from coprimality of `n` and `d`
    (`coprime_n_d`). -/
theorem odd_n_of_even_d (p : AdmissiblePair) (hd : Even p.d) : Odd p.n := by
  rcases Nat.even_or_odd p.n with hn | hn
  · exact absurd (p.coprime_n_d ▸ Nat.dvd_gcd hn.two_dvd hd.two_dvd) (by norm_num)
  · exact hn

/-! ### The rank-one family

Specializing the Diophantine equation to `r = 1` gives the canonical admissible pair in every
dimension `d > 3`.
-/

/-- Every dimension `d > 3` has the rank-one admissible pair `(d,1)`.

Its associated field is `ℚ(√((d+1)(d-3)))`; see [AFK25, remark on p. 13]. -/
def rankOne (d : ℕ) (hd : d > 3) : AdmissiblePair := by
  apply ofN d 1 (d + 1) Nat.one_pos (by omega) (by omega)
  have h1 : 1 ≤ d := by omega
  have h2 : 1 ≤ d ^ 2 := Nat.one_le_pow 2 d (by omega)
  zify [h1, h2]
  ring

end AdmissiblePair

end SIC

end
