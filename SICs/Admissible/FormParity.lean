/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Admissible.AssociatedStabilizers

/-!
# Parities of the Scaled Form

The scaled form `(f_j/f)Q`, its coefficient parity, and the sign lemma of Lemma 5.5.

For an admissible tuple `t = (d,r,Q) ∼ (K,j,m,Q)` with form conductor `f`, the source scales the
form to `Q̄ = (f_j/f) Q`, whose discriminant is the level-`j` tower discriminant `Δ_j` rather than
`disc(Q)`.  This file records the resulting parity constraints on the coefficients of `Q̄`, which
[AFK25, Lemma 5.5, `lem:drafjfqp`] uses to match the sign of the Shintani--Faddeev phase against
the level generator `A_t`.

## Mathematical argument

Scaling multiplies a discriminant by the square of the scalar, so

`b̄² - 4 ā c̄ = (f_j/f)² disc(Q) = f_j² Δ₀ = Δ_j = (d_j - 3)(d_j + 1)`,

using `disc(Q) = f² Δ₀` and `RealQuadraticUnitData.canonicalConductor_sq_mul_discr`.  Everything
else is elementary arithmetic in that one equation.  If `d_j` is even the right-hand side is odd,
so `b̄` is odd; then `b̄² ≡ 1 (mod 8)` forces `ā c̄` odd as well, since `Δ_j ≡ 4 ā c̄ + 1 (mod 8)`.
If `d_j` is odd the right-hand side is divisible by four, so `b̄` is even, and dividing by four
compares the parities of `b̄/2` and `ā c̄`: they differ when `d_j ≡ 1 (mod 4)`, where
`Δ_j/4 = 4n² - 1` is odd, and agree when `d_j ≡ 3 (mod 4)`, where `Δ_j/4 = 4n(n+1)` is even.

## References

- [AFK25] Appleby, Flammia, Kopp, arXiv:2501.03970v2, Lemma 5.3 and Corollary 5.4
-/

open scoped MatrixGroups

namespace SIC

/-! ### Odd squares modulo eight

Mathlib's divisibility of an odd square minus one gives the residue used in the discriminant
arguments below. -/

/-- An odd square is one modulo eight, in the residue form used by the three discriminant
parity lemmas below. -/
private lemma sq_emod_eight_of_odd {b : ℤ} (h : b % 2 = 1) : b ^ 2 % 8 = 1 := by
  have hdiv := Int.eight_dvd_sq_sub_one_of_odd (Int.odd_iff.mpr h)
  omega

/-! ### The discriminant equation, as integer arithmetic

The three clauses of [AFK25, Lemma 5.3, `lem:fjfqcmpsoddeven`] are elementary consequences of one
equation `b² - 4ac = (D - 3)(D + 1)`, so they are proved once here for arbitrary integers and
applied at `D = d_j` below. -/

/-- The integer content of [AFK25, Lemma 5.3(1), `lem:fjfqcmpsoddeven`]: for even `D` the
right-hand side is odd, so `b` is odd, and then `b² ≡ 1 (mod 8)` forces `ac` odd too.

The squares and the product `ac` are abstracted with `set` before each `omega` call, since that
tactic drops hypotheses containing nonlinear terms rather than treating them as atoms. Note that
`4 * a * c` does not contain `a * c` as a subterm, so the abstraction is applied to the
`4 * (a * c)` form produced by `linear_combination`. -/
private lemma odd_of_disc_of_even {a b c D : ℤ} (hD : D % 2 = 0)
    (hdisc : b ^ 2 - 4 * a * c = (D - 3) * (D + 1)) :
    a % 2 = 1 ∧ b % 2 = 1 ∧ c % 2 = 1 := by
  obtain ⟨n, hn⟩ : ∃ n, D = 2 * n := ⟨D / 2, by omega⟩
  subst hn
  obtain ⟨s, hs⟩ := Int.even_mul_succ_self (n - 1)
  set X := b ^ 2 with hX
  set Y := a * c with hY
  have hlin : X - 4 * Y = 8 * s - 3 := by
    rw [hX, hY]; linear_combination hdisc + (4 : ℤ) * hs
  have hbodd : b % 2 = 1 := by
    rcases Int.emod_two_eq_zero_or_one b with h2 | h2
    · have h4 : X % 4 = 0 := by rw [hX, Int.sq_emod_four, h2]
      omega
    · exact h2
  have hac : Y % 2 = 1 := by
    have h8 : X % 8 = 1 := by rw [hX]; exact sq_emod_eight_of_odd hbodd
    omega
  have hodd : Odd (a * c) := Int.odd_iff.mpr (by rw [← hY]; exact hac)
  rw [Int.odd_mul] at hodd
  exact ⟨Int.odd_iff.mp hodd.1, hbodd, Int.odd_iff.mp hodd.2⟩

/-- If `b² - 4ac = 4z`, then `b = 2β` and the divided equation is `β² - ac = z`. -/
private lemma exists_half_middle_of_disc_eq_four_mul {a b c z : ℤ}
    (hdisc : b ^ 2 - 4 * a * c = 4 * z) :
    ∃ β : ℤ, b = 2 * β ∧ β ^ 2 - a * c = z := by
  have hbeven : b % 2 = 0 := by
    rcases Int.emod_two_eq_zero_or_one b with h2 | h2
    · exact h2
    · exfalso
      set X := b ^ 2 with hX
      set Y := a * c with hY
      have hlin : X - 4 * Y = 4 * z := by
        rw [hX, hY]
        linear_combination hdisc
      have h4 : X % 4 = 1 := by rw [hX, Int.sq_emod_four, h2]
      omega
  obtain ⟨β, hβ⟩ : ∃ β : ℤ, b = 2 * β := ⟨b / 2, by omega⟩
  refine ⟨β, hβ, ?_⟩
  rw [hβ] at hdisc
  nlinarith

/-- The integer content of [AFK25, Lemma 5.3(2), `lem:fjfqcmpsoddeven`]: for `D ≡ 1 (mod 4)` the
right-hand side is `16n² - 4`, so `b = 2β` and `β² - ac = 4n² - 1` is odd. -/
private lemma parity_of_disc_of_emod_four_eq_one {a b c D : ℤ} (hD : D % 4 = 1)
    (hdisc : b ^ 2 - 4 * a * c = (D - 3) * (D + 1)) :
    (b % 4 = 0 ∧ a * c % 2 = 1) ∨ (b % 4 = 2 ∧ a * c % 2 = 0) := by
  obtain ⟨n, hn⟩ : ∃ n, D = 4 * n + 1 := ⟨D / 4, by omega⟩
  subst hn
  have hdisc' : b ^ 2 - 4 * a * c = 4 * (4 * (n * n) - 1) := by
    linear_combination hdisc
  obtain ⟨β, hβ, hred⟩ := exists_half_middle_of_disc_eq_four_mul hdisc'
  rw [hβ]
  set W := β ^ 2 with hW
  set Y := a * c with hY
  set N := n * n with hN
  have hlin : W - Y = 4 * N - 1 := by
    rw [hW, hY, hN]
    exact hred
  have hβsq : W % 4 = β % 2 := by rw [hW, Int.sq_emod_four]
  rcases Int.emod_two_eq_zero_or_one β with h2 | h2
  · exact Or.inl ⟨by omega, by omega⟩
  · exact Or.inr ⟨by omega, by omega⟩

/-- The integer content of [AFK25, Lemma 5.3(3), `lem:fjfqcmpsoddeven`]: for `D ≡ 3 (mod 4)` the
right-hand side is `16n(n+1)`, so `b = 2β` and `β² - ac = 4n(n+1)` is even. -/
private lemma parity_of_disc_of_emod_four_eq_three {a b c D : ℤ} (hD : D % 4 = 3)
    (hdisc : b ^ 2 - 4 * a * c = (D - 3) * (D + 1)) :
    (b % 4 = 0 ∧ a * c % 2 = 0) ∨ (b % 4 = 2 ∧ a * c % 2 = 1) := by
  obtain ⟨n, hn⟩ : ∃ n, D = 4 * n + 3 := ⟨D / 4, by omega⟩
  subst hn
  have hdisc' : b ^ 2 - 4 * a * c = 4 * (4 * (n * n) + 4 * n) := by
    linear_combination hdisc
  obtain ⟨β, hβ, hred⟩ := exists_half_middle_of_disc_eq_four_mul hdisc'
  rw [hβ]
  set W := β ^ 2 with hW
  set Y := a * c with hY
  set N := n * n with hN
  have hlin : W - Y = 4 * N + 4 * n := by
    rw [hW, hY, hN]
    exact hred
  have hβsq : W % 4 = β % 2 := by rw [hW, Int.sq_emod_four]
  rcases Int.emod_two_eq_zero_or_one β with h2 | h2
  · exact Or.inl ⟨by omega, by omega⟩
  · exact Or.inr ⟨by omega, by omega⟩

namespace AdmissibleTuple

/-! ### The discriminant of the scaled form

`Q̄ = (f_j/f) Q` has discriminant `Δ_j`, the level-`j` tower discriminant. -/

/-- **The discriminant of the scaled form** `Q̄ = (f_j/f) Q`:

`b̄² - 4 ā c̄ = (d_j - 3)(d_j + 1)`.

The right-hand side is `Δ_j` of [AFK25, Definition 4.2, `dfn:discriminantLevelj`]; this is the
equation the proof of [AFK25, Lemma 5.3, `lem:fjfqcmpsoddeven`] opens with. It is
`AdmissibleTuple.towerConductorRatio_sq_mul_disc` with `disc(Q) = b² - 4ac` expanded. -/
theorem scaledForm_disc (t : AdmissibleTuple) :
    ((t.towerConductorRatio : ℤ) * t.Q.b) ^ 2 -
        4 * ((t.towerConductorRatio : ℤ) * t.Q.a) * ((t.towerConductorRatio : ℤ) * t.Q.c) =
      ((t.triple.towerDimension : ℤ) - 3) * ((t.triple.towerDimension : ℤ) + 1) := by
  have h := t.towerConductorRatio_sq_mul_disc
  simp only [BinaryQF.disc, discrim] at h
  linear_combination h

/-! ### Parities of the scaled coefficients

The three clauses of [AFK25, Lemma 5.3, `lem:fjfqcmpsoddeven`], one per residue of `d_j`.  Each
is elementary arithmetic in `scaledForm_disc`; the statements are `Δ_j`-free so that consumers see
only the coefficients. -/

/-- **[AFK25, Lemma 5.3(1), `lem:fjfqcmpsoddeven`].** If `d_j` is even, then the coefficients
`⟨ā, b̄, c̄⟩ = (f_j/f) Q` are all odd. -/
@[source "AFK25, Lemma 5.3, p. 74, lem:fjfqcmpsoddeven (1)"]
theorem odd_scaledForm_of_even_towerDimension (t : AdmissibleTuple)
    (h : (t.triple.towerDimension : ℤ) % 2 = 0) :
    (t.towerConductorRatio : ℤ) * t.Q.a % 2 = 1 ∧
      (t.towerConductorRatio : ℤ) * t.Q.b % 2 = 1 ∧
      (t.towerConductorRatio : ℤ) * t.Q.c % 2 = 1 :=
  odd_of_disc_of_even h t.scaledForm_disc

/-- **[AFK25, Lemma 5.3(2), `lem:fjfqcmpsoddeven`].** If `d_j ≡ 1 (mod 4)`, then either
`b̄ ≡ 0 (mod 4)` and `ā c̄` is odd, or `b̄ ≡ 2 (mod 4)` and `ā c̄` is even. -/
@[source "AFK25, Lemma 5.3, p. 74, lem:fjfqcmpsoddeven (2)"]
theorem scaledForm_of_towerDimension_emod_four_eq_one (t : AdmissibleTuple)
    (h : (t.triple.towerDimension : ℤ) % 4 = 1) :
    ((t.towerConductorRatio : ℤ) * t.Q.b % 4 = 0 ∧
        (t.towerConductorRatio : ℤ) * t.Q.a * ((t.towerConductorRatio : ℤ) * t.Q.c) % 2 = 1) ∨
      ((t.towerConductorRatio : ℤ) * t.Q.b % 4 = 2 ∧
        (t.towerConductorRatio : ℤ) * t.Q.a * ((t.towerConductorRatio : ℤ) * t.Q.c) % 2 = 0) :=
  parity_of_disc_of_emod_four_eq_one h t.scaledForm_disc

/-- **[AFK25, Lemma 5.3(3), `lem:fjfqcmpsoddeven`].** If `d_j ≡ 3 (mod 4)`, then either
`b̄ ≡ 0 (mod 4)` and `ā c̄` is even, or `b̄ ≡ 2 (mod 4)` and `ā c̄` is odd. -/
@[source "AFK25, Lemma 5.3, p. 74, lem:fjfqcmpsoddeven (3)"]
theorem scaledForm_of_towerDimension_emod_four_eq_three (t : AdmissibleTuple)
    (h : (t.triple.towerDimension : ℤ) % 4 = 3) :
    ((t.towerConductorRatio : ℤ) * t.Q.b % 4 = 0 ∧
        (t.towerConductorRatio : ℤ) * t.Q.a * ((t.towerConductorRatio : ℤ) * t.Q.c) % 2 = 0) ∨
      ((t.towerConductorRatio : ℤ) * t.Q.b % 4 = 2 ∧
        (t.towerConductorRatio : ℤ) * t.Q.a * ((t.towerConductorRatio : ℤ) * t.Q.c) % 2 = 1) :=
  parity_of_disc_of_emod_four_eq_three h t.scaledForm_disc

/-- **[AFK25, Corollary 5.4, `cor:fjmfqcmpsoddeven`].** If `d = d_{j,m}` is even, then the
coefficients of `(f_{jm}/f) Q` are all odd.

An even `d` forces `d_j` even, since [AFK25, Lemma 4.23, `lem:dimgridtechres`] makes `d_{j,m}` odd
for every `m` when `d_j` is odd. The rank is odd by `AdmissiblePair.odd_r_of_even_d`.
Since `(f_{jm}/f) Q = r_{j,m} (f_j/f) Q` by
`conductorRatio_eq_rank_mul`, the claim follows from
`odd_scaledForm_of_even_towerDimension`. -/
@[source "AFK25, Corollary 5.4, p. 75, cor:fjmfqcmpsoddeven"]
theorem odd_gridScaledForm_of_even_d (t : AdmissibleTuple) (h : Even t.d) :
    Odd ((t.conductorRatio : ℤ) * t.Q.a) ∧ Odd ((t.conductorRatio : ℤ) * t.Q.b) ∧
      Odd ((t.conductorRatio : ℤ) * t.Q.c) := by
  have hJeven := t.even_towerDimension_of_even_d h
  have hJ : ((t.triple.towerDimension : ℕ) : ℤ) % 2 = 0 := by
    exact_mod_cast Nat.even_iff.mp hJeven
  have hrank : Odd ((t.triple.rank : ℕ) : ℤ) := by
    rw [← t.r_eq_rank]
    exact_mod_cast t.pair.odd_r_of_even_d h
  obtain ⟨ha, hb, hc⟩ := t.odd_scaledForm_of_even_towerDimension hJ
  have hsplit : ((t.conductorRatio : ℕ) : ℤ) =
      ((t.triple.rank : ℕ) : ℤ) * ((t.towerConductorRatio : ℕ) : ℤ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) t.conductorRatio_eq_rank_mul
  refine ⟨?_, ?_, ?_⟩ <;> rw [hsplit, mul_assoc]
  · exact hrank.mul (Int.odd_iff.mpr ha)
  · exact hrank.mul (Int.odd_iff.mpr hb)
  · exact hrank.mul (Int.odd_iff.mpr hc)

/-! ### The parity entering the sign lemma

The clauses above combine into the single statement the sign lemma needs: `b̄` has the opposite
parity to `d_j`, whichever residue `d_j` has. -/

/-- `b̄ + d_j` is odd: by [AFK25, Lemma 5.3, `lem:fjfqcmpsoddeven`], `b̄` is odd exactly when `d_j`
is even.  Used by `IsAssociatedStabilizerPair.two_dvd_scaledForm_eval_iff` to halve
`d(d_j - 3) - e b̄`. -/
private lemma scaledForm_b_add_towerDimension_odd (t : AdmissibleTuple) :
    ((t.towerConductorRatio : ℤ) * t.Q.b + (t.triple.towerDimension : ℤ)) % 2 = 1 := by
  have hcases : (t.triple.towerDimension : ℤ) % 4 = 0 ∨ (t.triple.towerDimension : ℤ) % 4 = 1 ∨
      (t.triple.towerDimension : ℤ) % 4 = 2 ∨ (t.triple.towerDimension : ℤ) % 4 = 3 := by omega
  rcases hcases with h | h | h | h
  · have := (t.odd_scaledForm_of_even_towerDimension (by omega)).2.1
    omega
  · rcases t.scaledForm_of_towerDimension_emod_four_eq_one h with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
  · have := (t.odd_scaledForm_of_even_towerDimension (by omega)).2.1
    omega
  · rcases t.scaledForm_of_towerDimension_emod_four_eq_three h with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega

/-! ### The sign lemma

[AFK25, Lemma 5.5, `lem:drafjfqp`] matches the sign `(-1)^{Q̄(p)}` carried by the Shintani--Faddeev
phase against the level generator.  The closed form of `A_t` turns the two components of
`(A_t - I)p` into `d` times an explicit combination of `p` with the coefficients of `Q̄`, so the
congruence `A_t p ≡ p (mod 2d)` becomes a pair of congruences modulo two.  Writing
`e = r_{j,m+1} - r_{j,m}` and `2u = d(d_j - 3) - e b̄`, those are

`u p₁ ≡ e c̄ p₂`  and  `e ā p₁ + (u + e b̄) p₂ ≡ 0`   (mod 2),

while the phase sign is governed by `ā p₁² + b̄ p₁ p₂ + c̄ p₂² (mod 2)`.  Both sides then depend
only on residues modulo two, and the parity clauses above pin those residues down: if `d_j` is
even then `ā, b̄, c̄` are all odd and `e ≡ d`, with `u` odd whenever `d` is even; if `d_j` is odd
then `b̄` is even, `d` and `e` are odd, and `u ≡ ā c̄`.  Each of the two resulting statements over
`ZMod 2` is a finite check.
-/

/-- **[AFK25, Lemma 5.5, `lem:drafjfqp`].** For every integer index `p`, the scaled form
`Q̄ = (f_j/f) Q` satisfies

`Q̄(p) ≡ 0 (mod 2)  ⟺  A_t p ≡ p (mod 2d)`.

The source states the equivalent sign form `(-1)^{(f_j/f)Q(p)} = (-1)^{1 + δ^{(2d)}_{A_t p, p}}`,
with `δ` the modular delta of [AFK25, Definition 1.33, `dfn:modulardeltafunction`]; the two
statements differ only by rewriting a sign as a parity.

The source's proof divides `A_t - I` by `d` and analyses the resulting integral matrix `H` in four
cases. The proof here works with `2(A_t - I)` instead, which
`IsAssociatedStabilizerPair.twice_A_sub_one_eq` supplies without dividing, and closes each case by
a finite check over `ZMod 2`. -/
@[source "AFK25, Lemma 5.5, p. 75, lem:drafjfqp"]
theorem IsAssociatedStabilizerPair.two_dvd_scaledForm_eval_iff {t : AdmissibleTuple}
    {A_t Lz : SL(2, ℤ)} (h : t.IsAssociatedStabilizerPair A_t Lz) (p : Fin 2 → ℤ) :
    (2 : ℤ) ∣ (t.towerConductorRatio : ℤ) * t.Q.eval (p 0) (p 1) ↔
      ∀ i, (2 * (t.d : ℤ)) ∣
        (Matrix.mulVec (A_t : Mat(2, ℤ)) p i - p i) := by
  have hdpos : (0 : ℤ) < (t.d : ℤ) := by
    exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) t.three_lt_d
  -- The entries of the closed form of `A_t`.
  have hmat := h.twice_A_sub_one_eq
  have e00 := congrFun (congrFun hmat 0) 0
  have e01 := congrFun (congrFun hmat 0) 1
  have e10 := congrFun (congrFun hmat 1) 0
  have e11 := congrFun (congrFun hmat 1) 1
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply,
    smul_eq_mul] at e00 e01 e10 e11
  simp only [Fin.isValue, Matrix.one_apply_eq, mul_one, BinaryQF.twiceSQ, Int.reduceNeg, neg_mul,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, mul_neg,
    ne_eq, zero_ne_one, not_false_eq_true, Matrix.one_apply_ne, sub_zero, mul_zero,
    Matrix.cons_val_one, zero_add, one_ne_zero] at e00 e01 e10 e11
  -- Abstract the tower and form data, so that `omega` and the `ZMod 2` step see opaque integers.
  obtain ⟨R, hR⟩ : ∃ R, t.triple.tower.rankGridInt t.triple.j (t.triple.m : ℕ) = R := ⟨_, rfl⟩
  obtain ⟨R1, hR1⟩ : ∃ R1,
      t.triple.tower.rankGridInt t.triple.j ((t.triple.m : ℕ) + 1) = R1 := ⟨_, rfl⟩
  obtain ⟨Ab, hAb⟩ : ∃ X, (t.towerConductorRatio : ℤ) * t.Q.a = X := ⟨_, rfl⟩
  obtain ⟨Bb, hBb⟩ : ∃ X, (t.towerConductorRatio : ℤ) * t.Q.b = X := ⟨_, rfl⟩
  obtain ⟨Cb, hCb⟩ : ∃ X, (t.towerConductorRatio : ℤ) * t.Q.c = X := ⟨_, rfl⟩
  rw [hR, hR1] at e00 e01 e10 e11
  have f00 : 2 * ((A_t : Mat(2, ℤ)) 0 0 - 1) =
      (t.d : ℤ) ^ 2 * ((t.triple.towerDimension : ℤ) - 3) - (t.d : ℤ) * (R1 - R) * Bb := by
    rw [← hBb]; linear_combination e00
  have f01 : 2 * ((A_t : Mat(2, ℤ)) 0 1) =
      -2 * (t.d : ℤ) * (R1 - R) * Cb := by rw [← hCb]; linear_combination e01
  have f10 : 2 * ((A_t : Mat(2, ℤ)) 1 0) =
      2 * (t.d : ℤ) * (R1 - R) * Ab := by rw [← hAb]; linear_combination e10
  have f11 : 2 * ((A_t : Mat(2, ℤ)) 1 1 - 1) =
      (t.d : ℤ) ^ 2 * ((t.triple.towerDimension : ℤ) - 3) + (t.d : ℤ) * (R1 - R) * Bb := by
    rw [← hBb]; linear_combination e11
  -- `d = r_{j,m+1} + r_{j,m}`, and `b̄ + d_j` is odd, so `d(d_j - 3) - e b̄` is even.
  have hd : (t.d : ℤ) = R1 + R := by
    rw [← hR, ← hR1, t.d_eq_dimension]
    exact t.triple.tower.dimensionGrid_coe_int t.triple.j t.triple.m
  have hoddb : (Bb + (t.triple.towerDimension : ℤ)) % 2 = 1 := by
    rw [← hBb]; exact t.scaledForm_b_add_towerDimension_odd
  obtain ⟨w, hw⟩ : ∃ w, (t.triple.towerDimension : ℤ) - 3 - Bb = 2 * w :=
    ⟨((t.triple.towerDimension : ℤ) - 3 - Bb) / 2, by omega⟩
  obtain ⟨u, hu⟩ : ∃ u, u = (t.d : ℤ) * w + R * Bb := ⟨_, rfl⟩
  have hu2 : (t.d : ℤ) * ((t.triple.towerDimension : ℤ) - 3) - (R1 - R) * Bb = 2 * u := by
    rw [hu, hd]; linear_combination (R1 + R) * hw
  -- The two components of `(A_t - I)p`, each `d` times an explicit combination.
  have hq0 : Matrix.mulVec (A_t : Mat(2, ℤ)) p 0 - p 0 =
      (t.d : ℤ) * (u * p 0 - (R1 - R) * Cb * p 1) := by
    refine mul_left_cancel₀ (a := (2 : ℤ)) (by norm_num) ?_
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linear_combination (p 0) * f00 + (p 1) * f01 + (p 0 * (t.d : ℤ)) * hu2
  have hq1 : Matrix.mulVec (A_t : Mat(2, ℤ)) p 1 - p 1 =
      (t.d : ℤ) * ((R1 - R) * Ab * p 0 + (u + (R1 - R) * Bb) * p 1) := by
    refine mul_left_cancel₀ (a := (2 : ℤ)) (by norm_num) ?_
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linear_combination (p 0) * f10 + (p 1) * f11 + (p 1 * (t.d : ℤ)) * hu2
  have hev : (t.towerConductorRatio : ℤ) * t.Q.eval (p 0) (p 1) =
      Ab * p 0 ^ 2 + Bb * (p 0 * p 1) + Cb * p 1 ^ 2 := by
    rw [← hAb, ← hBb, ← hCb, BinaryQF.eval]; ring
  rw [Fin.forall_fin_two, hq0, hq1, hev,
    show (2 : ℤ) * (t.d : ℤ) = (t.d : ℤ) * 2 by ring,
    mul_dvd_mul_iff_left (ne_of_gt hdpos), mul_dvd_mul_iff_left (ne_of_gt hdpos)]
  simp only [← even_iff_two_dvd, ← ZMod.intCast_eq_zero_iff_even]
  push_cast
  -- `e = r_{j,m+1} - r_{j,m}` and `d = r_{j,m+1} + r_{j,m}` agree modulo two.
  have hEz : ((R1 : ℤ) : ZMod 2) - ((R : ℤ) : ZMod 2) = (((t.d : ℕ) : ℤ) : ZMod 2) := by
    have hpar : (R1 - R) % 2 = ((t.d : ℕ) : ℤ) % 2 := by omega
    have h2 := (ZMod.intCast_eq_intCast_iff' _ _ 2).mpr hpar
    push_cast at h2
    exact h2
  rw [hEz]
  have hdcast : ((t.d : ℕ) : ℤ) =
      ((t.triple.tower.dimensionGrid t.triple.j t.triple.m : ℕ) : ℤ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) t.d_eq_dimension
  have hdimcast : ((t.triple.towerDimension : ℕ) : ℤ) =
      t.triple.tower.dimensionInt (t.triple.j : ℕ) :=
    t.triple.tower.canonicalDimension_coe_int t.triple.j
  rcases Int.emod_two_eq_zero_or_one ((t.triple.towerDimension : ℕ) : ℤ) with hJ | hJ
  · -- `d_j` even: the coefficients of `Q̄` are all odd.
    obtain ⟨ha, hb, hc⟩ := t.odd_scaledForm_of_even_towerDimension hJ
    rw [hAb] at ha
    rw [hBb] at hb
    rw [hCb] at hc
    rw [(Int.odd_iff.mpr ha).intCast_zmod_two, (Int.odd_iff.mpr hb).intCast_zmod_two,
      (Int.odd_iff.mpr hc).intCast_zmod_two]
    rcases Int.emod_two_eq_zero_or_one ((t.d : ℕ) : ℤ) with hD | hD
    · -- `d` even: the admissible rank `r_{j,m}` is odd, so `u` is odd.
      have hdEven : Even t.d := by
        rw [Nat.even_iff]
        exact_mod_cast hD
      have hRodd : R % 2 = 1 := by
        have hr : Odd ((t.triple.rank : ℕ) : ℤ) := by
          rw [← t.r_eq_rank]
          exact_mod_cast t.pair.odd_r_of_even_d hdEven
        have hcast : ((t.triple.rank : ℕ) : ℤ) =
            t.triple.tower.rankGridInt t.triple.j (t.triple.m : ℕ) :=
          t.triple.tower.rankGrid_coe_int t.triple.j t.triple.m
        rwa [Int.odd_iff, hcast, hR] at hr
      have hm1 : ((t.d : ℕ) : ℤ) * w % 2 = 0 := by rw [Int.mul_emod, hD]; simp
      have hm2 : R * Bb % 2 = 1 := by rw [Int.mul_emod, hRodd, hb]; norm_num
      have huodd : u % 2 = 1 := by rw [hu, Int.add_emod, hm1, hm2]; norm_num
      rw [(Int.even_iff.mpr hD).intCast_zmod_two, (Int.odd_iff.mpr huodd).intCast_zmod_two]
      generalize ((p 0 : ℤ) : ZMod 2) = x
      generalize ((p 1 : ℤ) : ZMod 2) = y
      revert x y
      decide
    · -- `d` odd: the two congruences already determine `p` modulo two, for either parity of `u`.
      rw [(Int.odd_iff.mpr hD).intCast_zmod_two]
      generalize ((u : ℤ) : ZMod 2) = U
      generalize ((p 0 : ℤ) : ZMod 2) = x
      generalize ((p 1 : ℤ) : ZMod 2) = y
      revert U x y
      decide
  · -- `d_j` odd: `b̄` is even, `d` is odd, and `u ≡ ā c̄`.
    have hj1 : (2 : ℤ) ∣ t.triple.tower.dimensionInt (t.triple.j : ℕ) - 1 := by omega
    have hDodd : ((t.d : ℕ) : ℤ) % 2 = 1 := by
      have hg :=
        t.triple.tower.dimensionGrid_emod_two_of_two_dvd_sub_one t.triple.j t.triple.m hj1
      rw [← hdcast] at hg
      exact hg
    obtain ⟨P, hP⟩ : ∃ P, Ab * Cb = P := ⟨_, rfl⟩
    have hb4 : Bb % 4 = 0 ∧ P % 2 = 1 ∨ Bb % 4 = 2 ∧ P % 2 = 0 ∨
        Bb % 4 = 0 ∧ P % 2 = 0 ∨ Bb % 4 = 2 ∧ P % 2 = 1 := by
      have h4 : ((t.triple.towerDimension : ℕ) : ℤ) % 4 = 1 ∨
          ((t.triple.towerDimension : ℕ) : ℤ) % 4 = 3 := by omega
      rcases h4 with h4 | h4
      · rcases t.scaledForm_of_towerDimension_emod_four_eq_one h4 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          rw [hBb] at h1 <;> rw [hAb, hCb, hP] at h2
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr (Or.inl ⟨h1, h2⟩)
      · rcases t.scaledForm_of_towerDimension_emod_four_eq_three h4 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          rw [hBb] at h1 <;> rw [hAb, hCb, hP] at h2
        · exact Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨h1, h2⟩))
    have hBeven : Bb % 2 = 0 := by omega
    have hwP : w % 2 = P % 2 := by
      have h4 : ((t.triple.towerDimension : ℕ) : ℤ) % 4 = 1 ∨
          ((t.triple.towerDimension : ℕ) : ℤ) % 4 = 3 := by omega
      rcases h4 with h4 | h4
      · rcases t.scaledForm_of_towerDimension_emod_four_eq_one h4 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          rw [hBb] at h1 <;> rw [hAb, hCb, hP] at h2 <;> omega
      · rcases t.scaledForm_of_towerDimension_emod_four_eq_three h4 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          rw [hBb] at h1 <;> rw [hAb, hCb, hP] at h2 <;> omega
    have hm1 : ((t.d : ℕ) : ℤ) * w % 2 = w % 2 := by rw [Int.mul_emod, hDodd]; omega
    have hm2 : R * Bb % 2 = 0 := by rw [Int.mul_emod, hBeven]; simp
    have huP : u % 2 = (Ab * Cb) % 2 := by rw [hu, Int.add_emod, hm1, hm2, hP]; omega
    have hUz := (ZMod.intCast_eq_intCast_iff' _ _ 2).mpr huP
    push_cast at hUz
    rw [(Int.odd_iff.mpr hDodd).intCast_zmod_two, (Int.even_iff.mpr hBeven).intCast_zmod_two, hUz]
    generalize ((Ab : ℤ) : ZMod 2) = A
    generalize ((Cb : ℤ) : ZMod 2) = C
    generalize ((p 0 : ℤ) : ZMod 2) = x
    generalize ((p 1 : ℤ) : ZMod 2) = y
    revert A C x y
    decide

end AdmissibleTuple

end SIC
