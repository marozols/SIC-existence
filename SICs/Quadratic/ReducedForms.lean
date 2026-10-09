/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Quadratic.FormActions
import SICs.SL2Z.HJExpansion

/-!
# Hirzebruch--Jung reduced forms and purely periodic expansions

Hirzebruch–Jung reduced forms, the rotation on forms, and the purely periodic expansion of a reduced
quadratic irrational.

This file proves that a real quadratic number `β` with `0 < β' < 1 < β` has a *purely* periodic
Hirzebruch--Jung continued fraction expansion, the half of [72, Kopp (2024), Proposition 7.2,
`prop:quadhj`] that the cycle data of [72, Kopp (2024), Definition 7.4, `defn:cycledata`] needs.
Kopp cites [68, Katok (2003), Theorem 1.4] for it, and the proof below is Katok's, transposed from
her parametrization `β = (m + √D)/ℓ` to the coefficients of the integral form having `β` as a root.

## The reduced condition on coefficients

Kopp's condition is on the two roots. For a form `Q = ⟨a,b,c⟩` with `a > 0` it is equivalent to

$$
c > 0,\qquad a + b + c < 0,
$$

because `ax² + bx + c = a(x-β)(x-β')`, so `c = a\beta\beta'` and `a+b+c = a(1-\beta)(1-\beta')`:
the first inequality says both roots have the same sign and the second says exactly one of them
exceeds `1`. That is `isHJReduced_iff_roots`. The coefficient form is the one used everywhere
below, because it is elementary integer arithmetic; `IsHJReduced` is defined by it.

Katok's bound `|m - ℓ| < √D` in the proof of [68, Katok (2003), Theorem 1.3], for the
parametrization `β = (m + √D)/ℓ`, is exactly `a + b + c < 0` after clearing denominators: there
`a = ℓ`, `b = -2m` and `c = (m² - D)/ℓ`, so `a + b + c = ((m-ℓ)² - D)/ℓ`.

## The rotation on forms

One Hirzebruch--Jung rotation `β ↦ 1/(⌈β⌉ - β)` of `SICs.SL2Z.HJExpansion` is realized on forms
by

$$
\langle a,b,c\rangle \longmapsto \langle Q(b_0,1),\,-(2ab_0+b),\,a\rangle,
\qquad b_0 = \lceil\beta\rceil,
$$

which is the `GL₂(ℤ)` action of the Hirzebruch--Jung generator `T^{b_0}S`: substituting
`β = b_0 - 1/γ` into `aβ² + bβ + c = 0` and clearing `γ²` produces exactly these coefficients.
The discriminant is unchanged (`disc_hjRotateForm`), and the rotation sends the root `β` to
`1/(b_0-β)` and its conjugate `β'` to `1/(b_0-β')`.

Reducedness is preserved: `b_0 - β ∈ (0,1)` at an irrational `β`, so the new root exceeds `1`,
while `b_0 ≥ 2` and `β' < 1` give `b_0 - β' > 1`, so the new conjugate lies in `(0,1)`. This is
Katok's induction "for all `i ≥ 1`, `0 < β'_i < 1`".

## Why the orbit closes up

Two elementary facts finish the argument.

*Finiteness.* A reduced form has `a, c ≥ 1` and, since `a+b+c` is a negative integer,
`b ≤ -(a+c)-1`; hence `Δ = b² - 4ac ≥ (a+c+1)² - 4ac = (a-c)² + 2(a+c) + 1`, so
`2(a+c) < Δ`. Both `a` and `c` are therefore bounded by `Δ`, and `b² = Δ + 4ac` bounds `b`. So
only finitely many reduced forms have a given discriminant (`finite_setOf_isHJReduced`), and the
rotation orbit of a reduced form must repeat.

*Injectivity.* The rotation can be undone. Its output records `a` as its own `c`, and the
previous partial quotient is read off the *conjugate* root: the new conjugate is `1/(b_0-β')`
with `β' ∈ (0,1)`, so `b_0 = ⌈1/β'_{new}⌉`. Knowing `b_0` and the output's coefficients returns
`⟨a,b,c⟩`, so the rotation is injective on reduced irreducible forms
(`hjRotateForm_injOn`). A repeat `Q_j = Q_k` with `j < k` can then be pulled back to
`Q_0 = Q_{k-j}`, which is pure periodicity.

## References

- [72, Kopp (2024), Proposition 7.2, `prop:quadhj`]: the statement, in the form the cycle data of
  [72, Kopp (2024), Definition 7.4, `defn:cycledata`] uses.
- [68, Katok (2003), Theorem 1.4] and the boundedness step in the proof of her Theorem 1.3: the
  argument formalized here. Katok writes the partial quotient as `⌊β⌋ + 1`, which agrees with
  `⌈β⌉` off `ℤ`, so her recursion is `hjRotate`.
- `SICs.SL2Z.HJExpansion`: the expansion itself, its cycle matrices, and [72, Kopp (2024), Lemma
  7.5, `lem:betajs`].
-/

namespace SIC

namespace BinaryQF

/-! ### The reduced condition

Reducedness is recorded on the coefficients, where it is integer arithmetic, and characterized on
the roots, where it is Kopp's condition `0 < β' < 1 < β`. -/

/-- **Hirzebruch--Jung reducedness of a form of positive leading coefficient**: `c > 0` and
`a + b + c < 0`. For `a > 0` this is exactly the condition `0 < ρ_{Q,-} < 1 < ρ_{Q,+}` on the
roots imposed by [72, Kopp (2024), Proposition 7.2, `prop:quadhj`] and [72, Kopp (2024), Definition
7.4, `defn:cycledata`] (`isHJReduced_iff_roots`); it is stated on the coefficients because the
finiteness argument is integer arithmetic. The leading coefficient is part of the condition, so
that reducedness alone pins the orientation of the two roots.

This is *not* Gauss reduction of indefinite forms; the two notions cut out different sets of
representatives, and only this one corresponds to purely periodic minus continued fractions.

The anonymous constructor is the introduction rule; `IsHJReduced.a_pos`, `IsHJReduced.c_pos` and
`IsHJReduced.add_neg` are the projections. -/
def IsHJReduced (Q : BinaryQF) : Prop := 0 < Q.a ∧ 0 < Q.c ∧ Q.a + Q.b + Q.c < 0

/-- A reduced form has positive leading coefficient. -/
theorem IsHJReduced.a_pos {Q : BinaryQF} (h : Q.IsHJReduced) : 0 < Q.a := h.1

/-- A reduced form has positive trailing coefficient. -/
theorem IsHJReduced.c_pos {Q : BinaryQF} (h : Q.IsHJReduced) : 0 < Q.c := h.2.1

/-- A reduced form takes a negative value at `(1,1)`. -/
theorem IsHJReduced.add_neg {Q : BinaryQF} (h : Q.IsHJReduced) : Q.a + Q.b + Q.c < 0 := h.2.2

/-- The identity `Δ - (2a+b)² = -4a(a+b+c)`, which converts the two unit inequalities on the
roots into the sign of the form's value at `(1,1)`. -/
private lemma disc_cast_sub_two_mul_add_sq (Q : BinaryQF) :
    (Q.disc : ℝ) - (2 * (Q.a : ℝ) + Q.b) ^ 2 =
      -4 * (Q.a : ℝ) * (Q.a + Q.b + Q.c) := by
  rw [disc_cast_eq_coefficients]
  ring

/-- A reduced form has negative middle coefficient, since `a` and `c` are positive. -/
theorem IsHJReduced.b_neg {Q : BinaryQF} (h : Q.IsHJReduced) : Q.b < 0 := by
  nlinarith [h.a_pos, h.c_pos, h.add_neg]

/-- **The reduced box**: `2(a+c) < Δ`. Since `a + b + c` is a negative *integer*,
`b ≤ -(a+c)-1`, so `Δ = b² - 4ac ≥ (a+c+1)² - 4ac = (a-c)² + 2(a+c) + 1`. This is the finiteness
bound of the proof of [68, Katok (2003), Theorem 1.3]; Katok bounds `ℓ` by a divisibility
argument after `|m - ℓ| < √D`, which the integer bound on `a + b + c` replaces here. -/
theorem IsHJReduced.two_mul_add_lt_disc {Q : BinaryQF} (h : Q.IsHJReduced) :
    2 * (Q.a + Q.c) < Q.disc := by
  have hadd := h.add_neg
  have hb : Q.b ≤ -(Q.a + Q.c) - 1 := by omega
  rw [disc_eq_coefficients]
  nlinarith [sq_nonneg (Q.a - Q.c), h.a_pos, h.c_pos]

/-- **A reduced form is indefinite**: `Δ = b² - 4ac > 0`, because the stronger reduced-box
bound `2(a+c) < Δ` has a positive left side. -/
theorem IsHJReduced.disc_pos {Q : BinaryQF} (h : Q.IsHJReduced) : 0 < Q.disc := by
  nlinarith [h.two_mul_add_lt_disc, h.a_pos, h.c_pos]

/-- **Positivity of the conjugate root, cleared of denominators**: `0 < ρ_{Q,-}` says exactly
`√Δ < -b`. No hypothesis on the discriminant is needed, since only the positive denominator `2a`
is cleared. -/
private lemma rootMinus_pos_iff {Q : BinaryQF} (ha : 0 < Q.a) :
    0 < Q.rootMinus ↔ Real.sqrt (Q.disc : ℝ) < -(Q.b : ℝ) := by
  have hden : 0 < 2 * (Q.a : ℝ) := by positivity
  rw [rootMinus, div_pos_iff_of_pos_right hden]
  constructor <;> intro h <;> linarith

/-- **The two unit inequalities, cleared of denominators**: `ρ_{Q,-} < 1 < ρ_{Q,+}` says exactly
`|2a + b| < √Δ`, one root lying above `1` and the other below. As in `rootMinus_pos_iff`, only
the positive denominator `2a` is cleared. -/
private lemma rootMinus_lt_one_and_one_lt_rootPlus_iff {Q : BinaryQF} (ha : 0 < Q.a) :
    (Q.rootMinus < 1 ∧ 1 < Q.rootPlus) ↔ |2 * (Q.a : ℝ) + Q.b| < Real.sqrt (Q.disc : ℝ) := by
  have hden : 0 < 2 * (Q.a : ℝ) := by positivity
  rw [rootMinus, rootPlus, div_lt_one hden, one_lt_div hden, abs_lt]
  constructor
  · intro h; exact ⟨by linarith [h.1], by linarith [h.2]⟩
  · intro h; exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- **Reducedness on the roots**, [72, Kopp (2024), Proposition 7.2, `prop:quadhj`]'s condition
`0 < β' < 1 < β`: for a form of positive leading coefficient it is the coefficient condition
`IsHJReduced`.

Both directions run through the two translations above, so what is left is arithmetic in `√Δ`:
`√Δ < -b` is `b < 0` together with `4ac > 0`, and `|2a+b| < √Δ` is
`Δ - (2a+b)² = -4a(a+b+c) > 0`. -/
theorem isHJReduced_iff_roots {Q : BinaryQF} (ha : 0 < Q.a) :
    Q.IsHJReduced ↔ 0 < Q.rootMinus ∧ Q.rootMinus < 1 ∧ 1 < Q.rootPlus := by
  have haR : 0 < (Q.a : ℝ) := by exact_mod_cast ha
  have hs : 0 ≤ Real.sqrt (Q.disc : ℝ) := Real.sqrt_nonneg _
  have hid := disc_cast_sub_two_mul_add_sq Q
  have hdisc_coeff := disc_cast_eq_coefficients Q
  rw [and_congr (rootMinus_pos_iff ha) (rootMinus_lt_one_and_one_lt_rootPlus_iff ha)]
  constructor
  · intro h
    have hs2 : Real.sqrt (Q.disc : ℝ) ^ 2 = (Q.disc : ℝ) :=
      Real.sq_sqrt (by exact_mod_cast h.disc_pos.le)
    have hbR : (Q.b : ℝ) < 0 := by exact_mod_cast h.b_neg
    have hcR : 0 < (Q.c : ℝ) := by exact_mod_cast h.c_pos
    have haddR : (Q.a + Q.b + Q.c : ℝ) < 0 := by exact_mod_cast h.add_neg
    refine ⟨by nlinarith, abs_lt_of_sq_lt_sq (by rw [hs2]; nlinarith) hs⟩
  · rintro ⟨hslt, habs⟩
    have hdisc : 0 ≤ (Q.disc : ℝ) := by
      rcases le_or_gt 0 (Q.disc : ℝ) with h | h
      · exact h
      · rw [Real.sqrt_eq_zero_of_nonpos h.le] at habs
        exact absurd (abs_nonneg _) (not_le.mpr habs)
    have hs2 : Real.sqrt (Q.disc : ℝ) ^ 2 = (Q.disc : ℝ) :=
      Real.sq_sqrt hdisc
    have hsq : (2 * (Q.a : ℝ) + Q.b) ^ 2 < (Q.disc : ℝ) := by
      rw [← hs2]; exact sq_lt_sq' (neg_lt_of_abs_lt habs) (lt_of_abs_lt habs)
    have hcR : 0 < (Q.c : ℝ) := by nlinarith
    have haddR : (Q.a + Q.b + Q.c : ℝ) < 0 := by nlinarith
    exact ⟨ha, by exact_mod_cast hcR, by exact_mod_cast haddR⟩

/-- The conjugate root of a reduced form is positive. -/
theorem IsHJReduced.rootMinus_pos {Q : BinaryQF} (h : Q.IsHJReduced) : 0 < Q.rootMinus :=
  ((isHJReduced_iff_roots h.a_pos).mp h).1

/-- The conjugate root of a reduced form is below `1`. -/
theorem IsHJReduced.rootMinus_lt_one {Q : BinaryQF} (h : Q.IsHJReduced) : Q.rootMinus < 1 :=
  ((isHJReduced_iff_roots h.a_pos).mp h).2.1

/-- The selected root of a reduced form is above `1`. -/
theorem IsHJReduced.one_lt_rootPlus {Q : BinaryQF} (h : Q.IsHJReduced) : 1 < Q.rootPlus :=
  ((isHJReduced_iff_roots h.a_pos).mp h).2.2

/-- Both roots of a reduced irreducible form are irrational, so the expansion of
`SICs.SL2Z.HJExpansion` applies to them. -/
theorem IsHJReduced.irrational_rootPlus {Q : BinaryQF} (h : Q.IsHJReduced)
    (hirr : Q.IsIrreducible) : Irrational Q.rootPlus :=
  hirr.rootPlus_irrational h.disc_pos.le

/-! ### The rotation on forms

Substituting `β = b_0 - 1/γ` into the quadratic equation of `β` and clearing `γ²` gives the form
satisfied by the rotated number. It is the `GL₂(ℤ)` action of the Hirzebruch--Jung generator; it
preserves the discriminant and reducedness. -/

/-- One Hirzebruch--Jung rotation, realized on forms: `⟨a,b,c⟩ ↦ ⟨Q(b_0,1), -(2ab_0+b), a⟩` with
`b_0 = ⌈ρ_{Q,+}⌉`. Its selected root is the rotation `hjRotate ρ_{Q,+}` of
`SICs.SL2Z.HJExpansion` (`rootPlus_hjRotateForm`). -/
noncomputable def hjRotateForm (Q : BinaryQF) : BinaryQF where
  a := Q.eval (hjLetter Q.rootPlus) 1
  b := -(2 * Q.a * hjLetter Q.rootPlus + Q.b)
  c := Q.a

/-- The rotation preserves the discriminant. -/
@[simp] theorem disc_hjRotateForm (Q : BinaryQF) : Q.hjRotateForm.disc = Q.disc := by
  simp [disc, discrim, hjRotateForm, eval]
  ring

/-- The rotation preserves irreducibility, since it preserves the discriminant. -/
theorem isIrreducible_hjRotateForm {Q : BinaryQF} (hirr : Q.IsIrreducible) :
    Q.hjRotateForm.IsIrreducible := by
  simpa [IsIrreducible] using hirr

/-- **The rotated form has positive leading coefficient**: `Q(b_0,1) = a(b_0-β)(b_0-β')` with
`a > 0`, `b_0 - β ∈ (0,1)` and `b_0 - β' > 1`. -/
theorem a_hjRotateForm_pos {Q : BinaryQF} (h : Q.IsHJReduced)
    (hirr : Q.IsIrreducible) : 0 < Q.hjRotateForm.a := by
  have haR : 0 < (Q.a : ℝ) := by exact_mod_cast h.a_pos
  have hletterPlus : 0 < (hjLetter Q.rootPlus : ℝ) - Q.rootPlus :=
    hjLetter_sub_pos (h.irrational_rootPlus hirr)
  have hletterR : (2 : ℝ) ≤ hjLetter Q.rootPlus := by
    exact_mod_cast two_le_hjLetter h.one_lt_rootPlus
  have hletterMinus : 1 < (hjLetter Q.rootPlus : ℝ) - Q.rootMinus := by
    linarith [h.rootMinus_lt_one]
  have hfactor := eval_one_factorization Q (hjLetter Q.rootPlus) h.a_pos.ne' h.disc_pos.le
  have heval : 0 < (Q.eval (hjLetter Q.rootPlus) 1 : ℝ) := by
    rw [hfactor]
    positivity
  exact_mod_cast heval

/-- **Both roots of the rotated form, in one computation.** For any root `ρ` of `Q` distinct from
the partial quotient `b_0 = ⌈ρ_{Q,+}⌉`,

```text
(2a b_0 + b + (2aρ + b)) / (2 Q(b_0,1)) = 1/(b_0 - ρ),
```

because `(b_0 - ρ)·(2a b_0 + b + (2aρ + b)) = 2 Q(b_0,1)` whenever `aρ² + bρ + c = 0`. Since
`2aρ_{Q,±} + b = ±√Δ`, the two roots of `Q.hjRotateForm` are the two instances of this identity;
that is `rootPlus_hjRotateForm` and `rootMinus_hjRotateForm`. -/
private lemma hjRotateForm_root_aux {Q : BinaryQF} (h : Q.IsHJReduced) (hirr : Q.IsIrreducible)
    {ρ : ℝ} (hρ : (Q.a : ℝ) * ρ ^ 2 + (Q.b : ℝ) * ρ + (Q.c : ℝ) = 0)
    (hne : (hjLetter Q.rootPlus : ℝ) - ρ ≠ 0) :
    (2 * (Q.a : ℝ) * (hjLetter Q.rootPlus : ℝ) + (Q.b : ℝ) + (2 * (Q.a : ℝ) * ρ + (Q.b : ℝ))) /
        (2 * (Q.eval (hjLetter Q.rootPlus) 1 : ℝ)) =
      ((hjLetter Q.rootPlus : ℝ) - ρ)⁻¹ := by
  have heval : (Q.eval (hjLetter Q.rootPlus) 1 : ℝ) ≠ 0 := by
    exact_mod_cast (a_hjRotateForm_pos h hirr).ne'
  have hkey :
      ((hjLetter Q.rootPlus : ℝ) - ρ) *
          (2 * (Q.a : ℝ) * (hjLetter Q.rootPlus : ℝ) + (Q.b : ℝ) +
            (2 * (Q.a : ℝ) * ρ + (Q.b : ℝ))) =
        2 * (Q.eval (hjLetter Q.rootPlus) 1 : ℝ) := by
    simp only [eval, Int.cast_add, Int.cast_mul, Int.cast_pow, one_pow, mul_one]
    linear_combination (-2 : ℝ) * hρ
  field_simp
  linear_combination hkey

/-- **The rotation acts on the selected root as one Hirzebruch--Jung step**:
`ρ_{Q',+} = 1/(⌈ρ_{Q,+}⌉ - ρ_{Q,+})`. -/
theorem rootPlus_hjRotateForm {Q : BinaryQF} (h : Q.IsHJReduced) (hirr : Q.IsIrreducible) :
    Q.hjRotateForm.rootPlus = hjRotate Q.rootPlus := by
  have hsqrt := two_mul_a_mul_rootPlus Q h.a_pos.ne'
  have hnum : Q.hjRotateForm.rootPlus =
      (2 * (Q.a : ℝ) * (hjLetter Q.rootPlus : ℝ) + (Q.b : ℝ) +
          (2 * (Q.a : ℝ) * Q.rootPlus + (Q.b : ℝ))) /
        (2 * (Q.eval (hjLetter Q.rootPlus) 1 : ℝ)) := by
    rw [rootPlus, disc_hjRotateForm]
    simp only [hjRotateForm]
    push_cast
    rw [hsqrt]
    ring
  rw [hnum, hjRotate]
  exact hjRotateForm_root_aux h hirr
    (rootPlus_satisfies_quadratic_of_disc_nonneg Q h.a_pos.ne' h.disc_pos.le)
    (hjLetter_sub_pos (h.irrational_rootPlus hirr)).ne'

/-- **The rotation acts on the conjugate root by the same formula**:
`ρ_{Q',-} = 1/(⌈ρ_{Q,+}⌉ - ρ_{Q,-})`. This is Katok's relation `β'_{i+1} = 1/(b_i - β'_i)`,
[68, Katok (2003), equation (1.1.5)], and it is what makes the rotation invertible. -/
@[source "68, equation (1.1.5), p. 6 (roots of a reduced form)"]
theorem rootMinus_hjRotateForm {Q : BinaryQF} (h : Q.IsHJReduced) (hirr : Q.IsIrreducible) :
    Q.hjRotateForm.rootMinus = ((hjLetter Q.rootPlus : ℝ) - Q.rootMinus)⁻¹ := by
  have hletterR : (2 : ℝ) ≤ (hjLetter Q.rootPlus : ℝ) := by
    exact_mod_cast two_le_hjLetter h.one_lt_rootPlus
  have hgap : 0 < (hjLetter Q.rootPlus : ℝ) - Q.rootMinus := by
    linarith [h.rootMinus_lt_one]
  have hsqrt := two_mul_a_mul_rootMinus Q h.a_pos.ne'
  have hnum : Q.hjRotateForm.rootMinus =
      (2 * (Q.a : ℝ) * (hjLetter Q.rootPlus : ℝ) + (Q.b : ℝ) +
          (2 * (Q.a : ℝ) * Q.rootMinus + (Q.b : ℝ))) /
        (2 * (Q.eval (hjLetter Q.rootPlus) 1 : ℝ)) := by
    rw [rootMinus, disc_hjRotateForm]
    simp only [hjRotateForm]
    push_cast
    rw [hsqrt]
    ring
  rw [hnum]
  exact hjRotateForm_root_aux h hirr
    (rootMinus_satisfies_quadratic_of_disc_nonneg Q h.a_pos.ne' h.disc_pos.le)
    hgap.ne'

/-- **The rotation preserves reducedness**, Katok's induction `0 < β'_i < 1` in the proof of
[68, Katok (2003), Theorem 1.4]. -/
theorem isHJReduced_hjRotateForm {Q : BinaryQF} (h : Q.IsHJReduced)
    (hirr : Q.IsIrreducible) : Q.hjRotateForm.IsHJReduced := by
  apply (isHJReduced_iff_roots (a_hjRotateForm_pos h hirr)).2
  have hletterR : (2 : ℝ) ≤ hjLetter Q.rootPlus := by
    exact_mod_cast two_le_hjLetter h.one_lt_rootPlus
  have hminusGap : 1 < (hjLetter Q.rootPlus : ℝ) - Q.rootMinus := by
    linarith [h.rootMinus_lt_one]
  have hminusGapPos : 0 < (hjLetter Q.rootPlus : ℝ) - Q.rootMinus :=
    lt_trans zero_lt_one hminusGap
  constructor
  · rw [rootMinus_hjRotateForm h hirr]
    exact inv_pos.mpr hminusGapPos
  constructor
  · rw [rootMinus_hjRotateForm h hirr, inv_lt_one₀ hminusGapPos]
    exact hminusGap
  · rw [rootPlus_hjRotateForm h hirr]
    exact one_lt_hjRotate (h.irrational_rootPlus hirr)

/-! ### Iterating the rotation

The invariants of one step propagate, so the whole rotation orbit of a reduced irreducible form
consists of reduced irreducible forms of the same discriminant, and its selected roots are the
rotated numbers `β_n` of [72, Kopp (2024), Definition 7.4, `defn:cycledata`]. -/

/-- Every form in the rotation orbit has the same discriminant. -/
@[simp] theorem disc_hjRotateForm_iterate (Q : BinaryQF) (n : ℕ) :
    (hjRotateForm^[n] Q).disc = Q.disc := by
  induction n generalizing Q with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih, disc_hjRotateForm]

/-- Every form in the rotation orbit of a reduced irreducible form is reduced and irreducible. -/
theorem isHJReduced_hjRotateForm_iterate {Q : BinaryQF} (h : Q.IsHJReduced)
    (hirr : Q.IsIrreducible) (n : ℕ) :
    (hjRotateForm^[n] Q).IsHJReduced ∧ (hjRotateForm^[n] Q).IsIrreducible := by
  induction n generalizing Q with
  | zero => exact ⟨h, hirr⟩
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih (isHJReduced_hjRotateForm h hirr) (isIrreducible_hjRotateForm hirr)

/-- **The orbit's selected roots are Kopp's rotated numbers**: `ρ_{Q_n,+} = β_n` for
`β = ρ_{Q,+}`. -/
theorem rootPlus_hjRotateForm_iterate {Q : BinaryQF} (h : Q.IsHJReduced)
    (hirr : Q.IsIrreducible) (n : ℕ) :
    (hjRotateForm^[n] Q).rootPlus = hjPeriod Q.rootPlus n := by
  induction n generalizing Q with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply,
        ih (isHJReduced_hjRotateForm h hirr) (isIrreducible_hjRotateForm hirr),
        hjPeriod_succ_left, rootPlus_hjRotateForm h hirr]

/-! ### Finiteness and injectivity

The two inputs to pure periodicity. Finiteness comes from the reduced box `2(a+c) < Δ`;
injectivity from reading the previous partial quotient off the conjugate root. -/

/-- **The reduced box.** A reduced form has coefficients confined to an interval determined by
its discriminant: `1 ≤ a, c ≤ Δ` from `2(a+c) < Δ`, and then `|b| ≤ 1 + 2Δ` from
`b² = Δ + 4ac`. This is the finiteness step in the proof of [68, Katok (2003), Theorem 1.3],
with Katok's divisibility argument for `ℓ` replaced by the integer bound
`IsHJReduced.two_mul_add_lt_disc`. -/
private lemma mem_reduced_box {Q : BinaryQF} (h : Q.IsHJReduced) :
    Q.a ∈ Set.Icc 1 Q.disc ∧ Q.b ∈ Set.Icc (-(1 + 2 * Q.disc)) (1 + 2 * Q.disc) ∧
      Q.c ∈ Set.Icc 1 Q.disc := by
  have haPos := h.a_pos
  have hcPos := h.c_pos
  have hbox := h.two_mul_add_lt_disc
  have haΔ : Q.a ≤ Q.disc := by omega
  have hcΔ : Q.c ≤ Q.disc := by omega
  have hac : Q.a * Q.c ≤ Q.disc * Q.disc := mul_le_mul haΔ hcΔ (by omega) (by omega)
  have hb2 : Q.b ^ 2 = Q.disc + 4 * Q.a * Q.c := by rw [disc_eq_coefficients]; ring
  have hsq : Q.b ^ 2 < (1 + 2 * Q.disc) ^ 2 := by nlinarith
  exact ⟨⟨by omega, haΔ⟩, ⟨by nlinarith, by nlinarith⟩, by omega, hcΔ⟩

/-- **Only finitely many reduced forms have a given discriminant**, by the reduced box
`mem_reduced_box`. -/
theorem finite_setOf_isHJReduced (Δ : ℤ) :
    {Q : BinaryQF | Q.disc = Δ ∧ Q.IsHJReduced}.Finite := by
  refine Set.Finite.of_finite_image (f := fun Q ↦ (Q.a, Q.b, Q.c)) ?_ ?_
  · refine ((Set.finite_Icc 1 Δ).prod
      ((Set.finite_Icc (-(1 + 2 * Δ)) (1 + 2 * Δ)).prod (Set.finite_Icc 1 Δ))).subset ?_
    rintro _ ⟨Q, ⟨hdisc, hred⟩, rfl⟩
    obtain ⟨ha, hb, hc⟩ := mem_reduced_box hred
    rw [hdisc] at ha hb hc
    exact ⟨ha, hb, hc⟩
  · intro Q₁ _ Q₂ _ heq
    simp only [Prod.mk.injEq] at heq
    exact BinaryQF.ext heq.1 heq.2.1 heq.2.2

/-- Taking the ceiling of `k - x` recovers `k` when `x` lies in `[0,1)`. -/
private lemma ceil_intCast_sub_eq (k : ℤ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ⌈(k : ℝ) - x⌉ = k := by
  rw [Int.ceil_eq_iff]
  constructor <;> linarith

/-- **The rotation is injective on reduced irreducible forms.** The previous partial quotient is
`b_0 = ⌈1/ρ_{Q',-}⌉`, because `ρ_{Q',-} = 1/(b_0 - ρ_{Q,-})` with `ρ_{Q,-} ∈ (0,1)` irrational;
knowing `b_0` and `Q'` returns `Q` by the coefficient formulas. This is the step
"`b_{i-1} = ⌊1/β'_i⌋ + 1`" of [68, Katok (2003), Theorem 1.4]. -/
theorem hjRotateForm_injOn :
    Set.InjOn hjRotateForm {Q : BinaryQF | Q.IsHJReduced ∧ Q.IsIrreducible} := by
  rintro Q₁ ⟨h₁, hirr₁⟩ Q₂ ⟨h₂, hirr₂⟩ heq
  have ha : Q₁.a = Q₂.a := by
    have hout := congrArg BinaryQF.c heq
    simpa [hjRotateForm] using hout
  have hroot := congrArg rootMinus heq
  rw [rootMinus_hjRotateForm h₁ hirr₁, rootMinus_hjRotateForm h₂ hirr₂] at hroot
  have hbase :
      (hjLetter Q₁.rootPlus : ℝ) - Q₁.rootMinus =
        (hjLetter Q₂.rootPlus : ℝ) - Q₂.rootMinus :=
    inv_injective hroot
  have hletter : hjLetter Q₁.rootPlus = hjLetter Q₂.rootPlus := by
    have hceil := congrArg Int.ceil hbase
    rw [ceil_intCast_sub_eq _ h₁.rootMinus_pos.le h₁.rootMinus_lt_one,
      ceil_intCast_sub_eq _ h₂.rootMinus_pos.le h₂.rootMinus_lt_one] at hceil
    exact hceil
  have hb : Q₁.b = Q₂.b := by
    have hout := congrArg BinaryQF.b heq
    simp only [hjRotateForm] at hout
    rw [ha, hletter] at hout
    omega
  have hc : Q₁.c = Q₂.c := by
    have hout := congrArg BinaryQF.a heq
    change Q₁.eval (hjLetter Q₁.rootPlus) 1 =
      Q₂.eval (hjLetter Q₂.rootPlus) 1 at hout
    simp only [eval, one_pow, mul_one] at hout
    rw [ha, hb, hletter] at hout
    omega
  exact BinaryQF.ext ha hb hc

/-- Every iterate of the rotation is injective on reduced irreducible forms. -/
private lemma hjRotateForm_iterate_injOn (m : ℕ) :
    Set.InjOn (hjRotateForm^[m]) {Q : BinaryQF | Q.IsHJReduced ∧ Q.IsIrreducible} := by
  exact hjRotateForm_injOn.iterate (fun _ h ↦
    ⟨isHJReduced_hjRotateForm h.1 h.2, isIrreducible_hjRotateForm h.2⟩) m

/-! ### Purely periodic expansions

The rotation orbit of a reduced irreducible form lives in a finite set, so it repeats; injectivity
pulls the repeat back to the start. -/

/-- **The rotation orbit of a reduced irreducible form closes up**: `Q_ℓ = Q` for some `ℓ ≥ 1`.
-/
theorem exists_hjRotateForm_iterate_eq_self {Q : BinaryQF} (h : Q.IsHJReduced)
    (hirr : Q.IsIrreducible) : ∃ ℓ, 0 < ℓ ∧ hjRotateForm^[ℓ] Q = Q := by
  let t : Set BinaryQF := {Q' | Q'.disc = Q.disc ∧ Q'.IsHJReduced}
  have hmaps : Set.MapsTo (fun n ↦ hjRotateForm^[n] Q) (Set.univ : Set ℕ) t := by
    intro n _
    exact ⟨disc_hjRotateForm_iterate Q n, (isHJReduced_hjRotateForm_iterate h hirr n).1⟩
  obtain ⟨j, -, k, -, hjk, heq⟩ :=
    Set.Infinite.exists_ne_map_eq_of_mapsTo Set.infinite_univ hmaps
      (finite_setOf_isHJReduced Q.disc)
  have close {j k : ℕ} (hlt : j < k)
      (heq : hjRotateForm^[j] Q = hjRotateForm^[k] Q) :
      ∃ ℓ, 0 < ℓ ∧ hjRotateForm^[ℓ] Q = Q := by
    refine ⟨k - j, Nat.sub_pos_of_lt hlt, ?_⟩
    apply hjRotateForm_iterate_injOn j
    · exact isHJReduced_hjRotateForm_iterate h hirr (k - j)
    · exact ⟨h, hirr⟩
    rw [← Function.iterate_add_apply, Nat.add_sub_of_le hlt.le]
    exact heq.symm
  rcases lt_or_gt_of_ne hjk with hjk | hkj
  · exact close hjk heq
  · exact close hkj heq.symm

/-- **The sufficiency direction of [72, Kopp (2024), Proposition 7.2, `prop:quadhj`]**: a
real quadratic number with `0 < β' < 1 < β` has a purely periodic Hirzebruch--Jung expansion,
`β_ℓ = β` for some `ℓ ≥ 1`. This is [68, Katok (2003), Theorem 1.4]; the proof is Katok's, run on
the coefficients of the form. -/
@[source "72, Proposition 7.2, p. 63, prop:quadhj (reduced implies purely periodic)"
  "68, Theorem 1.4, p. 5 (reduced implies purely periodic)"]
theorem exists_hjPeriod_rootPlus_eq {Q : BinaryQF} (h : Q.IsHJReduced) (hirr : Q.IsIrreducible) :
    ∃ ℓ, 0 < ℓ ∧ hjPeriod Q.rootPlus ℓ = Q.rootPlus := by
  obtain ⟨ℓ, hℓ, hclose⟩ := exists_hjRotateForm_iterate_eq_self h hirr
  refine ⟨ℓ, hℓ, ?_⟩
  rw [← rootPlus_hjRotateForm_iterate h hirr, hclose]

/-! ### The conjugate companion sequence

The conjugate roots `β'_n = ρ_{Q_n,-}` of the rotation orbit obey the same recursion
`β'_n = b_n - 1/β'_{n+1}` as the rotated numbers (`rootMinus_hjRotateForm`) and stay in `(0,1)`
(`isHJReduced_hjRotateForm_iterate`), so they form a companion sequence of the expansion of `β`
in the sense of `SICs.SL2Z.HJExpansion`, with values in `(0,1)`. This is Katok's sequence `x_i` in
the proof of [68, Katok (2003), Theorem 1.4], and it is the input `SICs.SL2Z.HJStabilizer` takes
in place of the Galois conjugate. Pure periodicity of `β` closes up the forms as well, because a
form with positive leading coefficient is determined by its discriminant and its root
(`eq_of_rootPlus_eq_of_disc_eq`), so the conjugate sequence is periodic with the same period. -/

/-- **The conjugate roots of the orbit lie in `(0,1)`**: `0 < β'_n < 1`. -/
theorem rootMinus_hjRotateForm_iterate_mem_Ioo {Q : BinaryQF} (h : Q.IsHJReduced)
    (hirr : Q.IsIrreducible) (n : ℕ) :
    0 < (hjRotateForm^[n] Q).rootMinus ∧ (hjRotateForm^[n] Q).rootMinus < 1 := by
  have hn := (isHJReduced_hjRotateForm_iterate h hirr n).1
  exact ⟨hn.rootMinus_pos, hn.rootMinus_lt_one⟩

/-- **The conjugate roots form a companion sequence of the expansion of `β`**:
`β'_n = ⌈β_n⌉ - 1/β'_{n+1}` with `β'_{n+1} ≠ 0`, from `rootMinus_hjRotateForm` at `Q_n` and
`rootPlus_hjRotateForm_iterate`. -/
theorem isHJCompanion_rootMinus_hjRotateForm_iterate {Q : BinaryQF} (h : Q.IsHJReduced)
    (hirr : Q.IsIrreducible) :
    IsHJCompanion Q.rootPlus (fun n ↦ (hjRotateForm^[n] Q).rootMinus) := by
  intro n
  let Qn := hjRotateForm^[n] Q
  have hn := isHJReduced_hjRotateForm_iterate h hirr n
  have hsucc : hjRotateForm^[n + 1] Q = Qn.hjRotateForm := by
    simpa [Qn] using Function.iterate_succ_apply' hjRotateForm n Q
  constructor
  · exact (rootMinus_hjRotateForm_iterate_mem_Ioo h hirr (n + 1)).1.ne'
  · change (hjRotateForm^[n] Q).rootMinus =
      (hjLetter (hjPeriod Q.rootPlus n) : ℝ) - 1 / (hjRotateForm^[n + 1] Q).rootMinus
    rw [hsucc, rootMinus_hjRotateForm hn.1 hn.2,
      ← rootPlus_hjRotateForm_iterate h hirr n]
    simp only [one_div, inv_inv]
    ring

/-- **A period of the root is a period of the form**: `β_ℓ = β` forces `Q_ℓ = Q`, since `Q_ℓ` is
reduced with the discriminant and the root of `Q` (`eq_of_rootPlus_eq_of_disc_eq`). -/
theorem hjRotateForm_iterate_eq_self_of_hjPeriod_eq {Q : BinaryQF} (h : Q.IsHJReduced)
    (hirr : Q.IsIrreducible) {ℓ : ℕ} (hℓ : hjPeriod Q.rootPlus ℓ = Q.rootPlus) :
    hjRotateForm^[ℓ] Q = Q := by
  apply eq_of_rootPlus_eq_of_disc_eq hirr h.disc_pos.le h.a_pos
    (isHJReduced_hjRotateForm_iterate h hirr ℓ).1.a_pos
    (disc_hjRotateForm_iterate Q ℓ)
  rw [rootPlus_hjRotateForm_iterate h hirr ℓ, hℓ]

/-- **The conjugate sequence has every period of `β`**: `β'_ℓ = β'` when `β_ℓ = β`. -/
theorem rootMinus_hjRotateForm_iterate_of_hjPeriod_eq {Q : BinaryQF} (h : Q.IsHJReduced)
    (hirr : Q.IsIrreducible) {ℓ : ℕ} (hℓ : hjPeriod Q.rootPlus ℓ = Q.rootPlus) :
    (hjRotateForm^[ℓ] Q).rootMinus = Q.rootMinus := by
  rw [hjRotateForm_iterate_eq_self_of_hjPeriod_eq h hirr hℓ]

end BinaryQF

end SIC
