/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import SICs.Source

/-!
# Dedekind Sums and the Rademacher Class Invariant

Dedekind sums, their symmetries, and the Rademacher class invariant `Ψ`.

This file develops the rational sawtooth function, its Dedekind sums, and the Rademacher class
invariant `Ψ(M)` used in the Shintani--Faddeev phase. Inversion negates the invariant. The
reciprocity law for `𝔰`, and the values of `𝔰` it yields, are in `SICs.SL2Z.DedekindReciprocity`.

## Main definitions and results

- `dedekindSawtooth`: the periodic sawtooth function `((x))`.
- `dedekindSum`: the Dedekind sum `𝔰(a,b)`.
- `dedekindSum_eq_of_mul_modEq_one`: invariance under replacing the first argument by its
  multiplicative inverse modulo the second.
- `rademacherInvariant`: the class invariant `Ψ(M)` of [AFK25, Definition 1.29, `df:meyinv`].
- `rademacherInvariant_inv`: inversion negates `Ψ`, [AFK25, Proposition 5.1,
  `lem:RademacherProperties`, `eq:mypm1`].

## References

- [AFK25, Definition 1.29, `df:meyinv`]
- [72, Kopp (2024), equation (2.5), `eq:Phi`], the Rademacher function `Φ = Ψ + 3·sgn(c·Tr)`
- [86] H. Rademacher, "Zur Theorie der Dedekindschen Summen", Math. Z. 63:445--463, 1955,
  Satz 7, equation (11)
- [88] H. Rademacher and E. Grosswald, "Dedekind Sums", Carus Mathematical Monographs 16,
  Mathematical Association of America, 1972, equations (1), (2), (33a)--(33c), (59), and (63)
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### Rademacher class invariant

The Dedekind sawtooth and sum define the integer-valued Rademacher invariant `Ψ(M)` from [AFK25,
Definition 1.29, `df:meyinv`].  The ensuing formulas reduce it to explicit matrix entries and
control the root-of-unity phase in ghost overlaps. -/

/-- The Dedekind sawtooth function `((x)) = x - ⌊x⌋ - 1/2` for `x ∉ ℤ` and `((x)) = 0` for
    `x ∈ ℤ`. See [AFK25, Definition 1.29, `df:meyinv`, equation (1.43), `eq:dedekindsum`] and
    [88, Rademacher and Grosswald (1972), equation (2), p. 1]. -/
@[source "88, equation (2), p. 1" "AFK25, equation (1.43), p. 16, eq:dedekindsum (sawtooth)"
  (symbol := "((x))")]
noncomputable def dedekindSawtooth (x : ℚ) : ℚ := if x.den = 1 then 0 else x - ⌊x⌋ - 1/2

/-- The sawtooth function vanishes at every integer. -/
@[simp]
lemma dedekindSawtooth_of_den_eq_one {x : ℚ} (h : x.den = 1) : dedekindSawtooth x = 0 := by
  unfold dedekindSawtooth
  simp [h]

/-- A rational number has trivial denominator exactly when its fractional part vanishes. -/
lemma den_eq_one_iff_fract_eq_zero (x : ℚ) : x.den = 1 ↔ Int.fract x = 0 := by
  rw [Int.fract_eq_zero_iff]
  constructor
  · intro h
    exact ⟨x.num, (Rat.den_eq_one_iff x).mp h⟩
  · rintro ⟨z, hz⟩
    rw [← hz]
    simp

/-- Away from the integers, the sawtooth function is the fractional part shifted down by `1/2`. -/
lemma dedekindSawtooth_of_fract_ne_zero {x : ℚ} (h : Int.fract x ≠ 0) :
    dedekindSawtooth x = Int.fract x - 1 / 2 := by
  have hden : x.den ≠ 1 := fun hc => h ((den_eq_one_iff_fract_eq_zero x).mp hc)
  unfold dedekindSawtooth
  rw [ite_eq_right hden, Int.fract]

/-- The sawtooth function is odd. Stated as `((-x)) = -((x))` at
    [88, Rademacher and Grosswald (1972), p. 26], where it is what gives equation (33a). -/
lemma dedekindSawtooth_neg (x : ℚ) : dedekindSawtooth (-x) = -dedekindSawtooth x := by
  rcases eq_or_ne (Int.fract x) 0 with h | h
  · have hx : x.den = 1 := (den_eq_one_iff_fract_eq_zero x).mpr h
    have hnx : (-x).den = 1 :=
      (den_eq_one_iff_fract_eq_zero (-x)).mpr (Int.fract_neg_eq_zero.mpr h)
    simp [dedekindSawtooth_of_den_eq_one hx, dedekindSawtooth_of_den_eq_one hnx]
  · have hnx : Int.fract (-x) ≠ 0 := Int.fract_neg_eq_zero.not.mpr h
    rw [dedekindSawtooth_of_fract_ne_zero h, dedekindSawtooth_of_fract_ne_zero hnx,
      Int.fract_neg h]
    ring

/-- The sawtooth function is invariant under shifting its argument by an integer: it is the
    "sawtooth function of period 1" of [88, Rademacher and Grosswald (1972), p. 1], immediately
    after equation (2). -/
lemma dedekindSawtooth_add_intCast (x : ℚ) (k : ℤ) :
    dedekindSawtooth (x + (k : ℚ)) = dedekindSawtooth x := by
  rcases eq_or_ne (Int.fract x) 0 with h | h
  · have hx' : Int.fract (x + (k : ℚ)) = 0 := by rw [Int.fract_add_intCast]; exact h
    have hx : x.den = 1 := (den_eq_one_iff_fract_eq_zero x).mpr h
    have hx'' : (x + (k : ℚ)).den = 1 := (den_eq_one_iff_fract_eq_zero _).mpr hx'
    simp [dedekindSawtooth_of_den_eq_one hx, dedekindSawtooth_of_den_eq_one hx'']
  · have hx' : Int.fract (x + (k : ℚ)) ≠ 0 := by rw [Int.fract_add_intCast]; exact h
    rw [dedekindSawtooth_of_fract_ne_zero h, dedekindSawtooth_of_fract_ne_zero hx',
      Int.fract_add_intCast]

/-- The Dedekind sum `𝔰(a, b)` for integers `a`, `b` with `b ≠ 0`:
      `𝔰(a, b) = Σ_{n=1}^{|b|-1} ((n/b)) · ((na/b))`
    where ((x)) = x - ⌊x⌋ - 1/2 for x ∉ ℤ and ((x)) = 0 for x ∈ ℤ.
    See [AFK25, Definition 1.29, `df:meyinv`, equation (1.43), `eq:dedekindsum`] and
    [88, Rademacher and Grosswald (1972), equation (1), p. 1]. The classical `s(h,k)` is defined
    only for `k ≥ 1` and `(h,k) = 1`, and sums to `k` rather than `|k| - 1`; the extra term
    vanishes, and this definition drops both restrictions, agreeing with `s` where both apply.

    The source defines `𝔰(a, b)` only for `b ≠ 0`. The definition here is total, taking the junk
    value `𝔰(a, 0) = 0` by the Mathlib convention for out-of-domain arguments; this is a choice of
    convention outside the source's domain, not a simplification of the source concept. -/
@[source "88, equation (1), p. 1" "AFK25, equation (1.43), p. 16, eq:dedekindsum (Dedekind sum)"
  (symbol := "s(h, k)")]
noncomputable def dedekindSum (a b : ℤ) : ℚ :=
  ∑ n ∈ Finset.range (b.natAbs - 1),
    let nn := (n + 1 : ℤ)
    dedekindSawtooth (nn / b) * dedekindSawtooth (nn * a / b)

/-- The Dedekind sum vanishes at second argument `0`, the junk value fixed by `dedekindSum`'s
totalizing convention outside the source's domain. -/
@[simp]
lemma dedekindSum_of_snd_eq_zero (a : ℤ) : dedekindSum a 0 = 0 := by
  simp [dedekindSum]

/-- The Dedekind sum is odd in its first argument, `𝔰(-a, b) = -𝔰(a, b)`.
    See [88, Rademacher and Grosswald (1972), equation (33a), p. 26]. -/
@[source "88, equation (33a), p. 26"]
lemma dedekindSum_neg_left (a b : ℤ) :
    dedekindSum (-a) b = -dedekindSum a b := by
  unfold dedekindSum
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n _
  dsimp only
  push_cast
  have key : ((n : ℚ) + 1) * (-(a : ℚ)) / (b : ℚ) = -(((n : ℚ) + 1) * (a : ℚ) / (b : ℚ)) := by
    ring
  rw [key, dedekindSawtooth_neg]
  ring

/-- The Dedekind sum is even in its second argument, `𝔰(a, -b) = 𝔰(a, b)`.
    See [88, Rademacher and Grosswald (1972), equation (33b), p. 26]. -/
@[source "88, equation (33b), p. 26"]
lemma dedekindSum_neg_right (a b : ℤ) :
    dedekindSum a (-b) = dedekindSum a b := by
  unfold dedekindSum
  simp only [Int.natAbs_neg]
  apply Finset.sum_congr rfl
  intro n _
  rw [show ((n + 1 : ℤ) : ℚ) / ((-b : ℤ) : ℚ) =
      -(((n + 1 : ℤ) : ℚ) / (b : ℚ)) by push_cast; ring,
    show ((n + 1 : ℤ) : ℚ) * (a : ℚ) / ((-b : ℤ) : ℚ) =
      -(((n + 1 : ℤ) : ℚ) * (a : ℚ) / (b : ℚ)) by push_cast; ring,
    dedekindSawtooth_neg, dedekindSawtooth_neg]
  ring

/-- The Dedekind sum is invariant under shifting its first argument by an integer multiple of the
second. This is immediate from the residue-system form
`𝔰(h, k) = Σ_{μ mod k} ((μ/k))·((hμ/k))` written at
[88, Rademacher and Grosswald (1972), p. 26], in which `h` enters only modulo `k`. -/
lemma dedekindSum_add_mul_right (a b k : ℤ) :
    dedekindSum (a + k * b) b = dedekindSum a b := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp only [dedekindSum_of_snd_eq_zero]
  unfold dedekindSum
  apply Finset.sum_congr rfl
  intro n _
  dsimp only
  push_cast
  have key : ((n : ℚ) + 1) * ((a : ℚ) + (k : ℚ) * (b : ℚ)) / (b : ℚ) =
      ((n : ℚ) + 1) * (a : ℚ) / (b : ℚ) + ((((n : ℤ) + 1) * k : ℤ) : ℚ) := by
    push_cast
    field_simp
  rw [key, dedekindSawtooth_add_intCast]

/-- The sawtooth function evaluated at a nonnegative fraction `a / b` whose quotient by Euclidean
division is the known value `j`. -/
lemma dedekindSawtooth_natCast_div_of_bounds {a b j : ℕ} (hb : 0 < b)
    (hlo : j * b ≤ a) (hhi : a < (j + 1) * b) (hne : a ≠ j * b) :
    dedekindSawtooth ((a : ℚ) / (b : ℚ)) = (a : ℚ) / (b : ℚ) - (j : ℚ) - 1 / 2 := by
  have hdiv : a / b = j := Nat.div_eq_of_lt_le hlo hhi
  have hfloor : ⌊(a : ℚ) / (b : ℚ)⌋ = (j : ℤ) := by
    rw [Rat.floor_natCast_div_natCast]
    exact_mod_cast hdiv
  have hfract : Int.fract ((a : ℚ) / (b : ℚ)) ≠ 0 := by
    rw [Int.fract, hfloor]
    have hb' : (b : ℚ) ≠ 0 := by positivity
    intro hcontra
    rw [sub_eq_zero, div_eq_iff hb'] at hcontra
    exact hne (by exact_mod_cast hcontra)
  rw [dedekindSawtooth_of_fract_ne_zero hfract, Int.fract, hfloor]
  push_cast
  ring

/-- Reindex the Dedekind sum, for a nonnegative denominator given as a natural-number cast, as a
sum over the shifted range `Ico 1 γ`. -/
lemma dedekindSum_eq_sum_Ico (a : ℤ) (γ : ℕ) :
    dedekindSum a (γ : ℤ) =
      ∑ r ∈ Finset.Ico 1 γ,
        dedekindSawtooth ((r : ℚ) / (γ : ℚ)) * dedekindSawtooth ((r : ℚ) * (a : ℚ) / (γ : ℚ)) := by
  rw [Finset.sum_Ico_eq_sum_range]
  unfold dedekindSum
  simp only [Int.natAbs_natCast]
  apply Finset.sum_congr rfl
  intro k _
  congr 2 <;> push_cast <;> ring

/-! ### Invariance under modular inversion

The proof of `𝔰(a⁻¹, b) = 𝔰(a, b)` follows [88, Rademacher and Grosswald (1972), equation (33c)]
literally: write the defining sum over all residue classes modulo `|b|`, then reindex by
multiplication by the unit represented by `a`. The private lemmas below only bridge the range-based
definition to that finite-ring sum. -/

/-- The sawtooth of `x / k` depends only on the residue class of `x` modulo `k`. This is the
periodicity step used by `dedekindSum_eq_of_mul_modEq_one`. -/
private lemma dedekindSawtooth_div_eq_of_modEq {x y k : ℤ} (hk : k ≠ 0)
    (hxy : x ≡ y [ZMOD k]) :
    dedekindSawtooth ((x : ℚ) / (k : ℚ)) =
      dedekindSawtooth ((y : ℚ) / (k : ℚ)) := by
  rw [Int.modEq_iff_dvd] at hxy
  obtain ⟨q, hq⟩ := hxy
  have hrat : (y : ℚ) / (k : ℚ) = (x : ℚ) / (k : ℚ) + (q : ℚ) := by
    have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast hk
    have hqQ : (y : ℚ) - (x : ℚ) = (k : ℚ) * (q : ℚ) := by exact_mod_cast hq
    field_simp [hkQ]
    linear_combination hqQ
  rw [hrat, dedekindSawtooth_add_intCast]

/-- Replacing a product by its least nonnegative residue does not change the sawtooth factor in
the residue-class form of `dedekindSum_eq_of_mul_modEq_one`. -/
private lemma dedekindSawtooth_val_mul {k : ℕ} [NeZero k] (a : ℤ) (x : ZMod k) :
    dedekindSawtooth ((((a : ZMod k) * x).val : ℕ) / (k : ℚ)) =
      dedekindSawtooth ((a : ℚ) * (x.val : ℚ) / (k : ℚ)) := by
  have hmod : (((a : ZMod k) * x).val : ℤ) ≡ a * (x.val : ℤ) [ZMOD (k : ℤ)] := by
    apply (ZMod.intCast_eq_intCast_iff _ _ k).mp
    push_cast
    simp only [ZMod.natCast_zmod_val]
  have h := dedekindSawtooth_div_eq_of_modEq
    (x := (((a : ZMod k) * x).val : ℤ)) (y := a * (x.val : ℤ)) (k := (k : ℤ))
    (by exact_mod_cast (NeZero.ne k)) hmod
  simpa only [Int.cast_natCast, Int.cast_mul] using h

/-- `dedekindSum` as a sum over the full range `{0, …, k-1}`. The term at zero vanishes, so this
only changes the indexing used by the defining sum. This is the full-residue-system form of
[88, Rademacher and Grosswald (1972), equation (1), p. 1]. -/
lemma dedekindSum_eq_sum_range (a : ℤ) (k : ℕ) (hk : 0 < k) :
    dedekindSum a (k : ℤ) =
      ∑ r ∈ Finset.range k, dedekindSawtooth ((r : ℚ) / (k : ℚ)) *
        dedekindSawtooth ((r : ℚ) * (a : ℚ) / (k : ℚ)) := by
  rw [dedekindSum_eq_sum_Ico, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hk]
  simp [dedekindSawtooth]

/-- The standard equivalence `Fin k ≃ ZMod k` preserves least nonnegative representatives. This
identifies the range sum with the residue-class sum below. -/
private lemma val_finEquiv {k : ℕ} [NeZero k] (i : Fin k) :
    (ZMod.finEquiv k i).val = i.val := by
  cases k with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ k => rfl

/-- The defining Dedekind sum written over all residue classes modulo a positive natural `k`.
This is the form on which multiplication by a unit acts as a permutation. -/
private lemma dedekindSum_eq_sum_zmod (a : ℤ) (k : ℕ) [NeZero k] (hk : 0 < k) :
    dedekindSum a (k : ℤ) =
      ∑ x : ZMod k,
        dedekindSawtooth ((x.val : ℚ) / (k : ℚ)) *
          dedekindSawtooth ((((a : ZMod k) * x).val : ℕ) / (k : ℚ)) := by
  rw [dedekindSum_eq_sum_range a k hk, ← Fin.sum_univ_eq_sum_range]
  apply Fintype.sum_equiv (ZMod.finEquiv k).toEquiv
  intro i
  have hval : ((ZMod.finEquiv k).toEquiv i).val = i.val := val_finEquiv i
  rw [hval, dedekindSawtooth_val_mul]
  congr 2
  rw [hval]
  ring

/-- Invariance under modular inversion for a positive modulus. This is the reindexing core of
`dedekindSum_eq_of_mul_modEq_one`. -/
private lemma dedekindSum_eq_of_mul_modEq_one_of_pos {a b c : ℤ} (hc : 0 < c)
    (hab : a * b ≡ 1 [ZMOD c]) :
    dedekindSum a c = dedekindSum b c := by
  let k := c.toNat
  have hk : 0 < k := by simpa [k] using hc
  have hkc : (k : ℤ) = c := by simp [k, hc.le]
  let _ : NeZero k := ⟨hk.ne'⟩
  have habZ : (a : ZMod k) * (b : ZMod k) = 1 := by
    rw [← Int.cast_mul, ← Int.cast_one, ZMod.intCast_eq_intCast_iff]
    simpa only [hkc] using hab
  let u : (ZMod k)ˣ := Units.mkOfMulEqOne (a : ZMod k) (b : ZMod k) habZ
  rw [← hkc, dedekindSum_eq_sum_zmod a k hk, dedekindSum_eq_sum_zmod b k hk]
  calc
    (∑ x : ZMod k,
        dedekindSawtooth ((x.val : ℚ) / (k : ℚ)) *
          dedekindSawtooth ((((a : ZMod k) * x).val : ℕ) / (k : ℚ))) =
        ∑ x : ZMod k,
          dedekindSawtooth ((((a : ZMod k) * x).val : ℕ) / (k : ℚ)) *
            dedekindSawtooth ((x.val : ℚ) / (k : ℚ)) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = ∑ x : ZMod k,
        dedekindSawtooth ((x.val : ℚ) / (k : ℚ)) *
          dedekindSawtooth ((((b : ZMod k) * x).val : ℕ) / (k : ℚ)) := by
      apply Fintype.sum_equiv u.mulLeft
      intro x
      simp only [u, Units.mulLeft_apply, Units.val_mkOfMulEqOne]
      rw [show (b : ZMod k) * ((a : ZMod k) * x) = x by
        rw [← mul_assoc, mul_comm (b : ZMod k) a, habZ, one_mul]]

/-- If `ab ≡ 1 (mod c)` and `c ≠ 0`, then `𝔰(a, c) = 𝔰(b, c)`.
    See [88, Rademacher and Grosswald (1972), equation (33c), p. 26]. The proof follows the
    source's reindexing by multiplication with `a` over the residue classes modulo `|c|`. -/
@[source "88, equation (33c), p. 26"]
lemma dedekindSum_eq_of_mul_modEq_one {a b c : ℤ} (hc : c ≠ 0)
    (hab : a * b ≡ 1 [ZMOD c]) :
    dedekindSum a c = dedekindSum b c := by
  rcases lt_or_gt_of_ne hc with hcneg | hcpos
  · have hab' : a * b ≡ 1 [ZMOD -c] := by
      rw [Int.modEq_iff_dvd] at hab ⊢
      exact neg_dvd.mpr hab
    calc
      dedekindSum a c = dedekindSum a (-c) := (dedekindSum_neg_right a c).symm
      _ = dedekindSum b (-c) := dedekindSum_eq_of_mul_modEq_one_of_pos (by omega) hab'
      _ = dedekindSum b c := dedekindSum_neg_right b c
  · exact dedekindSum_eq_of_mul_modEq_one_of_pos hcpos hab

/-- The Rademacher class invariant `Ψ(M)` for
    `M = [[α, β], [γ, δ]] ∈ SL₂(ℤ)`:
      Ψ(M) = Tr(M)/γ - 3·sgn(γ·Tr(M)) - 12·sgn(γ)·𝔰(α,γ)   if γ ≠ 0
              β/δ                                               if γ = 0
    The bundled special-linear-group argument encodes the determinant-one condition. This is the
    key ingredient in defining the SF phase.
    See [AFK25, Definition 1.29, `df:meyinv`], equation (1.42) and
    [86, Rademacher (1955), Satz 7, equation (11)] and
    [88, Rademacher and Grosswald (1972), equations (59), p. 49 and (63), p. 54]. [86] states the
    invariant in exactly this form, with the Dedekind sum written `s(a, |c|)`. [88] instead writes
    it as `s(δ, |γ|)`, since its `s` takes a positive second argument; that is the same value as
    `𝔰(α, γ)` by [88, Rademacher and Grosswald (1972), equations (33b) and (33c), p. 26], using
    `αδ ≡ 1 (mod γ)`. The book makes the same identification at [88, Rademacher and Grosswald
    (1972), p. 50]. -/
@[source "AFK25, Definition 1.29, p. 16, df:meyinv"
  "86, Satz 7, p. 449 (equation (11))"
  (symbol := "Ψ(M)")]
noncomputable def rademacherInvariant (M : SL(2, ℤ)) : ℚ :=
  let α := M 0 0
  let β := M 0 1
  let γ := M 1 0
  let δ := M 1 1
  let tr := α + δ
  if γ ≠ 0 then
    tr / γ - 3 * Int.sign (γ * tr) - 12 * Int.sign γ * dedekindSum α γ
  else
    β / δ

/-- `rademacherInvariant` unfolded on the branch the word walk uses, with the `let` bindings of
its definition spelled out. -/
lemma rademacherInvariant_of_lowerLeft_ne_zero (M : SL(2, ℤ)) (hγ : M 1 0 ≠ 0) :
    rademacherInvariant M =
      ((M 0 0 + M 1 1 : ℤ) : ℚ) / ((M 1 0 : ℤ) : ℚ) -
        3 * (Int.sign (M 1 0 * (M 0 0 + M 1 1)) : ℚ) -
        12 * (Int.sign (M 1 0) : ℚ) * dedekindSum (M 0 0) (M 1 0) := by
  unfold rademacherInvariant
  rw [ite_eq_left hγ]

/-! ### Inversion symmetry

The negative-lower-left branch of the word cocycle is evaluated through the inverse matrix. The
following source identity returns its phase from `Ψ(M⁻¹)` to `Ψ(M)`. -/

/-- **Inversion negates the Rademacher invariant:** `Ψ(M⁻¹) = -Ψ(M)`.

This is [AFK25, Proposition 5.1, equation (5.2), `lem:RademacherProperties`, `eq:mypm1`], citing
[86, Rademacher (1955), Satz 7] and [88, Rademacher and Grosswald (1972), Chapter 4, Section C].
For nonzero lower-left entry, the proof substitutes the adjugate formula into `Ψ` and uses
`dedekindSum_neg_right` and `dedekindSum_eq_of_mul_modEq_one`; the zero case is immediate from
the determinant-one condition. -/
@[source "AFK25, Proposition 5.1, p. 73, lem:RademacherProperties (Ψ(M⁻¹))"
  "86, Satz 7, p. 449 (equation (12), Ψ(M⁻¹))", simp]
theorem rademacherInvariant_inv (M : SL(2, ℤ)) :
    rademacherInvariant M⁻¹ = -rademacherInvariant M := by
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have h := M.2
    rw [Matrix.det_fin_two] at h
    exact h
  rcases eq_or_ne (M 1 0) 0 with hc | hc
  · have hdiag : M 0 0 = M 1 1 := by
      rw [hc, mul_zero, sub_zero] at hdet
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with h | h <;> omega
    unfold rademacherInvariant
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    simp [hc, hdiag]
    ring
  · have hinv : M⁻¹ 1 0 ≠ 0 := by
      rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      exact neg_ne_zero.mpr hc
    have hmod : M 0 0 * M 1 1 ≡ 1 [ZMOD M 1 0] := by
      rw [Int.modEq_iff_dvd]
      refine ⟨-M 0 1, ?_⟩
      linear_combination -hdet
    have hded : dedekindSum (M 1 1) (-M 1 0) = dedekindSum (M 0 0) (M 1 0) := by
      rw [dedekindSum_neg_right]
      exact (dedekindSum_eq_of_mul_modEq_one hc hmod).symm
    rw [rademacherInvariant_of_lowerLeft_ne_zero M⁻¹ hinv,
      rademacherInvariant_of_lowerLeft_ne_zero M hc,
      Matrix.SpecialLinearGroup.SL2_inv_expl]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hded, show -M 1 0 * (M 1 1 + M 0 0) =
      -(M 1 0 * (M 0 0 + M 1 1)) by ring, Int.sign_neg]
    rw [Int.sign_neg]
    push_cast
    ring

end SIC

end
