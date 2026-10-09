/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SL2Z.Characteristics
import SICs.SL2Z.HJExpansion

/-!
# Characteristics along a Hirzebruch--Jung expansion

Kopp's reduced characteristics `r_n` and Shintani arguments `w_n` along a Hirzebruch–Jung expansion,
with `0 < w_n < β_n + 1`, their shift and closing laws, the dual shift
`(w'_{n+1}-1)/x_{n+1} ≡ w'_n - 1` along any companion sequence, the reduced characteristics of
`-r`, and the phase sum `λ_r(A)` with Proposition 7.22, `λ_{-r} = λ_r`.

This file completes the Hirzebruch--Jung cycle data of [72, Kopp (2024), Definition 7.4,
`defn:cycledata`]. `SICs.SL2Z.HJExpansion` supplies the rotated numbers `β_n` and the cycle
matrices `A_{m,n}`; what remains is the pair of sequences attached to a rational characteristic
`r`,

$$
\mathbf r_n = \{A_{n,0}\mathbf r\},
\qquad w_n = \langle\!\langle \mathbf r_n, \beta_n\rangle\!\rangle,
$$

the reduced characteristics and the arguments at which the Stark--Tangedal--Yamamoto invariant
of [72, Kopp (2024), Definition 7.13, `defn:tangedalu`] evaluates the double sine.

## The reduction `{r}`

[72, Kopp (2024), Definition 7.3, `defn:fracpart`] reduces a characteristic by

$$
\{\mathbf r\} = \begin{pmatrix} r_1 - \lfloor r_1\rfloor - 1\\
                  r_2 - \lfloor r_2\rfloor\end{pmatrix},
$$

so `{r} ≡ r (mod ℤ²)` and `{r} = r` exactly when `-1 ≤ r₁ < 0` and `0 ≤ r₂ < 1`. The asymmetry
between the coordinates is deliberate: it puts the first coordinate in `[-1,0)` rather than
`[0,1)`, which is what makes the pairing `w = ⟨⟨r,β⟩⟩ = r₂β - r₁` *strictly positive*. Combined
with `r₂ < 1` and `-r₁ ≤ 1` it gives

$$
0 < w_n < \beta_n + 1
$$

(`fracSymplecticFormRat_hjReduceChar_pos`, `fracSymplecticFormRat_hjReduceChar_lt_add_one`), so
the base point `w_n - 1` lies in the chamber `(-1, β_n)` on which
`SICs.Cocycle.SigmaS.Reduction.sigmaSHonest_eq_sigmaS` evaluates the real `σ_S`. That is the reason
the reduction is part of the cycle data rather than a normalization of convenience.

## The two sequences

Since Kopp's `A_{n,0}` is the inverse of the cycle matrix `A_{0,n}`, the reduced characteristics
are `hjChar r β n = {A_{0,n}⁻¹ r}` and the arguments are `hjShintaniArg r β n = ⟨⟨r_n, β_n⟩⟩`.
Two facts make the sequence usable:

* nonintegrality is preserved, because the `SL₂(ℤ)` action and the reduction both preserve it
  (`not_isIntegralIndex_hjChar`) — this is the standing hypothesis `r ∉ ℤ²` of [72, Kopp (2024),
  Definition 7.4, `defn:cycledata`];
* consecutive characteristics are related by one Hirzebruch--Jung generator,
  `T^{b_n}S\,\mathbf r_{n+1} \equiv \mathbf r_n \pmod{\mathbb Z^2}`, because
  `A_{0,n+1} = A_{0,n}\,T^{b_n}S` and because the reduction only changes a characteristic by an
  integer vector, which the action of an integral matrix keeps integral. The proof of
  [72, Kopp (2024), Proposition 7.20, `prop:almost`] writes this relation as the equality
  `T^{b_{n-1}}S\mathbf r_n = \mathbf r_{n-1}`, which fails in general: for the form `⟨4,-6,1⟩`
  with `r = (-6/7, 3/7)`, so that `b_0 = 2`, one has `r_1 = (-4/7, 5/7)` and
  `T²S r_1 = (-13/7, -4/7) ≠ r_0`. The congruence is all that [72, Kopp (2024), Lemma 7.19,
  `lem:deltafrac2`] consumes, since that lemma reduces `T^bS\mathbf r` before evaluating.

Kopp's remaining piece of data, the exponent `k` with `A = P^k \in \Gamma_{\mathbf r}`, is not
specific to the expansion; the statements here take the closing condition `A_{0,N} ∈ Γ_r` as a
hypothesis.

## References

- [72, Kopp (2024), Definition 7.3, `defn:fracpart`] and [72, Kopp (2024), Definition 7.4,
  `defn:cycledata`].
- [AFK25, equation (1.24), `eq:FractionalSymplecticForm`]: the pairing `⟨⟨r,τ⟩⟩ = r₂τ - r₁`,
  which is `fracSymplecticFormRat` (`SICs.SL2Z.Characteristics`). Kopp writes the same
  pairing as `[[r, β]] = r₂β - r₁` ([72, Kopp (2024), Section 1.9, List of notation]); this file
  follows [AFK25]'s symbol.
- `SICs.SL2Z.HJExpansion`: the rotated numbers, the cycle matrices, and [72, Kopp (2024), Lemma 7.5,
  `lem:betajs`].
-/

open ModularGroup MatrixGroups

open scoped MatrixGroups

namespace SIC

/-! ### Kopp's reduction of a characteristic

The reduction sends each characteristic to the representative of its class modulo `ℤ²` with first
coordinate in `[-1,0)` and second in `[0,1)`. -/

/-- **Kopp's reduced representative** `{r}` of a characteristic modulo `ℤ²`, [72, Kopp (2024),
Definition 7.3, `defn:fracpart`]: `{r} = (r₁ - ⌊r₁⌋ - 1, r₂ - ⌊r₂⌋)`. Kopp's `rᵢ - ⌊rᵢ⌋` is the
fractional part `Int.fract rᵢ`, which is how it is written here. The subtracted `1` in the first
coordinate is the source's, and is what makes the pairing with a positive modulus positive (see
the file docstring). -/
@[source "72, Definition 7.3, p. 63, defn:fracpart" (symbol := "{r}")]
def hjReduceChar (r : Fin 2 → ℚ) : Fin 2 → ℚ :=
  fun i => Int.fract (r i) - (if i = 0 then 1 else 0)

/-- The first coordinate of the reduction: `{r}₁ = r₁ - ⌊r₁⌋ - 1`. -/
@[simp] theorem hjReduceChar_apply_zero (r : Fin 2 → ℚ) :
    hjReduceChar r 0 = Int.fract (r 0) - 1 := by
  simp [hjReduceChar]

/-- The second coordinate of the reduction: `{r}₂ = r₂ - ⌊r₂⌋`. -/
@[simp] theorem hjReduceChar_apply_one (r : Fin 2 → ℚ) : hjReduceChar r 1 = Int.fract (r 1) := by
  simp [hjReduceChar]

/-- **The reduction changes a characteristic by an integer vector**: `{r} ≡ r (mod ℤ²)`. -/
theorem hjReduceChar_sub_intVec (r : Fin 2 → ℚ) (i : Fin 2) :
    ∃ m : ℤ, hjReduceChar r i - r i = (m : ℚ) := by
  refine ⟨-⌊r i⌋ - (if i = 0 then 1 else 0), ?_⟩
  simp only [hjReduceChar, Int.fract]
  split <;> push_cast <;> ring

/-- The first coordinate of a reduced characteristic is at least `-1`. -/
theorem neg_one_le_hjReduceChar_apply_zero (r : Fin 2 → ℚ) : -1 ≤ hjReduceChar r 0 := by
  rw [hjReduceChar_apply_zero]
  linarith [Int.fract_nonneg (r 0)]

/-- The first coordinate of a reduced characteristic is negative. -/
theorem hjReduceChar_apply_zero_neg (r : Fin 2 → ℚ) : hjReduceChar r 0 < 0 := by
  rw [hjReduceChar_apply_zero]
  linarith [Int.fract_lt_one (r 0)]

/-- The second coordinate of a reduced characteristic is nonnegative. -/
theorem hjReduceChar_apply_one_nonneg (r : Fin 2 → ℚ) : 0 ≤ hjReduceChar r 1 := by
  rw [hjReduceChar_apply_one]
  exact Int.fract_nonneg (r 1)

/-- The second coordinate of a reduced characteristic is below `1`. -/
theorem hjReduceChar_apply_one_lt_one (r : Fin 2 → ℚ) : hjReduceChar r 1 < 1 := by
  rw [hjReduceChar_apply_one]
  exact Int.fract_lt_one (r 1)

/-- **The reduction depends only on the class modulo `ℤ²`.** This is what lets the reduction be
applied at any stage of a computation that only knows a characteristic up to integer vectors. -/
theorem hjReduceChar_congr {r s : Fin 2 → ℚ} (h : ∀ i, ∃ m : ℤ, r i - s i = (m : ℚ)) :
    hjReduceChar r = hjReduceChar s := by
  funext i
  obtain ⟨m, hm⟩ := h i
  simp only [hjReduceChar]
  rw [show r i = s i + (m : ℚ) by linarith, Int.fract_add_intCast]

/-- **The reduction is idempotent**: `{{r}} = {r}`, since `{r} ≡ r (mod ℤ²)`. -/
@[simp] theorem hjReduceChar_hjReduceChar (r : Fin 2 → ℚ) :
    hjReduceChar (hjReduceChar r) = hjReduceChar r :=
  hjReduceChar_congr (hjReduceChar_sub_intVec r)

/-- **The reduction preserves nonintegrality in both directions**, since it changes a
characteristic by an integer vector. -/
theorem isIntegralIndex_hjReduceChar_iff (r : Fin 2 → ℚ) :
    IsIntegralIndex (hjReduceChar r) ↔ IsIntegralIndex r := by
  constructor
  · intro h i
    obtain ⟨m, hm⟩ := h i
    obtain ⟨k, hk⟩ := hjReduceChar_sub_intVec r i
    refine ⟨m - k, ?_⟩
    push_cast
    linarith
  · intro h i
    obtain ⟨m, hm⟩ := h i
    obtain ⟨k, hk⟩ := hjReduceChar_sub_intVec r i
    refine ⟨m + k, ?_⟩
    push_cast
    linarith

/-! ### The cycle characteristics and the Shintani arguments

Kopp's `r_n = {A_{n,0}r}` and `w_n = ⟨⟨r_n, β_n⟩⟩`. The inverse of the cycle matrix `A_{0,n}` is
Kopp's `A_{n,0}`, so both sequences are indexed by the same `n` as the rotated numbers. -/

/-- Kopp's reduced characteristic `r_n = {A_{n,0}r}` of [72, Kopp (2024), Definition 7.4,
`defn:cycledata`], with `A_{n,0} = A_{0,n}⁻¹` the inverse of the cycle matrix of
`SICs.SL2Z.HJExpansion`. -/
noncomputable def hjChar (r : Fin 2 → ℚ) (β : ℝ) (n : ℕ) : Fin 2 → ℚ :=
  hjReduceChar
    (ratVecAction (((hjCycleMatrix β n)⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) r)

/-- Kopp's `w_n = ⟨⟨r_n, β_n⟩⟩` of [72, Kopp (2024), Definition 7.4, `defn:cycledata`], the
argument at which the Stark--Tangedal--Yamamoto invariant [72, Kopp (2024), Definition 7.13,
`defn:tangedalu`] evaluates the double sine of modulus `β_n`. -/
noncomputable def hjShintaniArg (r : Fin 2 → ℚ) (β : ℝ) (n : ℕ) : ℝ :=
  fracSymplecticFormRat (hjChar r β n) (hjPeriod β n)

/-- Kopp's conjugate argument `w_n' = ⟨⟨r_n, β_n'⟩⟩` of [72, Kopp (2024), Proposition 7.10,
`prop:shintanidecomp`], the second Shintani argument `x₂` at which the double zeta function
`z₂(s, (w_n, w_n'), (β_n, β_n'))` is evaluated, stated along an arbitrary sequence `x` in place
of the conjugates `β_n'`. At `x = hjPeriod β` it is `hjShintaniArg` itself
(`hjShintaniArg_eq_hjShintaniArgCompanion`); the intended instance is a companion sequence of
the expansion (`IsHJCompanion`) with values in `(0,1)`. -/
noncomputable def hjShintaniArgCompanion (r : Fin 2 → ℚ) (β : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  fracSymplecticFormRat (hjChar r β n) (x n)

/-- The Shintani argument is its own companion version along the rotated numbers. -/
theorem hjShintaniArg_eq_hjShintaniArgCompanion (r : Fin 2 → ℚ) (β : ℝ) (n : ℕ) :
    hjShintaniArg r β n = hjShintaniArgCompanion r β (hjPeriod β) n :=
  rfl

/-- The zeroth cycle characteristic is the reduction of `r`: `r_0 = {r}`. -/
@[simp] theorem hjChar_zero (r : Fin 2 → ℚ) (β : ℝ) : hjChar r β 0 = hjReduceChar r := by
  simp [hjChar, Matrix.SpecialLinearGroup.coe_one]

/-- **The cycle characteristics stay nonintegral**, the standing hypothesis
`r ∈ ℚ² \ ℤ²` of [72, Kopp (2024), Definition 7.4, `defn:cycledata`]. -/
theorem not_isIntegralIndex_hjChar {r : Fin 2 → ℚ} (hr : ¬ IsIntegralIndex r) (β : ℝ) (n : ℕ) :
    ¬ IsIntegralIndex (hjChar r β n) := by
  intro h
  apply hr
  apply (isIntegralIndex_ratVecAction_iff ((hjCycleMatrix β n)⁻¹)).mp
  exact (isIntegralIndex_hjReduceChar_iff _).mp h

/-! ### The pairing with a reduced characteristic

For any characteristic `s` and modulus `τ > 0`, the pairing `⟨⟨{s},τ⟩⟩` with the reduction lies
in `(0, τ + 1)`, and the raw pairing `⟨⟨s,τ⟩⟩` differs from it by the lattice vector
`⌊s₂⌋τ - ⌊s₁⌋`, up to the constant `1` that the reduction's first coordinate carries. Written with
base point `⟨⟨{s},τ⟩⟩ - 1 ∈ (-1, τ)`, this is exactly the shape in which
`SICs.Cocycle.SigmaS.Reduction.sigmaSHonest_eq_sigmaS` evaluates the real `σ_S` at the raw
pairing. -/

/-- **The pairing with a reduced characteristic is positive**: `0 < ⟨⟨{s},τ⟩⟩` for `τ > 0`,
since `{s}₂ ≥ 0` and `{s}₁ < 0`. At `s = A_{0,n}⁻¹ r`, `τ = β_n` this is `0 < w_n`. -/
theorem fracSymplecticFormRat_hjReduceChar_pos (s : Fin 2 → ℚ) {τ : ℝ} (hτ : 0 < τ) :
    0 < fracSymplecticFormRat (hjReduceChar s) τ := by
  have hzero : (hjReduceChar s 0 : ℝ) < 0 := by
    exact_mod_cast hjReduceChar_apply_zero_neg s
  have hone : 0 ≤ (hjReduceChar s 1 : ℝ) := by
    exact_mod_cast hjReduceChar_apply_one_nonneg s
  unfold fracSymplecticFormRat
  nlinarith

/-- **The pairing with a reduced characteristic lies below `τ + 1`**: `⟨⟨{s},τ⟩⟩ < τ + 1` for
`τ > 0`, since `{s}₂ < 1` and `-{s}₁ ≤ 1`. At `s = A_{0,n}⁻¹ r`, `τ = β_n` this is
`w_n < β_n + 1`. -/
theorem fracSymplecticFormRat_hjReduceChar_lt_add_one (s : Fin 2 → ℚ) {τ : ℝ} (hτ : 0 < τ) :
    fracSymplecticFormRat (hjReduceChar s) τ < τ + 1 := by
  have hzero : (-1 : ℝ) ≤ hjReduceChar s 0 := by
    exact_mod_cast neg_one_le_hjReduceChar_apply_zero s
  have hone : (hjReduceChar s 1 : ℝ) < 1 := by
    exact_mod_cast hjReduceChar_apply_one_lt_one s
  unfold fracSymplecticFormRat
  nlinarith

/-- **The raw pairing as a lattice translate of the reduced one**:
`⟨⟨s,τ⟩⟩ = (⟨⟨{s},τ⟩⟩ - 1) + ⌊s₂⌋τ + (-⌊s₁⌋)`, since `{s} = (s₁ - ⌊s₁⌋ - 1, s₂ - ⌊s₂⌋)`. The base
point `⟨⟨{s},τ⟩⟩ - 1` lies in `(-1, τ)` by the two bounds above, so this is the presentation of
the raw pairing that `SICs.Cocycle.SigmaS.Reduction.sigmaSHonest_eq_sigmaS` consumes. -/
theorem fracSymplecticFormRat_eq_hjReduceChar_add (s : Fin 2 → ℚ) (τ : ℝ) :
    fracSymplecticFormRat s τ =
      (fracSymplecticFormRat (hjReduceChar s) τ - 1) + (⌊s 1⌋ : ℝ) * τ +
        ((-⌊s 0⌋ : ℤ) : ℝ) := by
  unfold fracSymplecticFormRat
  simp only [hjReduceChar_apply_zero, hjReduceChar_apply_one, Int.fract]
  push_cast
  ring

/-- Applying an integral special-linear matrix preserves congruence modulo `ℤ²`.
This helper supplies the transport step in `hjChar_congr`. -/
private lemma ratVecAction_sub_intVec {v w : Fin 2 → ℚ} (M : SL(2, ℤ))
    (h : ∀ i, ∃ m : ℤ, v i - w i = (m : ℚ)) :
    ∀ i, ∃ m : ℤ,
      ratVecAction (M : Mat(2, ℤ)) v i -
        ratVecAction (M : Mat(2, ℤ)) w i = (m : ℚ) := by
  have hint : IsIntegralIndex (v - w) := by
    intro i
    simpa only [Pi.sub_apply] using h i
  have himage := isIntegralIndex_ratVecAction (M : Mat(2, ℤ)) hint
  rw [ratVecAction_sub] at himage
  exact himage

/-! ### Shifting the expansion

Peeling one rotation from the left replaces `β` by `β_1` and `r` by `(T^{b_0}S)⁻¹ r`, because
`A_{0,n+1}(β) = T^{b_0}S · A_{0,n}(β_1)`. This is the recursion along which the word-chained cocycle
walks, and it keeps the cycle characteristics in step with the rotated numbers. -/

/-- **Left peeling of the cycle characteristics**: `r_{n+1}` at `(r, β)` is `r_n` at
`((T^{b_0}S)⁻¹ r, β_1)`, from `A_{0,n+1} = T^{b_0}S · A_{0,n}(β_1)` (`hjCycleMatrix_succ`). -/
theorem hjChar_succ_left (r : Fin 2 → ℚ) (β : ℝ) (n : ℕ) :
    hjChar r β (n + 1) =
      hjChar (ratVecAction (((T ^ hjLetter β * S)⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) r)
        (hjRotate β) n := by
  unfold hjChar
  rw [hjCycleMatrix_succ, mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul,
    ratVecAction_mul]

/-- **Left peeling of the conjugate Shintani arguments**: `w'_{n+1}` at `(r, β, x)` is `w'_n` at
`((T^{b_0}S)⁻¹ r, β_1, (x_{k+1})_k)`, by `hjChar_succ_left`. -/
theorem hjShintaniArgCompanion_succ_left (r : Fin 2 → ℚ) (β : ℝ) (x : ℕ → ℝ) (n : ℕ) :
    hjShintaniArgCompanion r β x (n + 1) =
      hjShintaniArgCompanion
        (ratVecAction (((T ^ hjLetter β * S)⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) r)
        (hjRotate β) (fun k => x (k + 1)) n := by
  unfold hjShintaniArgCompanion
  rw [hjChar_succ_left]

/-- **One generator on a characteristic, first coordinate**: `(T^bS u)₁ = b u₁ - u₂`, from
`T^bS = [[b, -1], [1, 0]]`. -/
theorem ratVecAction_T_zpow_mul_S_apply_zero (b : ℤ) (u : Fin 2 → ℚ) :
    ratVecAction ((T ^ b * S : SL(2, ℤ)) : Mat(2, ℤ)) u 0 =
      b * u 0 - u 1 := by
  rw [coe_T_zpow_mul_S]
  simp [ratVecAction, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply]
  ring

/-- **One generator on a characteristic, second coordinate**: `(T^bS u)₂ = u₁`. This is why
consecutive cycle characteristics share a fractional part (`hjChar_succ_apply_zero`) and why the
`q`-Pochhammer indices of consecutive word steps agree in the telescoping of
[72, Kopp (2024), Proposition 7.20, `prop:almost`]. -/
theorem ratVecAction_T_zpow_mul_S_apply_one (b : ℤ) (u : Fin 2 → ℚ) :
    ratVecAction ((T ^ b * S : SL(2, ℤ)) : Mat(2, ℤ)) u 1 = u 0 := by
  rw [coe_T_zpow_mul_S]
  simp [ratVecAction, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply]

/-- **Covariance of the pairing along one rotation of a companion sequence**:
`⟨⟨T^{b_n}S u, x_n⟩⟩ = ⟨⟨u, x_{n+1}⟩⟩/x_{n+1}` for a companion sequence `x` of the expansion of
`β` (`IsHJCompanion`): `fracSymplecticFormRat_ratVecAction` at `M = T^{b_n}S`, whose Jacobi
denominator at `x_{n+1}` is `x_{n+1} ≠ 0` and which carries `x_{n+1}` to `x_n = b_n - 1/x_{n+1}`
(`flt_T_zpow_mul_S`, `fltDenominator_T_zpow_mul_S`). -/
theorem fracSymplecticFormRat_ratVecAction_hjCompanion {β : ℝ}
    {x : ℕ → ℝ} (hx : IsHJCompanion β x) (n : ℕ) (u : Fin 2 → ℚ) :
    fracSymplecticFormRat
        (ratVecAction ((T ^ hjLetter (hjPeriod β n) * S : SL(2, ℤ)) : Mat(2, ℤ))
          u) (x n) =
      fracSymplecticFormRat u (x (n + 1)) / x (n + 1) := by
  have hxnext : x (n + 1) ≠ 0 := (hx n).1
  have hflt : flt
      ((T ^ hjLetter (hjPeriod β n) * S : SL(2, ℤ)) : Mat(2, ℤ))
      (x (n + 1)) = x n := by
    rw [flt_T_zpow_mul_S _ hxnext, ← (hx n).2]
  have h := fracSymplecticFormRat_ratVecAction
    ((T ^ hjLetter (hjPeriod β n) * S : SL(2, ℤ)) : Mat(2, ℤ)) u
    (x (n + 1)) (by rw [fltDenominator_T_zpow_mul_S]; exact hxnext)
  rw [hflt, fltDenominator_T_zpow_mul_S] at h
  simpa [(T ^ hjLetter (hjPeriod β n) * S : SL(2, ℤ)).2] using h

/-- The unreduced characteristic at step `n` is obtained from the one at step `n+1`
by applying `T^{b_n}S`; used in the consecutive-coordinate identities. -/
private lemma hjChar_eq_hjReduceChar_ratVecAction_succ (r : Fin 2 → ℚ) (β : ℝ) (n : ℕ) :
    hjChar r β n = hjReduceChar (ratVecAction
      ((T ^ hjLetter (hjPeriod β n) * S : SL(2, ℤ)) : Mat(2, ℤ))
      (ratVecAction (((hjCycleMatrix β (n + 1))⁻¹ : SL(2, ℤ)) :
        Mat(2, ℤ)) r)) := by
  let B : SL(2, ℤ) := T ^ hjLetter (hjPeriod β n) * S
  let A : SL(2, ℤ) := hjCycleMatrix β n
  have hcycle : hjCycleMatrix β (n + 1) = A * B := hjCycleMatrix_succ_right β n
  have haction : ratVecAction (B : Mat(2, ℤ))
      (ratVecAction (((hjCycleMatrix β (n + 1))⁻¹ : SL(2, ℤ)) :
        Mat(2, ℤ)) r) =
      ratVecAction ((A⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) r := by
    rw [← ratVecAction_mul, ← Matrix.SpecialLinearGroup.coe_mul, hcycle]
    group
  unfold hjChar
  rw [haction]

/-- **Kopp's relation between consecutive first and second coordinates**,
`r_{(n+1)1} = r_{n2} - 1`, used in the proof of [72, Kopp (2024), Proposition 7.22,
`prop:lambdaminus`]. With `u = A_{0,n+1}⁻¹ r` and `v = A_{0,n}⁻¹ r = T^{b_n}S u` one has
`v₂ = u₁`, so the two reductions see the same fractional part, offset by the `-1` of the first
coordinate. -/
theorem hjChar_succ_apply_zero (r : Fin 2 → ℚ) (β : ℝ) (n : ℕ) :
    hjChar r β (n + 1) 0 = hjChar r β n 1 - 1 := by
  rw [hjChar_eq_hjReduceChar_ratVecAction_succ r β n]
  simp only [hjChar, hjReduceChar_apply_zero, hjReduceChar_apply_one]
  rw [ratVecAction_T_zpow_mul_S_apply_one]

/-! ### Congruent characteristics and the closed cycle

The cycle characteristics depend on `r` only modulo `ℤ²`, and when the cycle matrix `A_{0,N}` lies
in `Γ_r` the sequence returns to its start: `r_N = r_0 = {r}`. No periodicity of `β` is needed for
the latter, only the congruence `A_{0,N}⁻¹ r ≡ r`. -/

/-- **The cycle characteristics depend on `r` only modulo `ℤ²`**: the action of an integral
matrix preserves congruence, and the reduction forgets it (`hjReduceChar_congr`). -/
theorem hjChar_congr {r r' : Fin 2 → ℚ} (h : ∀ i, ∃ m : ℤ, r i - r' i = (m : ℚ)) (β : ℝ)
    (n : ℕ) : hjChar r β n = hjChar r' β n := by
  unfold hjChar
  exact hjReduceChar_congr (ratVecAction_sub_intVec _ h)

/-- **The cycle closes on the characteristics**: if `A_{0,N} ∈ Γ_r` then `r_N = {r} = r_0`,
because `A_{0,N}⁻¹ ∈ Γ_r` too (`inv_mem_gammaSubgroup`), so `A_{0,N}⁻¹ r ≡ r (mod ℤ²)`. This is
the standing situation of [72, Kopp (2024), Definition 7.4, `defn:cycledata`], where `N = kℓ` is
chosen with `A = P^k ∈ Γ_r`. -/
theorem hjChar_of_mem_gammaSubgroup {r : Fin 2 → ℚ} {β : ℝ} {N : ℕ}
    (hA : (hjCycleMatrix β N : SL(2, ℤ)) ∈ gammaSubgroup r) :
    hjChar r β N = hjReduceChar r := by
  unfold hjChar
  exact hjReduceChar_congr
    (ratVecAction_sub_intVec_of_mem_gammaSubgroup (inv_mem_gammaSubgroup hA))

/-- **The conjugate Shintani arguments depend on `r` only modulo `ℤ²`**, by `hjChar_congr`. -/
theorem hjShintaniArgCompanion_congr {r r' : Fin 2 → ℚ} (h : ∀ i, ∃ m : ℤ, r i - r' i = (m : ℚ))
    (β : ℝ) (x : ℕ → ℝ) (n : ℕ) :
    hjShintaniArgCompanion r β x n = hjShintaniArgCompanion r' β x n := by
  unfold hjShintaniArgCompanion
  rw [hjChar_congr h]

/-- **The cycle closes on the conjugate Shintani arguments**: if `A_{0,N} ∈ Γ_r` and `x_N = x_0`,
then `w'_N = w'_0`. -/
theorem hjShintaniArgCompanion_of_mem_gammaSubgroup {r : Fin 2 → ℚ} {β : ℝ} {N : ℕ}
    (hA : (hjCycleMatrix β N : SL(2, ℤ)) ∈ gammaSubgroup r)
    {x : ℕ → ℝ} (hxN : x N = x 0) :
    hjShintaniArgCompanion r β x N = hjShintaniArgCompanion r β x 0 := by
  unfold hjShintaniArgCompanion
  rw [hjChar_of_mem_gammaSubgroup hA, hjChar_zero, hxN]

/-! ### The dual shift between consecutive steps

The word walk evaluates its `σ_S` factor at step `n+1` through a `q`-Pochhammer product in the
dual variables `((w_{n+1} - 1)/β_{n+1}, -1/β_{n+1})` (`SICs.Cocycle.SigmaS.Basic.sigmaS`), and
its
factor at step `n` through one in the direct variables `(w_n - 1, β_n)`. The two coincide modulo
`ℤ` in both variables: `-1/β_{n+1} = β_n - b_n` is the rotation read backwards, and

$$
\frac{w_{n+1}-1}{\beta_{n+1}} \equiv w_n - 1 \pmod{\mathbb Z}
$$

because `⟨⟨u,β_{n+1}⟩⟩/β_{n+1} = ⟨⟨T^{b_n}S u, β_n⟩⟩` (the covariance of the pairing) and the two
reductions differ from `u` and `T^{b_n}S u` by integer vectors whose contributions along `β_n`
agree. This is what makes consecutive `q`-Pochhammer factors of the word walk cancel in
[72, Kopp (2024), Proposition 7.20, `prop:almost`]. -/

/-- The arithmetic core of `hjShintaniArgCompanion_succ_sub_one_div`: covariance of the raw
pairings descends to an integral shift after reducing both characteristics. -/
private lemma fracSymplecticFormRat_hjReduceChar_sub_one_div
    (u v : Fin 2 → ℚ) (x y : ℝ) (b : ℤ) (hx : x ≠ 0)
    (hcov : fracSymplecticFormRat v y = fracSymplecticFormRat u x / x)
    (hvone : v 1 = u 0) (hrecip : x⁻¹ = (b : ℝ) - y) :
    ∃ k : ℤ, (fracSymplecticFormRat (hjReduceChar u) x - 1) / x =
      fracSymplecticFormRat (hjReduceChar v) y - 1 + k := by
  have hrawNext := fracSymplecticFormRat_eq_hjReduceChar_add u x
  have hrawNow := fracSymplecticFormRat_eq_hjReduceChar_add v y
  rw [hvone] at hrawNow
  refine ⟨-⌊u 1⌋ + ⌊u 0⌋ * b - ⌊v 0⌋, ?_⟩
  push_cast at hrawNext hrawNow ⊢
  rw [hrawNext, hrawNow] at hcov
  have hxy : ((b : ℝ) - y) * x = 1 := by
    rw [← hrecip]
    exact inv_mul_cancel₀ hx
  field_simp [hx] at hcov ⊢
  linear_combination -hcov - (⌊u 0⌋ : ℝ) * hxy

/-- **The dual shift of the conjugate Shintani arguments**:
`(w'_{n+1} - 1)/x_{n+1} ≡ w'_n - 1 (mod ℤ)` along any companion sequence `x` of the expansion
of `β`. The argument of the section comment applies verbatim with `x_n` in place of `β_n`: the
covariance `fracSymplecticFormRat_ratVecAction_hjCompanion`, the
presentations `fracSymplecticFormRat_eq_hjReduceChar_add` of the raw pairings at `u` and
`T^{b_n}S u`, the coordinate relation `ratVecAction_T_zpow_mul_S_apply_one`, and
`1/x_{n+1} = b_n - x_n`. The integer is `-⌊u₂⌋ + ⌊u₁⌋b_n - ⌊(T^{b_n}S u)₁⌋`. -/
theorem hjShintaniArgCompanion_succ_sub_one_div (r : Fin 2 → ℚ) {β : ℝ} {x : ℕ → ℝ}
    (hx : IsHJCompanion β x) (n : ℕ) :
    ∃ k : ℤ, (hjShintaniArgCompanion r β x (n + 1) - 1) / x (n + 1) =
      hjShintaniArgCompanion r β x n - 1 + k := by
  let xNext := x (n + 1)
  let xNow := x n
  let b := hjLetter (hjPeriod β n)
  let B : SL(2, ℤ) := T ^ b * S
  let u : Fin 2 → ℚ := ratVecAction
    (((hjCycleMatrix β (n + 1))⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) r
  let v : Fin 2 → ℚ := ratVecAction (B : Mat(2, ℤ)) u
  have hcov : fracSymplecticFormRat v xNow = fracSymplecticFormRat u xNext / xNext := by
    simpa only [v, B, b, xNow, xNext] using
      fracSymplecticFormRat_ratVecAction_hjCompanion hx n u
  have hcharNext : hjChar r β (n + 1) = hjReduceChar u := by rfl
  have hcharNow : hjChar r β n = hjReduceChar v := by
    simpa only [B, b, u, v] using hjChar_eq_hjReduceChar_ratVecAction_succ r β n
  have hvone : v 1 = u 0 := ratVecAction_T_zpow_mul_S_apply_one b u
  have hrecip : xNext⁻¹ = (b : ℝ) - xNow := by
    simp only [xNext, xNow, b, ← one_div]
    linarith [(hx n).2]
  simpa only [hjShintaniArgCompanion, hcharNext, hcharNow, xNext, xNow] using
    fracSymplecticFormRat_hjReduceChar_sub_one_div
      u v xNext xNow b (hx n).1 hcov hvone hrecip

/-! ### The reflected characteristics

Negating `r` negates every `A_{0,n}⁻¹ r`, and the reduction of a negated vector is determined by
that of the vector: `{-u}₂ = 1 - {u}₂` unless `{u}₂ = 0`, and `{-u}₁ = -1 - {u}₁` unless
`{u}₁ = -1`. These are the three cases of [72, Kopp (2024), Proposition 7.22,
`prop:lambdaminus`]. -/

/-- The first coordinate of the reduction of `-u`: `-1` if `u₁ ∈ ℤ`, and `-fract(u₁)` otherwise,
that is `-1 - {u}₁` in terms of the reduction of `u`. -/
theorem hjReduceChar_neg_apply_zero (u : Fin 2 → ℚ) :
    hjReduceChar (-u) 0 = if hjReduceChar u 0 = -1 then -1 else -1 - hjReduceChar u 0 := by
  by_cases h : Int.fract (u 0) = 0
  · have hn : Int.fract (-u 0) = 0 := Int.fract_neg_eq_zero.mpr h
    simp [hjReduceChar_apply_zero, h, hn]
  · rw [hjReduceChar_apply_zero, Pi.neg_apply, Int.fract_neg h,
      hjReduceChar_apply_zero]
    simp [h]
    ring

/-- The second coordinate of the reduction of `-u`: `0` if `u₂ ∈ ℤ`, and `1 - fract(u₂)`
otherwise, that is `1 - {u}₂`. -/
theorem hjReduceChar_neg_apply_one (u : Fin 2 → ℚ) :
    hjReduceChar (-u) 1 = if hjReduceChar u 1 = 0 then 0 else 1 - hjReduceChar u 1 := by
  by_cases h : Int.fract (u 1) = 0
  · have hn : Int.fract (-u 1) = 0 := Int.fract_neg_eq_zero.mpr h
    simp [hjReduceChar_apply_one, h, hn]
  · rw [hjReduceChar_apply_one, Pi.neg_apply, Int.fract_neg h,
      hjReduceChar_apply_one]
    simp [h]

/-- **The cycle characteristics of `-r`** are the reductions of the negated cycle characteristics
of `r`: `r̃_n = {-r_n}`, since the action is linear and the reduction forgets integer vectors. -/
theorem hjChar_neg (r : Fin 2 → ℚ) (β : ℝ) (n : ℕ) :
    hjChar (-r) β n = hjReduceChar (-(hjChar r β n)) := by
  unfold hjChar
  rw [show ratVecAction
      (((hjCycleMatrix β n)⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) (-r) =
      -(ratVecAction (((hjCycleMatrix β n)⁻¹ : SL(2, ℤ)) :
        Mat(2, ℤ)) r) by
    simp only [ratVecAction, Matrix.mulVec_neg]]
  apply hjReduceChar_congr
  intro i
  obtain ⟨m, hm⟩ := hjReduceChar_sub_intVec
    (ratVecAction (((hjCycleMatrix β n)⁻¹ : SL(2, ℤ)) :
      Mat(2, ℤ)) r) i
  refine ⟨m, ?_⟩
  simp only [Pi.neg_apply]
  linarith

/-! ### Kopp's `r`-dependent phase sum

The second exponential prefactor accumulated along the cycle in [72, Kopp (2024), Proposition
7.20, `prop:almost`] is `e(λ_r(A)/4)` with

$$
\lambda_{\mathbf r}(A) = \sum_{n=0}^{N-1} \frac{(\beta_n - w_n)(1 - w_n)}{\beta_n},
\qquad A = A_{0,N}.
$$

[72, Kopp (2024), Proposition 7.22, `prop:lambdaminus`] shows it is even in `r`. Write `a_n` for the
`n`-th summand at `r` and `ã_n` for the one at `-r`, with `w̃_n` the Shintani argument of `-r`. In
terms of `r_n = (r_{n1}, r_{n2})`:

* if `r_{n1} ≠ -1` and `r_{n2} ≠ 0`, then `w̃_n = β_n + 1 - w_n` and `ã_n = a_n`;
* if `r_{n1} ≠ -1` and `r_{n2} = 0`, then `w̃_n = 1 - w_n` and `ã_n = a_n - (1 + 2r_{n1})`;
* if `r_{n1} = -1` and `r_{n2} ≠ 0`, then `w̃_n = β_n + 2 - w_n` and `ã_n = a_n + (1 - 2r_{n2})`;

the fourth combination is `r_n ∈ ℤ²`, excluded. Since `r_{(n+1)1} = r_{n2} - 1`
(`hjChar_succ_apply_zero`), the second case at `n` is exactly the third case at `n+1`, where
moreover `r_{(n+1)2} = -r_{n1}`, so the two corrections cancel in pairs. With
`g_n := 1 - 2r_{n2}` if `r_{n1} = -1` and `g_n := 0` otherwise, every case reads
`ã_n - a_n = g_n - g_{n+1}`, and the sum telescopes to `g_0 - g_N = 0` once the cycle closes
(`hjChar_of_mem_gammaSubgroup`). -/

/-- Kopp's `r`-dependent phase sum `λ_r(A) = Σ_{n<N} (β_n - w_n)(1 - w_n)/β_n` of
[72, Kopp (2024), Proposition 7.20, `prop:almost`], attached to the cycle matrix `A = A_{0,N}`
through its length `N`. -/
noncomputable def hjLambda (r : Fin 2 → ℚ) (β : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N,
    (hjPeriod β n - hjShintaniArg r β n) * (1 - hjShintaniArg r β n) / hjPeriod β n

/-- **The second coordinate after a boundary step**: if `r_{n2} = 0`, then `r_{(n+1)2} = -r_{n1}`.
With `hjChar_succ_apply_zero` this says that the case `r_{n2} = 0` at `n` is the case
`r_{(n+1)1} = -1` at `n + 1` with `r_{(n+1)2} = -r_{n1}`; it pairs the boundary corrections in
`hjLambda_neg`. -/
theorem hjChar_succ_apply_one_of_apply_one_eq_zero {r : Fin 2 → ℚ}
    (hr : ¬ IsIntegralIndex r) (β : ℝ) (n : ℕ) (hone : hjChar r β n 1 = 0) :
    hjChar r β (n + 1) 1 = -hjChar r β n 0 := by
  let b := hjLetter (hjPeriod β n)
  let B : SL(2, ℤ) := T ^ b * S
  let u : Fin 2 → ℚ := ratVecAction
    (((hjCycleMatrix β (n + 1))⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) r
  have hnext : hjChar r β (n + 1) = hjReduceChar u := rfl
  have hnow : hjChar r β n = hjReduceChar
      (ratVecAction (B : Mat(2, ℤ)) u) := by
    simpa only [B, b, u] using hjChar_eq_hjReduceChar_ratVecAction_succ r β n
  have hu0fract : Int.fract (u 0) = 0 := by
    rw [hnow, hjReduceChar_apply_one,
      ratVecAction_T_zpow_mul_S_apply_one] at hone
    exact hone
  have hu0 : u 0 = (⌊u 0⌋ : ℚ) := by
    unfold Int.fract at hu0fract
    linarith
  have hu1fract : Int.fract (u 1) ≠ 0 := by
    intro hu1
    apply not_isIntegralIndex_hjChar hr β (n + 1)
    apply isIntegralIndex_of_coords
    · refine ⟨-1, ?_⟩
      rw [hjChar_succ_apply_zero, hone]
      norm_num
    · refine ⟨0, ?_⟩
      rw [hnext, hjReduceChar_apply_one, hu1]
      norm_num
  have hnowZero : hjChar r β n 0 = Int.fract (-u 1) - 1 := by
    rw [hnow, hjReduceChar_apply_zero,
      ratVecAction_T_zpow_mul_S_apply_zero]
    have harg : (b : ℚ) * u 0 - u 1 = -u 1 + ((b * ⌊u 0⌋ : ℤ) : ℚ) := by
      nth_rewrite 1 [hu0]
      push_cast
      ring
    rw [harg, Int.fract_add_intCast]
  rw [hnext, hjReduceChar_apply_one, hnowZero, Int.fract_neg hu1fract]
  ring

/-- The correction whose consecutive difference is the change of one `hjLambda` summand under
negating the characteristic; used in `hjLambda_neg`. -/
private noncomputable def hjLambdaCorrection (r : Fin 2 → ℚ) (β : ℝ) (n : ℕ) : ℝ :=
  if hjChar r β n 0 = -1 then 1 - 2 * (hjChar r β n 1 : ℝ) else 0

/-- Negating a nonintegral characteristic changes one `hjLambda` summand by the consecutive
difference of `hjLambdaCorrection`; used in `hjLambda_neg`. -/
private lemma hjLambda_summand_neg_sub {r : Fin 2 → ℚ} (hr : ¬ IsIntegralIndex r)
    {β : ℝ} (hβ : Irrational β) (n : ℕ) :
    (hjPeriod β n - hjShintaniArg (-r) β n) *
          (1 - hjShintaniArg (-r) β n) / hjPeriod β n -
        (hjPeriod β n - hjShintaniArg r β n) *
          (1 - hjShintaniArg r β n) / hjPeriod β n =
      hjLambdaCorrection r β n - hjLambdaCorrection r β (n + 1) := by
  have hx : hjPeriod β n ≠ 0 := (irrational_hjPeriod hβ n).ne_zero
  have hneg0 := congrFun (hjChar_neg r β n) 0
  have hneg1 := congrFun (hjChar_neg r β n) 1
  rw [hjReduceChar_neg_apply_zero] at hneg0
  rw [hjReduceChar_neg_apply_one] at hneg1
  have hred : hjReduceChar (hjChar r β n) = hjChar r β n := by
    unfold hjChar
    rw [hjReduceChar_hjReduceChar]
  rw [hred] at hneg0 hneg1
  have hnext0 := hjChar_succ_apply_zero r β n
  by_cases h0 : hjChar r β n 0 = -1
  · by_cases h1 : hjChar r β n 1 = 0
    · exfalso
      apply not_isIntegralIndex_hjChar hr β n
      apply isIntegralIndex_of_coords
      · exact ⟨-1, h0⟩
      · exact ⟨0, h1⟩
    · have hn0 : hjChar r β (n + 1) 0 ≠ -1 := by
        rw [hnext0]
        intro h
        apply h1
        linarith
      unfold hjShintaniArg fracSymplecticFormRat
      rw [hneg0, hneg1]
      simp only [hjLambdaCorrection, ite_eq_left h0, ite_eq_right h1, ite_eq_right hn0]
      field_simp [hx]
      push_cast
      rw [h0]
      ring
  · by_cases h1 : hjChar r β n 1 = 0
    · have hn0 : hjChar r β (n + 1) 0 = -1 := by
        rw [hnext0, h1]
        norm_num
      have hnext1 := hjChar_succ_apply_one_of_apply_one_eq_zero hr β n h1
      unfold hjShintaniArg fracSymplecticFormRat
      rw [hneg0, hneg1]
      simp only [hjLambdaCorrection, ite_eq_right h0, ite_eq_left h1, ite_eq_left hn0]
      field_simp [hx]
      rw [h1, hnext1]
      push_cast
      ring
    · have hn0 : hjChar r β (n + 1) 0 ≠ -1 := by
        rw [hnext0]
        intro h
        apply h1
        linarith
      unfold hjShintaniArg fracSymplecticFormRat
      rw [hneg0, hneg1]
      simp only [hjLambdaCorrection, ite_eq_right h0, ite_eq_right h1, ite_eq_right hn0]
      field_simp [hx]
      push_cast
      ring

/-- **[72, Kopp (2024), Proposition 7.22, `prop:lambdaminus`]**: `λ_{-r}(A) = λ_r(A)` whenever
the cycle closes on `r`, that is `A_{0,N} ∈ Γ_r`. Kopp states it under his standing assumptions
(`(r,β)` a reduced representative and `A = P^k`); the proof uses only the closing of the cycle,
`r ∉ ℤ²`, and `β_n ≠ 0`. See the section comment for the three cases and the telescoping. -/
@[source "72, Proposition 7.22, p. 75, prop:lambdaminus"]
theorem hjLambda_neg {r : Fin 2 → ℚ} (hr : ¬ IsIntegralIndex r) {β : ℝ} (hβ : Irrational β)
    {N : ℕ} (hA : (hjCycleMatrix β N : SL(2, ℤ)) ∈ gammaSubgroup r) :
    hjLambda (-r) β N = hjLambda r β N := by
  have hchar : hjChar r β N = hjChar r β 0 := by
    rw [hjChar_of_mem_gammaSubgroup hA, hjChar_zero]
  have hcorrection : hjLambdaCorrection r β N = hjLambdaCorrection r β 0 := by
    unfold hjLambdaCorrection
    rw [hchar]
  rw [← sub_eq_zero]
  unfold hjLambda
  rw [← Finset.sum_sub_distrib]
  simp_rw [hjLambda_summand_neg_sub hr hβ]
  rw [Finset.sum_range_sub']
  exact sub_eq_zero.mpr hcorrection.symm

end SIC
