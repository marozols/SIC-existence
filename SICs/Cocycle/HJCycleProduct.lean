/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Cocycle.FixedPointCharacter
import SICs.Cocycle.HJCycleData

/-!
# The real modular cocycle as a double-sine product over a Hirzebruch--Jung cycle

Kopp's Proposition 7.20 by telescoping along a companion sequence of the expansion:
at the rotated numbers `U^{(1)}·ש^r_A(β) = e(γ/24 + λ_r/4)`, at the conjugates `U^{(2)}·ש^r_A(β') =
e(γ'/24 + λ'_r/4)`; with `U^{(1)}(r)U^{(1)}(-r) = 1`, the reflected product
`ש^r_A(β)ש^{-r}_A(β) = e(γ/12 + λ_r/2)` and quotient `ש^r_A(β)/ש^{-r}_A(β) = U^{(1)}(r)^{-2}`.

This file proves [72, Kopp (2024), Proposition 7.20, `prop:almost`] for the real cocycle value
`sfModularCocycleReal` of `SICs.Cocycle.Modular.Values`, together with the phase statements
[72, Kopp (2024), Proposition 7.21, `prop:globalphase`] and [72, Kopp (2024), Proposition 7.22,
`prop:lambdaminus`] for closed cycles. Throughout, `β` is an irrational number
above `1` whose Hirzebruch--Jung expansion closes after `N` steps (`β_N = β`), `A = A_{0,N}` is the
cycle matrix, which then fixes `β`, and `r ∈ ℚ² ∖ ℤ²` is a characteristic with `A ∈ Γ_r`. Kopp's `N`
is `kℓ`, `k` full periods of the minimal period `ℓ`, with `k` chosen so that `A = P^k ∈ Γ_r`;
nothing here needs `N` to be a multiple of the minimal period.

## The statement

With the cycle data `β_n`, `w_n` of `SICs.SL2Z.HJExpansion` and `SICs.Cocycle.HJCycleData`, the
Stark--Tangedal--Yamamoto invariant of [72, Kopp (2024), Definition 7.13, `defn:tangedalu`] is

$$
U^{(1)} = \prod_{n=0}^{N-1} S_2(w_n, \beta_n),
$$

and [72, Kopp (2024), Proposition 7.20, `prop:almost`] reads

$$
ש^{\mathbf r}_A(\beta) = e\!\left(\tfrac{1}{24}\gamma(A) + \tfrac14\lambda_{\mathbf r}(A)\right)
  \big/\, U^{(1)},
\qquad
\gamma(A) = \sum_{n<N}\Bigl(\beta_n - 3 + \tfrac1{\beta_n}\Bigr),
\quad
\lambda_{\mathbf r}(A) = \sum_{n<N}\frac{(\beta_n - w_n)(1 - w_n)}{\beta_n},
$$

with `γ` and `λ_r` from `SICs.SL2Z.HJExpansion.hjGamma` and `SICs.Cocycle.HJCycleData.hjLambda`.

## The proof: telescoping along the word walk

Kopp proves the proposition on the upper half plane, telescoping the period-product quotients
`ϖ_{r_{n-1}}(A_{n-1,kℓ}·τ) / ϖ_{r_n}(A_{n,kℓ}·τ)` and taking `τ → β`. Here the
value `ש^r_A(β)` is *defined* through the word walk of `A`, and by `hjStep_hjCycleMatrix` that walk
visits exactly the cycle matrices `A_{m,N}`, evaluating one real `σ_S` factor at each rotated
number `β_m`. So the telescoping happens on the real line, in the finite `q`-Pochhammer
bookkeeping of the factors, and no limit is taken.

Concretely, seed the walk at an arbitrary characteristic `s` and the pair `(⟨⟨s,β_N⟩⟩, β_N)`,
and write `r = A_{0,N}s`. The factor at step `m` is `σ_S(⟨⟨A_{m,N}s, β_m⟩⟩, β_m)`, and
`A_{m,N}s ≡ A_{0,m}⁻¹ r`, whose reduction is the cycle characteristic `r_m`. Presenting the raw
pairing as `(w_m - 1) + ⌊(A_{m,N}s)₂⌋β_m - ⌊(A_{m,N}s)₁⌋`
(`fracSymplecticFormRat_eq_hjReduceChar_add`) and applying `sigmaSHonest_eq_sigmaS` turns the
factor into

$$
\frac{\varpi_{\lfloor u_2\rfloor}(w_m - 1, \beta_m)}
     {\varpi_{\lfloor u_1\rfloor}\!\bigl(\tfrac{w_m-1}{\beta_m}, -\tfrac1{\beta_m}\bigr)}
\;\sigma_S^{\mathrm{base}}(w_m - 1, \beta_m),
\qquad u = A_{m,N}s .
$$

The denominator at step `m` is the numerator at step `m-1`: the indices agree because
`(T^{b}S\,u)_2 = u_1`, and the arguments agree modulo `ℤ` in both variables by the dual shift
`hjShintaniArgCompanion_succ_sub_one_div` and `-1/β_m = β_{m-1} - b_{m-1}`. So the product over
the walk collapses to its two ends,

$$
\sigma_A(\langle\!\langle s,\beta_N\rangle\!\rangle, \beta_N)
  \cdot \varpi_{\lfloor r_2\rfloor}(w_0 - 1, \beta_0)
  = \varpi_{\lfloor s_2\rfloor}(w_N - 1, \beta_N)
    \prod_{m=1}^{N} \sigma_S^{\mathrm{base}}(w_m - 1, \beta_m),
$$

which is `wordSigmaS_hjCycleMatrix_mul_qPochhammerFin`, proved by induction on `N` along the
left-peeling recursion `A_{0,N+1}(β) = T^{b_0}S\,A_{0,N}(β_1)`, with `β` replaced by `β_1` and no
periodicity assumed.

When the cycle closes and `A ∈ Γ_r`, take `s = r`: then `A r ≡ r`, so the cycle data are those of
`r`, and `w_N = w_0`, `β_N = β_0`. The denominator `ϖ_{n_QP(r,A)}(⟨⟨r,β⟩⟩/j_A(β), β)` of
[AFK25, equation (1.26), `eq:shindf`] combines with the left-hand boundary factor into
`ϖ_{⌊r₂⌋}(w_0 - 1, β)`, because `⟨⟨r,β⟩⟩/j_A(β) = ⟨⟨Ar,β⟩⟩` and `n_QP(r,A) = r₂ - (Ar)₂`; that
is the right-hand boundary factor, and it cancels. What remains is the product of the base values
`σ_S^{base}(w_m - 1, β_m) = exp(X(w_m - 1, β_m)) / S_2(w_m, β_m)`, and the exponent
`X(w - 1, β)` of [AFK25, equation (8.6), `eq:SFJacobiCocycleTermsDoubleSine`] is Kopp's
`2πi((β - 3 + β⁻¹)/24 + (β - w)(1 - w)/(4β))` (`sfExpArg_sub_one`).

## The phases

* `e(γ(A)/24)² = ψ²(A)` [72, Kopp (2024), Proposition 7.21, `prop:globalphase`]: `γ(A)` is the word
  accumulator `W(A)` (`hjGamma_eq_wordRademacher`), and at the positive trace of a fixed-point
  matrix `W(A)` is the Rademacher invariant `Ψ(A)` (`hjGamma_eq_rademacherInvariant`), which is
  how `ψ²` enters the Shintani--Faddeev phase of [AFK25].
* `λ_{-r}(A) = λ_r(A)` [72, Kopp (2024), Proposition 7.22, `prop:lambdaminus`] is `hjLambda_neg`.
* The product of the two instances of Proposition 7.20 at `r` and `-r`, which Kopp compares with
  his Theorem 4.36 in the proof of [72, Kopp (2024), Proposition 7.23, `prop:lambdachi`], is
  `sfModularCocycleReal_mul_neg_hjCycleMatrix`, `ש^r_A(β)·ש^{-r}_A(β) = e(γ(A)/12 + λ_r(A)/2)`. It
  has modulus `1/(U^{(1)}(r)U^{(1)}(-r))`; the fixed-point reflection law
  `sfModularCocycleReal_mul_neg_of_flt_eq_self` shows the product has modulus one, and the two
  invariants are positive, so `U^{(1)}(r)U^{(1)}(-r) = 1` (`starkTangedalYamamoto_mul_neg`).
  Dividing instead of multiplying the two instances gives the reflected quotient
  `ש^r_A(β)/ש^{-r}_A(β) = U^{(1)}(r)^{-2}` (`sfModularCocycleReal_div_neg_hjCycleMatrix`), the value
  side of [72, Kopp (2024), Theorem 8.2, `thm:mainrestate`].

## References

- [72, Kopp (2024), Definition 7.13, `defn:tangedalu`], [72, Kopp (2024), Proposition 7.20,
  `prop:almost`], [72, Kopp (2024), Proposition 7.21, `prop:globalphase`], [72, Kopp (2024),
  Proposition 7.22, `prop:lambdaminus`], [72, Kopp (2024), Proposition 7.23, `prop:lambdachi`].
- [AFK25, Definition 1.18, `def:shin`, equation (1.26), `eq:shindf`] and [AFK25, equation (8.6),
  `eq:SFJacobiCocycleTermsDoubleSine`].
-/

noncomputable section

open ModularGroup MatrixGroups Complex Real

open scoped MatrixGroups

namespace SIC

/-! ### The Stark--Tangedal--Yamamoto invariant

Kopp attaches `U^{(1)}` to a ray class through a reduced representative `(r, β)` of its image
under his correspondence `Υ̃_𝔪`; here it is attached to the pair `(r, β)` and the cycle length
`N` directly, which is all the product depends on. -/

/-- **The Stark--Tangedal--Yamamoto invariant** `U^{(1)} = ∏_{n<N} S₂(w_n, β_n)` of
[72, Kopp (2024), Definition 7.13, `defn:tangedalu`], at the real place `ρ_1` where `β` and the
`w_n` live, over the cycle data of the pair `(r, β)` of length `N` (Kopp's `kℓ`). Kopp's
`Sin_2(w, β)` is the two-argument double sine `S₂(w, β) = S₂(w; β, 1)` of
`SICs.SpecialFunctions.DoubleSine.RealIntegral`. -/
@[source "72, Definition 7.13, p. 69, defn:tangedalu" (symbol := "U^{(1)}")]
def starkTangedalYamamoto (r : Fin 2 → ℚ) (β : ℝ) (N : ℕ) : ℝ :=
  ∏ n ∈ Finset.range N, doubleSine' (hjShintaniArg r β n) (hjPeriod β n)

/-- **The invariant is positive**, as a product of double-sine values, each of which is an
exponential (`doubleSine_pos`). Kopp uses this in the proof of [72, Kopp (2024), Proposition
7.23, `prop:lambdachi`]. -/
theorem starkTangedalYamamoto_pos (r : Fin 2 → ℚ) (β : ℝ) (N : ℕ) :
    0 < starkTangedalYamamoto r β N := by
  exact Finset.prod_pos fun n _ ↦ doubleSine_pos _ _ _

/-- **The Stark--Tangedal--Yamamoto invariant at the other place**
`U^{(2)} = ∏_{n<N} S₂(w'_n, β'_n)` of [72, Kopp (2024), Definition 7.13, `defn:tangedalu`], the
product at `ρ_2` over the conjugate cycle data: `w'_n = ⟨⟨r_n, β'_n⟩⟩` (`hjShintaniArgCompanion`)
along a companion sequence `x` in the role of the conjugates `β'_n`. -/
def starkTangedalYamamotoConj (r : Fin 2 → ℚ) (β : ℝ) (x : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∏ n ∈ Finset.range N, doubleSine' (hjShintaniArgCompanion r β x n) (x n)

/-! ### Kopp's exponent

The base value `σ_S^{base}(z, τ) = exp(X(z,τ)) / S₂(z + 1, τ)` of [AFK25, equation (8.6),
`eq:SFJacobiCocycleTermsDoubleSine`] is evaluated at `z = w - 1`, where its double sine is
`S₂(w, τ)` and its exponent is the one of [72, Kopp (2024), Lemma 7.19, `lem:deltafrac2`]. -/

/-- **The exponent of [AFK25, equation (8.6), `eq:SFJacobiCocycleTermsDoubleSine`] at
`z = w - 1`** is Kopp's exponent of
[72, Kopp (2024), Lemma 7.19, `lem:deltafrac2`]:
`X(w - 1, τ) = 2πi·((τ - 3 + τ⁻¹)/24 + (τ - w)(1 - w)/(4τ))`. Both sides are
`πi/(12τ)·(6w² - 6w - 6τw + τ² + 3τ + 1)`. -/
theorem sfExpArg_sub_one (w τ : ℝ) (hτ : τ ≠ 0) :
    sfExpArg (w - 1) τ =
      2 * π * I * (((τ - 3 + τ⁻¹) / 24 + (τ - w) * (1 - w) / (4 * τ) : ℝ) : ℂ) := by
  unfold sfExpArg
  have hτC : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ
  push_cast
  exact faddeevSExpArg_sub_one (w : ℂ) (τ : ℂ) hτC

/-! ### Lattice avoidance along the cycle

Every base point `w_n - 1` the word walk uses avoids the lattice `ℤβ_n + ℤ`, because `r_n ∉ ℤ²`
and `β_n` is irrational. This discharges every nonvanishing side condition of the `q`-Pochhammer
calculus below. -/

/-- **The real `σ_S` at a rational pairing, through Kopp's reduction.** For an irrational
`τ > 0` and a characteristic `s ∉ ℤ²`,
`σ_S(⟨⟨s,τ⟩⟩, τ) = sigmaS (⟨⟨{s},τ⟩⟩ - 1) τ ⌊s₂⌋ (-⌊s₁⌋)`: the presentation
`fracSymplecticFormRat_eq_hjReduceChar_add` of the raw pairing, with base point in `(-1, τ)`
by `fracSymplecticFormRat_hjReduceChar_pos` and
`fracSymplecticFormRat_hjReduceChar_lt_add_one`, fed to
`SICs.Cocycle.SigmaS.Reduction.sigmaSHonest_eq_sigmaS`. -/
theorem sigmaSHonest_fracSymplecticFormRat {τ : ℝ} (hτ : Irrational τ) (hτ0 : 0 < τ)
    {s : Fin 2 → ℚ} (hs : ¬ IsIntegralIndex s) :
    sigmaSHonest (fracSymplecticFormRat s τ) τ =
      sigmaS (fracSymplecticFormRat (hjReduceChar s) τ - 1) τ ⌊s 1⌋ (-⌊s 0⌋) := by
  apply sigmaSHonest_eq_sigmaS _ _ _ _ _ hτ0
  · linarith [fracSymplecticFormRat_hjReduceChar_pos s hτ0]
  · linarith [fracSymplecticFormRat_hjReduceChar_lt_add_one s hτ0]
  · have hlat := sigmaSLatticeFree_fracSymplecticFormRat hτ
      ((isIntegralIndex_hjReduceChar_iff s).not.mpr hs)
    simpa [sub_eq_add_neg] using hlat.add 0 (-1)
  · exact (fracSymplecticFormRat_eq_hjReduceChar_add s τ).symm

/-! ### The telescoped word product

The word walk of `A_{0,N}` is followed along a *companion sequence* `x` of the expansion of `β`
(`IsHJCompanion`, `SICs.SL2Z.HJExpansion`): a sequence with `x_n = b_n - 1/x_{n+1}` for the partial
quotients `b_n` of `β`. The rotated numbers `β_n` form one, and so do the Galois conjugates `β'_n`
of a reduced real quadratic `β`, which is how [72, Kopp (2024), Definition 7.13, `defn:tangedalu`]'s
invariant at the second place `U^{(2)}` is reached by the same telescoping as `U^{(1)}`. The walk
seeded at `(⟨⟨s, x_N⟩⟩, x_N)` visits `(⟨⟨A_{m,N}s, x_m⟩⟩, x_m)`, because `A_{m,N}·x_N = x_m`
(`IsHJCompanion.flt_hjCycleMatrix`), and the finite `q`-Pochhammer factors cancel between
consecutive steps by the companion form of the dual shift
(`hjShintaniArgCompanion_succ_sub_one_div`). The induction runs along the left-peeling recursion
of the cycle matrices with the seed characteristic `s` fixed, `β` replaced by `β_1`, and `x` by its
shift; the characteristic `r = A_{0,N}s` whose cycle data appear on the right changes accordingly,
which is why it is a parameter tied to `s` by an equation rather than a `let`.

The hypotheses on `x` are that every term is positive and irrational; for `x = hjPeriod β` these
follow from `1 < β` and the irrationality of `β`, for the conjugates from `0 < β' < 1`. -/

/-- **The shifted conjugate Shintani arguments are lattice-free**: `w'_n - 1 ∉ ℤx_n + ℤ` for
`r ∉ ℤ²` and irrational `x_n`, since `w'_n = ⟨⟨r_n, x_n⟩⟩` with `r_n ∉ ℤ²`
(`not_isIntegralIndex_hjChar`). -/
theorem sigmaSLatticeFree_hjShintaniArgCompanion_sub_one {r : Fin 2 → ℚ}
    (hr : ¬ IsIntegralIndex r) (β : ℝ) {x : ℕ → ℝ} {n : ℕ} (hxn : Irrational (x n)) :
    SigmaSLatticeFree (x n) (hjShintaniArgCompanion r β x n - 1) := by
  have hlat := sigmaSLatticeFree_fracSymplecticFormRat hxn (not_isIntegralIndex_hjChar hr β n)
  simpa [hjShintaniArgCompanion, sub_eq_add_neg] using hlat.add 0 (-1)

/-- Applying the inverse HJ generator recovers a vector from its image. -/
private lemma ratVecAction_hjGenerator_inv_of_eq (b : ℤ) {u r : Fin 2 → ℚ}
    (h : ratVecAction (((T ^ b * S : SL(2, ℤ)) : Mat(2, ℤ))) u = r) :
    ratVecAction ((((T ^ b * S)⁻¹ : SL(2, ℤ)) : Mat(2, ℤ))) r = u := by
  rw [← h, ratVecAction_inv_ratVecAction]

/-- The dual finite factor at step one is the direct finite factor at step zero, along a
companion sequence: the indices agree because `(T^{b_0}S u)₂ = u₁`, the arguments modulo `ℤ` by
`hjShintaniArgCompanion_succ_sub_one_div`, and the moduli by `-1/x_1 = x_0 - b_0`. -/
private lemma qPochhammerFin_hjCycle_dual {β : ℝ} {x : ℕ → ℝ} (hx : IsHJCompanion β x)
    (r u : Fin 2 → ℚ)
    (hru : ratVecAction
      (((T ^ hjLetter β * S : SL(2, ℤ)) : Mat(2, ℤ))) u = r) :
    qPochhammerFin ⌊u 0⌋
        (((hjShintaniArgCompanion r β x 1 - 1) / x 1 : ℝ) : ℂ)
        (((-1 / x 1 : ℝ) : ℂ)) =
      qPochhammerFin ⌊r 1⌋ ((hjShintaniArgCompanion r β x 0 - 1 : ℝ) : ℂ) (x 0 : ℂ) := by
  have hi : ⌊u 0⌋ = ⌊r 1⌋ := by
    have hu : u 0 = r 1 := by
      rw [← congrFun hru 1]
      exact (ratVecAction_T_zpow_mul_S_apply_one (hjLetter β) u).symm
    rw [hu]
  obtain ⟨k, hk⟩ := hjShintaniArgCompanion_succ_sub_one_div r hx 0
  have hm : -1 / x 1 = x 0 + (-(hjLetter β) : ℤ) := by
    have hrec := (hx 0).2
    rw [hjPeriod_zero] at hrec
    norm_num at hrec
    rw [div_eq_mul_inv, neg_one_mul]
    calc
      -(x 1)⁻¹ = x 0 - (hjLetter β : ℝ) := by linarith
      _ = x 0 + (-(hjLetter β) : ℤ) := by push_cast; ring
  rw [hi]
  calc
    qPochhammerFin ⌊r 1⌋
        (((hjShintaniArgCompanion r β x 1 - 1) / x 1 : ℝ) : ℂ) (((-1 / x 1 : ℝ) : ℂ)) =
        qPochhammerFin ⌊r 1⌋ (((hjShintaniArgCompanion r β x 0 - 1 : ℝ) : ℂ) + k)
          (((-1 / x 1 : ℝ) : ℂ)) := by congr 2; exact_mod_cast hk
    _ = qPochhammerFin ⌊r 1⌋ ((hjShintaniArgCompanion r β x 0 - 1 : ℝ) : ℂ)
          (((-1 / x 1 : ℝ) : ℂ)) := qPochhammerFin_add_intCast _ _ _ _
    _ = qPochhammerFin ⌊r 1⌋ ((hjShintaniArgCompanion r β x 0 - 1 : ℝ) : ℂ)
          (x 0 : ℂ) := by
      rw [show (((-1 / x 1 : ℝ) : ℂ)) = (x 0 : ℂ) + (-(hjLetter β) : ℤ) by
        exact_mod_cast hm]
      exact qPochhammerFin_tau_add_intCast _ _ _ _

/-- The `σ_S` factor peeled off first by the walk seeded at `A_{0,N}` and `(⟨⟨s,x_N⟩⟩, x_N)`, in
`sigmaS` form at the base point `w'_0 - 1` of `u = A_{0,N}s`: the covariance of the pairing turns
its argument into `⟨⟨u, x_0⟩⟩` (`fracSymplecticFormRat_ratVecAction`,
`IsHJCompanion.flt_hjCycleMatrix`, `IsHJCompanion.fltDenominator_hjCycleMatrix`), and
`sigmaSHonest_fracSymplecticFormRat` reduces it. -/
private lemma sigmaSHonest_hjCycle_peel {β : ℝ} {x : ℕ → ℝ} (hx : IsHJCompanion β x)
    (hx0 : Irrational (x 0)) (hxpos : ∀ n, 0 < x n)
    {s : Fin 2 → ℚ} (hs : ¬ IsIntegralIndex s) (N : ℕ) {u : Fin 2 → ℚ}
    (hu : ratVecAction (hjCycleMatrix β N : SL(2, ℤ)) s = u) :
    sigmaSHonest
        (fracSymplecticFormRat s (x N) /
          fltDenominator (hjCycleMatrix β N : SL(2, ℤ)) (x N))
        (flt (hjCycleMatrix β N : SL(2, ℤ)) (x N)) =
      qPochhammerFin ⌊u 1⌋ ((hjShintaniArgCompanion u β x 0 - 1 : ℝ) : ℂ) (x 0 : ℂ) /
          qPochhammerFin ⌊u 0⌋ (((hjShintaniArgCompanion u β x 0 - 1) / x 0 : ℝ) : ℂ)
            (((-1 / x 0 : ℝ) : ℂ)) *
        sigmaSBase (hjShintaniArgCompanion u β x 0 - 1) (x 0) := by
  subst hu
  have hden : fltDenominator
      (hjCycleMatrix β N : SL(2, ℤ)) (x N) ≠ 0 := by
    rw [hx.fltDenominator_hjCycleMatrix]
    exact (Finset.prod_pos fun i _ ↦ hxpos (i + 1)).ne'
  have hfrac : fracSymplecticFormRat s (x N) /
      fltDenominator (hjCycleMatrix β N : SL(2, ℤ)) (x N) =
      fracSymplecticFormRat
        (ratVecAction (hjCycleMatrix β N : SL(2, ℤ)) s) (x 0) := by
    have h := fracSymplecticFormRat_ratVecAction
      (hjCycleMatrix β N : SL(2, ℤ)) s (x N) hden
    rw [hx.flt_hjCycleMatrix] at h
    simpa using h.symm
  have hsu : ¬ IsIntegralIndex
      (ratVecAction (hjCycleMatrix β N : SL(2, ℤ)) s) :=
    (isIntegralIndex_ratVecAction_iff (hjCycleMatrix β N)).not.mpr hs
  rw [hx.flt_hjCycleMatrix, hfrac,
    sigmaSHonest_fracSymplecticFormRat hx0 (hxpos 0) hsu]
  simp only [hjShintaniArgCompanion, hjChar_zero]
  rw [sigmaS]
  simp only [neg_neg]
  push_cast
  rfl

/-- **The word walk along a cycle, telescoped along a companion sequence.** For an irrational
`β`, a companion sequence `x` of its expansion with positive irrational terms, a characteristic
`s ∉ ℤ²`, and `r = A_{0,N}s`,

$$
\sigma_{A_{0,N}}(\langle\!\langle s,x_N\rangle\!\rangle, x_N)
  \cdot \varpi_{\lfloor r_2\rfloor}(w'_0 - 1, x_0)
  = \varpi_{\lfloor s_2\rfloor}(w'_N - 1, x_N)
    \prod_{m<N} \sigma_S^{\mathrm{base}}(w'_{m+1} - 1, x_{m+1}),
$$

where `w'_n = ⟨⟨r_n, x_n⟩⟩` are the conjugate Shintani arguments of `r` along `x`. At
`x = hjPeriod β` this is the real-line form of the telescoping in the proof of
[72, Kopp (2024), Proposition 7.20, `prop:almost`]; see the file docstring for why consecutive
`q`-Pochhammer factors cancel. No periodicity is assumed. -/
theorem wordSigmaS_hjCycleMatrix_mul_qPochhammerFin {β : ℝ} (hβ : Irrational β) {x : ℕ → ℝ}
    (hx : IsHJCompanion β x) (hxirr : ∀ n, Irrational (x n)) (hxpos : ∀ n, 0 < x n)
    {s : Fin 2 → ℚ} (hs : ¬ IsIntegralIndex s) (N : ℕ) {r : Fin 2 → ℚ}
    (hr : ratVecAction (hjCycleMatrix β N : SL(2, ℤ)) s = r)
    (h0 : 0 ≤ (hjCycleMatrix β N) 1 0) :
    wordSigmaS (fracSymplecticFormRat s (x N)) (x N) (hjCycleMatrix β N) h0 *
        qPochhammerFin ⌊r 1⌋ ((hjShintaniArgCompanion r β x 0 - 1 : ℝ) : ℂ) (x 0 : ℂ) =
      qPochhammerFin ⌊s 1⌋ ((hjShintaniArgCompanion r β x N - 1 : ℝ) : ℂ) (x N : ℂ) *
        ∏ m ∈ Finset.range N,
          sigmaSBase (hjShintaniArgCompanion r β x (m + 1) - 1) (x (m + 1)) := by
  induction N generalizing β x r with
  | zero =>
      rw [hjCycleMatrix_zero, Matrix.SpecialLinearGroup.coe_one, ratVecAction_one] at hr
      subst r
      rw [wordSigmaS_of_lowerLeft_eq_zero _ _ _ h0 (by simp)]
      simp
  | succ N ih =>
      let β' := hjRotate β
      let x' : ℕ → ℝ := fun n ↦ x (n + 1)
      let A' := hjCycleMatrix β' N
      let u := ratVecAction ((A' : SL(2, ℤ)) : Mat(2, ℤ)) s
      have hβ' : Irrational β' := irrational_hjRotate hβ
      have hx' : IsHJCompanion β' x' := hx.shift
      have h0' : 0 ≤ A' 1 0 := lowerLeft_hjCycleMatrix_nonneg hβ' N
      have hru : ratVecAction
          (((T ^ hjLetter β * S : SL(2, ℤ)) : Mat(2, ℤ))) u = r := by
        simpa [u, A', β', hjCycleMatrix_succ, Matrix.SpecialLinearGroup.coe_mul,
          ratVecAction_mul] using hr
      have hu : ratVecAction
          ((((T ^ hjLetter β * S)⁻¹ : SL(2, ℤ)) : Mat(2, ℤ))) r = u :=
        ratVecAction_hjGenerator_inv_of_eq (hjLetter β) hru
      have hw (m : ℕ) : hjShintaniArgCompanion r β x (m + 1) =
          hjShintaniArgCompanion u β' x' m := by
        rw [hjShintaniArgCompanion_succ_left, hu]
      have hwalk := wordSigmaS_step
        (fracSymplecticFormRat s (x (N + 1))) (x (N + 1)) h0
        (lowerLeft_hjCycleMatrix_pos hβ (Nat.succ_ne_zero N)).ne'
        (congrArg Prod.snd (hjStep_hjCycleMatrix hβ N)) h0'
      have hsig := sigmaSHonest_hjCycle_peel hx' (hxirr 1) (fun n ↦ hxpos (n + 1))
        hs N (u := u) rfl
      have hdual : qPochhammerFin ⌊u 0⌋
          (((hjShintaniArgCompanion u β' x' 0 - 1) / x' 0 : ℝ) : ℂ)
          (((-1 / x' 0 : ℝ) : ℂ)) =
          qPochhammerFin ⌊r 1⌋ ((hjShintaniArgCompanion r β x 0 - 1 : ℝ) : ℂ) (x 0 : ℂ) := by
        have hd := qPochhammerFin_hjCycle_dual hx r u hru
        rw [hw 0] at hd
        exact hd
      have hrr : ¬ IsIntegralIndex r :=
        hru ▸ (isIntegralIndex_ratVecAction_iff (T ^ hjLetter β * S)).not.mpr
          ((isIntegralIndex_ratVecAction_iff (A' : SL(2, ℤ))).not.mpr hs)
      have hqp : qPochhammerFin ⌊r 1⌋
          ((hjShintaniArgCompanion r β x 0 - 1 : ℝ) : ℂ) (x 0 : ℂ) ≠ 0 :=
        qPochhammerFin_ne_zero_of_forall_factor_ne_zero _ _ _
          (sigmaSLatticeFree_hjShintaniArgCompanion_sub_one hrr β (hxirr 0)).one_sub_exp_ne_zero
      have hih := ih hβ' hx' (fun n ↦ hxirr (n + 1)) (fun n ↦ hxpos (n + 1))
        (r := u) rfl h0'
      rw [hwalk, hsig, hdual]
      have hcancel :
          (qPochhammerFin ⌊u 1⌋
                ((hjShintaniArgCompanion u β' x' 0 - 1 : ℝ) : ℂ) (x' 0 : ℂ) /
              qPochhammerFin ⌊r 1⌋
                ((hjShintaniArgCompanion r β x 0 - 1 : ℝ) : ℂ) (x 0 : ℂ) *
              sigmaSBase (hjShintaniArgCompanion u β' x' 0 - 1) (x' 0)) *
                wordSigmaS (fracSymplecticFormRat s (x' N)) (x' N) A' h0' *
              qPochhammerFin ⌊r 1⌋
                ((hjShintaniArgCompanion r β x 0 - 1 : ℝ) : ℂ) (x 0 : ℂ) =
            (wordSigmaS (fracSymplecticFormRat s (x' N)) (x' N) A' h0' *
                qPochhammerFin ⌊u 1⌋
                  ((hjShintaniArgCompanion u β' x' 0 - 1 : ℝ) : ℂ) (x' 0 : ℂ)) *
              sigmaSBase (hjShintaniArgCompanion u β' x' 0 - 1) (x' 0) := by
        field_simp
      rw [hcancel, hih, Finset.prod_range_succ']
      simp_rw [hw]
      simp [x']
      ring

/-! ### Kopp's Proposition 7.20 at both real places

When the companion sequence closes, `x_N = x_0`, and `A_{0,N} ∈ Γ_r`, the boundary factors of the
telescoped product cancel against the finite denominator of [AFK25, equation (1.26),
`eq:shindf`], and the real cocycle at `x_0` is the product of the base values. At `x = hjPeriod β`
this is [72, Kopp (2024), Proposition 7.20, `prop:almost`]; at the conjugates `x = β'` it is the
same statement for `U^{(2)}`, which Kopp does not state: the cycle matrix fixes `β'` as well as
`β`, with `j_A(β') = ε'^k > 0`. -/

/-- The transformed second-coordinate floor and the cocycle index add to the original floor. -/
private lemma floor_ratVecAction_add_nQPInt {r : Fin 2 → ℚ}
    {A : SL(2, ℤ)} (hA : A ∈ gammaSubgroup r) :
    ⌊ratVecAction (A : Mat(2, ℤ)) r 1⌋ +
        nQPInt r (A : Mat(2, ℤ)) = ⌊r 1⌋ := by
  have heq : r 1 = ratVecAction (A : Mat(2, ℤ)) r 1 +
      (nQPInt r (A : Mat(2, ℤ)) : ℚ) := by
    rw [nQPInt_cast_of_mem hA]
    simp only [nQP, ratVecAction, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.map_apply]
    ring
  rw [heq, Int.floor_add_intCast]

/-- At a closed cycle, the finite cocycle denominator joins the left boundary factor: with
`A = A_{0,N}` fixing `x_0` (`IsHJCompanion.flt_hjCycleMatrix_of_eq`) and `r' = Ar ≡ r`,
`⟨⟨r,x_0⟩⟩/j_A(x_0) = ⟨⟨r',x_0⟩⟩ = (w'_0 - 1) + ⌊r'_2⌋x_0 - ⌊r'_1⌋`
(`fracSymplecticFormRat_eq_hjReduceChar_add`, `hjReduceChar_congr`), and
`qPochhammerFin_add` with `floor_ratVecAction_add_nQPInt`. -/
private lemma qPochhammerFin_hjCycle_boundary {β : ℝ} {x : ℕ → ℝ} (hx : IsHJCompanion β x)
    (hx0 : Irrational (x 0)) {N : ℕ} (hxN : x N = x 0) {r : Fin 2 → ℚ}
    (hr : ¬ IsIntegralIndex r)
    (hA : (hjCycleMatrix β N : SL(2, ℤ)) ∈
      gammaSubgroup r) :
    let A := hjCycleMatrix β N
    let r' := ratVecAction ((A : SL(2, ℤ)) : Mat(2, ℤ)) r
    qPochhammerFin ⌊r' 1⌋ ((hjShintaniArgCompanion r β x 0 - 1 : ℝ) : ℂ) (x 0 : ℂ) *
        qPochhammerFin (nQPInt r ((A : SL(2, ℤ)) : Mat(2, ℤ)))
          (((fracSymplecticFormRat r (x 0) : ℝ) : ℂ) /
            ((fltDenominator ((A : SL(2, ℤ)) : Mat(2, ℤ)) (x 0) : ℝ) : ℂ))
          ((flt ((A : SL(2, ℤ)) : Mat(2, ℤ)) (x 0) : ℝ) : ℂ) =
      qPochhammerFin ⌊r 1⌋ ((hjShintaniArgCompanion r β x 0 - 1 : ℝ) : ℂ) (x 0 : ℂ) := by
  dsimp only
  let A := hjCycleMatrix β N
  let r' := ratVecAction ((A : SL(2, ℤ)) : Mat(2, ℤ)) r
  have hfix : flt ((A : SL(2, ℤ)) : Mat(2, ℤ)) (x 0) = x 0 :=
    hx.flt_hjCycleMatrix_of_eq hxN
  have hden : fltDenominator
      ((A : SL(2, ℤ)) : Mat(2, ℤ)) (x 0) ≠ 0 := by
    rw [hx.fltDenominator_hjCycleMatrix_of_eq hxN, Finset.prod_ne_zero_iff]
    intro i _
    exact (hx i).1
  have htrans : fracSymplecticFormRat r (x 0) /
      fltDenominator ((A : SL(2, ℤ)) : Mat(2, ℤ)) (x 0) =
        fracSymplecticFormRat r' (x 0) := by
    have h := fracSymplecticFormRat_ratVecAction
      (((A : SL(2, ℤ)) : Mat(2, ℤ))) r (x 0) hden
    rw [hfix] at h
    simpa [r'] using h.symm
  have hred : hjReduceChar r' = hjReduceChar r :=
    hjReduceChar_congr (ratVecAction_sub_intVec_of_mem_gammaSubgroup hA)
  have harg : ((fracSymplecticFormRat r (x 0) : ℝ) : ℂ) /
        ((fltDenominator ((A : SL(2, ℤ)) : Mat(2, ℤ)) (x 0) : ℝ) : ℂ) =
      ((hjShintaniArgCompanion r β x 0 - 1 : ℝ) : ℂ) + (⌊r' 1⌋ : ℂ) * (x 0 : ℂ) +
        ((-⌊r' 0⌋ : ℤ) : ℂ) := by
    exact_mod_cast (htrans.trans (by
      rw [fracSymplecticFormRat_eq_hjReduceChar_add, hred]
      simp only [hjShintaniArgCompanion, hjChar_zero]))
  rw [hfix, harg]
  rw [qPochhammerFin_add_intCast]
  rw [← qPochhammerFin_add]
  · rw [floor_ratVecAction_add_nQPInt hA]
  · exact (sigmaSLatticeFree_hjShintaniArgCompanion_sub_one hr β hx0).one_sub_exp_ne_zero

/-- A finite product is unchanged by a cyclic shift when its two boundary values agree. -/
private lemma prod_range_succ_eq_of_last_eq_first {f : ℕ → ℂ} {N : ℕ} (h0 : f 0 ≠ 0)
    (hN : f N = f 0) :
    (∏ n ∈ Finset.range N, f (n + 1)) = ∏ n ∈ Finset.range N, f n := by
  apply mul_left_cancel₀ h0
  calc
    f 0 * ∏ n ∈ Finset.range N, f (n + 1) =
        (∏ n ∈ Finset.range N, f (n + 1)) * f 0 := by ring
    _ = ∏ n ∈ Finset.range (N + 1), f n := (Finset.prod_range_succ' f N).symm
    _ = (∏ n ∈ Finset.range N, f n) * f N := Finset.prod_range_succ f N
    _ = f 0 * ∏ n ∈ Finset.range N, f n := by rw [hN]; ring

/-- The telescoped word identity with both ends identified along a closed companion sequence:
`wordSigmaS_hjCycleMatrix_mul_qPochhammerFin` at `s = r`, `r' = Ar`, whose cycle data are those
of `r` (`hjShintaniArgCompanion_congr`), with `w'_N = w'_0`
(`hjShintaniArgCompanion_of_mem_gammaSubgroup`) and the product shifted back by one step
(`prod_range_succ_eq_of_last_eq_first`). -/
private lemma wordSigmaS_hjCycleMatrix_closed {β : ℝ} (hβ : Irrational β) {x : ℕ → ℝ}
    (hx : IsHJCompanion β x) (hxirr : ∀ n, Irrational (x n)) (hxpos : ∀ n, 0 < x n)
    {N : ℕ} (hxN : x N = x 0) {r : Fin 2 → ℚ} (hr : ¬ IsIntegralIndex r)
    (hA : (hjCycleMatrix β N : SL(2, ℤ)) ∈
      gammaSubgroup r) (h0 : 0 ≤ (hjCycleMatrix β N) 1 0) :
    let r' := ratVecAction
      (hjCycleMatrix β N : SL(2, ℤ)) r
    wordSigmaS (fracSymplecticFormRat r (x 0)) (x 0) (hjCycleMatrix β N) h0 *
        qPochhammerFin ⌊r' 1⌋
          ((hjShintaniArgCompanion r β x 0 - 1 : ℝ) : ℂ) (x 0 : ℂ) =
      qPochhammerFin ⌊r 1⌋
          ((hjShintaniArgCompanion r β x 0 - 1 : ℝ) : ℂ) (x 0 : ℂ) *
        ∏ n ∈ Finset.range N,
          sigmaSBase (hjShintaniArgCompanion r β x n - 1) (x n) := by
  dsimp only
  let r' := ratVecAction
    (hjCycleMatrix β N : SL(2, ℤ)) r
  have hw (n : ℕ) : hjShintaniArgCompanion r' β x n =
      hjShintaniArgCompanion r β x n :=
    hjShintaniArgCompanion_congr (ratVecAction_sub_intVec_of_mem_gammaSubgroup hA) β x n
  have h := wordSigmaS_hjCycleMatrix_mul_qPochhammerFin hβ hx hxirr hxpos hr N
    (r := r') rfl h0
  rw [hxN] at h
  simp_rw [hw] at h
  rw [hjShintaniArgCompanion_of_mem_gammaSubgroup hA hxN] at h
  let f : ℕ → ℂ := fun n ↦
    sigmaSBase (hjShintaniArgCompanion r β x n - 1) (x n)
  have hf0 : f 0 ≠ 0 := by
    change sigmaSBase (hjShintaniArgCompanion r β x 0 - 1) (x 0) ≠ 0
    rw [sigmaSBase_eq_exp_div]
    exact div_ne_zero (Complex.exp_ne_zero _)
      (by rw [sub_add_cancel]; exact_mod_cast
        doubleSine_ne_zero (hjShintaniArgCompanion r β x 0) (x 0) 1)
  have hfN : f N = f 0 := by
    simp only [f]
    rw [hjShintaniArgCompanion_of_mem_gammaSubgroup hA hxN, hxN]
  rw [prod_range_succ_eq_of_last_eq_first hf0 hfN] at h
  exact h

/-- Cancelling a nonzero boundary factor turns two product identities into a quotient identity. -/
private lemma div_eq_of_boundary_products {w d l b p : ℂ} (hl : l ≠ 0) (hd : d ≠ 0)
    (hwalk : w * l = b * p) (hboundary : l * d = b) : w / d = p := by
  rw [div_eq_iff hd]
  apply mul_right_cancel₀ hl
  rw [mul_assoc, hwalk, ← hboundary]
  ring

/-- **The real modular cocycle at a closed companion sequence is the product of the base
values**: for an irrational `β`, a companion sequence `x` of its expansion with positive irrational
terms and `x_N = x_0`, `r ∉ ℤ²`, and `A = A_{0,N} ∈ Γ_r`,

$$
ש^{\mathbf r}_A(x_0) = \prod_{n<N} \sigma_S^{\mathrm{base}}(w'_n - 1, x_n).
$$

At `x = hjPeriod β` this is [72, Kopp (2024), Proposition 7.20, `prop:almost`] before the base
values are unfolded (`starkTangedalYamamoto_mul_sfModularCocycleReal` is Kopp's form); at the
conjugates it is the corresponding statement at `β'`. From `wordSigmaS_hjCycleMatrix_closed`,
`qPochhammerFin_hjCycle_boundary` and `div_eq_of_boundary_products`, the nonvanishing of the
factors coming from `sigmaSLatticeFree_hjShintaniArgCompanion_sub_one` and
`qPochhammerFin_nQPInt_ne_zero_of_irrational`. -/
theorem sfModularCocycleReal_hjCycleMatrix_eq_prod {β : ℝ} (hβ : Irrational β)
    {x : ℕ → ℝ} (hx : IsHJCompanion β x) (hxirr : ∀ n, Irrational (x n))
    (hxpos : ∀ n, 0 < x n) {N : ℕ} (hxN : x N = x 0) {r : Fin 2 → ℚ}
    (hr : ¬ IsIntegralIndex r)
    (hA : (hjCycleMatrix β N : SL(2, ℤ)) ∈ gammaSubgroup r)
    (h0 : 0 ≤ (hjCycleMatrix β N) 1 0) :
    sfModularCocycleReal r (hjCycleMatrix β N) hA h0 (x 0) =
      ∏ n ∈ Finset.range N, sigmaSBase (hjShintaniArgCompanion r β x n - 1) (x n) := by
  let A := hjCycleMatrix β N
  let r' := ratVecAction ((A : SL(2, ℤ)) : Mat(2, ℤ)) r
  have hwalk := wordSigmaS_hjCycleMatrix_closed hβ hx hxirr hxpos hxN hr hA h0
  dsimp only at hwalk
  have hboundary : qPochhammerFin ⌊r' 1⌋
          ((hjShintaniArgCompanion r β x 0 - 1 : ℝ) : ℂ) (x 0 : ℂ) *
        qPochhammerFin
          (nQPInt r ((A : SL(2, ℤ)) : Mat(2, ℤ)))
          (((fracSymplecticFormRat r (x 0) : ℝ) : ℂ) /
            ((fltDenominator ((A : SL(2, ℤ)) : Mat(2, ℤ)) (x 0) : ℝ) : ℂ))
          ((flt ((A : SL(2, ℤ)) : Mat(2, ℤ)) (x 0) : ℝ) : ℂ) =
      qPochhammerFin ⌊r 1⌋
        ((hjShintaniArgCompanion r β x 0 - 1 : ℝ) : ℂ) (x 0 : ℂ) := by
    simpa only [A, r'] using qPochhammerFin_hjCycle_boundary hx (hxirr 0) hxN hr hA
  have hleft : qPochhammerFin ⌊r' 1⌋
      ((hjShintaniArgCompanion r β x 0 - 1 : ℝ) : ℂ) (x 0 : ℂ) ≠ 0 :=
    qPochhammerFin_ne_zero_of_forall_factor_ne_zero _ _ _
      (sigmaSLatticeFree_hjShintaniArgCompanion_sub_one hr β (hxirr 0)).one_sub_exp_ne_zero
  have hden : fltDenominator
      ((A : SL(2, ℤ)) : Mat(2, ℤ)) (x 0) ≠ 0 := by
    rw [hx.fltDenominator_hjCycleMatrix_of_eq hxN]
    exact (Finset.prod_pos fun i _ ↦ hxpos (i + 1)).ne'
  have hdenqp := qPochhammerFin_nQPInt_ne_zero_of_irrational hr
    (((A : SL(2, ℤ)) : Mat(2, ℤ))) (hxirr 0) hden
  rw [sfModularCocycleReal_eq_of_not_isIntegralIndex hr]
  change wordSigmaS (fracSymplecticFormRat r (x 0)) (x 0) A h0 / _ = _
  exact div_eq_of_boundary_products hleft hdenqp hwalk hboundary

/-- **Kopp's Proposition 7.20 along a companion sequence**: for an irrational `β`, a companion
sequence `x` of its expansion with positive irrational terms and `x_N = x_0`, `r ∉ ℤ²`, and
`A = A_{0,N} ∈ Γ_r`,

$$
\Bigl(\prod_{n<N} S_2(w'_n, x_n)\Bigr)\cdot ש^{\mathbf r}_A(x_0)
  = e\!\Bigl(\sum_{n<N}\Bigl(\frac{x_n - 3 + x_n^{-1}}{24}
      + \frac{(x_n - w'_n)(1 - w'_n)}{4x_n}\Bigr)\Bigr),
$$

with `w'_n = ⟨⟨r_n, x_n⟩⟩` and the product `starkTangedalYamamotoConj r β x N`. At
`x = hjPeriod β` this is [72, Kopp (2024), Proposition 7.20, `prop:almost`]
(`starkTangedalYamamoto_mul_sfModularCocycleReal`); at the conjugates `x_n = β'_n` of a reduced
real quadratic `β` it evaluates `U^{(2)}` of [72, Kopp (2024), Definition 7.13, `defn:tangedalu`],
which Kopp does not do. Proof: `sfModularCocycleReal_hjCycleMatrix_eq_prod`, then each
factor `S₂(w'_n, x_n)·σ_S^{base}(w'_n - 1, x_n) = exp(X(w'_n - 1, x_n))` (`sigmaSBase_eq_exp_div`)
with the exponent of `sfExpArg_sub_one`. -/
theorem starkTangedalYamamotoConj_mul_sfModularCocycleReal {β : ℝ} (hβ : Irrational β)
    {x : ℕ → ℝ} (hx : IsHJCompanion β x) (hxirr : ∀ n, Irrational (x n))
    (hxpos : ∀ n, 0 < x n) {N : ℕ} (hxN : x N = x 0) {r : Fin 2 → ℚ}
    (hr : ¬ IsIntegralIndex r)
    (hA : (hjCycleMatrix β N : SL(2, ℤ)) ∈ gammaSubgroup r)
    (h0 : 0 ≤ (hjCycleMatrix β N) 1 0) :
    (starkTangedalYamamotoConj r β x N : ℂ) *
        sfModularCocycleReal r (hjCycleMatrix β N) hA h0 (x 0) =
      Complex.exp (2 * π * I * ((∑ n ∈ Finset.range N,
        ((x n - 3 + (x n)⁻¹) / 24 +
          (x n - hjShintaniArgCompanion r β x n) * (1 - hjShintaniArgCompanion r β x n) /
            (4 * x n)) : ℝ) : ℂ)) := by
  rw [sfModularCocycleReal_hjCycleMatrix_eq_prod hβ hx hxirr hxpos hxN hr hA h0]
  rw [starkTangedalYamamotoConj, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  have hfactor (n : ℕ) :
      (doubleSine' (hjShintaniArgCompanion r β x n) (x n) : ℂ) *
          sigmaSBase (hjShintaniArgCompanion r β x n - 1) (x n) =
        Complex.exp (sfExpArg (hjShintaniArgCompanion r β x n - 1) (x n)) := by
    rw [sigmaSBase_eq_exp_div, sub_add_cancel]
    field_simp [doubleSine_ne_zero]
  simp_rw [hfactor]
  rw [← Complex.exp_sum]
  congr 1
  simp_rw [sfExpArg_sub_one _ _ (hxpos _).ne']
  rw [← Finset.mul_sum, ← Complex.ofReal_sum]

/-- **[72, Kopp (2024), Proposition 7.20, `prop:almost`], for the real cocycle value**: for an
irrational `β > 1` with `β_N = β`, `r ∉ ℤ²`, and `A = A_{0,N} ∈ Γ_r`,

$$
U^{(1)}\cdot ש^{\mathbf r}_A(\beta)
  = e\!\left(\tfrac{1}{24}\gamma(A) + \tfrac14\lambda_{\mathbf r}(A)\right),
$$

that is `U^{(1)}(𝒜)⁻¹ = e(-γ(A)/24 - λ_r(A)/4)·ש^r_A(β)` in Kopp's arrangement. Kopp's `β` is a
reduced quadratic irrational, `0 < β' < 1 < β`, which is what makes its expansion purely periodic
([72, Kopp (2024), Proposition 7.2, `prop:quadhj`]); here the closing of the cycle is the
hypothesis. This is `starkTangedalYamamotoConj_mul_sfModularCocycleReal` along the rotated numbers
(`isHJCompanion_hjPeriod`), whose conjugate Shintani arguments are the Shintani arguments
(`hjShintaniArg_eq_hjShintaniArgCompanion`) and whose exponent sums to
`γ(A)/24 + λ_r(A)/4`. -/
@[source "72, Proposition 7.20, p. 73, prop:almost"]
theorem starkTangedalYamamoto_mul_sfModularCocycleReal {β : ℝ} (hβ : Irrational β) (hβ1 : 1 < β)
    {N : ℕ} (hN : hjPeriod β N = β) {r : Fin 2 → ℚ} (hr : ¬ IsIntegralIndex r)
    (hA : (hjCycleMatrix β N : SL(2, ℤ)) ∈ gammaSubgroup r)
    (h0 : 0 ≤ (hjCycleMatrix β N) 1 0) :
    (starkTangedalYamamoto r β N : ℂ) * sfModularCocycleReal r (hjCycleMatrix β N) hA h0 β =
      Complex.exp (2 * π * I * ((hjGamma β N / 24 + hjLambda r β N / 4 : ℝ) : ℂ)) := by
  have h := starkTangedalYamamotoConj_mul_sfModularCocycleReal hβ (isHJCompanion_hjPeriod hβ)
    (irrational_hjPeriod hβ) (fun n => zero_lt_one.trans (one_lt_hjPeriod hβ hβ1 n)) hN hr hA h0
  rw [hjPeriod_zero] at h
  have hU : starkTangedalYamamotoConj r β (hjPeriod β) N = starkTangedalYamamoto r β N := rfl
  rw [hU] at h
  rw [h]
  congr 3
  unfold hjGamma hjLambda
  rw [Finset.sum_add_distrib, Finset.sum_div]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n _
  simp only [hjShintaniArg_eq_hjShintaniArgCompanion]
  ring

/-! ### The phases

The global phase is the Rademacher invariant, and the two reflected invariants multiply to one. -/

/-- **[72, Kopp (2024), Proposition 7.21, `prop:globalphase`], last identity**: along a closed
cycle, `γ(A) = Ψ(A)` for the Rademacher invariant `Ψ` of `SICs.SL2Z.Rademacher`. From
`hjGamma_eq_wordRademacher` and `wordRademacher_eq_rademacherInvariant`, whose trace hypothesis
holds because `A` fixes `β` with positive Jacobi denominator
(`trace_pos_of_flt_eq_self`, `fltDenominator_hjCycleMatrix_pos_of_hjPeriod_eq`). Kopp
writes the right-hand side as `Ψ(P, √j_P)` in the metaplectic notation of his Section 2.5. -/
@[source "72, Proposition 7.21, p. 74, prop:globalphase (last identity)"]
theorem hjGamma_eq_rademacherInvariant {β : ℝ} (hβ : Irrational β) {N : ℕ}
    (hN : hjPeriod β N = β) :
    hjGamma β N = (rademacherInvariant (hjCycleMatrix β N) : ℝ) := by
  have h0 := lowerLeft_hjCycleMatrix_nonneg hβ N
  have hterm : (hjCycleMatrix β N) 1 0 = 0 → 0 < (hjCycleMatrix β N) 0 0 := by
    intro hz
    have hN0 : N = 0 := by
      by_contra hn
      have hp := lowerLeft_hjCycleMatrix_pos hβ hn
      rw [hz] at hp
      omega
    subst N
    simp
  have htr := trace_pos_of_flt_eq_self (flt_hjCycleMatrix_of_hjPeriod_eq hβ hN)
    (fltDenominator_hjCycleMatrix_pos_of_hjPeriod_eq hβ hN)
  calc
    hjGamma β N = (wordRademacher (hjCycleMatrix β N) h0 : ℝ) :=
      hjGamma_eq_wordRademacher hβ hN h0
    _ = (rademacherInvariant (hjCycleMatrix β N) : ℝ) := by
      exact_mod_cast wordRademacher_eq_rademacherInvariant
        (hjCycleMatrix β N) h0 hterm htr

/-- **The two reflected invariants multiply to one**: `U^{(1)}(r)·U^{(1)}(-r) = 1` along a closed
cycle with `A_{0,N} ∈ Γ_r`. This is the step in the proof of [72, Kopp (2024), Proposition 7.23,
`prop:lambdachi`] where Kopp concludes `U^{(1)}_𝔪(𝒜)U^{(1)}_𝔪(𝔑𝒜) = 1` from the unit modulus of
`ש^r_A(β)ש^{-r}_A(β)`; that modulus follows from the fixed-point reflection law
`sfModularCocycleReal_mul_neg_of_flt_eq_self` with the closed form
`SICs.Cocycle.Word.Reflection.wordSfExpArg_eq`, whose exponent is purely imaginary. -/
theorem starkTangedalYamamoto_mul_neg {β : ℝ} (hβ : Irrational β) (hβ1 : 1 < β) {N : ℕ}
    (hN : hjPeriod β N = β) {r : Fin 2 → ℚ} (hr : ¬ IsIntegralIndex r)
    (hA : (hjCycleMatrix β N : SL(2, ℤ)) ∈ gammaSubgroup r) :
    starkTangedalYamamoto r β N * starkTangedalYamamoto (-r) β N = 1 := by
  let A := hjCycleMatrix β N
  have h0 : 0 ≤ A 1 0 := lowerLeft_hjCycleMatrix_nonneg hβ N
  have hrneg : ¬ IsIntegralIndex (-r) := (isIntegralIndex_neg_iff r).not.mpr hr
  have hpos : 0 < starkTangedalYamamoto r β N * starkTangedalYamamoto (-r) β N :=
    mul_pos (starkTangedalYamamoto_pos r β N) (starkTangedalYamamoto_pos (-r) β N)
  -- The reflected product of the cocycle has modulus one.
  have hcocycle : ‖sfModularCocycleReal r A hA h0 β *
      sfModularCocycleReal (-r) A (neg_mem_gammaSubgroup hA) h0 β‖ = 1 :=
    norm_sfModularCocycleReal_mul_neg_of_flt_eq_self hβ hA h0
      (fltDenominator_hjCycleMatrix_pos_of_hjPeriod_eq hβ hN)
      (flt_hjCycleMatrix_of_hjPeriod_eq hβ hN)
      (sigmaSLatticeFree_fracSymplecticFormRat hβ hr)
  -- Both instances of Proposition 7.20 have a phase on the right.
  have hmul :
      ((starkTangedalYamamoto r β N * starkTangedalYamamoto (-r) β N : ℝ) : ℂ) *
          (sfModularCocycleReal r A hA h0 β *
            sfModularCocycleReal (-r) A (neg_mem_gammaSubgroup hA) h0 β) =
        Complex.exp (2 * π * I * ((hjGamma β N / 24 + hjLambda r β N / 4 : ℝ) : ℂ)) *
          Complex.exp (2 * π * I * ((hjGamma β N / 24 + hjLambda (-r) β N / 4 : ℝ) : ℂ)) := by
    rw [← starkTangedalYamamoto_mul_sfModularCocycleReal hβ hβ1 hN hr hA h0,
      ← starkTangedalYamamoto_mul_sfModularCocycleReal hβ hβ1 hN hrneg
        (neg_mem_gammaSubgroup hA) h0]
    push_cast
    ring
  have hnorm := congrArg norm hmul
  rw [norm_mul, hcocycle, mul_one, Complex.norm_real, Real.norm_of_nonneg hpos.le] at hnorm
  simpa [norm_mul, Complex.norm_exp] using hnorm

/-- **The reflected product of the cocycle along a closed cycle**:

$$
ש^{\mathbf r}_A(\beta)\,ש^{-\mathbf r}_A(\beta)
  = e\!\left(\tfrac1{12}\gamma(A) + \tfrac12\lambda_{\mathbf r}(A)\right).
$$

This is [72, Kopp (2024), Theorem 4.36, `thm:shincharacter`], `ש^r_A(β)ש^{-r}_A(β) = ψ²(A)χ_r(A)`,
with its right-hand side evaluated by [72, Kopp (2024), Proposition 7.21, `prop:globalphase`] and
[72, Kopp (2024), Proposition 7.23, `prop:lambdachi`]; the project states it without the characters,
which enter [AFK25] only through this product. Proof: multiply the two instances of
`starkTangedalYamamoto_mul_sfModularCocycleReal` at `r` and `-r`, use `hjLambda_neg` and
`starkTangedalYamamoto_mul_neg`. -/
theorem sfModularCocycleReal_mul_neg_hjCycleMatrix {β : ℝ} (hβ : Irrational β) (hβ1 : 1 < β)
    {N : ℕ} (hN : hjPeriod β N = β) {r : Fin 2 → ℚ} (hr : ¬ IsIntegralIndex r)
    (hA : (hjCycleMatrix β N : SL(2, ℤ)) ∈ gammaSubgroup r)
    (h0 : 0 ≤ (hjCycleMatrix β N) 1 0) :
    sfModularCocycleReal r (hjCycleMatrix β N) hA h0 β *
        sfModularCocycleReal (-r) (hjCycleMatrix β N) (neg_mem_gammaSubgroup hA) h0 β =
      Complex.exp (2 * π * I * ((hjGamma β N / 12 + hjLambda r β N / 2 : ℝ) : ℂ)) := by
  have hrneg : ¬ IsIntegralIndex (-r) := (isIntegralIndex_neg_iff r).not.mpr hr
  have hpos := starkTangedalYamamoto_mul_sfModularCocycleReal
    hβ hβ1 hN hr hA h0
  have hneg := starkTangedalYamamoto_mul_sfModularCocycleReal
    hβ hβ1 hN hrneg (neg_mem_gammaSubgroup hA) h0
  have hunit := starkTangedalYamamoto_mul_neg hβ hβ1 hN hr hA
  calc
    sfModularCocycleReal r (hjCycleMatrix β N) hA h0 β *
        sfModularCocycleReal (-r) (hjCycleMatrix β N) (neg_mem_gammaSubgroup hA) h0 β =
      (((starkTangedalYamamoto r β N * starkTangedalYamamoto (-r) β N : ℝ) : ℂ) *
        (sfModularCocycleReal r (hjCycleMatrix β N) hA h0 β *
          sfModularCocycleReal (-r) (hjCycleMatrix β N)
            (neg_mem_gammaSubgroup hA) h0 β)) := by rw [hunit]; simp
    _ = ((starkTangedalYamamoto r β N : ℂ) *
            sfModularCocycleReal r (hjCycleMatrix β N) hA h0 β) *
          ((starkTangedalYamamoto (-r) β N : ℂ) *
            sfModularCocycleReal (-r) (hjCycleMatrix β N)
              (neg_mem_gammaSubgroup hA) h0 β) := by
      push_cast
      ring
    _ = Complex.exp
          (2 * π * I * ((hjGamma β N / 24 + hjLambda r β N / 4 : ℝ) : ℂ)) *
        Complex.exp
          (2 * π * I * ((hjGamma β N / 24 + hjLambda (-r) β N / 4 : ℝ) : ℂ)) := by
      rw [hpos, hneg]
    _ = Complex.exp
        (2 * π * I * ((hjGamma β N / 24 + hjLambda r β N / 4 : ℝ) : ℂ) +
          2 * π * I * ((hjGamma β N / 24 + hjLambda (-r) β N / 4 : ℝ) : ℂ)) := by
      rw [Complex.exp_add]
    _ = Complex.exp
        (2 * π * I * ((hjGamma β N / 12 + hjLambda r β N / 2 : ℝ) : ℂ)) := by
      rw [hjLambda_neg hr hβ hA]
      push_cast
      ring_nf


/-- **The reflected quotient of the cocycle along a closed cycle is `U^{(1)}(r)^{-2}`**:

$$
\frac{ש^{\mathbf r}_A(\beta)}{ש^{-\mathbf r}_A(\beta)} = U^{(1)}(\mathbf r)^{-2}.
$$

The two instances of `starkTangedalYamamoto_mul_sfModularCocycleReal` at `r` and `-r` have the
same phase (`hjLambda_neg`), and `U^{(1)}(r)U^{(1)}(-r) = 1` (`starkTangedalYamamoto_mul_neg`).
This is the value side of [72, Kopp (2024), Theorem 8.2, `thm:mainrestate`], whose other side is
`exp(nZ'_{𝔪∞₂}(0,𝒜))`; in particular the quotient is a positive real. -/
theorem sfModularCocycleReal_div_neg_hjCycleMatrix {β : ℝ} (hβ : Irrational β) (hβ1 : 1 < β)
    {N : ℕ} (hN : hjPeriod β N = β) {r : Fin 2 → ℚ} (hr : ¬ IsIntegralIndex r)
    (hA : (hjCycleMatrix β N : SL(2, ℤ)) ∈ gammaSubgroup r)
    (h0 : 0 ≤ (hjCycleMatrix β N) 1 0) :
    sfModularCocycleReal r (hjCycleMatrix β N) hA h0 β /
        sfModularCocycleReal (-r) (hjCycleMatrix β N) (neg_mem_gammaSubgroup hA) h0 β =
      (((starkTangedalYamamoto r β N ^ 2)⁻¹ : ℝ) : ℂ) := by
  let U := starkTangedalYamamoto r β N
  let Uneg := starkTangedalYamamoto (-r) β N
  let phase := Complex.exp (2 * π * I * ((hjGamma β N / 24 + hjLambda r β N / 4 : ℝ) : ℂ))
  have hpos : (U : ℂ) * sfModularCocycleReal r (hjCycleMatrix β N) hA h0 β = phase :=
    starkTangedalYamamoto_mul_sfModularCocycleReal hβ hβ1 hN hr hA h0
  have hneg : (Uneg : ℂ) *
      sfModularCocycleReal (-r) (hjCycleMatrix β N) (neg_mem_gammaSubgroup hA) h0 β = phase := by
    rw [starkTangedalYamamoto_mul_sfModularCocycleReal hβ hβ1 hN
      ((isIntegralIndex_neg_iff r).not.mpr hr) (neg_mem_gammaSubgroup hA) h0,
      hjLambda_neg hr hβ hA]
  have hunitC : (U : ℂ) * (Uneg : ℂ) = 1 := by
    exact_mod_cast starkTangedalYamamoto_mul_neg hβ hβ1 hN hr hA
  have hU : (U : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (starkTangedalYamamoto_pos _ _ _).ne'
  have hUneg : (Uneg : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (starkTangedalYamamoto_pos _ _ _).ne'
  have hvpos : sfModularCocycleReal r (hjCycleMatrix β N) hA h0 β = phase / (U : ℂ) := by
    apply (eq_div_iff hU).2
    simpa [mul_comm] using hpos
  have hvneg : sfModularCocycleReal (-r) (hjCycleMatrix β N) (neg_mem_gammaSubgroup hA) h0 β =
      phase / (Uneg : ℂ) := by
    apply (eq_div_iff hUneg).2
    simpa [mul_comm] using hneg
  have hUneg_eq : (Uneg : ℂ) = (U : ℂ)⁻¹ := eq_inv_of_mul_eq_one_right hunitC
  have hphase : phase ≠ 0 := Complex.exp_ne_zero _
  rw [hvpos, hvneg]
  calc
    (phase / (U : ℂ)) / (phase / (Uneg : ℂ)) = (Uneg : ℂ) / (U : ℂ) := by
      field_simp [hU, hUneg, hphase]
    _ = ((U : ℂ) ^ 2)⁻¹ := by rw [hUneg_eq]; simp [div_eq_mul_inv, pow_two]
    _ = (((U ^ 2)⁻¹ : ℝ) : ℂ) := by rw [Complex.ofReal_inv, Complex.ofReal_pow]

end SIC
