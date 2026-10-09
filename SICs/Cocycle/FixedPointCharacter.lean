/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Cocycle.Modular.Reflection
import SICs.SL2Z.ThetaCharacter
import SICs.SL2Z.RademacherWord

/-!
# Fixed-point values: the reflected product and integral characteristics

Kopp's Theorem 4.36 for the real cocycle: at an irrational fixed point, `ש^r_M(τ)ש^{-r}_M(τ) =
ψ²(M)χ_r(M)`; and the integral-characteristic part of his Theorem 4.38, with its two
Jacobi-square-root branches.

This file proves [72, Kopp (2024), Theorem 4.36, `thm:shincharacter`] for the real
cocycle of `SICs.Cocycle.Modular.Values`: at an irrational fixed point `τ` of `M ∈ Γ_r` with
`j_M(τ) > 0` and `r ∉ ℤ²`,

$$
ש^{\mathbf r}_M(\tau)\,ש^{-\mathbf r}_M(\tau) = \psi^2(M)\,\chi_{\mathbf r}(M),
$$

with the eta and theta multipliers of `SICs.SL2Z.ThetaCharacter`; in particular the reflected
product is a root of unity.

The last section evaluates every integral characteristic at such a fixed point, proving the
positive-real-domain form of [AFK25, Lemma 2.15, `lm:shinatzero`] and the integral part of
[72, Kopp (2024), Theorem 4.38, `thm:trivrmval`]. Its zero characteristic is
`ש^0_M(τ) = e^{πiΨ(M)/12}/√(j_M(τ))`, which [AFK25, Lemma 5.9, `lem:nu01overnu0val`] uses for the
origin overlap. For positive second coordinate, the regularized shift correction instead gives
`e^{πiΨ(M)/12}√(j_M(τ))`. Both branches are nonzero.

## Mathematical argument

Kopp proves the theorem on the upper half plane, from the modular transformation law of the theta
null with characteristics (his Theorem 2.14) and of the eta function, by analytic continuation to
the fixed point. The reflected product has the following closed form: the
fixed-point reflection law `sfModularCocycleReal_mul_neg_of_flt_eq_self` gives, with
`z = ⟨⟨r,τ⟩⟩`, `x = z/j_M(τ)` and `n = n_QP(r,M)`,

```text
ש^r_M(τ)·ש^{-r}_M(τ) = (-1)^n · e(z - (1+n)x - n(n+1)τ/2) · exp(2·X_M(z,τ)),
```

and `wordSfExpArg_eq` evaluates the accumulated exponent as
`2X_M(z,τ) = πi(c z²/j_M(τ) + z(1/j_M(τ) - 1) + (τ - M·τ + W(M))/6)`, where `W(M)` is the word
Rademacher accumulator, equal to `Ψ(M)` at the positive trace of a fixed-point matrix
(`wordRademacher_eq_rademacherInvariant`, `trace_pos_of_flt_eq_self`). At the fixed point
`τ - M·τ = 0`, and `x = ⟨⟨Mr,τ⟩⟩ = (cr₁ + dr₂)τ - (ar₁ + br₂)`
(`fracSymplecticFormRat_ratVecAction_of_flt_eq_self`). So the product is `e(E)` with

```text
E = n/2 + z - (1+n)x - n(n+1)τ/2 + c z x/2 + (x - z)/2 + Ψ(M)/12,
```

and the claim is `E ≡ Ψ(M)/12 + thetaCharacterExponent r M (mod ℤ)`. With the integrality
witnesses `k₁ = (a-1)r₁ + br₂`, `k₂ = cr₁ + (d-1)r₂` of `M ∈ Γ_r` (so `n = -k₂`) and the
quadratic relation `cτ² + (d-a)τ - b = 0` of the fixed point, the terms of `E` involving `τ`
cancel and

```text
E - Ψ(M)/12 = (k₁ + k₂ + k₁k₂ + k₁r₂ - k₂r₁)/2 - k₁k₂ - k₂,
```

a polynomial identity modulo `cτ² + (d-a)τ - b = 0`, `ad - bc = 1` and the two witness equations.
The simplified formula `thetaCharacterExponent_eq_add_intCast` of [72, Kopp (2024), Lemma 2.15,
`lem:charsimp`] identifies the first term with the exponent of `χ_r(M)` modulo `ℤ`, and
`-k₁k₂ - k₂` is an integer.

## References

- [72, Kopp (2024), Theorem 4.36, `thm:shincharacter`; Lemma 2.15, `lem:charsimp`]
- [AFK25, Lemma 2.15, `lm:shinatzero`]
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### Fixed-point bookkeeping

Three facts about a matrix `M = [[a, b], [c, d]] ∈ SL(2, ℤ)` at a fixed point `τ` with
`j_M(τ) = cτ + d > 0`: the quadratic relation `cτ² + (d-a)τ - b = 0`; the index
`n_QP(r, M) = -k₂` for the second integrality witness of `M ∈ Γ_r`; and
`⟨⟨r,τ⟩⟩/j_M(τ) = ⟨⟨Mr,τ⟩⟩ = (cr₁ + dr₂)τ - (ar₁ + br₂)`. That `a > 0` when `c = 0` is
`topLeft_pos_of_lowerLeft_eq_zero`. -/

/-- **The quadratic relation of a fixed point**: `M·τ = τ` with `j_M(τ) ≠ 0` gives
`cτ² + (d - a)τ - b = 0`. -/
theorem quadratic_of_flt_eq_self {M : Mat(2, ℤ)} {τ : ℝ}
    (hden : fltDenominator M τ ≠ 0) (hfix : flt M τ = τ) :
    (M 1 0 : ℝ) * τ ^ 2 + ((M 1 1 : ℝ) - M 0 0) * τ - M 0 1 = 0 := by
  have hj0 : (M 1 0 : ℝ) * τ + (M 1 1 : ℝ) ≠ 0 := by simpa only [fltDenominator] using hden
  have hnum : (M 0 0 : ℝ) * τ + (M 0 1 : ℝ) = τ * ((M 1 0 : ℝ) * τ + (M 1 1 : ℝ)) := by
    unfold flt at hfix
    rw [div_eq_iff hj0] at hfix
    exact hfix
  linear_combination -hnum

/-- On `Γ_r`, `n_QP(r, M) = -(cr₁ + (d-1)r₂)`, the negative of the second integrality witness
(`nQPInt_cast_of_mem`). -/
private lemma nQPInt_cast_eq_neg {r : Fin 2 → ℚ} {M : SL(2, ℤ)}
    (hM : M ∈ gammaSubgroup r) :
    ((nQPInt r (M : Mat(2, ℤ)) : ℤ) : ℝ) =
      -((M 1 0 : ℝ) * r 0 + ((M 1 1 : ℝ) - 1) * r 1) := by
  have h : ((nQPInt r (M : Mat(2, ℤ)) : ℤ) : ℚ) =
      -((M 1 0 : ℚ) * r 0 + ((M 1 1 : ℚ) - 1) * r 1) := by
    rw [nQPInt_cast_of_mem hM]
    unfold nQP
    ring
  exact_mod_cast h

/-- **The rescaled pairing at a fixed point**: `⟨⟨r,τ⟩⟩/j_M(τ) = (cr₁ + dr₂)τ - (ar₁ + br₂)`,
the pairing `⟨⟨Mr,τ⟩⟩` (`fracSymplecticFormRat_ratVecAction_of_flt_eq_self`). -/
theorem fracSymplecticFormRat_div_fltDenominator {M : SL(2, ℤ)} {τ : ℝ}
    (hden : fltDenominator (M : Mat(2, ℤ)) τ ≠ 0)
    (hfix : flt (M : Mat(2, ℤ)) τ = τ) (r : Fin 2 → ℚ) :
    fracSymplecticFormRat r τ / fltDenominator (M : Mat(2, ℤ)) τ =
      ((M 1 0 : ℝ) * r 0 + (M 1 1 : ℝ) * r 1) * τ - ((M 0 0 : ℝ) * r 0 + (M 0 1 : ℝ) * r 1) := by
  rw [← fracSymplecticFormRat_ratVecAction_of_flt_eq_self hden hfix r]
  unfold fracSymplecticFormRat ratVecAction
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply]
  push_cast
  ring

/-! ### The identity

The polynomial bookkeeping is isolated in a lemma on the exponents; the theorem itself only
assembles the closed forms of `SICs.Cocycle.Modular.Reflection` and
`SICs.Cocycle.Word.Reflection`. -/

/-- The real polynomial identity of the module docstring: with `n = -k₂`,
`x = (cr₁ + dr₂)τ - (ar₁ + br₂)` and `z = r₂τ - r₁`,
`E₀ - (k₁ + k₂ + k₁k₂ + k₁r₂ - k₂r₁)/2 = -(k₁k₂ + k₂)` modulo the quadratic relation,
`ad - bc = 1`, and the two witness equations. -/
private lemma fixedPointCharacter_exponent_identity
    (a b c d k₁ k₂ : ℝ) (r₁ r₂ τ x z n : ℝ)
    (hdet : a * d - b * c = 1) (hquad : c * τ ^ 2 + (d - a) * τ - b = 0)
    (hk₁ : (a - 1) * r₁ + b * r₂ = k₁) (hk₂ : c * r₁ + (d - 1) * r₂ = k₂)
    (hn : n = -k₂) (hx : x = (c * r₁ + d * r₂) * τ - (a * r₁ + b * r₂))
    (hz : z = r₂ * τ - r₁) :
    n / 2 + z - x - n * x - n * (n + 1) * τ / 2 + c * z * x / 2 + (x - z) / 2 -
      (k₁ + k₂ + k₁ * k₂ + k₁ * r₂ - k₂ * r₁) / 2 = -(k₁ * k₂ + k₂) := by
  rw [hn, hx, hz]
  linear_combination
    (r₂ * (c * r₁ + d * r₂) / 2) * hquad +
    (-(r₂ * (r₁ - r₂ * τ)) / 2) * hdet +
    ((-k₂ + r₂ + 1) / 2) * hk₁ +
    ((a * r₁ + b * r₂ - c * r₁ * τ - d * r₂ * τ + k₂ * τ - r₂ * τ - τ) / 2) * hk₂

/-- **[72, Kopp (2024), Theorem 4.36, `thm:shincharacter`] for the real cocycle**: at an irrational
fixed point `τ` of `M ∈ Γ_r` with `j_M(τ) > 0` and `r ∉ ℤ²`,
`ש^r_M(τ)·ש^{-r}_M(τ) = ψ²(M)χ_r(M)`. Kopp assumes `τ` in the source domain `D̃_M`;
the real fixed-point reflection law requires irrationality, `j_M(τ) > 0`, and `r ∉ ℤ²`
(the last through `sigmaSLatticeFree_fracSymplecticFormRat`). See the module docstring for the
exponent computation. -/
@[source "72, Theorem 4.36, p. 47, thm:shincharacter (real cocycle)"]
theorem sfModularCocycleReal_mul_neg_eq_character {r : Fin 2 → ℚ} {M : SL(2, ℤ)}
    {τ : ℝ} (hτ : Irrational τ) (hr : ¬ IsIntegralIndex r)
    (hM : M ∈ gammaSubgroup r) (h0 : 0 ≤ M 1 0)
    (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) τ)
    (hfix : flt (M : Mat(2, ℤ)) τ = τ) :
    sfModularCocycleReal r M hM h0 τ *
        sfModularCocycleReal (-r) M (neg_mem_gammaSubgroup hM) h0 τ =
      etaMultiplierSq M * thetaCharacter r (M : Mat(2, ℤ)) := by
  -- The integrality witnesses of `M ∈ Γ_r` and the fixed-point facts.
  obtain ⟨k₁, hk₁⟩ := hM 0
  obtain ⟨k₂, hk₂⟩ := hM 1
  rw [Fin.sum_univ_two] at hk₁ hk₂
  norm_num at hk₁ hk₂
  have hquad := quadratic_of_flt_eq_self hjac.ne' hfix
  have htr := trace_pos_of_flt_eq_self hfix hjac
  have hW := wordRademacher_eq_rademacherInvariant M h0
    (topLeft_pos_of_lowerLeft_eq_zero hjac) htr
  set z : ℝ := fracSymplecticFormRat r τ with hz
  set J : ℝ := fltDenominator (M : Mat(2, ℤ)) τ with hJ
  set x : ℝ := z / J with hx
  have hxval := fracSymplecticFormRat_div_fltDenominator hjac.ne' hfix r
  rw [← hz, ← hJ, ← hx] at hxval
  have hE := fixedPointCharacter_exponent_identity
    (M 0 0 : ℝ) (M 0 1 : ℝ) (M 1 0 : ℝ) (M 1 1 : ℝ)
    k₁ k₂ (r 0) (r 1) τ x z (nQPInt r (M : Mat(2, ℤ)))
    (det_fin_two_cast_eq_one M) hquad (by exact_mod_cast hk₁) (by exact_mod_cast hk₂)
    (by rw [nQPInt_cast_eq_neg hM]; exact_mod_cast congrArg (fun q : ℚ => -q) hk₂) hxval hz
  -- The two closed forms, with `x = z/J` and `W(M) = Ψ(M)` substituted.
  have hrefl := sfModularCocycleReal_mul_neg_of_flt_eq_self hτ hM h0 hjac hfix
    (sigmaSLatticeFree_fracSymplecticFormRat hτ hr)
  rw [← hz, ← hJ, ← hx] at hrefl
  have hxC : (z : ℂ) / (J : ℂ) = (x : ℂ) := by exact_mod_cast hx.symm
  have hword := wordSfExpArg_eq hτ z M h0 hjac
  rw [← hJ, hfix, show (((wordRademacher M h0 : ℤ) : ℂ)) = ((rademacherInvariant M : ℚ) : ℂ) by
    exact_mod_cast hW, show Real.pi * Complex.I * (M 1 0 : ℂ) * (z : ℂ) ^ 2 / (J : ℂ) =
      Real.pi * Complex.I * (M 1 0 : ℂ) * (z : ℂ) * (x : ℂ) by rw [← hxC]; ring,
    show Real.pi * Complex.I * (z : ℂ) * (1 / (J : ℂ) - 1) =
      Real.pi * Complex.I * ((x : ℂ) - (z : ℂ)) by rw [← hxC]; ring] at hword
  have hneg : (-1 : ℂ) ^ nQPInt r (M : Mat(2, ℤ)) =
      Complex.exp (Real.pi * Complex.I * (nQPInt r (M : Mat(2, ℤ)) : ℂ)) := by
    rw [mul_comm, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  -- Compare the exponents modulo `2πiℤ`.
  rw [hrefl, hneg, hword, thetaCharacter_eq_exp M hk₁ hk₂]
  rw [etaMultiplierSq_eq_of_trace_pos htr]
  simp only [← Complex.exp_add]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨-(k₁ * k₂ + k₂), ?_⟩
  have hEC := congrArg (fun y : ℝ ↦ (y : ℂ)) hE
  push_cast at hEC ⊢
  linear_combination (2 * Real.pi * Complex.I) * hEC

/-- `sfModularCocycleReal_mul_neg_eq_character` for the total cocycle
`sfModularCocycleRealTotal`, through `sfModularCocycleRealTotal_of_nonneg`. -/
theorem sfModularCocycleRealTotal_mul_neg_eq_character {r : Fin 2 → ℚ}
    {M : SL(2, ℤ)} {τ : ℝ} (hτ : Irrational τ) (hr : ¬ IsIntegralIndex r)
    (hM : M ∈ gammaSubgroup r) (h0 : 0 ≤ M 1 0)
    (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) τ)
    (hfix : flt (M : Mat(2, ℤ)) τ = τ) :
    sfModularCocycleRealTotal r M hM τ *
        sfModularCocycleRealTotal (-r) M (neg_mem_gammaSubgroup hM) τ =
      etaMultiplierSq M * thetaCharacter r (M : Mat(2, ℤ)) := by
  rw [sfModularCocycleRealTotal_of_nonneg hM h0, sfModularCocycleRealTotal_of_nonneg _ h0]
  exact sfModularCocycleReal_mul_neg_eq_character hτ hr hM h0 hjac hfix

/-! ### The value at the zero characteristic

At `r = 0` the pairing `⟨⟨0,τ⟩⟩` and the index `n_QP(0,M)` both vanish, so `ש^0_M(τ)` is the bare
word value `σ_M(0,τ)` of [AFK25, equation (8.5), `eq:sfjldecom`]. Each letter contributes
`σ_S(0,ν) = e^{X(0,ν)}/S₂(1;ν,1)` by [AFK25, equation (8.6), `eq:SFJacobiCocycleTermsDoubleSine`],
and `S₂(1;ν,1) = √ν` (`doubleSine_one`); the moduli `ν = N·τ` the word visits multiply to `j_M(τ)`
(`fltDenominator_hjStep`). Hence

$$
\sigma_M(0,\tau) = \frac{e^{X_M(0,\tau)}}{\sqrt{j_M(\tau)}},
$$

and at a fixed point the closed form `wordSfExpArg_eq` gives `2X_M(0,τ) = πiW(M)/6`, with
`W(M) = Ψ(M)` at positive trace (`wordRademacher_eq_rademacherInvariant`). So

$$
ש^{\mathbf 0}_M(\tau) = \frac{e^{\pi i\Psi(M)/12}}{\sqrt{j_M(\tau)}},
$$

which is the case `r = 0` of [72, Kopp (2024), Theorem 4.38, `thm:trivrmval`], quoted as
[AFK25, Lemma 2.15, `lm:shinatzero`], once `ψ(M,√j_M) = e^{πiΨ(M)/12}` [AFK25, Proposition 5.2,
`prop:rademacher`] is substituted. Kopp derives it on `ℍ` from the transformation law of the
Dedekind eta function at the characteristic `(0,1)` and the exceptional periodicity of his
Proposition 4.35, neither of which reaches the real word value at `r = 0`; the computation here is
the `r = 0` case of the telescoping along the word that gives his Proposition 7.20
(`SICs.Cocycle.HJCycleProduct`). For `M₁₀ < 0` the total cocycle is the inverse of the value at
`M⁻¹`, and `Ψ(M⁻¹) = -Ψ(M)` (`rademacherInvariant_inv`) with `j_{M⁻¹}(τ) = j_M(τ)⁻¹` gives the
same formula. For a general integral characteristic, the regularized shifts of Kopp's
Proposition 4.35 multiply the zero value by `j_M(τ)` exactly when the second coordinate is
positive (`sfModularCocycleReal_integral_of_flt_eq_self`). This correction also
passes through inverse orientation. Since the positive square root squares to `j_M(τ)`,
it turns the quotient branch into the product branch of Kopp's Theorem 4.38. -/

/-- The terminal case used by `wordSigmaS_zero_eq`: positivity of the denominator selects the
positive diagonal sign, so both the empty word and its denominator evaluate to one. -/
private lemma wordSigmaS_zero_base {τ : ℝ} (M : SL(2, ℤ)) (h0 : 0 ≤ M 1 0)
    (hz : M 1 0 = 0)
    (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) τ) :
    wordSigmaS 0 τ M h0 =
      Complex.exp (wordSfExpArg 0 τ M h0) /
        ((Real.sqrt (fltDenominator (M : Mat(2, ℤ)) τ) : ℝ) : ℂ) := by
  rw [wordSigmaS_of_lowerLeft_eq_zero _ _ _ _ hz,
    wordSfExpArg_of_lowerLeft_eq_zero _ _ _ _ hz,
    fltDenominator_eq_one_of_lowerLeft_eq_zero hz hjac]
  norm_num

/-- **The word value at `z = 0`**: `σ_M(0,τ) = e^{X_M(0,τ)}/√(j_M(τ))` for an irrational `τ` with
`j_M(τ) > 0`, where `X_M` is the word-accumulated exponent `wordSfExpArg`. By induction along the
word: each letter contributes `σ_S(0,ν) = e^{X(0,ν)}/S₂(1;ν,1)` with `S₂(1;ν,1) = √ν`
(`sigmaSHonest_zero`, `sigmaSBase_eq_exp_div`, `doubleSine_one`), and `j_M(τ) = ν·j_N(τ)`
(`fltDenominator_hjStep`). -/
theorem wordSigmaS_zero_eq {τ : ℝ} (hτ : Irrational τ) (M : SL(2, ℤ)) (h0 : 0 ≤ M 1 0)
    (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) τ) :
    wordSigmaS 0 τ M h0 =
      Complex.exp (wordSfExpArg 0 τ M h0) /
        ((Real.sqrt (fltDenominator (M : Mat(2, ℤ)) τ) : ℝ) : ℂ) := by
  induction M, h0 using wordSigmaS.induct with
  | case1 M h0 hz _ => exact wordSigmaS_zero_base M h0 hz hjac
  | case2 M h0 hz hpos h0N _ _ ih =>
      obtain ⟨hνpos, hJpos⟩ := flt_and_fltDenominator_pos_of_hjStep M τ hτ hpos hjac
      have hds : doubleSine' (0 + 1)
          (flt ((hjStep M).2 : Mat(2, ℤ)) τ) =
          Real.sqrt (flt ((hjStep M).2 : Mat(2, ℤ)) τ) := by
        change doubleSine (0 + 1) _ 1 = _
        norm_num
        exact doubleSine_one _ hνpos
      rw [wordSigmaS_step 0 τ h0 hz rfl h0N,
        wordSfExpArg_step 0 τ h0 hz rfl h0N, zero_div,
        sigmaSHonest_zero, sigmaSBase_eq_exp_div, hds,
        ih hJpos, fltDenominator_hjStep M τ hτ, Real.sqrt_mul hνpos.le, Complex.exp_add]
      push_cast
      ring

/-- **The cocycle at the zero characteristic, on the word walk**: at an irrational fixed point
`τ` of `M` with `M₁₀ ≥ 0` and `j_M(τ) > 0`, `ש^0_M(τ) = e^{πiΨ(M)/12}/√(j_M(τ))`. The `r = 0` case
of [72, Kopp (2024), Theorem 4.38, `thm:trivrmval`] for the real cocycle. -/
theorem sfModularCocycleReal_zero_of_flt_eq_self {M : SL(2, ℤ)} {τ : ℝ} (hτ : Irrational τ)
    (hM : M ∈ gammaSubgroup 0) (h0 : 0 ≤ M 1 0)
    (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) τ)
    (hfix : flt (M : Mat(2, ℤ)) τ = τ) :
    sfModularCocycleReal 0 M hM h0 τ =
      Complex.exp (Real.pi * Complex.I / 12 * ((rademacherInvariant M : ℚ) : ℂ)) /
        ((Real.sqrt (fltDenominator (M : Mat(2, ℤ)) τ) : ℝ) : ℂ) := by
  have htr := trace_pos_of_flt_eq_self hfix hjac
  have hW := wordRademacher_eq_rademacherInvariant M h0
    (topLeft_pos_of_lowerLeft_eq_zero hjac) htr
  have hword := wordSfExpArg_eq hτ 0 M h0 hjac
  rw [hfix, show (((wordRademacher M h0 : ℤ) : ℂ)) =
      ((rademacherInvariant M : ℚ) : ℂ) by exact_mod_cast hW] at hword
  norm_num at hword
  have hX : wordSfExpArg 0 τ M h0 =
      Real.pi * Complex.I / 12 * ((rademacherInvariant M : ℚ) : ℂ) := by
    linear_combination (1 / 2) * hword
  rw [sfModularCocycleReal_zero, wordSigmaS_zero_eq hτ M h0 hjac, hX]

/-- The exponential character in the zero-value formula inverts with the matrix; used by
`sfModularCocycleRealTotal_zero_of_flt_eq_self`. -/
private lemma zero_character_phase_inv (M : SL(2, ℤ)) :
    Complex.exp (Real.pi * Complex.I / 12 * ((rademacherInvariant M⁻¹ : ℚ) : ℂ)) =
      (Complex.exp (Real.pi * Complex.I / 12 * ((rademacherInvariant M : ℚ) : ℂ)))⁻¹ := by
  rw [rademacherInvariant_inv, ← Complex.exp_neg]
  congr 1
  push_cast
  ring

/-- **[72, Kopp (2024), Theorem 4.38, `thm:trivrmval`] at `r = 0`** for the total cocycle, quoted as
[AFK25, Lemma 2.15, `lm:shinatzero`]: at an irrational fixed point `τ` of `M ∈ SL₂(ℤ)` with
`j_M(τ) > 0`, `ש^0_M(τ) = e^{πiΨ(M)/12}/√(j_M(τ))`, Kopp's `ψ(M,√j_M)/√(j_M(τ))`. For `M₁₀ ≥ 0`
this is `sfModularCocycleReal_zero_of_flt_eq_self`; for `M₁₀ < 0` it is that statement at `M⁻¹`,
inverted, with `Ψ(M⁻¹) = -Ψ(M)` (`rademacherInvariant_inv`) and `j_{M⁻¹}(τ)j_M(τ) = 1`
(`fltDenominator_inv_mul_self_of_flt_eq_self`). -/
theorem sfModularCocycleRealTotal_zero_of_flt_eq_self {M : SL(2, ℤ)} {τ : ℝ} (hτ : Irrational τ)
    (hM : M ∈ gammaSubgroup 0)
    (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) τ)
    (hfix : flt (M : Mat(2, ℤ)) τ = τ) :
    sfModularCocycleRealTotal 0 M hM τ =
      Complex.exp (Real.pi * Complex.I / 12 * ((rademacherInvariant M : ℚ) : ℂ)) /
        ((Real.sqrt (fltDenominator (M : Mat(2, ℤ)) τ) : ℝ) : ℂ) := by
  by_cases h0 : 0 ≤ M 1 0
  · rw [sfModularCocycleRealTotal_of_nonneg hM h0]
    exact sfModularCocycleReal_zero_of_flt_eq_self hτ hM h0 hjac hfix
  · have h0inv : 0 ≤ (M⁻¹) 1 0 := by rw [SL2Z.lowerLeft_inv]; omega
    have hfixinv := flt_inv_of_flt_eq_self hjac.ne' hfix
    have hprod := fltDenominator_inv_mul_self_of_flt_eq_self hjac.ne' hfix
    have hJinv : fltDenominator ((M⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) τ =
        (fltDenominator (M : Mat(2, ℤ)) τ)⁻¹ :=
      (mul_eq_one_iff_eq_inv₀ hjac.ne').mp hprod
    have hJinvpos :
        0 < fltDenominator ((M⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) τ := by
      rw [hJinv]
      exact inv_pos.mpr hjac
    have hinv := sfModularCocycleReal_zero_of_flt_eq_self hτ
      (inv_mem_gammaSubgroup hM) h0inv hJinvpos hfixinv
    unfold sfModularCocycleRealTotal
    rw [dite_eq_right h0, hfix, hinv, inv_div, zero_character_phase_inv, hJinv,
      Real.sqrt_inv]
    push_cast
    rw [div_inv_eq_mul]
    ring

/-! ### Integral characteristics

Kopp's Proposition 4.35 relates each integral characteristic to zero: at a fixed point the
finite shift factors cancel, leaving $j_M(τ)$ exactly when the second coordinate is positive.
The same relation survives inverse orientation since $j_{M^{-1}}(τ)=j_M(τ)^{-1}$. Applying it
to the proved zero value yields the two square-root branches of Theorem 4.38 and their
nonvanishing. -/

/-- The integral shift correction passes through inverse orientation; used by
`sfModularCocycleRealTotal_integral_of_flt_eq_self`. -/
private lemma sfModularCocycleRealTotal_integral_correction
    {r : Fin 2 → ℚ} {M : SL(2, ℤ)} {τ : ℝ} (hr : IsIntegralIndex r)
    (hM : M ∈ gammaSubgroup r)
    (hM0 : M ∈ gammaSubgroup 0)
    (hden : fltDenominator (M : Mat(2, ℤ)) τ ≠ 0)
    (hfix : flt (M : Mat(2, ℤ)) τ = τ) :
    sfModularCocycleRealTotal r M hM τ = sfModularCocycleRealTotal 0 M hM0 τ *
      (if 0 < r 1 then (fltDenominator (M : Mat(2, ℤ)) τ : ℂ) else 1) := by
  by_cases h0 : 0 ≤ M 1 0
  · rw [sfModularCocycleRealTotal_of_nonneg hM h0,
      sfModularCocycleRealTotal_of_nonneg hM0 h0,
      sfModularCocycleReal_integral_of_flt_eq_self hr hM h0 hfix,
      sfModularCocycleReal_zero]
  · have h0inv : 0 ≤ (M⁻¹) 1 0 := by rw [SL2Z.lowerLeft_inv]; omega
    have hfixinv := flt_inv_of_flt_eq_self hden hfix
    have hJinv := eq_inv_of_mul_eq_one_left
      (fltDenominator_inv_mul_self_of_flt_eq_self hden hfix)
    rw [sfModularCocycleRealTotal, dite_eq_right h0, hfix,
      sfModularCocycleReal_integral_of_flt_eq_self hr
        (inv_mem_gammaSubgroup hM) h0inv hfixinv,
      sfModularCocycleRealTotal, dite_eq_right h0, hfix, sfModularCocycleReal_zero]
    simp only [← ofReal_fltDenominator, hJinv, Complex.ofReal_inv]
    split_ifs <;> simp [mul_comm]

/-- **The integral-characteristic fixed-point formula**, [AFK25, Lemma 2.15, `lm:shinatzero`]
and the integral case of [72, Kopp (2024), Theorem 4.38, `thm:trivrmval`], on the positive real
source domain: for $r\in\mathbb Z^2$ and an irrational fixed point $\tau$ with $j_M(\tau)>0$,
$ש^r_M(\tau)=\psi(M,\sqrt{j_M})\sqrt{j_M(\tau)}$ if $r_1>0$ (the paper's $r_2>0$), and
$ש^r_M(\tau)=\psi(M,\sqrt{j_M})/\sqrt{j_M(\tau)}$ otherwise. Here
$\psi(M,\sqrt{j_M})=e^{\pi i\Psi(M)/12}$. The half-integral conclusions of Kopp's theorem
are not asserted here. -/
@[source "AFK25, Lemma 2.15, p. 32, lm:shinatzero (real-positive-domain)"
  "72, Theorem 4.38, p. 48, thm:trivrmval (integral-real-positive-domain)"]
theorem sfModularCocycleRealTotal_integral_of_flt_eq_self
    {r : Fin 2 → ℚ} {M : SL(2, ℤ)} {τ : ℝ} (hτ : Irrational τ) (hr : IsIntegralIndex r)
    (hM : M ∈ gammaSubgroup r)
    (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) τ)
    (hfix : flt (M : Mat(2, ℤ)) τ = τ) :
    sfModularCocycleRealTotal r M hM τ =
      if 0 < r 1 then
        Complex.exp (Real.pi * Complex.I / 12 * ((rademacherInvariant M : ℚ) : ℂ)) *
          ((Real.sqrt (fltDenominator (M : Mat(2, ℤ)) τ) : ℝ) : ℂ)
      else
        Complex.exp (Real.pi * Complex.I / 12 * ((rademacherInvariant M : ℚ) : ℂ)) /
          ((Real.sqrt (fltDenominator (M : Mat(2, ℤ)) τ) : ℝ) : ℂ) := by
  have hM0 : M ∈ gammaSubgroup 0 :=
    fun _ => ⟨0, by simp⟩
  rw [sfModularCocycleRealTotal_integral_correction hr hM hM0 hjac.ne' hfix,
    sfModularCocycleRealTotal_zero_of_flt_eq_self hτ hM0 hjac hfix]
  split_ifs
  · have hs : ((Real.sqrt (fltDenominator (M : Mat(2, ℤ)) τ) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr hjac).ne'
    have hsq : ((Real.sqrt (fltDenominator (M : Mat(2, ℤ)) τ) : ℝ) : ℂ) ^ 2 =
        (fltDenominator (M : Mat(2, ℤ)) τ : ℂ) := by
      exact_mod_cast Real.sq_sqrt hjac.le
    rw [← hsq, sq, ← mul_assoc, div_mul_cancel₀ _ hs]
  · exact mul_one _

/-- The integral values in `sfModularCocycleRealTotal_integral_of_flt_eq_self` never vanish:
both the character and the positive Jacobi square root are nonzero. -/
theorem sfModularCocycleRealTotal_integral_ne_zero
    {r : Fin 2 → ℚ} {M : SL(2, ℤ)} {τ : ℝ} (hτ : Irrational τ) (hr : IsIntegralIndex r)
    (hM : M ∈ gammaSubgroup r)
    (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) τ)
    (hfix : flt (M : Mat(2, ℤ)) τ = τ) :
    sfModularCocycleRealTotal r M hM τ ≠ 0 := by
  rw [sfModularCocycleRealTotal_integral_of_flt_eq_self hτ hr hM hjac hfix]
  have hs : ((Real.sqrt (fltDenominator (M : Mat(2, ℤ)) τ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hjac).ne'
  split_ifs
  · exact mul_ne_zero (Complex.exp_ne_zero _) hs
  · exact div_ne_zero (Complex.exp_ne_zero _) hs

end SIC

end
