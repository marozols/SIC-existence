/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.FieldTheory.ComplexGalois
import SICs.SL2Z.Characteristics
import SICs.SL2Z.Rademacher

/-!
# The eta and theta multipliers as roots of unity

The eta multiplier square `ψ²(M)` and Kopp's theta multiplier expression `χ_r(M)` as roots of
unity, with his simplified formula `χ_r(M) = e((k₁ + k₂ + k₁k₂ + k₁r₂ - k₂r₁)/2)` for `(M - I)r =
(k₁,k₂)`.

This file defines the two multiplier expressions through which the phase of a real multiplication
value of the Shintani--Faddeev cocycle is expressed in [72, Kopp (2024)]. The eta multiplier square
is `ψ²(M) = e(E(M))`, where, for `M = [[a,b],[c,d]]` and the AFK25 Rademacher symbol `Ψ`,

$$
E(M) = \begin{cases}
\Psi(M)/12 + (\operatorname{sgn}(d)-1)/4,&c=0,\\
(\Psi(M)+3\operatorname{sgn}(c(a+d))-3\operatorname{sgn}(c))/12,&c\ne0.
\end{cases}
$$

These are the logarithmic corrections in [72, Kopp (2024), Section 2.5, `sec:eta`,
equations (2.5), (2.6), and (2.7), `eq:Phi`, `eq:Psi`, `eq:etatrans`]. The AFK25 symbol differs from
Kopp's metaplectic invariant away from positive trace: `E(M) = Ψ(M)/12` when `Tr M > 0`. This
positive-trace bridge is what the real fixed-point and cycle calculations use.

The theta multiplier expression on `Γ_r` is that of [72, Kopp (2024), Theorem 2.14,
`thm:thetamod`],

$$
\chi_{\mathbf r}(M)
  = e\!\left(\tfrac12\bigl((c-d+1)r_1 + (-a+b+1)r_2 - cd\,r_1^2 + 2(a-1)d\,r_1r_2
      - (a-2)b\,r_2^2\bigr)\right),
\qquad M = \begin{pmatrix} a & b \\ c & d\end{pmatrix}.
$$

The modular transformation laws and the multiplicativity of the characters in `M` are not proved
here; the last section proves their behaviour in the characteristic `r` instead.
Both expressions are exponentials of rational multiples of `2πi`, so both are roots of unity,
which every `ℚ`-automorphism of `ℂ` sends to modulus one.

The section on the simplified formula proves [72, Kopp (2024), Lemma 2.15, `lem:charsimp`] in
exponent form: for `M ∈ Γ_r` with `(M - I)r = (k₁, k₂) ∈ ℤ²`, the exponent of `χ_r(M)` is congruent
modulo `ℤ` to `(k₁ + k₂ + k₁k₂ + k₁r₂ - k₂r₁)/2`; this is the form in which the fixed-point
reflection law of `SICs.Cocycle.FixedPointCharacter` recovers the character. Kopp derives it from
the character property of `χ_r`, which comes from the modular transformation law of the theta
null; here it is a direct computation with the two integrality witnesses.

The last section reads the simplified formula as a statement about the characteristic: `χ_r(M)`
is `1` for integral `r`, is `ℤ²`-periodic in `r` on `Γ_r`, and obeys the Gaussian law
`χ_{r+s}(M) = χ_r(M) χ_s(M) ⟨r; s⟩_M` with the bicharacter `⟨r; s⟩_M = e(k₁s₂ - k₂s₁)`,
`(k₁, k₂) = (M - I)r`. In this form `χ_r(M)` is the Gaussian `⟨u⟩_γ` of Radchenko and Wheeler
[RW26, Radchenko, Wheeler (2026), equation (3), `eq:gaussianpairing`], which
`SICs.Principal.Dilogarithm.Group` uses on
the finite group `G_d` of the principal cocycle; the eta multiplier `ψ(M, √j_M) = e^{πiΨ(M)/12}`,
their `μ_γ`, is defined here beside its square.

## References

- [72, Kopp (2024), Section 2.5, `sec:eta`, equation (2.7), `eq:etatrans`; Theorem 2.14,
  `thm:thetamod`; Lemma 2.15, `lem:charsimp`]
- [RW26, Radchenko, Wheeler (2026), Section 1, equation (2), `eq:fgam.def`, and Section 3.2,
  Lemma 2, `lem:lam.inv`]
-/

noncomputable section

open scoped MatrixGroups

open Complex Real

namespace SIC

/-! ### The square of the eta multiplier

Kopp's equation `eq:Psi` compares the logarithmic eta transformation with the Rademacher
function `Φ`. For `c ≠ 0`, the square multiplier is `e((Φ(M)-3 sgn(c))/12)`; replacing `Φ` by
`Ψ + 3 sgn(c Tr M)` gives the formula below. For `c = 0`, the logarithm of `d = ±1` contributes
`(sgn(d)-1)/4` to the exponent. These corrections vanish at positive trace, where the real
fixed-point calculations use the AFK25 symbol.
-/

/-- The rational exponent `E(M)` of the eta multiplier square: `ψ²(M) = e(E(M))`, from
[72, Kopp (2024), equations (2.5), (2.6), and (2.7), `eq:Phi`, `eq:Psi`, `eq:etatrans`]. The branch
`c = 0` is `Ψ(M)/12 + (sgn(d)-1)/4`; otherwise it is
`(Ψ(M) + 3 sgn(c Tr M) - 3 sgn(c))/12`. -/
def etaMultiplierExponent (M : SL(2, ℤ)) : ℚ :=
  if M 1 0 = 0 then
    rademacherInvariant M / 12 + ((Int.sign (M 1 1) : ℚ) - 1) / 4
  else
    (rademacherInvariant M + 3 * (Int.sign (M 1 0 * (M 0 0 + M 1 1)) : ℚ) -
      3 * (Int.sign (M 1 0) : ℚ)) / 12

/-- At positive trace, `E(M) = Ψ(M)/12`: the sign corrections in
`etaMultiplierExponent` vanish. This bridges Kopp's eta exponent to the AFK25 symbol. -/
theorem etaMultiplierExponent_eq_of_trace_pos {M : SL(2, ℤ)}
    (htr : 0 < M 0 0 + M 1 1) :
    etaMultiplierExponent M = rademacherInvariant M / 12 := by
  unfold etaMultiplierExponent
  split_ifs with hc
  · have hdet := M.2
    rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
    have hd : M 1 1 = 1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with h | h <;> omega
    simp [hd]
  · rw [Int.sign_mul, Int.sign_eq_one_of_pos htr, mul_one]
    ring

/-- The square of the eta multiplier, `ψ²(M) = e(E(M))`, with `E` as in
`etaMultiplierExponent` [72, Kopp (2024), Section 2.5, `sec:eta`, after equation (2.7),
`eq:etatrans`]. -/
@[source "72, Section 2.5, p. 14, sec:eta" (symbol := "ψ²(M)")]
def etaMultiplierSq (M : SL(2, ℤ)) : ℂ :=
  Complex.exp (2 * π * I * (etaMultiplierExponent M : ℂ))

/-- At positive trace, the eta multiplier square is `ψ²(M) = e(Ψ(M)/12)`, by
`etaMultiplierExponent_eq_of_trace_pos`. -/
theorem etaMultiplierSq_eq_of_trace_pos {M : SL(2, ℤ)} (htr : 0 < M 0 0 + M 1 1) :
    etaMultiplierSq M = Complex.exp (2 * π * I * ((rademacherInvariant M / 12 : ℚ) : ℂ)) := by
  rw [etaMultiplierSq, etaMultiplierExponent_eq_of_trace_pos htr]

/-- `|g(ψ²(M))| = 1` for every ambient automorphism `g` (`norm_map_exp_two_pi_I_ratCast`). -/
theorem norm_map_etaMultiplierSq (g : ComplexGaloisAutomorphism) (M : SL(2, ℤ)) :
    ‖g (etaMultiplierSq M)‖ = 1 :=
  norm_map_exp_two_pi_I_ratCast g _

/-- The root-of-unity relation `ψ²(M) ^ den(E(M)) = 1`. -/
theorem etaMultiplierSq_pow_den (M : SL(2, ℤ)) :
    etaMultiplierSq M ^ (etaMultiplierExponent M).den = 1 :=
  exp_two_pi_I_ratCast_pow_den _

/-- `ψ²(M) ≠ 0`. -/
theorem etaMultiplierSq_ne_zero (M : SL(2, ℤ)) : etaMultiplierSq M ≠ 0 :=
  Complex.exp_ne_zero _

/-! ### The eta multiplier

The square root `e^{πiΨ(M)/12}` of `ψ²(M)` that the fixed-point values of the real cocycle
carry (`sfModularCocycleReal_zero_of_flt_eq_self`,
`sfModularCocycleRealTotal_integral_of_flt_eq_self`). It squares to `ψ²(M)` at positive
trace, where `E(M) = Ψ(M)/12`. -/

/-- **The eta multiplier** `ψ(M, √j_M) = e^{πiΨ(M)/12}`: Kopp's `ψ(A, ε)` of [72, Kopp (2024),
Section 2.5, `sec:eta`, equation (2.7), `eq:etatrans`] for the principal square root
`ε(τ) = √(cτ + d)`, at positive trace, where the metaplectic `Ψ(A, λ)` is the Rademacher
invariant `Ψ(A)`; it is the multiplier system `μ_γ = η(γz)/(η(z)√(cz + d))` of the Dedekind eta
function in [RW26, Radchenko, Wheeler (2026), the sentence after equation (2),
`eq:fgam.def`]. -/
def etaMultiplier (M : SL(2, ℤ)) : ℂ :=
  Complex.exp (π * I / 12 * ((rademacherInvariant M : ℚ) : ℂ))

/-- At positive trace the eta multiplier squares to `ψ²(M)` (`etaMultiplierSq_eq_of_trace_pos`). -/
theorem etaMultiplier_sq_of_trace_pos {M : SL(2, ℤ)} (htr : 0 < M 0 0 + M 1 1) :
    etaMultiplier M ^ 2 = etaMultiplierSq M := by
  rw [etaMultiplierSq_eq_of_trace_pos htr]
  unfold etaMultiplier
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `ψ(M, √j_M) ≠ 0`. -/
theorem etaMultiplier_ne_zero (M : SL(2, ℤ)) : etaMultiplier M ≠ 0 :=
  Complex.exp_ne_zero _

/-- **The eta multiplier has modulus one**: `conj ψ(M, √j_M) = ψ(M, √j_M)⁻¹`, since its exponent
`πiΨ(M)/12` is purely imaginary (`Complex.exp_conj`, `Complex.exp_neg`). -/
theorem starRingEnd_etaMultiplier (M : SL(2, ℤ)) :
    starRingEnd ℂ (etaMultiplier M) = (etaMultiplier M)⁻¹ := by
  rw [etaMultiplier, ← Complex.exp_conj, ← Complex.exp_neg]
  simp only [map_mul, map_div₀, map_ofNat, conj_ofReal, conj_I, map_ratCast]
  ring_nf

/-! ### The theta multiplier character

The exponent of `χ_r(M)` is the rational number of [72, Kopp (2024), Theorem 2.14,
`thm:thetamod`]; the character is its exponential. Kopp states the formula for `M ∈ Γ_r`, where
`χ_r` is a character; the expression itself makes sense for every integer matrix and every
`r ∈ ℚ²`, and nothing below assumes `M ∈ Γ_r` except the simplified formula. -/

/-- **The exponent of the theta multiplier character**,
`((c-d+1)r₁ + (-a+b+1)r₂ - cd r₁² + 2(a-1)d r₁r₂ - (a-2)b r₂²)/2` for
`M = [[a, b], [c, d]]`, so that `χ_r(M) = e(thetaCharacterExponent r M)`
[72, Kopp (2024), Theorem 2.14, `thm:thetamod`]. -/
def thetaCharacterExponent (r : Fin 2 → ℚ) (M : Mat(2, ℤ)) : ℚ :=
  (((M 1 0 : ℚ) - M 1 1 + 1) * r 0 + (-(M 0 0 : ℚ) + M 0 1 + 1) * r 1
      - (M 1 0 : ℚ) * M 1 1 * r 0 ^ 2 + 2 * ((M 0 0 : ℚ) - 1) * M 1 1 * r 0 * r 1
      - ((M 0 0 : ℚ) - 2) * M 0 1 * r 1 ^ 2) / 2

/-- **The theta multiplier character** `χ_r(M) = e(thetaCharacterExponent r M)`
[72, Kopp (2024), Theorem 2.14, `thm:thetamod`]. -/
@[source "72, Theorem 2.14, p. 17, thm:thetamod (character formula)" (symbol := "χ_r(M)")]
def thetaCharacter (r : Fin 2 → ℚ) (M : Mat(2, ℤ)) : ℂ :=
  Complex.exp (2 * π * I * (thetaCharacterExponent r M : ℂ))

/-- `|g(χ_r(M))| = 1` for every ambient automorphism `g` (`norm_map_exp_two_pi_I_ratCast`). -/
theorem norm_map_thetaCharacter (g : ComplexGaloisAutomorphism) (r : Fin 2 → ℚ)
    (M : Mat(2, ℤ)) : ‖g (thetaCharacter r M)‖ = 1 :=
  norm_map_exp_two_pi_I_ratCast g _

/-- `χ_r(M) ≠ 0`. -/
theorem thetaCharacter_ne_zero (r : Fin 2 → ℚ) (M : Mat(2, ℤ)) :
    thetaCharacter r M ≠ 0 :=
  Complex.exp_ne_zero _

/-! ### The simplified formula on `Γ_r`

[72, Kopp (2024), Lemma 2.15, `lem:charsimp`] rewrites `χ_r(M)`, for `M ∈ Γ_r`, as
`-(-1)^{δ₂(Mr - r)} e(⟨Mr, r⟩/2)`, where `⟨·,·⟩` is the symplectic pairing and `δ₂(q) = 1`
exactly when `q ∈ 2ℤ²`. With `Mr - r = (k₁, k₂)`, the sign is `e((k₁ + k₂ + k₁k₂)/2)` and the
pairing is `⟨Mr, r⟩ = ⟨(k₁,k₂), r⟩ = k₁r₂ - k₂r₁`, so the lemma says that the exponent of
`χ_r(M)` is congruent to `(k₁ + k₂ + k₁k₂ + k₁r₂ - k₂r₁)/2` modulo `ℤ`.

Kopp's proof uses that `χ_r` is a character; the direct computation below gives the integer
explicitly. Writing `M = [[a, b], [c, d]]`, the polynomial identity

`thetaCharacterExponent r M - (k₁ + k₂ + k₁k₂ + k₁r₂ - k₂r₁)/2
  = -(cd k₁² - 2bc k₁k₂ + ab k₂² - (d - 1 - c) k₁ - (a - 1 - b) k₂)/2`

holds modulo `ad - bc = 1`, `(a-1)r₁ + br₂ = k₁`, `cr₁ + (d-1)r₂ = k₂`, and the right-hand
side is an integer: modulo `2`, `cd k₁² - (d-1-c)k₁ ≡ (c+1)(d-1)k₁` and
`ab k₂² - (a-1-b)k₂ ≡ (a-1)(b+1)k₂`, and `ad - bc = 1` forces `b`, `c` odd whenever `a` or
`d` is even. -/

/-- The numerator of the integer correction in `thetaCharacterExponent_eq_add_intCast` is even
when `ad - bc = 1`. -/
private theorem thetaCharacterNumerator_even (a b c d k₁ k₂ : ℤ)
    (hdet : a * d - b * c = 1) :
    Even (c * d * k₁ ^ 2 - 2 * b * c * k₁ * k₂ + a * b * k₂ ^ 2
      - (d - 1 - c) * k₁ - (a - 1 - b) * k₂) := by
  rw [even_iff_two_dvd]
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
  have hdetmod : (a : ZMod 2) * d - b * c = 1 := by
    rw [← Int.cast_mul, ← Int.cast_mul, ← Int.cast_sub, hdet]
    norm_num
  have hmod : ∀ a b c d k₁ k₂ : ZMod 2, a * d - b * c = 1 →
      c * d * k₁ ^ 2 - 2 * b * c * k₁ * k₂ + a * b * k₂ ^ 2 -
        (d - 1 - c) * k₁ - (a - 1 - b) * k₂ = 0 := by decide
  push_cast
  exact hmod _ _ _ _ _ _ hdetmod

/-- The polynomial identity underlying `thetaCharacterExponent_eq_add_intCast`, before using
the parity of its correction numerator. -/
private theorem thetaCharacterExponent_eq_sub_correction {r : Fin 2 → ℚ}
    {M : Mat(2, ℤ)} {k₁ k₂ : ℤ}
    (hdet : (M 0 0 : ℚ) * M 1 1 - M 0 1 * M 1 0 = 1)
    (hk₁ : ((M 0 0 : ℚ) - 1) * r 0 + (M 0 1 : ℚ) * r 1 = k₁)
    (hk₂ : (M 1 0 : ℚ) * r 0 + ((M 1 1 : ℚ) - 1) * r 1 = k₂) :
    thetaCharacterExponent r M =
      ((k₁ : ℚ) + k₂ + k₁ * k₂ + k₁ * r 1 - k₂ * r 0) / 2 -
        ((M 1 0 * M 1 1 * k₁ ^ 2 - 2 * M 0 1 * M 1 0 * k₁ * k₂
          + M 0 0 * M 0 1 * k₂ ^ 2 - (M 1 1 - 1 - M 1 0) * k₁
          - (M 0 0 - 1 - M 0 1) * k₂ : ℤ) : ℚ) / 2 := by
  unfold thetaCharacterExponent
  push_cast
  linear_combination
    -(-M 0 1 * k₂ * r 1 + M 0 1 * r 1 ^ 2 - M 1 0 * k₁ * r 0
      + M 1 0 * r 0 ^ 2 - r 0 * r 1 + r 0 + r 1) / 2 * hdet +
    -(M 0 1 * M 1 0 ^ 2 * r 0 + M 0 1 * M 1 0 * M 1 1 * r 1
      - 2 * M 0 1 * M 1 0 * k₂ + M 1 0 * M 1 1 * k₁
      - M 1 0 * M 1 1 * r 0 + M 1 0 * r 0 + M 1 0 - M 1 1 - k₂ - r 1) / 2 * hk₁ +
    (M 0 0 * M 0 1 * M 1 0 * r 0 - M 0 0 * M 0 1 * k₂
      + M 0 0 * M 0 1 * r 1 + M 0 0 * r 0 + M 0 0
      + M 0 1 ^ 2 * M 1 0 * r 1 - 2 * M 0 1 * M 1 0 * r 0
      - M 0 1 - 2 * r 0) / 2 * hk₂

/-- **The simplified exponent of the theta multiplier** [72, Kopp (2024), Lemma 2.15,
`lem:charsimp`], with the integrality witnesses `k₁ = ((M - I)r)₁`, `k₂ = ((M - I)r)₂` made
explicit: `thetaCharacterExponent r M = (k₁ + k₂ + k₁k₂ + k₁r₂ - k₂r₁)/2 + j` for an
integer `j`. See the section comment for the polynomial identity and the parity argument. -/
theorem thetaCharacterExponent_eq_add_intCast {r : Fin 2 → ℚ} (M : SL(2, ℤ)) {k₁ k₂ : ℤ}
    (hk₁ : ((M 0 0 : ℚ) - 1) * r 0 + (M 0 1 : ℚ) * r 1 = k₁)
    (hk₂ : (M 1 0 : ℚ) * r 0 + ((M 1 1 : ℚ) - 1) * r 1 = k₂) :
    ∃ j : ℤ, thetaCharacterExponent r M =
      ((k₁ : ℚ) + k₂ + k₁ * k₂ + k₁ * r 1 - k₂ * r 0) / 2 + j := by
  have hdetInt := det_fin_two_cast_eq_one (R := ℤ) M
  have hdet' := det_fin_two_cast_eq_one (R := ℚ) M
  let N : ℤ := M 1 0 * M 1 1 * k₁ ^ 2 - 2 * M 0 1 * M 1 0 * k₁ * k₂
    + M 0 0 * M 0 1 * k₂ ^ 2 - (M 1 1 - 1 - M 1 0) * k₁
    - (M 0 0 - 1 - M 0 1) * k₂
  have hEven : Even N := thetaCharacterNumerator_even _ _ _ _ _ _ hdetInt
  obtain ⟨n, hn⟩ := hEven
  have hN : N = 2 * n := by linear_combination hn
  refine ⟨-n, ?_⟩
  have hpoly : thetaCharacterExponent r M =
      ((k₁ : ℚ) + k₂ + k₁ * k₂ + k₁ * r 1 - k₂ * r 0) / 2 - (N : ℚ) / 2 := by
    simpa only [N] using thetaCharacterExponent_eq_sub_correction hdet' hk₁ hk₂
  rw [hpoly, hN]
  push_cast
  ring

/-- **The simplified theta multiplier** [72, Kopp (2024), Lemma 2.15, `lem:charsimp`]:
`χ_r(M) = e((k₁ + k₂ + k₁k₂ + k₁r₂ - k₂r₁)/2)` for the integrality witnesses of `M ∈ Γ_r`, by
`thetaCharacterExponent_eq_add_intCast` and `Complex.exp_int_mul_two_pi_mul_I`. -/
@[source "72, Lemma 2.15, p. 18, lem:charsimp"]
theorem thetaCharacter_eq_exp {r : Fin 2 → ℚ} (M : SL(2, ℤ)) {k₁ k₂ : ℤ}
    (hk₁ : ((M 0 0 : ℚ) - 1) * r 0 + (M 0 1 : ℚ) * r 1 = k₁)
    (hk₂ : (M 1 0 : ℚ) * r 0 + ((M 1 1 : ℚ) - 1) * r 1 = k₂) :
    thetaCharacter r M =
      Complex.exp (2 * π * I *
        ((((k₁ : ℚ) + k₂ + k₁ * k₂ + k₁ * r 1 - k₂ * r 0) / 2 : ℚ) : ℂ)) := by
  obtain ⟨j, hj⟩ := thetaCharacterExponent_eq_add_intCast M hk₁ hk₂
  unfold thetaCharacter
  rw [hj]
  apply exp_two_pi_I_eq_of_sub_intCast _ _ j
  push_cast
  ring

/-! ### The character in its characteristic

Kopp's `χ_r(M)` is a character of `M ∈ Γ_r` ([72, Kopp (2024), Theorem 2.14, `thm:thetamod`]);
this section studies it as a function of `r`. Through the simplified formula
`thetaCharacter_eq_exp`, with `(M - I)r = (k₁, k₂)`:

- `χ_r(M) = 1` for `r ∈ ℤ²`, since then `k₁ + k₂ + k₁k₂ + k₁r₂ - k₂r₁` is even;
- `χ_{r+e}(M) = χ_r(M)` for `e ∈ ℤ²` and `M ∈ Γ_r`, so `χ_·(M)` lives on `Γ_r`-characteristics
  modulo `ℤ²`;
- the Gaussian law `χ_{r+s}(M) = χ_r(M) χ_s(M) e(k₁s₂ - k₂s₁)` for `M ∈ Γ_r ∩ Γ_s`, whose
  quotient is the bicharacter `⟨r; s⟩_M := χ_{r+s}(M)/(χ_r(M)χ_s(M))`.

These are the Gaussian `⟨u⟩_γ = (-1)^{u₁+u₂+u₁u₂} e_{2N}(ω(uγ, u))` and the bicharacter
`⟨u; v⟩_γ = e_N(ω(uγ - u, v)) = ⟨u+v⟩_γ/(⟨u⟩_γ⟨v⟩_γ)` of Radchenko and Wheeler,
[RW26, Radchenko, Wheeler (2026), equation (3), `eq:gaussianpairing`;
Section 3.2, before Lemma 2, `lem:lam.inv`], written for the row vector
`u = (k₂, -k₁)` with `(k₁, k₂) = (γ - I)r`, `N = tr γ - 2`, and `ω(v, w) = v₁w₂ - v₂w₁`, for
every `M` of trace `≠ 2`. -/

/-- The witnesses `(k₁, k₂) = (M - I)r` for `M ∈ Γ_r`, in the shape used by
`thetaCharacter_eq_exp`, from `ratVecAction_sub_intVec_of_mem_gammaSubgroup`. -/
theorem exists_thetaCharacter_witnesses {r : Fin 2 → ℚ} {M : SL(2, ℤ)}
    (hM : M ∈ gammaSubgroup r) :
    ∃ k₁ k₂ : ℤ,
      ((M 0 0 : ℚ) - 1) * r 0 + (M 0 1 : ℚ) * r 1 = k₁ ∧
      (M 1 0 : ℚ) * r 0 + ((M 1 1 : ℚ) - 1) * r 1 = k₂ := by
  obtain ⟨k₁, h₁⟩ := ratVecAction_sub_intVec_of_mem_gammaSubgroup hM 0
  obtain ⟨k₂, h₂⟩ := ratVecAction_sub_intVec_of_mem_gammaSubgroup hM 1
  refine ⟨k₁, k₂, ?_, ?_⟩ <;>
    simp only [ratVecAction, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.map_apply] at h₁ h₂ <;>
    linarith

/-- Integral shifts of a rational exponent leave its phase unchanged; used by
`thetaCharacter_of_isIntegralIndex` and `thetaCharacter_add`. -/
private theorem thetaPhase_add_int (q : ℚ) (n : ℤ) :
    Complex.exp (2 * π * I * (((q + n : ℚ) : ℂ))) =
      Complex.exp (2 * π * I * (q : ℂ)) := by
  exact exp_two_pi_I_eq_of_sub_intCast _ _ n (by push_cast; ring)

/-- An even integer numerator gives the trivial phase in
`thetaCharacter_of_isIntegralIndex`. -/
private theorem thetaPhase_even {n : ℤ} (hn : Even n) :
    Complex.exp (2 * π * I * (((n : ℚ) / 2 : ℚ) : ℂ)) = 1 := by
  obtain ⟨j, rfl⟩ := hn
  calc
    _ = Complex.exp (2 * π * I * (0 : ℂ)) :=
      exp_two_pi_I_eq_of_sub_intCast _ _ j (by push_cast; ring)
    _ = 1 := by simp

/-- The phase of a sum is the product of phases; used by `thetaCharacter_add`. -/
private theorem thetaPhase_add (q t : ℚ) :
    Complex.exp (2 * π * I * (((q + t : ℚ) : ℂ))) =
      Complex.exp (2 * π * I * (q : ℂ)) *
        Complex.exp (2 * π * I * (t : ℂ)) := by
  rw [show 2 * (π : ℂ) * I * (((q + t : ℚ) : ℂ)) =
      2 * π * I * (q : ℂ) + 2 * π * I * (t : ℂ) by push_cast; ring,
    Complex.exp_add]

/-- The cross term in `thetaCharacter_add` reduces to the determinant of `M - I`. -/
private theorem thetaCharacter_cross_term {r s : Fin 2 → ℚ} (M : SL(2, ℤ))
    {k₁ k₂ l₁ l₂ : ℤ}
    (hk₁ : ((M 0 0 : ℚ) - 1) * r 0 + (M 0 1 : ℚ) * r 1 = k₁)
    (hk₂ : (M 1 0 : ℚ) * r 0 + ((M 1 1 : ℚ) - 1) * r 1 = k₂)
    (hl₁ : ((M 0 0 : ℚ) - 1) * s 0 + (M 0 1 : ℚ) * s 1 = l₁)
    (hl₂ : (M 1 0 : ℚ) * s 0 + ((M 1 1 : ℚ) - 1) * s 1 = l₂) :
    (l₁ : ℚ) * r 1 - l₂ * r 0 - k₁ * s 1 + k₂ * s 0 =
      (k₁ : ℚ) * l₂ - k₂ * l₁ := by
  have hdet := det_fin_two_cast_eq_one (R := ℚ) M
  rw [← hk₁, ← hk₂, ← hl₁, ← hl₂]
  linear_combination -(r 0 * s 1 - r 1 * s 0) * hdet

/-- The exponent identity for `thetaCharacter_add`; its integer correction is `k₁l₂`. -/
private theorem thetaCharacter_add_exponent {r s : Fin 2 → ℚ} (M : SL(2, ℤ))
    {k₁ k₂ l₁ l₂ : ℤ}
    (hk₁ : ((M 0 0 : ℚ) - 1) * r 0 + (M 0 1 : ℚ) * r 1 = k₁)
    (hk₂ : (M 1 0 : ℚ) * r 0 + ((M 1 1 : ℚ) - 1) * r 1 = k₂)
    (hl₁ : ((M 0 0 : ℚ) - 1) * s 0 + (M 0 1 : ℚ) * s 1 = l₁)
    (hl₂ : (M 1 0 : ℚ) * s 0 + ((M 1 1 : ℚ) - 1) * s 1 = l₂) :
    (((k₁ + l₁ : ℤ) : ℚ) + (k₂ + l₂ : ℤ) +
      (k₁ + l₁ : ℤ) * (k₂ + l₂ : ℤ) + (k₁ + l₁ : ℤ) * (r + s) 1 -
      (k₂ + l₂ : ℤ) * (r + s) 0) / 2 =
      ((k₁ : ℚ) + k₂ + k₁ * k₂ + k₁ * r 1 - k₂ * r 0) / 2 +
      ((l₁ : ℚ) + l₂ + l₁ * l₂ + l₁ * s 1 - l₂ * s 0) / 2 +
      ((k₁ : ℚ) * s 1 - k₂ * s 0) + (k₁ * l₂ : ℤ) := by
  have hcross := thetaCharacter_cross_term M hk₁ hk₂ hl₁ hl₂
  simp only [Pi.add_apply]
  push_cast
  linear_combination hcross / 2

/-- The numerator of Kopp's simplified character exponent is even at an integral characteristic;
used by `thetaCharacter_of_isIntegralIndex`. -/
private theorem thetaCharacter_integral_numerator_even (a b c d m n k₁ k₂ : ℤ)
    (hdet : a * d - b * c = 1)
    (hk₁ : (a - 1) * m + b * n = k₁)
    (hk₂ : c * m + (d - 1) * n = k₂) :
    Even (k₁ + k₂ + k₁ * k₂ + k₁ * n - k₂ * m) := by
  rw [← hk₁, ← hk₂]
  rw [even_iff_two_dvd]
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
  have hdetmod : (a : ZMod 2) * d - b * c = 1 := by
    rw [← Int.cast_mul, ← Int.cast_mul, ← Int.cast_sub, hdet]
    norm_num
  have hmod : ∀ a b c d m n : ZMod 2, a * d - b * c = 1 →
      ((a - 1) * m + b * n) + (c * m + (d - 1) * n) +
        ((a - 1) * m + b * n) * (c * m + (d - 1) * n) +
        ((a - 1) * m + b * n) * n - (c * m + (d - 1) * n) * m = 0 := by decide
  push_cast
  exact hmod _ _ _ _ _ _ hdetmod

/-- **`χ_r(M) = 1` at integral characteristics.** With `(M - I)r = (k₁, k₂) ∈ ℤ²`, the exponent
`(k₁ + k₂ + k₁k₂ + k₁r₂ - k₂r₁)/2` of `thetaCharacter_eq_exp` is an integer: `k₁ + k₂ + k₁k₂`
is even, and `k₁r₂ - k₂r₁ ≡ k₁ + k₂ + k₁k₂ (mod 2)` for integral `r`. Project-local
consequence of [72, Kopp (2024), Lemma 2.15, `lem:charsimp`], consumed by
`SICs.Principal.Dilogarithm.Values` at the zero class of `G_d`. -/
theorem thetaCharacter_of_isIntegralIndex {r : Fin 2 → ℚ} (M : SL(2, ℤ))
    (hr : IsIntegralIndex r) : thetaCharacter r (M : Mat(2, ℤ)) = 1 := by
  obtain ⟨m, hm⟩ := hr 0
  obtain ⟨n, hn⟩ := hr 1
  let k₁ : ℤ := (M 0 0 - 1) * m + M 0 1 * n
  let k₂ : ℤ := M 1 0 * m + (M 1 1 - 1) * n
  have hk₁ : ((M 0 0 : ℚ) - 1) * r 0 + (M 0 1 : ℚ) * r 1 = k₁ := by
    rw [hm, hn]
    dsimp [k₁]
    push_cast
    ring
  have hk₂ : (M 1 0 : ℚ) * r 0 + ((M 1 1 : ℚ) - 1) * r 1 = k₂ := by
    rw [hm, hn]
    dsimp [k₂]
    push_cast
    ring
  have hdet := det_fin_two_cast_eq_one (R := ℤ) M
  have hz : Even (k₁ + k₂ + k₁ * k₂ + k₁ * n - k₂ * m) :=
    thetaCharacter_integral_numerator_even _ _ _ _ _ _ _ _ hdet rfl rfl
  rw [thetaCharacter_eq_exp M hk₁ hk₂]
  have hexp : (((k₁ : ℚ) + k₂ + k₁ * k₂ + k₁ * r 1 - k₂ * r 0) / 2 : ℚ) =
      (((k₁ + k₂ + k₁ * k₂ + k₁ * n - k₂ * m : ℤ) : ℚ) / 2) := by
    rw [hm, hn]
    push_cast
    ring
  rw [hexp]
  exact thetaPhase_even hz

/-- **The Gaussian law of the character in its characteristic**: for `M ∈ Γ_r ∩ Γ_s` with
`(M - I)r = (k₁, k₂)`,
`χ_{r+s}(M) = χ_r(M) χ_s(M) e(k₁s₂ - k₂s₁)`.
In the notation of [RW26, Radchenko, Wheeler (2026), Section 3.2, before Lemma 2, `lem:lam.inv`],
`⟨u+v⟩_γ = ⟨u⟩_γ ⟨v⟩_γ ⟨u; v⟩_γ` with `⟨u; v⟩_γ = e_N(ω(uγ - u, v))`; proved from
`thetaCharacter_eq_exp` at `r`, `s`, and `r + s`. -/
theorem thetaCharacter_add {r s : Fin 2 → ℚ} (M : SL(2, ℤ)) {k₁ k₂ : ℤ}
    (hk₁ : ((M 0 0 : ℚ) - 1) * r 0 + (M 0 1 : ℚ) * r 1 = k₁)
    (hk₂ : (M 1 0 : ℚ) * r 0 + ((M 1 1 : ℚ) - 1) * r 1 = k₂)
    (hs : M ∈ gammaSubgroup s) :
    thetaCharacter (r + s) (M : Mat(2, ℤ)) =
      thetaCharacter r (M : Mat(2, ℤ)) * thetaCharacter s (M : Mat(2, ℤ)) *
        Complex.exp (2 * π * I * (((k₁ : ℚ) * s 1 - (k₂ : ℚ) * s 0 : ℚ) : ℂ)) := by
  obtain ⟨l₁, l₂, hl₁, hl₂⟩ := exists_thetaCharacter_witnesses hs
  have hsum₁ : ((M 0 0 : ℚ) - 1) * (r + s) 0 + (M 0 1 : ℚ) * (r + s) 1 =
      (k₁ + l₁ : ℤ) := by
    simp only [Pi.add_apply]
    push_cast
    linear_combination hk₁ + hl₁
  have hsum₂ : (M 1 0 : ℚ) * (r + s) 0 + ((M 1 1 : ℚ) - 1) * (r + s) 1 =
      (k₂ + l₂ : ℤ) := by
    simp only [Pi.add_apply]
    push_cast
    linear_combination hk₂ + hl₂
  rw [thetaCharacter_eq_exp M hsum₁ hsum₂, thetaCharacter_eq_exp M hk₁ hk₂,
    thetaCharacter_eq_exp M hl₁ hl₂]
  rw [thetaCharacter_add_exponent M hk₁ hk₂ hl₁ hl₂]
  rw [thetaPhase_add_int, thetaPhase_add, thetaPhase_add]

/-- **`ℤ²`-periodicity of the character in its characteristic**: `χ_{r+e}(M) = χ_r(M)` for
`e ∈ ℤ²` and `M ∈ Γ_r`. This is the `Λ`-periodicity of the Gaussian `⟨u⟩_γ` asserted in
[RW26, Radchenko, Wheeler (2026), Section 1, before Theorem 2, `thm:fg.equs`,
`eq:fgam.def`], which makes it a
function on `G = ℤ²/Λ`; proved from `thetaCharacter_add` and the integral case. -/
theorem thetaCharacter_add_of_isIntegralIndex {r e : Fin 2 → ℚ} (M : SL(2, ℤ))
    (hM : M ∈ gammaSubgroup r) (he : IsIntegralIndex e) :
    thetaCharacter (r + e) (M : Mat(2, ℤ)) = thetaCharacter r (M : Mat(2, ℤ)) := by
  obtain ⟨k₁, k₂, hk₁, hk₂⟩ := exists_thetaCharacter_witnesses hM
  obtain ⟨m, hm⟩ := he 0
  obtain ⟨n, hn⟩ := he 1
  have heM : M ∈ gammaSubgroup e :=
    mem_gammaSubgroup_of_isIntegralIndex
      (isIntegralIndex_sub (isIntegralIndex_ratVecAction M he) he)
  have hphase : Complex.exp (2 * π * I *
      (((k₁ : ℚ) * e 1 - (k₂ : ℚ) * e 0 : ℚ) : ℂ)) = 1 := by
    rw [hm, hn]
    calc
      _ = Complex.exp (2 * π * I * (0 : ℂ)) :=
        exp_two_pi_I_eq_of_sub_intCast _ _ (k₁ * n - k₂ * m) (by push_cast; ring)
      _ = 1 := by simp
  rw [thetaCharacter_add M hk₁ hk₂ heM, thetaCharacter_of_isIntegralIndex M he,
    mul_one, hphase, mul_one]

/-- **The character is even on `Γ_r`**: `χ_{-r}(M) = χ_r(M)` for `M ∈ Γ_r`. Under
`(r, k) ↦ (-r, -k)` the exponent `(k₁ + k₂ + k₁k₂ + k₁r₂ - k₂r₁)/2` of `thetaCharacter_eq_exp`
changes by the integer `-(k₁ + k₂)`. Evenness of the Gaussian `⟨u⟩_γ` is immediate from its
formula in [RW26, Radchenko, Wheeler (2026), Section 1, before Theorem 2, `thm:fg.equs`,
`eq:fgam.def`]. -/
theorem thetaCharacter_neg {r : Fin 2 → ℚ} (M : SL(2, ℤ)) (hr : M ∈ gammaSubgroup r) :
    thetaCharacter (-r) (M : Mat(2, ℤ)) = thetaCharacter r (M : Mat(2, ℤ)) := by
  obtain ⟨k₁, k₂, hk₁, hk₂⟩ := exists_thetaCharacter_witnesses hr
  have hn₁ : ((M 0 0 : ℚ) - 1) * (-r) 0 + (M 0 1 : ℚ) * (-r) 1 = (-k₁ : ℤ) := by
    simp only [Pi.neg_apply, Int.cast_neg]
    linear_combination -hk₁
  have hn₂ : (M 1 0 : ℚ) * (-r) 0 + ((M 1 1 : ℚ) - 1) * (-r) 1 = (-k₂ : ℤ) := by
    simp only [Pi.neg_apply, Int.cast_neg]
    linear_combination -hk₂
  rw [thetaCharacter_eq_exp M hn₁ hn₂, thetaCharacter_eq_exp M hk₁ hk₂]
  have hq : ((((-k₁ : ℤ) : ℚ) + (-k₂ : ℤ) + (-k₁ : ℤ) * (-k₂ : ℤ) +
      (-k₁ : ℤ) * (-r) 1 - (-k₂ : ℤ) * (-r) 0) / 2 : ℚ) =
      (((k₁ : ℚ) + k₂ + k₁ * k₂ + k₁ * r 1 - k₂ * r 0) / 2 : ℚ) +
        (-(k₁ + k₂) : ℤ) := by
    simp only [Pi.neg_apply]
    push_cast
    ring
  rw [hq, thetaPhase_add_int]

/-- **The bicharacter** `⟨r; s⟩_M = χ_{r+s}(M) / (χ_r(M) χ_s(M))` of
[RW26, Radchenko, Wheeler (2026), Section 1, before Theorem 2, `thm:fg.equs`, `eq:fgam.def`],
there written `⟨u; v⟩_γ = e_N(ω(uγ - u, v))` and identified with this quotient in Section 3.2
before Lemma 2, `lem:lam.inv`; defined for every integer matrix and every pair of rational
characteristics, and evaluated in closed form on `Γ_r ∩ Γ_s` by `thetaBicharacter_eq_exp`. -/
def thetaBicharacter (r s : Fin 2 → ℚ) (M : Mat(2, ℤ)) : ℂ :=
  thetaCharacter (r + s) M / (thetaCharacter r M * thetaCharacter s M)

/-- `⟨r; s⟩_M = e(k₁s₂ - k₂s₁)` for `M ∈ Γ_r ∩ Γ_s` with `(M - I)r = (k₁, k₂)`; the closed form
`⟨u; v⟩_γ = e_N(ω(uγ - u, v))` of [RW26, Radchenko, Wheeler (2026), Section 1, before
Theorem 2, `thm:fg.equs`, `eq:fgam.def`], by `thetaCharacter_add`. -/
theorem thetaBicharacter_eq_exp {r s : Fin 2 → ℚ} (M : SL(2, ℤ)) {k₁ k₂ : ℤ}
    (hk₁ : ((M 0 0 : ℚ) - 1) * r 0 + (M 0 1 : ℚ) * r 1 = k₁)
    (hk₂ : (M 1 0 : ℚ) * r 0 + ((M 1 1 : ℚ) - 1) * r 1 = k₂)
    (hs : M ∈ gammaSubgroup s) :
    thetaBicharacter r s (M : Mat(2, ℤ)) =
      Complex.exp (2 * π * I * (((k₁ : ℚ) * s 1 - (k₂ : ℚ) * s 0 : ℚ) : ℂ)) := by
  rw [thetaBicharacter, thetaCharacter_add M hk₁ hk₂ hs]
  exact mul_div_cancel_left₀ _
    (mul_ne_zero (thetaCharacter_ne_zero _ _) (thetaCharacter_ne_zero _ _))

/-- The bicharacter is symmetric, `⟨r; s⟩_M = ⟨s; r⟩_M`, since `χ_{r+s} = χ_{s+r}`. -/
theorem thetaBicharacter_comm (r s : Fin 2 → ℚ) (M : Mat(2, ℤ)) :
    thetaBicharacter r s M = thetaBicharacter s r M := by
  simp only [thetaBicharacter, add_comm r s, mul_comm]

/-- `⟨0; s⟩_M = 1`, by `thetaCharacter_of_isIntegralIndex` at `r = 0`. -/
theorem thetaBicharacter_zero_left (s : Fin 2 → ℚ) (M : SL(2, ℤ)) :
    thetaBicharacter 0 s (M : Mat(2, ℤ)) = 1 := by
  simp [thetaBicharacter, thetaCharacter_of_isIntegralIndex M
    (show IsIntegralIndex (0 : Fin 2 → ℚ) from by
      intro i
      exact ⟨0, by simp⟩), thetaCharacter_ne_zero]

/-- **Additivity of the bicharacter in its first characteristic**:
`⟨r + r'; s⟩_M = ⟨r; s⟩_M ⟨r'; s⟩_M` for `M ∈ Γ_r ∩ Γ_{r'} ∩ Γ_s`, by `thetaBicharacter_eq_exp`
and the additivity of `(M - I)r` in `r`. -/
theorem thetaBicharacter_add_left {r r' s : Fin 2 → ℚ} (M : SL(2, ℤ))
    (hr : M ∈ gammaSubgroup r) (hr' : M ∈ gammaSubgroup r') (hs : M ∈ gammaSubgroup s) :
    thetaBicharacter (r + r') s (M : Mat(2, ℤ)) =
      thetaBicharacter r s (M : Mat(2, ℤ)) * thetaBicharacter r' s (M : Mat(2, ℤ)) := by
  obtain ⟨k₁, k₂, hk₁, hk₂⟩ := exists_thetaCharacter_witnesses hr
  obtain ⟨l₁, l₂, hl₁, hl₂⟩ := exists_thetaCharacter_witnesses hr'
  have hsum₁ : ((M 0 0 : ℚ) - 1) * (r + r') 0 + (M 0 1 : ℚ) * (r + r') 1 =
      (k₁ + l₁ : ℤ) := by
    simp only [Pi.add_apply]
    push_cast
    linear_combination hk₁ + hl₁
  have hsum₂ : (M 1 0 : ℚ) * (r + r') 0 + ((M 1 1 : ℚ) - 1) * (r + r') 1 =
      (k₂ + l₂ : ℤ) := by
    simp only [Pi.add_apply]
    push_cast
    linear_combination hk₂ + hl₂
  rw [thetaBicharacter_eq_exp M hsum₁ hsum₂ hs,
    thetaBicharacter_eq_exp M hk₁ hk₂ hs,
    thetaBicharacter_eq_exp M hl₁ hl₂ hs]
  have hq : ((k₁ + l₁ : ℤ) : ℚ) * s 1 - ((k₂ + l₂ : ℤ) : ℚ) * s 0 =
      ((k₁ : ℚ) * s 1 - k₂ * s 0) + ((l₁ : ℚ) * s 1 - l₂ * s 0) := by
    push_cast
    ring
  rw [hq, thetaPhase_add]

/-- **`ℤ²`-periodicity of the bicharacter in its first characteristic**:
`⟨r + e; s⟩_M = ⟨r; s⟩_M` for `e ∈ ℤ²` and `M ∈ Γ_r ∩ Γ_s`, by
`thetaBicharacter_add_left` and `thetaCharacter_add_of_isIntegralIndex`. -/
theorem thetaBicharacter_add_of_isIntegralIndex_left {r e s : Fin 2 → ℚ} (M : SL(2, ℤ))
    (hr : M ∈ gammaSubgroup r) (hs : M ∈ gammaSubgroup s) (he : IsIntegralIndex e) :
    thetaBicharacter (r + e) s (M : Mat(2, ℤ)) = thetaBicharacter r s (M : Mat(2, ℤ)) := by
  have heM : M ∈ gammaSubgroup e :=
    mem_gammaSubgroup_of_isIntegralIndex
      (isIntegralIndex_sub (isIntegralIndex_ratVecAction M he) he)
  have hzero : thetaBicharacter e s (M : Mat(2, ℤ)) = 1 := by
    unfold thetaBicharacter
    rw [show e + s = s + e by abel, thetaCharacter_add_of_isIntegralIndex M hs he,
      thetaCharacter_of_isIntegralIndex M he, one_mul]
    exact div_self (thetaCharacter_ne_zero s M)
  rw [thetaBicharacter_add_left M hr heM hs, hzero, mul_one]

/-- The bicharacter exponent in terms of the rational vector `(M-I)r`, used by
`thetaBicharacter_conj`. -/
private theorem thetaBicharacter_eq_exp_diff {r s : Fin 2 → ℚ} (M : SL(2, ℤ))
    (hr : M ∈ gammaSubgroup r) (hs : M ∈ gammaSubgroup s) :
    thetaBicharacter r s M =
      Complex.exp (2 * Real.pi * I *
        ((((ratVecAction (M : Mat(2, ℤ)) r - r) 0) * s 1 -
          ((ratVecAction (M : Mat(2, ℤ)) r - r) 1) * s 0 : ℚ) : ℂ)) := by
  obtain ⟨k₀, k₁, hk₀, hk₁⟩ := exists_thetaCharacter_witnesses hr
  rw [thetaBicharacter_eq_exp M hk₀ hk₁ hs]
  have h₀ : (ratVecAction (M : Mat(2, ℤ)) r - r) 0 = (k₀ : ℚ) := by
    simp only [ratVecAction, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.map_apply, Pi.sub_apply]
    linear_combination hk₀
  have h₁ : (ratVecAction (M : Mat(2, ℤ)) r - r) 1 = (k₁ : ℚ) := by
    simp only [ratVecAction, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.map_apply, Pi.sub_apply]
    linear_combination hk₁
  rw [h₀, h₁]
/-- Determinant-one matrices preserve the symplectic pairing of rational vectors, used by
`thetaBicharacter_conj`. -/
private theorem symplectic_ratVecAction (R : SL(2, ℤ)) (k s : Fin 2 → ℚ) :
    (ratVecAction (R : Mat(2, ℤ)) k) 0 * (ratVecAction (R : Mat(2, ℤ)) s) 1 -
      (ratVecAction (R : Mat(2, ℤ)) k) 1 * (ratVecAction (R : Mat(2, ℤ)) s) 0 =
        k 0 * s 1 - k 1 * s 0 := by
  have hdet := det_fin_two_cast_eq_one (R := ℚ) R
  simp only [ratVecAction, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.map_apply]
  linear_combination (k 0 * s 1 - k 1 * s 0) * hdet
/-- The theta bicharacter is invariant under determinant-one conjugation on fixed rational
characteristics. The exponent is the symplectic pairing of `(A-I)r` with `s`. -/
theorem thetaBicharacter_conj {r s : Fin 2 → ℚ} (A R : SL(2, ℤ))
    (hr : A ∈ gammaSubgroup r) (hs : A ∈ gammaSubgroup s) :
    thetaBicharacter (ratVecAction (R : Mat(2, ℤ)) r)
      (ratVecAction (R : Mat(2, ℤ)) s) (R * A * R⁻¹ : SL(2, ℤ)) =
        thetaBicharacter r s A := by
  let B : SL(2, ℤ) := R * A * R⁻¹
  have hconj : (B : Mat(2, ℤ)) * (R : Mat(2, ℤ)) =
      (R : Mat(2, ℤ)) * (A : Mat(2, ℤ)) := by
    exact congrArg (fun M : SL(2, ℤ) => (M : Mat(2, ℤ)))
      (show B * R = R * A by simp [B, mul_assoc])
  have hrB : B ∈ gammaSubgroup (ratVecAction (R : Mat(2, ℤ)) r) :=
    mem_gammaSubgroup_ratVecAction_of_mul_eq hr hconj
  have hsB : B ∈ gammaSubgroup (ratVecAction (R : Mat(2, ℤ)) s) :=
    mem_gammaSubgroup_ratVecAction_of_mul_eq hs hconj
  rw [thetaBicharacter_eq_exp_diff B hrB hsB,
    thetaBicharacter_eq_exp_diff A hr hs]
  have hk : ratVecAction (B : Mat(2, ℤ)) (ratVecAction (R : Mat(2, ℤ)) r) -
      ratVecAction (R : Mat(2, ℤ)) r =
        ratVecAction (R : Mat(2, ℤ)) (ratVecAction (A : Mat(2, ℤ)) r - r) := by
    calc
      _ = ratVecAction ((B : Mat(2, ℤ)) * (R : Mat(2, ℤ))) r -
          ratVecAction (R : Mat(2, ℤ)) r := by rw [ratVecAction_mul]
      _ = ratVecAction ((R : Mat(2, ℤ)) * (A : Mat(2, ℤ))) r -
          ratVecAction (R : Mat(2, ℤ)) r := by rw [hconj]
      _ = _ := by rw [ratVecAction_mul, ratVecAction_sub]
  rw [hk, symplectic_ratVecAction]

end SIC

end
