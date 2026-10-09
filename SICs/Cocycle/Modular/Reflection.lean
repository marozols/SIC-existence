/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Cocycle.Modular.Values
import SICs.Cocycle.Word.Reflection

/-!
# Reflection of real modular values

Modular reflection and its fixed-point form.

The reflection `r ↦ -r` follows from the word reflection law and the finite-product
reflection identity in [AFK25, proof of Theorem 5.8, `thm:nupnumpeq1`]. At a fixed point
the rational characteristic's integrality witnesses simplify the exponential prefactor,
giving the reflected product and its norm. These identities supply the overlap reciprocity
and fixed-point character computations.
-/

noncomputable section

open ModularGroup MatrixGroups

open scoped MatrixGroups

namespace SIC

/-! ### The reflection law `r ↦ -r`

Pairing the word-level reflection of `SICs.Cocycle.Word.Reflection` with the `q`-Pochhammer
reflection of `SICs.SpecialFunctions.QPochhammer.Finite` gives the cocycle's own behaviour
under negating the characteristic. This is the real form of the functional equation
[72, Kopp (2024), Theorem 4.32, `thm:funchar`], whose fixed-point specialization
[72, Kopp (2024), Theorem 4.36, `thm:shincharacter`] is the analytic input to the reciprocity
identity [AFK25, Theorem 5.8, `thm:nupnumpeq1`].

The exponential factor is `SICs.Cocycle.Word.Reflection.wordSfExpArg`.
Its closed form is `wordSfExpArg_eq`; the fixed-point character identity is proved in
`SICs.Cocycle.FixedPointCharacter`. Together with the Rademacher invariant in the SF phase,
these formulas give the phase relation [AFK25, Theorem 5.6, `thm:phaserelation`]. -/

/-- **The reflection law for the real Shintani--Faddeev modular cocycle.** Writing
`z = ⟨⟨r,τ⟩⟩`, `x = z/j_M(τ)`, `μ = M·τ` and `n = n_QP(r,M)`,

```text
ש^r_M(τ)·ש^{-r}_M(τ) · (1 - e(-z)) · (-1)^n e(nx + n(n+1)μ/2) (1 - e(x))
  = (1 - e(-x)) · exp(2·X_M(z,τ)) · (1 - e(x + nμ)),
```

with `e(y) = e^{2πiy}` and `X_M` the word-accumulated `wordSfExpArg`. This is the real form
of [72, Kopp (2024), Theorem 4.32, `thm:funchar`]. Every factor is explicit except `exp(2X_M)`;
compare the source's right-hand side, where the same content appears as `ψ²(A)χ_r(A)` times an
eta-quotient of `τ` and `M·τ`.

At a fixed point `M·τ = τ` the source's eta-quotient becomes `1`, leaving the root of unity
`ψ²(A)χ_r(A)` of [72, Kopp (2024), Theorem 4.36, `thm:shincharacter`]. The evaluation of `X_M`
is `wordSfExpArg_eq`; `SICs.Cocycle.FixedPointCharacter` identifies the resulting character.
This supplies the phase computation in [AFK25, Theorem 5.6, `thm:phaserelation`] used for
[AFK25, Theorem 5.8, `thm:nupnumpeq1`].

Stated multiplicatively; the hypotheses are the word walk's standing ones, `hlat` being the source's
`r ∉ ℤ²` on the real line. -/
theorem sfModularCocycleReal_mul_neg {r : Fin 2 → ℚ} {M : SL(2, ℤ)} {τ : ℝ}
    (hτ : Irrational τ) (hM : M ∈ gammaSubgroup r)
    (h0 : 0 ≤ M 1 0) (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) τ)
    (hlat : SigmaSLatticeFree τ (fracSymplecticFormRat r τ)) :
    sfModularCocycleReal r M hM h0 τ *
          sfModularCocycleReal (-r) M (neg_mem_gammaSubgroup hM) h0 τ *
        ((1 - Complex.exp (-(2 * Real.pi * Complex.I *
            ((fracSymplecticFormRat r τ : ℝ) : ℂ)))) *
          ((-1 : ℂ) ^ nQPInt r (M : Mat(2, ℤ)) *
            Complex.exp (2 * Real.pi * Complex.I *
              ((nQPInt r (M : Mat(2, ℤ)) : ℂ) *
                  ((fracSymplecticFormRat r τ /
                    fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ) +
                (nQPInt r (M : Mat(2, ℤ)) : ℂ) *
                  ((nQPInt r (M : Mat(2, ℤ)) : ℂ) + 1) / 2 *
                  ((flt (M : Mat(2, ℤ)) τ : ℝ) : ℂ))) *
            (1 - Complex.exp (2 * Real.pi * Complex.I *
              ((fracSymplecticFormRat r τ /
                fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ))))) =
      (1 - Complex.exp (-(2 * Real.pi * Complex.I *
          ((fracSymplecticFormRat r τ /
            fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ)))) *
        Complex.exp (2 * wordSfExpArg (fracSymplecticFormRat r τ) τ M h0) *
        (1 - Complex.exp (2 * Real.pi * Complex.I *
          (((fracSymplecticFormRat r τ /
              fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ) +
            (nQPInt r (M : Mat(2, ℤ)) : ℂ) *
              ((flt (M : Mat(2, ℤ)) τ : ℝ) : ℂ)))) := by
  set z : ℝ := fracSymplecticFormRat r τ with hz
  set J : ℝ := fltDenominator (M : Mat(2, ℤ)) τ with hJ
  set μ : ℝ := flt (M : Mat(2, ℤ)) τ with hμ
  set n : ℤ := nQPInt r (M : Mat(2, ℤ)) with hn
  set x : ℝ := z / J with hx
  have hJ0 : J ≠ 0 := hjac.ne'
  have hxC : ((x : ℝ) : ℂ) = ((z : ℝ) : ℂ) / ((J : ℝ) : ℂ) := by rw [hx]; push_cast; ring
  -- Lattice-freeness transports to the rescaled argument, ruling out every vanishing factor.
  have hlatx : SigmaSLatticeFree μ x := hlat.div_fltDenominator hJ0
  have hfac : ∀ j : ℤ,
      (1 : ℂ) - Complex.exp (2 * Real.pi * Complex.I *
        (((x : ℝ) : ℂ) + (j : ℂ) * ((μ : ℝ) : ℂ))) ≠ 0 :=
    fun j => hlatx.one_sub_exp_ne_zero j
  have hfacneg : ∀ j : ℤ,
      (1 : ℂ) - Complex.exp (2 * Real.pi * Complex.I *
        (-((x : ℝ) : ℂ) + (j : ℂ) * ((μ : ℝ) : ℂ))) ≠ 0 := by
    intro j
    have h := hlatx.neg.one_sub_exp_ne_zero j
    rwa [Complex.ofReal_neg] at h
  have hP : qPochhammerFin n ((x : ℝ) : ℂ) ((μ : ℝ) : ℂ) ≠ 0 :=
    qPochhammerFin_ne_zero_of_forall_factor_ne_zero _ _ _ hfac
  have hQ : qPochhammerFin (-n) (-((x : ℝ) : ℂ)) ((μ : ℝ) : ℂ) ≠ 0 :=
    qPochhammerFin_ne_zero_of_forall_factor_ne_zero _ _ _ hfacneg
  -- The two halves: the word walk's reflection and the `q`-Pochhammer reflection.
  have hword := wordSigmaS_mul_neg hτ z hlat M h0 hjac
  have hrefl := qPochhammerFin_mul_neg_reflect n ((x : ℝ) : ℂ) ((μ : ℝ) : ℂ) hfac
  have hr : ¬ IsIntegralIndex r := by
    intro h
    obtain ⟨a, ha⟩ := h 1
    obtain ⟨b, hb⟩ := h 0
    apply hlat a (-b)
    simp [z, fracSymplecticFormRat, ha, hb, sub_eq_add_neg]
  rw [sfModularCocycleReal_eq_of_not_isIntegralIndex hr,
    sfModularCocycleReal_eq_of_not_isIntegralIndex (hr ∘ (isIntegralIndex_neg_iff r).mp),
    fracSymplecticFormRat_neg,
    nQPInt_neg, ← hz, ← hJ, ← hμ, ← hn, ← hxC,
    show ((-z : ℝ) : ℂ) / ((J : ℝ) : ℂ) = -((x : ℝ) : ℂ) from by rw [hxC]; push_cast; ring,
    div_mul_div_comm, div_mul_eq_mul_div, div_eq_iff (mul_ne_zero hP hQ)]
  rw [← hxC] at hword
  calc
    wordSigmaS z τ M h0 * wordSigmaS (-z) τ M h0 *
        ((1 - Complex.exp (-(2 * Real.pi * Complex.I * ((z : ℝ) : ℂ)))) *
          ((-1 : ℂ) ^ n *
            Complex.exp (2 * Real.pi * Complex.I *
              ((n : ℂ) * ((x : ℝ) : ℂ) + (n : ℂ) * ((n : ℂ) + 1) / 2 * ((μ : ℝ) : ℂ))) *
            (1 - Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) : ℂ)))))
        = (wordSigmaS z τ M h0 * wordSigmaS (-z) τ M h0 *
            (1 - Complex.exp (-(2 * Real.pi * Complex.I * ((z : ℝ) : ℂ))))) *
          ((-1 : ℂ) ^ n *
            Complex.exp (2 * Real.pi * Complex.I *
              ((n : ℂ) * ((x : ℝ) : ℂ) + (n : ℂ) * ((n : ℂ) + 1) / 2 * ((μ : ℝ) : ℂ))) *
            (1 - Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) : ℂ)))) := by ring
    _ = ((1 - Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℝ) : ℂ)))) *
          Complex.exp (2 * wordSfExpArg z τ M h0)) *
        (qPochhammerFin n ((x : ℝ) : ℂ) ((μ : ℝ) : ℂ) *
          qPochhammerFin (-n) (-((x : ℝ) : ℂ)) ((μ : ℝ) : ℂ) *
          (1 - Complex.exp (2 * Real.pi * Complex.I *
            (((x : ℝ) : ℂ) + (n : ℂ) * ((μ : ℝ) : ℂ))))) := by
        rw [hword, ← hrefl]
    _ = _ := by ring


/-! ### The reflection at a fixed point

At a fixed point of `M` the two end factors of `sfModularCocycleReal_mul_neg` coincide: the
rescaled argument `x = z/j_M(τ)`, moved by `n_QP(r,M)` periods, returns to `z` up to an integer.
That is the index bookkeeping of `Γ_r` -- the *other* coordinate of `(M - I)r` -- and it collapses
the reflection law to a closed form with no `1 - e(·)` factors, as in
[72, Kopp (2024), Theorem 4.36, `thm:shincharacter`]. -/

/-- **The reflection law at a fixed point.** If `M·τ = τ`, then with `z = ⟨⟨r,τ⟩⟩`,
`x = z/j_M(τ)` and `n = n_QP(r,M)`,

```text
ש^r_M(τ)·ש^{-r}_M(τ) = (-1)^n · e(z - (1+n)x - n(n+1)τ/2) · exp(2·X_M(z,τ)).
```

Every `1 - e(·)` factor of `sfModularCocycleReal_mul_neg` has cancelled: at a fixed point
`div_fltDenominator_add_nQPInt_mul` makes the two end factors equal, and
`1 - e(-y) = -e(-y)(1 - e(y))` matches the remaining pair. This is the real form of
[72, Kopp (2024), Theorem 4.36, `thm:shincharacter`].

Substituting `SICs.Cocycle.Word.Reflection.wordSfExpArg_eq` for `X_M` makes the right-hand side
completely explicit, and at a fixed point its `τ - M·τ` term vanishes; what is left of
[AFK25, Theorem 5.8, `thm:nupnumpeq1`] is then the phase bookkeeping of
[AFK25, Theorem 5.6, `thm:phaserelation`]. -/
theorem sfModularCocycleReal_mul_neg_of_flt_eq_self {r : Fin 2 → ℚ} {M : SL(2, ℤ)} {τ : ℝ}
    (hτ : Irrational τ) (hM : M ∈ gammaSubgroup r)
    (h0 : 0 ≤ M 1 0) (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) τ)
    (hfix : flt (M : Mat(2, ℤ)) τ = τ)
    (hlat : SigmaSLatticeFree τ (fracSymplecticFormRat r τ)) :
    sfModularCocycleReal r M hM h0 τ *
        sfModularCocycleReal (-r) M (neg_mem_gammaSubgroup hM) h0 τ =
      (-1 : ℂ) ^ nQPInt r (M : Mat(2, ℤ)) *
        (Complex.exp (2 * Real.pi * Complex.I * ((fracSymplecticFormRat r τ : ℝ) : ℂ)) *
          Complex.exp (-(2 * Real.pi * Complex.I *
            ((fracSymplecticFormRat r τ /
              fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ))) *
          Complex.exp (-(2 * Real.pi * Complex.I *
            ((nQPInt r (M : Mat(2, ℤ)) : ℂ) *
                ((fracSymplecticFormRat r τ /
                  fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ) +
              (nQPInt r (M : Mat(2, ℤ)) : ℂ) *
                ((nQPInt r (M : Mat(2, ℤ)) : ℂ) + 1) / 2 * (τ : ℂ))))) *
        Complex.exp (2 * wordSfExpArg (fracSymplecticFormRat r τ) τ M h0) := by
  set z : ℝ := fracSymplecticFormRat r τ with hz
  set J : ℝ := fltDenominator (M : Mat(2, ℤ)) τ with hJdef
  set x : ℝ := z / J with hxdef
  set n : ℤ := nQPInt r (M : Mat(2, ℤ)) with hn
  -- The five exponential values the identity is built from.
  set A : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((z : ℝ) : ℂ)) with hA
  set Am : ℂ := Complex.exp (-(2 * Real.pi * Complex.I * ((z : ℝ) : ℂ))) with hAm
  set B : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) : ℂ)) with hB
  set Bm : ℂ := Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℝ) : ℂ))) with hBm
  set C : ℂ := Complex.exp (2 * Real.pi * Complex.I *
    ((n : ℂ) * ((x : ℝ) : ℂ) + (n : ℂ) * ((n : ℂ) + 1) / 2 * (τ : ℂ))) with hC
  set Cm : ℂ := Complex.exp (-(2 * Real.pi * Complex.I *
    ((n : ℂ) * ((x : ℝ) : ℂ) + (n : ℂ) * ((n : ℂ) + 1) / 2 * (τ : ℂ)))) with hCm
  set E : ℂ := Complex.exp (2 * wordSfExpArg z τ M h0) with hE
  set P : ℂ := sfModularCocycleReal r M hM h0 τ *
    sfModularCocycleReal (-r) M (neg_mem_gammaSubgroup hM) h0 τ with hP
  have hinv : ∀ w : ℂ, Complex.exp (-w) * Complex.exp w = 1 := by
    intro w; rw [← Complex.exp_add]; simp
  have hAmA : Am * A = 1 := hinv _
  have hBmB : Bm * B = 1 := hinv _
  have hCmC : Cm * C = 1 := hinv _
  have hsq : ((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n) = 1 := by
    rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    exact Even.neg_one_zpow ⟨n, by ring⟩
  -- `1 - e(-w) = -e(-w)(1 - e(w))`, for the two reflected end factors.
  have hreflA : (1 : ℂ) - Am = -Am * (1 - A) := by
    rw [hAm, hA]; linear_combination -hinv (2 * Real.pi * Complex.I * ((z : ℝ) : ℂ))
  have hreflB : (1 : ℂ) - Bm = -Bm * (1 - B) := by
    rw [hBm, hB]; linear_combination -hinv (2 * Real.pi * Complex.I * ((x : ℝ) : ℂ))
  -- Lattice-freeness rules out both surviving factors.
  have hlatx : SigmaSLatticeFree (flt (M : Mat(2, ℤ)) τ) x :=
    hlat.div_fltDenominator hjac.ne'
  rw [hfix] at hlatx
  have hA1 : (1 : ℂ) - A ≠ 0 := by
    have h := hlat.one_sub_exp_ne_zero (j := 0)
    rw [hA]
    simpa using h
  have hB1 : (1 : ℂ) - B ≠ 0 := by
    have h := hlatx.one_sub_exp_ne_zero (j := 0)
    rw [hB]
    simpa using h
  -- The two end factors agree at a fixed point.
  obtain ⟨m, hm⟩ := div_fltDenominator_add_nQPInt_mul hM hfix hjac.ne'
  have hend : Complex.exp (2 * Real.pi * Complex.I *
      (((x : ℝ) : ℂ) + (n : ℂ) * (τ : ℂ))) = A := by
    have hmC : ((x : ℝ) : ℂ) + (n : ℂ) * (τ : ℂ) = ((z : ℝ) : ℂ) + (m : ℂ) := by
      rw [← hxdef, ← hn] at hm
      exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) hm
    rw [hmC, hA,
      show (2 : ℂ) * Real.pi * Complex.I * (((z : ℝ) : ℂ) + (m : ℂ)) =
        2 * Real.pi * Complex.I * ((z : ℝ) : ℂ) + (m : ℂ) * (2 * Real.pi * Complex.I) from by ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  -- The general reflection law, at this fixed point.
  have hbig := sfModularCocycleReal_mul_neg hτ hM h0 hjac hlat
  rw [← hz, ← hJdef, ← hn, hfix] at hbig
  rw [← hxdef, hend, ← hAm, ← hB, ← hBm, ← hC, ← hE] at hbig
  -- Cancel the two surviving factors, then unwind the inverses.
  have hcan : P * Am * ((-1 : ℂ) ^ n * C) = Bm * E := by
    refine mul_right_cancel₀ (mul_ne_zero hA1 hB1) ?_
    rw [hreflA, hreflB] at hbig
    linear_combination -hbig
  calc P = P * (Am * A) * (Cm * C) * (((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n)) := by
        rw [hAmA, hCmC, hsq]; ring
    _ = P * Am * ((-1 : ℂ) ^ n * C) * (A * Cm * (-1 : ℂ) ^ n) := by ring
    _ = Bm * E * (A * Cm * (-1 : ℂ) ^ n) := by rw [hcan]
    _ = (-1 : ℂ) ^ n * (A * Bm * Cm) * E := by ring

/-- **The reflected product at a fixed point has modulus one**: `|ש^r_M(τ)·ש^{-r}_M(τ)| = 1`
under the hypotheses of `sfModularCocycleReal_mul_neg_of_flt_eq_self`. Every factor of that
closed form is a sign or an exponential of a purely imaginary number, the last by
`SICs.Cocycle.Word.Reflection.norm_exp_two_wordSfExpArg_of_flt_eq_self`. This is the modulus
statement contained in [72, Kopp (2024), Theorem 4.36, `thm:shincharacter`], whose right-hand side
`ψ²(A)χ_r(A)` is a root of unity. -/
theorem norm_sfModularCocycleReal_mul_neg_of_flt_eq_self {r : Fin 2 → ℚ} {M : SL(2, ℤ)}
    {τ : ℝ} (hτ : Irrational τ) (hM : M ∈ gammaSubgroup r)
    (h0 : 0 ≤ M 1 0) (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) τ)
    (hfix : flt (M : Mat(2, ℤ)) τ = τ)
    (hlat : SigmaSLatticeFree τ (fracSymplecticFormRat r τ)) :
    ‖sfModularCocycleReal r M hM h0 τ *
        sfModularCocycleReal (-r) M (neg_mem_gammaSubgroup hM) h0 τ‖ = 1 := by
  have hphase : ∀ x : ℝ, ‖Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))‖ = 1 := by
    intro x
    rw [Complex.norm_exp]
    simp
  have hphase' : ∀ x : ℝ, ‖Complex.exp (-(2 * Real.pi * Complex.I * (x : ℂ)))‖ = 1 := by
    intro x
    rw [Complex.norm_exp]
    simp
  rw [sfModularCocycleReal_mul_neg_of_flt_eq_self hτ hM h0 hjac hfix hlat]
  simp only [norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul, hphase, hphase',
    norm_exp_two_wordSfExpArg_of_flt_eq_self hτ _ M h0 hjac hfix]
  -- The remaining factor is `exp(-(2πi·(real)))` with its real argument spelled out.
  rw [show (2 : ℂ) * Real.pi * Complex.I *
        ((nQPInt r (M : Mat(2, ℤ)) : ℂ) *
            ((fracSymplecticFormRat r τ /
              fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ) +
          (nQPInt r (M : Mat(2, ℤ)) : ℂ) *
            ((nQPInt r (M : Mat(2, ℤ)) : ℂ) + 1) / 2 * (τ : ℂ)) =
      2 * Real.pi * Complex.I *
        (((nQPInt r (M : Mat(2, ℤ)) : ℝ) *
            (fracSymplecticFormRat r τ /
              fltDenominator (M : Mat(2, ℤ)) τ) +
          (nQPInt r (M : Mat(2, ℤ)) : ℝ) *
            ((nQPInt r (M : Mat(2, ℤ)) : ℝ) + 1) / 2 * τ : ℝ) : ℂ) from by
      push_cast; ring,
    hphase']
  ring

end SIC

end
