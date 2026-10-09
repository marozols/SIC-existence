/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Cocycle.Domains
import SICs.Cocycle.Modular.Values
import SICs.Cocycle.Word.Shifts

/-!
# Integral translations of a modular characteristic

Integral translations of modular characteristics for either matrix orientation.

This file proves [AFK25, Lemma 2.14, `lm:shinperiodicity`] for real word values.
The word's lattice-shift formula and the finite q-Pochhammer shift law cancel the
extra factors. Irrationality and a nonintegral characteristic give the needed
nonvanishing; the inverse-orientation API transports the law to either matrix orientation.
-/

noncomputable section

open ModularGroup MatrixGroups

open scoped MatrixGroups

namespace SIC

/-! ### `ℤ²`-periodicity in the rational index

Changing `r` by an integral vector shifts the Jacobi argument along its period lattice.  The
word-level lattice law cancels the induced finite-product correction, proving the periodicity of
[AFK25, Lemma 2.14, `lm:shinperiodicity`] directly on the real line. -/

/-! [72, Kopp (2024), Proposition 4.35, `prop:invariance`] is sharper: at an integral index the
cocycle picks up `j_M(ξ)^{±1}` only when `r₂` and `r₂ + s₂` lie on opposite sides of `0`
(`j_M(ξ)` if `r₂ ≤ 0 < r₂+s₂`, its inverse if `r₂+s₂ ≤ 0 < r₂`), and is unchanged otherwise. That
refinement uses the regularized integral correction in `SICs.Cocycle.Modular.Values`.
The raw finite-product cancellation below applies to nonintegral indices: at an integral index,
`⟨⟨r,τ⟩⟩` lies on `ℤτ + ℤ` and factors can vanish. The integral construction cancels those
factors before evaluation and starts from the zero word value supplied by
`SICs.Cocycle.SigmaS.Reduction.sigmaSHonest_zero`. Its sign-dependent fixed-point values are
proved in `SICs.Cocycle.FixedPointCharacter.sfModularCocycleRealTotal_integral_of_flt_eq_self`. -/

/-- The shape of the final cancellation: two quotients agree once the numerators and the
denominators are related by a common pair of nonzero correction factors. Split off because the
`H = 0` branch (where `K = 0` too, and both sides are Lean's `x / 0 = 0`) is pure bookkeeping that
would obscure the cocycle argument. -/
private lemma div_eq_div_of_mul_eq_mul {P Q G H K L : ℂ} (hG : G ≠ 0) (hL : L ≠ 0)
    (h1 : P * G = Q * L) (h2 : G * H = K * L) : P / H = Q / K := by
  rcases eq_or_ne H 0 with hH | hH
  · have hK : K = 0 := by
      have hKL : K * L = 0 := by rw [← h2, hH, mul_zero]
      exact (mul_eq_zero.mp hKL).resolve_right hL
    rw [hH, hK, div_zero, div_zero]
  · have hK : K ≠ 0 := fun hK => hH (by
      have hGH : G * H = 0 := by rw [h2, hK, zero_mul]
      exact (mul_eq_zero.mp hGH).resolve_left hG)
    rw [div_eq_div_iff hH hK]
    refine mul_right_cancel₀ (mul_ne_zero hG hL) ?_
    linear_combination (K * L) * h1 - (Q * L) * h2

/-- **`ℤ²`-periodicity of the Shintani--Faddeev modular cocycle in its rational index**,
[AFK25, Lemma 2.14, `lm:shinperiodicity`]
(= [72, Kopp (2024), Proposition 4.35, `prop:invariance`]) on the real line:
```
ש^{r+s}_M(ξ) = ש^r_M(ξ)      for every s ∈ ℤ²,
```
at a fixed point `ξ` of `M` lying in `D_M`, and for `r ∈ ℚ² \ ℤ²`.

**This is not the source's proof.** [72, Kopp (2024), Proposition 4.35, `prop:invariance`]
compares two infinite products through the coboundary expression
[AFK25, equation (1.27), `eq:coboundary`], which AFK25 says explicitly "does not make sense
outside the upper half plane", and then continues analytically. Here three real-domain
identities prove the same conclusion:

- `SICs.Cocycle.Word.Shifts.wordSigmaS_lattice_shift`: the numerator `σ_M` picks up
  `ϖ_a(⟨⟨r,ξ⟩⟩,ξ) / ϖ_{m₁}(⟨⟨r,ξ⟩⟩/j_M(ξ), M·ξ)`, with `m₁ = a·M₁₁ - b·M₁₀`;
- `nQPInt_add_intVec`: the denominator's index moves by `n_QP(s,M)`, and `m₁ + n_QP(s,M) = s₁`
  exactly — which is why the two corrections can cancel at all;
- `exists_fracSymplecticFormRat_div_fltDenominator`: at the fixed point the denominator's
  argument is `⟨⟨r,ξ⟩⟩` shifted by `ℤ`, so the leftover factor is literally `ϖ_a(⟨⟨r,ξ⟩⟩,ξ)`.

`hr` is the source's `r ∉ ℤ²`, and `hdom` its `ξ ∈ D_M`; `hτ` is the
irrationality hypothesis on the real quadratic point. See the section discussion above for why `hr`
cannot
simply be weakened to [72, Kopp (2024), Proposition 4.35, `prop:invariance`]'s sharper condition.
The condition `h0 : 0 ≤ M 1 0` is `sfModularCocycleReal`'s own word-decomposition restriction, not
an extra assumption of this lemma. -/
@[source "AFK25, Lemma 2.14, p. 32, lm:shinperiodicity"
  "72, Proposition 4.35, p. 46, prop:invariance"]
theorem sfModularCocycleReal_add_intVec (r : Fin 2 → ℚ) (s : Fin 2 → ℤ) (M : SL(2, ℤ))
    (hM : M ∈ gammaSubgroup r) (h0 : 0 ≤ M 1 0) {τ : ℝ}
    (hτ : Irrational τ) (hr : ¬ IsIntegralIndex r)
    (hdom : ((τ : ℝ) : ℂ) ∈ sfDomain (M : Mat(2, ℤ)))
    (hfix : flt (M : Mat(2, ℤ)) τ = τ) :
    sfModularCocycleReal (r + fun i => (s i : ℚ)) M (add_intVec_mem_gammaSubgroup hM s) h0 τ =
      sfModularCocycleReal r M hM h0 τ := by
  have hjac : 0 < fltDenominator (M : Mat(2, ℤ)) τ :=
    (mem_sfDomain_ofReal_iff M τ).mp hdom
  have hJ0 : fltDenominator (M : Mat(2, ℤ)) τ ≠ 0 := hjac.ne'
  have hlat : SigmaSLatticeFree τ (fracSymplecticFormRat r τ) :=
    sigmaSLatticeFree_fracSymplecticFormRat hτ hr
  obtain ⟨a, ha⟩ : ∃ a : ℤ, a = s 1 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℤ, b = -(s 0) := ⟨_, rfl⟩
  -- The index shift, and the cancellation that drives the whole proof.
  have hn' : nQPInt (r + fun i => (s i : ℚ)) (M : Mat(2, ℤ)) =
      nQPInt r (M : Mat(2, ℤ)) +
        (-(M 1 0) * s 0 + (1 - M 1 1) * s 1) := nQPInt_add_intVec hM s
  have hcancel : (a * M 1 1 - b * M 1 0) +
      (nQPInt r (M : Mat(2, ℤ)) + (-(M 1 0) * s 0 + (1 - M 1 1) * s 1)) =
      nQPInt r (M : Mat(2, ℤ)) + a := by
    rw [ha, hb]; ring
  have hz' : fracSymplecticFormRat (r + fun i => (s i : ℚ)) τ =
      fracSymplecticFormRat r τ + (a : ℝ) * τ + (b : ℝ) := by
    simp only [fracSymplecticFormRat, Pi.add_apply]
    rw [ha, hb]
    push_cast
    ring
  -- Lattice-freeness, transported to the rescaled argument (the period is `τ` itself, by `hfix`).
  have hlatx : SigmaSLatticeFree τ
      (fracSymplecticFormRat r τ /
        fltDenominator (M : Mat(2, ℤ)) τ) := by
    have h := hlat.div_fltDenominator (N := (M : Mat(2, ℤ))) hJ0
    rwa [hfix] at h
  have hlatx' : SigmaSLatticeFree τ
      ((fracSymplecticFormRat r τ + (a : ℝ) * τ + (b : ℝ)) /
        fltDenominator (M : Mat(2, ℤ)) τ) := by
    have h := (hlat.add a b).div_fltDenominator (N := (M : Mat(2, ℤ))) hJ0
    rwa [hfix] at h
  have hfacx : ∀ j : ℤ, (1 : ℂ) - Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
      (((fracSymplecticFormRat r τ : ℝ) : ℂ) /
        ((fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ) +
          (j : ℂ) * (τ : ℂ))) ≠ 0 := by
    intro j
    have h := hlatx.one_sub_exp_ne_zero j
    rwa [show ((fracSymplecticFormRat r τ /
        fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ) =
      ((fracSymplecticFormRat r τ : ℝ) : ℂ) /
        ((fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ) from by
      push_cast; ring] at h
  have hfacx' : ∀ j : ℤ, (1 : ℂ) - Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
      (((fracSymplecticFormRat r τ + (a : ℝ) * τ + (b : ℝ) : ℝ) : ℂ) /
        ((fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ) +
          (j : ℂ) * (τ : ℂ))) ≠ 0 := by
    intro j
    have h := hlatx'.one_sub_exp_ne_zero j
    rwa [show (((fracSymplecticFormRat r τ + (a : ℝ) * τ + (b : ℝ)) /
        fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ) =
      ((fracSymplecticFormRat r τ + (a : ℝ) * τ + (b : ℝ) : ℝ) : ℂ) /
        ((fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ) from by
      push_cast; ring] at h
  -- The numerator's shift law.
  have hshift := wordSigmaS_lattice_shift hτ (fracSymplecticFormRat r τ) a b hlat M h0 hjac
  rw [hfix] at hshift
  -- The denominator's index arithmetic.
  obtain ⟨c, hc⟩ := exists_fracSymplecticFormRat_div_fltDenominator hM hJ0 hfix
  have hcC : ((fracSymplecticFormRat r τ : ℝ) : ℂ) /
        ((fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ) +
        ((nQPInt r (M : Mat(2, ℤ)) : ℤ) : ℂ) * (τ : ℂ) =
      ((fracSymplecticFormRat r τ : ℝ) : ℂ) + (c : ℂ) := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) hc
    push_cast at h ⊢
    linear_combination h
  have hargC : ((fracSymplecticFormRat r τ + (a : ℝ) * τ + (b : ℝ) : ℝ) : ℂ) /
        ((fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ) =
      ((fracSymplecticFormRat r τ : ℝ) : ℂ) /
          ((fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ) +
        ((a * M 1 1 - b * M 1 0 : ℤ) : ℂ) * (τ : ℂ) +
        ((-(a * M 0 1) + b * M 0 0 : ℤ) : ℂ) := by
    have h := div_fltDenominator_add_lattice M τ
      (fracSymplecticFormRat r τ) a b hJ0
    rw [hfix] at h
    have h' := congrArg (fun x : ℝ => (x : ℂ)) h
    push_cast at h' ⊢
    linear_combination h'
  have hdenrel :
      qPochhammerFin (a * M 1 1 - b * M 1 0)
          (((fracSymplecticFormRat r τ : ℝ) : ℂ) /
            ((fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ)) (τ : ℂ) *
        qPochhammerFin (nQPInt r (M : Mat(2, ℤ)) +
            (-(M 1 0) * s 0 + (1 - M 1 1) * s 1))
          (((fracSymplecticFormRat r τ + (a : ℝ) * τ + (b : ℝ) : ℝ) : ℂ) /
            ((fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ)) (τ : ℂ) =
      qPochhammerFin (nQPInt r (M : Mat(2, ℤ)))
          (((fracSymplecticFormRat r τ : ℝ) : ℂ) /
            ((fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ)) (τ : ℂ) *
        qPochhammerFin a ((fracSymplecticFormRat r τ : ℝ) : ℂ) (τ : ℂ) := by
    rw [hargC, qPochhammerFin_add_intCast, ← qPochhammerFin_add _ _ _ _ hfacx, hcancel,
      qPochhammerFin_add _ _ _ _ hfacx, hcC, qPochhammerFin_add_intCast]
  -- Assemble.
  have hr' : ¬ IsIntegralIndex (r + fun i => (s i : ℚ)) := by
    intro h
    apply hr
    simpa only [add_sub_cancel_right] using
      isIntegralIndex_sub h (show IsIntegralIndex (fun i => (s i : ℚ)) from fun i => ⟨s i, rfl⟩)
  rw [sfModularCocycleReal_eq_of_not_isIntegralIndex hr',
    sfModularCocycleReal_eq_of_not_isIntegralIndex hr]
  rw [hz', hn', hfix]
  exact div_eq_div_of_mul_eq_mul
    (qPochhammerFin_ne_zero_of_forall_factor_ne_zero _ _ _ hfacx)
    (qPochhammerFin_ne_zero_of_forall_factor_ne_zero _ _ _ hlat.one_sub_exp_ne_zero)
    hshift hdenrel


/-- **`ℤ²`-periodicity, as a congruence.** The form consumers use: two indices differing by an
integer vector give the same value, with no need to exhibit the shift. `hr` is stated for `r`,
but by `sfModularCocycleReal_add_intVec`'s conclusion it could equally be stated for `r'`. -/
theorem sfModularCocycleReal_congr_of_sub_intVec (r r' : Fin 2 → ℚ) (M : SL(2, ℤ))
    (hM : M ∈ gammaSubgroup r)
    (hM' : M ∈ gammaSubgroup r') (h0 : 0 ≤ M 1 0) {τ : ℝ}
    (hτ : Irrational τ) (hr : ¬ IsIntegralIndex r)
    (hdom : ((τ : ℝ) : ℂ) ∈ sfDomain (M : Mat(2, ℤ)))
    (hfix : flt (M : Mat(2, ℤ)) τ = τ)
    (hdiff : ∀ i, ∃ m : ℤ, r' i - r i = (m : ℚ)) :
    sfModularCocycleReal r' M hM' h0 τ = sfModularCocycleReal r M hM h0 τ := by
  choose s hs using hdiff
  have hs' : r' = r + fun i => (s i : ℚ) := by
    funext i
    have h := hs i
    simp only [Pi.add_apply]
    linarith
  subst hs'
  exact sfModularCocycleReal_add_intVec r s M hM h0 hτ hr hdom hfix

/-! #### Orientation-independent total value

The word theorem above assumes a nonnegative lower-left entry. For `M₁₀ < 0`, the total cocycle is
the reciprocal word value at `M⁻¹`; applying the theorem there and then inverting gives the same
index-periodicity law. The hypotheses include both domains so that either orientation is
available. Associated stabilizers supply them simultaneously by [AFK25, Theorem 1.31,
`thm:ghostWellDefinedCondition`]. The condition `M₁₀ ≠ 0` excludes the triangular case, where the
reciprocal branch identity does not apply. -/

/-- **`ℤ²`-periodicity for the orientation-independent real cocycle.** At an irrational fixed
point `ξ ∈ D_M ∩ D_{M⁻¹}`, characteristics with `r' - r ∈ ℤ²` have equal total values. This is the
total-value lift of `sfModularCocycleReal_congr_of_sub_intVec`. -/
theorem sfModularCocycleRealTotal_congr_of_sub_intVec
    (r r' : Fin 2 → ℚ) (M : SL(2, ℤ))
    (hM : M ∈ gammaSubgroup r)
    (hM' : M ∈ gammaSubgroup r') {τ : ℝ}
    (hτ : Irrational τ) (hr : ¬ IsIntegralIndex r)
    (hdom : ((τ : ℝ) : ℂ) ∈ sfDomain (M : Mat(2, ℤ)))
    (hdomInv : ((τ : ℝ) : ℂ) ∈
      sfDomain ((M⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)))
    (hfix : flt (M : Mat(2, ℤ)) τ = τ)
    (hlower : M 1 0 ≠ 0)
    (hdiff : ∀ i, ∃ m : ℤ, r' i - r i = (m : ℚ)) :
    sfModularCocycleRealTotal r' M hM' τ =
      sfModularCocycleRealTotal r M hM τ := by
  rcases lt_or_gt_of_ne hlower with hneg | hpos
  · have hposInv : 0 ≤ (M⁻¹ : SL(2, ℤ)) 1 0 := by
      rw [SL2Z.lowerLeft_inv]
      omega
    have hfixInv :
        flt ((M⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) τ = τ :=
      flt_inv_of_flt_eq_self
        ((mem_sfDomain_ofReal_iff M τ).mp hdom).ne' hfix
    have hword := sfModularCocycleReal_congr_of_sub_intVec r r' M⁻¹
      (inv_mem_gammaSubgroup hM) (inv_mem_gammaSubgroup hM') hposInv hτ hr
      hdomInv hfixInv hdiff
    rw [sfModularCocycleRealTotal, dite_eq_right (by omega),
      sfModularCocycleRealTotal, dite_eq_right (by omega), hfix]
    exact congrArg Inv.inv hword
  · rw [sfModularCocycleRealTotal_of_nonneg hM' hpos.le,
      sfModularCocycleRealTotal_of_nonneg hM hpos.le]
    exact sfModularCocycleReal_congr_of_sub_intVec r r' M hM hM' hpos.le hτ hr
      hdom hfix hdiff

end SIC

end
