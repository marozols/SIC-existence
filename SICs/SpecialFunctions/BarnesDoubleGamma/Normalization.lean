/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.BarnesDoubleGamma.Rows

/-!
# Cancellation of the Barnes double gamma normalization series

Cone rearrangement and cancellation of both normalization series.

This file follows [95, Shintani (1977), proof of Proposition 1 on pp. 172–173]. The punctured
cone is split into the positive real axis and the rows `m+n tau`, `n≥1`. The ordinary gamma
function evaluates each row. Subtracting the summable digamma and trigamma remainders leaves
a convergent product of the corrected gamma ratios

```text
Gamma(n tau)/Gamma(n tau+z) exp(z log(n tau)+(z²-z)/(2n tau)).
```

The two remainder sums cancel exactly against Shintani's coefficients `gamma₂₂` and `gamma₂₁`.
The resulting expression has only an explicit elementary exponential and the corrected gamma
product. This is the formula immediately preceding the difference-equation calculation on
p. 173, from which `SICs.SpecialFunctions.BarnesDoubleGamma.Difference` derives the period-one
equation.
Working with exponentials avoids introducing logarithm branches for gamma values;
all identities include the zeros of the reciprocal gamma factors.
-/

noncomputable section

open Complex Filter
open scoped Topology

namespace SIC

/-! ### Rearranging the cone by rows

The source's separation of the axial row is an explicit bijection of index sets. Absolute
convergence of the genus-two factors justifies the subsequent product over horizontal rows.
-/

/-- The bijection separating `(m+1,0)` from `(m,n+1)`, used to rearrange the Barnes product
in `barnesDoubleGammaInvFactor_tprod_eq_rows`. -/
private def barnesDoubleGammaRowsEquiv : ℕ ⊕ (ℕ × ℕ) ≃ BarnesDoubleGammaIndex where
  toFun
    | .inl m => ⟨(m + 1, 0), by simp⟩
    | .inr p => ⟨(p.2, p.1 + 1), by simp⟩
  invFun p := if p.1.2 = 0 then Sum.inl (p.1.1 - 1)
    else Sum.inr (p.1.2 - 1, p.1.1)
  left_inv := by
    rintro (m | ⟨n, m⟩) <;> simp
  right_inv := by
    intro p
    dsimp only
    split_ifs with hn
    · apply Subtype.ext
      apply Prod.ext
      · have hm : p.1.1 ≠ 0 := fun hm => p.2 (Prod.ext hm hn)
        exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm)
      · exact hn.symm
    · apply Subtype.ext
      change (p.1.1, p.1.2 - 1 + 1) = p.1
      exact Prod.ext rfl (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn))

/-- A positive horizontal row in the Barnes cone, used by the row rearrangement. -/
private def barnesDoubleGammaPositiveRow (p : ℕ × ℕ) : BarnesDoubleGammaIndex :=
  barnesDoubleGammaRowsEquiv (Sum.inr p)

/-- Positive row coordinates are injective, allowing restriction of the absolute convergence
estimate from the full cone. -/
private lemma barnesDoubleGammaPositiveRow_injective :
    Function.Injective barnesDoubleGammaPositiveRow :=
  barnesDoubleGammaRowsEquiv.injective.comp Sum.inr_injective

/-- A Barnes factor at the positive row coordinates is the ordinary genus-two factor. -/
private lemma barnesDoubleGammaInvFactor_positiveRow (z tau : ℂ) (p : ℕ × ℕ) :
    barnesDoubleGammaInvFactor z 1 tau (barnesDoubleGammaPositiveRow p) =
      barnesGenusTwoFactor (z / (((p.1 + 1 : ℕ) : ℂ) * tau + p.2)) := by
  rw [barnesDoubleGammaInvFactor_eq_genusTwoFactor]
  simp only [barnesDoubleGammaLatticePoint, barnesDoubleGammaPositiveRow,
    barnesDoubleGammaRowsEquiv, Equiv.coe_fn_mk, mul_one, add_comm (p.2 : ℂ)]

/-- The positive cone rows form a multipliable double family, by restriction of the absolute
convergence estimate. This justifies `barnesDoubleGammaGammaRows_hasProd`. -/
private lemma multipliable_barnesDoubleGammaPositiveRows (z tau : ℂ)
    (htau : tau ∈ Complex.slitPlane) :
    Multipliable (fun p : ℕ × ℕ =>
      barnesDoubleGammaInvFactor z 1 tau (barnesDoubleGammaPositiveRow p)) := by
  have hs :=
    (summable_norm_barnesDoubleGammaInvFactor_sub_one z tau htau).comp_injective
      barnesDoubleGammaPositiveRow_injective
  simpa using multipliable_one_add_of_summable hs

/-- Evaluating the positive cone rows by `barnesGenusTwoFactor_hasProd_gamma` preserves
their double product. This supplies both the rearrangement and the correction calculation. -/
private lemma barnesDoubleGammaGammaRows_hasProd (z tau : ℂ) (htau : tau ∈ Complex.slitPlane) :
    HasProd (fun n : ℕ =>
      Complex.Gamma (((n + 1 : ℕ) : ℂ) * tau) /
          Complex.Gamma (((n + 1 : ℕ) : ℂ) * tau + z) *
        Complex.exp (z * Complex.digamma (((n + 1 : ℕ) : ℂ) * tau) +
          z ^ 2 / 2 * deriv Complex.digamma (((n + 1 : ℕ) : ℂ) * tau)))
      (∏' p : ℕ × ℕ, barnesDoubleGammaInvFactor z 1 tau (barnesDoubleGammaPositiveRow p)) := by
  apply (multipliable_barnesDoubleGammaPositiveRows z tau htau).hasProd.prod_fiberwise
  intro n
  simpa only [barnesDoubleGammaInvFactor_positiveRow] using
    barnesGenusTwoFactor_hasProd_gamma (((n + 1 : ℕ) : ℂ) * tau) z (by
      rcases htau with h | h
      · left
        simpa using mul_pos (show (0 : ℝ) < n + 1 by positivity) h
      · right
        simpa using mul_ne_zero (show (n : ℝ) + 1 ≠ 0 by positivity) h)

/-- The Barnes cone product is the axial row times the gamma-evaluated positive rows.
This is the exponential form of the first displayed rearrangement in
[95, Shintani (1977), proof of Proposition 1 on p. 173]. -/
lemma barnesDoubleGammaInvFactor_tprod_eq_rows (z tau : ℂ) (htau : tau ∈ Complex.slitPlane) :
    (∏' p : BarnesDoubleGammaIndex, barnesDoubleGammaInvFactor z 1 tau p) =
      ((Complex.Gamma (1 + z))⁻¹ * Complex.exp
        (-(Real.eulerMascheroniConstant : ℂ) * z + (Real.pi : ℂ) ^ 2 * z ^ 2 / 12)) *
      ∏' n : ℕ,
        Complex.Gamma (((n + 1 : ℕ) : ℂ) * tau) /
            Complex.Gamma (((n + 1 : ℕ) : ℂ) * tau + z) *
          Complex.exp (z * Complex.digamma (((n + 1 : ℕ) : ℂ) * tau) +
            z ^ 2 / 2 * deriv Complex.digamma (((n + 1 : ℕ) : ℂ) * tau)) := by
  have hp := multipliable_barnesDoubleGammaPositiveRows z tau htau
  have hrows := barnesDoubleGammaGammaRows_hasProd z tau htau
  let f := fun p => barnesDoubleGammaInvFactor z 1 tau (barnesDoubleGammaRowsEquiv p)
  have haxis : HasProd (f ∘ Sum.inl) _ :=
    (barnesGenusTwoFactor_hasProd_axis z).congr_fun fun m => by
      dsimp only [f, Function.comp_apply]
      rw [barnesDoubleGammaInvFactor_eq_genusTwoFactor]
      simp only [barnesDoubleGammaLatticePoint, barnesDoubleGammaRowsEquiv, Equiv.coe_fn_mk,
        Nat.cast_add, Nat.cast_one, Nat.cast_zero, mul_one, zero_mul, add_zero, add_comm (m : ℂ)]
  have hprod : HasProd f _ := HasProd.sum (f := f) haxis hp.hasProd
  have hfull := (barnesDoubleGammaRowsEquiv.hasProd_iff
    (f := fun p => barnesDoubleGammaInvFactor z 1 tau p)).mp hprod
  exact hfull.tprod_eq.trans (congrArg (_ * ·) hrows.tprod_eq.symm)

/-! ### The convergent corrected gamma product

The two digamma remainders are absolutely summable. Removing their exponentials from the
evaluated horizontal rows gives the gamma-ratio product appearing on p. 173 of the source.
-/

/-- The corrected gamma ratio

```text
R_n(z,tau) = Gamma((n+1)tau)/Gamma((n+1)tau+z)
             exp(z log((n+1)tau)+(z²-z)/(2(n+1)tau)).
```

This is the exponential of the summand remaining after normalization cancellation in
[95, Shintani (1977), proof of Proposition 1 on p. 173], for periods `(1,tau)`. -/
def barnesDoubleGammaNormalizedRow (z tau : ℂ) (n : ℕ) : ℂ :=
  Complex.Gamma (((n + 1 : ℕ) : ℂ) * tau) /
      Complex.Gamma (((n + 1 : ℕ) : ℂ) * tau + z) *
    Complex.exp (z * Complex.log (((n + 1 : ℕ) : ℂ) * tau) +
      (z ^ 2 - z) / (2 * ((n + 1 : ℕ) : ℂ) * tau))

/-- The sum of the two normalization corrections for one horizontal row, used to pass from
`barnesGenusTwoFactor_hasProd_gamma` to `barnesDoubleGammaNormalizedRow`. -/
private def barnesDoubleGammaRowCorrection (z tau : ℂ) (n : ℕ) : ℂ :=
  z * (Complex.digamma (((n + 1 : ℕ) : ℂ) * tau) -
      Complex.log (((n + 1 : ℕ) : ℂ) * tau) +
      1 / (2 * ((n + 1 : ℕ) : ℂ) * tau)) +
    z ^ 2 / 2 * (deriv Complex.digamma (((n + 1 : ℕ) : ℂ) * tau) -
      1 / (((n + 1 : ℕ) : ℂ) * tau))

/-- The two absolutely convergent Barnes normalization series give absolute convergence of
the row correction used by `multipliable_barnesDoubleGammaNormalizedRow`. -/
private lemma summable_barnesDoubleGammaRowCorrection (z tau : ℂ)
    (htau : tau ∈ Complex.slitPlane) : Summable (barnesDoubleGammaRowCorrection z tau) := by
  have hratio : tau / 1 ∈ Complex.slitPlane := by
    rw [div_one]
    exact htau
  have h22 := (summable_barnesGamma22Series 1 tau hratio).mul_left z
  have h21 := (summable_barnesGamma21Series 1 tau hratio).mul_left (z ^ 2 / 2)
  unfold barnesDoubleGammaRowCorrection
  simpa only [div_one] using h22.add h21

/-- Separating the summable digamma remainders from the exact gamma row gives the corrected
ratio `barnesDoubleGammaNormalizedRow`. -/
private lemma barnesDoubleGammaGammaRow_eq_normalized (z tau : ℂ) (n : ℕ) :
    Complex.Gamma (((n + 1 : ℕ) : ℂ) * tau) /
        Complex.Gamma (((n + 1 : ℕ) : ℂ) * tau + z) *
      Complex.exp (z * Complex.digamma (((n + 1 : ℕ) : ℂ) * tau) +
        z ^ 2 / 2 * deriv Complex.digamma (((n + 1 : ℕ) : ℂ) * tau)) =
      barnesDoubleGammaNormalizedRow z tau n *
        Complex.exp (barnesDoubleGammaRowCorrection z tau n) := by
  unfold barnesDoubleGammaNormalizedRow barnesDoubleGammaRowCorrection
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Removing the summable row correction preserves convergence and gives the exact product
value used by `barnesDoubleGammaInv_eq_normalizedRow_tprod`. -/
private lemma barnesDoubleGammaNormalizedRow_hasProd (z tau : ℂ) (htau : tau ∈ Complex.slitPlane) :
    HasProd (barnesDoubleGammaNormalizedRow z tau)
      ((∏' n : ℕ,
        Complex.Gamma (((n + 1 : ℕ) : ℂ) * tau) /
            Complex.Gamma (((n + 1 : ℕ) : ℂ) * tau + z) *
          Complex.exp (z * Complex.digamma (((n + 1 : ℕ) : ℂ) * tau) +
            z ^ 2 / 2 * deriv Complex.digamma (((n + 1 : ℕ) : ℂ) * tau))) *
        Complex.exp (-(∑' n, barnesDoubleGammaRowCorrection z tau n))) := by
  have hraw := (barnesDoubleGammaGammaRows_hasProd z tau htau).multipliable.hasProd
  have hcor := (summable_barnesDoubleGammaRowCorrection z tau htau).hasSum.neg.cexp
  apply (hraw.mul hcor).congr_fun
  intro n
  rw [barnesDoubleGammaGammaRow_eq_normalized, mul_assoc]
  simp only [Function.comp_apply, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]

/-- The corrected gamma rows `R_n(z,tau)` have a convergent product for `tau∈ℂ \ (-∞,0]`.
This is the convergence of the residual product in
`barnesDoubleGammaInv_eq_normalizedRow_tprod`, including its zero cases. -/
lemma multipliable_barnesDoubleGammaNormalizedRow (z tau : ℂ) (htau : tau ∈ Complex.slitPlane) :
    Multipliable (barnesDoubleGammaNormalizedRow z tau) :=
  (barnesDoubleGammaNormalizedRow_hasProd z tau htau).multipliable

/-- The normalization coefficients cancel exactly against the summed digamma corrections.
This is the elementary exponential calculation used by
`barnesDoubleGammaInv_eq_normalizedRow_tprod`. -/
private lemma barnesDoubleGamma_normalization_cancellation (z tau : ℂ)
    (htau : tau ∈ Complex.slitPlane) :
    barnesGamma22 1 tau * z + z ^ 2 / 2 * barnesGamma21 1 tau -
        (Real.eulerMascheroniConstant : ℂ) * z + (Real.pi : ℂ) ^ 2 * z ^ 2 / 12 +
        ∑' n, barnesDoubleGammaRowCorrection z tau n =
      (z ^ 2 - z) * (Complex.log tau - (Real.eulerMascheroniConstant : ℂ)) / (2 * tau) +
        z * (Complex.log tau - (Real.log (2 * Real.pi) : ℂ)) / 2 := by
  have hratio : tau / 1 ∈ Complex.slitPlane := by
    rw [div_one]
    exact htau
  have h22 := summable_barnesGamma22Series 1 tau hratio
  have h21 := summable_barnesGamma21Series 1 tau hratio
  simp only [div_one] at h22 h21
  simp only [barnesDoubleGammaRowCorrection]
  rw [(h22.mul_left z).tsum_add (h21.mul_left (z ^ 2 / 2)), tsum_mul_left, tsum_mul_left]
  simp only [barnesGamma22, barnesGamma21, inv_one, Complex.log_one, mul_zero, zero_div,
    add_zero, div_one, one_pow, mul_one, one_mul]
  generalize (∑' n : ℕ, (Complex.digamma (((n + 1 : ℕ) : ℂ) * tau) -
    Complex.log (((n + 1 : ℕ) : ℂ) * tau) + 1 / (2 * ((n + 1 : ℕ) : ℂ) * tau))) = A
  generalize (∑' n : ℕ, (deriv Complex.digamma (((n + 1 : ℕ) : ℂ) * tau) -
    1 / (((n + 1 : ℕ) : ℂ) * tau))) = B
  have htau0 : tau ≠ 0 := Complex.slitPlane_ne_zero htau
  field_simp [htau0]
  ring

/-- Shintani's normalized gamma-product expression

```text
Gamma₂(z;1,tau)⁻¹ = Gamma(z)⁻¹
  exp((z²-z)(log(tau)-gamma)/(2tau) + z(log(tau)-log(2pi))/2)
  ∏_{n≥1} Gamma(n tau)/Gamma(n tau+z) exp(z log(n tau)+(z²-z)/(2n tau)).
```

This is the exponential form of the second displayed formula in
[95, Shintani (1977), proof of Proposition 1 on p. 173], for periods `(1,tau)`; the
extension to nonreal period ratios is stated in paragraph 1.6 on p. 181. The row product
converges by `multipliable_barnesDoubleGammaNormalizedRow`. Every factor is interpreted
through reciprocal gamma at its zeros, so the identity holds for all `z`. -/
theorem barnesDoubleGammaInv_eq_normalizedRow_tprod (z tau : ℂ) (htau : tau ∈ Complex.slitPlane) :
    barnesDoubleGammaInv z 1 tau = (Complex.Gamma z)⁻¹ *
      Complex.exp ((z ^ 2 - z) * (Complex.log tau - (Real.eulerMascheroniConstant : ℂ)) /
        (2 * tau) + z * (Complex.log tau - (Real.log (2 * Real.pi) : ℂ)) / 2) *
      ∏' n, barnesDoubleGammaNormalizedRow z tau n := by
  have hprod := (barnesDoubleGammaNormalizedRow_hasProd z tau htau).tprod_eq
  have hraw := congrArg (· * Complex.exp (∑' n, barnesDoubleGammaRowCorrection z tau n))
    hprod
  rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one] at hraw
  rw [barnesDoubleGammaInv, barnesDoubleGammaInvFactor_tprod_eq_rows z tau htau, ← hraw]
  rw [Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one z, add_comm z 1,
    ← barnesDoubleGamma_normalization_cancellation z tau htau]
  simp only [neg_mul, Complex.exp_add, Complex.exp_sub, Complex.exp_neg]
  ring

end SIC

end
