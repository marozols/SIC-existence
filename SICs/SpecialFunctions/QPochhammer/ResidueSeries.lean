/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.QPochhammer.Binomial
import SICs.SpecialFunctions.QPochhammer.Divisor
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# The q-product residue series

Absolute convergence and evaluation of the two-index q-product residue series.

This module follows the residue summation in [RW26, Radchenko, Wheeler (2026),
Appendix A.2, `app:mod.fad`]. After the congruence classes have been summed, the
pole coefficients separate into a forward q-binomial series and an inverse-base
q-binomial series. The parameters are `a=pτ+y`, `b=y/ε`, `u=ℓτ+w`,
`v=w/ε-hσ`, with `σ=γτ` and `ε=cτ+d` in the source; the summation itself
does not require a relation between the two upper-half-plane periods.

## The argument

Splitting the infinite products at their lattice shifts writes each coefficient
as a constant times two finite-product ratios. The forward ratio is summed by
the q-binomial theorem at `(a,u,τ)`. Finite base inversion turns the backward
ratio into a forward one at `(σ-b,b+v,σ)`. The convergence conditions are
`Im u > 0` and `Im(b+v) > 0`. Absolute convergence permits multiplication of
the two sums over `ℕ × ℕ`; restoring the constant gives the source's product
expression, with its exact q-product normalization.

This is the series part of the residue argument. Identifying the contour integral
with this sum still requires a contour deformation, bounds on the closing paths,
and the indexing of the poles. The real-period identity also requires a boundary
limit; none of those assertions follows from the summation alone.
-/

noncomputable section

open Complex Real

namespace SIC

/-! ### Summing the pole coefficients

The forward and backward lattice shifts supply the two finite-product ratios.
Their absolutely convergent sums can then be multiplied and rescaled.
-/

/-- The forward infinite-product quotient is the finite q-binomial coefficient
times `ϖ(τ,τ)/ϖ(a,τ)`; used by `hasSum_qPochhammer_residue_series`.
The splitting is that of [RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`]. -/
private lemma qPochhammer_residue_forward_coefficient (a τ : ℂ)
    (hτ : 0 < τ.im) (ha : qPochhammer a τ ≠ 0) (n : ℕ) :
    qPochhammer (((n : ℂ) + 1) * τ) τ /
      qPochhammer (a + (n : ℂ) * τ) τ =
    (qPochhammer τ τ / qPochhammer a τ) *
      (qPochhammerFin (n : ℤ) a τ / qPochhammerFin (n : ℤ) τ τ) := by
  have hτsplit := qPochhammerFin_natCast_mul_qPochhammer_add n τ τ hτ
  have hasplit := qPochhammerFin_natCast_mul_qPochhammer_add n a τ hτ
  have harg : τ + (n : ℂ) * τ = ((n : ℂ) + 1) * τ := by ring
  rw [harg] at hτsplit
  have hτprod : qPochhammerFin (n : ℤ) τ τ *
      qPochhammer (((n : ℂ) + 1) * τ) τ ≠ 0 := by rw [hτsplit]; exact qPochhammer_tau_ne_zero τ hτ
  have hfinτ := (mul_ne_zero_iff.mp hτprod).1
  have hshiftA : qPochhammer (a + (n : ℂ) * τ) τ ≠ 0 :=
    qPochhammer_add_natCast_mul_ne_zero n a τ hτ ha
  field_simp [ha, hfinτ, hshiftA]
  rw [← hτsplit, ← hasplit]
  ring

/-- The backward infinite product splits into its first `m` factors and
`ϖ(b,σ)`; used by `hasSum_qPochhammer_residue_series`.
See [RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`]. -/
private lemma qPochhammer_residue_backward_coefficient (b σ : ℂ)
    (hσ : 0 < σ.im) (m : ℕ) :
    qPochhammer (b - (m : ℂ) * σ) σ /
      (qPochhammerFin (m : ℤ) (-(m : ℂ) * σ) σ * qPochhammer σ σ) =
    (qPochhammer b σ / qPochhammer σ σ) *
      (qPochhammerFin (m : ℤ) (b - (m : ℂ) * σ) σ /
        qPochhammerFin (m : ℤ) (-(m : ℂ) * σ) σ) := by
  have hsplit := qPochhammerFin_natCast_mul_qPochhammer_add
    m (b - (m : ℂ) * σ) σ hσ
  have harg : b - (m : ℂ) * σ + (m : ℂ) * σ = b := by ring
  rw [harg] at hsplit
  rw [← hsplit]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Splits the character of the two-index residue coefficient into its
forward and backward factors; used by `hasSum_qPochhammer_residue_series`. -/
private lemma qPochhammer_residue_exp_add (n m : ℕ) (u v : ℂ) :
    Complex.exp (2 * π * I * ((n : ℂ) * u + (m : ℂ) * v)) =
    Complex.exp (2 * π * I * u) ^ n * Complex.exp (2 * π * I * v) ^ m := by
  rw [show 2 * π * I * ((n : ℂ) * u + (m : ℂ) * v) =
      (n : ℂ) * (2 * π * I * u) + (m : ℂ) * (2 * π * I * v) by ring,
    Complex.exp_add, Complex.exp_nat_mul, Complex.exp_nat_mul]

/-- The two-index residue series of
[RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`], after the
congruence classes have been summed. The direct q-series has `Im u > 0` and
the inverse-base series has `Im(b+v) > 0`; their product converges absolutely.
Here `a=pτ+y`, `b=y/ε`, `u=ℓτ+w`, `v=w/ε-hσ`, and `σ=γτ` in the source.
The factor `ε` includes the contour orientation and the residue scale. This is a
series evaluation, with no assertion that a contour integral equals this series. -/
theorem hasSum_qPochhammer_residue_series (a b u v τ σ ε : ℂ)
    (hτ : 0 < τ.im) (hσ : 0 < σ.im) (hu : 0 < u.im) (hbv : 0 < (b + v).im)
    (ha : qPochhammer a τ ≠ 0) :
    HasSum (fun nk : ℕ × ℕ =>
      ε * (qPochhammer (((nk.1 : ℂ) + 1) * τ) τ /
        qPochhammer (a + (nk.1 : ℂ) * τ) τ) *
        (qPochhammer (b - (nk.2 : ℂ) * σ) σ /
          (qPochhammerFin (nk.2 : ℤ) (-(nk.2 : ℂ) * σ) σ * qPochhammer σ σ)) *
        Complex.exp (2 * π * I * ((nk.1 : ℂ) * u + (nk.2 : ℂ) * v)))
      (ε * (qPochhammer τ τ * qPochhammer b σ * qPochhammer (a + u) τ *
        qPochhammer (σ + v) σ) /
        (qPochhammer σ σ * qPochhammer a τ * qPochhammer u τ *
          qPochhammer (b + v) σ)) := by
  let f : ℕ → ℂ := fun n => qPochhammerFin (n : ℤ) a τ /
    qPochhammerFin (n : ℤ) τ τ * Complex.exp (2 * π * I * u) ^ n
  let g : ℕ → ℂ := fun n => qPochhammerFin (n : ℤ) (b - (n : ℂ) * σ) σ /
    qPochhammerFin (n : ℤ) (-(n : ℂ) * σ) σ * Complex.exp (2 * π * I * v) ^ n
  have hf := hasSum_qPochhammerFin_div a u τ hτ hu
  have hg := hasSum_qPochhammerFin_backward_div b v σ hσ hbv
  have hfg : Summable (fun nk : ℕ × ℕ => f nk.1 * g nk.2) :=
    summable_mul_of_summable_norm hf.summable.norm hg.summable.norm
  have hprod := (hf.mul hg hfg).mul_left
      (ε * (qPochhammer τ τ / qPochhammer a τ) *
        (qPochhammer b σ / qPochhammer σ σ))
  have hvalue :
      (ε * (qPochhammer τ τ / qPochhammer a τ) *
        (qPochhammer b σ / qPochhammer σ σ)) *
        ((qPochhammer (a + u) τ / qPochhammer u τ) *
          (qPochhammer (σ + v) σ / qPochhammer (b + v) σ)) =
      ε * (qPochhammer τ τ * qPochhammer b σ * qPochhammer (a + u) τ *
        qPochhammer (σ + v) σ) /
        (qPochhammer σ σ * qPochhammer a τ * qPochhammer u τ *
          qPochhammer (b + v) σ) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hvalue] at hprod
  exact hprod.congr_fun (fun nk => by
    rw [qPochhammer_residue_forward_coefficient a τ hτ ha nk.1,
      qPochhammer_residue_backward_coefficient b σ hσ nk.2,
      qPochhammer_residue_exp_add nk.1 nk.2 u v]
    ring)

end SIC
