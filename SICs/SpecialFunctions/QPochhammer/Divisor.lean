/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.QPochhammer.Infinite

/-!
# Derivatives and residues of q-Pochhammer products

Exact derivatives at q-Pochhammer zeros and residues of their reciprocal quotients.

This module follows the first-factor and shift calculation in [95, Shintani (1977),
proof of Proposition 5, p. 181], and the residue evaluation of [RW26, Radchenko,
Wheeler (2026), Appendix A.2, `app:mod.fad`]. It supplies the simple-pole constants needed by the
modular five-term integral.

## The argument

At `z = k-nτ`, split off the first `n` nonzero factors and then the zero factor.
The latter has derivative `-2πi`; the remaining tail is `(q;q)∞ = ϖ(τ,τ)`.
Their product gives the derivative, which is nonzero. Dividing the first-order
expansion gives the reciprocal residue; multiplication by a continuous numerator
then evaluates residues of q-Pochhammer quotients. Limits are punctured, so they
describe the meromorphic poles independently of totalized point values.
The finite-factor form follows by periodicity and by splitting the shifted
product into its first `n` factors and an unshifted tail. Dividing the argument
by a nonzero scale transports the punctured limit and multiplies the residue
by that scale; a continuous factor contributes its value at the pole.
-/

noncomputable section

open Complex Real Filter
open scoped Topology

namespace SIC

/-! ### Simple zeros and reciprocal residues

The first nonzero Taylor coefficient controls both the zero order and the pole
coefficient of a reciprocal quotient.
-/

/-- The infinite tail `ϖ(τ,τ)` is nonzero in the upper half plane. -/
lemma qPochhammer_tau_ne_zero (τ : ℂ) (hτ : 0 < τ.im) :
    qPochhammer τ τ ≠ 0 := by
  rw [ne_eq, qPochhammer_eq_zero_iff τ τ hτ, not_exists]
  intro n
  rw [not_exists]
  intro k h
  have him := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.intCast_im, Complex.mul_im, Complex.natCast_re,
    Complex.natCast_im, zero_mul, zero_sub] at him
  nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]

/-- The origin derivative of `ϖ` is `-2πi ϖ(τ,τ)`, the first-factor calculation in
[95, Shintani (1977), proof of Proposition 5, p. 181]. -/
lemma qPochhammer_hasDerivAt_zero (τ : ℂ) (hτ : 0 < τ.im) :
    HasDerivAt (fun z => qPochhammer z τ) (-2 * π * I * qPochhammer τ τ) 0 := by
  have htail : DifferentiableAt ℂ (fun z : ℂ => qPochhammer (z + τ) τ) 0 :=
    (qPochhammer_differentiable τ hτ).differentiableAt.comp 0 (by fun_prop)
  have hfactor : HasDerivAt (fun z : ℂ => 1 - Complex.exp (2 * π * I * z))
      (-2 * π * I) 0 := by
    have hlin : HasDerivAt (fun z : ℂ => 2 * π * I * z) (2 * π * I) 0 := by
      exact hasDerivAt_const_mul (2 * π * I)
    have hexp : HasDerivAt (fun z : ℂ => Complex.exp (2 * π * I * z))
        (2 * π * I) 0 := by
      simpa only [mul_zero, Complex.exp_zero, one_mul] using hlin.cexp
    exact ((hasDerivAt_const (x := (0 : ℂ)) (c := (1 : ℂ))).sub hexp).congr_deriv
      (by ring)
  have hproduct := htail.hasDerivAt.mul hfactor
  refine (hproduct.congr_deriv ?_).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun z => ?_)
  · simp
    ring
  have hsplit := qPochhammerFin_natCast_mul_qPochhammer_add 1 z τ hτ
  simpa [qPochhammerFin_one, mul_comm] using hsplit.symm

/-- The finite prefix before the factor at `-nτ` has no zeros. -/
lemma qPochhammerFin_neg_nat_mul_ne_zero (τ : ℂ) (hτ : 0 < τ.im) (n : ℕ) :
    qPochhammerFin (n : ℤ) (-(n : ℂ) * τ) τ ≠ 0 := by
  rw [qPochhammerFin_natCast]
  refine Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  apply one_sub_exp_two_pi_I_ne_zero_of_im_ne_zero
  have hjn : (j : ℝ) < n := by exact_mod_cast Finset.mem_range.mp hj
  have him : (-(n : ℂ) * τ + (j : ℂ) * τ).im = ((j : ℝ) - n) * τ.im := by
    simp [Complex.add_im, Complex.mul_im]
    ring
  rw [him]
  exact ne_of_lt (mul_neg_of_neg_of_pos (sub_neg.mpr hjn) hτ)

/-- At `-nτ`, the first `n` factors multiply the origin derivative of the shifted tail.
Used by `qPochhammer_hasDerivAt_lattice`. -/
private lemma qPochhammer_hasDerivAt_neg_nat_mul (τ : ℂ) (hτ : 0 < τ.im) (n : ℕ) :
    HasDerivAt (fun z => qPochhammer z τ)
      (-2 * π * I * qPochhammerFin (n : ℤ) (-(n : ℂ) * τ) τ * qPochhammer τ τ)
      (-(n : ℂ) * τ) := by
  have hprefix : DifferentiableAt ℂ (fun z : ℂ => qPochhammerFin (n : ℤ) z τ)
      (-(n : ℂ) * τ) := by
    rw [funext fun z => qPochhammerFin_natCast n z τ]
    fun_prop
  have htail : HasDerivAt (fun z : ℂ => qPochhammer (z + (n : ℂ) * τ) τ)
      (-2 * π * I * qPochhammer τ τ) (-(n : ℂ) * τ) := by
    have hbase : -(n : ℂ) * τ + (n : ℂ) * τ = 0 := by ring
    have hzeroDeriv : HasDerivAt (fun z => qPochhammer z τ)
        (-2 * π * I * qPochhammer τ τ) (-(n : ℂ) * τ + (n : ℂ) * τ) := by
      simpa only [hbase] using qPochhammer_hasDerivAt_zero τ hτ
    exact hzeroDeriv.comp_add_const (-(n : ℂ) * τ) ((n : ℂ) * τ)
  have hproduct := hprefix.hasDerivAt.mul htail
  have hzero : qPochhammer (-(n : ℂ) * τ + (n : ℂ) * τ) τ = 0 := by
    simpa using qPochhammer_zero τ
  refine (hproduct.congr_deriv ?_).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun z => ?_)
  · rw [hzero]
    ring
  exact (qPochhammerFin_natCast_mul_qPochhammer_add n z τ hτ).symm

/-- At a zero `k-nτ`, the derivative of `ϖ` is
`-2πi ϖₙ(-nτ,τ) ϖ(τ,τ)`. This is the shifted first-factor calculation of
[95, Shintani (1977), proof of Proposition 5, p. 181], used in the residue sum
of [RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`]. -/
theorem qPochhammer_hasDerivAt_lattice (τ : ℂ) (hτ : 0 < τ.im) (n : ℕ) (k : ℤ) :
    HasDerivAt (fun z => qPochhammer z τ)
      (-2 * π * I * qPochhammerFin (n : ℤ) (-(n : ℂ) * τ) τ * qPochhammer τ τ)
      ((k : ℂ) - n * τ) := by
  have hpoint : ((k : ℂ) - n * τ) + (-(k : ℤ) : ℂ) = -(n : ℂ) * τ := by
    ring
  have hbase : HasDerivAt (fun z => qPochhammer z τ)
      (-2 * π * I * qPochhammerFin (n : ℤ) (-(n : ℂ) * τ) τ * qPochhammer τ τ)
      (((k : ℂ) - n * τ) + (-(k : ℤ) : ℂ)) := by
    simpa only [hpoint] using qPochhammer_hasDerivAt_neg_nat_mul τ hτ n
  have hshift := hbase.comp_add_const ((k : ℂ) - n * τ) (-(k : ℤ) : ℂ)
  have hperiod : (fun z => qPochhammer (z + (-(k : ℤ) : ℂ)) τ) =
      (fun z => qPochhammer z τ) :=
    funext fun z => by simpa only [Int.cast_neg] using qPochhammer_add_intCast z τ (-k)
  simpa only [hperiod] using hshift

/-- Every zero `k-nτ` of `ϖ` is simple, as in [95, Shintani (1977),
proof of Proposition 5, p. 181]. The explicit derivative is
`qPochhammer_hasDerivAt_lattice`. -/
theorem qPochhammer_deriv_lattice_ne_zero (τ : ℂ) (hτ : 0 < τ.im) (n : ℕ) (k : ℤ) :
    deriv (fun z => qPochhammer z τ) ((k : ℂ) - n * τ) ≠ 0 := by
  rw [(qPochhammer_hasDerivAt_lattice τ hτ n k).deriv]
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero)
      (qPochhammerFin_neg_nat_mul_ne_zero τ hτ n))
    (qPochhammer_tau_ne_zero τ hτ)

/-- Every zero of `ϖ(z,τ)` is simple for `Im τ > 0`, by the zero set in
`qPochhammer_eq_zero_iff` and the first-factor derivative calculation of
[95, Shintani (1977), proof of Proposition 5, p. 181]. -/
theorem qPochhammer_deriv_ne_zero_of_eq_zero (z τ : ℂ) (hτ : 0 < τ.im)
    (hz : qPochhammer z τ = 0) : deriv (fun w => qPochhammer w τ) z ≠ 0 := by
  obtain ⟨n, k, rfl⟩ := (qPochhammer_eq_zero_iff z τ hτ).mp hz
  exact qPochhammer_deriv_lattice_ne_zero τ hτ n k

/-- The reciprocal `1/ϖ(z,τ)` has coefficient
`1/(-2πi ϖₙ(-nτ,τ) ϖ(τ,τ))` at `k-nτ`. -/
lemma tendsto_qPochhammer_reciprocal_residue (τ : ℂ) (hτ : 0 < τ.im)
    (n : ℕ) (k : ℤ) :
    Tendsto (fun z : ℂ => (z - ((k : ℂ) - n * τ)) / qPochhammer z τ)
      (𝓝[≠] ((k : ℂ) - n * τ))
      (𝓝 (1 / (-2 * π * I * qPochhammerFin (n : ℤ) (-(n : ℂ) * τ) τ *
        qPochhammer τ τ))) := by
  have hder := qPochhammer_hasDerivAt_lattice τ hτ n k
  have hzero : qPochhammer ((k : ℂ) - n * τ) τ = 0 :=
    (qPochhammer_eq_zero_iff _ τ hτ).mpr ⟨n, k, rfl⟩
  have hne : -2 * π * I * qPochhammerFin (n : ℤ) (-(n : ℂ) * τ) τ *
      qPochhammer τ τ ≠ 0 := by
    simpa only [hder.deriv] using qPochhammer_deriv_lattice_ne_zero τ hτ n k
  have hslope := hder.tendsto_slope
  have hslope' : Tendsto
      (fun z : ℂ => qPochhammer z τ / (z - ((k : ℂ) - n * τ)))
      (𝓝[≠] ((k : ℂ) - n * τ))
      (𝓝 (-2 * π * I * qPochhammerFin (n : ℤ) (-(n : ℂ) * τ) τ *
        qPochhammer τ τ)) := by
    convert hslope using 1
    ext z
    rw [slope_def_field, hzero, sub_zero]
  simpa only [inv_div, one_div] using hslope'.inv₀ hne

/-- The residue limit of `ϖ(z+y,τ)/ϖ(z,τ)` at `z=k-nτ` is its numerator value
divided by `-2πi ϖₙ(-nτ,τ) ϖ(τ,τ)`. This is the simple-pole calculation
used in [RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`]; a zero numerator
gives residue zero and permits a removable singularity. -/
theorem tendsto_qPochhammer_quotient_residue (y τ : ℂ) (hτ : 0 < τ.im)
    (n : ℕ) (k : ℤ) :
    Tendsto (fun z : ℂ => (z - ((k : ℂ) - n * τ)) *
      (qPochhammer (z + y) τ / qPochhammer z τ))
      (𝓝[≠] ((k : ℂ) - n * τ))
      (𝓝 (qPochhammer ((k : ℂ) - n * τ + y) τ /
        (-2 * π * I * qPochhammerFin (n : ℤ) (-(n : ℂ) * τ) τ *
          qPochhammer τ τ))) := by
  have hnum : Tendsto (fun z : ℂ => qPochhammer (z + y) τ)
      (𝓝[≠] ((k : ℂ) - n * τ))
      (𝓝 (qPochhammer ((k : ℂ) - n * τ + y) τ)) := by
    have hshift : ContinuousAt (fun z : ℂ => z + y) ((k : ℂ) - n * τ) := by
      fun_prop
    have hcont : ContinuousAt (fun z : ℂ => qPochhammer (z + y) τ)
        ((k : ℂ) - n * τ) :=
      (qPochhammer_continuous τ hτ).continuousAt.comp hshift
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hrecip := tendsto_qPochhammer_reciprocal_residue τ hτ n k
  convert hnum.mul hrecip using 1
  · ext z
    ring
  · simp [div_eq_mul_inv]

/-! ### Finite-factor and scaled residues

The shifted numerator splits into the finite backward prefix and its tail.
The scaled limit is its image under the invertible linear map `z ↦ z/ε`.
-/

/-- The residue of `ϖ(z+y,τ)/ϖ(z,τ)` at `z=k-nτ`, factored as
`ϖ(y,τ)/(-2πi ϖ(τ,τ))` times `ϖₙ(y-nτ,τ)/ϖₙ(-nτ,τ)`.
This is the finite-factor residue expression in
[RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`]. -/
theorem tendsto_qPochhammer_quotient_residue_fin (y τ : ℂ) (hτ : 0 < τ.im)
    (n : ℕ) (k : ℤ) :
    Tendsto (fun z : ℂ => (z - ((k : ℂ) - n * τ)) *
      (qPochhammer (z + y) τ / qPochhammer z τ))
      (𝓝[≠] ((k : ℂ) - n * τ))
      (𝓝 (qPochhammer y τ / (-2 * π * I * qPochhammer τ τ) *
        (qPochhammerFin (n : ℤ) (y - (n : ℂ) * τ) τ /
          qPochhammerFin (n : ℤ) (-(n : ℂ) * τ) τ))) := by
  have hperiod : qPochhammer ((k : ℂ) - n * τ + y) τ =
      qPochhammer (y - (n : ℂ) * τ) τ := by
    rw [show (k : ℂ) - n * τ + y = (y - (n : ℂ) * τ) + k by ring,
      qPochhammer_add_intCast]
  have hsplit : qPochhammer (y - (n : ℂ) * τ) τ =
      qPochhammerFin (n : ℤ) (y - (n : ℂ) * τ) τ * qPochhammer y τ := by
    simpa only [show y - (n : ℂ) * τ + (n : ℂ) * τ = y by ring] using
      (qPochhammerFin_natCast_mul_qPochhammer_add n (y - (n : ℂ) * τ) τ hτ).symm
  convert tendsto_qPochhammer_quotient_residue y τ hτ n k using 1
  rw [hperiod, hsplit]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring_nf

/-- Under `z ↦ z/ε`, the residue at `ε(k-nτ)` acquires the factor `ε`;
a continuous numerator contributes its value there. This transports
`tendsto_qPochhammer_quotient_residue_fin` to the scaled integrand of
[RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`]. -/
theorem tendsto_mul_qPochhammer_quotient_residue_div (g : ℂ → ℂ) (y τ ε : ℂ)
    (hτ : 0 < τ.im) (hε : ε ≠ 0) (n : ℕ) (k : ℤ)
    (hg : ContinuousAt g (ε * ((k : ℂ) - n * τ))) :
    Tendsto (fun z : ℂ => (z - ε * ((k : ℂ) - n * τ)) *
      (g z * (qPochhammer ((z + y) / ε) τ / qPochhammer (z / ε) τ)))
      (𝓝[≠] (ε * ((k : ℂ) - n * τ)))
      (𝓝 (g (ε * ((k : ℂ) - n * τ)) * ε *
        (qPochhammer (y / ε) τ / (-2 * π * I * qPochhammer τ τ) *
          (qPochhammerFin (n : ℤ) (y / ε - (n : ℂ) * τ) τ /
            qPochhammerFin (n : ℤ) (-(n : ℂ) * τ) τ)))) := by
  have hmap : Tendsto (fun z : ℂ => z / ε)
      (𝓝[≠] (ε * ((k : ℂ) - n * τ))) (𝓝[≠] ((k : ℂ) - n * τ)) := by
    have hder := ((hasDerivAt_id (ε * ((k : ℂ) - n * τ))).div_const ε)
    simpa [hε] using hder.tendsto_nhdsNE (one_div_ne_zero hε)
  have hres := (tendsto_qPochhammer_quotient_residue_fin (y / ε) τ hτ n k).comp hmap
  have hnum : Tendsto g (𝓝[≠] (ε * ((k : ℂ) - n * τ)))
      (𝓝 (g (ε * ((k : ℂ) - n * τ)))) :=
    hg.tendsto.mono_left nhdsWithin_le_nhds
  convert (hnum.mul_const ε).mul hres using 1
  ext z
  dsimp only [Function.comp_def]
  have hdiff : (z / ε - ((k : ℂ) - n * τ)) * ε =
      z - ε * ((k : ℂ) - n * τ) := by
    rw [sub_mul, div_mul_cancel₀ z hε]
    ring
  rw [add_div, ← hdiff]
  ring

end SIC
