/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.BarnesDoubleGamma.Product

/-!
# Joint continuity of the Barnes double gamma product

Locally uniform convergence and joint continuity of the inverse Barnes double gamma
on the slit plane.

This module follows the continuation of the defining product in
[95, Shintani (1977), paragraph 1.6, p. 181] and Proposition 1. It supplies the
continuity in the period needed to pass from complex to positive real periods.

## The argument

On a compact subset of `ℂ × (ℂ \ (-∞,0])`, the continuous function
`‖z‖ C(τ)` is bounded, where `C` is the ray constant from the digamma estimates.
The cone comparison bounds `‖(m+nτ)⁻¹‖` by both `C(τ)` and
`C(τ) ‖(m+ni)⁻¹‖`. The cubic Weierstrass estimate is therefore bounded
uniformly by a constant times `‖(m+ni)⁻¹‖³`, a summable family.
The product converges locally uniformly in both variables. Its continuous
factors and the holomorphic normalization coefficients then give joint continuity.
-/

noncomputable section

open Complex Set Filter
open scoped Topology

namespace SIC

/-! ### Uniform convergence on compact subsets

The ray comparison gives one summable majorant on every compact subset of
the continued period domain. The factor denominators are nonzero there.
-/

/-- Each Barnes factor is jointly continuous in `(z,τ)` on the slit-plane period domain. -/
lemma continuousOn_barnesDoubleGammaInvFactor (p : BarnesDoubleGammaIndex) :
    ContinuousOn (fun q : ℂ × ℂ => barnesDoubleGammaInvFactor q.1 1 q.2 p)
      {q | q.2 ∈ Complex.slitPlane} := by
  have ha : Continuous (fun q : ℂ × ℂ => barnesDoubleGammaLatticePoint 1 q.2 p) := by
    unfold barnesDoubleGammaLatticePoint
    fun_prop
  have hdiv := continuous_fst.continuousOn.div ha.continuousOn
    (fun q hq => barnesDoubleGammaLatticePoint_one_ne_zero q.2 hq p)
  simp_rw [barnesDoubleGammaInvFactor_eq_genusTwoFactor, barnesGenusTwoFactor]
  exact (continuousOn_const.add hdiv).mul
    ((hdiv.neg.add ((hdiv.pow 2).div_const 2)).cexp)

/-- The defining Barnes product converges locally uniformly in `(z,τ)` for
`τ ∈ ℂ \ (-∞,0]`. This makes the product continuation in
[95, Shintani (1977), paragraph 1.6, p. 181] explicit. -/
theorem hasProdLocallyUniformlyOn_barnesDoubleGammaInvFactor :
    HasProdLocallyUniformlyOn
      (fun p : BarnesDoubleGammaIndex => fun q : ℂ × ℂ =>
        barnesDoubleGammaInvFactor q.1 1 q.2 p)
      (fun q => ∏' p : BarnesDoubleGammaIndex, barnesDoubleGammaInvFactor q.1 1 q.2 p)
      {q | q.2 ∈ Complex.slitPlane} := by
  apply hasProdLocallyUniformlyOn_of_forall_compact
    (Complex.isOpen_slitPlane.preimage continuous_snd)
  intro K hK hKc
  obtain ⟨B, hB⟩ := hKc.bddAbove_image (continuous_fst.norm.continuousOn.mul
    (continuousOn_digammaRayConstant.comp continuous_snd.continuousOn hK))
  let C := max B 0
  have hbound (q : ℂ × ℂ) (hq : q ∈ K) : ‖q.1‖ * digammaRayConstant q.2 ≤ C :=
    (hB (mem_image_of_mem _ hq)).trans (le_max_left _ _)
  have hu : Summable (fun p : BarnesDoubleGammaIndex =>
      (2 * (1 + C) ^ 4 * Real.exp ((1 + C) ^ 2) * C ^ 3) *
        ‖(barnesDoubleGammaLatticePoint 1 I p)⁻¹‖ ^ 3) :=
    (summable_barnesDoubleGammaLatticePoint_inv_cube I (by simp)).mul_left _
  have hprod : HasProdUniformlyOn
      (fun p : BarnesDoubleGammaIndex => fun q : ℂ × ℂ =>
        1 + (barnesDoubleGammaInvFactor q.1 1 q.2 p - 1))
      (fun q => ∏' p : BarnesDoubleGammaIndex,
        (1 + (barnesDoubleGammaInvFactor q.1 1 q.2 p - 1))) K := by
    apply hu.hasProdUniformlyOn_one_add hKc
    · exact Filter.Eventually.of_forall fun p q hq =>
        norm_barnesDoubleGammaInvFactor_sub_one_le (hK hq) (hbound q hq) p
    · intro p
      exact ((continuousOn_barnesDoubleGammaInvFactor p).mono hK).sub continuousOn_const
  simpa only [← add_sub_assoc, add_sub_cancel_left] using hprod

/-! ### Continuity of the normalized product

Locally uniform convergence preserves continuity. The coefficient derivatives
proved in `Coefficients` provide the remaining exponential normalization.
-/

/-- The Barnes product is jointly continuous on the slit-plane period domain,
by `hasProdLocallyUniformlyOn_barnesDoubleGammaInvFactor`. -/
lemma continuousOn_barnesDoubleGammaInvFactor_tprod :
    ContinuousOn (fun q : ℂ × ℂ =>
      ∏' p : BarnesDoubleGammaIndex, barnesDoubleGammaInvFactor q.1 1 q.2 p)
      {q | q.2 ∈ Complex.slitPlane} := by
  apply hasProdLocallyUniformlyOn_barnesDoubleGammaInvFactor.continuousOn
  exact Filter.Eventually.frequently (Filter.Eventually.of_forall fun s =>
    continuousOn_finsetProd s fun p _ => continuousOn_barnesDoubleGammaInvFactor p)

/-- The inverse Barnes double gamma is jointly continuous in `(z,τ)` for
`τ ∈ ℂ \ (-∞,0]`. This makes the period continuation in
[95, Shintani (1977), paragraph 1.6, p. 181] explicit: on compact subsets the cubic
Weierstrass estimate is uniform, and the normalization coefficients are holomorphic. -/
theorem continuousAt_barnesDoubleGammaInv {z tau : ℂ}
    (htau : tau ∈ Complex.slitPlane) :
    ContinuousAt (fun p : ℂ × ℂ => barnesDoubleGammaInv p.1 1 p.2) (z, tau) := by
  have h21 : ContinuousAt (fun w : ℂ => barnesGamma21 1 w) tau :=
    (differentiableAt_barnesGamma21_comp (differentiableAt_const 1) differentiableAt_id
      htau (by simpa using htau)).continuousAt
  have h22 : ContinuousAt (fun w : ℂ => barnesGamma22 1 w) tau :=
    (differentiableAt_barnesGamma22_comp (differentiableAt_const 1) differentiableAt_id
      Complex.one_mem_slitPlane (by simpa using htau)).continuousAt
  have h21p : ContinuousAt (fun p : ℂ × ℂ => barnesGamma21 1 p.2) (z, tau) :=
    ContinuousAt.comp (f := Prod.snd) (g := fun w => barnesGamma21 1 w) h21 continuousAt_snd
  have h22p : ContinuousAt (fun p : ℂ × ℂ => barnesGamma22 1 p.2) (z, tau) :=
    ContinuousAt.comp (f := Prod.snd) (g := fun w => barnesGamma22 1 w) h22 continuousAt_snd
  have hprod := continuousOn_barnesDoubleGammaInvFactor_tprod.continuousAt (x := (z, tau))
    ((Complex.isOpen_slitPlane.preimage continuous_snd).mem_nhds htau)
  unfold barnesDoubleGammaInv
  exact (continuousAt_fst.mul ((h22p.mul continuousAt_fst).add
    (((continuousAt_fst.pow 2).div_const 2).mul h21p)).cexp).mul hprod

end SIC

end
