/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Dilogarithm.TorsionConvolution
import SICs.Principal.Dilogarithm.GhostOverlap
import SICs.Principal.Construction.TCCFiniteForm

/-!
# The Principal Twisted Convolution Conjecture from Theorem 7

The finite form of the principal Twisted Convolution Conjecture at `λ = 1`,
`∑_q ξ_d^{⟨p, q⟩} ν̃_d(q)/ν̃_d(q - p) = d² δ_{p ≡ 0}`, derived from Radchenko and Wheeler's
convolution identity through the bridge `F(p/d) ν̃_d(p) = ζ_d(p)`.

This module proves the finite and real principal-family restrictions of
[AFK25, Conjecture 1.35, `cnj:tci`] at `λ = 1`, from
[RW26, Radchenko, Wheeler (2026), Theorem 7, `thm:ghostsic`] in the conjugate form
`principalDilogConvolutionConj` of `SICs.Principal.Dilogarithm.TorsionConvolution`, and hence
`principalRealShiftTCC` and `IsPrincipalRealShift d 1` through
`principalFiniteShiftTCC_iff`. Radchenko and Wheeler remark after Theorem 7 that it is
"equivalent to the principal ideal case of the identity conjectured by Appleby--Flammia--Kopp";
the finite and real shift consequences are made explicit here.

## The argument

Write `F(q/d)` for `principalDilogValue` at `q/d`, `χ_q = ⟨q/d⟩` for the Gaussian, and
`ζ_d(q) = (-1)^{s_d(q)} ξ_d^{-Q_d(q)}` for the bridge phase. The bridge
`F(q/d) ν̃_d(q) = ζ_d(q)` (`principalDilogValue_mul_phasedGhostOverlap`) holds at every
integer `q`, so the summand of `principalPhasedShiftSum` at the canonical representative `q` is

$$
\xi_d^{\langle p, q\rangle}\frac{\tilde\nu_d(q)}{\tilde\nu_d(q - p)}
  = \xi_d^{\langle p, q\rangle}\frac{\zeta_d(q)}{\zeta_d(q - p)}\cdot\frac{F((q - p)/d)}{F(q/d)}
  = -\zeta_d(-p)^{-1}\,\omega_d^{-(p_1q_1 + p_2q_2 + p_1q_2)}\,\frac{F((q - p)/d)}{F(q/d)},
$$

by the convolution law of the bridge phase
(`principalDilogBridgePhase_convolution`). The reflection law (5) gives
`1/F(q/d) = χ_q F⁻(-q/d)`, and `F⁻(-q/d) = F(-q/d)` except at `q = 0`, where
`F⁻(0) - F(0) = ε^{-1/2} - ε^{1/2} = -√N` (`sqrt_principalJacobiFactor_sub_inv`). Hence

$$
\sum_q \xi_d^{\langle p, q\rangle}\frac{\tilde\nu_d(q)}{\tilde\nu_d(q - p)}
  = -\zeta_d(-p)^{-1}\Big[\sum_q \omega_d^{-(p_1q_1 + p_2q_2 + p_1q_2)}\,\chi_q\,
    F((q - p)/d)\,F(-q/d) - \sqrt N\,F(-p/d)\Big].
$$

Replacing `q` by `-q`, which permutes the residue classes and leaves every factor invariant up to
its `d`-periodicity (`principalDilogValue_shiftRationalPoint_congr`,
`thetaCharacter_shiftRationalPoint_principalA_congr`, `thetaCharacter_neg`), the bracketed sum
becomes `d` times the left side of `principalDilogConvolutionConj` at `-p`, which is
`d(√(d - 3) F(-p/d) + d δ_{p ≡ 0})`; with `√N = d √(d - 3)` (`sqrt_principalDilogOrder`) the
bracket is `d² δ_{p ≡ 0}`, and on the zero class `ζ_d(-p) = -1`
(`principalDilogBridgePhase_of_mod_eq_zero`). This is
`∑_q ξ_d^{⟨p, q⟩} ν̃_d(q)/ν̃_d(q - p) = d² δ_{p ≡ 0}`.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### The finite character sum through the bridge

`principalPhasedShiftSum` at `λ = 1`, rewritten in the values `F` and the character of the
conjugate vector. -/

/-- The bridge expresses the ratio of overlaps through the ratio of dilogarithm values. -/
private lemma principalPhasedGhostOverlap_ratio_eq (d : RankOneDimension)
    (p q : IntPhaseSpace) :
    principalPhasedGhostOverlap d q / principalPhasedGhostOverlap d (q - p) =
      (principalDilogBridgePhase d q / principalDilogBridgePhase d (q - p)) *
        (principalDilogValue d (shiftRationalPoint d (q - p)) /
          principalDilogValue d (shiftRationalPoint d q)) := by
  have hmem (r : IntPhaseSpace) :
      principalA d ∈ gammaSubgroup (shiftRationalPoint d r) :=
    principalA_mem_gammaSubgroup_shiftRationalPoint d d.property r
  have hFq := principalDilogValue_ne_zero d d.property (hmem q)
  have hFqp := principalDilogValue_ne_zero d d.property (hmem (q - p))
  have hνqp := principalPhasedGhostOverlap_ne_zero d (q - p)
  have hζqp := principalDilogBridgePhase_ne_zero d (q - p)
  have hbq := principalDilogValue_mul_phasedGhostOverlap d q
  have hbqp := principalDilogValue_mul_phasedGhostOverlap d (q - p)
  calc
    _ = (principalDilogBridgePhase d q /
          principalDilogValue d (shiftRationalPoint d q)) /
        (principalDilogBridgePhase d (q - p) /
          principalDilogValue d (shiftRationalPoint d (q - p))) := by
      rw [← hbq, ← hbqp]
      field_simp
    _ = _ := by field_simp

/-- The bridge and reflection identities rewrite one summand of the finite shift sum. -/
private lemma principalPhasedShiftSummand_eq (d : RankOneDimension)
    (p q : IntPhaseSpace) :
    displacementPhase d ^ intSymplecticForm p q *
        (principalPhasedGhostOverlap d q /
          principalPhasedGhostOverlap d (q - p)) =
      -(principalDilogBridgePhase d (-p))⁻¹ *
        standardRoot d ^ (-(p 0 * q 0 + p 1 * q 1 + p 0 * q 1)) *
        thetaCharacter (shiftRationalPoint d q) (principalA d : Mat(2, ℤ)) *
        principalDilogValue d (shiftRationalPoint d (q - p)) *
        principalDilogValueMinus d (shiftRationalPoint d (-q)) := by
  rw [principalPhasedGhostOverlap_ratio_eq d p q]
  calc
    _ = (displacementPhase d ^ intSymplecticForm p q *
          (principalDilogBridgePhase d q / principalDilogBridgePhase d (q - p))) *
        (principalDilogValue d (shiftRationalPoint d (q - p)) *
          (principalDilogValue d (shiftRationalPoint d q))⁻¹) := by
      rw [div_eq_mul_inv]
      ring
    _ = _ := by
      rw [principalDilogBridgePhase_convolution d p q,
        inv_principalDilogValue_shiftRationalPoint d d.property q]
      ring

/-- Away from the zero residue the two dilogarithm values agree; the origin contributes `√N`. -/
private lemma principalDilogValueMinus_shift_neg_eq (d : RankOneDimension)
    (c : PhaseSpaceMod d) :
    principalDilogValueMinus d
        (shiftRationalPoint d (-(canonicalPhaseSpaceTransversal d).repr c)) =
      principalDilogValue d
        (shiftRationalPoint d (-(canonicalPhaseSpaceTransversal d).repr c)) -
        if c = 0 then (Real.sqrt (principalDilogOrder d) : ℂ) else 0 := by
  by_cases hc : c = 0
  · subst c
    have hint : IsIntegralIndex (0 : Fin 2 → ℚ) := by
      intro i
      exact ⟨0, by simp⟩
    have hz : principalDilogValueMinus d 0 = principalDilogValue d 0 -
        (Real.sqrt (principalDilogOrder d) : ℂ) := by
      rw [principalDilogValueMinus_of_isIntegralIndex d hint,
        principalDilogValue_of_isIntegralIndex d hint]
      have h := sqrt_principalJacobiFactor_sub_inv d d.property
      have h' : (Real.sqrt (principalJacobiFactor d))⁻¹ =
          Real.sqrt (principalJacobiFactor d) - Real.sqrt (principalDilogOrder d) := by
        linarith
      exact_mod_cast h'
    simpa [shiftRationalPoint] using hz
  · have hmod : intPhaseSpaceMod d (-(canonicalPhaseSpaceTransversal d).repr c) ≠ 0 := by
      rw [intPhaseSpaceMod_neg, (canonicalPhaseSpaceTransversal d).residue_repr]
      simpa using hc
    rw [principalDilogValueMinus_of_not_isIntegralIndex d
      (not_isIntegralIndex_shiftRationalPoint d (by omega) hmod)]
    simp [hc]

/-- Only the zero representative contributes to the correction sum. -/
private lemma principalDilogConvolution_correction_sum (d : ℕ) [NeZero d]
    (p : IntPhaseSpace) :
    (∑ c : PhaseSpaceMod d,
      standardRoot d ^
          (-(p 0 * (canonicalPhaseSpaceTransversal d).repr c 0 +
            p 1 * (canonicalPhaseSpaceTransversal d).repr c 1 +
            p 0 * (canonicalPhaseSpaceTransversal d).repr c 1)) *
        (thetaCharacter (shiftRationalPoint d ((canonicalPhaseSpaceTransversal d).repr c))
          (principalA d : Mat(2, ℤ)) *
          (principalDilogValue d
            (shiftRationalPoint d ((canonicalPhaseSpaceTransversal d).repr c - p)) *
            if c = 0 then (Real.sqrt (principalDilogOrder d) : ℂ) else 0))) =
      (Real.sqrt (principalDilogOrder d) : ℂ) *
        principalDilogValue d (shiftRationalPoint d (-p)) := by
  have hχzero : thetaCharacter (shiftRationalPoint d (0 : IntPhaseSpace))
      (principalA d : Mat(2, ℤ)) = 1 := by
    apply thetaCharacter_of_isIntegralIndex
    intro i
    exact ⟨0, by simp [shiftRationalPoint]⟩
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    canonicalPhaseSpaceTransversal_repr_zero, Pi.zero_apply, mul_zero, add_zero, neg_zero,
    zpow_zero, one_mul, zero_sub, hχzero]
  ring

/-- **The finite Twisted Convolution sum in Radchenko and Wheeler's values**: at `λ = 1`,
`∑_q ξ_d^{⟨p, q⟩} ν̃_d(q)/ν̃_d(q - p)
  = -ζ_d(-p)⁻¹ [∑_q ω_d^{-(p₁q₁ + p₂q₂ + p₁q₂)} χ_q F((q - p)/d) F(-q/d) - √N F(-p/d)]`,
by the bridge `F(q/d) ν̃_d(q) = ζ_d(q)`, the convolution law of the bridge phase, and the
reflection law (5) with its correction at `q = 0`. -/
theorem principalPhasedShiftSum_one_eq (d : RankOneDimension) (p : IntPhaseSpace) :
    principalPhasedShiftSum d 1 p =
      -(principalDilogBridgePhase d (-p))⁻¹ *
        ((∑ c : PhaseSpaceMod d,
          standardRoot d ^
              (-(p 0 * (canonicalPhaseSpaceTransversal d).repr c 0 +
                p 1 * (canonicalPhaseSpaceTransversal d).repr c 1 +
                p 0 * (canonicalPhaseSpaceTransversal d).repr c 1)) *
            thetaCharacter (shiftRationalPoint d ((canonicalPhaseSpaceTransversal d).repr c))
              (principalA d : Mat(2, ℤ)) *
            principalDilogValue d
              (shiftRationalPoint d ((canonicalPhaseSpaceTransversal d).repr c - p)) *
            principalDilogValue d
              (shiftRationalPoint d (-(canonicalPhaseSpaceTransversal d).repr c))) -
      (Real.sqrt (principalDilogOrder d) : ℂ) *
            principalDilogValue d (shiftRationalPoint d (-p))) := by
  unfold principalPhasedShiftSum
  simp only [show (2 * (1 : ℤ) - 1) = 1 by norm_num, one_mul]
  simp_rw [principalPhasedShiftSummand_eq d p]
  simp_rw [principalDilogValueMinus_shift_neg_eq d]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  rw [principalDilogConvolution_correction_sum d p]
  ring

/-- The phase at the negated representative equals the phase at the negative index. -/
private lemma principalDilogConvolution_reindex_phase (d : ℕ) [NeZero d]
    (p : IntPhaseSpace) (c : PhaseSpaceMod d) :
    let q := (canonicalPhaseSpaceTransversal d).repr c
    let q' := (canonicalPhaseSpaceTransversal d).repr (-c)
    standardRoot d ^ (-(p 0 * q' 0 + p 1 * q' 1 + p 0 * q' 1)) =
      standardRoot d ^ (-(p 0 * (-q) 0 + p 1 * (-q) 1 + p 0 * (-q) 1)) := by
  dsimp
  let q := (canonicalPhaseSpaceTransversal d).repr c
  let q' := (canonicalPhaseSpaceTransversal d).repr (-c)
  have hq : intPhaseSpaceMod d q' = intPhaseSpaceMod d (-q) := by
    simp only [q, q', (canonicalPhaseSpaceTransversal d).residue_repr,
      intPhaseSpaceMod_neg]
  obtain ⟨a, ha⟩ := exists_eq_add_smul_of_intPhaseSpaceMod_eq d hq
  subst q'
  apply standardRoot_zpow_eq_of_dvd_sub
  refine ⟨-(p 0 * a 0 + p 1 * a 1 + p 0 * a 1), ?_⟩
  rw [ha]
  simp only [q, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Periodicity and evenness of the theta character identify the nonphase factors. -/
private lemma principalDilogConvolution_reindex_factors (d : RankOneDimension)
    (p q q' : IntPhaseSpace) (hq : intPhaseSpaceMod d q' = intPhaseSpaceMod d (-q)) :
    thetaCharacter (shiftRationalPoint d q') (principalA d : Mat(2, ℤ)) *
        principalDilogValue d (shiftRationalPoint d (q' - p)) *
        principalDilogValue d (shiftRationalPoint d (-q')) =
      principalDilogValue d (shiftRationalPoint d q) *
        principalDilogValue d (shiftRationalPoint d (-p - q)) *
        thetaCharacter (shiftRationalPoint d q) (principalA d : Mat(2, ℤ)) := by
  have hshift : intPhaseSpaceMod d (q' - p) = intPhaseSpaceMod d (-q - p) := by
    funext i
    have hi := congrFun hq i
    simpa [intPhaseSpaceMod, Pi.sub_apply] using
      congrArg (fun x : ZMod d => x - (p i : ZMod d)) hi
  have hneg : intPhaseSpaceMod d (-q') = intPhaseSpaceMod d q := by
    rw [intPhaseSpaceMod_neg, hq, intPhaseSpaceMod_neg, neg_neg]
  have hχ := thetaCharacter_shiftRationalPoint_principalA_congr d hq
  have hχneg : thetaCharacter (shiftRationalPoint d (-q))
      (principalA d : Mat(2, ℤ)) =
      thetaCharacter (shiftRationalPoint d q) (principalA d : Mat(2, ℤ)) := by
    rw [shiftRationalPoint_neg]
    apply thetaCharacter_neg (principalA d)
    exact principalA_mem_gammaSubgroup_shiftRationalPoint d d.property q
  have hFshift := principalDilogValue_shiftRationalPoint_congr d d.property hshift
  have hFneg := principalDilogValue_shiftRationalPoint_congr d d.property hneg
  have hswap : -q - p = -p - q := by
    funext i
    simp only [Pi.sub_apply, Pi.neg_apply]
    ring
  rw [hχ, hχneg, hFshift, hFneg, hswap]
  ring

/-- Negating a residue class transforms its convolution summand into the conjugate one. -/
private lemma principalDilogConvolution_reindex_term (d : RankOneDimension)
    (p : IntPhaseSpace) (c : PhaseSpaceMod d) :
    let q := (canonicalPhaseSpaceTransversal d).repr c
    let q' := (canonicalPhaseSpaceTransversal d).repr (-c)
    standardRoot d ^ (-(p 0 * q' 0 + p 1 * q' 1 + p 0 * q' 1)) *
        thetaCharacter (shiftRationalPoint d q') (principalA d : Mat(2, ℤ)) *
        principalDilogValue d (shiftRationalPoint d (q' - p)) *
        principalDilogValue d (shiftRationalPoint d (-q')) =
      principalDilogValue d (shiftRationalPoint d q) *
        principalDilogValue d (shiftRationalPoint d (-p - q)) *
        thetaCharacter (shiftRationalPoint d q) (principalA d : Mat(2, ℤ)) *
        standardRoot d ^
          (-((-p) 0 * q 0 + (-p) 1 * q 1 + (-p) 0 * q 1)) := by
  dsimp
  let q := (canonicalPhaseSpaceTransversal d).repr c
  let q' := (canonicalPhaseSpaceTransversal d).repr (-c)
  have hq : intPhaseSpaceMod d q' = intPhaseSpaceMod d (-q) := by
    simp only [q, q', (canonicalPhaseSpaceTransversal d).residue_repr,
      intPhaseSpaceMod_neg]
  have hω := principalDilogConvolution_reindex_phase d p c
  have hfactor := principalDilogConvolution_reindex_factors d p q q' hq
  have hexp : -(p 0 * (-q) 0 + p 1 * (-q) 1 + p 0 * (-q) 1) =
      -((-p) 0 * q 0 + (-p) 1 * q 1 + (-p) 0 * q 1) := by
    simp only [Pi.neg_apply]; ring
  change _ = principalDilogValue d (shiftRationalPoint d q) *
      principalDilogValue d (shiftRationalPoint d (-p - q)) *
      thetaCharacter (shiftRationalPoint d q) (principalA d : Mat(2, ℤ)) *
      standardRoot d ^ (-((-p) 0 * q 0 + (-p) 1 * q 1 + (-p) 0 * q 1))
  rw [hω, hexp]
  conv_lhs => arg 1; rw [mul_assoc]
  rw [mul_assoc, hfactor]
  ring

/-- The involution on residue classes reindexes the bridge sum as the conjugate convolution. -/
private lemma principalDilogConvolution_reindex_sum (d : RankOneDimension)
    (p : IntPhaseSpace) :
    (∑ c : PhaseSpaceMod d,
      standardRoot d ^
          (-(p 0 * (canonicalPhaseSpaceTransversal d).repr c 0 +
            p 1 * (canonicalPhaseSpaceTransversal d).repr c 1 +
            p 0 * (canonicalPhaseSpaceTransversal d).repr c 1)) *
        thetaCharacter (shiftRationalPoint d ((canonicalPhaseSpaceTransversal d).repr c))
          (principalA d : Mat(2, ℤ)) *
        principalDilogValue d
          (shiftRationalPoint d ((canonicalPhaseSpaceTransversal d).repr c - p)) *
        principalDilogValue d
          (shiftRationalPoint d (-(canonicalPhaseSpaceTransversal d).repr c))) =
    ∑ c : PhaseSpaceMod d,
      principalDilogValue d (shiftRationalPoint d ((canonicalPhaseSpaceTransversal d).repr c)) *
        principalDilogValue d
          (shiftRationalPoint d (-p - (canonicalPhaseSpaceTransversal d).repr c)) *
        thetaCharacter (shiftRationalPoint d ((canonicalPhaseSpaceTransversal d).repr c))
          (principalA d : Mat(2, ℤ)) *
        standardRoot d ^
          (-((-p) 0 * (canonicalPhaseSpaceTransversal d).repr c 0 +
            (-p) 1 * (canonicalPhaseSpaceTransversal d).repr c 1 +
            (-p) 0 * (canonicalPhaseSpaceTransversal d).repr c 1)) := by
  let f : PhaseSpaceMod d → ℂ := fun c =>
    standardRoot d ^
        (-(p 0 * (canonicalPhaseSpaceTransversal d).repr c 0 +
          p 1 * (canonicalPhaseSpaceTransversal d).repr c 1 +
          p 0 * (canonicalPhaseSpaceTransversal d).repr c 1)) *
      thetaCharacter (shiftRationalPoint d ((canonicalPhaseSpaceTransversal d).repr c))
        (principalA d : Mat(2, ℤ)) *
      principalDilogValue d
        (shiftRationalPoint d ((canonicalPhaseSpaceTransversal d).repr c - p)) *
      principalDilogValue d
        (shiftRationalPoint d (-(canonicalPhaseSpaceTransversal d).repr c))
  change (∑ c, f c) = _
  calc
    _ = ∑ c, f (-c) := (Equiv.sum_comp (Equiv.neg (PhaseSpaceMod d)) f).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c _
      exact principalDilogConvolution_reindex_term d p c

/-- **The bracketed sum is `d² δ_{p ≡ 0}`**: reindexing `q ↦ -q` turns
`∑_q ω_d^{-(p₁q₁ + p₂q₂ + p₁q₂)} χ_q F((q - p)/d) F(-q/d)` into `d` times the left side of
`principalDilogConvolutionConj` at `-p`, so the sum is `d √(d - 3) F(-p/d) + d² δ_{p ≡ 0}`, and
`√N F(-p/d)` cancels the first term (`sqrt_principalDilogOrder`). -/
theorem principalDilogConvolutionConj_sum_neg (d : RankOneDimension) (p : IntPhaseSpace) :
    (∑ c : PhaseSpaceMod d,
        standardRoot d ^
            (-(p 0 * (canonicalPhaseSpaceTransversal d).repr c 0 +
              p 1 * (canonicalPhaseSpaceTransversal d).repr c 1 +
              p 0 * (canonicalPhaseSpaceTransversal d).repr c 1)) *
          thetaCharacter (shiftRationalPoint d ((canonicalPhaseSpaceTransversal d).repr c))
            (principalA d : Mat(2, ℤ)) *
          principalDilogValue d
            (shiftRationalPoint d ((canonicalPhaseSpaceTransversal d).repr c - p)) *
          principalDilogValue d
            (shiftRationalPoint d (-(canonicalPhaseSpaceTransversal d).repr c))) -
        (Real.sqrt (principalDilogOrder d) : ℂ) *
          principalDilogValue d (shiftRationalPoint d (-p)) =
      if intPhaseSpaceMod d p = 0 then (d : ℂ) ^ 2 else 0 := by
  have hdne : (d : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne (d : ℕ))
  have hconj := principalDilogConvolutionConj d (-p)
  field_simp [hdne] at hconj
  have hsqrt : (Real.sqrt (principalDilogOrder d) : ℂ) =
      (d : ℂ) * (Real.sqrt ((d : ℝ) - 3) : ℂ) :=
    ofReal_sqrt_principalDilogOrder d d.property
  rw [principalDilogConvolution_reindex_sum d p, hconj, hsqrt]
  by_cases hp : intPhaseSpaceMod d p = 0
  · have hpneg : intPhaseSpaceMod d (-p) = 0 := by
      rw [intPhaseSpaceMod_neg, hp, neg_zero]
    simp only [hp, hpneg, ite_true]
    ring
  · have hpneg : intPhaseSpaceMod d (-p) ≠ 0 := by
      intro hn
      rw [intPhaseSpaceMod_neg] at hn
      exact hp (neg_eq_zero.mp hn)
    simp only [hp, hpneg, ite_false]
    ring

/-! ### The principal Twisted Convolution theorems

The finite identity from `principalDilogConvolutionConj_sum_neg` proves
`PrincipalFiniteShiftTCC`; the equivalence of `SICs.Principal.Construction.TCCFiniteForm`
carries it to the real shift at `λ = 1`. -/

/-- **The finite form of the principal Twisted Convolution Conjecture at `λ = 1` holds**, by
[RW26, Radchenko, Wheeler (2026), Theorem 7, `thm:ghostsic`]: for every `d > 3` and `p ∈ ℤ²`,
`∑_q ξ_d^{⟨p, q⟩} ν̃_d(q)/ν̃_d(q - p) = d² δ_{p ≡ 0}`. This discharges the `λ = 1` clause of
[AFK25, Conjecture 1.35, `cnj:tci`] for the principal family, combining
`principalPhasedShiftSum_one_eq`, `principalDilogConvolutionConj_sum_neg`, and
`principalDilogBridgePhase_of_mod_eq_zero` on the zero class. -/
theorem principalFiniteShiftTCC : PrincipalFiniteShiftTCC := by
  intro d p
  rw [principalPhasedShiftSum_one_eq d p,
    principalDilogConvolutionConj_sum_neg d p]
  by_cases hp : intPhaseSpaceMod d p = 0
  · have hpneg : intPhaseSpaceMod d (-p) = 0 := by
      rw [intPhaseSpaceMod_neg, hp, neg_zero]
    simp only [hp, ite_true, principalDilogBridgePhase_of_mod_eq_zero d (-p) hpneg]
    norm_num
  · simp only [hp, ite_false]
    ring

/-- **The principal-family real restriction of [AFK25, Conjecture 1.35, `cnj:tci`] at `λ = 1`
holds**, by [RW26, Radchenko, Wheeler (2026), Theorem 7, `thm:ghostsic`]: the finite form
`principalFiniteShiftTCC` through `principalFiniteShiftTCC_iff`. -/
theorem principalRealShiftTCC : PrincipalRealShiftTCC :=
  principalFiniteShiftTCC_iff.mp principalFiniteShiftTCC

/-- **`λ = 1` is a principal real shift in every dimension `d > 3`**: the `λ = 1` clause of
[AFK25, Conjecture 1.35, `cnj:tci`] for the principal family, proved by
[RW26, Radchenko, Wheeler (2026), Theorem 7, `thm:ghostsic`]. -/
theorem isPrincipalRealShift_one (d : RankOneDimension) : IsPrincipalRealShift d 1 :=
  principalRealShiftTCC d

end SIC

end
