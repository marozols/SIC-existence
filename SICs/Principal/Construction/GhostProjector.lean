/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Ghost.PhasedOverlaps
import SICs.Principal.Ghost.Candidate

/-!
# The Principal Ghost Projector

Idempotency of `principalGhostCandidate` from the exact real shift.

This file proves the idempotency step in the principal-family specialization of [AFK25, Theorem
1.45, `thm:ghstExist`]. It is downstream of `SICs.Principal.Cocycle.Real` to avoid an import cycle:
the exact real cocycle is defined using the explicit overlap from `SICs.Principal.Ghost.Overlaps`,
while the proof here converts its Twisted Convolution identity back into the displacement-operator
convolution satisfied by that overlap. The phase identities and coefficient comparisons are in
`SICs.Principal.Ghost.PhasedOverlaps`.

The analytic origin value used in [AFK25, Lemma 5.9, `lem:nu01overnu0val`] is supplied
unconditionally by `doubleSine'_one_principalRoot_pow_three`. Consequently, the exact principal
real shift is the only hypothesis of the final idempotency theorem.

## Main results

- `principalExcludedConvolution`: the nonzero coefficient identity in the square of the ghost
  displacement expansion.
- `principalGhostCandidate_idempotent_of_realShift`: idempotency conditional on the
  exact principal real
  shift.

## References

- [AFK25, proof of Theorem 1.45, `thm:ghstExist`, subsection `sbsc:proofofghosttheorem`]
- [AFK25, Lemma 5.9, `lem:nu01overnu0val`, and equation (1.49), `eq:tcc`]
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### The nonzero convolution coefficients

For a nonzero output residue, the real-shift identity gives a vanishing autocorrelation of phased
overlaps. Removing the two endpoints where the nonzero-overlap expansion omits the origin leaves
the coefficient required in the square of the ghost candidate.
-/

/-- An exact real shift makes every nonzero phased-overlap autocorrelation vanish. -/
private lemma principalPhasedGhostOverlap_autocorrelation (d : RankOneDimension)
    (hshift : IsPrincipalRealShift d 1) (p : IntPhaseSpace)
    (I : PhaseSpaceTransversal d) (hI0 : I.repr 0 = 0)
    (hIp : I.repr (intPhaseSpaceMod d p) = p)
    (hp : intPhaseSpaceMod d p ≠ 0) :
    (∑ q : PhaseSpaceMod d,
      displacementPhase d ^ intSymplecticForm p (I.repr q) *
        principalPhasedGhostOverlap d (I.repr q) /
          principalPhasedGhostOverlap d (I.repr q - p)) = 0 := by
  let ph := fun x : IntPhaseSpace =>
    (principalRankOneAdmissibleTuple d).sfPhase (principalA d) x
  let F := principalSFModularCocycleAd d
  have hconv := hshift.2 p I hI0 hIp
  rw [ite_eq_right hp] at hconv
  have hpoint (q : PhaseSpaceMod d) :
      displacementPhase d ^ intSymplecticForm p (I.repr q) *
          principalPhasedGhostOverlap d (I.repr q) /
            principalPhasedGhostOverlap d (I.repr q - p) =
        (ph 0 / ph (-p)) *
          (standardRoot d ^ intSymplecticForm p
              (shiftZaunerAction 1 (principalU d : Mat(2, ℤ)) (I.repr q)) *
            F (I.repr q) * principalSFModularCocycleAdInv d (I.repr q - p)) := by
    rw [principalSFModularCocycleAdInv_eq_inv]
    change displacementPhase d ^ intSymplecticForm p (I.repr q) *
        (ph (I.repr q) * F (I.repr q)) /
          (ph (I.repr q - p) * F (I.repr q - p)) = _
    have hphase := principalSFPhase_convolution_identity d p (I.repr q)
    change standardRoot d ^ intSymplecticForm p
        (shiftZaunerAction 1 (principalU d : Mat(2, ℤ)) (I.repr q)) *
          ph (I.repr q - p) * ph 0 =
        ph (-p) * ph (I.repr q) * displacementPhase d ^ intSymplecticForm p (I.repr q) at hphase
    have hratio : displacementPhase d ^ intSymplecticForm p (I.repr q) * ph (I.repr q) /
          ph (I.repr q - p) =
        (ph 0 / ph (-p)) *
          standardRoot d ^ intSymplecticForm p
            (shiftZaunerAction 1 (principalU d : Mat(2, ℤ)) (I.repr q)) := by
      apply (div_eq_iff (principalSFPhase_ne_zero d (I.repr q - p))).2
      rw [show (ph 0 / ph (-p)) *
          standardRoot d ^ intSymplecticForm p
            (shiftZaunerAction 1 (principalU d : Mat(2, ℤ)) (I.repr q)) *
          ph (I.repr q - p) =
        (ph 0 * standardRoot d ^ intSymplecticForm p
            (shiftZaunerAction 1 (principalU d : Mat(2, ℤ)) (I.repr q)) *
          ph (I.repr q - p)) / ph (-p) by rw [div_eq_mul_inv]; ring]
      apply (eq_div_iff (principalSFPhase_ne_zero d (-p))).2
      calc
        _ = ph (-p) * ph (I.repr q) *
            displacementPhase d ^ intSymplecticForm p (I.repr q) := by ring
        _ = standardRoot d ^ intSymplecticForm p
              (shiftZaunerAction 1 (principalU d : Mat(2, ℤ)) (I.repr q)) *
            ph (I.repr q - p) * ph 0 := hphase.symm
        _ = _ := by ring
    calc
      _ = (displacementPhase d ^ intSymplecticForm p (I.repr q) * ph (I.repr q) /
          ph (I.repr q - p)) * (F (I.repr q) / F (I.repr q - p)) := by
        field_simp [principalSFPhase_ne_zero d, principalSFModularCocycleAd_ne_zero d]
      _ = ((ph 0 / ph (-p)) *
          standardRoot d ^ intSymplecticForm p
            (shiftZaunerAction 1 (principalU d : Mat(2, ℤ)) (I.repr q))) *
          (F (I.repr q) / F (I.repr q - p)) := by rw [hratio]
      _ = _ := by
        rw [div_eq_mul_inv]
        ring
  rw [Finset.sum_congr rfl fun q _ => hpoint q, ← Finset.mul_sum]
  unfold principalRealShiftConvolutionSum at hconv
  rw [hconv, mul_zero]

/-- The complex form of `principalNormGhostOverlapReal_zero_add_inv`. -/
private lemma principalPhasedGhostOverlap_zero_add_inv_complex
    (d : RankOneDimension) :
    principalPhasedGhostOverlap d 0 + (principalPhasedGhostOverlap d 0)⁻¹ =
      -(((d : ℂ) - 2) * (Real.sqrt ((d : ℝ) + 1) : ℂ)) := by
  have hreal := principalNormGhostOverlapReal_zero_add_inv d
  have hcast : ((principalNormGhostOverlapReal d 0 : ℝ) : ℂ) =
      principalPhasedGhostOverlap d 0 := by
    rw [principalPhasedGhostOverlap_zero]
    exact ofReal_principalNormGhostOverlapReal d 0
  rw [← hcast, ← Complex.ofReal_inv, ← Complex.ofReal_add]
  exact_mod_cast hreal

/-- For a nonzero output residue, evaluates the two excluded convolution endpoints and converts
the vanishing phased autocorrelation into the coefficient required for idempotency. -/
lemma principalExcludedConvolution (d : RankOneDimension)
    (hshift : IsPrincipalRealShift d 1)
    (I : PhaseSpaceTransversal d) (hI0 : I.repr 0 = 0)
    (p : PhaseSpaceMod d) (hp : p ≠ 0) :
    (∑ q : PhaseSpaceMod d, if q = 0 ∨ q = p then 0 else
      displacementPhase d ^ intSymplecticForm (I.repr p) (I.repr q) *
        principalNormGhostOverlap d (I.repr p - I.repr q) *
        principalNormGhostOverlap d (I.repr q)) =
      ((d : ℂ) - 2) * (Real.sqrt ((d : ℝ) + 1) : ℂ) *
        principalNormGhostOverlap d (I.repr p) := by
  let P := I.repr p
  have hPmod : intPhaseSpaceMod d P = p := I.residue_repr p
  have hPne : intPhaseSpaceMod d P ≠ 0 := by rw [hPmod]; exact hp
  have hauto := principalPhasedGhostOverlap_autocorrelation d hshift P I hI0
    (by rw [hPmod]) hPne
  let A := principalPhasedGhostOverlap d 0 / principalPhasedGhostOverlap d (-P)
  let B := principalPhasedGhostOverlap d P / principalPhasedGhostOverlap d 0
  let E := fun q : PhaseSpaceMod d =>
    displacementPhase d ^ intSymplecticForm P (I.repr q) *
      principalNormGhostOverlap d (P - I.repr q) *
      principalNormGhostOverlap d (I.repr q)
  have hterm (q : PhaseSpaceMod d) :
      displacementPhase d ^ intSymplecticForm P (I.repr q) *
          principalPhasedGhostOverlap d (I.repr q) /
            principalPhasedGhostOverlap d (I.repr q - P) =
        (if q = 0 then A else 0) + (if q = p then B else 0) +
          (if q = 0 ∨ q = p then 0 else E q) := by
    by_cases hq0 : q = 0
    · subst q
      simp [A, hI0, intSymplecticForm, Ne.symm hp]
    by_cases hqp : q = p
    · subst q
      rw [ite_eq_right hq0, ite_eq_left rfl, ite_eq_left (Or.inr rfl), zero_add]
      simp only [P, sub_self]
      rw [show intSymplecticForm (I.repr p) (I.repr p) = 0 by
        simp [intSymplecticForm]
        ring, zpow_zero, one_mul]
      dsimp only [B]
      ring
    have hqne : intPhaseSpaceMod d (I.repr q) ≠ 0 := by
      rw [I.residue_repr]
      exact hq0
    have hdiffmod : intPhaseSpaceMod d (I.repr q - P) = q - p := by
      funext i
      have hq := congrFun (I.residue_repr q) i
      have hp' := congrFun hPmod i
      simpa [intPhaseSpaceMod] using congrArg₂ (· - ·) hq hp'
    have hdiffne : intPhaseSpaceMod d (I.repr q - P) ≠ 0 := by
      rw [hdiffmod]
      exact sub_ne_zero.mpr hqp
    have hμq := principalPhasedGhostOverlap_eq_overlap d (I.repr q) hqne
    have hμdiff := principalPhasedGhostOverlap_eq_overlap d (I.repr q - P) hdiffne
    have hrecip := principalNormGhostOverlap_reciprocal d (I.repr q - P) hdiffne
    have hneg : -(I.repr q - P) = P - I.repr q := by
      funext i
      simp
    rw [hneg] at hrecip
    have hinv : (principalNormGhostOverlap d (I.repr q - P))⁻¹ =
        principalNormGhostOverlap d (P - I.repr q) :=
      (eq_inv_of_mul_eq_one_right hrecip).symm
    rw [ite_eq_right hq0, ite_eq_right hqp, ite_eq_right (not_or_intro hq0 hqp), zero_add, hμq,
      hμdiff, div_eq_mul_inv, hinv]
    dsimp only [E]
    ring
  have hsum :
      (∑ q : PhaseSpaceMod d,
        displacementPhase d ^ intSymplecticForm P (I.repr q) *
          principalPhasedGhostOverlap d (I.repr q) /
            principalPhasedGhostOverlap d (I.repr q - P)) =
        A + B + ∑ q : PhaseSpaceMod d, if q = 0 ∨ q = p then 0 else E q := by
    rw [Finset.sum_congr rfl fun q _ => hterm q, Finset.sum_add_distrib,
      Finset.sum_add_distrib]
    simp
  have hends : A + B =
      -(((d : ℂ) - 2) * (Real.sqrt ((d : ℝ) + 1) : ℂ)) *
        principalNormGhostOverlap d P := by
    have hμP := principalPhasedGhostOverlap_eq_overlap d P hPne
    have hnegP : intPhaseSpaceMod d (-P) ≠ 0 := by
      have hnegmod : intPhaseSpaceMod d (-P) = -(intPhaseSpaceMod d P) := by
        funext i
        simp [intPhaseSpaceMod]
      intro h
      apply hPne
      rw [hnegmod] at h
      exact neg_eq_zero.mp h
    have hμneg := principalPhasedGhostOverlap_eq_overlap d (-P) hnegP
    have hrecip := principalNormGhostOverlap_reciprocal d P hPne
    have hinv : principalNormGhostOverlap d (-P) =
        (principalNormGhostOverlap d P)⁻¹ := eq_inv_of_mul_eq_one_right hrecip
    have hνne := principalNormGhostOverlap_ne_zero d P
    have hμ0ne := principalPhasedGhostOverlap_ne_zero d 0
    dsimp only [A, B]
    rw [hμP, hμneg, hinv, div_inv_eq_mul, div_eq_mul_inv]
    calc
      _ = (principalPhasedGhostOverlap d 0 + (principalPhasedGhostOverlap d 0)⁻¹) *
          principalNormGhostOverlap d P := by ring
      _ = _ := by rw [principalPhasedGhostOverlap_zero_add_inv_complex d]
  rw [hsum] at hauto
  change (∑ q : PhaseSpaceMod d, if q = 0 ∨ q = p then 0 else E q) = _
  rw [show (∑ q : PhaseSpaceMod d, if q = 0 ∨ q = p then 0 else E q) = -(A + B) by
    linear_combination hauto]
  rw [hends]
  ring

/-! ### The full nonidentity sum

Reciprocity and the preceding nonzero coefficients evaluate the square of the entire nonidentity
part of the displacement expansion through the General square law
`transversalDisplacementSum_sq_eq_of_reciprocal`.
-/

/-- The rank-one ghost normalization prefactor in dimension `d` reduces to
`1 / (d * sqrt (d + 1))`. -/
private lemma principalGhostPrefactor_reduced (d : ℕ) (hd : 3 < d) :
    Real.sqrt (((1 : ℝ) * ((d : ℝ) - 1)) /
        ((d : ℝ) ^ 2 * ((d : ℝ) ^ 2 - 1))) =
      1 / ((d : ℝ) * Real.sqrt ((d : ℝ) + 1)) := by
  have hdR : (3 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hd1 : (d : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  have hd2m1 : (d : ℝ) ^ 2 - 1 ≠ 0 := ne_of_gt (by nlinarith)
  have harg : ((1 : ℝ) * ((d : ℝ) - 1)) /
      ((d : ℝ) ^ 2 * ((d : ℝ) ^ 2 - 1)) =
      1 / ((d : ℝ) ^ 2 * ((d : ℝ) + 1)) := by
    field_simp [hd0, hd1, hd2m1]
    ring
  rw [harg, Real.sqrt_div (by positivity), Real.sqrt_one,
    Real.sqrt_mul (sq_nonneg (d : ℝ)), Real.sqrt_sq_eq_abs, abs_of_pos (by positivity)]

/-- The nonidentity part of the principal ghost displacement expansion satisfies its required
quadratic relation.

Specializes `SIC.transversalDisplacementSum_sq_eq_of_reciprocal`, the square law whose
hypotheses are the principal reciprocity `principalNormGhostOverlap_reciprocal` and the
excluded convolution `principalExcludedConvolution` of the exact real shift. The relation itself
is the rank-one case of the one displayed in the proof of [AFK25, Theorem 1.45,
`thm:ghstExist`, subsection `sbsc:proofofghosttheorem`], whose general-rank coefficients
`(d² - 1)` and `(d - 2r)√(d_j + 1)` become, at `r = 1`, `d_j = d`, the `(d² - 1)` and
`(d - 2)√(d + 1)` below. -/
lemma principalOverlapDisplacementSum_sq (d : RankOneDimension)
    (hshift : IsPrincipalRealShift d 1)
    (I : PhaseSpaceTransversal d) (hI0 : I.repr 0 = 0) :
    (∑ q : PhaseSpaceMod d, if q = 0 then 0 else
        principalNormGhostOverlap d (I.repr q) • integerDisplacement d (I.repr q)) ^ 2 =
      ((d : ℂ) ^ 2 - 1) • (1 : Mat(d, ℂ)) +
        (((d : ℂ) - 2) * (Real.sqrt ((d : ℝ) + 1) : ℂ)) •
          (∑ q : PhaseSpaceMod d, if q = 0 then 0 else
            principalNormGhostOverlap d (I.repr q) • integerDisplacement d (I.repr q)) := by
  let w := principalNormGhostOverlap d
  have hw : RespectsPhaseSpaceResiduesAwayFromZero d
      (fun p => w p • integerDisplacement d p) := by
    intro p p' hmod hp
    dsimp only [w]
    rw [principalNormGhostOverlap_transport d p p' hmod,
      integerDisplacement_change_representative hmod, smul_smul]
    congr 1
    calc
      _ = principalNormGhostOverlap d p *
          (displacementPhase d ^ intSymplecticForm p' p *
            displacementPhase d ^ (-intSymplecticForm p' p)) := by ring
      _ = principalNormGhostOverlap d p := by
        rw [← zpow_add₀ (displacementPhase_ne_zero d), add_neg_cancel, zpow_zero, mul_one]
  exact transversalDisplacementSum_sq_eq_of_reciprocal w hw I hI0 _
    (fun p hp => principalNormGhostOverlap_reciprocal d p hp)
    (fun p hp => principalExcludedConvolution d hshift I hI0 p hp)

/-! ### Idempotency of the principal ghost candidate

The candidate is the identity plus the nonzero displacement sum with the normalization of
[AFK25, Definition 1.43, `dfn:CandidateGhostAndSICFiducials`]. Substituting the squared-sum
identity reduces idempotency to scalar arithmetic.
-/

/-- Rewrite `principalGhostCandidate` as the identity plus its explicit nonzero displacement sum. -/
lemma principalGhostCandidate_expansion (d : RankOneDimension) :
    principalGhostCandidate d =
      ((1 : ℂ) / (d : ℂ)) • (1 : Mat(d, ℂ)) +
        Real.sqrt (((1 : ℝ) * ((d : ℝ) - 1)) /
          ((d : ℝ) ^ 2 * ((d : ℝ) ^ 2 - 1))) •
          ∑ q : PhaseSpaceMod d, if q = 0 then 0 else
            principalNormGhostOverlap d ((canonicalPhaseSpaceTransversal d).repr q) •
              integerDisplacement d ((canonicalPhaseSpaceTransversal d).repr q) := by
  have hsum : (∑ q : PhaseSpaceMod d, if q = 0 then 0 else
      (principalGhostFiducialData d).overlaps.normalized
          ((principalGhostFiducialData d).twistedIndex
            ((canonicalPhaseSpaceTransversal d).repr q)) •
        integerDisplacement d ((canonicalPhaseSpaceTransversal d).repr q)) =
      ∑ q : PhaseSpaceMod d, if q = 0 then 0 else
        principalNormGhostOverlap d ((canonicalPhaseSpaceTransversal d).repr q) •
          integerDisplacement d ((canonicalPhaseSpaceTransversal d).repr q) := by
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq : q = 0
    · simp [hq]
    · rw [ite_eq_right hq, ite_eq_right hq]
      have hpull := congrFun (principalGhostFiducialData_integerPullback d)
        ((canonicalPhaseSpaceTransversal d).repr q)
      have hcoeff : (((principalGhostFiducialData d).overlaps.normalized
          ((principalGhostFiducialData d).twistedIndex
            ((canonicalPhaseSpaceTransversal d).repr q)) : ℝ) : ℂ) =
          principalNormGhostOverlap d ((canonicalPhaseSpaceTransversal d).repr q) := by
        simpa [GhostOverlapData.integerPullback, GhostFiducialData.twistedIndex,
        principalGhostFiducialData, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hpull
      ext i j
      simp [hcoeff]
  rw [principalGhostCandidate, ghostFiducialMatrix]
  rw [hsum]
  congr 2
  · push_cast
    ring
  · rw [ghostFiducialPrefactor]
    norm_num

/-- **Principal convolution-to-idempotency.** An exact principal real shift at `λ = 1` makes the
explicit principal ghost candidate idempotent; used by `principalGhostCandidate_idempotent`. The
required origin value is supplied unconditionally by `doubleSine'_one_principalRoot_pow_three`. -/
theorem principalGhostCandidate_idempotent_of_realShift (d : RankOneDimension)
    (hshift : IsPrincipalRealShift d 1) :
    principalGhostCandidate d ^ 2 = principalGhostCandidate d := by
  let I := canonicalPhaseSpaceTransversal d
  let S := ∑ q : PhaseSpaceMod d, if q = 0 then 0 else
    principalNormGhostOverlap d (I.repr q) • integerDisplacement d (I.repr q)
  have hI0 : I.repr 0 = 0 := by
    funext i
    simp [I, canonicalPhaseSpaceTransversal]
  have hSsq : S ^ 2 = ((d : ℂ) ^ 2 - 1) • (1 : Mat(d, ℂ)) +
      (((d : ℂ) - 2) * (Real.sqrt ((d : ℝ) + 1) : ℂ)) • S := by
    exact principalOverlapDisplacementSum_sq d hshift I hI0
  have hexp := principalGhostCandidate_expansion d
  change principalGhostCandidate d =
      ((1 : ℂ) / (d : ℂ)) • (1 : Mat(d, ℂ)) +
        Real.sqrt (((1 : ℝ) * ((d : ℝ) - 1)) /
          ((d : ℝ) ^ 2 * ((d : ℝ) ^ 2 - 1))) • S at hexp
  rw [hexp, principalGhostPrefactor_reduced d d.property]
  let a : ℂ := (1 : ℂ) / (d : ℂ)
  let R : ℝ := Real.sqrt ((d : ℝ) + 1)
  let b : ℝ := 1 / ((d : ℝ) * R)
  change (a • (1 : Mat(d, ℂ)) + b • S) ^ 2 =
    a • (1 : Mat(d, ℂ)) + b • S
  let bc : ℂ := (b : ℂ)
  change (a • (1 : Mat(d, ℂ)) + bc • S) ^ 2 =
    a • (1 : Mat(d, ℂ)) + bc • S
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne (d : ℕ))
  have hRpos : 0 < R := by
    dsimp only [R]
    exact Real.sqrt_pos.mpr (by positivity)
  have hR0r : R ≠ 0 := ne_of_gt hRpos
  have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR0r
  have hR2r : R ^ 2 = (d : ℝ) + 1 := by
    dsimp only [R]
    rw [Real.sq_sqrt (by positivity)]
  have hR2 : (R : ℂ) ^ 2 = (d : ℂ) + 1 := by exact_mod_cast hR2r
  have hbc : bc = 1 / ((d : ℂ) * (R : ℂ)) := by
    dsimp only [bc, b]
    push_cast
    rfl
  have ha0 : a ^ 2 + bc ^ 2 * ((d : ℂ) ^ 2 - 1) = a := by
    rw [hbc]
    dsimp only [a]
    field_simp [hd0, hR0]
    rw [hR2]
    ring
  have ha1 : 2 * a * bc + bc ^ 2 * (((d : ℂ) - 2) * (R : ℂ)) = bc := by
    rw [hbc]
    dsimp only [a]
    field_simp [hd0, hR0]
    ring
  exact smul_one_add_smul_sq_eq_self hSsq ha0 ha1

end SIC

end
