/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Ghost.PhasedOverlaps

/-!
# The Principal Convolution Summand

The `μ`-form of the principal convolution summand, the unconditional origin case, and coprimality
at `λ = 1`.

This file prepares the principal convolution identity of [AFK25, Definition 1.34, `dfn:shift`] for
its finite form in `SICs.Principal.Construction.TCCFiniteForm`. Each summand is written in its
`μ`-form: a `q`-independent SF-phase unit times `ξ_d^{(2λ-1)⟨p,q⟩}` times a ratio of two phased
overlaps (`principalRealShiftSummand_mul_eq`). The phased overlap is constant on the zero residue
class, since the principal SF phase and the exact real cocycle both reduce there to the origin.

The origin case of the convolution identity is proved here unconditionally, for every
shift (`principalRealShiftConvolutionSum_zero`): by the inverse-cocycle relation every summand
is `1`.  The open content of `IsPrincipalRealShift` is therefore exactly the classes
`p ≢ 0 (mod d)`. The coprimality half of the shift condition at `λ = 1` also holds
unconditionally, since `d + 1` is coprime to `d`.

## Main declarations

- `principalPhasedGhostOverlap_of_mod_eq_zero`: the phased overlap is constant on the zero
  residue class.
- `principalRealShiftSummand_mul_eq`: the `μ`-form of the principal convolution summand.
- `principalRealShiftConvolutionSum_zero`: the `p = 0` convolution identity, unconditionally.
- `isShiftCoprime_principal_one`: the coprimality half of the shift `λ = 1`.

## References

- [AFK25, Definition 1.34, `dfn:shift`]
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### The zero residue class

The principal SF phase transports an index to its canonical representative, which is the origin on
the zero residue class; the exact real cocycle reduces in the same way. Hence the phased overlap
is constant on that class.
-/

/-- The principal SF phase is constant on the zero residue class: the canonical representative
is the origin, and the transport factor pairs the index against the zero vector. -/
lemma principalSFPhase_of_mod_eq_zero (d : RankOneDimension)
    (p : IntPhaseSpace) (hp : intPhaseSpaceMod d p = 0) :
    (principalRankOneAdmissibleTuple d).sfPhase (principalA d) p =
      (principalRankOneAdmissibleTuple d).sfPhase (principalA d) 0 := by
  have hcan : canonicalIntPhaseSpaceRep d p = 0 := by
    funext i
    have hzero : ((p i : ZMod d)) = 0 := congrFun hp i
    have hdvd : (d : ℤ) ∣ p i := (ZMod.intCast_zmod_eq_zero_iff_dvd _ d).mp hzero
    exact Int.emod_eq_zero_of_dvd hdvd
  rw [principalSFPhase_transport d p, hcan,
    show intSymplecticForm p 0 = 0 by simp [intSymplecticForm], zpow_zero, one_mul]

/-- On the zero residue class the phased overlap is constant. -/
lemma principalPhasedGhostOverlap_of_mod_eq_zero (d : RankOneDimension)
    (p : IntPhaseSpace) (hp : intPhaseSpaceMod d p = 0) :
    principalPhasedGhostOverlap d p = principalPhasedGhostOverlap d 0 := by
  have hF : principalSFModularCocycleAd d p = principalSFModularCocycleAd d 0 :=
    principalSFModularCocycleAd_eq_of_modEq d 0 p
      (by rw [hp]; funext i; simp [intPhaseSpaceMod])
  rw [principalPhasedGhostOverlap, principalPhasedGhostOverlap,
    principalSFPhase_of_mod_eq_zero d p hp, hF]

/-! ### The `μ`-form of the convolution summand

Dividing the phased overlap at `q` by that at `q-p` rewrites the shift convolution in ratio form.
Nonvanishing of the cocycle justifies this normalization at every index.
-/

/-- The `μ`-form of the principal real convolution summand, for an arbitrary shift `λ`: cleared
of denominators, the summand times the nonzero factor `Φ_d(0)·ν̃_d(q-p)` equals
`Φ_d(-p)·ξ_d^{(2λ-1)⟨p,q⟩}·ν̃_d(q)`. This is the exact-value form of the phase manipulation of
`principalSFPhase_convolution_identity`, with the shift kept general: the `λ`-dependence of
the summand is entirely the character `ω_d^{(λ-1)⟨p,q⟩}`, which combines with the `λ = 1` identity
`principalSFPhase_convolution_identity` into the displayed exponent. -/
theorem principalRealShiftSummand_mul_eq (d : RankOneDimension)
    (lam : ℤ) (p q : IntPhaseSpace) :
    standardRoot d ^ intSymplecticForm p
        (shiftZaunerAction lam (principalU d : Mat(2, ℤ)) q) *
        principalSFModularCocycleAd d q *
        principalSFModularCocycleAdInv d (q - p) *
        ((principalRankOneAdmissibleTuple d).sfPhase (principalA d)
            (0 : IntPhaseSpace) *
          principalPhasedGhostOverlap d (q - p)) =
      (principalRankOneAdmissibleTuple d).sfPhase (principalA d) (-p) *
        displacementPhase d ^ ((2 * lam - 1) * intSymplecticForm p q) *
        principalPhasedGhostOverlap d q := by
  have hsym : intSymplecticForm p
      (shiftZaunerAction lam (principalU d : Mat(2, ℤ)) q) =
      intSymplecticForm p
          (shiftZaunerAction 1 (principalU d : Mat(2, ℤ)) q) +
        (lam - 1) * intSymplecticForm p q := by
    have hact := shiftZaunerAction_add 1 (lam - 1)
      (principalU d : Mat(2, ℤ)) q
    rw [show (1 : ℤ) + (lam - 1) = lam by ring] at hact
    rw [hact, intSymplecticForm_add_smul]
  have hphase := principalSFPhase_convolution_identity d p q
  have hxi : standardRoot d ^ ((lam - 1) * intSymplecticForm p q) *
      displacementPhase d ^ intSymplecticForm p q =
      displacementPhase d ^ ((2 * lam - 1) * intSymplecticForm p q) := by
    rw [← displacementPhase_sq]
    change (displacementPhase d ^ (2 : ℤ)) ^ ((lam - 1) * intSymplecticForm p q) * _ = _
    rw [← zpow_mul, ← zpow_add₀ (displacementPhase_ne_zero d)]
    congr 1
    ring
  have hcancel : (principalSFModularCocycleAd d (q - p))⁻¹ *
      principalSFModularCocycleAd d (q - p) = 1 :=
    inv_mul_cancel₀ (principalSFModularCocycleAd_ne_zero d (q - p))
  rw [principalSFModularCocycleAdInv_eq_inv, hsym, zpow_add₀ (standardRoot_ne_zero d),
    principalPhasedGhostOverlap, principalPhasedGhostOverlap]
  linear_combination (standardRoot d ^ intSymplecticForm p
        (shiftZaunerAction 1 (principalU d : Mat(2, ℤ)) q) *
      standardRoot d ^ ((lam - 1) * intSymplecticForm p q) *
      principalSFModularCocycleAd d q *
      (principalRankOneAdmissibleTuple d).sfPhase (principalA d) (0 : IntPhaseSpace) *
      (principalRankOneAdmissibleTuple d).sfPhase (principalA d) (q - p)) * hcancel +
    (standardRoot d ^ ((lam - 1) * intSymplecticForm p q) *
      principalSFModularCocycleAd d q) * hphase +
    ((principalRankOneAdmissibleTuple d).sfPhase (principalA d) (-p) *
      (principalRankOneAdmissibleTuple d).sfPhase (principalA d) q *
      principalSFModularCocycleAd d q) * hxi

/-! ### The origin case, unconditionally

At output index zero, reciprocity pairs every nonzero summand with its inverse. The separately
normalized origin term completes the convolution identity without a TCC assumption.
-/

/-- The `p = 0` instance of the principal convolution identity holds unconditionally, for every
shift `λ` and every transversal: the character is trivial and each summand collapses to `1` by
the inverse-cocycle relation.  The open content of `IsPrincipalRealShift` is therefore exactly
the classes `p ≢ 0 (mod d)`. -/
theorem principalRealShiftConvolutionSum_zero (d : RankOneDimension) (lam : ℤ)
    (I : PhaseSpaceTransversal d) :
    principalRealShiftConvolutionSum d lam I 0 = (d : ℂ) ^ 2 := by
  unfold principalRealShiftConvolutionSum
  have hterm (c : PhaseSpaceMod d) :
      (standardRoot d) ^ intSymplecticForm 0
          (shiftZaunerAction lam (principalU d : Mat(2, ℤ)) (I.repr c)) *
        principalSFModularCocycleAd d (I.repr c) *
        principalSFModularCocycleAdInv d (I.repr c - 0) = 1 := by
    rw [sub_zero, show intSymplecticForm 0
        (shiftZaunerAction lam (principalU d : Mat(2, ℤ)) (I.repr c)) = 0 by
      simp [intSymplecticForm], zpow_zero, one_mul, mul_comm]
    exact principalSFModularCocycleAdInv_mul_self d (I.repr c)
  rw [Finset.sum_congr rfl fun c _ => hterm c, Finset.sum_const, Finset.card_univ]
  have hcard : Fintype.card (PhaseSpaceMod d) = d ^ 2 := by simp [PhaseSpaceMod]
  rw [hcard, nsmul_eq_mul, mul_one]
  push_cast
  ring

/-! ### Coprimality at `λ = 1`

For the principal tuple the tower dimension `d_j` is `d`, so the coprimality condition at `λ = 1`
asks that `2·1 + d - 1 = d + 1` be coprime to `d`.
-/

/-- For the principal tuple the tower dimension `d_j` entering the shift conditions is `d`
itself: the tuple sits on the `m = 1` grid row. -/
lemma principalRankOneAdmissibleTuple_towerDimension (d : ℕ) (hd : 3 < d) :
    (principalRankOneAdmissibleTuple
      ⟨d, hd⟩).toAdmissibleTuple.triple.towerDimension = d := by
  change ((principalRankOneAdmissibleTuple
    ⟨d, hd⟩).triple.toAdmissibleTriple).towerDimension = d
  rw [RankOneAdmissibleTriple.toAdmissibleTriple_towerDimension]
  have hdim := (principalRankOneAdmissibleTuple ⟨d, hd⟩).d_eq_dimension
  rw [principalRankOneAdmissibleTuple_d] at hdim
  exact hdim.symm

/-- The coprimality condition holds unconditionally at `λ = 1` for the principal tuple:
`2·1 + d - 1 = d + 1` is coprime to `d`. -/
lemma isShiftCoprime_principal_one (d : ℕ) (hd : 3 < d) :
    (principalRankOneAdmissibleTuple ⟨d, hd⟩).IsShiftCoprime 1 := by
  unfold RankOneAdmissibleTuple.IsShiftCoprime AdmissibleTuple.IsShiftCoprime
  rw [principalRankOneAdmissibleTuple_towerDimension d hd,
    RankOneAdmissibleTuple.toAdmissibleTuple_d, principalRankOneAdmissibleTuple_d]
  exact ⟨1, -1, by ring⟩

end SIC

end
