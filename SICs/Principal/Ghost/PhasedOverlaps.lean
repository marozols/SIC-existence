/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Cocycle.ModularValues

/-!
# Phased Ghost Overlaps of the Principal Family

The principal SF phase algebra, the phased overlap, and its comparison with the explicit ghost
overlap at the origin and outside the zero residue class.

This module develops [AFK25, Definitions 1.30 and 1.32, `dfn:SFKPhase`, `dfn:GhostOverlaps`] for
the principal tuple. It supplies the coefficient identities used by
`SICs.Principal.Construction.GhostProjector` and the phase algebra used by
`SICs.Principal.Construction.ShiftSymmetry`.

## The argument

The principal form gives an explicit relation between its polar form and the symplectic pairing.
Together with the parity of `s_d`, this converts the SF phases in the raw cocycle convolution into
the displacement phase. The general phase-transport theorem then reduces each integer index to
its canonical representative.

The independently computed three-double-sine product agrees with the phased principal cocycle
outside the zero residue class. At the literal origin, the phase's exponential cancels the
cocycle's exponential, leaving the sign `(-1)^{s_d(0)} = -1`. No identification is asserted at
other integral characteristics, where the auxiliary principal coefficient extension need not agree
with the source cocycle.

## Main declarations

- `principalSFPhase_convolution_identity` and `principalSFPhase_transport`: the phase identities.
- `principalPhasedGhostOverlap`: the phased principal value, with its origin, product, and
  nonvanishing lemmas.

## References

- [AFK25, Definitions 1.30 and 1.32, `dfn:SFKPhase`, `dfn:GhostOverlaps`]
- [AFK25, Lemma 5.9, `lem:nu01overnu0val`, and equation (1.49), `eq:tcc`]
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### Principal phase algebra

The general Weyl--Heisenberg multiplication law for integer lifts is
`SIC.integerDisplacement_mul`. This section supplies the principal SF-phase calculation that
turns the Twisted Convolution identity into the character occurring in that matrix product.
-/

/-- The phase identity that converts the raw principal SF-cocycle convolution into the convolution
of `principalPhasedGhostOverlap` used by
`principalGhostCandidate_idempotent_of_realShift`. -/
lemma principalSFPhase_convolution_identity (d : RankOneDimension)
    (p q : IntPhaseSpace) :
    standardRoot d ^ intSymplecticForm p
        (shiftZaunerAction 1 (principalU d : Mat(2, ℤ)) q) *
        (principalRankOneAdmissibleTuple d).sfPhase (principalA d) (q - p) *
        (principalRankOneAdmissibleTuple d).sfPhase (principalA d) 0 =
      (principalRankOneAdmissibleTuple d).sfPhase (principalA d) (-p) *
        (principalRankOneAdmissibleTuple d).sfPhase (principalA d) q *
        displacementPhase d ^ intSymplecticForm p q := by
  have hc : (principalRankOneAdmissibleTuple d).conductorRatio = 1 :=
    principalRankOneAdmissibleTuple_conductorRatio d
  let Q := principalOneSICForm d
  let e := intSymplecticForm p
    (shiftZaunerAction 1 (principalU d : Mat(2, ℤ)) q)
  let c := q 0 * p 1 + p 0 * q 1
  let t := intSymplecticForm p q
  have hs : sfSignExp d (q - p) + sfSignExp d 0 =
      sfSignExp d (-p) + sfSignExp d q - ((d + 1 : ℕ) : ℤ) * c := by
    simp [sfSignExp, c]
    ring
  have ha : 2 * e - Q.eval ((q - p) 0) ((q - p) 1) =
      (-Q.eval ((-p) 0) ((-p) 1) - Q.eval (q 0) (q 1) + t) + (d : ℤ) * t := by
    simp [e, t, intSymplecticForm, shiftZaunerAction, coe_principalU,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, Q, principalOneSICForm, BinaryQF.eval]
    ring
  have he : Even (t - c) := by
    refine ⟨-(p 0 * q 1), ?_⟩
    simp [t, c, intSymplecticForm]
    ring
  have hphase := neg_one_zpow_mul_displacementPhase_zpow_eq d
    (sfSignExp d (q - p) + sfSignExp d 0)
    (sfSignExp d (-p) + sfSignExp d q)
    (2 * e - Q.eval ((q - p) 0) ((q - p) 1))
    (-Q.eval ((-p) 0) ((-p) 1) - Q.eval (q 0) (q 1) + t) c t hs ha (he.mul_left _)
  have hphase' :
      (-1 : ℂ) ^ (sfSignExp d (q - p) + sfSignExp d 0) *
          displacementPhase d ^ (2 * e - (principalOneSICForm d).eval ((q - p) 0) ((q - p) 1)) =
        (-1 : ℂ) ^ (sfSignExp d (-p) + sfSignExp d q) *
          displacementPhase d ^ (-(principalOneSICForm d).eval ((-p) 0) ((-p) 1) -
            (principalOneSICForm d).eval (q 0) (q 1) + t) := by
    simpa only [Q] using hphase
  have hQ0 : (principalOneSICForm d).eval ((0 : IntPhaseSpace) 0)
      ((0 : IntPhaseSpace) 1) = 0 := by
    simp [principalOneSICForm, BinaryQF.eval]
  have homega : (displacementPhase d ^ 2) ^ e = displacementPhase d ^ (2 * e) := by
    change (displacementPhase d ^ (2 : ℤ)) ^ e = _
    rw [← zpow_mul]
  simp only [RankOneAdmissibleTuple.sfPhase_of_conductorRatio_eq_one _ hc,
    principalRankOneAdmissibleTuple_d, principalRankOneAdmissibleTuple_Q]
  rw [← displacementPhase_sq]
  rw [homega, hQ0, neg_zero, zpow_zero, mul_one]
  let E := Complex.exp (-Real.pi * Complex.I / 12 *
    (rademacherInvariant (principalA d) : ℂ))
  have hsignL : (-1 : ℂ) ^ sfSignExp d (q - p) * (-1 : ℂ) ^ sfSignExp d 0 =
      (-1 : ℂ) ^ (sfSignExp d (q - p) + sfSignExp d 0) := by
    rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  have hsignR : (-1 : ℂ) ^ sfSignExp d (-p) * (-1 : ℂ) ^ sfSignExp d q =
      (-1 : ℂ) ^ (sfSignExp d (-p) + sfSignExp d q) := by
    rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  have hrootL : displacementPhase d ^ (2 * e) *
      displacementPhase d ^ (-(principalOneSICForm d).eval ((q - p) 0) ((q - p) 1)) =
      displacementPhase d ^ (2 * e - (principalOneSICForm d).eval ((q - p) 0) ((q - p) 1)) := by
    rw [show 2 * e - (principalOneSICForm d).eval ((q - p) 0) ((q - p) 1) =
      2 * e + (-(principalOneSICForm d).eval ((q - p) 0) ((q - p) 1)) by ring,
      zpow_add₀ (displacementPhase_ne_zero d)]
  have hrootR : displacementPhase d ^ (-(principalOneSICForm d).eval ((-p) 0) ((-p) 1)) *
        displacementPhase d ^ (-(principalOneSICForm d).eval (q 0) (q 1)) *
          displacementPhase d ^ t =
      displacementPhase d ^ (-(principalOneSICForm d).eval ((-p) 0) ((-p) 1) -
        (principalOneSICForm d).eval (q 0) (q 1) + t) := by
    rw [show -(principalOneSICForm d).eval ((-p) 0) ((-p) 1) -
        (principalOneSICForm d).eval (q 0) (q 1) + t =
      (-(principalOneSICForm d).eval ((-p) 0) ((-p) 1) +
        (-(principalOneSICForm d).eval (q 0) (q 1))) + t by ring,
      zpow_add₀ (displacementPhase_ne_zero d), zpow_add₀ (displacementPhase_ne_zero d)]
  calc
    _ = E ^ 2 * ((-1 : ℂ) ^ (sfSignExp d (q - p) + sfSignExp d 0) *
        displacementPhase d ^ (2 * e - (principalOneSICForm d).eval ((q - p) 0) ((q - p) 1))) := by
      rw [← hsignL, ← hrootL]
      dsimp only [E, e]
      ring
    _ = E ^ 2 * ((-1 : ℂ) ^ (sfSignExp d (-p) + sfSignExp d q) *
        displacementPhase d ^ (-(principalOneSICForm d).eval ((-p) 0) ((-p) 1) -
          (principalOneSICForm d).eval (q 0) (q 1) + t)) := by rw [hphase']
    _ = _ := by
      rw [← hsignR, ← hrootR]
      dsimp only [E, t]
      ring

/-! ### Transporting the principal SF phase

The general phase-transport theorem applies directly to the principal tuple. This specialization
selects the canonical representative used by the explicit overlap.
-/

/-- The principal SF phase at an integer index differs from its canonical representative by the
symplectic phase required by displacement-operator transport. Specializes
`SIC.AdmissibleTuple.sfPhase_transport`. -/
lemma principalSFPhase_transport (d : RankOneDimension)
    (p : IntPhaseSpace) :
    (principalRankOneAdmissibleTuple d).sfPhase (principalA d) p =
      displacementPhase d ^ intSymplecticForm p (canonicalIntPhaseSpaceRep d p) *
        (principalRankOneAdmissibleTuple d).sfPhase (principalA d)
          (canonicalIntPhaseSpaceRep d p) := by
  have hmod := intPhaseSpaceMod_canonicalIntPhaseSpaceRep d p
  have htransport :=
    (principalRankOneAdmissibleTuple d).toAdmissibleTuple.sfPhase_transport
      (principalA d) (canonicalIntPhaseSpaceRep d p) p hmod.symm
  simpa only [RankOneAdmissibleTuple.toAdmissibleTuple_d,
    principalRankOneAdmissibleTuple_d,
    RankOneAdmissibleTuple.sfPhase_toAdmissibleTuple] using htransport

/-! ### Identifying cocycle and product overlaps

The phased principal cocycle agrees with the explicit three-double-sine overlap outside the zero
residue class and at the literal origin; other integral characteristics are not identified with
the origin.
-/

/-- The phased overlap `ν̃_d(p) = Φ_d(p) ש_{A_d}^{p/d}(ρ_d)` used as the coefficient in
the principal convolution-to-idempotency argument. -/
noncomputable def principalPhasedGhostOverlap (d : RankOneDimension)
    (p : IntPhaseSpace) : ℂ :=
  (principalRankOneAdmissibleTuple d).sfPhase (principalA d) p *
    principalSFModularCocycleAd d p

/-- At the literal origin the phased cocycle value is the explicit overlap. The sign factor
`(-1)^{s_d(0)} = -1` remains after the phase and cocycle exponentials cancel, and is built
into `principalNormGhostOverlap`. -/
lemma principalPhasedGhostOverlap_zero (d : RankOneDimension) :
    principalPhasedGhostOverlap d 0 = principalNormGhostOverlap d 0 := by
  exact sfPhase_mul_principalSFModularCocycleAdCanonical_zero d

/-- Away from the zero residue, the exact phased principal SF value equals the explicit
three-double-sine overlap used in `principalGhostCandidate`. -/
lemma principalPhasedGhostOverlap_eq_overlap (d : RankOneDimension)
    (p : IntPhaseSpace) (hp : intPhaseSpaceMod d p ≠ 0) :
    principalPhasedGhostOverlap d p = principalNormGhostOverlap d p := by
  let P := canonicalIntPhaseSpaceRep d p
  have hP0 : 0 ≤ P 0 := canonicalIntPhaseSpaceRep_nonneg (by omega) p 0
  have hP0' : P 0 < (d : ℤ) := canonicalIntPhaseSpaceRep_lt (by omega) p 0
  have hP1 : 0 ≤ P 1 := canonicalIntPhaseSpaceRep_nonneg (by omega) p 1
  have hP1' : P 1 < (d : ℤ) := canonicalIntPhaseSpaceRep_lt (by omega) p 1
  have hmod : intPhaseSpaceMod d P = intPhaseSpaceMod d p := by
    funext i
    exact (ZMod.intCast_eq_intCast_iff _ _ _).mpr (canonicalIntPhaseSpaceRep_emod d p i)
  have hPne : ¬(P 0 = 0 ∧ P 1 = 0) := by
    rintro ⟨h0, h1⟩
    apply hp
    funext i
    fin_cases i
    · simpa [intPhaseSpaceMod, h0] using (congrFun hmod 0).symm
    · simpa [intPhaseSpaceMod, h1] using (congrFun hmod 1).symm
  have hcanonical := sfPhase_mul_principalSFModularCocycleAdCanonical
    d d.property (P 0) (P 1) hP0 hP0' hP1 hP1' hPne
  have hPvec : ![P 0, P 1] = P := by
    funext i
    fin_cases i <;> rfl
  rw [hPvec] at hcanonical
  have hFc : principalSFModularCocycleAd d P =
      principalSFModularCocycleAdCanonical d (P 0) (P 1) := by
    unfold principalSFModularCocycleAd
    have hPP : canonicalIntPhaseSpaceRep d P = P :=
      canonicalIntPhaseSpaceRep_idem d p
    rw [hPP]
  have hF := principalSFModularCocycleAd_eq_of_modEq d P p hmod.symm
  rw [principalPhasedGhostOverlap, principalSFPhase_transport, hF, hFc, mul_assoc, hcanonical]
  rw [← principalNormGhostOverlap_canonRep d p hp]
  exact (principalNormGhostOverlap_transport d P p hmod.symm).symm

/-! ### Nonvanishing

The SF phase and the principal modular value are nonzero. Their product therefore supplies a
nonzero coefficient wherever the convolution identities divide by a phased overlap.
-/

/-- The principal SF phase is nonzero. -/
lemma principalSFPhase_ne_zero (d : RankOneDimension)
    (p : IntPhaseSpace) :
    (principalRankOneAdmissibleTuple d).sfPhase (principalA d) p ≠ 0 := by
  simpa only [RankOneAdmissibleTuple.sfPhase_toAdmissibleTuple] using
    (principalRankOneAdmissibleTuple d).toAdmissibleTuple.sfPhase_ne_zero (principalA d) p

/-- The principal phased ghost overlap is nonzero at every integer index. -/
lemma principalPhasedGhostOverlap_ne_zero (d : RankOneDimension)
    (p : IntPhaseSpace) : principalPhasedGhostOverlap d p ≠ 0 :=
  mul_ne_zero (principalSFPhase_ne_zero d p)
    (principalSFModularCocycleAd_ne_zero d p)

end SIC

end
