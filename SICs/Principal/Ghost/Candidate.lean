/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Ghost.Fiducials
import SICs.Principal.Ghost.Overlaps

/-!
# The Principal Ghost Candidate

`principalGhostCandidate`, its representative-independent summand, and its fiducial packaging.

This file builds the identity-twist ghost-fiducial data of the principal family from the packaged
overlaps of `SICs.Principal.Ghost.Overlaps`, forms the rank-one displacement-operator expansion of
[AFK25, Definition 1.43, `dfn:CandidateGhostAndSICFiducials`] through the general
`ghostFiducialMatrix`, and shows that its summand depends only on the residue class. The general
`isGhostFiducialWith_of_idempotent` then packages every clause of [AFK25, Theorem 1.45,
`thm:ghstExist`] except idempotency, which `SICs.Principal.Construction.GhostProjector` supplies
from the exact principal real shift.

Representative independence comes from the quasi-periodicity of the overlap through the general
bridge `GhostFiducialData.hasRepresentativeIndependentSummand_of_quasiperiodic`; rank one follows
from the trace once idempotency is known, so no separate rank hypothesis is needed.

## Main definitions and results

- `principalGhostFiducialData`: the identity-twist `GhostFiducialData d` built from
  `principalGhostOverlapData`, with `principalGhostFiducialData_integerPullback`.
- `hasRepresentativeIndependentSummand_principal`: its
  overlap-coefficient/displacement-operator summand depends only on the residue class.
- `principalGhostCandidate`: the rank-one displacement-operator sum of [AFK25, Definition 1.43,
  `dfn:CandidateGhostAndSICFiducials`] at the canonical transversal.
- `principalGhostCandidate_isGhostFiducialWith`: the ghost-fiducial packaging of
  [AFK25, Theorem 1.45, `thm:ghstExist`], conditional only on idempotency of the candidate.

## References

- [AFK25] Appleby, Flammia, Kopp, arXiv:2501.03970v2, Definition 1.43 and Theorem 1.45
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### Representative independence and the ghost candidate

The identity-twist ghost-fiducial data for the principal family has a representative-independent
summand, by the quasi-periodicity of
`principalNormGhostOverlap`; and the resulting displacement-operator sum of [AFK25, Definition 1.43,
`dfn:CandidateGhostAndSICFiducials`] -- defined as `ghostFiducialMatrix` in
`SICs.Ghost.Fiducials` -- gives the principal ghost candidate operator.
`SICs.Principal.Construction.GhostProjector` proves
idempotency from the predicate `IsPrincipalRealShift`; `SICs.Principal.Construction.Existence`
discharges it by `isPrincipalRealShift_one`. The argument also uses the Shintani--Faddeev
identification of the principal cocycle. -/

/-- The principal family's ghost-fiducial data for the identity twist `G = I`, the twist used
throughout this construction. -/
noncomputable def principalGhostFiducialData (d : RankOneDimension) : GhostFiducialData d :=
  { overlaps := principalGhostOverlapData d
    twist := 1 }

/-- The integer pullback of the principal family's packaged overlap data agrees pointwise with
the original complex-valued overlap `principalNormGhostOverlap`. -/
lemma principalGhostFiducialData_integerPullback (d : RankOneDimension) :
    (principalGhostFiducialData d).overlaps.integerPullback =
      principalNormGhostOverlap d := by
  funext p
  simp only [GhostOverlapData.integerPullback, principalGhostFiducialData,
    principalGhostOverlapData]
  rw [principalNormGhostOverlapQuotient_eq, ofReal_principalNormGhostOverlapReal]

/-- **The overlap-coefficient/displacement-operator summand of the principal ghost-fiducial
expansion depends only on the residue class of its integer index.** This is the
representative-independence hypothesis required for the displacement-operator sum of
`principalGhostCandidate` to be well-defined, obtained here from the quasi-periodicity of
`principalNormGhostOverlap` via the general bridge
`GhostFiducialData.hasRepresentativeIndependentSummand_of_quasiperiodic`. -/
theorem hasRepresentativeIndependentSummand_principal (d : RankOneDimension) :
    (principalGhostFiducialData d).HasRepresentativeIndependentSummand := by
  apply GhostFiducialData.hasRepresentativeIndependentSummand_of_quasiperiodic
  rw [principalGhostFiducialData_integerPullback]
  exact principalNormGhostOverlap_quasiperiodic d

/-- **The principal ghost candidate operator.** The rank-one displacement-operator expansion of
[AFK25, Definition 1.43, `dfn:CandidateGhostAndSICFiducials`] at the principal family's overlap
data and the identity twist, evaluated at the canonical phase-space transversal. -/
noncomputable def principalGhostCandidate (d : RankOneDimension) : Mat(d, ℂ) :=
  ghostFiducialMatrix 1 (principalGhostFiducialData d) (canonicalPhaseSpaceTransversal d)

/-! ### The ghost-fiducial packaging

Given idempotency, the principal candidate satisfies [AFK25, Theorem 1.45, `thm:ghstExist`].
Representative independence follows from `hasRepresentativeIndependentSummand_principal`, and
rank one follows from the trace via `rank_eq_of_idempotent_of_trace`.
`SICs.Principal.Construction.Existence` proves the idempotency hypothesis from the principal
twisted convolution identity. -/

/-- Given idempotency, the principal ghost candidate is a ghost fiducial for its explicit overlap
data. Representative independence, parity-Hermiticity, and trace one are unconditional.
Rank one follows from the supplied idempotency hypothesis, which
`principalGhostCandidate_idempotent_of_realShift` derives from the exact principal
shift. -/
theorem principalGhostCandidate_isGhostFiducialWith (d : RankOneDimension)
    (hidem : principalGhostCandidate d ^ 2 = principalGhostCandidate d) :
    IsGhostFiducialWith 1 (principalGhostCandidate d)
      (principalGhostFiducialData d) := by
  exact isGhostFiducialWith_of_idempotent _ _
    (hasRepresentativeIndependentSummand_principal d) rfl hidem

end SIC

end
