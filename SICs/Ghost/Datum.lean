/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Ghost.GhostProjector
import SICs.Admissible.StabilizerExistence

/-!
# Ghost data for an admissible tuple

A shift and compatible twist, their candidate ghost fiducial, and Theorem 1.45.

This module packages the ghost part of [AFK25, Definition 1.41, `def:fiducialdata`]. A shift
for the tuple's associated stabilizers and a compatible quotient twist determine the candidate
of [AFK25, Definition 1.43, `dfn:CandidateGhostAndSICFiducials`]. The projector construction in
`SICs.Ghost.GhostProjector` proves it is a ghost fiducial with the datum's ghost-fiducial data,
which is [AFK25, Theorem 1.45, `thm:ghstExist`]. Conversely, any shift supplies a compatible twist
by its coprimality clause. A Galois automorphism enters only in `SICs.Ghost.LiveCandidate`.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

namespace AdmissibleTuple

/-! ### Ghost data

The data a candidate ghost fiducial depends on: the tuple's associated stabilizers, a shift, and
a compatible twist. A Galois automorphism is not part of it; the live candidate is obtained later
by applying one automorphism entrywise to the fixed ghost candidate. -/

/-- **A ghost datum for an admissible tuple `t`**: a shift `λ ∈ Z_t` ([AFK25, Definition 1.34,
`dfn:shift`]) and a twist `G ∈ GL₂(ℤ/d̄ℤ)` with `Det(G) r(2λ + d_j - 1 + d) ≡ 1 (mod d̄)`
([AFK25, Definition 1.41, `def:fiducialdata`, equation (1.51), `eq:TwistCondition`]), with respect
to the tuple's associated stabilizers `A_t`, `L_{z,t}` (`levelGenerator`, `zaunerGenerator`,
[AFK25, Theorem 4.50, `tm:symgp`]).

This is the part of a fiducial datum `s = (t, G, g)` on which the candidate ghost fiducial `Π̃_s`
of [AFK25, Definition 1.43, `dfn:CandidateGhostAndSICFiducials`] depends. The Galois automorphism
`g` is left out: it enters only the live candidate `Π_s = g(Π̃_s)`. The source asks only that some
`λ ∈ Z_t` satisfy the twist condition; the datum records an integer representative of one, which
is determined by the twist modulo `d` by the injectivity of `f_t` in [AFK25, Lemma 5.11,
`lem:fdf`]. -/
structure GhostDatum (t : AdmissibleTuple) where
  /-- An integer representative of the shift `λ`. -/
  shift : ℤ
  /-- The twist `G`, an element of `GL₂(ℤ/d̄ℤ)`. -/
  twist : GhostTwist t.d
  /-- The shift lies in `Z_t`. -/
  isShift : t.IsShift t.levelGenerator t.zaunerGenerator shift
  /-- The twist is compatible with the shift. -/
  isCompatibleTwist : t.IsCompatibleTwist shift twist

namespace GhostDatum

variable {t : AdmissibleTuple}

/-- **The candidate ghost fiducial `Π̃_s`** of a ghost datum, [AFK25, Definition 1.43,
`dfn:CandidateGhostAndSICFiducials`, equation (1.53), `eq:ghostProjectorDef`]: the candidate ghost
operator of the tuple's level generator and the datum's twist. -/
@[source "AFK25, Definition 1.43, p. 20, dfn:CandidateGhostAndSICFiducials (ghost)"
  (symbol := "Π̃_s")]
noncomputable def candidate (s : t.GhostDatum) : Mat(t.d, ℂ) :=
  t.candidateGhostOperator t.levelGenerator s.twist

/-- The ghost-fiducial data of a ghost datum: the tuple's real normalized overlaps and the datum's
twist. -/
noncomputable def fiducialData (s : t.GhostDatum) : GhostFiducialData t.d :=
  t.isAssociatedStabilizerPair_levelGenerator.ghostFiducialData s.twist

/-- The candidate ghost fiducial of a ghost datum is a ghost `r`-SIC fiducial with the datum's
ghost-fiducial data (`IsShift.candidateGhostOperator_isGhostFiducialWith`). -/
theorem isGhostFiducialWith (s : t.GhostDatum) :
    IsGhostFiducialWith t.r s.candidate s.fiducialData := by
  exact s.isShift.candidateGhostOperator_isGhostFiducialWith
    t.isAssociatedStabilizerPair_levelGenerator s.isCompatibleTwist

/-- The packaged coefficient of a ghost datum is the candidate overlap at the twisted index,
`v(p) = ν̃_t(Gp)` for `p ≢ 0 (mod d)` and any integer lift `G` of the twist
(`IsAssociatedStabilizerPair.ghostFiducialData_normalizedCoefficient`). -/
theorem fiducialData_normalizedCoefficient (s : t.GhostDatum) {G : Mat(2, ℤ)}
    (hG : IsGhostTwistLift G s.twist) {p : IntPhaseSpace} (hp : intPhaseSpaceMod t.d p ≠ 0) :
    s.fiducialData.normalizedCoefficient p =
      t.candidateNormGhostOverlap t.levelGenerator (Matrix.mulVec G p) :=
  t.isAssociatedStabilizerPair_levelGenerator.ghostFiducialData_normalizedCoefficient s.twist hG hp

/-- **A shift gives a ghost datum**: a shift `λ` for any associated stabilizer pair of `t` is a
shift for the tuple's own pair (`IsAssociatedStabilizerPair.unique`), and its coprimality clause
supplies a compatible twist (`IsShift.exists_isCompatibleTwist`), chosen here. -/
noncomputable def ofIsShift {A Lz : SL(2, ℤ)} (h : t.IsAssociatedStabilizerPair A Lz) {lam : ℤ}
    (hlam : t.IsShift A Lz lam) : t.GhostDatum :=
  let hpair := h.unique t.isAssociatedStabilizerPair_levelGenerator
  let hlam' : t.IsShift t.levelGenerator t.zaunerGenerator lam := by
    rw [← hpair.1, ← hpair.2]
    exact hlam
  let g := Classical.choose hlam'.exists_isCompatibleTwist
  {
    shift := lam
    twist := g
    isShift := hlam'
    isCompatibleTwist := Classical.choose_spec hlam'.exists_isCompatibleTwist
  }

end GhostDatum

end AdmissibleTuple

end SIC

end
