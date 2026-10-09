/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Ghost.CandidateOverlaps

/-!
# Candidate Ghost Operator

The ghost-operator clause of Definition 1.43, independent of transversal and twist lift.

Following [AFK25, Subsection 1.6, `ssc:MainTheorems1`], this file defines the candidate ghost
operator in the General layer from the exact candidate overlaps. It formalizes the ghost-operator
clause of [AFK25, Definition 1.43, `dfn:CandidateGhostAndSICFiducials`] and proves that the operator
is independent of both the phase-space transversal and the integer lift used to present its quotient
twist.

## Mathematical argument

The source sums `d⁻¹ ν_t(Gp)D_p` over a complete set of representatives modulo `d`. The project
stores the twist in `GL₂(ℤ/dbar dℤ)`, so the formula is first evaluated using an integer lift.
The zero class is written separately as `(r/d)I`; a nonzero integer representative of that class
could otherwise introduce a spurious displacement sign. For the remaining classes, [AFK25,
Lemma 5.7, `lem:nupperiodicity`] makes the overlap phase cancel the representative-change phase of
`D_p`. The same `dbar d`-periodicity shows that two integer lifts of one quotient twist give equal
coefficients.

Thus every lift and transversal give the same operator, and the canonical definition uses fixed
choices only to produce a term of the required matrix type. This quotient-twist
presentation is a representation difference from the integral matrix in the paper, not a change
to the resulting operator.

## References

- [AFK25] Appleby, Flammia, Kopp, arXiv:2501.03970v2, Lemma 1.42 and Definition 1.43
-/

noncomputable section

open scoped MatrixGroups

namespace SIC
namespace AdmissibleTuple

/-! ### The candidate operator and independence of choices -/

/-- The candidate ghost operator
`Π̃_s = d⁻¹ ∑_p ν_t(Gp)D_p` of [AFK25, Definition 1.43,
`dfn:CandidateGhostAndSICFiducials`, equation (1.53), `eq:ghostProjectorDef`], computed from an
integer twist lift `G` and a complete phase-space transversal `I`. -/
noncomputable def candidateGhostOperatorOfLift (t : AdmissibleTuple) (A : SL(2, ℤ))
    (G : Mat(2, ℤ)) (I : PhaseSpaceTransversal t.d) :
    Mat(t.d, ℂ) :=
  ((t.r : ℂ) / (t.d : ℂ)) • (1 : Mat(t.d, ℂ)) +
    ((t.d : ℂ)⁻¹) •
      ∑ q : PhaseSpaceMod t.d, if q = 0 then 0 else
        rawTwistedGhostSummand (d := t.d) t.r G (t.candidateNormGhostOverlap A) (I.repr q)

/-- The candidate ghost operator is independent of the complete integer transversal when the
twist determinant is invertible modulo `dbar d`. This specializes the representative-independent
summand API underlying `IsGhostOverlapQuasiperiodic.sum_rawTwistedGhostSummand_eq`. -/
theorem IsAssociatedStabilizerPair.candidateGhostOperatorOfLift_eq_of_transversal
    {t : AdmissibleTuple} {A_t Lz : SL(2, ℤ)}
    (h : t.IsAssociatedStabilizerPair A_t Lz)
    (G : Mat(2, ℤ)) (hG : IsCoprime G.det (dbar t.d : ℤ))
    (I J : PhaseSpaceTransversal t.d) :
    candidateGhostOperatorOfLift t A_t G I = candidateGhostOperatorOfLift t A_t G J := by
  unfold candidateGhostOperatorOfLift
  rw [h.candidateNormGhostOverlap_quasiperiodic.sum_rawTwistedGhostSummand_eq
    t.r G hG I J]

/-- The candidate ghost operator is independent of the integer lift chosen for one fixed quotient
ghost twist. This is the lift-independence bridge required by the project's quotient-valued twist
representation. -/
theorem IsAssociatedStabilizerPair.candidateGhostOperatorOfLift_eq_of_isLift
    {t : AdmissibleTuple} {A_t Lz : SL(2, ℤ)}
    (h : t.IsAssociatedStabilizerPair A_t Lz)
    {G H : Mat(2, ℤ)} {g : GhostTwist t.d}
    (hG : IsGhostTwistLift G g) (hH : IsGhostTwistLift H g)
    (I : PhaseSpaceTransversal t.d) :
    candidateGhostOperatorOfLift t A_t G I = candidateGhostOperatorOfLift t A_t H I := by
  unfold candidateGhostOperatorOfLift
  rw [h.candidateNormGhostOverlap_quasiperiodic.sum_rawTwistedGhostSummand_eq_of_isLift
    t.r hG hH I]

/-- The representative-independent candidate ghost operator attached to a quotient twist. It uses
the canonical integer lift and phase-space transversal to represent
`candidateGhostOperatorOfLift`. -/
noncomputable def candidateGhostOperator (t : AdmissibleTuple) (A : SL(2, ℤ))
    (g : GhostTwist t.d) : Mat(t.d, ℂ) :=
  candidateGhostOperatorOfLift t A g.integerLift (canonicalPhaseSpaceTransversal t.d)

/-- Any integer lift and complete phase-space transversal compute `candidateGhostOperator`, so
the operator depends only on the admissible tuple, associated level generator, and quotient
twist. -/
theorem IsAssociatedStabilizerPair.candidateGhostOperator_eq_of_lift_transversal
    {t : AdmissibleTuple} {A_t Lz : SL(2, ℤ)}
    (h : t.IsAssociatedStabilizerPair A_t Lz) {g : GhostTwist t.d}
    {G : Mat(2, ℤ)} (hG : IsGhostTwistLift G g)
    (I : PhaseSpaceTransversal t.d) :
    candidateGhostOperator t A_t g = candidateGhostOperatorOfLift t A_t G I := by
  calc
    candidateGhostOperator t A_t g =
        candidateGhostOperatorOfLift t A_t G (canonicalPhaseSpaceTransversal t.d) := by
      exact h.candidateGhostOperatorOfLift_eq_of_isLift
        g.integerLift_isLift hG _
    _ = candidateGhostOperatorOfLift t A_t G I :=
      h.candidateGhostOperatorOfLift_eq_of_transversal G hG.det_isCoprime _ I

end AdmissibleTuple
end SIC
