/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Ghost.TwistedSummands

/-!
# Abstract ghost fiducials

Abstract ghost matrices, trace and rank, and the ghost-fiducial predicate.

This file formalizes the ghost projectors of [AFK25, Definition 1.11, `dfn:ghostFiducial`] with
fixed overlap and twist data, and their independence of the transversal
in [AFK25, Lemma 1.42, `lem:GhostFiducialIndependenceOfTransversal`]. The overlap data
and quotient twists are in `SICs.Ghost.OverlapData`; the phase cancellation and twisted
sum identities are in `SICs.Ghost.TwistedSummands`.

Summing real overlap coefficients against integer displacements gives the expansion matrix of
the definition. The quasiperiodicity of the overlaps makes its full summand independent of the
integer representative, so every transversal gives the same matrix. Its trace is the
prescribed rank; idempotency then supplies the ghost-projector predicate. No analytic
formula for the overlaps is required in this algebraic layer. Conversely, when $0 < r < d$,
the universal expansion of a completed ghost fiducial forces each normalized summand to be
independent of representatives. Cancelling the displacement phase recovers quasi-periodicity
of its normalized coefficients.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### Normalized coefficients

The quotient twist is absorbed into the source coefficient. Periodicity and reciprocity hold
for the packaged data. For a completed ghost fiducial in the range $0 < r < d$, the universal
expansion implies quasi-periodicity, as proved below. -/

/-- The complex normalized coefficient `v(p)` of packaged ghost-fiducial data, including its
quotient twist. It is the complex coercion of the real coefficient appearing in
`ghostFiducialMatrix`. -/
def GhostFiducialData.normalizedCoefficient {d : ℕ} (s : GhostFiducialData d)
    (p : IntPhaseSpace) : ℂ :=
  s.overlaps.normalized (s.twistedIndex p)

/-- The packaged normalized coefficient depends only on the integer index modulo `dbar d`. -/
theorem GhostFiducialData.normalizedCoefficient_dbar_periodic {d : ℕ}
    (s : GhostFiducialData d) {p p' : IntPhaseSpace}
    (hmod : intPhaseSpaceMod (dbar d) p' = intPhaseSpaceMod (dbar d) p) :
    s.normalizedCoefficient p' = s.normalizedCoefficient p := by
  simp [GhostFiducialData.normalizedCoefficient, GhostFiducialData.twistedIndex, hmod]

/-- Packaged ghost coefficients satisfy the reciprocal identity at every nonzero residue, even
after composing the overlap data with an arbitrary quotient ghost twist. -/
theorem GhostFiducialData.normalizedCoefficient_mul_neg {d : ℕ} [NeZero d]
    (s : GhostFiducialData d) (p : IntPhaseSpace) (hp : intPhaseSpaceMod d p ≠ 0) :
    s.normalizedCoefficient p * s.normalizedCoefficient (-p) = 1 := by
  let G := s.twist.integerLift
  have hG : IsGhostTwistLift G s.twist := s.twist.integerLift_isLift
  have hpG : intPhaseSpaceMod d (Matrix.mulVec G p) ≠ 0 :=
    intPhaseSpaceMod_matrix_mulVec_ne_zero G hG.det_isCoprime hp
  have hrec := s.overlaps.reciprocal (Matrix.mulVec G p) hpG
  have hGp := hG.intPhaseSpaceMod_mulVec_eq_twistedIndex s p
  have hGneg := hG.intPhaseSpaceMod_mulVec_eq_twistedIndex s (-p)
  have hrecC := congrArg (fun x : ℝ => (x : ℂ)) hrec
  rw [Complex.ofReal_mul, Complex.ofReal_one] at hrecC
  unfold GhostFiducialData.normalizedCoefficient
  rw [← hGp, ← hGneg]
  simpa only [Matrix.mulVec_neg] using hrecC

/-! ### Representative-independent normalized summands

Summing the twisted coefficients over a transversal gives the abstract ghost-fiducial matrix.
The interface packages the representative-independence and projector conditions needed by the
later ghost-to-live construction. -/

/-- The normalized summand `ν̃_(G p) D_p` attached to abstract ghost-fiducial data. -/
noncomputable def normalizedGhostSummand {d : ℕ} [NeZero d]
    (s : GhostFiducialData d) (p : IntPhaseSpace) : Mat(d, ℂ) :=
  s.overlaps.normalized (s.twistedIndex p) • integerDisplacement d p

/-- The representative-independence condition required for the normalized summand in the
ghost-fiducial expansion.

`hasRepresentativeIndependentSummand_of_quasiperiodic` derives it from
`IsGhostOverlapQuasiperiodic` before constructing a ghost fiducial. Conversely,
`IsGhostFiducialWith.hasRepresentativeIndependentSummand` derives this condition from the
universal expansion of a completed ghost fiducial when $0 < r < d$. -/
def GhostFiducialData.HasRepresentativeIndependentSummand {d : ℕ} [NeZero d]
    (s : GhostFiducialData d) : Prop :=
  RespectsPhaseSpaceResiduesAwayFromZero d (normalizedGhostSummand s)

/-- Computing a normalized ghost summand with any integer lift of the datum's twist agrees with
the quotient-indexed definition. -/
theorem GhostFiducialData.rawTwistedNormalizedGhostSummand_eq
    {d : ℕ} [NeZero d] (s : GhostFiducialData d)
    {G : Mat(2, ℤ)} (hG : IsGhostTwistLift G s.twist)
    (p : IntPhaseSpace) :
    rawTwistedNormalizedGhostSummand (d := d) G s.overlaps.integerPullback p =
      normalizedGhostSummand s p := by
  unfold rawTwistedNormalizedGhostSummand GhostOverlapData.integerPullback
    normalizedGhostSummand
  rw [hG.intPhaseSpaceMod_mulVec_eq_twistedIndex]
  ext i j
  simp [Complex.real_smul]

/-- Quasi-periodicity of the integer pullback of a datum's normalized overlaps gives the
representative independence required by its ghost-fiducial expansion.

This is the quotient-twist form of
`IsGhostOverlapQuasiperiodic.rawTwistedNormalizedGhostSummand_respectsResidues`. It assumes the
quasi-periodicity input; each concrete overlap construction must establish that input separately. -/
theorem GhostFiducialData.hasRepresentativeIndependentSummand_of_quasiperiodic
    {d : ℕ} [NeZero d] (s : GhostFiducialData d)
    (hs : IsGhostOverlapQuasiperiodic d s.overlaps.integerPullback) :
    s.HasRepresentativeIndependentSummand := by
  let G := s.twist.integerLift
  have hG : IsGhostTwistLift G s.twist := s.twist.integerLift_isLift
  intro p p' hpp' hp
  rw [← s.rawTwistedNormalizedGhostSummand_eq hG,
    ← s.rawTwistedNormalizedGhostSummand_eq hG]
  exact hs.rawTwistedNormalizedGhostSummand_eq G hG.det_isCoprime hpp' hp

/-! ### The ghost-fiducial matrix

The expansion of [AFK25, Definition 1.11, `dfn:ghostFiducial`] has real coefficients
and trace `r`. Its independence follows from the normalized summand above. -/

/-- The real scalar
`√(r(d-r)/(d²(d²-1)))` multiplying the nonidentity displacement sum in a ghost-fiducial
expansion [AFK25, equation (1.12), `eq:ghstSIC`]. -/
noncomputable def ghostFiducialPrefactor (d r : ℕ) : ℝ :=
  Real.sqrt ((r * (d - r) : ℝ) / (d ^ 2 * (d ^ 2 - 1)))

/-- The ghost-fiducial prefactor is positive for a nonzero rank strictly below the dimension. -/
theorem ghostFiducialPrefactor_pos {d r : ℕ} (hr : 0 < r) (hrd : r < d) :
    0 < ghostFiducialPrefactor d r := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hrdR : (r : ℝ) < d := by exact_mod_cast hrd
  have hdR : (1 : ℝ) < d := by exact_mod_cast (by omega : 1 < d)
  apply Real.sqrt_pos.2
  exact div_pos (mul_pos hrR (sub_pos.mpr hrdR))
    (mul_pos (sq_pos_of_pos (lt_trans zero_lt_one hdR)) (by nlinarith))

/-- The ghost-fiducial prefactor is the overlap scale divided by `d`:
`√(r(d-r)/(d²(d²-1))) = √(r(d-r)/(d²-1))/d`. -/
theorem ghostFiducialPrefactor_eq_div (d r : ℕ) :
    ghostFiducialPrefactor d r = Real.sqrt ((r * (d - r) : ℝ) / ((d : ℝ) ^ 2 - 1)) / d := by
  rw [ghostFiducialPrefactor, mul_comm ((d : ℝ) ^ 2), ← div_div, Real.sqrt_div' _ (sq_nonneg _),
    Real.sqrt_sq (Nat.cast_nonneg d)]

/-- The matrix in the ghost-fiducial expansion for a chosen complete transversal.

The definition follows [AFK25, equation (1.12), `eq:ghstSIC`] with genuinely integer-indexed
displacement operators. A faithful ghost fiducial below requires this matrix to be independent of
the chosen transversal. `GhostFiducialData.HasRepresentativeIndependentSummand` records that extra
property, and `GhostFiducialData.hasRepresentativeIndependentSummand_of_quasiperiodic` derives it
from a separately established quasi-periodicity hypothesis. -/
noncomputable def ghostFiducialMatrix {d : ℕ} [NeZero d] (r : ℕ)
    (s : GhostFiducialData d) (I : PhaseSpaceTransversal d) :
    Mat(d, ℂ) :=
  ((r : ℂ) / (d : ℂ)) • (1 : Mat(d, ℂ)) +
    ghostFiducialPrefactor d r •
      ∑ q : PhaseSpaceMod d, if q = 0 then 0 else
        s.overlaps.normalized (s.twistedIndex (I.repr q)) •
          integerDisplacement d (I.repr q)

/-- Representative independence of the normalized summand makes the ghost-fiducial matrix
independent of the complete transversal. -/
theorem ghostFiducialMatrix_eq_of_transversal {d : ℕ} [NeZero d]
    (r : ℕ) (s : GhostFiducialData d) (hs : s.HasRepresentativeIndependentSummand)
    (I J : PhaseSpaceTransversal d) :
    ghostFiducialMatrix r s I = ghostFiducialMatrix r s J := by
  have hsum := sum_transversal_eq_of_respectsResidues
    (normalizedGhostSummand s) hs I J
  simp only [normalizedGhostSummand] at hsum
  unfold ghostFiducialMatrix
  rw [hsum]

/-- Every matrix given by the ghost-fiducial expansion has trace `r`, independently of
idempotency and of the chosen transversal. -/
theorem trace_ghostFiducialMatrix {d : ℕ} [NeZero d] (r : ℕ)
    (s : GhostFiducialData d) (I : PhaseSpaceTransversal d) :
    (ghostFiducialMatrix r s I).trace = (r : ℂ) := by
  have hsum :
      (∑ q : PhaseSpaceMod d, if q = 0 then 0 else
        s.overlaps.normalized (s.twistedIndex (I.repr q)) •
          integerDisplacement d (I.repr q)).trace = 0 := by
    rw [Matrix.trace_sum]
    apply Finset.sum_eq_zero
    intro q _
    by_cases hq : q = 0
    · simp [hq]
    · rw [ite_eq_right hq, Matrix.trace_smul,
        trace_integerDisplacement_of_mod_ne_zero]
      · simp
      · intro hz
        apply hq
        rw [← I.residue_repr q, hz]
  rw [ghostFiducialMatrix, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one,
    Matrix.trace_smul, hsum]
  simp [show (d : ℂ) ≠ 0 by exact_mod_cast NeZero.ne d]

/-! ### The ghost-projector predicate

An idempotent expansion matrix has rank equal to its trace `r`, which gives the rank-`r` projector
condition of [AFK25, Definition 1.11, `dfn:ghostFiducial`]. -/

/-- An idempotent complex matrix with trace `r` has matrix rank `r`. -/
lemma rank_eq_of_idempotent_of_trace {d r : ℕ}
    (P : Mat(d, ℂ)) (hP : P ^ 2 = P) (htrace : P.trace = (r : ℂ)) :
    P.rank = r := by
  have hcast : (P.rank : ℂ) = (r : ℂ) := by
    rw [← htrace, trace_eq_rank_of_idempotent P hP]
  exact_mod_cast hcast

/-- A matrix is the ghost fiducial attached to fixed overlap and twist data when it is a rank-`r`
idempotent and the expansion `ghostFiducialMatrix` gives that same matrix for every complete
set of integer residue representatives.

The real-valuedness and reciprocal identity are fields of `GhostOverlapData`; the universal
quantifier over `PhaseSpaceTransversal` makes the source's phrase "over any set of coset
representatives" explicit rather than assuming false periodicity of the individual displacement
operators modulo `d`. -/
structure IsGhostFiducialWith {d : ℕ} [NeZero d] (r : ℕ)
    (P : Mat(d, ℂ)) (s : GhostFiducialData d) : Prop where
  /-- A ghost fiducial is a projection operator, though generally not a Hermitian one. -/
  idempotent : P ^ 2 = P
  /-- Its matrix rank is `r`. -/
  rank_eq : P.rank = r
  /-- Its defining expansion is independent of the chosen complete transversal. -/
  expansion : ∀ I : PhaseSpaceTransversal d, P = ghostFiducialMatrix r s I

/-! #### Coefficient laws from the universal expansion

For $0 < r < d$, the prefactor is positive. Comparing two expansions of the same ghost fiducial
therefore gives equal sums over every transversal. Changing one representative isolates its
summand. The representative-change law for the nonzero displacement operator then gives the
quasi-periodicity of the normalized coefficient. -/

/-- A ghost fiducial's universal expansion gives representative independence of its normalized
summand when $0 < r < d$. This recovers the construction input to
`isGhostFiducialWith_of_idempotent` from a completed `IsGhostFiducialWith`. -/
theorem IsGhostFiducialWith.hasRepresentativeIndependentSummand {d r : ℕ} [NeZero d]
    {P : Mat(d, ℂ)} {s : GhostFiducialData d}
    (hP : IsGhostFiducialWith r P s) (hr : 0 < r) (hrd : r < d) :
    s.HasRepresentativeIndependentSummand := by
  classical
  apply respectsResidues_of_sum_transversal_eq
  intro I J
  have hh := (hP.expansion I).symm.trans (hP.expansion J)
  simp only [ghostFiducialMatrix] at hh
  exact smul_right_injective (Mat(d, ℂ))
    (ne_of_gt (ghostFiducialPrefactor_pos hr hrd)) (add_left_cancel hh)

/-- A completed ghost fiducial has quasi-periodic normalized coefficients when $0 < r < d$:
`v(p') = ξ_d^{⟨p',p⟩} v(p)` for nonzero congruent indices. This follows from
`IsGhostFiducialWith.hasRepresentativeIndependentSummand` and the displacement phase law. -/
theorem IsGhostFiducialWith.normalizedCoefficient_quasiperiodic {d r : ℕ} [NeZero d]
    {P : Mat(d, ℂ)} {s : GhostFiducialData d}
    (hP : IsGhostFiducialWith r P s) (hr : 0 < r) (hrd : r < d) :
    IsGhostOverlapQuasiperiodic d s.normalizedCoefficient := by
  intro p p' hmod hp
  have hh : s.normalizedCoefficient p' • integerDisplacement d p' =
      s.normalizedCoefficient p • integerDisplacement d p := by
    simpa only [normalizedGhostSummand, GhostFiducialData.normalizedCoefficient,
      RCLike.real_smul_eq_coe_smul (K := ℂ)] using!
      hP.hasRepresentativeIndependentSummand hr hrd p p' hmod hp
  rw [integerDisplacement_change_representative hmod, smul_smul] at hh
  have he := smul_left_injective ℂ (integerDisplacement_ne_zero p) hh
  have hn := displacementPhase_ne_zero d
  apply mul_left_injective₀ (zpow_ne_zero _ hn)
  calc
    s.normalizedCoefficient p' * displacementPhase d ^ (-intSymplecticForm p' p) =
        s.normalizedCoefficient p := he
    _ = (displacementPhase d ^ intSymplecticForm p' p * s.normalizedCoefficient p) *
        displacementPhase d ^ (-intSymplecticForm p' p) := by
      rw [mul_right_comm, ← zpow_add₀ hn, add_neg_cancel, zpow_zero, one_mul]

/-! #### Projector properties and construction

The expansion supplies the trace. Idempotency therefore suffices to construct the ghost-projector
predicate once representative independence is known. -/

/-- To construct a ghost fiducial with fixed data, it suffices to prove representative
independence of the summand, identify the matrix using the canonical transversal, and prove
idempotency. The rank conclusion follows automatically from the trace of the expansion. -/
theorem isGhostFiducialWith_of_idempotent {d r : ℕ} [NeZero d]
    (P : Mat(d, ℂ)) (s : GhostFiducialData d)
    (hs : s.HasRepresentativeIndependentSummand)
    (hP : P = ghostFiducialMatrix r s (canonicalPhaseSpaceTransversal d))
    (hidempotent : P ^ 2 = P) : IsGhostFiducialWith r P s := by
  have hexpansion : ∀ I : PhaseSpaceTransversal d, P = ghostFiducialMatrix r s I := by
    intro I
    exact hP.trans (ghostFiducialMatrix_eq_of_transversal r s hs _ I)
  have htrace : P.trace = (r : ℂ) := by
    rw [hexpansion (canonicalPhaseSpaceTransversal d), trace_ghostFiducialMatrix]
  exact {
    idempotent := hidempotent
    rank_eq := rank_eq_of_idempotent_of_trace P hidempotent htrace
    expansion := hexpansion
  }

end SIC

end
