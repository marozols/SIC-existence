/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Quantum.GaloisAction
import SICs.Quantum.Fiducials
import SICs.Ghost.Fiducials

/-!
# Converting a Ghost Fiducial into a Live Fiducial

Arbitrary-rank ghost-to-live conversion and the local live-fiducial theorem.

The local ghost-to-live argument of [AFK25, Theorem 1.46,
`thm:rayclassfieldrsicgen`] is independent of the explicit quadratic form, admissible tuple,
shift, and Shintani--Faddeev formula that produced the ghost fiducial. This module states that
argument for arbitrary rank `r`, arbitrary packaged ghost-overlap and twist data, and one fixed
ambient Galois automorphism.

For ghost data `s`, write `v(p)` for the normalized coefficient already composed with `s.twist`.
When `0 < r < d`, the ghost expansion holds for every choice of representatives. Comparing
two such expansions and cancelling the positive prefactor and the nonzero displacement
operator gives quasi-periodicity of `v`. The live coefficient is

`mu(p) = g(v(H_g⁻¹ p))`.

Entrywise application of `g` preserves the projector equation and trace, sends `D_p` to
`D_(H_g p)`, and reindexing by `H_g` gives a displacement expansion with coefficients `mu`.
Reciprocity of `GhostOverlapData` and the unit-modulus condition imply
`mu(-p) = conj (mu(p))`; consequently that expansion is Hermitian. Hilbert--Schmidt orthogonality
then reads off the displacement overlaps, and the standard ghost prefactor gives exactly
`sqrt (r(d-r)/(d^2-1))`. Thus the Galois image is a live rank-`r` SIC fiducial.

The theorem uses `ComplexGaloisAutomorphism`, a field automorphism of `ℂ`.
`SICs.Ghost.LiveCandidate` and `SICs.Principal.Construction.Live` apply it to the ghost candidates
of the general and the principal construction.

## References

- [AFK25] Appleby, Flammia, Kopp, arXiv:2501.03970v2, Lemma 1.44 and Theorem 1.46
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### Ghost and live normalized coefficients

The quotient twist is absorbed into the source coefficient. Composing with the inverse Galois
index matrix then gives the coefficient of the reindexed live expansion. -/

/-- The exact local input for converting fixed ghost data with one fixed automorphism: every
nonzero normalized coefficient has unit modulus after applying that automorphism. This is the
`exists g, forall p` input used in [AFK25, proof of Theorem 1.46,
`thm:rayclassfieldrsicgen`], with the existential quantifier left to callers. -/
def LiveConversionCondition {d : ℕ} (s : GhostFiducialData d)
    (g : ComplexGaloisAutomorphism) : Prop :=
  ∀ p : IntPhaseSpace, intPhaseSpaceMod d p ≠ 0 →
    ‖g (s.normalizedCoefficient p)‖ = 1

/-- The live normalized coefficient `mu(p) = g(v(H_g⁻¹ p))` from [AFK25, Lemma 1.44,
`lm:OverlapTermsGhostOverlap`], with the datum's compatible twist already included in `v`. -/
def liveNormalizedCoefficient (d : ℕ) [NeZero d] (s : GhostFiducialData d)
    (g : ComplexGaloisAutomorphism) (p : IntPhaseSpace) : ℂ :=
  g (s.normalizedCoefficient (Matrix.mulVec (galoisInverseIndexMatrix d g) p))

/-- At an index already moved by `H_g`, the live coefficient is the Galois image of the source
coefficient. The equality uses only the built-in `dbar d`-periodicity of packaged data. -/
theorem liveNormalizedCoefficient_mulVec (d : ℕ) [NeZero d] (s : GhostFiducialData d)
    (g : ComplexGaloisAutomorphism) (p : IntPhaseSpace) :
    liveNormalizedCoefficient d s g
        (Matrix.mulVec (galoisIndexMatrix (galoisExponent d g)) p) =
      g (s.normalizedCoefficient p) := by
  rw [liveNormalizedCoefficient]
  exact congrArg g (s.normalizedCoefficient_dbar_periodic
    (galoisInverseIndexMatrix_mulVec_mulVec d g p))

/-- Quasi-periodicity of a ghost coefficient is preserved by Galois conjugation followed by
inverse-index transport. This is the coefficient-level phase cancellation in [AFK25, proof of
Theorem 1.46, `thm:rayclassfieldrsicgen`]. -/
theorem IsGhostOverlapQuasiperiodic.liveNormalizedCoefficient_quasiperiodic
    {d : ℕ} [NeZero d]
    (s : GhostFiducialData d)
    (hs : IsGhostOverlapQuasiperiodic d s.normalizedCoefficient)
    (g : ComplexGaloisAutomorphism) :
    IsGhostOverlapQuasiperiodic d (liveNormalizedCoefficient d s g) := by
  intro p p' hmod hp
  set H' := galoisInverseIndexMatrix d g with hH'
  have hmod' : intPhaseSpaceMod d (Matrix.mulVec H' p') =
      intPhaseSpaceMod d (Matrix.mulVec H' p) :=
    intPhaseSpaceMod_matrix_mulVec_eq H' hmod
  have hp' : intPhaseSpaceMod d (Matrix.mulVec H' p) ≠ 0 :=
    intPhaseSpaceMod_matrix_mulVec_ne_zero H'
      (galoisInverseIndexMatrix_det_isCoprime d g) hp
  have hqp := hs _ _ hmod' hp'
  rw [intSymplecticForm_matrix_mulVec] at hqp
  rw [liveNormalizedCoefficient, liveNormalizedCoefficient, hqp, map_mul,
    map_displacementPhase_zpow]
  congr 1
  refine displacementPhase_zpow_eq_of_dbar_dvd_sub ?_
  have hdvd : (dbar d : ℤ) ∣ ((galoisExponent d g : ℤ) * H'.det - 1) := by
    have h := galoisExponent_mul_galoisExponentInv d g
    rw [hH', galoisInverseIndexMatrix, galoisIndexMatrix_det]
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ (dbar d)).mp ?_
    push_cast
    rw [sub_eq_zero, h]
  obtain ⟨t, ht⟩ := hdvd
  refine ⟨t * intSymplecticForm p' p, ?_⟩
  have : (galoisExponent d g : ℤ) * (H'.det * intSymplecticForm p' p) -
      intSymplecticForm p' p =
      ((galoisExponent d g : ℤ) * H'.det - 1) * intSymplecticForm p' p := by
    ring
  rw [this, ht]
  ring

/-- The live coefficient times its displacement operator depends only on the nonzero residue
class modulo `d`. -/
theorem IsGhostOverlapQuasiperiodic.liveSummand_respectsResidues {d : ℕ} [NeZero d]
    (s : GhostFiducialData d)
    (hs : IsGhostOverlapQuasiperiodic d s.normalizedCoefficient)
    (g : ComplexGaloisAutomorphism) :
    RespectsPhaseSpaceResiduesAwayFromZero d
      (fun p => liveNormalizedCoefficient d s g p • integerDisplacement d p) := by
  have hqp := hs.liveNormalizedCoefficient_quasiperiodic s g
  have h := hqp.rawTwistedNormalizedGhostSummand_respectsResidues
    (1 : Mat(2, ℤ)) (by simpa using isCoprime_one_left)
  intro p p' hmod hp
  have := h p p' hmod hp
  simpa only [rawTwistedNormalizedGhostSummand, Matrix.one_mulVec] using this

/-! ### The reindexed Galois image

Applying `g` entrywise first gives displacements indexed by `H_g p`; reindexing the finite sum
returns the expansion to the standard displacement basis and introduces
`liveNormalizedCoefficient`. -/

/-- Entrywise Galois conjugation of an abstract ghost fiducial conjugates every coefficient and
moves each displacement index by `H_g`; this is the middle display in [AFK25, proof of Theorem
1.46, `thm:rayclassfieldrsicgen`]. -/
theorem IsGhostFiducialWith.mapMatrix_eq_mulVec_sum {d r : ℕ} [NeZero d]
    {P : Mat(d, ℂ)} {s : GhostFiducialData d}
    (hP : IsGhostFiducialWith r P s) (g : ComplexGaloisAutomorphism)
    (I : PhaseSpaceTransversal d) :
    g.mapMatrix P =
      ((r : ℂ) / (d : ℂ)) • 1 +
        g (ghostFiducialPrefactor d r : ℂ) •
          ∑ q : PhaseSpaceMod d, if q = 0 then 0 else
            g (s.normalizedCoefficient (I.repr q)) •
              integerDisplacement d
                (Matrix.mulVec (galoisIndexMatrix (galoisExponent d g)) (I.repr q)) := by
  have h1 : g ((r : ℂ) / (d : ℂ)) •
      g.mapMatrix (1 : Mat(d, ℂ)) =
      ((r : ℂ) / (d : ℂ)) • (1 : Mat(d, ℂ)) := by
    simp
  have h2 : ∀ q : PhaseSpaceMod d,
      g.mapMatrix (if q = 0 then 0 else
        s.overlaps.normalized (s.twistedIndex (I.repr q)) •
          integerDisplacement d (I.repr q)) =
        if q = 0 then 0 else
          g (s.normalizedCoefficient (I.repr q)) •
            integerDisplacement d
              (Matrix.mulVec (galoisIndexMatrix (galoisExponent d g)) (I.repr q)) := by
    intro q
    by_cases hq : q = 0
    · simp [hq]
    · rw [ite_eq_right hq, ite_eq_right hq, RCLike.real_smul_eq_coe_smul (K := ℂ), mapMatrix_smul,
        mapMatrix_integerDisplacement]
      rfl
  rw [hP.expansion I, ghostFiducialMatrix, map_add,
    RCLike.real_smul_eq_coe_smul (K := ℂ), mapMatrix_smul, mapMatrix_smul, map_sum, h1,
    Finset.sum_congr rfl (fun q _ => h2 q)]
  rfl

/-- Reindexing the preceding display by the `H_g` permutation gives the standard displacement
expansion with live normalized coefficients. -/
theorem IsGhostFiducialWith.mapMatrix_eq_live_sum {d r : ℕ} [NeZero d]
    {P : Mat(d, ℂ)} {s : GhostFiducialData d}
    (hP : IsGhostFiducialWith r P s)
    (hs : IsGhostOverlapQuasiperiodic d s.normalizedCoefficient)
    (g : ComplexGaloisAutomorphism) (I : PhaseSpaceTransversal d) :
    g.mapMatrix P =
      ((r : ℂ) / (d : ℂ)) • 1 +
        g (ghostFiducialPrefactor d r : ℂ) •
          ∑ q : PhaseSpaceMod d, if q = 0 then 0 else
            liveNormalizedCoefficient d s g (I.repr q) •
              integerDisplacement d (I.repr q) := by
  rw [hP.mapMatrix_eq_mulVec_sum g I]
  congr 2
  refine Eq.trans ?_
    (sum_transversal_mulVec_eq_of_respectsResidues
      (fun p => liveNormalizedCoefficient d s g p • integerDisplacement d p)
      (hs.liveSummand_respectsResidues s g)
      (galoisIndexMatrix (galoisExponent d g)) (galoisIndexMatrix_det_isCoprime d g) I)
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : q = 0
  · simp [hq]
  · rw [ite_eq_right hq, ite_eq_right hq, liveNormalizedCoefficient_mulVec]

/-! ### Reciprocity, unit modulus, and Hermiticity

Reciprocity is part of `GhostOverlapData`. The twist is invertible modulo `dbar d`, so composing
with it preserves the nonzero side condition. After Galois transport, unit modulus turns the
reciprocal at `-p` into complex conjugation. -/

/-- Applying a Galois automorphism preserves the reciprocal identity of a packaged ghost
coefficient. -/
theorem map_normalizedCoefficient_mul_neg {d : ℕ} [NeZero d]
    (s : GhostFiducialData d) (g : ComplexGaloisAutomorphism)
    (p : IntPhaseSpace) (hp : intPhaseSpaceMod d p ≠ 0) :
    g (s.normalizedCoefficient p) * g (s.normalizedCoefficient (-p)) = 1 := by
  rw [← map_mul, s.normalizedCoefficient_mul_neg p hp, map_one]

/-- Unit modulus turns the transported reciprocal identity into conjugate symmetry. -/
theorem map_normalizedCoefficient_neg_eq_conj {d : ℕ} [NeZero d]
    (s : GhostFiducialData d) (g : ComplexGaloisAutomorphism)
    (p : IntPhaseSpace) (hp : intPhaseSpaceMod d p ≠ 0)
    (hg : ‖g (s.normalizedCoefficient p)‖ = 1) :
    g (s.normalizedCoefficient (-p)) = starRingEnd ℂ (g (s.normalizedCoefficient p)) := by
  have hmul := map_normalizedCoefficient_mul_neg s g p hp
  rw [eq_inv_of_mul_eq_one_right hmul, Complex.inv_eq_conj hg]

/-- A live-conversion condition gives unit modulus for the reindexed live coefficients. -/
theorem LiveConversionCondition.norm_liveNormalizedCoefficient {d : ℕ} [NeZero d]
    {s : GhostFiducialData d} {g : ComplexGaloisAutomorphism}
    (hg : LiveConversionCondition s g) (p : IntPhaseSpace)
    (hp : intPhaseSpaceMod d p ≠ 0) :
    ‖liveNormalizedCoefficient d s g p‖ = 1 :=
  hg _ (intPhaseSpaceMod_matrix_mulVec_ne_zero _
    (galoisInverseIndexMatrix_det_isCoprime d g) hp)

/-- The reindexed live coefficients are conjugate-symmetric under negation. -/
theorem LiveConversionCondition.liveNormalizedCoefficient_neg {d : ℕ} [NeZero d]
    {s : GhostFiducialData d} {g : ComplexGaloisAutomorphism}
    (hg : LiveConversionCondition s g) (p : IntPhaseSpace)
    (hp : intPhaseSpaceMod d p ≠ 0) :
    liveNormalizedCoefficient d s g (-p) =
      starRingEnd ℂ (liveNormalizedCoefficient d s g p) := by
  have hp' : intPhaseSpaceMod d
      (Matrix.mulVec (galoisInverseIndexMatrix d g) p) ≠ 0 :=
    intPhaseSpaceMod_matrix_mulVec_ne_zero _
      (galoisInverseIndexMatrix_det_isCoprime d g) hp
  rw [liveNormalizedCoefficient, liveNormalizedCoefficient, Matrix.mulVec_neg]
  exact map_normalizedCoefficient_neg_eq_conj s g _ hp' (hg _ hp')

/-! ### The general ghost prefactor under Galois transport

The prefactor has rational square. Any ambient `Q`-automorphism therefore moves it only by a sign,
which preserves both self-adjointness and its norm. -/

/-- The square of the ghost-fiducial prefactor is its defining rational radicand. -/
theorem ghostFiducialPrefactor_sq_eq_ratCast (d r : ℕ) (hr : 0 < r) (hrd : r < d) :
    ((ghostFiducialPrefactor d r : ℝ) : ℂ) ^ 2 =
      (((((r : ℚ) * ((d : ℚ) - (r : ℚ))) /
        ((d : ℚ) ^ 2 * ((d : ℚ) ^ 2 - 1))) : ℚ) : ℂ) := by
  rw [ghostFiducialPrefactor, ← Complex.ofReal_pow,
    Real.sq_sqrt (Real.sqrt_pos.mp (ghostFiducialPrefactor_pos hr hrd)).le]
  push_cast
  ring

/-- A Galois image of the real ghost-fiducial prefactor is self-adjoint. -/
theorem isSelfAdjoint_map_ghostFiducialPrefactor (d r : ℕ) (hr : 0 < r) (hrd : r < d)
    (g : ComplexGaloisAutomorphism) :
    IsSelfAdjoint (g (ghostFiducialPrefactor d r : ℂ)) := by
  have hreal : IsSelfAdjoint (ghostFiducialPrefactor d r : ℂ) :=
    isSelfAdjoint_iff.mpr (Complex.conj_ofReal _)
  rcases map_eq_self_or_neg_of_sq_eq_ratCast g
      (ghostFiducialPrefactor_sq_eq_ratCast d r hr hrd) with h | h <;> rw [h]
  · exact hreal
  · exact hreal.neg

/-- The norm of the transported prefactor, multiplied by `d`, is the overlap norm prescribed for
a rank-`r` SIC. -/
theorem norm_map_ghostFiducialPrefactor_mul_dimension (d r : ℕ)
    (hr : 0 < r) (hrd : r < d) (g : ComplexGaloisAutomorphism) :
    ‖g (ghostFiducialPrefactor d r : ℂ)‖ * (d : ℝ) =
      Real.sqrt ((r * (d - r) : ℝ) / (d ^ 2 - 1)) := by
  rw [norm_map_eq_of_sq_eq_ratCast g
      (ghostFiducialPrefactor_sq_eq_ratCast d r hr hrd),
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (ghostFiducialPrefactor_pos hr hrd).le, ghostFiducialPrefactor_eq_div]
  exact div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (lt_trans hr hrd)))

/-- The Galois image of a ghost fiducial is Hermitian when `0 < r < d` and the live-conversion
condition holds. The universal ghost expansion supplies coefficient quasi-periodicity. -/
theorem IsGhostFiducialWith.mapMatrix_isHermitian {d r : ℕ} [NeZero d]
    {P : Mat(d, ℂ)} {s : GhostFiducialData d}
    (hP : IsGhostFiducialWith r P s)
    (g : ComplexGaloisAutomorphism) (hg : LiveConversionCondition s g)
    (hr : 0 < r) (hrd : r < d) :
    (g.mapMatrix P).IsHermitian := by
  have hs := hP.normalizedCoefficient_quasiperiodic hr hrd
  let I := canonicalPhaseSpaceTransversal d
  have hS : (∑ q : PhaseSpaceMod d, if q = 0 then 0 else
      liveNormalizedCoefficient d s g (I.repr q) •
        integerDisplacement d (I.repr q)).IsHermitian :=
    isHermitian_transversal_sum_of_conj_symm _
      (hs.liveSummand_respectsResidues s g)
      (fun p hp => hg.liveNormalizedCoefficient_neg p hp) I
  have hA : (((r : ℂ) / (d : ℂ)) •
      (1 : Mat(d, ℂ))).IsHermitian :=
    Matrix.isHermitian_one.smul (isSelfAdjoint_iff.mpr (by norm_num))
  have hB := hS.smul (isSelfAdjoint_map_ghostFiducialPrefactor d r hr hrd g)
  rw [hP.mapMatrix_eq_live_sum hs g I]
  exact hA.add hB

/-! ### Projector rank and displacement overlaps

Idempotency and trace are transported entrywise. The reindexed expansion then makes each nonzero
displacement overlap a single live coefficient times the transported prefactor and `d`. -/

/-- Entrywise Galois conjugation carries a ghost fiducial's idempotency to its live image. -/
theorem IsGhostFiducialWith.mapMatrix_sq_eq_self {d r : ℕ} [NeZero d]
    {P : Mat(d, ℂ)} {s : GhostFiducialData d}
    (hP : IsGhostFiducialWith r P s) (g : ComplexGaloisAutomorphism) :
    g.mapMatrix P ^ 2 = g.mapMatrix P :=
  SIC.mapMatrix_sq_eq_self g hP.idempotent

/-- Entrywise Galois conjugation preserves the trace `r` of a ghost fiducial. -/
theorem IsGhostFiducialWith.trace_mapMatrix {d r : ℕ} [NeZero d]
    {P : Mat(d, ℂ)} {s : GhostFiducialData d}
    (hP : IsGhostFiducialWith r P s) (g : ComplexGaloisAutomorphism) :
    (g.mapMatrix P).trace = (r : ℂ) := by
  rw [SIC.trace_mapMatrix, hP.expansion (canonicalPhaseSpaceTransversal d),
    trace_ghostFiducialMatrix]
  simp

/-- An entrywise Galois image of a ghost fiducial still has matrix rank `r`. -/
theorem IsGhostFiducialWith.rank_mapMatrix {d r : ℕ} [NeZero d]
    {P : Mat(d, ℂ)} {s : GhostFiducialData d}
    (hP : IsGhostFiducialWith r P s) (g : ComplexGaloisAutomorphism) :
    (g.mapMatrix P).rank = r :=
  rank_eq_of_idempotent_of_trace _ (hP.mapMatrix_sq_eq_self g) (hP.trace_mapMatrix g)

/-- A nonzero displacement overlap of the Galois image is its live normalized coefficient,
multiplied by the transported prefactor and by `d`. -/
theorem IsGhostFiducialWith.overlap_mapMatrix {d r : ℕ} [NeZero d]
    {P : Mat(d, ℂ)} {s : GhostFiducialData d}
    (hP : IsGhostFiducialWith r P s)
    (hs : IsGhostOverlapQuasiperiodic d s.normalizedCoefficient)
    (g : ComplexGaloisAutomorphism) (p : Fin d × Fin d) (hp : p ≠ 0) :
    overlap (g.mapMatrix P) p =
      g (ghostFiducialPrefactor d r : ℂ) *
        ((d : ℂ) * liveNormalizedCoefficient d s g (finPhaseSpaceToInt p)) := by
  let I := canonicalPhaseSpaceTransversal d
  have h0 : ((((r : ℂ) / (d : ℂ)) • (1 : Mat(d, ℂ))) *
      (displacementOperator d p).conjTranspose).trace = 0 := by
    rw [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, Matrix.trace_conjTranspose,
      trace_displacementOperator]
    simp [hp]
  rw [overlap, hP.mapMatrix_eq_live_sum hs g I, Matrix.add_mul, Matrix.trace_add, h0, zero_add,
    Matrix.smul_mul, Matrix.trace_smul,
    trace_transversal_sum_mul_conjTranspose _
      (hs.liveSummand_respectsResidues s g) I p hp, smul_eq_mul]

/-- Every nonzero displacement overlap of the Galois image has the norm required of a rank-`r`
SIC fiducial. -/
theorem IsGhostFiducialWith.norm_overlap_mapMatrix {d r : ℕ} [NeZero d]
    {P : Mat(d, ℂ)} {s : GhostFiducialData d}
    (hP : IsGhostFiducialWith r P s)
    (g : ComplexGaloisAutomorphism) (hg : LiveConversionCondition s g)
    (hr : 0 < r) (hrd : r < d) (p : Fin d × Fin d) (hp : p ≠ 0) :
    ‖overlap (g.mapMatrix P) p‖ =
      Real.sqrt ((r * (d - r) : ℝ) / (d ^ 2 - 1)) := by
  have hs := hP.normalizedCoefficient_quasiperiodic hr hrd
  have hmod : intPhaseSpaceMod d (finPhaseSpaceToInt p) ≠ 0 := by
    intro h
    refine hp ?_
    rw [← intPhaseSpaceToFin_finPhaseSpaceToInt d p, intPhaseSpaceToFin_eq_zero_iff]
    exact h
  rw [hP.overlap_mapMatrix hs g p hp, norm_mul, norm_mul,
    hg.norm_liveNormalizedCoefficient _ hmod, Complex.norm_natCast, mul_one,
    norm_map_ghostFiducialPrefactor_mul_dimension d r hr hrd g]

/-- **General local live-conversion theorem.** If fixed ghost data gives a rank-`r` ghost
fiducial with `0 < r < d` and one fixed automorphism satisfies the unit-modulus live-conversion
condition at every nonzero residue, then the entrywise Galois image is a live rank-`r` SIC
fiducial. Coefficient quasi-periodicity follows from the universal ghost expansion.
This is the parameterized local form of [AFK25, Theorem 1.46,
`thm:rayclassfieldrsicgen`]. -/
theorem IsGhostFiducialWith.mapMatrix_isFiducial {d r : ℕ} [NeZero d]
    {P : Mat(d, ℂ)} {s : GhostFiducialData d}
    (hP : IsGhostFiducialWith r P s)
    (g : ComplexGaloisAutomorphism) (hg : LiveConversionCondition s g)
    (hr : 0 < r) (hrd : r < d) :
    IsFiducial r (g.mapMatrix P) := by
  refine isFiducial_of_overlap_norm r _
    ⟨⟨hP.mapMatrix_isHermitian g hg hr hrd, hP.mapMatrix_sq_eq_self g⟩,
      hP.rank_mapMatrix g⟩ hr hrd ?_
  intro p hp
  exact hP.norm_overlap_mapMatrix g hg hr hrd p hp

end SIC

end
