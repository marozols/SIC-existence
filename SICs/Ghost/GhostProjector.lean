/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Ghost.ShiftConvolution
import SICs.Ghost.RealOverlaps
import SICs.Ghost.CandidateOperator
import SICs.Ghost.CompatibleTwists

/-!
# The candidate ghost fiducial of a shift and a compatible twist

The square law of the twisted displacement sum, idempotency of the candidate, and its ghost data.

This module proves the operator calculation of [AFK25, Theorem 1.45, `thm:ghstExist`], for
an admissible tuple, a shift, and a compatible twist. The candidate of [AFK25, Definition 1.43,
`dfn:CandidateGhostAndSICFiducials`] is idempotent by the shifted convolution identity. Its
real reciprocal coefficients and representative independence then make it a ghost fiducial.
`SICs.Ghost.Datum` bundles these inputs, and `SICs.Ghost.LiveCandidate` handles Galois
conversion of that fixed candidate.

## Mathematical argument

Write `S_G = ∑_{p ≢ 0} ν̃_t(Gp) D_p` (`candidateTwistedSum`) for an integer lift `G` of the twist.
By the Weyl--Heisenberg product rule, `S_G²` is the sum over output classes `p` of
`∑_{q ≠ 0, p} ξ_d^{⟨p,q⟩} ν̃_t(G(p - q)) ν̃_t(Gq)` times `D_p` (`transversalDisplacementSum_sq`).

- At `p = 0` every summand is `ν̃_t(-Gq)ν̃_t(Gq) = 1` by reciprocity, giving `d² - 1`.
- At `p ≢ 0`, the congruence `Det(G) f_t(λ) ≡ 1 (mod d̄)` and `⟨Gp,Gq⟩ = Det(G)⟨p,q⟩` turn the
  phase into `ξ_d^{f_t(λ)⟨Gp,Gq⟩}` (`IsCompatibleTwistLift.displacementPhase_zpow_eq`), and as `q`
  runs through a transversal so does `Gq` (`PhaseSpaceTransversal.map`). The coefficient is then
  the excluded convolution of the shift at `Gp`, which is `(d - 2r)√(d_j + 1) ν̃_t(Gp)`
  (`IsShift.sum_excluded_candidateNormGhostOverlap_mul`, from `SICs.Ghost.ShiftConvolution`).

So `S_G² = (d² - 1)I + (d - 2r)√(d_j + 1) S_G`, by the square law
`transversalDisplacementSum_sq_eq_of_reciprocal`. With `Π̃ = aI + bS_G`, `a = r/d`,
`b = 1/(d√(d_j + 1))` (the scale `√(r(d-r)/(d²-1))` is `1/√(d_j + 1)` by the pair equation
`(d_j + 1) r(d - r) = d² - 1`), idempotency reduces to `a² + b²(d² - 1) = a` and
`2ab + b²(d - 2r)√(d_j + 1) = b` (`smul_one_add_smul_sq_eq_self`), both of which are the pair
equation again. This is the proof in
[AFK25, Section 5.4, `sbsc:proofofghosttheorem`], run with the twist applied to the overlap index
rather than, as in the source, to the displacement index.

The remaining clauses of a ghost fiducial are the realness and reciprocity of
[AFK25, Theorem 5.8, `thm:nupnumpeq1`] (`IsAssociatedStabilizerPair.ghostOverlapData`) and
independence of the transversal ([AFK25, Lemma 1.42, `lem:GhostFiducialIndependenceOfTransversal`]).

**The hypothesis of Theorem 1.45.** The source assumes the Twisted Convolution Conjecture, but its
proof uses only that the fiducial datum's shift `λ` lies in `Z_t`, which is part of
[AFK25, Definition 1.41, `def:fiducialdata`]. The theorems below therefore carry no conjecture;
the explicit shift of [AFK26, Appleby, Flammia, Kopp (2026), Theorem 1.2, `thm:tci`]
(`SICs.Dilogarithm.TwistedConvolution`) supplies such a shift unconditionally.

## References

- [AFK25, Theorem 1.45, `thm:ghstExist`, proof in Section 5.4, `sbsc:proofofghosttheorem`]
- [AFK25, Definition 1.41, `def:fiducialdata`; Definition 1.43,
  `dfn:CandidateGhostAndSICFiducials`; Definition 1.11, `dfn:ghostFiducial`; Lemma 1.44,
  `lm:OverlapTermsGhostOverlap`; Theorem 1.46, `thm:rayclassfieldrsicgen`]
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

namespace AdmissibleTuple

/-! ### The twisted nonidentity sum and its square

The nonidentity part of the candidate ghost operator, with the twist applied to the overlap
index, squares to a combination of the identity and itself. -/

/-- The twisted nonidentity part `S_G = ∑_{q ≢ 0} ν̃_t(Gq) D_q` of the candidate ghost operator,
summed over the representatives `q` of a complete transversal `I`, for an integer twist lift `G`.
-/
noncomputable def candidateTwistedSum (t : AdmissibleTuple) (A : SL(2, ℤ))
    (G : Mat(2, ℤ)) (I : PhaseSpaceTransversal t.d) :
    Mat(t.d, ℂ) :=
  ∑ q : PhaseSpaceMod t.d, if q = 0 then 0 else
    t.candidateNormGhostOverlap A (Matrix.mulVec G (I.repr q)) • integerDisplacement t.d (I.repr q)

/-- **The overlap scale of an admissible tuple is `1/√(d_j + 1)`**:
`√(r(d-r)/(d²-1)) · √(d_j + 1) = 1`, from the pair equation `(d_j + 1) r(d - r) = d² - 1`
(`AdmissiblePair.equation_int`, `pair_n_eq`). This is the rewriting of the prefactor of
[AFK25, equation (1.53), `eq:ghostProjectorDef`] as `1/(d√(d_j + 1))` at the start of the proof of
[AFK25, Theorem 1.45, `thm:ghstExist`]. -/
theorem sqrt_overlapScale_mul_sqrt (t : AdmissibleTuple) :
    Real.sqrt ((t.r * (t.d - t.r) : ℝ) / ((t.d : ℝ) ^ 2 - 1)) *
      Real.sqrt ((t.triple.towerDimension : ℝ) + 1) = 1 := by
  have hdr : (t.r : ℝ) < t.d := by exact_mod_cast t.pair.rank_lt_d
  have hr0 : (0 : ℝ) < t.r := by exact_mod_cast t.pair.rank_pos
  have hd1N : (1 : ℕ) < t.d := lt_trans (by omega) t.three_lt_d
  have hd1 : (1 : ℝ) < t.d := by exact_mod_cast hd1N
  have hden : (0 : ℝ) < (t.d : ℝ) ^ 2 - 1 := by nlinarith
  rw [← Real.sqrt_mul (by positivity :
    0 ≤ (t.r * (t.d - t.r) : ℝ) / ((t.d : ℝ) ^ 2 - 1))]
  have heqZ := t.pair.equation_int
  rw [t.pair_n_eq] at heqZ
  have heq := congrArg (fun z : ℤ => (z : ℝ)) heqZ
  norm_num at heq
  rw [show (t.r * (t.d - t.r) : ℝ) / ((t.d : ℝ) ^ 2 - 1) *
      ((t.triple.towerDimension : ℝ) + 1) = 1 by
    field_simp [ne_of_gt hden]
    nlinarith [heq]]
  exact Real.sqrt_one

/-- **The candidate operator of an integer lift is `(r/d) I + d⁻¹√(r(d-r)/(d²-1)) S_G`**: off the
zero class the twisted index `Gq` is nonzero modulo `d`
(`intPhaseSpaceMod_matrix_mulVec_ne_zero`), where the raw overlap `rawGhostOverlap` is the scaled
normalized one. -/
theorem candidateGhostOperatorOfLift_eq_twistedSum (t : AdmissibleTuple)
    (A : SL(2, ℤ)) {G : Mat(2, ℤ)} (hG : IsCoprime G.det (dbar t.d : ℤ))
    (I : PhaseSpaceTransversal t.d) :
    candidateGhostOperatorOfLift t A G I =
      ((t.r : ℂ) / (t.d : ℂ)) • (1 : Mat(t.d, ℂ)) +
        ((t.d : ℂ)⁻¹ * (Real.sqrt ((t.r * (t.d - t.r) : ℝ) / ((t.d : ℝ) ^ 2 - 1)) : ℂ)) •
          t.candidateTwistedSum A G I := by
  unfold candidateGhostOperatorOfLift rawTwistedGhostSummand rawGhostOverlap candidateTwistedSum
  congr 1
  rw [Finset.smul_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : q = 0
  · simp only [hq, ↓reduceIte, smul_zero]
  · rw [ite_eq_right hq, ite_eq_right hq]
    have hp : intPhaseSpaceMod t.d (I.repr q) ≠ 0 := by
      rw [I.residue_repr]
      exact hq
    have hGp := intPhaseSpaceMod_matrix_mulVec_ne_zero G hG hp
    rw [ite_eq_right hGp, smul_smul, smul_smul]
    congr 1
    ring

/-- At a nonzero output class `p`, the coefficient of `D_p` in `S_G²` is the excluded
convolution of the shift at `Gp`, over the image transversal `I.map G`: the compatible twist moves
the phase to the twisted indices (`IsCompatibleTwistLift.displacementPhase_zpow_eq`), and
`q ↦ Gq` reindexes the sum (`PhaseSpaceTransversal.sum_ite_map_repr`). -/
private lemma candidateTwistedSum_nonzeroCoefficient {t : AdmissibleTuple}
    {A Lz : SL(2, ℤ)} (h : t.IsAssociatedStabilizerPair A Lz) {lam : ℤ}
    (hlam : t.IsShift A Lz lam) {G : Mat(2, ℤ)}
    (hG : t.IsCompatibleTwistLift lam G) (I : PhaseSpaceTransversal t.d)
    (hI0 : I.repr 0 = 0) (p : PhaseSpaceMod t.d) (hp : p ≠ 0) :
    (∑ q : PhaseSpaceMod t.d, if q = 0 ∨ q = p then 0 else
      displacementPhase t.d ^ intSymplecticForm (I.repr p) (I.repr q) *
        t.candidateNormGhostOverlap A (Matrix.mulVec G (I.repr p - I.repr q)) *
        t.candidateNormGhostOverlap A (Matrix.mulVec G (I.repr q))) =
      ((((t.d : ℝ) - 2 * t.r) * Real.sqrt ((t.triple.towerDimension : ℝ) + 1) : ℝ) : ℂ) *
        t.candidateNormGhostOverlap A (Matrix.mulVec G (I.repr p)) := by
  have hGcop := hG.det_isCoprime
  have hGd := isCoprime_of_isCoprime_dbar hGcop
  set P := Matrix.mulVec G (I.repr p)
  have hPe : intPhaseSpaceMod t.d P = phaseSpaceModMulVecEquiv G hGd p := by
    rw [intPhaseSpaceMod_mulVec_eq_mulVecEquiv G hGd, I.residue_repr]
  have hP : intPhaseSpaceMod t.d P ≠ 0 := by
    rw [hPe, Ne, phaseSpaceModMulVecEquiv_eq_zero_iff]
    exact hp
  have hJP : (I.map G hGd).repr (intPhaseSpaceMod t.d P) = P := by
    rw [hPe]
    exact I.map_repr_apply G hGd p
  rw [Finset.sum_congr rfl fun q _ => by
      rw [Matrix.mulVec_sub, hG.displacementPhase_zpow_eq (I.repr p) (I.repr q)],
    I.sum_ite_map_repr G hGd (fun X => displacementPhase t.d ^
      (twistFnInt t.d t.r t.triple.towerDimension lam * intSymplecticForm P X) *
        t.candidateNormGhostOverlap A (P - X) * t.candidateNormGhostOverlap A X) p, ← hPe]
  exact hlam.sum_excluded_candidateNormGhostOverlap_mul h hP (I.map G hGd)
    (I.map_repr_zero G hGd hI0) hJP

/-- **The square of the twisted nonidentity sum**: if `λ` is a shift for `t` and the integer
matrix `G` satisfies the compatibility congruence `Det(G) f_t(λ) ≡ 1 (mod d̄)`, then for every
complete transversal `I` representing the zero class by `0`,
`S_G² = (d² - 1) I + (d - 2r)√(d_j + 1) S_G`. See the module docstring: the coefficient of `D_0` is
`d² - 1` by reciprocity (`candidateNormGhostOverlap_reciprocal`), and the coefficient of `D_p`,
`p ≢ 0`, is the excluded convolution of the shift at `Gp` over the transversal `I.map G`
(`IsShift.sum_excluded_candidateNormGhostOverlap_mul`). This is the evaluation of the double sum
in [AFK25, equation (5.79), `eq:Pi2MinusPia`] in the proof of [AFK25, Theorem 1.45,
`thm:ghstExist`]. -/
theorem IsShift.candidateTwistedSum_sq {t : AdmissibleTuple} {A Lz : SL(2, ℤ)}
    (h : t.IsAssociatedStabilizerPair A Lz) {lam : ℤ} (hlam : t.IsShift A Lz lam)
    {G : Mat(2, ℤ)} (hG : t.IsCompatibleTwistLift lam G)
    (I : PhaseSpaceTransversal t.d) (hI0 : I.repr 0 = 0) :
    t.candidateTwistedSum A G I ^ 2 =
      ((t.d : ℂ) ^ 2 - 1) • (1 : Mat(t.d, ℂ)) +
        ((((t.d : ℝ) - 2 * t.r) * Real.sqrt ((t.triple.towerDimension : ℝ) + 1) : ℝ) : ℂ) •
          t.candidateTwistedSum A G I := by
  have hGcop := hG.det_isCoprime
  refine transversalDisplacementSum_sq_eq_of_reciprocal
    (fun p => t.candidateNormGhostOverlap A (Matrix.mulVec G p))
    (h.candidateNormGhostOverlap_quasiperiodic.rawTwistedNormalizedGhostSummand_respectsResidues
      G hGcop) I hI0 _ (fun p hp => ?_)
    (fun p hp => candidateTwistedSum_nonzeroCoefficient h hlam hG I hI0 p hp)
  simpa only [Matrix.mulVec_neg] using h.candidateNormGhostOverlap_reciprocal _
    (intPhaseSpaceMod_matrix_mulVec_ne_zero G hGcop hp)

/-! ### Idempotency

Substituting the square of the twisted sum reduces `Π̃² = Π̃` to two scalar identities, both
equivalent to the pair equation. -/

/-- The two scalar identities of idempotency: with `a = r/d`, `b = d⁻¹x`,
`x = √(r(d-r)/(d²-1))` and `C = (d - 2r)√(d_j + 1)`, `a² + b²(d² - 1) = a` and
`2ab + b²C = b`. Both are the pair equation `(d_j + 1) r(d - r) = d² - 1`, the second through
`x√(d_j + 1) = 1` (`sqrt_overlapScale_mul_sqrt`). -/
private lemma candidateGhostOperator_scalar_identities (t : AdmissibleTuple) :
    ((t.r : ℂ) / t.d) ^ 2 + ((t.d : ℂ)⁻¹ *
        (Real.sqrt ((t.r * (t.d - t.r) : ℝ) / ((t.d : ℝ) ^ 2 - 1)) : ℂ)) ^ 2 *
          ((t.d : ℂ) ^ 2 - 1) = (t.r : ℂ) / t.d ∧
      2 * ((t.r : ℂ) / t.d) * ((t.d : ℂ)⁻¹ *
          (Real.sqrt ((t.r * (t.d - t.r) : ℝ) / ((t.d : ℝ) ^ 2 - 1)) : ℂ)) +
        ((t.d : ℂ)⁻¹ * (Real.sqrt ((t.r * (t.d - t.r) : ℝ) / ((t.d : ℝ) ^ 2 - 1)) : ℂ)) ^ 2 *
          ((((t.d : ℝ) - 2 * t.r) * Real.sqrt ((t.triple.towerDimension : ℝ) + 1) : ℝ) : ℂ) =
        (t.d : ℂ)⁻¹ * (Real.sqrt ((t.r * (t.d - t.r) : ℝ) / ((t.d : ℝ) ^ 2 - 1)) : ℂ) := by
  set x : ℝ := Real.sqrt ((t.r * (t.d - t.r) : ℝ) / ((t.d : ℝ) ^ 2 - 1)) with hxdef
  set R : ℝ := Real.sqrt ((t.triple.towerDimension : ℝ) + 1) with hR
  have hd1 : (1 : ℝ) < t.d := by exact_mod_cast lt_trans (by omega) t.three_lt_d
  have hdr : (t.r : ℝ) < t.d := by exact_mod_cast t.pair.rank_lt_d
  have hx2 : x ^ 2 = (t.r * (t.d - t.r) : ℝ) / ((t.d : ℝ) ^ 2 - 1) :=
    Real.sq_sqrt (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (by nlinarith))
  have hxR' : x * R = 1 := sqrt_overlapScale_mul_sqrt t
  have hxR : (x : ℂ) * (R : ℂ) = 1 := by rw [← Complex.ofReal_mul, hxR', Complex.ofReal_one]
  have hd0 : (t.d : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne t.d)
  have hden : (t.d : ℂ) ^ 2 - 1 ≠ 0 := by exact_mod_cast (show (t.d : ℝ) ^ 2 - 1 ≠ 0 by nlinarith)
  have hx2C : (x : ℂ) ^ 2 * ((t.d : ℂ) ^ 2 - 1) = (t.r : ℂ) * (t.d - t.r) := by
    rw [← Complex.ofReal_pow, hx2]
    push_cast
    field_simp
  constructor
  · field_simp
    linear_combination hx2C
  · push_cast
    field_simp
    linear_combination ((x : ℂ) * ((t.d : ℂ) - 2 * t.r)) * hxR

/-- **Idempotency of the candidate ghost operator of an integer lift**: a shift `λ` and an integer
matrix `G` with `Det(G) f_t(λ) ≡ 1 (mod d̄)` make `candidateGhostOperatorOfLift t A_t G I`
idempotent, for every complete transversal `I`. The transversal is first replaced by the canonical
one (`IsAssociatedStabilizerPair.candidateGhostOperatorOfLift_eq_of_transversal`), which represents
the zero class by `0`; then `candidateGhostOperatorOfLift_eq_twistedSum`,
`IsShift.candidateTwistedSum_sq` and `sqrt_overlapScale_mul_sqrt` leave scalar algebra. This is the
idempotency step (4) of the proof of [AFK25, Theorem 1.45, `thm:ghstExist`]. -/
theorem IsShift.candidateGhostOperatorOfLift_sq {t : AdmissibleTuple} {A Lz : SL(2, ℤ)}
    (h : t.IsAssociatedStabilizerPair A Lz) {lam : ℤ} (hlam : t.IsShift A Lz lam)
    {G : Mat(2, ℤ)} (hG : t.IsCompatibleTwistLift lam G)
    (I : PhaseSpaceTransversal t.d) :
    candidateGhostOperatorOfLift t A G I ^ 2 = candidateGhostOperatorOfLift t A G I := by
  have hGcop := hG.det_isCoprime
  let J := canonicalPhaseSpaceTransversal t.d
  rw [h.candidateGhostOperatorOfLift_eq_of_transversal G hGcop I J,
    candidateGhostOperatorOfLift_eq_twistedSum t A hGcop J]
  obtain ⟨h₁, h₂⟩ := candidateGhostOperator_scalar_identities t
  exact smul_one_add_smul_sq_eq_self
    (hlam.candidateTwistedSum_sq h hG J (canonicalPhaseSpaceTransversal_repr_zero t.d)) h₁ h₂

/-- **Idempotency of the candidate ghost operator** of a quotient twist compatible with a shift:
`IsShift.candidateGhostOperatorOfLift_sq` at the canonical integer lift
(`isCompatibleTwist_iff_integerLift`). -/
theorem IsShift.candidateGhostOperator_sq {t : AdmissibleTuple} {A Lz : SL(2, ℤ)}
    (h : t.IsAssociatedStabilizerPair A Lz) {lam : ℤ} (hlam : t.IsShift A Lz lam)
    {g : GhostTwist t.d} (hg : t.IsCompatibleTwist lam g) :
    t.candidateGhostOperator A g ^ 2 = t.candidateGhostOperator A g := by
  exact hlam.candidateGhostOperatorOfLift_sq h
    ((t.isCompatibleTwist_iff_integerLift lam g).mp hg)
    (canonicalPhaseSpaceTransversal t.d)

/-! ### The ghost-fiducial expansion of the candidate

The candidate operator is the expansion `ghostFiducialMatrix` of the tuple's real overlap data
with the twist, so the ghost-fiducial predicate needs only idempotency. -/

/-- The ghost-fiducial data of the candidate ghost operator of `t` with twist `g`: the tuple's real
normalized overlaps `IsAssociatedStabilizerPair.ghostOverlapData` ([AFK25, Theorem 5.8,
`thm:nupnumpeq1`]) together with `g`. -/
noncomputable def IsAssociatedStabilizerPair.ghostFiducialData {t : AdmissibleTuple}
    {A Lz : SL(2, ℤ)} (h : t.IsAssociatedStabilizerPair A Lz) (g : GhostTwist t.d) :
    GhostFiducialData t.d where
  overlaps := h.ghostOverlapData
  twist := g

/-- The packaged coefficient of the tuple's ghost-fiducial data is the candidate overlap at the
twisted index: `v(p) = ν̃_t(Gp)` for `p ≢ 0 (mod d)` and any integer lift `G` of the twist
(`IsGhostTwistLift.intPhaseSpaceMod_mulVec_eq_twistedIndex`,
`ofReal_ghostOverlapData_normalized`). -/
theorem IsAssociatedStabilizerPair.ghostFiducialData_normalizedCoefficient {t : AdmissibleTuple}
    {A Lz : SL(2, ℤ)} (h : t.IsAssociatedStabilizerPair A Lz) (g : GhostTwist t.d)
    {G : Mat(2, ℤ)} (hG : IsGhostTwistLift G g) {p : IntPhaseSpace}
    (hp : intPhaseSpaceMod t.d p ≠ 0) :
    (h.ghostFiducialData g).normalizedCoefficient p =
      t.candidateNormGhostOverlap A (Matrix.mulVec G p) := by
  unfold GhostFiducialData.normalizedCoefficient
  rw [← hG.intPhaseSpaceMod_mulVec_eq_twistedIndex (h.ghostFiducialData g) p]
  exact h.ofReal_ghostOverlapData_normalized
    (intPhaseSpaceMod_matrix_mulVec_ne_zero G hG.det_isCoprime hp)

/-- **The candidate operator of a lift is the ghost-fiducial expansion** of the tuple's
ghost-fiducial data: `candidateGhostOperatorOfLift t A_t G I = ghostFiducialMatrix r (t, g) I` for
every integer lift `G` of `g` and every transversal `I`. The prefactors agree,
`d⁻¹√(r(d-r)/(d²-1)) = √(r(d-r)/(d²(d²-1)))` (`ghostFiducialPrefactor`), and so do the
coefficients (`ghostFiducialData_normalizedCoefficient`). -/
theorem IsAssociatedStabilizerPair.candidateGhostOperatorOfLift_eq_fiducialMatrix
    {t : AdmissibleTuple} {A Lz : SL(2, ℤ)} (h : t.IsAssociatedStabilizerPair A Lz)
    {g : GhostTwist t.d} {G : Mat(2, ℤ)} (hG : IsGhostTwistLift G g)
    (I : PhaseSpaceTransversal t.d) :
    candidateGhostOperatorOfLift t A G I = ghostFiducialMatrix t.r (h.ghostFiducialData g) I := by
  have hprefC : ((ghostFiducialPrefactor t.d t.r : ℝ) : ℂ) =
      (t.d : ℂ)⁻¹ * (Real.sqrt ((t.r * (t.d - t.r) : ℝ) / ((t.d : ℝ) ^ 2 - 1)) : ℂ) := by
    rw [ghostFiducialPrefactor_eq_div]
    push_cast
    ring
  rw [candidateGhostOperatorOfLift_eq_twistedSum t A hG.det_isCoprime I, ← hprefC,
    ghostFiducialMatrix, RCLike.real_smul_eq_coe_smul (K := ℂ), candidateTwistedSum]
  congr 2
  refine Finset.sum_congr rfl fun q _ => ?_
  split_ifs with hq
  · rfl
  · rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    exact congrArg (· • integerDisplacement t.d (I.repr q))
      (h.ghostFiducialData_normalizedCoefficient g hG (by rwa [I.residue_repr])).symm

/-- The candidate ghost operator of a quotient twist is the ghost-fiducial expansion of the
tuple's ghost-fiducial data over every transversal
(`candidateGhostOperatorOfLift_eq_fiducialMatrix` at the canonical lift). -/
theorem IsAssociatedStabilizerPair.candidateGhostOperator_eq_fiducialMatrix
    {t : AdmissibleTuple} {A Lz : SL(2, ℤ)} (h : t.IsAssociatedStabilizerPair A Lz)
    (g : GhostTwist t.d) (I : PhaseSpaceTransversal t.d) :
    t.candidateGhostOperator A g = ghostFiducialMatrix t.r (h.ghostFiducialData g) I := by
  rw [h.candidateGhostOperator_eq_of_lift_transversal g.integerLift_isLift I]
  exact h.candidateGhostOperatorOfLift_eq_fiducialMatrix g.integerLift_isLift I

/-- **The local form of [AFK25, Theorem 1.45, `thm:ghstExist`]**: for an associated stabilizer
pair, a shift `λ` and a twist `g` compatible with it, the candidate ghost operator is a ghost
`r`-SIC fiducial with the tuple's ghost-fiducial data (`isGhostFiducialWith_of_idempotent`,
`IsShift.candidateGhostOperator_sq`, `candidateGhostOperator_eq_fiducialMatrix`, and
representative independence from `ghostOverlapData_integerPullback_quasiperiodic`). The
Twisted Convolution Conjecture assumed by the source is not needed: see the module docstring. -/
theorem IsShift.candidateGhostOperator_isGhostFiducialWith {t : AdmissibleTuple}
    {A Lz : SL(2, ℤ)} (h : t.IsAssociatedStabilizerPair A Lz) {lam : ℤ}
    (hlam : t.IsShift A Lz lam) {g : GhostTwist t.d} (hg : t.IsCompatibleTwist lam g) :
    IsGhostFiducialWith t.r (t.candidateGhostOperator A g) (h.ghostFiducialData g) := by
  apply isGhostFiducialWith_of_idempotent
  · exact GhostFiducialData.hasRepresentativeIndependentSummand_of_quasiperiodic _
      h.ghostOverlapData_integerPullback_quasiperiodic
  · exact h.candidateGhostOperator_eq_fiducialMatrix g _
  · exact hlam.candidateGhostOperator_sq h hg

end AdmissibleTuple

end SIC

end
