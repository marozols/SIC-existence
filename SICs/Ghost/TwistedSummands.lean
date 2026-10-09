/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Ghost.OverlapData
import SICs.Quantum.DisplacementSums

/-!
# Twisted ghost summands and their independence properties

Twisted summands, phase cancellation, and independence of lifts and transversals.

This file proves the finite-sum independence in [AFK25, Lemma 1.42,
`lem:GhostFiducialIndependenceOfTransversal`] from abstract quasiperiodic overlaps.
It combines an integer lift of a quotient twist, an overlap coefficient and an integer
displacement operator. Both normalized and unnormalized summands are included.

Changing a representative contributes opposite phases in the overlap and displacement.
The determinant's coprimality makes the remaining phase a multiple of `dbar d`, hence
one. The full summand therefore descends to each nonzero residue class, and the generic
transversal-sum API proves independence of the transversal and the chosen integer lift.
The resulting ghost-fiducial matrices are packaged in `SICs.Ghost.Fiducials`.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### The determinant phase

Coprimality removes the residual phase after twisting the overlap index. -/

/-- Coprimality of a twist determinant makes its residual representative-change exponent a
multiple of `dbar d`: for `p' ≡ p (mod d)` and `a` coprime to `dbar d`,
`dbar d ∣ (a - 1)⟨p',p⟩`, because `a` is odd when `d` is even. -/
lemma dbar_dvd_det_sub_one_mul_symplectic {d : ℕ}
    {p p' : IntPhaseSpace} (h : intPhaseSpaceMod d p' = intPhaseSpaceMod d p)
    (a : ℤ) (ha : IsCoprime a (dbar d : ℤ)) :
    (dbar d : ℤ) ∣ (a - 1) * intSymplecticForm p' p := by
  obtain ⟨s, hs⟩ := dvd_intSymplecticForm_of_mod_eq h
  by_cases hd : d % 2 = 1
  · rw [dbar, ite_eq_left hd]
    refine ⟨(a - 1) * s, ?_⟩
    rw [hs]
    ring
  · have hc : IsCoprime a ((2 : ℤ) * (d : ℤ)) := by
      simpa only [dbar, ite_eq_right hd, Nat.cast_mul, Nat.cast_ofNat] using ha
    have haodd : Odd a := Int.isCoprime_two_right.mp hc.of_mul_right_left
    obtain ⟨k, hk⟩ := haodd
    rw [dbar, ite_eq_right hd]
    refine ⟨k * s, ?_⟩
    rw [hs, hk]
    push_cast
    ring

/-! ### Normalized and unnormalized twisted summands

These definitions combine a lifted twist, an overlap coefficient, and an integer displacement.
The normalized and scaled versions are shown independent of the selected lift and representative. -/

/-- The normalized integer-indexed ghost summand associated with a raw overlap function `v` and
an integer lift `G` of a twist.

The explicit SF candidate from [AFK25] specializes this construction to its overlap function. -/
noncomputable def rawTwistedNormalizedGhostSummand {d : ℕ} [NeZero d]
    (G : Mat(2, ℤ)) (v : IntPhaseSpace → ℂ) (p : IntPhaseSpace) :
    Mat(d, ℂ) :=
  v (Matrix.mulVec G p) • integerDisplacement d p

/-- A quasiperiodic raw normalized overlap evaluated after a quotient twist is independent of
the chosen integer lift, away from the zero residue class modulo `d`. -/
theorem IsGhostOverlapQuasiperiodic.eq_matrix_mulVec_of_isLift
    {d : ℕ} [NeZero d] {v : IntPhaseSpace → ℂ}
    (hv : IsGhostOverlapQuasiperiodic d v)
    {G H : Mat(2, ℤ)} {g : GhostTwist d}
    (hG : IsGhostTwistLift G g) (hH : IsGhostTwistLift H g)
    {p : IntPhaseSpace} (hp : intPhaseSpaceMod d p ≠ 0) :
    v (Matrix.mulVec G p) = v (Matrix.mulVec H p) := by
  have hbar := hG.intPhaseSpaceMod_mulVec_eq_of_lifts hH p
  have hd := intPhaseSpaceMod_eq_of_dbar_eq hbar
  have hGne := intPhaseSpaceMod_matrix_mulVec_ne_zero G hG.det_isCoprime hp
  have hv' := hv (Matrix.mulVec G p) (Matrix.mulVec H p) hd.symm hGne
  rw [hv']
  have hphase : displacementPhase d ^ intSymplecticForm (Matrix.mulVec H p)
      (Matrix.mulVec G p) = 1 :=
    displacementPhase_zpow_eq_one_of_dbar_dvd (dvd_intSymplecticForm_of_mod_eq hbar.symm)
  rw [hphase, one_mul]

/-- The abstract algebraic implication underlying [AFK25, Lemma 1.42,
`lem:GhostFiducialIndependenceOfTransversal`]: quasiperiodicity of a raw
normalized overlap function makes its twisted displacement summand depend only on the nonzero
residue class modulo `d`.

The theorem assumes the quasiperiodicity conclusion `IsGhostOverlapQuasiperiodic`; it does not
establish that analytic input for a concrete overlap family. The matrix `G` is an integer lift whose
determinant is invertible modulo `dbar d`; the preceding theorems show that the resulting summands
are independent of the chosen lift away from zero. -/
theorem IsGhostOverlapQuasiperiodic.rawTwistedNormalizedGhostSummand_respectsResidues
    {d : ℕ} [NeZero d] {v : IntPhaseSpace → ℂ} (hv : IsGhostOverlapQuasiperiodic d v)
    (G : Mat(2, ℤ)) (hG : IsCoprime G.det (dbar d : ℤ)) :
    RespectsPhaseSpaceResiduesAwayFromZero d
      (rawTwistedNormalizedGhostSummand (d := d) G v) := by
  intro p p' hpp' hp
  have hGpp' := intPhaseSpaceMod_matrix_mulVec_eq G hpp'
  have hGp := intPhaseSpaceMod_matrix_mulVec_ne_zero G hG hp
  simp only [rawTwistedNormalizedGhostSummand]
  change v (Matrix.mulVec G p') • integerDisplacement d p' =
    v (Matrix.mulVec G p) • integerDisplacement d p
  rw [hv (Matrix.mulVec G p) (Matrix.mulVec G p') hGpp' hGp]
  rw [intSymplecticForm_matrix_mulVec]
  rw [integerDisplacement_change_representative hpp', smul_smul]
  have hphase : (displacementPhase d) ^
      ((G.det - 1) * intSymplecticForm p' p) = 1 := by
    obtain ⟨k, hk⟩ := dbar_dvd_det_sub_one_mul_symplectic hpp' G.det hG
    rw [hk, _root_.zpow_mul, zpow_natCast, displacementPhase_pow_dbar, one_zpow]
  congr 1
  calc
    ((displacementPhase d) ^ (G.det * intSymplecticForm p' p) *
        v (Matrix.mulVec G p)) *
        (displacementPhase d) ^ (-intSymplecticForm p' p) =
        ((displacementPhase d) ^ (G.det * intSymplecticForm p' p) *
          (displacementPhase d) ^ (-intSymplecticForm p' p)) *
          v (Matrix.mulVec G p) := by ring
    _ = (displacementPhase d) ^ ((G.det - 1) * intSymplecticForm p' p) *
          v (Matrix.mulVec G p) := by
      rw [← zpow_add₀ (by simp [displacementPhase])]
      congr 2
      ring
    _ = v (Matrix.mulVec G p) := by rw [hphase, one_mul]

/-- Pointwise form of representative independence for a quasiperiodic normalized ghost
summand. -/
theorem IsGhostOverlapQuasiperiodic.rawTwistedNormalizedGhostSummand_eq
    {d : ℕ} [NeZero d] {v : IntPhaseSpace → ℂ} (hv : IsGhostOverlapQuasiperiodic d v)
    (G : Mat(2, ℤ)) (hG : IsCoprime G.det (dbar d : ℤ))
    {p p' : IntPhaseSpace} (hpp' : intPhaseSpaceMod d p' = intPhaseSpaceMod d p)
    (hp : intPhaseSpaceMod d p ≠ 0) :
    rawTwistedNormalizedGhostSummand (d := d) G v p' =
      rawTwistedNormalizedGhostSummand (d := d) G v p :=
  hv.rawTwistedNormalizedGhostSummand_respectsResidues G hG p p' hpp' hp

/-! ### Unnormalized overlaps and summands

The source normalization scales every nonzero overlap by one common real factor.
This preserves the representative and lift independence already proved above. -/

/-- The raw integer-indexed unnormalized ghost overlap obtained from a normalized overlap
function, with the value at zero totalized as the rank `r`.

This is the generic scaling formula from [AFK25, Definition 1.11, `dfn:ghostFiducial`], not the
explicit SF candidate. -/
noncomputable def rawGhostOverlap (d r : ℕ) (v : IntPhaseSpace → ℂ)
    (p : IntPhaseSpace) : ℂ :=
  if intPhaseSpaceMod d p = 0 then r
  else Real.sqrt ((r * (d - r) : ℝ) / (d ^ 2 - 1)) * v p

/-- The unnormalized integer-indexed ghost summand associated with a raw normalized overlap
function and an integer twist lift. -/
noncomputable def rawTwistedGhostSummand {d : ℕ} [NeZero d] (r : ℕ)
    (G : Mat(2, ℤ)) (v : IntPhaseSpace → ℂ) (p : IntPhaseSpace) :
    Mat(d, ℂ) :=
  rawGhostOverlap d r v (Matrix.mulVec G p) • integerDisplacement d p

/-- The unnormalized raw overlap obtained from a quasiperiodic function is independent of the
integer lift of its quotient ghost twist away from zero modulo `d`. -/
theorem IsGhostOverlapQuasiperiodic.rawGhostOverlap_matrix_mulVec_eq_of_isLift
    {d : ℕ} [NeZero d] {v : IntPhaseSpace → ℂ}
    (hv : IsGhostOverlapQuasiperiodic d v) (r : ℕ)
    {G H : Mat(2, ℤ)} {g : GhostTwist d}
    (hG : IsGhostTwistLift G g) (hH : IsGhostTwistLift H g)
    {p : IntPhaseSpace} (hp : intPhaseSpaceMod d p ≠ 0) :
    rawGhostOverlap d r v (Matrix.mulVec G p) =
      rawGhostOverlap d r v (Matrix.mulVec H p) := by
  have hGne := intPhaseSpaceMod_matrix_mulVec_ne_zero G hG.det_isCoprime hp
  have hHne := intPhaseSpaceMod_matrix_mulVec_ne_zero H hH.det_isCoprime hp
  unfold rawGhostOverlap
  rw [ite_eq_right hGne, ite_eq_right hHne,
    hv.eq_matrix_mulVec_of_isLift hG hH hp]

/-- The unnormalized raw twisted summand of a quasiperiodic overlap is independent of the integer
lift of its quotient ghost twist away from zero modulo `d`. -/
theorem IsGhostOverlapQuasiperiodic.rawTwistedGhostSummand_eq_of_isLift
    {d : ℕ} [NeZero d] {v : IntPhaseSpace → ℂ}
    (hv : IsGhostOverlapQuasiperiodic d v) (r : ℕ)
    {G H : Mat(2, ℤ)} {g : GhostTwist d}
    (hG : IsGhostTwistLift G g) (hH : IsGhostTwistLift H g)
    {p : IntPhaseSpace} (hp : intPhaseSpaceMod d p ≠ 0) :
    rawTwistedGhostSummand (d := d) r G v p =
      rawTwistedGhostSummand (d := d) r H v p := by
  simp only [rawTwistedGhostSummand]
  rw [hv.rawGhostOverlap_matrix_mulVec_eq_of_isLift r hG hH hp]

/-- The unnormalized companion of
`IsGhostOverlapQuasiperiodic.rawTwistedNormalizedGhostSummand_respectsResidues`. The zero branch is
irrelevant because the summand is compared only on nonzero residue classes modulo `d`. -/
theorem IsGhostOverlapQuasiperiodic.rawTwistedGhostSummand_respectsResidues
    {d : ℕ} [NeZero d] {v : IntPhaseSpace → ℂ} (hv : IsGhostOverlapQuasiperiodic d v)
    (r : ℕ) (G : Mat(2, ℤ)) (hG : IsCoprime G.det (dbar d : ℤ)) :
    RespectsPhaseSpaceResiduesAwayFromZero d
      (rawTwistedGhostSummand (d := d) r G v) := by
  intro p p' hpp' hp
  have hp' : intPhaseSpaceMod d p' ≠ 0 := by rwa [hpp']
  have hGp := intPhaseSpaceMod_matrix_mulVec_ne_zero G hG hp
  have hGp' := intPhaseSpaceMod_matrix_mulVec_ne_zero G hG hp'
  have hnorm := hv.rawTwistedNormalizedGhostSummand_respectsResidues G hG
    p p' hpp' hp
  simp only [rawTwistedNormalizedGhostSummand] at hnorm
  unfold rawTwistedGhostSummand rawGhostOverlap
  rw [ite_eq_right hGp', ite_eq_right hGp]
  simpa only [mul_smul] using congrArg
    (fun M : Mat(d, ℂ) ↦
      (Real.sqrt ((r * (d - r) : ℝ) / (d ^ 2 - 1)) : ℂ) • M) hnorm

/-! ### Independence of the transversal sums

The pointwise independence gives [AFK25, Lemma 1.42,
`lem:GhostFiducialIndependenceOfTransversal`] by reindexing the nonzero residue classes. -/

/-- The unnormalized twisted sum over nonzero residue classes is independent of the complete
integer transversal. This is the sum-level consequence of
`IsGhostOverlapQuasiperiodic.rawTwistedGhostSummand_respectsResidues`. -/
theorem IsGhostOverlapQuasiperiodic.sum_rawTwistedGhostSummand_eq
    {d : ℕ} [NeZero d] {v : IntPhaseSpace → ℂ} (hv : IsGhostOverlapQuasiperiodic d v)
    (r : ℕ) (G : Mat(2, ℤ)) (hG : IsCoprime G.det (dbar d : ℤ))
    (I J : PhaseSpaceTransversal d) :
    (∑ q : PhaseSpaceMod d, if q = 0 then 0 else
      rawTwistedGhostSummand (d := d) r G v (I.repr q)) =
      ∑ q : PhaseSpaceMod d, if q = 0 then 0 else
        rawTwistedGhostSummand (d := d) r G v (J.repr q) :=
  sum_transversal_eq_of_respectsResidues _
    (hv.rawTwistedGhostSummand_respectsResidues r G hG) I J

/-- For a quasiperiodic raw overlap, the unnormalized nonzero sum is independent of the integer
lift used to represent a fixed quotient ghost twist. -/
theorem IsGhostOverlapQuasiperiodic.sum_rawTwistedGhostSummand_eq_of_isLift
    {d : ℕ} [NeZero d] {v : IntPhaseSpace → ℂ}
    (hv : IsGhostOverlapQuasiperiodic d v) (r : ℕ)
    {G H : Mat(2, ℤ)} {g : GhostTwist d}
    (hG : IsGhostTwistLift G g) (hH : IsGhostTwistLift H g)
    (I : PhaseSpaceTransversal d) :
    (∑ q : PhaseSpaceMod d, if q = 0 then 0 else
      rawTwistedGhostSummand (d := d) r G v (I.repr q)) =
      ∑ q : PhaseSpaceMod d, if q = 0 then 0 else
        rawTwistedGhostSummand (d := d) r H v (I.repr q) := by
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : q = 0
  · simp [hq]
  · rw [ite_eq_right hq, ite_eq_right hq]
    apply hv.rawTwistedGhostSummand_eq_of_isLift r hG hH
    rwa [I.residue_repr]

end SIC

end
