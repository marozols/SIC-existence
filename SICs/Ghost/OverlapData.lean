/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Quantum.IntegerDisplacement

/-!
# Abstract ghost overlaps and quotient twists

Real overlap data, quotient twists and integer lifts, quasiperiodicity and quotient descent.

This file records the overlap and twist data in [AFK25, Definition 1.11,
`dfn:ghostFiducial`] and the quasiperiodicity of [AFK25, Lemma 5.7,
`lem:nupperiodicity`]. Twists live over `ZMod (dbar d)` and admit canonical integer
lifts. Real quotient-indexed overlaps satisfy the reciprocal identity.

The raw integer-indexed quasiperiodicity predicate retains the exceptional zero class.
Away from that class, congruence modulo `dbar d` forces the displacement phase to be one,
so quasiperiodic overlaps descend to the quotient. The matrix and projector constructions
are in `SICs.Ghost.TwistedSummands` and `SICs.Ghost.Fiducials`.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### Ghost twists and their integer lifts

A ghost twist lives over `ZMod (dbar d)`, but matrix-vector formulas use integral lifts.  This
section constructs a canonical lift and proves that all lifts act identically after reduction. -/

/-- A twist for a ghost fiducial is an element of
`GL₂(ℤ / dbar d ℤ)`, exactly as in [AFK25, Definition 1.11, `dfn:ghostFiducial`]. -/
abbrev GhostTwist (d : ℕ) := GL (Fin 2) (ZMod (dbar d))

/-- An integer matrix lifts a quotient-valued ghost twist when reducing every entry modulo
`dbar d` recovers the twist matrix. -/
def IsGhostTwistLift {d : ℕ} (G : Mat(2, ℤ))
    (g : GhostTwist d) : Prop :=
  G.map (Int.castRingHom (ZMod (dbar d))) =
    (g : Mat(2, ZMod (dbar d)))

/-- The canonical entrywise integer lift of a quotient-valued ghost twist, using balanced
integer representatives. -/
def GhostTwist.integerLift {d : ℕ} (g : GhostTwist d) :
    Mat(2, ℤ) :=
  fun i j ↦ (g i j).valMinAbs

/-- The canonical integer matrix associated to a ghost twist is a lift of that twist. -/
theorem GhostTwist.integerLift_isLift {d : ℕ} (g : GhostTwist d) :
    IsGhostTwistLift g.integerLift g := by
  ext i j
  simp [GhostTwist.integerLift, Matrix.map_apply]

/-- The determinant of every integer lift of a ghost twist is coprime to `dbar d`. -/
theorem IsGhostTwistLift.det_isCoprime {d : ℕ} {G : Mat(2, ℤ)}
    {g : GhostTwist d} (hG : IsGhostTwistLift G g) :
    IsCoprime G.det (dbar d : ℤ) := by
  have hgdet : IsUnit
      ((g : Mat(2, ZMod (dbar d))).det) :=
    ((g : Mat(2, ZMod (dbar d))).isUnit_iff_isUnit_det).mp g.isUnit
  have hdet : IsUnit (G.det : ZMod (dbar d)) := by
    change IsUnit ((Int.castRingHom (ZMod (dbar d))) G.det)
    rw [(Int.castRingHom (ZMod (dbar d))).map_det]
    change IsUnit (G.map (Int.castRingHom (ZMod (dbar d)))).det
    rwa [hG]
  exact ((ZMod.coe_int_isUnit_iff_isCoprime G.det (dbar d)).mp hdet).symm

/-! ### Abstract overlap data and quasi-periodicity

The abstract data bundle retains the realness and reciprocal law of normalized ghost overlaps.
The separate integer quasi-periodicity predicate is precisely the input that makes displacement
summands independent of representatives. -/

/-- Real normalized ghost-overlap data from [AFK25, Definition 1.11, `dfn:ghostFiducial`].

Indexing by `PhaseSpaceMod (dbar d)` builds the paper's `dbar d`-periodicity into the type.
The value at zero is a harmless totalization: the normalized overlap is used only away from zero,
and the unnormalized overlap is defined separately there.

The reciprocal hypothesis below is stated for `p ≢ 0 (mod d)`, whereas the source definition as
printed says `p ≠ 0 (mod d̄)`. The printed side condition appears to be a typo: the proof of
[AFK25, Theorem 5.8, `thm:nupnumpeq1`] establishes exactly the mod-`d` condition, as does the
reference implementation [42, Flammia (2024)]. The distinction is real only for even `d` — the
mod-`d̄` reading would additionally constrain classes like `p = (d, 0) mod 2d`, where the
elementary argument genuinely breaks down — but no such class enters the expansion, since the sum
runs over representatives of `ℤ²/dℤ²` with `0` removed.

The typo is confined to that side condition: the overlaps themselves stay indexed modulo `dbar d`,
since they are not `d`-periodic in even dimensions, and twists stay in `GL₂(ℤ/d̄ℤ)`. -/
structure GhostOverlapData (d : ℕ) where
  /-- The real normalized ghost overlap `ν̃_p`. -/
  normalized : PhaseSpaceMod (dbar d) → ℝ
  /-- The reciprocal relation `ν̃_p ν̃_{-p} = 1`, for every integer lift `p` with `p ≢ 0 (mod d)`.
  This is well-defined on residues modulo `dbar d`: both `normalized (intPhaseSpaceMod (dbar d) p)`
  and the side condition `intPhaseSpaceMod d p ≠ 0` depend on `p` only through its class modulo
  `dbar d`, since `d ∣ dbar d` (`dvd_dbar`). -/
  reciprocal : ∀ p : IntPhaseSpace, intPhaseSpaceMod d p ≠ 0 →
    normalized (intPhaseSpaceMod (dbar d) p) * normalized (intPhaseSpaceMod (dbar d) (-p)) = 1

/-- Pull quotient-indexed normalized ghost overlaps back to an integer-indexed complex function.

This pullback is the raw function to which the quasi-periodicity law
`IsGhostOverlapQuasiperiodic` applies. -/
def GhostOverlapData.integerPullback {d : ℕ} (v : GhostOverlapData d) :
    IntPhaseSpace → ℂ :=
  fun p ↦ v.normalized (intPhaseSpaceMod (dbar d) p)

/-- The data occurring in the expansion of one abstract ghost fiducial: its real normalized
overlaps and its twist. -/
structure GhostFiducialData (d : ℕ) where
  /-- Real normalized ghost-overlap data. -/
  overlaps : GhostOverlapData d
  /-- The twist acting on overlap indices. -/
  twist : GhostTwist d

/-- Apply a ghost datum's twist to an integer phase-space point, reducing the result modulo
`dbar d`. -/
def GhostFiducialData.twistedIndex {d : ℕ} (s : GhostFiducialData d)
    (p : IntPhaseSpace) : PhaseSpaceMod (dbar d) :=
  Matrix.mulVec (s.twist : Mat(2, ZMod (dbar d)))
    (intPhaseSpaceMod (dbar d) p)

/-! ### Integer quasiperiodicity and quotient descent

The condition in [AFK25, Lemma 5.7, `lem:nupperiodicity`] is stated before quotient
descent, so it also applies to raw analytic candidates. -/

/-- The quasi-periodicity proved for the exact candidate normalized ghost overlaps in
[AFK25, Lemma 5.7, `lem:nupperiodicity`]. This predicate deliberately takes a raw integer-indexed
complex function: descent to the real quotient-indexed `GhostOverlapData` is a later theorem, not
a requirement of this predicate. -/
def IsGhostOverlapQuasiperiodic (d : ℕ) [NeZero d] (v : IntPhaseSpace → ℂ) : Prop :=
  ∀ p p', intPhaseSpaceMod d p' = intPhaseSpaceMod d p →
    intPhaseSpaceMod d p ≠ 0 →
      v p' = (displacementPhase d) ^ intSymplecticForm p' p * v p

/-- An integer lift and its quotient ghost twist have the same action after reduction modulo
`dbar d`. -/
theorem IsGhostTwistLift.intPhaseSpaceMod_mulVec {d : ℕ}
    {G : Mat(2, ℤ)} {g : GhostTwist d} (hG : IsGhostTwistLift G g)
    (p : IntPhaseSpace) :
    intPhaseSpaceMod (dbar d) (Matrix.mulVec G p) =
      Matrix.mulVec (g : Mat(2, ZMod (dbar d)))
        (intPhaseSpaceMod (dbar d) p) := by
  rw [intPhaseSpaceMod_matrix_mulVec, hG]

/-- An integer lift of a ghost datum's twist computes the datum's quotient-valued twisted
index. -/
theorem IsGhostTwistLift.intPhaseSpaceMod_mulVec_eq_twistedIndex {d : ℕ}
    (s : GhostFiducialData d) {G : Mat(2, ℤ)}
    (hG : IsGhostTwistLift G s.twist) (p : IntPhaseSpace) :
    intPhaseSpaceMod (dbar d) (Matrix.mulVec G p) = s.twistedIndex p := by
  rw [GhostFiducialData.twistedIndex, hG.intPhaseSpaceMod_mulVec]

/-- Two integer lifts of the same quotient ghost twist act identically after reduction modulo
`dbar d`. -/
theorem IsGhostTwistLift.intPhaseSpaceMod_mulVec_eq_of_lifts {d : ℕ}
    {G H : Mat(2, ℤ)} {g : GhostTwist d}
    (hG : IsGhostTwistLift G g) (hH : IsGhostTwistLift H g)
    (p : IntPhaseSpace) :
    intPhaseSpaceMod (dbar d) (Matrix.mulVec G p) =
      intPhaseSpaceMod (dbar d) (Matrix.mulVec H p) :=
  (hG.intPhaseSpaceMod_mulVec p).trans (hH.intPhaseSpaceMod_mulVec p).symm

/-! Congruence modulo `dbar d` implies congruence modulo `d`, while the symplectic exponent in the
quasiperiodicity law is itself a multiple of `dbar d`. Its displacement phase is therefore one.
This is the generic descent used after [AFK25, Lemma 5.7, `lem:nupperiodicity`]. The nonzero
hypothesis retains the integral-index exception described in [72, Kopp (2024), Proposition 4.35,
`prop:invariance`]. -/

/-- A quasiperiodic normalized overlap is genuinely periodic modulo `dbar d`, away from the zero
residue class modulo `d`. This is the quotient-descent consequence of
`IsGhostOverlapQuasiperiodic`. -/
theorem IsGhostOverlapQuasiperiodic.eq_of_dbar_eq
    {d : ℕ} [NeZero d] {v : IntPhaseSpace → ℂ}
    (hv : IsGhostOverlapQuasiperiodic d v) {p p' : IntPhaseSpace}
    (hmod : intPhaseSpaceMod (dbar d) p' = intPhaseSpaceMod (dbar d) p)
    (hp : intPhaseSpaceMod d p ≠ 0) :
    v p' = v p := by
  rw [hv p p' (intPhaseSpaceMod_eq_of_dbar_eq hmod) hp]
  have hdvd : (dbar d : ℤ) ∣ intSymplecticForm p' p :=
    dvd_intSymplecticForm_of_mod_eq hmod
  rw [displacementPhase_zpow_eq_one_of_dbar_dvd hdvd, one_mul]

end SIC

end
