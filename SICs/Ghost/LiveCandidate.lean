/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Ghost.Datum
import SICs.Ghost.Live
import SICs.Ghost.PhaseGalois

/-!
# Live candidates of ghost data

Live fiducials from ghost data and the modulus-one condition on real multiplication values.

This module applies the algebraic conversion theorem of `SICs.Ghost.Live` to the fixed ghost
candidate of `SICs.Ghost.Datum`, following [AFK25, proof of Theorem 1.46,
`thm:rayclassfieldrsicgen`]. One ambient automorphism acts on every coefficient. Unit modulus
of the bare real multiplication values suffices: the normalized overlaps differ from them by
the SF phase, a root of unity whose Galois images also have modulus one. The unconditional input is
`AdmissibleTuple.norm_map_levelGenerator`, applied in `SICs.Construction`.
-/

noncomputable section

open Complex Real
open scoped MatrixGroups

namespace SIC

namespace AdmissibleTuple.GhostDatum

variable {t : AdmissibleTuple}

/-- **The live candidate of a ghost datum is an `r`-SIC fiducial**: if one ambient automorphism
`g` sends every nonzero normalized overlap of the datum to modulus one, then `Π_s = g(Π̃_s)` is an
`r`-SIC fiducial. This is the local form of [AFK25, Theorem 1.46, `thm:rayclassfieldrsicgen`], with
the Minimalist RMVC replaced by its one consequence the proof uses
(`IsGhostFiducialWith.mapMatrix_isFiducial`). -/
theorem mapMatrix_candidate_isFiducial (s : t.GhostDatum) (g : ComplexGaloisAutomorphism)
    (hg : LiveConversionCondition s.fiducialData g) :
    IsFiducial t.r (g.mapMatrix s.candidate) := by
  exact s.isGhostFiducialWith.mapMatrix_isFiducial g hg t.pair.rank_pos t.pair.rank_lt_d

/-- **The live conversion condition from the real multiplication values**: if an ambient
automorphism `g` sends `ש^{p/d}_{A_t}(ρ_t)` to modulus one for every `p ≢ 0 (mod d)`, then it
sends every nonzero normalized overlap of the ghost datum to modulus one. The overlap is
`ν̃_t(Gp) = Φ_t(Gp) ש^{Gp/d}_{A_t}(ρ_t)` with `Gp ≢ 0` (`fiducialData_normalizedCoefficient`,
`candidateNormGhostOverlap_eq_sfPhase_mul`), and `g` sends the root-of-unity
phase `Φ_t` to modulus one (`AdmissibleTuple.norm_map_sfPhase`). This is the step of
[AFK25, proof of Theorem 1.46, `thm:rayclassfieldrsicgen`] that follows the appeal to the
Minimalist RMVC. -/
theorem liveConversionCondition_of_norm_map (s : t.GhostDatum) (g : ComplexGaloisAutomorphism)
    (hg : ∀ p : IntPhaseSpace, intPhaseSpaceMod t.d p ≠ 0 →
      ‖g (sfModularCocycleRealTotal (shiftRationalPoint t.d p) t.levelGenerator
        (t.isAssociatedStabilizerPair_levelGenerator.A_mem_gammaSubgroup
          (exists_intCast_mul_shiftRationalPoint t.d p)) t.Q.rootPlus)‖ = 1) :
    LiveConversionCondition s.fiducialData g := by
  intro p hp
  have hG := s.twist.integerLift_isLift
  rw [s.fiducialData_normalizedCoefficient hG hp,
    candidateNormGhostOverlap_eq_sfPhase_mul
      t.isAssociatedStabilizerPair_levelGenerator,
    map_mul, norm_mul, t.norm_map_sfPhase, one_mul]
  exact hg _ (intPhaseSpaceMod_matrix_mulVec_ne_zero _ hG.det_isCoprime hp)

end AdmissibleTuple.GhostDatum

end SIC

end
