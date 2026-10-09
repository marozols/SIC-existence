/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Ghost.Phase
import SICs.Admissible.StabilizerDomain
import SICs.Cocycle.Modular.Shifts
import SICs.Ghost.Shifts

/-!
# Candidate ghost overlaps

Candidate normalized ghost overlaps and Lemma 5.7 in both stabilizer orientations.

This module follows [AFK25, Definition 1.32, `dfn:GhostOverlaps`] and
[AFK25, Lemma 5.7, `lem:nupperiodicity`]. Multiplying the phase of `SICs.Ghost.Phase` by the
real-line Shintani--Faddeev value gives the normalized overlap. The unnormalized overlap, the rank
on the zero residue class and otherwise the source's square-root scale times the normalized one, is
formed from it by the generic `rawGhostOverlap` of `SICs.Ghost.TwistedSummands`.

At an associated stabilizer, `IsAssociatedStabilizerPair.A_mem_gammaSubgroup` removes the
matrix totalization branch. `SICs.Admissible.StabilizerDomain` proves membership of both roots
in the domains of the stabilizer and its inverse, as in [AFK25, Theorem 1.31,
`thm:ghostWellDefinedCondition`]. The real-line word value remains total; comparison with the
meromorphically continued cocycle is a separate analytic obligation.

Index periodicity is proved at the stabilizer when its lower-left entry is positive and at its
inverse when it is negative. Combining it with phase transport gives the symplectic factor of
Lemma 5.7. Reciprocity is in `SICs.Ghost.OverlapReciprocity`, realness in
`SICs.Ghost.RealOverlaps`, and the origin value in `SICs.Ghost.Origin`.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

namespace AdmissibleTuple

/-! #### Transport of the cocycle under a change of representative

The sign-free theorem in `SICs.Cocycle.Modular.Shifts` selects the word at `A_t` or `A_t⁻¹`,
according
to the orientation of the associated stabilizer. Specializing its hypotheses to the rational
characteristics `p/d` and `p'/d` supplies the cocycle input to [AFK25, Lemma 5.7,
`lem:nupperiodicity`]. -/

/-- At an associated stabilizer, congruent nonzero phase-space representatives give equal total
Shintani--Faddeev values at `ρ_t`. This specializes
`sfModularCocycleRealTotal_congr_of_sub_intVec` for use in
`IsAssociatedStabilizerPair.candidateNormGhostOverlap_quasiperiodic`. -/
theorem IsAssociatedStabilizerPair.sfModularCocycleRealTotal_shiftRationalPoint_congr
    {t : AdmissibleTuple} {A_t Lz : SL(2, ℤ)}
    (h : t.IsAssociatedStabilizerPair A_t Lz) (p p' : IntPhaseSpace)
    (hmod : intPhaseSpaceMod t.d p' = intPhaseSpaceMod t.d p)
    (hp : intPhaseSpaceMod t.d p ≠ 0) :
    sfModularCocycleRealTotal (shiftRationalPoint t.d p') A_t
        (h.A_mem_gammaSubgroup (exists_intCast_mul_shiftRationalPoint t.d p')) t.Q.rootPlus =
      sfModularCocycleRealTotal (shiftRationalPoint t.d p) A_t
        (h.A_mem_gammaSubgroup (exists_intCast_mul_shiftRationalPoint t.d p)) t.Q.rootPlus := by
  have hd : 0 < t.d := by
    rw [t.d_eq_dimension]
    exact t.triple.dimension_pos
  exact sfModularCocycleRealTotal_congr_of_sub_intVec
    (shiftRationalPoint t.d p) (shiftRationalPoint t.d p') A_t
    (h.A_mem_gammaSubgroup (exists_intCast_mul_shiftRationalPoint t.d p))
    (h.A_mem_gammaSubgroup (exists_intCast_mul_shiftRationalPoint t.d p'))
    t.form_admissible.rootPlus_irrational
    (not_isIntegralIndex_shiftRationalPoint t.d hd hp)
    h.ofReal_rootPlus_mem_sfDomain h.ofReal_rootPlus_mem_sfDomain_inv
    h.flt_A_rootPlus h.lowerLeft_A_ne_zero
    (exists_intCast_shiftRationalPoint_sub_of_mod_eq t.d hd hmod)

/-- **The candidate normalized ghost overlaps** `ν̃_t(p) = Φ_t(p) · ש^{p/d}_{A_t}(ρ_t)`
of [AFK25, Definition 1.32, `dfn:GhostOverlaps`, equation (1.46), `eq:ghostoverlapformula`], at the
tuple's own real quadratic point `ρ_t = ρ_{Q,+}`. -/
@[source "AFK25, Definition 1.32, p. 17, dfn:GhostOverlaps (normalized)" (symbol := "ν̃_t(p)")]
noncomputable def candidateNormGhostOverlap (t : AdmissibleTuple) (A : SL(2, ℤ))
    (p : IntPhaseSpace) : ℂ :=
  t.sfPhase A p * sfModularCocycleReal' (shiftRationalPoint t.d p) A t.Q.rootPlus

/-- **At an associated stabilizer pair the cocycle factor takes no junk branch**, so the
normalized overlap is the source's: `ν̃_t(p) = Φ_t(p) · ש^{p/d}_{A_t}(ρ_t)` with `ש` the exact
value of `sfModularCocycleRealTotal`. -/
lemma candidateNormGhostOverlap_eq_sfPhase_mul {t : AdmissibleTuple}
    {A_t Lz : SL(2, ℤ)} (hp : t.IsAssociatedStabilizerPair A_t Lz) (p : IntPhaseSpace) :
    t.candidateNormGhostOverlap A_t p =
      t.sfPhase A_t p *
        sfModularCocycleRealTotal (shiftRationalPoint t.d p) A_t
          (hp.A_mem_gammaSubgroup (exists_intCast_mul_shiftRationalPoint t.d p)) t.Q.rootPlus := by
  rw [candidateNormGhostOverlap, hp.sfModularCocycleReal'_A]

/-! #### Quasi-periodicity

Combining the phase and cocycle transport laws proves [AFK25, Lemma 5.7, `lem:nupperiodicity`].
Congruence modulo `dbar d` then kills the residual symplectic phase, giving genuine periodicity away
from integral characteristics. Those excluded characteristics have the exceptional law of [72, Kopp
(2024), Proposition 4.35, `prop:invariance`]. Realness enters later when the quotient-indexed
coefficients are packaged as `GhostOverlapData`. -/

/-- **[AFK25, Lemma 5.7, `lem:nupperiodicity`] for the general candidate normalized overlap.**
For every associated stabilizer pair,
`ν̃_t(p') = ξ_d^⟨p',p⟩ ν̃_t(p)` whenever `p' ≡ p (mod d)` and `p ≢ 0 (mod d)`. -/
@[source "AFK25, Lemma 5.7, p. 79, lem:nupperiodicity"]
theorem IsAssociatedStabilizerPair.candidateNormGhostOverlap_quasiperiodic
    {t : AdmissibleTuple} {A_t Lz : SL(2, ℤ)}
    (h : t.IsAssociatedStabilizerPair A_t Lz) :
    IsGhostOverlapQuasiperiodic t.d (t.candidateNormGhostOverlap A_t) := by
  intro p p' hmod hp
  rw [candidateNormGhostOverlap_eq_sfPhase_mul h p',
    candidateNormGhostOverlap_eq_sfPhase_mul h p,
    t.sfPhase_transport A_t p p' hmod,
    h.sfModularCocycleRealTotal_shiftRationalPoint_congr p p' hmod hp]
  ring

/-- The general candidate normalized overlap is periodic modulo `dbar d` away from the zero
residue class modulo `d`, by
`IsAssociatedStabilizerPair.candidateNormGhostOverlap_quasiperiodic`. -/
theorem IsAssociatedStabilizerPair.candidateNormGhostOverlap_dbar_periodic
    {t : AdmissibleTuple} {A_t Lz : SL(2, ℤ)}
    (h : t.IsAssociatedStabilizerPair A_t Lz) {p p' : IntPhaseSpace}
    (hmod : intPhaseSpaceMod (dbar t.d) p' = intPhaseSpaceMod (dbar t.d) p)
    (hp : intPhaseSpaceMod t.d p ≠ 0) :
    t.candidateNormGhostOverlap A_t p' = t.candidateNormGhostOverlap A_t p :=
  h.candidateNormGhostOverlap_quasiperiodic.eq_of_dbar_eq hmod hp

end AdmissibleTuple

end SIC

end
