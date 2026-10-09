/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Admissible.PairTriple
import SICs.Dilogarithm.TwistedConvolution
import SICs.Dilogarithm.TupleUnitaryConjugates
import SICs.FieldTheory.ComplexAutomorphisms
import SICs.Ghost.LiveCandidate

/-!
# General existence of live `r`-SIC fiducials

Every admissible pair has a live Weyl--Heisenberg `r`-SIC fiducial.

This module combines the ghost construction of [AFK26, Appleby, Flammia, Kopp (2026),
Theorem 1.3, `thm:ghost`], the unitary conjugates of [RW26b, Radchenko, Wheeler (2026b),
Proposition 7], and the ghost-to-live conversion in [AFK25, proof of Theorem 1.46,
`thm:rayclassfieldrsicgen`]. The latter theorem is conditional as printed; the conditions needed
here are supplied by the cited unconditional results.

## The argument

For an admissible tuple with positive leading coefficient, choose an associated stabilizer pair.
The shift `-d_j` from the twisted convolution identity gives one ghost datum `s`. Choose one
automorphism switching the two square roots of the discriminant. Proposition 7 sends every
nonzero level-generator cocycle value to modulus one under this automorphism, so all normalized
overlaps of this same datum satisfy the live conversion condition. Its mapped candidate is
therefore a fiducial, so its Weyl--Heisenberg orbit is an `r`-SIC. Every admissible pair has such
a tuple.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### Live fiducials

The tuple construction uses one ghost datum for both the shift and the live overlap condition.
The pair result then forgets the tuple. -/

/-- A live `r`-SIC fiducial of an admissible tuple with positive leading coefficient. The ghost
datum comes from [AFK26, Appleby, Flammia, Kopp (2026), Theorems 1.2--1.3,
`thm:tci`, `thm:ghost`]; [RW26b, Radchenko, Wheeler (2026b), Proposition 7] supplies the
unit-modulus values used in [AFK25, proof of Theorem 1.46, `thm:rayclassfieldrsicgen`]. -/
theorem AdmissibleTuple.exists_liveFiducial (t : AdmissibleTuple) (ha : 0 < t.Q.a) :
    ∃ P : Mat(t.d, ℂ), IsFiducial t.r P := by
  obtain ⟨A_t, Lz, hp⟩ := t.exists_isAssociatedStabilizerPair
  let s : t.GhostDatum := .ofIsShift hp (t.isShift_neg_towerDimension hp ha)
  obtain ⟨g, hg⟩ := exists_switchesSqrt t.triple.tower.discr_pos
    (not_isSquare_numberField_discr t.triple.tower.finrank_eq_two)
  exact ⟨g.mapMatrix s.candidate, s.mapMatrix_candidate_isFiducial g
    (s.liveConversionCondition_of_norm_map g fun _ hp ↦
      t.norm_map_levelGenerator ha g hg hp)⟩

/-- Every admissible pair `(d, r)` has a live `r`-SIC fiducial. This combines the admissible
tuple of [AFK26, Appleby, Flammia, Kopp (2026), Theorem 1.3, `thm:ghost`] with
`AdmissibleTuple.exists_liveFiducial`. -/
theorem AdmissiblePair.exists_liveFiducial (p : AdmissiblePair) :
    ∃ P : Mat(p.d, ℂ), IsFiducial p.r P := by
  obtain ⟨t, rfl, ha⟩ := p.exists_admissibleTuple
  exact t.exists_liveFiducial ha

end SIC

end
