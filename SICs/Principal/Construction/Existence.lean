/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.FieldTheory.ComplexAutomorphisms
import SICs.Principal.Construction.GhostProjector
import SICs.Principal.Construction.Live
import SICs.Principal.Dilogarithm.TwistedConvolution
import SICs.Principal.Dilogarithm.UnitaryConjugates
import SICs.Quantum.LowDimensions

/-!
# Principal-Family Rank-One Existence

Weyl--Heisenberg rank-one fiducials in every positive dimension, from the principal family.

This file combines the exact principal real shift, the principal ghost-projector
calculation, and the exact unit-modulus input used by the live construction. It then adjoins the
explicit low-dimensional fiducials.

The shift hypothesis is discharged by `principalRealShiftTCC` of
`SICs.Principal.Dilogarithm.TwistedConvolution`, following
[RW26, Radchenko, Wheeler (2026), Theorem 7, `thm:ghostsic`]. Thus
`principalGhostCandidate_idempotent` proves the required ghost idempotency directly.

The live input is supplied by `principalLiveUnitModulus_holds`: an
automorphism of `ℂ` switching `√Δ_K`, where `Δ_K = disc(K)`, sends every nonzero principal overlap
to the unit circle by
[RW26b, Radchenko, Wheeler (2026b), Proposition 7] (`SICs.Principal.Dilogarithm.UnitaryConjugates`).
The live construction combines these two theorems, and the explicit fiducials in dimensions one
through three complete `exists_rankOneFiducial` in every positive dimension.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### Unconditional principal inputs

The theorem `principalRealShiftTCC` makes the principal ghost candidate idempotent in every
dimension `d > 3`. The switching automorphism proves the exact unit-modulus condition
consumed by the live construction. -/

/-- **The principal ghost candidate is idempotent in every dimension `d > 3`**:
`principalGhostCandidate_idempotent_of_realShift` at the shift `λ = 1`,
which is a theorem
(`isPrincipalRealShift_one`) by [RW26, Radchenko, Wheeler (2026), Theorem 7, `thm:ghostsic`]. -/
theorem principalGhostCandidate_idempotent (d : RankOneDimension) :
    principalGhostCandidate d ^ 2 = principalGhostCandidate d :=
  principalGhostCandidate_idempotent_of_realShift d (isPrincipalRealShift_one d)

/-- **The principal live unit-modulus input holds**: in every dimension `d > 3`, one automorphism
of `ℂ`, any one switching `√Δ_K` for `Δ_K = disc(K)`, sends every nonzero principal normalized
ghost overlap to the unit circle ([RW26b, Radchenko, Wheeler (2026b), Proposition 7 and the
paragraph after it]). -/
theorem principalLiveUnitModulus_holds : principalLiveUnitModulus := by
  intro d
  obtain ⟨τ, hτ⟩ := exists_switchesSqrt
    (rankOneRealQuadraticFieldData d).discr_pos
    (not_isSquare_numberField_discr (rankOneField_finrank d))
  exact ⟨τ, fun p hp ↦ norm_map_principalNormGhostOverlap d hτ hp⟩

/-! ### Unconditional existence

The live construction turns the idempotent ghost candidate into a Weyl--Heisenberg SIC in every
dimension above three. The explicit low-dimensional fiducials complete the statement in every
positive dimension. -/

/-- **Weyl--Heisenberg-covariant rank-one existence**: in every positive dimension there is a
Weyl--Heisenberg SIC fiducial. This proves the covariant strengthening of
[AFK25, Conjecture 1.3, `conj:zauner`]. For `d > 3` the witness is the principal live candidate of
[AFK25, Theorem 1.46, `thm:rayclassfieldrsicgen`], whose hypotheses are supplied by
[RW26, Radchenko, Wheeler (2026), Theorem 7, `thm:ghostsic`] and
[RW26b, Radchenko, Wheeler (2026b), Proposition 7]; for `d ≤ 3` it is explicit. -/
theorem exists_rankOneFiducial (d : ℕ) (hd : 0 < d) :
    haveI : NeZero d := ⟨by omega⟩
    ∃ P₀ : Mat(d, ℂ), IsFiducial 1 P₀ := by
  let _ : NeZero d := ⟨by omega⟩
  by_cases hlarge : 3 < d
  · exact exists_rankOneFiducialAboveThree
      principalGhostCandidate_idempotent principalLiveUnitModulus_holds d hlarge
  · have hdle : d ≤ 3 := by omega
    interval_cases d
    · exact ⟨fiducialDimOne, fiducialDimOne_isFiducial⟩
    · exact ⟨fiducialDimTwo, fiducialDimTwo_isFiducial⟩
    · exact ⟨fiducialDimThree, fiducialDimThree_isFiducial⟩

end SIC

end
