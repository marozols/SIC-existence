/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Ghost.Live
import SICs.Principal.Ghost.Candidate

/-!
# The Live Candidate of the Principal Family

`principalLiveUnitModulus` and the fiducial of Theorem 1.46.

The ghost-to-live argument is proved in `SICs.Ghost.Live`. This module supplies the
principal-family inputs and specializations:

* `principalLiveUnitModulus` is the exact project-local condition that one ambient Galois
  automorphism, fixed for the whole candidate in each dimension, sends every nonzero principal
  normalized overlap to the unit circle;
* `principalLiveCandidate` is the principal instance of the general entrywise Galois image, and
  `principalLiveCandidate_isFiducial` is a direct corollary of
  `IsGhostFiducialWith.mapMatrix_isFiducial`.

Idempotency of the principal ghost candidate is an explicit hypothesis here.
`principalGhostCandidate_idempotent` in `SICs.Principal.Construction.Existence` proves it from
the principal twisted convolution identity.

## Quantifier order and the RM-values input

[AFK25, Conjecture 1.36, `conj:mrmvc`] is stated one Shintani--Faddeev value at a time and
quantifies universally over sign-switching automorphisms. A live matrix requires one automorphism
acting on all entries simultaneously. Accordingly, `principalLiveUnitModulus` uses
`∃ g, ∀ p`. The printed universal clause supplies this simultaneous witness once a switching
automorphism exists; a separate existential witness for each index would not suffice.

In [AFK25, Theorem 1.46, `thm:rayclassfieldrsicgen`] the modulus-one input comes from clause (2)
of the Minimalist RMVC; the project proves `principalLiveUnitModulus` unconditionally from
[RW26b, Radchenko, Wheeler (2026b), Proposition 7] (`principalLiveUnitModulus_holds` in
`SICs.Principal.Construction.Existence`).

## References

- [AFK25] Appleby, Flammia, Kopp, arXiv:2501.03970v2, Theorem 1.8, Definition 1.32,
  Conjecture 1.36, Definition 1.43, Lemma 1.44 and Theorem 1.46
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### The unit-modulus input and Conjecture 1.36

`principalLiveUnitModulus` asks for exactly what the live construction consumes, without
algebraicity or square-root switching. The definition below records how it differs from clause (2)
of [AFK25, Conjecture 1.36, `conj:mrmvc`]. -/

/-- The exact unit-modulus input consumed by the principal live-candidate construction: in each
dimension, one ambient Galois automorphism sends every nonzero principal normalized ghost overlap
to a value of modulus one. The condition is project-local. Compared with clause (2) of
[AFK25, Conjecture 1.36, `conj:mrmvc`], it is stated only for the principal tuples `t_d`, where
`ρ = ρ_d`, `A = A_d` and `r = p/d`; it concerns the normalized ghost overlaps
`ν̃_p(t_d) = Φ_{t_d}(p) ש^{p/d}_{A_d}(ρ_d)` of [AFK25, Definition 1.32, `dfn:GhostOverlaps`]
rather than the bare cocycle values; it uses automorphisms of `ℂ` rather than `Gal(ℚ̄/ℚ)`; it asks
for one automorphism serving all overlaps of a dimension (the footnote to Conjecture 1.36 notes
that one automorphism satisfying clause (2) would suffice for SIC existence); and it drops the
requirement that the automorphism exchange the square roots of `Δ_d`. The algebraicity of
clause (1) is not assumed.

It is a theorem, `principalLiveUnitModulus_holds`, by [RW26b, Radchenko, Wheeler (2026b),
Proposition 7]. -/
def principalLiveUnitModulus : Prop :=
  ∀ d : RankOneDimension,
    ∃ g : ComplexGaloisAutomorphism,
      ∀ p : IntPhaseSpace, intPhaseSpaceMod d p ≠ 0 →
        ‖g (principalNormGhostOverlap d p)‖ = 1

/-! ### Direct specialization of the General live-conversion theorem

The principal twist is the identity, so the General packaged coefficient is exactly
`principalNormGhostOverlap`. This is the only family-specific identification needed below. -/

/-- For the principal identity-twist data, the General packaged coefficient is the explicit
principal normalized ghost overlap. -/
private lemma principal_normalizedCoefficient (d : RankOneDimension) (p : IntPhaseSpace) :
    (principalGhostFiducialData d).normalizedCoefficient p =
      principalNormGhostOverlap d p := by
  rw [← principalGhostFiducialData_integerPullback d]
  simp [GhostFiducialData.normalizedCoefficient, GhostOverlapData.integerPullback,
    GhostFiducialData.twistedIndex, principalGhostFiducialData]

/-- The principal live candidate `Π_d = g(Π̃_d)` of [AFK25, Definition 1.43,
`dfn:CandidateGhostAndSICFiducials`]. -/
@[source "AFK25, Definition 1.43, p. 20, dfn:CandidateGhostAndSICFiducials (SIC, principal family)"
  (symbol := "Π_d")]
def principalLiveCandidate (d : RankOneDimension) (g : ComplexGaloisAutomorphism) :
    Mat(d, ℂ) :=
  g.mapMatrix (principalGhostCandidate d)

/-- The principal live candidate is a rank-one SIC fiducial. Specializes
`IsGhostFiducialWith.mapMatrix_isFiducial`, the general local form of [AFK25, Theorem 1.46,
`thm:rayclassfieldrsicgen`]. -/
theorem principalLiveCandidate_isFiducial (d : RankOneDimension)
    (g : ComplexGaloisAutomorphism)
    (hidem : principalGhostCandidate d ^ 2 = principalGhostCandidate d)
    (hg : ∀ p : IntPhaseSpace, intPhaseSpaceMod d p ≠ 0 →
      ‖g (principalNormGhostOverlap d p)‖ = 1) :
    IsFiducial 1 (principalLiveCandidate d g) := by
  have hghost := principalGhostCandidate_isGhostFiducialWith d hidem
  have hlive : LiveConversionCondition (principalGhostFiducialData d) g := by
    intro p hp
    rw [principal_normalizedCoefficient d]
    exact hg p hp
  simpa only [principalLiveCandidate] using
    hghost.mapMatrix_isFiducial g hlive one_pos (by omega)

/-! ### Principal existence above dimension three

Applying the live-candidate theorem in each dimension gives rank-one fiducial existence. -/

/-- Idempotency of the principal ghost candidate together with the exact unit-modulus input gives
Weyl--Heisenberg-covariant rank-one fiducial existence in every dimension `d > 3`. -/
theorem exists_rankOneFiducialAboveThree
    (hidem : ∀ d : RankOneDimension,
      principalGhostCandidate d ^ 2 = principalGhostCandidate d)
    (hlive : principalLiveUnitModulus) (d : ℕ) (hd : d > 3) :
    haveI : NeZero d := ⟨by omega⟩
    ∃ P₀ : Mat(d, ℂ), IsFiducial 1 P₀ := by
  let _ : NeZero d := ⟨by omega⟩
  obtain ⟨g, hg⟩ := hlive ⟨d, hd⟩
  exact ⟨principalLiveCandidate ⟨d, hd⟩ g,
    principalLiveCandidate_isFiducial ⟨d, hd⟩ g (hidem ⟨d, hd⟩) hg⟩

end SIC

end
