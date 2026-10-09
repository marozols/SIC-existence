/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Dilogarithm.Reciprocity.UnitaryConjugates
import SICs.Principal.Dilogarithm.GhostOverlap
import SICs.Principal.Dilogarithm.Pseudolattice
import SICs.Quadratic.ConductorOneElements

/-!
# Unitary conjugates of the principal overlaps

An automorphism of `ℂ` switching `√Δ_K` sends every nonzero principal normalized ghost overlap to
the unit circle.

This module follows [RW26b, Radchenko, Wheeler (2026b), Proposition 7 and the paragraph after
it] at the principal family of [RW26, Radchenko, Wheeler (2026), Theorem 7, `thm:ghostsic`]. It
supplies the unit-modulus input `principalLiveUnitModulus` of the live construction
(`principalLiveUnitModulus_holds` in `SICs.Principal.Construction.Existence`) without any
conjectural hypothesis.

## The argument

Fix `d > 3` and an automorphism `τ` of `ℂ` with `τ(√Δ_K) = -√Δ_K`, where
`Δ_K = disc(K)` for the rank-one field `K = ℚ(ρ_d)`. It moves the selected real copy of `K`.

For `p ≢ 0 (mod d)` the shift point `x_p = ⟨⟨p/d,ρ_d⟩⟩ = (p₁/d)ρ_d - p₀/d` is not in the
principal pseudolattice `I_d = ℤρ_d + ℤ`, since `1, ρ_d` are linearly independent over `ℚ`; and
`(ρ_d³ - 1)x_p ∈ I_d` (`mul_principalShiftElement_mem`). So
`pseudolatticeDilog_norm_map_eq_one` gives `|τ(E_{I_d,ρ_d³}(x_p))| = 1`, and
`E_{I_d,ρ_d³}(x_p) = F(p/d)` (`pseudolatticeDilog_principalShiftElement`).

The bridge `F(p/d) ν̃_d(p) = ζ_d(p)` (`principalDilogValue_mul_phasedGhostOverlap`) has a root of
unity on the right, `ζ_d(p) = (-1)^{s_d(p)} ξ_d^{-Q_d(p)}` with `ξ_d = -e^{πi/d}`, so
`|τ(ζ_d(p))| = 1` for every automorphism `τ`. Hence `|τ(ν̃_d(p))| = 1`, and
`ν̃_d(p) = ν_d(p)` off the zero residue class (`principalPhasedGhostOverlap_eq_overlap`).
-/

noncomputable section

namespace SIC

/-! ### The shift points off the pseudolattice

`x_p ∈ I_d` exactly when both coordinates of `p` are divisible by `d`. -/

/-- The shift point `x_p = ⟨⟨p/d,ρ_d⟩⟩` is not in the principal pseudolattice `I_d = ℤρ_d + ℤ`
when `p ≢ 0 (mod d)`: the hypothesis `x ∉ I` of [RW26b, Radchenko, Wheeler (2026b),
Proposition 7] at the principal shift points. -/
theorem principalShiftElement_notMem (d : RankOneDimension) {p : IntPhaseSpace}
    (hp : intPhaseSpaceMod d p ≠ 0) :
    principalShiftElement d p ∉ (principalPseudolattice d).submodule := by
  rw [← (principalPseudolattice d).isIntegralIndex_characteristic_iff,
    characteristic_principalShiftElement]
  exact not_isIntegralIndex_shiftRationalPoint d (by omega) hp

/-! ### Unitary conjugates

The bridge phase is a root of unity; the finite quantum dilogarithm values are moved to the unit
circle by [RW26b, Radchenko, Wheeler (2026b), Proposition 7]; their quotient is the principal
overlap. -/

/-- Every automorphism of `ℂ` sends the bridge phase `ζ_d(p) = (-1)^{s_d(p)} ξ_d^{-Q_d(p)}` to
the unit circle, since it is a root of unity. Glue for `norm_map_principalNormGhostOverlap`. -/
theorem norm_map_principalDilogBridgePhase (d : RankOneDimension) (τ : ComplexGaloisAutomorphism)
    (p : IntPhaseSpace) :
    ‖τ (principalDilogBridgePhase d p)‖ = 1 := by
  apply norm_eq_one_of_norm_pow_eq_one (by decide : (2 : ℕ) ≠ 0)
  rw [← map_pow, principalDilogBridgePhase_sq, map_inv₀, norm_inv,
    norm_map_thetaCharacter, inv_one]

/-- **[RW26b, Radchenko, Wheeler (2026b), Proposition 7 and the paragraph after it], principal
family**: an automorphism `τ` of `ℂ` with `τ(√Δ_K) = -√Δ_K`, `Δ_K = disc(K)`, sends every
nonzero principal normalized ghost overlap `ν_d(p)`, `p ≢ 0 (mod d)`, to the unit circle. -/
theorem norm_map_principalNormGhostOverlap (d : RankOneDimension)
    {τ : ComplexGaloisAutomorphism} (hτ : SwitchesSqrt τ (NumberField.discr (RankOneField d)))
    {p : IntPhaseSpace} (hp : intPhaseSpaceMod d p ≠ 0) :
    ‖τ (principalNormGhostOverlap d p)‖ = 1 := by
  have hmove := (rankOneRealQuadraticFieldData d).exists_map_realEmbeddingAt_ne_of_switchesSqrt hτ
  have hF : ‖τ (principalDilogValue d (shiftRationalPoint d p))‖ = 1 := by
    rw [← pseudolatticeDilog_principalShiftElement]
    exact pseudolatticeDilog_norm_map_eq_one (principalPseudolattice_isPeriod d) τ hmove
      (mul_principalShiftElement_mem d p) (principalShiftElement_notMem d hp)
  have hbridge := congrArg (fun z : ℂ => ‖τ z‖)
    (principalDilogValue_mul_phasedGhostOverlap d p)
  rw [map_mul, norm_mul, hF, one_mul, norm_map_principalDilogBridgePhase] at hbridge
  rw [← principalPhasedGhostOverlap_eq_overlap d p hp]
  exact hbridge

end SIC

end
