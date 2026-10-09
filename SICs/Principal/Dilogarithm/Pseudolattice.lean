/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Dilogarithm.Pseudolattice.Basic
import SICs.Principal.Dilogarithm.Values

/-!
# The principal pseudolattice

The principal pseudolattice `I_d = ℤρ_d + ℤ` with period `ε = ρ_d³`, whose finite quantum
dilogarithm at `⟨⟨p/d,ρ_d⟩⟩` is the principal value `F(p/d)`.

This module follows [RW26b, Radchenko, Wheeler (2026b), Definition 1 and the paragraph after
Proposition 7] at the principal family of [RW26, Radchenko, Wheeler (2026), Theorem 7,
`thm:ghostsic`]. It presents the principal fixed point `(A_d, ρ_d)` as the pseudolattice data of
`SICs.Dilogarithm.Pseudolattice.Basic`, so that a theorem about `pseudolatticeDilog` applies to
the principal values without any unit-modulus assumption.

## The argument

In the rank-one field `K = ℚ(ρ_d)`, with `ρ_d² = (d-1)ρ_d - 1`, take the oriented basis
`(β₁, β₂) = (ρ_d, 1)`: `β₂ = 1` is totally positive, and orientation is `ρ_d' < ρ_d` at the
selected place, where `ρ_d` is the larger root. The period is `ε = ρ_d³`: it is a unit of norm
`N(ρ_d)³ = 1`, it exceeds `1` since `ρ_d > 1`, and it preserves `ℤρ_d + ℤ` since `ρ_d` does. Its
matrix is `A_d = U_d³`, because `U_d(ρ_d, 1)ᵀ = ρ_d(ρ_d, 1)ᵀ` for `U_d = T^{d-1}S`; the matrix is
unique by `IsPeriod.matrix_eq_of_isPairMap`. The real fixed point is `β = ρ_1(ρ_d) = ρ_d`.

With `β₂ = 1` the characteristic of `x` is the rational `r` with `x = ⟨⟨r,ρ_d⟩⟩`; at
`x = ⟨⟨p/d,ρ_d⟩⟩` it is `p/d`. Hence `E_{I_d,ε}(x) = finiteDilogValue A_d ρ_d (p/d)`, which is
`principalDilogValue d (p/d)` by definition. Since `A_d ∈ Γ_{p/d}`, the element lies in the group
`G_{I_d,ε}`: `(ε - 1)x ∈ I_d`.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### The pseudolattice and its period

The oriented basis `(ρ_d, 1)` of `ℤρ_d + ℤ`, the period `ρ_d³`, and its matrix `A_d`. -/

/-- **The principal pseudolattice** `I_d = ℤρ_d + ℤ` of [RW26b, Radchenko, Wheeler (2026b),
the paragraph after Proposition 7], with oriented basis `(ρ_d, 1)` in the rank-one field. -/
def principalPseudolattice (d : RankOneDimension) :
    PseudolatticeBasis (rankOneRealQuadraticFieldData d) where
  tau := rankOneFieldRoot d
  scale := 1
  other_lt := by
    let F := rankOneRealQuadraticFieldData d
    have hroot : 1 < rankOneRoot d := one_lt_rankOneRoot d d.property
    have hselected : realEmbeddingAt (RankOneField d) F.place (rankOneFieldRoot d) =
        rankOneRoot d := by
      simp [F, rankOneRealQuadraticFieldData, realEmbeddingAt_rankOneInfinitePlace]
    have hprod : rankOneRoot d *
        realEmbeddingAt (RankOneField d) F.otherPlace (rankOneFieldRoot d) = 1 := by
      simpa [hselected, rankOneFieldRoot_norm] using
        F.mul_realEmbeddingAt_otherPlace_eq_norm (rankOneFieldRoot d)
    have hother : realEmbeddingAt (RankOneField d) F.otherPlace (rankOneFieldRoot d) =
        (rankOneRoot d)⁻¹ := by
      calc
        _ = (rankOneRoot d)⁻¹ * (rankOneRoot d *
            realEmbeddingAt (RankOneField d) F.otherPlace (rankOneFieldRoot d)) := by
          field_simp [ne_of_gt (zero_lt_one.trans hroot)]
        _ = (rankOneRoot d)⁻¹ := by rw [hprod, mul_one]
    change realEmbeddingAt (RankOneField d) F.otherPlace (rankOneFieldRoot d) <
      realEmbeddingAt (RankOneField d) F.place (rankOneFieldRoot d)
    rw [hother, hselected]
    exact (inv_lt_one₀ (zero_lt_one.trans hroot)).mpr hroot |>.trans hroot
  scale_pos := ⟨by simp, by simp⟩

/-- The real fixed point of the principal pseudolattice is `ρ_d`. -/
theorem principalPseudolattice_beta (d : RankOneDimension) :
    (principalPseudolattice d).beta = principalRoot d := by
  simp [PseudolatticeBasis.beta, principalPseudolattice, rankOneRealQuadraticFieldData,
    realEmbeddingAt_rankOneInfinitePlace, principalRoot]

/-- The field equation makes `U_d(ρ_d,1)ᵀ = ρ_d(ρ_d,1)ᵀ`; used by
`principalA_isPairMap`. -/
private theorem principalU_isPairMap (d : RankOneDimension) :
    IsPairMap (principalU d : Mat(2, ℤ)) (rankOneFieldRoot d)
      (rankOneFieldRoot d) (rankOneFieldRoot d) := by
  apply IsPairMap.intro
  · have hq : rankOneFieldRoot d ^ 2 -
        ((d : RankOneField d) - 1) * rankOneFieldRoot d + 1 = 0 := by
      simpa using rankOneFieldRoot_quadratic d
    have hrow : ((d : RankOneField d) - 1) * rankOneFieldRoot d - 1 =
        rankOneFieldRoot d * rankOneFieldRoot d := by
      linear_combination -hq
    simpa [coe_principalU, sub_eq_add_neg] using hrow
  · simp [fltDenominator, coe_principalU]

/-- Cubing the pair map for `U_d` gives `A_d(ρ_d,1)ᵀ = ρ_d³(ρ_d,1)ᵀ`, used by
`principalPseudolattice_isPeriod` and `principalPseudolattice_matrix`. -/
private theorem principalA_isPairMap (d : RankOneDimension) :
    IsPairMap (principalA d : Mat(2, ℤ)) (rankOneFieldRoot d)
      (rankOneFieldRoot d ^ 3) (rankOneFieldRoot d) := by
  have hU := principalU_isPairMap d
  have hA := (hU.mul hU).mul hU
  simpa [principalA, Matrix.SpecialLinearGroup.coe_pow, pow_succ, pow_two,
    mul_assoc] using hA

/-- `ε = ρ_d³` is a period of the principal pseudolattice. -/
theorem principalPseudolattice_isPeriod (d : RankOneDimension) :
    (principalPseudolattice d).IsPeriod (rankOneFieldRoot d ^ 3) := by
  have hA := principalA_isPairMap d
  have hroot : 1 < rankOneRoot d := one_lt_rankOneRoot d d.property
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Submodule.mem_span_pair.mpr
    exact ⟨(principalA d : Mat(2, ℤ)) 0 0, (principalA d : Mat(2, ℤ)) 0 1,
      by simpa [principalPseudolattice, zsmul_eq_mul] using hA.first_row⟩
  · apply Submodule.mem_span_pair.mpr
    exact ⟨(principalA d : Mat(2, ℤ)) 1 0, (principalA d : Mat(2, ℤ)) 1 1,
      by simpa [principalPseudolattice, zsmul_eq_mul, fltDenominator] using
        hA.denominator_eq⟩
  · simp [map_pow, rankOneFieldRoot_norm]
  · rw [map_pow]
    simpa [rankOneRealQuadraticFieldData, realEmbeddingAt_rankOneInfinitePlace] using
      one_lt_pow₀ hroot (by norm_num : 3 ≠ 0)

/-- The matrix of the period `ρ_d³` is `A_d = U_d³`. -/
theorem principalPseudolattice_matrix (d : RankOneDimension) :
    (principalPseudolattice_isPeriod d).matrix = principalA d := by
  exact ((principalPseudolattice_isPeriod d).matrix_eq_of_isPairMap
    (principalA_isPairMap d)).symm

/-! ### The principal values

The finite quantum dilogarithm of the principal pseudolattice is the principal value at the
characteristic, and the shift points `⟨⟨p/d,ρ_d⟩⟩` have characteristic `p/d`. -/

/-- **The principal pseudolattice bridge**: `E_{I_d,ρ_d³}(x) = F(r)` for the characteristic `r`
of `x`, with `F = principalDilogValue` ([RW26b, Radchenko, Wheeler (2026b), Definition 1]). -/
theorem pseudolatticeDilog_principal_eq (d : RankOneDimension) (x : RankOneField d) :
    pseudolatticeDilog (principalPseudolattice_isPeriod d) x =
      principalDilogValue d ((principalPseudolattice d).characteristic x) := by
  unfold pseudolatticeDilog
  rw [principalPseudolattice_matrix, principalPseudolattice_beta,
    finiteDilogValue_principalA]

/-- The shift point `x_p = ⟨⟨p/d,ρ_d⟩⟩ = (p₁/d)ρ_d - p₀/d` of the rank-one field. -/
def principalShiftElement (d : RankOneDimension) (p : IntPhaseSpace) : RankOneField d :=
  fracSymplecticFormRat (shiftRationalPoint d p) (rankOneFieldRoot d)

/-- The characteristic of `x_p = ⟨⟨p/d,ρ_d⟩⟩` is `p/d`. -/
theorem characteristic_principalShiftElement (d : RankOneDimension) (p : IntPhaseSpace) :
    (principalPseudolattice d).characteristic (principalShiftElement d p) =
      shiftRationalPoint d p := by
  apply (principalPseudolattice d).characteristic_eq_of_eq
  simp [principalPseudolattice, principalShiftElement]

/-- The shift point `x_p` lies in the group `G_{I_d,ρ_d³}`: `(ρ_d³ - 1)x_p ∈ I_d`. -/
theorem mul_principalShiftElement_mem (d : RankOneDimension) (p : IntPhaseSpace) :
    (rankOneFieldRoot d ^ 3 - 1) * principalShiftElement d p ∈
      (principalPseudolattice d).submodule := by
  apply ((principalPseudolattice_isPeriod d).mem_gammaSubgroup_characteristic_iff _).mp
  rw [principalPseudolattice_matrix, characteristic_principalShiftElement]
  exact principalA_mem_gammaSubgroup_shiftRationalPoint d d.property p

/-- `E_{I_d,ρ_d³}(x_p) = F(p/d)`, the form of `pseudolatticeDilog_principal_eq` at the shift
points consumed by the principal overlaps (`principalDilogValue_mul_phasedGhostOverlap`). -/
theorem pseudolatticeDilog_principalShiftElement (d : RankOneDimension) (p : IntPhaseSpace) :
    pseudolatticeDilog (principalPseudolattice_isPeriod d) (principalShiftElement d p) =
      principalDilogValue d (shiftRationalPoint d p) := by
  rw [pseudolatticeDilog_principal_eq, characteristic_principalShiftElement]

end SIC

end
