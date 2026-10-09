/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Dilogarithm.Pseudolattice.Basic

/-!
# Powers of the Period of the Pseudolattice Dilogarithm

The finite quantum dilogarithm of a pseudolattice at a power of its period is the power of its
value, `E_{I,εⁿ}(x) = E_{I,ε}(x)ⁿ` on `G_{I,ε}`, and a period acts on characteristics through the
inverse of its matrix.

This module follows [RW26b, Radchenko, Wheeler (2026b), Proposition 2, equation (8)], which cites
[RW26, Radchenko, Wheeler (2026), Proposition 8, `prop:powers`]. The groups `G_{I,εʳ}` are viewed
as subgroups of `K/I`, so `G_{I,ε} ⊆ G_{I,εʳ}`, and (8) is stated for `x ∈ G_{I,ε}`.

## The argument

*Powers.* A power `εⁿ`, `n ≥ 1`, of a period is a period: it preserves `ℤτ + ℤ` by iteration,
has norm `N(ε)ⁿ = 1`, and `ρ₁(ε)ⁿ > 1`. Its matrix is `γⁿ`, since `γⁿ(τ, 1)ᵀ = εⁿ(τ, 1)ᵀ` and the
matrix of a period is unique (`IsPairMap.mul`, `IsPeriod.matrix_eq_of_isPairMap`). On `I` both
sides of (8) are `√(εⁿ) = (√ε)ⁿ`; off `I`, `E_{I,εⁿ}(x) = μ_{γⁿ}/ש^r_{γⁿ}(β)` with
`ש^r_{γⁿ}(β) = ש^r_γ(β)ⁿ` by the cocycle relation at a fixed point
(`sfModularCocycleRealTotal_pow_of_flt_eq_self`) and `μ_{γⁿ} = μ_γⁿ` by the reduction to a
Hirzebruch--Jung cycle (`etaMultiplier_pow_of_flt_eq_self`).

*Characteristics.* The characteristic of `εx` is `γ⁻¹r` for the characteristic `r` of `x`
(`characteristic_inv_mul` at `εx`).
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
variable {F : RealQuadraticFieldData K} {B : PseudolatticeBasis F} {ε : K}

namespace PseudolatticeBasis.IsPeriod

/-! ### Powers of a period and their matrices -/

/-- A period preserves the normalized lattice `ℤτ + ℤ` (`mul_tau_mem`, `mem`); the step of
`IsPeriod.pow`. -/
theorem mul_mem_span (h : B.IsPeriod ε) {y : K} (hy : y ∈ Submodule.span ℤ {B.tau, 1}) :
    ε * y ∈ Submodule.span ℤ {B.tau, 1} := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hy
  convert (Submodule.span ℤ {B.tau, 1}).add_mem
    ((Submodule.span ℤ {B.tau, 1}).smul_mem a h.mul_tau_mem)
    ((Submodule.span ℤ {B.tau, 1}).smul_mem b h.mem) using 1
  simp [zsmul_eq_mul]
  ring

/-- **A positive power of a period is a period** [RW26b, Radchenko, Wheeler (2026b),
Proposition 2]: `εⁿ`, `n ≥ 1`, preserves `ℤτ + ℤ` (`mul_mem_span`), has norm `1` (`map_pow`),
and `ρ₁(εⁿ) = ρ₁(ε)ⁿ > 1` (`one_lt_pow₀`). -/
theorem pow (h : B.IsPeriod ε) {n : ℕ} (hn : 0 < n) : B.IsPeriod (ε ^ n) := by
  have hspan : ∀ (k : ℕ) {y : K}, y ∈ Submodule.span ℤ {B.tau, 1} →
      ε ^ k * y ∈ Submodule.span ℤ {B.tau, 1} := by
    intro k
    induction k with
    | zero =>
        intro y hy
        simpa using hy
    | succ k ih =>
        intro y hy
        simpa only [pow_succ', mul_assoc] using h.mul_mem_span (ih hy)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hspan n (Submodule.subset_span (by simp))
  · simpa using hspan n (y := (1 : K)) (Submodule.subset_span (by simp))
  · simp [map_pow, h.norm_one]
  · simpa only [map_pow] using one_lt_pow₀ h.one_lt hn.ne'

/-- **The matrix of `εⁿ` is `γⁿ`** (`IsPairMap.mul` iterated, `matrix_eq_of_isPairMap`). -/
theorem matrix_pow (h : B.IsPeriod ε) {n : ℕ} (hn : 0 < n) :
    (h.pow hn).matrix = h.matrix ^ n := by
  have hpair (k : ℕ) : IsPairMap ((h.matrix ^ k : SL(2, ℤ)) : Mat(2, ℤ))
      B.tau (ε ^ k) B.tau := by
    induction k with
    | zero => simpa only [pow_zero, Matrix.SpecialLinearGroup.coe_one] using
        (IsPairMap.one B.tau)
    | succ k ih =>
        simpa only [pow_succ, Matrix.SpecialLinearGroup.coe_mul] using
          h.isPairMap_matrix.mul ih
  exact ((h.pow hn).matrix_eq_of_isPairMap (hpair n)).symm

/-- The characteristic of `εx` is `γ⁻¹r` for the characteristic `r` of `x`
(`characteristic_inv_mul` at `εx`). -/
theorem characteristic_mul (h : B.IsPeriod ε) (x : K) :
    B.characteristic (ε * x) =
      ratVecAction ((h.matrix⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) (B.characteristic x) := by
  have hchar := h.characteristic_inv_mul (ε * x)
  have hx : ε⁻¹ * (ε * x) = x := by simp [h.ne_zero]
  rw [hx] at hchar
  rw [hchar, ratVecAction_inv_ratVecAction]

end PseudolatticeBasis.IsPeriod

/-! ### Equation (8): powers of the period -/

/-- **[RW26b, Radchenko, Wheeler (2026b), Proposition 2, equation (8)]**:
`E_{I,εⁿ}(x) = E_{I,ε}(x)ⁿ` for `x ∈ G_{I,ε}` and `n ≥ 1`. On `I` both sides are `√(εⁿ)`;
off `I`, `ש^r_{γⁿ}(β) = ש^r_γ(β)ⁿ` (`sfModularCocycleRealTotal_pow_of_flt_eq_self`) and
`μ_{γⁿ} = μ_γⁿ` (`etaMultiplier_pow_of_flt_eq_self`), with `IsPeriod.matrix_pow`. -/
@[source "RW26b, Proposition 2, p. 4 (equation (8))"]
theorem pseudolatticeDilog_pow_period (h : B.IsPeriod ε) {n : ℕ} (hn : 0 < n) {x : K}
    (hx : (ε - 1) * x ∈ B.submodule) :
    pseudolatticeDilog (h.pow hn) x = pseudolatticeDilog h x ^ n := by
  have hr := (h.mem_gammaSubgroup_characteristic_iff x).mpr hx
  have hden : 0 < fltDenominator (h.matrix : Mat(2, ℤ)) B.beta := by
    rw [h.fltDenominator_matrix]
    exact lt_trans zero_lt_one h.one_lt
  have hsqrt (a : ℝ) (ha : 0 ≤ a) (k : ℕ) :
      Real.sqrt (a ^ k) = Real.sqrt a ^ k := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_natCast, ← Real.rpow_mul ha, ← Real.rpow_mul ha, mul_comm]
  unfold pseudolatticeDilog
  rw [h.matrix_pow hn]
  by_cases hint : IsIntegralIndex (B.characteristic x)
  · rw [finiteDilogValue_of_isIntegralIndex (h.matrix ^ n) B.beta hint,
      finiteDilogValue_of_isIntegralIndex h.matrix B.beta hint,
      fltDenominator_pow_of_flt_eq_self hden.ne' h.flt_matrix,
      hsqrt _ hden.le]
    norm_cast
  · rw [finiteDilogValue_of_not_isIntegralIndex (h.matrix ^ n) B.beta hint,
      finiteDilogValue_of_not_isIntegralIndex h.matrix B.beta hint,
      sfModularCocycleReal'_of_mem (pow_mem_gammaSubgroup hr n) B.beta,
      sfModularCocycleReal'_of_mem hr B.beta,
      etaMultiplier_pow_of_flt_eq_self (τ := B.tau) B.other_lt.ne h.flt_matrix
        (by change 1 < fltDenominator (h.matrix : Mat(2, ℤ)) B.beta
            rw [h.fltDenominator_matrix]
            exact h.one_lt) n,
      sfModularCocycleRealTotal_pow_of_flt_eq_self hr B.beta_irrational hint
        h.flt_matrix hden n,
      div_pow]

end SIC

end
