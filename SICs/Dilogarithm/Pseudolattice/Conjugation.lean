/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Dilogarithm.Pseudolattice.Homothety

/-!
# Complex Conjugation and the Mixed-Sign Homothety of the Pseudolattice Dilogarithm

The complex conjugate of the finite quantum dilogarithm of a pseudolattice,
`conj E_{I,ε}(x) = ⟨x⟩ E_{I,ε}(x)`, and the mixed-sign case `E_{αI,ε}(αx) = E_{I,ε}(x)⁻¹` for
`α > 0 > α'` of the homothety law.

This module follows [RW26b, Radchenko, Wheeler (2026b), Proposition 2, equation (7), citing
RW26, Corollary 1; Appendix B, Proposition 8, third case]. The totally positive case of
Proposition 8 is in `SICs.Dilogarithm.Pseudolattice.Homothety`.

## The argument

*Conjugation (7).* `E(x) = μ_γ/ש^r_γ(β)` off `I`, with `|μ_γ| = 1`. The conjugation law of the
cocycle at a real quadratic fixed point, `conj(ש^r) ש^{-r} = 1`
(`sfModularCocycleRealTotal_conj_mul_neg`), and Kopp's Theorem 4.36, `ש^r ש^{-r} = μ_γ² χ_r(γ)`
(`sfModularCocycleRealTotal_mul_neg_eq_character`), give
`conj E(x) = μ_γ⁻¹ ש^{-r} = μ_γ⁻¹ μ_γ² χ_r(γ)/ש^r = ⟨x⟩ E(x)`. On `I` both sides are `√ε`.
This is the unnumbered proposition `conj F^±(u) = 1/F^∓(-u)` before
[RW26, Radchenko, Wheeler (2026), Corollary 1, `cor:argument`] combined with the reflection
law (4).

*Reflection (Proposition 8, third case).* For `α > 0 > α'`, the pair `(-αβ₁, αβ₂)` is an
oriented basis of `αI` whose second vector is positive at the first place only; normalizing, its
`τ` is `-τ`, its real fixed point is `-β`, the matrix of `ε` on it is `R₀γR₀` for the reflection
`R₀ = diag(-1, 1)`, and the characteristic of `αx` on it is `R₀(-r) = (r₀, -r₁)`. An admissible
basis `(β₁', β₂')` of `αI` is reached from it by `U ∈ SL₂(ℤ)` with `U(-τ, 1)ᵀ = j(τ', 1)ᵀ`,
`j = β₂'/(αβ₂)`, `ρ₁(j) > 0`: `det U = 1` by the orientation identity
(`IsPairMap.det_mul_sub_eq`), since `ρ₁(j)ρ₂(j) < 0` and `ρ₁(-τ) - ρ₂(-τ) < 0`. Kopp's
Theorem 4.37 for determinant one (`sfModularCocycleRealTotal_mul_mul_inv`) transports the value
to `U`, and for the reflection (`sfModularCocycleRealTotal_conj_of_det_neg_one` at `R₀`, with
`j_{R₀}(β) = 1`) it gives `ש^{R₀(-r)}_{R₀γR₀}(-β) = conj ש^{-r}_γ(β)`; the eta multiplier is a
class function (`etaMultiplier_conj`) with `μ_{R₀γR₀} = μ_γ⁻¹`
(`etaMultiplier_eq_inv_of_mul_reflectionMatrix`). Hence
`E_{αI,ε}(αx) = μ_γ⁻¹/conj ש^{-r}_γ(β) = conj E_{I,ε}(-x)`, which (7) and (4) turn into
`E_{I,ε}(x)⁻¹`, the source's form.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
variable {F : RealQuadraticFieldData K} {B : PseudolatticeBasis F} {ε : K}

/-! ### Equation (7): complex conjugation -/

/-- **[RW26b, Radchenko, Wheeler (2026b), Proposition 2, equation (7)]**:
`conj E_{I,ε}(x) = ⟨x⟩ E_{I,ε}(x)` for `x ∈ G_{I,ε}`, from
[RW26, Radchenko, Wheeler (2026), Corollary 1, `cor:argument`]: off `I`, by the conjugation law
`sfModularCocycleRealTotal_conj_mul_neg` and Kopp's Theorem 4.36
`sfModularCocycleRealTotal_mul_neg_eq_character` with `μ_γ² = ψ²(γ)`
(`etaMultiplier_sq_of_trace_pos`) and `|μ_γ| = 1` (`starRingEnd_etaMultiplier`); on `I` both
sides are `√ε` (`pseudolatticeDilog_of_mem`, `thetaCharacter_of_isIntegralIndex`). -/
@[source "RW26b, Proposition 2, p. 4 (equation (7))"]
theorem pseudolatticeDilog_conj (h : B.IsPeriod ε) {x : K} (hx : (ε - 1) * x ∈ B.submodule) :
    starRingEnd ℂ (pseudolatticeDilog h x) =
      pseudolatticeGaussian h x * pseudolatticeDilog h x := by
  by_cases hx0 : x ∈ B.submodule
  · rw [pseudolatticeDilog_of_mem h hx0]
    have hG : pseudolatticeGaussian h x = 1 :=
      thetaCharacter_of_isIntegralIndex h.matrix
        ((B.isIntegralIndex_characteristic_iff x).mpr hx0)
    rw [hG, one_mul]
    simp
  · let r := B.characteristic x
    let A := h.matrix
    have hA : A ∈ gammaSubgroup r := (h.mem_gammaSubgroup_characteristic_iff x).mpr hx
    have hr : ¬ IsIntegralIndex r := by
      intro hi
      exact hx0 ((B.isIntegralIndex_characteristic_iff x).mp hi)
    have hjA : 0 < fltDenominator (A : Mat(2, ℤ)) B.beta := by
      rw [h.fltDenominator_matrix]
      exact zero_lt_one.trans h.one_lt
    have hc : sfModularCocycleRealTotal r A hA B.beta ≠ 0 :=
      sfModularCocycleRealTotal_ne_zero_of_flt_eq_self hA B.beta_irrational hr hjA
        h.flt_matrix
    have hconj := sfModularCocycleRealTotal_conj_mul_neg (F := F) B.other_lt.ne
      hA hr h.flt_matrix (h.fltDenominator_matrix.symm ▸ h.one_lt)
    change starRingEnd ℂ (sfModularCocycleRealTotal r A hA B.beta) *
      sfModularCocycleRealTotal (-r) A (neg_mem_gammaSubgroup hA) B.beta = 1 at hconj
    have hprod := sfModularCocycleRealTotal_mul_neg_eq_character
      B.beta_irrational hr hA h.lowerLeft_pos.le hjA h.flt_matrix
    have hμ : etaMultiplier A ≠ 0 := etaMultiplier_ne_zero A
    have hμsq : etaMultiplier A ^ 2 = etaMultiplierSq A :=
      etaMultiplier_sq_of_trace_pos h.isAttractiveFixedPoint.trace_pos
    have hval : sfModularCocycleRealTotal (-r) A (neg_mem_gammaSubgroup hA) B.beta =
        etaMultiplier A ^ 2 * thetaCharacter r (A : Mat(2, ℤ)) /
          sfModularCocycleRealTotal r A hA B.beta := by
      apply (eq_div_iff hc).mpr
      rw [mul_comm, hμsq]
      exact hprod
    rw [pseudolatticeDilog, finiteDilogValue_of_not_isIntegralIndex A B.beta hr,
      sfModularCocycleReal'_of_mem hA]
    change starRingEnd ℂ
        (etaMultiplier A / sfModularCocycleRealTotal r A hA B.beta) =
      thetaCharacter r (A : Mat(2, ℤ)) *
        (etaMultiplier A / sfModularCocycleRealTotal r A hA B.beta)
    rw [map_div₀, starRingEnd_etaMultiplier, div_eq_mul_inv,
      inv_eq_of_mul_eq_one_right hconj, hval]
    field_simp [hμ, hc]

/-! ### Proposition 8, third case: a mixed-sign homothety

`E_{αI,ε}(αx) = conj E_{I,ε}(-x)` for `α > 0 > α'`, in the form the reflection gives; then the
source's inverse form by (7) and (4). -/

/-- The oriented change of pair from `(-τ, αβ₂)` to an admissible basis of `αI`, used by
`pseudolatticeDilog_smul_of_pos_of_neg`. The two negative signs in the orientation identity
force determinant one. -/
private theorem exists_mixedSignPairMap (B : PseudolatticeBasis F) {α : K}
    (hα : 0 < realEmbeddingAt K F.place α) (hα' : realEmbeddingAt K F.otherPlace α < 0)
    {B' : PseudolatticeBasis F}
    (hI : ∀ y, y ∈ B'.submodule ↔ ∃ z ∈ B.submodule, y = α * z) :
    ∃ U : SL(2, ℤ), IsPairMap (U : Mat(2, ℤ)) (-B.tau)
      (B'.scale / (α * B.scale)) B'.tau := by
  have hα0 : α ≠ 0 := by
    intro he
    simp [he] at hα
  have hb : α * B.scale ≠ 0 := mul_ne_zero hα0 B.scale_ne_zero
  have hforward : B'.submodule ≤
      Submodule.span ℤ {(α * B.scale) * (-B.tau), α * B.scale} := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := (hI y).mp hy
    obtain ⟨m, n, hmn⟩ := Submodule.mem_span_pair.mp hz
    apply Submodule.mem_span_pair.mpr
    refine ⟨-m, n, ?_⟩
    rw [← hmn]
    simp [zsmul_eq_mul]
    ring
  have hback : Submodule.span ℤ {(α * B.scale) * (-B.tau), α * B.scale} ≤
      B'.submodule := by
    apply Submodule.span_le.mpr
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · apply (hI _).mpr
      refine ⟨-(B.scale * B.tau), B.submodule.neg_mem
        (Submodule.subset_span (by simp)), ?_⟩
      ring
    · apply (hI _).mpr
      exact ⟨B.scale, Submodule.subset_span (by simp), rfl⟩
  have hirr : Irrational (realEmbeddingAt K F.place (-B.tau)) := by
    simpa [PseudolatticeBasis.beta] using B.beta_irrational.neg
  apply exists_sl2_pairMap_of_span_eq F hb B'.scale_ne_zero hirr hforward hback
  have hjf : 0 < realEmbeddingAt K F.place (B'.scale / (α * B.scale)) := by
    rw [map_div₀, map_mul]
    exact div_pos B'.scale_pos.1 (mul_pos hα B.scale_pos.1)
  have hjg : realEmbeddingAt K F.otherPlace (B'.scale / (α * B.scale)) < 0 := by
    rw [map_div₀, map_mul]
    exact div_neg_of_pos_of_neg B'.scale_pos.2
      (mul_neg_of_neg_of_pos hα' B.scale_pos.2)
  have hdiff : realEmbeddingAt K F.place (-B.tau) -
      realEmbeddingAt K F.otherPlace (-B.tau) < 0 := by
    simp only [map_neg]
    linarith [B.other_lt]
  exact mul_pos_of_neg_of_neg
    (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hjf hjg) (sub_pos.mpr B'.other_lt))
    hdiff

/-- Reversing the first vector of a period basis gives the reflected period matrix. This is
the matrix used in `pseudolatticeDilog_smul_of_pos_of_neg`. -/
private theorem exists_reflectedPeriodMatrix (h : B.IsPeriod ε) :
    ∃ A₀ : SL(2, ℤ), IsPairMap (A₀ : Mat(2, ℤ)) (-B.tau) ε (-B.tau) ∧
      (A₀ : Mat(2, ℤ)) * reflectionMatrix =
        reflectionMatrix * (h.matrix : Mat(2, ℤ)) := by
  let M : Mat(2, ℤ) := reflectionMatrix * (h.matrix : Mat(2, ℤ)) * reflectionMatrix
  have hdet : M.det = 1 := by
    simp [M, Matrix.det_mul, det_reflectionMatrix, Matrix.SpecialLinearGroup.det_coe]
  let A₀ : SL(2, ℤ) := ⟨M, hdet⟩
  have hR (t : K) : IsPairMap reflectionMatrix t 1 (-t) := by
    simp [IsPairMap, reflectionMatrix, fltDenominator]
  have hpair : IsPairMap (A₀ : Mat(2, ℤ)) (-B.tau) ε (-B.tau) := by
    have hRm : IsPairMap reflectionMatrix (-B.tau) 1 B.tau := by
      simpa only [neg_neg] using hR (-B.tau)
    have hcomp := (hRm.mul h.isPairMap_matrix).mul (hR B.tau)
    simpa only [A₀, M, mul_assoc, one_mul, mul_one, neg_neg] using hcomp
  have hcomm : (A₀ : Mat(2, ℤ)) * reflectionMatrix =
      reflectionMatrix * (h.matrix : Mat(2, ℤ)) := by
    change M * reflectionMatrix = reflectionMatrix * (h.matrix : Mat(2, ℤ))
    simp [M, mul_assoc, reflectionMatrix_mul_self]
  exact ⟨A₀, hpair, hcomm⟩

/-- The period matrix in the mixed-sign basis is conjugate to the reflected matrix; this is
the matrix step in `pseudolatticeDilog_smul_of_pos_of_neg`. -/
private theorem mixedSign_matrix_congr {B' : PseudolatticeBasis F}
    (h' : B'.IsPeriod ε) {α : K} {U A₀ : SL(2, ℤ)}
    (hU : IsPairMap (U : Mat(2, ℤ)) (-B.tau)
      (B'.scale / (α * B.scale)) B'.tau)
    (hA₀ : IsPairMap (A₀ : Mat(2, ℤ)) (-B.tau) ε (-B.tau)) :
    h'.matrix = U * A₀ * U⁻¹ := by
  have hirr : Irrational (realEmbeddingAt K F.place (-B.tau)) := by
    simpa [PseudolatticeBasis.beta, map_neg] using B.beta_irrational.neg
  have hconj : (h'.matrix : Mat(2, ℤ)) * U = U * (A₀ : Mat(2, ℤ)) :=
    IsPairMap.conj hirr hU hA₀ h'.isPairMap_matrix
  have hprod : h'.matrix * U = U * A₀ := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simpa only [Matrix.SpecialLinearGroup.coe_mul] using
      congrArg (fun M : Mat(2, ℤ) => M i j) hconj
  calc
    h'.matrix = h'.matrix * U * U⁻¹ := by simp [mul_assoc]
    _ = U * A₀ * U⁻¹ := by rw [hprod]

/-- Reversing the first basis vector and then changing basis sends the characteristic of
`-x` to that of `αx`; used in `pseudolatticeDilog_smul_of_pos_of_neg`. -/
private theorem mixedSign_characteristic (B B' : PseudolatticeBasis F) {α : K}
    (hα0 : α ≠ 0) {U : SL(2, ℤ)}
    (hU : IsPairMap (U : Mat(2, ℤ)) (-B.tau)
      (B'.scale / (α * B.scale)) B'.tau) (x : K) :
    B'.characteristic (α * x) = ratVecAction (U : Mat(2, ℤ))
      (ratVecAction reflectionMatrix (B.characteristic (-x))) := by
  have hj : B'.scale / (α * B.scale) ≠ 0 :=
    div_ne_zero B'.scale_ne_zero (mul_ne_zero hα0 B.scale_ne_zero)
  have hRchar : fracSymplecticFormRat
      (ratVecAction reflectionMatrix (B.characteristic (-x))) (-B.tau) = x / B.scale := by
    have hcov := fracSymplecticFormRat_ratVecAction reflectionMatrix
      (B.characteristic (-x)) B.tau
      (by rw [fltDenominator_reflectionMatrix]; exact one_ne_zero)
    simp only [flt_reflectionMatrix, det_reflectionMatrix, Int.cast_neg,
      Int.cast_one, neg_one_mul, fltDenominator_reflectionMatrix, div_one] at hcov
    simpa [B.fracSymplecticFormRat_characteristic, neg_div] using hcov
  apply B'.characteristic_eq_of_eq
  have hcov := fracSymplecticFormRat_ratVecAction (U : Mat(2, ℤ))
    (ratVecAction reflectionMatrix (B.characteristic (-x))) (-B.tau)
    (by rw [hU.denominator_eq]; exact hj)
  rw [hU.flt_eq hj, Matrix.SpecialLinearGroup.det_coe] at hcov
  simp only [Int.cast_one, one_mul, hU.denominator_eq, hRchar] at hcov
  rw [hcov]
  field_simp [hα0, B.scale_ne_zero, B'.scale_ne_zero]

/-- The mixed-sign pair map sends `-β` to `β'` with positive denominator; used by
`cocycle_mixedSign`. -/
private theorem mixedSign_basis_flt (B B' : PseudolatticeBasis F) {α : K}
    (hα : 0 < realEmbeddingAt K F.place α) {U : SL(2, ℤ)}
    (hU : IsPairMap (U : Mat(2, ℤ)) (-B.tau)
      (B'.scale / (α * B.scale)) B'.tau) :
    B'.beta = flt (U : Mat(2, ℤ)) (-B.beta) ∧
      0 < fltDenominator (U : Mat(2, ℤ)) (-B.beta) := by
  have hα0 : α ≠ 0 := by
    intro he
    simp [he] at hα
  have hj : B'.scale / (α * B.scale) ≠ 0 :=
    div_ne_zero B'.scale_ne_zero (mul_ne_zero hα0 B.scale_ne_zero)
  constructor
  · have hf := congrArg (realEmbeddingAt K F.place) (hU.flt_eq hj)
    simpa only [PseudolatticeBasis.beta, map_flt, map_neg] using hf.symm
  · have hden := congrArg (realEmbeddingAt K F.place) hU.denominator_eq
    simp only [map_fltDenominator, map_neg, map_div₀, map_mul] at hden
    change fltDenominator (U : Mat(2, ℤ)) (-B.beta) = _ at hden
    rw [hden]
    exact div_pos B'.scale_pos.1 (mul_pos hα B.scale_pos.1)

/-- The reflected period matrix fixes `-β` with positive denominator; used by
`cocycle_mixedSign`. -/
private theorem reflectedPeriod_flt (h : B.IsPeriod ε) {A₀ : SL(2, ℤ)}
    (hA₀pair : IsPairMap (A₀ : Mat(2, ℤ)) (-B.tau) ε (-B.tau)) :
    flt (A₀ : Mat(2, ℤ)) (-B.beta) = -B.beta ∧
      0 < fltDenominator (A₀ : Mat(2, ℤ)) (-B.beta) := by
  constructor
  · have hf := congrArg (realEmbeddingAt K F.place) (hA₀pair.flt_eq h.ne_zero)
    simpa only [PseudolatticeBasis.beta, map_flt, map_neg] using hf
  · have hden := congrArg (realEmbeddingAt K F.place) hA₀pair.denominator_eq
    simp only [map_fltDenominator, map_neg] at hden
    change fltDenominator (A₀ : Mat(2, ℤ)) (-B.beta) = _ at hden
    rw [hden]
    exact zero_lt_one.trans h.one_lt

/-- Reflection and change of basis transport the cocycle for `αx` to the conjugate cocycle
for `-x`; this is the cocycle step in `pseudolatticeDilog_smul_of_pos_of_neg`. -/
private theorem cocycle_mixedSign (h : B.IsPeriod ε) {α : K}
    (hα : 0 < realEmbeddingAt K F.place α) {B' : PseudolatticeBasis F}
    (h' : B'.IsPeriod ε) {U A₀ : SL(2, ℤ)}
    (hU : IsPairMap (U : Mat(2, ℤ)) (-B.tau)
      (B'.scale / (α * B.scale)) B'.tau)
    (hA₀pair : IsPairMap (A₀ : Mat(2, ℤ)) (-B.tau) ε (-B.tau))
    (hRcomm : (A₀ : Mat(2, ℤ)) * reflectionMatrix = reflectionMatrix * (h.matrix : Mat(2, ℤ)))
    {x : K}
    (hxneg : (ε - 1) * (-x) ∈ B.submodule)
    (hr : ¬ IsIntegralIndex (B.characteristic (-x)))
    (hchar : B'.characteristic (α * x) = ratVecAction (U : Mat(2, ℤ))
      (ratVecAction reflectionMatrix (B.characteristic (-x))))
    (hmat : h'.matrix = U * A₀ * U⁻¹) :
    sfModularCocycleReal' (B'.characteristic (α * x)) h'.matrix B'.beta =
      starRingEnd ℂ (sfModularCocycleReal' (B.characteristic (-x)) h.matrix B.beta) := by
  have hA : h.matrix ∈ gammaSubgroup (B.characteristic (-x)) :=
    (h.mem_gammaSubgroup_characteristic_iff (-x)).mpr hxneg
  have hA₀ : A₀ ∈ gammaSubgroup
      (ratVecAction reflectionMatrix (B.characteristic (-x))) :=
    mem_gammaSubgroup_ratVecAction_of_mul_eq hA hRcomm
  have hr₀ : ¬ IsIntegralIndex
      (ratVecAction reflectionMatrix (B.characteristic (-x))) := by
    intro hi
    exact hr ((isIntegralIndex_ratVecAction_iff_of_det
      (Or.inr det_reflectionMatrix) _).mp hi)
  obtain ⟨hβ, hjU⟩ := mixedSign_basis_flt B B' hα hU
  have hjA : 0 < fltDenominator (h.matrix : Mat(2, ℤ)) B.beta := by
    rw [h.fltDenominator_matrix]
    exact zero_lt_one.trans h.one_lt
  obtain ⟨hfix₀, hjA₀⟩ := reflectedPeriod_flt h hA₀pair
  have hA' : h'.matrix ∈ gammaSubgroup (B'.characteristic (α * x)) := by
    rw [hmat, hchar]
    exact mul_mul_inv_mem_gammaSubgroup_ratVecAction hA₀ U
  have htrans := sfModularCocycleRealTotal_mul_mul_inv hA₀ U B.beta_irrational.neg
    hr₀ hfix₀ hjA₀ hjU
  have href := sfModularCocycleRealTotal_conj_of_det_neg_one
    det_reflectionMatrix hA hA₀ hRcomm B.beta_irrational hr h.flt_matrix hjA
    (by rw [fltDenominator_reflectionMatrix]; exact zero_lt_one)
  rw [sfModularCocycleReal'_of_mem hA', sfModularCocycleReal'_of_mem hA]
  simpa only [hchar, hmat, hβ] using
    htrans.trans (by simpa only [flt_reflectionMatrix] using href)

/-- **The third case of [RW26b, Radchenko, Wheeler (2026b), Proposition 8] in conjugate form**:
for `α > 0 > α'`, an admissible basis `B'` of `αI` with the same period, and `x ∈ G_{I,ε}`,
`E_{αI,ε}(αx) = conj E_{I,ε}(-x)`. Through the oriented basis `(-αβ₁, αβ₂)` of `αI`
(`exists_pairMap_of_mem_span`, `IsPairMap.det_mul_sub_eq` for `det U = 1`), Kopp's Theorem 4.37
(`sfModularCocycleRealTotal_mul_mul_inv`), the reflection
(`sfModularCocycleRealTotal_conj_of_det_neg_one` at `reflectionMatrix`), and the eta multiplier
of the reflected matrix (`etaMultiplier_conj`, `etaMultiplier_eq_inv_of_mul_reflectionMatrix`,
`starRingEnd_etaMultiplier`); on `I` both sides are `√ε`. -/
theorem pseudolatticeDilog_smul_of_pos_of_neg (h : B.IsPeriod ε) {α : K}
    (hα : 0 < realEmbeddingAt K F.place α) (hα' : realEmbeddingAt K F.otherPlace α < 0)
    {B' : PseudolatticeBasis F} (hI : ∀ y, y ∈ B'.submodule ↔ ∃ z ∈ B.submodule, y = α * z)
    (h' : B'.IsPeriod ε) {x : K} (hx : (ε - 1) * x ∈ B.submodule) :
    pseudolatticeDilog h' (α * x) = starRingEnd ℂ (pseudolatticeDilog h (-x)) := by
  have hα0 : α ≠ 0 := by
    intro he
    simp [he] at hα
  by_cases hx0 : x ∈ B.submodule
  · have hy0 : α * x ∈ B'.submodule := (hI _).mpr ⟨x, hx0, rfl⟩
    have hneg : -x ∈ B.submodule := B.submodule.neg_mem hx0
    rw [pseudolatticeDilog_of_mem h' hy0, pseudolatticeDilog_of_mem h hneg]
    simp
  · obtain ⟨U, hU⟩ := exists_mixedSignPairMap B hα hα' hI
    obtain ⟨A₀, hA₀pair, hRcomm⟩ := exists_reflectedPeriodMatrix h
    have hxneg : (ε - 1) * (-x) ∈ B.submodule := by
      simpa only [mul_neg] using B.submodule.neg_mem hx
    have hx0neg : -x ∉ B.submodule := by simpa using hx0
    have hr : ¬ IsIntegralIndex (B.characteristic (-x)) := by
      intro hi
      exact hx0neg ((B.isIntegralIndex_characteristic_iff (-x)).mp hi)
    have hchar : B'.characteristic (α * x) = ratVecAction (U : Mat(2, ℤ))
        (ratVecAction reflectionMatrix (B.characteristic (-x))) :=
      mixedSign_characteristic B B' hα0 hU x
    have hr' : ¬ IsIntegralIndex (B'.characteristic (α * x)) := by
      rw [hchar, isIntegralIndex_ratVecAction_iff]
      intro hi
      exact hr ((isIntegralIndex_ratVecAction_iff_of_det
        (Or.inr det_reflectionMatrix) _).mp hi)
    have hmat : h'.matrix = U * A₀ * U⁻¹ :=
      mixedSign_matrix_congr h' hU hA₀pair
    have hC := cocycle_mixedSign h hα h' hU hA₀pair hRcomm hxneg hr hchar hmat
    have hη : etaMultiplier h'.matrix = starRingEnd ℂ (etaMultiplier h.matrix) := by
      rw [hmat, etaMultiplier_conj,
        etaMultiplier_eq_inv_of_mul_reflectionMatrix hRcomm,
        starRingEnd_etaMultiplier]
    rw [pseudolatticeDilog, finiteDilogValue_of_not_isIntegralIndex h'.matrix B'.beta hr',
      hη, hC]
    rw [pseudolatticeDilog, finiteDilogValue_of_not_isIntegralIndex h.matrix B.beta hr]
    rw [map_div₀]

/-- **[RW26b, Radchenko, Wheeler (2026b), Appendix B, Proposition 8, third case]**:
`E_{αI,ε}(αx) = E_{I,ε}(x)⁻¹` for `α > 0 > α'` and `x ∈ G_{I,ε} ∖ I`, from the conjugate form
`pseudolatticeDilog_smul_of_pos_of_neg`, the conjugation law `pseudolatticeDilog_conj` at `-x`,
and the reflection law `pseudolatticeDilog_mul_neg`. -/
@[source "RW26b, Proposition 8, p. 20 (third case)"]
theorem pseudolatticeDilog_smul_of_pos_of_neg_eq_inv (h : B.IsPeriod ε) {α : K}
    (hα : 0 < realEmbeddingAt K F.place α) (hα' : realEmbeddingAt K F.otherPlace α < 0)
    {B' : PseudolatticeBasis F} (hI : ∀ y, y ∈ B'.submodule ↔ ∃ z ∈ B.submodule, y = α * z)
    (h' : B'.IsPeriod ε) {x : K} (hx : (ε - 1) * x ∈ B.submodule) (hx0 : x ∉ B.submodule) :
    pseudolatticeDilog h' (α * x) = (pseudolatticeDilog h x)⁻¹ := by
  have hxneg : (ε - 1) * (-x) ∈ B.submodule := by
    simpa only [mul_neg] using B.submodule.neg_mem hx
  have hA : h.matrix ∈ gammaSubgroup (B.characteristic x) :=
    (h.mem_gammaSubgroup_characteristic_iff x).mpr hx
  have hgauss : pseudolatticeGaussian h (-x) = pseudolatticeGaussian h x := by
    simp only [pseudolatticeGaussian, B.characteristic_neg, thetaCharacter_neg h.matrix hA]
  have hrefl := pseudolatticeDilog_mul_neg h hx hx0
  have hG : pseudolatticeGaussian h x ≠ 0 :=
    thetaCharacter_ne_zero _ _
  rw [pseudolatticeDilog_smul_of_pos_of_neg h hα hα' hI h' hx,
    pseudolatticeDilog_conj h hxneg, hgauss]
  apply eq_inv_of_mul_eq_one_left
  calc
    (pseudolatticeGaussian h x * pseudolatticeDilog h (-x)) *
        pseudolatticeDilog h x =
        pseudolatticeGaussian h x *
          (pseudolatticeDilog h x * pseudolatticeDilog h (-x)) := by ring
    _ = pseudolatticeGaussian h x * (pseudolatticeGaussian h x)⁻¹ := by rw [hrefl]
    _ = 1 := mul_inv_cancel₀ hG

end SIC

end
