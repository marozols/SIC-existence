/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Dilogarithm.Pseudolattice.Basic

/-!
# Homothety and Change of Basis for the Pseudolattice Dilogarithm

The finite quantum dilogarithm of a pseudolattice is unchanged by a totally positive homothety,
`E_{cI,ε}(cx) = E_{I,ε}(x)`, and independent of the admissible basis presenting the lattice.

This module follows [RW26b, Radchenko, Wheeler (2026b), Section 3, equation (1); Appendix B,
the change of basis and Proposition 8, first case]. The mixed-sign case `α > 0 > α'` of
Proposition 8, which inverts the value, needs the complex-conjugation law (7) and is in
`SICs.Dilogarithm.Pseudolattice.Conjugation`.

## The argument

*Homothety (1).* For `c ∈ K` totally positive, `(cβ₁, cβ₂)` is an admissible basis of `cI` with
the same `τ`, so the same matrix `γ` and real fixed point; the characteristic of `cx` in it is
that of `x` in `(β₁, β₂)`, since `cx/(cβ₂) = x/β₂`. So `E_{cI,ε}(cx) = E_{I,ε}(x)` term by term.

*Change of basis (Appendix B).* Two admissible bases `(τ, β₂)`, `(τ', β₂')` of one lattice are
related by `U ∈ GL₂(ℤ)` with `U(τ, 1)ᵀ = j(τ', 1)ᵀ`, `j = β₂'/β₂` totally positive
(`IsPairMap`); comparing the orientation forms, `det U · (τ - τ̄) = j j̄ (τ' - τ̄')` with all
factors positive, so `det U = 1`. Then `τ' = U·τ`, the matrix of `ε` on the new basis is
`UγU⁻¹` (`IsPairMap.conj`, `IsPeriod.matrix_eq_of_isPairMap`), the characteristic of `x` in the
new basis is `Ur` (`fracSymplecticFormRat_ratVecAction`), and the real cocycle identity from
Kopp's Theorem 4.37, `sfModularCocycleRealTotal_mul_mul_inv` with `j_U(β) = ρ₁(j) > 0`, gives
`ש^{Ur}_{UγU⁻¹}(U·β) = ש^r_γ(β)`; the eta multiplier is a class function
(`etaMultiplier_conj`), so the values agree off `I`, and on `I` both are `√ε`.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
variable {F : RealQuadraticFieldData K}

namespace PseudolatticeBasis

variable (B : PseudolatticeBasis F)

/-! ### Totally positive homothety -/

/-- **The admissible basis `(cβ₁, cβ₂)` of `cI`** for `c` totally positive: the same `τ`, the
scale `cβ₂`. -/
def smul (c : K) (hc : F.IsTotallyPositive c) : PseudolatticeBasis F where
  tau := B.tau
  scale := c * B.scale
  other_lt := B.other_lt
  scale_pos := hc.mul B.scale_pos

variable {B}

/-- **Membership in `cI`**: `y ∈ cI` iff `y = cx` with `x ∈ I` (`mul_mem_span_pair_iff`). -/
theorem mem_smul_submodule_iff {c : K} (hc : F.IsTotallyPositive c) (y : K) :
    y ∈ (B.smul c hc).submodule ↔ ∃ x ∈ B.submodule, y = c * x := by
  constructor
  · intro hy
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hy
    refine ⟨a • (B.scale * B.tau) + b • B.scale,
      Submodule.mem_span_pair.mpr ⟨a, b, rfl⟩, ?_⟩
    rw [← hab]
    simp only [PseudolatticeBasis.submodule, PseudolatticeBasis.smul, zsmul_eq_mul] at *
    ring
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hx
    apply Submodule.mem_span_pair.mpr
    refine ⟨a, b, ?_⟩
    rw [← hab]
    simp only [PseudolatticeBasis.submodule, PseudolatticeBasis.smul, zsmul_eq_mul] at *
    ring

/-- The characteristic of `cx` in `(cβ₁, cβ₂)` is that of `x` in `(β₁, β₂)`, since
`cx/(cβ₂) = x/β₂` (`characteristic_eq_of_eq`). -/
theorem characteristic_smul {c : K} (hc : F.IsTotallyPositive c) (x : K) :
    (B.smul c hc).characteristic (c * x) = B.characteristic x := by
  apply (B.smul c hc).characteristic_eq_of_eq
  change fracSymplecticFormRat (B.characteristic x) B.tau = c * x / (c * B.scale)
  rw [B.fracSymplecticFormRat_characteristic]
  have hc0 : c ≠ 0 := hc.ne_zero
  change x / B.scale = c * x / (c * B.scale)
  field_simp

/-- A period of `I` is a period of `cI`, the normalized lattice `ℤτ + ℤ` being the same. -/
theorem IsPeriod.smul {ε : K} (h : B.IsPeriod ε) (c : K) (hc : F.IsTotallyPositive c) :
    (B.smul c hc).IsPeriod ε :=
  ⟨h.mul_tau_mem, h.mem, h.norm_one, h.one_lt⟩

/-- The matrix of `ε` is unchanged by homothety (`IsPeriod.matrix_eq_of_isPairMap`). -/
theorem IsPeriod.matrix_smul {ε : K} (h : B.IsPeriod ε) {c : K}
    (hc : F.IsTotallyPositive c) :
    (h.smul c hc).matrix = h.matrix := by
  apply (h.smul c hc).matrix_eq_of_isPairMap
  exact h.isPairMap_matrix

end PseudolatticeBasis

/-- **Homothety, [RW26b, Radchenko, Wheeler (2026b), equation (1)]**: `E_{cI,ε}(cx) = E_{I,ε}(x)`
for `c` totally positive, the first case of Proposition 8; the matrix, fixed point and
characteristic are unchanged (`IsPeriod.matrix_smul`, `characteristic_smul`). -/
@[source "RW26b, equation (1), p. 3"]
theorem pseudolatticeDilog_smul {B : PseudolatticeBasis F} {ε : K} (h : B.IsPeriod ε) {c : K}
    (hc : F.IsTotallyPositive c) (x : K) :
    pseudolatticeDilog (h.smul c hc) (c * x) = pseudolatticeDilog h x := by
  simp only [pseudolatticeDilog, h.matrix_smul hc,
    B.characteristic_smul hc]
  rfl

/-! ### Independence of the admissible basis

[RW26b, Radchenko, Wheeler (2026b), Appendix B]: two admissible bases of one lattice are related
by a matrix of determinant one, and the value is conjugation invariant. The change of basis is
built for raw pairs `(τ, b)`, presenting the lattice `b(ℤτ + ℤ)`, so that the mixed-sign case
of Proposition 8 in `SICs.Dilogarithm.Pseudolattice.Conjugation` can use a basis whose second
vector is positive at the first place only. -/

omit [NumberField K] [NumberField.IsTotallyReal K] in
/-- **The change of basis between two presentations of nested lattices**: if `b'τ'` and `b'` lie
in `b(ℤτ + ℤ)`, there is an integer matrix `M` with `M(τ, 1)ᵀ = (b'/b)(τ', 1)ᵀ`, by
`Submodule.mem_span_pair`; the row construction of `exists_matrix_of_mul_mem_span` for two
pairs. -/
theorem exists_pairMap_of_mem_span {τ τ' b b' : K} (hb : b ≠ 0)
    (h1 : b' * τ' ∈ Submodule.span ℤ {b * τ, b}) (h2 : b' ∈ Submodule.span ℤ {b * τ, b}) :
    ∃ M : Mat(2, ℤ), IsPairMap M τ (b' / b) τ' := by
  obtain ⟨a, c, hac⟩ := Submodule.mem_span_pair.mp h1
  obtain ⟨d, e, hde⟩ := Submodule.mem_span_pair.mp h2
  have hrow0 : (a : K) * τ + c = (b' / b) * τ' := by
    apply mul_left_cancel₀ hb
    calc
      b * ((a : K) * τ + c) = a • (b * τ) + c • b := by
        simp [zsmul_eq_mul]; ring
      _ = b' * τ' := hac
      _ = b * ((b' / b) * τ') := by field_simp [hb]
  have hrow1 : (d : K) * τ + e = b' / b := by
    apply mul_left_cancel₀ hb
    calc
      b * ((d : K) * τ + e) = d • (b * τ) + e • b := by
        simp [zsmul_eq_mul]; ring
      _ = b' := hde
      _ = b * (b' / b) := by field_simp [hb]
  exact ⟨!![a, c; d, e], IsPairMap.intro (by simpa using hrow0)
    (by simpa [fltDenominator] using hrow1)⟩

/-- **The orientation identity of a pair map**: for `M(τ, 1)ᵀ = j(τ', 1)ᵀ`,
`det M · (ρ₁τ - ρ₂τ) = ρ₁(j)ρ₂(j)(ρ₁τ' - ρ₂τ')`, the comparison of the orientation forms
`β₁β₂' - β₁'β₂` of the two bases [RW26b, Radchenko, Wheeler (2026b), Appendix B]; it fixes the
sign of `det M` once the signs of `j` and of the orientations are known. -/
theorem IsPairMap.det_mul_sub_eq (F : RealQuadraticFieldData K) {τ τ' j : K} {M : Mat(2, ℤ)}
    (h : IsPairMap M τ j τ') :
    (M.det : ℝ) * (realEmbeddingAt K F.place τ - realEmbeddingAt K F.otherPlace τ) =
      realEmbeddingAt K F.place j * realEmbeddingAt K F.otherPlace j *
        (realEmbeddingAt K F.place τ' - realEmbeddingAt K F.otherPlace τ') := by
  let f := realEmbeddingAt K F.place
  let g := realEmbeddingAt K F.otherPlace
  have hf0 : (M 0 0 : ℝ) * f τ + M 0 1 = f j * f τ' := by
    simpa [f] using congrArg f h.first_row
  have hg0 : (M 0 0 : ℝ) * g τ + M 0 1 = g j * g τ' := by
    simpa [g] using congrArg g h.first_row
  have hf1 : (M 1 0 : ℝ) * f τ + M 1 1 = f j := by
    simpa [f, fltDenominator] using congrArg f h.denominator_eq
  have hg1 : (M 1 0 : ℝ) * g τ + M 1 1 = g j := by
    simpa [g, fltDenominator] using congrArg g h.denominator_eq
  calc
    _ = ((M 0 0 : ℝ) * f τ + M 0 1) * ((M 1 0 : ℝ) * g τ + M 1 1) -
          ((M 0 0 : ℝ) * g τ + M 0 1) * ((M 1 0 : ℝ) * f τ + M 1 1) := by
            rw [Matrix.det_fin_two]
            push_cast
            ring
    _ = _ := by rw [hf0, hg1, hg0, hf1]; ring

/-- **The change of basis between two oriented presentations**
[RW26b, Radchenko, Wheeler (2026b), Appendix B]: mutually included lattices
`b(ℤτ + ℤ)` and `b'(ℤτ' + ℤ)` have an integer pair map of determinant one when their
orientation forms have the same sign. -/
theorem exists_sl2_pairMap_of_span_eq (F : RealQuadraticFieldData K) {τ τ' b b' : K}
    (hb : b ≠ 0) (hb' : b' ≠ 0)
    (hτ : Irrational (realEmbeddingAt K F.place τ))
    (hforward : Submodule.span ℤ {b' * τ', b'} ≤ Submodule.span ℤ {b * τ, b})
    (hback : Submodule.span ℤ {b * τ, b} ≤ Submodule.span ℤ {b' * τ', b'})
    (hsign : 0 < realEmbeddingAt K F.place (b' / b) *
      realEmbeddingAt K F.otherPlace (b' / b) *
      (realEmbeddingAt K F.place τ' - realEmbeddingAt K F.otherPlace τ') *
      (realEmbeddingAt K F.place τ - realEmbeddingAt K F.otherPlace τ)) :
    ∃ U : SL(2, ℤ), IsPairMap (U : Mat(2, ℤ)) τ (b' / b) τ' := by
  have hfirst := hforward (Submodule.subset_span (by simp : b' * τ' ∈ {b' * τ', b'}))
  have hsecond := hforward (Submodule.subset_span (by simp : b' ∈ {b' * τ', b'}))
  obtain ⟨M, hM⟩ := exists_pairMap_of_mem_span hb hfirst hsecond
  have hbackfirst := hback (Submodule.subset_span (by simp : b * τ ∈ {b * τ, b}))
  have hbacksecond := hback (Submodule.subset_span (by simp : b ∈ {b * τ, b}))
  obtain ⟨M', hM'⟩ := exists_pairMap_of_mem_span hb' hbackfirst hbacksecond
  have hj : b' / b ≠ 0 := div_ne_zero hb' hb
  have hpm : M.det = 1 ∨ M.det = -1 :=
    IsPairMap.det_eq_one_or_neg_one hτ hj hM (by simpa [inv_div] using hM')
  have hdet := IsPairMap.det_mul_sub_eq F hM
  have hdiff : realEmbeddingAt K F.place τ - realEmbeddingAt K F.otherPlace τ ≠ 0 := by
    intro he
    simp [he] at hsign
  have hone : M.det = 1 := by
    rcases hpm with hp | hn
    · exact hp
    · have hcast : (M.det : ℝ) = -1 := by exact_mod_cast hn
      rw [hcast] at hdet
      have hmul := congrArg (fun z : ℝ => z *
        (realEmbeddingAt K F.place τ - realEmbeddingAt K F.otherPlace τ)) hdet
      nlinarith [sq_pos_of_ne_zero hdiff]
  exact ⟨⟨M, hone⟩, hM⟩

namespace PseudolatticeBasis

/-- **The change of basis between two admissible bases of one lattice**: `U ∈ SL₂(ℤ)` with
`U(τ, 1)ᵀ = j(τ', 1)ᵀ`, `j = β₂'/β₂`. Existence of an integer `U` with `U(β₁, β₂)ᵀ = (β₁', β₂')ᵀ`
is the equality of the lattices (`mem_span_pair_iff_exists_fracSymplecticFormRat`); its
determinant is `±1` (`IsPairMap.det_eq_one_or_neg_one`) and positive by the orientation
`det U · (ρ₁τ - ρ₂τ) = ρ₁(j)ρ₂(j)(ρ₁τ' - ρ₂τ')`. -/
theorem exists_changeOfBasis {B B' : PseudolatticeBasis F} (hI : B.submodule = B'.submodule) :
    ∃ U : SL(2, ℤ), IsPairMap (U : Mat(2, ℤ)) B.tau (B'.scale / B.scale) B'.tau := by
  apply exists_sl2_pairMap_of_span_eq F B.scale_ne_zero B'.scale_ne_zero
    B.beta_irrational (le_of_eq hI.symm) (le_of_eq hI)
  have hjf : 0 < realEmbeddingAt K F.place (B'.scale / B.scale) := by
    rw [map_div₀]
    exact div_pos B'.scale_pos.1 B.scale_pos.1
  have hjg : 0 < realEmbeddingAt K F.otherPlace (B'.scale / B.scale) := by
    rw [map_div₀]
    exact div_pos B'.scale_pos.2 B.scale_pos.2
  exact mul_pos (mul_pos (mul_pos hjf hjg) (sub_pos.mpr B'.other_lt))
    (sub_pos.mpr B.other_lt)

/-- **The period matrix under change of basis** [RW26b, Radchenko, Wheeler (2026b), Appendix B]:
the second admissible basis has matrix `UγU⁻¹` when its pair map is `U`. -/
theorem IsPeriod.matrix_congr_basis {B B' : PseudolatticeBasis F} {ε : K}
    (h : B.IsPeriod ε) (h' : B'.IsPeriod ε) {U : SL(2, ℤ)}
    (hU : IsPairMap (U : Mat(2, ℤ)) B.tau (B'.scale / B.scale) B'.tau) :
    h'.matrix = U * h.matrix * U⁻¹ := by
  have hmat : (h'.matrix : Mat(2, ℤ)) * U = U * (h.matrix : Mat(2, ℤ)) :=
    IsPairMap.conj B.beta_irrational hU h.isPairMap_matrix h'.isPairMap_matrix
  have hprod : h'.matrix * U = U * h.matrix := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simpa only [Matrix.SpecialLinearGroup.coe_mul] using congrArg (fun M => M i j) hmat
  calc
    h'.matrix = h'.matrix * U * U⁻¹ := by simp [mul_assoc]
    _ = U * h.matrix * U⁻¹ := by rw [hprod]

/-- **The fixed point under change of basis** [RW26b, Radchenko, Wheeler (2026b), Appendix B]:
the real value `β'` is the fractional linear image `U·β`. -/
theorem beta_eq_flt_of_isPairMap {B B' : PseudolatticeBasis F} {U : SL(2, ℤ)}
    (hU : IsPairMap (U : Mat(2, ℤ)) B.tau (B'.scale / B.scale) B'.tau) :
    B'.beta = flt (U : Mat(2, ℤ)) B.beta := by
  have hj : B'.scale / B.scale ≠ 0 := div_ne_zero B'.scale_ne_zero B.scale_ne_zero
  have hflt := IsPairMap.flt_eq hU hj
  have hf := congrArg (realEmbeddingAt K F.place) hflt
  simpa only [PseudolatticeBasis.beta, map_flt] using hf.symm

/-- **The characteristic under change of basis** [RW26b, Radchenko, Wheeler (2026b),
Appendix B]: the characteristic of `x` on the second basis is `Ur`. -/
theorem characteristic_eq_ratVecAction_of_isPairMap {B B' : PseudolatticeBasis F}
    {U : SL(2, ℤ)}
    (hU : IsPairMap (U : Mat(2, ℤ)) B.tau (B'.scale / B.scale) B'.tau) (x : K) :
    B'.characteristic x = ratVecAction (U : Mat(2, ℤ)) (B.characteristic x) := by
  apply B'.characteristic_eq_of_eq
  have hj : fltDenominator (U : Mat(2, ℤ)) B.tau ≠ 0 := by
    rw [hU.denominator_eq]
    exact div_ne_zero B'.scale_ne_zero B.scale_ne_zero
  have hcov := fracSymplecticFormRat_ratVecAction (U : Mat(2, ℤ))
    (B.characteristic x) B.tau hj
  rw [hU.flt_eq (div_ne_zero B'.scale_ne_zero B.scale_ne_zero),
    Matrix.SpecialLinearGroup.det_coe] at hcov
  simp only [Int.cast_one, one_mul, hU.denominator_eq,
    B.fracSymplecticFormRat_characteristic] at hcov
  calc
    _ = (x / B.scale) / (B'.scale / B.scale) := hcov
    _ = x / B'.scale := by field_simp [B.scale_ne_zero, B'.scale_ne_zero]

end PseudolatticeBasis

/-- Kopp's conjugation identity transports the cocycle between two admissible bases whenever
`(ε - 1)x ∈ I`. This is the cocycle step in `pseudolatticeDilog_congr_basis`. -/
private theorem cocycle_congr_basis {B B' : PseudolatticeBasis F} {ε : K}
    (h : B.IsPeriod ε) (h' : B'.IsPeriod ε) {U : SL(2, ℤ)}
    (hU : IsPairMap (U : Mat(2, ℤ)) B.tau (B'.scale / B.scale) B'.tau) (x : K)
    (hG : (ε - 1) * x ∈ B.submodule) (hr : ¬ IsIntegralIndex (B.characteristic x)) :
    sfModularCocycleReal' (B'.characteristic x) h'.matrix B'.beta =
      sfModularCocycleReal' (B.characteristic x) h.matrix B.beta := by
  have hA : h.matrix ∈ gammaSubgroup (B.characteristic x) :=
    (h.mem_gammaSubgroup_characteristic_iff x).mpr hG
  have hAct : U * h.matrix * U⁻¹ ∈
      gammaSubgroup (ratVecAction (U : Mat(2, ℤ)) (B.characteristic x)) :=
    mul_mul_inv_mem_gammaSubgroup_ratVecAction hA U
  have hjU : 0 < fltDenominator (U : Mat(2, ℤ)) B.beta := by
    change 0 < fltDenominator (U : Mat(2, ℤ))
      (realEmbeddingAt K F.place B.tau)
    rw [← map_fltDenominator (realEmbeddingAt K F.place) (U : Mat(2, ℤ)) B.tau,
      hU.denominator_eq, map_div₀]
    exact div_pos B'.scale_pos.1 B.scale_pos.1
  have hjA : 0 < fltDenominator (h.matrix : Mat(2, ℤ)) B.beta := by
    rw [h.fltDenominator_matrix]
    exact lt_trans zero_lt_one h.one_lt
  rw [PseudolatticeBasis.characteristic_eq_ratVecAction_of_isPairMap hU x,
    PseudolatticeBasis.IsPeriod.matrix_congr_basis h h' hU,
    PseudolatticeBasis.beta_eq_flt_of_isPairMap hU,
    sfModularCocycleReal'_of_mem hAct, sfModularCocycleReal'_of_mem hA]
  exact sfModularCocycleRealTotal_mul_mul_inv hA U B.beta_irrational hr
    h.flt_matrix hjA hjU

/-- **Independence of the admissible basis** [RW26b, Radchenko, Wheeler (2026b), Appendix B]:
`E_{I,ε}` computed on two admissible bases of the same lattice agrees. With `U` the change of
basis (`exists_changeOfBasis`), the new matrix is `UγU⁻¹` (`IsPairMap.conj`,
`IsPeriod.matrix_eq_of_isPairMap`), the new fixed point is `U·β`, the new characteristic is `Ur`
(`fracSymplecticFormRat_ratVecAction`, `characteristic_eq_of_eq`); off `I`, Kopp's Theorem 4.37
`sfModularCocycleRealTotal_mul_mul_inv` at `j_U(β) = ρ₁(β₂'/β₂) > 0` and `etaMultiplier_conj`
give equality; on `I` both values are `√ε` (`pseudolatticeDilog_of_mem`). Outside
`(ε - 1)⁻¹I`, both totalized values are zero. -/
theorem pseudolatticeDilog_congr_basis {B B' : PseudolatticeBasis F}
    (hI : B.submodule = B'.submodule) {ε : K} (h : B.IsPeriod ε) (h' : B'.IsPeriod ε) (x : K) :
    pseudolatticeDilog h' x = pseudolatticeDilog h x := by
  obtain ⟨U, hU⟩ := PseudolatticeBasis.exists_changeOfBasis hI
  have hmat := PseudolatticeBasis.IsPeriod.matrix_congr_basis h h' hU
  by_cases hx : x ∈ B.submodule
  · have hx' : x ∈ B'.submodule := by rw [← hI]; exact hx
    rw [pseudolatticeDilog_of_mem h' hx', pseudolatticeDilog_of_mem h hx]
  · have hx' : x ∉ B'.submodule := by rw [← hI]; exact hx
    have hr : ¬ IsIntegralIndex (B.characteristic x) := by
      intro hi
      exact hx ((B.isIntegralIndex_characteristic_iff x).mp hi)
    have hr' : ¬ IsIntegralIndex (B'.characteristic x) := by
      intro hi
      exact hx' ((B'.isIntegralIndex_characteristic_iff x).mp hi)
    rw [pseudolatticeDilog, pseudolatticeDilog,
      finiteDilogValue_of_not_isIntegralIndex h'.matrix B'.beta hr',
      finiteDilogValue_of_not_isIntegralIndex h.matrix B.beta hr]
    by_cases hG : (ε - 1) * x ∈ B.submodule
    · rw [cocycle_congr_basis h h' hU x hG hr, hmat, etaMultiplier_conj]
    · have hA : h.matrix ∉ gammaSubgroup (B.characteristic x) := by
        intro hm
        exact hG ((h.mem_gammaSubgroup_characteristic_iff x).mp hm)
      have hG' : (ε - 1) * x ∉ B'.submodule := by rw [← hI]; exact hG
      have hA' : h'.matrix ∉ gammaSubgroup (B'.characteristic x) := by
        intro hm
        exact hG' ((h'.mem_gammaSubgroup_characteristic_iff x).mp hm)
      simp [sfModularCocycleReal', hA, hA']

end SIC

end
