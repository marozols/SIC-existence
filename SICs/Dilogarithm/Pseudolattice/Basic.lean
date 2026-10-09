/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Cocycle.FixedPointReduction
import SICs.Dilogarithm.Values
import SICs.Quadratic.LatticeUnits

/-!
# The Finite Quantum Dilogarithm of a Pseudolattice

Pseudolattices `I ⊆ K` of a real quadratic field presented by an oriented basis `(β₁, β₂)` with
`β₂` totally positive, their periods `ε` with the matrix `γ` of `ε` on the basis, the torsion
group `G_{I,ε} = (ε - 1)⁻¹I/I` as fixed characteristics, and the finite quantum dilogarithm
`E_{I,ε}` of Radchenko and Wheeler on it, with its value `√ε` on `I`, its well-definedness on
`K/I`, and the reflection law (4).

This module follows [RW26b, Radchenko, Wheeler (2026b), Section 3, Definition 1 and equations
(2)–(4)]. A pseudolattice is a free rank-two subgroup `I ⊆ K`; an oriented basis `(β₁, β₂)`
has `β₁β₂' - β₁'β₂ > 0`, and `β₂` is taken totally positive. With `τ = β₁/β₂` and `ε > 1` a
norm-one unit with `εI = I`, the matrix `γ ∈ SL₂(ℤ)` with `ε(β₁, β₂) = (aβ₁ + bβ₂, cβ₁ + dβ₂)`
satisfies `γτ = τ` and `cτ + d = ε`, and for `x ∈ G_{I,ε}` with `(ε⁻¹ - 1)x = uβ₁ + vβ₂`,
`E_{I,ε}(x) = μ_γ Φ_{γ,u,0}(x/β₂; τ)` for `x ∉ I` and `E_{I,ε}(x) = √ε` for `x ∈ I`.

## The argument

*Presentation.* Dividing by `β₂`, `I = β₂(ℤτ + ℤ)` with `τ = β₁/β₂`, and orientation says
`τ > τ'` at the two real places; so a `PseudolatticeBasis` is the pair `(τ, β₂)` with `τ' < τ`
and `β₂` totally positive, and the lattice is `Submodule.span ℤ {β₂τ, β₂}` in the language of
`SICs.Quadratic.LatticeUnits`. The real value `β = ρ₁(τ)` is irrational since `τ ≠ τ'`.

*Characteristics.* Every `x ∈ K` is `x = β₂⟨⟨r, τ⟩⟩ = β₂(r₁τ - r₀)` for a unique
`r ∈ ℚ²` (`exists_fracSymplecticFormRat_eq`), the characteristic of `x`; `x ∈ I` exactly when
`r ∈ ℤ²`, and `x ↦ r` is additive. This is the dictionary of `SICs.Dilogarithm.Values`:
`z = x/β₂ = ⟨⟨r, τ⟩⟩`.

*Periods.* A period is a norm-one `ε > 1` with `ε(ℤτ + ℤ) ⊆ ℤτ + ℤ`; its matrix `γ` is the
pair map `γ(τ, 1)ᵀ = ε(τ, 1)ᵀ` (`IsPairMap`, `exists_matrix_of_mul_mem_span`), of determinant
`N(ε) = 1` (`det_eq_mul_of_fltDenominator_eq`). Then `γ·β = β`, `j_γ(β) = ρ₁(ε) > 1`, and
`c > 0` because `cτ + d = ε` and `cτ' + d = ε' = ε⁻¹ < 1 < ε` while `τ > τ'`: this is
`IsAttractiveFixedPoint γ β`. Since `ε` is integral of norm one, `ε⁻¹ = Tr(ε) - ε` also
preserves the lattice, so `εI = I`. Conversely, an attractive fixed point `β = ρ₁(τ)` of `γ`
with `τ ∈ K` arises this way from the basis `(τ, 1)` and the period `ε = cτ + d`
(`ofAttractiveFixedPoint`): `γτ = τ` in `K` gives `ετ = aτ + b`, `N(ε) = det γ = 1`, and the
same inequalities read backwards give the orientation `τ' < τ`.

*The group.* `γ ∈ Γ_r` means `(γ - I)r ∈ ℤ²`, i.e. `⟨⟨γr, τ⟩⟩ - ⟨⟨r, τ⟩⟩ ∈ ℤτ + ℤ`; by
`fracSymplecticFormRat_ratVecAction` at the fixed point, `⟨⟨γr, τ⟩⟩ = ⟨⟨r, τ⟩⟩/ε`, so this is
`(ε⁻¹ - 1)x ∈ I`, equivalently `(ε - 1)x ∈ I`: the group `G_{I,ε} = (ε - 1)⁻¹I/I` of
[RW26b, Radchenko, Wheeler (2026b), Definition 1] is the fixed characteristics of `γ` modulo
`N = Tr ε - 2`.

*Values.* `E_{I,ε}(x) = finiteDilogValue γ β r` at the characteristic of `x`; the laws of
`SICs.Dilogarithm.Values` transport: `E = √ε` on `I`, `E` depends only on `x` modulo `I`
(`finiteDilogValue_congr`), `E(x) ≠ 0`, and the reflection law `E(x)E(-x) = ⟨x⟩⁻¹` off `I`
with the Gaussian `⟨x⟩ = χ_r(γ)` (`finiteDilogValue_mul_valueMinus_neg`). The Gaussian (2) of
[RW26b] is taken in this theta-character form; the homothety laws and the independence of the
basis are in `SICs.Dilogarithm.Pseudolattice.Homothety`.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]

/-! ### Oriented bases with totally positive second vector

`I = β₂(ℤτ + ℤ)` with `τ' < τ` and `β₂` totally positive. -/

/-- **A pseudolattice with an admissible basis** [RW26b, Radchenko, Wheeler (2026b), Section 3]:
the lattice `I = β₂(ℤτ + ℤ) = ℤβ₁ + ℤβ₂` with `τ = β₁/β₂`, presented by `τ` with `τ' < τ`
(the orientation `β₁β₂' - β₁'β₂ > 0`) and the totally positive scale `β₂`. The real value
`ρ₁(τ)` is the fixed point at which the finite quantum dilogarithm is evaluated. -/
structure PseudolatticeBasis (F : RealQuadraticFieldData K) where
  /-- `τ = β₁/β₂`. -/
  tau : K
  /-- `β₂`, the second basis vector. -/
  scale : K
  /-- Orientation: `τ' < τ`, i.e. `β₁β₂' - β₁'β₂ > 0`. -/
  other_lt : realEmbeddingAt K F.otherPlace tau < realEmbeddingAt K F.place tau
  /-- `β₂ > 0` at both real places. -/
  scale_pos : F.IsTotallyPositive scale

namespace PseudolatticeBasis

variable {F : RealQuadraticFieldData K} (B : PseudolatticeBasis F)

/-- The pseudolattice `I = ℤβ₁ + ℤβ₂ = span ℤ {β₂τ, β₂}` itself. -/
def submodule : Submodule ℤ K :=
  Submodule.span ℤ {B.scale * B.tau, B.scale}

/-- The real fixed point `β = ρ₁(τ)`. -/
def beta : ℝ := realEmbeddingAt K F.place B.tau

/-- `β₂ ≠ 0`. -/
theorem scale_ne_zero : B.scale ≠ 0 := by
  exact B.scale_pos.ne_zero

/-- `β` is irrational, since `ρ₁(τ) ≠ ρ₂(τ)` (`irrational_realEmbeddingAt_of_ne`). -/
theorem beta_irrational : Irrational B.beta := by
  exact irrational_realEmbeddingAt_of_ne B.other_lt.ne'

/-- **Membership in `I`**: `x ∈ I` iff `x = β₂⟨⟨v, τ⟩⟩` for an integer vector `v`
(`mem_span_pair_iff_exists_fracSymplecticFormRat`). -/
theorem mem_submodule_iff (x : K) :
    x ∈ B.submodule ↔
      ∃ v : Fin 2 → ℚ, IsIntegralIndex v ∧ x = B.scale * fracSymplecticFormRat v B.tau := by
  exact mem_span_pair_iff_exists_fracSymplecticFormRat B.scale B.tau x

/-! ### Characteristics

`x = β₂⟨⟨r, τ⟩⟩` for a unique `r ∈ ℚ²`. -/

/-- **The characteristic of `x ∈ K`**: the unique `r ∈ ℚ²` with `x/β₂ = ⟨⟨r, τ⟩⟩ = r₁τ - r₀`
(`exists_fracSymplecticFormRat_eq`); `z = x/β₂` is the argument of `Φ_{γ,u,0}` in
[RW26b, Radchenko, Wheeler (2026b), Definition 1] under the dictionary of
`SICs.Dilogarithm.Values`. -/
def characteristic (x : K) : Fin 2 → ℚ :=
  Classical.choose
    (exists_fracSymplecticFormRat_eq F.finrank_eq_two B.beta_irrational (x / B.scale))

/-- `⟨⟨r, τ⟩⟩ = x/β₂` at the characteristic `r` of `x`. -/
theorem fracSymplecticFormRat_characteristic (x : K) :
    fracSymplecticFormRat (B.characteristic x) B.tau = x / B.scale := by
  exact (Classical.choose_spec
    (exists_fracSymplecticFormRat_eq F.finrank_eq_two B.beta_irrational
      (x / B.scale))).symm

/-- The characteristic is determined by its pairing: `⟨⟨r, τ⟩⟩ = x/β₂` forces
`r = characteristic x`, since `τ` is irrational at `ρ₁` (`ratCast_eq_zero_of_irrational_mul`). -/
theorem characteristic_eq_of_eq {x : K} {r : Fin 2 → ℚ}
    (hr : fracSymplecticFormRat r B.tau = x / B.scale) : B.characteristic x = r := by
  have hpair := (B.fracSymplecticFormRat_characteristic x).trans hr.symm
  have hreal := congrArg (realEmbeddingAt K F.place) hpair
  simp only [map_fracSymplecticFormRat] at hreal
  have hrel :
      (((B.characteristic x 1 - r 1) : ℚ) : ℝ) * B.beta =
        (((B.characteristic x 0 - r 0) : ℚ) : ℝ) := by
    simp only [fracSymplecticFormRat, beta] at hreal ⊢
    push_cast
    linarith
  obtain ⟨h1, h0⟩ := ratCast_eq_zero_of_irrational_mul B.beta_irrational hrel
  funext i
  fin_cases i
  · exact sub_eq_zero.mp h0
  · exact sub_eq_zero.mp h1

/-- A characteristic recovers the element built from its pairing with `τ`; used when
constructing preimages in `exists_residue_eq` and `pseudolatticeDilog_distribution`. -/
theorem characteristic_scale_fracSymplecticFormRat (s : Fin 2 → ℚ) :
    B.characteristic (B.scale * fracSymplecticFormRat s B.tau) = s := by
  apply B.characteristic_eq_of_eq
  simp [B.scale_ne_zero]

/-- `characteristic 0 = 0`. -/
@[simp]
theorem characteristic_zero : B.characteristic 0 = 0 :=
  B.characteristic_eq_of_eq (by simp [fracSymplecticFormRat])

/-- `characteristic (-x) = -characteristic x` (`fracSymplecticFormRat_neg`). -/
theorem characteristic_neg (x : K) : B.characteristic (-x) = -B.characteristic x := by
  apply B.characteristic_eq_of_eq
  rw [fracSymplecticFormRat_neg, B.fracSymplecticFormRat_characteristic, neg_div]

/-- `characteristic (x - y) = characteristic x - characteristic y`. -/
theorem characteristic_sub (x y : K) :
    B.characteristic (x - y) = B.characteristic x - B.characteristic y := by
  apply B.characteristic_eq_of_eq
  rw [fracSymplecticFormRat_sub, B.fracSymplecticFormRat_characteristic,
    B.fracSymplecticFormRat_characteristic, sub_div]

/-- `characteristic (x + y) = characteristic x + characteristic y`. -/
theorem characteristic_add (x y : K) :
    B.characteristic (x + y) = B.characteristic x + B.characteristic y := by
  apply B.characteristic_eq_of_eq
  rw [fracSymplecticFormRat_add, B.fracSymplecticFormRat_characteristic,
    B.fracSymplecticFormRat_characteristic, add_div]

/-- **`x ∈ I` iff its characteristic is integral** (`mem_submodule_iff`,
`characteristic_eq_of_eq`). -/
theorem isIntegralIndex_characteristic_iff (x : K) :
    IsIntegralIndex (B.characteristic x) ↔ x ∈ B.submodule := by
  rw [B.mem_submodule_iff]
  constructor
  · intro hx
    exact ⟨B.characteristic x, hx, by
      rw [B.fracSymplecticFormRat_characteristic, mul_div_cancel₀ x B.scale_ne_zero]⟩
  · rintro ⟨v, hv, hval⟩
    convert hv using 1
    apply B.characteristic_eq_of_eq
    rw [hval, mul_div_cancel_left₀ _ B.scale_ne_zero]

/-! ### Periods and their matrices

A norm-one unit `ε > 1` with `ε(ℤτ + ℤ) ⊆ ℤτ + ℤ`, and the matrix `γ` with
`γ(τ, 1)ᵀ = ε(τ, 1)ᵀ`. -/

/-- **A period of the pseudolattice** [RW26b, Radchenko, Wheeler (2026b), Section 3]: a
norm-one unit `ε > 1` (at the first real place) with `εI = I`, stated as `ε(ℤτ + ℤ) ⊆ ℤτ + ℤ`
on the normalized lattice. -/
structure IsPeriod (ε : K) : Prop where
  /-- `ετ ∈ ℤτ + ℤ`. -/
  mul_tau_mem : ε * B.tau ∈ Submodule.span ℤ {B.tau, 1}
  /-- `ε ∈ ℤτ + ℤ`. -/
  mem : ε ∈ Submodule.span ℤ {B.tau, 1}
  /-- `N(ε) = 1`. -/
  norm_one : Algebra.norm ℚ ε = 1
  /-- `ε > 1` at the first real place. -/
  one_lt : 1 < realEmbeddingAt K F.place ε

namespace IsPeriod

variable {B} {ε : K} (h : B.IsPeriod ε)
include h

/-- `ε ≠ 0`. -/
theorem ne_zero : ε ≠ 0 := by
  intro he
  have := h.one_lt
  simp [he] at this
  linarith

/-- `ρ₂(ε) = ρ₁(ε)⁻¹`, since `ρ₁(ε)ρ₂(ε) = N(ε) = 1`
(`mul_realEmbeddingAt_otherPlace_eq_norm`). -/
theorem other_eq_inv :
    realEmbeddingAt K F.otherPlace ε = (realEmbeddingAt K F.place ε)⁻¹ := by
  have hf : realEmbeddingAt K F.place ε ≠ 0 := ne_of_gt (zero_lt_one.trans h.one_lt)
  apply mul_left_cancel₀ hf
  rw [mul_inv_cancel₀ hf]
  simpa [h.norm_one] using F.mul_realEmbeddingAt_otherPlace_eq_norm ε

/-- `εI ⊆ I`. -/
theorem mul_mem {x : K} (hx : x ∈ B.submodule) : ε * x ∈ B.submodule := by
  have hx' : x / B.scale ∈ Submodule.span ℤ {B.tau, 1} :=
    (mul_mem_span_pair_iff B.scale_ne_zero B.tau (x / B.scale)).mp
      (by simpa [PseudolatticeBasis.submodule, mul_div_cancel₀ x B.scale_ne_zero] using hx)
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hx'
  have hprod : ε * (x / B.scale) ∈ Submodule.span ℤ {B.tau, 1} := by
    rw [← hab]
    convert (Submodule.span ℤ {B.tau, 1}).add_mem
      ((Submodule.span ℤ {B.tau, 1}).smul_mem a h.mul_tau_mem)
      ((Submodule.span ℤ {B.tau, 1}).smul_mem b h.mem) using 1;
      simp [zsmul_eq_mul]; ring
  have := (mul_mem_span_pair_iff B.scale_ne_zero B.tau (ε * (x / B.scale))).mpr hprod
  convert this using 1
  · simp [PseudolatticeBasis.submodule]
  · field_simp [B.scale_ne_zero]

/-- A norm-one period of one pseudolattice is a period of another when it preserves the
second pseudolattice. Used by `IsPeriod.of_le` and the split Frobenius theorem. -/
theorem of_mul_mem {B' : PseudolatticeBasis F}
    (hB' : ∀ y ∈ B'.submodule, ε * y ∈ B'.submodule) : B'.IsPeriod ε := by
  refine ⟨?_, ?_, h.norm_one, h.one_lt⟩
  · apply (mul_mem_span_pair_iff B'.scale_ne_zero B'.tau (ε * B'.tau)).mp
    simpa only [PseudolatticeBasis.submodule, mul_left_comm, mul_comm, mul_assoc] using
      hB' (B'.scale * B'.tau)
        (Submodule.subset_span (by simp : B'.scale * B'.tau ∈ {B'.scale * B'.tau, B'.scale}))
  · apply (mul_mem_span_pair_iff B'.scale_ne_zero B'.tau ε).mp
    simpa only [PseudolatticeBasis.submodule, mul_comm] using
      hB' B'.scale
        (Submodule.subset_span (by simp : B'.scale ∈ {B'.scale * B'.tau, B'.scale}))

/-- **There is a matrix `γ ∈ SL₂(ℤ)` with `γ(τ, 1)ᵀ = ε(τ, 1)ᵀ`**, that is
`ε(β₁, β₂) = (aβ₁ + bβ₂, cβ₁ + dβ₂)` [RW26b, Radchenko, Wheeler (2026b), Section 3]: the pair
map of `exists_matrix_of_mul_mem_span`, of determinant `N(ε) = 1`
(`det_eq_mul_of_fltDenominator_eq`, `mul_realEmbeddingAt_otherPlace_eq_norm`). -/
theorem exists_matrix : ∃ M : SL(2, ℤ), IsPairMap (M : Mat(2, ℤ)) B.tau ε B.tau := by
  obtain ⟨M, hden, hfirst⟩ := exists_matrix_of_mul_mem_span h.mul_tau_mem h.mem
  have hdetR : (M.det : ℝ) = 1 := by
    rw [det_eq_mul_of_fltDenominator_eq B.other_lt.ne' hden hfirst,
      F.mul_realEmbeddingAt_otherPlace_eq_norm, h.norm_one]
    norm_num
  have hdet : M.det = 1 := by exact_mod_cast hdetR
  exact ⟨⟨M, hdet⟩, IsPairMap.intro hfirst.symm hden.symm⟩

/-- **The matrix `γ` of the period**, `γ(τ, 1)ᵀ = ε(τ, 1)ᵀ` (`exists_matrix`). -/
def matrix : SL(2, ℤ) := Classical.choose h.exists_matrix

/-- `γ(τ, 1)ᵀ = ε(τ, 1)ᵀ`. -/
theorem isPairMap_matrix : IsPairMap (h.matrix : Mat(2, ℤ)) B.tau ε B.tau :=
  Classical.choose_spec h.exists_matrix

/-- `γ` is the unique matrix with `γ(τ, 1)ᵀ = ε(τ, 1)ᵀ` (`IsPairMap.unique`). -/
theorem matrix_eq_of_isPairMap {M : SL(2, ℤ)} (hM : IsPairMap (M : Mat(2, ℤ)) B.tau ε B.tau) :
    M = h.matrix := by
  apply Subtype.ext
  exact IsPairMap.unique B.beta_irrational hM h.isPairMap_matrix

/-- `j_γ(β) = ρ₁(ε)` (`IsPairMap.denominator_eq`, `map_fltDenominator`). -/
theorem fltDenominator_matrix :
    fltDenominator (h.matrix : Mat(2, ℤ)) B.beta = realEmbeddingAt K F.place ε := by
  rw [beta, ← map_fltDenominator, h.isPairMap_matrix.denominator_eq]

/-- `γ·β = β` (`IsPairMap.flt_eq`, `map_flt`). -/
theorem flt_matrix : flt (h.matrix : Mat(2, ℤ)) B.beta = B.beta := by
  rw [beta, ← map_flt, h.isPairMap_matrix.flt_eq h.ne_zero]

/-- **`c > 0`**: `cρ₁(τ) + d = ρ₁(ε) > 1` and `cρ₂(τ) + d = ρ₂(ε) = ρ₁(ε)⁻¹ < 1` with
`ρ₂(τ) < ρ₁(τ)`, so `c(ρ₁(τ) - ρ₂(τ)) > 0`. -/
theorem lowerLeft_pos : 0 < (h.matrix : Mat(2, ℤ)) 1 0 := by
  have hfirst :
      ((h.matrix : Mat(2, ℤ)) 1 0 : ℝ) * B.beta +
        ((h.matrix : Mat(2, ℤ)) 1 1 : ℝ) = realEmbeddingAt K F.place ε := by
    simpa [fltDenominator] using h.fltDenominator_matrix
  have hsecond :
      ((h.matrix : Mat(2, ℤ)) 1 0 : ℝ) * realEmbeddingAt K F.otherPlace B.tau +
        ((h.matrix : Mat(2, ℤ)) 1 1 : ℝ) = realEmbeddingAt K F.otherPlace ε := by
    have hmap := congrArg (realEmbeddingAt K F.otherPlace)
      h.isPairMap_matrix.denominator_eq
    simpa [map_fltDenominator, fltDenominator] using hmap
  have hother : realEmbeddingAt K F.otherPlace ε < 1 := by
    rw [h.other_eq_inv]
    exact (inv_lt_one₀ (zero_lt_one.trans h.one_lt)).mpr h.one_lt
  have hdiff : 0 < ((h.matrix : Mat(2, ℤ)) 1 0 : ℝ) *
      (B.beta - realEmbeddingAt K F.otherPlace B.tau) := by
    nlinarith [h.one_lt]
  have hc : 0 < ((h.matrix : Mat(2, ℤ)) 1 0 : ℝ) :=
    (mul_pos_iff_of_pos_right (sub_pos.mpr B.other_lt)).mp hdiff
  exact_mod_cast hc

/-- **The period's matrix at the fixed point is attractive**: `IsAttractiveFixedPoint γ β`, from
`beta_irrational`, `flt_matrix`, `fltDenominator_matrix` with `one_lt`, and `lowerLeft_pos`. -/
theorem isAttractiveFixedPoint : IsAttractiveFixedPoint h.matrix B.beta := by
  exact ⟨B.beta_irrational, h.flt_matrix,
    h.fltDenominator_matrix.symm ▸ h.one_lt, h.lowerLeft_pos⟩

/-- **The period's matrix is conjugate to a letter word.** There are `R ∈ SL₂(ℤ)` with
`j_R(β) > 0` and a nonempty word `[b₁,…,b_n]` with every `b_j ≥ 2` such that
`RγR⁻¹ = ∏_j T^{b_j}S` and `(∏_j T^{b_j}S, R·β)` is again an attractive fixed point. The word is
the Hirzebruch–Jung cycle of the reduced point `R·β` (`exists_hjCycleMatrix_conj`,
`hjCycleMatrix_eq_letterWord`). -/
theorem exists_letterWord_conj :
    ∃ (R : SL(2, ℤ)) (bs : List ℤ), bs ≠ [] ∧ (∀ b ∈ bs, 2 ≤ b) ∧
      0 < fltDenominator (R : Mat(2, ℤ)) B.beta ∧
      R * h.matrix * R⁻¹ = letterWord bs ∧
      IsAttractiveFixedPoint (letterWord bs) (flt (R : Mat(2, ℤ)) B.beta) := by
  have hjA : 1 < fltDenominator (h.matrix : Mat(2, ℤ)) B.beta := by
    rw [h.fltDenominator_matrix]
    exact h.one_lt
  obtain ⟨R, N, hNpos, hjR, hx1, hperiod, hconj⟩ :=
    exists_hjCycleMatrix_conj B.other_lt.ne h.flt_matrix hjA
  let x := flt (R : Mat(2, ℤ)) B.beta
  change 0 < fltDenominator (R : Mat(2, ℤ)) B.beta at hjR
  change 1 < x at hx1
  change hjPeriod x N = x at hperiod
  change R * h.matrix * R⁻¹ = hjCycleMatrix x N at hconj
  have hirr : Irrational x := Irrational.flt B.beta_irrational R
  have hNne : N ≠ 0 := Nat.ne_of_gt hNpos
  have hne : hjLetters x N ≠ [] := by
    intro hempty
    have hlen := hjLetters_length x N
    rw [hempty] at hlen
    simp at hlen
    exact hNne hlen.symm
  have hden : 1 < fltDenominator (hjCycleMatrix x N : Mat(2, ℤ)) x := by
    rw [← hconj]
    change 1 < fltDenominator ((R * h.matrix * R⁻¹ : SL(2, ℤ)) : Mat(2, ℤ))
      (flt (R : Mat(2, ℤ)) B.beta)
    rw [fltDenominator_mul_mul_inv_of_flt_eq_self R hjR.ne'
      (zero_lt_one.trans hjA).ne' h.flt_matrix]
    exact hjA
  refine ⟨R, hjLetters x N, hne, ?_, hjR, ?_, ?_⟩
  · intro b hb
    exact two_le_of_mem_hjLetters hirr hx1 N b hb
  · simpa only [hjCycleMatrix_eq_letterWord] using hconj
  · rw [← hjCycleMatrix_eq_letterWord]
    exact ⟨hirr, flt_hjCycleMatrix_of_hjPeriod_eq hirr hperiod, hden,
      lowerLeft_hjCycleMatrix_pos hirr hNne⟩

/-- The period's inverse is the trace of its basis matrix minus the period; used in
`inv_mul_mem`. -/
private theorem inv_eq_matrix_trace :
    ε⁻¹ = (((h.matrix : Mat(2, ℤ)) 0 0 + (h.matrix : Mat(2, ℤ)) 1 1 : ℤ) : K) - ε := by
  let M : Mat(2, ℤ) := h.matrix
  have hden : ε = (M 1 0 : K) * B.tau + (M 1 1 : K) := by
    simpa [M, fltDenominator] using h.isPairMap_matrix.denominator_eq.symm
  have hfirst : (M 0 0 : K) * B.tau + (M 0 1 : K) = ε * B.tau :=
    h.isPairMap_matrix.first_row
  have hdet : (M 0 0 : K) * (M 1 1 : K) - (M 0 1 : K) * (M 1 0 : K) = 1 := by
    have hd : M.det = 1 := h.matrix.det_coe
    rw [Matrix.det_fin_two] at hd
    exact_mod_cast hd
  have hquad : ε ^ 2 - ((M 0 0 + M 1 1 : ℤ) : K) * ε + 1 = 0 := by
    push_cast
    linear_combination (ε - (M 0 0 : K)) * hden - (M 1 0 : K) * hfirst - hdet
  change ε⁻¹ = ((M 0 0 + M 1 1 : ℤ) : K) - ε
  apply mul_left_cancel₀ h.ne_zero
  rw [mul_inv_cancel₀ h.ne_zero]
  linear_combination hquad

/-- **`ε⁻¹I ⊆ I`**: the quadratic relation of `ε` from the pair map gives
`ε⁻¹ = Tr(γ) - ε` (`inv_eq_matrix_trace`), so the inverse preserves the lattice. -/
theorem inv_mul_mem {x : K} (hx : x ∈ B.submodule) : ε⁻¹ * x ∈ B.submodule := by
  have hmul := h.mul_mem hx
  have htrace := B.submodule.smul_mem
    ((h.matrix : Mat(2, ℤ)) 0 0 + (h.matrix : Mat(2, ℤ)) 1 1) hx
  convert B.submodule.sub_mem htrace hmul using 1
  simp [h.inv_eq_matrix_trace, zsmul_eq_mul, sub_mul]

/-- The matrix action on characteristics corresponds to multiplication by `ε⁻¹`; used by
`mem_gammaSubgroup_characteristic_iff` and the unit-invariance law. -/
theorem characteristic_inv_mul (x : K) :
    B.characteristic (ε⁻¹ * x) = ratVecAction (h.matrix : Mat(2, ℤ)) (B.characteristic x) := by
  have htrans := fracSymplecticFormRat_ratVecAction (h.matrix : Mat(2, ℤ))
    (B.characteristic x) B.tau (by
      rw [h.isPairMap_matrix.denominator_eq]
      exact h.ne_zero)
  rw [h.isPairMap_matrix.flt_eq h.ne_zero, h.isPairMap_matrix.denominator_eq,
    h.matrix.det_coe, Int.cast_one, one_mul,
    B.fracSymplecticFormRat_characteristic] at htrans
  apply B.characteristic_eq_of_eq
  rw [htrans]
  field_simp [h.ne_zero, B.scale_ne_zero]

/-- **The group `G_{I,ε}` as fixed characteristics**: `γ ∈ Γ_r` for the characteristic `r` of
`x` iff `(ε - 1)x ∈ I`; by `fracSymplecticFormRat_ratVecAction` at the fixed point,
`⟨⟨γr, τ⟩⟩ = ⟨⟨r, τ⟩⟩/ε`, so `(γ - I)r ∈ ℤ²` says `(ε⁻¹ - 1)x ∈ I`, and `ε` is a unit of
the lattice (`mul_mem`, `inv_mul_mem`). This is `G_{I,ε} = (ε - 1)⁻¹I/I` of
[RW26b, Radchenko, Wheeler (2026b), Definition 1]. -/
theorem mem_gammaSubgroup_characteristic_iff (x : K) :
    h.matrix ∈ gammaSubgroup (B.characteristic x) ↔ (ε - 1) * x ∈ B.submodule := by
  have hchar : B.characteristic ((ε⁻¹ - 1) * x) =
      ratVecAction (h.matrix : Mat(2, ℤ)) (B.characteristic x) - B.characteristic x := by
    rw [sub_mul, one_mul, B.characteristic_sub, h.characteristic_inv_mul]
  have hgroup : h.matrix ∈ gammaSubgroup (B.characteristic x) ↔
      (ε⁻¹ - 1) * x ∈ B.submodule := by
    rw [← B.isIntegralIndex_characteristic_iff, hchar]
    constructor
    · intro hm i
      obtain ⟨m, hi⟩ := ratVecAction_sub_intVec_of_mem_gammaSubgroup hm i
      exact ⟨m, by simpa using hi⟩
    · exact mem_gammaSubgroup_of_isIntegralIndex
  rw [hgroup]
  constructor
  · intro hx
    have hm := h.mul_mem hx
    have heq : ε * ((ε⁻¹ - 1) * x) = -((ε - 1) * x) := by
      field_simp [h.ne_zero]
      ring
    rw [heq] at hm
    exact B.submodule.neg_mem_iff.mp hm
  · intro hx
    have hm := h.inv_mul_mem hx
    have heq : ε⁻¹ * ((ε - 1) * x) = -((ε⁻¹ - 1) * x) := by
      field_simp [h.ne_zero]
      ring
    rw [heq] at hm
    exact B.submodule.neg_mem_iff.mp hm

end IsPeriod

/-! ### The pseudolattice of an attractive fixed point

An attractive fixed point `β = ρ₁(τ)` of `γ`, with `τ ∈ K`, is the fixed point of the
pseudolattice `ℤτ + ℤ` with the period `ε = cτ + d`, whose matrix is `γ`. -/

variable {A : SL(2, ℤ)} {τ : K}

/-- The fixed point equation over the first real embedding gives the pair map over `K`. -/
private theorem isPairMap_of_isAttractiveFixedPoint
    (hA : IsAttractiveFixedPoint A (realEmbeddingAt K F.place τ)) :
    IsPairMap (A : Mat(2, ℤ)) τ (fltDenominator (A : Mat(2, ℤ)) τ) τ := by
  have hfix : flt (A : Mat(2, ℤ)) τ = τ :=
    (realEmbeddingAt K F.place).injective (by
      rw [map_flt]
      exact hA.flt_eq)
  have hden : fltDenominator (A : Mat(2, ℤ)) τ ≠ 0 := by
    intro hz
    have hr := hA.one_lt_fltDenominator
    rw [← map_fltDenominator, hz, map_zero] at hr
    norm_num at hr
  apply IsPairMap.intro
  · have := (div_eq_iff hden).mp hfix
    simpa [flt, fltDenominator, mul_comm] using this
  · rfl

/-- Irrationality at the first place separates the two values of `τ`. -/
private theorem realEmbeddingAt_ne_other_of_isAttractiveFixedPoint
    (hA : IsAttractiveFixedPoint A (realEmbeddingAt K F.place τ)) :
    realEmbeddingAt K F.place τ ≠ realEmbeddingAt K F.otherPlace τ := by
  intro heq
  have htrace := F.add_realEmbeddingAt_otherPlace_eq_trace τ
  rw [← heq] at htrace
  have hrat : realEmbeddingAt K F.place τ = ((Algebra.trace ℚ K τ / 2 : ℚ) : ℝ) := by
    push_cast
    linarith
  exact hA.irrational ⟨_, hrat.symm⟩

/-- **The pseudolattice of an attractive fixed point**: for `γ = (a b; c d)` with attractive fixed
point `β = ρ₁(τ)`, `τ ∈ K`, the basis `(τ, 1)` of `ℤτ + ℤ` is admissible in the sense of
[RW26b, Radchenko, Wheeler (2026b), Section 3]: `β₂ = 1` is totally positive, and `τ' < τ`
because `c(τ - τ') = ε - ε⁻¹ > 0` for `ε = cτ + d > 1`, `c > 0`. -/
def ofAttractiveFixedPoint (hA : IsAttractiveFixedPoint A (realEmbeddingAt K F.place τ)) :
    PseudolatticeBasis F where
  tau := τ
  scale := 1
  other_lt := by
    let ε : K := fltDenominator (A : Mat(2, ℤ)) τ
    have hpair : IsPairMap (A : Mat(2, ℤ)) τ ε τ :=
      isPairMap_of_isAttractiveFixedPoint hA
    have hprod : realEmbeddingAt K F.place ε * realEmbeddingAt K F.otherPlace ε = 1 := by
      have hdet := det_eq_mul_of_fltDenominator_eq
        (realEmbeddingAt_ne_other_of_isAttractiveFixedPoint hA)
        hpair.denominator_eq.symm hpair.first_row.symm
      rw [Matrix.SpecialLinearGroup.det_coe] at hdet
      norm_num at hdet
      exact hdet.symm
    have hfirst : 1 < realEmbeddingAt K F.place ε := by
      simpa [ε, map_fltDenominator] using hA.one_lt_fltDenominator
    have hother : realEmbeddingAt K F.otherPlace ε =
        (realEmbeddingAt K F.place ε)⁻¹ := by
      apply mul_left_cancel₀ (ne_of_gt (zero_lt_one.trans hfirst))
      rw [mul_inv_cancel₀ (ne_of_gt (zero_lt_one.trans hfirst))]
      exact hprod
    have hsecond_lt : realEmbeddingAt K F.otherPlace ε < 1 := by
      rw [hother]
      exact (inv_lt_one₀ (zero_lt_one.trans hfirst)).mpr hfirst
    have hfirst_eq : realEmbeddingAt K F.place ε =
        (A 1 0 : ℝ) * realEmbeddingAt K F.place τ + A 1 1 := by
      simp [ε, fltDenominator]
    have hsecond_eq : realEmbeddingAt K F.otherPlace ε =
        (A 1 0 : ℝ) * realEmbeddingAt K F.otherPlace τ + A 1 1 := by
      simp [ε, fltDenominator]
    have hc : (0 : ℝ) < A 1 0 := by exact_mod_cast hA.lowerLeft_pos
    have hdiff : 0 < (A 1 0 : ℝ) *
        (realEmbeddingAt K F.place τ - realEmbeddingAt K F.otherPlace τ) := by
      nlinarith
    exact sub_pos.mp ((mul_pos_iff_of_pos_left hc).mp hdiff)
  scale_pos := by
    exact ⟨by simp, by simp⟩

/-- **The period of the pseudolattice of an attractive fixed point**: `ε = cτ + d` is a period of
`ℤτ + ℤ` [RW26b, Radchenko, Wheeler (2026b), Section 3]: `ετ = aτ + b` and `ε = cτ + d` lie in
`ℤτ + ℤ`, `N(ε) = det γ = 1`, and `ρ₁(ε) = j_γ(β) > 1`. -/
theorem isPeriod_ofAttractiveFixedPoint
    (hA : IsAttractiveFixedPoint A (realEmbeddingAt K F.place τ)) :
    (ofAttractiveFixedPoint hA).IsPeriod ((A 1 0 : K) * τ + (A 1 1 : K)) := by
  let ε : K := fltDenominator (A : Mat(2, ℤ)) τ
  have hpair : IsPairMap (A : Mat(2, ℤ)) τ ε τ :=
    isPairMap_of_isAttractiveFixedPoint hA
  have hmem : ε ∈ Submodule.span ℤ {τ, 1} := by
    apply Submodule.mem_span_pair.mpr
    exact ⟨A 1 0, A 1 1, by simp [ε, fltDenominator, zsmul_eq_mul]⟩
  have hmul : ε * τ ∈ Submodule.span ℤ {τ, 1} := by
    apply Submodule.mem_span_pair.mpr
    exact ⟨A 0 0, A 0 1, by simpa [zsmul_eq_mul] using hpair.first_row⟩
  have hdet := det_eq_mul_of_fltDenominator_eq
    (realEmbeddingAt_ne_other_of_isAttractiveFixedPoint hA)
    hpair.denominator_eq.symm hpair.first_row.symm
  rw [Matrix.SpecialLinearGroup.det_coe,
    F.mul_realEmbeddingAt_otherPlace_eq_norm] at hdet
  have hnorm : Algebra.norm ℚ ε = 1 := by
    exact_mod_cast hdet.symm
  exact ⟨by simpa [ofAttractiveFixedPoint, ε, fltDenominator] using hmul,
    by simpa [ofAttractiveFixedPoint, ε, fltDenominator] using hmem,
    by simpa [ε, fltDenominator] using hnorm,
    by simpa [ε, map_fltDenominator, fltDenominator] using
      hA.one_lt_fltDenominator⟩

/-- **The period matrix of an attractive fixed point is the matrix itself**: the matrix of
`ε = cτ + d` on the basis `(τ, 1)` is `γ` (`IsPeriod.matrix_eq_of_isPairMap`). -/
theorem matrix_isPeriod_ofAttractiveFixedPoint
    (hA : IsAttractiveFixedPoint A (realEmbeddingAt K F.place τ)) :
    (isPeriod_ofAttractiveFixedPoint hA).matrix = A := by
  exact ((isPeriod_ofAttractiveFixedPoint hA).matrix_eq_of_isPairMap
    (by simpa [ofAttractiveFixedPoint, fltDenominator] using
      isPairMap_of_isAttractiveFixedPoint hA)).symm

end PseudolatticeBasis

/-! ### The finite quantum dilogarithm `E_{I,ε}`

`E_{I,ε}(x) = finiteDilogValue γ β r` at the characteristic `r` of `x`. -/

variable {F : RealQuadraticFieldData K} {B : PseudolatticeBasis F} {ε : K}

/-- **The finite quantum dilogarithm `E_{I,ε}`** of [RW26b, Radchenko, Wheeler (2026b),
Definition 1] on `K` (a function of `x` modulo `I`, meaningful for `(ε - 1)x ∈ I`): for
`x ∉ I`, `E_{I,ε}(x) = μ_γ Φ_{γ,u,0}(x/β₂; τ)` with `(ε⁻¹ - 1)x = uβ₁ + vβ₂`, and
`E_{I,ε}(x) = √ε` for `x ∈ I`; it is `finiteDilogValue` at the period's matrix, the real fixed
point `β = ρ₁(τ)`, and the characteristic of `x`. -/
@[source "RW26b, Definition 1, p. 3 (E_{I,ε})" (symbol := "E_{I,ε}(x)")]
def pseudolatticeDilog (h : B.IsPeriod ε) (x : K) : ℂ :=
  finiteDilogValue h.matrix B.beta (B.characteristic x)

/-- **`E_{I,ε}(x) = √ε` on `I`** [RW26b, Radchenko, Wheeler (2026b), Definition 1]
(`finiteDilogValue_of_isIntegralIndex`, `isIntegralIndex_characteristic_iff`,
`IsPeriod.fltDenominator_matrix`). -/
theorem pseudolatticeDilog_of_mem (h : B.IsPeriod ε) {x : K} (hx : x ∈ B.submodule) :
    pseudolatticeDilog h x = ((Real.sqrt (realEmbeddingAt K F.place ε) : ℝ) : ℂ) := by
  unfold pseudolatticeDilog
  rw [finiteDilogValue_of_isIntegralIndex h.matrix B.beta
    ((B.isIntegralIndex_characteristic_iff x).mpr hx), h.fltDenominator_matrix]

/-- **`E_{I,ε}` is a function on `K/I`**: `E(y) = E(x)` for `x - y ∈ I` and `(ε - 1)x ∈ I`
(`finiteDilogValue_congr`, `characteristic_sub`, `isIntegralIndex_characteristic_iff`); the
well-definedness of [RW26b, Radchenko, Wheeler (2026b), Definition 1]. -/
theorem pseudolatticeDilog_congr (h : B.IsPeriod ε) {x y : K} (hx : (ε - 1) * x ∈ B.submodule)
    (hxy : x - y ∈ B.submodule) : pseudolatticeDilog h y = pseudolatticeDilog h x := by
  have hdiff : IsIntegralIndex (B.characteristic y - B.characteristic x) := by
    have hxy' : IsIntegralIndex (B.characteristic x - B.characteristic y) := by
      rw [← B.characteristic_sub]
      exact (B.isIntegralIndex_characteristic_iff (x - y)).mpr hxy
    simpa [neg_sub] using
      (isIntegralIndex_neg_iff (B.characteristic x - B.characteristic y)).mpr hxy'
  exact finiteDilogValue_congr h.isAttractiveFixedPoint
    ((h.mem_gammaSubgroup_characteristic_iff x).mpr hx) hdiff

/-- `E_{I,ε}(x) ≠ 0` for `(ε - 1)x ∈ I` (`finiteDilogValue_ne_zero`). -/
theorem pseudolatticeDilog_ne_zero (h : B.IsPeriod ε) {x : K} (hx : (ε - 1) * x ∈ B.submodule) :
    pseudolatticeDilog h x ≠ 0 := by
  exact finiteDilogValue_ne_zero h.isAttractiveFixedPoint
    ((h.mem_gammaSubgroup_characteristic_iff x).mpr hx)

/-- **The Gaussian `⟨x⟩ = ⟨x⟩_{I,ε}`** of [RW26b, Radchenko, Wheeler (2026b), equation (2)] as
the theta character `χ_r(γ)` at the characteristic of `x`. The coordinate-free form
`s_I((ε - 1)x) e(½ω_I(x, εx))` of (2) is not formalized. -/
@[source "RW26b, equation (2), p. 3" (symbol := "⟨x⟩_{I,ε}")]
def pseudolatticeGaussian (h : B.IsPeriod ε) (x : K) : ℂ :=
  thetaCharacter (B.characteristic x) (h.matrix : Mat(2, ℤ))

/-- **The reflection law (4) off `I`**: `E(x)E(-x) = ⟨x⟩⁻¹` for `(ε - 1)x ∈ I`, `x ∉ I`
[RW26b, Radchenko, Wheeler (2026b), Proposition 1, equation (4)], from
`finiteDilogValue_mul_valueMinus_neg` with `F⁻ = F` off `ℤ²`
(`finiteDilogValueMinus_of_not_isIntegralIndex`) and `characteristic_neg`. -/
@[source "RW26b, Proposition 1, p. 4 (equation (4), x ∉ I)"]
theorem pseudolatticeDilog_mul_neg (h : B.IsPeriod ε) {x : K} (hx : (ε - 1) * x ∈ B.submodule)
    (hx0 : x ∉ B.submodule) :
    pseudolatticeDilog h x * pseudolatticeDilog h (-x) = (pseudolatticeGaussian h x)⁻¹ := by
  have hr := (h.mem_gammaSubgroup_characteristic_iff x).mpr hx
  have hnot : ¬ IsIntegralIndex (B.characteristic x) := by
    intro hi
    exact hx0 ((B.isIntegralIndex_characteristic_iff x).mp hi)
  have hnotneg : ¬ IsIntegralIndex (-B.characteristic x) := by
    simpa only [isIntegralIndex_neg_iff] using hnot
  have hrefl := finiteDilogValue_mul_valueMinus_neg h.isAttractiveFixedPoint hr
  rw [finiteDilogValueMinus_of_not_isIntegralIndex h.matrix B.beta hnotneg] at hrefl
  simpa only [pseudolatticeDilog, pseudolatticeGaussian, B.characteristic_neg] using hrefl

end SIC

end
