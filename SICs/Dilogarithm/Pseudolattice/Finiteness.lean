/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Dilogarithm.Pseudolattice.Basic

/-!
# Finitely many pseudolattices with a given period up to homothety

For a fixed norm-one unit `ε > 1` of a real quadratic field there is a finite set of
pseudolattices with period `ε` such that every pseudolattice with period `ε` is `αI₀` for one of
them and some `α` positive at the first real place.

This module supplies the finiteness statement at the start of the proof of [RW26b, Radchenko,
Wheeler (2026b), Section 5, Theorem 5] ("there are only finitely many `ε`-stable pseudolattices
up to totally positive homothety"). The source argues with the narrow class group of `𝒪_K` and
the finitely many lattices between `c𝒪_K I` and `𝒪_K I`; the proof here uses Hirzebruch–Jung
reduction instead, which is already formalized, and allows homotheties `α` with `α' < 0`; the
proof of Theorem 5 covers them by the mixed-sign homothety law
(`pseudolatticeDilog_smul_of_pos_of_neg_eq_inv`), which preserves the absolute values of the
Fourier coefficients.

## The argument

Let `I = β₂(ℤτ + ℤ)` have period `ε`. By `RealQuadraticFieldData.exists_flt_reduced` there is
`R = (a b; c d) ∈ SL₂(ℤ)` with `τ₀ = R·τ` reduced, `0 < τ₀' < 1 < τ₀`, and `cτ + d > 0` at the
first place. Then `ℤτ₀ + ℤ = (cτ + d)⁻¹(ℤτ + ℤ)`, so `I = α(ℤτ₀ + ℤ)` with `α = β₂(cτ + d)`
positive at the first place, and `(τ₀, 1)` is an admissible basis with period `ε`. Its matrix
`γ₀ = (a₀ b₀; c₀ d₀)` has `γ₀τ₀ = τ₀`, so `τ₀` is the larger root of the form
`Q = ⟨c₀, d₀ - a₀, -b₀⟩` of discriminant `(Tr γ₀)² - 4 = (Tr ε)² - 4`, with `c₀ > 0`
(`lowerLeft_pos`). The roots `τ₀ > 1 > τ₀' > 0` make `Q` Hirzebruch–Jung reduced
(`isHJReduced_iff_roots`), and there are finitely many such forms (`finite_setOf_isHJReduced`);
`τ₀` is determined by `Q`.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]

/-! ### Finiteness up to homothety -/

/-- The quadratic form fixed by the matrix of a period, used in
`PseudolatticeBasis.exists_finite_homothety`. -/
private def PseudolatticeBasis.IsPeriod.periodForm {F : RealQuadraticFieldData K}
    {B : PseudolatticeBasis F} {ε : K} (h : B.IsPeriod ε) : BinaryQF :=
  ⟨(h.matrix : Mat(2, ℤ)) 1 0,
    (h.matrix : Mat(2, ℤ)) 1 1 - (h.matrix : Mat(2, ℤ)) 0 0,
    -(h.matrix : Mat(2, ℤ)) 0 1⟩

/-- The form of a period has discriminant `(Tr γ)² - 4`; used in
`PseudolatticeBasis.exists_finite_homothety`. -/
private theorem PseudolatticeBasis.IsPeriod.periodForm_disc {F : RealQuadraticFieldData K}
    {B : PseudolatticeBasis F} {ε : K} (h : B.IsPeriod ε) :
    h.periodForm.disc =
      ((h.matrix : Mat(2, ℤ)) 0 0 + (h.matrix : Mat(2, ℤ)) 1 1) ^ 2 - 4 := by
  have hdet := Matrix.SpecialLinearGroup.det_coe h.matrix
  rw [Matrix.det_fin_two] at hdet
  rw [BinaryQF.disc_eq_coefficients]
  dsimp [periodForm]
  nlinarith

/-- A reduced period form has roots `ρ₁(τ)` and `ρ₂(τ)`; used in
`PseudolatticeBasis.exists_finite_homothety`. -/
private theorem PseudolatticeBasis.IsPeriod.periodForm_roots {F : RealQuadraticFieldData K}
    {B : PseudolatticeBasis F} {ε : K} (h : B.IsPeriod ε) :
    h.periodForm.rootPlus = B.beta ∧
      h.periodForm.rootMinus = realEmbeddingAt K F.otherPlace B.tau := by
  let e := realEmbeddingAt K F.place ε
  let c := ((h.matrix : Mat(2, ℤ)) 1 0 : ℝ)
  let a := ((h.matrix : Mat(2, ℤ)) 0 0 : ℝ)
  let d := ((h.matrix : Mat(2, ℤ)) 1 1 : ℝ)
  have he : 1 < e := h.one_lt
  have he0 : e ≠ 0 := ne_of_gt (zero_lt_one.trans he)
  have hc : 0 < c := by
    change (0 : ℝ) < ((h.matrix : Mat(2, ℤ)) 1 0 : ℝ)
    exact_mod_cast h.lowerLeft_pos
  have htr : a + d = e + e⁻¹ := by
    simpa [a, d, e, h.fltDenominator_matrix] using h.isAttractiveFixedPoint.trace_eq
  have hd1 : c * B.beta + d = e := by
    simpa [c, d, e, fltDenominator] using h.fltDenominator_matrix
  have hd2 : c * realEmbeddingAt K F.otherPlace B.tau + d = e⁻¹ := by
    have hden := congrArg (realEmbeddingAt K F.otherPlace)
      h.isPairMap_matrix.denominator_eq
    simpa [c, d, e, map_fltDenominator, fltDenominator, h.other_eq_inv] using hden
  have hdisc : (h.periodForm.disc : ℝ) = (e - e⁻¹) ^ 2 := by
    have hdisc0 : (h.periodForm.disc : ℝ) = (a + d) ^ 2 - 4 := by
      change (h.periodForm.disc : ℝ) =
        (((h.matrix : Mat(2, ℤ)) 0 0 : ℝ) +
          ((h.matrix : Mat(2, ℤ)) 1 1 : ℝ)) ^ 2 - 4
      exact_mod_cast h.periodForm_disc
    rw [hdisc0, htr]
    nlinarith [mul_inv_cancel₀ he0]
  have hnonneg : 0 ≤ e - e⁻¹ := by
    have hi : e⁻¹ < 1 := (inv_lt_one₀ (zero_lt_one.trans he)).mpr he
    linarith
  have hsqrt : Real.sqrt (h.periodForm.disc : ℝ) = e - e⁻¹ := by
    rw [hdisc, Real.sqrt_sq hnonneg]
  constructor
  · rw [BinaryQF.rootPlus, hsqrt]
    simp only [periodForm, Int.cast_sub]
    change (-((d - a : ℝ)) + (e - e⁻¹)) / (2 * c) = B.beta
    apply (div_eq_iff (by positivity : (2 * c) ≠ 0)).2
    nlinarith [htr, hd1]
  · rw [BinaryQF.rootMinus, hsqrt]
    simp only [periodForm, Int.cast_sub]
    change (-((d - a : ℝ)) - (e - e⁻¹)) / (2 * c) =
      realEmbeddingAt K F.otherPlace B.tau
    apply (div_eq_iff (by positivity : (2 * c) ≠ 0)).2
    nlinarith [htr, hd2]

/-- Reduced roots make the form of a period HJ reduced; used in
`PseudolatticeBasis.exists_finite_homothety`. -/
private theorem PseudolatticeBasis.IsPeriod.periodForm_reduced {F : RealQuadraticFieldData K}
    {B : PseudolatticeBasis F} {ε : K} (h : B.IsPeriod ε)
    (hplace : 1 < B.beta)
    (hother : realEmbeddingAt K F.otherPlace B.tau ∈ Set.Ioo 0 1) :
    h.periodForm.IsHJReduced := by
  apply (BinaryQF.isHJReduced_iff_roots h.lowerLeft_pos).2
  rw [h.periodForm_roots.1, h.periodForm_roots.2]
  exact ⟨hother.1, hother.2, hplace⟩

/-- Period forms for one `ε` have the same discriminant; used in
`PseudolatticeBasis.exists_finite_homothety`. -/
private theorem PseudolatticeBasis.IsPeriod.periodForm_disc_eq {F : RealQuadraticFieldData K}
    {B B' : PseudolatticeBasis F} {ε : K} (h : B.IsPeriod ε) (h' : B'.IsPeriod ε) :
    h.periodForm.disc = h'.periodForm.disc := by
  have ht := h.isAttractiveFixedPoint.trace_eq
  have ht' := h'.isAttractiveFixedPoint.trace_eq
  rw [h.fltDenominator_matrix] at ht
  rw [h'.fltDenominator_matrix] at ht'
  have htr : ((h.matrix : Mat(2, ℤ)) 0 0 + (h.matrix : Mat(2, ℤ)) 1 1 : ℤ) =
      (h'.matrix : Mat(2, ℤ)) 0 0 + (h'.matrix : Mat(2, ℤ)) 1 1 := by
    exact_mod_cast ht.trans ht'.symm
  rw [h.periodForm_disc, h'.periodForm_disc, htr]

/-- A period is preserved when the normalized basis changes by `R ∈ SL₂(ℤ)`; used in
`PseudolatticeBasis.exists_reduced_homothety`. -/
private theorem PseudolatticeBasis.IsPeriod.flt {F : RealQuadraticFieldData K}
    {B B₀ : PseudolatticeBasis F} {ε : K} (h : B.IsPeriod ε) (R : SL(2, ℤ))
    (hj : fltDenominator (R : Mat(2, ℤ)) B.tau ≠ 0)
    (hτ : B₀.tau = flt (R : Mat(2, ℤ)) B.tau) : B₀.IsPeriod ε := by
  let j := fltDenominator (R : Mat(2, ℤ)) B.tau
  let τ₀ := SIC.flt (R : Mat(2, ℤ)) B.tau
  have hmul : ∀ x : K, x ∈ Submodule.span ℤ {B.tau, 1} →
      ε * x ∈ Submodule.span ℤ {B.tau, 1} := by
    intro x hx
    obtain ⟨u, v, rfl⟩ := Submodule.mem_span_pair.mp hx
    simpa [zsmul_eq_mul, mul_add, mul_left_comm, mul_comm, mul_assoc] using
      ((Submodule.span ℤ ({B.tau, 1} : Set K)).add_mem
        ((Submodule.span ℤ ({B.tau, 1} : Set K)).smul_mem u h.mul_tau_mem)
        ((Submodule.span ℤ ({B.tau, 1} : Set K)).smul_mem v h.mem))
  have hjtau : j * τ₀ ∈ Submodule.span ℤ {B.tau, 1} :=
    (mem_span_pair_flt_iff R hj τ₀).mp
      (Submodule.subset_span (by simp [τ₀]))
  have hjone : j ∈ Submodule.span ℤ {B.tau, 1} := by
    simpa only [mul_one] using
      (mem_span_pair_flt_iff R hj (1 : K)).mp
        (Submodule.subset_span (by simp))
  refine ⟨?_, ?_, h.norm_one, h.one_lt⟩
  · rw [hτ]
    apply (mem_span_pair_flt_iff R hj (ε * τ₀)).mpr
    simpa only [mul_left_comm, mul_assoc] using hmul (j * τ₀) hjtau
  · rw [hτ]
    apply (mem_span_pair_flt_iff R hj ε).mpr
    simpa only [mul_comm] using hmul j hjone

/-- The lattice of `R·τ` is the original lattice divided by `j_R(τ)`; used in
`PseudolatticeBasis.exists_reduced_homothety`. -/
private theorem PseudolatticeBasis.submodule_flt {F : RealQuadraticFieldData K}
    (B : PseudolatticeBasis F) (R : SL(2, ℤ))
    (hj : fltDenominator (R : Mat(2, ℤ)) B.tau ≠ 0) (y : K) :
    y ∈ B.submodule ↔
      ∃ z ∈ Submodule.span ℤ {flt (R : Mat(2, ℤ)) B.tau, 1},
        y = (B.scale * fltDenominator (R : Mat(2, ℤ)) B.tau) * z := by
  let j := fltDenominator (R : Mat(2, ℤ)) B.tau
  let α := B.scale * j
  have hα : α ≠ 0 := mul_ne_zero B.scale_ne_zero hj
  constructor
  · intro hy
    have hynorm : y / B.scale ∈ Submodule.span ℤ {B.tau, 1} := by
      have hm := (mul_mem_span_pair_iff B.scale_ne_zero B.tau (y / B.scale)).mp
      apply hm
      rw [mul_div_cancel₀ y B.scale_ne_zero]
      exact hy
    let z := y / α
    refine ⟨z, ?_, ?_⟩
    · apply (mem_span_pair_flt_iff R hj z).mpr
      have hz : j * z = y / B.scale := by
        dsimp [z, α]
        field_simp [hj, B.scale_ne_zero]
        exact mul_div_cancel_left₀ y hj
      rw [hz]
      exact hynorm
    · exact (mul_div_cancel₀ y hα).symm
  · rintro ⟨z, hz, rfl⟩
    have hznorm : j * z ∈ Submodule.span ℤ {B.tau, 1} :=
      (mem_span_pair_flt_iff R hj z).mp hz
    have hscaled := (mul_mem_span_pair_iff B.scale_ne_zero B.tau (j * z)).mpr hznorm
    convert hscaled using 1
    · simp only [PseudolatticeBasis.submodule]
    · ring

/-- HJ reduction replaces a period basis by `(τ₀, 1)` and a homothety positive at the first
real place; used in `PseudolatticeBasis.exists_finite_homothety`. -/
private theorem PseudolatticeBasis.exists_reduced_homothety
    (F : RealQuadraticFieldData K) {ε : K} (B : PseudolatticeBasis F) (h : B.IsPeriod ε) :
    ∃ B₀ : PseudolatticeBasis F, B₀.IsPeriod ε ∧ B₀.scale = 1 ∧
      1 < B₀.beta ∧ realEmbeddingAt K F.otherPlace B₀.tau ∈ Set.Ioo 0 1 ∧
        ∃ α : K, 0 < realEmbeddingAt K F.place α ∧
          ∀ y, y ∈ B.submodule ↔ ∃ z ∈ B₀.submodule, y = α * z := by
  obtain ⟨R, hplace, hother, hjreal⟩ := F.exists_flt_reduced B.other_lt.ne
  let τ₀ := flt (R : Mat(2, ℤ)) B.tau
  let j := fltDenominator (R : Mat(2, ℤ)) B.tau
  have hjpos : 0 < realEmbeddingAt K F.place j := by
    simpa only [j, map_fltDenominator, PseudolatticeBasis.beta] using hjreal
  have hj : j ≠ 0 := by
    intro hz
    have := hjpos
    simp [hz] at this
  let B₀ : PseudolatticeBasis F :=
    ⟨τ₀, 1, lt_trans hother.2 hplace, ⟨by simp, by simp⟩⟩
  have h₀ : B₀.IsPeriod ε := h.flt R hj rfl
  let α := B.scale * j
  have hαpos : 0 < realEmbeddingAt K F.place α := by
    change 0 < realEmbeddingAt K F.place (B.scale * j)
    rw [map_mul]
    exact mul_pos B.scale_pos.1 hjpos
  refine ⟨B₀, h₀, rfl, hplace, hother, α, hαpos, ?_⟩
  intro y
  simpa only [B₀, PseudolatticeBasis.submodule, one_mul, α, j, τ₀] using
    B.submodule_flt R hj y

/-- The period form determines a basis with scale one: its larger root determines `τ`; used in
`PseudolatticeBasis.finite_reduced_bases`. -/
private theorem PseudolatticeBasis.periodForm_injective {F : RealQuadraticFieldData K}
    {B B' : PseudolatticeBasis F} {ε : K} (h : B.IsPeriod ε) (h' : B'.IsPeriod ε)
    (hs : B.scale = 1) (hs' : B'.scale = 1) (hQ : h.periodForm = h'.periodForm) :
    B = B' := by
  have hβ : B.beta = B'.beta := by
    rw [← h.periodForm_roots.1, ← h'.periodForm_roots.1, hQ]
  have hτ : B.tau = B'.tau := (realEmbeddingAt K F.place).injective hβ
  have hscale : B.scale = B'.scale := hs.trans hs'.symm
  cases B
  cases B'
  cases hτ
  cases hscale
  rfl

/-- Reduced bases `(τ₀, 1)` with period `ε` inject into the finite set of HJ-reduced forms of
the period discriminant; used in `PseudolatticeBasis.exists_finite_homothety`. -/
private theorem PseudolatticeBasis.finite_reduced_bases
    (F : RealQuadraticFieldData K) (ε : K) :
    {B : PseudolatticeBasis F | B.IsPeriod ε ∧ B.scale = 1 ∧
      1 < B.beta ∧ realEmbeddingAt K F.otherPlace B.tau ∈ Set.Ioo 0 1}.Finite := by
  classical
  let S : Set (PseudolatticeBasis F) :=
    {B | B.IsPeriod ε ∧ B.scale = 1 ∧
      1 < B.beta ∧ realEmbeddingAt K F.otherPlace B.tau ∈ Set.Ioo 0 1}
  change S.Finite
  by_cases hS : ∃ B : PseudolatticeBasis F, B ∈ S
  · obtain ⟨B₀, hB₀⟩ := hS
    have hfinQ := BinaryQF.finite_setOf_isHJReduced (hB₀.1.periodForm.disc)
    let f : S → {Q : BinaryQF | Q.disc = hB₀.1.periodForm.disc ∧ Q.IsHJReduced} :=
      fun B => ⟨B.property.1.periodForm,
        ⟨B.property.1.periodForm_disc_eq hB₀.1,
          B.property.1.periodForm_reduced B.property.2.2.1 B.property.2.2.2⟩⟩
    apply Set.finite_coe_iff.mp
    apply @Finite.of_injective S _ (Set.finite_coe_iff.mpr hfinQ) f
    rintro ⟨B, hB⟩ ⟨B', hB'⟩ heq
    exact Subtype.ext (PseudolatticeBasis.periodForm_injective hB.1 hB'.1 hB.2.1 hB'.2.1
      (congrArg Subtype.val heq))
  · have hempty : S = ∅ := by
      ext B
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hB
      exact hS ⟨B, hB⟩
    simpa only [hempty] using Set.finite_empty

/-- **Finitely many pseudolattices with period `ε` up to homothety**, the finiteness at the start
of the proof of [RW26b, Radchenko, Wheeler (2026b), Section 5, Theorem 5], with homotheties `α`
positive at the first real place: a finite set `S` of admissible bases with period `ε` such that
every pseudolattice with period `ε` is `α I₀` for some `I₀` presented by `S`. -/
theorem PseudolatticeBasis.exists_finite_homothety (F : RealQuadraticFieldData K) (ε : K) :
    ∃ S : Set (PseudolatticeBasis F), S.Finite ∧ (∀ B₀ ∈ S, B₀.IsPeriod ε) ∧
      ∀ B : PseudolatticeBasis F, B.IsPeriod ε → ∃ B₀ ∈ S, ∃ α : K,
        0 < realEmbeddingAt K F.place α ∧
          ∀ y, y ∈ B.submodule ↔ ∃ z ∈ B₀.submodule, y = α * z := by
  let S : Set (PseudolatticeBasis F) :=
    {B | B.IsPeriod ε ∧ B.scale = 1 ∧
      1 < B.beta ∧ realEmbeddingAt K F.otherPlace B.tau ∈ Set.Ioo 0 1}
  refine ⟨S, PseudolatticeBasis.finite_reduced_bases F ε, ?_, ?_⟩
  · intro B₀ hB₀
    exact hB₀.1
  · intro B h
    obtain ⟨B₀, h₀, hs, hplace, hother, α, hαpos, hiff⟩ :=
      PseudolatticeBasis.exists_reduced_homothety F B h
    exact ⟨B₀, ⟨h₀, hs, hplace, hother⟩, α, hαpos, hiff⟩

end SIC

end
