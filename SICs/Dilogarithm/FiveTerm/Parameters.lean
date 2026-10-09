/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Dilogarithm.FaddeevWord
import SICs.SpecialFunctions.Faddeev.FiveTerm.ParameterDomain
import SICs.SpecialFunctions.Faddeev.WordFiveTerm.Kernel

/-!
# Source parameters of the finite five-term relation

The standing hypotheses on a letter word at an attractive fixed point, the source arguments
`z_u = (u₁τ+u₂)/(ε⁻¹-1)` of integer pairs `u`, their lattice index
`S(u) = (1-d)u₁ + cu₂`, their residues in the finite group `G`, the exact convergence rates and
right source-pole position of the five-term integral at these arguments, and the identification
of the continued word product at `z_u` with the finite dilogarithm, including the ordinary
product off the zero residue class.

This module follows [RW26, Radchenko, Wheeler (2026), equation (2), `eq:fgam.def`, and
Section 3.2, the parameter substitutions in the proof of Theorem 2, `thm:fg.equs`] for
`γ = (a b; c d)` at an attractive fixed point `τ`, `ε = j_γ(τ) = cτ+d`, `N = a+d-2`. The source
uses `p = v₁` and `ℓ = u₁+1`. The principal case is proved directly in
`SICs.Principal.Dilogarithm.Faddeev.FiveTerm.FiniteParameters` and `.FiniteCharacteristics`,
whose index is `S/d`.

## The argument

Since `cτ - ε = -d`, `cz_u/ε + u₁ = -S(u)/(ε-1)`. This single identity gives the upper rate
`λ = 1 - S(u)/(ε-1)` at `w = z_u`, `ℓ = u₁+1`, and the lower rate
`μ = -(S(u)+S(v))/(ε-1)` at `y = z_v`, `p = v₁`. The unit equation `ε + ε⁻¹ = N+2` shows
that `S(u) < N` implies `ε⁻¹ < λ`, while `μ < 0` is `0 < S(u)+S(v)`. The right source pole is
`β_v = (ε-1)S(v)/(cN)`.

The residue of `u` is the lattice characteristic of `(-u₂,u₁)`; its kernel is the row lattice
`ℤ²(γ-I)`, spanned by `(a-1,b)` and `(c,d-1)`, on which `S` takes the values `N` and `0`. Its
rational lift `r` satisfies `(γ-I)r = (-u₂,u₁)`, so `n_QP(r,γ) = -u₁` and, at the fixed point,
`⟨⟨r,τ⟩⟩ = z_u`. The source relation `z_u/ε-z_u=u₁τ+u₂` also gives the exponential identity
needed by the telescoping sum. The word-product values of `SICs.Dilogarithm.FaddeevWord` give
`μ_γ Φ^cont_{γ,u₁,0}(z_u;τ) = E(x)` off the zero class; on it, the type rule gives `E(0)` or
`F⁻(0)` according to the sign of `S(u)`, since there `-S(u)/N` is the diagonal index of the type
rule.
-/

noncomputable section

open Complex
open scoped MatrixGroups

namespace SIC

/-! ### Letter words at attractive fixed points -/

/-- The standing hypotheses of the letter-word finite five-term relation: a nonempty letter word
`γ = ∏_j T^{b_j}S` whose letters after the first are at least `2`, at an attractive fixed point
`τ` ([RW26, Radchenko, Wheeler (2026), Section 1]). -/
structure IsLetterWordFixedPoint (bs : List ℤ) (τ : ℝ) : Prop where
  /-- The word is nonempty. -/
  ne_nil : bs ≠ []
  /-- The letters after the first are at least `2`. -/
  two_le : ∀ b ∈ bs.tail, 2 ≤ b
  /-- `τ` is an attractive fixed point of the word. -/
  fixedPoint : IsAttractiveFixedPoint (letterWord bs) τ

/-- At an attractive fixed point of a letter word, all word periods and their Jacobi denominators
are positive. -/
theorem IsLetterWordFixedPoint.periodsPos {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) : FaddeevWordPeriodsPos bs τ := by
  intro w hw
  have hpos := WordSigmaSVisits.period_pos τ h.fixedPoint.irrational
    (letterWord_lowerLeft_nonneg h.two_le) h.fixedPoint.fltDenominator_pos
    (wordSigmaSVisits_letterWord h.ne_nil h.two_le w hw)
  exact ⟨hpos.2, hpos.1⟩

/-! ### Source arguments, lattice index, and residues -/

/-- The source argument `z_u = (u₁τ+u₂)/(ε⁻¹-1)`, `ε = j_γ(τ)`, of an integer pair `u`, from
[RW26, Radchenko, Wheeler (2026), equation (2), `eq:fgam.def`]. -/
def fiveTermLatticeArgument (γ : SL(2, ℤ)) (τ : ℝ) (u₁ u₂ : ℤ) : ℝ :=
  ((u₁ : ℝ) * τ + u₂) / ((fltDenominator (γ : Mat(2, ℤ)) τ)⁻¹ - 1)

/-- The lattice index `S(u) = (1-d)u₁ + cu₂` of an integer pair for `γ = (a b; c d)`; the
convergence rates of the five-term integral at source arguments are `-S/(ε-1)` up to `1`. -/
def fiveTermLatticeIndex (γ : SL(2, ℤ)) (u₁ u₂ : ℤ) : ℤ :=
  (1 - γ 1 1) * u₁ + γ 1 0 * u₂

/-- The residue in `G` of the source pair `(u₁,u₂)`: the lattice characteristic of `(-u₂,u₁)`,
as in [RW26, Radchenko, Wheeler (2026), equation (2), `eq:fgam.def`, and Section 3.2]. -/
abbrev fiveTermCharacteristicResidue (γ : SL(2, ℤ)) (u₁ u₂ : ℤ) :
    Fin 2 → ZMod (finiteDilogOrder γ) :=
  latticeCharacteristic γ (finiteDilogOrder γ) ![-u₂, u₁]

/-- The rational characteristic `-adj(γ-I)(-u₂,u₁)/N` lifting the residue of `(u₁,u₂)`. -/
def fiveTermRationalCharacteristic (γ : SL(2, ℤ)) (u₁ u₂ : ℤ) : Fin 2 → ℚ :=
  latticeCharacteristicLift γ (finiteDilogOrder γ) ![-u₂, u₁]

/-- The second coordinate of the source lift, used in the zero-class type rule. -/
private theorem fiveTermRationalCharacteristic_snd (γ : SL(2, ℤ)) (u₁ u₂ : ℤ) :
    fiveTermRationalCharacteristic γ u₁ u₂ 1 =
      (↑(-γ 1 0 * u₂ - (γ 0 0 - 1) * u₁) : ℚ) /
        (finiteDilogOrder γ : ℚ) := by
  simp [fiveTermRationalCharacteristic, latticeCharacteristicLift,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.adjugate_fin_two]
  ring

/-- The source argument is additive in the pair. -/
theorem fiveTermLatticeArgument_add (γ : SL(2, ℤ)) (τ : ℝ) (u₁ u₂ v₁ v₂ : ℤ) :
    fiveTermLatticeArgument γ τ (u₁ + v₁) (u₂ + v₂) =
      fiveTermLatticeArgument γ τ u₁ u₂ + fiveTermLatticeArgument γ τ v₁ v₂ := by
  unfold fiveTermLatticeArgument
  push_cast
  ring

/-- The lattice index is additive in the pair. -/
theorem fiveTermLatticeIndex_add (γ : SL(2, ℤ)) (u₁ u₂ v₁ v₂ : ℤ) :
    fiveTermLatticeIndex γ (u₁ + v₁) (u₂ + v₂) =
      fiveTermLatticeIndex γ u₁ u₂ + fiveTermLatticeIndex γ v₁ v₂ := by
  unfold fiveTermLatticeIndex
  ring

/-- The residue is additive in the pair. -/
theorem fiveTermCharacteristicResidue_add (γ : SL(2, ℤ)) (u₁ u₂ v₁ v₂ : ℤ) :
    fiveTermCharacteristicResidue γ (u₁ + v₁) (u₂ + v₂) =
      fiveTermCharacteristicResidue γ u₁ u₂ + fiveTermCharacteristicResidue γ v₁ v₂ := by
  funext i
  fin_cases i <;>
    simp [fiveTermCharacteristicResidue, latticeCharacteristic, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, Matrix.adjugate_fin_two]
  all_goals ring

/-- The residue and its rational lift satisfy the fixed-group and integrality conditions. -/
private theorem fiveTermResidue_liftData {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (u₁ u₂ : ℤ) :
    fiveTermCharacteristicResidue γ u₁ u₂ ∈ finiteDilogGroup γ ∧
      IsIntegralIndex
        (zmodCharacteristic (finiteDilogOrder γ) (fiveTermCharacteristicResidue γ u₁ u₂) -
          fiveTermRationalCharacteristic γ u₁ u₂) := by
  let _ : NeZero (finiteDilogOrder γ) := finiteDilogOrder_neZero h
  exact ⟨latticeCharacteristic_mem γ (finiteDilogOrder γ) ![-u₂, u₁]
      (det_sub_one_eq_neg_finiteDilogOrder h),
    isIntegralIndex_latticeCharacteristic_sub_lift γ (finiteDilogOrder γ) ![-u₂, u₁]⟩

/-- Every residue lies in the finite group `G`. -/
theorem fiveTermCharacteristicResidue_mem {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (u₁ u₂ : ℤ) :
    fiveTermCharacteristicResidue γ u₁ u₂ ∈ finiteDilogGroup γ := by
  exact (fiveTermResidue_liftData h u₁ u₂).1

/-- Every class of `G` is the residue of a source pair. -/
theorem exists_fiveTermCharacteristicResidue_eq {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) {x : Fin 2 → ZMod (finiteDilogOrder γ)}
    (hx : x ∈ finiteDilogGroup γ) :
    ∃ u₁ u₂ : ℤ, fiveTermCharacteristicResidue γ u₁ u₂ = x := by
  obtain ⟨k, hk⟩ := exists_latticeCharacteristic_eq_of_mem h hx
  refine ⟨k 1, -k 0, ?_⟩
  simpa only [fiveTermCharacteristicResidue, neg_neg,
    show ![k 0, k 1] = k by funext i; fin_cases i <;> simp] using hk

/-- A source pair has zero residue exactly when it lies in the row lattice `ℤ²(γ-I)`, spanned by
`(a-1,b)` and `(c,d-1)`. -/
theorem fiveTermCharacteristicResidue_eq_zero_iff {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (u₁ u₂ : ℤ) :
    fiveTermCharacteristicResidue γ u₁ u₂ = 0 ↔
      ∃ s t : ℤ, u₁ = s * (γ 0 0 - 1) + t * γ 1 0 ∧ u₂ = s * γ 0 1 + t * (γ 1 1 - 1) := by
  let _ : NeZero (finiteDilogOrder γ) := finiteDilogOrder_neZero h
  exact (latticeCharacteristic_eq_zero_iff γ (finiteDilogOrder γ)
    (det_sub_one_eq_neg_finiteDilogOrder h) ![-u₂, u₁]).trans
      (sourcePair_mem_rowLattice_iff γ u₁ u₂)

/-- The first row `(a-1,b)` of `γ-I` has lattice index `N`. -/
theorem fiveTermLatticeIndex_firstRow {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) :
    fiveTermLatticeIndex γ (γ 0 0 - 1) (γ 0 1) = finiteDilogOrder γ := by
  have hdet : (γ : Mat(2, ℤ)).det = 1 := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at hdet
  rw [fiveTermLatticeIndex, cast_finiteDilogOrder h]
  nlinarith

/-- The second row `(c,d-1)` of `γ-I` has lattice index `0`. -/
private theorem fiveTermLatticeIndex_secondRow (γ : SL(2, ℤ)) :
    fiveTermLatticeIndex γ (γ 1 0) (γ 1 1 - 1) = 0 := by
  simp only [fiveTermLatticeIndex]
  ring

/-- The row-lattice pair `s(a-1,b)+t(c,d-1)` has index `sN`. -/
theorem fiveTermLatticeIndex_rows {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (s t : ℤ) :
    fiveTermLatticeIndex γ (s * (γ 0 0 - 1) + t * γ 1 0)
      (s * γ 0 1 + t * (γ 1 1 - 1)) = s * finiteDilogOrder γ := by
  calc
    _ = s * fiveTermLatticeIndex γ (γ 0 0 - 1) (γ 0 1) +
        t * fiveTermLatticeIndex γ (γ 1 0) (γ 1 1 - 1) := by
          simp only [fiveTermLatticeIndex]
          ring
    _ = _ := by rw [fiveTermLatticeIndex_firstRow h, fiveTermLatticeIndex_secondRow]; ring

/-- A zero residue has lattice index divisible by the group order `N`. -/
theorem fiveTermLatticeIndex_dvd_of_residue_zero {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (u₁ u₂ : ℤ)
    (hz : fiveTermCharacteristicResidue γ u₁ u₂ = 0) :
    (finiteDilogOrder γ : ℤ) ∣ fiveTermLatticeIndex γ u₁ u₂ := by
  obtain ⟨s, t, rfl, rfl⟩ :=
    (fiveTermCharacteristicResidue_eq_zero_iff h u₁ u₂).1 hz
  exact ⟨s, by simpa only [mul_comm] using fiveTermLatticeIndex_rows h s t⟩

/-! ### Rates and pole positions at source arguments -/

/-- The source argument satisfies `z_u/ε - z_u = u₁τ + u₂`. -/
theorem fiveTermLatticeArgument_div_sub_self {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (u₁ u₂ : ℤ) :
    fiveTermLatticeArgument γ τ u₁ u₂ / fltDenominator (γ : Mat(2, ℤ)) τ -
        fiveTermLatticeArgument γ τ u₁ u₂ = u₁ * τ + u₂ := by
  have hε : 1 < fltDenominator (γ : Mat(2, ℤ)) τ := h.one_lt_fltDenominator
  have hε0 : fltDenominator (γ : Mat(2, ℤ)) τ ≠ 0 := ne_of_gt (by linarith)
  have hden : (fltDenominator (γ : Mat(2, ℤ)) τ)⁻¹ - 1 ≠ 0 := by
    have : (fltDenominator (γ : Mat(2, ℤ)) τ)⁻¹ < 1 :=
      (inv_lt_one₀ (by linarith)).2 hε
    linarith
  unfold fiveTermLatticeArgument
  field_simp
  have : 1 - fltDenominator (γ : Mat(2, ℤ)) τ ≠ 0 := by linarith
  field_simp

/-- A source argument obeys `e(z_u/ε) = e(z_u+u₁τ)`. -/
theorem fiveTermLatticeArgument_exp_div {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (u₁ u₂ : ℤ) :
    Complex.exp (2 * Real.pi * I *
        ((fiveTermLatticeArgument γ τ u₁ u₂ : ℂ) /
          fltDenominator (γ : Mat(2, ℤ)) (τ : ℂ))) =
      Complex.exp (2 * Real.pi * I *
        ((fiveTermLatticeArgument γ τ u₁ u₂ : ℂ) + u₁ * (τ : ℂ))) := by
  have hz := fiveTermLatticeArgument_div_sub_self h u₁ u₂
  have hzC : (fiveTermLatticeArgument γ τ u₁ u₂ : ℂ) /
        fltDenominator (γ : Mat(2, ℤ)) (τ : ℂ) -
      (fiveTermLatticeArgument γ τ u₁ u₂ : ℂ) =
        (u₁ : ℂ) * (τ : ℂ) + u₂ := by
    exact_mod_cast hz
  apply exp_two_pi_I_eq_of_sub_intCast _ _ u₂
  linear_combination hzC

/-- Rewrites a source argument with denominator `ε-1`; used by the rate identity. -/
theorem fiveTermLatticeArgument_eq {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (u₁ u₂ : ℤ) :
    fiveTermLatticeArgument γ τ u₁ u₂ =
      -(fltDenominator (γ : Mat(2, ℤ)) τ * ((u₁ : ℝ) * τ + u₂)) /
        (fltDenominator (γ : Mat(2, ℤ)) τ - 1) := by
  have hε : 1 < fltDenominator (γ : Mat(2, ℤ)) τ := h.one_lt_fltDenominator
  have hε0 : fltDenominator (γ : Mat(2, ℤ)) τ ≠ 0 := ne_of_gt (by linarith)
  have hε1 : fltDenominator (γ : Mat(2, ℤ)) τ - 1 ≠ 0 := ne_of_gt (by linarith)
  have hinv : (fltDenominator (γ : Mat(2, ℤ)) τ)⁻¹ - 1 =
      -(fltDenominator (γ : Mat(2, ℤ)) τ - 1) /
        fltDenominator (γ : Mat(2, ℤ)) τ := by
    field_simp
    ring
  rw [fiveTermLatticeArgument, hinv]
  field_simp

/-- The rate identity `cz_u/ε + u₁ = -S(u)/(ε-1)` used by the source parameter tests. -/
private theorem fiveTermLatticeArgument_baseRate {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (u₁ u₂ : ℤ) :
    (γ 1 0 : ℝ) * fiveTermLatticeArgument γ τ u₁ u₂ /
        fltDenominator (γ : Mat(2, ℤ)) τ + u₁ =
      -(fiveTermLatticeIndex γ u₁ u₂ : ℝ) /
        (fltDenominator (γ : Mat(2, ℤ)) τ - 1) := by
  have hε : 1 < fltDenominator (γ : Mat(2, ℤ)) τ := h.one_lt_fltDenominator
  have hε0 : fltDenominator (γ : Mat(2, ℤ)) τ ≠ 0 := ne_of_gt (by linarith)
  have hε1 : fltDenominator (γ : Mat(2, ℤ)) τ - 1 ≠ 0 := ne_of_gt (by linarith)
  have hlin : (γ 1 0 : ℝ) * τ + γ 1 1 =
      fltDenominator (γ : Mat(2, ℤ)) τ := rfl
  rw [fiveTermLatticeArgument_eq h]
  simp only [fiveTermLatticeIndex]
  push_cast
  field_simp [hε0, hε1]
  linear_combination -(u₁ : ℝ) * hlin

/-- At `w = z_u` and `ℓ = u₁+1`, the upper rate is `λ = 1 - S(u)/(ε-1)`. -/
theorem fiveTermUpperRate_latticeArgument {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (u₁ u₂ : ℤ) :
    fiveTermUpperRate γ (u₁ + 1) (fiveTermLatticeArgument γ τ u₁ u₂) τ =
      1 - fiveTermLatticeIndex γ u₁ u₂ / (fltDenominator (γ : Mat(2, ℤ)) τ - 1) := by
  have hbase := fiveTermLatticeArgument_baseRate h u₁ u₂
  calc
    fiveTermUpperRate γ (u₁ + 1) (fiveTermLatticeArgument γ τ u₁ u₂) τ =
        ((γ 1 0 : ℝ) * fiveTermLatticeArgument γ τ u₁ u₂ /
          fltDenominator (γ : Mat(2, ℤ)) τ + u₁) + 1 := by
          simp only [fiveTermUpperRate, Int.cast_add, Int.cast_one]
          ring
    _ = _ := by rw [hbase]; ring

/-- At `w = z_u`, `ℓ = u₁+1`, `y = z_v`, `p = v₁`, the lower rate is
`μ = -(S(u)+S(v))/(ε-1)`. -/
private theorem fiveTermLowerRate_latticeArgument {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (u₁ u₂ v₁ v₂ : ℤ) :
    fiveTermLowerRate γ (u₁ + 1) v₁ (fiveTermLatticeArgument γ τ u₁ u₂)
        (fiveTermLatticeArgument γ τ v₁ v₂) τ =
      -((fiveTermLatticeIndex γ u₁ u₂ + fiveTermLatticeIndex γ v₁ v₂ : ℤ) : ℝ) /
        (fltDenominator (γ : Mat(2, ℤ)) τ - 1) := by
  have hu := fiveTermLatticeArgument_baseRate h u₁ u₂
  have hv := fiveTermLatticeArgument_baseRate h v₁ v₂
  simp only [fiveTermLowerRate]
  push_cast
  ring_nf at hu hv ⊢
  linarith

/-- The strict lower convergence condition at source arguments is `0 < S(u) + S(v)`. -/
theorem fiveTermLowerRate_latticeArgument_neg_iff {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (u₁ u₂ v₁ v₂ : ℤ) :
    fiveTermLowerRate γ (u₁ + 1) v₁ (fiveTermLatticeArgument γ τ u₁ u₂)
        (fiveTermLatticeArgument γ τ v₁ v₂) τ < 0 ↔
      0 < fiveTermLatticeIndex γ u₁ u₂ + fiveTermLatticeIndex γ v₁ v₂ := by
  rw [fiveTermLowerRate_latticeArgument h, neg_div]
  have hden : 0 < fltDenominator (γ : Mat(2, ℤ)) τ - 1 := by
    linarith [h.one_lt_fltDenominator]
  constructor
  · intro hr
    have hdiv : 0 <
        ((fiveTermLatticeIndex γ u₁ u₂ + fiveTermLatticeIndex γ v₁ v₂ : ℤ) : ℝ) /
          (fltDenominator (γ : Mat(2, ℤ)) τ - 1) := by linarith
    have hs : 0 <
        ((fiveTermLatticeIndex γ u₁ u₂ + fiveTermLatticeIndex γ v₁ v₂ : ℤ) : ℝ) := by
      have := (lt_div_iff₀ hden).mp hdiv
      nlinarith
    exact_mod_cast hs
  · intro hs
    have hs' : 0 <
        ((fiveTermLatticeIndex γ u₁ u₂ + fiveTermLatticeIndex γ v₁ v₂ : ℤ) : ℝ) := by
      exact_mod_cast hs
    have hdiv : 0 <
        ((fiveTermLatticeIndex γ u₁ u₂ + fiveTermLatticeIndex γ v₁ v₂ : ℤ) : ℝ) /
          (fltDenominator (γ : Mat(2, ℤ)) τ - 1) :=
      (lt_div_iff₀ hden).mpr (by nlinarith)
    linarith

/-- The right source pole is `β_v=(ε-1)S(v)/(cN)`. For the crossed-pole position. -/
theorem fiveTermLatticeArgument_beta_eq {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (v₁ v₂ : ℤ) :
    -((v₁ : ℝ) * fltDenominator (γ : Mat(2, ℤ)) τ /
        (γ 1 0 : ℝ) + fiveTermLatticeArgument (γ) τ v₁ v₂) =
      (fltDenominator (γ : Mat(2, ℤ)) τ - 1) *
        (fiveTermLatticeIndex (γ) v₁ v₂ : ℝ) /
          ((γ 1 0 : ℝ) * (finiteDilogOrder (γ) : ℝ)) := by
  let ε : ℝ := fltDenominator (γ : Mat(2, ℤ)) τ
  let c : ℝ := γ 1 0
  let N : ℝ := finiteDilogOrder (γ)
  let S : ℤ := fiveTermLatticeIndex (γ) v₁ v₂
  let y := fiveTermLatticeArgument (γ) τ v₁ v₂
  have hc : 0 < c := by dsimp [c]; exact_mod_cast h.lowerLeft_pos
  have hN : 0 < N := by dsimp [N]; exact_mod_cast finiteDilogOrder_pos h
  have hε : 0 < ε - 1 := sub_pos.mpr h.one_lt_fltDenominator
  have hε0 : ε ≠ 0 := h.fltDenominator_pos.ne'
  have he : ε - 1 ≠ 0 := hε.ne'
  have hq : (ε - 1) ^ 2 = N * ε := by
    have hcast := cast_finiteDilogOrder_eq h
    have hinv := mul_inv_cancel₀ hε0
    dsimp [N, ε] at *
    rw [hcast]
    nlinarith
  have harg : y = -(ε * ((v₁ : ℝ) * τ + v₂)) / (ε - 1) :=
    fiveTermLatticeArgument_eq h v₁ v₂
  have hεdef : ε = c * τ + (γ 1 1 : ℝ) := rfl
  have hSdef : (S : ℝ) =
      (1 - (γ 1 1 : ℝ)) * v₁ + c * v₂ := by
    dsimp [S, c, fiveTermLatticeIndex]
    push_cast
    ring
  have hβ' : -((v₁ : ℝ) * ε / c + y) = ε * (S : ℝ) / (c * (ε - 1)) := by
    rw [harg, hSdef]
    field_simp [hc.ne', he]
    linear_combination -(v₁ : ℝ) * hεdef
  change -((v₁ : ℝ) * ε / c + y) = (ε - 1) * (S : ℝ) / (c * N)
  rw [hβ']
  apply (div_eq_div_iff (mul_ne_zero hc.ne' he) (mul_ne_zero hc.ne' hN.ne')).2
  nlinarith [congrArg (fun t : ℝ => t * (S : ℝ)) hq]

/-- The positive source indices give the upper and lower convergence rates for the residue
sum. For convergence of the residue sum. -/
theorem fiveTermLatticeArgument_source_rates {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (u₁ u₂ v₁ v₂ : ℤ)
    (hu : fiveTermLatticeIndex (γ) u₁ u₂ < finiteDilogOrder (γ))
    (huv : 0 < fiveTermLatticeIndex (γ) u₁ u₂ +
      fiveTermLatticeIndex (γ) v₁ v₂) :
    (fltDenominator (γ : Mat(2, ℤ)) τ)⁻¹ <
      fiveTermUpperRate (γ) (u₁ + 1)
        (fiveTermLatticeArgument (γ) τ u₁ u₂) τ ∧
    fiveTermLowerRate (γ) (u₁ + 1) v₁
      (fiveTermLatticeArgument (γ) τ u₁ u₂)
      (fiveTermLatticeArgument (γ) τ v₁ v₂) τ < 0 := by
  let ε := fltDenominator (γ : Mat(2, ℤ)) τ
  let N : ℝ := finiteDilogOrder (γ)
  let S : ℤ := fiveTermLatticeIndex (γ) u₁ u₂
  have hεpos : 0 < ε := h.fltDenominator_pos
  have hepos : 0 < ε - 1 := sub_pos.mpr h.one_lt_fltDenominator
  have hS : (S : ℝ) < N := by
    dsimp [S, N]
    exact_mod_cast hu
  have hq : (ε - 1) ^ 2 = N * ε := by
    have hcast := cast_finiteDilogOrder_eq h
    have hinv := mul_inv_cancel₀ hεpos.ne'
    dsimp [N, ε] at *
    rw [hcast]
    nlinarith
  have hfrac : (S : ℝ) / (ε - 1) < (ε - 1) / ε := by
    apply (div_lt_div_iff₀ hepos hεpos).2
    nlinarith [mul_lt_mul_of_pos_right hS hεpos]
  have hinv : ε⁻¹ = 1 - (ε - 1) / ε := by
    field_simp
    ring
  constructor
  · rw [fiveTermUpperRate_latticeArgument h]
    change ε⁻¹ < 1 - (S : ℝ) / (ε - 1)
    linarith
  · exact (fiveTermLowerRate_latticeArgument_neg_iff h u₁ u₂ v₁ v₂).2 huv

/-! ### The characteristic dictionary -/

/-- The source lift obeys `(γ-I)r=(-u₂,u₁)`; used by the characteristic dictionary. -/
private theorem ratVecAction_fiveTermRationalCharacteristic_sub {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (u₁ u₂ : ℤ) :
    ratVecAction (γ : Mat(2, ℤ)) (fiveTermRationalCharacteristic γ u₁ u₂) -
      fiveTermRationalCharacteristic γ u₁ u₂ = fun i => (![(-u₂ : ℤ), u₁] i : ℚ) := by
  exact @ratVecAction_latticeCharacteristicLift_sub γ (finiteDilogOrder γ)
    (finiteDilogOrder_neZero h) (det_sub_one_eq_neg_finiteDilogOrder h) ![-u₂, u₁]

/-- The second row of `(γ-I)r_u=(-u₂,u₁)` determines the first source coordinate;
used by `fiveTermResiduePhase_eq_bicharacter`. -/
theorem fiveTermRationalCharacteristic_second {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (u₁ u₂ : ℤ) :
    (u₁ : ℂ) = (γ 1 0 : ℂ) *
        (fiveTermRationalCharacteristic γ u₁ u₂ 0 : ℂ) +
      ((γ 1 1 : ℂ) - 1) *
        (fiveTermRationalCharacteristic γ u₁ u₂ 1 : ℂ) := by
  have hrow := ratVecAction_fiveTermRationalCharacteristic_sub h u₁ u₂
  have heq := congrFun hrow 1
  simp only [Pi.sub_apply, ratVecAction, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.map_apply] at heq
  have hq : (u₁ : ℚ) = (γ 1 0 : ℚ) *
      fiveTermRationalCharacteristic γ u₁ u₂ 0 +
      ((γ 1 1 : ℚ) - 1) * fiveTermRationalCharacteristic γ u₁ u₂ 1 := by
    linear_combination -heq
  exact_mod_cast hq

/-- The coefficient of `τ` in a source argument is `-v₁-S(v)/N`. -/
theorem fiveTermRationalCharacteristic_snd_eq {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (v₁ v₂ : ℤ) :
    fiveTermRationalCharacteristic γ v₁ v₂ 1 =
      -(v₁ : ℚ) - (fiveTermLatticeIndex γ v₁ v₂ : ℚ) /
        (finiteDilogOrder γ : ℚ) := by
  have hN : (finiteDilogOrder γ : ℚ) =
      (γ 0 0 : ℚ) + γ 1 1 - 2 := by
    exact_mod_cast cast_finiteDilogOrder h
  have hN0 : (finiteDilogOrder γ : ℚ) ≠ 0 := by
    exact_mod_cast (finiteDilogOrder_pos h).ne'
  rw [fiveTermRationalCharacteristic_snd]
  simp only [fiveTermLatticeIndex]
  push_cast
  field_simp [hN0]
  linear_combination (v₁ : ℚ) * hN

/-- The divisor combination of source coordinates is `S(v)/N`. -/
theorem fiveTermRationalCharacteristic_row_eq {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (v₁ v₂ : ℤ) :
    -(γ 1 0 : ℚ) * fiveTermRationalCharacteristic γ v₁ v₂ 0 -
      (γ 1 1 : ℚ) * fiveTermRationalCharacteristic γ v₁ v₂ 1 =
        (fiveTermLatticeIndex γ v₁ v₂ : ℚ) / (finiteDilogOrder γ : ℚ) := by
  have hrow := fiveTermRationalCharacteristic_second h v₁ v₂
  have hrowQ : (v₁ : ℚ) = (γ 1 0 : ℚ) *
      fiveTermRationalCharacteristic γ v₁ v₂ 0 +
        ((γ 1 1 : ℚ) - 1) * fiveTermRationalCharacteristic γ v₁ v₂ 1 := by
    exact_mod_cast hrow
  rw [fiveTermRationalCharacteristic_snd_eq h v₁ v₂] at hrowQ ⊢
  linear_combination hrowQ

/-- The canonical residue lift and the source lift differ by an integer vector. -/
private theorem isIntegralIndex_fiveTermCharacteristicResidue_sub_lift {γ : SL(2, ℤ)}
    {τ : ℝ} (h : IsAttractiveFixedPoint γ τ) (u₁ u₂ : ℤ) :
    IsIntegralIndex
      (zmodCharacteristic (finiteDilogOrder γ) (fiveTermCharacteristicResidue γ u₁ u₂) -
        fiveTermRationalCharacteristic γ u₁ u₂) := by
  exact (fiveTermResidue_liftData h u₁ u₂).2

/-- At the fixed point, the symplectic argument of the rational lift of `(u₁,u₂)` is the source
argument `z_u`. -/
theorem fracSymplecticFormRat_fiveTermRationalCharacteristic {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (u₁ u₂ : ℤ) :
    fracSymplecticFormRat (fiveTermRationalCharacteristic γ u₁ u₂) τ =
      fiveTermLatticeArgument γ τ u₁ u₂ := by
  have hscale := fracSymplecticFormRat_ratVecAction_of_flt_eq_self
    h.fltDenominator_pos.ne' h.flt_eq (fiveTermRationalCharacteristic γ u₁ u₂)
  have hpair := congrArg
    (fun r : Fin 2 → ℚ => fracSymplecticFormRat r τ)
    (ratVecAction_fiveTermRationalCharacteristic_sub h u₁ u₂)
  rw [fracSymplecticFormRat_sub, hscale] at hpair
  simp only [fracSymplecticFormRat, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.cons_val_zero] at hpair
  norm_num at hpair
  have hε : 1 < fltDenominator (γ : Mat(2, ℤ)) τ := h.one_lt_fltDenominator
  have hne : (fltDenominator (γ : Mat(2, ℤ)) τ)⁻¹ - 1 ≠ 0 := by
    have hlt : (fltDenominator (γ : Mat(2, ℤ)) τ)⁻¹ < 1 :=
      (inv_lt_one₀ (by linarith)).2 hε
    linarith
  rw [fiveTermLatticeArgument, eq_div_iff hne]
  unfold fracSymplecticFormRat
  rw [mul_sub, mul_one, ← div_eq_mul_inv]
  exact hpair

/-- `γ` lies in `Γ_r` for the rational lift `r` of every source pair. -/
theorem mem_gammaSubgroup_fiveTermRationalCharacteristic {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (u₁ u₂ : ℤ) :
    γ ∈ gammaSubgroup (fiveTermRationalCharacteristic γ u₁ u₂) := by
  apply mem_gammaSubgroup_of_isIntegralIndex
  rw [ratVecAction_fiveTermRationalCharacteristic_sub h]
  intro i
  exact ⟨![-u₂, u₁] i, rfl⟩

/-- The cocycle index of the rational lift of `(u₁,u₂)` is `-u₁`. -/
theorem nQPInt_fiveTermRationalCharacteristic {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (u₁ u₂ : ℤ) :
    nQPInt (fiveTermRationalCharacteristic γ u₁ u₂) (γ : Mat(2, ℤ)) = -u₁ := by
  have hcast := nQPInt_cast_of_mem
    (mem_gammaSubgroup_fiveTermRationalCharacteristic h u₁ u₂)
  have hcoord := congrFun (ratVecAction_fiveTermRationalCharacteristic_sub h u₁ u₂) 1
  simp only [Pi.sub_apply] at hcoord
  have hnq : nQP (fiveTermRationalCharacteristic γ u₁ u₂) (γ : Mat(2, ℤ)) =
      -(ratVecAction (γ : Mat(2, ℤ)) (fiveTermRationalCharacteristic γ u₁ u₂) 1 -
        fiveTermRationalCharacteristic γ u₁ u₂ 1) := by
    simp [nQP, ratVecAction, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  rw [hnq, hcoord] at hcast
  have hcast' : ((nQPInt (fiveTermRationalCharacteristic γ u₁ u₂)
      (γ : Mat(2, ℤ)) : ℤ) : ℚ) = ((-u₁ : ℤ) : ℚ) := by
    simpa only [Matrix.cons_val_one, Matrix.cons_val_fin_one, Int.cast_neg] using hcast
  exact (Int.cast_injective : Function.Injective (fun z : ℤ => (z : ℚ))) hcast'

/-- A source argument avoids `ℤ+ℤτ` exactly when its residue is nonzero. -/
theorem not_isPeriodLatticePoint_fiveTermLatticeArgument_iff {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (u₁ u₂ : ℤ) :
    ¬ IsPeriodLatticePoint (τ : ℂ) (fiveTermLatticeArgument γ τ u₁ u₂ : ℂ) ↔
      fiveTermCharacteristicResidue γ u₁ u₂ ≠ 0 := by
  let _ : NeZero (finiteDilogOrder γ) := finiteDilogOrder_neZero h
  have harg := congrArg (fun z : ℝ => (z : ℂ))
    (fracSymplecticFormRat_fiveTermRationalCharacteristic h u₁ u₂)
  rw [ofReal_fracSymplecticFormRat] at harg
  have hsub := isIntegralIndex_fiveTermCharacteristicResidue_sub_lift h u₁ u₂
  rw [← harg, isPeriodLatticePoint_fracSymplecticFormRat_iff h.irrational,
    (isIntegralIndex_iff_of_isIntegralIndex_sub hsub).symm,
    isIntegralIndex_zmodCharacteristic_iff]

/-- On the zero class, the continued product's diagonal type is negative exactly when `S<0`. -/
private theorem fiveTermZeroClassType_iff {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (u₁ u₂ : ℤ)
    (hz : fiveTermCharacteristicResidue γ u₁ u₂ = 0) :
    1 ≤ (fiveTermRationalCharacteristic γ u₁ u₂ 1).num -
      nQPInt (fiveTermRationalCharacteristic γ u₁ u₂) (γ : Mat(2, ℤ)) ↔
      fiveTermLatticeIndex γ u₁ u₂ < 0 := by
  let _ : NeZero (finiteDilogOrder γ) := finiteDilogOrder_neZero h
  have hsub := isIntegralIndex_fiveTermCharacteristicResidue_sub_lift h u₁ u₂
  have hr : IsIntegralIndex (fiveTermRationalCharacteristic γ u₁ u₂) := by
    apply (isIntegralIndex_iff_of_isIntegralIndex_sub hsub).mp
    simpa [hz] using (show IsIntegralIndex (0 : Fin 2 → ℚ) from by
      intro i
      exact ⟨0, by simp⟩)
  obtain ⟨q, hq⟩ := hr 1
  have hnum : (fiveTermRationalCharacteristic γ u₁ u₂ 1).num = q := by
    rw [hq, Rat.num_intCast]
  have hcoord := fiveTermRationalCharacteristic_snd γ u₁ u₂
  have hN : (finiteDilogOrder γ : ℚ) = (γ 0 0 : ℚ) + γ 1 1 - 2 := by
    exact_mod_cast cast_finiteDilogOrder h
  have hn : (finiteDilogOrder γ : ℚ) ≠ 0 := by
    exact_mod_cast (NeZero.ne (finiteDilogOrder γ))
  have hfrac : (q : ℚ) + u₁ =
      -(fiveTermLatticeIndex γ u₁ u₂ : ℚ) / (finiteDilogOrder γ : ℚ) := by
    rw [← hq, hcoord]
    simp only [fiveTermLatticeIndex]
    push_cast
    field_simp [hn]
    linear_combination (u₁ : ℚ) * hN
  rw [hnum, nQPInt_fiveTermRationalCharacteristic h]
  have hnpos : (0 : ℚ) < finiteDilogOrder γ := by
    exact_mod_cast finiteDilogOrder_pos h
  constructor
  · intro htype
    have hqpos : (0 : ℚ) < (q : ℚ) + u₁ := by exact_mod_cast (by omega : 0 < q + u₁)
    have hs : (fiveTermLatticeIndex γ u₁ u₂ : ℚ) < 0 := by
      have : 0 < -(fiveTermLatticeIndex γ u₁ u₂ : ℚ) /
          (finiteDilogOrder γ : ℚ) := by rw [← hfrac]; exact hqpos
      have := (lt_div_iff₀ hnpos).mp this
      nlinarith
    exact_mod_cast hs
  · intro hs
    have hs' : (fiveTermLatticeIndex γ u₁ u₂ : ℚ) < 0 := by exact_mod_cast hs
    have hqpos : (0 : ℚ) < (q : ℚ) + u₁ := by
      rw [hfrac]
      exact div_pos (by linarith) hnpos
    have hqint : 0 < q + u₁ := by exact_mod_cast hqpos
    omega

/-- Selects the zero-class continued value from the sign of the lattice index. -/
private lemma value_by_index (S q : ℤ) (V E M E' M' : ℂ)
    (hword : V = if 1 ≤ q then M else E) (htype : 1 ≤ q ↔ S < 0)
    (hE : E = E') (hM : M = M') :
    V = if 0 ≤ S then E' else M' := by
  by_cases hs : 0 ≤ S
  · have ht : ¬ 1 ≤ q := fun hi => (not_lt_of_ge hs) (htype.mp hi)
    simpa [hs, ht, hE] using hword
  · have ht : 1 ≤ q := htype.mpr (lt_of_not_ge hs)
    simpa [hs, ht, hM] using hword

/-- The continued value on the zero residue class. -/
private theorem fiveTermContinuedValue_zeroClass {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (u₁ u₂ : ℤ)
    (hx : fiveTermCharacteristicResidue (letterWord bs) u₁ u₂ = 0) :
    etaMultiplier (letterWord bs) *
        faddeevWordContinued bs u₁ 0 (fiveTermLatticeArgument (letterWord bs) τ u₁ u₂) τ =
      if 0 ≤ fiveTermLatticeIndex (letterWord bs) u₁ u₂ then
        finiteDilogE (letterWord bs) τ (fiveTermCharacteristicResidue (letterWord bs) u₁ u₂)
      else
        finiteDilogEMinus (letterWord bs) τ
          (fiveTermCharacteristicResidue (letterWord bs) u₁ u₂) := by
  let γ := letterWord bs
  let r := fiveTermRationalCharacteristic γ u₁ u₂
  let x := fiveTermCharacteristicResidue γ u₁ u₂
  change x = 0 at hx
  let _ : NeZero (finiteDilogOrder γ) := finiteDilogOrder_neZero h.fixedPoint
  have hA : γ ∈ gammaSubgroup r :=
    mem_gammaSubgroup_fiveTermRationalCharacteristic h.fixedPoint u₁ u₂
  have hsub : IsIntegralIndex (zmodCharacteristic (finiteDilogOrder γ) x - r) :=
    isIntegralIndex_fiveTermCharacteristicResidue_sub_lift h.fixedPoint u₁ u₂
  have hnq : nQPInt r (γ : Mat(2, ℤ)) = -u₁ :=
    nQPInt_fiveTermRationalCharacteristic h.fixedPoint u₁ u₂
  have hnq' : nQPInt r (letterWord bs : Mat(2, ℤ)) = -u₁ := hnq
  have harg : (fracSymplecticFormRat r τ : ℂ) =
      (fiveTermLatticeArgument γ τ u₁ u₂ : ℂ) := by
    exact_mod_cast fracSymplecticFormRat_fiveTermRationalCharacteristic h.fixedPoint u₁ u₂
  have hE : finiteDilogValue γ τ r = finiteDilogE γ τ x :=
    (finiteDilogValue_congr h.fixedPoint hA hsub).symm
  change etaMultiplier γ *
      faddeevWordContinued bs u₁ 0 (fiveTermLatticeArgument γ τ u₁ u₂) τ =
    if 0 ≤ fiveTermLatticeIndex γ u₁ u₂ then finiteDilogE γ τ x
    else finiteDilogEMinus γ τ x
  have hr : IsIntegralIndex r := by
    apply (isIntegralIndex_iff_of_isIntegralIndex_sub hsub).mp
    simpa [hx] using (show IsIntegralIndex (0 : Fin 2 → ℚ) from by
      intro i
      exact ⟨0, by simp⟩)
  have hword := etaMultiplier_mul_faddeevWordContinued_zeroClass
    h.ne_nil h.two_le h.fixedPoint hr 0
  rw [hnq', harg] at hword
  simp only [neg_neg, add_zero] at hword
  have hM : finiteDilogValueMinus γ τ r = finiteDilogEMinus γ τ x :=
    (finiteDilogValueMinus_congr h.fixedPoint hA hsub).symm
  have htype := fiveTermZeroClassType_iff h.fixedPoint u₁ u₂ hx
  have htype' : 1 ≤ (r 1).num + u₁ ↔ fiveTermLatticeIndex γ u₁ u₂ < 0 := by
    change 1 ≤ (r 1).num - nQPInt r (γ : Mat(2, ℤ)) ↔
      fiveTermLatticeIndex γ u₁ u₂ < 0 at htype
    rw [hnq] at htype
    simpa only [sub_neg_eq_add] using htype
  exact value_by_index (fiveTermLatticeIndex γ u₁ u₂) ((r 1).num + u₁) _ _ _ _ _
    (by simpa using hword) htype' hE hM

/-- The continued value on the nonzero residue class. -/
private theorem fiveTermContinuedValue_nonzeroClass {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (u₁ u₂ : ℤ)
    (hx : fiveTermCharacteristicResidue (letterWord bs) u₁ u₂ ≠ 0) :
    etaMultiplier (letterWord bs) *
        faddeevWordContinued bs u₁ 0 (fiveTermLatticeArgument (letterWord bs) τ u₁ u₂) τ =
      if 0 ≤ fiveTermLatticeIndex (letterWord bs) u₁ u₂ then
        finiteDilogE (letterWord bs) τ (fiveTermCharacteristicResidue (letterWord bs) u₁ u₂)
      else
        finiteDilogEMinus (letterWord bs) τ
          (fiveTermCharacteristicResidue (letterWord bs) u₁ u₂) := by
  let γ := letterWord bs
  let r := fiveTermRationalCharacteristic γ u₁ u₂
  let x := fiveTermCharacteristicResidue γ u₁ u₂
  change x ≠ 0 at hx
  let _ : NeZero (finiteDilogOrder γ) := finiteDilogOrder_neZero h.fixedPoint
  have hA : γ ∈ gammaSubgroup r :=
    mem_gammaSubgroup_fiveTermRationalCharacteristic h.fixedPoint u₁ u₂
  have hsub : IsIntegralIndex (zmodCharacteristic (finiteDilogOrder γ) x - r) :=
    isIntegralIndex_fiveTermCharacteristicResidue_sub_lift h.fixedPoint u₁ u₂
  have hnq : nQPInt r (γ : Mat(2, ℤ)) = -u₁ :=
    nQPInt_fiveTermRationalCharacteristic h.fixedPoint u₁ u₂
  have hnq' : nQPInt r (letterWord bs : Mat(2, ℤ)) = -u₁ := hnq
  have harg : (fracSymplecticFormRat r τ : ℂ) =
      (fiveTermLatticeArgument γ τ u₁ u₂ : ℂ) := by
    exact_mod_cast fracSymplecticFormRat_fiveTermRationalCharacteristic h.fixedPoint u₁ u₂
  have hE : finiteDilogValue γ τ r = finiteDilogE γ τ x :=
    (finiteDilogValue_congr h.fixedPoint hA hsub).symm
  change etaMultiplier γ *
      faddeevWordContinued bs u₁ 0 (fiveTermLatticeArgument γ τ u₁ u₂) τ =
    if 0 ≤ fiveTermLatticeIndex γ u₁ u₂ then finiteDilogE γ τ x
    else finiteDilogEMinus γ τ x
  have hr : ¬ IsIntegralIndex r := by
    intro hr
    apply hx
    exact (isIntegralIndex_zmodCharacteristic_iff _ _).mp
      ((isIntegralIndex_iff_of_isIntegralIndex_sub hsub).mpr hr)
  have hword := etaMultiplier_mul_faddeevWordContinued
    h.ne_nil h.two_le h.fixedPoint hr hA 0
  rw [hnq', harg] at hword
  simp only [neg_neg, add_zero] at hword
  rw [hE] at hword
  have hminus := finiteDilogEMinus_of_ne_zero h.fixedPoint hx
  by_cases hs : 0 ≤ fiveTermLatticeIndex γ u₁ u₂
  · simpa [hs] using hword
  · simpa [hs] using hword.trans hminus.symm

/-- **The finite dilogarithm at a source argument.** At an attractive fixed point of a letter
word, `μ_γ Φ^cont_{γ,u₁,0}(z_u;τ)` is `E(x)` for the residue `x` of `(u₁,u₂)` when `S(u) ≥ 0`
and `F⁻(x)` when `S(u) < 0`; the two agree off the zero class. This combines [RW26, Radchenko,
Wheeler (2026), equation (2), `eq:fgam.def`] for the letter word
(`etaMultiplier_mul_faddeevWordContinued`, `etaMultiplier_mul_faddeevWordContinued_zeroClass`)
with Lemma 2, `lem:lam.inv` (`finiteDilogValue_congr`). -/
theorem etaMultiplier_mul_faddeevWordContinued_latticeArgument {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (u₁ u₂ : ℤ) :
    etaMultiplier (letterWord bs) *
        faddeevWordContinued bs u₁ 0 (fiveTermLatticeArgument (letterWord bs) τ u₁ u₂) τ =
      if 0 ≤ fiveTermLatticeIndex (letterWord bs) u₁ u₂ then
        finiteDilogE (letterWord bs) τ (fiveTermCharacteristicResidue (letterWord bs) u₁ u₂)
      else
        finiteDilogEMinus (letterWord bs) τ
          (fiveTermCharacteristicResidue (letterWord bs) u₁ u₂) := by
  by_cases hx : fiveTermCharacteristicResidue (letterWord bs) u₁ u₂ = 0
  · exact fiveTermContinuedValue_zeroClass h u₁ u₂ hx
  · exact fiveTermContinuedValue_nonzeroClass h u₁ u₂ hx

/-- Off the zero class, the finite value `E` is the word product at the source argument
multiplied by `μ_γ`; at a source argument. -/
theorem etaMultiplier_mul_faddeevWord_latticeArgument {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (u₁ u₂ : ℤ)
    (hu : fiveTermCharacteristicResidue (letterWord bs) u₁ u₂ ≠ 0) :
    etaMultiplier (letterWord bs) *
      faddeevWord bs u₁ 0 (fiveTermLatticeArgument (letterWord bs) τ u₁ u₂) τ =
        finiteDilogE (letterWord bs) τ
          (fiveTermCharacteristicResidue (letterWord bs) u₁ u₂) := by
  have hvalue := etaMultiplier_mul_faddeevWordContinued_latticeArgument h u₁ u₂
  rw [faddeevWordContinued_eq_of_notMem bs u₁ 0 h.periodsPos.slitPlane
    ((not_isPeriodLatticePoint_fiveTermLatticeArgument_iff h.fixedPoint u₁ u₂).2 hu)]
    at hvalue
  simpa only [finiteDilogEMinus_of_ne_zero h.fixedPoint hu, ite_self] using hvalue


end SIC

end
