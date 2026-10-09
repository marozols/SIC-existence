/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Dilogarithm.FiniteQuantum
import SICs.Dilogarithm.FiveTerm.CrossedIdentity
import SICs.Dilogarithm.FiveTerm.CrossedStrip

/-!
# The finite five-term relation along a letter word

The finite five-term relation (7) at an attractive fixed point of a letter word, for every pair
of classes not both zero.

This module proves [RW26, Radchenko, Wheeler (2026), Theorem 2, `thm:fg.equs`, equation (7),
`eq:Fgpm.5term`] for `γ = ∏_j T^{b_j}S` (letters after the first at least `2`) at an attractive
fixed point `τ`, `ε = j_γ(τ)`, `N = Tr γ - 2`, by the crossed-pole form of its residue argument
in Section 3.2. The principal word `A_d` is proved directly in
`SICs.Principal.Dilogarithm.FiveTerm`.

## The argument

For a nonzero right class `v`, choose positive source representatives
(`exists_fiveTerm_positive_representatives`) and a common line `x` just right of
`β_v = -(v₁ε/c+z_v)`, avoiding the countably many irregular crossings; irrationality of `β_v`
keeps the crossed integer positions `j/c` constant on a small interval to its right. The crossed
residue strip (`integral_fiveTermWordResidueSum_of_crossed`) and the crossed shifted integral
(`integral_fiveTermWordDifferenceSum_of_crossed`) have the same square corrections; on a line
regular at both boundaries the telescoping identity (`ae_fiveTermWordResidueSum_sub_shift_eq`)
identifies their remaining integrals, so subtraction cancels the squares and gives
`ε/(ε-1) ∑_g ⟨g;u⟩ E(g)/F⁻(g+v) = √ε E(u+v)/(F⁻(u)F⁻(v))`. Since `ε-1 = √(Nε)`, this is (7).
For `v = 0` and `u ≠ 0`, (7) follows from the reflection law and `E(0)² = √N E(0) + 1` by
character orthogonality (`MetricGroup.fiveTerm_zero_right`). The finite quantum dilogarithm is
then `finiteDilogFiniteQuantum` on `fixedMetricGroup`.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology MatrixGroups

namespace SIC

/-! ### Regular common lines

The two strip boundaries must avoid the period lattices and the residue-kernel poles. A
countable exclusion chooses such a line in any prescribed open interval. -/

/-- The four countable families excluded from a common line: the period lattice at each
parameter and the residue-kernel poles. Used by `finiteDilogFiveTerm_letterWord_of_ne_zero_right`.
-/
private def fiveTermWordBadPoint (bs : List ℤ) (τ y y' : ℝ)
    (q : FiveTermIndex (letterWord bs) × (Fin 4 × (ℤ × ℤ))) : ℝ :=
  let s := ((q.1 : ℕ) : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
    (letterWord bs 1 0 : ℝ)
  let z := (q.2.2.1 : ℝ) + (q.2.2.2 : ℝ) * τ
  if q.2.1 = 0 then s + z else
    if q.2.1 = 1 then s + z - y else
      if q.2.1 = 2 then s + z - y' else
        s + fiveTermLatticeArgument (letterWord bs) τ ((q.1 : ℕ) : ℤ) q.2.2.1

/-- A common line avoids all four forbidden families at every contour index. Used by
`finiteDilogFiveTerm_letterWord_of_ne_zero_right`. -/
private def fiveTermWordCrossingAvoids (bs : List ℤ) (τ y y' x : ℝ) : Prop :=
  ∀ m : FiveTermIndex (letterWord bs),
    (∀ n k : ℤ, x - ((m : ℕ) : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
      (letterWord bs 1 0 : ℝ) ≠ (n : ℝ) + (k : ℝ) * τ) ∧
    (∀ n k : ℤ, x - ((m : ℕ) : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
      (letterWord bs 1 0 : ℝ) + y ≠ (n : ℝ) + (k : ℝ) * τ) ∧
    (∀ n k : ℤ, x - ((m : ℕ) : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
      (letterWord bs 1 0 : ℝ) + y' ≠ (n : ℝ) + (k : ℝ) * τ) ∧
    (∀ k : ℤ, x - ((m : ℕ) : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
      (letterWord bs 1 0 : ℝ) ≠
        fiveTermLatticeArgument (letterWord bs) τ ((m : ℕ) : ℤ) k)

/-- Avoiding the range of `fiveTermWordBadPoint` gives all regularity conditions. Used by
`exists_fiveTermWord_avoiding_between`. -/
private theorem fiveTermWordCrossingAvoids_of_not_mem (bs : List ℤ) (τ y y' x : ℝ)
    (hx : x ∉ Set.range (fiveTermWordBadPoint bs τ y y')) :
    fiveTermWordCrossingAvoids bs τ y y' x := by
  intro m
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n k h
    apply hx
    refine ⟨(m, (0, (n, k))), ?_⟩
    dsimp [fiveTermWordBadPoint]
    linarith
  · intro n k h
    apply hx
    refine ⟨(m, (1, (n, k))), ?_⟩
    dsimp [fiveTermWordBadPoint]
    linarith
  · intro n k h
    apply hx
    refine ⟨(m, (2, (n, k))), ?_⟩
    dsimp [fiveTermWordBadPoint]
    linarith
  · intro k h
    apply hx
    refine ⟨(m, (3, (k, 0))), ?_⟩
    dsimp [fiveTermWordBadPoint]
    linarith

/-- Every nonempty open interval contains a common line regular at both boundaries of the
translated strip. Used by `finiteDilogFiveTerm_letterWord_of_ne_zero_right`. -/
private theorem exists_fiveTermWord_avoiding_between (bs : List ℤ) (τ y y' a b : ℝ)
    (hab : a < b) :
    ∃ x : ℝ, a < x ∧ x < b ∧ fiveTermWordCrossingAvoids bs τ y y' x ∧
      fiveTermWordCrossingAvoids bs τ y y'
        (x + (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
          (letterWord bs 1 0 : ℝ)) := by
  have hne : (Set.Ioo a b).Nonempty := ⟨(a + b) / 2, by constructor <;> linarith⟩
  let bad := Set.range (fiveTermWordBadPoint bs τ y y')
  let bad' := Set.range (fun q => fiveTermWordBadPoint bs τ y y' q -
    (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
      (letterWord bs 1 0 : ℝ))
  have hcount : (bad ∪ bad').Countable :=
    (Set.countable_range _).union (Set.countable_range _)
  obtain ⟨x, hxBad, hxI⟩ := (hcount.dense_compl ℝ).exists_mem_open isOpen_Ioo hne
  have hxBad₁ : x ∉ bad := fun h => hxBad (Set.mem_union_left _ h)
  have hxBad₂ : x + (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
      (letterWord bs 1 0 : ℝ) ∉ bad := by
    intro ⟨q, hq⟩
    apply hxBad (Set.mem_union_right _ _)
    refine ⟨q, ?_⟩
    dsimp [bad']
    linarith
  exact ⟨x, hxI.1, hxI.2,
    fiveTermWordCrossingAvoids_of_not_mem bs τ y y' x hxBad₁,
    fiveTermWordCrossingAvoids_of_not_mem bs τ y y' _ hxBad₂⟩

/-- The real exclusions give the regular crossings used by the residue and shifted integrals.
Used by `finiteDilogFiveTerm_letterWord_of_ne_zero_right`. -/
private theorem fiveTermWordCrossingAvoids_regular (bs : List ℤ) (τ y y' x : ℝ)
    (havoid : fiveTermWordCrossingAvoids bs τ y y' x) :
    (∀ m : FiveTermIndex (letterWord bs),
      IsFiveTermResidueCrossing (letterWord bs) τ ((m : ℕ) : ℤ) y
        (x - ((m : ℕ) : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
          (letterWord bs 1 0 : ℝ))) ∧
    (∀ m : FiveTermIndex (letterWord bs),
      IsRegularPeriodLatticeCrossing τ y'
        (x - ((m : ℕ) : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
          (letterWord bs 1 0 : ℝ))) := by
  constructor
  · intro m
    obtain ⟨hbase, hshift, _, hpole⟩ := havoid m
    refine ⟨⟨?_, ?_⟩, hpole⟩
    · rintro ⟨n, k, h⟩
      apply hbase n k
      apply Complex.ofReal_injective
      simpa only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_intCast] using h
    · rintro ⟨n, k, h⟩
      apply hshift n k
      apply Complex.ofReal_injective
      simpa only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_intCast] using h
  · intro m
    obtain ⟨hbase, _, hshift, _⟩ := havoid m
    refine ⟨?_, ?_⟩
    · rintro ⟨n, k, h⟩
      apply hbase n k
      apply Complex.ofReal_injective
      simpa only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_intCast] using h
    · rintro ⟨n, k, h⟩
      apply hshift n k
      apply Complex.ofReal_injective
      simpa only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_intCast] using h

/-! ### The crossed right pole and the selected strip

For positive right index, the pole lies strictly between zero and the strip width. Its
irrational position leaves the integer crossings unchanged just to its right. -/

/-- A positive right source pole misses every integer crossing `j/c`. Used by
`fiveTermWord_crossed_beta_data`. -/
private theorem fiveTermWord_crossed_beta_ne_grid {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (v₁ v₂ j : ℤ)
    (hv : 1 ≤ fiveTermLatticeIndex (letterWord bs) v₁ v₂) :
    -((v₁ : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
        (letterWord bs 1 0 : ℝ) + fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) ≠
      (j : ℝ) / (letterWord bs 1 0 : ℝ) := by
  let ε : ℝ := fltDenominator (letterWord bs : Mat(2, ℤ)) τ
  let c : ℝ := letterWord bs 1 0
  let N : ℝ := finiteDilogOrder (letterWord bs)
  let S : ℤ := fiveTermLatticeIndex (letterWord bs) v₁ v₂
  have hc : c ≠ 0 := by dsimp [c]; exact_mod_cast h.fixedPoint.lowerLeft_pos.ne'
  have hN : N ≠ 0 := by dsimp [N]; exact_mod_cast (finiteDilogOrder_pos h.fixedPoint).ne'
  have hirrε : Irrational (ε - 1) := by
    have hc0 : (letterWord bs 1 0 : ℤ) ≠ 0 := h.fixedPoint.lowerLeft_pos.ne'
    have hi := (h.fixedPoint.irrational.intCast_mul hc0).intCast_add
      (letterWord bs 1 1 - 1)
    convert hi using 1
    dsimp [ε, fltDenominator]
    push_cast
    ring
  intro hj
  rw [fiveTermLatticeArgument_beta_eq h.fixedPoint] at hj
  have hmul := (div_eq_div_iff (mul_ne_zero hc hN) hc).1 hj
  have hEq : (ε - 1) * (S : ℝ) =
      ((j * (finiteDilogOrder (letterWord bs) : ℤ) : ℤ) : ℝ) := by
    have hcancel : c * ((ε - 1) * (S : ℝ)) = c * ((j : ℝ) * N) := by
      nlinarith [hmul]
    have hcancel' := mul_left_cancel₀ hc hcancel
    simpa only [N, Int.cast_mul, Int.cast_natCast] using hcancel'
  exact (hirrε.mul_intCast (by omega : S ≠ 0)).ne_int _ hEq

/-- The positive right source pole lies inside the strip and off the integer grid. Used by
`exists_fiveTermWord_crossed_line`. -/
private theorem fiveTermWord_crossed_beta_data {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (v₁ v₂ : ℤ)
    (hv : 1 ≤ fiveTermLatticeIndex (letterWord bs) v₁ v₂ ∧
      fiveTermLatticeIndex (letterWord bs) v₁ v₂ ≤ finiteDilogOrder (letterWord bs)) :
    let ε := fltDenominator (letterWord bs : Mat(2, ℤ)) τ
    let c : ℝ := letterWord bs 1 0
    let y := fiveTermLatticeArgument (letterWord bs) τ v₁ v₂
    let β := -((v₁ : ℝ) * ε / c + y)
    0 < β ∧ β ≤ (ε - 1) / c ∧ ∀ j : ℤ, β ≠ (j : ℝ) / c := by
  let ε : ℝ := fltDenominator (letterWord bs : Mat(2, ℤ)) τ
  let c : ℝ := letterWord bs 1 0
  let N : ℝ := finiteDilogOrder (letterWord bs)
  let S : ℤ := fiveTermLatticeIndex (letterWord bs) v₁ v₂
  let y := fiveTermLatticeArgument (letterWord bs) τ v₁ v₂
  let β := -((v₁ : ℝ) * ε / c + y)
  have hc : 0 < c := by dsimp [c]; exact_mod_cast h.fixedPoint.lowerLeft_pos
  have hN : 0 < N := by dsimp [N]; exact_mod_cast finiteDilogOrder_pos h.fixedPoint
  have hε : 0 < ε - 1 := sub_pos.mpr h.fixedPoint.one_lt_fltDenominator
  have hS : 0 < (S : ℝ) := by exact_mod_cast hv.1
  have hSle : (S : ℝ) ≤ N := by
    dsimp [S, N]
    exact_mod_cast hv.2
  have hβ : β = (ε - 1) * (S : ℝ) / (c * N) := fiveTermLatticeArgument_beta_eq h.fixedPoint v₁ v₂
  change 0 < β ∧ β ≤ (ε - 1) / c ∧ ∀ j : ℤ, β ≠ (j : ℝ) / c
  refine ⟨?_, ?_, ?_⟩
  · rw [hβ]
    exact div_pos (mul_pos hε hS) (mul_pos hc hN)
  · rw [hβ]
    apply (div_le_div_iff₀ (mul_pos hc hN) hc).2
    nlinarith [mul_nonneg (mul_nonneg hε.le hc.le) (sub_nonneg.mpr hSle)]
  · intro j
    exact fiveTermWord_crossed_beta_ne_grid h v₁ v₂ j hv.1

/-- A common line just right of the right source pole meets both crossed endpoint domains,
keeps the crossed integer set fixed, and is regular at both strip boundaries. Used by
`finiteDilogFiveTerm_letterWord_of_ne_zero_right`. -/
private theorem exists_fiveTermWord_crossed_line {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (v₁ v₂ : ℤ)
    (hv : 1 ≤ fiveTermLatticeIndex (letterWord bs) v₁ v₂ ∧
      fiveTermLatticeIndex (letterWord bs) v₁ v₂ ≤ finiteDilogOrder (letterWord bs)) :
    let ε := fltDenominator (letterWord bs : Mat(2, ℤ)) τ
    let c : ℝ := letterWord bs 1 0
    let N : ℝ := finiteDilogOrder (letterWord bs)
    let δ := (ε - 1) / c
    let y := fiveTermLatticeArgument (letterWord bs) τ v₁ v₂
    let β := -((v₁ : ℝ) * ε / c + y)
    ∃ (x : ℝ) (F : Finset ℤ),
      β < x ∧ x < β + δ / N ∧ x < ε / c ∧
      (∀ j : ℤ, j ∈ F ↔ 0 ≤ j ∧ (j : ℝ) / c < β) ∧
      (∀ j : ℤ, 0 ≤ j → ((j : ℝ) / c < x ↔ (j : ℝ) / c < β)) ∧
      (∀ m : FiveTermIndex (letterWord bs),
        IsFiveTermResidueCrossing (letterWord bs) τ ((m : ℕ) : ℤ) y
          (x - ((m : ℕ) : ℝ) * ε / c)) ∧
      (∀ m : FiveTermIndex (letterWord bs),
        IsFiveTermResidueCrossing (letterWord bs) τ ((m : ℕ) : ℤ) y
          (x + δ - ((m : ℕ) : ℝ) * ε / c)) := by
  let ε : ℝ := fltDenominator (letterWord bs : Mat(2, ℤ)) τ
  let c : ℝ := letterWord bs 1 0
  let N : ℝ := finiteDilogOrder (letterWord bs)
  let δ : ℝ := (ε - 1) / c
  let y := fiveTermLatticeArgument (letterWord bs) τ v₁ v₂
  let y' := fiveTermShiftedParameter (letterWord bs) τ y
  let β := -((v₁ : ℝ) * ε / c + y)
  have hc : 0 < c := by dsimp [c]; exact_mod_cast h.fixedPoint.lowerLeft_pos
  have hN : 0 < N := by dsimp [N]; exact_mod_cast finiteDilogOrder_pos h.fixedPoint
  have hε : 0 < ε - 1 := sub_pos.mpr h.fixedPoint.one_lt_fltDenominator
  obtain ⟨_, hβle, hβgrid⟩ := fiveTermWord_crossed_beta_data h v₁ v₂ hv
  have hβeps : β < ε / c := by
    have hδlt : δ < ε / c := by
      dsimp [δ]
      apply (div_lt_div_iff₀ hc hc).2
      nlinarith [hc]
    exact lt_of_le_of_lt hβle hδlt
  have hβnext : β < (⌈c * β⌉ : ℝ) / c := by
    have hceil : c * β ≤ (⌈c * β⌉ : ℝ) := Int.le_ceil _
    have hne : c * β ≠ (⌈c * β⌉ : ℝ) := by
      intro heq
      apply hβgrid ⌈c * β⌉
      apply (eq_div_iff hc.ne').2
      nlinarith [heq]
    exact (lt_div_iff₀ hc).2 (by nlinarith [lt_of_le_of_ne hceil hne])
  have hδN : 0 < δ / N := div_pos (div_pos hε hc) hN
  let b := min (β + δ / N) (min (ε / c) ((⌈c * β⌉ : ℝ) / c))
  have hβb : β < b := lt_min (by linarith) (lt_min hβeps hβnext)
  obtain ⟨x, hβx, hxb, havoid, havoidRight⟩ :=
    exists_fiveTermWord_avoiding_between bs τ y y' β b hβb
  let F : Finset ℤ := Finset.Ico 0 ⌈c * β⌉
  have hF : ∀ j : ℤ, j ∈ F ↔ 0 ≤ j ∧ (j : ℝ) / c < β := by
    intro j
    change j ∈ Finset.Ico 0 ⌈c * β⌉ ↔ 0 ≤ j ∧ (j : ℝ) / c < β
    rw [Finset.mem_Ico, Int.lt_ceil]
    constructor
    · rintro ⟨hj0, hj⟩
      exact ⟨hj0, (div_lt_iff₀ hc).2 (by nlinarith [hj])⟩
    · rintro ⟨hj0, hj⟩
      exact ⟨hj0, (div_lt_iff₀ hc).1 hj |>.trans_eq (mul_comm β c)⟩
  have hstable : ∀ j : ℤ, 0 ≤ j → ((j : ℝ) / c < x ↔ (j : ℝ) / c < β) := by
    intro j _
    constructor
    · intro hjx
      have hjcx : (j : ℝ) < x * c := (div_lt_iff₀ hc).1 hjx
      have hxceil : x * c < (⌈c * β⌉ : ℝ) := (lt_div_iff₀ hc).1
        (lt_of_lt_of_le hxb ((min_le_right _ _).trans (min_le_right _ _)))
      have hjceil : j < ⌈c * β⌉ := by exact_mod_cast lt_trans hjcx hxceil
      exact (div_lt_iff₀ hc).2 ((Int.lt_ceil.1 hjceil).trans_eq (mul_comm c β))
    · intro hjβ
      exact lt_trans hjβ hβx
  have hreg := (fiveTermWordCrossingAvoids_regular bs τ y y' x havoid).1
  have hregRight := (fiveTermWordCrossingAvoids_regular bs τ y y' (x + δ) havoidRight).1
  change ∃ (x : ℝ) (F : Finset ℤ), β < x ∧ x < β + δ / N ∧ x < ε / c ∧
    (∀ j : ℤ, j ∈ F ↔ 0 ≤ j ∧ (j : ℝ) / c < β) ∧
    (∀ j : ℤ, 0 ≤ j → ((j : ℝ) / c < x ↔ (j : ℝ) / c < β)) ∧
    (∀ m : FiveTermIndex (letterWord bs),
      IsFiveTermResidueCrossing (letterWord bs) τ ((m : ℕ) : ℤ) y
        (x - ((m : ℕ) : ℝ) * ε / c)) ∧
    (∀ m : FiveTermIndex (letterWord bs),
      IsFiveTermResidueCrossing (letterWord bs) τ ((m : ℕ) : ℤ) y
        (x + δ - ((m : ℕ) : ℝ) * ε / c))
  exact ⟨x, F, hβx, lt_of_lt_of_le hxb (min_le_left _ _),
    lt_of_lt_of_le hxb ((min_le_right _ _).trans (min_le_left _ _)),
    hF, hstable, hreg, by simpa [δ, ε, c] using hregRight⟩

/-- A sufficiently small positive radius is regular at both vertical edges of the crossed
squares. Used by `finiteDilogFiveTerm_letterWord_of_ne_zero_right`. -/
private theorem exists_fiveTermWord_regular_radius {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (y b : ℝ) (hb : 0 < b) :
    ∃ r : ℝ, 0 < r ∧ r < b ∧
      IsRegularPeriodLatticeCrossing τ y r ∧ IsRegularPeriodLatticeCrossing τ y (-r) := by
  let bad := Set.range (fiveTermWordBadPoint bs τ y y)
  let badNeg := Set.range (fun q => -fiveTermWordBadPoint bs τ y y q)
  have hcount : (bad ∪ badNeg).Countable :=
    (Set.countable_range _).union (Set.countable_range _)
  have hne : (Set.Ioo (0 : ℝ) b).Nonempty := ⟨b / 2, by constructor <;> linarith⟩
  obtain ⟨r, hrBad, hrI⟩ := (hcount.dense_compl ℝ).exists_mem_open isOpen_Ioo hne
  have hrPlus : r ∉ bad := fun h => hrBad (Set.mem_union_left _ h)
  have hrMinus : -r ∉ bad := by
    intro ⟨q, hq⟩
    apply hrBad (Set.mem_union_right _ _)
    refine ⟨q, ?_⟩
    dsimp [badNeg] at hq ⊢
    linarith
  have hc : 0 < (letterWord bs 1 0).toNat := by
    have := h.fixedPoint.lowerLeft_pos
    omega
  let m : FiveTermIndex (letterWord bs) := ⟨0, hc⟩
  have hplus := (fiveTermWordCrossingAvoids_regular bs τ y y r
    (fiveTermWordCrossingAvoids_of_not_mem bs τ y y r hrPlus)).2 m
  have hminus := (fiveTermWordCrossingAvoids_regular bs τ y y (-r)
    (fiveTermWordCrossingAvoids_of_not_mem bs τ y y (-r) hrMinus)).2 m
  exact ⟨r, hrI.1, hrI.2, by simpa [m] using hplus, by simpa [m] using hminus⟩

/-! ### Telescoping and normalization

The source index bounds make both boundary integrals convergent. The almost-everywhere
telescoping identity identifies their difference with the shifted integral. -/

/-- Translation of a vertical line by `δ=(ε-1)/c` is a real translation of its crossing.
Used by `fiveTermWord_integral_telescope`. -/
private theorem fiveTermWord_line_shift (bs : List ℤ) (τ x t : ℝ) :
    ((x : ℂ) + t * I) +
        (fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) - 1) /
          (letterWord bs 1 0 : ℂ) =
      ((x + (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
        (letterWord bs 1 0 : ℝ) : ℝ) : ℂ) + t * I := by
  push_cast
  ring

/-- Integrating the almost-everywhere telescoping identity gives the difference of the two
strip-boundary integrals. Used by `finiteDilogFiveTerm_letterWord_of_ne_zero_right`. -/
private theorem fiveTermWord_integral_telescope {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ p : ℤ) (w y x : ℝ)
    (hreg : ∀ m : FiveTermIndex (letterWord bs),
      IsFiveTermResidueCrossing (letterWord bs) τ ((m : ℕ) : ℤ) y
        (x - ((m : ℕ) : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
          (letterWord bs 1 0 : ℝ)))
    (hregRight : ∀ m : FiveTermIndex (letterWord bs),
      IsFiveTermResidueCrossing (letterWord bs) τ ((m : ℕ) : ℤ) y
        (x + (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
          (letterWord bs 1 0 : ℝ) -
          ((m : ℕ) : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
            (letterWord bs 1 0 : ℝ)))
    (hupper : (fltDenominator (letterWord bs : Mat(2, ℤ)) τ)⁻¹ <
      fiveTermUpperRate (letterWord bs) ℓ w τ)
    (hlower : fiveTermLowerRate (letterWord bs) ℓ p w y τ < 0)
    (hw : Complex.exp (2 * Real.pi * I *
        ((w : ℂ) / fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ))) =
      Complex.exp (2 * Real.pi * I * ((w : ℂ) + (ℓ - 1) * (τ : ℂ))))
    (hy : Complex.exp (2 * Real.pi * I *
        ((y : ℂ) / fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ))) =
      Complex.exp (2 * Real.pi * I * ((y : ℂ) + p * (τ : ℂ)))) :
    (∫ t : ℝ, fiveTermWordDifferenceSum bs ℓ p w y τ ((x : ℂ) + t * I) * I) =
      (∫ t : ℝ, fiveTermWordResidueSum bs ℓ p w y τ ((x : ℂ) + t * I) * I) -
        (∫ t : ℝ, fiveTermWordResidueSum bs ℓ p w y τ
          (((x + (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
            (letterWord bs 1 0 : ℝ) : ℝ) : ℂ) + t * I) * I) := by
  let L := fiveTermWordResidueSum bs ℓ p w y τ
  have hleft := integrable_fiveTermWordResidueSum h ℓ p w y x hreg hupper hlower
  have hright := integrable_fiveTermWordResidueSum h ℓ p w y
    (x + (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
      (letterWord bs 1 0 : ℝ)) hregRight hupper hlower
  have hrightShift : Integrable (fun t : ℝ => L (((x : ℂ) + t * I) +
      (fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) - 1) /
        (letterWord bs 1 0 : ℂ))) volume := by
    convert hright using 1
    funext t
    exact congrArg L (fiveTermWord_line_shift bs τ x t)
  have hae := ae_fiveTermWordResidueSum_sub_shift_eq h ℓ p w y hw hy x
  calc
    _ = ∫ t : ℝ, (L ((x : ℂ) + t * I) -
        L (((x : ℂ) + t * I) +
          (fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) - 1) /
            (letterWord bs 1 0 : ℂ))) * I := by
      apply integral_congr_ae
      filter_upwards [hae] with t ht
      rw [ht]
    _ = _ := by
      simp_rw [sub_mul]
      rw [integral_sub (hleft.mul_const I) (hrightShift.mul_const I)]
      have heq : (∫ t : ℝ, L (((x : ℂ) + t * I) +
          (fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) - 1) /
            (letterWord bs 1 0 : ℂ)) * I) =
          (∫ t : ℝ, L
            (((x + (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
              (letterWord bs 1 0 : ℝ) : ℝ) : ℂ) + t * I) * I) := by
        apply integral_congr_ae
        filter_upwards [] with t
        rw [fiveTermWord_line_shift bs τ x t]
      exact congrArg₂ (· - ·) rfl heq

/-- The crossed-strip coefficient is `√ε/√N`, because `ε-1 = √N√ε`. Used by
`finiteDilogFiveTerm_letterWord_of_ne_zero_right`. -/
private theorem fiveTermWord_crossed_prefactor_eq {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) :
    ((fltDenominator (letterWord bs : Mat(2, ℤ)) τ : ℝ) : ℂ) /
        (((fltDenominator (letterWord bs : Mat(2, ℤ)) τ : ℝ) : ℂ) - 1) =
      (Real.sqrt (fltDenominator (letterWord bs : Mat(2, ℤ)) τ) : ℂ) /
        (Real.sqrt (finiteDilogOrder (letterWord bs)) : ℂ) := by
  let ε : ℝ := fltDenominator (letterWord bs : Mat(2, ℤ)) τ
  let s : ℝ := Real.sqrt ε
  let n : ℝ := Real.sqrt (finiteDilogOrder (letterWord bs))
  have hε : 1 < ε := h.fixedPoint.one_lt_fltDenominator
  have hs0 : s ≠ 0 := Real.sqrt_ne_zero'.mpr (by linarith)
  have hn0 : n ≠ 0 := Real.sqrt_ne_zero'.mpr (by
    exact_mod_cast finiteDilogOrder_pos h.fixedPoint)
  have hsq : s ^ 2 = ε := Real.sq_sqrt (by linarith)
  have hrel : ε - 1 = n * s := by
    have hroot := sqrt_finiteDilogOrder_eq h.fixedPoint
    have hmul := congrArg (fun t : ℝ => t * s) hroot
    have hinv := mul_inv_cancel₀ hs0
    dsimp [s, n, ε] at *
    nlinarith [hmul]
  have heC : (ε : ℂ) - 1 ≠ 0 := by
    exact_mod_cast (ne_of_gt (by linarith : 0 < ε - 1))
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  suffices heq : (ε : ℂ) / ((ε : ℂ) - 1) = (s : ℂ) / (n : ℂ) by
    simpa only [ε, s, n] using heq
  apply (div_eq_div_iff heC hnC).2
  have hsqC : (s : ℂ) ^ 2 = (ε : ℂ) := by exact_mod_cast hsq
  have hrelC : (ε : ℂ) - 1 = (n : ℂ) * s := by exact_mod_cast hrel
  calc
    (ε : ℂ) * n = (s : ℂ) ^ 2 * n := by rw [hsqC]
    _ = (s : ℂ) * ((ε : ℂ) - 1) := by rw [hrelC]; ring

/-- Cancel the nonzero factor `√ε` after the residue prefactor has become `√ε/√N`.
Used by `finiteDilogFiveTerm_letterWord_of_ne_zero_right`. -/
private theorem fiveTermWord_normalize {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (A B S : ℂ)
    (heq : (Real.sqrt (fltDenominator (letterWord bs : Mat(2, ℤ)) τ) : ℂ) * A / B =
      ((Real.sqrt (fltDenominator (letterWord bs : Mat(2, ℤ)) τ) : ℂ) /
        (Real.sqrt (finiteDilogOrder (letterWord bs)) : ℂ)) * S) :
    (1 / (Real.sqrt (finiteDilogOrder (letterWord bs)) : ℂ)) * S = A / B := by
  have hs0 : (Real.sqrt (fltDenominator (letterWord bs : Mat(2, ℤ)) τ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr h.fixedPoint.fltDenominator_pos)
  have hcancel :
      (Real.sqrt (fltDenominator (letterWord bs : Mat(2, ℤ)) τ) : ℂ) * (A / B) =
        (Real.sqrt (fltDenominator (letterWord bs : Mat(2, ℤ)) τ) : ℂ) *
          ((1 / (Real.sqrt (finiteDilogOrder (letterWord bs)) : ℂ)) * S) := by
    calc
      _ = (Real.sqrt (fltDenominator (letterWord bs : Mat(2, ℤ)) τ) : ℂ) * A / B := by ring
      _ = ((Real.sqrt (fltDenominator (letterWord bs : Mat(2, ℤ)) τ) : ℂ) /
        (Real.sqrt (finiteDilogOrder (letterWord bs)) : ℂ)) * S := heq
      _ = _ := by ring
  exact (mul_left_cancel₀ hs0 hcancel).symm

/-- **[RW26, Radchenko, Wheeler (2026), Theorem 2, `thm:fg.equs`, equation (7), `eq:Fgpm.5term`]
along a letter word**, the finite five-term relation at an attractive fixed point `τ` of
`γ = ∏_j T^{b_j}S`: for `u, v ∈ G` with `v ≠ 0`,
`(1/√N) ∑_{x ∈ G} ⟨x; u⟩ F⁺(x)/F⁻(x + v) = F⁺(u + v)/(F⁻(u) F⁻(v))`. -/
theorem finiteDilogFiveTerm_letterWord_of_ne_zero_right {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) [NeZero (finiteDilogOrder (letterWord bs))]
    {u v : Fin 2 → ZMod (finiteDilogOrder (letterWord bs))}
    (hu : u ∈ finiteDilogGroup (letterWord bs)) (hv : v ∈ finiteDilogGroup (letterWord bs))
    (hv0 : v ≠ 0) :
    (1 / (Real.sqrt (finiteDilogOrder (letterWord bs)) : ℂ)) *
        ∑ x : finiteDilogGroup (letterWord bs),
          fixedBicharacter (letterWord bs) (finiteDilogOrder (letterWord bs)) x u *
            (finiteDilogE (letterWord bs) τ x / finiteDilogEMinus (letterWord bs) τ (x + v)) =
      finiteDilogE (letterWord bs) τ (u + v) /
        (finiteDilogEMinus (letterWord bs) τ u * finiteDilogEMinus (letterWord bs) τ v) := by
  obtain ⟨u₁, u₂, v₁, v₂, huEq, hvEq, huBound, hvBound, huZero, huvZero⟩ :=
    exists_fiveTerm_positive_representatives h.fixedPoint hu hv hv0
  have hvNonzero : fiveTermCharacteristicResidue (letterWord bs) v₁ v₂ ≠ 0 := by
    simpa only [hvEq] using hv0
  have huZero' : fiveTermCharacteristicResidue (letterWord bs) u₁ u₂ = 0 →
      u₁ = 0 ∧ u₂ = 0 := by
    intro hz
    exact huZero (by simpa only [huEq] using hz)
  have huvZero' : fiveTermCharacteristicResidue (letterWord bs) (u₁ + v₁) (u₂ + v₂) = 0 →
      u₁ + v₁ = letterWord bs 0 0 - 1 ∧ u₂ + v₂ = letterWord bs 0 1 := by
    intro hz
    apply huvZero
    simpa only [fiveTermCharacteristicResidue_add, huEq, hvEq] using hz
  have huvPos : 0 < fiveTermLatticeIndex (letterWord bs) u₁ u₂ +
      fiveTermLatticeIndex (letterWord bs) v₁ v₂ := by omega
  obtain ⟨hupper, hlower⟩ :=
    fiveTermLatticeArgument_source_rates h.fixedPoint u₁ u₂ v₁ v₂ huBound.2 huvPos
  let w := fiveTermLatticeArgument (letterWord bs) τ u₁ u₂
  let y := fiveTermLatticeArgument (letterWord bs) τ v₁ v₂
  let y' := fiveTermShiftedParameter (letterWord bs) τ y
  obtain ⟨x, F, hβx, hxδ, hxε, hF, hstable, hreg, hregRight⟩ :=
    exists_fiveTermWord_crossed_line h v₁ v₂ hvBound
  have hw := fiveTermLatticeArgument_exp_div h.fixedPoint u₁ u₂
  have hy := fiveTermLatticeArgument_exp_div h.fixedPoint v₁ v₂
  have hbridge := fiveTermWord_integral_telescope h (u₁ + 1) v₁ w y x
    hreg hregRight hupper hlower (by simpa [w] using hw) hy
  have hstrip := integral_fiveTermWordResidueSum_of_crossed h
    u₁ u₂ v₁ v₂ huBound hvBound hvNonzero x F hβx hxδ hxε hF hstable hreg
  have hshift := integral_fiveTermWordDifferenceSum_of_crossed h
    u₁ u₂ v₁ v₂ huBound hvBound hvNonzero huZero' huvZero'
      x F hβx hxε hF hstable hreg
  obtain ⟨b, hb, hbsub⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset).1 (hstrip.and hshift)
  obtain ⟨r, hr0, hrb, hrplus, hrminus⟩ :=
    exists_fiveTermWord_regular_radius h y' b hb
  obtain ⟨hstripR, hshiftR⟩ := hbsub ⟨hr0, hrb⟩
  have hshiftR := hshiftR hrplus hrminus
  rw [← hbridge] at hstripR
  have hmain := hshiftR.symm.trans hstripR
  rw [fiveTermWord_crossed_prefactor_eq h] at hmain
  have hresult := fiveTermWord_normalize h _ _ _ hmain
  rw [fiveTermCharacteristicResidue_add, huEq, hvEq] at hresult
  exact hresult

/-- **[RW26, Radchenko, Wheeler (2026), Theorem 2, `thm:fg.equs`, equation (7), `eq:Fgpm.5term`]
along a letter word**: the finite five-term relation at an attractive fixed point of
`γ = ∏_j T^{b_j}S` for all `u, v ∈ G` not both zero. -/
@[source "RW26, equation (7), p. 3, eq:Fgpm.5term (letter words)"]
theorem finiteDilogFiveTerm_letterWord {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) [NeZero (finiteDilogOrder (letterWord bs))]
    {u v : Fin 2 → ZMod (finiteDilogOrder (letterWord bs))}
    (hu : u ∈ finiteDilogGroup (letterWord bs)) (hv : v ∈ finiteDilogGroup (letterWord bs))
    (huv : (u, v) ≠ (0, 0)) :
    (1 / (Real.sqrt (finiteDilogOrder (letterWord bs)) : ℂ)) *
        ∑ x : finiteDilogGroup (letterWord bs),
          fixedBicharacter (letterWord bs) (finiteDilogOrder (letterWord bs)) x u *
            (finiteDilogE (letterWord bs) τ x / finiteDilogEMinus (letterWord bs) τ (x + v)) =
      finiteDilogE (letterWord bs) τ (u + v) /
        (finiteDilogEMinus (letterWord bs) τ u * finiteDilogEMinus (letterWord bs) τ v) := by
  by_cases hv0 : v = 0
  · subst v
    have hu0 : u ≠ 0 := by
      intro hz
      exact huv (by simp [hz])
    let M := fixedMetricGroup (letterWord bs) (finiteDilogOrder (letterWord bs))
      (det_sub_one_eq_neg_finiteDilogOrder h.fixedPoint)
    let E : finiteDilogGroup (letterWord bs) → ℂ := fun x => finiteDilogE (letterWord bs) τ x
    let Fm : finiteDilogGroup (letterWord bs) → ℂ :=
      fun x => finiteDilogEMinus (letterWord bs) τ x
    have hzero := M.fiveTerm_zero_right (E := E) (Fm := Fm)
      (by
        intro x
        simpa only [M, E, Fm, fixedMetricGroup_gaussian, AddSubgroup.coe_neg] using
          finiteDilogE_mul_EMinus_neg h.fixedPoint x.property)
      (by
        intro x hx
        exact finiteDilogEMinus_of_ne_zero h.fixedPoint
          (fun hz => hx (Subtype.ext hz)))
      (by
        simpa only [M, E, fixedMetricGroup_sqrtCard, AddSubgroup.coe_zero] using
          finiteDilogE_zero_sq h.fixedPoint)
      (u := ⟨u, hu⟩) (fun hz => hu0 (congrArg Subtype.val hz))
    simpa only [M, E, Fm, fixedMetricGroup_sqrtCard, fixedMetricGroup_bichar,
      inv_eq_one_div, AddSubgroup.coe_add, AddSubgroup.coe_zero, add_zero] using hzero
  · exact finiteDilogFiveTerm_letterWord_of_ne_zero_right h hu hv hv0

end SIC

end
