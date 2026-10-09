/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Quadratic.Towers

/-!
# Constructing the Fundamental Positive-Norm Unit

The canonical oriented minimal positive-norm fundamental unit.

This file constructs the distinguished unit of [AFK25, Definition 1.22,
`dfn:fundamentalTotallyPositiveUnit`] from exact real quadratic field data. Mathlib's rank-one
Dirichlet fundamental-system lift is first inverted and signed so that its selected real value
exceeds one. It is then squared exactly when its field norm is negative. The resulting unit has norm
one, is greater than one at the selected real place, and is minimal among all units with those two
properties.

Thus `RealQuadraticFieldData.toRealQuadraticUnitData` discharges the fundamental-unit existence
part of the arithmetic shortcut. `SICs.Quadratic.RankOneFields` constructs the concrete rank-one
quadratic field, and `SICs.Quadratic.Discriminants` supplies the general theorem that its
number-field discriminant is fundamental.

## Main results

- `RealQuadraticFieldData.positiveRaw`: the positively oriented Dirichlet generator.
- `RealQuadraticFieldData.epsilon`: the resulting positive-norm fundamental unit.
- `RealQuadraticFieldData.epsilon_isFundamental`: the exact AFK minimality theorem.
- `RealQuadraticFieldData.toRealQuadraticUnitData`: the canonical unit-data constructor.

## References

- [AFK25, Definition 1.22, `dfn:fundamentalTotallyPositiveUnit`]
- Dirichlet's unit theorem, as formalized in Mathlib
-/

noncomputable section

open scoped NumberField

namespace SIC

open NumberField NumberField.InfinitePlace

namespace RealQuadraticFieldData

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]

/-! ### Oriented Dirichlet generator

The rank-one Dirichlet generator is inverted when necessary and then signed so its selected real
value exceeds one.  Injectivity of the chosen embedding transfers the resulting power
classification back to units. -/

/-- The selected signed real value of a unit. -/
noncomputable def selectedReal (F : RealQuadraticFieldData K)
    (u : (NumberField.RingOfIntegers K)ˣ) : ℝ :=
  realEmbeddingAt K F.place (u : K)

/-- Selected real values commute with inversion of units. -/
lemma selectedReal_inv (F : RealQuadraticFieldData K)
    (u : (NumberField.RingOfIntegers K)ˣ) :
    F.selectedReal u⁻¹ = (F.selectedReal u)⁻¹ := by
  unfold selectedReal
  rw [← zpow_neg_one u, NumberField.Units.coe_zpow, zpow_neg_one, map_inv₀]

/-- Selected real values commute with negation of units. -/
lemma selectedReal_neg (F : RealQuadraticFieldData K)
    (u : (NumberField.RingOfIntegers K)ˣ) :
    F.selectedReal (-u) = -F.selectedReal u := by
  unfold selectedReal
  change (realEmbeddingAt K F.place) ((-(u : NumberField.RingOfIntegers K) :
    NumberField.RingOfIntegers K) : K) = _
  simp

/-- Selected real values commute with integral powers of units. -/
lemma selectedReal_zpow (F : RealQuadraticFieldData K)
    (u : (NumberField.RingOfIntegers K)ˣ) (k : ℤ) :
    F.selectedReal (u ^ k) = F.selectedReal u ^ k := by
  unfold selectedReal
  rw [NumberField.Units.coe_zpow, map_zpow₀]

/-- Selected real values commute with natural powers of units. -/
lemma selectedReal_pow (F : RealQuadraticFieldData K)
    (u : (NumberField.RingOfIntegers K)ˣ) (n : ℕ) :
    F.selectedReal (u ^ n) = F.selectedReal u ^ n := by
  unfold selectedReal
  rw [NumberField.Units.coe_pow, map_pow]

/-- The selected-real-value map on units is injective. -/
lemma selectedReal_injective (F : RealQuadraticFieldData K) :
    Function.Injective F.selectedReal := by
  intro u v huv
  apply NumberField.Units.coe_injective K
  apply (realEmbeddingAt K F.place).injective
  exact huv

/-- The selected signed real value of the raw rank-one Dirichlet generator. -/
noncomputable def rawReal (F : RealQuadraticFieldData K) : ℝ :=
  F.selectedReal F.rawFundamentalUnit

/-- The raw Dirichlet generator has nonzero selected real value. -/
lemma rawReal_ne_zero (F : RealQuadraticFieldData K) : F.rawReal ≠ 0 := by
  exact map_ne_zero (realEmbeddingAt K F.place) |>.mpr
    (NumberField.Units.coe_ne_zero F.rawFundamentalUnit)

/-- The selected absolute value of the raw Dirichlet generator is not one. -/
lemma abs_rawReal_ne_one (F : RealQuadraticFieldData K) : |F.rawReal| ≠ 1 := by
  intro h
  have hvalue : F.rawReal = 1 ∨ F.rawReal = -1 :=
    (abs_eq (zero_le_one : (0 : ℝ) ≤ 1)).mp h
  apply F.rawFundamentalUnit_not_mem_torsion
  rw [NumberField.Units.mem_torsion K]
  intro w
  rcases hvalue with hvalue | hvalue
  · have hu : F.rawFundamentalUnit = 1 := by
      apply F.selectedReal_injective
      simpa [rawReal, selectedReal] using hvalue
    simp [hu]
  · have hu : F.rawFundamentalUnit = -1 := by
      apply F.selectedReal_injective
      simpa [rawReal, selectedReal] using hvalue
    rw [hu]
    rw [← norm_embedding_of_isReal
      (NumberField.IsTotallyReal.isReal w) ((-1 : (NumberField.RingOfIntegers K)ˣ) : K)]
    simp

/-- A positive signed representative of a raw integral power has value equal to the
corresponding power of the raw absolute value. -/
lemma selectedReal_eq_abs_rawReal_zpow_of_pos (F : RealQuadraticFieldData K)
    (x : (NumberField.RingOfIntegers K)ˣ) (k : ℤ)
    (hx : x = F.rawFundamentalUnit ^ k ∨ x = -(F.rawFundamentalUnit ^ k))
    (hpos : 0 < F.selectedReal x) :
    F.selectedReal x = |F.rawReal| ^ k := by
  rcases hx with rfl | rfl
  · have hpraw : F.selectedReal (F.rawFundamentalUnit ^ k) = F.rawReal ^ k := by
      rw [F.selectedReal_zpow]
      rfl
    rw [hpraw] at hpos
    rw [F.selectedReal_zpow]
    change F.rawReal ^ k = |F.rawReal| ^ k
    rw [← abs_of_pos hpos, abs_zpow]
  · have hpraw : F.selectedReal (-(F.rawFundamentalUnit ^ k)) = -(F.rawReal ^ k) := by
      rw [F.selectedReal_neg, F.selectedReal_zpow]
      rfl
    rw [hpraw] at hpos
    rw [F.selectedReal_neg, F.selectedReal_zpow]
    change -(F.rawReal ^ k) = |F.rawReal| ^ k
    rw [← abs_of_pos hpos, abs_neg, abs_zpow]

/-- Invert the raw generator exactly when its selected absolute value is below one. -/
noncomputable def expansiveRaw (F : RealQuadraticFieldData K) :
    (NumberField.RingOfIntegers K)ˣ :=
  if 1 < |F.rawReal| then F.rawFundamentalUnit else F.rawFundamentalUnit⁻¹

/-- Change the sign of the expansive generator when needed to make its selected value positive. -/
noncomputable def positiveRaw (F : RealQuadraticFieldData K) :
    (NumberField.RingOfIntegers K)ˣ :=
  if 0 < F.selectedReal F.expansiveRaw then F.expansiveRaw else -F.expansiveRaw

/-- The absolute selected value of the expansive generator is greater than one. -/
lemma one_lt_abs_selectedReal_expansiveRaw (F : RealQuadraticFieldData K) :
    1 < |F.selectedReal F.expansiveRaw| := by
  by_cases h : 1 < |F.rawReal|
  · unfold expansiveRaw
    rw [ite_eq_left h]
    change 1 < |F.rawReal|
    exact h
  · have hpos : 0 < |F.rawReal| := abs_pos.mpr F.rawReal_ne_zero
    have hlt : |F.rawReal| < 1 :=
      lt_of_le_of_ne (le_of_not_gt h) F.abs_rawReal_ne_one
    unfold expansiveRaw
    rw [ite_eq_right h, F.selectedReal_inv, abs_inv]
    exact (one_lt_inv₀ hpos).mpr hlt

/-- The positively oriented generator has selected value equal to the absolute value of the
expansive generator. -/
lemma selectedReal_positiveRaw_eq_abs (F : RealQuadraticFieldData K) :
    F.selectedReal F.positiveRaw = |F.selectedReal F.expansiveRaw| := by
  by_cases h : 0 < F.selectedReal F.expansiveRaw
  · unfold positiveRaw
    rw [ite_eq_left h]
    exact (abs_of_pos h).symm
  · have hne : F.selectedReal F.expansiveRaw ≠ 0 := by
      unfold selectedReal
      exact map_ne_zero (realEmbeddingAt K F.place) |>.mpr
        (NumberField.Units.coe_ne_zero F.expansiveRaw)
    have hneg : F.selectedReal F.expansiveRaw < 0 :=
      lt_of_le_of_ne (le_of_not_gt h) hne
    unfold positiveRaw
    rw [ite_eq_right h, F.selectedReal_neg]
    exact (abs_of_neg hneg).symm

/-- The positively oriented raw generator is greater than one. -/
lemma one_lt_selectedReal_positiveRaw (F : RealQuadraticFieldData K) :
    1 < F.selectedReal F.positiveRaw := by
  rw [F.selectedReal_positiveRaw_eq_abs]
  exact F.one_lt_abs_selectedReal_expansiveRaw

/-- The positive generator has value `|raw|` or its inverse according as `|raw|` is greater or
less than one. -/
lemma selectedReal_positiveRaw_eq (F : RealQuadraticFieldData K) :
    F.selectedReal F.positiveRaw =
      if 1 < |F.rawReal| then |F.rawReal| else |F.rawReal|⁻¹ := by
  rw [F.selectedReal_positiveRaw_eq_abs]
  by_cases h : 1 < |F.rawReal|
  · unfold expansiveRaw
    rw [ite_eq_left h, ite_eq_left h]
    rfl
  · unfold expansiveRaw
    rw [ite_eq_right h, ite_eq_right h, F.selectedReal_inv, abs_inv]
    rfl

/-- Every unit greater than one at the selected embedding is a positive natural power of the
positively oriented raw Dirichlet generator. The standard consequence of Dirichlet's unit theorem
in the real quadratic case: the unit group modulo torsion is infinite cyclic, so the units above
one at a fixed real place are exactly the positive powers of its generator. -/
lemma exists_eq_positiveRaw_pow (F : RealQuadraticFieldData K)
    (x : (NumberField.RingOfIntegers K)ˣ) (hx : 1 < F.selectedReal x) :
    ∃ n : ℕ, 0 < n ∧ x = F.positiveRaw ^ n := by
  obtain ⟨k, hk⟩ := F.exists_eq_rawFundamentalUnit_zpow_or_neg x
  have hxpos : 0 < F.selectedReal x := lt_trans Real.zero_lt_one hx
  have hxvalue : F.selectedReal x = |F.rawReal| ^ k :=
    F.selectedReal_eq_abs_rawReal_zpow_of_pos x k hk hxpos
  have hqpos : 0 < |F.rawReal| := abs_pos.mpr F.rawReal_ne_zero
  by_cases hq : 1 < |F.rawReal|
  · have hkpos : 0 < k := (one_lt_zpow_iff_right₀ hq).mp (hxvalue ▸ hx)
    obtain ⟨n, hkn⟩ := Int.eq_ofNat_of_zero_le (le_of_lt hkpos)
    have hn : 0 < n := by omega
    refine ⟨n, hn, F.selectedReal_injective ?_⟩
    rw [F.selectedReal_pow, F.selectedReal_positiveRaw_eq, ite_eq_left hq, hxvalue,
      hkn, zpow_natCast]
  · have hqne : |F.rawReal| ≠ 1 := F.abs_rawReal_ne_one
    have hqlt : |F.rawReal| < 1 := lt_of_le_of_ne (le_of_not_gt hq) hqne
    have hkneg : k < 0 :=
      (one_lt_zpow_iff_right_of_lt_one₀ hqpos hqlt).mp (hxvalue ▸ hx)
    obtain ⟨n, hnk⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.mpr (le_of_lt hkneg))
    have hn : 0 < n := by omega
    have hk_eq : k = -(n : ℤ) := by omega
    refine ⟨n, hn, F.selectedReal_injective ?_⟩
    rw [F.selectedReal_pow, F.selectedReal_positiveRaw_eq, ite_eq_right hq, hxvalue,
      hk_eq, zpow_neg, zpow_natCast, inv_pow]

/-! ### Positive norm and minimality

If the oriented generator has norm `-1`, squaring it produces the least norm-one unit above one;
otherwise the generator itself does.  This proves the minimality condition of [AFK25, Definition
1.22, `dfn:fundamentalTotallyPositiveUnit`]. -/

/-- The positively oriented generator has field norm `1` or `-1`. -/
lemma norm_positiveRaw_eq_one_or_neg_one (F : RealQuadraticFieldData K) :
    Algebra.norm ℚ (F.positiveRaw : K) = 1 ∨
      Algebra.norm ℚ (F.positiveRaw : K) = -1 :=
  (abs_eq (zero_le_one : (0 : ℚ) ≤ 1)).mp
    (NumberField.Units.norm K F.positiveRaw)

/-- Use the oriented generator itself when its norm is positive, and its square otherwise. -/
noncomputable def epsilon (F : RealQuadraticFieldData K) :
    (NumberField.RingOfIntegers K)ˣ :=
  if Algebra.norm ℚ (F.positiveRaw : K) = 1 then F.positiveRaw else F.positiveRaw ^ 2

/-- The constructed fundamental unit has positive field norm. -/
lemma epsilon_norm_eq_one (F : RealQuadraticFieldData K) :
    Algebra.norm ℚ (F.epsilon : K) = 1 := by
  by_cases hnorm : Algebra.norm ℚ (F.positiveRaw : K) = 1
  · simp [epsilon, hnorm]
  · have hnorm_neg : Algebra.norm ℚ (F.positiveRaw : K) = -1 :=
      F.norm_positiveRaw_eq_one_or_neg_one.resolve_left hnorm
    unfold epsilon
    rw [ite_eq_right hnorm]
    rw [show ((F.positiveRaw ^ 2 : (NumberField.RingOfIntegers K)ˣ) : K) =
      (F.positiveRaw : K) ^ 2 from NumberField.Units.coe_pow F.positiveRaw 2,
      map_pow, hnorm_neg]
    norm_num

/-- The constructed positive-norm unit is greater than one at the selected place. -/
lemma one_lt_selectedReal_epsilon (F : RealQuadraticFieldData K) :
    1 < F.selectedReal F.epsilon := by
  by_cases hnorm : Algebra.norm ℚ (F.positiveRaw : K) = 1
  · simpa [epsilon, hnorm] using F.one_lt_selectedReal_positiveRaw
  · unfold epsilon
    rw [ite_eq_right hnorm, F.selectedReal_pow]
    nlinarith [F.one_lt_selectedReal_positiveRaw]

/-- The constructed unit is minimal among positive-norm units greater than one at the selected
real embedding. -/
lemma epsilon_minimal (F : RealQuadraticFieldData K)
    (u : (NumberField.RingOfIntegers K)ˣ)
    (hu_norm : Algebra.norm ℚ (u : K) = 1)
    (hu_gt_one : 1 < F.selectedReal u) :
    F.selectedReal F.epsilon ≤ F.selectedReal u := by
  obtain ⟨n, hn, hu⟩ := F.exists_eq_positiveRaw_pow u hu_gt_one
  have hbase : 1 ≤ F.selectedReal F.positiveRaw :=
    le_of_lt F.one_lt_selectedReal_positiveRaw
  by_cases hnorm : Algebra.norm ℚ (F.positiveRaw : K) = 1
  · rw [epsilon, ite_eq_left hnorm, hu, F.selectedReal_pow]
    simpa using pow_le_pow_right₀ hbase (show 1 ≤ n by omega)
  · have hn_ne_one : n ≠ 1 := by
      intro hn_one
      subst n
      simp only [pow_one] at hu
      subst u
      exact hnorm hu_norm
    have hn_two : 2 ≤ n := by omega
    rw [epsilon, ite_eq_right hnorm, hu, F.selectedReal_pow, F.selectedReal_pow]
    exact pow_le_pow_right₀ hbase hn_two

/-- The canonically constructed unit is the oriented fundamental positive-norm unit, in the exact
sense of `IsFundamentalPositiveNormUnit`. -/
lemma epsilon_isFundamental (F : RealQuadraticFieldData K) :
    IsFundamentalPositiveNormUnit F.place F.epsilon := by
  refine ⟨F.epsilon_norm_eq_one, ?_, ?_⟩
  · exact F.one_lt_selectedReal_epsilon
  · intro u hu_norm hu_one
    exact F.epsilon_minimal u hu_norm hu_one

/-- Equip exact real-quadratic field data with its canonical unit and the proof
`epsilon_isFundamental`, producing the tower input `RealQuadraticUnitData`. -/
noncomputable def toRealQuadraticUnitData (F : RealQuadraticFieldData K) :
    RealQuadraticUnitData K where
  toRealQuadraticFieldData := F
  epsilon := F.epsilon
  epsilon_isFundamental := F.epsilon_isFundamental

end RealQuadraticFieldData

end SIC

end
