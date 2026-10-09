/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Quadratic.RealFields
import Mathlib.Data.PNat.Basic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import SICs.Source

/-!
# Real Quadratic Unit and Tower Data

Fundamental units, the rank-one Dirichlet decomposition, and conductor and dimension tower data.

This file equips the oriented quadratic field of `SICs.Quadratic.RealFields` with the
fundamental-unit data underlying the dimension towers of [AFK25]. Inequalities are interpreted
through the chosen real place, and the distinguished unit satisfies the global minimality
condition from [AFK25, Definition 1.22, `dfn:fundamentalTotallyPositiveUnit`].

The file also gives relational, positive-index interfaces for the integer conductor and
trace-dimension values intended to be `f_j` and `d_j`. These interfaces preserve the unsquared
conductor equation and therefore its sign. The companion
module `SICs.Quadratic.TowerValues` constructs these rank-one values at every positive index, and
`SICs.Quadratic.DimensionGrids` uses them to construct the complete rank and dimension grids.

## Main definitions

- `IsFundamentalPositiveNormUnit`: the characterization of the AFK fundamental unit.
- `RealQuadraticUnitData`: a degree-two totally real field with its oriented fundamental unit.
- `RealQuadraticUnitData.exists_eq_epsilon_pow`: every norm-one unit greater than one at the
  selected real place is a positive power of that fundamental unit.
- `RealQuadraticUnitData.IsConductorSequenceValue`: the exact equation defining `f_j`.
- `RealQuadraticUnitData.IsDimensionTowerValue`: the rank-one expression defining `d_j`.
- `RealQuadraticUnitData.RankOneLevel`: exact integral data at one positive tower index.

## References

- [AFK25, Definition 1.22, `dfn:fundamentalTotallyPositiveUnit`] and [AFK25, Definition 1.23,
  `dfn:sequenceofconductors`] and [AFK25, Definition 1.24, `dfn:fjrjmdjm`]
- [AFK25, Lemma 4.3, `lem:towerbasic`]
- [AFK25, Theorem 4.20, `thm:nrddjmrjm`]
- Dirichlet's unit theorem, as formalized in Mathlib
-/

noncomputable section

namespace SIC

open NumberField NumberField.InfinitePlace

/-! ### Oriented fundamental units

The unit data equip an oriented real quadratic field with a positive-norm fundamental unit
characterized by minimality.  This is the exact arithmetic data of
[AFK25, Definition 1.22, `dfn:fundamentalTotallyPositiveUnit`, and
Definition 1.23, `dfn:sequenceofconductors`]. -/

/-- A unit is the fundamental positive-norm unit at `w` when its field norm is one, its selected
real value is greater than one, and no other norm-one unit greater than one has smaller value.
This is the literal minimality characterization in [AFK25, Definition 1.22,
`dfn:fundamentalTotallyPositiveUnit`]. -/
@[source "AFK25, Definition 1.22, p. 13, dfn:fundamentalTotallyPositiveUnit" (symbol := "ε")]
def IsFundamentalPositiveNormUnit
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (w : InfinitePlace K) (epsilon : (NumberField.RingOfIntegers K)ˣ) : Prop :=
  Algebra.norm ℚ (epsilon : K) = 1 ∧
    1 < realEmbeddingAt K w (epsilon : K) ∧
    ∀ u : (NumberField.RingOfIntegers K)ˣ,
      Algebra.norm ℚ (u : K) = 1 →
      1 < realEmbeddingAt K w (u : K) →
      realEmbeddingAt K w (epsilon : K) ≤ realEmbeddingAt K w (u : K)

/-- A fundamental positive-norm unit has field norm one. -/
lemma IsFundamentalPositiveNormUnit.norm_eq_one
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {w : InfinitePlace K} {epsilon : (NumberField.RingOfIntegers K)ˣ}
    (h : IsFundamentalPositiveNormUnit w epsilon) :
    Algebra.norm ℚ (epsilon : K) = 1 :=
  h.1

/-- A fundamental positive-norm unit is greater than one at the selected real place. -/
lemma IsFundamentalPositiveNormUnit.one_lt
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {w : InfinitePlace K} {epsilon : (NumberField.RingOfIntegers K)ˣ}
    (h : IsFundamentalPositiveNormUnit w epsilon) :
    1 < realEmbeddingAt K w (epsilon : K) :=
  h.2.1

/-- A fundamental positive-norm unit is minimal among norm-one units greater than one. -/
lemma IsFundamentalPositiveNormUnit.minimal
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {w : InfinitePlace K} {epsilon : (NumberField.RingOfIntegers K)ˣ}
    (h : IsFundamentalPositiveNormUnit w epsilon)
    (u : (NumberField.RingOfIntegers K)ˣ) (hnorm : Algebra.norm ℚ (u : K) = 1)
    (hone : 1 < realEmbeddingAt K w (u : K)) :
    realEmbeddingAt K w (epsilon : K) ≤ realEmbeddingAt K w (u : K) :=
  h.2.2 u hnorm hone

/-- Exact field and fundamental-unit data preceding the conductor and dimension grids in
[AFK25]. -/
structure RealQuadraticUnitData (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] extends RealQuadraticFieldData K where
  /-- The distinguished unit in the ring of integers. -/
  epsilon : (NumberField.RingOfIntegers K)ˣ
  /-- The distinguished unit has the exact minimality property `IsFundamentalPositiveNormUnit`. -/
  epsilon_isFundamental : IsFundamentalPositiveNormUnit place epsilon

/-- The field underlying the unit data has fundamental discriminant; see
`RealQuadraticFieldData.discr_fundamental`. -/
lemma RealQuadraticUnitData.discr_fundamental
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (T : RealQuadraticUnitData K) : IsFundamentalDiscriminant (NumberField.discr K) :=
  T.toRealQuadraticFieldData.discr_fundamental

namespace RealQuadraticFieldData

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]

/-! ### The rank-one Dirichlet unit group

The two real places give unit rank one. Mathlib's fundamental system and torsion decomposition
then express every unit as a power of one unit, up to sign. -/

/-- A real quadratic field has Dirichlet unit rank one. -/
lemma unitRank_eq_one (F : RealQuadraticFieldData K) : NumberField.Units.rank K = 1 := by
  rw [NumberField.Units.rank, F.card_infinitePlace_eq_two]

/-- The unique index of Mathlib's Dirichlet fundamental system when the unit rank is one. -/
noncomputable def fundIndex (F : RealQuadraticFieldData K) :
    Fin (NumberField.Units.rank K) :=
  ⟨0, by rw [F.unitRank_eq_one]; omega⟩

/-- Mathlib's arbitrary fundamental-system lift in unit rank one.

This unit has no prescribed sign at the selected real place and need not have positive norm. -/
noncomputable def rawFundamentalUnit (F : RealQuadraticFieldData K) :
    (NumberField.RingOfIntegers K)ˣ :=
  NumberField.Units.fundSystem K F.fundIndex

/-- The raw rank-one Dirichlet unit is not torsion. -/
lemma rawFundamentalUnit_not_mem_torsion (F : RealQuadraticFieldData K) :
    F.rawFundamentalUnit ∉ NumberField.Units.torsion K := by
  intro htor
  have hzero : Additive.ofMul
      (QuotientGroup.mk F.rawFundamentalUnit :
        (NumberField.RingOfIntegers K)ˣ ⧸ NumberField.Units.torsion K) = 0 := by
    rw [ofMul_eq_zero, QuotientGroup.eq_one_iff]
    exact htor
  change Additive.ofMul
      (QuotientGroup.mk (NumberField.Units.fundSystem K F.fundIndex)) = 0 at hzero
  rw [NumberField.Units.fundSystem_mk] at hzero
  let _ : Module ℤ
      (Additive ((NumberField.RingOfIntegers K)ˣ ⧸ NumberField.Units.torsion K)) :=
    AddCommGroup.toIntModule
      (Additive ((NumberField.RingOfIntegers K)ˣ ⧸ NumberField.Units.torsion K))
  have hrepr := congrArg
    (fun v => (NumberField.Units.basisModTorsion K).repr v F.fundIndex) hzero
  simp at hrepr

/-- In a totally real number field every torsion unit is `1` or `-1`. Standard: a root of unity in
a totally real field is real, and the only real roots of unity are `±1`. -/
lemma unit_eq_one_or_neg_one_of_mem_torsion (F : RealQuadraticFieldData K)
    (u : (NumberField.RingOfIntegers K)ˣ) (hu : u ∈ NumberField.Units.torsion K) :
    u = 1 ∨ u = -1 := by
  have hw := NumberField.IsTotallyReal.isReal F.place
  have hplace : F.place (u : K) = 1 := (NumberField.Units.mem_torsion K).mp hu F.place
  have hnorm := norm_embedding_of_isReal hw (u : K)
  rw [hplace] at hnorm
  have habs : |realEmbeddingAt K F.place (u : K)| = 1 := by
    simpa [realEmbeddingAt, Real.norm_eq_abs] using hnorm
  rcases (abs_eq (zero_le_one : (0 : ℝ) ≤ 1)).mp habs with hvalue | hvalue
  · left
    apply NumberField.Units.coe_injective K
    apply (realEmbeddingAt K F.place).injective
    simpa using hvalue
  · right
    apply NumberField.Units.coe_injective K
    apply (realEmbeddingAt K F.place).injective
    simpa using hvalue

/-- Every unit is a torsion unit times an integral power of the single raw Dirichlet unit. -/
lemma exists_eq_torsion_mul_rawFundamentalUnit_zpow (F : RealQuadraticFieldData K)
    (x : (NumberField.RingOfIntegers K)ˣ) :
    ∃ (ζ : (NumberField.RingOfIntegers K)ˣ) (k : ℤ),
      ζ ∈ NumberField.Units.torsion K ∧ x = ζ * F.rawFundamentalUnit ^ k := by
  classical
  obtain ⟨⟨ζ, exponent⟩, hx, _⟩ := NumberField.Units.exist_unique_eq_mul_prod K x
  refine ⟨ζ, exponent F.fundIndex, ζ.property, ?_⟩
  rw [hx]
  congr 1
  rw [Finset.prod_eq_single F.fundIndex]
  · rfl
  · intro i _ hi
    exfalso
    apply hi
    apply Fin.ext
    change i.val = 0
    have hilower : 0 ≤ i.val := Nat.zero_le _
    have hiupper : i.val < 1 := by simpa [F.unitRank_eq_one] using i.isLt
    omega
  · simp

/-- Every unit is, up to sign, an integral power of the single raw Dirichlet unit. -/
lemma exists_eq_rawFundamentalUnit_zpow_or_neg (F : RealQuadraticFieldData K)
    (x : (NumberField.RingOfIntegers K)ˣ) :
    ∃ k : ℤ, x = F.rawFundamentalUnit ^ k ∨ x = -(F.rawFundamentalUnit ^ k) := by
  obtain ⟨ζ, k, hζ, hx⟩ := F.exists_eq_torsion_mul_rawFundamentalUnit_zpow x
  rcases F.unit_eq_one_or_neg_one_of_mem_torsion ζ hζ with rfl | rfl
  · exact ⟨k, Or.inl (by simpa using hx)⟩
  · exact ⟨k, Or.inr (by simpa using hx)⟩

end RealQuadraticFieldData

namespace RealQuadraticUnitData

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]

/-- The discriminant of the totally real number field underlying the unit data is positive. -/
lemma discr_pos (T : RealQuadraticUnitData K) : 0 < NumberField.discr K :=
  T.toRealQuadraticFieldData.discr_pos

/-- The selected real value of the fundamental positive-norm unit. -/
noncomputable def epsilonReal (T : RealQuadraticUnitData K) : ℝ :=
  realEmbeddingAt K T.place (T.epsilon : K)

/-- The selected fundamental unit has field norm one. -/
lemma epsilon_norm_eq_one (T : RealQuadraticUnitData K) :
    Algebra.norm ℚ (T.epsilon : K) = 1 :=
  T.epsilon_isFundamental.norm_eq_one

/-- The selected real value of the fundamental unit is greater than one. -/
lemma one_lt_epsilonReal (T : RealQuadraticUnitData K) : 1 < T.epsilonReal :=
  T.epsilon_isFundamental.one_lt

/-- The selected real value of the fundamental unit is positive. -/
lemma epsilonReal_pos (T : RealQuadraticUnitData K) : 0 < T.epsilonReal :=
  lt_trans Real.zero_lt_one T.one_lt_epsilonReal

/-- Every positive-index power of the selected real unit value is greater than one. -/
lemma one_lt_epsilonReal_pow (T : RealQuadraticUnitData K) (j : ℕ+) :
    1 < T.epsilonReal ^ (j : ℕ) :=
  one_lt_pow₀ T.one_lt_epsilonReal (ne_of_gt j.property)

/-- Every positive-index power of the selected real unit value is positive. -/
lemma epsilonReal_pow_pos (T : RealQuadraticUnitData K) (j : ℕ+) :
    0 < T.epsilonReal ^ (j : ℕ) :=
  lt_trans Real.zero_lt_one (T.one_lt_epsilonReal_pow j)

/-- Every norm-one unit greater than one at the selected real place is a positive natural power
of the distinguished fundamental unit.

This is the rank-one unit-group step used in the proof of
[AFK25, Theorem 3.20, `thm:dimtowunique`], which the paper attributes to
[14, Appleby, Flammia, McConnell, Yard (2020), Lemma 4, `pellemma`]. The proof uses only the global
minimality in `IsFundamentalPositiveNormUnit` and the Archimedean
property of `ℝ`.
-/
lemma exists_eq_epsilon_pow (T : RealQuadraticUnitData K)
    (u : (NumberField.RingOfIntegers K)ˣ)
    (hu_norm : Algebra.norm ℚ (u : K) = 1)
    (hu_one : 1 < realEmbeddingAt K T.place (u : K)) :
    ∃ j : ℕ+, u = T.epsilon ^ (j : ℕ) := by
  obtain ⟨n, hn_lower, hn_upper⟩ :=
    exists_nat_pow_near (le_of_lt hu_one) T.one_lt_epsilonReal
  let v : (NumberField.RingOfIntegers K)ˣ := u * T.epsilon ^ (-(n : ℤ))
  have hv_coe : (v : K) = (u : K) * (T.epsilon : K) ^ (-(n : ℤ)) := by
    dsimp [v]
    rw [map_mul, NumberField.Units.coe_zpow]
  have hv_real : realEmbeddingAt K T.place (v : K) =
      realEmbeddingAt K T.place (u : K) * T.epsilonReal ^ (-(n : ℤ)) := by
    rw [hv_coe, map_mul, map_zpow₀]
    rfl
  have hepsilon_pow_pos : 0 < T.epsilonReal ^ n := pow_pos T.epsilonReal_pos n
  have hv_lower : 1 ≤ realEmbeddingAt K T.place (v : K) := by
    rw [hv_real, zpow_neg, zpow_natCast]
    apply (le_div_iff₀ hepsilon_pow_pos).2
    simpa using hn_lower
  have hv_upper : realEmbeddingAt K T.place (v : K) < T.epsilonReal := by
    rw [hv_real, zpow_neg, zpow_natCast]
    apply (div_lt_iff₀ hepsilon_pow_pos).2
    simpa [pow_succ, mul_comm] using hn_upper
  have hv_norm : Algebra.norm ℚ (v : K) = 1 := by
    rw [hv_coe, map_mul, Algebra.norm_zpow, hu_norm, T.epsilon_norm_eq_one]
    simp
  have hv_not_one_lt : ¬1 < realEmbeddingAt K T.place (v : K) := by
    intro hv_one
    exact (not_le_of_gt hv_upper)
      (T.epsilon_isFundamental.minimal v hv_norm hv_one)
  have hv_eq_one : realEmbeddingAt K T.place (v : K) = 1 :=
    le_antisymm (le_of_not_gt hv_not_one_lt) hv_lower
  have hu_real : realEmbeddingAt K T.place (u : K) = T.epsilonReal ^ n := by
    rw [hv_real, zpow_neg, zpow_natCast] at hv_eq_one
    exact (mul_inv_eq_one₀ (ne_of_gt hepsilon_pow_pos)).mp hv_eq_one
  have hu_eq : u = T.epsilon ^ n := by
    apply NumberField.Units.coe_injective K
    apply (realEmbeddingAt K T.place).injective
    calc
      realEmbeddingAt K T.place (u : K) = T.epsilonReal ^ n := hu_real
      _ = realEmbeddingAt K T.place ((T.epsilon : K) ^ n) := by
        rw [map_pow]
        rfl
      _ = realEmbeddingAt K T.place
          ((T.epsilon ^ n : (NumberField.RingOfIntegers K)ˣ) : K) := by
        rw [NumberField.Units.coe_pow]
  have hn_pos : 0 < n := by
    by_contra hn
    have hn_zero : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp at hu_real
    linarith
  exact ⟨⟨n, hn_pos⟩, hu_eq⟩

/-! ### Relational conductor and dimension values

The defining real equations for `f_j` and `d_j` are separated from their positive-integral
realizations.  This relational layer states exactly the conductor and dimension equations before
the canonical values are constructed. -/

/-- The real expression `ε^j + ε^(-j) + 1` for the rank-one dimension-tower value from
[AFK25, Lemma 4.3, `lem:towerbasic`, equation (4.4), `eq:towerbasic1`]. -/
noncomputable def dimensionValue (T : RealQuadraticUnitData K) (j : ℕ+) : ℝ :=
  T.epsilonReal ^ (j : ℕ) + (T.epsilonReal ^ (j : ℕ))⁻¹ + 1

/-- The real dimension expression is greater than three at every positive index. -/
lemma three_lt_dimensionValue (T : RealQuadraticUnitData K) (j : ℕ+) :
    3 < T.dimensionValue j := by
  let x := T.epsilonReal ^ (j : ℕ)
  have hx : 1 < x := T.one_lt_epsilonReal_pow j
  have hxne : x ≠ 0 := ne_of_gt (lt_trans Real.zero_lt_one hx)
  have hmul : x * x⁻¹ = 1 := mul_inv_cancel₀ hxne
  have hsquare : 0 < (x - 1) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr (ne_of_gt hx))
  rw [dimensionValue]
  change 3 < x + x⁻¹ + 1
  nlinarith

/-- `f` realizes the conductor-sequence value at the positive index `j` when it satisfies the
oriented, unsquared equation (1.37) from [AFK25, Definition 1.23, `dfn:sequenceofconductors`]. Using
`ℕ+` records both the
integrality and positivity asserted immediately after that definition. -/
@[source "AFK25, Definition 1.23, p. 14, dfn:sequenceofconductors" (symbol := "f_j")]
def IsConductorSequenceValue (T : RealQuadraticUnitData K) (j f : ℕ+) : Prop :=
  ((f : ℕ) : ℝ) * Real.sqrt (NumberField.discr K) =
    T.epsilonReal ^ (j : ℕ) - (T.epsilonReal ^ (j : ℕ))⁻¹

/-- `d` realizes the rank-one dimension-tower value at `j` when it equals `dimensionValue`. -/
def IsDimensionTowerValue (T : RealQuadraticUnitData K) (j : ℕ+) (d : ℕ) : Prop :=
  (d : ℝ) = T.dimensionValue j

/-- The positive-integer conductor value at a fixed index is unique. -/
lemma IsConductorSequenceValue.unique {T : RealQuadraticUnitData K} {j f g : ℕ+}
    (hf : T.IsConductorSequenceValue j f) (hg : T.IsConductorSequenceValue j g) : f = g := by
  have hsqrt : 0 < Real.sqrt (NumberField.discr K) := by
    exact Real.sqrt_pos.2 (by exact_mod_cast T.discr_pos)
  change ((f : ℕ) : ℝ) * Real.sqrt (NumberField.discr K) =
    T.epsilonReal ^ (j : ℕ) - (T.epsilonReal ^ (j : ℕ))⁻¹ at hf
  change ((g : ℕ) : ℝ) * Real.sqrt (NumberField.discr K) =
    T.epsilonReal ^ (j : ℕ) - (T.epsilonReal ^ (j : ℕ))⁻¹ at hg
  have hreal : (((f : ℕ) : ℝ)) = (g : ℕ) := by nlinarith [hf, hg]
  have hnat : (f : ℕ) = (g : ℕ) := by exact_mod_cast hreal
  exact Subtype.ext hnat

/-- The natural dimension value at a fixed index is unique. -/
lemma IsDimensionTowerValue.unique {T : RealQuadraticUnitData K} {j : ℕ+} {d e : ℕ}
    (hd : T.IsDimensionTowerValue j d) (he : T.IsDimensionTowerValue j e) : d = e := by
  change (d : ℝ) = T.dimensionValue j at hd
  change (e : ℝ) = T.dimensionValue j at he
  exact_mod_cast hd.trans he.symm

/-- Every natural dimension witness at a positive tower index is greater than three. -/
lemma IsDimensionTowerValue.three_lt {T : RealQuadraticUnitData K} {j : ℕ+} {d : ℕ}
    (hd : T.IsDimensionTowerValue j d) : 3 < d := by
  have hreal : (3 : ℝ) < d := by
    rw [hd]
    exact T.three_lt_dimensionValue j
  exact_mod_cast hreal

/-- Exact conductor and dimension data at one positive rank-one tower index.

This project-local bundle packages witnesses for `IsConductorSequenceValue` and
`IsDimensionTowerValue`. It is deliberately smaller than an `AdmissibleTriple`: it has no
rank-grid index `m`, does not package complete sequences, and makes no existence claim. -/
structure RankOneLevel (T : RealQuadraticUnitData K) (d : ℕ) where
  /-- The positive tower index. -/
  j : ℕ+
  /-- The positive integral conductor-sequence value at `j`. -/
  f : ℕ+
  /-- The conductor witness satisfies the unsquared defining equation. -/
  conductor_spec : T.IsConductorSequenceValue j f
  /-- The ambient natural dimension is the tower value at `j`. -/
  dimension_spec : T.IsDimensionTowerValue j d

/-- The dimension underlying a rank-one level is greater than three. -/
lemma RankOneLevel.three_lt {T : RealQuadraticUnitData K} {d : ℕ} (L : T.RankOneLevel d) :
    3 < d :=
  L.dimension_spec.three_lt

end RealQuadraticUnitData

end SIC

end
