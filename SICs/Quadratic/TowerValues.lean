/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Quadratic.Towers
import SICs.MatrixNotation

/-!
# Integral Values in a Real Quadratic Dimension Tower

Canonical conductor and trace-dimension values at every tower index.

This file constructs the positive integers `f_j` and natural trace-dimension values attached to
every positive power of the fundamental unit in [AFK25]. The conductor value is the absolute
determinant of the coordinates of `(1, ε^j)` in an integral basis. Basis change and a degree-two
Cayley–Hamilton calculation prove the exact oriented equation

`f_j √Δ₀ = ε^j - ε^(-j)`

and the trace formula

`d_j = ε^j + ε^(-j) + 1`.

Consequently, every positive index canonically supplies an exact
`RealQuadraticUnitData.RankOneLevel`. This proves integrality of the rank-one conductor and trace
expressions in [AFK25, Lemma 4.3, `lem:towerbasic`]. The companion module
`SICs.Quadratic.DimensionGrids` uses these values to construct the complete two-index rank and
dimension grids.

## Main results

- `RealQuadraticUnitData.canonicalConductor`: the positive integer `f_j`.
- `RealQuadraticUnitData.canonicalDimension`: the natural trace-dimension value intended to be
  `d_j`.
- `RealQuadraticUnitData.canonicalConductor_spec`: the unsquared equation (1.37).
- `RealQuadraticUnitData.canonicalDimension_spec`: the rank-one formula (4.4).
- `RealQuadraticUnitData.canonicalRankOneLevel`: exact integral tower data at every positive
  index.
- `RealQuadraticUnitData.RankOneLevel.radicand_eq`: the integer identity
  `(d + 1)(d - 3) = f_j² Δ₀`, with `RealQuadraticUnitData.canonicalConductor_sq_mul_discr` its
  specialization to the canonical values.

## References

- [AFK25, Definition 1.23, `dfn:sequenceofconductors`, equation (1.37)]
- [AFK25, Definition 4.2, `dfn:discriminantLevelj`, equation (4.1)]
- [AFK25, Lemma 4.3, `lem:towerbasic`, equations (4.3)–(4.5)]
-/

noncomputable section

open scoped NumberField Matrix

open scoped MatrixGroups

namespace SIC

namespace RealQuadraticUnitData

open Module NumberField

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]

/-! ### Integral-basis discriminants

The common rank-two basis from `SICs.Quadratic.DegreeTwoAlgebras` lets the pair `(1, ε^j)` be
compared by a determinant. Its discriminant differs from the field discriminant by the square of
that determinant. -/

/-- The common rank-two basis specialized to the ring of integers underlying the tower. -/
noncomputable def integralBasisFinTwo (T : RealQuadraticUnitData K) :
    Module.Basis (Fin 2) ℤ (NumberField.RingOfIntegers K) :=
  DegreeTwoAlgebra.basisFinTwo ℤ (NumberField.RingOfIntegers K) (by
    rw [NumberField.RingOfIntegers.rank, T.finrank_eq_two])

/-- The ordered pair `(1, ε^j)` in the ring of integers. -/
def powerPair (T : RealQuadraticUnitData K) (j : ℕ) :
    Fin 2 → NumberField.RingOfIntegers K :=
  ![1, (T.epsilon ^ j : (NumberField.RingOfIntegers K)ˣ)]

/-- The coordinate matrix of `(1, ε^j)` in the chosen integral basis. -/
noncomputable def powerPairMatrix (T : RealQuadraticUnitData K) (j : ℕ) :
    Mat(2, ℤ) :=
  T.integralBasisFinTwo.toMatrix (T.powerPair j)

/-- The absolute determinant of the coordinate matrix of `(1, ε^j)`. -/
noncomputable def conductorNat (T : RealQuadraticUnitData K) (j : ℕ) : ℕ :=
  Int.natAbs (T.powerPairMatrix j).det

/-- Integral basis change gives the square-factor relation between the pair discriminant and the
number-field discriminant. -/
lemma powerPair_discr (T : RealQuadraticUnitData K) (j : ℕ) :
    Algebra.discr ℤ (T.powerPair j) =
      (T.conductorNat j : ℤ) ^ 2 * NumberField.discr K := by
  let b := T.integralBasisFinTwo
  calc
    Algebra.discr ℤ (T.powerPair j) = Algebra.discr ℤ
        (b ᵥ* (b.toMatrix (T.powerPair j)).map
          (algebraMap ℤ (NumberField.RingOfIntegers K))) := by
      rw [Basis.toMatrix_map_vecMul]
    _ = (b.toMatrix (T.powerPair j)).det ^ 2 * Algebra.discr ℤ b :=
      Algebra.discr_of_matrix_vecMul b (b.toMatrix (T.powerPair j))
    _ = (T.conductorNat j : ℤ) ^ 2 * NumberField.discr K := by
      rw [NumberField.discr_eq_discr K b]
      simp only [conductorNat, powerPairMatrix, Int.natCast_natAbs, sq_abs]
      rfl

/-- Casting the integral pair discriminant gives the corresponding rational pair
discriminant. -/
lemma powerPair_discr_cast (T : RealQuadraticUnitData K) (j : ℕ) :
    (Algebra.discr ℤ (T.powerPair j) : ℚ) =
      Algebra.discr ℚ ![(1 : K), (T.epsilon : K) ^ j] := by
  have hmatrix : (Algebra.traceMatrix ℤ (T.powerPair j)).map (algebraMap ℤ ℚ) =
      Algebra.traceMatrix ℚ ![(1 : K), (T.epsilon : K) ^ j] := by
    ext i k
    simp only [Matrix.map_apply, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
    change ((Algebra.trace ℤ (NumberField.RingOfIntegers K)
      (T.powerPair j i * T.powerPair j k) : ℤ) : ℚ) = _
    rw [Algebra.coe_trace_int]
    fin_cases i <;> fin_cases k <;> simp [powerPair]
  rw [Algebra.discr_def, Algebra.discr_def, ← hmatrix]
  change algebraMap ℤ ℚ (Matrix.det (Algebra.traceMatrix ℤ (T.powerPair j))) = _
  rw [RingHom.map_det]
  congr 1

/-! ### Degree-two trace and discriminant identities

Cayley--Hamilton in degree two gives the trace-and-norm polynomial of every field element.  For a
norm-one unit this converts the pair discriminant into `( ε^j - ε^{-j} )²` at the selected real
embedding. -/

/-- A degree-two field element satisfies its trace-and-norm polynomial.

This specializes `DegreeTwoAlgebra.sq_eq_trace_mul_sub_norm_of_basis` to the quadratic field
underlying the tower. -/
lemma sq_eq_trace_mul_sub_norm (T : RealQuadraticUnitData K) (x : K) :
    x ^ 2 = algebraMap ℚ K (Algebra.trace ℚ K x) * x -
      algebraMap ℚ K (Algebra.norm ℚ x) := by
  exact DegreeTwoAlgebra.sq_eq_trace_mul_sub_norm_of_basis ℚ K
    (DegreeTwoAlgebra.basisFinTwo ℚ K T.finrank_eq_two) x

/-- The trace of a norm-one element is the sum of its selected real value and its inverse. -/
lemma trace_eq_embedding_add_inv (T : RealQuadraticUnitData K) (x : K)
    (hnorm : Algebra.norm ℚ x = 1) :
    (Algebra.trace ℚ K x : ℝ) =
      realEmbeddingAt K T.place x + (realEmbeddingAt K T.place x)⁻¹ := by
  have hx : x ≠ 0 := Algebra.norm_ne_zero_iff.mp (by rw [hnorm]; exact one_ne_zero)
  have h := congrArg (realEmbeddingAt K T.place) (T.sq_eq_trace_mul_sub_norm x)
  simp only [map_sub, map_mul, map_pow] at h
  have hcast (q : ℚ) : realEmbeddingAt K T.place (algebraMap ℚ K q) = (q : ℝ) := by
    change realEmbeddingAt K T.place (q : K) = (q : ℝ)
    exact map_ratCast (realEmbeddingAt K T.place) q
  simp_rw [hcast] at h
  rw [hnorm] at h
  norm_num at h
  have hxreal : realEmbeddingAt K T.place x ≠ 0 := by
    intro hzero
    apply hx
    exact (realEmbeddingAt K T.place).injective (by simpa using hzero)
  have htx : (Algebra.trace ℚ K x : ℝ) * realEmbeddingAt K T.place x =
      (realEmbeddingAt K T.place x) ^ 2 + 1 := by
    nlinarith [h]
  calc
    (Algebra.trace ℚ K x : ℝ) =
        ((Algebra.trace ℚ K x : ℝ) * realEmbeddingAt K T.place x) *
          (realEmbeddingAt K T.place x)⁻¹ := by
      rw [mul_assoc, mul_inv_cancel₀ hxreal, mul_one]
    _ = ((realEmbeddingAt K T.place x) ^ 2 + 1) *
          (realEmbeddingAt K T.place x)⁻¹ := by rw [htx]
    _ = realEmbeddingAt K T.place x + (realEmbeddingAt K T.place x)⁻¹ := by
      field_simp

/-- In degree two, the rational discriminant of `(1,x)` for a norm-one element is the square of
the difference between its selected real value and its inverse. -/
lemma pair_discr_eq_embedding_sub_inv_sq (T : RealQuadraticUnitData K) (x : K)
    (hnorm : Algebra.norm ℚ x = 1) :
    ((Algebra.discr ℚ ![(1 : K), x] : ℚ) : ℝ) =
      (realEmbeddingAt K T.place x - (realEmbeddingAt K T.place x)⁻¹) ^ 2 := by
  have hx : x ≠ 0 := Algebra.norm_ne_zero_iff.mp (by rw [hnorm]; exact one_ne_zero)
  have htrace := T.trace_eq_embedding_add_inv x hnorm
  have hone : Algebra.trace ℚ K 1 = 2 := by
    simpa only [map_one, T.finrank_eq_two, nsmul_eq_mul, Nat.cast_ofNat, mul_one] using
      (Algebra.trace_algebraMap (R := ℚ) (S := K) 1)
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  change (((Algebra.trace ℚ K ((1 : K) * 1) * Algebra.trace ℚ K (x * x) -
    Algebra.trace ℚ K ((1 : K) * x) * Algebra.trace ℚ K (x * 1)) : ℚ) : ℝ) = _
  have hsquare := congrArg (Algebra.trace ℚ K) (T.sq_eq_trace_mul_sub_norm x)
  simp only [map_sub] at hsquare
  rw [← Algebra.smul_def] at hsquare
  simp only [map_smul, Algebra.trace_algebraMap, T.finrank_eq_two, nsmul_eq_mul,
    Nat.cast_ofNat, smul_eq_mul, hnorm] at hsquare
  rw [one_mul, mul_one, ← pow_two, hsquare, hone]
  norm_num
  rw [htrace]
  have hxreal : realEmbeddingAt K T.place x ≠ 0 := by
    intro hzero
    apply hx
    exact (realEmbeddingAt K T.place).injective (by simpa using hzero)
  field_simp
  ring

/-- Every natural power of the distinguished unit has norm one. -/
lemma epsilon_pow_norm_eq_one (T : RealQuadraticUnitData K) (j : ℕ) :
    Algebra.norm ℚ ((T.epsilon : K) ^ j) = 1 := by
  rw [map_pow, T.epsilon_norm_eq_one, one_pow]

/-- The determinant conductor satisfies the squared real conductor equation. -/
lemma conductorNat_sq_mul_discr_eq (T : RealQuadraticUnitData K) (j : ℕ) :
    (T.conductorNat j : ℝ) ^ 2 * (NumberField.discr K : ℝ) =
      (T.epsilonReal ^ j - (T.epsilonReal ^ j)⁻¹) ^ 2 := by
  let x : K := (T.epsilon : K) ^ j
  have hz := congrArg (fun z : ℤ ↦ (z : ℝ)) (T.powerPair_discr j)
  norm_num at hz
  have hcast : (Algebra.discr ℤ (T.powerPair j) : ℝ) =
      ((Algebra.discr ℚ ![(1 : K), x] : ℚ) : ℝ) := by
    change (Algebra.discr ℤ (T.powerPair j) : ℝ) =
      ((Algebra.discr ℚ ![(1 : K), (T.epsilon : K) ^ j] : ℚ) : ℝ)
    exact_mod_cast T.powerPair_discr_cast j
  calc
    (T.conductorNat j : ℝ) ^ 2 * (NumberField.discr K : ℝ) =
        (Algebra.discr ℤ (T.powerPair j) : ℝ) := hz.symm
    _ = ((Algebra.discr ℚ ![(1 : K), x] : ℚ) : ℝ) := hcast
    _ = (realEmbeddingAt K T.place x - (realEmbeddingAt K T.place x)⁻¹) ^ 2 :=
      T.pair_discr_eq_embedding_sub_inv_sq x (T.epsilon_pow_norm_eq_one j)
    _ = (T.epsilonReal ^ j - (T.epsilonReal ^ j)⁻¹) ^ 2 := by
      simp [x, epsilonReal, map_pow]

/-! ### Canonical positive conductor and dimension values

Positivity chooses the unsquared sign in the determinant-discriminant equation and yields the
canonical conductor `f_j`.  The trace identity similarly produces the integral dimension `d_j`,
and the two values form an exact rank-one level at every positive index. -/

/-- The determinant conductor is positive at every positive index. -/
lemma conductorNat_pos (T : RealQuadraticUnitData K) (j : ℕ+) :
    0 < T.conductorNat (j : ℕ) := by
  have hx : 1 < T.epsilonReal ^ (j : ℕ) := T.one_lt_epsilonReal_pow j
  have hinv : (T.epsilonReal ^ (j : ℕ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx
  have hdiff : 0 < T.epsilonReal ^ (j : ℕ) - (T.epsilonReal ^ (j : ℕ))⁻¹ := by
    linarith
  have hsquare := T.conductorNat_sq_mul_discr_eq (j : ℕ)
  by_contra hpos
  have hzero : T.conductorNat (j : ℕ) = 0 := Nat.eq_zero_of_not_pos hpos
  rw [hzero] at hsquare
  norm_num at hsquare
  nlinarith [sq_pos_of_pos hdiff]

/-- The canonical positive integer `f_j`, obtained as the index determinant of `ℤ[ε^j]` in
the ring of integers. -/
noncomputable def canonicalConductor (T : RealQuadraticUnitData K) (j : ℕ+) : ℕ+ :=
  ⟨T.conductorNat (j : ℕ), T.conductorNat_pos j⟩

/-- The canonical determinant conductor satisfies AFK's oriented, unsquared equation (1.37). -/
lemma canonicalConductor_spec (T : RealQuadraticUnitData K) (j : ℕ+) :
    T.IsConductorSequenceValue j (T.canonicalConductor j) := by
  have hΔnonneg : (0 : ℝ) ≤ NumberField.discr K := by
    exact_mod_cast (le_of_lt T.discr_pos)
  have hsqrt_sq : Real.sqrt (NumberField.discr K) ^ 2 =
      (NumberField.discr K : ℝ) := Real.sq_sqrt hΔnonneg
  have hsquares :
      (((T.canonicalConductor j : ℕ) : ℝ) * Real.sqrt (NumberField.discr K)) ^ 2 =
        (T.epsilonReal ^ (j : ℕ) - (T.epsilonReal ^ (j : ℕ))⁻¹) ^ 2 := by
    rw [mul_pow, hsqrt_sq]
    exact T.conductorNat_sq_mul_discr_eq (j : ℕ)
  have hleft : 0 <
      ((T.canonicalConductor j : ℕ) : ℝ) * Real.sqrt (NumberField.discr K) := by
    apply mul_pos
    · exact_mod_cast (T.canonicalConductor j).property
    · exact Real.sqrt_pos.2 (by exact_mod_cast T.discr_pos)
  have hx : 1 < T.epsilonReal ^ (j : ℕ) := T.one_lt_epsilonReal_pow j
  have hinv : (T.epsilonReal ^ (j : ℕ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx
  have hright : 0 <
      T.epsilonReal ^ (j : ℕ) - (T.epsilonReal ^ (j : ℕ))⁻¹ := by
    linarith
  change (((T.canonicalConductor j : ℕ) : ℝ) * Real.sqrt (NumberField.discr K) = _)
  nlinarith

/-- The integral expression `Tr(ε^j) + 1` for the rank-one dimension value. -/
noncomputable def dimensionInt (T : RealQuadraticUnitData K) (j : ℕ) : ℤ :=
  Algebra.trace ℤ (NumberField.RingOfIntegers K)
      ((T.epsilon ^ j : (NumberField.RingOfIntegers K)ˣ) :
        NumberField.RingOfIntegers K) + 1

/-- The integral trace expression has the real value `ε^j + ε^(-j) + 1`. -/
lemma dimensionInt_cast_eq_dimensionValue (T : RealQuadraticUnitData K) (j : ℕ+) :
    (T.dimensionInt (j : ℕ) : ℝ) = T.dimensionValue j := by
  let u : NumberField.RingOfIntegers K :=
    ((T.epsilon ^ (j : ℕ) : (NumberField.RingOfIntegers K)ˣ) :
      NumberField.RingOfIntegers K)
  let x : K := (T.epsilon : K) ^ (j : ℕ)
  have htrace := T.trace_eq_embedding_add_inv x
    (T.epsilon_pow_norm_eq_one (j : ℕ))
  have hcoe : ((Algebra.trace ℤ (NumberField.RingOfIntegers K) u : ℤ) : ℚ) =
      Algebra.trace ℚ K x := by
    simpa [u, x, NumberField.Units.coe_pow] using Algebra.coe_trace_int u
  have hcoeReal := congrArg (fun q : ℚ ↦ (q : ℝ)) hcoe
  norm_num at hcoeReal
  calc
    (T.dimensionInt (j : ℕ) : ℝ) =
        (Algebra.trace ℤ (NumberField.RingOfIntegers K) u : ℝ) + 1 := by
      simp [dimensionInt, u]
    _ = (Algebra.trace ℚ K x : ℝ) + 1 := by rw [hcoeReal]
    _ = realEmbeddingAt K T.place x + (realEmbeddingAt K T.place x)⁻¹ + 1 := by
      rw [htrace]
    _ = T.dimensionValue j := by
      simp [dimensionValue, x, epsilonReal, map_pow]

/-- The integral dimension expression is greater than three at every positive index. -/
lemma dimensionInt_gt_three (T : RealQuadraticUnitData K) (j : ℕ+) :
    3 < T.dimensionInt (j : ℕ) := by
  have hreal : (3 : ℝ) < T.dimensionInt (j : ℕ) := by
    rw [T.dimensionInt_cast_eq_dimensionValue j]
    exact T.three_lt_dimensionValue j
  exact_mod_cast hreal

/-- The canonical natural trace value `Tr(ε^j) + 1`, intended to be the grid value `d_j`. -/
noncomputable def canonicalDimension (T : RealQuadraticUnitData K) (j : ℕ+) : ℕ :=
  (T.dimensionInt (j : ℕ)).toNat

/-- The canonical natural dimension casts back to the integral expression it truncates:
`(d_j : ℤ) = Tr(ε^j) + 1`. The truncation is harmless because `dimensionInt_gt_three` makes the
integer positive. -/
lemma canonicalDimension_coe_int (T : RealQuadraticUnitData K) (j : ℕ+) :
    (T.canonicalDimension j : ℤ) = T.dimensionInt (j : ℕ) :=
  Int.toNat_of_nonneg
    (le_of_lt (lt_trans (by norm_num) (T.dimensionInt_gt_three j)))

/-- The canonical natural dimension realizes AFK's rank-one formula (4.4). -/
lemma canonicalDimension_spec (T : RealQuadraticUnitData K) (j : ℕ+) :
    T.IsDimensionTowerValue j (T.canonicalDimension j) := by
  have hcastReal := congrArg (fun z : ℤ ↦ (z : ℝ)) (T.canonicalDimension_coe_int j)
  change ((T.canonicalDimension j : ℕ) : ℝ) = T.dimensionValue j
  rw [← T.dimensionInt_cast_eq_dimensionValue j]
  norm_num at hcastReal ⊢
  exact hcastReal

/-- The canonical conductor and dimension form an exact rank-one level at every positive
index. -/
noncomputable def canonicalRankOneLevel (T : RealQuadraticUnitData K) (j : ℕ+) :
    T.RankOneLevel (T.canonicalDimension j) where
  j := j
  f := T.canonicalConductor j
  conductor_spec := T.canonicalConductor_spec j
  dimension_spec := T.canonicalDimension_spec j

/-! ### The rank-one radicand

Squaring the two rank-one tower equations `d_j = ε^j + ε^{-j} + 1` and
`f_j √Δ₀ = ε^j - ε^{-j}` eliminates the unit and leaves an identity between integers:

```text
(d_j + 1)(d_j - 3) = f_j² Δ₀.
```

The left-hand side is the radicand `(d+1)(d-3)` attached to the rank-one pair `(d_j, 1)`, so this
says that the tower field is `ℚ(√((d+1)(d-3)))` with the tower conductor as the index of the
associated order. It is what turns a form of discriminant `(d+1)(d-3)` into one of conductor `f_j`
over `Δ₀`. At the canonical values it reads `f_j² Δ₀ = (d_j - 3)(d_j + 1)`. -/

/-- The rank-one tower equations `d = u + u⁻¹ + 1` and `f √Δ₀ = u - u⁻¹`, with `u` standing for
the unit power `ε^j`, imply the integer identity `(d + 1)(d - 3) = f² Δ₀`.

This unbundled form takes no packaged tower. Private: the public statements are
`RankOneLevel.radicand_eq` and its canonical specialization below. -/
private lemma rankOneRadicand_eq_of_towerEquations (d f : ℕ) (Δ₀ : ℤ) (u : ℝ)
    (hΔ₀ : 0 ≤ Δ₀) (hu : 0 < u) (hdim : (d : ℝ) = u + u⁻¹ + 1)
    (hconductor : (f : ℝ) * Real.sqrt Δ₀ = u - u⁻¹) :
    ((d : ℤ) + 1) * ((d : ℤ) - 3) = (f : ℤ) ^ 2 * Δ₀ := by
  have humul : u * u⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hu)
  have hsum : (d : ℝ) - 1 = u + u⁻¹ := by linarith
  have hsqrt : Real.sqrt Δ₀ ^ 2 = (Δ₀ : ℝ) := Real.sq_sqrt (by exact_mod_cast hΔ₀)
  have hreal : (((d : ℤ) + 1) * ((d : ℤ) - 3) : ℝ) = (f : ℝ) ^ 2 * (Δ₀ : ℝ) := by
    calc
      (((d : ℤ) + 1) * ((d : ℤ) - 3) : ℝ) = ((d : ℝ) - 1) ^ 2 - 4 := by push_cast; ring
      _ = (u + u⁻¹) ^ 2 - 4 := by rw [hsum]
      _ = (u - u⁻¹) ^ 2 := by nlinarith [humul]
      _ = ((f : ℝ) * Real.sqrt Δ₀) ^ 2 := by rw [hconductor]
      _ = (f : ℝ) ^ 2 * (Δ₀ : ℝ) := by rw [mul_pow, hsqrt]
  exact_mod_cast hreal

/-- At an exact rank-one tower level, `(d + 1)(d - 3) = f_j² disc(K)`.

This is [AFK25, Lemma 4.3, `lem:towerbasic`, equation (4.5)] together with
[AFK25, Definition 4.2, `dfn:discriminantLevelj`, equation (4.1)], in the integer form used to
compute form conductors over the field discriminant. -/
lemma RankOneLevel.radicand_eq {d : ℕ} {T : RealQuadraticUnitData K} (L : T.RankOneLevel d) :
    ((d : ℤ) + 1) * ((d : ℤ) - 3) = ((L.f : ℕ) : ℤ) ^ 2 * NumberField.discr K :=
  rankOneRadicand_eq_of_towerEquations d (L.f : ℕ) (NumberField.discr K)
    (T.epsilonReal ^ (L.j : ℕ)) (le_of_lt T.discr_pos) (T.epsilonReal_pow_pos L.j)
    L.dimension_spec L.conductor_spec

/-- **The tower discriminant.** `f_j² Δ₀ = (d_j - 3)(d_j + 1)`, where `Δ₀ = disc(K)`.

This is `RankOneLevel.radicand_eq` at `canonicalRankOneLevel j`, where the level's conductor and
dimension are the canonical values. -/
theorem canonicalConductor_sq_mul_discr (T : RealQuadraticUnitData K) (j : ℕ+) :
    ((T.canonicalConductor j : ℕ) : ℤ) ^ 2 * NumberField.discr K =
      ((T.canonicalDimension j : ℤ) - 3) * ((T.canonicalDimension j : ℤ) + 1) := by
  have h := (T.canonicalRankOneLevel j).radicand_eq
  simp only [canonicalRankOneLevel] at h
  linarith [h]

end RealQuadraticUnitData

end SIC

end
