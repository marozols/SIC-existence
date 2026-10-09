/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Admissible.Triples
import SICs.Quadratic.Orders
import SICs.Quadratic.FundamentalForms

/-!
# Triples and Tuples over Admissible Pairs

Theorem 4.20(B), existence: a triple `(K, j, m)` for every admissible pair by the norm-one unit
`(P + r f_j√Δ₀)/2 = ε^{jm}`, and an admissible tuple over every admissible pair.

This file formalizes the existence half of [AFK25, Theorem 4.20(B), `thm:nrddjmrjm`]: every
admissible pair `(d,r)` is associated with an admissible triple `(K,j,m)`, that is,
`d = d_{j,m}` and `r = r_{j,m}`. Adding the principal form of the field discriminant turns that
triple into an admissible tuple, the input of
[AFK26, Appleby, Flammia, Kopp (2026), Theorem 1.3, `thm:ghost`].

## Mathematical argument

An admissible pair `(d,r)` first selects the concrete real quadratic field of the rank-one
dimension `n-1`.  The proof follows the source's norm-one-unit argument: the Pell identity
attached to `(d,r,n)` produces an integral norm-one element in `ℤ[ε^j]`; the fundamental unit
theorem and `dvd_of_epsilon_pow_mem_powerOrder` identify its exponent as `jm`.  The conductor and
neighbouring-rank identities then recover `r = r_{j,m}` and `d = d_{j,m}`.

## Main results

- `AdmissiblePair.exists_admissibleTriple`: every admissible pair is associated with a triple.
- `AdmissiblePair.exists_admissibleTuple`: every admissible pair underlies an admissible tuple
  whose form has positive leading coefficient.

## References

- [AFK25, Theorem 4.20, `thm:nrddjmrjm`]
- [AFK26, Appleby, Flammia, Kopp (2026), Theorem 1.3, `thm:ghost`]
-/

noncomputable section

open scoped NumberField

namespace SIC

namespace AdmissiblePair

/-! ### Constructing a triple from a pair

The following integer identity is the Pell equation obtained by solving the admissible-pair
equation for its dimension.  Keeping it separate makes the subsequent unit calculation a direct
ring computation.
-/

/-- The discriminant identity `(2d-nr)² = r²n(n-4)+4` attached to an admissible pair. -/
private lemma dimensionDiscriminant_sq (p : AdmissiblePair) :
    (2 * (p.d : ℤ) - (p.n : ℤ) * (p.r : ℤ)) ^ 2 =
      (p.r : ℤ) ^ 2 * (p.n : ℤ) * ((p.n : ℤ) - 4) + 4 := by
  linear_combination -4 * p.equation_int

/-- The absolute discriminant numerator has the parity needed for the integral unit
`a + rρ_{n-1}`. -/
private lemma exists_two_mul_eq_abs_sub (p : AdmissiblePair) :
    ∃ a : ℤ, 2 * a =
      |2 * (p.d : ℤ) - (p.n : ℤ) * (p.r : ℤ)| -
        (p.r : ℤ) * ((p.n : ℤ) - 2) := by
  by_cases h : 0 ≤ 2 * (p.d : ℤ) - (p.n : ℤ) * (p.r : ℤ)
  · refine ⟨(p.d : ℤ) - (p.r : ℤ) * ((p.n : ℤ) - 1), ?_⟩
    rw [abs_of_nonneg h]
    ring
  · refine ⟨(p.r : ℤ) - (p.d : ℤ), ?_⟩
    rw [abs_of_neg (lt_of_not_ge h)]
    ring

/-- The two integral rank-one roots add to `n - 2` when the root dimension is `n - 1`. -/
private lemma rankOneRootInteger_add_inv_of_eq_n_sub_one (p : AdmissiblePair)
    (d₀ : RankOneDimension) (hd₀ : (d₀ : ℕ) = p.n - 1) :
    rankOneRootInteger d₀ + rankOneRootIntegerInv d₀ =
      algebraMap ℤ (NumberField.RingOfIntegers (RankOneField d₀)) ((p.n : ℤ) - 2) := by
  calc
    rankOneRootInteger d₀ + rankOneRootIntegerInv d₀ =
        algebraMap ℤ (NumberField.RingOfIntegers (RankOneField d₀)) ((d₀ : ℤ) - 1) := by
      dsimp [rankOneRootIntegerInv]
      ring
    _ = algebraMap ℤ (NumberField.RingOfIntegers (RankOneField d₀))
        ((p.n : ℤ) - 2) := by
      congr 1
      rw [hd₀]
      omega

/-- The integral element `a + rρ_{n-1}` times its conjugate is one under the Pell identity. -/
private lemma pairUnit_mul_conjugate (p : AdmissiblePair) (d₀ : RankOneDimension)
    (hd₀ : (d₀ : ℕ) = p.n - 1) (P a : ℤ)
    (hP : P ^ 2 = (p.r : ℤ) ^ 2 * (p.n : ℤ) * ((p.n : ℤ) - 4) + 4)
    (ha : 2 * a = P - (p.r : ℤ) * ((p.n : ℤ) - 2)) :
    (algebraMap ℤ _ a + algebraMap ℤ _ (p.r : ℤ) * rankOneRootInteger d₀) *
        (algebraMap ℤ _ a + algebraMap ℤ _ (p.r : ℤ) * rankOneRootIntegerInv d₀) =
      1 := by
  have hscalar : a ^ 2 + a * (p.r : ℤ) * ((p.n : ℤ) - 2) + (p.r : ℤ) ^ 2 = 1 := by
    have hP' := hP
    rw [show P = 2 * a + (p.r : ℤ) * ((p.n : ℤ) - 2) by linarith [ha]] at hP'
    nlinarith [hP']
  have hscalar' := congrArg
    (algebraMap ℤ (NumberField.RingOfIntegers (RankOneField d₀))) hscalar
  push_cast at hscalar'
  calc
    (algebraMap ℤ _ a + algebraMap ℤ _ (p.r : ℤ) * rankOneRootInteger d₀) *
        (algebraMap ℤ _ a + algebraMap ℤ _ (p.r : ℤ) * rankOneRootIntegerInv d₀) =
      (algebraMap ℤ _ a) ^ 2 + algebraMap ℤ _ a * algebraMap ℤ _ (p.r : ℤ) *
        (rankOneRootInteger d₀ + rankOneRootIntegerInv d₀) +
          (algebraMap ℤ _ (p.r : ℤ)) ^ 2 *
            (rankOneRootInteger d₀ * rankOneRootIntegerInv d₀) := by ring
    _ = (algebraMap ℤ _ a) ^ 2 + algebraMap ℤ _ a * algebraMap ℤ _ (p.r : ℤ) *
        algebraMap ℤ _ ((p.n : ℤ) - 2) + (algebraMap ℤ _ (p.r : ℤ)) ^ 2 := by
      rw [p.rankOneRootInteger_add_inv_of_eq_n_sub_one d₀ hd₀,
        rankOneRootInteger_mul_inv, mul_one]
    _ = 1 := by simpa using hscalar'

/-- The selected real value of `a + rρ_{n-1}` is
`(P + r√(n(n-4)))/2`, with the radicand represented by `rankOneRadicand`. -/
private lemma pairUnit_realEmbedding (p : AdmissiblePair) (d₀ : RankOneDimension)
    (hd₀ : (d₀ : ℕ) = p.n - 1) (P a : ℤ)
    (ha : 2 * a = P - (p.r : ℤ) * ((p.n : ℤ) - 2)) :
    realEmbeddingAt (RankOneField d₀) (rankOneRealQuadraticUnitData d₀).place
        ((a : RankOneField d₀) + (p.r : RankOneField d₀) * rankOneFieldRoot d₀) =
      ((P : ℝ) + (p.r : ℝ) * Real.sqrt (rankOneRadicand d₀)) / 2 := by
  rw [map_add, map_mul, map_intCast, map_natCast]
  have hroot : realEmbeddingAt (RankOneField d₀) (rankOneRealQuadraticUnitData d₀).place
      (rankOneFieldRoot d₀) = rankOneRoot d₀ := by
    change realEmbeddingAt (RankOneField d₀) (rankOneInfinitePlace d₀)
      (rankOneFieldRoot d₀) = rankOneRoot d₀
    exact realEmbeddingAt_rankOneRootUnit d₀
  rw [hroot]
  rw [rankOneRoot, hd₀]
  have hncast : ((p.n - 1 : ℕ) : ℝ) = (p.n : ℝ) - 1 := by
    rw [Nat.cast_sub (by have := p.four_lt_n; omega)]
    norm_num
  rw [hncast]
  have haReal : 2 * (a : ℝ) = (P : ℝ) - (p.r : ℝ) * ((p.n : ℝ) - 2) := by
    exact_mod_cast ha
  linarith

/-- The rank-one root has trace `n - 2` when its dimension is `n - 1`. -/
private lemma rankOneRootInteger_trace_of_eq_n_sub_one (p : AdmissiblePair)
    (d₀ : RankOneDimension) (hd₀ : (d₀ : ℕ) = p.n - 1) :
    Algebra.trace ℚ (RankOneField d₀) (rankOneFieldRoot d₀) =
      (p.n : ℚ) - 2 := by
  have htrace := (rankOneRealQuadraticUnitData d₀).trace_eq_embedding_add_inv
    (rankOneFieldRoot d₀) (rankOneFieldRoot_norm d₀)
  have hroot : realEmbeddingAt (RankOneField d₀) (rankOneRealQuadraticUnitData d₀).place
      (rankOneFieldRoot d₀) = rankOneRoot d₀ := by
    change realEmbeddingAt (RankOneField d₀) (rankOneInfinitePlace d₀)
      (rankOneFieldRoot d₀) = rankOneRoot d₀
    exact realEmbeddingAt_rankOneRootUnit d₀
  rw [hroot] at htrace
  have hroot : rankOneRoot d₀ + (rankOneRoot d₀)⁻¹ = (p.n : ℝ) - 2 := by
    rw [rankOneRoot_add_inv d₀ d₀.property, hd₀]
    rw [Nat.cast_sub (by have := p.four_lt_n; omega)]
    ring
  exact_mod_cast htrace.trans hroot

/-- The trace of the constructed element `a + rρ_{n-1}` is `P`. -/
private lemma pairUnit_trace (p : AdmissiblePair) (d₀ : RankOneDimension)
    (hd₀ : (d₀ : ℕ) = p.n - 1) (P a : ℤ)
    (ha : 2 * a = P - (p.r : ℤ) * ((p.n : ℤ) - 2)) :
    Algebra.trace ℚ (RankOneField d₀)
        ((a : RankOneField d₀) + (p.r : RankOneField d₀) * rankOneFieldRoot d₀) = P := by
  rw [map_add]
  rw [show (a : RankOneField d₀) = algebraMap ℚ _ (a : ℚ) by norm_num,
    Algebra.trace_algebraMap, rankOneField_finrank]
  rw [show (p.r : RankOneField d₀) = algebraMap ℚ _ (p.r : ℚ) by norm_num,
    ← Algebra.smul_def, map_smul, p.rankOneRootInteger_trace_of_eq_n_sub_one d₀ hd₀]
  simp only [nsmul_eq_mul, smul_eq_mul]
  have haQ : 2 * (a : ℚ) = (P : ℚ) - (p.r : ℚ) * ((p.n : ℚ) - 2) := by
    exact_mod_cast ha
  push_cast
  linear_combination haQ

/-- The conjugate of `a + rρ_{n-1}` is `P - (a + rρ_{n-1})`. -/
private lemma pairUnit_conjugate_eq_sub (p : AdmissiblePair) (d₀ : RankOneDimension)
    (hd₀ : (d₀ : ℕ) = p.n - 1) (P a : ℤ)
    (ha : 2 * a = P - (p.r : ℤ) * ((p.n : ℤ) - 2)) :
    ((a : NumberField.RingOfIntegers (RankOneField d₀)) +
        (p.r : NumberField.RingOfIntegers (RankOneField d₀)) * rankOneRootIntegerInv d₀ :
      RankOneField d₀) =
      (P : RankOneField d₀) -
        ((a : NumberField.RingOfIntegers (RankOneField d₀)) +
          (p.r : NumberField.RingOfIntegers (RankOneField d₀)) * rankOneRootInteger d₀ :
            RankOneField d₀) := by
  have haMap := congrArg
    (algebraMap ℤ (NumberField.RingOfIntegers (RankOneField d₀))) ha
  push_cast at haMap
  have hsum :
      (algebraMap ℤ _ a + algebraMap ℤ _ (p.r : ℤ) * rankOneRootInteger d₀) +
        (algebraMap ℤ _ a + algebraMap ℤ _ (p.r : ℤ) * rankOneRootIntegerInv d₀) =
      algebraMap ℤ (NumberField.RingOfIntegers (RankOneField d₀)) P := by
    calc
      _ = 2 * algebraMap ℤ _ a + algebraMap ℤ _ (p.r : ℤ) *
          (rankOneRootInteger d₀ + rankOneRootIntegerInv d₀) := by ring
      _ = 2 * algebraMap ℤ _ a + algebraMap ℤ _ (p.r : ℤ) *
          algebraMap ℤ _ ((p.n : ℤ) - 2) := by
        rw [p.rankOneRootInteger_add_inv_of_eq_n_sub_one d₀ hd₀]
      _ = algebraMap ℤ _ P := by simpa using (eq_add_of_sub_eq haMap.symm).symm
  have hsumField := congrArg
    (fun z : NumberField.RingOfIntegers (RankOneField d₀) ↦ (z : RankOneField d₀)) hsum
  change ((a : RankOneField d₀) + (p.r : RankOneField d₀) * rankOneFieldRoot d₀) +
      ((a : RankOneField d₀) + (p.r : RankOneField d₀) *
        (rankOneRootIntegerInv d₀ : RankOneField d₀)) = (P : RankOneField d₀) at hsumField
  change (a : RankOneField d₀) + (p.r : RankOneField d₀) *
      (rankOneRootIntegerInv d₀ : RankOneField d₀) =
    (P : RankOneField d₀) -
      ((a : RankOneField d₀) + (p.r : RankOneField d₀) * rankOneFieldRoot d₀)
  linear_combination hsumField

/-- The constructed element has field norm one once its trace and conjugate product are known. -/
private lemma pairUnit_norm {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (T₀ : RealQuadraticUnitData K) (w winv : K) (P : ℤ)
    (htrace : Algebra.trace ℚ K w = P) (hconj : winv = (P : K) - w)
    (hmul : w * winv = 1) : Algebra.norm ℚ w = 1 := by
  have hquad := T₀.sq_eq_trace_mul_sub_norm w
  rw [htrace] at hquad
  rw [show algebraMap ℚ K (P : ℚ) = (P : K) by norm_num] at hquad
  rw [hconj] at hmul
  apply (algebraMap ℚ K).injective
  change algebraMap ℚ K (Algebra.norm ℚ w) = algebraMap ℚ K 1
  rw [map_one]
  linear_combination hquad + hmul

/-- The Pell construction produces the norm-one unit `w = a + rρ_{n-1}` with trace `P` and
selected real value `(P + r√(n(n-4)))/2`, as in [AFK25, Theorem 4.20(B),
`thm:nrddjmrjm`]. -/
private lemma exists_pairNormOneUnit (p : AdmissiblePair) (d₀ : RankOneDimension)
    (hd₀ : (d₀ : ℕ) = p.n - 1) (P a : ℤ)
    (hP : P ^ 2 = (p.r : ℤ) ^ 2 * (p.n : ℤ) * ((p.n : ℤ) - 4) + 4)
    (ha : 2 * a = P - (p.r : ℤ) * ((p.n : ℤ) - 2)) :
    ∃ u : (NumberField.RingOfIntegers (RankOneField d₀))ˣ,
      (u : NumberField.RingOfIntegers (RankOneField d₀)) =
          algebraMap ℤ _ a + algebraMap ℤ _ (p.r : ℤ) * rankOneRootInteger d₀ ∧
      realEmbeddingAt (RankOneField d₀) (rankOneRealQuadraticUnitData d₀).place
          (u : RankOneField d₀) =
        ((P : ℝ) + (p.r : ℝ) * Real.sqrt (rankOneRadicand d₀)) / 2 ∧
      Algebra.trace ℚ (RankOneField d₀) (u : RankOneField d₀) = P ∧
      Algebra.norm ℚ (u : RankOneField d₀) = 1 := by
  let w : NumberField.RingOfIntegers (RankOneField d₀) :=
    algebraMap ℤ _ a + algebraMap ℤ _ (p.r : ℤ) * rankOneRootInteger d₀
  let winv : NumberField.RingOfIntegers (RankOneField d₀) :=
    algebraMap ℤ _ a + algebraMap ℤ _ (p.r : ℤ) * rankOneRootIntegerInv d₀
  have hw : w * winv = 1 := p.pairUnit_mul_conjugate d₀ hd₀ P a hP ha
  let u : (NumberField.RingOfIntegers (RankOneField d₀))ˣ := Units.mkOfMulEqOne w winv hw
  have hu : (u : NumberField.RingOfIntegers (RankOneField d₀)) = w := rfl
  have hval := p.pairUnit_realEmbedding d₀ hd₀ P a ha
  have htrace := p.pairUnit_trace d₀ hd₀ P a ha
  have hconj := p.pairUnit_conjugate_eq_sub d₀ hd₀ P a ha
  refine ⟨u, hu, ?_, ?_, ?_⟩
  · change realEmbeddingAt (RankOneField d₀) (rankOneRealQuadraticUnitData d₀).place
        ((a : RankOneField d₀) + (p.r : RankOneField d₀) * rankOneFieldRoot d₀) = _
    exact hval
  · change Algebra.trace ℚ (RankOneField d₀)
        ((a : RankOneField d₀) + (p.r : RankOneField d₀) * rankOneFieldRoot d₀) = P
    exact htrace
  · apply pairUnit_norm (rankOneRealQuadraticUnitData d₀) (u : RankOneField d₀)
      (winv : RankOneField d₀) P
    · change Algebra.trace ℚ (RankOneField d₀)
          ((a : RankOneField d₀) + (p.r : RankOneField d₀) * rankOneFieldRoot d₀) = P
      exact htrace
    · change (winv : RankOneField d₀) = (P : RankOneField d₀) -
          ((a : RankOneField d₀) + (p.r : RankOneField d₀) * rankOneFieldRoot d₀)
      exact hconj
    · exact_mod_cast hw

/-- The difference of the selected value of the constructed unit and its inverse is
`r(ε^j-ε⁻ʲ)`. -/
private lemma pairUnit_embedding_sub_inv (p : AdmissiblePair) (d₀ : RankOneDimension)
    (T₀ : RealQuadraticUnitData (RankOneField d₀))
    (j : ℕ+) (u : (NumberField.RingOfIntegers (RankOneField d₀))ˣ) (P : ℤ)
    (hval : realEmbeddingAt (RankOneField d₀) T₀.place (u : RankOneField d₀) =
      ((P : ℝ) + (p.r : ℝ) * Real.sqrt (rankOneRadicand d₀)) / 2)
    (htrace : Algebra.trace ℚ (RankOneField d₀) (u : RankOneField d₀) = P)
    (hnorm : Algebra.norm ℚ (u : RankOneField d₀) = 1)
    (hjroot : rankOneRootUnit d₀ = T₀.epsilon ^ (j : ℕ))
    (hrootval : realEmbeddingAt (RankOneField d₀) T₀.place
      (rankOneRootUnit d₀ : RankOneField d₀) = rankOneRoot d₀) :
    (p.r : ℝ) * (T₀.epsilonReal ^ (j : ℕ) - (T₀.epsilonReal ^ (j : ℕ))⁻¹) =
      realEmbeddingAt (RankOneField d₀) T₀.place (u : RankOneField d₀) -
        (realEmbeddingAt (RankOneField d₀) T₀.place (u : RankOneField d₀))⁻¹ := by
  have htraceReal := T₀.trace_eq_embedding_add_inv (u : RankOneField d₀) hnorm
  rw [htrace] at htraceReal
  have hxroot : T₀.epsilonReal ^ (j : ℕ) = rankOneRoot d₀ := by
    have h := congrArg (fun v : (NumberField.RingOfIntegers (RankOneField d₀))ˣ ↦
      realEmbeddingAt (RankOneField d₀) T₀.place (v : RankOneField d₀)) hjroot
    rw [hrootval] at h
    simpa [RealQuadraticUnitData.epsilonReal, NumberField.Units.coe_pow, map_pow] using h.symm
  have hrootdiff : rankOneRoot d₀ - (rankOneRoot d₀)⁻¹ =
      Real.sqrt (rankOneRadicand d₀) := by
    rw [inv_rankOneRoot d₀ d₀.property, rankOneRoot]
    ring
  rw [hxroot, hrootdiff]
  norm_num at hval htraceReal
  nlinarith [hval, htraceReal]

/-- The fundamental-unit exponent of the constructed unit is a positive multiple `jm`. -/
private lemma exists_pairUnit_exponent_mul (p : AdmissiblePair) (d₀ : RankOneDimension)
    (T₀ : RealQuadraticUnitData (RankOneField d₀)) (j : ℕ+)
    (u : (NumberField.RingOfIntegers (RankOneField d₀))ˣ) (a : ℤ)
    (huval : (u : NumberField.RingOfIntegers (RankOneField d₀)) =
      algebraMap ℤ _ a + algebraMap ℤ _ (p.r : ℤ) * rankOneRootInteger d₀)
    (hnorm : Algebra.norm ℚ (u : RankOneField d₀) = 1)
    (hone : 1 < realEmbeddingAt (RankOneField d₀) T₀.place (u : RankOneField d₀))
    (hjroot : rankOneRootUnit d₀ = T₀.epsilon ^ (j : ℕ)) :
    ∃ k m : ℕ+, u = T₀.epsilon ^ (k : ℕ) ∧ (k : ℕ) = (j : ℕ) * (m : ℕ) := by
  obtain ⟨k, huk⟩ := T₀.exists_eq_epsilon_pow u hnorm hone
  have hmem : ((T₀.epsilon ^ (k : ℕ) :
      (NumberField.RingOfIntegers (RankOneField d₀))ˣ) :
        NumberField.RingOfIntegers (RankOneField d₀)) ∈ T₀.powerOrder (j : ℕ) := by
    rw [← huk, huval]
    rw [show rankOneRootInteger d₀ =
      (rankOneRootUnit d₀ : NumberField.RingOfIntegers (RankOneField d₀)) from rfl, hjroot]
    exact (T₀.powerOrder (j : ℕ)).add_mem ((T₀.powerOrder (j : ℕ)).algebraMap_mem _)
      ((T₀.powerOrder (j : ℕ)).mul_mem ((T₀.powerOrder (j : ℕ)).algebraMap_mem _)
        (Algebra.subset_adjoin (Set.mem_singleton _)))
  obtain ⟨m, hkm⟩ := T₀.dvd_of_epsilon_pow_mem_powerOrder j (k : ℕ) hmem
  have hmpos : 0 < m := by
    by_contra hm
    rw [Nat.eq_zero_of_not_pos hm, mul_zero] at hkm
    exact k.property.ne' hkm
  exact ⟨k, ⟨m, hmpos⟩, huk, hkm⟩

/-- The equality `k = jm` identifies the pair rank with `r_{j,m}`. -/
private lemma pairUnit_rank_eq_rankGrid {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (p : AdmissiblePair)
    (T₀ : RealQuadraticUnitData K) (j k m : ℕ+)
    (u : (NumberField.RingOfIntegers K)ˣ)
    (huk : u = T₀.epsilon ^ (k : ℕ)) (hkm : (k : ℕ) = (j : ℕ) * (m : ℕ))
    (hdiff : (p.r : ℝ) *
      (T₀.epsilonReal ^ (j : ℕ) - (T₀.epsilonReal ^ (j : ℕ))⁻¹) =
      realEmbeddingAt K T₀.place (u : K) - (realEmbeddingAt K T₀.place (u : K))⁻¹) :
    p.r = (T₀.rankGrid j m : ℕ) := by
  have hu : realEmbeddingAt K T₀.place (u : K) =
      (T₀.epsilonReal ^ (j : ℕ)) ^ (m : ℕ) := by
    rw [huk, NumberField.Units.coe_pow, map_pow, hkm, pow_mul]
    rfl
  rw [hu] at hdiff
  have hgrid := T₀.rankGridInt_mul_epsilonSub j (m : ℕ)
  have hsub : T₀.epsilonReal ^ (j : ℕ) - (T₀.epsilonReal ^ (j : ℕ))⁻¹ ≠ 0 := by
    have hone := T₀.one_lt_epsilonReal_pow j
    have hinv := inv_lt_one_of_one_lt₀ hone
    linarith
  have hrankReal : (p.r : ℝ) = (T₀.rankGridInt j (m : ℕ) : ℝ) :=
    mul_right_cancel₀ hsub (hdiff.trans hgrid.symm)
  exact_mod_cast hrankReal.trans
    (congrArg (fun z : ℤ ↦ (z : ℝ)) (T₀.rankGrid_coe_int j m)).symm

/-- The constructed unit yields `k = jm` and `r = r_{j,m}`, the exponent-and-rank
identification in [AFK25, Theorem 4.20(B), `thm:nrddjmrjm`]. -/
private lemma exists_pairUnit_exponent_mul_and_rank_eq (p : AdmissiblePair)
    (d₀ : RankOneDimension)
    (T₀ : RealQuadraticUnitData (RankOneField d₀)) (j : ℕ+)
    (u : (NumberField.RingOfIntegers (RankOneField d₀))ˣ) (P a : ℤ)
    (huval : (u : NumberField.RingOfIntegers (RankOneField d₀)) =
      algebraMap ℤ _ a + algebraMap ℤ _ (p.r : ℤ) * rankOneRootInteger d₀)
    (hval : realEmbeddingAt (RankOneField d₀) T₀.place (u : RankOneField d₀) =
      ((P : ℝ) + (p.r : ℝ) * Real.sqrt (rankOneRadicand d₀)) / 2)
    (htrace : Algebra.trace ℚ (RankOneField d₀) (u : RankOneField d₀) = P)
    (hnorm : Algebra.norm ℚ (u : RankOneField d₀) = 1)
    (hone : 1 < realEmbeddingAt (RankOneField d₀) T₀.place (u : RankOneField d₀))
    (hjroot : rankOneRootUnit d₀ = T₀.epsilon ^ (j : ℕ))
    (hrootval : realEmbeddingAt (RankOneField d₀) T₀.place
      (rankOneRootUnit d₀ : RankOneField d₀) = rankOneRoot d₀) :
    ∃ k m : ℕ+, u = T₀.epsilon ^ (k : ℕ) ∧ (k : ℕ) = (j : ℕ) * (m : ℕ) ∧
      p.r = (T₀.rankGrid j m : ℕ) := by
  obtain ⟨k, m, huk, hkm⟩ := p.exists_pairUnit_exponent_mul d₀ T₀ j u a huval hnorm hone hjroot
  have hdiff := p.pairUnit_embedding_sub_inv d₀ T₀ j u P hval htrace hnorm hjroot
    hrootval
  exact ⟨k, m, huk, hkm, p.pairUnit_rank_eq_rankGrid T₀ j k m u huk hkm hdiff⟩

/-- The neighbouring-rank identities and the admissible rank bound select
`d = r_{j,m+1} + r_{j,m} = d_{j,m}`, as in [AFK25, Theorem 4.20(B),
`thm:nrddjmrjm`]. -/
private lemma pair_dimension_eq_dimensionGrid {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (p : AdmissiblePair)
    (T₀ : RealQuadraticUnitData K) (j m : ℕ+) (P : ℤ)
    (hP : P = |2 * (p.d : ℤ) - (p.n : ℤ) * (p.r : ℤ)|)
    (hrank : p.r = (T₀.rankGrid j m : ℕ))
    (hneighbourSum : ((p.n : ℤ) - 2) * (p.r : ℤ) =
      T₀.rankGridInt j ((m : ℕ) + 1) + T₀.rankGridInt j ((m : ℕ) - 1))
    (hneighbourDiff : P = T₀.rankGridInt j ((m : ℕ) + 1) -
      T₀.rankGridInt j ((m : ℕ) - 1)) :
    p.d = T₀.dimensionGrid j m := by
  let p₀ : ℤ := 2 * (p.d : ℤ) - (p.n : ℤ) * (p.r : ℤ)
  have hrint : (p.r : ℤ) = T₀.rankGridInt j (m : ℕ) := by
    rw [← T₀.rankGrid_coe_int j m]
    exact_mod_cast hrank
  have hp₀sign : p₀ = P ∨ p₀ = -P := by
    by_cases hp : 0 ≤ p₀
    · left
      rw [hP, abs_of_nonneg hp]
    · right
      rw [hP, abs_of_neg (lt_of_not_ge hp)]
      ring
  rcases hp₀sign with hplus | hminus
  · have hdint : (p.d : ℤ) = T₀.rankGridInt j ((m : ℕ) + 1) +
        T₀.rankGridInt j (m : ℕ) := by
      dsimp [p₀] at hplus
      linarith only [hplus, hneighbourSum, hneighbourDiff, hrint]
    exact_mod_cast hdint.trans (T₀.dimensionGrid_coe_int j m).symm
  · have hdsmall : (p.d : ℤ) = T₀.rankGridInt j ((m : ℕ) - 1) +
        T₀.rankGridInt j (m : ℕ) := by
      dsimp [p₀] at hminus
      linarith only [hminus, hneighbourSum, hneighbourDiff, hrint]
    have hprev := T₀.rankGridInt_lt_succ j ((m : ℕ) - 1)
    have hm : (m : ℕ) - 1 + 1 = (m : ℕ) := Nat.sub_add_cancel m.property
    rw [hm] at hprev
    have hbound := p.rank_lt
    zify [show 1 ≤ p.d by have := p.three_lt_d; omega] at hbound
    linarith only [hdsmall, hprev, hbound, hrint]

/-- The selected value of the Pell unit is greater than one. -/
private lemma one_lt_pairNormOneUnit (p : AdmissiblePair) (d₀ : RankOneDimension)
    (T₀ : RealQuadraticUnitData (RankOneField d₀))
    (u : (NumberField.RingOfIntegers (RankOneField d₀))ˣ) (P : ℤ)
    (hP : P ^ 2 = (p.r : ℤ) ^ 2 * (p.n : ℤ) * ((p.n : ℤ) - 4) + 4)
    (hPnonneg : 0 ≤ P)
    (hval : realEmbeddingAt (RankOneField d₀) T₀.place (u : RankOneField d₀) =
      ((P : ℝ) + (p.r : ℝ) * Real.sqrt (rankOneRadicand d₀)) / 2) :
    1 < realEmbeddingAt (RankOneField d₀) T₀.place (u : RankOneField d₀) := by
  have hPthree : 3 ≤ P := by
    have hr : (1 : ℤ) ≤ p.r := by exact_mod_cast p.rank_pos
    have hn5 : (5 : ℤ) ≤ p.n := by exact_mod_cast p.four_lt_n
    nlinarith [sq_nonneg ((p.r : ℤ) * ((p.n : ℤ) - 4))]
  rw [hval]
  have hsqrt : 0 ≤ Real.sqrt (rankOneRadicand d₀) := Real.sqrt_nonneg _
  have hrnonneg : (0 : ℝ) ≤ p.r := by positivity
  have hPthreeReal : (3 : ℝ) ≤ P := by exact_mod_cast hPthree
  nlinarith

/-- Equality `r = r_{j,m}` and `d_j = n - 1` give the neighbouring-rank sum. -/
private lemma pairUnit_neighbourSum {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (p : AdmissiblePair) (T₀ : RealQuadraticUnitData K)
    (j m : ℕ+) (hnInt : T₀.dimensionInt (j : ℕ) = (p.n : ℤ) - 1)
    (hrank : p.r = (T₀.rankGrid j m : ℕ)) :
    ((p.n : ℤ) - 2) * (p.r : ℤ) =
      T₀.rankGridInt j ((m : ℕ) + 1) + T₀.rankGridInt j ((m : ℕ) - 1) := by
  have hrankInt : (p.r : ℤ) = T₀.rankGridInt j (m : ℕ) := by
    rw [← T₀.rankGrid_coe_int j m]
    exact_mod_cast hrank
  have h := T₀.epsilonAddInv_mul_rankGridInt j m
  have hxtrace : T₀.epsilonReal ^ (j : ℕ) +
      (T₀.epsilonReal ^ (j : ℕ))⁻¹ = (p.n : ℝ) - 2 := by
    have hdim := T₀.dimensionInt_cast_eq_dimensionValue j
    rw [RealQuadraticUnitData.dimensionValue, hnInt] at hdim
    push_cast at hdim
    linarith
  rw [hxtrace] at h
  have hrankReal := congrArg (fun z : ℤ ↦ (z : ℝ)) hrankInt
  rw [← hrankReal] at h
  exact_mod_cast h

/-- The trace of the Pell unit gives the neighbouring-rank difference. -/
private lemma pairUnit_neighbourDiff {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (T₀ : RealQuadraticUnitData K) (j k m : ℕ+)
    (u : (NumberField.RingOfIntegers K)ˣ) (P : ℤ)
    (huk : u = T₀.epsilon ^ (k : ℕ)) (hkm : (k : ℕ) = (j : ℕ) * (m : ℕ))
    (htrace : Algebra.trace ℚ K (u : K) = P) (hnorm : Algebra.norm ℚ (u : K) = 1) :
    P = T₀.rankGridInt j ((m : ℕ) + 1) - T₀.rankGridInt j ((m : ℕ) - 1) := by
  have htraceReal := T₀.trace_eq_embedding_add_inv (u : K) hnorm
  rw [htrace] at htraceReal
  have hvalue : realEmbeddingAt K T₀.place (u : K) =
      (T₀.epsilonReal ^ (j : ℕ)) ^ (m : ℕ) := by
    rw [huk, NumberField.Units.coe_pow, map_pow, hkm, pow_mul]
    rfl
  rw [hvalue] at htraceReal
  have h := T₀.epsilonPow_add_inv_eq_rankGridInt_sub j m
  rw [← htraceReal] at h
  exact_mod_cast h

/-- The constructed Pell unit completes the associated triple once its canonical level is fixed. -/
private lemma exists_admissibleTriple_of_pairNormOneUnit (p : AdmissiblePair)
    (d₀ : RankOneDimension) (T₀ : RealQuadraticUnitData (RankOneField d₀)) (j : ℕ+)
    (hnInt : T₀.dimensionInt (j : ℕ) = (p.n : ℤ) - 1) (P a : ℤ)
    (hP : P ^ 2 = (p.r : ℤ) ^ 2 * (p.n : ℤ) * ((p.n : ℤ) - 4) + 4)
    (hPabs : P = |2 * (p.d : ℤ) - (p.n : ℤ) * (p.r : ℤ)|)
    (hPnonneg : 0 ≤ P) (u : (NumberField.RingOfIntegers (RankOneField d₀))ˣ)
    (huval : (u : NumberField.RingOfIntegers (RankOneField d₀)) =
      algebraMap ℤ _ a + algebraMap ℤ _ (p.r : ℤ) * rankOneRootInteger d₀)
    (hval : realEmbeddingAt (RankOneField d₀) T₀.place (u : RankOneField d₀) =
      ((P : ℝ) + (p.r : ℝ) * Real.sqrt (rankOneRadicand d₀)) / 2)
    (htrace : Algebra.trace ℚ (RankOneField d₀) (u : RankOneField d₀) = P)
    (hnorm : Algebra.norm ℚ (u : RankOneField d₀) = 1)
    (hjroot : rankOneRootUnit d₀ = T₀.epsilon ^ (j : ℕ))
    (hrootval : realEmbeddingAt (RankOneField d₀) T₀.place
      (rankOneRootUnit d₀ : RankOneField d₀) = rankOneRoot d₀) :
    ∃ T : AdmissibleTriple.{0}, T.IsAssociatedPair p := by
  have hone := p.one_lt_pairNormOneUnit d₀ T₀ u P hP hPnonneg hval
  obtain ⟨k, m, huk, hkm, hrank⟩ := p.exists_pairUnit_exponent_mul_and_rank_eq
    d₀ T₀ j u P a huval hval htrace hnorm hone hjroot hrootval
  have hsum := p.pairUnit_neighbourSum T₀ j m hnInt hrank
  have hdiff := pairUnit_neighbourDiff T₀ j k m u P huk hkm htrace hnorm
  have hdimension := p.pair_dimension_eq_dimensionGrid T₀ j m P hPabs hrank hsum hdiff
  exact ⟨⟨RankOneField d₀, T₀, j, m⟩, hdimension, hrank⟩

/-- **[AFK25, Theorem 4.20(B), `thm:nrddjmrjm`], existence.** Every admissible pair `(d,r)`
comes from a real quadratic rank and dimension grid: there is an admissible triple `(K,j,m)`
with `d=d_{j,m}` and `r=r_{j,m}`.

The proof follows the source's norm-one-unit construction in the concrete field
`ℚ(√(n(n-4)))`, represented as `RankOneField ⟨n-1, _⟩`.  The source invokes its order theorem to
deduce `k=jm`; here `dvd_of_epsilon_pow_mem_powerOrder` supplies precisely that step by a direct
real-embedding argument. -/
@[source "AFK25, Theorem 4.20, p. 56, thm:nrddjmrjm (B, existence)"]
theorem exists_admissibleTriple (p : AdmissiblePair) :
    ∃ T : AdmissibleTriple.{0}, T.IsAssociatedPair p := by
  let d₀ : RankOneDimension := ⟨p.n - 1, by have := p.four_lt_n; omega⟩
  let _ : Fact (Irreducible (rankOnePolynomialRat d₀)) := rankOnePolynomialRat_fact d₀
  let _ : NumberField.IsTotallyReal (RankOneField d₀) := rankOneFieldTotallyReal d₀
  let T₀ := rankOneRealQuadraticUnitData d₀
  let L₀ := rankOneFieldLevel d₀
  let j : ℕ+ := L₀.j
  have hd₀ : (d₀ : ℕ) = p.n - 1 := rfl
  have hn : (T₀.canonicalDimension j : ℕ) = p.n - 1 := by
    exact (T₀.canonicalDimension_spec j).unique L₀.dimension_spec
  have hnInt : T₀.dimensionInt (j : ℕ) = (p.n : ℤ) - 1 := by
    rw [← T₀.canonicalDimension_coe_int j, hn]
    omega
  let p₀ : ℤ := 2 * (p.d : ℤ) - (p.n : ℤ) * (p.r : ℤ)
  let P : ℤ := |p₀|
  have hP : P ^ 2 = (p.r : ℤ) ^ 2 * (p.n : ℤ) * ((p.n : ℤ) - 4) + 4 := by
    rw [show P ^ 2 = p₀ ^ 2 by simp [P]]
    exact p.dimensionDiscriminant_sq
  obtain ⟨a, ha⟩ := p.exists_two_mul_eq_abs_sub
  have ha' : 2 * a = P - (p.r : ℤ) * ((p.n : ℤ) - 2) := by
    simpa [P, p₀] using ha
  obtain ⟨u, huval', humap, htracew, hunorm⟩ :=
    p.exists_pairNormOneUnit d₀ hd₀ P a hP ha'
  have hjroot : rankOneRootUnit d₀ = T₀.epsilon ^ (j : ℕ) := by
    simpa [T₀, L₀, j] using rankOneRootUnit_eq_epsilon_pow d₀
  have hrootval : realEmbeddingAt (RankOneField d₀) T₀.place
      (rankOneRootUnit d₀ : RankOneField d₀) = rankOneRoot d₀ := by
    exact realEmbeddingAt_rankOneRootUnit d₀
  exact p.exists_admissibleTriple_of_pairNormOneUnit d₀ T₀ j hnInt P a hP
    (by rfl) (abs_nonneg p₀) u huval' humap htracew hunorm hjroot hrootval

/-! ### An admissible tuple over every pair

The triple of `exists_admissibleTriple` with the principal form `conductorOneForm Δ₀` of the field
discriminant is an admissible tuple: its conductor `1` divides `f_j`, and admissibility needs only
that `Δ₀` is positive, fundamental, and not a square. Its leading coefficient is `1 > 0`, the
orientation [AFK26, Appleby, Flammia, Kopp (2026), Section 4] assumes ("`γ₂₁ > 0`"). -/

/-- **An admissible tuple over every admissible pair**, with a form of positive leading
coefficient: the tuple input of [AFK26, Appleby, Flammia, Kopp (2026), Theorem 1.3, `thm:ghost`].
The form is the principal form of conductor one, which the source's sign convention
`γ₂₁ > 0` of Section 4 allows. -/
theorem exists_admissibleTuple (p : AdmissiblePair) :
    ∃ t : AdmissibleTuple, t.pair = p ∧ 0 < t.Q.a := by
  obtain ⟨T, hT⟩ := p.exists_admissibleTriple
  have hfund := T.tower.discr_fundamental
  have hpos := T.tower.discr_pos
  have hnsq : ¬ IsSquare (NumberField.discr T.K) :=
    not_isSquare_numberField_discr T.tower.finrank_eq_two
  refine ⟨{
    triple := T
    pair := p
    Q := conductorOneForm (NumberField.discr T.K)
    associated := hT
    form_admissible := isAdmissible_conductorOneForm hfund hpos hnsq
    formConductor := 1
    formConductor_spec := isConductor_conductorOneForm hfund hpos
    formConductor_dvd := one_dvd _
  }, rfl, ?_⟩
  norm_num [conductorOneForm_a]

end AdmissiblePair

end SIC

end
