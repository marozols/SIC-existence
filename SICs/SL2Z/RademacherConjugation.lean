/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SL2Z.DedekindReciprocity
import SICs.SL2Z.ThetaCharacter
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices

/-!
# The Rademacher Invariant is a Class Function

Rademacher's `Ψ` is invariant under conjugation in `SL₂(ℤ)`, hence so is the eta multiplier
`μ_M = e^{πiΨ(M)/12}`.

This module follows [88, Rademacher and Grosswald (1972), Chapter 4, Section C, equations
(63)–(67)], which prove that `Ψ(M) = Φ(M) - 3 sgn(c(a + d))` is a class invariant of the
modular group; the project's `rademacherInvariant` is this `Ψ`, written with `𝔰(a, |c|)` in
place of `𝔰(d, |c|)` (`dedekindSum_eq_of_mul_modEq_one`). The invariance is what makes the
finite quantum dilogarithm of a pseudolattice independent of its oriented basis
([RW26b, Radchenko, Wheeler (2026b), Appendix B]: "`μ_{AγA⁻¹} = μ_γ` by the eta cocycle"), used
by `SICs.Dilogarithm.Pseudolattice.Homothety`.

## The argument

`S = (0 -1; 1 0)` and `T = (1 1; 0 1)` generate `SL₂(ℤ)` (`SpecialLinearGroup.SL2Z_generators`),
so it suffices to treat conjugation by each (Rademacher and Grosswald write `S` for the
translation and `T` for the inversion).

- `TMT⁻¹ = (a + c, b + d - a - c; c, d - c)` has the same lower-left entry and trace as `M`,
  and `𝔰(a + c, |c|) = 𝔰(a, |c|)` by periodicity (`dedekindSum_add_mul_right`), so `Ψ` is
  unchanged; for `c = 0` the matrix is `±T^b` and `TMT⁻¹ = M`.
- `SMS⁻¹ = (d, -c; -b, a)`. For `bc ≠ 0` the claim
  `Ψ(M) = (a + d)/c - 3 sgn(c(a + d)) - 12 sgn(c) 𝔰(a, |c|)
   = -(a + d)/b + 3 sgn(b(a + d)) + 12 sgn(b) 𝔰(d, |b|)`
  follows from two reciprocity laws and two inversions of the first argument: `𝔰(a, |c|)` is
  paired by `dedekindSum_reciprocity` with `𝔰(|c|, |a|)`, which equals `±𝔰(b, |a|)` because
  `-bc ≡ 1 (mod a)`, and `𝔰(b, |a|)` is paired with `𝔰(|a|, |b|) = ±𝔰(d, |b|)` because
  `ad ≡ 1 (mod b)`; the rational terms of the two reciprocity laws and the sign terms cancel
  against `(a + d)/c + (a + d)/b = (a + d)(b + c)/(bc)` by the sign identity
  `sgn(c(a + d)) + sgn(b(a + d)) = sgn(ac) + sgn(ab)` of [88, Rademacher and Grosswald (1972),
  equation (67)], after the cases on
  the signs of `a`, `b`, `c`, `d` (`Int.sign`, `dedekindSum_neg_left`, `dedekindSum_neg_right`).
  For `b = 0` or `c = 0`, the determinant forces both diagonal entries to be `±1`. The
  lower-triangular case follows from reciprocity at first argument `±1`; the upper-triangular
  case follows by conjugating twice by `S`.

Rademacher and Grosswald derive the `S`-case from the composition rule
[88, Rademacher and Grosswald (1972), equation (62)], proved there analytically through
`log η`; the arithmetic proof above
uses only the reciprocity law already in `SICs.SL2Z.DedekindReciprocity`, as their remark after
(62) says is possible.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### Conjugation by the generators -/

/-- The entries of a conjugate by `T`, used by `rademacherInvariant_conj_T`. -/
private lemma conj_T_entries (M : SL(2, ℤ)) :
    (ModularGroup.T * M * ModularGroup.T⁻¹) 0 0 = M 0 0 + M 1 0 ∧
    (ModularGroup.T * M * ModularGroup.T⁻¹) 0 1 = M 0 1 + M 1 1 - M 0 0 - M 1 0 ∧
    (ModularGroup.T * M * ModularGroup.T⁻¹) 1 0 = M 1 0 ∧
    (ModularGroup.T * M * ModularGroup.T⁻¹) 1 1 = M 1 1 - M 1 0 := by
  have h (i j : Fin 2) :
      (ModularGroup.T * M * ModularGroup.T⁻¹) i j =
        ((ModularGroup.T : Mat(2, ℤ)) *
          (M : Mat(2, ℤ)) *
          ((ModularGroup.T⁻¹ : SL(2, ℤ)) : Mat(2, ℤ))) i j := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    rw [h]
    simp [ModularGroup.coe_T, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two] <;> ring

/-- The entries of a conjugate by `S`, used by `rademacherInvariant_conj_S`. -/
private lemma conj_S_entries (M : SL(2, ℤ)) :
    (ModularGroup.S * M * ModularGroup.S⁻¹) 0 0 = M 1 1 ∧
    (ModularGroup.S * M * ModularGroup.S⁻¹) 0 1 = -M 1 0 ∧
    (ModularGroup.S * M * ModularGroup.S⁻¹) 1 0 = -M 0 1 ∧
    (ModularGroup.S * M * ModularGroup.S⁻¹) 1 1 = M 0 0 := by
  have h (i j : Fin 2) :
      (ModularGroup.S * M * ModularGroup.S⁻¹) i j =
        ((ModularGroup.S : Mat(2, ℤ)) *
          (M : Mat(2, ℤ)) *
          ((ModularGroup.S⁻¹ : SL(2, ℤ)) : Mat(2, ℤ))) i j := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    rw [h, Matrix.mul_apply]
    simp [ModularGroup.coe_S, Matrix.SpecialLinearGroup.SL2_inv_expl,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- **`Ψ` is invariant under conjugation by `T`** ([88, Rademacher and Grosswald (1972),
Chapter 4, Section C, equation (64)], where the translation is called `S`): `TMT⁻¹` has the
same lower-left entry and trace as `M`, and `𝔰(a + c, |c|) = 𝔰(a, |c|)`. -/
@[source "88, equation (64), p. 55"]
theorem rademacherInvariant_conj_T (M : SL(2, ℤ)) :
    rademacherInvariant (ModularGroup.T * M * ModularGroup.T⁻¹) = rademacherInvariant M := by
  obtain ⟨h00, h01, h10, h11⟩ := conj_T_entries M
  by_cases hc : M 1 0 = 0
  · have hdet : M 0 0 * M 1 1 = 1 := by
      have h := M.2
      rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at h
      exact h
    have hdiag : M 0 0 = M 1 1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with h | h <;> omega
    have hmat : ModularGroup.T * M * ModularGroup.T⁻¹ = M := by
      ext i j
      fin_cases i <;> fin_cases j
      · simpa [hc] using h00
      · simpa [hc, hdiag] using h01
      · simpa using h10
      · simpa [hc] using h11
    rw [hmat]
  · have hconj : (ModularGroup.T * M * ModularGroup.T⁻¹) 1 0 ≠ 0 := by
      rwa [h10]
    rw [rademacherInvariant_of_lowerLeft_ne_zero _ hconj,
      rademacherInvariant_of_lowerLeft_ne_zero M hc, h00, h10, h11]
    have hs : dedekindSum (M 0 0 + M 1 0) (M 1 0) =
        dedekindSum (M 0 0) (M 1 0) := by
      simpa using dedekindSum_add_mul_right (M 0 0) (M 1 0) 1
    rw [hs]
    have htr : M 0 0 + M 1 0 + (M 1 1 - M 1 0) = M 0 0 + M 1 1 := by ring
    rw [htr]

/-- The sign identity (67) used in `rademacherInvariant_conj_S` when `bc ≠ 0`. -/
private lemma conj_S_sign_identity {a b c d : ℤ} (hb : b ≠ 0) (hc : c ≠ 0)
    (hdet : a * d - b * c = 1) :
    Int.sign (c * (a + d)) + Int.sign (b * (a + d)) =
      Int.sign (a * c) + Int.sign (a * b) := by
  simp only [Int.sign_mul]
  by_cases hbc : 0 < b * c
  · have had : 0 < a * d := by omega
    have htr : Int.sign (a + d) = Int.sign a := by
      by_cases ha : 0 < a
      · have hd : 0 < d := by
          by_contra h
          have hz : a * d ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha.le (le_of_not_gt h)
          omega
        rw [Int.sign_eq_one_of_pos ha, Int.sign_eq_one_of_pos (by omega)]
      · have ha' : a < 0 := by
          by_contra h
          have : a = 0 := by omega
          simp [this] at had
        have hd : d < 0 := by
          by_contra h
          have hz : a * d ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha'.le (le_of_not_gt h)
          omega
        rw [Int.sign_eq_neg_one_of_neg ha', Int.sign_eq_neg_one_of_neg (by omega)]
    rw [htr]
    ring
  · have hsum : Int.sign b + Int.sign c = 0 := by
      rcases lt_or_gt_of_ne hb with hb | hb
      · have hc' : 0 < c := by
          by_contra h
          have hcn : c < 0 := by omega
          exact (not_lt_of_ge (le_of_not_gt hbc)) (mul_pos_of_neg_of_neg hb hcn)
        rw [Int.sign_eq_neg_one_of_neg hb, Int.sign_eq_one_of_pos hc']
        ring
      · have hc' : c < 0 := by
          by_contra h
          have hcp : 0 < c := by omega
          exact (not_lt_of_ge (le_of_not_gt hbc)) (mul_pos hb hcp)
        rw [Int.sign_eq_one_of_pos hb, Int.sign_eq_neg_one_of_neg hc']
        ring
    calc
      Int.sign c * Int.sign (a + d) + Int.sign b * Int.sign (a + d) =
          (Int.sign b + Int.sign c) * Int.sign (a + d) := by ring
      _ = 0 := by rw [hsum]; ring
      _ = Int.sign a * Int.sign c + Int.sign a * Int.sign b := by
        calc
          0 = Int.sign a * (Int.sign b + Int.sign c) := by rw [hsum]; ring
          _ = _ := by ring

/-- The reciprocity calculation for `rademacherInvariant_conj_S` when `abc ≠ 0`. -/
private lemma conj_S_arithmetic_of_topLeft_ne_zero {a b c d : ℤ}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hdet : a * d - b * c = 1) :
    ((d + a : ℤ) : ℚ) / ((-b : ℤ) : ℚ) -
        3 * (Int.sign (-b * (d + a)) : ℚ) -
        12 * (Int.sign (-b) : ℚ) * dedekindSum d (-b) =
      ((a + d : ℤ) : ℚ) / (c : ℚ) -
        3 * (Int.sign (c * (a + d)) : ℚ) -
        12 * (Int.sign c : ℚ) * dedekindSum a c := by
  have hcopAC : IsCoprime a c := ⟨d, -b, by linear_combination hdet⟩
  have hcopAB : IsCoprime a b := ⟨d, -c, by linear_combination hdet⟩
  have hmodCB : c * (-b) ≡ 1 [ZMOD a] := by
    rw [Int.modEq_iff_dvd]
    refine ⟨d, ?_⟩
    nlinarith [hdet]
  have hmodAD : a * d ≡ 1 [ZMOD b] := by
    rw [Int.modEq_iff_dvd]
    refine ⟨-c, ?_⟩
    nlinarith [hdet]
  have hcb : dedekindSum c a = -dedekindSum b a := by
    rw [← dedekindSum_neg_left]
    exact dedekindSum_eq_of_mul_modEq_one ha hmodCB
  have hda : dedekindSum d b = dedekindSum a b :=
    (dedekindSum_eq_of_mul_modEq_one hb hmodAD).symm
  have hrecC := dedekindSum_reciprocity_signed ha hc hcopAC
  have hrecB := dedekindSum_reciprocity_signed ha hb hcopAB
  rw [hcb] at hrecC
  have haQ : (a : ℚ) ≠ 0 := Int.cast_ne_zero.mpr ha
  have hbQ : (b : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hb
  have hcQ : (c : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hc
  have hdetQ : (a : ℚ) * (d : ℚ) - (b : ℚ) * (c : ℚ) = 1 := by
    exact_mod_cast hdet
  have hdQ : (d : ℚ) = (1 + (b : ℚ) * (c : ℚ)) / (a : ℚ) := by
    apply (eq_div_iff haQ).2
    linear_combination hdetQ
  have hrat :
      (a : ℚ) / (c : ℚ) + (a : ℚ) / (b : ℚ) +
          (c : ℚ) / (a : ℚ) + (b : ℚ) / (a : ℚ) +
          1 / ((a : ℚ) * (c : ℚ)) + 1 / ((a : ℚ) * (b : ℚ)) =
        ((a + d : ℤ) : ℚ) / (c : ℚ) + ((a + d : ℤ) : ℚ) / (b : ℚ) := by
    rw [show ((a + d : ℤ) : ℚ) = (a : ℚ) + (d : ℚ) by push_cast; rfl, hdQ]
    field_simp
    ring
  have hsign := conj_S_sign_identity hb hc hdet
  have hsignQ :
      (Int.sign (c * (a + d)) : ℚ) + (Int.sign (b * (a + d)) : ℚ) =
        (Int.sign (a * c) : ℚ) + (Int.sign (a * b) : ℚ) := by
    exact_mod_cast hsign
  rw [dedekindSum_neg_right, hda, Int.sign_neg]
  rw [show -b * (d + a) = -(b * (a + d)) by ring, Int.sign_neg]
  push_cast at hrat ⊢
  linear_combination hrecC + hrecB + hrat + 3 * hsignQ

/-- The Dedekind-sum calculation for `rademacherInvariant_conj_S` when `bc ≠ 0`. -/
private lemma conj_S_arithmetic {a b c d : ℤ} (hb : b ≠ 0) (hc : c ≠ 0)
    (hdet : a * d - b * c = 1) :
    ((d + a : ℤ) : ℚ) / ((-b : ℤ) : ℚ) -
        3 * (Int.sign (-b * (d + a)) : ℚ) -
        12 * (Int.sign (-b) : ℚ) * dedekindSum d (-b) =
      ((a + d : ℤ) : ℚ) / (c : ℚ) -
        3 * (Int.sign (c * (a + d)) : ℚ) -
        12 * (Int.sign c : ℚ) * dedekindSum a c := by
  by_cases ha : a = 0
  · subst a
    have h : (-b) * c = 1 := by nlinarith [hdet]
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' h with ⟨hb, hc⟩ | ⟨hb, hc⟩
    · have hb' : b = -1 := by omega
      subst b
      subst c
      norm_num [dedekindSum]
    · have hb' : b = 1 := by omega
      subst b
      subst c
      norm_num [dedekindSum]
  · exact conj_S_arithmetic_of_topLeft_ne_zero ha hb hc hdet

/-- The triangular case `b = 0` of `rademacherInvariant_conj_S`, reduced to reciprocity at
the unit top-left entry. -/
private lemma conj_S_lower_arithmetic {a c : ℤ} (ha2 : a * a = 1) (hc : c ≠ 0) :
    ((-c : ℤ) : ℚ) / (a : ℚ) =
      ((a + a : ℤ) : ℚ) / (c : ℚ) -
        3 * (Int.sign (c * (a + a)) : ℚ) -
        12 * (Int.sign c : ℚ) * dedekindSum a c := by
  have ha : a ≠ 0 := by nlinarith [ha2]
  have hcop : IsCoprime a c := ⟨a, 0, by nlinarith [ha2]⟩
  have hrec := dedekindSum_reciprocity_signed ha hc hcop
  have hs : dedekindSum c a = 0 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' ha2 with h | h
    · rw [h.1]
      simp [dedekindSum]
    · rw [h.1]
      simp [dedekindSum]
  rw [hs] at hrec
  simp only [mul_zero, add_zero] at hrec
  have hsign : Int.sign (c * (a + a)) = Int.sign (a * c) := by
    rw [show c * (a + a) = 2 * (a * c) by ring, Int.sign_mul,
      Int.sign_eq_one_of_pos (by norm_num : (0 : ℤ) < 2), one_mul]
  rw [hsign]
  have ha2Q : (a : ℚ) * (a : ℚ) = 1 := by exact_mod_cast ha2
  have haQ : (a : ℚ) ≠ 0 := Int.cast_ne_zero.mpr ha
  have hcQ : (c : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hc
  have hq : 1 / ((a : ℚ) * (c : ℚ)) = (a : ℚ) / (c : ℚ) := by
    field_simp
    nlinarith [ha2Q]
  push_cast
  linear_combination hrec + hq

/-- Conjugation by `S` when the top-right entry vanishes, the triangular case of
`rademacherInvariant_conj_S`. -/
private lemma rademacherInvariant_conj_S_of_topRight_zero (M : SL(2, ℤ))
    (hb : M 0 1 = 0) :
    rademacherInvariant (ModularGroup.S * M * ModularGroup.S⁻¹) =
      rademacherInvariant M := by
  obtain ⟨h00, h01, h10, h11⟩ := conj_S_entries M
  have hdet : M 0 0 * M 1 1 = 1 := by
    have h := M.2
    rw [Matrix.det_fin_two, hb, zero_mul, sub_zero] at h
    exact h
  have hdiag : M 0 0 = M 1 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with h | h <;> omega
  by_cases hc : M 1 0 = 0
  · have hmat : ModularGroup.S * M * ModularGroup.S⁻¹ = M := by
      ext i j
      fin_cases i <;> fin_cases j
      · simpa [hdiag] using h00
      · simpa [hc, hb] using h01
      · simpa [hb, hc] using h10
      · simpa [hdiag] using h11
    rw [hmat]
  · have hconj : (ModularGroup.S * M * ModularGroup.S⁻¹) 1 0 = 0 := by
      rw [h10, hb, neg_zero]
    have ha2 : M 0 0 * M 0 0 = 1 := by rwa [← hdiag] at hdet
    rw [rademacherInvariant_of_lowerLeft_ne_zero M hc]
    unfold rademacherInvariant
    simp only [hconj, ne_eq, not_true_eq_false, ite_false, h01, h11]
    rw [← hdiag]
    exact conj_S_lower_arithmetic ha2 hc

/-- Double conjugation by `S` restores the matrix, used for the second triangular case of
`rademacherInvariant_conj_S`. -/
private lemma conj_S_conj_S (M : SL(2, ℤ)) :
    ModularGroup.S * (ModularGroup.S * M * ModularGroup.S⁻¹) * ModularGroup.S⁻¹ = M := by
  obtain ⟨h00, h01, h10, h11⟩ := conj_S_entries M
  obtain ⟨hh00, hh01, hh10, hh11⟩ :=
    conj_S_entries (ModularGroup.S * M * ModularGroup.S⁻¹)
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [h11] using hh00
  · simpa [h10] using hh01
  · simpa [h01] using hh10
  · simpa [h00] using hh11

/-- **`Ψ` is invariant under conjugation by `S`** ([88, Rademacher and Grosswald (1972),
Chapter 4, Section C, equations (65)–(67)], where the inversion is called `T`): for
`SMS⁻¹ = (d, -c; -b, a)` the two Dedekind sums `𝔰(a, |c|)` and `𝔰(d, |b|)` are related by the
reciprocity law `dedekindSum_reciprocity` applied twice, with `dedekindSum_eq_of_mul_modEq_one`
at `-bc ≡ 1 (mod a)` and `ad ≡ 1 (mod b)`, and the sign identity (67). -/
@[source "88, equation (65), p. 55"]
theorem rademacherInvariant_conj_S (M : SL(2, ℤ)) :
    rademacherInvariant (ModularGroup.S * M * ModularGroup.S⁻¹) = rademacherInvariant M := by
  by_cases hb : M 0 1 = 0
  · exact rademacherInvariant_conj_S_of_topRight_zero M hb
  by_cases hc : M 1 0 = 0
  · have hN01 : (ModularGroup.S * M * ModularGroup.S⁻¹) 0 1 = 0 := by
      rw [(conj_S_entries M).2.1, hc, neg_zero]
    have h := rademacherInvariant_conj_S_of_topRight_zero
      (ModularGroup.S * M * ModularGroup.S⁻¹) hN01
    rw [conj_S_conj_S] at h
    exact h.symm
  obtain ⟨h00, _, h10, h11⟩ := conj_S_entries M
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have h := M.2
    rwa [Matrix.det_fin_two] at h
  have hconj : (ModularGroup.S * M * ModularGroup.S⁻¹) 1 0 ≠ 0 := by
    rw [h10]
    exact neg_ne_zero.mpr hb
  rw [rademacherInvariant_of_lowerLeft_ne_zero _ hconj,
    rademacherInvariant_of_lowerLeft_ne_zero M hc, h00, h10, h11]
  exact conj_S_arithmetic hb hc hdet

/-! ### The class invariant -/

/-- **The Rademacher invariant is a class function**, the class invariance asserted in
[86, Rademacher (1955), Satz 7] and [88, Rademacher and Grosswald (1972),
Chapter 4, Section C, "the class invariant `Ψ(M)`"]: `Ψ(UMU⁻¹) = Ψ(M)` for every
`U ∈ SL₂(ℤ)`, from the two generators (`rademacherInvariant_conj_S`,
`rademacherInvariant_conj_T`) by `Subgroup.closure_induction` on
`SpecialLinearGroup.SL2Z_generators`. -/
@[source "86, Satz 7, p. 449 (class invariance)"]
theorem rademacherInvariant_conj (U M : SL(2, ℤ)) :
    rademacherInvariant (U * M * U⁻¹) = rademacherInvariant M := by
  have hU : U ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    rw [SpecialLinearGroup.SL2Z_generators]
    trivial
  suffices h : ∀ V : SL(2, ℤ), V ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} →
      ∀ N : SL(2, ℤ), rademacherInvariant (V * N * V⁻¹) = rademacherInvariant N from
    h U hU M
  intro V hV
  induction hV using Subgroup.closure_induction with
  | mem V hV =>
      rcases hV with rfl | rfl
      · exact rademacherInvariant_conj_S
      · exact rademacherInvariant_conj_T
  | one =>
      intro N
      simp
  | mul V W _ _ ihV ihW =>
      intro N
      calc
        rademacherInvariant ((V * W) * N * (V * W)⁻¹) =
            rademacherInvariant (V * (W * N * W⁻¹) * V⁻¹) := by congr 1; group
        _ = rademacherInvariant (W * N * W⁻¹) := ihV _
        _ = rademacherInvariant N := ihW _
  | inv V _ ihV =>
      intro N
      have h := ihV (V⁻¹ * N * V)
      simpa [mul_assoc] using h.symm

/-- **The eta multiplier is a class function**: `μ_{UMU⁻¹} = μ_M`
(`rademacherInvariant_conj`); the "`μ_{AγA⁻¹} = μ_γ` by the eta cocycle" of
[RW26b, Radchenko, Wheeler (2026b), Appendix B]. -/
theorem etaMultiplier_conj (U M : SL(2, ℤ)) :
    etaMultiplier (U * M * U⁻¹) = etaMultiplier M := by
  unfold etaMultiplier
  rw [rademacherInvariant_conj]

end SIC

end
