/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Ring.Units

/-!
# Power indices in infinite completions

The exact index of nth powers in the multiplicative group of an infinite completion.

This follows Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII,
Proposition 6.8, at infinite places.

## The argument

The power map on complex nonzero elements is surjective. On the real nonzero elements
it is surjective for odd n and has image the positive elements for even n, of index two.
Counting the roots of unity yields the uniform formula using the normalized absolute
value: the ordinary absolute value at real places and its square at complex places.
-/

noncomputable section

open NumberField

namespace SIC.InfinitePlace

/-- Every positive real unit has an nth root. Used by `real_power_index`. -/
private theorem real_pow_mem_of_pos {n : ℕ} (hn : 0 < n) (x : ℝˣ) (hx : 0 < (x : ℝ)) :
    x ∈ (powMonoidHom n : ℝˣ →* ℝˣ).range := by
  let y : ℝ := (x : ℝ) ^ (n : ℝ)⁻¹
  refine ⟨Units.mk0 y (Real.rpow_pos_of_pos hx _).ne', Units.ext ?_⟩
  exact Real.rpow_inv_natCast_pow hx.le hn.ne'

/-- For even n, the real nth-power image is exactly the positive units.
Milne, *Class Field Theory*, Chapter VII, Proposition 6.8, real-place calculation. -/
private theorem real_pow_range_even {n : ℕ} (hn : 0 < n) (heven : Even n) (x : ℝˣ) :
    x ∈ (powMonoidHom n : ℝˣ →* ℝˣ).range ↔ 0 < (x : ℝ) := by
  constructor
  · rintro ⟨y, rfl⟩
    exact heven.pow_pos y.ne_zero
  · exact real_pow_mem_of_pos hn x

/-- The real power index is two for even n and one for odd n.
Milne, *Class Field Theory*, Chapter VII, Proposition 6.8, real-place calculation. -/
private theorem real_power_index {n : ℕ} (hn : 0 < n) :
    (powMonoidHom n : ℝˣ →* ℝˣ).range.index = if Even n then 2 else 1 := by
  split_ifs with heven
  · have hpos : (powMonoidHom n : ℝˣ →* ℝˣ).range = Units.posSubgroup ℝ := by
      ext x
      exact real_pow_range_even hn heven x
    rw [hpos]
    exact Units.index_posSubgroup ℝ
  · apply Subgroup.index_eq_one.mpr
    apply MonoidHom.range_eq_top_of_surjective
    intro x
    rcases lt_or_gt_of_ne x.ne_zero with hx | hx
    · have hneg : 0 < ((-x : ℝˣ) : ℝ) := neg_pos.mpr hx
      obtain ⟨y, hy⟩ := real_pow_mem_of_pos hn (-x) hneg
      refine ⟨-y, ?_⟩
      change (-y) ^ n = x
      rw [(Nat.not_even_iff_odd.mp heven).neg_pow, show y ^ n = -x from hy, neg_neg]
    · exact real_pow_mem_of_pos hn x hx

/-- The real nth roots of unity number two for even n and one for odd n.
Milne, *Class Field Theory*, Chapter VII, Proposition 6.8, real-place calculation. -/
private theorem real_roots_card {n : ℕ} (hn : 0 < n) :
    Nat.card (rootsOfUnity n ℝ) = if Even n then 2 else 1 := by
  split_ifs with heven
  · have heq : rootsOfUnity n ℝ = rootsOfUnity 2 ℝ := by
      ext x
      simp only [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one,
        pow_eq_one_iff_of_ne_zero hn.ne', pow_eq_one_iff_of_ne_zero (by decide : 2 ≠ 0),
        heven, even_two, and_true]
    rw [heq]
    exact (IsPrimitiveRoot.neg_one (R := ℝ) 0 (by decide)).card_rootsOfUnity
  · have heq : rootsOfUnity n ℝ = ⊥ := by
      ext x
      simp only [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one,
        pow_eq_one_iff_of_ne_zero hn.ne', heven, and_false, or_false, Subgroup.mem_bot]
    rw [heq]
    exact Nat.card_unique

/-- The complex power map is surjective, so its image has index one.
Milne, *Class Field Theory*, Chapter VII, Proposition 6.8, complex-place calculation. -/
private theorem complex_power_index {n : ℕ} (hn : 0 < n) :
    (powMonoidHom n : ℂˣ →* ℂˣ).range.index = 1 := by
  apply Subgroup.index_eq_one.mpr
  apply MonoidHom.range_eq_top_of_surjective
  intro x
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x : ℂ) hn
  have hy0 : y ≠ 0 := by
    intro h
    simp only [h, zero_pow hn.ne'] at hy
    exact x.ne_zero hy.symm
  exact ⟨Units.mk0 y hy0, Units.ext hy⟩

variable {K : Type*} [Field K]

/-- At an infinite place, $[K_v^\times:K_v^{\times n}]=n|\mu_n(K_v)|/|n|_v$,
where the absolute value is squared at complex places.
Milne, *Class Field Theory*, Chapter VII, Proposition 6.8, infinite-place clause. -/
theorem card_units_powerQuotient (v : NumberField.InfinitePlace K)
    {n : ℕ} (hn : 0 < n) :
    (Nat.card (v.Completionˣ ⧸
      (powMonoidHom n : v.Completionˣ →* v.Completionˣ).range) : ℝ) =
      n * Nat.card (rootsOfUnity n v.Completion) / (n : ℝ) ^ v.mult := by
  have : NeZero n := ⟨hn.ne'⟩
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  change ((powMonoidHom n : v.Completionˣ →* v.Completionˣ).range.index : ℝ) = _
  rcases v.isReal_or_isComplex with hv | hv
  · let e := NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv
    have hi := Subgroup.index_map_equiv
      (powMonoidHom n : v.Completionˣ →* v.Completionˣ).range (Units.mapEquiv e.toMulEquiv)
    rw [MulEquiv.map_range_powMonoidHom] at hi
    rw [← hi, real_power_index hn,
      Nat.card_congr (e.toMulEquiv.restrictRootsOfUnity n).toEquiv,
      real_roots_card hn, hv.mult_eq_one, pow_one]
    apply (eq_div_iff hnR).2
    ring
  · let e := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv
    have hi := Subgroup.index_map_equiv
      (powMonoidHom n : v.Completionˣ →* v.Completionˣ).range (Units.mapEquiv e.toMulEquiv)
    rw [MulEquiv.map_range_powMonoidHom] at hi
    rw [← hi, complex_power_index hn,
      Nat.card_congr (e.toMulEquiv.restrictRootsOfUnity n).toEquiv,
      Complex.card_rootsOfUnity, hv.mult_eq_two]
    norm_num only [Nat.cast_one]
    apply (eq_div_iff (pow_ne_zero 2 hnR)).2
    ring

end SIC.InfinitePlace
