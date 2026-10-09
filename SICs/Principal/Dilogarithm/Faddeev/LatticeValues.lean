/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Dilogarithm.Faddeev.Continuation
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.FiniteCharacteristics

/-!
# Continued principal products at zero-class lattice arguments

The continued principal product at a zero-class lattice argument is `ε^{1/2}/μ_{A_d}` or
`ε^{-1/2}/μ_{A_d}` according to the sign of the lattice index, and after a simultaneous index shift
by `j` according to its position relative to `jH`.

This module follows the zero-class values `F^±_γ(u) = ε^{±1/2}` of
[RW26, Radchenko, Wheeler (2026), Section 1, equation (2), `eq:fgam.def`] and the residue
bookkeeping of Section 3.2, the proof of Theorem 2, `thm:fg.equs`, at `γ = A_d`, `τ = ρ_d`,
`ε = ρ_d³`.

## The argument

For a zero-class source pair `x = (m, k)` the lattice argument is a lattice point
`z_x = Kρ_d + L`, and the two lattice shift laws of Section 2.2 give
`Φ_{m,0}(z_x + w) = Φ_{m+K, K(1-d) - d(d-2)L}(w)` as germs at `w = 0`. Reading the action
`(A_d - I)r = (-k, m)` at the integral characteristic `r = (-L, K)` gives
`m = -d(d-2)L - dK`, so the two indices coincide: the shifted product is the diagonal product
`Φ_{j,j}` with `j = m + K = -S_d(x)/(d(d-3))`.

For `j ≥ 1`, the index shift laws give
`Φ_{j,j}(w) = Φ_{0,0}(w) ∏_{i<j} (1 - q^i e(w/ε))/(1 - q^i e(w))`
with `q = e(ρ_d)`; the factor `i = 0` tends to `1/ε` as `w → 0`, the others to `1`. For `j ≤ 0` the
inverse product has no factor `i = 0` and tends to `1`. Since `Φ_{0,0}` is regular at the origin
with value `ε^{1/2}/μ_{A_d}`, the continued value at `z_x` is `ε^{1/2}/μ_{A_d}` when
`S_d(x) ≥ 0` and
`ε^{-1/2}/μ_{A_d}` when `S_d(x) < 0`. These are the source's `F⁺(0)` and `F⁻(0)`; which of the two
a residue computation meets depends only on the sign of the lattice index of the representative.
-/

noncomputable section

open Complex Filter Topology
open scoped MatrixGroups

namespace SIC

/-! ### Lattice shifts and the diagonal product

Iterating the two lattice shift laws moves the argument by an arbitrary lattice vector. On the
diagonal `Φ_{j,j}` the index shift laws separate a finite product of `q`-factors from `Φ_{0,0}`.
-/

/-- The finite `q`-factor ratio relating `Φ_{j,j}` to `Φ_{0,0}`:
`∏_{i<j} (1 - q^i e(w/ε))/(1 - q^i e(w))` for `j ≥ 0` and
`∏_{i<-j} (1 - q^{-(i+1)} e(w))/(1 - q^{-(i+1)} e(w/ε))` for `j < 0`, with `q = e(ρ_d)` and
`ε = ρ_d³`. Its punctured limit at the origin is `1/ε` for `j ≥ 1` and `1` otherwise. -/
def principalFiveTermDiagonalRatio (d : ℕ) (j : ℤ) (w : ℂ) : ℂ :=
  if 0 ≤ j then
    ∏ i ∈ Finset.range j.toNat,
      (1 - Complex.exp (2 * Real.pi * I *
          (w / (principalRoot d : ℂ) ^ 3 + i * (principalRoot d : ℂ)))) /
        (1 - Complex.exp (2 * Real.pi * I * (w + i * (principalRoot d : ℂ))))
  else
    ∏ i ∈ Finset.range (-j).toNat,
      (1 - Complex.exp (2 * Real.pi * I * (w - ((i : ℂ) + 1) * (principalRoot d : ℂ)))) /
        (1 - Complex.exp (2 * Real.pi * I *
          (w / (principalRoot d : ℂ) ^ 3 - ((i : ℂ) + 1) * (principalRoot d : ℂ))))

/-- The numerator factor in the diagonal index shift. -/
private def principalDiagonalNumerator (d : ℕ) (i : ℤ) (w : ℂ) : ℂ :=
  1 - Complex.exp (2 * Real.pi * I *
    (w / (principalRoot d : ℂ) ^ 3 + i * (principalRoot d : ℂ)))

/-- The denominator factor in the diagonal index shift. -/
private def principalDiagonalDenominator (d : ℕ) (i : ℤ) (w : ℂ) : ℂ :=
  1 - Complex.exp (2 * Real.pi * I * (w + i * (principalRoot d : ℂ)))

/-- One simultaneous index shift multiplies the principal product by `A_i(w)/B_i(w)`. -/
private lemma principalFaddeev_diag_step_eventuallyEq (d : ℕ) (hd : 3 < d)
    (i : ℤ) (z : ℂ) :
    principalFaddeev d (i + 1) (i + 1) =ᶠ[𝓝[≠] z]
      (fun w => principalFaddeev d i i w *
        (principalDiagonalNumerator d i w / principalDiagonalDenominator d i w)) := by
  have hleft := principalFaddeev_index_add_one_left_eventuallyEq d hd i (i + 1) z
  have hright := principalFaddeev_index_add_one_right_eventuallyEq d hd i i z
  have hden : ∀ᶠ w in 𝓝[≠] z,
      1 - Complex.exp (2 * Real.pi * I * (w + i * (principalRoot d : ℂ))) ≠ 0 := by
    filter_upwards [eventually_exp_affine_ne_nhdsNE (2 * Real.pi * I)
      ((2 * Real.pi * I) * (i * (principalRoot d : ℂ))) 1 z
      Complex.two_pi_I_ne_zero] with w hw
    exact sub_ne_zero.mpr (by simpa only [mul_add] using hw.symm)
  filter_upwards [hleft, hright, hden] with w hl hr hne
  have hl' : principalFaddeev d (i + 1) (i + 1) w *
      principalDiagonalDenominator d i w = principalFaddeev d i (i + 1) w := hl
  have hr' : principalFaddeev d i (i + 1) w =
      principalDiagonalNumerator d i w * principalFaddeev d i i w := by
    simpa only [principalDiagonalNumerator, principalJacobiFactor_eq_principalRoot_pow_three d hd,
      Complex.ofReal_pow] using hr
  have hne' : principalDiagonalDenominator d i w ≠ 0 := hne
  apply mul_right_cancel₀ hne'
  calc
    principalFaddeev d (i + 1) (i + 1) w * principalDiagonalDenominator d i w =
        principalDiagonalNumerator d i w * principalFaddeev d i i w := hl'.trans hr'
    _ = (principalFaddeev d i i w *
        (principalDiagonalNumerator d i w / principalDiagonalDenominator d i w)) *
          principalDiagonalDenominator d i w := by field_simp [hne]

/-- Appending one nonnegative diagonal factor extends the finite ratio. -/
private lemma principalFiveTermDiagonalRatio_succ_nat (d i : ℕ) (w : ℂ) :
    principalFiveTermDiagonalRatio d ((i : ℤ) + 1) w =
      principalFiveTermDiagonalRatio d i w *
        (principalDiagonalNumerator d i w / principalDiagonalDenominator d i w) := by
  simp only [principalFiveTermDiagonalRatio, Int.toNat_natCast_add_one,
    Finset.prod_range_succ, neg_add_rev, Int.reduceNeg, Nat.cast_nonneg, ↓reduceIte,
    Int.toNat_natCast, principalDiagonalNumerator, Int.cast_natCast,
    principalDiagonalDenominator, ite_eq_left_iff, not_le]
  intro h
  omega

/-- Appending one negative diagonal factor extends the inverse finite ratio. -/
private lemma principalFiveTermDiagonalRatio_pred_nat (d i : ℕ) (w : ℂ) :
    principalFiveTermDiagonalRatio d (-((i : ℤ) + 1)) w =
      principalFiveTermDiagonalRatio d (-(i : ℤ)) w *
        (principalDiagonalDenominator d (-((i : ℤ) + 1)) w /
          principalDiagonalNumerator d (-((i : ℤ) + 1)) w) := by
  by_cases hi : i = 0
  · subst i
    simp [principalFiveTermDiagonalRatio, principalDiagonalNumerator,
      principalDiagonalDenominator, sub_eq_add_neg]
  · have hpos : 0 < i := Nat.pos_of_ne_zero hi
    simp [principalFiveTermDiagonalRatio, principalDiagonalNumerator,
      principalDiagonalDenominator, Finset.prod_range_succ, hi,
      sub_eq_add_neg, -Finset.prod_div_distrib]
    split_ifs with hguard
    · omega
    · congr 2 <;> congr 2 <;> ring_nf

/-- The numerator factor also has isolated zeros, so the diagonal step can be reversed. -/
private lemma principalDiagonalNumerator_eventually_ne_zero (d : ℕ) (hd : 3 < d)
    (i : ℤ) (z : ℂ) : ∀ᶠ w in 𝓝[≠] z, principalDiagonalNumerator d i w ≠ 0 := by
  let ε : ℂ := (principalRoot d : ℂ) ^ 3
  have hε : ε ≠ 0 := pow_ne_zero 3 (ofReal_principalRoot_ne_zero d hd)
  have hb : (2 * Real.pi * I : ℂ) / ε ≠ 0 :=
    div_ne_zero Complex.two_pi_I_ne_zero hε
  have heq : principalDiagonalNumerator d i =
      fun w => 1 - Complex.exp (((2 * Real.pi * I : ℂ) / ε) *
        (w + i * (principalRoot d : ℂ) * ε)) := by
    funext w
    simp only [principalDiagonalNumerator]
    congr 1
    dsimp only [ε]
    field_simp
  rw [heq]
  filter_upwards [eventually_exp_affine_ne_nhdsNE
    ((2 * Real.pi * I : ℂ) / ε) (((2 * Real.pi * I : ℂ) / ε) *
      (i * (principalRoot d : ℂ) * ε)) 1 z hb] with w hw
  exact sub_ne_zero.mpr (by simpa only [mul_add] using hw.symm)

/-- Reverse one simultaneous index shift as a punctured germ. -/
private lemma principalFaddeev_diag_step_rev_eventuallyEq (d : ℕ) (hd : 3 < d)
    (i : ℤ) (z : ℂ) :
    principalFaddeev d i i =ᶠ[𝓝[≠] z]
      (fun w => principalFaddeev d (i + 1) (i + 1) w *
        (principalDiagonalDenominator d i w / principalDiagonalNumerator d i w)) := by
  have hden : ∀ᶠ w in 𝓝[≠] z,
      1 - Complex.exp (2 * Real.pi * I * (w + i * (principalRoot d : ℂ))) ≠ 0 := by
    filter_upwards [eventually_exp_affine_ne_nhdsNE (2 * Real.pi * I)
      ((2 * Real.pi * I) * (i * (principalRoot d : ℂ))) 1 z
      Complex.two_pi_I_ne_zero] with w hw
    exact sub_ne_zero.mpr (by simpa only [mul_add] using hw.symm)
  filter_upwards [principalFaddeev_diag_step_eventuallyEq d hd i z,
    principalDiagonalNumerator_eventually_ne_zero d hd i z, hden] with w hs hne hd'
  rw [hs]
  change principalDiagonalDenominator d i w ≠ 0 at hd'
  field_simp [hne, hd']

/-- The lattice shift by `Kρ_d + L` changes the indices by `(K, K(1-d) - d(d-2)L)`, as germs at
every complex argument. The general lemma `eventuallyEq_add_int_mul_of_add` iterates
`principalFaddeev_add_one_eventuallyEq` and
`principalFaddeev_add_principalRoot_eventuallyEq`, the two lattice shift laws of
[RW26, Radchenko, Wheeler (2026), Section 2.2] at `A_d`. -/
theorem principalFaddeev_add_lattice_eventuallyEq (d : ℕ) (hd : 3 < d)
    (m n K L : ℤ) (z : ℂ) :
    (fun w => principalFaddeev d m n (w + ((K : ℂ) * (principalRoot d : ℂ) + L)))
      =ᶠ[𝓝[≠] z]
      (fun w => principalFaddeev d (m + K)
        (n + K * (1 - (d : ℤ)) - (d : ℤ) * ((d : ℤ) - 2) * L) w) := by
  let F : (ℤ × ℤ) → ℂ → ℂ := fun p => principalFaddeev d p.1 p.2
  let C : ℤ := (d : ℤ) * ((d : ℤ) - 2)
  have hunit : ∀ p z, (fun w => F p (w + 1)) =ᶠ[𝓝[≠] z] F (p + (0, -C)) := by
    intro p z
    simpa [F, C, sub_eq_add_neg] using
      principalFaddeev_add_one_eventuallyEq d hd p.1 p.2 z
  have hroot : ∀ p z, (fun w => F p (w + (principalRoot d : ℂ))) =ᶠ[𝓝[≠] z]
      F (p + (1, 1 - (d : ℤ))) := by
    intro p z
    convert principalFaddeev_add_principalRoot_eventuallyEq d hd p.1 p.2 z using 1
    ext w
    simp [F, Prod.fst_add, Prod.snd_add]
    ring_nf
  have hL := eventuallyEq_comp_add_const_nhdsNE (c := (K : ℂ) * principalRoot d)
    (eventuallyEq_add_int_mul_of_add F 1 (0, -C) hunit L (m, n)
      (z + (K : ℂ) * principalRoot d))
  have hK := eventuallyEq_add_int_mul_of_add F (principalRoot d : ℂ)
    (1, 1 - (d : ℤ)) hroot K ((m, n) + L • (0, -C)) z
  have ht := hL.trans hK
  simpa [F, C, Prod.fst_add, Prod.snd_add, add_mul, mul_comm, add_assoc,
    add_left_comm, add_comm, sub_eq_add_neg] using ht

/-- The lattice shift germ becomes a pointwise identity where both products are analytic. -/
theorem principalFaddeev_add_lattice_of_notMem
    (d : ℕ) (hd : 3 < d) (m n K L : ℤ) (z : ℂ)
    (hz : ¬ IsPeriodLatticePoint (principalRoot d : ℂ) z) :
    principalFaddeev d m n
        (z + ((K : ℂ) * (principalRoot d : ℂ) + L)) =
      principalFaddeev d (m + K)
        (n + K * (1 - (d : ℤ)) - (d : ℤ) * ((d : ℤ) - 2) * L) z := by
  have hz' : ¬ IsPeriodLatticePoint (principalRoot d : ℂ)
      (z + ((K : ℂ) * (principalRoot d : ℂ) + L)) := by
    simpa only [add_assoc] using
      (isPeriodLatticePoint_add_int_mul_add_int_iff
        (principalRoot d : ℂ) z K L).not.mpr hz
  have ht : ContinuousAt
      (fun w : ℂ => w + ((K : ℂ) * (principalRoot d : ℂ) + L)) z := by
    exact continuousAt_id.add continuousAt_const
  have hf : ContinuousAt (fun w : ℂ => principalFaddeev d m n
      (w + ((K : ℂ) * (principalRoot d : ℂ) + L))) z := by
    exact ContinuousAt.comp
      (f := fun w : ℂ => w + ((K : ℂ) * (principalRoot d : ℂ) + L))
      (g := principalFaddeev d m n)
      (analyticAt_principalFaddeev d hd m n _
        (principalFaddeevGammaRegular_of_notMem d hd m n _ hz')).continuousAt
      ht
  have hg : ContinuousAt (principalFaddeev d (m + K)
      (n + K * (1 - (d : ℤ)) - (d : ℤ) * ((d : ℤ) - 2) * L)) z := by
    exact (analyticAt_principalFaddeev d hd _ _ _
      (principalFaddeevGammaRegular_of_notMem d hd _ _ _ hz)).continuousAt
  exact eq_of_eventuallyEq_nhdsNE_of_continuousAt hf hg
    (principalFaddeev_add_lattice_eventuallyEq d hd m n K L z)

/-- On the diagonal, the index shift laws factor `Φ_{j,j}` as `Φ_{0,0}` times the finite ratio
`principalFiveTermDiagonalRatio`, as germs at every complex argument. This iterates
`principalFaddeev_index_add_one_left_eventuallyEq` and
`principalFaddeev_index_add_one_right_eventuallyEq`. -/
theorem principalFaddeev_diag_eventuallyEq (d : ℕ) (hd : 3 < d) (j : ℤ) (z : ℂ) :
    principalFaddeev d j j =ᶠ[𝓝[≠] z]
      (fun w => principalFaddeev d 0 0 w * principalFiveTermDiagonalRatio d j w) := by
  induction j using Int.induction_on with
  | zero => simp [principalFiveTermDiagonalRatio]
  | succ i hi =>
    filter_upwards [principalFaddeev_diag_step_eventuallyEq d hd i z, hi]
      with w hs hiw
    rw [hs, hiw, principalFiveTermDiagonalRatio_succ_nat]
    ring
  | pred i hi =>
    have hrev := principalFaddeev_diag_step_rev_eventuallyEq d hd
      (-((i : ℤ) + 1)) z
    filter_upwards [hrev, hi] with w hr hiw
    have hindex : -((i : ℤ) + 1) + 1 = -(i : ℤ) := by omega
    rw [hindex, hiw] at hr
    have hr' : principalFaddeev d (-((i : ℤ) + 1)) (-((i : ℤ) + 1)) w =
        principalFaddeev d 0 0 w *
          principalFiveTermDiagonalRatio d (-((i : ℤ) + 1)) w := by
      rw [hr, principalFiveTermDiagonalRatio_pred_nat]
      ring
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hr'

/-- A nonzero power of `q = e(ρ_d)` is not one. -/
private lemma principalDiagonalDenominator_zero_ne (d : ℕ) (hd : 3 < d)
    (i : ℤ) (hi : i ≠ 0) : principalDiagonalDenominator d i 0 ≠ 0 := by
  have hreal : ∀ n : ℤ, (i : ℝ) * principalRoot d ≠ n := by
    intro n hn
    have hrel : (((i : ℤ) : ℚ) : ℝ) * principalRoot d = (((n : ℤ) : ℚ) : ℝ) := by
      simpa using hn
    exact hi (by exact_mod_cast (ratCast_eq_zero_of_irrational_mul
      (principalRoot_irrational d hd) hrel).1)
  simpa [principalDiagonalDenominator] using
    one_sub_exp_two_pi_I_ne_zero_of_forall_ne_int
      ((i : ℝ) * principalRoot d) hreal

/-- Every nonzero-index diagonal factor has punctured limit one. -/
private lemma tendsto_diagonalQuotient_of_ne_zero (d : ℕ) (hd : 3 < d)
    (i : ℤ) (hi : i ≠ 0) :
    Tendsto (fun w => principalDiagonalNumerator d i w / principalDiagonalDenominator d i w)
      (𝓝[≠] 0) (𝓝 1) := by
  have hA : ContinuousAt (principalDiagonalNumerator d i) 0 := by
    unfold principalDiagonalNumerator
    fun_prop
  have hB : ContinuousAt (principalDiagonalDenominator d i) 0 := by
    unfold principalDiagonalDenominator
    fun_prop
  have heq : principalDiagonalNumerator d i 0 = principalDiagonalDenominator d i 0 := by
    simp [principalDiagonalNumerator, principalDiagonalDenominator]
  have hne := principalDiagonalDenominator_zero_ne d hd i hi
  convert (hA.tendsto.mono_left nhdsWithin_le_nhds).div
    (hB.tendsto.mono_left nhdsWithin_le_nhds) hne using 1
  simp [heq, hne]

/-- The inverse of a nonzero-index diagonal factor also tends to one. -/
private lemma tendsto_diagonalQuotient_inv_of_ne_zero
    (d : ℕ) (hd : 3 < d) (i : ℤ) (hi : i ≠ 0) :
    Tendsto (fun w => principalDiagonalDenominator d i w / principalDiagonalNumerator d i w)
      (𝓝[≠] 0) (𝓝 1) := by
  have hA : ContinuousAt (principalDiagonalNumerator d i) 0 := by
    unfold principalDiagonalNumerator
    fun_prop
  have hB : ContinuousAt (principalDiagonalDenominator d i) 0 := by
    unfold principalDiagonalDenominator
    fun_prop
  have heq : principalDiagonalNumerator d i 0 = principalDiagonalDenominator d i 0 := by
    simp [principalDiagonalNumerator, principalDiagonalDenominator]
  have hne := principalDiagonalDenominator_zero_ne d hd i hi
  convert (hB.tendsto.mono_left nhdsWithin_le_nhds).div
    (hA.tendsto.mono_left nhdsWithin_le_nhds) (heq.symm ▸ hne) using 1
  simp [heq, hne]

/-- The exceptional zero-index factor has limit `ε⁻¹`. -/
private lemma tendsto_diagonalQuotient_zero (d : ℕ) (hd : 3 < d) :
    Tendsto (fun w => principalDiagonalNumerator d 0 w /
      principalDiagonalDenominator d 0 w) (𝓝[≠] 0)
      (𝓝 (((principalRoot d : ℂ) ^ 3)⁻¹)) := by
  let ε : ℂ := (principalRoot d : ℂ) ^ 3
  have hε : ε ≠ 0 := pow_ne_zero 3 (ofReal_principalRoot_ne_zero d hd)
  have hlim := tendsto_one_sub_exp_mul_div ((2 * Real.pi * I) / ε)
    (2 * Real.pi * I) Complex.two_pi_I_ne_zero
  convert hlim using 1
  · funext w
    simp only [principalDiagonalNumerator, principalDiagonalDenominator,
      Int.cast_zero, zero_mul, add_zero, ε]
    congr 2
    field_simp
  · dsimp only [ε]
    field_simp [Complex.two_pi_I_ne_zero, hε]

/-- Positive induction step for the diagonal ratio's punctured limit. -/
private lemma tendsto_principalFiveTermDiagonalRatio_succ_nat
    (d : ℕ) (hd : 3 < d) (i : ℕ)
    (hi : Tendsto (principalFiveTermDiagonalRatio d i) (𝓝[≠] 0)
      (𝓝 (if 1 ≤ (i : ℤ) then ((principalRoot d : ℂ) ^ 3)⁻¹ else 1))) :
    Tendsto (principalFiveTermDiagonalRatio d ((i : ℤ) + 1)) (𝓝[≠] 0)
      (𝓝 (if 1 ≤ (i : ℤ) + 1 then ((principalRoot d : ℂ) ^ 3)⁻¹ else 1)) := by
  have hfun : principalFiveTermDiagonalRatio d ((i : ℤ) + 1) =
      fun w => principalFiveTermDiagonalRatio d i w *
        (principalDiagonalNumerator d i w / principalDiagonalDenominator d i w) :=
    funext (principalFiveTermDiagonalRatio_succ_nat d i)
  rw [hfun]
  by_cases hi0 : i = 0
  · subst i
    have h := hi.mul (tendsto_diagonalQuotient_zero d hd)
    simpa using h
  · have hfactor := tendsto_diagonalQuotient_of_ne_zero
      d hd i (by exact_mod_cast hi0)
    have h := hi.mul hfactor
    have hipos : (1 : ℤ) ≤ i := by omega
    have hjpos : (1 : ℤ) ≤ (i : ℤ) + 1 := by omega
    simpa [hipos, hjpos] using h

/-- Negative induction step for the diagonal ratio's punctured limit. -/
private lemma tendsto_principalFiveTermDiagonalRatio_pred_nat
    (d : ℕ) (hd : 3 < d) (i : ℕ)
    (hi : Tendsto (principalFiveTermDiagonalRatio d (-(i : ℤ))) (𝓝[≠] 0)
      (𝓝 (if 1 ≤ -(i : ℤ) then ((principalRoot d : ℂ) ^ 3)⁻¹ else 1))) :
    Tendsto (principalFiveTermDiagonalRatio d (-(i : ℤ) - 1)) (𝓝[≠] 0)
      (𝓝 (if 1 ≤ -(i : ℤ) - 1 then ((principalRoot d : ℂ) ^ 3)⁻¹ else 1)) := by
  have hfun : principalFiveTermDiagonalRatio d (-((i : ℤ) + 1)) =
      fun w => principalFiveTermDiagonalRatio d (-(i : ℤ)) w *
        (principalDiagonalDenominator d (-((i : ℤ) + 1)) w /
          principalDiagonalNumerator d (-((i : ℤ) + 1)) w) :=
    funext (principalFiveTermDiagonalRatio_pred_nat d i)
  have hindex : -((i : ℤ) + 1) ≠ 0 := by omega
  have hfactor := tendsto_diagonalQuotient_inv_of_ne_zero
    d hd (-((i : ℤ) + 1)) hindex
  have h := hi.mul hfactor
  have hneg : ¬(1 : ℤ) ≤ -((i : ℤ) + 1) := by omega
  have hineg : ¬(1 : ℤ) ≤ -(i : ℤ) := by omega
  have heq : -(i : ℤ) - 1 = -((i : ℤ) + 1) := by omega
  rw [heq, hfun]
  simpa only [ite_eq_right hneg, ite_eq_right hineg, one_mul] using h

/-- The diagonal ratio tends to `1/ε` at the origin when `j ≥ 1` and to `1` otherwise: the
factor `i = 0` is `(1 - e(w/ε))/(1 - e(w)) → 1/ε`, and every other factor is continuous and
nonzero at `0` because `q^i ≠ 1` for `i ≠ 0`. -/
theorem tendsto_principalFiveTermDiagonalRatio_zero (d : ℕ) (hd : 3 < d) (j : ℤ) :
    Tendsto (principalFiveTermDiagonalRatio d j) (𝓝[≠] 0)
      (𝓝 (if 1 ≤ j then ((principalRoot d : ℂ) ^ 3)⁻¹ else 1)) := by
  induction j using Int.induction_on with
  | zero =>
    change Tendsto (fun _ : ℂ => (1 : ℂ)) (𝓝[≠] 0) (𝓝 1)
    exact tendsto_const_nhds
  | succ i hi => exact tendsto_principalFiveTermDiagonalRatio_succ_nat d hd i hi
  | pred i hi => exact tendsto_principalFiveTermDiagonalRatio_pred_nat d hd i hi

/-- The normal-form diagonal product has no pole at the origin; used to evaluate its limit. -/
private lemma analyticAt_continued_diag_zero
    (d : ℕ) (hd : 3 < d) (j : ℤ) :
    AnalyticAt ℂ (principalFaddeevContinued d j j) 0 := by
  have ho : meromorphicOrderAt (principalFaddeev d j j) 0 = 0 := by
    simpa using meromorphicOrderAt_principalFaddeev_real_lattice d hd j j 0 0
  apply (principalFaddeevContinued_meromorphicNFAt d hd j j 0
    |>.meromorphicOrderAt_nonneg_iff_analyticAt).mp
  rw [meromorphicOrderAt_principalFaddeevContinued d hd, ho]

/-- The continued diagonal product at the origin:
`Φ^cont_{j,j}(0) = ε^{1/2}/μ_{A_d}` for `j ≤ 0` and `ε^{-1/2}/μ_{A_d}` for `j ≥ 1`. -/
theorem principalFaddeevContinued_diag_zero (d : ℕ) (hd : 3 < d) (j : ℤ) :
    principalFaddeevContinued d j j 0 =
      (if 1 ≤ j then ((principalRoot d : ℂ) ^ 3)⁻¹ else 1) *
        ((Real.sqrt (principalRoot d ^ 3) : ℂ) / etaMultiplier (principalA d)) := by
  have hbase : Tendsto (principalFaddeev d 0 0) (𝓝[≠] 0)
      (𝓝 ((Real.sqrt (principalRoot d ^ 3) : ℂ) / etaMultiplier (principalA d))) := by
    rw [← principalFaddeev_zero_eq_etaMultiplier d hd]
    exact (analyticAt_principalFaddeev d hd 0 0 0
      (principalFaddeevGammaRegular_zero d hd)).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
  have hraw : Tendsto (principalFaddeev d j j) (𝓝[≠] 0)
      (𝓝 ((if 1 ≤ j then ((principalRoot d : ℂ) ^ 3)⁻¹ else 1) *
        ((Real.sqrt (principalRoot d ^ 3) : ℂ) / etaMultiplier (principalA d)))) := by
    convert (hbase.mul (tendsto_principalFiveTermDiagonalRatio_zero d hd j)).congr'
      (principalFaddeev_diag_eventuallyEq d hd j 0).symm using 1
    ring_nf
  have hcont := (analyticAt_continued_diag_zero d hd j).continuousAt
  apply tendsto_nhds_unique (l := 𝓝[≠] (0 : ℂ))
  · exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  · exact hraw.congr'
      (principalFaddeev_eventuallyEq_continued d hd j j 0)

/-! ### Zero-class lattice arguments

A zero-class source pair has an integral rational characteristic. Its lattice coordinates
determine the pair, and the lattice index of the pair measures the position of its lattice
argument relative to the diagonal threshold.
-/

/-- The first row of `(A_d-I)r=(-k,m)` at `r=(-L,K)` gives `k` in lattice coordinates. -/
private lemma k_eq_of_characteristic_eq
    (d : ℕ) (hd : 3 < d) (m k K L : ℤ)
    (hrK : (principalFiveTermRationalCharacteristic d m k) 1 = (K : ℚ))
    (hrL : (principalFiveTermRationalCharacteristic d m k) 0 = -(L : ℚ)) :
    k = (((d : ℤ) - 1) * ((d : ℤ) ^ 2 - 2 * d - 1) - 1) * L +
      ((d : ℤ) * ((d : ℤ) - 2)) * K := by
  let r := principalFiveTermRationalCharacteristic d m k
  change r 1 = (K : ℚ) at hrK
  change r 0 = -(L : ℚ) at hrL
  have hrow₀ := congrFun
    (ratVecAction_rationalCharacteristic_sub d hd m k) 0
  simp only [Pi.sub_apply, Matrix.cons_val_zero] at hrow₀
  change ratVecAction (principalA d : Mat(2, ℤ)) r 0 - r 0 = (-(k : ℤ) : ℚ) at hrow₀
  have hk' : (k : ℚ) =
      (((d : ℚ) - 1) * ((d : ℚ) ^ 2 - 2 * d - 1) - 1) * L +
        ((d : ℚ) * ((d : ℚ) - 2)) * K := by
    simp [ratVecAction, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      coe_principalA, hrK, hrL] at hrow₀
    linear_combination hrow₀
  exact_mod_cast hk'

/-- The two rows of `(A_d-I)r=(-k,m)` at `r=(-L,K)` determine the lattice index. -/
private lemma m_eq_and_latticeIndex_eq_of_characteristic_eq
    (d : ℕ) (hd : 3 < d) (m k K L : ℤ)
    (hrK : (principalFiveTermRationalCharacteristic d m k) 1 = (K : ℚ))
    (hrL : (principalFiveTermRationalCharacteristic d m k) 0 = -(L : ℚ)) :
    m = -((d : ℤ) * ((d : ℤ) - 2)) * L - (d : ℤ) * K ∧
      principalFiveTermLatticeIndex d m k =
        -(principalFiveTermUpperIndexBound d) * (m + K) := by
  let r := principalFiveTermRationalCharacteristic d m k
  change r 1 = (K : ℚ) at hrK
  change r 0 = -(L : ℚ) at hrL
  have hrow := congrFun
    (ratVecAction_rationalCharacteristic_sub d hd m k) 1
  simp only [Pi.sub_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hrow
  change ratVecAction (principalA d : Mat(2, ℤ)) r 1 - r 1 = (m : ℚ) at hrow
  have hm : m = -((d : ℤ) * ((d : ℤ) - 2)) * L - (d : ℤ) * K := by
    have hrow' : (m : ℚ) = -((d : ℚ) * ((d : ℚ) - 2)) * L - (d : ℚ) * K := by
      simp [ratVecAction, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        coe_principalA, hrK, hrL] at hrow
      linear_combination hrow.symm
    exact_mod_cast hrow'
  refine ⟨hm, ?_⟩
  simp only [principalFiveTermLatticeIndex, principalFiveTermUpperIndexBound]
  rw [k_eq_of_characteristic_eq d hd m k K L hrK hrL, hm]
  ring

/-- A zero-class source pair `(m, k)` has lattice argument `Kρ_d + L` with
`m = -d(d-2)L - dK` and `S_d(m, k) = -d(d-3)(m + K)`. The characteristic
`principalFiveTermRationalCharacteristic d m k` is the integral vector `(-L, K)`, and the two
rows of `(A_d - I)r = (-k, m)` give the two identities. -/
theorem exists_lattice_coordinates_of_residue_eq_zero
    (d : ℕ) (hd : 3 < d) (m k : ℤ)
    (h : principalFiveTermCharacteristicResidue d m k = 0) :
    ∃ K L : ℤ,
      (principalFiveTermLatticeArgument d m k : ℂ) = (K : ℂ) * (principalRoot d : ℂ) + L ∧
      m = -((d : ℤ) * ((d : ℤ) - 2)) * L - (d : ℤ) * K ∧
      principalFiveTermLatticeIndex d m k = -(principalFiveTermUpperIndexBound d) * (m + K) := by
  have hlattice : IsPeriodLatticePoint (principalRoot d : ℂ)
      (principalFiveTermLatticeArgument d m k : ℂ) := by
    by_contra hn
    exact ((not_isPeriodLatticePoint_latticeArgument_iff
      d hd m k).mp hn) h
  obtain ⟨L, K, hz⟩ := hlattice
  let r := principalFiveTermRationalCharacteristic d m k
  have harg := congrArg (fun x : ℝ => (x : ℂ))
    (fracSymplecticFormRat_rationalCharacteristic d hd m k)
  have hreal : (r 1 : ℝ) * principalRoot d - (r 0 : ℝ) =
      (L : ℝ) + (K : ℝ) * principalRoot d := by
    simpa [r, fracSymplecticFormRat] using congrArg Complex.re (harg.trans hz)
  have hrel : ((r 1 - (K : ℚ) : ℚ) : ℝ) * principalRoot d =
      ((r 0 + (L : ℚ) : ℚ) : ℝ) := by
    push_cast
    linear_combination hreal
  obtain ⟨hK, hL⟩ := ratCast_eq_zero_of_irrational_mul
    (principalRoot_irrational d hd) hrel
  have hrK : r 1 = (K : ℚ) := sub_eq_zero.mp hK
  have hrL : r 0 = -(L : ℚ) := add_eq_zero_iff_eq_neg.mp hL
  obtain ⟨hm, hS⟩ := m_eq_and_latticeIndex_eq_of_characteristic_eq
    d hd m k K L hrK hrL
  exact ⟨K, L, by simpa [add_comm, mul_comm] using hz, hm, hS⟩

/-- A translated germ equality identifies continued values at analytic points. -/
private lemma continued_eq_of_shift_eventuallyEq
    (d : ℕ) (hd : 3 < d) (m n m' n' : ℤ) (z : ℂ)
    (hshift : (fun w => principalFaddeev d m n (w + z)) =ᶠ[𝓝[≠] 0]
      principalFaddeev d m' n')
    (ha : AnalyticAt ℂ (principalFaddeevContinued d m n) z)
    (hb : AnalyticAt ℂ (principalFaddeevContinued d m' n') 0) :
    principalFaddeevContinued d m n z =
      principalFaddeevContinued d m' n' 0 := by
  have ht : Tendsto (fun w : ℂ => w + z) (𝓝[≠] 0) (𝓝 z) := by
    convert ((tendsto_id.add_const z).mono_left nhdsWithin_le_nhds) using 1 <;> simp
  have hleft : Tendsto (fun w => principalFaddeev d m n (w + z))
      (𝓝[≠] 0) (𝓝 (principalFaddeevContinued d m n z)) := by
    have hc := ha.continuousAt.tendsto.comp ht
    have heq := eventuallyEq_comp_add_const_nhdsNE (z := 0) (c := z)
      (show principalFaddeev d m n =ᶠ[𝓝[≠] (0 + z)]
        principalFaddeevContinued d m n by
          simpa only [zero_add] using
            principalFaddeev_eventuallyEq_continued
              d hd m n z)
    exact hc.congr' heq.symm
  have hright : Tendsto (principalFaddeev d m' n') (𝓝[≠] 0)
      (𝓝 (principalFaddeevContinued d m' n' 0)) := by
    exact (hb.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
      (principalFaddeev_eventuallyEq_continued
        d hd m' n' 0).symm
  exact tendsto_nhds_unique (hright.congr' hshift.symm) hleft |>.symm

/-- The continued source product is analytic at its characteristic argument. -/
private lemma analyticAt_continued_latticeArgument
    (d : ℕ) (hd : 3 < d) (m k j : ℤ) :
    AnalyticAt ℂ (principalFaddeevContinued d (m + j) j)
      (principalFiveTermLatticeArgument d m k) := by
  have h' := analyticAt_principalFaddeevContinued_characteristic d hd
    (principalFiveTermRationalCharacteristic d m k) j
  rw [nQPInt_principalFiveTermRationalCharacteristic d hd m k,
    ← ofReal_fracSymplecticFormRat,
    fracSymplecticFormRat_rationalCharacteristic d hd m k] at h'
  simpa using h'

/-- For the shifted diagonal, `jH_d ≤ S_d=-H_d(m+K)` is equivalent to `m+K+j≤0`. -/
private lemma upperIndexBound_mul_le_latticeIndex_iff
    (d : ℕ) (hd : 3 < d) (m k K j : ℤ)
    (hS : principalFiveTermLatticeIndex d m k =
      -(principalFiveTermUpperIndexBound d) * (m + K)) :
    (principalFiveTermUpperIndexBound d * j ≤ principalFiveTermLatticeIndex d m k) ↔
      ¬1 ≤ m + K + j := by
  have hH : 0 < principalFiveTermUpperIndexBound d :=
    principalFiveTermUpperIndexBound_pos d hd
  rw [hS, show -(principalFiveTermUpperIndexBound d) * (m + K) =
    principalFiveTermUpperIndexBound d * (-(m + K)) by ring,
    mul_le_mul_iff_right₀ hH]
  omega

/-! ### Simultaneously shifted source indices

The closed form in Section 3.2 has second index `1`. More generally, a simultaneous index
shift by `j` moves the diagonal threshold from `0` to `jH`: the zero-class value is `F⁺(0)`
when `jH ≤ S_d(x)` and `F⁻(0)` otherwise. Off the zero class the index shifts preserve the
finite value by equation (16), so the same rule covers every source pair.
-/

/-- The zero-class calculation for the shifted type rule
`etaMultiplier_mul_principalFaddeevContinued_indices_add`.
The lattice shift sends `Φ^cont_{m+j,j}(z_x)` to `Φ^cont_{m+K+j,m+K+j}(0)`. -/
private lemma continued_indices_add_of_residue_eq_zero
    (d : ℕ) (hd : 3 < d) (m k j : ℤ)
    (h : principalFiveTermCharacteristicResidue d m k = 0) :
    principalFaddeevContinued d (m + j) j
        (principalFiveTermLatticeArgument d m k) =
      (if principalFiveTermUpperIndexBound d * j ≤ principalFiveTermLatticeIndex d m k
        then 1 else ((principalRoot d : ℂ) ^ 3)⁻¹) *
        ((Real.sqrt (principalRoot d ^ 3) : ℂ) / etaMultiplier (principalA d)) := by
  obtain ⟨K, L, hz, hm, hS⟩ :=
    exists_lattice_coordinates_of_residue_eq_zero d hd m k h
  let t : ℤ := m + K + j
  have hidx : j + K * (1 - (d : ℤ)) -
      (d : ℤ) * ((d : ℤ) - 2) * L = t := by
    dsimp only [t]
    rw [hm]
    ring
  have hshift := principalFaddeev_add_lattice_eventuallyEq d hd (m + j) j K L 0
  rw [hidx] at hshift
  rw [← hz] at hshift
  have hshift' : (fun w => principalFaddeev d (m + j) j
      (w + (principalFiveTermLatticeArgument d m k : ℂ))) =ᶠ[𝓝[≠] 0]
      principalFaddeev d t t := by
    simpa [t, add_assoc, add_left_comm, add_comm] using hshift
  have hval := continued_eq_of_shift_eventuallyEq
    d hd (m + j) j t t _ hshift'
      (analyticAt_continued_latticeArgument d hd m k j)
      (analyticAt_continued_diag_zero d hd t)
  rw [hval, principalFaddeevContinued_diag_zero d hd t]
  have hsign : (principalFiveTermUpperIndexBound d * j ≤
      principalFiveTermLatticeIndex d m k) ↔ ¬1 ≤ t :=
    upperIndexBound_mul_le_latticeIndex_iff d hd m k K j hS
  by_cases hs : principalFiveTermUpperIndexBound d * j ≤
      principalFiveTermLatticeIndex d m k
  · have ht := hsign.mp hs
    simp [hs, ht]
  · have ht : 1 ≤ t := by
      by_contra hj
      exact hs (hsign.mpr hj)
    simp [hs, ht]

/-! The value conversion uses `principalDilogE_zero` and `principalDilogEMinus_zero`. -/

/-- Converts the shifted zero-class product to `F⁺(0)` or `F⁻(0)` for
`etaMultiplier_mul_principalFaddeevContinued_indices_add`. -/
private lemma principalFaddeev_shifted_zero_value
    (d : ℕ) (hd : 3 < d) (m k j : ℤ)
    (h : principalFiveTermCharacteristicResidue d m k = 0) :
    etaMultiplier (principalA d) *
        principalFaddeevContinued d (m + j) j
          (principalFiveTermLatticeArgument d m k) =
      if principalFiveTermUpperIndexBound d * j ≤ principalFiveTermLatticeIndex d m k
        then principalDilogE d 0
      else principalDilogEMinus d 0 := by
  rw [continued_indices_add_of_residue_eq_zero
      d hd m k j h,
    principalDilogE_zero, principalDilogEMinus_zero,
    principalJacobiFactor_eq_principalRoot_pow_three d hd]
  have hε : (principalRoot d : ℂ) ^ 3 ≠ 0 :=
    pow_ne_zero 3 (ofReal_principalRoot_ne_zero d hd)
  have hμ := etaMultiplier_ne_zero (principalA d)
  have hsq : ((Real.sqrt (principalRoot d ^ 3) : ℂ)) ^ 2 =
      (principalRoot d : ℂ) ^ 3 := by
    exact_mod_cast Real.sq_sqrt (pow_nonneg (le_of_lt (principalRoot_pos d hd)) 3)
  have hs : (Real.sqrt (principalRoot d ^ 3) : ℂ) ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by norm_num)] at hsq
    exact hε hsq.symm
  split_ifs
  · field_simp [hμ]
  · rw [Complex.ofReal_inv]
    field_simp [hμ, hε, hs]
    rw [hsq]
    exact div_self hε

/-- Equation (16), `eq:faddeevperiod`, at a nonzero source residue. This supplies the
off-zero-class step of
`etaMultiplier_mul_principalFaddeevContinued_indices_add`. -/
private lemma principalFaddeev_indices_add_of_residue_ne_zero
    (d : ℕ) (hd : 3 < d) (m k j : ℤ)
    (h : principalFiveTermCharacteristicResidue d m k ≠ 0) :
    principalFaddeev d (m + j) j (principalFiveTermLatticeArgument d m k) =
      principalFaddeev d m 0 (principalFiveTermLatticeArgument d m k) := by
  have hz := (not_isPeriodLatticePoint_latticeArgument_iff d hd m k).2 h
  have hphase : Complex.exp (2 * Real.pi * I *
        ((principalFiveTermLatticeArgument d m k : ℂ) + m * (principalRoot d : ℂ))) =
      Complex.exp (2 * Real.pi * I *
        ((principalFiveTermLatticeArgument d m k : ℂ) /
          (principalJacobiFactor d : ℂ) + ((0 : ℤ) : ℂ) * (principalRoot d : ℂ))) := by
    simpa [principalJacobiFactor_eq_principalRoot_pow_three d hd, add_comm] using
      (principalFiveTermLatticeArgument_exp_lower d hd m k)
  have h₀ := (principalFaddeevGammaRegular_of_notMem d hd
    (m + max j 0) 0 _ hz).last
  have h₂ := (principalFaddeevGammaRegular_of_notMem d hd
    m (min j 0) _ hz).first
  simpa using principalFaddeev_indices_add d hd m 0 j
    (principalFiveTermLatticeArgument d m k) hphase h₀
    (by simpa only [zero_add] using h₂)

/-- The shifted type rule in [RW26, Radchenko, Wheeler (2026), Section 3.2, the proof of
Theorem 2, `thm:fg.equs`]: `μ Φ^cont_{m+j,j}(z_x)` is `F⁺(x)` when `jH ≤ S_d(x)` and
`F⁻(x)` otherwise. At the zero class this follows from
`principalFaddeevContinued_diag_zero`; off it the two finite values agree. -/
theorem etaMultiplier_mul_principalFaddeevContinued_indices_add
    (d : ℕ) (hd : 3 < d) (m k j : ℤ) :
    etaMultiplier (principalA d) *
        principalFaddeevContinued d (m + j) j
          (principalFiveTermLatticeArgument d m k) =
      if principalFiveTermUpperIndexBound d * j ≤ principalFiveTermLatticeIndex d m k then
        principalDilogE d (principalFiveTermCharacteristicResidue d m k)
      else principalDilogEMinus d (principalFiveTermCharacteristicResidue d m k) := by
  by_cases h : principalFiveTermCharacteristicResidue d m k = 0
  · simpa only [h] using
      principalFaddeev_shifted_zero_value
        d hd m k j h
  · have hz := (not_isPeriodLatticePoint_latticeArgument_iff d hd m k).2 h
    rw [principalFaddeevContinued_eq_of_notMem d hd _ _ _ hz,
      principalFaddeev_indices_add_of_residue_ne_zero d hd m k j h,
      principalDilogEMinus_of_ne_zero d hd h]
    simp only [ite_self]
    exact (principalDilogE_characteristicResidue d hd m k h).symm

end SIC

end
