/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Dilogarithm.Faddeev.Basic

/-!
# The divisor of the principal Faddeev product

Exact meromorphic orders of the principal three-factor product on and off its period lattice.

This module follows the zero and pole calculation in
[RW26, Radchenko, Wheeler (2026), Section 2.2], using the three-factor expression of
Proposition 2(ii), equation (20), `eq:modulartofaddeevCF`, at `A_d` and `τ = ρ_d`.

## The argument

Write `b = d-1` and `z = kρ_d+ℓ`. Since `ρ_d⁻¹ = b-ρ_d`, division by `ρ_d`
changes the coordinates to `(-ℓ,k+bℓ)`. A second division changes them to
`(-k-bℓ,bk+(b²-1)ℓ)`. The order of each generator is the difference of its two
coordinate half-plane indicators. Adding all three orders cancels the intermediate
indicators and leaves `1_{k+m≤0} - 1_{k'+n≤0}`, where
`k' = (1-d)k-d(d-2)ℓ` is the coordinate in the basis transformed by `A_d`.
Off the period lattice, all three factors have order zero.

These are identities of meromorphic orders. Totalized point values can be zero at a
removable zero-pole cancellation and do not determine the divisor there.
-/

noncomputable section

open Filter
open scoped Topology

namespace SIC

/-! ### The lattice divisor

The generator orders add after the affine changes of argument, whose derivatives
are nonzero. The result keeps only the two outer index conditions.
-/

/-- Division by $ρ_d$ sends lattice coordinates $(k,ℓ)$ to $(-ℓ,k+(d-1)ℓ)$.
Used by `meromorphicOrderAt_principalFaddeev_real_lattice`. -/
private lemma principal_div_coordinates (d : ℕ) (hd : 3 < d) (k l : ℤ) :
    (((k : ℂ) * (principalRoot d : ℂ) + l) / (principalRoot d : ℂ)) =
      ((-l : ℤ) : ℂ) * (principalRoot d : ℂ) +
        ((k + ((d : ℤ) - 1) * l : ℤ) : ℂ) := by
  let ρ : ℂ := principalRoot d
  have hinv : ρ⁻¹ = (d : ℂ) - 1 - ρ := ofReal_principalRoot_inv d hd
  change ((k : ℂ) * ρ + l) / ρ =
    ((-l : ℤ) : ℂ) * ρ + ((k + ((d : ℤ) - 1) * l : ℤ) : ℂ)
  have hquad : ρ ^ 2 - ((d : ℂ) - 1) * ρ + 1 = 0 :=
    ofReal_principalRoot_quadratic d hd
  rw [div_eq_mul_inv, hinv]
  push_cast
  linear_combination -(k : ℂ) * hquad

/-- Two divisions by $ρ_d$ give the coordinates of the first principal factor.
Used by `meromorphicOrderAt_principalFaddeev_real_lattice`. -/
private lemma principal_div_sq_coordinates (d : ℕ) (hd : 3 < d) (k l : ℤ) :
    (((k : ℂ) * (principalRoot d : ℂ) + l) / (principalRoot d : ℂ) ^ 2) =
      ((-k - ((d : ℤ) - 1) * l : ℤ) : ℂ) * (principalRoot d : ℂ) +
        (((d : ℤ) - 1) * k + (((d : ℤ) - 1) ^ 2 - 1) * l : ℤ) := by
  let ρ : ℂ := principalRoot d
  calc
    ((k : ℂ) * ρ + l) / ρ ^ 2 = (((k : ℂ) * ρ + l) / ρ) / ρ := by
      rw [pow_two, div_mul_eq_div_div]
    _ = (((-l : ℤ) : ℂ) * ρ +
        ((k + ((d : ℤ) - 1) * l : ℤ) : ℂ)) / ρ := by
      rw [principal_div_coordinates d hd]
    _ = ((-(k + ((d : ℤ) - 1) * l) : ℤ) : ℂ) * ρ +
        ((-l + ((d : ℤ) - 1) * (k + ((d : ℤ) - 1) * l) : ℤ) : ℂ) := by
      exact principal_div_coordinates d hd (-l) (k + ((d : ℤ) - 1) * l)
    _ = _ := by push_cast; ring

/-- The divisor order of the principal product is the sum of its three generator orders.
Specializes `meromorphicOrderAt_faddeevS_div_add` at its three affine factors;
used by both principal divisor theorems. -/
private lemma principal_order_sum (d : ℕ) (hd : 3 < d) (m n : ℤ) (z : ℂ) :
    meromorphicOrderAt (principalFaddeev d m n) z =
      meromorphicOrderAt (fun w : ℂ => faddeevS w (principalRoot d))
        (z / (principalRoot d : ℂ) ^ 2 - n) +
      meromorphicOrderAt (fun w : ℂ => faddeevS w (principalRoot d))
        (z / (principalRoot d : ℂ)) +
      meromorphicOrderAt (fun w : ℂ => faddeevS w (principalRoot d))
        (z + m * (principalRoot d : ℂ)) := by
  let ρ : ℂ := principalRoot d
  have hρ : ρ ≠ 0 := ofReal_principalRoot_ne_zero d hd
  have hslit : ρ ∈ Complex.slitPlane := ofReal_principalRoot_mem_slitPlane d hd
  have h₂ := meromorphicAt_faddeevS_div_add ρ hslit (ρ ^ 2) (-n) z
  have h₁ := meromorphicAt_faddeevS_div_add ρ hslit ρ 0 z
  have h₀ := meromorphicAt_faddeevS_div_add ρ hslit 1 (m * ρ) z
  unfold principalFaddeev
  simp only [sub_eq_add_neg]
  change meromorphicOrderAt
    ((fun w : ℂ => faddeevS (w / ρ ^ 2 + -n) ρ) *
     (fun w : ℂ => faddeevS (w / ρ) ρ) *
     (fun w : ℂ => faddeevS (w + m * ρ) ρ)) z = _
  rw [meromorphicOrderAt_mul (h₂.mul (by simpa only [add_zero] using h₁))
      (by simpa only [div_one] using h₀),
    meromorphicOrderAt_mul h₂ (by simpa only [add_zero] using h₁)]
  rw [meromorphicOrderAt_faddeevS_div_add ρ (ρ ^ 2) (-n) z (pow_ne_zero _ hρ),
    show meromorphicOrderAt (fun w : ℂ => faddeevS (w / ρ) ρ) z =
      meromorphicOrderAt (fun w : ℂ => faddeevS w ρ) (z / ρ) by
      simpa only [add_zero] using meromorphicOrderAt_faddeevS_div_add ρ ρ 0 z hρ,
    show meromorphicOrderAt (fun w : ℂ => faddeevS (w + m * ρ) ρ) z =
      meromorphicOrderAt (fun w : ℂ => faddeevS w ρ) (z + m * ρ) by
      simpa only [div_one] using meromorphicOrderAt_faddeevS_div_add ρ 1 (m * ρ) z one_ne_zero]

/-- The intermediate lattice indicators cancel, leaving the two outer conditions.
Used by `meromorphicOrderAt_principalFaddeev_real_lattice`. -/
private lemma principal_indicator_cancellation (d : ℕ) (m n k l : ℤ) :
    ((if -k - ((d : ℤ) - 1) * l ≤ 0 then (1 : ℤ) else 0) -
       (if 0 ≤ ((d : ℤ) - 1) * k + (((d : ℤ) - 1) ^ 2 - 1) * l - n
        then 1 else 0)) +
      ((if -l ≤ 0 then (1 : ℤ) else 0) -
        (if 0 ≤ k + ((d : ℤ) - 1) * l then 1 else 0)) +
      ((if k + m ≤ 0 then (1 : ℤ) else 0) -
        (if 0 ≤ l then 1 else 0)) =
      ((if k + m ≤ 0 then (1 : ℤ) else 0) -
        (if (1 - (d : ℤ)) * k - (d : ℤ) * ((d : ℤ) - 2) * l + n ≤ 0
          then 1 else 0)) := by
  have h₁ : (-k - ((d : ℤ) - 1) * l ≤ 0) ↔
      (0 ≤ k + ((d : ℤ) - 1) * l) := by omega
  have h₂ : (-l ≤ 0) ↔ (0 ≤ l) := by omega
  have h₃ : (0 ≤ ((d : ℤ) - 1) * k + (((d : ℤ) - 1) ^ 2 - 1) * l - n) ↔
      ((1 - (d : ℤ)) * k - (d : ℤ) * ((d : ℤ) - 2) * l + n ≤ 0) := by
    constructor <;> intro h <;> nlinarith [h]
  simp only [h₁, h₂, h₃]
  ring

/-- At `z = kρ_d+ℓ`, the order of `Φ_{A_d,m,n}` is
`1_{k+m≤0} - 1_{k'+n≤0}`, with `k' = (1-d)k-d(d-2)ℓ`, as in the zero and pole
sets of [RW26, Radchenko, Wheeler (2026), Section 2.2].
Specializes `meromorphicOrderAt_faddeevS_real_lattice` at the three principal arguments. -/
theorem meromorphicOrderAt_principalFaddeev_real_lattice (d : ℕ) (hd : 3 < d)
    (m n k l : ℤ) :
    meromorphicOrderAt (principalFaddeev d m n)
        ((k : ℂ) * (principalRoot d : ℂ) + l) =
      (((if k + m ≤ 0 then (1 : ℤ) else 0) -
        (if (1 - (d : ℤ)) * k - (d : ℤ) * ((d : ℤ) - 2) * l + n ≤ 0
          then 1 else 0) : ℤ) : WithTop ℤ) := by
  let ρ : ℂ := principalRoot d
  have hfirst : ((k : ℂ) * ρ + l) / ρ ^ 2 - n =
      ((-k - ((d : ℤ) - 1) * l : ℤ) : ℂ) * ρ +
        ((((d : ℤ) - 1) * k + (((d : ℤ) - 1) ^ 2 - 1) * l - n : ℤ) : ℂ) := by
    rw [principal_div_sq_coordinates d hd k l]
    push_cast
    ring
  have hmid := principal_div_coordinates d hd k l
  have hlast : (k : ℂ) * ρ + l + m * ρ = ((k + m : ℤ) : ℂ) * ρ + l := by
    push_cast
    ring
  rw [principal_order_sum d hd m n, hfirst, hmid, hlast]
  rw [meromorphicOrderAt_faddeevS_real_lattice (principalRoot d)
        (principalRoot_pos d hd) (principalRoot_irrational d hd)
        (-k - ((d : ℤ) - 1) * l)
        (((d : ℤ) - 1) * k + (((d : ℤ) - 1) ^ 2 - 1) * l - n),
      meromorphicOrderAt_faddeevS_real_lattice (principalRoot d)
        (principalRoot_pos d hd) (principalRoot_irrational d hd)
        (-l) (k + ((d : ℤ) - 1) * l),
      meromorphicOrderAt_faddeevS_real_lattice (principalRoot d)
        (principalRoot_pos d hd) (principalRoot_irrational d hd)
        (k + m) l]
  exact_mod_cast principal_indicator_cancellation d m n k l

/-- At $kρ_d+ℓ$, the principal product has positive order exactly when $k+m≤0$ and
$(1-d)k-d(d-2)ℓ+n>0$. This is the zero support of
`meromorphicOrderAt_principalFaddeev_real_lattice`. -/
theorem meromorphicOrderAt_principalFaddeev_pos_iff (d : ℕ) (hd : 3 < d)
    (m n k l : ℤ) :
    0 < meromorphicOrderAt (principalFaddeev d m n)
        ((k : ℂ) * (principalRoot d : ℂ) + l) ↔
      k + m ≤ 0 ∧
        0 < (1 - (d : ℤ)) * k - (d : ℤ) * ((d : ℤ) - 2) * l + n := by
  rw [meromorphicOrderAt_principalFaddeev_real_lattice d hd]
  norm_cast
  split_ifs <;> simp_all [Int.subNatNat, not_le]

/-- At $kρ_d+ℓ$, the principal product has negative order exactly when $k+m>0$ and
$(1-d)k-d(d-2)ℓ+n≤0$. This is the pole support of
`meromorphicOrderAt_principalFaddeev_real_lattice`. -/
theorem meromorphicOrderAt_principalFaddeev_neg_iff (d : ℕ) (hd : 3 < d)
    (m n k l : ℤ) :
    meromorphicOrderAt (principalFaddeev d m n)
        ((k : ℂ) * (principalRoot d : ℂ) + l) < 0 ↔
      0 < k + m ∧
        (1 - (d : ℤ)) * k - (d : ℤ) * ((d : ℤ) - 2) * l + n ≤ 0 := by
  rw [meromorphicOrderAt_principalFaddeev_real_lattice d hd]
  norm_cast
  split_ifs <;> simp_all [Int.subNatNat, not_le]

/-- Division by $ρ_d$ preserves the complement of its integer lattice.
Specializes `isPeriodLatticePoint_div_fltDenominator_iff` at `principalU d`;
used by `principalFaddeev_arguments_notMem_lattice`. -/
private lemma principal_not_mem_lattice_div (d : ℕ) (hd : 3 < d) (z : ℂ)
    (hz : ¬ IsPeriodLatticePoint (principalRoot d) z) :
    ¬ IsPeriodLatticePoint (principalRoot d) (z / (principalRoot d : ℂ)) := by
  have hden : fltDenominator (↑(principalU d))
      (principalRoot d : ℂ) = principalRoot d := by
    exact_mod_cast fltDenominator_principalU_principalRoot d
  have hfix : flt (↑(principalU d)) (principalRoot d : ℂ) =
      principalRoot d := flt_principalU_principalRoot_complex d hd
  have htransport := isPeriodLatticePoint_div_fltDenominator_iff (principalU d)
    (by rw [hden]; exact ofReal_principalRoot_ne_zero d hd) z
  simpa only [hden, hfix] using htransport.not.mpr hz

/-- The three arguments in equation (20) at the principal fixed point stay off
`ℤ+ℤρ_d` when `z` does. This is the lattice transport used by the divisor and
real-period continuity of `principalFaddeev`. -/
theorem principalFaddeev_arguments_notMem_lattice (d : ℕ) (hd : 3 < d)
    (m n : ℤ) (z : ℂ) (hz : ¬ IsPeriodLatticePoint (principalRoot d) z) :
    ¬ IsPeriodLatticePoint (principalRoot d) (z / (principalRoot d : ℂ) ^ 2 - n) ∧
      ¬ IsPeriodLatticePoint (principalRoot d) (z / (principalRoot d : ℂ)) ∧
      ¬ IsPeriodLatticePoint (principalRoot d) (z + m * (principalRoot d : ℂ)) := by
  have hzmid := principal_not_mem_lattice_div d hd z hz
  have hzsq : ¬ IsPeriodLatticePoint (principalRoot d)
      (z / (principalRoot d : ℂ) ^ 2) := by
    simpa only [pow_two, div_mul_eq_div_div] using
      principal_not_mem_lattice_div d hd (z / (principalRoot d : ℂ)) hzmid
  have hzfirst : ¬ IsPeriodLatticePoint (principalRoot d)
      (z / (principalRoot d : ℂ) ^ 2 - n) := by
    simpa only [Int.cast_zero, zero_mul, add_zero, Int.cast_neg,
      sub_eq_add_neg] using
      (isPeriodLatticePoint_add_int_mul_add_int_iff
        (principalRoot d) (z / (principalRoot d : ℂ) ^ 2) 0 (-n)).not.mpr hzsq
  have hzlast : ¬ IsPeriodLatticePoint (principalRoot d)
      (z + m * (principalRoot d : ℂ)) := by
    simpa only [Int.cast_zero, add_zero] using
      (isPeriodLatticePoint_add_int_mul_add_int_iff
        (principalRoot d) z m 0).not.mpr hz
  exact ⟨hzfirst, hzmid, hzlast⟩

/-- Off the principal period lattice, all three gamma denominators of the concrete
principal Faddeev product are nonzero. -/
theorem principalFaddeevGammaRegular_of_notMem (d : ℕ) (hd : 3 < d)
    (m n : ℤ) (z : ℂ) (hz : ¬ IsPeriodLatticePoint (principalRoot d) z) :
    PrincipalFaddeevGammaRegular d m n z := by
  obtain ⟨hzfirst, hzmid, hzlast⟩ :=
    principalFaddeev_arguments_notMem_lattice d hd m n z hz
  have hslit : (principalRoot d : ℂ) ∈ Complex.slitPlane :=
    ofReal_principalRoot_mem_slitPlane d hd
  exact ⟨faddeevS_denominator_ne_zero_of_not_mem_lattice _ _ hslit hzfirst,
    faddeevS_denominator_ne_zero_of_not_mem_lattice _ _ hslit hzmid,
    faddeevS_denominator_ne_zero_of_not_mem_lattice _ _ hslit hzlast⟩

/-- Off `ℤ+ℤρ_d`, the pointwise principal product is nonzero.
Specializes `faddeevS_ne_zero_of_not_mem_lattice` at the three arguments of equation (20). -/
theorem principalFaddeev_ne_zero_of_notMem (d : ℕ) (hd : 3 < d)
    (m n : ℤ) (z : ℂ) (hz : ¬ IsPeriodLatticePoint (principalRoot d) z) :
    principalFaddeev d m n z ≠ 0 := by
  obtain ⟨hzfirst, hzmid, hzlast⟩ :=
    principalFaddeev_arguments_notMem_lattice d hd m n z hz
  have hslit : (principalRoot d : ℂ) ∈ Complex.slitPlane :=
    ofReal_principalRoot_mem_slitPlane d hd
  unfold principalFaddeev
  exact mul_ne_zero
    (mul_ne_zero
      (faddeevS_ne_zero_of_not_mem_lattice _ _ hslit hzfirst)
      (faddeevS_ne_zero_of_not_mem_lattice _ _ hslit hzmid))
    (faddeevS_ne_zero_of_not_mem_lattice _ _ hslit hzlast)

/-- Off `ℤρ_d+ℤ`, the principal Faddeev product has order zero.
Specializes `meromorphicOrderAt_faddeevS_eq_zero` at its three arguments. -/
theorem meromorphicOrderAt_principalFaddeev_eq_zero
    (d : ℕ) (hd : 3 < d) (m n : ℤ) (z : ℂ)
    (hz : ¬ IsPeriodLatticePoint (principalRoot d) z) :
    meromorphicOrderAt (principalFaddeev d m n) z = 0 := by
  obtain ⟨hzfirst, hzmid, hzlast⟩ :=
    principalFaddeev_arguments_notMem_lattice d hd m n z hz
  rw [principal_order_sum d hd m n z,
    meromorphicOrderAt_faddeevS_eq_zero
      _ (principalRoot d) (principalRoot_pos d hd) hzfirst,
    meromorphicOrderAt_faddeevS_eq_zero
      _ (principalRoot d) (principalRoot_pos d hd) hzmid,
    meromorphicOrderAt_faddeevS_eq_zero
      _ (principalRoot d) (principalRoot_pos d hd) hzlast]
  simp

/-- The divisor order of $\Phi_{A_d,m,n}$ is finite at every point. -/
theorem meromorphicOrderAt_principalFaddeev_ne_top
    (d : ℕ) (hd : 3 < d) (m n : ℤ) (z : ℂ) :
    meromorphicOrderAt (principalFaddeev d m n) z ≠ ⊤ := by
  by_cases hz : IsPeriodLatticePoint (principalRoot d) z
  · obtain ⟨L, K, hpoint⟩ := hz
    rw [hpoint]
    rw [show (L : ℂ) + (K : ℂ) * (principalRoot d : ℂ) =
      (K : ℂ) * (principalRoot d : ℂ) + L by ring,
      meromorphicOrderAt_principalFaddeev_real_lattice d hd m n K L]
    exact WithTop.coe_ne_top
  · rw [meromorphicOrderAt_principalFaddeev_eq_zero
      d hd m n z hz]
    exact WithTop.coe_ne_top

/-- Every pole of the principal Faddeev product is at most simple, by
`meromorphicOrderAt_principalFaddeev_real_lattice` and its off-lattice counterpart. -/
theorem meromorphicOrderAt_principalFaddeev_ge_neg_one (d : ℕ) (hd : 3 < d)
    (m n : ℤ) (z : ℂ) :
    ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (principalFaddeev d m n) z := by
  by_cases hlat : IsPeriodLatticePoint (principalRoot d : ℂ) z
  · rcases hlat with ⟨l, k, rfl⟩
    rw [show (l : ℂ) + (k : ℂ) * principalRoot d =
      (k : ℂ) * principalRoot d + l by ring,
      meromorphicOrderAt_principalFaddeev_real_lattice d hd m n k l]
    split_ifs <;> decide
  · rw [meromorphicOrderAt_principalFaddeev_eq_zero
      d hd m n z hlat]
    decide

/-- The principal Faddeev product is nonzero on a punctured neighborhood of every point. -/
theorem eventually_principalFaddeev_ne_zero
    (d : ℕ) (hd : 3 < d) (m n : ℤ) (z : ℂ) :
    ∀ᶠ ζ in 𝓝[≠] z, principalFaddeev d m n ζ ≠ 0 := by
  exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
    (meromorphicAt_principalFaddeev d hd m n z)).mp
      (meromorphicOrderAt_principalFaddeev_ne_top d hd m n z)

end SIC

end
