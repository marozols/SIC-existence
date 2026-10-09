/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Dilogarithm.Faddeev.Divisor

/-!
# Continued principal Faddeev products

The meromorphic normal form in the argument gives the continued principal product at every
finite characteristic.

This module follows the special values of [RW26, Radchenko, Wheeler (2026), equation (2),
`eq:fgam.def`], the zero and pole support in Section 2.2, and the product expression of
Proposition 2(ii), equation (20), `eq:modulartofaddeevCF`, at `A_d` and `τ = ρ_d`.

## The argument

For fixed `d`, `m`, and `n`, the raw three-factor product is meromorphic in `z`. Its Mathlib
normal form changes only the point value at each singularity. Although the definition below is
pointwise, it agrees with the single global normal form on `Set.univ`; hence it has the raw
product's punctured germs and meromorphic orders everywhere.

At `z = ⟨⟨r,ρ_d⟩⟩`, the order of the product with indices
`(-nQPInt r A_d+j,j)` is zero. Here `nQPInt` is the total integer convention `Rat.num`; on the
source domain `A_d ∈ Γ_r` it is the source index `n_QP(r,A_d)`. Outside that domain, a
nonintegral characteristic is off the period lattice, so the order vanishes for arbitrary
integer outer indices. If `r = (-ℓ,k)` is integral, `nQPInt` reduces directly to
`dk+d(d-2)ℓ`, and the two indicators in the exact lattice-order formula have the same argument.
Thus the continued value is analytic and nonzero, and the raw product tends to it through the
punctured neighborhood.

At a genuine pole the normal form assigns the total value zero; it does not turn that pole into
a finite meromorphic value. This construction varies only `z` at the fixed period `ρ_d`.
Removing these `z`-singularities does not establish joint continuity or meromorphic continuation
in `τ`.
-/

noncomputable section

open Filter Topology
open scoped MatrixGroups

namespace SIC

/-! ### Global normal form in the argument

The pointwise definition is identified with Mathlib's global normal form, which supplies its
meromorphic API and comparison with the raw punctured germs.
-/

/-- The continued value of the principal product in its argument `z`, with the period fixed at
`ρ_d`. It is the value of the meromorphic normal form of
`Φ_{A_d,m,n}(z;ρ_d)`. At nonzero meromorphic order this totalized value is zero. -/
def principalFaddeevContinued (d : ℕ) (m n : ℤ) (z : ℂ) : ℂ :=
  toMeromorphicNFAt (principalFaddeev d m n) z z

/-- The raw principal product is meromorphic on the whole argument plane; used to identify the
pointwise continued definition with one global normal form. -/
private lemma meromorphicOn_principalFaddeev (d : ℕ) (hd : 3 < d)
    (m n : ℤ) : MeromorphicOn (principalFaddeev d m n) Set.univ :=
  fun z _ => meromorphicAt_principalFaddeev d hd m n z

/-- The pointwise continued principal product is the global meromorphic normal form of the raw
product on the whole argument plane. -/
theorem principalFaddeevContinued_eq_toMeromorphicNFOn
    (d : ℕ) (hd : 3 < d) (m n : ℤ) :
    principalFaddeevContinued d m n =
      toMeromorphicNFOn (principalFaddeev d m n) Set.univ := by
  funext z
  rw [principalFaddeevContinued,
    toMeromorphicNFOn_eq_toMeromorphicNFAt
      (meromorphicOn_principalFaddeev d hd m n) (Set.mem_univ z)]

/-- The continued principal product has meromorphic normal form at every complex argument. -/
theorem principalFaddeevContinued_meromorphicNFAt
    (d : ℕ) (hd : 3 < d) (m n : ℤ) (z : ℂ) :
    MeromorphicNFAt (principalFaddeevContinued d m n) z := by
  rw [principalFaddeevContinued_eq_toMeromorphicNFOn d hd m n]
  exact meromorphicNFOn_toMeromorphicNFOn _ _ (Set.mem_univ z)

/-- The raw and continued principal products have the same punctured germ at every argument. -/
theorem principalFaddeev_eventuallyEq_continued
    (d : ℕ) (hd : 3 < d) (m n : ℤ) (z : ℂ) :
    principalFaddeev d m n =ᶠ[𝓝[≠] z]
      principalFaddeevContinued d m n := by
  rw [principalFaddeevContinued_eq_toMeromorphicNFOn d hd m n]
  exact (meromorphicOn_principalFaddeev d hd m n
    |>.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z)).symm

/-- Continuation in `z` preserves the meromorphic order of the raw principal product. -/
theorem meromorphicOrderAt_principalFaddeevContinued
    (d : ℕ) (hd : 3 < d) (m n : ℤ) (z : ℂ) :
    meromorphicOrderAt (principalFaddeevContinued d m n) z =
      meromorphicOrderAt (principalFaddeev d m n) z := by
  rw [principalFaddeevContinued_eq_toMeromorphicNFOn d hd m n,
    meromorphicOrderAt_toMeromorphicNFOn
      (meromorphicOn_principalFaddeev d hd m n) (Set.mem_univ z)]

/-! ### The finite characteristics

For nonintegral characteristics, irrationality excludes the period lattice. For integral
characteristics, the total index `nQPInt` is computed directly from the integer coordinates, and
the two lattice-order indicators coincide after their coordinates are expanded.
-/

/-- At an integral characteristic `r = (-ℓ,k)`, the total principal finite index is
`nQPInt r A_d = dk+d(d-2)ℓ`; used by the integral branch of the order calculation. -/
private lemma nQPInt_principalA_of_integral_coordinates (d : ℕ) {r : Fin 2 → ℚ}
    (k l : ℤ)
    (hr₀ : r 0 = ((-l : ℤ) : ℚ)) (hr₁ : r 1 = (k : ℚ)) :
    nQPInt r (principalA d) =
      (d : ℤ) * k + (d : ℤ) * ((d : ℤ) - 2) * l := by
  have hq : nQP r (principalA d : Mat(2, ℤ)) =
      (((d : ℤ) * k + (d : ℤ) * ((d : ℤ) - 2) * l : ℤ) : ℚ) := by
    simp [nQP, coe_principalA, hr₀, hr₁]
    ring
  rw [nQPInt, hq, Rat.num_intCast]

/-- At every rational characteristic, simultaneous shifts of the two outer indices have order
zero at the characteristic argument:
`ord Φ_{A_d,-nQPInt(r,A_d)+j,j}(⟨⟨r,ρ_d⟩⟩;ρ_d) = 0`.

For an integral `r = (-ℓ,k)`, both indicators of [RW26, Radchenko, Wheeler (2026), Section 2.2]
have argument `(1-d)k-d(d-2)ℓ+j`. The statement shifts both indices by the same `j`; it makes no
claim for unmatched shifts. On the source domain `A_d ∈ Γ_r`, `nQPInt r A_d` represents
`n_QP(r,A_d)`; outside it, the theorem uses `nQPInt`'s total `Rat.num` convention. -/
theorem meromorphicOrderAt_principalFaddeev_characteristic
    (d : ℕ) (hd : 3 < d) (r : Fin 2 → ℚ) (j : ℤ) :
    meromorphicOrderAt
        (principalFaddeev d (-nQPInt r (principalA d) + j) j)
        (fracSymplecticFormRat r (principalRoot d) : ℂ) = 0 := by
  by_cases hr : IsIntegralIndex r
  · obtain ⟨r₀, hr₀⟩ := hr 0
    obtain ⟨r₁, hr₁⟩ := hr 1
    let k : ℤ := r₁
    let l : ℤ := -r₀
    have hz : (fracSymplecticFormRat r (principalRoot d) : ℂ) =
        (k : ℂ) * (principalRoot d : ℂ) + l := by
      rw [fracSymplecticFormRat, hr₀, hr₁]
      simp only [k, l, Int.cast_neg]
      push_cast
      ring
    have hN := nQPInt_principalA_of_integral_coordinates d k l
      (by simpa only [l, neg_neg] using hr₀) (by simpa only [k] using hr₁)
    have hthreshold : k + (-nQPInt r (principalA d) + j) =
        (1 - (d : ℤ)) * k - (d : ℤ) * ((d : ℤ) - 2) * l + j := by
      rw [hN]
      ring
    rw [hz, meromorphicOrderAt_principalFaddeev_real_lattice d hd, hthreshold]
    simp
  · have hoff := (isPeriodLatticePoint_fracSymplecticFormRat_iff
      (principalRoot_irrational d hd) r).not.mpr hr
    exact meromorphicOrderAt_principalFaddeev_eq_zero
      d hd _ _ _ hoff

/-- The continued principal product with simultaneously shifted indices is nonzero at every
finite characteristic. This converts the order-zero calculation into the point-value statement
for the global normal form. -/
theorem principalFaddeevContinued_characteristic_ne_zero
    (d : ℕ) (hd : 3 < d) (r : Fin 2 → ℚ) (j : ℤ) :
    principalFaddeevContinued d (-nQPInt r (principalA d) + j) j
      (fracSymplecticFormRat r (principalRoot d) : ℂ) ≠ 0 := by
  apply (principalFaddeevContinued_meromorphicNFAt d hd _ _ _
    |>.meromorphicOrderAt_eq_zero_iff).mp
  rw [meromorphicOrderAt_principalFaddeevContinued d hd,
    meromorphicOrderAt_principalFaddeev_characteristic d hd r j]

/-- The continued principal product with simultaneously shifted indices is analytic at every
finite characteristic. -/
theorem analyticAt_principalFaddeevContinued_characteristic
    (d : ℕ) (hd : 3 < d) (r : Fin 2 → ℚ) (j : ℤ) :
    AnalyticAt ℂ
      (principalFaddeevContinued d (-nQPInt r (principalA d) + j) j)
      (fracSymplecticFormRat r (principalRoot d) : ℂ) := by
  apply (principalFaddeevContinued_meromorphicNFAt d hd _ _ _
    |>.meromorphicOrderAt_nonneg_iff_analyticAt).mp
  rw [meromorphicOrderAt_principalFaddeevContinued d hd,
    meromorphicOrderAt_principalFaddeev_characteristic d hd r j]

/-- The raw product with simultaneously shifted indices tends through the punctured
characteristic neighborhood to its continued value. This varies only `z`, with `ρ_d` fixed. -/
theorem tendsto_principalFaddeev_continued_characteristic
    (d : ℕ) (hd : 3 < d) (r : Fin 2 → ℚ) (j : ℤ) :
    Tendsto (principalFaddeev d (-nQPInt r (principalA d) + j) j)
      (𝓝[≠] (fracSymplecticFormRat r (principalRoot d) : ℂ))
      (𝓝 (principalFaddeevContinued d (-nQPInt r (principalA d) + j) j
        (fracSymplecticFormRat r (principalRoot d) : ℂ))) := by
  exact (analyticAt_principalFaddeevContinued_characteristic d hd r j)
    |>.continuousAt.tendsto |>.mono_left nhdsWithin_le_nhds |>.congr'
      (principalFaddeev_eventuallyEq_continued d hd _ _ _).symm

/-! ### Agreement with raw values

At an analytic point, normal-form continuation leaves the raw point value unchanged. This gives
the factorwise gamma-domain and lattice-free comparisons.
-/

/-- On the factorwise gamma domain, the continued principal product equals the raw product. -/
theorem principalFaddeevContinued_eq_of_gammaRegular
    (d : ℕ) (hd : 3 < d) (m n : ℤ) (z : ℂ)
    (hz : PrincipalFaddeevGammaRegular d m n z) :
    principalFaddeevContinued d m n z = principalFaddeev d m n z := by
  unfold principalFaddeevContinued
  rw [toMeromorphicNFAt_eq_self.mpr
    (analyticAt_principalFaddeev d hd m n z hz).meromorphicNFAt]

/-- Away from `ℤ+ℤρ_d`, the continued and raw principal products agree. -/
theorem principalFaddeevContinued_eq_of_notMem
    (d : ℕ) (hd : 3 < d) (m n : ℤ) (z : ℂ)
    (hz : ¬ IsPeriodLatticePoint (principalRoot d) z) :
    principalFaddeevContinued d m n z = principalFaddeev d m n z := by
  exact principalFaddeevContinued_eq_of_gammaRegular d hd m n z
    (principalFaddeevGammaRegular_of_notMem d hd m n z hz)

end SIC

end
