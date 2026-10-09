/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.QPochhammer.Divisor
import Mathlib.Analysis.Meromorphic.Basic

/-!
# The modular q-product on the upper half plane

The modular q-product for upper-half-plane periods, its meromorphy and pole geometry.

This module follows [RW26, Radchenko, Wheeler (2026), Section 1, equation (1),
`eq:phigam.def`] and Appendix A.2, `app:mod.fad`. Write `ε = cτ+d` and `σ = γτ`.

## The argument

The q-product factors are entire in `z`, so their quotient is meromorphic. The numerator of
`Φ_{γ,n,0}` vanishes on `ℤ-(n+ℕ)τ` and the denominator on
`ε(ℤ-ℕσ)`. Both sets lie in `ℤ+ℤτ`; a common zero is removable, although the raw
quotient takes the totalized value zero there. At an uncancelled denominator zero the
forward row index is positive. At an uncancelled numerator zero the backward row index
is positive. Their coordinate identities give height bounds, and a real bound on the zeros when
`c > 0` and `Re ε ≥ 0`. Closedness, compact finiteness and local isolation follow from
the discrete period lattice. At the common zero `z=0`, the ratio of the two first-order
q-product terms gives a removable value for fixed `τ ∈ ℍ`. These facts precede both modular
growth and five-term integrals. When `τ ∈ ℍ`, a real noninteger is outside `ℤ+ℤτ`, so neither
q-product factor vanishes there and the raw quotient is analytic and nonzero. This says nothing
about arbitrary complex inputs without lattice exclusion or about the real-period boundary.
-/

noncomputable section

open Complex Real Filter Set MeasureTheory
open scoped Topology MatrixGroups

namespace SIC

/-! ### The modular q-product

Equation (1) is a quotient of entire q-products for upper-half-plane periods, hence meromorphic.
Its totalized values are measurable, even at common zeros where the continued value can differ. -/

/-- Faddeev's modular quantum dilogarithm on the upper half plane,
`Φ_{γ,m,n}(z;τ) = (qᵐe(z);q)∞ / (q̃ⁿe(z/(cτ+d));q̃)∞` with `q = e(τ)` and `q̃ = e(γτ)`,
that is `ϖ(z+mτ,τ)/ϖ(z/j_γ(τ) + nγτ, γτ)`.
[RW26, Radchenko, Wheeler (2026), Section 1, equation (1), `eq:phigam.def`].
The source defines it by this formula for `τ ∈ ℍ` and continues it meromorphically;
this declaration is the formula on `ℍ`, and values at poles are totalized to zero. -/
@[source "RW26, equation (1), p. 2, eq:phigam.def" (symbol := "Φ_{γ,m,n}(z;τ)")]
def faddeevModularUHP (γ : SL(2, ℤ)) (m n : ℤ) (z τ : ℂ) : ℂ :=
  qPochhammer (z + m * τ) τ /
    qPochhammer (z / fltDenominator (γ : Mat(2, ℤ)) τ + n * flt (γ : Mat(2, ℤ)) τ)
      (flt (γ : Mat(2, ℤ)) τ)

/-- The shifted denominator in [RW26, Radchenko, Wheeler (2026), Section 1, equation (1),
`eq:phigam.def`] is nonzero away from `ℤ + ℤτ`. Its lattice support is also used in
[RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`]. -/
theorem qPochhammer_div_fltDenominator_add_int_mul_ne_zero
    (γ : SL(2, ℤ)) (n : ℤ) (z τ : ℂ) (hτ : 0 < τ.im)
    (hz : ¬ IsPeriodLatticePoint τ z) :
    qPochhammer (z / fltDenominator (γ : Mat(2, ℤ)) τ +
      n * flt (γ : Mat(2, ℤ)) τ) (flt (γ : Mat(2, ℤ)) τ) ≠ 0 := by
  intro hzero
  apply hz
  have hσ := flt_im_pos γ hτ
  obtain ⟨k, j, hkj⟩ :=
    isPeriodLatticePoint_of_qPochhammer_add_zero
      (flt (γ : Mat(2, ℤ)) τ) hσ n hzero
  refine ⟨k * γ 1 1 + j * γ 0 1, k * γ 1 0 + j * γ 0 0, ?_⟩
  have hε := fltDenominator_ne_zero_of_im_ne_zero γ hτ.ne'
  calc
    z = fltDenominator (γ : Mat(2, ℤ)) τ *
        (z / fltDenominator (γ : Mat(2, ℤ)) τ) := by field_simp [hε]
    _ = fltDenominator (γ : Mat(2, ℤ)) τ *
        ((k : ℂ) + (j : ℂ) * flt (γ : Mat(2, ℤ)) τ) := by rw [hkj]
    _ = _ := fltDenominator_mul_intCast_add_intCast_mul γ τ hε k j

/-- The raw modular quotient of [RW26, Radchenko, Wheeler (2026), Section 1, equation (1),
`eq:phigam.def`] is analytic in `z` away from `ℤ + ℤτ`, the regular locus used in
[RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`]. -/
theorem analyticAt_faddeevModularUHP_of_not_mem_lattice
    (γ : SL(2, ℤ)) (m n : ℤ) (z τ : ℂ) (hτ : 0 < τ.im)
    (hz : ¬ IsPeriodLatticePoint τ z) :
    AnalyticAt ℂ (fun w => faddeevModularUHP γ m n w τ) z := by
  have hnum : Differentiable ℂ (fun w => qPochhammer (w + m * τ) τ) :=
    (qPochhammer_differentiable τ hτ).comp (by fun_prop)
  have hden : Differentiable ℂ (fun w => qPochhammer
      (w / fltDenominator (γ : Mat(2, ℤ)) τ + n * flt (γ : Mat(2, ℤ)) τ)
      (flt (γ : Mat(2, ℤ)) τ)) :=
    (qPochhammer_differentiable _ (flt_im_pos γ hτ)).comp (by fun_prop)
  change AnalyticAt ℂ (fun w => qPochhammer (w + m * τ) τ / qPochhammer
    (w / fltDenominator (γ : Mat(2, ℤ)) τ + n * flt (γ : Mat(2, ℤ)) τ)
      (flt (γ : Mat(2, ℤ)) τ)) z
  exact (hnum.analyticAt z).div (hden.analyticAt z)
    (qPochhammer_div_fltDenominator_add_int_mul_ne_zero γ n z τ hτ hz)

/-- The raw modular quotient of [RW26, Radchenko, Wheeler (2026), Section 1, equation (1),
`eq:phigam.def`] is nonzero away from `ℤ + ℤτ`: neither q-product factor vanishes there. -/
theorem faddeevModularUHP_ne_zero_of_not_mem_lattice
    (γ : SL(2, ℤ)) (m n : ℤ) (z τ : ℂ) (hτ : 0 < τ.im)
    (hz : ¬ IsPeriodLatticePoint τ z) : faddeevModularUHP γ m n z τ ≠ 0 := by
  apply div_ne_zero
  · intro hzero
    exact hz (isPeriodLatticePoint_of_qPochhammer_add_zero τ hτ m hzero)
  · exact qPochhammer_div_fltDenominator_add_int_mul_ne_zero γ n z τ hτ hz

/-- For `τ ∈ ℍ`, `Φ_{γ,m,n}(·;τ)` is meromorphic. This follows from the q-product quotient
defining `faddeevModularUHP` in [RW26, Radchenko, Wheeler (2026), Section 1, equation (1),
`eq:phigam.def`]. -/
theorem meromorphic_faddeevModularUHP (γ : SL(2, ℤ)) (m n : ℤ)
    (τ : ℂ) (hτ : 0 < τ.im) :
    Meromorphic (fun z => faddeevModularUHP γ m n z τ) := by
  let ε := fltDenominator (γ : Mat(2, ℤ)) τ
  let σ := flt (γ : Mat(2, ℤ)) τ
  have hqτ : Differentiable ℂ (fun z => qPochhammer (z + m * τ) τ) :=
    (qPochhammer_differentiable τ hτ).comp (by fun_prop)
  have hqσ : Differentiable ℂ (fun z =>
      qPochhammer (z / ε + n * σ) σ) :=
    (qPochhammer_differentiable σ (flt_im_pos γ hτ)).comp (by fun_prop)
  have hn : Meromorphic (fun z => qPochhammer (z + m * τ) τ) :=
    fun z => (hqτ.analyticAt z).meromorphicAt
  have hd : Meromorphic (fun z => qPochhammer (z / ε + n * σ) σ) :=
    fun z => (hqσ.analyticAt z).meromorphicAt
  change Meromorphic ((fun z : ℂ => qPochhammer (z + m * τ) τ) /
    (fun z : ℂ => qPochhammer (z / ε + n * σ) σ))
  exact hn.div hd

/-- The modular q-product is measurable as a totalized quotient, including at common zeros. -/
theorem measurable_faddeevModularUHP (γ : SL(2, ℤ)) (n k : ℤ) (τ : ℂ)
    (hτ : 0 < τ.im) : Measurable (fun z => faddeevModularUHP γ n k z τ) := by
  exact (meromorphic_faddeevModularUHP γ n k τ hτ).measurable

/-! ### Lattice coordinates of denominator zeros

The zeros are `ε(k-jσ) = (kc-ja)τ+(kd-jb)`. Adding the shift `mτ` gives the integer
row index `kc-ja+m`; the determinant identity also gives `cε(k-jσ)+mε = (kc-ja+m)ε+j`. -/

/-- The zero `ε(k-jσ)` of `ϖ(z/ε,σ)`, with `ε = j_γ(τ)` and `σ = γτ`: the possible poles
of the modular q-product in
[RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`]. -/
def faddeevModularUHPPole (γ : SL(2, ℤ)) (τ : ℂ) (k : ℤ) (j : ℕ) : ℂ :=
  fltDenominator (γ : Mat(2, ℤ)) τ * ((k : ℂ) - j * flt (γ : Mat(2, ℤ)) τ)

/-- The row index `N = kc-ja+m` of `ε(k-jσ)+mτ` in the period lattice. -/
def faddeevModularUHPIndex (γ : SL(2, ℤ)) (m k : ℤ) (j : ℕ) : ℤ :=
  k * γ 1 0 - (j : ℤ) * γ 0 0 + m

/-- Since `εσ = aτ + b` and `ε = cτ + d`, the pole `ε(k-jσ)` is the lattice point
`(kc-ja)τ + (kd-jb)`. -/
theorem faddeevModularUHPPole_eq (γ : SL(2, ℤ)) (τ : ℂ)
    (hε : fltDenominator (γ : Mat(2, ℤ)) τ ≠ 0) (k : ℤ) (j : ℕ) :
    faddeevModularUHPPole γ τ k j =
      ((k * γ 1 0 - (j : ℤ) * γ 0 0 : ℤ) : ℂ) * τ + ((k * γ 1 1 - (j : ℤ) * γ 0 1 : ℤ) : ℂ) := by
  unfold fltDenominator at hε
  unfold faddeevModularUHPPole fltDenominator flt
  push_cast
  field_simp [hε]
  ring

/-- The zeros of `ϖ(z/ε,σ)` are exactly the points `ε(k-jσ)`, by the zero set of `ϖ`. -/
theorem qPochhammer_div_fltDenominator_eq_zero_iff (γ : SL(2, ℤ)) (τ : ℂ) (hτ : 0 < τ.im)
    (z : ℂ) :
    qPochhammer (z / fltDenominator (γ : Mat(2, ℤ)) τ) (flt (γ : Mat(2, ℤ)) τ) = 0 ↔
      ∃ (k : ℤ) (j : ℕ), z = faddeevModularUHPPole γ τ k j := by
  have hε := fltDenominator_ne_zero_of_im_ne_zero γ (ne_of_gt hτ)
  rw [qPochhammer_eq_zero_iff _ _ (flt_im_pos γ hτ)]
  constructor
  · rintro ⟨j, k, h⟩
    refine ⟨k, j, ?_⟩
    unfold faddeevModularUHPPole
    apply (div_eq_iff hε).mp at h
    simpa [mul_comm] using h
  · rintro ⟨k, j, rfl⟩
    exact ⟨j, k, by simp [faddeevModularUHPPole, hε]⟩

/-- The pole coordinates satisfy `ε(k-jσ)+mτ = Nτ+(kd-jb)`, where
`N = kc-ja+m`; see [RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`]. -/
theorem faddeevModularUHPPole_add_index (γ : SL(2, ℤ)) (τ : ℂ)
    (hε : fltDenominator (γ : Mat(2, ℤ)) τ ≠ 0) (m k : ℤ) (j : ℕ) :
    faddeevModularUHPPole γ τ k j + (m : ℂ) * τ =
      (faddeevModularUHPIndex γ m k j : ℂ) * τ +
        ((k * γ 1 1 - (j : ℤ) * γ 0 1 : ℤ) : ℂ) := by
  rw [faddeevModularUHPPole_eq γ τ hε]
  unfold faddeevModularUHPIndex
  push_cast
  ring

/-- The pole and forward index satisfy `c ε(k-jσ)+mε = Nε+j`, by `ad-bc=1`. -/
theorem faddeevModularUHPPole_linear (γ : SL(2, ℤ)) (τ : ℂ)
    (hε : fltDenominator (γ : Mat(2, ℤ)) τ ≠ 0) (m k : ℤ) (j : ℕ) :
    ((γ 1 0 : ℤ) : ℂ) * faddeevModularUHPPole γ τ k j +
        fltDenominator (γ : Mat(2, ℤ)) τ * m =
      fltDenominator (γ : Mat(2, ℤ)) τ * (faddeevModularUHPIndex γ m k j : ℂ) + j := by
  have hdet : ((γ 0 0 : ℤ) : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 :=
    det_fin_two_cast_eq_one γ
  rw [faddeevModularUHPPole_eq γ τ hε]
  unfold faddeevModularUHPIndex fltDenominator
  push_cast
  linear_combination (j : ℂ) * hdet

/-- The pole `ε(k-jσ)` has real part `((N-m) Re ε + j)/c`, where `N = kc-ja+m`: the real part
of `faddeevModularUHPPole_linear`. -/
theorem re_faddeevModularUHPPole (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (τ : ℂ)
    (hε : fltDenominator (γ : Mat(2, ℤ)) τ ≠ 0) (m k : ℤ) (j : ℕ) :
    (faddeevModularUHPPole γ τ k j).re =
      (((faddeevModularUHPIndex γ m k j : ℝ) - m) *
          (fltDenominator (γ : Mat(2, ℤ)) τ).re + j) / (γ 1 0 : ℝ) := by
  have hlin := congrArg Complex.re (faddeevModularUHPPole_linear γ τ hε m k j)
  simp only [Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
    Complex.natCast_re, zero_mul, sub_zero, Complex.add_re] at hlin
  have hc' : (0 : ℝ) < (γ 1 0 : ℝ) := by exact_mod_cast hc
  apply (eq_div_iff hc'.ne').mpr
  nlinarith

/-- The map `(k,j) ↦ ε(k-jσ)` is injective for `τ ∈ ℍ`. -/
theorem faddeevModularUHPPole_injective (γ : SL(2, ℤ)) (τ : ℂ) (hτ : 0 < τ.im) :
    Function.Injective (fun kj : ℤ × ℕ => faddeevModularUHPPole γ τ kj.1 kj.2) := by
  rintro ⟨k, j⟩ ⟨k', j'⟩ h
  have hε := fltDenominator_ne_zero_of_im_ne_zero γ hτ.ne'
  have hσ := flt_im_pos γ hτ
  unfold faddeevModularUHPPole at h
  apply (mul_left_cancel₀ hε) at h
  have hcoord : (k : ℂ) + ((-(j : ℤ)) : ℂ) * flt (γ : Mat(2, ℤ)) τ =
      (k' : ℂ) + ((-(j' : ℤ)) : ℂ) * flt (γ : Mat(2, ℤ)) τ := by
    simpa only [Int.cast_neg, Int.cast_natCast, neg_mul, sub_eq_add_neg] using h
  obtain ⟨hk, hj⟩ :=
    (intCast_add_intCast_mul_eq_iff _ hσ.ne' k (-(j : ℤ)) k' (-(j' : ℤ))).mp
      (by simpa only [Int.cast_neg, Int.cast_natCast] using hcoord)
  have hj' : j = j' := by omega
  exact Prod.ext hk hj'

/-! ### Poles and zeros

A pole is a zero of the denominator at which the numerator does not vanish, and a zero is the
reverse. Both lie on the lattice `ℤ + ℤτ`; the fractional-linear lattice conversion places a
zero at height at least `Im σ` in the denominator's variable, while a pole lies at height at
least `Im τ` in the numerator's variable. Lattice membership also makes both genuine pole sets
closed. -/

/-- The poles of `Φ_{γ,n,0}(·;τ)` on `ℍ`: the zeros of `ϖ(z/ε,σ)` at which `ϖ(z+nτ,τ)` does not
vanish. [RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`] locates them at the lattice
points `ε(k - jσ)`. -/
def faddeevModularUHPPoles (γ : SL(2, ℤ)) (n : ℤ) (τ : ℂ) : Set ℂ :=
  {u | qPochhammer (u / fltDenominator (γ : Mat(2, ℤ)) τ) (flt (γ : Mat(2, ℤ)) τ) = 0 ∧
    qPochhammer (u + n * τ) τ ≠ 0}

/-- The zeros of `Φ_{γ,n,0}(·;τ)` on `ℍ`: the zeros of `ϖ(z+nτ,τ)` at which `ϖ(z/ε,σ)` does not
vanish. -/
def faddeevModularUHPZeros (γ : SL(2, ℤ)) (n : ℤ) (τ : ℂ) : Set ℂ :=
  {u | qPochhammer (u + n * τ) τ = 0 ∧
    qPochhammer (u / fltDenominator (γ : Mat(2, ℤ)) τ) (flt (γ : Mat(2, ℤ)) τ) ≠ 0}

/-- Every zero of `ϖ(z/ε,σ)` lies in `ℤ + ℤτ`. -/
theorem isPeriodLatticePoint_of_qPochhammer_div_eq_zero (γ : SL(2, ℤ))
    (τ : ℂ) (hτ : 0 < τ.im) {z : ℂ}
    (hz : qPochhammer (z / fltDenominator (γ : Mat(2, ℤ)) τ)
      (flt (γ : Mat(2, ℤ)) τ) = 0) : IsPeriodLatticePoint τ z := by
  obtain ⟨k, j, rfl⟩ := (qPochhammer_div_fltDenominator_eq_zero_iff γ τ hτ z).mp hz
  have hε := fltDenominator_ne_zero_of_im_ne_zero γ hτ.ne'
  rw [faddeevModularUHPPole_eq γ τ hε]
  exact ⟨k * γ 1 1 - (j : ℤ) * γ 0 1,
    k * γ 1 0 - (j : ℤ) * γ 0 0, by ring⟩

/-- Genuine poles of `Φ_{γ,n,0}` form a closed subset of the period lattice. -/
theorem isClosed_faddeevModularUHPPoles (γ : SL(2, ℤ)) (n : ℤ) (τ : ℂ)
    (hτ : 0 < τ.im) : IsClosed (faddeevModularUHPPoles γ n τ) := by
  apply (periodPair τ hτ.ne').isClosed_of_subset_lattice
  intro u hu
  exact (isPeriodLatticePoint_iff_mem_lattice τ hτ.ne' _).mp
    (isPeriodLatticePoint_of_qPochhammer_div_eq_zero γ τ hτ hu.1)

/-- Genuine zeros of `Φ_{γ,n,0}` form a closed subset of the period lattice. -/
theorem isClosed_faddeevModularUHPZeros (γ : SL(2, ℤ)) (n : ℤ) (τ : ℂ)
    (hτ : 0 < τ.im) : IsClosed (faddeevModularUHPZeros γ n τ) := by
  apply (periodPair τ hτ.ne').isClosed_of_subset_lattice
  intro u hu
  exact (isPeriodLatticePoint_iff_mem_lattice τ hτ.ne' _).mp
    (isPeriodLatticePoint_of_qPochhammer_add_zero τ hτ n hu.1)

/-- If a q-product is nonzero at `K + Nτ`, then the integer coefficient `N` is positive. -/
private lemma pos_coeff_of_qPochhammer_ne_zero (τ : ℂ) (K N : ℤ)
    (h : qPochhammer ((K : ℂ) + (N : ℂ) * τ) τ ≠ 0) : 0 < N := by
  by_contra hn
  have hN : N ≤ 0 := le_of_not_gt hn
  have hNj : N = -((Int.toNat (-N) : ℕ) : ℤ) := by omega
  have hNcast : (N : ℂ) = -((Int.toNat (-N) : ℕ) : ℂ) := by
    exact_mod_cast hNj
  have heq : (K : ℂ) + (N : ℂ) * τ =
      (K : ℂ) - (Int.toNat (-N) : ℕ) * τ := by rw [hNcast]; ring
  exact h (heq ▸ qPochhammer_intCast_sub_natCast_mul_eq_zero K
    (Int.toNat (-N)) τ)

/-- A numerator zero `u` has the row `k-(n+j)τ`; after division by `ε` its
coordinates are `K = ka+(n+j)b` and `N = -ck-(n+j)d`. -/
private lemma numerator_zero_lattice_coordinates (γ : SL(2, ℤ)) (n : ℤ)
    {τ u : ℂ} (hτ : 0 < τ.im) (hnum : qPochhammer (u + n * τ) τ = 0) :
    ∃ (k : ℤ) (j : ℕ),
      u = (k : ℂ) - (n + (j : ℤ) : ℤ) * τ ∧
      u / fltDenominator (γ : Mat(2, ℤ)) τ =
        ((k * γ 0 0 + (n + (j : ℤ)) * γ 0 1 : ℤ) : ℂ) +
        ((-(k * γ 1 0 + (n + (j : ℤ)) * γ 1 1) : ℤ) : ℂ) *
          flt (γ : Mat(2, ℤ)) τ := by
  obtain ⟨j, k, hrow⟩ := (qPochhammer_eq_zero_iff _ τ hτ).mp hnum
  have hε := fltDenominator_ne_zero_of_im_ne_zero γ (ne_of_gt hτ)
  let ε := fltDenominator (γ : Mat(2, ℤ)) τ
  let σ := flt (γ : Mat(2, ℤ)) τ
  let K : ℤ := k * γ 0 0 + (n + j) * γ 0 1
  let N : ℤ := -(k * γ 1 0 + (n + j) * γ 1 1)
  have hu' : u = (k : ℂ) - (n + (j : ℤ) : ℤ) * τ := by
    calc
      u = (k : ℂ) - j * τ - n * τ := by linear_combination hrow
      _ = (k : ℂ) - (n + (j : ℤ) : ℤ) * τ := by push_cast; ring
  refine ⟨k, j, hu', ?_⟩
  rw [hu']
  calc
    ((k : ℂ) - (n + (j : ℤ) : ℤ) * τ) / ε =
        ((k : ℂ) + (-(n + (j : ℤ)) : ℤ) * τ) / ε := by push_cast; ring
    _ = (K : ℂ) + (N : ℂ) * σ := by
      convert intCast_add_intCast_mul_div_fltDenominator γ τ hε k
        (-(n + (j : ℤ))) using 1
      all_goals dsimp [K, N, σ]
      all_goals ring_nf

/-- A genuine zero `u` of `Φ_{γ,n,0}` has `u=k-(n+j)τ` and a positive
backward row index `N=-ck-(n+j)d`; division by `ε` gives the row
`(ka+(n+j)b)+Nσ`. -/
theorem faddeevModularUHPZero_coordinates (γ : SL(2, ℤ)) (n : ℤ)
    {τ u : ℂ} (hτ : 0 < τ.im) (hu : u ∈ faddeevModularUHPZeros γ n τ) :
    ∃ (k : ℤ) (j : ℕ) (N : ℤ), 0 < N ∧
      u = (k : ℂ) - (n + (j : ℤ) : ℤ) * τ ∧
      N = -(k * γ 1 0 + (n + (j : ℤ)) * γ 1 1) ∧
      u / fltDenominator (γ : Mat(2, ℤ)) τ =
        ((k * γ 0 0 + (n + (j : ℤ)) * γ 0 1 : ℤ) : ℂ) +
        (N : ℂ) * flt (γ : Mat(2, ℤ)) τ := by
  obtain ⟨k, j, hrow, hcoord⟩ :=
    numerator_zero_lattice_coordinates γ n hτ hu.1
  let K : ℤ := k * γ 0 0 + (n + (j : ℤ)) * γ 0 1
  let N : ℤ := -(k * γ 1 0 + (n + (j : ℤ)) * γ 1 1)
  have hN : 0 < N := by
    apply pos_coeff_of_qPochhammer_ne_zero (flt (γ : Mat(2, ℤ)) τ) K N
    rw [← hcoord]
    exact hu.2
  exact ⟨k, j, N, hN, hrow, rfl, hcoord⟩

/-- At a genuine pole `ε(k-jσ)` of `Φ_{γ,n,0}`, the forward index
`N=kc-ja+n` is positive. -/
theorem faddeevModularUHPIndex_pos_of_mem_poles (γ : SL(2, ℤ)) (n k : ℤ)
    (j : ℕ) (τ : ℂ) (hτ : 0 < τ.im)
    (hu : faddeevModularUHPPole γ τ k j ∈ faddeevModularUHPPoles γ n τ) :
    0 < faddeevModularUHPIndex γ n k j := by
  have hε := fltDenominator_ne_zero_of_im_ne_zero γ (ne_of_gt hτ)
  let K : ℤ := k * γ 1 1 - (j : ℤ) * γ 0 1
  have hrow : faddeevModularUHPPole γ τ k j + n * τ =
      (faddeevModularUHPIndex γ n k j : ℂ) * τ + K := by
    simpa [K] using faddeevModularUHPPole_add_index γ τ hε n k j
  apply pos_coeff_of_qPochhammer_ne_zero τ K (faddeevModularUHPIndex γ n k j)
  have hnum := hu.2
  rw [hrow] at hnum
  simpa [add_comm] using hnum

/-- A pole `u` of `Φ_{γ,n,0}(·;τ)` has `Im(u + nτ) ≥ Im τ`. -/
theorem im_le_im_add_of_mem_faddeevModularUHPPoles (γ : SL(2, ℤ)) (n : ℤ) {τ u : ℂ}
    (hτ : 0 < τ.im) (hu : u ∈ faddeevModularUHPPoles γ n τ) :
    τ.im ≤ (u + n * τ).im := by
  obtain ⟨k, j, rfl⟩ :=
    (qPochhammer_div_fltDenominator_eq_zero_iff γ τ hτ u).mp hu.1
  have hε := fltDenominator_ne_zero_of_im_ne_zero γ (ne_of_gt hτ)
  have hN := faddeevModularUHPIndex_pos_of_mem_poles γ n k j τ hτ hu
  have hrow := faddeevModularUHPPole_add_index γ τ hε n k j
  have him : (faddeevModularUHPPole γ τ k j + n * τ).im =
      (faddeevModularUHPIndex γ n k j : ℝ) * τ.im := by rw [hrow]; simp
  have hNreal : (1 : ℝ) ≤ (faddeevModularUHPIndex γ n k j : ℝ) := by exact_mod_cast hN
  nlinarith

/-- A zero `u` of `Φ_{γ,n,0}(·;τ)` has `Im(u/ε) ≥ Im σ`. -/
theorem im_le_im_div_of_mem_faddeevModularUHPZeros (γ : SL(2, ℤ)) (n : ℤ) {τ u : ℂ}
    (hτ : 0 < τ.im) (hu : u ∈ faddeevModularUHPZeros γ n τ) :
    (flt (γ : Mat(2, ℤ)) τ).im ≤ (u / fltDenominator (γ : Mat(2, ℤ)) τ).im := by
  obtain ⟨k, j, N, hN, _, _, hrow'⟩ :=
    faddeevModularUHPZero_coordinates γ n hτ hu
  let ε := fltDenominator (γ : Mat(2, ℤ)) τ
  let σ := flt (γ : Mat(2, ℤ)) τ
  have hσ : 0 < σ.im := flt_im_pos γ hτ
  have him : (u / ε).im = (N : ℝ) * σ.im := by
    rw [hrow']
    simp [σ]
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  nlinarith

/-! ### Real bounds and pole indexing

A positive row index places the zeros to the left of `(-n Re ε-1)/c` when `c > 0` and
`Re ε ≥ 0`. The indexed pole description records exactly the uncancelled zeros. -/

/-- Genuine zeros of `Φ_{γ,n,0}` satisfy `Re u ≤ (-n Re ε-1)/c` when `c > 0` and
`Re ε ≥ 0`; see [RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`]. -/
theorem re_upperBound_of_mem_faddeevModularUHPZeros
    (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (n : ℤ) {τ u : ℂ}
    (hτ : 0 < τ.im) (he : 0 ≤ (fltDenominator (γ : Mat(2, ℤ)) τ).re)
    (hu : u ∈ faddeevModularUHPZeros γ n τ) :
    u.re ≤ (-(n : ℝ) * (fltDenominator (γ : Mat(2, ℤ)) τ).re - 1) / (γ 1 0 : ℝ) := by
  obtain ⟨k, j, N, hN, rfl, hNeq, _⟩ := faddeevModularUHPZero_coordinates γ n hτ hu
  have hlin : ((γ 1 0 : ℤ) : ℂ) * ((k : ℂ) - (n + (j : ℤ) : ℤ) * τ) =
      -((n + (j : ℤ) : ℤ) : ℂ) * fltDenominator (γ : Mat(2, ℤ)) τ - N := by
    rw [hNeq]
    unfold fltDenominator
    push_cast
    ring
  have hre := congrArg Complex.re hlin
  simp only [Int.cast_add, Int.cast_natCast, Complex.sub_re, Complex.intCast_re,
    Complex.mul_re, Complex.add_re, Complex.natCast_re, Complex.add_im,
    Complex.intCast_im, Complex.natCast_im, add_zero, zero_mul, sub_zero,
    neg_mul, Complex.neg_re] at hre
  have hc' : (0 : ℝ) < (γ 1 0 : ℝ) := by exact_mod_cast hc
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hcoeff : 0 ≤ (j : ℝ) * (fltDenominator (γ : Mat(2, ℤ)) τ).re :=
    mul_nonneg hj he
  apply (le_div_iff₀ hc').mpr
  have hreal : ((k : ℂ) - (n + (j : ℤ) : ℤ) * τ).re =
      (k : ℝ) - ((n : ℝ) + j) * τ.re := by simp [Complex.sub_re, Complex.mul_re]
  rw [hreal]
  nlinarith

/-- At `ε(k-jσ)`, the numerator `ϖ(z+(m+1)τ,τ)` is nonzero exactly when
`N = kc-ja+m ≥ 0`; the pole indexing in [RW26, Radchenko, Wheeler (2026), Appendix A.2,
`app:mod.fad`]. -/
theorem mem_faddeevModularUHPPoles_iff (γ : SL(2, ℤ)) (m : ℤ)
    {τ z : ℂ} (hτ : 0 < τ.im) :
    z ∈ faddeevModularUHPPoles γ (m + 1) τ ↔
      ∃ k : ℤ, ∃ j : ℕ, z = faddeevModularUHPPole γ τ k j ∧
        0 ≤ faddeevModularUHPIndex γ m k j := by
  constructor
  · intro hz
    obtain ⟨k, j, rfl⟩ :=
      (qPochhammer_div_fltDenominator_eq_zero_iff γ τ hτ z).mp hz.1
    refine ⟨k, j, rfl, ?_⟩
    have hN := faddeevModularUHPIndex_pos_of_mem_poles γ (m + 1) k j τ hτ hz
    dsimp [faddeevModularUHPIndex] at *
    omega
  · rintro ⟨k, j, rfl, hN⟩
    have hε := fltDenominator_ne_zero_of_im_ne_zero γ hτ.ne'
    have hindex : faddeevModularUHPIndex γ (m + 1) k j =
        faddeevModularUHPIndex γ m k j + 1 := by
      simp only [faddeevModularUHPIndex]
      ring
    have hrow : faddeevModularUHPPole γ τ k j + ((m + 1 : ℤ) : ℂ) * τ =
        ((faddeevModularUHPIndex γ m k j + 1 : ℤ) : ℂ) * τ +
          ((k * γ 1 1 - (j : ℤ) * γ 0 1 : ℤ) : ℂ) := by
      simpa only [hindex] using faddeevModularUHPPole_add_index γ τ hε (m + 1) k j
    refine ⟨(qPochhammer_div_fltDenominator_eq_zero_iff γ τ hτ _).mpr ⟨k, j, rfl⟩, ?_⟩
    intro hzero
    have hnonpos := im_nonpos_of_qPochhammer_eq_zero hτ hzero
    rw [hrow] at hnonpos
    simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
      zero_mul, add_zero] at hnonpos
    have hN' : (0 : ℝ) ≤ faddeevModularUHPIndex γ m k j := by exact_mod_cast hN
    push_cast at hnonpos
    have hpos : 0 < ((faddeevModularUHPIndex γ m k j : ℝ) + 1) * τ.im :=
      mul_pos (by linarith) hτ
    linarith

/-! ### Discrete denominator zeros

The denominator zeros lie in the period lattice, so they are finite in compact sets and
absent from a sufficiently small punctured neighborhood of any point. -/

/-- The zero set of `ϖ(z/ε,σ)` meets every compact set in finitely many points, by
`finite_periodLattice_inter_compact`. -/
theorem finite_qPochhammer_div_zeros_inter_compact (γ : SL(2, ℤ))
    (τ : ℂ) (hτ : 0 < τ.im) {K : Set ℂ} (hK : IsCompact K) :
    (K ∩ {z | qPochhammer (z / fltDenominator (γ : Mat(2, ℤ)) τ)
      (flt (γ : Mat(2, ℤ)) τ) = 0}).Finite := by
  apply (finite_periodLattice_inter_compact τ hτ.ne' hK).subset
  rintro z ⟨hzK, hz⟩
  exact ⟨hzK, isPeriodLatticePoint_of_qPochhammer_div_eq_zero γ τ hτ hz⟩

/-- Near any point, punctured neighborhoods avoid zeros of `ϖ(z/ε,σ)`, by
`eventually_not_isPeriodLatticePoint`. -/
theorem eventually_qPochhammer_div_fltDenominator_ne_zero (γ : SL(2, ℤ))
    (τ : ℂ) (hτ : 0 < τ.im) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z,
      qPochhammer (w / fltDenominator (γ : Mat(2, ℤ)) τ)
        (flt (γ : Mat(2, ℤ)) τ) ≠ 0 := by
  filter_upwards [eventually_not_isPeriodLatticePoint τ hτ.ne' z] with w hw hz
  exact hw (isPeriodLatticePoint_of_qPochhammer_div_eq_zero γ τ hτ hz)

/-! ### Removable origin

At fixed `τ ∈ ℍ`, both q-products vanish to first order at `z=0`. The modular denominator
has its derivative divided by `ε=cτ+d`; the ratio of slopes gives the punctured limit in `z`.
This does not assert a boundary limit as `τ` approaches the real axis. -/

/-- The derivative at the origin of the modular denominator in
`tendsto_faddeevModularUHP_zero`. -/
private lemma hasDerivAt_faddeevModularUHP_denominator_zero (γ : SL(2, ℤ))
    (τ : ℂ) (hτ : 0 < τ.im) :
    HasDerivAt (fun z : ℂ => qPochhammer (z / fltDenominator (γ : Mat(2, ℤ)) τ)
      (flt (γ : Mat(2, ℤ)) τ))
      ((-2 * π * I * qPochhammer (flt (γ : Mat(2, ℤ)) τ)
        (flt (γ : Mat(2, ℤ)) τ)) / fltDenominator (γ : Mat(2, ℤ)) τ) 0 := by
  let ε := fltDenominator (γ : Mat(2, ℤ)) τ
  let σ := flt (γ : Mat(2, ℤ)) τ
  have hσder : HasDerivAt (fun z : ℂ => qPochhammer z σ)
      (-2 * π * I * qPochhammer σ σ) (0 / ε) := by
    simpa using qPochhammer_hasDerivAt_zero σ (flt_im_pos γ hτ)
  simpa [Function.comp_def, div_eq_mul_inv, ε, σ] using
    hσder.comp 0 ((hasDerivAt_id (0 : ℂ)).div_const ε)

/-- The exact removable-origin value of the upper-half-plane modular q-product. The raw
q-product quotient is `0 / 0` at the origin; this definition names its punctured limit rather
than Lean's totalized value of that quotient. -/
noncomputable def faddeevModularUHPOriginValue (γ : SL(2, ℤ)) (τ : ℂ) : ℂ :=
  fltDenominator (γ : Mat(2, ℤ)) τ *
    (qPochhammer τ τ /
      qPochhammer (flt (γ : Mat(2, ℤ)) τ) (flt (γ : Mat(2, ℤ)) τ))

/-- At the common zero `z=0`, the punctured modular q-product tends to
`(cτ+d) ϖ(τ,τ)/ϖ(γτ,γτ)`. This is the exact scalar prefactor in
[RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`], obtained from
`qPochhammer_hasDerivAt_zero` in numerator and denominator. -/
theorem tendsto_faddeevModularUHP_zero (γ : SL(2, ℤ)) (τ : ℂ) (hτ : 0 < τ.im) :
    Tendsto (fun z : ℂ => faddeevModularUHP γ 0 0 z τ) (𝓝[≠] 0)
      (𝓝 (faddeevModularUHPOriginValue γ τ)) := by
  let ε := fltDenominator (γ : Mat(2, ℤ)) τ
  let σ := flt (γ : Mat(2, ℤ)) τ
  have hε : ε ≠ 0 := fltDenominator_ne_zero_of_im_ne_zero γ hτ.ne'
  have hσ : 0 < σ.im := flt_im_pos γ hτ
  have hfactor : (-2 * π * I : ℂ) ≠ 0 := by simp
  have htail : qPochhammer σ σ ≠ 0 := qPochhammer_tau_ne_zero σ hσ
  have hden : HasDerivAt (fun z : ℂ => qPochhammer (z / ε) σ)
      ((-2 * π * I * qPochhammer σ σ) / ε) 0 := by
    simpa [ε, σ] using hasDerivAt_faddeevModularUHP_denominator_zero γ τ hτ
  have hden_ne := div_ne_zero (mul_ne_zero hfactor htail) hε
  have hlim := (qPochhammer_hasDerivAt_zero τ hτ).tendsto_slope.div
    hden.tendsto_slope hden_ne
  have hlim' : Tendsto (fun z : ℂ => qPochhammer z τ / qPochhammer (z / ε) σ)
      (𝓝[≠] 0) (𝓝 ((-2 * π * I * qPochhammer τ τ) /
        ((-2 * π * I * qPochhammer σ σ) / ε))) := by
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz : z ≠ 0 := by simpa using hz
    change slope (fun w => qPochhammer w τ) 0 z /
      slope (fun w => qPochhammer (w / ε) σ) 0 z = _
    simp only [slope_def_field, zero_div, qPochhammer_zero, sub_zero,
      div_div_div_cancel_right₀ hz]
  convert hlim' using 1
  · ext z
    simp [faddeevModularUHP, ε, σ]
  · dsimp [faddeevModularUHPOriginValue, ε, σ]
    field_simp [hfactor, hε, htail]

end SIC
