/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.Faddeev.FiveTerm.Kernel
import SICs.SpecialFunctions.QPochhammer.ResidueSeries

/-!
# Residues of the five-term kernel

The residues of the five-term kernel and the absolute sum of their two-index series.

This module follows the residue calculation in [RW26, Radchenko, Wheeler (2026),
Appendix A.2, `app:mod.fad`], the proof of Theorem 3, `thm:5term.mod.fad`.

## The argument

At the denominator zero `ε(k-jσ)`, the kernel is a regular factor times a scaled
q-product quotient. Integer periodicity and `ad-bc=1` express the residue through
the forward index `N=kc-ja+m` and the backward index `j`.
As `0 ≤ m < c` and `k ∈ ℤ` vary, division with remainder makes `N` run through `ℤ`
exactly once. Thus the genuine pole indices correspond to `ℕ × ℕ`, and
`hasSum_qPochhammer_residue_series` evaluates their absolute sum under
`Im(ℓτ+w)>0` and `Im((w+y)/ε)>0`. This is the source's character-sum bookkeeping
in lattice coordinates. The q-product prefactor is retained, without eta normalization.
-/

noncomputable section

open Complex Real Filter Set MeasureTheory
open scoped Topology MatrixGroups

namespace SIC

/-! ### Residues at the indexed poles

The regular factor at `ε(k-jσ)` depends only on `N=kc-ja+m` and `j`. The scaled
q-product residue computes the coefficient. -/

/-- The residue of the five-term kernel at the pole with forward index `N` and backward
index `j`: `1/(-2πi)` times
`ε ϖ((N+1)τ,τ)/ϖ(pτ+y+Nτ,τ) · ϖ(y/ε-jσ,σ)/(ϖ_j(-jσ,σ) ϖ(σ,σ)) · e(N(ℓτ+w) + jw/ε)`,
the coefficient in the residue sum of
[RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`]. -/
def fiveTermResidueUHP (γ : SL(2, ℤ)) (ℓ p : ℤ) (w y τ : ℂ) (N : ℤ) (j : ℕ) : ℂ :=
  fltDenominator (γ : Mat(2, ℤ)) τ *
      (qPochhammer (((N : ℂ) + 1) * τ) τ / qPochhammer ((p : ℂ) * τ + y + N * τ) τ) *
      (qPochhammer (y / fltDenominator (γ : Mat(2, ℤ)) τ - j * flt (γ : Mat(2, ℤ)) τ)
          (flt (γ : Mat(2, ℤ)) τ) /
        (qPochhammerFin (j : ℤ) (-(j : ℂ) * flt (γ : Mat(2, ℤ)) τ) (flt (γ : Mat(2, ℤ)) τ) *
          qPochhammer (flt (γ : Mat(2, ℤ)) τ) (flt (γ : Mat(2, ℤ)) τ))) *
      Complex.exp (2 * π * I *
        ((N : ℂ) * ((ℓ : ℂ) * τ + w) + (j : ℂ) * (w / fltDenominator (γ : Mat(2, ℤ)) τ))) /
    (-2 * π * I)

/-- Integer periodicity identifies the shifted denominator value at `ε(k-jσ)` with
`ϖ(pτ+y+Nτ,τ)`, where `N = kc-ja+m`. -/
private lemma fiveTermPole_qPochhammer_denominator (γ : SL(2, ℤ)) (p m k : ℤ)
    (y τ : ℂ) (j : ℕ) (hε : fltDenominator (γ : Mat(2, ℤ)) τ ≠ 0) :
    qPochhammer (faddeevModularUHPPole γ τ k j + y + ((m : ℂ) + p) * τ) τ =
      qPochhammer ((p : ℂ) * τ + y + (faddeevModularUHPIndex γ m k j : ℂ) * τ) τ := by
  have hs := faddeevModularUHPPole_add_index γ τ hε m k j
  calc
    _ = qPochhammer (((p : ℂ) * τ + y +
        (faddeevModularUHPIndex γ m k j : ℂ) * τ) +
        ((k * γ 1 1 - (j : ℤ) * γ 0 1 : ℤ) : ℂ)) τ := by
          congr 1; linear_combination hs
    _ = _ := qPochhammer_add_intCast _ τ _

/-- The numerator q-product value at a pole, used by
`fiveTerm_regular_residue_value`. -/
private lemma fiveTermPole_qPochhammer_numerator (γ : SL(2, ℤ)) (m k : ℤ)
    (τ : ℂ) (j : ℕ) (hε : fltDenominator (γ : Mat(2, ℤ)) τ ≠ 0) :
    qPochhammer (faddeevModularUHPPole γ τ k j + ((m : ℂ) + 1) * τ) τ =
      qPochhammer (((faddeevModularUHPIndex γ m k j : ℂ) + 1) * τ) τ := by
  convert fiveTermPole_qPochhammer_denominator γ 1 m k 0 τ j hε using 1 <;> ring_nf

/-- The exponential at a pole is the forward and backward index exponential;
`tendsto_fiveTermKernelUHP_residue` uses this periodicity. -/
private lemma fiveTermPole_exp (γ : SL(2, ℤ)) (ℓ m k : ℤ)
    (w τ : ℂ) (j : ℕ) (hε : fltDenominator (γ : Mat(2, ℤ)) τ ≠ 0) :
    Complex.exp (2 * π * I *
      (((((γ 1 0 : ℤ) : ℂ) * faddeevModularUHPPole γ τ k j +
          fltDenominator (γ : Mat(2, ℤ)) τ * m) * w /
          fltDenominator (γ : Mat(2, ℤ)) τ) +
        ℓ * (faddeevModularUHPPole γ τ k j + m * τ))) =
      Complex.exp (2 * π * I *
        ((faddeevModularUHPIndex γ m k j : ℂ) * ((ℓ : ℂ) * τ + w) +
          (j : ℂ) * (w / fltDenominator (γ : Mat(2, ℤ)) τ))) := by
  apply exp_two_pi_I_eq_of_sub_intCast _ _
    (ℓ * (k * γ 1 1 - (j : ℤ) * γ 0 1))
  rw [faddeevModularUHPPole_linear γ τ hε m k j,
    faddeevModularUHPPole_add_index γ τ hε m k j]
  field_simp [hε]
  push_cast
  ring

/-- The regular factor of the expanded kernel is continuous at a pole with
nonvanishing left-hand denominator, as used by
`tendsto_fiveTermKernelUHP_residue`. -/
private lemma fiveTerm_regular_continuous (γ : SL(2, ℤ)) (ℓ p m k : ℤ)
    (w y τ : ℂ) (j : ℕ) (hτ : 0 < τ.im)
    (hden : qPochhammer ((p : ℂ) * τ + y +
      (faddeevModularUHPIndex γ m k j : ℂ) * τ) τ ≠ 0) :
    ContinuousAt (fun z =>
      qPochhammer (z + ((m : ℂ) + 1) * τ) τ /
        qPochhammer (z + y + ((m : ℂ) + p) * τ) τ *
        Complex.exp (2 * π * I *
          ((((γ 1 0 : ℤ) : ℂ) * z + fltDenominator (γ : Mat(2, ℤ)) τ * m) * w /
              fltDenominator (γ : Mat(2, ℤ)) τ + ℓ * (z + m * τ))))
      (faddeevModularUHPPole γ τ k j) := by
  have hε := fltDenominator_ne_zero_of_im_ne_zero γ (ne_of_gt hτ)
  have hden' := fiveTermPole_qPochhammer_denominator γ p m k y τ j hε
  have hn : ContinuousAt (fun z => qPochhammer (z + ((m : ℂ) + 1) * τ) τ)
      (faddeevModularUHPPole γ τ k j) :=
    (qPochhammer_continuous τ hτ).continuousAt.comp (by fun_prop)
  have hd : ContinuousAt (fun z => qPochhammer (z + y + ((m : ℂ) + p) * τ) τ)
      (faddeevModularUHPPole γ τ k j) :=
    (qPochhammer_continuous τ hτ).continuousAt.comp (by fun_prop)
  have he : ContinuousAt (fun z => Complex.exp (2 * π * I *
      ((((γ 1 0 : ℤ) : ℂ) * z + fltDenominator (γ : Mat(2, ℤ)) τ * m) * w /
          fltDenominator (γ : Mat(2, ℤ)) τ + ℓ * (z + m * τ))))
      (faddeevModularUHPPole γ τ k j) := by fun_prop
  exact (hn.div hd (hden' ▸ hden)).mul he

/-- The regular value times the scaled q-product residue equals the indexed
coefficient in `tendsto_fiveTermKernelUHP_residue`. -/
private lemma fiveTerm_regular_residue_value (γ : SL(2, ℤ)) (ℓ p m k : ℤ)
    (w y τ : ℂ) (j : ℕ) (hτ : 0 < τ.im) :
    (qPochhammer (faddeevModularUHPPole γ τ k j + ((m : ℂ) + 1) * τ) τ /
        qPochhammer (faddeevModularUHPPole γ τ k j + y + ((m : ℂ) + p) * τ) τ *
        Complex.exp (2 * π * I *
          ((((γ 1 0 : ℤ) : ℂ) * faddeevModularUHPPole γ τ k j +
              fltDenominator (γ : Mat(2, ℤ)) τ * m) * w /
              fltDenominator (γ : Mat(2, ℤ)) τ +
            ℓ * (faddeevModularUHPPole γ τ k j + m * τ)))) *
      fltDenominator (γ : Mat(2, ℤ)) τ *
      (qPochhammer (y / fltDenominator (γ : Mat(2, ℤ)) τ)
          (flt (γ : Mat(2, ℤ)) τ) /
          (-2 * π * I * qPochhammer (flt (γ : Mat(2, ℤ)) τ)
            (flt (γ : Mat(2, ℤ)) τ)) *
        (qPochhammerFin (j : ℤ)
            (y / fltDenominator (γ : Mat(2, ℤ)) τ -
              (j : ℂ) * flt (γ : Mat(2, ℤ)) τ) (flt (γ : Mat(2, ℤ)) τ) /
          qPochhammerFin (j : ℤ) (-(j : ℂ) * flt (γ : Mat(2, ℤ)) τ)
            (flt (γ : Mat(2, ℤ)) τ))) =
      fiveTermResidueUHP γ ℓ p w y τ (faddeevModularUHPIndex γ m k j) j := by
  have hε := fltDenominator_ne_zero_of_im_ne_zero γ (ne_of_gt hτ)
  have hnum := fiveTermPole_qPochhammer_numerator γ m k τ j hε
  have hden := fiveTermPole_qPochhammer_denominator γ p m k y τ j hε
  rw [hnum, hden, fiveTermPole_exp γ ℓ m k w τ j hε]
  have hfin := qPochhammerFin_natCast_mul_qPochhammer_add j
    (y / fltDenominator (γ : Mat(2, ℤ)) τ -
      (j : ℂ) * flt (γ : Mat(2, ℤ)) τ) (flt (γ : Mat(2, ℤ)) τ)
    (flt_im_pos γ hτ)
  have harg : y / fltDenominator (γ : Mat(2, ℤ)) τ -
      (j : ℂ) * flt (γ : Mat(2, ℤ)) τ +
      (j : ℂ) * flt (γ : Mat(2, ℤ)) τ =
      y / fltDenominator (γ : Mat(2, ℤ)) τ := by ring
  rw [harg] at hfin
  unfold fiveTermResidueUHP
  rw [← hfin]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The residue of the `m`-th five-term kernel at `ε(k-jσ)` is the coefficient
`fiveTermResidueUHP` at the forward index `kc - ja + m`, when `ϖ` is nonzero at
`pτ+y+(kc-ja+m)τ`. This is the residue evaluation in the proof of
[RW26, Radchenko, Wheeler (2026), Theorem 3, `thm:5term.mod.fad`, Appendix A.2,
`app:mod.fad`], in the coordinates `(k, j)` of the zero of `ϖ(·,σ)`. -/
theorem tendsto_fiveTermKernelUHP_residue (γ : SL(2, ℤ)) (ℓ p : ℤ) (w y τ : ℂ)
    (hτ : 0 < τ.im) (m k : ℤ) (j : ℕ)
    (hden : qPochhammer ((p : ℂ) * τ + y + (faddeevModularUHPIndex γ m k j : ℂ) * τ) τ ≠ 0) :
    Tendsto (fun z => (z - faddeevModularUHPPole γ τ k j) *
      fiveTermKernelUHP γ ℓ p w y τ m z)
      (𝓝[≠] (faddeevModularUHPPole γ τ k j))
      (𝓝 (fiveTermResidueUHP γ ℓ p w y τ (faddeevModularUHPIndex γ m k j) j)) := by
  let g : ℂ → ℂ := fun z =>
    qPochhammer (z + ((m : ℂ) + 1) * τ) τ /
      qPochhammer (z + y + ((m : ℂ) + p) * τ) τ *
      Complex.exp (2 * π * I *
        ((((γ 1 0 : ℤ) : ℂ) * z + fltDenominator (γ : Mat(2, ℤ)) τ * m) * w /
          fltDenominator (γ : Mat(2, ℤ)) τ + ℓ * (z + m * τ)))
  have hε := fltDenominator_ne_zero_of_im_ne_zero γ (ne_of_gt hτ)
  have hg : ContinuousAt g (faddeevModularUHPPole γ τ k j) :=
    fiveTerm_regular_continuous γ ℓ p m k w y τ j hτ hden
  have hres := tendsto_mul_qPochhammer_quotient_residue_div g y
    (flt (γ : Mat(2, ℤ)) τ) (fltDenominator (γ : Mat(2, ℤ)) τ)
    (flt_im_pos γ hτ) hε j k hg
  convert hres using 1
  · ext z
    rw [fiveTermKernelUHP_eq]
    rfl
  · rfl
  · congr 1
    exact (fiveTerm_regular_residue_value γ ℓ p m k w y τ j hτ).symm

/-! ### The residue sum

The genuine poles of the kernels with `0 ≤ m < c` are indexed by `ℕ × ℕ`. The residue
coefficients are those of the two-index q-binomial series, which is summed in
`SICs.SpecialFunctions.QPochhammer.ResidueSeries`.
-/

/-- The genuine poles of the `m`-th kernel among the zeros `ε(k-jσ)`: those with
nonnegative forward index `kc - ja + m`. -/
def fiveTermPoles (γ : SL(2, ℤ)) (m : ℤ) : Set (ℤ × ℕ) :=
  {kj | 0 ≤ faddeevModularUHPIndex γ m kj.1 kj.2}

/-- Division with remainder recovers the forward index in `fiveTermPoleEquiv`. -/
private lemma fiveTermIndex_division (γ : SL(2, ℤ)) (hc : 0 < γ 1 0)
    (N j : ℕ) :
    faddeevModularUHPIndex γ
      (((((N : ℤ) + (j : ℤ) * γ 0 0) % γ 1 0).toNat : ℕ) : ℤ)
      (((N : ℤ) + (j : ℤ) * γ 0 0) / γ 1 0) j = N := by
  have hrem : 0 ≤ ((N : ℤ) + (j : ℤ) * γ 0 0) % γ 1 0 :=
    Int.emod_nonneg _ (ne_of_gt hc)
  have hdiv := Int.emod_add_mul_ediv ((N : ℤ) + (j : ℤ) * γ 0 0) (γ 1 0)
  dsimp [faddeevModularUHPIndex]
  rw [Int.toNat_of_nonneg hrem]
  linear_combination hdiv

/-- The quotient and remainder of an existing pole recover its data in
`fiveTermPoleEquiv`. -/
private lemma fiveTermIndex_inverse (γ : SL(2, ℤ)) (hc : 0 < γ 1 0)
    (m : Fin (γ 1 0).toNat) (k : ℤ) (j : ℕ)
    (hN : 0 ≤ faddeevModularUHPIndex γ ((m : ℕ) : ℤ) k j) :
    (((faddeevModularUHPIndex γ ((m : ℕ) : ℤ) k j).toNat : ℤ) +
      (j : ℤ) * γ 0 0) / γ 1 0 = k ∧
    (((faddeevModularUHPIndex γ ((m : ℕ) : ℤ) k j).toNat : ℤ) +
      (j : ℤ) * γ 0 0) % γ 1 0 = m := by
  apply (Int.ediv_emod_unique hc).2
  refine ⟨?_, by exact_mod_cast Nat.zero_le m.val, ?_⟩
  · rw [Int.toNat_of_nonneg hN]
    dsimp [faddeevModularUHPIndex]
    ring
  · have hcNat : ((γ 1 0).toNat : ℤ) = γ 1 0 :=
      Int.toNat_of_nonneg (le_of_lt hc)
    have hmLt : ((m : ℕ) : ℤ) < ((γ 1 0).toNat : ℤ) := by
      exact_mod_cast m.isLt
    exact lt_of_lt_of_eq hmLt hcNat

/-- The poles of the kernels with representatives `0 ≤ m < c` correspond to `ℕ × ℕ` by
`(m, k, j) ↦ (kc-ja+m, j)`; for fixed `j`, dividing `N + ja` by `c` with remainder
recovers `k` and `m`. This is the congruence bookkeeping of
[RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`]. -/
def fiveTermPoleEquiv (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) :
    (Σ m : Fin (γ 1 0).toNat, fiveTermPoles γ ((m : ℕ) : ℤ)) ≃ ℕ × ℕ where
  toFun x := ((faddeevModularUHPIndex γ ((x.1 : ℕ) : ℤ) x.2.1.1 x.2.1.2).toNat, x.2.1.2)
  invFun Nj :=
    ⟨⟨((Nj.1 + (Nj.2 : ℤ) * γ 0 0) % γ 1 0).toNat, by
        exact (Int.toNat_lt_toNat hc).2 (Int.emod_lt_of_pos _ hc)⟩,
      ⟨((Nj.1 + (Nj.2 : ℤ) * γ 0 0) / γ 1 0, Nj.2), by
        change 0 ≤ faddeevModularUHPIndex γ
          (((((Nj.1 : ℤ) + (Nj.2 : ℤ) * γ 0 0) % γ 1 0).toNat : ℕ) : ℤ)
          (((Nj.1 : ℤ) + (Nj.2 : ℤ) * γ 0 0) / γ 1 0) Nj.2
        rw [fiveTermIndex_division γ hc]
        exact_mod_cast Nat.zero_le Nj.1⟩⟩
  left_inv := by
    intro x
    rcases x with ⟨m, ⟨⟨k, j⟩, hN⟩⟩
    obtain ⟨hk, hm⟩ := fiveTermIndex_inverse γ hc m k j hN
    apply Sigma.subtype_ext
    · apply Fin.ext
      simpa only [Int.toNat_natCast] using congrArg Int.toNat hm
    · simp only [hk]
  right_inv := by
    intro Nj
    rcases Nj with ⟨N, j⟩
    simp only [fiveTermIndex_division γ hc, Int.toNat_natCast]

/-- The residue coefficients of the five-term kernels over `(N, j) ∈ ℕ × ℕ` sum absolutely
to `ε ϖ(τ,τ)/ϖ(σ,σ) · Φ_{γ,p+ℓ,0}(w+y;τ)/(Φ_{γ,p,0}(y;τ) Φ_{γ,ℓ,1}(w;τ))` divided by `-2πi`,
for `Im(ℓτ+w) > 0`, `Im((y+w)/ε) > 0`, and `ϖ(pτ+y,τ) ≠ 0`. This is the residue sum of
[RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`] at `n = h = 0`, with its
exact q-product prefactor; it is `hasSum_qPochhammer_residue_series` at `a = pτ+y`,
`b = y/ε`, `u = ℓτ+w`, `v = w/ε`. -/
theorem hasSum_fiveTermResidueUHP (γ : SL(2, ℤ)) (ℓ p : ℤ) (w y τ : ℂ)
    (hτ : 0 < τ.im) (hu : 0 < ((ℓ : ℂ) * τ + w).im)
    (hv : 0 < ((y + w) / fltDenominator (γ : Mat(2, ℤ)) τ).im)
    (ha : qPochhammer ((p : ℂ) * τ + y) τ ≠ 0) :
    HasSum (fun Nj : ℕ × ℕ => fiveTermResidueUHP γ ℓ p w y τ Nj.1 Nj.2)
      (fltDenominator (γ : Mat(2, ℤ)) τ *
          (qPochhammer τ τ / qPochhammer (flt (γ : Mat(2, ℤ)) τ) (flt (γ : Mat(2, ℤ)) τ)) *
          (faddeevModularUHP γ (p + ℓ) 0 (w + y) τ /
            (faddeevModularUHP γ p 0 y τ * faddeevModularUHP γ ℓ 1 w τ)) /
        (-2 * π * I)) := by
  have hσ := flt_im_pos γ hτ
  have hbv : 0 < (y / fltDenominator (γ : Mat(2, ℤ)) τ +
      w / fltDenominator (γ : Mat(2, ℤ)) τ).im := by
    simpa only [add_div] using hv
  have hs := (hasSum_qPochhammer_residue_series
    ((p : ℂ) * τ + y) (y / fltDenominator (γ : Mat(2, ℤ)) τ)
    ((ℓ : ℂ) * τ + w) (w / fltDenominator (γ : Mat(2, ℤ)) τ)
    τ (flt (γ : Mat(2, ℤ)) τ) (fltDenominator (γ : Mat(2, ℤ)) τ)
    hτ hσ hu hbv ha).div_const (-2 * π * I)
  convert hs using 1
  · funext Nj
    simp only [fiveTermResidueUHP, Int.cast_natCast]
  · unfold faddeevModularUHP
    simp only [Int.cast_zero, zero_mul, add_zero, Int.cast_add, Int.cast_one, one_mul]
    have hA : w + y + ((p : ℂ) + (ℓ : ℂ)) * τ =
        (p : ℂ) * τ + y + ((ℓ : ℂ) * τ + w) := by ring
    have hB : y + (p : ℂ) * τ = (p : ℂ) * τ + y := by ring
    have hC : w + (ℓ : ℂ) * τ = (ℓ : ℂ) * τ + w := by ring
    have hD : (w + y) / fltDenominator (γ : Mat(2, ℤ)) τ =
        y / fltDenominator (γ : Mat(2, ℤ)) τ +
          w / fltDenominator (γ : Mat(2, ℤ)) τ := by ring
    rw [hA, hB, hC, hD]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring_nf

/-- The residues of the kernels `K_m`, `0 ≤ m < c`, at their genuine poles `ε(k-jσ)` sum
absolutely to `ε ϖ(τ,τ)/ϖ(σ,σ) · Φ_{γ,p+ℓ,0}(w+y;τ)/(Φ_{γ,p,0}(y;τ) Φ_{γ,ℓ,1}(w;τ))`
divided by `-2πi`. Each summand is the residue computed by
`tendsto_fiveTermKernelUHP_residue`. This is the residue sum in the proof of
[RW26, Radchenko, Wheeler (2026), Theorem 3, `thm:5term.mod.fad`, Appendix A.2,
`app:mod.fad`] at `n = h = 0`, after the congruence classes have been summed. -/
theorem hasSum_fiveTermResidueUHP_poles (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (ℓ p : ℤ)
    (w y τ : ℂ) (hτ : 0 < τ.im) (hu : 0 < ((ℓ : ℂ) * τ + w).im)
    (hv : 0 < ((y + w) / fltDenominator (γ : Mat(2, ℤ)) τ).im)
    (ha : qPochhammer ((p : ℂ) * τ + y) τ ≠ 0) :
    HasSum (fun x : Σ m : Fin (γ 1 0).toNat, fiveTermPoles γ ((m : ℕ) : ℤ) =>
        fiveTermResidueUHP γ ℓ p w y τ
          (faddeevModularUHPIndex γ ((x.1 : ℕ) : ℤ) x.2.1.1 x.2.1.2) x.2.1.2)
      (fltDenominator (γ : Mat(2, ℤ)) τ *
          (qPochhammer τ τ / qPochhammer (flt (γ : Mat(2, ℤ)) τ) (flt (γ : Mat(2, ℤ)) τ)) *
          (faddeevModularUHP γ (p + ℓ) 0 (w + y) τ /
            (faddeevModularUHP γ p 0 y τ * faddeevModularUHP γ ℓ 1 w τ)) /
        (-2 * π * I)) := by
  have hs := (fiveTermPoleEquiv γ hc).hasSum_iff.mpr
    (hasSum_fiveTermResidueUHP γ ℓ p w y τ hτ hu hv ha)
  convert hs using 1
  funext x
  have hN : 0 ≤ faddeevModularUHPIndex γ ((x.1 : ℕ) : ℤ) x.2.1.1 x.2.1.2 := x.2.2
  change fiveTermResidueUHP γ ℓ p w y τ
      (faddeevModularUHPIndex γ ((x.1 : ℕ) : ℤ) x.2.1.1 x.2.1.2) x.2.1.2 =
    fiveTermResidueUHP γ ℓ p w y τ
      (((faddeevModularUHPIndex γ ((x.1 : ℕ) : ℤ) x.2.1.1 x.2.1.2).toNat : ℕ) : ℤ) x.2.1.2
  rw [Int.toNat_of_nonneg hN]

/-! ### Finite residue sums

When finitely many right poles lie to the left of the contours, their residues correct the
contour identity. Each residue depends on `w` only through an exponential of an affine
function, so a finite sum of them is entire in `w`. -/

/-- The residues of the kernels `K_m`, `0 ≤ m < c`, at the right poles with indices in the
finite sets `F m`: the correction to the contour identity of
[RW26, Radchenko, Wheeler (2026), Theorem 3, `thm:5term.mod.fad`, Appendix A.2, `app:mod.fad`]
when those poles lie to the left of their contours. -/
def fiveTermResidueSumUHP (γ : SL(2, ℤ)) (ℓ p : ℤ) (w y τ : ℂ)
    (F : FiveTermIndex γ → Finset (ℤ × ℕ)) : ℂ :=
  ∑ m : FiveTermIndex γ, ∑ kj ∈ F m,
    fiveTermResidueUHP γ ℓ p w y τ
      (faddeevModularUHPIndex γ ((m : ℕ) : ℤ) kj.1 kj.2) kj.2

/-- A finite sum of five-term residues is entire in the exponential parameter `w`. -/
theorem differentiable_fiveTermResidueSumUHP (γ : SL(2, ℤ)) (ℓ p : ℤ) (y τ : ℂ)
    (F : FiveTermIndex γ → Finset (ℤ × ℕ)) :
    Differentiable ℂ (fun w => fiveTermResidueSumUHP γ ℓ p w y τ F) := by
  unfold fiveTermResidueSumUHP
  apply Differentiable.fun_sum
  intro m _
  apply Differentiable.fun_sum
  intro kj _
  unfold fiveTermResidueUHP
  fun_prop

end SIC
