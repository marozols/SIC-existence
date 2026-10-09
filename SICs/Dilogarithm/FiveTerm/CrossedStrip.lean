/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Dilogarithm.FiveTerm.Strip
import SICs.SpecialFunctions.Faddeev.FiveTerm.CrossedPoles

/-!
# Cancellation of crossed poles in the residue strip of a letter word

The residue strip of a letter word with positive source representatives cancels the crossed-pole
square corrections and supplies the finite sum with its zero-class value `F⁺(0)`.

This module follows [RW26, Radchenko, Wheeler (2026), Section 3.2, the proof of Theorem 2,
`thm:fg.equs`], using the deformations of `D_m(y)` in Figure 1 in straight-line form, for
`γ = ∏_j T^{b_j}S = (a b; c d)` at an attractive fixed point `τ`. Write `ε = j_γ(τ)`,
`δ = (ε-1)/c`, and `S(m,k) = (1-d)m + ck`. The principal word is treated directly in
`SICs.Principal.Dilogarithm.Faddeev.FiveTerm.CrossedStrip`.

## The argument

Choose `0 ≤ S(u) < N`, `1 ≤ S(v) ≤ N`, and a common line just right of
`β_v = -(v₁ε/c+z_v) = (ε-1)S(v)/(cN)`. Since `z_{(m,k)} + mε/c = -(ε-1)S(m,k)/(cN)`, the kernel
poles in its strip have indices `-N-S(v) ≤ S(x) < -S(v)`, one representative of each finite
class (`sum_fiveTermWindow`). The exact divisor of the word product also puts numerator poles of
the residue sum `L` at `δ+j/c` for positive integers `j` with `j/c < β_v`. The poles crossed by
the difference kernel `J` lie at `j/c`, including `j=0`.

The germ identity `J(z)=L(z)-L(z+δ)` pairs the positive-index corrections with these product
poles. At zero it leaves `Res L(0)-Res L(δ)`. The negative-index window has numerator type `F⁻`;
this difference replaces only the zero-class numerator by `F⁺(0)`. The denominator type
throughout the window is `F⁻`. The rectangle residue theorem, the exponential tail bounds of the
residue kernel, and the window bijection then leave `ε/(ε-1)` times the finite five-term sum.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology MatrixGroups

namespace SIC

/-! ### Strip geometry and the crossed-pole window

The translated kernel poles are spaced by `(ε-1)/(cN)`. Positive representatives of the
right source pair put the crossing coordinate `β_v` between zero and the strip width. -/

/-- The crossing coordinate `β_v` is the pole spacing times `S(v)`; used by
`integral_fiveTermWordResidueSum_of_crossed`. -/
private lemma wordCrossed_beta_eq_spacing_index {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (v₁ v₂ : ℤ) :
    -((v₁ : ℝ) * fltDenominator (γ : Mat(2, ℤ)) τ / (γ 1 0 : ℝ) +
      fiveTermLatticeArgument γ τ v₁ v₂) =
      (fltDenominator (γ : Mat(2, ℤ)) τ - 1) /
        ((γ 1 0 : ℝ) * (finiteDilogOrder γ : ℝ)) *
          (fiveTermLatticeIndex γ v₁ v₂ : ℝ) := by
  rw [fiveTermLatticeArgument_beta_eq h]
  ring

/-- The common kernel-pole spacing is positive; used by the crossed-strip window. -/
private lemma wordCrossed_spacing_pos {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) :
    0 < (fltDenominator (γ : Mat(2, ℤ)) τ - 1) /
      ((γ 1 0 : ℝ) * (finiteDilogOrder γ : ℝ)) := by
  apply div_pos
  · exact sub_pos.mpr h.one_lt_fltDenominator
  · exact mul_pos (by exact_mod_cast h.lowerLeft_pos)
      (by exact_mod_cast finiteDilogOrder_pos h)

/-- The residue strip has width `N` times the pole spacing; used by the crossed-strip
window. -/
private lemma wordCrossed_width_eq_spacing_mul_order {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) :
    (fltDenominator (γ : Mat(2, ℤ)) τ - 1) / (γ 1 0 : ℝ) =
      (fltDenominator (γ : Mat(2, ℤ)) τ - 1) /
        ((γ 1 0 : ℝ) * (finiteDilogOrder γ : ℝ)) *
          (finiteDilogOrder γ : ℝ) := by
  have hc : (γ 1 0 : ℝ) ≠ 0 := by exact_mod_cast h.lowerLeft_pos.ne'
  have hN : (finiteDilogOrder γ : ℝ) ≠ 0 := by
    exact_mod_cast (finiteDilogOrder_pos h).ne'
  field_simp

/-- For `1 ≤ S(v) ≤ N`, the crossing coordinate lies in `(0,(ε-1)/c]`; used by
`integral_fiveTermWordResidueSum_of_crossed`. -/
private lemma wordCrossed_beta_bounds {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (v₁ v₂ : ℤ)
    (hv : 1 ≤ fiveTermLatticeIndex γ v₁ v₂ ∧
      fiveTermLatticeIndex γ v₁ v₂ ≤ finiteDilogOrder γ) :
    0 < -((v₁ : ℝ) * fltDenominator (γ : Mat(2, ℤ)) τ / (γ 1 0 : ℝ) +
        fiveTermLatticeArgument γ τ v₁ v₂) ∧
      -((v₁ : ℝ) * fltDenominator (γ : Mat(2, ℤ)) τ / (γ 1 0 : ℝ) +
        fiveTermLatticeArgument γ τ v₁ v₂) ≤
        (fltDenominator (γ : Mat(2, ℤ)) τ - 1) / (γ 1 0 : ℝ) := by
  rw [wordCrossed_beta_eq_spacing_index h]
  have hs : (0 : ℝ) < (fiveTermLatticeIndex γ v₁ v₂ : ℝ) := by
    exact_mod_cast hv.1
  have hle : (fiveTermLatticeIndex γ v₁ v₂ : ℝ) ≤
      (finiteDilogOrder γ : ℝ) := by exact_mod_cast hv.2
  exact ⟨mul_pos (wordCrossed_spacing_pos h) hs,
    (wordCrossed_width_eq_spacing_mul_order h).symm ▸
      mul_le_mul_of_nonneg_left hle (wordCrossed_spacing_pos h).le⟩

/-- A lattice-spaced pole in the closed crossed strip still lies in the open index window;
used to exclude kernel poles outside the finite pole set. -/
private lemma wordCrossed_closed_window_arithmetic (a x : ℝ) (N V S : ℤ)
    (ha : 0 < a) (hx₁ : a * (V : ℝ) < x)
    (hx₂ : x < a * ((V : ℝ) + 1))
    (hlo : x ≤ -a * (S : ℝ))
    (hhi : -a * (S : ℝ) ≤ x + a * (N : ℝ)) :
    -N - V ≤ S ∧ S < -V := by
  constructor
  · by_contra hn
    have hS : S ≤ -N - V - 1 := by omega
    have hSR : (S : ℝ) ≤ -(N : ℝ) - V - 1 := by exact_mod_cast hS
    nlinarith [mul_nonneg ha.le
      (show (0 : ℝ) ≤ -(N : ℝ) - V - 1 - S by linarith)]
  · by_contra hn
    have hS : -V ≤ S := by omega
    have hSR : -(V : ℝ) ≤ S := by exact_mod_cast hS
    nlinarith [mul_nonneg ha.le
      (show (0 : ℝ) ≤ (S : ℝ) + V by linarith)]

/-- Integer indices between `-N-S(v)` and `-S(v)` give exactly the kernel poles inside
the open crossed strip; used by `wordCrossed_kernel_mem_window_iff_mem_strip`. -/
private lemma wordCrossed_window_arithmetic (a x : ℝ) (N V S : ℤ)
    (ha : 0 < a) (hx₁ : a * (V : ℝ) < x)
    (hx₂ : x < a * ((V : ℝ) + 1)) :
    (-N - V ≤ S ∧ S < -V) ↔
      x < -a * (S : ℝ) ∧ -a * (S : ℝ) < x + a * (N : ℝ) := by
  constructor
  · rintro ⟨hlo, hhi⟩
    have hhiR : (S : ℝ) ≤ -(V : ℝ) - 1 := by
      exact_mod_cast (show S ≤ -V - 1 by omega)
    have hloR : -(N : ℝ) - V ≤ S := by exact_mod_cast hlo
    constructor
    · nlinarith [mul_nonneg ha.le
        (show (0 : ℝ) ≤ -(V : ℝ) - 1 - S by linarith)]
    · nlinarith [mul_nonneg ha.le
        (show (0 : ℝ) ≤ (S : ℝ) + N + V by linarith)]
  · rintro ⟨hlo, hhi⟩
    exact wordCrossed_closed_window_arithmetic a x N V S ha hx₁ hx₂ hlo.le hhi.le

/-- A translated kernel pole in the closed strip belongs to the crossed source window. -/
private lemma wordCrossed_kernel_mem_window_of_closed_strip {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (v₁ v₂ m k : ℤ) (x : ℝ)
    (hx₁ : -((v₁ : ℝ) * fltDenominator (γ : Mat(2, ℤ)) τ / (γ 1 0 : ℝ) +
      fiveTermLatticeArgument γ τ v₁ v₂) < x)
    (hx₂ : x < -((v₁ : ℝ) * fltDenominator (γ : Mat(2, ℤ)) τ / (γ 1 0 : ℝ) +
      fiveTermLatticeArgument γ τ v₁ v₂) +
      (fltDenominator (γ : Mat(2, ℤ)) τ - 1) /
        ((γ 1 0 : ℝ) * (finiteDilogOrder γ : ℝ)))
    (hm : 0 ≤ m ∧ m < γ 1 0)
    (hlo : x ≤ (fiveTermStripPolePosition γ τ m k).re)
    (hhi : (fiveTermStripPolePosition γ τ m k).re ≤
      x + (fltDenominator (γ : Mat(2, ℤ)) τ - 1) / (γ 1 0 : ℝ)) :
    (m, k) ∈ fiveTermWindow γ
      (-(finiteDilogOrder γ : ℤ) - fiveTermLatticeIndex γ v₁ v₂) := by
  let a : ℝ := (fltDenominator (γ : Mat(2, ℤ)) τ - 1) /
    ((γ 1 0 : ℝ) * (finiteDilogOrder γ : ℝ))
  have ha : 0 < a := wordCrossed_spacing_pos h
  have hβ := wordCrossed_beta_eq_spacing_index h v₁ v₂
  have hwidth := wordCrossed_width_eq_spacing_mul_order h
  have hpos := fiveTermLatticeArgument_add_mul_eq h m k
  have hpos' : (fiveTermStripPolePosition γ τ m k).re =
      -a * (fiveTermLatticeIndex γ m k : ℝ) := by
    simp only [fiveTermStripPolePosition, Complex.ofReal_re]
    dsimp [a]
    linear_combination hpos
  have hx₁' : a * (fiveTermLatticeIndex γ v₁ v₂ : ℝ) < x := by
    rwa [← hβ]
  have hx₂' : x < a * ((fiveTermLatticeIndex γ v₁ v₂ : ℝ) + 1) := by
    rw [hβ] at hx₂
    convert hx₂ using 1
    ring
  have hw := wordCrossed_closed_window_arithmetic a x
    (finiteDilogOrder γ) (fiveTermLatticeIndex γ v₁ v₂)
    (fiveTermLatticeIndex γ m k) ha hx₁' hx₂'
    (by rw [← hpos']; exact hlo)
    (by
      rw [← hpos']
      calc
        _ ≤ x + (fltDenominator (γ : Mat(2, ℤ)) τ - 1) / (γ 1 0 : ℝ) := hhi
        _ = x + a * (finiteDilogOrder γ : ℝ) := by rw [hwidth])
  apply (mem_fiveTermWindow h _ (m, k)).2
  refine ⟨hm.1, hm.2, hw.1, ?_⟩
  change fiveTermLatticeIndex γ m k <
    -(finiteDilogOrder γ : ℤ) - fiveTermLatticeIndex γ v₁ v₂ +
      (finiteDilogOrder γ : ℤ)
  omega

/-- A translated kernel pole is inside the open crossed strip exactly when its source pair
lies in the negative-index window. -/
private lemma wordCrossed_kernel_mem_window_iff_mem_strip {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (v₁ v₂ m k : ℤ) (x : ℝ)
    (hx₁ : -((v₁ : ℝ) * fltDenominator (γ : Mat(2, ℤ)) τ / (γ 1 0 : ℝ) +
      fiveTermLatticeArgument γ τ v₁ v₂) < x)
    (hx₂ : x < -((v₁ : ℝ) * fltDenominator (γ : Mat(2, ℤ)) τ / (γ 1 0 : ℝ) +
      fiveTermLatticeArgument γ τ v₁ v₂) +
      (fltDenominator (γ : Mat(2, ℤ)) τ - 1) /
        ((γ 1 0 : ℝ) * (finiteDilogOrder γ : ℝ)))
    (hm : 0 ≤ m ∧ m < γ 1 0) :
    (m, k) ∈ fiveTermWindow γ
      (-(finiteDilogOrder γ : ℤ) - fiveTermLatticeIndex γ v₁ v₂) ↔
      x < fiveTermLatticeArgument γ τ m k +
          (m : ℝ) * fltDenominator (γ : Mat(2, ℤ)) τ / (γ 1 0 : ℝ) ∧
        fiveTermLatticeArgument γ τ m k +
            (m : ℝ) * fltDenominator (γ : Mat(2, ℤ)) τ / (γ 1 0 : ℝ) <
          x + (fltDenominator (γ : Mat(2, ℤ)) τ - 1) / (γ 1 0 : ℝ) := by
  let a : ℝ := (fltDenominator (γ : Mat(2, ℤ)) τ - 1) /
    ((γ 1 0 : ℝ) * (finiteDilogOrder γ : ℝ))
  have ha : 0 < a := wordCrossed_spacing_pos h
  have hβ := wordCrossed_beta_eq_spacing_index h v₁ v₂
  have hwidth := wordCrossed_width_eq_spacing_mul_order h
  have hpos := fiveTermLatticeArgument_add_mul_eq h m k
  have hpos' : fiveTermLatticeArgument γ τ m k +
      (m : ℝ) * fltDenominator (γ : Mat(2, ℤ)) τ / (γ 1 0 : ℝ) =
      -a * (fiveTermLatticeIndex γ m k : ℝ) := by
    dsimp [a]
    linear_combination hpos
  have hx₁' : a * (fiveTermLatticeIndex γ v₁ v₂ : ℝ) < x := by
    rwa [← hβ]
  have hx₂' : x < a * ((fiveTermLatticeIndex γ v₁ v₂ : ℝ) + 1) := by
    rw [hβ] at hx₂
    convert hx₂ using 1
    ring
  rw [mem_fiveTermWindow h _ (m, k), hpos', hwidth]
  convert wordCrossed_window_arithmetic a x (finiteDilogOrder γ)
    (fiveTermLatticeIndex γ v₁ v₂) (fiveTermLatticeIndex γ m k) ha hx₁' hx₂' using 1
  all_goals simp only [hm.1, hm.2, true_and]
  all_goals ring_nf

/-! ### Product poles and residue rates

The word-product divisor places every numerator pole below the right strip boundary on the
first pole row. Its common-line position is `δ+j/c` for a positive integer `j`. -/

/-- A numerator pole below `(2ε-1)/c` has first pole index `1` and position
`δ+j/c`, where `j = 1-dk+cl ≥ 1`; used by the crossed-strip divisor argument. -/
private lemma wordCrossed_numerator_pole_arithmetic {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (m k l : ℤ)
    (hK : 0 < k + m)
    (hQ : γ 1 1 * k - γ 1 0 * l ≤ 0)
    (hz : (k : ℝ) * τ + l +
      (m : ℝ) * fltDenominator (γ : Mat(2, ℤ)) τ / (γ 1 0 : ℝ) <
      (2 * fltDenominator (γ : Mat(2, ℤ)) τ - 1) / (γ 1 0 : ℝ)) :
    k + m = 1 ∧
      1 ≤ 1 - γ 1 1 * k + γ 1 0 * l ∧
      (k : ℝ) * τ + l +
        (m : ℝ) * fltDenominator (γ : Mat(2, ℤ)) τ / (γ 1 0 : ℝ) =
        (fltDenominator (γ : Mat(2, ℤ)) τ - 1) / (γ 1 0 : ℝ) +
          ((1 - γ 1 1 * k + γ 1 0 * l : ℤ) : ℝ) / (γ 1 0 : ℝ) := by
  let ε : ℝ := fltDenominator (γ : Mat(2, ℤ)) τ
  let c : ℝ := γ 1 0
  let K : ℤ := k + m
  let J : ℤ := 1 - γ 1 1 * k + γ 1 0 * l
  have hc : 0 < c := by
    dsimp [c]
    exact_mod_cast h.lowerLeft_pos
  have hε : 0 < ε := h.fltDenominator_pos
  have hJ : 1 ≤ J := by dsimp [J]; omega
  have heq : (k : ℝ) * τ + l + (m : ℝ) * ε / c =
      ((K : ℝ) * ε + (J : ℝ) - 1) / c := by
    have hlin : c * τ = ε - (γ 1 1 : ℝ) := by
      dsimp [ε, c, fltDenominator]
      ring
    apply (eq_div_iff hc.ne').2
    calc
      ((k : ℝ) * τ + l + (m : ℝ) * ε / c) * c =
          (k : ℝ) * (c * τ) + (l : ℝ) * c + (m : ℝ) * ε := by
            field_simp [hc.ne']
      _ = ((K : ℝ) * ε + (J : ℝ) - 1) := by
        rw [hlin]
        dsimp [K, J, c]
        push_cast
        ring
  have hKle : K ≤ 1 := by
    by_contra hn
    have hKtwo : 2 ≤ K := by omega
    have hKtwoR : (2 : ℝ) ≤ K := by exact_mod_cast hKtwo
    have hJR : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    have hmult : 2 * ε ≤ (K : ℝ) * ε :=
      mul_le_mul_of_nonneg_right hKtwoR hε.le
    have hz' := hz
    change (k : ℝ) * τ + l + (m : ℝ) * ε / c < (2 * ε - 1) / c at hz'
    rw [heq] at hz'
    have hz'' := (div_lt_div_iff_of_pos_right hc).mp hz'
    linarith
  have hKone : K = 1 := by omega
  refine ⟨hKone, hJ, ?_⟩
  rw [heq, hKone]
  dsimp [ε, c, J]
  ring

/-! ### The two finite pole sets

The crossed rectangle contains kernel poles indexed by the negative window and numerator
product poles at `δ+j/c`. Irrationality of `ε=cτ+d` keeps the two families apart. -/

/-- The kernel-pole positions selected by the crossed source window. -/
private def wordCrossedKernelPoleSet (γ : SL(2, ℤ)) (τ : ℝ)
    (v₁ v₂ : ℤ) : Finset ℂ :=
  (fiveTermWindow γ (-(finiteDilogOrder γ : ℤ) - fiveTermLatticeIndex γ v₁ v₂)).image
    (fun mk => fiveTermStripPolePosition γ τ mk.1 mk.2)

/-- The positive numerator product-pole positions selected by the crossing indices. -/
private def wordCrossedProductPoleSet (γ : SL(2, ℤ)) (τ : ℝ)
    (F : Finset ℤ) : Finset ℂ :=
  (F.filter (0 < ·)).image (fun (j : ℤ) =>
    (((fltDenominator (γ : Mat(2, ℤ)) τ - 1) / (γ 1 0 : ℝ) +
      (j : ℝ) / (γ 1 0 : ℝ)) : ℂ))

/-- Positive rational grid points `j/c` are not kernel-pole positions. -/
private lemma wordCrossed_kernel_position_ne_rational {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (m k j : ℤ) (hj : 0 < j) :
    fiveTermStripPolePosition γ τ m k ≠ ((j : ℝ) / (γ 1 0 : ℝ) : ℂ) := by
  intro heq
  have hpos := fiveTermLatticeArgument_add_mul_eq h m k
  have hreal := congrArg Complex.re heq
  have hc : (0 : ℝ) < (γ 1 0 : ℝ) := by exact_mod_cast h.lowerLeft_pos
  have hN : (0 : ℝ) < (finiteDilogOrder γ : ℝ) := by
    exact_mod_cast finiteDilogOrder_pos h
  have hlin : (fltDenominator (γ : Mat(2, ℤ)) τ - 1) *
      (fiveTermLatticeIndex γ m k : ℝ) =
      -(j : ℝ) * (finiteDilogOrder γ : ℝ) := by
    simp only [fiveTermStripPolePosition, Complex.ofReal_re] at hreal
    norm_cast at hreal
    rw [Rat.cast_divInt] at hreal
    rw [hreal] at hpos
    field_simp [hc.ne', hN.ne'] at hpos ⊢
    nlinarith
  have hS : fiveTermLatticeIndex γ m k ≠ 0 := by
    intro hzero
    rw [hzero] at hlin
    have hjR : (0 : ℝ) < j := by exact_mod_cast hj
    have hzero' : (j : ℝ) * (finiteDilogOrder γ : ℝ) = 0 := by
      simpa using hlin.symm
    exact (mul_ne_zero hjR.ne' hN.ne') hzero'
  have hεirr : Irrational (fltDenominator (γ : Mat(2, ℤ)) τ) := by
    change Irrational ((γ 1 0 : ℝ) * τ + γ 1 1)
    exact (h.irrational.intCast_mul h.lowerLeft_pos.ne').add_intCast _
  have hprod : Irrational ((fiveTermLatticeIndex γ m k : ℝ) *
      fltDenominator (γ : Mat(2, ℤ)) τ) := hεirr.intCast_mul hS
  have heqInt : (fiveTermLatticeIndex γ m k : ℝ) *
      fltDenominator (γ : Mat(2, ℤ)) τ =
      ((fiveTermLatticeIndex γ m k - j * (finiteDilogOrder γ : ℤ) : ℤ) : ℝ) := by
    push_cast
    linarith [hlin]
  exact hprod.ne_int _ heqInt

/-- Adding the first row of `γ-I` moves a kernel pole left by one strip width. -/
private lemma wordCrossed_kernel_position_sub_width {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (m k : ℤ) :
    fiveTermStripPolePosition γ τ (m + γ 0 0 - 1) (k + γ 0 1) =
      fiveTermStripPolePosition γ τ m k -
        (((fltDenominator (γ : Mat(2, ℤ)) τ - 1) / (γ 1 0 : ℝ)) : ℂ) := by
  have hS : fiveTermLatticeIndex γ (m + γ 0 0 - 1) (k + γ 0 1) =
      fiveTermLatticeIndex γ m k + finiteDilogOrder γ := by
    convert fiveTermLatticeIndex_add γ m k (γ 0 0 - 1) (γ 0 1) using 1
    · ring_nf
    · rw [fiveTermLatticeIndex_firstRow h]
  have hpos1 := fiveTermLatticeArgument_add_mul_eq h
    (m + γ 0 0 - 1) (k + γ 0 1)
  have hpos2 := fiveTermLatticeArgument_add_mul_eq h m k
  dsimp [fiveTermStripPolePosition]
  norm_cast
  rw [hS] at hpos1
  rw [hpos1, hpos2]
  rw [wordCrossed_width_eq_spacing_mul_order h]
  push_cast
  ring

/-- Kernel poles and positive numerator product poles have distinct positions. -/
private lemma wordCrossed_kernel_product_positions_disjoint {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (m k j : ℤ) (hj : 0 < j) :
    fiveTermStripPolePosition γ τ m k ≠
      (((fltDenominator (γ : Mat(2, ℤ)) τ - 1) / (γ 1 0 : ℝ) +
        (j : ℝ) / (γ 1 0 : ℝ)) : ℂ) := by
  intro heq
  have hshift := wordCrossed_kernel_position_sub_width h m k
  rw [heq] at hshift
  have hrational : fiveTermStripPolePosition γ τ
      (m + γ 0 0 - 1) (k + γ 0 1) =
      (((j : ℝ) / (γ 1 0 : ℝ)) : ℂ) := by
    convert hshift using 1
    push_cast
    ring
  exact wordCrossed_kernel_position_ne_rational h _ _ j hj hrational

/-- Distinct positive grid indices give distinct numerator product-pole positions. -/
private lemma wordCrossed_product_position_injective {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) :
    Function.Injective (fun (j : ℤ) =>
      (((fltDenominator (γ : Mat(2, ℤ)) τ - 1) / (γ 1 0 : ℝ) +
        (j : ℝ) / (γ 1 0 : ℝ)) : ℂ)) := by
  intro j k hjk
  have hreal : (fltDenominator (γ : Mat(2, ℤ)) τ - 1) / (γ 1 0 : ℝ) +
      (j : ℝ) / (γ 1 0 : ℝ) =
      (fltDenominator (γ : Mat(2, ℤ)) τ - 1) / (γ 1 0 : ℝ) +
      (k : ℝ) / (γ 1 0 : ℝ) := by
    dsimp at hjk
    exact_mod_cast hjk
  have hc : (γ 1 0 : ℝ) ≠ 0 := by exact_mod_cast h.lowerLeft_pos.ne'
  have hcast : (j : ℝ) = k := by
    apply (div_left_inj' hc).mp
    linarith
  exact_mod_cast hcast

/-- A raw numerator pole in the crossed strip has position `δ+j/c` for a positive integer
`j`; used by the regularity argument. -/
private lemma wordCrossed_raw_numerator_pole_location {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (m : ℤ) (ζ : ℂ) (x : ℝ)
    (hx : x < fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
      (letterWord bs 1 0 : ℝ))
    (hz : ζ.re ≤ x + (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
      (letterWord bs 1 0 : ℝ))
    (hord : meromorphicOrderAt (fun z => faddeevWord bs m 0 z τ)
      (ζ - (m : ℂ) * fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
        (letterWord bs 1 0 : ℂ)) < 0) :
    ∃ j : ℤ, 1 ≤ j ∧
      ζ = (((fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
        (letterWord bs 1 0 : ℝ) + (j : ℝ) / (letterWord bs 1 0 : ℝ)) : ℂ) ∧
      (j : ℝ) / (letterWord bs 1 0 : ℝ) ≤ x := by
  let z : ℂ := ζ - (m : ℂ) *
    fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) / (letterWord bs 1 0 : ℂ)
  have hlat : IsPeriodLatticePoint (τ : ℂ) z := by
    by_contra hn
    have ho := meromorphicOrderAt_faddeevWord_eq_zero bs m 0 h.periodsPos.slitPlane hn
    change meromorphicOrderAt (fun z => faddeevWord bs m 0 z τ) z < 0 at hord
    rw [ho] at hord
    exact (not_lt.mpr le_rfl) hord
  rcases hlat with ⟨l, k, hk⟩
  have horder : meromorphicOrderAt (fun z => faddeevWord bs m 0 z τ)
      ((k : ℂ) * (τ : ℂ) + l) < 0 := by
    change meromorphicOrderAt (fun z => faddeevWord bs m 0 z τ) z < 0 at hord
    rw [hk] at hord
    simpa only [add_comm] using hord
  obtain ⟨hK, hQ⟩ :=
    (meromorphicOrderAt_faddeevWord_neg_iff bs h.ne_nil m 0 k l
      h.fixedPoint.irrational (fun w hw => (h.periodsPos w hw).2)).1 horder
  have hζ : ζ = ((k : ℝ) * τ + l +
      (m : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
        (letterWord bs 1 0 : ℝ) : ℂ) := by
    have hz' : ζ = ((l : ℂ) + (k : ℂ) * (τ : ℂ)) +
        (m : ℂ) * fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
          (letterWord bs 1 0 : ℂ) := by
      dsimp [z] at hk
      linear_combination hk
    rw [hz']
    push_cast
    ring
  have hzreal : ζ.re = (k : ℝ) * τ + l +
      (m : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
        (letterWord bs 1 0 : ℝ) := by
    rw [hζ]
    norm_cast
  have hupper : (k : ℝ) * τ + l +
      (m : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
        (letterWord bs 1 0 : ℝ) <
      (2 * fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
        (letterWord bs 1 0 : ℝ) := by
    rw [hzreal] at hz
    have hsum : fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
        (letterWord bs 1 0 : ℝ) +
        (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
          (letterWord bs 1 0 : ℝ) =
        (2 * fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
          (letterWord bs 1 0 : ℝ) := by ring
    linarith
  obtain ⟨_, hjpos, heq⟩ := wordCrossed_numerator_pole_arithmetic h.fixedPoint
    m k l hK (by simpa only [add_zero] using hQ) hupper
  let j : ℤ := 1 - letterWord bs 1 1 * k + letterWord bs 1 0 * l
  refine ⟨j, hjpos, ?_, ?_⟩
  · rw [hζ]
    exact_mod_cast heq
  · have hζr : ζ.re = (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
        (letterWord bs 1 0 : ℝ) + (j : ℝ) / (letterWord bs 1 0 : ℝ) := by
      rw [hzreal]
      exact heq
    rw [hζr] at hz
    linarith

/-- At a nonnegative rational grid point, the shifted denominator has nonpositive order;
used to compute the crossed-square residues. -/
private lemma wordCrossed_denominator_order_nonpos_at_rational {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (m v₁ v₂ j : ℤ) (hj : 0 ≤ j)
    (hv : 1 ≤ fiveTermLatticeIndex (letterWord bs) v₁ v₂) :
    meromorphicOrderAt
      (fun z : ℂ => faddeevWord bs (m + v₁) 0
        (z + fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ)
      ((j : ℂ) / (letterWord bs 1 0 : ℂ) -
        (m : ℂ) * fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
          (letterWord bs 1 0 : ℂ)) ≤ 0 := by
  let γ := letterWord bs
  let V := fiveTermLatticeIndex γ v₁ v₂
  let c : ℤ := γ 1 0
  let N := finiteDilogOrder γ
  let y := fiveTermLatticeArgument γ τ v₁ v₂
  let ε := fltDenominator (γ : Mat(2, ℤ)) τ
  let Z : ℂ := (j : ℂ) / (c : ℂ) - (m : ℂ) * (ε : ℂ) / (c : ℂ) + (y : ℂ)
  have hεcast : (ε : ℂ) = fltDenominator (γ : Mat(2, ℤ)) (τ : ℂ) := by
    simp [ε]
  rw [← hεcast]
  change meromorphicOrderAt
    ((fun z : ℂ => faddeevWord bs (m + v₁) 0 z τ) ∘ (· + (y : ℂ)))
      ((j : ℂ) / (c : ℂ) - (m : ℂ) * (ε : ℂ) / (c : ℂ)) ≤ 0
  rw [meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]
  change meromorphicOrderAt (fun z : ℂ => faddeevWord bs (m + v₁) 0 z τ) Z ≤ 0
  by_cases hlat : IsPeriodLatticePoint (τ : ℂ) Z
  · rcases hlat with ⟨l, k, hk⟩
    by_contra hn
    have hpos : 0 < meromorphicOrderAt (fun z : ℂ => faddeevWord bs (m + v₁) 0 z τ)
        ((k : ℂ) * (τ : ℂ) + l) := by
      change ¬ meromorphicOrderAt (fun z : ℂ => faddeevWord bs (m + v₁) 0 z τ) Z ≤ 0 at hn
      rw [hk] at hn
      simpa only [add_comm, not_le] using hn
    obtain ⟨hK, hQ⟩ :=
      (meromorphicOrderAt_faddeevWord_pos_iff bs h.ne_nil (m + v₁) 0 k l
        h.fixedPoint.irrational (fun w hw => (h.periodsPos w hw).2)).1 hpos
    have hc : 0 < c := h.fixedPoint.lowerLeft_pos
    have hN : 0 < (N : ℤ) := by exact_mod_cast finiteDilogOrder_pos h.fixedPoint
    have hV : 0 < V := by dsimp [V, γ]; omega
    have hε : ε = (c : ℝ) * τ + 1 - (1 - γ 1 1 : ℤ) := by
      dsimp [ε, c, fltDenominator]
      push_cast
      ring
    have hy : y = -((v₁ : ℝ) * ε / c) -
        (ε - 1) * V / ((c : ℝ) * (N : ℝ)) := by
      have hp := fiveTermLatticeArgument_add_mul_eq h.fixedPoint v₁ v₂
      dsimp [y, ε, c, N, V]
      linear_combination hp
    have harg : (j : ℝ) / c - ((m + v₁ : ℤ) : ℝ) * ε / c -
        (ε - 1) * V / ((c : ℝ) * (N : ℝ)) = (k : ℝ) * τ + l := by
      have hkre := congrArg Complex.re hk
      dsimp [Z] at hkre
      norm_cast at hkre
      rw [Rat.cast_divInt] at hkre
      rw [hy] at hkre
      dsimp [c, ε, N, V] at hkre ⊢
      push_cast at hkre ⊢
      convert hkre using 1 <;> ring
    have hQneg := faddeevCrossedDenominatorIndex_neg τ ε
      (1 - γ 1 1) c N V m v₁ j k l h.fixedPoint.irrational hc hN hV hj hε harg
    have hQneg' : γ 1 1 * k - γ 1 0 * l < 0 := by
      convert hQneg using 1
      ring
    dsimp [γ] at hQneg'
    omega
  · rw [meromorphicOrderAt_faddeevWord_eq_zero
      bs (m + v₁) 0 h.periodsPos.slitPlane hlat]

/-- Throughout the crossed strip the shifted denominator has nonpositive order. -/
private lemma wordCrossed_denominator_order_nonpos_on_strip {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (m v₁ v₂ : ℤ) (x : ℝ)
    (hx : -((v₁ : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
        (letterWord bs 1 0 : ℝ) +
      fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) < x)
    (z : ℂ) (hz : x ≤ z.re) :
    meromorphicOrderAt
      (fun ζ : ℂ => faddeevWord bs (m + v₁) 0
        (ζ + fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ)
      (z - (m : ℂ) * fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
        (letterWord bs 1 0 : ℂ)) ≤ 0 := by
  apply meromorphicOrderAt_faddeevWord_denominator_nonpos h m v₁
    (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂)
  have hreal :
      (z - (m : ℂ) * fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
        (letterWord bs 1 0 : ℂ)).re =
      z.re - (m : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
        (letterWord bs 1 0 : ℝ) := by norm_cast
  rw [hreal]
  have hsum : -((m + v₁ : ℤ) : ℝ) *
      fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
        (letterWord bs 1 0 : ℝ) -
        fiveTermLatticeArgument (letterWord bs) τ v₁ v₂ =
      -((v₁ : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
        (letterWord bs 1 0 : ℝ) +
          fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) -
        (m : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
          (letterWord bs 1 0 : ℝ) := by
    push_cast
    ring
  rw [hsum]
  linarith

/-- A point outside the kernel-pole set is not a kernel pole of any shifted summand in the
closed strip. -/
private lemma wordCrossed_no_kernel_pole_outside_set {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (v₁ v₂ : ℤ) (x : ℝ)
    (hx₁ : -((v₁ : ℝ) * fltDenominator (γ : Mat(2, ℤ)) τ / (γ 1 0 : ℝ) +
      fiveTermLatticeArgument γ τ v₁ v₂) < x)
    (hx₂ : x < -((v₁ : ℝ) * fltDenominator (γ : Mat(2, ℤ)) τ / (γ 1 0 : ℝ) +
      fiveTermLatticeArgument γ τ v₁ v₂) +
      (fltDenominator (γ : Mat(2, ℤ)) τ - 1) /
        ((γ 1 0 : ℝ) * (finiteDilogOrder γ : ℝ)))
    (z : ℂ) (hz₁ : x ≤ z.re)
    (hz₂ : z.re ≤ x + (fltDenominator (γ : Mat(2, ℤ)) τ - 1) / (γ 1 0 : ℝ))
    (hnot : z ∉ wordCrossedKernelPoleSet γ τ v₁ v₂)
    (m : FiveTermIndex γ) (k : ℤ) :
    z ≠ fiveTermStripPolePosition γ τ ((m : ℕ) : ℤ) k := by
  intro heq
  have hm := fiveTermIndex_range h m
  have hmem := wordCrossed_kernel_mem_window_of_closed_strip h v₁ v₂
    ((m : ℕ) : ℤ) k x hx₁ hx₂ hm
    (by rw [← heq]; exact hz₁) (by rw [← heq]; exact hz₂)
  apply hnot
  exact Finset.mem_image.mpr ⟨(((m : ℕ) : ℤ), k), hmem, heq.symm⟩

/-- Every selected kernel pole is strictly inside the crossed strip. -/
private lemma wordCrossed_kernel_poles_inside_strip {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (v₁ v₂ : ℤ) (x : ℝ)
    (hx₁ : -((v₁ : ℝ) * fltDenominator (γ : Mat(2, ℤ)) τ / (γ 1 0 : ℝ) +
      fiveTermLatticeArgument γ τ v₁ v₂) < x)
    (hx₂ : x < -((v₁ : ℝ) * fltDenominator (γ : Mat(2, ℤ)) τ / (γ 1 0 : ℝ) +
      fiveTermLatticeArgument γ τ v₁ v₂) +
      (fltDenominator (γ : Mat(2, ℤ)) τ - 1) /
        ((γ 1 0 : ℝ) * (finiteDilogOrder γ : ℝ)))
    (s : ℂ) (hs : s ∈ wordCrossedKernelPoleSet γ τ v₁ v₂) :
    x < s.re ∧ s.re < x + (fltDenominator (γ : Mat(2, ℤ)) τ - 1) /
      (γ 1 0 : ℝ) ∧ s.im = 0 := by
  obtain ⟨⟨m, k⟩, hmk, rfl⟩ := Finset.mem_image.mp hs
  have hm := (mem_fiveTermWindow h _ (m, k)).mp hmk
  have hstrip := (wordCrossed_kernel_mem_window_iff_mem_strip h v₁ v₂ m k x
    hx₁ hx₂ ⟨hm.1, hm.2.1⟩).1 hmk
  simpa only [fiveTermStripPolePosition, Complex.ofReal_re, Complex.ofReal_im] using
    (show x < fiveTermLatticeArgument γ τ m k +
        (m : ℝ) * fltDenominator (γ : Mat(2, ℤ)) τ / (γ 1 0 : ℝ) ∧
      fiveTermLatticeArgument γ τ m k +
          (m : ℝ) * fltDenominator (γ : Mat(2, ℤ)) τ / (γ 1 0 : ℝ) <
        x + (fltDenominator (γ : Mat(2, ℤ)) τ - 1) / (γ 1 0 : ℝ) ∧
      (0 : ℝ) = 0 from ⟨hstrip.1, hstrip.2, rfl⟩)

/-- Every selected positive numerator product pole is strictly inside the crossed strip. -/
private lemma wordCrossed_product_poles_inside_strip {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (v₁ v₂ : ℤ) (x : ℝ) (F : Finset ℤ)
    (hx : x < fltDenominator (γ : Mat(2, ℤ)) τ / (γ 1 0 : ℝ))
    (hF : ∀ j : ℤ, j ∈ F ↔ 0 ≤ j ∧ (j : ℝ) / (γ 1 0 : ℝ) <
      -((v₁ : ℝ) * fltDenominator (γ : Mat(2, ℤ)) τ / (γ 1 0 : ℝ) +
        fiveTermLatticeArgument γ τ v₁ v₂))
    (hgrid : ∀ j : ℤ, 0 ≤ j →
      ((j : ℝ) / (γ 1 0 : ℝ) < x ↔
        (j : ℝ) / (γ 1 0 : ℝ) <
          -((v₁ : ℝ) * fltDenominator (γ : Mat(2, ℤ)) τ / (γ 1 0 : ℝ) +
            fiveTermLatticeArgument γ τ v₁ v₂)))
    (s : ℂ) (hs : s ∈ wordCrossedProductPoleSet γ τ F) :
    x < s.re ∧ s.re < x + (fltDenominator (γ : Mat(2, ℤ)) τ - 1) /
      (γ 1 0 : ℝ) ∧ s.im = 0 := by
  obtain ⟨j, hjF, rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨hjF, hj⟩ := Finset.mem_filter.mp hjF
  have hc : 0 < (γ 1 0 : ℝ) := by exact_mod_cast h.lowerLeft_pos
  have hjpos : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
  have hjx : (j : ℝ) / (γ 1 0 : ℝ) < x :=
    (hgrid j (by omega)).2 ((hF j).1 hjF).2
  have hdiv : 1 / (γ 1 0 : ℝ) ≤ (j : ℝ) / (γ 1 0 : ℝ) :=
    (div_le_div_iff_of_pos_right hc).2 hjpos
  have hε : (fltDenominator (γ : Mat(2, ℤ)) τ - 1) / (γ 1 0 : ℝ) +
      1 / (γ 1 0 : ℝ) =
      fltDenominator (γ : Mat(2, ℤ)) τ / (γ 1 0 : ℝ) := by ring
  norm_cast
  rw [Rat.cast_divInt]
  refine ⟨?_, ?_, rfl⟩ <;> linarith

/-- The finite kernel and product-pole sets of the crossed strip are disjoint. -/
private lemma wordCrossed_pole_sets_disjoint {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (v₁ v₂ : ℤ) (F : Finset ℤ) :
    Disjoint (wordCrossedKernelPoleSet γ τ v₁ v₂) (wordCrossedProductPoleSet γ τ F) := by
  apply Finset.disjoint_left.mpr
  intro s hK hP
  obtain ⟨⟨m, k⟩, _, rfl⟩ := Finset.mem_image.mp hK
  obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hP
  have hjpos : 0 < j := (Finset.mem_filter.mp hj).2
  exact wordCrossed_kernel_product_positions_disjoint h m k j hjpos heq.symm

/-! ### Meromorphic orders in the crossed strip

Away from the two listed pole sets the numerator has nonnegative order, while the denominator
has nonpositive order throughout the strip. -/

/-- Away from the listed product poles, the numerator has nonnegative order on the closed
crossed strip. -/
private lemma wordCrossed_numerator_order_nonneg_on_closed_strip {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (m : ℤ) (x β : ℝ) (F : Finset ℤ)
    (hx : x < fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
      (letterWord bs 1 0 : ℝ))
    (hgrid : ∀ j : ℤ, 0 ≤ j →
      ((j : ℝ) / (letterWord bs 1 0 : ℝ) < x ↔
        (j : ℝ) / (letterWord bs 1 0 : ℝ) < β))
    (hF : ∀ j : ℤ, j ∈ F ↔ 0 ≤ j ∧
      (j : ℝ) / (letterWord bs 1 0 : ℝ) < β)
    (hreg : ¬ IsPeriodLatticePoint (τ : ℂ)
      (((x + (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
        (letterWord bs 1 0 : ℝ) -
        (m : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
          (letterWord bs 1 0 : ℝ)) : ℂ)))
    (z : ℂ) (hz : z.re ≤ x +
      (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
        (letterWord bs 1 0 : ℝ))
    (hnot : z ∉ wordCrossedProductPoleSet (letterWord bs) τ F) :
    0 ≤ meromorphicOrderAt (fun ζ => faddeevWord bs m 0 ζ τ)
      (z - (m : ℂ) * fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
        (letterWord bs 1 0 : ℂ)) := by
  by_contra hn
  have hneg : meromorphicOrderAt (fun ζ => faddeevWord bs m 0 ζ τ)
      (z - (m : ℂ) * fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
        (letterWord bs 1 0 : ℂ)) < 0 := by simpa only [not_le] using hn
  obtain ⟨j, hj, hjz, hjx⟩ :=
    wordCrossed_raw_numerator_pole_location h m z x hx hz hneg
  by_cases hstrict : (j : ℝ) / (letterWord bs 1 0 : ℝ) < x
  · have hmem : j ∈ F := (hF j).2 ⟨by omega, (hgrid j (by omega)).1 hstrict⟩
    apply hnot
    exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨hmem, by omega⟩, hjz.symm⟩
  · have heq : (j : ℝ) / (letterWord bs 1 0 : ℝ) = x := by linarith
    have hzreal : z = ((x + (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
        (letterWord bs 1 0 : ℝ)) : ℂ) := by
      rw [hjz]
      exact_mod_cast (show
        (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
          (letterWord bs 1 0 : ℝ) +
          (j : ℝ) / (letterWord bs 1 0 : ℝ) =
        x + (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
          (letterWord bs 1 0 : ℝ) by rw [heq]; ring)
    apply hreg
    have hlat : IsPeriodLatticePoint (τ : ℂ)
        (z - (m : ℂ) * fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
          (letterWord bs 1 0 : ℂ)) := by
      by_contra hnl
      have ho := meromorphicOrderAt_faddeevWord_eq_zero bs m 0 h.periodsPos.slitPlane hnl
      rw [ho] at hneg
      exact (not_lt.mpr le_rfl) hneg
    convert hlat using 1
    rw [hzreal]
    norm_cast

/-- A lower bound for the numerator order passes to a shifted residue-kernel summand when
the shifted denominator has nonpositive order. -/
private lemma wordCrossed_shifted_term_order_ge_bound {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ v₁ v₂ : ℤ) (w : ℝ)
    (m : FiveTermIndex (letterWord bs)) (z : ℂ) (b : ℤ)
    (hnot : ∀ k : ℤ,
      z ≠ fiveTermStripPolePosition (letterWord bs) τ ((m : ℕ) : ℤ) k)
    (hnum : ((b : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (fun ζ => faddeevWord bs ((m : ℕ) : ℤ) 0 ζ τ)
        (z - ((m : ℕ) : ℂ) *
          fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
            (letterWord bs 1 0 : ℂ)))
    (hden : meromorphicOrderAt
      (fun ζ : ℂ => faddeevWord bs (((m : ℕ) : ℤ) + v₁) 0
        (ζ + fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ)
      (z - ((m : ℕ) : ℂ) *
        fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
          (letterWord bs 1 0 : ℂ)) ≤ 0) :
    ((b : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt
      (fun ζ => fiveTermWordResidueKernel bs ℓ v₁ w
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ ((m : ℕ) : ℤ)
          (ζ - ((m : ℕ) : ℂ) *
            fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
              (letterWord bs 1 0 : ℂ))) z := by
  let c : ℂ := ((m : ℕ) : ℂ) *
    fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) / (letterWord bs 1 0 : ℂ)
  have hpole : ∀ k : ℤ, z - c ≠
      fiveTermLatticeArgument (letterWord bs) τ ((m : ℕ) : ℤ) k := by
    intro k hk
    apply hnot k
    calc
      z = (z - c) + c := by ring
      _ = _ := by rw [hk]; dsimp [fiveTermStripPolePosition, c]; push_cast; ring
  rw [meromorphicOrderAt_fun_comp_sub_const_eq_meromorphicOrderAt]
  rw [meromorphicOrderAt_fiveTermWordResidueKernel h ℓ ((m : ℕ) : ℤ) v₁ w
    (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) (z - c) hpole]
  have hneg : 0 ≤ -meromorphicOrderAt
      (fun ζ : ℂ => faddeevWord bs (((m : ℕ) : ℤ) + v₁) 0
        (ζ + fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ) (z - c) := by
    rcases lt_or_eq_of_le hden with hlt | heq
    · exact (LinearOrderedAddCommGroupWithTop.neg_pos.mpr (Or.inl hlt)).le
    · rw [heq]
      simp
  have hle := le_add_of_nonneg_right
    (a := meromorphicOrderAt (fun ζ => faddeevWord bs ((m : ℕ) : ℤ) 0 ζ τ) (z - c)) hneg
  rw [← sub_eq_add_neg] at hle
  exact hnum.trans hle

/-- A shifted residue-kernel summand has pole order at least minus one away from its
kernel poles. -/
private lemma wordCrossed_shifted_term_order_ge_neg_one {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ v₁ v₂ : ℤ) (w : ℝ)
    (m : FiveTermIndex (letterWord bs)) (z : ℂ)
    (hnot : ∀ k : ℤ,
      z ≠ fiveTermStripPolePosition (letterWord bs) τ ((m : ℕ) : ℤ) k)
    (hden : meromorphicOrderAt
      (fun ζ : ℂ => faddeevWord bs (((m : ℕ) : ℤ) + v₁) 0
        (ζ + fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ)
      (z - ((m : ℕ) : ℂ) *
        fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
          (letterWord bs 1 0 : ℂ)) ≤ 0) :
    ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt
      (fun ζ => fiveTermWordResidueKernel bs ℓ v₁ w
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ ((m : ℕ) : ℤ)
          (ζ - ((m : ℕ) : ℂ) *
            fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
              (letterWord bs 1 0 : ℂ))) z := by
  exact wordCrossed_shifted_term_order_ge_bound h ℓ v₁ v₂ w m z (-1) hnot
    (meromorphicOrderAt_faddeevWord_ge_neg_one bs h.ne_nil ((m : ℕ) : ℤ) 0
      h.fixedPoint.irrational (fun w hw => (h.periodsPos w hw).2) _) hden

/-- A shifted summand away from both pole sets has nonnegative order. -/
private lemma wordCrossed_shifted_term_order_nonneg {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ v₁ v₂ : ℤ) (w : ℝ)
    (m : FiveTermIndex (letterWord bs)) (z : ℂ)
    (hnot : ∀ k : ℤ,
      z ≠ fiveTermStripPolePosition (letterWord bs) τ ((m : ℕ) : ℤ) k)
    (hnum : 0 ≤ meromorphicOrderAt (fun ζ => faddeevWord bs ((m : ℕ) : ℤ) 0 ζ τ)
      (z - ((m : ℕ) : ℂ) *
        fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
          (letterWord bs 1 0 : ℂ)))
    (hden : meromorphicOrderAt
      (fun ζ : ℂ => faddeevWord bs (((m : ℕ) : ℤ) + v₁) 0
        (ζ + fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ)
      (z - ((m : ℕ) : ℂ) *
        fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
          (letterWord bs 1 0 : ℂ)) ≤ 0) :
    0 ≤ meromorphicOrderAt
      (fun ζ => fiveTermWordResidueKernel bs ℓ v₁ w
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ ((m : ℕ) : ℤ)
          (ζ - ((m : ℕ) : ℂ) *
            fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
              (letterWord bs 1 0 : ℂ))) z := by
  exact wordCrossed_shifted_term_order_ge_bound h ℓ v₁ v₂ w m z 0 hnot hnum hden

/-! ### The rectangle residue identity

The residue sum is bounded away from the two finite pole sets, so all other singularities in
a compact rectangle are removable. The rectangle theorem then sums the residue limits of the
selected poles. -/

/-- Away from the listed poles, the residue sum is bounded on a punctured neighborhood of
each closed-strip point. -/
private lemma wordCrossed_residue_sum_bounded_off_poles {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ v₁ v₂ : ℤ) (w x β : ℝ) (F : Finset ℤ)
    (hβ : -((v₁ : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
        (letterWord bs 1 0 : ℝ) +
      fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) < x)
    (hx₂ : x < -((v₁ : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
        (letterWord bs 1 0 : ℝ) +
      fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) +
      (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
        ((letterWord bs 1 0 : ℝ) * (finiteDilogOrder (letterWord bs) : ℝ)))
    (hx : x < fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
      (letterWord bs 1 0 : ℝ))
    (hgrid : ∀ j : ℤ, 0 ≤ j →
      ((j : ℝ) / (letterWord bs 1 0 : ℝ) < x ↔
        (j : ℝ) / (letterWord bs 1 0 : ℝ) < β))
    (hF : ∀ j : ℤ, j ∈ F ↔ 0 ≤ j ∧
      (j : ℝ) / (letterWord bs 1 0 : ℝ) < β)
    (hreg : ∀ m : FiveTermIndex (letterWord bs),
      IsFiveTermResidueCrossing (letterWord bs) τ ((m : ℕ) : ℤ)
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂)
        (x - ((m : ℕ) : ℝ) *
          fltDenominator (letterWord bs : Mat(2, ℤ)) τ / (letterWord bs 1 0 : ℝ)))
    (z : ℂ) (hz₁ : x ≤ z.re)
    (hz₂ : z.re ≤ x + (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
      (letterWord bs 1 0 : ℝ))
    (hK : z ∉ wordCrossedKernelPoleSet (letterWord bs) τ v₁ v₂)
    (hP : z ∉ wordCrossedProductPoleSet (letterWord bs) τ F) :
    IsBoundedUnder (· ≤ ·) (𝓝[≠] z)
      (fun ζ => ‖fiveTermWordResidueSum bs ℓ v₁ w
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ ζ‖) := by
  apply fiveTermWordResidueSum_bdd_of_order_nonneg h
  intro m
  have hnot := wordCrossed_no_kernel_pole_outside_set h.fixedPoint v₁ v₂ x
    hβ hx₂ z hz₁ hz₂ hK m
  have hright := fiveTerm_strip_right_crossing h v₁ v₂ x hreg m
  have hright' : ¬ IsPeriodLatticePoint (τ : ℂ)
      (((x + (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
        (letterWord bs 1 0 : ℝ) -
        (((m : ℕ) : ℤ) : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
          (letterWord bs 1 0 : ℝ)) : ℂ)) := by
    convert hright.lattice.base using 1
    push_cast
    ring_nf
  have hnum := wordCrossed_numerator_order_nonneg_on_closed_strip h
    ((m : ℕ) : ℤ) x β F hx hgrid hF hright' z hz₂ hP
  have hden := wordCrossed_denominator_order_nonpos_on_strip h
    ((m : ℕ) : ℤ) v₁ v₂ x hβ z hz₁
  exact wordCrossed_shifted_term_order_nonneg h ℓ v₁ v₂ w m z hnot hnum hden

/-- The crossed rectangle has only the selected poles and a finite set of removable raw
product singularities. -/
private lemma wordCrossed_rectangle_removable {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ v₁ v₂ : ℤ) (w x β : ℝ) (F : Finset ℤ)
    (hβ : -((v₁ : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
        (letterWord bs 1 0 : ℝ) +
      fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) < x)
    (hx₂ : x < -((v₁ : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
        (letterWord bs 1 0 : ℝ) +
      fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) +
      (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
        ((letterWord bs 1 0 : ℝ) * (finiteDilogOrder (letterWord bs) : ℝ)))
    (hx : x < fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
      (letterWord bs 1 0 : ℝ))
    (hgrid : ∀ j : ℤ, 0 ≤ j →
      ((j : ℝ) / (letterWord bs 1 0 : ℝ) < x ↔
        (j : ℝ) / (letterWord bs 1 0 : ℝ) < β))
    (hF : ∀ j : ℤ, j ∈ F ↔ 0 ≤ j ∧
      (j : ℝ) / (letterWord bs 1 0 : ℝ) < β)
    (hreg : ∀ m : FiveTermIndex (letterWord bs),
      IsFiveTermResidueCrossing (letterWord bs) τ ((m : ℕ) : ℤ)
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂)
        (x - ((m : ℕ) : ℝ) *
          fltDenominator (letterWord bs : Mat(2, ℤ)) τ / (letterWord bs 1 0 : ℝ))) :
    ∀ Y : ℝ, ∃ E : Finset ℂ,
      Disjoint (wordCrossedKernelPoleSet (letterWord bs) τ v₁ v₂ ∪
        wordCrossedProductPoleSet (letterWord bs) τ F) E ∧
      DifferentiableOn ℂ
        (fiveTermWordResidueSum bs ℓ v₁ w
          (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ)
        ((Icc x (x + (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
          (letterWord bs 1 0 : ℝ)) ×ℂ Icc (-Y) Y) \
          (↑(wordCrossedKernelPoleSet (letterWord bs) τ v₁ v₂ ∪
            wordCrossedProductPoleSet (letterWord bs) τ F) ∪ ↑E)) ∧
      (∀ e ∈ E, ∀ᶠ ζ in 𝓝[≠] e,
        DifferentiableAt ℂ (fiveTermWordResidueSum bs ℓ v₁ w
          (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ) ζ) ∧
      (∀ e ∈ E, IsBoundedUnder (· ≤ ·) (𝓝[≠] e)
        (fun ζ => ‖fiveTermWordResidueSum bs ℓ v₁ w
          (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ ζ‖)) := by
  intro Y
  let A : Set ℂ := Icc x
    (x + (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
      (letterWord bs 1 0 : ℝ)) ×ℂ Icc (-Y) Y
  have hA : IsCompact A := isCompact_Icc.reProdIm isCompact_Icc
  apply exists_finset_removable_of_meromorphic_bounded _ A hA _
    (meromorphic_fiveTermWordResidueSum h ℓ v₁ w
      (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂))
  intro z hz hn
  have hK : z ∉ wordCrossedKernelPoleSet (letterWord bs) τ v₁ v₂ := by
    intro hm
    exact hn (by simp [hm])
  have hP : z ∉ wordCrossedProductPoleSet (letterWord bs) τ F := by
    intro hm
    exact hn (by simp [hm])
  exact wordCrossed_residue_sum_bounded_off_poles h ℓ v₁ v₂ w x β F
    hβ hx₂ hx hgrid hF hreg z hz.1.1 hz.1.2 hK hP

/-- A shifted summand with nonnegative order has zero residue limit. -/
private lemma wordCrossed_shifted_term_residue_zero {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ v₁ v₂ : ℤ) (w : ℝ)
    (m : FiveTermIndex (letterWord bs)) (s : ℂ)
    (hnot : ∀ k : ℤ,
      s ≠ fiveTermStripPolePosition (letterWord bs) τ ((m : ℕ) : ℤ) k)
    (hnum : 0 ≤ meromorphicOrderAt
      (fun ζ => faddeevWord bs ((m : ℕ) : ℤ) 0 ζ τ)
      (s - ((m : ℕ) : ℂ) *
        fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
          (letterWord bs 1 0 : ℂ)))
    (hden : meromorphicOrderAt
      (fun ζ : ℂ => faddeevWord bs (((m : ℕ) : ℤ) + v₁) 0
        (ζ + fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ)
      (s - ((m : ℕ) : ℂ) *
        fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
          (letterWord bs 1 0 : ℂ)) ≤ 0) :
    Tendsto (fun ζ : ℂ => (ζ - s) *
      fiveTermWordResidueKernel bs ℓ v₁ w
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ ((m : ℕ) : ℤ)
        (ζ - ((m : ℕ) : ℂ) *
          fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
            (letterWord bs 1 0 : ℂ))) (𝓝[≠] s) (𝓝 0) := by
  let f : ℂ → ℂ := fun ζ => fiveTermWordResidueKernel bs ℓ v₁ w
    (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ ((m : ℕ) : ℤ)
    (ζ - ((m : ℕ) : ℂ) *
      fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
        (letterWord bs 1 0 : ℂ))
  have hf : MeromorphicAt f s := by
    change MeromorphicAt ((fiveTermWordResidueKernel bs ℓ v₁ w
      (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ ((m : ℕ) : ℤ)) ∘
        (fun ζ => ζ - ((m : ℕ) : ℂ) *
          fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
            (letterWord bs 1 0 : ℂ))) s
    apply (meromorphicAt_comp_sub_const_iff_meromorphicAt).2
    exact meromorphic_fiveTermWordResidueKernel h ℓ v₁ ((m : ℕ) : ℤ) w
      (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) _
  have ho := wordCrossed_shifted_term_order_nonneg h ℓ v₁ v₂ w m s hnot hnum hden
  obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hf ho
  have hs : Tendsto (fun ζ : ℂ => ζ - s) (𝓝[≠] s) (𝓝 0) := by
    simpa only [sub_self, id_eq] using
      (tendsto_id.sub_const s).mono_left
        (show 𝓝[≠] s ≤ 𝓝 s from nhdsWithin_le_nhds)
  simpa only [f, zero_mul] using hs.mul hc

/-- Every product pole has a residue limit for the finite residue sum. -/
private lemma wordCrossed_residue_sum_residue_exists_at_product_pole {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ v₁ v₂ : ℤ) (w x : ℝ)
    (hx : -((v₁ : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
        (letterWord bs 1 0 : ℝ) +
      fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) < x)
    (hx₂ : x < -((v₁ : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
        (letterWord bs 1 0 : ℝ) +
      fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) +
      (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
        ((letterWord bs 1 0 : ℝ) * (finiteDilogOrder (letterWord bs) : ℝ)))
    (s : ℂ) (hs₁ : x ≤ s.re)
    (hs₂ : s.re ≤ x + (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
      (letterWord bs 1 0 : ℝ))
    (hK : s ∉ wordCrossedKernelPoleSet (letterWord bs) τ v₁ v₂) :
    ∃ R : ℂ, Tendsto (fun ζ : ℂ => (ζ - s) *
      fiveTermWordResidueSum bs ℓ v₁ w
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ ζ)
      (𝓝[≠] s) (𝓝 R) := by
  have hm (m : FiveTermIndex (letterWord bs)) :
      ∃ R : ℂ, Tendsto (fun ζ : ℂ => (ζ - s) *
        fiveTermWordResidueKernel bs ℓ v₁ w
          (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ ((m : ℕ) : ℤ)
          (ζ - ((m : ℕ) : ℂ) *
            fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
              (letterWord bs 1 0 : ℂ))) (𝓝[≠] s) (𝓝 R) := by
    have hnot := wordCrossed_no_kernel_pole_outside_set h.fixedPoint v₁ v₂ x
      hx hx₂ s hs₁ hs₂ hK m
    have hden := wordCrossed_denominator_order_nonpos_on_strip h
      ((m : ℕ) : ℤ) v₁ v₂ x hx s hs₁
    let f : ℂ → ℂ := fun ζ => fiveTermWordResidueKernel bs ℓ v₁ w
      (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ ((m : ℕ) : ℤ)
      (ζ - ((m : ℕ) : ℂ) *
        fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
          (letterWord bs 1 0 : ℂ))
    have hmer : MeromorphicAt f s := by
      change MeromorphicAt ((fiveTermWordResidueKernel bs ℓ v₁ w
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ ((m : ℕ) : ℤ)) ∘
          (fun ζ => ζ - ((m : ℕ) : ℂ) *
            fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
              (letterWord bs 1 0 : ℂ))) s
      apply (meromorphicAt_comp_sub_const_iff_meromorphicAt).2
      exact meromorphic_fiveTermWordResidueKernel h ℓ v₁ ((m : ℕ) : ℤ) w
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) _
    exact tendsto_sub_mul_of_meromorphicOrderAt_ge_neg_one f s hmer
      (wordCrossed_shifted_term_order_ge_neg_one h ℓ v₁ v₂ w m s hnot hden)
  choose R hR using hm
  refine ⟨∑ m : FiveTermIndex (letterWord bs), R m, ?_⟩
  have hsum := tendsto_finsetSum Finset.univ (fun m _ => hR m)
  convert hsum using 1
  funext ζ
  simp only [fiveTermWordResidueSum, Finset.mul_sum]

/-- The rectangle boundary integral equals the sum of residue limits at its kernel and
product poles. -/
private lemma wordCrossed_rectangle_identity_of_residue_limits {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ v₁ v₂ : ℤ) (w x β : ℝ) (F : Finset ℤ)
    (hβeq : β = -((v₁ : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
      (letterWord bs 1 0 : ℝ) +
      fiveTermLatticeArgument (letterWord bs) τ v₁ v₂))
    (hβ : -((v₁ : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
        (letterWord bs 1 0 : ℝ) +
      fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) < x)
    (hx₂ : x < -((v₁ : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
        (letterWord bs 1 0 : ℝ) +
      fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) +
      (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
        ((letterWord bs 1 0 : ℝ) * (finiteDilogOrder (letterWord bs) : ℝ)))
    (hx : x < fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
      (letterWord bs 1 0 : ℝ))
    (hgrid : ∀ j : ℤ, 0 ≤ j →
      ((j : ℝ) / (letterWord bs 1 0 : ℝ) < x ↔
        (j : ℝ) / (letterWord bs 1 0 : ℝ) < β))
    (hF : ∀ j : ℤ, j ∈ F ↔ 0 ≤ j ∧
      (j : ℝ) / (letterWord bs 1 0 : ℝ) < β)
    (hreg : ∀ m : FiveTermIndex (letterWord bs),
      IsFiveTermResidueCrossing (letterWord bs) τ ((m : ℕ) : ℤ)
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂)
        (x - ((m : ℕ) : ℝ) *
          fltDenominator (letterWord bs : Mat(2, ℤ)) τ / (letterWord bs 1 0 : ℝ)))
    (R : ℂ → ℂ)
    (hR : ∀ s ∈ wordCrossedKernelPoleSet (letterWord bs) τ v₁ v₂ ∪
        wordCrossedProductPoleSet (letterWord bs) τ F,
      Tendsto (fun ζ : ℂ => (ζ - s) *
        fiveTermWordResidueSum bs ℓ v₁ w
          (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ ζ)
        (𝓝[≠] s) (𝓝 (R s)))
    (Y : ℝ) (hY : 0 < Y) :
    (∫ t : ℝ in x..x + (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
        (letterWord bs 1 0 : ℝ),
      fiveTermWordResidueSum bs ℓ v₁ w
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ
        ((t : ℂ) + (-Y) * I)) -
    (∫ t : ℝ in x..x + (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
        (letterWord bs 1 0 : ℝ),
      fiveTermWordResidueSum bs ℓ v₁ w
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ
        ((t : ℂ) + Y * I)) +
    I • (∫ t : ℝ in -Y..Y, fiveTermWordResidueSum bs ℓ v₁ w
      (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ
        (((x + (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
          (letterWord bs 1 0 : ℝ) : ℝ) : ℂ) + t * I)) -
    I • (∫ t : ℝ in -Y..Y, fiveTermWordResidueSum bs ℓ v₁ w
      (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ ((x : ℂ) + t * I)) =
    2 * Real.pi * I *
      ∑ s ∈ wordCrossedKernelPoleSet (letterWord bs) τ v₁ v₂ ∪
        wordCrossedProductPoleSet (letterWord bs) τ F, R s := by
  let X : ℝ := x + (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
    (letterWord bs 1 0 : ℝ)
  let L : ℂ → ℂ := fiveTermWordResidueSum bs ℓ v₁ w
    (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ
  let S : Finset ℂ := wordCrossedKernelPoleSet (letterWord bs) τ v₁ v₂ ∪
    wordCrossedProductPoleSet (letterWord bs) τ F
  have hzre : (((x : ℂ) + (-Y) * I)).re = x := by simp
  have hzim : (((x : ℂ) + (-Y) * I)).im = -Y := by simp
  have hwre : (((X : ℂ) + Y * I)).re = X := by simp
  have hwim : (((X : ℂ) + Y * I)).im = Y := by simp
  obtain ⟨E, hSE, hdiff, hEd, hEb⟩ :=
    wordCrossed_rectangle_removable h ℓ v₁ v₂ w x β F
      hβ hx₂ hx hgrid hF hreg Y
  have hwidth : x ≤ X := by
    dsimp [X]
    have hpos : 0 < (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
        (letterWord bs 1 0 : ℝ) :=
      div_pos (sub_pos.mpr h.fixedPoint.one_lt_fltDenominator)
        (by exact_mod_cast h.fixedPoint.lowerLeft_pos)
    linarith
  have hdiff' := differentiableOn_rect_of_Icc L x X Y S E hwidth hY.le (by
    simpa only [L, S, X] using hdiff)
  have hrect := integral_boundary_rect_eq_sum_residues_of_bounded L
    ((x : ℂ) + (-Y) * I) ((X : ℂ) + Y * I) S E R
    hSE (by
      intro s hs
      obtain hsK | hsP := Finset.mem_union.mp hs
      · obtain ⟨hlo, hhi, him⟩ :=
          wordCrossed_kernel_poles_inside_strip h.fixedPoint v₁ v₂ x hβ hx₂ s hsK
        simp only [hzre, hwre, hzim, hwim, him]
        exact ⟨hlo, hhi, by linarith, hY⟩
      · obtain ⟨hlo, hhi, him⟩ :=
          wordCrossed_product_poles_inside_strip h.fixedPoint v₁ v₂ x F hx
            (by simpa only [hβeq] using hF) (by simpa only [hβeq] using hgrid) s hsP
        simp only [hzre, hwre, hzim, hwim, him]
        exact ⟨hlo, hhi, by linarith, hY⟩)
    hdiff' (by intro s hs; exact hR s hs) hEd hEb
  rw [hzre, hzim, hwre, hwim] at hrect
  dsimp only [L, S, X] at hrect
  simpa only [Complex.ofReal_neg] using hrect

/-! ### Kernel residue fibers

At each common-line kernel pole, one residue arises from each contour index that has that pole.
Summing first over indices and then over positions recovers the source-window sum. -/

/-- The residue fiber in the crossed window `[-N-S(v),-S(v))`. -/
private abbrev wordCrossedResidueFiber (bs : List ℤ) (τ : ℝ)
    (ℓ v₁ v₂ : ℤ) (w : ℝ) (m : FiveTermIndex (letterWord bs)) (s : ℂ) : ℂ :=
  fiveTermWindowResidueFiber bs τ
    (-(finiteDilogOrder (letterWord bs) : ℤ) -
      fiveTermLatticeIndex (letterWord bs) v₁ v₂)
    ℓ v₁ w (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) m s

/-- A kernel pole in a source-index fiber contributes its kernel residue. -/
private lemma wordCrossed_residue_fiber_eq_of_pole {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ v₁ v₂ : ℤ) (w x : ℝ)
    (hx₁ : -((v₁ : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
        (letterWord bs 1 0 : ℝ) +
      fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) < x)
    (hx₂ : x < -((v₁ : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
        (letterWord bs 1 0 : ℝ) +
      fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) +
      (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
        ((letterWord bs 1 0 : ℝ) * (finiteDilogOrder (letterWord bs) : ℝ)))
    (m : FiveTermIndex (letterWord bs)) (k : ℤ)
    (hlo : x < (fiveTermStripPolePosition (letterWord bs) τ ((m : ℕ) : ℤ) k).re)
    (hhi : (fiveTermStripPolePosition (letterWord bs) τ ((m : ℕ) : ℤ) k).re <
      x + (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
        (letterWord bs 1 0 : ℝ)) :
    wordCrossedResidueFiber bs τ ℓ v₁ v₂ w m
      (fiveTermStripPolePosition (letterWord bs) τ ((m : ℕ) : ℤ) k) =
      fiveTermWordKernelResidue bs ℓ v₁ w
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ ((m : ℕ) : ℤ)
        (fiveTermLatticeArgument (letterWord bs) τ ((m : ℕ) : ℤ) k) := by
  have hmem := (wordCrossed_kernel_mem_window_iff_mem_strip h.fixedPoint v₁ v₂
    ((m : ℕ) : ℤ) k x hx₁ hx₂ (fiveTermIndex_range h.fixedPoint m)).2 (by
      simpa only [fiveTermStripPolePosition, Complex.ofReal_re, Int.cast_natCast] using
        (show x < (fiveTermStripPolePosition (letterWord bs) τ ((m : ℕ) : ℤ) k).re ∧
          (fiveTermStripPolePosition (letterWord bs) τ ((m : ℕ) : ℤ) k).re <
            x + (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
              (letterWord bs 1 0 : ℝ) from ⟨hlo, hhi⟩))
  exact fiveTermWindowResidueFiber_eq_of_pole h
    (-(finiteDilogOrder (letterWord bs) : ℤ) -
      fiveTermLatticeIndex (letterWord bs) v₁ v₂)
    ℓ v₁ w (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) m k hmem

/-- A source-index fiber with no kernel pole at a position contributes zero. -/
private lemma wordCrossed_residue_fiber_eq_zero_of_no_pole (bs : List ℤ) (τ : ℝ)
    (ℓ v₁ v₂ : ℤ) (w : ℝ) (m : FiveTermIndex (letterWord bs)) (s : ℂ)
    (hnot : ∀ k : ℤ,
      s ≠ fiveTermStripPolePosition (letterWord bs) τ ((m : ℕ) : ℤ) k) :
    wordCrossedResidueFiber bs τ ℓ v₁ v₂ w m s = 0 := by
  exact fiveTermWindowResidueFiber_eq_zero bs τ
    (-(finiteDilogOrder (letterWord bs) : ℤ) -
      fiveTermLatticeIndex (letterWord bs) v₁ v₂)
    ℓ v₁ w (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) m s hnot

/-- Every window pair has a corresponding finite first-coordinate contour index. -/
private lemma wordCrossed_window_first_index {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (v₁ v₂ : ℤ) (mk : ℤ × ℤ)
    (hmk : mk ∈ fiveTermWindow γ
      (-(finiteDilogOrder γ : ℤ) - fiveTermLatticeIndex γ v₁ v₂)) :
    ∃ m : FiveTermIndex γ, ((m : ℕ) : ℤ) = mk.1 := by
  obtain ⟨hm0, hm1, _, _⟩ := (mem_fiveTermWindow h _ mk).mp hmk
  have hc : 0 < γ 1 0 := h.lowerLeft_pos
  have hlt : mk.1.toNat < (γ 1 0).toNat := by
    exact (Int.toNat_lt_toNat hc).2 hm1
  refine ⟨⟨mk.1.toNat, hlt⟩, ?_⟩
  simp [Int.toNat_of_nonneg hm0]

/-- Fiber sums at one kernel position equal the selected window-pair sum at that position. -/
private lemma wordCrossed_residue_fibers_at_position {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ v₁ v₂ : ℤ) (w : ℝ) (s : ℂ) :
    (∑ m : FiveTermIndex (letterWord bs),
      wordCrossedResidueFiber bs τ ℓ v₁ v₂ w m s) =
      ∑ mk ∈ fiveTermWindow (letterWord bs)
          (-(finiteDilogOrder (letterWord bs) : ℤ) -
            fiveTermLatticeIndex (letterWord bs) v₁ v₂) with
        fiveTermStripPolePosition (letterWord bs) τ mk.1 mk.2 = s,
        fiveTermWordKernelResidue bs ℓ v₁ w
          (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ mk.1
          (fiveTermLatticeArgument (letterWord bs) τ mk.1 mk.2) := by
  simp only [wordCrossedResidueFiber, fiveTermWindowResidueFiber, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro mk hmk
  obtain ⟨m0, hm0⟩ := wordCrossed_window_first_index h.fixedPoint v₁ v₂ mk hmk
  by_cases hs : fiveTermStripPolePosition (letterWord bs) τ mk.1 mk.2 = s
  · simp only [hs, and_true]
    rw [Finset.sum_eq_single m0]
    · simp [hm0]
    · intro m hm hne
      have hne' : mk.1 ≠ ((m : ℕ) : ℤ) := by
        intro heq
        apply hne
        apply Fin.ext
        exact_mod_cast (hm0.trans heq).symm
      simp [hne']
    · simp
  · simp [hs]

/-- Summing over the kernel positions recovers the full crossed-window residue sum. -/
private lemma wordCrossed_residue_fibers_total {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ v₁ v₂ : ℤ) (w : ℝ) :
    (∑ s ∈ wordCrossedKernelPoleSet (letterWord bs) τ v₁ v₂,
      ∑ m : FiveTermIndex (letterWord bs),
        wordCrossedResidueFiber bs τ ℓ v₁ v₂ w m s) =
      ∑ mk ∈ fiveTermWindow (letterWord bs)
          (-(finiteDilogOrder (letterWord bs) : ℤ) -
            fiveTermLatticeIndex (letterWord bs) v₁ v₂),
        fiveTermWordKernelResidue bs ℓ v₁ w
          (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ mk.1
          (fiveTermLatticeArgument (letterWord bs) τ mk.1 mk.2) := by
  simp_rw [wordCrossed_residue_fibers_at_position h]
  have hmap : ∀ mk ∈ fiveTermWindow (letterWord bs)
      (-(finiteDilogOrder (letterWord bs) : ℤ) -
        fiveTermLatticeIndex (letterWord bs) v₁ v₂),
      fiveTermStripPolePosition (letterWord bs) τ mk.1 mk.2 ∈
        wordCrossedKernelPoleSet (letterWord bs) τ v₁ v₂ := by
    intro mk hmk
    exact Finset.mem_image.mpr ⟨mk, hmk, rfl⟩
  exact Finset.sum_fiberwise_of_maps_to hmap
    (fun mk => fiveTermWordKernelResidue bs ℓ v₁ w
      (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ mk.1
      (fiveTermLatticeArgument (letterWord bs) τ mk.1 mk.2))

/-- The residue limit of one shifted summand at a kernel position equals its fiber
contribution. -/
private lemma wordCrossed_shifted_term_residue_fiber_at_kernel_pole
    {bs : List ℤ} {τ : ℝ} (h : IsLetterWordFixedPoint bs τ)
    (ℓ v₁ v₂ : ℤ) (w x β : ℝ) (F : Finset ℤ)
    (hβ : -((v₁ : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
        (letterWord bs 1 0 : ℝ) +
      fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) < x)
    (hx₂ : x < -((v₁ : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
        (letterWord bs 1 0 : ℝ) +
      fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) +
      (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
        ((letterWord bs 1 0 : ℝ) * (finiteDilogOrder (letterWord bs) : ℝ)))
    (hx : x < fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
      (letterWord bs 1 0 : ℝ))
    (hgrid : ∀ j : ℤ, 0 ≤ j →
      ((j : ℝ) / (letterWord bs 1 0 : ℝ) < x ↔
        (j : ℝ) / (letterWord bs 1 0 : ℝ) < β))
    (hF : ∀ j : ℤ, j ∈ F ↔ 0 ≤ j ∧
      (j : ℝ) / (letterWord bs 1 0 : ℝ) < β)
    (hreg : ∀ m : FiveTermIndex (letterWord bs),
      IsFiveTermResidueCrossing (letterWord bs) τ ((m : ℕ) : ℤ)
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂)
        (x - ((m : ℕ) : ℝ) *
          fltDenominator (letterWord bs : Mat(2, ℤ)) τ / (letterWord bs 1 0 : ℝ)))
    (s : ℂ) (hs : s ∈ wordCrossedKernelPoleSet (letterWord bs) τ v₁ v₂)
    (m : FiveTermIndex (letterWord bs)) :
    Tendsto (fun ζ : ℂ => (ζ - s) *
      fiveTermWordResidueKernel bs ℓ v₁ w
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ ((m : ℕ) : ℤ)
        (ζ - ((m : ℕ) : ℂ) *
          fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
            (letterWord bs 1 0 : ℂ))) (𝓝[≠] s)
      (𝓝 (wordCrossedResidueFiber bs τ ℓ v₁ v₂ w m s)) := by
  obtain ⟨hs₁, hs₂, _⟩ :=
    wordCrossed_kernel_poles_inside_strip h.fixedPoint v₁ v₂ x hβ hx₂ s hs
  by_cases hp : ∃ k : ℤ,
      s = fiveTermStripPolePosition (letterWord bs) τ ((m : ℕ) : ℤ) k
  · obtain ⟨k, rfl⟩ := hp
    rw [wordCrossed_residue_fiber_eq_of_pole h ℓ v₁ v₂ w x hβ hx₂ m k hs₁ hs₂]
    exact tendsto_sub_mul_fiveTermWordResidueKernel_sub h ℓ w
      ((m : ℕ) : ℤ) k v₁ v₂
  · have hnot : ∀ k : ℤ,
        s ≠ fiveTermStripPolePosition (letterWord bs) τ ((m : ℕ) : ℤ) k := by
      simpa only [not_exists] using hp
    rw [wordCrossed_residue_fiber_eq_zero_of_no_pole bs τ ℓ v₁ v₂ w m s hnot]
    have hP : s ∉ wordCrossedProductPoleSet (letterWord bs) τ F :=
      Finset.disjoint_left.mp (wordCrossed_pole_sets_disjoint h.fixedPoint v₁ v₂ F) hs
    have hright := fiveTerm_strip_right_crossing h v₁ v₂ x hreg m
    have hright' : ¬ IsPeriodLatticePoint (τ : ℂ)
        (((x + (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
          (letterWord bs 1 0 : ℝ) -
          (((m : ℕ) : ℤ) : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
            (letterWord bs 1 0 : ℝ)) : ℂ)) := by
      convert hright.lattice.base using 1
      push_cast
      ring_nf
    have hnum := wordCrossed_numerator_order_nonneg_on_closed_strip h
      ((m : ℕ) : ℤ) x β F hx hgrid hF hright' s hs₂.le hP
    have hden := wordCrossed_denominator_order_nonpos_on_strip h
      ((m : ℕ) : ℤ) v₁ v₂ x hβ s hs₁.le
    exact wordCrossed_shifted_term_residue_zero h ℓ v₁ v₂ w m s hnot hnum hden

/-- At one kernel position, residues of coincident shifted summands add by fibers. -/
private lemma wordCrossed_residue_sum_residue_fibers_at_kernel_pole
    {bs : List ℤ} {τ : ℝ} (h : IsLetterWordFixedPoint bs τ)
    (ℓ v₁ v₂ : ℤ) (w x β : ℝ) (F : Finset ℤ)
    (hβ : -((v₁ : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
        (letterWord bs 1 0 : ℝ) +
      fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) < x)
    (hx₂ : x < -((v₁ : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
        (letterWord bs 1 0 : ℝ) +
      fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) +
      (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
        ((letterWord bs 1 0 : ℝ) * (finiteDilogOrder (letterWord bs) : ℝ)))
    (hx : x < fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
      (letterWord bs 1 0 : ℝ))
    (hgrid : ∀ j : ℤ, 0 ≤ j →
      ((j : ℝ) / (letterWord bs 1 0 : ℝ) < x ↔
        (j : ℝ) / (letterWord bs 1 0 : ℝ) < β))
    (hF : ∀ j : ℤ, j ∈ F ↔ 0 ≤ j ∧
      (j : ℝ) / (letterWord bs 1 0 : ℝ) < β)
    (hreg : ∀ m : FiveTermIndex (letterWord bs),
      IsFiveTermResidueCrossing (letterWord bs) τ ((m : ℕ) : ℤ)
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂)
        (x - ((m : ℕ) : ℝ) *
          fltDenominator (letterWord bs : Mat(2, ℤ)) τ / (letterWord bs 1 0 : ℝ)))
    (s : ℂ) (hs : s ∈ wordCrossedKernelPoleSet (letterWord bs) τ v₁ v₂) :
    Tendsto (fun ζ : ℂ => (ζ - s) *
      fiveTermWordResidueSum bs ℓ v₁ w
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ ζ)
      (𝓝[≠] s)
      (𝓝 (∑ m : FiveTermIndex (letterWord bs),
        wordCrossedResidueFiber bs τ ℓ v₁ v₂ w m s)) := by
  have ht (m : FiveTermIndex (letterWord bs)) :=
    wordCrossed_shifted_term_residue_fiber_at_kernel_pole h ℓ v₁ v₂ w x β F
      hβ hx₂ hx hgrid hF hreg s hs m
  have hsum := tendsto_finsetSum Finset.univ (fun m _ => ht m)
  convert hsum using 1
  funext ζ
  simp only [fiveTermWordResidueSum, Finset.mul_sum]

/-- Every selected numerator product pole admits a residue limit of the finite sum. -/
private lemma wordCrossed_product_residue_limits {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ v₁ v₂ : ℤ) (w x : ℝ) (F : Finset ℤ)
    (hβ : -((v₁ : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
        (letterWord bs 1 0 : ℝ) +
      fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) < x)
    (hx₂ : x < -((v₁ : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
        (letterWord bs 1 0 : ℝ) +
      fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) +
      (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
        ((letterWord bs 1 0 : ℝ) * (finiteDilogOrder (letterWord bs) : ℝ)))
    (hx : x < fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
      (letterWord bs 1 0 : ℝ))
    (hF : ∀ j : ℤ, j ∈ F ↔ 0 ≤ j ∧
      (j : ℝ) / (letterWord bs 1 0 : ℝ) <
        -((v₁ : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
          (letterWord bs 1 0 : ℝ) +
          fiveTermLatticeArgument (letterWord bs) τ v₁ v₂))
    (hgrid : ∀ j : ℤ, 0 ≤ j →
      ((j : ℝ) / (letterWord bs 1 0 : ℝ) < x ↔
        (j : ℝ) / (letterWord bs 1 0 : ℝ) <
          -((v₁ : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
            (letterWord bs 1 0 : ℝ) +
            fiveTermLatticeArgument (letterWord bs) τ v₁ v₂))) :
    ∃ RP : ℂ → ℂ,
      ∀ s ∈ wordCrossedProductPoleSet (letterWord bs) τ F,
        Tendsto (fun ζ : ℂ => (ζ - s) *
          fiveTermWordResidueSum bs ℓ v₁ w
            (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ ζ)
          (𝓝[≠] s) (𝓝 (RP s)) := by
  have hprod (s : ℂ) (hs : s ∈ wordCrossedProductPoleSet (letterWord bs) τ F) :
      ∃ r : ℂ, Tendsto (fun ζ : ℂ => (ζ - s) *
        fiveTermWordResidueSum bs ℓ v₁ w
          (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ ζ)
        (𝓝[≠] s) (𝓝 r) := by
    obtain ⟨hlo, hhi, _⟩ := wordCrossed_product_poles_inside_strip h.fixedPoint
      v₁ v₂ x F hx hF hgrid s hs
    have hK : s ∉ wordCrossedKernelPoleSet (letterWord bs) τ v₁ v₂ :=
      Finset.disjoint_right.mp (wordCrossed_pole_sets_disjoint h.fixedPoint v₁ v₂ F) hs
    exact wordCrossed_residue_sum_residue_exists_at_product_pole h ℓ v₁ v₂ w x
      hβ hx₂ s hlo.le hhi.le hK
  let RP : ℂ → ℂ := fun s =>
    if hs : s ∈ wordCrossedProductPoleSet (letterWord bs) τ F then
      Classical.choose (hprod s hs) else 0
  refine ⟨RP, ?_⟩
  intro s hs
  simpa [RP, hs] using Classical.choose_spec (hprod s hs)

/-- Horizontal decay and the rectangle theorem give the difference of the two vertical
line integrals as minus `2πi` times the residue limits. -/
private lemma wordCrossed_integral_of_residue_limits {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ v₁ v₂ : ℤ) (w x β : ℝ) (F : Finset ℤ)
    (hβeq : β = -((v₁ : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
      (letterWord bs 1 0 : ℝ) +
      fiveTermLatticeArgument (letterWord bs) τ v₁ v₂))
    (hβ : β < x)
    (hx₂ : x < β +
      (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
        ((letterWord bs 1 0 : ℝ) * (finiteDilogOrder (letterWord bs) : ℝ)))
    (hx : x < fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
      (letterWord bs 1 0 : ℝ))
    (hgrid : ∀ j : ℤ, 0 ≤ j →
      ((j : ℝ) / (letterWord bs 1 0 : ℝ) < x ↔
        (j : ℝ) / (letterWord bs 1 0 : ℝ) < β))
    (hF : ∀ j : ℤ, j ∈ F ↔ 0 ≤ j ∧
      (j : ℝ) / (letterWord bs 1 0 : ℝ) < β)
    (hreg : ∀ m : FiveTermIndex (letterWord bs),
      IsFiveTermResidueCrossing (letterWord bs) τ ((m : ℕ) : ℤ)
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂)
        (x - ((m : ℕ) : ℝ) *
          fltDenominator (letterWord bs : Mat(2, ℤ)) τ / (letterWord bs 1 0 : ℝ)))
    (hupper : (fltDenominator (letterWord bs : Mat(2, ℤ)) τ)⁻¹ <
      fiveTermUpperRate (letterWord bs) ℓ w τ)
    (hlower : fiveTermLowerRate (letterWord bs) ℓ v₁ w
      (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ < 0)
    (R : ℂ → ℂ)
    (hR : ∀ s ∈ wordCrossedKernelPoleSet (letterWord bs) τ v₁ v₂ ∪
        wordCrossedProductPoleSet (letterWord bs) τ F,
      Tendsto (fun ζ : ℂ => (ζ - s) *
        fiveTermWordResidueSum bs ℓ v₁ w
          (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ ζ)
        (𝓝[≠] s) (𝓝 (R s))) :
    (∫ t : ℝ, fiveTermWordResidueSum bs ℓ v₁ w
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ ((x : ℂ) + t * I) * I) -
      (∫ t : ℝ, fiveTermWordResidueSum bs ℓ v₁ w
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ
        (((x + (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
          (letterWord bs 1 0 : ℝ) : ℝ) : ℂ) + t * I) * I) =
      -(2 * Real.pi * I) *
        ∑ s ∈ wordCrossedKernelPoleSet (letterWord bs) τ v₁ v₂ ∪
          wordCrossedProductPoleSet (letterWord bs) τ F, R s := by
  have hβ' : -((v₁ : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
      (letterWord bs 1 0 : ℝ) +
      fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) < x := by
    simpa only [hβeq] using hβ
  have hx₂' : x < -((v₁ : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
      (letterWord bs 1 0 : ℝ) +
      fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) +
      (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
        ((letterWord bs 1 0 : ℝ) * (finiteDilogOrder (letterWord bs) : ℝ)) := by
    simpa only [hβeq] using hx₂
  let L : ℂ → ℂ := fiveTermWordResidueSum bs ℓ v₁ w
    (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ
  let b : ℝ := x + (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
    (letterWord bs 1 0 : ℝ)
  have hright (m : FiveTermIndex (letterWord bs)) :
      IsFiveTermResidueCrossing (letterWord bs) τ ((m : ℕ) : ℤ)
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂)
        (b - ((m : ℕ) : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
          (letterWord bs 1 0 : ℝ)) :=
    fiveTerm_strip_right_crossing h v₁ v₂ x hreg m
  have hintleft := integrable_fiveTermWordResidueSum h ℓ v₁ w
    (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) x hreg hupper hlower
  have hintright := integrable_fiveTermWordResidueSum h ℓ v₁ w
    (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) b hright hupper hlower
  have hbottom := tendsto_intervalIntegral_fiveTermWordResidueSum_lower h ℓ v₁ w
    (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) x b hlower
  have htop := tendsto_intervalIntegral_fiveTermWordResidueSum_upper h ℓ v₁ w
    (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) x b hupper
  have hrect : ∀ᶠ Y : ℝ in atTop,
      (∫ t : ℝ in x..b, L ((t : ℂ) + (-Y) * I)) -
      (∫ t : ℝ in x..b, L ((t : ℂ) + Y * I)) +
      I • (∫ t : ℝ in -Y..Y, L ((b : ℂ) + t * I)) -
      I • (∫ t : ℝ in -Y..Y, L ((x : ℂ) + t * I)) =
        2 * Real.pi * I *
          ∑ s ∈ wordCrossedKernelPoleSet (letterWord bs) τ v₁ v₂ ∪
            wordCrossedProductPoleSet (letterWord bs) τ F, R s := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
    simpa only [L, b] using wordCrossed_rectangle_identity_of_residue_limits
      h ℓ v₁ v₂ w x β F hβeq hβ' hx₂' hx hgrid hF hreg R hR Y hY
  simpa only [L, b] using integral_vertical_sub_eq_neg_residue_of_rectangle
    L x b (∑ s ∈ wordCrossedKernelPoleSet (letterWord bs) τ v₁ v₂ ∪
      wordCrossedProductPoleSet (letterWord bs) τ F, R s)
    hintleft hintright hbottom htop hrect

/-- The crossed-strip integral difference equals the negative `2πi` multiple of the
kernel-window residues plus the numerator product-pole residues. -/
private lemma wordCrossed_strip_residue_identity {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ v₁ v₂ : ℤ) (w x β : ℝ) (F : Finset ℤ)
    (hβeq : β = -((v₁ : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
      (letterWord bs 1 0 : ℝ) +
      fiveTermLatticeArgument (letterWord bs) τ v₁ v₂))
    (hβ : β < x)
    (hx₂ : x < β +
      (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
        ((letterWord bs 1 0 : ℝ) * (finiteDilogOrder (letterWord bs) : ℝ)))
    (hx : x < fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
      (letterWord bs 1 0 : ℝ))
    (hgrid : ∀ j : ℤ, 0 ≤ j →
      ((j : ℝ) / (letterWord bs 1 0 : ℝ) < x ↔
        (j : ℝ) / (letterWord bs 1 0 : ℝ) < β))
    (hF : ∀ j : ℤ, j ∈ F ↔ 0 ≤ j ∧
      (j : ℝ) / (letterWord bs 1 0 : ℝ) < β)
    (hreg : ∀ m : FiveTermIndex (letterWord bs),
      IsFiveTermResidueCrossing (letterWord bs) τ ((m : ℕ) : ℤ)
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂)
        (x - ((m : ℕ) : ℝ) *
          fltDenominator (letterWord bs : Mat(2, ℤ)) τ / (letterWord bs 1 0 : ℝ)))
    (hupper : (fltDenominator (letterWord bs : Mat(2, ℤ)) τ)⁻¹ <
      fiveTermUpperRate (letterWord bs) ℓ w τ)
    (hlower : fiveTermLowerRate (letterWord bs) ℓ v₁ w
      (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ < 0) :
    ∃ RP : ℂ → ℂ,
      (∀ s ∈ wordCrossedProductPoleSet (letterWord bs) τ F,
        Tendsto (fun ζ : ℂ => (ζ - s) *
          fiveTermWordResidueSum bs ℓ v₁ w
            (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ ζ)
          (𝓝[≠] s) (𝓝 (RP s))) ∧
      ((∫ t : ℝ, fiveTermWordResidueSum bs ℓ v₁ w
          (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ
          ((x : ℂ) + t * I) * I) -
        (∫ t : ℝ, fiveTermWordResidueSum bs ℓ v₁ w
          (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ
          (((x + (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
            (letterWord bs 1 0 : ℝ) : ℝ) : ℂ) + t * I) * I)) =
        -(2 * Real.pi * I) *
          ((∑ mk ∈ fiveTermWindow (letterWord bs)
              (-(finiteDilogOrder (letterWord bs) : ℤ) -
                fiveTermLatticeIndex (letterWord bs) v₁ v₂),
              fiveTermWordKernelResidue bs ℓ v₁ w
                (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ mk.1
                (fiveTermLatticeArgument (letterWord bs) τ mk.1 mk.2)) +
            ∑ s ∈ wordCrossedProductPoleSet (letterWord bs) τ F, RP s) := by
  have hβ' : -((v₁ : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
      (letterWord bs 1 0 : ℝ) +
      fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) < x := by
    simpa only [hβeq] using hβ
  have hx₂' : x < -((v₁ : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
      (letterWord bs 1 0 : ℝ) +
      fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) +
      (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
        ((letterWord bs 1 0 : ℝ) * (finiteDilogOrder (letterWord bs) : ℝ)) := by
    simpa only [hβeq] using hx₂
  obtain ⟨RP, hRP⟩ := wordCrossed_product_residue_limits h ℓ v₁ v₂ w x F
    hβ' hx₂' hx (by simpa only [hβeq] using hF)
    (by simpa only [hβeq] using hgrid)
  let R : ℂ → ℂ := fun s =>
    if s ∈ wordCrossedKernelPoleSet (letterWord bs) τ v₁ v₂ then
      ∑ m : FiveTermIndex (letterWord bs),
        wordCrossedResidueFiber bs τ ℓ v₁ v₂ w m s else RP s
  have hR (s : ℂ)
      (hs : s ∈ wordCrossedKernelPoleSet (letterWord bs) τ v₁ v₂ ∪
        wordCrossedProductPoleSet (letterWord bs) τ F) :
      Tendsto (fun ζ : ℂ => (ζ - s) *
        fiveTermWordResidueSum bs ℓ v₁ w
          (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ ζ)
        (𝓝[≠] s) (𝓝 (R s)) := by
    by_cases hsK : s ∈ wordCrossedKernelPoleSet (letterWord bs) τ v₁ v₂
    · simpa [R, hsK] using
        wordCrossed_residue_sum_residue_fibers_at_kernel_pole h ℓ v₁ v₂ w x β F
          hβ' hx₂' hx hgrid hF hreg s hsK
    · have hsP := (Finset.mem_union.mp hs).resolve_left hsK
      simpa [R, hsK] using hRP s hsP
  have hlim := wordCrossed_integral_of_residue_limits h ℓ v₁ v₂ w x β F
    hβeq hβ hx₂ hx hgrid hF hreg hupper hlower R hR
  have hsum : (∑ s ∈ wordCrossedKernelPoleSet (letterWord bs) τ v₁ v₂ ∪
      wordCrossedProductPoleSet (letterWord bs) τ F, R s) =
      (∑ mk ∈ fiveTermWindow (letterWord bs)
          (-(finiteDilogOrder (letterWord bs) : ℤ) -
            fiveTermLatticeIndex (letterWord bs) v₁ v₂),
          fiveTermWordKernelResidue bs ℓ v₁ w
            (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ mk.1
            (fiveTermLatticeArgument (letterWord bs) τ mk.1 mk.2)) +
        ∑ s ∈ wordCrossedProductPoleSet (letterWord bs) τ F, RP s := by
    rw [Finset.sum_union (wordCrossed_pole_sets_disjoint h.fixedPoint v₁ v₂ F)]
    have hK : (∑ s ∈ wordCrossedKernelPoleSet (letterWord bs) τ v₁ v₂, R s) =
        ∑ s ∈ wordCrossedKernelPoleSet (letterWord bs) τ v₁ v₂,
          ∑ m : FiveTermIndex (letterWord bs),
            wordCrossedResidueFiber bs τ ℓ v₁ v₂ w m s := by
      apply Finset.sum_congr rfl
      intro s hs
      simp [R, hs]
    have hP : (∑ s ∈ wordCrossedProductPoleSet (letterWord bs) τ F, R s) =
        ∑ s ∈ wordCrossedProductPoleSet (letterWord bs) τ F, RP s := by
      apply Finset.sum_congr rfl
      intro s hs
      have hnot := Finset.disjoint_right.mp
        (wordCrossed_pole_sets_disjoint h.fixedPoint v₁ v₂ F) hs
      simp [R, hnot]
    rw [hK, hP, wordCrossed_residue_fibers_total h]
  refine ⟨RP, hRP, ?_⟩
  simpa only [hsum] using hlim

/-! ### Crossed-square corrections

The telescoping germ subtracts the residue limits of the two translated residue sums. The
positive squares cancel the product-pole residues, while the square at zero retains the
difference between the zero and width kernel fibers. -/

/-- The telescoping germ subtracts the residue limits of the two shifted residue sums. -/
private lemma wordCrossed_difference_residue_limit {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ p : ℤ) (w y : ℝ)
    (hw : Complex.exp (2 * Real.pi * I *
        ((w : ℂ) / fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ))) =
      Complex.exp (2 * Real.pi * I * ((w : ℂ) + (ℓ - 1) * (τ : ℂ))))
    (hy : Complex.exp (2 * Real.pi * I *
        ((y : ℂ) / fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ))) =
      Complex.exp (2 * Real.pi * I * ((y : ℂ) + p * (τ : ℂ))))
    (s A B : ℂ)
    (hA : Tendsto (fun ζ : ℂ => (ζ - s) *
      fiveTermWordResidueSum bs ℓ p w y τ ζ) (𝓝[≠] s) (𝓝 A))
    (hB : Tendsto (fun ζ : ℂ =>
      (ζ - (s + (fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) - 1) /
        (letterWord bs 1 0 : ℂ))) *
        fiveTermWordResidueSum bs ℓ p w y τ ζ)
      (𝓝[≠] (s + (fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) - 1) /
        (letterWord bs 1 0 : ℂ))) (𝓝 B)) :
    Tendsto (fun ζ : ℂ => (ζ - s) * fiveTermWordDifferenceSum bs ℓ p w y τ ζ)
      (𝓝[≠] s) (𝓝 (A - B)) := by
  let Δ : ℂ := (fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) - 1) /
    (letterWord bs 1 0 : ℂ)
  let L : ℂ → ℂ := fiveTermWordResidueSum bs ℓ p w y τ
  let J : ℂ → ℂ := fiveTermWordDifferenceSum bs ℓ p w y τ
  have hshift : Tendsto (fun ζ : ℂ => (ζ - s) * L (ζ + Δ))
      (𝓝[≠] s) (𝓝 B) := by
    have ht := hB.comp (tendsto_add_const_nhdsNE Δ s)
    convert ht using 1
    funext ζ
    simp only [L, Δ, Function.comp_def]
    ring
  have hdiff := hA.sub hshift
  have hdiff' : Tendsto (fun ζ : ℂ => (ζ - s) * (L ζ - L (ζ + Δ)))
      (𝓝[≠] s) (𝓝 (A - B)) := by
    convert hdiff using 1
    funext ζ
    ring
  have hEq := fiveTermWordResidueSum_sub_shift_eventuallyEq h ℓ p w y hw hy s
  have hEqMul : (fun ζ : ℂ => (ζ - s) * (L ζ - L (ζ + Δ))) =ᶠ[𝓝[≠] s]
      (fun ζ => (ζ - s) * J ζ) := by
    filter_upwards [hEq] with ζ hζ
    exact congrArg ((ζ - s) * ·) hζ
  exact hdiff'.congr' hEqMul

/-- The telescoping germ makes the difference sum meromorphic at every square center. -/
private lemma wordCrossed_difference_meromorphicAt {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ p : ℤ) (w y : ℝ)
    (hw : Complex.exp (2 * Real.pi * I *
        ((w : ℂ) / fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ))) =
      Complex.exp (2 * Real.pi * I * ((w : ℂ) + (ℓ - 1) * (τ : ℂ))))
    (hy : Complex.exp (2 * Real.pi * I *
        ((y : ℂ) / fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ))) =
      Complex.exp (2 * Real.pi * I * ((y : ℂ) + p * (τ : ℂ))))
    (s : ℂ) : MeromorphicAt (fiveTermWordDifferenceSum bs ℓ p w y τ) s := by
  let Δ : ℂ := (fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) - 1) /
    (letterWord bs 1 0 : ℂ)
  let L : ℂ → ℂ := fiveTermWordResidueSum bs ℓ p w y τ
  have hL := meromorphic_fiveTermWordResidueSum h ℓ p w y s
  have hLshift : MeromorphicAt (fun ζ => L (ζ + Δ)) s := by
    change MeromorphicAt (L ∘ fun ζ => ζ + Δ) s
    apply (meromorphicAt_comp_add_const_iff_meromorphicAt).2
    exact meromorphic_fiveTermWordResidueSum h ℓ p w y (s + Δ)
  have hEq := fiveTermWordResidueSum_sub_shift_eventuallyEq h ℓ p w y hw hy s
  exact (hL.sub hLshift).congr hEq

/-- Below the strip width, the word-product numerator has nonnegative order. -/
private lemma wordCrossed_numerator_order_nonneg_below_width {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (m : ℤ) (z : ℂ)
    (hz : z.re ≤ (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
      (letterWord bs 1 0 : ℝ)) :
    0 ≤ meromorphicOrderAt (fun ζ => faddeevWord bs m 0 ζ τ)
      (z - (m : ℂ) * fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
        (letterWord bs 1 0 : ℂ)) := by
  by_contra hn
  have hneg : meromorphicOrderAt (fun ζ => faddeevWord bs m 0 ζ τ)
      (z - (m : ℂ) * fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
        (letterWord bs 1 0 : ℂ)) < 0 := by simpa only [not_le] using hn
  have hε : (0 : ℝ) < fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
      (letterWord bs 1 0 : ℝ) :=
    div_pos h.fixedPoint.fltDenominator_pos
      (by exact_mod_cast h.fixedPoint.lowerLeft_pos)
  obtain ⟨j, hj, _, hjx⟩ := wordCrossed_raw_numerator_pole_location h m z 0
    hε (by simpa only [zero_add] using hz) hneg
  have hjR : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hc : (0 : ℝ) < (letterWord bs 1 0 : ℝ) := by
    exact_mod_cast h.fixedPoint.lowerLeft_pos
  have hdiv : (0 : ℝ) < (j : ℝ) / (letterWord bs 1 0 : ℝ) :=
    div_pos hjR hc
  linarith

/-- The residue sum has zero residue limit at a positive rational grid point below the
strip width. -/
private lemma wordCrossed_residue_sum_residue_zero_at_rational {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ v₁ v₂ : ℤ) (w : ℝ) (j : ℤ)
    (hj : 0 < j)
    (hjδ : (j : ℝ) / (letterWord bs 1 0 : ℝ) ≤
      (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
        (letterWord bs 1 0 : ℝ))
    (hv : 1 ≤ fiveTermLatticeIndex (letterWord bs) v₁ v₂) :
    Tendsto (fun ζ : ℂ => (ζ - ((j : ℂ) / (letterWord bs 1 0 : ℂ))) *
      fiveTermWordResidueSum bs ℓ v₁ w
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ ζ)
      (𝓝[≠] ((j : ℂ) / (letterWord bs 1 0 : ℂ))) (𝓝 0) := by
  let s : ℂ := (j : ℂ) / (letterWord bs 1 0 : ℂ)
  have ht (m : FiveTermIndex (letterWord bs)) :
      Tendsto (fun ζ : ℂ => (ζ - s) *
        fiveTermWordResidueKernel bs ℓ v₁ w
          (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ ((m : ℕ) : ℤ)
          (ζ - ((m : ℕ) : ℂ) *
            fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
              (letterWord bs 1 0 : ℂ))) (𝓝[≠] s) (𝓝 0) := by
    have hnot : ∀ k : ℤ,
        s ≠ fiveTermStripPolePosition (letterWord bs) τ ((m : ℕ) : ℤ) k := by
      intro k heq
      apply wordCrossed_kernel_position_ne_rational h.fixedPoint ((m : ℕ) : ℤ) k j hj
      calc
        fiveTermStripPolePosition (letterWord bs) τ ((m : ℕ) : ℤ) k = s := heq.symm
        _ = (((j : ℝ) / (letterWord bs 1 0 : ℝ)) : ℂ) := by dsimp [s]
    have hnum : 0 ≤ meromorphicOrderAt
      (fun ζ => faddeevWord bs ((m : ℕ) : ℤ) 0 ζ τ)
      (s - ((m : ℕ) : ℂ) *
        fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
          (letterWord bs 1 0 : ℂ)) := by
      apply wordCrossed_numerator_order_nonneg_below_width h
      have hsre : s.re = (j : ℝ) / (letterWord bs 1 0 : ℝ) := by
        dsimp [s]
        norm_cast
      rw [hsre]
      exact hjδ
    have hden := wordCrossed_denominator_order_nonpos_at_rational h
      ((m : ℕ) : ℤ) v₁ v₂ j hj.le hv
    exact wordCrossed_shifted_term_residue_zero h ℓ v₁ v₂ w m s hnot hnum hden
  have hsum := tendsto_finsetSum Finset.univ (fun m _ => ht m)
  convert hsum using 1
  · funext ζ
    simp only [s, fiveTermWordResidueSum, Finset.mul_sum]
  · simp

/-- A positive crossed square cancels its paired numerator product-pole residue. -/
private lemma wordCrossed_positive_square_correction {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ v₁ v₂ : ℤ) (w : ℝ)
    (F : Finset ℤ) (j : ℤ) (hjF : j ∈ F) (hj : 0 < j)
    (hjδ : (j : ℝ) / (letterWord bs 1 0 : ℝ) ≤
      (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
        (letterWord bs 1 0 : ℝ))
    (hv : 1 ≤ fiveTermLatticeIndex (letterWord bs) v₁ v₂)
    (hw : Complex.exp (2 * Real.pi * I *
        ((w : ℂ) / fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ))) =
      Complex.exp (2 * Real.pi * I * ((w : ℂ) + (ℓ - 1) * (τ : ℂ))))
    (hy : Complex.exp (2 * Real.pi * I *
        ((fiveTermLatticeArgument (letterWord bs) τ v₁ v₂ : ℂ) /
          fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ))) =
      Complex.exp (2 * Real.pi * I *
        ((fiveTermLatticeArgument (letterWord bs) τ v₁ v₂ : ℂ) + v₁ * (τ : ℂ))))
    (RP : ℂ → ℂ)
    (hRP : ∀ s ∈ wordCrossedProductPoleSet (letterWord bs) τ F,
      Tendsto (fun ζ : ℂ => (ζ - s) *
        fiveTermWordResidueSum bs ℓ v₁ w
          (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ ζ)
        (𝓝[≠] s) (𝓝 (RP s))) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      rectBoundaryIntegral
        (fiveTermWordDifferenceSum bs ℓ v₁ w
          (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ)
        ((j : ℂ) / (letterWord bs 1 0 : ℂ) - (r + r * I))
        ((j : ℂ) / (letterWord bs 1 0 : ℂ) + (r + r * I)) =
      -(2 * Real.pi * I) *
        RP (((fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
          (letterWord bs 1 0 : ℝ) +
          (j : ℝ) / (letterWord bs 1 0 : ℝ)) : ℂ) := by
  let s : ℂ := (j : ℂ) / (letterWord bs 1 0 : ℂ)
  let Δ : ℂ := (fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) - 1) /
    (letterWord bs 1 0 : ℂ)
  have hp : s + Δ ∈ wordCrossedProductPoleSet (letterWord bs) τ F := by
    apply Finset.mem_image.mpr
    refine ⟨j, Finset.mem_filter.mpr ⟨hjF, hj⟩, ?_⟩
    dsimp [s, Δ]
    norm_cast
    ring
  have hA := wordCrossed_residue_sum_residue_zero_at_rational h ℓ v₁ v₂ w j
    hj hjδ hv
  have hB := hRP (s + Δ) hp
  have hJres : Tendsto (fun ζ : ℂ => (ζ - s) *
      fiveTermWordDifferenceSum bs ℓ v₁ w
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ ζ)
      (𝓝[≠] s) (𝓝 (-RP (s + Δ))) := by
    simpa only [zero_sub] using
      wordCrossed_difference_residue_limit h ℓ v₁ w
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) hw hy s 0 (RP (s + Δ))
        (by simpa only [s] using hA) (by simpa only [Δ] using hB)
  have hJmer := wordCrossed_difference_meromorphicAt h ℓ v₁ w
    (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) hw hy s
  have hsquare := eventually_rectBoundaryIntegral_square_eq_residue hJmer hJres
  have heq : (((fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
      (letterWord bs 1 0 : ℝ) +
      (j : ℝ) / (letterWord bs 1 0 : ℝ)) : ℂ) = s + Δ := by
    dsimp [s, Δ]
    norm_cast
    ring
  simpa only [heq, s, mul_neg, neg_mul] using hsquare

/-- The sum of kernel residues over all source-index fibers at a fixed position. -/
private def wordCrossedResidueAtPosition (bs : List ℤ) (τ : ℝ)
    (ℓ v₁ v₂ : ℤ) (w : ℝ) (s : ℂ) : ℂ := by
  classical
  exact ∑ m : FiveTermIndex (letterWord bs),
    if h : ∃ k : ℤ,
      s = fiveTermStripPolePosition (letterWord bs) τ ((m : ℕ) : ℤ) k then
      fiveTermWordKernelResidue bs ℓ v₁ w
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ ((m : ℕ) : ℤ)
        (s - ((m : ℕ) : ℂ) *
          fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
            (letterWord bs 1 0 : ℂ))
    else 0

/-- At a special position below the strip width, the residue-sum limit is the sum of its
kernel fibers. -/
private lemma wordCrossed_residue_sum_limit_at_special_position {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ v₁ v₂ : ℤ) (w : ℝ) (s : ℂ)
    (hs : s.re ≤ (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
      (letterWord bs 1 0 : ℝ))
    (hden : ∀ m : FiveTermIndex (letterWord bs),
      meromorphicOrderAt
        (fun ζ : ℂ => faddeevWord bs (((m : ℕ) : ℤ) + v₁) 0
          (ζ + fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ)
        (s - ((m : ℕ) : ℂ) *
          fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
            (letterWord bs 1 0 : ℂ)) ≤ 0) :
    Tendsto (fun ζ : ℂ => (ζ - s) *
      fiveTermWordResidueSum bs ℓ v₁ w
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ ζ)
      (𝓝[≠] s) (𝓝 (wordCrossedResidueAtPosition bs τ ℓ v₁ v₂ w s)) := by
  classical
  have ht (m : FiveTermIndex (letterWord bs)) :
      Tendsto (fun ζ : ℂ => (ζ - s) *
        fiveTermWordResidueKernel bs ℓ v₁ w
          (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ ((m : ℕ) : ℤ)
          (ζ - ((m : ℕ) : ℂ) *
            fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
              (letterWord bs 1 0 : ℂ))) (𝓝[≠] s)
        (𝓝 (if h : ∃ k : ℤ,
          s = fiveTermStripPolePosition (letterWord bs) τ ((m : ℕ) : ℤ) k then
            fiveTermWordKernelResidue bs ℓ v₁ w
              (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ ((m : ℕ) : ℤ)
              (s - ((m : ℕ) : ℂ) *
                fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
                  (letterWord bs 1 0 : ℂ))
          else 0)) := by
    split_ifs with hp
    · obtain ⟨k, hk⟩ := hp
      have hlim := tendsto_sub_mul_fiveTermWordResidueKernel_sub h ℓ w
        ((m : ℕ) : ℤ) k v₁ v₂
      rw [hk]
      convert hlim using 1
      dsimp [fiveTermStripPolePosition]
      norm_cast
      ring_nf
    · have hnot : ∀ k : ℤ,
          s ≠ fiveTermStripPolePosition (letterWord bs) τ ((m : ℕ) : ℤ) k := by
        simpa only [not_exists] using hp
      have hnum := wordCrossed_numerator_order_nonneg_below_width h
        ((m : ℕ) : ℤ) s hs
      exact wordCrossed_shifted_term_residue_zero h ℓ v₁ v₂ w m s hnot hnum (hden m)
  have hsum := tendsto_finsetSum Finset.univ (fun m _ => ht m)
  unfold wordCrossedResidueAtPosition
  convert hsum using 1
  funext ζ
  simp only [fiveTermWordResidueSum, Finset.mul_sum]

/-- The residue-sum limit at zero is its kernel-fiber sum. -/
private lemma wordCrossed_residue_sum_limit_at_zero {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ v₁ v₂ : ℤ) (w : ℝ)
    (hv : 1 ≤ fiveTermLatticeIndex (letterWord bs) v₁ v₂) :
    Tendsto (fun ζ : ℂ => ζ *
      fiveTermWordResidueSum bs ℓ v₁ w
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ ζ)
      (𝓝[≠] 0) (𝓝 (wordCrossedResidueAtPosition bs τ ℓ v₁ v₂ w 0)) := by
  have hδ : (0 : ℝ) ≤ (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
      (letterWord bs 1 0 : ℝ) :=
    (div_pos (sub_pos.mpr h.fixedPoint.one_lt_fltDenominator)
      (by exact_mod_cast h.fixedPoint.lowerLeft_pos)).le
  have hden (m : FiveTermIndex (letterWord bs)) :
      meromorphicOrderAt
        (fun ζ : ℂ => faddeevWord bs (((m : ℕ) : ℤ) + v₁) 0
          (ζ + fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ)
        (0 - ((m : ℕ) : ℂ) *
          fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
            (letterWord bs 1 0 : ℂ)) ≤ 0 := by
    convert wordCrossed_denominator_order_nonpos_at_rational h
      ((m : ℕ) : ℤ) v₁ v₂ 0 (by omega) hv using 1
    push_cast
    ring_nf
  simpa only [sub_zero, Complex.zero_re] using
    wordCrossed_residue_sum_limit_at_special_position h ℓ v₁ v₂ w 0 hδ hden

/-- The residue-sum limit at one strip width is its kernel-fiber sum. -/
private lemma wordCrossed_residue_sum_limit_at_width {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ v₁ v₂ : ℤ) (w : ℝ)
    (hv : fiveTermLatticeIndex (letterWord bs) v₁ v₂ ≤
      finiteDilogOrder (letterWord bs)) :
    let δ : ℝ := (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
      (letterWord bs 1 0 : ℝ)
    Tendsto (fun ζ : ℂ => (ζ - (δ : ℂ)) *
      fiveTermWordResidueSum bs ℓ v₁ w
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ ζ)
      (𝓝[≠] (δ : ℂ))
      (𝓝 (wordCrossedResidueAtPosition bs τ ℓ v₁ v₂ w (δ : ℂ))) := by
  dsimp
  let δ : ℝ := (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
    (letterWord bs 1 0 : ℝ)
  have hβ : -((v₁ : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
      (letterWord bs 1 0 : ℝ) +
      fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) ≤ δ := by
    dsimp [δ]
    rw [wordCrossed_beta_eq_spacing_index h.fixedPoint v₁ v₂,
      wordCrossed_width_eq_spacing_mul_order h.fixedPoint]
    have hvR : (fiveTermLatticeIndex (letterWord bs) v₁ v₂ : ℝ) ≤
        (finiteDilogOrder (letterWord bs) : ℝ) := by exact_mod_cast hv
    exact mul_le_mul_of_nonneg_left hvR (wordCrossed_spacing_pos h.fixedPoint).le
  have hden (m : FiveTermIndex (letterWord bs)) :
      meromorphicOrderAt
        (fun ζ : ℂ => faddeevWord bs (((m : ℕ) : ℤ) + v₁) 0
          (ζ + fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ)
        ((δ : ℂ) - ((m : ℕ) : ℂ) *
          fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
            (letterWord bs 1 0 : ℂ)) ≤ 0 := by
    apply meromorphicOrderAt_faddeevWord_denominator_nonpos h
    have hre : ((δ : ℂ) - ((m : ℕ) : ℂ) *
        fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
          (letterWord bs 1 0 : ℂ)).re =
        δ - ((m : ℕ) : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
          (letterWord bs 1 0 : ℝ) := by norm_cast
    rw [hre]
    have hsum : (-((((m : ℕ) : ℤ) + v₁ : ℤ) : ℝ)) *
        fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
        (letterWord bs 1 0 : ℝ) -
        fiveTermLatticeArgument (letterWord bs) τ v₁ v₂ =
        -((v₁ : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
          (letterWord bs 1 0 : ℝ) +
          fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) -
          ((m : ℕ) : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
            (letterWord bs 1 0 : ℝ) := by
      push_cast
      ring
    rw [hsum]
    dsimp [δ]
    linarith
  have hs : (δ : ℂ).re ≤ (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
      (letterWord bs 1 0 : ℝ) := by dsimp [δ]; norm_cast
  exact wordCrossed_residue_sum_limit_at_special_position h ℓ v₁ v₂ w
    (δ : ℂ) hs hden

/-- The zero square integral is `2πi` times the residue difference at zero and at one strip
width. -/
private lemma wordCrossed_zero_square_correction {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ v₁ v₂ : ℤ) (w : ℝ)
    (hv₁ : 1 ≤ fiveTermLatticeIndex (letterWord bs) v₁ v₂)
    (hv₂ : fiveTermLatticeIndex (letterWord bs) v₁ v₂ ≤
      finiteDilogOrder (letterWord bs))
    (hw : Complex.exp (2 * Real.pi * I *
        ((w : ℂ) / fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ))) =
      Complex.exp (2 * Real.pi * I * ((w : ℂ) + (ℓ - 1) * (τ : ℂ))))
    (hy : Complex.exp (2 * Real.pi * I *
        ((fiveTermLatticeArgument (letterWord bs) τ v₁ v₂ : ℂ) /
          fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ))) =
      Complex.exp (2 * Real.pi * I *
        ((fiveTermLatticeArgument (letterWord bs) τ v₁ v₂ : ℂ) + v₁ * (τ : ℂ)))) :
    let δ : ℝ := (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
      (letterWord bs 1 0 : ℝ)
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      rectBoundaryIntegral
        (fiveTermWordDifferenceSum bs ℓ v₁ w
          (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ)
        (-(r + r * I)) (r + r * I) =
      2 * Real.pi * I *
        (wordCrossedResidueAtPosition bs τ ℓ v₁ v₂ w 0 -
          wordCrossedResidueAtPosition bs τ ℓ v₁ v₂ w (δ : ℂ)) := by
  dsimp
  let δR : ℝ := (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
    (letterWord bs 1 0 : ℝ)
  let δ : ℂ := (fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) - 1) /
    (letterWord bs 1 0 : ℂ)
  have hA := wordCrossed_residue_sum_limit_at_zero h ℓ v₁ v₂ w hv₁
  have hB := wordCrossed_residue_sum_limit_at_width h ℓ v₁ v₂ w hv₂
  change Tendsto (fun ζ : ℂ => (ζ - (δR : ℂ)) *
      fiveTermWordResidueSum bs ℓ v₁ w
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ ζ)
      (𝓝[≠] (δR : ℂ))
      (𝓝 (wordCrossedResidueAtPosition bs τ ℓ v₁ v₂ w (δR : ℂ))) at hB
  have hδ : (δR : ℂ) = δ := by dsimp [δR, δ]; norm_cast
  rw [hδ] at hB
  have hB' : Tendsto (fun ζ : ℂ => (ζ - δ) *
      fiveTermWordResidueSum bs ℓ v₁ w
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ ζ)
      (𝓝[≠] δ) (𝓝 (wordCrossedResidueAtPosition bs τ ℓ v₁ v₂ w δ)) := hB
  have hJres := wordCrossed_difference_residue_limit h ℓ v₁ w
    (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) hw hy 0
    (wordCrossedResidueAtPosition bs τ ℓ v₁ v₂ w 0)
    (wordCrossedResidueAtPosition bs τ ℓ v₁ v₂ w δ)
    (by simpa only [sub_zero] using hA)
    (by simpa only [zero_add] using hB')
  have hJmer := wordCrossed_difference_meromorphicAt h ℓ v₁ w
    (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) hw hy 0
  have hsquare := eventually_rectBoundaryIntegral_square_eq_residue hJmer hJres
  change ∀ᶠ r : ℝ in 𝓝[>] 0,
    rectBoundaryIntegral
      (fiveTermWordDifferenceSum bs ℓ v₁ w
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ)
      (-(r + r * I)) (r + r * I) =
      2 * Real.pi * I *
        (wordCrossedResidueAtPosition bs τ ℓ v₁ v₂ w 0 -
          wordCrossedResidueAtPosition bs τ ℓ v₁ v₂ w (δR : ℂ))
  rw [hδ]
  simpa only [zero_sub, zero_add] using hsquare

/-! ### Finite value comparison

The negative window has `F⁻` in both factors. The two special fibers change the numerator
zero class to `E(0)`, yielding the finite group sum. -/

/-- Residues in the negative crossed window have `F⁻` numerator and denominator values.
Used by `integral_fiveTermWordResidueSum_of_crossed`. -/
private lemma wordCrossed_window_kernel_residue_type {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (u₁ u₂ v₁ v₂ : ℤ)
    (hv : 1 ≤ fiveTermLatticeIndex (letterWord bs) v₁ v₂)
    (mk : ℤ × ℤ)
    (hmk : mk ∈ fiveTermWindow (letterWord bs)
      (-finiteDilogOrder (letterWord bs) - fiveTermLatticeIndex (letterWord bs) v₁ v₂)) :
    fiveTermWordKernelResidue bs (u₁ + 1) v₁
      (fiveTermLatticeArgument (letterWord bs) τ u₁ u₂)
      (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ mk.1
      (fiveTermLatticeArgument (letterWord bs) τ mk.1 mk.2) =
    fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
      (2 * Real.pi * I * (1 - fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ))) *
      fixedBicharacter (letterWord bs) (finiteDilogOrder (letterWord bs))
        (fiveTermCharacteristicResidue (letterWord bs) mk.1 mk.2)
        (fiveTermCharacteristicResidue (letterWord bs) u₁ u₂) *
      (finiteDilogEMinus (letterWord bs) τ
          (fiveTermCharacteristicResidue (letterWord bs) mk.1 mk.2) /
        finiteDilogEMinus (letterWord bs) τ
          (fiveTermCharacteristicResidue (letterWord bs) mk.1 mk.2 +
            fiveTermCharacteristicResidue (letterWord bs) v₁ v₂)) := by
  obtain ⟨_, _, hlo, hhi⟩ :=
    (mem_fiveTermWindow h.fixedPoint _ mk).mp hmk
  have hS : fiveTermLatticeIndex (letterWord bs) mk.1 mk.2 < 0 := by omega
  have hSv : fiveTermLatticeIndex (letterWord bs) (mk.1 + v₁) (mk.2 + v₂) < 0 := by
    rw [fiveTermLatticeIndex_add]
    omega
  rw [fiveTermWordKernelResidue_eq_of_types h mk.1 mk.2 u₁ u₂ v₁ v₂]
  simp only [not_le.mpr hS, not_le.mpr hSv, ↓reduceIte]
  rw [fiveTermCharacteristicResidue_add]

/-- Summing the negative window gives the finite group sum with `F⁻` numerator values.
Used by `integral_fiveTermWordResidueSum_of_crossed`. -/
private lemma wordCrossed_window_residue_sum_eq {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) [NeZero (finiteDilogOrder (letterWord bs))]
    (u₁ u₂ v₁ v₂ : ℤ)
    (hv : 1 ≤ fiveTermLatticeIndex (letterWord bs) v₁ v₂) :
    (∑ mk ∈ fiveTermWindow (letterWord bs)
        (-finiteDilogOrder (letterWord bs) - fiveTermLatticeIndex (letterWord bs) v₁ v₂),
      fiveTermWordKernelResidue bs (u₁ + 1) v₁
        (fiveTermLatticeArgument (letterWord bs) τ u₁ u₂)
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ mk.1
        (fiveTermLatticeArgument (letterWord bs) τ mk.1 mk.2)) =
      fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
        (2 * Real.pi * I * (1 - fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ))) *
        ∑ g : finiteDilogGroup (letterWord bs),
          fixedBicharacter (letterWord bs) (finiteDilogOrder (letterWord bs)) g
            (fiveTermCharacteristicResidue (letterWord bs) u₁ u₂) *
          (finiteDilogEMinus (letterWord bs) τ g /
            finiteDilogEMinus (letterWord bs) τ
              (g + fiveTermCharacteristicResidue (letterWord bs) v₁ v₂)) := by
  let f : (Fin 2 → ZMod (finiteDilogOrder (letterWord bs))) → ℂ := fun g =>
    fixedBicharacter (letterWord bs) (finiteDilogOrder (letterWord bs)) g
      (fiveTermCharacteristicResidue (letterWord bs) u₁ u₂) *
      (finiteDilogEMinus (letterWord bs) τ g /
        finiteDilogEMinus (letterWord bs) τ
          (g + fiveTermCharacteristicResidue (letterWord bs) v₁ v₂))
  calc
    _ = ∑ mk ∈ fiveTermWindow (letterWord bs)
        (-finiteDilogOrder (letterWord bs) - fiveTermLatticeIndex (letterWord bs) v₁ v₂),
          fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
            (2 * Real.pi * I *
              (1 - fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ))) *
            f (fiveTermCharacteristicResidue (letterWord bs) mk.1 mk.2) := by
      apply Finset.sum_congr rfl
      intro mk hmk
      simpa only [f, mul_assoc] using
        wordCrossed_window_kernel_residue_type h u₁ u₂ v₁ v₂ hv mk hmk
    _ = _ := by
      rw [← Finset.mul_sum]
      rw [sum_fiveTermWindow h.fixedPoint _ f]

/-- The residue at a position is the corresponding filtered window sum when every pole at
that position belongs to the window. Used by `integral_fiveTermWordResidueSum_of_crossed`. -/
private lemma wordCrossed_residue_at_position_eq_window {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ v₁ v₂ : ℤ) (w : ℝ) (a : ℤ) (s : ℂ)
    (hmem : ∀ (m k : ℤ), 0 ≤ m → m < letterWord bs 1 0 →
      s = fiveTermStripPolePosition (letterWord bs) τ m k →
      (m, k) ∈ fiveTermWindow (letterWord bs) a) :
    wordCrossedResidueAtPosition bs τ ℓ v₁ v₂ w s =
      ∑ mk ∈ fiveTermWindow (letterWord bs) a with
        fiveTermStripPolePosition (letterWord bs) τ mk.1 mk.2 = s,
        fiveTermWordKernelResidue bs ℓ v₁ w
          (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ mk.1
          (fiveTermLatticeArgument (letterWord bs) τ mk.1 mk.2) := by
  classical
  let M : Finset (FiveTermIndex (letterWord bs)) :=
    Finset.univ.filter (fun m => ∃ k : ℤ,
      s = fiveTermStripPolePosition (letterWord bs) τ ((m : ℕ) : ℤ) k)
  have hsum : wordCrossedResidueAtPosition bs τ ℓ v₁ v₂ w s =
      ∑ m ∈ M,
        fiveTermWordKernelResidue bs ℓ v₁ w
          (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ ((m : ℕ) : ℤ)
          (s - ((m : ℕ) : ℂ) *
            fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
              (letterWord bs 1 0 : ℂ)) := by
    unfold wordCrossedResidueAtPosition M
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m _
    split_ifs <;> rfl
  rw [hsum]
  dsimp only [M]
  apply Finset.sum_bij
    (fun (m : FiveTermIndex (letterWord bs)) (hm : m ∈ M) =>
      (((m : ℕ) : ℤ), Classical.choose (Finset.mem_filter.mp hm).2))
  · intro m hm
    have hp := Classical.choose_spec (Finset.mem_filter.mp hm).2
    have hrange := fiveTermIndex_range h.fixedPoint m
    exact Finset.mem_filter.mpr ⟨hmem _ _ hrange.1 hrange.2 hp, hp.symm⟩
  · intro m hm n hn hmn
    apply Fin.ext
    have hfst := congrArg Prod.fst hmn
    dsimp at hfst
    exact_mod_cast hfst
  · intro mk hmk
    obtain ⟨hmkW, hmkP⟩ := Finset.mem_filter.mp hmk
    obtain ⟨hm0, hm1, _, _⟩ := (mem_fiveTermWindow h.fixedPoint a mk).mp hmkW
    have hc : 0 < letterWord bs 1 0 := h.fixedPoint.lowerLeft_pos
    have hlt : mk.1.toNat < (letterWord bs 1 0).toNat :=
      (Int.toNat_lt_toNat hc).2 hm1
    let m : FiveTermIndex (letterWord bs) := ⟨mk.1.toNat, hlt⟩
    have hmeq : (((m : ℕ) : ℤ)) = mk.1 := Int.toNat_of_nonneg hm0
    have hmM : m ∈ M := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, mk.2, ?_⟩
      rw [hmeq]
      exact hmkP.symm
    refine ⟨m, hmM, Prod.ext hmeq ?_⟩
    apply fiveTermStripPolePosition_injective h.fixedPoint mk.1
    have hp := Classical.choose_spec (Finset.mem_filter.mp hmM).2
    have hp' : s = fiveTermStripPolePosition (letterWord bs) τ mk.1
        (Classical.choose (Finset.mem_filter.mp hmM).2) := by
      simpa only [hmeq] using hp
    exact hp'.symm.trans hmkP.symm
  · intro m hm
    have hp := Classical.choose_spec (Finset.mem_filter.mp hm).2
    dsimp
    congr 1
    calc
      s - ((m : ℕ) : ℂ) * fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
          (letterWord bs 1 0 : ℂ) =
        fiveTermStripPolePosition (letterWord bs) τ ((m : ℕ) : ℤ)
          (Classical.choose (Finset.mem_filter.mp hm).2) -
          ((m : ℕ) : ℂ) * fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
            (letterWord bs 1 0 : ℂ) := by congr 1
      _ = _ := by
        dsimp [fiveTermStripPolePosition]
        norm_cast
        ring

/-- A common-line pole has its prescribed lattice index exactly when its position equals
the corresponding spacing multiple. Used by `integral_fiveTermWordResidueSum_of_crossed`. -/
private lemma wordCrossed_position_eq_iff_index_eq {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (m k a : ℤ) :
    fiveTermStripPolePosition γ τ m k =
        ((-(fltDenominator (γ : Mat(2, ℤ)) τ - 1) * (a : ℝ) /
          ((γ 1 0 : ℝ) * (finiteDilogOrder γ : ℝ))) : ℂ) ↔
      fiveTermLatticeIndex γ m k = a := by
  have hscale : (fltDenominator (γ : Mat(2, ℤ)) τ - 1) /
      ((γ 1 0 : ℝ) * (finiteDilogOrder γ : ℝ)) ≠ 0 :=
    ne_of_gt (wordCrossed_spacing_pos h)
  have hreal :
      fiveTermLatticeArgument γ τ m k +
        (m : ℝ) * fltDenominator (γ : Mat(2, ℤ)) τ / (γ 1 0 : ℝ) =
          -(fltDenominator (γ : Mat(2, ℤ)) τ - 1) * (a : ℝ) /
            ((γ 1 0 : ℝ) * (finiteDilogOrder γ : ℝ)) ↔
        fiveTermLatticeIndex γ m k = a := by
    rw [fiveTermLatticeArgument_add_mul_eq h]
    have hform (n : ℤ) :
        -(fltDenominator (γ : Mat(2, ℤ)) τ - 1) * (n : ℝ) /
            ((γ 1 0 : ℝ) * (finiteDilogOrder γ : ℝ)) =
          -((fltDenominator (γ : Mat(2, ℤ)) τ - 1) /
            ((γ 1 0 : ℝ) * (finiteDilogOrder γ : ℝ))) * n := by ring
    rw [hform (fiveTermLatticeIndex γ m k), hform a]
    constructor
    · intro hp
      exact_mod_cast (mul_left_cancel₀ (neg_ne_zero.mpr hscale) hp)
    · intro hp
      rw [hp]
  dsimp only [fiveTermStripPolePosition]
  exact_mod_cast hreal

/-- The residue at an exact-index position is the corresponding window fiber. Used by
`integral_fiveTermWordResidueSum_of_crossed`. -/
private lemma wordCrossed_residue_at_index_eq_window {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ v₁ v₂ : ℤ) (w : ℝ) (a : ℤ) :
    wordCrossedResidueAtPosition bs τ ℓ v₁ v₂ w
      ((-(fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) * (a : ℝ) /
        ((letterWord bs 1 0 : ℝ) * (finiteDilogOrder (letterWord bs) : ℝ))) : ℂ) =
      ∑ mk ∈ fiveTermWindow (letterWord bs) a with
        fiveTermLatticeIndex (letterWord bs) mk.1 mk.2 = a,
        fiveTermWordKernelResidue bs ℓ v₁ w
          (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ mk.1
          (fiveTermLatticeArgument (letterWord bs) τ mk.1 mk.2) := by
  have hmem (m k : ℤ)
      (hm0 : 0 ≤ m) (hm1 : m < letterWord bs 1 0)
      (hpos : ((-(fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) * (a : ℝ) /
        ((letterWord bs 1 0 : ℝ) * (finiteDilogOrder (letterWord bs) : ℝ))) : ℂ) =
          fiveTermStripPolePosition (letterWord bs) τ m k) :
      (m, k) ∈ fiveTermWindow (letterWord bs) a := by
    have hS := (wordCrossed_position_eq_iff_index_eq h.fixedPoint m k a).1 hpos.symm
    apply (mem_fiveTermWindow h.fixedPoint a (m, k)).2
    rw [hS]
    exact ⟨hm0, hm1, le_refl _, by
      have hN : (0 : ℤ) < finiteDilogOrder (letterWord bs) := by
        exact_mod_cast finiteDilogOrder_pos h.fixedPoint
      omega⟩
  rw [wordCrossed_residue_at_position_eq_window h ℓ v₁ v₂ w a _ hmem]
  simp only [wordCrossed_position_eq_iff_index_eq h.fixedPoint]

/-- The zero-position fiber has `E` values in both factors. Used by
`integral_fiveTermWordResidueSum_of_crossed`. -/
private lemma wordCrossed_residue_at_zero_eq_fiber {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (u₁ u₂ v₁ v₂ : ℤ)
    (hv : 1 ≤ fiveTermLatticeIndex (letterWord bs) v₁ v₂) :
    wordCrossedResidueAtPosition bs τ (u₁ + 1) v₁ v₂
      (fiveTermLatticeArgument (letterWord bs) τ u₁ u₂) 0 =
      fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
        (2 * Real.pi * I * (1 - fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ))) *
      ∑ mk ∈ fiveTermWindow (letterWord bs) 0 with
        fiveTermLatticeIndex (letterWord bs) mk.1 mk.2 = 0,
        fixedBicharacter (letterWord bs) (finiteDilogOrder (letterWord bs))
          (fiveTermCharacteristicResidue (letterWord bs) mk.1 mk.2)
          (fiveTermCharacteristicResidue (letterWord bs) u₁ u₂) *
        (finiteDilogE (letterWord bs) τ
            (fiveTermCharacteristicResidue (letterWord bs) mk.1 mk.2) /
          finiteDilogE (letterWord bs) τ
            (fiveTermCharacteristicResidue (letterWord bs) mk.1 mk.2 +
              fiveTermCharacteristicResidue (letterWord bs) v₁ v₂)) := by
  have hfib := wordCrossed_residue_at_index_eq_window h (u₁ + 1) v₁ v₂
    (fiveTermLatticeArgument (letterWord bs) τ u₁ u₂) 0
  have hfib0 : wordCrossedResidueAtPosition bs τ (u₁ + 1) v₁ v₂
      (fiveTermLatticeArgument (letterWord bs) τ u₁ u₂) 0 =
      ∑ mk ∈ fiveTermWindow (letterWord bs) 0 with
        fiveTermLatticeIndex (letterWord bs) mk.1 mk.2 = 0,
        fiveTermWordKernelResidue bs (u₁ + 1) v₁
          (fiveTermLatticeArgument (letterWord bs) τ u₁ u₂)
          (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ mk.1
          (fiveTermLatticeArgument (letterWord bs) τ mk.1 mk.2) := by
    simpa using hfib
  rw [hfib0, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro mk hmk
  have hS := (Finset.mem_filter.mp hmk).2
  have hSv : 0 ≤ fiveTermLatticeIndex (letterWord bs) (mk.1 + v₁) (mk.2 + v₂) := by
    rw [fiveTermLatticeIndex_add, hS]
    omega
  rw [fiveTermWordKernelResidue_eq_of_types h mk.1 mk.2 u₁ u₂ v₁ v₂]
  simp only [hS, hSv, le_refl, ↓reduceIte]
  rw [fiveTermCharacteristicResidue_add]
  ring

/-- If `0 < S(v) < N`, the denominator of the negative special fiber avoids the zero
class. Used by `integral_fiveTermWordResidueSum_of_crossed`. -/
private lemma wordCrossed_denominator_class_ne_zero {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (m k v₁ v₂ : ℤ)
    (hS : fiveTermLatticeIndex γ m k = -finiteDilogOrder γ)
    (hv : 0 < fiveTermLatticeIndex γ v₁ v₂ ∧
      fiveTermLatticeIndex γ v₁ v₂ < finiteDilogOrder γ) :
    fiveTermCharacteristicResidue γ (m + v₁) (k + v₂) ≠ 0 := by
  intro hz
  have hdiv := fiveTermLatticeIndex_dvd_of_residue_zero h (m + v₁) (k + v₂) hz
  rw [fiveTermLatticeIndex_add, hS] at hdiv
  have hVdiv : (finiteDilogOrder γ : ℤ) ∣ fiveTermLatticeIndex γ v₁ v₂ := by
    convert (dvd_refl (finiteDilogOrder γ : ℤ)).add hdiv using 1; omega
  have hzero := Int.eq_zero_of_dvd_of_nonneg_of_lt hv.1.le hv.2 hVdiv
  omega

/-- The width-position fiber has `F⁻` numerator and `E` denominator values. Used by
`integral_fiveTermWordResidueSum_of_crossed`. -/
private lemma wordCrossed_residue_at_width_eq_fiber {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (u₁ u₂ v₁ v₂ : ℤ)
    (hv : 1 ≤ fiveTermLatticeIndex (letterWord bs) v₁ v₂ ∧
      fiveTermLatticeIndex (letterWord bs) v₁ v₂ ≤ finiteDilogOrder (letterWord bs)) :
    wordCrossedResidueAtPosition bs τ (u₁ + 1) v₁ v₂
      (fiveTermLatticeArgument (letterWord bs) τ u₁ u₂)
      (((fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
        (letterWord bs 1 0 : ℝ) : ℝ) : ℂ) =
      fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
        (2 * Real.pi * I * (1 - fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ))) *
      ∑ mk ∈ fiveTermWindow (letterWord bs) (-finiteDilogOrder (letterWord bs)) with
        fiveTermLatticeIndex (letterWord bs) mk.1 mk.2 =
          -finiteDilogOrder (letterWord bs),
        fixedBicharacter (letterWord bs) (finiteDilogOrder (letterWord bs))
          (fiveTermCharacteristicResidue (letterWord bs) mk.1 mk.2)
          (fiveTermCharacteristicResidue (letterWord bs) u₁ u₂) *
        (finiteDilogEMinus (letterWord bs) τ
            (fiveTermCharacteristicResidue (letterWord bs) mk.1 mk.2) /
          finiteDilogE (letterWord bs) τ
            (fiveTermCharacteristicResidue (letterWord bs) mk.1 mk.2 +
              fiveTermCharacteristicResidue (letterWord bs) v₁ v₂)) := by
  have hfib := wordCrossed_residue_at_index_eq_window h (u₁ + 1) v₁ v₂
    (fiveTermLatticeArgument (letterWord bs) τ u₁ u₂)
    (-finiteDilogOrder (letterWord bs))
  have hδ :
      ((-(fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) *
        ((-finiteDilogOrder (letterWord bs) : ℤ) : ℝ) /
        ((letterWord bs 1 0 : ℝ) *
          (finiteDilogOrder (letterWord bs) : ℝ))) : ℂ) =
      (((fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
        (letterWord bs 1 0 : ℝ) : ℝ) : ℂ) := by
    have hN : (finiteDilogOrder (letterWord bs) : ℝ) ≠ 0 := by
      exact_mod_cast (finiteDilogOrder_pos h.fixedPoint).ne'
    have hc : (letterWord bs 1 0 : ℝ) ≠ 0 := by
      exact_mod_cast h.fixedPoint.lowerLeft_pos.ne'
    have hr : -(fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) *
        ((-finiteDilogOrder (letterWord bs) : ℤ) : ℝ) /
          ((letterWord bs 1 0 : ℝ) * (finiteDilogOrder (letterWord bs) : ℝ)) =
        (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
          (letterWord bs 1 0 : ℝ) := by
      push_cast
      field_simp [hc, hN]
    exact_mod_cast hr
  rw [hδ] at hfib
  rw [hfib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro mk hmk
  have hS := (Finset.mem_filter.mp hmk).2
  have hN := finiteDilogOrder_pos h.fixedPoint
  have hSneg : fiveTermLatticeIndex (letterWord bs) mk.1 mk.2 < 0 := by omega
  have hSv : fiveTermLatticeIndex (letterWord bs) (mk.1 + v₁) (mk.2 + v₂) =
      -finiteDilogOrder (letterWord bs) + fiveTermLatticeIndex (letterWord bs) v₁ v₂ := by
    rw [fiveTermLatticeIndex_add, hS]
  rw [fiveTermWordKernelResidue_eq_of_types h mk.1 mk.2 u₁ u₂ v₁ v₂]
  simp only [not_le.mpr hSneg, ↓reduceIte]
  by_cases hV : fiveTermLatticeIndex (letterWord bs) v₁ v₂ =
      finiteDilogOrder (letterWord bs)
  · have hSv0 : 0 ≤ fiveTermLatticeIndex (letterWord bs) (mk.1 + v₁) (mk.2 + v₂) := by
      rw [hSv, hV]
      omega
    simp only [hSv0, ↓reduceIte]
    rw [fiveTermCharacteristicResidue_add]
    ring
  · have hSvneg : fiveTermLatticeIndex (letterWord bs) (mk.1 + v₁) (mk.2 + v₂) < 0 := by
      rw [hSv]
      omega
    have hclass := wordCrossed_denominator_class_ne_zero h.fixedPoint
      mk.1 mk.2 v₁ v₂ hS ⟨by omega, by omega⟩
    simp only [not_le.mpr hSvneg, ↓reduceIte]
    rw [finiteDilogEMinus_of_ne_zero h.fixedPoint hclass,
      fiveTermCharacteristicResidue_add]
    ring

/-- Transporting the two special fibers leaves only the numerator zero-class difference.
Used by `integral_fiveTermWordResidueSum_of_crossed`. -/
private lemma wordCrossed_zero_fiber_value_difference {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) [NeZero (finiteDilogOrder (letterWord bs))]
    (u₁ u₂ v₁ v₂ : ℤ) :
    (∑ mk ∈ fiveTermWindow (letterWord bs) 0 with
        fiveTermLatticeIndex (letterWord bs) mk.1 mk.2 = 0,
        fixedBicharacter (letterWord bs) (finiteDilogOrder (letterWord bs))
          (fiveTermCharacteristicResidue (letterWord bs) mk.1 mk.2)
          (fiveTermCharacteristicResidue (letterWord bs) u₁ u₂) *
        (finiteDilogE (letterWord bs) τ
            (fiveTermCharacteristicResidue (letterWord bs) mk.1 mk.2) /
          finiteDilogE (letterWord bs) τ
            (fiveTermCharacteristicResidue (letterWord bs) mk.1 mk.2 +
              fiveTermCharacteristicResidue (letterWord bs) v₁ v₂))) -
      (∑ mk ∈ fiveTermWindow (letterWord bs) (-finiteDilogOrder (letterWord bs)) with
        fiveTermLatticeIndex (letterWord bs) mk.1 mk.2 =
          -finiteDilogOrder (letterWord bs),
        fixedBicharacter (letterWord bs) (finiteDilogOrder (letterWord bs))
          (fiveTermCharacteristicResidue (letterWord bs) mk.1 mk.2)
          (fiveTermCharacteristicResidue (letterWord bs) u₁ u₂) *
        (finiteDilogEMinus (letterWord bs) τ
            (fiveTermCharacteristicResidue (letterWord bs) mk.1 mk.2) /
          finiteDilogE (letterWord bs) τ
            (fiveTermCharacteristicResidue (letterWord bs) mk.1 mk.2 +
              fiveTermCharacteristicResidue (letterWord bs) v₁ v₂))) =
      (finiteDilogE (letterWord bs) τ 0 - finiteDilogEMinus (letterWord bs) τ 0) /
        finiteDilogE (letterWord bs) τ
          (fiveTermCharacteristicResidue (letterWord bs) v₁ v₂) := by
  let f : (Fin 2 → ZMod (finiteDilogOrder (letterWord bs))) → ℂ := fun g =>
    fixedBicharacter (letterWord bs) (finiteDilogOrder (letterWord bs)) g
      (fiveTermCharacteristicResidue (letterWord bs) u₁ u₂) *
      (finiteDilogEMinus (letterWord bs) τ g /
        finiteDilogE (letterWord bs) τ
          (g + fiveTermCharacteristicResidue (letterWord bs) v₁ v₂))
  have htransport := sum_fiveTermWindow_index_sub h.fixedPoint 0 f
  simp only [zero_sub] at htransport
  change (∑ mk ∈ fiveTermWindow (letterWord bs) 0 with
        fiveTermLatticeIndex (letterWord bs) mk.1 mk.2 = 0,
        fixedBicharacter (letterWord bs) (finiteDilogOrder (letterWord bs))
          (fiveTermCharacteristicResidue (letterWord bs) mk.1 mk.2)
          (fiveTermCharacteristicResidue (letterWord bs) u₁ u₂) *
        (finiteDilogE (letterWord bs) τ
            (fiveTermCharacteristicResidue (letterWord bs) mk.1 mk.2) /
          finiteDilogE (letterWord bs) τ
            (fiveTermCharacteristicResidue (letterWord bs) mk.1 mk.2 +
              fiveTermCharacteristicResidue (letterWord bs) v₁ v₂))) -
      (∑ mk ∈ fiveTermWindow (letterWord bs) (-finiteDilogOrder (letterWord bs)) with
        fiveTermLatticeIndex (letterWord bs) mk.1 mk.2 =
          -finiteDilogOrder (letterWord bs),
        f (fiveTermCharacteristicResidue (letterWord bs) mk.1 mk.2)) = _
  rw [← htransport, ← Finset.sum_sub_distrib]
  have hzero : (0, 0) ∈ fiveTermWindow (letterWord bs) 0 := by
    apply (mem_fiveTermWindow h.fixedPoint 0 (0, 0)).2
    have hc : (0 : ℤ) < letterWord bs 1 0 := h.fixedPoint.lowerLeft_pos
    have hN : 0 < finiteDilogOrder (letterWord bs) :=
      finiteDilogOrder_pos h.fixedPoint
    simpa [fiveTermLatticeIndex] using
      (show 0 ≤ (0 : ℤ) ∧ 0 < letterWord bs 1 0 ∧
        0 ≤ (0 : ℤ) ∧ 0 < finiteDilogOrder (letterWord bs) from
        ⟨le_refl _, hc, le_refl _, hN⟩)
  have hzeroF : (0, 0) ∈
      (fiveTermWindow (letterWord bs) 0).filter
        (fun mk => fiveTermLatticeIndex (letterWord bs) mk.1 mk.2 = 0) :=
    Finset.mem_filter.mpr ⟨hzero, by simp [fiveTermLatticeIndex]⟩
  have h00 : fiveTermCharacteristicResidue (letterWord bs) 0 0 = 0 := by
    apply (fiveTermCharacteristicResidue_eq_zero_iff h.fixedPoint 0 0).2
    exact ⟨0, 0, by simp, by simp⟩
  rw [Finset.sum_eq_single (0, 0)]
  · simp only [f, h00, zero_add, fixedBicharacter_zero_left, one_mul]
    ring
  · intro mk hmk hne
    have hmkW := (Finset.mem_filter.mp hmk).1
    have hclass : fiveTermCharacteristicResidue (letterWord bs) mk.1 mk.2 ≠ 0 := by
      intro hz
      have heq := fiveTermCharacteristicResidue_injOn h.fixedPoint 0 hmkW hzero
      apply hne
      apply heq
      exact hz.trans h00.symm
    simp [f, finiteDilogEMinus_of_ne_zero h.fixedPoint hclass]
  · simp [hzeroF]

/-- The difference of residues at zero and one strip width is the zero-class value
correction. Used by `integral_fiveTermWordResidueSum_of_crossed`. -/
private lemma wordCrossed_zero_residue_difference {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) [NeZero (finiteDilogOrder (letterWord bs))]
    (u₁ u₂ v₁ v₂ : ℤ)
    (hv : 1 ≤ fiveTermLatticeIndex (letterWord bs) v₁ v₂ ∧
      fiveTermLatticeIndex (letterWord bs) v₁ v₂ ≤ finiteDilogOrder (letterWord bs))
    (hv0 : fiveTermCharacteristicResidue (letterWord bs) v₁ v₂ ≠ 0) :
    wordCrossedResidueAtPosition bs τ (u₁ + 1) v₁ v₂
        (fiveTermLatticeArgument (letterWord bs) τ u₁ u₂) 0 -
      wordCrossedResidueAtPosition bs τ (u₁ + 1) v₁ v₂
        (fiveTermLatticeArgument (letterWord bs) τ u₁ u₂)
        (((fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
          (letterWord bs 1 0 : ℝ) : ℝ) : ℂ) =
      fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
        (2 * Real.pi * I * (1 - fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ))) *
        ((finiteDilogE (letterWord bs) τ 0 - finiteDilogEMinus (letterWord bs) τ 0) /
          finiteDilogEMinus (letterWord bs) τ
            (fiveTermCharacteristicResidue (letterWord bs) v₁ v₂)) := by
  rw [wordCrossed_residue_at_zero_eq_fiber h u₁ u₂ v₁ v₂ hv.1,
    wordCrossed_residue_at_width_eq_fiber h u₁ u₂ v₁ v₂ hv]
  rw [← mul_sub, wordCrossed_zero_fiber_value_difference h u₁ u₂ v₁ v₂]
  rw [finiteDilogEMinus_of_ne_zero h.fixedPoint hv0]

/-- Adding the zero-class correction replaces `F⁻` by `E` in the finite sum. Used by
`integral_fiveTermWordResidueSum_of_crossed`. -/
private lemma wordCrossed_finite_values_correction {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) [NeZero (finiteDilogOrder (letterWord bs))]
    (u₁ u₂ v₁ v₂ : ℤ) :
    (∑ g : finiteDilogGroup (letterWord bs),
        fixedBicharacter (letterWord bs) (finiteDilogOrder (letterWord bs)) g
          (fiveTermCharacteristicResidue (letterWord bs) u₁ u₂) *
        (finiteDilogEMinus (letterWord bs) τ g /
          finiteDilogEMinus (letterWord bs) τ
            (g + fiveTermCharacteristicResidue (letterWord bs) v₁ v₂))) +
      (finiteDilogE (letterWord bs) τ 0 - finiteDilogEMinus (letterWord bs) τ 0) /
        finiteDilogEMinus (letterWord bs) τ
          (fiveTermCharacteristicResidue (letterWord bs) v₁ v₂) =
      ∑ g : finiteDilogGroup (letterWord bs),
        fixedBicharacter (letterWord bs) (finiteDilogOrder (letterWord bs)) g
          (fiveTermCharacteristicResidue (letterWord bs) u₁ u₂) *
        (finiteDilogE (letterWord bs) τ g /
          finiteDilogEMinus (letterWord bs) τ
            (g + fiveTermCharacteristicResidue (letterWord bs) v₁ v₂)) := by
  classical
  have hdiff :
      (∑ g : finiteDilogGroup (letterWord bs),
        fixedBicharacter (letterWord bs) (finiteDilogOrder (letterWord bs)) g
          (fiveTermCharacteristicResidue (letterWord bs) u₁ u₂) *
        (finiteDilogE (letterWord bs) τ g /
          finiteDilogEMinus (letterWord bs) τ
            (g + fiveTermCharacteristicResidue (letterWord bs) v₁ v₂))) -
      (∑ g : finiteDilogGroup (letterWord bs),
        fixedBicharacter (letterWord bs) (finiteDilogOrder (letterWord bs)) g
          (fiveTermCharacteristicResidue (letterWord bs) u₁ u₂) *
        (finiteDilogEMinus (letterWord bs) τ g /
          finiteDilogEMinus (letterWord bs) τ
            (g + fiveTermCharacteristicResidue (letterWord bs) v₁ v₂))) =
      (finiteDilogE (letterWord bs) τ 0 - finiteDilogEMinus (letterWord bs) τ 0) /
        finiteDilogEMinus (letterWord bs) τ
          (fiveTermCharacteristicResidue (letterWord bs) v₁ v₂) := by
    rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single (0 : finiteDilogGroup (letterWord bs))]
    · simp [fixedBicharacter_zero_left]
      ring
    · intro g hg hne
      have hg0 : (g : Fin 2 → ZMod (finiteDilogOrder (letterWord bs))) ≠ 0 := by
        intro hz
        exact hne (Subtype.ext hz)
      rw [finiteDilogEMinus_of_ne_zero h.fixedPoint hg0]
      ring
    · simp
  linear_combination -hdiff

/-- Reindexing positive square corrections gives the product-pole residue sum. Used by
`wordCrossed_square_sum`. -/
private lemma wordCrossed_positive_square_sum {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ v₁ v₂ : ℤ) (w β : ℝ) (F : Finset ℤ)
    (hβle : β ≤ (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
      (letterWord bs 1 0 : ℝ))
    (hF : ∀ j : ℤ, j ∈ F ↔ 0 ≤ j ∧
      (j : ℝ) / (letterWord bs 1 0 : ℝ) < β)
    (hv : 1 ≤ fiveTermLatticeIndex (letterWord bs) v₁ v₂)
    (hw : Complex.exp (2 * Real.pi * I *
        ((w : ℂ) / fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ))) =
      Complex.exp (2 * Real.pi * I * ((w : ℂ) + (ℓ - 1) * (τ : ℂ))))
    (hy : Complex.exp (2 * Real.pi * I *
        ((fiveTermLatticeArgument (letterWord bs) τ v₁ v₂ : ℂ) /
          fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ))) =
      Complex.exp (2 * Real.pi * I *
        ((fiveTermLatticeArgument (letterWord bs) τ v₁ v₂ : ℂ) + v₁ * (τ : ℂ))))
    (RP : ℂ → ℂ)
    (hRP : ∀ s ∈ wordCrossedProductPoleSet (letterWord bs) τ F,
      Tendsto (fun ζ : ℂ => (ζ - s) *
        fiveTermWordResidueSum bs ℓ v₁ w
          (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ ζ)
        (𝓝[≠] s) (𝓝 (RP s))) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      (∑ j ∈ F.filter (0 < ·), rectBoundaryIntegral
        (fiveTermWordDifferenceSum bs ℓ v₁ w
          (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ)
        ((j : ℂ) / (letterWord bs 1 0 : ℂ) - (r + r * I))
        ((j : ℂ) / (letterWord bs 1 0 : ℂ) + (r + r * I))) =
      -(2 * Real.pi * I) *
        (∑ s ∈ wordCrossedProductPoleSet (letterWord bs) τ F, RP s) := by
  classical
  let G := F.filter (0 < ·)
  have hpositive : ∀ᶠ r : ℝ in 𝓝[>] 0,
      ∀ j ∈ G,
        rectBoundaryIntegral
          (fiveTermWordDifferenceSum bs ℓ v₁ w
            (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ)
          ((j : ℂ) / (letterWord bs 1 0 : ℂ) - (r + r * I))
          ((j : ℂ) / (letterWord bs 1 0 : ℂ) + (r + r * I)) =
        -(2 * Real.pi * I) *
          RP (((fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
            (letterWord bs 1 0 : ℝ) +
            (j : ℝ) / (letterWord bs 1 0 : ℝ)) : ℂ) := by
    apply (Finset.eventually_all G).2
    intro j hjG
    obtain ⟨hjF, hj⟩ := Finset.mem_filter.mp hjG
    apply wordCrossed_positive_square_correction h ℓ v₁ v₂ w F j hjF hj
      (le_trans (le_of_lt ((hF j).1 hjF).2) hβle) hv hw hy RP hRP
  filter_upwards [hpositive] with r hrP
  have hsumImage :
      (∑ s ∈ wordCrossedProductPoleSet (letterWord bs) τ F, RP s) =
        ∑ j ∈ G,
          RP (((fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
            (letterWord bs 1 0 : ℝ) +
            (j : ℝ) / (letterWord bs 1 0 : ℝ)) : ℂ) := by
    dsimp [wordCrossedProductPoleSet, G]
    apply Finset.sum_image
    intro a ha b hb hab
    exact wordCrossed_product_position_injective h.fixedPoint hab
  have hG : (∑ j ∈ G, rectBoundaryIntegral
        (fiveTermWordDifferenceSum bs ℓ v₁ w
          (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ)
        ((j : ℂ) / (letterWord bs 1 0 : ℂ) - (r + r * I))
        ((j : ℂ) / (letterWord bs 1 0 : ℂ) + (r + r * I))) =
      -(2 * Real.pi * I) *
        (∑ s ∈ wordCrossedProductPoleSet (letterWord bs) τ F, RP s) := by
    calc
      _ = ∑ j ∈ G, -(2 * Real.pi * I) *
          RP (((fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
            (letterWord bs 1 0 : ℝ) +
            (j : ℝ) / (letterWord bs 1 0 : ℝ)) : ℂ) := by
        apply Finset.sum_congr rfl
        exact hrP
      _ = _ := by
        rw [← Finset.mul_sum]
        rw [hsumImage]
  exact hG

/-- The square integrals cancel positive product residues and retain the zero correction.
Used by `integral_fiveTermWordResidueSum_of_crossed`. -/
private lemma wordCrossed_square_sum {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ v₁ v₂ : ℤ) (w β : ℝ) (F : Finset ℤ)
    (hβpos : 0 < β)
    (hβle : β ≤ (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
      (letterWord bs 1 0 : ℝ))
    (hF : ∀ j : ℤ, j ∈ F ↔ 0 ≤ j ∧
      (j : ℝ) / (letterWord bs 1 0 : ℝ) < β)
    (hv : 1 ≤ fiveTermLatticeIndex (letterWord bs) v₁ v₂ ∧
      fiveTermLatticeIndex (letterWord bs) v₁ v₂ ≤ finiteDilogOrder (letterWord bs))
    (hw : Complex.exp (2 * Real.pi * I *
        ((w : ℂ) / fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ))) =
      Complex.exp (2 * Real.pi * I * ((w : ℂ) + (ℓ - 1) * (τ : ℂ))))
    (hy : Complex.exp (2 * Real.pi * I *
        ((fiveTermLatticeArgument (letterWord bs) τ v₁ v₂ : ℂ) /
          fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ))) =
      Complex.exp (2 * Real.pi * I *
        ((fiveTermLatticeArgument (letterWord bs) τ v₁ v₂ : ℂ) + v₁ * (τ : ℂ))))
    (RP : ℂ → ℂ)
    (hRP : ∀ s ∈ wordCrossedProductPoleSet (letterWord bs) τ F,
      Tendsto (fun ζ : ℂ => (ζ - s) *
        fiveTermWordResidueSum bs ℓ v₁ w
          (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ ζ)
        (𝓝[≠] s) (𝓝 (RP s))) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      (∑ j ∈ F, rectBoundaryIntegral
        (fiveTermWordDifferenceSum bs ℓ v₁ w
          (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ)
        ((j : ℂ) / (letterWord bs 1 0 : ℂ) - (r + r * I))
        ((j : ℂ) / (letterWord bs 1 0 : ℂ) + (r + r * I))) =
      2 * Real.pi * I *
        (wordCrossedResidueAtPosition bs τ ℓ v₁ v₂ w 0 -
          wordCrossedResidueAtPosition bs τ ℓ v₁ v₂ w
            (((fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
              (letterWord bs 1 0 : ℝ) : ℝ) : ℂ)) -
      2 * Real.pi * I *
        (∑ s ∈ wordCrossedProductPoleSet (letterWord bs) τ F, RP s) := by
  classical
  let G := F.filter (0 < ·)
  have hF0 : (0 : ℤ) ∈ F := (hF 0).2 ⟨le_refl _, by simpa using hβpos⟩
  have hsplit : F = insert 0 G := by
    ext j
    simp only [G, Finset.mem_insert, Finset.mem_filter]
    constructor
    · intro hj
      by_cases hj0 : j = 0
      · exact Or.inl hj0
      · exact Or.inr ⟨hj, by have := (hF j).1 hj; omega⟩
    · rintro (rfl | ⟨hj, _⟩)
      · exact hF0
      · exact hj
  have h0not : (0 : ℤ) ∉ G := by simp [G]
  have hzero := wordCrossed_zero_square_correction h ℓ v₁ v₂ w hv.1 hv.2 hw hy
  have hpositive := wordCrossed_positive_square_sum h ℓ v₁ v₂ w β F
    hβle hF hv.1 hw hy RP hRP
  filter_upwards [hzero, hpositive] with r hr0 hrP
  conv_lhs => rw [hsplit, Finset.sum_insert h0not]
  simp only [Int.cast_zero, zero_div, zero_add, zero_sub]
  rw [hr0, hrP]
  ring

/-- The corrected kernel residues equal the finite five-term sum. Used by
`integral_fiveTermWordResidueSum_of_crossed`. -/
private lemma wordCrossed_finite_residue_synthesis {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) [NeZero (finiteDilogOrder (letterWord bs))]
    (u₁ u₂ v₁ v₂ : ℤ)
    (hv : 1 ≤ fiveTermLatticeIndex (letterWord bs) v₁ v₂ ∧
      fiveTermLatticeIndex (letterWord bs) v₁ v₂ ≤ finiteDilogOrder (letterWord bs))
    (hv0 : fiveTermCharacteristicResidue (letterWord bs) v₁ v₂ ≠ 0) :
    -(2 * Real.pi * I) *
      ((∑ mk ∈ fiveTermWindow (letterWord bs)
          (-finiteDilogOrder (letterWord bs) -
            fiveTermLatticeIndex (letterWord bs) v₁ v₂),
          fiveTermWordKernelResidue bs (u₁ + 1) v₁
            (fiveTermLatticeArgument (letterWord bs) τ u₁ u₂)
            (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ mk.1
            (fiveTermLatticeArgument (letterWord bs) τ mk.1 mk.2)) +
        (wordCrossedResidueAtPosition bs τ (u₁ + 1) v₁ v₂
            (fiveTermLatticeArgument (letterWord bs) τ u₁ u₂) 0 -
          wordCrossedResidueAtPosition bs τ (u₁ + 1) v₁ v₂
            (fiveTermLatticeArgument (letterWord bs) τ u₁ u₂)
            (((fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
              (letterWord bs 1 0 : ℝ) : ℝ) : ℂ))) =
      fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
        (fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) - 1) *
        ∑ g : finiteDilogGroup (letterWord bs),
          fixedBicharacter (letterWord bs) (finiteDilogOrder (letterWord bs)) g
            (fiveTermCharacteristicResidue (letterWord bs) u₁ u₂) *
          (finiteDilogE (letterWord bs) τ g /
            finiteDilogEMinus (letterWord bs) τ
              (g + fiveTermCharacteristicResidue (letterWord bs) v₁ v₂)) := by
  rw [wordCrossed_window_residue_sum_eq h u₁ u₂ v₁ v₂ hv.1,
    wordCrossed_zero_residue_difference h u₁ u₂ v₁ v₂ hv hv0]
  have hfin := wordCrossed_finite_values_correction h u₁ u₂ v₁ v₂
  have hfac : -(2 * Real.pi * I) *
      (fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
        (2 * Real.pi * I *
          (1 - fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ)))) =
      fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
        (fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) - 1) := by
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hI : (I : ℂ) ≠ 0 := I_ne_zero
    have hε : fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) - 1 ≠ 0 := by
      exact_mod_cast (ne_of_gt (sub_pos.mpr h.fixedPoint.one_lt_fltDenominator))
    have hε' : 1 - fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) ≠ 0 := by
      intro hz
      apply hε
      linear_combination -hz
    field_simp [hπ, hI, hε, hε']
    ring
  calc
    _ = (-(2 * Real.pi * I) *
        (fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
          (2 * Real.pi * I *
            (1 - fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ))))) *
        ((∑ g : finiteDilogGroup (letterWord bs),
          fixedBicharacter (letterWord bs) (finiteDilogOrder (letterWord bs)) g
            (fiveTermCharacteristicResidue (letterWord bs) u₁ u₂) *
          (finiteDilogEMinus (letterWord bs) τ g /
            finiteDilogEMinus (letterWord bs) τ
              (g + fiveTermCharacteristicResidue (letterWord bs) v₁ v₂))) +
          (finiteDilogE (letterWord bs) τ 0 -
            finiteDilogEMinus (letterWord bs) τ 0) /
            finiteDilogEMinus (letterWord bs) τ
              (fiveTermCharacteristicResidue (letterWord bs) v₁ v₂)) := by ring
    _ = _ := by rw [hfin, hfac]

/-- **The crossed residue strip.** For positive source representatives `0 ≤ S(u) < N`,
`1 ≤ S(v) ≤ N` with `v` off the zero class, and a common line `β_v < x < β_v + δ/N`,
`x < ε/c`, through regular residue crossings, the difference of the line integrals of the residue
sum `L` at `x` and `x + δ`, minus the boundary integrals of the difference sum `J` over the small
squares around the crossed points `j/c`, is `ε/(ε-1) ∑_{g ∈ G} ⟨g; u⟩ E(g)/F⁻(g+v)`. This is the
residue computation in the proof of [RW26, Radchenko, Wheeler (2026), Theorem 2, `thm:fg.equs`,
Section 3.2], with the deformed contours in straight-line form. -/
theorem integral_fiveTermWordResidueSum_of_crossed {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) [NeZero (finiteDilogOrder (letterWord bs))]
    (u₁ u₂ v₁ v₂ : ℤ)
    (hu : 0 ≤ fiveTermLatticeIndex (letterWord bs) u₁ u₂ ∧
      fiveTermLatticeIndex (letterWord bs) u₁ u₂ < finiteDilogOrder (letterWord bs))
    (hv : 1 ≤ fiveTermLatticeIndex (letterWord bs) v₁ v₂ ∧
      fiveTermLatticeIndex (letterWord bs) v₁ v₂ ≤ finiteDilogOrder (letterWord bs))
    (hv0 : fiveTermCharacteristicResidue (letterWord bs) v₁ v₂ ≠ 0) :
    let ε := fltDenominator (letterWord bs : Mat(2, ℤ)) τ
    let c : ℝ := (letterWord bs 1 0 : ℝ)
    let N : ℝ := (finiteDilogOrder (letterWord bs) : ℝ)
    let δ := (ε - 1) / c
    let w := fiveTermLatticeArgument (letterWord bs) τ u₁ u₂
    let y := fiveTermLatticeArgument (letterWord bs) τ v₁ v₂
    let β := -((v₁ : ℝ) * ε / c + y)
    let L := fiveTermWordResidueSum bs (u₁ + 1) v₁ w y τ
    let J := fiveTermWordDifferenceSum bs (u₁ + 1) v₁ w y τ
    ∀ (x : ℝ) (F : Finset ℤ),
      β < x → x < β + δ / N → x < ε / c →
      (∀ j : ℤ, j ∈ F ↔ 0 ≤ j ∧ (j : ℝ) / c < β) →
      (∀ j : ℤ, 0 ≤ j → ((j : ℝ) / c < x ↔ (j : ℝ) / c < β)) →
      (∀ m : FiveTermIndex (letterWord bs),
        IsFiveTermResidueCrossing (letterWord bs) τ ((m : ℕ) : ℤ) y
          (x - ((m : ℕ) : ℝ) * ε / c)) →
      ∀ᶠ r : ℝ in 𝓝[>] 0,
        ((∫ t : ℝ, L ((x : ℂ) + t * I) * I) -
          (∫ t : ℝ, L (((x + δ : ℝ) : ℂ) + t * I) * I)) -
          (∑ j ∈ F, rectBoundaryIntegral J
            ((j : ℂ) / (c : ℂ) - (r + r * I)) ((j : ℂ) / (c : ℂ) + (r + r * I))) =
        (ε : ℂ) / ((ε : ℂ) - 1) *
          ∑ g : finiteDilogGroup (letterWord bs),
            fixedBicharacter (letterWord bs) (finiteDilogOrder (letterWord bs)) g
              (fiveTermCharacteristicResidue (letterWord bs) u₁ u₂) *
            (finiteDilogE (letterWord bs) τ g /
              finiteDilogEMinus (letterWord bs) τ
                (g + fiveTermCharacteristicResidue (letterWord bs) v₁ v₂)) := by
  dsimp
  intro x F hβ hx₂ hx hF hgrid hreg
  have hβbounds := wordCrossed_beta_bounds h.fixedPoint v₁ v₂ hv
  have hβpos : 0 < -((v₁ : ℝ) *
      fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
      (letterWord bs 1 0 : ℝ) +
      fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) := hβbounds.1
  have hβle : -((v₁ : ℝ) *
      fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
      (letterWord bs 1 0 : ℝ) +
      fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) ≤
      (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
      (letterWord bs 1 0 : ℝ) := hβbounds.2
  have hx₂' : x < -((v₁ : ℝ) *
      fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
      (letterWord bs 1 0 : ℝ) +
      fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) +
      (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
        ((letterWord bs 1 0 : ℝ) *
          (finiteDilogOrder (letterWord bs) : ℝ)) := by
    convert hx₂ using 1
    ring
  have hsum : 0 < fiveTermLatticeIndex (letterWord bs) u₁ u₂ +
      fiveTermLatticeIndex (letterWord bs) v₁ v₂ := by omega
  have hrate := fiveTermLatticeArgument_source_rates h.fixedPoint
    u₁ u₂ v₁ v₂ hu.2 hsum
  have hw : Complex.exp (2 * Real.pi * I *
      ((fiveTermLatticeArgument (letterWord bs) τ u₁ u₂ : ℂ) /
        fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ))) =
      Complex.exp (2 * Real.pi * I *
        ((fiveTermLatticeArgument (letterWord bs) τ u₁ u₂ : ℂ) +
          ((u₁ + 1 : ℤ) - 1) * (τ : ℂ))) := by
    convert fiveTermLatticeArgument_exp_div h.fixedPoint u₁ u₂ using 1
    push_cast
    ring_nf
  have hy := fiveTermLatticeArgument_exp_div h.fixedPoint v₁ v₂
  obtain ⟨RP, hRP, hstrip⟩ := wordCrossed_strip_residue_identity h
    (u₁ + 1) v₁ v₂ (fiveTermLatticeArgument (letterWord bs) τ u₁ u₂) x
    (-((v₁ : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
      (letterWord bs 1 0 : ℝ) +
      fiveTermLatticeArgument (letterWord bs) τ v₁ v₂)) F
    rfl hβ hx₂' hx hgrid hF hreg hrate.1 hrate.2
  have hsquares := wordCrossed_square_sum h (u₁ + 1) v₁ v₂
    (fiveTermLatticeArgument (letterWord bs) τ u₁ u₂)
    (-((v₁ : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
      (letterWord bs 1 0 : ℝ) +
      fiveTermLatticeArgument (letterWord bs) τ v₁ v₂)) F
    hβpos hβle hF hv hw hy RP hRP
  have hfinite := wordCrossed_finite_residue_synthesis h u₁ u₂ v₁ v₂ hv hv0
  filter_upwards [hsquares] with r hr
  rw [hstrip, hr]
  convert hfinite using 1
  · ring
  · push_cast
    rfl

end SIC

end
