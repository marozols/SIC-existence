/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.ResidueStrip
import SICs.SpecialFunctions.Faddeev.FiveTerm.CrossedPoles

/-!
# Cancellation of crossed poles in the principal residue strip

The residue strip with positive source representatives cancels the crossed-pole square
corrections and supplies the finite sum with its zero-class value `F⁺(0)`.

This module follows [RW26, Radchenko, Wheeler (2026), Section 3.2, the proof of Theorem 2,
`thm:fg.equs`] at `A_d`, using the deformations of `D_m(y)` in Figure 1 in straight-line form.
Write `ε = ρ_d³`, `c = d(d-2)`, `H = d(d-3)`, `δ = (ε-1)/c`, and `S_d(m,k) = m+(d-2)k`.

## The argument

Choose `0 ≤ S_d(u) < H`, `1 ≤ S_d(v) ≤ H`, and a common line just right of
`β_v = -(v₁ε/c+z_v)`. The kernel poles in its strip have indices
`-H-S_d(v) ≤ S_d(x) < -S_d(v)`, one representative of each finite class. The exact divisor
also puts numerator poles of `L` at `δ+j/c` for positive integers `j` with `j/c < β_v`.
The poles crossed by the difference kernel `J` lie at `j/c`, including `j=0`.

The germ identity `J(z)=L(z)-L(z+δ)` pairs the positive-index corrections with these product
poles. At zero it leaves `Res L(0)-Res L(δ)`. The negative-index window has numerator type
`F⁻`; this difference replaces only the zero-class numerator by `F⁺(0)`. When `S_d(v)=H`,
`δ` lies left of the strip, but the same difference of fibers still gives this replacement;
the zero-class representative in the window is then at `2δ`. This comparison does not require
`δ` itself to lie in the strip. The denominator type throughout the window
is `F⁻`. The rectangle residue theorem, exponential tail bounds, and window bijection then
leave `ε/(ε-1)` times the finite five-term sum.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology MatrixGroups

namespace SIC

/-! ### Strip geometry, divisor, and pole sets

The spacing of the kernel poles turns the strip inequalities into the exact negative-index
window. The product divisor supplies the additional poles at `δ+j/c`; irrationality excludes
denominator zeros at the crossed rational points. These two pole sets account for all
possible singularities in the closed strip.
-/

/-- The crossing coordinate `β` is the pole spacing times `S_d(v)`.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_beta_eq_spacing_index (d : ℕ) (hd : 3 < d) (v₁ v₂ : ℤ) :
    -((v₁ : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ) +
      principalFiveTermLatticeArgument d v₁ v₂) =
      (principalRoot d ^ 3 - 1) /
        (((principalA d) 1 0 : ℝ) *
          (principalFiveTermUpperIndexBound d : ℝ)) *
        (principalFiveTermLatticeIndex d v₁ v₂ : ℝ) := by
  have h := principalFiveTermLatticeArgument_add_mul_eq d hd v₁ v₂
  linear_combination -h

/-- The common pole spacing is positive.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_spacing_pos (d : ℕ) (hd : 3 < d) :
    0 < (principalRoot d ^ 3 - 1) /
      (((principalA d) 1 0 : ℝ) *
        (principalFiveTermUpperIndexBound d : ℝ)) := by
  apply div_pos
  · exact sub_pos.mpr (one_lt_principalRoot_pow_three d hd)
  · exact mul_pos (by exact_mod_cast principalA_lowerLeft_pos d hd)
      (by exact_mod_cast principalFiveTermUpperIndexBound_pos d hd)

/-- The strip width is `H` times the pole spacing.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_width_eq_spacing_mul_bound (d : ℕ) (hd : 3 < d) :
    (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ) =
      (principalRoot d ^ 3 - 1) /
        (((principalA d) 1 0 : ℝ) *
          (principalFiveTermUpperIndexBound d : ℝ)) *
        (principalFiveTermUpperIndexBound d : ℝ) := by
  have hc : ((principalA d) 1 0 : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast principalA_lowerLeft_pos d hd)
  have hH : (principalFiveTermUpperIndexBound d : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast principalFiveTermUpperIndexBound_pos d hd)
  field_simp

/-- The crossing coordinate lies no farther right than the strip width.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_width_ge_beta (d : ℕ) (hd : 3 < d)
    (v₁ v₂ : ℤ)
    (hv : principalFiveTermLatticeIndex d v₁ v₂ ≤
      principalFiveTermUpperIndexBound d) :
    -((v₁ : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ) +
      principalFiveTermLatticeArgument d v₁ v₂) ≤
      (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ) := by
  rw [crossed_beta_eq_spacing_index d hd v₁ v₂,
    crossed_width_eq_spacing_mul_bound d hd]
  have hvR : (principalFiveTermLatticeIndex d v₁ v₂ : ℝ) ≤
      (principalFiveTermUpperIndexBound d : ℝ) := by exact_mod_cast hv
  exact mul_le_mul_of_nonneg_left hvR (crossed_spacing_pos d hd).le

/-- A kernel pole in the closed strip belongs to the source window.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_kernel_mem_window_of_closed_strip (d : ℕ) (hd : 3 < d)
    (v₁ v₂ m k : ℤ) (x : ℝ)
    (hx₁ : -((v₁ : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ) +
      principalFiveTermLatticeArgument d v₁ v₂) < x)
    (hx₂ : x < -((v₁ : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ) +
      principalFiveTermLatticeArgument d v₁ v₂) +
      (principalRoot d ^ 3 - 1) /
        (((principalA d) 1 0 : ℝ) *
          (principalFiveTermUpperIndexBound d : ℝ)))
    (hm : 0 ≤ m ∧ m < (d : ℤ) * ((d : ℤ) - 2))
    (hlo : x ≤ (principalFiveTermStripPolePosition d m k).re)
    (hhi : (principalFiveTermStripPolePosition d m k).re ≤
      x + (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ)) :
    (m, k) ∈ principalFiveTermWindow d
      (-principalFiveTermUpperIndexBound d -
        principalFiveTermLatticeIndex d v₁ v₂) := by
  let a : ℝ := (principalRoot d ^ 3 - 1) /
    (((principalA d) 1 0 : ℝ) *
      (principalFiveTermUpperIndexBound d : ℝ))
  have ha : 0 < a := crossed_spacing_pos d hd
  have hβ := crossed_beta_eq_spacing_index d hd v₁ v₂
  have hwidth := crossed_width_eq_spacing_mul_bound d hd
  have hpos := principalFiveTermLatticeArgument_add_mul_eq d hd m k
  have hpos' : (principalFiveTermStripPolePosition d m k).re =
      -a * (principalFiveTermLatticeIndex d m k : ℝ) := by
    simp only [principalFiveTermStripPolePosition, Complex.ofReal_re]
    dsimp [a]
    linear_combination hpos
  have hx₁' : a * (principalFiveTermLatticeIndex d v₁ v₂ : ℝ) < x := by
    rwa [← hβ]
  have hx₂' : x < a * ((principalFiveTermLatticeIndex d v₁ v₂ : ℝ) + 1) := by
    rw [hβ] at hx₂
    convert hx₂ using 1
    ring
  have hw : -principalFiveTermUpperIndexBound d -
      principalFiveTermLatticeIndex d v₁ v₂ ≤
        principalFiveTermLatticeIndex d m k ∧
      principalFiveTermLatticeIndex d m k <
        -principalFiveTermLatticeIndex d v₁ v₂ := by
    have hlo' : x ≤ -a * (principalFiveTermLatticeIndex d m k : ℝ) := by
      rwa [← hpos']
    have hhi' : -a * (principalFiveTermLatticeIndex d m k : ℝ) ≤
        x + a * (principalFiveTermUpperIndexBound d : ℝ) := by
      rwa [← hpos', ← hwidth]
    constructor
    · by_contra hn
      have hS : principalFiveTermLatticeIndex d m k ≤
          -principalFiveTermUpperIndexBound d -
            principalFiveTermLatticeIndex d v₁ v₂ - 1 := by omega
      have hSR : (principalFiveTermLatticeIndex d m k : ℝ) ≤
          -(principalFiveTermUpperIndexBound d : ℝ) -
            (principalFiveTermLatticeIndex d v₁ v₂ : ℝ) - 1 := by
        exact_mod_cast hS
      nlinarith [mul_nonneg ha.le (sub_nonneg.mpr
        (show (0 : ℝ) ≤ -(principalFiveTermUpperIndexBound d : ℝ) -
          (principalFiveTermLatticeIndex d v₁ v₂ : ℝ) - 1 -
            (principalFiveTermLatticeIndex d m k : ℝ) by linarith))]
    · by_contra hn
      have hS : -principalFiveTermLatticeIndex d v₁ v₂ ≤
          principalFiveTermLatticeIndex d m k := by omega
      have hSR : -(principalFiveTermLatticeIndex d v₁ v₂ : ℝ) ≤
          (principalFiveTermLatticeIndex d m k : ℝ) := by exact_mod_cast hS
      nlinarith [mul_nonneg ha.le (sub_nonneg.mpr
        (show (0 : ℝ) ≤ (principalFiveTermLatticeIndex d m k : ℝ) +
          (principalFiveTermLatticeIndex d v₁ v₂ : ℝ) by linarith))]
  apply (mem_principalFiveTermWindow d hd _ (m,k)).2
  refine ⟨hm.1, hm.2, hw.1, ?_⟩
  change principalFiveTermLatticeIndex d m k <
    -principalFiveTermUpperIndexBound d -
      principalFiveTermLatticeIndex d v₁ v₂ + principalFiveTermUpperIndexBound d
  omega

/-- A kernel pole lies in the open strip exactly when its source pair lies in the
window.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_kernel_mem_window_iff_mem_strip (d : ℕ) (hd : 3 < d)
    (v₁ v₂ m k : ℤ) (x : ℝ)
    (hx₁ : -((v₁ : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ) +
      principalFiveTermLatticeArgument d v₁ v₂) < x)
    (hx₂ : x < -((v₁ : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ) +
      principalFiveTermLatticeArgument d v₁ v₂) +
      (principalRoot d ^ 3 - 1) /
        (((principalA d) 1 0 : ℝ) *
          (principalFiveTermUpperIndexBound d : ℝ)))
    (hm : 0 ≤ m ∧ m < (d : ℤ) * ((d : ℤ) - 2)) :
    (m, k) ∈ principalFiveTermWindow d
      (-principalFiveTermUpperIndexBound d -
        principalFiveTermLatticeIndex d v₁ v₂) ↔
      x < principalFiveTermLatticeArgument d m k +
          (m : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ) ∧
        principalFiveTermLatticeArgument d m k +
          (m : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ) <
          x + (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ) := by
  let a : ℝ := (principalRoot d ^ 3 - 1) /
    (((principalA d) 1 0 : ℝ) *
      (principalFiveTermUpperIndexBound d : ℝ))
  have ha : 0 < a := crossed_spacing_pos d hd
  have hβ := crossed_beta_eq_spacing_index d hd v₁ v₂
  have hwidth := crossed_width_eq_spacing_mul_bound d hd
  have hpos := principalFiveTermLatticeArgument_add_mul_eq d hd m k
  have hpos' : principalFiveTermLatticeArgument d m k +
      (m : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ) =
      -a * (principalFiveTermLatticeIndex d m k : ℝ) := by
    dsimp [a]
    linear_combination hpos
  have hx₁' : a * (principalFiveTermLatticeIndex d v₁ v₂ : ℝ) < x := by
    rwa [← hβ]
  have hx₂' : x < a * ((principalFiveTermLatticeIndex d v₁ v₂ : ℝ) + 1) := by
    rw [hβ] at hx₂
    convert hx₂ using 1
    ring
  constructor
  · intro hmem
    obtain ⟨_, _, hlo, hhi⟩ :=
      (mem_principalFiveTermWindow d hd _ (m, k)).1 hmem
    change principalFiveTermLatticeIndex d m k <
      -principalFiveTermUpperIndexBound d -
        principalFiveTermLatticeIndex d v₁ v₂ +
          principalFiveTermUpperIndexBound d at hhi
    have hhiR : (principalFiveTermLatticeIndex d m k : ℝ) ≤
        -(principalFiveTermLatticeIndex d v₁ v₂ : ℝ) - 1 := by
      exact_mod_cast (show principalFiveTermLatticeIndex d m k ≤
        -principalFiveTermLatticeIndex d v₁ v₂ - 1 by omega)
    have hloR : -(principalFiveTermUpperIndexBound d : ℝ) -
        (principalFiveTermLatticeIndex d v₁ v₂ : ℝ) ≤
          (principalFiveTermLatticeIndex d m k : ℝ) := by exact_mod_cast hlo
    rw [hpos', hwidth]
    constructor
    · nlinarith [mul_nonneg ha.le (sub_nonneg.mpr
        (show (0 : ℝ) ≤ -(principalFiveTermLatticeIndex d v₁ v₂ : ℝ) - 1 -
          (principalFiveTermLatticeIndex d m k : ℝ) by linarith))]
    · nlinarith [mul_nonneg ha.le (sub_nonneg.mpr
        (show (0 : ℝ) ≤ (principalFiveTermLatticeIndex d m k : ℝ) +
          (principalFiveTermUpperIndexBound d : ℝ) +
          (principalFiveTermLatticeIndex d v₁ v₂ : ℝ) by linarith))]
  · rintro ⟨hlo, hhi⟩
    apply crossed_kernel_mem_window_of_closed_strip d hd v₁ v₂ m k x hx₁ hx₂ hm
    · simpa only [principalFiveTermStripPolePosition, Complex.ofReal_re,
        Int.cast_natCast] using le_of_lt hlo
    · simpa only [principalFiveTermStripPolePosition, Complex.ofReal_re,
        Int.cast_natCast] using le_of_lt hhi

/-- A numerator pole under the right boundary has first pole index one and position
`δ+j/c`.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_numerator_pole_arithmetic (d : ℕ) (hd : 3 < d)
    (m k l : ℤ)
    (hK : 0 < k + m)
    (hQ : (1 - (d : ℤ)) * k - (d : ℤ) * ((d : ℤ) - 2) * l ≤ 0)
    (hz : (k : ℝ) * principalRoot d + l +
      (m : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ) <
      (2 * principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ)) :
    k + m = 1 ∧
      1 ≤ 1 + ((d : ℤ) - 1) * k + (principalA d) 1 0 * l ∧
      (k : ℝ) * principalRoot d + l +
        (m : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ) =
        (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ) +
          ((1 + ((d : ℤ) - 1) * k + (principalA d) 1 0 * l : ℤ) : ℝ) /
            ((principalA d) 1 0 : ℝ) := by
  let ε : ℝ := principalRoot d ^ 3
  let c : ℝ := ((principalA d) 1 0 : ℝ)
  let K : ℤ := k + m
  let J : ℤ := 1 + ((d : ℤ) - 1) * k + (principalA d) 1 0 * l
  have hc : 0 < c := by
    dsimp [c]
    exact_mod_cast principalA_lowerLeft_pos d hd
  have hε : 0 < ε := pow_pos (principalRoot_pos d hd) 3
  have hJ : 1 ≤ J := by
    dsimp [J]
    have hA : (principalA d) 1 0 = (d : ℤ) * ((d : ℤ) - 2) := by simp [coe_principalA]
    rw [hA]
    have hQ' : 0 ≤ ((d : ℤ) - 1) * k + (d : ℤ) * ((d : ℤ) - 2) * l := by
      have hrewrite : (1 - (d : ℤ)) * k - (d : ℤ) * ((d : ℤ) - 2) * l =
          -(((d : ℤ) - 1) * k + (d : ℤ) * ((d : ℤ) - 2) * l) := by ring
      rw [hrewrite] at hQ
      omega
    omega
  have heq : (k : ℝ) * principalRoot d + l + (m : ℝ) * ε / c =
      ((K : ℝ) * ε + (J : ℝ) - 1) / c := by
    have hε' := principalRoot_pow_three_eq d hd
    have hc' : c = (d : ℝ) * ((d : ℝ) - 2) := by simp [c, coe_principalA]
    have hlin : c * principalRoot d = ε + (d : ℝ) - 1 := by
      dsimp [ε]
      rw [hc']
      linarith
    apply (eq_div_iff hc.ne').2
    calc
      ((k : ℝ) * principalRoot d + l + (m : ℝ) * ε / c) * c =
          (k : ℝ) * (c * principalRoot d) + (l : ℝ) * c + (m : ℝ) * ε := by
            field_simp [hc.ne']
      _ = ((K : ℝ) * ε + (J : ℝ) - 1) := by
        rw [hlin]
        dsimp [K, J]
        push_cast
        ring
  have hKle : K ≤ 1 := by
    by_contra hn
    have hKtwo : 2 ≤ K := by omega
    have hKtwoR : (2 : ℝ) ≤ K := by exact_mod_cast hKtwo
    have hJR : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    have hmult : 2 * ε ≤ (K : ℝ) * ε := by
      exact mul_le_mul_of_nonneg_right hKtwoR hε.le
    have hz' := hz
    change (k : ℝ) * principalRoot d + l + (m : ℝ) * ε / c <
      (2 * ε - 1) / c at hz'
    rw [heq] at hz'
    have hz'' := (div_lt_div_iff_of_pos_right hc).mp hz'
    linarith
  have hKone : K = 1 := by omega
  refine ⟨hKone, hJ, ?_⟩
  rw [heq, hKone]
  dsimp [ε, c, J]
  ring

/-- The normalized parameter ranges give the upper and lower exponential tail rates.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_residue_rates (d : ℕ) (hd : 3 < d)
    (u₁ u₂ v₁ v₂ : ℤ)
    (hu : 0 ≤ principalFiveTermLatticeIndex d u₁ u₂ ∧
      principalFiveTermLatticeIndex d u₁ u₂ < principalFiveTermUpperIndexBound d)
    (hv : 1 ≤ principalFiveTermLatticeIndex d v₁ v₂ ∧
      principalFiveTermLatticeIndex d v₁ v₂ ≤ principalFiveTermUpperIndexBound d) :
    (principalRoot d ^ 3)⁻¹ < principalFiveTermUpperRate d (u₁ + 1)
      (principalFiveTermLatticeArgument d u₁ u₂) ∧
    principalFiveTermLowerRate d (u₁ + 1) v₁
      (principalFiveTermLatticeArgument d u₁ u₂)
      (principalFiveTermLatticeArgument d v₁ v₂) < 0 := by
  have huRate := (principalFiveTermLatticeRate_lt_one_sub_inv_iff d hd u₁ u₂).2 hu.2
  have huvRate := (principalFiveTermLatticeRates_add_pos_iff d hd u₁ u₂ v₁ v₂).2
    (show 0 < principalFiveTermLatticeIndex d u₁ u₂ +
      principalFiveTermLatticeIndex d v₁ v₂ by omega)
  rw [principalFiveTermUpperRate_latticeArgument d hd,
    principalFiveTermLowerRate_latticeArgument d hd]
  constructor <;> linarith

/-- A raw numerator pole in the strip has the position `δ+j/c` for a positive integer
`j`.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_raw_numerator_pole_location (d : ℕ) (hd : 3 < d)
    (m : ℤ) (ζ : ℂ) (x : ℝ)
    (hx : x < principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ))
    (hz : ζ.re ≤ x + (principalRoot d ^ 3 - 1) /
      ((principalA d) 1 0 : ℝ))
    (hord : meromorphicOrderAt (principalFaddeev d m 0)
      (ζ - (m : ℂ) * (principalRoot d : ℂ) ^ 3 /
        ((principalA d) 1 0 : ℂ)) < 0) :
    ∃ j : ℤ, 1 ≤ j ∧
      ζ = ((principalRoot d ^ 3 - 1) /
        ((principalA d) 1 0 : ℝ) +
          (j : ℝ) / ((principalA d) 1 0 : ℝ) : ℂ) ∧
      (j : ℝ) / ((principalA d) 1 0 : ℝ) ≤ x := by
  let z : ℂ := ζ - (m : ℂ) * (principalRoot d : ℂ) ^ 3 /
    ((principalA d) 1 0 : ℂ)
  have hlat : IsPeriodLatticePoint (principalRoot d : ℂ) z := by
    by_contra hn
    have ho := meromorphicOrderAt_principalFaddeev_eq_zero
      d hd m 0 z hn
    change meromorphicOrderAt (principalFaddeev d m 0) z < 0 at hord
    rw [ho] at hord
    exact (not_lt.mpr le_rfl) hord
  rcases hlat with ⟨l, k, hk⟩
  have horder : meromorphicOrderAt (principalFaddeev d m 0)
      ((k : ℂ) * (principalRoot d : ℂ) + l) < 0 := by
    change meromorphicOrderAt (principalFaddeev d m 0) z < 0 at hord
    rw [hk] at hord
    simpa only [add_comm] using hord
  obtain ⟨hK, hQ⟩ :=
    (meromorphicOrderAt_principalFaddeev_neg_iff d hd m 0 k l).1 horder
  have hζ : ζ = ((k : ℝ) * principalRoot d + l +
      (m : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ) : ℂ) := by
    have hc : ((principalA d) 1 0 : ℂ) =
        (((principalA d) 1 0 : ℝ) : ℂ) := by norm_cast
    have hz' : ζ = ((l : ℂ) + (k : ℂ) * (principalRoot d : ℂ)) +
        (m : ℂ) * (principalRoot d : ℂ) ^ 3 /
          ((principalA d) 1 0 : ℂ) := by
      dsimp [z] at hk
      linear_combination hk
    rw [hz', hc]
    push_cast
    ring
  have hc : 0 < ((principalA d) 1 0 : ℝ) := by
    exact_mod_cast principalA_lowerLeft_pos d hd
  have hzreal : ζ.re = (k : ℝ) * principalRoot d + l +
      (m : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ) := by
    rw [hζ]
    norm_cast
  have hupper : (k : ℝ) * principalRoot d + l +
      (m : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ) <
      (2 * principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ) := by
    rw [hzreal] at hz
    have hsum : principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ) +
        (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ) =
        (2 * principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ) := by ring
    linarith
  obtain ⟨hKone, hjpos, heq⟩ := crossed_numerator_pole_arithmetic d hd m k l hK
    (by simpa only [add_zero] using hQ) hupper
  let j : ℤ := 1 + ((d : ℤ) - 1) * k + (principalA d) 1 0 * l
  refine ⟨j, hjpos, ?_, ?_⟩
  · rw [hζ]
    exact_mod_cast heq
  · have hζr : ζ.re = (principalRoot d ^ 3 - 1) /
        ((principalA d) 1 0 : ℝ) +
          (j : ℝ) / ((principalA d) 1 0 : ℝ) := by
      rw [hzreal]
      exact heq
    rw [hζr] at hz
    linarith

/-- At a nonnegative rational grid point the denominator order is nonpositive.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_denominator_order_nonpos_at_rational (d : ℕ) (hd : 3 < d)
    (m v₁ v₂ j : ℤ) (hj : 0 ≤ j)
    (hv : 1 ≤ principalFiveTermLatticeIndex d v₁ v₂) :
    meromorphicOrderAt
      (fun z : ℂ => principalFaddeev d (m + v₁) 0
        (z + principalFiveTermLatticeArgument d v₁ v₂))
      ((j : ℂ) / ((principalA d) 1 0 : ℂ) -
        (m : ℂ) * (principalRoot d : ℂ) ^ 3 / ((principalA d) 1 0 : ℂ)) ≤ 0 := by
  let V := principalFiveTermLatticeIndex d v₁ v₂
  let c : ℤ := (principalA d) 1 0
  let H := principalFiveTermUpperIndexBound d
  let y := principalFiveTermLatticeArgument d v₁ v₂
  let ε := principalRoot d ^ 3
  let Z : ℂ := (j : ℂ) / ((principalA d) 1 0 : ℂ) -
    (m : ℂ) * (principalRoot d : ℂ) ^ 3 / ((principalA d) 1 0 : ℂ) +
      (principalFiveTermLatticeArgument d v₁ v₂ : ℂ)
  rw [meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt]
  change meromorphicOrderAt (principalFaddeev d (m + v₁) 0) Z ≤ 0
  by_cases hlat : IsPeriodLatticePoint (principalRoot d : ℂ) Z
  · rcases hlat with ⟨l, k, hk⟩
    by_contra hn
    have hpos : 0 < meromorphicOrderAt (principalFaddeev d (m + v₁) 0)
        ((k : ℂ) * (principalRoot d : ℂ) + l) := by
      change ¬ meromorphicOrderAt (principalFaddeev d (m + v₁) 0) Z ≤ 0 at hn
      rw [hk] at hn
      simpa only [add_comm, not_le] using hn
    obtain ⟨hK, hQ⟩ :=
      (meromorphicOrderAt_principalFaddeev_pos_iff d hd (m + v₁) 0 k l).1 hpos
    have hρ : Irrational (principalRoot d) := principalRoot_irrational d hd
    have hc : 0 < c := principalA_lowerLeft_pos d hd
    have hH : 0 < H := principalFiveTermUpperIndexBound_pos d hd
    have hV : 0 < V := by omega
    have hε : ε = (c : ℝ) * principalRoot d + 1 - d := by
      convert principalRoot_pow_three_eq d hd using 1
      simp [c, coe_principalA]
      ring
    have hy : y = -((v₁ : ℝ) * ε / c) -
        (ε - 1) * V / ((c : ℝ) * (H : ℝ)) := by
      have h := principalFiveTermLatticeArgument_add_mul_eq d hd v₁ v₂
      dsimp [y, ε, c, H, V]
      linear_combination h
    have harg : (j : ℝ) / c - ((m + v₁ : ℤ) : ℝ) * ε / c -
        (ε - 1) * V / ((c : ℝ) * (H : ℝ)) =
        (k : ℝ) * principalRoot d + l := by
      have hkre := congrArg Complex.re hk
      dsimp [Z] at hkre
      norm_cast at hkre
      rw [Rat.cast_divInt] at hkre
      rw [show principalFiveTermLatticeArgument d v₁ v₂ =
        -((v₁ : ℝ) * ε / c) - (ε - 1) * V / ((c : ℝ) * (H : ℝ)) from hy] at hkre
      dsimp [c, ε, H, V] at hkre ⊢
      push_cast at hkre ⊢
      convert hkre using 1 <;> ring
    have hQneg := faddeevCrossedDenominatorIndex_neg
      (principalRoot d) ε d c H V m v₁ j k l hρ hc hH hV hj hε harg
    have hQneg' : (1 - (d : ℤ)) * k - (d : ℤ) * ((d : ℤ) - 2) * l < 0 := by
      simpa [c, coe_principalA] using hQneg
    omega
  · rw [meromorphicOrderAt_principalFaddeev_eq_zero
      d hd (m + v₁) 0 Z hlat]

/-- A positive rational grid point is not a kernel pole position.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_kernel_position_ne_rational (d : ℕ) (hd : 3 < d)
    (m k j : ℤ) (hj : 0 < j) :
    principalFiveTermStripPolePosition d m k ≠
      ((j : ℝ) / ((principalA d) 1 0 : ℝ) : ℂ) := by
  intro heq
  have hpos := principalFiveTermLatticeArgument_add_mul_eq d hd m k
  have hreal := congrArg Complex.re heq
  have hc : 0 < ((principalA d) 1 0 : ℝ) := by
    exact_mod_cast principalA_lowerLeft_pos d hd
  have hH : 0 < (principalFiveTermUpperIndexBound d : ℝ) := by
    exact_mod_cast principalFiveTermUpperIndexBound_pos d hd
  have hlin : (principalRoot d ^ 3 - 1) *
      principalFiveTermLatticeIndex d m k =
      -(j : ℝ) * principalFiveTermUpperIndexBound d := by
    simp only [principalFiveTermStripPolePosition, Complex.ofReal_re] at hreal
    norm_cast at hreal
    rw [Rat.cast_divInt] at hreal
    rw [hreal] at hpos
    field_simp [hc.ne', hH.ne'] at hpos ⊢
    nlinarith
  have hS : principalFiveTermLatticeIndex d m k ≠ 0 := by
    intro hzero
    rw [hzero] at hlin
    have hjR : (0 : ℝ) < j := by exact_mod_cast hj
    have hzero' : (j : ℝ) * (principalFiveTermUpperIndexBound d : ℝ) = 0 := by
      simpa using hlin.symm
    exact (mul_ne_zero hjR.ne' hH.ne') hzero'
  have hSreal : (principalFiveTermLatticeIndex d m k : ℝ) ≠ 0 := by exact_mod_cast hS
  have heps : principalRoot d ^ 3 - 1 =
      (-(j : ℝ) * principalFiveTermUpperIndexBound d) /
        principalFiveTermLatticeIndex d m k := by
    exact (eq_div_iff hSreal).2 hlin
  have hrat : ∃ q : ℚ, (q : ℝ) = principalRoot d ^ 3 - 1 := by
    refine ⟨(-(j : ℚ) * principalFiveTermUpperIndexBound d) /
      principalFiveTermLatticeIndex d m k, ?_⟩
    push_cast
    exact heps.symm
  exact principalRoot_pow_three_sub_one_irrational d hd hrat

/-- The finite kernel pole positions selected by the common strip window.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private def crossedKernelPoleSet (d : ℕ) (v₁ v₂ : ℤ) : Finset ℂ :=
  (principalFiveTermWindow d
    (-principalFiveTermUpperIndexBound d - principalFiveTermLatticeIndex d v₁ v₂)).image
      (fun mk => principalFiveTermStripPolePosition d mk.1 mk.2)

/-- The positive numerator product pole positions selected by `F`.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private def crossedProductPoleSet (d : ℕ) (F : Finset ℤ) : Finset ℂ :=
  (F.filter (0 < ·)).image (fun (j : ℤ) =>
    (((principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ) +
      (j : ℝ) / ((principalA d) 1 0 : ℝ)) : ℂ))

/-- Distinct grid indices give distinct numerator product pole positions.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_product_position_injective (d : ℕ) (hd : 3 < d) :
    Function.Injective (fun (j : ℤ) =>
      (((principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ) +
        (j : ℝ) / ((principalA d) 1 0 : ℝ)) : ℂ)) := by
  intro j k h
  have hreal : (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ) +
      (j : ℝ) / ((principalA d) 1 0 : ℝ) =
      (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ) +
      (k : ℝ) / ((principalA d) 1 0 : ℝ) := by
    dsimp at h
    exact_mod_cast h
  have hc : ((principalA d) 1 0 : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (principalA_lowerLeft_pos d hd))
  have hjk : (j : ℝ) = k := by
    apply (div_left_inj' hc).mp
    linarith
  exact_mod_cast hjk

/-- Transporting a source pair changes its kernel position by one strip width.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_kernel_position_sub_width (d : ℕ) (hd : 3 < d)
    (m k : ℤ) :
    principalFiveTermStripPolePosition d (m - d) (k + d) =
      principalFiveTermStripPolePosition d m k -
        (((principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ)) : ℂ) := by
  have hS : principalFiveTermLatticeIndex d (m - d) (k + d) =
      principalFiveTermLatticeIndex d m k + principalFiveTermUpperIndexBound d := by
    simp [principalFiveTermLatticeIndex, principalFiveTermUpperIndexBound]
    ring
  have hpos1 := principalFiveTermLatticeArgument_add_mul_eq d hd (m - d) (k + d)
  have hpos2 := principalFiveTermLatticeArgument_add_mul_eq d hd m k
  have hc : ((principalA d) 1 0 : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (principalA_lowerLeft_pos d hd))
  have hH : (principalFiveTermUpperIndexBound d : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (principalFiveTermUpperIndexBound_pos d hd))
  dsimp [principalFiveTermStripPolePosition]
  norm_cast
  rw [hS] at hpos1
  rw [hpos1, hpos2]
  push_cast
  field_simp [hc, hH]
  ring

/-- The kernel and numerator product pole sets are disjoint.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_kernel_product_positions_disjoint (d : ℕ) (hd : 3 < d)
    (m k j : ℤ) (hj : 0 < j) :
    principalFiveTermStripPolePosition d m k ≠
      (((principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ) +
        (j : ℝ) / ((principalA d) 1 0 : ℝ)) : ℂ) := by
  intro heq
  have hshift := crossed_kernel_position_sub_width d hd m k
  rw [heq] at hshift
  have hrational : principalFiveTermStripPolePosition d (m - d) (k + d) =
      (((j : ℝ) / ((principalA d) 1 0 : ℝ)) : ℂ) := by
    convert hshift using 1
    push_cast
    ring
  exact crossed_kernel_position_ne_rational d hd (m - d) (k + d) j hj hrational


/-- Away from listed product poles, the numerator has nonnegative order on the closed
strip.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_numerator_order_nonneg_on_closed_strip (d : ℕ) (hd : 3 < d)
    (m : ℤ) (x β : ℝ) (F : Finset ℤ)
    (hx : x < principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ))
    (hgrid : ∀ j : ℤ, 0 ≤ j →
      ((j : ℝ) / ((principalA d) 1 0 : ℝ) < x ↔
        (j : ℝ) / ((principalA d) 1 0 : ℝ) < β))
    (hF : ∀ j : ℤ, j ∈ F ↔ 0 ≤ j ∧
      (j : ℝ) / ((principalA d) 1 0 : ℝ) < β)
    (hreg : ¬ IsPeriodLatticePoint (principalRoot d : ℂ)
      (((x + (principalRoot d ^ 3 - 1) /
        ((principalA d) 1 0 : ℝ) -
        (m : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ)) : ℂ)))
    (z : ℂ) (hz : z.re ≤ x + (principalRoot d ^ 3 - 1) /
      ((principalA d) 1 0 : ℝ))
    (hnot : z ∉ crossedProductPoleSet d F) :
    0 ≤ meromorphicOrderAt (principalFaddeev d m 0)
      (z - (m : ℂ) * (principalRoot d : ℂ) ^ 3 /
        ((principalA d) 1 0 : ℂ)) := by
  by_contra hn
  have hneg : meromorphicOrderAt (principalFaddeev d m 0)
      (z - (m : ℂ) * (principalRoot d : ℂ) ^ 3 /
        ((principalA d) 1 0 : ℂ)) < 0 := by
    simpa only [not_le] using hn
  obtain ⟨j, hj, hjz, hjx⟩ := crossed_raw_numerator_pole_location d hd m z x hx hz hneg
  by_cases hstrict : (j : ℝ) / ((principalA d) 1 0 : ℝ) < x
  · have hmem : j ∈ F := (hF j).2 ⟨by omega, (hgrid j (by omega)).1 hstrict⟩
    apply hnot
    exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨hmem, by omega⟩, hjz.symm⟩
  · have heq : (j : ℝ) / ((principalA d) 1 0 : ℝ) = x := by linarith
    have hzreal : z = ((x + (principalRoot d ^ 3 - 1) /
        ((principalA d) 1 0 : ℝ)) : ℂ) := by
      rw [hjz]
      exact_mod_cast (show
        (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ) +
          (j : ℝ) / ((principalA d) 1 0 : ℝ) =
          x + (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ) by
            rw [heq]
            ring)
    apply hreg
    have hlat : IsPeriodLatticePoint (principalRoot d : ℂ)
        (z - (m : ℂ) * (principalRoot d : ℂ) ^ 3 /
          ((principalA d) 1 0 : ℂ)) := by
      by_contra hnl
      have ho := meromorphicOrderAt_principalFaddeev_eq_zero
        d hd m 0 _ hnl
      rw [ho] at hneg
      exact (not_lt.mpr le_rfl) hneg
    convert hlat using 1
    rw [hzreal]
    norm_cast

/-- The denominator order is nonpositive throughout the strip.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_denominator_order_nonpos_on_strip (d : ℕ) (hd : 3 < d)
    (m v₁ v₂ : ℤ) (x : ℝ)
    (hx : -((v₁ : ℝ) * principalRoot d ^ 3 /
        ((principalA d) 1 0 : ℝ) +
      principalFiveTermLatticeArgument d v₁ v₂) < x)
    (z : ℂ) (hz : x ≤ z.re) :
    meromorphicOrderAt
      (fun ζ : ℂ => principalFaddeev d (m + v₁) 0
        (ζ + principalFiveTermLatticeArgument d v₁ v₂))
      (z - (m : ℂ) * (principalRoot d : ℂ) ^ 3 /
        ((principalA d) 1 0 : ℂ)) ≤ 0 := by
  apply meromorphicOrderAt_principalFaddeev_add_nonpos d hd m v₁
    (principalFiveTermLatticeArgument d v₁ v₂)
  have hreal :
      (z - (m : ℂ) * (principalRoot d : ℂ) ^ 3 /
        ((principalA d) 1 0 : ℂ)).re =
      z.re - (m : ℝ) * principalRoot d ^ 3 /
        ((principalA d) 1 0 : ℝ) := by
    norm_cast
  rw [hreal]
  have hsum : -((m + v₁ : ℤ) : ℝ) * principalRoot d ^ 3 /
      ((principalA d) 1 0 : ℝ) - principalFiveTermLatticeArgument d v₁ v₂ =
      -((v₁ : ℝ) * principalRoot d ^ 3 /
        ((principalA d) 1 0 : ℝ) +
          principalFiveTermLatticeArgument d v₁ v₂) -
        (m : ℝ) * principalRoot d ^ 3 /
          ((principalA d) 1 0 : ℝ) := by
    push_cast
    ring
  rw [hsum]
  linarith

/-- A point outside the kernel set is not a kernel pole of any shifted summand.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_no_kernel_pole_outside_set (d : ℕ) (hd : 3 < d)
    (v₁ v₂ : ℤ) (x : ℝ)
    (hx₁ : -((v₁ : ℝ) * principalRoot d ^ 3 /
        ((principalA d) 1 0 : ℝ) +
      principalFiveTermLatticeArgument d v₁ v₂) < x)
    (hx₂ : x < -((v₁ : ℝ) * principalRoot d ^ 3 /
        ((principalA d) 1 0 : ℝ) +
      principalFiveTermLatticeArgument d v₁ v₂) +
      (principalRoot d ^ 3 - 1) /
        (((principalA d) 1 0 : ℝ) *
          (principalFiveTermUpperIndexBound d : ℝ)))
    (z : ℂ) (hz₁ : x ≤ z.re)
    (hz₂ : z.re ≤ x + (principalRoot d ^ 3 - 1) /
      ((principalA d) 1 0 : ℝ))
    (hnot : z ∉ crossedKernelPoleSet d v₁ v₂)
    (m : FiveTermIndex (principalA d)) (k : ℤ) :
    z ≠ principalFiveTermStripPolePosition d ((m : ℕ) : ℤ) k := by
  intro heq
  have hm := principalFiveTermIndex_range d hd m
  have hmem := crossed_kernel_mem_window_of_closed_strip d hd v₁ v₂
    ((m : ℕ) : ℤ) k x hx₁ hx₂ hm
    (by rw [← heq]; exact hz₁) (by rw [← heq]; exact hz₂)
  apply hnot
  exact Finset.mem_image.mpr ⟨(((m : ℕ) : ℤ), k), hmem, heq.symm⟩

/-- Every selected kernel pole lies strictly inside the rectangle.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_kernel_poles_inside_strip (d : ℕ) (hd : 3 < d)
    (v₁ v₂ : ℤ) (x : ℝ)
    (hx₁ : -((v₁ : ℝ) * principalRoot d ^ 3 /
        ((principalA d) 1 0 : ℝ) +
      principalFiveTermLatticeArgument d v₁ v₂) < x)
    (hx₂ : x < -((v₁ : ℝ) * principalRoot d ^ 3 /
        ((principalA d) 1 0 : ℝ) +
      principalFiveTermLatticeArgument d v₁ v₂) +
      (principalRoot d ^ 3 - 1) /
        (((principalA d) 1 0 : ℝ) *
          (principalFiveTermUpperIndexBound d : ℝ)))
    (s : ℂ) (hs : s ∈ crossedKernelPoleSet d v₁ v₂) :
    x < s.re ∧ s.re < x + (principalRoot d ^ 3 - 1) /
      ((principalA d) 1 0 : ℝ) ∧ s.im = 0 := by
  obtain ⟨⟨m,k⟩, hmk, rfl⟩ := Finset.mem_image.mp hs
  have hm := (mem_principalFiveTermWindow d hd _ (m,k)).mp hmk
  have hstrip := (crossed_kernel_mem_window_iff_mem_strip d hd v₁ v₂ m k x
    hx₁ hx₂ ⟨hm.1, hm.2.1⟩).1 hmk
  simpa only [principalFiveTermStripPolePosition, Complex.ofReal_re,
    Complex.ofReal_im] using (show
      x < principalFiveTermLatticeArgument d m k +
        (m : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ) ∧
      principalFiveTermLatticeArgument d m k +
        (m : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ) <
        x + (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ) ∧
      (0 : ℝ) = 0 from ⟨hstrip.1,hstrip.2,rfl⟩)

/-- Every selected numerator product pole lies strictly inside the rectangle.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_product_poles_inside_strip (d : ℕ) (hd : 3 < d)
    (v₁ v₂ : ℤ) (x : ℝ) (F : Finset ℤ)
    (hx : x < principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ))
    (hF : ∀ j : ℤ, j ∈ F ↔ 0 ≤ j ∧
      (j : ℝ) / ((principalA d) 1 0 : ℝ) <
        -((v₁ : ℝ) * principalRoot d ^ 3 /
          ((principalA d) 1 0 : ℝ) +
            principalFiveTermLatticeArgument d v₁ v₂))
    (hgrid : ∀ j : ℤ, 0 ≤ j →
      ((j : ℝ) / ((principalA d) 1 0 : ℝ) < x ↔
        (j : ℝ) / ((principalA d) 1 0 : ℝ) <
          -((v₁ : ℝ) * principalRoot d ^ 3 /
            ((principalA d) 1 0 : ℝ) +
              principalFiveTermLatticeArgument d v₁ v₂)))
    (s : ℂ) (hs : s ∈ crossedProductPoleSet d F) :
    x < s.re ∧ s.re < x + (principalRoot d ^ 3 - 1) /
      ((principalA d) 1 0 : ℝ) ∧ s.im = 0 := by
  obtain ⟨j, hjF, rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨hjF, hj⟩ := Finset.mem_filter.mp hjF
  have hc : 0 < ((principalA d) 1 0 : ℝ) := by
    exact_mod_cast principalA_lowerLeft_pos d hd
  have hjpos : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
  have hjx : (j : ℝ) / ((principalA d) 1 0 : ℝ) < x :=
    (hgrid j (by omega)).2 ((hF j).1 hjF).2
  have hdiv : 1 / ((principalA d) 1 0 : ℝ) ≤
      (j : ℝ) / ((principalA d) 1 0 : ℝ) :=
    (div_le_div_iff_of_pos_right hc).2 hjpos
  have hε : (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ) +
      1 / ((principalA d) 1 0 : ℝ) =
      principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ) := by ring
  norm_cast
  rw [Rat.cast_divInt]
  refine ⟨?_, ?_, rfl⟩
  · linarith
  · linarith

/-- The two finite pole sets for the residue rectangle are disjoint.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_pole_sets_disjoint (d : ℕ) (hd : 3 < d)
    (v₁ v₂ : ℤ) (F : Finset ℤ) :
    Disjoint (crossedKernelPoleSet d v₁ v₂) (crossedProductPoleSet d F) := by
  apply Finset.disjoint_left.mpr
  intro s hK hP
  obtain ⟨⟨m,k⟩, _, rfl⟩ := Finset.mem_image.mp hK
  obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hP
  have hjpos : 0 < j := (Finset.mem_filter.mp hj).2
  exact crossed_kernel_product_positions_disjoint d hd m k j hjpos heq.symm

/-- A lower bound for the principal numerator order passes to a shifted kernel
summand when its denominator has nonpositive order.
Used by `crossed_shifted_term_order_ge_neg_one` and
`crossed_shifted_term_order_nonneg`. -/
private lemma crossed_shifted_term_order_ge_bound (d : ℕ) (hd : 3 < d)
    (ℓ v₁ v₂ : ℤ) (w : ℝ) (m : FiveTermIndex (principalA d))
    (z : ℂ) (b : ℤ)
    (hnot : ∀ k : ℤ, z ≠ principalFiveTermStripPolePosition d ((m : ℕ) : ℤ) k)
    (hnum : ((b : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (principalFaddeev d ((m : ℕ) : ℤ) 0)
        (z - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
          ((principalA d) 1 0 : ℂ)))
    (hden : meromorphicOrderAt
      (fun ζ : ℂ => principalFaddeev d (((m : ℕ) : ℤ) + v₁) 0
        (ζ + principalFiveTermLatticeArgument d v₁ v₂))
      (z - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
        ((principalA d) 1 0 : ℂ)) ≤ 0) :
    ((b : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt
      (fun ζ => principalFiveTermResidueKernel d ℓ v₁ w
        (principalFiveTermLatticeArgument d v₁ v₂) ((m : ℕ) : ℤ)
          (ζ - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
            ((principalA d) 1 0 : ℂ))) z := by
  let c : ℂ := ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
    ((principalA d) 1 0 : ℂ)
  have hpole : ∀ k : ℤ, z - c ≠ principalFiveTermLatticeArgument d ((m : ℕ) : ℤ) k := by
    intro k hk
    apply hnot k
    calc
      z = (z - c) + c := by ring
      _ = _ := by rw [hk]; dsimp [principalFiveTermStripPolePosition]; push_cast; ring
  rw [meromorphicOrderAt_fun_comp_sub_const_eq_meromorphicOrderAt]
  rw [meromorphicOrderAt_principalFiveTermResidueKernel d hd ℓ ((m : ℕ) : ℤ) v₁ w
    (principalFiveTermLatticeArgument d v₁ v₂) (z - c) hpole]
  have hneg : 0 ≤ -meromorphicOrderAt
      (fun ζ : ℂ => principalFaddeev d (((m : ℕ) : ℤ) + v₁) 0
        (ζ + principalFiveTermLatticeArgument d v₁ v₂)) (z - c) := by
    rcases lt_or_eq_of_le hden with hlt | heq
    · exact (LinearOrderedAddCommGroupWithTop.neg_pos.mpr (Or.inl hlt)).le
    · rw [heq]
      simp
  have hle := le_add_of_nonneg_right
    (a := meromorphicOrderAt (principalFaddeev d ((m : ℕ) : ℤ) 0) (z - c)) hneg
  rw [← sub_eq_add_neg] at hle
  exact hnum.trans hle

/-- Each shifted kernel summand has pole order at least minus one in the strip.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_shifted_term_order_ge_neg_one (d : ℕ) (hd : 3 < d)
    (ℓ v₁ v₂ : ℤ) (w : ℝ) (m : FiveTermIndex (principalA d))
    (z : ℂ)
    (hnot : ∀ k : ℤ, z ≠ principalFiveTermStripPolePosition d ((m : ℕ) : ℤ) k)
    (hden : meromorphicOrderAt
      (fun ζ : ℂ => principalFaddeev d (((m : ℕ) : ℤ) + v₁) 0
        (ζ + principalFiveTermLatticeArgument d v₁ v₂))
      (z - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
        ((principalA d) 1 0 : ℂ)) ≤ 0) :
    ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt
      (fun ζ => principalFiveTermResidueKernel d ℓ v₁ w
        (principalFiveTermLatticeArgument d v₁ v₂) ((m : ℕ) : ℤ)
          (ζ - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
            ((principalA d) 1 0 : ℂ))) z := by
  exact crossed_shifted_term_order_ge_bound d hd ℓ v₁ v₂ w m z (-1)
    hnot (meromorphicOrderAt_principalFaddeev_ge_neg_one d hd
      ((m : ℕ) : ℤ) 0 _) hden

/-- A shifted summand away from kernel and product poles has nonnegative order.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_shifted_term_order_nonneg (d : ℕ) (hd : 3 < d)
    (ℓ v₁ v₂ : ℤ) (w : ℝ) (m : FiveTermIndex (principalA d))
    (z : ℂ)
    (hnot : ∀ k : ℤ, z ≠ principalFiveTermStripPolePosition d ((m : ℕ) : ℤ) k)
    (hnum : 0 ≤ meromorphicOrderAt (principalFaddeev d ((m : ℕ) : ℤ) 0)
      (z - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
        ((principalA d) 1 0 : ℂ)))
    (hden : meromorphicOrderAt
      (fun ζ : ℂ => principalFaddeev d (((m : ℕ) : ℤ) + v₁) 0
        (ζ + principalFiveTermLatticeArgument d v₁ v₂))
      (z - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
        ((principalA d) 1 0 : ℂ)) ≤ 0) :
    0 ≤ meromorphicOrderAt
      (fun ζ => principalFiveTermResidueKernel d ℓ v₁ w
        (principalFiveTermLatticeArgument d v₁ v₂) ((m : ℕ) : ℤ)
          (ζ - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
            ((principalA d) 1 0 : ℂ))) z := by
  exact crossed_shifted_term_order_ge_bound d hd ℓ v₁ v₂ w m z 0
    hnot hnum hden

/-! ### The rectangle residue identity

The product divisor and kernel divisor give the finite pole set. Elsewhere in the closed
strip, the shifted summands are bounded, so the rectangle theorem applies with removable
product exceptions. Kernel residues are grouped by position across source-index fibers.
-/

/-- The residue sum is locally bounded away from the selected poles.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_residue_sum_bounded_off_poles (d : ℕ) (hd : 3 < d)
    (ℓ v₁ v₂ : ℤ) (w x β : ℝ) (F : Finset ℤ)
    (hβ : -((v₁ : ℝ) * principalRoot d ^ 3 /
        ((principalA d) 1 0 : ℝ) +
      principalFiveTermLatticeArgument d v₁ v₂) < x)
    (hx₂ : x < -((v₁ : ℝ) * principalRoot d ^ 3 /
        ((principalA d) 1 0 : ℝ) +
      principalFiveTermLatticeArgument d v₁ v₂) +
      (principalRoot d ^ 3 - 1) /
        (((principalA d) 1 0 : ℝ) *
          (principalFiveTermUpperIndexBound d : ℝ)))
    (hx : x < principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ))
    (hgrid : ∀ j : ℤ, 0 ≤ j →
      ((j : ℝ) / ((principalA d) 1 0 : ℝ) < x ↔
        (j : ℝ) / ((principalA d) 1 0 : ℝ) < β))
    (hF : ∀ j : ℤ, j ∈ F ↔ 0 ≤ j ∧
      (j : ℝ) / ((principalA d) 1 0 : ℝ) < β)
    (hreg : ∀ (m : FiveTermIndex (principalA d)),
      IsPrincipalFiveTermResidueCrossing d ((m : ℕ) : ℤ)
        (principalFiveTermLatticeArgument d v₁ v₂)
        (x - ((m : ℕ) : ℝ) * principalRoot d ^ 3 /
          ((principalA d) 1 0 : ℝ)))
    (z : ℂ) (hz₁ : x ≤ z.re)
    (hz₂ : z.re ≤ x + (principalRoot d ^ 3 - 1) /
      ((principalA d) 1 0 : ℝ))
    (hK : z ∉ crossedKernelPoleSet d v₁ v₂)
    (hP : z ∉ crossedProductPoleSet d F) :
    IsBoundedUnder (· ≤ ·) (𝓝[≠] z)
      (fun ζ => ‖principalFiveTermResidueSum d ℓ v₁ w
        (principalFiveTermLatticeArgument d v₁ v₂) ζ‖) := by
  apply principalFiveTermResidueSum_bdd_of_order_nonneg d hd
  intro m
  have hnot := crossed_no_kernel_pole_outside_set d hd v₁ v₂ x
    hβ hx₂ z hz₁ hz₂ hK m
  have hright := principalFiveTerm_strip_right_crossing d hd v₁ v₂ x hreg m
  have hright' : ¬ IsPeriodLatticePoint (principalRoot d : ℂ)
      (((x + (principalRoot d ^ 3 - 1) /
        ((principalA d) 1 0 : ℝ) -
        (((m : ℕ) : ℤ) : ℝ) * principalRoot d ^ 3 /
          ((principalA d) 1 0 : ℝ)) : ℂ)) := by
    convert hright.lattice.base using 1
    push_cast
    ring_nf
  have hnum := crossed_numerator_order_nonneg_on_closed_strip d hd
    ((m : ℕ) : ℤ) x β F hx hgrid hF hright' z hz₂ hP
  have hden := crossed_denominator_order_nonpos_on_strip d hd
    ((m : ℕ) : ℤ) v₁ v₂ x hβ z hz₁
  exact crossed_shifted_term_order_nonneg d hd ℓ v₁ v₂ w m z hnot hnum hden

/-- The rectangle has only the selected simple poles and removable raw product
exceptions.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_rectangle_removable (d : ℕ) (hd : 3 < d)
    (ℓ v₁ v₂ : ℤ) (w x β : ℝ) (F : Finset ℤ)
    (hβ : -((v₁ : ℝ) * principalRoot d ^ 3 /
        ((principalA d) 1 0 : ℝ) +
      principalFiveTermLatticeArgument d v₁ v₂) < x)
    (hx₂ : x < -((v₁ : ℝ) * principalRoot d ^ 3 /
        ((principalA d) 1 0 : ℝ) +
      principalFiveTermLatticeArgument d v₁ v₂) +
      (principalRoot d ^ 3 - 1) /
        (((principalA d) 1 0 : ℝ) *
          (principalFiveTermUpperIndexBound d : ℝ)))
    (hx : x < principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ))
    (hgrid : ∀ j : ℤ, 0 ≤ j →
      ((j : ℝ) / ((principalA d) 1 0 : ℝ) < x ↔
        (j : ℝ) / ((principalA d) 1 0 : ℝ) < β))
    (hF : ∀ j : ℤ, j ∈ F ↔ 0 ≤ j ∧
      (j : ℝ) / ((principalA d) 1 0 : ℝ) < β)
    (hreg : ∀ (m : FiveTermIndex (principalA d)),
      IsPrincipalFiveTermResidueCrossing d ((m : ℕ) : ℤ)
        (principalFiveTermLatticeArgument d v₁ v₂)
        (x - ((m : ℕ) : ℝ) * principalRoot d ^ 3 /
          ((principalA d) 1 0 : ℝ))) :
    ∀ Y : ℝ, ∃ E : Finset ℂ,
      Disjoint (crossedKernelPoleSet d v₁ v₂ ∪ crossedProductPoleSet d F) E ∧
      DifferentiableOn ℂ
        (principalFiveTermResidueSum d ℓ v₁ w
          (principalFiveTermLatticeArgument d v₁ v₂))
        ((Icc x (x + (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ)) ×ℂ
          Icc (-Y) Y) \ (↑(crossedKernelPoleSet d v₁ v₂ ∪
            crossedProductPoleSet d F) ∪ ↑E)) ∧
      (∀ e ∈ E, ∀ᶠ ζ in 𝓝[≠] e,
        DifferentiableAt ℂ (principalFiveTermResidueSum d ℓ v₁ w
          (principalFiveTermLatticeArgument d v₁ v₂)) ζ) ∧
      (∀ e ∈ E, IsBoundedUnder (· ≤ ·) (𝓝[≠] e)
        (fun ζ => ‖principalFiveTermResidueSum d ℓ v₁ w
          (principalFiveTermLatticeArgument d v₁ v₂) ζ‖)) := by
  intro Y
  let A : Set ℂ := Icc x
    (x + (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ)) ×ℂ Icc (-Y) Y
  have hA : IsCompact A := isCompact_Icc.reProdIm isCompact_Icc
  apply exists_finset_removable_of_meromorphic_bounded _ A hA _
    (meromorphic_principalFiveTermResidueSum d hd ℓ v₁ w
      (principalFiveTermLatticeArgument d v₁ v₂))
  intro z hz hn
  have hK : z ∉ crossedKernelPoleSet d v₁ v₂ := by
    intro hm
    exact hn (by simp [hm])
  have hP : z ∉ crossedProductPoleSet d F := by
    intro hm
    exact hn (by simp [hm])
  exact crossed_residue_sum_bounded_off_poles d hd ℓ v₁ v₂ w x β F
    hβ hx₂ hx hgrid hF hreg z hz.1.1 hz.1.2 hK hP

/-- A shifted summand with nonnegative order has zero residue limit.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_shifted_term_residue_zero (d : ℕ) (hd : 3 < d)
    (ℓ v₁ v₂ : ℤ) (w : ℝ)
    (m : FiveTermIndex (principalA d)) (s : ℂ)
    (hnot : ∀ k : ℤ, s ≠ principalFiveTermStripPolePosition d ((m : ℕ) : ℤ) k)
    (hnum : 0 ≤ meromorphicOrderAt (principalFaddeev d ((m : ℕ) : ℤ) 0)
      (s - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
        ((principalA d) 1 0 : ℂ)))
    (hden : meromorphicOrderAt
      (fun ζ : ℂ => principalFaddeev d (((m : ℕ) : ℤ) + v₁) 0
        (ζ + principalFiveTermLatticeArgument d v₁ v₂))
      (s - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
        ((principalA d) 1 0 : ℂ)) ≤ 0) :
    Tendsto (fun ζ : ℂ => (ζ - s) *
      principalFiveTermResidueKernel d ℓ v₁ w
        (principalFiveTermLatticeArgument d v₁ v₂) ((m : ℕ) : ℤ)
        (ζ - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
          ((principalA d) 1 0 : ℂ))) (𝓝[≠] s) (𝓝 0) := by
  let f : ℂ → ℂ := fun ζ => principalFiveTermResidueKernel d ℓ v₁ w
    (principalFiveTermLatticeArgument d v₁ v₂) ((m : ℕ) : ℤ)
    (ζ - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
      ((principalA d) 1 0 : ℂ))
  have hf : MeromorphicAt f s := by
    change MeromorphicAt ((principalFiveTermResidueKernel d ℓ v₁ w
      (principalFiveTermLatticeArgument d v₁ v₂) ((m : ℕ) : ℤ)) ∘
        (fun ζ => ζ - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
          ((principalA d) 1 0 : ℂ))) s
    apply (meromorphicAt_comp_sub_const_iff_meromorphicAt).2
    exact meromorphic_principalFiveTermResidueKernel d hd ℓ v₁ w
      (principalFiveTermLatticeArgument d v₁ v₂) ((m : ℕ) : ℤ) _
  have ho := crossed_shifted_term_order_nonneg d hd ℓ v₁ v₂ w m s hnot hnum hden
  obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hf ho
  have hs : Tendsto (fun ζ : ℂ => ζ - s) (𝓝[≠] s) (𝓝 0) := by
    simpa only [sub_self, id_eq] using
      (tendsto_id.sub_const s).mono_left (show 𝓝[≠] s ≤ 𝓝 s from nhdsWithin_le_nhds)
  simpa only [f, zero_mul] using hs.mul hc

/-- Every numerator product pole has a residue limit for the finite residue sum.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_residue_sum_residue_exists_at_product_pole (d : ℕ) (hd : 3 < d)
    (ℓ v₁ v₂ : ℤ) (w x : ℝ)
    (hx : -((v₁ : ℝ) * principalRoot d ^ 3 /
        ((principalA d) 1 0 : ℝ) +
      principalFiveTermLatticeArgument d v₁ v₂) < x)
    (hx₂ : x < -((v₁ : ℝ) * principalRoot d ^ 3 /
        ((principalA d) 1 0 : ℝ) +
      principalFiveTermLatticeArgument d v₁ v₂) +
      (principalRoot d ^ 3 - 1) /
        (((principalA d) 1 0 : ℝ) *
          (principalFiveTermUpperIndexBound d : ℝ)))
    (s : ℂ) (hs₁ : x ≤ s.re)
    (hs₂ : s.re ≤ x + (principalRoot d ^ 3 - 1) /
      ((principalA d) 1 0 : ℝ))
    (hK : s ∉ crossedKernelPoleSet d v₁ v₂) :
    ∃ R : ℂ, Tendsto (fun ζ : ℂ => (ζ - s) *
      principalFiveTermResidueSum d ℓ v₁ w
        (principalFiveTermLatticeArgument d v₁ v₂) ζ)
      (𝓝[≠] s) (𝓝 R) := by
  have hm (m : FiveTermIndex (principalA d)) :
      ∃ R : ℂ, Tendsto (fun ζ : ℂ => (ζ - s) *
        principalFiveTermResidueKernel d ℓ v₁ w
          (principalFiveTermLatticeArgument d v₁ v₂) ((m : ℕ) : ℤ)
          (ζ - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
            ((principalA d) 1 0 : ℂ))) (𝓝[≠] s) (𝓝 R) := by
    have hnot := crossed_no_kernel_pole_outside_set d hd v₁ v₂ x
      hx hx₂ s hs₁ hs₂ hK m
    have hden := crossed_denominator_order_nonpos_on_strip d hd
      ((m : ℕ) : ℤ) v₁ v₂ x hx s hs₁
    let f : ℂ → ℂ := fun ζ => principalFiveTermResidueKernel d ℓ v₁ w
      (principalFiveTermLatticeArgument d v₁ v₂) ((m : ℕ) : ℤ)
      (ζ - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
        ((principalA d) 1 0 : ℂ))
    have hmer : MeromorphicAt f s := by
      change MeromorphicAt ((principalFiveTermResidueKernel d ℓ v₁ w
        (principalFiveTermLatticeArgument d v₁ v₂) ((m : ℕ) : ℤ)) ∘
          (fun ζ => ζ - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
            ((principalA d) 1 0 : ℂ))) s
      apply (meromorphicAt_comp_sub_const_iff_meromorphicAt).2
      exact meromorphic_principalFiveTermResidueKernel d hd ℓ v₁ w
        (principalFiveTermLatticeArgument d v₁ v₂) ((m : ℕ) : ℤ) _
    exact tendsto_sub_mul_of_meromorphicOrderAt_ge_neg_one f s hmer
      (crossed_shifted_term_order_ge_neg_one d hd ℓ v₁ v₂ w m s hnot hden)
  choose R hR using hm
  refine ⟨∑ m : FiveTermIndex (principalA d), R m, ?_⟩
  have hsum := tendsto_finsetSum Finset.univ (fun m _ => hR m)
  convert hsum using 1
  funext ζ
  simp only [principalFiveTermResidueSum, Finset.mul_sum]

/-- The rectangle residue theorem expresses its boundary integral as the finite
residue sum.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_rectangle_identity_of_residue_limits (d : ℕ) (hd : 3 < d)
    (ℓ v₁ v₂ : ℤ) (w x β : ℝ) (F : Finset ℤ)
    (hβeq : β = -((v₁ : ℝ) * principalRoot d ^ 3 /
      ((principalA d) 1 0 : ℝ) +
      principalFiveTermLatticeArgument d v₁ v₂))
    (hβ : -((v₁ : ℝ) * principalRoot d ^ 3 /
        ((principalA d) 1 0 : ℝ) +
      principalFiveTermLatticeArgument d v₁ v₂) < x)
    (hx₂ : x < -((v₁ : ℝ) * principalRoot d ^ 3 /
        ((principalA d) 1 0 : ℝ) +
      principalFiveTermLatticeArgument d v₁ v₂) +
      (principalRoot d ^ 3 - 1) /
        (((principalA d) 1 0 : ℝ) *
          (principalFiveTermUpperIndexBound d : ℝ)))
    (hx : x < principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ))
    (hgrid : ∀ j : ℤ, 0 ≤ j →
      ((j : ℝ) / ((principalA d) 1 0 : ℝ) < x ↔
        (j : ℝ) / ((principalA d) 1 0 : ℝ) < β))
    (hF : ∀ j : ℤ, j ∈ F ↔ 0 ≤ j ∧
      (j : ℝ) / ((principalA d) 1 0 : ℝ) < β)
    (hreg : ∀ (m : FiveTermIndex (principalA d)),
      IsPrincipalFiveTermResidueCrossing d ((m : ℕ) : ℤ)
        (principalFiveTermLatticeArgument d v₁ v₂)
        (x - ((m : ℕ) : ℝ) * principalRoot d ^ 3 /
          ((principalA d) 1 0 : ℝ)))
    (R : ℂ → ℂ)
    (hR : ∀ s ∈ crossedKernelPoleSet d v₁ v₂ ∪ crossedProductPoleSet d F,
      Tendsto (fun ζ : ℂ => (ζ - s) *
        principalFiveTermResidueSum d ℓ v₁ w
          (principalFiveTermLatticeArgument d v₁ v₂) ζ) (𝓝[≠] s) (𝓝 (R s)))
    (Y : ℝ) (hY : 0 < Y) :
    (∫ t : ℝ in x..x + (principalRoot d ^ 3 - 1) /
        ((principalA d) 1 0 : ℝ),
      principalFiveTermResidueSum d ℓ v₁ w
        (principalFiveTermLatticeArgument d v₁ v₂) ((t : ℂ) + (-Y) * I)) -
    (∫ t : ℝ in x..x + (principalRoot d ^ 3 - 1) /
        ((principalA d) 1 0 : ℝ),
      principalFiveTermResidueSum d ℓ v₁ w
        (principalFiveTermLatticeArgument d v₁ v₂) ((t : ℂ) + Y * I)) +
    I • (∫ t : ℝ in -Y..Y, principalFiveTermResidueSum d ℓ v₁ w
      (principalFiveTermLatticeArgument d v₁ v₂)
        (((x + (principalRoot d ^ 3 - 1) /
          ((principalA d) 1 0 : ℝ) : ℝ) : ℂ) + t * I)) -
    I • (∫ t : ℝ in -Y..Y, principalFiveTermResidueSum d ℓ v₁ w
      (principalFiveTermLatticeArgument d v₁ v₂) ((x : ℂ) + t * I)) =
    2 * Real.pi * I *
      ∑ s ∈ crossedKernelPoleSet d v₁ v₂ ∪ crossedProductPoleSet d F, R s := by
  let X : ℝ := x + (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ)
  let L : ℂ → ℂ := principalFiveTermResidueSum d ℓ v₁ w
    (principalFiveTermLatticeArgument d v₁ v₂)
  let S : Finset ℂ := crossedKernelPoleSet d v₁ v₂ ∪ crossedProductPoleSet d F
  have hzre : (((x : ℂ) + (-Y) * I)).re = x := by simp
  have hzim : (((x : ℂ) + (-Y) * I)).im = -Y := by simp
  have hwre : (((X : ℂ) + Y * I)).re = X := by simp
  have hwim : (((X : ℂ) + Y * I)).im = Y := by simp
  obtain ⟨E, hSE, hdiff, hEd, hEb⟩ :=
    crossed_rectangle_removable d hd ℓ v₁ v₂ w x β F
      hβ hx₂ hx hgrid hF hreg Y
  have hwidth : x ≤ X := by
    dsimp [X]
    have hpos : 0 < (principalRoot d ^ 3 - 1) /
        ((principalA d) 1 0 : ℝ) :=
      div_pos (sub_pos.mpr (one_lt_principalRoot_pow_three d hd))
        (by exact_mod_cast principalA_lowerLeft_pos d hd)
    linarith
  have hdiff' := differentiableOn_rect_of_Icc L x X Y S E hwidth hY.le (by
    simpa only [L, S, X] using hdiff)
  have hrect := integral_boundary_rect_eq_sum_residues_of_bounded L
    ((x : ℂ) + (-Y) * I) ((X : ℂ) + Y * I) S E R
    hSE (by
      intro s hs
      obtain hsK | hsP := Finset.mem_union.mp hs
      · obtain ⟨hlo, hhi, him⟩ := crossed_kernel_poles_inside_strip d hd v₁ v₂
          x hβ hx₂ s hsK
        simp only [hzre, hwre, hzim, hwim, him]
        exact ⟨hlo, hhi, by linarith, hY⟩
      · obtain ⟨hlo, hhi, him⟩ := crossed_product_poles_inside_strip d hd
          v₁ v₂ x F hx (by simpa only [hβeq] using hF)
            (by simpa only [hβeq] using hgrid) s hsP
        simp only [hzre, hwre, hzim, hwim, him]
        exact ⟨hlo, hhi, by linarith, hY⟩)
    hdiff' (by intro s hs; exact hR s hs) hEd hEb
  rw [hzre, hzim, hwre, hwim] at hrect
  dsimp only [L, S, X] at hrect
  simpa only [Complex.ofReal_neg] using hrect

/-- The residue fiber in the crossed window `[-H-S_d(v),-S_d(v))`.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private abbrev crossedResidueFiber (d : ℕ) (ℓ v₁ v₂ : ℤ) (w : ℝ)
    (m : FiveTermIndex (principalA d)) (s : ℂ) : ℂ :=
  principalFiveTermWindowResidueFiber d
    (-principalFiveTermUpperIndexBound d - principalFiveTermLatticeIndex d v₁ v₂)
    ℓ v₁ w (principalFiveTermLatticeArgument d v₁ v₂) m s

/-- A pole in a source-index fiber contributes its kernel residue.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_residue_fiber_eq_of_pole (d : ℕ) (hd : 3 < d)
    (ℓ v₁ v₂ : ℤ) (w x : ℝ)
    (hx₁ : -((v₁ : ℝ) * principalRoot d ^ 3 /
        ((principalA d) 1 0 : ℝ) +
      principalFiveTermLatticeArgument d v₁ v₂) < x)
    (hx₂ : x < -((v₁ : ℝ) * principalRoot d ^ 3 /
        ((principalA d) 1 0 : ℝ) +
      principalFiveTermLatticeArgument d v₁ v₂) +
      (principalRoot d ^ 3 - 1) /
        (((principalA d) 1 0 : ℝ) *
          (principalFiveTermUpperIndexBound d : ℝ)))
    (m : FiveTermIndex (principalA d)) (k : ℤ)
    (hlo : x < (principalFiveTermStripPolePosition d ((m : ℕ) : ℤ) k).re)
    (hhi : (principalFiveTermStripPolePosition d ((m : ℕ) : ℤ) k).re <
      x + (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ)) :
    crossedResidueFiber d ℓ v₁ v₂ w m
      (principalFiveTermStripPolePosition d ((m : ℕ) : ℤ) k) =
      principalFiveTermKernelResidue d ℓ v₁ w
        (principalFiveTermLatticeArgument d v₁ v₂) ((m : ℕ) : ℤ)
        (principalFiveTermLatticeArgument d ((m : ℕ) : ℤ) k) := by
  have hmem := (crossed_kernel_mem_window_iff_mem_strip d hd v₁ v₂
    ((m : ℕ) : ℤ) k x hx₁ hx₂ (principalFiveTermIndex_range d hd m)).2 (by
      simpa only [principalFiveTermStripPolePosition, Complex.ofReal_re,
        Int.cast_natCast] using (show
          x < (principalFiveTermStripPolePosition d ((m : ℕ) : ℤ) k).re ∧
          (principalFiveTermStripPolePosition d ((m : ℕ) : ℤ) k).re <
            x + (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ) from
              ⟨hlo,hhi⟩))
  exact principalFiveTermWindowResidueFiber_eq_of_pole d hd
    (-principalFiveTermUpperIndexBound d - principalFiveTermLatticeIndex d v₁ v₂)
    ℓ v₁ w (principalFiveTermLatticeArgument d v₁ v₂) m k hmem

/-- A source-index fiber with no pole contributes zero.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_residue_fiber_eq_zero_of_no_pole (d : ℕ)
    (ℓ v₁ v₂ : ℤ) (w : ℝ) (m : FiveTermIndex (principalA d))
    (s : ℂ)
    (hnot : ∀ k : ℤ, s ≠ principalFiveTermStripPolePosition d ((m : ℕ) : ℤ) k) :
    crossedResidueFiber d ℓ v₁ v₂ w m s = 0 := by
  exact principalFiveTermWindowResidueFiber_eq_zero d
    (-principalFiveTermUpperIndexBound d - principalFiveTermLatticeIndex d v₁ v₂)
    ℓ v₁ w (principalFiveTermLatticeArgument d v₁ v₂) m s hnot

/-- The residue limit of one shifted summand equals its fiber contribution.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_shifted_term_residue_fiber_at_kernel_pole
    (d : ℕ) (hd : 3 < d) (ℓ v₁ v₂ : ℤ) (w x β : ℝ) (F : Finset ℤ)
    (hβ : -((v₁ : ℝ) * principalRoot d ^ 3 /
        ((principalA d) 1 0 : ℝ) +
      principalFiveTermLatticeArgument d v₁ v₂) < x)
    (hx₂ : x < -((v₁ : ℝ) * principalRoot d ^ 3 /
        ((principalA d) 1 0 : ℝ) +
      principalFiveTermLatticeArgument d v₁ v₂) +
      (principalRoot d ^ 3 - 1) /
        (((principalA d) 1 0 : ℝ) *
          (principalFiveTermUpperIndexBound d : ℝ)))
    (hx : x < principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ))
    (hgrid : ∀ j : ℤ, 0 ≤ j →
      ((j : ℝ) / ((principalA d) 1 0 : ℝ) < x ↔
        (j : ℝ) / ((principalA d) 1 0 : ℝ) < β))
    (hF : ∀ j : ℤ, j ∈ F ↔ 0 ≤ j ∧
      (j : ℝ) / ((principalA d) 1 0 : ℝ) < β)
    (hreg : ∀ (m : FiveTermIndex (principalA d)),
      IsPrincipalFiveTermResidueCrossing d ((m : ℕ) : ℤ)
        (principalFiveTermLatticeArgument d v₁ v₂)
        (x - ((m : ℕ) : ℝ) * principalRoot d ^ 3 /
          ((principalA d) 1 0 : ℝ)))
    (s : ℂ) (hs : s ∈ crossedKernelPoleSet d v₁ v₂)
    (m : FiveTermIndex (principalA d)) :
    Tendsto (fun ζ : ℂ => (ζ - s) *
      principalFiveTermResidueKernel d ℓ v₁ w
        (principalFiveTermLatticeArgument d v₁ v₂) ((m : ℕ) : ℤ)
        (ζ - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
          ((principalA d) 1 0 : ℂ))) (𝓝[≠] s)
      (𝓝 (crossedResidueFiber d ℓ v₁ v₂ w m s)) := by
  obtain ⟨hs₁, hs₂, _⟩ := crossed_kernel_poles_inside_strip d hd v₁ v₂ x hβ hx₂ s hs
  by_cases hp : ∃ k : ℤ, s = principalFiveTermStripPolePosition d ((m : ℕ) : ℤ) k
  · obtain ⟨k, rfl⟩ := hp
    rw [crossed_residue_fiber_eq_of_pole d hd ℓ v₁ v₂ w x hβ hx₂ m k
      hs₁ hs₂]
    exact tendsto_sub_mul_principalFiveTermResidueKernel_sub d hd ℓ w
      ((m : ℕ) : ℤ) k v₁ v₂
  · have hnot : ∀ k : ℤ,
        s ≠ principalFiveTermStripPolePosition d ((m : ℕ) : ℤ) k := by
      simpa only [not_exists] using hp
    rw [crossed_residue_fiber_eq_zero_of_no_pole d ℓ v₁ v₂ w m s hnot]
    have hP : s ∉ crossedProductPoleSet d F :=
      Finset.disjoint_left.mp (crossed_pole_sets_disjoint d hd v₁ v₂ F) hs
    have hright := principalFiveTerm_strip_right_crossing d hd v₁ v₂ x hreg m
    have hright' : ¬ IsPeriodLatticePoint (principalRoot d : ℂ)
        (((x + (principalRoot d ^ 3 - 1) /
          ((principalA d) 1 0 : ℝ) -
          (((m : ℕ) : ℤ) : ℝ) * principalRoot d ^ 3 /
            ((principalA d) 1 0 : ℝ)) : ℂ)) := by
      convert hright.lattice.base using 1
      push_cast
      ring_nf
    have hnum := crossed_numerator_order_nonneg_on_closed_strip d hd
      ((m : ℕ) : ℤ) x β F hx hgrid hF hright' s hs₂.le hP
    have hden := crossed_denominator_order_nonpos_on_strip d hd
      ((m : ℕ) : ℤ) v₁ v₂ x hβ s hs₁.le
    exact crossed_shifted_term_residue_zero d hd ℓ v₁ v₂ w m s hnot hnum hden

/-- At a common kernel position, residues of coincident summands add by fibers.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_residue_sum_residue_fibers_at_kernel_pole
    (d : ℕ) (hd : 3 < d) (ℓ v₁ v₂ : ℤ) (w x β : ℝ) (F : Finset ℤ)
    (hβ : -((v₁ : ℝ) * principalRoot d ^ 3 /
        ((principalA d) 1 0 : ℝ) +
      principalFiveTermLatticeArgument d v₁ v₂) < x)
    (hx₂ : x < -((v₁ : ℝ) * principalRoot d ^ 3 /
        ((principalA d) 1 0 : ℝ) +
      principalFiveTermLatticeArgument d v₁ v₂) +
      (principalRoot d ^ 3 - 1) /
        (((principalA d) 1 0 : ℝ) *
          (principalFiveTermUpperIndexBound d : ℝ)))
    (hx : x < principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ))
    (hgrid : ∀ j : ℤ, 0 ≤ j →
      ((j : ℝ) / ((principalA d) 1 0 : ℝ) < x ↔
        (j : ℝ) / ((principalA d) 1 0 : ℝ) < β))
    (hF : ∀ j : ℤ, j ∈ F ↔ 0 ≤ j ∧
      (j : ℝ) / ((principalA d) 1 0 : ℝ) < β)
    (hreg : ∀ (m : FiveTermIndex (principalA d)),
      IsPrincipalFiveTermResidueCrossing d ((m : ℕ) : ℤ)
        (principalFiveTermLatticeArgument d v₁ v₂)
        (x - ((m : ℕ) : ℝ) * principalRoot d ^ 3 /
          ((principalA d) 1 0 : ℝ)))
    (s : ℂ) (hs : s ∈ crossedKernelPoleSet d v₁ v₂) :
    Tendsto (fun ζ : ℂ => (ζ - s) *
      principalFiveTermResidueSum d ℓ v₁ w
        (principalFiveTermLatticeArgument d v₁ v₂) ζ)
      (𝓝[≠] s)
      (𝓝 (∑ m : FiveTermIndex (principalA d),
        crossedResidueFiber d ℓ v₁ v₂ w m s)) := by
  have ht (m : FiveTermIndex (principalA d)) :=
    crossed_shifted_term_residue_fiber_at_kernel_pole d hd ℓ v₁ v₂ w x β F
      hβ hx₂ hx hgrid hF hreg s hs m
  have hsum := tendsto_finsetSum Finset.univ (fun m _ => ht m)
  convert hsum using 1
  funext ζ
  simp only [principalFiveTermResidueSum, Finset.mul_sum]

/-- A window pair has a corresponding finite first-coordinate index.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_window_first_index (d : ℕ) (hd : 3 < d)
    (v₁ v₂ : ℤ) (mk : ℤ × ℤ)
    (hmk : mk ∈ principalFiveTermWindow d
      (-principalFiveTermUpperIndexBound d - principalFiveTermLatticeIndex d v₁ v₂)) :
    ∃ m : FiveTermIndex (principalA d), ((m : ℕ) : ℤ) = mk.1 := by
  obtain ⟨hm0, hm1, _, _⟩ := (mem_principalFiveTermWindow d hd _ mk).mp hmk
  have hc : 0 < (principalA d) 1 0 := principalA_lowerLeft_pos d hd
  have hlt : mk.1.toNat < ((principalA d) 1 0).toNat := by
    apply (Int.toNat_lt_toNat hc).2
    simpa [coe_principalA] using hm1
  refine ⟨⟨mk.1.toNat, hlt⟩, ?_⟩
  simp [Int.toNat_of_nonneg hm0]

/-- Fiber sums at one position equal the selected window-pair sum.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_residue_fibers_at_position (d : ℕ) (hd : 3 < d)
    (ℓ v₁ v₂ : ℤ) (w : ℝ) (s : ℂ) :
    (∑ m : FiveTermIndex (principalA d),
      crossedResidueFiber d ℓ v₁ v₂ w m s) =
      ∑ mk ∈ principalFiveTermWindow d
          (-principalFiveTermUpperIndexBound d - principalFiveTermLatticeIndex d v₁ v₂) with
        principalFiveTermStripPolePosition d mk.1 mk.2 = s,
        principalFiveTermKernelResidue d ℓ v₁ w
          (principalFiveTermLatticeArgument d v₁ v₂) mk.1
          (principalFiveTermLatticeArgument d mk.1 mk.2) := by
  simp only [crossedResidueFiber, principalFiveTermWindowResidueFiber, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro mk hmk
  obtain ⟨m0, hm0⟩ := crossed_window_first_index d hd v₁ v₂ mk hmk
  by_cases hs : principalFiveTermStripPolePosition d mk.1 mk.2 = s
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

/-- Summing over kernel positions recovers the full window residue sum.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_residue_fibers_total (d : ℕ) (hd : 3 < d)
    (ℓ v₁ v₂ : ℤ) (w : ℝ) :
    (∑ s ∈ crossedKernelPoleSet d v₁ v₂,
      ∑ m : FiveTermIndex (principalA d),
        crossedResidueFiber d ℓ v₁ v₂ w m s) =
      ∑ mk ∈ principalFiveTermWindow d
          (-principalFiveTermUpperIndexBound d - principalFiveTermLatticeIndex d v₁ v₂),
        principalFiveTermKernelResidue d ℓ v₁ w
          (principalFiveTermLatticeArgument d v₁ v₂) mk.1
          (principalFiveTermLatticeArgument d mk.1 mk.2) := by
  simp_rw [crossed_residue_fibers_at_position d hd]
  have hmap : ∀ mk ∈ principalFiveTermWindow d
      (-principalFiveTermUpperIndexBound d - principalFiveTermLatticeIndex d v₁ v₂),
      principalFiveTermStripPolePosition d mk.1 mk.2 ∈
        crossedKernelPoleSet d v₁ v₂ := by
    intro mk hmk
    exact Finset.mem_image.mpr ⟨mk, hmk, rfl⟩
  exact Finset.sum_fiberwise_of_maps_to hmap
    (fun mk => principalFiveTermKernelResidue d ℓ v₁ w
      (principalFiveTermLatticeArgument d v₁ v₂) mk.1
      (principalFiveTermLatticeArgument d mk.1 mk.2))

/-- All numerator product poles admit residue limits of the finite residue sum.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_product_residue_limits (d : ℕ) (hd : 3 < d)
    (ℓ v₁ v₂ : ℤ) (w x : ℝ) (F : Finset ℤ)
    (hβ : -((v₁ : ℝ) * principalRoot d ^ 3 /
        ((principalA d) 1 0 : ℝ) +
      principalFiveTermLatticeArgument d v₁ v₂) < x)
    (hx₂ : x < -((v₁ : ℝ) * principalRoot d ^ 3 /
        ((principalA d) 1 0 : ℝ) +
      principalFiveTermLatticeArgument d v₁ v₂) +
      (principalRoot d ^ 3 - 1) /
        (((principalA d) 1 0 : ℝ) *
          (principalFiveTermUpperIndexBound d : ℝ)))
    (hx : x < principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ))
    (hF : ∀ j : ℤ, j ∈ F ↔ 0 ≤ j ∧
      (j : ℝ) / ((principalA d) 1 0 : ℝ) <
        -((v₁ : ℝ) * principalRoot d ^ 3 /
          ((principalA d) 1 0 : ℝ) +
          principalFiveTermLatticeArgument d v₁ v₂))
    (hgrid : ∀ j : ℤ, 0 ≤ j →
      ((j : ℝ) / ((principalA d) 1 0 : ℝ) < x ↔
        (j : ℝ) / ((principalA d) 1 0 : ℝ) <
          -((v₁ : ℝ) * principalRoot d ^ 3 /
            ((principalA d) 1 0 : ℝ) +
            principalFiveTermLatticeArgument d v₁ v₂))) :
    ∃ RP : ℂ → ℂ,
      ∀ s ∈ crossedProductPoleSet d F,
        Tendsto (fun ζ : ℂ => (ζ - s) *
          principalFiveTermResidueSum d ℓ v₁ w
            (principalFiveTermLatticeArgument d v₁ v₂) ζ)
          (𝓝[≠] s) (𝓝 (RP s)) := by
  have hprod (s : ℂ) (hs : s ∈ crossedProductPoleSet d F) :
      ∃ r : ℂ, Tendsto (fun ζ : ℂ => (ζ - s) *
        principalFiveTermResidueSum d ℓ v₁ w
          (principalFiveTermLatticeArgument d v₁ v₂) ζ)
        (𝓝[≠] s) (𝓝 r) := by
    obtain ⟨hlo, hhi, _⟩ := crossed_product_poles_inside_strip d hd
      v₁ v₂ x F hx hF hgrid s hs
    have hK : s ∉ crossedKernelPoleSet d v₁ v₂ :=
      Finset.disjoint_right.mp (crossed_pole_sets_disjoint d hd v₁ v₂ F) hs
    exact crossed_residue_sum_residue_exists_at_product_pole d hd ℓ v₁ v₂ w x
      hβ hx₂ s hlo.le hhi.le hK
  let RP : ℂ → ℂ := fun s => if hs : s ∈ crossedProductPoleSet d F then
    Classical.choose (hprod s hs) else 0
  refine ⟨RP, ?_⟩
  intro s hs
  simpa [RP, hs] using Classical.choose_spec (hprod s hs)

/-- Horizontal tails and the rectangle theorem give the vertical-line integral
difference.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_integral_of_residue_limits (d : ℕ) (hd : 3 < d)
    (ℓ v₁ v₂ : ℤ) (w x β : ℝ) (F : Finset ℤ)
    (hβeq : β = -((v₁ : ℝ) * principalRoot d ^ 3 /
      ((principalA d) 1 0 : ℝ) +
      principalFiveTermLatticeArgument d v₁ v₂))
    (hβ : β < x)
    (hx₂ : x < β +
      (principalRoot d ^ 3 - 1) /
        (((principalA d) 1 0 : ℝ) *
          (principalFiveTermUpperIndexBound d : ℝ)))
    (hx : x < principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ))
    (hgrid : ∀ j : ℤ, 0 ≤ j →
      ((j : ℝ) / ((principalA d) 1 0 : ℝ) < x ↔
        (j : ℝ) / ((principalA d) 1 0 : ℝ) < β))
    (hF : ∀ j : ℤ, j ∈ F ↔ 0 ≤ j ∧
      (j : ℝ) / ((principalA d) 1 0 : ℝ) < β)
    (hreg : ∀ (m : FiveTermIndex (principalA d)),
      IsPrincipalFiveTermResidueCrossing d ((m : ℕ) : ℤ)
        (principalFiveTermLatticeArgument d v₁ v₂)
        (x - ((m : ℕ) : ℝ) * principalRoot d ^ 3 /
          ((principalA d) 1 0 : ℝ)))
    (hupper : (principalRoot d ^ 3)⁻¹ < principalFiveTermUpperRate d ℓ w)
    (hlower : principalFiveTermLowerRate d ℓ v₁ w
      (principalFiveTermLatticeArgument d v₁ v₂) < 0)
    (R : ℂ → ℂ)
    (hR : ∀ s ∈ crossedKernelPoleSet d v₁ v₂ ∪ crossedProductPoleSet d F,
      Tendsto (fun ζ : ℂ => (ζ - s) *
        principalFiveTermResidueSum d ℓ v₁ w
          (principalFiveTermLatticeArgument d v₁ v₂) ζ)
        (𝓝[≠] s) (𝓝 (R s))) :
    (∫ t : ℝ, principalFiveTermResidueSum d ℓ v₁ w
        (principalFiveTermLatticeArgument d v₁ v₂) ((x : ℂ) + t * I) * I) -
      (∫ t : ℝ, principalFiveTermResidueSum d ℓ v₁ w
        (principalFiveTermLatticeArgument d v₁ v₂)
        (((x + (principalRoot d ^ 3 - 1) /
          ((principalA d) 1 0 : ℝ) : ℝ) : ℂ) + t * I) * I) =
      -(2 * Real.pi * I) *
        ∑ s ∈ crossedKernelPoleSet d v₁ v₂ ∪ crossedProductPoleSet d F, R s := by
  have hβ' : -((v₁ : ℝ) * principalRoot d ^ 3 /
      ((principalA d) 1 0 : ℝ) +
      principalFiveTermLatticeArgument d v₁ v₂) < x := by
    simpa only [hβeq] using hβ
  have hx₂' : x < -((v₁ : ℝ) * principalRoot d ^ 3 /
      ((principalA d) 1 0 : ℝ) +
      principalFiveTermLatticeArgument d v₁ v₂) +
      (principalRoot d ^ 3 - 1) /
        (((principalA d) 1 0 : ℝ) *
          (principalFiveTermUpperIndexBound d : ℝ)) := by
    simpa only [hβeq] using hx₂
  let L : ℂ → ℂ := principalFiveTermResidueSum d ℓ v₁ w
    (principalFiveTermLatticeArgument d v₁ v₂)
  let b : ℝ := x + (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ)
  have hright (m : FiveTermIndex (principalA d)) :
      IsPrincipalFiveTermResidueCrossing d ((m : ℕ) : ℤ)
        (principalFiveTermLatticeArgument d v₁ v₂)
        (b - ((m : ℕ) : ℝ) * principalRoot d ^ 3 /
          ((principalA d) 1 0 : ℝ)) :=
    principalFiveTerm_strip_right_crossing d hd v₁ v₂ x hreg m
  have hintleft := integrable_principalFiveTermResidueSum d hd ℓ v₁ w
    (principalFiveTermLatticeArgument d v₁ v₂) x hreg hupper hlower
  have hintright := integrable_principalFiveTermResidueSum d hd ℓ v₁ w
    (principalFiveTermLatticeArgument d v₁ v₂) b hright hupper hlower
  have hbottom := tendsto_intervalIntegral_principalFiveTermResidueSum_lower
    d hd ℓ v₁ w (principalFiveTermLatticeArgument d v₁ v₂) x b hlower
  have htop := tendsto_intervalIntegral_principalFiveTermResidueSum_upper
    d hd ℓ v₁ w (principalFiveTermLatticeArgument d v₁ v₂) x b hupper
  have hrect : ∀ᶠ Y : ℝ in atTop,
      (∫ t : ℝ in x..b, L ((t : ℂ) + (-Y) * I)) -
      (∫ t : ℝ in x..b, L ((t : ℂ) + Y * I)) +
      I • (∫ t : ℝ in -Y..Y, L ((b : ℂ) + t * I)) -
      I • (∫ t : ℝ in -Y..Y, L ((x : ℂ) + t * I)) =
        2 * Real.pi * I *
          ∑ s ∈ crossedKernelPoleSet d v₁ v₂ ∪ crossedProductPoleSet d F, R s := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
    simpa only [L, b] using crossed_rectangle_identity_of_residue_limits
      d hd ℓ v₁ v₂ w x β F hβeq hβ' hx₂' hx hgrid hF hreg R hR Y hY
  simpa only [L, b] using integral_vertical_sub_eq_neg_residue_of_rectangle
    L x b (∑ s ∈ crossedKernelPoleSet d v₁ v₂ ∪
      crossedProductPoleSet d F, R s)
    hintleft hintright hbottom htop hrect

/-- The strip integral difference equals the kernel-window residues plus product-pole
residues.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_strip_residue_identity (d : ℕ) (hd : 3 < d)
    (ℓ v₁ v₂ : ℤ) (w x β : ℝ) (F : Finset ℤ)
    (hβeq : β = -((v₁ : ℝ) * principalRoot d ^ 3 /
      ((principalA d) 1 0 : ℝ) +
      principalFiveTermLatticeArgument d v₁ v₂))
    (hβ : β < x)
    (hx₂ : x < β +
      (principalRoot d ^ 3 - 1) /
        (((principalA d) 1 0 : ℝ) *
          (principalFiveTermUpperIndexBound d : ℝ)))
    (hx : x < principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ))
    (hgrid : ∀ j : ℤ, 0 ≤ j →
      ((j : ℝ) / ((principalA d) 1 0 : ℝ) < x ↔
        (j : ℝ) / ((principalA d) 1 0 : ℝ) < β))
    (hF : ∀ j : ℤ, j ∈ F ↔ 0 ≤ j ∧
      (j : ℝ) / ((principalA d) 1 0 : ℝ) < β)
    (hreg : ∀ (m : FiveTermIndex (principalA d)),
      IsPrincipalFiveTermResidueCrossing d ((m : ℕ) : ℤ)
        (principalFiveTermLatticeArgument d v₁ v₂)
        (x - ((m : ℕ) : ℝ) * principalRoot d ^ 3 /
          ((principalA d) 1 0 : ℝ)))
    (hupper : (principalRoot d ^ 3)⁻¹ < principalFiveTermUpperRate d ℓ w)
    (hlower : principalFiveTermLowerRate d ℓ v₁ w
      (principalFiveTermLatticeArgument d v₁ v₂) < 0) :
    ∃ RP : ℂ → ℂ,
      (∀ s ∈ crossedProductPoleSet d F,
        Tendsto (fun ζ : ℂ => (ζ - s) *
          principalFiveTermResidueSum d ℓ v₁ w
            (principalFiveTermLatticeArgument d v₁ v₂) ζ)
          (𝓝[≠] s) (𝓝 (RP s))) ∧
      ((∫ t : ℝ, principalFiveTermResidueSum d ℓ v₁ w
          (principalFiveTermLatticeArgument d v₁ v₂) ((x : ℂ) + t * I) * I) -
        (∫ t : ℝ, principalFiveTermResidueSum d ℓ v₁ w
          (principalFiveTermLatticeArgument d v₁ v₂)
          (((x + (principalRoot d ^ 3 - 1) /
            ((principalA d) 1 0 : ℝ) : ℝ) : ℂ) + t * I) * I)) =
        -(2 * Real.pi * I) *
          ((∑ mk ∈ principalFiveTermWindow d
              (-principalFiveTermUpperIndexBound d -
                principalFiveTermLatticeIndex d v₁ v₂),
              principalFiveTermKernelResidue d ℓ v₁ w
                (principalFiveTermLatticeArgument d v₁ v₂) mk.1
                (principalFiveTermLatticeArgument d mk.1 mk.2)) +
            ∑ s ∈ crossedProductPoleSet d F, RP s) := by
  have hβ' : -((v₁ : ℝ) * principalRoot d ^ 3 /
      ((principalA d) 1 0 : ℝ) +
      principalFiveTermLatticeArgument d v₁ v₂) < x := by
    simpa only [hβeq] using hβ
  have hx₂' : x < -((v₁ : ℝ) * principalRoot d ^ 3 /
      ((principalA d) 1 0 : ℝ) +
      principalFiveTermLatticeArgument d v₁ v₂) +
      (principalRoot d ^ 3 - 1) /
        (((principalA d) 1 0 : ℝ) *
          (principalFiveTermUpperIndexBound d : ℝ)) := by
    simpa only [hβeq] using hx₂
  obtain ⟨RP, hRP⟩ := crossed_product_residue_limits d hd ℓ v₁ v₂ w x F
    hβ' hx₂' hx (by simpa only [hβeq] using hF)
    (by simpa only [hβeq] using hgrid)
  let R : ℂ → ℂ := fun s => if s ∈ crossedKernelPoleSet d v₁ v₂ then
    ∑ m : FiveTermIndex (principalA d),
      crossedResidueFiber d ℓ v₁ v₂ w m s else RP s
  have hR (s : ℂ)
      (hs : s ∈ crossedKernelPoleSet d v₁ v₂ ∪ crossedProductPoleSet d F) :
      Tendsto (fun ζ : ℂ => (ζ - s) *
        principalFiveTermResidueSum d ℓ v₁ w
          (principalFiveTermLatticeArgument d v₁ v₂) ζ)
        (𝓝[≠] s) (𝓝 (R s)) := by
    by_cases hsK : s ∈ crossedKernelPoleSet d v₁ v₂
    · simpa [R, hsK] using
        crossed_residue_sum_residue_fibers_at_kernel_pole d hd ℓ v₁ v₂ w x β F
          hβ' hx₂' hx hgrid hF hreg s hsK
    · have hsP := (Finset.mem_union.mp hs).resolve_left hsK
      simpa [R, hsK] using hRP s hsP
  have hlim := crossed_integral_of_residue_limits d hd ℓ v₁ v₂ w x β F
    hβeq hβ hx₂ hx hgrid hF hreg hupper hlower R hR
  have hsum : (∑ s ∈ crossedKernelPoleSet d v₁ v₂ ∪
      crossedProductPoleSet d F, R s) =
      (∑ mk ∈ principalFiveTermWindow d
          (-principalFiveTermUpperIndexBound d -
            principalFiveTermLatticeIndex d v₁ v₂),
          principalFiveTermKernelResidue d ℓ v₁ w
            (principalFiveTermLatticeArgument d v₁ v₂) mk.1
            (principalFiveTermLatticeArgument d mk.1 mk.2)) +
        ∑ s ∈ crossedProductPoleSet d F, RP s := by
    rw [Finset.sum_union (crossed_pole_sets_disjoint d hd v₁ v₂ F)]
    have hK : (∑ s ∈ crossedKernelPoleSet d v₁ v₂, R s) =
        ∑ s ∈ crossedKernelPoleSet d v₁ v₂,
          ∑ m : FiveTermIndex (principalA d),
            crossedResidueFiber d ℓ v₁ v₂ w m s := by
      apply Finset.sum_congr rfl
      intro s hs
      simp [R, hs]
    have hP : (∑ s ∈ crossedProductPoleSet d F, R s) =
        ∑ s ∈ crossedProductPoleSet d F, RP s := by
      apply Finset.sum_congr rfl
      intro s hs
      have hnot := Finset.disjoint_right.mp
        (crossed_pole_sets_disjoint d hd v₁ v₂ F) hs
      simp [R, hnot]
    rw [hK, hP, crossed_residue_fibers_total d hd]
  refine ⟨RP, hRP, ?_⟩
  simpa only [hsum] using hlim

/-! ### Crossed-square corrections

The telescoping germ pairs the positive numerator poles with the squares centered at
`j/c`. The square at zero gives the residue difference at `0` and `δ`, including when
`S_d(v)=H` places `δ` outside the strip.
-/

/-- The telescoping germ subtracts the residue limits of the two shifted residue
sums.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_difference_residue_limit (d : ℕ) (hd : 3 < d)
    (ℓ p : ℤ) (w y : ℝ)
    (hw : Complex.exp (2 * Real.pi * I * ((w : ℂ) / (principalRoot d : ℂ) ^ 3)) =
      Complex.exp (2 * Real.pi * I * ((w : ℂ) + (ℓ - 1) * (principalRoot d : ℂ))))
    (hy : Complex.exp (2 * Real.pi * I * ((y : ℂ) / (principalRoot d : ℂ) ^ 3)) =
      Complex.exp (2 * Real.pi * I * ((y : ℂ) + p * (principalRoot d : ℂ))))
    (s A B : ℂ)
    (hA : Tendsto (fun ζ : ℂ => (ζ - s) *
      principalFiveTermResidueSum d ℓ p w y ζ) (𝓝[≠] s) (𝓝 A))
    (hB : Tendsto (fun ζ : ℂ =>
      (ζ - (s + ((principalRoot d : ℂ) ^ 3 - 1) /
        ((principalA d) 1 0 : ℂ))) *
        principalFiveTermResidueSum d ℓ p w y ζ)
      (𝓝[≠] (s + ((principalRoot d : ℂ) ^ 3 - 1) /
        ((principalA d) 1 0 : ℂ))) (𝓝 B)) :
    Tendsto (fun ζ : ℂ => (ζ - s) *
      principalFiveTermDifferenceSum d ℓ p w y ζ)
      (𝓝[≠] s) (𝓝 (A - B)) := by
  let Δ : ℂ := ((principalRoot d : ℂ) ^ 3 - 1) / ((principalA d) 1 0 : ℂ)
  let L : ℂ → ℂ := principalFiveTermResidueSum d ℓ p w y
  let J : ℂ → ℂ := principalFiveTermDifferenceSum d ℓ p w y
  have hshift : Tendsto (fun ζ : ℂ => (ζ - s) * L (ζ + Δ))
      (𝓝[≠] s) (𝓝 B) := by
    have h := hB.comp (tendsto_add_const_nhdsNE Δ s)
    convert h using 1
    funext ζ
    simp only [L, Δ, Function.comp_def]
    ring
  have hdiff := hA.sub hshift
  have hdiff' : Tendsto (fun ζ : ℂ => (ζ - s) * (L ζ - L (ζ + Δ)))
      (𝓝[≠] s) (𝓝 (A - B)) := by
    convert hdiff using 1
    funext ζ
    ring
  have hEq := principalFiveTermResidueSum_sub_shift_eventuallyEq d hd ℓ p w y hw hy s
  have hEqMul : (fun ζ : ℂ => (ζ - s) * (L ζ - L (ζ + Δ)))
      =ᶠ[𝓝[≠] s] (fun ζ => (ζ - s) * J ζ) := by
    filter_upwards [hEq] with ζ hζ
    exact congrArg ((ζ - s) * ·) hζ
  exact hdiff'.congr' hEqMul

/-- The telescoping germ makes the difference kernel meromorphic at a square center.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_difference_meromorphicAt (d : ℕ) (hd : 3 < d)
    (ℓ p : ℤ) (w y : ℝ)
    (hw : Complex.exp (2 * Real.pi * I * ((w : ℂ) / (principalRoot d : ℂ) ^ 3)) =
      Complex.exp (2 * Real.pi * I * ((w : ℂ) + (ℓ - 1) * (principalRoot d : ℂ))))
    (hy : Complex.exp (2 * Real.pi * I * ((y : ℂ) / (principalRoot d : ℂ) ^ 3)) =
      Complex.exp (2 * Real.pi * I * ((y : ℂ) + p * (principalRoot d : ℂ))))
    (s : ℂ) : MeromorphicAt (principalFiveTermDifferenceSum d ℓ p w y) s := by
  let Δ : ℂ := ((principalRoot d : ℂ) ^ 3 - 1) / ((principalA d) 1 0 : ℂ)
  let L : ℂ → ℂ := principalFiveTermResidueSum d ℓ p w y
  have hL := meromorphic_principalFiveTermResidueSum d hd ℓ p w y s
  have hLshift : MeromorphicAt (fun ζ => L (ζ + Δ)) s := by
    change MeromorphicAt (L ∘ fun ζ => ζ + Δ) s
    apply (meromorphicAt_comp_add_const_iff_meromorphicAt).2
    exact meromorphic_principalFiveTermResidueSum d hd ℓ p w y (s + Δ)
  have hEq := principalFiveTermResidueSum_sub_shift_eventuallyEq d hd ℓ p w y hw hy s
  exact (hL.sub hLshift).congr hEq

/-- Below the strip width, the numerator has nonnegative order at a positive grid
point.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_numerator_order_nonneg_below_width (d : ℕ) (hd : 3 < d)
    (m : ℤ) (z : ℂ)
    (hz : z.re ≤ (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ)) :
    0 ≤ meromorphicOrderAt (principalFaddeev d m 0)
      (z - (m : ℂ) * (principalRoot d : ℂ) ^ 3 /
        ((principalA d) 1 0 : ℂ)) := by
  by_contra hn
  have hneg : meromorphicOrderAt (principalFaddeev d m 0)
      (z - (m : ℂ) * (principalRoot d : ℂ) ^ 3 /
        ((principalA d) 1 0 : ℂ)) < 0 := by
    simpa only [not_le] using hn
  have hε : (0 : ℝ) < principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ) :=
    div_pos (lt_trans zero_lt_one (one_lt_principalRoot_pow_three d hd))
      (by exact_mod_cast principalA_lowerLeft_pos d hd)
  obtain ⟨j, hj, _, hjx⟩ := crossed_raw_numerator_pole_location d hd m z 0
    hε (by simpa only [zero_add] using hz) hneg
  have hjR : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hc : (0 : ℝ) < (principalA d) 1 0 := by
    exact_mod_cast principalA_lowerLeft_pos d hd
  have hdiv : (0 : ℝ) < (j : ℝ) / ((principalA d) 1 0 : ℝ) :=
    div_pos hjR hc
  linarith

/-- The residue sum has zero residue limit at a positive rational grid point.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_residue_sum_residue_zero_at_rational (d : ℕ) (hd : 3 < d)
    (ℓ v₁ v₂ : ℤ) (w : ℝ) (j : ℤ)
    (hj : 0 < j)
    (hjδ : (j : ℝ) / ((principalA d) 1 0 : ℝ) ≤
      (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ))
    (hv : 1 ≤ principalFiveTermLatticeIndex d v₁ v₂) :
    Tendsto (fun ζ : ℂ => (ζ - ((j : ℂ) / ((principalA d) 1 0 : ℂ))) *
      principalFiveTermResidueSum d ℓ v₁ w
        (principalFiveTermLatticeArgument d v₁ v₂) ζ)
      (𝓝[≠] ((j : ℂ) / ((principalA d) 1 0 : ℂ))) (𝓝 0) := by
  let s : ℂ := (j : ℂ) / ((principalA d) 1 0 : ℂ)
  have ht (m : FiveTermIndex (principalA d)) :
      Tendsto (fun ζ : ℂ => (ζ - s) *
        principalFiveTermResidueKernel d ℓ v₁ w
          (principalFiveTermLatticeArgument d v₁ v₂) ((m : ℕ) : ℤ)
          (ζ - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
            ((principalA d) 1 0 : ℂ))) (𝓝[≠] s) (𝓝 0) := by
    have hnot : ∀ k : ℤ,
        s ≠ principalFiveTermStripPolePosition d ((m : ℕ) : ℤ) k := by
      intro k heq
      apply crossed_kernel_position_ne_rational d hd ((m : ℕ) : ℤ) k j hj
      calc
        principalFiveTermStripPolePosition d ((m : ℕ) : ℤ) k = s := heq.symm
        _ = (((j : ℝ) / ((principalA d) 1 0 : ℝ)) : ℂ) := by
          dsimp [s]
    have hnum : 0 ≤ meromorphicOrderAt (principalFaddeev d ((m : ℕ) : ℤ) 0)
      (s - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
        ((principalA d) 1 0 : ℂ)) := by
      apply crossed_numerator_order_nonneg_below_width d hd
      have hsre : s.re = (j : ℝ) / ((principalA d) 1 0 : ℝ) := by
        dsimp [s]
        norm_cast
      rw [hsre]
      exact hjδ
    have hden := crossed_denominator_order_nonpos_at_rational d hd
      ((m : ℕ) : ℤ) v₁ v₂ j hj.le hv
    exact crossed_shifted_term_residue_zero d hd ℓ v₁ v₂ w m s hnot hnum hden
  have hsum := tendsto_finsetSum Finset.univ (fun m _ => ht m)
  convert hsum using 1
  · funext ζ
    simp only [s, principalFiveTermResidueSum, Finset.mul_sum]
  · simp

/-- A positive square integral cancels its paired numerator product residue.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_positive_square_correction (d : ℕ) (hd : 3 < d)
    (ℓ v₁ v₂ : ℤ) (w : ℝ) (F : Finset ℤ) (j : ℤ)
    (hjF : j ∈ F) (hj : 0 < j)
    (hjδ : (j : ℝ) / ((principalA d) 1 0 : ℝ) ≤
      (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ))
    (hv : 1 ≤ principalFiveTermLatticeIndex d v₁ v₂)
    (hw : Complex.exp (2 * Real.pi * I * ((w : ℂ) / (principalRoot d : ℂ) ^ 3)) =
      Complex.exp (2 * Real.pi * I * ((w : ℂ) + (ℓ - 1) * (principalRoot d : ℂ))))
    (hy : Complex.exp (2 * Real.pi * I *
        ((principalFiveTermLatticeArgument d v₁ v₂ : ℂ) /
          (principalRoot d : ℂ) ^ 3)) =
      Complex.exp (2 * Real.pi * I *
        ((principalFiveTermLatticeArgument d v₁ v₂ : ℂ) +
          v₁ * (principalRoot d : ℂ))))
    (RP : ℂ → ℂ)
    (hRP : ∀ s ∈ crossedProductPoleSet d F,
      Tendsto (fun ζ : ℂ => (ζ - s) *
        principalFiveTermResidueSum d ℓ v₁ w
          (principalFiveTermLatticeArgument d v₁ v₂) ζ)
        (𝓝[≠] s) (𝓝 (RP s))) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      rectBoundaryIntegral
        (principalFiveTermDifferenceSum d ℓ v₁ w
          (principalFiveTermLatticeArgument d v₁ v₂))
        ((j : ℂ) / ((principalA d) 1 0 : ℂ) - (r + r * I))
        ((j : ℂ) / ((principalA d) 1 0 : ℂ) + (r + r * I)) =
      -(2 * Real.pi * I) *
        RP (((principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ) +
          (j : ℝ) / ((principalA d) 1 0 : ℝ)) : ℂ) := by
  let s : ℂ := (j : ℂ) / ((principalA d) 1 0 : ℂ)
  let Δ : ℂ := ((principalRoot d : ℂ) ^ 3 - 1) / ((principalA d) 1 0 : ℂ)
  have hp : s + Δ ∈ crossedProductPoleSet d F := by
    apply Finset.mem_image.mpr
    refine ⟨j, Finset.mem_filter.mpr ⟨hjF, hj⟩, ?_⟩
    dsimp [s, Δ]
    norm_cast
    ring
  have hA := crossed_residue_sum_residue_zero_at_rational d hd ℓ v₁ v₂ w j
    hj hjδ hv
  have hB := hRP (s + Δ) hp
  have hJres : Tendsto (fun ζ : ℂ => (ζ - s) *
      principalFiveTermDifferenceSum d ℓ v₁ w
        (principalFiveTermLatticeArgument d v₁ v₂) ζ)
      (𝓝[≠] s) (𝓝 (-RP (s + Δ))) := by
    simpa only [zero_sub] using
      crossed_difference_residue_limit d hd ℓ v₁ w
        (principalFiveTermLatticeArgument d v₁ v₂) hw hy s 0 (RP (s + Δ))
        (by simpa only [s] using hA) (by simpa only [Δ] using hB)
  have hJmer := crossed_difference_meromorphicAt d hd ℓ v₁ w
    (principalFiveTermLatticeArgument d v₁ v₂) hw hy s
  have hsquare := eventually_rectBoundaryIntegral_square_eq_residue hJmer hJres
  have heq : (((principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ) +
      (j : ℝ) / ((principalA d) 1 0 : ℝ)) : ℂ) = s + Δ := by
    dsimp [s, Δ]
    norm_cast
    ring
  simpa only [heq, s, mul_neg, neg_mul] using hsquare

/-- The sum of kernel residues over all source-index fibers at a fixed position.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private def crossedResidueAtPosition (d : ℕ) (ℓ v₁ v₂ : ℤ)
    (w : ℝ) (s : ℂ) : ℂ := by
  classical
  exact ∑ m : FiveTermIndex (principalA d),
    if h : ∃ k : ℤ, s = principalFiveTermStripPolePosition d ((m : ℕ) : ℤ) k then
      principalFiveTermKernelResidue d ℓ v₁ w
        (principalFiveTermLatticeArgument d v₁ v₂) ((m : ℕ) : ℤ)
        (s - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
          ((principalA d) 1 0 : ℂ))
    else 0

/-- At a special position the residue-sum limit is the sum of its kernel fibers.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_residue_sum_limit_at_special_position (d : ℕ) (hd : 3 < d)
    (ℓ v₁ v₂ : ℤ) (w : ℝ) (s : ℂ)
    (hs : s.re ≤ (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ))
    (hden : ∀ m : FiveTermIndex (principalA d),
      meromorphicOrderAt
        (fun ζ : ℂ => principalFaddeev d (((m : ℕ) : ℤ) + v₁) 0
          (ζ + principalFiveTermLatticeArgument d v₁ v₂))
        (s - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
          ((principalA d) 1 0 : ℂ)) ≤ 0) :
    Tendsto (fun ζ : ℂ => (ζ - s) *
      principalFiveTermResidueSum d ℓ v₁ w
        (principalFiveTermLatticeArgument d v₁ v₂) ζ)
      (𝓝[≠] s) (𝓝 (crossedResidueAtPosition d ℓ v₁ v₂ w s)) := by
  classical
  have ht (m : FiveTermIndex (principalA d)) :
      Tendsto (fun ζ : ℂ => (ζ - s) *
        principalFiveTermResidueKernel d ℓ v₁ w
          (principalFiveTermLatticeArgument d v₁ v₂) ((m : ℕ) : ℤ)
          (ζ - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
            ((principalA d) 1 0 : ℂ))) (𝓝[≠] s)
        (𝓝 (if h : ∃ k : ℤ,
          s = principalFiveTermStripPolePosition d ((m : ℕ) : ℤ) k then
            principalFiveTermKernelResidue d ℓ v₁ w
              (principalFiveTermLatticeArgument d v₁ v₂) ((m : ℕ) : ℤ)
              (s - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
                ((principalA d) 1 0 : ℂ))
          else 0)) := by
    split_ifs with hp
    · obtain ⟨k, hk⟩ := hp
      have hlim := tendsto_sub_mul_principalFiveTermResidueKernel_sub d hd ℓ w
        ((m : ℕ) : ℤ) k v₁ v₂
      rw [hk]
      convert hlim using 1
      dsimp [principalFiveTermStripPolePosition]
      norm_cast
      ring_nf
    · have hnot : ∀ k : ℤ,
          s ≠ principalFiveTermStripPolePosition d ((m : ℕ) : ℤ) k := by
        simpa only [not_exists] using hp
      have hnum := crossed_numerator_order_nonneg_below_width d hd
        ((m : ℕ) : ℤ) s hs
      exact crossed_shifted_term_residue_zero d hd ℓ v₁ v₂ w m s hnot hnum (hden m)
  have hsum := tendsto_finsetSum Finset.univ (fun m _ => ht m)
  unfold crossedResidueAtPosition
  convert hsum using 1
  funext ζ
  simp only [principalFiveTermResidueSum, Finset.mul_sum]

/-- The residue-sum limit at zero is its kernel-fiber sum.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_residue_sum_limit_at_zero (d : ℕ) (hd : 3 < d)
    (ℓ v₁ v₂ : ℤ) (w : ℝ)
    (hv : 1 ≤ principalFiveTermLatticeIndex d v₁ v₂) :
    Tendsto (fun ζ : ℂ => ζ *
      principalFiveTermResidueSum d ℓ v₁ w
        (principalFiveTermLatticeArgument d v₁ v₂) ζ)
      (𝓝[≠] 0) (𝓝 (crossedResidueAtPosition d ℓ v₁ v₂ w 0)) := by
  have hδ : (0 : ℝ) ≤ (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ) :=
    (div_pos (sub_pos.mpr (one_lt_principalRoot_pow_three d hd))
      (by exact_mod_cast principalA_lowerLeft_pos d hd)).le
  have hden (m : FiveTermIndex (principalA d)) :
      meromorphicOrderAt
        (fun ζ : ℂ => principalFaddeev d (((m : ℕ) : ℤ) + v₁) 0
          (ζ + principalFiveTermLatticeArgument d v₁ v₂))
        (0 - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
          ((principalA d) 1 0 : ℂ)) ≤ 0 := by
    convert crossed_denominator_order_nonpos_at_rational d hd
      ((m : ℕ) : ℤ) v₁ v₂ 0 (by omega) hv using 1
    push_cast
    ring_nf
  simpa only [sub_zero, Complex.zero_re] using
    crossed_residue_sum_limit_at_special_position d hd ℓ v₁ v₂ w 0 hδ hden

/-- The residue-sum limit at the strip width is its kernel-fiber sum.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_residue_sum_limit_at_width (d : ℕ) (hd : 3 < d)
    (ℓ v₁ v₂ : ℤ) (w : ℝ)
    (hv : principalFiveTermLatticeIndex d v₁ v₂ ≤
      principalFiveTermUpperIndexBound d) :
    let δ : ℝ := (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ)
    Tendsto (fun ζ : ℂ => (ζ - (δ : ℂ)) *
      principalFiveTermResidueSum d ℓ v₁ w
        (principalFiveTermLatticeArgument d v₁ v₂) ζ)
      (𝓝[≠] (δ : ℂ))
      (𝓝 (crossedResidueAtPosition d ℓ v₁ v₂ w (δ : ℂ))) := by
  dsimp
  let δ : ℝ := (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ)
  have hβ := crossed_width_ge_beta d hd v₁ v₂ hv
  have hden (m : FiveTermIndex (principalA d)) :
      meromorphicOrderAt
        (fun ζ : ℂ => principalFaddeev d (((m : ℕ) : ℤ) + v₁) 0
          (ζ + principalFiveTermLatticeArgument d v₁ v₂))
        ((δ : ℂ) - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
          ((principalA d) 1 0 : ℂ)) ≤ 0 := by
    apply meromorphicOrderAt_principalFaddeev_add_nonpos d hd
    have hre : ((δ : ℂ) - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
        ((principalA d) 1 0 : ℂ)).re =
        δ - ((m : ℕ) : ℝ) * principalRoot d ^ 3 /
          ((principalA d) 1 0 : ℝ) := by norm_cast
    rw [hre]
    have hsum : (-((((m : ℕ) : ℤ) + v₁ : ℤ) : ℝ)) * principalRoot d ^ 3 /
        ((principalA d) 1 0 : ℝ) - principalFiveTermLatticeArgument d v₁ v₂ =
        -((v₁ : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ) +
          principalFiveTermLatticeArgument d v₁ v₂) -
          ((m : ℕ) : ℝ) * principalRoot d ^ 3 /
            ((principalA d) 1 0 : ℝ) := by
      push_cast
      ring
    rw [hsum]
    dsimp [δ]
    linarith
  have hs : (δ : ℂ).re ≤ (principalRoot d ^ 3 - 1) /
      ((principalA d) 1 0 : ℝ) := by
    dsimp [δ]
    norm_cast
  exact crossed_residue_sum_limit_at_special_position d hd ℓ v₁ v₂ w
    (δ : ℂ) hs hden

/-- The zero square integral is `2πi` times the residue difference at zero and `δ`.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_zero_square_correction (d : ℕ) (hd : 3 < d)
    (ℓ v₁ v₂ : ℤ) (w : ℝ)
    (hv₁ : 1 ≤ principalFiveTermLatticeIndex d v₁ v₂)
    (hv₂ : principalFiveTermLatticeIndex d v₁ v₂ ≤
      principalFiveTermUpperIndexBound d)
    (hw : Complex.exp (2 * Real.pi * I * ((w : ℂ) / (principalRoot d : ℂ) ^ 3)) =
      Complex.exp (2 * Real.pi * I * ((w : ℂ) + (ℓ - 1) * (principalRoot d : ℂ))))
    (hy : Complex.exp (2 * Real.pi * I *
        ((principalFiveTermLatticeArgument d v₁ v₂ : ℂ) /
          (principalRoot d : ℂ) ^ 3)) =
      Complex.exp (2 * Real.pi * I *
        ((principalFiveTermLatticeArgument d v₁ v₂ : ℂ) +
          v₁ * (principalRoot d : ℂ)))) :
    let δ : ℝ := (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ)
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      rectBoundaryIntegral
        (principalFiveTermDifferenceSum d ℓ v₁ w
          (principalFiveTermLatticeArgument d v₁ v₂))
        (-(r + r * I)) (r + r * I) =
      2 * Real.pi * I *
        (crossedResidueAtPosition d ℓ v₁ v₂ w 0 -
          crossedResidueAtPosition d ℓ v₁ v₂ w (δ : ℂ)) := by
  dsimp
  let δR : ℝ := (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ)
  let δ : ℂ := ((principalRoot d : ℂ) ^ 3 - 1) / ((principalA d) 1 0 : ℂ)
  have hA := crossed_residue_sum_limit_at_zero d hd ℓ v₁ v₂ w hv₁
  have hB := crossed_residue_sum_limit_at_width d hd ℓ v₁ v₂ w hv₂
  change Tendsto (fun ζ : ℂ => (ζ - (δR : ℂ)) *
      principalFiveTermResidueSum d ℓ v₁ w
        (principalFiveTermLatticeArgument d v₁ v₂) ζ)
      (𝓝[≠] (δR : ℂ))
      (𝓝 (crossedResidueAtPosition d ℓ v₁ v₂ w (δR : ℂ))) at hB
  have hδ : (δR : ℂ) = δ := by
    dsimp [δR, δ]
    norm_cast
  rw [hδ] at hB
  have hB' : Tendsto (fun ζ : ℂ => (ζ - δ) *
      principalFiveTermResidueSum d ℓ v₁ w
        (principalFiveTermLatticeArgument d v₁ v₂) ζ)
      (𝓝[≠] δ) (𝓝 (crossedResidueAtPosition d ℓ v₁ v₂ w δ)) := by
    exact hB
  have hJres := crossed_difference_residue_limit d hd ℓ v₁ w
    (principalFiveTermLatticeArgument d v₁ v₂) hw hy 0
    (crossedResidueAtPosition d ℓ v₁ v₂ w 0)
    (crossedResidueAtPosition d ℓ v₁ v₂ w δ)
    (by simpa only [sub_zero] using hA)
    (by simpa only [zero_add] using hB')
  have hJmer := crossed_difference_meromorphicAt d hd ℓ v₁ w
    (principalFiveTermLatticeArgument d v₁ v₂) hw hy 0
  have hsquare := eventually_rectBoundaryIntegral_square_eq_residue hJmer hJres
  change ∀ᶠ r : ℝ in 𝓝[>] 0,
    rectBoundaryIntegral
      (principalFiveTermDifferenceSum d ℓ v₁ w
        (principalFiveTermLatticeArgument d v₁ v₂))
      (-(r + r * I)) (r + r * I) =
      2 * Real.pi * I *
        (crossedResidueAtPosition d ℓ v₁ v₂ w 0 -
          crossedResidueAtPosition d ℓ v₁ v₂ w (δR : ℂ))
  rw [hδ]
  simpa only [zero_sub, zero_add] using hsquare

/-! ### Finite value comparison

The window residues have `F⁻` in both factors. Comparing the zero-position fibers at
`0` and `δ` changes the numerator in the zero class to `F⁺(0)`; the window bijection
then produces the finite group sum.
-/

/-- Every residue in the negative-index window has `F⁻` numerator and denominator
types.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_window_kernel_residue_type (d : ℕ) (hd : 3 < d)
    [NeZero (principalDilogOrder d)] (u₁ u₂ v₁ v₂ : ℤ)
    (hv : 1 ≤ principalFiveTermLatticeIndex d v₁ v₂)
    (mk : ℤ × ℤ)
    (hmk : mk ∈ principalFiveTermWindow d
      (-principalFiveTermUpperIndexBound d - principalFiveTermLatticeIndex d v₁ v₂)) :
    principalFiveTermKernelResidue d (u₁ + 1) v₁
      (principalFiveTermLatticeArgument d u₁ u₂)
      (principalFiveTermLatticeArgument d v₁ v₂) mk.1
      (principalFiveTermLatticeArgument d mk.1 mk.2) =
    (principalRoot d : ℂ) ^ 3 / (2 * Real.pi * I * (1 - (principalRoot d : ℂ) ^ 3)) *
      principalDilogBicharacter d (principalFiveTermCharacteristicResidue d mk.1 mk.2)
        (principalFiveTermCharacteristicResidue d u₁ u₂) *
      (principalDilogEMinus d (principalFiveTermCharacteristicResidue d mk.1 mk.2) /
        principalDilogEMinus d
          (principalFiveTermCharacteristicResidue d mk.1 mk.2 +
            principalFiveTermCharacteristicResidue d v₁ v₂)) := by
  obtain ⟨_, _, hlo, hhi⟩ := (mem_principalFiveTermWindow d hd _ mk).mp hmk
  have hS : principalFiveTermLatticeIndex d mk.1 mk.2 < 0 := by omega
  have hSv : principalFiveTermLatticeIndex d (mk.1 + v₁) (mk.2 + v₂) < 0 := by
    rw [principalFiveTermLatticeIndex_add]
    omega
  rw [principalFiveTermKernelResidue_eq_of_types d hd mk.1 mk.2 u₁ u₂ v₁ v₂]
  simp only [not_le.mpr hS, not_le.mpr hSv, ↓reduceIte]
  rw [principalFiveTermCharacteristicResidue_add]

/-- The window residues equal the finite-group sum with `F⁻` numerator values.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_window_residue_sum_eq (d : ℕ) (hd : 3 < d)
    [NeZero (principalDilogOrder d)] (u₁ u₂ v₁ v₂ : ℤ)
    (hv : 1 ≤ principalFiveTermLatticeIndex d v₁ v₂) :
    (∑ mk ∈ principalFiveTermWindow d
        (-principalFiveTermUpperIndexBound d - principalFiveTermLatticeIndex d v₁ v₂),
      principalFiveTermKernelResidue d (u₁ + 1) v₁
        (principalFiveTermLatticeArgument d u₁ u₂)
        (principalFiveTermLatticeArgument d v₁ v₂) mk.1
        (principalFiveTermLatticeArgument d mk.1 mk.2)) =
      (principalRoot d : ℂ) ^ 3 / (2 * Real.pi * I * (1 - (principalRoot d : ℂ) ^ 3)) *
        ∑ g : principalDilogGroup d,
          principalDilogBicharacter d g
            (principalFiveTermCharacteristicResidue d u₁ u₂) *
          (principalDilogEMinus d g /
            principalDilogEMinus d (g + principalFiveTermCharacteristicResidue d v₁ v₂)) := by
  let f : (Fin 2 → ZMod (principalDilogOrder d)) → ℂ := fun g =>
    principalDilogBicharacter d g (principalFiveTermCharacteristicResidue d u₁ u₂) *
      (principalDilogEMinus d g /
        principalDilogEMinus d (g + principalFiveTermCharacteristicResidue d v₁ v₂))
  calc
    _ = ∑ mk ∈ principalFiveTermWindow d
        (-principalFiveTermUpperIndexBound d - principalFiveTermLatticeIndex d v₁ v₂),
          (principalRoot d : ℂ) ^ 3 /
            (2 * Real.pi * I * (1 - (principalRoot d : ℂ) ^ 3)) *
            f (principalFiveTermCharacteristicResidue d mk.1 mk.2) := by
      apply Finset.sum_congr rfl
      intro mk hmk
      simpa only [f, mul_assoc] using
        crossed_window_kernel_residue_type d hd u₁ u₂ v₁ v₂ hv mk hmk
    _ = _ := by
      rw [← Finset.mul_sum]
      rw [sum_principalFiveTermWindow d hd _ f]

/-- A fiber residue sum at a position equals the corresponding filtered window sum.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_residue_at_position_eq_window (d : ℕ) (hd : 3 < d)
    (ℓ v₁ v₂ : ℤ) (w : ℝ) (a : ℤ) (s : ℂ)
    (hmem : ∀ (m k : ℤ), 0 ≤ m → m < (d : ℤ) * ((d : ℤ) - 2) →
      s = principalFiveTermStripPolePosition d m k →
      (m, k) ∈ principalFiveTermWindow d a) :
    crossedResidueAtPosition d ℓ v₁ v₂ w s =
      ∑ mk ∈ principalFiveTermWindow d a with
        principalFiveTermStripPolePosition d mk.1 mk.2 = s,
        principalFiveTermKernelResidue d ℓ v₁ w
          (principalFiveTermLatticeArgument d v₁ v₂) mk.1
          (principalFiveTermLatticeArgument d mk.1 mk.2) := by
  classical
  let M : Finset (FiveTermIndex (principalA d)) :=
    Finset.univ.filter (fun m => ∃ k : ℤ,
      s = principalFiveTermStripPolePosition d ((m : ℕ) : ℤ) k)
  have hsum : crossedResidueAtPosition d ℓ v₁ v₂ w s =
      ∑ m ∈ M,
        principalFiveTermKernelResidue d ℓ v₁ w
          (principalFiveTermLatticeArgument d v₁ v₂) ((m : ℕ) : ℤ)
          (s - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
            ((principalA d) 1 0 : ℂ)) := by
    unfold crossedResidueAtPosition M
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m _
    split_ifs <;> rfl
  rw [hsum]
  dsimp only [M]
  apply Finset.sum_bij
    (fun (m : FiveTermIndex (principalA d)) (hm : m ∈ M) =>
      (((m : ℕ) : ℤ),
        Classical.choose (Finset.mem_filter.mp hm).2))
  · intro m hm
    have hp := Classical.choose_spec (Finset.mem_filter.mp hm).2
    have hrange := principalFiveTermIndex_range d hd m
    exact Finset.mem_filter.mpr
      ⟨hmem _ _ hrange.1 hrange.2 hp, hp.symm⟩
  · intro m hm n hn hmn
    apply Fin.ext
    have h := congrArg Prod.fst hmn
    dsimp at h
    exact_mod_cast h
  · intro mk hmk
    obtain ⟨hmkW, hmkP⟩ := Finset.mem_filter.mp hmk
    obtain ⟨hm0, hm1, _, _⟩ := (mem_principalFiveTermWindow d hd a mk).mp hmkW
    have hc : 0 < (principalA d) 1 0 := principalA_lowerLeft_pos d hd
    have hlt : mk.1.toNat < ((principalA d) 1 0).toNat := by
      apply (Int.toNat_lt_toNat hc).2
      simpa [coe_principalA] using hm1
    let m : FiveTermIndex (principalA d) := ⟨mk.1.toNat, hlt⟩
    have hmeq : (((m : ℕ) : ℤ)) = mk.1 := by
      exact Int.toNat_of_nonneg hm0
    have hmM : m ∈ M := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, mk.2, ?_⟩
      rw [hmeq]
      exact hmkP.symm
    refine ⟨m, hmM, Prod.ext hmeq ?_⟩
    apply principalFiveTermStripPolePosition_injective d hd mk.1
    have hp := Classical.choose_spec (Finset.mem_filter.mp hmM).2
    have hp' : s = principalFiveTermStripPolePosition d mk.1
        (Classical.choose (Finset.mem_filter.mp hmM).2) := by
      simpa only [hmeq] using hp
    exact hp'.symm.trans hmkP.symm
  · intro m hm
    have hp := Classical.choose_spec (Finset.mem_filter.mp hm).2
    dsimp
    congr 1
    calc
      s - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
          ((principalA d) 1 0 : ℂ) =
        principalFiveTermStripPolePosition d ((m : ℕ) : ℤ)
          (Classical.choose (Finset.mem_filter.mp hm).2) -
          ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
            ((principalA d) 1 0 : ℂ) := by
        congr 1
      _ = _ := by
        dsimp [principalFiveTermStripPolePosition]
        push_cast
        ring

/-- A common-line pole has a prescribed position exactly when its lattice index is
prescribed.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_position_eq_iff_index_eq (d : ℕ) (hd : 3 < d)
    (m k a : ℤ) :
    principalFiveTermStripPolePosition d m k =
        ((-(principalRoot d ^ 3 - 1) * (a : ℝ) /
          (((principalA d) 1 0 : ℝ) *
            (principalFiveTermUpperIndexBound d : ℝ))) : ℂ) ↔
      principalFiveTermLatticeIndex d m k = a := by
  have hscale : (principalRoot d ^ 3 - 1) /
      (((principalA d) 1 0 : ℝ) *
        (principalFiveTermUpperIndexBound d : ℝ)) ≠ 0 :=
    ne_of_gt (crossed_spacing_pos d hd)
  have hreal :
      principalFiveTermLatticeArgument d m k +
        (m : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ) =
          -(principalRoot d ^ 3 - 1) * (a : ℝ) /
            (((principalA d) 1 0 : ℝ) *
              (principalFiveTermUpperIndexBound d : ℝ)) ↔
        principalFiveTermLatticeIndex d m k = a := by
    rw [principalFiveTermLatticeArgument_add_mul_eq d hd]
    have hform (n : ℤ) :
        -(principalRoot d ^ 3 - 1) * (n : ℝ) /
            (((principalA d) 1 0 : ℝ) *
              (principalFiveTermUpperIndexBound d : ℝ)) =
          -((principalRoot d ^ 3 - 1) /
            (((principalA d) 1 0 : ℝ) *
              (principalFiveTermUpperIndexBound d : ℝ))) * n := by ring
    rw [hform (principalFiveTermLatticeIndex d m k), hform a]
    constructor
    · intro h
      exact_mod_cast (mul_left_cancel₀ (neg_ne_zero.mpr hscale) h)
    · intro h
      rw [h]
  dsimp only [principalFiveTermStripPolePosition]
  norm_cast
  simpa only [Int.cast_mul] using hreal

/-- The residue at the position of an index is the window sum over that index fiber.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_residue_at_index_eq_window (d : ℕ) (hd : 3 < d)
    (ℓ v₁ v₂ : ℤ) (w : ℝ) (a : ℤ) :
    crossedResidueAtPosition d ℓ v₁ v₂ w
      ((-(principalRoot d ^ 3 - 1) * (a : ℝ) /
        (((principalA d) 1 0 : ℝ) *
          (principalFiveTermUpperIndexBound d : ℝ))) : ℂ) =
      ∑ mk ∈ principalFiveTermWindow d a with
        principalFiveTermLatticeIndex d mk.1 mk.2 = a,
        principalFiveTermKernelResidue d ℓ v₁ w
          (principalFiveTermLatticeArgument d v₁ v₂) mk.1
          (principalFiveTermLatticeArgument d mk.1 mk.2) := by
  have hmem (m k : ℤ)
      (hm0 : 0 ≤ m) (hm1 : m < (d : ℤ) * ((d : ℤ) - 2))
      (hpos : ((-(principalRoot d ^ 3 - 1) * (a : ℝ) /
        (((principalA d) 1 0 : ℝ) *
          (principalFiveTermUpperIndexBound d : ℝ))) : ℂ) =
          principalFiveTermStripPolePosition d m k) :
      (m, k) ∈ principalFiveTermWindow d a := by
    have hS := (crossed_position_eq_iff_index_eq d hd m k a).1 hpos.symm
    apply (mem_principalFiveTermWindow d hd a (m, k)).2
    exact ⟨hm0, hm1, hS.ge, by linarith [principalFiveTermUpperIndexBound_pos d hd]⟩
  rw [crossed_residue_at_position_eq_window d hd ℓ v₁ v₂ w a _ hmem]
  simp only [crossed_position_eq_iff_index_eq d hd]

/-- The zero-position fiber has `E` numerator and denominator values.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_residue_at_zero_eq_fiber (d : ℕ) (hd : 3 < d)
    [NeZero (principalDilogOrder d)] (u₁ u₂ v₁ v₂ : ℤ)
    (hv : 1 ≤ principalFiveTermLatticeIndex d v₁ v₂) :
    crossedResidueAtPosition d (u₁ + 1) v₁ v₂
      (principalFiveTermLatticeArgument d u₁ u₂) 0 =
      (principalRoot d : ℂ) ^ 3 /
        (2 * Real.pi * I * (1 - (principalRoot d : ℂ) ^ 3)) *
      ∑ mk ∈ principalFiveTermWindow d 0 with
        principalFiveTermLatticeIndex d mk.1 mk.2 = 0,
        principalDilogBicharacter d
          (principalFiveTermCharacteristicResidue d mk.1 mk.2)
          (principalFiveTermCharacteristicResidue d u₁ u₂) *
        (principalDilogE d (principalFiveTermCharacteristicResidue d mk.1 mk.2) /
          principalDilogE d
            (principalFiveTermCharacteristicResidue d mk.1 mk.2 +
              principalFiveTermCharacteristicResidue d v₁ v₂)) := by
  have hfib := crossed_residue_at_index_eq_window d hd (u₁ + 1) v₁ v₂
    (principalFiveTermLatticeArgument d u₁ u₂) 0
  have hfib0 : crossedResidueAtPosition d (u₁ + 1) v₁ v₂
      (principalFiveTermLatticeArgument d u₁ u₂) 0 =
      ∑ mk ∈ principalFiveTermWindow d 0 with
        principalFiveTermLatticeIndex d mk.1 mk.2 = 0,
        principalFiveTermKernelResidue d (u₁ + 1) v₁
          (principalFiveTermLatticeArgument d u₁ u₂)
          (principalFiveTermLatticeArgument d v₁ v₂) mk.1
          (principalFiveTermLatticeArgument d mk.1 mk.2) := by
    simpa using hfib
  rw [hfib0, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro mk hmk
  have hS := (Finset.mem_filter.mp hmk).2
  have hSv : 0 ≤ principalFiveTermLatticeIndex d (mk.1 + v₁) (mk.2 + v₂) := by
    rw [principalFiveTermLatticeIndex_add, hS]
    omega
  rw [principalFiveTermKernelResidue_eq_of_types d hd mk.1 mk.2 u₁ u₂ v₁ v₂]
  simp only [hS, hSv, le_refl, ↓reduceIte]
  rw [principalFiveTermCharacteristicResidue_add]
  ring

/-- For `S(v)<H`, the negative special fiber avoids the denominator zero class.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_denominator_class_ne_zero
    (d : ℕ) (hd : 3 < d) (m k v₁ v₂ : ℤ)
    (hS : principalFiveTermLatticeIndex d m k =
      -principalFiveTermUpperIndexBound d)
    (hv : 0 < principalFiveTermLatticeIndex d v₁ v₂ ∧
      principalFiveTermLatticeIndex d v₁ v₂ < principalFiveTermUpperIndexBound d) :
    principalFiveTermCharacteristicResidue d (m + v₁) (k + v₂) ≠ 0 := by
  intro hz
  have hdiv := principalFiveTermUpperIndexBound_dvd_latticeIndex
    d hd (m + v₁) (k + v₂) hz
  rw [principalFiveTermLatticeIndex_add, hS] at hdiv
  have hVdiv : principalFiveTermUpperIndexBound d ∣
      principalFiveTermLatticeIndex d v₁ v₂ := by
    convert (dvd_refl (principalFiveTermUpperIndexBound d)).add hdiv using 1; omega
  have hzero := Int.eq_zero_of_dvd_of_nonneg_of_lt hv.1.le hv.2 hVdiv
  omega

/-- The width-position fiber has `F⁻` numerator and `E` denominator values.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_residue_at_width_eq_fiber (d : ℕ) (hd : 3 < d)
    [NeZero (principalDilogOrder d)] (u₁ u₂ v₁ v₂ : ℤ)
    (hv : 1 ≤ principalFiveTermLatticeIndex d v₁ v₂ ∧
      principalFiveTermLatticeIndex d v₁ v₂ ≤ principalFiveTermUpperIndexBound d) :
    crossedResidueAtPosition d (u₁ + 1) v₁ v₂
      (principalFiveTermLatticeArgument d u₁ u₂)
      (((principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ) : ℝ) : ℂ) =
      (principalRoot d : ℂ) ^ 3 /
        (2 * Real.pi * I * (1 - (principalRoot d : ℂ) ^ 3)) *
      ∑ mk ∈ principalFiveTermWindow d (-principalFiveTermUpperIndexBound d) with
        principalFiveTermLatticeIndex d mk.1 mk.2 =
          -principalFiveTermUpperIndexBound d,
        principalDilogBicharacter d
          (principalFiveTermCharacteristicResidue d mk.1 mk.2)
          (principalFiveTermCharacteristicResidue d u₁ u₂) *
        (principalDilogEMinus d (principalFiveTermCharacteristicResidue d mk.1 mk.2) /
          principalDilogE d
            (principalFiveTermCharacteristicResidue d mk.1 mk.2 +
              principalFiveTermCharacteristicResidue d v₁ v₂)) := by
  have hfib := crossed_residue_at_index_eq_window d hd (u₁ + 1) v₁ v₂
    (principalFiveTermLatticeArgument d u₁ u₂)
    (-principalFiveTermUpperIndexBound d)
  have hδ :
      ((-(principalRoot d ^ 3 - 1) *
        ((-principalFiveTermUpperIndexBound d : ℤ) : ℝ) /
        (((principalA d) 1 0 : ℝ) *
          (principalFiveTermUpperIndexBound d : ℝ))) : ℂ) =
      (((principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ) : ℝ) : ℂ) := by
    have hH : (principalFiveTermUpperIndexBound d : ℝ) ≠ 0 := by
      exact_mod_cast (principalFiveTermUpperIndexBound_pos d hd).ne'
    have hc : ((principalA d) 1 0 : ℝ) ≠ 0 := by
      exact_mod_cast (principalA_lowerLeft_pos d hd).ne'
    have hr : -(principalRoot d ^ 3 - 1) *
        ((-principalFiveTermUpperIndexBound d : ℤ) : ℝ) /
          (((principalA d) 1 0 : ℝ) *
            (principalFiveTermUpperIndexBound d : ℝ)) =
        (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ) := by
      push_cast
      field_simp [hc, hH]
    have hcast := congrArg (fun t : ℝ => (t : ℂ)) hr
    push_cast at hcast
    push_cast
    exact hcast
  rw [hδ] at hfib
  rw [hfib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro mk hmk
  have hS := (Finset.mem_filter.mp hmk).2
  have hH := principalFiveTermUpperIndexBound_pos d hd
  have hSneg : principalFiveTermLatticeIndex d mk.1 mk.2 < 0 := by omega
  have hSv : principalFiveTermLatticeIndex d (mk.1 + v₁) (mk.2 + v₂) =
      -principalFiveTermUpperIndexBound d +
        principalFiveTermLatticeIndex d v₁ v₂ := by
    rw [principalFiveTermLatticeIndex_add, hS]
  rw [principalFiveTermKernelResidue_eq_of_types d hd mk.1 mk.2 u₁ u₂ v₁ v₂]
  simp only [not_le.mpr hSneg, ↓reduceIte]
  by_cases hV : principalFiveTermLatticeIndex d v₁ v₂ =
      principalFiveTermUpperIndexBound d
  · have hSv0 : 0 ≤ principalFiveTermLatticeIndex d (mk.1 + v₁) (mk.2 + v₂) := by
      rw [hSv, hV]
      omega
    simp only [hSv0, ↓reduceIte]
    rw [principalFiveTermCharacteristicResidue_add]
    ring
  · have hSvneg : principalFiveTermLatticeIndex d (mk.1 + v₁) (mk.2 + v₂) < 0 := by
      rw [hSv]
      omega
    have hclass := crossed_denominator_class_ne_zero
      d hd mk.1 mk.2 v₁ v₂ hS ⟨by omega, by omega⟩
    simp only [not_le.mpr hSvneg, ↓reduceIte]
    rw [principalDilogEMinus_of_ne_zero d hd hclass,
      principalFiveTermCharacteristicResidue_add]
    ring

/-- Transporting the two special fibers leaves only the numerator zero-class
difference.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_zero_fiber_value_difference (d : ℕ) (hd : 3 < d)
    [NeZero (principalDilogOrder d)] (u₁ u₂ v₁ v₂ : ℤ) :
    (∑ mk ∈ principalFiveTermWindow d 0 with
        principalFiveTermLatticeIndex d mk.1 mk.2 = 0,
        principalDilogBicharacter d
          (principalFiveTermCharacteristicResidue d mk.1 mk.2)
          (principalFiveTermCharacteristicResidue d u₁ u₂) *
        (principalDilogE d (principalFiveTermCharacteristicResidue d mk.1 mk.2) /
          principalDilogE d
            (principalFiveTermCharacteristicResidue d mk.1 mk.2 +
              principalFiveTermCharacteristicResidue d v₁ v₂))) -
      (∑ mk ∈ principalFiveTermWindow d (-principalFiveTermUpperIndexBound d) with
        principalFiveTermLatticeIndex d mk.1 mk.2 =
          -principalFiveTermUpperIndexBound d,
        principalDilogBicharacter d
          (principalFiveTermCharacteristicResidue d mk.1 mk.2)
          (principalFiveTermCharacteristicResidue d u₁ u₂) *
        (principalDilogEMinus d (principalFiveTermCharacteristicResidue d mk.1 mk.2) /
          principalDilogE d
            (principalFiveTermCharacteristicResidue d mk.1 mk.2 +
              principalFiveTermCharacteristicResidue d v₁ v₂))) =
      (principalDilogE d 0 - principalDilogEMinus d 0) /
        principalDilogE d (principalFiveTermCharacteristicResidue d v₁ v₂) := by
  let f : (Fin 2 → ZMod (principalDilogOrder d)) → ℂ := fun g =>
    principalDilogBicharacter d g
      (principalFiveTermCharacteristicResidue d u₁ u₂) *
      (principalDilogEMinus d g /
        principalDilogE d (g + principalFiveTermCharacteristicResidue d v₁ v₂))
  have htransport := sum_principalFiveTermWindow_index_sub_bound d hd 0 f
  simp only [zero_sub] at htransport
  change (∑ mk ∈ principalFiveTermWindow d 0 with
        principalFiveTermLatticeIndex d mk.1 mk.2 = 0,
        principalDilogBicharacter d
          (principalFiveTermCharacteristicResidue d mk.1 mk.2)
          (principalFiveTermCharacteristicResidue d u₁ u₂) *
        (principalDilogE d (principalFiveTermCharacteristicResidue d mk.1 mk.2) /
          principalDilogE d
            (principalFiveTermCharacteristicResidue d mk.1 mk.2 +
              principalFiveTermCharacteristicResidue d v₁ v₂))) -
      (∑ mk ∈ principalFiveTermWindow d (-principalFiveTermUpperIndexBound d) with
        principalFiveTermLatticeIndex d mk.1 mk.2 =
          -principalFiveTermUpperIndexBound d,
        f (principalFiveTermCharacteristicResidue d mk.1 mk.2)) = _
  rw [← htransport, ← Finset.sum_sub_distrib]
  have hzero : (0, 0) ∈ principalFiveTermWindow d 0 := by
    apply (mem_principalFiveTermWindow d hd 0 (0, 0)).2
    have hdI : (3 : ℤ) < d := by exact_mod_cast hd
    have hc : (0 : ℤ) < (d : ℤ) * ((d : ℤ) - 2) := by nlinarith
    simpa [principalFiveTermLatticeIndex] using
      (show 0 ≤ (0 : ℤ) ∧ 0 < (d : ℤ) * ((d : ℤ) - 2) ∧
        0 ≤ (0 : ℤ) ∧ 0 < principalFiveTermUpperIndexBound d from
          ⟨le_refl _, hc, le_refl _, principalFiveTermUpperIndexBound_pos d hd⟩)
  have hzeroF : (0, 0) ∈
      (principalFiveTermWindow d 0).filter
        (fun mk => principalFiveTermLatticeIndex d mk.1 mk.2 = 0) := by
    exact Finset.mem_filter.mpr ⟨hzero, by simp [principalFiveTermLatticeIndex]⟩
  have h00 : principalFiveTermCharacteristicResidue d 0 0 = 0 := by
    apply (principalFiveTermCharacteristicResidue_eq_zero_iff d hd 0 0).2
    simp
  rw [Finset.sum_eq_single (0, 0)]
  · simp only [f, h00, zero_add,
      principalDilogBicharacter, fixedBicharacter_zero_left, one_mul]
    ring
  · intro mk hmk hne
    have hmkW := (Finset.mem_filter.mp hmk).1
    have hclass : principalFiveTermCharacteristicResidue d mk.1 mk.2 ≠ 0 := by
      intro hz
      have heq := principalFiveTermCharacteristicResidue_injOn
        d hd 0 hmkW hzero
      apply hne
      apply heq
      exact hz.trans h00.symm
    simp [f, principalDilogEMinus_of_ne_zero d hd hclass]
  · simp [hzeroF]

/-- The difference of residues at zero and the width is the zero-class value
correction.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_zero_residue_difference (d : ℕ) (hd : 3 < d)
    [NeZero (principalDilogOrder d)] (u₁ u₂ v₁ v₂ : ℤ)
    (hv : 1 ≤ principalFiveTermLatticeIndex d v₁ v₂ ∧
      principalFiveTermLatticeIndex d v₁ v₂ ≤ principalFiveTermUpperIndexBound d)
    (hv0 : principalFiveTermCharacteristicResidue d v₁ v₂ ≠ 0) :
    crossedResidueAtPosition d (u₁ + 1) v₁ v₂
        (principalFiveTermLatticeArgument d u₁ u₂) 0 -
      crossedResidueAtPosition d (u₁ + 1) v₁ v₂
        (principalFiveTermLatticeArgument d u₁ u₂)
        (((principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ) : ℝ) : ℂ) =
      (principalRoot d : ℂ) ^ 3 /
        (2 * Real.pi * I * (1 - (principalRoot d : ℂ) ^ 3)) *
        ((principalDilogE d 0 - principalDilogEMinus d 0) /
          principalDilogEMinus d (principalFiveTermCharacteristicResidue d v₁ v₂)) := by
  rw [crossed_residue_at_zero_eq_fiber d hd u₁ u₂ v₁ v₂ hv.1,
    crossed_residue_at_width_eq_fiber d hd u₁ u₂ v₁ v₂ hv]
  rw [← mul_sub, crossed_zero_fiber_value_difference d hd u₁ u₂ v₁ v₂]
  rw [principalDilogEMinus_of_ne_zero d hd hv0]

/-- Adding the zero-class correction replaces `F⁻` by `E` in the finite sum.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_finite_values_correction (d : ℕ) (hd : 3 < d)
    [NeZero (principalDilogOrder d)] (u₁ u₂ v₁ v₂ : ℤ) :
    (∑ g : principalDilogGroup d,
        principalDilogBicharacter d g
          (principalFiveTermCharacteristicResidue d u₁ u₂) *
        (principalDilogEMinus d g /
          principalDilogEMinus d
            (g + principalFiveTermCharacteristicResidue d v₁ v₂))) +
      (principalDilogE d 0 - principalDilogEMinus d 0) /
        principalDilogEMinus d (principalFiveTermCharacteristicResidue d v₁ v₂) =
      ∑ g : principalDilogGroup d,
        principalDilogBicharacter d g
          (principalFiveTermCharacteristicResidue d u₁ u₂) *
        (principalDilogE d g /
          principalDilogEMinus d
            (g + principalFiveTermCharacteristicResidue d v₁ v₂)) := by
  classical
  have hdiff :
      (∑ g : principalDilogGroup d,
        principalDilogBicharacter d g
          (principalFiveTermCharacteristicResidue d u₁ u₂) *
        (principalDilogE d g /
          principalDilogEMinus d
            (g + principalFiveTermCharacteristicResidue d v₁ v₂))) -
      (∑ g : principalDilogGroup d,
        principalDilogBicharacter d g
          (principalFiveTermCharacteristicResidue d u₁ u₂) *
        (principalDilogEMinus d g /
          principalDilogEMinus d
            (g + principalFiveTermCharacteristicResidue d v₁ v₂))) =
      (principalDilogE d 0 - principalDilogEMinus d 0) /
        principalDilogEMinus d (principalFiveTermCharacteristicResidue d v₁ v₂) := by
    rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single (0 : principalDilogGroup d)]
    · simp [principalDilogBicharacter, fixedBicharacter_zero_left]
      ring
    · intro g hg hne
      have hg0 : (g : Fin 2 → ZMod (principalDilogOrder d)) ≠ 0 := by
        intro h
        exact hne (Subtype.ext h)
      rw [principalDilogEMinus_of_ne_zero d hd hg0]
      ring
    · simp
  linear_combination -hdiff

/-- Reindexing the positive square corrections gives the product-pole residue sum.
Used by `crossed_square_sum`. -/
private lemma crossed_positive_square_sum (d : ℕ) (hd : 3 < d)
    (ℓ v₁ v₂ : ℤ) (w β : ℝ) (F : Finset ℤ)
    (hβle : β ≤ (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ))
    (hF : ∀ j : ℤ, j ∈ F ↔ 0 ≤ j ∧
      (j : ℝ) / ((principalA d) 1 0 : ℝ) < β)
    (hv : 1 ≤ principalFiveTermLatticeIndex d v₁ v₂)
    (hw : Complex.exp (2 * Real.pi * I * ((w : ℂ) / (principalRoot d : ℂ) ^ 3)) =
      Complex.exp (2 * Real.pi * I * ((w : ℂ) + (ℓ - 1) * (principalRoot d : ℂ))))
    (hy : Complex.exp (2 * Real.pi * I *
        ((principalFiveTermLatticeArgument d v₁ v₂ : ℂ) /
          (principalRoot d : ℂ) ^ 3)) =
      Complex.exp (2 * Real.pi * I *
        ((principalFiveTermLatticeArgument d v₁ v₂ : ℂ) +
          v₁ * (principalRoot d : ℂ))))
    (RP : ℂ → ℂ)
    (hRP : ∀ s ∈ crossedProductPoleSet d F,
      Tendsto (fun ζ : ℂ => (ζ - s) *
        principalFiveTermResidueSum d ℓ v₁ w
          (principalFiveTermLatticeArgument d v₁ v₂) ζ)
        (𝓝[≠] s) (𝓝 (RP s))) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      (∑ j ∈ F.filter (0 < ·), rectBoundaryIntegral
        (principalFiveTermDifferenceSum d ℓ v₁ w
          (principalFiveTermLatticeArgument d v₁ v₂))
        ((j : ℂ) / ((principalA d) 1 0 : ℂ) - (r + r * I))
        ((j : ℂ) / ((principalA d) 1 0 : ℂ) + (r + r * I))) =
      -(2 * Real.pi * I) *
        (∑ s ∈ crossedProductPoleSet d F, RP s) := by
  classical
  let G := F.filter (0 < ·)
  have hpositive : ∀ᶠ r : ℝ in 𝓝[>] 0,
      ∀ j ∈ G,
        rectBoundaryIntegral
          (principalFiveTermDifferenceSum d ℓ v₁ w
            (principalFiveTermLatticeArgument d v₁ v₂))
          ((j : ℂ) / ((principalA d) 1 0 : ℂ) - (r + r * I))
          ((j : ℂ) / ((principalA d) 1 0 : ℂ) + (r + r * I)) =
        -(2 * Real.pi * I) *
          RP (((principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ) +
            (j : ℝ) / ((principalA d) 1 0 : ℝ)) : ℂ) := by
    apply (Finset.eventually_all G).2
    intro j hjG
    obtain ⟨hjF, hj⟩ := Finset.mem_filter.mp hjG
    apply crossed_positive_square_correction d hd ℓ v₁ v₂ w F j hjF hj
      (le_trans (le_of_lt ((hF j).1 hjF).2) hβle) hv hw hy RP hRP
  filter_upwards [hpositive] with r hrP
  have hsumImage :
      (∑ s ∈ crossedProductPoleSet d F, RP s) =
        ∑ j ∈ G,
          RP (((principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ) +
            (j : ℝ) / ((principalA d) 1 0 : ℝ)) : ℂ) := by
    dsimp [crossedProductPoleSet, G]
    apply Finset.sum_image
    intro a ha b hb hab
    apply crossed_product_position_injective d hd
    convert hab using 1
  have hG : (∑ j ∈ G, rectBoundaryIntegral
        (principalFiveTermDifferenceSum d ℓ v₁ w
          (principalFiveTermLatticeArgument d v₁ v₂))
        ((j : ℂ) / ((principalA d) 1 0 : ℂ) - (r + r * I))
        ((j : ℂ) / ((principalA d) 1 0 : ℂ) + (r + r * I))) =
      -(2 * Real.pi * I) *
        (∑ s ∈ crossedProductPoleSet d F, RP s) := by
    calc
      _ = ∑ j ∈ G, -(2 * Real.pi * I) *
          RP (((principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ) +
            (j : ℝ) / ((principalA d) 1 0 : ℝ)) : ℂ) := by
        apply Finset.sum_congr rfl
        exact hrP
      _ = _ := by
        rw [← Finset.mul_sum]
        rw [hsumImage]
  exact hG

/-- The square integrals cancel positive product residues and retain the zero
correction.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_square_sum (d : ℕ) (hd : 3 < d)
    (ℓ v₁ v₂ : ℤ) (w β : ℝ) (F : Finset ℤ)
    (hβpos : 0 < β)
    (hβle : β ≤ (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ))
    (hF : ∀ j : ℤ, j ∈ F ↔ 0 ≤ j ∧
      (j : ℝ) / ((principalA d) 1 0 : ℝ) < β)
    (hv : 1 ≤ principalFiveTermLatticeIndex d v₁ v₂ ∧
      principalFiveTermLatticeIndex d v₁ v₂ ≤ principalFiveTermUpperIndexBound d)
    (hw : Complex.exp (2 * Real.pi * I * ((w : ℂ) / (principalRoot d : ℂ) ^ 3)) =
      Complex.exp (2 * Real.pi * I * ((w : ℂ) + (ℓ - 1) * (principalRoot d : ℂ))))
    (hy : Complex.exp (2 * Real.pi * I *
        ((principalFiveTermLatticeArgument d v₁ v₂ : ℂ) /
          (principalRoot d : ℂ) ^ 3)) =
      Complex.exp (2 * Real.pi * I *
        ((principalFiveTermLatticeArgument d v₁ v₂ : ℂ) +
          v₁ * (principalRoot d : ℂ))))
    (RP : ℂ → ℂ)
    (hRP : ∀ s ∈ crossedProductPoleSet d F,
      Tendsto (fun ζ : ℂ => (ζ - s) *
        principalFiveTermResidueSum d ℓ v₁ w
          (principalFiveTermLatticeArgument d v₁ v₂) ζ)
        (𝓝[≠] s) (𝓝 (RP s))) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      (∑ j ∈ F, rectBoundaryIntegral
        (principalFiveTermDifferenceSum d ℓ v₁ w
          (principalFiveTermLatticeArgument d v₁ v₂))
        ((j : ℂ) / ((principalA d) 1 0 : ℂ) - (r + r * I))
        ((j : ℂ) / ((principalA d) 1 0 : ℂ) + (r + r * I))) =
      2 * Real.pi * I *
        (crossedResidueAtPosition d ℓ v₁ v₂ w 0 -
          crossedResidueAtPosition d ℓ v₁ v₂ w
            (((principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ) : ℝ) : ℂ)) -
      2 * Real.pi * I *
        (∑ s ∈ crossedProductPoleSet d F, RP s) := by
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
  have hzero := crossed_zero_square_correction d hd ℓ v₁ v₂ w hv.1 hv.2 hw hy
  have hpositive := crossed_positive_square_sum d hd ℓ v₁ v₂ w β F
    hβle hF hv.1 hw hy RP hRP
  filter_upwards [hzero, hpositive] with r hr0 hrP
  conv_lhs => rw [hsplit, Finset.sum_insert h0not]
  simp only [Int.cast_zero, zero_div, zero_add, zero_sub]
  rw [hr0, hrP]
  ring

/-- The corrected kernel residues equal the requested finite five-term sum.
Used by `integral_principalFiveTermResidueSum_of_crossed`. -/
private lemma crossed_finite_residue_synthesis (d : ℕ) (hd : 3 < d)
    [NeZero (principalDilogOrder d)] (u₁ u₂ v₁ v₂ : ℤ)
    (hv : 1 ≤ principalFiveTermLatticeIndex d v₁ v₂ ∧
      principalFiveTermLatticeIndex d v₁ v₂ ≤ principalFiveTermUpperIndexBound d)
    (hv0 : principalFiveTermCharacteristicResidue d v₁ v₂ ≠ 0) :
    -(2 * Real.pi * I) *
      ((∑ mk ∈ principalFiveTermWindow d
          (-principalFiveTermUpperIndexBound d -
            principalFiveTermLatticeIndex d v₁ v₂),
          principalFiveTermKernelResidue d (u₁ + 1) v₁
            (principalFiveTermLatticeArgument d u₁ u₂)
            (principalFiveTermLatticeArgument d v₁ v₂) mk.1
            (principalFiveTermLatticeArgument d mk.1 mk.2)) +
        (crossedResidueAtPosition d (u₁ + 1) v₁ v₂
            (principalFiveTermLatticeArgument d u₁ u₂) 0 -
          crossedResidueAtPosition d (u₁ + 1) v₁ v₂
            (principalFiveTermLatticeArgument d u₁ u₂)
            (((principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ) : ℝ) : ℂ))) =
      (principalRoot d : ℂ) ^ 3 / ((principalRoot d : ℂ) ^ 3 - 1) *
        ∑ g : principalDilogGroup d,
          principalDilogBicharacter d g
            (principalFiveTermCharacteristicResidue d u₁ u₂) *
          (principalDilogE d g /
            principalDilogEMinus d
              (g + principalFiveTermCharacteristicResidue d v₁ v₂)) := by
  rw [crossed_window_residue_sum_eq d hd u₁ u₂ v₁ v₂ hv.1,
    crossed_zero_residue_difference d hd u₁ u₂ v₁ v₂ hv hv0]
  have hfin := crossed_finite_values_correction d hd u₁ u₂ v₁ v₂
  have hfac : -(2 * Real.pi * I) *
      ((principalRoot d : ℂ) ^ 3 /
        (2 * Real.pi * I * (1 - (principalRoot d : ℂ) ^ 3))) =
      (principalRoot d : ℂ) ^ 3 / ((principalRoot d : ℂ) ^ 3 - 1) := by
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hI : (I : ℂ) ≠ 0 := I_ne_zero
    have hε : (principalRoot d : ℂ) ^ 3 - 1 ≠ 0 := by
      exact_mod_cast (ne_of_gt (sub_pos.mpr (one_lt_principalRoot_pow_three d hd)))
    have hε' : 1 - (principalRoot d : ℂ) ^ 3 ≠ 0 := by
      intro h
      apply hε
      linear_combination -h
    field_simp [hπ, hI, hε, hε']
    ring
  calc
    _ = (-(2 * Real.pi * I) *
        ((principalRoot d : ℂ) ^ 3 /
          (2 * Real.pi * I * (1 - (principalRoot d : ℂ) ^ 3)))) *
        ((∑ g : principalDilogGroup d,
          principalDilogBicharacter d g
            (principalFiveTermCharacteristicResidue d u₁ u₂) *
          (principalDilogEMinus d g /
            principalDilogEMinus d
              (g + principalFiveTermCharacteristicResidue d v₁ v₂))) +
          (principalDilogE d 0 - principalDilogEMinus d 0) /
            principalDilogEMinus d
              (principalFiveTermCharacteristicResidue d v₁ v₂)) := by ring
    _ = _ := by rw [hfin, hfac]

/-- The strip identity for the deformed contours of [RW26, Radchenko, Wheeler (2026),
Section 3.2, proof of Theorem 2, `thm:fg.equs`]. Subtracting the square integrals of `J` at
`j/c < β_v` from `∫_x L-∫_{x+δ} L` cancels the numerator poles and restores `F⁺(0)`, leaving
`ε/(ε-1) ∑_g ⟨g;u⟩ F⁺(g)/F⁻(g+v)`. -/
theorem integral_principalFiveTermResidueSum_of_crossed
    (d : ℕ) (hd : 3 < d) [NeZero (principalDilogOrder d)]
    (u₁ u₂ v₁ v₂ : ℤ)
    (hu : 0 ≤ principalFiveTermLatticeIndex d u₁ u₂ ∧
      principalFiveTermLatticeIndex d u₁ u₂ < principalFiveTermUpperIndexBound d)
    (hv : 1 ≤ principalFiveTermLatticeIndex d v₁ v₂ ∧
      principalFiveTermLatticeIndex d v₁ v₂ ≤ principalFiveTermUpperIndexBound d)
    (hv0 : principalFiveTermCharacteristicResidue d v₁ v₂ ≠ 0) :
    let ε := principalRoot d ^ 3
    let c : ℝ := ((principalA d) 1 0 : ℝ)
    let H : ℝ := (principalFiveTermUpperIndexBound d : ℝ)
    let δ := (ε - 1) / c
    let w := principalFiveTermLatticeArgument d u₁ u₂
    let y := principalFiveTermLatticeArgument d v₁ v₂
    let β := -((v₁ : ℝ) * ε / c + y)
    let L := principalFiveTermResidueSum d (u₁ + 1) v₁ w y
    let J := principalFiveTermDifferenceSum d (u₁ + 1) v₁ w y
    ∀ (x : ℝ) (F : Finset ℤ),
      β < x → x < β + δ / H → x < ε / c →
      (∀ j : ℤ, j ∈ F ↔ 0 ≤ j ∧ (j : ℝ) / c < β) →
      (∀ j : ℤ, 0 ≤ j → ((j : ℝ) / c < x ↔ (j : ℝ) / c < β)) →
      (∀ m : FiveTermIndex (principalA d),
        IsPrincipalFiveTermResidueCrossing d ((m : ℕ) : ℤ) y
          (x - ((m : ℕ) : ℝ) * ε / c)) →
      ∀ᶠ r : ℝ in 𝓝[>] 0,
        ((∫ t : ℝ, L ((x : ℂ) + t * I) * I) -
          (∫ t : ℝ, L (((x + δ : ℝ) : ℂ) + t * I) * I)) -
          (∑ j ∈ F, rectBoundaryIntegral J
            ((j : ℂ) / (c : ℂ) - (r + r * I))
            ((j : ℂ) / (c : ℂ) + (r + r * I))) =
        (ε : ℂ) / ((ε : ℂ) - 1) *
          ∑ g : principalDilogGroup d,
            principalDilogBicharacter d g
              (principalFiveTermCharacteristicResidue d u₁ u₂) *
            (principalDilogE d g /
              principalDilogEMinus d (g + principalFiveTermCharacteristicResidue d v₁ v₂)) := by
  dsimp
  intro x F hβ hx₂ hx hF hgrid hreg
  have hβpos : 0 < -((v₁ : ℝ) * principalRoot d ^ 3 /
      ((principalA d) 1 0 : ℝ) + principalFiveTermLatticeArgument d v₁ v₂) := by
    rw [crossed_beta_eq_spacing_index d hd]
    exact mul_pos (crossed_spacing_pos d hd) (by exact_mod_cast hv.1)
  have hβle := crossed_width_ge_beta d hd v₁ v₂ hv.2
  have hx₂' : x < -((v₁ : ℝ) * principalRoot d ^ 3 /
      ((principalA d) 1 0 : ℝ) + principalFiveTermLatticeArgument d v₁ v₂) +
      (principalRoot d ^ 3 - 1) /
        (((principalA d) 1 0 : ℝ) *
          (principalFiveTermUpperIndexBound d : ℝ)) := by
    convert hx₂ using 1
    ring
  have hrate := crossed_residue_rates d hd u₁ u₂ v₁ v₂ hu hv
  have hw : Complex.exp (2 * Real.pi * I *
      ((principalFiveTermLatticeArgument d u₁ u₂ : ℂ) /
        (principalRoot d : ℂ) ^ 3)) =
      Complex.exp (2 * Real.pi * I *
        ((principalFiveTermLatticeArgument d u₁ u₂ : ℂ) +
          ((u₁ + 1 : ℤ) - 1) * (principalRoot d : ℂ))) := by
    convert (principalFiveTermLatticeArgument_exp_lower d hd u₁ u₂).symm using 1
    push_cast
    ring_nf
  have hy : Complex.exp (2 * Real.pi * I *
      ((principalFiveTermLatticeArgument d v₁ v₂ : ℂ) /
        (principalRoot d : ℂ) ^ 3)) =
      Complex.exp (2 * Real.pi * I *
        ((principalFiveTermLatticeArgument d v₁ v₂ : ℂ) +
          v₁ * (principalRoot d : ℂ))) := by
    convert (principalFiveTermLatticeArgument_exp_lower d hd v₁ v₂).symm using 1
    ring_nf
  obtain ⟨RP, hRP, hstrip⟩ := crossed_strip_residue_identity d hd
    (u₁ + 1) v₁ v₂ (principalFiveTermLatticeArgument d u₁ u₂) x
    (-((v₁ : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ) +
      principalFiveTermLatticeArgument d v₁ v₂)) F
    rfl hβ hx₂' hx hgrid hF hreg
    hrate.1 hrate.2
  have hsquares := crossed_square_sum d hd (u₁ + 1) v₁ v₂
    (principalFiveTermLatticeArgument d u₁ u₂)
    (-((v₁ : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ) +
      principalFiveTermLatticeArgument d v₁ v₂)) F
    hβpos hβle hF hv hw hy RP hRP
  have hfinite := crossed_finite_residue_synthesis d hd u₁ u₂ v₁ v₂ hv hv0
  filter_upwards [hsquares] with r hr
  rw [hstrip, hr]
  convert hfinite using 1
  · ring
  · push_cast
    rfl


end SIC

end
