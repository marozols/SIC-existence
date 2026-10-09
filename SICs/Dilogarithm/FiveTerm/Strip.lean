/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Dilogarithm.FiveTerm.ClassWindow
import SICs.Dilogarithm.FiveTerm.ResidueBounds

/-!
# Residue strips for a letter word

The source arguments of a letter word give evenly spaced kernel poles on the common residue
line; the residue sum is meromorphic and its regular strip boundaries admit vertical integrals.

This module follows [RW26, Radchenko, Wheeler (2026), Section 3.2, proof of Theorem 2,
`thm:fg.equs`], for `γ = ∏_j T^{b_j}S = (a b; c d)` at an attractive fixed point `τ`,
`ε = cτ+d`, and `N = a+d-2`. It supplies the strip geometry and analytic input for
`SICs.Dilogarithm.FiveTerm.CrossedStrip`.

## The argument

The rate identity at `z_(m,k)` says `cz_(m,k)/ε + m = -S(m,k)/(ε-1)`.
The unit equation `(ε-1)² = Nε` therefore puts its translated kernel pole at
`z_(m,k)+mε/c = -(ε-1)S(m,k)/(cN)`. Positivity of `c`, `N`, and `ε-1` fixes the order of
these poles and identifies the index window inside a strip of width `(ε-1)/c`.

The shifted denominator has no zeros to the right of its divisor bound. In
`SICs.Dilogarithm.FiveTerm.CrossedStrip`, the numerator divisor is tracked by the finite
product-pole set. At a crossed-strip point away from that set and the kernel poles, every
summand has nonnegative meromorphic order, so the finite residue sum is bounded nearby. A
common-line kernel pole has a unique source pair in the window, and its residue is the
corresponding finite-group summand. The upper and lower sector estimates make the horizontal
parts of a long rectangle vanish; a regular translated vertical line avoids both the product
divisors and the pole factor. These facts supply the analytic strip argument in
`SICs.Dilogarithm.FiveTerm.CrossedStrip`.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology MatrixGroups

namespace SIC

/-! ### Kernel poles on the common line

The unit equation converts the source rate into a pole position indexed by `S`. -/

/-- At a source argument, the common-line kernel pole is
`z_(m,k)+mε/c = -(ε-1)S(m,k)/(cN)`, as in [RW26, Radchenko, Wheeler (2026), Section 3.2]. -/
theorem fiveTermLatticeArgument_add_mul_eq {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (m k : ℤ) :
    fiveTermLatticeArgument γ τ m k +
        (m : ℝ) * fltDenominator (γ : Mat(2, ℤ)) τ / (γ 1 0 : ℝ) =
      -(fltDenominator (γ : Mat(2, ℤ)) τ - 1) *
          (fiveTermLatticeIndex γ m k : ℝ) /
        ((γ 1 0 : ℝ) * (finiteDilogOrder γ : ℝ)) := by
  have hβ := fiveTermLatticeArgument_beta_eq h m k
  linear_combination -hβ

/-! ### Meromorphy and removable points

The residue kernel and its finite common-line sum are meromorphic. Nonnegative order of every
summand makes the totalized sum bounded near a removable point. -/

/-- Each word residue kernel is meromorphic; used by `meromorphic_fiveTermWordResidueSum`. -/
theorem meromorphic_fiveTermWordResidueKernel {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ p m : ℤ) (w y : ℂ) :
    Meromorphic (fiveTermWordResidueKernel bs ℓ p w y τ m) := by
  intro z
  unfold fiveTermWordResidueKernel
  apply MeromorphicAt.div
  · apply MeromorphicAt.mul
    · exact meromorphicAt_fiveTermWordKernel bs ℓ p m h.periodsPos.slitPlane z
    · exact (show AnalyticAt ℂ
          (fun ζ : ℂ => 1 - Complex.exp (2 * Real.pi * I * (ζ + m * (τ : ℂ)))) z
          by fun_prop).meromorphicAt
  · exact (show AnalyticAt ℂ (fiveTermPoleFactor (letterWord bs) τ m) z by
      unfold fiveTermPoleFactor
      fun_prop).meromorphicAt

/-- A zero of `Φ_{m,0}` lies left of `-mε/c`; used by the crossed-strip denominator
order bound. -/
private lemma fiveTerm_denominator_zero_re_bound {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (m k l : ℤ)
    (hK : k + m ≤ 0) (hL : 0 < γ 1 1 * k - γ 1 0 * l) :
    (k : ℝ) * τ + l <
      (-(m : ℝ)) * fltDenominator (γ : Mat(2, ℤ)) τ / (γ 1 0 : ℝ) := by
  have hc : (0 : ℝ) < (γ 1 0 : ℝ) := by exact_mod_cast h.lowerLeft_pos
  have hε : 0 < fltDenominator (γ : Mat(2, ℤ)) τ := h.fltDenominator_pos
  have hK : (k : ℝ) ≤ -(m : ℝ) := by
    exact_mod_cast (show k ≤ -m by omega)
  have hLr : (γ 1 0 : ℝ) * l < (γ 1 1 : ℝ) * k := by
    have hLr' : (0 : ℝ) < (γ 1 1 : ℝ) * k - (γ 1 0 : ℝ) * l := by
      exact_mod_cast hL
    linarith
  apply (lt_div_iff₀ hc).2
  have hlin : (γ 1 0 : ℝ) * τ + γ 1 1 =
      fltDenominator (γ : Mat(2, ℤ)) τ := rfl
  have hlinK := congrArg (fun t : ℝ => t * (k : ℝ)) hlin
  have hmul : 0 ≤ (-(m : ℝ) - (k : ℝ)) *
      fltDenominator (γ : Mat(2, ℤ)) τ :=
    mul_nonneg (sub_nonneg.mpr hK) hε.le
  nlinarith [hlinK, hmul]

/-- The shifted denominator `Φ_{m+p,0}(ζ+y)` has no zero right of
`-(m+p)ε/c-y`; used by the crossed-strip denominator order bound. -/
lemma meromorphicOrderAt_faddeevWord_denominator_nonpos {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (m p : ℤ) (y : ℝ) (ζ : ℂ)
    (hζ : (-(m + p : ℤ) : ℝ) *
      fltDenominator (letterWord bs : Mat(2, ℤ)) τ / (letterWord bs 1 0 : ℝ) - y ≤ ζ.re) :
    meromorphicOrderAt (fun z : ℂ => faddeevWord bs (m + p) 0 (z + y) τ) ζ ≤ 0 := by
  change meromorphicOrderAt
    ((fun z : ℂ => faddeevWord bs (m + p) 0 z τ) ∘ (· + (y : ℂ))) ζ ≤ 0
  rw [meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]
  by_cases hlat : IsPeriodLatticePoint (τ : ℂ) (ζ + y)
  · rcases hlat with ⟨l, k, hk⟩
    apply le_of_not_gt
    intro hpos
    rw [hk] at hpos
    have hpos' : 0 < meromorphicOrderAt (fun z => faddeevWord bs (m + p) 0 z τ)
        ((k : ℂ) * (τ : ℂ) + l) := by
      simpa only [add_comm] using hpos
    obtain ⟨hK, hL⟩ :=
      (meromorphicOrderAt_faddeevWord_pos_iff bs h.ne_nil (m + p) 0 k l
        h.fixedPoint.irrational (fun w hw => (h.periodsPos w hw).2)).mp hpos'
    have hb := fiveTerm_denominator_zero_re_bound h.fixedPoint (m + p) k l hK
      (by simpa using hL)
    have hre : (ζ + (y : ℂ)).re = ζ.re + y := by simp
    have hre' : (((l : ℂ) + (k : ℂ) * (τ : ℂ)).re) = (k : ℝ) * τ + l := by
      simp [Complex.mul_re, add_comm]
    rw [hk, hre'] at hre
    linarith
  · rw [meromorphicOrderAt_faddeevWord_eq_zero
      bs (m + p) 0 h.periodsPos.slitPlane hlat]

/-- Away from pole-factor zeros, the word residue kernel has the numerator order minus the
shifted-denominator order; used by the crossed-strip summand order bound. -/
lemma meromorphicOrderAt_fiveTermWordResidueKernel {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ m p : ℤ) (w y : ℂ) (ζ : ℂ)
    (hζ : ∀ k : ℤ, ζ ≠ fiveTermLatticeArgument (letterWord bs) τ m k) :
    meromorphicOrderAt (fiveTermWordResidueKernel bs ℓ p w y τ m) ζ =
      meromorphicOrderAt (fun z => faddeevWord bs m 0 z τ) ζ -
        meromorphicOrderAt (fun z : ℂ => faddeevWord bs (m + p) 0 (z + y) τ) ζ := by
  let N : ℂ → ℂ := fun z => faddeevWord bs m 0 z τ
  let D : ℂ → ℂ := fun z => faddeevWord bs (m + p) 0 (z + y) τ
  let P : ℂ → ℂ := fiveTermPoleFactor (letterWord bs) τ m
  let E : ℂ → ℂ := fun z => Complex.exp (2 * Real.pi * I *
    ((((letterWord bs 1 0 : ℤ) : ℂ) * z +
        fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) * m) * w /
      fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) + ℓ * (z + m * (τ : ℂ))))
  have hN : MeromorphicAt N ζ := meromorphicAt_faddeevWord bs m 0 h.periodsPos.slitPlane ζ
  have hD : MeromorphicAt D ζ := by
    have hcomp := (meromorphicAt_faddeevWord bs (m + p) 0 h.periodsPos.slitPlane
      (ζ + y)).comp_analyticAt
        (g := fun z : ℂ => z + y)
        (show AnalyticAt ℂ (fun z : ℂ => z + y) ζ by fun_prop)
    simpa only [D, Function.comp_def] using hcomp
  have hP : AnalyticAt ℂ P ζ := by
    unfold P fiveTermPoleFactor
    fun_prop
  have hE : AnalyticAt ℂ E ζ := by
    dsimp [E]
    fun_prop
  have hPne : P ζ ≠ 0 := by
    intro hz
    obtain ⟨k, hk⟩ := (fiveTermPoleFactor_eq_zero_iff h.fixedPoint m ζ).mp hz
    exact hζ k hk
  have hPord : meromorphicOrderAt P ζ = 0 := by
    simp [hP.meromorphicOrderAt_eq, (hP.analyticOrderAt_eq_zero).mpr hPne]
  have hEord : meromorphicOrderAt E ζ = 0 := by
    simp [hE.meromorphicOrderAt_eq,
      (hE.analyticOrderAt_eq_zero).mpr (Complex.exp_ne_zero _)]
  rw [meromorphicOrderAt_congr (fiveTermWordResidueKernel_eventuallyEq h ℓ p w y m ζ)]
  change meromorphicOrderAt ((N / D * E) / P) ζ =
    meromorphicOrderAt N ζ - meromorphicOrderAt D ζ
  rw [meromorphicOrderAt_div ((hN.div hD).mul hE.meromorphicAt) hP.meromorphicAt,
    meromorphicOrderAt_mul (hN.div hD) hE.meromorphicAt,
    meromorphicOrderAt_div hN hD, hPord, hEord]
  simp

/-- The finite common-line sum of word residue kernels is meromorphic; used by the rectangle
argument of [RW26, Radchenko, Wheeler (2026), Section 3.2]. -/
theorem meromorphic_fiveTermWordResidueSum {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ p : ℤ) (w y : ℂ) :
    Meromorphic (fiveTermWordResidueSum bs ℓ p w y τ) := by
  intro z
  unfold fiveTermWordResidueSum
  apply MeromorphicAt.fun_sum
  intro m _
  let c : ℂ := ((m : ℕ) : ℂ) *
    fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
      (letterWord bs 1 0 : ℂ)
  have hterm := (meromorphic_fiveTermWordResidueKernel h ℓ p ((m : ℕ) : ℤ) w y
    (z - c)).comp_analyticAt
      (g := fun ζ : ℂ => ζ - c)
      (show AnalyticAt ℂ (fun ζ : ℂ => ζ - c) z by fun_prop)
  simpa only [Function.comp_def, c] using hterm

/-- If every shifted summand has nonnegative order at a point, the common-line sum is bounded
on a punctured neighborhood; used for removable points on the strip rectangle. -/
lemma fiveTermWordResidueSum_bdd_of_order_nonneg {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ p : ℤ) (w y : ℂ) (z : ℂ)
    (horder : ∀ m : FiveTermIndex (letterWord bs),
      0 ≤ meromorphicOrderAt
        (fun ζ => fiveTermWordResidueKernel bs ℓ p w y τ ((m : ℕ) : ℤ)
          (ζ - ((m : ℕ) : ℂ) *
            fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
              (letterWord bs 1 0 : ℂ))) z) :
    IsBoundedUnder (· ≤ ·) (𝓝[≠] z)
      (fun ζ => ‖fiveTermWordResidueSum bs ℓ p w y τ ζ‖) := by
  let F (m : FiveTermIndex (letterWord bs)) (ζ : ℂ) :=
    fiveTermWordResidueKernel bs ℓ p w y τ ((m : ℕ) : ℤ)
      (ζ - ((m : ℕ) : ℂ) *
        fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
          (letterWord bs 1 0 : ℂ))
  have hterm (m : FiveTermIndex (letterWord bs)) : MeromorphicAt (F m) z := by
    exact (meromorphicAt_comp_sub_const_iff_meromorphicAt).2
      (meromorphic_fiveTermWordResidueKernel h ℓ p ((m : ℕ) : ℤ) w y _)
  have hlim (m : FiveTermIndex (letterWord bs)) :
      ∃ c : ℂ, Tendsto (F m) (𝓝[≠] z) (𝓝 c) :=
    tendsto_nhds_of_meromorphicOrderAt_nonneg (hterm m) (horder m)
  choose c hc using hlim
  have hsum := tendsto_finsetSum Finset.univ (fun m _ => hc m)
  have hsum' : Tendsto (fiveTermWordResidueSum bs ℓ p w y τ)
      (𝓝[≠] z) (𝓝 (∑ m : FiveTermIndex (letterWord bs), c m)) := by
    exact hsum
  exact hsum'.norm.isBoundedUnder_le

/-! ### Pole positions

The first coordinate of a summation index is an integer in `[0,c)`, and the second coordinate
enumerates distinct real poles. -/

/-- The common-line pole of the source pair `(m,k)`; used by the crossed-strip residue sum. -/
def fiveTermStripPolePosition (γ : SL(2, ℤ)) (τ : ℝ) (m k : ℤ) : ℂ :=
  (fiveTermLatticeArgument γ τ m k +
    (m : ℝ) * fltDenominator (γ : Mat(2, ℤ)) τ / (γ 1 0 : ℝ) : ℝ)

/-- Translating a word residue kernel carries its source-argument residue limit to the common
line; used by the crossed-strip residue fibers. -/
lemma tendsto_sub_mul_fiveTermWordResidueKernel_sub {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ : ℤ) (w : ℝ) (m k v₁ v₂ : ℤ) :
    Tendsto (fun z : ℂ =>
      (z - fiveTermStripPolePosition (letterWord bs) τ m k) *
        fiveTermWordResidueKernel bs ℓ v₁ w
          (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ m
          (z - (m : ℂ) * fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
            (letterWord bs 1 0 : ℂ)))
      (𝓝[≠] (fiveTermStripPolePosition (letterWord bs) τ m k))
      (𝓝 (fiveTermWordKernelResidue bs ℓ v₁ w
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ m
        (fiveTermLatticeArgument (letterWord bs) τ m k))) := by
  let c : ℂ := (m : ℂ) * fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
    (letterWord bs 1 0 : ℂ)
  let z₀ : ℂ := fiveTermLatticeArgument (letterWord bs) τ m k
  have hp : fiveTermStripPolePosition (letterWord bs) τ m k = z₀ + c := by
    dsimp [fiveTermStripPolePosition, z₀, c]
    push_cast
    ring
  have ht : Tendsto (fun z : ℂ => z - c)
      (𝓝[≠] (fiveTermStripPolePosition (letterWord bs) τ m k)) (𝓝[≠] z₀) := by
    simpa only [hp, sub_eq_add_neg, add_neg_cancel_right] using
      SIC.tendsto_add_const_nhdsNE (-c)
        (fiveTermStripPolePosition (letterWord bs) τ m k)
  have hr := (tendsto_sub_mul_fiveTermWordResidueKernel h ℓ w m k v₁ v₂).comp ht
  convert hr using 1
  funext z
  rw [hp]
  simp only [Function.comp_def]
  ring

/-- For a fixed first index, distinct second indices give distinct common-line poles. -/
lemma fiveTermStripPolePosition_injective {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (m : ℤ) :
    Function.Injective (fiveTermStripPolePosition γ τ m) := by
  intro k l hkl
  have hδ : (fltDenominator (γ : Mat(2, ℤ)) τ)⁻¹ - 1 ≠ 0 := by
    have hε := h.one_lt_fltDenominator
    exact ne_of_lt (sub_neg.mpr ((inv_lt_one₀ h.fltDenominator_pos).2 hε))
  have hr : fiveTermLatticeArgument γ τ m k = fiveTermLatticeArgument γ τ m l := by
    have hp := congrArg Complex.re hkl
    simp only [fiveTermStripPolePosition, Complex.ofReal_re] at hp
    linarith
  unfold fiveTermLatticeArgument at hr
  have hk : (k : ℝ) = (l : ℝ) := by
    apply (div_left_inj' hδ).mp at hr
    linarith
  exact_mod_cast hk

/-! ### Window residue fibers

A fiber records the residue from one contour index at one common-line pole. Injectivity in
the second source coordinate makes each such fiber a singleton or zero. -/

/-- The residue contribution of one contour index at a common-line position, restricted to
the source window `[a,a+N)`; used by the crossed-strip residue sum. -/
def fiveTermWindowResidueFiber (bs : List ℤ) (τ : ℝ) (a ℓ p : ℤ) (w y : ℝ)
    (m : FiveTermIndex (letterWord bs)) (s : ℂ) : ℂ :=
  ∑ mk ∈ fiveTermWindow (letterWord bs) a with
    mk.1 = ((m : ℕ) : ℤ) ∧
      fiveTermStripPolePosition (letterWord bs) τ mk.1 mk.2 = s,
    fiveTermWordKernelResidue bs ℓ p w y τ mk.1
      (fiveTermLatticeArgument (letterWord bs) τ mk.1 mk.2)

/-- A window pole has exactly its own residue in the corresponding fiber. -/
theorem fiveTermWindowResidueFiber_eq_of_pole {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (a ℓ p : ℤ) (w y : ℝ)
    (m : FiveTermIndex (letterWord bs)) (k : ℤ)
    (hmem : (((m : ℕ) : ℤ), k) ∈ fiveTermWindow (letterWord bs) a) :
    fiveTermWindowResidueFiber bs τ a ℓ p w y m
        (fiveTermStripPolePosition (letterWord bs) τ ((m : ℕ) : ℤ) k) =
      fiveTermWordKernelResidue bs ℓ p w y τ ((m : ℕ) : ℤ)
        (fiveTermLatticeArgument (letterWord bs) τ ((m : ℕ) : ℤ) k) := by
  unfold fiveTermWindowResidueFiber
  rw [Finset.sum_filter]
  calc
    _ = if (((m : ℕ) : ℤ), k).1 = ((m : ℕ) : ℤ) ∧
          fiveTermStripPolePosition (letterWord bs) τ (((m : ℕ) : ℤ), k).1
            (((m : ℕ) : ℤ), k).2 =
            fiveTermStripPolePosition (letterWord bs) τ ((m : ℕ) : ℤ) k then
          fiveTermWordKernelResidue bs ℓ p w y τ (((m : ℕ) : ℤ), k).1
            (fiveTermLatticeArgument (letterWord bs) τ (((m : ℕ) : ℤ), k).1
              (((m : ℕ) : ℤ), k).2) else 0 := by
        apply Finset.sum_eq_single_of_mem (((m : ℕ) : ℤ), k) hmem
        intro mk hmk hne
        by_cases hp : mk.1 = ((m : ℕ) : ℤ) ∧
            fiveTermStripPolePosition (letterWord bs) τ mk.1 mk.2 =
              fiveTermStripPolePosition (letterWord bs) τ ((m : ℕ) : ℤ) k
        · have hk : mk.2 = k := by
            have hs : fiveTermStripPolePosition (letterWord bs) τ ((m : ℕ) : ℤ) mk.2 =
                fiveTermStripPolePosition (letterWord bs) τ ((m : ℕ) : ℤ) k := by
              simpa only [hp.1] using hp.2
            exact (fiveTermStripPolePosition_injective h.fixedPoint ((m : ℕ) : ℤ)) hs
          exact (hne (Prod.ext hp.1 hk)).elim
        · simp [hp]
    _ = _ := by simp

/-- A contour index with no pole at a position contributes zero to every window fiber. -/
theorem fiveTermWindowResidueFiber_eq_zero (bs : List ℤ) (τ : ℝ)
    (a ℓ p : ℤ) (w y : ℝ) (m : FiveTermIndex (letterWord bs)) (s : ℂ)
    (hnot : ∀ k : ℤ,
      s ≠ fiveTermStripPolePosition (letterWord bs) τ ((m : ℕ) : ℤ) k) :
    fiveTermWindowResidueFiber bs τ a ℓ p w y m s = 0 := by
  unfold fiveTermWindowResidueFiber
  rw [Finset.sum_filter]
  apply Finset.sum_eq_zero
  intro mk hmk
  have hn : ¬(mk.1 = ((m : ℕ) : ℤ) ∧
      fiveTermStripPolePosition (letterWord bs) τ mk.1 mk.2 = s) := by
    rintro ⟨hm, hs⟩
    exact hnot mk.2 (hm ▸ hs.symm)
  simp [hn]

/-- Every finite summation index lies in `[0,c)` for `c = γ₁₀ > 0`. -/
lemma fiveTermIndex_range {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (m : FiveTermIndex γ) :
    0 ≤ (((m : ℕ) : ℤ)) ∧ (((m : ℕ) : ℤ)) < γ 1 0 := by
  constructor
  · exact_mod_cast Nat.zero_le m.val
  · have hm' : (((m : ℕ) : ℤ)) < ((γ 1 0).toNat : ℤ) := by
      exact_mod_cast m.isLt
    rw [Int.toNat_of_nonneg h.lowerLeft_pos.le] at hm'
    exact hm'

/-! ### Horizontal segment limits

The sector bounds for each kernel summand are uniform on a fixed translated horizontal segment.
Summing over the finite contour index makes both horizontal rectangle sides vanish. -/

/-- The upper sector estimate is uniform on a translated horizontal segment; used by
`tendsto_intervalIntegral_fiveTermWordResidueSum_upper`. -/
private lemma fiveTermWord_upper_segment_bound {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ p m : ℤ) (w y a b s : ℝ)
    (hRate : (fltDenominator (letterWord bs : Mat(2, ℤ)) τ)⁻¹ <
      fiveTermUpperRate (letterWord bs) ℓ w τ) :
    ∃ g : ℝ → ℝ, Tendsto g atTop (𝓝 0) ∧
      ∀ᶠ Y : ℝ in atTop, ∀ t ∈ uIcc a b,
        ‖fiveTermWordResidueKernel bs ℓ p w y τ m
          ((t : ℂ) + Y * I - (s : ℂ))‖ ≤ g Y := by
  obtain ⟨C, κ, R, hκ, hbound⟩ :=
    exists_norm_fiveTermWordResidueKernel_upper h ℓ p m w y 1 hRate
  simpa using
    (exists_horizontal_segment_bound_of_sector
      (fiveTermWordResidueKernel bs ℓ p w y τ m) a b s 1 C κ R
      (by norm_num) hκ (by simpa only [one_mul] using hbound))

/-- The lower sector estimate is uniform on a translated horizontal segment; used by
`tendsto_intervalIntegral_fiveTermWordResidueSum_lower`. -/
private lemma fiveTermWord_lower_segment_bound {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ p m : ℤ) (w y a b s : ℝ)
    (hRate : fiveTermLowerRate (letterWord bs) ℓ p w y τ < 0) :
    ∃ g : ℝ → ℝ, Tendsto g atTop (𝓝 0) ∧
      ∀ᶠ Y : ℝ in atTop, ∀ t ∈ uIcc a b,
        ‖fiveTermWordResidueKernel bs ℓ p w y τ m
          ((t : ℂ) + (-Y) * I - (s : ℂ))‖ ≤ g Y := by
  obtain ⟨C, κ, R, hκ, hbound⟩ :=
    exists_norm_fiveTermWordResidueKernel_lower h ℓ p m w y 1 hRate
  simpa using
    (exists_horizontal_segment_bound_of_sector
      (fiveTermWordResidueKernel bs ℓ p w y τ m) a b s (-1) C κ R
      (by norm_num) hκ (by simpa only [neg_one_mul, one_mul] using hbound))

/-- The upper horizontal side of a fixed rectangle for the word residue sum vanishes as its
height grows. -/
lemma tendsto_intervalIntegral_fiveTermWordResidueSum_upper {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ p : ℤ) (w y a b : ℝ)
    (hupper : (fltDenominator (letterWord bs : Mat(2, ℤ)) τ)⁻¹ <
      fiveTermUpperRate (letterWord bs) ℓ w τ) :
    Tendsto (fun Y : ℝ => ∫ t : ℝ in a..b,
      fiveTermWordResidueSum bs ℓ p w y τ ((t : ℂ) + Y * I)) atTop (𝓝 0) := by
  let F (m : FiveTermIndex (letterWord bs)) (t Y : ℝ) :=
    fiveTermWordResidueKernel bs ℓ p w y τ ((m : ℕ) : ℤ)
      ((t : ℂ) + Y * I - ((m : ℕ) : ℂ) *
        fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
          (letterWord bs 1 0 : ℂ))
  have hbound (m : FiveTermIndex (letterWord bs)) :
      ∃ g : ℝ → ℝ, Tendsto g atTop (𝓝 0) ∧
        ∀ᶠ Y : ℝ in atTop, ∀ t ∈ uIcc a b, ‖F m t Y‖ ≤ g Y := by
    let s : ℝ := ((m : ℕ) : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
      (letterWord bs 1 0 : ℝ)
    obtain ⟨g, hg, hb⟩ := fiveTermWord_upper_segment_bound h ℓ p
      ((m : ℕ) : ℤ) w y a b s hupper
    refine ⟨g, hg, ?_⟩
    have hc : ((m : ℕ) : ℂ) * fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
        (letterWord bs 1 0 : ℂ) = (s : ℂ) := by norm_cast
    simpa only [F, hc] using hb
  change Tendsto (fun Y : ℝ => ∫ t : ℝ in a..b, ∑ m, F m t Y) atTop (𝓝 0)
  exact tendsto_intervalIntegral_sum_of_bounds F a b hbound

/-- The lower horizontal side of a fixed rectangle for the word residue sum vanishes as its
height grows. -/
lemma tendsto_intervalIntegral_fiveTermWordResidueSum_lower {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ p : ℤ) (w y a b : ℝ)
    (hlower : fiveTermLowerRate (letterWord bs) ℓ p w y τ < 0) :
    Tendsto (fun Y : ℝ => ∫ t : ℝ in a..b,
      fiveTermWordResidueSum bs ℓ p w y τ ((t : ℂ) + (-Y) * I)) atTop (𝓝 0) := by
  let F (m : FiveTermIndex (letterWord bs)) (t Y : ℝ) :=
    fiveTermWordResidueKernel bs ℓ p w y τ ((m : ℕ) : ℤ)
      ((t : ℂ) + (-Y) * I - ((m : ℕ) : ℂ) *
        fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
          (letterWord bs 1 0 : ℂ))
  have hbound (m : FiveTermIndex (letterWord bs)) :
      ∃ g : ℝ → ℝ, Tendsto g atTop (𝓝 0) ∧
        ∀ᶠ Y : ℝ in atTop, ∀ t ∈ uIcc a b, ‖F m t Y‖ ≤ g Y := by
    let s : ℝ := ((m : ℕ) : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
      (letterWord bs 1 0 : ℝ)
    obtain ⟨g, hg, hb⟩ := fiveTermWord_lower_segment_bound h ℓ p
      ((m : ℕ) : ℤ) w y a b s hlower
    refine ⟨g, hg, ?_⟩
    have hc : ((m : ℕ) : ℂ) * fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
        (letterWord bs 1 0 : ℂ) = (s : ℂ) := by norm_cast
    simpa only [F, hc] using hb
  change Tendsto (fun Y : ℝ => ∫ t : ℝ in a..b, ∑ m, F m t Y) atTop (𝓝 0)
  exact tendsto_intervalIntegral_sum_of_bounds F a b hbound

/-! ### Regularity on the translated line

Translation by `(ε-1)/c` permutes the contour indices modulo `c`. The corresponding source
arguments differ by a period-lattice shift, so regularity on the left line transfers to the
right line. -/

/-- Every shifted contour index has a representative in `[0,c)` and an integer quotient;
used by `fiveTerm_strip_right_crossing`. -/
private lemma fiveTermStrip_reindex_exists {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (m : FiveTermIndex γ) :
    ∃ m' : FiveTermIndex γ, ∃ M : ℤ,
      ((m : ℕ) : ℤ) + γ 0 0 - M * γ 1 0 = ((m' : ℕ) : ℤ) + 1 := by
  let c : ℕ := (γ 1 0).toNat
  let n : ℤ := ((m : ℕ) : ℤ) + γ 0 0 - 1
  have hcpos : 0 < γ 1 0 := h.lowerLeft_pos
  have hc : (c : ℤ) = γ 1 0 := Int.toNat_of_nonneg hcpos.le
  have hcne : NeZero c := ⟨by omega⟩
  let m' : Fin c := @Fin.intCast c hcne n
  refine ⟨m', n / (c : ℤ), ?_⟩
  have hm' : ((m' : ℕ) : ℤ) = n % (c : ℤ) := by
    calc
      _ = (((n % (c : ℤ)).toNat : ℕ) : ℤ) := by
        exact congrArg (fun k : ℕ => (k : ℤ)) (@Fin.val_intCast c hcne n)
      _ = _ := Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  have hdiv := Int.emod_add_mul_ediv n (c : ℤ)
  dsimp [n] at hm' hdiv ⊢
  linear_combination hc * (n / (c : ℤ)) - hdiv - hm'

/-- The translated right crossing is an integral period-lattice shift of the reindexed left
crossing; used by `fiveTerm_strip_right_crossing`. -/
private lemma fiveTerm_strip_shift_real {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (m m' M : ℤ)
    (hm : m + γ 0 0 - M * γ 1 0 = m' + 1) (x : ℝ) :
    x + (fltDenominator (γ : Mat(2, ℤ)) τ - 1) / (γ 1 0 : ℝ) -
        (m : ℝ) * fltDenominator (γ : Mat(2, ℤ)) τ / (γ 1 0 : ℝ) =
      x - (m' : ℝ) * fltDenominator (γ : Mat(2, ℤ)) τ / (γ 1 0 : ℝ) +
        ((γ 0 0 - M * γ 1 0 : ℤ) : ℝ) * τ +
          ((γ 0 1 - M * γ 1 1 : ℤ) : ℝ) := by
  have hc : (γ 1 0 : ℝ) ≠ 0 := by exact_mod_cast h.lowerLeft_pos.ne'
  have hdetZ : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = (1 : ℤ) := by
    simpa only [Matrix.det_fin_two] using Matrix.SpecialLinearGroup.det_coe γ
  have hdet : (γ 0 0 : ℝ) * γ 1 1 - (γ 0 1 : ℝ) * γ 1 0 = 1 := by
    exact_mod_cast hdetZ
  have hε : fltDenominator (γ : Mat(2, ℤ)) τ =
      (γ 1 0 : ℝ) * τ + γ 1 1 := rfl
  have hmR : (m : ℝ) + γ 0 0 - (M : ℝ) * γ 1 0 = (m' : ℝ) + 1 := by
    exact_mod_cast hm
  have hK : (m' : ℝ) - m + 1 = (γ 0 0 : ℝ) - M * γ 1 0 := by
    linarith [hmR]
  have hKε := congrArg (fun t : ℝ => t * fltDenominator (γ : Mat(2, ℤ)) τ) hK
  have hεK := congrArg (fun t : ℝ => ((γ 0 0 : ℝ) - M * γ 1 0) * t) hε
  push_cast
  field_simp [hc]
  nlinarith [hdet, hKε, hεK]

/-- The source arguments on corresponding right and left contours differ by the same
period-lattice shift; used by `fiveTerm_strip_right_crossing`. -/
private lemma fiveTerm_strip_latticeArgument_shift {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (m m' M k : ℤ)
    (hm : m + γ 0 0 - M * γ 1 0 = m' + 1) :
    fiveTermLatticeArgument γ τ m k =
      fiveTermLatticeArgument γ τ m' (k + γ 0 1 + M * (1 - γ 1 1)) +
        ((γ 0 0 - M * γ 1 0 : ℤ) : ℝ) * τ +
          ((γ 0 1 - M * γ 1 1 : ℤ) : ℝ) := by
  let ε := fltDenominator (γ : Mat(2, ℤ)) τ
  let c : ℝ := γ 1 0
  let a : ℝ := γ 0 0
  let b : ℝ := γ 0 1
  let d : ℝ := γ 1 1
  have hε0 : ε ≠ 0 := ne_of_gt h.fltDenominator_pos
  have hδ : ε⁻¹ - 1 ≠ 0 := by
    exact ne_of_lt (sub_neg.mpr
      ((inv_lt_one₀ h.fltDenominator_pos).2 h.one_lt_fltDenominator))
  have hroot : a * τ + b = τ * ε := by
    have hfixed := h.flt_eq
    change (a * τ + b) / ε = τ at hfixed
    exact (div_eq_iff hε0).mp hfixed
  have hε : ε = c * τ + d := rfl
  have hmR : (m : ℝ) + a - (M : ℝ) * c = (m' : ℝ) + 1 := by
    dsimp [a, c]
    exact_mod_cast hm
  have hshift : (a - (M : ℝ) * c) * τ + b - M * d = (τ - M) * ε := by
    have hεM := congrArg (fun t : ℝ => (M : ℝ) * t) hε
    nlinarith [hroot, hεM]
  have hδs : (ε⁻¹ - 1) * ((a - (M : ℝ) * c) * τ + b - M * d) =
      ((m : ℝ) - m') * τ - b - M * (1 - d) := by
    rw [hshift]
    have hbasic : (ε⁻¹ - 1) * ((τ - M) * ε) = (1 - ε) * (τ - M) := by
      field_simp [hε0]
    rw [hbasic]
    have hmτ := congrArg (fun t : ℝ => t * τ) hmR
    have hεM := congrArg (fun t : ℝ => (M : ℝ) * t) hε
    nlinarith [hroot, hεM, hmτ]
  unfold fiveTermLatticeArgument
  push_cast
  apply (div_eq_iff hδ).2
  calc
    (m : ℝ) * τ + k = (m' : ℝ) * τ + (k + b + M * (1 - d)) +
        (ε⁻¹ - 1) * ((a - M * c) * τ + b - M * d) := by
      rw [hδs]
      ring
    _ = (((m' : ℝ) * τ + (k + b + M * (1 - d))) / (ε⁻¹ - 1)) *
          (ε⁻¹ - 1) + ((a - M * c) * τ + b - M * d) * (ε⁻¹ - 1) := by
      rw [div_mul_cancel₀ _ hδ]
      ring
    _ = _ := by ring

/-- Reindexing carries regular residue crossings on the left line to the translated right
line, as in [RW26, Radchenko, Wheeler (2026), Section 3.2]. -/
lemma fiveTerm_strip_right_crossing {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (v₁ v₂ : ℤ) (x : ℝ)
    (hreg : ∀ m : FiveTermIndex (letterWord bs),
      IsFiveTermResidueCrossing (letterWord bs) τ ((m : ℕ) : ℤ)
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂)
        (x - ((m : ℕ) : ℝ) *
          fltDenominator (letterWord bs : Mat(2, ℤ)) τ / (letterWord bs 1 0 : ℝ)))
    (m : FiveTermIndex (letterWord bs)) :
    IsFiveTermResidueCrossing (letterWord bs) τ ((m : ℕ) : ℤ)
      (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂)
      (x + (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
        (letterWord bs 1 0 : ℝ) -
          ((m : ℕ) : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
            (letterWord bs 1 0 : ℝ)) := by
  obtain ⟨m', M, hm⟩ := fiveTermStrip_reindex_exists h.fixedPoint m
  let K : ℤ := letterWord bs 0 0 - M * letterWord bs 1 0
  let L : ℤ := letterWord bs 0 1 - M * letterWord bs 1 1
  let xl := x - ((m' : ℕ) : ℝ) *
    fltDenominator (letterWord bs : Mat(2, ℤ)) τ / (letterWord bs 1 0 : ℝ)
  let xr := x + (fltDenominator (letterWord bs : Mat(2, ℤ)) τ - 1) /
    (letterWord bs 1 0 : ℝ) -
      ((m : ℕ) : ℝ) * fltDenominator (letterWord bs : Mat(2, ℤ)) τ /
        (letterWord bs 1 0 : ℝ)
  have hshift : xr = xl + (K : ℝ) * τ + L := by
    convert fiveTerm_strip_shift_real h.fixedPoint
      ((m : ℕ) : ℤ) ((m' : ℕ) : ℤ) M hm x using 1
  have hleft := hreg m'
  refine ⟨?_, ?_⟩
  · simpa only [xr, xl, hshift] using
      IsRegularPeriodLatticeCrossing.add_int_mul_add_int τ
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) xl K L hleft.lattice
  · intro k hk
    have harg := fiveTerm_strip_latticeArgument_shift h.fixedPoint
      ((m : ℕ) : ℤ) ((m' : ℕ) : ℤ) M k hm
    have hleftEq : xl = fiveTermLatticeArgument (letterWord bs) τ ((m' : ℕ) : ℤ)
        (k + letterWord bs 0 1 + M * (1 - letterWord bs 1 1)) := by
      dsimp [xr, xl, K, L] at hshift hk
      linarith [harg]
    exact hleft.pole _ hleftEq

end SIC

end
