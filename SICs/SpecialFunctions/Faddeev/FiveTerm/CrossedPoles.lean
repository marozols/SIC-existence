/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.Faddeev.FiveTerm.ContourGeometry
import SICs.SpecialFunctions.Faddeev.FiveTerm.Rectangle

/-!
# Crossed right poles near a boundary period

Crossed right-pole stability, small-square residues, and denominator exclusion at rational
crossing points.

This module prepares the boundary passage of the contour deformation in [RW26, Radchenko,
Wheeler (2026), Theorem 3, `thm:5term.mod.fad`, equation (23), `eq:5term.int`, Appendix A.2,
`app:mod.fad`] at `n = h = 0`: the finitely many right poles crossed by a straight contour carry
residues that do not converge at a real period, and the boundary integrals over small squares
replace them.

## The argument

A right pole of the `m`-th kernel with forward index `N = kc-ja+m ≥ 0` and backward index `j`
has real part `((N-m) Re ε + j)/c`, and a zero `k-(n+j)τ` of `Φ_{γ,n,0}` with backward index
`N = -(kc+(n+j)d) > 0` has real part `(-N-(n+j) Re ε)/c`. While `Re ε` stays between two
positive bounds, both formulas confine the indices of the right poles left of a vertical line,
and of the zeros right of one, to a finite set independent of the period. Each such point moves
continuously with the period. Hence, if no right pole lies on a vertical line at `τ₀`, then for
nearby periods none does and the same ones lie to its left.

At a real period `τ₀`, both families lie on the real axis at lattice points of `ℤ+ℤτ₀`, the
zeros translated by `-y`. When `τ₀` is irrational distinct indices give distinct right poles, and
when `y` avoids the lattice no translated zero meets a right pole. So a small square centred at
the position of one right pole at `τ₀` contains, for nearby periods in the upper half plane,
that pole and no other right pole or translated zero, and none lies on its boundary. The local
rectangle theorem `integral_boundary_rect_fiveTermKernelUHP_of_local` then gives its
residue as the boundary integral. The rational-crossing calculation of Section 3.2 also
excludes denominator zeros by comparing the two rational coordinates at an irrational period.
-/

noncomputable section

open Complex Real Filter Set
open scoped Topology MatrixGroups

namespace SIC


/-! ### Denominator indices at rational crossings

For a real irrational period, comparing rational coefficients in a lattice equality
excludes denominator zeros at nonnegative rational crossing points. The calculation uses
only the affine denominator `ε=cρ+1-d` and the positive displacement ratio `V/H`.
Here the integer `d` parametrizes the lower-right matrix entry `1-d`; it is not a dimension.
-/

/-- At a rational crossing, the lattice equality forces the denominator index
`(1-d)k-cℓ` to be negative. This is the elementary no-pinching calculation in the crossed
contour argument of [RW26, Radchenko, Wheeler (2026), Section 3.2, proof of Theorem 2,
`thm:fg.equs`], with affine denominator `ε=cρ+1-d` and positive displacement `V/H`. -/
theorem faddeevCrossedDenominatorIndex_neg
    (ρ ε : ℝ) (d c H V m p j k l : ℤ)
    (hρ : Irrational ρ) (hc : 0 < c) (hH : 0 < H) (hV : 0 < V) (hj : 0 ≤ j)
    (hε : ε = (c : ℝ) * ρ + 1 - d)
    (harg : (j : ℝ) / c - ((m + p : ℤ) : ℝ) * ε / c -
      (ε - 1) * V / (c * H) = (k : ℝ) * ρ + l) :
    (1 - d) * k - c * l < 0 := by
  let A : ℤ := c * (H * (m + p + k) + V)
  let B : ℤ := H * j - (H * (m + p) + V) * (1 - d) + V - c * H * l
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hc)
  have hHR : (H : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hH)
  have hlinear : (A : ℝ) * ρ = B := by
    dsimp [A, B]
    push_cast
    have harg' := harg
    field_simp [hcR, hHR] at harg'
    push_cast at harg'
    linear_combination -harg' - (H * (m + p) + V : ℝ) * hε
  have hrat : (((A : ℤ) : ℚ) : ℝ) * ρ = (((B : ℤ) : ℚ) : ℝ) := by
    simpa using hlinear
  obtain ⟨hAq, hBq⟩ := ratCast_eq_zero_of_irrational_mul hρ hrat
  have hA : A = 0 := by exact_mod_cast hAq
  have hB : B = 0 := by exact_mod_cast hBq
  have hA' : H * (m + p + k) + V = 0 := by
    dsimp [A] at hA
    have hc0 : c ≠ 0 := by omega
    exact (mul_eq_zero.mp hA).resolve_left hc0
  have hB' : H * j - (H * (m + p) + V) * (1 - d) + V - c * H * l = 0 := hB
  have hident : H * ((1 - d) * k - c * l) = -H * j - V := by
    linear_combination (1 - d) * hA' + hB'
  have hHRpos : (0 : ℝ) < H := by exact_mod_cast hH
  have hJRnonneg : (0 : ℝ) ≤ j := by exact_mod_cast hj
  have hVRpos : (0 : ℝ) < V := by exact_mod_cast hV
  have hidentR : (H : ℝ) * (((1 - d) * k - c * l : ℤ) : ℝ) =
      -(H : ℝ) * j - V := by exact_mod_cast hident
  have hqR : ((((1 - d) * k - c * l : ℤ) : ℝ)) < 0 := by
    nlinarith [mul_nonneg hHRpos.le hJRnonneg]
  exact_mod_cast hqR

/-! ### Poles at a real period

At a real period the poles `ε(k-jσ) = (kc-ja)τ₀+(kd-jb)` are real lattice points, distinct for
distinct indices when `τ₀` is irrational. -/

/-- The pole `ε(k-jσ)` lies in `ℤ+ℤτ` wherever `j_γ(τ) ≠ 0`: it is `(kc-ja)τ+(kd-jb)` by
`faddeevModularUHPPole_eq`. -/
theorem isPeriodLatticePoint_faddeevModularUHPPole (γ : SL(2, ℤ)) (τ : ℂ)
    (hε : fltDenominator (γ : Mat(2, ℤ)) τ ≠ 0) (k : ℤ) (j : ℕ) :
    IsPeriodLatticePoint τ (faddeevModularUHPPole γ τ k j) := by
  refine ⟨k * γ 1 1 - (j : ℤ) * γ 0 1,
    k * γ 1 0 - (j : ℤ) * γ 0 0, ?_⟩
  rw [faddeevModularUHPPole_eq γ τ hε]
  ring

/-- At a real period the pole `ε(k-jσ)` is real. -/
theorem im_faddeevModularUHPPole_ofReal (γ : SL(2, ℤ)) (τ₀ : ℝ) (k : ℤ) (j : ℕ) :
    (faddeevModularUHPPole γ (τ₀ : ℂ) k j).im = 0 := by
  by_cases hε : fltDenominator (γ : Mat(2, ℤ)) (τ₀ : ℂ) = 0
  · simp [faddeevModularUHPPole, hε]
  · rw [faddeevModularUHPPole_eq γ _ hε]
    simp

/-- At a real period with `j_γ(τ₀) ≠ 0`, no pole `ε(k-jσ)` lies on the vertical line
through a crossing `x` outside `ℤ+ℤτ₀`: the pole is a real lattice point. -/
theorem re_faddeevModularUHPPole_ofReal_ne (γ : SL(2, ℤ)) (τ₀ : ℝ)
    (hε : fltDenominator (γ : Mat(2, ℤ)) (τ₀ : ℂ) ≠ 0) (x : ℝ)
    (hx : ¬ IsPeriodLatticePoint τ₀ (x : ℂ)) (k : ℤ) (j : ℕ) :
    (faddeevModularUHPPole γ (τ₀ : ℂ) k j).re ≠ x := by
  intro hEq
  apply hx
  have hp : faddeevModularUHPPole γ (τ₀ : ℂ) k j = (x : ℂ) := by
    apply Complex.ext
    · simpa using hEq
    · simpa using im_faddeevModularUHPPole_ofReal γ τ₀ k j
  rw [← hp]
  exact isPeriodLatticePoint_faddeevModularUHPPole γ (τ₀ : ℂ) hε k j

/-- At an irrational real period with `j_γ(τ₀) ≠ 0`, distinct indices give distinct poles
`(kc-ja)τ₀+(kd-jb)`, by the irrationality of `τ₀` and `ad-bc = 1`. -/
theorem faddeevModularUHPPole_ofReal_injective (γ : SL(2, ℤ)) (τ₀ : ℝ) (hτ₀ : Irrational τ₀)
    (hε : fltDenominator (γ : Mat(2, ℤ)) (τ₀ : ℂ) ≠ 0) :
    Function.Injective (fun kj : ℤ × ℕ => faddeevModularUHPPole γ (τ₀ : ℂ) kj.1 kj.2) := by
  rintro ⟨k, j⟩ ⟨k', j'⟩ h
  dsimp at h
  rw [faddeevModularUHPPole_eq γ _ hε,
    faddeevModularUHPPole_eq γ _ hε] at h
  have hcoord := (intCast_add_intCast_mul_eq_iff_of_irrational τ₀ hτ₀
    (k * γ 1 1 - (j : ℤ) * γ 0 1)
    (k * γ 1 0 - (j : ℤ) * γ 0 0)
    (k' * γ 1 1 - (j' : ℤ) * γ 0 1)
    (k' * γ 1 0 - (j' : ℤ) * γ 0 0)).mp (by simpa only [add_comm] using h)
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = (1 : ℤ) :=
    det_fin_two_cast_eq_one γ
  have hk : k = k' := by
    apply sub_eq_zero.mp
    calc
      k - k' = (k - k') * (γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0) := by rw [hdet]; ring
      _ = 0 := by
        linear_combination (γ 0 0) * hcoord.1 - (γ 0 1) * hcoord.2
  have hj : j = j' := by
    have hj' : (j : ℤ) = j' := by
      apply sub_eq_zero.mp
      calc
        (j : ℤ) - j' = ((j : ℤ) - j') *
            (γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0) := by rw [hdet]; ring
        _ = 0 := by
          linear_combination (γ 1 0) * hcoord.1 - (γ 1 1) * hcoord.2
    exact_mod_cast hj'
  exact Prod.ext hk hj

/-! ### Uniform index bounds near a period

While `Re ε` stays between `Re j_γ(τ₀)/2` and `2 Re j_γ(τ₀)`, the real-part formulas bound the
indices of the right poles left of a line and of the zeros right of one. -/

/-- Keeps the real denominator between two positive bounds; used by
`exists_finset_fiveTermPoles_re_lt_nhds` and
`exists_finset_faddeevModularUHPZeros_le_re_nhds`. -/
private lemma eventually_re_fltDenominator_between (γ : SL(2, ℤ)) (τ₀ : ℂ)
    (he : 0 < (fltDenominator (γ : Mat(2, ℤ)) τ₀).re) :
    ∀ᶠ τ : ℂ in 𝓝 τ₀,
      (fltDenominator (γ : Mat(2, ℤ)) τ₀).re / 2 <
        (fltDenominator (γ : Mat(2, ℤ)) τ).re ∧
      (fltDenominator (γ : Mat(2, ℤ)) τ).re <
        2 * (fltDenominator (γ : Mat(2, ℤ)) τ₀).re := by
  have hcont : ContinuousAt
      (fun τ : ℂ => (fltDenominator (γ : Mat(2, ℤ)) τ).re) τ₀ := by
    unfold fltDenominator
    fun_prop
  have hlo := hcont.eventually
    (isOpen_Ioi.mem_nhds (show
      (fltDenominator (γ : Mat(2, ℤ)) τ₀).re / 2 <
        (fltDenominator (γ : Mat(2, ℤ)) τ₀).re by linarith))
  have hhi := hcont.eventually
    (isOpen_Iio.mem_nhds (show
      (fltDenominator (γ : Mat(2, ℤ)) τ₀).re <
        2 * (fltDenominator (γ : Mat(2, ℤ)) τ₀).re by linarith))
  exact hlo.and hhi

/-- If `e/2 < E < 2e`, then `aE ≤ 2|a|e`; used by
`exists_finset_fiveTermPoles_re_lt_nhds` and
`exists_finset_faddeevModularUHPZeros_le_re_nhds`. -/
private lemma mul_le_two_abs_mul (a e E : ℝ) (hlo : e / 2 < E) (hhi : E < 2 * e) :
    a * E ≤ 2 * |a| * e := by
  calc
    a * E ≤ |a| * E :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
    _ ≤ |a| * (2 * e) :=
      mul_le_mul_of_nonneg_left hhi.le (abs_nonneg _)
    _ = 2 * |a| * e := by ring

/-- Near a period `τ₀` with `Re j_γ(τ₀) > 0`, the right poles of the `m`-th kernel to the left of
the line `Re z = B` have indices in one finite set: their real parts `((N-m) Re ε + j)/c`
(`re_faddeevModularUHPPole`) bound `N ≥ 0` and `j` uniformly while `Re ε` stays near
`Re j_γ(τ₀)`, and `finite_fiveTermPoleIndices_lt` counts them. -/
theorem exists_finset_fiveTermPoles_re_lt_nhds (γ : SL(2, ℤ)) (hc : 0 < γ 1 0)
    (m : ℤ) (τ₀ : ℂ) (he : 0 < (fltDenominator (γ : Mat(2, ℤ)) τ₀).re) (B : ℝ) :
    ∃ G : Finset (ℤ × ℕ), ∀ᶠ τ : ℂ in 𝓝 τ₀, ∀ kj : ℤ × ℕ,
      0 ≤ faddeevModularUHPIndex γ m kj.1 kj.2 →
        (faddeevModularUHPPole γ τ kj.1 kj.2).re < B → kj ∈ G := by
  let e := (fltDenominator (γ : Mat(2, ℤ)) τ₀).re
  let C := (γ 1 0 : ℝ) * B + 2 * |(m : ℝ)| * e
  have he' : 0 < e / 2 := by dsimp [e]; linarith
  let hfin := finite_fiveTermPoleIndices_lt γ hc m he' C
  refine ⟨hfin.toFinset, ?_⟩
  filter_upwards [eventually_re_fltDenominator_between γ τ₀ he] with τ hτ
  intro kj hN hreal
  have hε : fltDenominator (γ : Mat(2, ℤ)) τ ≠ 0 :=
    Complex.ne_zero_of_re_pos (by linarith [hτ.1])
  have hc' : (0 : ℝ) < (γ 1 0 : ℝ) := by exact_mod_cast hc
  have hNr : (0 : ℝ) ≤ faddeevModularUHPIndex γ m kj.1 kj.2 := by
    exact_mod_cast hN
  have hsum : (faddeevModularUHPIndex γ m kj.1 kj.2 : ℝ) *
      (fltDenominator (γ : Mat(2, ℤ)) τ).re + kj.2 <
      (γ 1 0 : ℝ) * B + (m : ℝ) *
        (fltDenominator (γ : Mat(2, ℤ)) τ).re := by
    rw [re_faddeevModularUHPPole γ hc τ hε m kj.1 kj.2] at hreal
    apply (div_lt_iff₀ hc').mp at hreal
    nlinarith
  have hm := mul_le_two_abs_mul (m : ℝ) e
    (fltDenominator (γ : Mat(2, ℤ)) τ).re hτ.1 hτ.2
  have hlow : (faddeevModularUHPIndex γ m kj.1 kj.2 : ℝ) * (e / 2) ≤
      (faddeevModularUHPIndex γ m kj.1 kj.2 : ℝ) *
        (fltDenominator (γ : Mat(2, ℤ)) τ).re :=
    mul_le_mul_of_nonneg_left hτ.1.le hNr
  exact hfin.mem_toFinset.mpr ⟨hN, by dsimp [C]; linarith⟩

/-- The pair `(N,j)` determines the zero coordinate `(k,j)` when `c > 0`; used by
`finite_faddeevModularUHPZeroIndices_lt`. -/
private lemma faddeevModularUHPZero_index_pair_injective (γ : SL(2, ℤ))
    (hc : 0 < γ 1 0) (n : ℤ) :
    Function.Injective (fun kj : ℤ × ℕ =>
      (-(kj.1 * γ 1 0 + (n + (kj.2 : ℤ)) * γ 1 1), kj.2)) := by
  rintro ⟨k, j⟩ ⟨k', j'⟩ heq
  have hj : j = j' := congrArg Prod.snd heq
  subst j'
  have hN := congrArg Prod.fst heq
  have hkc : k * γ 1 0 = k' * γ 1 0 := by
    dsimp at hN
    omega
  exact Prod.ext (mul_right_cancel₀ hc.ne' hkc) rfl

/-- Finitely many zero coordinates satisfy `N > 0` and `N + je < C`; used by
`exists_finset_faddeevModularUHPZeros_le_re_nhds`. -/
private lemma finite_faddeevModularUHPZeroIndices_lt (γ : SL(2, ℤ))
    (hc : 0 < γ 1 0) (n : ℤ) {e : ℝ} (he : 0 < e) (C : ℝ) :
    {kj : ℤ × ℕ |
      0 < -(kj.1 * γ 1 0 + (n + (kj.2 : ℤ)) * γ 1 1) ∧
      ((-(kj.1 * γ 1 0 + (n + (kj.2 : ℤ)) * γ 1 1) : ℤ) : ℝ) +
        kj.2 * e < C}.Finite := by
  let index : ℤ × ℕ → ℤ := fun kj =>
    -(kj.1 * γ 1 0 + (n + (kj.2 : ℤ)) * γ 1 1)
  let f : ℤ × ℕ → ℤ × ℕ := fun kj => (index kj, kj.2)
  let T : Set (ℤ × ℕ) :=
    {kj | 0 < index kj ∧ (index kj : ℝ) + kj.2 * e < C}
  have himage : (f '' T).Finite :=
    ((Set.finite_Icc (1 : ℤ) ⌈C⌉).prod
      (Set.finite_Icc (0 : ℕ) ⌈C / e⌉₊)).subset (by
      rintro _ ⟨kj, ⟨hN, hsum⟩, rfl⟩
      have hNr : (0 : ℝ) ≤ index kj := by exact_mod_cast hN.le
      have hjr : (0 : ℝ) ≤ kj.2 := Nat.cast_nonneg _
      have hNbound : index kj ≤ ⌈C⌉ := by
        have : (index kj : ℝ) ≤ C := by nlinarith [mul_nonneg hjr he.le]
        exact_mod_cast this.trans (Int.le_ceil C)
      have hjbound : kj.2 ≤ ⌈C / e⌉₊ := by
        have : (kj.2 : ℝ) ≤ C / e := (le_div_iff₀ he).mpr (by nlinarith)
        exact_mod_cast this.trans (Nat.le_ceil _)
      change (1 ≤ index kj ∧ index kj ≤ ⌈C⌉) ∧
        (0 ≤ kj.2 ∧ kj.2 ≤ ⌈C / e⌉₊)
      exact ⟨⟨by omega, hNbound⟩, ⟨Nat.zero_le _, hjbound⟩⟩)
  have hinj : Set.InjOn f T := fun _ _ _ _ heq =>
    faddeevModularUHPZero_index_pair_injective γ hc n heq
  exact Set.Finite.of_finite_image himage hinj

/-- The zero coordinate `u = k-(n+j)τ` satisfies `c Re u = -N-(n+j) Re ε`; used by
`exists_finset_faddeevModularUHPZeros_le_re_nhds`. -/
private lemma re_faddeevModularUHPZero_coordinate (γ : SL(2, ℤ)) (n k N : ℤ)
    (j : ℕ) (τ : ℂ)
    (hN : N = -(k * γ 1 0 + (n + (j : ℤ)) * γ 1 1)) :
    (γ 1 0 : ℝ) * ((k : ℝ) - ((n : ℝ) + j) * τ.re) =
      -((n : ℝ) + j) * (fltDenominator (γ : Mat(2, ℤ)) τ).re - N := by
  have hlin : ((γ 1 0 : ℤ) : ℂ) *
      ((k : ℂ) - ((n + (j : ℤ) : ℤ) : ℂ) * τ) =
      -((n + (j : ℤ) : ℤ) : ℂ) *
        fltDenominator (γ : Mat(2, ℤ)) τ - N := by
    rw [hN]
    unfold fltDenominator
    push_cast
    ring
  simpa [Complex.mul_re, Complex.sub_re, Complex.add_re, Complex.add_im] using
    congrArg Complex.re hlin

/-- Near a period `τ₀` with `Re j_γ(τ₀) > 0`, the zeros of `Φ_{γ,n,0}` to the right of the line
`Re z = A` lie at `k-(n+j)τ` with `(k,j)` in one finite set: a zero `k-(n+j)τ` has backward
index `N = -(kc+(n+j)d) > 0` (`faddeevModularUHPZero_coordinates`) and real part
`(-N-(n+j) Re ε)/c`, which bounds `N` and `j` uniformly while `Re ε` stays near `Re j_γ(τ₀)`. -/
theorem exists_finset_faddeevModularUHPZeros_le_re_nhds (γ : SL(2, ℤ))
    (hc : 0 < γ 1 0) (n : ℤ) (τ₀ : ℂ) (he : 0 < (fltDenominator (γ : Mat(2, ℤ)) τ₀).re)
    (A : ℝ) :
    ∃ G : Finset (ℤ × ℕ), ∀ᶠ τ : ℂ in 𝓝[{τ : ℂ | 0 < τ.im}] τ₀,
      ∀ u ∈ faddeevModularUHPZeros γ n τ, A ≤ u.re →
        ∃ kj ∈ G, u = (kj.1 : ℂ) - ((n + (kj.2 : ℤ) : ℤ) : ℂ) * τ := by
  let e := (fltDenominator (γ : Mat(2, ℤ)) τ₀).re
  let C := -(γ 1 0 : ℝ) * A + 2 * |(n : ℝ)| * e + 1
  have he' : 0 < e / 2 := by dsimp [e]; linarith
  let hfin := finite_faddeevModularUHPZeroIndices_lt γ hc n he' C
  refine ⟨hfin.toFinset, ?_⟩
  filter_upwards [
    (eventually_re_fltDenominator_between γ τ₀ he).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with τ hτ hUHP
  intro u hu hAu
  obtain ⟨k, j, N, hN, rfl, hNeq, _⟩ :=
    faddeevModularUHPZero_coordinates γ n hUHP hu
  have hre := re_faddeevModularUHPZero_coordinate γ n k N j τ hNeq
  have hAu' : A ≤ (k : ℝ) - ((n : ℝ) + j) * τ.re := by
    simpa [Complex.sub_re, Complex.mul_re] using hAu
  have hc' : (0 : ℝ) < (γ 1 0 : ℝ) := by exact_mod_cast hc
  have hAprod := mul_le_mul_of_nonneg_left hAu' hc'.le
  have hNr : (0 : ℝ) ≤ N := by exact_mod_cast hN.le
  have hjr : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hlow : (j : ℝ) * (e / 2) ≤
      (j : ℝ) * (fltDenominator (γ : Mat(2, ℤ)) τ).re :=
    mul_le_mul_of_nonneg_left hτ.1.le hjr
  have hn : -(n : ℝ) * (fltDenominator (γ : Mat(2, ℤ)) τ).re ≤
      2 * |(n : ℝ)| * e := by
    simpa only [abs_neg] using mul_le_two_abs_mul (-(n : ℝ)) e
      (fltDenominator (γ : Mat(2, ℤ)) τ).re hτ.1 hτ.2
  have hsum : (N : ℝ) + (j : ℝ) * (e / 2) < C := by
    dsimp [C]; nlinarith
  refine ⟨(k, j), ?_, rfl⟩
  exact hfin.mem_toFinset.mpr ⟨by simpa [hNeq] using hN, by simpa [hNeq] using hsum⟩

/-! ### The crossed poles near a period

If no right pole at `τ₀` lies on a vertical line, the finitely many near it keep their sides,
and the rest stay far to its right. -/

/-- A pole moves continuously where `j_γ(τ₀) ≠ 0`; used by
`eventually_faddeevModularUHPPole_re_lt_iff` and `eventually_pole_inside_square`. -/
private lemma continuousAt_faddeevModularUHPPole (γ : SL(2, ℤ)) (τ₀ : ℂ)
    (hε : fltDenominator (γ : Mat(2, ℤ)) τ₀ ≠ 0) (k : ℤ) (j : ℕ) :
    ContinuousAt (fun τ : ℂ => faddeevModularUHPPole γ τ k j) τ₀ := by
  unfold faddeevModularUHPPole fltDenominator flt
  fun_prop (disch := assumption)

/-- A fixed pole stays on the same side of a line it avoids; used by
`eventually_fiveTermPoles_re_lt_iff`. -/
private lemma eventually_faddeevModularUHPPole_re_lt_iff (γ : SL(2, ℤ)) (τ₀ : ℂ)
    (hε : fltDenominator (γ : Mat(2, ℤ)) τ₀ ≠ 0) (k : ℤ) (j : ℕ) (x : ℝ)
    (hx : (faddeevModularUHPPole γ τ₀ k j).re ≠ x) :
    ∀ᶠ τ : ℂ in 𝓝 τ₀,
      (faddeevModularUHPPole γ τ k j).re ≠ x ∧
        ((faddeevModularUHPPole γ τ k j).re < x ↔
          (faddeevModularUHPPole γ τ₀ k j).re < x) := by
  have hcont : ContinuousAt
      (fun τ : ℂ => (faddeevModularUHPPole γ τ k j).re) τ₀ :=
    Complex.continuous_re.continuousAt.comp
      (continuousAt_faddeevModularUHPPole γ τ₀ hε k j)
  by_cases hlt : (faddeevModularUHPPole γ τ₀ k j).re < x
  · filter_upwards [hcont.eventually (isOpen_Iio.mem_nhds hlt)] with τ hτ
    exact ⟨ne_of_lt hτ, by simp [hτ, hlt]⟩
  · have hgt : x < (faddeevModularUHPPole γ τ₀ k j).re :=
      lt_of_le_of_ne (le_of_not_gt hlt) hx.symm
    filter_upwards [hcont.eventually (isOpen_Ioi.mem_nhds hgt)] with τ hτ
    exact ⟨ne_of_gt hτ, by simp [not_lt.mpr hτ.le, hlt]⟩

/-- The finitely many candidate right poles keep their sides of the line; used by
`eventually_fiveTermPoles_re_lt_iff`. -/
private lemma eventually_finset_faddeevModularUHPPole_re_lt_iff (γ : SL(2, ℤ))
    (m : ℤ) (τ₀ : ℂ) (hε : fltDenominator (γ : Mat(2, ℤ)) τ₀ ≠ 0)
    (x : ℝ) (G : Finset (ℤ × ℕ))
    (hx : ∀ kj : ℤ × ℕ, 0 ≤ faddeevModularUHPIndex γ m kj.1 kj.2 →
      (faddeevModularUHPPole γ τ₀ kj.1 kj.2).re ≠ x) :
    ∀ᶠ τ : ℂ in 𝓝 τ₀, ∀ kj ∈ G,
      0 ≤ faddeevModularUHPIndex γ m kj.1 kj.2 →
        (faddeevModularUHPPole γ τ kj.1 kj.2).re ≠ x ∧
          ((faddeevModularUHPPole γ τ kj.1 kj.2).re < x ↔
            (faddeevModularUHPPole γ τ₀ kj.1 kj.2).re < x) := by
  apply (Finset.eventually_all G).mpr
  intro kj _
  by_cases hN : 0 ≤ faddeevModularUHPIndex γ m kj.1 kj.2
  · filter_upwards [eventually_faddeevModularUHPPole_re_lt_iff
      γ τ₀ hε kj.1 kj.2 x (hx kj hN)] with τ hτ _
    exact hτ
  · exact Filter.Eventually.of_forall (fun _ h => (hN h).elim)

/-- If no right pole of the `m`-th kernel at `τ₀` lies on the line `Re z = x`, where
`Re j_γ(τ₀) > 0`, then for periods near `τ₀` none does, and the same right poles lie to its
left. -/
theorem eventually_fiveTermPoles_re_lt_iff (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (m : ℤ)
    (τ₀ : ℂ) (he : 0 < (fltDenominator (γ : Mat(2, ℤ)) τ₀).re) (x : ℝ)
    (hx : ∀ kj : ℤ × ℕ, 0 ≤ faddeevModularUHPIndex γ m kj.1 kj.2 →
      (faddeevModularUHPPole γ τ₀ kj.1 kj.2).re ≠ x) :
    ∀ᶠ τ : ℂ in 𝓝 τ₀, ∀ kj : ℤ × ℕ, 0 ≤ faddeevModularUHPIndex γ m kj.1 kj.2 →
      (faddeevModularUHPPole γ τ kj.1 kj.2).re ≠ x ∧
        ((faddeevModularUHPPole γ τ kj.1 kj.2).re < x ↔
          (faddeevModularUHPPole γ τ₀ kj.1 kj.2).re < x) := by
  obtain ⟨G, hG⟩ :=
    exists_finset_fiveTermPoles_re_lt_nhds γ hc m τ₀ he (x + 1)
  have hG₀ := Filter.Eventually.self_of_nhds hG
  have hfinite := eventually_finset_faddeevModularUHPPole_re_lt_iff γ m τ₀
    (Complex.ne_zero_of_re_pos he) x G hx
  filter_upwards [hG, hfinite] with τ hτ hF
  intro kj hN
  by_cases hmem : kj ∈ G
  · exact hF kj hmem hN
  · have hτge : x + 1 ≤ (faddeevModularUHPPole γ τ kj.1 kj.2).re := by
      by_contra h
      exact hmem (hτ kj hN (lt_of_not_ge h))
    have h₀ge : x + 1 ≤ (faddeevModularUHPPole γ τ₀ kj.1 kj.2).re := by
      by_contra h
      exact hmem (hG₀ kj hN (lt_of_not_ge h))
    constructor
    · linarith
    · constructor <;> intro h <;> linarith

/-! ### Squares around crossed poles at a real period

For small `r` and nearby periods, the square of half-side `r` centred at the position at `τ₀` of
one right pole contains that pole and no other singularity of the kernel. -/

/-- At an irrational real period, another pole has a different real coordinate; used by
`eventually_right_poles_isolated_in_square`. -/
private lemma re_faddeevModularUHPPole_ne_of_ne (γ : SL(2, ℤ)) (τ₀ : ℝ)
    (hτ₀ : Irrational τ₀) (hε : fltDenominator (γ : Mat(2, ℤ)) (τ₀ : ℂ) ≠ 0)
    (kj base : ℤ × ℕ) (hne : kj ≠ base) :
    (faddeevModularUHPPole γ (τ₀ : ℂ) kj.1 kj.2).re ≠
      (faddeevModularUHPPole γ (τ₀ : ℂ) base.1 base.2).re := by
  intro hre
  apply hne
  apply faddeevModularUHPPole_ofReal_injective γ τ₀ hτ₀ hε
  apply Complex.ext hre
  simp [im_faddeevModularUHPPole_ofReal]

/-- A real lattice point shifted by `-y` cannot meet another real lattice point when `y`
avoids the lattice; used by `re_shifted_zero_ne_pole`. -/
private lemma re_shifted_lattice_ne (τ₀ y : ℝ)
    (hy : ¬ IsPeriodLatticePoint τ₀ (y : ℂ)) (P : ℂ)
    (hP : IsPeriodLatticePoint τ₀ P) (hPim : P.im = 0) (a b : ℤ) :
    ((a : ℂ) + (b : ℂ) * (τ₀ : ℂ) - y).re ≠ P.re := by
  intro hre
  have heq : (a : ℂ) + (b : ℂ) * (τ₀ : ℂ) - y = P := by
    apply Complex.ext hre
    simp [hPim]
  obtain ⟨m, n, hm⟩ := hP
  apply hy
  refine ⟨a - m, b - n, ?_⟩
  rw [Int.cast_sub, Int.cast_sub]
  linear_combination -heq - hm

/-- A shifted zero coordinate has a different real position from the chosen pole; used by
`eventually_shifted_zeros_avoid_square`. -/
private lemma re_shifted_zero_ne_pole (γ : SL(2, ℤ)) (τ₀ y : ℝ)
    (he : 0 < (fltDenominator (γ : Mat(2, ℤ)) (τ₀ : ℂ)).re)
    (hy : ¬ IsPeriodLatticePoint τ₀ (y : ℂ))
    (k : ℤ) (j : ℕ) (n : ℤ) (kj : ℤ × ℕ) :
    ((kj.1 : ℂ) - ((n + (kj.2 : ℤ) : ℤ) : ℂ) * (τ₀ : ℂ) - y).re ≠
      (faddeevModularUHPPole γ (τ₀ : ℂ) k j).re := by
  have hε := Complex.ne_zero_of_re_pos he
  have hx := re_shifted_lattice_ne τ₀ y hy
    (faddeevModularUHPPole γ (τ₀ : ℂ) k j)
    (isPeriodLatticePoint_faddeevModularUHPPole γ (τ₀ : ℂ) hε k j)
    (im_faddeevModularUHPPole_ofReal γ τ₀ k j)
    kj.1 (-(n + (kj.2 : ℤ)))
  convert hx using 1
  push_cast
  ring_nf

/-- A finite family of continuous real coordinates stays outside a smaller gap; used by
`eventually_right_poles_isolated_in_square` and `eventually_shifted_zeros_avoid_square`. -/
private lemma eventually_finset_real_away {α : Type*} (F : Finset α)
    (f : α → ℂ → ℝ) (τ₀ : ℂ) (x : ℝ)
    (hcont : ∀ a ∈ F, ContinuousAt (f a) τ₀)
    (hx : ∀ a ∈ F, f a τ₀ ≠ x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r < δ →
      ∀ᶠ τ : ℂ in 𝓝 τ₀, ∀ a ∈ F, r < |f a τ - x| := by
  obtain ⟨δ, hδ, hgap⟩ := exists_pos_le_abs_sub_of_finset F (fun a => f a τ₀) x hx
  refine ⟨δ, hδ, ?_⟩
  intro r _ hr
  apply (Finset.eventually_all F).mpr
  intro a ha
  have hopen : IsOpen {v : ℝ | r < |v - x|} :=
    isOpen_Ioi.preimage (by fun_prop : Continuous (fun v : ℝ => |v - x|))
  exact (hcont a ha).eventually
    (hopen.mem_nhds (lt_of_lt_of_le hr (hgap a ha)))

/-- A continuous real coordinate stays within any positive distance of its value; used by
`eventually_pole_inside_square`. -/
private lemma eventually_real_close (f : ℂ → ℝ) (τ₀ : ℂ)
    (hcont : ContinuousAt f τ₀) (r : ℝ) (hr : 0 < r) :
    ∀ᶠ τ : ℂ in 𝓝 τ₀, |f τ - f τ₀| < r := by
  have hopen : IsOpen {v : ℝ | |v - f τ₀| < r} :=
    isOpen_Iio.preimage (by fun_prop : Continuous (fun v : ℝ => |v - f τ₀|))
  exact hcont.eventually (hopen.mem_nhds (by simpa using hr))

/-- Eventually a positive radius lies below a fixed positive gap and below one; used by
`eventually_right_poles_isolated_in_square` and `eventually_shifted_zeros_avoid_square`. -/
private lemma eventually_radius_lt_gap_one (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r ∧ r < δ ∧ r < 1 := by
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (isOpen_Iio.mem_nhds
      (show (0 : ℝ) < min δ 1 by simp [hδ]))] with r hr hr'
  exact ⟨hr, hr'.trans_le (min_le_left _ _), hr'.trans_le (min_le_right _ _)⟩

/-- The chosen pole enters the open square for small radii and nearby periods; used by
`eventually_right_poles_isolated_in_square`. -/
private lemma eventually_pole_inside_square (γ : SL(2, ℤ)) (τ₀ : ℝ)
    (hε : fltDenominator (γ : Mat(2, ℤ)) (τ₀ : ℂ) ≠ 0)
    (k : ℤ) (j : ℕ) (r : ℝ) (hr : 0 < r) :
    ∀ᶠ τ : ℂ in 𝓝 (τ₀ : ℂ),
      (faddeevModularUHPPole γ τ k j).re ∈
        Ioo ((faddeevModularUHPPole γ (τ₀ : ℂ) k j).re - r)
          ((faddeevModularUHPPole γ (τ₀ : ℂ) k j).re + r) ∧
      (faddeevModularUHPPole γ τ k j).im ∈ Ioo (-r) r := by
  have hre := eventually_real_close
    (fun τ : ℂ => (faddeevModularUHPPole γ τ k j).re) (τ₀ : ℂ)
    (Complex.continuous_re.continuousAt.comp
      (continuousAt_faddeevModularUHPPole γ _ hε k j)) r hr
  have hcontIm := Complex.continuous_im.continuousAt.comp
    (continuousAt_faddeevModularUHPPole γ _ hε k j)
  have him := eventually_real_close
    (fun τ : ℂ => (faddeevModularUHPPole γ τ k j).im) (τ₀ : ℂ)
    hcontIm r hr
  filter_upwards [hre, him] with τ hrt hit
  rw [im_faddeevModularUHPPole_ofReal] at hit
  constructor
  · rcases abs_lt.mp hrt with ⟨hl, hu⟩
    exact ⟨by linarith, by linarith⟩
  · simpa using (abs_lt.mp hit)

/-- Every right pole in the closed square is the chosen indexed pole; used by
`eventually_rectBoundaryIntegral_fiveTermKernelUHP`. -/
private lemma eventually_right_poles_isolated_in_square
    (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (m : ℤ) (τ₀ : ℝ)
    (hτ₀ : Irrational τ₀)
    (he : 0 < (fltDenominator (γ : Mat(2, ℤ)) (τ₀ : ℂ)).re)
    (k : ℤ) (j : ℕ) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ᶠ τ : ℂ in 𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ),
      (faddeevModularUHPPole γ τ k j).re ∈
        Ioo ((faddeevModularUHPPole γ (τ₀ : ℂ) k j).re - r)
          ((faddeevModularUHPPole γ (τ₀ : ℂ) k j).re + r) ∧
      (faddeevModularUHPPole γ τ k j).im ∈ Ioo (-r) r ∧
      (∀ kj : ℤ × ℕ, 0 ≤ faddeevModularUHPIndex γ m kj.1 kj.2 →
        faddeevModularUHPPole γ τ kj.1 kj.2 ∈
          Icc ((faddeevModularUHPPole γ (τ₀ : ℂ) k j).re - r)
            ((faddeevModularUHPPole γ (τ₀ : ℂ) k j).re + r) ×ℂ Icc (-r) r →
        kj = (k, j)) := by
  let P := faddeevModularUHPPole γ (τ₀ : ℂ) k j
  obtain ⟨G, hG⟩ := exists_finset_fiveTermPoles_re_lt_nhds
    γ hc m (τ₀ : ℂ) he (P.re + 1)
  have hε := Complex.ne_zero_of_re_pos he
  obtain ⟨δ, hδ, hfar⟩ := eventually_finset_real_away (G.erase (k, j))
    (fun kj τ => (faddeevModularUHPPole γ τ kj.1 kj.2).re)
    (τ₀ : ℂ) P.re
    (by
      intro kj _
      exact Complex.continuous_re.continuousAt.comp
        (continuousAt_faddeevModularUHPPole γ _ hε _ _))
    (by
      intro kj hkj
      exact re_faddeevModularUHPPole_ne_of_ne γ τ₀ hτ₀ hε kj (k, j)
        (Finset.ne_of_mem_erase hkj))
  filter_upwards [eventually_radius_lt_gap_one δ hδ] with r ⟨hr, hrδ, hr1⟩
  filter_upwards [
    (eventually_pole_inside_square γ τ₀ hε k j r hr).filter_mono nhdsWithin_le_nhds,
    (hfar r hr hrδ).filter_mono nhdsWithin_le_nhds,
    hG.filter_mono nhdsWithin_le_nhds] with τ hinside hfarτ hGτ
  refine ⟨hinside.1, hinside.2, ?_⟩
  intro kj hN hclosed
  have hmem : kj ∈ G := hGτ kj hN
    (lt_of_le_of_lt hclosed.1.2 (by dsimp [P]; linarith))
  by_contra hne
  have haway := hfarτ kj (Finset.mem_erase.mpr ⟨hne, hmem⟩)
  have hle : |(faddeevModularUHPPole γ τ kj.1 kj.2).re - P.re| ≤ r :=
    abs_le.mpr ⟨by linarith [hclosed.1.1], by linarith [hclosed.1.2]⟩
  exact (not_lt_of_ge hle) haway

/-- No shifted left pole enters the closed square; used by
`eventually_rectBoundaryIntegral_fiveTermKernelUHP`. -/
private lemma eventually_shifted_zeros_avoid_square
    (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (n : ℤ) (y τ₀ : ℝ)
    (he : 0 < (fltDenominator (γ : Mat(2, ℤ)) (τ₀ : ℂ)).re)
    (hy : ¬ IsPeriodLatticePoint τ₀ (y : ℂ)) (k : ℤ) (j : ℕ) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ᶠ τ : ℂ in 𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ),
      ∀ u ∈ faddeevModularUHPZeros γ n τ,
        u - y ∉
          Icc ((faddeevModularUHPPole γ (τ₀ : ℂ) k j).re - r)
            ((faddeevModularUHPPole γ (τ₀ : ℂ) k j).re + r) ×ℂ Icc (-r) r := by
  let P := faddeevModularUHPPole γ (τ₀ : ℂ) k j
  obtain ⟨H, hH⟩ := exists_finset_faddeevModularUHPZeros_le_re_nhds
    γ hc n (τ₀ : ℂ) he (P.re + y - 1)
  obtain ⟨δ, hδ, hfar⟩ := eventually_finset_real_away H
    (fun kj τ => ((kj.1 : ℂ) - ((n + (kj.2 : ℤ) : ℤ) : ℂ) * τ - y).re)
    (τ₀ : ℂ) P.re
    (by intro kj _; fun_prop)
    (by intro kj _; exact re_shifted_zero_ne_pole γ τ₀ y he hy k j n kj)
  filter_upwards [eventually_radius_lt_gap_one δ hδ] with r ⟨hr, hrδ, hr1⟩
  filter_upwards [(hfar r hr hrδ).filter_mono nhdsWithin_le_nhds,
    hH] with τ hfarτ hHτ
  intro u hu hclosed
  have hA : P.re + y - 1 ≤ u.re := by
    have hre := hclosed.1.1
    simp only [Complex.sub_re, Complex.ofReal_re] at hre
    linarith
  obtain ⟨kj, hkj, huEq⟩ := hHτ u hu hA
  have haway := hfarτ kj hkj
  rw [huEq] at hclosed
  have hle : |((kj.1 : ℂ) - ((n + (kj.2 : ℤ) : ℤ) : ℂ) * τ - y).re - P.re| ≤
      r := abs_le.mpr ⟨by linarith [hclosed.1.1], by linarith [hclosed.1.2]⟩
  exact (not_lt_of_ge hle) haway

/-- Converts the four side integrals of the local rectangle theorem to
`rectBoundaryIntegral`; used by
`eventually_rectBoundaryIntegral_fiveTermKernelUHP`. -/
private lemma rectBoundaryIntegral_square_eq_four (f : ℂ → ℂ) (P : ℂ)
    (hPim : P.im = 0) (r : ℝ) :
    rectBoundaryIntegral f (P - (r + r * I)) (P + (r + r * I)) =
      (∫ s : ℝ in (P.re - r)..(P.re + r), f (s + (-r) * I)) -
        (∫ s : ℝ in (P.re - r)..(P.re + r), f (s + r * I)) +
        I * (∫ t : ℝ in (-r)..r, f ((P.re + r) + t * I)) -
        I * (∫ t : ℝ in (-r)..r, f ((P.re - r) + t * I)) := by
  unfold rectBoundaryIntegral
  simp [smul_eq_mul, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, hPim]

/-- The local rectangle contains precisely the chosen pole index; used by
`eventually_rectBoundaryIntegral_fiveTermKernelUHP`. -/
private lemma fiveTerm_square_index_set_eq_singleton (γ : SL(2, ℤ))
    (m : ℤ) (τ P : ℂ) (r : ℝ) (k : ℤ) (j : ℕ)
    (hN : 0 ≤ faddeevModularUHPIndex γ m k j)
    (hinside : P.re - r < (faddeevModularUHPPole γ τ k j).re ∧
      (faddeevModularUHPPole γ τ k j).re < P.re + r ∧
      -r < (faddeevModularUHPPole γ τ k j).im ∧
      (faddeevModularUHPPole γ τ k j).im < r)
    (hunique : ∀ kj : ℤ × ℕ,
      0 ≤ faddeevModularUHPIndex γ m kj.1 kj.2 →
      faddeevModularUHPPole γ τ kj.1 kj.2 ∈
        Icc (P.re - r) (P.re + r) ×ℂ Icc (-r) r → kj = (k, j))
    (S : Finset (ℤ × ℕ))
    (hS : ∀ kj : ℤ × ℕ, kj ∈ S ↔
      0 ≤ faddeevModularUHPIndex γ m kj.1 kj.2 ∧
        P.re - r < (faddeevModularUHPPole γ τ kj.1 kj.2).re ∧
        (faddeevModularUHPPole γ τ kj.1 kj.2).re < P.re + r ∧
        -r < (faddeevModularUHPPole γ τ kj.1 kj.2).im ∧
        (faddeevModularUHPPole γ τ kj.1 kj.2).im < r) :
    S = {(k, j)} := by
  ext kj
  rw [hS kj]
  simp only [Finset.mem_singleton]
  constructor
  · rintro ⟨hN', hlo, hhi, hilo, hihi⟩
    exact hunique kj hN' ⟨⟨hlo.le, hhi.le⟩, ⟨hilo.le, hihi.le⟩⟩
  · intro hkj
    subst kj
    exact ⟨hN, hinside⟩

/-- Every genuine right pole in the closed square lies in its interior; used by
`eventually_rectBoundaryIntegral_fiveTermKernelUHP`. -/
private lemma right_poles_in_square_are_interior (γ : SL(2, ℤ)) (m : ℤ)
    (τ P : ℂ) (hτ : 0 < τ.im) (r : ℝ) (k : ℤ) (j : ℕ)
    (hinside : P.re - r < (faddeevModularUHPPole γ τ k j).re ∧
      (faddeevModularUHPPole γ τ k j).re < P.re + r ∧
      -r < (faddeevModularUHPPole γ τ k j).im ∧
      (faddeevModularUHPPole γ τ k j).im < r)
    (hunique : ∀ kj : ℤ × ℕ,
      0 ≤ faddeevModularUHPIndex γ m kj.1 kj.2 →
      faddeevModularUHPPole γ τ kj.1 kj.2 ∈
        Icc (P.re - r) (P.re + r) ×ℂ Icc (-r) r → kj = (k, j)) :
    ∀ u ∈ faddeevModularUHPPoles γ (m + 1) τ,
      u ∈ Icc (P.re - r) (P.re + r) ×ℂ Icc (-r) r →
      P.re - r < u.re ∧ u.re < P.re + r ∧ -r < u.im ∧ u.im < r := by
  intro u hu hclosed
  obtain ⟨k', j', rfl, hN'⟩ := (mem_faddeevModularUHPPoles_iff γ m hτ).mp hu
  have heq := hunique (k', j') hN' hclosed
  have hk : k' = k := congrArg Prod.fst heq
  have hj : j' = j := congrArg Prod.snd heq
  subst k'
  subst j'
  exact hinside

/-- Near an irrational real period `τ₀` with `j_γ(τ₀) > 0`, and for `y` outside `ℤ+ℤτ₀`, the
counterclockwise boundary integral of the `m`-th kernel over the square of half-side `r` centred
at the position `ε(k-jσ)` at `τ₀` of a right pole with `N = kc-ja+m ≥ 0` is `2πi` times its
residue, for all small `r` and all periods in the upper half plane near `τ₀`: the square then
contains that pole and no other right pole or shifted left pole, and none on its boundary, so
`integral_boundary_rect_fiveTermKernelUHP_of_local` applies. This writes a residue of the
contour deformation in [RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`] as a
boundary integral that has a limit at `τ₀`. -/
theorem eventually_rectBoundaryIntegral_fiveTermKernelUHP
    (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (ℓ p m : ℤ) (w : ℂ) (y τ₀ : ℝ)
    (hτ₀ : Irrational τ₀) (he : 0 < (fltDenominator (γ : Mat(2, ℤ)) (τ₀ : ℂ)).re)
    (hy : ¬ IsPeriodLatticePoint τ₀ (y : ℂ)) (k : ℤ) (j : ℕ)
    (hN : 0 ≤ faddeevModularUHPIndex γ m k j) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ᶠ τ : ℂ in 𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ),
      rectBoundaryIntegral (fiveTermKernelUHP γ ℓ p w y τ m)
          (faddeevModularUHPPole γ (τ₀ : ℂ) k j - (r + r * I))
          (faddeevModularUHPPole γ (τ₀ : ℂ) k j + (r + r * I)) =
        2 * π * I * fiveTermResidueUHP γ ℓ p w y τ
          (faddeevModularUHPIndex γ m k j) j := by
  let P := faddeevModularUHPPole γ (τ₀ : ℂ) k j
  have hright := eventually_right_poles_isolated_in_square γ hc m τ₀ hτ₀ he k j
  have hleft := eventually_shifted_zeros_avoid_square γ hc (m + p) y τ₀ he hy k j
  filter_upwards [hright, hleft, self_mem_nhdsWithin] with r hRr hLr hr
  change 0 < r at hr
  filter_upwards [hRr, hLr, self_mem_nhdsWithin] with τ hR hL hτ
  have hP := right_poles_in_square_are_interior γ m τ P hτ r k j
    ⟨hR.1.1, hR.1.2, hR.2.1.1, hR.2.1.2⟩ hR.2.2
  have hL : ∀ z ∈ Icc (P.re - r) (P.re + r) ×ℂ Icc (-r) r,
      z + (y : ℂ) ∉ faddeevModularUHPZeros γ (m + p) τ := by
    intro z hz hzero
    exact hL (z + y) hzero (by simpa using hz)
  have hden : qPochhammer ((p : ℂ) * τ + y) τ ≠ 0 :=
    qPochhammer_intCast_mul_add_ofReal_ne_zero τ hτ p y
      ((sigmaSLatticeFree_iff_not_isPeriodLatticePoint τ₀ y).mpr hy).ne_intCast
  obtain ⟨S, hS, hInt⟩ := integral_boundary_rect_fiveTermKernelUHP_of_local
    γ ℓ p m w (y : ℂ) τ hτ (P.re - r) (P.re + r) (-r) r
    (by linarith) (by linarith) hP hL hden
  have hSingleton := fiveTerm_square_index_set_eq_singleton γ m τ P r k j
    hN ⟨hR.1.1, hR.1.2, hR.2.1.1, hR.2.1.2⟩ hR.2.2 S hS
  rw [rectBoundaryIntegral_square_eq_four _ P
    (im_faddeevModularUHPPole_ofReal γ τ₀ k j) r]
  simpa [hSingleton] using hInt

end SIC
