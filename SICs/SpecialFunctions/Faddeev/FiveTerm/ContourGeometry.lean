/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.Faddeev.FiveTerm.Kernel

/-!
# Separating contours for the five-term kernel

Vertical separating lines and pole-free closing sides for the five-term contour.

This module positions the contours in [RW26, Radchenko, Wheeler (2026), Appendix A.2,
`app:mod.fad`], the proof of Theorem 3, `thm:5term.mod.fad`.

## The argument

The real bounds on the modular q-product's poles and zeros give positive gaps between
the initial vertical line and both genuine pole families of the kernel. Horizontal
lines halfway between period-lattice rows have a fixed positive gap from the right
poles. In any fixed height strip, integer translates of a lattice-free vertical line
supply separated right sides escaping to infinity; their gap may depend on the strip.
A crossing to the right of the shifted left poles stays there for all nearby periods.

A right pole with forward index `N` and backward index `j` has real part `((N-m) Re ε + j)/c`.
When `Re ε > 0`, only finitely many lie to the left of a given vertical line. A line to the
right of the shifted left poles that meets no right pole is therefore still uniformly
separated from both families; it is the straight contour of the source's deformation clause,
before the deformation around the finitely many right poles on its left.
-/

noncomputable section

open Complex Real Filter Set MeasureTheory
open scoped Topology MatrixGroups

namespace SIC

/-! ### Horizontal and right-side separation

Half-integer heights separate horizontal sides from all pole rows. Integer translates
of a lattice-free vertical line provide right sides in any fixed height strip. -/

/-- At height `(r+1/2) Im τ`, every horizontal point stays at least `Im τ/2`
from the right poles, as in [RW26, Radchenko, Wheeler (2026), Appendix A.2,
`app:mod.fad`]. -/
theorem dist_faddeevModularUHPPoles_le_of_half_height (γ : SL(2, ℤ)) (m : ℤ)
    (τ : ℂ) (hτ : 0 < τ.im) (r : ℤ) (s : ℝ)
    {u : ℂ} (hu : u ∈ faddeevModularUHPPoles γ (m + 1) τ) :
    τ.im / 2 ≤ ‖((s : ℂ) + (((r : ℝ) + 1 / 2) * τ.im) * I) - u‖ :=
  half_height_le_norm_sub_periodLatticePoint τ hτ r u
    (isPeriodLatticePoint_of_qPochhammer_div_eq_zero γ τ hτ hu.1) s

/-- In each fixed height strip there are right sides tending to infinity which stay a
positive distance from all right poles and meet no pole real coordinate; see
[RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`]. -/
theorem exists_pos_dist_fiveTerm_right_sides (γ : SL(2, ℤ)) (m : ℤ)
    (τ : ℂ) (hτ : 0 < τ.im) (a b : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ X : ℕ → ℝ, Tendsto X atTop atTop ∧
      (∀ n, ∀ t ∈ Set.uIcc a b, ∀ u ∈ faddeevModularUHPPoles γ (m + 1) τ,
        δ ≤ ‖((X n : ℂ) + t * I) - u‖) ∧
      (∀ n, ∀ u ∈ faddeevModularUHPPoles γ (m + 1) τ, u.re ≠ X n) := by
  obtain ⟨δ, hδ, X, hX, hdist, havoid⟩ :=
    exists_periodLattice_right_sides τ hτ.ne' a b
  refine ⟨δ, hδ, X, hX, ?_, ?_⟩
  · intro n t ht u hu
    exact hdist n t ht u
      (isPeriodLatticePoint_of_qPochhammer_div_eq_zero γ τ hτ hu.1)
  · intro n u hu
    exact havoid n u
      (isPeriodLatticePoint_of_qPochhammer_div_eq_zero γ τ hτ hu.1)

/-! ### Vertical contour separation

The bound on the shifted left poles persists for nearby periods, and a vertical line to its right
has a uniform real-part gap from them. -/

/-- A crossing to the right of the bound `(-(m+p) Re ε - 1)/c - Re y` on the shifted left poles
stays to its right for periods near `τ₀`, since `Re ε` depends continuously on the period.
Project-local glue for [RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`]. -/
theorem eventually_fiveTerm_leftBound_lt (γ : SL(2, ℤ)) (m p : ℤ) (y τ₀ : ℂ) (x : ℝ)
    (hx : (-((m + p : ℤ) : ℝ) * (fltDenominator (γ : Mat(2, ℤ)) τ₀).re - 1) /
      (γ 1 0 : ℝ) - y.re < x) :
    ∀ᶠ τ : ℂ in 𝓝 τ₀, (-((m + p : ℤ) : ℝ) * (fltDenominator (γ : Mat(2, ℤ)) τ).re - 1) /
      (γ 1 0 : ℝ) - y.re < x := by
  have hLeft : ContinuousAt (fun τ : ℂ =>
      (-((m + p : ℤ) : ℝ) * (fltDenominator (γ : Mat(2, ℤ)) τ).re - 1) /
        (γ 1 0 : ℝ) - y.re) τ₀ := by
    unfold fltDenominator
    fun_prop
  exact hLeft.tendsto.eventually_lt_const hx

/-- A lower bound on the difference of real parts gives a norm bound; used by
`exists_pos_dist_left_vertical` and `exists_pos_dist_right_vertical`. -/
private lemma norm_sub_ge_re_gap (a b : ℂ) {δ : ℝ}
    (h : δ ≤ a.re - b.re) : δ ≤ ‖a - b‖ := by
  calc
    δ ≤ a.re - b.re := h
    _ ≤ |(a - b).re| := by rw [Complex.sub_re]; exact le_abs_self _
    _ ≤ ‖a - b‖ := Complex.abs_re_le_norm _

/-- The shifted left poles have a uniform real-part gap from a line to their right; used by
`exists_pos_dist_fiveTerm_of_regular`. -/
private lemma exists_pos_dist_left_vertical
    (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (m p : ℤ) (y τ : ℂ)
    (hτ : 0 < τ.im) (he : 0 ≤ (fltDenominator (γ : Mat(2, ℤ)) τ).re)
    (x : ℝ)
    (hxL : (-((m + p : ℤ) : ℝ) * (fltDenominator (γ : Mat(2, ℤ)) τ).re - 1) /
      (γ 1 0 : ℝ) - y.re < x) :
    ∃ L : ℝ, 0 < L ∧ ∀ t : ℝ, ∀ u ∈ faddeevModularUHPZeros γ (m + p) τ,
      L ≤ ‖((x : ℂ) + t * I) + y - u‖ := by
  let L := x + y.re -
    (-(m + p : ℝ) * (fltDenominator (γ : Mat(2, ℤ)) τ).re - 1) / (γ 1 0 : ℝ)
  have hL : 0 < L := by dsimp [L]; push_cast at hxL ⊢; linarith
  refine ⟨L, hL, ?_⟩
  intro t u hu
  have hb := re_upperBound_of_mem_faddeevModularUHPZeros γ hc (m + p) hτ he hu
  have hle : L ≤ x + y.re - u.re := by
    dsimp [L]
    push_cast at hb
    linarith
  exact norm_sub_ge_re_gap (((x : ℂ) + t * I) + y) u (by simpa using hle)

/-! ### Right poles to the left of a contour

A genuine right pole with forward index `N` and backward index `j` has real part
`((N-m) Re ε + j)/c`. When `Re ε > 0`, a vertical line therefore has only finitely many right
poles on its left. A line meeting none of them, and lying to the right of the shifted left
poles, keeps a positive distance from both families. -/

/-- For `e > 0`, only finitely many right-pole indices `(k,j)` have forward index
`N = kc-ja+m ≥ 0` with `N e + j < C`: both `N` and `j` are bounded, and `(k,j) ↦ (N,j)` is
injective. Used by `finite_fiveTermPoles_re_lt` and, with `e` a lower bound for `Re ε`
near a period, by `exists_finset_fiveTermPoles_re_lt_nhds`.
Project-local glue for [RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`]. -/
theorem finite_fiveTermPoleIndices_lt (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (m : ℤ)
    {e : ℝ} (he : 0 < e) (C : ℝ) :
    {kj : ℤ × ℕ | 0 ≤ faddeevModularUHPIndex γ m kj.1 kj.2 ∧
      (faddeevModularUHPIndex γ m kj.1 kj.2 : ℝ) * e + kj.2 < C}.Finite := by
  let f : ℤ × ℕ → ℤ × ℕ := fun kj => (faddeevModularUHPIndex γ m kj.1 kj.2, kj.2)
  refine Set.Finite.of_finite_image (f := f) ?_ ?_
  · refine ((Set.finite_Icc (0 : ℤ) ⌈C / e⌉).prod
      (Set.finite_Icc (0 : ℕ) ⌈C⌉₊)).subset ?_
    rintro _ ⟨⟨k, j⟩, ⟨hN, hsum⟩, rfl⟩
    have hN' : (0 : ℝ) ≤ faddeevModularUHPIndex γ m k j := by exact_mod_cast hN
    have hj' : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    have hNbound : (faddeevModularUHPIndex γ m k j : ℝ) ≤ C / e := by
      apply (le_div_iff₀ he).mpr
      nlinarith
    have hjbound : (j : ℝ) ≤ C := by
      nlinarith [mul_nonneg hN' he.le]
    exact ⟨⟨hN, by exact_mod_cast hNbound.trans (Int.le_ceil _)⟩,
      ⟨Nat.zero_le _, by exact_mod_cast hjbound.trans (Nat.le_ceil _)⟩⟩
  · rintro ⟨k, j⟩ _ ⟨k', j'⟩ _ heq
    have hj : j = j' := congrArg Prod.snd heq
    subst j'
    have hN : faddeevModularUHPIndex γ m k j =
        faddeevModularUHPIndex γ m k' j := congrArg Prod.fst heq
    have hkc : k * γ 1 0 = k' * γ 1 0 := by
      dsimp [faddeevModularUHPIndex] at hN
      omega
    exact Prod.ext (mul_right_cancel₀ hc.ne' hkc) rfl

/-- Only finitely many genuine right poles of the `m`-th kernel lie to the left of a vertical
line: by `re_faddeevModularUHPPole`, their real parts `((N-m) Re ε + j)/c` bound both the forward
index `N ≥ 0` and the backward index `j`. -/
theorem finite_fiveTermPoles_re_lt (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (m : ℤ)
    (τ : ℂ) (he : 0 < (fltDenominator (γ : Mat(2, ℤ)) τ).re) (x : ℝ) :
    {kj : ℤ × ℕ | 0 ≤ faddeevModularUHPIndex γ m kj.1 kj.2 ∧
      (faddeevModularUHPPole γ τ kj.1 kj.2).re < x}.Finite := by
  have hε : fltDenominator (γ : Mat(2, ℤ)) τ ≠ 0 := Complex.ne_zero_of_re_pos he
  have hc' : (0 : ℝ) < (γ 1 0 : ℝ) := by exact_mod_cast hc
  refine (finite_fiveTermPoleIndices_lt γ hc m he
    ((γ 1 0 : ℝ) * x + (m : ℝ) * (fltDenominator (γ : Mat(2, ℤ)) τ).re)).subset ?_
  rintro ⟨k, j⟩ ⟨hN, hreal⟩
  refine ⟨hN, ?_⟩
  rw [re_faddeevModularUHPPole γ hc τ hε m k j] at hreal
  have hbound := (div_lt_iff₀ hc').mp hreal
  push_cast at hbound ⊢
  nlinarith

/-- A finite index set of the genuine right poles of the `m`-th kernel to the left of a
vertical line; `finite_fiveTermPoles_re_lt` as a `Finset`. -/
theorem exists_finset_fiveTermPoles_re_lt (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (m : ℤ)
    (τ : ℂ) (he : 0 < (fltDenominator (γ : Mat(2, ℤ)) τ).re) (x : ℝ) :
    ∃ F : Finset (ℤ × ℕ), ∀ kj : ℤ × ℕ, kj ∈ F ↔
      0 ≤ faddeevModularUHPIndex γ m kj.1 kj.2 ∧
        (faddeevModularUHPPole γ τ kj.1 kj.2).re < x := by
  let hfin := finite_fiveTermPoles_re_lt γ hc m τ he x
  exact ⟨hfin.toFinset, fun kj => hfin.mem_toFinset⟩

/-- Finitely many real coordinates avoiding a fixed coordinate have a common positive gap;
used by `exists_pos_dist_right_vertical` and by
`SICs.SpecialFunctions.Faddeev.FiveTerm.CrossedPoles`. -/
theorem exists_pos_le_abs_sub_of_finset {α : Type*} (F : Finset α) (f : α → ℝ) (x : ℝ)
    (hx : ∀ a ∈ F, f a ≠ x) : ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ F, δ ≤ |f a - x| := by
  classical
  by_cases hF : F = ∅
  · subst F
    exact ⟨1, by positivity, by simp⟩
  · have hF' : F.Nonempty := Finset.nonempty_iff_ne_empty.mpr hF
    refine ⟨F.inf' hF' (fun a => |f a - x|), ?_, ?_⟩
    · apply (Finset.lt_inf'_iff hF').2
      intro a ha
      exact abs_pos.mpr (sub_ne_zero.mpr (hx a ha))
    · intro a ha
      exact Finset.inf'_le _ ha

/-- A regular vertical line has a uniform gap from all genuine right poles: only finitely
many poles have real part below `x+1`; used by
`exists_pos_dist_fiveTerm_of_regular`. -/
private lemma exists_pos_dist_right_vertical
    (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (m : ℤ) (τ : ℂ)
    (hτ : 0 < τ.im) (he : 0 < (fltDenominator (γ : Mat(2, ℤ)) τ).re)
    (x : ℝ) (hxP : ∀ u ∈ faddeevModularUHPPoles γ (m + 1) τ, u.re ≠ x) :
    ∃ R : ℝ, 0 < R ∧ ∀ t : ℝ, ∀ u ∈ faddeevModularUHPPoles γ (m + 1) τ,
      R ≤ ‖((x : ℂ) + t * I) - u‖ := by
  obtain ⟨F, hF⟩ := exists_finset_fiveTermPoles_re_lt γ hc m τ he (x + 1)
  have hregular : ∀ kj ∈ F,
      (faddeevModularUHPPole γ τ kj.1 kj.2).re ≠ x := by
    rintro ⟨k, j⟩ hkj
    apply hxP
    exact (mem_faddeevModularUHPPoles_iff γ m hτ).mpr
      ⟨k, j, rfl, ((hF (k, j)).mp hkj).1⟩
  obtain ⟨R, hR, hgap⟩ := exists_pos_le_abs_sub_of_finset F
    (fun kj => (faddeevModularUHPPole γ τ kj.1 kj.2).re) x hregular
  refine ⟨min R 1, lt_min hR zero_lt_one, ?_⟩
  intro t u hu
  by_cases hux : u.re < x + 1
  · obtain ⟨k, j, rfl, hN⟩ := (mem_faddeevModularUHPPoles_iff γ m hτ).mp hu
    have hkj : (k, j) ∈ F := (hF (k, j)).mpr ⟨hN, hux⟩
    have hnorm : |(faddeevModularUHPPole γ τ k j).re - x| ≤
        ‖((x : ℂ) + t * I) - faddeevModularUHPPole γ τ k j‖ := by
      have h := Complex.abs_re_le_norm
        (((x : ℂ) + t * I) - faddeevModularUHPPole γ τ k j)
      simpa [Complex.sub_re, abs_sub_comm] using h
    exact (min_le_left R 1).trans ((hgap (k, j) hkj).trans hnorm)
  · have hreal : 1 ≤ u.re - x := by linarith
    have hdist := norm_sub_ge_re_gap u ((x : ℂ) + t * I) (by simpa using hreal)
    have hnorm : 1 ≤ ‖((x : ℂ) + t * I) - u‖ := by
      simpa only [norm_sub_rev] using hdist
    exact (min_le_right R 1).trans hnorm

/-- A vertical line to the right of the shifted left poles that meets no genuine right pole
keeps a positive distance from both pole families, even when finitely many right poles lie on
its left. This is the straight contour of [RW26, Radchenko, Wheeler (2026), Theorem 3,
`thm:5term.mod.fad`, Appendix A.2, `app:mod.fad`] before its deformation around those poles. -/
theorem exists_pos_dist_fiveTerm_of_regular
    (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (m p : ℤ) (y τ : ℂ)
    (hτ : 0 < τ.im) (he : 0 < (fltDenominator (γ : Mat(2, ℤ)) τ).re)
    (x : ℝ)
    (hxP : ∀ u ∈ faddeevModularUHPPoles γ (m + 1) τ, u.re ≠ x)
    (hxL : (-((m + p : ℤ) : ℝ) * (fltDenominator (γ : Mat(2, ℤ)) τ).re - 1) /
      (γ 1 0 : ℝ) - y.re < x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ,
      (∀ u ∈ faddeevModularUHPPoles γ (m + 1) τ,
        δ ≤ ‖((x : ℂ) + t * I) - u‖) ∧
      (∀ u ∈ faddeevModularUHPZeros γ (m + p) τ,
        δ ≤ ‖((x : ℂ) + t * I) + y - u‖) := by
  obtain ⟨R, hR, hRight⟩ :=
    exists_pos_dist_right_vertical γ hc m τ hτ he x hxP
  obtain ⟨L, hL, hLeft⟩ :=
    exists_pos_dist_left_vertical γ hc m p y τ hτ he.le x hxL
  refine ⟨min R L, lt_min hR hL, ?_⟩
  intro t
  constructor
  · intro u hu
    exact (min_le_left R L).trans (hRight t u hu)
  · intro u hu
    exact (min_le_right R L).trans (hLeft t u hu)

end SIC
