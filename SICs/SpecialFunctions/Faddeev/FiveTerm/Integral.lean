/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.Faddeev.FiveTerm.Rectangle
import SICs.SpecialFunctions.Faddeev.FiveTerm.ContourLimits
import SICs.SpecialFunctions.Faddeev.FiveTerm.Integrability
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The upper-half-plane five-term integral in the residue region

The integral of the five-term kernel equals the closed five-term expression where the
residue series converges absolutely.

This module follows [RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`], the
residue computation in the proof of Theorem 3, `thm:5term.mod.fad`, equation (23), at
`n = h = 0`.

## The argument

We close each upward vertical contour to the right with rectangles. Their horizontal sides
lie halfway between consecutive rows of the period lattice. For each height we choose a
right side far enough that its integral is small and that it misses the pole set. The
top and bottom integrals vanish uniformly in this choice. The finite pole sets exhaust
all genuine poles, so absolute convergence lets the rectangle residues tend to their
full series. The contour orientation gives the factor $-2\pi i$. Summing over the
representatives $0\le m<c$ and evaluating the residue series gives the identity.

The residue convergence conditions on $w$ are retained in the crossed-pole identity here.
Its raw totalized expression is not the continued point value at some common zeros outside
this region.

The contour need not lie to the left of every right pole. If it lies to the right of the shifted
left poles and meets no right pole, only finitely many right poles lie to its left; the
rectangles then exhaust the others, and the integral is $-2\pi i$ times the series minus their
residues. This is the straight-line form of the source's deformation of the contour around
those poles.
-/

noncomputable section

open Complex Real Filter Set MeasureTheory
open scoped MatrixGroups Topology

namespace SIC


/-! ### Heights between lattice rows

The heights $((n+1/2)\operatorname{Im}\tau)$ separate every point on either horizontal
side of the rectangle from the genuine poles, by
`dist_faddeevModularUHPPoles_le_of_half_height`. -/

/-- The chosen half-integer heights tend to infinity. -/
private lemma fiveTerm_heights_tendsto (τ : ℂ) (hτ : 0 < τ.im) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1 / 2) * τ.im) atTop atTop := by
  exact (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_mul_const hτ

/-- Both sides at height $\pm(n+1/2)\operatorname{Im}\tau$ have the same pole gap. -/
private lemma fiveTerm_height_pole_gaps (γ : SL(2, ℤ)) (m : ℤ) (τ : ℂ)
    (hτ : 0 < τ.im) (n : ℕ) (s : ℝ) {u : ℂ}
    (hu : u ∈ faddeevModularUHPPoles γ (m + 1) τ) :
    τ.im / 2 ≤ ‖((s : ℂ) + (((n : ℝ) + 1 / 2) * τ.im) * I) - u‖ ∧
    τ.im / 2 ≤ ‖((s : ℂ) - (((n : ℝ) + 1 / 2) * τ.im) * I) - u‖ := by
  constructor
  · simpa using dist_faddeevModularUHPPoles_le_of_half_height
      γ m τ hτ (n : ℤ) s hu
  · convert dist_faddeevModularUHPPoles_le_of_half_height
      γ m τ hτ (-(n : ℤ) - 1) s hu using 1
    congr 1
    push_cast
    ring

/-- Neither horizontal side meets a genuine pole. -/
private lemma fiveTerm_height_avoids_poles (γ : SL(2, ℤ)) (m : ℤ) (τ : ℂ)
    (hτ : 0 < τ.im) (n : ℕ) {u : ℂ}
    (hu : u ∈ faddeevModularUHPPoles γ (m + 1) τ) :
    u.im ≠ -(((n : ℝ) + 1 / 2) * τ.im) ∧
      u.im ≠ ((n : ℝ) + 1 / 2) * τ.im := by
  have hg := fiveTerm_height_pole_gaps γ m τ hτ n u.re hu
  constructor
  · intro h
    have hz : ((u.re : ℂ) - (((n : ℝ) + 1 / 2) * τ.im) * I) = u := by
      calc
        _ = (u.re : ℂ) + (u.im : ℂ) * I := by rw [h]; push_cast; ring
        _ = u := Complex.re_add_im u
    rw [hz, sub_self, norm_zero] at hg
    linarith [hg.2]
  · intro h
    have hz : ((u.re : ℂ) + (((n : ℝ) + 1 / 2) * τ.im) * I) = u := by
      calc
        _ = (u.re : ℂ) + (u.im : ℂ) * I := by rw [h]; push_cast; ring
        _ = u := Complex.re_add_im u
    rw [hz, sub_self, norm_zero] at hg
    linarith [hg.1]

/-! ### Diagonal right edges

For each fixed height, the right-side estimate gives a sequence of pole-free edges with
vanishing integrals. Choosing one sufficiently far out also forces the chosen edges to
escape to infinity as the height grows. -/

/-- At each height choose a good right edge beyond $n+1$ with right integral below
$1/(n+1)$. -/
private lemma exists_fiveTerm_diagonal_right_edge (γ : SL(2, ℤ))
    (hc : 0 < γ 1 0) (ℓ p m : ℤ) (w y τ : ℂ) (hτ : 0 < τ.im)
    (hv : 0 < ((w + y) / fltDenominator (γ : Mat(2, ℤ)) τ).im)
    (x : ℝ) (n : ℕ) :
    ∃ X : ℝ, x + 1 ≤ X ∧ (n : ℝ) + 1 ≤ X ∧
      (∀ u ∈ faddeevModularUHPPoles γ (m + 1) τ, u.re ≠ X) ∧
      ‖∫ t in -(((n : ℝ) + 1 / 2) * τ.im)..(((n : ℝ) + 1 / 2) * τ.im),
        fiveTermKernelUHP γ ℓ p w y τ m ((X : ℂ) + t * I)‖ <
        1 / ((n : ℝ) + 1) := by
  let Y : ℝ := ((n : ℝ) + 1 / 2) * τ.im
  obtain ⟨δ, hδ, R, hR, hsep, havoid⟩ :=
    exists_pos_dist_fiveTerm_right_sides γ m τ hτ (-Y) Y
  have hlim := tendsto_integral_fiveTermKernelUHP_right
    γ hc ℓ p m w y τ hτ (-Y) Y R hR δ hδ hsep hv
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hlim)
    (1 / ((n : ℝ) + 1)) (by positivity)
  obtain ⟨k, hk, hkN⟩ :=
    ((hR.eventually_ge_atTop (max (x + 1) ((n : ℝ) + 1))).and
      (eventually_ge_atTop N)).exists
  refine ⟨R k, le_trans (le_max_left _ _) hk,
    le_trans (le_max_right _ _) hk, havoid k, ?_⟩
  simpa only [dist_zero_right] using hN k hkN

/-- Choose escaping right edges whose vertical integrals vanish and which avoid every pole. -/
private lemma exists_fiveTerm_diagonal_right_edges (γ : SL(2, ℤ))
    (hc : 0 < γ 1 0) (ℓ p m : ℤ) (w y τ : ℂ) (hτ : 0 < τ.im)
    (hv : 0 < ((w + y) / fltDenominator (γ : Mat(2, ℤ)) τ).im)
    (x : ℝ) :
    ∃ X : ℕ → ℝ, Tendsto X atTop atTop ∧ (∀ n, x < X n) ∧
      (∀ n, ∀ u ∈ faddeevModularUHPPoles γ (m + 1) τ, u.re ≠ X n) ∧
      (∀ n,
        ‖∫ t in -(((n : ℝ) + 1 / 2) * τ.im)..(((n : ℝ) + 1 / 2) * τ.im),
          fiveTermKernelUHP γ ℓ p w y τ m ((X n : ℂ) + t * I)‖ <
          1 / ((n : ℝ) + 1)) := by
  classical
  let edge := fun n : ℕ =>
    exists_fiveTerm_diagonal_right_edge γ hc ℓ p m w y τ hτ hv x n
  refine ⟨fun n => (edge n).choose, ?_, ?_, ?_, ?_⟩
  · exact tendsto_atTop_mono (fun n => (edge n).choose_spec.2.1)
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  · intro n
    linarith [(edge n).choose_spec.1]
  · intro n u hu
    exact (edge n).choose_spec.2.2.1 u hu
  · intro n
    exact (edge n).choose_spec.2.2.2

/-! ### Exhaustion of the genuine poles

Every genuine pole either lies in the finite set left of the contour or eventually
inside the increasing vertical and horizontal bounds. Monotonicity of the finite pole
sets is unnecessary. -/

/-- The union of rectangle poles and the finitely many poles left of a regular contour
exhausts the genuine poles. -/
private lemma fiveTerm_rectangle_indices_exhaust (γ : SL(2, ℤ))
    (m : ℤ) (τ : ℂ) (hτ : 0 < τ.im) (x : ℝ)
    (hxP : ∀ u ∈ faddeevModularUHPPoles γ (m + 1) τ, u.re ≠ x)
    (X : ℕ → ℝ) (hX : Tendsto X atTop atTop)
    (S : ℕ → Finset (ℤ × ℕ))
    (hS : ∀ n kj, kj ∈ S n ↔
      0 ≤ faddeevModularUHPIndex γ m kj.1 kj.2 ∧
        x < (faddeevModularUHPPole γ τ kj.1 kj.2).re ∧
        (faddeevModularUHPPole γ τ kj.1 kj.2).re < X n ∧
        -(((n : ℝ) + 1 / 2) * τ.im) < (faddeevModularUHPPole γ τ kj.1 kj.2).im ∧
        (faddeevModularUHPPole γ τ kj.1 kj.2).im < ((n : ℝ) + 1 / 2) * τ.im)
    (F : Finset (ℤ × ℕ))
    (hF : ∀ kj : ℤ × ℕ, kj ∈ F ↔
      0 ≤ faddeevModularUHPIndex γ m kj.1 kj.2 ∧
        (faddeevModularUHPPole γ τ kj.1 kj.2).re < x) :
    Tendsto (fun n => (S n ∪ F).subtype (fun kj =>
      0 ≤ faddeevModularUHPIndex γ m kj.1 kj.2)) atTop atTop := by
  classical
  rw [Filter.atTop_finset_eq_iInf, tendsto_iInf]
  rintro ⟨⟨k, j⟩, hN⟩
  simp only [tendsto_principal, mem_Ici, Finset.singleton_subset_iff]
  have hu : faddeevModularUHPPole γ τ k j ∈
      faddeevModularUHPPoles γ (m + 1) τ :=
    (mem_faddeevModularUHPPoles_iff γ m hτ).mpr ⟨k, j, rfl, hN⟩
  rcases lt_trichotomy (faddeevModularUHPPole γ τ k j).re x with hx | heq | hx
  · exact Eventually.of_forall fun n => by
      simp [Finset.mem_subtype, (hF (k, j)).mpr ⟨hN, hx⟩]
  · exact False.elim (hxP _ hu heq)
  let Y : ℕ → ℝ := fun n => ((n : ℝ) + 1 / 2) * τ.im
  have hY : Tendsto Y atTop atTop := fiveTerm_heights_tendsto τ hτ
  filter_upwards [hX.eventually_ge_atTop ((faddeevModularUHPPole γ τ k j).re + 1),
    hY.eventually_ge_atTop (|(faddeevModularUHPPole γ τ k j).im| + 1)] with n hnX hnY
  simp only [Finset.mem_subtype, Finset.mem_union]
  left
  apply (hS n (k, j)).mpr
  have hlo := neg_abs_le (faddeevModularUHPPole γ τ k j).im
  have hhi := le_abs_self (faddeevModularUHPPole γ τ k j).im
  exact ⟨hN, hx, by linarith, by dsimp [Y] at hnY; linarith,
    by dsimp [Y] at hnY; linarith⟩

/-- Disjoint finite sets of genuine pole indices sum over their union as a subtype
of all genuine pole indices. -/
private lemma fiveTerm_sum_union_subtype (γ : SL(2, ℤ)) (m : ℤ)
    (S F : Finset (ℤ × ℕ))
    (hS : ∀ kj ∈ S, kj ∈ fiveTermPoles γ m)
    (hF : ∀ kj ∈ F, kj ∈ fiveTermPoles γ m)
    (hdisj : Disjoint S F) (f : ℤ × ℕ → ℂ) :
    (∑ kj ∈ S, f kj) + ∑ kj ∈ F, f kj =
      ∑ kj ∈ (S ∪ F).subtype (fun kj =>
        0 ≤ faddeevModularUHPIndex γ m kj.1 kj.2), f kj.1 := by
  classical
  have hmem : ∀ kj ∈ S ∪ F,
      0 ≤ faddeevModularUHPIndex γ m kj.1 kj.2 := by
    intro kj hkj
    rcases Finset.mem_union.mp hkj with hkj | hkj
    · exact hS kj hkj
    · exact hF kj hkj
  have hmap : ((S ∪ F).subtype (fun kj : ℤ × ℕ =>
      0 ≤ faddeevModularUHPIndex γ m kj.1 kj.2)).map
      (Function.Embedding.subtype _) = S ∪ F := Finset.subtype_map_of_mem hmem
  calc
    _ = ∑ kj ∈ S ∪ F, f kj := (Finset.sum_union hdisj).symm
    _ = _ := by
      conv_lhs => rw [← hmap, Finset.sum_map]
      rfl

/-- The rectangle residue sums converge to the full series minus the finite left-pole sum. -/
private lemma fiveTerm_rectangle_residues_tendsto (γ : SL(2, ℤ))
    (m : ℤ) (ℓ p : ℤ) (w y τ : ℂ)
    (S : ℕ → Finset (ℤ × ℕ))
    (hS : ∀ n kj, kj ∈ S n → kj ∈ fiveTermPoles γ m)
    (F : Finset (ℤ × ℕ))
    (hF : ∀ kj ∈ F, kj ∈ fiveTermPoles γ m)
    (hdisj : ∀ n, Disjoint (S n) F)
    (hexhaust : Tendsto (fun n => (S n ∪ F).subtype (fun kj =>
      0 ≤ faddeevModularUHPIndex γ m kj.1 kj.2))
      atTop atTop)
    (hs : Summable (fun kj : fiveTermPoles γ m =>
      fiveTermResidueUHP γ ℓ p w y τ
        (faddeevModularUHPIndex γ m kj.1.1 kj.1.2) kj.1.2)) :
    Tendsto (fun n => ∑ kj ∈ S n, fiveTermResidueUHP γ ℓ p w y τ
      (faddeevModularUHPIndex γ m kj.1 kj.2) kj.2) atTop
      (𝓝 ((∑' kj : fiveTermPoles γ m,
        fiveTermResidueUHP γ ℓ p w y τ
          (faddeevModularUHPIndex γ m kj.1.1 kj.1.2) kj.1.2) -
        ∑ kj ∈ F, fiveTermResidueUHP γ ℓ p w y τ
          (faddeevModularUHPIndex γ m kj.1 kj.2) kj.2)) := by
  classical
  have hlim := hs.hasSum.comp hexhaust
  have hlim' : Tendsto (fun n =>
      (∑ kj ∈ S n, fiveTermResidueUHP γ ℓ p w y τ
        (faddeevModularUHPIndex γ m kj.1 kj.2) kj.2) +
      ∑ kj ∈ F, fiveTermResidueUHP γ ℓ p w y τ
        (faddeevModularUHPIndex γ m kj.1 kj.2) kj.2) atTop
      (𝓝 (∑' kj : fiveTermPoles γ m,
        fiveTermResidueUHP γ ℓ p w y τ
          (faddeevModularUHPIndex γ m kj.1.1 kj.1.2) kj.1.2)) := by
    convert hlim using 1
    ext n
    change (∑ kj ∈ S n, fiveTermResidueUHP γ ℓ p w y τ
        (faddeevModularUHPIndex γ m kj.1 kj.2) kj.2) +
      ∑ kj ∈ F, fiveTermResidueUHP γ ℓ p w y τ
        (faddeevModularUHPIndex γ m kj.1 kj.2) kj.2 =
      ∑ kj ∈ (S n ∪ F).subtype (fun kj =>
        0 ≤ faddeevModularUHPIndex γ m kj.1 kj.2),
        fiveTermResidueUHP γ ℓ p w y τ
          (faddeevModularUHPIndex γ m kj.1.1 kj.1.2) kj.1.2
    exact fiveTerm_sum_union_subtype γ m (S n) F (hS n) hF (hdisj n) _
  convert hlim'.sub_const (∑ kj ∈ F,
    fiveTermResidueUHP γ ℓ p w y τ
      (faddeevModularUHPIndex γ m kj.1 kj.2) kj.2) using 1
  simp

/-! ### Passage from finite rectangles to a vertical integral

The chosen right integrals are bounded by a null sequence; the horizontal integrals
vanish by the uniform closing estimates. -/

/-- The right integrals chosen by `exists_fiveTerm_diagonal_right_edge` tend to zero. -/
private lemma fiveTerm_diagonal_right_tendsto (γ : SL(2, ℤ))
    (ℓ p m : ℤ) (w y τ : ℂ) (X : ℕ → ℝ)
    (hX : ∀ n,
      ‖∫ t in -(((n : ℝ) + 1 / 2) * τ.im)..(((n : ℝ) + 1 / 2) * τ.im),
        fiveTermKernelUHP γ ℓ p w y τ m ((X n : ℂ) + t * I)‖ <
        1 / ((n : ℝ) + 1)) :
    Tendsto (fun n => ∫ t in -(((n : ℝ) + 1 / 2) * τ.im)..
      (((n : ℝ) + 1 / 2) * τ.im),
      fiveTermKernelUHP γ ℓ p w y τ m ((X n : ℂ) + t * I))
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall fun n => (hX n).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

/-- The two interval endpoints tending to opposite infinities recover the full
vertical integral. -/
private lemma fiveTerm_vertical_truncations_tendsto (γ : SL(2, ℤ))
    (ℓ p m : ℤ) (w y τ : ℂ) (hτ : 0 < τ.im) (x : ℝ)
    (hi : Integrable (fun t : ℝ => fiveTermKernelUHP γ ℓ p w y τ m
      ((x : ℂ) + t * I))) :
    Tendsto (fun n : ℕ => ∫ t in -(((n : ℝ) + 1 / 2) * τ.im)..
      (((n : ℝ) + 1 / 2) * τ.im),
      fiveTermKernelUHP γ ℓ p w y τ m ((x : ℂ) + t * I))
      atTop (𝓝 (∫ t : ℝ, fiveTermKernelUHP γ ℓ p w y τ m
        ((x : ℂ) + t * I))) := by
  have hY := fiveTerm_heights_tendsto τ hτ
  exact intervalIntegral_tendsto_integral hi
    (tendsto_neg_atTop_atBot.comp hY) hY

/-- If the three closing sides vanish, the oriented rectangle formula tends to
$iL=-2\pi iP$. -/
private lemma fiveTerm_four_side_limit {B T R L P : ℕ → ℂ} {Llim Plim : ℂ}
    (hB : Tendsto B atTop (𝓝 0)) (hT : Tendsto T atTop (𝓝 0))
    (hR : Tendsto R atTop (𝓝 0)) (hL : Tendsto L atTop (𝓝 Llim))
    (hP : Tendsto P atTop (𝓝 Plim))
    (hrect : ∀ n, B n - T n + I * R n - I * L n = 2 * π * I * P n) :
    I * Llim = (-2 * π * I) * Plim := by
  have hboundary := ((hB.sub hT).add
    ((tendsto_const_nhds (x := (I : ℂ))).mul hR)).sub
    ((tendsto_const_nhds (x := (I : ℂ))).mul hL)
  have hresidue := (tendsto_const_nhds (x := (2 * π * I : ℂ))).mul hP
  have heq : (0 : ℂ) - 0 + I * 0 - I * Llim = (2 * π * I) * Plim := by
    exact tendsto_nhds_unique
      (hboundary.congr' (Eventually.of_forall hrect)) hresidue
  calc
    I * Llim = -((0 : ℂ) - 0 + I * 0 - I * Llim) := by ring
    _ = -((2 * π * I) * Plim) := congrArg Neg.neg heq
    _ = _ := by ring

/-- A rectangle contains only poles to the right of its left edge, disjoint from the
finite pole set strictly left of that edge. -/
private lemma fiveTerm_rectangle_pole_sets_disjoint (γ : SL(2, ℤ))
    (τ : ℂ) (x : ℝ) (S : ℕ → Finset (ℤ × ℕ))
    (hS : ∀ n kj, kj ∈ S n →
      x < (faddeevModularUHPPole γ τ kj.1 kj.2).re)
    (F : Finset (ℤ × ℕ))
    (hF : ∀ kj ∈ F, (faddeevModularUHPPole γ τ kj.1 kj.2).re < x) :
    ∀ n, Disjoint (S n) F := by
  intro n
  apply Finset.disjoint_left.mpr
  intro kj hkj hkjF
  exact lt_asymm (hS n kj hkj) (hF kj hkjF)

/-- The limits of the four rectangle sides turn the finite residue formula into
the vertical-integral formula for one representative. -/
private lemma fiveTerm_rectangle_limit (γ : SL(2, ℤ)) (hc : 0 < γ 1 0)
    (ℓ p m : ℤ) (w y τ : ℂ) (hτ : 0 < τ.im)
    (he : 0 < (fltDenominator (γ : Mat(2, ℤ)) τ).re)
    (hLam : 0 < ((((γ 1 0 : ℤ) : ℂ) * w /
      fltDenominator (γ : Mat(2, ℤ)) τ + ℓ)).re)
    (hMu : ((((γ 1 0 : ℤ) : ℂ) * (w + y) /
      fltDenominator (γ : Mat(2, ℤ)) τ + ℓ + p - 1)).re < 0)
    (hu : 0 < ((ℓ : ℂ) * τ + w).im)
    (hv : 0 < ((w + y) / fltDenominator (γ : Mat(2, ℤ)) τ).im)
    (x : ℝ) (hi : Integrable (fun t : ℝ =>
      fiveTermKernelUHP γ ℓ p w y τ m ((x : ℂ) + t * I)))
    (hxP : ∀ u ∈ faddeevModularUHPPoles γ (m + 1) τ, u.re ≠ x)
    (X : ℕ → ℝ) (hX : Tendsto X atTop atTop) (hxX : ∀ n, x ≤ X n)
    (hRight : ∀ n,
      ‖∫ t in -(((n : ℝ) + 1 / 2) * τ.im)..(((n : ℝ) + 1 / 2) * τ.im),
        fiveTermKernelUHP γ ℓ p w y τ m ((X n : ℂ) + t * I)‖ <
        1 / ((n : ℝ) + 1))
    (S : ℕ → Finset (ℤ × ℕ))
    (hS : ∀ n kj, kj ∈ S n ↔
      0 ≤ faddeevModularUHPIndex γ m kj.1 kj.2 ∧
        x < (faddeevModularUHPPole γ τ kj.1 kj.2).re ∧
        (faddeevModularUHPPole γ τ kj.1 kj.2).re < X n ∧
        -(((n : ℝ) + 1 / 2) * τ.im) < (faddeevModularUHPPole γ τ kj.1 kj.2).im ∧
        (faddeevModularUHPPole γ τ kj.1 kj.2).im < ((n : ℝ) + 1 / 2) * τ.im)
    (hRect : ∀ n : ℕ,
      (∫ s : ℝ in x..X n, fiveTermKernelUHP γ ℓ p w y τ m
          (s - (((n : ℝ) + 1 / 2) * τ.im) * I)) -
        (∫ s : ℝ in x..X n, fiveTermKernelUHP γ ℓ p w y τ m
          (s + (((n : ℝ) + 1 / 2) * τ.im) * I)) +
        I * (∫ t : ℝ in -(((n : ℝ) + 1 / 2) * τ.im)..
          (((n : ℝ) + 1 / 2) * τ.im), fiveTermKernelUHP γ ℓ p w y τ m
            (X n + t * I)) -
        I * (∫ t : ℝ in -(((n : ℝ) + 1 / 2) * τ.im)..
          (((n : ℝ) + 1 / 2) * τ.im), fiveTermKernelUHP γ ℓ p w y τ m
            (x + t * I)) =
      2 * π * I * ∑ kj ∈ S n, fiveTermResidueUHP γ ℓ p w y τ
        (faddeevModularUHPIndex γ m kj.1 kj.2) kj.2)
    (hs : Summable (fun kj : fiveTermPoles γ m =>
      fiveTermResidueUHP γ ℓ p w y τ
        (faddeevModularUHPIndex γ m kj.1.1 kj.1.2) kj.1.2))
    (F : Finset (ℤ × ℕ))
    (hF : ∀ kj : ℤ × ℕ, kj ∈ F ↔
      0 ≤ faddeevModularUHPIndex γ m kj.1 kj.2 ∧
        (faddeevModularUHPPole γ τ kj.1 kj.2).re < x) :
    I * (∫ t : ℝ, fiveTermKernelUHP γ ℓ p w y τ m
      ((x : ℂ) + t * I)) =
      (-2 * π * I) * ((∑' kj : fiveTermPoles γ m,
        fiveTermResidueUHP γ ℓ p w y τ
          (faddeevModularUHPIndex γ m kj.1.1 kj.1.2) kj.1.2) -
        ∑ kj ∈ F, fiveTermResidueUHP γ ℓ p w y τ
          (faddeevModularUHPIndex γ m kj.1 kj.2) kj.2) := by
  let Y : ℕ → ℝ := fun n => ((n : ℝ) + 1 / 2) * τ.im
  have hY : Tendsto Y atTop atTop := fiveTerm_heights_tendsto τ hτ
  have htop := tendsto_integral_fiveTermKernelUHP_top γ hc ℓ p m w y τ
    hτ hLam hu hv x Y X hY hxX (τ.im / 2) (by positivity)
    (fun n s _ u h => by simpa [Y] using
      (fiveTerm_height_pole_gaps γ m τ hτ n s h).1)
  have hbottom := tendsto_integral_fiveTermKernelUHP_bottom γ hc ℓ p m w y τ
    hτ he hMu hv x Y X hY hxX
  have hright := fiveTerm_diagonal_right_tendsto γ ℓ p m w y τ X hRight
  have hleft := fiveTerm_vertical_truncations_tendsto γ ℓ p m w y τ hτ x hi
  have hexhaust := fiveTerm_rectangle_indices_exhaust γ m τ hτ x hxP
    X hX S hS F hF
  have hdisj := fiveTerm_rectangle_pole_sets_disjoint γ τ x S
    (fun n kj h => ((hS n kj).mp h).2.1) F (fun kj h => ((hF kj).mp h).2)
  have hres := fiveTerm_rectangle_residues_tendsto γ m ℓ p w y τ S
    (fun n kj h => (hS n kj).mp h |>.1) F
    (fun kj h => (hF kj).mp h |>.1) hdisj hexhaust hs
  apply fiveTerm_four_side_limit hbottom htop hright hleft hres
  intro n
  simpa [Y] using hRect n

/-! ### Right poles to the left of the contours

A vertical line to the right of the shifted left poles may have finitely many right poles on its
left. The rectangles then exhaust only the right poles to its right, so the contour integral is
the residue series minus the finitely many residues on its left. This is the straight-line form of
the deformation clause of Theorem 3: the separating contour runs around those poles. -/

/-- One upward vertical contour to the right of the shifted left poles and meeting no genuine
right pole equals `-2πi` times the absolutely convergent series of right-pole residues, minus
the residues at the finitely many right poles to its left, indexed by `F`. This is the
straight-line form of the contour deformation in [RW26, Radchenko, Wheeler (2026), Theorem 3,
`thm:5term.mod.fad`, Appendix A.2, `app:mod.fad`] at `n = h = 0`. -/
theorem integral_fiveTermKernelUHP_of_crossed
    (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (ℓ p m : ℤ) (w y τ : ℂ) (hτ : 0 < τ.im)
    (he : 0 < (fltDenominator (γ : Mat(2, ℤ)) τ).re)
    (hLam : 0 < ((((γ 1 0 : ℤ) : ℂ) * w /
      fltDenominator (γ : Mat(2, ℤ)) τ + ℓ)).re)
    (hMu : ((((γ 1 0 : ℤ) : ℂ) * (w + y) /
      fltDenominator (γ : Mat(2, ℤ)) τ + ℓ + p - 1)).re < 0)
    (hu : 0 < ((ℓ : ℂ) * τ + w).im)
    (hv : 0 < ((w + y) / fltDenominator (γ : Mat(2, ℤ)) τ).im)
    (ha : qPochhammer ((p : ℂ) * τ + y) τ ≠ 0)
    (x : ℝ)
    (hxP : ∀ u ∈ faddeevModularUHPPoles γ (m + 1) τ, u.re ≠ x)
    (hxL : (-((m + p : ℤ) : ℝ) * (fltDenominator (γ : Mat(2, ℤ)) τ).re - 1) /
      (γ 1 0 : ℝ) - y.re < x)
    (hs : Summable (fun kj : fiveTermPoles γ m =>
      fiveTermResidueUHP γ ℓ p w y τ
        (faddeevModularUHPIndex γ m kj.1.1 kj.1.2) kj.1.2))
    (F : Finset (ℤ × ℕ))
    (hF : ∀ kj : ℤ × ℕ, kj ∈ F ↔ 0 ≤ faddeevModularUHPIndex γ m kj.1 kj.2 ∧
      (faddeevModularUHPPole γ τ kj.1 kj.2).re < x) :
    I * (∫ t : ℝ, fiveTermKernelUHP γ ℓ p w y τ m
      ((x : ℂ) + t * I)) =
      (-2 * π * I) * ((∑' kj : fiveTermPoles γ m,
        fiveTermResidueUHP γ ℓ p w y τ
          (faddeevModularUHPIndex γ m kj.1.1 kj.1.2) kj.1.2) -
        ∑ kj ∈ F, fiveTermResidueUHP γ ℓ p w y τ
          (faddeevModularUHPIndex γ m kj.1 kj.2) kj.2) := by
  classical
  let Y : ℕ → ℝ := fun n => ((n : ℝ) + 1 / 2) * τ.im
  obtain ⟨X, hX, hxX, hAvoid, hRight⟩ :=
    exists_fiveTerm_diagonal_right_edges γ hc ℓ p m w y τ hτ hv x
  let rect := fun n : ℕ =>
    integral_boundary_rect_fiveTermKernelUHP_of_regular γ hc ℓ p m w y τ
      hτ he.le x (X n) (-Y n) (Y n)
      (hxX n)
      (by have hY : 0 < Y n := mul_pos (by positivity) hτ; linarith)
      hxP hxL ha
      (fun u hu => (fiveTerm_height_avoids_poles γ m τ hτ n hu).1)
      (fun u hu => (fiveTerm_height_avoids_poles γ m τ hτ n hu).2)
      (hAvoid n)
  let S : ℕ → Finset (ℤ × ℕ) := fun n => (rect n).choose
  refine fiveTerm_rectangle_limit γ hc ℓ p m w y τ hτ he hLam hMu hu hv x
    (integrable_fiveTermKernelUHP_of_regular γ hc ℓ p m w y τ
      hτ he hLam hMu x hxP hxL) hxP X hX (fun n => (hxX n).le) hRight S ?_ ?_ hs F hF
  · intro n kj
    simpa [S, Y] using (rect n).choose_spec.1 kj
  · intro n
    simpa [S, Y, sub_eq_add_neg] using (rect n).choose_spec.2

/-- Summing the absolutely convergent pole residues over representatives gives the
closed five-term expression of [RW26, Radchenko, Wheeler (2026), Theorem 3,
`thm:5term.mod.fad`, Appendix A.2, `app:mod.fad`]. -/
private lemma fiveTerm_full_residue_sum
    (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (ℓ p : ℤ) (w y τ : ℂ)
    (hτ : 0 < τ.im) (hu : 0 < ((ℓ : ℂ) * τ + w).im)
    (hv : 0 < ((y + w) / fltDenominator (γ : Mat(2, ℤ)) τ).im)
    (ha : qPochhammer ((p : ℂ) * τ + y) τ ≠ 0) :
    (-2 * π * I) * (∑ m : FiveTermIndex γ,
      ∑' kj : fiveTermPoles γ ((m : ℕ) : ℤ),
        fiveTermResidueUHP γ ℓ p w y τ
          (faddeevModularUHPIndex γ ((m : ℕ) : ℤ) kj.1.1 kj.1.2) kj.1.2) =
      faddeevModularUHPOriginValue γ τ *
        (faddeevModularUHP γ (p + ℓ) 0 (w + y) τ /
          (faddeevModularUHP γ p 0 y τ * faddeevModularUHP γ ℓ 1 w τ)) := by
  have hs := hasSum_fiveTermResidueUHP_poles γ hc ℓ p w y τ hτ hu hv ha
  have hnonzero : (-2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  calc
    _ = (-2 * π * I) * ∑' a :
        Σ m : FiveTermIndex γ, fiveTermPoles γ ((m : ℕ) : ℤ),
        fiveTermResidueUHP γ ℓ p w y τ
          (faddeevModularUHPIndex γ ((a.1 : ℕ) : ℤ) a.2.1.1 a.2.1.2)
          a.2.1.2 := by
            congr 1
            rw [hs.summable.tsum_sigma, tsum_fintype]
    _ = _ := by
      rw [hs.tsum_eq]
      exact mul_div_cancel₀ _ hnonzero

/-- The upper-half-plane five-term identity in the residue region for contours to the right of the
shifted left poles that meet no genuine right pole: finitely many right poles, indexed by `F m`,
may lie to the left of the `m`-th contour, and their residues correct the closed expression by
`2πi fiveTermResidueSumUHP`. This is the straight-line form of the contour
deformation in [RW26, Radchenko, Wheeler (2026), Theorem 3,
`thm:5term.mod.fad`, equation (23), `eq:5term.int`, Appendix A.2, `app:mod.fad`] at
`n = h = 0`, in the residue region. -/
theorem sum_integral_fiveTermKernelUHP_of_im_pos_of_crossed
    (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (ℓ p : ℤ) (w y τ : ℂ)
    (hτ : 0 < τ.im)
    (he : 0 < (fltDenominator (γ : Mat(2, ℤ)) τ).re)
    (hLam : 0 < ((((γ 1 0 : ℤ) : ℂ) * w /
      fltDenominator (γ : Mat(2, ℤ)) τ + ℓ)).re)
    (hMu : ((((γ 1 0 : ℤ) : ℂ) * (w + y) /
      fltDenominator (γ : Mat(2, ℤ)) τ + ℓ + p - 1)).re < 0)
    (hu : 0 < ((ℓ : ℂ) * τ + w).im)
    (hv : 0 < ((y + w) / fltDenominator (γ : Mat(2, ℤ)) τ).im)
    (ha : qPochhammer ((p : ℂ) * τ + y) τ ≠ 0)
    (x : FiveTermIndex γ → ℝ)
    (hxP : ∀ m : FiveTermIndex γ,
      ∀ u ∈ faddeevModularUHPPoles γ (((m : ℕ) : ℤ) + 1) τ, u.re ≠ x m)
    (hxL : ∀ m : FiveTermIndex γ, (-((((m : ℕ) : ℤ) + p : ℤ) : ℝ) *
      (fltDenominator (γ : Mat(2, ℤ)) τ).re - 1) /
      (γ 1 0 : ℝ) - y.re < x m)
    (F : FiveTermIndex γ → Finset (ℤ × ℕ))
    (hF : ∀ (m : FiveTermIndex γ) (kj : ℤ × ℕ), kj ∈ F m ↔
      0 ≤ faddeevModularUHPIndex γ ((m : ℕ) : ℤ) kj.1 kj.2 ∧
        (faddeevModularUHPPole γ τ kj.1 kj.2).re < x m) :
    (∑ m : FiveTermIndex γ, I * (∫ t : ℝ,
      fiveTermKernelUHP γ ℓ p w y τ ((m : ℕ) : ℤ) ((x m : ℂ) + t * I))) =
      faddeevModularUHPOriginValue γ τ *
          (faddeevModularUHP γ (p + ℓ) 0 (w + y) τ /
            (faddeevModularUHP γ p 0 y τ * faddeevModularUHP γ ℓ 1 w τ)) +
        2 * π * I * fiveTermResidueSumUHP γ ℓ p w y τ F := by
  have hs := hasSum_fiveTermResidueUHP_poles γ hc ℓ p w y τ hτ hu hv ha
  have hv' : 0 < ((w + y) / fltDenominator (γ : Mat(2, ℤ)) τ).im := by
    simpa only [add_comm w y] using hv
  have hm (m : FiveTermIndex γ) :=
    integral_fiveTermKernelUHP_of_crossed γ hc ℓ p
      ((m : ℕ) : ℤ) w y τ hτ he hLam hMu hu hv' ha (x m)
      (hxP m) (hxL m) (hs.summable.sigma_factor m) (F m) (hF m)
  calc
    (∑ m : FiveTermIndex γ, I * (∫ t : ℝ,
      fiveTermKernelUHP γ ℓ p w y τ ((m : ℕ) : ℤ)
        ((x m : ℂ) + t * I))) =
        (-2 * π * I) * (∑ m : FiveTermIndex γ,
          ∑' kj : fiveTermPoles γ ((m : ℕ) : ℤ),
            fiveTermResidueUHP γ ℓ p w y τ
              (faddeevModularUHPIndex γ ((m : ℕ) : ℤ) kj.1.1 kj.1.2) kj.1.2) -
        (-2 * π * I) * fiveTermResidueSumUHP γ ℓ p w y τ F := by
          simp_rw [hm, mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum]
          rfl
    _ = _ := by
      rw [fiveTerm_full_residue_sum γ hc ℓ p w y τ hτ hu hv ha]
      ring

end SIC
