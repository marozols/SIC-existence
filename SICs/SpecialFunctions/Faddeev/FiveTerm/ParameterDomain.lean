/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.Faddeev.Modular
import Mathlib.Analysis.Complex.Convex

/-!
# The parameter strip of the five-term integral

The convergence strip in the parameter `w` and its intersection with the residue region.

This module follows the analytic continuation in [RW26, Radchenko, Wheeler (2026),
Appendix A.2, `app:mod.fad`]. For `ε = cτ+d`, the corrected convergence conditions are
`0 < Re(cw/ε+ℓ)` and `Re(c(w+y)/ε+ℓ+p-1) < 0`.

## The argument

Both inequalities are affine half planes, so their intersection is open and convex.
Translation in the direction `iε` preserves both real parts. When `Re ε > 0`, a
sufficiently large such translation makes both residue-series imaginary parts positive.
-/

noncomputable section

open Complex Real Filter Set
open scoped Topology MatrixGroups

namespace SIC

/-- The strip of absolute convergence in `w` for [RW26, Radchenko, Wheeler (2026),
Theorem 3, `thm:5term.mod.fad`, equation (23), `eq:5term.int`], at `n=h=0`, with
the corrected lower condition `Re(c(w+y)/ε+ℓ+p-1) < 0`. -/
def fiveTermParameterStrip (γ : SL(2, ℤ)) (ℓ p : ℤ) (y τ : ℂ) : Set ℂ :=
  {w | 0 < ((((γ 1 0 : ℤ) : ℂ) * w /
      fltDenominator (γ : Mat(2, ℤ)) τ + ℓ)).re ∧
    ((((γ 1 0 : ℤ) : ℂ) * (w + y) /
      fltDenominator (γ : Mat(2, ℤ)) τ + ℓ + p - 1)).re < 0}

/-! ### Topology and convexity

The two convergence conditions define affine open half planes in the parameter `w`, and they
persist under small changes of the period where `j_γ` does not vanish. -/

/-- Unfolding lemma for `fiveTermParameterStrip`; see that definition for the source. -/
@[simp] theorem mem_fiveTermParameterStrip (γ : SL(2, ℤ)) (ℓ p : ℤ) (y τ w : ℂ) :
    w ∈ fiveTermParameterStrip γ ℓ p y τ ↔
      0 < ((((γ 1 0 : ℤ) : ℂ) * w / fltDenominator (γ : Mat(2, ℤ)) τ + ℓ)).re ∧
      ((((γ 1 0 : ℤ) : ℂ) * (w + y) / fltDenominator (γ : Mat(2, ℤ)) τ + ℓ + p - 1)).re < 0 :=
  Iff.rfl

/-- The convergence strip is open in `w`; see [RW26, Radchenko, Wheeler (2026),
Appendix A.2, `app:mod.fad`]. -/
theorem isOpen_fiveTermParameterStrip (γ : SL(2, ℤ)) (ℓ p : ℤ) (y τ : ℂ) :
    IsOpen (fiveTermParameterStrip γ ℓ p y τ) := by
  change IsOpen {w : ℂ | 0 < ((((γ 1 0 : ℤ) : ℂ) * w /
      fltDenominator (γ : Mat(2, ℤ)) τ + ℓ)).re ∧
    ((((γ 1 0 : ℤ) : ℂ) * (w + y) /
      fltDenominator (γ : Mat(2, ℤ)) τ + ℓ + p - 1)).re < 0}
  exact (isOpen_lt (by fun_prop) (by fun_prop)).and
    (isOpen_lt (by fun_prop) (by fun_prop))

/-- Membership of `w` in the convergence strip persists for periods near `τ₀` when
`j_γ(τ₀) ≠ 0`: both conditions are strict inequalities between functions continuous in the period
there. -/
theorem eventually_mem_fiveTermParameterStrip (γ : SL(2, ℤ)) (ℓ p : ℤ) (y w τ₀ : ℂ)
    (hε : fltDenominator (γ : Mat(2, ℤ)) τ₀ ≠ 0)
    (hw : w ∈ fiveTermParameterStrip γ ℓ p y τ₀) :
    ∀ᶠ τ : ℂ in 𝓝 τ₀, w ∈ fiveTermParameterStrip γ ℓ p y τ := by
  obtain ⟨hUpper, hLower⟩ :=
    (mem_fiveTermParameterStrip γ ℓ p y τ₀ w).mp hw
  have hUpperContinuous : ContinuousAt (fun τ : ℂ =>
      ((((γ 1 0 : ℤ) : ℂ) * w /
        fltDenominator (γ : Mat(2, ℤ)) τ + ℓ)).re) τ₀ := by
    unfold fltDenominator at hε ⊢
    fun_prop
  have hLowerContinuous : ContinuousAt (fun τ : ℂ =>
      ((((γ 1 0 : ℤ) : ℂ) * (w + y) /
        fltDenominator (γ : Mat(2, ℤ)) τ + ℓ + p - 1)).re) τ₀ := by
    unfold fltDenominator at hε ⊢
    fun_prop
  have hUpperEventually := hUpperContinuous.tendsto.eventually_const_lt hUpper
  have hLowerEventually := hLowerContinuous.tendsto.eventually_lt_const hLower
  filter_upwards [hUpperEventually, hLowerEventually] with τ hτUpper hτLower
  exact (mem_fiveTermParameterStrip γ ℓ p y τ w).mpr
    ⟨hτUpper, hτLower⟩

/-- An affine inverse image of the right real half plane is convex; used by
`convex_fiveTermParameterStrip`. -/
private lemma convex_re_affine_gt (a b : ℂ) :
    Convex ℝ {w : ℂ | 0 < (a * w + b).re} := by
  exact (((convex_halfSpace_re_gt (0 : ℝ)).translate_preimage_left b).linear_preimage
    (LinearMap.mulLeft ℝ a))

/-- An affine inverse image of the left real half plane is convex; used by
`convex_fiveTermParameterStrip`. -/
private lemma convex_re_affine_lt (a b : ℂ) :
    Convex ℝ {w : ℂ | (a * w + b).re < 0} := by
  exact (((convex_halfSpace_re_lt (0 : ℝ)).translate_preimage_left b).linear_preimage
    (LinearMap.mulLeft ℝ a))

/-- The convergence strip is convex in `w`; see [RW26, Radchenko, Wheeler (2026),
Appendix A.2, `app:mod.fad`]. -/
theorem convex_fiveTermParameterStrip (γ : SL(2, ℤ)) (ℓ p : ℤ) (y τ : ℂ) :
    Convex ℝ (fiveTermParameterStrip γ ℓ p y τ) := by
  let ε := fltDenominator (γ : Mat(2, ℤ)) τ
  let a : ℂ := ((γ 1 0 : ℤ) : ℂ) / ε
  have heq : fiveTermParameterStrip γ ℓ p y τ =
      {w : ℂ | 0 < (a * w + ℓ).re} ∩
        {w : ℂ | (a * w + (a * y + ℓ + p - 1)).re < 0} := by
    have h₁ (w : ℂ) : a * w + ℓ =
        ((γ 1 0 : ℤ) : ℂ) * w / ε + ℓ := by
      dsimp [a]
      ring
    have h₂ (w : ℂ) : a * w + (a * y + ℓ + p - 1) =
        ((γ 1 0 : ℤ) : ℂ) * (w + y) / ε + ℓ + p - 1 := by
      dsimp [a]
      ring
    ext w
    simp only [mem_fiveTermParameterStrip, Set.mem_inter_iff, Set.mem_ofPred_eq]
    rw [h₁, h₂]
  rw [heq]
  exact (convex_re_affine_gt a ℓ).inter (convex_re_affine_lt a (a * y + ℓ + p - 1))

/-! ### Real periods

At a real period with real parameters, the two convergence conditions are inequalities on the
real decay rates of the kernel on its upper and lower vertical tails. -/

/-- The upper vertical decay rate `λ = cw/ε + ℓ`, `ε = j_γ(τ)`, of the five-term kernel at a
real period, from the convergence condition of [RW26, Radchenko, Wheeler (2026), Theorem 3,
`thm:5term.mod.fad`]. -/
def fiveTermUpperRate (γ : SL(2, ℤ)) (ℓ : ℤ) (w τ : ℝ) : ℝ :=
  (γ 1 0 : ℝ) * w / fltDenominator (γ : Mat(2, ℤ)) τ + ℓ

/-- The lower vertical decay rate `μ = c(w+y)/ε + ℓ + p - 1`, `ε = j_γ(τ)`, of the five-term
kernel at a real period. The `p` term corrects the printed convergence condition in
[RW26, Radchenko, Wheeler (2026), Theorem 3, `thm:5term.mod.fad`], as in
`fiveTermParameterStrip`. -/
def fiveTermLowerRate (γ : SL(2, ℤ)) (ℓ p : ℤ) (w y τ : ℝ) : ℝ :=
  (γ 1 0 : ℝ) * (w + y) / fltDenominator (γ : Mat(2, ℤ)) τ + ℓ + p - 1

/-- At a real period with real parameters, membership in the convergence strip is
`0 < λ` and `μ < 0` for the upper and lower decay rates. -/
theorem mem_fiveTermParameterStrip_ofReal_iff (γ : SL(2, ℤ)) (ℓ p : ℤ) (w y τ : ℝ) :
    (w : ℂ) ∈ fiveTermParameterStrip γ ℓ p y τ ↔
      0 < fiveTermUpperRate γ ℓ w τ ∧ fiveTermLowerRate γ ℓ p w y τ < 0 := by
  simp [mem_fiveTermParameterStrip, fiveTermUpperRate, fiveTermLowerRate,
    ← ofReal_fltDenominator]

/-! ### Translation into the residue region

Translation by `t i ε` preserves the strip because the coefficient `c` is real, while it
increases the two residue-series imaginary parts by `t Re ε` and `t`, respectively. -/

/-- Translation by `t i ε` preserves `Re(cz/ε)` for integral `c`; used by
`mem_fiveTermParameterStrip_vertical_shift`. -/
private lemma fiveTerm_vertical_re (c : ℤ) (z ε : ℂ) (t : ℝ) (hε : ε ≠ 0) :
    (((c : ℂ) * (z + (t : ℂ) * ε * I) / ε)).re =
      (((c : ℂ) * z / ε)).re := by
  have h : (c : ℂ) * (z + (t : ℂ) * ε * I) / ε =
      (c : ℂ) * z / ε + ((c : ℂ) * t) * I := by
    field_simp
  rw [h, add_re]
  simp

/-- A vertical translation by `t i ε` preserves both strip inequalities; used by
`exists_mem_fiveTermParameterStrip_im_pos`. -/
private lemma mem_fiveTermParameterStrip_vertical_shift
    (γ : SL(2, ℤ)) (ℓ p : ℤ) (y τ w : ℂ)
    (hε : fltDenominator (γ : Mat(2, ℤ)) τ ≠ 0)
    (hw : w ∈ fiveTermParameterStrip γ ℓ p y τ) (t : ℝ) :
    w + (t : ℂ) * fltDenominator (γ : Mat(2, ℤ)) τ * I ∈
      fiveTermParameterStrip γ ℓ p y τ := by
  obtain ⟨h₁, h₂⟩ := (mem_fiveTermParameterStrip γ ℓ p y τ w).mp hw
  apply (mem_fiveTermParameterStrip γ ℓ p y τ _).mpr
  constructor
  · simpa only [Complex.add_re, fiveTerm_vertical_re _ w _ t hε] using h₁
  · have hz : (w + (t : ℂ) * fltDenominator (γ : Mat(2, ℤ)) τ * I) + y =
        (w + y) + (t : ℂ) * fltDenominator (γ : Mat(2, ℤ)) τ * I := by abel
    rw [hz]
    simpa only [Complex.add_re, Complex.sub_re,
      fiveTerm_vertical_re _ (w + y) _ t hε] using h₂

/-- A vertical translation by `t i ε` adds `t Re ε` to the imaginary part; used by
`exists_mem_fiveTermParameterStrip_im_pos`. -/
private lemma fiveTerm_vertical_im (z ε : ℂ) (t : ℝ) :
    (z + (t : ℂ) * ε * I).im = z.im + t * ε.re := by
  simp [add_im, mul_im, mul_re]

/-- After division by nonzero `ε`, a vertical translation by `t i ε` adds `t` to the
imaginary part; used by `exists_mem_fiveTermParameterStrip_im_pos`. -/
private lemma fiveTerm_vertical_im_div (z ε : ℂ) (t : ℝ) (hε : ε ≠ 0) :
    ((z + (t : ℂ) * ε * I) / ε).im = (z / ε).im + t := by
  have h : (z + (t : ℂ) * ε * I) / ε = z / ε + (t : ℂ) * I := by
    field_simp
  rw [h, add_im]
  simp

/-- One real shift makes both affine imaginary-part bounds positive; used by
`exists_mem_fiveTermParameterStrip_im_pos`. -/
private lemma exists_fiveTerm_positive_shift (r A B : ℝ) (hr : 0 < r) :
    ∃ t : ℝ, 0 < A + t * r ∧ 0 < B + t := by
  let t : ℝ := max (-A / r) (-B) + 1
  have htA : -A / r < t := by
    dsimp [t]
    linarith [le_max_left (-A / r) (-B)]
  have htB : -B < t := by
    dsimp [t]
    linarith [le_max_right (-A / r) (-B)]
  refine ⟨t, ?_, by linarith⟩
  have ht := (div_lt_iff₀ hr).mp htA
  linarith

/-- If `Re ε > 0`, every point of the convergence strip can be translated within the strip
to a point with `Im(ℓτ+v) > 0` and `Im((y+v)/ε) > 0`, where `ε = cτ+d`. This is the
parameter geometry used in [RW26, Radchenko, Wheeler (2026), Appendix A.2,
`app:mod.fad`]. -/
theorem exists_mem_fiveTermParameterStrip_im_pos
    (γ : SL(2, ℤ)) (ℓ p : ℤ) (y τ w : ℂ)
    (he : 0 < (fltDenominator (γ : Mat(2, ℤ)) τ).re)
    (hw : w ∈ fiveTermParameterStrip γ ℓ p y τ) :
    ∃ v ∈ fiveTermParameterStrip γ ℓ p y τ,
      0 < ((ℓ : ℂ) * τ + v).im ∧
      0 < ((y + v) / fltDenominator (γ : Mat(2, ℤ)) τ).im := by
  let ε := fltDenominator (γ : Mat(2, ℤ)) τ
  have he' : 0 < ε.re := he
  have hε : ε ≠ 0 := Complex.ne_zero_of_re_pos he'
  obtain ⟨t, hA, hB⟩ := exists_fiveTerm_positive_shift ε.re
    (((ℓ : ℂ) * τ + w).im) (((y + w) / ε).im) he'
  refine ⟨w + (t : ℂ) * ε * I,
    mem_fiveTermParameterStrip_vertical_shift γ ℓ p y τ w hε hw t, ?_, ?_⟩
  · simpa only [show (ℓ : ℂ) * τ + (w + (t : ℂ) * ε * I) =
        ((ℓ : ℂ) * τ + w) + (t : ℂ) * ε * I from by abel,
      fiveTerm_vertical_im] using hA
  · change 0 < ((y + (w + (t : ℂ) * ε * I)) / ε).im
    rw [show y + (w + (t : ℂ) * ε * I) =
      (y + w) + (t : ℂ) * ε * I from by abel]
    rw [fiveTerm_vertical_im_div (y + w) ε t hε]
    exact hB

end SIC
