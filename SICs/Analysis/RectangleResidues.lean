/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import SICs.Analysis.PuncturedNeighborhood

/-!
# The residue theorem on rectangles

Boundary integrals over a rectangle of a function with finitely many simple poles inside and
finitely many removable singularities.

A function complex differentiable on a closed rectangle except at finitely many interior points
`s`, where `(ζ - s) f(ζ) → R_s`, has counterclockwise boundary integral `2πi ∑ R_s`. This is
the classical residue theorem (L. V. Ahlfors, *Complex Analysis*, 3rd ed., McGraw–Hill (1979),
Chapter 4, Section 5.1, Theorem 17) for a rectangle, the contour shape of Mathlib's
Cauchy–Goursat theorem. It supplies the contour closing in the residue calculation of
[RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`].

## The argument

For one point `s` of the open rectangle, `(ζ - s)⁻¹` has an explicit primitive on each side:
the principal logarithm of `ζ - s` on the bottom, right, and top sides, where `ζ - s` avoids
the closed negative real axis, and the principal logarithm of `s - ζ` on the left side, where
`s - ζ` has positive real part. The four differences telescope to the values at the two left
corners, `log(a) - log(-a)` at the upper-left corner `a` minus `s`, in the open second quadrant,
and `log(-b) - log(b)` at the lower-left corner `b` minus `s`, in the open third quadrant; each
is `πi`. So the boundary integral of `(ζ - s)⁻¹` is `2πi`.

In general, subtract the principal parts: `g(ζ) = f(ζ) - ∑_s R_s (ζ - s)⁻¹` satisfies
`(ζ - s) g(ζ) → 0` at each `s ∈ S`, so its singularities are removable by Riemann's theorem.
The Cauchy–Goursat theorem makes the boundary integral of its continuous extension vanish, and
the extension agrees with `g` on the boundary, which avoids `S`.

Finitely many further points where `f` is bounded and differentiable nearby, anywhere in the
closed rectangle, are removable singularities: replacing the values there by the limits makes
`f` differentiable at them by Riemann's theorem, and changes each side integral only on a finite,
hence null, set of parameters. The kernel of the modular five-term integral has such points on
its contour.
-/

noncomputable section

open Complex Filter Set MeasureTheory
open scoped Interval Topology Real

namespace SIC

/-! ### The boundary integral

The counterclockwise integral over the boundary of a rectangle, in the four-side form of
Mathlib's Cauchy–Goursat theorem. -/

/-- The counterclockwise boundary integral of `f` over the rectangle with lower-left corner `z`
and upper-right corner `w`, with the four sides written as in
`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`. -/
def rectBoundaryIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) -
    (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) -
    I • (∫ y : ℝ in z.im..w.im, f (z.re + y * I))

/-! ### The principal part

The boundary integral of `(ζ - s)⁻¹` is computed from logarithmic primitives, side by side. -/

/-- Evaluates a horizontal inverse integral using the principal logarithm; used by
`bottom_integral` and `top_integral`. -/
private lemma horizontal_log_integral (a b : ℝ) (c : ℂ)
    (h : ∀ x ∈ Set.uIcc a b, (x : ℂ) + c ∈ Complex.slitPlane) :
    (∫ x : ℝ in a..b, ((x : ℂ) + c)⁻¹) =
      Complex.log ((b : ℂ) + c) - Complex.log ((a : ℂ) + c) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    convert (((Complex.hasDerivAt_log (h x hx)).comp (x : ℂ)
      ((hasDerivAt_id (x : ℂ)).add_const c)).comp_ofReal) using 1 <;> simp
  · apply ContinuousOn.intervalIntegrable
    exact ((Complex.continuous_ofReal.continuousOn.add continuousOn_const).inv₀
      (fun x hx => Complex.slitPlane_ne_zero (h x hx)))

/-- Evaluates a vertical inverse integral using the principal logarithm; used by
`right_integral`. -/
private lemma vertical_log_integral (a b : ℝ) (c : ℂ)
    (h : ∀ y ∈ Set.uIcc a b, (y : ℂ) * I + c ∈ Complex.slitPlane) :
    I • (∫ y : ℝ in a..b, ((y : ℂ) * I + c)⁻¹) =
      Complex.log ((b : ℂ) * I + c) - Complex.log ((a : ℂ) * I + c) := by
  rw [← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro y hy
    convert (((Complex.hasDerivAt_log (h y hy)).comp (y : ℂ)
      (((hasDerivAt_id (y : ℂ)).mul_const I).add_const c)).comp_ofReal) using 1
    · rfl
    · change I * (↑y * I + c)⁻¹ = (↑y * I + c)⁻¹ * (1 * I)
      ring
  · exact (Complex.continuous_ofReal.continuousOn.mul continuousOn_const |>.add
      continuousOn_const |>.inv₀ (fun y hy => Complex.slitPlane_ne_zero (h y hy))
      |>.const_smul I).intervalIntegrable

/-- Evaluates a vertical inverse integral with the reversed logarithmic argument; used by
`left_integral`. -/
private lemma vertical_neg_log_integral (a b : ℝ) (c : ℂ)
    (h : ∀ y ∈ Set.uIcc a b, c - (y : ℂ) * I ∈ Complex.slitPlane) :
    I • (∫ y : ℝ in a..b, ((y : ℂ) * I - c)⁻¹) =
      Complex.log (c - (b : ℂ) * I) - Complex.log (c - (a : ℂ) * I) := by
  rw [← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro y hy
    convert (((Complex.hasDerivAt_log (h y hy)).comp (y : ℂ)
      (((hasDerivAt_id (y : ℂ)).mul_const I).const_sub c)).comp_ofReal) using 1
    · rfl
    · change I * ((y : ℂ) * I - c)⁻¹ = (c - (y : ℂ) * I)⁻¹ * ( -(1 * I))
      rw [show ((y : ℂ) * I - c) = -(c - (y : ℂ) * I) by ring, inv_neg]
      ring
  · have hn : ∀ y ∈ uIcc a b, (y : ℂ) * I - c ≠ 0 := by
      intro y hy h0
      apply Complex.slitPlane_ne_zero (h y hy)
      rw [show c - (y : ℂ) * I = -((y : ℂ) * I - c) by ring, h0, neg_zero]
    exact ((Complex.continuous_ofReal.continuousOn.mul continuousOn_const |>.sub
      continuousOn_const |>.inv₀ hn).const_smul I).intervalIntegrable

/-- Evaluates the bottom side of the contour of `integral_boundary_rect_inv_sub`. -/
private lemma bottom_integral (z w s : ℂ) (h₃ : z.im < s.im) :
    (∫ x : ℝ in z.re..w.re, ((x : ℂ) + z.im * I - s)⁻¹) =
      log ((w.re : ℂ) + z.im * I - s) -
        log ((z.re : ℂ) + z.im * I - s) := by
  have h : ∀ x ∈ uIcc z.re w.re, (x : ℂ) + (z.im * I - s) ∈ slitPlane := by
    intro x hx
    apply Complex.mem_slitPlane_iff.mpr
    right
    simp only [add_im, sub_im, ofReal_im, mul_I_im, ofReal_re]
    linarith
  simpa only [sub_eq_add_neg, add_assoc] using
    horizontal_log_integral z.re w.re (z.im * I - s) h

/-- Evaluates the top side of the contour of `integral_boundary_rect_inv_sub`. -/
private lemma top_integral (z w s : ℂ) (h₄ : s.im < w.im) :
    (∫ x : ℝ in z.re..w.re, ((x : ℂ) + w.im * I - s)⁻¹) =
      log ((w.re : ℂ) + w.im * I - s) -
        log ((z.re : ℂ) + w.im * I - s) := by
  have h : ∀ x ∈ uIcc z.re w.re, (x : ℂ) + (w.im * I - s) ∈ slitPlane := by
    intro x hx
    apply Complex.mem_slitPlane_iff.mpr
    right
    simp only [add_im, sub_im, ofReal_im, mul_I_im, ofReal_re]
    linarith
  simpa only [sub_eq_add_neg, add_assoc] using
    horizontal_log_integral z.re w.re (w.im * I - s) h

/-- Evaluates the right side of the contour of `integral_boundary_rect_inv_sub`. -/
private lemma right_integral (z w s : ℂ) (h₂ : s.re < w.re) :
    I • (∫ y : ℝ in z.im..w.im, ((w.re : ℂ) + y * I - s)⁻¹) =
      log ((w.re : ℂ) + w.im * I - s) -
        log ((w.re : ℂ) + z.im * I - s) := by
  have h : ∀ y ∈ uIcc z.im w.im, (y : ℂ) * I + ((w.re : ℂ) - s) ∈ slitPlane := by
    intro y hy
    apply Complex.mem_slitPlane_iff.mpr
    left
    simp only [add_re, sub_re, ofReal_re, mul_I_re, ofReal_im]
    linarith
  simpa only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    vertical_log_integral z.im w.im ((w.re : ℂ) - s) h

/-- Evaluates the left side of the contour of `integral_boundary_rect_inv_sub`. -/
private lemma left_integral (z w s : ℂ) (h₁ : z.re < s.re) :
    I • (∫ y : ℝ in z.im..w.im, ((z.re : ℂ) + y * I - s)⁻¹) =
      log (s - ((z.re : ℂ) + w.im * I)) -
        log (s - ((z.re : ℂ) + z.im * I)) := by
  have h : ∀ y ∈ uIcc z.im w.im, (s - (z.re : ℂ)) - (y : ℂ) * I ∈ slitPlane := by
    intro y hy
    apply Complex.mem_slitPlane_iff.mpr
    left
    simp only [sub_re, mul_I_re, ofReal_re, ofReal_im]
    linarith
  calc
    _ = I • (∫ y : ℝ in z.im..w.im, ((y : ℂ) * I - (s - (z.re : ℂ)))⁻¹) := by
      apply congrArg (fun q : ℝ → ℂ => I • ∫ y in z.im..w.im, q y)
      funext y
      congr 1
      ring
    _ = log ((s - (z.re : ℂ)) - (w.im : ℂ) * I) -
          log ((s - (z.re : ℂ)) - (z.im : ℂ) * I) :=
      vertical_neg_log_integral z.im w.im (s - (z.re : ℂ)) h
    _ = _ := by
      congr 1 <;> congr 1 <;> ring

/-- Computes the logarithmic jump in the upper half-plane; used by
`integral_boundary_rect_inv_sub`. -/
private lemma log_sub_log_neg_of_im_pos (a : ℂ) (h : 0 < a.im) :
    log a - log (-a) = π * I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, Complex.arg_neg_eq_arg_sub_pi_of_im_pos h]

/-- Computes the logarithmic jump in the lower half-plane; used by
`integral_boundary_rect_inv_sub`. -/
private lemma log_neg_sub_log_of_im_neg (b : ℂ) (h : b.im < 0) :
    log (-b) - log b = π * I := by
  simpa using log_sub_log_neg_of_im_pos (-b) (by simpa using h)

/-- The counterclockwise boundary integral of `(ζ - s)⁻¹` over the rectangle with lower-left
corner `z` and upper-right corner `w` is `2πi` when `s` lies in the open rectangle. The
boundary integral is written as in `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`. -/
theorem integral_boundary_rect_inv_sub (z w s : ℂ) (h₁ : z.re < s.re) (h₂ : s.re < w.re)
    (h₃ : z.im < s.im) (h₄ : s.im < w.im) :
    (∫ x : ℝ in z.re..w.re, ((x : ℂ) + z.im * I - s)⁻¹) -
        (∫ x : ℝ in z.re..w.re, ((x : ℂ) + w.im * I - s)⁻¹) +
        I • (∫ y : ℝ in z.im..w.im, ((w.re : ℂ) + y * I - s)⁻¹) -
        I • (∫ y : ℝ in z.im..w.im, ((z.re : ℂ) + y * I - s)⁻¹) =
      2 * π * I := by
  let a : ℂ := (z.re : ℂ) + w.im * I - s
  let b : ℂ := (z.re : ℂ) + z.im * I - s
  have ha : 0 < a.im := by dsimp [a]; simp only [mul_I_im, ofReal_re]; linarith
  have hb : b.im < 0 := by dsimp [b]; simp only [mul_I_im, ofReal_re]; linarith
  rw [bottom_integral z w s h₃, top_integral z w s h₄,
    right_integral z w s h₂, left_integral z w s h₁]
  have hna : s - ((z.re : ℂ) + w.im * I) = -a := by dsimp [a]; ring
  have hnb : s - ((z.re : ℂ) + z.im * I) = -b := by dsimp [b]; ring
  rw [hna, hnb]
  have hlog₁ := log_sub_log_neg_of_im_pos a ha
  have hlog₂ := log_neg_sub_log_of_im_neg b hb
  calc
    _ = (log a - log (-a)) + (log (-b) - log b) := by dsimp [a, b]; ring
    _ = 2 * π * I := by rw [hlog₁, hlog₂]; ring

/-! ### Finitely many simple poles

Subtracting the principal parts leaves removable singularities, and Cauchy–Goursat applies. -/

/-- A finite set is absent near one of its points after puncturing; used by
`remainder_punctured_differentiable`. -/
private lemma eventually_not_mem_finset_punctured (S : Finset ℂ) (s : ℂ) :
    ∀ᶠ ζ in 𝓝[≠] s, ζ ∉ S := by
  have h₁ : (S.erase s : Set ℂ)ᶜ ∈ 𝓝 s :=
    (S.erase s).isClosed.isOpen_compl.mem_nhds (by simp)
  have h₂ : {s}ᶜ ∈ 𝓝[≠] s := self_mem_nhdsWithin
  have h₁e : ∀ᶠ ζ in 𝓝 s, ζ ∉ S.erase s := h₁
  filter_upwards [h₁e.filter_mono nhdsWithin_le_nhds, h₂] with ζ hζ₁ hζ₂
  simp only [mem_compl_iff, mem_singleton_iff] at hζ₂
  exact fun h => hζ₁ (Finset.mem_erase.mpr ⟨hζ₂, h⟩)

/-- The finite sum of principal parts is differentiable away from its poles; used by
`remainder_differentiableAt`. -/
private lemma principal_sum_differentiableAt (S : Finset ℂ) (R : ℂ → ℂ)
    {ζ : ℂ} (hζ : ζ ∉ S) :
    DifferentiableAt ℂ (fun u => ∑ s ∈ S, R s * (u - s)⁻¹) ζ := by
  apply DifferentiableAt.fun_sum
  intro s hs
  have hne : ζ ≠ s := by intro he; exact hζ (he ▸ hs)
  exact (differentiableAt_const _).mul
    ((differentiableAt_id.sub_const s).inv (sub_ne_zero.mpr hne))

/-- The product of the principal-part sum with `ζ - s` tends to `R s`; used by
`remainder_product_tendsto`. -/
private lemma principal_product_tendsto (S : Finset ℂ) (R : ℂ → ℂ)
    (s : ℂ) (hs : s ∈ S) :
    Tendsto (fun ζ => (ζ - s) * ∑ t ∈ S, R t * (ζ - t)⁻¹)
      (𝓝[≠] s) (𝓝 (R s)) := by
  have hrest : ContinuousAt (fun ζ : ℂ => ∑ t ∈ S.erase s, R t * (ζ - t)⁻¹) s :=
    (principal_sum_differentiableAt (S.erase s) R (by simp)).continuousAt
  have hzero : Tendsto (fun ζ : ℂ => (ζ - s) * ∑ t ∈ S.erase s,
      R t * (ζ - t)⁻¹) (𝓝[≠] s) (𝓝 0) := by
    have hc : ContinuousAt (fun ζ : ℂ => (ζ - s) * ∑ t ∈ S.erase s,
        R t * (ζ - t)⁻¹) s := (continuousAt_id.sub_const s).mul hrest
    simpa using hc.mono_left nhdsWithin_le_nhds
  have heq : (fun ζ : ℂ => (ζ - s) * ∑ t ∈ S, R t * (ζ - t)⁻¹) =ᶠ[𝓝[≠] s]
      (fun ζ => R s + (ζ - s) * ∑ t ∈ S.erase s, R t * (ζ - t)⁻¹) := by
    filter_upwards [self_mem_nhdsWithin] with ζ hζ
    rw [← Finset.add_sum_erase S (fun t => R t * (ζ - t)⁻¹) hs]
    have hn : ζ - s ≠ 0 := sub_ne_zero.mpr hζ
    field_simp [hn]
  exact Filter.Tendsto.congr' heq.symm (by simpa using tendsto_const_nhds.add hzero)

/-- The original function after subtracting its finite sum of principal parts; used by
`integral_boundary_rect_eq_sum_residues`. -/
private def residueRemainder (f : ℂ → ℂ) (S : Finset ℂ) (R : ℂ → ℂ) : ℂ → ℂ :=
  fun ζ => f ζ - ∑ t ∈ S, R t * (ζ - t)⁻¹

/-- The pole-cancelled remainder tends to zero after multiplication by `ζ - s`; used by
`remainder_isLittleO`. -/
private lemma remainder_product_tendsto (f : ℂ → ℂ) (S : Finset ℂ) (R : ℂ → ℂ)
    (s : ℂ) (hs : s ∈ S) (hR : Tendsto (fun ζ => (ζ - s) * f ζ) (𝓝[≠] s) (𝓝 (R s))) :
    Tendsto (fun ζ => (ζ - s) * residueRemainder f S R ζ) (𝓝[≠] s) (𝓝 0) := by
  convert hR.sub (principal_product_tendsto S R s hs) using 1
  · funext ζ
    dsimp [residueRemainder]
    ring
  · simp

/-- The remainder satisfies the smallness hypothesis of the removable-singularity theorem;
used by `extension_continuousAt_pole`. -/
private lemma remainder_isLittleO (f : ℂ → ℂ) (S : Finset ℂ) (R : ℂ → ℂ)
    (s : ℂ) (hs : s ∈ S) (hR : Tendsto (fun ζ => (ζ - s) * f ζ) (𝓝[≠] s) (𝓝 (R s))) :
    (fun ζ => residueRemainder f S R ζ - residueRemainder f S R s) =o[𝓝[≠] s]
      fun ζ => (ζ - s)⁻¹ := by
  have hprod := remainder_product_tendsto f S R s hs hR
  have hconst : Tendsto (fun ζ : ℂ => (ζ - s) * residueRemainder f S R s)
      (𝓝[≠] s) (𝓝 0) := by
    have hc : ContinuousAt (fun ζ : ℂ => (ζ - s) * residueRemainder f S R s) s :=
      (continuousAt_id.sub_const s).mul continuousAt_const
    simpa using hc.mono_left nhdsWithin_le_nhds
  have hdiff : Tendsto (fun ζ => (residueRemainder f S R ζ - residueRemainder f S R s) * (ζ - s))
      (𝓝[≠] s) (𝓝 0) := by
    convert hprod.sub hconst using 1
    · funext ζ
      ring
    · simp
  refine (Asymptotics.isLittleO_iff_tendsto' ?_).mpr ?_
  · filter_upwards [self_mem_nhdsWithin] with ζ hζ hz
    exact False.elim ((inv_ne_zero (sub_ne_zero.mpr hζ)) hz)
  · simpa only [div_eq_mul_inv, inv_inv, mul_comm] using hdiff

/-- The remainder is differentiable in the open rectangle away from the poles; used by
`extension_differentiableAt`. -/
private lemma remainder_differentiableAt (f : ℂ → ℂ) (z w : ℂ) (S : Finset ℂ)
    (R : ℂ → ℂ) (hf : DifferentiableOn ℂ f
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]] \ (S : Set ℂ)))
    {ζ : ℂ} (hζ : ζ ∈ Ioo (min z.re w.re) (max z.re w.re) ×ℂ
      Ioo (min z.im w.im) (max z.im w.im) \ (S : Set ℂ)) :
    DifferentiableAt ℂ (residueRemainder f S R) ζ := by
  have hOpen : Ioo (min z.re w.re) (max z.re w.re) ×ℂ
      Ioo (min z.im w.im) (max z.im w.im) ∈ 𝓝 ζ :=
    (isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds hζ.1
  have hClosed : [[z.re, w.re]] ×ℂ [[z.im, w.im]] ∈ 𝓝 ζ :=
    Filter.mem_of_superset hOpen
      (inter_subset_inter (preimage_mono Ioo_subset_Icc_self) (preimage_mono Ioo_subset_Icc_self))
  have hComp : (S : Set ℂ)ᶜ ∈ 𝓝 ζ := S.isClosed.isOpen_compl.mem_nhds hζ.2
  exact (hf.differentiableAt (inter_mem hClosed hComp)).sub
    (principal_sum_differentiableAt S R hζ.2)

/-- The remainder extended at each pole by its punctured limit; used by
`rectBoundaryIntegral_extension_zero`. -/
private def residueExtension (f : ℂ → ℂ) (S : Finset ℂ) (R : ℂ → ℂ) : ℂ → ℂ :=
  fun ζ => if ζ ∈ S then limUnder (𝓝[≠] ζ) (residueRemainder f S R)
    else residueRemainder f S R ζ

/-- The remainder is differentiable on a punctured neighborhood of a pole; used by
`extension_continuousAt_pole`. -/
private lemma remainder_punctured_differentiable (f : ℂ → ℂ) (z w : ℂ)
    (S : Finset ℂ) (R : ℂ → ℂ) (hf : DifferentiableOn ℂ f
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]] \ (S : Set ℂ)))
    (s : ℂ) (hs : s ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im) :
    ∀ᶠ ζ in 𝓝[≠] s, DifferentiableAt ℂ (residueRemainder f S R) ζ := by
  have hr : z.re < w.re := lt_trans hs.1.1 hs.1.2
  have hi : z.im < w.im := lt_trans hs.2.1 hs.2.2
  have hs' : s ∈ Ioo (min z.re w.re) (max z.re w.re) ×ℂ
      Ioo (min z.im w.im) (max z.im w.im) := by
    simpa [min_eq_left hr.le, max_eq_right hr.le,
      min_eq_left hi.le, max_eq_right hi.le] using hs
  have hopen : Ioo (min z.re w.re) (max z.re w.re) ×ℂ
      Ioo (min z.im w.im) (max z.im w.im) ∈ 𝓝 s :=
    (isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds hs'
  have hopen_e : ∀ᶠ ζ in 𝓝 s, ζ ∈ Ioo (min z.re w.re) (max z.re w.re) ×ℂ
      Ioo (min z.im w.im) (max z.im w.im) := hopen
  filter_upwards [hopen_e.filter_mono nhdsWithin_le_nhds,
    eventually_not_mem_finset_punctured S s] with ζ hζ hnot
  exact remainder_differentiableAt f z w S R hf ⟨hζ, hnot⟩

/-- The residue extension is continuous at one pole; used by `extension_continuousOn`. -/
private lemma extension_continuousAt_pole (f : ℂ → ℂ) (z w : ℂ)
    (S : Finset ℂ) (R : ℂ → ℂ) (hf : DifferentiableOn ℂ f
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]] \ (S : Set ℂ)))
    (s : ℂ) (hs : s ∈ S) (hsopen : s ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im)
    (hR : Tendsto (fun ζ => (ζ - s) * f ζ) (𝓝[≠] s) (𝓝 (R s))) :
    ContinuousAt (residueExtension f S R) s := by
  have hlim := Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isLittleO
    (remainder_punctured_differentiable f z w S R hf s hsopen)
    (remainder_isLittleO f S R s hs hR)
  have hupdate : ContinuousAt (Function.update (residueRemainder f S R) s
      (limUnder (𝓝[≠] s) (residueRemainder f S R))) s :=
    continuousAt_update_same.mpr hlim
  apply hupdate.congr_of_eventuallyEq
  have hnear : (S.erase s : Set ℂ)ᶜ ∈ 𝓝 s :=
    (S.erase s).isClosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [hnear] with ζ hζ
  by_cases hEq : ζ = s
  · subst ζ
    simp [residueExtension, hs]
  · have hn : ζ ∉ S := by
      intro hz
      exact hζ (Finset.mem_erase.mpr ⟨hEq, hz⟩)
    simp [residueExtension, hn, hEq]

/-- The residue extension is continuous on the closed rectangle; used by
`rectBoundaryIntegral_extension_zero`. -/
private lemma extension_continuousOn (f : ℂ → ℂ) (z w : ℂ)
    (S : Finset ℂ) (R : ℂ → ℂ)
    (hS : ∀ s ∈ S, s ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im)
    (hf : DifferentiableOn ℂ f ([[z.re, w.re]] ×ℂ [[z.im, w.im]] \ (S : Set ℂ)))
    (hR : ∀ s ∈ S, Tendsto (fun ζ => (ζ - s) * f ζ) (𝓝[≠] s) (𝓝 (R s))) :
    ContinuousOn (residueExtension f S R) ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) := by
  intro ζ hζ
  by_cases hp : ζ ∈ S
  · exact (extension_continuousAt_pole f z w S R hf ζ hp (hS ζ hp) (hR ζ hp)).continuousWithinAt
  · have hcomp : (S : Set ℂ)ᶜ ∈ 𝓝 ζ := S.isClosed.isOpen_compl.mem_nhds hp
    have hcomp_e : ∀ᶠ u in 𝓝 ζ, u ∉ S := hcomp
    have hcomp_within : (S : Set ℂ)ᶜ ∈ 𝓝[([[z.re, w.re]] ×ℂ [[z.im, w.im]])] ζ :=
      hcomp_e.filter_mono nhdsWithin_le_nhds
    have hfilter : 𝓝[([[z.re, w.re]] ×ℂ [[z.im, w.im]]) \ (S : Set ℂ)] ζ =
        𝓝[([[z.re, w.re]] ×ℂ [[z.im, w.im]])] ζ := by
      simpa only [sdiff_eq] using nhdsWithin_inter_of_mem' hcomp_within
    have hg : ContinuousWithinAt (residueRemainder f S R)
        ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) ζ := by
      change Tendsto (residueRemainder f S R)
        (𝓝[([[z.re, w.re]] ×ℂ [[z.im, w.im]])] ζ)
        (𝓝 (residueRemainder f S R ζ))
      rw [← hfilter]
      exact (hf.continuousOn ζ ⟨hζ, hp⟩).sub
        (principal_sum_differentiableAt S R hp).continuousAt.continuousWithinAt
    apply hg.congr_of_eventuallyEq_of_mem _ hζ
    filter_upwards [hcomp_within] with u hu
    have hun : u ∉ S := hu
    simp [residueExtension, hun]

/-- The residue extension is differentiable away from the poles; used by
`rectBoundaryIntegral_extension_zero`. -/
private lemma extension_differentiableAt (f : ℂ → ℂ) (z w : ℂ)
    (S : Finset ℂ) (R : ℂ → ℂ) (hf : DifferentiableOn ℂ f
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]] \ (S : Set ℂ)))
    {ζ : ℂ} (hζ : ζ ∈ Ioo (min z.re w.re) (max z.re w.re) ×ℂ
      Ioo (min z.im w.im) (max z.im w.im) \ (S : Set ℂ)) :
    DifferentiableAt ℂ (residueExtension f S R) ζ := by
  apply (remainder_differentiableAt f z w S R hf hζ).congr_of_eventuallyEq
  have hcomp : (S : Set ℂ)ᶜ ∈ 𝓝 ζ := S.isClosed.isOpen_compl.mem_nhds hζ.2
  filter_upwards [hcomp] with u hu
  have hun : u ∉ S := hu
  simp [residueExtension, hun]

/-- Continuity off the poles makes a horizontal side integrable; used by
`boundary_side_integrable`. -/
private lemma horizontal_integrable (f : ℂ → ℂ) (z w : ℂ) (S : Finset ℂ)
    (y : ℝ) (hy : y ∈ uIcc z.im w.im) (hno : ∀ s ∈ S, s.im ≠ y)
    (hc : ContinuousOn f ([[z.re, w.re]] ×ℂ [[z.im, w.im]] \ (S : Set ℂ))) :
    IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + y * I)) volume z.re w.re := by
  apply ContinuousOn.intervalIntegrable
  apply hc.comp
  · exact (Complex.continuous_ofReal.add continuous_const).continuousOn
  · intro x hx
    constructor
    · simpa only [mem_reProdIm, add_re, add_im, ofReal_re, ofReal_im,
        mul_I_re, mul_I_im, zero_add, add_zero, neg_zero] using And.intro hx hy
    · intro hmem
      exact (hno _ hmem) (by simp)

/-- Continuity off the poles makes a vertical side integrable; used by
`boundary_side_integrable`. -/
private lemma vertical_integrable (f : ℂ → ℂ) (z w : ℂ) (S : Finset ℂ)
    (x : ℝ) (hx : x ∈ uIcc z.re w.re) (hno : ∀ s ∈ S, s.re ≠ x)
    (hc : ContinuousOn f ([[z.re, w.re]] ×ℂ [[z.im, w.im]] \ (S : Set ℂ))) :
    IntervalIntegrable (fun y : ℝ => f ((x : ℂ) + y * I)) volume z.im w.im := by
  apply ContinuousOn.intervalIntegrable
  apply hc.comp
  · exact (Complex.continuous_ofReal.mul continuous_const |>.const_add _).continuousOn
  · intro y hy
    constructor
    · simpa only [mem_reProdIm, add_re, add_im, ofReal_re, ofReal_im,
        mul_I_re, mul_I_im, zero_add, add_zero, neg_zero] using And.intro hx hy
    · intro hmem
      exact (hno _ hmem) (by simp)

/-- All four contour sides are integrable when the poles lie in the open rectangle; used by
`integral_boundary_rect_eq_sum_residues`. -/
private lemma boundary_side_integrable (f : ℂ → ℂ) (z w : ℂ) (S : Finset ℂ)
    (hS : ∀ s ∈ S, s ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im)
    (hc : ContinuousOn f ([[z.re, w.re]] ×ℂ [[z.im, w.im]] \ (S : Set ℂ))) :
    IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + z.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + w.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun y : ℝ => f ((w.re : ℂ) + y * I)) volume z.im w.im ∧
    IntervalIntegrable (fun y : ℝ => f ((z.re : ℂ) + y * I)) volume z.im w.im := by
  have hb : ∀ s ∈ S, s.im ≠ z.im := fun s hs => ne_of_gt (hS s hs).2.1
  have ht : ∀ s ∈ S, s.im ≠ w.im := fun s hs => ne_of_lt (hS s hs).2.2
  have hr : ∀ s ∈ S, s.re ≠ w.re := fun s hs => ne_of_lt (hS s hs).1.2
  have hl : ∀ s ∈ S, s.re ≠ z.re := fun s hs => ne_of_gt (hS s hs).1.1
  exact ⟨horizontal_integrable f z w S z.im left_mem_uIcc hb hc,
    horizontal_integrable f z w S w.im right_mem_uIcc ht hc,
    vertical_integrable f z w S w.re right_mem_uIcc hr hc,
    vertical_integrable f z w S z.re left_mem_uIcc hl hc⟩

/-- The four interval-integrability conditions used by `rectBoundaryIntegral_sub` and
`rectBoundaryIntegral_finsetSum`. -/
private def rectSideIntegrable (z w : ℂ) (f : ℂ → ℂ) : Prop :=
  IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + z.im * I)) volume z.re w.re ∧
  IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + w.im * I)) volume z.re w.re ∧
  IntervalIntegrable (fun y : ℝ => f ((w.re : ℂ) + y * I)) volume z.im w.im ∧
  IntervalIntegrable (fun y : ℝ => f ((z.re : ℂ) + y * I)) volume z.im w.im

/-- The rectangle boundary integral distributes over subtraction; used by
`integral_boundary_rect_eq_sum_residues`. -/
private lemma rectBoundaryIntegral_sub (z w : ℂ) (f g : ℂ → ℂ)
    (hf : rectSideIntegrable z w f) (hg : rectSideIntegrable z w g) :
    rectBoundaryIntegral (fun ζ => f ζ - g ζ) z w =
      rectBoundaryIntegral f z w - rectBoundaryIntegral g z w := by
  rcases hf with ⟨hf₁, hf₂, hf₃, hf₄⟩
  rcases hg with ⟨hg₁, hg₂, hg₃, hg₄⟩
  unfold rectBoundaryIntegral
  simp only [intervalIntegral.integral_sub hf₁ hg₁, intervalIntegral.integral_sub hf₂ hg₂,
    intervalIntegral.integral_sub hf₃ hg₃, intervalIntegral.integral_sub hf₄ hg₄, smul_sub]
  abel

/-- The rectangle boundary integral distributes over a finite sum; used by
`rectBoundaryIntegral_principal_sum`. -/
private lemma rectBoundaryIntegral_finsetSum (z w : ℂ) (S : Finset ℂ) (F : ℂ → ℂ → ℂ)
    (h : ∀ s ∈ S, rectSideIntegrable z w (F s)) :
    rectBoundaryIntegral (fun ζ => ∑ s ∈ S, F s ζ) z w =
      ∑ s ∈ S, rectBoundaryIntegral (F s) z w := by
  have h₁ : ∀ s ∈ S, IntervalIntegrable (fun x : ℝ => F s (x + z.im * I)) volume z.re w.re :=
    fun s hs => (h s hs).1
  have h₂ : ∀ s ∈ S, IntervalIntegrable (fun x : ℝ => F s (x + w.im * I)) volume z.re w.re :=
    fun s hs => (h s hs).2.1
  have h₃ : ∀ s ∈ S, IntervalIntegrable (fun y : ℝ => F s (w.re + y * I)) volume z.im w.im :=
    fun s hs => (h s hs).2.2.1
  have h₄ : ∀ s ∈ S, IntervalIntegrable (fun y : ℝ => F s (z.re + y * I)) volume z.im w.im :=
    fun s hs => (h s hs).2.2.2
  unfold rectBoundaryIntegral
  simp only [intervalIntegral.integral_finsetSum h₁, intervalIntegral.integral_finsetSum h₂,
    intervalIntegral.integral_finsetSum h₃, intervalIntegral.integral_finsetSum h₄,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.smul_sum]

/-- A scalar multiple of one principal part contributes its scalar times `2πi`; used by
`rectBoundaryIntegral_principal_sum`. -/
private lemma rectBoundaryIntegral_principal_term (z w s R : ℂ)
    (h₁ : z.re < s.re) (h₂ : s.re < w.re)
    (h₃ : z.im < s.im) (h₄ : s.im < w.im) :
    rectBoundaryIntegral (fun ζ => R * (ζ - s)⁻¹) z w = R * (2 * π * I) := by
  have h := integral_boundary_rect_inv_sub z w s h₁ h₂ h₃ h₄
  unfold rectBoundaryIntegral
  simp only [intervalIntegral.integral_const_mul, smul_eq_mul]
  calc
    _ = R * ((∫ x : ℝ in z.re..w.re, ((x : ℂ) + z.im * I - s)⁻¹) -
        (∫ x : ℝ in z.re..w.re, ((x : ℂ) + w.im * I - s)⁻¹) +
        I * (∫ y : ℝ in z.im..w.im, ((w.re : ℂ) + y * I - s)⁻¹) -
        I * (∫ y : ℝ in z.im..w.im, ((z.re : ℂ) + y * I - s)⁻¹)) := by ring
    _ = _ := by simp only [smul_eq_mul] at h; rw [h]

/-- A principal part is continuous on the rectangle away from the poles; used by
`rectBoundaryIntegral_principal_sum`. -/
private lemma principal_term_continuousOn (z w : ℂ) (S : Finset ℂ)
    (R : ℂ → ℂ) (s : ℂ) (hs : s ∈ S) :
    ContinuousOn (fun ζ => R s * (ζ - s)⁻¹)
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]] \ (S : Set ℂ)) := by
  intro ζ hζ
  have hne : ζ ≠ s := by intro he; exact hζ.2 (he ▸ hs)
  exact (continuousAt_const.mul
    ((continuousAt_id.sub_const s).inv₀ (sub_ne_zero.mpr hne))).continuousWithinAt

/-- The finite principal-part sum has boundary integral `2πi` times the residue sum; used by
`integral_boundary_rect_eq_sum_residues`. -/
private lemma rectBoundaryIntegral_principal_sum (z w : ℂ) (S : Finset ℂ) (R : ℂ → ℂ)
    (hS : ∀ s ∈ S, s ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im) :
    rectBoundaryIntegral (fun ζ => ∑ s ∈ S, R s * (ζ - s)⁻¹) z w =
      2 * π * I * ∑ s ∈ S, R s := by
  have hterm : ∀ s ∈ S, rectSideIntegrable z w (fun ζ => R s * (ζ - s)⁻¹) := by
    intro s hs
    exact boundary_side_integrable (fun ζ => R s * (ζ - s)⁻¹) z w S hS
      (principal_term_continuousOn z w S R s hs)
  calc
    _ = ∑ s ∈ S, rectBoundaryIntegral (fun ζ => R s * (ζ - s)⁻¹) z w :=
      rectBoundaryIntegral_finsetSum z w S (fun s ζ => R s * (ζ - s)⁻¹) hterm
    _ = ∑ s ∈ S, R s * (2 * π * I) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact rectBoundaryIntegral_principal_term z w s (R s)
        (hS s hs).1.1 (hS s hs).1.2 (hS s hs).2.1 (hS s hs).2.2
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- Each side of the rectangle avoids every interior pole; used by
`rectBoundaryIntegral_extension_eq_remainder`. -/
private lemma boundary_avoids_poles (z w : ℂ) (S : Finset ℂ)
    (hS : ∀ s ∈ S, s ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im) :
    (∀ x : ℝ, (x : ℂ) + z.im * I ∉ S) ∧
    (∀ x : ℝ, (x : ℂ) + w.im * I ∉ S) ∧
    (∀ y : ℝ, (w.re : ℂ) + y * I ∉ S) ∧
    (∀ y : ℝ, (z.re : ℂ) + y * I ∉ S) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    have h := (hS _ hx).2.1
    simp only [add_im, ofReal_im, mul_I_im, ofReal_re, zero_add] at h
    exact (lt_irrefl _) h
  · intro x hx
    have h := (hS _ hx).2.2
    simp only [add_im, ofReal_im, mul_I_im, ofReal_re, zero_add] at h
    exact (lt_irrefl _) h
  · intro y hy
    have h := (hS _ hy).1.2
    simp only [add_re, ofReal_re, mul_I_re, ofReal_im, add_zero, neg_zero] at h
    exact (lt_irrefl _) h
  · intro y hy
    have h := (hS _ hy).1.1
    simp only [add_re, ofReal_re, mul_I_re, ofReal_im, add_zero, neg_zero] at h
    exact (lt_irrefl _) h

/-- The extension and remainder have the same boundary integral; used by
`integral_boundary_rect_eq_sum_residues`. -/
private lemma rectBoundaryIntegral_extension_eq_remainder (f : ℂ → ℂ) (z w : ℂ)
    (S : Finset ℂ) (R : ℂ → ℂ)
    (hS : ∀ s ∈ S, s ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im) :
    rectBoundaryIntegral (residueExtension f S R) z w =
      rectBoundaryIntegral (residueRemainder f S R) z w := by
  obtain ⟨hb, ht, hr, hl⟩ := boundary_avoids_poles z w S hS
  unfold rectBoundaryIntegral
  simp only [residueExtension, hb, ht, hr, hl, ite_false]

/-- Cauchy–Goursat gives zero boundary integral for the extended remainder; used by
`integral_boundary_rect_eq_sum_residues`. -/
private lemma rectBoundaryIntegral_extension_zero (f : ℂ → ℂ) (z w : ℂ)
    (S : Finset ℂ) (R : ℂ → ℂ)
    (hS : ∀ s ∈ S, s ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im)
    (hf : DifferentiableOn ℂ f ([[z.re, w.re]] ×ℂ [[z.im, w.im]] \ (S : Set ℂ)))
    (hR : ∀ s ∈ S, Tendsto (fun ζ => (ζ - s) * f ζ) (𝓝[≠] s) (𝓝 (R s))) :
    rectBoundaryIntegral (residueExtension f S R) z w = 0 := by
  exact Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
    (residueExtension f S R) z w (S : Set ℂ) S.finite_toSet.countable
    (extension_continuousOn f z w S R hS hf hR)
    (fun ζ hζ => extension_differentiableAt f z w S R hf hζ)

/-- **The residue theorem on a rectangle.** Let `S` be a finite set of points of the open
rectangle with lower-left corner `z` and upper-right corner `w`, and let `f` be complex
differentiable on the closed rectangle minus `S`, with `(ζ - s) f(ζ) → R s` as `ζ → s` for each
`s ∈ S`. Then the counterclockwise boundary integral of `f`, written as in
`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`, is `2πi ∑_{s ∈ S} R s`. -/
theorem integral_boundary_rect_eq_sum_residues (f : ℂ → ℂ) (z w : ℂ) (S : Finset ℂ)
    (R : ℂ → ℂ) (hS : ∀ s ∈ S, z.re < s.re ∧ s.re < w.re ∧ z.im < s.im ∧ s.im < w.im)
    (hf : DifferentiableOn ℂ f ([[z.re, w.re]] ×ℂ [[z.im, w.im]] \ (S : Set ℂ)))
    (hR : ∀ s ∈ S, Tendsto (fun ζ => (ζ - s) * f ζ) (𝓝[≠] s) (𝓝 (R s))) :
    (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
        I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) -
        I • (∫ y : ℝ in z.im..w.im, f (z.re + y * I)) =
      2 * π * I * ∑ s ∈ S, R s := by
  have hSopen : ∀ s ∈ S, s ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im := by
    intro s hs
    rcases hS s hs with ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
  have hPcont : ContinuousOn (fun ζ => ∑ s ∈ S, R s * (ζ - s)⁻¹)
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]] \ (S : Set ℂ)) :=
    fun ζ hζ => (principal_sum_differentiableAt S R hζ.2).continuousAt.continuousWithinAt
  have hFint : rectSideIntegrable z w f :=
    boundary_side_integrable f z w S hSopen hf.continuousOn
  have hPint : rectSideIntegrable z w (fun ζ => ∑ s ∈ S, R s * (ζ - s)⁻¹) :=
    boundary_side_integrable _ z w S hSopen hPcont
  have hSub : rectBoundaryIntegral (residueRemainder f S R) z w = rectBoundaryIntegral f z w -
      rectBoundaryIntegral (fun ζ => ∑ s ∈ S, R s * (ζ - s)⁻¹) z w :=
    rectBoundaryIntegral_sub z w f _ hFint hPint
  have hZero := rectBoundaryIntegral_extension_zero f z w S R hSopen hf hR
  have hEq := rectBoundaryIntegral_extension_eq_remainder f z w S R hSopen
  have hBoundaryF : rectBoundaryIntegral f z w =
      rectBoundaryIntegral (fun ζ => ∑ s ∈ S, R s * (ζ - s)⁻¹) z w :=
    sub_eq_zero.mp (hSub ▸ (hEq ▸ hZero))
  exact hBoundaryF.trans (rectBoundaryIntegral_principal_sum z w S R hSopen)

/-! ### Removable singularities on the rectangle and its boundary

Filling finitely many punctured limits leaves the contour integral unchanged. -/

/-- Replaces the values at `E` by their punctured limits; used by
`integral_boundary_rect_eq_sum_residues_of_bounded`. -/
private def removableExtension (f : ℂ → ℂ) (E : Finset ℂ) : ℂ → ℂ :=
  fun ζ => if ζ ∈ E then limUnder (𝓝[≠] ζ) f else f ζ

/-- The removable extension equals the original function off `E`; used by
`removableExtension_eventuallyEq` and `rectBoundaryIntegral_removableExtension`. -/
private lemma removableExtension_eq_of_not_mem (f : ℂ → ℂ) (E : Finset ℂ)
    {ζ : ℂ} (hζ : ζ ∉ E) : removableExtension f E ζ = f ζ := by
  simp [removableExtension, hζ]

/-- Off `E`, the removable extension agrees with the original function nearby; used by
`removableExtension_differentiableAt_mem`, `removableExtension_differentiableOn`, and
`integral_boundary_rect_eq_sum_residues_of_bounded`. -/
private lemma removableExtension_eventuallyEq (f : ℂ → ℂ) (E : Finset ℂ)
    {ζ : ℂ} (hζ : ζ ∉ E) : removableExtension f E =ᶠ[𝓝 ζ] f := by
  have hnear : (E : Set ℂ)ᶜ ∈ 𝓝 ζ := E.isClosed.isOpen_compl.mem_nhds hζ
  filter_upwards [hnear] with u hu
  exact removableExtension_eq_of_not_mem f E hu

/-- Boundedness of `f` gives the bound required by Riemann's theorem at `e`; used by
`removableExtension_continuousAt_mem`. -/
private lemma removableExtension_bounded_sub (f : ℂ → ℂ) (e : ℂ)
    (hb : IsBoundedUnder (· ≤ ·) (𝓝[≠] e) fun ζ => ‖f ζ‖) :
    IsBoundedUnder (· ≤ ·) (𝓝[≠] e) fun ζ => ‖f ζ - f e‖ := by
  obtain ⟨B, hB⟩ := hb
  refine ⟨B + ‖f e‖, ?_⟩
  have hB' : ∀ᶠ ζ in 𝓝[≠] e, ‖f ζ‖ ≤ B := hB
  change ∀ᶠ ζ in 𝓝[≠] e, ‖f ζ - f e‖ ≤ B + ‖f e‖
  filter_upwards [hB'] with ζ hζ
  exact (norm_sub_le (f ζ) (f e)).trans (by gcongr)

/-- The filled value is continuous at a removable point; used by
`removableExtension_differentiableAt_mem`. -/
private lemma removableExtension_continuousAt_mem (f : ℂ → ℂ) (E : Finset ℂ)
    (e : ℂ) (he : e ∈ E)
    (hd : ∀ᶠ ζ in 𝓝[≠] e, DifferentiableAt ℂ f ζ)
    (hb : IsBoundedUnder (· ≤ ·) (𝓝[≠] e) fun ζ => ‖f ζ‖) :
    ContinuousAt (removableExtension f E) e := by
  have hlim := Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under
    hd (removableExtension_bounded_sub f e hb)
  have hu : ContinuousAt (Function.update f e ((𝓝[≠] e).limUnder f)) e :=
    continuousAt_update_same.mpr hlim
  apply hu.congr_of_eventuallyEq
  have hnear : (E.erase e : Set ℂ)ᶜ ∈ 𝓝 e :=
    (E.erase e).isClosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [hnear] with ζ hζ
  by_cases hEq : ζ = e
  · subst ζ
    simp [removableExtension, he]
  · have hn : ζ ∉ E := by
      intro hz
      exact hζ (Finset.mem_erase.mpr ⟨hEq, hz⟩)
    simp [removableExtension, hn, hEq]

/-- Riemann's theorem makes the filled function differentiable at `e`; used by
`removableExtension_differentiableOn`. -/
private lemma removableExtension_differentiableAt_mem (f : ℂ → ℂ) (E : Finset ℂ)
    (e : ℂ) (he : e ∈ E)
    (hd : ∀ᶠ ζ in 𝓝[≠] e, DifferentiableAt ℂ f ζ)
    (hb : IsBoundedUnder (· ≤ ·) (𝓝[≠] e) fun ζ => ‖f ζ‖) :
    DifferentiableAt ℂ (removableExtension f E) e := by
  have hdiff : ∀ᶠ ζ in 𝓝[≠] e, DifferentiableAt ℂ (removableExtension f E) ζ := by
    filter_upwards [hd, eventually_not_mem_finset_punctured E e] with ζ hζ hnot
    exact hζ.congr_of_eventuallyEq (removableExtension_eventuallyEq f E hnot)
  exact (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    hdiff (removableExtension_continuousAt_mem f E e he hd hb)).differentiableAt

/-- Away from `E`, differentiation on the punctured rectangle survives filling `E`; used by
`removableExtension_differentiableOn`. -/
private lemma removableExtension_differentiableWithinAt_off (f : ℂ → ℂ)
    (A : Set ℂ) (S E : Finset ℂ) (hf : DifferentiableOn ℂ f (A \ ((S : Set ℂ) ∪ E)))
    {ζ : ℂ} (hζ : ζ ∈ A \ (S : Set ℂ)) (hnot : ζ ∉ E) :
    DifferentiableWithinAt ℂ (removableExtension f E) (A \ (S : Set ℂ)) ζ := by
  have hnear : (E : Set ℂ)ᶜ ∈ 𝓝 ζ := E.isClosed.isOpen_compl.mem_nhds hnot
  have hmem : ζ ∈ A \ ((S : Set ℂ) ∪ E) := ⟨hζ.1, by simp [hζ.2, hnot]⟩
  have hfd : DifferentiableWithinAt ℂ f ((A \ (S : Set ℂ)) ∩ (E : Set ℂ)ᶜ) ζ := by
    simpa only [sdiff_eq, compl_union, inter_assoc] using hf ζ hmem
  have hfd' : DifferentiableWithinAt ℂ f (A \ (S : Set ℂ)) ζ :=
    (differentiableWithinAt_inter hnear).mp hfd
  exact hfd'.congr_of_eventuallyEq
    ((removableExtension_eventuallyEq f E hnot).filter_mono nhdsWithin_le_nhds)
    (removableExtension_eq_of_not_mem f E hnot)

/-- Filling finitely many removable points makes the function differentiable on the closed
rectangle minus the poles; used by `integral_boundary_rect_eq_sum_residues_of_bounded`. -/
private lemma removableExtension_differentiableOn (f : ℂ → ℂ) (A : Set ℂ)
    (S E : Finset ℂ) (hf : DifferentiableOn ℂ f (A \ ((S : Set ℂ) ∪ E)))
    (hd : ∀ e ∈ E, ∀ᶠ ζ in 𝓝[≠] e, DifferentiableAt ℂ f ζ)
    (hb : ∀ e ∈ E, IsBoundedUnder (· ≤ ·) (𝓝[≠] e) fun ζ => ‖f ζ‖) :
    DifferentiableOn ℂ (removableExtension f E) (A \ (S : Set ℂ)) := by
  intro ζ hζ
  by_cases he : ζ ∈ E
  · exact (removableExtension_differentiableAt_mem f E ζ he
      (hd ζ he) (hb ζ he)).differentiableWithinAt
  · exact removableExtension_differentiableWithinAt_off f A S E hf hζ he

/-- Changing a function at finitely many points does not change its integral along an
injectively parametrized side; used by `rectBoundaryIntegral_removableExtension`. -/
private lemma intervalIntegral_congr_off_finset (f g : ℂ → ℂ) (E : Finset ℂ)
    (φ : ℝ → ℂ) (hφ : Function.Injective φ) (hfg : ∀ ζ ∉ E, f ζ = g ζ) (a b : ℝ) :
    (∫ x : ℝ in a..b, f (φ x)) = ∫ x : ℝ in a..b, g (φ x) := by
  have hfinite : (φ ⁻¹' (E : Set ℂ)).Finite :=
    E.finite_toSet.preimage (fun _ _ _ _ h => hφ h)
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hfinite.countable.ae_notMem (volume : Measure ℝ)] with x hx _
  exact hfg (φ x) hx

/-- Filling finitely many values leaves the four sides of the rectangle unchanged; used by
`integral_boundary_rect_eq_sum_residues_of_bounded`. -/
private lemma rectBoundaryIntegral_removableExtension (f : ℂ → ℂ) (z w : ℂ) (E : Finset ℂ) :
    rectBoundaryIntegral (removableExtension f E) z w = rectBoundaryIntegral f z w := by
  have hH (c : ℂ) : Function.Injective (fun x : ℝ => (x : ℂ) + c) := by
    intro x y h
    have h' := congrArg Complex.re h
    simpa using h'
  have hV (c : ℝ) : Function.Injective (fun y : ℝ => (c : ℂ) + y * I) := by
    intro x y h
    have h' := congrArg Complex.im h
    simpa using h'
  have hfg : ∀ ζ ∉ E, removableExtension f E ζ = f ζ :=
    fun _ hζ => removableExtension_eq_of_not_mem f E hζ
  unfold rectBoundaryIntegral
  rw [intervalIntegral_congr_off_finset _ _ E _ (hH _) hfg,
    intervalIntegral_congr_off_finset _ _ E _ (hH _) hfg,
    intervalIntegral_congr_off_finset _ _ E _ (hV _) hfg,
    intervalIntegral_congr_off_finset _ _ E _ (hV _) hfg]

/-- **The residue theorem on a rectangle, with removable singularities.** As
`integral_boundary_rect_eq_sum_residues`, but `f` may also fail to be differentiable at the points
of a finite set `E` disjoint from `S`, anywhere in the closed rectangle including its boundary,
provided `f` is differentiable on a punctured neighborhood of each `e ∈ E` and bounded near it.
Riemann's removable singularity theorem makes these points regular, and changing `f` at finitely
many points does not change the boundary integral. -/
theorem integral_boundary_rect_eq_sum_residues_of_bounded (f : ℂ → ℂ) (z w : ℂ)
    (S E : Finset ℂ) (R : ℂ → ℂ) (hSE : Disjoint S E)
    (hS : ∀ s ∈ S, z.re < s.re ∧ s.re < w.re ∧ z.im < s.im ∧ s.im < w.im)
    (hf : DifferentiableOn ℂ f ([[z.re, w.re]] ×ℂ [[z.im, w.im]] \ ((S : Set ℂ) ∪ E)))
    (hR : ∀ s ∈ S, Tendsto (fun ζ => (ζ - s) * f ζ) (𝓝[≠] s) (𝓝 (R s)))
    (hEd : ∀ e ∈ E, ∀ᶠ ζ in 𝓝[≠] e, DifferentiableAt ℂ f ζ)
    (hEb : ∀ e ∈ E, IsBoundedUnder (· ≤ ·) (𝓝[≠] e) fun ζ => ‖f ζ‖) :
    (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
        I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) -
        I • (∫ y : ℝ in z.im..w.im, f (z.re + y * I)) =
      2 * π * I * ∑ s ∈ S, R s := by
  let g := removableExtension f E
  have hgdiff : DifferentiableOn ℂ g
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]] \ (S : Set ℂ)) :=
    removableExtension_differentiableOn f _ S E hf hEd hEb
  have hgR : ∀ s ∈ S, Tendsto (fun ζ => (ζ - s) * g ζ) (𝓝[≠] s) (𝓝 (R s)) := by
    intro s hs
    have hnot : s ∉ E := (Finset.disjoint_left.mp hSE) hs
    have hnear : g =ᶠ[𝓝[≠] s] f :=
      (removableExtension_eventuallyEq f E hnot).filter_mono nhdsWithin_le_nhds
    have hprod : (fun ζ => (ζ - s) * g ζ) =ᶠ[𝓝[≠] s]
        (fun ζ => (ζ - s) * f ζ) := hnear.mono fun ζ hζ => by
      simpa only using congrArg (fun v : ℂ => (ζ - s) * v) hζ
    exact (hR s hs).congr' hprod.symm
  have hg := integral_boundary_rect_eq_sum_residues g z w S R hS hgdiff hgR
  exact (rectBoundaryIntegral_removableExtension f z w E).symm.trans hg

/-! ### From rectangle residues to vertical integrals

Finite removable singularities permit the rectangle theorem to be applied to a meromorphic
function. Uniform decay removes the horizontal sides, leaving the difference of the two
vertical line integrals. -/

/-- A differentiability hypothesis on a closed real rectangle has the oriented complex
rectangle form required by `integral_boundary_rect_eq_sum_residues_of_bounded`. -/
theorem differentiableOn_rect_of_Icc (f : ℂ → ℂ) (a b Y : ℝ) (S E : Finset ℂ)
    (hab : a ≤ b) (hY : 0 ≤ Y)
    (h : DifferentiableOn ℂ f ((Icc a b ×ℂ Icc (-Y) Y) \ ((S : Set ℂ) ∪ E))) :
    DifferentiableOn ℂ f
      ((Set.uIcc ((a : ℂ) + (-Y) * I).re ((b : ℂ) + Y * I).re ×ℂ
        Set.uIcc ((a : ℂ) + (-Y) * I).im ((b : ℂ) + Y * I).im) \
          ((S : Set ℂ) ∪ E)) := by
  simpa [uIcc_of_le hab, uIcc_of_le (by linarith : -Y ≤ Y)] using h

/-- Meromorphy and local boundedness away from a finite pole set provide the removable
exception set required by the rectangle residue theorem. -/
theorem exists_finset_removable_of_meromorphic_bounded (f : ℂ → ℂ) (A : Set ℂ)
    (hA : IsCompact A) (S : Finset ℂ) (hf : Meromorphic f)
    (hb : ∀ z ∈ A, z ∉ S → IsBoundedUnder (· ≤ ·) (𝓝[≠] z) (fun ζ => ‖f ζ‖)) :
    ∃ E : Finset ℂ, Disjoint S E ∧
      DifferentiableOn ℂ f (A \ ((S : Set ℂ) ∪ E)) ∧
      (∀ e ∈ E, ∀ᶠ ζ in 𝓝[≠] e, DifferentiableAt ℂ f ζ) ∧
      (∀ e ∈ E, IsBoundedUnder (· ≤ ·) (𝓝[≠] e) (fun ζ => ‖f ζ‖)) := by
  have hcod : {z | AnalyticAt ℂ f z} ∈ codiscreteWithin A :=
    MeromorphicOn.eventually_codiscreteWithin_analyticAt f (fun z _ => hf z)
  have hfin : (A \ {z | AnalyticAt ℂ f z}).Finite :=
    hA.finite_sdiff_of_mem_codiscreteWithin hcod
  let E : Finset ℂ := hfin.toFinset \ S
  have hE (z : ℂ) (hz : z ∈ E) : z ∈ A ∧ z ∉ S := by
    exact ⟨(hfin.mem_toFinset.mp (Finset.mem_sdiff.mp hz).1).1,
      (Finset.mem_sdiff.mp hz).2⟩
  refine ⟨E, Finset.disjoint_left.mpr (fun _ hs he => (hE _ he).2 hs), ?_, ?_, ?_⟩
  · intro z hz
    have han : AnalyticAt ℂ f z := by
      by_contra hn
      exact hz.2 (Or.inr (Finset.mem_sdiff.mpr
        ⟨hfin.mem_toFinset.mpr ⟨hz.1, hn⟩, fun hs => hz.2 (Or.inl hs)⟩))
    exact han.differentiableAt.differentiableWithinAt
  · intro e he
    filter_upwards [(hf e).eventually_analyticAt] with z hz
    exact hz.differentiableAt
  · intro e he
    exact hb e (hE e he).1 (hE e he).2


/-- Passing a residue identity on symmetric rectangles to the two vertical integrals. -/
theorem integral_vertical_sub_eq_neg_residue_of_rectangle (f : ℂ → ℂ) (a b : ℝ) (R : ℂ)
    (ha : Integrable (fun t : ℝ => f ((a : ℂ) + t * I)))
    (hb : Integrable (fun t : ℝ => f ((b : ℂ) + t * I)))
    (hbottom : Tendsto (fun Y : ℝ => ∫ t : ℝ in a..b, f ((t : ℂ) + (-Y) * I))
      atTop (𝓝 0))
    (htop : Tendsto (fun Y : ℝ => ∫ t : ℝ in a..b, f ((t : ℂ) + Y * I))
      atTop (𝓝 0))
    (hrect : ∀ᶠ Y : ℝ in atTop,
      (∫ t : ℝ in a..b, f ((t : ℂ) + (-Y) * I)) -
        (∫ t : ℝ in a..b, f ((t : ℂ) + Y * I)) +
        I • (∫ t : ℝ in -Y..Y, f ((b : ℂ) + t * I)) -
        I • (∫ t : ℝ in -Y..Y, f ((a : ℂ) + t * I)) =
        2 * Real.pi * I * R) :
    (∫ t : ℝ, f ((a : ℂ) + t * I) * I) -
      (∫ t : ℝ, f ((b : ℂ) + t * I) * I) = -(2 * Real.pi * I) * R := by
  have hright := intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id
  have hleft := intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id
  have hlim := (hbottom.sub htop).add (hright.const_smul I) |>.sub (hleft.const_smul I)
  have heq : (0 : ℂ) - 0 + I • (∫ t : ℝ, f ((b : ℂ) + t * I)) -
      I • (∫ t : ℝ, f ((a : ℂ) + t * I)) = 2 * Real.pi * I * R := by
    apply tendsto_nhds_unique hlim
    exact (tendsto_const_nhds : Tendsto (fun _ : ℝ => 2 * Real.pi * I * R)
      atTop (𝓝 (2 * Real.pi * I * R))).congr' (hrect.mono fun Y h => h.symm)
  simp only [integral_mul_const, smul_eq_mul] at heq ⊢
  linear_combination -heq


/-- Uniform norm decay on a fixed horizontal segment makes its integral tend to zero. -/
theorem tendsto_intervalIntegral_of_uniform_bound (f : ℝ → ℝ → ℂ) (a b : ℝ)
    (g : ℝ → ℝ) (hg : Tendsto g atTop (𝓝 0))
    (hbound : ∀ᶠ Y : ℝ in atTop, ∀ t ∈ uIcc a b, ‖f t Y‖ ≤ g Y) :
    Tendsto (fun Y => ∫ t : ℝ in a..b, f t Y) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
    (hbound.mono (fun Y hY => intervalIntegral.norm_integral_le_of_norm_le_const
      (fun t ht => hY t (uIoc_subset_uIcc ht))))
  simpa using hg.mul_const |b - a|

/-- Uniform decay of finitely many summands makes the horizontal integral of their sum
vanish. -/
theorem tendsto_intervalIntegral_sum_of_bounds {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℝ → ℂ) (a b : ℝ)
    (h : ∀ i : ι, ∃ g : ℝ → ℝ, Tendsto g atTop (𝓝 0) ∧
      ∀ᶠ Y : ℝ in atTop, ∀ t ∈ uIcc a b, ‖f i t Y‖ ≤ g Y) :
    Tendsto (fun Y => ∫ t : ℝ in a..b, ∑ i, f i t Y) atTop (𝓝 0) := by
  choose g hg hbound using h
  have hgSum : Tendsto (fun Y => ∑ i, g i Y) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun i _ => hg i)
  apply tendsto_intervalIntegral_of_uniform_bound _ a b _ hgSum
  filter_upwards [Filter.eventually_all.mpr hbound] with Y hY t ht
  calc
    ‖∑ i, f i t Y‖ ≤ ∑ i, ‖f i t Y‖ := norm_sum_le _ _
    _ ≤ ∑ i, g i Y := Finset.sum_le_sum (fun i _ => hY i t ht)

/-! ### Small squares about one meromorphic singularity

A meromorphic germ is analytic at all nearby points other than its centre. The rectangle
residue theorem with the singleton pole set therefore evaluates every sufficiently small square.
Residue limits also give translation, vanishing, and finite-sum rules for these integrals.
-/

/-- A meromorphic germ of order at least `−1` has a finite residue limit. Multiplying by
`z-s` makes the order nonnegative, so Mathlib’s
`tendsto_nhds_of_meromorphicOrderAt_nonneg` supplies the limit used by
`eventually_rectBoundaryIntegral_square_eq_residue`. -/
theorem tendsto_sub_mul_of_meromorphicOrderAt_ge_neg_one (f : ℂ → ℂ) (s : ℂ)
    (hf : MeromorphicAt f s) (ho : ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f s) :
    ∃ R : ℂ, Tendsto (fun ζ : ℂ => (ζ - s) * f ζ) (𝓝[≠] s) (𝓝 R) := by
  let g : ℂ → ℂ := fun ζ => (ζ - s) * f ζ
  have hmer : MeromorphicAt g s :=
    (show AnalyticAt ℂ (fun ζ : ℂ => ζ - s) s by fun_prop).meromorphicAt.mul hf
  have hord : meromorphicOrderAt g s = (1 : WithTop ℤ) + meromorphicOrderAt f s := by
    change meromorphicOrderAt ((fun ζ : ℂ => ζ - s) * f) s = _
    rw [meromorphicOrderAt_mul
      (show AnalyticAt ℂ (fun ζ : ℂ => ζ - s) s by fun_prop).meromorphicAt hf]
    simp
  have hnonneg : 0 ≤ meromorphicOrderAt g s := by
    rw [hord]
    have h := add_le_add_left ho (1 : WithTop ℤ)
    simpa [add_comm] using h
  exact tendsto_nhds_of_meromorphicOrderAt_nonneg hmer hnonneg


/-- A closed square of half-side `r` about `p` lies in the ball of radius `ε` when
`2r < ε`; used by `eventually_rectBoundaryIntegral_square_eq_residue`. -/
private lemma square_subset_ball (p : ℂ) {r ε : ℝ} (hr : 0 ≤ r) (hε : 2 * r < ε) :
    (Set.uIcc (p - (r + r * I)).re (p + (r + r * I)).re ×ℂ
      Set.uIcc (p - (r + r * I)).im (p + (r + r * I)).im) ⊆ Metric.ball p ε := by
  intro ζ hζ
  have hcoords : ζ.re ∈ uIcc (p.re - r) (p.re + r) ∧
      ζ.im ∈ uIcc (p.im - r) (p.im + r) := by
    simpa [mem_reProdIm] using hζ
  have bound (a b : ℝ) (hb : b ∈ uIcc (a - r) (a + r)) : |b - a| ≤ r := by
    rw [uIcc_of_le (by linarith)] at hb
    exact abs_le.mpr ⟨by linarith [hb.1], by linarith [hb.2]⟩
  have hre : |(ζ - p).re| ≤ r := by simpa only [sub_re] using bound p.re ζ.re hcoords.1
  have him : |(ζ - p).im| ≤ r := by simpa only [sub_im] using bound p.im ζ.im hcoords.2
  rw [Metric.mem_ball, dist_eq_norm]
  calc
    ‖ζ - p‖ ≤ |(ζ - p).re| + |(ζ - p).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2 * r := by linarith
    _ < ε := hε

/-- The boundary integral over every sufficiently small square about a meromorphic point is
`2πi R` when `(z-p)f(z) → R`. This is the singleton case of
`integral_boundary_rect_eq_sum_residues`, using `MeromorphicAt.eventually_analyticAt` to isolate
the centre. It also applies with `R=0` at removable singularities. -/
theorem eventually_rectBoundaryIntegral_square_eq_residue
    {f : ℂ → ℂ} {p R : ℂ} (hf : MeromorphicAt f p)
    (hR : Tendsto (fun z : ℂ => (z - p) * f z) (𝓝[≠] p) (𝓝 R)) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      rectBoundaryIntegral f (p - (r + r * I)) (p + (r + r * I)) =
        2 * Real.pi * I * R := by
  obtain ⟨ε, hε, hAnalytic⟩ := Metric.eventually_nhds_iff_ball.mp
    (eventually_nhdsWithin_iff.mp hf.eventually_analyticAt)
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (isOpen_Iio.mem_nhds
      (show (0 : ℝ) < ε / 2 by positivity))] with r hr hrε
  have hrpos : 0 < r := hr
  have hrlt : r < ε / 2 := hrε
  have hleft : (p - (r + r * I)).re = p.re - r := by simp
  have hright : (p + (r + r * I)).re = p.re + r := by simp
  have hbottom : (p - (r + r * I)).im = p.im - r := by simp
  have htop : (p + (r + r * I)).im = p.im + r := by simp
  have hS : ∀ s ∈ ({p} : Finset ℂ),
      (p - (r + r * I)).re < s.re ∧ s.re < (p + (r + r * I)).re ∧
        (p - (r + r * I)).im < s.im ∧ s.im < (p + (r + r * I)).im := by
    intro s hs
    simp only [Finset.mem_singleton] at hs
    subst s
    rw [hleft, hright, hbottom, htop]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hdiff : DifferentiableOn ℂ f
      (Set.uIcc (p - (r + r * I)).re (p + (r + r * I)).re ×ℂ
        Set.uIcc (p - (r + r * I)).im (p + (r + r * I)).im \ ({p} : Set ℂ)) := by
    intro ζ hζ
    have hball : ζ ∈ Metric.ball p ε := square_subset_ball p hrpos.le (by linarith) hζ.1
    have hne : ζ ∈ ({p} : Set ℂ)ᶜ := hζ.2
    exact (hAnalytic ζ hball hne).differentiableAt.differentiableWithinAt
  have h := integral_boundary_rect_eq_sum_residues f
    (p - (r + r * I)) (p + (r + r * I)) {p} (fun _ => R) hS
    (by simpa only [Finset.coe_singleton] using hdiff)
    (by simpa using hR)
  simpa only [rectBoundaryIntegral, Finset.sum_singleton] using h

/-- Translation carries the small-square integral of a meromorphic germ at `p - v` to the
small-square integral of its translate at `p`, by
`eventually_rectBoundaryIntegral_square_eq_residue`. -/
theorem eventually_rectBoundaryIntegral_square_translate
    (f : ℂ → ℂ) (p v : ℂ)
    (hf : MeromorphicAt f (p - v))
    (ho : (-1 : WithTop ℤ) ≤ meromorphicOrderAt f (p - v)) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      rectBoundaryIntegral (fun z => f (z - v))
        (p - (r + r * I)) (p + (r + r * I)) =
      rectBoundaryIntegral f ((p - v) - (r + r * I))
        ((p - v) + (r + r * I)) := by
  obtain ⟨R, hR⟩ :=
    tendsto_sub_mul_of_meromorphicOrderAt_ge_neg_one f (p - v) hf ho
  have hShift : Tendsto (fun z : ℂ => z - v) (𝓝[≠] p) (𝓝[≠] (p - v)) := by
    simpa only [sub_eq_add_neg] using tendsto_add_const_nhdsNE (-v) p
  have hR' : Tendsto (fun z : ℂ => (z - p) * f (z - v)) (𝓝[≠] p) (𝓝 R) := by
    convert hR.comp hShift using 1
    funext z
    congr 1
    ring
  have hf' : MeromorphicAt (fun z => f (z - v)) p :=
    (meromorphicAt_comp_sub_const_iff_meromorphicAt).2 hf
  filter_upwards [eventually_rectBoundaryIntegral_square_eq_residue hf' hR',
    eventually_rectBoundaryIntegral_square_eq_residue hf hR] with r hleft hright
  rw [hleft, hright]

/-- A meromorphic germ of nonnegative order has zero small-square integral, by
`eventually_rectBoundaryIntegral_square_eq_residue`. -/
theorem eventually_rectBoundaryIntegral_square_eq_zero (f : ℂ → ℂ) (p : ℂ)
    (hf : MeromorphicAt f p) (ho : 0 ≤ meromorphicOrderAt f p) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      rectBoundaryIntegral f (p - (r + r * I)) (p + (r + r * I)) = 0 := by
  obtain ⟨C, hC⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hf ho
  have hz : Tendsto (fun z : ℂ => z - p) (𝓝[≠] p) (𝓝 0) := by
    simpa only [sub_self, id_eq] using
      (tendsto_id.sub_const p).mono_left (show 𝓝[≠] p ≤ 𝓝 p from nhdsWithin_le_nhds)
  have hR : Tendsto (fun z : ℂ => (z - p) * f z) (𝓝[≠] p) (𝓝 0) := by
    simpa only [zero_mul] using hz.mul hC
  simpa only [mul_zero] using eventually_rectBoundaryIntegral_square_eq_residue hf hR

/-- A punctured-germ identity with a scalar finite sum gives the corresponding small-square
integral identity, by `eventually_rectBoundaryIntegral_square_eq_residue`. -/
theorem eventually_rectBoundaryIntegral_square_mul_sum {ι : Type*} [Fintype ι]
    (J : ℂ → ℂ) (f : ι → ℂ → ℂ) (P p : ℂ)
    (hEq : J =ᶠ[𝓝[≠] p] fun z => P * ∑ i, f i z)
    (hf : ∀ i, MeromorphicAt (f i) p)
    (ho : ∀ i, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (f i) p) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      rectBoundaryIntegral J (p - (r + r * I)) (p + (r + r * I)) =
        P * ∑ i, rectBoundaryIntegral (f i)
          (p - (r + r * I)) (p + (r + r * I)) := by
  classical
  choose R hR using (fun i =>
    tendsto_sub_mul_of_meromorphicOrderAt_ge_neg_one (f i) p (hf i) (ho i))
  have hSumR : Tendsto (fun z : ℂ => (z - p) * ∑ i, f i z) (𝓝[≠] p)
      (𝓝 (∑ i, R i)) := by
    have h := tendsto_finsetSum Finset.univ (fun i _ => hR i)
    convert h using 1
    funext z
    simp only [Finset.mul_sum]
  have hMerSum : MeromorphicAt (fun z => P * ∑ i, f i z) p := by
    exact (MeromorphicAt.const P p).mul
      (MeromorphicAt.fun_sum (s := Finset.univ) (by intro i _; exact hf i))
  have hMerJ : MeromorphicAt J p := hMerSum.congr hEq.symm
  have hRJ : Tendsto (fun z : ℂ => (z - p) * J z) (𝓝[≠] p)
      (𝓝 (P * ∑ i, R i)) := by
    have hP : Tendsto (fun _ : ℂ => P) (𝓝[≠] p) (𝓝 P) := tendsto_const_nhds
    have h := hP.mul hSumR
    have h' : Tendsto (fun z : ℂ => (z - p) * (P * ∑ i, f i z)) (𝓝[≠] p)
        (𝓝 (P * ∑ i, R i)) := by
      convert h using 1
      funext z
      ring
    have heq : (fun z : ℂ => (z - p) * (P * ∑ i, f i z)) =ᶠ[𝓝[≠] p]
        (fun z : ℂ => (z - p) * J z) := by
      filter_upwards [hEq] with z hz
      rw [hz]
    exact h'.congr' heq
  have hJ := eventually_rectBoundaryIntegral_square_eq_residue hMerJ hRJ
  have hF := Filter.eventually_all.mpr
    (fun i => eventually_rectBoundaryIntegral_square_eq_residue (hf i) (hR i))
  filter_upwards [hJ, hF] with r hJ hF
  rw [hJ]
  simp_rw [hF]
  rw [← Finset.mul_sum]
  ring

end SIC
