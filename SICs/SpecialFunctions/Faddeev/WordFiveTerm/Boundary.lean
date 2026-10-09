/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.Faddeev.WordFiveTerm.Kernel
import SICs.Analysis.CompactConvergence

/-!
# Finite five-term contours of a letter word at the real boundary

The upper-half-plane five-term kernel of a letter word converges, as its period approaches a
real period with positive word periods, to the word kernel uniformly on compact segments of
regular vertical lines; hence its integrals over finite vertical and horizontal segments, and its
boundary integrals over rectangles with regular vertical sides, converge to those of the word
kernel at the real period.

This module follows the boundary passage of [RW26, Radchenko, Wheeler (2026), Theorem 3,
`thm:5term.mod.fad`, equation (23), `eq:5term.int`, Appendix A.2, `app:mod.fad`], with the word
product of equation (20), `eq:modulartofaddeevCF`. The principal word is treated directly in
`SICs.Principal.Dilogarithm.Faddeev.FiveTerm.Boundary`.

## The argument

For each fixed upper-half-plane period, the modular kernel and the word kernel agree outside a
countable subset of every affine real contour, so their integrals over it agree, and the word
kernel inherits measurability. At the real period, a vertical line whose crossing `x` and its
translate `x+y` avoid `ℤ+ℤτ₀` meets no pole of the word kernel, and the kernel is jointly
continuous in the point and the period along it. Compactness of a finite segment then gives
uniform convergence as the period tends to `τ₀`, which passes the finite integrals to the
limit. Off the real axis the real lattice is absent, so horizontal segments at nonzero height
converge in the same way, and so do the boundary integrals of rectangles whose vertical sides
cross the real axis at regular crossings.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology MatrixGroups

namespace SIC

/-! ### Measurability -/

/-- Along an affine real contour the word kernel inherits almost-everywhere strong
measurability from the modular kernel; used by the finite-segment limits below. -/
private lemma aestronglyMeasurable_fiveTermWordKernel_affine (bs : List ℤ) (hbs : bs ≠ [])
    (ℓ p m : ℤ) (w y τ c b : ℂ) (hτ : 0 < τ.im) (hc : c ≠ 0) :
    AEStronglyMeasurable (fun t : ℝ =>
      fiveTermWordKernel bs ℓ p w y τ m (c * t + b)) := by
  have hz : Measurable (fun t : ℝ => c * (t : ℂ) + b) := by fun_prop
  have hk : Measurable (fun t : ℝ =>
      fiveTermKernelUHP (letterWord bs) ℓ p w y τ m (c * t + b)) :=
    (measurable_fiveTermKernelUHP (letterWord bs) ℓ p w y τ hτ m).comp hz
  exact hk.aestronglyMeasurable.congr
    (ae_fiveTermKernelUHP_eq_fiveTermWordKernel bs hbs ℓ p m w y τ c b hτ hc)

/-- For a fixed upper-half-plane period, the five-term kernel of a nonempty letter word is
almost everywhere strongly measurable along every vertical line, since it agrees almost
everywhere with the measurable modular kernel. -/
theorem aestronglyMeasurable_fiveTermWordKernel (bs : List ℤ) (hbs : bs ≠ [])
    (ℓ p m : ℤ) (w y τ : ℂ) (hτ : 0 < τ.im) (x : ℝ) :
    AEStronglyMeasurable (fun t : ℝ =>
      fiveTermWordKernel bs ℓ p w y τ m ((x : ℂ) + t * I)) := by
  have h := aestronglyMeasurable_fiveTermWordKernel_affine
    bs hbs ℓ p m w y τ I x hτ Complex.I_ne_zero
  have harg (t : ℝ) : I * (t : ℂ) + x = (x : ℂ) + t * I := by ring
  simpa only [harg] using h

/-! ### Uniform convergence on vertical segments -/

/-! ### Finite segments and rectangles -/

/-- Almost-everywhere equality of the modular and word kernels gives equality of their
finite affine-contour integrals; used by both segment limits below. -/
private lemma intervalIntegral_fiveTermKernelUHP_eq_word_affine (bs : List ℤ) (hbs : bs ≠ [])
    (ℓ p m : ℤ) (w y τ c b k : ℂ) (s₁ s₂ : ℝ)
    (hτ : 0 < τ.im) (hc : c ≠ 0) :
    (∫ t in s₁..s₂,
      fiveTermKernelUHP (letterWord bs) ℓ p w y τ m (c * t + b) * k) =
      ∫ t in s₁..s₂,
        fiveTermWordKernel bs ℓ p w y τ m (c * t + b) * k := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [ae_fiveTermKernelUHP_eq_fiveTermWordKernel
    bs hbs ℓ p m w y τ c b hτ hc] with t ht _
  rw [ht]

/-- The integral of the upper-half-plane five-term kernel of a letter word over a finite segment
of a regular vertical line converges to the word kernel's integral at a real period with
positive word periods; used by `tendsto_rectBoundaryIntegral_kernelUHP_letterWord`. -/
private theorem tendsto_intervalIntegral_kernelUHP_letterWord (bs : List ℤ) (hbs : bs ≠ [])
    {τ₀ : ℝ} (hτ₀ : FaddeevWordPeriodsPos bs τ₀) (ℓ p m : ℤ) (w y x a b : ℝ)
    (hx : IsRegularPeriodLatticeCrossing τ₀ y x) :
    Tendsto (fun τ : ℂ => ∫ t in a..b,
        fiveTermKernelUHP (letterWord bs) ℓ p w y τ m ((x : ℂ) + t * I) * I)
      (𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ))
      (𝓝 (∫ t in a..b, fiveTermWordKernel bs ℓ p w y τ₀ m ((x : ℂ) + t * I) * I)) := by
  let U : Set ℂ := {τ | 0 < τ.im}
  have hf : ∀ t ∈ Set.uIcc a b, ContinuousAt
      (fun q : ℝ × ℂ =>
        fiveTermWordKernel bs ℓ p w y q.2 m (x + q.1 * I) * I)
      (t, (τ₀ : ℂ)) := by
    intro t _
    exact (continuousAt_fiveTermWordKernel_vertical bs hτ₀ ℓ p m w y x t hx).mul
      continuousAt_const
  have hmeas : ∀ᶠ τ in 𝓝[U] (τ₀ : ℂ),
      AEStronglyMeasurable (fun t : ℝ =>
        fiveTermWordKernel bs ℓ p w y τ m (x + t * I) * I)
        (volume.restrict (Set.uIoc a b)) := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact ((aestronglyMeasurable_fiveTermWordKernel bs hbs ℓ p m w y τ hτ x).mul_const I)
      |>.restrict
  have hlim := tendsto_intervalIntegral_of_continuousAt_prod
    nhdsWithin_le_nhds a b hf hmeas
  have heq : (fun τ : ℂ => ∫ t in a..b,
      fiveTermKernelUHP (letterWord bs) ℓ p w y τ m (x + t * I) * I) =ᶠ[
      𝓝[U] (τ₀ : ℂ)] (fun τ : ℂ => ∫ t in a..b,
      fiveTermWordKernel bs ℓ p w y τ m (x + t * I) * I) := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have h := intervalIntegral_fiveTermKernelUHP_eq_word_affine
      bs hbs ℓ p m w y τ I x I a b hτ Complex.I_ne_zero
    have harg (t : ℝ) : I * (t : ℂ) + x = (x : ℂ) + t * I := by ring
    simpa only [harg] using h
  exact hlim.congr' heq.symm

/-- Joint continuity of the word kernel on a horizontal contour at nonzero height;
used by the horizontal finite-segment limit. -/
private lemma continuousAt_fiveTermWordKernel_horizontal (bs : List ℤ) {τ₀ : ℝ}
    (hτ₀ : FaddeevWordPeriodsPos bs τ₀) (ℓ p m : ℤ)
    (w y a s : ℝ) (ha : a ≠ 0) :
    ContinuousAt (fun q : ℝ × ℂ =>
      fiveTermWordKernel bs ℓ p w y q.2 m (q.1 + a * I)) (s, (τ₀ : ℂ)) := by
  have hz_im : (((s : ℂ) + a * I)).im = a := by simp
  have hzy_im : ((((s : ℂ) + a * I) + y)).im = a := by simp
  have hz_nonzero : (((s : ℂ) + a * I)).im ≠ 0 := by
    rw [hz_im]
    exact ha
  have hzy_nonzero : ((((s : ℂ) + a * I) + y)).im ≠ 0 := by
    rw [hzy_im]
    exact ha
  have hz := not_isPeriodLatticePoint_of_im_ne_zero
    ((s : ℂ) + a * I) τ₀ hz_nonzero
  have hzy := not_isPeriodLatticePoint_of_im_ne_zero
    (((s : ℂ) + a * I) + y) τ₀ hzy_nonzero
  have h := continuousAt_fiveTermWordKernel bs hτ₀ ℓ p m w y ((s : ℂ) + a * I) hz hzy
  have harg : ContinuousAt (fun q : ℝ × ℂ =>
      ((q.1 : ℂ) + a * I, q.2)) (s, (τ₀ : ℂ)) := by fun_prop
  simpa only [Function.comp_def] using h.comp_of_eq harg rfl

/-- The integral of the upper-half-plane five-term kernel of a letter word over a finite
horizontal segment at nonzero height converges to the word kernel's integral at a real period
with positive word periods; used by `tendsto_rectBoundaryIntegral_kernelUHP_letterWord`. -/
private theorem tendsto_intervalIntegral_kernelUHP_letterWord_horizontal (bs : List ℤ)
    (hbs : bs ≠ []) {τ₀ : ℝ} (hτ₀ : FaddeevWordPeriodsPos bs τ₀) (ℓ p m : ℤ)
    (w y a s₁ s₂ : ℝ) (ha : a ≠ 0) :
    Tendsto (fun τ : ℂ => ∫ s in s₁..s₂,
        fiveTermKernelUHP (letterWord bs) ℓ p w y τ m ((s : ℂ) + a * I))
      (𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ))
      (𝓝 (∫ s in s₁..s₂, fiveTermWordKernel bs ℓ p w y τ₀ m ((s : ℂ) + a * I))) := by
  let U : Set ℂ := {τ | 0 < τ.im}
  have hf : ∀ s ∈ Set.uIcc s₁ s₂, ContinuousAt
      (fun q : ℝ × ℂ =>
        fiveTermWordKernel bs ℓ p w y q.2 m (q.1 + a * I))
      (s, (τ₀ : ℂ)) := by
    intro s _
    exact continuousAt_fiveTermWordKernel_horizontal bs hτ₀ ℓ p m w y a s ha
  have hmeas : ∀ᶠ τ in 𝓝[U] (τ₀ : ℂ),
      AEStronglyMeasurable (fun s : ℝ =>
        fiveTermWordKernel bs ℓ p w y τ m (s + a * I))
        (volume.restrict (Set.uIoc s₁ s₂)) := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have h := aestronglyMeasurable_fiveTermWordKernel_affine
      bs hbs ℓ p m w y τ 1 (a * I) hτ one_ne_zero
    simpa only [one_mul] using (h.restrict (s := Set.uIoc s₁ s₂))
  have hlim := tendsto_intervalIntegral_of_continuousAt_prod
    nhdsWithin_le_nhds s₁ s₂ hf hmeas
  have heq : (fun τ : ℂ => ∫ s in s₁..s₂,
      fiveTermKernelUHP (letterWord bs) ℓ p w y τ m (s + a * I)) =ᶠ[
      𝓝[U] (τ₀ : ℂ)] (fun τ : ℂ => ∫ s in s₁..s₂,
      fiveTermWordKernel bs ℓ p w y τ m (s + a * I)) := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have h := intervalIntegral_fiveTermKernelUHP_eq_word_affine
      bs hbs ℓ p m w y τ 1 (a * I) 1 s₁ s₂ hτ one_ne_zero
    simpa only [one_mul, mul_one] using h
  exact hlim.congr' heq.symm

/-- The boundary integral of the upper-half-plane five-term kernel of a letter word over a
rectangle with corners off the real axis and regular vertical sides converges to that of the
word kernel at a real period with positive word periods. -/
theorem tendsto_rectBoundaryIntegral_kernelUHP_letterWord (bs : List ℤ)
    (hbs : bs ≠ []) {τ₀ : ℝ} (hτ₀ : FaddeevWordPeriodsPos bs τ₀) (ℓ p m : ℤ) (w y : ℝ)
    (z₁ z₂ : ℂ) (h₁ : z₁.im ≠ 0) (h₂ : z₂.im ≠ 0)
    (hx₁ : IsRegularPeriodLatticeCrossing τ₀ y z₁.re)
    (hx₂ : IsRegularPeriodLatticeCrossing τ₀ y z₂.re) :
    Tendsto (fun τ : ℂ =>
        rectBoundaryIntegral (fiveTermKernelUHP (letterWord bs) ℓ p w y τ m) z₁ z₂)
      (𝓝[{τ : ℂ | 0 < τ.im}] (τ₀ : ℂ))
      (𝓝 (rectBoundaryIntegral (fiveTermWordKernel bs ℓ p w y τ₀ m) z₁ z₂)) := by
  have hbottom := tendsto_intervalIntegral_kernelUHP_letterWord_horizontal
    bs hbs hτ₀ ℓ p m w y z₁.im z₁.re z₂.re h₁
  have htop := tendsto_intervalIntegral_kernelUHP_letterWord_horizontal
    bs hbs hτ₀ ℓ p m w y z₂.im z₁.re z₂.re h₂
  have hright := tendsto_intervalIntegral_kernelUHP_letterWord
    bs hbs hτ₀ ℓ p m w y z₂.re z₁.im z₂.im hx₂
  have hleft := tendsto_intervalIntegral_kernelUHP_letterWord
    bs hbs hτ₀ ℓ p m w y z₁.re z₁.im z₂.im hx₁
  simp only [intervalIntegral.integral_mul_const] at hright hleft
  simpa only [rectBoundaryIntegral, smul_eq_mul, mul_comm I] using
    ((hbottom.sub htop).add hright).sub hleft

end SIC

end
