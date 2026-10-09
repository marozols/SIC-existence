/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.Faddeev.FiveTerm.Bounds
import SICs.SpecialFunctions.Faddeev.FiveTerm.ContourGeometry
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Absolute integrability of the vertical five-term kernel

The upper-half-plane five-term kernel is measurable and absolutely integrable on a vertical line
separated from its genuine poles.

This module follows [RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`], in the proof
of Theorem 3, `thm:5term.mod.fad`, with the corrected lower decay rate from
`SICs.SpecialFunctions.Faddeev.FiveTerm.Bounds`. Write `ε = cτ+d`, `λ = cw/ε+ℓ`, and
`μ = c(w+y)/ε+ℓ+p-1`. If `Re ε > 0`, the modular height `Im((x+it)/ε)` grows with `t`.
Thus the upper sector bound gives exponential decay as `t → +∞` when `Re λ > 0`, and the lower
sector bound gives decay as `t → -∞` when `Re μ < 0`. On the finite middle interval the global
bound has a continuous exponent. The separation hypotheses concern only genuine poles and zeros;
the kernel may have totalized, discontinuous values at removable points on the line.
A line that meets no genuine right pole remains integrable even if finitely many right poles lie
to its left.
-/

noncomputable section

open Complex Real Filter MeasureTheory Set
open scoped Topology MatrixGroups

namespace SIC

/-! ### Vertical geometry

The modular height along a vertical line has positive slope when `Re ε > 0`. -/

/-- The height of a vertical line in modular coordinates; used by the two sector estimates. -/
private lemma fiveTerm_vertical_div_im (e : ℂ) (x t : ℝ) :
    (((x : ℂ) + (t : ℂ) * I) / e).im =
      (t * e.re - x * e.im) / Complex.normSq e := by
  rw [Complex.div_im]
  simp only [Complex.add_im, Complex.add_re, Complex.ofReal_im, Complex.ofReal_re,
    Complex.mul_I_im, Complex.mul_I_re, zero_add]
  ring_nf

/-- `Re ε > 0` makes both sector heights large on the upper vertical tail; used by
`exists_norm_fiveTermKernelUHP_vertical_Ici`. -/
private lemma fiveTerm_vertical_upper_region (e : ℂ) (he : 0 < e.re) (x T : ℝ) :
    ∃ U : ℝ, ∀ t : ℝ, U ≤ t → T ≤ t ∧ T ≤ (((x : ℂ) + (t : ℂ) * I) / e).im := by
  have hen : 0 < Complex.normSq e := Complex.normSq_pos.mpr (by
    intro h; simp [h] at he)
  refine ⟨max T ((T * Complex.normSq e + x * e.im) / e.re), ?_⟩
  intro t ht
  constructor
  · exact (le_max_left _ _).trans ht
  rw [fiveTerm_vertical_div_im]
  apply (le_div_iff₀ hen).2
  have hmul := (div_le_iff₀ he).1 ((le_max_right _ _).trans ht)
  nlinarith

/-- `Re ε > 0` makes both sector heights negative on the lower vertical tail; used by
`exists_norm_fiveTermKernelUHP_vertical_Iic`. -/
private lemma fiveTerm_vertical_lower_region (e : ℂ) (he : 0 < e.re) (x T : ℝ) :
    ∃ U : ℝ, ∀ t : ℝ, t ≤ -U → t ≤ -T ∧
      (((x : ℂ) + (t : ℂ) * I) / e).im ≤ -T := by
  have hen : 0 < Complex.normSq e := Complex.normSq_pos.mpr (by
    intro h; simp [h] at he)
  refine ⟨max T ((T * Complex.normSq e - x * e.im) / e.re), ?_⟩
  intro t ht
  constructor
  · exact ht.trans (neg_le_neg (le_max_left _ _))
  rw [fiveTerm_vertical_div_im]
  apply (div_le_iff₀ hen).2
  have hmax : max T ((T * Complex.normSq e - x * e.im) / e.re) ≤ -t := by
    linarith
  have hmul := (div_le_iff₀ he).1 ((le_max_right _ _).trans hmax)
  nlinarith

/-! ### Exponential tails

The sector estimates from `SICs.SpecialFunctions.Faddeev.FiveTerm.Bounds` become ordinary
one-dimensional exponentials after restricting to a vertical line. -/

/-- The imaginary part of a phase along a vertical line; used by both tail estimates. -/
private lemma fiveTerm_vertical_phase (v : ℂ) (x t : ℝ) :
    (v * ((x : ℂ) + (t : ℂ) * I)).im = (v * (x : ℂ)).im + v.re * t := by
  simp only [mul_add, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_I_re, Complex.I_im]
  ring_nf

/-- On the upper vertical tail, `‖K_m(x+it)‖ ≤ C exp(-2π Re(λ)t)`, where
`λ = cw/ε+ℓ`. This is the first convergence condition in
[RW26, Radchenko, Wheeler (2026), Theorem 3, `thm:5term.mod.fad`]. -/
theorem exists_norm_fiveTermKernelUHP_vertical_Ici (γ : SL(2, ℤ)) (ℓ p : ℤ)
    (w y τ : ℂ) (hτ : 0 < τ.im) (m : ℤ)
    (he : 0 < (fltDenominator (γ : Mat(2, ℤ)) τ).re) (x : ℝ) :
    ∃ C T : ℝ, ∀ t : ℝ, T ≤ t →
      ‖fiveTermKernelUHP γ ℓ p w y τ m ((x : ℂ) + (t : ℂ) * I)‖ ≤
        C * Real.exp ((-2 * π *
          ((((γ 1 0 : ℤ) : ℂ) * w / fltDenominator (γ : Mat(2, ℤ)) τ + ℓ)).re) * t) := by
  let e := fltDenominator (γ : Mat(2, ℤ)) τ
  let lam : ℂ := ((γ 1 0 : ℤ) : ℂ) * w / e + ℓ
  obtain ⟨C, T, hbound⟩ := exists_norm_fiveTermKernelUHP_le_upper γ ℓ p w y τ hτ m
  obtain ⟨U, hregion⟩ := fiveTerm_vertical_upper_region e he x T
  refine ⟨C * Real.exp (-2 * π * (lam * (x : ℂ)).im), U, ?_⟩
  intro t ht
  obtain ⟨ht, hte⟩ := hregion t ht
  have h := hbound ((x : ℂ) + (t : ℂ) * I) (by simpa using ht) hte
  change ‖fiveTermKernelUHP γ ℓ p w y τ m ((x : ℂ) + (t : ℂ) * I)‖ ≤
    C * Real.exp (-2 * π * (lam * ((x : ℂ) + (t : ℂ) * I)).im) at h
  rw [fiveTerm_vertical_phase] at h
  change ‖fiveTermKernelUHP γ ℓ p w y τ m ((x : ℂ) + (t : ℂ) * I)‖ ≤
    (C * Real.exp (-2 * π * (lam * (x : ℂ)).im)) *
      Real.exp ((-2 * π * lam.re) * t)
  calc
    _ ≤ C * Real.exp (-2 * π * ((lam * (x : ℂ)).im + lam.re * t)) := h
    _ = _ := by rw [mul_add, Real.exp_add]; ring_nf

/-- On the lower vertical tail, `‖K_m(x+it)‖ ≤ C exp(-2π Re(μ)t)`, where
`μ = c(w+y)/ε+ℓ+p-1`. This uses the corrected lower convergence condition of
[RW26, Radchenko, Wheeler (2026), Theorem 3, `thm:5term.mod.fad`]. -/
theorem exists_norm_fiveTermKernelUHP_vertical_Iic (γ : SL(2, ℤ)) (ℓ p : ℤ)
    (w y τ : ℂ) (hτ : 0 < τ.im) (m : ℤ)
    (he : 0 < (fltDenominator (γ : Mat(2, ℤ)) τ).re) (x : ℝ) :
    ∃ C T : ℝ, ∀ t : ℝ, t ≤ -T →
      ‖fiveTermKernelUHP γ ℓ p w y τ m ((x : ℂ) + (t : ℂ) * I)‖ ≤
        C * Real.exp ((-2 * π *
          ((((γ 1 0 : ℤ) : ℂ) * (w + y) /
            fltDenominator (γ : Mat(2, ℤ)) τ + ℓ + p - 1)).re) * t) := by
  let e := fltDenominator (γ : Mat(2, ℤ)) τ
  let mu : ℂ := ((γ 1 0 : ℤ) : ℂ) * (w + y) / e + ℓ + p - 1
  obtain ⟨C, T, hbound⟩ := exists_norm_fiveTermKernelUHP_le_lower γ ℓ p w y τ hτ m
  obtain ⟨U, hregion⟩ := fiveTerm_vertical_lower_region e he x T
  refine ⟨C * Real.exp (-2 * π * (mu * (x : ℂ)).im), U, ?_⟩
  intro t ht
  obtain ⟨ht, hte⟩ := hregion t ht
  have h := hbound ((x : ℂ) + (t : ℂ) * I) (by simpa using ht) hte
  change ‖fiveTermKernelUHP γ ℓ p w y τ m ((x : ℂ) + (t : ℂ) * I)‖ ≤
    C * Real.exp (-2 * π * (mu * ((x : ℂ) + (t : ℂ) * I)).im) at h
  rw [fiveTerm_vertical_phase] at h
  change ‖fiveTermKernelUHP γ ℓ p w y τ m ((x : ℂ) + (t : ℂ) * I)‖ ≤
    (C * Real.exp (-2 * π * (mu * (x : ℂ)).im)) *
      Real.exp ((-2 * π * mu.re) * t)
  calc
    _ ≤ C * Real.exp (-2 * π * ((mu * (x : ℂ)).im + mu.re * t)) := h
    _ = _ := by rw [mul_add, Real.exp_add]; ring_nf

/-! ### Absolute integrability

The global bound controls the finite middle interval without any continuity assertion about the
kernel. The two exponential tails then cover the rest of the line. -/

/-- Measurable functions dominated on a measurable set by an integrable real function are
integrable there; used by `integrableOn_kernelUHP_vertical_Icc` and the
vertical tail proofs. -/
private lemma fiveTerm_integrableOn_of_bound {f : ℝ → ℂ} (hf : Measurable f)
    {s : Set ℝ} (hs : MeasurableSet s) {g : ℝ → ℝ} (hg : IntegrableOn g s)
    (hfg : ∀ t ∈ s, ‖f t‖ ≤ g t) : IntegrableOn f s :=
  Integrable.mono' hg hf.aestronglyMeasurable ((ae_restrict_mem hs).mono hfg)

/-- The global kernel bound gives integrability on every finite vertical interval separated from
genuine poles and zeros; used by `integrable_fiveTermKernelUHP_of_separated`. -/
private theorem integrableOn_kernelUHP_vertical_Icc
    (γ : SL(2, ℤ)) (ℓ p : ℤ) (w y τ : ℂ) (hτ : 0 < τ.im) (m : ℤ)
    (x δ : ℝ) (hδ : 0 < δ)
    (hR : ∀ t : ℝ, ∀ u ∈ faddeevModularUHPPoles γ (m + 1) τ,
      δ ≤ ‖((x : ℂ) + t * I) - u‖)
    (hL : ∀ t : ℝ, ∀ u ∈ faddeevModularUHPZeros γ (m + p) τ,
      δ ≤ ‖((x : ℂ) + t * I) + y - u‖) (a b : ℝ) :
    IntegrableOn (fun t : ℝ => fiveTermKernelUHP γ ℓ p w y τ m
      ((x : ℂ) + t * I)) (Icc a b) := by
  let z : ℝ → ℂ := fun t => (x : ℂ) + t * I
  let E : ℂ → ℝ := fiveTermGrowthExponent γ ℓ p m w y τ
  obtain ⟨C, hC⟩ := exists_norm_fiveTermKernelUHP_le γ ℓ p w y τ hτ m δ hδ
  have hz : Continuous z := by fun_prop
  have hE : Continuous E :=
    continuous_fiveTermKernelUHP_growthExponent γ ℓ p m w y τ
  have hdom : IntegrableOn (fun t : ℝ => C * Real.exp (E (z t))) (Icc a b) :=
    (continuous_const.mul (Real.continuous_exp.comp (hE.comp hz))).integrableOn_Icc
  apply fiveTerm_integrableOn_of_bound
    ((measurable_fiveTermKernelUHP γ ℓ p w y τ hτ m).comp hz.measurable)
    measurableSet_Icc hdom
  intro t _
  exact hC (z t) (hR t) (hL t)

/-- The two tails and the finite middle interval cover the line; used by
`integrable_fiveTermKernelUHP_of_separated`. -/
private lemma fiveTerm_integrable_of_three_regions {f : ℝ → ℂ} {T : ℝ}
    (hlower : IntegrableOn f (Iic (-T))) (hmiddle : IntegrableOn f (Icc (-T) T))
    (hupper : IntegrableOn f (Ioi T)) : Integrable f := by
  have hcover : (Iic (-T) ∪ (Icc (-T) T ∪ Ioi T) : Set ℝ) = univ := by
    ext t
    simp only [mem_union, mem_Iic, mem_Icc, mem_Ioi, mem_univ, iff_true]
    by_cases ht : t ≤ -T
    · exact Or.inl ht
    · by_cases hT : t ≤ T
      · exact Or.inr (Or.inl ⟨(lt_of_not_ge ht).le, hT⟩)
      · exact Or.inr (Or.inr (lt_of_not_ge hT))
  rw [← integrableOn_univ, ← hcover, integrableOn_union, integrableOn_union]
  exact ⟨hlower, hmiddle, hupper⟩

/-- An exponential upper-tail estimate with a negative rate is integrable. -/
private lemma fiveTerm_integrableOn_upper_of_exponential_bound {f : ℝ → ℂ}
    (hf : Measurable f) {C a T₀ T : ℝ} (ha : a < 0) (hT : T₀ ≤ T)
    (hbound : ∀ t, T₀ ≤ t → ‖f t‖ ≤ C * Real.exp (a * t)) :
    IntegrableOn f (Ioi T) := by
  apply fiveTerm_integrableOn_of_bound hf measurableSet_Ioi
    ((integrableOn_exp_mul_Ioi ha T).const_mul C)
  intro t ht
  exact hbound t (hT.trans ht.le)

/-- An exponential lower-tail estimate with a positive rate is integrable. -/
private lemma fiveTerm_integrableOn_lower_of_exponential_bound {f : ℝ → ℂ}
    (hf : Measurable f) {C a T₀ T : ℝ} (ha : 0 < a) (hT : T₀ ≤ T)
    (hbound : ∀ t, t ≤ -T₀ → ‖f t‖ ≤ C * Real.exp (a * t)) :
    IntegrableOn f (Iic (-T)) := by
  apply fiveTerm_integrableOn_of_bound hf measurableSet_Iic
    ((integrableOn_exp_mul_Iic ha (-T)).const_mul C)
  intro t ht
  exact hbound t (ht.trans (neg_le_neg hT))

/-- Absolute convergence of the vertical integral of `K_m` under `Re ε > 0`,
`Re λ > 0`, `Re μ < 0`, and separation from its genuine right and left poles.
[RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`, proof of Theorem 3,
`thm:5term.mod.fad`]; the lower condition uses `μ = c(w+y)/ε+ℓ+p-1`. -/
theorem integrable_fiveTermKernelUHP_of_separated
    (γ : SL(2, ℤ)) (ℓ p : ℤ) (w y τ : ℂ) (hτ : 0 < τ.im) (m : ℤ)
    (he : 0 < (fltDenominator (γ : Mat(2, ℤ)) τ).re)
    (hLam : 0 < ((((γ 1 0 : ℤ) : ℂ) * w /
      fltDenominator (γ : Mat(2, ℤ)) τ + ℓ)).re)
    (hMu : ((((γ 1 0 : ℤ) : ℂ) * (w + y) /
      fltDenominator (γ : Mat(2, ℤ)) τ + ℓ + p - 1)).re < 0)
    (x δ : ℝ) (hδ : 0 < δ)
    (hR : ∀ t : ℝ, ∀ u ∈ faddeevModularUHPPoles γ (m + 1) τ,
      δ ≤ ‖((x : ℂ) + t * I) - u‖)
    (hL : ∀ t : ℝ, ∀ u ∈ faddeevModularUHPZeros γ (m + p) τ,
      δ ≤ ‖((x : ℂ) + t * I) + y - u‖) :
    Integrable (fun t : ℝ => fiveTermKernelUHP γ ℓ p w y τ m
      ((x : ℂ) + t * I)) := by
  let f : ℝ → ℂ := fun t => fiveTermKernelUHP γ ℓ p w y τ m ((x : ℂ) + t * I)
  have hf : Measurable f :=
    (measurable_fiveTermKernelUHP γ ℓ p w y τ hτ m).comp (by fun_prop)
  obtain ⟨Cu, Tu, hu⟩ :=
    exists_norm_fiveTermKernelUHP_vertical_Ici γ ℓ p w y τ hτ m he x
  obtain ⟨Cl, Tl, hl⟩ :=
    exists_norm_fiveTermKernelUHP_vertical_Iic γ ℓ p w y τ hτ m he x
  let T := max Tu Tl
  have hau : -2 * π *
      ((((γ 1 0 : ℤ) : ℂ) * w / fltDenominator (γ : Mat(2, ℤ)) τ + ℓ)).re < 0 := by
    nlinarith [Real.pi_pos, hLam]
  have hal : 0 < -2 * π *
      ((((γ 1 0 : ℤ) : ℂ) * (w + y) /
        fltDenominator (γ : Mat(2, ℤ)) τ + ℓ + p - 1)).re := by
    nlinarith [Real.pi_pos, hMu]
  have hupper : IntegrableOn f (Ioi T) :=
    fiveTerm_integrableOn_upper_of_exponential_bound hf hau (le_max_left _ _) hu
  have hlower : IntegrableOn f (Iic (-T)) :=
    fiveTerm_integrableOn_lower_of_exponential_bound hf hal (le_max_right _ _) hl
  have hmiddle : IntegrableOn f (Icc (-T) T) :=
    integrableOn_kernelUHP_vertical_Icc
      γ ℓ p w y τ hτ m x δ hδ hR hL (-T) T
  exact fiveTerm_integrable_of_three_regions hlower hmiddle hupper

/-! ### The concrete vertical contour

The real inequalities supply the uniform separation required by the integrability theorem. -/

/-- The vertical integral of `K_m(x+it)` is absolutely convergent when `Re ε > 0`,
`Re(cw/ε+ℓ) > 0`, `Re(c(w+y)/ε+ℓ+p-1) < 0`, the line lies to the right of the shifted left
poles, and it meets no genuine right pole; finitely many right poles may lie to its left.
This is `integrable_fiveTermKernelUHP_of_separated` with the separation of
`exists_pos_dist_fiveTerm_of_regular`. -/
theorem integrable_fiveTermKernelUHP_of_regular
    (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (ℓ p m : ℤ) (w y τ : ℂ)
    (hτ : 0 < τ.im) (he : 0 < (fltDenominator (γ : Mat(2, ℤ)) τ).re)
    (hLam : 0 < ((((γ 1 0 : ℤ) : ℂ) * w /
      fltDenominator (γ : Mat(2, ℤ)) τ + ℓ)).re)
    (hMu : ((((γ 1 0 : ℤ) : ℂ) * (w + y) /
      fltDenominator (γ : Mat(2, ℤ)) τ + ℓ + p - 1)).re < 0)
    (x : ℝ)
    (hxP : ∀ u ∈ faddeevModularUHPPoles γ (m + 1) τ, u.re ≠ x)
    (hxL : (-((m + p : ℤ) : ℝ) * (fltDenominator (γ : Mat(2, ℤ)) τ).re - 1) /
      (γ 1 0 : ℝ) - y.re < x) :
    Integrable (fun t : ℝ => fiveTermKernelUHP γ ℓ p w y τ m
      ((x : ℂ) + t * I)) := by
  obtain ⟨δ, hδ, hsep⟩ :=
    exists_pos_dist_fiveTerm_of_regular γ hc m p y τ hτ he x hxP hxL
  exact integrable_fiveTermKernelUHP_of_separated
    γ ℓ p w y τ hτ m he hLam hMu x δ hδ
    (fun t u hu => (hsep t).1 u hu) (fun t u hu => (hsep t).2 u hu)

end SIC
