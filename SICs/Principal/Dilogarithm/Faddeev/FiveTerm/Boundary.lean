/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Analysis.CompactConvergence
import SICs.Principal.Dilogarithm.Faddeev.Boundary
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.Kernel
import SICs.SpecialFunctions.Faddeev.FiveTerm.Kernel

/-!
# Principal five-term contours at the real boundary

The complex-period principal kernel agrees almost everywhere with the upper-half-plane kernel,
its regular real-period vertical contours are integrable under strict decay, and finite
vertical contour integrals converge at the principal real period.

This module follows the boundary passage of [RW26, Radchenko, Wheeler (2026),
Theorem 3, `thm:5term.mod.fad`, equation (23), `eq:5term.int`], with the three-generator
expression of equation (20), `eq:modulartofaddeevCF`.

## The argument

For each fixed upper-half-plane period, the q-product and generator expressions agree
outside a countable subset of every affine real contour. Thus their integrals agree.
At the real period, choose a vertical line whose real crossing and its translate by `y`
are outside `ℤ+ℤρ_d`. Every generator factor is then regular along the whole line, and
the denominator product is nonzero. Joint continuity and compactness yield a common
bound on each finite segment, including its real-axis crossing. Dominated convergence
passes the finite integrals to `ρ_d`. Off the real axis the lattice `ℤ+ℤρ_d` is absent, so
horizontal segments at nonzero height converge in the same way, and so do the boundary integrals
of rectangles whose vertical sides cross the real axis at regular crossings. At `ρ_d`, the two
known exponential tail bounds and continuity on the compact middle give integrability on the
entire vertical line. The limit theorems here concern finite intervals only. Uniform
complex-period estimates on both infinite tails and the resulting improper-integral passage are
supplied in
`SICs.Principal.Dilogarithm.Faddeev.FiveTerm.ImproperBoundary`.
-/

noncomputable section

open Complex Filter Topology MeasureTheory Set
open scoped MatrixGroups

namespace SIC

/-! ### Boundary identities and regularity

Equation (20) identifies the two modular factors almost everywhere at each upper-half-plane
period. At the real fixed point their generator forms give the real principal kernel.
-/

/-- The complex-period three-generator form of the principal kernel of
[RW26, Radchenko, Wheeler (2026), equation (23), `eq:5term.int`] at `n=h=0`.
The phase uses the actual Jacobi denominator `j_{A_d}(τ)`. -/
def principalFiveTermKernelComplex (d : ℕ) (ℓ p : ℤ) (w y τ : ℂ)
    (m : ℤ) (z : ℂ) : ℂ :=
  principalFaddeevComplex d (m + 1) 0 z τ /
    principalFaddeevComplex d (m + p) 0 (z + y) τ *
      Complex.exp (2 * Real.pi * I *
        (((((principalA d) 1 0 : ℤ) : ℂ) * z +
              fltDenominator (principalA d : Mat(2, ℤ)) τ * m) * w /
            fltDenominator (principalA d : Mat(2, ℤ)) τ + ℓ * (z + m * τ)))

/-- At `τ=ρ_d`, the variable-period kernel becomes the real principal kernel;
this uses `principalFaddeevComplex_principalRoot` and `j_{A_d}(ρ_d)=ρ_d³`. -/
theorem principalFiveTermKernelComplex_principalRoot (d : ℕ) (hd : 3 < d)
    (ℓ p m : ℤ) (w y : ℝ) (z : ℂ) :
    principalFiveTermKernelComplex d ℓ p w y (principalRoot d) m z =
      principalFiveTermKernel d ℓ p w y m z := by
  have hJ := fltDenominator_principalA_principalRoot_complex d hd
  have hc : (((principalA d) 1 0 : ℤ) : ℂ) =
      (d : ℂ) * ((d : ℂ) - 2) := by simp [coe_principalA]
  simp only [principalFiveTermKernelComplex, principalFiveTermKernel,
    principalFaddeevComplex_principalRoot d hd, hc]
  change _ = principalFaddeev d (m + 1) 0 z /
      principalFaddeev d (m + p) 0 (z + y) *
        Complex.exp (2 * Real.pi * I *
          ((((d : ℂ) * ((d : ℂ) - 2) * z + (principalRoot d : ℂ) ^ 3 * m) * w) /
            (principalRoot d : ℂ) ^ 3 + ℓ * (z + m * (principalRoot d : ℂ))))
  congr 1
  congr 1
  rw [hJ]

/-- For each fixed upper-half-plane period the two principal kernel expressions agree
almost everywhere on `z=a t+b`, `a≠0`. This applies
`ae_faddeevModularUHP_principalA` to both modular factors of equation (23). -/
theorem ae_kernelUHP_principalA (d : ℕ)
    (ℓ p m : ℤ) (w y τ a b : ℂ) (hτ : 0 < τ.im) (ha : a ≠ 0) :
    ∀ᵐ t : ℝ, fiveTermKernelUHP (principalA d) ℓ p w y τ m (a * t + b) =
      principalFiveTermKernelComplex d ℓ p w y τ m (a * t + b) := by
  have hn := ae_faddeevModularUHP_principalA
    d (m + 1) 0 τ a b hτ ha
  have hden := ae_faddeevModularUHP_principalA
    d (m + p) 0 τ a (b + y) hτ ha
  filter_upwards [hn, hden] with t hnt hdt
  have harg : (a * (t : ℂ) + b) + y = a * t + (b + y) := by ring
  rw [fiveTermKernelUHP, principalFiveTermKernelComplex, hnt, harg, hdt]

/-- On a vertical line, the upper-half-plane kernel equals the generator kernel almost
everywhere for each fixed period. -/
theorem ae_kernelUHP_principalA_vertical
    (d : ℕ) (ℓ p m : ℤ)
    (w y x : ℝ) (τ : ℂ) (hτ : 0 < τ.im) :
    ∀ᵐ t : ℝ,
      fiveTermKernelUHP (principalA d) ℓ p w y τ m (x + t * I) =
        principalFiveTermKernelComplex d ℓ p w y τ m (x + t * I) := by
  have h := ae_kernelUHP_principalA d ℓ p m w y τ I x
    hτ Complex.I_ne_zero
  have harg (t : ℝ) : I * (t : ℂ) + x = (x : ℂ) + t * I := by ring
  simpa only [harg] using h

/-- Measurability on an affine real contour; used by
`aestronglyMeasurable_principalFiveTermKernelComplex` and
`tendsto_intervalIntegral_kernelUHP_principalA_horizontal`. -/
private lemma aestronglyMeasurable_kernelComplex_affine
    (d : ℕ) (ℓ p m : ℤ) (w y : ℝ) (τ c b : ℂ)
    (hτ : 0 < τ.im) (hc : c ≠ 0) :
    AEStronglyMeasurable (fun t : ℝ =>
      principalFiveTermKernelComplex d ℓ p w y τ m (c * t + b)) := by
  have hz : Measurable (fun t : ℝ => c * (t : ℂ) + b) := by fun_prop
  have hk : Measurable (fun t : ℝ =>
      fiveTermKernelUHP (principalA d) ℓ p w y τ m (c * t + b)) :=
    (measurable_fiveTermKernelUHP (principalA d) ℓ p w y τ hτ m).comp hz
  exact hk.aestronglyMeasurable.congr
    (ae_kernelUHP_principalA d ℓ p m w y τ c b hτ hc)

/-- At a fixed upper-half-plane period, the complex generator kernel is almost everywhere
strongly measurable on the whole vertical line. -/
theorem aestronglyMeasurable_principalFiveTermKernelComplex
    (d : ℕ) (ℓ p m : ℤ) (w y x : ℝ) (τ : ℂ) (hτ : 0 < τ.im) :
    AEStronglyMeasurable (fun t : ℝ =>
      principalFiveTermKernelComplex d ℓ p w y τ m ((x : ℂ) + t * I)) := by
  have h := aestronglyMeasurable_kernelComplex_affine
    d ℓ p m w y τ I x hτ Complex.I_ne_zero
  have harg (t : ℝ) : I * (t : ℂ) + x = (x : ℂ) + t * I := by ring
  simpa only [harg] using h

/-- For complex `w,y`, the principal kernel varies jointly in `z,τ` at its real period
when `z` and `z+y` are outside `ℤ+ℤρ_d`. This uses the regular factors in
`continuousAt_principalFaddeevComplex_of_notMem`. -/
theorem continuousAt_principalFiveTermKernelComplex (d : ℕ) (hd : 3 < d)
    (ℓ p m : ℤ) (w y z : ℂ)
    (hz : ¬ IsPeriodLatticePoint (principalRoot d) z)
    (hzy : ¬ IsPeriodLatticePoint (principalRoot d) (z + y)) :
    ContinuousAt (fun q : ℂ × ℂ =>
      principalFiveTermKernelComplex d ℓ p w y q.2 m q.1)
      (z, (principalRoot d : ℂ)) := by
  have hn := continuousAt_principalFaddeevComplex_of_notMem
    d hd (m + 1) 0 z hz
  have harg : ContinuousAt
      (fun q : ℂ × ℂ => (q.1 + y, q.2))
      (z, (principalRoot d : ℂ)) := by fun_prop
  have hden0 := continuousAt_principalFaddeevComplex_of_notMem
    d hd (m + p) 0 (z + y) hzy
  have hden : ContinuousAt (fun q : ℂ × ℂ =>
      principalFaddeevComplex d (m + p) 0 (q.1 + y) q.2)
      (z, (principalRoot d : ℂ)) := by
    simpa only [Function.comp_def] using hden0.comp_of_eq harg rfl
  have hnonzero : principalFaddeevComplex d (m + p) 0
      (z + y) (principalRoot d) ≠ 0 := by
    rw [principalFaddeevComplex_principalRoot d hd]
    exact principalFaddeev_ne_zero_of_notMem d hd _ _ _ hzy
  have hJ := fltDenominator_principalA_principalRoot_ne_zero d hd
  have hphase := continuousAt_fiveTermPhase (principalA d) ℓ m w z
    (principalRoot d : ℂ) hJ
  exact (hn.div hden hnonzero).mul hphase

/-! ### Regular vertical contours

The real crossings control lattice avoidance on the entire line. Joint continuity then
supplies both the compact middle of the real integral and finite-segment limits.
-/

/-- The complex kernel is jointly continuous in the contour height and period along a
vertical line with two lattice-free real crossings. -/
theorem continuousAt_principalFiveTermKernelComplex_vertical
    (d : ℕ) (hd : 3 < d)
    (ℓ p m : ℤ) (w y x t : ℝ)
    (hx : ¬ IsPeriodLatticePoint (principalRoot d) (x : ℂ))
    (hxy : ¬ IsPeriodLatticePoint (principalRoot d) ((x : ℂ) + y)) :
    ContinuousAt (fun q : ℝ × ℂ =>
      principalFiveTermKernelComplex d ℓ p w y q.2 m (x + q.1 * I))
      (t, (principalRoot d : ℂ)) := by
  have hz := not_isPeriodLatticePoint_vertical (principalRoot d) x t hx
  have hshift : ((x : ℂ) + (t : ℂ) * I) + y =
      ((x + y : ℝ) : ℂ) + t * I := by push_cast; ring
  have hzy : ¬ IsPeriodLatticePoint (principalRoot d)
      (((x : ℂ) + t * I) + y) := by
    rw [hshift]
    exact not_isPeriodLatticePoint_vertical (principalRoot d) (x + y) t
      (by simpa only [Complex.ofReal_add] using hxy)
  have h := continuousAt_principalFiveTermKernelComplex d hd ℓ p m w y
    ((x : ℂ) + t * I) hz hzy
  have harg : ContinuousAt (fun q : ℝ × ℂ =>
      ((x : ℂ) + q.1 * I, q.2)) (t, (principalRoot d : ℂ)) := by fun_prop
  simpa only [Function.comp_def] using h.comp_of_eq harg rfl

/-- The real-period kernel is continuous along a regular vertical contour. -/
lemma continuous_principalFiveTermKernel_vertical (d : ℕ) (hd : 3 < d)
    (ℓ p m : ℤ) (w y x : ℝ)
    (hx : ¬ IsPeriodLatticePoint (principalRoot d) (x : ℂ))
    (hxy : ¬ IsPeriodLatticePoint (principalRoot d) ((x : ℂ) + y)) :
    Continuous (fun t : ℝ =>
      principalFiveTermKernel d ℓ p w y m ((x : ℂ) + t * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have h := continuousAt_principalFiveTermKernelComplex_vertical
    d hd ℓ p m w y x t hx hxy
  have hs : ContinuousAt (fun s : ℝ => (s, (principalRoot d : ℂ))) t :=
    continuousAt_id.prodMk continuousAt_const
  simpa only [Function.comp_def, principalFiveTermKernelComplex_principalRoot
    d hd ℓ p m w y] using h.comp_of_eq hs rfl

/-- On a vertical line whose two real crossings avoid `ℤ+ℤρ_d`, the real-period
kernel is integrable when `λ>0` and `μ<0`. This completes the two tail results
`integrableOn_principalFiveTermKernel_upper` and
`integrableOn_principalFiveTermKernel_lower` by regularity on a compact middle. -/
theorem integrable_principalFiveTermKernel (d : ℕ) (hd : 3 < d)
    (ℓ p m : ℤ) (w y x : ℝ)
    (hx : ¬ IsPeriodLatticePoint (principalRoot d) (x : ℂ))
    (hxy : ¬ IsPeriodLatticePoint (principalRoot d) ((x : ℂ) + y))
    (hupper : 0 < principalFiveTermUpperRate d ℓ w)
    (hlower : principalFiveTermLowerRate d ℓ p w y < 0) :
    Integrable (fun t : ℝ =>
      principalFiveTermKernel d ℓ p w y m ((x : ℂ) + t * I)) := by
  let f : ℝ → ℂ := fun t =>
    principalFiveTermKernel d ℓ p w y m ((x : ℂ) + t * I)
  obtain ⟨T₁, hupperT⟩ :=
    integrableOn_principalFiveTermKernel_upper d hd ℓ p m w y x hupper
  obtain ⟨T₂, hlowerT⟩ :=
    integrableOn_principalFiveTermKernel_lower d hd ℓ p m w y x hlower
  let a := min (-T₂) T₁
  let b := max (-T₂) T₁
  have ha : IntegrableOn f (Iio a) :=
    hlowerT.mono_set (Iio_subset_Iio (min_le_left _ _))
  have hb : IntegrableOn f (Ioi b) :=
    hupperT.mono_set (Ioi_subset_Ioi (le_max_right _ _))
  have hm : IntegrableOn f (Icc a b) :=
    (continuous_principalFiveTermKernel_vertical d hd ℓ p m w y x hx hxy).continuousOn
      |>.integrableOn_Icc
  have hab : a ≤ b := (min_le_left _ _).trans (le_max_left _ _)
  change Integrable f
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := b),
    ← Set.Iio_union_Icc_eq_Iic hab]
  exact (ha.union hm).union hb

/-! ### Finite contour limits

Joint continuity controls each finite vertical segment through a regular crossing and each
finite horizontal segment off the real axis, and the upper-half-plane modular kernel may be
replaced by the generator kernel under a finite integral. The four sides of a rectangle then
converge together.
-/

/-- At a fixed upper-half-plane period, the generator kernel times the vertical differential is
almost everywhere strongly measurable on a finite interval. -/
private lemma aestronglyMeasurable_kernelComplex_vertical_mul_I
    (d : ℕ) (ℓ p m : ℤ) (w y x a b : ℝ) (τ : ℂ) (hτ : 0 < τ.im) :
    AEStronglyMeasurable (fun t : ℝ =>
      principalFiveTermKernelComplex d ℓ p w y τ m (x + t * I) * I)
      (volume.restrict (Set.uIoc a b)) := by
  exact (aestronglyMeasurable_principalFiveTermKernelComplex
    d ℓ p m w y x τ hτ).mul_const I |>.restrict

/-- Equality of the modular and generator integrals on an affine contour; used by
`intervalIntegral_kernelUHP_eq_complex` and
`tendsto_intervalIntegral_kernelUHP_principalA_horizontal`. -/
private lemma intervalIntegral_kernelUHP_eq_complex_affine
    (d : ℕ) (ℓ p m : ℤ) (w y : ℝ) (τ c b k : ℂ) (s₁ s₂ : ℝ)
    (hτ : 0 < τ.im) (hc : c ≠ 0) :
    (∫ t in s₁..s₂,
      fiveTermKernelUHP (principalA d) ℓ p w y τ m (c * t + b) * k) =
      ∫ t in s₁..s₂,
        principalFiveTermKernelComplex d ℓ p w y τ m (c * t + b) * k := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [ae_kernelUHP_principalA
    d ℓ p m w y τ c b hτ hc]
    with t ht _
  rw [ht]

/-- At a fixed upper-half-plane period, the modular and generator kernels have
equal integrals over every finite vertical segment. -/
private lemma intervalIntegral_kernelUHP_eq_complex
    (d : ℕ) (ℓ p m : ℤ) (w y x a b : ℝ) (τ : ℂ) (hτ : 0 < τ.im) :
    (∫ t in a..b,
      fiveTermKernelUHP (principalA d) ℓ p w y τ m (x + t * I) * I) =
      ∫ t in a..b,
        principalFiveTermKernelComplex d ℓ p w y τ m (x + t * I) * I := by
  have h := intervalIntegral_kernelUHP_eq_complex_affine
    d ℓ p m w y τ I x I a b hτ Complex.I_ne_zero
  have harg (t : ℝ) : I * (t : ℂ) + x = (x : ℂ) + t * I := by ring
  simpa only [harg] using h

/-- The upper-half-plane principal contour integral over each finite segment converges to
the real-period integral, with `dz=i dt`, oriented from `a` to `b` (upward if `a≤b`).
Specializes `tendsto_intervalIntegral_of_continuousAt_prod` using the almost-everywhere
kernel comparison; its hypotheses allow the finite segment to cross the real axis. -/
theorem tendsto_intervalIntegral_kernelUHP_principalA
    (d : ℕ) (hd : 3 < d) (ℓ p m : ℤ) (w y x a b : ℝ)
    (hx : ¬ IsPeriodLatticePoint (principalRoot d) (x : ℂ))
    (hxy : ¬ IsPeriodLatticePoint (principalRoot d) ((x : ℂ) + y)) :
    Tendsto
      (fun τ : ℂ => ∫ t in a..b,
        fiveTermKernelUHP (principalA d) ℓ p w y τ m (x + t * I) * I)
      (𝓝[{τ : ℂ | 0 < τ.im}] (principalRoot d : ℂ))
      (𝓝 (∫ t in a..b,
        principalFiveTermKernel d ℓ p w y m (x + t * I) * I)) := by
  let U : Set ℂ := {τ | 0 < τ.im}
  have hf : ∀ t ∈ Set.uIcc a b, ContinuousAt
      (fun q : ℝ × ℂ =>
        principalFiveTermKernelComplex d ℓ p w y q.2 m (x + q.1 * I) * I)
      (t, (principalRoot d : ℂ)) := by
    intro t _
    exact (continuousAt_principalFiveTermKernelComplex_vertical
      d hd ℓ p m w y x t hx hxy).mul continuousAt_const
  have hmeas : ∀ᶠ τ in 𝓝[U] (principalRoot d : ℂ),
      AEStronglyMeasurable (fun t : ℝ =>
        principalFiveTermKernelComplex d ℓ p w y τ m (x + t * I) * I)
        (volume.restrict (Set.uIoc a b)) := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact aestronglyMeasurable_kernelComplex_vertical_mul_I
      d ℓ p m w y x a b τ hτ
  have hlim := tendsto_intervalIntegral_of_continuousAt_prod
    nhdsWithin_le_nhds a b hf hmeas
  have heq : (fun τ : ℂ => ∫ t in a..b,
      fiveTermKernelUHP (principalA d) ℓ p w y τ m (x + t * I) * I) =ᶠ[
      𝓝[U] (principalRoot d : ℂ)] (fun τ : ℂ => ∫ t in a..b,
      principalFiveTermKernelComplex d ℓ p w y τ m (x + t * I) * I) := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact intervalIntegral_kernelUHP_eq_complex
      d ℓ p m w y x a b τ hτ
  apply Filter.Tendsto.congr' heq.symm
  simpa only [principalFiveTermKernelComplex_principalRoot d hd ℓ p m w y]
    using hlim

/-- Joint continuity on a horizontal contour away from the real axis; used by
`tendsto_intervalIntegral_kernelUHP_principalA_horizontal`. -/
private lemma continuousAt_kernelComplex_horizontal
    (d : ℕ) (hd : 3 < d) (ℓ p m : ℤ) (w y a s : ℝ) (ha : a ≠ 0) :
    ContinuousAt (fun q : ℝ × ℂ =>
      principalFiveTermKernelComplex d ℓ p w y q.2 m (q.1 + a * I))
      (s, (principalRoot d : ℂ)) := by
  have hz_im : (((s : ℂ) + a * I)).im = a := by simp
  have hzy_im : ((((s : ℂ) + a * I) + y)).im = a := by simp
  have hz_nonzero : (((s : ℂ) + a * I)).im ≠ 0 := by
    rw [hz_im]
    exact ha
  have hzy_nonzero : ((((s : ℂ) + a * I) + y)).im ≠ 0 := by
    rw [hzy_im]
    exact ha
  have hz := not_isPeriodLatticePoint_of_im_ne_zero
    ((s : ℂ) + a * I) (principalRoot d) hz_nonzero
  have hzy := not_isPeriodLatticePoint_of_im_ne_zero
    (((s : ℂ) + a * I) + y) (principalRoot d) hzy_nonzero
  have h := continuousAt_principalFiveTermKernelComplex
    d hd ℓ p m w y ((s : ℂ) + a * I) hz hzy
  have harg : ContinuousAt (fun q : ℝ × ℂ =>
      ((q.1 : ℂ) + a * I, q.2)) (s, (principalRoot d : ℂ)) := by fun_prop
  simpa only [Function.comp_def] using h.comp_of_eq harg rfl

/-- The upper-half-plane principal contour integral over a finite horizontal segment at a
nonzero height `a` converges to the real-period integral: the segment avoids the real lattice
`ℤ+ℤρ_d` and so does its translate by `y`. The horizontal counterpart of
`tendsto_intervalIntegral_kernelUHP_principalA`. -/
theorem tendsto_intervalIntegral_kernelUHP_principalA_horizontal
    (d : ℕ) (hd : 3 < d) (ℓ p m : ℤ) (w y a s₁ s₂ : ℝ) (ha : a ≠ 0) :
    Tendsto
      (fun τ : ℂ => ∫ s in s₁..s₂,
        fiveTermKernelUHP (principalA d) ℓ p w y τ m (s + a * I))
      (𝓝[{τ : ℂ | 0 < τ.im}] (principalRoot d : ℂ))
      (𝓝 (∫ s in s₁..s₂, principalFiveTermKernel d ℓ p w y m (s + a * I))) := by
  let U : Set ℂ := {τ | 0 < τ.im}
  have hf : ∀ s ∈ Set.uIcc s₁ s₂, ContinuousAt
      (fun q : ℝ × ℂ =>
        principalFiveTermKernelComplex d ℓ p w y q.2 m (q.1 + a * I))
      (s, (principalRoot d : ℂ)) := by
    intro s _
    exact continuousAt_kernelComplex_horizontal
      d hd ℓ p m w y a s ha
  have hmeas : ∀ᶠ τ in 𝓝[U] (principalRoot d : ℂ),
      AEStronglyMeasurable (fun s : ℝ =>
        principalFiveTermKernelComplex d ℓ p w y τ m (s + a * I))
        (volume.restrict (Set.uIoc s₁ s₂)) := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have h := aestronglyMeasurable_kernelComplex_affine
      d ℓ p m w y τ 1 (a * I) hτ one_ne_zero
    simpa only [one_mul] using (h.restrict (s := Set.uIoc s₁ s₂))
  have hlim := tendsto_intervalIntegral_of_continuousAt_prod
    nhdsWithin_le_nhds s₁ s₂ hf hmeas
  have heq : (fun τ : ℂ => ∫ s in s₁..s₂,
      fiveTermKernelUHP (principalA d) ℓ p w y τ m (s + a * I)) =ᶠ[
      𝓝[U] (principalRoot d : ℂ)] (fun τ : ℂ => ∫ s in s₁..s₂,
      principalFiveTermKernelComplex d ℓ p w y τ m (s + a * I)) := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have h := intervalIntegral_kernelUHP_eq_complex_affine
      d ℓ p m w y τ 1 (a * I) 1 s₁ s₂ hτ one_ne_zero
    simpa only [one_mul, mul_one] using h
  apply Filter.Tendsto.congr' heq.symm
  simpa only [principalFiveTermKernelComplex_principalRoot d hd ℓ p m w y]
    using hlim

/-- The boundary integral of the upper-half-plane principal kernel over a rectangle whose
horizontal sides lie off the real axis and whose vertical sides cross it at regular crossings
converges to that of the real-period kernel, side by side. -/
theorem tendsto_rectBoundaryIntegral_kernelUHP_principalA
    (d : ℕ) (hd : 3 < d) (ℓ p m : ℤ) (w y : ℝ) (z₁ z₂ : ℂ)
    (h₁ : z₁.im ≠ 0) (h₂ : z₂.im ≠ 0)
    (hx₁ : IsRegularPeriodLatticeCrossing (principalRoot d) y z₁.re)
    (hx₂ : IsRegularPeriodLatticeCrossing (principalRoot d) y z₂.re) :
    Tendsto (fun τ : ℂ =>
      rectBoundaryIntegral (fiveTermKernelUHP (principalA d) ℓ p w y τ m) z₁ z₂)
      (𝓝[{τ : ℂ | 0 < τ.im}] (principalRoot d : ℂ))
      (𝓝 (rectBoundaryIntegral (principalFiveTermKernel d ℓ p w y m) z₁ z₂)) := by
  have hbottom := tendsto_intervalIntegral_kernelUHP_principalA_horizontal
    d hd ℓ p m w y z₁.im z₁.re z₂.re h₁
  have htop := tendsto_intervalIntegral_kernelUHP_principalA_horizontal
    d hd ℓ p m w y z₂.im z₁.re z₂.re h₂
  have hright := tendsto_intervalIntegral_kernelUHP_principalA
    d hd ℓ p m w y z₂.re z₁.im z₂.im hx₂.base hx₂.shifted
  have hleft := tendsto_intervalIntegral_kernelUHP_principalA
    d hd ℓ p m w y z₁.re z₁.im z₂.im hx₁.base hx₁.shifted
  simp only [intervalIntegral.integral_mul_const] at hright hleft
  simpa only [rectBoundaryIntegral, smul_eq_mul, mul_comm I] using
    ((hbottom.sub htop).add hright).sub hleft

end SIC
