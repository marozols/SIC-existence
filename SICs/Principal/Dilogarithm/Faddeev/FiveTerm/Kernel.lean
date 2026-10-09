/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Dilogarithm.Faddeev.Asymptotics
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The principal five-term kernel on vertical tails

The real-period five-term kernel has exponential bounds on both vertical tails, and each tail
is integrable under its corresponding strict decay condition. Its named finite integral sum is
the straight-contour left side of the principal five-term identity.

This module follows [RW26, Radchenko, Wheeler (2026), Theorem 3, `thm:5term.mod.fad`,
equation (23), `eq:5term.int`] at `γ = A_d`, `τ = ρ_d`, and `n = h = 0`.

## The argument

The kernel is meromorphic as a quotient of the two principal products times an entire,
nonvanishing phase exponential. Its divisor is therefore the numerator divisor minus the
shifted denominator divisor.

On an upper vertical tail, each principal product tends to one by the upper clause of Lemma 1,
so their ratio is bounded. On a lower tail, divide each product by its exact reflected
exponential; the normalized products tend to nonzero constants by the lower clause. The
quadratic terms in the two reflection exponents cancel, leaving the slope
`c(w+y)/ρ_d³+ℓ+p-1`, where `c=d(d-2)`. All remaining phase constants have modulus one for
real `w` and `y`. Measurability follows from meromorphicity, and the resulting real
exponential majorants give the two tail integrals.

For a finite family of real crossings `x_m`, the contour integral is parametrized by
`z=x_m+it`, so `dz=i dt`. The resulting sum is recorded by
`principalFiveTermIntegralSum` for use by the boundary and closed-form theorems.

The printed convergence condition in Theorem 3 omits `p` in the lower rate. We retain `p`,
as in the corrected general bound in `SICs.SpecialFunctions.Faddeev.FiveTerm.Bounds`.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace SIC

/-! ### The kernel and its rates

The phase is that of equation (23) with the principal matrix and real parameters. -/

/-- The logarithmic phase `(cz+εm)w/ε + ℓ(z+mρ_d)` of the principal five-term kernel in
[RW26, Radchenko, Wheeler (2026), equation (23), `eq:5term.int`], with `c = d(d-2)` and
`ε = ρ_d³`; the kernel multiplies its products by `e` of this phase. -/
def principalFiveTermPhase (d : ℕ) (ℓ : ℤ) (w : ℝ) (m : ℤ) (z : ℂ) : ℂ :=
  (((d : ℂ) * ((d : ℂ) - 2) * z + (principalRoot d : ℂ) ^ 3 * m) * w) /
    (principalRoot d : ℂ) ^ 3 + ℓ * (z + m * (principalRoot d : ℂ))

/-- The `m`-th principal five-term integrand at the real period `ρ_d`, before contour
integration. This is the summand in [RW26, Radchenko, Wheeler (2026), Theorem 3,
`thm:5term.mod.fad`, equation (23), `eq:5term.int`] at `A_d`, `τ=ρ_d`, and `n=h=0`. -/
def principalFiveTermKernel (d : ℕ) (ℓ p : ℤ) (w y : ℝ) (m : ℤ)
    (z : ℂ) : ℂ :=
  principalFaddeev d (m + 1) 0 z /
    principalFaddeev d (m + p) 0 (z + y) *
      Complex.exp (2 * Real.pi * I * principalFiveTermPhase d ℓ w m z)

/-- The real-period principal five-term kernel is meromorphic at every point,
by the meromorphy of its two Faddeev products and its entire exponential phase. -/
theorem meromorphicAt_principalFiveTermKernel
    (d : ℕ) (hd : 3 < d) (ℓ p m : ℤ) (w y : ℝ) (z : ℂ) :
    MeromorphicAt (principalFiveTermKernel d ℓ p w y m) z := by
  unfold principalFiveTermKernel
  apply MeromorphicAt.mul
  · apply MeromorphicAt.div
    · exact meromorphicAt_principalFaddeev d hd _ _ _
    · have h := (meromorphicAt_principalFaddeev d hd (m + p) 0 (z + y)).comp_analyticAt
        (g := fun ζ : ℂ => ζ + (y : ℂ))
        (show AnalyticAt ℂ (fun ζ : ℂ => ζ + (y : ℂ)) z by fun_prop)
      simpa only [Function.comp_def] using h
  · exact (show AnalyticAt ℂ
      (fun ζ => Complex.exp (2 * Real.pi * I * principalFiveTermPhase d ℓ w m ζ)) z by
        dsimp [principalFiveTermPhase]
        fun_prop).meromorphicAt


/-- The divisor of the principal five-term kernel is the numerator divisor minus
the shifted denominator divisor; the phase exponential has order zero. -/
theorem meromorphicOrderAt_principalFiveTermKernel
    (d : ℕ) (hd : 3 < d) (ℓ p m : ℤ) (w y : ℝ) (z : ℂ) :
    meromorphicOrderAt (principalFiveTermKernel d ℓ p w y m) z =
      meromorphicOrderAt (principalFaddeev d (m + 1) 0) z -
        meromorphicOrderAt (fun ζ : ℂ =>
          principalFaddeev d (m + p) 0 (ζ + y)) z := by
  let N : ℂ → ℂ := principalFaddeev d (m + 1) 0
  let D : ℂ → ℂ := fun ζ => principalFaddeev d (m + p) 0 (ζ + y)
  let E : ℂ → ℂ := fun ζ =>
    Complex.exp (2 * Real.pi * I * principalFiveTermPhase d ℓ w m ζ)
  have hN : MeromorphicAt N z := meromorphicAt_principalFaddeev d hd _ _ _
  have hD : MeromorphicAt D z := by
    have h := (meromorphicAt_principalFaddeev d hd (m + p) 0 (z + y)).comp_analyticAt
      (g := fun ζ : ℂ => ζ + (y : ℂ))
      (show AnalyticAt ℂ (fun ζ : ℂ => ζ + (y : ℂ)) z by fun_prop)
    simpa only [D, Function.comp_def] using h
  have hE : AnalyticAt ℂ E z := by dsimp [E, principalFiveTermPhase]; fun_prop
  have hEord : meromorphicOrderAt E z = 0 := by
    simp [hE.meromorphicOrderAt_eq,
      (hE.analyticOrderAt_eq_zero).mpr (Complex.exp_ne_zero _)]
  change meromorphicOrderAt ((N / D) * E) z = _
  rw [meromorphicOrderAt_mul (hN.div hD) hE.meromorphicAt,
    meromorphicOrderAt_div hN hD, hEord]
  simp only [add_zero, N, D]


/-- The finite sum of principal straight-contour integrals in
[RW26, Radchenko, Wheeler (2026), Theorem 3, `thm:5term.mod.fad`, equation (23),
`eq:5term.int`], parametrized by `z=x_m+it` and hence with the factor `i=dz/dt`. -/
def principalFiveTermIntegralSum (d : ℕ) (ℓ p : ℤ) (w y : ℝ)
    (x : Fin ((principalA d) 1 0).toNat → ℝ) : ℂ :=
  ∑ m : Fin ((principalA d) 1 0).toNat,
    I * (∫ t : ℝ, principalFiveTermKernel d ℓ p w y ((m : ℕ) : ℤ)
      ((x m : ℂ) + t * I))

/-- Expands the named principal straight-contour integral sum. -/
theorem principalFiveTermIntegralSum_def (d : ℕ) (ℓ p : ℤ) (w y : ℝ)
    (x : Fin ((principalA d) 1 0).toNat → ℝ) :
    principalFiveTermIntegralSum d ℓ p w y x =
      ∑ m : Fin ((principalA d) 1 0).toNat,
        I * (∫ t : ℝ, principalFiveTermKernel d ℓ p w y ((m : ℕ) : ℤ)
          ((x m : ℂ) + t * I)) := rfl

/-- The upper vertical decay rate `λ = d(d-2)w/ρ_d³ + ℓ`. -/
def principalFiveTermUpperRate (d : ℕ) (ℓ : ℤ) (w : ℝ) : ℝ :=
  (d : ℝ) * ((d : ℝ) - 2) * w / (principalRoot d) ^ 3 + ℓ

/-- At every point, the phase of the principal five-term kernel has imaginary part
$\lambda\operatorname{Im}z$, where $\lambda=d(d-2)w/\rho_d^3+\ell$. -/
theorem principalFiveTermPhase_im (d : ℕ) (ℓ m : ℤ) (w : ℝ) (z : ℂ) :
    (principalFiveTermPhase d ℓ w m z).im =
      principalFiveTermUpperRate d ℓ w * z.im := by
  simp [principalFiveTermPhase, principalFiveTermUpperRate, Complex.div_ofReal_im,
    Complex.mul_im, ← Complex.ofReal_pow]
  ring

/-- The phase exponential has modulus $\exp(-2\pi\lambda\operatorname{Im}z)$ for every $z$. -/
theorem norm_exp_principalFiveTermPhase (d : ℕ) (ℓ m : ℤ) (w : ℝ) (z : ℂ) :
    ‖Complex.exp (2 * Real.pi * I * principalFiveTermPhase d ℓ w m z)‖ =
      Real.exp ((-2 * Real.pi * principalFiveTermUpperRate d ℓ w) * z.im) := by
  rw [norm_exp_two_pi_I_mul, principalFiveTermPhase_im]
  congr 1
  ring

/-- The lower vertical decay rate `μ = d(d-2)(w+y)/ρ_d³ + ℓ+p-1`.
The `p` term corrects the printed convergence condition in
[RW26, Radchenko, Wheeler (2026), Theorem 3,
`thm:5term.mod.fad`]. -/
def principalFiveTermLowerRate (d : ℕ) (ℓ p : ℤ) (w y : ℝ) : ℝ :=
  (d : ℝ) * ((d : ℝ) - 2) * (w + y) / (principalRoot d) ^ 3 + ℓ + p - 1

/-! ### Phase calculations on vertical lines

The reflected phase is affine, with slope given by the lower rate. -/

/-- The difference of the two reflected exponents cancels its quadratic terms;
after adding the original phase its vertical slope is `μ`. -/
private def principalFiveTermReflectedPhase (d : ℕ) (ℓ p m : ℤ) (w y : ℝ)
    (z : ℂ) : ℂ :=
  principalFaddeevReflectionExponent d (-(m + 1)) 0 (-z) -
    principalFaddeevReflectionExponent d (-(m + p)) 0 (-(z + y)) +
      principalFiveTermPhase d ℓ w m z

/-- The reflected phase is affine in `z`, with coefficient `μ`. -/
private lemma principalFiveTermReflectedPhase_eq (d : ℕ) (hd : 3 < d)
    (ℓ p m : ℤ) (w y : ℝ) (z : ℂ) :
    principalFiveTermReflectedPhase d ℓ p m w y z =
      (principalFiveTermLowerRate d ℓ p w y : ℂ) * z +
        principalFiveTermReflectedPhase d ℓ p m w y 0 := by
  have hρ : (principalRoot d : ℂ) ≠ 0 := ofReal_principalRoot_ne_zero d hd
  simp only [principalFiveTermReflectedPhase, principalFaddeevReflectionExponent,
    principalFiveTermPhase, principalFiveTermLowerRate]
  push_cast
  field_simp [hρ]
  ring

/-- On `z=x+it`, the reflected phase has imaginary part `μt`. -/
private lemma principalFiveTermReflectedPhase_vertical_im (d : ℕ) (hd : 3 < d)
    (ℓ p m : ℤ) (w y x t : ℝ) :
    (principalFiveTermReflectedPhase d ℓ p m w y ((x : ℂ) + t * I)).im =
      principalFiveTermLowerRate d ℓ p w y * t := by
  rw [principalFiveTermReflectedPhase_eq d hd]
  have hconst : (principalFiveTermReflectedPhase d ℓ p m w y 0).im = 0 := by
    simp [principalFiveTermReflectedPhase, principalFaddeevReflectionExponent,
      principalFiveTermPhase, Complex.div_ofReal_im, Complex.mul_im,
      pow_two, ← Complex.ofReal_pow]
  simp [hconst, Complex.mul_im]

/-- The reflected exponential has norm `exp(-2πμt)` on `x+it`. -/
private lemma norm_principalFiveTermReflectedPhase_exp (d : ℕ) (hd : 3 < d)
    (ℓ p m : ℤ) (w y x t : ℝ) :
    ‖Complex.exp (2 * Real.pi * I *
      principalFiveTermReflectedPhase d ℓ p m w y ((x : ℂ) + t * I))‖ =
      Real.exp ((-2 * Real.pi * principalFiveTermLowerRate d ℓ p w y) * t) := by
  rw [norm_exp_two_pi_I_mul, principalFiveTermReflectedPhase_vertical_im d hd]
  congr 1
  ring

/-! ### Upper exponential tail

Both products tend to one along the upper vertical ray, hence their quotient is bounded. -/

/-- For `t` sufficiently large, the principal kernel satisfies
`‖K_m(x+it)‖ ≤ C exp(-2πλt)` with `λ=d(d-2)w/ρ_d³+ℓ`.
This is the upper-tail ingredient of
[RW26, Radchenko, Wheeler (2026), Theorem 3, `thm:5term.mod.fad`],
obtained from Lemma 1, `lem:asymp`. -/
theorem exists_norm_principalFiveTermKernel_upper (d : ℕ) (hd : 3 < d)
    (ℓ p m : ℤ) (w y x : ℝ) :
    ∃ C T : ℝ, ∀ t : ℝ, T ≤ t →
      ‖principalFiveTermKernel d ℓ p w y m ((x : ℂ) + t * I)‖ ≤
        C * Real.exp ((-2 * Real.pi * principalFiveTermUpperRate d ℓ w) * t) := by
  let z : ℝ → ℂ := fun t => (x : ℂ) + t * I
  let z' : ℝ → ℂ := fun t => ((x + y : ℝ) : ℂ) + t * I
  obtain ⟨huIm, huRe⟩ := upperVerticalLine_sector x
  obtain ⟨hdIm, hdRe⟩ := upperVerticalLine_sector (x + y)
  have hu := tendsto_principalFaddeev_of_abs_re_le d hd (m + 1) 0 z 1 huIm huRe
  have hv := tendsto_principalFaddeev_of_abs_re_le d hd (m + p) 0 z' 1 hdIm hdRe
  have hratio : Tendsto (fun t => principalFaddeev d (m + 1) 0 (z t) /
      principalFaddeev d (m + p) 0 (z' t)) atTop (𝓝 (1 : ℂ)) := by
    convert hu.div hv (by norm_num : (1 : ℂ) ≠ 0) using 1
    simp
  obtain ⟨C, hC⟩ := (hratio.isBigO_one ℂ).bound
  obtain ⟨T, hT⟩ := eventually_atTop.mp hC
  refine ⟨C, T, ?_⟩
  intro t ht
  have hz : z' t = z t + y := by simp [z, z']; ring
  have hbound : ‖principalFaddeev d (m + 1) 0 (z t) /
      principalFaddeev d (m + p) 0 (z' t)‖ ≤ C := by
    simpa using hT t ht
  simpa [principalFiveTermKernel, z, ← hz,
    norm_mul, norm_exp_principalFiveTermPhase] using
    mul_le_mul_of_nonneg_right hbound (Real.exp_pos _).le

/-! ### Lower exponential tail

The reflected normalization makes both products converge to nonzero constants. The difference
of their reflection exponents supplies the corrected lower slope. -/

/-- A principal product divided by the exponential in its lower-sector asymptotic. -/
private def principalFiveTermNormalizedProduct (d : ℕ) (m : ℤ) (z : ℂ) : ℂ :=
  principalFaddeev d m 0 z /
    Complex.exp (2 * Real.pi * I *
      principalFaddeevReflectionExponent d (-m) 0 (-z))

/-- As `t → -∞`, the ratio of reflected-normalized products tends to
`((-1)^(m+1) e^{-πid/2}) / ((-1)^(m+p) e^{-πid/2})`.
Used by `exists_norm_principalFiveTermKernel_lower`. -/
private lemma tendsto_normalizedProduct_div_lower (d : ℕ) (hd : 3 < d)
    (p m : ℤ) (x y : ℝ) :
    Tendsto (fun t : ℝ =>
      principalFiveTermNormalizedProduct d (m + 1) ((x : ℂ) + t * I) /
        principalFiveTermNormalizedProduct d (m + p) (((x + y : ℝ) : ℂ) + t * I))
      atBot (𝓝 (((-1 : ℂ) ^ (m + 1) * Complex.exp (-Real.pi * I * (d : ℂ) / 2)) /
        ((-1 : ℂ) ^ (m + p) * Complex.exp (-Real.pi * I * (d : ℂ) / 2)))) := by
  let z : ℝ → ℂ := fun t => (x : ℂ) + t * I
  let z' : ℝ → ℂ := fun t => ((x + y : ℝ) : ℂ) + t * I
  obtain ⟨huIm, huRe⟩ := lowerVerticalLine_sector x
  obtain ⟨hdIm, hdRe⟩ := lowerVerticalLine_sector (x + y)
  have hu := tendsto_principalFaddeev_div_exp_of_abs_re_le
    d hd (m + 1) 0 z 1 huIm huRe
  have hv := tendsto_principalFaddeev_div_exp_of_abs_re_le
    d hd (m + p) 0 z' 1 hdIm hdRe
  have hne : (-1 : ℂ) ^ (m + p) *
      Complex.exp (-Real.pi * I * (d : ℂ) / 2) ≠ 0 :=
    mul_ne_zero (zpow_ne_zero (m + p) (by norm_num)) (Complex.exp_ne_zero _)
  convert hu.div hv (by simpa using hne) using 1
  · funext t
    simp [principalFiveTermNormalizedProduct, z, z']
  · simp

/-- The kernel equals the ratio of reflected-normalized products times the residual phase. -/
private lemma principalFiveTermKernel_eq_normalized (d : ℕ) (ℓ p m : ℤ)
    (w y : ℝ) (z : ℂ) :
    principalFiveTermKernel d ℓ p w y m z =
      (principalFiveTermNormalizedProduct d (m + 1) z /
        principalFiveTermNormalizedProduct d (m + p) (z + y)) *
          Complex.exp (2 * Real.pi * I *
            principalFiveTermReflectedPhase d ℓ p m w y z) := by
  let N := principalFaddeev d (m + 1) 0 z
  let D := principalFaddeev d (m + p) 0 (z + y)
  let E₁ := Complex.exp (2 * Real.pi * I *
    principalFaddeevReflectionExponent d (-(m + 1)) 0 (-z))
  let E₂ := Complex.exp (2 * Real.pi * I *
    principalFaddeevReflectionExponent d (-(m + p)) 0 (-(z + y)))
  let P := Complex.exp (2 * Real.pi * I * principalFiveTermPhase d ℓ w m z)
  have hE₁ : E₁ ≠ 0 := Complex.exp_ne_zero _
  have hE₂ : E₂ ≠ 0 := Complex.exp_ne_zero _
  have hphase : Complex.exp (2 * Real.pi * I *
      principalFiveTermReflectedPhase d ℓ p m w y z) = E₁ / E₂ * P := by
    simp [principalFiveTermReflectedPhase, E₁, E₂, P, mul_add, mul_sub,
      Complex.exp_add, Complex.exp_sub]
  change N / D * P = (N / E₁ / (D / E₂)) * _
  rw [hphase]
  by_cases hD : D = 0
  · simp [hD]
  · field_simp

/-- For `t` sufficiently negative, the principal kernel satisfies
`‖K_m(x+it)‖ ≤ C exp(-2πμt)` with `μ=d(d-2)(w+y)/ρ_d³+ℓ+p-1`.
The lower rate retains the `p` term omitted in the printed convergence condition of
[RW26, Radchenko, Wheeler (2026), Theorem 3, `thm:5term.mod.fad`]; the bound follows from
Lemma 1, `lem:asymp`. -/
theorem exists_norm_principalFiveTermKernel_lower (d : ℕ) (hd : 3 < d)
    (ℓ p m : ℤ) (w y x : ℝ) :
    ∃ C T : ℝ, ∀ t : ℝ, t ≤ -T →
      ‖principalFiveTermKernel d ℓ p w y m ((x : ℂ) + t * I)‖ ≤
        C * Real.exp ((-2 * Real.pi * principalFiveTermLowerRate d ℓ p w y) * t) := by
  have hlim := tendsto_normalizedProduct_div_lower d hd p m x y
  obtain ⟨C, hC⟩ := (hlim.isBigO_one ℂ).bound
  obtain ⟨T₀, hT⟩ := eventually_atBot.mp hC
  refine ⟨C, -T₀, ?_⟩
  intro t ht
  have hz : ((x + y : ℝ) : ℂ) + t * I = ((x : ℂ) + t * I) + y := by
    push_cast
    ring
  have hbound : ‖principalFiveTermNormalizedProduct d (m + 1) ((x : ℂ) + t * I) /
      principalFiveTermNormalizedProduct d (m + p) (((x + y : ℝ) : ℂ) + t * I)‖ ≤ C := by
    simpa using hT t (by linarith)
  rw [principalFiveTermKernel_eq_normalized, ← hz, norm_mul,
    norm_principalFiveTermReflectedPhase_exp d hd]
  exact mul_le_mul_of_nonneg_right hbound (Real.exp_pos _).le

/-! ### Tail integrability

Meromorphicity makes the totalized kernel measurable even at exceptional real-lattice points.
The exponential majorants are integrable on their respective tails. -/

/-- The principal five-term kernel is Borel measurable for real `w,y`. -/
private lemma measurable_principalFiveTermKernel (d : ℕ) (hd : 3 < d)
    (ℓ p m : ℤ) (w y : ℝ) :
    Measurable (principalFiveTermKernel d ℓ p w y m) := by
  have hN : Meromorphic (principalFaddeev d (m + 1) 0) :=
    fun z => meromorphicAt_principalFaddeev d hd (m + 1) 0 z
  have hD : Meromorphic (principalFaddeev d (m + p) 0) :=
    fun z => meromorphicAt_principalFaddeev d hd (m + p) 0 z
  have hP : Measurable (fun z : ℂ => Complex.exp
      (2 * Real.pi * I * principalFiveTermPhase d ℓ w m z)) := by
    unfold principalFiveTermPhase
    fun_prop
  exact (hN.measurable.div (hD.measurable.comp (by fun_prop))).mul hP

/-- If `λ=d(d-2)w/ρ_d³+ℓ>0`, then the actual complex kernel on `x+it` is integrable
on some upper tail `Ioi T`. This is the upper-tail convergence ingredient of
[RW26, Radchenko, Wheeler (2026), Theorem 3, `thm:5term.mod.fad`]. -/
theorem integrableOn_principalFiveTermKernel_upper (d : ℕ) (hd : 3 < d)
    (ℓ p m : ℤ) (w y x : ℝ) (hRate : 0 < principalFiveTermUpperRate d ℓ w) :
    ∃ T : ℝ, IntegrableOn
      (fun t : ℝ => principalFiveTermKernel d ℓ p w y m ((x : ℂ) + t * I))
      (Ioi T) := by
  obtain ⟨C, T, hbound⟩ :=
    exists_norm_principalFiveTermKernel_upper d hd ℓ p m w y x
  have ha : -2 * Real.pi * principalFiveTermUpperRate d ℓ w < 0 := by
    nlinarith [Real.pi_pos]
  have hf : Measurable (fun t : ℝ =>
      principalFiveTermKernel d ℓ p w y m ((x : ℂ) + t * I)) :=
    (measurable_principalFiveTermKernel d hd ℓ p m w y).comp (by fun_prop)
  refine ⟨T, ?_⟩
  apply Integrable.mono' ((integrableOn_exp_mul_Ioi ha T).const_mul C)
    hf.aestronglyMeasurable
  exact (ae_restrict_mem measurableSet_Ioi).mono (fun t ht => hbound t ht.le)

/-- If `μ=d(d-2)(w+y)/ρ_d³+ℓ+p-1<0`, then the actual complex kernel on `x+it` is
integrable on some lower tail `Iio (-T)`. The `p` term is required by the reflection
exponent in [RW26, Radchenko, Wheeler (2026), Theorem 3, `thm:5term.mod.fad`]. -/
theorem integrableOn_principalFiveTermKernel_lower (d : ℕ) (hd : 3 < d)
    (ℓ p m : ℤ) (w y x : ℝ) (hμ : principalFiveTermLowerRate d ℓ p w y < 0) :
    ∃ T : ℝ, IntegrableOn
      (fun t : ℝ => principalFiveTermKernel d ℓ p w y m ((x : ℂ) + t * I))
      (Iio (-T)) := by
  obtain ⟨C, T, hbound⟩ :=
    exists_norm_principalFiveTermKernel_lower d hd ℓ p m w y x
  have ha : 0 < -2 * Real.pi * principalFiveTermLowerRate d ℓ p w y := by
    nlinarith [Real.pi_pos]
  have hf : Measurable (fun t : ℝ =>
      principalFiveTermKernel d ℓ p w y m ((x : ℂ) + t * I)) :=
    (measurable_principalFiveTermKernel d hd ℓ p m w y).comp (by fun_prop)
  refine ⟨T, ?_⟩
  have hi : IntegrableOn (fun t : ℝ =>
      C * Real.exp ((-2 * Real.pi * principalFiveTermLowerRate d ℓ p w y) * t))
      (Iic (-T)) := (integrableOn_exp_mul_Iic ha (-T)).const_mul C
  have hg : IntegrableOn (fun t : ℝ =>
      C * Real.exp ((-2 * Real.pi * principalFiveTermLowerRate d ℓ p w y) * t))
      (Iio (-T)) := hi.mono_set Iio_subset_Iic_self
  apply Integrable.mono' hg hf.aestronglyMeasurable
  exact (ae_restrict_mem measurableSet_Iio).mono (fun t ht => hbound t ht.le)

end SIC

end
