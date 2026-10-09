/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Topology.Algebra.GroupWithZero

/-!
# Analytic Construction of the Barnes Double Sine

The real double-sine integral, its convergence, and the shorthand `S₂(z,τ)`.

This file defines the Barnes double sine function `S₂(z; ω₁, ω₂)` on its real fundamental chamber
and proves convergence of the defining integral. Scalar integral evaluations and the boundary-period
value are proved in `SICs.SpecialFunctions.DoubleSine.IntegralIdentities`. The symmetry, reflection,
positivity, and quasiperiodicity identities are in `SICs.SpecialFunctions.DoubleSine.Identities`.

Mathlib does not contain a Barnes double sine, double gamma, or multiple sine/gamma definition
as of v4.34.1.

## Convention

The definition uses the **Kurokawa–Koyama convention**: `S₂` is the ratio of Barnes double gammas

$$S_2(z; \omega_1, \omega_2) = \Gamma_2(z; \omega_1, \omega_2)^{-1}\,
  \Gamma_2(\omega_1 + \omega_2 - z; \omega_1, \omega_2)$$

of [77, Kurokawa, Koyama (2003), equation (2.2)], which is the convention adopted by
[AFK25, Section 8.2] and prevalent in the mathematics literature. Its reciprocal is the
convention of [84, Ponsot (2003), Appendix B], prevalent in the physics literature and used by
the numerical reference implementation [42, Flammia (2024)]:

$$S_2^{\text{Ponsot}}(z; \omega_1, \omega_2) = 1 / S_2(z; \omega_1, \omega_2).$$

The two are told apart by the period shift: the convention used here *divides* by
`2 sin(πz/ω₂)`, Ponsot's *multiplies*.

**Conflicting attributions to Shintani.** [AFK25, Section 8.2] writes "we are using the definition
of Shintani and Kurokawa and Koyama … as opposed to the definition of Ponsot", and
[72, Kopp (2024), equation (4.8), `eq:dsinegamma`] likewise calls the convention used here
Shintani's double sine function. [42, Flammia (2024)] instead attributes the *reciprocal* to
Shintani, recording that "many authors, including Koyama & Kurokawa, Kurokawa & Koyama, and
Tangedal, use a convention which replaces S₂ by 1/S₂ relative to our convention".
Although [95, Shintani (1977)] does not use the name double sine, paragraph 1.6 on p. 181
explicitly defines `F(z;ω)=Γ₂(ω₁+ω₂-z;ω)/Γ₂(z;ω)`, agreeing with the convention here.
The function called `F` in its introduction, paragraph 0-2 on p. 167, has the reciprocal
orientation. Thus the two occurrences of `F` in [95] must be distinguished when comparing
attributions. This project names the reciprocal convention after [84] rather than after Shintani.

## Integral representation

For `ω₁ > 0`, `ω₂ > 0`, and `0 < z < ω₁ + ω₂`, the Kurokawa–Koyama double sine has the
integral representation

$$S_2^{\text{KK}}(z; \omega_1, \omega_2)
  = \exp\!\left(-\frac{1}{2}\int_0^\infty K(z, \omega_1, \omega_2, t)\,dt\right)$$

where the kernel is

$$K(z, \omega_1, \omega_2, t) =
  \left(\frac{\sinh\bigl((\omega_1 + \omega_2 - 2z)\,t\bigr)}
             {\sinh(\omega_1 t)\,\sinh(\omega_2 t)}
  - \frac{\omega_1 + \omega_2 - 2z}{\omega_1\,\omega_2\,t}\right)\frac{1}{t}.$$

The subtraction removes the `1/t²` singularity at `t = 0`, leaving a removable singularity
with a finite limit for positive periods. At infinity the hyperbolic-sine ratio decays exponentially
when `0 < z < ω₁ + ω₂`, while the subtracted term is a constant multiple of `t⁻²`.

This is the negative of the log-integral used by [42, Flammia (2024)]: that implementation
computes `exp(+(1/2) ∫ ...)` for S₂^{Ponsot}, while we compute `exp(-(1/2) ∫ ...)` for
S₂^{KK} = 1/S₂^{Ponsot}.

## Convergence

The kernel is integrable on `(0, ∞)` when `ω₁, ω₂ > 0` and `0 < z < ω₁ + ω₂`
(`doubleSineKernel_integrableOn_Ioi`). The proof is split into two pieces combined via
`IntegrableOn.union` with `Ioc_union_Ioi_eq_Ioi`:

- **At `t → ∞`**: `doubleSineKernel_integrableOn_Ioi_one` establishes integrability
  on `(1, ∞)` by decomposing the kernel into a sinh ratio piece (exponentially decaying,
  handled via `integrable_of_isBigO_exp_neg`) and a polynomial piece (`t^{−2}`, handled via
  `integrableOn_Ioi_rpow_of_lt`). The exponential estimate follows compositionally from
  `sinh (ωt) ~ exp (ωt) / 2` at infinity.

- **Near `t = 0`**: `doubleSineKernel_integrableOn_Ioc_zero_one` establishes integrability
  on `(0, 1]` from the asymptotic estimate `K(t) = O(1)` as `t → 0⁺`. The numerator is
  `O(t⁴)` by `sinh(x) − x = O(x³)`, while the denominator is asymptotic to a nonzero
  constant times `t⁴` because `sinh(ωt) ~ ωt`. Continuity handles the compact interval
  away from zero.

## References

- [AFK25, Section 8.2], and its equation (8.7), `eq:dsintrep`
- [72, Kopp (2024), Proposition 4.28, `prop:sinhintegral`], the integral representation defining
  `doubleSine` here
- [77, Kurokawa, Koyama (2003), equation (2.2)], the ratio of double gammas it computes
- [84, Ponsot (2003), Appendix B], the reciprocal convention
- [95, Shintani (1977)], which defines the double gamma Γ₂ this is the sine of; [AFK25,
  Section 1] credits the double sine's introduction to it and to [94], [96], [97]
- [42, Flammia (2024)], *Zauner.jl*: numerical implementation, in Ponsot's convention
-/

noncomputable section

open Real MeasureTheory Set Asymptotics Filter

namespace SIC

/-! ### Double sine kernel

The regularized hyperbolic kernel is the analytic input for the integral definition.  Its
elementary symmetries already contain the reflection and period-shift identities of the function. -/

/-- The integrand kernel for the Barnes double sine function on `(0, ∞)`:

$$K(z, \omega_1, \omega_2, t) =
  \left(\frac{\sinh((\omega_1 + \omega_2 - 2z) t)}{\sinh(\omega_1 t)\,\sinh(\omega_2 t)}
  - \frac{\omega_1 + \omega_2 - 2z}{\omega_1 \omega_2 t}\right) \frac{1}{t}.$$

The subtraction removes the `1/t²` singularity at `t = 0`, leaving a removable singularity
with a finite limit for positive periods. It is the integrand of the integral
representation cited at `doubleSine`, after the substitution `t ↦ t/2` that clears the halved
arguments there. -/
def doubleSineKernel (z ω₁ ω₂ t : ℝ) : ℝ :=
  (sinh ((ω₁ + ω₂ - 2 * z) * t) / (sinh (ω₁ * t) * sinh (ω₂ * t))
    - (ω₁ + ω₂ - 2 * z) / (ω₁ * ω₂ * t)) / t

/-- `sinh(x − y) − sinh(x + y) = −2 cosh(x) sinh(y)`. Used for the quasiperiodicity
kernel difference calculation. -/
private lemma sinh_sub_sub_sinh_add (x y : ℝ) :
    sinh (x - y) - sinh (x + y) = -2 * cosh x * sinh y := by
  simp [sinh_add, sinh_sub]; ring

/-- **Kernel difference under ω₁-shift.**

For `ω₁, ω₂, t > 0`, the difference `K(z + ω₁, ω₁, ω₂, t) − K(z, ω₁, ω₂, t)` simplifies to

$$\frac{1}{t}\left(\frac{2}{\omega_2 t}
  - \frac{2\cosh\bigl((\omega_2 - 2z)t\bigr)}{\sinh(\omega_2 t)}\right).$$

The `sinh(ω₁ t)` factor in the denominator cancels with a factor from the numerator
difference via `sinh(x − y) − sinh(x + y) = −2 cosh(x) sinh(y)`.

This is the kernel-level content of `doubleSine_quasiperiod_fst`, which evaluates the
integral of this expression as `2 log(2 sin(π z / ω₂))`. -/
lemma doubleSineKernel_shift_sub (z ω₁ ω₂ t : ℝ)
    (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂) (ht : 0 < t) :
    doubleSineKernel (z + ω₁) ω₁ ω₂ t - doubleSineKernel z ω₁ ω₂ t =
    (2 / (ω₂ * t) - 2 * cosh ((ω₂ - 2 * z) * t) / sinh (ω₂ * t)) / t := by
  unfold doubleSineKernel
  have hs₁ : sinh (ω₁ * t) ≠ 0 := ne_of_gt (sinh_pos_iff.mpr (mul_pos hω₁ ht))
  have hs₂ : sinh (ω₂ * t) ≠ 0 := ne_of_gt (sinh_pos_iff.mpr (mul_pos hω₂ ht))
  rw [show (sinh ((ω₁ + ω₂ - 2 * (z + ω₁)) * t) / (sinh (ω₁ * t) * sinh (ω₂ * t)) -
          (ω₁ + ω₂ - 2 * (z + ω₁)) / (ω₁ * ω₂ * t)) / t -
        (sinh ((ω₁ + ω₂ - 2 * z) * t) / (sinh (ω₁ * t) * sinh (ω₂ * t)) -
          (ω₁ + ω₂ - 2 * z) / (ω₁ * ω₂ * t)) / t
      = (sinh ((ω₁ + ω₂ - 2 * (z + ω₁)) * t) / (sinh (ω₁ * t) * sinh (ω₂ * t))
          - sinh ((ω₁ + ω₂ - 2 * z) * t) / (sinh (ω₁ * t) * sinh (ω₂ * t))
          - ((ω₁ + ω₂ - 2 * (z + ω₁)) / (ω₁ * ω₂ * t) -
             (ω₁ + ω₂ - 2 * z) / (ω₁ * ω₂ * t))) / t
      from by ring]
  rw [div_sub_div_same (sinh _) (sinh _),
      show (ω₁ + ω₂ - 2 * (z + ω₁)) * t = (ω₂ - 2 * z) * t - ω₁ * t from by ring,
      show (ω₁ + ω₂ - 2 * z) * t = (ω₂ - 2 * z) * t + ω₁ * t from by ring,
      sinh_sub_sub_sinh_add]
  rw [show (ω₁ + ω₂ - 2 * (z + ω₁)) / (ω₁ * ω₂ * t) - (ω₁ + ω₂ - 2 * z) / (ω₁ * ω₂ * t)
      = -2 / (ω₂ * t) from by field_simp; ring]
  field_simp; ring

/-! ### Log-integral

Integrating the kernel over the positive real axis packages the logarithm of the double sine.
Lean's total integral makes the definition global, while the convergence results below identify
the chamber where it has the intended analytic meaning. -/

/-- The log-integral for the Barnes double sine function:

$$\mathcal{I}(z; \omega_1, \omega_2) = \int_0^\infty K(z, \omega_1, \omega_2, t)\,dt.$$

This is the integral on `(0, ∞)` of the double sine kernel; `doubleSine` carries the citation.
The integral converges when `ω₁, ω₂ > 0` and `0 < z < ω₁ + ω₂`. When the kernel is not
integrable, Lean's Bochner integral totalizes to `0`. -/
def doubleSineLogIntegral (z ω₁ ω₂ : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), doubleSineKernel z ω₁ ω₂ t

/-! ### Double sine function

Exponentiating minus one half of the log-integral gives the Kurokawa--Koyama convention used by
[AFK25, Section 8.2]; the module header compares it with the reciprocal convention. -/

/-- The Barnes double sine function `S₂(z; ω₁, ω₂)` in the Kurokawa–Koyama convention.

On the fundamental chamber `ω₁ > 0`, `ω₂ > 0`, `0 < z < ω₁ + ω₂`:

$$S_2(z; \omega_1, \omega_2) =
  \exp\!\left(-\frac{1}{2}\,\mathcal{I}(z; \omega_1, \omega_2)\right).$$

This is [72, Kopp (2024), Proposition 4.28, `prop:sinhintegral`], whose `ω₂ = 1` case with `z`
shifted to `z + 1` is [AFK25, equation (8.7), `eq:dsintrep`]. [42, Flammia (2024)] uses the
reciprocal convention of [84, Ponsot (2003)]: `S₂^Ponsot = 1/S₂`; see the module header.

When the kernel is not integrable, the Bochner integral totalizes to `0`, so the expression
then evaluates to `exp(0) = 1`. This definition alone does not supply analytic continuation
outside the chamber; `doubleSine_quasiperiod_fst` and `doubleSine_quasiperiod_snd` prove the
period relations where both arguments lie in the chamber. -/
def doubleSine (z ω₁ ω₂ : ℝ) : ℝ :=
  exp (-doubleSineLogIntegral z ω₁ ω₂ / 2)

/-- The two-argument shorthand `S₂(z, τ) = S₂(z; τ, 1)` of [72, Kopp (2024), Section 4.8], used in
[AFK25, Section 8.2]. -/
abbrev doubleSine' (z τ : ℝ) : ℝ := doubleSine z τ 1

/-! ### Convergence building blocks and tail integrability

The double sine kernel is continuous on `(0, ∞)` when `ω₁, ω₂ > 0`. Its integrability on
`(0, ∞)` for `0 < z < ω₁ + ω₂` reduces to two estimates:

- **At `t → ∞`**: The kernel is decomposed as `f(t) − g(t)` where
  `f(t) = sinh(at)/(sinh(ω₁t)·sinh(ω₂t)·t)` (exponentially decaying) and
  `g(t) = a/(ω₁ω₂t²)` (polynomially decaying). Each is separately integrable
  on `(1, ∞)`:

  For `f`, `sinh (ωt) ~ exp (ωt) / 2` for positive `ω`. Combining the two reciprocal
  equivalences with `|sinh(at)| = O(exp(|a|t))` and `t⁻¹ = O(1)` gives
  `f(t) = O(exp(−(ω₁+ω₂−|a|)t))`. Since `|a| < ω₁ + ω₂`, the decay
  rate is positive, and `integrable_of_isBigO_exp_neg` gives integrability.

  For `g`: `a/(ω₁ω₂t²) = c · t^{−2}` is integrable on `(1, ∞)` by
  `integrableOn_Ioi_rpow_of_lt` since `−2 < −1`.

  Combined via `IntegrableOn.sub`, the kernel is integrable on `(1, ∞)`.
  This is `doubleSineKernel_integrableOn_Ioi_one`.

- **Near `t = 0`**: let `a = ω₁ + ω₂ − 2z`. The subtracted term removes the
  `1/t²` pole. Writing `r_c(t) = sinh(ct) − ct`, the regularized numerator is `O(t⁴)`
  by `sinh_sub_id_isBigO`, while its denominator is asymptotic to a nonzero constant
  times `t⁴`. Hence the full kernel is `O(1)` as `t → 0⁺`; boundedness near zero and
  continuity away from zero give `doubleSineKernel_integrableOn_Ioc_zero_one`.

`IntegrableOn.union` with `Ioc_union_Ioi_eq_Ioi` combines the two pieces in
`doubleSineKernel_integrableOn_Ioi`. -/

/-- `|sinh(x)| ≤ exp(|x|)/2` for all `x : ℝ`. This follows from `sinh(y) ≤ exp(y)/2`
(since `exp(−y) ≥ 0`) applied with `y = |x|` via `|sinh(x)| = sinh(|x|)`. -/
lemma abs_sinh_le_exp_half (x : ℝ) : |sinh x| ≤ exp (|x|) / 2 := by
  rw [abs_sinh, sinh_eq]; linarith [exp_nonneg (-|x|)]

/-- **Taylor remainder for sinh.** `sinh(x) − x = O(x³)` as `x → 0`.

This is the precise cancellation needed to show that the double sine kernel has a
removable singularity at `t = 0`. The proof derives the bound from
`Real.exp_sub_sum_range_isBigO_pow` applied to `exp(x)` and `exp(−x)`.

It is composed below with `sinh(ωt) ~ ωt` to show that the full kernel
`K(z, ω₁, ω₂, t) = O(1)` as `t → 0⁺`. -/
lemma sinh_sub_id_isBigO :
    (fun x : ℝ => sinh x - x) =O[nhds 0] (fun x => x ^ 3) := by
  rw [show (fun x : ℝ => sinh x - x) = fun x =>
      ((exp x - (1 + x + x ^ 2 / 2)) -
       (exp (-x) - (1 - x + x ^ 2 / 2))) / 2 from by
    ext x; rw [sinh_eq]; ring]
  have h1 := exp_sub_sum_range_isBigO_pow (n := 3)
  simp [Finset.sum_range_succ, Nat.factorial] at h1
  have hneg : Tendsto (fun x : ℝ => -x) (nhds 0) (nhds (0 : ℝ)) :=
    (continuous_neg.tendsto 0).congr (fun _ => rfl)
      |>.mono_right (by rw [neg_zero])
  have h2 : (fun x : ℝ => exp (-x) - (1 - x + x ^ 2 / 2))
      =O[nhds 0] (fun x => x ^ 3) :=
    ((h1.comp_tendsto hneg).congr_left
      (fun x => by simp [Function.comp]; ring)).trans
    ((isBigO_refl _ _).neg_left.congr_left
      (fun x => by simp [Function.comp]; ring))
  exact (h1.sub h2).const_mul_left (1 / 2)
    |>.congr_left (fun x => by ring)

/-- The double sine kernel is continuous on `(0, ∞)` when `ω₁, ω₂ > 0`. -/
lemma doubleSineKernel_continuousOn (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂) (z : ℝ) :
    ContinuousOn (doubleSineKernel z ω₁ ω₂) (Ioi 0) := by
  unfold doubleSineKernel
  apply ContinuousOn.div
  · apply ContinuousOn.sub
    · apply ContinuousOn.div
      · exact (continuous_sinh.comp
          (continuous_const.mul continuous_id')).continuousOn
      · exact (ContinuousOn.mul
          (continuous_sinh.comp
            (continuous_const.mul continuous_id')).continuousOn
          (continuous_sinh.comp
            (continuous_const.mul continuous_id')).continuousOn)
      · intro t ht; simp only [mem_Ioi] at ht
        exact ne_of_gt (mul_pos (sinh_pos_iff.mpr (mul_pos hω₁ ht))
                                (sinh_pos_iff.mpr (mul_pos hω₂ ht)))
    · apply ContinuousOn.div
      · exact continuousOn_const
      · exact (continuous_const.mul continuous_id').continuousOn
      · intro t ht; simp only [mem_Ioi] at ht
        exact ne_of_gt (mul_pos (mul_pos hω₁ hω₂) ht)
  · exact continuous_id'.continuousOn
  · intro t ht; simp only [mem_Ioi] at ht; exact ne_of_gt ht

/-- For `ω > 0`, `sinh (ωt)` is asymptotic to `exp (ωt) / 2` as `t → ∞`. -/
private lemma sinh_mul_isEquivalent_exp_atTop (ω : ℝ) (hω : 0 < ω) :
    (fun t : ℝ => sinh (ω * t)) ~[atTop] (fun t => exp (ω * t) / 2) := by
  apply isEquivalent_of_tendsto_one
  have he : Tendsto (fun t : ℝ => exp (-2 * ω * t)) atTop (nhds 0) :=
    tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by linarith : -2 * ω < 0))
  convert (tendsto_const_nhds (x := (1 : ℝ))).sub he using 1
  · funext t
    change sinh (ω * t) / (exp (ω * t) / 2) = 1 - exp (-2 * ω * t)
    rw [sinh_eq]
    field_simp [exp_ne_zero]
    rw [mul_sub, mul_one, ← exp_add]
    congr 1
    ring_nf
  · norm_num

/-- The hyperbolic-sine ratio in the tail of the double-sine kernel decays exponentially. -/
private lemma sinh_ratio_isBigO_exp_neg (a ω₁ ω₂ : ℝ)
    (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂) :
    (fun t : ℝ => sinh (a * t) / (sinh (ω₁ * t) * sinh (ω₂ * t) * t))
      =O[atTop] (fun t => exp (- (ω₁ + ω₂ - |a|) * t)) := by
  have hnum : (fun t : ℝ => sinh (a * t)) =O[atTop] (fun t => exp (|a| * t)) := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (exp_pos _).le]
    calc
      |sinh (a * t)| ≤ exp (|a| * t) / 2 := by
        simpa [abs_mul, abs_of_nonneg ht] using abs_sinh_le_exp_half (a * t)
      _ ≤ 1 * exp (|a| * t) := by rw [one_mul]; linarith [exp_pos (|a| * t)]
  have h₁ := (sinh_mul_isEquivalent_exp_atTop ω₁ hω₁).inv.isBigO
  have h₂ := (sinh_mul_isEquivalent_exp_atTop ω₂ hω₂).inv.isBigO
  have ht : (fun t : ℝ => t⁻¹) =O[atTop] (fun _ => (1 : ℝ)) := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    rw [Real.norm_eq_abs, abs_inv, abs_of_nonneg (by linarith : 0 ≤ t), norm_one,
      one_mul, inv_le_one₀ (by linarith : 0 < t)]
    exact ht
  have h := ((hnum.mul h₁).mul h₂).mul ht
  have h' : (fun t : ℝ => sinh (a * t) / (sinh (ω₁ * t) * sinh (ω₂ * t) * t))
      =O[atTop] (fun t => 4 * exp (- (ω₁ + ω₂ - |a|) * t)) := by
    apply h.congr'
    · filter_upwards with t
      simp only [Pi.inv_apply]
      simp [div_eq_mul_inv]
      ring
    · filter_upwards with t
      simp only [Pi.inv_apply]
      rw [show (exp (ω₁ * t) / 2)⁻¹ = 2 * exp (- (ω₁ * t)) by
        rw [exp_neg]; field_simp,
        show (exp (ω₂ * t) / 2)⁻¹ = 2 * exp (- (ω₂ * t)) by
        rw [exp_neg]; field_simp]
      calc
        exp (|a| * t) * (2 * exp (- (ω₁ * t))) * (2 * exp (- (ω₂ * t))) * 1 =
            4 * (exp (|a| * t) * exp (- (ω₁ * t)) * exp (- (ω₂ * t))) := by ring
        _ = 4 * exp (|a| * t + -(ω₁ * t) + -(ω₂ * t)) := by rw [exp_add, exp_add]
        _ = 4 * exp (- (ω₁ + ω₂ - |a|) * t) := by congr 2; ring
  exact h'.trans ((isBigO_refl _ _).const_mul_left 4)

/-- The hyperbolic-sine ratio is integrable on `(1, ∞)` when its numerator grows more slowly
than the product of its two denominator factors. -/
private lemma sinh_ratio_integrableOn_Ioi_one (a ω₁ ω₂ : ℝ)
    (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂) (ha : |a| < ω₁ + ω₂) :
    IntegrableOn (fun t : ℝ => sinh (a * t) /
      (sinh (ω₁ * t) * sinh (ω₂ * t) * t)) (Ioi 1) := by
  apply integrable_of_isBigO_exp_neg (by linarith : 0 < ω₁ + ω₂ - |a|)
  · apply ContinuousOn.div
    · exact (continuous_sinh.comp (continuous_const.mul continuous_id')).continuousOn
    · exact ((continuous_sinh.comp (continuous_const.mul continuous_id')).mul
        (continuous_sinh.comp (continuous_const.mul continuous_id')) |>.mul
        continuous_id').continuousOn
    · intro t ht
      simp only [mem_Ici] at ht
      have ht0 : 0 < t := zero_lt_one.trans_le ht
      exact ne_of_gt (by positivity)
  · exact sinh_ratio_isBigO_exp_neg a ω₁ ω₂ hω₁ hω₂

/-- A constant multiple of `t⁻²` is integrable on `(1, ∞)`. -/
private lemma const_div_mul_sq_integrableOn_Ioi_one (a ω₁ ω₂ : ℝ) :
    IntegrableOn (fun t : ℝ => a / (ω₁ * ω₂ * (t * t))) (Ioi 1) := by
  have h := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) one_pos
  apply (h.const_mul (a / (ω₁ * ω₂))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [mem_Ioi] at ht
  rw [rpow_neg (by positivity : 0 ≤ t), rpow_two]
  field_simp

/-- **Tail integrability of the double sine kernel on `(1, ∞)`.**

For `ω₁, ω₂ > 0` and `0 < z < ω₁ + ω₂`, decompose the kernel into an
exponentially decaying hyperbolic-sine ratio and an integrable multiple of `t⁻²`. -/
theorem doubleSineKernel_integrableOn_Ioi_one
    (z ω₁ ω₂ : ℝ) (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂)
    (hz : 0 < z) (hzu : z < ω₁ + ω₂) :
    IntegrableOn (doubleSineKernel z ω₁ ω₂) (Ioi (1 : ℝ)) := by
  let a := ω₁ + ω₂ - 2 * z
  have ha : |a| < ω₁ + ω₂ := by
    simp only [a]
    rw [abs_lt]
    constructor <;> linarith
  apply (sinh_ratio_integrableOn_Ioi_one a ω₁ ω₂ hω₁ hω₂ ha).sub
      (const_div_mul_sq_integrableOn_Ioi_one a ω₁ ω₂) |>.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [mem_Ioi] at ht
  have ht0 : 0 < t := by linarith
  have hs₁ : sinh (ω₁ * t) ≠ 0 := ne_of_gt (sinh_pos_iff.mpr (mul_pos hω₁ ht0))
  have hs₂ : sinh (ω₂ * t) ≠ 0 := ne_of_gt (sinh_pos_iff.mpr (mul_pos hω₂ ht0))
  change sinh (a * t) / (sinh (ω₁ * t) * sinh (ω₂ * t) * t) -
      a / (ω₁ * ω₂ * (t * t)) = doubleSineKernel z ω₁ ω₂ t
  simp only [doubleSineKernel, a]
  field_simp [hω₁.ne', hω₂.ne', hs₁, hs₂]

/-! ### Near-zero integrability and full convergence

Taylor cancellation removes the apparent singularity at the origin.  A boundedness argument on
`(0, 1]`, combined with the previously proved tail estimate, yields convergence on `(0, ∞)`. -/

/-- After a linear rescaling, the cubic Taylor remainder of `sinh` remains `O(t³)`. -/
private lemma sinh_mul_sub_isBigO (c : ℝ) :
    (fun t : ℝ => sinh (c * t) - c * t) =O[nhds 0] (fun t => t ^ 3) := by
  have hc : Tendsto (fun t : ℝ => c * t) (nhds 0) (nhds 0) := by
    have h : Continuous (fun t : ℝ => c * t) := continuous_const.mul continuous_id
    simpa using h.tendsto 0
  have h := sinh_sub_id_isBigO.comp_tendsto hc
  exact h.trans (((isBigO_refl (fun t : ℝ => t ^ 3) (nhds 0)).const_mul_left (c ^ 3)).congr_left
    (fun t => by simp; ring))

/-- The double-sine kernel is bounded asymptotically at its removable singularity `0⁺`.

Writing its numerator in terms of `r_c(t) = sinh(ct) - ct` makes it `O(t⁴)`, while its
denominator is asymptotic to `ω₁²ω₂²t⁴`. -/
private lemma doubleSineKernel_isBigO_one_nhdsWithin
    (z ω₁ ω₂ : ℝ) (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂) :
    (doubleSineKernel z ω₁ ω₂) =O[nhdsWithin 0 (Ioi 0)] (fun _ => (1 : ℝ)) := by
  let a := ω₁ + ω₂ - 2 * z
  let r := fun c t : ℝ => sinh (c * t) - c * t
  let N := fun t : ℝ => ω₁ * ω₂ * t * r a t - a * ω₁ * t * r ω₂ t -
    a * ω₂ * t * r ω₁ t - a * r ω₁ t * r ω₂ t
  let D := fun t : ℝ => ω₁ * ω₂ * t ^ 2 * sinh (ω₁ * t) * sinh (ω₂ * t)
  have hr (c : ℝ) : r c =O[nhds 0] (fun t : ℝ => t ^ 3) := sinh_mul_sub_isBigO c
  have ht : (fun t : ℝ => t) =O[nhds 0] (fun t => t) := isBigO_refl _ _
  have hfour : (fun t : ℝ => t * t ^ 3) =O[nhds 0] (fun t => t ^ 4) :=
    (isBigO_refl (fun t : ℝ => t ^ 4) (nhds 0)).congr_left (fun t => by ring)
  have hsix_four : (fun t : ℝ => t ^ 6) =O[nhds 0] (fun t => t ^ 4) :=
    (isLittleO_pow_pow (by omega : 4 < 6)).isBigO
  have hN : N =O[nhds 0] (fun t : ℝ => t ^ 4) := by
    have h1 := ((ht.mul (hr a)).trans hfour).const_mul_left (ω₁ * ω₂)
    have h2 := ((ht.mul (hr ω₂)).trans hfour).const_mul_left (a * ω₁)
    have h3 := ((ht.mul (hr ω₁)).trans hfour).const_mul_left (a * ω₂)
    have h4 := (((hr ω₁).mul (hr ω₂)).congr_right (fun t => by ring)).trans hsix_four
      |>.const_mul_left a
    exact (((h1.sub h2).sub h3).sub h4).congr_left (fun t => by simp only [N]; ring)
  have hmul (ω : ℝ) : (fun t : ℝ => sinh (ω * t)) ~[nhds 0] (fun t => ω * t) := by
    have hc : Tendsto (fun t : ℝ => ω * t) (nhds 0) (nhds 0) := by
      have h : Continuous (fun t : ℝ => ω * t) := continuous_const.mul continuous_id
      simpa using h.tendsto 0
    exact Real.isEquivalent_sinh.comp_tendsto hc
  have hD : D ~[nhds 0]
      (fun t : ℝ => ω₁ * ω₂ * t ^ 2 * (ω₁ * t) * (ω₂ * t)) := by
    have h := ((IsEquivalent.refl (l := nhds 0) (u := fun t : ℝ => ω₁ * ω₂ * t ^ 2)).mul
      (hmul ω₁)).mul (hmul ω₂)
    change (fun t : ℝ => ω₁ * ω₂ * t ^ 2 * sinh (ω₁ * t) * sinh (ω₂ * t)) ~[nhds 0]
      (fun t => ω₁ * ω₂ * t ^ 2 * (ω₁ * t) * (ω₂ * t)) at h
    exact h
  have hquot : (fun t => N t * (D t)⁻¹) =O[nhdsWithin 0 (Ioi 0)]
      (fun t : ℝ => t ^ 4 * (ω₁ * ω₂ * t ^ 2 * (ω₁ * t) * (ω₂ * t))⁻¹) :=
    (hN.mul hD.inv.isBigO).mono nhdsWithin_le_nhds
  have hright : (fun t : ℝ => t ^ 4 *
      (ω₁ * ω₂ * t ^ 2 * (ω₁ * t) * (ω₂ * t))⁻¹)
      =O[nhdsWithin 0 (Ioi 0)] (fun _ => (1 : ℝ)) := by
    apply IsBigO.of_bound ((ω₁ * ω₂)⁻¹ ^ 2)
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [mem_Ioi] at ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_one, mul_one]
    field_simp
    norm_num
  have hratio : (fun t => N t / D t) =O[nhdsWithin 0 (Ioi 0)] (fun _ => (1 : ℝ)) :=
    (hquot.trans hright).congr_left (fun t => by simp [div_eq_mul_inv])
  refine hratio.congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [mem_Ioi] at ht
  have hs₁ : sinh (ω₁ * t) ≠ 0 := ne_of_gt (sinh_pos_iff.mpr (mul_pos hω₁ ht))
  have hs₂ : sinh (ω₂ * t) ≠ 0 := ne_of_gt (sinh_pos_iff.mpr (mul_pos hω₂ ht))
  simp only [N, D, r, a, doubleSineKernel]
  field_simp
  ring

/-- A function continuous on `(0, ∞)` and `O(1)` at `0⁺` is integrable on `(0, 1]`. -/
private lemma integrableOn_Ioc_zero_one_of_isBigO_one {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Ioi 0))
    (hO : f =O[nhdsWithin 0 (Ioi 0)] (fun _ => (1 : ℝ))) :
    IntegrableOn f (Ioc 0 1) := by
  obtain ⟨C, hC⟩ := hO.bound
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hC
  obtain ⟨ε, hε, hC⟩ := hC
  let δ := min (ε / 2) 1
  have hδ : 0 < δ := lt_min (div_pos hε two_pos) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδε : δ < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hsmall : IntegrableOn f (Ioc 0 δ) := by
    apply IntegrableOn.of_bound measure_Ioc_lt_top
    · exact (hcont.mono fun _ ht => ht.1).aestronglyMeasurable measurableSet_Ioc
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      simp only [mem_Ioc] at ht
      simpa using hC (by rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
                         exact lt_of_le_of_lt ht.2 hδε) ht.1
  have hlarge : IntegrableOn f (Ioc δ 1) := by
    apply IntegrableOn.mono_set
      ((hcont.mono fun _ ht => hδ.trans_le ht.1).integrableOn_Icc)
    exact Ioc_subset_Icc_self
  rw [← Ioc_union_Ioc_eq_Ioc hδ.le hδ1]
  exact hsmall.union hlarge

/-- **Near-zero integrability of the double sine kernel on `(0, 1]`.**

The kernel has a removable singularity at `t = 0`. Its combined numerator is `O(t⁴)` by the
cubic remainder of `sinh`, and its denominator is asymptotic to `ω₁²ω₂²t⁴`, so the kernel is
`O(1)` at `0⁺`. Continuity supplies integrability on the remainder of `(0, 1]`. -/
theorem doubleSineKernel_integrableOn_Ioc_zero_one
    (z ω₁ ω₂ : ℝ) (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂) :
    IntegrableOn (doubleSineKernel z ω₁ ω₂) (Ioc (0 : ℝ) 1) := by
  exact integrableOn_Ioc_zero_one_of_isBigO_one
    (doubleSineKernel_continuousOn hω₁ hω₂ z)
    (doubleSineKernel_isBigO_one_nhdsWithin z ω₁ ω₂ hω₁ hω₂)
/-- **Full integrability of the double sine kernel on `(0, ∞)`.**

For `ω₁, ω₂ > 0` and `0 < z < ω₁ + ω₂`, the double sine kernel is integrable on
`(0, ∞)`. Combines the near-zero piece `doubleSineKernel_integrableOn_Ioc_zero_one`
with the tail piece `doubleSineKernel_integrableOn_Ioi_one`. -/
theorem doubleSineKernel_integrableOn_Ioi
    (z ω₁ ω₂ : ℝ) (hω₁ : 0 < ω₁) (hω₂ : 0 < ω₂)
    (hz : 0 < z) (hzu : z < ω₁ + ω₂) :
    IntegrableOn (doubleSineKernel z ω₁ ω₂) (Ioi (0 : ℝ)) := by
  rw [show Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 from (Ioc_union_Ioi_eq_Ioi (by linarith : (0:ℝ) ≤ 1)).symm]
  exact IntegrableOn.union
    (doubleSineKernel_integrableOn_Ioc_zero_one z ω₁ ω₂ hω₁ hω₂)
    (doubleSineKernel_integrableOn_Ioi_one z ω₁ ω₂ hω₁ hω₂ hz hzu)

end SIC

end
