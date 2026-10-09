/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Dilogarithm.Faddeev.LatticeValues
import SICs.SpecialFunctions.Faddeev.FiveTerm.Algebra

/-!
# The residue kernel of the principal finite five-term relation

The kernel whose residues at the lattice arguments are the terms of the finite five-term sum:
its pole factor, its simple poles, their residues, and the bicharacter phase.

This module follows [RW26, Radchenko, Wheeler (2026), Section 3.2, the proof of Theorem 2,
`thm:fg.equs`, the computation of equation (7), `eq:Fgpm.5term`] at `γ = A_d`, `τ = ρ_d`,
with `c = d(d-2)`, `ε = ρ_d³`, `q = e(ρ_d)`, and `n = h = 0`.

## The argument

The source divides the integrand of Theorem 3 with numerator index `m` by
`e(z/ε) - q^m e(z)`. Here the residue kernel is the five-term kernel
`Φ_{m+1,0}(z)/Φ_{m+p,0}(z+y) · e(phase)` multiplied by `(1 - q^m e(z))/(e(z/ε) - q^m e(z))`,
which by the left index shift law is `Φ_{m,0}(z)/Φ_{m+p,0}(z+y) · e(phase)/(e(z/ε) - q^m e(z))`
as germs. The pole factor vanishes exactly at the lattice arguments `z_{(m,k)}`, `k ∈ ℤ`, simply,
and its reciprocal has residue `ε e(-z/ε)/(2πi(1-ε))` there. At `z = z_{(m,k)}` with `y = z_v` and
`p = v₁`, both products have continued values, analytic and nonzero by
`SICs.Principal.Dilogarithm.Faddeev.Continuation`, so the kernel has a simple pole with residue
the reciprocal residue times `e(phase)` times the quotient of continued values.

At the lattice arguments the phase is a bicharacter: with `w = z_u` and `ℓ = u₁ + 1`,
`e(-z_x/ε) e(phase_m(z_x)) = ⟨x; u⟩`, the display in the proof of Theorem 2 of Section 3.2. Since
`e(z_x/ε - z_x) = e(mρ_d)` the term `e(-z_x/ε) e(ℓ(z_x + mρ_d))` reduces to `e(u₁(z_x + mρ_d))`,
and the remaining exponent is a quadratic expression in the rational characteristics of `x` and
`u`, equal modulo integers to the exponent of `thetaBicharacter`.

Off the zero class the continued values are the finite dilogarithm values
`E(x)/F⁻(x+v)`; at the zero class and at the class of `-v` they are the values of the type rule
of `SICs.Principal.Dilogarithm.Faddeev.LatticeValues`.
-/

noncomputable section

open Complex Filter Topology
open scoped MatrixGroups

namespace SIC

/-- The denominator `ρ_d⁻³ - 1` in the lattice argument is nonzero. -/
private theorem principalFiveTermPoleDenom_ne_zero (d : ℕ) (hd : 3 < d) :
    ((principalRoot d : ℂ) ^ 3)⁻¹ - 1 ≠ 0 := by
  have hpow : 1 < principalRoot d ^ 3 :=
    one_lt_principalRoot_pow_three d hd
  have h : (principalRoot d ^ 3)⁻¹ - 1 ≠ 0 := by
    have hi : (principalRoot d ^ 3)⁻¹ < 1 :=
      (inv_lt_one₀ (by positivity)).2 hpow
    exact ne_of_lt (sub_neg.mpr hi)
  exact_mod_cast h

/-! ### The pole factor

`e(z/ε) - q^m e(z)` vanishes exactly when `z/ε - z - mρ_d` is an integer, that is at the lattice
arguments of the source pairs with first coordinate `m`. -/

/-- The pole factor `e(z/ε) - q^m e(z)` of the residue kernel, `ε = ρ_d³`, `q = e(ρ_d)`, from the
denominator of the integrand in [RW26, Radchenko, Wheeler (2026), Section 3.2]. -/
def principalFiveTermPoleFactor (d : ℕ) (m : ℤ) (z : ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * I * (z / (principalRoot d : ℂ) ^ 3)) -
    Complex.exp (2 * Real.pi * I * (z + m * (principalRoot d : ℂ)))

/-- The zeros of the pole factor are exactly the lattice arguments `z_{(m,k)}`, `k ∈ ℤ`,
by `Complex.exp_eq_exp_iff_exists_int` and
`principalFiveTermLatticeArgument_div_sub_self`. -/
theorem principalFiveTermPoleFactor_eq_zero_iff (d : ℕ) (hd : 3 < d) (m : ℤ) (z : ℂ) :
    principalFiveTermPoleFactor d m z = 0 ↔
      ∃ k : ℤ, z = (principalFiveTermLatticeArgument d m k : ℂ) := by
  have hc : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp
  have hden := principalFiveTermPoleDenom_ne_zero d hd
  constructor
  · intro h
    rw [principalFiveTermPoleFactor, sub_eq_zero,
      Complex.exp_eq_exp_iff_exists_int] at h
    obtain ⟨k, hk⟩ := h
    have heq : z / (principalRoot d : ℂ) ^ 3 =
        z + m * (principalRoot d : ℂ) + k := by
      apply mul_left_cancel₀ hc
      calc
        (2 * Real.pi * I) * (z / (principalRoot d : ℂ) ^ 3) =
            (2 * Real.pi * I) * (z + m * (principalRoot d : ℂ)) +
              (k : ℂ) * (2 * Real.pi * I) := hk
        _ = _ := by ring
    refine ⟨k, ?_⟩
    have hcast : (principalFiveTermLatticeArgument d m k : ℂ) =
        ((m : ℂ) * (principalRoot d : ℂ) + k) /
          (((principalRoot d : ℂ) ^ 3)⁻¹ - 1) := by
      simp [principalFiveTermLatticeArgument]
    rw [hcast, eq_div_iff hden]
    rw [div_eq_mul_inv] at heq
    linear_combination heq
  · rintro ⟨k, rfl⟩
    unfold principalFiveTermPoleFactor
    rw [sub_eq_zero]
    convert (principalFiveTermLatticeArgument_exp_lower d hd m k).symm using 1
    congr 1
    ring

/-- The derivative of the pole factor. -/
theorem hasDerivAt_principalFiveTermPoleFactor (d : ℕ) (m : ℤ) (z : ℂ) :
    HasDerivAt (principalFiveTermPoleFactor d m)
      (2 * Real.pi * I *
        (Complex.exp (2 * Real.pi * I * (z / (principalRoot d : ℂ) ^ 3)) /
            (principalRoot d : ℂ) ^ 3 -
          Complex.exp (2 * Real.pi * I * (z + m * (principalRoot d : ℂ))))) z := by
  unfold principalFiveTermPoleFactor
  have h₁ := ((hasDerivAt_id z).div_const ((principalRoot d : ℂ) ^ 3) |>.const_mul
    (2 * Real.pi * I) |>.cexp)
  have h₂ := ((hasDerivAt_id z).add_const (m * (principalRoot d : ℂ)) |>.const_mul
    (2 * Real.pi * I) |>.cexp)
  convert h₁.sub h₂ using 1
  · funext x
    rfl
  · simp only [id_eq, mul_one]
    ring

/-- At a lattice argument the pole factor has the nonzero derivative
`2πi e(z/ε)(1/ε - 1)`, so its zeros are simple. -/
theorem deriv_principalFiveTermPoleFactor_latticeArgument (d : ℕ) (hd : 3 < d) (m k : ℤ) :
    deriv (principalFiveTermPoleFactor d m) (principalFiveTermLatticeArgument d m k) =
      2 * Real.pi * I *
        Complex.exp (2 * Real.pi * I *
          ((principalFiveTermLatticeArgument d m k : ℂ) / (principalRoot d : ℂ) ^ 3)) *
        (((principalRoot d : ℂ) ^ 3)⁻¹ - 1) := by
  rw [(hasDerivAt_principalFiveTermPoleFactor d m _).deriv]
  have hzero : principalFiveTermPoleFactor d m
      (principalFiveTermLatticeArgument d m k) = 0 :=
    (principalFiveTermPoleFactor_eq_zero_iff d hd m _).2 ⟨k, rfl⟩
  have he := sub_eq_zero.mp hzero
  rw [← he]
  ring

/-- The inverse simple-pole derivative has the source prefactor `εe(-z/ε)/(2πi(1-ε))`. -/
private theorem principalFiveTermPoleInverse_algebra (ε z : ℂ)
    (hε : ε ≠ 0) :
    (2 * Real.pi * I * Complex.exp (2 * Real.pi * I * (z / ε)) * (ε⁻¹ - 1))⁻¹ =
      ε * Complex.exp (2 * Real.pi * I * (-z / ε)) /
        (2 * Real.pi * I * (1 - ε)) := by
  have hexp : Complex.exp (2 * Real.pi * I * (-z / ε)) =
      (Complex.exp (2 * Real.pi * I * (z / ε)))⁻¹ := by
    rw [← Complex.exp_neg]
    congr 1
    ring
  rw [hexp]
  field_simp

/-- The explicit derivative in the slope limit equals the lattice derivative formula. -/
private theorem principalFiveTermPoleFactor_deriv_form
    (d : ℕ) (hd : 3 < d) (m k : ℤ) :
    let z₀ : ℂ := principalFiveTermLatticeArgument d m k
    let ε : ℂ := (principalRoot d : ℂ) ^ 3
    let e : ℂ := Complex.exp (2 * Real.pi * I * (z₀ / ε))
    2 * Real.pi * I *
      (Complex.exp (2 * Real.pi * I * (z₀ / (principalRoot d : ℂ) ^ 3)) /
          (principalRoot d : ℂ) ^ 3 -
        Complex.exp (2 * Real.pi * I * (z₀ + m * (principalRoot d : ℂ)))) =
      2 * Real.pi * I * e * (ε⁻¹ - 1) := by
  dsimp only
  calc
    _ = deriv (principalFiveTermPoleFactor d m)
        (principalFiveTermLatticeArgument d m k) :=
      (hasDerivAt_principalFiveTermPoleFactor d m _).deriv.symm
    _ = _ := deriv_principalFiveTermPoleFactor_latticeArgument d hd m k

/-- The reciprocal pole factor has residue `ε e(-z/ε)/(2πi(1-ε))` at each lattice argument:
`(z - z_{(m,k)})/(e(z/ε) - q^m e(z))` tends to that value. -/
theorem tendsto_sub_div_principalFiveTermPoleFactor (d : ℕ) (hd : 3 < d) (m k : ℤ) :
    Tendsto (fun z : ℂ => (z - principalFiveTermLatticeArgument d m k) /
        principalFiveTermPoleFactor d m z)
      (𝓝[≠] (principalFiveTermLatticeArgument d m k : ℂ))
      (𝓝 ((principalRoot d : ℂ) ^ 3 *
        Complex.exp (2 * Real.pi * I *
          (-(principalFiveTermLatticeArgument d m k : ℂ) / (principalRoot d : ℂ) ^ 3)) /
        (2 * Real.pi * I * (1 - (principalRoot d : ℂ) ^ 3)))) := by
  let z₀ : ℂ := principalFiveTermLatticeArgument d m k
  let ε : ℂ := (principalRoot d : ℂ) ^ 3
  let e : ℂ := Complex.exp (2 * Real.pi * I * (z₀ / ε))
  have hε : ε ≠ 0 := by
    dsimp [ε]
    exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr
      (ne_of_gt (lt_trans zero_lt_one (one_lt_principalRoot d hd))))
  have hden : ε⁻¹ - 1 ≠ 0 := principalFiveTermPoleDenom_ne_zero d hd
  have hcoef : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp
  have he : e ≠ 0 := Complex.exp_ne_zero _
  have hzero : principalFiveTermPoleFactor d m z₀ = 0 :=
    (principalFiveTermPoleFactor_eq_zero_iff d hd m z₀).2 ⟨k, rfl⟩
  have hderiv := principalFiveTermPoleFactor_deriv_form d hd m k
  have hslope := (hasDerivAt_principalFiveTermPoleFactor d m z₀).tendsto_slope
  rw [slope_fun_def_field, hzero] at hslope
  rw [hderiv] at hslope
  have hinv := hslope.inv₀ (mul_ne_zero (mul_ne_zero hcoef he) hden)
  have hvalue := principalFiveTermPoleInverse_algebra ε z₀ hε
  rw [hvalue] at hinv
  convert hinv using 1
  funext z
  simp only [inv_div, sub_zero, z₀]

/-! ### The residue kernel

The kernel of [RW26, Radchenko, Wheeler (2026), Section 3.2] divided by the pole factor. It is
defined through the five-term kernel so that its tail bounds are inherited. -/

/-- The residue kernel `K̃_m(z) = Φ_{m,0}(z)/Φ_{m+p,0}(z+y) · e(phase)/(e(z/ε) - q^m e(z))` of
[RW26, Radchenko, Wheeler (2026), Section 3.2], written as the five-term kernel
`principalFiveTermKernel` times `(1 - q^m e(z))/(e(z/ε) - q^m e(z))`. -/
def principalFiveTermResidueKernel (d : ℕ) (ℓ p : ℤ) (w y : ℝ) (m : ℤ) (z : ℂ) : ℂ :=
  principalFiveTermKernel d ℓ p w y m z *
    (1 - Complex.exp (2 * Real.pi * I * (z + m * (principalRoot d : ℂ)))) /
      principalFiveTermPoleFactor d m z

/-- The residue of the residue kernel at a lattice argument, before its identification with the
finite dilogarithm values: `ε/(2πi(1-ε)) · e(-z/ε + phase) · Φ^cont_{m,0}(z)/Φ^cont_{m+p,0}(z+y)`,
with the continued products of `SICs.Principal.Dilogarithm.Faddeev.Continuation`. -/
def principalFiveTermKernelResidue (d : ℕ) (ℓ p : ℤ) (w y : ℝ) (m : ℤ) (z : ℂ) : ℂ :=
  (principalRoot d : ℂ) ^ 3 / (2 * Real.pi * I * (1 - (principalRoot d : ℂ) ^ 3)) *
    Complex.exp (2 * Real.pi * I *
      (-z / (principalRoot d : ℂ) ^ 3 + principalFiveTermPhase d ℓ w m z)) *
    (principalFaddeevContinued d m 0 z /
      principalFaddeevContinued d (m + p) 0 (z + y))

/-- As germs, the residue kernel is `Φ_{m,0}(z)/Φ_{m+p,0}(z+y) · e(phase)/(e(z/ε) - q^m e(z))`,
by the left index shift law `principalFaddeev_index_add_one_left_eventuallyEq`. -/
theorem principalFiveTermResidueKernel_eventuallyEq (d : ℕ) (hd : 3 < d) (ℓ p : ℤ)
    (w y : ℝ) (m : ℤ) (z : ℂ) :
    principalFiveTermResidueKernel d ℓ p w y m =ᶠ[𝓝[≠] z]
      (fun ζ => principalFaddeev d m 0 ζ / principalFaddeev d (m + p) 0 (ζ + y) *
        Complex.exp (2 * Real.pi * I * principalFiveTermPhase d ℓ w m ζ) /
          principalFiveTermPoleFactor d m ζ) := by
  filter_upwards [principalFaddeev_index_add_one_left_eventuallyEq d hd m 0 z]
    with ζ hζ
  unfold principalFiveTermResidueKernel principalFiveTermKernel
  calc
    _ = (principalFaddeev d (m + 1) 0 ζ *
          (1 - Complex.exp (2 * Real.pi * I * (ζ + m * (principalRoot d : ℂ))))) /
        principalFaddeev d (m + p) 0 (ζ + y) *
          Complex.exp (2 * Real.pi * I * principalFiveTermPhase d ℓ w m ζ) /
        principalFiveTermPoleFactor d m ζ := by ring
    _ = _ := by rw [hζ]

/-- The raw product tends to its continued value at a source lattice argument. -/
private theorem tendsto_principalFaddeev_latticeArgument (d : ℕ) (hd : 3 < d)
    (m k : ℤ) :
    Tendsto (principalFaddeev d m 0)
      (𝓝[≠] (principalFiveTermLatticeArgument d m k : ℂ))
      (𝓝 (principalFaddeevContinued d m 0
        (principalFiveTermLatticeArgument d m k))) := by
  have harg := congrArg (fun z : ℝ => (z : ℂ))
    (fracSymplecticFormRat_rationalCharacteristic d hd m k)
  rw [ofReal_fracSymplecticFormRat] at harg
  have ht := tendsto_principalFaddeev_continued_characteristic d hd
    (principalFiveTermRationalCharacteristic d m k) 0
  rw [nQPInt_principalFiveTermRationalCharacteristic d hd m k, neg_neg, add_zero, harg] at ht
  exact ht

/-- Translation by a lattice argument carries the punctured germ at `z_x` to that at
`z_{x+v}`. -/
private theorem tendsto_add_principalFiveTermLatticeArgument (d : ℕ)
    (m k v₁ v₂ : ℤ) :
    Tendsto (fun z : ℂ => z + (principalFiveTermLatticeArgument d v₁ v₂ : ℂ))
      (𝓝[≠] (principalFiveTermLatticeArgument d m k : ℂ))
      (𝓝[≠] (principalFiveTermLatticeArgument d (m + v₁) (k + v₂) : ℂ)) := by
  have hadd : (principalFiveTermLatticeArgument d m k : ℂ) +
      (principalFiveTermLatticeArgument d v₁ v₂ : ℂ) =
      (principalFiveTermLatticeArgument d (m + v₁) (k + v₂) : ℂ) := by
    exact_mod_cast (principalFiveTermLatticeArgument_add d m k v₁ v₂).symm
  simpa only [hadd] using
    tendsto_add_const_nhdsNE (principalFiveTermLatticeArgument d v₁ v₂ : ℂ)
      (principalFiveTermLatticeArgument d m k : ℂ)

/-- The continued product does not vanish at a source lattice argument. -/
private theorem continued_ne_zero_latticeArgument (d : ℕ)
    (hd : 3 < d) (m k : ℤ) :
    principalFaddeevContinued d m 0
      (principalFiveTermLatticeArgument d m k) ≠ 0 := by
  have harg := congrArg (fun z : ℝ => (z : ℂ))
    (fracSymplecticFormRat_rationalCharacteristic d hd m k)
  rw [ofReal_fracSymplecticFormRat] at harg
  have h := principalFaddeevContinued_characteristic_ne_zero d hd
    (principalFiveTermRationalCharacteristic d m k) 0
  rw [nQPInt_principalFiveTermRationalCharacteristic d hd m k, neg_neg, add_zero, harg] at h
  exact h

/-- The quotient of raw products tends to the quotient of their continued lattice values. -/
private theorem tendsto_principalFaddeev_div_latticeArgument (d : ℕ)
    (hd : 3 < d) (m k v₁ v₂ : ℤ) :
    Tendsto (fun z : ℂ => principalFaddeev d m 0 z /
        principalFaddeev d (m + v₁) 0
          (z + principalFiveTermLatticeArgument d v₁ v₂))
      (𝓝[≠] (principalFiveTermLatticeArgument d m k : ℂ))
      (𝓝 (principalFaddeevContinued d m 0
          (principalFiveTermLatticeArgument d m k) /
        principalFaddeevContinued d (m + v₁) 0
          (principalFiveTermLatticeArgument d m k +
            principalFiveTermLatticeArgument d v₁ v₂))) := by
  have hadd : (principalFiveTermLatticeArgument d m k : ℂ) +
      (principalFiveTermLatticeArgument d v₁ v₂ : ℂ) =
      (principalFiveTermLatticeArgument d (m + v₁) (k + v₂) : ℂ) := by
    exact_mod_cast (principalFiveTermLatticeArgument_add d m k v₁ v₂).symm
  have hn := tendsto_principalFaddeev_latticeArgument d hd m k
  have hs := tendsto_add_principalFiveTermLatticeArgument d m k v₁ v₂
  have hd₀ := (tendsto_principalFaddeev_latticeArgument d hd
    (m + v₁) (k + v₂)).comp hs
  have hd₁ := hd₀
  rw [Function.comp_def, ← hadd] at hd₁
  have hdn := continued_ne_zero_latticeArgument d hd
    (m + v₁) (k + v₂)
  rw [← hadd] at hdn
  exact hn.div hd₁ hdn

/-- **The residue at a lattice argument.** With `y = z_v` and `p = v₁`, the residue kernel has
a simple pole at `z_x`, `x = (m, k)`, with residue `principalFiveTermKernelResidue`: the
continued products are analytic and nonzero at the lattice arguments `z_x` and
`z_x + z_v = z_{x+v}` (`analyticAt_principalFaddeevContinued_characteristic`,
`principalFaddeevContinued_characteristic_ne_zero` at the characteristics of
`SICs.Principal.Dilogarithm.Faddeev.FiveTerm.FiniteCharacteristics`). This is the residue
evaluation in [RW26, Radchenko, Wheeler (2026), Section 3.2]. -/
theorem tendsto_sub_mul_principalFiveTermResidueKernel (d : ℕ) (hd : 3 < d)
    (ℓ : ℤ) (w : ℝ) (m k v₁ v₂ : ℤ) :
    Tendsto (fun z : ℂ => (z - principalFiveTermLatticeArgument d m k) *
        principalFiveTermResidueKernel d ℓ v₁ w (principalFiveTermLatticeArgument d v₁ v₂) m z)
      (𝓝[≠] (principalFiveTermLatticeArgument d m k : ℂ))
      (𝓝 (principalFiveTermKernelResidue d ℓ v₁ w (principalFiveTermLatticeArgument d v₁ v₂) m
        (principalFiveTermLatticeArgument d m k))) := by
  let z₀ : ℂ := principalFiveTermLatticeArgument d m k
  let y : ℝ := principalFiveTermLatticeArgument d v₁ v₂
  have hq := tendsto_principalFaddeev_div_latticeArgument d hd m k v₁ v₂
  have hp : Tendsto (fun z : ℂ => Complex.exp
      (2 * Real.pi * I * principalFiveTermPhase d ℓ w m z)) (𝓝[≠] z₀)
      (𝓝 (Complex.exp (2 * Real.pi * I * principalFiveTermPhase d ℓ w m z₀))) := by
    have hc : ContinuousAt (fun z : ℂ => Complex.exp
        (2 * Real.pi * I * principalFiveTermPhase d ℓ w m z)) z₀ := by
      unfold principalFiveTermPhase
      fun_prop
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have hr := tendsto_sub_div_principalFiveTermPoleFactor d hd m k
  have ht := (hq.mul hp).mul hr
  have heq := principalFiveTermResidueKernel_eventuallyEq d hd ℓ v₁ w y m z₀
  have hevent : (fun z : ℂ => (z - z₀) *
      principalFiveTermResidueKernel d ℓ v₁ w y m z) =ᶠ[𝓝[≠] z₀]
      (fun z => (principalFaddeev d m 0 z /
          principalFaddeev d (m + v₁) 0 (z + y) *
            Complex.exp (2 * Real.pi * I * principalFiveTermPhase d ℓ w m z)) *
              ((z - z₀) / principalFiveTermPoleFactor d m z)) := by
    filter_upwards [heq] with z hz
    rw [hz]
    ring
  convert ht.congr' hevent.symm using 1
  congr 1
  dsimp [principalFiveTermKernelResidue, z₀, y]
  rw [mul_add]
  rw [Complex.exp_add]
  ring

/-! ### The bicharacter phase

At the lattice arguments the exponential of the kernel phase with the residue factor `e(-z/ε)`
is the bicharacter of the two source pairs. -/

/-- Integral changes of the source lifts preserve their bicharacter pairing. -/
private theorem principalFiveTermBicharacter_eq_theta_rational (d : ℕ) (hd : 3 < d)
    (m k u₁ u₂ : ℤ) :
    principalDilogBicharacter d (principalFiveTermCharacteristicResidue d m k)
        (principalFiveTermCharacteristicResidue d u₁ u₂) =
      thetaBicharacter (principalFiveTermRationalCharacteristic d m k)
        (principalFiveTermRationalCharacteristic d u₁ u₂) (principalA d : Mat(2, ℤ)) := by
  let r := principalFiveTermRationalCharacteristic d m k
  let s := principalFiveTermRationalCharacteristic d u₁ u₂
  let r' := zmodCharacteristic (principalDilogOrder d)
    (principalFiveTermCharacteristicResidue d m k)
  let s' := zmodCharacteristic (principalDilogOrder d)
    (principalFiveTermCharacteristicResidue d u₁ u₂)
  have hr := principalA_mem_gammaSubgroup_characteristic d hd m k
  have hs := principalA_mem_gammaSubgroup_characteristic d hd u₁ u₂
  have her := isIntegralIndex_characteristicResidue_sub
    d hd m k
  have hes := isIntegralIndex_characteristicResidue_sub
    d hd u₁ u₂
  have hr' : r + (r' - r) = r' := by abel
  have hs' : s + (s' - s) = s' := by abel
  have hgs' : principalA d ∈ gammaSubgroup s' := by
    exact mem_gammaSubgroup_of_isIntegralIndex_sub hes hs
  have hfirst := thetaBicharacter_add_of_isIntegralIndex_left (principalA d) hr hgs' her
  rw [hr'] at hfirst
  have hsecond := thetaBicharacter_add_of_isIntegralIndex_left (principalA d) hs hr hes
  rw [hs'] at hsecond
  change thetaBicharacter r' s' (principalA d : Mat(2, ℤ)) = _
  calc
    _ = thetaBicharacter r s' (principalA d : Mat(2, ℤ)) := hfirst
    _ = thetaBicharacter s' r (principalA d : Mat(2, ℤ)) := thetaBicharacter_comm _ _ _
    _ = thetaBicharacter s r (principalA d : Mat(2, ℤ)) := hsecond
    _ = _ := thetaBicharacter_comm _ _ _

/-- The pairing of source residues is the exponential of `-k(r_u)₁ - m(r_u)₀`. -/
private theorem principalFiveTermBicharacter_eq_exp_rational (d : ℕ) (hd : 3 < d)
    (m k u₁ u₂ : ℤ) :
    principalDilogBicharacter d (principalFiveTermCharacteristicResidue d m k)
        (principalFiveTermCharacteristicResidue d u₁ u₂) =
      Complex.exp (2 * Real.pi * I *
        (((-(k : ℚ)) * (principalFiveTermRationalCharacteristic d u₁ u₂) 1 -
          (m : ℚ) * (principalFiveTermRationalCharacteristic d u₁ u₂) 0 : ℚ) : ℂ)) := by
  let r := principalFiveTermRationalCharacteristic d m k
  let s := principalFiveTermRationalCharacteristic d u₁ u₂
  have hrow := ratVecAction_rationalCharacteristic_sub d hd m k
  have hk₁ : ((principalA d 0 0 : ℚ) - 1) * r 0 +
      (principalA d 0 1 : ℚ) * r 1 = (-k : ℤ) := by
    have h := congrFun hrow 0
    simp only [Pi.sub_apply, ratVecAction, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.map_apply] at h
    linear_combination h
  have hk₂ : (principalA d 1 0 : ℚ) * r 0 +
      ((principalA d 1 1 : ℚ) - 1) * r 1 = m := by
    have h := congrFun hrow 1
    simp only [Pi.sub_apply, ratVecAction, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.map_apply] at h
    linear_combination h
  rw [principalFiveTermBicharacter_eq_theta_rational d hd m k u₁ u₂,
    thetaBicharacter_eq_exp (principalA d) hk₁ hk₂
      (principalA_mem_gammaSubgroup_characteristic d hd u₁ u₂)]
  rfl

/-- The second coordinate of `(A_d-I)r_u=(-u₂,u₁)` determines `u₁`. -/
private theorem principalFiveTermRationalCharacteristic_second (d : ℕ) (hd : 3 < d)
    (u₁ u₂ : ℤ) :
    (u₁ : ℂ) = (d : ℂ) * ((d : ℂ) - 2) *
        (principalFiveTermRationalCharacteristic d u₁ u₂ 0 : ℂ) -
      (d : ℂ) * (principalFiveTermRationalCharacteristic d u₁ u₂ 1 : ℂ) := by
  have h := congrFun (ratVecAction_rationalCharacteristic_sub d hd u₁ u₂) 1
  simp only [ratVecAction, coe_principalA, neg_mul, Matrix.mulVec_fin_two,
    Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.map_apply, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Int.cast_mul,
    Int.cast_sub, Int.cast_natCast, Int.cast_one, Int.cast_pow, Int.cast_ofNat,
    Matrix.cons_val_one, Int.cast_neg, Pi.sub_apply] at h
  have hq : (u₁ : ℚ) = (d : ℚ) * ((d : ℚ) - 2) *
      principalFiveTermRationalCharacteristic d u₁ u₂ 0 -
      (d : ℚ) * principalFiveTermRationalCharacteristic d u₁ u₂ 1 := by
    linear_combination -h
  exact_mod_cast hq

/-- The complex source argument is the symplectic argument of its rational characteristic. -/
private theorem rationalCharacteristic_argument_complex (d : ℕ)
    (hd : 3 < d) (u₁ u₂ : ℤ) :
    (principalFiveTermLatticeArgument d u₁ u₂ : ℂ) =
      (principalFiveTermRationalCharacteristic d u₁ u₂ 1 : ℂ) *
        (principalRoot d : ℂ) -
      (principalFiveTermRationalCharacteristic d u₁ u₂ 0 : ℂ) := by
  have h := (fracSymplecticFormRat_rationalCharacteristic
    d hd u₁ u₂).symm
  simp only [fracSymplecticFormRat] at h
  exact_mod_cast h

/-- **The phase identity.** For source pairs `x = (m, k)` and `u = (u₁, u₂)`, with `w = z_u` and
`ℓ = u₁ + 1`, `e(-z_x/ε) e(phase_m(z_x)) = ⟨x; u⟩`: the display in the proof of
[RW26, Radchenko, Wheeler (2026), Section 3.2, Theorem 2, `thm:fg.equs`], in the residue
coordinates of `SICs.Principal.Dilogarithm.Group`. -/
theorem principalFiveTermResiduePhase_eq_bicharacter (d : ℕ) (hd : 3 < d) (m k u₁ u₂ : ℤ) :
    Complex.exp (2 * Real.pi * I *
        (-(principalFiveTermLatticeArgument d m k : ℂ) / (principalRoot d : ℂ) ^ 3 +
          principalFiveTermPhase d (u₁ + 1) (principalFiveTermLatticeArgument d u₁ u₂) m
            (principalFiveTermLatticeArgument d m k))) =
      principalDilogBicharacter d (principalFiveTermCharacteristicResidue d m k)
        (principalFiveTermCharacteristicResidue d u₁ u₂) := by
  let ρ : ℂ := principalRoot d
  let ε : ℂ := ρ ^ 3
  let c : ℂ := (d : ℂ) * ((d : ℂ) - 2)
  let z : ℂ := principalFiveTermLatticeArgument d m k
  let w : ℝ := principalFiveTermLatticeArgument d u₁ u₂
  let s := principalFiveTermRationalCharacteristic d u₁ u₂
  have hε : ε ≠ 0 := pow_ne_zero 3 (ofReal_principalRoot_ne_zero d hd)
  have hz : z / ε - z = (m : ℂ) * ρ + k := by
    dsimp [z, ε, ρ]
    exact_mod_cast principalFiveTermLatticeArgument_div_sub_self d hd m k
  have halg := FiniteFiveTerm.residuePhase_algebra
    ρ ε c (1 - (d : ℂ)) z (w : ℂ)
    (s 0 : ℂ) (s 1 : ℂ) m k u₁ hε hz
    (rationalCharacteristic_argument_complex d hd u₁ u₂)
    (by
      rw [principalFiveTermRationalCharacteristic_second d hd u₁ u₂]
      ring)
    (by
      simpa [ε, c, ρ, sub_eq_add_neg, add_assoc] using
        congrArg Complex.ofReal (principalRoot_pow_three_eq d hd))
  have hphase : -z / ε + principalFiveTermPhase d (u₁ + 1) w m z =
        (-(k : ℂ) * (s 1 : ℂ) - (m : ℂ) * (s 0 : ℂ)) -
          (k : ℂ) * ((u₁ : ℂ) + 1) := by
    simpa [principalFiveTermPhase, z, w, ε, c, ρ, add_assoc] using halg
  rw [principalFiveTermBicharacter_eq_exp_rational d hd m k u₁ u₂]
  apply exp_two_pi_I_eq_of_sub_intCast _ _ (-(k * (u₁ + 1)))
  change (-z / ε + principalFiveTermPhase d (u₁ + 1) w m z) -
    (((-(k : ℚ)) * s 1 - (m : ℚ) * s 0 : ℚ) : ℂ) = _
  rw [hphase]
  push_cast
  ring

/-! ### The residue in the continued-value types

The shifted type rule of `SICs.Principal.Dilogarithm.Faddeev.LatticeValues` gives both continued
values at the lattice arguments: off the zero class they are the finite dilogarithm values, and at
the zero class they are `F⁺(0)` or `F⁻(0)`. -/

/-- Identifies the kernel residue from any two eta-normalized continued values.
Used by `principalFiveTermKernelResidue_eq_of_types`. -/
private theorem principalFiveTermKernelResidue_eq_of_values (d : ℕ) (hd : 3 < d)
    (m k u₁ u₂ v₁ v₂ : ℤ) (num den : ℂ)
    (hnum : etaMultiplier (principalA d) *
      principalFaddeevContinued d m 0 (principalFiveTermLatticeArgument d m k) =
        num)
    (hden : etaMultiplier (principalA d) *
      principalFaddeevContinued d (m + v₁) 0
        (principalFiveTermLatticeArgument d (m + v₁) (k + v₂)) =
          den) :
    principalFiveTermKernelResidue d (u₁ + 1) v₁
        (principalFiveTermLatticeArgument d u₁ u₂)
        (principalFiveTermLatticeArgument d v₁ v₂) m
        (principalFiveTermLatticeArgument d m k) =
      (principalRoot d : ℂ) ^ 3 / (2 * Real.pi * I * (1 - (principalRoot d : ℂ) ^ 3)) *
        principalDilogBicharacter d (principalFiveTermCharacteristicResidue d m k)
          (principalFiveTermCharacteristicResidue d u₁ u₂) *
        (num / den) := by
  have hadd : (principalFiveTermLatticeArgument d m k : ℂ) +
      (principalFiveTermLatticeArgument d v₁ v₂ : ℂ) =
      (principalFiveTermLatticeArgument d (m + v₁) (k + v₂) : ℂ) := by
    exact_mod_cast (principalFiveTermLatticeArgument_add d m k v₁ v₂).symm
  have hq : principalFaddeevContinued d m 0
        (principalFiveTermLatticeArgument d m k) /
      principalFaddeevContinued d (m + v₁) 0
        (principalFiveTermLatticeArgument d (m + v₁) (k + v₂)) =
      num / den := by
    calc
      _ = (etaMultiplier (principalA d) * _ : ℂ) /
          (etaMultiplier (principalA d) * _) :=
        (mul_div_mul_left _ _ (etaMultiplier_ne_zero (principalA d))).symm
      _ = _ := by rw [hnum, hden]
  unfold principalFiveTermKernelResidue
  rw [hadd, principalFiveTermResiduePhase_eq_bicharacter d hd m k u₁ u₂, hq]

/-- The kernel residue with both continued-value types made explicit. This combines
`principalFiveTermResiduePhase_eq_bicharacter` with the type rule
`etaMultiplier_mul_principalFaddeevContinued_indices_add`
at shift zero, for the residue computation of
[RW26, Radchenko, Wheeler (2026), Section 3.2, proof of Theorem 2, `thm:fg.equs`]. -/
theorem principalFiveTermKernelResidue_eq_of_types (d : ℕ) (hd : 3 < d)
    (m k u₁ u₂ v₁ v₂ : ℤ) :
    principalFiveTermKernelResidue d (u₁ + 1) v₁
        (principalFiveTermLatticeArgument d u₁ u₂)
        (principalFiveTermLatticeArgument d v₁ v₂) m
        (principalFiveTermLatticeArgument d m k) =
      (principalRoot d : ℂ) ^ 3 / (2 * Real.pi * I * (1 - (principalRoot d : ℂ) ^ 3)) *
        principalDilogBicharacter d (principalFiveTermCharacteristicResidue d m k)
          (principalFiveTermCharacteristicResidue d u₁ u₂) *
        ((if 0 ≤ principalFiveTermLatticeIndex d m k then
            principalDilogE d (principalFiveTermCharacteristicResidue d m k) else
            principalDilogEMinus d (principalFiveTermCharacteristicResidue d m k)) /
          (if 0 ≤ principalFiveTermLatticeIndex d (m + v₁) (k + v₂) then
            principalDilogE d (principalFiveTermCharacteristicResidue d (m + v₁) (k + v₂)) else
            principalDilogEMinus d
              (principalFiveTermCharacteristicResidue d (m + v₁) (k + v₂)))) := by
  apply principalFiveTermKernelResidue_eq_of_values d hd m k u₁ u₂ v₁ v₂
  · simpa using
      (etaMultiplier_mul_principalFaddeevContinued_indices_add
        d hd m k 0)
  · simpa using
      (etaMultiplier_mul_principalFaddeevContinued_indices_add
        d hd (m + v₁) (k + v₂) 0)

end SIC

end
