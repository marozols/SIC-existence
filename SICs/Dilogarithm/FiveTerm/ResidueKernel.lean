/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Dilogarithm.FiveTerm.Parameters
import SICs.SpecialFunctions.Faddeev.FiveTerm.Algebra

/-!
# The residue kernel of the finite five-term relation

The kernel whose residues at the source arguments are the terms of the finite five-term sum,
for a letter word at an attractive fixed point: its pole factor, its simple poles, their
residues, and the bicharacter phase.

This module follows [RW26, Radchenko, Wheeler (2026), Section 3.2, the proof of Theorem 2,
`thm:fg.equs`, the computation of equation (7), `eq:Fgpm.5term`] for `γ = ∏_j T^{b_j}S` at an
attractive fixed point `τ`, `ε = j_γ(τ)`, `q = e(τ)`, and `n = h = 0`. The principal word is
treated directly in `SICs.Principal.Dilogarithm.Faddeev.FiveTerm.ResidueKernel`.

## The argument

The source divides the integrand of Theorem 3 with numerator index `m` by
`e(z/ε) - q^m e(z)`. Here the residue kernel is the five-term word kernel
`Φ_{m+1,0}(z)/Φ_{m+p,0}(z+y) · e(phase)` multiplied by `(1 - q^m e(z))/(e(z/ε) - q^m e(z))`,
which by the left index shift law is `Φ_{m,0}(z)/Φ_{m+p,0}(z+y) · e(phase)/(e(z/ε) - q^m e(z))`
as germs. The pole factor vanishes exactly at the source arguments `z_{(m,k)}`, `k ∈ ℤ`, since
`z_{(m,k)}/ε - z_{(m,k)} = mτ + k`; the zeros are simple, and the reciprocal has residue
`ε e(-z/ε)/(2πi(1-ε))` there. At `z = z_{(m,k)}` with `y = z_v` and `p = v₁`, both word products
have continued values, analytic and nonzero, so the kernel has a simple pole with residue the
reciprocal residue times `e(phase)` times the quotient of continued values.

At the source arguments the phase is a bicharacter: with `w = z_u` and `ℓ = u₁ + 1`,
`e(-z_x/ε) e(phase_m(z_x)) = ⟨x; u⟩`, the display in the proof of Theorem 2 of Section 3.2.
The continued values are the finite dilogarithm values of
`etaMultiplier_mul_faddeevWordContinued_latticeArgument`, with the type rule at the zero class.
-/

noncomputable section

open Complex Filter
open scoped Topology MatrixGroups

namespace SIC

/-! The denominator `ε⁻¹ - 1` is nonzero at an attractive fixed point. -/

/-- The source-argument denominator is nonzero; used by `fiveTermPoleFactor_eq_zero_iff`. -/
private theorem fiveTermPoleDenom_ne_zero {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) :
    (fltDenominator (γ : Mat(2, ℤ)) (τ : ℂ))⁻¹ - 1 ≠ 0 := by
  have hi : (fltDenominator (γ : Mat(2, ℤ)) τ)⁻¹ < 1 :=
    (inv_lt_one₀ h.fltDenominator_pos).2 h.one_lt_fltDenominator
  have hne : (fltDenominator (γ : Mat(2, ℤ)) τ)⁻¹ - 1 ≠ 0 :=
    ne_of_lt (sub_neg.mpr hi)
  exact_mod_cast hne

/-! ### The pole factor -/

/-- The pole factor `e(z/ε) - q^m e(z)` of the residue kernel, `ε = j_γ(τ)`, `q = e(τ)`, from the
denominator of the integrand in [RW26, Radchenko, Wheeler (2026), Section 3.2]. -/
def fiveTermPoleFactor (γ : SL(2, ℤ)) (τ : ℝ) (m : ℤ) (z : ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * I * (z / fltDenominator (γ : Mat(2, ℤ)) (τ : ℂ))) -
    Complex.exp (2 * Real.pi * I * (z + m * (τ : ℂ)))

/-- The zeros of the pole factor are exactly the source arguments `z_{(m,k)}`, `k ∈ ℤ`. -/
theorem fiveTermPoleFactor_eq_zero_iff {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (m : ℤ) (z : ℂ) :
    fiveTermPoleFactor γ τ m z = 0 ↔ ∃ k : ℤ, z = (fiveTermLatticeArgument γ τ m k : ℂ) := by
  have hc : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp
  have hden := fiveTermPoleDenom_ne_zero h
  constructor
  · intro hz
    rw [fiveTermPoleFactor, sub_eq_zero, Complex.exp_eq_exp_iff_exists_int] at hz
    obtain ⟨k, hk⟩ := hz
    have heq : z / fltDenominator (γ : Mat(2, ℤ)) (τ : ℂ) =
        z + m * (τ : ℂ) + k := by
      apply mul_left_cancel₀ hc
      calc
        (2 * Real.pi * I) *
            (z / fltDenominator (γ : Mat(2, ℤ)) (τ : ℂ)) =
          (2 * Real.pi * I) * (z + m * (τ : ℂ)) + (k : ℂ) * (2 * Real.pi * I) := hk
        _ = _ := by ring
    refine ⟨k, ?_⟩
    have hcast : (fiveTermLatticeArgument γ τ m k : ℂ) =
        ((m : ℂ) * (τ : ℂ) + k) /
          ((fltDenominator (γ : Mat(2, ℤ)) (τ : ℂ))⁻¹ - 1) := by
      simp [fiveTermLatticeArgument]
    rw [hcast, eq_div_iff hden]
    rw [div_eq_mul_inv] at heq
    linear_combination heq
  · rintro ⟨k, rfl⟩
    unfold fiveTermPoleFactor
    rw [sub_eq_zero, Complex.exp_eq_exp_iff_exists_int]
    refine ⟨k, ?_⟩
    have harg := congrArg (fun x : ℝ => (x : ℂ))
      (fiveTermLatticeArgument_div_sub_self h m k)
    simp only [Complex.ofReal_div, Complex.ofReal_sub,
      ofReal_fltDenominator] at harg
    calc
      (2 * Real.pi * I) *
          ((fiveTermLatticeArgument γ τ m k : ℂ) /
            fltDenominator (γ : Mat(2, ℤ)) (τ : ℂ)) =
        (2 * Real.pi * I) *
          ((fiveTermLatticeArgument γ τ m k : ℂ) + m * (τ : ℂ) + k) := by
            rw [sub_eq_iff_eq_add] at harg
            rw [harg]
            push_cast
            ring
      _ = _ := by ring

/-- The derivative of the pole factor; used by `tendsto_sub_div_fiveTermPoleFactor`. -/
private theorem hasDerivAt_fiveTermPoleFactor (γ : SL(2, ℤ)) (τ : ℝ) (m : ℤ) (z : ℂ) :
    HasDerivAt (fiveTermPoleFactor γ τ m)
      (2 * Real.pi * I *
        (Complex.exp (2 * Real.pi * I *
            (z / fltDenominator (γ : Mat(2, ℤ)) (τ : ℂ))) /
          fltDenominator (γ : Mat(2, ℤ)) (τ : ℂ) -
          Complex.exp (2 * Real.pi * I * (z + m * (τ : ℂ))))) z := by
  unfold fiveTermPoleFactor
  have h₁ := ((hasDerivAt_id z).div_const
    (fltDenominator (γ : Mat(2, ℤ)) (τ : ℂ)) |>.const_mul
      (2 * Real.pi * I) |>.cexp)
  have h₂ := ((hasDerivAt_id z).add_const (m * (τ : ℂ)) |>.const_mul
    (2 * Real.pi * I) |>.cexp)
  convert h₁.sub h₂ using 1
  · funext x
    rfl
  · simp only [id_eq, mul_one]
    ring

/-- The derivative at a source argument; used by `tendsto_sub_div_fiveTermPoleFactor`. -/
private theorem deriv_fiveTermPoleFactor_latticeArgument {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (m k : ℤ) :
    deriv (fiveTermPoleFactor γ τ m) (fiveTermLatticeArgument γ τ m k) =
      2 * Real.pi * I *
        Complex.exp (2 * Real.pi * I *
          ((fiveTermLatticeArgument γ τ m k : ℂ) /
            fltDenominator (γ : Mat(2, ℤ)) (τ : ℂ))) *
        ((fltDenominator (γ : Mat(2, ℤ)) (τ : ℂ))⁻¹ - 1) := by
  rw [(hasDerivAt_fiveTermPoleFactor γ τ m _).deriv]
  have hzero : fiveTermPoleFactor γ τ m (fiveTermLatticeArgument γ τ m k) = 0 :=
    (fiveTermPoleFactor_eq_zero_iff h m _).2 ⟨k, rfl⟩
  have he := sub_eq_zero.mp hzero
  rw [← he]
  ring

/-- The reciprocal pole factor has a simple pole at `z₀ = z_{(m,k)}` with residue
`ε e(-z₀/ε)/(2πi(1-ε))`. -/
private theorem tendsto_sub_div_fiveTermPoleFactor {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (m k : ℤ) :
    Tendsto (fun z : ℂ => (z - fiveTermLatticeArgument γ τ m k) / fiveTermPoleFactor γ τ m z)
      (𝓝[≠] (fiveTermLatticeArgument γ τ m k : ℂ))
      (𝓝 (fltDenominator (γ : Mat(2, ℤ)) (τ : ℂ) *
        Complex.exp (2 * Real.pi * I *
          (-(fiveTermLatticeArgument γ τ m k : ℂ) / fltDenominator (γ : Mat(2, ℤ)) (τ : ℂ))) /
        (2 * Real.pi * I * (1 - fltDenominator (γ : Mat(2, ℤ)) (τ : ℂ))))) := by
  let z₀ : ℂ := fiveTermLatticeArgument γ τ m k
  let ε : ℂ := fltDenominator (γ : Mat(2, ℤ)) (τ : ℂ)
  let e : ℂ := Complex.exp (2 * Real.pi * I * (z₀ / ε))
  have hε : ε ≠ 0 := by
    dsimp [ε]
    exact_mod_cast h.fltDenominator_pos.ne'
  have hden : ε⁻¹ - 1 ≠ 0 := fiveTermPoleDenom_ne_zero h
  have hcoef : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp
  have he : e ≠ 0 := Complex.exp_ne_zero _
  have hzero : fiveTermPoleFactor γ τ m z₀ = 0 :=
    (fiveTermPoleFactor_eq_zero_iff h m z₀).2 ⟨k, rfl⟩
  have hslope := (hasDerivAt_fiveTermPoleFactor γ τ m z₀).tendsto_slope
  rw [slope_fun_def_field, hzero] at hslope
  have hderiv := deriv_fiveTermPoleFactor_latticeArgument h m k
  rw [← (hasDerivAt_fiveTermPoleFactor γ τ m z₀).deriv, hderiv] at hslope
  have hinv := hslope.inv₀ (mul_ne_zero (mul_ne_zero hcoef he) hden)
  have hvalue : (2 * Real.pi * I * e * (ε⁻¹ - 1))⁻¹ =
      ε * Complex.exp (2 * Real.pi * I * (-z₀ / ε)) /
        (2 * Real.pi * I * (1 - ε)) := by
    have hexp : Complex.exp (2 * Real.pi * I * (-z₀ / ε)) = e⁻¹ := by
      rw [← Complex.exp_neg]
      congr 1
      ring
    rw [hexp]
    field_simp
  rw [hvalue] at hinv
  convert hinv using 1
  funext z
  simp only [inv_div, sub_zero, z₀]

/-! ### The residue kernel and its residues -/

/-- The residue kernel `K̃_m(z) = Φ_{m,0}(z)/Φ_{m+p,0}(z+y) · e(phase)/(e(z/ε) - q^m e(z))` of
[RW26, Radchenko, Wheeler (2026), Section 3.2] for a letter word, written as the five-term word
kernel times `(1 - q^m e(z))/(e(z/ε) - q^m e(z))`. -/
def fiveTermWordResidueKernel (bs : List ℤ) (ℓ p : ℤ) (w y : ℂ) (τ : ℝ) (m : ℤ) (z : ℂ) : ℂ :=
  fiveTermWordKernel bs ℓ p w y τ m z *
    (1 - Complex.exp (2 * Real.pi * I * (z + m * (τ : ℂ)))) /
      fiveTermPoleFactor (letterWord bs) τ m z

/-- The residue of the residue kernel at a source argument, before its identification with the
finite dilogarithm values:
`ε/(2πi(1-ε)) · e(-z/ε + phase_m(z)) · Φ^cont_{m,0}(z)/Φ^cont_{m+p,0}(z+y)`. -/
def fiveTermWordKernelResidue (bs : List ℤ) (ℓ p : ℤ) (w y : ℂ) (τ : ℝ) (m : ℤ) (z : ℂ) : ℂ :=
  fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
      (2 * Real.pi * I * (1 - fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ))) *
    Complex.exp (2 * Real.pi * I *
      (-z / fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) +
        ((((letterWord bs 1 0 : ℤ) : ℂ) * z +
            fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) * m) * w /
          fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) + ℓ * (z + m * (τ : ℂ))))) *
    (faddeevWordContinued bs m 0 z τ / faddeevWordContinued bs (m + p) 0 (z + y) τ)

/-- As germs, the residue kernel is `Φ_{m,0}(z)/Φ_{m+p,0}(z+y) · e(phase)/(e(z/ε) - q^m e(z))`,
by the left index shift law of the word product. -/
theorem fiveTermWordResidueKernel_eventuallyEq {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ p : ℤ) (w y : ℂ) (m : ℤ) (z : ℂ) :
    fiveTermWordResidueKernel bs ℓ p w y τ m =ᶠ[𝓝[≠] z]
      (fun ζ => faddeevWord bs m 0 ζ τ / faddeevWord bs (m + p) 0 (ζ + y) τ *
        Complex.exp (2 * Real.pi * I *
          ((((letterWord bs 1 0 : ℤ) : ℂ) * ζ +
              fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) * m) * w /
            fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) + ℓ * (ζ + m * (τ : ℂ)))) /
        fiveTermPoleFactor (letterWord bs) τ m ζ) := by
  filter_upwards [faddeevWord_index_add_one_left_eventuallyEq bs h.ne_nil m 0
    h.periodsPos.slitPlane z] with ζ hζ
  unfold fiveTermWordResidueKernel fiveTermWordKernel
  calc
    _ = (faddeevWord bs (m + 1) 0 ζ τ *
          (1 - Complex.exp (2 * Real.pi * I * (ζ + m * (τ : ℂ))))) /
        faddeevWord bs (m + p) 0 (ζ + y) τ *
          Complex.exp (2 * Real.pi * I *
            ((((letterWord bs 1 0 : ℤ) : ℂ) * ζ +
                fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) * m) * w /
              fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) +
              ℓ * (ζ + m * (τ : ℂ)))) /
        fiveTermPoleFactor (letterWord bs) τ m ζ := by ring
    _ = _ := by rw [hζ]

/-- The source argument and index agree with the rational characteristic data. -/
private lemma fiveTermWord_characteristic_data {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (m k : ℤ) :
    (fracSymplecticFormRat (fiveTermRationalCharacteristic (letterWord bs) m k) τ : ℂ) =
        (fiveTermLatticeArgument (letterWord bs) τ m k : ℂ) ∧
      nQPInt (fiveTermRationalCharacteristic (letterWord bs) m k)
        (letterWord bs : Mat(2, ℤ)) = -m := by
  constructor
  · rw [← ofReal_fracSymplecticFormRat]
    exact_mod_cast fracSymplecticFormRat_fiveTermRationalCharacteristic h.fixedPoint m k
  · exact nQPInt_fiveTermRationalCharacteristic h.fixedPoint m k

/-- The raw word product tends to its continued value at a source argument; used by
`tendsto_sub_mul_fiveTermWordResidueKernel`. -/
private theorem tendsto_faddeevWord_latticeArgument {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (m k : ℤ) :
    Tendsto (faddeevWord bs m 0 · τ)
      (𝓝[≠] (fiveTermLatticeArgument (letterWord bs) τ m k : ℂ))
      (𝓝 (faddeevWordContinued bs m 0
        (fiveTermLatticeArgument (letterWord bs) τ m k) τ)) := by
  obtain ⟨harg, hnq⟩ := fiveTermWord_characteristic_data h m k
  have ht := tendsto_faddeevWord_continued_characteristic bs h.ne_nil
    h.fixedPoint.irrational (fun w hw => (h.periodsPos w hw).2)
    (fiveTermRationalCharacteristic (letterWord bs) m k) 0
  rw [hnq, neg_neg, add_zero, harg] at ht
  exact ht

/-- Translation by a source argument carries the punctured germ at `z_x` to that at
`z_{x+v}`; used by `tendsto_sub_mul_fiveTermWordResidueKernel`. -/
private theorem tendsto_add_fiveTermLatticeArgument (γ : SL(2, ℤ)) (τ : ℝ)
    (m k v₁ v₂ : ℤ) :
    Tendsto (fun z : ℂ => z + (fiveTermLatticeArgument γ τ v₁ v₂ : ℂ))
      (𝓝[≠] (fiveTermLatticeArgument γ τ m k : ℂ))
      (𝓝[≠] (fiveTermLatticeArgument γ τ (m + v₁) (k + v₂) : ℂ)) := by
  have hadd : (fiveTermLatticeArgument γ τ m k : ℂ) +
      (fiveTermLatticeArgument γ τ v₁ v₂ : ℂ) =
      (fiveTermLatticeArgument γ τ (m + v₁) (k + v₂) : ℂ) := by
    exact_mod_cast (fiveTermLatticeArgument_add γ τ m k v₁ v₂).symm
  simpa only [hadd] using
    tendsto_add_const_nhdsNE (fiveTermLatticeArgument γ τ v₁ v₂ : ℂ)
      (fiveTermLatticeArgument γ τ m k : ℂ)

/-- The continued word product does not vanish at a source argument; used by
`tendsto_sub_mul_fiveTermWordResidueKernel`. -/
private theorem continued_ne_zero_fiveTermArgument {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (m k : ℤ) :
    faddeevWordContinued bs m 0
      (fiveTermLatticeArgument (letterWord bs) τ m k) τ ≠ 0 := by
  obtain ⟨harg, hnq⟩ := fiveTermWord_characteristic_data h m k
  have hn := faddeevWordContinued_characteristic_ne_zero bs h.ne_nil
    h.fixedPoint.irrational (fun w hw => (h.periodsPos w hw).2)
    (fiveTermRationalCharacteristic (letterWord bs) m k) 0
  rw [hnq, neg_neg, add_zero, harg] at hn
  exact hn

/-- The quotient of raw products tends to the quotient of continued values; used by
`tendsto_sub_mul_fiveTermWordResidueKernel`. -/
private theorem tendsto_faddeevWord_div_latticeArgument {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (m k v₁ v₂ : ℤ) :
    Tendsto (fun z : ℂ => faddeevWord bs m 0 z τ /
        faddeevWord bs (m + v₁) 0
          (z + fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ)
      (𝓝[≠] (fiveTermLatticeArgument (letterWord bs) τ m k : ℂ))
      (𝓝 (faddeevWordContinued bs m 0
          (fiveTermLatticeArgument (letterWord bs) τ m k) τ /
        faddeevWordContinued bs (m + v₁) 0
          (fiveTermLatticeArgument (letterWord bs) τ m k +
            fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ)) := by
  have hadd : (fiveTermLatticeArgument (letterWord bs) τ m k : ℂ) +
      (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂ : ℂ) =
      (fiveTermLatticeArgument (letterWord bs) τ (m + v₁) (k + v₂) : ℂ) := by
    exact_mod_cast (fiveTermLatticeArgument_add (letterWord bs) τ m k v₁ v₂).symm
  have hn := tendsto_faddeevWord_latticeArgument h m k
  have hs := tendsto_add_fiveTermLatticeArgument (letterWord bs) τ m k v₁ v₂
  have hd₀ := (tendsto_faddeevWord_latticeArgument h
    (m + v₁) (k + v₂)).comp hs
  have hd₁ := hd₀
  rw [Function.comp_def, ← hadd] at hd₁
  have hdn := continued_ne_zero_fiveTermArgument h (m + v₁) (k + v₂)
  rw [← hadd] at hdn
  exact hn.div hd₁ hdn

/-- At a source argument `z_{(m,k)}` with `y = z_v` and `p = v₁`, the residue kernel has a simple
pole whose residue is `fiveTermWordKernelResidue`. -/
theorem tendsto_sub_mul_fiveTermWordResidueKernel {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (ℓ : ℤ) (w : ℂ) (m k v₁ v₂ : ℤ) :
    Tendsto (fun z : ℂ => (z - fiveTermLatticeArgument (letterWord bs) τ m k) *
        fiveTermWordResidueKernel bs ℓ v₁ w (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂)
          τ m z)
      (𝓝[≠] (fiveTermLatticeArgument (letterWord bs) τ m k : ℂ))
      (𝓝 (fiveTermWordKernelResidue bs ℓ v₁ w
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ m
        (fiveTermLatticeArgument (letterWord bs) τ m k))) := by
  let z₀ : ℂ := fiveTermLatticeArgument (letterWord bs) τ m k
  let y : ℂ := fiveTermLatticeArgument (letterWord bs) τ v₁ v₂
  have hq := tendsto_faddeevWord_div_latticeArgument h m k v₁ v₂
  have hp : Tendsto (fun z : ℂ => Complex.exp (2 * Real.pi * I *
      ((((letterWord bs 1 0 : ℤ) : ℂ) * z +
          fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) * m) * w /
        fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) +
        ℓ * (z + m * (τ : ℂ))))) (𝓝[≠] z₀)
      (𝓝 (Complex.exp (2 * Real.pi * I *
        ((((letterWord bs 1 0 : ℤ) : ℂ) * z₀ +
            fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) * m) * w /
          fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) +
          ℓ * (z₀ + m * (τ : ℂ)))))) := by
    have hc : ContinuousAt (fun z : ℂ => Complex.exp (2 * Real.pi * I *
        ((((letterWord bs 1 0 : ℤ) : ℂ) * z +
            fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) * m) * w /
          fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) +
          ℓ * (z + m * (τ : ℂ))))) z₀ := by fun_prop
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have hr := tendsto_sub_div_fiveTermPoleFactor h.fixedPoint m k
  have ht := (hq.mul hp).mul hr
  have heq := fiveTermWordResidueKernel_eventuallyEq h ℓ v₁ w y m z₀
  have hevent : (fun z : ℂ => (z - z₀) *
      fiveTermWordResidueKernel bs ℓ v₁ w y τ m z) =ᶠ[𝓝[≠] z₀]
      (fun z => (faddeevWord bs m 0 z τ /
          faddeevWord bs (m + v₁) 0 (z + y) τ *
            Complex.exp (2 * Real.pi * I *
              ((((letterWord bs 1 0 : ℤ) : ℂ) * z +
                  fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) * m) * w /
                fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) +
                ℓ * (z + m * (τ : ℂ))))) *
          ((z - z₀) / fiveTermPoleFactor (letterWord bs) τ m z)) := by
    filter_upwards [heq] with z hz
    rw [hz]
    ring
  convert ht.congr' hevent.symm using 1
  congr 1
  dsimp [fiveTermWordKernelResidue, z₀, y]
  rw [mul_add]
  rw [Complex.exp_add]
  ring

/-! ### The bicharacter phase and the residues as finite values -/

/-- Integral changes of source lifts preserve their pairing; used by
`fiveTermResiduePhase_eq_bicharacter`. -/
private theorem fiveTermBicharacter_eq_theta_rational {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (m k u₁ u₂ : ℤ) :
    fixedBicharacter γ (finiteDilogOrder γ) (fiveTermCharacteristicResidue γ m k)
        (fiveTermCharacteristicResidue γ u₁ u₂) =
      thetaBicharacter (fiveTermRationalCharacteristic γ m k)
        (fiveTermRationalCharacteristic γ u₁ u₂) (γ : Mat(2, ℤ)) := by
  let r := fiveTermRationalCharacteristic γ m k
  let s := fiveTermRationalCharacteristic γ u₁ u₂
  let r' := zmodCharacteristic (finiteDilogOrder γ)
    (fiveTermCharacteristicResidue γ m k)
  let s' := zmodCharacteristic (finiteDilogOrder γ)
    (fiveTermCharacteristicResidue γ u₁ u₂)
  let _ : NeZero (finiteDilogOrder γ) := finiteDilogOrder_neZero h
  have hr := mem_gammaSubgroup_fiveTermRationalCharacteristic h m k
  have hs := mem_gammaSubgroup_fiveTermRationalCharacteristic h u₁ u₂
  have her := isIntegralIndex_latticeCharacteristic_sub_lift γ
    (finiteDilogOrder γ) ![-k, m]
  have hes := isIntegralIndex_latticeCharacteristic_sub_lift γ
    (finiteDilogOrder γ) ![-u₂, u₁]
  change IsIntegralIndex (r' - r) at her
  change IsIntegralIndex (s' - s) at hes
  have hr' : r + (r' - r) = r' := by abel
  have hs' : s + (s' - s) = s' := by abel
  have hgs' : γ ∈ gammaSubgroup s' :=
    mem_gammaSubgroup_of_isIntegralIndex_sub hes hs
  have hfirst := thetaBicharacter_add_of_isIntegralIndex_left γ hr hgs' her
  change thetaBicharacter (r + (r' - r)) s' (γ : Mat(2, ℤ)) =
    thetaBicharacter r s' (γ : Mat(2, ℤ)) at hfirst
  rw [hr'] at hfirst
  have hsecond := thetaBicharacter_add_of_isIntegralIndex_left γ hs hr hes
  change thetaBicharacter (s + (s' - s)) r (γ : Mat(2, ℤ)) =
    thetaBicharacter s r (γ : Mat(2, ℤ)) at hsecond
  rw [hs'] at hsecond
  change thetaBicharacter r' s' (γ : Mat(2, ℤ)) = _
  calc
    _ = thetaBicharacter r s' (γ : Mat(2, ℤ)) := hfirst
    _ = thetaBicharacter s' r (γ : Mat(2, ℤ)) := thetaBicharacter_comm _ _ _
    _ = thetaBicharacter s r (γ : Mat(2, ℤ)) := hsecond
    _ = _ := thetaBicharacter_comm _ _ _

/-- The source-pair pairing is the exponential of `-k(r_u)₁-m(r_u)₀`; used by
`fiveTermResiduePhase_eq_bicharacter`. -/
private theorem fiveTermBicharacter_eq_exp_rational {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (m k u₁ u₂ : ℤ) :
    fixedBicharacter γ (finiteDilogOrder γ) (fiveTermCharacteristicResidue γ m k)
        (fiveTermCharacteristicResidue γ u₁ u₂) =
      Complex.exp (2 * Real.pi * I *
        (((-(k : ℚ)) * (fiveTermRationalCharacteristic γ u₁ u₂) 1 -
          (m : ℚ) * (fiveTermRationalCharacteristic γ u₁ u₂) 0 : ℚ) : ℂ)) := by
  let _ : NeZero (finiteDilogOrder γ) := finiteDilogOrder_neZero h
  let r := fiveTermRationalCharacteristic γ m k
  let s := fiveTermRationalCharacteristic γ u₁ u₂
  have hrow := ratVecAction_latticeCharacteristicLift_sub γ (finiteDilogOrder γ)
    (det_sub_one_eq_neg_finiteDilogOrder h) ![-k, m]
  change ratVecAction (γ : Mat(2, ℤ)) r - r =
    (fun i => (![-k, m] i : ℚ)) at hrow
  have hk₁ : ((γ 0 0 : ℚ) - 1) * r 0 + (γ 0 1 : ℚ) * r 1 = (-k : ℤ) := by
    have heq := congrFun hrow 0
    simp only [Pi.sub_apply, ratVecAction, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.map_apply] at heq
    linear_combination heq
  have hk₂ : (γ 1 0 : ℚ) * r 0 + ((γ 1 1 : ℚ) - 1) * r 1 = m := by
    have heq := congrFun hrow 1
    simp only [Pi.sub_apply, ratVecAction, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.map_apply] at heq
    linear_combination heq
  rw [fiveTermBicharacter_eq_theta_rational h m k u₁ u₂,
    thetaBicharacter_eq_exp γ hk₁ hk₂
      (mem_gammaSubgroup_fiveTermRationalCharacteristic h u₁ u₂)]
  rfl

/-- At the source arguments, `e(-z_x/ε) e(phase_m(z_x)) = ⟨x; u⟩` for `x = (m,k)`, `w = z_u`,
`ℓ = u₁+1`: the display in [RW26, Radchenko, Wheeler (2026), Section 3.2, proof of Theorem 2,
`thm:fg.equs`]. -/
private theorem fiveTermResiduePhase_eq_bicharacter {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (m k u₁ u₂ : ℤ) :
    Complex.exp (2 * Real.pi * I *
        (-(fiveTermLatticeArgument γ τ m k : ℂ) / fltDenominator (γ : Mat(2, ℤ)) (τ : ℂ) +
          ((((γ 1 0 : ℤ) : ℂ) * fiveTermLatticeArgument γ τ m k +
              fltDenominator (γ : Mat(2, ℤ)) (τ : ℂ) * m) * fiveTermLatticeArgument γ τ u₁ u₂ /
            fltDenominator (γ : Mat(2, ℤ)) (τ : ℂ) +
            ((u₁ + 1 : ℤ) : ℂ) * (fiveTermLatticeArgument γ τ m k + m * (τ : ℂ))))) =
      fixedBicharacter γ (finiteDilogOrder γ) (fiveTermCharacteristicResidue γ m k)
        (fiveTermCharacteristicResidue γ u₁ u₂) := by
  let ρ : ℂ := τ
  let ε : ℂ := fltDenominator (γ : Mat(2, ℤ)) (τ : ℂ)
  let c : ℂ := γ 1 0
  let d : ℂ := γ 1 1
  let z : ℂ := fiveTermLatticeArgument γ τ m k
  let w : ℂ := fiveTermLatticeArgument γ τ u₁ u₂
  let s := fiveTermRationalCharacteristic γ u₁ u₂
  have hε : ε ≠ 0 := by
    dsimp [ε]
    exact_mod_cast h.fltDenominator_pos.ne'
  have hz : z / ε - z = (m : ℂ) * ρ + k := by
    dsimp [z, ε, ρ]
    exact_mod_cast fiveTermLatticeArgument_div_sub_self h m k
  have hw : w = (s 1 : ℂ) * ρ - (s 0 : ℂ) := by
    have heq := (fracSymplecticFormRat_fiveTermRationalCharacteristic
      h u₁ u₂).symm
    simp only [fracSymplecticFormRat] at heq
    dsimp [w, s, ρ]
    exact_mod_cast heq
  have halg := FiniteFiveTerm.residuePhase_algebra ρ ε c d z w
    (s 0 : ℂ) (s 1 : ℂ) m k u₁ hε hz
    hw
    (fiveTermRationalCharacteristic_second h u₁ u₂)
    (by simp [ε, c, d, ρ, fltDenominator])
  have hphase : -z / ε +
      (((c * z + ε * m) * w) / ε + (u₁ + 1 : ℤ) * (z + m * ρ)) =
      (-(k : ℂ) * (s 1 : ℂ) - (m : ℂ) * (s 0 : ℂ)) -
        (k : ℂ) * ((u₁ : ℂ) + 1) := by
    simpa [z, w, ε, c, ρ, add_assoc] using halg
  rw [fiveTermBicharacter_eq_exp_rational h m k u₁ u₂]
  apply exp_two_pi_I_eq_of_sub_intCast _ _ (-(k * (u₁ + 1)))
  change (-z / ε + (((c * z + ε * m) * w) / ε +
    (u₁ + 1 : ℤ) * (z + m * ρ))) -
      (((-(k : ℚ)) * s 1 - (m : ℚ) * s 0 : ℚ) : ℂ) = _
  rw [hphase]
  push_cast
  ring

/-- The residue of the residue kernel at `z_{(m,k)}`, with `w = z_u`, `ℓ = u₁+1`, `y = z_v`,
`p = v₁`, is `ε/(2πi(1-ε)) ⟨x; u⟩ E^±(x)/E^±(x+v)` for `x = (m,k)`, where each `E^±` is `E` for
a nonnegative lattice index and `F⁻` for a negative one, as in the proof of [RW26, Radchenko,
Wheeler (2026), Theorem 2, `thm:fg.equs`, Section 3.2]. -/
theorem fiveTermWordKernelResidue_eq_of_types {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) (m k u₁ u₂ v₁ v₂ : ℤ) :
    fiveTermWordKernelResidue bs (u₁ + 1) v₁ (fiveTermLatticeArgument (letterWord bs) τ u₁ u₂)
        (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂) τ m
        (fiveTermLatticeArgument (letterWord bs) τ m k) =
      fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ) /
          (2 * Real.pi * I * (1 - fltDenominator (letterWord bs : Mat(2, ℤ)) (τ : ℂ))) *
        fixedBicharacter (letterWord bs) (finiteDilogOrder (letterWord bs))
          (fiveTermCharacteristicResidue (letterWord bs) m k)
          (fiveTermCharacteristicResidue (letterWord bs) u₁ u₂) *
        ((if 0 ≤ fiveTermLatticeIndex (letterWord bs) m k then
            finiteDilogE (letterWord bs) τ (fiveTermCharacteristicResidue (letterWord bs) m k)
          else finiteDilogEMinus (letterWord bs) τ
            (fiveTermCharacteristicResidue (letterWord bs) m k)) /
          (if 0 ≤ fiveTermLatticeIndex (letterWord bs) (m + v₁) (k + v₂) then
            finiteDilogE (letterWord bs) τ
              (fiveTermCharacteristicResidue (letterWord bs) (m + v₁) (k + v₂))
          else finiteDilogEMinus (letterWord bs) τ
            (fiveTermCharacteristicResidue (letterWord bs) (m + v₁) (k + v₂)))) := by
  have hadd : (fiveTermLatticeArgument (letterWord bs) τ m k : ℂ) +
      (fiveTermLatticeArgument (letterWord bs) τ v₁ v₂ : ℂ) =
      (fiveTermLatticeArgument (letterWord bs) τ (m + v₁) (k + v₂) : ℂ) := by
    exact_mod_cast (fiveTermLatticeArgument_add (letterWord bs) τ m k v₁ v₂).symm
  have hnum := etaMultiplier_mul_faddeevWordContinued_latticeArgument h m k
  have hden := etaMultiplier_mul_faddeevWordContinued_latticeArgument h
    (m + v₁) (k + v₂)
  have hq : faddeevWordContinued bs m 0
        (fiveTermLatticeArgument (letterWord bs) τ m k) τ /
      faddeevWordContinued bs (m + v₁) 0
        (fiveTermLatticeArgument (letterWord bs) τ (m + v₁) (k + v₂)) τ =
      (if 0 ≤ fiveTermLatticeIndex (letterWord bs) m k then
          finiteDilogE (letterWord bs) τ
            (fiveTermCharacteristicResidue (letterWord bs) m k)
        else finiteDilogEMinus (letterWord bs) τ
          (fiveTermCharacteristicResidue (letterWord bs) m k)) /
      (if 0 ≤ fiveTermLatticeIndex (letterWord bs) (m + v₁) (k + v₂) then
          finiteDilogE (letterWord bs) τ
            (fiveTermCharacteristicResidue (letterWord bs) (m + v₁) (k + v₂))
        else finiteDilogEMinus (letterWord bs) τ
          (fiveTermCharacteristicResidue (letterWord bs) (m + v₁) (k + v₂))) := by
    calc
      _ = (etaMultiplier (letterWord bs) * _ : ℂ) /
          (etaMultiplier (letterWord bs) * _) :=
        (mul_div_mul_left _ _ (etaMultiplier_ne_zero (letterWord bs))).symm
      _ = _ := by rw [hnum, hden]
  unfold fiveTermWordKernelResidue
  rw [hadd, fiveTermResiduePhase_eq_bicharacter h.fixedPoint m k u₁ u₂, hq]

end SIC

end
