/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.Faddeev.WordShift

/-!
# The reflection exponent of the Faddeev word product

The exponent `Q_{γ,m,n}` of the reflection law of the word product, and the phase identities that
pair reflected generator factors along a word into `(-1)^{m+n}e(Q_{γ,m,n}(z,τ))κ_γ`, with the
source multiplier `κ_γ = μ_γ⁻²` expanded in the word letters.

This module follows [RW26, Radchenko, Wheeler (2026), Proposition 1, `prop:reflection`] for the
word product of Proposition 2(ii), `prop:prod.id.mod,fad`, equation (20),
`eq:modulartofaddeevCF`, at `γ=∏_{j=1}^r T^{b_j}S=(a b; c d)`. Put `e(x)=exp(2πix)` and
`B₂(x)=x²-x+1/6`. The phase identities are consumed by the lower-sector estimate of
`SICs.SpecialFunctions.Faddeev.WordAsymptotics`.

## The argument

Choose every intermediate index of `Φ_{γ,m+1,n+1}(z)` equal to `1` and every intermediate index
of `Φ_{γ,-m,-n}(-z)` equal to `0`. Then the `j`-th factors are `Φ(x_j+τ_j-1;τ_j)` and
`Φ(-x_j;τ_j)` with `x_j=z_j+μ_jτ_j-μ_{j-1}`, `μ=(n,0,…,0,m)`, and the generator reflection
`faddeevS_mul_neg` gives
`exp(-πi(x_j²/τ_j+(1-τ_j⁻¹)x_j+(τ_j+τ_j⁻¹)/6-1/2))` for each pair.
Peeling one letter at a time, `reflectionSingleton_phase` treats a one-letter word and
`reflectionCons_phase` a first letter followed by the remaining word with indices `(m,0)`.

The exponents sum to `Q_{γ,m,n}(z,τ)` up to integers and a constant. Since
`τ_{j-1}=b_j-1/τ_j` with `τ_r=τ` and `τ_0=γ·τ`, the sum `Σ_j(τ_j+τ_j⁻¹)` telescopes to
`Σ_jb_j+τ-γ·τ`; the terms `τ/6-γ·τ/6` are the constants of `B₂(m+1)τ-B₂(n+1)γ·τ`, and the rest
is `κ_γ=exp(-πi(Σ_jb_j-3r)/6)`. The integer parts give the sign `(-1)^{m+n}`.

This constant is the word expansion of `μ_γ⁻²` in Proposition 1. At `γ=S` it is the
factor `i` of equation (13), `eq:PhiS.reflection`. The polynomial `Q` is the one in the source.
-/

noncomputable section

open ModularGroup
open scoped MatrixGroups

namespace SIC

/-! ### The quadratic exponent -/

/-- The polynomial `Q_{γ,m,n}(z,τ)` of [RW26, Radchenko, Wheeler (2026), Proposition 1,
`prop:reflection`]:
`-½[cz²/(cτ+d)+(2m+1-(2n+1)/(cτ+d))z+B₂(m+1)τ-B₂(n+1)(aτ+b)/(cτ+d)]` for `γ=(a b; c d)`,
with `B₂(m+1)=m²+m+1/6`. -/
def faddeevReflectionExponent (γ : SL(2, ℤ)) (m n : ℤ) (z τ : ℂ) : ℂ :=
  -(1 / 2 : ℂ) *
    ((γ 1 0 : ℂ) * z ^ 2 / fltDenominator (γ : Mat(2, ℤ)) τ +
      (2 * (m : ℂ) + 1 - (2 * (n : ℂ) + 1) / fltDenominator (γ : Mat(2, ℤ)) τ) * z +
      ((m : ℂ) ^ 2 + m + 1 / 6) * τ - ((n : ℂ) ^ 2 + n + 1 / 6) * flt (γ : Mat(2, ℤ)) τ)

/-! ### Phases of paired factors

The exponents of the paired factors are compared with `Q` letter by letter; their integer
differences give the sign. -/

/-- The quadratic bracket (2Q) in matrix coordinates, used to compare successive word
factors. -/
private def reflectionQuadratic (A B C D m n z τ : ℂ) : ℂ :=
  -(C * z ^ 2 / (C * τ + D) +
      (2 * m + 1 - (2 * n + 1) / (C * τ + D)) * z +
      (m ^ 2 + m + 1 / 6) * τ -
      (n ^ 2 + n + 1 / 6) * ((A * τ + B) / (C * τ + D)))

/-- The bracket in the generator reflection exponent, used by the phase identities below and
the lower word asymptotic estimate. -/
def reflectionPairBracket (x τ : ℂ) : ℂ :=
  -(x ^ 2 / τ + (1 - τ⁻¹) * x + (τ + τ⁻¹) / 6 - 1 / 2)

/-- The one-letter exponent comparison, used by `reflectionExponent_singleton`. -/
private theorem reflectionSingletonAlgebra (a m n z τ : ℂ) (hτ : τ ≠ 0) :
    reflectionPairBracket (z + m * τ - n) τ + (a - 3) / 6 =
      reflectionQuadratic a (-1) 1 0 m n z τ +
        (2 * m * n + m + n - a * n * (n + 1)) := by
  unfold reflectionPairBracket reflectionQuadratic
  field_simp [hτ]
  ring_nf

/-- The determinant-one exponent recursion, used by `reflectionExponent_cons`. -/
private theorem reflectionConsAlgebra (a A B C D m n z τ : ℂ)
    (hdet : A * D - B * C = 1) (hj : C * τ + D ≠ 0) (hu : A * τ + B ≠ 0) :
    reflectionPairBracket (z / (C * τ + D) - n) ((A * τ + B) / (C * τ + D)) +
      reflectionQuadratic A B C D m 0 z τ + (a - 3) / 6 =
      reflectionQuadratic (a * A - C) (a * B - D) A B m n z τ +
        (n - a * n * (n + 1)) := by
  unfold reflectionPairBracket reflectionQuadratic
  have hu' : τ * A + B ≠ 0 := by simpa only [mul_comm] using hu
  field_simp [hj, hu, hu']
  linear_combination 12 * z ^ 2 * hdet

/-- The coordinate bracket equals twice `faddeevReflectionExponent`; used by
`reflectionExponent_cons` and `reflectionExponent_singleton`. -/
private theorem reflectionExponent_eq_quadratic (M : SL(2, ℤ)) (m n : ℤ) (z τ : ℂ) :
    2 * faddeevReflectionExponent M m n z τ =
      reflectionQuadratic (M 0 0) (M 0 1) (M 1 0) (M 1 1) m n z τ := by
  unfold faddeevReflectionExponent reflectionQuadratic fltDenominator flt
  ring_nf

/-- The first letter changes the four matrix entries as required by
`reflectionExponent_cons`. -/
private theorem reflectionQuadratic_head (a : ℤ) (w : List ℤ) (m n : ℤ) (z τ : ℂ) :
    reflectionQuadratic (letterWord (a :: w) 0 0) (letterWord (a :: w) 0 1)
      (letterWord (a :: w) 1 0) (letterWord (a :: w) 1 1) m n z τ =
    reflectionQuadratic ((a : ℂ) * letterWord w 0 0 - letterWord w 1 0)
      ((a : ℂ) * letterWord w 0 1 - letterWord w 1 1)
      (letterWord w 0 0) (letterWord w 0 1) m n z τ := by
  rw [letterWord_cons_apply_zero, letterWord_cons_apply_zero,
    letterWord_cons_apply_one, letterWord_cons_apply_one]
  push_cast
  rfl

/-- The reflection exponent recursion along `T^aS`, used by
`reflectionCons_phase`. -/
private theorem reflectionExponent_cons (a : ℤ) (w : List ℤ) (m n : ℤ) (z τ : ℂ)
    (hj : fltDenominator (letterWord w : Mat(2, ℤ)) τ ≠ 0)
    (hσ : flt (letterWord w : Mat(2, ℤ)) τ ≠ 0) :
    reflectionPairBracket
        (z / fltDenominator (letterWord w : Mat(2, ℤ)) τ - n)
        (flt (letterWord w : Mat(2, ℤ)) τ) +
      2 * faddeevReflectionExponent (letterWord w) m 0 z τ + ((a : ℂ) - 3) / 6 =
      2 * faddeevReflectionExponent (letterWord (a :: w)) m n z τ +
        ((n : ℂ) - (a : ℂ) * n * (n + 1)) := by
  let W := letterWord w
  have hdetI : W 0 0 * W 1 1 - W 0 1 * W 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using Matrix.SpecialLinearGroup.det_coe W
  have hdet : (W 0 0 : ℂ) * W 1 1 - W 0 1 * W 1 0 = 1 := by
    exact_mod_cast hdetI
  have hu : (W 0 0 : ℂ) * τ + W 0 1 ≠ 0 := by
    intro h
    apply hσ
    change flt (W : Mat(2, ℤ)) τ = 0
    simp only [flt, h, zero_div]
  have h := reflectionConsAlgebra (a : ℂ) (W 0 0 : ℂ) (W 0 1 : ℂ) (W 1 0 : ℂ)
    (W 1 1 : ℂ) m n z τ hdet hj hu
  rw [reflectionExponent_eq_quadratic, reflectionExponent_eq_quadratic,
    reflectionQuadratic_head]
  simpa only [flt, fltDenominator, Int.cast_zero] using h

/-- The one-letter exponent comparison in terms of `faddeevReflectionExponent`, used by
`reflectionSingleton_phase`. -/
private theorem reflectionExponent_singleton (a m n : ℤ) (z τ : ℂ) (hτ : τ ≠ 0) :
    reflectionPairBracket (z + m * τ - n) τ + ((a : ℂ) - 3) / 6 =
      2 * faddeevReflectionExponent (letterWord [a]) m n z τ +
        (2 * (m : ℂ) * n + m + n - (a : ℂ) * n * (n + 1)) := by
  have h := reflectionSingletonAlgebra (a : ℂ) m n z τ hτ
  rw [letterWord_singleton, reflectionExponent_eq_quadratic]
  rw [coe_T_zpow_mul_S]
  simpa using h

/-- Integer multiples of `πi` give the sign used by
`reflectionExp_phase`. -/
private theorem reflectionExp_int (k : ℤ) :
    Complex.exp ((k : ℂ) * ((Real.pi : ℂ) * Complex.I)) = (-1 : ℂ) ^ k := by
  rw [Complex.exp_int_mul, Complex.exp_pi_mul_I]

/-- The one-letter integral phase has parity `m+n`; used by
`reflectionSingleton_phase`. -/
private theorem reflectionSingleton_sign (a m n : ℤ) :
    (-1 : ℂ) ^ (2 * m * n + m + n - a * n * (n + 1)) =
      (-1 : ℂ) ^ (m + n) := by
  have he : Even (2 * m * n - a * n * (n + 1)) := by
    convert (even_two_mul (m * n)).sub ((Int.even_mul_succ_self n).mul_left a) using 1;
      ring_nf
  have hk : 2 * m * n + m + n - a * n * (n + 1) =
      (m + n) + (2 * m * n - a * n * (n + 1)) := by ring_nf
  rw [hk, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), he.neg_one_zpow, mul_one]

/-- The new integral phase at a peeled letter has parity `n`; used by
`reflectionCons_phase`. -/
private theorem reflectionCons_sign (a n : ℤ) :
    (-1 : ℂ) ^ (n - a * n * (n + 1)) = (-1 : ℂ) ^ n := by
  have he : Even (-(a * n * (n + 1))) := by
    convert ((Int.even_mul_succ_self n).mul_left a).neg using 1; ring_nf
  have hk : n - a * n * (n + 1) = n + -(a * n * (n + 1)) := by ring_nf
  rw [hk, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), he.neg_one_zpow, mul_one]

/-- The exponential phase bookkeeping used by `reflectionSingleton_phase` and
`reflectionCons_phase`. -/
private theorem reflectionExp_phase (u v w c d : ℂ) (k : ℤ)
    (h : u + v + c = w + (k : ℂ)) :
    Complex.exp ((Real.pi : ℂ) * Complex.I * u) *
        Complex.exp ((Real.pi : ℂ) * Complex.I * v) *
        Complex.exp (-(Real.pi : ℂ) * Complex.I * d) =
      (-1 : ℂ) ^ k * Complex.exp ((Real.pi : ℂ) * Complex.I * w) *
        Complex.exp (-(Real.pi : ℂ) * Complex.I * (c + d)) := by
  calc
    _ = Complex.exp ((Real.pi : ℂ) * Complex.I * (u + v - d)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      ring_nf
    _ = Complex.exp ((k : ℂ) * ((Real.pi : ℂ) * Complex.I)) *
          Complex.exp ((Real.pi : ℂ) * Complex.I * w) *
          Complex.exp (-(Real.pi : ℂ) * Complex.I * (c + d)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      linear_combination ((Real.pi : ℂ) * Complex.I) * h
    _ = _ := by rw [reflectionExp_int]

/-- The one-letter phase: the reflected generator exponential of `T^aS` is
`(-1)^{m+n}e(Q_{T^aS,m,n}(z,τ))` times its constant phase. Used by the lower word asymptotic
estimate. -/
theorem reflectionSingleton_phase (a m n : ℤ) (z τ : ℂ) (hτ : τ ≠ 0) :
    Complex.exp ((Real.pi : ℂ) * Complex.I *
        reflectionPairBracket (z + m * τ - n) τ) =
      (-1 : ℂ) ^ (m + n) *
        Complex.exp (2 * Real.pi * Complex.I *
          faddeevReflectionExponent (letterWord [a]) m n z τ) *
        Complex.exp (-(Real.pi : ℂ) * Complex.I * ((a : ℂ) - 3) / 6) := by
  let k : ℤ := 2 * m * n + m + n - a * n * (n + 1)
  have h : reflectionPairBracket (z + m * τ - n) τ + 0 + ((a : ℂ) - 3) / 6 =
      2 * faddeevReflectionExponent (letterWord [a]) m n z τ + (k : ℂ) := by
    convert reflectionExponent_singleton a m n z τ hτ using 1 <;>
      simp only [add_zero, k, Int.cast_add, Int.cast_sub, Int.cast_mul]
    ring_nf
  have hp := reflectionExp_phase
    (reflectionPairBracket (z + m * τ - n) τ) 0
    (2 * faddeevReflectionExponent (letterWord [a]) m n z τ)
    (((a : ℂ) - 3) / 6) 0 k h
  simp only [mul_zero, Complex.exp_zero, mul_one, add_zero] at hp
  rw [reflectionSingleton_sign a m n] at hp
  convert hp using 1; ring_nf

/-- The constant phase splits into the first letter and the remaining word, as used by
`reflectionCons_phase`. -/
private theorem reflectionConstant_cons (a : ℤ) (w : List ℤ) :
    ((((a :: w).sum : ℤ) : ℂ) - 3 * (a :: w).length) / 6 =
      ((a : ℂ) - 3) / 6 + (((w.sum : ℤ) : ℂ) - 3 * w.length) / 6 := by
  simp only [List.sum_cons, List.length_cons, Int.cast_add, Nat.cast_add, Nat.cast_one]
  ring_nf

/-- The reflection asymptote `e(Q_{γ,m,n}(z,τ))κ_γ` of a word, without its sign; used by the
lower word asymptotic estimate. -/
def reflectionWordKernel (w : List ℤ) (m n : ℤ) (z τ : ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I *
      faddeevReflectionExponent (letterWord w) m n z τ) *
    Complex.exp (-(Real.pi : ℂ) * Complex.I *
      (((w.sum : ℤ) : ℂ) - 3 * w.length) / 6)

/-- The reflected exponential of the first factor of a nonempty suffix, used by the lower word
asymptotic estimate. -/
def reflectionFirstPair (w : List ℤ) (n : ℤ) (z τ : ℂ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I *
    reflectionPairBracket
      (z / fltDenominator (letterWord w : Mat(2, ℤ)) τ - n)
      (flt (letterWord w : Mat(2, ℤ)) τ))

/-- The phase of a peeled letter and its tail, used by the lower word asymptotic estimate. -/
theorem reflectionCons_phase (a : ℤ) (w : List ℤ) (m n : ℤ) (z τ : ℂ)
    (hj : fltDenominator (letterWord w : Mat(2, ℤ)) τ ≠ 0)
    (hσ : flt (letterWord w : Mat(2, ℤ)) τ ≠ 0) :
    reflectionFirstPair w n z τ * reflectionWordKernel w m 0 z τ =
      (-1 : ℂ) ^ n * reflectionWordKernel (a :: w) m n z τ := by
  unfold reflectionFirstPair reflectionWordKernel
  let k : ℤ := n - a * n * (n + 1)
  have h : reflectionPairBracket
        (z / fltDenominator (letterWord w : Mat(2, ℤ)) τ - n)
        (flt (letterWord w : Mat(2, ℤ)) τ) +
      2 * faddeevReflectionExponent (letterWord w) m 0 z τ +
      ((a : ℂ) - 3) / 6 =
      2 * faddeevReflectionExponent (letterWord (a :: w)) m n z τ + (k : ℂ) := by
    convert reflectionExponent_cons a w m n z τ hj hσ using 1;
      simp only [k, Int.cast_sub, Int.cast_mul, Int.cast_add, Int.cast_one]
  have hp := reflectionExp_phase
    (reflectionPairBracket
      (z / fltDenominator (letterWord w : Mat(2, ℤ)) τ - n)
      (flt (letterWord w : Mat(2, ℤ)) τ))
    (2 * faddeevReflectionExponent (letterWord w) m 0 z τ)
    (2 * faddeevReflectionExponent (letterWord (a :: w)) m n z τ)
    (((a : ℂ) - 3) / 6)
    ((((w.sum : ℤ) : ℂ) - 3 * w.length) / 6) k h
  simp only [k, reflectionCons_sign a n] at hp
  rw [← reflectionConstant_cons a w] at hp
  convert hp using 1 <;> ring_nf

end SIC
