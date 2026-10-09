/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SL2Z.Basic
import SICs.Analysis.Irrational
import SICs.Source
import Mathlib.Analysis.Complex.Basic

/-!
# Fractional-linear actions and Jacobi denominators

The Möbius action `M·τ`, its Jacobi denominator `j_M(τ)`, continuity, composition, fixed-point
transport, and real signs.

Following [AFK25, equation (1.20), `eq:fractionalineartransform`], the total expression
`M·τ = (aτ+b)/(cτ+d)` is defined over any division ring. Ring homomorphisms commute with it.
A nonsingular integer matrix preserves irrationality and has nonzero denominator at every
irrational real point. Inversion and composition hold wherever their denominators are nonzero.
The inverse identities also identify the lattices `ℤ + ℤτ` and `j_M(τ)(ℤ + ℤ(M·τ))`.
The denominator is affine in a complex modulus, so both expressions are continuous away
from the pole. The composition laws transport fixed points and their Jacobi denominators
under conjugation, as in [72, Kopp (2024), Lemma 4.10, `lem:jeval`].

At a fixed point the Jacobi denominator is an eigenvalue, so its integer powers describe those
of the matrix, and `j_M(τ) + j_M(τ)⁻¹ = Tr M`. Positivity therefore forces positive trace.
The upper-half-plane formulas and the translations ending a real word walk supply the domain
and recursion arguments of the Shintani--Faddeev cocycle.
-/

open ModularGroup
open scoped MatrixGroups

namespace SIC

/-! ### Fractional linear transformations

The Möbius expression and its Jacobi denominator are defined on integer matrices, at a point `τ`
of an arbitrary division ring `K`. One definition serves every reading the project needs: `K = ℂ`
for the upper-half-plane cocycle; `K = ℝ` for the product along a word of generators
(the Hirzebruch--Jung word of `SICs.SL2Z.Words`) at a real quadratic argument, with every
intermediate point in `ℝ`; and `K` a number field for the
lattice arithmetic of `SICs.Quadratic.LatticeUnits`. Ring homomorphisms `K →+* L` commute with
both expressions (`map_flt`, `map_fltDenominator`), which is how the readings are compared; the
cast `ℝ → ℂ` is the case recorded for `norm_cast` as `ofReal_flt`, `ofReal_fltDenominator`.

At an irrational real argument the expressions are well behaved: a rational linear relation in
`τ` forces both of its coefficients to vanish (`ratCast_eq_zero_of_irrational_mul`), so neither
row of a determinant-one matrix can vanish at `τ`, and irrationality propagates through the
action. -/

section DivisionRing

variable {K L : Type*} [DivisionRing K] [DivisionRing L]

/-- The fractional linear expression `M · τ = (ατ + β) / (γτ + δ)` for
    `M = [[α, β], [γ, δ]]` and `τ` in a division ring `K`. This agrees with the fractional
    linear transformation for `M ∈ GL₂(ℤ)` wherever `γτ + δ ≠ 0`; Lean's division makes the
    displayed expression total at the pole as well. See [AFK25, equation (1.20),
    `eq:fractionalineartransform`]. -/
def flt (M : Mat(2, ℤ)) (τ : K) : K :=
  ((M 0 0 : K) * τ + (M 0 1 : K)) / ((M 1 0 : K) * τ + (M 1 1 : K))

/-- The denominator `j_M(τ) = γτ + δ` of the fractional linear expression, for `τ` in a
    division ring `K`. See [AFK25, equation (1.20), `eq:fractionalineartransform`]. -/
def fltDenominator (M : Mat(2, ℤ)) (τ : K) : K :=
  (M 1 0 : K) * τ + (M 1 1 : K)

/-- **A ring homomorphism commutes with the Jacobi denominator**: `f(j_M(τ)) = j_M(f(τ))`,
since `f` fixes `ℤ` (`map_intCast`). -/
theorem map_fltDenominator (f : K →+* L) (M : Mat(2, ℤ)) (τ : K) :
    f (fltDenominator M τ) = fltDenominator M (f τ) := by
  simp [fltDenominator]

/-- **A ring homomorphism commutes with the fractional linear expression**: `f(M·τ) = M·f(τ)`,
with `map_div₀` (both sides read `x/0 = 0`, so no nonvanishing hypothesis is needed). -/
theorem map_flt (f : K →+* L) (M : Mat(2, ℤ)) (τ : K) :
    f (flt M τ) = flt M (f τ) := by
  simp [flt]

/-- The Möbius action of an upper-triangular matrix `U = [[a,b],[0,d]]` is affine:
`U·x = (ax + b)/d`. -/
theorem flt_upperTriangular (a b d : ℤ) (x : K) :
    flt !![a, b; 0, d] x = ((a : K) * x + b) / d := by
  simp [flt]

/-- The Jacobi denominator of an upper-triangular matrix `U = [[a,b],[0,d]]` is the constant
`j_U(x) = d`. -/
theorem fltDenominator_upperTriangular (a b d : ℤ) (x : K) :
    fltDenominator !![a, b; 0, d] x = d := by
  simp [fltDenominator]

end DivisionRing

/-- `fltDenominator` commutes with the cast `ℝ → ℂ`: `map_fltDenominator` at `Complex.ofRealHom`,
stated for the cast so that `norm_cast` can use it. -/
@[simp, norm_cast]
lemma ofReal_fltDenominator (M : Mat(2, ℤ)) (τ : ℝ) :
    ((fltDenominator M τ : ℝ) : ℂ) = fltDenominator M (τ : ℂ) :=
  map_fltDenominator Complex.ofRealHom M τ

/-- `flt` commutes with the cast `ℝ → ℂ`: `map_flt` at `Complex.ofRealHom`, stated for the cast
so that `norm_cast` can use it. -/
@[simp, norm_cast]
lemma ofReal_flt (M : Mat(2, ℤ)) (τ : ℝ) :
    ((flt M τ : ℝ) : ℂ) = flt M (τ : ℂ) :=
  map_flt Complex.ofRealHom M τ

/-- **The Jacobi denominator is continuous in its complex argument**: it is affine in `τ`. Used,
with `flt_tendsto` below, to transport a limit of moduli through one factor of a word
(`SICs.Cocycle.Word.UpperHalfPlane`). -/
theorem fltDenominator_tendsto {ι : Type*} {l : Filter ι} (M : Mat(2, ℤ))
    {f : ι → ℂ} {τ : ℂ} (h : Filter.Tendsto f l (nhds τ)) :
    Filter.Tendsto (fun n => fltDenominator M (f n)) l (nhds (fltDenominator M τ)) := by
  unfold fltDenominator
  exact (tendsto_const_nhds.mul h).add tendsto_const_nhds

/-- **The Möbius expression is continuous away from its pole**: a quotient of affine functions,
continuous wherever the Jacobi denominator does not vanish. -/
theorem flt_tendsto {ι : Type*} {l : Filter ι} (M : Mat(2, ℤ))
    {f : ι → ℂ} {τ : ℂ} (h : Filter.Tendsto f l (nhds τ)) (hden : fltDenominator M τ ≠ 0) :
    Filter.Tendsto (fun n => flt M (f n)) l (nhds (flt M τ)) := by
  unfold flt
  exact ((tendsto_const_nhds.mul h).add tendsto_const_nhds).div
    (fltDenominator_tendsto M h) hden

/-- **The Jacobi denominator of a nonsingular integer matrix does not vanish at an irrational
point**: `j_M(τ) = 0` would force `M₁₀ = M₁₁ = 0` (`ratCast_eq_zero_of_irrational_mul`), hence
`det M = 0`. The `SL(2, ℤ)` case is `fltDenominator_ne_zero_of_irrational`. -/
theorem fltDenominator_ne_zero_of_irrational_of_det {τ : ℝ} (hτ : Irrational τ)
    {M : Mat(2, ℤ)} (hM : M.det ≠ 0) : fltDenominator M τ ≠ 0 := by
  intro h
  obtain ⟨hc, hd⟩ := ratCast_eq_zero_of_irrational_mul (a := (M 1 0 : ℚ))
    (b := -(M 1 1 : ℚ)) hτ
    (by unfold fltDenominator at h; push_cast; linarith)
  have hc' : M 1 0 = 0 := by exact_mod_cast hc
  have hd' : M 1 1 = 0 := by
    have : ((M 1 1 : ℤ) : ℚ) = 0 := by linarith [hd]
    exact_mod_cast this
  apply hM
  rw [Matrix.det_fin_two, hc', hd']
  ring

/-- **Irrationality propagates along the action of a nonsingular integer matrix**; the
`SL(2, ℤ)` case is `Irrational.flt`. -/
theorem Irrational.flt_of_det_ne_zero {τ : ℝ} (hτ : Irrational τ)
    {M : Mat(2, ℤ)} (hM : M.det ≠ 0) : Irrational (SIC.flt M τ) := by
  have hden := fltDenominator_ne_zero_of_irrational_of_det hτ hM
  unfold SIC.flt
  rintro ⟨q, hq⟩
  have hden' : (M 1 0 : ℝ) * τ + (M 1 1 : ℝ) ≠ 0 := hden
  rw [eq_div_iff hden'] at hq
  obtain ⟨ha, hb⟩ := ratCast_eq_zero_of_irrational_mul
    (a := (M 0 0 : ℚ) - q * (M 1 0 : ℚ))
    (b := q * (M 1 1 : ℚ) - (M 0 1 : ℚ)) hτ (by push_cast; linear_combination -hq)
  apply hM
  have hzero : ((M.det : ℤ) : ℚ) = 0 := by
    rw [Matrix.det_fin_two]
    push_cast
    linear_combination (M 1 1 : ℚ) * ha + (M 1 0 : ℚ) * hb
  exact_mod_cast hzero

/-- A determinant-one integer matrix has nonzero Jacobi denominator at an irrational point;
the determinant-one case of `fltDenominator_ne_zero_of_irrational_of_det`. -/
theorem fltDenominator_ne_zero_of_irrational {τ : ℝ} (hτ : Irrational τ)
    (M : SL(2, ℤ)) : fltDenominator (M : Mat(2, ℤ)) τ ≠ 0 :=
  fltDenominator_ne_zero_of_irrational_of_det hτ (by simp [M.2])

/-- A determinant-one integer matrix preserves irrationality; the determinant-one case of
`Irrational.flt_of_det_ne_zero`. -/
theorem Irrational.flt {τ : ℝ} (hτ : Irrational τ) (M : SL(2, ℤ)) :
    Irrational (SIC.flt (M : Mat(2, ℤ)) τ) :=
  Irrational.flt_of_det_ne_zero hτ (by simp [M.2])

/-! ### Inverse fractional-linear action

From here to the end of the Möbius API, `K` is a field: the identities are proved by clearing
denominators, which needs commutativity. The inverse identities transport the integer period
lattice between `τ` and its image. -/

section Field

variable {K : Type*} [Field K]

/-- `M⁻¹` undoes `M`'s fractional linear action: `M⁻¹ · (M · τ) = τ`. -/
lemma flt_inv_flt (M : SL(2, ℤ)) (τ : K)
    (hτ : fltDenominator (M : Mat(2, ℤ)) τ ≠ 0) :
    flt ((M⁻¹ : SL(2, ℤ)) : Mat(2, ℤ))
        (flt (M : Mat(2, ℤ)) τ) = τ := by
  have hdet' : (M.1 0 0 : K) * M.1 1 1 - M.1 0 1 * M.1 1 0 = 1 :=
    det_fin_two_cast_eq_one M
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl M]
  simp only [flt, fltDenominator] at hτ ⊢
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hτ2 : τ * (M.1 1 0 : K) + (M.1 1 1 : K) ≠ 0 := by rw [mul_comm]; exact hτ
  field_simp [hτ2]
  refine (div_eq_iff ?_).mpr ?_
  · push_cast
    have hone : (M.1 0 0 : K) * τ * (-M.1 1 0) + M.1 0 1 * (-M.1 1 0) +
        M.1 0 0 * (τ * M.1 1 0 + M.1 1 1) = 1 := by linear_combination hdet'
    rw [show (M.1 0 0 : K) * τ * (-M.1 1 0) + M.1 0 1 * (-M.1 1 0) +
        M.1 0 0 * (τ * M.1 1 0 + M.1 1 1) = (M.1 0 0 * τ + M.1 0 1) * (-M.1 1 0) +
        M.1 0 0 * (τ * M.1 1 0 + M.1 1 1) from by ring] at hone
    rw [hone]
    norm_num
  · push_cast
    ring

/-- **A fixed point of `M` is a fixed point of `M⁻¹`**: `flt_inv_flt` specialized to `M·τ = τ`.
The inverse-matrix cocycle `sfModularCocycleRealInv` uses the value at `M` evaluated at
`M⁻¹·τ`; at a fixed point this argument is `τ` itself. -/
lemma flt_inv_of_flt_eq_self {M : SL(2, ℤ)} {τ : K}
    (hτ : fltDenominator (M : Mat(2, ℤ)) τ ≠ 0)
    (hfix : flt (M : Mat(2, ℤ)) τ = τ) :
    flt ((M⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) τ = τ := by
  have h := flt_inv_flt M τ hτ
  rwa [hfix] at h

/-! ### General Möbius composition laws

Numerators and denominators are tracked separately under matrix multiplication. Once the
intermediate denominator is nonzero, these identities recover composition of the Möbius
action. Comparing both sides of `A′R = RA` then shows that `R` transports a fixed
point of `A` to one of `A′` without changing its Jacobi denominator. -/

/-- **The Jacobi-denominator cocycle law**: `j_{AB}(τ) = j_A(B·τ)·j_B(τ)`, for arbitrary integer
matrices `A, B` (no determinant hypothesis needed). Only `B`'s own denominator at `τ` needs to be
nonzero: unfolding both sides and clearing that one denominator gives a literal polynomial
identity, so no case split on `A`'s resulting denominator is needed. -/
theorem fltDenominator_mul (A B : Mat(2, ℤ)) (τ : K)
    (hB : fltDenominator B τ ≠ 0) :
    fltDenominator (A * B) τ = fltDenominator A (flt B τ) * fltDenominator B τ := by
  unfold fltDenominator flt at *
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  field_simp
  ring

/-- **The Möbius composition law**: `(AB)·τ = A·(B·τ)`, for arbitrary integer matrices `A, B`.
Only `B`'s denominator at `τ` needs to be nonzero; the resulting outer denominator
may vanish, since the same factor is used on both sides. -/
theorem flt_mul (A B : Mat(2, ℤ)) (τ : K) (hB : fltDenominator B τ ≠ 0) :
    flt (A * B) τ = flt A (flt B τ) := by
  unfold flt fltDenominator at *
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at *
  push_cast at *
  field_simp
  ring

/-- **The Jacobi denominator of a conjugate at the transported fixed point**,
[72, Kopp (2024), Lemma 4.10, `lem:jeval`]: if `A'R = RA`, `A·β = β` and `j_R(β) ≠ 0`, then
`j_{A'}(R·β) = j_A(β)`, for `j_A(β) ≠ 0`. From the cocycle law `fltDenominator_mul` on both
sides of `A'R = RA`: `j_{A'}(R·β) j_R(β) = j_R(A·β) j_A(β) = j_R(β) j_A(β)`. -/
@[source "72, Lemma 4.10, p. 34, lem:jeval"]
theorem fltDenominator_of_mul_eq_of_flt_eq_self {A A' R : Mat(2, ℤ)}
    (hconj : A' * R = R * A) {β : ℝ} (hjR : fltDenominator R β ≠ 0)
    (hjA : fltDenominator A β ≠ 0) (hfix : flt A β = β) :
    fltDenominator A' (flt R β) = fltDenominator A β := by
  have h1 := fltDenominator_mul A' R β hjR
  have h2 := fltDenominator_mul R A β hjA
  rw [hfix] at h2
  rw [hconj, h2, mul_comm] at h1
  exact mul_right_cancel₀ hjR h1.symm

/-- **A conjugate fixes the transported fixed point**: if `A'R = RA`, `A·β = β`, `j_A(β) ≠ 0`
and `j_R(β) ≠ 0`, then `A'·(R·β) = R·β`, from the composition law `flt_mul` on both sides. -/
theorem flt_of_mul_eq_of_flt_eq_self {A A' R : Mat(2, ℤ)}
    (hconj : A' * R = R * A) {β : ℝ} (hjR : fltDenominator R β ≠ 0)
    (hjA : fltDenominator A β ≠ 0) (hfix : flt A β = β) :
    flt A' (flt R β) = flt R β := by
  rw [← flt_mul A' R β hjR, hconj,
    flt_mul R A β hjA, hfix]

/-- The automorphy factor picked up by `M⁻¹` at the point `M` sends `τ` to is the reciprocal of the
one `M` picks up at `τ`: the case `M₁ = M⁻¹, M₂ = M` of `j_{M₁M₂}(τ) = j_{M₁}(M₂·τ)·j_{M₂}(τ)`,
using `j_I ≡ 1`. -/
lemma fltDenominator_inv_flt (M : SL(2, ℤ)) (τ : K)
    (hτ : fltDenominator (M : Mat(2, ℤ)) τ ≠ 0) :
    fltDenominator ((M⁻¹ : SL(2, ℤ)) : Mat(2, ℤ))
        (flt (M : Mat(2, ℤ)) τ) *
      fltDenominator (M : Mat(2, ℤ)) τ = 1 := by
  have h := fltDenominator_mul
    ((M⁻¹ : SL(2, ℤ)) : Mat(2, ℤ))
    (M : Mat(2, ℤ)) τ hτ
  rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one] at h
  simpa [fltDenominator] using h.symm

/-- For `M = (a b; c d) ∈ SL₂(ℤ)`, `1/j_M(τ) = a - c·(M·τ)`: the Jacobi denominator of `M⁻¹` at
`M·τ`, by `fltDenominator_inv_flt`. -/
theorem inv_fltDenominator_eq (M : SL(2, ℤ)) (τ : K)
    (hτ : fltDenominator (M : Mat(2, ℤ)) τ ≠ 0) :
    (fltDenominator (M : Mat(2, ℤ)) τ)⁻¹ =
      (M 0 0 : K) - (M 1 0 : K) * flt (M : Mat(2, ℤ)) τ := by
  have h := fltDenominator_inv_flt M τ hτ
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl M] at h
  simp only [fltDenominator, Matrix.cons_val_one, Matrix.cons_val_zero] at h
  push_cast at h
  have h' : ((M 0 0 : K) - (M 1 0 : K) * flt (M : Mat(2, ℤ)) τ) *
      fltDenominator (M : Mat(2, ℤ)) τ = 1 := by
    convert h using 1
    simp only [fltDenominator]
    ring
  exact (eq_inv_of_mul_eq_one_left h').symm

/-- For `M = (a b; c d) ∈ SL₂(ℤ)`, `τ/j_M(τ) = d·(M·τ) - b`: the numerator of `M⁻¹` at `M·τ`, by
`flt_inv_flt`. With `inv_fltDenominator_eq`, it shows `j_M(τ)(ℤ + ℤ(M·τ)) = ℤ + ℤτ`. -/
theorem div_fltDenominator_eq (M : SL(2, ℤ)) (τ : K)
    (hτ : fltDenominator (M : Mat(2, ℤ)) τ ≠ 0) :
    τ / fltDenominator (M : Mat(2, ℤ)) τ =
      (M 1 1 : K) * flt (M : Mat(2, ℤ)) τ - (M 0 1 : K) := by
  have hdet : (M.1 0 0 : K) * M.1 1 1 - M.1 0 1 * M.1 1 0 = 1 :=
    det_fin_two_cast_eq_one M
  simp only [flt, fltDenominator] at hτ ⊢
  apply (div_eq_iff hτ).2
  have hτ' : τ * (M.1 1 0 : K) + (M.1 1 1 : K) ≠ 0 := by
    rw [mul_comm]
    exact hτ
  field_simp [hτ']
  linear_combination -τ * hdet

/-- For `M = (a b; c d) ∈ SL₂(ℤ)`, dividing the lattice point `m + nτ` by `j_M(τ)` gives the
lattice point `(ma - nb) + (nd - mc)(M·τ)`, by `inv_fltDenominator_eq` and
`div_fltDenominator_eq`. -/
theorem intCast_add_intCast_mul_div_fltDenominator (M : SL(2, ℤ)) (τ : K)
    (hτ : fltDenominator (M : Mat(2, ℤ)) τ ≠ 0) (m n : ℤ) :
    ((m : K) + n * τ) / fltDenominator (M : Mat(2, ℤ)) τ =
      ((m * M 0 0 - n * M 0 1 : ℤ) : K) +
        ((n * M 1 1 - m * M 1 0 : ℤ) : K) * flt (M : Mat(2, ℤ)) τ := by
  calc
    _ = (m : K) * (fltDenominator (M : Mat(2, ℤ)) τ)⁻¹ +
          n * (τ / fltDenominator (M : Mat(2, ℤ)) τ) := by ring
    _ = _ := by
      rw [inv_fltDenominator_eq M τ hτ, div_fltDenominator_eq M τ hτ]
      push_cast
      ring

/-- For `M = (a b; c d) ∈ SL₂(ℤ)`, `j_M(τ)(m + n(M·τ)) = (md + nb) + (mc + na)τ`: multiplication by
the Jacobi denominator maps `ℤ + ℤ(M·τ)` into `ℤ + ℤτ`. -/
theorem fltDenominator_mul_intCast_add_intCast_mul (M : SL(2, ℤ)) (τ : K)
    (hτ : fltDenominator (M : Mat(2, ℤ)) τ ≠ 0) (m n : ℤ) :
    fltDenominator (M : Mat(2, ℤ)) τ * ((m : K) + n * flt (M : Mat(2, ℤ)) τ) =
      ((m * M 1 1 + n * M 0 1 : ℤ) : K) + ((m * M 1 0 + n * M 0 0 : ℤ) : K) * τ := by
  have hnum : fltDenominator (M : Mat(2, ℤ)) τ * flt (M : Mat(2, ℤ)) τ =
      (M 0 0 : K) * τ + (M 0 1 : K) := by
    simp only [flt, fltDenominator] at hτ ⊢
    field_simp [hτ]
  calc
    _ = (m : K) * fltDenominator (M : Mat(2, ℤ)) τ +
          n * (fltDenominator (M : Mat(2, ℤ)) τ *
            flt (M : Mat(2, ℤ)) τ) := by ring
    _ = _ := by
      rw [hnum]
      simp only [fltDenominator]
      push_cast
      ring

/-! ### The action on the upper half plane

A determinant-one integral matrix has nonvanishing Jacobi denominator at every nonreal point and
maps the upper half plane to itself. Both facts are what let the upper-half-plane product
quotients of `SICs.Cocycle.UpperHalfPlane` be composed along a word of matrices: every
intermediate modulus stays in `ℍ`, where those products converge. -/

/-- The Jacobi denominator of an integer matrix `M = (a b; c d)` satisfies
`Im j_M(τ) = c Im τ`; see `fltDenominator`. -/
theorem fltDenominator_im (M : Mat(2, ℤ)) (τ : ℂ) :
    (fltDenominator M τ).im = (M 1 0 : ℝ) * τ.im := by
  simp [fltDenominator, Complex.mul_im]

/-- **The imaginary part of a determinant-one Möbius image**: `Im(M·τ) = Im τ / |j_M(τ)|²`.
Direct computation from `Complex.div_im`, using `det M = 1` to collapse the numerator. No
nonvanishing hypothesis is needed: at a zero of `j_M` both sides are `0` under Lean's division
convention. -/
theorem flt_im (M : SL(2, ℤ)) (τ : ℂ) :
    (flt (M : Mat(2, ℤ)) τ).im =
      τ.im / Complex.normSq (fltDenominator (M : Mat(2, ℤ)) τ) := by
  have hdet : (M 0 0 : ℝ) * (M 1 1 : ℝ) - (M 0 1 : ℝ) * (M 1 0 : ℝ) = 1 := by
    have h := M.2
    rw [Matrix.det_fin_two] at h
    exact_mod_cast h
  simp only [flt, fltDenominator] at *
  rw [Complex.div_im, div_sub_div_same]
  congr 1
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.intCast_re, Complex.intCast_im]
  linear_combination τ.im * hdet

/-- **A determinant-one integral matrix has nonvanishing Jacobi denominator off the real line.**
If `j_M(τ) = 0` with `Im τ ≠ 0`, the bottom row of `M` vanishes and `det M = 0`. -/
theorem fltDenominator_ne_zero_of_im_ne_zero (M : SL(2, ℤ)) {τ : ℂ} (hτ : τ.im ≠ 0) :
    fltDenominator (M : Mat(2, ℤ)) τ ≠ 0 := by
  intro h
  have him : (M 1 0 : ℝ) * τ.im = 0 := by
    have := congrArg Complex.im h
    simpa [fltDenominator] using this
  have hc : M 1 0 = 0 := by
    rcases mul_eq_zero.mp him with h' | h'
    · exact_mod_cast h'
    · exact absurd h' hτ
  have hd : M 1 1 = 0 := by
    rw [fltDenominator, hc] at h
    exact_mod_cast (by simpa using h : ((M 1 1 : ℤ) : ℂ) = 0)
  have : (0 : ℤ) = 1 := by rw [← M.2, Matrix.det_fin_two, hc, hd]; ring
  exact absurd this (by decide)

/-- **A determinant-one integral matrix preserves the upper half plane**: the positivity fact that
lets the `ℍ`-convergent `q`-Pochhammer products be evaluated at a transported modulus `M·τ`.
Immediate from `flt_im`, since `|j_M(τ)|² > 0`. -/
theorem flt_im_pos (M : SL(2, ℤ)) {τ : ℂ} (hτ : 0 < τ.im) :
    0 < (flt (M : Mat(2, ℤ)) τ).im := by
  have hne := fltDenominator_ne_zero_of_im_ne_zero M hτ.ne'
  rw [flt_im M]
  exact div_pos hτ (Complex.normSq_pos.mpr hne)

/-! ### Iterating a matrix that fixes `τ`

At a real fixed point of `M` the Möbius composition laws above collapse: `M^k` fixes `τ` too, and
its Jacobi denominator is the `k`-th power of `M`'s. This is what turns [AFK25, Definition 1.28,
`dfn:AssociatedStabilizers`]'s power relation `A_t = L_{z,t}^{2m+1}` into a statement about
`j_{A_t}(ρ_t)` without computing a
single entry of `A_t` (`SICs.Admissible.StabilizerDomain`). -/

/-- The identity matrix's Jacobi denominator is `1`. -/
@[simp]
theorem fltDenominator_one (τ : K) :
    fltDenominator (1 : Mat(2, ℤ)) τ = 1 := by
  simp [fltDenominator]

/-- `1·τ = τ`: the identity matrix acts trivially. -/
@[simp]
theorem flt_one (τ : K) : flt (1 : Mat(2, ℤ)) τ = τ := by
  simp [flt]

/-- **The Jacobi denominator of a power, at a fixed point**: `j_{M^k}(τ) = j_M(τ)^k` whenever
`M·τ = τ`. Induction on `k` through `fltDenominator_mul`, whose transported argument
`M·τ` collapses to `τ` at each step. -/
theorem fltDenominator_pow_of_flt_eq_self {M : SL(2, ℤ)} {τ : K}
    (hden : fltDenominator (M : Mat(2, ℤ)) τ ≠ 0)
    (hfix : flt (M : Mat(2, ℤ)) τ = τ) (k : ℕ) :
    fltDenominator ((M ^ k : SL(2, ℤ)) : Mat(2, ℤ)) τ =
      fltDenominator (M : Mat(2, ℤ)) τ ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, fltDenominator_mul _ _ τ hden, hfix,
        ih, pow_succ]

/-- **Every power of `M` fixes what `M` fixes.** The nonvanishing side condition of `flt_mul`
is the assumed nonvanishing at the fixed point. -/
theorem flt_pow_of_flt_eq_self {M : SL(2, ℤ)} {τ : K}
    (hden : fltDenominator (M : Mat(2, ℤ)) τ ≠ 0)
    (hfix : flt (M : Mat(2, ℤ)) τ = τ) (k : ℕ) :
    flt ((M ^ k : SL(2, ℤ)) : Mat(2, ℤ)) τ = τ := by
  induction k with
  | zero => simp [flt]
  | succ n ih =>
      rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, flt_mul _ _ τ hden, hfix, ih]

/-- **A product of matrices fixing `τ` fixes `τ`**, provided the second factor's Jacobi
denominator is nonzero. -/
theorem flt_mul_of_flt_eq_self {M N : Mat(2, ℤ)} {τ : K}
    (hM : flt M τ = τ) (hN : flt N τ = τ) (hNden : fltDenominator N τ ≠ 0) : flt (M * N) τ = τ := by
  rw [flt_mul _ _ τ hNden, hN, hM]

/-- **The Jacobi denominator of a product of matrices fixing `τ` is the product**:
`j_{MN}(τ) = j_M(τ) j_N(τ)`, `fltDenominator_mul` with the transported argument `N·τ`
collapsed to `τ`. -/
theorem fltDenominator_mul_of_flt_eq_self {M N : Mat(2, ℤ)} {τ : K}
    (hN : flt N τ = τ) (hNden : fltDenominator N τ ≠ 0) :
    fltDenominator (M * N) τ = fltDenominator M τ * fltDenominator N τ := by
  rw [fltDenominator_mul _ _ τ hNden, hN]

/-- **At a fixed point, the inverse's Jacobi denominator is the reciprocal**:
`j_{M⁻¹}(τ)·j_M(τ) = 1` whenever `M·τ = τ`. This is `fltDenominator_inv_flt`
at the fixed point. -/
theorem fltDenominator_inv_mul_self_of_flt_eq_self {M : SL(2, ℤ)} {τ : K}
    (hden : fltDenominator (M : Mat(2, ℤ)) τ ≠ 0)
    (hfix : flt (M : Mat(2, ℤ)) τ = τ) :
    fltDenominator ((M⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) τ *
        fltDenominator (M : Mat(2, ℤ)) τ = 1 := by
  simpa only [hfix] using fltDenominator_inv_flt M τ hden

/-- **The Jacobi denominator of an integer power, at a fixed point**: `j_{M^k}(τ) = j_M(τ)^k` for
`k ∈ ℤ` whenever `M·τ = τ`, extending `fltDenominator_pow_of_flt_eq_self` to negative
exponents through `fltDenominator_inv_mul_self_of_flt_eq_self`. -/
theorem fltDenominator_zpow_of_flt_eq_self {M : SL(2, ℤ)} {τ : K}
    (hden : fltDenominator (M : Mat(2, ℤ)) τ ≠ 0)
    (hfix : flt (M : Mat(2, ℤ)) τ = τ) (k : ℤ) :
    fltDenominator ((M ^ k : SL(2, ℤ)) : Mat(2, ℤ)) τ =
      fltDenominator (M : Mat(2, ℤ)) τ ^ k := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rw [zpow_natCast, zpow_natCast]
    exact fltDenominator_pow_of_flt_eq_self hden hfix n
  · have hpowfix := flt_pow_of_flt_eq_self hden hfix n
    have hpowden := fltDenominator_pow_of_flt_eq_self hden hfix n
    have hpowden_ne :
        fltDenominator ((M ^ n : SL(2, ℤ)) : Mat(2, ℤ)) τ ≠ 0 := by
      rw [hpowden]
      exact pow_ne_zero n hden
    have hinv := fltDenominator_inv_mul_self_of_flt_eq_self hpowden_ne hpowfix
    rw [zpow_neg, zpow_natCast]
    change fltDenominator
        (((M ^ n)⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) τ =
      fltDenominator (M : Mat(2, ℤ)) τ ^ (-(n : ℤ))
    rw [zpow_neg, zpow_natCast]
    rw [hpowden] at hinv
    exact eq_inv_of_mul_eq_one_left hinv

/-- **Every integer power of `M` fixes what `M` fixes.** -/
theorem flt_zpow_of_flt_eq_self {M : SL(2, ℤ)} {τ : K}
    (hden : fltDenominator (M : Mat(2, ℤ)) τ ≠ 0)
    (hfix : flt (M : Mat(2, ℤ)) τ = τ) (k : ℤ) :
    flt ((M ^ k : SL(2, ℤ)) : Mat(2, ℤ)) τ = τ := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rw [zpow_natCast]
    exact flt_pow_of_flt_eq_self hden hfix n
  · have hpowfix := flt_pow_of_flt_eq_self hden hfix n
    have hpowden := fltDenominator_pow_of_flt_eq_self hden hfix n
    have hpowden_ne :
        fltDenominator ((M ^ n : SL(2, ℤ)) : Mat(2, ℤ)) τ ≠ 0 := by
      rw [hpowden]
      exact pow_ne_zero n hden
    rw [zpow_neg, zpow_natCast]
    exact flt_inv_of_flt_eq_self hpowden_ne hpowfix

/-! ### Numerator nonvanishing, and the `S`/`T^r` actions

Irrationality rules out a zero numerator for a determinant-one matrix.  Explicit formulas for the
generators `S` and `T^r` then provide the elementary transformations used in each word step. -/

/-- A determinant-one integer matrix sends an irrational point to a nonzero point,
since `Irrational.flt` shows that its image is irrational. -/
theorem flt_ne_zero_of_irrational {τ : ℝ} (hτ : Irrational τ)
    (M : SL(2, ℤ)) : flt (M : Mat(2, ℤ)) τ ≠ 0 :=
  (Irrational.flt hτ M).ne_zero

/-- `T^r`'s Möbius action is the integer shift `x ↦ x + r`, matching `ModularGroup`'s
`coe_T_zpow_smul_eq` for the complex upper half-plane action. -/
theorem flt_T_zpow (r : ℤ) (x : K) :
    flt ((T ^ r : SL(2, ℤ)) : Mat(2, ℤ)) x = x + r := by
  unfold flt
  rw [coe_T_zpow]
  norm_num

/-- `T^r`'s Jacobi denominator is identically `1`. -/
@[simp]
theorem fltDenominator_T_zpow (r : ℤ) (x : K) :
    fltDenominator ((T ^ r : SL(2, ℤ)) : Mat(2, ℤ)) x = 1 := by
  unfold fltDenominator
  rw [coe_T_zpow]
  norm_num

/-- `S`'s Möbius action is `y ↦ -1/y`. -/
theorem flt_S (y : K) : flt ((S : SL(2, ℤ)) : Mat(2, ℤ)) y = -1 / y := by
  unfold flt
  rw [coe_S]
  norm_num

/-- `S`'s Jacobi denominator is the identity, `j_S(y) = y`. -/
theorem fltDenominator_S (y : K) :
    fltDenominator ((S : SL(2, ℤ)) : Mat(2, ℤ)) y = y := by
  unfold fltDenominator
  rw [coe_S]
  norm_num

/-! ### Differences and trace at a real fixed point

Clearing the two Jacobi denominators gives the difference formula. At a fixed point,
the characteristic equation gives `Tr M = j_M(τ) + 1/j_M(τ)`, hence positive trace when
`j_M(τ) > 0`. These elementary identities supply the period and reflection calculations. -/

/-- **The general cross-ratio identity** for `flt`: for any integer matrix `M` and points
`x, τ` with nonzero denominators, `M`'s images of `x` and `τ` differ by `det(M)·(x-τ)` divided by
the product of the two denominators. No fixed-point or `SL₂` hypothesis is needed; this is the
elementary difference formula `M(x)-M(τ) = det(M)(x-τ)/(j_M(x)j_M(τ))`. -/
theorem flt_sub_flt (M : Mat(2, ℤ)) (x τ : K)
    (hx : fltDenominator M x ≠ 0) (hτ : fltDenominator M τ ≠ 0) :
    flt M x - flt M τ =
      (M.det : K) * (x - τ) / (fltDenominator M x * fltDenominator M τ) := by
  unfold flt fltDenominator at *
  rw [div_sub_div _ _ hx hτ, Matrix.det_fin_two]
  push_cast
  congr 1
  ring

/-- For a determinant-one matrix with `c ≠ 0` and `j_M(τ) ≠ 0`,
`a/c - M·τ = 1/(c j_M(τ))`. This elementary identity compares the matrix-row ratio with
the current period in `flt_and_fltDenominator_pos_of_hjStep`. -/
theorem topLeft_div_lowerLeft_sub_flt (M : SL(2, ℤ)) (τ : K)
    (hc : (M 1 0 : K) ≠ 0)
    (hτ : fltDenominator (M : Mat(2, ℤ)) τ ≠ 0) :
    (M 0 0 : K) / (M 1 0 : K) - flt (M : Mat(2, ℤ)) τ =
      1 / ((M 1 0 : K) * fltDenominator (M : Mat(2, ℤ)) τ) := by
  have hdet' : (M 0 0 : K) * (M 1 1 : K) - (M 0 1 : K) * (M 1 0 : K) = 1 :=
    det_fin_two_cast_eq_one M
  unfold flt fltDenominator at *
  field_simp
  linear_combination hdet'

/-- **At a fixed point the Jacobi denominator and its inverse sum to the trace**:
`j_M(τ) + j_M(τ)⁻¹ = Tr M` whenever `M·τ = τ` and `j_M(τ) ≠ 0`. Indeed `(τ,1)` is an eigenvector
of `M` with eigenvalue `j_M(τ)`, and `det M = 1` makes `j_M(τ)⁻¹` the other eigenvalue. -/
lemma fltDenominator_add_inv_of_flt_eq_self {M : SL(2, ℤ)} {τ : K}
    (hfix : flt (M : Mat(2, ℤ)) τ = τ)
    (hj0 : fltDenominator (M : Mat(2, ℤ)) τ ≠ 0) :
    fltDenominator (M : Mat(2, ℤ)) τ +
        (fltDenominator (M : Mat(2, ℤ)) τ)⁻¹ = ((M 0 0 + M 1 1 : ℤ) : K) := by
  have hjval : fltDenominator (M : Mat(2, ℤ)) τ =
      (M 1 0 : K) * τ + (M 1 1 : K) := rfl
  have hnum : (M 0 0 : K) * τ + (M 0 1 : K) =
      τ * fltDenominator (M : Mat(2, ℤ)) τ := by
    have h : ((M 0 0 : K) * τ + (M 0 1 : K)) /
        fltDenominator (M : Mat(2, ℤ)) τ = τ := hfix
    rw [div_eq_iff hj0] at h
    exact h
  have hdet : (M 0 0 : K) * (M 1 1 : K) - (M 0 1 : K) * (M 1 0 : K) = 1 :=
    det_fin_two_cast_eq_one M
  -- `j² - (Tr M)·j + 1 = 0`, the characteristic equation at the eigenvalue `j`.
  have hquad : ((M 0 0 : K) + (M 1 1 : K)) *
      fltDenominator (M : Mat(2, ℤ)) τ =
      fltDenominator (M : Mat(2, ℤ)) τ ^ 2 + 1 := by
    rw [hjval] at hnum ⊢
    linear_combination hdet + (M 1 0 : K) * hnum
  push_cast
  field_simp
  linear_combination -hquad

/-- **At a fixed point in the real domain the trace is positive.** If `M·τ = τ` and
`j_M(τ) > 0` then `Tr M = j_M(τ) + 1/j_M(τ) > 0` (`fltDenominator_add_inv_of_flt_eq_self`). -/
lemma trace_pos_of_flt_eq_self {M : SL(2, ℤ)} {τ : ℝ}
    (hfix : flt (M : Mat(2, ℤ)) τ = τ)
    (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) τ) :
    0 < M 0 0 + M 1 1 := by
  have h := fltDenominator_add_inv_of_flt_eq_self hfix hjac.ne'
  have hpos : (0 : ℝ) < ((M 0 0 + M 1 1 : ℤ) : ℝ) := by
    rw [← h]
    positivity
  exact_mod_cast hpos

/-! ### Translations at the end of a word walk

A matrix with vanishing lower-left entry is `±T^k`; a positive Jacobi denominator at a real point
selects the sign `+`. This is the terminal case of every recursion along the Hirzebruch--Jung
word. -/

/-- **A matrix with vanishing lower-left entry and positive Jacobi denominator is a translation**:
if `M 1 0 = 0` and `0 < j_M(τ)` for `M ∈ SL₂(ℤ)`, then `M 0 0 = M 1 1 = 1`, since `j_M(τ) = M 1 1`
and `M 0 0 · M 1 1 = det M = 1`. -/
theorem diag_eq_one_of_lowerLeft_eq_zero {M : SL(2, ℤ)} {τ : ℝ} (hz : M 1 0 = 0)
    (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) τ) : M 0 0 = 1 ∧ M 1 1 = 1 := by
  have hdet : M 0 0 * M 1 1 = 1 := by
    have h := M.2
    rw [Matrix.det_fin_two, hz, mul_zero, sub_zero] at h
    exact h
  have h11 : 0 < M 1 1 := by
    have h : (0 : ℝ) < (M 1 0 : ℝ) * τ + (M 1 1 : ℝ) := hjac
    rw [hz, Int.cast_zero, zero_mul, zero_add] at h
    exact_mod_cast h
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with h | h <;> omega

/-- A matrix with vanishing lower-left entry and positive Jacobi denominator has positive
upper-left entry (`diag_eq_one_of_lowerLeft_eq_zero`). This is the terminal hypothesis of the word
walk in `wordRademacher_eq_rademacherInvariant` and `tendsto_sfJacobiCocycle_word`. -/
theorem topLeft_pos_of_lowerLeft_eq_zero {M : SL(2, ℤ)} {τ : ℝ}
    (hdenM : 0 < fltDenominator (M : Mat(2, ℤ)) τ) (hz : M 1 0 = 0) :
    0 < M 0 0 := by
  rw [(diag_eq_one_of_lowerLeft_eq_zero hz hdenM).1]
  exact one_pos

/-- At a matrix with vanishing lower-left entry and positive Jacobi denominator, `j_M(τ) = 1`
(`diag_eq_one_of_lowerLeft_eq_zero`). -/
theorem fltDenominator_eq_one_of_lowerLeft_eq_zero {M : SL(2, ℤ)} {τ : ℝ} (hz : M 1 0 = 0)
    (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) τ) :
    fltDenominator (M : Mat(2, ℤ)) τ = 1 := by
  change (M 1 0 : ℝ) * τ + (M 1 1 : ℝ) = 1
  rw [hz, (diag_eq_one_of_lowerLeft_eq_zero hz hjac).2]
  norm_num

/-- At a matrix with vanishing lower-left entry and positive Jacobi denominator,
`M·τ = τ + M 0 1` (`diag_eq_one_of_lowerLeft_eq_zero`). -/
theorem flt_eq_add_of_lowerLeft_eq_zero {M : SL(2, ℤ)} {τ : ℝ} (hz : M 1 0 = 0)
    (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) τ) :
    flt (M : Mat(2, ℤ)) τ = τ + (M 0 1 : ℝ) := by
  obtain ⟨h00, h11⟩ := diag_eq_one_of_lowerLeft_eq_zero hz hjac
  change ((M 0 0 : ℝ) * τ + (M 0 1 : ℝ)) / ((M 1 0 : ℝ) * τ + (M 1 1 : ℝ)) = τ + (M 0 1 : ℝ)
  rw [hz, h00, h11]
  push_cast
  ring

end Field

end SIC
