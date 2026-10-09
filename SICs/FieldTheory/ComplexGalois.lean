/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Ambient Complex Galois Automorphisms

Ambient complex Galois automorphisms, square-root switching, unit modulus descending from a
power, and the rational phases `e(q)` as roots of unity.

The analytic values lie in `ℂ`. This file therefore isolates the
project's ambient model of Galois automorphisms as `ℚ`-algebra automorphisms of `ℂ`, together
with the square-root switching condition used by the Minimalist Real Multiplication Values
Conjecture. It also records how such an automorphism moves a square root of a rational number,
and the elementary descent of unit modulus from a power of a complex number to the number itself.

This is an ambient analytic model rather than the group `Gal(ℚ̄/ℚ)`; consumers that need only
this representation can import it without depending on any quantum or ghost-fiducial
construction.

## Main definitions and results

- `ComplexGaloisAutomorphism`, `SwitchesSqrt`: the ambient automorphisms and the switching
  condition of [AFK25, Conjecture 1.36, `conj:mrmvc`](2).
- `map_eq_self_or_neg_of_sq_eq_ratCast`, `norm_map_eq_of_sq_eq_ratCast`: a `ℚ`-automorphism moves
  a square root of a rational number by at most a sign, so it preserves its modulus.
- `norm_eq_one_of_norm_pow_eq_one`: unit modulus descends from a nonzero natural power, the step
  used when a distribution identity controls a power of a Shintani--Faddeev value.
- `exp_two_pi_I_ratCast_pow_den`, `norm_map_exp_two_pi_I_ratCast`: the rational phase `e(q)` is
  a root of unity, hence of modulus one under every ambient automorphism;
  `exp_two_pi_I_eq_of_sub_intCast` is the integer periodicity `e(a) = e(b)` for `a - b ∈ ℤ` that
  the phases and q-products share.

## References

- [AFK25] Appleby, Flammia, Kopp, arXiv:2501.03970v2, Conjecture 1.36 and the remark on p. 20
-/

noncomputable section

namespace SIC

/-! ### Ambient Galois automorphisms

The analytic values lie in `ℂ`, so Galois actions are represented by `ℚ`-algebra
automorphisms of `ℂ`.  The square-root switching predicate isolates the action required by the
Minimalist RMVC. -/

/-- An ambient representative of a Galois automorphism over `ℚ`.

    AFK25 formulates the Minimalist RMVC using `Gal(ℚ̄/ℚ)`. Here the analytic values lie in `ℂ`,
    so Galois actions use automorphisms of `ℂ`; these preserve the subfield of algebraic values.
    This is also the ambient interpretation of [AFK25, remark on p. 20]. -/
abbrev ComplexGaloisAutomorphism := ℂ ≃ₐ[ℚ] ℂ

/-- `g` exchanges the two square roots of the positive discriminant `Δ`.
    This is the Galois condition in [AFK25, Conjecture 1.36, `conj:mrmvc`](2). -/
def SwitchesSqrt (g : ComplexGaloisAutomorphism) (Δ : ℤ) : Prop :=
  g (Real.sqrt (Δ : ℝ)) = -(Real.sqrt (Δ : ℝ) : ℂ)

/-! ### Square roots of rationals under a `ℚ`-automorphism

The ghost expansion carries the real prefactor `√(r(d-r)/(d²(d²-1)))`, which `g` does not fix.
That movement must be tracked rather than silently assumed invariant: a
`ℚ`-automorphism moves the square root of a rational number by at most a sign, which is all the
live construction needs, since only its modulus is consumed downstream. -/

/-- **A `ℚ`-automorphism of `ℂ` moves a square root of a rational number at most by a sign.** -/
theorem map_eq_self_or_neg_of_sq_eq_ratCast (g : ComplexGaloisAutomorphism) {y : ℂ} {r : ℚ}
    (hy : y ^ 2 = (r : ℂ)) : g y = y ∨ g y = -y := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  rw [← map_pow, hy, map_ratCast]

/-- Consequently `g` preserves the modulus of a square root of a rational number. -/
theorem norm_map_eq_of_sq_eq_ratCast (g : ComplexGaloisAutomorphism) {y : ℂ} {r : ℚ}
    (hy : y ^ 2 = (r : ℂ)) : ‖g y‖ = ‖y‖ := by
  rcases map_eq_self_or_neg_of_sq_eq_ratCast g hy with h | h <;> simp [h]

/-! ### Unit modulus from a power

That a *power* of a Shintani--Faddeev value has modulus one under a sign-switching automorphism is
established elsewhere. Passing back to the value itself is elementary and needs no
algebraicity: the modulus is a nonnegative real, and on nonnegative reals `x ↦ xⁿ` separates `1`
from everything else. -/

/-- If some positive power of `x` has modulus one, then so does `x`. The nonnegative-real step is
Mathlib's `pow_eq_one_iff_of_nonneg`. -/
theorem norm_eq_one_of_norm_pow_eq_one {x : ℂ} {m : ℕ} (hm : m ≠ 0) (h : ‖x ^ m‖ = 1) :
    ‖x‖ = 1 :=
  (pow_eq_one_iff_of_nonneg (norm_nonneg x) hm).mp (by rwa [← norm_pow])

/-! ### Rational phases

The exponential `e(q) = exp(2πi q)` of a rational number `q` is a root of unity. These are the
facts every root-of-unity phase of the project needs: a vanishing power and unit modulus under
every ambient automorphism; beside them, the integer periodicity of `e` and the criterion that
`e(q) = 1` exactly for integral `q`. -/

/-- `e(q)^{den(q)} = 1` for a rational `q`, since `Complex.isPrimitiveRoot_exp_rat`
identifies `e(q)` as a primitive `den(q)`-th root of unity. -/
theorem exp_two_pi_I_ratCast_pow_den (q : ℚ) :
    Complex.exp (2 * Real.pi * Complex.I * (q : ℂ)) ^ q.den = 1 :=
  (Complex.isPrimitiveRoot_exp_rat q).pow_eq_one

/-- `e(a) = e(b)` whenever `a - b` is an (embedded) integer: the elementary periodicity
underlying every integer-shift invariance of the project's phases and q-products. Phrased with
`a - b = k` (rather than `a = b + k`) so callers can discharge the hypothesis with
`push_cast; ring`, without matching a particular cast shape. -/
lemma exp_two_pi_I_eq_of_sub_intCast (a b : ℂ) (k : ℤ) (hab : a - b = (k : ℂ)) :
    Complex.exp (2 * Real.pi * Complex.I * a) = Complex.exp (2 * Real.pi * Complex.I * b) := by
  have ha : a = b + (k : ℂ) := by linear_combination hab
  rw [ha, mul_add, Complex.exp_add,
    show (2 : ℂ) * Real.pi * Complex.I * (k : ℂ) = (k : ℂ) * (2 * Real.pi * Complex.I) from
      by ring,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The rational phase `e(q)` equals one exactly when `q` is integral, by
`Complex.exp_eq_one_iff`. This is used by `SICs.Principal.Dilogarithm.ExactSequence`. -/
theorem exp_two_pi_I_ratCast_eq_one_iff (q : ℚ) :
    Complex.exp (2 * Real.pi * Complex.I * (q : ℂ)) = 1 ↔ ∃ n : ℤ, q = n := by
  have hf : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hc : (q : ℂ) = (n : ℂ) := mul_left_cancel₀ hf (by simpa only [mul_comm] using hn)
    exact_mod_cast hc
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    push_cast
    ring

/-- Every ambient automorphism sends `e(q)`, `q` rational, to a number of modulus one: its
image is again a `den(q)`-th root of unity (`Complex.norm_eq_one_of_pow_eq_one`). -/
theorem norm_map_exp_two_pi_I_ratCast (g : ComplexGaloisAutomorphism) (q : ℚ) :
    ‖g (Complex.exp (2 * Real.pi * Complex.I * (q : ℂ)))‖ = 1 := by
  apply Complex.norm_eq_one_of_pow_eq_one (n := q.den)
  · rw [← map_pow, exp_two_pi_I_ratCast_pow_den, map_one]
  · exact q.den_ne_zero

end SIC

end
