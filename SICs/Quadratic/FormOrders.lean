/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Quadratic.FormStabilizers
import Mathlib.Algebra.QuadraticAlgebra.Basic

/-!
# Monic Quadratic Orders

The monic quadratic order `ℤ[X]/(X²+bX+c)`, its norm-one units, its evaluation at `ρ_{Q,+}`, and
coordinatewise divisibility.

For a monic form `Q = ⟨1,b,c⟩` with positive nonsquare discriminant, the order `ℤ[ρ_{Q,+}]`
has integral coordinates
`x + yρ_{Q,+}`, with `ρ_{Q,+}² = -bρ_{Q,+}-c`. We use Mathlib's quadratic algebra
`ℤ[X]/(X²+bX+c)` for these coordinates and evaluate them at `ρ_{Q,+}` in `ℝ`; the quadratic
equation of the root makes evaluation a ring homomorphism.

The norm of `x+yρ_{Q,+}` is `x²-bxy+cy²`, and divisibility by an integer is equivalent to
divisibility of both coordinates. This is the coordinate form of
[AFK25, Corollary 4.35, `cr:etaqmodn`]; `SICs.Quadratic.CanonicalRepresentation` represents
these coordinates by form stabilizers, as in [AFK25, Theorem 4.34, `tm:canisointun`].

For the conductor-one form `⟨1,-Δ₀,(Δ₀²-Δ₀)/4⟩`, these are precisely the source coordinates
`x+y(Δ₀+√Δ₀)/2`. The construction below does not require an identification with the ring of
integers of a separately bundled number field.
-/

noncomputable section

namespace SIC.BinaryQF

/-! ### Integral order coordinates

The quadratic relation reduces products to two integral coordinates. -/

/-- The coordinate ring `ℤ[X]/(X²+bX+c)` associated with `Q = ⟨a,b,c⟩`. For a monic admissible
form, evaluation at the root (`monicOrderReal`) identifies it with the order `ℤ[ρ_{Q,+}]`. The
conductor-one instance is the integral order in [AFK25, Theorem 4.34(1), `tm:canisointun`]. -/
abbrev MonicOrder (Q : BinaryQF) := QuadraticAlgebra ℤ (-Q.c) (-Q.b)

/-- The coordinate norm is `Nm(x+yρ) = x²-bxy+cy²`. -/
lemma monicOrder_norm (Q : BinaryQF) (z : Q.MonicOrder) :
    z.norm = z.re ^ 2 - Q.b * z.re * z.im + Q.c * z.im ^ 2 := by
  simp only [QuadraticAlgebra.norm_def]
  ring

/-! ### Norm-one units

The norm-one units of the coordinate ring form a subgroup of its unit group;
`SICs.Quadratic.CanonicalRepresentation` maps it onto the determinant-one stabilizers. -/

/-- The norm-one subgroup of the units of `ℤ[X]/(X²+bX+c)`. Under evaluation at `ρ_{Q,+}`, these
are the norm-one units of the real order `ℤ[ρ_{Q,+}]`. -/
def monicNormOneUnits (Q : BinaryQF) : Subgroup Q.MonicOrderˣ :=
  (QuadraticAlgebra.norm.comp (Units.coeHom Q.MonicOrder)).ker

/-- A unit belongs to `monicNormOneUnits` exactly when `Nm(u) = 1`. -/
lemma mem_monicNormOneUnits_iff (Q : BinaryQF) (u : Q.MonicOrderˣ) :
    u ∈ Q.monicNormOneUnits ↔ (u : Q.MonicOrder).norm = 1 := Iff.rfl

/-! ### Evaluation in the selected real root

Evaluation sends the quadratic coordinate to `ρ_{Q,+}`. The root equation makes this a ring
map. -/

/-- Evaluation `x+yρ ↦ x+yρ_{Q,+}` of integral order coordinates in the selected real root. -/
def monicOrderReal {Q : BinaryQF} (ha : Q.a = 1) (hdisc : 0 ≤ Q.disc) :
    Q.MonicOrder →ₐ[ℤ] ℝ :=
  QuadraticAlgebra.lift ⟨Q.rootPlus, by
    have h := Q.rootPlus_satisfies_quadratic_of_disc_nonneg
      (by omega) hdisc
    rw [ha] at h
    simp only [Int.cast_one, one_mul] at h
    simp only [zsmul_eq_mul, Int.cast_neg, mul_one]
    nlinarith⟩

/-- Evaluation at `ρ_{Q,+}` has the coordinate formula `x+yρ_{Q,+}`. -/
@[simp]
lemma monicOrderReal_apply {Q : BinaryQF} (ha : Q.a = 1) (hdisc : 0 ≤ Q.disc)
    (z : Q.MonicOrder) :
    monicOrderReal ha hdisc z = (z.re : ℝ) + (z.im : ℝ) * Q.rootPlus := by
  simp [monicOrderReal, QuadraticAlgebra.lift, zsmul_eq_mul]

/-! ### Integral divisibility

Divisibility by `d` in the quadratic order is equivalent to divisibility of both integral
coordinates. Applied to `u-1` in `SICs.Quadratic.CanonicalRepresentation`, this gives the exact
congruence correspondence for units.
The proof of [AFK25, Corollary 4.35, `cr:etaqmodn`] drops `S` from `SQ` in its second matrix-algebra
membership statement; the canonical representation uses `SQ` throughout. -/

/-- Divisibility by an integer in the quadratic order is coordinatewise:
`n ∣ x+yρ` if and only if `n ∣ x` and `n ∣ y`. This is Mathlib's
`QuadraticAlgebra.algebraMap_dvd_iff` for the integer cast, and the coordinate form of
[AFK25, Corollary 4.35, `cr:etaqmodn`], including `n = 0`. -/
lemma monicOrder_intCast_dvd_iff (Q : BinaryQF) (n : ℤ) (z : Q.MonicOrder) :
    (n : Q.MonicOrder) ∣ z ↔ n ∣ z.re ∧ n ∣ z.im :=
  QuadraticAlgebra.algebraMap_dvd_iff

end SIC.BinaryQF

end
