/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Analysis.IdentityTheorem
import SICs.Principal.Quadratic.Stabilizers
import SICs.SpecialFunctions.Faddeev.Divisor

/-!
# The principal Faddeev product

The meromorphic three-factor Faddeev product at `A_d` and its index and lattice shift laws.

This module follows [RW26, Radchenko, Wheeler (2026), Proposition 2(ii),
`prop:prod.id.mod,fad`, equation (20), `eq:modulartofaddeevCF`] at
`A_d = (T^{d-1}S)³`, `τ = ρ_d`. All three intermediate periods are `ρ_d` and their
arguments are `z/ρ_d²`, `z/ρ_d`, and `z`. We choose the two free intermediate indices to
be zero, giving `Φ(z/ρ_d²-n;ρ_d) Φ(z/ρ_d;ρ_d) Φ(z+mρ_d;ρ_d)`. Each factor is
meromorphic in its complex argument, hence so is the product.

## The argument

Increasing the left index shifts the last generator by `ρ_d`; increasing the right index
shifts the first generator by `-1`. The generator's difference equations therefore give
the index shifts of Section 2.2. For the right index the identity
`-1/ρ_d = ρ_d-(d-1)` matches the exponential multiplier with `j_{A_d}(ρ_d) = ρ_d³`.

The two internal indices are free. Transfer the first between the first two factors, then
the second between the last two factors. The identity `ρ_d + ρ_d⁻¹ = d-1` makes the
phase gaps integral at every step. Nonzero gamma denominators at the two endpoints of
each transfer control the intermediate steps by closure of the Barnes zero cone.

For simultaneous shifts of the outer indices, the phase equality of equation (16)
gives an integer gap between `z+mρ_d` and `(z/ρ_d²-n)/ρ_d`. The same transport
therefore applies to the two outer factors, leaving the middle factor fixed. It uses
the gamma denominators at the two endpoint arguments.

For the lattice shift by `1`, choose intermediate indices `(1-d,-1)` in the product with
outer indices `(m,n-d(d-2))`. The three arguments become those at `z+1` because
`ρ_d + ρ_d⁻¹ = d-1`. For the shift by `ρ_d`, the outer indices are `(m+1,n+1-d)`
and the intermediate indices are `(-1,0)`. Only the first adjacent pair moves in the latter
case, so no denominator condition is needed on the unchanged last factor.

These are pointwise gamma quotients. A product of their totalized values does not cancel
a zero against a pole. The shift identities therefore retain their gamma-denominator
conditions; their equality as meromorphic germs extends to every complex argument.
-/

noncomputable section

open Topology

namespace SIC

/-! ### The fixed three-factor expression

The matrix and period are fixed by the principal family; only the integer indices and the
complex argument vary. The expression is equation (20) with both internal indices zero.
-/

/-- The product `Φ_{A_d,m,n}(z;ρ_d)` of [RW26, Radchenko, Wheeler (2026), Proposition 2(ii),
`prop:prod.id.mod,fad`, equation (20), `eq:modulartofaddeevCF`] at `γ = A_d`, extracting its
three-factor product with both intermediate indices zero. Each factor is `faddeevS`; pole values
use its totalization. The arbitrary-index identity is `principalFaddeev_eq_indices`.
At `τ=ρ_d`, `principalFaddeevComplex_principalRoot` identifies the direct complex-period
product with this expression; `faddeevModularUHP_principalA_eventuallyEq_complex` compares
that product with the modular q-product as meromorphic germs. -/
def principalFaddeev (d : ℕ) (m n : ℤ) (z : ℂ) : ℂ :=
  faddeevS (z / (principalRoot d : ℂ) ^ 2 - n) (principalRoot d) *
    faddeevS (z / (principalRoot d : ℂ)) (principalRoot d) *
    faddeevS (z + m * (principalRoot d : ℂ)) (principalRoot d)

/-- The factorwise sufficient gamma domain for the concrete principal Faddeev product.
Its constructor records nonvanishing of the three displayed quotient denominators; this
domain need not be the maximal analytic locus of their product. -/
structure PrincipalFaddeevGammaRegular (d : ℕ) (m n : ℤ) (z : ℂ) : Prop where
  /-- The gamma denominator of the first Faddeev factor is nonzero. -/
  first : barnesDoubleGammaInv ((principalRoot d : ℂ) -
    (z / (principalRoot d : ℂ) ^ 2 - n)) 1 (principalRoot d) ≠ 0
  /-- The gamma denominator of the middle Faddeev factor is nonzero. -/
  middle : barnesDoubleGammaInv ((principalRoot d : ℂ) -
    z / (principalRoot d : ℂ)) 1 (principalRoot d) ≠ 0
  /-- The gamma denominator of the last Faddeev factor is nonzero. -/
  last : barnesDoubleGammaInv ((principalRoot d : ℂ) -
    (z + m * (principalRoot d : ℂ))) 1 (principalRoot d) ≠ 0

/-- The origin is in the factorwise gamma domain of the unshifted principal product. -/
theorem principalFaddeevGammaRegular_zero (d : ℕ) (hd : 3 < d) :
    PrincipalFaddeevGammaRegular d 0 0 0 := by
  have hρpos := principalRoot_pos d hd
  have hρ := ofReal_principalRoot_mem_slitPlane d hd
  have hden : barnesDoubleGammaInv (principalRoot d) 1 (principalRoot d) ≠ 0 :=
    barnesDoubleGammaInv_ne_zero_of_re_pos _ _ hρ hρpos.le hρpos
  constructor <;> simpa using hden

/-- The principal three-factor product is analytic on its factorwise gamma domain. -/
theorem analyticAt_principalFaddeev (d : ℕ) (hd : 3 < d)
    (m n : ℤ) (z : ℂ) (hz : PrincipalFaddeevGammaRegular d m n z) :
    AnalyticAt ℂ (principalFaddeev d m n) z := by
  let ρ : ℂ := principalRoot d
  have hρ := ofReal_principalRoot_mem_slitPlane d hd
  exact ((analyticAt_faddeevS _ ρ hρ hz.first).comp
    (f := fun w : ℂ => w / ρ ^ 2 - n) (by fun_prop)).mul
    ((analyticAt_faddeevS _ ρ hρ hz.middle).comp
      (f := fun w : ℂ => w / ρ) (by fun_prop)) |>.mul
    ((analyticAt_faddeevS _ ρ hρ hz.last).comp
      (f := fun w : ℂ => w + m * ρ) (by fun_prop))

/-- The product `Φ_{A_d,m,n}(z;ρ_d)` is meromorphic in `z`, as follows from
[RW26, Radchenko, Wheeler (2026), equation (20), `eq:modulartofaddeevCF`].
Specializes `meromorphicAt_faddeevS` at the three affine principal arguments. -/
theorem meromorphicAt_principalFaddeev (d : ℕ) (hd : 3 < d)
    (m n : ℤ) (z : ℂ) : MeromorphicAt (principalFaddeev d m n) z := by
  let ρ : ℂ := principalRoot d
  have hρ : ρ ∈ Complex.slitPlane := ofReal_principalRoot_mem_slitPlane d hd
  have h₂ : MeromorphicAt (fun w : ℂ => faddeevS (w / ρ ^ 2 - n) ρ) z := by
    have ha : AnalyticAt ℂ (fun w : ℂ => w / ρ ^ 2 - n) z :=
      (analyticAt_id.div_const).sub analyticAt_const
    exact (meromorphicAt_faddeevS (z / ρ ^ 2 - n) ρ hρ).comp_analyticAt
      (g := fun w : ℂ => w / ρ ^ 2 - n) ha
  have h₁ : MeromorphicAt (fun w : ℂ => faddeevS (w / ρ) ρ) z := by
    have ha : AnalyticAt ℂ (fun w : ℂ => w / ρ) z := analyticAt_id.div_const
    exact (meromorphicAt_faddeevS (z / ρ) ρ hρ).comp_analyticAt
      (g := fun w : ℂ => w / ρ) ha
  have h₀ : MeromorphicAt (fun w : ℂ => faddeevS (w + m * ρ) ρ) z := by
    have ha : AnalyticAt ℂ (fun w : ℂ => w + m * ρ) z :=
      analyticAt_id.add analyticAt_const
    exact (meromorphicAt_faddeevS (z + m * ρ) ρ hρ).comp_analyticAt
      (g := fun w : ℂ => w + m * ρ) ha
  exact (h₂.mul h₁).mul h₀

/-! ### Index shifts

Only the factor containing the shifted index changes. The displayed gamma denominators
exclude poles in that factor; no nonvanishing condition is needed on the unchanged factors.
-/

/-- The first factor's shifted phase agrees with the principal Jacobi phase modulo an
integer, using `ρ_d + ρ_d⁻¹ = d - 1` and `j_{A_d}(ρ_d) = ρ_d³`.
Used by `principalFaddeev_index_add_one_right`. -/
private lemma principalFaddeev_right_phase (d : ℕ) (hd : 3 < d)
    (n : ℤ) (z : ℂ) :
    Complex.exp (2 * Real.pi * Complex.I *
        ((z / (principalRoot d : ℂ) ^ 2 - n) / (principalRoot d : ℂ))) =
      Complex.exp (2 * Real.pi * Complex.I *
        (z / (principalJacobiFactor d : ℂ) + n * (principalRoot d : ℂ))) := by
  let ρ : ℂ := principalRoot d
  have hρ : ρ ≠ 0 := ofReal_principalRoot_ne_zero d hd
  have hsum : ρ + ρ⁻¹ = (d : ℂ) - 1 := ofReal_principalRoot_add_inv d hd
  have hj : (principalJacobiFactor d : ℂ) = ρ ^ 3 := by
    dsimp only [ρ]
    exact_mod_cast principalJacobiFactor_eq_principalRoot_pow_three d hd
  apply exp_two_pi_I_eq_of_sub_intCast _ _ (-n * ((d : ℤ) - 1))
  rw [hj]
  calc
    (z / ρ ^ 2 - (n : ℂ)) / ρ - (z / ρ ^ 3 + (n : ℂ) * ρ) =
        -(n : ℂ) * (ρ + ρ⁻¹) := by field_simp [hρ]; ring
    _ = ((-n * ((d : ℤ) - 1) : ℤ) : ℂ) := by rw [hsum]; push_cast; ring

/-- A nonreal principal argument remains a finite gamma quotient after any integer
translation in `ℤρ_d+ℤ`; used by the nonreal product identities. -/
private lemma principalFaddeev_den_ne_zero (d : ℕ) (hd : 3 < d)
    (w : ℂ) (hw : w.im ≠ 0) (a b : ℤ) :
    barnesDoubleGammaInv
      ((principalRoot d : ℂ) - (w + a * (principalRoot d : ℂ) + b))
      1 (principalRoot d) ≠ 0 := by
  have hρpos := principalRoot_pos d hd
  apply faddeevS_denominator_ne_zero_of_im_ne_zero _ _ hρpos
  simpa [Complex.mul_im] using hw

/-- Division by `ρ_d` or `ρ_d²` preserves a nonzero imaginary part. -/
private lemma principalFaddeev_div_im_ne_zero (d : ℕ) (hd : 3 < d)
    (z : ℂ) (hz : z.im ≠ 0) (k : ℕ) :
    (z / (principalRoot d : ℂ) ^ k).im ≠ 0 := by
  simpa only [← Complex.ofReal_pow, Complex.div_ofReal_im] using
    div_ne_zero hz (pow_ne_zero k (ne_of_gt (principalRoot_pos d hd)))

/-- The left index shift `Φ_{A_d,m+1,n}(z)(1-e(z+mρ_d)) = Φ_{A_d,m,n}(z)` of
[RW26, Radchenko, Wheeler (2026), Section 2.2], where the shifted factor's gamma
denominator at `-(z+mρ_d)` is nonzero.
Specializes `faddeevS_add_tau` at the last factor. -/
theorem principalFaddeev_index_add_one_left (d : ℕ) (hd : 3 < d)
    (m n : ℤ) (z : ℂ)
    (hzτ : barnesDoubleGammaInv
      (-(z + m * (principalRoot d : ℂ))) 1 (principalRoot d) ≠ 0) :
    principalFaddeev d (m + 1) n z *
        (1 - Complex.exp (2 * Real.pi * Complex.I * (z + m * (principalRoot d : ℂ)))) =
      principalFaddeev d m n z := by
  let ρ : ℂ := principalRoot d
  have hρ : ρ ∈ Complex.slitPlane := ofReal_principalRoot_mem_slitPlane d hd
  have hshift := faddeevS_add_tau (z + m * ρ) ρ hρ hzτ
  simp only [principalFaddeev, Int.cast_add, Int.cast_one]
  rw [show z + ((m : ℂ) + 1) * ρ = (z + m * ρ) + ρ by ring]
  calc
    (faddeevS (z / ρ ^ 2 - n) ρ * faddeevS (z / ρ) ρ *
        faddeevS ((z + m * ρ) + ρ) ρ) *
        (1 - Complex.exp (2 * Real.pi * Complex.I * (z + m * ρ))) =
      (faddeevS (z / ρ ^ 2 - n) ρ * faddeevS (z / ρ) ρ) *
        (faddeevS ((z + m * ρ) + ρ) ρ *
          (1 - Complex.exp (2 * Real.pi * Complex.I * (z + m * ρ)))) := by ring
    _ = _ := by rw [hshift]

/-- The right index shift
`Φ_{A_d,m,n+1}(z) = (1-e(z/j_{A_d}(ρ_d)+nρ_d)) Φ_{A_d,m,n}(z)` of
[RW26, Radchenko, Wheeler (2026), Section 2.2], where the first factor's gamma
denominator at `ρ_d-(z/ρ_d²-n)` is nonzero.
Specializes `faddeevS_add_one` at the first factor. -/
theorem principalFaddeev_index_add_one_right (d : ℕ) (hd : 3 < d)
    (m n : ℤ) (z : ℂ)
    (hz : barnesDoubleGammaInv
      ((principalRoot d : ℂ) - (z / (principalRoot d : ℂ) ^ 2 - n))
      1 (principalRoot d) ≠ 0) :
    principalFaddeev d m (n + 1) z =
      (1 - Complex.exp (2 * Real.pi * Complex.I *
        (z / (principalJacobiFactor d : ℂ) + n * (principalRoot d : ℂ)))) *
          principalFaddeev d m n z := by
  let ρ : ℂ := principalRoot d
  have hρ : ρ ∈ Complex.slitPlane := ofReal_principalRoot_mem_slitPlane d hd
  have hden : barnesDoubleGammaInv
      (ρ - (z / ρ ^ 2 - (n + 1 : ℤ)) - 1) 1 ρ ≠ 0 := by
    change barnesDoubleGammaInv (ρ - (z / ρ ^ 2 - n)) 1 ρ ≠ 0 at hz
    simpa only [show ρ - (z / ρ ^ 2 - (n + 1 : ℤ)) - 1 =
        ρ - (z / ρ ^ 2 - n) by push_cast; ring] using hz
  have hshift := faddeevS_add_one (z / ρ ^ 2 - (n + 1 : ℤ)) ρ hρ hden
  have hn : z / ρ ^ 2 - (n + 1 : ℤ) + 1 = z / ρ ^ 2 - n := by push_cast; ring
  rw [hn, principalFaddeev_right_phase d hd n z] at hshift
  simp only [principalFaddeev]
  rw [← hshift]
  ring

/-! ### Intermediate indices

Equation (20) permits arbitrary intermediate integers. The two adjacent transfers move
the first internal index from zero to `m₁`, then the second from zero to `m₂`.
The four gamma denominators below are at the endpoints of these transfers.
In this section, `ρ` denotes the complex embedding of the principal root `ρ_d`.
-/

section PrincipalFaddeevPaths

variable (d : ℕ)

/-- The complex principal root for the index and lattice-shift formulas. -/
local notation "ρ" => (principalRoot d : ℂ)

/-- Adjacent-factor transport at `ρ_d`, where `ρ_d + ρ_d⁻¹ = d - 1`.
Used by `principalFaddeev_eq_indices` and
`principalFaddeev_add_principalRoot`. Specializes `faddeevS_transfer_int`. -/
private lemma principalFaddeev_transfer_pair (hd : 3 < d)
    (u v : ℂ) (k r : ℤ)
    (huv : u - v / ρ = k)
    (hu : barnesDoubleGammaInv (ρ - (u + (max r 0 : ℤ) * ρ)) 1 ρ ≠ 0)
    (hv : barnesDoubleGammaInv (ρ - (v - (min r 0 : ℤ))) 1 ρ ≠ 0) :
    faddeevS (u + r * ρ) ρ * faddeevS (v - r) ρ =
      faddeevS u ρ * faddeevS v ρ := by
  have hρ : ρ ∈ Complex.slitPlane := ofReal_principalRoot_mem_slitPlane d hd
  have hsum : ρ + ρ⁻¹ = (d : ℂ) - 1 := ofReal_principalRoot_add_inv d hd
  exact faddeevS_transfer_int u v ρ ρ k
    ((d : ℤ) - 1) r hρ hρ
    (by simpa only [one_div, Int.cast_sub, Int.cast_natCast, Int.cast_one] using hsum)
    huv hu hv

/-- The product formula with arbitrary intermediate integers `m₁,m₂` at `A_d`:
`Φ_{A_d,m,n}(z) = Φ(z/ρ_d²+m₁ρ_d-n) Φ(z/ρ_d+m₂ρ_d-m₁) Φ(z+mρ_d-m₂)`.
This is [RW26, Radchenko, Wheeler (2026), Proposition 2(ii), `prop:prod.id.mod,fad`,
equation (20), `eq:modulartofaddeevCF`], where the four gamma denominators at the
transfer endpoints are nonzero. Specializes `faddeevS_transfer_int` at the principal period. -/
@[source
  "RW26, equation (20), p. 7, eq:modulartofaddeevCF (γ = A_d, arbitrary intermediate indices)"]
theorem principalFaddeev_eq_indices (hd : 3 < d)
    (m n m₁ m₂ : ℤ) (z : ℂ)
    (h₂ : barnesDoubleGammaInv
      (ρ - (z / ρ ^ 2 + (max m₁ 0 : ℤ) * ρ - n)) 1 ρ ≠ 0)
    (h₁ : barnesDoubleGammaInv
      (ρ - (z / ρ - (min m₁ 0 : ℤ))) 1 ρ ≠ 0)
    (h₁' : barnesDoubleGammaInv
      (ρ - (z / ρ + (max m₂ 0 : ℤ) * ρ - m₁)) 1 ρ ≠ 0)
    (h₀ : barnesDoubleGammaInv
      (ρ - (z + m * ρ - (min m₂ 0 : ℤ))) 1 ρ ≠ 0) :
    principalFaddeev d m n z =
      faddeevS (z / ρ ^ 2 + m₁ * ρ - n) ρ *
        faddeevS (z / ρ + m₂ * ρ - m₁) ρ *
        faddeevS (z + m * ρ - m₂) ρ := by
  have hρ0 : ρ ≠ 0 := ofReal_principalRoot_ne_zero d hd
  have hphase₁ : (z / ρ ^ 2 - (n : ℂ)) - (z / ρ) / ρ = ((-n : ℤ) : ℂ) := by
    simp only [Int.cast_neg]; field_simp [hρ0]; ring
  have hphase₂ : (z / ρ - (m₁ : ℂ)) - (z + m * ρ) / ρ = ((-m₁-m : ℤ) : ℂ) := by
    simp only [Int.cast_sub, Int.cast_neg]; field_simp [hρ0]; ring
  have h₂' : barnesDoubleGammaInv
      (ρ - ((z / ρ ^ 2 - n) + (max m₁ 0 : ℤ) * ρ)) 1 ρ ≠ 0 := by
    convert h₂ using 1; ring_nf
  have h₁'' : barnesDoubleGammaInv
      (ρ - ((z / ρ - m₁) + (max m₂ 0 : ℤ) * ρ)) 1 ρ ≠ 0 := by
    convert h₁' using 1; ring_nf
  have hfirst := principalFaddeev_transfer_pair d hd
    (z / ρ ^ 2 - n) (z / ρ) (-n) m₁ hphase₁ h₂' h₁
  have hsecond := principalFaddeev_transfer_pair d hd
    (z / ρ - m₁) (z + m * ρ) (-m₁-m) m₂ hphase₂ h₁'' h₀
  simp only [principalFaddeev]
  calc
    _ = (faddeevS (z / ρ ^ 2 - n + m₁ * ρ) ρ * faddeevS (z / ρ - m₁) ρ) *
        faddeevS (z + m * ρ) ρ := by rw [hfirst]
    _ = faddeevS (z / ρ ^ 2 - n + m₁ * ρ) ρ *
        (faddeevS (z / ρ - m₁ + m₂ * ρ) ρ *
          faddeevS (z + m * ρ - m₂) ρ) := by rw [mul_assoc, hsecond]
    _ = _ := by
      rw [show z / ρ ^ 2 - (n : ℂ) + m₁ * ρ = z / ρ ^ 2 + m₁ * ρ - n by ring,
          show z / ρ - (m₁ : ℂ) + m₂ * ρ = z / ρ + m₂ * ρ - m₁ by ring,
          ← mul_assoc]

/-! ### Simultaneous index shifts

At the fixed point `ρ_d`, equation (16) follows from equality of the outer factors'
exponential multipliers. The first factor's phase agrees with the Jacobi phase, and
equality of complex exponentials gives an integer phase gap. Transport the two outer
factors together; the middle factor does not change.
-/

/-- The simultaneous index shift `Φ_{A_d,m+k,n+k}(z;ρ_d) = Φ_{A_d,m,n}(z;ρ_d)` of
[RW26, Radchenko, Wheeler (2026), equation (16), `eq:faddeevperiod`], when
`e(z+mρ_d) = e(z/j_{A_d}(ρ_d)+nρ_d)` and the gamma denominators along the two
outer transfer endpoints are nonzero. Specializes `faddeevS_transfer_int` at the
principal period. -/
@[source "RW26, equation (16), p. 6, eq:faddeevperiod (γ = A_d, endpoint gamma denominators)"]
theorem principalFaddeev_indices_add (hd : 3 < d)
    (m n k : ℤ) (z : ℂ)
    (hphase : Complex.exp (2 * Real.pi * Complex.I * (z + m * ρ)) =
      Complex.exp (2 * Real.pi * Complex.I *
        (z / (principalJacobiFactor d : ℂ) + n * ρ)))
    (h₀ : barnesDoubleGammaInv
      (ρ - (z + (m + max k 0 : ℤ) * ρ)) 1 ρ ≠ 0)
    (h₂ : barnesDoubleGammaInv
      (ρ - (z / ρ ^ 2 - (n + min k 0 : ℤ))) 1 ρ ≠ 0) :
    principalFaddeev d (m + k) (n + k) z =
      principalFaddeev d m n z := by
  let u : ℂ := z + m * ρ
  let v : ℂ := z / ρ ^ 2 - n
  have hphase' : Complex.exp (2 * Real.pi * Complex.I * u) =
      Complex.exp (2 * Real.pi * Complex.I * (v / ρ)) := by
    exact hphase.trans (principalFaddeev_right_phase d hd n z).symm
  obtain ⟨a, ha⟩ := Complex.exp_eq_exp_iff_exists_int.mp hphase'
  have hfactor : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have hgap : u - v / ρ = (a : ℂ) := by
    apply mul_left_cancel₀ hfactor
    linear_combination ha
  have h₀' : barnesDoubleGammaInv
      (ρ - (u + (max k 0 : ℤ) * ρ)) 1 ρ ≠ 0 := by
    convert h₀ using 1; dsimp [u]; push_cast; ring_nf
  have h₂' : barnesDoubleGammaInv
      (ρ - (v - (min k 0 : ℤ))) 1 ρ ≠ 0 := by
    convert h₂ using 1; dsimp [v]; push_cast; ring_nf
  have htransfer := principalFaddeev_transfer_pair d hd u v a k hgap h₀' h₂'
  calc
    _ = (faddeevS (u + k * ρ) ρ * faddeevS (v - k) ρ) *
        faddeevS (z / ρ) ρ := by dsimp [principalFaddeev, u, v]; push_cast; ring_nf
    _ = principalFaddeev d m n z := by
      rw [htransfer]
      dsimp [principalFaddeev, u, v]
      ring

/-! ### Lattice shifts

The lower row of `A_d` is `(d(d-2),1-d)`. The two lattice shifts of
[RW26, Radchenko, Wheeler (2026), Section 2.2] therefore change the outer indices by
`(0,-d(d-2))` and `(1,1-d)`. The arbitrary intermediate-index formula gives the first
shift with indices `(1-d,-1)`. The second needs only the first adjacent-factor transfer,
at index `-1`; the last factor already has the required argument.
-/

/-- The quadratic identity for the first factor in `principalFaddeev_add_one`. -/
private lemma principalFaddeev_unit_root_identity (hd : 3 < d) :
    (1 - (d : ℂ)) * ρ + (d : ℂ) * ((d : ℂ) - 2) = 1 / ρ ^ 2 := by
  have hρ : ρ ≠ 0 := ofReal_principalRoot_ne_zero d hd
  have hsum : ρ + ρ⁻¹ = (d : ℂ) - 1 := ofReal_principalRoot_add_inv d hd
  have hd' : (d : ℂ) = ρ + ρ⁻¹ + 1 := by linear_combination -hsum
  rw [hd']
  field_simp [hρ]
  ring

/-- The unit lattice shift `Φ_{A_d,m,n}(z+1) = Φ_{A_d,m,n-d(d-2)}(z)` of
[RW26, Radchenko, Wheeler (2026), Section 2.2], where the gamma denominators along
the four transfer endpoints for intermediate indices `(1-d,-1)` are nonzero.
This follows from `principalFaddeev_eq_indices`. -/
theorem principalFaddeev_add_one (hd : 3 < d)
    (m n : ℤ) (z : ℂ)
    (h₂ : barnesDoubleGammaInv
      (ρ - (z / ρ ^ 2 + (max (1 - (d : ℤ)) 0 : ℤ) * ρ -
        (n - (d : ℤ) * ((d : ℤ) - 2) : ℤ))) 1 ρ ≠ 0)
    (h₁ : barnesDoubleGammaInv
      (ρ - (z / ρ - (min (1 - (d : ℤ)) 0 : ℤ))) 1 ρ ≠ 0)
    (h₁' : barnesDoubleGammaInv
      (ρ - (z / ρ + (max (-1 : ℤ) 0 : ℤ) * ρ - (1 - (d : ℤ) : ℤ))) 1 ρ ≠ 0)
    (h₀ : barnesDoubleGammaInv
      (ρ - (z + m * ρ - (min (-1 : ℤ) 0 : ℤ))) 1 ρ ≠ 0) :
    principalFaddeev d m n (z + 1) =
      principalFaddeev d m (n - (d : ℤ) * ((d : ℤ) - 2)) z := by
  have hsum : ρ + ρ⁻¹ = (d : ℂ) - 1 := ofReal_principalRoot_add_inv d hd
  have hunit₂ : (1 - (d : ℂ)) * ρ + (d : ℂ) * ((d : ℂ) - 2) = 1 / ρ ^ 2 :=
    principalFaddeev_unit_root_identity d hd
  have hunit₁ : -ρ - (1 - (d : ℂ)) = 1 / ρ := by
    rw [one_div]
    linear_combination -hsum
  have harg₂ : z / ρ ^ 2 + (1 - (d : ℤ) : ℤ) * ρ -
      (n - (d : ℤ) * ((d : ℤ) - 2) : ℤ) = (z + 1) / ρ ^ 2 - n := by
    push_cast
    rw [add_div]
    linear_combination hunit₂
  have harg₁ : z / ρ + (-1 : ℤ) * ρ - (1 - (d : ℤ) : ℤ) =
      (z + 1) / ρ := by
    push_cast
    rw [add_div]
    linear_combination hunit₁
  have hindices := principalFaddeev_eq_indices d hd m
    (n - (d : ℤ) * ((d : ℤ) - 2)) (1 - (d : ℤ)) (-1) z h₂ h₁ h₁' h₀
  rw [hindices]
  simp only [principalFaddeev]
  rw [← harg₂, ← harg₁]
  congr 2
  norm_num
  ring

/-- The first factor's period-shifted argument in
`principalFaddeev_add_principalRoot`. -/
private lemma principalFaddeev_period_first_argument (hd : 3 < d)
    (n : ℤ) (z : ℂ) :
    z / ρ ^ 2 - (n + 1 - (d : ℤ) : ℤ) + (-1 : ℤ) * ρ =
      (z + ρ) / ρ ^ 2 - n := by
  have hρ : ρ ≠ 0 := ofReal_principalRoot_ne_zero d hd
  have hsum : ρ + ρ⁻¹ = (d : ℂ) - 1 := ofReal_principalRoot_add_inv d hd
  have hρdiv : ρ / ρ ^ 2 = ρ⁻¹ := by field_simp [hρ]
  push_cast
  rw [add_div, hρdiv]
  linear_combination -hsum

/-- The period lattice shift `Φ_{A_d,m,n}(z+ρ_d) = Φ_{A_d,m+1,n+1-d}(z)` of
[RW26, Radchenko, Wheeler (2026), Section 2.2], where the gamma denominators along
the two endpoints of the first intermediate-index transfer from `0` to `-1` are nonzero.
Specializes `faddeevS_transfer_int` at the first adjacent pair. -/
theorem principalFaddeev_add_principalRoot (hd : 3 < d)
    (m n : ℤ) (z : ℂ)
    (h₂ : barnesDoubleGammaInv
      (ρ - (z / ρ ^ 2 + (max (-1 : ℤ) 0 : ℤ) * ρ -
        (n + 1 - (d : ℤ) : ℤ))) 1 ρ ≠ 0)
    (h₁ : barnesDoubleGammaInv
      (ρ - (z / ρ - (min (-1 : ℤ) 0 : ℤ))) 1 ρ ≠ 0) :
    principalFaddeev d m n (z + ρ) =
      principalFaddeev d (m + 1) (n + 1 - (d : ℤ)) z := by
  have hρ : ρ ≠ 0 := ofReal_principalRoot_ne_zero d hd
  have hphase : (z / ρ ^ 2 - (n + 1 - (d : ℤ) : ℤ)) - (z / ρ) / ρ =
      ((-(n + 1 - (d : ℤ)) : ℤ) : ℂ) := by
    push_cast
    field_simp [hρ]
    ring
  have h₂' : barnesDoubleGammaInv
      (ρ - ((z / ρ ^ 2 - (n + 1 - (d : ℤ) : ℤ)) +
        (max (-1 : ℤ) 0 : ℤ) * ρ)) 1 ρ ≠ 0 := by
    convert h₂ using 1; ring_nf
  have htransfer := principalFaddeev_transfer_pair d hd
    (z / ρ ^ 2 - (n + 1 - (d : ℤ) : ℤ)) (z / ρ)
    (-(n + 1 - (d : ℤ))) (-1) hphase h₂' h₁
  have harg₂ : z / ρ ^ 2 - (n + 1 - (d : ℤ) : ℤ) + (-1 : ℤ) * ρ =
      (z + ρ) / ρ ^ 2 - n := principalFaddeev_period_first_argument d hd n z
  have harg₁ : z / ρ - (-1 : ℤ) = (z + ρ) / ρ := by
    push_cast
    field_simp [hρ]
    ring
  simp only [principalFaddeev, Int.cast_add, Int.cast_one]
  rw [← harg₂, ← harg₁, ← htransfer]
  congr 2
  ring

/-! ### Pointwise identities off the real axis

All arguments in the product are real affine transforms of `z`. Their imaginary parts
remain nonzero when `z` is nonreal, so every endpoint gamma denominator is nonzero.
-/

/-- For nonreal `z`, the unit lattice shift of
[RW26, Radchenko, Wheeler (2026), Section 2.2] follows from
`principalFaddeev_add_one`. -/
theorem principalFaddeev_add_one_of_im_ne_zero (hd : 3 < d)
    (m n : ℤ) (z : ℂ) (hz : z.im ≠ 0) :
    principalFaddeev d m n (z + 1) =
      principalFaddeev d m (n - (d : ℤ) * ((d : ℤ) - 2)) z := by
  have hz₂ := principalFaddeev_div_im_ne_zero d hd z hz 2
  have hz₁ := principalFaddeev_div_im_ne_zero d hd z hz 1
  apply principalFaddeev_add_one d hd m n z
  · convert principalFaddeev_den_ne_zero d hd (z / ρ ^ 2) hz₂
      (max (1 - (d : ℤ)) 0) (-(n - (d : ℤ) * ((d : ℤ) - 2))) using 1;
      push_cast; ring_nf
  · convert principalFaddeev_den_ne_zero d hd (z / ρ) (by simpa using hz₁)
      0 (-(min (1 - (d : ℤ)) 0)) using 1; push_cast; ring_nf
  · convert principalFaddeev_den_ne_zero d hd (z / ρ) (by simpa using hz₁)
      (max (-1 : ℤ) 0) (-(1 - (d : ℤ))) using 1; push_cast; ring_nf
  · convert principalFaddeev_den_ne_zero d hd z hz m (-(min (-1 : ℤ) 0))
      using 1; push_cast; ring_nf

/-- For nonreal `z`, the `ρ_d` lattice shift of
[RW26, Radchenko, Wheeler (2026), Section 2.2] follows from
`principalFaddeev_add_principalRoot`. -/
theorem principalFaddeev_add_principalRoot_of_im_ne_zero (hd : 3 < d)
    (m n : ℤ) (z : ℂ) (hz : z.im ≠ 0) :
    principalFaddeev d m n (z + ρ) =
      principalFaddeev d (m + 1) (n + 1 - (d : ℤ)) z := by
  have hz₂ := principalFaddeev_div_im_ne_zero d hd z hz 2
  have hz₁ := principalFaddeev_div_im_ne_zero d hd z hz 1
  apply principalFaddeev_add_principalRoot d hd m n z
  · convert principalFaddeev_den_ne_zero d hd (z / ρ ^ 2) hz₂
      (max (-1 : ℤ) 0) (-(n + 1 - (d : ℤ))) using 1; push_cast; ring_nf
  · convert principalFaddeev_den_ne_zero d hd (z / ρ) (by simpa using hz₁)
      0 (-(min (-1 : ℤ) 0)) using 1; push_cast; ring_nf

/-- For nonreal `z`, the left index shift of
[RW26, Radchenko, Wheeler (2026), Section 2.2] follows from
`principalFaddeev_index_add_one_left`. -/
theorem principalFaddeev_index_add_one_left_of_im_ne_zero (hd : 3 < d)
    (m n : ℤ) (z : ℂ) (hz : z.im ≠ 0) :
    principalFaddeev d (m + 1) n z *
        (1 - Complex.exp (2 * Real.pi * Complex.I * (z + m * ρ))) =
      principalFaddeev d m n z := by
  apply principalFaddeev_index_add_one_left d hd m n z
  convert principalFaddeev_den_ne_zero d hd z hz (m + 1) 0 using 1;
    push_cast; ring_nf

/-- For nonreal `z`, the right index shift of
[RW26, Radchenko, Wheeler (2026), Section 2.2] follows from
`principalFaddeev_index_add_one_right`. -/
theorem principalFaddeev_index_add_one_right_of_im_ne_zero (hd : 3 < d)
    (m n : ℤ) (z : ℂ) (hz : z.im ≠ 0) :
    principalFaddeev d m (n + 1) z =
      (1 - Complex.exp (2 * Real.pi * Complex.I *
        (z / (principalJacobiFactor d : ℂ) + n * ρ))) *
          principalFaddeev d m n z := by
  have hz₂ := principalFaddeev_div_im_ne_zero d hd z hz 2
  apply principalFaddeev_index_add_one_right d hd m n z
  convert principalFaddeev_den_ne_zero d hd (z / ρ ^ 2) hz₂ 0 (-n)
    using 1; push_cast; ring_nf

end PrincipalFaddeevPaths

/-! ### Identities of meromorphic germs

The pointwise identities hold off the real axis. Both sides are meromorphic on the
complex plane, so the identity principle extends equality to every punctured germ.
-/

/-- Nonreal points form a punctured neighborhood of `i`; used by the meromorphic
germ identities for the principal Faddeev product. -/
private lemma principalFaddeev_im_ne_zero_eventually :
    ∀ᶠ w in 𝓝[≠] (Complex.I : ℂ), w.im ≠ 0 := by
  have hi : Complex.I.im ≠ 0 := by simp
  exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
    (Complex.continuous_im.continuousAt.eventually_ne hi)

/-- The germ form of `principalFaddeev_add_one`, the unit lattice shift of
[RW26, Radchenko, Wheeler (2026), Section 2.2]. -/
theorem principalFaddeev_add_one_eventuallyEq (d : ℕ) (hd : 3 < d)
    (m n : ℤ) (z : ℂ) :
    (fun w => principalFaddeev d m n (w + 1)) =ᶠ[𝓝[≠] z]
      (fun w => principalFaddeev d m (n - (d : ℤ) * ((d : ℤ) - 2)) w) := by
  refine MeromorphicOn.eventuallyEq_nhdsNE_of_isPreconnected
    (U := Set.univ) (x := Complex.I) (y := z) ?_ ?_ isPreconnected_univ
    (Set.mem_univ _) (Set.mem_univ _) ?_
  · intro w _
    exact (meromorphicAt_principalFaddeev d hd m n (w + 1)).comp_analyticAt
      (g := fun u : ℂ => u + 1) (by fun_prop)
  · intro w _
    exact meromorphicAt_principalFaddeev d hd m
      (n - (d : ℤ) * ((d : ℤ) - 2)) w
  · filter_upwards [principalFaddeev_im_ne_zero_eventually] with w hw
    exact principalFaddeev_add_one_of_im_ne_zero d hd m n w hw

/-- The germ form of `principalFaddeev_add_principalRoot`, the `ρ_d`
lattice shift of [RW26, Radchenko, Wheeler (2026), Section 2.2]. -/
theorem principalFaddeev_add_principalRoot_eventuallyEq
    (d : ℕ) (hd : 3 < d) (m n : ℤ) (z : ℂ) :
    (fun w => principalFaddeev d m n (w + principalRoot d)) =ᶠ[𝓝[≠] z]
      (fun w => principalFaddeev d (m + 1) (n + 1 - (d : ℤ)) w) := by
  refine MeromorphicOn.eventuallyEq_nhdsNE_of_isPreconnected
    (U := Set.univ) (x := Complex.I) (y := z) ?_ ?_ isPreconnected_univ
    (Set.mem_univ _) (Set.mem_univ _) ?_
  · intro w _
    exact (meromorphicAt_principalFaddeev d hd m n
      (w + principalRoot d)).comp_analyticAt
        (g := fun u : ℂ => u + principalRoot d) (by fun_prop)
  · intro w _
    exact meromorphicAt_principalFaddeev d hd (m + 1)
      (n + 1 - (d : ℤ)) w
  · filter_upwards [principalFaddeev_im_ne_zero_eventually] with w hw
    exact principalFaddeev_add_principalRoot_of_im_ne_zero d hd m n w hw

/-- The germ form of `principalFaddeev_index_add_one_left`, the left index
shift of [RW26, Radchenko, Wheeler (2026), Section 2.2]. -/
theorem principalFaddeev_index_add_one_left_eventuallyEq
    (d : ℕ) (hd : 3 < d) (m n : ℤ) (z : ℂ) :
    (fun w => principalFaddeev d (m + 1) n w *
      (1 - Complex.exp (2 * Real.pi * Complex.I *
        (w + m * (principalRoot d : ℂ))))) =ᶠ[𝓝[≠] z]
      (fun w => principalFaddeev d m n w) := by
  refine MeromorphicOn.eventuallyEq_nhdsNE_of_isPreconnected
    (U := Set.univ) (x := Complex.I) (y := z) ?_ ?_ isPreconnected_univ
    (Set.mem_univ _) (Set.mem_univ _) ?_
  · intro w _
    have hf : AnalyticAt ℂ (fun u : ℂ => 1 - Complex.exp
        (2 * Real.pi * Complex.I * (u + m * (principalRoot d : ℂ)))) w := by fun_prop
    exact (meromorphicAt_principalFaddeev d hd (m + 1) n w).mul
      hf.meromorphicAt
  · intro w _
    exact meromorphicAt_principalFaddeev d hd m n w
  · filter_upwards [principalFaddeev_im_ne_zero_eventually] with w hw
    exact principalFaddeev_index_add_one_left_of_im_ne_zero d hd m n w hw

/-- The germ form of `principalFaddeev_index_add_one_right`, the right index
shift of [RW26, Radchenko, Wheeler (2026), Section 2.2]. -/
theorem principalFaddeev_index_add_one_right_eventuallyEq
    (d : ℕ) (hd : 3 < d) (m n : ℤ) (z : ℂ) :
    (fun w => principalFaddeev d m (n + 1) w) =ᶠ[𝓝[≠] z]
      (fun w => (1 - Complex.exp (2 * Real.pi * Complex.I *
        (w / (principalJacobiFactor d : ℂ) + n * (principalRoot d : ℂ)))) *
          principalFaddeev d m n w) := by
  refine MeromorphicOn.eventuallyEq_nhdsNE_of_isPreconnected
    (U := Set.univ) (x := Complex.I) (y := z) ?_ ?_ isPreconnected_univ
    (Set.mem_univ _) (Set.mem_univ _) ?_
  · intro w _
    exact meromorphicAt_principalFaddeev d hd m (n + 1) w
  · intro w _
    have hf : AnalyticAt ℂ (fun u : ℂ => 1 - Complex.exp
        (2 * Real.pi * Complex.I *
          (u / (principalJacobiFactor d : ℂ) + n * (principalRoot d : ℂ)))) w := by
      fun_prop
    exact hf.meromorphicAt.mul (meromorphicAt_principalFaddeev d hd m n w)
  · filter_upwards [principalFaddeev_im_ne_zero_eventually] with w hw
    exact principalFaddeev_index_add_one_right_of_im_ne_zero d hd m n w hw

end SIC

end
