/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.QPochhammer.Divisor

/-!
# The two q-products in Shintani's double sine

Shintani's two entire q-products, their shifts, their zero divisors, and the simplicity of the
zeros of the first.

This file follows [95, Shintani (1977), Proposition 5 and its proof on p. 181], specializing
its products to periods `(1,τ)` with `Im τ > 0`. The q-Pochhammer factor equations give their
four shifts. Their factors identify the exact zero sets. The general q-Pochhammer first-factor
calculation and lattice derivative theorem give simplicity for the first product.

These products supply the quotient normalized by Dedekind eta in
`SICs.SpecialFunctions.DoubleSine.ShintaniProduct`. They are entire functions in their argument;
a quotient of their pointwise values alone does not cancel common zeros.
-/

noncomputable section

open Complex Real Set

namespace SIC

/-! ### The two products in Shintani's proof

The first product is the general q-Pochhammer product, so its integer shift and divisor
results apply directly. The second is the same product after an affine change of variable.
-/

/-- Shintani's first product after specializing `(ω₁,ω₂) = (1,tau)`:

```text
f₁(z,tau) = ∏_{n≥0} (1 - exp(2πi(z + n tau))).
```

Shintani's `f₁` and `f₂` are functions of `z` at a fixed pair of periods, and this specialization
keeps that reading: results below carry `0 < tau.im`, matching the hypothesis of
[95, Shintani (1977), Proposition 5 on p. 181], and the `tprod` value at other moduli is Lean's
totalization. -/
@[source "95, Proposition 5, p. 181 (f₁, periods (1, τ))" (symbol := "f₁(z, ω)")]
noncomputable def shintaniF1 (z tau : ℂ) : ℂ :=
  qPochhammer z tau

/-- Shintani's second product after specializing `(ω₁,ω₂) = (1,tau)`:

```text
f₂(z,tau) = ∏_{n≥1} (1 - exp(2πi(z-n)/tau)).
```

Its index starts at `1`, so it is the `qPochhammer` tail based at `(z-1)/tau` with
modulus `-1/tau`.

Shintani's `f₁` and `f₂` are functions of `z` at a fixed pair of periods, and this specialization
keeps that reading: results below carry `0 < tau.im`, matching the hypothesis of
[95, Shintani (1977), Proposition 5 on p. 181], and the `tprod` value at other moduli is Lean's
totalization. -/
@[source "95, Proposition 5, p. 181 (f₂, periods (1, τ))" (symbol := "f₂(z, ω)")]
noncomputable def shintaniF2 (z tau : ℂ) : ℂ :=
  qPochhammer ((z - 1) / tau) (-1 / tau)

/-- Shintani's first product is `1`-periodic:
`f₁(z+1,tau) = f₁(z,tau)`.  This is the first of its two difference equations in
[95, Shintani (1977), proof of Proposition 5 on p. 181]. -/
lemma shintaniF1_add_one (z tau : ℂ) :
    shintaniF1 (z + 1) tau = shintaniF1 z tau := by
  simpa only [shintaniF1, Int.cast_one] using qPochhammer_add_intCast z tau 1

/-- Shintani's first product satisfies
`f₁(z+tau,tau) (1-exp(2πiz)) = f₁(z,tau)`.  This is the second of its difference equations
in [95, Shintani (1977), proof of Proposition 5 on p. 181]. -/
lemma shintaniF1_add_tau (z tau : ℂ) (htau : 0 < tau.im) :
    shintaniF1 (z + tau) tau * (1 - Complex.exp (2 * π * I * z)) =
      shintaniF1 z tau := by
  have h := qPochhammerFin_natCast_mul_qPochhammer_add 1 z tau htau
  simp [qPochhammerFin] at h
  simpa [shintaniF1, mul_comm] using h

/-- Shintani's second product satisfies
`f₂(z+1,tau) = (1-exp(2πiz/tau)) f₂(z,tau)`.  This is the first of its two difference
equations in [95, Shintani (1977), proof of Proposition 5 on p. 181]. -/
lemma shintaniF2_add_one (z tau : ℂ) (htau : 0 < tau.im) :
    shintaniF2 (z + 1) tau =
      (1 - Complex.exp (2 * π * I * (z / tau))) * shintaniF2 z tau := by
  have hinv := neg_one_div_im_pos tau htau
  have h := qPochhammerFin_natCast_mul_qPochhammer_add
    1 (z / tau) (-1 / tau) hinv
  simp [qPochhammerFin] at h
  unfold shintaniF2
  convert h.symm using 1 <;> ring_nf

/-- Shintani's second product is `tau`-periodic:
`f₂(z+tau,tau) = f₂(z,tau)`.  This is the second of its two difference equations in
[95, Shintani (1977), proof of Proposition 5 on p. 181]. -/
lemma shintaniF2_add_tau (z tau : ℂ) (htau : 0 < tau.im) :
    shintaniF2 (z + tau) tau = shintaniF2 z tau := by
  have hinv := neg_one_div_im_pos tau htau
  unfold shintaniF2
  have h := qPochhammer_add_intCast_mul_add_intCast
    ((z - 1) / tau) (-1 / tau) hinv 0 1 (by simp [qPochhammerFin])
  have htaune : tau ≠ 0 := fun hzero => by simp [hzero] at htau
  have hbase : (z + tau - 1) / tau = (z - 1) / tau + 1 := by
    field_simp
    ring
  rw [hbase]
  simpa [qPochhammerFin] using h

/-! #### Analyticity and zero sets of the two products -/

/-- For an upper-half-plane modulus, Shintani's first product is entire in `z`.  This is the
analytic assertion preceding the divisor calculation in [95, Shintani (1977), proof of
Proposition 5 on p. 181]. -/
lemma shintaniF1_differentiable (tau : ℂ) (htau : 0 < tau.im) :
    Differentiable ℂ (fun z => shintaniF1 z tau) := by
  simpa only [shintaniF1] using qPochhammer_differentiable tau htau

/-- For an upper-half-plane modulus, Shintani's second product is entire in `z`.  This is the
analytic assertion preceding the divisor calculation in [95, Shintani (1977), proof of
Proposition 5 on p. 181]. -/
lemma shintaniF2_differentiable (tau : ℂ) (htau : 0 < tau.im) :
    Differentiable ℂ (fun z => shintaniF2 z tau) := by
  have hinv := neg_one_div_im_pos tau htau
  unfold shintaniF2
  exact (qPochhammer_differentiable (-1 / tau) hinv).comp (by fun_prop)

/-- The zeros of Shintani's first product are exactly

```text
z = k - n tau,    k ∈ ℤ, n ≥ 0.
```

This is the first divisor statement in [95, Shintani (1977), proof of Proposition 5 on p. 181].
Simplicity at every zero is recorded in `shintaniF1_deriv_ne_zero_of_eq_zero`. -/
lemma shintaniF1_eq_zero_iff (z tau : ℂ) (htau : 0 < tau.im) :
    shintaniF1 z tau = 0 ↔
      ∃ n : ℕ, ∃ k : ℤ, z = k - n * tau := by
  simpa only [shintaniF1] using qPochhammer_eq_zero_iff z tau htau

/-- The zeros of Shintani's second product are exactly

```text
z = n + k tau,    n ≥ 1, k ∈ ℤ.
```

This is the second divisor statement in [95, Shintani (1977), proof of Proposition 5 on p. 181]. -/
lemma shintaniF2_eq_zero_iff (z tau : ℂ) (htau : 0 < tau.im) :
    shintaniF2 z tau = 0 ↔
      ∃ n : ℕ, ∃ k : ℤ, z = (n + 1 : ℕ) + k * tau := by
  have hinv := neg_one_div_im_pos tau htau
  have htau0 : tau ≠ 0 := fun hzero => by simp [hzero] at htau
  rw [shintaniF2, qPochhammer_eq_zero_iff _ _ hinv]
  constructor
  · rintro ⟨n, k, h⟩
    refine ⟨n, k, ?_⟩
    field_simp [htau0] at h
    push_cast at h ⊢
    linear_combination h
  · rintro ⟨n, k, h⟩
    refine ⟨n, k, ?_⟩
    subst z
    field_simp [htau0]
    push_cast
    ring

/-- Outside the period lattice `ℤ + ℤ tau`, Shintani's first product is nonzero.
This specializes `shintaniF1_eq_zero_iff` to the domain needed for pointwise boundary
comparison at nonintegral characteristics. -/
lemma shintaniF1_ne_zero_of_not_mem_lattice (z tau : ℂ) (htau : 0 < tau.im)
    (hz : ∀ m n : ℤ, z ≠ m + n * tau) : shintaniF1 z tau ≠ 0 := by
  intro hzero
  obtain ⟨n, k, hk⟩ := (shintaniF1_eq_zero_iff z tau htau).mp hzero
  apply hz k (-n)
  simpa only [Int.cast_neg, Int.cast_natCast, neg_mul, sub_eq_add_neg] using hk

/-- Outside the period lattice `ℤ + ℤ tau`, Shintani's second product is nonzero.
This specializes `shintaniF2_eq_zero_iff` and excludes both poles and removable common
zeros of the raw product quotient. -/
lemma shintaniF2_ne_zero_of_not_mem_lattice (z tau : ℂ) (htau : 0 < tau.im)
    (hz : ∀ m n : ℤ, z ≠ m + n * tau) : shintaniF2 z tau ≠ 0 := by
  intro hzero
  obtain ⟨n, k, hk⟩ := (shintaniF2_eq_zero_iff z tau htau).mp hzero
  exact hz (n + 1) k (by exact_mod_cast hk)

/-- Shintani's first product vanishes at the origin.  It is the `n = k = 0` point of its
divisor. -/
lemma shintaniF1_zero (tau : ℂ) :
    shintaniF1 0 tau = 0 := by
  simpa only [shintaniF1] using qPochhammer_zero tau

/-- The value `f₂(0,tau)` is nonzero, as zero is outside the second product's divisor. -/
lemma shintaniF2_zero_ne_zero (tau : ℂ) (htau : 0 < tau.im) :
    shintaniF2 0 tau ≠ 0 := by
  rw [ne_eq, shintaniF2_eq_zero_iff 0 tau htau, not_exists]
  intro n
  rw [not_exists]
  intro k h
  have him := congrArg Complex.im h
  simp only [Complex.natCast_im, Complex.add_im, zero_add, Complex.mul_im,
    Complex.intCast_re, Complex.intCast_im, zero_mul, add_zero] at him
  have hk : k = 0 := by
    have hkR : (k : ℝ) = 0 := (mul_eq_zero.mp him.symm).resolve_right htau.ne'
    exact_mod_cast hkR
  subst k
  have hre := congrArg Complex.re h
  norm_num [Complex.mul_re] at hre
  have hnpos : (0 : ℝ) < n + 1 := by positivity
  linarith

/-- **The derivative of Shintani's first product at the origin**:

```text
f₁'(0,tau) = -2πi f₁(tau,tau).
```

This is the first-order product calculation used in [95, Shintani (1977), proof of
Proposition 5 on p. 181] to evaluate `lim (f₁(z,tau) / z)`. -/
lemma shintaniF1_hasDerivAt_zero (tau : ℂ) (htau : 0 < tau.im) :
    HasDerivAt (fun z => shintaniF1 z tau)
      (-2 * π * I * shintaniF1 tau tau) 0 := by
  simpa only [shintaniF1] using qPochhammer_hasDerivAt_zero tau htau

/-! #### Multiplicities of the product zeros

Shintani's proof of Proposition 5 cancels divisors with multiplicity. The general
q-Pochhammer theorem obtains the first product's simple lattice zeros by splitting
off the factor that vanishes.
-/

/-- Every zero of `f₁` has nonzero derivative, by
`qPochhammer_deriv_ne_zero_of_eq_zero`. -/
lemma shintaniF1_deriv_ne_zero_of_eq_zero (z tau : ℂ) (htau : 0 < tau.im)
    (hz : shintaniF1 z tau = 0) : deriv (fun w => shintaniF1 w tau) z ≠ 0 := by
  simpa only [shintaniF1] using qPochhammer_deriv_ne_zero_of_eq_zero z tau htau hz

end SIC

end
