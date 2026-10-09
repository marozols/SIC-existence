/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Canonical Roots of Unity for SIC Constructions

The canonical phases `ω_d`, `ξ_d`.

This file packages the two complex phases used throughout the Weyl--Heisenberg and ghost/live
constructions:

- `standardRoot d`, the primitive root `ω_d = exp (2πi/d)`;
- `displacementPhase d`, the primitive displacement phase `ξ_d = -exp (πi/d)` of order
  `dbar d`;
- `omegaFin d`, the resulting additive character on `Fin d`.

The definitions follow [AFK25, Definition 1.5, `def:WHGroup`]. General facts about complex roots of
unity come from Mathlib; this file records the consequences specific to the conventions of [AFK25].

## References

- [AFK25] Appleby, Flammia, Kopp, arXiv:2501.03970v2, Definition 1.5
- [5, Appleby (2007)] *Symmetric informationally complete measurements of
  arbitrary rank*, arXiv:quant-ph/0611260
-/

noncomputable section

namespace SIC

/-! ### The phase order `dbar`

The displacement phase has order `d` in odd dimensions and `2d` in even dimensions.  The basic
divisibility lemmas here make that parity convention available without repeated case splits. -/

/-- `dbar d` is `d` if `d` is odd and `2d` if `d` is even. It is the order of the displacement
phase `ξ_d`; see [AFK25, Definition 1.5, `def:WHGroup`]. -/
def dbar (d : ℕ) : ℕ := if d % 2 = 1 then d else 2 * d

/-- The dimension `d` divides `dbar d`; the quotient is one in odd dimensions and two in even
dimensions. -/
lemma dvd_dbar (d : ℕ) : d ∣ dbar d := by
  rw [dbar]
  split_ifs <;> simp

/-- `dbar d` divides `2d`: it equals `d` in odd dimensions and `2d` in even dimensions. Together
with `dvd_dbar` this pins `dbar d` between `d` and `2d`. -/
lemma dbar_dvd_two_mul (d : ℕ) : dbar d ∣ 2 * d := by
  rw [dbar]
  split_ifs
  · exact Dvd.intro 2 (Nat.mul_comm d 2)
  · exact dvd_rfl

/-- In odd dimensions `dbar d = d`. -/
lemma dbar_of_odd {d : ℕ} (hd : Odd d) : dbar d = d := by
  rw [dbar, ite_eq_left (Nat.odd_iff.mp hd)]

/-- In even dimensions `dbar d = 2d`. -/
lemma dbar_of_even {d : ℕ} (hd : Even d) : dbar d = 2 * d := by
  rw [dbar, ite_eq_right (by simp [Nat.even_iff.mp hd])]

/-- The phase order `dbar d` is nonzero whenever the dimension `d` is nonzero. -/
lemma dbar_ne_zero (d : ℕ) [NeZero d] : dbar d ≠ 0 := by
  have hd := NeZero.ne d
  unfold dbar
  split <;> omega

/-- The phase order `dbar d` is a nonzero dimension whenever `d` is, so instances needing
`NeZero (dbar d)` do not need to derive it by hand at every use site. -/
instance instNeZeroDbar (d : ℕ) [NeZero d] : NeZero (dbar d) := ⟨dbar_ne_zero d⟩

/-! ### The canonical phases

The roots `ω_d` and `ξ_d` implement the phase conventions of [AFK25, Definition 1.5,
`def:WHGroup`].  Their primitive-root, power, and norm identities drive the later
Weyl--Heisenberg calculations. -/

/-- The primitive `d`-th root of unity `ω_d = exp (2πi/d)`, used in the phase operator and the
Weyl--Heisenberg commutation relation; see [AFK25, Definition 1.5, `def:WHGroup`]. -/
def standardRoot (d : ℕ) [_hd : NeZero d] : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / (d : ℂ))

/-- The displacement phase `ξ_d = -exp (πi/d)`. This is often called `τ_d` in the SIC literature;
the Lean name `displacementPhase` avoids conflict with the modular variable `τ` and follows the
convention of [AFK25, Definition 1.5, `def:WHGroup`]. -/
def displacementPhase (d : ℕ) [_hd : NeZero d] : ℂ :=
  -(Complex.exp (Real.pi * Complex.I / (d : ℂ)))

/-- `standardRoot d` is a primitive `d`-th root of unity. -/
lemma standardRoot_isPrimitiveRoot (d : ℕ) [NeZero d] : IsPrimitiveRoot (standardRoot d) d := by
  rw [standardRoot]
  exact Complex.isPrimitiveRoot_exp d (NeZero.ne d)

/-- `standardRoot d` is a `d`-th root of unity. -/
lemma standardRoot_pow_d (d : ℕ) [NeZero d] : standardRoot d ^ d = 1 :=
  (standardRoot_isPrimitiveRoot d).pow_eq_one

/-- Natural powers of `standardRoot d` depend only on the exponent modulo `d`. -/
lemma standardRoot_pow_mod (d : ℕ) [NeZero d] (n : ℕ) :
    standardRoot d ^ (n % d) = standardRoot d ^ n :=
  pow_eq_pow_of_modEq (Nat.mod_modEq n d) (standardRoot_pow_d d)

/-- The displacement phase satisfies `ξ_d² = ω_d`. -/
@[simp] lemma displacementPhase_sq (d : ℕ) [NeZero d] :
    displacementPhase d ^ 2 = standardRoot d := by
  simp only [displacementPhase, standardRoot, neg_sq, ← Complex.exp_nat_mul]
  congr 1
  ring

/-- The `d`-th power of the displacement phase is the parity sign governing changes of integer
representatives. -/
lemma displacementPhase_pow_d (d : ℕ) [NeZero d] :
    displacementPhase d ^ d = (-1 : ℂ) ^ (d + 1) := by
  rw [displacementPhase, neg_pow, ← Complex.exp_nat_mul]
  rw [show (d : ℂ) * (Real.pi * Complex.I / (d : ℂ)) = Real.pi * Complex.I by
    field_simp [show (d : ℂ) ≠ 0 by exact_mod_cast NeZero.ne d]]
  rw [Complex.exp_pi_mul_I, pow_succ]

/-- The phase `ξ_d` as a single complex exponential, folding `-1 = exp(πi)` into its exponent. -/
lemma displacementPhase_eq_exp (d : ℕ) [NeZero d] :
    displacementPhase d = Complex.exp (Real.pi * Complex.I + Real.pi * Complex.I / d) := by
  rw [displacementPhase, neg_eq_neg_one_mul, ← Complex.exp_pi_mul_I, ← Complex.exp_add]

/-- Integer multiples of `d` in the exponent of `ξ_d` give the standard parity sign. -/
lemma displacementPhase_zpow_d_mul (d : ℕ) [NeZero d] (k : ℤ) :
    displacementPhase d ^ ((d : ℤ) * k) = (-1 : ℂ) ^ (((d + 1 : ℕ) : ℤ) * k) := by
  rw [_root_.zpow_mul, zpow_natCast, displacementPhase_pow_d, ← zpow_natCast, _root_.zpow_mul]

/-- The phase `ξ_d` raised to a multiple of `d²` is one, since `d(d + 1)` is even. -/
lemma displacementPhase_zpow_d_sq_mul (d : ℕ) [NeZero d] (k : ℤ) :
    displacementPhase d ^ ((d : ℤ) * ((d : ℤ) * k)) = 1 := by
  rw [show (d : ℤ) * ((d : ℤ) * k) = (d : ℤ) * ((d : ℤ) * k) from rfl, displacementPhase_zpow_d_mul]
  refine Even.neg_one_zpow ?_
  have hd : Even ((d : ℤ) * ((d : ℤ) + 1)) := Int.even_mul_succ_self _
  obtain ⟨m, hm⟩ := hd
  refine ⟨m * k, ?_⟩
  push_cast
  linear_combination k * hm

/-- The phase `ξ_d` is a `(2d)`-th root of unity. -/
lemma displacementPhase_pow_two_d (d : ℕ) [NeZero d] : displacementPhase d ^ (2 * d) = 1 := by
  rw [pow_mul, displacementPhase_sq, standardRoot_pow_d]

/-- The displacement phase `ξ_d` is a `dbar d`-th root of unity, as specified in
[AFK25, Definition 1.5, `def:WHGroup`]. -/
lemma displacementPhase_pow_dbar (d : ℕ) [NeZero d] : displacementPhase d ^ dbar d = 1 := by
  rw [dbar]
  split_ifs with hd
  · rw [displacementPhase_pow_d]
    exact (Nat.odd_iff.mpr hd).add_one.neg_one_pow
  · exact displacementPhase_pow_two_d d

/-- The phase `ξ_d` is a primitive `dbar d`-th root of unity.

This strengthens the source-level power identity `displacementPhase_pow_dbar` and lets later
Galois arguments represent every automorphic image of `ξ_d` by a unique coprime exponent. -/
lemma displacementPhase_isPrimitiveRoot (d : ℕ) [NeZero d] :
    IsPrimitiveRoot (displacementPhase d) (dbar d) := by
  rcases Nat.even_or_odd d with hd | hd
  · rw [dbar_of_even hd]
    have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
    have hcop : Nat.Coprime (d + 1) (2 * d) := by
      have h1 : Nat.gcd (d + 1) (2 * d) ∣ d + 1 := Nat.gcd_dvd_left _ _
      have h2 : Nat.gcd (d + 1) (2 * d) ∣ 2 * d := Nat.gcd_dvd_right _ _
      have h3 : Nat.gcd (d + 1) (2 * d) ∣ 2 := by
        have h := Nat.dvd_sub (h1.mul_left 2) h2
        rwa [show 2 * (d + 1) - 2 * d = 2 by omega] at h
      obtain ⟨k, hk⟩ := hd
      rcases (Nat.dvd_prime Nat.prime_two).mp h3 with h | h
      · exact h
      · exfalso; rw [h] at h1; omega
    have hxi : displacementPhase d =
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((2 * d : ℕ) : ℂ)) ^ (d + 1) := by
      rw [← Complex.exp_nat_mul, displacementPhase,
        show ((d + 1 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / ((2 * d : ℕ) : ℂ)) =
          (Real.pi : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I / (d : ℂ) by
          push_cast; field_simp,
        Complex.exp_add, Complex.exp_pi_mul_I]
      ring
    rw [hxi]
    exact (Complex.isPrimitiveRoot_exp (2 * d) (by simpa using NeZero.ne d)).pow_of_coprime _ hcop
  · rw [dbar_of_odd hd]
    obtain ⟨m, hm⟩ := hd
    have hxi : displacementPhase d = standardRoot d ^ (m + 1) := by
      rw [← displacementPhase_sq, ← pow_mul, show 2 * (m + 1) = d + 1 by omega,
        pow_succ, displacementPhase_pow_d,
        (by exact ⟨m + 1, by omega⟩ : Even (d + 1)).neg_one_pow, one_mul]
    have hcop : Nat.Coprime (m + 1) d := by
      refine Nat.dvd_one.mp ?_
      have h2 := Nat.dvd_sub ((Nat.gcd_dvd_left (m + 1) d).mul_left 2)
        (Nat.gcd_dvd_right (m + 1) d)
      rwa [show 2 * (m + 1) - d = 1 by omega] at h2
    rw [hxi]
    exact (standardRoot_isPrimitiveRoot d).pow_of_coprime _ hcop

/-- The primitive root `standardRoot d` lies on the complex unit circle. -/
@[simp] lemma norm_standardRoot (d : ℕ) [NeZero d] : ‖standardRoot d‖ = 1 :=
  (standardRoot_isPrimitiveRoot d).norm'_eq_one (NeZero.ne d)

/-- The displacement phase `displacementPhase d` lies on the complex unit circle. -/
@[simp] lemma norm_displacementPhase (d : ℕ) [NeZero d] : ‖displacementPhase d‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one (displacementPhase_pow_two_d d)
    (mul_ne_zero (by norm_num) (NeZero.ne d))

/-- The displacement phase `displacementPhase d` is nonzero. -/
lemma displacementPhase_ne_zero (d : ℕ) [NeZero d] : displacementPhase d ≠ 0 := by
  simp [displacementPhase]

/-- The primitive root `standardRoot d` is nonzero. -/
lemma standardRoot_ne_zero (d : ℕ) [NeZero d] : standardRoot d ≠ 0 := by
  rw [standardRoot]
  exact Complex.exp_ne_zero _

/-- Integer powers of `ω_d` agree when their exponents differ by a multiple of `d`. -/
lemma standardRoot_zpow_eq_of_dvd_sub {d : ℕ} [NeZero d] {a b : ℤ}
    (h : (d : ℤ) ∣ a - b) : standardRoot d ^ a = standardRoot d ^ b := by
  obtain ⟨t, ht⟩ := h
  have hab : a = b + (d : ℤ) * t := by linarith
  rw [hab, zpow_add₀ (standardRoot_ne_zero d), _root_.zpow_mul, zpow_natCast, standardRoot_pow_d,
    _root_.one_zpow, mul_one]

/-- A `dbar d`-divisible integer exponent gives the trivial `ξ_d` phase. -/
lemma displacementPhase_zpow_eq_one_of_dbar_dvd {d : ℕ} [NeZero d]
    {a : ℤ} (ha : (dbar d : ℤ) ∣ a) : displacementPhase d ^ a = 1 := by
  obtain ⟨k, rfl⟩ := ha
  rw [_root_.zpow_mul, zpow_natCast, displacementPhase_pow_dbar, one_zpow]

/-- Integer powers of `ξ_d` agree when their exponents differ by a multiple of `dbar d`. -/
lemma displacementPhase_zpow_eq_of_dbar_dvd_sub {d : ℕ} [NeZero d] {a b : ℤ}
    (h : (dbar d : ℤ) ∣ a - b) : displacementPhase d ^ a = displacementPhase d ^ b := by
  obtain ⟨t, ht⟩ := h
  have hab : a = b + (dbar d : ℤ) * t := by linarith
  rw [hab, zpow_add₀ (displacementPhase_ne_zero d), _root_.zpow_mul, zpow_natCast,
    displacementPhase_pow_dbar,
    _root_.one_zpow, mul_one]

/-- **Moving a multiple of `d` between the exponents of `-1` and `ξ_d`**: since
`ξ_d^{dk} = (-1)^{(d+1)k}`, `(-1)^{s - (d+1)c} ξ_d^{a + du} = (-1)^s ξ_d^a` whenever
`(d+1)(u - c)` is even. This is the parity bookkeeping of the phase identity in the proof of
[AFK25, Theorem 1.45, `thm:ghstExist`]. -/
lemma neg_one_zpow_mul_displacementPhase_zpow_eq (d : ℕ) [NeZero d] (sL sR aL aR c u : ℤ)
    (hs : sL = sR - (d + 1 : ℕ) * c)
    (ha : aL = aR + (d : ℕ) * u)
    (he : Even (((d + 1 : ℕ) : ℤ) * (u - c))) :
    (-1 : ℂ) ^ sL * displacementPhase d ^ aL =
      (-1 : ℂ) ^ sR * displacementPhase d ^ aR := by
  rw [hs, show sR - ((d + 1 : ℕ) : ℤ) * c =
      sR + (-((d + 1 : ℕ) : ℤ) * c) by ring,
    zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ha,
    zpow_add₀ (displacementPhase_ne_zero d), displacementPhase_zpow_d_mul]
  calc
    _ = (-1 : ℂ) ^ sR * displacementPhase d ^ aR *
        ((-1 : ℂ) ^ (-((d + 1 : ℕ) : ℤ) * c) *
          (-1 : ℂ) ^ (((d + 1 : ℕ) : ℤ) * u)) := by ring
    _ = (-1 : ℂ) ^ sR * displacementPhase d ^ aR *
        (-1 : ℂ) ^ (((d + 1 : ℕ) : ℤ) * (u - c)) := by
      rw [show ((d + 1 : ℕ) : ℤ) * (u - c) =
        -((d + 1 : ℕ) : ℤ) * c + ((d + 1 : ℕ) : ℤ) * u by ring,
        zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    _ = _ := by rw [he.neg_one_zpow, mul_one]

/-! ### The additive character on `Fin d`

Evaluating powers of `ω_d` on canonical residues gives the finite additive character.  Its
multiplicativity and orthogonality are the scalar Fourier facts used throughout phase space. -/

/-- The standard additive character of `Fin d` induced by `ω_d`.

This project-local wrapper lets finite phase sums use the additive structure of `Fin d` directly. -/
def omegaFin (d : ℕ) [NeZero d] (x : Fin d) : ℂ :=
  standardRoot d ^ x.val

/-- The powers of `ω_d` with exponents in `Fin d` are distinct. -/
lemma standardRoot_pow_injective (d : ℕ) [NeZero d] :
    Function.Injective (fun i : Fin d => standardRoot d ^ i.val) := by
  intro i j h
  exact Fin.ext ((standardRoot_isPrimitiveRoot d).pow_inj i.isLt j.isLt h)

/-- The finite character `omegaFin` converts addition in `Fin d` into multiplication. -/
lemma omegaFin_add (d : ℕ) [NeZero d] (x y : Fin d) :
    omegaFin d (x + y) = omegaFin d x * omegaFin d y := by
  unfold omegaFin
  rw [Fin.val_add, standardRoot_pow_mod, pow_add]

/-- A product in `Fin d` gives the corresponding product exponent of `ω_d`. -/
lemma omega_pow_mul_eq_omegaFin (d : ℕ) [NeZero d] (x y : Fin d) :
    standardRoot d ^ (x.val * y.val) = omegaFin d (x * y) := by
  unfold omegaFin
  rw [Fin.val_mul, standardRoot_pow_mod]

/-- The finite character `omegaFin` sends additive inverses to multiplicative inverses. -/
lemma omegaFin_neg (d : ℕ) [NeZero d] (x : Fin d) :
    omegaFin d (-x) = (omegaFin d x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← omegaFin_add, add_neg_cancel]
  simp [omegaFin]

/-- Character orthogonality for the powers of `ω_d`. -/
lemma omega_geom_sum (d : ℕ) [NeZero d] (n : Fin d) :
    ∑ j : Fin d, standardRoot d ^ (j.val * n.val) =
      if n = 0 then (d : ℂ) else 0 := by
  split_ifs with h
  · subst n; simp
  · simp_rw [mul_comm _ n.val, pow_mul]
    rw [Fin.sum_univ_eq_sum_range,
      geom_sum_eq (by simpa using (standardRoot_pow_injective d).ne h),
      ← pow_mul, mul_comm n.val d, pow_mul, standardRoot_pow_d,
      one_pow, sub_self, zero_div]

/-- Orthogonality for `omegaFin`: summing `y ↦ omegaFin d (y * x)` vanishes unless `x` is zero. -/
lemma sum_omegaFin_mul (d : ℕ) [NeZero d] (x : Fin d) :
    ∑ y : Fin d, omegaFin d (y * x) = if x = 0 then (d : ℂ) else 0 := by
  simpa only [← omega_pow_mul_eq_omegaFin] using omega_geom_sum d x

end SIC
