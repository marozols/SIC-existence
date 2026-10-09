/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.ResidueKernel
import SICs.SpecialFunctions.Faddeev.FiveTerm.Kernel

/-!
# Telescoping of the principal residue kernels

The sum of the residue kernels on a common line, shifted by `(ε-1)/c`, telescopes to the
difference kernel of the five-term identity at shifted parameters.

This module follows [RW26, Radchenko, Wheeler (2026), Section 3.2, the proof of Theorem 2,
`thm:fg.equs`, the computation of equation (7), `eq:Fgpm.5term`] at `γ = A_d`, `τ = ρ_d`, with
`A_d = [[a, b], [c, 1-d]]`, `ε = ρ_d³`, `q = e(ρ_d)`, and `n = h = 0`.

## The argument

Move every contour to one line: `L(z) = ∑_{m<c} K̃_m(z - mε/c)`. Translating by `(ε-1)/c` sends
the `m`-th summand to a lattice shift of the `m'`-th, where `m + a - 1 = m' + Mc`, `0 ≤ m' < c`:
`-mε/c + (ε-1)/c = -m'ε/c + (aρ_d + b) - Mε`. The shift laws
`Φ_{m,n}(z + aρ_d + b) = Φ_{m+a,n+1}(z)` and `Φ_{m,n}(z + ε) = Φ_{m+c,n}(z)` change the two
products of `K̃_m` to `Φ_{m'+1,1}(z)/Φ_{m'+p+1,1}(z+y)`, the pole factor becomes
`q(e(z/ε) - q^{m'} e(z))` because `e((aρ_d + b)/ε) = q` and `e(aρ_d + b) = q^a`, and the phase
gains the factor `q` through `e(w - w/ε) = q^{1-ℓ}` and `e(ℓ(ρ_d + b + M(d-1))) = q^ℓ`. Hence
`K̃_m(z - mε/c + (ε-1)/c) = (K̃_{m'} B_{m'})(z - m'ε/c)` with the one-step bracket
`B_{m'}(z) = (1 - e(z/ε))(1 - q^{m'+p}e(z+y)) / ((1 - q^{m'}e(z))(1 - e((z+y)/ε)))`.

Since `m ↦ m'` permutes `ℤ/c`, `L(z) - L(z + (ε-1)/c) = ∑_{m'} (K̃_{m'}(1 - B_{m'}))(z - m'ε/c)`,
and `q^p e(y) = e(y/ε)` makes `K̃_{m'}(1 - B_{m'})` the difference kernel
`J_{m'}(z) = (1 - q^p e(y)) Φ_{m'+1,0}(z)/Φ_{m'+p,1}(z+y) · e(phase)`, which is free of the kernel
poles. All identities are identities of germs at every point; on a vertical line they hold
outside a countable set.

The lattice relations `e(w/ε) = e(w + (ℓ-1)ρ_d)` and `e(y/ε) = e(y + pρ_d)` are the
hypotheses `q^ℓ e(w) = q̃ e(w/ε)` and `q^p e(y) = e(y/ε)` of the source, satisfied by
`w = z_u`, `ℓ = u₁ + 1`, `y = z_v`, `p = v₁` (`principalFiveTermLatticeArgument_exp_lower`).
-/

noncomputable section

open Complex Filter Topology MeasureTheory
open scoped MatrixGroups

namespace SIC

/-! ### The bracket and the difference kernel -/

/-- The one-step bracket
`B_m(z) = (1 - e(z/ε))(1 - q^{m+p} e(z+y)) / ((1 - q^m e(z))(1 - e((z+y)/ε)))`
of [RW26, Radchenko, Wheeler (2026), Section 3.2]. -/
def principalFiveTermBracket (d : ℕ) (p : ℤ) (y : ℝ) (m : ℤ) (z : ℂ) : ℂ :=
  (1 - Complex.exp (2 * Real.pi * I * (z / (principalRoot d : ℂ) ^ 3))) *
      (1 - Complex.exp (2 * Real.pi * I * (z + y + (m + p) * (principalRoot d : ℂ)))) /
    ((1 - Complex.exp (2 * Real.pi * I * (z + m * (principalRoot d : ℂ)))) *
      (1 - Complex.exp (2 * Real.pi * I * ((z + y) / (principalRoot d : ℂ) ^ 3))))

/-- The difference kernel
`J_m(z) = (1 - q^p e(y)) Φ_{m+1,0}(z)/Φ_{m+p,1}(z+y) · e(phase_m(z))` of
[RW26, Radchenko, Wheeler (2026), Section 3.2]: the integrand of Theorem 3 at the parameters
`(ℓ, p - a, w, y + aρ_d + b)` times `1 - q^p e(y)`. -/
def principalFiveTermDifferenceKernel (d : ℕ) (ℓ p : ℤ) (w y : ℝ) (m : ℤ) (z : ℂ) : ℂ :=
  (1 - Complex.exp (2 * Real.pi * I * ((y : ℂ) + p * (principalRoot d : ℂ)))) *
    (principalFaddeev d (m + 1) 0 z / principalFaddeev d (m + p) 1 (z + y)) *
      Complex.exp (2 * Real.pi * I * principalFiveTermPhase d ℓ w m z)

/-- The sum `L(z) = ∑_{m<c} K̃_m(z - mε/c)` of the residue kernels moved to a common line. -/
def principalFiveTermResidueSum (d : ℕ) (ℓ p : ℤ) (w y : ℝ) (z : ℂ) : ℂ :=
  ∑ m : FiveTermIndex (principalA d),
    principalFiveTermResidueKernel d ℓ p w y ((m : ℕ) : ℤ)
      (z - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 / ((principalA d) 1 0 : ℂ))

/-- The sum `J(z) = ∑_{m<c} J_m(z - mε/c)` of the difference kernels on the common line. -/
def principalFiveTermDifferenceSum (d : ℕ) (ℓ p : ℤ) (w y : ℝ) (z : ℂ) : ℂ :=
  ∑ m : FiveTermIndex (principalA d),
    principalFiveTermDifferenceKernel d ℓ p w y ((m : ℕ) : ℤ)
      (z - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 / ((principalA d) 1 0 : ℂ))

/-- The two factors in the bracket denominator avoid zero on a punctured germ. -/
private lemma eventually_principalFiveTermBracket_den_ne
    (d : ℕ) (hd : 3 < d) (m : ℤ) (y : ℝ) (z : ℂ) :
    ∀ᶠ ζ in 𝓝[≠] z,
      (1 - Complex.exp (2 * Real.pi * I *
        (ζ + m * (principalRoot d : ℂ))) ≠ 0) ∧
      (1 - Complex.exp (2 * Real.pi * I *
        ((ζ + y) / (principalRoot d : ℂ) ^ 3)) ≠ 0) := by
  let ε : ℂ := (principalRoot d : ℂ) ^ 3
  have hε : ε ≠ 0 := pow_ne_zero 3 (ofReal_principalRoot_ne_zero d hd)
  have hB := eventually_exp_two_pi_I_affine_ne_one_nhdsNE 1
    (m * (principalRoot d : ℂ)) z one_ne_zero
  have hF := eventually_exp_two_pi_I_affine_ne_one_nhdsNE ((1 : ℂ) / ε)
    ((y : ℂ) / ε) z (div_ne_zero one_ne_zero hε)
  filter_upwards [hB, hF] with ζ hBζ hFζ
  constructor
  · exact sub_ne_zero.mpr (by simpa only [one_mul] using hBζ.symm)
  · apply sub_ne_zero.mpr
    convert hFζ.symm using 2; ring

/-- The pole factor `e(ζ/ε) - e(ζ+mρ_d)` avoids zero on every punctured germ; used by the
bracket identity. -/
private lemma eventually_principalFiveTermPoleFactor_ne_zero
    (d : ℕ) (hd : 3 < d) (m : ℤ) (z : ℂ) :
    ∀ᶠ ζ in 𝓝[≠] z, principalFiveTermPoleFactor d m ζ ≠ 0 := by
  let ε : ℂ := (principalRoot d : ℂ) ^ 3
  have hε0 : ε ≠ 0 := pow_ne_zero 3 (ofReal_principalRoot_ne_zero d hd)
  have hε1 : ε ≠ 1 := by
    dsimp [ε]
    exact_mod_cast (ne_of_gt (one_lt_principalRoot_pow_three d hd))
  have hA : (1 : ℂ) / ε - 1 ≠ 0 := by
    intro h
    exact hε1 (((div_eq_one_iff_eq hε0).mp (sub_eq_zero.mp h)).symm)
  have h := eventually_exp_two_pi_I_affine_ne_one_nhdsNE ((1 : ℂ) / ε - 1)
    (-(m : ℂ) * (principalRoot d : ℂ)) z hA
  filter_upwards [h] with ζ hζ
  intro hz
  apply hζ
  have hexp : Complex.exp (2 * Real.pi * I *
      (((1 : ℂ) / ε - 1) * ζ + -(m : ℂ) * (principalRoot d : ℂ))) =
      Complex.exp (2 * Real.pi * I * (ζ / ε)) /
        Complex.exp (2 * Real.pi * I * (ζ + m * (principalRoot d : ℂ))) := by
    rw [← Complex.exp_sub]
    congr 1
    ring
  rw [hexp]
  have heq : Complex.exp (2 * Real.pi * I * (ζ / ε)) =
      Complex.exp (2 * Real.pi * I * (ζ + m * (principalRoot d : ℂ))) :=
    sub_eq_zero.mp hz
  rw [heq, div_self (Complex.exp_ne_zero _)]

/-- Multiplicativity of `e` separates `z+mρ_d` from `y+pρ_d`; used by the bracket identity. -/
private lemma principalFiveTerm_exp_product_left (d : ℕ) (m p : ℤ) (y : ℝ) (z : ℂ) :
    Complex.exp (2 * Real.pi * I * (z + y + (m + p) * (principalRoot d : ℂ))) =
      Complex.exp (2 * Real.pi * I * (z + m * (principalRoot d : ℂ))) *
        Complex.exp (2 * Real.pi * I * ((y : ℂ) + p * (principalRoot d : ℂ))) := by
  rw [← Complex.exp_add]
  congr 1
  ring

/-- The hypothesis on `y` separates `e((z+y)/ε)` into `e(z/ε)e(y+pρ_d)`; used by the
bracket identity. -/
private lemma principalFiveTerm_exp_product_right (d : ℕ) (p : ℤ) (y : ℝ) (z : ℂ)
    (hy : Complex.exp (2 * Real.pi * I * ((y : ℂ) / (principalRoot d : ℂ) ^ 3)) =
      Complex.exp (2 * Real.pi * I * ((y : ℂ) + p * (principalRoot d : ℂ)))) :
    Complex.exp (2 * Real.pi * I * ((z + y) / (principalRoot d : ℂ) ^ 3)) =
      Complex.exp (2 * Real.pi * I * (z / (principalRoot d : ℂ) ^ 3)) *
        Complex.exp (2 * Real.pi * I * ((y : ℂ) + p * (principalRoot d : ℂ))) := by
  rw [← hy, ← Complex.exp_add]
  congr 1
  ring

/-- The principal matrix has `cρ_d+1-d=ε`, `aρ_d+b=ρ_d ε`, and determinant one;
these three identities control the contour shift. -/
private lemma principalFiveTerm_shift_matrix_data (d : ℕ) (hd : 3 < d) :
    let ρ : ℂ := principalRoot d
    let ε : ℂ := ρ ^ 3
    let a : ℂ := (principalA d) 0 0
    let b : ℂ := (principalA d) 0 1
    let c : ℂ := (principalA d) 1 0
    let e : ℂ := (principalA d) 1 1
    ε = c * ρ + e ∧ a * ρ + b = ρ * ε ∧ a * e - b * c = 1 := by
  dsimp
  constructor
  · exact_mod_cast (by simpa [coe_principalA] using (principalRoot_pow_three_eq d hd))
  constructor
  · exact_mod_cast principalA_numerator_principalRoot d hd
  · exact_mod_cast (by simpa only [Matrix.det_fin_two] using det_principalA d)

/-- The determinant-one fixed-point identity gives `a-cρ_d=ε⁻¹`; used in the phase shift. -/
private lemma principalFiveTerm_shift_inverse (d : ℕ) (hd : 3 < d) :
    ((principalA d) 0 0 : ℂ) -
        ((principalA d) 1 0 : ℂ) * (principalRoot d : ℂ) =
      1 / (principalRoot d : ℂ) ^ 3 := by
  let ρ : ℂ := principalRoot d
  let ε : ℂ := ρ ^ 3
  let a : ℂ := (principalA d) 0 0
  let b : ℂ := (principalA d) 0 1
  let c : ℂ := (principalA d) 1 0
  let e : ℂ := (principalA d) 1 1
  have hε0 : ε ≠ 0 := pow_ne_zero 3 (ofReal_principalRoot_ne_zero d hd)
  obtain ⟨hε, hfix, hdet⟩ := principalFiveTerm_shift_matrix_data d hd
  change ε = c * ρ + e at hε
  change a * ρ + b = ρ * ε at hfix
  change a * e - b * c = 1 at hdet
  have hunit : (a - c * ρ) * ε = 1 := by
    calc
      (a - c * ρ) * ε = a * ε - c * (ρ * ε) := by ring
      _ = a * (c * ρ + e) - c * (a * ρ + b) := by rw [← hfix, hε]
      _ = a * e - b * c := by ring
      _ = 1 := hdet
  exact (eq_div_iff hε0).2 hunit

/-- Translating by `aρ_d+b-Mε` changes `Φ_{r,0}` to `Φ_{r+a-Mc,1}` as a germ; this is
`principalFaddeev_add_lattice_eventuallyEq` in the contour coordinates. -/
private lemma principalFiveTermProduct_add_shift_eventuallyEq
    (d : ℕ) (hd : 3 < d) (r M : ℤ) (z : ℂ) :
    (fun ζ => principalFaddeev d r 0
      (ζ + (((principalA d) 0 0 : ℂ) * (principalRoot d : ℂ) +
        ((principalA d) 0 1 : ℂ)) - M * (principalRoot d : ℂ) ^ 3)) =ᶠ[𝓝[≠] z]
      (fun ζ => principalFaddeev d
        (r + (principalA d) 0 0 - M * (principalA d) 1 0) 1 ζ) := by
  obtain ⟨hε, -, -⟩ := principalFiveTerm_shift_matrix_data d hd
  have hidx : (0 : ℤ) + ((principalA d) 0 0 - M * (principalA d) 1 0) *
      (1 - (d : ℤ)) - (d : ℤ) * ((d : ℤ) - 2) *
        ((principalA d) 0 1 + M * ((d : ℤ) - 1)) = 1 := by
    simp [coe_principalA]
    ring
  have h := principalFaddeev_add_lattice_eventuallyEq d hd r 0
    ((principalA d) 0 0 - M * (principalA d) 1 0)
    ((principalA d) 0 1 + M * ((d : ℤ) - 1)) z
  filter_upwards [h] with ζ hζ
  have hshift :
      ζ + (((principalA d) 0 0 : ℂ) * (principalRoot d : ℂ) +
        ((principalA d) 0 1 : ℂ)) - M * (principalRoot d : ℂ) ^ 3 =
      ζ + ((((principalA d) 0 0 - M * (principalA d) 1 0 : ℤ) : ℂ) *
        (principalRoot d : ℂ) +
        (((principalA d) 0 1 + M * ((d : ℤ) - 1) : ℤ) : ℂ)) := by
    push_cast
    have he : ((principalA d) 1 1 : ℂ) = 1 - (d : ℂ) := by simp [coe_principalA]
    rw [hε, he]
    ring
  rw [hshift, hζ, hidx]
  congr 1
  ring

/-- The shifted argument divided by `ε` differs from `z/ε+ρ_d` by the integer `-M`;
used by the shifted pole and phase factors. -/
private lemma principalFiveTermShift_div_argument (d : ℕ) (hd : 3 < d) (M : ℤ) (z : ℂ) :
    (z + (((principalA d) 0 0 : ℂ) * (principalRoot d : ℂ) +
        ((principalA d) 0 1 : ℂ)) - M * (principalRoot d : ℂ) ^ 3) /
      (principalRoot d : ℂ) ^ 3 -
      (z / (principalRoot d : ℂ) ^ 3 + (principalRoot d : ℂ)) = -(M : ℂ) := by
  obtain ⟨-, hfix, -⟩ := principalFiveTerm_shift_matrix_data d hd
  have hS : (((principalA d) 0 0 : ℂ) * (principalRoot d : ℂ) +
      ((principalA d) 0 1 : ℂ)) - M * (principalRoot d : ℂ) ^ 3 =
      ((principalRoot d : ℂ) - M) * (principalRoot d : ℂ) ^ 3 := by
    rw [hfix]
    ring
  rw [show z + (((principalA d) 0 0 : ℂ) * (principalRoot d : ℂ) +
    ((principalA d) 0 1 : ℂ)) - M * (principalRoot d : ℂ) ^ 3 =
      z + ((((principalA d) 0 0 : ℂ) * (principalRoot d : ℂ) +
        ((principalA d) 0 1 : ℂ)) - M * (principalRoot d : ℂ) ^ 3) by ring, hS]
  field_simp [ofReal_principalRoot_ne_zero d hd]
  ring

/-- The shifted argument plus `mρ_d` differs from `z+(m'+1)ρ_d` by the integer
`b+M(d-1)` under the reindexing relation; used by the shifted pole and phase factors. -/
private lemma principalFiveTermShift_add_argument (d : ℕ) (hd : 3 < d) (m m' M : ℤ)
    (hm : m + (principalA d) 0 0 - M * (principalA d) 1 0 = m' + 1) (z : ℂ) :
    (z + (((principalA d) 0 0 : ℂ) * (principalRoot d : ℂ) +
      ((principalA d) 0 1 : ℂ)) - M * (principalRoot d : ℂ) ^ 3 +
        m * (principalRoot d : ℂ)) -
      (z + (m' + 1) * (principalRoot d : ℂ)) =
        (((principalA d) 0 1 + M * ((d : ℤ) - 1) : ℤ) : ℂ) := by
  obtain ⟨hε, -, -⟩ := principalFiveTerm_shift_matrix_data d hd
  have hε' : (principalRoot d : ℂ) ^ 3 =
      ((principalA d) 1 0 : ℂ) * (principalRoot d : ℂ) + 1 - (d : ℂ) := by
    simpa [coe_principalA, sub_eq_add_neg, add_assoc] using hε
  have hmC : (m : ℂ) + ((principalA d) 0 0 : ℂ) -
      M * ((principalA d) 1 0 : ℂ) = (m' : ℂ) + 1 := by exact_mod_cast hm
  push_cast
  linear_combination (principalRoot d : ℂ) * hmC - (M : ℂ) * hε'

/-- The coefficient of `w` in the shifted phase is `1-ε⁻¹`; used by the phase factor. -/
private lemma principalFiveTermShift_phase_coefficient (d : ℕ) (hd : 3 < d) (m m' M : ℤ)
    (hm : m + (principalA d) 0 0 - M * (principalA d) 1 0 = m' + 1) :
    ((principalA d) 1 0 : ℂ) *
      ((((principalA d) 0 0 : ℂ) * (principalRoot d : ℂ) +
        ((principalA d) 0 1 : ℂ)) - M * (principalRoot d : ℂ) ^ 3) /
      (principalRoot d : ℂ) ^ 3 + (m : ℂ) - m' =
      1 - 1 / (principalRoot d : ℂ) ^ 3 := by
  let ρ : ℂ := principalRoot d
  let ε : ℂ := ρ ^ 3
  let a : ℂ := (principalA d) 0 0
  let b : ℂ := (principalA d) 0 1
  let c : ℂ := (principalA d) 1 0
  let S : ℂ := a * ρ + b - M * ε
  have hε0 : ε ≠ 0 := pow_ne_zero 3 (ofReal_principalRoot_ne_zero d hd)
  obtain ⟨-, hfix, -⟩ := principalFiveTerm_shift_matrix_data d hd
  change a * ρ + b = ρ * ε at hfix
  have hac : a - c * ρ = 1 / ε := principalFiveTerm_shift_inverse d hd
  have hS : S = (ρ - M) * ε := by dsimp [S]; rw [hfix]; ring
  have hmC : (m : ℂ) + a - M * c = (m' : ℂ) + 1 := by
    dsimp [a, c]
    exact_mod_cast hm
  change c * S / ε + (m : ℂ) - m' = 1 - 1 / ε
  calc
    c * S / ε + (m : ℂ) - m' = c * (ρ - M) + (m : ℂ) - m' := by
      rw [hS, show c * ((ρ - M) * ε) = (c * (ρ - M)) * ε by ring,
        mul_div_cancel_right₀ _ hε0]
    _ = 1 - (a - c * ρ) := by linear_combination hmC
    _ = 1 - 1 / ε := by rw [hac]

/-- The `ℓ` part of the shifted phase is `ρ_d+b+M(d-1)` after reindexing. -/
private lemma principalFiveTermShift_phase_sum (d : ℕ) (hd : 3 < d) (m m' M : ℤ)
    (hm : m + (principalA d) 0 0 - M * (principalA d) 1 0 = m' + 1) :
    ((((principalA d) 0 0 : ℂ) * (principalRoot d : ℂ) +
      ((principalA d) 0 1 : ℂ)) - M * (principalRoot d : ℂ) ^ 3) +
        ((m : ℂ) - m') * (principalRoot d : ℂ) =
      (principalRoot d : ℂ) +
        (((principalA d) 0 1 + M * ((d : ℤ) - 1) : ℤ) : ℂ) := by
  have h := principalFiveTermShift_add_argument d hd m m' M hm 0
  linear_combination h

/-- The difference of two principal phases under any argument shift is affine in that shift. -/
private lemma principalFiveTermPhase_shift_linear (d : ℕ) (hd : 3 < d)
    (ℓ m m' : ℤ) (w : ℝ) (S z : ℂ) :
    principalFiveTermPhase d ℓ w m (z + S) -
      principalFiveTermPhase d ℓ w m' z =
      (((principalA d) 1 0 : ℂ) * S / (principalRoot d : ℂ) ^ 3 +
        ((m : ℂ) - m')) * w +
        ℓ * (S + ((m : ℂ) - m') * (principalRoot d : ℂ)) := by
  have hε0 : (principalRoot d : ℂ) ^ 3 ≠ 0 :=
    pow_ne_zero 3 (ofReal_principalRoot_ne_zero d hd)
  have hc : ((principalA d) 1 0 : ℂ) =
      (d : ℂ) * ((d : ℂ) - 2) := by simp [coe_principalA]
  rw [hc]
  simp only [principalFiveTermPhase]
  field_simp [hε0, ofReal_principalRoot_ne_zero d hd]
  ring

/-- The shifted phase differs by `w-w/ε+ℓ(ρ_d+b+M(d-1))`; used to compare its exponential. -/
private lemma principalFiveTermPhase_add_shift_argument (d : ℕ) (hd : 3 < d)
    (ℓ m m' M : ℤ) (w : ℝ)
    (hm : m + (principalA d) 0 0 - M * (principalA d) 1 0 = m' + 1)
    (z : ℂ) :
    principalFiveTermPhase d ℓ w m
      (z + (((principalA d) 0 0 : ℂ) * (principalRoot d : ℂ) +
        ((principalA d) 0 1 : ℂ)) - M * (principalRoot d : ℂ) ^ 3) -
        principalFiveTermPhase d ℓ w m' z =
      (w : ℂ) - (w : ℂ) / (principalRoot d : ℂ) ^ 3 +
        ℓ * ((principalRoot d : ℂ) +
          (((principalA d) 0 1 + M * ((d : ℤ) - 1) : ℤ) : ℂ)) := by
  let ρ : ℂ := principalRoot d
  let ε : ℂ := ρ ^ 3
  let c : ℂ := (principalA d) 1 0
  let S : ℂ := ((principalA d) 0 0 : ℂ) * ρ +
    ((principalA d) 0 1 : ℂ) - M * ε
  have hcoeff : c * S / ε + ((m : ℂ) - m') = 1 - 1 / ε := by
    simpa only [← add_sub_assoc] using
      (principalFiveTermShift_phase_coefficient d hd m m' M hm)
  have hsum : S + ((m : ℂ) - m') * ρ =
      ρ + ((principalA d) 0 1 : ℂ) + M * ((d : ℂ) - 1) := by
    convert principalFiveTermShift_phase_sum d hd m m' M hm using 1
    push_cast
    ring
  have hphase := principalFiveTermPhase_shift_linear d hd ℓ m m' w S z
  rw [show z + (((principalA d) 0 0 : ℂ) * (principalRoot d : ℂ) +
      ((principalA d) 0 1 : ℂ)) - M * (principalRoot d : ℂ) ^ 3 = z + S by
    dsimp [S, ρ, ε]; ring]
  rw [hphase, hcoeff, hsum]
  push_cast
  ring

/-- The parameter relation `e(w/ε)=e(w+(ℓ-1)ρ)` turns the nonintegral part of the phase
shift into `e(ρ)`. -/
private lemma principalFiveTerm_phase_exp_base (ρ ε : ℂ) (w : ℝ) (ℓ : ℤ)
    (hw : Complex.exp (2 * Real.pi * I * ((w : ℂ) / ε)) =
      Complex.exp (2 * Real.pi * I * ((w : ℂ) + (ℓ - 1) * ρ))) :
    Complex.exp (2 * Real.pi * I * ((w : ℂ) - (w : ℂ) / ε + ℓ * ρ)) =
      Complex.exp (2 * Real.pi * I * ρ) := by
  have h₁ : Complex.exp (2 * Real.pi * I *
      ((w : ℂ) - (w : ℂ) / ε + ℓ * ρ)) *
        Complex.exp (2 * Real.pi * I * ((w : ℂ) / ε)) =
      Complex.exp (2 * Real.pi * I * ((w : ℂ) + ℓ * ρ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have h₂ : Complex.exp (2 * Real.pi * I * ρ) *
      Complex.exp (2 * Real.pi * I * ((w : ℂ) + (ℓ - 1) * ρ)) =
      Complex.exp (2 * Real.pi * I * ((w : ℂ) + ℓ * ρ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hw] at h₁
  exact mul_right_cancel₀ (Complex.exp_ne_zero _) (h₁.trans h₂.symm)

/-- The integral part `ℓ(b+M(d-1))` of the phase shift has exponential one. -/
private lemma principalFiveTerm_phase_exp_integer (ρ ε : ℂ) (w : ℝ) (ℓ k : ℤ)
    (hw : Complex.exp (2 * Real.pi * I * ((w : ℂ) / ε)) =
      Complex.exp (2 * Real.pi * I * ((w : ℂ) + (ℓ - 1) * ρ))) :
    Complex.exp (2 * Real.pi * I * ((w : ℂ) - (w : ℂ) / ε + ℓ * (ρ + k))) =
      Complex.exp (2 * Real.pi * I * ρ) := by
  have h := exp_two_pi_I_eq_of_sub_intCast
    ((w : ℂ) - (w : ℂ) / ε + ℓ * (ρ + k))
    ((w : ℂ) - (w : ℂ) / ε + ℓ * ρ) (ℓ * k) (by push_cast; ring)
  exact h.trans (principalFiveTerm_phase_exp_base ρ ε w ℓ hw)

/-- The phase exponential acquires `e(ρ_d)` under the contour reindexing shift. -/
private lemma principalFiveTermPhase_exp_add_shift (d : ℕ) (hd : 3 < d)
    (ℓ m m' M : ℤ) (w : ℝ)
    (hw : Complex.exp (2 * Real.pi * I * ((w : ℂ) / (principalRoot d : ℂ) ^ 3)) =
      Complex.exp (2 * Real.pi * I * ((w : ℂ) + (ℓ - 1) * (principalRoot d : ℂ))))
    (hm : m + (principalA d) 0 0 - M * (principalA d) 1 0 = m' + 1)
    (z : ℂ) :
    Complex.exp (2 * Real.pi * I * principalFiveTermPhase d ℓ w m
      (z + (((principalA d) 0 0 : ℂ) * (principalRoot d : ℂ) +
        ((principalA d) 0 1 : ℂ)) - M * (principalRoot d : ℂ) ^ 3)) =
      Complex.exp (2 * Real.pi * I * (principalRoot d : ℂ)) *
        Complex.exp (2 * Real.pi * I * principalFiveTermPhase d ℓ w m' z) := by
  let ρ : ℂ := principalRoot d
  let ε : ℂ := ρ ^ 3
  let k : ℤ := (principalA d) 0 1 + M * ((d : ℤ) - 1)
  let T : ℂ := z + (((principalA d) 0 0 : ℂ) * ρ +
    ((principalA d) 0 1 : ℂ)) - M * ε
  have harg := principalFiveTermPhase_add_shift_argument d hd ℓ m m' M w hm z
  have hphase : principalFiveTermPhase d ℓ w m T =
      principalFiveTermPhase d ℓ w m' z +
        ((w : ℂ) - (w : ℂ) / ε + ℓ * (ρ + k)) := by
    linear_combination harg
  have hexp := principalFiveTerm_phase_exp_integer ρ ε w ℓ k hw
  change Complex.exp (2 * Real.pi * I * principalFiveTermPhase d ℓ w m T) =
    Complex.exp (2 * Real.pi * I * ρ) *
      Complex.exp (2 * Real.pi * I * principalFiveTermPhase d ℓ w m' z)
  rw [hphase, show 2 * Real.pi * I *
      (principalFiveTermPhase d ℓ w m' z +
        ((w : ℂ) - (w : ℂ) / ε + ℓ * (ρ + k))) =
      2 * Real.pi * I * principalFiveTermPhase d ℓ w m' z +
        2 * Real.pi * I * ((w : ℂ) - (w : ℂ) / ε + ℓ * (ρ + k)) by ring,
    Complex.exp_add, hexp]
  ring

/-- The pole factor acquires `e(ρ_d)` under the reindexing shift. -/
private lemma principalFiveTermPoleFactor_add_shift (d : ℕ) (hd : 3 < d)
    (m m' M : ℤ)
    (hm : m + (principalA d) 0 0 - M * (principalA d) 1 0 = m' + 1) (z : ℂ) :
    principalFiveTermPoleFactor d m
      (z + (((principalA d) 0 0 : ℂ) * (principalRoot d : ℂ) +
        ((principalA d) 0 1 : ℂ)) - M * (principalRoot d : ℂ) ^ 3) =
      Complex.exp (2 * Real.pi * I * (principalRoot d : ℂ)) *
        principalFiveTermPoleFactor d m' z := by
  let ρ : ℂ := principalRoot d
  let ε : ℂ := ρ ^ 3
  let T : ℂ := z + (((principalA d) 0 0 : ℂ) * ρ + ((principalA d) 0 1 : ℂ)) - M * ε
  have he1 : Complex.exp (2 * Real.pi * I * (T / ε)) =
      Complex.exp (2 * Real.pi * I * (z / ε + ρ)) :=
    exp_two_pi_I_eq_of_sub_intCast _ _ (-M)
      (by simpa [T, ε, ρ] using principalFiveTermShift_div_argument d hd M z)
  have he2 : Complex.exp (2 * Real.pi * I * (T + m * ρ)) =
      Complex.exp (2 * Real.pi * I * (z + (m' + 1) * ρ)) :=
    exp_two_pi_I_eq_of_sub_intCast _ _
      ((principalA d) 0 1 + M * ((d : ℤ) - 1))
      (by simpa [T, ε, ρ] using principalFiveTermShift_add_argument d hd m m' M hm z)
  have hmul1 : Complex.exp (2 * Real.pi * I * (z / ε + ρ)) =
      Complex.exp (2 * Real.pi * I * ρ) *
        Complex.exp (2 * Real.pi * I * (z / ε)) := by
    rw [show 2 * Real.pi * I * (z / ε + ρ) =
      2 * Real.pi * I * ρ + 2 * Real.pi * I * (z / ε) by ring, Complex.exp_add]
  have hmul2 : Complex.exp (2 * Real.pi * I * (z + (m' + 1) * ρ)) =
      Complex.exp (2 * Real.pi * I * ρ) *
        Complex.exp (2 * Real.pi * I * (z + m' * ρ)) := by
    rw [show 2 * Real.pi * I * (z + (m' + 1) * ρ) =
      2 * Real.pi * I * ρ + 2 * Real.pi * I * (z + m' * ρ) by ring,
      Complex.exp_add]
  change principalFiveTermPoleFactor d m T =
    Complex.exp (2 * Real.pi * I * ρ) * principalFiveTermPoleFactor d m' z
  simp only [principalFiveTermPoleFactor]
  rw [he1, he2, hmul1, hmul2]
  ring

/-- The translated arguments of both product factors use the same lattice shift. -/
private lemma principalFiveTerm_shifted_arguments (d : ℕ) (M : ℤ) (ζ y : ℂ) :
    let S : ℂ := (((principalA d) 0 0 : ℂ) * (principalRoot d : ℂ) +
      ((principalA d) 0 1 : ℂ)) - M * (principalRoot d : ℂ) ^ 3
    (ζ + S = ζ + (((principalA d) 0 0 : ℂ) * (principalRoot d : ℂ) +
      ((principalA d) 0 1 : ℂ)) - M * (principalRoot d : ℂ) ^ 3) ∧
    ((ζ + y) + (((principalA d) 0 0 : ℂ) * (principalRoot d : ℂ) +
      ((principalA d) 0 1 : ℂ)) - M * (principalRoot d : ℂ) ^ 3 = (ζ + S) + y) := by
  dsimp
  constructor <;> ring

/-- After the contour shift, the simplified residue kernel has indices `(m'+1,1)` and
`(m'+p+1,1)`, with matching factors `e(ρ_d)` in phase and pole. -/
private lemma residueKernel_shift_eventuallyEq_factor
    (d : ℕ) (hd : 3 < d) (ℓ p : ℤ) (w y : ℝ)
    (hw : Complex.exp (2 * Real.pi * I * ((w : ℂ) / (principalRoot d : ℂ) ^ 3)) =
      Complex.exp (2 * Real.pi * I * ((w : ℂ) + (ℓ - 1) * (principalRoot d : ℂ))))
    (m m' M : ℤ) (hm : m + (principalA d) 0 0 - M * (principalA d) 1 0 = m' + 1)
    (z : ℂ) :
    (fun ζ => principalFiveTermResidueKernel d ℓ p w y m
      (ζ + (((principalA d) 0 0 : ℂ) * (principalRoot d : ℂ) +
        ((principalA d) 0 1 : ℂ)) - M * (principalRoot d : ℂ) ^ 3)) =ᶠ[𝓝[≠] z]
      (fun ζ => principalFaddeev d (m' + 1) 1 ζ /
        principalFaddeev d (m' + p + 1) 1 (ζ + y) *
          (Complex.exp (2 * Real.pi * I * (principalRoot d : ℂ)) *
            Complex.exp (2 * Real.pi * I * principalFiveTermPhase d ℓ w m' ζ)) /
            (Complex.exp (2 * Real.pi * I * (principalRoot d : ℂ)) *
              principalFiveTermPoleFactor d m' ζ)) := by
  let S : ℂ := (((principalA d) 0 0 : ℂ) * (principalRoot d : ℂ) +
    ((principalA d) 0 1 : ℂ)) - M * (principalRoot d : ℂ) ^ 3
  have htS := tendsto_add_const_nhdsNE S z
  have htY := tendsto_add_const_nhdsNE (y : ℂ) z
  have hK := (principalFiveTermResidueKernel_eventuallyEq d hd ℓ p w y m (z + S))
    |>.comp_tendsto htS
  have hN := principalFiveTermProduct_add_shift_eventuallyEq d hd m M z
  have hD := (principalFiveTermProduct_add_shift_eventuallyEq d hd (m + p) M (z + y))
    |>.comp_tendsto htY
  filter_upwards [hK, hN, hD] with ζ hKζ hNζ hDζ
  obtain ⟨harg, hargY⟩ := principalFiveTerm_shifted_arguments d M ζ (y : ℂ)
  change ζ + S = _ at harg
  simp only [Function.comp_def] at hKζ hDζ
  rw [← harg, hm] at hNζ
  rw [hargY, show m + p + (principalA d) 0 0 - M * (principalA d) 1 0 =
    m' + p + 1 by omega] at hDζ
  have hpole : principalFiveTermPoleFactor d m (ζ + S) =
      Complex.exp (2 * Real.pi * I * (principalRoot d : ℂ)) *
        principalFiveTermPoleFactor d m' ζ := by
    simpa only [harg] using principalFiveTermPoleFactor_add_shift d hd m m' M hm ζ
  have hphase : Complex.exp (2 * Real.pi * I *
      principalFiveTermPhase d ℓ w m (ζ + S)) =
      Complex.exp (2 * Real.pi * I * (principalRoot d : ℂ)) *
        Complex.exp (2 * Real.pi * I * principalFiveTermPhase d ℓ w m' ζ) := by
    simpa only [harg] using principalFiveTermPhase_exp_add_shift d hd ℓ m m' M w hw hm ζ
  rw [← harg]
  change principalFiveTermResidueKernel d ℓ p w y m (ζ + S) = _
  rw [hKζ, hNζ, hDζ, hpole, hphase]

/-- The pointwise algebra of the four index shifts after removing their isolated exceptions. -/
private lemma principalFiveTerm_shifted_factor_pointwise
    (d : ℕ) (ℓ p : ℤ) (w y : ℝ) (m : ℤ) (ζ : ℂ)
    (hK : principalFiveTermResidueKernel d ℓ p w y m ζ =
      principalFaddeev d m 0 ζ /
        principalFaddeev d (m + p) 0 (ζ + y) *
          Complex.exp (2 * Real.pi * I * principalFiveTermPhase d ℓ w m ζ) /
            principalFiveTermPoleFactor d m ζ)
    (hU : principalFaddeev d m 0 ζ =
      principalFaddeev d (m + 1) 0 ζ *
        (1 - Complex.exp (2 * Real.pi * I * (ζ + m * (principalRoot d : ℂ)))))
    (hV : principalFaddeev d (m + p) 0 (ζ + y) =
      principalFaddeev d (m + p + 1) 0 (ζ + y) *
        (1 - Complex.exp (2 * Real.pi * I *
          (ζ + y + (m + p) * (principalRoot d : ℂ)))))
    (hU11 : principalFaddeev d (m + 1) 1 ζ =
      (1 - Complex.exp (2 * Real.pi * I *
        (ζ / (principalRoot d : ℂ) ^ 3))) * principalFaddeev d (m + 1) 0 ζ)
    (hV11 : principalFaddeev d (m + p + 1) 1 (ζ + y) =
      (1 - Complex.exp (2 * Real.pi * I *
        ((ζ + y) / (principalRoot d : ℂ) ^ 3))) *
          principalFaddeev d (m + p + 1) 0 (ζ + y))
    (hVne : principalFaddeev d (m + p) 0 (ζ + y) ≠ 0)
    (hAB : principalFiveTermPoleFactor d m ζ ≠ 0)
    (hden : (1 - Complex.exp (2 * Real.pi * I *
        (ζ + m * (principalRoot d : ℂ))) ≠ 0) ∧
      (1 - Complex.exp (2 * Real.pi * I *
        ((ζ + y) / (principalRoot d : ℂ) ^ 3)) ≠ 0)) :
    principalFaddeev d (m + 1) 1 ζ /
      principalFaddeev d (m + p + 1) 1 (ζ + y) *
        (Complex.exp (2 * Real.pi * I * (principalRoot d : ℂ)) *
          Complex.exp (2 * Real.pi * I * principalFiveTermPhase d ℓ w m ζ)) /
          (Complex.exp (2 * Real.pi * I * (principalRoot d : ℂ)) *
            principalFiveTermPoleFactor d m ζ) =
      principalFiveTermResidueKernel d ℓ p w y m ζ *
        principalFiveTermBracket d p y m ζ := by
  let ε : ℂ := (principalRoot d : ℂ) ^ 3
  let A := Complex.exp (2 * Real.pi * I * (ζ / ε))
  let B := Complex.exp (2 * Real.pi * I * (ζ + m * (principalRoot d : ℂ)))
  let D := Complex.exp (2 * Real.pi * I * (ζ + y + (m + p) * (principalRoot d : ℂ)))
  let F := Complex.exp (2 * Real.pi * I * ((ζ + y) / ε))
  let Q := Complex.exp (2 * Real.pi * I * (principalRoot d : ℂ))
  let U := principalFaddeev d m 0 ζ
  let V := principalFaddeev d (m + p) 0 (ζ + y)
  let U1 := principalFaddeev d (m + 1) 0 ζ
  let V1 := principalFaddeev d (m + p + 1) 0 (ζ + y)
  let U11 := principalFaddeev d (m + 1) 1 ζ
  let V11 := principalFaddeev d (m + p + 1) 1 (ζ + y)
  let E := Complex.exp (2 * Real.pi * I * principalFiveTermPhase d ℓ w m ζ)
  have halg := FiniteFiveTerm.shift_algebra A B D F Q U V U1 V1 U11 V11 E
    (Complex.exp_ne_zero _) hAB hden.1 hden.2 hVne hU hV hU11 hV11
  change U11 / V11 * (Q * E) / (Q * (A - B)) =
    principalFiveTermResidueKernel d ℓ p w y m ζ *
      principalFiveTermBracket d p y m ζ
  rw [hK]
  exact halg

/-- The four index shifts turn the shifted product fraction into `K̃_m B_m` as a germ. -/
private lemma shiftedFactor_eventuallyEq_mul_bracket
    (d : ℕ) (hd : 3 < d) (ℓ p : ℤ) (w y : ℝ) (m : ℤ) (z : ℂ) :
    (fun ζ => principalFaddeev d (m + 1) 1 ζ /
      principalFaddeev d (m + p + 1) 1 (ζ + y) *
        (Complex.exp (2 * Real.pi * I * (principalRoot d : ℂ)) *
          Complex.exp (2 * Real.pi * I * principalFiveTermPhase d ℓ w m ζ)) /
          (Complex.exp (2 * Real.pi * I * (principalRoot d : ℂ)) *
            principalFiveTermPoleFactor d m ζ)) =ᶠ[𝓝[≠] z]
      (fun ζ => principalFiveTermResidueKernel d ℓ p w y m ζ *
        principalFiveTermBracket d p y m ζ) := by
  have ht := tendsto_add_const_nhdsNE (y : ℂ) z
  have hK := principalFiveTermResidueKernel_eventuallyEq d hd ℓ p w y m z
  have hU := principalFaddeev_index_add_one_left_eventuallyEq d hd m 0 z
  have hV := (principalFaddeev_index_add_one_left_eventuallyEq
    d hd (m + p) 0 (z + y)).comp_tendsto ht
  have hU1 := principalFaddeev_index_add_one_right_eventuallyEq d hd (m + 1) 0 z
  have hV1 := (principalFaddeev_index_add_one_right_eventuallyEq
    d hd (m + p + 1) 0 (z + y)).comp_tendsto ht
  have hVne := ht.eventually
    (eventually_principalFaddeev_ne_zero d hd (m + p) 0 (z + y))
  have hAB := eventually_principalFiveTermPoleFactor_ne_zero d hd m z
  have hden := eventually_principalFiveTermBracket_den_ne d hd m y z
  filter_upwards [hK, hU, hV, hU1, hV1, hVne, hAB, hden]
    with ζ hKζ hUζ hVζ hU1ζ hV1ζ hVneζ hABζ hdenζ
  exact principalFiveTerm_shifted_factor_pointwise d ℓ p w y m ζ
    hKζ hUζ.symm
    (by simpa only [Function.comp_def, Int.cast_add] using hVζ.symm)
    (by simpa only [principalJacobiFactor_eq_principalRoot_pow_three d hd,
      Complex.ofReal_pow, Int.cast_zero, zero_mul, add_zero, zero_add] using hU1ζ)
    (by simpa only [Function.comp_def, principalJacobiFactor_eq_principalRoot_pow_three d hd,
      Complex.ofReal_pow, Int.cast_zero, zero_mul, add_zero, zero_add] using hV1ζ)
    hVneζ hABζ hdenζ

/-! ### The one-step identities

Both are identities of germs; the bracket's poles and the kernel poles are isolated. -/

/-- `K̃_m (1 - B_m) = J_m` as germs at every point, when `e(y/ε) = e(y + pρ_d)`: the algebra
`(1 - q^m e(z))(1 - e((z+y)/ε)) - (1 - e(z/ε))(1 - q^{m+p}e(z+y))
= (e(z/ε) - q^m e(z))(1 - q^p e(y))`
and the index shift laws `Φ_{m+1,0}(1 - q^m e) = Φ_{m,0}`, `Φ_{m+p,1} = (1 - e(·/ε))Φ_{m+p,0}`
(`principalFaddeev_index_add_one_left_eventuallyEq`,
`principalFaddeev_index_add_one_right_eventuallyEq`), from
[RW26, Radchenko, Wheeler (2026), Section 3.2]. -/
theorem principalFiveTermResidueKernel_mul_one_sub_bracket
    (d : ℕ) (hd : 3 < d) (ℓ p : ℤ) (w y : ℝ)
    (hy : Complex.exp (2 * Real.pi * I * ((y : ℂ) / (principalRoot d : ℂ) ^ 3)) =
      Complex.exp (2 * Real.pi * I * ((y : ℂ) + p * (principalRoot d : ℂ))))
    (m : ℤ) (z : ℂ) :
    (fun ζ => principalFiveTermResidueKernel d ℓ p w y m ζ *
        (1 - principalFiveTermBracket d p y m ζ)) =ᶠ[𝓝[≠] z]
      principalFiveTermDifferenceKernel d ℓ p w y m := by
  let ε : ℂ := (principalRoot d : ℂ) ^ 3
  have ht := tendsto_add_const_nhdsNE (y : ℂ) z
  have hV := ht.eventually
    (eventually_principalFaddeev_ne_zero d hd (m + p) 0 (z + y))
  have hW := (principalFaddeev_index_add_one_right_eventuallyEq
    d hd (m + p) 0 (z + y)).comp_tendsto ht
  have hAB := eventually_principalFiveTermPoleFactor_ne_zero d hd m z
  have hden := eventually_principalFiveTermBracket_den_ne d hd m y z
  filter_upwards [hV, hW, hAB, hden] with ζ hVζ hWζ hABζ hdenζ
  let A := Complex.exp (2 * Real.pi * I * (ζ / ε))
  let B := Complex.exp (2 * Real.pi * I * (ζ + m * (principalRoot d : ℂ)))
  let C := Complex.exp (2 * Real.pi * I * ((y : ℂ) + p * (principalRoot d : ℂ)))
  let D := Complex.exp (2 * Real.pi * I * (ζ + y + (m + p) * (principalRoot d : ℂ)))
  let F := Complex.exp (2 * Real.pi * I * ((ζ + y) / ε))
  let U := principalFaddeev d (m + 1) 0 ζ
  let V := principalFaddeev d (m + p) 0 (ζ + y)
  let W := principalFaddeev d (m + p) 1 (ζ + y)
  let E := Complex.exp (2 * Real.pi * I * principalFiveTermPhase d ℓ w m ζ)
  change ((U / V * E) * (1 - B) / (A - B)) *
    (1 - ((1 - A) * (1 - D) / ((1 - B) * (1 - F)))) = (1 - C) * (U / W) * E
  exact FiniteFiveTerm.bracket_algebra A B C D F U V W E hABζ hdenζ.1 hdenζ.2
    hVζ (by simpa only [principalJacobiFactor_eq_principalRoot_pow_three d hd,
      Complex.ofReal_pow, Int.cast_zero, zero_mul, add_zero, zero_add,
      Function.comp_def] using hWζ)
    (principalFiveTerm_exp_product_left d m p y ζ)
    (principalFiveTerm_exp_product_right d p y ζ hy)

/-- **The reindexing shift.** With `m + a - 1 = m' + Mc` for `a = (A_d)₀₀`, `b = (A_d)₀₁`,
`c = (A_d)₁₀`, and `e(w/ε) = e(w + (ℓ-1)ρ_d)`:
`K̃_m(ζ + (aρ_d + b) - Mε) = K̃_{m'}(ζ) B_{m'}(ζ)` as germs at every point. This is the
contour translation of [RW26, Radchenko, Wheeler (2026), Section 3.2] in the form of the module
docstring, from the lattice shift laws of Section 2.2 and `e((aρ_d+b)/ε) = q`, `e(aρ_d+b) = q^a`. -/
theorem principalFiveTermResidueKernel_shift_eventuallyEq
    (d : ℕ) (hd : 3 < d) (ℓ p : ℤ) (w y : ℝ)
    (hw : Complex.exp (2 * Real.pi * I * ((w : ℂ) / (principalRoot d : ℂ) ^ 3)) =
      Complex.exp (2 * Real.pi * I * ((w : ℂ) + (ℓ - 1) * (principalRoot d : ℂ))))
    (m m' M : ℤ) (hm : m + (principalA d) 0 0 - M * (principalA d) 1 0 = m' + 1) (z : ℂ) :
    (fun ζ => principalFiveTermResidueKernel d ℓ p w y m
        (ζ + (((principalA d) 0 0 : ℂ) * (principalRoot d : ℂ) + ((principalA d) 0 1 : ℂ)) -
          M * (principalRoot d : ℂ) ^ 3)) =ᶠ[𝓝[≠] z]
      (fun ζ => principalFiveTermResidueKernel d ℓ p w y m' ζ *
        principalFiveTermBracket d p y m' ζ) := by
  exact (residueKernel_shift_eventuallyEq_factor
    d hd ℓ p w y hw m m' M hm z).trans
      (shiftedFactor_eventuallyEq_mul_bracket d hd ℓ p w y m' z)

/-! ### The telescoping identity

The map `m ↦ m'` permutes the summation index; summing the reindexing shift over it gives the
difference kernels. -/

/-- The reindexing `m ↦ (m + a - 1) mod c` of the summation index. -/
def principalFiveTermReindex (d : ℕ) (hd : 3 < d) :
    FiveTermIndex (principalA d) ≃ FiveTermIndex (principalA d) :=
  letI : NeZero ((principalA d) 1 0).toNat :=
    ⟨by have := principalA_lowerLeft_pos d hd; omega⟩
  Equiv.addRight ⟨((principalA d) 0 0 - 1).toNat % ((principalA d) 1 0).toNat,
    Nat.mod_lt _ (by have := principalA_lowerLeft_pos d hd; omega)⟩

/-- The upper-left entry `a` of `A_d` is at least one for `d>3`. -/
private lemma principalA_upperLeft_ge_one (d : ℕ) (hd : 3 < d) :
    1 ≤ (principalA d) 0 0 := by
  have hd4 : (4 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  simp [coe_principalA]
  nlinarith [sq_nonneg ((d : ℤ) - 3)]

/-- For each `m`, the permutation gives `m+a-1=m'+Mc` with `0≤m'<c`; used to reindex
the finite kernel sum. -/
lemma principalFiveTermReindex_exists_quotient (d : ℕ) (hd : 3 < d)
    (m : FiveTermIndex (principalA d)) :
    ∃ M : ℤ, ((m : ℕ) : ℤ) + (principalA d) 0 0 -
        M * (principalA d) 1 0 =
      (((principalFiveTermReindex d hd m :
        FiveTermIndex (principalA d)) : ℕ) : ℤ) + 1 := by
  let c : ℕ := ((principalA d) 1 0).toNat
  let a : ℕ := ((principalA d) 0 0 - 1).toNat
  have hcpos : 0 < (principalA d) 1 0 := principalA_lowerLeft_pos d hd
  have hapos : 0 ≤ (principalA d) 0 0 - 1 := by
    have h := principalA_upperLeft_ge_one d hd
    omega
  have hc : (c : ℤ) = (principalA d) 1 0 := by exact Int.toNat_of_nonneg hcpos.le
  have ha : (a : ℤ) = (principalA d) 0 0 - 1 := by
    exact Int.toNat_of_nonneg hapos
  have hval : (principalFiveTermReindex d hd m).val = (m.val + a % c) % c := rfl
  have hmod : (principalFiveTermReindex d hd m).val = (m.val + a) % c := by
    rw [hval, Nat.add_mod]
    simp
  refine ⟨((m.val + a) / c : ℕ), ?_⟩
  have hdiv := Nat.mod_add_div (m.val + a) c
  have hdivZ : (((m.val + a) % c : ℕ) : ℤ) +
      (c : ℤ) * (((m.val + a) / c : ℕ) : ℤ) = ((m.val + a : ℕ) : ℤ) := by
    exact_mod_cast hdiv
  have hA : (principalA d) 0 0 = (a : ℤ) + 1 := by omega
  have hmodZ : (((principalFiveTermReindex d hd m).val : ℕ) : ℤ) =
      (((m.val + a) % c : ℕ) : ℤ) := congrArg (fun n : ℕ => (n : ℤ)) hmod
  simp only [Nat.cast_add] at hdivZ
  linear_combination hA + (((m.val + a) / c : ℕ) : ℤ) * hc - hdivZ - hmodZ

/-- The common-line translation equals the lattice shift of the reindexed summand when
`m+a-1=m'+Mc`. -/
lemma principalFiveTermShift_coordinate (d : ℕ) (hd : 3 < d) (m m' M : ℤ)
    (hm : m + (principalA d) 0 0 - M * (principalA d) 1 0 = m' + 1)
    (z : ℂ) :
    z + ((principalRoot d : ℂ) ^ 3 - 1) / ((principalA d) 1 0 : ℂ) -
        (m : ℂ) * (principalRoot d : ℂ) ^ 3 / ((principalA d) 1 0 : ℂ) =
      (z - (m' : ℂ) * (principalRoot d : ℂ) ^ 3 / ((principalA d) 1 0 : ℂ)) +
        (((principalA d) 0 0 : ℂ) * (principalRoot d : ℂ) +
          ((principalA d) 0 1 : ℂ)) - M * (principalRoot d : ℂ) ^ 3 := by
  let ρ : ℂ := principalRoot d
  let ε : ℂ := ρ ^ 3
  let a : ℂ := (principalA d) 0 0
  let b : ℂ := (principalA d) 0 1
  let c : ℂ := (principalA d) 1 0
  let e : ℂ := (principalA d) 1 1
  have hc0 : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast (ne_of_gt (principalA_lowerLeft_pos d hd))
  obtain ⟨hε, -, hdet⟩ := principalFiveTerm_shift_matrix_data d hd
  change ε = c * ρ + e at hε
  change a * e - b * c = 1 at hdet
  have hroot : c * (a * ρ + b) = a * ε - 1 := by
    calc
      c * (a * ρ + b) = a * (c * ρ + e) - (a * e - b * c) := by ring
      _ = a * ε - 1 := by rw [← hε, hdet]
  have hmC : (m : ℂ) + a - M * c = (m' : ℂ) + 1 := by
    dsimp [a, c]
    exact_mod_cast hm
  change z + (ε - 1) / c - m * ε / c =
    (z - m' * ε / c) + (a * ρ + b) - M * ε
  field_simp [hc0]
  linear_combination -hroot - ε * hmC

/-- One translated common-line summand equals the bracketed summand at its reindexed
position, as a germ. -/
private lemma residueSum_shift_summand_eventuallyEq
    (d : ℕ) (hd : 3 < d) (ℓ p : ℤ) (w y : ℝ)
    (hw : Complex.exp (2 * Real.pi * I * ((w : ℂ) / (principalRoot d : ℂ) ^ 3)) =
      Complex.exp (2 * Real.pi * I * ((w : ℂ) + (ℓ - 1) * (principalRoot d : ℂ))))
    (m : FiveTermIndex (principalA d)) (z : ℂ) :
    (fun ζ => principalFiveTermResidueKernel d ℓ p w y ((m : ℕ) : ℤ)
      (ζ + ((principalRoot d : ℂ) ^ 3 - 1) / ((principalA d) 1 0 : ℂ) -
        ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 / ((principalA d) 1 0 : ℂ)))
      =ᶠ[𝓝[≠] z]
    (fun ζ => principalFiveTermResidueKernel d ℓ p w y
      (((principalFiveTermReindex d hd m : FiveTermIndex (principalA d)) : ℕ) : ℤ)
      (ζ - (((principalFiveTermReindex d hd m :
        FiveTermIndex (principalA d)) : ℕ) : ℂ) *
          (principalRoot d : ℂ) ^ 3 / ((principalA d) 1 0 : ℂ)) *
      principalFiveTermBracket d p y
        (((principalFiveTermReindex d hd m : FiveTermIndex (principalA d)) : ℕ) : ℤ)
        (ζ - (((principalFiveTermReindex d hd m :
          FiveTermIndex (principalA d)) : ℕ) : ℂ) *
            (principalRoot d : ℂ) ^ 3 / ((principalA d) 1 0 : ℂ))) := by
  obtain ⟨M, hm⟩ := principalFiveTermReindex_exists_quotient d hd m
  let m' := principalFiveTermReindex d hd m
  let v : ℂ := ((m' : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
    ((principalA d) 1 0 : ℂ)
  have ht : Tendsto (fun ζ : ℂ => ζ - v) (𝓝[≠] z) (𝓝[≠] (z - v)) := by
    simpa only [sub_eq_add_neg] using tendsto_add_const_nhdsNE (-v) z
  have h := (principalFiveTermResidueKernel_shift_eventuallyEq
    d hd ℓ p w y hw ((m : ℕ) : ℤ) ((m' : ℕ) : ℤ) M hm (z - v)).comp_tendsto ht
  filter_upwards [h] with ζ hζ
  have hcoord := principalFiveTermShift_coordinate d hd
    ((m : ℕ) : ℤ) ((m' : ℕ) : ℤ) M hm ζ
  simp only [Int.cast_natCast] at hcoord
  simp only [Function.comp_def] at hζ
  change _ = principalFiveTermResidueKernel d ℓ p w y ((m' : ℕ) : ℤ) (ζ - v) *
    principalFiveTermBracket d p y ((m' : ℕ) : ℤ) (ζ - v)
  rw [hcoord]
  exact hζ

/-- The bracket cancellation survives the translation of each summand to the common line. -/
private lemma residueSum_bracket_summand_eventuallyEq
    (d : ℕ) (hd : 3 < d) (ℓ p : ℤ) (w y : ℝ)
    (hy : Complex.exp (2 * Real.pi * I * ((y : ℂ) / (principalRoot d : ℂ) ^ 3)) =
      Complex.exp (2 * Real.pi * I * ((y : ℂ) + p * (principalRoot d : ℂ))))
    (m : FiveTermIndex (principalA d)) (z : ℂ) :
    (fun ζ => principalFiveTermResidueKernel d ℓ p w y ((m : ℕ) : ℤ)
      (ζ - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 / ((principalA d) 1 0 : ℂ)) *
        (1 - principalFiveTermBracket d p y ((m : ℕ) : ℤ)
          (ζ - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
            ((principalA d) 1 0 : ℂ)))) =ᶠ[𝓝[≠] z]
      (fun ζ => principalFiveTermDifferenceKernel d ℓ p w y ((m : ℕ) : ℤ)
        (ζ - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
          ((principalA d) 1 0 : ℂ))) := by
  let v : ℂ := ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
    ((principalA d) 1 0 : ℂ)
  have ht : Tendsto (fun ζ : ℂ => ζ - v) (𝓝[≠] z) (𝓝[≠] (z - v)) := by
    simpa only [sub_eq_add_neg] using tendsto_add_const_nhdsNE (-v) z
  simpa only [Function.comp_def] using
    (principalFiveTermResidueKernel_mul_one_sub_bracket
      d hd ℓ p w y hy ((m : ℕ) : ℤ) (z - v)).comp_tendsto ht

/-- **Telescoping.** `L(ζ) - L(ζ + (ε-1)/c) = J(ζ)` as germs at every point, under the two
lattice relations of the parameters. This is the sum over the reindexing of
`principalFiveTermResidueKernel_shift_eventuallyEq` combined with
`principalFiveTermResidueKernel_mul_one_sub_bracket`, the telescoping through the
`c` sub-steps of [RW26, Radchenko, Wheeler (2026), Section 3.2]. -/
theorem principalFiveTermResidueSum_sub_shift_eventuallyEq
    (d : ℕ) (hd : 3 < d) (ℓ p : ℤ) (w y : ℝ)
    (hw : Complex.exp (2 * Real.pi * I * ((w : ℂ) / (principalRoot d : ℂ) ^ 3)) =
      Complex.exp (2 * Real.pi * I * ((w : ℂ) + (ℓ - 1) * (principalRoot d : ℂ))))
    (hy : Complex.exp (2 * Real.pi * I * ((y : ℂ) / (principalRoot d : ℂ) ^ 3)) =
      Complex.exp (2 * Real.pi * I * ((y : ℂ) + p * (principalRoot d : ℂ))))
    (z : ℂ) :
    (fun ζ => principalFiveTermResidueSum d ℓ p w y ζ -
        principalFiveTermResidueSum d ℓ p w y
          (ζ + ((principalRoot d : ℂ) ^ 3 - 1) / ((principalA d) 1 0 : ℂ))) =ᶠ[𝓝[≠] z]
      principalFiveTermDifferenceSum d ℓ p w y := by
  let e := principalFiveTermReindex d hd
  have hs := Filter.eventually_all.mpr (fun m : FiveTermIndex (principalA d) =>
    residueSum_shift_summand_eventuallyEq d hd ℓ p w y hw m z)
  have hb := Filter.eventually_all.mpr (fun m : FiveTermIndex (principalA d) =>
    residueSum_bracket_summand_eventuallyEq d hd ℓ p w y hy m z)
  filter_upwards [hs, hb] with ζ hsζ hbζ
  let f : FiveTermIndex (principalA d) → ℂ := fun m =>
    principalFiveTermResidueKernel d ℓ p w y ((m : ℕ) : ℤ)
      (ζ - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 / ((principalA d) 1 0 : ℂ))
  let b : FiveTermIndex (principalA d) → ℂ := fun m =>
    principalFiveTermBracket d p y ((m : ℕ) : ℤ)
      (ζ - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 / ((principalA d) 1 0 : ℂ))
  let g : FiveTermIndex (principalA d) → ℂ := fun m =>
    principalFiveTermDifferenceKernel d ℓ p w y ((m : ℕ) : ℤ)
      (ζ - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 / ((principalA d) 1 0 : ℂ))
  have hsum : (∑ m : FiveTermIndex (principalA d),
      principalFiveTermResidueKernel d ℓ p w y ((m : ℕ) : ℤ)
        (ζ + ((principalRoot d : ℂ) ^ 3 - 1) / ((principalA d) 1 0 : ℂ) -
          ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 / ((principalA d) 1 0 : ℂ))) =
      ∑ m, f (e m) * b (e m) := by
    exact Finset.sum_congr rfl (fun m hm => hsζ m)
  change (∑ m, f m) - (∑ m : FiveTermIndex (principalA d),
    principalFiveTermResidueKernel d ℓ p w y ((m : ℕ) : ℤ)
      (ζ + ((principalRoot d : ℂ) ^ 3 - 1) / ((principalA d) 1 0 : ℂ) -
        ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 / ((principalA d) 1 0 : ℂ))) =
    ∑ m, g m
  rw [hsum]
  exact FiniteFiveTerm.finite_telescope e f b g (fun m => hbζ m)

/-- On a vertical line the telescoping identity holds almost everywhere: the set where a germ
identity at every point fails is countable, so its trace on the line is null. -/
theorem ae_principalFiveTermResidueSum_sub_shift_eq
    (d : ℕ) (hd : 3 < d) (ℓ p : ℤ) (w y : ℝ)
    (hw : Complex.exp (2 * Real.pi * I * ((w : ℂ) / (principalRoot d : ℂ) ^ 3)) =
      Complex.exp (2 * Real.pi * I * ((w : ℂ) + (ℓ - 1) * (principalRoot d : ℂ))))
    (hy : Complex.exp (2 * Real.pi * I * ((y : ℂ) / (principalRoot d : ℂ) ^ 3)) =
      Complex.exp (2 * Real.pi * I * ((y : ℂ) + p * (principalRoot d : ℂ))))
    (x : ℝ) :
    ∀ᵐ t : ℝ,
      principalFiveTermResidueSum d ℓ p w y ((x : ℂ) + t * I) -
        principalFiveTermResidueSum d ℓ p w y
          ((x : ℂ) + t * I + ((principalRoot d : ℂ) ^ 3 - 1) / ((principalA d) 1 0 : ℂ)) =
      principalFiveTermDifferenceSum d ℓ p w y ((x : ℂ) + t * I) := by
  have h := ae_eq_comp_affine_of_forall_eventuallyEq_nhdsNE
    (fun z => principalFiveTermResidueSum_sub_shift_eventuallyEq d hd ℓ p w y hw hy z)
    I (x : ℂ) Complex.I_ne_zero
  simpa only [mul_comm I, add_comm] using h

end SIC

end
