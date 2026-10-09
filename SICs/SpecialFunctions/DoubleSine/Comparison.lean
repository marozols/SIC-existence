/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Analysis.RemovableQuotient
import SICs.SpecialFunctions.DoubleSine.Gamma
import SICs.SpecialFunctions.DoubleSine.ShintaniProduct

/-!
# Shintani's product formula for the double sine

Shintani's Proposition 5: the double-gamma ratio equals the normalized q-product.

This file proves [95, Shintani (1977), Proposition 5] with periods `(1, τ)`, `Im τ > 0`: the
Barnes double-gamma ratio `S₂(z;1,τ) = Γ₂(z)⁻¹ / Γ₂(1+τ-z)⁻¹` of
`SICs.SpecialFunctions.DoubleSine.Gamma` equals Shintani's normalized q-product
`√i exp(πi(τ+τ⁻¹)/12) f₁(z)/f₂(z) exp(P(z))` of `SICs.SpecialFunctions.DoubleSine.ShintaniProduct`.
The two constructions have different established domains and are kept as separate definitions;
the identity is proved here in the denominator-cleared form of an identity between entire
functions,

```text
Γ₂(z;1,τ)⁻¹ f₂(z,τ) = Γ₂(1+τ-z;1,τ)⁻¹ √i exp(πi(τ+τ⁻¹)/12) f₁(z,τ) exp(P(z,τ)),
```

from which the quotient identity follows wherever the two denominators are nonzero, in
particular off the period lattice `ℤ + ℤτ`. The comparison of the gamma ratio with the complex
integral of [AFK25, equation (8.7), `eq:dsintrep`] is
`SICs.SpecialFunctions.DoubleSine.IntegralRepresentation`.

## Mathematical argument

Following Shintani's proof, write `N(z)` for the left side and `D(z)` for the right side of the
cleared identity. Both are entire, and their zeros are lattice points `m + nτ`: `Γ₂(z)⁻¹`
vanishes at `m, n ≤ 0` and `f₂` at `m ≥ 1`; `Γ₂(1+τ-z)⁻¹` vanishes at `m, n ≥ 1` and `f₁` at
`n ≤ 0`. So both vanish exactly at the lattice points with `n ≤ 0` or `m, n ≥ 1`, and all these
zeros are simple. The two double-gamma difference equations, the four product
difference equations, and Euler's reflection formula give `N(z+1)D(z) = N(z)D(z+1)` and
`N(z+τ)D(z) = N(z)D(z+τ)` off the lattice, so the quotient `N/D` is doubly periodic there. By
`differentiable_removableQuotient` it extends to an entire function, which is doubly periodic by
continuity and therefore constant by
`apply_eq_apply_of_differentiable_of_periodic`.
Near the origin the quotient is `(S₂(z)/z) / (S₂^prod(z)/z)`, and both factors tend to
`2π/√τ` (`tendsto_shintaniDoubleSineGamma_div`, `tendsto_shintaniDoubleSineProduct_div`), so the
constant is `1`.

The raw q-product uses pointwise division: at a zero of `f₂`, such as `z = 1`, its value is `0`,
whereas the gamma ratio is nonzero there when `Re τ > 0`. The cleared identity holds at every
`z`; the quotient identity is stated with the two nonvanishing hypotheses its denominators need.

## References

- [95, Shintani (1977), Proposition 5]
- [72, Kopp (2024), Theorem 4.23, `thm:shin5`]
-/

noncomputable section

open Complex Real Filter Topology

namespace SIC

/-! ### The two cleared sides of Shintani's identity

`N(z) = Γ₂(z;1,τ)⁻¹ f₂(z,τ)` carries the numerator of the gamma ratio and the denominator of
the product; `D(z)` carries the other two factors and the product's normalization. -/

/-- The cleared gamma side `N(z) = Γ₂(z;1,τ)⁻¹ f₂(z,τ)` of Shintani's identity. -/
private def shintaniGammaSide (z tau : ℂ) : ℂ :=
  barnesDoubleGammaInv z 1 tau * shintaniF2 z tau

/-- The cleared product side
`D(z) = Γ₂(1+τ-z;1,τ)⁻¹ √i exp(πi(τ+τ⁻¹)/12) f₁(z,τ) exp(P(z,τ))` of Shintani's identity. -/
private def shintaniProductSide (z tau : ℂ) : ℂ :=
  barnesDoubleGammaInv (1 + tau - z) 1 tau *
    (Complex.sqrt I * Complex.exp (π * I / 12 * (tau + tau⁻¹)) * shintaniF1 z tau *
      Complex.exp (shintaniDoubleSineProductPhase z tau))

/-- `N` is entire for `Im τ > 0`. -/
private lemma shintaniGammaSide_differentiable (tau : ℂ) (htau : 0 < tau.im) :
    Differentiable ℂ (fun z => shintaniGammaSide z tau) := by
  exact (differentiable_barnesDoubleGammaInv tau (Or.inr htau.ne')).mul
    (shintaniF2_differentiable tau htau)

/-- `D` is entire for `Im τ > 0`. -/
private lemma shintaniProductSide_differentiable (tau : ℂ) (htau : 0 < tau.im) :
    Differentiable ℂ (fun z => shintaniProductSide z tau) := by
  unfold shintaniProductSide
  apply Differentiable.mul
  · exact (differentiable_barnesDoubleGammaInv tau
      (Or.inr htau.ne')).comp (by fun_prop)
  · apply Differentiable.mul
    · exact ((differentiable_const (c :=
        Complex.sqrt I * Complex.exp (π * I / 12 * (tau + tau⁻¹)))).mul
          (shintaniF1_differentiable tau htau))
    · unfold shintaniDoubleSineProductPhase
      fun_prop

/-- A zero of the reflected inverse double gamma lies in the strictly positive lattice cone. -/
private lemma exists_pos_lattice_of_reflected_gamma_eq_zero (z tau : ℂ)
    (htau : 0 < tau.im) (hz : barnesDoubleGammaInv (1 + tau - z) 1 tau = 0) :
    ∃ m n : ℤ, z = (m : ℂ) + (n : ℂ) * tau ∧ 1 ≤ m ∧ 1 ≤ n := by
  rcases (barnesDoubleGammaInv_eq_zero_iff
    (1 + tau - z) tau (Or.inr htau.ne')).mp hz with h | ⟨p, h⟩
  · refine ⟨1, 1, ?_, by omega, by omega⟩
    linear_combination -h
  · refine ⟨(p.1.1 : ℤ) + 1, (p.1.2 : ℤ) + 1, ?_, by omega, by omega⟩
    unfold barnesDoubleGammaLatticePoint at h
    push_cast at h ⊢
    linear_combination -h

/-- The second Shintani product vanishes on every lattice column with positive first
coordinate. -/
private lemma shintaniF2_eq_zero_of_one_le (tau : ℂ) (htau : 0 < tau.im) (m n : ℤ)
    (hm : 1 ≤ m) : shintaniF2 ((m : ℂ) + (n : ℂ) * tau) tau = 0 := by
  rw [shintaniF2_eq_zero_iff _ tau htau]
  let a := (m - 1).toNat
  have ha : (a : ℤ) + 1 = m := by
    dsimp [a]
    omega
  refine ⟨a, n, ?_⟩
  exact_mod_cast (congrArg (fun k : ℤ => (k : ℂ) + (n : ℂ) * tau) ha).symm

/-- The inverse double gamma vanishes on the nonpositive lattice cone. -/
private lemma barnesDoubleGammaInv_eq_zero_of_nonpos (tau : ℂ) (htau : 0 < tau.im)
    (m n : ℤ) (hm : m ≤ 0) (hn : n ≤ 0) :
    barnesDoubleGammaInv ((m : ℂ) + (n : ℂ) * tau) 1 tau = 0 := by
  let a := (-m).toNat
  let b := (-n).toNat
  have ha : (a : ℤ) = -m := by
    dsimp [a]
    omega
  have hb : (b : ℤ) = -n := by
    dsimp [b]
    omega
  by_cases hab : (a, b) = (0, 0)
  · have ham : m = 0 := by have := congrArg Prod.fst hab; dsimp at this; omega
    have hbn : n = 0 := by have := congrArg Prod.snd hab; dsimp at this; omega
    simp [ham, hbn]
  · rw [barnesDoubleGammaInv_eq_zero_iff _ tau (Or.inr htau.ne')]
    right
    refine ⟨⟨(a, b), hab⟩, ?_⟩
    unfold barnesDoubleGammaLatticePoint
    push_cast
    rw [show (a : ℂ) = -(m : ℂ) by exact_mod_cast ha,
      show (b : ℂ) = -(n : ℂ) by exact_mod_cast hb]
    ring

/-- `D` vanishes exactly when its reflected inverse double gamma or `f₁` does; its constant
and exponential factors are nonzero. -/
private lemma shintaniProductSide_eq_zero_iff (z tau : ℂ) :
    shintaniProductSide z tau = 0 ↔
      barnesDoubleGammaInv (1 + tau - z) 1 tau = 0 ∨ shintaniF1 z tau = 0 := by
  simp only [shintaniProductSide, mul_eq_zero, sqrt_I_ne_zero, Complex.exp_ne_zero, false_or,
    or_false]

/-- Every zero of `D` is a period lattice point: the zeros of `Γ₂(1+τ-·;1,τ)⁻¹` are the
`m + nτ` with `m, n ≥ 1` and those of `f₁` are the `m + nτ` with `n ≤ 0`. -/
private lemma isPeriodLatticePoint_of_productSide_eq_zero (z tau : ℂ) (htau : 0 < tau.im)
    (hz : shintaniProductSide z tau = 0) : IsPeriodLatticePoint tau z := by
  have hz' := (shintaniProductSide_eq_zero_iff z tau).mp hz
  rcases hz' with hgamma | hf₁
  · obtain ⟨m, n, hmn, -, -⟩ :=
      exists_pos_lattice_of_reflected_gamma_eq_zero z tau htau hgamma
    exact ⟨m, n, hmn⟩
  · obtain ⟨n, k, hk⟩ := (shintaniF1_eq_zero_iff z tau htau).mp hf₁
    refine ⟨k, -(n : ℤ), ?_⟩
    simpa only [Int.cast_neg, Int.cast_natCast, neg_mul, sub_eq_add_neg] using hk

/-- `D` is nonzero off the period lattice, the contrapositive of
`isPeriodLatticePoint_of_productSide_eq_zero`. -/
private lemma shintaniProductSide_ne_zero (z tau : ℂ) (htau : 0 < tau.im)
    (hz : ¬ IsPeriodLatticePoint tau z) : shintaniProductSide z tau ≠ 0 :=
  fun h => hz (isPeriodLatticePoint_of_productSide_eq_zero z tau htau h)

/-- Every zero of `D` is a zero of `N`: at `m + nτ` with `m, n ≥ 1` the factor `f₂` vanishes;
at `m + nτ` with `n ≤ 0`, `f₂` vanishes if `m ≥ 1` and `Γ₂(·;1,τ)⁻¹` vanishes if `m ≤ 0`.
(The lattice points with `m ≤ 0 < n` are zeros of neither side.) -/
private lemma gammaSide_eq_zero_of_productSide_eq_zero (z tau : ℂ)
    (htau : 0 < tau.im) (hz : shintaniProductSide z tau = 0) : shintaniGammaSide z tau = 0 := by
  have hz' := (shintaniProductSide_eq_zero_iff z tau).mp hz
  unfold shintaniGammaSide
  rcases hz' with hgamma | hf₁
  · obtain ⟨m, n, rfl, hm, -⟩ :=
      exists_pos_lattice_of_reflected_gamma_eq_zero z tau htau hgamma
    rw [shintaniF2_eq_zero_of_one_le tau htau m n hm, mul_zero]
  · obtain ⟨a, k, rfl⟩ := (shintaniF1_eq_zero_iff z tau htau).mp hf₁
    have hform : (k : ℂ) - (a : ℂ) * tau =
        (k : ℂ) + ((-(a : ℤ) : ℤ) : ℂ) * tau := by
      push_cast
      ring
    rw [hform]
    by_cases hk : 1 ≤ k
    · rw [shintaniF2_eq_zero_of_one_le tau htau k (-(a : ℤ)) hk, mul_zero]
    · have hk0 : k ≤ 0 := by omega
      rw [barnesDoubleGammaInv_eq_zero_of_nonpos tau htau k (-(a : ℤ)) hk0 (by omega),
        zero_mul]

/-- The reflected inverse double gamma and `f₁` have disjoint zero sets. -/
private lemma reflected_gamma_ne_zero_of_shintaniF1_eq_zero (z tau : ℂ)
    (htau : 0 < tau.im) (hf₁ : shintaniF1 z tau = 0) :
    barnesDoubleGammaInv (1 + tau - z) 1 tau ≠ 0 := by
  intro hgamma
  obtain ⟨m, n, hmn, -, hn⟩ :=
    exists_pos_lattice_of_reflected_gamma_eq_zero z tau htau hgamma
  obtain ⟨a, k, hk⟩ := (shintaniF1_eq_zero_iff z tau htau).mp hf₁
  have hk' : z = (k : ℂ) + ((-(a : ℤ) : ℤ) : ℂ) * tau := by
    simpa only [Int.cast_neg, Int.cast_natCast, neg_mul, sub_eq_add_neg] using hk
  have hcoords := (intCast_add_intCast_mul_eq_iff tau htau.ne' m n k (-(a : ℤ))).mp
    (hmn.symm.trans hk')
  omega

/-- At a zero of the reflected inverse double gamma, `f₁` is nonzero. -/
private lemma shintaniF1_ne_zero_of_reflected_gamma_eq_zero (z tau : ℂ)
    (htau : 0 < tau.im) (hgamma : barnesDoubleGammaInv (1 + tau - z) 1 tau = 0) :
    shintaniF1 z tau ≠ 0 := by
  intro hf₁
  exact reflected_gamma_ne_zero_of_shintaniF1_eq_zero z tau htau hf₁ hgamma

/-- A zero of the reflected inverse double gamma remains simple after the affine reflection. -/
private lemma deriv_reflected_gamma_ne_zero (z tau : ℂ) (htau : 0 < tau.im)
    (hz : barnesDoubleGammaInv (1 + tau - z) 1 tau = 0) :
    deriv (fun w => barnesDoubleGammaInv (1 + tau - w) 1 tau) z ≠ 0 := by
  have houter : deriv (fun w => barnesDoubleGammaInv w 1 tau) (1 + tau - z) ≠ 0 := by
    rcases (barnesDoubleGammaInv_eq_zero_iff
      (1 + tau - z) tau (Or.inr htau.ne')).mp hz with h | ⟨p, hp⟩
    · rw [h, deriv_barnesDoubleGammaInv_zero tau (Or.inr htau.ne')]
      exact one_ne_zero
    · rw [hp]
      exact deriv_barnesDoubleGammaInv_neg_ne_zero tau
        (Or.inr htau.ne') (barnesDoubleGammaLatticePoint_one_injective tau htau) p
  change deriv ((fun u : ℂ => barnesDoubleGammaInv u 1 tau) ∘
    (fun w : ℂ => 1 + tau - w)) z ≠ 0
  rw [deriv_comp z (differentiable_barnesDoubleGammaInv tau
    (Or.inr htau.ne') (1 + tau - z)) (by fun_prop)]
  rw [deriv_const_sub]
  simpa using houter

/-- Every zero of `D` is simple: exactly one of the factors `Γ₂(1+τ-·;1,τ)⁻¹` and `f₁` vanishes
there, with nonzero derivative, and the other factors are nonzero. -/
private lemma deriv_shintaniProductSide_ne_zero (z tau : ℂ) (htau : 0 < tau.im)
    (hz : shintaniProductSide z tau = 0) :
    deriv (fun w => shintaniProductSide w tau) z ≠ 0 := by
  have hsqrt : Complex.sqrt I ≠ 0 := sqrt_I_ne_zero
  have hA : DifferentiableAt ℂ
      (fun w => barnesDoubleGammaInv (1 + tau - w) 1 tau) z :=
    ((differentiable_barnesDoubleGammaInv tau
      (Or.inr htau.ne')) (1 + tau - z)).comp z (by fun_prop)
  have hF : DifferentiableAt ℂ (fun w => shintaniF1 w tau) z :=
    shintaniF1_differentiable tau htau z
  have hE : DifferentiableAt ℂ
      (fun w => Complex.exp (shintaniDoubleSineProductPhase w tau)) z := by
    unfold shintaniDoubleSineProductPhase
    fun_prop
  let C := Complex.sqrt I * Complex.exp (π * I / 12 * (tau + tau⁻¹))
  have hB : DifferentiableAt ℂ
      (fun w => C * shintaniF1 w tau *
        Complex.exp (shintaniDoubleSineProductPhase w tau)) z :=
    (hF.const_mul C).mul hE
  have hC : C ≠ 0 := mul_ne_zero hsqrt (Complex.exp_ne_zero _)
  have hz' := (shintaniProductSide_eq_zero_iff z tau).mp hz
  unfold shintaniProductSide
  rw [deriv_fun_mul hA hB]
  rcases hz' with hgamma | hf₁
  · rw [hgamma, zero_mul, add_zero]
    exact mul_ne_zero (deriv_reflected_gamma_ne_zero z tau htau hgamma)
      (mul_ne_zero (mul_ne_zero hC
        (shintaniF1_ne_zero_of_reflected_gamma_eq_zero z tau htau hgamma))
        (Complex.exp_ne_zero _))
  · have hgamma := reflected_gamma_ne_zero_of_shintaniF1_eq_zero z tau htau hf₁
    have hBderiv : deriv (fun w => C * shintaniF1 w tau *
        Complex.exp (shintaniDoubleSineProductPhase w tau)) z =
        C * deriv (fun w => shintaniF1 w tau) z *
          Complex.exp (shintaniDoubleSineProductPhase z tau) := by
      rw [deriv_fun_mul (hF.const_mul C) hE, deriv_const_mul C hF, hf₁]
      ring
    simp only [hf₁, mul_zero, zero_mul]
    rw [hBderiv]
    simpa only [zero_add] using mul_ne_zero hgamma (mul_ne_zero (mul_ne_zero hC
      (shintaniF1_deriv_ne_zero_of_eq_zero z tau htau hf₁)) (Complex.exp_ne_zero _))

/-! ### Double periodicity of the quotient

Both sides change by the same factor under `z ↦ z + 1` and `z ↦ z + τ`. For `z ↦ z + 1`,
`barnesDoubleGammaInv_add_one_mul_inv_Gamma` at `z` and at `τ - z`, `shintaniF2_add_one`,
`shintaniF1_add_one`, and Euler's reflection formula `Γ(u)⁻¹Γ(1-u)⁻¹ = sin(πu)/π` with
`u = z/τ` give `N(z+1)D(z) sin(πu)/π = N(z)D(z+1) sin(πu)/π`; for `z ↦ z + τ`, the second
difference equation at `z` and at `1 - z`, `shintaniF2_add_tau`, and `shintaniF1_add_tau` give
the same with `sin(πz)`. Since the project's reflection laws are already cleared of the sine,
the cross-multiplied identities hold for every `z`; the sine only enters when dividing. -/

/-- The first product factor exactly accounts for the phase change under `z ↦ z + 1`. -/
private lemma shintani_phase_add_one (z tau : ℂ) (htau : 0 < tau.im) :
    (1 - Complex.exp (2 * π * I * (z / tau))) *
        Complex.exp (shintaniDoubleSineProductPhase z tau) =
      2 * Complex.sin (π * z / tau) *
        Complex.exp (shintaniDoubleSineProductPhase (z + 1) tau) := by
  have htau0 : tau ≠ 0 := fun h => by simp [h] at htau
  have hphase : shintaniDoubleSineProductPhase (z + 1) tau =
      shintaniDoubleSineProductPhase z tau + π * I * (z / tau) - π / 2 * I := by
    unfold shintaniDoubleSineProductPhase
    field_simp
    ring
  rw [one_sub_exp_two_pi_I_eq_two_exp_shift, hphase]
  rw [show shintaniDoubleSineProductPhase z tau + π * I * (z / tau) - π / 2 * I =
      shintaniDoubleSineProductPhase z tau + (π * I * (z / tau) - π / 2 * I) by ring,
    Complex.exp_add]
  rw [show π * (z / tau) = π * z / tau by ring]
  ring

/-- The second product factor exactly accounts for the phase change under `z ↦ z + τ`. -/
private lemma shintani_phase_add_tau (z tau : ℂ) (htau : 0 < tau.im) :
    (1 - Complex.exp (2 * π * I * z)) *
        Complex.exp (shintaniDoubleSineProductPhase z tau) =
      2 * Complex.sin (π * z) *
        Complex.exp (shintaniDoubleSineProductPhase (z + tau) tau) := by
  have htau0 : tau ≠ 0 := fun h => by simp [h] at htau
  have hphase : shintaniDoubleSineProductPhase (z + tau) tau =
      shintaniDoubleSineProductPhase z tau + π * I * z - π / 2 * I := by
    unfold shintaniDoubleSineProductPhase
    field_simp
    ring
  rw [one_sub_exp_two_pi_I_eq_two_exp_shift, hphase]
  rw [show shintaniDoubleSineProductPhase z tau + π * I * z - π / 2 * I =
      shintaniDoubleSineProductPhase z tau + (π * I * z - π / 2 * I) by ring,
    Complex.exp_add]
  ring

/-- `N(z+1) D(z) = N(z) D(z+1)` for every `z`, from the denominator-cleared reflection law
`barnesDoubleGammaInv_reflect_add_one` and the two product shifts. -/
private lemma shintaniGammaSide_add_one_mul (z tau : ℂ) (htau : 0 < tau.im) :
    shintaniGammaSide (z + 1) tau * shintaniProductSide z tau =
      shintaniGammaSide z tau * shintaniProductSide (z + 1) tau := by
  have hgamma := barnesDoubleGammaInv_reflect_add_one z tau (Or.inr htau.ne')
  have hphase := shintani_phase_add_one z tau htau
  unfold shintaniGammaSide shintaniProductSide
  rw [shintaniF2_add_one z tau htau, shintaniF1_add_one z tau,
    show 1 + tau - (z + 1) = tau - z by ring]
  calc
    _ = (barnesDoubleGammaInv (z + 1) 1 tau *
          barnesDoubleGammaInv (1 + tau - z) 1 tau) *
        (shintaniF2 z tau *
          (Complex.sqrt I * Complex.exp (π * I / 12 * (tau + tau⁻¹))) *
          shintaniF1 z tau *
          ((1 - Complex.exp (2 * π * I * (z / tau))) *
            Complex.exp (shintaniDoubleSineProductPhase z tau))) := by ring
    _ = (barnesDoubleGammaInv (z + 1) 1 tau *
          barnesDoubleGammaInv (1 + tau - z) 1 tau *
          (2 * Complex.sin (π * z / tau))) *
        (shintaniF2 z tau *
          (Complex.sqrt I * Complex.exp (π * I / 12 * (tau + tau⁻¹))) *
          shintaniF1 z tau *
          Complex.exp (shintaniDoubleSineProductPhase (z + 1) tau)) := by
      rw [hphase]
      ring
    _ = _ := by
      rw [hgamma]
      ring

/-- `N(z+τ) D(z) = N(z) D(z+τ)` for every `z`, from the denominator-cleared reflection law
`barnesDoubleGammaInv_reflect_add_tau` and the two product shifts. -/
private lemma shintaniGammaSide_add_tau_mul (z tau : ℂ) (htau : 0 < tau.im) :
    shintaniGammaSide (z + tau) tau * shintaniProductSide z tau =
      shintaniGammaSide z tau * shintaniProductSide (z + tau) tau := by
  have hgamma := barnesDoubleGammaInv_reflect_add_tau z tau (Or.inr htau.ne')
  have hphase := shintani_phase_add_tau z tau htau
  have hf₁ := shintaniF1_add_tau z tau htau
  unfold shintaniGammaSide shintaniProductSide
  rw [shintaniF2_add_tau z tau htau,
    show 1 + tau - (z + tau) = 1 - z by ring]
  rw [← hf₁]
  calc
    _ = (barnesDoubleGammaInv (z + tau) 1 tau *
          barnesDoubleGammaInv (1 + tau - z) 1 tau) *
        (shintaniF2 z tau *
          (Complex.sqrt I * Complex.exp (π * I / 12 * (tau + tau⁻¹))) *
          shintaniF1 (z + tau) tau *
          ((1 - Complex.exp (2 * π * I * z)) *
            Complex.exp (shintaniDoubleSineProductPhase z tau))) := by ring
    _ = (barnesDoubleGammaInv (z + tau) 1 tau *
          barnesDoubleGammaInv (1 + tau - z) 1 tau *
          (2 * Complex.sin (π * z))) *
        (shintaniF2 z tau *
          (Complex.sqrt I * Complex.exp (π * I / 12 * (tau + tau⁻¹))) *
          shintaniF1 (z + tau) tau *
          Complex.exp (shintaniDoubleSineProductPhase (z + tau) tau)) := by
      rw [hphase]
      ring
    _ = _ := by
      rw [hgamma]
      ring

/-! ### The entire quotient and Liouville's theorem -/

/-- The quotient `N/D` with its removable singularities at the zeros of `D` filled in. -/
private def shintaniQuotient (tau : ℂ) : ℂ → ℂ :=
  removableQuotient (fun z => shintaniGammaSide z tau) (fun z => shintaniProductSide z tau)
    {z | shintaniProductSide z tau = 0}

/-- The filled quotient is entire, by `differentiable_removableQuotient`. -/
private lemma shintaniQuotient_differentiable (tau : ℂ) (htau : 0 < tau.im) :
    Differentiable ℂ (shintaniQuotient tau) := by
  apply differentiable_removableQuotient
    (shintaniGammaSide_differentiable tau htau)
    (shintaniProductSide_differentiable tau htau)
  · intro z hz
    exact hz
  · intro z hz
    exact gammaSide_eq_zero_of_productSide_eq_zero z tau htau hz
  · intro z hz
    exact hz
  · intro z hz
    exact deriv_shintaniProductSide_ne_zero z tau htau hz

/-- The filled quotient is `1`-periodic: off the lattice by `shintaniGammaSide_add_one_mul`, on
it by continuity, since the lattice is discrete. -/
private lemma shintaniQuotient_periodic_one (tau : ℂ) (htau : 0 < tau.im) :
    Function.Periodic (shintaniQuotient tau) 1 := by
  apply periodic_of_forall_not_isPeriodLatticePoint tau htau.ne'
    (shintaniQuotient_differentiable tau htau).continuous
  intro z hz
  have hz1 : ¬ IsPeriodLatticePoint tau (z + 1) :=
    fun h => hz ((isPeriodLatticePoint_add_one_iff tau z).mp h)
  have hDz := shintaniProductSide_ne_zero z tau htau hz
  have hDz1 := shintaniProductSide_ne_zero (z + 1) tau htau hz1
  unfold shintaniQuotient
  rw [removableQuotient_of_not_mem _ _ (by simpa),
    removableQuotient_of_not_mem _ _ (by simpa)]
  exact (div_eq_div_iff hDz1 hDz).2 (shintaniGammaSide_add_one_mul z tau htau)

/-- The filled quotient is `τ`-periodic: off the lattice by `shintaniGammaSide_add_tau_mul`, on
it by continuity, since the lattice is discrete. -/
private lemma shintaniQuotient_periodic_tau (tau : ℂ) (htau : 0 < tau.im) :
    Function.Periodic (shintaniQuotient tau) tau := by
  apply periodic_of_forall_not_isPeriodLatticePoint tau htau.ne'
    (shintaniQuotient_differentiable tau htau).continuous
  intro z hz
  have hzτ : ¬ IsPeriodLatticePoint tau (z + tau) :=
    fun h => hz ((isPeriodLatticePoint_add_tau_iff tau z).mp h)
  have hDz := shintaniProductSide_ne_zero z tau htau hz
  have hDzτ := shintaniProductSide_ne_zero (z + tau) tau htau hzτ
  unfold shintaniQuotient
  rw [removableQuotient_of_not_mem _ _ (by simpa),
    removableQuotient_of_not_mem _ _ (by simpa)]
  exact (div_eq_div_iff hDzτ hDz).2 (shintaniGammaSide_add_tau_mul z tau htau)

/-- The filled quotient is `1` at the origin: on a punctured neighborhood of `0` it equals
`(S₂(z;1,τ)/z) / (S₂^prod(z,τ)/z)`, both factors tend to `2π/√τ ≠ 0`, and the quotient is
continuous at `0`. -/
private lemma shintaniQuotient_zero (tau : ℂ) (htau : 0 < tau.im) :
    shintaniQuotient tau 0 = 1 := by
  have htau0 : tau ≠ 0 := fun h => by simp [h] at htau
  have hsqrtTau : Complex.sqrt tau ≠ 0 := by
    rw [Complex.sqrt, Complex.cpow_ne_zero_iff]
    exact Or.inl htau0
  have hlimit : 2 * (π : ℂ) / Complex.sqrt tau ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) hsqrtTau
  have heq : shintaniQuotient tau =ᶠ[𝓝[≠] 0]
      (fun z => (shintaniDoubleSineGamma z tau / z) /
        (shintaniDoubleSineProduct z tau / z)) := by
    filter_upwards [eventually_not_isPeriodLatticePoint tau htau.ne' 0] with z hz
    have hz0 : z ≠ 0 := fun h => hz (h ▸ isPeriodLatticePoint_zero tau)
    have hlattice := (not_isPeriodLatticePoint_iff tau z).mp hz
    have hf₂ := shintaniF2_ne_zero_of_not_mem_lattice z tau htau hlattice
    have hD := shintaniProductSide_ne_zero z tau htau hz
    have hgamma : barnesDoubleGammaInv (1 + tau - z) 1 tau ≠ 0 :=
      fun h => hD ((shintaniProductSide_eq_zero_iff z tau).mpr (Or.inl h))
    unfold shintaniQuotient
    rw [removableQuotient_of_not_mem _ _ (by simpa using hD)]
    unfold shintaniGammaSide shintaniProductSide shintaniDoubleSineGamma
      barnesDoubleSineGamma shintaniDoubleSineProduct
    field_simp
  have hratio : Tendsto
      (fun z => (shintaniDoubleSineGamma z tau / z) /
        (shintaniDoubleSineProduct z tau / z))
      (𝓝[≠] 0) (𝓝 1) := by
    have hfun :
        (fun z => (shintaniDoubleSineGamma z tau / z) /
          (shintaniDoubleSineProduct z tau / z)) =
        (fun z => shintaniDoubleSineGamma z tau / z) /
          (fun z => shintaniDoubleSineProduct z tau / z) := by
      funext z
      simp
    rw [hfun]
    simpa only [div_self hlimit] using
      (tendsto_shintaniDoubleSineGamma_div tau htau).div
        (tendsto_shintaniDoubleSineProduct_div tau htau) hlimit
  have hpunctured : Tendsto (shintaniQuotient tau) (𝓝[≠] 0) (𝓝 1) :=
    hratio.congr' heq.symm
  have hcontinuous : Tendsto (shintaniQuotient tau) (𝓝[≠] 0)
      (𝓝 (shintaniQuotient tau 0)) :=
    (shintaniQuotient_differentiable tau htau).continuous.continuousAt.mono_left inf_le_left
  exact tendsto_nhds_unique hcontinuous hpunctured

/-- The filled quotient is identically `1`, by Liouville's theorem for doubly periodic entire
functions and its value at the origin. -/
private lemma shintaniQuotient_eq_one (tau : ℂ) (htau : 0 < tau.im) (z : ℂ) :
    shintaniQuotient tau z = 1 := by
  rw [apply_eq_apply_of_differentiable_of_periodic tau htau.ne'
    (shintaniQuotient_differentiable tau htau) (shintaniQuotient_periodic_one tau htau)
    (shintaniQuotient_periodic_tau tau htau) z 0, shintaniQuotient_zero tau htau]

/-! ### Shintani's Proposition 5 -/

/-- **Shintani's product formula for the double sine, cleared of denominators**
[95, Shintani (1977), Proposition 5], with periods `(1, τ)`, `Im τ > 0`:

```text
Γ₂(z;1,τ)⁻¹ f₂(z,τ) = Γ₂(1+τ-z;1,τ)⁻¹ √i exp(πi(τ+τ⁻¹)/12) f₁(z,τ) exp(P(z,τ))
```

for every `z ∈ ℂ`, where `P(z,τ) = πi/2 (z²/τ - (1+τ⁻¹)z)`. This is the identity of entire
functions behind the source's meromorphic identity `S₂ = S₂^prod`. -/
@[source "95, Proposition 5, p. 181 (periods (1, τ), cleared of denominators)"]
theorem barnesDoubleGammaInv_mul_shintaniF2_eq (z tau : ℂ) (htau : 0 < tau.im) :
    barnesDoubleGammaInv z 1 tau * shintaniF2 z tau =
      barnesDoubleGammaInv (1 + tau - z) 1 tau *
        (Complex.sqrt I * Complex.exp (π * I / 12 * (tau + tau⁻¹)) * shintaniF1 z tau *
          Complex.exp (shintaniDoubleSineProductPhase z tau)) := by
  have hmul := mul_removableQuotient
    (N := fun w => shintaniGammaSide w tau)
    (D := fun w => shintaniProductSide w tau)
    (Z := {w | shintaniProductSide w tau = 0})
    (fun w hw => hw)
    (fun w hw => gammaSide_eq_zero_of_productSide_eq_zero w tau htau hw)
    (fun _ hw => hw) z
  change shintaniProductSide z tau * shintaniQuotient tau z =
    shintaniGammaSide z tau at hmul
  rw [shintaniQuotient_eq_one tau htau z, mul_one] at hmul
  simpa only [shintaniGammaSide, shintaniProductSide] using hmul.symm

/-- **Shintani's product formula for the double sine** [95, Shintani (1977), Proposition 5],
with periods `(1, τ)`, `Im τ > 0`: `S₂(z;1,τ) = S₂^prod(z,τ)` wherever the displayed
denominators `Γ₂(1+τ-z;1,τ)⁻¹` of the gamma ratio and `f₂(z,τ)` of the product are nonzero.
This is the quotient form of `barnesDoubleGammaInv_mul_shintaniF2_eq`; see also
[72, Kopp (2024), Theorem 4.23, `thm:shin5`]. -/
@[source "95, Proposition 5, p. 181 (periods (1, τ))"]
theorem shintaniDoubleSineGamma_eq_product (z tau : ℂ) (htau : 0 < tau.im)
    (hf₂ : shintaniF2 z tau ≠ 0) (hΓ : barnesDoubleGammaInv (1 + tau - z) 1 tau ≠ 0) :
    shintaniDoubleSineGamma z tau = shintaniDoubleSineProduct z tau := by
  unfold shintaniDoubleSineGamma barnesDoubleSineGamma shintaniDoubleSineProduct
  apply (div_eq_iff hΓ).2
  rw [show Complex.sqrt I * Complex.exp (π * I / 12 * (tau + tau⁻¹)) *
        (shintaniF1 z tau / shintaniF2 z tau) *
        Complex.exp (shintaniDoubleSineProductPhase z tau) *
        barnesDoubleGammaInv (1 + tau - z) 1 tau =
      (barnesDoubleGammaInv (1 + tau - z) 1 tau *
        (Complex.sqrt I * Complex.exp (π * I / 12 * (tau + tau⁻¹)) *
          shintaniF1 z tau * Complex.exp (shintaniDoubleSineProductPhase z tau))) /
        shintaniF2 z tau by
      simp only [div_eq_mul_inv]
      ring]
  apply (eq_div_iff hf₂).2
  exact barnesDoubleGammaInv_mul_shintaniF2_eq z tau htau

/-- Off the period lattice `ℤ + ℤτ`, the double-gamma ratio equals Shintani's normalized
product. This specializes `shintaniDoubleSineGamma_eq_product` to the domain
where both denominators are known to be nonzero. -/
theorem shintaniDoubleSineGamma_eq_product_of_forall_ne (z tau : ℂ)
    (htau : 0 < tau.im) (hz : ∀ m n : ℤ, z ≠ m + n * tau) :
    shintaniDoubleSineGamma z tau = shintaniDoubleSineProduct z tau := by
  have hlattice : ¬ IsPeriodLatticePoint tau z :=
    (not_isPeriodLatticePoint_iff tau z).mpr hz
  have hf₂ := shintaniF2_ne_zero_of_not_mem_lattice z tau htau hz
  have hD := shintaniProductSide_ne_zero z tau htau hlattice
  have hΓ : barnesDoubleGammaInv (1 + tau - z) 1 tau ≠ 0 :=
    fun h => hD ((shintaniProductSide_eq_zero_iff z tau).mpr (Or.inl h))
  exact shintaniDoubleSineGamma_eq_product z tau htau hf₂ hΓ

end SIC

end
