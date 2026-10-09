/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.ClosedForm
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.Telescoping

/-!
# The five-term integral of the difference kernels

The difference kernels are five-term kernels at shifted parameters, and the principal five-term
closed form at those parameters is `ε^{1/2} E(u+v)/(E(u)E(v))` at the source lattice arguments.

This module follows the last lines of the proof of [RW26, Radchenko, Wheeler (2026), Theorem 2,
`thm:fg.equs`, Section 3.2], which evaluate the telescoped integral by Theorem 3,
`thm:5term.mod.fad`, equation (23), `eq:5term.int`, at `γ = A_d`, `τ = ρ_d`, `ε = ρ_d³`,
`A_d = [[a, b], [c, 1-d]]`.

## The argument

The difference kernel `J_m(z) = (1 - q^p e(y)) Φ_{m+1,0}(z)/Φ_{m+p,1}(z+y) · e(phase)` is
`1 - q^p e(y)` times the five-term kernel at the parameters `(ℓ, p - a, w, y + aρ_d + b)`,
since `Φ_{m+p-a,0}(z + y + aρ_d + b) = Φ_{m+p,1}(z+y)` by the lattice shift laws, and
`aρ_d + b = (aε - 1)/c` is real. At these parameters the upper rate is unchanged, the lower rate
drops by `1/ε`, and lattice-freeness of `w`, `y'`, `w + y'` follows from that of `z_u`, `z_v`,
`z_{u+v}` off the zero class; these are the hypotheses under which Theorem 3 evaluates the line
integral of the difference sum. The closed form is
`Φ_{0,0}(0) Φ_{p+ℓ,1}(w+y)/(Φ_{p,1}(y)Φ_{ℓ,1}(w))`, and at the lattice arguments equation (16),
`eq:faddeevperiod`, moves the second indices to `0`: `Φ_{ℓ,1}(z_u) = Φ_{u₁,0}(z_u)`,
`(1 - q^p e(y))/Φ_{p,1}(z_v) = 1/Φ_{p+1,1}(z_v) = 1/Φ_{v₁,0}(z_v)`, and
`Φ_{p+ℓ,1}(z_{u+v}) = Φ_{u₁+v₁,0}(z_{u+v})`, giving `ε^{1/2} E(u+v)/(E(u)E(v))` with
`Φ_{0,0}(0) = ε^{1/2}/μ_{A_d}`.
-/

noncomputable section

open Complex Filter MeasureTheory
open scoped Topology

namespace SIC

/-! ### The shifted parameters -/

/-- The shifted second parameter `y' = y + aρ_d + b = y + (aε - 1)/c` of the five-term identity
evaluated in the telescoped integral. -/
def principalFiveTermShiftedParameter (d : ℕ) (y : ℝ) : ℝ :=
  y + (((principalA d) 0 0 : ℝ) * principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ)

/-- The shift `aρ_d + b = (aε - 1)/c` is the real number of the shifted parameter, by
`ε = cρ_d + 1 - d` and `ad - bc = 1` (`coe_principalA`, `principalRoot_satisfies_quadratic`). -/
theorem principalFiveTermShiftedParameter_eq (d : ℕ) (hd : 3 < d) (y : ℝ) :
    (principalFiveTermShiftedParameter d y : ℂ) =
      (y : ℂ) + (((principalA d) 0 0 : ℂ) * (principalRoot d : ℂ) + ((principalA d) 0 1 : ℂ)) := by
  have hc : ((principalA d) 1 0 : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (principalA_lowerLeft_pos d hd))
  have hJ : ((principalA d) 1 0 : ℝ) * principalRoot d +
      ((principalA d) 1 1 : ℝ) = principalRoot d ^ 3 := by
    simpa [principalJacobiFactor, coe_principalA] using
      principalJacobiFactor_eq_principalRoot_pow_three d hd
  have hdet : ((principalA d) 0 0 : ℝ) * ((principalA d) 1 1 : ℝ) -
      ((principalA d) 0 1 : ℝ) * ((principalA d) 1 0 : ℝ) = 1 := by
    simp [coe_principalA]
    ring
  have hreal : (((principalA d) 0 0 : ℝ) * principalRoot d ^ 3 - 1) /
      ((principalA d) 1 0 : ℝ) =
      ((principalA d) 0 0 : ℝ) * principalRoot d + ((principalA d) 0 1 : ℝ) := by
    apply (div_eq_iff hc).2
    linear_combination -((principalA d) 0 0 : ℝ) * hJ + hdet
  simp only [principalFiveTermShiftedParameter, hreal]
  push_cast
  ring

/-- The difference kernel is `1 - q^p e(y)` times the five-term kernel at the parameters
`(ℓ, p - a, w, y')`, as germs: `Φ_{m+p-a,0}(z + y') = Φ_{m+p,1}(z + y)` by
`principalFaddeev_add_lattice_eventuallyEq` with the lattice vector `aρ_d + b`. -/
theorem principalFiveTermDifferenceKernel_eventuallyEq (d : ℕ) (hd : 3 < d)
    (ℓ p : ℤ) (w y : ℝ) (m : ℤ) (z : ℂ) :
    principalFiveTermDifferenceKernel d ℓ p w y m =ᶠ[𝓝[≠] z]
      (fun ζ => (1 - Complex.exp (2 * Real.pi * I * ((y : ℂ) + p * (principalRoot d : ℂ)))) *
        principalFiveTermKernel d ℓ (p - (principalA d) 0 0) w
          (principalFiveTermShiftedParameter d y) m ζ) := by
  have ht : Tendsto (fun ζ : ℂ => ζ + (y : ℂ)) (𝓝[≠] z) (𝓝[≠] (z + y)) := by
    simpa only [Function.id_def] using
      ((hasDerivAt_id z).add_const (y : ℂ)).tendsto_nhdsNE one_ne_zero
  have hshift := (principalFaddeev_add_lattice_eventuallyEq d hd
    (m + p - (principalA d) 0 0) 0 ((principalA d) 0 0) ((principalA d) 0 1)
    (z + y)).comp_tendsto ht
  filter_upwards [hshift] with ζ hζ
  have hden : principalFaddeev d
      (m + p - (principalA d) 0 0) 0
      (ζ + (principalFiveTermShiftedParameter d y : ℂ)) =
      principalFaddeev d (m + p) 1 (ζ + y) := by
    convert hζ using 1 <;>
      simp [principalFiveTermShiftedParameter_eq d hd y] <;> ring_nf
  simp only [principalFiveTermDifferenceKernel, principalFiveTermKernel]
  rw [show m + (p - (principalA d) 0 0) = m + p - (principalA d) 0 0 by omega,
    ← hden]
  ring

/-- On a vertical line the difference sum equals, almost everywhere, `1 - q^p e(y)` times the
sum of the shifted five-term kernels on the translated crossings. -/
theorem ae_principalFiveTermDifferenceSum_eq (d : ℕ) (hd : 3 < d) (ℓ p : ℤ) (w y x : ℝ) :
    ∀ᵐ t : ℝ,
      principalFiveTermDifferenceSum d ℓ p w y ((x : ℂ) + t * I) =
        (1 - Complex.exp (2 * Real.pi * I * ((y : ℂ) + p * (principalRoot d : ℂ)))) *
          ∑ m : FiveTermIndex (principalA d),
            principalFiveTermKernel d ℓ (p - (principalA d) 0 0) w
              (principalFiveTermShiftedParameter d y) ((m : ℕ) : ℤ)
              (((x - ((m : ℕ) : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ) : ℝ) : ℂ) +
                t * I) := by
  have h_each (m : FiveTermIndex (principalA d)) :
      ∀ᵐ t : ℝ, principalFiveTermDifferenceKernel d ℓ p w y ((m : ℕ) : ℤ)
          (((x : ℂ) + t * I) -
            ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 / ((principalA d) 1 0 : ℂ)) =
        (1 - Complex.exp (2 * Real.pi * I * ((y : ℂ) + p * (principalRoot d : ℂ)))) *
          principalFiveTermKernel d ℓ (p - (principalA d) 0 0) w
            (principalFiveTermShiftedParameter d y) ((m : ℕ) : ℤ)
            (((x - ((m : ℕ) : ℝ) * principalRoot d ^ 3 /
              ((principalA d) 1 0 : ℝ) : ℝ) : ℂ) + t * I) := by
    have h := ae_eq_comp_affine_of_forall_eventuallyEq_nhdsNE
      (fun z => principalFiveTermDifferenceKernel_eventuallyEq d hd ℓ p w y
        ((m : ℕ) : ℤ) z) I
      (x - ((m : ℕ) : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ)) I_ne_zero
    filter_upwards [h] with t ht
    convert ht using 1 <;> push_cast <;> ring_nf
  filter_upwards [Filter.eventually_all.mpr h_each] with t ht
  simp only [principalFiveTermDifferenceSum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  exact ht m

/-! ### The integral identity at the shifted parameters -/

/-- The shift by `aρ_d+b` decreases the lower decay rate by `ρ_d⁻³`. -/
theorem principalFiveTermLowerRate_shifted (d : ℕ) (hd : 3 < d)
    (ℓ p : ℤ) (w y : ℝ) :
    principalFiveTermLowerRate d ℓ (p - (principalA d) 0 0) w
        (principalFiveTermShiftedParameter d y) =
      principalFiveTermLowerRate d ℓ p w y - 1 / principalRoot d ^ 3 := by
  have hε : principalRoot d ^ 3 ≠ 0 :=
    ne_of_gt (pow_pos (principalRoot_pos d hd) _)
  have hc : ((principalA d) 1 0 : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (principalA_lowerLeft_pos d hd))
  have hentry : ((principalA d) 1 0 : ℝ) = (d : ℝ) * ((d : ℝ) - 2) := by
    simp [coe_principalA]
  have hcore (a c e l q w y : ℝ) (hc : c ≠ 0) (he : e ≠ 0) :
      c * (w + (y + (a * e - 1) / c)) / e + l + (q - a) - 1 =
        c * (w + y) / e + l + q - 1 - 1 / e := by
    field_simp [hc, he]
    ring
  simpa only [principalFiveTermLowerRate, principalFiveTermShiftedParameter,
    Int.cast_sub, hentry] using
    hcore (((principalA d) 0 0 : ℤ) : ℝ) ((principalA d) 1 0 : ℝ)
      (principalRoot d ^ 3) ℓ p w y hc hε

/-- Off the zero class, the shifted source argument remains outside `ℤ+ℤρ_d`. -/
theorem not_isPeriodLatticePoint_shiftedParameter (d : ℕ) (hd : 3 < d)
    (v₁ v₂ : ℤ) (hv : principalFiveTermCharacteristicResidue d v₁ v₂ ≠ 0) :
    ¬ IsPeriodLatticePoint (principalRoot d : ℂ)
      (principalFiveTermShiftedParameter d (principalFiveTermLatticeArgument d v₁ v₂) : ℂ) := by
  rw [principalFiveTermShiftedParameter_eq d hd, ← add_assoc,
    isPeriodLatticePoint_add_int_mul_add_int_iff]
  exact (not_isPeriodLatticePoint_latticeArgument_iff d hd v₁ v₂).2 hv

/-- Adding a shifted lattice argument preserves lattice-freeness of the source sum. -/
private theorem not_isPeriodLatticePoint_shiftedSum (d : ℕ) (hd : 3 < d)
    (u₁ u₂ v₁ v₂ : ℤ)
    (huv : principalFiveTermCharacteristicResidue d (u₁ + v₁) (u₂ + v₂) ≠ 0) :
    ¬ IsPeriodLatticePoint (principalRoot d : ℂ)
      ((principalFiveTermLatticeArgument d u₁ u₂ : ℂ) +
        (principalFiveTermShiftedParameter d (principalFiveTermLatticeArgument d v₁ v₂) : ℂ)) := by
  rw [principalFiveTermShiftedParameter_eq d hd]
  simp only [← add_assoc, ← Complex.ofReal_add,
    ← principalFiveTermLatticeArgument_add d u₁ u₂ v₁ v₂,
    isPeriodLatticePoint_add_int_mul_add_int_iff]
  exact (not_isPeriodLatticePoint_latticeArgument_iff d hd
    (u₁ + v₁) (u₂ + v₂)).2 huv

/-- Integrating the almost-everywhere kernel equality gives the shifted finite integral sum. -/
theorem integral_principalFiveTermDifferenceSum_eq
    (d : ℕ) (hd : 3 < d) (ℓ p : ℤ) (w y x : ℝ)
    (hInt : ∀ m : FiveTermIndex (principalA d),
      Integrable (fun t : ℝ =>
        principalFiveTermKernel d ℓ (p - (principalA d) 0 0) w
          (principalFiveTermShiftedParameter d y) ((m : ℕ) : ℤ)
          (((x - ((m : ℕ) : ℝ) * principalRoot d ^ 3 /
            ((principalA d) 1 0 : ℝ) : ℝ) : ℂ) + t * I))) :
    (∫ t : ℝ, principalFiveTermDifferenceSum d ℓ p w y ((x : ℂ) + t * I) * I) =
      (1 - Complex.exp (2 * Real.pi * I * ((y : ℂ) + p * (principalRoot d : ℂ)))) *
        principalFiveTermIntegralSum d ℓ (p - (principalA d) 0 0) w
          (principalFiveTermShiftedParameter d y)
          (fun m => x - ((m : ℕ) : ℝ) * principalRoot d ^ 3 /
            ((principalA d) 1 0 : ℝ)) := by
  have hAE := ae_principalFiveTermDifferenceSum_eq d hd ℓ p w y x
  calc
    _ = ∫ t : ℝ,
        ((1 - Complex.exp (2 * Real.pi * I * ((y : ℂ) + p * (principalRoot d : ℂ)))) *
          ∑ m : FiveTermIndex (principalA d),
            principalFiveTermKernel d ℓ (p - (principalA d) 0 0) w
              (principalFiveTermShiftedParameter d y) ((m : ℕ) : ℤ)
              (((x - ((m : ℕ) : ℝ) * principalRoot d ^ 3 /
                ((principalA d) 1 0 : ℝ) : ℝ) : ℂ) + t * I)) * I :=
      integral_congr_ae (hAE.mono fun t ht => congrArg (· * I) ht)
    _ = _ := by
      rw [integral_mul_const, integral_const_mul,
        MeasureTheory.integral_finsetSum Finset.univ (by intro m hm; exact hInt m)]
      rw [principalFiveTermIntegralSum_def, mul_assoc, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro m hm
      ring

/-- The shifted lower rate is negative whenever the original rate is negative. -/
theorem principalFiveTermLowerRate_shifted_neg (d : ℕ) (hd : 3 < d)
    (ℓ p : ℤ) (w y : ℝ) (hlower : principalFiveTermLowerRate d ℓ p w y < 0) :
    principalFiveTermLowerRate d ℓ (p - (principalA d) 0 0) w
      (principalFiveTermShiftedParameter d y) < 0 := by
  rw [principalFiveTermLowerRate_shifted d hd]
  have hε : 0 < principalRoot d ^ 3 := pow_pos (principalRoot_pos d hd) _
  have : 0 < 1 / principalRoot d ^ 3 := one_div_pos.mpr hε
  linarith

/-! ### The closed form at the lattice arguments -/

/-- Shifting the argument by `aρ_d+b` changes `(m-a,0)` to `(m,1)`. -/
private theorem principalFaddeev_add_principalMatrixShift
    (d : ℕ) (hd : 3 < d) (m : ℤ) (z : ℂ)
    (hz : ¬ IsPeriodLatticePoint (principalRoot d : ℂ) z) :
    principalFaddeev d (m - (principalA d) 0 0) 0
        (z + (((principalA d) 0 0 : ℂ) * (principalRoot d : ℂ) +
          ((principalA d) 0 1 : ℂ))) =
      principalFaddeev d m 1 z := by
  have h := principalFaddeev_add_lattice_of_notMem d hd
    (m - (principalA d) 0 0) 0 ((principalA d) 0 0) ((principalA d) 0 1) z hz
  convert h using 1
  all_goals simp [coe_principalA]
  all_goals ring_nf

/-- Equation (16) identifies the adjacent diagonal indices at a source lattice argument. -/
private theorem principalFaddeev_lattice_indices_one
    (d : ℕ) (hd : 3 < d) (u₁ u₂ : ℤ)
    (hu : principalFiveTermCharacteristicResidue d u₁ u₂ ≠ 0) :
    principalFaddeev d (u₁ + 1) 1 (principalFiveTermLatticeArgument d u₁ u₂) =
      principalFaddeev d u₁ 0 (principalFiveTermLatticeArgument d u₁ u₂) := by
  have hz := (not_isPeriodLatticePoint_latticeArgument_iff d hd u₁ u₂).2 hu
  have hshift := etaMultiplier_mul_principalFaddeevContinued_indices_add
    d hd u₁ u₂ 1
  have hbase := etaMultiplier_mul_principalFaddeevContinued_indices_add
    d hd u₁ u₂ 0
  rw [principalFaddeevContinued_eq_of_notMem d hd _ _ _ hz] at hshift hbase
  simp only [principalDilogEMinus_of_ne_zero d hd hu, ite_self] at hshift hbase
  exact mul_left_cancel₀ (etaMultiplier_ne_zero (principalA d))
    (hshift.trans (by simpa only [add_zero] using hbase.symm))

/-- The left index shift absorbs `1-e(z_v+v₁ρ_d)` into the denominator product. -/
private theorem principalFiveTerm_factor_div_product (d : ℕ) (hd : 3 < d)
    (v₁ v₂ : ℤ) (hv : principalFiveTermCharacteristicResidue d v₁ v₂ ≠ 0) :
    (1 - Complex.exp (2 * Real.pi * I *
      ((principalFiveTermLatticeArgument d v₁ v₂ : ℂ) + v₁ * (principalRoot d : ℂ)))) /
        principalFaddeev d v₁ 1 (principalFiveTermLatticeArgument d v₁ v₂) =
      1 / principalFaddeev d v₁ 0
        (principalFiveTermLatticeArgument d v₁ v₂) := by
  have hz := (not_isPeriodLatticePoint_latticeArgument_iff d hd v₁ v₂).2 hv
  have hreg := (principalFaddeevGammaRegular_of_notMem d hd
    (v₁ + 1) 1 _ hz).last
  have hgamma : barnesDoubleGammaInv
      (-((principalFiveTermLatticeArgument d v₁ v₂ : ℂ) + v₁ * (principalRoot d : ℂ)))
      1 (principalRoot d) ≠ 0 := by
    convert hreg using 1
    all_goals push_cast
    all_goals ring_nf
  have hshift := principalFaddeev_index_add_one_left d hd v₁ 1
    (principalFiveTermLatticeArgument d v₁ v₂) hgamma
  have hdiag := principalFaddeev_lattice_indices_one d hd v₁ v₂ hv
  rw [← hdiag]
  apply (div_eq_div_iff
    (principalFaddeev_ne_zero_of_notMem d hd v₁ 1 _ hz)
    (principalFaddeev_ne_zero_of_notMem d hd (v₁ + 1) 1 _ hz)).2
  simpa [mul_comm] using hshift

/-- The matrix shift evaluates a product at the shifted source argument. -/
private theorem principalFaddeev_shifted_latticeArgument
    (d : ℕ) (hd : 3 < d) (m u₁ u₂ : ℤ)
    (hu : principalFiveTermCharacteristicResidue d u₁ u₂ ≠ 0) :
    principalFaddeev d (m - (principalA d) 0 0) 0
        (principalFiveTermShiftedParameter d (principalFiveTermLatticeArgument d u₁ u₂)) =
      principalFaddeev d m 1 (principalFiveTermLatticeArgument d u₁ u₂) := by
  rw [principalFiveTermShiftedParameter_eq d hd]
  exact principalFaddeev_add_principalMatrixShift d hd m _
    ((not_isPeriodLatticePoint_latticeArgument_iff d hd u₁ u₂).2 hu)

/-- The matrix shift evaluates the numerator product at `z_{u+v}`. -/
private theorem principalFaddeev_shifted_latticeSum
    (d : ℕ) (hd : 3 < d) (u₁ u₂ v₁ v₂ : ℤ)
    (huv : principalFiveTermCharacteristicResidue d (u₁ + v₁) (u₂ + v₂) ≠ 0) :
    principalFaddeev d ((v₁ - (principalA d) 0 0) + (u₁ + 1)) 0
        ((principalFiveTermLatticeArgument d u₁ u₂ : ℂ) +
          (principalFiveTermShiftedParameter d (principalFiveTermLatticeArgument d v₁ v₂) : ℂ)) =
      principalFaddeev d (u₁ + v₁ + 1) 1
        (principalFiveTermLatticeArgument d (u₁ + v₁) (u₂ + v₂)) := by
  have harg : (principalFiveTermLatticeArgument d u₁ u₂ : ℂ) +
      (principalFiveTermShiftedParameter d (principalFiveTermLatticeArgument d v₁ v₂) : ℂ) =
      (principalFiveTermLatticeArgument d (u₁ + v₁) (u₂ + v₂) : ℂ) +
        (((principalA d) 0 0 : ℂ) * (principalRoot d : ℂ) + ((principalA d) 0 1 : ℂ)) := by
    rw [principalFiveTermShiftedParameter_eq d hd]
    simp only [← add_assoc, ← Complex.ofReal_add,
      ← principalFiveTermLatticeArgument_add d u₁ u₂ v₁ v₂]
  rw [harg]
  simpa only [show (v₁ - (principalA d) 0 0) + (u₁ + 1) =
    u₁ + v₁ + 1 - (principalA d) 0 0 by omega] using
    (principalFaddeev_add_principalMatrixShift d hd (u₁ + v₁ + 1) _
      ((not_isPeriodLatticePoint_latticeArgument_iff d hd _ _).2 huv))

/-- The shifted closed form reduces to three products at the source lattice arguments. -/
private theorem closedForm_shifted_eq_products
    (d : ℕ) (hd : 3 < d) (u₁ u₂ v₁ v₂ : ℤ)
    (hu0 : principalFiveTermCharacteristicResidue d u₁ u₂ ≠ 0)
    (hv0 : principalFiveTermCharacteristicResidue d v₁ v₂ ≠ 0)
    (huv0 : principalFiveTermCharacteristicResidue d (u₁ + v₁) (u₂ + v₂) ≠ 0) :
    (1 - Complex.exp (2 * Real.pi * I *
        ((principalFiveTermLatticeArgument d v₁ v₂ : ℂ) + v₁ * (principalRoot d : ℂ)))) *
      principalFiveTermClosedForm d (u₁ + 1) (v₁ - (principalA d) 0 0)
        (principalFiveTermLatticeArgument d u₁ u₂)
        (principalFiveTermShiftedParameter d (principalFiveTermLatticeArgument d v₁ v₂)) =
      (Real.sqrt (principalRoot d ^ 3) : ℂ) / etaMultiplier (principalA d) *
        (principalFaddeev d (u₁ + v₁) 0
          (principalFiveTermLatticeArgument d (u₁ + v₁) (u₂ + v₂)) /
          (principalFaddeev d v₁ 0 (principalFiveTermLatticeArgument d v₁ v₂) *
            principalFaddeev d u₁ 0 (principalFiveTermLatticeArgument d u₁ u₂))) := by
  rw [principalFiveTermClosedForm_eq_etaMultiplier d hd,
    principalFaddeev_shifted_latticeSum d hd u₁ u₂ v₁ v₂ huv0,
    principalFaddeev_shifted_latticeArgument d hd v₁ v₁ v₂ hv0,
    principalFaddeev_lattice_indices_one d hd (u₁ + v₁) (u₂ + v₂) huv0,
    principalFaddeev_lattice_indices_one d hd u₁ u₂ hu0]
  exact FiniteFiveTerm.closedForm_algebra _ _ _ _ _ _ _
    (principalFiveTerm_factor_div_product d hd v₁ v₂ hv0)

/-- **The shifted closed form in the finite dilogarithm values.** For `u`, `v`, `u + v` off the
zero class,
`(1 - q^{v₁} e(z_v)) Φ_{0,0}(0) Φ_{u₁+v₁+1-a,0}(z_u + y')/(Φ_{v₁-a,0}(y') Φ_{u₁+1,1}(z_u))`
equals `ε^{1/2} E(u+v)/(E(u) E(v))`, by the lattice shift to second index `1`, equation (16),
`eq:faddeevperiod`, at the three lattice arguments
(`principalFaddeev_indices_add`), the left index shift
`principalFaddeev_index_add_one_left`, and
`principalDilogE_characteristicResidue`. This is the final evaluation in the
proof of [RW26, Radchenko, Wheeler (2026), Theorem 2, `thm:fg.equs`, Section 3.2]. -/
theorem principalFiveTermClosedForm_shifted_eq (d : ℕ) (hd : 3 < d) (u₁ u₂ v₁ v₂ : ℤ)
    (hu0 : principalFiveTermCharacteristicResidue d u₁ u₂ ≠ 0)
    (hv0 : principalFiveTermCharacteristicResidue d v₁ v₂ ≠ 0)
    (huv0 : principalFiveTermCharacteristicResidue d (u₁ + v₁) (u₂ + v₂) ≠ 0) :
    (1 - Complex.exp (2 * Real.pi * I *
        ((principalFiveTermLatticeArgument d v₁ v₂ : ℂ) + v₁ * (principalRoot d : ℂ)))) *
      principalFiveTermClosedForm d (u₁ + 1) (v₁ - (principalA d) 0 0)
        (principalFiveTermLatticeArgument d u₁ u₂)
        (principalFiveTermShiftedParameter d (principalFiveTermLatticeArgument d v₁ v₂)) =
      (Real.sqrt (principalRoot d ^ 3) : ℂ) *
        principalDilogE d (principalFiveTermCharacteristicResidue d (u₁ + v₁) (u₂ + v₂)) /
          (principalDilogE d (principalFiveTermCharacteristicResidue d u₁ u₂) *
            principalDilogE d (principalFiveTermCharacteristicResidue d v₁ v₂)) := by
  have hμ := etaMultiplier_ne_zero (principalA d)
  have huF := principalFaddeev_ne_zero_of_notMem d hd u₁ 0 _
    ((not_isPeriodLatticePoint_latticeArgument_iff d hd _ _).2 hu0)
  have hvF := principalFaddeev_ne_zero_of_notMem d hd v₁ 0 _
    ((not_isPeriodLatticePoint_latticeArgument_iff d hd _ _).2 hv0)
  calc
    _ = (Real.sqrt (principalRoot d ^ 3) : ℂ) / etaMultiplier (principalA d) *
        (principalFaddeev d (u₁ + v₁) 0
          (principalFiveTermLatticeArgument d (u₁ + v₁) (u₂ + v₂)) /
          (principalFaddeev d v₁ 0 (principalFiveTermLatticeArgument d v₁ v₂) *
            principalFaddeev d u₁ 0 (principalFiveTermLatticeArgument d u₁ u₂))) :=
      closedForm_shifted_eq_products d hd u₁ u₂ v₁ v₂ hu0 hv0 huv0
    _ = _ := by
      rw [principalDilogE_characteristicResidue d hd u₁ u₂ hu0,
        principalDilogE_characteristicResidue d hd v₁ v₂ hv0,
        principalDilogE_characteristicResidue d hd
          (u₁ + v₁) (u₂ + v₂) huv0]
      field_simp [hμ, huF, hvF]

/-! ### The continued shifted value at the zero classes

The literal source origin handles a zero left class. If the sum class is zero, the source
sum `(a-1,b)` makes the shifted numerator the removable origin `Φ_{0,0}(0)`. These choices
supply the same finite quotient as the lattice-free cases, with the correct `F⁻(0)` denominator.
-/

/-- The difference-kernel factor is nonzero at a nonzero source class; used by
`tendsto_closedFormUHPContinued_principalA_shifted`. -/
theorem principalFiveTerm_shifted_factor_ne_zero
    (d : ℕ) (hd : 3 < d) (v₁ v₂ : ℤ)
    (hv : principalFiveTermCharacteristicResidue d v₁ v₂ ≠ 0) :
    (1 : ℂ) - Complex.exp (2 * Real.pi * I *
      ((principalFiveTermLatticeArgument d v₁ v₂ : ℂ) +
        v₁ * (principalRoot d : ℂ))) ≠ 0 := by
  have hlat : SigmaSLatticeFree (principalRoot d)
      (principalFiveTermLatticeArgument d v₁ v₂) :=
    (sigmaSLatticeFree_iff_not_isPeriodLatticePoint _ _).2
      ((not_isPeriodLatticePoint_latticeArgument_iff d hd v₁ v₂).2 hv)
  exact hlat.one_sub_exp_ne_zero v₁

/-- The selected zero-sum source pair places the shifted numerator at the origin; used by
`tendsto_closedFormUHPContinued_principalA_shifted`. -/
private theorem principalFiveTerm_shifted_sum_origin (d : ℕ) (hd : 3 < d)
    (u₁ u₂ v₁ v₂ : ℤ)
    (h₁ : u₁ + v₁ = (principalA d) 0 0 - 1)
    (h₂ : u₂ + v₂ = (principalA d) 0 1) :
    (principalFiveTermLatticeArgument d u₁ u₂ : ℂ) +
      (principalFiveTermShiftedParameter d
        (principalFiveTermLatticeArgument d v₁ v₂) : ℂ) = 0 := by
  have hε : principalRoot d ^ 3 ≠ 0 :=
    ne_of_gt (pow_pos (principalRoot_pos d hd) _)
  have hρ : principalRoot d ≠ 0 := (principalRoot_pos d hd).ne'
  have hε' : (principalRoot d ^ 3)⁻¹ - 1 ≠ 0 := by
    have h := one_lt_principalRoot_pow_three d hd
    exact ne_of_lt (sub_neg.mpr ((inv_lt_one₀ (by positivity)).2 h))
  have hsource : (((principalA d) 0 0 - 1 : ℤ) : ℝ) * principalRoot d +
      ((principalA d) 0 1 : ℝ) =
      (principalRoot d ^ 3 - 1) * principalRoot d := by
    have h := principalA_numerator_principalRoot d hd
    push_cast at h ⊢
    linear_combination h
  have harg : principalFiveTermLatticeArgument d
      ((principalA d) 0 0 - 1) ((principalA d) 0 1) =
      -(((principalA d) 0 0 : ℝ) * principalRoot d +
        ((principalA d) 0 1 : ℝ)) := by
    rw [principalFiveTermLatticeArgument, hsource,
      principalA_numerator_principalRoot d hd]
    apply (div_eq_iff hε').2
    field_simp [hρ]
    ring
  rw [principalFiveTermShiftedParameter_eq d hd]
  simp only [← add_assoc, ← Complex.ofReal_add,
    ← principalFiveTermLatticeArgument_add d u₁ u₂ v₁ v₂, h₁, h₂]
  rw [harg]
  push_cast
  ring

/-- At the literal left origin, the shifted product ratio has the finite value required by
`tendsto_closedFormUHPContinued_principalA_shifted`. -/
private theorem principalFiveTerm_shifted_zero_left_value (d : ℕ) (hd : 3 < d)
    (v₁ v₂ : ℤ) (hv : principalFiveTermCharacteristicResidue d v₁ v₂ ≠ 0) :
    (1 - Complex.exp (2 * Real.pi * I *
      ((principalFiveTermLatticeArgument d v₁ v₂ : ℂ) + v₁ * (principalRoot d : ℂ)))) *
      ((principalRoot d : ℂ) ^ 3 *
        principalFaddeev d (v₁ - (principalA d) 0 0 + 1) 0
          (principalFiveTermShiftedParameter d (principalFiveTermLatticeArgument d v₁ v₂)) /
        principalFaddeev d (v₁ - (principalA d) 0 0) 0
          (principalFiveTermShiftedParameter d (principalFiveTermLatticeArgument d v₁ v₂))) =
      (Real.sqrt (principalRoot d ^ 3) : ℂ) *
        principalDilogE d (principalFiveTermCharacteristicResidue d v₁ v₂) /
          (principalDilogEMinus d 0 *
            principalDilogEMinus d (principalFiveTermCharacteristicResidue d v₁ v₂)) := by
  have hshiftNum := principalFaddeev_shifted_latticeArgument d hd
    (v₁ + 1) v₁ v₂ hv
  have hshiftDen := principalFaddeev_shifted_latticeArgument d hd
    v₁ v₁ v₂ hv
  have hdiag := principalFaddeev_lattice_indices_one d hd v₁ v₂ hv
  have hfactor := principalFiveTerm_factor_div_product d hd v₁ v₂ hv
  have hz := (not_isPeriodLatticePoint_latticeArgument_iff d hd v₁ v₂).2 hv
  have hF : principalFaddeev d v₁ 0
      (principalFiveTermLatticeArgument d v₁ v₂) ≠ 0 :=
    principalFaddeev_ne_zero_of_notMem d hd _ _ _ hz
  have hs : (Real.sqrt (principalRoot d ^ 3) : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (pow_pos (principalRoot_pos d hd) _)
  have hE : principalDilogE d (principalFiveTermCharacteristicResidue d v₁ v₂) ≠ 0 :=
    principalDilogE_ne_zero d hd (principalFiveTermCharacteristicResidue_mem d hd v₁ v₂)
  have hsq : (Real.sqrt (principalRoot d ^ 3) : ℂ) ^ 2 =
      (principalRoot d : ℂ) ^ 3 := by
    exact_mod_cast Real.sq_sqrt (pow_nonneg (le_of_lt (principalRoot_pos d hd)) 3)
  rw [show v₁ - (principalA d) 0 0 + 1 = (v₁ + 1) - (principalA d) 0 0 by omega,
    hshiftNum, hshiftDen, hdiag]
  calc
    _ = (principalRoot d : ℂ) ^ 3 *
        principalFaddeev d v₁ 0 (principalFiveTermLatticeArgument d v₁ v₂) *
          ((1 - Complex.exp (2 * Real.pi * I *
            ((principalFiveTermLatticeArgument d v₁ v₂ : ℂ) +
              v₁ * (principalRoot d : ℂ)))) /
            principalFaddeev d v₁ 1 (principalFiveTermLatticeArgument d v₁ v₂)) := by
      ring
    _ = (principalRoot d : ℂ) ^ 3 := by
      rw [hfactor]
      field_simp [hF]
    _ = _ := by
      rw [principalDilogEMinus_zero,
        principalDilogEMinus_of_ne_zero d hd hv,
        principalJacobiFactor_eq_principalRoot_pow_three d hd]
      field_simp [hs, hE]
      rw [← hsq]
      push_cast
      field_simp [hs]

/-- The removable numerator at the selected zero sum has value `E(0)` in the shifted quotient;
used by `tendsto_closedFormUHPContinued_principalA_shifted`. -/
private theorem principalFiveTerm_shifted_zero_sum_value
    (d : ℕ) (hd : 3 < d) (u₁ u₂ v₁ v₂ : ℤ)
    (hu : principalFiveTermCharacteristicResidue d u₁ u₂ ≠ 0)
    (hv : principalFiveTermCharacteristicResidue d v₁ v₂ ≠ 0)
    (hzero : principalFiveTermCharacteristicResidue d (u₁ + v₁) (u₂ + v₂) = 0)
    (h₁ : u₁ + v₁ = (principalA d) 0 0 - 1)
    (h₂ : u₂ + v₂ = (principalA d) 0 1) :
    (1 - Complex.exp (2 * Real.pi * I *
      ((principalFiveTermLatticeArgument d v₁ v₂ : ℂ) + v₁ * (principalRoot d : ℂ)))) *
      principalFiveTermClosedForm d (u₁ + 1) (v₁ - (principalA d) 0 0)
        (principalFiveTermLatticeArgument d u₁ u₂)
        (principalFiveTermShiftedParameter d (principalFiveTermLatticeArgument d v₁ v₂)) =
      (Real.sqrt (principalRoot d ^ 3) : ℂ) *
        principalDilogE d (principalFiveTermCharacteristicResidue d (u₁ + v₁) (u₂ + v₂)) /
          (principalDilogEMinus d (principalFiveTermCharacteristicResidue d u₁ u₂) *
            principalDilogEMinus d (principalFiveTermCharacteristicResidue d v₁ v₂)) := by
  have harg := principalFiveTerm_shifted_sum_origin d hd u₁ u₂ v₁ v₂ h₁ h₂
  have hidx : (v₁ - (principalA d) 0 0) + (u₁ + 1) = 0 := by omega
  have hshift := principalFaddeev_shifted_latticeArgument d hd v₁ v₁ v₂ hv
  have hdiag := principalFaddeev_lattice_indices_one d hd u₁ u₂ hu
  have hfactor := principalFiveTerm_factor_div_product d hd v₁ v₂ hv
  have hμ := etaMultiplier_ne_zero (principalA d)
  have hFu : principalFaddeev d u₁ 0
      (principalFiveTermLatticeArgument d u₁ u₂) ≠ 0 :=
    principalFaddeev_ne_zero_of_notMem d hd _ _ _
      ((not_isPeriodLatticePoint_latticeArgument_iff d hd u₁ u₂).2 hu)
  have hFv : principalFaddeev d v₁ 0
      (principalFiveTermLatticeArgument d v₁ v₂) ≠ 0 :=
    principalFaddeev_ne_zero_of_notMem d hd _ _ _
      ((not_isPeriodLatticePoint_latticeArgument_iff d hd v₁ v₂).2 hv)
  calc
    _ = (Real.sqrt (principalRoot d ^ 3) : ℂ) / etaMultiplier (principalA d) *
          ((Real.sqrt (principalRoot d ^ 3) : ℂ) / etaMultiplier (principalA d) /
            (principalFaddeev d v₁ 0 (principalFiveTermLatticeArgument d v₁ v₂) *
              principalFaddeev d u₁ 0
                (principalFiveTermLatticeArgument d u₁ u₂))) := by
      rw [principalFiveTermClosedForm_eq_etaMultiplier d hd,
        hidx, harg, principalFaddeev_zero_eq_etaMultiplier d hd,
        hshift, hdiag]
      exact FiniteFiveTerm.closedForm_algebra _ _ _ _ _ _ _ hfactor
    _ = _ := by
      rw [hzero, principalDilogE_zero,
        principalJacobiFactor_eq_principalRoot_pow_three d hd,
        principalDilogEMinus_of_ne_zero d hd hu,
        principalDilogEMinus_of_ne_zero d hd hv,
        principalDilogE_characteristicResidue d hd u₁ u₂ hu,
        principalDilogE_characteristicResidue d hd v₁ v₂ hv]
      field_simp [hμ, hFu, hFv]

/-- The source sum is either lattice-free or the selected removable origin; used by
`tendsto_closedFormUHPContinued_principalA_shifted`. -/
private theorem principalFiveTerm_shifted_sum_admissible (d : ℕ) (hd : 3 < d)
    (u₁ u₂ v₁ v₂ : ℤ)
    (huvZero : principalFiveTermCharacteristicResidue d (u₁ + v₁) (u₂ + v₂) = 0 →
      u₁ + v₁ = (principalA d) 0 0 - 1 ∧ u₂ + v₂ = (principalA d) 0 1) :
    ¬ IsPeriodLatticePoint (principalRoot d : ℂ)
      ((principalFiveTermLatticeArgument d u₁ u₂ : ℂ) +
        (principalFiveTermShiftedParameter d (principalFiveTermLatticeArgument d v₁ v₂) : ℂ)) ∨
      ((principalFiveTermLatticeArgument d u₁ u₂ : ℂ) +
        (principalFiveTermShiftedParameter d (principalFiveTermLatticeArgument d v₁ v₂) : ℂ) =
        0 ∧ (v₁ - (principalA d) 0 0) + (u₁ + 1) = 0) := by
  by_cases hzero : principalFiveTermCharacteristicResidue d (u₁ + v₁) (u₂ + v₂) = 0
  · obtain ⟨h₁, h₂⟩ := huvZero hzero
    exact Or.inr ⟨principalFiveTerm_shifted_sum_origin d hd u₁ u₂ v₁ v₂ h₁ h₂, by omega⟩
  · exact Or.inl (not_isPeriodLatticePoint_shiftedSum d hd u₁ u₂ v₁ v₂ hzero)

/-- The shifted continued closed form in [RW26, Radchenko, Wheeler (2026), Section 3.2,
proof of Theorem 2, `thm:fg.equs`], including the zero left and zero sum classes. The factor
`1-q^{v₁}e(z_v)` multiplies this value in the difference kernel. At a zero left class choose
`u=(0,0)`; at a zero sum choose `u+v=(a-1,b)`, making the shifted numerator the removable
origin. Otherwise use `principalFiveTermClosedForm_shifted_eq`. -/
theorem tendsto_closedFormUHPContinued_principalA_shifted
    (d : ℕ) (hd : 3 < d) (u₁ u₂ v₁ v₂ : ℤ)
    (hv0 : principalFiveTermCharacteristicResidue d v₁ v₂ ≠ 0)
    (huZero : principalFiveTermCharacteristicResidue d u₁ u₂ = 0 → u₁ = 0 ∧ u₂ = 0)
    (huvZero : principalFiveTermCharacteristicResidue d (u₁ + v₁) (u₂ + v₂) = 0 →
      u₁ + v₁ = (principalA d) 0 0 - 1 ∧ u₂ + v₂ = (principalA d) 0 1) :
    Tendsto (fun τ : ℂ => fiveTermClosedFormUHPContinued (principalA d)
      (u₁ + 1) (v₁ - (principalA d) 0 0)
      (principalFiveTermShiftedParameter d (principalFiveTermLatticeArgument d v₁ v₂)) τ
      (principalFiveTermLatticeArgument d u₁ u₂))
      (𝓝[{τ : ℂ | 0 < τ.im}] (principalRoot d : ℂ))
      (𝓝 (((Real.sqrt (principalRoot d ^ 3) : ℂ) *
        principalDilogE d (principalFiveTermCharacteristicResidue d (u₁ + v₁) (u₂ + v₂)) /
          (principalDilogEMinus d (principalFiveTermCharacteristicResidue d u₁ u₂) *
            principalDilogEMinus d (principalFiveTermCharacteristicResidue d v₁ v₂))) /
        (1 - Complex.exp (2 * Real.pi * I *
          ((principalFiveTermLatticeArgument d v₁ v₂ : ℂ) + v₁ * (principalRoot d : ℂ)))))) := by
  let P : ℂ := 1 - Complex.exp (2 * Real.pi * I *
    ((principalFiveTermLatticeArgument d v₁ v₂ : ℂ) + v₁ * (principalRoot d : ℂ)))
  let Q : ℂ := (Real.sqrt (principalRoot d ^ 3) : ℂ) *
    principalDilogE d (principalFiveTermCharacteristicResidue d (u₁ + v₁) (u₂ + v₂)) /
      (principalDilogEMinus d (principalFiveTermCharacteristicResidue d u₁ u₂) *
        principalDilogEMinus d (principalFiveTermCharacteristicResidue d v₁ v₂))
  change Tendsto _ _ (𝓝 (Q / P))
  have hP : P ≠ 0 := principalFiveTerm_shifted_factor_ne_zero d hd v₁ v₂ hv0
  have hy := not_isPeriodLatticePoint_shiftedParameter d hd v₁ v₂ hv0
  by_cases hu : principalFiveTermCharacteristicResidue d u₁ u₂ = 0
  · obtain ⟨hu₁, hu₂⟩ := huZero hu
    subst u₁
    subst u₂
    have hzero : principalFiveTermCharacteristicResidue d 0 0 = 0 := by
      funext i
      fin_cases i <;>
        simp [principalFiveTermCharacteristicResidue, principalDilogOfLattice_apply]
    have hvalue : (principalRoot d : ℂ) ^ 3 *
        principalFaddeev d (v₁ - (principalA d) 0 0 + 1) 0
          (principalFiveTermShiftedParameter d (principalFiveTermLatticeArgument d v₁ v₂)) /
        principalFaddeev d (v₁ - (principalA d) 0 0) 0
          (principalFiveTermShiftedParameter d (principalFiveTermLatticeArgument d v₁ v₂)) =
        Q / P := by
      apply (eq_div_iff hP).2
      simpa only [P, Q, zero_add, hzero, mul_comm] using
        principalFiveTerm_shifted_zero_left_value d hd v₁ v₂ hv0
    have hlim := tendsto_closedFormUHPContinued_principalA_zero_left
      d hd (v₁ - (principalA d) 0 0)
      (principalFiveTermShiftedParameter d (principalFiveTermLatticeArgument d v₁ v₂)) hy
    rw [hvalue] at hlim
    simpa only [zero_add, show principalFiveTermLatticeArgument d 0 0 = 0 by
      simp [principalFiveTermLatticeArgument], Complex.ofReal_zero] using hlim
  · have hw := (not_isPeriodLatticePoint_latticeArgument_iff
      d hd u₁ u₂).2 hu
    have hlim := tendsto_closedFormUHPContinued_principalA d hd
      (u₁ + 1) (v₁ - (principalA d) 0 0)
      (principalFiveTermLatticeArgument d u₁ u₂)
      (principalFiveTermShiftedParameter d (principalFiveTermLatticeArgument d v₁ v₂))
      hw hy (principalFiveTerm_shifted_sum_admissible d hd u₁ u₂ v₁ v₂ huvZero)
    have hvalue : principalFiveTermClosedForm d (u₁ + 1)
        (v₁ - (principalA d) 0 0)
        (principalFiveTermLatticeArgument d u₁ u₂)
        (principalFiveTermShiftedParameter d (principalFiveTermLatticeArgument d v₁ v₂)) =
        Q / P := by
      apply (eq_div_iff hP).2
      by_cases huv : principalFiveTermCharacteristicResidue d (u₁ + v₁) (u₂ + v₂) = 0
      · obtain ⟨h₁, h₂⟩ := huvZero huv
        simpa only [P, Q, mul_comm] using
          principalFiveTerm_shifted_zero_sum_value d hd u₁ u₂ v₁ v₂ hu hv0 huv h₁ h₂
      · simpa only [P, Q, mul_comm, principalDilogEMinus_of_ne_zero d hd hu,
          principalDilogEMinus_of_ne_zero d hd hv0] using
          principalFiveTermClosedForm_shifted_eq d hd u₁ u₂ v₁ v₂ hu hv0 huv
    rw [hvalue] at hlim
    exact hlim

end SIC

end
