/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Dilogarithm.Group
import SICs.Dilogarithm.Values

/-!
# Values of the Principal Finite Quantum Dilogarithm

The values `F(r) = μ_{A_d} / ש^r_{A_d}(ρ_d)` of Radchenko and Wheeler's finite quantum
dilogarithm at the principal level matrix, with their zero-class values `ε^{±1/2}`, their
`ℤ²`-periodicity, the reflection law `F(r) F⁻(-r) = ⟨r⟩⁻¹`, and the invariance under `U_d`.

This module follows [RW26, Radchenko, Wheeler (2026), Section 1, equations (1) and (2),
`eq:phigam.def`, `eq:fgam.def`; Section 3.2, Lemma 2, `lem:lam.inv`; Theorem 2, `thm:fg.equs`,
equations (4) and (5), `eq:Fgpm.zero`, `eq:Fgpm.reflection`; Section 4.3, equation (37),
`eq:fgam.defalt`; Section 4.4, equation (38), `eq:fgamma3sym`] at `γ = A_d`, `τ = ρ_d`.
Their values are
`F^±_γ(u) = μ_γ Φ_{γ,u₁,0}(z_u; τ)` for `u` outside the zero class of `G`, where
`z_u (ε⁻¹ - 1) = u₁τ + u₂`, and `F^±_γ(u) = ε^{±1/2}` on the zero class, with `ε = j_γ(τ)` and
`μ_γ` the eta multiplier. Under the dictionary
`z_u = ⟨⟨r, τ⟩⟩`, `u₁τ + u₂ = ⟨⟨(γ - I)r, τ⟩⟩`, the Faddeev product `Φ_{γ,u₁,0}(z_u; τ)` is the
reciprocal of the Shintani--Faddeev cocycle, `Φ_{γ,0,n_QP(r,γ)}(⟨⟨r,τ⟩⟩; τ) = ש^r_γ(τ)⁻¹`, by
the shift law [RW26, Radchenko, Wheeler (2026), equation (16), `eq:faddeevperiod`]; at the fixed
point `ρ_d` of `A_d`,
`ε = j_{A_d}(ρ_d) = ρ_d³` (`principalJacobiFactor`), and the zero class of `G` is the class of
`ℤ²`. So `F(r) = μ_{A_d} / ש^r_{A_d}(ρ_d)` for `r ∉ ℤ²`, evaluated using the real word product
(`sfModularCocycleReal'`), and `F(r) = √(j_{A_d}(ρ_d))`,
`F⁻(r) = 1/√(j_{A_d}(ρ_d))` for `r ∈ ℤ²`.

## The argument

The identities follow from fixed-point theorems for the real cocycle defined by the word product:

- (4), `principalDilogE_zero` and `principalDilogEMinus_zero`: `F^±(0) = ε^{±1/2}` with
  `ε = j_{A_d}(ρ_d)`, the larger root of `x² - (N + 2)x + 1` (`principalJacobiFactor_quadratic`,
  `one_lt_principalJacobiFactor`).
- Lemma 2, `principalDilogValue_congr`: `F` is a function on `G_d`, i.e.
  `ℤ²`-periodic in `r`, by the periodicity of the cocycle at a fixed point
  (`sfModularCocycleRealTotal_congr_of_flt_eq_self`).
- (5), `principalDilogValue_mul_valueMinus_neg`: `F(r) F⁻(-r) = ⟨r⟩⁻¹`, from
  Kopp's Theorem 4.36 for the real cocycle,
  `ש^r_{A_d}(ρ_d) ש^{-r}_{A_d}(ρ_d) = ψ²(A_d) χ_r(A_d)`
  (`sfModularCocycleRealTotal_mul_neg_eq_character`), together with
  `μ_{A_d}² = ψ²(A_d)` (`etaMultiplier_sq_of_trace_pos`); on `ℤ²` both sides are `1`
  (`thetaCharacter_of_isIntegralIndex`).
- (38), `principalDilogValue_ratVecAction_principalU`: `F(εz) = F(z)` also gives
  `F(U_d r) = F(r)`,
  from Kopp's Theorem 4.37 at `R = U_d` (`sfModularCocycleRealTotal_mul_mul_inv`): `U_d` commutes
  with `A_d = U_d³`, fixes `ρ_d`, and has `j_{U_d}(ρ_d) = ρ_d > 0`. Multiplication of
  `z = ⟨⟨r, ρ_d⟩⟩` by `ρ_d` is `r ↦ U_d⁻¹ r`, while `U_d` acts as `ε⁻¹` on `z`;
  hence (38) holds for both unit actions. Here `ρ_d² = (d - 1)ρ_d - 1`.

The values at the characteristics `p/d` of the integer phase space are the reciprocals of the
principal cocycle `principalSFModularCocycleAd` up to `μ_{A_d}`
(`principalDilogValue_shiftRationalPoint`), which `SICs.Principal.Dilogarithm.GhostOverlap` turns
into
the comparison with the phased ghost overlap.

Composed with the lift `zmodCharacteristic` of `SICs.SL2Z.TorsionCharacteristics`, the values
become functions `E = F⁺` and `F⁻` on the residue vectors of `G_d` (`principalDilogE`,
`principalDilogEMinus`), which is where [RW26, Radchenko, Wheeler (2026), Theorem 2,
`thm:fg.equs`] lives: the zero class of `G_d` is the single residue vector `0`
(`isIntegralIndex_zmodCharacteristic_iff`), (5) becomes `E(x)F⁻(-x) = ⟨x⟩⁻¹` with the Gaussian
`principalDilogGaussian`, and the two relations (i) `E(0)² = √N E(0) + 1` and (ii)
`E(x)E(-x) = ⟨x⟩⁻¹` for `x ≠ 0` of [RW26, Radchenko, Wheeler (2026), Theorem 5,
`thm:fqdilogbasicproperties`] follow, the first from `ε^{1/2} - ε^{-1/2} = √N`
(`sqrt_principalJacobiFactor_sub_inv`).
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### The values `F` and `F⁻`

Off `ℤ²` both are `μ_{A_d} / ש^r_{A_d}(ρ_d)`; on `ℤ²` they are `ε^{1/2}` and `ε^{-1/2}`. -/

open scoped Classical in
/-- **The finite quantum dilogarithm `F(r) = F⁺_{A_d}(u)`** of
[RW26, Radchenko, Wheeler (2026), equation (2), `eq:fgam.def`] at `γ = A_d`, `τ = ρ_d`, in the
characteristic coordinate `r` with `z_u = ⟨⟨r, ρ_d⟩⟩` (equation (37), `eq:fgam.defalt`, is the same
value on `G = (1/(ε - 1))I_τ / I_τ`): for `r ∉ ℤ²`,
`F(r) = μ_{A_d} Φ_{A_d,u₁,0}(z_u; ρ_d) = μ_{A_d} / ש^r_{A_d}(ρ_d)`, and for `r ∈ ℤ²`,
`F(r) = ε^{1/2} = √(j_{A_d}(ρ_d))`. The cocycle is the real word-product value
`sfModularCocycleReal'`, `0` off `Γ_r`; the value is meaningful for `A_d ∈ Γ_r`, i.e. `r ∈ G_d`
up to `ℤ²`.
The source symbols are `F_γ(z)` and `F⁺_γ(u)`.
Specializes `finiteDilogValue`. -/
def principalDilogValue (d : ℕ) (r : Fin 2 → ℚ) : ℂ :=
  if IsIntegralIndex r then ((Real.sqrt (principalJacobiFactor d) : ℝ) : ℂ)
  else etaMultiplier (principalA d) / sfModularCocycleReal' r (principalA d) (principalRoot d)

open scoped Classical in
/-- **The value `F⁻(r) = F⁻_{A_d}(u)`** of [RW26, Radchenko, Wheeler (2026), equation (2),
`eq:fgam.def`] at `γ = A_d`, `τ = ρ_d`: `F⁻(r) = F(r)` for `r ∉ ℤ²`, and
`F⁻(r) = ε^{-1/2} = 1/√(j_{A_d}(ρ_d))` for `r ∈ ℤ²`.
The source symbol is `F⁻_γ(u)`.
Specializes `finiteDilogValueMinus`. -/
def principalDilogValueMinus (d : ℕ) (r : Fin 2 → ℚ) : ℂ :=
  if IsIntegralIndex r then (((Real.sqrt (principalJacobiFactor d))⁻¹ : ℝ) : ℂ)
  else etaMultiplier (principalA d) / sfModularCocycleReal' r (principalA d) (principalRoot d)

/-- Unfolding lemma for `principalDilogValue` on `ℤ²`. -/
theorem principalDilogValue_of_isIntegralIndex (d : ℕ) {r : Fin 2 → ℚ} (hr : IsIntegralIndex r) :
    principalDilogValue d r = ((Real.sqrt (principalJacobiFactor d) : ℝ) : ℂ) := by
  simp only [principalDilogValue, hr, ite_true]

/-- Unfolding lemma for `principalDilogValue` off `ℤ²`. -/
theorem principalDilogValue_of_not_isIntegralIndex (d : ℕ) {r : Fin 2 → ℚ}
    (hr : ¬ IsIntegralIndex r) :
    principalDilogValue d r =
      etaMultiplier (principalA d) / sfModularCocycleReal' r (principalA d) (principalRoot d) := by
  simp only [principalDilogValue, hr, ite_false]

/-- Unfolding lemma for `principalDilogValueMinus` on `ℤ²`. -/
theorem principalDilogValueMinus_of_isIntegralIndex (d : ℕ) {r : Fin 2 → ℚ}
    (hr : IsIntegralIndex r) :
    principalDilogValueMinus d r = (((Real.sqrt (principalJacobiFactor d))⁻¹ : ℝ) : ℂ) := by
  simp only [principalDilogValueMinus, hr, ite_true]

/-- Off `ℤ²` the two values agree, `F⁻(r) = F(r)`. -/
theorem principalDilogValueMinus_of_not_isIntegralIndex (d : ℕ) {r : Fin 2 → ℚ}
    (hr : ¬ IsIntegralIndex r) :
    principalDilogValueMinus d r = principalDilogValue d r := by
  simp only [principalDilogValueMinus, principalDilogValue, hr, ite_false]

/-- `F(r) ≠ 0` for `A_d ∈ Γ_r`: `μ_{A_d} ≠ 0`, and the cocycle is nonzero at the fixed point
(`sfModularCocycleRealTotal_ne_zero_of_flt_eq_self`). -/
theorem principalDilogValue_ne_zero (d : ℕ) (hd : 3 < d) {r : Fin 2 → ℚ}
    (hr : principalA d ∈ gammaSubgroup r) : principalDilogValue d r ≠ 0 := by
  by_cases h : IsIntegralIndex r
  · rw [principalDilogValue_of_isIntegralIndex d h]
    exact_mod_cast Real.sqrt_ne_zero'.mpr (principalJacobiFactor_pos d hd)
  · rw [principalDilogValue_of_not_isIntegralIndex d h,
      sfModularCocycleReal'_of_mem hr]
    exact div_ne_zero (etaMultiplier_ne_zero _) <|
      sfModularCocycleRealTotal_ne_zero_of_flt_eq_self hr
        (principalRoot_irrational d hd) h
        (fltDenominator_principalA_principalRoot_pos d hd)
        (flt_principalA_principalRoot d hd)

/-! ### The zero class: equation (4)

The zero-class values are `F^±(0) = ε^{±1/2}` with `ε = j_{A_d}(ρ_d)`; with `N = d²(d - 3)` they
satisfy `ε^{1/2} - ε^{-1/2} = √N`. -/

/-- `ε^{1/2} - ε^{-1/2} = √N` for `ε = j_{A_d}(ρ_d)` and `N = d²(d - 3)`: the left side is
positive since `ε > 1` (`one_lt_principalJacobiFactor`), and its square is `ε + ε⁻¹ - 2 = N`
(`principalJacobiFactor_add_inv`). This is the relation `E(0)² = √N E(0) + 1` of
[RW26, Radchenko, Wheeler (2026), Section 4.3, before Proposition 10, `prop:rqffinitedilog`]
in real form. -/
theorem sqrt_principalJacobiFactor_sub_inv (d : ℕ) (hd : 3 < d) :
    Real.sqrt (principalJacobiFactor d) - (Real.sqrt (principalJacobiFactor d))⁻¹ =
      Real.sqrt (principalDilogOrder d) := by
  let s : ℝ := Real.sqrt (principalJacobiFactor d)
  have hs : 1 < s := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) (one_lt_principalJacobiFactor d hd)
  have hs0 : s ≠ 0 := ne_of_gt (lt_trans zero_lt_one hs)
  have hsq : s ^ 2 = principalJacobiFactor d :=
    Real.sq_sqrt (le_of_lt (principalJacobiFactor_pos d hd))
  have hsum := principalJacobiFactor_add_inv d hd
  have hcast := cast_principalDilogOrder_eq d hd
  have hnonneg : 0 ≤ s - s⁻¹ := by
    have : s⁻¹ < 1 := inv_lt_one_of_one_lt₀ hs
    linarith
  have hsq' : (s - s⁻¹) ^ 2 = (principalDilogOrder d : ℝ) := by
    have hinv : s * s⁻¹ = 1 := mul_inv_cancel₀ hs0
    have hjinv : (principalJacobiFactor d)⁻¹ = (s⁻¹) ^ 2 := by
      rw [← hsq, inv_pow]
    rw [hcast]
    nlinarith
  rw [← Real.sqrt_sq hnonneg, hsq']

/-- For $\varepsilon=\rho_d^3$ and $N=d^2(d-3)$, the positive identity is
$\varepsilon-1=\sqrt N\sqrt\varepsilon$; it restates
`sqrt_principalJacobiFactor_sub_inv` in the principal-root notation. -/
theorem principalRoot_pow_three_sub_one_eq_sqrt_mul (d : ℕ) (hd : 3 < d) :
    principalRoot d ^ 3 - 1 =
      Real.sqrt (principalDilogOrder d) * Real.sqrt (principalRoot d ^ 3) := by
  let ε : ℝ := principalRoot d ^ 3
  let s : ℝ := Real.sqrt ε
  let n : ℝ := Real.sqrt (principalDilogOrder d)
  have hε : 1 < ε := one_lt_principalRoot_pow_three d hd
  have hs0 : s ≠ 0 := (Real.sqrt_ne_zero').mpr (by linarith)
  have hsq : s ^ 2 = ε := Real.sq_sqrt (by linarith)
  have hsub : s - s⁻¹ = n := by
    simpa [ε, s, n, principalJacobiFactor_eq_principalRoot_pow_three d hd] using
      sqrt_principalJacobiFactor_sub_inv d hd
  have hmul := congrArg (fun a : ℝ => a * s) hsub
  have hinv : s⁻¹ * s = 1 := inv_mul_cancel₀ hs0
  dsimp [ε, s, n] at *
  nlinarith

/-! ### Well-definedness on `G_d`: Lemma 2

`F` and `F⁻` are `ℤ²`-periodic on the characteristics with `A_d ∈ Γ_r`. -/

/-- **[RW26, Radchenko, Wheeler (2026), Lemma 2, `lem:lam.inv`] for `F⁺` at `γ = A_d`**: `F` is
well defined on `G_d`, i.e. `F(r') = F(r)` for `r' - r ∈ ℤ²` and `A_d ∈ Γ_r`. Off `ℤ²` this is the
periodicity of the cocycle at a fixed point,
`sfModularCocycleRealTotal_congr_of_flt_eq_self`; on `ℤ²` both sides are
`√(j_{A_d}(ρ_d))`. Specializes `finiteDilogValue_congr`. -/
theorem principalDilogValue_congr (d : ℕ) (hd : 3 < d) {r r' : Fin 2 → ℚ}
    (hr : principalA d ∈ gammaSubgroup r) (h : IsIntegralIndex (r' - r)) :
    principalDilogValue d r' = principalDilogValue d r := by
  have hiff := isIntegralIndex_iff_of_isIntegralIndex_sub h
  by_cases hR : IsIntegralIndex r
  · rw [principalDilogValue_of_isIntegralIndex d hR,
      principalDilogValue_of_isIntegralIndex d (hiff.mpr hR)]
  · have hR' : ¬ IsIntegralIndex r' := fun hh => hR (hiff.mp hh)
    have hr' : principalA d ∈ gammaSubgroup r' := by
      rw [gammaSubgroup_eq_of_isIntegralIndex_sub h]
      exact hr
    rw [principalDilogValue_of_not_isIntegralIndex d hR,
      principalDilogValue_of_not_isIntegralIndex d hR',
      sfModularCocycleReal'_of_mem hr,
      sfModularCocycleReal'_of_mem hr']
    congr 1
    exact sfModularCocycleRealTotal_congr_of_flt_eq_self
      hr hr' (principalRoot_irrational d hd) hR
      (flt_principalA_principalRoot d hd)
      (fltDenominator_principalA_principalRoot_pos d hd) h

/-- **[RW26, Radchenko, Wheeler (2026), Lemma 2, `lem:lam.inv`] for `F⁻` at `γ = A_d`**, by
`principalDilogValue_congr` off `ℤ²`. Specializes `finiteDilogValueMinus_congr`. -/
theorem principalDilogValueMinus_congr (d : ℕ) (hd : 3 < d)
    {r r' : Fin 2 → ℚ} (hr : principalA d ∈ gammaSubgroup r) (h : IsIntegralIndex (r' - r)) :
    principalDilogValueMinus d r' = principalDilogValueMinus d r := by
  have hiff := isIntegralIndex_iff_of_isIntegralIndex_sub h
  by_cases hR : IsIntegralIndex r
  · rw [principalDilogValueMinus_of_isIntegralIndex d hR,
      principalDilogValueMinus_of_isIntegralIndex d (hiff.mpr hR)]
  · have hR' : ¬ IsIntegralIndex r' := fun hh => hR (hiff.mp hh)
    rw [principalDilogValueMinus_of_not_isIntegralIndex d hR,
      principalDilogValueMinus_of_not_isIntegralIndex d hR']
    exact principalDilogValue_congr d hd hr h

/-! ### The reflection law: equation (5)

`F(r) F⁻(-r) = ⟨r⟩⁻¹`, Kopp's Theorem 4.36 divided by `μ_{A_d}² = ψ²(A_d)`. -/

/-- The nonintegral case of `principalDilogValue_mul_valueMinus_neg`. -/
private lemma principalDilogValue_reflection_nonintegral (d : ℕ) (hd : 3 < d)
    {r : Fin 2 → ℚ} (hr : principalA d ∈ gammaSubgroup r)
    (h : ¬ IsIntegralIndex r) :
    principalDilogValue d r * principalDilogValueMinus d (-r) =
      (thetaCharacter r (principalA d : Mat(2, ℤ)))⁻¹ := by
  have hn : ¬ IsIntegralIndex (-r) :=
    fun hh => h ((isIntegralIndex_neg_iff r).mp hh)
  have hrn := neg_mem_gammaSubgroup hr
  have hj := fltDenominator_principalA_principalRoot_pos d hd
  have hprod := sfModularCocycleRealTotal_mul_neg_eq_character
    (principalRoot_irrational d hd) h hr (principalA_lowerLeft_nonneg d hd)
    hj (flt_principalA_principalRoot d hd)
  have htrace : 0 < (principalA d : Mat(2, ℤ)) 0 0 +
      (principalA d : Mat(2, ℤ)) 1 1 := by
    rw [← Matrix.trace_fin_two]
    exact zero_lt_trace_principalA d hd
  rw [principalDilogValue_of_not_isIntegralIndex d h,
    principalDilogValueMinus_of_not_isIntegralIndex d hn,
    principalDilogValue_of_not_isIntegralIndex d hn,
    sfModularCocycleReal'_of_mem hr,
    sfModularCocycleReal'_of_mem hrn,
    div_mul_div_comm, ← pow_two, etaMultiplier_sq_of_trace_pos htrace, hprod]
  field_simp [etaMultiplierSq_ne_zero (principalA d),
    thetaCharacter_ne_zero r (principalA d : Mat(2, ℤ))]

/-- **[RW26, Radchenko, Wheeler (2026), Theorem 2, `thm:fg.equs`, equation (5),
`eq:Fgpm.reflection`] at `γ = A_d`**: `F⁺(r) F⁻(-r) = ⟨r⟩⁻¹` for `A_d ∈ Γ_r`, with the Gaussian
`⟨r⟩ = χ_r(A_d)`. Off `ℤ²` it is [72, Kopp (2024), Theorem 4.36, `thm:shincharacter`] on the
real cocycle, `sfModularCocycleRealTotal_mul_neg_eq_character`, divided into
`μ_{A_d}² = ψ²(A_d)` (`etaMultiplier_sq_of_trace_pos`, `zero_lt_trace_principalA`); on `ℤ²` it
is `ε^{1/2} ε^{-1/2} = 1 = χ_r(A_d)⁻¹` (`thetaCharacter_of_isIntegralIndex`).
Specializes `finiteDilogValue_mul_valueMinus_neg`. -/
theorem principalDilogValue_mul_valueMinus_neg (d : ℕ) (hd : 3 < d)
    {r : Fin 2 → ℚ} (hr : principalA d ∈ gammaSubgroup r) :
    principalDilogValue d r * principalDilogValueMinus d (-r) =
      (thetaCharacter r (principalA d : Mat(2, ℤ)))⁻¹ := by
  by_cases h : IsIntegralIndex r
  · have hn : IsIntegralIndex (-r) := (isIntegralIndex_neg_iff r).mpr h
    rw [principalDilogValue_of_isIntegralIndex d h,
      principalDilogValueMinus_of_isIntegralIndex d hn,
      thetaCharacter_of_isIntegralIndex (principalA d) h, inv_one]
    have hj : Real.sqrt (principalJacobiFactor d) ≠ 0 :=
      Real.sqrt_ne_zero'.mpr (principalJacobiFactor_pos d hd)
    exact_mod_cast mul_inv_cancel₀ hj
  · exact principalDilogValue_reflection_nonintegral d hd hr h

/-! ### The threefold symmetry: equation (38)

`F(εz) = F(z)`: multiplication of `z = ⟨⟨r, ρ_d⟩⟩` by `ε = ρ_d` is `r ↦ U_d⁻¹ r`, and `U_d`
conjugates `A_d` to itself. -/

/-- Cocycle transport under `U_d` for the nonintegral case of
`principalDilogValue_ratVecAction_principalU`. -/
private lemma principalDilogValue_cocycle_principalU (d : ℕ) (hd : 3 < d)
    {r : Fin 2 → ℚ} (hr : principalA d ∈ gammaSubgroup r)
    (h : ¬ IsIntegralIndex r) :
    sfModularCocycleReal' (ratVecAction (principalU d : Mat(2, ℤ)) r)
      (principalA d) (principalRoot d) =
    sfModularCocycleReal' r (principalA d) (principalRoot d) := by
  have hcomm := principalU_mul_principalA_mul_inv d
  have hmem : principalA d ∈ gammaSubgroup
      (ratVecAction (principalU d : Mat(2, ℤ)) r) := by
    rw [← hcomm]
    exact mul_mul_inv_mem_gammaSubgroup_ratVecAction hr (principalU d)
  have hjA := fltDenominator_principalA_principalRoot_pos d hd
  have hjU := fltDenominator_principalU_principalRoot_pos d hd
  rw [sfModularCocycleReal'_of_mem hmem, sfModularCocycleReal'_of_mem hr]
  calc
    _ = sfModularCocycleRealTotal _
        (principalU d * principalA d * (principalU d)⁻¹)
        (mul_mul_inv_mem_gammaSubgroup_ratVecAction hr (principalU d))
        (principalRoot d) :=
      (sfModularCocycleRealTotal_congr hcomm _ hmem _).symm
    _ = sfModularCocycleRealTotal _
        (principalU d * principalA d * (principalU d)⁻¹)
        (mul_mul_inv_mem_gammaSubgroup_ratVecAction hr (principalU d))
        (flt (principalU d : Mat(2, ℤ)) (principalRoot d)) := by
      rw [flt_principalU_principalRoot d hd]
    _ = _ := sfModularCocycleRealTotal_mul_mul_inv hr (principalU d)
      (principalRoot_irrational d hd) h (flt_principalA_principalRoot d hd) hjA hjU

/-- **[RW26, Radchenko, Wheeler (2026), equation (38), `eq:fgamma3sym`] at `γ = A_d`**, the second
identity of Proposition 8, `prop:powers`, for `γ = α³`, `α = U_d`: `F(U_d r) = F(r)` for
`A_d ∈ Γ_r`. Here `U_d` acts as `ε⁻¹` on `z = ⟨⟨r, ρ_d⟩⟩`; this is equivalent to the displayed
`F(εz) = F(z)` because `ε` is invertible. This is [72, Kopp (2024), Theorem 4.37, `thm:shinconj`] on
the real cocycle, `sfModularCocycleRealTotal_mul_mul_inv`, at `R = U_d`, which satisfies
`U_d A_d U_d⁻¹ = A_d`, `U_d · ρ_d = ρ_d` (`principalU_fixes_principalRoot`), and
`j_{U_d}(ρ_d) = ρ_d > 0` (`fltDenominator_principalU_principalRoot`); on `ℤ²` both sides are
`√(j_{A_d}(ρ_d))` (`isIntegralIndex_ratVecAction_iff`). -/
theorem principalDilogValue_ratVecAction_principalU (d : ℕ) (hd : 3 < d) {r : Fin 2 → ℚ}
    (hr : principalA d ∈ gammaSubgroup r) :
    principalDilogValue d (ratVecAction (principalU d : Mat(2, ℤ)) r) =
      principalDilogValue d r := by
  by_cases h : IsIntegralIndex r
  · have h' := (isIntegralIndex_ratVecAction_iff (principalU d)).mpr h
    rw [principalDilogValue_of_isIntegralIndex d h',
      principalDilogValue_of_isIntegralIndex d h]
  · have h' : ¬ IsIntegralIndex (ratVecAction (principalU d : Mat(2, ℤ)) r) :=
      (isIntegralIndex_ratVecAction_iff (principalU d)).not.mpr h
    rw [principalDilogValue_of_not_isIntegralIndex d h',
      principalDilogValue_of_not_isIntegralIndex d h,
      principalDilogValue_cocycle_principalU d hd hr h]

/-! ### The values on the `d`-torsion

At the characteristics `p/d` of the integer phase space, `F` is `μ_{A_d}` over the principal
cocycle `principalSFModularCocycleAd`, which reduces `p` modulo `d`. -/

/-- **`F(p/d) = μ_{A_d} / ש^{p/d}_{A_d}(ρ_d)` for `p ≢ 0 (mod d)`**, with the cocycle in its
principal closed form `principalSFModularCocycleAd` (`sfModularCocycleReal'_principalA`,
`not_isIntegralIndex_div`). -/
theorem principalDilogValue_shiftRationalPoint (d : ℕ) (hd : 3 < d) (p : IntPhaseSpace)
    (hp : intPhaseSpaceMod d p ≠ 0) :
    principalDilogValue d (shiftRationalPoint d p) =
      etaMultiplier (principalA d) / principalSFModularCocycleAd d p := by
  have hnot := not_isIntegralIndex_shiftRationalPoint d (by omega) hp
  have hdiv : ¬((d : ℤ) ∣ p 0 ∧ (d : ℤ) ∣ p 1) :=
    fun hh => hp ((intPhaseSpaceMod_eq_zero_iff_dvd d p).mpr hh)
  have hpvec : ![p 0, p 1] = p := by
    funext i
    fin_cases i <;> rfl
  rw [principalDilogValue_of_not_isIntegralIndex d hnot,
    shiftRationalPoint_eq_cons,
    sfModularCocycleReal'_principalA d hd (p 0) (p 1) (Or.inr hdiv), hpvec]

/-- **`F(p/d) = √(j_{A_d}(ρ_d))` for `p ≡ 0 (mod d)`**: `p/d ∈ ℤ²`. -/
theorem principalDilogValue_shiftRationalPoint_eq_sqrt (d : ℕ) (hd : 3 < d)
    (p : IntPhaseSpace) (hp : intPhaseSpaceMod d p = 0) :
    principalDilogValue d (shiftRationalPoint d p) =
      ((Real.sqrt (principalJacobiFactor d) : ℝ) : ℂ) := by
  have : NeZero d := ⟨by omega⟩
  have hint := isIntegralIndex_shiftRationalPoint_of_mod_eq_zero d p hp
  exact principalDilogValue_of_isIntegralIndex d hint

/-- **`F(p/d)` depends on `p` only modulo `d`**: Lemma 2
(`principalDilogValue_congr`) at `A_d ∈ Γ_{p/d}`
(`principalA_mem_gammaSubgroup`), since `p' ≡ p (mod d)` makes `(p' - p)/d` integral. -/
theorem principalDilogValue_shiftRationalPoint_congr (d : ℕ) (hd : 3 < d) {p p' : IntPhaseSpace}
    (h : intPhaseSpaceMod d p' = intPhaseSpaceMod d p) :
    principalDilogValue d (shiftRationalPoint d p') =
      principalDilogValue d (shiftRationalPoint d p) := by
  have hr := principalA_mem_gammaSubgroup_shiftRationalPoint d hd p
  exact principalDilogValue_congr d hd hr
    (exists_intCast_shiftRationalPoint_sub_of_mod_eq d (by omega) h)

/-- The reflection law (5) at `p/d` in reciprocal form: `F(q/d)⁻¹ = χ_{q/d}(A_d) F⁻(-q/d)`
(`principalDilogValue_mul_valueMinus_neg`, `shiftRationalPoint_neg`). -/
theorem inv_principalDilogValue_shiftRationalPoint (d : ℕ) (hd : 3 < d)
    (q : IntPhaseSpace) :
    (principalDilogValue d (shiftRationalPoint d q))⁻¹ =
      thetaCharacter (shiftRationalPoint d q) (principalA d : Mat(2, ℤ)) *
        principalDilogValueMinus d (shiftRationalPoint d (-q)) := by
  have hmem := principalA_mem_gammaSubgroup_shiftRationalPoint d hd q
  have hFq := principalDilogValue_ne_zero d hd hmem
  have hr := principalDilogValue_mul_valueMinus_neg d hd hmem
  rw [← shiftRationalPoint_neg] at hr
  have hχ := thetaCharacter_ne_zero (shiftRationalPoint d q)
    (principalA d : Mat(2, ℤ))
  have hχcancel : (thetaCharacter (shiftRationalPoint d q)
      (principalA d : Mat(2, ℤ)))⁻¹ *
      thetaCharacter (shiftRationalPoint d q) (principalA d : Mat(2, ℤ)) = 1 :=
    inv_mul_cancel₀ hχ
  calc
    _ = (principalDilogValue d (shiftRationalPoint d q))⁻¹ *
        ((principalDilogValue d (shiftRationalPoint d q) *
            principalDilogValueMinus d (shiftRationalPoint d (-q))) *
          thetaCharacter (shiftRationalPoint d q) (principalA d : Mat(2, ℤ))) := by
        rw [hr, hχcancel, mul_one]
    _ = _ := by field_simp

/-! ### The values on `G_d`

`E(x) = F(x/N)` and `F⁻(x) = F⁻(x/N)` at the lifted characteristic of a residue vector `x`. On
`G_d` these are Radchenko and Wheeler's `F^±_γ(u)`, `u ∈ G`, with `E(u) = F⁺_γ(u)` their finite
quantum dilogarithm; the zero class is the residue vector `0`. -/

/-- **The finite quantum dilogarithm `E(x) = F⁺(x)` on `G_d`**: the value `principalDilogValue`
at the lifted characteristic `x/N` of a residue vector `x ∈ (ℤ/Nℤ)²`. On `G_d` this is
`E(u) = F⁺_γ(u)` of [RW26, Radchenko, Wheeler (2026), Proposition 10, `prop:rqffinitedilog`;
equation (2), `eq:fgam.def`] at `γ = A_d`; it is meaningful for `x ∈ G_d`, where
`A_d ∈ Γ_{x/N}`. -/
def principalDilogE (d : ℕ) (x : Fin 2 → ZMod (principalDilogOrder d)) : ℂ :=
  principalDilogValue d (zmodCharacteristic (principalDilogOrder d) x)

/-- **The value `F⁻(x)` on `G_d`**: `principalDilogValueMinus` at the lifted characteristic, the
`F⁻_γ(u)`, `u ∈ G`, of [RW26, Radchenko, Wheeler (2026), equation (2), `eq:fgam.def`] at
`γ = A_d`. -/
def principalDilogEMinus (d : ℕ) (x : Fin 2 → ZMod (principalDilogOrder d)) : ℂ :=
  principalDilogValueMinus d (zmodCharacteristic (principalDilogOrder d) x)

/-- `E(0) = ε^{1/2}` (`principalDilogValue_of_isIntegralIndex` at the zero lift). -/
theorem principalDilogE_zero (d : ℕ) :
    principalDilogE d 0 = ((Real.sqrt (principalJacobiFactor d) : ℝ) : ℂ) := by
  rw [principalDilogE, zmodCharacteristic_zero]
  exact principalDilogValue_of_isIntegralIndex d (fun i => ⟨0, by simp⟩)

/-- `F⁻(0) = ε^{-1/2}`. -/
theorem principalDilogEMinus_zero (d : ℕ) :
    principalDilogEMinus d 0 = (((Real.sqrt (principalJacobiFactor d))⁻¹ : ℝ) : ℂ) := by
  rw [principalDilogEMinus, zmodCharacteristic_zero]
  exact principalDilogValueMinus_of_isIntegralIndex d (fun i => ⟨0, by simp⟩)

/-- Off the zero residue vector the two values agree, `F⁻(x) = E(x)`
(`isIntegralIndex_zmodCharacteristic_iff`). -/
theorem principalDilogEMinus_of_ne_zero (d : ℕ) (hd : 3 < d)
    {x : Fin 2 → ZMod (principalDilogOrder d)} (hx : x ≠ 0) :
    principalDilogEMinus d x = principalDilogE d x := by
  let _ : NeZero (principalDilogOrder d) := principalDilogOrder_neZero d hd
  exact principalDilogValueMinus_of_not_isIntegralIndex d
    (fun h => hx ((isIntegralIndex_zmodCharacteristic_iff _ x).mp h))

/-- `E(x) ≠ 0` for `x ∈ G_d` (`principalDilogValue_ne_zero`, `mem_principalDilogGroup_iff`). -/
theorem principalDilogE_ne_zero (d : ℕ) (hd : 3 < d)
    {x : Fin 2 → ZMod (principalDilogOrder d)} (hx : x ∈ principalDilogGroup d) :
    principalDilogE d x ≠ 0 := by
  exact principalDilogValue_ne_zero d hd ((mem_principalDilogGroup_iff d hd x).mp hx)

/-- **The reflection law (5) on `G_d`**: `E(x) F⁻(-x) = ⟨x⟩⁻¹` for `x ∈ G_d`, from
`principalDilogValue_mul_valueMinus_neg` at the lifted characteristic, the lift of
`-x` differing from the negative of the lift by an integer vector
(`isIntegralIndex_zmodCharacteristic_neg_add`,
`principalDilogValueMinus_congr`). -/
theorem principalDilogE_mul_principalDilogEMinus_neg (d : ℕ) (hd : 3 < d)
    {x : Fin 2 → ZMod (principalDilogOrder d)} (hx : x ∈ principalDilogGroup d) :
    principalDilogE d x * principalDilogEMinus d (-x) = (principalDilogGaussian d x)⁻¹ := by
  let _ : NeZero (principalDilogOrder d) := principalDilogOrder_neZero d hd
  have hr := (mem_principalDilogGroup_iff d hd x).mp hx
  have hsub : IsIntegralIndex
      (zmodCharacteristic (principalDilogOrder d) (-x) -
        -(zmodCharacteristic (principalDilogOrder d) x)) := by
    simpa only [sub_neg_eq_add] using
      isIntegralIndex_zmodCharacteristic_neg_add (principalDilogOrder d) x
  have hcongr := principalDilogValueMinus_congr d hd
    (neg_mem_gammaSubgroup hr) hsub
  rw [principalDilogE, principalDilogEMinus, hcongr]
  exact principalDilogValue_mul_valueMinus_neg d hd hr

/-- **[RW26, Radchenko, Wheeler (2026), Theorem 5, `thm:fqdilogbasicproperties`](ii) for
`E = F⁺_{A_d}`**: `E(x) E(-x) = ⟨x⟩⁻¹` for `x ∈ G_d`, `x ≠ 0`, which is (5) with `F⁻(-x) = E(-x)`
off the zero class (`principalDilogEMinus_of_ne_zero`). -/
theorem principalDilogE_mul_principalDilogE_neg (d : ℕ) (hd : 3 < d)
    {x : Fin 2 → ZMod (principalDilogOrder d)} (hx : x ∈ principalDilogGroup d) (hx0 : x ≠ 0) :
    principalDilogE d x * principalDilogE d (-x) = (principalDilogGaussian d x)⁻¹ := by
  rw [← principalDilogEMinus_of_ne_zero d hd (neg_ne_zero.mpr hx0)]
  exact principalDilogE_mul_principalDilogEMinus_neg d hd hx

/-- The reflection law in the form used by [RW26, Radchenko, Wheeler (2026), Section 4.4]:
`E(x)⟨x⟩E(-x)=1` for nonzero `x ∈ G_d`. -/
theorem principalDilogE_mul_gaussian_mul_E_neg
    (d : ℕ) (hd : 3 < d) {x : Fin 2 → ZMod (principalDilogOrder d)}
    (hx : x ∈ principalDilogGroup d) (hx0 : x ≠ 0) :
    principalDilogE d x * principalDilogGaussian d x * principalDilogE d (-x) = 1 := by
  calc
    _ = (principalDilogE d x * principalDilogE d (-x)) * principalDilogGaussian d x := by ring
    _ = 1 := by
      rw [principalDilogE_mul_principalDilogE_neg d hd hx hx0]
      exact inv_mul_cancel₀ (fixedGaussian_ne_zero (principalA d) (principalDilogOrder d) x)

/-- **[RW26, Radchenko, Wheeler (2026), Theorem 5, `thm:fqdilogbasicproperties`](i) for
`E = F⁺_{A_d}`**: `E(0)² = √N E(0) + 1`, i.e. `ε = √N ε^{1/2} + 1`, which is
`ε^{1/2} - ε^{-1/2} = √N` (`sqrt_principalJacobiFactor_sub_inv`) multiplied by `ε^{1/2}`; noted
as true by (4) before Proposition 10 in [RW26, Radchenko, Wheeler (2026), Section 4.3,
`prop:rqffinitedilog`]. Specializes `finiteDilogE_zero_sq`. -/
theorem principalDilogE_zero_sq (d : ℕ) (hd : 3 < d) :
    principalDilogE d 0 ^ 2 =
      (Real.sqrt (principalDilogOrder d) : ℂ) * principalDilogE d 0 + 1 := by
  rw [principalDilogE_zero]
  have hs : Real.sqrt (principalJacobiFactor d) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (principalJacobiFactor_pos d hd)
  have hreal : Real.sqrt (principalJacobiFactor d) ^ 2 =
      Real.sqrt (principalDilogOrder d) * Real.sqrt (principalJacobiFactor d) + 1 := by
    have h := sqrt_principalJacobiFactor_sub_inv d hd
    have hinv := mul_inv_cancel₀ hs
    have hmul := congrArg (fun t : ℝ => t * Real.sqrt (principalJacobiFactor d)) h
    nlinarith [hmul]
  exact_mod_cast hreal

/-- **`E` on the `d`-torsion**: `E(d(d - 3)p) = F(p/d)`, since the lift of `d(d - 3)p` is `p/d`
up to `ℤ²` (`isIntegralIndex_principalDilogTorsion_sub`,
`principalDilogValue_congr`). -/
theorem principalDilogE_principalDilogTorsion (d : ℕ) (hd : 3 < d) (p : IntPhaseSpace) :
    principalDilogE d (principalDilogTorsion d p) =
      principalDilogValue d (shiftRationalPoint d p) := by
  have hr := principalA_mem_gammaSubgroup_shiftRationalPoint d hd p
  exact principalDilogValue_congr d hd hr
    (isIntegralIndex_principalDilogTorsion_sub d hd p)

/-! ### Bridges to the general finite quantum dilogarithm

At the principal matrix and root, the general value reduces to its principal form. -/

/-- The principal value $F_{A_d}^+(r)$ is the general value at $(A_d,\rho_d)$.
Specializes `finiteDilogValue`. -/
theorem finiteDilogValue_principalA (d : ℕ) :
    finiteDilogValue (principalA d) (principalRoot d) = principalDilogValue d := by
  funext r
  simp only [finiteDilogValue, principalDilogValue,
    fltDenominator_principalA_principalRoot]

end SIC

end
