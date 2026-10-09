/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Cocycle.FixedPointCocycle
import SICs.Dilogarithm.Group
import SICs.SL2Z.RademacherConjugation

/-!
# Values of the Finite Quantum Dilogarithm of a Hyperbolic Matrix

The values `F(r) = μ_γ / ש^r_γ(τ)` of Radchenko and Wheeler's finite quantum dilogarithm at an
arbitrary hyperbolic matrix `γ` and its attractive fixed point `τ`, with their zero-class values
`ε^{±1/2}`, their `ℤ²`-periodicity, the reflection law `F(r) F⁻(-r) = ⟨r⟩⁻¹`, their invariance
under conjugation and, for `F⁻`, under matrices commuting with `γ`, and their descent to the
group `G`.

This module follows [RW26, Radchenko, Wheeler (2026), Section 1, equations (1) and (2),
`eq:phigam.def`, `eq:fgam.def`; Section 3.2, Lemma 2, `lem:lam.inv`; Theorem 2, `thm:fg.equs`,
equation (5), `eq:Fgpm.reflection`; Section 4.3, equation (37),
`eq:fgam.defalt`; Section 4.4, equation (38), `eq:fgamma3sym`] for every `(γ, τ)` with
`IsAttractiveFixedPoint γ τ`, generalizing `SICs.Principal.Dilogarithm.Values` from
`(A_d, ρ_d)`; the principal declarations are its instances, with their own proofs kept. Their
values are `F^±_γ(u) = μ_γ Φ_{γ,u₁,0}(z_u; τ)` for `u` outside the zero class of `G`, where
`z_u (ε⁻¹ - 1) = u₁τ + u₂`, and `F^±_γ(u) = ε^{±1/2}` on the zero class, with `ε = j_γ(τ)` and
`μ_γ` the eta multiplier. Under the dictionary `z_u = ⟨⟨r, τ⟩⟩`, `u₁τ + u₂ = ⟨⟨(γ - I)r, τ⟩⟩`,
the Faddeev product `Φ_{γ,u₁,0}(z_u; τ)` is the reciprocal of the Shintani--Faddeev cocycle,
`Φ_{γ,0,n_QP(r,γ)}(⟨⟨r,τ⟩⟩; τ) = ש^r_γ(τ)⁻¹`, by the shift law
[RW26, Radchenko, Wheeler (2026), equation (16), `eq:faddeevperiod`]; the identification is
proved at `A_d` in `SICs.Principal.Dilogarithm.Faddeev.Cocycle` and is part of the general
Faddeev boundary theory for arbitrary `γ`. So `F(r) = μ_γ / ש^r_γ(τ)` for `r ∉ ℤ²`, evaluated
using the real cocycle `sfModularCocycleReal'`, and `F(r) = √ε`,
`F⁻(r) = 1/√ε` for `r ∈ ℤ²`.

## The argument

The identities follow from the fixed-point theorems for the real cocycle:

- The zero-class convention before (2), `finiteDilogValue_of_isIntegralIndex`:
  `F(0) = ε^{1/2}`. At an attractive fixed point, `ε` is the larger root of
  `x² - (N + 2)x + 1` (`IsAttractiveFixedPoint.fltDenominator_sq`), so the quadratic formula
  gives (4), which is not stated separately.
- Lemma 2, `finiteDilogValue_congr`: `F` is a function on `G`, i.e. `ℤ²`-periodic in `r`, by
  the periodicity of the cocycle at a fixed point
  (`sfModularCocycleRealTotal_congr_of_flt_eq_self`).
- (5), `finiteDilogValue_mul_valueMinus_neg`: `F(r) F⁻(-r) = ⟨r⟩⁻¹`, from Kopp's Theorem 4.36
  for the real cocycle, `ש^r_γ(τ) ש^{-r}_γ(τ) = ψ²(γ) χ_r(γ)`
  (`sfModularCocycleRealTotal_mul_neg_eq_character`, which needs `c ≥ 0`), together with
  `μ_γ² = ψ²(γ)` (`etaMultiplier_sq_of_trace_pos`); on `ℤ²` both sides are `1`.
- (38) for `F⁻`, `finiteDilogValueMinus_ratVecAction`: `F⁻(Rr) = F⁻(r)` for `R` commuting with
  `γ`, fixing `τ`, with `j_R(τ) > 0`, from Kopp's Theorem 4.37
  (`sfModularCocycleRealTotal_mul_mul_inv`).
- On `G`: `E(x) = F(x/N)`, `F⁻(x) = F⁻(x/N)` at the lifted characteristic of a residue vector,
  the `E` of [RW26, Radchenko, Wheeler (2026), Section 4.3, `prop:rqffinitedilog`]; the
  reflection law gives `E(x)F⁻(-x) = ⟨x⟩⁻¹` on `G`, and `E(0)² = √N E(0) + 1` is clause (i) of
  [RW26, Radchenko, Wheeler (2026), Theorem 5, `thm:fqdilogbasicproperties`] for this `E`.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### The values `F(r)` and `F⁻(r)`

`F(r) = μ_γ / ש^r_γ(τ)` off `ℤ²`, `ε^{±1/2}` on `ℤ²`. -/

open scoped Classical in
/-- **The finite quantum dilogarithm `F(r) = F⁺_γ(u)`** of
[RW26, Radchenko, Wheeler (2026), equation (2), `eq:fgam.def`] at a hyperbolic `γ` and a real
point `τ`, in the characteristic coordinate `r` with `z_u = ⟨⟨r, τ⟩⟩` (equation (37),
`eq:fgam.defalt`, is the same value on `G = (1/(ε - 1))I_τ / I_τ`): for `r ∉ ℤ²`,
`F(r) = μ_γ Φ_{γ,u₁,0}(z_u; τ) = μ_γ / ש^r_γ(τ)`, and for `r ∈ ℤ²`, `F(r) = ε^{1/2} = √(j_γ(τ))`.
The cocycle is the real value `sfModularCocycleReal'`, `0` off `Γ_r`; the value is
meaningful under `IsAttractiveFixedPoint γ τ` for `γ ∈ Γ_r`, i.e. `r ∈ G` up to `ℤ²`. -/
@[source "RW26, equation (2), p. 2, eq:fgam.def (F⁺)" (symbol := "F_γ(z), F⁺_γ(u)")]
def finiteDilogValue (A : SL(2, ℤ)) (τ : ℝ) (r : Fin 2 → ℚ) : ℂ :=
  if IsIntegralIndex r then ((Real.sqrt (fltDenominator (A : Mat(2, ℤ)) τ) : ℝ) : ℂ)
  else etaMultiplier A / sfModularCocycleReal' r A τ

open scoped Classical in
/-- **The value `F⁻(r) = F⁻_γ(u)`** of [RW26, Radchenko, Wheeler (2026), equation (2),
`eq:fgam.def`]: `F⁻(r) = F(r)` for `r ∉ ℤ²`, and `F⁻(r) = ε^{-1/2} = 1/√(j_γ(τ))` for
`r ∈ ℤ²`. -/
@[source "RW26, equation (2), p. 2, eq:fgam.def (F⁻)" (symbol := "F⁻_γ(u)")]
def finiteDilogValueMinus (A : SL(2, ℤ)) (τ : ℝ) (r : Fin 2 → ℚ) : ℂ :=
  if IsIntegralIndex r then (((Real.sqrt (fltDenominator (A : Mat(2, ℤ)) τ))⁻¹ : ℝ) : ℂ)
  else etaMultiplier A / sfModularCocycleReal' r A τ

variable {A : SL(2, ℤ)} {τ : ℝ}

/-- The zero-class convention for `F⁺` before
[RW26, Radchenko, Wheeler (2026), equation (2), `eq:fgam.def`]: `F(r) = ε^{1/2}` on `ℤ²`.
This unfolds `finiteDilogValue`. -/
@[source "RW26, equation (2), p. 2, eq:fgam.def (zero-class convention, F⁺)"]
theorem finiteDilogValue_of_isIntegralIndex (A : SL(2, ℤ)) (τ : ℝ) {r : Fin 2 → ℚ}
    (hr : IsIntegralIndex r) :
    finiteDilogValue A τ r = ((Real.sqrt (fltDenominator (A : Mat(2, ℤ)) τ) : ℝ) : ℂ) := by
  simp only [finiteDilogValue, hr, ite_true]

/-- Unfolding lemma for `finiteDilogValue` off `ℤ²`. -/
theorem finiteDilogValue_of_not_isIntegralIndex (A : SL(2, ℤ)) (τ : ℝ) {r : Fin 2 → ℚ}
    (hr : ¬ IsIntegralIndex r) :
    finiteDilogValue A τ r = etaMultiplier A / sfModularCocycleReal' r A τ := by
  simp only [finiteDilogValue, hr, ite_false]

/-- The zero-class convention for `F⁻` before
[RW26, Radchenko, Wheeler (2026), equation (2), `eq:fgam.def`]: `F⁻(r) = ε^{-1/2}` on `ℤ²`.
This unfolds `finiteDilogValueMinus`. -/
@[source "RW26, equation (2), p. 2, eq:fgam.def (zero-class convention, F⁻)"]
theorem finiteDilogValueMinus_of_isIntegralIndex (A : SL(2, ℤ)) (τ : ℝ) {r : Fin 2 → ℚ}
    (hr : IsIntegralIndex r) :
    finiteDilogValueMinus A τ r =
      (((Real.sqrt (fltDenominator (A : Mat(2, ℤ)) τ))⁻¹ : ℝ) : ℂ) := by
  simp only [finiteDilogValueMinus, hr, ite_true]

/-- Off `ℤ²` the two values agree, `F⁻(r) = F(r)`. -/
theorem finiteDilogValueMinus_of_not_isIntegralIndex (A : SL(2, ℤ)) (τ : ℝ) {r : Fin 2 → ℚ}
    (hr : ¬ IsIntegralIndex r) :
    finiteDilogValueMinus A τ r = finiteDilogValue A τ r := by
  simp only [finiteDilogValueMinus, finiteDilogValue, hr, ite_false]

/-- `F(r) ≠ 0` for `γ ∈ Γ_r`: `μ_γ ≠ 0`, and the cocycle is nonzero at the fixed point
(`sfModularCocycleRealTotal_ne_zero_of_flt_eq_self`). -/
theorem finiteDilogValue_ne_zero (h : IsAttractiveFixedPoint A τ) {r : Fin 2 → ℚ}
    (hr : A ∈ gammaSubgroup r) : finiteDilogValue A τ r ≠ 0 := by
  by_cases hR : IsIntegralIndex r
  · rw [finiteDilogValue_of_isIntegralIndex A τ hR]
    exact_mod_cast Real.sqrt_ne_zero'.mpr h.fltDenominator_pos
  · rw [finiteDilogValue_of_not_isIntegralIndex A τ hR,
      sfModularCocycleReal'_of_mem hr]
    exact div_ne_zero (etaMultiplier_ne_zero _) <|
      sfModularCocycleRealTotal_ne_zero_of_flt_eq_self hr
        h.irrational hR h.fltDenominator_pos h.flt_eq

/-- `F⁻(r) ≠ 0` for `γ ∈ Γ_r` (`finiteDilogValue_ne_zero`). -/
theorem finiteDilogValueMinus_ne_zero (h : IsAttractiveFixedPoint A τ) {r : Fin 2 → ℚ}
    (hr : A ∈ gammaSubgroup r) : finiteDilogValueMinus A τ r ≠ 0 := by
  by_cases hR : IsIntegralIndex r
  · rw [finiteDilogValueMinus_of_isIntegralIndex A τ hR]
    exact_mod_cast inv_ne_zero (Real.sqrt_ne_zero'.mpr h.fltDenominator_pos)
  · rw [finiteDilogValueMinus_of_not_isIntegralIndex A τ hR]
    exact finiteDilogValue_ne_zero h hr

/-! ### Periodicity: Lemma 2

`F` is a function on `G`: `F(r') = F(r)` for `r' - r ∈ ℤ²`. -/

/-- The periodicity used by `finiteDilogValue_congr` needs only an irrational fixed point with
positive Jacobi denominator; this form also applies to conjugates with either lower-left sign. -/
private theorem finiteDilogValue_congr_of_fixed {A : SL(2, ℤ)} {τ : ℝ}
    (hirr : Irrational τ) (hfixed : flt (A : Mat(2, ℤ)) τ = τ)
    (hden : 0 < fltDenominator (A : Mat(2, ℤ)) τ) {r r' : Fin 2 → ℚ}
    (hr : A ∈ gammaSubgroup r) (hdiff : IsIntegralIndex (r' - r)) :
    finiteDilogValue A τ r' = finiteDilogValue A τ r := by
  have hiff := isIntegralIndex_iff_of_isIntegralIndex_sub hdiff
  by_cases hR : IsIntegralIndex r
  · rw [finiteDilogValue_of_isIntegralIndex A τ hR,
      finiteDilogValue_of_isIntegralIndex A τ (hiff.mpr hR)]
  · have hR' : ¬ IsIntegralIndex r' := fun hh => hR (hiff.mp hh)
    have hr' : A ∈ gammaSubgroup r' := by
      rw [gammaSubgroup_eq_of_isIntegralIndex_sub hdiff]
      exact hr
    rw [finiteDilogValue_of_not_isIntegralIndex A τ hR,
      finiteDilogValue_of_not_isIntegralIndex A τ hR',
      sfModularCocycleReal'_of_mem hr,
      sfModularCocycleReal'_of_mem hr']
    congr 1
    exact sfModularCocycleRealTotal_congr_of_flt_eq_self
      hr hr' hirr hR hfixed hden hdiff

/-- The periodicity of `F⁻` under the same fixed-point hypotheses as
`finiteDilogValue_congr_of_fixed`. -/
private theorem finiteDilogValueMinus_congr_of_fixed {A : SL(2, ℤ)} {τ : ℝ}
    (hirr : Irrational τ) (hfixed : flt (A : Mat(2, ℤ)) τ = τ)
    (hden : 0 < fltDenominator (A : Mat(2, ℤ)) τ) {r r' : Fin 2 → ℚ}
    (hr : A ∈ gammaSubgroup r) (hdiff : IsIntegralIndex (r' - r)) :
    finiteDilogValueMinus A τ r' = finiteDilogValueMinus A τ r := by
  have hiff := isIntegralIndex_iff_of_isIntegralIndex_sub hdiff
  by_cases hR : IsIntegralIndex r
  · rw [finiteDilogValueMinus_of_isIntegralIndex A τ hR,
      finiteDilogValueMinus_of_isIntegralIndex A τ (hiff.mpr hR)]
  · have hR' : ¬ IsIntegralIndex r' := fun hh => hR (hiff.mp hh)
    rw [finiteDilogValueMinus_of_not_isIntegralIndex A τ hR,
      finiteDilogValueMinus_of_not_isIntegralIndex A τ hR']
    exact finiteDilogValue_congr_of_fixed hirr hfixed hden hr hdiff

/-- **[RW26, Radchenko, Wheeler (2026), Lemma 2, `lem:lam.inv`] for `F⁺`**: `F` is
well defined on `G`, i.e. `F(r') = F(r)` for `r' - r ∈ ℤ²` and `γ ∈ Γ_r`. Off `ℤ²` this is the
periodicity of the cocycle at a fixed point, `sfModularCocycleRealTotal_congr_of_flt_eq_self`;
on `ℤ²` both sides are `√(j_γ(τ))`. -/
@[source "RW26, Lemma 2, p. 12, lem:lam.inv (F⁺)"]
theorem finiteDilogValue_congr (h : IsAttractiveFixedPoint A τ) {r r' : Fin 2 → ℚ}
    (hr : A ∈ gammaSubgroup r) (hdiff : IsIntegralIndex (r' - r)) :
    finiteDilogValue A τ r' = finiteDilogValue A τ r :=
  finiteDilogValue_congr_of_fixed h.irrational h.flt_eq h.fltDenominator_pos hr hdiff

/-- **[RW26, Radchenko, Wheeler (2026), Lemma 2, `lem:lam.inv`] for `F⁻`**, by
`finiteDilogValue_congr` off `ℤ²`. -/
@[source "RW26, Lemma 2, p. 12, lem:lam.inv (F⁻)"]
theorem finiteDilogValueMinus_congr (h : IsAttractiveFixedPoint A τ) {r r' : Fin 2 → ℚ}
    (hr : A ∈ gammaSubgroup r) (hdiff : IsIntegralIndex (r' - r)) :
    finiteDilogValueMinus A τ r' = finiteDilogValueMinus A τ r :=
  finiteDilogValueMinus_congr_of_fixed h.irrational h.flt_eq h.fltDenominator_pos hr hdiff

/-! ### The reflection law: equation (5)

`F(r) F⁻(-r) = ⟨r⟩⁻¹`, Kopp's Theorem 4.36 divided by `μ_γ² = ψ²(γ)`. -/

/-- The nonintegral case of `finiteDilogValue_mul_valueMinus_neg`. -/
private lemma finiteDilogValue_reflection_nonintegral (h : IsAttractiveFixedPoint A τ)
    {r : Fin 2 → ℚ} (hr : A ∈ gammaSubgroup r) (hR : ¬ IsIntegralIndex r) :
    finiteDilogValue A τ r * finiteDilogValueMinus A τ (-r) =
      (thetaCharacter r (A : Mat(2, ℤ)))⁻¹ := by
  have hn : ¬ IsIntegralIndex (-r) :=
    fun hh => hR ((isIntegralIndex_neg_iff r).mp hh)
  have hrn := neg_mem_gammaSubgroup hr
  have hprod := sfModularCocycleRealTotal_mul_neg_eq_character
    h.irrational hR hr h.lowerLeft_nonneg h.fltDenominator_pos h.flt_eq
  rw [finiteDilogValue_of_not_isIntegralIndex A τ hR,
    finiteDilogValueMinus_of_not_isIntegralIndex A τ hn,
    finiteDilogValue_of_not_isIntegralIndex A τ hn,
    sfModularCocycleReal'_of_mem hr,
    sfModularCocycleReal'_of_mem hrn,
    div_mul_div_comm, ← pow_two, etaMultiplier_sq_of_trace_pos h.trace_pos, hprod]
  field_simp [etaMultiplierSq_ne_zero A, thetaCharacter_ne_zero r (A : Mat(2, ℤ))]

/-- **[RW26, Radchenko, Wheeler (2026), Theorem 2, `thm:fg.equs`, equation (5),
`eq:Fgpm.reflection`]**: `F⁺(r) F⁻(-r) = ⟨r⟩⁻¹` for `γ ∈ Γ_r`, with the Gaussian
`⟨r⟩ = χ_r(γ)`. Off `ℤ²` it is [72, Kopp (2024), Theorem 4.36, `thm:shincharacter`] for the
real cocycle, `sfModularCocycleRealTotal_mul_neg_eq_character` (at `c ≥ 0`), divided into
`μ_γ² = ψ²(γ)` (`etaMultiplier_sq_of_trace_pos`, `IsAttractiveFixedPoint.trace_pos`); on `ℤ²` it
is `ε^{1/2} ε^{-1/2} = 1 = χ_r(γ)⁻¹` (`thetaCharacter_of_isIntegralIndex`). -/
@[source "RW26, equation (5), p. 3, eq:Fgpm.reflection"]
theorem finiteDilogValue_mul_valueMinus_neg (h : IsAttractiveFixedPoint A τ) {r : Fin 2 → ℚ}
    (hr : A ∈ gammaSubgroup r) :
    finiteDilogValue A τ r * finiteDilogValueMinus A τ (-r) =
      (thetaCharacter r (A : Mat(2, ℤ)))⁻¹ := by
  by_cases hR : IsIntegralIndex r
  · have hn : IsIntegralIndex (-r) := (isIntegralIndex_neg_iff r).mpr hR
    rw [finiteDilogValue_of_isIntegralIndex A τ hR,
      finiteDilogValueMinus_of_isIntegralIndex A τ hn,
      thetaCharacter_of_isIntegralIndex A hR, inv_one]
    have hj : Real.sqrt (fltDenominator (A : Mat(2, ℤ)) τ) ≠ 0 :=
      Real.sqrt_ne_zero'.mpr h.fltDenominator_pos
    exact_mod_cast mul_inv_cancel₀ hj
  · exact finiteDilogValue_reflection_nonintegral h hr hR

/-! ### Conjugation

`F_{RγR⁻¹}(Rr) = F_γ(r)` at the transported point `R·τ` for `j_R(τ) > 0`: the cocycle is
conjugation invariant by [72, Kopp (2024), Theorem 4.37, `thm:shinconj`], the eta multiplier by
`etaMultiplier_conj`, and `j_{RγR⁻¹}(R·τ) = j_γ(τ)` at a fixed point. -/

/-- **Conjugation invariance of `F`**: at an attractive fixed point `(γ, τ)` with `γ ∈ Γ_r` and
`R ∈ SL₂(ℤ)` with `j_R(τ) > 0`, `F_{RγR⁻¹}(Rr)` at `R·τ` equals `F_γ(r)` at `τ`. This is
[72, Kopp (2024), Theorem 4.37, `thm:shinconj`] (`sfModularCocycleRealTotal_mul_mul_inv`)
with `μ_{RγR⁻¹} = μ_γ` (`etaMultiplier_conj`). -/
theorem finiteDilogValue_mul_mul_inv (h : IsAttractiveFixedPoint A τ) {r : Fin 2 → ℚ}
    (hr : A ∈ gammaSubgroup r) (R : SL(2, ℤ))
    (hjR : 0 < fltDenominator (R : Mat(2, ℤ)) τ) :
    finiteDilogValue (R * A * R⁻¹) (flt (R : Mat(2, ℤ)) τ)
        (ratVecAction (R : Mat(2, ℤ)) r) =
      finiteDilogValue A τ r := by
  have hmem := mul_mul_inv_mem_gammaSubgroup_ratVecAction hr R
  by_cases hint : IsIntegralIndex r
  · have hint' := (isIntegralIndex_ratVecAction_iff R).mpr hint
    rw [finiteDilogValue_of_isIntegralIndex _ _ hint',
      finiteDilogValue_of_isIntegralIndex _ _ hint,
      fltDenominator_mul_mul_inv_of_flt_eq_self R hjR.ne'
        h.fltDenominator_pos.ne' h.flt_eq]
  · have hint' : ¬ IsIntegralIndex (ratVecAction (R : Mat(2, ℤ)) r) :=
      (isIntegralIndex_ratVecAction_iff R).not.mpr hint
    rw [finiteDilogValue_of_not_isIntegralIndex _ _ hint',
      finiteDilogValue_of_not_isIntegralIndex _ _ hint,
      sfModularCocycleReal'_of_mem hmem, sfModularCocycleReal'_of_mem hr,
      etaMultiplier_conj,
      sfModularCocycleRealTotal_mul_mul_inv hr R h.irrational hint h.flt_eq
        h.fltDenominator_pos hjR]

/-- The conjugation invariance `finiteDilogValue_mul_mul_inv` for `F⁻`. -/
theorem finiteDilogValueMinus_mul_mul_inv (h : IsAttractiveFixedPoint A τ)
    {r : Fin 2 → ℚ} (hr : A ∈ gammaSubgroup r) (R : SL(2, ℤ))
    (hjR : 0 < fltDenominator (R : Mat(2, ℤ)) τ) :
    finiteDilogValueMinus (R * A * R⁻¹) (flt (R : Mat(2, ℤ)) τ)
        (ratVecAction (R : Mat(2, ℤ)) r) =
      finiteDilogValueMinus A τ r := by
  by_cases hint : IsIntegralIndex r
  · have hint' := (isIntegralIndex_ratVecAction_iff R).mpr hint
    rw [finiteDilogValueMinus_of_isIntegralIndex _ _ hint',
      finiteDilogValueMinus_of_isIntegralIndex _ _ hint,
      fltDenominator_mul_mul_inv_of_flt_eq_self R hjR.ne'
        h.fltDenominator_pos.ne' h.flt_eq]
  · have hint' : ¬ IsIntegralIndex (ratVecAction (R : Mat(2, ℤ)) r) :=
      (isIntegralIndex_ratVecAction_iff R).not.mpr hint
    rw [finiteDilogValueMinus_of_not_isIntegralIndex _ _ hint',
      finiteDilogValueMinus_of_not_isIntegralIndex _ _ hint]
    exact finiteDilogValue_mul_mul_inv h hr R hjR

/-! ### Invariance under commuting matrices: equation (38)

`F⁻(Rr) = F⁻(r)` for `R` commuting with `γ`, fixing `τ`, with `j_R(τ) > 0`. -/

/-- **The invariance of [RW26, Radchenko, Wheeler (2026), equation (38), `eq:fgamma3sym`] for
`F⁻`**: `F⁻(Rr) = F⁻(r)` for `γ ∈ Γ_r` and `R ∈ SL₂(ℤ)` with `RγR⁻¹ = γ`, `R·τ = τ`, and
`j_R(τ) > 0`; the conjugation law `finiteDilogValueMinus_mul_mul_inv` at `RγR⁻¹ = γ`. -/
theorem finiteDilogValueMinus_ratVecAction (h : IsAttractiveFixedPoint A τ) {r : Fin 2 → ℚ}
    (hr : A ∈ gammaSubgroup r) {R : SL(2, ℤ)} (hcomm : R * A * R⁻¹ = A)
    (hR : flt (R : Mat(2, ℤ)) τ = τ) (hjR : 0 < fltDenominator (R : Mat(2, ℤ)) τ) :
    finiteDilogValueMinus A τ (ratVecAction (R : Mat(2, ℤ)) r) =
      finiteDilogValueMinus A τ r := by
  simpa only [hcomm, hR] using finiteDilogValueMinus_mul_mul_inv h hr R hjR

/-! ### The values on `G`

`E(x) = F(x/N)` and `F⁻(x) = F⁻(x/N)` at the lifted characteristic of a residue vector `x`. On
`G` these are Radchenko and Wheeler's `F^±_γ(u)`, `u ∈ G`, with `E(u) = F⁺_γ(u)` their finite
quantum dilogarithm; the zero class is the residue vector `0`. -/

/-- **The finite quantum dilogarithm `E(x) = F⁺(x)` on `G`**: the value `finiteDilogValue` at
the lifted characteristic `x/N` of a residue vector `x ∈ (ℤ/Nℤ)²`. On `G` this is
`E(u) = F⁺_γ(u)` of [RW26, Radchenko, Wheeler (2026), Proposition 10, `prop:rqffinitedilog`;
equation (2), `eq:fgam.def`]; it is meaningful for `x ∈ G`, where `γ ∈ Γ_{x/N}`. -/
def finiteDilogE (A : SL(2, ℤ)) (τ : ℝ) (x : Fin 2 → ZMod (finiteDilogOrder A)) : ℂ :=
  finiteDilogValue A τ (zmodCharacteristic (finiteDilogOrder A) x)

/-- **The value `F⁻(x)` on `G`**: `finiteDilogValueMinus` at the lifted characteristic, the
`F⁻_γ(u)`, `u ∈ G`, of [RW26, Radchenko, Wheeler (2026), equation (2), `eq:fgam.def`]. -/
def finiteDilogEMinus (A : SL(2, ℤ)) (τ : ℝ) (x : Fin 2 → ZMod (finiteDilogOrder A)) : ℂ :=
  finiteDilogValueMinus A τ (zmodCharacteristic (finiteDilogOrder A) x)

/-- The symmetry `F⁻(Rx) = F⁻(x)` on the residue group, used by
`finiteDilogTorsionSum_eq_zero`. -/
theorem finiteDilogEMinus_ratVecAction (h : IsAttractiveFixedPoint A τ) (R : SL(2, ℤ))
    (hcomm : R * A * R⁻¹ = A) (hR : flt (R : Mat(2, ℤ)) τ = τ)
    (hjR : 0 < fltDenominator (R : Mat(2, ℤ)) τ) (x : finiteDilogGroup A) :
    finiteDilogEMinus A τ (residueMulVec R (finiteDilogOrder A) x) =
      finiteDilogEMinus A τ x := by
  let _ : NeZero (finiteDilogOrder A) := finiteDilogOrder_neZero h
  have hr := (mem_finiteDilogGroup_iff h x).mp x.property
  have hrR : A ∈ gammaSubgroup
      (ratVecAction (R : Mat(2, ℤ)) (zmodCharacteristic (finiteDilogOrder A) x)) := by
    simpa only [hcomm] using mul_mul_inv_mem_gammaSubgroup_ratVecAction hr R
  exact (finiteDilogValueMinus_congr h hrR
    (isIntegralIndex_residueMulVec_sub R (finiteDilogOrder A) x)).trans
      (finiteDilogValueMinus_ratVecAction h hr hcomm hR hjR)

/-- At a conjugated fixed point, `RγR⁻¹` fixes `R·τ` with positive Jacobi denominator; used by
`finiteDilogE_conj` and `finiteDilogEMinus_conj`. -/
private theorem conj_fixed_point_data (h : IsAttractiveFixedPoint A τ) (R : SL(2, ℤ))
    (hR : 0 < fltDenominator (R : Mat(2, ℤ)) τ) :
    flt ((R * A * R⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) (flt (R : Mat(2, ℤ)) τ) =
        flt (R : Mat(2, ℤ)) τ ∧
      0 < fltDenominator ((R * A * R⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) (flt (R : Mat(2, ℤ)) τ) := by
  have hconj : ((R * A * R⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) * (R : Mat(2, ℤ)) =
      (R : Mat(2, ℤ)) * (A : Mat(2, ℤ)) := by
    exact congrArg (fun M : SL(2, ℤ) => (M : Mat(2, ℤ)))
      (show R * A * R⁻¹ * R = R * A by simp [mul_assoc])
  refine ⟨flt_of_mul_eq_of_flt_eq_self hconj hR.ne' h.fltDenominator_pos.ne' h.flt_eq, ?_⟩
  rw [fltDenominator_of_mul_eq_of_flt_eq_self hconj hR.ne'
    h.fltDenominator_pos.ne' h.flt_eq]
  exact h.fltDenominator_pos

/-- Conjugation transports `E` along the residue-group equivalence, by
`finiteDilogValue_mul_mul_inv` and integral periodicity. -/
theorem finiteDilogE_conj (h : IsAttractiveFixedPoint A τ) (R : SL(2, ℤ))
    (hR : 0 < fltDenominator (R : Mat(2, ℤ)) τ) (x : finiteDilogGroup A) :
    finiteDilogE (R * A * R⁻¹) (flt (R : Mat(2, ℤ)) τ)
      (finiteDilogGroup_conjAddEquiv A R x) = finiteDilogE A τ x := by
  let _ : NeZero (finiteDilogOrder A) := finiteDilogOrder_neZero h
  let B := R * A * R⁻¹
  obtain ⟨hfix, hden⟩ := conj_fixed_point_data h R hR
  have hr : A ∈ gammaSubgroup (zmodCharacteristic (finiteDilogOrder A) x) :=
    (mem_finiteDilogGroup_iff h x).mp x.property
  change finiteDilogValue B (flt (R : Mat(2, ℤ)) τ)
    (zmodCharacteristic (finiteDilogOrder B)
      (finiteDilogGroup_conjAddEquiv A R x : Fin 2 → ZMod (finiteDilogOrder B))) =
      finiteDilogValue A τ (zmodCharacteristic (finiteDilogOrder A) x)
  rw [zmodCharacteristic_conjAddEquiv]
  exact (finiteDilogValue_congr_of_fixed (Irrational.flt h.irrational R)
    hfix hden (mul_mul_inv_mem_gammaSubgroup_ratVecAction hr R)
    (isIntegralIndex_residueMulVec_sub R (finiteDilogOrder A) x)).trans
      (finiteDilogValue_mul_mul_inv h hr R hR)

/-- The same conjugation transport for `F⁻`, by
`finiteDilogValueMinus_mul_mul_inv` and integral periodicity. -/
theorem finiteDilogEMinus_conj (h : IsAttractiveFixedPoint A τ) (R : SL(2, ℤ))
    (hR : 0 < fltDenominator (R : Mat(2, ℤ)) τ) (x : finiteDilogGroup A) :
    finiteDilogEMinus (R * A * R⁻¹) (flt (R : Mat(2, ℤ)) τ)
      (finiteDilogGroup_conjAddEquiv A R x) = finiteDilogEMinus A τ x := by
  let _ : NeZero (finiteDilogOrder A) := finiteDilogOrder_neZero h
  let B := R * A * R⁻¹
  obtain ⟨hfix, hden⟩ := conj_fixed_point_data h R hR
  have hr : A ∈ gammaSubgroup (zmodCharacteristic (finiteDilogOrder A) x) :=
    (mem_finiteDilogGroup_iff h x).mp x.property
  change finiteDilogValueMinus B (flt (R : Mat(2, ℤ)) τ)
    (zmodCharacteristic (finiteDilogOrder B)
      (finiteDilogGroup_conjAddEquiv A R x : Fin 2 → ZMod (finiteDilogOrder B))) =
      finiteDilogValueMinus A τ (zmodCharacteristic (finiteDilogOrder A) x)
  rw [zmodCharacteristic_conjAddEquiv]
  exact (finiteDilogValueMinus_congr_of_fixed (Irrational.flt h.irrational R)
    hfix hden (mul_mul_inv_mem_gammaSubgroup_ratVecAction hr R)
    (isIntegralIndex_residueMulVec_sub R (finiteDilogOrder A) x)).trans
      (finiteDilogValueMinus_mul_mul_inv h hr R hR)

/-- `E(0) = ε^{1/2}` (`finiteDilogValue_of_isIntegralIndex` at the zero lift). -/
theorem finiteDilogE_zero (A : SL(2, ℤ)) (τ : ℝ) :
    finiteDilogE A τ 0 = ((Real.sqrt (fltDenominator (A : Mat(2, ℤ)) τ) : ℝ) : ℂ) := by
  rw [finiteDilogE, zmodCharacteristic_zero]
  exact finiteDilogValue_of_isIntegralIndex A τ (fun i => ⟨0, by simp⟩)

/-- `F⁻(0) = ε^{-1/2}`. -/
theorem finiteDilogEMinus_zero (A : SL(2, ℤ)) (τ : ℝ) :
    finiteDilogEMinus A τ 0 = (((Real.sqrt (fltDenominator (A : Mat(2, ℤ)) τ))⁻¹ : ℝ) : ℂ) := by
  rw [finiteDilogEMinus, zmodCharacteristic_zero]
  exact finiteDilogValueMinus_of_isIntegralIndex A τ (fun i => ⟨0, by simp⟩)

/-- Off the zero residue vector the two values agree, `F⁻(x) = E(x)`
(`isIntegralIndex_zmodCharacteristic_iff`). -/
theorem finiteDilogEMinus_of_ne_zero (h : IsAttractiveFixedPoint A τ)
    {x : Fin 2 → ZMod (finiteDilogOrder A)} (hx : x ≠ 0) :
    finiteDilogEMinus A τ x = finiteDilogE A τ x := by
  let _ : NeZero (finiteDilogOrder A) := finiteDilogOrder_neZero h
  exact finiteDilogValueMinus_of_not_isIntegralIndex A τ
    (fun hint => hx ((isIntegralIndex_zmodCharacteristic_iff _ x).mp hint))

/-- `E(x) ≠ 0` for `x ∈ G` (`finiteDilogValue_ne_zero`, `mem_finiteDilogGroup_iff`). -/
theorem finiteDilogE_ne_zero (h : IsAttractiveFixedPoint A τ)
    {x : Fin 2 → ZMod (finiteDilogOrder A)} (hx : x ∈ finiteDilogGroup A) :
    finiteDilogE A τ x ≠ 0 := by
  exact finiteDilogValue_ne_zero h ((mem_finiteDilogGroup_iff h x).mp hx)

/-- `F⁻(x) ≠ 0` for `x ∈ G` (`finiteDilogValueMinus_ne_zero`). -/
theorem finiteDilogEMinus_ne_zero (h : IsAttractiveFixedPoint A τ)
    {x : Fin 2 → ZMod (finiteDilogOrder A)} (hx : x ∈ finiteDilogGroup A) :
    finiteDilogEMinus A τ x ≠ 0 := by
  exact finiteDilogValueMinus_ne_zero h ((mem_finiteDilogGroup_iff h x).mp hx)

/-- **The reflection law (5) on `G`**: `E(x) F⁻(-x) = ⟨x⟩⁻¹` for `x ∈ G`, from
`finiteDilogValue_mul_valueMinus_neg` at the lifted characteristic, the lift of `-x` differing
from the negative of the lift by an integer vector (`isIntegralIndex_zmodCharacteristic_neg_add`,
`finiteDilogValueMinus_congr`). -/
theorem finiteDilogE_mul_EMinus_neg (h : IsAttractiveFixedPoint A τ)
    {x : Fin 2 → ZMod (finiteDilogOrder A)} (hx : x ∈ finiteDilogGroup A) :
    finiteDilogE A τ x * finiteDilogEMinus A τ (-x) =
      (fixedGaussian A (finiteDilogOrder A) x)⁻¹ := by
  let _ : NeZero (finiteDilogOrder A) := finiteDilogOrder_neZero h
  have hr := (mem_finiteDilogGroup_iff h x).mp hx
  have hsub : IsIntegralIndex
      (zmodCharacteristic (finiteDilogOrder A) (-x) -
        -(zmodCharacteristic (finiteDilogOrder A) x)) := by
    simpa only [sub_neg_eq_add] using
      isIntegralIndex_zmodCharacteristic_neg_add (finiteDilogOrder A) x
  have hcongr := finiteDilogValueMinus_congr h (neg_mem_gammaSubgroup hr) hsub
  rw [finiteDilogE, finiteDilogEMinus, hcongr]
  exact finiteDilogValue_mul_valueMinus_neg h hr

/-- **[RW26, Radchenko, Wheeler (2026), Theorem 5, `thm:fqdilogbasicproperties`](i) for
`E = F⁺_γ`**: `E(0)² = √N E(0) + 1`, i.e. `ε = √N ε^{1/2} + 1`, which is
`ε^{1/2} - ε^{-1/2} = √N` (`sqrt_finiteDilogOrder_eq`) multiplied by `ε^{1/2}`; noted as true
by (4) before Proposition 10 in [RW26, Radchenko, Wheeler (2026), Section 4.3,
`prop:rqffinitedilog`]. -/
@[source "RW26, Theorem 5, p. 16, thm:fqdilogbasicproperties (i, E = F⁺_γ)"]
theorem finiteDilogE_zero_sq (h : IsAttractiveFixedPoint A τ) :
    finiteDilogE A τ 0 ^ 2 =
      (Real.sqrt (finiteDilogOrder A) : ℂ) * finiteDilogE A τ 0 + 1 := by
  rw [finiteDilogE_zero]
  have hs : Real.sqrt (fltDenominator (A : Mat(2, ℤ)) τ) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr h.fltDenominator_pos
  have hreal : Real.sqrt (fltDenominator (A : Mat(2, ℤ)) τ) ^ 2 =
      Real.sqrt (finiteDilogOrder A) * Real.sqrt (fltDenominator (A : Mat(2, ℤ)) τ) + 1 := by
    have hsqrt := sqrt_finiteDilogOrder_eq h
    have hinv := mul_inv_cancel₀ hs
    have hmul := congrArg
      (fun t : ℝ => t * Real.sqrt (fltDenominator (A : Mat(2, ℤ)) τ)) hsqrt
    nlinarith [hmul]
  exact_mod_cast hreal

end SIC

end
