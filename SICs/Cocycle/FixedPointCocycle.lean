/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Cocycle.Conjugation
import SICs.SL2Z.HJStabilizer

/-!
# The cocycle relation at a common fixed point

The cocycle relation at a common irrational fixed point, `ש^r_{AB}(β) = ש^r_A(β)ש^r_B(β)` for `A, B
∈ Γ_r` with `j_A(β), j_B(β) > 0`, from the boundary limit of the coboundary `ϖ_r(A·τ)/ϖ_r(τ)`; hence
`ש^r_I(β) = 1`, the inverse and natural-power laws, and `ℤ²`-periodicity in `r` at a fixed point.

This file proves the cocycle property of the real multiplication values of the Shintani--Faddeev
modular cocycle: for `A, B ∈ Γ_r` fixing an irrational `β` with `j_A(β), j_B(β) > 0`,

$$
ש^{\mathbf r}_{AB}(\beta) = ש^{\mathbf r}_A(\beta)\,ש^{\mathbf r}_B(\beta),
$$

together with its consequences `ש^r_I(β) = 1`, `ש^r_{A⁻¹}(β) = ש^r_A(β)⁻¹` and
`ש^r_{A^n}(β) = ש^r_A(β)^n` for `n ∈ ℕ`. This is the step "by the cocycle property,
`ש^r_{A₀^{t+1}}(β) = ש^r_{A₀^t}(A₀·β) ש^r_{A₀}(β) = ש^r_{A₀^t}(β) ש^r_{A₀}(β)`, so by induction
`ש^r_{A₀^k}(β) = ש^r_{A₀}(β)^k`" of the proof of [AFK25, Theorem 2.20, `thm:field0`], which
reduces the value at an arbitrary element of the stabilizer of `β` to the value at its generator.
The file also records the `ℤ²`-periodicity of the value at a fixed point in the form the
finite dilogarithm values use (`SICs.Dilogarithm.Values`).

## Mathematical argument

On the upper half plane the Shintani--Faddeev modular cocycle is the coboundary
`ש^r_A(τ) = ϖ_r(A·τ)/ϖ_r(τ)` of the period product `ϖ_r` [72, Kopp (2024), Definition 4.18,
`defn:sfmodular`], so the cocycle relation `ש^r_{AB}(τ) = ש^r_A(B·τ) ש^r_B(τ)` is the identity

$$
\frac{\varpi_r(AB\cdot\tau)}{\varpi_r(\tau)}
  = \frac{\varpi_r(A\cdot(B\cdot\tau))}{\varpi_r(B\cdot\tau)}\cdot
    \frac{\varpi_r(B\cdot\tau)}{\varpi_r(\tau)},
\qquad \varpi_r(B\cdot\tau) \ne 0 ,
$$

the nonvanishing being the nonintegrality of `r` (`qPochhammer_ne_zero_of_not_isPeriodLatticePoint`,
`not_isPeriodLatticePoint_fracSymplecticFormRat_div`). At an irrational fixed point `β` of `A` and
`B` with positive Jacobi denominators, the real value `ש^r_M(β)` (`sfModularCocycleRealTotal`) is
the boundary value of the quotient along any approach `τ_k → β` from `ℍ`
(`tendsto_sfPeriodProduct_div_total`,
`sfModularCocycleRealTotal_eq_of_tendsto` of `SICs.Cocycle.Conjugation`). Along the vertical
approach `τ_k = β + i/(k+1)` (`tendsto_ofReal_add_I_div`), the points `B·τ_k` also tend to
`B·β = β` from inside `ℍ` (`flt_tendsto`, `flt_im_pos`), so the two factors on the right tend to
`ש^r_A(β)` and `ש^r_B(β)`, while the left side tends to `ש^r_{AB}(β)`, whose Jacobi denominator
`j_{AB}(β) = j_A(β) j_B(β)` (`fltDenominator_mul`) is positive. Uniqueness of limits gives the
relation. The value at `I` is the limit of the constant `1`, and the inverse and power laws follow
from the relation by group algebra, with `j_{A⁻¹}(β) = j_A(β)⁻¹`
(`fltDenominator_inv_mul_self_of_flt_eq_self`) and `j_{A^n}(β) = j_A(β)^n`
(`fltDenominator_pow_of_flt_eq_self`).

## References

- [AFK25, Theorem 2.20, `thm:field0`], proof (the cocycle property along the stabilizer).
- [72, Kopp (2024), Definition 4.18, `defn:sfmodular`] (the coboundary on `ℍ`).
-/

noncomputable section

open Complex Filter

open scoped MatrixGroups

namespace SIC

/-! ### The vertical approach and its image

`τ_k = β + i/(k+1)` tends to `β` from inside `ℍ`, and so does `B·τ_k` when `B·β = β`. -/

/-- **A Möbius image of the vertical approach to a fixed point is again an approach to it**:
if `B·β = β` and `j_B(β) ≠ 0`, then `B·(β + i/(k+1)) → β` (`flt_tendsto`,
`tendsto_ofReal_add_I_div`). -/
theorem tendsto_flt_ofReal_add_I_div_of_flt_eq_self (B : Mat(2, ℤ)) {β : ℝ}
    (hjB : fltDenominator B β ≠ 0) (hfix : flt B β = β) :
    Tendsto (fun k : ℕ => flt B ((β : ℂ) + I * (1 / ((k : ℂ) + 1)))) atTop (nhds (β : ℂ)) := by
  have h := flt_tendsto B (tendsto_ofReal_add_I_div β) (by exact_mod_cast hjB)
  have hfix' : flt B (β : ℂ) = (β : ℂ) := by exact_mod_cast hfix
  rwa [hfix'] at h

/-! ### The cocycle relation -/

/-- **The cocycle relation at a common irrational fixed point**, the step "by the cocycle
property" in the proof of [AFK25, Theorem 2.20, `thm:field0`]: for `A, B ∈ Γ_r`, `r ∉ ℤ²`, an
irrational `β` with `A·β = β = B·β` and `j_A(β), j_B(β) > 0`,

$$ש^{\mathbf r}_{AB}(\beta) = ש^{\mathbf r}_A(\beta)\,ש^{\mathbf r}_B(\beta).$$

On `ℍ` the quotient `ϖ_r(AB·τ)/ϖ_r(τ)` is the product of the quotients for `A` at `B·τ` and for
`B` at `τ` (`flt_mul`, `sfPeriodProduct_ne_zero`, `div_mul_div_cancel₀`); along the vertical
approach to `β` each factor tends to the corresponding real value
(`tendsto_sfPeriodProduct_div_total`,
`tendsto_flt_ofReal_add_I_div_of_flt_eq_self`, `flt_im_pos`), and the left side to `ש^r_{AB}(β)`
(`sfModularCocycleRealTotal_eq_of_tendsto`, with `j_{AB}(β) = j_A(β)j_B(β) > 0` by
`fltDenominator_mul`). -/
theorem sfModularCocycleRealTotal_mul_of_flt_eq_self {r : Fin 2 → ℚ} {A B : SL(2, ℤ)}
    (hA : A ∈ gammaSubgroup r)
    (hB : B ∈ gammaSubgroup r) {β : ℝ} (hβ : Irrational β)
    (hr : ¬ IsIntegralIndex r)
    (hfixA : flt (A : Mat(2, ℤ)) β = β)
    (hfixB : flt (B : Mat(2, ℤ)) β = β)
    (hjA : 0 < fltDenominator (A : Mat(2, ℤ)) β)
    (hjB : 0 < fltDenominator (B : Mat(2, ℤ)) β) :
    sfModularCocycleRealTotal r (A * B)
        (mul_mem_gammaSubgroup hA hB) β =
      sfModularCocycleRealTotal r A hA β * sfModularCocycleRealTotal r B hB β := by
  let tauSeq : ℕ → ℂ := fun k => (β : ℂ) + I * (1 / ((k : ℂ) + 1))
  have htau : Tendsto tauSeq atTop (nhds (β : ℂ)) := tendsto_ofReal_add_I_div β
  have him : ∀ᶠ k in atTop, 0 < (tauSeq k).im :=
    Filter.Eventually.of_forall (im_ofReal_add_I_div_pos β)
  have hBtend := tendsto_flt_ofReal_add_I_div_of_flt_eq_self
    (B : Mat(2, ℤ)) hjB.ne' hfixB
  have hBim : ∀ᶠ k in atTop, 0 < (flt (B : Mat(2, ℤ)) (tauSeq k)).im :=
    him.mono fun _ hk => flt_im_pos B hk
  have hABfix : flt ((A * B : SL(2, ℤ)) : Mat(2, ℤ)) β = β := by
    rw [Matrix.SpecialLinearGroup.coe_mul,
      flt_mul _ _ β hjB.ne', hfixB, hfixA]
  have hABden : 0 < fltDenominator
      ((A * B : SL(2, ℤ)) : Mat(2, ℤ)) β := by
    rw [Matrix.SpecialLinearGroup.coe_mul, fltDenominator_mul _ _ β hjB.ne', hfixB]
    exact mul_pos hjA hjB
  have hleft := tendsto_sfPeriodProduct_div_total
    tauSeq (mul_mem_gammaSubgroup hA hB) hr hβ hABden hABfix htau him
  have hright := (tendsto_sfPeriodProduct_div_total
    (fun k => flt (B : Mat(2, ℤ)) (tauSeq k)) hA hr hβ hjA hfixA
      hBtend hBim).mul
    (tendsto_sfPeriodProduct_div_total
      tauSeq hB hr hβ hjB hfixB htau him)
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  filter_upwards [him] with k hk
  have hdenB := fltDenominator_ne_zero_of_im_ne_zero B hk.ne'
  have himB := flt_im_pos B hk
  rw [Matrix.SpecialLinearGroup.coe_mul, flt_mul _ _ _ hdenB,
    div_mul_div_cancel₀ (sfPeriodProduct_ne_zero hr himB)]

/-- **`I ∈ Γ_r`** (`mem_gammaSubgroup_of_isIntegralIndex`, `ratVecAction_one`). -/
theorem one_mem_gammaSubgroup (r : Fin 2 → ℚ) :
    (1 : SL(2, ℤ)) ∈ gammaSubgroup r := by
  apply mem_gammaSubgroup_of_isIntegralIndex
  change IsIntegralIndex (ratVecAction (1 : Mat(2, ℤ)) r - r)
  rw [ratVecAction_one, sub_self]
  exact fun _ => ⟨0, rfl⟩

/-- **The value at the identity is $1$** for every characteristic and every real argument,
by `sfModularCocycleReal_one`, which cancels the integral correction before evaluation. -/
theorem sfModularCocycleRealTotal_one (r : Fin 2 → ℚ) {β : ℝ} :
    sfModularCocycleRealTotal r 1 (one_mem_gammaSubgroup r) β = 1 := by
  rw [sfModularCocycleRealTotal_of_nonneg _ (by simp), sfModularCocycleReal_one]

/-- **The value at the inverse is the inverse of the value**, for `A ∈ Γ_r` fixing an
irrational `β` with `j_A(β) > 0`: from `sfModularCocycleRealTotal_mul_of_flt_eq_self` at
`A⁻¹`, `A` and `sfModularCocycleRealTotal_one`, with `A⁻¹·β = β` (`flt_inv_of_flt_eq_self`) and
`j_{A⁻¹}(β) = j_A(β)⁻¹ > 0` (`fltDenominator_inv_mul_self_of_flt_eq_self`). The lemma
`sfModularCocycleRealTotal_inv_of_flt_eq_self` of `SICs.Cocycle.Modular.Values` is the same
statement
under the hypothesis `A₁₀ > 0` in place of `j_A(β) > 0`. -/
theorem sfModularCocycleRealTotal_inv_of_irrational {r : Fin 2 → ℚ}
    {A : SL(2, ℤ)} (hA : A ∈ gammaSubgroup r) {β : ℝ}
    (hβ : Irrational β) (hr : ¬ IsIntegralIndex r)
    (hfix : flt (A : Mat(2, ℤ)) β = β)
    (hjA : 0 < fltDenominator (A : Mat(2, ℤ)) β) :
    sfModularCocycleRealTotal r A⁻¹ (inv_mem_gammaSubgroup hA) β =
      (sfModularCocycleRealTotal r A hA β)⁻¹ := by
  have hfixInv := flt_inv_of_flt_eq_self hjA.ne' hfix
  have hdenInv := fltDenominator_inv_mul_self_of_flt_eq_self hjA.ne' hfix
  have hdenInvEq : fltDenominator
      ((A⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) β =
      (fltDenominator (A : Mat(2, ℤ)) β)⁻¹ :=
    eq_inv_of_mul_eq_one_left hdenInv
  have hjInv : 0 < fltDenominator
      ((A⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) β := by
    rw [hdenInvEq]
    exact inv_pos.mpr hjA
  have hmul := sfModularCocycleRealTotal_mul_of_flt_eq_self
    (inv_mem_gammaSubgroup hA) hA hβ hr hfixInv hfix hjInv hjA
  have hproduct : sfModularCocycleRealTotal r A⁻¹ (inv_mem_gammaSubgroup hA) β *
      sfModularCocycleRealTotal r A hA β = 1 := by
    calc
      _ = sfModularCocycleRealTotal r (A⁻¹ * A)
          (mul_mem_gammaSubgroup (inv_mem_gammaSubgroup hA) hA) β := hmul.symm
      _ = sfModularCocycleRealTotal r 1 (one_mem_gammaSubgroup r) β :=
        sfModularCocycleRealTotal_congr (inv_mul_cancel A) _ _ β
      _ = 1 := sfModularCocycleRealTotal_one r
  exact eq_inv_of_mul_eq_one_left hproduct

/-- **The value at a natural power is the power of the value**: `ש^r_{A^n}(β) = ש^r_A(β)^n` for
`A ∈ Γ_r` fixing an irrational `β` with `j_A(β) > 0`, by induction from
`sfModularCocycleRealTotal_mul_of_flt_eq_self` (`pow_succ`, `flt_pow_of_flt_eq_self`,
`fltDenominator_pow_of_flt_eq_self`) and `sfModularCocycleRealTotal_one`. -/
theorem sfModularCocycleRealTotal_pow_of_flt_eq_self {r : Fin 2 → ℚ} {A : SL(2, ℤ)}
    (hA : A ∈ gammaSubgroup r) {β : ℝ} (hβ : Irrational β)
    (hr : ¬ IsIntegralIndex r) (hfix : flt (A : Mat(2, ℤ)) β = β)
    (hjA : 0 < fltDenominator (A : Mat(2, ℤ)) β) (n : ℕ) :
    sfModularCocycleRealTotal r (A ^ n) (pow_mem_gammaSubgroup hA n) β =
      sfModularCocycleRealTotal r A hA β ^ n := by
  induction n with
  | zero =>
      simpa only [pow_zero] using sfModularCocycleRealTotal_one r
  | succ n ih =>
      have hfixPow := flt_pow_of_flt_eq_self hjA.ne' hfix n
      have hjPow : 0 < fltDenominator
          ((A ^ n : SL(2, ℤ)) : Mat(2, ℤ)) β := by
        rw [fltDenominator_pow_of_flt_eq_self hjA.ne' hfix]
        exact pow_pos hjA n
      have hmul := sfModularCocycleRealTotal_mul_of_flt_eq_self
        (pow_mem_gammaSubgroup hA n) hA hβ hr hfixPow hfix hjPow hjA
      calc
        sfModularCocycleRealTotal r (A ^ n.succ) (pow_mem_gammaSubgroup hA n.succ) β =
            sfModularCocycleRealTotal r (A ^ n * A)
              (mul_mem_gammaSubgroup (pow_mem_gammaSubgroup hA n) hA) β :=
          sfModularCocycleRealTotal_congr (pow_succ A n) _ _ β
        _ = sfModularCocycleRealTotal r (A ^ n) (pow_mem_gammaSubgroup hA n) β *
              sfModularCocycleRealTotal r A hA β := hmul
        _ = sfModularCocycleRealTotal r A hA β ^ n *
              sfModularCocycleRealTotal r A hA β := by rw [ih]
        _ = sfModularCocycleRealTotal r A hA β ^ n.succ := (pow_succ _ n).symm

/-! ### `ℤ²`-periodicity at a fixed point

`sfModularCocycleRealTotal_congr_of_sub_intVec` of `SICs.Cocycle.Modular.Shifts` asks for the domain
memberships and `M₁₀ ≠ 0`; at an irrational fixed point with `j_M(β) > 0` these are automatic,
except that `M₁₀ = 0` forces `M = I`, where both values are `1`. -/

/-- **A matrix with vanishing lower-left entry fixing an irrational number with positive Jacobi
denominator is the identity**: `M = [[a, b], [0, d]]` with `ad = 1` and `j_M(β) = d > 0` gives
`d = 1`, so the bottom row is `(0, 1)` and `eq_one_of_row_one_eq_zero_one_of_flt_eq_self`
applies. -/
theorem eq_one_of_lowerLeft_eq_zero_of_flt_eq_self {M : SL(2, ℤ)} {β : ℝ}
    (h0 : M 1 0 = 0) (hfix : flt (M : Mat(2, ℤ)) β = β)
    (hj : 0 < fltDenominator (M : Mat(2, ℤ)) β) : M = 1 := by
  have hdet : M 0 0 * M 1 1 = 1 := by
    have h := M.2
    rw [Matrix.det_fin_two, h0, mul_zero, sub_zero] at h
    exact h
  rw [fltDenominator, h0] at hj
  norm_num at hj
  obtain ⟨_, h11⟩ | ⟨_, h11⟩ := Int.eq_one_or_neg_one_of_mul_eq_one' hdet
  · apply eq_one_of_row_one_eq_zero_one_of_flt_eq_self _ hfix
    funext i
    fin_cases i <;> simp_all
  · rw [h11] at hj
    norm_num at hj

/-- **`ℤ²`-periodicity of the value at an irrational fixed point with positive Jacobi
denominator**: `ש^{r'}_M(β) = ש^r_M(β)` for `r' - r ∈ ℤ²`. For `M₁₀ ≠ 0` this is
`sfModularCocycleRealTotal_congr_of_sub_intVec`, whose domain hypotheses are `j_M(β) > 0`
(`mem_sfDomain_ofReal_iff`) and `j_{M⁻¹}(β) = j_M(β)⁻¹ > 0`
(`fltDenominator_inv_mul_self_of_flt_eq_self`); for `M₁₀ = 0`, `M = I`
(`eq_one_of_lowerLeft_eq_zero_of_flt_eq_self`) and both sides are `1`
(`sfModularCocycleRealTotal_one`). -/
theorem sfModularCocycleRealTotal_congr_of_flt_eq_self {r r' : Fin 2 → ℚ}
    {M : SL(2, ℤ)} (hM : M ∈ gammaSubgroup r)
    (hM' : M ∈ gammaSubgroup r') {β : ℝ} (hβ : Irrational β)
    (hr : ¬ IsIntegralIndex r) (hfix : flt (M : Mat(2, ℤ)) β = β)
    (hj : 0 < fltDenominator (M : Mat(2, ℤ)) β)
    (hdiff : IsIntegralIndex (r' - r)) :
    sfModularCocycleRealTotal r' M hM' β = sfModularCocycleRealTotal r M hM β := by
  by_cases h0 : M 1 0 = 0
  · have hMone := eq_one_of_lowerLeft_eq_zero_of_flt_eq_self h0 hfix hj
    subst M
    calc
      sfModularCocycleRealTotal r' 1 hM' β = 1 :=
        sfModularCocycleRealTotal_one r'
      _ = sfModularCocycleRealTotal r 1 hM β :=
        (sfModularCocycleRealTotal_one r).symm
  · have hdenInv := fltDenominator_inv_mul_self_of_flt_eq_self hj.ne' hfix
    have hdenInvEq : fltDenominator
        ((M⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) β =
        (fltDenominator (M : Mat(2, ℤ)) β)⁻¹ :=
      eq_inv_of_mul_eq_one_left hdenInv
    have hjInv : 0 < fltDenominator
        ((M⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) β := by
      rw [hdenInvEq]
      exact inv_pos.mpr hj
    exact sfModularCocycleRealTotal_congr_of_sub_intVec r r' M hM hM' hβ hr
      ((mem_sfDomain_ofReal_iff M β).mpr hj)
      ((mem_sfDomain_ofReal_iff M⁻¹ β).mpr hjInv) hfix h0 hdiff

end SIC

end
