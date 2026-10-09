/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Cocycle.ModularBoundary
import SICs.Cocycle.Modular.Reflection

/-!
# The `GL₂(ℤ)`-invariance of the real multiplication values

Kopp's Theorem 4.37, the `GL₂(ℤ)`-invariance of the real multiplication values, for
`j_R(β) > 0`: `ש^{Rr}_{RAR⁻¹}(R·β) = ש^r_A(β)` for `det R = 1` and its complex conjugate for
`det R = -1`, through the boundary limit of the period-product quotient for the total cocycle; the
theorem at the conjugate `RAR⁻¹` itself with its transported fixed-point data.

This file proves [72, Kopp (2024), Theorem 4.37, `thm:shinconj`] for the real cocycle value
`sfModularCocycleRealTotal` of `SICs.Cocycle.Modular.Values`: for `r ∈ ℚ² ∖ ℤ²`, `A ∈ Γ_r`, an
irrational fixed point `β` of `A` with `j_A(β) > 0`, and `R ∈ GL₂(ℤ)` with `j_R(β) > 0`,

$$
ש^{R\mathbf r}_{RAR^{-1}}(R\cdot\beta) =
\begin{cases} ש^{\mathbf r}_A(\beta) & \det R = 1,\\
\overline{ש^{\mathbf r}_A(\beta)} & \det R = -1.\end{cases}
$$

Kopp's statement carries the sign `s_R(β) = sgn j_R(β)` on the characteristic, `s_R(β)Rr`; only
the case `j_R(β) > 0`, where `s_R(β) = 1`, is formalized.

Kopp states the theorem for every `r ∈ ℚ²` and every `β ∈ D̃_A` with `A·β = β`, where his domain
`D̃_A` [72, Kopp (2024), eq. (4.3), `eq:tDD`] is `j_A(β) > 0` for `A₁₀ ≠ 0` and all of `ℂ` for
`A₁₀ = 0`. The additional hypotheses `r ∉ ℤ²` and `β` irrational are required by the boundary
limit `tendsto_sfPeriodProduct_div_of_not_isIntegralIndex`. The condition `j_A(β) > 0` is
assumed in every case, which excludes Kopp's corner `A = -T^k` at a real `β`. The formal
statement thus covers the real nonintegral fixed-point values in this restricted domain.

The conjugate `RAR⁻¹` is written as a matrix `A'` with `A'R = RA`, so that no inverse of an
integer matrix of determinant `-1` appears; `R` is an element of `SL(2, ℤ)` in the first case
and an integer matrix of determinant `-1` in the second. For `R ∈ SL(2, ℤ)` the file also states
the theorem at `A' = RAR⁻¹` itself, with the transported fixed-point data
(`sfModularCocycleRealTotal_mul_mul_inv`), the form in which reductions to a reduced
representative use it.

## Mathematical argument

Kopp proves the theorem on the upper half plane and passes to the boundary. The real cocycle value
is the boundary value of the period-product quotient
(`tendsto_sfPeriodProduct_div_of_not_isIntegralIndex`), so the same argument
applies once that theorem is extended to `sfModularCocycleRealTotal`, i.e. to matrices with a
negative lower-left entry (`tendsto_sfPeriodProduct_div_total`: at a fixed
point the total value is the reciprocal of the word value at `M⁻¹`, and the quotient for `M⁻¹`
along `M·τ_k` is the reciprocal of the quotient for `M`). Uniqueness of limits then identifies the
total value at a fixed point with the limit of the quotient along any approach from `ℍ`
(`sfModularCocycleRealTotal_eq_of_tendsto`).

*Determinant one.* For `R ∈ SL₂(ℤ)` and `τ ∈ ℍ`, the transformation law
[AFK25, equation (1.25), `eq:LActOnSymplecticInnerProduct`] gives
`ϖ_{Rr}(R·τ) = ϖ(⟨⟨r,τ⟩⟩/j_R(τ), R·τ) = J_R(τ)·ϖ_r(τ)` with `J_R` the Jacobi-cocycle quotient of
[AFK25, Definition 1.16, `df:shinfadjacocycle`] (`sfPeriodProduct_ratVecAction_flt`). Hence

$$\frac{\varpi_{R\mathbf r}(RAR^{-1}\cdot R\tau)}{\varpi_{R\mathbf r}(R\tau)}
  = \frac{J_R(A\tau)}{J_R(\tau)}\cdot\frac{\varpi_{\mathbf r}(A\tau)}{\varpi_{\mathbf r}(\tau)}.$$

As `τ → β` inside `ℍ`, both `J_R(τ)` and `J_R(Aτ)` tend to the nonzero word value
`σ_R(⟨⟨r,β⟩⟩, β)` (`tendsto_qPochhammer_div_wordSigmaS`, which needs
`j_R(β) > 0` and `0 ≤ R₁₀`, and `wordSigmaS_ne_zero`), so the right-hand side tends to
`ש^r_A(β)`, while the left-hand side, along `R·τ → R·β`, tends to `ש^{Rr}_{RAR⁻¹}(R·β)`. The
orientation `0 ≤ R₁₀` is removed by exchanging the roles of the two pairs (the statement is
symmetric under `R ↦ R⁻¹`).

*Determinant minus one.* Every such `R` is `R'R₀` with `R' ∈ SL₂(ℤ)` and `R₀ = diag(-1, 1)`,
so it suffices to treat `R₀`, where `R₀·τ = -τ`. Complex conjugation of the convergent product
gives `conj ϖ_r(τ) = ϖ_{R₀r}(-conj τ)` for `τ ∈ ℍ` (`conj_sfPeriodProduct`; Kopp's
eq. (4.21), `eq:varpibar`), and `R₀AR₀·(-conj τ) = -conj(A·τ)`, so the quotient for
`(R₀r, R₀AR₀)` along `-conj τ_k → -β` is the conjugate of the quotient for `(r, A)` along
`τ_k → β`.

## References

- [72, Kopp (2024), Theorem 4.37, `thm:shinconj`], and its proof; [72, Kopp (2024), Lemma 4.10,
  `lem:jeval`] for `j_{RAR⁻¹}(R·β) = j_A(β)`.
- [AFK25, Definition 1.16, `df:shinfadjacocycle`; equation (1.25),
  `eq:LActOnSymplecticInnerProduct`].
-/

noncomputable section

open Complex Filter
open scoped MatrixGroups

namespace SIC

/-! ### The reflection matrix

The reflection `R₀ = diag(-1, 1)` represents the determinant-minus-one case of the
conjugation argument. Fixed-point transport and characteristic integrality are supplied by
`SICs.SL2Z.FractionalLinear` and `SICs.SL2Z.Characteristics`. -/

/-- **The reflection** `R₀ = diag(-1, 1) ∈ GL₂(ℤ)`, the representative of the nontrivial coset of
`SL₂(ℤ)` used in the proof of [72, Kopp (2024), Theorem 4.37, `thm:shinconj`]; it acts by
`τ ↦ -τ` and on characteristics by `(r₁, r₂) ↦ (-r₁, r₂)`. -/
def reflectionMatrix : Mat(2, ℤ) := !![-1, 0; 0, 1]

/-- `det R₀ = -1`. -/
theorem det_reflectionMatrix : reflectionMatrix.det = -1 := by
  simp [reflectionMatrix, Matrix.det_fin_two]

/-- `R₀ R₀ = 1`. -/
theorem reflectionMatrix_mul_self : reflectionMatrix * reflectionMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [reflectionMatrix]

/-- `j_{R₀}(τ) = 1`, at a point `τ` of any division ring. -/
theorem fltDenominator_reflectionMatrix {K : Type*} [DivisionRing K] (τ : K) :
    fltDenominator reflectionMatrix τ = 1 := by
  simp [fltDenominator, reflectionMatrix]

/-- `R₀·τ = -τ`, at a point `τ` of any division ring. -/
theorem flt_reflectionMatrix {K : Type*} [DivisionRing K] (τ : K) :
    flt reflectionMatrix τ = -τ := by
  simp [flt, reflectionMatrix]

/-- `R₀ r = (-r₁, r₂)`, coordinatewise. -/
theorem ratVecAction_reflectionMatrix_apply (r : Fin 2 → ℚ) :
    ratVecAction reflectionMatrix r 0 = -r 0 ∧ ratVecAction reflectionMatrix r 1 = r 1 := by
  simp [ratVecAction, reflectionMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-! ### The period product under `SL₂(ℤ)` and under complex conjugation

The two identities on `ℍ` that Kopp's proof rests on: the transformation law of the period product
under `R ∈ SL₂(ℤ)`, and its behaviour under complex conjugation, [72, Kopp (2024), eq. (4.21),
`eq:varpibar`]. -/

/-- **The period product at a transformed characteristic and modulus**: for `R ∈ SL₂(ℤ)` and
`τ ∈ ℍ`, `ϖ_{Rr}(R·τ) = ϖ(⟨⟨r,τ⟩⟩/j_R(τ), R·τ)`, by the transformation law
[AFK25, equation (1.25), `eq:LActOnSymplecticInnerProduct`] (`fracSymplecticFormRat_ratVecAction`)
with `det R = 1`. The right-hand side is the numerator of the Jacobi cocycle quotient
`σ_R(⟨⟨r,τ⟩⟩, τ)` of [AFK25, Definition 1.16, `df:shinfadjacocycle`]. -/
theorem sfPeriodProduct_ratVecAction_flt (R : SL(2, ℤ)) (r : Fin 2 → ℚ) {τ : ℂ}
    (hτ : 0 < τ.im) :
    sfPeriodProduct (ratVecAction (R : Mat(2, ℤ)) r)
        (flt (R : Mat(2, ℤ)) τ) =
      qPochhammer (fracSymplecticFormRat r τ / fltDenominator (R : Mat(2, ℤ)) τ)
        (flt (R : Mat(2, ℤ)) τ) := by
  unfold sfPeriodProduct
  rw [fracSymplecticFormRat_ratVecAction _ r τ
    (fltDenominator_ne_zero_of_im_ne_zero R hτ.ne'), R.2]
  simp

/-- **Complex conjugation reflects the period product**, [72, Kopp (2024), eq. (4.21),
`eq:varpibar`] in the proof of Theorem 4.37: for `τ ∈ ℍ`, `conj ϖ_r(τ) = ϖ_{R₀r}(-conj τ)`, since
conjugating each
factor `1 - e((k + r₂)τ - r₁)` gives `1 - e((k + r₂)(-conj τ) + r₁)`, the factor of
`ϖ_{(-r₁, r₂)}` at `-conj τ ∈ ℍ`. Conjugation is a continuous ring homomorphism, so it passes
through the convergent product (`HasProd.map` with the `HasProd` of `qPochhammer_multipliable`,
or `tprod` under a continuous multiplicative equivalence). -/
theorem conj_sfPeriodProduct (r : Fin 2 → ℚ) {τ : ℂ} (hτ : 0 < τ.im) :
    starRingEnd ℂ (sfPeriodProduct r τ) =
      sfPeriodProduct (ratVecAction reflectionMatrix r) (-(starRingEnd ℂ τ)) := by
  rcases ratVecAction_reflectionMatrix_apply r with ⟨hr0, hr1⟩
  unfold sfPeriodProduct qPochhammer
  have hp := (qPochhammer_multipliable (fracSymplecticFormRat r τ) τ hτ).hasProd
  rw [← (hp.map (starRingEnd ℂ) Complex.continuous_conj).tprod_eq]
  apply tprod_congr
  intro j
  simp only [Function.comp_apply, map_sub, map_one, ← Complex.exp_conj, map_mul,
    map_add, map_natCast, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  congr 2
  simp only [fracSymplecticFormRat, hr0, hr1, Rat.cast_neg, map_sub, map_mul,
    map_ratCast]
  ring

/-- **Complex conjugation commutes with the action of an integer matrix**:
`conj (M·τ) = M·(conj τ)`, since the entries are real (`map_div₀`, `map_add`, `map_mul`,
`map_intCast`). -/
theorem conj_flt (M : Mat(2, ℤ)) (τ : ℂ) :
    starRingEnd ℂ (flt M τ) = flt M (starRingEnd ℂ τ) := by
  simp only [flt, map_div₀, map_add, map_mul, map_intCast]

/-- Composing `A'` with the reflection transports its action at `conj τ` to the action of
`A'` at `-conj τ`; this is the left composition step in
`flt_neg_conj_of_mul_reflectionMatrix_eq`. -/
private theorem flt_mul_reflectionMatrix_conj {A' : SL(2, ℤ)} (τ : ℂ) :
    flt (A' : Mat(2, ℤ)) (-(starRingEnd ℂ τ)) =
      flt ((A' : Mat(2, ℤ)) * reflectionMatrix) (starRingEnd ℂ τ) := by
  rw [flt_mul _ _ _ (by simp [fltDenominator_reflectionMatrix]), flt_reflectionMatrix]

/-- Composing the reflection with `A` sends `conj τ` to `-conj (A·τ)`; this is the right
composition step in `flt_neg_conj_of_mul_reflectionMatrix_eq`. -/
private theorem flt_reflectionMatrix_mul_conj {A : SL(2, ℤ)} {τ : ℂ} (hτ : 0 < τ.im) :
    flt (reflectionMatrix * (A : Mat(2, ℤ))) (starRingEnd ℂ τ) =
      -(starRingEnd ℂ (flt (A : Mat(2, ℤ)) τ)) := by
  have him : (starRingEnd ℂ τ).im ≠ 0 := by
    simp only [conj_im, ne_eq, neg_eq_zero]
    exact hτ.ne'
  rw [flt_mul _ _ _ (fltDenominator_ne_zero_of_im_ne_zero A him)]
  simp only [flt_reflectionMatrix, conj_flt]

/-- **The reflected conjugate acts by `-conj`**: if `A'R₀ = R₀A` then
`A'·(-conj τ) = -conj (A·τ)` for `τ ∈ ℍ`, from `flt_mul` on both sides of `A'R₀ = R₀A` at
`conj τ` (whose imaginary part is nonzero, `fltDenominator_ne_zero_of_im_ne_zero`),
`flt_reflectionMatrix` and `conj_flt`. -/
theorem flt_neg_conj_of_mul_reflectionMatrix_eq {A A' : SL(2, ℤ)}
    (hconj : (A' : Mat(2, ℤ)) * reflectionMatrix =
      reflectionMatrix * (A : Mat(2, ℤ))) {τ : ℂ} (hτ : 0 < τ.im) :
    flt (A' : Mat(2, ℤ)) (-(starRingEnd ℂ τ)) =
      -(starRingEnd ℂ (flt (A : Mat(2, ℤ)) τ)) := by
  rw [flt_mul_reflectionMatrix_conj τ, hconj,
    flt_reflectionMatrix_mul_conj hτ]

/-! ### The total cocycle at a fixed point as a boundary value

`tendsto_sfPeriodProduct_div_of_not_isIntegralIndex` is extended to
`sfModularCocycleRealTotal`, for either sign of `M₁₀`, at an irrational fixed point in `D_M`; the
total value is then characterized as the limit of the quotient along any approach from `ℍ`. -/

/-- **The real cocycle does not vanish at an irrational fixed point** with `j_M(τ) > 0` and
`r ∉ ℤ²`: the reflected product has modulus one
(`norm_sfModularCocycleReal_mul_neg_of_flt_eq_self`, with
`sigmaSLatticeFree_fracSymplecticFormRat`), so neither factor is zero. -/
theorem sfModularCocycleReal_ne_zero_of_flt_eq_self {r : Fin 2 → ℚ} {M : SL(2, ℤ)}
    (hM : M ∈ gammaSubgroup r) (h0 : 0 ≤ M 1 0) {τ : ℝ}
    (hτ : Irrational τ) (hr : ¬ IsIntegralIndex r)
    (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) τ)
    (hfix : flt (M : Mat(2, ℤ)) τ = τ) :
    sfModularCocycleReal r M hM h0 τ ≠ 0 := by
  intro hz
  have hnorm := norm_sfModularCocycleReal_mul_neg_of_flt_eq_self hτ hM h0 hjac hfix
    (sigmaSLatticeFree_fracSymplecticFormRat hτ hr)
  rw [hz, zero_mul, norm_zero] at hnorm
  norm_num at hnorm

/-- **The total cocycle at a negatively oriented matrix, at a fixed point**: for `M₁₀ < 0` and
`M·τ = τ` with `j_M(τ) ≠ 0`, `ש^r_M(τ) = (ש^r_{M⁻¹}(τ))⁻¹` with `M⁻¹`'s word value; the
definition `sfModularCocycleRealTotal` with `M·τ = τ` substituted. -/
theorem sfModularCocycleRealTotal_of_neg_of_flt_eq_self {r : Fin 2 → ℚ} {M : SL(2, ℤ)}
    (hM : M ∈ gammaSubgroup r) (hneg : M 1 0 < 0) {τ : ℝ}
    (hfix : flt (M : Mat(2, ℤ)) τ = τ) :
    sfModularCocycleRealTotal r M hM τ =
      (sfModularCocycleReal r M⁻¹ (inv_mem_gammaSubgroup hM)
        (by rw [SL2Z.lowerLeft_inv]; omega) τ)⁻¹ := by
  rw [sfModularCocycleRealTotal, dite_eq_right (by omega), hfix]

/-- At a fixed point with positive Jacobi denominator, the inverse matrix also has positive
Jacobi denominator. This supplies the inverse branch in
`sfModularCocycleRealTotal_ne_zero_of_flt_eq_self` and
`tendsto_sfPeriodProduct_div_total_of_lowerLeft_neg`. -/
private theorem fltDenominator_inv_pos_of_flt_eq_self {M : SL(2, ℤ)} {τ : ℝ}
    (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) τ)
    (hfix : flt (M : Mat(2, ℤ)) τ = τ) :
    0 < fltDenominator ((M⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) τ := by
  have hprod := fltDenominator_inv_mul_self_of_flt_eq_self hjac.ne' hfix
  have heq : fltDenominator
      ((M⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) τ =
      1 / fltDenominator (M : Mat(2, ℤ)) τ :=
    (eq_div_iff hjac.ne').mpr hprod
  rw [heq]
  positivity

/-- **The total cocycle does not vanish at an irrational fixed point** with `j_M(τ) > 0` and
`r ∉ ℤ²`: both branches of `sfModularCocycleRealTotal` are nonzero by
`sfModularCocycleReal_ne_zero_of_flt_eq_self`, the second at `M⁻¹`, which fixes `τ`
(`flt_inv_of_flt_eq_self`) with `j_{M⁻¹}(τ) = j_M(τ)⁻¹ > 0`
(`fltDenominator_inv_mul_self_of_flt_eq_self`). -/
theorem sfModularCocycleRealTotal_ne_zero_of_flt_eq_self {r : Fin 2 → ℚ} {M : SL(2, ℤ)}
    (hM : M ∈ gammaSubgroup r) {τ : ℝ}
    (hτ : Irrational τ) (hr : ¬ IsIntegralIndex r)
    (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) τ)
    (hfix : flt (M : Mat(2, ℤ)) τ = τ) :
    sfModularCocycleRealTotal r M hM τ ≠ 0 := by
  by_cases h0 : 0 ≤ M 1 0
  · rw [sfModularCocycleRealTotal_of_nonneg hM h0]
    exact sfModularCocycleReal_ne_zero_of_flt_eq_self hM h0 hτ hr hjac hfix
  · have hneg : M 1 0 < 0 := lt_of_not_ge h0
    rw [sfModularCocycleRealTotal_of_neg_of_flt_eq_self hM hneg hfix]
    apply inv_ne_zero
    have hfix' := flt_inv_of_flt_eq_self hjac.ne' hfix
    have hjac' := fltDenominator_inv_pos_of_flt_eq_self hjac hfix
    exact sfModularCocycleReal_ne_zero_of_flt_eq_self (inv_mem_gammaSubgroup hM)
      (by rw [SL2Z.lowerLeft_inv]; omega) hτ hr hjac' hfix'

/-- For a matrix with negative lower-left entry, the period-product quotient is the inverse of
the quotient for the inverse matrix along the transported approach. This is the negative branch
of `tendsto_sfPeriodProduct_div_total`. -/
private theorem tendsto_sfPeriodProduct_div_total_of_lowerLeft_neg {ι : Type*} {l : Filter ι}
    (tauSeq : ι → ℂ) {τ : ℝ} {r : Fin 2 → ℚ} {M : SL(2, ℤ)}
    (hM : M ∈ gammaSubgroup r) (hr : ¬ IsIntegralIndex r)
    (hτ : Irrational τ) (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) τ)
    (hfix : flt (M : Mat(2, ℤ)) τ = τ) (hneg : M 1 0 < 0)
    (htauT : Tendsto tauSeq l (nhds (τ : ℂ))) (him : ∀ᶠ k in l, 0 < (tauSeq k).im) :
    Tendsto (fun k => sfPeriodProduct r (flt (M : Mat(2, ℤ)) (tauSeq k)) /
        sfPeriodProduct r (tauSeq k)) l
      (nhds (sfModularCocycleRealTotal r M hM τ)) := by
  have hjacC : fltDenominator (M : Mat(2, ℤ)) (τ : ℂ) ≠ 0 := by
    rw [← ofReal_fltDenominator]
    exact_mod_cast hjac.ne'
  have htauT' : Tendsto (fun k => flt (M : Mat(2, ℤ)) (tauSeq k)) l
      (nhds (τ : ℂ)) := by
    convert flt_tendsto (M : Mat(2, ℤ)) htauT hjacC using 1
    rw [← ofReal_flt, hfix]
  have him' : ∀ᶠ k in l,
      0 < (flt (M : Mat(2, ℤ)) (tauSeq k)).im := by
    filter_upwards [him] with k hk
    exact flt_im_pos M hk
  have hfix' := flt_inv_of_flt_eq_self hjac.ne' hfix
  have hjac' := fltDenominator_inv_pos_of_flt_eq_self hjac hfix
  have hlim := tendsto_sfPeriodProduct_div_of_not_isIntegralIndex
    (fun k => flt (M : Mat(2, ℤ)) (tauSeq k))
    (inv_mem_gammaSubgroup hM) hr hτ (by rw [SL2Z.lowerLeft_inv]; omega)
    hjac' htauT' him'
  have hnonzero := sfModularCocycleReal_ne_zero_of_flt_eq_self
    (inv_mem_gammaSubgroup hM) (by rw [SL2Z.lowerLeft_inv]; omega) hτ hr hjac' hfix'
  rw [sfModularCocycleRealTotal_of_neg_of_flt_eq_self hM hneg hfix]
  apply (hlim.inv₀ hnonzero).congr'
  filter_upwards [him] with k hk
  rw [inv_div, flt_inv_flt M _
    (fltDenominator_ne_zero_of_im_ne_zero M hk.ne')]

/-- **The period-product quotient tends to the total real cocycle at an irrational fixed point**:
for `M ∈ Γ_r`, `r ∉ ℤ²`, an irrational `τ` with `M·τ = τ` and `j_M(τ) > 0`, and `τ_k → τ` from
inside `ℍ`,

$$\frac{\varpi_r(M\cdot\tau_k)}{\varpi_r(\tau_k)} \longrightarrow ש^{r}_M(\tau),$$

for either sign of `M₁₀`. For `0 ≤ M₁₀` this is
`tendsto_sfPeriodProduct_div_of_not_isIntegralIndex`. For `M₁₀ < 0` the
total value is `(ש^r_{M⁻¹}(τ))⁻¹` (`sfModularCocycleRealTotal_of_neg_of_flt_eq_self`), and
the quotient is the reciprocal of the quotient for `M⁻¹` along `M·τ_k → τ`
(`flt_inv_flt`, `flt_tendsto`, `flt_im_pos`), which tends to `ש^r_{M⁻¹}(τ) ≠ 0`
(`sfModularCocycleReal_ne_zero_of_flt_eq_self`) by the same theorem at `M⁻¹`, whose
lower-left entry is `-M₁₀ > 0` and whose Jacobi denominator at `τ` is `j_M(τ)⁻¹ > 0`. -/
theorem tendsto_sfPeriodProduct_div_total {ι : Type*} {l : Filter ι}
    (tauSeq : ι → ℂ) {τ : ℝ} {r : Fin 2 → ℚ} {M : SL(2, ℤ)}
    (hM : M ∈ gammaSubgroup r) (hr : ¬ IsIntegralIndex r)
    (hτ : Irrational τ) (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) τ)
    (hfix : flt (M : Mat(2, ℤ)) τ = τ)
    (htauT : Tendsto tauSeq l (nhds (τ : ℂ))) (him : ∀ᶠ k in l, 0 < (tauSeq k).im) :
    Tendsto (fun k => sfPeriodProduct r (flt (M : Mat(2, ℤ)) (tauSeq k)) /
        sfPeriodProduct r (tauSeq k)) l (nhds (sfModularCocycleRealTotal r M hM τ)) := by
  by_cases h0 : 0 ≤ M 1 0
  · rw [sfModularCocycleRealTotal_of_nonneg hM h0]
    exact tendsto_sfPeriodProduct_div_of_not_isIntegralIndex
      tauSeq hM hr hτ h0 hjac htauT him
  · exact tendsto_sfPeriodProduct_div_total_of_lowerLeft_neg tauSeq hM hr hτ hjac hfix
      (lt_of_not_ge h0) htauT him

/-- **The total cocycle at an irrational fixed point is the boundary value of the quotient**: if
the period-product quotient tends to `L` along some approach from `ℍ` (over a nontrivial filter),
then `ש^r_M(τ) = L`. Uniqueness of limits (`tendsto_nhds_unique`) applied to
`tendsto_sfPeriodProduct_div_total`. -/
theorem sfModularCocycleRealTotal_eq_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    (tauSeq : ι → ℂ) {τ : ℝ} {r : Fin 2 → ℚ} {M : SL(2, ℤ)}
    (hM : M ∈ gammaSubgroup r) (hr : ¬ IsIntegralIndex r)
    (hτ : Irrational τ) (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) τ)
    (hfix : flt (M : Mat(2, ℤ)) τ = τ)
    (htauT : Tendsto tauSeq l (nhds (τ : ℂ))) (him : ∀ᶠ k in l, 0 < (tauSeq k).im) {L : ℂ}
    (hL : Tendsto (fun k => sfPeriodProduct r (flt (M : Mat(2, ℤ)) (tauSeq k)) /
        sfPeriodProduct r (tauSeq k)) l (nhds L)) :
    sfModularCocycleRealTotal r M hM τ = L :=
  tendsto_nhds_unique
    (tendsto_sfPeriodProduct_div_total tauSeq hM hr hτ hjac hfix htauT him) hL

/-- Conjugation transports irrationality, nonintegrality, the fixed-point equation, and the
positive Jacobi denominator to `R·β`. This packages the data used together by the conjugation
proofs `sfModularCocycleRealTotal_conj_of_det_one_aux`,
`sfModularCocycleRealTotal_conj_of_det_one`, `sfModularCocycleRealTotal_reflect`, and
`sfModularCocycleRealTotal_conj_of_det_neg_one`. -/
private theorem transported_fixed_point_data {r : Fin 2 → ℚ} {A A' : SL(2, ℤ)}
    {R : Mat(2, ℤ)} (hR : R.det = 1 ∨ R.det = -1)
    (hconj : (A' : Mat(2, ℤ)) * R =
      R * (A : Mat(2, ℤ))) {β : ℝ} (hβ : Irrational β)
    (hr : ¬ IsIntegralIndex r)
    (hfix : flt (A : Mat(2, ℤ)) β = β)
    (hjA : 0 < fltDenominator (A : Mat(2, ℤ)) β) :
    Irrational (flt R β) ∧ ¬ IsIntegralIndex (ratVecAction R r) ∧
      flt (A' : Mat(2, ℤ)) (flt R β) = flt R β ∧
      0 < fltDenominator (A' : Mat(2, ℤ)) (flt R β) := by
  have hdet : R.det ≠ 0 := by rcases hR with hR | hR <;> omega
  have hjR := fltDenominator_ne_zero_of_irrational_of_det hβ hdet
  refine ⟨Irrational.flt_of_det_ne_zero hβ hdet,
    (isIntegralIndex_ratVecAction_iff_of_det hR r).not.mpr hr,
    flt_of_mul_eq_of_flt_eq_self hconj hjR hjA.ne' hfix, ?_⟩
  rw [fltDenominator_of_mul_eq_of_flt_eq_self hconj hjR hjA.ne' hfix]
  exact hjA

/-- The vertical approach remains convergent after applying a real fractional-linear map whose
Jacobi denominator is nonzero. This is used by
`sfModularCocycleRealTotal_conj_of_det_one_aux`. -/
private theorem tendsto_flt_ofReal_add_I_div (M : Mat(2, ℤ)) {β : ℝ}
    (hM : fltDenominator M β ≠ 0) :
    Tendsto (fun k : ℕ => flt M ((β : ℂ) + I * (1 / ((k : ℂ) + 1)))) atTop
      (nhds ((flt M β : ℝ) : ℂ)) := by
  have hMC : fltDenominator M (β : ℂ) ≠ 0 := by
    rw [← ofReal_fltDenominator]
    exact_mod_cast hM
  convert flt_tendsto M (tendsto_ofReal_add_I_div β) hMC using 1
  rw [← ofReal_flt]

/-- If `j_R(β) > 0`, then `j_{R⁻¹}(R·β) > 0`. This supplies the reverse orientation in
`sfModularCocycleRealTotal_conj_of_det_one`. -/
private theorem fltDenominator_inv_flt_pos {R : SL(2, ℤ)} {β : ℝ}
    (hjR : 0 < fltDenominator (R : Mat(2, ℤ)) β) :
    0 < fltDenominator ((R⁻¹ : SL(2, ℤ)) : Mat(2, ℤ))
      (flt (R : Mat(2, ℤ)) β) := by
  have hprod := fltDenominator_inv_flt R β hjR.ne'
  have heq : fltDenominator
      ((R⁻¹ : SL(2, ℤ)) : Mat(2, ℤ))
        (flt (R : Mat(2, ℤ)) β) =
      1 / fltDenominator (R : Mat(2, ℤ)) β :=
    (eq_div_iff hjR.ne').mpr hprod
  rw [heq]
  positivity

/-! ### Kopp's Theorem 4.37, determinant one

The conjugate is an `A' ∈ SL(2, ℤ)` with `A'R = RA`; its membership in `Γ_{Rr}` is
`mem_gammaSubgroup_ratVecAction_of_mul_eq`, and is taken as a hypothesis so that consumers may
supply their own proof. -/

/-- The pointwise upper-half-plane quotient identity used in
`sfModularCocycleRealTotal_conj_of_det_one_aux`. -/
private theorem sfPeriodProduct_conj_quotient_identity {r : Fin 2 → ℚ} {A A' R : SL(2, ℤ)}
    (hconj : A' * R = R * A) (hr : ¬ IsIntegralIndex r) {τ : ℂ} (hτ : 0 < τ.im) :
    sfPeriodProduct (ratVecAction (R : Mat(2, ℤ)) r)
          (flt (A' : Mat(2, ℤ))
            (flt (R : Mat(2, ℤ)) τ)) /
        sfPeriodProduct (ratVecAction (R : Mat(2, ℤ)) r)
          (flt (R : Mat(2, ℤ)) τ) =
      (qPochhammer (fracSymplecticFormRat r (flt (A : Mat(2, ℤ)) τ) /
            fltDenominator (R : Mat(2, ℤ))
              (flt (A : Mat(2, ℤ)) τ))
          (flt (R : Mat(2, ℤ))
            (flt (A : Mat(2, ℤ)) τ)) /
        sfPeriodProduct r (flt (A : Mat(2, ℤ)) τ)) /
      (qPochhammer (fracSymplecticFormRat r τ /
            fltDenominator (R : Mat(2, ℤ)) τ)
          (flt (R : Mat(2, ℤ)) τ) / sfPeriodProduct r τ) *
      (sfPeriodProduct r (flt (A : Mat(2, ℤ)) τ) /
        sfPeriodProduct r τ) := by
  have hR := fltDenominator_ne_zero_of_im_ne_zero R hτ.ne'
  have hA := fltDenominator_ne_zero_of_im_ne_zero A hτ.ne'
  have hflt : flt (A' : Mat(2, ℤ))
      (flt (R : Mat(2, ℤ)) τ) =
      flt (R : Mat(2, ℤ)) (flt (A : Mat(2, ℤ)) τ) := by
    rw [← flt_mul _ _ τ hR]
    rw [← Matrix.SpecialLinearGroup.coe_mul, hconj, Matrix.SpecialLinearGroup.coe_mul,
      flt_mul _ _ τ hA]
  have hpτ : sfPeriodProduct r τ ≠ 0 := by
    apply qPochhammer_ne_zero_of_not_isPeriodLatticePoint hτ
    simpa [flt, fltDenominator] using
      (not_isPeriodLatticePoint_fracSymplecticFormRat_div hr 1 hτ.ne'
        (by simp [fltDenominator]))
  have hpA : sfPeriodProduct r (flt (A : Mat(2, ℤ)) τ) ≠ 0 := by
    apply qPochhammer_ne_zero_of_not_isPeriodLatticePoint (flt_im_pos A hτ)
    simpa [flt, fltDenominator] using
      (not_isPeriodLatticePoint_fracSymplecticFormRat_div hr 1
        (flt_im_pos A hτ).ne' (by simp [fltDenominator]))
  have hqR : qPochhammer (fracSymplecticFormRat r τ /
      fltDenominator (R : Mat(2, ℤ)) τ)
      (flt (R : Mat(2, ℤ)) τ) ≠ 0 :=
    qPochhammer_ne_zero_of_not_isPeriodLatticePoint (flt_im_pos R hτ)
      (not_isPeriodLatticePoint_fracSymplecticFormRat_div hr _ hτ.ne' hR)
  rw [hflt, sfPeriodProduct_ratVecAction_flt R r (flt_im_pos A hτ),
    sfPeriodProduct_ratVecAction_flt R r hτ]
  field_simp

/-- The common boundary value of the two Jacobi quotients in the oriented determinant-one
argument is nonzero. -/
private theorem wordSigmaS_fracSymplecticFormRat_ne_zero {r : Fin 2 → ℚ} {β : ℝ}
    (hβ : Irrational β) (hr : ¬ IsIntegralIndex r) (R : SL(2, ℤ)) (h0 : 0 ≤ R 1 0)
    (hjR : 0 < fltDenominator (R : Mat(2, ℤ)) β) :
    wordSigmaS (fracSymplecticFormRat r β) β R h0 ≠ 0 := by
  apply wordSigmaS_ne_zero hβ _ (sigmaSLatticeFree_fracSymplecticFormRat hβ hr) R h0 hjR
  intro b hb
  exact (sigmaSLatticeFree_fracSymplecticFormRat_div hβ hr _ hjR.ne') 0 b (by simpa using hb)

/-- Along an upper-half-plane approach to `β`, the quotient for `(Rr,A')` along `R·τ`
converges to the cocycle for `(r,A)`. This is the boundary quotient calculation used by
`sfModularCocycleRealTotal_conj_of_det_one_aux`. -/
private theorem tendsto_sfPeriodProduct_conj_quotient {r : Fin 2 → ℚ} {A A' R : SL(2, ℤ)}
    (tauSeq : ℕ → ℂ) (hA : A ∈ gammaSubgroup r)
    (hconj : A' * R = R * A) {β : ℝ} (hβ : Irrational β) (hr : ¬ IsIntegralIndex r)
    (hfix : flt (A : Mat(2, ℤ)) β = β)
    (hjA : 0 < fltDenominator (A : Mat(2, ℤ)) β)
    (hjR : 0 < fltDenominator (R : Mat(2, ℤ)) β) (h0R : 0 ≤ R 1 0)
    (htauT : Tendsto tauSeq atTop (nhds (β : ℂ))) (him : ∀ k, 0 < (tauSeq k).im) :
    Tendsto (fun k =>
      sfPeriodProduct (ratVecAction (R : Mat(2, ℤ)) r)
          (flt (A' : Mat(2, ℤ))
            (flt (R : Mat(2, ℤ)) (tauSeq k))) /
        sfPeriodProduct (ratVecAction (R : Mat(2, ℤ)) r)
          (flt (R : Mat(2, ℤ)) (tauSeq k))) atTop
      (nhds (sfModularCocycleRealTotal r A hA β)) := by
  have hAC : fltDenominator (A : Mat(2, ℤ)) (β : ℂ) ≠ 0 := by
    rw [← ofReal_fltDenominator]
    exact_mod_cast hjA.ne'
  have hAT : Tendsto (fun k => flt (A : Mat(2, ℤ)) (tauSeq k)) atTop
      (nhds (β : ℂ)) := by
    convert flt_tendsto (A : Mat(2, ℤ)) htauT hAC using 1
    rw [← ofReal_flt, hfix]
  have himA : ∀ᶠ k in atTop, 0 < (flt (A : Mat(2, ℤ)) (tauSeq k)).im :=
    Filter.Eventually.of_forall fun k => flt_im_pos A (him k)
  have hJ := tendsto_qPochhammer_div_wordSigmaS tauSeq hr hβ h0R hjR
    htauT (Filter.Eventually.of_forall him)
  have hJA := tendsto_qPochhammer_div_wordSigmaS
    (fun k => flt (A : Mat(2, ℤ)) (tauSeq k)) hr hβ h0R hjR hAT himA
  have hbase := tendsto_sfPeriodProduct_div_total tauSeq hA hr hβ hjA
    hfix htauT (Filter.Eventually.of_forall him)
  have hsigma := wordSigmaS_fracSymplecticFormRat_ne_zero hβ hr R h0R hjR
  have hlim := (hJA.div hJ hsigma).mul hbase
  have hlim' := hlim.congr' (Filter.Eventually.of_forall fun k =>
    (sfPeriodProduct_conj_quotient_identity hconj hr (him k)).symm)
  convert hlim' using 1
  rw [div_self hsigma, one_mul]

/-- The oriented core of the determinant-one case: `R ∈ SL(2, ℤ)` with `0 ≤ R₁₀` and
`j_R(β) > 0`. Along `τ_k = β + i/(k+1)`, the quotient for `(Rr, A')` at `R·τ_k` is
`(J_R(A·τ_k)/J_R(τ_k))·(ϖ_r(A·τ_k)/ϖ_r(τ_k))` by `sfPeriodProduct_ratVecAction_flt` at `τ_k`
and at `A·τ_k` together with `A'·(R·τ_k) = R·(A·τ_k)` (`flt_mul`), where
`J_R(τ) = ϖ(⟨⟨r,τ⟩⟩/j_R(τ), R·τ)/ϖ_r(τ)` and `ϖ_r(τ_k) ≠ 0`
(`qPochhammer_ne_zero_of_not_isPeriodLatticePoint`,
`not_isPeriodLatticePoint_fracSymplecticFormRat_div` at `N = 1`). Both `J_R(τ_k)` and
`J_R(A·τ_k)` tend to `σ_R(⟨⟨r,β⟩⟩, β) ≠ 0`
(`tendsto_qPochhammer_div_wordSigmaS`, `wordSigmaS_ne_zero` with
`sigmaSLatticeFree_fracSymplecticFormRat` and
`sigmaSLatticeFree_fracSymplecticFormRat_div`),
and the last factor to `ש^r_A(β)` (`tendsto_sfPeriodProduct_div_total`), so
`sfModularCocycleRealTotal_eq_of_tendsto` at `(Rr, A', R·β)` along `R·τ_k` concludes. The data at
`R·β`: irrational (`Irrational.flt`), `Rr ∉ ℤ²` (`isIntegralIndex_ratVecAction_iff`),
fixed by `A'` with `j_{A'}(R·β) = j_A(β) > 0` (`flt_of_mul_eq_of_flt_eq_self`,
`fltDenominator_of_mul_eq_of_flt_eq_self`). -/
private theorem sfModularCocycleRealTotal_conj_of_det_one_aux {r : Fin 2 → ℚ} {A A' R : SL(2, ℤ)}
    (hA : A ∈ gammaSubgroup r)
    (hA' : A' ∈
      gammaSubgroup (ratVecAction (R : Mat(2, ℤ)) r))
    (hconj : A' * R = R * A) {β : ℝ} (hβ : Irrational β) (hr : ¬ IsIntegralIndex r)
    (hfix : flt (A : Mat(2, ℤ)) β = β)
    (hjA : 0 < fltDenominator (A : Mat(2, ℤ)) β)
    (hjR : 0 < fltDenominator (R : Mat(2, ℤ)) β) (h0R : 0 ≤ R 1 0) :
    sfModularCocycleRealTotal (ratVecAction (R : Mat(2, ℤ)) r) A' hA'
        (flt (R : Mat(2, ℤ)) β) =
      sfModularCocycleRealTotal r A hA β := by
  let tauSeq : ℕ → ℂ := fun k => (β : ℂ) + I * (1 / ((k : ℂ) + 1))
  have htauT := tendsto_ofReal_add_I_div β
  have him : ∀ k, 0 < (tauSeq k).im := im_ofReal_add_I_div_pos β
  have hquot := tendsto_sfPeriodProduct_conj_quotient tauSeq hA hconj hβ hr hfix hjA hjR
    h0R htauT him
  obtain ⟨hβR, hrR, hfixR, hjAR⟩ := transported_fixed_point_data (Or.inl R.2)
    (congrArg Subtype.val hconj) hβ hr hfix hjA
  apply sfModularCocycleRealTotal_eq_of_tendsto (l := atTop)
    (fun k => flt (R : Mat(2, ℤ)) (tauSeq k)) hA' hrR hβR
  · exact hjAR
  · exact hfixR
  · exact tendsto_flt_ofReal_add_I_div R hjR.ne'
  · exact Filter.Eventually.of_forall fun k => flt_im_pos R (him k)
  · exact hquot

/-- **[72, Kopp (2024), Theorem 4.37, `thm:shinconj`], determinant one, `j_R(β) > 0`**: for
`r ∉ ℤ²`, `A ∈ Γ_r`, an irrational `β` with `A·β = β` and `j_A(β) > 0`, and `R ∈ SL₂(ℤ)` with
`j_R(β) > 0`, the conjugate `A'` (`A'R = RA`) satisfies

$$ש^{R\mathbf r}_{A'}(R\cdot\beta) = ש^{\mathbf r}_A(\beta).$$

The orientation `0 ≤ R₁₀` of `sfModularCocycleRealTotal_conj_of_det_one_aux` is removed by
symmetry: for `R₁₀ < 0` apply it to `R⁻¹` (`SL2Z.lowerLeft_inv`), which carries the pair
`(Rr, A', R·β)` back to `(r, A, β)` (`ratVecAction_mul`, `flt_inv_flt`,
`fltDenominator_inv_flt` for `j_{R⁻¹}(R·β) = j_R(β)⁻¹ > 0`). -/
@[source "72, Theorem 4.37, p. 47, thm:shinconj (determinant one, j_R(β) > 0)"]
theorem sfModularCocycleRealTotal_conj_of_det_one {r : Fin 2 → ℚ} {A A' R : SL(2, ℤ)}
    (hA : A ∈ gammaSubgroup r)
    (hA' : A' ∈
      gammaSubgroup (ratVecAction (R : Mat(2, ℤ)) r))
    (hconj : A' * R = R * A) {β : ℝ} (hβ : Irrational β) (hr : ¬ IsIntegralIndex r)
    (hfix : flt (A : Mat(2, ℤ)) β = β)
    (hjA : 0 < fltDenominator (A : Mat(2, ℤ)) β)
    (hjR : 0 < fltDenominator (R : Mat(2, ℤ)) β) :
    sfModularCocycleRealTotal (ratVecAction (R : Mat(2, ℤ)) r) A' hA'
        (flt (R : Mat(2, ℤ)) β) =
      sfModularCocycleRealTotal r A hA β := by
  by_cases h0 : 0 ≤ R 1 0
  · exact sfModularCocycleRealTotal_conj_of_det_one_aux hA hA' hconj hβ hr hfix hjA hjR h0
  · obtain ⟨hβ', hr', hfix', hjA'⟩ := transported_fixed_point_data (Or.inl R.2)
      (congrArg Subtype.val hconj) hβ hr hfix hjA
    have hjR' := fltDenominator_inv_flt_pos hjR
    have hconj' : A * R⁻¹ = R⁻¹ * A' := by
      calc
        A * R⁻¹ = R⁻¹ * (R * A) * R⁻¹ := by simp
        _ = R⁻¹ * (A' * R) * R⁻¹ := by rw [hconj]
        _ = R⁻¹ * A' := by simp [mul_assoc]
    have hAback : A ∈ gammaSubgroup
        (ratVecAction ((R⁻¹ : SL(2, ℤ)) : Mat(2, ℤ))
          (ratVecAction (R : Mat(2, ℤ)) r)) := by
      rw [ratVecAction_inv_ratVecAction]
      exact hA
    have haux := sfModularCocycleRealTotal_conj_of_det_one_aux hA' hAback hconj' hβ' hr'
      hfix' hjA' hjR' (by rw [SL2Z.lowerLeft_inv]; omega)
    simpa only [ratVecAction_inv_ratVecAction, flt_inv_flt R β hjR.ne'] using haux.symm

/-! ### The conjugate `RAR⁻¹`

Theorem 4.37 read at the conjugate `A' = RAR⁻¹` itself, with the transported fixed-point data, so
that a reduction to a reduced representative need not rebuild the conjugation relation
`A'R = RA`. -/

/-- The conjugation relation `(RAR⁻¹)R = RA` on integer matrices. -/
private theorem coe_mul_mul_inv_mul (A R : SL(2, ℤ)) :
    ((R * A * R⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) * R =
      R * (A : Mat(2, ℤ)) := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul,
    mul_assoc, inv_mul_cancel, mul_one]

/-- `RAR⁻¹ ∈ Γ_{Rr}` for `A ∈ Γ_r` (`mem_gammaSubgroup_ratVecAction_of_mul_eq`). -/
theorem mul_mul_inv_mem_gammaSubgroup_ratVecAction {r : Fin 2 → ℚ} {A : SL(2, ℤ)}
    (hA : A ∈ gammaSubgroup r) (R : SL(2, ℤ)) :
    R * A * R⁻¹ ∈ gammaSubgroup (ratVecAction (R : Mat(2, ℤ)) r) :=
  mem_gammaSubgroup_ratVecAction_of_mul_eq hA (coe_mul_mul_inv_mul A R)

/-- `RAR⁻¹` fixes `R·β` when `A` fixes `β` (`flt_of_mul_eq_of_flt_eq_self`). -/
theorem flt_mul_mul_inv_of_flt_eq_self {A : SL(2, ℤ)} (R : SL(2, ℤ)) {β : ℝ}
    (hjR : fltDenominator (R : Mat(2, ℤ)) β ≠ 0)
    (hjA : fltDenominator (A : Mat(2, ℤ)) β ≠ 0)
    (hfix : flt (A : Mat(2, ℤ)) β = β) :
    flt ((R * A * R⁻¹ : SL(2, ℤ)) : Mat(2, ℤ))
        (flt (R : Mat(2, ℤ)) β) = flt (R : Mat(2, ℤ)) β :=
  flt_of_mul_eq_of_flt_eq_self (coe_mul_mul_inv_mul A R) hjR hjA hfix

/-- `j_{RAR⁻¹}(R·β) = j_A(β)` when `A` fixes `β` (`fltDenominator_of_mul_eq_of_flt_eq_self`,
[72, Kopp (2024), Lemma 4.10, `lem:jeval`]). -/
theorem fltDenominator_mul_mul_inv_of_flt_eq_self {A : SL(2, ℤ)} (R : SL(2, ℤ)) {β : ℝ}
    (hjR : fltDenominator (R : Mat(2, ℤ)) β ≠ 0)
    (hjA : fltDenominator (A : Mat(2, ℤ)) β ≠ 0)
    (hfix : flt (A : Mat(2, ℤ)) β = β) :
    fltDenominator ((R * A * R⁻¹ : SL(2, ℤ)) : Mat(2, ℤ))
        (flt (R : Mat(2, ℤ)) β) =
      fltDenominator (A : Mat(2, ℤ)) β :=
  fltDenominator_of_mul_eq_of_flt_eq_self (coe_mul_mul_inv_mul A R) hjR hjA hfix

/-- **Kopp's Theorem 4.37 at the conjugate `RAR⁻¹`**: `ש^{Rr}_{RAR⁻¹}(R·β) = ש^r_A(β)` for `A ∈ Γ_r`
fixing an irrational `β` with `j_A(β) > 0`, `r ∉ ℤ²`, and `R ∈ SL₂(ℤ)` with `j_R(β) > 0`. This is
`sfModularCocycleRealTotal_conj_of_det_one` at `A' = RAR⁻¹`. -/
theorem sfModularCocycleRealTotal_mul_mul_inv {r : Fin 2 → ℚ} {A : SL(2, ℤ)}
    (hA : A ∈ gammaSubgroup r) (R : SL(2, ℤ)) {β : ℝ}
    (hβ : Irrational β) (hr : ¬ IsIntegralIndex r)
    (hfix : flt (A : Mat(2, ℤ)) β = β)
    (hjA : 0 < fltDenominator (A : Mat(2, ℤ)) β)
    (hjR : 0 < fltDenominator (R : Mat(2, ℤ)) β) :
    sfModularCocycleRealTotal (ratVecAction (R : Mat(2, ℤ)) r) (R * A * R⁻¹)
        (mul_mul_inv_mem_gammaSubgroup_ratVecAction hA R) (flt (R : Mat(2, ℤ)) β) =
      sfModularCocycleRealTotal r A hA β :=
  sfModularCocycleRealTotal_conj_of_det_one hA _ (by simp only [mul_assoc, inv_mul_cancel, mul_one])
    hβ hr hfix hjA hjR

/-! ### Kopp's Theorem 4.37, determinant minus one

The reflection `R₀` first, by complex conjugation on `ℍ`; then a general `R` of determinant `-1`
as `R = (RR₀)R₀` with `RR₀ ∈ SL₂(ℤ)`. -/

/-- Reflecting the vertical approach to `β` gives an upper-half-plane approach to `-β`.
This supplies the approach data for `sfModularCocycleRealTotal_reflect`. -/
private theorem reflected_vertical_approach (β : ℝ) :
    Tendsto (fun k : ℕ => -(starRingEnd ℂ
        ((β : ℂ) + I * (1 / ((k : ℂ) + 1))))) atTop (nhds ((-β : ℝ) : ℂ)) ∧
      ∀ᶠ k : ℕ in atTop,
        0 < (-(starRingEnd ℂ ((β : ℂ) + I * (1 / ((k : ℂ) + 1))))).im := by
  constructor
  · apply (tendsto_ofReal_add_I_div (-β)).congr'
    filter_upwards [] with k
    simp [Complex.ext_iff, Complex.normSq]
  · filter_upwards [] with k
    simpa [Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq] using
      im_ofReal_add_I_div_pos (-β) k

/-- Conjugating the period-product quotient for `(r,A)` gives the quotient for the reflected
pair `(R₀r,A')`. This is the limit identity used by `sfModularCocycleRealTotal_reflect`. -/
private theorem tendsto_reflected_sfPeriodProduct_quotient {r : Fin 2 → ℚ} {A A' : SL(2, ℤ)}
    (hconj : (A' : Mat(2, ℤ)) * reflectionMatrix =
      reflectionMatrix * (A : Mat(2, ℤ))) (tauSeq : ℕ → ℂ)
    (him : ∀ k, 0 < (tauSeq k).im) {L : ℂ}
    (hbase : Tendsto (fun k =>
      sfPeriodProduct r (flt (A : Mat(2, ℤ)) (tauSeq k)) /
        sfPeriodProduct r (tauSeq k)) atTop (nhds L)) :
    Tendsto (fun k =>
      sfPeriodProduct (ratVecAction reflectionMatrix r)
          (flt (A' : Mat(2, ℤ)) (-(starRingEnd ℂ (tauSeq k)))) /
        sfPeriodProduct (ratVecAction reflectionMatrix r) (-(starRingEnd ℂ (tauSeq k))))
      atTop (nhds (starRingEnd ℂ L)) := by
  apply ((Complex.continuous_conj.tendsto _).comp hbase).congr'
  filter_upwards [] with k
  change starRingEnd ℂ
      (sfPeriodProduct r (flt (A : Mat(2, ℤ)) (tauSeq k)) /
        sfPeriodProduct r (tauSeq k)) = _
  rw [map_div₀]
  rw [flt_neg_conj_of_mul_reflectionMatrix_eq hconj (him k),
    ← conj_sfPeriodProduct r (flt_im_pos A (him k)),
    ← conj_sfPeriodProduct r (him k)]

/-- **Kopp's Theorem 4.37 for the reflection `R₀ = diag(-1,1)`**: for `r ∉ ℤ²`, `A ∈ Γ_r`, an
irrational `β` with `A·β = β` and `j_A(β) > 0`, and `A'` with `A'R₀ = R₀A`,

$$ש^{R_0\mathbf r}_{A'}(-\beta) = \overline{ש^{\mathbf r}_A(\beta)}.$$

Along `τ_k = β + i/(k+1)`, the quotient for `(R₀r, A')` at `-conj τ_k` is the complex conjugate
of the quotient for `(r, A)` at `τ_k` (`conj_sfPeriodProduct`, `map_div₀`,
`flt_neg_conj_of_mul_reflectionMatrix_eq`), which tends to `conj ש^r_A(β)`
(`tendsto_sfPeriodProduct_div_total`, `Complex.continuous_conj`); and
`-conj τ_k → -β` inside `ℍ`, so `sfModularCocycleRealTotal_eq_of_tendsto` at `(R₀r, A', -β)`
concludes. The data at `-β`: irrational, `R₀r ∉ ℤ²` (`isIntegralIndex_ratVecAction_iff_of_det`),
`A'·(-β) = -β` with `j_{A'}(-β) = j_A(β) > 0` (the two lemmas `_of_mul_eq_of_flt_eq_self`
with `flt_reflectionMatrix`, `fltDenominator_reflectionMatrix`). -/
theorem sfModularCocycleRealTotal_reflect {r : Fin 2 → ℚ} {A A' : SL(2, ℤ)}
    (hA : A ∈ gammaSubgroup r)
    (hA' : A' ∈ gammaSubgroup (ratVecAction reflectionMatrix r))
    (hconj : (A' : Mat(2, ℤ)) * reflectionMatrix =
      reflectionMatrix * (A : Mat(2, ℤ)))
    {β : ℝ} (hβ : Irrational β) (hr : ¬ IsIntegralIndex r)
    (hfix : flt (A : Mat(2, ℤ)) β = β)
    (hjA : 0 < fltDenominator (A : Mat(2, ℤ)) β) :
    sfModularCocycleRealTotal (ratVecAction reflectionMatrix r) A' hA' (-β) =
      starRingEnd ℂ (sfModularCocycleRealTotal r A hA β) := by
  let tauSeq : ℕ → ℂ := fun k => (β : ℂ) + I * (1 / ((k : ℂ) + 1))
  let refSeq : ℕ → ℂ := fun k => -(starRingEnd ℂ (tauSeq k))
  have htauT := tendsto_ofReal_add_I_div β
  have him : ∀ k, 0 < (tauSeq k).im := im_ofReal_add_I_div_pos β
  obtain ⟨hrefT, hrefim⟩ := reflected_vertical_approach β
  have hbase := tendsto_sfPeriodProduct_div_total tauSeq hA hr hβ hjA
    hfix htauT (Filter.Eventually.of_forall him)
  have hlim := tendsto_reflected_sfPeriodProduct_quotient hconj tauSeq him hbase
  obtain ⟨hβ', hr', hfix', hjA'⟩ := transported_fixed_point_data
    (Or.inr det_reflectionMatrix) hconj hβ hr hfix hjA
  rw [flt_reflectionMatrix] at hβ' hfix' hjA'
  apply sfModularCocycleRealTotal_eq_of_tendsto (l := atTop) refSeq hA'
    hr' hβ' hjA' hfix'
  · simpa only [refSeq, tauSeq] using hrefT
  · simpa only [refSeq, tauSeq] using hrefim
  · simpa only [refSeq] using hlim

/-- For `det R = -1`, the product `RR₀` is the determinant-one factor used by
`sfModularCocycleRealTotal_conj_of_det_neg_one`. -/
private def rightReflectionFactor (R : Mat(2, ℤ)) (hR : R.det = -1) :
    SL(2, ℤ) := by
  refine ⟨R * reflectionMatrix, ?_⟩
  rw [Matrix.det_mul, hR, det_reflectionMatrix]
  norm_num

/-- The reflected conjugate `R₀AR₀` is the determinant-one matrix used by
`sfModularCocycleRealTotal_conj_of_det_neg_one`. -/
private def reflectionConjugate (A : SL(2, ℤ)) : SL(2, ℤ) := by
  refine ⟨reflectionMatrix * (A : Mat(2, ℤ)) * reflectionMatrix, ?_⟩
  rw [Matrix.det_mul, Matrix.det_mul, det_reflectionMatrix, A.2]
  norm_num

/-- The matrix `R₀AR₀` conjugates `A` through `R₀`; this supplies the reflection step in
`sfModularCocycleRealTotal_conj_of_det_neg_one`. -/
private theorem reflectionConjugate_mul_reflectionMatrix (A : SL(2, ℤ)) :
    (reflectionConjugate A : Mat(2, ℤ)) * reflectionMatrix =
      reflectionMatrix * (A : Mat(2, ℤ)) := by
  simp [reflectionConjugate, mul_assoc, reflectionMatrix_mul_self]

/-- Acting by `RR₀` after acting by `R₀` equals acting by `R`; this is the characteristic
identity used by `sfModularCocycleRealTotal_conj_of_det_neg_one`. -/
private theorem ratVecAction_rightReflectionFactor (R : Mat(2, ℤ))
    (hR : R.det = -1) (r : Fin 2 → ℚ) :
    ratVecAction (rightReflectionFactor R hR : Mat(2, ℤ))
        (ratVecAction reflectionMatrix r) = ratVecAction R r := by
  change ratVecAction (R * reflectionMatrix) (ratVecAction reflectionMatrix r) = _
  rw [← ratVecAction_mul, mul_assoc, reflectionMatrix_mul_self, mul_one]

/-- If `A'R = RA`, then `A'(RR₀) = (RR₀)(R₀AR₀)`; this is the determinant-one conjugacy
used by `sfModularCocycleRealTotal_conj_of_det_neg_one`. -/
private theorem mul_rightReflectionFactor_eq {A A' : SL(2, ℤ)}
    {R : Mat(2, ℤ)} (hR : R.det = -1)
    (hconj : (A' : Mat(2, ℤ)) * R =
      R * (A : Mat(2, ℤ))) :
    A' * rightReflectionFactor R hR = rightReflectionFactor R hR * reflectionConjugate A := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  change (A' : Mat(2, ℤ)) * (R * reflectionMatrix) = _
  calc
    (A' : Mat(2, ℤ)) * (R * reflectionMatrix) =
        ((A' : Mat(2, ℤ)) * R) * reflectionMatrix := by rw [mul_assoc]
    _ = (R * (A : Mat(2, ℤ))) * reflectionMatrix := by rw [hconj]
    _ = R * ((A : Mat(2, ℤ)) * reflectionMatrix) := by rw [mul_assoc]
    _ = R * ((reflectionMatrix * reflectionMatrix) *
        ((A : Mat(2, ℤ)) * reflectionMatrix)) := by
      rw [reflectionMatrix_mul_self, one_mul]
    _ = (R * reflectionMatrix) *
        (reflectionMatrix * (A : Mat(2, ℤ)) * reflectionMatrix) := by
      simp only [mul_assoc]

/-- The factor `RR₀` sends `-β` to `R·β`; this is the point identity used by
`sfModularCocycleRealTotal_conj_of_det_neg_one`. -/
private theorem flt_rightReflectionFactor_neg (R : Mat(2, ℤ))
    (hR : R.det = -1) (β : ℝ) :
    flt (rightReflectionFactor R hR : Mat(2, ℤ)) (-β) =
      flt R β := by
  change flt (R * reflectionMatrix) (-β) = flt R β
  rw [flt_mul R reflectionMatrix (-β)
    (by rw [fltDenominator_reflectionMatrix]; exact one_ne_zero),
    flt_reflectionMatrix, neg_neg]

/-- If `j_R(β) > 0`, then the factor `RR₀` has positive denominator at `-β`; this supplies
the oriented determinant-one step in `sfModularCocycleRealTotal_conj_of_det_neg_one`. -/
private theorem fltDenominator_rightReflectionFactor_neg_pos
    (R : Mat(2, ℤ)) (hR : R.det = -1) {β : ℝ}
    (hjR : 0 < fltDenominator R β) :
    0 < fltDenominator (rightReflectionFactor R hR : Mat(2, ℤ)) (-β) := by
  change 0 < fltDenominator (R * reflectionMatrix) (-β)
  rw [fltDenominator_mul R reflectionMatrix (-β)
    (by rw [fltDenominator_reflectionMatrix]; exact one_ne_zero),
    flt_reflectionMatrix, fltDenominator_reflectionMatrix, mul_one, neg_neg]
  exact hjR

/-- The determinant-one cocycle identity for `RR₀` becomes the desired identity at `R·β`
after identifying both the transported characteristic and the transported point. This is the
final transport step in `sfModularCocycleRealTotal_conj_of_det_neg_one`. -/
private theorem sfModularCocycleRealTotal_rightReflectionFactor {r : Fin 2 → ℚ}
    {A' A0 : SL(2, ℤ)} {R : Mat(2, ℤ)} (hR : R.det = -1)
    (hA' : A' ∈ gammaSubgroup (ratVecAction R r))
    (hA'Rp : A' ∈ gammaSubgroup
      (ratVecAction (rightReflectionFactor R hR : Mat(2, ℤ))
        (ratVecAction reflectionMatrix r)))
    (hA0 : A0 ∈
      gammaSubgroup (ratVecAction reflectionMatrix r)) {β : ℝ}
    (hdetone : sfModularCocycleRealTotal
      (ratVecAction (rightReflectionFactor R hR : Mat(2, ℤ))
        (ratVecAction reflectionMatrix r)) A' hA'Rp
          (flt (rightReflectionFactor R hR : Mat(2, ℤ)) (-β)) =
      sfModularCocycleRealTotal (ratVecAction reflectionMatrix r) A0 hA0 (-β)) :
    sfModularCocycleRealTotal (ratVecAction R r) A' hA' (flt R β) =
      sfModularCocycleRealTotal (ratVecAction reflectionMatrix r) A0 hA0 (-β) := by
  have hact := ratVecAction_rightReflectionFactor R hR r
  have hflt := flt_rightReflectionFactor_neg R hR β
  calc
    sfModularCocycleRealTotal (ratVecAction R r) A' hA' (flt R β) =
        sfModularCocycleRealTotal
          (ratVecAction (rightReflectionFactor R hR : Mat(2, ℤ))
            (ratVecAction reflectionMatrix r)) A' hA'Rp (flt R β) :=
      sfModularCocycleRealTotal_congr_index hact.symm hA' hA'Rp _
    _ = sfModularCocycleRealTotal
          (ratVecAction (rightReflectionFactor R hR : Mat(2, ℤ))
            (ratVecAction reflectionMatrix r)) A' hA'Rp
            (flt (rightReflectionFactor R hR : Mat(2, ℤ)) (-β)) := by
      rw [hflt]
    _ = sfModularCocycleRealTotal (ratVecAction reflectionMatrix r) A0 hA0 (-β) := hdetone

/-- **[72, Kopp (2024), Theorem 4.37, `thm:shinconj`], determinant minus one, `j_R(β) > 0`**:
for `r ∉ ℤ²`, `A ∈ Γ_r`, an irrational `β` with `A·β = β` and `j_A(β) > 0`, an integer matrix
`R` with `det R = -1` and `j_R(β) > 0`, and `A'` with `A'R = RA`,

$$ש^{R\mathbf r}_{A'}(R\cdot\beta) = \overline{ש^{\mathbf r}_A(\beta)}.$$

Write `R = R'R₀` with `R' = RR₀ ∈ SL₂(ℤ)` (`reflectionMatrix_mul_self`) and let
`A₀ = R₀AR₀ ∈ SL₂(ℤ)`. Then `sfModularCocycleRealTotal_reflect` gives
`ש^{R₀r}_{A₀}(-β) = conj ש^r_A(β)`, and `sfModularCocycleRealTotal_conj_of_det_one` at
`(R₀r, A₀, A', R')` and the point `-β` gives `ש^{Rr}_{A'}(R·β) = ש^{R₀r}_{A₀}(-β)`, since
`R'(R₀r) = Rr`, `R'·(-β) = R·β` (`flt_mul`, `flt_reflectionMatrix`),
`j_{R'}(-β) = j_R(β)` (`fltDenominator_mul`), and `A'R' = R'A₀`. -/
@[source "72, Theorem 4.37, p. 47, thm:shinconj (determinant minus one, j_R(β) > 0)"]
theorem sfModularCocycleRealTotal_conj_of_det_neg_one {r : Fin 2 → ℚ} {A A' : SL(2, ℤ)}
    {R : Mat(2, ℤ)} (hR : R.det = -1)
    (hA : A ∈ gammaSubgroup r)
    (hA' : A' ∈ gammaSubgroup (ratVecAction R r))
    (hconj : (A' : Mat(2, ℤ)) * R = R * (A : Mat(2, ℤ)))
    {β : ℝ} (hβ : Irrational β) (hr : ¬ IsIntegralIndex r)
    (hfix : flt (A : Mat(2, ℤ)) β = β)
    (hjA : 0 < fltDenominator (A : Mat(2, ℤ)) β)
    (hjR : 0 < fltDenominator R β) :
    sfModularCocycleRealTotal (ratVecAction R r) A' hA' (flt R β) =
      starRingEnd ℂ (sfModularCocycleRealTotal r A hA β) := by
  let Rp := rightReflectionFactor R hR
  let A0 := reflectionConjugate A
  have hconj0 : (A0 : Mat(2, ℤ)) * reflectionMatrix =
      reflectionMatrix * (A : Mat(2, ℤ)) :=
    reflectionConjugate_mul_reflectionMatrix A
  have hA0 : A0 ∈
      gammaSubgroup (ratVecAction reflectionMatrix r) :=
    mem_gammaSubgroup_ratVecAction_of_mul_eq hA hconj0
  have href := sfModularCocycleRealTotal_reflect hA hA0 hconj0 hβ hr hfix hjA
  have hact : ratVecAction (Rp : Mat(2, ℤ))
      (ratVecAction reflectionMatrix r) =
        ratVecAction R r :=
    ratVecAction_rightReflectionFactor R hR r
  have hA'Rp : A' ∈ gammaSubgroup
      (ratVecAction (Rp : Mat(2, ℤ))
        (ratVecAction reflectionMatrix r)) := by simpa only [hact] using hA'
  have hconjRp : A' * Rp = Rp * A0 := mul_rightReflectionFactor_eq hR hconj
  obtain ⟨hβ0, hr0, hfix0, hjA0⟩ := transported_fixed_point_data
    (Or.inr det_reflectionMatrix) hconj0 hβ hr hfix hjA
  rw [flt_reflectionMatrix] at hβ0 hfix0 hjA0
  have hjRp := fltDenominator_rightReflectionFactor_neg_pos R hR hjR
  have hdetone := sfModularCocycleRealTotal_conj_of_det_one hA0 hA'Rp hconjRp
    hβ0 hr0 hfix0 hjA0 hjRp
  calc
    sfModularCocycleRealTotal (ratVecAction R r) A' hA' (flt R β) =
        sfModularCocycleRealTotal (ratVecAction reflectionMatrix r) A0 hA0 (-β) :=
      sfModularCocycleRealTotal_rightReflectionFactor hR hA' hA'Rp hA0 hdetone
    _ = starRingEnd ℂ (sfModularCocycleRealTotal r A hA β) := href

end SIC

end
