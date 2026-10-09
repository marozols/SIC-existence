/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Cocycle.Conjugation
import SICs.Cocycle.HJCycleProduct
import SICs.Quadratic.CycleUnit
import SICs.Quadratic.HJReduction
import SICs.SL2Z.RademacherConjugation

/-!
# Reduction of a Fixed-Point Datum to a Hirzebruch--Jung Cycle

Every hyperbolic `A ∈ SL₂(ℤ)` at a real quadratic fixed point `β` with `j_A(β) > 1` is conjugate,
by a matrix `R` with `j_R(β) > 0`, to a cycle matrix `A_{0,N}` of a purely periodic
Hirzebruch--Jung expansion; through this reduction the eta multiplier is multiplicative on the
powers of `A`, and the real Shintani--Faddeev cocycle at `β` satisfies the conjugation law
`conj(ש^r_A(β)) ש^{-r}_A(β) = 1`.

This module follows [72, Kopp (2024), Proposition 3.17, `prop:reduced`; Proposition 7.7,
`prop:betatogamma`; Proposition 7.20, `prop:almost`; Proposition 7.21, `prop:globalphase`;
Proposition 7.22, `prop:lambdaminus`; Proposition 7.23, `prop:lambdachi`]. It
supplies the two facts about an arbitrary period that the pseudolattice dilogarithm of
`SICs.Dilogarithm.Pseudolattice` needs for [RW26b, Radchenko, Wheeler (2026b), Proposition 2,
equations (7) and (8)] and which the principal layer obtained from the explicit word of `A_d`:
`μ_{γⁿ} = μ_γⁿ` and the argument of the cocycle at the fixed point.

## The argument

*Reduction.* `β = ρ₁(τ)` for `τ ∈ K` real quadratic with `ρ₂(τ) ≠ ρ₁(τ)`. By the eventual
reducedness of the Hirzebruch--Jung expansion (`RealQuadraticFieldData.exists_flt_reduced`) there
is `R ∈ SL₂(ℤ)` with `j_R(β) > 0` carrying `τ` to a reduced `τ' = R·τ`, `0 < ρ₂(τ') < 1 < ρ₁(τ')`;
its real value `β' = R·β` is then purely periodic (`mem_periodicPts_hjRotate`), with cycle matrix
`P = A_{0,ℓ}` at the minimal period `ℓ`. The conjugate `RAR⁻¹` fixes `β'` and `ρ₂(τ')` with
`j(β')j(ρ₂τ') = 1`, so its Jacobi denominators at both roots are positive, and by the stabilizer
theorem `BinaryQF.exists_zpow_eq_of_flt_eq_self_of_sq_eq` (Kopp's Proposition 7.7 for the reduced
pair `β'`, `ρ₂(τ')`) it is `Pᵐ` for some `m ∈ ℤ`; since `j_{RAR⁻¹}(β') = j_A(β) > 1` and
`j_P(β') > 1`, `m ≥ 1`, and `Pᵐ = A_{0,mℓ}` by `hjCycleMatrix_mul_of_hjPeriod_eq` and the
periodicity `hjPeriod_mul_of_hjPeriod_eq`.

*Powers of the eta multiplier.* `Ψ` is a class function (`rademacherInvariant_conj`), and at the
cycle matrix it is the cycle sum `γ(A_{0,N}) = Σ_{n<N}(β_n - 3 + 1/β_n)`
(`hjGamma_eq_rademacherInvariant`), which is additive in `N` along a periodic expansion. So
`Ψ(Aⁿ) = Ψ(P^{mn}) = mn·γ(P) = nΨ(A)`, and `μ_{Aⁿ} = e(Ψ(Aⁿ)/24) = μ_Aⁿ`.

*The conjugation law.* At the cycle matrix, Kopp's Proposition 7.20 gives
`U(±r) ש^{±r}_{A_{0,N}}(β') = e(γ/24 + λ_{±r}/4)`
(`starkTangedalYamamoto_mul_sfModularCocycleReal`). The two phases agree because
`λ_{-r} = λ_r` (`hjLambda_neg`, Kopp's Proposition 7.22), and each has modulus one. Since the
real factors satisfy `U(r)U(-r) = 1` (`starkTangedalYamamoto_mul_neg`), conjugating the identity
at `r` and multiplying by the identity at `-r` gives `conj(ש^r) ש^{-r} = 1`. Kopp's Theorem 4.37
(`sfModularCocycleRealTotal_mul_mul_inv`, at `j_R(β) > 0`) transports both `ש^r_A(β)` and
`ש^{-r}_A(β)` to the cycle matrix, where the law holds.

*Reflection.* The reflection `R₀ = diag(-1, 1)` negates the Rademacher invariant,
`Ψ(R₀AR₀) = -Ψ(A)`, by its Dedekind-sum formula (`b ↦ -b`, `c ↦ -c`), so `μ_{R₀AR₀} = μ_A⁻¹`,
the "`μ_{ΔγΔ} = μ_γ⁻¹` by conjugating the eta transformation law" of
[RW26b, Radchenko, Wheeler (2026b), Appendix B, proof of Proposition 8].
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
variable {F : RealQuadraticFieldData K}

/-! ### Reduction to a cycle matrix

`RAR⁻¹ = A_{0,N}` at the purely periodic `R·β`, for some `R` with `j_R(β) > 0`. -/

/-- A matrix fixing the larger root of a reduced quadratic pair with positive Jacobi denominator
is a power of its minimal cycle matrix; used in `exists_hjCycleMatrix_conj`. -/
private theorem exists_zpow_hjCycleMatrix_of_reduced_pair {x y : ℝ} {t n : ℚ}
    (hx : x ^ 2 = t * x - n) (hy : y ^ 2 = t * y - n)
    (hirr : Irrational x) (hx1 : 1 < x) (hy01 : y ∈ Set.Ioo 0 1)
    {B : SL(2, ℤ)} (hfix : flt (B : Mat(2, ℤ)) x = x)
    (hj : 0 < fltDenominator (B : Mat(2, ℤ)) x) :
    ∃ m : ℤ, B = hjCycleMatrix x (Function.minimalPeriod hjRotate x) ^ m := by
  have hxy : x ≠ y := ne_of_gt (hy01.2.trans hx1)
  have hfix' := flt_eq_self_of_flt_eq_self_of_sq_eq hx hy hxy hirr hfix
  have hj' : 0 < fltDenominator (B : Mat(2, ℤ)) y := by
    nlinarith [fltDenominator_mul_fltDenominator_eq_one_of_sq_eq hx hy hxy hirr hfix]
  exact BinaryQF.exists_zpow_eq_of_flt_eq_self_of_sq_eq
    hx hy hirr hx1 hy01 hfix hfix' hj hj'

/-- A positive power of the minimal cycle matrix is a cycle matrix for a repeated period; used in
`exists_hjCycleMatrix_conj`. -/
private theorem exists_hjCycleMatrix_eq_of_zpow {x : ℝ} (hirr : Irrational x)
    (hx1 : 1 < x) {ℓ : ℕ} (hℓpos : 0 < ℓ) (hℓ : hjPeriod x ℓ = x)
    {B : SL(2, ℤ)} {m : ℤ}
    (hm : B = hjCycleMatrix x ℓ ^ m)
    (hjB : 1 < fltDenominator (B : Mat(2, ℤ)) x) :
    ∃ N : ℕ, 0 < N ∧ hjPeriod x N = x ∧ B = hjCycleMatrix x N := by
  let P := hjCycleMatrix x ℓ
  have hPden : 1 < fltDenominator (P : Mat(2, ℤ)) x :=
    one_lt_fltDenominator_hjCycleMatrix_of_hjPeriod_eq hirr hx1 hℓpos hℓ
  have hmpos : 0 < m := by
    by_contra hn
    have hle := zpow_le_one_of_nonpos₀ hPden.le (le_of_not_gt hn)
    have hPfix : flt (P : Mat(2, ℤ)) x = x :=
      flt_hjCycleMatrix_of_hjPeriod_eq hirr hℓ
    rw [hm, fltDenominator_zpow_of_flt_eq_self (zero_lt_one.trans hPden).ne' hPfix]
      at hjB
    exact (not_le_of_gt hjB) hle
  let k := m.toNat
  have hk : 0 < k := by dsimp [k]; omega
  have hmk : m = (k : ℤ) := by dsimp [k]; omega
  rw [hmk, zpow_natCast] at hm
  refine ⟨ℓ * k, Nat.mul_pos hℓpos hk, hjPeriod_mul_of_hjPeriod_eq hℓ k, ?_⟩
  rw [hjCycleMatrix_mul_of_hjPeriod_eq hℓ]
  exact hm

/-- **A hyperbolic matrix at a real quadratic fixed point is conjugate to a cycle matrix**: for
`τ ∈ K` with `ρ₂(τ) ≠ ρ₁(τ)`, `β = ρ₁(τ)`, and `A ∈ SL₂(ℤ)` with `A·β = β` and `j_A(β) > 1`,
there are `R ∈ SL₂(ℤ)` with `j_R(β) > 0` and `N ≥ 1` such that `β' = R·β > 1` is purely periodic
of period `N` under the Hirzebruch--Jung rotation and `RAR⁻¹ = A_{0,N}(β')` is its cycle matrix.
The reduction is [72, Kopp (2024), Proposition 3.17, `prop:reduced`]
(`RealQuadraticFieldData.exists_flt_reduced`, `mem_periodicPts_hjRotate`) and the identification
of the conjugate is [72, Kopp (2024), Proposition 7.7, `prop:betatogamma`]
(`BinaryQF.exists_zpow_eq_of_flt_eq_self_of_sq_eq` for the reduced pair of roots), the exponent
being fixed by `j_{RAR⁻¹}(β') = j_A(β) > 1`. -/
theorem exists_hjCycleMatrix_conj {τ : K}
    (hτ : realEmbeddingAt K F.otherPlace τ ≠ realEmbeddingAt K F.place τ) {A : SL(2, ℤ)}
    (hfix : flt (A : Mat(2, ℤ)) (realEmbeddingAt K F.place τ) = realEmbeddingAt K F.place τ)
    (hjA : 1 < fltDenominator (A : Mat(2, ℤ)) (realEmbeddingAt K F.place τ)) :
    ∃ (R : SL(2, ℤ)) (N : ℕ), 0 < N ∧
      0 < fltDenominator (R : Mat(2, ℤ)) (realEmbeddingAt K F.place τ) ∧
      1 < flt (R : Mat(2, ℤ)) (realEmbeddingAt K F.place τ) ∧
      hjPeriod (flt (R : Mat(2, ℤ)) (realEmbeddingAt K F.place τ)) N =
        flt (R : Mat(2, ℤ)) (realEmbeddingAt K F.place τ) ∧
      R * A * R⁻¹ = hjCycleMatrix (flt (R : Mat(2, ℤ)) (realEmbeddingAt K F.place τ)) N := by
  let β := realEmbeddingAt K F.place τ
  obtain ⟨R, hRx, hRy, hjR⟩ := F.exists_flt_reduced hτ
  let τ' := flt (R : Mat(2, ℤ)) τ
  let x := flt (R : Mat(2, ℤ)) β
  let y := realEmbeddingAt K F.otherPlace τ'
  have hx1 : 1 < x := by simpa only [x, β, τ', map_flt] using hRx
  have hy01 : y ∈ Set.Ioo 0 1 := hRy
  have hirr : Irrational x := by
    have hne : realEmbeddingAt K F.otherPlace τ' ≠ realEmbeddingAt K F.place τ' :=
      ne_of_lt (hy01.2.trans hRx)
    simpa only [x, β, τ', map_flt] using
      (irrational_realEmbeddingAt_of_ne hne.symm)
  have hperiodic : x ∈ Function.periodicPts hjRotate := by
    simpa only [x, β, τ', map_flt] using F.mem_periodicPts_hjRotate hRx hRy
  let ℓ := Function.minimalPeriod hjRotate x
  have hℓpos : 0 < ℓ := Function.minimalPeriod_pos_of_mem_periodicPts hperiodic
  have hℓ : hjPeriod x ℓ = x := hjPeriod_minimalPeriod x
  let B := R * A * R⁻¹
  have hjA0 : 0 < fltDenominator (A : Mat(2, ℤ)) β :=
    zero_lt_one.trans hjA
  have hBfix : flt (B : Mat(2, ℤ)) x = x :=
    flt_mul_mul_inv_of_flt_eq_self R hjR.ne' hjA0.ne' hfix
  have hBden : 1 < fltDenominator (B : Mat(2, ℤ)) x := by
    rw [fltDenominator_mul_mul_inv_of_flt_eq_self R hjR.ne' hjA0.ne' hfix]
    exact hjA
  have hx := map_sq_eq_trace_mul_sub_norm F.finrank_eq_two
    (realEmbeddingAt K F.place) τ'
  have hy := map_sq_eq_trace_mul_sub_norm F.finrank_eq_two
    (realEmbeddingAt K F.otherPlace) τ'
  have hx' : x ^ 2 = ((Algebra.trace ℚ K τ' : ℚ) : ℝ) * x -
      ((Algebra.norm ℚ τ' : ℚ) : ℝ) := by simpa only [x, β, τ', map_flt] using hx
  have hy' : y ^ 2 = ((Algebra.trace ℚ K τ' : ℚ) : ℝ) * y -
      ((Algebra.norm ℚ τ' : ℚ) : ℝ) := hy
  obtain ⟨m, hm⟩ := exists_zpow_hjCycleMatrix_of_reduced_pair
    hx' hy' hirr hx1 hy01 hBfix (zero_lt_one.trans hBden)
  obtain ⟨N, hNpos, hN, hBN⟩ := exists_hjCycleMatrix_eq_of_zpow
    hirr hx1 hℓpos hℓ hm hBden
  exact ⟨R, N, hNpos, hjR, hx1, hN, hBN⟩

/-! ### Powers of the eta multiplier

`Ψ(Aⁿ) = nΨ(A)` and `μ_{Aⁿ} = μ_Aⁿ` at an attractive real quadratic fixed point. -/

/-- The cycle sum repeats over full periods; used in
`rademacherInvariant_pow_of_flt_eq_self`. -/
private theorem hjGamma_mul_of_hjPeriod_eq {β : ℝ} {N : ℕ}
    (hN : hjPeriod β N = β) (n : ℕ) :
    hjGamma β (N * n) = n * hjGamma β N := by
  have hadd (m : ℕ) (hm : hjPeriod β m = β) :
      hjGamma β (m + N) = hjGamma β m + hjGamma β N := by
    unfold hjGamma
    rw [Finset.sum_range_add]
    simp only [hjPeriod_add_of_hjPeriod_eq hm]
  induction n with
  | zero => simp [hjGamma]
  | succ n ih =>
      rw [Nat.mul_succ, hadd (N * n) (hjPeriod_mul_of_hjPeriod_eq hN n), ih]
      push_cast
      ring

/-- **The Rademacher invariant is additive on the powers of a hyperbolic matrix**:
`Ψ(Aⁿ) = nΨ(A)` for `A·β = β`, `j_A(β) > 1`, `β = ρ₁(τ)` real quadratic. By
`exists_hjCycleMatrix_conj`, `Ψ(Aⁿ) = Ψ(A_{0,N}(β')ⁿ) = Ψ(A_{0,nN}(β'))`
(`rademacherInvariant_conj`, `hjCycleMatrix_add`), which is the cycle sum `γ(A_{0,nN})`
(`hjGamma_eq_rademacherInvariant`), `n` times the cycle sum over one period. The case of
[72, Kopp (2024), Proposition 7.21, `prop:globalphase`] along the repeated word. -/
theorem rademacherInvariant_pow_of_flt_eq_self {τ : K}
    (hτ : realEmbeddingAt K F.otherPlace τ ≠ realEmbeddingAt K F.place τ) {A : SL(2, ℤ)}
    (hfix : flt (A : Mat(2, ℤ)) (realEmbeddingAt K F.place τ) = realEmbeddingAt K F.place τ)
    (hjA : 1 < fltDenominator (A : Mat(2, ℤ)) (realEmbeddingAt K F.place τ)) (n : ℕ) :
    rademacherInvariant (A ^ n) = n * rademacherInvariant A := by
  obtain ⟨R, N, _, _, _, hN, hconj⟩ := exists_hjCycleMatrix_conj hτ hfix hjA
  let β := realEmbeddingAt K F.place τ
  let x := flt (R : Mat(2, ℤ)) β
  have hirr : Irrational x := Irrational.flt (irrational_realEmbeddingAt_of_ne hτ.symm) R
  have hperiod : hjPeriod x (N * n) = x := hjPeriod_mul_of_hjPeriod_eq hN n
  have hgamma : (rademacherInvariant (hjCycleMatrix x (N * n)) : ℝ) =
      (n : ℝ) * (rademacherInvariant (hjCycleMatrix x N) : ℝ) := by
    rw [← hjGamma_eq_rademacherInvariant hirr hperiod,
      ← hjGamma_eq_rademacherInvariant hirr hN,
      hjGamma_mul_of_hjPeriod_eq hN]
  calc
    rademacherInvariant (A ^ n) = rademacherInvariant (R * A ^ n * R⁻¹) :=
      (rademacherInvariant_conj R (A ^ n)).symm
    _ = rademacherInvariant (hjCycleMatrix x (N * n)) := by
      rw [← conj_pow, hconj, hjCycleMatrix_mul_of_hjPeriod_eq hN]
    _ = n * rademacherInvariant (hjCycleMatrix x N) := by exact_mod_cast hgamma
    _ = n * rademacherInvariant A := by rw [← hconj, rademacherInvariant_conj]

/-- **The eta multiplier is multiplicative on the powers of a hyperbolic matrix**:
`μ_{Aⁿ} = μ_Aⁿ`, from `rademacherInvariant_pow_of_flt_eq_self` and `μ = e(Ψ/24)`
(`Complex.exp_nat_mul`); the "`μ_{I,εʳ} = μ_{I,ε}ʳ`" behind
[RW26b, Radchenko, Wheeler (2026b), Proposition 2, equation (8)]. -/
theorem etaMultiplier_pow_of_flt_eq_self {τ : K}
    (hτ : realEmbeddingAt K F.otherPlace τ ≠ realEmbeddingAt K F.place τ) {A : SL(2, ℤ)}
    (hfix : flt (A : Mat(2, ℤ)) (realEmbeddingAt K F.place τ) = realEmbeddingAt K F.place τ)
    (hjA : 1 < fltDenominator (A : Mat(2, ℤ)) (realEmbeddingAt K F.place τ)) (n : ℕ) :
    etaMultiplier (A ^ n) = etaMultiplier A ^ n := by
  unfold etaMultiplier
  rw [rademacherInvariant_pow_of_flt_eq_self hτ hfix hjA]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-! ### The conjugation law at the fixed point

`conj(ש^r_A(β)) ש^{-r}_A(β) = 1`: the modulus of `ש^r_A(β)` is `U(r)⁻¹` and its argument is half
that of the reflected product. -/

/-- The conjugation law at a closed HJ cycle; used in
`sfModularCocycleRealTotal_conj_mul_neg`. -/
private theorem sfModularCocycleReal_conj_mul_neg_hjCycleMatrix {β : ℝ}
    (hβ : Irrational β) (hβ1 : 1 < β) {N : ℕ} (hN : hjPeriod β N = β)
    {r : Fin 2 → ℚ} (hr : ¬ IsIntegralIndex r)
    (hA : (hjCycleMatrix β N : SL(2, ℤ)) ∈ gammaSubgroup r)
    (h0 : 0 ≤ (hjCycleMatrix β N) 1 0) :
    starRingEnd ℂ (sfModularCocycleReal r (hjCycleMatrix β N) hA h0 β) *
      sfModularCocycleReal (-r) (hjCycleMatrix β N)
        (neg_mem_gammaSubgroup hA) h0 β = 1 := by
  let U := starkTangedalYamamoto r β N
  let Uneg := starkTangedalYamamoto (-r) β N
  let phase := Complex.exp (2 * Real.pi * Complex.I *
    ((hjGamma β N / 24 + hjLambda r β N / 4 : ℝ) : ℂ))
  have hpos : (U : ℂ) * sfModularCocycleReal r (hjCycleMatrix β N) hA h0 β = phase :=
    starkTangedalYamamoto_mul_sfModularCocycleReal hβ hβ1 hN hr hA h0
  have hneg : (Uneg : ℂ) * sfModularCocycleReal (-r) (hjCycleMatrix β N)
      (neg_mem_gammaSubgroup hA) h0 β = phase := by
    rw [starkTangedalYamamoto_mul_sfModularCocycleReal hβ hβ1 hN
      ((isIntegralIndex_neg_iff r).not.mpr hr) (neg_mem_gammaSubgroup hA) h0,
      hjLambda_neg hr hβ hA]
  have hunit : (U : ℂ) * (Uneg : ℂ) = 1 := by
    exact_mod_cast starkTangedalYamamoto_mul_neg hβ hβ1 hN hr hA
  have hstar : (U : ℂ) *
      starRingEnd ℂ (sfModularCocycleReal r (hjCycleMatrix β N) hA h0 β) =
        starRingEnd ℂ phase := by
    have h := congrArg (starRingEnd ℂ) hpos
    simpa only [map_mul, Complex.conj_ofReal] using h
  have hphase : starRingEnd ℂ phase * phase = 1 := by
    have hc : starRingEnd ℂ phase = phase⁻¹ := by
      dsimp [phase]
      rw [← Complex.exp_conj, ← Complex.exp_neg]
      simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
      ring_nf
    rw [hc, inv_mul_cancel₀ (Complex.exp_ne_zero _)]
  calc
    _ = ((U : ℂ) * (Uneg : ℂ)) *
        (starRingEnd ℂ (sfModularCocycleReal r (hjCycleMatrix β N) hA h0 β) *
          sfModularCocycleReal (-r) (hjCycleMatrix β N)
            (neg_mem_gammaSubgroup hA) h0 β) := by rw [hunit, one_mul]
    _ = ((U : ℂ) * starRingEnd ℂ (sfModularCocycleReal r
          (hjCycleMatrix β N) hA h0 β)) *
        ((Uneg : ℂ) * sfModularCocycleReal (-r) (hjCycleMatrix β N)
          (neg_mem_gammaSubgroup hA) h0 β) := by ring
    _ = starRingEnd ℂ phase * phase := by rw [hstar, hneg]
    _ = 1 := hphase

/-- **The conjugation law of the real cocycle at an attractive fixed point**:
`conj(ש^r_A(β)) · ש^{-r}_A(β) = 1` for `r ∉ ℤ²`, `A ∈ Γ_r`, `A·β = β`, `j_A(β) > 1`, and
`β = ρ₁(τ)` real quadratic. Transported by `sfModularCocycleRealTotal_mul_mul_inv` along the
reduction `exists_hjCycleMatrix_conj` to a cycle matrix. There
[72, Kopp (2024), Proposition 7.20, `prop:almost`] gives
`U(±r) ש^{±r} = e(γ/24 + λ_{±r}/4)` (`starkTangedalYamamoto_mul_sfModularCocycleReal`).
The phases agree by [72, Kopp (2024), Proposition 7.22, `prop:lambdaminus`] (`hjLambda_neg`),
have modulus one, and `U(r)U(-r) = 1` (`starkTangedalYamamoto_mul_neg`); conjugating the identity
at `r` and multiplying by the identity at `-r` gives the result. This is the unnumbered proposition
`conj(F^±_γ(u)) = 1/F^∓_γ(-u)` before [RW26, Radchenko, Wheeler (2026), Corollary 1,
`cor:argument`], in cocycle form. -/
theorem sfModularCocycleRealTotal_conj_mul_neg {τ : K}
    (hτ : realEmbeddingAt K F.otherPlace τ ≠ realEmbeddingAt K F.place τ) {r : Fin 2 → ℚ}
    {A : SL(2, ℤ)} (hA : A ∈ gammaSubgroup r) (hr : ¬ IsIntegralIndex r)
    (hfix : flt (A : Mat(2, ℤ)) (realEmbeddingAt K F.place τ) = realEmbeddingAt K F.place τ)
    (hjA : 1 < fltDenominator (A : Mat(2, ℤ)) (realEmbeddingAt K F.place τ)) :
    starRingEnd ℂ (sfModularCocycleRealTotal r A hA (realEmbeddingAt K F.place τ)) *
        sfModularCocycleRealTotal (-r) A (neg_mem_gammaSubgroup hA)
          (realEmbeddingAt K F.place τ) = 1 := by
  obtain ⟨R, N, _, hjR, hx1, hN, hconj⟩ := exists_hjCycleMatrix_conj hτ hfix hjA
  let β := realEmbeddingAt K F.place τ
  let x := flt (R : Mat(2, ℤ)) β
  let s := ratVecAction (R : Mat(2, ℤ)) r
  have hirr : Irrational β := irrational_realEmbeddingAt_of_ne hτ.symm
  have hirr' : Irrational x := Irrational.flt hirr R
  have hs : ¬ IsIntegralIndex s := (isIntegralIndex_ratVecAction_iff R).not.mpr hr
  have hB : R * A * R⁻¹ ∈ gammaSubgroup s :=
    mul_mul_inv_mem_gammaSubgroup_ratVecAction hA R
  have hP : (hjCycleMatrix x N : SL(2, ℤ)) ∈ gammaSubgroup s := by
    rw [← hconj]
    exact hB
  have h0 : 0 ≤ (hjCycleMatrix x N) 1 0 := lowerLeft_hjCycleMatrix_nonneg hirr' N
  have hcycle := sfModularCocycleReal_conj_mul_neg_hjCycleMatrix hirr' hx1 hN hs hP h0
  have hpos := sfModularCocycleRealTotal_mul_mul_inv hA R hirr hr hfix
    (zero_lt_one.trans hjA) hjR
  have hneg := sfModularCocycleRealTotal_mul_mul_inv (neg_mem_gammaSubgroup hA) R hirr
    ((isIntegralIndex_neg_iff r).not.mpr hr) hfix (zero_lt_one.trans hjA) hjR
  rw [sfModularCocycleRealTotal_congr_index (ratVecAction_neg _ r) _
    (neg_mem_gammaSubgroup hB)] at hneg
  have hpos' : sfModularCocycleRealTotal s (hjCycleMatrix x N) hP x =
      sfModularCocycleRealTotal r A hA β := by
    simpa only [s, x, hconj] using hpos
  have hneg' : sfModularCocycleRealTotal (-s) (hjCycleMatrix x N)
      (neg_mem_gammaSubgroup hP) x =
        sfModularCocycleRealTotal (-r) A (neg_mem_gammaSubgroup hA) β := by
    simpa only [s, x, hconj] using hneg
  rw [← hpos', ← hneg',
    sfModularCocycleRealTotal_of_nonneg hP h0,
    sfModularCocycleRealTotal_of_nonneg (neg_mem_gammaSubgroup hP) h0]
  exact hcycle


/-! ### The reflection and the eta multiplier

`Ψ(R₀AR₀) = -Ψ(A)` and `μ_{R₀AR₀} = μ_A⁻¹` for the reflection `R₀ = diag(-1, 1)`. -/

/-- **The reflection negates the Rademacher invariant**: `Ψ(A') = -Ψ(A)` when `A'R₀ = R₀A`, i.e.
`A' = R₀AR₀ = (a, -b; -c, d)`, by the formula `rademacherInvariant_of_lowerLeft_ne_zero`
(`dedekindSum_neg_right`) and the `c = 0` branch `b/d ↦ -b/d`. -/
theorem rademacherInvariant_eq_neg_of_mul_reflectionMatrix {A A' : SL(2, ℤ)}
    (h : (A' : Mat(2, ℤ)) * reflectionMatrix = reflectionMatrix * (A : Mat(2, ℤ))) :
    rademacherInvariant A' = -rademacherInvariant A := by
  have h00 : A' 0 0 = A 0 0 := by
    have h' := congrArg (fun M : Mat(2, ℤ) => M 0 0) h
    simpa [reflectionMatrix, Matrix.mul_apply, Fin.sum_univ_two] using h'
  have h01 : A' 0 1 = -A 0 1 := by
    have h' := congrArg (fun M : Mat(2, ℤ) => M 0 1) h
    simpa [reflectionMatrix, Matrix.mul_apply, Fin.sum_univ_two] using h'
  have h10 : A' 1 0 = -A 1 0 := by
    have h' := congrArg (fun M : Mat(2, ℤ) => M 1 0) h
    have h'' : -A' 1 0 = A 1 0 := by
      simpa [reflectionMatrix, Matrix.mul_apply, Fin.sum_univ_two] using h'
    omega
  have h11 : A' 1 1 = A 1 1 := by
    have h' := congrArg (fun M : Mat(2, ℤ) => M 1 1) h
    simpa [reflectionMatrix, Matrix.mul_apply, Fin.sum_univ_two] using h'
  by_cases hc : A 1 0 = 0
  · unfold rademacherInvariant
    simp only [h01, h10, h11, hc, neg_zero, ne_eq, not_true_eq_false, ↓reduceIte,
      Int.cast_neg, neg_div]
  · rw [rademacherInvariant_of_lowerLeft_ne_zero A' (by simpa [h10] using hc),
      rademacherInvariant_of_lowerLeft_ne_zero A hc]
    rw [h00, h10, h11, dedekindSum_neg_right]
    have hsign : -(A 1 0) * (A 0 0 + A 1 1) =
        -(A 1 0 * (A 0 0 + A 1 1)) := by ring
    rw [hsign, Int.sign_neg]
    push_cast
    simp only [Int.sign_neg, Int.cast_neg]
    ring

/-- **The reflection inverts the eta multiplier**: `μ_{A'} = μ_A⁻¹` when `A'R₀ = R₀A`
(`rademacherInvariant_eq_neg_of_mul_reflectionMatrix`, `Complex.exp_neg`); the
"`μ_{ΔγΔ} = μ_γ⁻¹`" of [RW26b, Radchenko, Wheeler (2026b), Appendix B, proof of
Proposition 8]. -/
theorem etaMultiplier_eq_inv_of_mul_reflectionMatrix {A A' : SL(2, ℤ)}
    (h : (A' : Mat(2, ℤ)) * reflectionMatrix = reflectionMatrix * (A : Mat(2, ℤ))) :
    etaMultiplier A' = (etaMultiplier A)⁻¹ := by
  unfold etaMultiplier
  rw [rademacherInvariant_eq_neg_of_mul_reflectionMatrix h]
  simp only [Rat.cast_neg, mul_neg, Complex.exp_neg]

end SIC

end
