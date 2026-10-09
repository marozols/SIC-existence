/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Cocycle.ConductorRelation
import SICs.Cocycle.EtaBoundary
import SICs.SL2Z.RademacherConjugation

/-!
# The conductor relation over the zero class

Over the zero class, the product of the real cocycle values along the nonintegral orbits of
`s` with `Bs ≡ 0` is the eta-multiplier ratio `μ_A/μ_C`. The zero fibre includes one
exceptional integral class, treated at `(0, 1)`.

This module proves the zero-fibre orbit relation of [RW26b, Radchenko, Wheeler (2026b),
Appendix A, proof of Proposition 3] in the cocycle language of [72, Kopp (2024), Theorem 4.46,
`thm:cllr`]. For `B ∈ G_f` with `BC = AB`, an irrational fixed point `α` of `C` with
`j_C(α) > 0` and `j_B(α) > 0`, and representatives `y` of the nonintegral orbits of lengths
`m(y)` over the zero class, it says

$$\prod_{\mathbf y} ש^{\mathbf y}_{C^{m(\mathbf y)}}(\alpha) = \frac{\mu_A}{\mu_C}.$$

Kopp's statement ranges over all classes `r ∈ ℚ²/ℤ²`, but at an integral class the cocycle
depends on the representative (`ש^0_M(α) = μ_M/√ε` while `ש^{(0,1)}_M(α) = μ_M√ε`,
`sfModularCocycleRealTotal_integral_of_flt_eq_self`), so the zero class is handled at the
representative `(0, 1)` and the common factor `√ε` is cancelled. The consumer is the
distribution relation of `SICs.Dilogarithm.Pseudolattice.Distribution` over the zero fibre.

## The argument

Write `B = UR` with `U = [[a,b],[0,d]]`, `a, d > 0`, and `R ∈ SL₂(ℤ)`
(`exists_eq_upperTriangular_mul_of_mem_Gf`), and put `α' = R·α`, `C' = RCR⁻¹`, so that
`UC' = AU`. On the upper half plane the upper-triangular splitting
(`sfPeriodProduct_ratio_upperTriangular`) at the integral characteristic `r = (0, 1)` writes
`ϖ_r(A·(U·τ))/ϖ_r(U·τ)` as the product over `(j, ℓ) ∈ [0,a) × [0,d)` of the quotients
`ϖ_s(C'·τ)/ϖ_s(τ)` at `s = s(j, ℓ)` (`sfUpperTriangularIndex`), whose second coordinate
`(ℓ + 1)/d` is positive. Exactly one factor index `s*` is integral; the others are the
nonzero classes over `0`. The nonintegral factors are grouped into `C'`-orbits and their
limit is taken by `tendsto_prod_sfPeriodProduct_div_orbits`. Along `τ → α'` the left quotient
tends to `ש^r_A(U·α') = μ_A √ε` and the `s*` factor to `μ_{C'} √ε`
(`tendsto_sfPeriodProduct_div_integral`, with `ε = j_A(U·α') = j_{C'}(α')`). Cancelling `√ε`
gives `μ_A/μ_{C'}`. The orbit decomposition moves from the fibre of `B` to the rectangle for
`U` by congruence and the action of `R`. Kopp's conjugation theorem
(`sfModularCocycleRealTotal_mul_mul_inv`) carries each orbit factor back, and
`etaMultiplier_conj` gives `μ_{C'} = μ_C`. The orbit relation is consumed by the
pseudolattice distribution proof.

## Main declaration

- `prod_sfModularCocycleReal'_orbits_preimage_zero`: the zero-class orbit product equals the
  eta-multiplier ratio.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### The zero class for a matrix of positive determinant

The product over the nonzero classes above `0` is the eta-multiplier ratio. -/

/-- The characteristic `(0,1)` is integral; used throughout the zero-class boundary proof. -/
private lemma zeroClass_integral : IsIntegralIndex ![(0 : ℚ), 1] := by
  intro i
  fin_cases i
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

/-- The factor characteristic over the integral representative `(0,1)`. -/
private abbrev zeroClassIndex (a d : ℕ) (b : ℤ) (p : Fin d × Fin a) : Fin 2 → ℚ :=
  sfUpperTriangularIndex ![(0 : ℚ), 1] a d b p.2 p.1

/-- The nonintegral factors in the upper-triangular rectangle over the zero class. -/
private abbrev zeroClassFactors (a d : ℕ) (b : ℤ) : Finset (Fin 2 → ℚ) := by
  classical
  exact (Finset.univ.image (zeroClassIndex a d b)).filter (fun s => ¬ IsIntegralIndex s)

/-- The upper-triangular factor rectangle over `(0,1)` contains exactly one integral
characteristic. This is the zero-class representative in the transversal used below. -/
private theorem unique_integral_upperTriangularIndex {a d : ℕ} (ha : 0 < a) (hd : 0 < d)
    (b : ℤ) : ∃! p : Fin d × Fin a,
      IsIntegralIndex (sfUpperTriangularIndex ![(0 : ℚ), 1] a d b p.2 p.1) := by
  classical
  let r : Fin 2 → ℚ := ![0, 1]
  let U : Mat(2, ℤ) := !![(a : ℤ), b; 0, (d : ℤ)]
  let index : Fin d × Fin a → Fin 2 → ℚ := fun p =>
    sfUpperTriangularIndex r a d b p.2 p.1
  have hT : IsPreimageTransversal U r (Finset.univ.image index) :=
    isPreimageTransversal_upperTriangular r ha hd b
  have hr : IsIntegralIndex r := zeroClass_integral
  have hzero : IsIntegralIndex (ratVecAction U (0 : Fin 2 → ℚ) - r) := by
    simpa [ratVecAction] using (isIntegralIndex_neg_iff r).mpr hr
  obtain ⟨s, hs, hsub⟩ := hT.exists_mem 0 hzero
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hs
  have hp : IsIntegralIndex (index p) :=
    (isIntegralIndex_neg_iff (index p)).mp (by simpa using hsub)
  refine ⟨p, hp, ?_⟩
  intro q hq
  have hval : index p = index q :=
    hT.eq_of_isIntegralIndex_sub _ (Finset.mem_image_of_mem _ (Finset.mem_univ p))
      _ (Finset.mem_image_of_mem _ (Finset.mem_univ q)) (isIntegralIndex_sub hp hq)
  exact (sfUpperTriangularIndex_injective r a d b) hval.symm

/-- Every factor characteristic over `(0,1)` has positive second coordinate, so the
integral-factor boundary theorem applies to the exceptional member of the rectangle. -/
private theorem upperTriangularIndex_zero_second_pos {a d : ℕ} (hd : 0 < d) (b : ℤ)
    (p : Fin d × Fin a) :
    0 < sfUpperTriangularIndex ![(0 : ℚ), 1] a d b p.2 p.1 1 := by
  simp only [sfUpperTriangularIndex, Matrix.cons_val_one, Matrix.cons_val_zero]
  exact div_pos (by positivity) (by exact_mod_cast hd)

open Classical in
/-- The unique integral member splits a product over the upper-triangular
rectangle. Used by `upperTriangular_zero_orbits_total`. -/
private theorem upperTriangular_zero_product_split {a d : ℕ} (b : ℤ)
    (q : (Fin 2 → ℚ) → ℂ) (p₀ : Fin d × Fin a)
    (hp₀ : IsIntegralIndex (sfUpperTriangularIndex ![(0 : ℚ), 1] a d b p₀.2 p₀.1))
    (hp₀_unique : ∀ p : Fin d × Fin a,
      IsIntegralIndex (sfUpperTriangularIndex ![(0 : ℚ), 1] a d b p.2 p.1) → p = p₀) :
    (∏ p : Fin d × Fin a,
      q (sfUpperTriangularIndex ![(0 : ℚ), 1] a d b p.2 p.1)) =
      q (sfUpperTriangularIndex ![(0 : ℚ), 1] a d b p₀.2 p₀.1) *
        ∏ s ∈ (Finset.univ.image fun p : Fin d × Fin a =>
          sfUpperTriangularIndex ![(0 : ℚ), 1] a d b p.2 p.1).filter
            (fun s => ¬ IsIntegralIndex s), q s := by
  classical
  let index : Fin d × Fin a → Fin 2 → ℚ := fun p =>
    sfUpperTriangularIndex ![(0 : ℚ), 1] a d b p.2 p.1
  let T : Finset (Fin 2 → ℚ) := Finset.univ.image index
  have hfilter : T.filter IsIntegralIndex = {index p₀} := by
    ext s
    constructor
    · intro hs
      obtain ⟨hsT, hsi⟩ := Finset.mem_filter.mp hs
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hsT
      exact Finset.mem_singleton.mpr (congrArg index (hp₀_unique p hsi))
    · intro hs
      rw [Finset.mem_singleton] at hs
      subst s
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image_of_mem _ (Finset.mem_univ p₀), hp₀⟩
  change (∏ p : Fin d × Fin a, q (index p)) =
    q (index p₀) * ∏ s ∈ T.filter (fun s => ¬ IsIntegralIndex s), q s
  rw [← Finset.prod_image
    (sfUpperTriangularIndex_injective ![(0 : ℚ), 1] a d b).injOn,
    ← Finset.prod_filter_mul_prod_filter_not T IsIntegralIndex q, hfilter]
  simp only [Finset.prod_singleton]

open Classical in
/-- At an upper-half-plane point, the integral factor separates from the nonintegral
factors of the upper-triangular quotient. -/
private theorem upperTriangular_zero_ratio_split {a d : ℕ} (ha : 0 < a) (hd : 0 < d)
    (b : ℤ) {C D : SL(2, ℤ)}
    (hconj : !![(a : ℤ), b; 0, (d : ℤ)] * (C : Mat(2, ℤ)) =
      (D : Mat(2, ℤ)) * !![(a : ℤ), b; 0, (d : ℤ)])
    (p₀ : Fin d × Fin a)
    (hp₀ : IsIntegralIndex (zeroClassIndex a d b p₀))
    (hp₀_unique : ∀ p : Fin d × Fin a,
      IsIntegralIndex (zeroClassIndex a d b p) → p = p₀)
    {τ : ℂ} (hτ : 0 < τ.im) :
    sfPeriodProduct ![(0 : ℚ), 1]
        (flt (D : Mat(2, ℤ)) (((a : ℂ) * τ + (b : ℂ)) / (d : ℂ))) /
      sfPeriodProduct ![(0 : ℚ), 1] (((a : ℂ) * τ + (b : ℂ)) / (d : ℂ)) =
      (sfPeriodProduct (zeroClassIndex a d b p₀)
        (flt (C : Mat(2, ℤ)) τ) /
        sfPeriodProduct (zeroClassIndex a d b p₀) τ) *
      ∏ s ∈ zeroClassFactors a d b,
        sfPeriodProduct s (flt (C : Mat(2, ℤ)) τ) / sfPeriodProduct s τ := by
  classical
  let r : Fin 2 → ℚ := ![0, 1]
  let index : Fin d × Fin a → Fin 2 → ℚ := fun p =>
    sfUpperTriangularIndex r a d b p.2 p.1
  let q (s : Fin 2 → ℚ) : ℂ :=
    sfPeriodProduct s (flt (C : Mat(2, ℤ)) τ) / sfPeriodProduct s τ
  rw [flt_upperTriangular_semiconj_complex a d hd b C D hconj τ hτ]
  rw [sfPeriodProduct_ratio_upperTriangular r a d ha hd b C τ hτ]
  change (∏ ell : Fin d, ∏ j : Fin a, q (index (ell, j))) = _
  rw [← Fintype.prod_prod_type (fun p : Fin d × Fin a => q (index p))]
  simpa only [zeroClassIndex, zeroClassFactors, q, index] using
    upperTriangular_zero_product_split b q p₀ hp₀ hp₀_unique

open Classical in
/-- The integral factor and the nonintegral orbit product give the total
boundary value of the upper-triangular quotient. Used by
`prod_zero_upperTriangular_orbits`. -/
private theorem upperTriangular_zero_orbits_total {a d : ℕ} (ha : 0 < a) (hd : 0 < d)
    (b : ℤ) {C D : SL(2, ℤ)}
    (hconj : !![(a : ℤ), b; 0, (d : ℤ)] * (C : Mat(2, ℤ)) =
      (D : Mat(2, ℤ)) * !![(a : ℤ), b; 0, (d : ℤ)])
    {α : ℝ} (hα : Irrational α) (hfix : flt (C : Mat(2, ℤ)) α = α)
    (hj : 0 < fltDenominator (C : Mat(2, ℤ)) α)
    (p₀ : Fin d × Fin a)
    (hp₀ : IsIntegralIndex (zeroClassIndex a d b p₀))
    (hp₀_unique : ∀ p : Fin d × Fin a,
      IsIntegralIndex (zeroClassIndex a d b p) → p = p₀)
    {R : Finset (Fin 2 → ℚ)} {m : (Fin 2 → ℚ) → ℕ+}
    (hR : IsOrbitDecomposition C
      (zeroClassFactors a d b) R m)
    (hβ : Irrational (((a : ℝ) * α + b) / d))
    (hfixD : flt (D : Mat(2, ℤ)) (((a : ℝ) * α + b) / d) =
      ((a : ℝ) * α + b) / d)
    (hjD : 0 < fltDenominator (D : Mat(2, ℤ)) (((a : ℝ) * α + b) / d)) :
    sfModularCocycleRealTotal ![(0 : ℚ), 1] D
      (mem_gammaSubgroup_of_integral zeroClass_integral D) (((a : ℝ) * α + b) / d) =
      sfModularCocycleRealTotal
        (zeroClassIndex a d b p₀) C
        (mem_gammaSubgroup_of_integral hp₀ C) α *
        ∏ y ∈ R, sfModularCocycleReal' y (C ^ (m y : ℕ)) α := by
  classical
  let r : Fin 2 → ℚ := ![0, 1]
  let index : Fin d × Fin a → Fin 2 → ℚ := fun p =>
    sfUpperTriangularIndex r a d b p.2 p.1
  let T : Finset (Fin 2 → ℚ) := Finset.univ.image index
  have hD : D ∈ gammaSubgroup r := mem_gammaSubgroup_of_integral zeroClass_integral D
  have hC₀ : C ∈ gammaSubgroup (index p₀) := mem_gammaSubgroup_of_integral hp₀ C
  have hleft := tendsto_sfPeriodProduct_div_integral
    (fun n ↦ ((a : ℂ) * sfUpperApproach α n + (b : ℂ)) / (d : ℂ)) hD
    zeroClass_integral (by simp [r]) hβ hjD hfixD
    (tendsto_sfUpperTriangularApproach a d b α)
    (Filter.Eventually.of_forall (sfUpperTriangularApproach_im_pos a d ha hd b α))
  have hint := tendsto_sfPeriodProduct_div_integral
    (sfUpperApproach α) hC₀ hp₀
    (upperTriangularIndex_zero_second_pos hd b p₀) hα hj hfix
    (tendsto_sfUpperApproach α)
    (Filter.Eventually.of_forall (sfUpperApproach_im_pos α))
  have hnonint : ∀ s ∈ T.filter (fun s => ¬ IsIntegralIndex s), ¬ IsIntegralIndex s := by
    intro s hs
    exact (Finset.mem_filter.mp hs).2
  have hdistinct : ∀ s ∈ T.filter (fun s => ¬ IsIntegralIndex s),
      ∀ s' ∈ T.filter (fun s => ¬ IsIntegralIndex s),
        IsIntegralIndex (s - s') → s = s' := by
    intro s hs s' hs' hsub
    have hT : IsPreimageTransversal !![(a : ℤ), b; 0, (d : ℤ)] r T :=
      isPreimageTransversal_upperTriangular r ha hd b
    exact hT.eq_of_isIntegralIndex_sub s (Finset.mem_filter.mp hs).1
      s' (Finset.mem_filter.mp hs').1 hsub
  have hR' : IsOrbitDecomposition C (T.filter (fun s => ¬ IsIntegralIndex s)) R m := by
    simpa only [zeroClassFactors, zeroClassIndex, T, index, r] using hR
  have horbit := tendsto_prod_sfPeriodProduct_div_orbits (sfUpperApproach α)
    hα hfix hj hnonint hdistinct hR' (tendsto_sfUpperApproach α)
    (Filter.Eventually.of_forall (sfUpperApproach_im_pos α))
  apply tendsto_nhds_unique hleft
  apply (hint.mul horbit).congr'
  filter_upwards with n
  exact (upperTriangular_zero_ratio_split ha hd b hconj p₀ hp₀ hp₀_unique
    (sfUpperApproach_im_pos α n)).symm

/-- At an integral characteristic with positive second coordinate, the real cocycle value
is the eta multiplier times the positive square root of the fixed-point denominator. -/
private theorem integral_total_pos_second {s : Fin 2 → ℚ} {C : SL(2, ℤ)} {α : ℝ}
    (hs : IsIntegralIndex s) (hs1 : 0 < s 1) (hα : Irrational α)
    (hfix : flt (C : Mat(2, ℤ)) α = α)
    (hj : 0 < fltDenominator (C : Mat(2, ℤ)) α) :
    sfModularCocycleRealTotal s C (mem_gammaSubgroup_of_integral hs C) α =
      etaMultiplier C * (Real.sqrt (fltDenominator (C : Mat(2, ℤ)) α) : ℂ) := by
  rw [sfModularCocycleRealTotal_integral_of_flt_eq_self hα hs
    (mem_gammaSubgroup_of_integral hs C) hj hfix, ite_eq_left hs1]
  rfl

open Classical in
/-- The zero-class upper-triangular relation groups the nonintegral factors by
orbits before taking their boundary limit. Used by
`prod_sfModularCocycleReal'_orbits_preimage_zero`. -/
private theorem prod_zero_upperTriangular_orbits {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (b : ℤ)
    {C D : SL(2, ℤ)}
    (hconj : !![(a : ℤ), b; 0, (d : ℤ)] * (C : Mat(2, ℤ)) =
      (D : Mat(2, ℤ)) * !![(a : ℤ), b; 0, (d : ℤ)])
    {α : ℝ} (hα : Irrational α) (hfix : flt (C : Mat(2, ℤ)) α = α)
    (hj : 0 < fltDenominator (C : Mat(2, ℤ)) α)
    {R : Finset (Fin 2 → ℚ)} {m : (Fin 2 → ℚ) → ℕ+}
    (hR : IsOrbitDecomposition C
      ((Finset.univ.image fun p : Fin d × Fin a =>
        sfUpperTriangularIndex ![(0 : ℚ), 1] a d b p.2 p.1).filter
        fun s => ¬ IsIntegralIndex s) R m) :
    ∏ y ∈ R, sfModularCocycleReal' y (C ^ (m y : ℕ)) α =
      etaMultiplier D / etaMultiplier C := by
  classical
  let r : Fin 2 → ℚ := ![0, 1]
  let index : Fin d × Fin a → Fin 2 → ℚ := fun p =>
    sfUpperTriangularIndex r a d b p.2 p.1
  let β : ℝ := ((a : ℝ) * α + b) / d
  let J : ℂ := ((Real.sqrt (fltDenominator (C : Mat(2, ℤ)) α) : ℝ) : ℂ)
  obtain ⟨p₀, hp₀, hp₀_unique⟩ := unique_integral_upperTriangularIndex ha hd b
  have hdZ : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  have hβ : Irrational β := ((hα.natCast_mul ha.ne').add_intCast b).div_natCast hd.ne'
  have hjD : 0 < fltDenominator (D : Mat(2, ℤ)) β := by
    rw [show fltDenominator (D : Mat(2, ℤ)) β =
      fltDenominator (C : Mat(2, ℤ)) α from by
        simpa only [β, Int.cast_natCast] using
          fltDenominator_eq_of_upperTriangular_semiconj hdZ hconj α]
    exact hj
  have hfixD : flt (D : Mat(2, ℤ)) β = β :=
    flt_upperTriangular_eq_self_of_semiconj hdZ hconj hj.ne' hfix
  have hD : D ∈ gammaSubgroup r := mem_gammaSubgroup_of_integral zeroClass_integral D
  have hC₀ : C ∈ gammaSubgroup (index p₀) := mem_gammaSubgroup_of_integral hp₀ C
  have htotal : sfModularCocycleRealTotal r D hD β =
      sfModularCocycleRealTotal (index p₀) C hC₀ α *
        ∏ y ∈ R, sfModularCocycleReal' y (C ^ (m y : ℕ)) α :=
    upperTriangular_zero_orbits_total ha hd b hconj hα hfix hj p₀ hp₀ hp₀_unique
      (by simpa only [zeroClassFactors, zeroClassIndex] using hR) hβ hfixD hjD
  have hJ : J ≠ 0 := by
    change (((Real.sqrt (fltDenominator (C : Mat(2, ℤ)) α) : ℝ) : ℂ) ≠ 0)
    exact_mod_cast (Real.sqrt_pos.mpr hj).ne'
  have hleftVal : sfModularCocycleRealTotal r D hD β = etaMultiplier D * J := by
    rw [integral_total_pos_second zeroClass_integral (by simp) hβ hfixD hjD]
    rw [show fltDenominator (D : Mat(2, ℤ)) β =
      fltDenominator (C : Mat(2, ℤ)) α from by
        simpa only [β, Int.cast_natCast] using
          fltDenominator_eq_of_upperTriangular_semiconj hdZ hconj α]
  have hintVal : sfModularCocycleRealTotal (index p₀) C hC₀ α =
      etaMultiplier C * J :=
    integral_total_pos_second hp₀ (upperTriangularIndex_zero_second_pos hd b p₀)
      hα hfix hj
  have hcancel : etaMultiplier D = etaMultiplier C *
      (∏ y ∈ R, sfModularCocycleReal' y (C ^ (m y : ℕ)) α) := by
    apply mul_right_cancel₀ hJ
    calc
      etaMultiplier D * J = _ := hleftVal.symm.trans htotal
      _ = (etaMultiplier C * _) * J := by rw [hintVal]; ring
  apply (eq_div_iff (etaMultiplier_ne_zero C)).2
  calc
    (∏ y ∈ R, sfModularCocycleReal' y (C ^ (m y : ℕ)) α) * etaMultiplier C =
        etaMultiplier C * _ := mul_comm _ _
    _ = etaMultiplier D := hcancel.symm

open scoped Classical in
/-- **The conductor relation over the zero class, along orbits**: for `B ∈ G_f`, `f > 0`,
`C, A ∈ SL₂(ℤ)` with `BC = AB`, an irrational `α` with `C·α = α`, `j_C(α) > 0` and
`j_B(α) > 0`, a transversal `S` of the classes over `0`, and an orbit decomposition `(R, m)` under
`C` of its classes outside `ℤ²`,

$$\prod_{\mathbf y\in R} ש^{\mathbf y}_{C^{m(\mathbf y)}}(\alpha) = \frac{\mu_A}{\mu_C}.$$

The zero orbit together with the other orbits over zero in [RW26b, Radchenko, Wheeler (2026b),
Appendix A, proof of Proposition 3]. At `m ≡ 1` it specializes to the fixed-class form of
[72, Kopp (2024), Theorem 4.46, `thm:cllr`]. -/
theorem prod_sfModularCocycleReal'_orbits_preimage_zero {f : ℕ} (hf : 0 < f) {B : Mat(2, ℤ)}
    (hB : B ∈ Gf (f : ℤ)) {A C : SL(2, ℤ)}
    (hconj : B * (C : Mat(2, ℤ)) = (A : Mat(2, ℤ)) * B)
    {α : ℝ} (hα : Irrational α) (hfix : flt (C : Mat(2, ℤ)) α = α)
    (hjC : 0 < fltDenominator (C : Mat(2, ℤ)) α) (hjB : 0 < fltDenominator B α)
    {S R : Finset (Fin 2 → ℚ)} {m : (Fin 2 → ℚ) → ℕ+} (hS : IsPreimageTransversal B 0 S)
    (hR : IsOrbitDecomposition C (S.filter fun s => ¬ IsIntegralIndex s) R m) :
    ∏ y ∈ R, sfModularCocycleReal' y (C ^ (m y : ℕ)) α =
      etaMultiplier A / etaMultiplier C := by
  classical
  obtain ⟨a, d, b, Q, had, _, _, hfac⟩ :=
    exists_eq_upperTriangular_mul_of_mem_Gf hf hB
  have hadpos : 0 < a * d := by simpa only [had] using hf
  have ha : 0 < a := Nat.pos_of_mul_pos_right hadpos
  have hd : 0 < d := Nat.pos_of_mul_pos_left hadpos
  let r : Fin 2 → ℚ := ![0, 1]
  let U : Mat(2, ℤ) := !![(a : ℤ), b; 0, (d : ℤ)]
  let C' : SL(2, ℤ) := Q * C * Q⁻¹
  let α' : ℝ := flt (Q : Mat(2, ℤ)) α
  let index : Fin d × Fin a → Fin 2 → ℚ := fun p =>
    sfUpperTriangularIndex r a d b p.2 p.1
  let action : (Fin 2 → ℚ) → Fin 2 → ℚ := ratVecAction (Q : Mat(2, ℤ))
  let invAction : (Fin 2 → ℚ) → Fin 2 → ℚ :=
    ratVecAction ((Q⁻¹ : SL(2, ℤ)) : Mat(2, ℤ))
  let T := Finset.univ.image index
  let S₀ := T.image invAction
  let m' : (Fin 2 → ℚ) → ℕ+ := fun t => m (invAction t)
  have hQden := fltDenominator_ne_zero_of_irrational hα Q
  have hjQ : 0 < fltDenominator (Q : Mat(2, ℤ)) α :=
    fltDenominator_pos_of_upperTriangular_factor a d b Q hd hfac hQden hjB
  have hα' : Irrational α' := Irrational.flt hα Q
  have hfix' : flt (C' : Mat(2, ℤ)) α' = α' :=
    flt_mul_mul_inv_of_flt_eq_self Q hQden hjC.ne' hfix
  have hjC' : 0 < fltDenominator (C' : Mat(2, ℤ)) α' := by
    rw [fltDenominator_mul_mul_inv_of_flt_eq_self Q hQden hjC.ne' hfix]
    exact hjC
  have hconj' : U * (C' : Mat(2, ℤ)) = (A : Mat(2, ℤ)) * U :=
    upperTriangular_semiconj_of_factor a d b Q hfac hconj
  have hT : IsPreimageTransversal U r T :=
    isPreimageTransversal_upperTriangular r ha hd b
  have hT0 : IsPreimageTransversal U 0 T :=
    hT.of_isIntegralIndex_sub (by simpa only [sub_zero] using zeroClass_integral)
  have hS₀ : IsPreimageTransversal B 0 S₀ := by
    rw [hfac]
    exact hT0.image_ratVecAction_inv Q
  have himage : S₀.image action = T := by
    simp only [S₀, T, Finset.image_image, Function.comp_def, action, invAction,
      ratVecAction_ratVecAction_inv]
  have hR₀ : IsOrbitDecomposition C (S₀.filter fun s => ¬ IsIntegralIndex s) R m := by
    obtain ⟨hTS, hST⟩ := hS.congruent_nonintegral hS₀
    exact hR.of_congruent_set hTS hST
  have hfilterimage :
      (S₀.filter fun s => ¬ IsIntegralIndex s).image action =
        T.filter (fun s => ¬ IsIntegralIndex s) := by
    simpa only [action, himage] using nonintegral_image_ratVecAction S₀ Q
  have hR' : IsOrbitDecomposition C' (T.filter fun s => ¬ IsIntegralIndex s)
      (R.image action) m' := by
    simpa only [C', action, invAction, m', hfilterimage] using
      hR₀.image_ratVecAction Q
  have hupper := prod_zero_upperTriangular_orbits ha hd b hconj' hα' hfix' hjC' hR'
  have hactinj : Function.Injective action := by
    intro s t hst
    have h := congrArg invAction hst
    simpa only [action, invAction, ratVecAction_inv_ratVecAction] using h
  have hpoint (y : Fin 2 → ℚ) (hy : y ∈ R) :
      sfModularCocycleReal' (action y) (C' ^ (m' (action y) : ℕ)) α' =
        sfModularCocycleReal' y (C ^ (m y : ℕ)) α := by
    have hmem : C ^ (m y : ℕ) ∈ gammaSubgroup y :=
      mem_gammaSubgroup_of_isIntegralIndex (hR.period y hy)
    have hnon : ¬ IsIntegralIndex y :=
      hR.not_isIntegralIndex_of_mem (fun s hs => (Finset.mem_filter.mp hs).2) hy
    simpa only [action, C', α', m', invAction, ratVecAction_inv_ratVecAction] using
      sfModularCocycleReal'_conj_pow (m y : ℕ) hmem Q hα hnon hfix hjC hjQ
  calc
    (∏ y ∈ R, sfModularCocycleReal' y (C ^ (m y : ℕ)) α) =
        ∏ t ∈ R.image action, sfModularCocycleReal' t (C' ^ (m' t : ℕ)) α' := by
          rw [Finset.prod_image hactinj.injOn]
          exact Finset.prod_congr rfl (fun y hy => (hpoint y hy).symm)
    _ = etaMultiplier A / etaMultiplier C' := hupper
    _ = etaMultiplier A / etaMultiplier C := by rw [etaMultiplier_conj Q C]

end SIC
