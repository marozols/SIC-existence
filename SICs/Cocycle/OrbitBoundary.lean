/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Cocycle.FixedPointCocycle

/-!
# Boundary values of period products along orbits of characteristics

When `C` permutes a finite set of classes of characteristics, the product of the period-product
quotients `ϖ_s(C·τ)/ϖ_s(τ)` over the set tends, at an irrational fixed point `α` of `C`, to the
product over the orbits of `ש^y_{C^m}(α)`, `m` the orbit length.

This module supplies the orbit telescoping of [RW26b, Radchenko, Wheeler (2026b), Appendix A,
proof of Proposition 3] for the distribution relation (10), in the language of the conductor
relation of [72, Kopp (2024), Theorem 4.46, `thm:cllr`], whose fixed-class case it extends. The
source telescopes each orbit with the index shifts and the cocycle formula of `Φ_{γ,u,v}` at the
real point ([RW26, Radchenko, Wheeler (2026), Section 2.2, equations (16),
`eq:faddeevperiod`, and (18), `eq:gamr.cocyc`]); here the
telescoping is an exact identity on the upper half plane, and one boundary limit is taken at the
end.

## The argument

*Characteristics move with the matrix.* With `⟨⟨Mt, M·τ⟩⟩ = ⟨⟨t, τ⟩⟩/j_M(τ)`
(`fracSymplecticFormRat_ratVecAction`), the definitions give, on `ℍ` and for `t ∉ ℤ²`,
`ϖ_{Mt}(M·τ) = σ_M(⟨⟨t, τ⟩⟩, τ) ϖ_t(τ)` with the Jacobi quotient `σ_M = sfJacobiCocycleUHP M`.

*Telescoping an orbit.* Let `t_j = C^j y` (exact rational vectors) for an orbit of length `m`,
so `t_m ≡ t_0`. Then `∏_{j<m} ϖ_{t_j}(C·τ)/ϖ_{t_j}(τ) = ∏_{j<m} σ_C(⟨⟨t_j, τ⟩⟩, τ) ·
ϖ_{t_0}(C·τ)/ϖ_{t_m}(C·τ)`, while iterating the first identity along `τ, C·τ, …` gives
`ϖ_{t_0}(C^m·τ)/ϖ_{t_0}(τ) = ∏_{j<m} σ_C(⟨⟨t_j, C^j·τ⟩⟩, C^j·τ) ·
ϖ_{t_0}(C^m·τ)/ϖ_{t_m}(C^m·τ)`. The two right sides differ only in where the factors are
evaluated. As `τ → α` from `ℍ`, every `C^j·τ` tends to `α`; each `σ_C(⟨⟨t, w⟩⟩, w)` tends to the
same nonzero word value along every approach `w → α` (`tendsto_sfJacobiCocycle_word`, through
`C⁻¹` when `C₁₀ < 0`), and each shift factor `ϖ_{t+e}(w)/ϖ_t(w)`, `e ∈ ℤ²`, is a finite product
with a nonzero limit. So the quotient of the two left sides tends to `1`, and the left side for
`C^m` tends to `ש^{y}_{C^m}(α)` (`tendsto_sfPeriodProduct_div_total`).

*Any set of representatives.* Replacing the members of the set by other representatives of the
same classes changes the product by shift factors evaluated at `C·τ` and at `τ`, whose quotient
tends to `1` by the same continuity.

## Main declarations

- `IsOrbitDecomposition`: finite orbit data for characteristic classes.
- `tendsto_prod_sfPeriodProduct_div_orbits`: the product boundary limit over those orbits.
-/

noncomputable section

open Filter Topology

open scoped MatrixGroups

namespace SIC

/-! ### Orbit decompositions of characteristics

A finite set of representatives `R` of the `C`-orbits of the classes of a finite set `S`. -/

/-- **An orbit decomposition** of the classes of a finite set `S ⊆ ℚ²` modulo `ℤ²` under
`C ∈ SL₂(ℤ)`: for each `y ∈ R`, `C^{m(y)}y ≡ y`, and the iterates `C^j y`, `y ∈ R`, `j < m(y)`,
represent each class of `S` exactly once. It indexes the orbits `y ∈ ℛ_x` with lengths `r_y` of
[RW26b, Radchenko, Wheeler (2026b), Proposition 3(i)] in the characteristic coordinates. -/
structure IsOrbitDecomposition (C : SL(2, ℤ)) (S R : Finset (Fin 2 → ℚ))
    (m : (Fin 2 → ℚ) → ℕ+) : Prop where
  /-- `C^{m(y)}y ≡ y`. -/
  period : ∀ y ∈ R, IsIntegralIndex (ratVecAction ((C ^ (m y : ℕ) : SL(2, ℤ)) : Mat(2, ℤ)) y - y)
  /-- Every member of `S` is congruent to an iterate `C^j y` with `j < m(y)`. -/
  exists_iterate : ∀ s ∈ S, ∃ y ∈ R, ∃ j < (m y : ℕ),
    IsIntegralIndex (s - ratVecAction ((C ^ j : SL(2, ℤ)) : Mat(2, ℤ)) y)
  /-- Every iterate `C^j y` with `j < m(y)` is congruent to a member of `S`. -/
  exists_mem : ∀ y ∈ R, ∀ j < (m y : ℕ), ∃ s ∈ S,
    IsIntegralIndex (s - ratVecAction ((C ^ j : SL(2, ℤ)) : Mat(2, ℤ)) y)
  /-- The iterates are pairwise incongruent. -/
  iterate_injective : ∀ y ∈ R, ∀ y' ∈ R, ∀ j < (m y : ℕ), ∀ j' < (m y' : ℕ),
    IsIntegralIndex (ratVecAction ((C ^ j : SL(2, ℤ)) : Mat(2, ℤ)) y -
      ratVecAction ((C ^ j' : SL(2, ℤ)) : Mat(2, ℤ)) y') → y = y' ∧ j = j'

/-! ### Operations on orbit decompositions

Changes of representatives, changes of basis, and restriction to nonintegral classes preserve
orbit decompositions. -/

/-- An orbit representative is nonintegral when all represented classes are nonintegral. -/
theorem IsOrbitDecomposition.not_isIntegralIndex_of_mem {C : SL(2, ℤ)}
    {S R : Finset (Fin 2 → ℚ)} {m : (Fin 2 → ℚ) → ℕ+}
    (hR : IsOrbitDecomposition C S R m)
    (hS : ∀ s ∈ S, ¬ IsIntegralIndex s) {y : Fin 2 → ℚ} (hy : y ∈ R) :
    ¬ IsIntegralIndex y := by
  obtain ⟨s, hs, hsy⟩ := hR.exists_mem y hy 0 (m y).pos
  have hcongr : IsIntegralIndex (s - y) := by simpa using hsy
  exact mt (isIntegralIndex_iff_of_isIntegralIndex_sub hcongr).mpr (hS s hs)

open scoped Classical in
/-- Filtering out integral classes commutes with an integral unimodular change of basis. -/
theorem nonintegral_image_ratVecAction (S : Finset (Fin 2 → ℚ)) (M : SL(2, ℤ)) :
    (S.filter fun s => ¬ IsIntegralIndex s).image (ratVecAction (M : Mat(2, ℤ))) =
      (S.image (ratVecAction (M : Mat(2, ℤ)))).filter
        (fun s => ¬ IsIntegralIndex s) := by
  classical
  ext t
  constructor
  · intro ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hsS, hsni⟩ := Finset.mem_filter.mp hs
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image_of_mem _ hsS,
        (isIntegralIndex_ratVecAction_iff M).not.mpr hsni⟩
  · intro ht
    obtain ⟨htS, htni⟩ := Finset.mem_filter.mp ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp htS
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr
      ⟨hs, (isIntegralIndex_ratVecAction_iff M).not.mp htni⟩)

/-- Replacing a finite factor set by another set of representatives of the same classes
preserves its orbit decomposition. This transports the decomposition in
`sfModularCocycleRealTotal_eq_prod_orbits_of_mem_Gf` to canonical factors. -/
theorem IsOrbitDecomposition.of_congruent_set {C : SL(2, ℤ)}
    {S T R : Finset (Fin 2 → ℚ)} {m : (Fin 2 → ℚ) → ℕ+}
    (hR : IsOrbitDecomposition C S R m)
    (hTS : ∀ t ∈ T, ∃ s ∈ S, IsIntegralIndex (t - s))
    (hST : ∀ s ∈ S, ∃ t ∈ T, IsIntegralIndex (s - t)) :
    IsOrbitDecomposition C T R m := by
  refine ⟨hR.period, ?_, ?_, hR.iterate_injective⟩
  · intro t ht
    obtain ⟨s, hs, hts⟩ := hTS t ht
    obtain ⟨y, hy, j, hj, hsj⟩ := hR.exists_iterate s hs
    refine ⟨y, hy, j, hj, ?_⟩
    convert isIntegralIndex_add hts hsj using 1
    module
  · intro y hy j hj
    obtain ⟨s, hs, hsj⟩ := hR.exists_mem y hy j hj
    obtain ⟨t, ht, hst⟩ := hST s hs
    refine ⟨t, ht, ?_⟩
    convert isIntegralIndex_sub hsj hst using 1
    module

/-- A unimodular change of coordinates carries an orbit decomposition of characteristic
classes to the conjugate action. This supplies the factor transport in
`sfModularCocycleRealTotal_eq_prod_orbits_of_mem_Gf`. -/
theorem IsOrbitDecomposition.image_ratVecAction {C : SL(2, ℤ)}
    {S R : Finset (Fin 2 → ℚ)} {m : (Fin 2 → ℚ) → ℕ+}
    (hR : IsOrbitDecomposition C S R m) (M : SL(2, ℤ)) :
    IsOrbitDecomposition (M * C * M⁻¹)
      (S.image (ratVecAction (M : Mat(2, ℤ))))
      (R.image (ratVecAction (M : Mat(2, ℤ))))
      (fun t => m (ratVecAction ((M⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) t)) := by
  classical
  have hact (j : ℕ) (t : Fin 2 → ℚ) :
      ratVecAction (((M * C * M⁻¹) ^ j : SL(2, ℤ)) : Mat(2, ℤ))
          (ratVecAction (M : Mat(2, ℤ)) t) =
        ratVecAction (M : Mat(2, ℤ))
          (ratVecAction ((C ^ j : SL(2, ℤ)) : Mat(2, ℤ)) t) := by
    rw [conj_pow]
    simp only [Matrix.SpecialLinearGroup.coe_mul, ratVecAction_mul,
      ratVecAction_inv_ratVecAction]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    simp only [ratVecAction_inv_ratVecAction]
    rw [hact, ← ratVecAction_sub]
    exact isIntegralIndex_ratVecAction _ (hR.period x hx)
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨y, hy, j, hj, htj⟩ := hR.exists_iterate t ht
    refine ⟨ratVecAction (M : Mat(2, ℤ)) y, Finset.mem_image_of_mem _ hy,
      j, ?_, ?_⟩
    · simpa only [ratVecAction_inv_ratVecAction] using hj
    · rw [hact, ← ratVecAction_sub]
      exact isIntegralIndex_ratVecAction _ htj
  · intro y hy j hj
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    simp only [ratVecAction_inv_ratVecAction] at hj
    obtain ⟨s, hs, hsj⟩ := hR.exists_mem x hx j hj
    refine ⟨ratVecAction (M : Mat(2, ℤ)) s, Finset.mem_image_of_mem _ hs, ?_⟩
    rw [hact, ← ratVecAction_sub]
    exact isIntegralIndex_ratVecAction _ hsj
  · intro y hy y' hy' j hj j' hj' hsub
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hy'
    simp only [ratVecAction_inv_ratVecAction] at hj hj'
    rw [hact, hact, ← ratVecAction_sub] at hsub
    obtain ⟨hxx', hjj'⟩ := hR.iterate_injective x hx x' hx' j hj j' hj'
      ((isIntegralIndex_ratVecAction_iff M).mp hsub)
    exact ⟨congrArg _ hxx', hjj'⟩

open scoped Classical in
/-- Restrict an orbit decomposition to its nonintegral characteristic classes. -/
theorem IsOrbitDecomposition.nonintegral {C : SL(2, ℤ)}
    {S R : Finset (Fin 2 → ℚ)} {m : (Fin 2 → ℚ) → ℕ+}
    (hR : IsOrbitDecomposition C S R m) :
    IsOrbitDecomposition C (S.filter fun s => ¬ IsIntegralIndex s)
      (R.filter fun r => ¬ IsIntegralIndex r) m := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy
    exact hR.period y (Finset.mem_filter.mp hy).1
  · intro s hs
    obtain ⟨y, hy, j, hj, hcong⟩ := hR.exists_iterate s (Finset.mem_filter.mp hs).1
    have hnon : ¬ IsIntegralIndex y := by
      intro hint
      have hint' := (isIntegralIndex_ratVecAction_iff (C ^ j)).mpr hint
      exact (Finset.mem_filter.mp hs).2
        ((isIntegralIndex_iff_of_isIntegralIndex_sub hcong).mpr hint')
    exact ⟨y, Finset.mem_filter.mpr ⟨hy, hnon⟩, j, hj, hcong⟩
  · intro y hy j hj
    obtain ⟨s, hs, hcong⟩ := hR.exists_mem y (Finset.mem_filter.mp hy).1 j hj
    have hnon : ¬ IsIntegralIndex s := by
      intro hint
      have hint' := (isIntegralIndex_iff_of_isIntegralIndex_sub hcong).mp hint
      exact (Finset.mem_filter.mp hy).2
        ((isIntegralIndex_ratVecAction_iff (C ^ j)).mp hint')
    exact ⟨s, Finset.mem_filter.mpr ⟨hs, hnon⟩, hcong⟩
  · intro y hy y' hy' j hj j' hj' hcong
    exact hR.iterate_injective y (Finset.mem_filter.mp hy).1
      y' (Finset.mem_filter.mp hy').1 j hj j' hj' hcong

/-! ### The orbit limit

The product of period-product quotients over `S` tends to the product over the orbits. -/

/-- **The period-product quotient moves the characteristic**: on `ℍ`, for `t ∉ ℤ²` and
`M ∈ SL₂(ℤ)`, `ϖ_{Mt}(M·τ) = σ_M(⟨⟨t, τ⟩⟩, τ) ϖ_t(τ)`. The coboundary identity [AFK25,
equation (1.27), `eq:coboundary`] without the condition `M ∈ Γ_t`; used by
`tendsto_prod_sfPeriodProduct_div_orbits`. -/
private theorem sfPeriodProduct_ratVecAction_flt_eq_mul {t : Fin 2 → ℚ}
    (ht : ¬ IsIntegralIndex t)
    (M : SL(2, ℤ)) {τ : ℂ} (hτ : 0 < τ.im) :
    sfPeriodProduct (ratVecAction (M : Mat(2, ℤ)) t) (flt (M : Mat(2, ℤ)) τ) =
      sfJacobiCocycleUHP (M : Mat(2, ℤ)) (fracSymplecticFormRat t τ) τ * sfPeriodProduct t τ := by
  rw [sfPeriodProduct_ratVecAction_flt M t hτ,
    sfJacobiCocycleUHP_eq_quotient _ _ _ (sfPeriodProduct_ne_zero ht hτ)]
  exact (div_mul_cancel₀ _ (sfPeriodProduct_ne_zero ht hτ)).symm

/-- The finite factor for a characteristic shift is nonzero at an irrational boundary point;
used by `tendsto_sfPeriodProduct_shift_div` and the orbit limit. -/
private theorem qPochhammerFin_shift_ne_zero {α : ℝ} (hα : Irrational α)
    {r : Fin 2 → ℚ} (hr : ¬ IsIntegralIndex r) (n : ℤ) :
    qPochhammerFin n ((fracSymplecticFormRat r α : ℝ) : ℂ) (α : ℂ) ≠ 0 := by
  have hlat := sigmaSLatticeFree_fracSymplecticFormRat hα hr
  apply qPochhammerFin_ne_zero_of_forall_ne_int n
    (fracSymplecticFormRat r α) α
  intro k _ m heq
  apply hlat (-k) m
  push_cast at heq ⊢
  linear_combination heq

/-- The finite shift factor of `ϖ_{r+e}/ϖ_r` has the same nonzero boundary value along every
upper-half-plane approach; used by `tendsto_prod_sfPeriodProduct_div_orbits`. -/
private theorem tendsto_sfPeriodProduct_shift_div {ι : Type*} {l : Filter ι}
    (tauSeq : ι → ℂ) {α : ℝ} (hα : Irrational α) {r : Fin 2 → ℚ}
    (hr : ¬ IsIntegralIndex r) (e : Fin 2 → ℤ)
    (htau : Tendsto tauSeq l (𝓝 (α : ℂ)))
    (him : ∀ᶠ k in l, 0 < (tauSeq k).im) :
    Tendsto (fun k => sfPeriodProduct (r + fun i => (e i : ℚ)) (tauSeq k) /
      sfPeriodProduct r (tauSeq k)) l
      (𝓝 (qPochhammerFin (e 1) ((fracSymplecticFormRat r α : ℝ) : ℂ) (α : ℂ))⁻¹) := by
  have hfin := qPochhammerFin_shift_ne_zero hα hr (e 1)
  have hfinT : Tendsto (fun k => qPochhammerFin (e 1)
      (fracSymplecticFormRat r (tauSeq k)) (tauSeq k)) l
      (𝓝 (qPochhammerFin (e 1) ((fracSymplecticFormRat r α : ℝ) : ℂ) (α : ℂ))) := by
    convert (continuousAt_qPochhammerFin (e 1) hfin).tendsto.comp
      ((fracSymplecticFormRat_tendsto r htau).prodMk_nhds htau) using 1
    rfl
  apply (hfinT.inv₀ hfin).congr'
  filter_upwards [him, hfinT.eventually_ne hfin] with k hk hkfin
  have harg : fracSymplecticFormRat (r + fun i => (e i : ℚ)) (tauSeq k) =
      fracSymplecticFormRat r (tauSeq k) + (e 1 : ℂ) * tauSeq k + (-e 0 : ℤ) := by
    simp only [fracSymplecticFormRat, Pi.add_apply]
    push_cast
    ring
  rw [sfPeriodProduct, sfPeriodProduct, harg,
    qPochhammer_add_intCast_mul_add_intCast _ _ hk (e 1) (-e 0) hkfin]
  exact (mul_div_cancel_right₀ _ (sfPeriodProduct_ne_zero hr hk)).symm

/-- The word boundary value of the Jacobi quotient for a moving characteristic; used by
`tendsto_sfJacobiCocycle_char` and the orbit telescoping. -/
private def sfJacobiCocycleCharBoundary (C : SL(2, ℤ)) (t : Fin 2 → ℚ) (α : ℝ) : ℂ :=
  if h0 : 0 ≤ C 1 0 then wordSigmaS (fracSymplecticFormRat t α) α C h0
  else (wordSigmaS (fracSymplecticFormRat (ratVecAction (C : Mat(2, ℤ)) t) α)
    α C⁻¹ (by rw [SL2Z.lowerLeft_inv]; omega))⁻¹

/-- The Jacobi quotient for `C` is the inverse quotient for `C⁻¹` at the moved
characteristic and modulus. -/
private theorem sfJacobiCocycle_char_inv {t : Fin 2 → ℚ}
    (ht : ¬ IsIntegralIndex t) (C : SL(2, ℤ)) {τ : ℂ} (hτ : 0 < τ.im) :
    sfJacobiCocycleUHP (C : Mat(2, ℤ)) (fracSymplecticFormRat t τ) τ =
      (sfJacobiCocycleUHP ((C⁻¹ : SL(2, ℤ)) : Mat(2, ℤ))
        (fracSymplecticFormRat (ratVecAction (C : Mat(2, ℤ)) t)
          (flt (C : Mat(2, ℤ)) τ)) (flt (C : Mat(2, ℤ)) τ))⁻¹ := by
  let tAct := ratVecAction (C : Mat(2, ℤ)) t
  have htAct : ¬ IsIntegralIndex tAct := by
    simpa only [tAct] using mt (isIntegralIndex_ratVecAction_iff C).mp ht
  have hden := fltDenominator_ne_zero_of_im_ne_zero C hτ.ne'
  have harg : fracSymplecticFormRat tAct (flt (C : Mat(2, ℤ)) τ) =
      fracSymplecticFormRat t τ /
        fltDenominator (C : Mat(2, ℤ)) τ := by
    dsimp only [tAct]
    rw [fracSymplecticFormRat_ratVecAction _ _ _ hden, C.2]
    simp
  rw [harg]
  have hnum : qPochhammer
      (fracSymplecticFormRat t τ /
        fltDenominator (C : Mat(2, ℤ)) τ)
      (flt (C : Mat(2, ℤ)) τ) ≠ 0 := by
    rw [← sfPeriodProduct_ratVecAction_flt C t hτ]
    exact sfPeriodProduct_ne_zero htAct (flt_im_pos C hτ)
  have hdenProd : qPochhammer (fracSymplecticFormRat t τ)
      τ ≠ 0 := sfPeriodProduct_ne_zero ht hτ
  exact (eq_inv_of_mul_eq_one_right
    (sfJacobiCocycle_inv_mul_self C _ _ hden hnum hdenProd))

/-- Every power of a matrix fixing `α` carries an upper-half-plane approach to `α`. -/
private theorem tendsto_flt_pow_fixed {ι : Type*} {l : Filter ι}
    (w : ι → ℂ) {α : ℝ} {C : SL(2, ℤ)}
    (hfix : flt (C : Mat(2, ℤ)) α = α)
    (hj : 0 < fltDenominator (C : Mat(2, ℤ)) α)
    (hw : Tendsto w l (𝓝 (α : ℂ))) (j : ℕ) :
    Tendsto (fun k => flt ((C ^ j : SL(2, ℤ)) : Mat(2, ℤ)) (w k)) l
      (𝓝 (α : ℂ)) := by
  have hdenj : fltDenominator ((C ^ j : SL(2, ℤ)) : Mat(2, ℤ)) α ≠ 0 := by
    rw [fltDenominator_pow_of_flt_eq_self hj.ne' hfix]
    exact pow_ne_zero _ hj.ne'
  convert flt_tendsto ((C ^ j : SL(2, ℤ)) : Mat(2, ℤ)) hw (by
    exact_mod_cast hdenj) using 1
  rw [← ofReal_flt, flt_pow_of_flt_eq_self hj.ne' hfix]

/-- For negative lower-left entry, the Jacobi quotient is the inverse quotient for
`C⁻¹` along the transported approach. This is the inverse-orientation boundary step. -/
private theorem tendsto_sfJacobiCocycle_char_neg {ι : Type*} {l : Filter ι}
    (tauSeq : ι → ℂ) {α : ℝ} (hα : Irrational α) {t : Fin 2 → ℚ}
    (ht : ¬ IsIntegralIndex t) {C : SL(2, ℤ)}
    (hfix : flt (C : Mat(2, ℤ)) α = α)
    (hj : 0 < fltDenominator (C : Mat(2, ℤ)) α)
    (htau : Tendsto tauSeq l (𝓝 (α : ℂ)))
    (him : ∀ᶠ k in l, 0 < (tauSeq k).im) (h0 : ¬ 0 ≤ C 1 0) :
    Tendsto (fun k => sfJacobiCocycleUHP (C : Mat(2, ℤ))
      (fracSymplecticFormRat t (tauSeq k)) (tauSeq k)) l
      (𝓝 (sfJacobiCocycleCharBoundary C t α)) := by
  let t' := ratVecAction (C : Mat(2, ℤ)) t
  have ht' : ¬ IsIntegralIndex t' := by
    simpa only [t'] using mt (isIntegralIndex_ratVecAction_iff C).mp ht
  have hjInv : 0 < fltDenominator ((C⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) α := by
    have hprod := fltDenominator_inv_mul_self_of_flt_eq_self hj.ne' hfix
    have hval : fltDenominator ((C⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) α =
        (fltDenominator (C : Mat(2, ℤ)) α)⁻¹ :=
      eq_inv_of_mul_eq_one_left hprod
    rw [hval]
    exact inv_pos.mpr hj
  have h0Inv : 0 ≤ (C⁻¹ : SL(2, ℤ)) 1 0 := by
    rw [SL2Z.lowerLeft_inv]
    omega
  have htau' : Tendsto (fun k => flt (C : Mat(2, ℤ)) (tauSeq k)) l
      (𝓝 (α : ℂ)) := by
    simpa only [pow_one] using tendsto_flt_pow_fixed tauSeq hfix hj htau 1
  have him' : ∀ᶠ k in l, 0 < (flt (C : Mat(2, ℤ)) (tauSeq k)).im :=
    him.mono fun _ hk => flt_im_pos C hk
  have hlim := tendsto_qPochhammer_div_wordSigmaS
    (fun k => flt (C : Mat(2, ℤ)) (tauSeq k)) ht' hα h0Inv hjInv htau' him'
  have hword : wordSigmaS (fracSymplecticFormRat t' α) α C⁻¹ h0Inv ≠ 0 := by
    apply wordSigmaS_ne_zero hα _ (sigmaSLatticeFree_fracSymplecticFormRat hα ht')
      C⁻¹ h0Inv hjInv
    intro b hb
    exact (sigmaSLatticeFree_fracSymplecticFormRat_div hα ht' _ hjInv.ne') 0 b
      (by simpa using hb)
  have hlimInv : Tendsto (fun k => sfJacobiCocycleUHP
      ((C⁻¹ : SL(2, ℤ)) : Mat(2, ℤ))
      (fracSymplecticFormRat t' (flt (C : Mat(2, ℤ)) (tauSeq k)))
      (flt (C : Mat(2, ℤ)) (tauSeq k))) l
      (𝓝 (wordSigmaS (fracSymplecticFormRat t' α) α C⁻¹ h0Inv)) := by
    apply hlim.congr'
    filter_upwards [him] with k hk
    exact (sfJacobiCocycleUHP_eq_quotient _ _ _
      (sfPeriodProduct_ne_zero ht' (flt_im_pos C hk))).symm
  simp only [sfJacobiCocycleCharBoundary, dite_eq_right h0]
  change Tendsto _ _ (𝓝 (wordSigmaS (fracSymplecticFormRat t' α)
    α C⁻¹ h0Inv)⁻¹)
  apply (hlimInv.inv₀ hword).congr'
  filter_upwards [him] with k hk
  exact (sfJacobiCocycle_char_inv ht C hk).symm

/-- The Jacobi quotient for a nonintegral characteristic has one word boundary value along
every approach to a positive fixed point; used by the orbit telescoping. -/
private theorem tendsto_sfJacobiCocycle_char {ι : Type*} {l : Filter ι}
    (tauSeq : ι → ℂ) {α : ℝ} (hα : Irrational α) {t : Fin 2 → ℚ}
    (ht : ¬ IsIntegralIndex t) {C : SL(2, ℤ)}
    (hfix : flt (C : Mat(2, ℤ)) α = α)
    (hj : 0 < fltDenominator (C : Mat(2, ℤ)) α)
    (htau : Tendsto tauSeq l (𝓝 (α : ℂ)))
    (him : ∀ᶠ k in l, 0 < (tauSeq k).im) :
    Tendsto (fun k => sfJacobiCocycleUHP (C : Mat(2, ℤ))
      (fracSymplecticFormRat t (tauSeq k)) (tauSeq k)) l
      (𝓝 (sfJacobiCocycleCharBoundary C t α)) := by
  by_cases h0 : 0 ≤ C 1 0
  · simp only [sfJacobiCocycleCharBoundary, dite_eq_left h0]
    have hlim := tendsto_qPochhammer_div_wordSigmaS tauSeq ht hα h0 hj htau him
    apply hlim.congr'
    filter_upwards [him] with k hk
    exact (sfJacobiCocycleUHP_eq_quotient (C : Mat(2, ℤ)) _ _
      (sfPeriodProduct_ne_zero ht hk)).symm
  · exact tendsto_sfJacobiCocycle_char_neg tauSeq hα ht hfix hj htau him h0

/-- A finite product of quotients agrees with the product using the next numerator, after
accounting for the two endpoint factors; used by the orbit telescoping. -/
private theorem prod_range_div_shift (f g : ℕ → ℂ) (n : ℕ)
    (hf : f n ≠ 0) (hg : ∀ j ∈ Finset.range n, g j ≠ 0) :
    (∏ j ∈ Finset.range n, f j / g j) =
      (∏ j ∈ Finset.range n, f (j + 1) / g j) * f 0 / f n := by
  have hgprod : (∏ j ∈ Finset.range n, g j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hg
  have hshift : (∏ j ∈ Finset.range n, f (j + 1)) * f 0 =
      (∏ j ∈ Finset.range n, f j) * f n := by
    calc
      _ = ∏ j ∈ Finset.range (n + 1), f j := (Finset.prod_range_succ' f n).symm
      _ = _ := Finset.prod_range_succ f n
  rw [Finset.prod_div_distrib, Finset.prod_div_distrib]
  field_simp [hf, hgprod]
  exact hshift.symm

/-- The exact characteristic at the `j`th step of an orbit, used by the two orbit products. -/
private def orbitIndex (C : SL(2, ℤ)) (y : Fin 2 → ℚ) (j : ℕ) : Fin 2 → ℚ :=
  ratVecAction ((C ^ j : SL(2, ℤ)) : Mat(2, ℤ)) y

/-- Advancing the orbit index is the rational-vector action of `C`; used by the moving
coboundary identity along an orbit. -/
private theorem orbitIndex_succ (C : SL(2, ℤ)) (y : Fin 2 → ℚ) (j : ℕ) :
    orbitIndex C y (j + 1) = ratVecAction (C : Mat(2, ℤ)) (orbitIndex C y j) := by
  simp only [orbitIndex, pow_succ', Matrix.SpecialLinearGroup.coe_mul, ratVecAction_mul]

/-- Every exact iterate of a nonintegral characteristic remains nonintegral; used by the orbit
limit. -/
private theorem orbitIndex_ne_integral (C : SL(2, ℤ)) {y : Fin 2 → ℚ}
    (hy : ¬ IsIntegralIndex y) (j : ℕ) : ¬ IsIntegralIndex (orbitIndex C y j) := by
  exact mt (isIntegralIndex_ratVecAction_iff (C ^ j)).mp hy

/-- Advancing the modulus along the orbit is one fractional-linear action of `C`; used by
the telescoped coboundary identity. -/
private theorem flt_pow_succ (C : SL(2, ℤ)) (j : ℕ) {τ : ℂ} (hτ : 0 < τ.im) :
    flt ((C ^ (j + 1) : SL(2, ℤ)) : Mat(2, ℤ)) τ =
      flt (C : Mat(2, ℤ)) (flt ((C ^ j : SL(2, ℤ)) : Mat(2, ℤ)) τ) := by
  rw [pow_succ', Matrix.SpecialLinearGroup.coe_mul]
  exact flt_mul _ _ _ (fltDenominator_ne_zero_of_im_ne_zero (C ^ j) hτ.ne')

/-- The product over exact orbit characteristics is the product of their Jacobi quotients
times the endpoint characteristic shift; used by `tendsto_sfPeriodProduct_orbit`. -/
private theorem prod_orbit_ratio_eq (C : SL(2, ℤ)) {y : Fin 2 → ℚ}
    (hy : ¬ IsIntegralIndex y) (n : ℕ) {τ : ℂ} (hτ : 0 < τ.im) :
    (∏ j ∈ Finset.range n,
        sfPeriodProduct (orbitIndex C y j) (flt (C : Mat(2, ℤ)) τ) /
          sfPeriodProduct (orbitIndex C y j) τ) =
      (∏ j ∈ Finset.range n, sfJacobiCocycleUHP (C : Mat(2, ℤ))
        (fracSymplecticFormRat (orbitIndex C y j) τ) τ) *
        sfPeriodProduct y (flt (C : Mat(2, ℤ)) τ) /
          sfPeriodProduct (orbitIndex C y n) (flt (C : Mat(2, ℤ)) τ) := by
  let f : ℕ → ℂ := fun j => sfPeriodProduct (orbitIndex C y j)
    (flt (C : Mat(2, ℤ)) τ)
  let g : ℕ → ℂ := fun j => sfPeriodProduct (orbitIndex C y j) τ
  have hf (j : ℕ) : f j ≠ 0 :=
    sfPeriodProduct_ne_zero (orbitIndex_ne_integral C hy j) (flt_im_pos C hτ)
  have hg (j : ℕ) : g j ≠ 0 :=
    sfPeriodProduct_ne_zero (orbitIndex_ne_integral C hy j) hτ
  calc
    (∏ j ∈ Finset.range n, f j / g j) =
        (∏ j ∈ Finset.range n, f (j + 1) / g j) * f 0 / f n :=
      prod_range_div_shift f g n (hf n) (fun j _ => hg j)
    _ = (∏ j ∈ Finset.range n, sfJacobiCocycleUHP (C : Mat(2, ℤ))
          (fracSymplecticFormRat (orbitIndex C y j) τ) τ) *
          sfPeriodProduct y (flt (C : Mat(2, ℤ)) τ) /
          sfPeriodProduct (orbitIndex C y n) (flt (C : Mat(2, ℤ)) τ) := by
      have hprod : (∏ j ∈ Finset.range n, f (j + 1) / g j) =
          ∏ j ∈ Finset.range n, sfJacobiCocycleUHP (C : Mat(2, ℤ))
            (fracSymplecticFormRat (orbitIndex C y j) τ) τ := by
        apply Finset.prod_congr rfl
        intro j _
        have hmove := sfPeriodProduct_ratVecAction_flt_eq_mul
          (orbitIndex_ne_integral C hy j) C hτ
        rw [← orbitIndex_succ C y j] at hmove
        exact (by
          dsimp only [f, g]
          rw [hmove]
          exact mul_div_cancel_right₀ _ (hg j))
      rw [hprod]
      simp only [f, orbitIndex, pow_zero, Matrix.SpecialLinearGroup.coe_one,
        ratVecAction_one]

/-- The quotient for `C^n` is the same Jacobi product evaluated along the transported
moduli, with its endpoint characteristic shift; used by `tendsto_sfPeriodProduct_orbit`. -/
private theorem pow_ratio_eq_prod_orbit (C : SL(2, ℤ)) {y : Fin 2 → ℚ}
    (hy : ¬ IsIntegralIndex y) (n : ℕ) {τ : ℂ} (hτ : 0 < τ.im) :
    sfPeriodProduct y (flt ((C ^ n : SL(2, ℤ)) : Mat(2, ℤ)) τ) /
        sfPeriodProduct y τ =
      (∏ j ∈ Finset.range n,
        sfJacobiCocycleUHP (C : Mat(2, ℤ))
          (fracSymplecticFormRat (orbitIndex C y j)
            (flt ((C ^ j : SL(2, ℤ)) : Mat(2, ℤ)) τ))
          (flt ((C ^ j : SL(2, ℤ)) : Mat(2, ℤ)) τ)) *
        sfPeriodProduct y (flt ((C ^ n : SL(2, ℤ)) : Mat(2, ℤ)) τ) /
          sfPeriodProduct (orbitIndex C y n)
            (flt ((C ^ n : SL(2, ℤ)) : Mat(2, ℤ)) τ) := by
  let f : ℕ → ℂ := fun j => sfPeriodProduct (orbitIndex C y j)
    (flt ((C ^ j : SL(2, ℤ)) : Mat(2, ℤ)) τ)
  let σ : ℕ → ℂ := fun j => sfJacobiCocycleUHP (C : Mat(2, ℤ))
    (fracSymplecticFormRat (orbitIndex C y j)
      (flt ((C ^ j : SL(2, ℤ)) : Mat(2, ℤ)) τ))
    (flt ((C ^ j : SL(2, ℤ)) : Mat(2, ℤ)) τ)
  have hf0 : f 0 ≠ 0 :=
    sfPeriodProduct_ne_zero (orbitIndex_ne_integral C hy 0) (flt_im_pos (C ^ 0) hτ)
  have hstep (j : ℕ) : f (j + 1) = σ j * f j := by
    have hmove := sfPeriodProduct_ratVecAction_flt_eq_mul
      (orbitIndex_ne_integral C hy j) C (flt_im_pos (C ^ j) hτ)
    rw [← orbitIndex_succ C y j, ← flt_pow_succ C j hτ] at hmove
    exact hmove
  have htel : (∏ j ∈ Finset.range n, σ j) = f n / f 0 := by
    apply Finset.prod_range_induction σ (fun j => f j / f 0) (div_self hf0) n
    intro j _
    rw [hstep j]
    field_simp [hf0]
  rw [htel]
  simp only [f, orbitIndex, pow_zero, Matrix.SpecialLinearGroup.coe_one,
    ratVecAction_one, flt_one]
  have hfn := sfPeriodProduct_ne_zero (orbitIndex_ne_integral C hy n)
    (flt_im_pos (C ^ n) hτ)
  have hf0 := sfPeriodProduct_ne_zero hy hτ
  field_simp [hf0, show sfPeriodProduct (ratVecAction ((C ^ n : SL(2, ℤ)) : Mat(2, ℤ)) y)
    (flt ((C ^ n : SL(2, ℤ)) : Mat(2, ℤ)) τ) ≠ 0 from hfn]
  exact (mul_div_cancel_right₀ _ hfn).symm

/-- The reciprocal endpoint factor of a finite characteristic orbit has the same
nonzero boundary value along every upper-half-plane approach. -/
private theorem tendsto_orbit_endpoint_shift {ι : Type*} {l : Filter ι}
    (w : ι → ℂ) {α : ℝ} (hα : Irrational α) {C : SL(2, ℤ)}
    {y : Fin 2 → ℚ} (hy : ¬ IsIntegralIndex y) (n : ℕ) (e : Fin 2 → ℤ)
    (heq : orbitIndex C y n = y + fun i => (e i : ℚ))
    (hwT : Tendsto w l (𝓝 (α : ℂ)))
    (hwIm : ∀ᶠ k in l, 0 < (w k).im) :
    Tendsto (fun k => sfPeriodProduct y (w k) /
      sfPeriodProduct (orbitIndex C y n) (w k)) l
      (𝓝 (qPochhammerFin (e 1)
        ((fracSymplecticFormRat y α : ℝ) : ℂ) (α : ℂ))) := by
  have h := tendsto_sfPeriodProduct_shift_div w hα hy e hwT hwIm
  have h' := h.inv₀ (inv_ne_zero (qPochhammerFin_shift_ne_zero hα hy (e 1)))
  apply (show Tendsto _ l (𝓝 (qPochhammerFin (e 1)
    ((fracSymplecticFormRat y α : ℝ) : ℂ) (α : ℂ))) by
      simpa only [inv_inv] using h').congr'
  filter_upwards with k
  rw [heq, inv_div]

/-- One exact orbit has the boundary value of the cocycle for its return matrix; used by
`tendsto_prod_sfPeriodProduct_div_orbits`. -/
private theorem tendsto_sfPeriodProduct_orbit {ι : Type*} {l : Filter ι}
    (tauSeq : ι → ℂ) {α : ℝ} (hα : Irrational α) {C : SL(2, ℤ)}
    (hfix : flt (C : Mat(2, ℤ)) α = α)
    (hj : 0 < fltDenominator (C : Mat(2, ℤ)) α)
    {y : Fin 2 → ℚ} (hy : ¬ IsIntegralIndex y) (n : ℕ)
    (hperiod : IsIntegralIndex (orbitIndex C y n - y))
    (htau : Tendsto tauSeq l (𝓝 (α : ℂ)))
    (him : ∀ᶠ k in l, 0 < (tauSeq k).im) :
    Tendsto (fun k => ∏ j ∈ Finset.range n,
      sfPeriodProduct (orbitIndex C y j) (flt (C : Mat(2, ℤ)) (tauSeq k)) /
        sfPeriodProduct (orbitIndex C y j) (tauSeq k)) l
      (𝓝 (sfModularCocycleReal' y (C ^ n) α)) := by
  rcases l.eq_or_neBot with hbot | hne
  · subst l
    exact Filter.tendsto_bot
  let : l.NeBot := hne
  have hpowfix : flt ((C ^ n : SL(2, ℤ)) : Mat(2, ℤ)) α = α :=
    flt_pow_of_flt_eq_self hj.ne' hfix n
  have hpowden : 0 < fltDenominator ((C ^ n : SL(2, ℤ)) : Mat(2, ℤ)) α := by
    rw [fltDenominator_pow_of_flt_eq_self hj.ne' hfix]
    exact pow_pos hj n
  have hpowMem : C ^ n ∈ gammaSubgroup y :=
    mem_gammaSubgroup_of_isIntegralIndex hperiod
  let e : Fin 2 → ℤ := fun i => Classical.choose (hperiod i)
  have heq : orbitIndex C y n = y + fun i => (e i : ℚ) := by
    ext i
    have hi := Classical.choose_spec (hperiod i)
    simp only [Pi.sub_apply, Pi.add_apply] at hi ⊢
    dsimp only [e]
    linarith
  let K : ℂ := qPochhammerFin (e 1) ((fracSymplecticFormRat y α : ℝ) : ℂ) (α : ℂ)
  have hTauPow (j : ℕ) := tendsto_flt_pow_fixed tauSeq hfix hj htau j
  have hImPow (j : ℕ) : ∀ᶠ k in l,
      0 < (flt ((C ^ j : SL(2, ℤ)) : Mat(2, ℤ)) (tauSeq k)).im :=
    him.mono fun _ hk => flt_im_pos (C ^ j) hk
  have hTauC : Tendsto (fun k => flt (C : Mat(2, ℤ)) (tauSeq k)) l
      (𝓝 (α : ℂ)) := by
    simpa only [pow_one] using hTauPow 1
  have hImC : ∀ᶠ k in l, 0 < (flt (C : Mat(2, ℤ)) (tauSeq k)).im :=
    him.mono fun _ hk => flt_im_pos C hk
  have hshiftC := tendsto_orbit_endpoint_shift
    (fun k => flt (C : Mat(2, ℤ)) (tauSeq k)) hα hy n e heq hTauC hImC
  have hshiftPow := tendsto_orbit_endpoint_shift
    (fun k => flt ((C ^ n : SL(2, ℤ)) : Mat(2, ℤ)) (tauSeq k))
    hα hy n e heq (hTauPow n) (hImPow n)
  let V : ℂ := ∏ j ∈ Finset.range n,
    sfJacobiCocycleCharBoundary C (orbitIndex C y j) α
  have hsig : Tendsto (fun k => ∏ j ∈ Finset.range n,
      sfJacobiCocycleUHP (C : Mat(2, ℤ))
        (fracSymplecticFormRat (orbitIndex C y j) (tauSeq k)) (tauSeq k))
      l (𝓝 V) := by
    apply tendsto_finsetProd (Finset.range n)
    intro j _
    exact tendsto_sfJacobiCocycle_char tauSeq hα (orbitIndex_ne_integral C hy j)
      hfix hj htau him
  have hsigPow : Tendsto (fun k => ∏ j ∈ Finset.range n,
      sfJacobiCocycleUHP (C : Mat(2, ℤ))
        (fracSymplecticFormRat (orbitIndex C y j)
          (flt ((C ^ j : SL(2, ℤ)) : Mat(2, ℤ)) (tauSeq k)))
        (flt ((C ^ j : SL(2, ℤ)) : Mat(2, ℤ)) (tauSeq k)))
      l (𝓝 V) := by
    apply tendsto_finsetProd (Finset.range n)
    intro j _
    exact tendsto_sfJacobiCocycle_char
      (fun k => flt ((C ^ j : SL(2, ℤ)) : Mat(2, ℤ)) (tauSeq k))
      hα (orbitIndex_ne_integral C hy j) hfix hj (hTauPow j) (hImPow j)
  have hleft : Tendsto (fun k => ∏ j ∈ Finset.range n,
      sfPeriodProduct (orbitIndex C y j) (flt (C : Mat(2, ℤ)) (tauSeq k)) /
        sfPeriodProduct (orbitIndex C y j) (tauSeq k)) l (𝓝 (V * K)) := by
    apply (hsig.mul hshiftC).congr'
    filter_upwards [him] with k hk
    simpa only [mul_div_assoc] using (prod_orbit_ratio_eq C hy n hk).symm
  have hright : Tendsto (fun k =>
      sfPeriodProduct y (flt ((C ^ n : SL(2, ℤ)) : Mat(2, ℤ)) (tauSeq k)) /
        sfPeriodProduct y (tauSeq k)) l (𝓝 (V * K)) := by
    apply (hsigPow.mul hshiftPow).congr'
    filter_upwards [him] with k hk
    simpa only [mul_div_assoc] using (pow_ratio_eq_prod_orbit C hy n hk).symm
  have hknown := tendsto_sfPeriodProduct_div_total tauSeq hpowMem hy hα hpowden
    hpowfix htau him
  have hvalue : V * K = sfModularCocycleRealTotal y (C ^ n) hpowMem α :=
    tendsto_nhds_unique hright hknown
  rw [sfModularCocycleReal'_of_mem hpowMem, ← hvalue]
  exact hleft

/-- The correction from replacing an orbit characteristic by a congruent one tends to one;
used to replace orbit iterates by the representatives in `S`. -/
private theorem tendsto_sfPeriodProduct_congr_factor {ι : Type*} {l : Filter ι}
    (tauSeq : ι → ℂ) {α : ℝ} (hα : Irrational α) {C : SL(2, ℤ)}
    (hfix : flt (C : Mat(2, ℤ)) α = α)
    (hj : 0 < fltDenominator (C : Mat(2, ℤ)) α)
    {s t : Fin 2 → ℚ} (ht : ¬ IsIntegralIndex t)
    (hcongr : IsIntegralIndex (s - t))
    (htau : Tendsto tauSeq l (𝓝 (α : ℂ)))
    (him : ∀ᶠ k in l, 0 < (tauSeq k).im) :
    Tendsto (fun k =>
      (sfPeriodProduct s (flt (C : Mat(2, ℤ)) (tauSeq k)) /
        sfPeriodProduct t (flt (C : Mat(2, ℤ)) (tauSeq k))) /
      (sfPeriodProduct s (tauSeq k) / sfPeriodProduct t (tauSeq k))) l (𝓝 (1 : ℂ)) := by
  let e : Fin 2 → ℤ := fun i => Classical.choose (hcongr i)
  have heq : s = t + fun i => (e i : ℚ) := by
    ext i
    have hi := Classical.choose_spec (hcongr i)
    simp only [Pi.sub_apply, Pi.add_apply] at hi ⊢
    dsimp only [e]
    linarith
  have htauC : Tendsto (fun k => flt (C : Mat(2, ℤ)) (tauSeq k)) l
      (𝓝 (α : ℂ)) := by
    simpa only [pow_one] using tendsto_flt_pow_fixed tauSeq hfix hj htau 1
  have himC : ∀ᶠ k in l, 0 < (flt (C : Mat(2, ℤ)) (tauSeq k)).im :=
    him.mono fun _ hk => flt_im_pos C hk
  let K : ℂ := (qPochhammerFin (e 1)
    ((fracSymplecticFormRat t α : ℝ) : ℂ) (α : ℂ))⁻¹
  have hK : K ≠ 0 := inv_ne_zero (qPochhammerFin_shift_ne_zero hα ht (e 1))
  have hshift : Tendsto (fun k => sfPeriodProduct s (tauSeq k) /
      sfPeriodProduct t (tauSeq k)) l (𝓝 K) := by
    simpa only [← heq] using tendsto_sfPeriodProduct_shift_div tauSeq hα ht e htau him
  have hshiftC : Tendsto (fun k => sfPeriodProduct s
      (flt (C : Mat(2, ℤ)) (tauSeq k)) /
      sfPeriodProduct t (flt (C : Mat(2, ℤ)) (tauSeq k))) l (𝓝 K) := by
    simpa only [← heq] using tendsto_sfPeriodProduct_shift_div
      (fun k => flt (C : Mat(2, ℤ)) (tauSeq k)) hα ht e htauC himC
  convert hshiftC.div hshift hK using 1
  · exact congrArg 𝓝 (div_self hK).symm

/-- A representative change factors the period-product quotient into the exact-orbit quotient
and its finite shift correction; used in the final orbit product. -/
private theorem sfPeriodProduct_div_eq_mul_correction {s t : Fin 2 → ℚ}
    (hs : ¬ IsIntegralIndex s) (ht : ¬ IsIntegralIndex t)
    (C : SL(2, ℤ)) {τ : ℂ} (hτ : 0 < τ.im) :
    sfPeriodProduct s (flt (C : Mat(2, ℤ)) τ) / sfPeriodProduct s τ =
      (sfPeriodProduct t (flt (C : Mat(2, ℤ)) τ) / sfPeriodProduct t τ) *
        ((sfPeriodProduct s (flt (C : Mat(2, ℤ)) τ) /
          sfPeriodProduct t (flt (C : Mat(2, ℤ)) τ)) /
          (sfPeriodProduct s τ / sfPeriodProduct t τ)) := by
  have hτC := flt_im_pos C hτ
  have hts := sfPeriodProduct_ne_zero ht hτ
  have hss := sfPeriodProduct_ne_zero hs hτ
  have htC := sfPeriodProduct_ne_zero ht hτC
  have hsC := sfPeriodProduct_ne_zero hs hτC
  field_simp [hts, hss, htC, hsC]

/-- Regroup a finite set of incongruent representatives by the exact iterates of an orbit
decomposition. This supplies the indexing of the boundary product. -/
private theorem exists_orbit_representatives {C : SL(2, ℤ)}
    {S R : Finset (Fin 2 → ℚ)} {m : (Fin 2 → ℚ) → ℕ+}
    (hSinj : ∀ s ∈ S, ∀ s' ∈ S, IsIntegralIndex (s - s') → s = s')
    (hR : IsOrbitDecomposition C S R m) :
    ∃ rep : Sigma (fun _ : Fin 2 → ℚ => ℕ) → Fin 2 → ℚ,
      (∀ q ∈ R.sigma (fun y => Finset.range (m y : ℕ)), rep q ∈ S) ∧
      (∀ q ∈ R.sigma (fun y => Finset.range (m y : ℕ)),
        IsIntegralIndex (rep q - orbitIndex C q.1 q.2)) ∧
      (∀ φ : (Fin 2 → ℚ) → ℂ,
        (∏ q ∈ R.sigma (fun y => Finset.range (m y : ℕ)), φ (rep q)) =
          ∏ s ∈ S, φ s) := by
  classical
  let T : Finset (Sigma (fun _ : Fin 2 → ℚ => ℕ)) :=
    R.sigma (fun y => Finset.range (m y : ℕ))
  have hexists (q : Sigma (fun _ : Fin 2 → ℚ => ℕ)) (hq : q ∈ T) :
      ∃ s ∈ S, IsIntegralIndex (s - orbitIndex C q.1 q.2) := by
    rcases Finset.mem_sigma.mp hq with ⟨hyR, hj⟩
    simpa only [orbitIndex] using
      hR.exists_mem q.1 hyR q.2 (Finset.mem_range.mp hj)
  let rep (q : Sigma (fun _ : Fin 2 → ℚ => ℕ)) : Fin 2 → ℚ :=
    if hq : q ∈ T then Classical.choose (hexists q hq) else 0
  have hrep_mem (q : Sigma (fun _ : Fin 2 → ℚ => ℕ)) (hq : q ∈ T) :
      rep q ∈ S := by
    simpa only [rep, dite_eq_left hq] using (Classical.choose_spec (hexists q hq)).1
  have hrep_congr (q : Sigma (fun _ : Fin 2 → ℚ => ℕ)) (hq : q ∈ T) :
      IsIntegralIndex (rep q - orbitIndex C q.1 q.2) := by
    simpa only [rep, dite_eq_left hq] using (Classical.choose_spec (hexists q hq)).2
  have hrep_inj (q : Sigma (fun _ : Fin 2 → ℚ => ℕ)) (hq : q ∈ T)
      (q' : Sigma (fun _ : Fin 2 → ℚ => ℕ)) (hq' : q' ∈ T)
      (heq : rep q = rep q') : q = q' := by
    rcases Finset.mem_sigma.mp hq with ⟨hyR, hj⟩
    rcases Finset.mem_sigma.mp hq' with ⟨hyR', hj'⟩
    have h1 := hrep_congr q hq
    have h2 := hrep_congr q' hq'
    rw [← heq] at h2
    have hdiff : IsIntegralIndex
        (orbitIndex C q.1 q.2 - orbitIndex C q'.1 q'.2) := by
      convert isIntegralIndex_sub h2 h1 using 1; abel
    obtain ⟨hyy, hjj⟩ := hR.iterate_injective q.1 hyR q'.1 hyR'
      q.2 (Finset.mem_range.mp hj) q'.2 (Finset.mem_range.mp hj') (by
        simpa only [orbitIndex] using hdiff)
    cases q with | mk y j =>
    cases q' with | mk y' j' =>
    cases hyy
    cases hjj
    rfl
  have hrep_surj (s : Fin 2 → ℚ) (hs : s ∈ S) :
      ∃ q, ∃ hq : q ∈ T, rep q = s := by
    obtain ⟨y, hyR, j, hj, hsj⟩ := hR.exists_iterate s hs
    let q : Sigma (fun _ : Fin 2 → ℚ => ℕ) := ⟨y, j⟩
    have hq : q ∈ T := Finset.mem_sigma.mpr
      ⟨hyR, Finset.mem_range.mpr hj⟩
    have hrep := hrep_congr q hq
    have hcongr : IsIntegralIndex (rep q - s) := by
      have hsj' : IsIntegralIndex (s - orbitIndex C y j) := by
        simpa only [orbitIndex] using hsj
      convert isIntegralIndex_sub hrep hsj' using 1; abel
    exact ⟨q, hq, hSinj (rep q) (hrep_mem q hq) s hs hcongr⟩
  have hprod_bij (φ : (Fin 2 → ℚ) → ℂ) :
      (∏ q ∈ T, φ (rep q)) = ∏ s ∈ S, φ s := by
    refine Finset.prod_bij (fun q _ => rep q)
      (fun q hq => hrep_mem q hq)
      (fun q hq q' hq' heq => hrep_inj q hq q' hq' heq)
      (fun s hs => hrep_surj s hs) ?_
    intro q _
    rfl
  exact ⟨rep, hrep_mem, hrep_congr, hprod_bij⟩

/-- **The orbit limit**: for `C ∈ SL₂(ℤ)` fixing an irrational `α` with `j_C(α) > 0`, a finite set
`S` of pairwise incongruent characteristics outside `ℤ²`, and an orbit decomposition `(R, m)` of
its classes under `C`, along every approach `τ_k → α` from `ℍ`,

$$\prod_{\mathbf s\in S}\frac{\varpi_{\mathbf s}(C\cdot\tau_k)}{\varpi_{\mathbf s}(\tau_k)}
  \longrightarrow \prod_{\mathbf y\in R} ש^{\mathbf y}_{C^{m(\mathbf y)}}(\alpha).$$

The orbit telescoping of [RW26b, Radchenko, Wheeler (2026b), Appendix A, proof of
Proposition 3]; for `m ≡ 1` it is the factor limit in the proof of [72, Kopp (2024),
Theorem 4.46, `thm:cllr`]. -/
theorem tendsto_prod_sfPeriodProduct_div_orbits {ι : Type*} {l : Filter ι} (tauSeq : ι → ℂ)
    {α : ℝ} (hα : Irrational α) {C : SL(2, ℤ)} (hfix : flt (C : Mat(2, ℤ)) α = α)
    (hj : 0 < fltDenominator (C : Mat(2, ℤ)) α) {S R : Finset (Fin 2 → ℚ)}
    {m : (Fin 2 → ℚ) → ℕ+} (hS : ∀ s ∈ S, ¬ IsIntegralIndex s)
    (hSinj : ∀ s ∈ S, ∀ s' ∈ S, IsIntegralIndex (s - s') → s = s')
    (hR : IsOrbitDecomposition C S R m) (htau : Tendsto tauSeq l (𝓝 (α : ℂ)))
    (him : ∀ᶠ k in l, 0 < (tauSeq k).im) :
    Tendsto (fun k => ∏ s ∈ S, sfPeriodProduct s (flt (C : Mat(2, ℤ)) (tauSeq k)) /
        sfPeriodProduct s (tauSeq k)) l
      (𝓝 (∏ y ∈ R, sfModularCocycleReal' y (C ^ (m y : ℕ)) α)) := by
  let T : Finset (Sigma (fun _ : Fin 2 → ℚ => ℕ)) :=
    R.sigma (fun y => Finset.range (m y : ℕ))
  have hy (y : Fin 2 → ℚ) (hyR : y ∈ R) : ¬ IsIntegralIndex y :=
    hR.not_isIntegralIndex_of_mem hS hyR
  obtain ⟨rep, hrep_mem, hrep_congr, hprod_bij⟩ :=
    exists_orbit_representatives hSinj hR
  have horbit : Tendsto (fun k => ∏ q ∈ T,
      sfPeriodProduct (orbitIndex C q.1 q.2)
        (flt (C : Mat(2, ℤ)) (tauSeq k)) /
        sfPeriodProduct (orbitIndex C q.1 q.2) (tauSeq k)) l
      (𝓝 (∏ y ∈ R, sfModularCocycleReal' y (C ^ (m y : ℕ)) α)) := by
    have h := tendsto_finsetProd R (fun y hyR =>
      tendsto_sfPeriodProduct_orbit tauSeq hα hfix hj (hy y hyR)
        (m y : ℕ) (hR.period y hyR) htau him)
    convert h using 1
    simp only [T, Finset.prod_sigma]
  have hcorrection : Tendsto (fun k => ∏ q ∈ T,
      (sfPeriodProduct (rep q) (flt (C : Mat(2, ℤ)) (tauSeq k)) /
        sfPeriodProduct (orbitIndex C q.1 q.2)
          (flt (C : Mat(2, ℤ)) (tauSeq k))) /
      (sfPeriodProduct (rep q) (tauSeq k) /
        sfPeriodProduct (orbitIndex C q.1 q.2) (tauSeq k))) l (𝓝 (1 : ℂ)) := by
    have h := tendsto_finsetProd T (fun q hq =>
      tendsto_sfPeriodProduct_congr_factor tauSeq hα hfix hj
        (orbitIndex_ne_integral C (hy q.1 (Finset.mem_sigma.mp hq).1) q.2)
        (hrep_congr q hq) htau him)
    simpa only [Finset.prod_const_one] using h
  have htotal := horbit.mul hcorrection
  have htotal' : Tendsto (fun k =>
      (∏ q ∈ T, sfPeriodProduct (orbitIndex C q.1 q.2)
          (flt (C : Mat(2, ℤ)) (tauSeq k)) /
          sfPeriodProduct (orbitIndex C q.1 q.2) (tauSeq k)) *
      (∏ q ∈ T,
        (sfPeriodProduct (rep q) (flt (C : Mat(2, ℤ)) (tauSeq k)) /
          sfPeriodProduct (orbitIndex C q.1 q.2)
            (flt (C : Mat(2, ℤ)) (tauSeq k))) /
        (sfPeriodProduct (rep q) (tauSeq k) /
          sfPeriodProduct (orbitIndex C q.1 q.2) (tauSeq k)))) l
      (𝓝 (∏ y ∈ R, sfModularCocycleReal' y (C ^ (m y : ℕ)) α)) := by
    simpa only [mul_one] using htotal
  apply htotal'.congr'
  filter_upwards [him] with k hk
  calc
    (∏ q ∈ T, sfPeriodProduct (orbitIndex C q.1 q.2)
        (flt (C : Mat(2, ℤ)) (tauSeq k)) /
        sfPeriodProduct (orbitIndex C q.1 q.2) (tauSeq k)) *
      (∏ q ∈ T,
        (sfPeriodProduct (rep q) (flt (C : Mat(2, ℤ)) (tauSeq k)) /
          sfPeriodProduct (orbitIndex C q.1 q.2)
            (flt (C : Mat(2, ℤ)) (tauSeq k))) /
        (sfPeriodProduct (rep q) (tauSeq k) /
          sfPeriodProduct (orbitIndex C q.1 q.2) (tauSeq k))) =
      (∏ q ∈ T, sfPeriodProduct (rep q)
        (flt (C : Mat(2, ℤ)) (tauSeq k)) / sfPeriodProduct (rep q) (tauSeq k)) := by
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro q hq
        exact (sfPeriodProduct_div_eq_mul_correction
          (hS (rep q) (hrep_mem q hq))
          (orbitIndex_ne_integral C (hy q.1 (Finset.mem_sigma.mp hq).1) q.2)
          C hk).symm
    _ = _ := hprod_bij (fun s =>
      sfPeriodProduct s (flt (C : Mat(2, ℤ)) (tauSeq k)) /
        sfPeriodProduct s (tauSeq k))

end SIC
