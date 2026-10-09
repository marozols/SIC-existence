/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Cocycle.FixedPointCharacter
import SICs.Dilogarithm.MetricGroup
import SICs.SL2Z.CharacteristicDuality

/-!
# The Finite Group of a Hyperbolic Matrix at its Attractive Fixed Point

The hypotheses on a hyperbolic matrix `γ ∈ SL₂(ℤ)` and a real fixed point `τ` under which
Radchenko and Wheeler's finite quantum dilogarithm is defined, the order `N = Tr γ - 2` of its
group `G = (ε - 1)⁻¹I_τ / I_τ`, and that group as the fixed characteristics modulo `N`.

This module follows [RW26, Radchenko, Wheeler (2026), Section 1 and Section 4.3,
`prop:rqffinitedilog`]: a hyperbolic `γ = (a b; c d)` with `c > 0` and trace `N + 2`, a fixed
point `τ` of `γ`, and `ε = j_γ(τ) = cτ + d > 1`, the larger root of `x² - (N + 2)x + 1`. It
generalizes `SICs.Principal.Dilogarithm.Group` from `γ = A_d`, `τ = ρ_d`, `N = d²(d - 3)` to
every such pair, for the pseudolattice formulation of [RW26b, Radchenko, Wheeler (2026b),
Section 3] in `SICs.Dilogarithm.Pseudolattice`.

## The argument

`IsAttractiveFixedPoint γ τ` bundles the standing hypotheses: `τ` irrational, `γ·τ = τ`,
`j_γ(τ) > 1`, `c > 0`. The quadratic relation of the fixed point, `cτ² + (d - a)τ - b = 0`
(`quadratic_of_flt_eq_self`), gives `ε² - (a + d)ε + 1 = 0`, hence `Tr γ = ε + ε⁻¹ > 2`, so
`N = Tr γ - 2 = ε + ε⁻¹ - 2 = (ε^{1/2} - ε^{-1/2})²` is a positive integer. Equivalently,
`(ε-1)² = Nε`, the pole-spacing identity used in the five-term strip. Moreover,
`√N = ε^{1/2} - ε^{-1/2}`, the identity `√N = E(0) - E(0)⁻¹` of [RW26b, Radchenko, Wheeler (2026b),
Section 3]. The group
`G = ℤ²/Λ_γ`, with the row congruence lattice
`Λ_γ = {u ∈ ℤ² : uγ ≡ u (mod N)} = ℤ²(γ - I)` of [RW26, Radchenko, Wheeler (2026), Section 1],
is isomorphic in characteristic coordinates to the kernel
`fixedCharacteristics γ N` of `γ - I` on `(ℤ/Nℤ)²`, the residue vectors `x` with
`γ ∈ Γ_{x/N}` (`mem_fixedCharacteristics_iff`); `det(γ - I) = 2 - Tr γ = -N` makes
`latticeCharacteristic γ N` its parametrization by `ℤ²`. The Gaussian `⟨x⟩` and bicharacter
`⟨x; y⟩` on it are `fixedGaussian γ N` and `fixedBicharacter γ N` of
`SICs.SL2Z.TorsionCharacteristics`. Their Gaussian and bicharacter laws, the nondegeneracy
`fixedBicharacter_eq_one_forall_iff`, and the order `|G| = N` (`card_fixedCharacteristics`)
make `G` a metric group with `s = √N` (`fixedMetricGroup`), the setting of
`SICs.Dilogarithm.FiniteQuantum`.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### The attractive fixed point

The standing hypotheses of [RW26, Radchenko, Wheeler (2026), Section 1] on `(γ, τ)`. -/

/-- **A hyperbolic matrix at its attractive fixed point**, the standing hypotheses of
[RW26, Radchenko, Wheeler (2026), Section 1]: `τ` irrational, `γ·τ = τ`, `ε = j_γ(τ) > 1`, and
`c > 0`. Every oriented basis of a pseudolattice with totally positive second vector produces
such a pair ([RW26b, Radchenko, Wheeler (2026b), Section 3]), and `(A_d, ρ_d)` is one. -/
structure IsAttractiveFixedPoint (A : SL(2, ℤ)) (τ : ℝ) : Prop where
  /-- `τ` is irrational. -/
  irrational : Irrational τ
  /-- `γ·τ = τ`. -/
  flt_eq : flt (A : Mat(2, ℤ)) τ = τ
  /-- `ε = j_γ(τ) = cτ + d > 1`. -/
  one_lt_fltDenominator : 1 < fltDenominator (A : Mat(2, ℤ)) τ
  /-- `c > 0`. -/
  lowerLeft_pos : 0 < (A : Mat(2, ℤ)) 1 0

namespace IsAttractiveFixedPoint

variable {A : SL(2, ℤ)} {τ : ℝ}

/-- `j_γ(τ) > 0`. -/
theorem fltDenominator_pos (h : IsAttractiveFixedPoint A τ) :
    0 < fltDenominator (A : Mat(2, ℤ)) τ :=
  zero_lt_one.trans h.one_lt_fltDenominator

/-- `c ≥ 0`, the form in which Kopp's reflection law takes the sign of `c`. -/
theorem lowerLeft_nonneg (h : IsAttractiveFixedPoint A τ) : 0 ≤ (A : Mat(2, ℤ)) 1 0 :=
  h.lowerLeft_pos.le

/-- **`ε` is a root of `x² - (Tr γ)x + 1`**: `ε² - (a + d)ε + 1 = 0`, from the quadratic
relation `cτ² + (d - a)τ - b = 0` of the fixed point (`quadratic_of_flt_eq_self`) and
`ad - bc = 1`. -/
theorem fltDenominator_sq (h : IsAttractiveFixedPoint A τ) :
    fltDenominator (A : Mat(2, ℤ)) τ ^ 2 -
      ((A : Mat(2, ℤ)) 0 0 + (A : Mat(2, ℤ)) 1 1 : ℝ) * fltDenominator (A : Mat(2, ℤ)) τ + 1 =
        0 := by
  have hquad := quadratic_of_flt_eq_self h.fltDenominator_pos.ne' h.flt_eq
  have hdetZ : (A : Mat(2, ℤ)).det = 1 := Matrix.SpecialLinearGroup.det_coe A
  rw [Matrix.det_fin_two] at hdetZ
  have hdet : (A 0 0 : ℝ) * A 1 1 - (A 0 1 : ℝ) * A 1 0 = 1 := by
    exact_mod_cast hdetZ
  unfold fltDenominator
  linear_combination (A 1 0 : ℝ) * hquad - hdet

/-- **`Tr γ = ε + ε⁻¹`** (`fltDenominator_sq` divided by `ε`). -/
theorem trace_eq (h : IsAttractiveFixedPoint A τ) :
    ((A : Mat(2, ℤ)) 0 0 + (A : Mat(2, ℤ)) 1 1 : ℝ) =
      fltDenominator (A : Mat(2, ℤ)) τ + (fltDenominator (A : Mat(2, ℤ)) τ)⁻¹ := by
  have hne := h.fltDenominator_pos.ne'
  have hinv := mul_inv_cancel₀ hne
  have hroot := h.fltDenominator_sq
  apply (mul_right_cancel₀ hne)
  nlinarith

/-- **`Tr γ > 2`**: `ε + ε⁻¹ > 2` for `ε > 1`. -/
theorem two_lt_trace (h : IsAttractiveFixedPoint A τ) :
    2 < (A : Mat(2, ℤ)) 0 0 + (A : Mat(2, ℤ)) 1 1 := by
  let ε := fltDenominator (A : Mat(2, ℤ)) τ
  have hε : 1 < ε := h.one_lt_fltDenominator
  have hεpos : 0 < ε := zero_lt_one.trans hε
  have hεsq : 0 < (ε - 1) ^ 2 := sq_pos_of_pos (sub_pos.mpr hε)
  have hεeq : ε + ε⁻¹ - 2 = (ε - 1) ^ 2 / ε := by
    field_simp
    ring
  have hreal : (2 : ℝ) < ((A : Mat(2, ℤ)) 0 0 + (A : Mat(2, ℤ)) 1 1 : ℝ) := by
    rw [h.trace_eq, ← sub_pos, hεeq]
    exact div_pos hεsq hεpos
  exact_mod_cast hreal

/-- `Tr γ > 0`, the hypothesis of `etaMultiplier_sq_of_trace_pos`. -/
theorem trace_pos (h : IsAttractiveFixedPoint A τ) :
    0 < (A : Mat(2, ℤ)) 0 0 + (A : Mat(2, ℤ)) 1 1 :=
  lt_trans (by norm_num) h.two_lt_trace

end IsAttractiveFixedPoint

/-! ### The order `N = Tr γ - 2` and the group

`|G| = N`, with `ε` the larger root of `x² - (N + 2)x + 1`. -/

/-- **The order `N = Tr γ - 2`** of the group of [RW26, Radchenko, Wheeler (2026), Section 1],
as a natural number; it is `|G_{I,ε}| = Tr ε - 2` of [RW26b, Radchenko, Wheeler (2026b),
Definition 1]. Meaningful for `Tr γ > 2`. -/
def finiteDilogOrder (A : SL(2, ℤ)) : ℕ :=
  ((A : Mat(2, ℤ)) 0 0 + (A : Mat(2, ℤ)) 1 1 - 2).toNat

/-- Conjugation preserves the finite group order `N = Tr γ - 2`. -/
theorem finiteDilogOrder_conj (A R : SL(2, ℤ)) :
    finiteDilogOrder (R * A * R⁻¹) = finiteDilogOrder A := by
  have htr : ((R * A * R⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)).trace =
      (A : Mat(2, ℤ)).trace := by
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
    rw [Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]
    simp
  unfold finiteDilogOrder
  congr 1
  simpa [Matrix.trace, Matrix.diag, Fin.sum_univ_two] using htr

/-- `N > 0` at an attractive fixed point (`IsAttractiveFixedPoint.two_lt_trace`). -/
theorem finiteDilogOrder_pos {A : SL(2, ℤ)} {τ : ℝ} (h : IsAttractiveFixedPoint A τ) :
    0 < finiteDilogOrder A := by
  have htrace := h.two_lt_trace
  unfold finiteDilogOrder
  omega

/-- `N ≠ 0` as an instance-shaped fact. -/
theorem finiteDilogOrder_neZero {A : SL(2, ℤ)} {τ : ℝ} (h : IsAttractiveFixedPoint A τ) :
    NeZero (finiteDilogOrder A) :=
  ⟨(finiteDilogOrder_pos h).ne'⟩

/-- `(N : ℤ) = Tr γ - 2`. -/
theorem cast_finiteDilogOrder {A : SL(2, ℤ)} {τ : ℝ} (h : IsAttractiveFixedPoint A τ) :
    (finiteDilogOrder A : ℤ) = (A : Mat(2, ℤ)) 0 0 + (A : Mat(2, ℤ)) 1 1 - 2 := by
  have htrace := h.two_lt_trace
  change ((A 0 0 + A 1 1 - 2 : ℤ).toNat : ℤ) = A 0 0 + A 1 1 - 2
  exact Int.toNat_of_nonneg (by omega : 0 ≤ A 0 0 + A 1 1 - 2)

/-- **`N = ε + ε⁻¹ - 2`** as real numbers (`IsAttractiveFixedPoint.trace_eq`). -/
theorem cast_finiteDilogOrder_eq {A : SL(2, ℤ)} {τ : ℝ} (h : IsAttractiveFixedPoint A τ) :
    (finiteDilogOrder A : ℝ) =
      fltDenominator (A : Mat(2, ℤ)) τ + (fltDenominator (A : Mat(2, ℤ)) τ)⁻¹ - 2 := by
  have hcast := cast_finiteDilogOrder h
  have hreal : (finiteDilogOrder A : ℝ) =
      ((A : Mat(2, ℤ)) 0 0 + (A : Mat(2, ℤ)) 1 1 : ℝ) - 2 := by
    exact_mod_cast hcast
  rw [hreal, h.trace_eq]

/-- The fixed-point unit equation `(ε-1)² = Nε`. -/
theorem IsAttractiveFixedPoint.denominator_sub_one_sq {A : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint A τ) :
    (fltDenominator (A : Mat(2, ℤ)) τ - 1) ^ 2 =
      (finiteDilogOrder A : ℝ) * fltDenominator (A : Mat(2, ℤ)) τ := by
  have hε : fltDenominator (A : Mat(2, ℤ)) τ ≠ 0 :=
    h.fltDenominator_pos.ne'
  rw [cast_finiteDilogOrder_eq h]
  nlinarith [mul_inv_cancel₀ hε]

/-- **`det(γ - I) = -N`**: `det(γ - I) = 2 - Tr γ` for `det γ = 1`; the hypothesis of
`latticeCharacteristic_mem` and `exists_latticeCharacteristic_eq`. -/
theorem det_sub_one_eq_neg_finiteDilogOrder {A : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint A τ) :
    ((A : Mat(2, ℤ)) - 1).det = -(finiteDilogOrder A : ℤ) := by
  have hdet : (A : Mat(2, ℤ)).det = 1 := Matrix.SpecialLinearGroup.det_coe A
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.det_fin_two]
  simp only [Matrix.sub_apply, Matrix.one_apply]
  norm_num
  rw [cast_finiteDilogOrder h]
  nlinarith

/-- **`√N = ε^{1/2} - ε^{-1/2}`**, the identity `√N = E(0) - E(0)⁻¹` of
[RW26b, Radchenko, Wheeler (2026b), Section 3], from `N = ε + ε⁻¹ - 2 = (ε^{1/2} - ε^{-1/2})²`
and `ε > 1`. -/
theorem sqrt_finiteDilogOrder_eq {A : SL(2, ℤ)} {τ : ℝ} (h : IsAttractiveFixedPoint A τ) :
    Real.sqrt (finiteDilogOrder A) =
      Real.sqrt (fltDenominator (A : Mat(2, ℤ)) τ) -
        (Real.sqrt (fltDenominator (A : Mat(2, ℤ)) τ))⁻¹ := by
  let ε := fltDenominator (A : Mat(2, ℤ)) τ
  let s := Real.sqrt ε
  have hε : 1 < ε := h.one_lt_fltDenominator
  have hspos : 0 < s := Real.sqrt_pos.2 (zero_lt_one.trans hε)
  have hsq : s ^ 2 = ε := Real.sq_sqrt (zero_lt_one.trans hε).le
  have hdiffpos : 0 ≤ s - s⁻¹ := by
    have hsqgt : 0 < s ^ 2 - 1 := by rw [hsq]; linarith
    have hdiff : s - s⁻¹ = (s ^ 2 - 1) / s := by
      field_simp
    rw [hdiff]
    exact (div_pos hsqgt hspos).le
  apply (Real.sqrt_eq_iff_eq_sq (Nat.cast_nonneg _) hdiffpos).2
  rw [cast_finiteDilogOrder_eq h]
  have hinv_sq : (s⁻¹) ^ 2 = ε⁻¹ := by rw [inv_pow, hsq]
  have hsinv : s * s⁻¹ = 1 := mul_inv_cancel₀ hspos.ne'
  nlinarith

/-- **The group `G`** of [RW26, Radchenko, Wheeler (2026), Section 1] for a hyperbolic `γ`: the
residue vectors `x ∈ (ℤ/Nℤ)²` whose characteristic `x/N` is fixed by `γ` modulo `ℤ²`, the kernel
`fixedCharacteristics` of `γ - I`; `G = ℤ²/Λ_γ` with `Λ_γ = Nℤ² + ker(γ - 1) = im(γ - 1)` of
[RW26, Radchenko, Wheeler (2026), Section 4.3, `prop:rqffinitedilog`] in characteristic
coordinates. -/
abbrev finiteDilogGroup (A : SL(2, ℤ)) : AddSubgroup (Fin 2 → ZMod (finiteDilogOrder A)) :=
  fixedCharacteristics (A : Mat(2, ℤ)) (finiteDilogOrder A)

/-- Conjugation identifies `G_A` with `G_{RAR⁻¹}` by the residue action of `R`. -/
def finiteDilogGroup_conjAddEquiv (A R : SL(2, ℤ)) :
    finiteDilogGroup A ≃+ finiteDilogGroup (R * A * R⁻¹) :=
  (fixedCharacteristics_conjAddEquiv A R (finiteDilogOrder A)).trans
    (fixedCharacteristics_congrModulus _ (finiteDilogOrder_conj A R).symm)

/-- The conjugation equivalence acts by `R` on residue vectors, with the equal-modulus cast. -/
private theorem finiteDilogGroup_conjAddEquiv_apply (A R : SL(2, ℤ))
    (x : finiteDilogGroup A) :
    ((finiteDilogGroup_conjAddEquiv A R x : finiteDilogGroup (R * A * R⁻¹)) :
        Fin 2 → ZMod (finiteDilogOrder (R * A * R⁻¹))) =
      fun i => ZMod.ringEquivCongr (finiteDilogOrder_conj A R).symm
        (residueMulVec R (finiteDilogOrder A) x i) := by
  simp [finiteDilogGroup_conjAddEquiv, fixedCharacteristics_conjAddEquiv,
    fixedCharacteristics_congrModulus_apply]

/-- The rational lift of the transported residue is the lift of `Rx` modulo integral indices. -/
theorem zmodCharacteristic_conjAddEquiv (A R : SL(2, ℤ)) (x : finiteDilogGroup A) :
    zmodCharacteristic (finiteDilogOrder (R * A * R⁻¹))
      (finiteDilogGroup_conjAddEquiv A R x :
        Fin 2 → ZMod (finiteDilogOrder (R * A * R⁻¹))) =
      zmodCharacteristic (finiteDilogOrder A)
        (residueMulVec R (finiteDilogOrder A) x) := by
  rw [finiteDilogGroup_conjAddEquiv_apply]
  funext i
  simp only [zmodCharacteristic, ZMod.ringEquivCongr_val, finiteDilogOrder_conj]

/-- The conjugation equivalence preserves the bicharacter of the finite dilogarithm group. -/
theorem finiteDilogGroup_conj_bichar (A R : SL(2, ℤ))
    [NeZero (finiteDilogOrder A)] (x y : finiteDilogGroup A) :
    fixedBicharacter (R * A * R⁻¹) (finiteDilogOrder (R * A * R⁻¹))
      (finiteDilogGroup_conjAddEquiv A R x) (finiteDilogGroup_conjAddEquiv A R y) =
        fixedBicharacter A (finiteDilogOrder A) x y := by
  change thetaBicharacter
    (zmodCharacteristic (finiteDilogOrder (R * A * R⁻¹))
      (finiteDilogGroup_conjAddEquiv A R x :
        Fin 2 → ZMod (finiteDilogOrder (R * A * R⁻¹))))
    (zmodCharacteristic (finiteDilogOrder (R * A * R⁻¹))
      (finiteDilogGroup_conjAddEquiv A R y :
        Fin 2 → ZMod (finiteDilogOrder (R * A * R⁻¹))))
    (R * A * R⁻¹ : SL(2, ℤ)) =
      fixedBicharacter A (finiteDilogOrder A) x y
  rw [zmodCharacteristic_conjAddEquiv, zmodCharacteristic_conjAddEquiv]
  exact fixedBicharacter_conj A R (finiteDilogOrder A) x.property y.property

/-- Membership in `G` is `γ ∈ Γ_{x/N}` (`mem_fixedCharacteristics_iff`). -/
theorem mem_finiteDilogGroup_iff {A : SL(2, ℤ)} {τ : ℝ} (h : IsAttractiveFixedPoint A τ)
    (x : Fin 2 → ZMod (finiteDilogOrder A)) :
    x ∈ finiteDilogGroup A ↔
      A ∈ gammaSubgroup (zmodCharacteristic (finiteDilogOrder A) x) := by
  have : NeZero (finiteDilogOrder A) := finiteDilogOrder_neZero h
  exact mem_fixedCharacteristics_iff A (finiteDilogOrder A) x

/-- Every element of `G` is the residue of a lattice vector `-adj(γ - I)k`
(`exists_latticeCharacteristic_eq` at `det(γ - I) = -N`). -/
theorem exists_latticeCharacteristic_eq_of_mem {A : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint A τ) {x : Fin 2 → ZMod (finiteDilogOrder A)}
    (hx : x ∈ finiteDilogGroup A) :
    ∃ k : Fin 2 → ℤ, latticeCharacteristic A (finiteDilogOrder A) k = x := by
  have : NeZero (finiteDilogOrder A) := finiteDilogOrder_neZero h
  exact exists_latticeCharacteristic_eq A (finiteDilogOrder A)
    (det_sub_one_eq_neg_finiteDilogOrder h) hx

/-! ### The metric group

The fixed characteristics modulo `N` with the Gaussian `fixedGaussian` and `s = √N`, for every
`M` with `det(M - I) = -N`. -/

/-- The quotient of fixed Gaussians equals the bicharacter, for `fixedMetricGroup`. -/
private theorem fixedBicharacter_eq_gaussian_div (M : SL(2, ℤ)) (N : ℕ) [NeZero N]
    {x y : Fin 2 → ZMod N}
    (hx : x ∈ fixedCharacteristics (M : Mat(2, ℤ)) N)
    (hy : y ∈ fixedCharacteristics (M : Mat(2, ℤ)) N) :
    fixedGaussian M N (x + y) / (fixedGaussian M N x * fixedGaussian M N y) =
      fixedBicharacter M N x y := by
  rw [fixedGaussian_add M N hx hy]
  exact mul_div_cancel_left₀ _
    (mul_ne_zero (fixedGaussian_ne_zero M N x) (fixedGaussian_ne_zero M N y))

/-- The quotient bicharacter is additive on the right, for `fixedMetricGroup`. -/
private theorem fixedBicharacter_add_right_div (M : SL(2, ℤ)) (N : ℕ) [NeZero N]
    (x y z : fixedCharacteristics (M : Mat(2, ℤ)) N) :
    fixedGaussian M N (x + (y + z)) / (fixedGaussian M N x * fixedGaussian M N (y + z)) =
      fixedGaussian M N (x + y) / (fixedGaussian M N x * fixedGaussian M N y) *
        (fixedGaussian M N (x + z) / (fixedGaussian M N x * fixedGaussian M N z)) := by
  rw [fixedBicharacter_eq_gaussian_div M N x.property
      (AddSubgroup.add_mem _ y.property z.property),
    fixedBicharacter_eq_gaussian_div M N x.property y.property,
    fixedBicharacter_eq_gaussian_div M N x.property z.property]
  exact fixedBicharacter_add_right M N x.property y.property z.property

/-- The quotient bicharacter is nondegenerate, for `fixedMetricGroup`. -/
private theorem fixedBicharacter_nondegenerate_div (M : SL(2, ℤ)) (N : ℕ) [NeZero N]
    (hdet : ((M : Mat(2, ℤ)) - 1).det = -(N : ℤ))
    (x : fixedCharacteristics (M : Mat(2, ℤ)) N)
    (hx : ∀ y : fixedCharacteristics (M : Mat(2, ℤ)) N,
      fixedGaussian M N (x + y) / (fixedGaussian M N x * fixedGaussian M N y) = 1) :
    x = 0 := by
  apply Subtype.ext
  apply (fixedBicharacter_eq_one_forall_iff M N hdet x.property).mp
  intro y
  rw [fixedBicharacter_comm]
  exact (fixedBicharacter_eq_gaussian_div M N x.property y.property).symm.trans (hx y)

/-- **The metric group `G`** of [RW26, Radchenko, Wheeler (2026), Section 4.3,
`prop:rqffinitedilog`]: the fixed characteristics modulo `N` with the Gaussian `⟨x⟩`
(`fixedGaussian`) and `s = √N`, when `det(M - I) = -N`; for `M = γ` hyperbolic with trace
`N + 2` this is `G = ℤ²/Λ_γ` with its Gaussian. -/
def fixedMetricGroup (M : SL(2, ℤ)) (N : ℕ) [NeZero N]
    (hdet : ((M : Mat(2, ℤ)) - 1).det = -(N : ℤ)) :
    MetricGroup (fixedCharacteristics (M : Mat(2, ℤ)) N) ℂ where
  gaussian x := fixedGaussian M N x
  gaussian_ne_zero x := fixedGaussian_ne_zero M N x
  gaussian_neg x := fixedGaussian_neg M N x.property
  bichar_add_right' x y z := fixedBicharacter_add_right_div M N x y z
  nondegenerate x hx := fixedBicharacter_nondegenerate_div M N hdet x hx
  sqrtCard := (Real.sqrt N : ℂ)
  sqrtCard_sq := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg N), card_fixedCharacteristics M N hdet]
    norm_cast
  sqrtCard_ne_zero := by
    exact_mod_cast (Real.sqrt_ne_zero').mpr (Nat.cast_pos.mpr (NeZero.pos N))

/-- The Gaussian of `fixedMetricGroup` is `fixedGaussian`. -/
@[simp]
theorem fixedMetricGroup_gaussian (M : SL(2, ℤ)) (N : ℕ) [NeZero N]
    (hdet : ((M : Mat(2, ℤ)) - 1).det = -(N : ℤ)) (x : fixedCharacteristics (M : Mat(2, ℤ)) N) :
    (fixedMetricGroup M N hdet).gaussian x = fixedGaussian M N x :=
  rfl

/-- The bicharacter of `fixedMetricGroup` is `fixedBicharacter`. -/
@[simp]
theorem fixedMetricGroup_bichar (M : SL(2, ℤ)) (N : ℕ) [NeZero N]
    (hdet : ((M : Mat(2, ℤ)) - 1).det = -(N : ℤ)) (x y : fixedCharacteristics (M : Mat(2, ℤ)) N) :
    (fixedMetricGroup M N hdet).bichar x y = fixedBicharacter M N x y := by
  exact fixedBicharacter_eq_gaussian_div M N x.property y.property

/-- The square root of the order in `fixedMetricGroup` is `√N`. -/
@[simp]
theorem fixedMetricGroup_sqrtCard (M : SL(2, ℤ)) (N : ℕ) [NeZero N]
    (hdet : ((M : Mat(2, ℤ)) - 1).det = -(N : ℤ)) :
    (fixedMetricGroup M N hdet).sqrtCard = (Real.sqrt N : ℂ) :=
  rfl

end SIC

end
