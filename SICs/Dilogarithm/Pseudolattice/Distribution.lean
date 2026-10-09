/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Cocycle.ConductorZeroClass
import SICs.Dilogarithm.Pseudolattice.Nested
import SICs.Dilogarithm.Pseudolattice.Powers

/-!
# The distribution relation of the finite quantum dilogarithm

For nested pseudolattices `I ⊆ J` with common period `ε`, the product over the `ε`-orbits of a
fibre of `K/I → K/J` is `E_{J,ε}` at that fibre, up to the eta-multiplier factor.

This module formalizes [RW26b, Radchenko, Wheeler (2026b), Proposition 3(i), equation (10)]:

$$\frac{\mu_{I,\varepsilon}^{d}}{\mu_{J,\varepsilon}}E_{J,\varepsilon}(x)
  = \prod_{y\in\mathcal R_x}E_{I,\varepsilon^{r_y}}(y),
  \qquad d=\sum_{y\in\mathcal R_x}r_y.$$

When `(ε - 1)J ⊆ I`, every orbit has length one. This gives Proposition 3(ii), equation (11),
over a set of representatives of `J/I` (`IsQuotientTransversal`).

## The argument

Let `B` be the inclusion matrix (`exists_inclusionMatrix`): `r_J = B r_I`, `B·β_I = β_J`,
`j_B(β_I) > 0`, `Bγ_I = γ_J B`, and `det B > 0`. The characteristics of a transversal of
`J/I` represent the classes over `r_J(x)`. Multiplication by `ε⁻¹` acts on characteristics by
`γ_I`; the index reversal `j ↦ r_y - j` identifies its orbits with the given `ε`-orbits.

*Nonzero fibres* (`x ∉ J`). The orbit conductor relation
(`sfModularCocycleRealTotal_eq_prod_orbits_of_mem_Gf`) gives the product of the cocycle values
`ש^{r_I(y)}_{γ_I^{r_y}}(β_I)` over the representatives. Each dilogarithm factor is
`μ_{γ_I}^{r_y}/ש^{r_I(y)}_{γ_I^{r_y}}(β_I)`, so the multipliers total `μ_{γ_I}^d`.

*The zero fibre* (`x ∈ J`). Exactly one orbit meets `I`; its length is one and its value is
`√ε`, as is `E_{J,ε}(x)`. For all other orbits, the zero-class relation
(`prod_sfModularCocycleReal'_orbits_preimage_zero`) gives the cocycle product
`μ_{γ_J}/μ_{γ_I}`. The remaining eta multipliers again total the required power.

## Main declarations

- `pseudolatticeDilog_orbit_distribution`: [RW26b, Radchenko, Wheeler (2026b),
  Proposition 3(i), equation (10)].
- `pseudolatticeDilog_distribution`: its length-one case, [RW26b, Radchenko, Wheeler (2026b),
  Proposition 3(ii), equation (11)].
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
variable {F : RealQuadraticFieldData K}

/-! ### Characteristic fibres

Representatives of `J/I` give the characteristic preimage needed for the orbit conductor
relations. -/

/-- The characteristics of a coset transversal for `J/I` represent exactly the classes over
`r_J(x)` under the inclusion matrix; used by `pseudolatticeDilog_orbit_distribution`. -/
private theorem characteristic_preimageTransversal {B B' : PseudolatticeBasis F}
    {M : Mat(2, ℤ)} (hdet : 0 < M.det)
    (hM : IsPairMap M B.tau ((M.det : K) * B'.scale / B.scale) B'.tau)
    {T : Finset K} (hT : IsQuotientTransversal B.submodule B'.submodule T) (x : K) :
    IsPreimageTransversal M (B'.characteristic x)
      (T.image fun t => B.characteristic (x + t)) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    rw [← B.characteristic_eq_ratVecAction_of_inclusion hdet hM,
      ← B'.characteristic_sub]
    exact (B'.isIntegralIndex_characteristic_iff _).mpr (by
      simpa only [add_sub_cancel_left] using hT.mem t ht)
  · intro s hs s' hs' hss'
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp hs'
    rw [← B.characteristic_sub] at hss'
    have hsub : t - t' ∈ B.submodule := by
      convert (B.isIntegralIndex_characteristic_iff _).mp hss' using 1; ring
    rw [hT.eq_of_sub_mem t ht t' ht' hsub]
  · intro s hs
    let y : K := B.scale * fracSymplecticFormRat s B.tau
    have hy : B.characteristic y = s := B.characteristic_scale_fracSymplecticFormRat s
    have hyx : y - x ∈ B'.submodule := by
      apply (B'.isIntegralIndex_characteristic_iff _).mp
      rw [B'.characteristic_sub,
        B.characteristic_eq_ratVecAction_of_inclusion hdet hM, hy]
      exact hs
    obtain ⟨t, ht, hyt⟩ := hT.exists_mem (y - x) hyx
    refine ⟨B.characteristic (x + t), Finset.mem_image.mpr ⟨t, ht, rfl⟩, ?_⟩
    rw [← hy, ← B.characteristic_sub]
    apply (B.isIntegralIndex_characteristic_iff _).mpr
    convert hyt using 1; ring

/-! ### Orbit indexing

The period matrix acts on characteristics by the inverse unit. Reversing the indices of each
finite unit orbit identifies these characteristic orbits with the given fibre orbits. -/

/-- Reverse an index in a nonempty cyclic orbit; used by `orbit_reverse_congruent`. -/
private def orbitReverse (n j : ℕ) : ℕ := if j = 0 then 0 else n - j

/-- Reversal preserves the range of a nonempty cyclic orbit; used by
`orbit_reverse_congruent`. -/
private theorem orbitReverse_lt {n j : ℕ} (hn : 0 < n) (hj : j < n) :
    orbitReverse n j < n := by
  unfold orbitReverse
  split_ifs with hzero
  · omega
  · omega

/-- Reversing a cyclic index twice recovers it; used by `orbit_reverse_congruent`. -/
private theorem orbitReverse_involutive {n j : ℕ} (hn : 0 < n) (hj : j < n) :
    orbitReverse n (orbitReverse n j) = j := by
  unfold orbitReverse
  split_ifs with hzero hzero'
  · omega
  · omega
  · omega
  · omega

/-- Inverse powers of a period preserve its pseudolattice; used by
`orbit_reverse_congruent`. -/
private theorem period_inv_pow_mem {B : PseudolatticeBasis F} {ε : K}
    (h : B.IsPeriod ε) {z : K} (hz : z ∈ B.submodule) (j : ℕ) :
    (ε⁻¹) ^ j * z ∈ B.submodule := by
  induction j with
  | zero => simpa using hz
  | succ j ih => simpa only [pow_succ', mul_assoc] using h.inv_mul_mem ih

/-- A forward iterate and the reverse inverse iterate of a unit orbit agree modulo `I`;
used by `orbit_characteristic_decomposition`. -/
private theorem orbit_reverse_congruent {B : PseudolatticeBasis F} {ε y : K}
    (h : B.IsPeriod ε) {n j : ℕ} (hj : j < n)
    (hper : ε ^ n * y - y ∈ B.submodule) :
    ε ^ j * y - (ε⁻¹) ^ (orbitReverse n j) * y ∈ B.submodule := by
  by_cases hzero : j = 0
  · simp [orbitReverse, hzero]
  · have hle : j ≤ n := hj.le
    have heq : n = j + (n - j) := by omega
    have hmem := period_inv_pow_mem h hper (n - j)
    have hcancel : (ε⁻¹) ^ (n - j) * ε ^ (n - j) = 1 := by
      rw [inv_pow]
      exact inv_mul_cancel₀ (pow_ne_zero _ h.ne_zero)
    have halg : (ε⁻¹) ^ (n - j) * (ε ^ n * y - y) =
        ε ^ j * y - (ε⁻¹) ^ (n - j) * y := by
      have hp : ε ^ n = ε ^ j * ε ^ (n - j) := by
        conv_lhs => rw [heq, pow_add]
      rw [hp]
      calc
        _ = ((ε⁻¹) ^ (n - j) * ε ^ (n - j)) * ε ^ j * y -
            (ε⁻¹) ^ (n - j) * y := by ring
        _ = _ := by rw [hcancel, one_mul]
    have hrev : orbitReverse n j = n - j := by simp [orbitReverse, hzero]
    rw [hrev, ← halg]
    exact hmem

/-- Multiplication by `ε⁻ʲ` acts on characteristics by `γʲ`; used by
`orbit_characteristic_decomposition`. -/
private theorem characteristic_inv_pow {B : PseudolatticeBasis F} {ε : K}
    (h : B.IsPeriod ε) (y : K) (j : ℕ) :
    B.characteristic ((ε⁻¹) ^ j * y) =
      ratVecAction ((h.matrix ^ j : SL(2, ℤ)) : Mat(2, ℤ)) (B.characteristic y) := by
  induction j with
  | zero => simp [ratVecAction_one]
  | succ j ih =>
      rw [pow_succ', mul_assoc, h.characteristic_inv_mul, ih, pow_succ',
        Matrix.SpecialLinearGroup.coe_mul, ratVecAction_mul]

/-- The characteristic map of a pseudolattice is injective; used by
`orbit_characteristic_decomposition`. -/
private theorem characteristic_injective (B : PseudolatticeBasis F) :
    Function.Injective B.characteristic := by
  intro y z hyz
  have h := congrArg (fun s => B.scale * fracSymplecticFormRat s B.tau) hyz
  simpa [B.fracSymplecticFormRat_characteristic, B.scale_ne_zero] using h

/-- A forward orbit over `x` remains in the same fibre when `x ∈ G_{J,ε}`; used by
`orbit_characteristic_decomposition`. -/
private theorem orbit_pow_sub_mem {B' : PseudolatticeBasis F} {ε x y : K}
    (h' : B'.IsPeriod ε) (hx : (ε - 1) * x ∈ B'.submodule)
    (hy : y - x ∈ B'.submodule) (j : ℕ) :
    ε ^ j * y - x ∈ B'.submodule := by
  induction j with
  | zero => simpa using hy
  | succ j ih =>
      have hsum := B'.submodule.add_mem (h'.mul_mem ih) hx
      convert hsum using 1
      rw [pow_succ']
      ring

/-- A full inverse turn also fixes a point modulo the pseudolattice; used by
`orbit_characteristic_decomposition`. -/
private theorem orbit_inverse_period {B : PseudolatticeBasis F} {ε y : K}
    (h : B.IsPeriod ε) {n : ℕ} (hper : ε ^ n * y - y ∈ B.submodule) :
    (ε⁻¹) ^ n * y - y ∈ B.submodule := by
  have hmem := period_inv_pow_mem h hper n
  have hcancel : (ε⁻¹) ^ n * ε ^ n = 1 := by
    rw [inv_pow]
    exact inv_mul_cancel₀ (pow_ne_zero _ h.ne_zero)
  have heq : (ε⁻¹) ^ n * (ε ^ n * y - y) = y - (ε⁻¹) ^ n * y := by
    rw [mul_sub, ← mul_assoc, hcancel, one_mul]
  have := B.submodule.neg_mem hmem
  simpa only [heq, neg_sub] using this

/-- Reverse the action of `ε⁻¹` along a finite `ε`-orbit modulo the pseudolattice. -/
private theorem orbit_forward_reverse {B B' : PseudolatticeBasis F} {ε x y : K}
    (h : B.IsPeriod ε) {Y : Finset K} {m : K → ℕ+}
    (hY : IsOrbitTransversal B.submodule B'.submodule ε x Y m)
    (hy : y ∈ Y) {j : ℕ} (hj : j < (m y : ℕ)) :
    ε ^ (orbitReverse (m y : ℕ) j) * y - (ε⁻¹) ^ j * y ∈ B.submodule := by
  have hk := orbitReverse_lt (m y).pos hj
  have h := orbit_reverse_congruent h hk (hY.period y hy)
  simpa only [orbitReverse_involutive (m y).pos hj] using h

/-- Distinct iterates of orbit representatives remain incongruent after passing to
characteristic coordinates. -/
private theorem characteristic_orbit_injective {B B' : PseudolatticeBasis F} {ε x : K}
    (h : B.IsPeriod ε) {Y : Finset K} {m : K → ℕ+}
    (hY : IsOrbitTransversal B.submodule B'.submodule ε x Y m)
    {y y' : K} (hy : y ∈ Y) (hy' : y' ∈ Y) {j j' : ℕ}
    (hj : j < (m y : ℕ)) (hj' : j' < (m y' : ℕ))
    (hdiff : IsIntegralIndex
      (ratVecAction ((h.matrix ^ j : SL(2, ℤ)) : Mat(2, ℤ)) (B.characteristic y) -
        ratVecAction ((h.matrix ^ j' : SL(2, ℤ)) : Mat(2, ℤ)) (B.characteristic y'))) :
    B.characteristic y = B.characteristic y' ∧ j = j' := by
  rw [← characteristic_inv_pow h, ← characteristic_inv_pow h,
    ← B.characteristic_sub] at hdiff
  have hdiffI := (B.isIntegralIndex_characteristic_iff _).mp hdiff
  let k := orbitReverse (m y : ℕ) j
  let k' := orbitReverse (m y' : ℕ) j'
  have hk : k < (m y : ℕ) := orbitReverse_lt (m y).pos hj
  have hk' : k' < (m y' : ℕ) := orbitReverse_lt (m y').pos hj'
  have hforward : ε ^ k * y - ε ^ k' * y' ∈ B.submodule := by
    have hh := B.submodule.sub_mem
      (orbit_forward_reverse h hY hy hj) (orbit_forward_reverse h hY hy' hj')
    convert B.submodule.add_mem hh hdiffI using 1
    ring
  obtain ⟨hyy', hkk'⟩ := hY.pow_injective y hy y' hy' k hk k' hk' hforward
  constructor
  · exact congrArg B.characteristic hyy'
  · subst y'
    have hjj' : j = j' := by
      calc
        j = orbitReverse (m y : ℕ) k := (orbitReverse_involutive (m y).pos hj).symm
        _ = orbitReverse (m y : ℕ) k' := by rw [hkk']
        _ = j' := orbitReverse_involutive (m y).pos hj'
    exact hjj'

/-- The characteristic classes of a quotient transversal carry the orbits supplied by
`IsOrbitTransversal`; used by `pseudolatticeDilog_orbit_distribution`. -/
private theorem orbit_characteristic_decomposition {B B' : PseudolatticeBasis F} {ε x : K}
    (h : B.IsPeriod ε) (h' : B'.IsPeriod ε) (hle : B.submodule ≤ B'.submodule)
    (hx : (ε - 1) * x ∈ B'.submodule) {Y : Finset K} {m : K → ℕ+}
    (hY : IsOrbitTransversal B.submodule B'.submodule ε x Y m)
    {T : Finset K} (hT : IsQuotientTransversal B.submodule B'.submodule T) :
    IsOrbitDecomposition h.matrix
      (T.image fun t => B.characteristic (x + t)) (Y.image B.characteristic)
      (fun s => m (B.scale * fracSymplecticFormRat s B.tau)) := by
  classical
  have hlift (y : K) : B.scale * fracSymplecticFormRat (B.characteristic y) B.tau = y := by
    rw [B.fracSymplecticFormRat_characteristic]
    exact mul_div_cancel₀ y B.scale_ne_zero
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hr
    rw [hlift, ← characteristic_inv_pow h, ← B.characteristic_sub]
    exact (B.isIntegralIndex_characteristic_iff _).mpr
      (orbit_inverse_period h (hY.period y hy))
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨y, hy, j, hj, hcong⟩ := hY.exists_pow (x + t) (by
      simpa only [add_sub_cancel_left] using hT.mem t ht)
    let k := orbitReverse (m y : ℕ) j
    refine ⟨B.characteristic y, Finset.mem_image.mpr ⟨y, hy, rfl⟩,
      k, by simpa only [hlift] using orbitReverse_lt (m y).pos hj, ?_⟩
    rw [← characteristic_inv_pow h, ← B.characteristic_sub]
    apply (B.isIntegralIndex_characteristic_iff _).mpr
    have hcong' := orbit_reverse_congruent h hj (hY.period y hy)
    convert B.submodule.add_mem hcong hcong' using 1
    ring
  · intro r hr j hj
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hr
    rw [hlift] at hj
    let k := orbitReverse (m y : ℕ) j
    have hk : k < (m y : ℕ) := orbitReverse_lt (m y).pos hj
    have hcong : ε ^ k * y - (ε⁻¹) ^ j * y ∈ B.submodule := orbit_forward_reverse h hY hy hj
    have hzJ : (ε⁻¹) ^ j * y - x ∈ B'.submodule := by
      have hpow := orbit_pow_sub_mem h' hx (hY.sub_mem y hy) k
      convert B'.submodule.sub_mem hpow (hle hcong) using 1
      ring
    obtain ⟨t, ht, hzt⟩ := hT.exists_mem ((ε⁻¹) ^ j * y - x) hzJ
    refine ⟨B.characteristic (x + t), Finset.mem_image.mpr ⟨t, ht, rfl⟩, ?_⟩
    rw [← characteristic_inv_pow h, ← B.characteristic_sub]
    apply (B.isIntegralIndex_characteristic_iff _).mpr
    convert B.submodule.neg_mem hzt using 1
    ring
  · intro r hr r' hr' j hj j' hj' hdiff
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hr'
    rw [hlift] at hj hj'
    exact characteristic_orbit_injective h hY hy hy' hj hj' hdiff

open scoped Classical in
/-- The zero fibre has exactly one orbit meeting `I`, and that orbit has length one; used by
`pseudolatticeDilog_orbit_distribution`. -/
private theorem IsOrbitTransversal.zero_orbit {B B' : PseudolatticeBasis F} {ε x : K}
    (h : B.IsPeriod ε) {Y : Finset K} {m : K → ℕ+}
    (hY : IsOrbitTransversal B.submodule B'.submodule ε x Y m)
    (hxJ : x ∈ B'.submodule) :
    ∃ y0 ∈ Y, y0 ∈ B.submodule ∧ (m y0 : ℕ) = 1 ∧
      ∀ y ∈ Y, y ∈ B.submodule → y = y0 := by
  obtain ⟨y0, hy0, j, hj, hcong⟩ := hY.exists_pow 0 (by
    simpa using B'.submodule.neg_mem hxJ)
  have hpow : ε ^ j * y0 ∈ B.submodule := by
    have := B.submodule.neg_mem hcong
    simpa using this
  have hy0I : y0 ∈ B.submodule := by
    have hmem := period_inv_pow_mem h hpow j
    have hcancel : (ε⁻¹) ^ j * ε ^ j = 1 := by
      rw [inv_pow]
      exact inv_mul_cancel₀ (pow_ne_zero _ h.ne_zero)
    simpa only [← mul_assoc, hcancel, one_mul] using hmem
  have hm0 : (m y0 : ℕ) = 1 := by
    by_contra hne
    have hgt : 1 < (m y0 : ℕ) := by omega
    have h01 := (hY.pow_injective y0 hy0 y0 hy0 0 (m y0).pos 1 hgt (by
      simpa using B.submodule.sub_mem hy0I (h.mul_mem hy0I))).2
    omega
  refine ⟨y0, hy0, hy0I, hm0, ?_⟩
  intro y hy hyI
  exact (hY.pow_injective y hy y0 hy0 0 (m y).pos 0 (m y0).pos (by
    simpa using B.submodule.sub_mem hyI hy0I)).1

/-- The product of the nonintegral orbit values is the eta power divided by the orbit
cocycle product; used in both fibres of `pseudolatticeDilog_orbit_distribution`. -/
private theorem orbit_nonintegral_values {B : PseudolatticeBasis F} {ε : K}
    (h : B.IsPeriod ε) {Z : Finset K} {m : K → ℕ+}
    (hZ : ∀ y ∈ Z, y ∉ B.submodule) :
    (∏ y ∈ Z, pseudolatticeDilog (h.pow (m y).pos) y) =
      etaMultiplier h.matrix ^ (∑ y ∈ Z, (m y : ℕ)) /
        ∏ y ∈ Z, sfModularCocycleReal' (B.characteristic y)
          (h.matrix ^ (m y : ℕ)) B.beta := by
  calc
    _ = ∏ y ∈ Z, etaMultiplier h.matrix ^ (m y : ℕ) /
        sfModularCocycleReal' (B.characteristic y)
          (h.matrix ^ (m y : ℕ)) B.beta := by
      apply Finset.prod_congr rfl
      intro y hy
      unfold pseudolatticeDilog
      rw [h.matrix_pow (m y).pos,
        finiteDilogValue_of_not_isIntegralIndex _ _
          ((B.isIntegralIndex_characteristic_iff y).not.mpr (hZ y hy)),
        etaMultiplier_pow_of_flt_eq_self (τ := B.tau) B.other_lt.ne
          h.flt_matrix (by
            change 1 < fltDenominator (h.matrix : Mat(2, ℤ)) B.beta
            rw [h.fltDenominator_matrix]
            exact h.one_lt) (m y : ℕ)]
    _ = _ := by rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]

open scoped Classical in
/-- On the zero fibre, removing its unique integral orbit leaves the eta-multiplier
ratio as the product of cocycle factors. -/
private theorem orbit_cocycle_zero {B B' : PseudolatticeBasis F} {ε x : K}
    (h : B.IsPeriod ε) (h' : B'.IsPeriod ε) (hle : B.submodule ≤ B'.submodule)
    (hx : (ε - 1) * x ∈ B'.submodule) {Y : Finset K} {m : K → ℕ+}
    (hY : IsOrbitTransversal B.submodule B'.submodule ε x Y m)
    (hxJ : x ∈ B'.submodule) {y0 : K} (hy0I : y0 ∈ B.submodule)
    (huniq : ∀ y ∈ Y, y ∈ B.submodule → y = y0) :
    (∏ y ∈ Y.erase y0,
      sfModularCocycleReal' (B.characteristic y) (h.matrix ^ (m y : ℕ)) B.beta) =
        etaMultiplier h'.matrix / etaMultiplier h.matrix := by
  classical
  obtain ⟨T, hT⟩ := B.exists_isQuotientTransversal hle
  obtain ⟨M, hdet, hM⟩ := B.exists_inclusionMatrix hle
  let S := T.image fun t => B.characteristic (x + t)
  let R := Y.image B.characteristic
  let mR : (Fin 2 → ℚ) → ℕ+ :=
    fun s => m (B.scale * fracSymplecticFormRat s B.tau)
  have hlift (y : K) : B.scale * fracSymplecticFormRat (B.characteristic y) B.tau = y := by
    rw [B.fracSymplecticFormRat_characteristic]
    exact mul_div_cancel₀ y B.scale_ne_zero
  have hS : IsPreimageTransversal M (B'.characteristic x) S :=
    characteristic_preimageTransversal hdet hM hT x
  have hR : IsOrbitDecomposition h.matrix S R mR :=
    orbit_characteristic_decomposition h h' hle hx hY hT
  let f : ℕ := M.det.toNat
  have hf : 0 < f := by omega
  have hGf : M ∈ Gf (f : ℤ) := mem_Gf_det_toNat hdet
  have hjC : 0 < fltDenominator (h.matrix : Mat(2, ℤ)) B.beta :=
    zero_lt_one.trans h.isAttractiveFixedPoint.one_lt_fltDenominator
  have hYfilter : (Y.filter fun y => y ∉ B.submodule) = Y.erase y0 := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hy, hnon⟩
      exact ⟨fun heq => hnon (heq ▸ hy0I), hy⟩
    · rintro ⟨hne, hy⟩
      exact ⟨hy, fun hyI => hne (huniq y hy hyI)⟩
  have hRfilter : (R.filter fun r => ¬ IsIntegralIndex r) =
      (Y.erase y0).image B.characteristic := by
    rw [Finset.filter_image]
    change (Y.filter fun y => ¬ IsIntegralIndex (B.characteristic y)).image
      B.characteristic = (Y.erase y0).image B.characteristic
    simp only [B.isIntegralIndex_characteristic_iff, hYfilter]
  have hrJ := (B'.isIntegralIndex_characteristic_iff x).mpr hxJ
  have hS0 : IsPreimageTransversal M 0 S :=
    hS.of_isIntegralIndex_sub (by simpa only [sub_zero] using hrJ)
  have hrel := prod_sfModularCocycleReal'_orbits_preimage_zero hf hGf
    (h.inclusionMatrix_mul h' hM) B.beta_irrational h.flt_matrix hjC
    (B.fltDenominator_pos_of_inclusion hdet hM) hS0 hR.nonintegral
  rw [hRfilter, Finset.prod_image (characteristic_injective B).injOn] at hrel
  simpa only [mR, hlift] using hrel

/-- On a nonzero fibre, the conductor relation gives the product of its cocycle
factors. -/
private theorem orbit_cocycle_nonzero {B B' : PseudolatticeBasis F} {ε x : K}
    (h : B.IsPeriod ε) (h' : B'.IsPeriod ε) (hle : B.submodule ≤ B'.submodule)
    (hx : (ε - 1) * x ∈ B'.submodule) {Y : Finset K} {m : K → ℕ+}
    (hY : IsOrbitTransversal B.submodule B'.submodule ε x Y m)
    (hxJ : x ∉ B'.submodule) :
    sfModularCocycleReal' (B'.characteristic x) h'.matrix B'.beta =
      ∏ y ∈ Y, sfModularCocycleReal' (B.characteristic y)
        (h.matrix ^ (m y : ℕ)) B.beta := by
  classical
  obtain ⟨T, hT⟩ := B.exists_isQuotientTransversal hle
  obtain ⟨M, hdet, hM⟩ := B.exists_inclusionMatrix hle
  let S := T.image fun t => B.characteristic (x + t)
  let R := Y.image B.characteristic
  let mR : (Fin 2 → ℚ) → ℕ+ :=
    fun s => m (B.scale * fracSymplecticFormRat s B.tau)
  have hlift (y : K) : B.scale * fracSymplecticFormRat (B.characteristic y) B.tau = y := by
    rw [B.fracSymplecticFormRat_characteristic]
    exact mul_div_cancel₀ y B.scale_ne_zero
  have hS : IsPreimageTransversal M (B'.characteristic x) S :=
    characteristic_preimageTransversal hdet hM hT x
  have hR : IsOrbitDecomposition h.matrix S R mR :=
    orbit_characteristic_decomposition h h' hle hx hY hT
  let f : ℕ := M.det.toNat
  have hf : 0 < f := by omega
  have hGf : M ∈ Gf (f : ℤ) := mem_Gf_det_toNat hdet
  have hjC : 0 < fltDenominator (h.matrix : Mat(2, ℤ)) B.beta :=
    zero_lt_one.trans h.isAttractiveFixedPoint.one_lt_fltDenominator
  have hrJ := (B'.isIntegralIndex_characteristic_iff x).not.mpr hxJ
  have hA := (h'.mem_gammaSubgroup_characteristic_iff x).mpr hx
  have hrel := sfModularCocycleRealTotal_eq_prod_orbits_of_mem_Gf hf hGf hrJ
    (h.inclusionMatrix_mul h' hM) hA B.beta_irrational h.flt_matrix hjC
    (B.fltDenominator_pos_of_inclusion hdet hM) hS hR
  rw [← B.beta_eq_flt_of_inclusion hdet hM,
    ← sfModularCocycleReal'_of_mem hA B'.beta] at hrel
  rw [Finset.prod_image (characteristic_injective B).injOn] at hrel
  simpa only [R, mR, hlift] using hrel

/-- **The orbit distribution relation** [RW26b, Radchenko, Wheeler (2026b), Proposition 3(i),
equation (10)]: for pseudolattices `I ⊆ J` with a common period `ε`, `x ∈ G_{J,ε}`, and orbit
representatives `Y = ℛ_x` of the fibre over `x` with lengths `m(y) = r_y`,

$$\frac{\mu_{I,\varepsilon}^{d}}{\mu_{J,\varepsilon}}\,E_{J,\varepsilon}(x)
  = \prod_{y\in\mathcal R_x} E_{I,\varepsilon^{r_y}}(y),\qquad d = \sum_{y} r_y = |J/I|.$$ -/
@[source "RW26b, Proposition 3, p. 4 (i, equation (10))"]
theorem pseudolatticeDilog_orbit_distribution {B B' : PseudolatticeBasis F} {ε : K}
    (h : B.IsPeriod ε) (h' : B'.IsPeriod ε) (hle : B.submodule ≤ B'.submodule) {x : K}
    (hx : (ε - 1) * x ∈ B'.submodule) {Y : Finset K} {m : K → ℕ+}
    (hY : IsOrbitTransversal B.submodule B'.submodule ε x Y m) :
    etaMultiplier h.matrix ^ (∑ y ∈ Y, (m y : ℕ)) / etaMultiplier h'.matrix *
        pseudolatticeDilog h' x =
      ∏ y ∈ Y, pseudolatticeDilog (h.pow (m y).pos) y := by
  classical
  by_cases hxJ : x ∈ B'.submodule
  · obtain ⟨y0, hy0, hy0I, hm0, huniq⟩ := hY.zero_orbit h hxJ
    have hprodC := orbit_cocycle_zero h h' hle hx hY hxJ hy0I huniq
    have hyI : ∀ y ∈ Y.erase y0, y ∉ B.submodule := by
      intro y hy hyI
      exact (Finset.mem_erase.mp hy).1 (huniq y (Finset.mem_erase.mp hy).2 hyI)
    have hEY := orbit_nonintegral_values h (m := m) hyI
    have hsum : (∑ y ∈ Y, (m y : ℕ)) =
        (∑ y ∈ Y.erase y0, (m y : ℕ)) + 1 := by
      calc
        _ = (∑ y ∈ Y.erase y0, (m y : ℕ)) + (m y0 : ℕ) :=
          (Finset.sum_erase_add Y (fun y => (m y : ℕ)) hy0).symm
        _ = _ := by rw [hm0]
    have hval0 : pseudolatticeDilog (h.pow (m y0).pos) y0 =
        (Real.sqrt ((realEmbeddingAt K F.place) ε) : ℂ) := by
      rw [pseudolatticeDilog_of_mem (h.pow (m y0).pos) hy0I]
      simp only [hm0, pow_one]
    rw [← Finset.prod_erase_mul Y (fun y => pseudolatticeDilog (h.pow (m y).pos) y)
      hy0, hEY, hval0, pseudolatticeDilog_of_mem h' hxJ, hprodC, hsum, pow_succ]
    field_simp [etaMultiplier_ne_zero h.matrix, etaMultiplier_ne_zero h'.matrix]
  · have hrJ := (B'.isIntegralIndex_characteristic_iff x).not.mpr hxJ
    have hprodC := orbit_cocycle_nonzero h h' hle hx hY hxJ
    have hyI : ∀ y ∈ Y, y ∉ B.submodule := by
      intro y hy hyI
      apply hxJ
      have := hY.sub_mem y hy
      have hyJ := hle hyI
      convert B'.submodule.sub_mem hyJ this using 1
      ring
    have hEY := orbit_nonintegral_values h (m := m) hyI
    have hEJ : pseudolatticeDilog h' x =
        etaMultiplier h'.matrix /
          sfModularCocycleReal' (B'.characteristic x) h'.matrix B'.beta :=
      finiteDilogValue_of_not_isIntegralIndex h'.matrix B'.beta hrJ
    rw [hEY, hEJ, hprodC]
    field_simp [etaMultiplier_ne_zero h'.matrix]

open scoped Classical in
/-- Under `(ε - 1)J ⊆ I`, translates of a quotient transversal are length-one orbit
representatives; used by `pseudolatticeDilog_distribution`. -/
private theorem IsQuotientTransversal.orbit_one {B B' : PseudolatticeBasis F} {ε x : K}
    (hJ : ∀ y ∈ B'.submodule, (ε - 1) * y ∈ B.submodule)
    {T : Finset K} (hT : IsQuotientTransversal B.submodule B'.submodule T)
    (hx : (ε - 1) * x ∈ B.submodule) :
    IsOrbitTransversal B.submodule B'.submodule ε x (T.image (x + ·))
      (fun _ : K => (1 : ℕ+)) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
    simpa only [add_sub_cancel_left] using hT.mem t ht
  · intro y hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
    have hsum := B.submodule.add_mem hx (hJ t (hT.mem t ht))
    convert hsum using 1
    norm_num
    ring
  · intro z hz
    obtain ⟨t, ht, hzt⟩ := hT.exists_mem (z - x) hz
    refine ⟨x + t, Finset.mem_image.mpr ⟨t, ht, rfl⟩, 0, by simp, ?_⟩
    simpa only [pow_zero, one_mul] using (by convert hzt using 1; ring :
      z - (x + t) ∈ B.submodule)
  · intro y hy y' hy' j hj j' hj' hcong
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp hy'
    have hj0 : j = 0 := by simpa using hj
    have hj'0 : j' = 0 := by simpa using hj'
    subst j
    subst j'
    have htt : t - t' ∈ B.submodule := by
      convert hcong using 1; simp
    exact ⟨congrArg (x + ·) (hT.eq_of_sub_mem t ht t' ht' htt), rfl⟩

/-- **The distribution relation** [RW26b, Radchenko, Wheeler (2026b), Proposition 3(ii),
equation (11)]: for pseudolattices `I ⊆ J` with `(ε - 1)J ⊆ I`, a period `ε` of `I`, a set `T` of
representatives of `H = J/I`, and `x ∈ G_{I,ε}`,

$$\frac{\mu_{I,\varepsilon}^{|H|}}{\mu_{J,\varepsilon}}\,E_{J,\varepsilon}(x)
  = \prod_{t\in T} E_{I,\varepsilon}(x+t).$$

The source defines `J` from the subgroup `H`; here `J` is given with an admissible basis, and the
clause that `J` is stabilized by `ε` is `PseudolatticeBasis.IsPeriod.of_le`. -/
@[source "RW26b, Proposition 3, p. 4 (ii, equation (11))"]
theorem pseudolatticeDilog_distribution {B B' : PseudolatticeBasis F} {ε : K}
    (h : B.IsPeriod ε) (hle : B.submodule ≤ B'.submodule)
    (hJ : ∀ y ∈ B'.submodule, (ε - 1) * y ∈ B.submodule) {T : Finset K}
    (hT : IsQuotientTransversal B.submodule B'.submodule T) {x : K}
    (hx : (ε - 1) * x ∈ B.submodule) :
    let h' := h.of_le hle hJ
    etaMultiplier h.matrix ^ T.card / etaMultiplier h'.matrix * pseudolatticeDilog h' x =
      ∏ t ∈ T, pseudolatticeDilog h (x + t) := by
  classical
  let h' := h.of_le hle hJ
  let Y := T.image (x + ·)
  let m : K → ℕ+ := fun _ => 1
  have hY : IsOrbitTransversal B.submodule B'.submodule ε x Y m :=
    hT.orbit_one hJ hx
  have horbit := pseudolatticeDilog_orbit_distribution h h' hle (hle hx) hY
  have hinj : Set.InjOn (x + ·) T := fun t _ u _ heq => add_left_cancel heq
  rw [Finset.sum_image hinj, Finset.prod_image hinj] at horbit
  have hsum : (∑ t ∈ T, (m (x + t) : ℕ)) = T.card := by simp [m]
  rw [hsum] at horbit
  convert horbit using 1
  apply Finset.prod_congr rfl
  intro t ht
  have hxt : (ε - 1) * (x + t) ∈ B.submodule := by
    have hsum := B.submodule.add_mem hx (hJ t (hT.mem t ht))
    convert hsum using 1; ring
  change pseudolatticeDilog h (x + t) = pseudolatticeDilog (h.pow one_pos) (x + t)
  rw [pseudolatticeDilog_pow_period h one_pos hxt, pow_one]

end SIC
