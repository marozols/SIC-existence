/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Dilogarithm.Pseudolattice.Basic

/-!
# The Group `G_{I,ε}` of a Pseudolattice as Fixed Characteristics

The residue map from `(ε - 1)⁻¹I` onto the finite group `G = fixedCharacteristics γ N`,
`N = Tr ε - 2`, additive with kernel `I`, and the pseudolattice dilogarithm and Gaussian as the
group-level values `E` and `⟨x⟩` at the residue.

This module follows [RW26b, Radchenko, Wheeler (2026b), Section 3, Definition 1]: the group
`G_{I,ε} = (ε - 1)⁻¹I/I` of order `N = Tr ε - 2` on which `E_{I,ε}` lives. It supplies the finite
abelian group on which the Fourier analysis of [RW26b, Radchenko, Wheeler (2026b), Section 4]
takes place: every function of `x ∈ (ε - 1)⁻¹I` modulo `I` is a function on
`finiteDilogGroup γ`.

## The argument

For `x ∈ K` with `(ε - 1)x ∈ I`, the characteristic `r` of `x` satisfies `γ ∈ Γ_r`
(`IsPeriod.mem_gammaSubgroup_characteristic_iff`), i.e. `k = (γ - I)r ∈ ℤ²`; since
`det(γ - I) = -N` (`det_sub_one_eq_neg_finiteDilogOrder`), `Nr = -adj(γ - I)k ∈ ℤ²`. The
residue of `x` is `Nr mod N ∈ (ℤ/Nℤ)²`, whose lift `zmodCharacteristic` differs from `r` by an
integer vector; so it lies in `G` (`mem_finiteDilogGroup_iff`), the map is additive, its kernel
is `I` (`isIntegralIndex_characteristic_iff`), and it is onto `G` because every residue vector
`y ∈ G` is the residue of `x = β₂⟨⟨y/N, τ⟩⟩`. The values transport by the `ℤ²`-periodicity of
`finiteDilogValue` (`finiteDilogValue_congr`) and of the theta character
(`thetaCharacter_add_of_isIntegralIndex`).
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
variable {F : RealQuadraticFieldData K} {B : PseudolatticeBasis F} {ε : K}

namespace PseudolatticeBasis.IsPeriod

variable (h : B.IsPeriod ε)

/-! ### The residue map

`x ↦ Nr mod N` for the characteristic `r` of `x`, meaningful for `(ε - 1)x ∈ I`. -/

/-- **The residue of `x ∈ (ε - 1)⁻¹I` in `G_{I,ε}`** [RW26b, Radchenko, Wheeler (2026b),
Definition 1]: the residue vector `Nr mod N ∈ (ℤ/Nℤ)²` of the characteristic `r` of `x`,
`N = Tr ε - 2`, which is integral for `(ε - 1)x ∈ I`; it is the class of `x` in
`G_{I,ε} = (ε - 1)⁻¹I/I` as an element of `finiteDilogGroup γ`. Total in `x` through the floor
of `Nr`; every law below assumes `(ε - 1)x ∈ I`. -/
def residue (x : K) : Fin 2 → ZMod (finiteDilogOrder h.matrix) :=
  fun i => ((⌊(finiteDilogOrder h.matrix : ℚ) * B.characteristic x i⌋ : ℤ) : ZMod _)

/-- **`Nr ∈ ℤ²` for `(ε - 1)x ∈ I`**: `γ ∈ Γ_r` gives `k = (γ - I)r ∈ ℤ²` and
`Nr = -adj(γ - I)k` (`det_sub_one_eq_neg_finiteDilogOrder`). -/
theorem isIntegralIndex_order_mul_characteristic {x : K} (hx : (ε - 1) * x ∈ B.submodule) :
    IsIntegralIndex (fun i => (finiteDilogOrder h.matrix : ℚ) * B.characteristic x i) := by
  let M : Mat(2, ℤ) := (h.matrix : Mat(2, ℤ)) - 1
  let r := B.characteristic x
  obtain ⟨k₀, hk₀⟩ := ratVecAction_sub_intVec_of_mem_gammaSubgroup
    ((h.mem_gammaSubgroup_characteristic_iff x).mpr hx) 0
  obtain ⟨k₁, hk₁⟩ := ratVecAction_sub_intVec_of_mem_gammaSubgroup
    ((h.mem_gammaSubgroup_characteristic_iff x).mpr hx) 1
  have h₀ : (M 0 0 : ℚ) * r 0 + (M 0 1 : ℚ) * r 1 = k₀ := by
    simp only [M, r, ratVecAction, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply] at hk₀ ⊢
    push_cast at hk₀ ⊢
    linear_combination hk₀
  have h₁ : (M 1 0 : ℚ) * r 0 + (M 1 1 : ℚ) * r 1 = k₁ := by
    simp only [M, r, ratVecAction, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply] at hk₁ ⊢
    push_cast at hk₁ ⊢
    linear_combination hk₁
  have hdet : (M 0 0 : ℚ) * M 1 1 - (M 0 1 : ℚ) * M 1 0 =
      -(finiteDilogOrder h.matrix : ℚ) := by
    have hd := det_sub_one_eq_neg_finiteDilogOrder h.isAttractiveFixedPoint
    rw [Matrix.det_fin_two] at hd
    exact_mod_cast hd
  intro i
  fin_cases i
  · refine ⟨-(M 1 1 * k₀) + M 0 1 * k₁, ?_⟩
    dsimp only
    push_cast
    linear_combination (M 0 1 : ℚ) * h₁ - (M 1 1 : ℚ) * h₀ + r 0 * hdet
  · refine ⟨M 1 0 * k₀ - M 0 0 * k₁, ?_⟩
    dsimp only
    push_cast
    linear_combination (M 1 0 : ℚ) * h₀ - (M 0 0 : ℚ) * h₁ + r 1 * hdet

/-- The lift of the residue differs from the characteristic by an integer vector
(`isIntegralIndex_zmodCharacteristic_intCast_sub`). -/
theorem isIntegralIndex_zmodCharacteristic_residue_sub {x : K}
    (hx : (ε - 1) * x ∈ B.submodule) :
    IsIntegralIndex
      (zmodCharacteristic (finiteDilogOrder h.matrix) (h.residue x) - B.characteristic x) := by
  let N := finiteDilogOrder h.matrix
  have : NeZero N := finiteDilogOrder_neZero h.isAttractiveFixedPoint
  choose k hk using h.isIntegralIndex_order_mul_characteristic hx
  have hres : h.residue x = fun i => (k i : ZMod N) := by
    funext i
    simp only [residue]
    have hki := hk i
    change (N : ℚ) * B.characteristic x i = (k i : ℚ) at hki
    rw [hki, Int.floor_intCast]
  have hq : (fun i => (k i : ℚ) / N) = B.characteristic x := by
    funext i
    have hn : (N : ℚ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
    have hki := hk i
    change (N : ℚ) * B.characteristic x i = (k i : ℚ) at hki
    simp only [← hki]
    field_simp
  simpa only [hres, hq] using isIntegralIndex_zmodCharacteristic_intCast_sub N k

/-- The residue lies in `G` (`mem_finiteDilogGroup_iff`, `mem_gammaSubgroup_of_isIntegralIndex`
through the lift). -/
theorem residue_mem {x : K} (hx : (ε - 1) * x ∈ B.submodule) :
    h.residue x ∈ finiteDilogGroup h.matrix := by
  apply (mem_finiteDilogGroup_iff h.isAttractiveFixedPoint _).mpr
  exact mem_gammaSubgroup_of_isIntegralIndex_sub
    (h.isIntegralIndex_zmodCharacteristic_residue_sub hx)
    ((h.mem_gammaSubgroup_characteristic_iff x).mpr hx)

/-- `residue 0 = 0`. -/
@[simp]
theorem residue_zero : h.residue 0 = 0 := by
  funext i
  simp [residue]

/-- The residue is additive on `(ε - 1)⁻¹I` (`characteristic_add`, the floor of a sum of
integers). -/
theorem residue_add {x y : K} (hx : (ε - 1) * x ∈ B.submodule) (hy : (ε - 1) * y ∈ B.submodule) :
    h.residue (x + y) = h.residue x + h.residue y := by
  funext i
  obtain ⟨a, ha⟩ := h.isIntegralIndex_order_mul_characteristic hx i
  obtain ⟨b, hb⟩ := h.isIntegralIndex_order_mul_characteristic hy i
  change (finiteDilogOrder h.matrix : ℚ) * B.characteristic x i = (a : ℚ) at ha
  change (finiteDilogOrder h.matrix : ℚ) * B.characteristic y i = (b : ℚ) at hb
  simp only [residue, Pi.add_apply, B.characteristic_add, mul_add]
  rw [ha, hb, ← Int.cast_add, Int.floor_intCast]
  simp

/-- `residue (-x) = -residue x` on `(ε - 1)⁻¹I` (`characteristic_neg`). -/
theorem residue_neg {x : K} (hx : (ε - 1) * x ∈ B.submodule) :
    h.residue (-x) = -h.residue x := by
  funext i
  obtain ⟨a, ha⟩ := h.isIntegralIndex_order_mul_characteristic hx i
  change (finiteDilogOrder h.matrix : ℚ) * B.characteristic x i = (a : ℚ) at ha
  simp only [residue, Pi.neg_apply, B.characteristic_neg, mul_neg]
  rw [ha, ← Int.cast_neg, Int.floor_intCast]
  simp

/-- **The kernel of the residue is `I`**: `residue x = 0 ↔ x ∈ I` for `(ε - 1)x ∈ I`
(`isIntegralIndex_characteristic_iff`, `isIntegralIndex_zmodCharacteristic_iff`). -/
theorem residue_eq_zero_iff {x : K} (hx : (ε - 1) * x ∈ B.submodule) :
    h.residue x = 0 ↔ x ∈ B.submodule := by
  rw [← B.isIntegralIndex_characteristic_iff]
  have : NeZero (finiteDilogOrder h.matrix) :=
    finiteDilogOrder_neZero h.isAttractiveFixedPoint
  exact ((isIntegralIndex_zmodCharacteristic_iff _ (h.residue x)).symm).trans
    (isIntegralIndex_iff_of_isIntegralIndex_sub
      (h.isIntegralIndex_zmodCharacteristic_residue_sub hx))

/-- Two elements of `(ε - 1)⁻¹I` have the same residue iff they agree modulo `I`
(`residue_add`, `residue_neg`, `residue_eq_zero_iff`). -/
theorem residue_eq_iff {x y : K} (hx : (ε - 1) * x ∈ B.submodule)
    (hy : (ε - 1) * y ∈ B.submodule) :
    h.residue x = h.residue y ↔ x - y ∈ B.submodule := by
  have hsub : (ε - 1) * (x - y) ∈ B.submodule := by
    simpa only [mul_sub] using B.submodule.sub_mem hx hy
  have hneg : (ε - 1) * (-y) ∈ B.submodule := by
    simpa only [mul_neg] using B.submodule.neg_mem hy
  have hr : h.residue (x - y) = h.residue x - h.residue y := by
    rw [sub_eq_add_neg, h.residue_add hx hneg, h.residue_neg hy, sub_eq_add_neg]
  rw [← h.residue_eq_zero_iff hsub, hr, sub_eq_zero]

/-- **The residue map is onto `G`**: every `y ∈ G` is the residue of `x = β₂⟨⟨y/N, τ⟩⟩`, whose
characteristic is the lift of `y` (`characteristic_eq_of_eq`) and which lies in `(ε - 1)⁻¹I`
(`mem_finiteDilogGroup_iff`, `mem_gammaSubgroup_characteristic_iff`). -/
theorem exists_residue_eq {y : Fin 2 → ZMod (finiteDilogOrder h.matrix)}
    (hy : y ∈ finiteDilogGroup h.matrix) :
    ∃ x : K, (ε - 1) * x ∈ B.submodule ∧ h.residue x = y := by
  let r := zmodCharacteristic (finiteDilogOrder h.matrix) y
  let x := B.scale * fracSymplecticFormRat r B.tau
  have hc : B.characteristic x = r := B.characteristic_scale_fracSymplecticFormRat r
  have hx : (ε - 1) * x ∈ B.submodule := by
    apply (h.mem_gammaSubgroup_characteristic_iff x).mp
    rw [hc]
    exact (mem_finiteDilogGroup_iff h.isAttractiveFixedPoint y).mp hy
  refine ⟨x, hx, ?_⟩
  have : NeZero (finiteDilogOrder h.matrix) :=
    finiteDilogOrder_neZero h.isAttractiveFixedPoint
  apply eq_of_isIntegralIndex_zmodCharacteristic_sub (finiteDilogOrder h.matrix)
  simpa only [hc, r] using h.isIntegralIndex_zmodCharacteristic_residue_sub hx

end PseudolatticeBasis.IsPeriod

/-! ### The values at the residue

`E_{I,ε}(x)` and `⟨x⟩` are the group-level values `E` and `⟨·⟩` of `SICs.Dilogarithm.Values` and
`SICs.SL2Z.TorsionCharacteristics` at the residue. -/

variable (h : B.IsPeriod ε)

/-- **`E_{I,ε}(x) = E(residue x)`**: the pseudolattice dilogarithm is the group-level value
`finiteDilogE` at the residue (`finiteDilogValue_congr`,
`isIntegralIndex_zmodCharacteristic_residue_sub`); the identification of
[RW26b, Radchenko, Wheeler (2026b), Definition 1] with [RW26, Radchenko, Wheeler (2026),
Section 4.3, `prop:rqffinitedilog`]. -/
theorem pseudolatticeDilog_eq_finiteDilogE {x : K} (hx : (ε - 1) * x ∈ B.submodule) :
    pseudolatticeDilog h x = finiteDilogE h.matrix B.beta (h.residue x) := by
  exact (finiteDilogValue_congr h.isAttractiveFixedPoint
    ((h.mem_gammaSubgroup_characteristic_iff x).mpr hx)
    (h.isIntegralIndex_zmodCharacteristic_residue_sub hx)).symm

/-- **`⟨x⟩_{I,ε} = ⟨residue x⟩`**: the Gaussian of [RW26b, Radchenko, Wheeler (2026b),
equation (2)] is `fixedGaussian` at the residue (`thetaCharacter_add_of_isIntegralIndex`). -/
theorem pseudolatticeGaussian_eq_fixedGaussian {x : K} (hx : (ε - 1) * x ∈ B.submodule) :
    pseudolatticeGaussian h x =
      fixedGaussian h.matrix (finiteDilogOrder h.matrix) (h.residue x) := by
  let r := B.characteristic x
  let t := zmodCharacteristic (finiteDilogOrder h.matrix) (h.residue x)
  have he : IsIntegralIndex (t - r) := h.isIntegralIndex_zmodCharacteristic_residue_sub hx
  have hindex : r + (t - r) = t := by abel
  change thetaCharacter r _ = thetaCharacter t _
  rw [← hindex, thetaCharacter_add_of_isIntegralIndex h.matrix
    ((h.mem_gammaSubgroup_characteristic_iff x).mpr hx) he]

end SIC

end
