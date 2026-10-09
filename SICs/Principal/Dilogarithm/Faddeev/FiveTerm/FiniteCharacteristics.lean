/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Dilogarithm.Faddeev.Cocycle
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.FiniteParameters
import SICs.Principal.Dilogarithm.UnitAction

/-!
# Finite characteristics for the principal five-term parameters

The source integer parameters cover every class of `G_d`, give its finite dilogarithm values, and
admit a residue-preserving transport that shifts the controlling index.

This module follows [RW26, Radchenko, Wheeler (2026), equation (2), `eq:fgam.def`, Section 3.2,
and Lemma 2, `lem:lam.inv`].

## The argument

For a source pair `u=(u₁,u₂)`, put `k=(-u₂,u₁)`. Its residue is the existing lattice coordinate
`principalDilogOfLattice d k`, and its rational characteristic is `r=-adj(A_d-I)k/N`.
Thus `(A_d-I)r=k`, the cocycle index is `-u₁`, and evaluation of the fractional symplectic form
at the fixed point `ρ_d` is the source argument `z_u`. The integral difference between this
characteristic and its canonical residue lift transfers the cocycle value to the finite
dilogarithm. Away from the zero class, this gives the raw principal Faddeev product at indices
`(u₁,0)`.

The source transport `(u₁,u₂) ↦ (u₁-dk,u₂+dk)` preserves the residue and changes the controlling
index by `d(d-3)k`, so integer division moves the index of a representative into any half-open
interval of width `d(d-3)`.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### Source characteristic dictionary

The source numerator `u₁ρ_d+u₂` corresponds to the lattice coordinate `(-u₂,u₁)`.
General characteristic duality supplies its rational lift, action equation, and surjectivity onto
the fixed group. Evaluating the action equation at the fixed point identifies its symplectic
argument and cocycle index with the source parameters.
-/

/-- The residue of the source pair `(u₁,u₂)`, with lattice coordinate `(-u₂,u₁)` as in
[RW26, Radchenko, Wheeler (2026), equation (2), `eq:fgam.def`, and Section 3.2]. -/
abbrev principalFiveTermCharacteristicResidue (d : ℕ) (u₁ u₂ : ℤ) :
    Fin 2 → ZMod (principalDilogOrder d) :=
  principalDilogOfLattice d ![-u₂, u₁]

/-- The rational characteristic `-adj(A_d-I)(-u₂,u₁)/N` lifting the source residue. -/
def principalFiveTermRationalCharacteristic (d : ℕ) (u₁ u₂ : ℤ) : Fin 2 → ℚ :=
  latticeCharacteristicLift (principalA d) (principalDilogOrder d) ![-u₂, u₁]

/-- The source residue is additive in the pair, since `principalDilogOfLattice` is linear
(`principalDilogOfLattice_apply`). -/
theorem principalFiveTermCharacteristicResidue_add (d : ℕ) (u₁ u₂ v₁ v₂ : ℤ) :
    principalFiveTermCharacteristicResidue d (u₁ + v₁) (u₂ + v₂) =
      principalFiveTermCharacteristicResidue d u₁ u₂ +
        principalFiveTermCharacteristicResidue d v₁ v₂ := by
  funext i
  fin_cases i <;>
    simp only [principalFiveTermCharacteristicResidue, principalDilogOfLattice_apply,
      Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  all_goals push_cast; ring

/-- Subtracting source pairs subtracts their residue vectors. -/
theorem principalFiveTermCharacteristicResidue_sub (d : ℕ) (m k m' k' : ℤ) :
    principalFiveTermCharacteristicResidue d (m - m') (k - k') =
      principalFiveTermCharacteristicResidue d m k -
        principalFiveTermCharacteristicResidue d m' k' := by
  funext i
  fin_cases i <;>
    simp only [principalFiveTermCharacteristicResidue, principalDilogOfLattice_apply,
      Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  all_goals push_cast; ring

/-- The lattice argument is additive in the pair. -/
theorem principalFiveTermLatticeArgument_add (d : ℕ) (u₁ u₂ v₁ v₂ : ℤ) :
    principalFiveTermLatticeArgument d (u₁ + v₁) (u₂ + v₂) =
      principalFiveTermLatticeArgument d u₁ u₂ + principalFiveTermLatticeArgument d v₁ v₂ := by
  unfold principalFiveTermLatticeArgument
  push_cast
  ring

/-- Every source residue belongs to the principal finite group `G_d`. -/
theorem principalFiveTermCharacteristicResidue_mem (d : ℕ) (hd : 3 < d) (u₁ u₂ : ℤ) :
    principalFiveTermCharacteristicResidue d u₁ u₂ ∈ principalDilogGroup d := by
  exact principalDilogOfLattice_mem d hd ![-u₂, u₁]

/-- Every class of `G_d` is represented by a source integer pair. -/
theorem exists_characteristicResidue_eq (d : ℕ) (hd : 3 < d)
    {x : Fin 2 → ZMod (principalDilogOrder d)} (hx : x ∈ principalDilogGroup d) :
    ∃ u₁ u₂ : ℤ, principalFiveTermCharacteristicResidue d u₁ u₂ = x := by
  let _ : NeZero (principalDilogOrder d) := principalDilogOrder_neZero d hd
  obtain ⟨k, hk⟩ := exists_latticeCharacteristic_eq
    (principalA d) (principalDilogOrder d) (det_principalA_sub_one d hd) hx
  refine ⟨k 1, -k 0, ?_⟩
  rw [principalFiveTermCharacteristicResidue, show ![-(-k 0), k 1] = k by
    funext i
    fin_cases i <;> simp]
  exact hk

/-- The source lift satisfies `(A_d-I)r=(-u₂,u₁)`. -/
theorem ratVecAction_rationalCharacteristic_sub (d : ℕ) (hd : 3 < d) (u₁ u₂ : ℤ) :
    ratVecAction (principalA d : Mat(2, ℤ)) (principalFiveTermRationalCharacteristic d u₁ u₂) -
      principalFiveTermRationalCharacteristic d u₁ u₂ = fun i => (![(-u₂ : ℤ), u₁] i : ℚ) := by
  let _ : NeZero (principalDilogOrder d) := principalDilogOrder_neZero d hd
  exact ratVecAction_latticeCharacteristicLift_sub
    (principalA d) (principalDilogOrder d) (det_principalA_sub_one d hd) ![-u₂, u₁]

/-- The principal matrix fixes the source rational characteristic modulo `ℤ²`. -/
theorem principalA_mem_gammaSubgroup_characteristic
    (d : ℕ) (hd : 3 < d) (u₁ u₂ : ℤ) :
    principalA d ∈ gammaSubgroup (principalFiveTermRationalCharacteristic d u₁ u₂) := by
  apply mem_gammaSubgroup_of_isIntegralIndex
  rw [ratVecAction_rationalCharacteristic_sub d hd]
  intro i
  exact ⟨![-u₂, u₁] i, rfl⟩

/-- The canonical lift of the source residue differs integrally from its rational
characteristic. -/
theorem isIntegralIndex_characteristicResidue_sub
    (d : ℕ) (hd : 3 < d) (u₁ u₂ : ℤ) :
    IsIntegralIndex
      (zmodCharacteristic (principalDilogOrder d) (principalFiveTermCharacteristicResidue d u₁ u₂) -
        principalFiveTermRationalCharacteristic d u₁ u₂) := by
  let _ : NeZero (principalDilogOrder d) := principalDilogOrder_neZero d hd
  exact isIntegralIndex_latticeCharacteristic_sub_lift
    (principalA d) (principalDilogOrder d) ![-u₂, u₁]

/-- The cocycle index of the source characteristic is `n_QP(r,A_d)=-u₁`. -/
theorem nQPInt_principalFiveTermRationalCharacteristic (d : ℕ) (hd : 3 < d) (u₁ u₂ : ℤ) :
    nQPInt (principalFiveTermRationalCharacteristic d u₁ u₂) (principalA d : Mat(2, ℤ)) = -u₁ := by
  have hcast := nQPInt_cast_of_mem
    (principalA_mem_gammaSubgroup_characteristic d hd u₁ u₂)
  have hcoord := congrFun (ratVecAction_rationalCharacteristic_sub d hd u₁ u₂) 1
  simp only [Pi.sub_apply] at hcoord
  have hnq : nQP (principalFiveTermRationalCharacteristic d u₁ u₂) (principalA d : Mat(2, ℤ)) =
      -(ratVecAction (principalA d : Mat(2, ℤ))
          (principalFiveTermRationalCharacteristic d u₁ u₂) 1 -
        principalFiveTermRationalCharacteristic d u₁ u₂ 1) := by
    simp [nQP, ratVecAction, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  rw [hnq, hcoord] at hcast
  have hcast' :
      ((nQPInt (principalFiveTermRationalCharacteristic d u₁ u₂)
        (principalA d : Mat(2, ℤ)) : ℤ) : ℚ) =
        ((-u₁ : ℤ) : ℚ) := by
    simpa only [Matrix.cons_val_one, Matrix.cons_val_fin_one, Int.cast_neg] using hcast
  exact (Int.cast_injective : Function.Injective (fun z : ℤ => (z : ℚ))) hcast'

/-- Source transport shifts the rational characteristic by the integer vector
`k(1,d-1)`. -/
theorem principalFiveTermRationalCharacteristic_transport (d : ℕ) (hd : 3 < d) (u₁ u₂ k : ℤ) :
    principalFiveTermRationalCharacteristic d (u₁ - (d : ℤ) * k) (u₂ + (d : ℤ) * k) =
      principalFiveTermRationalCharacteristic d u₁ u₂ +
        fun i => (![k, ((d : ℤ) - 1) * k] i : ℚ) := by
  have hd3 : (d : ℚ) - 3 ≠ 0 := by
    exact_mod_cast (by omega : (d : ℤ) - 3 ≠ 0)
  funext i
  fin_cases i <;>
    simp [principalFiveTermRationalCharacteristic, latticeCharacteristicLift, coe_principalA,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.adjugate_fin_two,
      principalDilogOrder, Nat.cast_sub (by omega : 3 ≤ d)] <;>
    field_simp [hd3] <;> ring

/-- The fractional symplectic form of the rational characteristic is exactly the source
lattice argument `z_u`. -/
theorem fracSymplecticFormRat_rationalCharacteristic
    (d : ℕ) (hd : 3 < d) (u₁ u₂ : ℤ) :
    fracSymplecticFormRat (principalFiveTermRationalCharacteristic d u₁ u₂) (principalRoot d) =
      principalFiveTermLatticeArgument d u₁ u₂ := by
  have hden : fltDenominator (principalA d : Mat(2, ℤ)) (principalRoot d) ≠ 0 := by
    rw [fltDenominator_principalA_principalRoot]
    exact (principalJacobiFactor_pos d hd).ne'
  have hscale := fracSymplecticFormRat_ratVecAction_of_flt_eq_self hden
    (flt_principalA_principalRoot d hd) (principalFiveTermRationalCharacteristic d u₁ u₂)
  rw [fltDenominator_principalA_principalRoot,
    principalJacobiFactor_eq_principalRoot_pow_three d hd] at hscale
  have hpair := congrArg
    (fun r : Fin 2 → ℚ => fracSymplecticFormRat r (principalRoot d))
    (ratVecAction_rationalCharacteristic_sub d hd u₁ u₂)
  rw [fracSymplecticFormRat_sub, hscale] at hpair
  simp only [fracSymplecticFormRat, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.cons_val_zero] at hpair
  norm_num at hpair
  have hε : 1 < principalRoot d ^ 3 :=
    one_lt_principalRoot_pow_three d hd
  have hne : (principalRoot d ^ 3)⁻¹ - 1 ≠ 0 := by
    exact ne_of_lt (sub_neg.mpr ((inv_lt_one₀ (lt_trans zero_lt_one hε)).2 hε))
  rw [principalFiveTermLatticeArgument, eq_div_iff hne]
  unfold fracSymplecticFormRat
  rw [mul_sub, mul_one, ← div_eq_mul_inv]
  exact hpair

/-- The source argument is outside `ℤ+ℤρ_d` exactly when its finite residue is nonzero. -/
theorem not_isPeriodLatticePoint_latticeArgument_iff
    (d : ℕ) (hd : 3 < d) (u₁ u₂ : ℤ) :
    ¬ IsPeriodLatticePoint (principalRoot d : ℂ)
        (principalFiveTermLatticeArgument d u₁ u₂ : ℂ) ↔
      principalFiveTermCharacteristicResidue d u₁ u₂ ≠ 0 := by
  let _ : NeZero (principalDilogOrder d) := principalDilogOrder_neZero d hd
  have harg := congrArg (fun z : ℝ => (z : ℂ))
    (fracSymplecticFormRat_rationalCharacteristic d hd u₁ u₂)
  rw [ofReal_fracSymplecticFormRat] at harg
  have hsub :=
    isIntegralIndex_characteristicResidue_sub d hd u₁ u₂
  rw [← harg, isPeriodLatticePoint_fracSymplecticFormRat_iff
    (principalRoot_irrational d hd),
    (isIntegralIndex_iff_of_isIntegralIndex_sub hsub).symm,
    isIntegralIndex_zmodCharacteristic_iff]

/-! ### Finite dilogarithm values

The canonical lift of the residue and the rational source characteristic differ by an integer
vector. Lemma 2 transfers the finite dilogarithm between them, and the cocycle comparison then
expresses the nonzero classes through the raw Faddeev product.
-/

/-- **[RW26, Radchenko, Wheeler (2026), equation (2), `eq:fgam.def`] at `γ=A_d` and a
nonzero source residue**: the finite dilogarithm is the raw principal Faddeev product at source
indices `(u₁,0)`. This bridges
`principalDilogValue_eq_etaMultiplier_mul` through
[RW26, Radchenko, Wheeler (2026), Lemma 2, `lem:lam.inv`], formalized by
`principalDilogValue_congr`. -/
@[source "RW26, equation (2), p. 2, eq:fgam.def (γ = A_d, nonzero source residue)"]
theorem principalDilogE_characteristicResidue (d : ℕ) (hd : 3 < d) (u₁ u₂ : ℤ)
    (hu : principalFiveTermCharacteristicResidue d u₁ u₂ ≠ 0) :
    principalDilogE d (principalFiveTermCharacteristicResidue d u₁ u₂) =
      etaMultiplier (principalA d) *
        principalFaddeev d u₁ 0
          (principalFiveTermLatticeArgument d u₁ u₂) := by
  let _ : NeZero (principalDilogOrder d) := principalDilogOrder_neZero d hd
  have hA := principalA_mem_gammaSubgroup_characteristic d hd u₁ u₂
  have hsub :=
    isIntegralIndex_characteristicResidue_sub d hd u₁ u₂
  have hr : ¬ IsIntegralIndex (principalFiveTermRationalCharacteristic d u₁ u₂) := by
    intro hr
    apply hu
    exact (isIntegralIndex_zmodCharacteristic_iff _ _).mp
      ((isIntegralIndex_iff_of_isIntegralIndex_sub hsub).mpr hr)
  have harg := congrArg (fun z : ℝ => (z : ℂ))
    (fracSymplecticFormRat_rationalCharacteristic d hd u₁ u₂)
  rw [ofReal_fracSymplecticFormRat] at harg
  calc
    principalDilogE d (principalFiveTermCharacteristicResidue d u₁ u₂) =
        principalDilogValue d (zmodCharacteristic (principalDilogOrder d)
          (principalFiveTermCharacteristicResidue d u₁ u₂)) := rfl
    _ = principalDilogValue d (principalFiveTermRationalCharacteristic d u₁ u₂) :=
      principalDilogValue_congr d hd hA hsub
    _ = _ := by
      rw [principalDilogValue_eq_etaMultiplier_mul
        d hd hr hA, nQPInt_principalFiveTermRationalCharacteristic d hd, harg]
      simp

/-! ### Transport and normalized representatives

The kernel transport adds the integral characteristic `k(1,d-1)`, so it preserves the residue
while shifting the source index by `d(d-3)k`. Division with remainder in this positive step
normalizes the index of every class into a window of `d(d-3)` consecutive integers.
-/

/-- Source transport preserves the finite residue. -/
theorem principalFiveTermCharacteristicResidue_transport (d : ℕ) (hd : 3 < d) (u₁ u₂ k : ℤ) :
    principalFiveTermCharacteristicResidue d (u₁ - (d : ℤ) * k) (u₂ + (d : ℤ) * k) =
      principalFiveTermCharacteristicResidue d u₁ u₂ := by
  let _ : NeZero (principalDilogOrder d) := principalDilogOrder_neZero d hd
  apply eq_of_isIntegralIndex_zmodCharacteristic_sub (principalDilogOrder d)
  have hnew := isIntegralIndex_characteristicResidue_sub d hd
    (u₁ - (d : ℤ) * k) (u₂ + (d : ℤ) * k)
  have hold :=
    isIntegralIndex_characteristicResidue_sub d hd u₁ u₂
  have hshift : IsIntegralIndex
      (principalFiveTermRationalCharacteristic d (u₁ - (d : ℤ) * k) (u₂ + (d : ℤ) * k) -
        principalFiveTermRationalCharacteristic d u₁ u₂) := by
    rw [principalFiveTermRationalCharacteristic_transport d hd]
    intro i
    exact ⟨![k, ((d : ℤ) - 1) * k] i, by simp⟩
  have h := isIntegralIndex_sub (isIntegralIndex_add hnew hshift) hold
  convert h using 1
  funext i
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-- Source transport shifts the integer index by `d(d-3)k`. -/
theorem principalFiveTermLatticeIndex_transport (d : ℕ) (u₁ u₂ k : ℤ) :
    principalFiveTermLatticeIndex d (u₁ - (d : ℤ) * k) (u₂ + (d : ℤ) * k) =
      principalFiveTermLatticeIndex d u₁ u₂ +
        principalFiveTermUpperIndexBound d * k := by
  simp only [principalFiveTermLatticeIndex, principalFiveTermUpperIndexBound]
  ring

end SIC
