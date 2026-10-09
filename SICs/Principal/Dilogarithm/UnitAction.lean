/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Dilogarithm.Values

/-!
# The Unit Action and the Lattice Coordinates of `G_d`

The action of `U_d` on `G_d`, which is multiplication by the conjugate unit `ε⁻¹ = ρ_d⁻¹`, the
threefold symmetry `E(U_d x) = E(x)` on `G_d`, the lattice coordinates `k ↦ -adj(A_d - I) k`
identifying `G_d` with `ℤ²/Λ`, and the vector `w'` with `(ε⁻¹ - 1)w' ≡ v` of the proof of
Theorem 7 run at the conjugate unit.

This module follows [RW26, Radchenko, Wheeler (2026), Section 1, the coordinates `G = ℤ²/Λ`;
equation (38), `eq:fgamma3sym`; and the proof of Theorem 7, `thm:ghostsic`, the vector
`w = ((r - s)ε + r)/(ε⁻³ - 1)` and the claim
`F_γ(w + j(ε - 1)/(M - 3)) = F_γ(v + w + j(ε - 1)/(M - 3))`] at `γ = A_d`, `τ = ρ_d`. In the
ideal-theoretic picture `G = (1/(ε³ - 1))ℤ[ε]/ℤ[ε]` the unit `ε = ρ_d` acts by multiplication;
in the project's characteristic coordinates multiplication by `ρ_d` is `r ↦ U_d⁻¹ r`
(`SICs.Principal.Dilogarithm.Values`), so multiplication by the conjugate unit `ε⁻¹` is
`r ↦ U_d r`, and on residue vectors it is `principalDilogUAction`, `x ↦ U_d x` with `U_d`
reduced modulo `N`. The threefold symmetry (38) also gives `F(ε⁻¹z) = F(z)`, which becomes
`E(U_d x) = E(x)` (`principalDilogE_principalDilogUAction`).

## The argument

**Lattice coordinates.** Radchenko and Wheeler name the elements of `G = ℤ²/Λ` by integer row
vectors `u`, with `z_u(ε⁻¹ - 1) = u₁τ + u₂`; the project's characteristic `r` has
`⟨⟨(γ - I)r, τ⟩⟩ = u₁τ + u₂`, so `u = (k₂, -k₁)` for `k = (γ - I)r ∈ ℤ²`, and `r = (γ - I)⁻¹k`.
Since `det(A_d - I) = -N`, the residue vector of `(A_d - I)⁻¹k` is `-adj(A_d - I) k`
(`principalDilogOfLattice`), which lies in `G_d` and pairs with the `d`-torsion by
`⟨-adj(A_d - I)k; d(d - 3)q⟩ = ω_d^{⟨q, k⟩}`
(`principalDilogBicharacter_ofLattice_torsion`, the last display of
[RW26, Radchenko, Wheeler (2026), Section 4.4] through
`thetaBicharacter_shiftRationalPoint_principalA`).

**The vector `w'`.** For `v = (rε + s)/M`, Radchenko and Wheeler take
`w = ((r - s)ε + r)/(ε⁻³ - 1)`, with `(ε - 1)w ≡ v (mod ℤ[ε])`. The same argument runs with `ε⁻¹`
in place of `ε`: in the project's coordinates `v = p/d` with `(r, s) = (p₂, -p₁)`, the vector
`w' = v/(ε⁻¹ - 1)` is `principalDilogDualVectorConj d p`, the lattice coordinates
`k = (-(p₁ + p₂), p₁)`, with `U_d w' = v + w'` (`principalDilogUAction_dualVectorConj`). Its
character `⟨w'; q/d⟩ = ω_d^{-(p₁q₁ + p₂q₂ + p₁q₂)}` is the one produced by the finite Twisted
Convolution sum. Since `U_d g = g` for the generator `g = (ε - 1)/(M - 3)` of `G_d/H`
(`principalDilogUAction_principalDilogGenerator`), (38) gives the claim
`E(w' + jg) = E(U_d(w' + jg)) = E(v + w' + jg)` (`principalDilogE_dualVectorConj_add_nsmul`), and
`v + w' + jg ≠ 0` for `v ≠ 0` because `U_d` is invertible on `(ℤ/Nℤ)²`. The vector serves
`SICs.Principal.Dilogarithm.TorsionConvolution`.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### The action of `U_d` on `G_d`

`x ↦ U_d x` on residue vectors is multiplication by the conjugate unit `ε⁻¹`; it preserves `G_d`,
fixes the generator `g`, and leaves `E` invariant. -/

/-- **The action of `U_d` on residue vectors**, `x ↦ U_d x` with `U_d` reduced modulo `N`: the
residue form of `r ↦ U_d r` on characteristics, which on `z = ⟨⟨r, ρ_d⟩⟩` is multiplication by
the conjugate unit `ε⁻¹ = ρ_d⁻¹` of [RW26, Radchenko, Wheeler (2026), Section 4.4], since
`r ↦ U_d⁻¹ r` is multiplication by `ρ_d` (`principalDilogValue_ratVecAction_principalU`).
Specializes `residueMulVec`. -/
abbrev principalDilogUAction (d : ℕ) (x : Fin 2 → ZMod (principalDilogOrder d)) :
    Fin 2 → ZMod (principalDilogOrder d) :=
  residueMulVec (principalU d) (principalDilogOrder d) x

/-- `U_d x = ((d - 1)x₁ - x₂, x₁)` (`coe_principalU`). -/
theorem principalDilogUAction_apply (d : ℕ) (x : Fin 2 → ZMod (principalDilogOrder d)) :
    principalDilogUAction d x =
      ![((d : ZMod (principalDilogOrder d)) - 1) * x 0 - x 1, x 0] := by
  funext i
  fin_cases i <;>
    simp [principalDilogUAction, residueMulVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      coe_principalU, Matrix.map_apply, sub_eq_add_neg]

/-- **`G_d` is stable under `U_d`**, because `U_d A_d U_d⁻¹ = A_d`.
Specializes `residueMulVec_mem_fixedCharacteristics`. -/
theorem principalDilogUAction_mem (d : ℕ) (_hd : 3 < d)
    {x : Fin 2 → ZMod (principalDilogOrder d)} (hx : x ∈ principalDilogGroup d) :
    principalDilogUAction d x ∈ principalDilogGroup d := by
  exact residueMulVec_mem_fixedCharacteristics (principalU d) (principalA d)
    (principalDilogOrder d) (principalU_mul_principalA_mul_inv d) hx

/-- **`U_d g = g`**: `U_d(1, 1) = (d - 2, 1) ≡ (1, 1) (mod (d - 3))`, i.e.
`ε⁻¹ (ε - 1)/(M - 3) ≡ (ε - 1)/(M - 3) (mod ℤ[ε])`, the invariance of the generator of `G_d/H`
under the unit. -/
theorem principalDilogUAction_principalDilogGenerator (d : ℕ) (hd : 3 < d) :
    principalDilogUAction d (principalDilogGenerator d) = principalDilogGenerator d := by
  have hN := natCast_sq_mul_natCast_sub_three_eq_zero d hd
  rw [principalDilogUAction_apply]
  funext i
  fin_cases i <;> simp [principalDilogGenerator]
  linear_combination hN

/-- **[RW26, Radchenko, Wheeler (2026), equation (38), `eq:fgamma3sym`] on `G_d`**:
`E(U_d x) = E(x)` for `x ∈ G_d`, the residue form of `principalDilogValue_ratVecAction_principalU`,
i.e. `F(ε⁻¹ z) = F(z)`; the lift of `U_d x` differs from `U_d (x/N)` by an integer vector, which
Lemma 2 (`principalDilogValue_congr`) absorbs. -/
theorem principalDilogE_principalDilogUAction (d : ℕ) (hd : 3 < d)
    {x : Fin 2 → ZMod (principalDilogOrder d)} (hx : x ∈ principalDilogGroup d) :
    principalDilogE d (principalDilogUAction d x) = principalDilogE d x := by
  let r := zmodCharacteristic (principalDilogOrder d) x
  have hr : principalA d ∈ gammaSubgroup r :=
    (mem_principalDilogGroup_iff d hd x).mp hx
  have : NeZero (principalDilogOrder d) := principalDilogOrder_neZero d hd
  have hsub := isIntegralIndex_residueMulVec_sub
    (principalU d) (principalDilogOrder d) x
  have hrev : IsIntegralIndex
      (ratVecAction (principalU d : Mat(2, ℤ)) r -
        zmodCharacteristic (principalDilogOrder d) (principalDilogUAction d x)) := by
    simpa only [neg_sub] using (isIntegralIndex_neg_iff _).mpr hsub
  have hr' : principalA d ∈ gammaSubgroup
      (ratVecAction (principalU d : Mat(2, ℤ)) r) :=
    mem_gammaSubgroup_of_isIntegralIndex_sub hrev
      ((mem_principalDilogGroup_iff d hd _).mp (principalDilogUAction_mem d hd hx))
  unfold principalDilogE
  rw [principalDilogValue_congr d hd hr'
    hsub]
  exact principalDilogValue_ratVecAction_principalU d hd hr

/-! ### Lattice coordinates

The residue vector `-adj(A_d - I) k` of the characteristic `(A_d - I)⁻¹ k`, `k ∈ ℤ²`: Radchenko and
Wheeler's coordinates on `G = ℤ²/Λ`, and their pairing with the `d`-torsion. -/

/-- **The lattice coordinates of `G_d`**: the residue vector `-adj(A_d - I) k` of the
characteristic `(A_d - I)⁻¹ k = -adj(A_d - I) k / N` of an integer vector `k`, explicitly
`(d k₁ - d(d - 2) k₂, d(d - 2) k₁ - d(d² - 3d + 1) k₂)`. This is the identification `G = ℤ²/Λ`
of [RW26, Radchenko, Wheeler (2026), Section 1] in the project's coordinates: their row vector
`u` with `z_u(ε⁻¹ - 1) = u₁τ + u₂` is `u = (k₂, -k₁)`. The general rational lift
`latticeCharacteristicLift` supplies this inverse image and its integral congruence with the
canonical residue lift.
Specializes `latticeCharacteristic`. -/
abbrev principalDilogOfLattice (d : ℕ) (k : IntPhaseSpace) :
    Fin 2 → ZMod (principalDilogOrder d) :=
  latticeCharacteristic (principalA d) (principalDilogOrder d) k

/-- The lattice coordinate formula is
`-adj(A_d-I)k=(d k₁-d(d-2)k₂, d(d-2)k₁-d(d²-3d+1)k₂)`. -/
theorem principalDilogOfLattice_apply (d : ℕ) (k : IntPhaseSpace) :
    principalDilogOfLattice d k =
      ![(((d : ℤ) * k 0 - (d : ℤ) * ((d : ℤ) - 2) * k 1 : ℤ) :
          ZMod (principalDilogOrder d)),
        (((d : ℤ) * ((d : ℤ) - 2) * k 0 -
          (d : ℤ) * ((d : ℤ) ^ 2 - 3 * d + 1) * k 1 : ℤ) :
          ZMod (principalDilogOrder d))] := by
  funext i
  fin_cases i <;>
    simp [principalDilogOfLattice, latticeCharacteristic, coe_principalA,
      Matrix.adjugate_fin_two, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    ring

/-- `-adj(A_d - I) k ∈ G_d` from `det(A_d-I)=-N`.
Specializes `latticeCharacteristic_mem`. -/
theorem principalDilogOfLattice_mem (d : ℕ) (hd : 3 < d) (k : IntPhaseSpace) :
    principalDilogOfLattice d k ∈ principalDilogGroup d := by
  exact latticeCharacteristic_mem (principalA d) (principalDilogOrder d) k
    (det_principalA_sub_one d hd)

/-- Integral changes of the two lifts preserve the lattice and torsion pairing.
Used by `principalDilogBicharacter_ofLattice_torsion`. -/
private theorem principalDilogOfLattice_pairing_lift_congr (d : ℕ) (hd : 3 < d)
    (k q : IntPhaseSpace) {r : Fin 2 → ℚ}
    (hk : ∀ i, ratVecAction (principalA d : Mat(2, ℤ)) r i - r i = (k i : ℚ))
    (he : IsIntegralIndex
      (zmodCharacteristic (principalDilogOrder d) (principalDilogOfLattice d k) - r)) :
    thetaBicharacter
        (zmodCharacteristic (principalDilogOrder d) (principalDilogOfLattice d k))
        (zmodCharacteristic (principalDilogOrder d) (principalDilogTorsion d q))
        (principalA d : Mat(2, ℤ)) =
      thetaBicharacter r (shiftRationalPoint d q) (principalA d : Mat(2, ℤ)) := by
  let s := shiftRationalPoint d q
  let r' := zmodCharacteristic (principalDilogOrder d) (principalDilogOfLattice d k)
  let s' := zmodCharacteristic (principalDilogOrder d) (principalDilogTorsion d q)
  have hr : principalA d ∈ gammaSubgroup r :=
    mem_gammaSubgroup_of_isIntegralIndex (by
      intro i
      exact ⟨k i, by simpa [Pi.sub_apply] using hk i⟩)
  have hs : principalA d ∈ gammaSubgroup s :=
    principalA_mem_gammaSubgroup_shiftRationalPoint d hd q
  have hr' : principalA d ∈ gammaSubgroup r' :=
    mem_gammaSubgroup_of_isIntegralIndex_sub he hr
  have he' : IsIntegralIndex (s' - s) :=
    isIntegralIndex_principalDilogTorsion_sub d hd q
  have hleft := thetaBicharacter_add_of_isIntegralIndex_left (principalA d) hr hs he
  have hright := thetaBicharacter_add_of_isIntegralIndex_left (principalA d) hs hr' he'
  have hidx : r + (r' - r) = r' := by abel
  have hidx' : s + (s' - s) = s' := by abel
  rw [hidx] at hleft
  rw [hidx'] at hright
  change thetaBicharacter r' s' _ = thetaBicharacter r s _
  rw [thetaBicharacter_comm r' s', hright,
    ← thetaBicharacter_comm r' s, hleft]

/-- **The pairing of the lattice coordinates with the `d`-torsion**:
`⟨-adj(A_d - I) k; d(d - 3) q⟩ = ω_d^{⟨q, k⟩}` with `⟨q, k⟩ = q₂k₁ - q₁k₂`, the last display of
[RW26, Radchenko, Wheeler (2026), Section 4.4] (`e_M(a₁v₂ - a₂v₁)` at `(a₁, a₂) = (k₂, -k₁)`,
`(v₁, v₂) = (q₂, -q₁)`), from `thetaBicharacter_shiftRationalPoint_principalA` at the exact
characteristic `-adj(A_d - I) k / N`, which satisfies `(A_d - I) r = k`; the lifts differ from
the exact characteristics by integer vectors
(`isIntegralIndex_latticeCharacteristic_sub_lift`,
`isIntegralIndex_principalDilogTorsion_sub`), absorbed by
`thetaBicharacter_add_of_isIntegralIndex_left` and `thetaBicharacter_comm`. -/
theorem principalDilogBicharacter_ofLattice_torsion
    (d : RankOneDimension) (k q : IntPhaseSpace) :
    principalDilogBicharacter d (principalDilogOfLattice d k) (principalDilogTorsion d q) =
      standardRoot d ^ intSymplecticForm q k := by
  have : NeZero (principalDilogOrder d) := principalDilogOrder_neZero d d.property
  let r := latticeCharacteristicLift (principalA d) (principalDilogOrder d) k
  have hk : ∀ i, ratVecAction (principalA d : Mat(2, ℤ)) r i - r i =
      (k i : ℚ) := fun i => by
    simpa only [r, Pi.sub_apply] using congrFun
      (ratVecAction_latticeCharacteristicLift_sub (principalA d)
        (principalDilogOrder d) (det_principalA_sub_one d d.property) k) i
  have he : IsIntegralIndex
      (zmodCharacteristic (principalDilogOrder d) (principalDilogOfLattice d k) - r) := by
    simpa only [principalDilogOfLattice, r] using
      (isIntegralIndex_latticeCharacteristic_sub_lift
        (principalA d) (principalDilogOrder d) k)
  change thetaBicharacter
    (zmodCharacteristic (principalDilogOrder d) (principalDilogOfLattice d k))
    (zmodCharacteristic (principalDilogOrder d) (principalDilogTorsion d q))
    (principalA d : Mat(2, ℤ)) = _
  rw [principalDilogOfLattice_pairing_lift_congr d d.property k q hk he]
  exact thetaBicharacter_shiftRationalPoint_principalA d hk q

/-! ### The conjugate vector `w'` of Theorem 7

`w' = v/(ε⁻¹ - 1)` for `v = p/d ∈ H`, the claim `E(w' + jg) = E(v + w' + jg)`, and the
nonvanishing `v + w' + jg ≠ 0`. -/

/-- **The conjugate vector `w' = v/(ε⁻¹ - 1)`**: the element of `G_d` with `(ε⁻¹ - 1)w' ≡ v`,
i.e. `U_d w' = v + w'`, with the lattice coordinates `k = (-(p₁ + p₂), p₁)`; `w' ≡ -w - v`
modulo the subgroup generated by `g`. Radchenko and Wheeler's argument for
[RW26, Radchenko, Wheeler (2026), Theorem 7, `thm:ghostsic`] runs verbatim with `ε⁻¹` in place
of `ε`, since (38) holds for both, and `w'` produces the character on `H` of the finite Twisted
Convolution sum. -/
def principalDilogDualVectorConj (d : ℕ) (p : IntPhaseSpace) :
    Fin 2 → ZMod (principalDilogOrder d) :=
  principalDilogOfLattice d ![-(p 0 + p 1), p 0]

/-- `w' ∈ G_d` (`principalDilogOfLattice_mem`). -/
theorem principalDilogDualVectorConj_mem (d : ℕ) (hd : 3 < d) (p : IntPhaseSpace) :
    principalDilogDualVectorConj d p ∈ principalDilogGroup d :=
  principalDilogOfLattice_mem d hd _

/-- **`(ε⁻¹ - 1)w' ≡ v`** in residue form: `U_d w' = v + w'` for `v = d(d - 3)p`. -/
theorem principalDilogUAction_dualVectorConj (d : ℕ) (hd : 3 < d)
    (p : IntPhaseSpace) :
    principalDilogUAction d (principalDilogDualVectorConj d p) =
      principalDilogTorsion d p + principalDilogDualVectorConj d p := by
  have hN := natCast_sq_mul_natCast_sub_three_eq_zero d hd
  rw [principalDilogUAction_apply]
  funext i
  fin_cases i
  · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, principalDilogDualVectorConj,
      principalDilogOfLattice_apply, Fin.isValue, neg_add_rev, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Int.cast_sub, Int.cast_mul,
      Int.cast_natCast, Int.cast_add, Int.cast_neg, Int.cast_ofNat, Int.cast_pow,
      Int.cast_one, Fin.zero_eta, Pi.add_apply, principalDilogTorsion,
      Nat.cast_mul]
    rw [Nat.cast_sub (by omega : 3 ≤ d)]
    norm_num
    ring
  · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, principalDilogDualVectorConj,
      principalDilogOfLattice_apply, Fin.isValue, neg_add_rev, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Int.cast_sub, Int.cast_mul,
      Int.cast_natCast, Int.cast_add, Int.cast_neg, Int.cast_ofNat, Int.cast_pow,
      Int.cast_one, Fin.mk_one, Pi.add_apply, principalDilogTorsion,
      Nat.cast_mul]
    rw [Nat.cast_sub (by omega : 3 ≤ d)]
    norm_num
    linear_combination (p 0 : ZMod (principalDilogOrder d)) * hN

/-- The action on `w'+jg` gives `v+w'+jg`. -/
theorem principalDilogUAction_dualVectorConj_add_nsmul
    (d : ℕ) (hd : 3 < d) (p : IntPhaseSpace) (j : ℕ) :
    principalDilogUAction d (principalDilogDualVectorConj d p +
      j • principalDilogGenerator d) =
      principalDilogTorsion d p + principalDilogDualVectorConj d p +
        j • principalDilogGenerator d := by
  change residueMulVec (principalU d) (principalDilogOrder d) _ = _
  rw [residueMulVec_add, residueMulVec_nsmul]
  change principalDilogUAction d (principalDilogDualVectorConj d p) +
    j • principalDilogUAction d (principalDilogGenerator d) = _
  rw [principalDilogUAction_dualVectorConj d hd p,
    principalDilogUAction_principalDilogGenerator d hd]

/-- The claim `E(w' + jg) = E(v + w' + jg)` for the conjugate vector, from (38)
(`principalDilogE_principalDilogUAction`) and `U_d(w' + jg) = v + w' + jg`. -/
theorem principalDilogE_dualVectorConj_add_nsmul (d : ℕ) (hd : 3 < d)
    (p : IntPhaseSpace) (j : ℕ) :
    principalDilogE d (principalDilogDualVectorConj d p + j • principalDilogGenerator d) =
      principalDilogE d
        (principalDilogTorsion d p + principalDilogDualVectorConj d p +
          j • principalDilogGenerator d) := by
  have hm : principalDilogDualVectorConj d p + j • principalDilogGenerator d ∈
      principalDilogGroup d :=
    AddSubgroup.add_mem _ (principalDilogDualVectorConj_mem d hd p)
      (AddSubgroup.nsmul_mem _ (principalDilogGenerator_mem d hd) j)
  have hU : principalDilogUAction d
      (principalDilogDualVectorConj d p + j • principalDilogGenerator d) =
      principalDilogTorsion d p + principalDilogDualVectorConj d p +
        j • principalDilogGenerator d :=
    principalDilogUAction_dualVectorConj_add_nsmul d hd p j
  rw [← hU, principalDilogE_principalDilogUAction d hd hm]

/-- `v + w' + jg ≠ 0` for `v = d(d - 3)p ≠ 0`: otherwise `U_d(w' + jg) = 0` gives `w' + jg = 0`
and then `v = 0`. -/
theorem principalDilogTorsion_add_dualVectorConj_add_nsmul_ne_zero (d : ℕ)
    (hd : 3 < d) (p : IntPhaseSpace) (hp : intPhaseSpaceMod d p ≠ 0) (j : ℕ) :
    principalDilogTorsion d p + principalDilogDualVectorConj d p +
      j • principalDilogGenerator d ≠ 0 := by
  have hv : principalDilogTorsion d p ≠ 0 :=
    (principalDilogTorsion_eq_zero_iff d hd p).not.mpr hp
  intro h
  have hU : principalDilogUAction d
      (principalDilogDualVectorConj d p + j • principalDilogGenerator d) = 0 := by
    rw [principalDilogUAction_dualVectorConj_add_nsmul d hd p j]
    exact h
  have hz := (residueMulVec_eq_zero_iff (principalU d) (principalDilogOrder d) _).mp hU
  have hh : principalDilogTorsion d p +
      (principalDilogDualVectorConj d p + j • principalDilogGenerator d) = 0 := by
    simpa [add_assoc] using h
  rw [hz, add_zero] at hh
  exact hv hh

end SIC

end
