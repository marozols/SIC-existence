/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SL2Z.TorsionCharacteristics
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient

/-!
# Lattice coordinates and duality for fixed characteristics

The fixed-characteristic bicharacter is nondegenerate when $\det(M-I)=-N$.

This module follows the group and Gaussian definitions of
[RW26, Radchenko, Wheeler (2026), Section 1] and the lattice identification in the proof of
[RW26, Radchenko, Wheeler (2026), Theorem 2, `thm:fg.equs`, Section 3.2]. It supplies the
integer linear algebra behind that identification.

## The argument

Put $A=M-I$ and suppose $\det A=-N$. The rational characteristic with lattice coordinate $k$ is
$r=-\operatorname{adj}(A)k/N$, so $Ar=k$. Its residue is `latticeCharacteristic M N k`.
Conversely, if a residue characteristic $x$ is fixed by $M$, then $A(x/N)$ is an integer vector
$k$; multiplying by $-\operatorname{adj}(A)/N$ recovers $x/N$, proving that every fixed
characteristic has a lattice coordinate.

The bicharacter of the lattice coordinate $k$ with $x$ is
$e(k_1x_2/N-k_2x_1/N)$. Testing the two coordinate vectors shows that a characteristic pairing
trivially with the whole fixed group has both coordinates integral, hence is zero.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### Rational lattice coordinates

The adjugate realizes the inverse of $M-I$ over $\mathbb Q$. Its rational value, residue, and
action equation connect the lattice coordinates used by Radchenko and Wheeler with
`fixedCharacteristics`. -/

/-- The rational characteristic $-\operatorname{adj}(M-I)k/N$ represented modulo $\mathbb Z^2$
by `latticeCharacteristic M N k`. This is the characteristic-coordinate form of the lattice
identification in [RW26, Radchenko, Wheeler (2026), Section 3.2]. -/
def latticeCharacteristicLift (M : SL(2, ℤ)) (N : ℕ) (k : Fin 2 → ℤ) : Fin 2 → ℚ :=
  fun i => (((-((M : Mat(2, ℤ)) - 1).adjugate).mulVec k) i : ℚ) / N

/-- If $\det(M-I)=-N$, then $(M-I)(-\operatorname{adj}(M-I)k/N)=k$. -/
theorem ratVecAction_latticeCharacteristicLift_sub (M : SL(2, ℤ)) (N : ℕ) [NeZero N]
    (hdet : ((M : Mat(2, ℤ)) - 1).det = -(N : ℤ)) (k : Fin 2 → ℤ) :
    ratVecAction (M : Mat(2, ℤ)) (latticeCharacteristicLift M N k) -
      latticeCharacteristicLift M N k = fun i => (k i : ℚ) := by
  have hn : (N : ℚ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  rw [Matrix.det_fin_two] at hdet
  have hdetQ :
      (((M : Mat(2, ℤ)) - 1) 0 0 : ℚ) * (((M : Mat(2, ℤ)) - 1) 1 1 : ℚ) -
        (((M : Mat(2, ℤ)) - 1) 0 1 : ℚ) * (((M : Mat(2, ℤ)) - 1) 1 0 : ℚ) =
          -(N : ℚ) := by exact_mod_cast hdet
  simp [Matrix.sub_apply] at hdetQ
  funext i
  fin_cases i <;>
    simp [ratVecAction, latticeCharacteristicLift, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Matrix.adjugate_fin_two] <;>
    field_simp
  · linear_combination -(k 0 : ℚ) * hdetQ
  · linear_combination -(k 1 : ℚ) * hdetQ

/-- The canonical lift of `latticeCharacteristic M N k` differs from
`latticeCharacteristicLift M N k` by an integer vector. -/
theorem isIntegralIndex_latticeCharacteristic_sub_lift
    (M : SL(2, ℤ)) (N : ℕ) [NeZero N] (k : Fin 2 → ℤ) :
    IsIntegralIndex (zmodCharacteristic N (latticeCharacteristic M N k) -
      latticeCharacteristicLift M N k) := by
  change IsIntegralIndex
    (zmodCharacteristic N (fun i =>
      (((-((M : Mat(2, ℤ)) - 1).adjugate).mulVec k) i : ZMod N)) -
        fun i => (((-((M : Mat(2, ℤ)) - 1).adjugate).mulVec k) i : ℚ) / N)
  exact isIntegralIndex_zmodCharacteristic_intCast_sub N
    ((-((M : Mat(2, ℤ)) - 1).adjugate).mulVec k)

/-- The adjugate lift is the unique rational vector whose $(M-I)$-image is its given lattice
coordinate; used by `exists_latticeCharacteristic_eq`. -/
private theorem latticeCharacteristicLift_eq_of_action (M : SL(2, ℤ)) (N : ℕ) [NeZero N]
    (hdet : ((M : Mat(2, ℤ)) - 1).det = -(N : ℤ)) {r : Fin 2 → ℚ}
    {k : Fin 2 → ℤ}
    (hk : ratVecAction (M : Mat(2, ℤ)) r - r = fun i => (k i : ℚ)) :
    latticeCharacteristicLift M N k = r := by
  let A := (((M : Mat(2, ℤ)) - 1).map (Int.castRingHom ℚ))
  have hA : A.det ≠ 0 := by
    dsimp only [A]
    have hmap : (((M : Mat(2, ℤ)) - 1).map (Int.castRingHom ℚ)).det =
        ((((M : Mat(2, ℤ)) - 1).det : ℤ) : ℚ) :=
      (RingHom.map_det (Int.castRingHom ℚ) ((M : Mat(2, ℤ)) - 1)).symm
    rw [hmap, hdet]
    have hnQ : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    exact neg_ne_zero.mpr hnQ
  apply Matrix.mulVec_injective_of_det_ne_zero hA
  have hAeq : A = (M : Mat(2, ℤ)).map (Int.castRingHom ℚ) - 1 := by
    ext i j
    simp [A, Matrix.sub_apply, Matrix.one_apply]
  rw [hAeq]
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec]
  simpa only [ratVecAction, Int.coe_castRingHom] using
    (ratVecAction_latticeCharacteristicLift_sub M N hdet k).trans hk.symm

/-- Every characteristic fixed by $M$ modulo $N$ is the residue of
$-\operatorname{adj}(M-I)k$ for an integer vector $k$. This is the surjectivity of the lattice
coordinates underlying the presentation of $G$ in
[RW26, Radchenko, Wheeler (2026), Sections 1 and 3.2]. -/
theorem exists_latticeCharacteristic_eq (M : SL(2, ℤ)) (N : ℕ) [NeZero N]
    (hdet : ((M : Mat(2, ℤ)) - 1).det = -(N : ℤ))
    {x : Fin 2 → ZMod N} (hx : x ∈ fixedCharacteristics M N) :
    ∃ k : Fin 2 → ℤ, latticeCharacteristic M N k = x := by
  have hgamma := (mem_fixedCharacteristics_iff M N x).mp hx
  choose k hk using ratVecAction_sub_intVec_of_mem_gammaSubgroup hgamma
  have hk' : ratVecAction (M : Mat(2, ℤ)) (zmodCharacteristic N x) -
      zmodCharacteristic N x = fun i => (k i : ℚ) := by
    funext i
    exact hk i
  refine ⟨k, eq_of_isIntegralIndex_zmodCharacteristic_sub N ?_⟩
  have hint := isIntegralIndex_latticeCharacteristic_sub_lift M N k
  rw [latticeCharacteristicLift_eq_of_action M N hdet hk'] at hint
  exact hint

/-! ### Perfect pairing

The lattice coordinates evaluate the bicharacter explicitly. The two standard coordinates detect
both coordinates of a fixed characteristic. -/

/-- The lattice-coordinate evaluation
$\langle -\operatorname{adj}(M-I)k;x\rangle_M=e(k_1x_2/N-k_2x_1/N)$ of the fixed
bicharacter. It bridges `thetaBicharacter_eq_exp` with the group coordinates of
[RW26, Radchenko, Wheeler (2026), Sections 1 and 3.2]. -/
theorem fixedBicharacter_latticeCharacteristic_left (M : SL(2, ℤ)) (N : ℕ) [NeZero N]
    (hdet : ((M : Mat(2, ℤ)) - 1).det = -(N : ℤ)) (k : Fin 2 → ℤ)
    {x : Fin 2 → ZMod N} (hx : x ∈ fixedCharacteristics M N) :
    fixedBicharacter M N (latticeCharacteristic M N k) x =
      Complex.exp (2 * Real.pi * Complex.I *
        (((k 0 : ℚ) * zmodCharacteristic N x 1 -
          (k 1 : ℚ) * zmodCharacteristic N x 0 : ℚ) : ℂ)) := by
  let r := latticeCharacteristicLift M N k
  let s := zmodCharacteristic N x
  have ha := ratVecAction_latticeCharacteristicLift_sub M N hdet k
  have hr : M ∈ gammaSubgroup r := mem_gammaSubgroup_of_isIntegralIndex (by
    rw [ha]
    intro i
    exact ⟨k i, rfl⟩)
  have hs : M ∈ gammaSubgroup s := (mem_fixedCharacteristics_iff M N x).mp hx
  have he := isIntegralIndex_latticeCharacteristic_sub_lift M N k
  have hp := thetaBicharacter_add_of_isIntegralIndex_left M hr hs he
  rw [show r + (zmodCharacteristic N (latticeCharacteristic M N k) - r) =
    zmodCharacteristic N (latticeCharacteristic M N k) by abel] at hp
  unfold fixedBicharacter
  rw [hp]
  let p : Fin 2 → ℤ := fun i => (x i).val
  have hs_eq : zmodCharacteristic N x = fun i => (p i : ℚ) / N := by
    ext i
    simp [p, zmodCharacteristic]
  have hdiv := thetaBicharacter_div_natCast M N
    (fun i => congrFun ha i) p (hs_eq ▸ hs)
  dsimp only [r, s]
  rw [hs_eq, hdiv]
  congr 1
  push_cast
  simp only [p]
  ring

/-- The fixed bicharacter is nondegenerate: a fixed characteristic pairs to one with every fixed
characteristic exactly when it is zero. This verifies the perfect-pairing condition used for the
finite group in [RW26, Radchenko, Wheeler (2026), Sections 3.2 and 4.1]. -/
theorem fixedBicharacter_eq_one_forall_iff (M : SL(2, ℤ)) (N : ℕ) [NeZero N]
    (hdet : ((M : Mat(2, ℤ)) - 1).det = -(N : ℤ))
    {x : Fin 2 → ZMod N} (hx : x ∈ fixedCharacteristics M N) :
    (∀ y : fixedCharacteristics M N, fixedBicharacter M N y x = 1) ↔ x = 0 := by
  constructor
  · intro h
    have h0 := h ⟨latticeCharacteristic M N ![0, -1],
      latticeCharacteristic_mem M N ![0, -1] hdet⟩
    have h1 := h ⟨latticeCharacteristic M N ![1, 0],
      latticeCharacteristic_mem M N ![1, 0] hdet⟩
    rw [fixedBicharacter_latticeCharacteristic_left M N hdet ![0, -1] hx] at h0
    rw [fixedBicharacter_latticeCharacteristic_left M N hdet ![1, 0] hx] at h1
    have h0' : Complex.exp (2 * Real.pi * Complex.I *
        ((zmodCharacteristic N x 0 : ℚ) : ℂ)) = 1 := by simpa using h0
    have h1' : Complex.exp (2 * Real.pi * Complex.I *
        ((zmodCharacteristic N x 1 : ℚ) : ℂ)) = 1 := by simpa using h1
    obtain ⟨n0, hn0⟩ := (exp_two_pi_I_ratCast_eq_one_iff _).mp h0'
    obtain ⟨n1, hn1⟩ := (exp_two_pi_I_ratCast_eq_one_iff _).mp h1'
    apply (isIntegralIndex_zmodCharacteristic_iff N x).mp
    intro i
    fin_cases i
    · exact ⟨n0, hn0⟩
    · exact ⟨n1, hn1⟩
  · rintro rfl y
    rw [fixedBicharacter_comm]
    exact fixedBicharacter_zero_left M N y

/-! ### Order of the fixed group

The lattice-coordinate map has kernel $(M-I)\mathbb Z^2$. The determinant computes the index of
this lattice and hence the order of the fixed group. -/

/-- The additive lattice-coordinate map used by `card_fixedCharacteristics`. -/
private def latticeCharacteristicHom (M : SL(2, ℤ)) (N : ℕ) [NeZero N]
    (hdet : ((M : Mat(2, ℤ)) - 1).det = -(N : ℤ)) :
    (Fin 2 → ℤ) →+ fixedCharacteristics M N where
  toFun k := ⟨latticeCharacteristic M N k, latticeCharacteristic_mem M N k hdet⟩
  map_zero' := by
    apply Subtype.ext
    funext i
    simp [latticeCharacteristic]
  map_add' k l := by
    apply Subtype.ext
    funext i
    simp [latticeCharacteristic, Matrix.mulVec_add]

/-- The kernel of the lattice-coordinate map is the image of $M-I$; used by
`card_fixedCharacteristics`. -/
private theorem latticeCharacteristicHom_ker (M : SL(2, ℤ)) (N : ℕ) [NeZero N]
    (hdet : ((M : Mat(2, ℤ)) - 1).det = -(N : ℤ)) :
    (latticeCharacteristicHom M N hdet).ker =
      (Matrix.toLin' ((M : Mat(2, ℤ)) - 1)).range.toAddSubgroup := by
  let A : Mat(2, ℤ) := (M : Mat(2, ℤ)) - 1
  have hn : (N : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  have hmul : A * (-A.adjugate) = (N : ℤ) • (1 : Mat(2, ℤ)) := by
    rw [mul_neg, Matrix.mul_adjugate, hdet]
    simp
  have hmul' : (-A.adjugate) * A = (N : ℤ) • (1 : Mat(2, ℤ)) := by
    rw [neg_mul, Matrix.adjugate_mul, hdet]
    simp
  ext k
  simp only [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, LinearMap.mem_range,
    Subtype.ext_iff, Matrix.toLin'_apply]
  change latticeCharacteristic M N k = 0 ↔ ∃ t : Fin 2 → ℤ, A.mulVec t = k
  constructor
  · intro hk
    have hk' : ∀ i, (((-A.adjugate).mulVec k) i : ZMod N) = 0 := by
      intro i
      simpa [latticeCharacteristic, A] using congrFun hk i
    have hdiv : ∀ i, ∃ t : ℤ, ((-A.adjugate).mulVec k) i = (N : ℤ) * t := by
      intro i
      obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp (hk' i)
      exact ⟨t, by simpa [mul_comm] using ht⟩
    choose t ht using hdiv
    refine ⟨t, ?_⟩
    have hv : (-A.adjugate).mulVec k = (N : ℤ) • t := by
      funext i
      simpa [Pi.smul_apply] using ht i
    have haction : A.mulVec ((-A.adjugate).mulVec k) = (N : ℤ) • k := by
      rw [Matrix.mulVec_mulVec, hmul, Matrix.smul_mulVec, Matrix.one_mulVec]
    have hscaled : (N : ℤ) • A.mulVec t = (N : ℤ) • k := by
      calc
        (N : ℤ) • A.mulVec t = A.mulVec ((N : ℤ) • t) :=
          (Matrix.mulVec_smul A (N : ℤ) t).symm
        _ = A.mulVec ((-A.adjugate).mulVec k) := by rw [hv]
        _ = (N : ℤ) • k := haction
    funext i
    exact mul_left_cancel₀ hn (by simpa [Pi.smul_apply] using congrFun hscaled i)
  · rintro ⟨t, rfl⟩
    have haction : (-A.adjugate).mulVec (A.mulVec t) = (N : ℤ) • t := by
      rw [Matrix.mulVec_mulVec, hmul', Matrix.smul_mulVec, Matrix.one_mulVec]
    change (fun i => (((-A.adjugate).mulVec (A.mulVec t)) i : ZMod N)) = 0
    rw [haction]
    funext i
    simp [Pi.smul_apply]

/-- The kernel of the lattice characteristic is the column lattice of $M-I$. -/
theorem latticeCharacteristic_eq_zero_iff (M : SL(2, ℤ)) (N : ℕ) [NeZero N]
    (hdet : ((M : Mat(2, ℤ)) - 1).det = -(N : ℤ)) (k : Fin 2 → ℤ) :
    latticeCharacteristic M N k = 0 ↔
      ∃ t : Fin 2 → ℤ, (((M : Mat(2, ℤ)) - 1).mulVec t) = k := by
  have hker := latticeCharacteristicHom_ker M N hdet
  constructor
  · intro hk
    have hmem : k ∈ (latticeCharacteristicHom M N hdet).ker := by
      apply Subtype.ext
      exact hk
    rw [hker] at hmem
    simpa only [Submodule.mem_toAddSubgroup, LinearMap.mem_range,
      Matrix.toLin'_apply] using hmem
  · rintro ⟨t, ht⟩
    have hmem : k ∈ (Matrix.toLin' ((M : Mat(2, ℤ)) - 1)).range.toAddSubgroup := by
      exact ⟨t, ht⟩
    rw [← hker] at hmem
    exact congrArg Subtype.val hmem

/-- A source pair is in the row lattice of $M-I$ exactly when its rotated pair is in the
column lattice. -/
theorem sourcePair_mem_rowLattice_iff (M : SL(2, ℤ)) (u₁ u₂ : ℤ) :
    (∃ v : Fin 2 → ℤ, (((M : Mat(2, ℤ)) - 1).mulVec v) = ![-u₂, u₁]) ↔
      ∃ s t : ℤ, u₁ = s * (M 0 0 - 1) + t * M 1 0 ∧
        u₂ = s * M 0 1 + t * (M 1 1 - 1) := by
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = (1 : ℤ) := by
    simpa only [Matrix.det_fin_two] using Matrix.SpecialLinearGroup.det_coe M
  constructor
  · rintro ⟨v, hv⟩
    have hv0 : (M 0 0 - 1) * v 0 + M 0 1 * v 1 = -u₂ := by
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.sub_apply,
        Matrix.one_apply] using congrFun hv 0
    have hv1 : M 1 0 * v 0 + (M 1 1 - 1) * v 1 = u₁ := by
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.sub_apply,
        Matrix.one_apply] using congrFun hv 1
    refine ⟨-M 1 0 * v 0 - M 1 1 * v 1,
      M 0 0 * v 0 + M 0 1 * v 1, ?_, ?_⟩
    · linear_combination -hv1 + v 1 * hdet
    · linear_combination hv0 - v 0 * hdet
  · rintro ⟨s, t, hu1, hu2⟩
    refine ⟨![M 0 1 * s + M 1 1 * t, -M 0 0 * s - M 1 0 * t], ?_⟩
    funext i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.sub_apply,
        Matrix.one_apply]
      linear_combination hu2 + t * hdet
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.sub_apply,
        Matrix.one_apply]
      linear_combination -hu1 - s * hdet

/-- **`|G| = N`**: the fixed characteristics modulo `N` number `N` when `det(M - I) = -N`. The
group `G = ℤ²/Λ_γ`, `Λ_γ = im(γ - 1)`, of [RW26, Radchenko, Wheeler (2026), Section 4.3,
`prop:rqffinitedilog`] has order `|det(γ - 1)|`: `k ↦ -adj(M - I)k/N` maps `ℤ²` onto the fixed
characteristics (`exists_latticeCharacteristic_eq`) with kernel `(M - I)ℤ²`, of index
`|det(M - I)|` (`AddSubgroup.index_eq_natAbs_det`). -/
theorem card_fixedCharacteristics (M : SL(2, ℤ)) (N : ℕ) [NeZero N]
    (hdet : ((M : Mat(2, ℤ)) - 1).det = -(N : ℤ)) :
    Fintype.card (fixedCharacteristics M N) = N := by
  let A : Mat(2, ℤ) := (M : Mat(2, ℤ)) - 1
  have hA : A.det ≠ 0 := by
    rw [hdet]
    exact neg_ne_zero.mpr (by exact_mod_cast (NeZero.ne N))
  have hcols : LinearIndependent ℤ A.col :=
    Matrix.mulVec_injective_iff.mp (Matrix.mulVec_injective_of_det_ne_zero hA)
  let B : Submodule ℤ (Fin 2 → ℤ) := Submodule.span ℤ (Set.range A.col)
  let bB : Module.Basis (Fin 2) ℤ B := Module.Basis.span hcols
  have hbdet : (Pi.basisFun ℤ (Fin 2)).det (fun i => (bB i : Fin 2 → ℤ)) = A.det := by
    rw [Module.Basis.det_apply]
    congr 1
    ext i j
    rw [Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    simp [bB, B]
  have hsurj : Function.Surjective (latticeCharacteristicHom M N hdet) := by
    intro x
    obtain ⟨k, hk⟩ := exists_latticeCharacteristic_eq M N hdet x.property
    exact ⟨k, Subtype.ext hk⟩
  calc
    Fintype.card (fixedCharacteristics M N) = Nat.card (fixedCharacteristics M N) :=
      Nat.card_eq_fintype_card.symm
    _ = Nat.card (latticeCharacteristicHom M N hdet).range := by
      rw [(AddMonoidHom.range_eq_top).mpr hsurj, AddSubgroup.card_top]
    _ = (latticeCharacteristicHom M N hdet).ker.index :=
      (AddSubgroup.index_ker _).symm
    _ = ((Matrix.toLin' A).range.toAddSubgroup).index := by
      rw [latticeCharacteristicHom_ker]
    _ = B.toAddSubgroup.index := by rw [Matrix.range_toLin' A]
    _ = ((Pi.basisFun ℤ (Fin 2)).det (fun i => (bB i : Fin 2 → ℤ))).natAbs :=
      AddSubgroup.index_eq_natAbs_det (Pi.basisFun ℤ (Fin 2)) B.toAddSubgroup bB
    _ = N := by rw [hbdet, hdet, Int.natAbs_neg, Int.natAbs_natCast]

end SIC
