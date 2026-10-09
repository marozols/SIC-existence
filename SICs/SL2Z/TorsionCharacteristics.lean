/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SL2Z.ThetaCharacter

/-!
# Fixed characteristics, Gaussian, and lattice coordinates

Rational characteristics with denominator `N` as residue vectors in `(ℤ/Nℤ)²`, their fixed
group, Gaussian, bicharacter, matrix action, and lattice coordinates.

This module supplies the finite abelian group on which Radchenko and Wheeler's finite quantum
dilogarithm lives, [RW26, Radchenko, Wheeler (2026), Section 1]: for a hyperbolic
`γ ∈ SL₂(ℤ)` of trace `N + 2`, their `G = ℤ²/Λ` with `Λ = Nℤ² + ker(γ - 1)` (the kernel read
modulo `N`), a group of order
`N`. The project works with characteristics `r ∈ ℚ²` and the subgroups `Γ_r` of
`SICs.SL2Z.Characteristics`, so the same group appears here as the kernel of `M - I` acting on
`(ℤ/Nℤ)²`: the residue vectors `m` whose characteristic `m/N` has `M ∈ Γ_{m/N}`. The two
pictures correspond as follows: `u` is their row vector, `k = (γ - I)r ∈ ℤ²` for a
characteristic `r`, and `u = (k₂, -k₁)`. Thus `(γ - I)r = (-u₂, u₁)ᵀ` and
`r = (γ - I)⁻¹(-u₂, u₁)ᵀ`. Here `(γ - I)⁻¹ = -adj(γ - I)/N` maps `ℤ²` into
`(1/N)ℤ²`, and `Λ = {u : uγ ≡ u (mod N)}` corresponds to `ℤ²` under this map.
`SICs.Principal.Dilogarithm.Group` instantiates this at the
principal level matrix `A_d` with `N = d²(d - 3)`.

## The argument

A residue vector `m ∈ (ℤ/Nℤ)²` lifts to the characteristic `zmodCharacteristic N m = m/N ∈ ℚ²`
through the canonical representatives `0 ≤ mᵢ < N`. The lift is additive up to `ℤ²`
(`isIntegralIndex_zmodCharacteristic_add_sub`), so functions of characteristics that are
`ℤ²`-periodic descend to `(ℤ/Nℤ)²`. The matrix `M - I` reduced modulo `N` acts on `(ℤ/Nℤ)²`, and
its kernel `fixedCharacteristics M N` is an additive subgroup; `mem_fixedCharacteristics_iff`
identifies membership with `M ∈ Γ_{m/N}`, because `(M - I)(m/N) ∈ ℤ²` is exactly
`(M - I)m ≡ 0 (mod N)`. The theta character and bicharacter descend to the fixed group,
and commuting integral matrices act on it. When `det(M - I) = -N`, the adjugate gives
coordinates of its elements from the integer lattice.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### The lift of a residue vector to a characteristic

Residue vectors modulo `N` name the characteristics of denominator `N` up to `ℤ²`; the lift picks
the representative with coordinates in `[0, 1)`. -/

/-- The characteristic `m/N ∈ ℚ²` of a residue vector `m ∈ (ℤ/Nℤ)²`, through the canonical
representatives `0 ≤ mᵢ < N` (`ZMod.val`). At `N = 0` the residues are the integers and the
value is `0`; every consumer assumes `N ≠ 0`. -/
def zmodCharacteristic (N : ℕ) (m : Fin 2 → ZMod N) : Fin 2 → ℚ :=
  fun i => ((m i).val : ℚ) / N

/-- The lift of the zero residue vector is the zero characteristic. -/
@[simp]
theorem zmodCharacteristic_zero (N : ℕ) : zmodCharacteristic N 0 = 0 := by
  ext i
  simp [zmodCharacteristic]

/-- The scalar fact `(a - b)/N ∈ ℤ ↔ a ≡ b (mod N)`: integer representatives have
an integral quotient difference exactly when they have the same residue. -/
theorem exists_div_sub_div_eq_intCast_iff (N : ℕ) [NeZero N] (a b : ℤ) :
    (∃ t : ℤ, (a : ℚ) / N - (b : ℚ) / N = t) ↔
      (a : ZMod N) = (b : ZMod N) := by
  have hn : (N : ℚ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub, dvd_sub_comm]
  simp_rw [← sub_div, div_eq_iff hn, dvd_iff_exists_eq_mul_left]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, by exact_mod_cast ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, by exact_mod_cast ht⟩

/-- The lift of a sum differs from the sum of the lifts by an integer vector. -/
theorem isIntegralIndex_zmodCharacteristic_add_sub (N : ℕ) [NeZero N] (m m' : Fin 2 → ZMod N) :
    IsIntegralIndex
      (zmodCharacteristic N (m + m') - (zmodCharacteristic N m + zmodCharacteristic N m')) := by
  intro i
  have hc : (((m + m') i).val : ZMod N) =
      ((m i).val : ZMod N) + ((m' i).val : ZMod N) := by
    simp only [Pi.add_apply, ZMod.natCast_zmod_val]
  obtain ⟨t, ht⟩ := (exists_div_sub_div_eq_intCast_iff N
    (((m + m') i).val : ℤ) (((m i).val : ℤ) + (m' i).val)).mpr (by
      simpa only [Int.cast_add, Int.cast_natCast] using hc)
  exact ⟨t, by simpa [zmodCharacteristic, Pi.sub_apply, Pi.add_apply,
    Int.cast_add, Nat.cast_add, add_div] using ht⟩

/-- The lift of a negative differs from the negative of the lift by an integer vector. -/
theorem isIntegralIndex_zmodCharacteristic_neg_add (N : ℕ) [NeZero N] (m : Fin 2 → ZMod N) :
    IsIntegralIndex (zmodCharacteristic N (-m) + zmodCharacteristic N m) := by
  intro i
  have hc : (((-m) i).val : ZMod N) = -((m i).val : ZMod N) := by
    simp only [Pi.neg_apply, ZMod.natCast_zmod_val]
  obtain ⟨t, ht⟩ := (exists_div_sub_div_eq_intCast_iff N
    (((-m) i).val : ℤ) (-((m i).val : ℤ))).mpr (by
      simpa only [Int.cast_neg, Int.cast_natCast] using hc)
  exact ⟨t, by simpa [zmodCharacteristic, Pi.add_apply, neg_div, sub_neg_eq_add] using ht⟩

/-- The lift of the residue vector of an integer vector `k` differs from `k/N` by an integer
vector. -/
theorem isIntegralIndex_zmodCharacteristic_intCast_sub (N : ℕ) [NeZero N] (k : Fin 2 → ℤ) :
    IsIntegralIndex
      (zmodCharacteristic N (fun i => (k i : ZMod N)) - fun i => (k i : ℚ) / N) := by
  intro i
  have hc : (((k i : ZMod N).val : ℤ) : ZMod N) = (k i : ZMod N) := by
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  obtain ⟨t, ht⟩ := (exists_div_sub_div_eq_intCast_iff N
    (((k i : ZMod N).val : ℤ)) (k i)).mpr hc
  exact ⟨t, by simpa [zmodCharacteristic, Pi.sub_apply] using ht⟩

/-- Two residue vectors with lifts differing by an integer vector are equal: the lift is
injective modulo `ℤ²`. -/
theorem eq_of_isIntegralIndex_zmodCharacteristic_sub (N : ℕ) [NeZero N] {m m' : Fin 2 → ZMod N}
    (h : IsIntegralIndex (zmodCharacteristic N m' - zmodCharacteristic N m)) : m' = m := by
  funext i
  obtain ⟨t, ht⟩ := h i
  have hc := (exists_div_sub_div_eq_intCast_iff N
    (((m' i).val : ℤ)) (((m i).val : ℤ))).mp (by
      exact ⟨t, by simpa [zmodCharacteristic, Pi.sub_apply] using ht⟩)
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hc

/-- The lift of a residue vector is an integer vector exactly when the residue vector is zero
(`eq_of_isIntegralIndex_zmodCharacteristic_sub` at `m = 0`). -/
theorem isIntegralIndex_zmodCharacteristic_iff (N : ℕ) [NeZero N] (m : Fin 2 → ZMod N) :
    IsIntegralIndex (zmodCharacteristic N m) ↔ m = 0 := by
  constructor
  · intro h
    apply eq_of_isIntegralIndex_zmodCharacteristic_sub N
    simpa using h
  · intro h
    rw [h, zmodCharacteristic_zero]
    intro i
    exact ⟨0, rfl⟩

/-- The residue and rational lift of a matrix row agree; used by
`isIntegralIndex_zmodCharacteristic_mulVec_sub` and `mulVec_row_eq_zero_iff_integral`. -/
private theorem mulVec_residue_lift (A : Mat(2, ℤ)) (N : ℕ) [NeZero N]
    (m : Fin 2 → ZMod N) (i : Fin 2) :
    ((A i 0 * (m 0).val + A i 1 * (m 1).val : ℤ) : ZMod N) =
        (A.map (Int.castRingHom (ZMod N))).mulVec m i ∧
      ((A i 0 * (m 0).val + A i 1 * (m 1).val : ℤ) : ℚ) / N =
        ∑ j, (A i j : ℚ) * zmodCharacteristic N m j := by
  constructor
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply]
  · simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast,
      Fin.sum_univ_two, zmodCharacteristic]
    ring

/-- The lift of `M m`, for an integer matrix `M` reduced modulo `N`, differs from `M (m/N)` by an
integer vector: the lift commutes with integer matrices up to `ℤ²`. -/
theorem isIntegralIndex_zmodCharacteristic_mulVec_sub (N : ℕ) [NeZero N] (M : Mat(2, ℤ))
    (m : Fin 2 → ZMod N) :
    IsIntegralIndex
      (zmodCharacteristic N ((M.map (Int.castRingHom (ZMod N))).mulVec m) -
        ratVecAction M (zmodCharacteristic N m)) := by
  intro i
  let a : ℤ := M i 0 * (m 0).val + M i 1 * (m 1).val
  obtain ⟨hc, hq'⟩ := mulVec_residue_lift M N m i
  have hq : (a : ℚ) / N = ratVecAction M (zmodCharacteristic N m) i := by
    simpa only [a, ratVecAction, Matrix.mulVec, dotProduct, Matrix.map_apply] using hq'
  obtain ⟨t, ht⟩ := (exists_div_sub_div_eq_intCast_iff N
    (((Matrix.mulVec (M.map (Int.castRingHom (ZMod N))) m i).val : ℤ)) a).mpr (by
      simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hc.symm)
  exact ⟨t, by simpa [zmodCharacteristic, Pi.sub_apply, hq] using ht⟩

/-! ### The characteristics fixed by a matrix

The kernel of `M - I` on `(ℤ/Nℤ)²` is the finite group `G` of
[RW26, Radchenko, Wheeler (2026), Section 1] in the project's characteristic coordinates. -/

/-- **The residue vectors whose characteristic is fixed by `M` modulo `ℤ²`**: the kernel of the
reduction of `M - I` modulo `N`, acting on `(ℤ/Nℤ)²`. This is the group `G = ℤ²/Λ`,
`Λ = Nℤ² + ker(γ - 1)` (the kernel read modulo `N`), of
[RW26, Radchenko, Wheeler (2026), Section 1], in the coordinates
`r = (γ - I)⁻¹(-u₂, u₁)ᵀ` for their row vector `u`; `mem_fixedCharacteristics_iff` reads
membership as `M ∈ Γ_{m/N}`. -/
def fixedCharacteristics (M : Mat(2, ℤ)) (N : ℕ) : AddSubgroup (Fin 2 → ZMod N) :=
  (LinearMap.ker (Matrix.mulVecLin ((M - 1).map (Int.castRingHom (ZMod N))))).toAddSubgroup

/-- Unfolding lemma: `m ∈ fixedCharacteristics M N` says `(M - I) m ≡ 0 (mod N)`, coordinate by
coordinate. -/
theorem mem_fixedCharacteristics_iff_mulVec (M : Mat(2, ℤ)) (N : ℕ) (m : Fin 2 → ZMod N) :
    m ∈ fixedCharacteristics M N ↔
      Matrix.mulVec ((M - 1).map (Int.castRingHom (ZMod N))) m = 0 := by
  simp only [fixedCharacteristics, Submodule.mem_toAddSubgroup, LinearMap.mem_ker,
    Matrix.mulVecLin_apply]

/-- Equal moduli identify the fixed characteristic groups. -/
def fixedCharacteristics_congrModulus (M : Mat(2, ℤ)) {N N' : ℕ} (h : N = N') :
    fixedCharacteristics M N ≃+ fixedCharacteristics M N' := by
  cases h
  exact AddEquiv.refl _

/-- The modulus identification acts coordinatewise by `ZMod.ringEquivCongr`. -/
theorem fixedCharacteristics_congrModulus_apply (M : Mat(2, ℤ)) {N N' : ℕ}
    (h : N = N') (x : fixedCharacteristics M N) :
    ((fixedCharacteristics_congrModulus M h x : fixedCharacteristics M N') : Fin 2 → ZMod N') =
      fun i => ZMod.ringEquivCongr h ((x : Fin 2 → ZMod N) i) := by
  cases h
  simp [fixedCharacteristics_congrModulus]

/-- A row of an integer matrix annihilates a residue vector modulo `N` exactly when its
rational action on the lifted characteristic has an integer coordinate. -/
theorem mulVec_row_eq_zero_iff_integral (A : Mat(2, ℤ)) (N : ℕ) [NeZero N]
    (m : Fin 2 → ZMod N) (i : Fin 2) :
    Matrix.mulVec (A.map (Int.castRingHom (ZMod N))) m i = 0 ↔
      ∃ t : ℤ, ∑ j, (A i j : ℚ) * zmodCharacteristic N m j = (t : ℚ) := by
  let a : ℤ := A i 0 * (m 0).val + A i 1 * (m 1).val
  obtain ⟨hc, hq⟩ := mulVec_residue_lift A N m i
  rw [← hc, ← hq]
  constructor
  · intro h
    change ((a : ℤ) : ZMod N) = 0 at h
    obtain ⟨t, ht⟩ := (exists_div_sub_div_eq_intCast_iff N a 0).mpr
      (by simpa only [Int.cast_zero] using h)
    exact ⟨t, by simpa only [Int.cast_zero, Nat.cast_zero, zero_div, sub_zero] using ht⟩
  · rintro ⟨t, ht⟩
    change ((a : ℤ) : ZMod N) = 0
    simpa only [Int.cast_zero] using (exists_div_sub_div_eq_intCast_iff N a 0).mp
      ⟨t, by simpa only [Int.cast_zero, Nat.cast_zero, zero_div, sub_zero] using ht⟩

/-- **Membership is `M ∈ Γ_{m/N}`**: a residue vector is fixed by `M` exactly when the matrix lies
in the congruence subgroup of its characteristic, since `(M - I)(m/N) ∈ ℤ²` is
`(M - I)m ≡ 0 (mod N)`. -/
theorem mem_fixedCharacteristics_iff (M : SL(2, ℤ)) (N : ℕ) [NeZero N] (m : Fin 2 → ZMod N) :
    m ∈ fixedCharacteristics (M : Mat(2, ℤ)) N ↔ M ∈ gammaSubgroup (zmodCharacteristic N m) := by
  rw [mem_fixedCharacteristics_iff_mulVec]
  constructor
  · intro h i
    have hi := congrFun h i
    obtain ⟨t, ht⟩ :=
      (mulVec_row_eq_zero_iff_integral ((M : Mat(2, ℤ)) - 1) N m i).mp hi
    refine ⟨t, ?_⟩
    simpa [Matrix.sub_apply, Matrix.one_apply] using ht
  · intro h
    funext i
    obtain ⟨t, ht⟩ := h i
    apply (mulVec_row_eq_zero_iff_integral ((M : Mat(2, ℤ)) - 1) N m i).mpr
    exact ⟨t, by simpa [Matrix.sub_apply, Matrix.one_apply] using ht⟩

/-- The fixed characteristics form a finite group. -/
noncomputable instance fixedCharacteristics.instFintype (M : Mat(2, ℤ)) (N : ℕ) [NeZero N] :
    Fintype (fixedCharacteristics M N) :=
  Fintype.ofFinite _

/-! ### The Gaussian and bicharacter on fixed characteristics

The character `χ_r(M)` and its quotient bicharacter descend to the fixed group through the
canonical lift. These are Radchenko and Wheeler's `⟨u⟩_γ` and `⟨u;v⟩_γ` in the characteristic
coordinates described above [RW26, Radchenko, Wheeler (2026), Section 1, before Theorem 2,
`thm:fg.equs`]. -/

/-- The Gaussian `⟨x⟩` on fixed residue characteristics: Kopp's character `χ_{x/N}(M)`.
Bridges `thetaCharacter` with the Gaussian of
[RW26, Radchenko, Wheeler (2026), Section 1, before Theorem 2, `thm:fg.equs`]. -/
def fixedGaussian (M : SL(2, ℤ)) (N : ℕ) (x : Fin 2 → ZMod N) : ℂ :=
  thetaCharacter (zmodCharacteristic N x) M

/-- The bicharacter `⟨x;y⟩` on fixed residue characteristics, the quotient of Gaussians.
Bridges `thetaBicharacter` with the bicharacter of
[RW26, Radchenko, Wheeler (2026), Section 1, before Theorem 2, `thm:fg.equs`]. -/
def fixedBicharacter (M : SL(2, ℤ)) (N : ℕ) (x y : Fin 2 → ZMod N) : ℂ :=
  thetaBicharacter (zmodCharacteristic N x) (zmodCharacteristic N y) M

/-- The Gaussian has value `⟨0⟩ = 1`. -/
@[simp]
theorem fixedGaussian_zero (M : SL(2, ℤ)) (N : ℕ) : fixedGaussian M N 0 = 1 := by
  simp only [fixedGaussian, zmodCharacteristic_zero]
  exact thetaCharacter_of_isIntegralIndex M (by
    intro i
    exact ⟨0, by simp⟩)

/-- The Gaussian never vanishes. -/
theorem fixedGaussian_ne_zero (M : SL(2, ℤ)) (N : ℕ) (x : Fin 2 → ZMod N) :
    fixedGaussian M N x ≠ 0 :=
  thetaCharacter_ne_zero _ _

/-- Membership and the lift defect for addition; used by `fixedGaussian_add` and
`fixedBicharacter_add_left`. -/
private theorem fixedCharacteristics_lift_add (M : SL(2, ℤ)) (N : ℕ) [NeZero N]
    {x y : Fin 2 → ZMod N}
    (hx : x ∈ fixedCharacteristics (M : Mat(2, ℤ)) N)
    (hy : y ∈ fixedCharacteristics (M : Mat(2, ℤ)) N) :
    M ∈ gammaSubgroup (zmodCharacteristic N x + zmodCharacteristic N y) ∧
      IsIntegralIndex (zmodCharacteristic N (x + y) -
        (zmodCharacteristic N x + zmodCharacteristic N y)) := by
  have ht := (mem_fixedCharacteristics_iff M N _).mp (AddSubgroup.add_mem _ hx hy)
  have he := isIntegralIndex_zmodCharacteristic_add_sub N x y
  have hrev : IsIntegralIndex
      (zmodCharacteristic N x + zmodCharacteristic N y - zmodCharacteristic N (x + y)) := by
    simpa only [neg_sub] using (isIntegralIndex_neg_iff _).mpr he
  exact ⟨mem_gammaSubgroup_of_isIntegralIndex_sub hrev ht, he⟩

/-- The Gaussian law `⟨x+y⟩ = ⟨x⟩⟨y⟩⟨x;y⟩` on the fixed group. -/
theorem fixedGaussian_add (M : SL(2, ℤ)) (N : ℕ) [NeZero N]
    {x y : Fin 2 → ZMod N}
    (hx : x ∈ fixedCharacteristics (M : Mat(2, ℤ)) N)
    (hy : y ∈ fixedCharacteristics (M : Mat(2, ℤ)) N) :
    fixedGaussian M N (x + y) =
      fixedGaussian M N x * fixedGaussian M N y * fixedBicharacter M N x y := by
  let r := zmodCharacteristic N x
  let s := zmodCharacteristic N y
  let t := zmodCharacteristic N (x + y)
  obtain ⟨hrs, he⟩ := fixedCharacteristics_lift_add M N hx hy
  have hindex : (r + s) + (t - (r + s)) = t := by abel
  have hperiod := thetaCharacter_add_of_isIntegralIndex M hrs he
  rw [hindex] at hperiod
  change thetaCharacter t _ = thetaCharacter r _ * thetaCharacter s _ *
    thetaBicharacter r s _
  rw [hperiod]
  simp only [thetaBicharacter]
  exact (mul_div_cancel₀ _
    (mul_ne_zero (thetaCharacter_ne_zero _ _) (thetaCharacter_ne_zero _ _))).symm

/-- The Gaussian is even on the fixed group: `⟨-x⟩ = ⟨x⟩`. -/
theorem fixedGaussian_neg (M : SL(2, ℤ)) (N : ℕ) [NeZero N]
    {x : Fin 2 → ZMod N} (hx : x ∈ fixedCharacteristics (M : Mat(2, ℤ)) N) :
    fixedGaussian M N (-x) = fixedGaussian M N x := by
  let r := zmodCharacteristic N x
  let s := zmodCharacteristic N (-x)
  have hr : M ∈ gammaSubgroup r := (mem_fixedCharacteristics_iff M N x).mp hx
  have he : IsIntegralIndex (s + r) := isIntegralIndex_zmodCharacteristic_neg_add N x
  have he' : IsIntegralIndex (s - -r) := by simpa only [sub_neg_eq_add] using he
  have hindex : -r + (s - -r) = s := by abel
  change thetaCharacter s _ = thetaCharacter r _
  rw [← hindex, thetaCharacter_add_of_isIntegralIndex M (neg_mem_gammaSubgroup hr) he',
    thetaCharacter_neg M hr]

/-- The bicharacter is symmetric: `⟨x;y⟩ = ⟨y;x⟩`. -/
theorem fixedBicharacter_comm (M : SL(2, ℤ)) (N : ℕ)
    (x y : Fin 2 → ZMod N) :
    fixedBicharacter M N x y = fixedBicharacter M N y x :=
  thetaBicharacter_comm _ _ _

/-- The bicharacter has `⟨0;y⟩ = 1`. -/
@[simp]
theorem fixedBicharacter_zero_left (M : SL(2, ℤ)) (N : ℕ)
    (y : Fin 2 → ZMod N) : fixedBicharacter M N 0 y = 1 := by
  simp only [fixedBicharacter, zmodCharacteristic_zero]
  exact thetaBicharacter_zero_left _ M

/-- The bicharacter is additive in its first argument on the fixed group. -/
theorem fixedBicharacter_add_left (M : SL(2, ℤ)) (N : ℕ) [NeZero N]
    {x x' y : Fin 2 → ZMod N}
    (hx : x ∈ fixedCharacteristics (M : Mat(2, ℤ)) N)
    (hx' : x' ∈ fixedCharacteristics (M : Mat(2, ℤ)) N)
    (hy : y ∈ fixedCharacteristics (M : Mat(2, ℤ)) N) :
    fixedBicharacter M N (x + x') y =
      fixedBicharacter M N x y * fixedBicharacter M N x' y := by
  let r := zmodCharacteristic N x
  let r' := zmodCharacteristic N x'
  let s := zmodCharacteristic N y
  let t := zmodCharacteristic N (x + x')
  have hr : M ∈ gammaSubgroup r := (mem_fixedCharacteristics_iff M N _).mp hx
  have hr' : M ∈ gammaSubgroup r' := (mem_fixedCharacteristics_iff M N _).mp hx'
  have hs : M ∈ gammaSubgroup s := (mem_fixedCharacteristics_iff M N _).mp hy
  obtain ⟨hrr', he⟩ := fixedCharacteristics_lift_add M N hx hx'
  have hindex : (r + r') + (t - (r + r')) = t := by abel
  have hperiod := thetaBicharacter_add_of_isIntegralIndex_left M hrr' hs he
  rw [hindex] at hperiod
  change thetaBicharacter t s _ = thetaBicharacter r s _ * thetaBicharacter r' s _
  rw [hperiod]
  exact thetaBicharacter_add_left M hr hr' hs

/-- The bicharacter is additive in its second argument on the fixed group. -/
theorem fixedBicharacter_add_right (M : SL(2, ℤ)) (N : ℕ) [NeZero N]
    {x u v : Fin 2 → ZMod N}
    (hx : x ∈ fixedCharacteristics (M : Mat(2, ℤ)) N)
    (hu : u ∈ fixedCharacteristics (M : Mat(2, ℤ)) N)
    (hv : v ∈ fixedCharacteristics (M : Mat(2, ℤ)) N) :
    fixedBicharacter M N x (u + v) =
      fixedBicharacter M N x u * fixedBicharacter M N x v := by
  rw [fixedBicharacter_comm M N x (u + v),
    fixedBicharacter_add_left M N hu hv hx,
    fixedBicharacter_comm M N u x, fixedBicharacter_comm M N v x]

/-- Natural multiples in the first argument become powers: `⟨n • x;y⟩ = ⟨x;y⟩ⁿ`. -/
theorem fixedBicharacter_nsmul_left (M : SL(2, ℤ)) (N : ℕ) [NeZero N]
    {x y : Fin 2 → ZMod N}
    (hx : x ∈ fixedCharacteristics (M : Mat(2, ℤ)) N)
    (hy : y ∈ fixedCharacteristics (M : Mat(2, ℤ)) N) (n : ℕ) :
    fixedBicharacter M N (n • x) y = fixedBicharacter M N x y ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [succ_nsmul, fixedBicharacter_add_left M N
        (AddSubgroup.nsmul_mem _ hx n) hx hy, ih, pow_succ]

/-! ### Matrix actions, lattice coordinates, and torsion

Integral determinant-one matrices act on residue vectors. A matrix commuting with `M` preserves
the kernel of `M - I`. When `det(M - I) = -N`, multiplying an integer vector by
`-adj(M - I)` produces a fixed residue characteristic. The theta character at `p/d` depends only
on the residues of `p`, while its bicharacter with another fixed characteristic has an explicit
`d`-th root of unity. These statements apply to the principal torsion formulas of
[RW26, Radchenko, Wheeler (2026), Section 4.4] without assuming a principal matrix. -/

/-- The action of `R ∈ SL₂(ℤ)` on residue vectors modulo `N`. -/
def residueMulVec (R : SL(2, ℤ)) (N : ℕ) (x : Fin 2 → ZMod N) : Fin 2 → ZMod N :=
  ((R : Mat(2, ℤ)).map (Int.castRingHom (ZMod N))).mulVec x

/-- The residue matrix action is additive. -/
theorem residueMulVec_add (R : SL(2, ℤ)) (N : ℕ) (x y : Fin 2 → ZMod N) :
    residueMulVec R N (x + y) = residueMulVec R N x + residueMulVec R N y :=
  Matrix.mulVec_add _ x y

/-- The residue action respects matrix multiplication. -/
private theorem residueMulVec_mul (R S : SL(2, ℤ)) (N : ℕ) (x : Fin 2 → ZMod N) :
    residueMulVec (R * S) N x = residueMulVec R N (residueMulVec S N x) := by
  unfold residueMulVec
  rw [Matrix.SpecialLinearGroup.coe_mul]
  have hmap : (((R : Mat(2, ℤ)) * (S : Mat(2, ℤ))).map
      (Int.castRingHom (ZMod N))) =
        (R : Mat(2, ℤ)).map (Int.castRingHom (ZMod N)) *
          (S : Mat(2, ℤ)).map (Int.castRingHom (ZMod N)) := by
    exact Matrix.map_mul
  rw [hmap]
  exact (Matrix.mulVec_mulVec x _ _).symm

/-- The residue matrix action commutes with natural multiples. -/
theorem residueMulVec_nsmul (R : SL(2, ℤ)) (N : ℕ) (n : ℕ) (x : Fin 2 → ZMod N) :
    residueMulVec R N (n • x) = n • residueMulVec R N x :=
  Matrix.mulVec_smul _ n x

/-- A determinant-one matrix acts injectively on residue vectors. -/
theorem residueMulVec_eq_zero_iff (R : SL(2, ℤ)) (N : ℕ) (x : Fin 2 → ZMod N) :
    residueMulVec R N x = 0 ↔ x = 0 := by
  let f := Int.castRingHom (ZMod N)
  have hinv : ((R⁻¹ : Mat(2, ℤ)).map f) * ((R : Mat(2, ℤ)).map f) = 1 := by
    rw [← Matrix.map_mul]
    simp
  constructor
  · intro h
    have h' := congrArg (fun v => ((R⁻¹ : Mat(2, ℤ)).map f).mulVec v) h
    simp only [residueMulVec, Matrix.mulVec_zero] at h'
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] at h'
    exact h'
  · rintro rfl
    simp [residueMulVec]

/-- The lift of `R x` differs from `R(x/N)` by an integer vector. -/
theorem isIntegralIndex_residueMulVec_sub
    (R : SL(2, ℤ)) (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N) :
    IsIntegralIndex (zmodCharacteristic N (residueMulVec R N x) -
      ratVecAction (R : Mat(2, ℤ)) (zmodCharacteristic N x)) :=
  isIntegralIndex_zmodCharacteristic_mulVec_sub N R x

/-- Conjugation carries a fixed residue characteristic of `M` to one of `RMR⁻¹`. -/
private theorem residueMulVec_mem_fixedCharacteristics_conj (R M : SL(2, ℤ)) (N : ℕ)
    {x : Fin 2 → ZMod N} (hx : x ∈ fixedCharacteristics (M : Mat(2, ℤ)) N) :
    residueMulVec R N x ∈ fixedCharacteristics ((R * M * R⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) N := by
  let f := Int.castRingHom (ZMod N)
  have hRM : (R * M * R⁻¹) * R = R * M := by simp [mul_assoc]
  have hcoe : ((R * M * R⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) * (R : Mat(2, ℤ)) =
      (R : Mat(2, ℤ)) * (M : Mat(2, ℤ)) := by
    exact congrArg (fun A : SL(2, ℤ) => (A : Mat(2, ℤ))) hRM
  have hmatrixInt :
      ((((R * M * R⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) - 1) * (R : Mat(2, ℤ))) =
        (R : Mat(2, ℤ)) * ((M : Mat(2, ℤ)) - 1) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hcoe]
  have hmatrix :
      (((R * M * R⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) - 1).map f * (R : Mat(2, ℤ)).map f =
        (R : Mat(2, ℤ)).map f * ((M : Mat(2, ℤ)) - 1).map f := by
    simpa only [Matrix.map_mul] using
      congrArg (fun A : Mat(2, ℤ) => A.map f) hmatrixInt
  rw [mem_fixedCharacteristics_iff_mulVec] at hx ⊢
  change ((((R * M * R⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) - 1).map f).mulVec
    (((R : Mat(2, ℤ)).map f).mulVec x) = 0
  rw [Matrix.mulVec_mulVec, hmatrix, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]

/-- If `RMR⁻¹ = M`, then `R` preserves the fixed residue characteristics of `M`. -/
theorem residueMulVec_mem_fixedCharacteristics (R M : SL(2, ℤ)) (N : ℕ)
    (hcomm : R * M * R⁻¹ = M) {x : Fin 2 → ZMod N}
    (hx : x ∈ fixedCharacteristics (M : Mat(2, ℤ)) N) :
    residueMulVec R N x ∈ fixedCharacteristics (M : Mat(2, ℤ)) N := by
  simpa only [hcomm] using residueMulVec_mem_fixedCharacteristics_conj R M N hx

/-- Conjugation identifies the fixed residue groups of `M` and `RMR⁻¹`. -/
def fixedCharacteristics_conjAddEquiv (M R : SL(2, ℤ)) (N : ℕ) :
    fixedCharacteristics (M : Mat(2, ℤ)) N ≃+
      fixedCharacteristics ((R * M * R⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) N where
  toFun x := ⟨residueMulVec R N x,
    residueMulVec_mem_fixedCharacteristics_conj R M N x.property⟩
  invFun y := ⟨residueMulVec R⁻¹ N y, by
    have hy := residueMulVec_mem_fixedCharacteristics_conj R⁻¹ (R * M * R⁻¹) N y.property
    have hc : R⁻¹ * (R * M * R⁻¹) * (R⁻¹)⁻¹ = M := by group
    simpa only [hc] using hy⟩
  left_inv x := by
    apply Subtype.ext
    change residueMulVec R⁻¹ N (residueMulVec R N x) = x
    rw [← residueMulVec_mul, inv_mul_cancel]
    simp [residueMulVec]
  right_inv y := by
    apply Subtype.ext
    change residueMulVec R N (residueMulVec R⁻¹ N y) = y
    rw [← residueMulVec_mul, mul_inv_cancel]
    simp [residueMulVec]
  map_add' x y := by
    apply Subtype.ext
    exact residueMulVec_add R N x y

/-- The fixed bicharacter is invariant under conjugation and the residue action of `R`. -/
theorem fixedBicharacter_conj (M R : SL(2, ℤ)) (N : ℕ) [NeZero N]
    {x y : Fin 2 → ZMod N}
    (hx : x ∈ fixedCharacteristics (M : Mat(2, ℤ)) N)
    (hy : y ∈ fixedCharacteristics (M : Mat(2, ℤ)) N) :
    fixedBicharacter (R * M * R⁻¹) N (residueMulVec R N x) (residueMulVec R N y) =
      fixedBicharacter M N x y := by
  let B := R * M * R⁻¹
  let r := zmodCharacteristic N x
  let s := zmodCharacteristic N y
  let r' := zmodCharacteristic N (residueMulVec R N x)
  let s' := zmodCharacteristic N (residueMulVec R N y)
  have hconj : (B : Mat(2, ℤ)) * (R : Mat(2, ℤ)) =
      (R : Mat(2, ℤ)) * (M : Mat(2, ℤ)) := by
    exact congrArg (fun T : SL(2, ℤ) => (T : Mat(2, ℤ)))
      (show B * R = R * M by simp [B, mul_assoc])
  have hr : M ∈ gammaSubgroup r := (mem_fixedCharacteristics_iff M N x).mp hx
  have hs : M ∈ gammaSubgroup s := (mem_fixedCharacteristics_iff M N y).mp hy
  have hrB : B ∈ gammaSubgroup (ratVecAction (R : Mat(2, ℤ)) r) :=
    mem_gammaSubgroup_ratVecAction_of_mul_eq hr hconj
  have hsB : B ∈ gammaSubgroup (ratVecAction (R : Mat(2, ℤ)) s) :=
    mem_gammaSubgroup_ratVecAction_of_mul_eq hs hconj
  have hdr : IsIntegralIndex (r' - ratVecAction (R : Mat(2, ℤ)) r) :=
    isIntegralIndex_residueMulVec_sub R N x
  have hds : IsIntegralIndex (s' - ratVecAction (R : Mat(2, ℤ)) s) :=
    isIntegralIndex_residueMulVec_sub R N y
  have hsB' : B ∈ gammaSubgroup s' :=
    mem_gammaSubgroup_of_isIntegralIndex_sub hds hsB
  have hleft : thetaBicharacter r' s' B =
      thetaBicharacter (ratVecAction (R : Mat(2, ℤ)) r) s' B := by
    have ht := thetaBicharacter_add_of_isIntegralIndex_left B hrB hsB' hdr
    have heq : ratVecAction (R : Mat(2, ℤ)) r +
        (r' - ratVecAction (R : Mat(2, ℤ)) r) = r' := by abel
    rwa [heq] at ht
  have hright : thetaBicharacter (ratVecAction (R : Mat(2, ℤ)) r) s' B =
      thetaBicharacter (ratVecAction (R : Mat(2, ℤ)) r)
        (ratVecAction (R : Mat(2, ℤ)) s) B := by
    have ht := thetaBicharacter_add_of_isIntegralIndex_left B hsB hrB hds
    have heq : ratVecAction (R : Mat(2, ℤ)) s +
        (s' - ratVecAction (R : Mat(2, ℤ)) s) = s' := by abel
    rw [heq] at ht
    exact (thetaBicharacter_comm _ _ _).trans
      (ht.trans (thetaBicharacter_comm _ _ _))
  exact hleft.trans (hright.trans (thetaBicharacter_conj M R hr hs))


/-- The residue of `-adj(M-I)k`, the lattice coordinate of a fixed characteristic. -/
def latticeCharacteristic (M : SL(2, ℤ)) (N : ℕ) (k : Fin 2 → ℤ) : Fin 2 → ZMod N :=
  fun i => (((-((M : Mat(2, ℤ)) - 1).adjugate).mulVec k) i : ZMod N)

/-- If `det(M-I) = -N`, then `-adj(M-I)k` lies in the fixed group modulo `N`. -/
theorem latticeCharacteristic_mem (M : SL(2, ℤ)) (N : ℕ) (k : Fin 2 → ℤ)
    (hdet : ((M : Mat(2, ℤ)) - 1).det = -(N : ℤ)) :
    latticeCharacteristic M N k ∈ fixedCharacteristics (M : Mat(2, ℤ)) N := by
  let A : Mat(2, ℤ) := (M : Mat(2, ℤ)) - 1
  have hA : A * (-A.adjugate) = (N : ℤ) • (1 : Mat(2, ℤ)) := by
    rw [mul_neg, Matrix.mul_adjugate, hdet]
    simp
  have hvec : A.mulVec ((-A.adjugate).mulVec k) = (N : ℤ) • k := by
    rw [Matrix.mulVec_mulVec, hA, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [mem_fixedCharacteristics_iff_mulVec]
  funext i
  change ((A.map (Int.castRingHom (ZMod N))).mulVec
    (fun j => (((-A.adjugate).mulVec k) j : ZMod N))) i = 0
  calc
    _ = ((Int.castRingHom (ZMod N)) (A.mulVec ((-A.adjugate).mulVec k) i)) := by
      simpa only [Function.comp_def, Int.coe_castRingHom] using
        (RingHom.map_mulVec (Int.castRingHom (ZMod N)) A ((-A.adjugate).mulVec k) i).symm
    _ = 0 := by rw [hvec]; simp [Pi.smul_apply]

/-- The general torsion bicharacter formula
`⟨r;p/d⟩_M = e((p₂k₁-p₁k₂)/d)` for `(M-I)r=k ∈ ℤ²` and `M ∈ Γ_{p/d}`.
Bridges `thetaBicharacter_eq_exp` with the torsion coordinates of
[RW26, Radchenko, Wheeler (2026), Section 4.4]. -/
theorem thetaBicharacter_div_natCast (M : SL(2, ℤ)) (d : ℕ) [NeZero d]
    {r : Fin 2 → ℚ} {k : Fin 2 → ℤ}
    (hk : ∀ i, ratVecAction (M : Mat(2, ℤ)) r i - r i = (k i : ℚ))
    (p : Fin 2 → ℤ)
    (hp : M ∈ gammaSubgroup (fun i => (p i : ℚ) / d)) :
    thetaBicharacter r (fun i => (p i : ℚ) / d) M =
      Complex.exp (2 * Real.pi * Complex.I *
        ((((p 1 * k 0 - p 0 * k 1 : ℤ) : ℚ) / d : ℚ) : ℂ)) := by
  have hk₁ : ((M 0 0 : ℚ) - 1) * r 0 + (M 0 1 : ℚ) * r 1 = (k 0 : ℚ) := by
    have h := hk 0
    simp [ratVecAction, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h ⊢
    linear_combination h
  have hk₂ : (M 1 0 : ℚ) * r 0 + ((M 1 1 : ℚ) - 1) * r 1 = (k 1 : ℚ) := by
    have h := hk 1
    simp [ratVecAction, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h ⊢
    linear_combination h
  rw [thetaBicharacter_eq_exp M hk₁ hk₂ hp]
  congr 1
  push_cast
  ring

/-- The theta character at `p/d` depends only on `p` modulo `d`, provided `M ∈ Γ_{p/d}`.
Bridges `thetaCharacter_add_of_isIntegralIndex` with residue coordinates. -/
theorem thetaCharacter_div_natCast_congr (M : SL(2, ℤ)) (d : ℕ) [NeZero d]
    {p p' : Fin 2 → ℤ}
    (hp : M ∈ gammaSubgroup (fun i => (p i : ℚ) / d))
    (h : ∀ i, (p' i : ZMod d) = (p i : ZMod d)) :
    thetaCharacter (fun i => (p' i : ℚ) / d) M =
      thetaCharacter (fun i => (p i : ℚ) / d) M := by
  have he : IsIntegralIndex
      ((fun i => (p' i : ℚ) / d) - (fun i => (p i : ℚ) / d)) := by
    intro i
    obtain ⟨t, ht⟩ := (exists_div_sub_div_eq_intCast_iff d (p' i) (p i)).mpr (h i)
    exact ⟨t, by simpa only [Pi.sub_apply] using ht⟩
  calc
    thetaCharacter (fun i => (p' i : ℚ) / d) M =
        thetaCharacter ((fun i => (p i : ℚ) / d) +
          ((fun i => (p' i : ℚ) / d) - (fun i => (p i : ℚ) / d))) M := by
            congr 1
            abel
    _ = thetaCharacter (fun i => (p i : ℚ) / d) M :=
      thetaCharacter_add_of_isIntegralIndex M hp he

end SIC

end
