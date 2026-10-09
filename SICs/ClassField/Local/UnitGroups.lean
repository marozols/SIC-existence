/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Algebra.Ring.Subring.Units
import Mathlib.Topology.Algebra.Group.Units
import SICs.ClassField.Completion.Basic

/-!
# Integral and higher unit groups of a finite completion

The group $U_v$ of integral units of the completion $K_v$ of a number field at a finite place, the
higher unit groups $U_v^{(n)} = 1 + \mathfrak p_v^n$, their descriptions by the normalized
valuation, the splitting $K_v^\times \cong U_v \times \mathbb Z$, their openness, and their
role as a basis of neighbourhoods of one.

These are the local unit groups of Milne, *Class Field Theory*, version 4.03 (2020), Chapter III,
§1, Lemma 1.3, with $U_v^{(0)} = U_v$. They are the local factors of the idèlic ray subgroups
of `SICs.ClassField.Ideles.RayModulus` and the Galois modules of local class field theory in
`SICs.ClassField.Local.ValuationSequence`.

## The argument

The integral units form the subgroup used by Mathlib's restricted product of local units; a unit
is integral exactly when its valuation is one. The level-`n` higher unit group is the kernel of
reduction of integral units modulo the `n`-th power of the maximal ideal. The image of a
uniformizer of the ring of integers is a uniformizer of the completion, of valuation
$\exp(-1)$, and the `n`-th power of the maximal ideal
is the set of elements of valuation at most $\exp(-n)$; so $x \in U_v^{(n)}$ exactly when
$v(x) = 1$ and $v(x - 1) \le \exp(-n)$. That is an open condition, being a valuation ball about
one intersected with the open group of integral units. Conversely, these balls form a basis of
neighbourhoods of one in $K_v$, and the units carry the subspace topology of $K_v$, so every
neighbourhood of one in $K_v^\times$ contains some $U_v^{(n)}$. Every element of $K_v^\times$ is a
power of an element of valuation $\exp(-1)$ times an integral unit.
-/

noncomputable section

open NumberField IsDedekindDomain
open scoped NumberField WithZero

namespace SIC

universe u

namespace FinitePlace

variable {K : Type u} [Field K] [NumberField K]

/-! ### Integral units -/

/-- The valuation ring inside a finite completion. -/
private abbrev completionIntegers
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
  v.adicCompletionIntegers K

/-- The integral units $U_v$ at a finite place, as the subgroup used by Mathlib's restricted
product of local units. Milne, *Class Field Theory*, Chapter III, §1, Lemma 1.3. -/
abbrev unitGroup
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Subgroup (v.adicCompletion K)ˣ :=
  (Submonoid.ofClass (v.adicCompletionIntegers K)).units

/-- A finite local unit is integral exactly when its valuation is one. -/
theorem mem_unitGroup_iff_valued
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (x : (v.adicCompletion K)ˣ) :
    x ∈ unitGroup v ↔ Valued.v (x : v.adicCompletion K) = 1 := by
  exact IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one

/-- An element of a finite completion is an integral unit exactly when its norm is one. -/
theorem mem_unitGroup_iff_norm_eq_one
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (x : (v.adicCompletion K)ˣ) :
    x ∈ unitGroup v ↔ ‖(x : v.adicCompletion K)‖ = 1 := by
  rw [mem_unitGroup_iff_valued]
  exact Valued.toNormedField.norm_eq_one_iff.symm

/-- A global unit maps into the local integral units exactly when its valuation is one. -/
theorem units_map_mem_unitGroup_iff
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) (x : Kˣ) :
    Units.map (algebraMap K (v.adicCompletion K)) x ∈ unitGroup v ↔
      v.valuation K (x : K) = 1 := by
  rw [mem_unitGroup_iff_valued]
  change Valued.v (((x : K) : v.adicCompletion K)) = 1 ↔ _
  rw [v.valuedAdicCompletion_eq_valuation']

/-- The group of integral units at a finite place is open. -/
theorem isOpen_unitGroup
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    IsOpen (unitGroup v : Set (v.adicCompletion K)ˣ) := by
  exact Submonoid.isOpen_units (U := Submonoid.ofClass (v.adicCompletionIntegers K))
    (Valued.isOpen_valuationSubring (v.adicCompletion K))

/-- The local valuation ring is compact [83, Neukirch (1999), Chapter II,
Proposition 5.1]. -/
@[source "83, Chapter II, Proposition 5.1, p. 135 (valuation ring)"]
theorem isCompact_adicCompletionIntegers
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  convert isCompact_closedBall (0 : v.adicCompletion K) 1 using 1
  ext x
  simpa only [SetLike.mem_coe, Metric.mem_closedBall, dist_zero_right,
    IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] using
    (Valued.toNormedField.norm_le_one_iff (x := x)).symm

/-- The integral units of a finite completion form a compact set, by compactness of the
valuation ring [83, Neukirch (1999), Chapter II, Proposition 5.1]. -/
theorem isCompact_unitGroup (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    IsCompact (unitGroup v : Set (v.adicCompletion K)ˣ) := by
  have hO := isCompact_adicCompletionIntegers v
  exact Submonoid.units_isCompact hO

/-- An open subgroup of $K_v^\times$ meets the integral units $U_v$ in a subgroup of finite index
in $U_v$. This is the compact/open-quotient consequence of `isCompact_unitGroup`, whose
compactness input is [83, Neukirch (1999), Chapter II, Proposition 5.1]. -/
theorem finiteIndex_subgroupOf_unitGroup (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    {V : Subgroup (v.adicCompletion K)ˣ} (hV : IsOpen (V : Set (v.adicCompletion K)ˣ)) :
    (V.subgroupOf (unitGroup v)).FiniteIndex := by
  have hUcompact : CompactSpace (unitGroup v) :=
    isCompact_iff_compactSpace.mp (isCompact_unitGroup v)
  have hVopen : IsOpen (V.subgroupOf (unitGroup v) : Set (unitGroup v)) :=
    Subgroup.subgroupOf_isOpen (unitGroup v) V hV
  have hfinite : Finite (unitGroup v ⧸ V.subgroupOf (unitGroup v)) :=
    @Subgroup.quotient_finite_of_isOpen _ _ _ _ hUcompact _ hVopen
  exact Subgroup.finiteIndex_iff_finite_quotient.mpr hfinite

/-! ### Higher unit groups -/

/-- Identify the multiplicative subtype of the completion's valuation ring with its ring
subtype; used by `unitGroupEquivIntegersUnits`. -/
private def completionIntegersMulEquiv
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (Submonoid.ofClass (completionIntegers v)) ≃* completionIntegers v where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Identify local integral units with the units of the completion's valuation ring; used by
`unitReduction`. -/
private def unitGroupEquivIntegersUnits
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    unitGroup v ≃* (completionIntegers v)ˣ :=
  (Submonoid.ofClass (completionIntegers v)).unitsEquivUnitsType.trans
    (Units.mapEquiv (completionIntegersMulEquiv v))

/-- Reduction of integral units modulo the `n`-th power of the maximal ideal. -/
private def unitReduction
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) (n : ℕ) :
    unitGroup v →*
      ((completionIntegers v) ⧸
        ((IsLocalRing.maximalIdeal (completionIntegers v)) ^ n))ˣ :=
  (Units.map (Ideal.Quotient.mk
    ((IsLocalRing.maximalIdeal (completionIntegers v)) ^ n)).toMonoidHom).comp
      (unitGroupEquivIntegersUnits v).toMonoidHom

/-- The `n`-th higher unit group, embedded in the multiplicative group of the completion.
Milne, *Class Field Theory*, Chapter III, §1, Lemma 1.3, with $U_v^{(0)} = U_v$. -/
def higherUnitGroup
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) (n : ℕ) :
    Subgroup (v.adicCompletion K)ˣ :=
  (unitReduction v n).ker.map (unitGroup v).subtype

/-- Every higher unit is an integral unit. -/
theorem higherUnitGroup_le_unitGroup
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) (n : ℕ) :
    higherUnitGroup v n ≤ unitGroup v := by
  rintro x hx
  rcases hx with ⟨y, hy, rfl⟩
  exact y.property

/-- Membership in the higher unit group is congruence to one modulo the `n`-th power of the
maximal ideal. -/
private theorem mem_higherUnitGroup_iff
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) (n : ℕ)
    (x : (v.adicCompletion K)ˣ) :
    x ∈ higherUnitGroup v n ↔
      ∃ hx : x ∈ unitGroup v,
        (((unitGroupEquivIntegersUnits v) ⟨x, hx⟩ :
          (completionIntegers v)ˣ) : completionIntegers v) - 1 ∈
          (IsLocalRing.maximalIdeal (completionIntegers v)) ^ n := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    subst x
    refine ⟨y.property, ?_⟩
    change unitReduction v n y = 1 at hy
    have hy' := congrArg Units.val hy
    change Ideal.Quotient.mk
      ((IsLocalRing.maximalIdeal (completionIntegers v)) ^ n)
        ((unitGroupEquivIntegersUnits v) y :
          completionIntegers v) = 1 at hy'
    have hmod := Ideal.Quotient.mk_eq_one_iff_sub_mem _ |>.mp hy'
    exact hmod
  · rintro ⟨hx, hmod⟩
    let y : unitGroup v := ⟨x, hx⟩
    refine ⟨y, ?_, rfl⟩
    change unitReduction v n y = 1
    apply Units.ext
    change Ideal.Quotient.mk
      ((IsLocalRing.maximalIdeal (completionIntegers v)) ^ n)
        ((unitGroupEquivIntegersUnits v) y :
          completionIntegers v) = 1
    apply Ideal.Quotient.mk_eq_one_iff_sub_mem _ |>.mpr
    simpa only [y] using hmod

/-- Higher-unit membership in terms of the completion valuation and a uniformizer. -/
theorem mem_higherUnitGroup_iff_valued_le
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    {ϖ : completionIntegers v} (hϖ : Irreducible ϖ) (n : ℕ)
    (x : (v.adicCompletion K)ˣ) :
    x ∈ higherUnitGroup v n ↔ x ∈ unitGroup v ∧
      Valued.v ((x : v.adicCompletion K) - 1) ≤
        Valued.v (ϖ : v.adicCompletion K) ^ n := by
  rw [mem_higherUnitGroup_iff]
  constructor
  · rintro ⟨hx, hmod⟩
    refine ⟨hx, ?_⟩
    change (((unitGroupEquivIntegersUnits v) ⟨x, hx⟩ :
        (completionIntegers v)ˣ) : completionIntegers v) - 1 ∈
      (((IsLocalRing.maximalIdeal (completionIntegers v)) ^ n :
        Ideal (completionIntegers v)) : Set (completionIntegers v)) at hmod
    rw [Valuation.Integers.maximalIdeal_pow_eq_setOfPred_le_v_algebraMap_pow
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers K v) hϖ n] at hmod
    exact hmod
  · rintro ⟨hx, hval⟩
    refine ⟨hx, ?_⟩
    change (((unitGroupEquivIntegersUnits v) ⟨x, hx⟩ :
        (completionIntegers v)ˣ) : completionIntegers v) - 1 ∈
      (((IsLocalRing.maximalIdeal (completionIntegers v)) ^ n :
        Ideal (completionIntegers v)) : Set (completionIntegers v))
    rw [Valuation.Integers.maximalIdeal_pow_eq_setOfPred_le_v_algebraMap_pow
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers K v) hϖ n]
    exact hval

/-- A finite completion has a uniformizer of normalized valuation $\exp(-1)$, the image of a
uniformizer of the ring of integers. -/
theorem exists_completion_uniformizer
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ ϖ : completionIntegers v,
      Irreducible ϖ ∧ Valued.v (ϖ : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  let ϖ : completionIntegers v := algebraMap (NumberField.RingOfIntegers K) _ π
  have hval : Valued.v (ϖ : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
    change Valued.v (π : v.adicCompletion K) = _
    rw [v.valuedAdicCompletion_eq_valuation' (π : K), v.valuation_of_algebraMap]
    exact hπ
  have hrange : WithZero.exp (-1 : ℤ) ∈ Set.range
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) := ⟨(ϖ : v.adicCompletion K), hval⟩
  have hgen := Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range hrange
  have hunif : (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).IsUniformizer
      (ϖ : v.adicCompletion K) := by
    rw [Valuation.IsUniformizer.iff, hgen]
    exact hval
  have hmax : IsLocalRing.maximalIdeal (completionIntegers v) = Ideal.span {ϖ} := by
    exact Valuation.IsUniformizer.is_generator hunif
  exact ⟨ϖ, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hmax, hval⟩

/-- Every finite completion has a unit of valuation `exp(-1)`; the unit form of
`exists_completion_uniformizer`. -/
theorem exists_valued_eq_exp_neg_one (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ ϖ : (v.adicCompletion K)ˣ,
      Valued.v (ϖ : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨ϖ, -, hϖ⟩ := exists_completion_uniformizer v
  refine ⟨Units.mk0 (ϖ : v.adicCompletion K) fun h ↦ ?_, hϖ⟩
  rw [h, map_zero] at hϖ
  exact WithZero.exp_ne_zero hϖ.symm

/-- A chosen uniformizer in the global ring of integers at `v`. -/
def integralUniformizer (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    NumberField.RingOfIntegers K :=
  (v.intValuation_exists_uniformizer).choose

/-- The chosen global uniformizer has normalized valuation `exp(-1)`. -/
theorem valued_integralUniformizer
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    v.intValuation (integralUniformizer v) = WithZero.exp (-1 : ℤ) :=
  (v.intValuation_exists_uniformizer).choose_spec

/-- A chosen uniformizer `ϖ_v` of the completion at a finite place `v`. -/
def uniformizer (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (v.adicCompletion K)ˣ := by
  have hπ : (integralUniformizer v : K) ≠ 0 := by
    intro hz
    have hz' : integralUniformizer v = 0 :=
      RingOfIntegers.coe_injective (by simpa using hz)
    have hv := valued_integralUniformizer v
    rw [hz', map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  exact Units.mk0 (algebraMap K (v.adicCompletion K) (integralUniformizer v : K))
    ((algebraMap K (v.adicCompletion K)).injective.ne hπ)

/-- The chosen uniformizer has valuation `exp(-1)`. -/
@[simp]
theorem valued_uniformizer (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Valued.v (uniformizer v : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
  change Valued.v ((integralUniformizer v : K) : v.adicCompletion K) = _
  rw [v.valuedAdicCompletion_eq_valuation', v.valuation_of_algebraMap]
  exact valued_integralUniformizer v

/-- Multiplying a local unit by the matching uniformizer power makes it integral. -/
theorem mul_zpow_uniformizer_mem_unitGroup
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (x y : (v.adicCompletion K)ˣ)
    (hy : Valued.v (y : v.adicCompletion K) = WithZero.exp (-1 : ℤ)) :
    x * y ^ WithZero.log (Valued.v (x : v.adicCompletion K)) ∈ unitGroup v := by
  let k : ℤ := WithZero.log (Valued.v (x : v.adicCompletion K))
  have hx0 : Valued.v (x : v.adicCompletion K) ≠ 0 := by
    simp [Units.ne_zero x]
  have hxval : Valued.v (x : v.adicCompletion K) = WithZero.exp k :=
    (WithZero.exp_log hx0).symm
  apply (mem_unitGroup_iff_valued v _).mpr
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hxval, hy,
    ← WithZero.exp_zsmul, ← WithZero.exp_add]
  simp [k]

/-! ### The valuation of a unit -/

section Valuation

variable {L : Type*} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L))

/-- The valuation of a unit of $L_w$, as an element of `Multiplicative ℤ`: the unit of
`ℤᵐ⁰ = WithZero (Multiplicative ℤ)` that is its valuation. A uniformizer goes to `ofAdd (-1)`. -/
def unitsValuation : (w.adicCompletion L)ˣ →* Multiplicative ℤ :=
  WithZero.unitsWithZeroEquiv.toMonoidHom.comp
    (Units.map (Valued.v : Valuation (w.adicCompletion L) ℤᵐ⁰).toMonoidWithZeroHom.toMonoidHom)

/-- The valuation of a unit, seen in `ℤᵐ⁰`, is its valuation. -/
@[simp]
theorem coe_unitsValuation (x : (w.adicCompletion L)ˣ) :
    ((unitsValuation w x : Multiplicative ℤ) : ℤᵐ⁰) = Valued.v (x : w.adicCompletion L) := by
  exact WithZero.coe_unitsWithZeroEquiv_eq_units_val _

/-- The valuation of units is onto `ℤ`. -/
theorem unitsValuation_surjective : Function.Surjective (unitsValuation w) := by
  intro n
  obtain ⟨x, hx⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective L w
    (n : ℤᵐ⁰)
  have hx0 : x ≠ 0 := by
    intro h
    have hn : (n : ℤᵐ⁰) = 0 := by simpa [h] using hx.symm
    exact WithZero.coe_ne_zero hn
  refine ⟨Units.mk0 x hx0, ?_⟩
  apply WithZero.coe_injective
  simpa only [coe_unitsValuation, Units.val_mk0] using hx

/-- A unit has valuation `0` exactly when it is integral: the kernel of the valuation is $U_w$. -/
theorem unitsValuation_eq_one_iff {x : (w.adicCompletion L)ˣ} :
    unitsValuation w x = 1 ↔ x ∈ unitGroup w := by
  rw [mem_unitGroup_iff_valued, ← coe_unitsValuation]
  exact WithZero.coe_injective.eq_iff.symm

/-- The normalized valuation of the chosen uniformizer is `-1`. -/
theorem unitsValuation_uniformizer
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    unitsValuation v (uniformizer v) = Multiplicative.ofAdd (-1 : ℤ) := by
  apply WithZero.coe_injective
  rw [coe_unitsValuation, valued_uniformizer]
  rfl

/-- Choosing an element mapping to $1$ in the additive value group splits
$K_v^\times \cong U_v \times \mathbb Z$.
Milne, *Class Field Theory*, Chapter VII, Proposition 6.8, proof. -/
def unitsEquivUnitGroupProd (v : HeightOneSpectrum (𝓞 L)) :
    (v.adicCompletion L)ˣ ≃* unitGroup v × Multiplicative ℤ := by
  let π := (uniformizer v)⁻¹
  have hπ : unitsValuation v π = Multiplicative.ofAdd (1 : ℤ) := by
    dsimp [π]
    rw [map_inv, unitsValuation_uniformizer]
    rfl
  let f := (unitGroup v).subtype.coprod (zpowersHom _ π)
  have hf (x : unitGroup v × Multiplicative ℤ) :
      unitsValuation v (f x) = x.2 := by
    change unitsValuation v (x.1 * π ^ x.2.toAdd) = x.2
    rw [map_mul, map_zpow, (unitsValuation_eq_one_iff v).mpr x.1.property, hπ, one_mul]
    change Multiplicative.ofAdd (x.2.toAdd * 1) = x.2
    rw [mul_one]
    rfl
  exact (MulEquiv.ofBijective f ⟨by
    intro x y hxy
    have hval : x.2 = y.2 := by rw [← hf x, ← hf y, hxy]
    apply Prod.ext _ hval
    apply Subtype.ext
    apply mul_right_cancel (b := π ^ x.2.toAdd)
    change (x.1 : (v.adicCompletion L)ˣ) * π ^ x.2.toAdd =
      y.1 * π ^ y.2.toAdd at hxy
    simpa only [hval] using hxy, by
    intro x
    let m := unitsValuation v x
    have hmem : x / π ^ m.toAdd ∈ unitGroup v := by
      convert mul_zpow_uniformizer_mem_unitGroup v x (uniformizer v) (valued_uniformizer v) using 1
      have hm : WithZero.log (Valued.v (x : v.adicCompletion L)) = m.toAdd := by
        rw [← coe_unitsValuation]
        exact WithZero.log_exp _
      simp [π, div_eq_mul_inv, hm]
    refine ⟨(⟨x / π ^ m.toAdd, hmem⟩, m), ?_⟩
    change x / π ^ m.toAdd * π ^ m.toAdd = x
    exact div_mul_cancel x _⟩).symm

end Valuation

/-- A subgroup of $K_v^\times$ containing the integral units and an element of valuation
$\exp(-1)$ is everything: $K_v^\times=\pi^{\mathbb Z}U_v$. -/
theorem eq_top_of_unitGroup_le (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    {H : Subgroup (v.adicCompletion K)ˣ} (hU : unitGroup v ≤ H) {y : (v.adicCompletion K)ˣ}
    (hy : Valued.v (y : v.adicCompletion K) = WithZero.exp (-1 : ℤ)) (hyH : y ∈ H) : H = ⊤ := by
  apply (Subgroup.eq_top_iff' H).mpr
  intro x
  let k : ℤ := WithZero.log (Valued.v (x : v.adicCompletion K))
  have hunit : x * y ^ k ∈ unitGroup v :=
    mul_zpow_uniformizer_mem_unitGroup v x y hy
  have hmem : x * y ^ k ∈ H := hU hunit
  exact (H.mul_mem_cancel_right (H.zpow_mem hyH k)).mp hmem


/-- Higher-unit membership in terms of the normalized valuation: `x` has valuation `1` and
`x - 1` has valuation at most `exp(-n)`. -/
theorem mem_higherUnitGroup_iff_valued
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) (n : ℕ)
    (x : (v.adicCompletion K)ˣ) :
    x ∈ higherUnitGroup v n ↔
      Valued.v (x : v.adicCompletion K) = 1 ∧
        Valued.v ((x : v.adicCompletion K) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  obtain ⟨ϖ, hϖ, hval⟩ := exists_completion_uniformizer v
  have hpow : Valued.v (ϖ : v.adicCompletion K) ^ n =
      WithZero.exp (-(n : ℤ)) := by
    rw [hval, ← WithZero.exp_nsmul]
    simp
  rw [mem_higherUnitGroup_iff_valued_le v hϖ n]
  rw [mem_unitGroup_iff_valued, hpow]

/-- A global element lies in a higher unit group exactly when `v(c) = 1` and
`v(c - 1) ≤ exp(-n)`. -/
theorem units_map_mem_higherUnitGroup_iff
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) (n : ℕ) (c : Kˣ) :
    Units.map (algebraMap K (v.adicCompletion K)) c ∈ higherUnitGroup v n ↔
      v.valuation K (c : K) = 1 ∧
        v.valuation K ((c : K) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  rw [mem_higherUnitGroup_iff_valued]
  change Valued.v ((c : K) : v.adicCompletion K) = 1 ∧
    Valued.v (((c : K) : v.adicCompletion K) - 1) ≤ _ ↔ _
  rw [v.valuedAdicCompletion_eq_valuation' (c : K)]
  have hsub : Valued.v (((c : K) : v.adicCompletion K) - 1) =
      v.valuation K ((c : K) - 1) := by
    have hmap : (((c : K) - 1 : K) : v.adicCompletion K) =
        ((c : K) : v.adicCompletion K) - 1 := by
      change algebraMap K (v.adicCompletion K) ((c : K) - 1) =
        algebraMap K (v.adicCompletion K) (c : K) - 1
      simp
    rw [← hmap]
    exact v.valuedAdicCompletion_eq_valuation' _
  rw [hsub]

/-- Higher-unit membership in the restricted valuation used by the completion topology. -/
private theorem mem_higherUnitGroup_iff_restrict_le
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    {ϖ : completionIntegers v} (hϖ : Irreducible ϖ) (n : ℕ)
    (x : (v.adicCompletion K)ˣ) :
    x ∈ higherUnitGroup v n ↔ x ∈ unitGroup v ∧
      Valued.v.restrict ((x : v.adicCompletion K) - 1) ≤
        Valued.v.restrict (ϖ : v.adicCompletion K) ^ n := by
  rw [mem_higherUnitGroup_iff_valued_le v hϖ n]
  simp only [← map_pow, Valuation.restrict_le_iff]

/-- Every finite higher unit group is open. -/
theorem isOpen_higherUnitGroup
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) (n : ℕ) :
    IsOpen (higherUnitGroup v n : Set (v.adicCompletion K)ˣ) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (completionIntegers v)
  let r := Valued.v.restrict ((ϖ : v.adicCompletion K) ^ n)
  have hϖ0 : (ϖ : v.adicCompletion K) ≠ 0 := by
    intro h
    apply hϖ.ne_zero
    exact Subtype.ext h
  have hvϖ : Valued.v (ϖ : v.adicCompletion K) ≠ 0 := by
    simpa using hϖ0
  have hvpow : Valued.v ((ϖ : v.adicCompletion K) ^ n) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero n hvϖ
  have hr : r ≠ 0 := by
    simpa only [r, ne_eq, Valuation.restrict_eq_zero_iff] using hvpow
  have hball0 := Valued.isOpen_closedBall (v.adicCompletion K) hr
  have hcontinuous : Continuous
      (fun x : (v.adicCompletion K)ˣ ↦ (x : v.adicCompletion K) - 1) :=
    Units.continuous_val.sub continuous_const
  have hball : IsOpen {x : (v.adicCompletion K)ˣ |
      Valued.v.restrict ((x : v.adicCompletion K) - 1) ≤
        Valued.v.restrict (ϖ : v.adicCompletion K) ^ n} := by
    simpa only [Set.preimage_ofPred_eq, r, map_pow] using hball0.preimage hcontinuous
  have hset : (higherUnitGroup v n : Set (v.adicCompletion K)ˣ) =
      (unitGroup v : Set (v.adicCompletion K)ˣ) ∩
        {x | Valued.v.restrict ((x : v.adicCompletion K) - 1) ≤
          Valued.v.restrict (ϖ : v.adicCompletion K) ^ n} := by
    ext x
    change (x ∈ higherUnitGroup v n ↔ x ∈ unitGroup v ∧
      Valued.v.restrict ((x : v.adicCompletion K) - 1) ≤
        Valued.v.restrict (ϖ : v.adicCompletion K) ^ n)
    exact mem_higherUnitGroup_iff_restrict_le v hϖ n x
  rw [hset]
  exact (isOpen_unitGroup v).inter hball

/-- The level-zero higher unit group is the full integral-unit group. -/
@[simp]
theorem higherUnitGroup_zero
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    higherUnitGroup v 0 = unitGroup v := by
  apply le_antisymm (higherUnitGroup_le_unitGroup v 0)
  intro x hx
  rw [mem_higherUnitGroup_iff]
  exact ⟨hx, by simp⟩

/-- The higher unit groups decrease as their level increases. -/
theorem higherUnitGroup_anti
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Antitone (higherUnitGroup v) := by
  intro a b hab x hx
  rw [mem_higherUnitGroup_iff] at hx ⊢
  obtain ⟨hxunit, hxmod⟩ := hx
  refine ⟨hxunit, ?_⟩
  exact (Ideal.pow_le_pow_right hab) hxmod

/-- The higher unit groups form a basis of neighbourhoods of one: every neighbourhood of one
in $K_v^\times$ contains some $U_v^{(n)}$. [83, Neukirch (1999), Chapter II, §3, p. 122];
Milne, *Class Field Theory*, Chapter I, 1.9. -/
theorem exists_higherUnitGroup_subset
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    {U : Set (v.adicCompletion K)ˣ} (hU : U ∈ nhds 1) :
    ∃ n, (higherUnitGroup v n : Set (v.adicCompletion K)ˣ) ⊆ U := by
  rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap] at hU
  obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.mp hU
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hV
  obtain ⟨n, hn⟩ := WithZero.exists_exp_neg_natCast_lt
    (x := MonoidWithZeroHom.ValueGroup₀.embedding γ.1) (by simp)
  refine ⟨n, fun x hx ↦ hVU ?_⟩
  apply hγ
  change Valued.v.restrict ((x : v.adicCompletion K) - 1) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  exact ((mem_higherUnitGroup_iff_valued v n x).mp hx).2.trans_lt hn

end FinitePlace

end SIC

end
