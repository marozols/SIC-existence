/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.Topology.Algebra.RestrictedProduct.Units
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Topology.Algebra.Group.Units

/-!
# Topology of units of restricted products

The units of a restricted product of topological monoids as a topological group, the continuity of
single-component insertions, and the homeomorphism with the restricted product of the unit groups.

## The argument

On a principal restricted-product chart, continuity of the units equivalence reduces to
continuity of each coordinate and its inverse. Every unit in the cofinite restricted product
belongs to a chart on which both it and its inverse satisfy the local conditions. These charts
embed openly, so continuity on them proves continuity globally in both directions. A
single-component insertion factors through the chart supported away from that component. This
complements Mathlib's algebraic `RestrictedProduct.unitsEquiv` and is used by the idèle component
homeomorphism.
-/

noncomputable section

open Filter Set Topology
open scoped RestrictedProduct

namespace SIC

/-! ### Units of a restricted product -/

namespace RestrictedProduct

variable {ι : Type*} (R : ι → Type*) [∀ i, Monoid (R i)]
  (B : ∀ i, Submonoid (R i)) [∀ i, TopologicalSpace (R i)]

/-- The restricted product before taking units, with an arbitrary indexing filter. -/
private abbrev Base (𝓕 : Filter ι) := Πʳ i, [R i, B i]_[𝓕]

/-- The corresponding restricted product of the local unit groups. -/
private abbrev LocalUnits (𝓕 : Filter ι) :=
  Πʳ i, [(R i)ˣ, (Submonoid.ofClass (B i)).units]_[𝓕]

/-- Inclusion from a smaller restricted-product chart as a monoid homomorphism. -/
private def inclusionHom {𝓕 𝓖 : Filter ι} (h : 𝓕 ≤ 𝓖) :
    Base R B 𝓖 →* Base R B 𝓕 where
  toFun := _root_.RestrictedProduct.inclusion R (fun i ↦ (B i : Set (R i))) h
  map_one' := rfl
  map_mul' _ _ := rfl

/-- On a principal chart, the restricted-product units equivalence is continuous. -/
private theorem unitsEquiv_continuous_principal (T : Set ι) :
    Continuous
      (_root_.RestrictedProduct.unitsEquiv R :
        (Base R B (𝓟 T))ˣ → LocalUnits R B (𝓟 T)) := by
  rw [_root_.RestrictedProduct.continuous_rng_of_principal_iff_forall]
  intro i
  apply Units.continuous_iff.mpr
  constructor
  · simpa [Function.comp_def] using
      (_root_.RestrictedProduct.continuous_eval i).comp
        (Units.continuous_val : Continuous (Units.val :
          (Base R B (𝓟 T))ˣ → Base R B (𝓟 T)))
  · change Continuous (fun x : (Base R B (𝓟 T))ˣ ↦ (x.inv : Base R B (𝓟 T)) i)
    simpa [Function.comp_def] using
      (_root_.RestrictedProduct.continuous_eval i).comp
        (Units.continuous_coe_inv :
          Continuous (fun u : (Base R B (𝓟 T))ˣ ↦ (↑u⁻¹ : Base R B (𝓟 T))))

/-- The inverse restricted-product units equivalence is continuous on a principal chart. -/
private theorem unitsEquiv_symm_continuous_principal (T : Set ι) :
    Continuous
      ((_root_.RestrictedProduct.unitsEquiv R :
        (Base R B (𝓟 T))ˣ ≃* LocalUnits R B (𝓟 T)).symm) := by
  apply Units.continuous_iff.mpr
  constructor
  · rw [_root_.RestrictedProduct.continuous_rng_of_principal_iff_forall]
    intro i
    change Continuous (fun x : LocalUnits R B (𝓟 T) ↦ (x i).val)
    simpa [Function.comp_def] using
      (Units.continuous_val : Continuous (Units.val : (R i)ˣ → R i)).comp
        (_root_.RestrictedProduct.continuous_eval i :
          Continuous (fun x : LocalUnits R B (𝓟 T) ↦ x i))
  · rw [_root_.RestrictedProduct.continuous_rng_of_principal_iff_forall]
    intro i
    change Continuous (fun x : LocalUnits R B (𝓟 T) ↦ (x i).inv)
    simpa [Function.comp_def] using
      (Units.continuous_coe_inv : Continuous (fun u : (R i)ˣ ↦ (↑u⁻¹ : R i))).comp
        (_root_.RestrictedProduct.continuous_eval i :
          Continuous (fun x : LocalUnits R B (𝓟 T) ↦ x i))

/-- Inclusion of the units of a principal chart into the units of the cofinite product. -/
private def unitInclusionHom (T : Set ι) (hT : cofinite ≤ 𝓟 T) :
    (Base R B (𝓟 T))ˣ →* (Base R B cofinite)ˣ :=
  Units.map (inclusionHom R B hT)

omit [∀ i, TopologicalSpace (R i)] in
/-- Every unit of the cofinite restricted product belongs to a principal units chart. -/
private theorem exists_unitInclusion_eq (x : (Base R B cofinite)ˣ) :
    ∃ (T : Set ι) (hT : cofinite ≤ 𝓟 T) (y : (Base R B (𝓟 T))ˣ),
      unitInclusionHom R B T hT y = x := by
  let T : Set ι := {i | x.val i ∈ B i ∧ x.inv i ∈ B i}
  have hT_mem : T ∈ cofinite := x.val.2.and x.inv.2
  have hT : cofinite ≤ 𝓟 T := le_principal_iff.mpr hT_mem
  let yval : Base R B (𝓟 T) :=
    ⟨x.val.1, (show ∀ i ∈ T, x.val i ∈ B i from fun _ hi ↦ hi.1)⟩
  let yinv : Base R B (𝓟 T) :=
    ⟨x.inv.1, (show ∀ i ∈ T, x.inv i ∈ B i from fun _ hi ↦ hi.2)⟩
  let y : (Base R B (𝓟 T))ˣ :=
    ⟨yval, yinv,
      by
        ext i
        change x.val.1 i * x.inv.1 i = (1 : Base R B cofinite).1 i
        exact congrArg (fun z : Base R B cofinite ↦ z.1 i) x.val_inv,
      by
        ext i
        change x.inv.1 i * x.val.1 i = (1 : Base R B cofinite).1 i
        exact congrArg (fun z : Base R B cofinite ↦ z.1 i) x.inv_val⟩
  exact ⟨T, hT, y, by ext i; rfl⟩

/-- A principal units chart is open in the units of the cofinite restricted product. -/
private theorem unitInclusion_isOpenEmbedding
    [hBopen : Fact (∀ i, IsOpen (B i : Set (R i)))]
    (T : Set ι) (hT : cofinite ≤ 𝓟 T) :
    IsOpenEmbedding (unitInclusionHom R B T hT) := by
  have hbase : IsOpenEmbedding (inclusionHom R B hT) :=
    _root_.RestrictedProduct.isOpenEmbedding_inclusion_principal hBopen.out hT
  exact .of_isEmbedding_isOpenMap hbase.isEmbedding.units_map
    (Units.isOpenMap_map hbase.injective hbase.isOpenMap)

/-- Continuity on every principal units chart implies global continuity. -/
private theorem continuous_units_of_continuous_principal
    [Fact (∀ i, IsOpen (B i : Set (R i)))]
    {X : Type*} [TopologicalSpace X] {f : (Base R B cofinite)ˣ → X}
    (hf : ∀ (T : Set ι) (hT : cofinite ≤ 𝓟 T),
      Continuous (f ∘ unitInclusionHom R B T hT)) :
    Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨T, hT, y, hy⟩ := exists_unitInclusion_eq R B x
  have hchart := unitInclusion_isOpenEmbedding R B T hT
  rw [← hy]
  exact hchart.continuousAt_iff.mp (hf T hT).continuousAt

/-- The forward units equivalence is continuous on the cofinite restricted product. -/
private theorem unitsEquiv_continuous_cofinite
    [Fact (∀ i, IsOpen (B i : Set (R i)))] :
    Continuous
      (_root_.RestrictedProduct.unitsEquiv R :
        (Base R B cofinite)ˣ → LocalUnits R B cofinite) := by
  apply continuous_units_of_continuous_principal R B
  intro T hT
  have hlocal : Continuous
      (_root_.RestrictedProduct.inclusion (fun i ↦ (R i)ˣ)
        (fun i ↦ ((Submonoid.ofClass (B i)).units : Set (R i)ˣ)) hT ∘
          (_root_.RestrictedProduct.unitsEquiv R :
            (Base R B (𝓟 T))ˣ → LocalUnits R B (𝓟 T))) :=
    (_root_.RestrictedProduct.continuous_inclusion hT).comp
      (unitsEquiv_continuous_principal R B T)
  convert hlocal using 1
  funext x
  apply _root_.RestrictedProduct.ext
  intro i
  rfl

/-- The inverse units equivalence is continuous on the cofinite restricted product. -/
private theorem unitsEquiv_symm_continuous_cofinite
    [Fact (∀ i, IsOpen (B i : Set (R i)))] :
    Continuous
      ((_root_.RestrictedProduct.unitsEquiv R :
        (Base R B cofinite)ˣ ≃* LocalUnits R B cofinite).symm) := by
  rw [_root_.RestrictedProduct.continuous_dom]
  intro T hT
  have hlocal : Continuous
      (unitInclusionHom R B T hT ∘
        (_root_.RestrictedProduct.unitsEquiv R :
          (Base R B (𝓟 T))ˣ ≃* LocalUnits R B (𝓟 T)).symm) :=
    (unitInclusion_isOpenEmbedding R B T hT).continuous.comp
      (unitsEquiv_symm_continuous_principal R B T)
  convert hlocal using 1
  funext x
  apply Units.ext
  apply _root_.RestrictedProduct.ext
  intro i
  rfl

/-- The algebraic equivalence between restricted-product units and the restricted product of
local unit groups, upgraded to a continuous multiplicative equivalence. -/
def unitsContinuousMulEquiv [Fact (∀ i, IsOpen (B i : Set (R i)))] :
    (Πʳ i, [R i, B i])ˣ ≃ₜ*
      Πʳ i, [(R i)ˣ, (Submonoid.ofClass (B i)).units] := by
  exact
    { __ := _root_.RestrictedProduct.unitsEquiv R
      continuous_toFun := unitsEquiv_continuous_cofinite R B
      continuous_invFun := unitsEquiv_symm_continuous_cofinite R B }

variable {S : ι → Type*} {G : ι → Type*} [∀ i, SetLike (S i) (G i)]
  (A : ∀ i, S i) [∀ i, One (G i)] [∀ i, OneMemClass (S i) (G i)]
  [∀ i, TopologicalSpace (G i)] [DecidableEq ι]

/-- Inserting one component into a cofinite restricted product is continuous. -/
theorem continuous_mulSingle (i : ι) :
    Continuous (_root_.RestrictedProduct.mulSingle A i) := by
  have hi : cofinite ≤ 𝓟 ({i}ᶜ : Set ι) := le_principal_iff.mpr (by simp)
  let f : G i → Πʳ j, [G j, A j]_[𝓟 ({i}ᶜ : Set ι)] := fun x ↦
    ⟨Pi.mulSingle i x, by
      intro j hj
      change Pi.mulSingle i x j ∈ A j
      rw [Pi.mulSingle_eq_of_ne]
      · exact one_mem (A j)
      · simpa using hj⟩
  have hf : Continuous f := by
    apply _root_.RestrictedProduct.continuous_rng_of_principal.mpr
    exact _root_.continuous_mulSingle i
  have hincl := (_root_.RestrictedProduct.continuous_inclusion hi).comp hf
  have heq : _root_.RestrictedProduct.mulSingle A i =
      _root_.RestrictedProduct.inclusion G (fun j ↦ (A j : Set (G j))) hi ∘ f := by
    funext x
    rfl
  rw [heq]
  exact hincl

end RestrictedProduct

end SIC

end
