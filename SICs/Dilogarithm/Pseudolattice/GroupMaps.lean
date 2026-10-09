/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Dilogarithm.Pseudolattice.Group

/-!
# Homomorphisms between the groups of pseudolattices

The lattice `(ε - 1)⁻¹I`, the residue homomorphism from it onto `G_{I,ε}` with kernel `I`, the
homomorphism `G_{I,ε} → G_{J,ε}` induced by an inclusion `I ⊆ J`, the isomorphism
`G_{I,ε} ≅ G_{αI,ε}` induced by a homothety, and the characters of `G_{I,ε}` induced by
characters of `K` trivial on `I`.

This module supplies the group maps of [RW26b, Radchenko, Wheeler (2026b), Section 5, Lemmas
2–3 and Theorem 5]: the natural map `φ : G_{I,ε} → G_{J,ε}` of Lemma 2, the characters of the
chain of Lemma 3, and the homothety invariance used in Theorem 5. The group `G_{I,ε}` is the
model `finiteDilogGroup γ` of fixed residues of `SICs.Dilogarithm.Pseudolattice.Group`, on which
the finite quantum dilogarithm of the period lives; the maps are defined through the residue
map `x ↦ residue x` of `x ∈ (ε - 1)⁻¹I`.

## The argument

*Residues.* The residue map is additive on `(ε - 1)⁻¹I` (`residue_add`), lands in
`finiteDilogGroup γ` (`residue_mem`), is onto (`exists_residue_eq`), and has kernel `I`
(`residue_eq_zero_iff`): it presents `G_{I,ε} = (ε - 1)⁻¹I/I`.

*Induced maps.* A homomorphism `K → K` carrying `(ε - 1)⁻¹I` into `(ε - 1)⁻¹J` and `I` into `J`
descends along the two residue maps: the inclusion for `I ⊆ J`, and multiplication by `α` for
`J = αI`, which is bijective with inverse multiplication by `α⁻¹`. A character `Ψ` of `K` trivial
on `I` descends to a character of `G_{I,ε}`, compatibly with the inclusion maps.

*The order.* `|G_{I,ε}| = N = Tr ε - 2` depends only on `ε`: the matrices of `ε` on two bases
have the trace `ε + ε⁻¹` at the first real place (`cast_finiteDilogOrder_eq`).
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
variable {F : RealQuadraticFieldData K}

namespace PseudolatticeBasis

/-! ### The lattice `(ε - 1)⁻¹I` -/

/-- **The lattice `(ε - 1)⁻¹I`** of a pseudolattice, whose quotient by `I` is the group
`G_{I,ε}` of [RW26b, Radchenko, Wheeler (2026b), Definition 1]. -/
def torsionLattice (B : PseudolatticeBasis F) (ε : K) : Submodule ℤ K :=
  B.submodule.comap (LinearMap.mulLeft ℤ (ε - 1))

/-- `I ⊆ J` gives `(ε - 1)⁻¹I ⊆ (ε - 1)⁻¹J`. -/
theorem torsionLattice_mono {B B' : PseudolatticeBasis F} {ε : K}
    (hle : B.submodule ≤ B'.submodule) : B.torsionLattice ε ≤ B'.torsionLattice ε := by
  exact Submodule.comap_mono hle

/-- A homothety `J = αI` carries `(ε - 1)⁻¹I` into `(ε - 1)⁻¹J`. -/
theorem mul_mem_torsionLattice {B B₀ : PseudolatticeBasis F} {ε α : K}
    (hI : ∀ y, y ∈ B.submodule ↔ ∃ z ∈ B₀.submodule, y = α * z) {x : K}
    (hx : x ∈ B₀.torsionLattice ε) : α * x ∈ B.torsionLattice ε := by
  apply (hI _).2
  refine ⟨(ε - 1) * x, hx, ?_⟩
  change (ε - 1) * (α * x) = α * ((ε - 1) * x)
  ring

/-- Multiplication by `α` identifies the two torsion lattices for `smulEquiv`. -/
private def torsionMulEquiv {B B₀ : PseudolatticeBasis F} {ε α : K} (hα : α ≠ 0)
    (hI : ∀ y, y ∈ B.submodule ↔ ∃ z ∈ B₀.submodule, y = α * z) :
    B₀.torsionLattice ε ≃+ B.torsionLattice ε := by
  have hback {y : K} (hy : y ∈ B.torsionLattice ε) :
      α⁻¹ * y ∈ B₀.torsionLattice ε := by
    obtain ⟨z, hz, heq⟩ := (hI _).1 hy
    change (ε - 1) * y = α * z at heq
    change (ε - 1) * (α⁻¹ * y) ∈ B₀.submodule
    have heq' : (ε - 1) * (α⁻¹ * y) = z := by
      calc
        (ε - 1) * (α⁻¹ * y) = α⁻¹ * ((ε - 1) * y) := by ring
        _ = z := by rw [heq]; simp [hα]
    rw [heq']
    exact hz
  refine {
    toFun := fun x => ⟨α * x, mul_mem_torsionLattice hI x.2⟩
    invFun := fun y => ⟨α⁻¹ * y, hback y.2⟩
    left_inv := ?_
    right_inv := ?_
    map_add' := ?_
  }
  · intro x
    apply Subtype.ext
    change α⁻¹ * (α * (x : K)) = x
    simp [hα]
  · intro y
    apply Subtype.ext
    change α * (α⁻¹ * (y : K)) = y
    simp [hα]
  · intro x y
    apply Subtype.ext
    exact mul_add α (x : K) y

namespace IsPeriod

variable {B : PseudolatticeBasis F} {ε : K} (h : B.IsPeriod ε)

/-- The unit equation `(ε - 1)² = Nε` used to bound each step of the saturation chain. -/
theorem sub_one_sq :
    (ε - 1) ^ 2 = (finiteDilogOrder h.matrix : K) * ε := by
  apply (realEmbeddingAt K F.place).injective
  simpa only [map_pow, map_sub, map_one, map_mul, map_natCast,
    ← h.fltDenominator_matrix] using
    h.isAttractiveFixedPoint.denominator_sub_one_sq

/-- If `x ∈ (ε - 1)⁻¹I`, then `x ∈ (εⁿ - 1)⁻¹I`.
Used by `pseudolatticeDilog_valuation_eq_one`. -/
theorem pow_sub_one_mul_mem (h : B.IsPeriod ε) {x : K} (hx : (ε - 1) * x ∈ B.submodule) (n : ℕ) :
    (ε ^ n - 1) * x ∈ B.submodule := by
  induction n with
  | zero => simp
  | succ n ih =>
      have heq : (ε ^ (n + 1) - 1) * x =
          ε * ((ε ^ n - 1) * x) + (ε - 1) * x := by
        ring
      rw [heq]
      exact B.submodule.add_mem (h.mul_mem ih) hx



/-! ### The residue homomorphism

`(ε - 1)⁻¹I → G_{I,ε}`, onto with kernel `I`. -/

/-- **The residue homomorphism** `(ε - 1)⁻¹I → G_{I,ε}`, `x ↦ residue x`, presenting
`G_{I,ε} = (ε - 1)⁻¹I/I` of [RW26b, Radchenko, Wheeler (2026b), Definition 1] as
`finiteDilogGroup γ`. -/
def residueHom : B.torsionLattice ε →+ finiteDilogGroup h.matrix :=
  AddMonoidHom.mk' (fun x => ⟨h.residue x, h.residue_mem x.2⟩) (fun x y => by
    apply Subtype.ext
    exact h.residue_add x.2 y.2)

/-- The underlying vector of `residueHom x` is `residue x`. -/
theorem coe_residueHom (x : B.torsionLattice ε) :
    (h.residueHom x : Fin 2 → ZMod (finiteDilogOrder h.matrix)) = h.residue x :=
  rfl

/-- The residue homomorphism is onto. -/
theorem residueHom_surjective : Function.Surjective h.residueHom := by
  intro y
  obtain ⟨x, hx, hxy⟩ := h.exists_residue_eq y.2
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

/-- The kernel of the residue homomorphism is `I`. -/
theorem residueHom_eq_zero_iff (x : B.torsionLattice ε) :
    h.residueHom x = 0 ↔ (x : K) ∈ B.submodule := by
  rw [← h.residue_eq_zero_iff x.2]
  exact Subtype.ext_iff

/-- A multiple of a residue vanishes exactly when that multiple of the lift lies in `I`. -/
theorem residueHom_nsmul_eq_zero_iff (x : B.torsionLattice ε) (n : ℕ) :
    n • h.residueHom x = 0 ↔ (n : K) * (x : K) ∈ B.submodule := by
  rw [← map_nsmul, h.residueHom_eq_zero_iff]
  simp only [Submodule.coe_smul_of_tower, nsmul_eq_mul]

/-- The order `N = Tr ε - 2` of `G_{I,ε}` depends only on `ε`, as stated after
[RW26b, Radchenko, Wheeler (2026b), Definition 1]. -/
theorem finiteDilogOrder_eq {B' : PseudolatticeBasis F} (h' : B'.IsPeriod ε) :
    finiteDilogOrder h.matrix = finiteDilogOrder h'.matrix := by
  have hh := cast_finiteDilogOrder_eq h.isAttractiveFixedPoint
  have hh' := cast_finiteDilogOrder_eq h'.isAttractiveFixedPoint
  rw [h.fltDenominator_matrix] at hh
  rw [h'.fltDenominator_matrix] at hh'
  exact_mod_cast hh.trans hh'.symm

/-- Shared descent for `inclusionHom`, `residueEquiv`, and `inducedChar`: lift a map on
`(ε - 1)⁻¹I` that vanishes on `I` to `G_{I,ε}`. -/
private def descendResidueHom {G : Type*} [AddGroup G] (f : B.torsionLattice ε →+ G)
    (hf : ∀ x : B.torsionLattice ε, (x : K) ∈ B.submodule → f x = 0) :
    finiteDilogGroup h.matrix →+ G :=
  h.residueHom.liftOfSurjective h.residueHom_surjective ⟨f, by
    intro x hx
    exact AddMonoidHom.mem_ker.mpr
      (hf x ((h.residueHom_eq_zero_iff x).mp (AddMonoidHom.mem_ker.mp hx)))⟩

/-- The defining property of `descendResidueHom` on residues. -/
private theorem descendResidueHom_apply {G : Type*} [AddGroup G]
    (f : B.torsionLattice ε →+ G)
    (hf : ∀ x : B.torsionLattice ε, (x : K) ∈ B.submodule → f x = 0)
    (x : B.torsionLattice ε) : h.descendResidueHom f hf (h.residueHom x) = f x := by
  exact AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x

/-- Descends an additive equivalence preserving lattice membership, for `smulEquiv`. -/
private def residueEquiv {B₀ : PseudolatticeBasis F} (h₀ : B₀.IsPeriod ε)
    (e : B₀.torsionLattice ε ≃+ B.torsionLattice ε)
    (he : ∀ x : B₀.torsionLattice ε,
      (x : K) ∈ B₀.submodule ↔ ((e x : B.torsionLattice ε) : K) ∈ B.submodule) :
    finiteDilogGroup h₀.matrix ≃+ finiteDilogGroup h.matrix := by
  let f := h₀.descendResidueHom (h.residueHom.comp e.toAddMonoidHom)
    (fun x hx => (h.residueHom_eq_zero_iff (e x)).2 ((he x).1 hx))
  let g := h.descendResidueHom (h₀.residueHom.comp e.symm.toAddMonoidHom)
    (fun y hy => (h₀.residueHom_eq_zero_iff (e.symm y)).2 <|
      (he (e.symm y)).2 (by simpa using hy))
  refine {
    toFun := f
    invFun := g
    left_inv := ?_
    right_inv := ?_
    map_add' := f.map_add
  }
  · intro a
    obtain ⟨x, rfl⟩ := h₀.residueHom_surjective a
    rw [show f (h₀.residueHom x) = h.residueHom (e x) from
      h₀.descendResidueHom_apply _ _ x]
    rw [show g (h.residueHom (e x)) = h₀.residueHom (e.symm (e x)) from
      h.descendResidueHom_apply _ _ (e x), e.symm_apply_apply]
  · intro a
    obtain ⟨y, rfl⟩ := h.residueHom_surjective a
    rw [show g (h.residueHom y) = h₀.residueHom (e.symm y) from
      h.descendResidueHom_apply _ _ y]
    rw [show f (h₀.residueHom (e.symm y)) = h.residueHom (e (e.symm y)) from
      h₀.descendResidueHom_apply _ _ (e.symm y), e.apply_symm_apply]

/-- The defining property of `residueEquiv`, used by `smulEquiv_residueHom`. -/
private theorem residueEquiv_residueHom {B₀ : PseudolatticeBasis F} (h₀ : B₀.IsPeriod ε)
    (e : B₀.torsionLattice ε ≃+ B.torsionLattice ε)
    (he : ∀ x : B₀.torsionLattice ε,
      (x : K) ∈ B₀.submodule ↔ ((e x : B.torsionLattice ε) : K) ∈ B.submodule)
    (x : B₀.torsionLattice ε) :
    h.residueEquiv h₀ e he (h₀.residueHom x) = h.residueHom (e x) := by
  simp only [residueEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk]
  exact h₀.descendResidueHom_apply
    (h.residueHom.comp e.toAddMonoidHom)
    (fun x hx => (h.residueHom_eq_zero_iff (e x)).2 ((he x).1 hx)) x

/-! ### Induced homomorphisms

The natural map `G_{I,ε} → G_{J,ε}` for `I ⊆ J`, and the isomorphism of a homothety. -/

/-- **The natural map `φ : G_{I,ε} → G_{J,ε}`** induced by an inclusion `I ⊆ J`, as in
[RW26b, Radchenko, Wheeler (2026b), Section 5, Lemma 2]. -/
def inclusionHom {B' : PseudolatticeBasis F} (h' : B'.IsPeriod ε)
    (hle : B.submodule ≤ B'.submodule) : finiteDilogGroup h.matrix →+ finiteDilogGroup h'.matrix :=
  h.descendResidueHom
    (h'.residueHom.comp (Submodule.inclusion (torsionLattice_mono hle)).toAddMonoidHom)
    (fun x hx => (h'.residueHom_eq_zero_iff
      (Submodule.inclusion (torsionLattice_mono hle) x)).2 (hle hx))

/-- `φ(residue x) = residue x`: the natural map is induced by the inclusion. -/
theorem inclusionHom_residueHom {B' : PseudolatticeBasis F} (h' : B'.IsPeriod ε)
    (hle : B.submodule ≤ B'.submodule) (x : B.torsionLattice ε) :
    h.inclusionHom h' hle (h.residueHom x) =
      h'.residueHom (Submodule.inclusion (torsionLattice_mono hle) x) := by
  exact h.descendResidueHom_apply _ _ x

/-- **The isomorphism `G_{I,ε} ≅ G_{αI,ε}`** induced by multiplication by `α ≠ 0`, used for the
homothety invariance in the proof of [RW26b, Radchenko, Wheeler (2026b), Section 5,
Theorem 5]. -/
def smulEquiv {B₀ : PseudolatticeBasis F} (h₀ : B₀.IsPeriod ε) {α : K} (hα : α ≠ 0)
    (hI : ∀ y, y ∈ B.submodule ↔ ∃ z ∈ B₀.submodule, y = α * z) :
    finiteDilogGroup h₀.matrix ≃+ finiteDilogGroup h.matrix := by
  apply h.residueEquiv h₀ (torsionMulEquiv hα hI)
  intro x
  change (x : K) ∈ B₀.submodule ↔ α * (x : K) ∈ B.submodule
  constructor
  · intro hx
    exact (hI _).2 ⟨x, hx, rfl⟩
  · intro hx
    obtain ⟨z, hz, heq⟩ := (hI _).1 hx
    have hzx : z = (x : K) := by
      apply mul_left_cancel₀ hα
      exact heq.symm
    rwa [hzx] at hz

/-- `e(residue x) = residue (αx)` for the homothety isomorphism. -/
theorem smulEquiv_residueHom {B₀ : PseudolatticeBasis F} (h₀ : B₀.IsPeriod ε) {α : K}
    (hα : α ≠ 0) (hI : ∀ y, y ∈ B.submodule ↔ ∃ z ∈ B₀.submodule, y = α * z)
    (x : B₀.torsionLattice ε) :
    h.smulEquiv h₀ hα hI (h₀.residueHom x) =
      h.residueHom ⟨α * x, mul_mem_torsionLattice hI x.2⟩ := by
  unfold smulEquiv
  rw [h.residueEquiv_residueHom]
  rfl

/-! ### Induced characters

A character of `K` trivial on `I` descends to `G_{I,ε}`. -/

/-- **The character of `G_{I,ε}` induced by a character `Ψ` of `K` trivial on `I`**; every
character of `G_{I,ε}` arises this way (`exists_inducedChar_eq`), as in the trace-dual description
of the characters in the proof of [RW26b, Radchenko, Wheeler (2026b), Section 5, Lemma 3]. -/
def inducedChar (Ψ : AddChar K ℂ) (hΨ : ∀ x ∈ B.submodule, Ψ x = 1) :
    AddChar (finiteDilogGroup h.matrix) ℂ :=
  (Units.coeHom ℂ).compAddChar
    (AddChar.toAddMonoidHomEquiv.symm <|
      h.descendResidueHom
        ((AddChar.toMonoidHomEquiv.symm Ψ.toMonoidHom.toHomUnits).toAddMonoidHom.comp
          (Submodule.subtype (B.torsionLattice ε)).toAddMonoidHom)
        (fun x hx => by
          change Ψ.toMonoidHom.toHomUnits (Multiplicative.ofAdd (x : K)) = (1 : ℂˣ)
          apply Units.ext
          exact hΨ x hx))

/-- `θ_Ψ(residue x) = Ψ(x)`. -/
theorem inducedChar_residueHom (Ψ : AddChar K ℂ) (hΨ : ∀ x ∈ B.submodule, Ψ x = 1)
    (x : B.torsionLattice ε) : h.inducedChar Ψ hΨ (h.residueHom x) = Ψ x := by
  simp only [inducedChar, MonoidHom.coe_compAddChar, Function.comp_apply,
    AddChar.toAddMonoidHomEquiv_symm_apply]
  rw [h.descendResidueHom_apply]
  rfl

/-- Induced characters are compatible with the natural maps: `θ_Ψ^J ∘ φ = θ_Ψ^I`, the
compatibility `θ_{i+1} ∘ φ_i = θ_i` of [RW26b, Radchenko, Wheeler (2026b), Section 5,
Lemma 3]. -/
theorem inducedChar_compAddMonoidHom_inclusionHom {B' : PseudolatticeBasis F}
    (h' : B'.IsPeriod ε) (hle : B.submodule ≤ B'.submodule) (Ψ : AddChar K ℂ)
    (hΨ' : ∀ x ∈ B'.submodule, Ψ x = 1) :
    (h'.inducedChar Ψ hΨ').compAddMonoidHom (h.inclusionHom h' hle) =
      h.inducedChar Ψ (fun x hx => hΨ' x (hle hx)) := by
  apply AddChar.ext
  intro y
  obtain ⟨x, rfl⟩ := h.residueHom_surjective y
  rw [AddChar.compAddMonoidHom_apply, h.inclusionHom_residueHom,
    h'.inducedChar_residueHom, h.inducedChar_residueHom]
  rfl

end IsPeriod

end PseudolatticeBasis

end SIC

end
