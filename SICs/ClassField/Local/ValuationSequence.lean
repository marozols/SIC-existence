/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Completion.FiniteDecomposition
import SICs.ClassField.Local.UnitGroups
import SICs.GroupCohomology.Multiplicative

/-!
# The valuation sequence of a finite completion

For a Galois extension of number fields `L/K` and a finite place `w` of `L` above `v`, the exact
sequence $1 \to U_w \to L_w^\times \to \mathbb Z \to 0$ of $\operatorname{Gal}(L_w/K_v)$-modules
given by the valuation, with the trivial action on $\mathbb Z$.

This is the sequence $0 \to U_L \to L^\times \xrightarrow{\operatorname{ord}_L} \mathbb Z \to 0$ of
Milne, *Class Field Theory*, version 4.03 (2020), Chapter III, §1, "The invariant map", used in the
proof of Chapter III, Lemma 2.5 to compute $h(L^\times) = h(U_L) h(\mathbb Z)$; it is the input of
`SICs.ClassField.Local.NormIndex` and `SICs.ClassField.Local.Unramified`.

## The argument

The valuation homomorphism $L_w^\times \to \mathbb Z$ is constructed in
`SICs.ClassField.Local.UnitGroups`, together with its kernel $U_w$ and surjectivity. Every
automorphism of $L_w/K_v$ preserves the valuation
(`valued_algEquiv_apply`), so it maps $U_w$ to itself and the valuation map is invariant; the
sequence is therefore one of $\operatorname{Gal}(L_w/K_v)$-modules.
The underlying splitting by a chosen uniformizer is in `SICs.ClassField.Local.UnitGroups`.
-/

noncomputable section

open NumberField IsDedekindDomain
open scoped NumberField WithZero SIC.FinitePlace

namespace SIC

namespace FinitePlace

/-! ### The Galois action

The automorphisms of $L_w/K_v$ preserve the valuation, hence the integral units and the valuation
of units. -/

section Galois

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [IsGalois K L]

/-- The automorphisms of $L_w/K_v$ map integral units to integral units. -/
theorem smul_mem_unitGroup (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
    {x : (w.adicCompletion L)ˣ} (hx : x ∈ unitGroup w) : σ • x ∈ unitGroup w := by
  rw [mem_unitGroup_iff_valued] at hx ⊢
  change Valued.v (σ (x : w.adicCompletion L)) = 1
  rw [valued_algEquiv_apply v w σ]
  exact hx

/-- The valuation of units is invariant under the automorphisms of $L_w/K_v$. -/
theorem unitsValuation_smul (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
    (x : (w.adicCompletion L)ˣ) : unitsValuation w (σ • x) = unitsValuation w x := by
  apply WithZero.coe_injective
  simp only [coe_unitsValuation]
  change Valued.v (σ (x : w.adicCompletion L)) = Valued.v (x : w.adicCompletion L)
  exact valued_algEquiv_apply v w σ _

/-- The integral units $U_w$, as a subrepresentation of $L_w^\times$ under
$\operatorname{Gal}(L_w/K_v)$. -/
def unitGroupSubrep :
    Subrepresentation (Representation.ofMulDistribMulAction
      (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) (w.adicCompletion L)ˣ) :=
  Representation.subgroupSubrep (unitGroup w) fun σ _ hx ↦ smul_mem_unitGroup v w σ hx

/-- Membership in the subrepresentation of integral units. -/
@[simp]
theorem mem_unitGroupSubrep (x : Additive (w.adicCompletion L)ˣ) :
    x ∈ unitGroupSubrep v w ↔ x.toMul ∈ unitGroup w := by
  exact Representation.mem_subgroupSubrep x

/-- The valuation $L_w^\times \to \mathbb Z$ as an intertwining map onto the trivial
representation. Milne, *Class Field Theory*, Chapter III, §1. -/
def unitsValuationHom :
    (Representation.ofMulDistribMulAction
      (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
        (w.adicCompletion L)ˣ).IntertwiningMap
      (Representation.trivial ℤ
        (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) ℤ) where
  toFun x := Multiplicative.toAdd (unitsValuation w x.toMul)
  map_add' x y := by
    simp only [toMul_add, map_mul, toAdd_mul]
  map_smul' n x := by
    simp only [toMul_zsmul, map_zpow, toAdd_zpow, RingHom.id_apply]
  isIntertwining' σ := by
    ext x
    simp only [LinearMap.comp_apply, Representation.ofMulDistribMulAction_apply_apply,
      Representation.trivial_apply]
    exact congrArg Multiplicative.toAdd (unitsValuation_smul v w σ x.toMul)

/-- The valuation map sends a unit to its integer valuation. -/
@[simp]
theorem unitsValuationHom_apply (x : Additive (w.adicCompletion L)ˣ) :
    unitsValuationHom v w x = Multiplicative.toAdd (unitsValuation w x.toMul) := by
  rfl

/-- The valuation map onto $\mathbb Z$ is surjective. -/
theorem unitsValuationHom_surjective : Function.Surjective (unitsValuationHom v w) := by
  intro n
  obtain ⟨x, hx⟩ := unitsValuation_surjective w (Multiplicative.ofAdd n)
  refine ⟨Additive.ofMul x, ?_⟩
  change (unitsValuation w x).toAdd = n
  rw [hx]
  rfl

/-- The sequence $1 \to U_w \to L_w^\times \to \mathbb Z \to 0$ is exact at $L_w^\times$.
Milne, *Class Field Theory*, Chapter III, §1. -/
theorem exact_unitGroupSubrep_unitsValuationHom :
    Function.Exact (Representation.Subrepresentation.subtype (unitGroupSubrep v w))
      (unitsValuationHom v w) := by
  intro x
  have hker : unitsValuationHom v w x = 0 ↔ x ∈ unitGroupSubrep v w := by
    rw [unitsValuationHom_apply, mem_unitGroupSubrep]
    change (unitsValuation w x.toMul).toAdd = (1 : Multiplicative ℤ).toAdd ↔
      x.toMul ∈ unitGroup w
    exact (Multiplicative.toAdd.injective.eq_iff).trans (unitsValuation_eq_one_iff w)
  rw [hker]
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact y.property

end Galois

end FinitePlace

end SIC
