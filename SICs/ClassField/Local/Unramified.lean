/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Local.UnitCohomology
import SICs.ClassField.Frobenius.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Group.Int.TypeTags
import SICs.GroupCohomology.Hilbert90

/-!
# Unramified local extensions

For a Galois extension of number fields `L/K` and a finite place `w` of `L` above `v` with
ramification index $e(w \mid v) = 1$, the extension $L_w/K_v$ is cyclic. Trivial Frobenius
gives local degree one; the integral units $U_w$ have trivial Tate groups in degrees $0$ and
$-1$, and the norm maps $U_w$ onto $U_v$.

This is Milne, *Class Field Theory*, version 4.03 (2020), Chapter III, Propositions 1.1 and 1.2,
in the degrees $0$ and $-1$ of the explicit Tate groups; Serre, *Local class field theory*, in
J. W. S. Cassels and A. Fröhlich (eds.), *Algebraic Number Theory* (1967), Chapter VI, §1.2,
Proposition 1(1). These are the unramified factors of the cohomology of the idèles in Milne,
Chapter VII, Propositions 2.5 and 2.7.

## The argument

*Cyclicity.* At $e(w \mid v)=1$, reduction identifies the decomposition group $D_w$ with the
Galois group of the residue extension $(\mathcal O_L / w) / (\mathcal O_K / v)$
(`SIC.decompositionResidueEquiv`). This finite-field Galois group is cyclic, and so is
$\operatorname{Gal}(L_w/K_v) \cong D_w$ (`decompositionEquiv`).
Frobenius generates $D_w$, so trivial Frobenius is equivalent to local degree one; the
forward implication is used in Milne, Chapter VII, Proposition 4.7.

*Degree $-1$.* A uniformizer $\pi$ of $K$ at `v` remains a uniformizer of $L_w$ when $e = 1$, and
it is fixed by $G = \operatorname{Gal}(L_w/K_v)$, so $L_w^\times = U_w \times \pi^{\mathbb Z}$ as
`G`-modules (Milne's (26)). If $u \in U_w$ has norm one, Hilbert's Theorem 90 for the cyclic
extension $L_w/K_v$ gives $u = \sigma y / y$ with $y \in L_w^\times$; writing $y = y_0 \pi^k$ with
$y_0 \in U_w$ gives $u = \sigma y_0 / y_0$. So $\widehat H^{-1}(G, U_w) = 0$.

*Degree $0$.* Since `G` is cyclic, $h(U_w) = 1$ (`SICs.ClassField.Local.UnitCohomology`), so
$|\widehat H^0(G, U_w)| = h(U_w) \cdot |\widehat H^{-1}(G, U_w)| = 1$. This replaces Milne's
filtration proof of Proposition 1.2 by his Lemma 2.5, which does not depend on it. A unit $u$ of
$K_v$ is a `G`-fixed unit of $L_w$, hence a norm $\prod_\sigma \sigma y = N_{L_w/K_v}(y)$ with
$y \in U_w$.
-/

noncomputable section

open NumberField IsDedekindDomain
open scoped NumberField SIC.FinitePlace Pointwise WithZero

namespace SIC

namespace FinitePlace

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [IsGalois K L]

/-- If $e(w \mid v) = 1$, then $\operatorname{Gal}(L_w/K_v) \cong D_w$ is isomorphic to the Galois
group of the residue extension, hence cyclic. Milne, *Class Field Theory*, Chapter III, §1. -/
theorem isCyclic_of_ramificationIdx_eq_one (h : w.asIdeal.ramificationIdx (𝓞 K) = 1) :
    IsCyclic (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) := by
  have : v.asIdeal.IsMaximal := Ideal.isMaximal_of_isPrime_of_ne_bot _ v.ne_bot
  have : w.asIdeal.IsMaximal := Ideal.isMaximal_of_isPrime_of_ne_bot _ w.ne_bot
  let _ := Ideal.Quotient.field v.asIdeal
  let _ := Ideal.Quotient.field w.asIdeal
  have : Finite ((𝓞 K) ⧸ v.asIdeal) := inferInstance
  have : Finite ((𝓞 L) ⧸ w.asIdeal) := inferInstance
  have hcyc : IsCyclic (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) := by
    let e := decompositionResidueEquiv v.asIdeal w.asIdeal v.ne_bot h
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  rw [← stabilizer_eq_stabilizer_asIdeal (K := K) w] at hcyc
  have := hcyc
  exact isCyclic_of_surjective (decompositionEquiv v w).toMonoidHom
    (decompositionEquiv v w).surjective

/-- Trivial Frobenius at an unramified place means local degree one, hence complete splitting.
Milne, *Class Field Theory*, Chapter V, remark after 1.12, used in Chapter VII,
Proposition 4.7. -/
theorem finrank_eq_one_of_isFrobeniusAt_one (hram : w.asIdeal.ramificationIdx (𝓞 K) = 1)
    (hFrob : IsFrobeniusAt K L 1 v.asIdeal w.asIdeal) :
    Module.finrank (v.adicCompletion K) (w.adicCompletion L) = 1 := by
  rw [finrank_eq_card_stabilizer, stabilizer_eq_stabilizer_asIdeal,
    ← hFrob.zpowers_eq_decomposition hram,
    Subgroup.zpowers_one_eq_bot, Subgroup.card_bot]

omit [IsGalois K L] in
/-- At ramification index one, a unit of $K_v$ maps to a uniformizer of $L_w$.
This is the valuation step used in `subsingleton_tateNegOne_unitGroupSubrep`. -/
private theorem base_uniformizer (h : w.asIdeal.ramificationIdx (𝓞 K) = 1) :
    ∃ π : (v.adicCompletion K)ˣ,
      unitsValuation w (Units.map (completionMap v w) π) =
        Multiplicative.ofAdd (-1 : ℤ) := by
  refine ⟨uniformizer v, ?_⟩
  apply WithZero.coe_injective
  rw [coe_unitsValuation]
  change Valued.v ((completionMap v w)
    (algebraMap K (v.adicCompletion K) (integralUniformizer v : K))) =
      (WithZero.exp (-1 : ℤ) : ℤᵐ⁰)
  rw [completionMap_algebraMap]
  change Valued.v (((algebraMap K L) (integralUniformizer v : K) : L) :
    w.adicCompletion L) = _
  rw [w.valuedAdicCompletion_eq_valuation',
    ← v.valuation_liesOver L w (integralUniformizer v : K),
    Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot,
    h, pow_one, v.valuation_of_algebraMap]
  exact valued_integralUniformizer v

omit [IsGalois K L] in
/-- A coboundary over $L_w$ has an integral-unit representative when $e(w \mid v)=1$.
This is the normalization used in `subsingleton_tateNegOne_unitGroupSubrep`. -/
private theorem integral_coboundary (h : w.asIdeal.ramificationIdx (𝓞 K) = 1)
    (g : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
    (y : (w.adicCompletion L)ˣ) :
    ∃ z ∈ unitGroup w, g • z / z = g • y / y := by
  obtain ⟨π, hπ⟩ := base_uniformizer v w h
  let t : (w.adicCompletion L)ˣ := Units.map (completionMap v w) π
  have ht : g • t = t := by
    apply Units.ext
    change g (completionMap v w (π : v.adicCompletion K)) =
      completionMap v w (π : v.adicCompletion K)
    exact g.commutes (π : v.adicCompletion K)
  let n : ℤ := (unitsValuation w y).toAdd
  let z := y * t ^ n
  have htval : Valued.v (t : w.adicCompletion L) = WithZero.exp (-1 : ℤ) := by
    rw [← coe_unitsValuation, hπ]
    rfl
  have hn : WithZero.log (Valued.v (y : w.adicCompletion L)) = n := by
    rw [← coe_unitsValuation]
    exact WithZero.log_exp _
  have hz : z ∈ unitGroup w := by
    dsimp [z]
    rw [← hn]
    exact mul_zpow_uniformizer_mem_unitGroup w y t htval
  refine ⟨z, hz, ?_⟩
  dsimp [z]
  change g • (y * t ^ n) / (y * t ^ n) = g • y / y
  rw [smul_mul', smul_zpow', ht]
  simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

omit [IsGalois K L] in
/-- Every element of the augmentation subgroup of $L_w^\times$ can be written using integral
units when $e(w \mid v)=1$. This is used in `subsingleton_tateNegOne_unitGroupSubrep`. -/
private theorem integral_augmentation_expression
    (h : w.asIdeal.ramificationIdx (𝓞 K) = 1)
    {x : (w.adicCompletion L)ˣ}
    (hx : x ∈ Representation.augmentationSubgroup
      (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
      (w.adicCompletion L)ˣ) :
    ∃ f : (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) →
        (w.adicCompletion L)ˣ,
      (∀ g, f g ∈ unitGroup w) ∧ x = ∏ g, g • f g / f g := by
  classical
  obtain ⟨y, hy⟩ := (Representation.mem_augmentationSubgroup_iff x).mp hx
  choose f hf hfy using fun g => integral_coboundary v w h g (y g)
  refine ⟨f, hf, hy.trans ?_⟩
  exact Finset.prod_congr rfl fun g _ => (hfy g).symm

/-- If $e(w \mid v) = 1$, then $\widehat H^{-1}(\operatorname{Gal}(L_w/K_v), U_w) = 0$. Milne,
*Class Field Theory*, Chapter III, Proposition 1.1. -/
theorem subsingleton_tateNegOne_unitGroupSubrep (h : w.asIdeal.ramificationIdx (𝓞 K) = 1) :
    Subsingleton (Representation.TateNegOne (unitGroupSubrep v w).toRepresentation) := by
  let G := w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L
  let M := (w.adicCompletion L)ˣ
  have : IsCyclic G := isCyclic_of_ramificationIdx_eq_one v w h
  apply (Representation.subsingleton_tateNegOne_subgroupSubrep_iff
    (unitGroup w) (smul_mem_unitGroup v w)).2
  intro x hx hnx
  have hxker : Additive.ofMul x ∈
      LinearMap.ker (Representation.ofMulDistribMulAction G M).norm := by
    rw [LinearMap.mem_ker, Representation.norm_ofMulDistribMulAction]
    exact congrArg Additive.ofMul hnx
  let xker : LinearMap.ker (Representation.ofMulDistribMulAction G M).norm :=
    ⟨Additive.ofMul x, hxker⟩
  have hsub : Subsingleton
      (Representation.TateNegOne (Representation.ofMulDistribMulAction G M)) :=
    Representation.subsingleton_tateNegOne_units
  have hzero : (Submodule.Quotient.mk xker :
      Representation.TateNegOne (Representation.ofMulDistribMulAction G M)) = 0 :=
    @Subsingleton.elim _ hsub _ _
  have haug : x ∈ Representation.augmentationSubgroup G M :=
    (Representation.mem_coinvariantsKer_ofMulDistribMulAction
      (Additive.ofMul x)).mp
      ((Representation.TateNegOne.mk_eq_zero_iff _ xker).mp hzero)
  exact integral_augmentation_expression v w h haug

/-- If $e(w \mid v) = 1$, then $\widehat H^0(\operatorname{Gal}(L_w/K_v), U_w) = 0$. Milne,
*Class Field Theory*, Chapter III, Proposition 1.1. -/
theorem subsingleton_tateZero_unitGroupSubrep (h : w.asIdeal.ramificationIdx (𝓞 K) = 1) :
    Subsingleton (Representation.TateZero (unitGroupSubrep v w).toRepresentation) := by
  have : IsCyclic (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) :=
    isCyclic_of_ramificationIdx_eq_one v w h
  exact Representation.subsingleton_tateZero_of_herbrandQuotient_eq_one
    (unitGroupSubrep v w).toRepresentation
    (hasHerbrandQuotient_unitGroupSubrep v w)
    (subsingleton_tateNegOne_unitGroupSubrep v w h)
    (herbrandQuotient_unitGroupSubrep v w)

/-- If $e(w \mid v) = 1$, the norm maps the integral units of $L_w$ onto those of $K_v$:
$N_{L_w/K_v}(U_w) = U_v$. Milne, *Class Field Theory*, Chapter III, Proposition 1.2. -/
theorem map_localNorm_unitGroup (h : w.asIdeal.ramificationIdx (𝓞 K) = 1) :
    (unitGroup w).map (localNorm v w) = unitGroup v := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact localNorm_mem_integral_units v w hy
  · intro x hx
    let G := w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L
    let x' : (w.adicCompletion L)ˣ := Units.map (completionMap v w) x
    have hx' : x' ∈ unitGroup w := by
      apply (units_map_completionMap_mem_iff v w).2
      exact hx
    have hfix (σ : G) : σ • x' = x' := by
      apply Units.ext
      change σ (completionMap v w (x : v.adicCompletion K)) =
        completionMap v w (x : v.adicCompletion K)
      exact σ.commutes (x : v.adicCompletion K)
    have hzero := subsingleton_tateZero_unitGroupSubrep v w h
    obtain ⟨y, hy, hnorm⟩ :=
      (Representation.subsingleton_tateZero_subgroupSubrep_iff
        (unitGroup w) (smul_mem_unitGroup v w)).mp hzero x' hx' hfix
    refine ⟨y, hy, ?_⟩
    apply (Units.map_injective (completionMap v w).injective)
    change Units.map (algebraMap (v.adicCompletion K) (w.adicCompletion L))
      ((Units.map (Algebra.norm (v.adicCompletion K))) y) = x'
    exact (Representation.unitsMap_algebraMap_norm y).trans hnorm

/-- In an unramified local extension every integral base unit is a local norm. This supplies
the range inclusion used by `SICs.ClassField.Ideles.NormTopology`,
`SICs.ClassField.Ideles.PowerSubgroup`, and `SICs.ClassField.Ideles.LocalGlobalPower`. -/
theorem unitGroup_le_range_localNorm (h : w.asIdeal.ramificationIdx (𝓞 K) = 1) :
    unitGroup v ≤ (localNorm v w).range := by
  rw [← map_localNorm_unitGroup v w h]
  exact Subgroup.map_le_range _ _

end FinitePlace

end SIC
