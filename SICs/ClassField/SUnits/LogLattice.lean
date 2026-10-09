/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.SUnits.Basic
import SICs.GroupCohomology.Permutation
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# The logarithmic lattice of ordinary units

The weighted logarithms of ordinary units, together with the diagonal vector, form a full
integer lattice in the real functions on the infinite places.

This module follows Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII, proof of
Proposition 3.1, logarithmic lattice at $S=S_\infty$, and *Algebraic Number Theory*,
version 3.08 (2020), §5, Theorem 5.11. The empty-exceptional-set S-unit representation is
identified with the units of the ring of integers by `sUnitsEmptyEquiv`.

## The argument

The $w$-coordinate of the logarithmic map is
$[L_w:\mathbb R]\log |x|_w$, where the multiplicity is one at a real place and two at a complex
place. Mathlib's infinite places store the usual absolute value; Milne's normalized value at a
complex place is its square, and the multiplicity supplies this normalization. The product
formula makes the coordinate sum zero. Mathlib's Dirichlet theorem gives a full lattice after
omitting one infinite coordinate; the missing coordinate is minus the sum of
the others. Adding the invariant all-ones vector supplies the complementary real direction.
An explicit real linear equivalence from the omitted coordinates and this diagonal direction
transports Mathlib's lattice to the range of the augmented logarithmic map. Its kernel is the
ordinary roots of unity in the first factor and zero in the diagonal factor.
-/

noncomputable section
open IsDedekindDomain NumberField NumberField.Units
open scoped NumberField

namespace SIC.IdeleGroup

section

variable {K : Type*} {L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

/-! ### The equivariant logarithm

At the empty exceptional set the actual S-unit action is the action on ordinary units. The
weighted logarithm is equivariant for the coordinate permutation action. -/

/-- The empty-set S-unit module used for the ordinary-unit representation. -/
private abbrev OrdinaryUnits :=
  (sUnitsSubrep (L := L) (∅ : Finset (HeightOneSpectrum (𝓞 K)))).toSubmodule

/-- The Galois action on ordinary units through the empty-set S-unit subrepresentation. -/
abbrev ordinaryUnitsRep : Representation ℤ (L ≃ₐ[K] L)
    (sUnitsSubrep (L := L) (∅ : Finset (HeightOneSpectrum (𝓞 K)))).toSubmodule :=
  (sUnitsSubrep (L := L) (∅ : Finset (HeightOneSpectrum (𝓞 K)))).toRepresentation

/-- The integer-linear identification of the ordinary-unit representation with
`Additive (𝓞 L)ˣ`, induced by `sUnitsEmptyEquiv`. -/
def ordinaryUnitsEquiv :
    (sUnitsSubrep (L := L) (∅ : Finset (HeightOneSpectrum (𝓞 K)))).toSubmodule ≃ₗ[ℤ]
    Additive ((𝓞 L)ˣ) := by
  change Additive (sUnits (L := L) (∅ : Finset (HeightOneSpectrum (𝓞 K)))) ≃ₗ[ℤ]
    Additive ((𝓞 L)ˣ)
  exact (sUnitsEmptyEquiv (K := K) (L := L)).toAdditive.toIntLinearEquiv

/-- The full weighted logarithm on ring-of-integers units; used by `logUnits`. -/
private def fullLog : Additive ((𝓞 L)ˣ) →+ (InfinitePlace L → ℝ) where
  toFun x w := (w.mult : ℝ) * Real.log (w (x.toMul : L))
  map_zero' := by ext w; simp
  map_add' x y := by ext w; simp [Real.log_mul, mul_add]

/-- The underlying integer-linear map of `logUnits`. -/
private def logUnitsLinear : OrdinaryUnits (K := K) (L := L) →ₗ[ℤ]
    (InfinitePlace L → ℝ) :=
  (fullLog (L := L)).toIntLinearMap.comp
    (ordinaryUnitsEquiv (K := K) (L := L)).toLinearMap

omit [NumberField K] in
/-- The $w$-coordinate of `logUnitsLinear`; used by `logUnits_apply`. -/
private theorem logUnitsLinear_apply (x : OrdinaryUnits (K := K) (L := L))
    (w : InfinitePlace L) :
    logUnitsLinear (K := K) (L := L) x w =
      (w.mult : ℝ) * Real.log (w (x.1.toMul : L)) := by
  change (w.mult : ℝ) * Real.log (w
    ((sUnitsEmptyEquiv (K := K) (L := L) ⟨x.1.toMul, x.2⟩ : (𝓞 L)ˣ) : L)) = _
  rw [sUnitsEmptyEquiv_coe]

/-- The equivariant integer-linear map $x\mapsto ([L_w:\mathbb R]\log|x|_w)_w$.
Milne, *Class Field Theory*, Chapter VII, proof of Proposition 3.1, logarithmic lattice at
$S=S_\infty$. -/
def logUnits : (ordinaryUnitsRep (K := K) (L := L)).IntertwiningMap
    (SIC.Representation.integral
      (SIC.Representation.permutation (k := ℝ) (G := L ≃ₐ[K] L) (X := InfinitePlace L))) where
  toLinearMap := logUnitsLinear (K := K) (L := L)
  isIntertwining' := by
    intro σ
    ext x w
    simp only [LinearMap.comp_apply, SIC.Representation.integral_apply,
      SIC.Representation.permutation_apply, logUnitsLinear_apply]
    have hsmul : ((ordinaryUnitsRep (K := K) (L := L) σ x).1.toMul : Lˣ) =
        σ • x.1.toMul := by
      exact sUnitsSubrep_smul (∅ : Finset (HeightOneSpectrum (𝓞 K))) σ x
    rw [hsmul, InfinitePlace.mult_smul, InfinitePlace.smul_apply]
    change (w.mult : ℝ) * Real.log (w (σ (x.1.toMul : L))) =
      (w.mult : ℝ) * Real.log (w (σ⁻¹.symm (x.1.toMul : L)))
    rfl

omit [NumberField K] in
/-- The logarithm of a unit $x$ at $w$ is
$[L_w:\mathbb R]\log|x|_w$. See `logUnits`. -/
theorem logUnits_apply
    (x : (sUnitsSubrep (L := L) (∅ : Finset (HeightOneSpectrum (𝓞 K)))).toSubmodule)
    (w : InfinitePlace L) :
    logUnits (K := K) (L := L) x w =
      (w.mult : ℝ) * Real.log (w (x.1.toMul : L)) := by
  exact logUnitsLinear_apply x w

/-! ### Completing the omitted coordinate

Mathlib's `logEmbedding` omits a distinguished infinite place. The completion sends omitted
coordinates `g` and diagonal coordinate `t` to `g(w)+t` away from that place and to
`t-∑ g(w)` at that place. Its inverse subtracts the mean coordinate. -/

open NumberField.Units.dirichletUnitTheorem in
/-- The linear completion of the omitted-coordinate log space; used by `logCompletion`. -/
private def logCompletionLinear : (logSpace L × ℝ) →ₗ[ℝ] (InfinitePlace L → ℝ) := by
  classical
  exact {
    toFun := fun p w => if h : w = w₀ then p.2 - ∑ v, p.1 v else p.1 ⟨w, h⟩ + p.2
    map_add' := by
      intro p q
      ext w
      by_cases h : w = w₀ <;> simp [h, Finset.sum_add_distrib] <;> ring
    map_smul' := by
      intro c p
      ext w
      by_cases h : w = w₀
      · simp [h, mul_sub, Finset.mul_sum]
      · simp [h, mul_add] }

open NumberField.Units.dirichletUnitTheorem in
/-- The sum of the completed coordinates is the number of infinite places times the diagonal
coordinate; used by `logCompletion`. -/
private theorem sum_logCompletionLinear (p : logSpace L × ℝ) :
    ∑ w, logCompletionLinear (L := L) p w =
      (Fintype.card (InfinitePlace L) : ℝ) * p.2 := by
  classical
  rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀]
  simp only [logCompletionLinear, LinearMap.coe_mk, AddHom.coe_mk]
  have hsum : (∑ i : {w : InfinitePlace L // w ≠ w₀},
      if h : (i : InfinitePlace L) = w₀ then p.2 - ∑ v, p.1 v
      else p.1 ⟨i, h⟩ + p.2) = ∑ i, (p.1 i + p.2) := by
    apply Finset.sum_congr rfl
    intro i _
    simp [i.property]
  rw [hsum]
  simp only [dite_eq_left, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have hc : Fintype.card (InfinitePlace L) =
      1 + Fintype.card {w : InfinitePlace L // w ≠ w₀} := by
    have h := Fintype.sum_eq_add_sum_subtype_ne
      (fun _ : InfinitePlace L => (1 : ℕ)) w₀
    simpa using h
  rw [hc]
  push_cast
  simp only [Finset.card_univ]
  ring

open NumberField.Units.dirichletUnitTheorem in
/-- Completion is a real linear equivalence between the omitted-coordinate log space plus the
diagonal direction and all infinite-place coordinates; used by `augmentedLog_range_eq`. -/
private def logCompletion : (logSpace L × ℝ) ≃ₗ[ℝ] (InfinitePlace L → ℝ) := by
  classical
  let F := logCompletionLinear (L := L)
  have hc : (Fintype.card (InfinitePlace L) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  apply LinearEquiv.ofBijective F
  constructor
  · intro p q hp
    have hs := congrArg (fun f : InfinitePlace L → ℝ => ∑ w, f w) hp
    change (∑ w, F p w) = ∑ w, F q w at hs
    rw [sum_logCompletionLinear, sum_logCompletionLinear] at hs
    have h2 : p.2 = q.2 := (mul_left_cancel₀ hc) hs
    apply Prod.ext
    · funext w
      have hw := congrFun hp w.1
      change F p w.1 = F q w.1 at hw
      simp only [F, logCompletionLinear, LinearMap.coe_mk, AddHom.coe_mk,
        dite_eq_right w.2] at hw
      simpa [h2] using hw
    · exact h2
  · intro f
    let t : ℝ := (∑ w, f w) / (Fintype.card (InfinitePlace L) : ℝ)
    let p : logSpace L × ℝ := (fun w => f w.1 - t, t)
    have hp : ∀ w : InfinitePlace L, w ≠ w₀ → F p w = f w := by
      intro w hw
      simp [F, logCompletionLinear, p, hw]
    have hs : (∑ w, F p w) = ∑ w, f w := by
      rw [sum_logCompletionLinear]
      exact mul_div_cancel₀ _ hc
    refine ⟨p, funext fun w => ?_⟩
    by_cases hw : w = w₀
    · subst w
      rw [Fintype.sum_eq_add_sum_subtype_ne (fun w => F p w) w₀,
        Fintype.sum_eq_add_sum_subtype_ne f w₀] at hs
      have hsub : (∑ v : {w : InfinitePlace L // w ≠ w₀}, F p v.1) =
          ∑ v : {w : InfinitePlace L // w ≠ w₀}, f v.1 := by
        apply Finset.sum_congr rfl
        intro v _
        exact hp v.1 v.2
      rw [hsub] at hs
      exact add_right_cancel hs
    · exact hp w hw

open NumberField.Units.dirichletUnitTheorem in
/-- Completing Mathlib's omitted-coordinate log embedding gives the full weighted logarithm;
used by `logCompletion_augmented`. -/
private theorem logCompletion_unit (u : (𝓞 L)ˣ) :
    logCompletion (L := L) ((logEmbedding L) (Additive.ofMul u), (0 : ℝ)) =
      fullLog (L := L) (Additive.ofMul u) := by
  classical
  funext w
  change logCompletion (L := L) ((logEmbedding L) (Additive.ofMul u), (0 : ℝ)) w =
    (w.mult : ℝ) * Real.log (w (u : L))
  by_cases hw : w = w₀
  · subst w
    have hs := sum_logEmbedding_component u
    simp only [logCompletion, LinearEquiv.ofBijective_apply, logCompletionLinear,
      LinearMap.coe_mk, AddHom.coe_mk, dite_eq_left]
    rw [hs]
    ring
  · simp [logCompletion, logCompletionLinear, hw, logEmbedding_component]

open NumberField.Units.dirichletUnitTheorem in
/-- The second completion coordinate adds a constant function; used by
`logCompletion_augmented`. -/
private theorem logCompletion_add_const (g : logSpace L) (t : ℝ) (w : InfinitePlace L) :
    logCompletion (L := L) (g, t) w = logCompletion (L := L) (g, 0) w + t := by
  by_cases hw : w = w₀
  · simp [logCompletion, logCompletionLinear, hw]
    ring
  · simp [logCompletion, logCompletionLinear, hw]

/-! ### The diagonal augmentation

The vector $(1,\ldots,1)$ is invariant. Adding its integer multiples to the zero-sum
logarithms gives the infinite-place part of Milne's logarithmic lattice. -/

/-- Integer constants as real-valued coordinate functions; used by `augmentedLog`. -/
private def constIntHom : ℤ →+ (InfinitePlace L → ℝ) where
  toFun n _ := n
  map_zero' := by ext; simp
  map_add' n m := by ext; simp

/-- The equivariant map $(x,n)\mapsto\log(x)+n(1,\ldots,1)$.
Milne, *Class Field Theory*, Chapter VII, proof of Proposition 3.1, logarithmic lattice at
$S=S_\infty$. -/
def augmentedLog : ((ordinaryUnitsRep (K := K) (L := L)).prod
    (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ)).IntertwiningMap
      (SIC.Representation.integral
        (SIC.Representation.permutation (k := ℝ) (G := L ≃ₐ[K] L)
          (X := InfinitePlace L))) where
  toLinearMap := LinearMap.coprod (logUnits (K := K) (L := L)).toLinearMap
    (constIntHom (L := L)).toIntLinearMap
  isIntertwining' := by
    intro σ
    apply LinearMap.ext
    intro p
    funext w
    simp only [LinearMap.comp_apply, LinearMap.coprod_apply, SIC.Representation.integral_apply,
      SIC.Representation.permutation_apply, Pi.add_apply]
    change logUnits (K := K) (L := L) (ordinaryUnitsRep σ p.1) w + (p.2 : ℝ) =
      logUnits (K := K) (L := L) p.1 (σ⁻¹ • w) + (p.2 : ℝ)
    congr 1
    have h := Representation.IntertwiningMap.isIntertwining
      (ordinaryUnitsRep (K := K) (L := L))
      (SIC.Representation.integral
        (SIC.Representation.permutation (k := ℝ) (G := L ≃ₐ[K] L)
          (X := InfinitePlace L)))
      (logUnits (K := K) (L := L)) σ p.1
    exact congrFun h w

omit [NumberField K] in
/-- Each coordinate of `augmentedLog (x,n)` is the weighted logarithm plus $n$. -/
theorem augmentedLog_apply
    (p : (sUnitsSubrep (L := L) (∅ : Finset (HeightOneSpectrum (𝓞 K)))).toSubmodule × ℤ)
    (w : InfinitePlace L) :
    augmentedLog (K := K) (L := L) p w =
      logUnits (K := K) (L := L) p.1 w + (p.2 : ℝ) := rfl

omit [NumberField K] in
/-- The log on the S-unit module equals the full log on ordinary units; used by
`logCompletion_augmented`. -/
private theorem logUnits_eq_fullLog (x : OrdinaryUnits (K := K) (L := L)) :
    logUnits (K := K) (L := L) x =
      fullLog (L := L) (ordinaryUnitsEquiv (K := K) (L := L) x) := by
  funext w
  rw [logUnits_apply]
  change (w.mult : ℝ) * Real.log (w (x.1.toMul : L)) =
    (w.mult : ℝ) * Real.log (w
      ((sUnitsEmptyEquiv (K := K) (L := L) ⟨x.1.toMul, x.2⟩ : (𝓞 L)ˣ) : L))
  rw [sUnitsEmptyEquiv_coe]

omit [NumberField K] in
/-- The augmented logarithm is the completion of Mathlib's omitted-coordinate log embedding
and the integer diagonal coordinate; used by `augmentedLog_range_eq`. -/
private theorem logCompletion_augmented
    (p : OrdinaryUnits (K := K) (L := L) × ℤ) :
    logCompletion (L := L)
      ((logEmbedding L) (ordinaryUnitsEquiv (K := K) (L := L) p.1), (p.2 : ℝ)) =
      augmentedLog (K := K) (L := L) p := by
  funext w
  rw [logCompletion_add_const]
  have h := logCompletion_unit
    (L := L) (ordinaryUnitsEquiv (K := K) (L := L) p.1).toMul
  change logCompletion (L := L)
    ((logEmbedding L) (ordinaryUnitsEquiv (K := K) (L := L) p.1), (0 : ℝ)) =
      fullLog (L := L) (ordinaryUnitsEquiv (K := K) (L := L) p.1) at h
  rw [congrFun h w, ← logUnits_eq_fullLog, augmentedLog_apply]

/-! ### The product lattice and its transport

Dirichlet's unit lattice occupies the omitted coordinates; integer multiples of $1$ occupy the
diagonal coordinate. The completion equivalence carries their product onto the actual range of
`augmentedLog`. -/

/-- Integer multiples of $1$ in the real diagonal line; used by `productUnitLattice`. -/
private def integerLattice : Submodule ℤ ℝ := ℤ ∙ (1 : ℝ)

/-- The diagonal integer lattice is the integer span of the singleton real basis; used by its
discrete and full-lattice instances. -/
private theorem integerLattice_eq_basisSpan : integerLattice =
    Submodule.span ℤ (Set.range (Module.Basis.singleton Unit ℝ)) := by
  simp [integerLattice, Set.range_unique]

/-- Membership in the integer diagonal lattice is equivalent to being the real image of an
integer; used by `augmentedLog_range_eq`. -/
private theorem mem_integerLattice (t : ℝ) :
    t ∈ integerLattice ↔ ∃ n : ℤ, (n : ℝ) = t := by
  simp only [integerLattice, Submodule.mem_span_singleton]
  simp

/-- The integer diagonal lattice is discrete; used by `productUnitLattice`. -/
private theorem integerLattice_discrete : DiscreteTopology integerLattice := by
  rw [integerLattice_eq_basisSpan]
  infer_instance

attribute [local instance] integerLattice_discrete

/-- The integer diagonal lattice spans the real line; used by `productUnitLattice`. -/
private theorem integerLattice_isZLattice : IsZLattice ℝ integerLattice := by
  constructor
  change Submodule.span ℝ (integerLattice : Set ℝ) = ⊤
  rw [integerLattice_eq_basisSpan]
  exact ZSpan.span_top (Module.Basis.singleton Unit ℝ)

attribute [local instance] integerLattice_isZLattice

open NumberField.Units.dirichletUnitTheorem in
/-- The product of Mathlib's Dirichlet unit lattice and the integer diagonal lattice; used by
`augmentedLog_range_eq`. -/
private def productUnitLattice : Submodule ℤ (logSpace L × ℝ) :=
  (unitLattice L).prod integerLattice

/-- The product of the omitted-coordinate unit lattice and integer diagonal is discrete; used
by `instDiscrete_augmentedLog_range`. -/
private theorem productUnitLattice_discrete : DiscreteTopology (productUnitLattice (L := L)) := by
  classical
  have : DiscreteTopology (unitLattice L) := inferInstance
  have : DiscreteTopology integerLattice := inferInstance
  change DiscreteTopology
    ↥((unitLattice L : Set (NumberField.Units.dirichletUnitTheorem.logSpace L)) ×ˢ
      (integerLattice : Set ℝ))
  exact (Homeomorph.Set.prod
    (unitLattice L : Set (NumberField.Units.dirichletUnitTheorem.logSpace L))
    (integerLattice : Set ℝ)).symm.discreteTopology

attribute [local instance] productUnitLattice_discrete

open scoped Classical in
/-- The product unit lattice spans the omitted log coordinates and the diagonal line; used by
`instZLattice_augmentedLog_range`. -/
private theorem productUnitLattice_isZLattice : IsZLattice ℝ (productUnitLattice (L := L)) := by
  constructor
  change Submodule.span ℝ
    ((unitLattice L : Set (NumberField.Units.dirichletUnitTheorem.logSpace L)) ×ˢ
      (integerLattice : Set ℝ)) = ⊤
  rw [Submodule.span_prod_eq ℝ (unitLattice L).zero_mem integerLattice.zero_mem]
  rw [IsZLattice.span_top, IsZLattice.span_top, Submodule.prod_top]

attribute [local instance] productUnitLattice_isZLattice

open scoped Classical in
omit [NumberField K] in
/-- The actual range of `augmentedLog` is the completion transport of the Dirichlet unit
lattice times the integer diagonal; used by its discrete and full-lattice instances. -/
private theorem augmentedLog_range_eq :
    LinearMap.range (augmentedLog (K := K) (L := L)).toLinearMap =
      ZLattice.comap ℝ (productUnitLattice (L := L))
        (logCompletion (L := L)).symm.toLinearMap := by
  ext f
  change (∃ p, augmentedLog (K := K) (L := L) p = f) ↔
    (logCompletion (L := L)).symm f ∈ productUnitLattice (L := L)
  constructor
  · rintro ⟨p, rfl⟩
    rw [← logCompletion_augmented, LinearEquiv.symm_apply_apply]
    change (logEmbedding L (ordinaryUnitsEquiv (K := K) (L := L) p.1)) ∈
      unitLattice L ∧ (p.2 : ℝ) ∈ integerLattice
    constructor
    · change _ ∈ Submodule.map (logEmbedding L).toIntLinearMap ⊤
      exact Submodule.mem_map.mpr ⟨_, Submodule.mem_top, rfl⟩
    · exact (mem_integerLattice _).mpr ⟨p.2, rfl⟩
  · intro hf
    change ((logCompletion (L := L)).symm f).1 ∈ unitLattice L ∧
      ((logCompletion (L := L)).symm f).2 ∈ integerLattice at hf
    obtain ⟨hg, ht⟩ := hf
    change ((logCompletion (L := L)).symm f).1 ∈
      Submodule.map (logEmbedding L).toIntLinearMap ⊤ at hg
    obtain ⟨a, _, ha⟩ := Submodule.mem_map.mp hg
    obtain ⟨n, hn⟩ := (mem_integerLattice _).mp ht
    let x : OrdinaryUnits (K := K) (L := L) :=
      (ordinaryUnitsEquiv (K := K) (L := L)).symm a
    refine ⟨(x, n), ?_⟩
    have hp : (logCompletion (L := L)).symm f =
        ((logEmbedding L) (ordinaryUnitsEquiv (K := K) (L := L) x), (n : ℝ)) := by
      apply Prod.ext
      · simpa [x] using ha.symm
      · exact hn.symm
    calc
      augmentedLog (K := K) (L := L) (x, n) =
          logCompletion (L := L)
            ((logEmbedding L) (ordinaryUnitsEquiv (K := K) (L := L) x), (n : ℝ)) :=
        (logCompletion_augmented (x, n)).symm
      _ = logCompletion (L := L) ((logCompletion (L := L)).symm f) :=
        congrArg (logCompletion (L := L)) hp.symm
      _ = f := LinearEquiv.apply_symm_apply _ f

/-- The range of the augmented logarithm is discrete. This is the infinite-place part of
Milne's logarithmic lattice, using Dirichlet's unit theorem for the omitted-coordinate summand. -/
instance instDiscrete_augmentedLog_range :
    DiscreteTopology (LinearMap.range (augmentedLog (K := K) (L := L)).toLinearMap) := by
  classical
  rw [augmentedLog_range_eq]
  let e := (logCompletion (L := L)).symm.toContinuousLinearEquiv
  change DiscreteTopology
    (ZLattice.comap ℝ (productUnitLattice (L := L)) e.toLinearMap)
  infer_instance

/-- The range of the augmented logarithm is a full real integer lattice, as in Milne,
*Class Field Theory*, Chapter VII, proof of Proposition 3.1, logarithmic lattice at $S=S_\infty$. -/
instance instZLattice_augmentedLog_range :
    IsZLattice ℝ (LinearMap.range (augmentedLog (K := K) (L := L)).toLinearMap) := by
  classical
  constructor
  rw [augmentedLog_range_eq]
  let e := (logCompletion (L := L)).symm.toContinuousLinearEquiv
  change Submodule.span ℝ
    (ZLattice.comap ℝ (productUnitLattice (L := L)) e.toLinearMap :
      Set (InfinitePlace L → ℝ)) = ⊤
  exact IsZLattice.span_top

/-! ### The finite kernel

Vanishing augmented logarithm forces its diagonal coordinate to vanish. Dirichlet's log-kernel
theorem then identifies the remaining kernel with the ordinary roots of unity. -/

omit [NumberField K] in
/-- The augmented logarithm vanishes precisely on $(\zeta,0)$ with $\zeta$ a root of unity.
Milne, *Class Field Theory*, Chapter VII, proof of Proposition 3.1, logarithmic lattice at
$S=S_\infty$. -/
theorem augmentedLog_eq_zero_iff
    (p : (sUnitsSubrep (L := L) (∅ : Finset (HeightOneSpectrum (𝓞 K)))).toSubmodule × ℤ) :
    augmentedLog (K := K) (L := L) p = 0 ↔
      (ordinaryUnitsEquiv (K := K) (L := L) p.1).toMul ∈ torsion L ∧ p.2 = 0 := by
  constructor
  · intro h
    have hp : ((logEmbedding L) (ordinaryUnitsEquiv (K := K) (L := L) p.1),
        (p.2 : ℝ)) = 0 := by
      apply (logCompletion (L := L)).injective
      rw [map_zero, logCompletion_augmented]
      exact h
    have hlog : (logEmbedding L) (ordinaryUnitsEquiv (K := K) (L := L) p.1) = 0 :=
      congrArg Prod.fst hp
    have hn : (p.2 : ℝ) = 0 := congrArg Prod.snd hp
    exact ⟨dirichletUnitTheorem.logEmbedding_eq_zero_iff.mp hlog,
      Int.cast_eq_zero.mp hn⟩
  · rintro ⟨ht, hn⟩
    have hlog : (logEmbedding L) (ordinaryUnitsEquiv (K := K) (L := L) p.1) = 0 :=
      dirichletUnitTheorem.logEmbedding_eq_zero_iff.mpr ht
    rw [← logCompletion_augmented, hlog, hn]
    simp

/-- The kernel of `augmentedLog` is finite because the group of ordinary roots of unity is
finite. Milne, *Class Field Theory*, Chapter VII, proof of Proposition 3.1. -/
instance instFinite_augmentedLog_ker :
    Finite (LinearMap.ker (augmentedLog (K := K) (L := L)).toLinearMap) := by
  let f : LinearMap.ker (augmentedLog (K := K) (L := L)).toLinearMap →
      torsion L := fun x =>
    ⟨(ordinaryUnitsEquiv (K := K) (L := L) x.1.1).toMul,
      (augmentedLog_eq_zero_iff x.1).mp x.2 |>.1⟩
  apply Finite.of_injective f
  intro x y hxy
  apply Subtype.ext
  apply Prod.ext
  · apply (ordinaryUnitsEquiv (K := K) (L := L)).injective
    exact congrArg (fun z : torsion L => Additive.ofMul z.1) hxy
  · have hx := ((augmentedLog_eq_zero_iff x.1).mp x.2).2
    have hy := ((augmentedLog_eq_zero_iff y.1).mp y.2).2
    exact hx.trans hy.symm

end
end SIC.IdeleGroup
