/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Ideles.Topology
import SICs.ClassField.Completion.FiniteBaseChange
import SICs.ClassField.Completion.InfiniteBaseChange

/-!
# Idèle norms for finite extensions of number fields

The componentwise norm on the full idèle group and the induced norm on idèle classes, including
the image identity for their norm subgroups.

## The argument

For every finite place `v` of the base field, the component of the norm is the product of the
local field norms over the finitely many primes above `v`. A finite local norm preserves integral
units, so the exceptional target places lie below the finite set of exceptional source places;
this proves restrictedness. At an infinite place, the component is likewise the product of the
local norms over the finitely many places above it. The component decomposition assembles the
two parts into the full idèle norm; its component formulas are then immediate from the two local
constructions.

The norm is transitive in a tower `K ⊆ L ⊆ M`: the primes of `M` above `v` are the primes above the
primes of `L` above `v` (`FinitePlace.PrimeAbove.sigmaEquiv`), and local norms compose. On a
principal idèle, the component at `v` is $\prod_{w \mid v} N_{L_w/K_v}(x) = N_{L/K}(x)$ by the
decomposition $K_v \otimes_K L \cong \prod_{w \mid v} L_w$ of
`SICs.ClassField.Completion.FiniteBaseChange` and `SICs.ClassField.Completion.InfiniteBaseChange`,
so the norm maps principal idèles to principal idèles and descends to a norm on idèle classes.
The quotient map sends the idèle norm subgroup onto the idèle-class norm subgroup, so
inclusion of norm images passes from idèles to classes. Through the tower, the norms from a field
`M` into which `L` embeds over `K` are norms from `L`. The norm of an idèle supported at one place
`w` is supported at the place below, with the local norm as component; at a place of local degree
one every local element is therefore a norm.

The componentwise norm and the induced class norm follow Milne, *Class Field Theory*, version
4.03 (2020), Chapter V, §4, "Norms of idèles". Chapter VII, §2 gives the Galois-product form.
-/

noncomputable section

open Filter IsDedekindDomain NumberField
open scoped BigOperators NumberField NumberField.AdeleRing NumberField.LiesOver
  RestrictedProduct SIC.FinitePlace SIC.InfinitePlace

namespace SIC

/-! ### Restricted products of finite local unit groups -/

namespace FiniteIdeleNorm

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L]

/-- The local norm contribution from one prime above a base place. -/
private def atPrimeAbove (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : FinitePlace.PrimeAbove (L := L) v) :
    FiniteLocalIdele L →* (v.adicCompletion K)ˣ :=
  (FinitePlace.localNorm v (FinitePlace.PrimeAbove.place v w)).comp
    (RestrictedProduct.evalMonoidHom
      (fun u : HeightOneSpectrum (NumberField.RingOfIntegers L) ↦ (u.adicCompletion L)ˣ)
      (FinitePlace.PrimeAbove.place v w))

/-- The product of all local norm contributions above a base place. -/
private def component (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    FiniteLocalIdele L →* (v.adicCompletion K)ˣ :=
  ∏ w : FinitePlace.PrimeAbove (L := L) v, atPrimeAbove v w

/-- Evaluation of a finite idèle norm component as the product of local norms. -/
@[simp]
private theorem component_apply
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (x : FiniteLocalIdele L) :
    component (K := K) (L := L) v x =
      ∏ w : FinitePlace.PrimeAbove (L := L) v,
        FinitePlace.localNorm v (FinitePlace.PrimeAbove.place v w)
          (x (FinitePlace.PrimeAbove.place v w)) := by
  simp [component, atPrimeAbove]

/-- The finite restricted-product idèle norm. -/
def map : FiniteLocalIdele L →* FiniteLocalIdele K where
  toFun x := ⟨fun v ↦ component (K := K) (L := L) v x, by
    rw [Filter.eventually_cofinite]
    let bad : Set (HeightOneSpectrum (NumberField.RingOfIntegers L)) :=
      {w | x w ∉ (Submonoid.ofClass (w.adicCompletionIntegers L)).units}
    have hbad : bad.Finite := by
      rw [← Filter.eventually_cofinite]
      exact x.2
    refine (hbad.image (FinitePlace.below (K := K) (L := L))).subset ?_
    intro v hv
    change ¬component (K := K) (L := L) v x ∈
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units at hv
    by_contra hnotImage
    apply hv
    rw [component_apply]
    exact Submonoid.prod_mem _ fun w _ ↦
      FinitePlace.localNorm_mem_integral_units v (FinitePlace.PrimeAbove.place v w) (by
        by_contra hw
        apply hnotImage
        refine ⟨FinitePlace.PrimeAbove.place v w, hw, ?_⟩
        exact FinitePlace.PrimeAbove.below_place v w)⟩
  map_one' := by
    apply RestrictedProduct.ext
    intro v
    exact (component (K := K) (L := L) v).map_one
  map_mul' x y := by
    apply RestrictedProduct.ext
    intro v
    exact (component (K := K) (L := L) v).map_mul x y

/-- Evaluation of the finite restricted-product norm at a base place. -/
@[simp]
theorem map_apply (x : FiniteLocalIdele L)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    map (K := K) (L := L) x v =
      ∏ w : FinitePlace.PrimeAbove (L := L) v,
        FinitePlace.localNorm v (FinitePlace.PrimeAbove.place v w)
          (x (FinitePlace.PrimeAbove.place v w)) := by
  exact component_apply v x

/-! ### Transitivity of the finite norm in towers -/

section Tower

variable {M : Type*} [Field M] [NumberField M] [Algebra L M] [Algebra K M]
  [IsScalarTower K L M]

/-- The finite idèle norm is transitive in towers: $N_{L/K} \circ N_{M/L} = N_{M/K}$. -/
theorem map_map (x : FiniteLocalIdele M) :
    map (K := K) (L := L) (map (K := L) (L := M) x) = map (K := K) (L := M) x := by
  apply RestrictedProduct.ext
  intro v
  let e := FinitePlace.PrimeAbove.sigmaEquiv (K := K) (L := L) (M := M) v
  simp only [map_apply]
  simp_rw [map_prod]
  calc
    _ = ∏ p : (Σ w : FinitePlace.PrimeAbove (L := L) v,
          FinitePlace.PrimeAbove (K := L) (L := M)
            (FinitePlace.PrimeAbove.place v w)),
          FinitePlace.localNorm v (FinitePlace.PrimeAbove.place v (e p))
            (x (FinitePlace.PrimeAbove.place v (e p))) := by
      rw [Fintype.prod_sigma]
      apply Finset.prod_congr rfl
      intro w _
      apply Finset.prod_congr rfl
      intro u _
      let w' := FinitePlace.PrimeAbove.place v w
      let u' := FinitePlace.PrimeAbove.place w' u
      let _ : u'.asIdeal.LiesOver v.asIdeal :=
        Ideal.LiesOver.trans u'.asIdeal w'.asIdeal v.asIdeal
      change FinitePlace.localNorm v w' (FinitePlace.localNorm w' u' (x u')) =
        FinitePlace.localNorm v u' (x u')
      exact FinitePlace.localNorm_trans v w' u' (x u')
    _ = _ := Equiv.prod_comp e (fun w : FinitePlace.PrimeAbove (L := M) v ↦
      FinitePlace.localNorm v (FinitePlace.PrimeAbove.place v w)
        (x (FinitePlace.PrimeAbove.place v w)))

end Tower

end FiniteIdeleNorm

/-! ### Product of the norms at infinite places -/

namespace InfiniteIdeleNorm

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L]

/-- The local norm contribution from one infinite place above a base place. -/
private def atPlaceAbove (v : NumberField.InfinitePlace K)
    (w : InfinitePlace.PlaceAbove (L := L) v) :
    InfiniteLocalIdele L →* v.Completionˣ := by
  exact
    (SIC.InfinitePlace.localNorm v w.1).comp
      (Pi.evalMonoidHom (fun u : NumberField.InfinitePlace L ↦ u.Completionˣ) w.1)

/-- The product of all local norm contributions above one infinite place. -/
private def component (v : NumberField.InfinitePlace K) :
    InfiniteLocalIdele L →* v.Completionˣ := by
  exact ∏ w : InfinitePlace.PlaceAbove (L := L) v, atPlaceAbove v w

omit [NumberField K] in
/-- Evaluation of an infinite idèle norm component as the product of local norms. -/
@[simp]
private theorem component_apply (v : NumberField.InfinitePlace K)
    (x : InfiniteLocalIdele L) :
    component (K := K) (L := L) v x =
      ∏ w : InfinitePlace.PlaceAbove (L := L) v,
        SIC.InfinitePlace.localNorm v w.1 (x w.1) := by
  simp [component, atPlaceAbove]

/-- The product norm on all infinite components of an idèle. -/
def map : InfiniteLocalIdele L →* InfiniteLocalIdele K := by
  exact
    { toFun := fun x v ↦ component (K := K) (L := L) v x
      map_one' := by
        funext v
        exact (component (K := K) (L := L) v).map_one
      map_mul' := by
        intro x y
        funext v
        exact (component (K := K) (L := L) v).map_mul x y }

omit [NumberField K] in
/-- Evaluation of the infinite idèle norm at a base place. -/
@[simp]
theorem map_apply (x : InfiniteLocalIdele L)
    (v : NumberField.InfinitePlace K) :
    map (K := K) (L := L) x v =
      ∏ w : InfinitePlace.PlaceAbove (L := L) v,
        SIC.InfinitePlace.localNorm v w.1 (x w.1) := by
  exact component_apply v x

/-! ### Transitivity of the infinite norm in towers -/

section Tower

variable {M : Type*} [Field M] [NumberField M] [Algebra L M] [Algebra K M]
  [IsScalarTower K L M]

omit [NumberField K] in
/-- The infinite idèle norm is transitive in towers: $N_{L/K} \circ N_{M/L} = N_{M/K}$. -/
theorem map_map (x : InfiniteLocalIdele M) :
    map (K := K) (L := L) (map (K := L) (L := M) x) = map (K := K) (L := M) x := by
  funext v
  let e := InfinitePlace.PlaceAbove.sigmaEquiv (K := K) (L := L) (M := M) v
  simp only [map_apply]
  calc
    _ = ∏ w : InfinitePlace.PlaceAbove (L := L) v,
          ∏ u : InfinitePlace.PlaceAbove (K := L) (L := M) w.1,
            InfinitePlace.localNorm v w.1
              (InfinitePlace.localNorm w.1 u.1 (x u.1)) := by
      apply Finset.prod_congr rfl
      intro w _
      exact map_prod (InfinitePlace.localNorm v w.1) _ Finset.univ
    _ = ∏ p : (Σ w : InfinitePlace.PlaceAbove (L := L) v,
          InfinitePlace.PlaceAbove (K := L) (L := M) w.1),
          InfinitePlace.localNorm v (e p).1 (x (e p).1) := by
      rw [Fintype.prod_sigma]
      apply Finset.prod_congr rfl
      intro w _
      apply Finset.prod_congr rfl
      intro u _
      have _ : u.1.LiesOver v := InfinitePlace.liesOver_trans v w.1 u.1
      change InfinitePlace.localNorm v w.1
          (InfinitePlace.localNorm w.1 u.1 (x u.1)) =
        InfinitePlace.localNorm v u.1 (x u.1)
      exact InfinitePlace.localNorm_trans v w.1 u.1 (x u.1)
    _ = _ := Equiv.prod_comp e (fun w : InfinitePlace.PlaceAbove (L := M) v ↦
      InfinitePlace.localNorm v w.1 (x w.1))

end Tower

end InfiniteIdeleNorm

/-! ### Norm on the full idèle group -/

namespace IdeleGroup

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L]

/-- The idèle norm for a finite extension, assembled as the product of the local norms over the
places above every base place. Milne, *Class Field Theory*, version 4.03, Chapter V, §4,
"Norms of idèles". -/
def norm :
    NumberField.IdeleGroup (NumberField.RingOfIntegers L) L →*
      NumberField.IdeleGroup (NumberField.RingOfIntegers K) K :=
  mapComponents (InfiniteIdeleNorm.map (K := K) (L := L)) (FiniteIdeleNorm.map (K := K) (L := L))

/-- The infinite component of the idèle norm is the product of the local norms above it. -/
@[simp]
theorem infiniteComponent_norm_apply
    (x : NumberField.IdeleGroup (NumberField.RingOfIntegers L) L)
    (v : NumberField.InfinitePlace K) :
    infiniteComponent K v (norm (K := K) (L := L) x) =
      ∏ w : InfinitePlace.PlaceAbove (L := L) v,
        SIC.InfinitePlace.localNorm v w.1 (infiniteComponent L w.1 x) := by
  change infiniteComponent K v
    (mapComponents (InfiniteIdeleNorm.map (K := K) (L := L))
      (FiniteIdeleNorm.map (K := K) (L := L)) x) = _
  rw [infiniteComponent_mapComponents]
  exact InfiniteIdeleNorm.map_apply (componentsContinuousEquiv L x).1 v

/-- The finite component of the idèle norm is the product of the local norms above it. -/
@[simp]
theorem finiteComponent_norm_apply
    (x : NumberField.IdeleGroup (NumberField.RingOfIntegers L) L)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    finiteComponent K v (norm (K := K) (L := L) x) =
      ∏ w : FinitePlace.PrimeAbove (L := L) v,
        FinitePlace.localNorm v (FinitePlace.PrimeAbove.place v w)
          (finiteComponent L (FinitePlace.PrimeAbove.place v w) x) := by
  change finiteComponent K v
    (mapComponents (InfiniteIdeleNorm.map (K := K) (L := L))
      (FiniteIdeleNorm.map (K := K) (L := L)) x) = _
  rw [finiteComponent_mapComponents]
  exact FiniteIdeleNorm.map_apply (componentsContinuousEquiv L x).2 v

/-! ### Principal idèles and towers -/

/-- The norm of a principal idèle is the principal idèle of the norm:
$N_{L/K}(\iota_L(x)) = \iota_K(N_{L/K}(x))$. Milne, *Class Field Theory*, Chapter V, §4,
"Norms of idèles"; the local formula is [83, Neukirch (1999), Chapter II, Corollary 8.4]. -/
theorem norm_unitEmbedding (x : Lˣ) :
    norm (K := K) (L := L) (NumberField.IdeleGroup.unitEmbedding (𝓞 L) L x) =
      NumberField.IdeleGroup.unitEmbedding (𝓞 K) K (Units.map (Algebra.norm K (S := L)) x) := by
  apply IdeleGroup.ext K
  · intro v
    rw [infiniteComponent_norm_apply]
    simp only [infiniteComponent_unitEmbedding]
    apply Units.ext
    simp only [Units.coe_prod, SIC.InfinitePlace.localNorm_val, Units.coe_map]
    exact (SIC.InfinitePlace.algebraMap_norm_eq_prod v (x : L)).symm
  · intro v
    rw [finiteComponent_norm_apply]
    simp only [finiteComponent_unitEmbedding]
    apply Units.ext
    simp only [Units.coe_prod, SIC.FinitePlace.localNorm_val, Units.coe_map]
    exact (SIC.FinitePlace.algebraMap_norm_eq_prod v (x : L)).symm

/-! ### Idèles supported at one place

The norm of an idèle supported at one place `w` of `L` is supported at the place `v` below it,
with component the local norm: every other place above `v` contributes a local norm of `1`. -/

/-- The norm of the idèle supported at a finite place `w` is the idèle supported at the place
`v` below it with component $N_{L_w/K_v}(x)$. Milne, *Class Field Theory*, Chapter V, §4,
"Norms of idèles". -/
theorem norm_ofAdicCompletion (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] (x : (w.adicCompletion L)ˣ) :
    norm (K := K) (L := L) (NumberField.IdeleGroup.ofAdicCompletion (𝓞 L) L w x) =
      NumberField.IdeleGroup.ofAdicCompletion (𝓞 K) K v (FinitePlace.localNorm v w x) := by
  classical
  apply ext K
  · intro u
    rw [infiniteComponent_norm_apply]
    simp only [infiniteComponent_ofAdicCompletion,
      map_one, Finset.prod_const_one]
  · intro u
    by_cases hu : u = v
    · subst u
      rw [finiteComponent_norm_apply]
      calc
        _ = FinitePlace.localNorm v w x := by
          rw [Finset.prod_eq_single (FinitePlace.PrimeAbove.mk v w)]
          · change FinitePlace.localNorm v w
              (finiteComponent L w (NumberField.IdeleGroup.ofAdicCompletion (𝓞 L) L w x)) =
                FinitePlace.localNorm v w x
            rw [finiteComponent_ofAdicCompletion_self]
          · intro q _ hq
            have hne : FinitePlace.PrimeAbove.place v q ≠ w := by
              intro heq
              exact hq (FinitePlace.PrimeAbove.place_injective v (by simpa using heq))
            rw [finiteComponent_ofAdicCompletion_of_ne L w _ hne x]
            exact (FinitePlace.localNorm v (FinitePlace.PrimeAbove.place v q)).map_one
          · simp
        _ = _ := (finiteComponent_ofAdicCompletion_self K v _).symm
    · rw [finiteComponent_norm_apply,
        finiteComponent_ofAdicCompletion_of_ne K v u hu (FinitePlace.localNorm v w x)]
      apply Finset.prod_eq_one
      intro q _
      have hne : FinitePlace.PrimeAbove.place u q ≠ w := by
        intro heq
        have hb : FinitePlace.below (K := K) w = u := by
          rw [← heq]
          exact FinitePlace.PrimeAbove.below_place u q
        exact hu (hb.symm.trans (FinitePlace.below_eq_of_liesOver v w))
      rw [finiteComponent_ofAdicCompletion_of_ne L w _ hne x]
      exact (FinitePlace.localNorm u (FinitePlace.PrimeAbove.place u q)).map_one

/-- The norm of the idèle supported at an infinite place `w` is the idèle supported at the place
`v` below it with component $N_{L_w/K_v}(x)$. Milne, *Class Field Theory*, Chapter V, §4,
"Norms of idèles". -/
theorem norm_ofCompletion (v : InfinitePlace K) (w : InfinitePlace L) [w.LiesOver v]
    (x : w.Completionˣ) :
    norm (K := K) (L := L) (NumberField.IdeleGroup.ofCompletion (𝓞 L) L w x) =
      NumberField.IdeleGroup.ofCompletion (𝓞 K) K v (InfinitePlace.localNorm v w x) := by
  classical
  apply ext K
  · intro u
    by_cases hu : u = v
    · subst u
      rw [infiniteComponent_norm_apply]
      calc
        _ = InfinitePlace.localNorm v w x := by
          rw [Finset.prod_eq_single
            (⟨w, show w ∈ v.placesOver L from (inferInstance : w.LiesOver v)⟩ :
              InfinitePlace.PlaceAbove (L := L) v)]
          · change InfinitePlace.localNorm v w
              (infiniteComponent L w (NumberField.IdeleGroup.ofCompletion (𝓞 L) L w x)) =
                InfinitePlace.localNorm v w x
            rw [infiniteComponent_ofCompletion_self]
          · intro q _ hq
            have hne : q.1 ≠ w := by
              intro heq
              exact hq (Subtype.ext heq)
            rw [infiniteComponent_ofCompletion_of_ne L q.1 w hne x]
            exact (InfinitePlace.localNorm v q.1).map_one
          · simp
        _ = _ := (infiniteComponent_ofCompletion_self K v _).symm
    · rw [infiniteComponent_norm_apply,
        infiniteComponent_ofCompletion_of_ne K u v hu (InfinitePlace.localNorm v w x)]
      apply Finset.prod_eq_one
      intro q _
      have hne : q.1 ≠ w := by
        intro heq
        have hb : InfinitePlace.below (K := K) w = u := by
          rw [← heq]
          exact InfinitePlace.below_eq_of_liesOver u q.1
        exact hu (hb.symm.trans (InfinitePlace.below_eq_of_liesOver v w))
      rw [infiniteComponent_ofCompletion_of_ne L q.1 w hne x]
      exact (InfinitePlace.localNorm u q.1).map_one
  · intro u
    rw [finiteComponent_norm_apply]
    simp only [finiteComponent_ofCompletion,
      map_one, Finset.prod_const_one]

/-- The norm maps principal idèles to principal idèles. -/
theorem principalSubgroup_le_comap_norm :
    NumberField.IdeleGroup.principalSubgroup (𝓞 L) L ≤
      (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K).comap (norm (K := K) (L := L)) := by
  rintro y ⟨x, rfl⟩
  exact ⟨Units.map (Algebra.norm K (S := L)) x, (norm_unitEmbedding x).symm⟩

variable {M : Type*} [Field M] [NumberField M] [Algebra L M] [Algebra K M]
  [IsScalarTower K L M]

/-- The idèle norm is transitive in towers: $N_{L/K} \circ N_{M/L} = N_{M/K}$. -/
theorem norm_norm (x : NumberField.IdeleGroup (𝓞 M) M) :
    norm (K := K) (L := L) (norm (K := L) (L := M) x) = norm (K := K) (L := M) x := by
  rw [show norm (K := K) (L := L) (norm (K := L) (L := M) x) =
    mapComponents (InfiniteIdeleNorm.map (K := K) (L := L))
      (FiniteIdeleNorm.map (K := K) (L := L))
      (mapComponents (InfiniteIdeleNorm.map (K := L) (L := M))
        (FiniteIdeleNorm.map (K := L) (L := M)) x) from rfl,
    mapComponents_mapComponents]
  apply (componentsEquiv K).injective
  simp only [componentsEquiv_mapComponents, MonoidHom.comp_apply]
  exact Prod.ext
    (InfiniteIdeleNorm.map_map (K := K) (L := L) (componentsContinuousEquiv M x).1)
    (FiniteIdeleNorm.map_map (K := K) (L := L) (componentsContinuousEquiv M x).2)

omit [Algebra L M] [IsScalarTower K L M] in
/-- Norms from a larger field are norms from a smaller one: if `L` embeds in `M` over `K`, then
$N_{M/K}J_M \subseteq N_{L/K}J_L$, since $N_{M/K} = N_{L/K}\circ N_{M/L}$. -/
theorem range_norm_le_of_algHom (f : L →ₐ[K] M) :
    (norm (K := K) (L := M)).range ≤ (norm (K := K) (L := L)).range := by
  let _ : Algebra L M := f.toRingHom.toAlgebra
  have _ : IsScalarTower K L M :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  rintro y ⟨x, rfl⟩
  exact ⟨norm (K := L) (L := M) x, norm_norm (K := K) (L := L) x⟩

end IdeleGroup

/-! ### Norm on idèle classes -/

namespace IdeleClassGroup

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L]

/-- The norm on idèle classes, induced by the idèle norm because principal idèles have principal
norms. Milne, *Class Field Theory*, version 4.03, Chapter V, §4, "Norms of idèles". -/
def norm :
    NumberField.IdeleClassGroup (𝓞 L) L →* NumberField.IdeleClassGroup (𝓞 K) K :=
  QuotientGroup.map _ _ (IdeleGroup.norm (K := K) (L := L))
    IdeleGroup.principalSubgroup_le_comap_norm

/-- The norm of the class of an idèle is the class of its norm. -/
@[simp]
theorem norm_mk (x : NumberField.IdeleGroup (𝓞 L) L) :
    norm (K := K) (L := L) (x : NumberField.IdeleClassGroup (𝓞 L) L) =
      (IdeleGroup.norm (K := K) (L := L) x : NumberField.IdeleClassGroup (𝓞 K) K) :=
  rfl

/-- The quotient map sends the idèle norm subgroup onto the idèle class norm subgroup.
This is the image identity used by `normResidueEquiv`. -/
theorem map_mk_range_norm :
    ((IdeleGroup.norm (K := K) (L := L)).range).map
        (QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K)) =
      (norm (K := K) (L := L)).range := by
  apply le_antisymm
  · rintro _ ⟨x, ⟨y, rfl⟩, rfl⟩
    exact ⟨(y : NumberField.IdeleClassGroup (𝓞 L) L), (norm_mk y).symm⟩
  · rintro _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨IdeleGroup.norm (K := K) (L := L) x, ⟨x, rfl⟩, norm_mk x⟩

variable {M : Type*} [Field M] [NumberField M] [Algebra L M] [Algebra K M]
  [IsScalarTower K L M]

/-- The norm on idèle classes is transitive in towers. -/
theorem norm_norm (x : NumberField.IdeleClassGroup (𝓞 M) M) :
    norm (K := K) (L := L) (norm (K := L) (L := M) x) = norm (K := K) (L := M) x := by
  refine QuotientGroup.induction_on x ?_
  intro y
  simp only [norm_mk, IdeleGroup.norm_norm]

omit [Algebra L M] [IsScalarTower K L M] in
/-- A $K$-embedding $L\to M$ gives
$N_{M/K}C_M\subseteq N_{L/K}C_L$; the class-group form of
`IdeleGroup.range_norm_le_of_algHom`. -/
theorem range_norm_le_of_algHom (f : L →ₐ[K] M) :
    (norm (K := K) (L := M)).range ≤ (norm (K := K) (L := L)).range := by
  rw [← map_mk_range_norm (K := K) (L := M), ← map_mk_range_norm (K := K) (L := L)]
  exact Subgroup.map_mono (IdeleGroup.range_norm_le_of_algHom f)

/-! ### Local groups at split places

At a place `v` with a place `w` above it of local degree one, every element of $K_v^\times$ is a
local norm from $L_w$, so the image of $K_v^\times$ in $C_K$ consists of norms. -/

/-- The class of the idèle supported at a finite place `w` has norm the class of the idèle
supported at `v` with component $N_{L_w/K_v}(x)$; the class form of
`IdeleGroup.norm_ofAdicCompletion`. -/
theorem norm_ofAdicCompletion (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] (x : (w.adicCompletion L)ˣ) :
    norm (K := K) (L := L) (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 L) L w x) =
      NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 K) K v (FinitePlace.localNorm v w x) := by
  change norm (K := K) (L := L)
    ((NumberField.IdeleGroup.ofAdicCompletion (𝓞 L) L w x) :
      NumberField.IdeleClassGroup (𝓞 L) L) = _
  rw [norm_mk, IdeleGroup.norm_ofAdicCompletion v w x]
  rfl

/-- The class of the idèle supported at an infinite place `w` has norm the class of the idèle
supported at `v` with component $N_{L_w/K_v}(x)$; the class form of
`IdeleGroup.norm_ofCompletion`. -/
theorem norm_ofCompletion (v : InfinitePlace K) (w : InfinitePlace L) [w.LiesOver v]
    (x : w.Completionˣ) :
    norm (K := K) (L := L) (NumberField.IdeleClassGroup.ofCompletion (𝓞 L) L w x) =
      NumberField.IdeleClassGroup.ofCompletion (𝓞 K) K v (InfinitePlace.localNorm v w x) := by
  change norm (K := K) (L := L)
    ((NumberField.IdeleGroup.ofCompletion (𝓞 L) L w x) :
      NumberField.IdeleClassGroup (𝓞 L) L) = _
  rw [norm_mk, IdeleGroup.norm_ofCompletion v w x]
  rfl

/-- If a finite place `w` above `v` has local degree $[L_w:K_v]=1$, the image of $K_v^\times$ in
$C_K$ lies in $N_{L/K}C_L$. Childress, *Class Field Theory*, Chapter VI, proof of
Theorem 2.8. -/
theorem range_ofAdicCompletion_le_range_norm (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (h : Module.finrank (v.adicCompletion K) (w.adicCompletion L) = 1) :
    (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 K) K v).range ≤
      (norm (K := K) (L := L)).range := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := FinitePlace.localNorm_surjective_of_finrank_eq_one v w h x
  refine ⟨NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 L) L w y, ?_⟩
  rw [norm_ofAdicCompletion v w y, hy]

/-- If an infinite place `w` above `v` has local degree $[L_w:K_v]=1$, the image of
$K_v^\times$ in $C_K$ lies in $N_{L/K}C_L$; the infinite case of Childress, *Class Field
Theory*, Chapter VI, proof of Theorem 2.8. -/
theorem range_ofCompletion_le_range_norm (v : InfinitePlace K) (w : InfinitePlace L)
    [w.LiesOver v] (h : Module.finrank v.Completion w.Completion = 1) :
    (NumberField.IdeleClassGroup.ofCompletion (𝓞 K) K v).range ≤
      (norm (K := K) (L := L)).range := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := InfinitePlace.localNorm_surjective_of_finrank_eq_one v w h x
  refine ⟨NumberField.IdeleClassGroup.ofCompletion (𝓞 L) L w y, ?_⟩
  rw [norm_ofCompletion v w y, hy]

end IdeleClassGroup

end SIC

end
