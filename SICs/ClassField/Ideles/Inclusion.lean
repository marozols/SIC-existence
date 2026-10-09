/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Ideles.Norm

/-!
# The inclusion of idèles in a finite extension

The homomorphism $I_K \to I_L$ of idèle groups for a finite extension of number fields `L/K`,
sending an idèle $(x_v)_v$ to the idèle with component $x_v \in K_v \subseteq L_w$ at every place
`w` of `L` above `v`, its descent $C_K \to C_L$ to idèle classes, and the formula
$N_{L/K}(x) = x^{[L : K]}$ for the norm of an included idèle.

This is the map $I_K \hookrightarrow I_L$ of Milne, *Class Field Theory*, version 4.03 (2020),
Chapter VII, §2, Proposition 2.5(a).

## The argument

At a finite place `w` of `L`, the component is the completion map $K_v \to L_w$ applied to the
component at the place `v` below `w`. Completion maps preserve integral units, and only finitely
many places of `L` lie above each place of `K`, so the exceptional places of the image lie above
the finitely many exceptional places of `x`; Mathlib's `RestrictedProduct.mapAlongMonoidHom`
assembles the restricted product. At infinite places the map is a plain product. On a
principal idèle every component is the image of the global element, so principal idèles go to
principal idèles and the map descends to idèle classes.

The norm of an included idèle has component $\prod_{w \mid v} N_{L_w/K_v}(x_v) = \prod_{w \mid v}
x_v^{[L_w : K_v]} = x_v^{[L : K]}$ at `v`, by `FinitePlace.localNorm_principal` and the degree
formula $\sum_{w \mid v} [L_w : K_v] = [L : K]$ of `SICs.ClassField.Completion.FiniteBaseChange` and
`SICs.ClassField.Completion.InfiniteBaseChange`.
-/

noncomputable section

open Filter IsDedekindDomain NumberField
open scoped NumberField NumberField.AdeleRing NumberField.LiesOver RestrictedProduct
  SIC.FinitePlace SIC.InfinitePlace

namespace SIC

namespace IdeleGroup

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [NumberField K] [NumberField L]

/-! ### The two local parts -/

-- The local maps are passed as `(f : A →+* B).toMonoidHom`: with the coercion `(f : A →* B)`,
-- elaborating `RestrictedProduct.mapAlongMonoidHom` times out in `isDefEq`.
/-- The finite part of the inclusion, $(x_v)_v \mapsto (x_{w|_K})_w$ on restricted products. -/
private def finiteInclusion : FiniteLocalIdele K →* FiniteLocalIdele L :=
  RestrictedProduct.mapAlongMonoidHom
    (fun v : HeightOneSpectrum (𝓞 K) ↦ (v.adicCompletion K)ˣ)
    (fun w : HeightOneSpectrum (𝓞 L) ↦ (w.adicCompletion L)ˣ)
    (FinitePlace.below (K := K) (L := L)) FinitePlace.tendsto_below_cofinite
    (fun w ↦ Units.map (FinitePlace.completionMap (FinitePlace.below w) w).toMonoidHom)
    (Filter.Eventually.of_forall fun w _ hx ↦
      (FinitePlace.units_map_completionMap_mem_iff (FinitePlace.below w) w).2 hx)

/-- The infinite part of the inclusion, $(x_v)_v \mapsto (x_{w|_K})_w$ on products. -/
private def infiniteInclusion : InfiniteLocalIdele K →* InfiniteLocalIdele L :=
  MonoidHom.pi fun w ↦
    (Units.map (NumberField.LiesOver.completionMap (v := InfinitePlace.below (K := K) w)
      (w := w)).toMonoidHom).comp
      (Pi.evalMonoidHom _ (InfinitePlace.below (K := K) w))

/-! ### The inclusion of idèles -/

/-- The inclusion of idèles $I_K \to I_L$: the component at a place `w` of `L` is the component at
the place below `w`, embedded in $L_w$. Milne, *Class Field Theory*, Chapter VII, §2,
Proposition 2.5(a). -/
def inclusion :
    NumberField.IdeleGroup (𝓞 K) K →* NumberField.IdeleGroup (𝓞 L) L :=
  mapComponents infiniteInclusion finiteInclusion

/-- The component of an included idèle at a finite place `w` above `v` is the component at `v`,
embedded in $L_w$. -/
theorem finiteComponent_inclusion (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] (x : NumberField.IdeleGroup (𝓞 K) K) :
    finiteComponent L w (inclusion x) =
      Units.map (FinitePlace.completionMap v w : v.adicCompletion K →* w.adicCompletion L)
        (finiteComponent K v x) := by
  have hv := FinitePlace.below_eq_of_liesOver v w
  subst v
  change finiteComponent L w (mapComponents infiniteInclusion finiteInclusion x) = _
  rw [finiteComponent_mapComponents]
  exact RestrictedProduct.mapAlongMonoidHom_apply _ _ _ _ _ _ _ _

/-- The component of an included idèle at an infinite place `w` above `v` is the component at
`v`, embedded in $L_w$. -/
theorem infiniteComponent_inclusion (v : InfinitePlace K) (w : InfinitePlace L) [w.LiesOver v]
    (x : NumberField.IdeleGroup (𝓞 K) K) :
    infiniteComponent L w (inclusion x) =
      Units.map (NumberField.LiesOver.completionMap (v := v) (w := w) :
        v.Completion →* w.Completion) (infiniteComponent K v x) := by
  have hv := InfinitePlace.below_eq_of_liesOver v w
  subst v
  change infiniteComponent L w (mapComponents infiniteInclusion finiteInclusion x) = _
  rw [infiniteComponent_mapComponents]
  rfl

/-- The inclusion of idèles $I_K \to I_L$ is injective. Milne, *Class Field Theory*,
Chapter VII, §2, Proposition 2.5(a). -/
theorem inclusion_injective : Function.Injective (inclusion (K := K) (L := L)) := by
  classical
  intro x y h
  apply ext K
  · intro v
    let w := (Classical.arbitrary (InfinitePlace.PlaceAbove (L := L) v)).1
    apply Units.map_injective (NumberField.LiesOver.completionMap (v := v) (w := w)).injective
    have hc := congrArg (infiniteComponent L w) h
    rwa [infiniteComponent_inclusion v w, infiniteComponent_inclusion v w] at hc
  · intro v
    let w := FinitePlace.PrimeAbove.place v
      (Classical.arbitrary (FinitePlace.PrimeAbove (L := L) v))
    apply Units.map_injective (FinitePlace.completionMap v w).injective
    have hc := congrArg (finiteComponent L w) h
    rwa [finiteComponent_inclusion v w, finiteComponent_inclusion v w] at hc

/-- The inclusion maps the principal idèle of `x ∈ Kˣ` to the principal idèle of `x ∈ Lˣ`. -/
@[simp]
theorem inclusion_unitEmbedding (x : Kˣ) :
    inclusion (L := L) (NumberField.IdeleGroup.unitEmbedding (𝓞 K) K x) =
      NumberField.IdeleGroup.unitEmbedding (𝓞 L) L (Units.map (algebraMap K L) x) := by
  apply ext L
  · intro w
    let v := InfinitePlace.below (K := K) w
    rw [infiniteComponent_inclusion v w, infiniteComponent_unitEmbedding,
      infiniteComponent_unitEmbedding]
    apply Units.ext
    change NumberField.LiesOver.completionMap (algebraMap K v.Completion (x : K)) =
      algebraMap L w.Completion (algebraMap K L (x : K))
    calc
      _ = algebraMap K w.Completion (x : K) :=
        (IsScalarTower.algebraMap_apply K v.Completion w.Completion (x : K)).symm
      _ = _ := IsScalarTower.algebraMap_apply K L w.Completion (x : K)
  · intro w
    let v := FinitePlace.below (K := K) w
    rw [finiteComponent_inclusion v w, finiteComponent_unitEmbedding,
      finiteComponent_unitEmbedding]
    apply Units.ext
    exact FinitePlace.completionMap_algebraMap v w (x : K)

/-- The inclusion maps principal idèles to principal idèles. -/
theorem principalSubgroup_le_comap_inclusion :
    NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ≤
      (NumberField.IdeleGroup.principalSubgroup (𝓞 L) L).comap (inclusion (K := K) (L := L)) := by
  intro y hy
  obtain ⟨x, hx⟩ := hy
  change ∃ z : Lˣ, NumberField.IdeleGroup.unitEmbedding (𝓞 L) L z =
    inclusion (K := K) (L := L) y
  refine ⟨Units.map (algebraMap K L) x, ?_⟩
  rw [← hx]
  exact (inclusion_unitEmbedding (K := K) (L := L) x).symm

/-- The norm of an included idèle is its `[L : K]`-th power: $N_{L/K}(x) = x^{[L : K]}$. -/
@[simp]
theorem norm_inclusion (x : NumberField.IdeleGroup (𝓞 K) K) :
    norm (K := K) (L := L) (inclusion x) = x ^ Module.finrank K L := by
  apply ext K
  · intro v
    calc
      infiniteComponent K v (norm (K := K) (L := L) (inclusion x)) =
          ∏ w : InfinitePlace.PlaceAbove (L := L) v,
            (infiniteComponent K v x) ^ Module.finrank v.Completion w.1.Completion := by
        rw [infiniteComponent_norm_apply]
        apply Finset.prod_congr rfl
        intro w _
        rw [infiniteComponent_inclusion v w.1 x, InfinitePlace.localNorm_principal]
      _ = infiniteComponent K v (x ^ Module.finrank K L) := by
        rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_finrank_placeAbove]
        exact (map_pow (infiniteComponent K v) x (Module.finrank K L)).symm
  · intro v
    calc
      finiteComponent K v (norm (K := K) (L := L) (inclusion x)) =
          ∏ w : FinitePlace.PrimeAbove (L := L) v,
            (finiteComponent K v x) ^
              Module.finrank (v.adicCompletion K)
                ((FinitePlace.PrimeAbove.place v w).adicCompletion L) := by
        rw [finiteComponent_norm_apply]
        apply Finset.prod_congr rfl
        intro w _
        rw [finiteComponent_inclusion v (FinitePlace.PrimeAbove.place v w) x,
          FinitePlace.localNorm_principal]
      _ = finiteComponent K v (x ^ Module.finrank K L) := by
        rw [Finset.prod_pow_eq_pow_sum, FinitePlace.sum_finrank_primeAbove]
        exact (map_pow (finiteComponent K v) x (Module.finrank K L)).symm

end IdeleGroup

/-! ### The inclusion of idèle classes -/

namespace IdeleClassGroup

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [NumberField K] [NumberField L]

/-- The homomorphism $C_K \to C_L$ of idèle class groups induced by the inclusion of idèles. -/
def inclusion :
    NumberField.IdeleClassGroup (𝓞 K) K →* NumberField.IdeleClassGroup (𝓞 L) L :=
  QuotientGroup.map _ _ (IdeleGroup.inclusion (K := K) (L := L))
    IdeleGroup.principalSubgroup_le_comap_inclusion

/-- The inclusion of the class of an idèle is the class of its inclusion. -/
@[simp]
theorem inclusion_mk (x : NumberField.IdeleGroup (𝓞 K) K) :
    inclusion (L := L) (x : NumberField.IdeleClassGroup (𝓞 K) K) =
      (IdeleGroup.inclusion (L := L) x : NumberField.IdeleClassGroup (𝓞 L) L) :=
  rfl

/-- The norm of an included idèle class is its `[L : K]`-th power. -/
@[simp]
theorem norm_inclusion (x : NumberField.IdeleClassGroup (𝓞 K) K) :
    norm (K := K) (L := L) (inclusion x) = x ^ Module.finrank K L := by
  refine Quotient.inductionOn x ?_
  intro y
  simp only [inclusion_mk, norm_mk, IdeleGroup.norm_inclusion]
  exact QuotientGroup.mk_pow
    (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K) y (Module.finrank K L)

end IdeleClassGroup

end SIC
