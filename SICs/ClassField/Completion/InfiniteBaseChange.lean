/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Completion.Norm
import SICs.ClassField.Completion.PlacesAbove
import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing

/-!
# The completed base change at an infinite place

The isomorphism $K_v \otimes_K L \cong \prod_{w \mid v} L_w$ for a finite extension of number
fields `L/K` and an infinite place `v` of `K`, with the norm formula
$N_{L/K}(x) = \prod_{w \mid v} N_{L_w/K_v}(x)$.

This is [83, Neukirch (1999), Chapter II, Proposition 8.3 and Corollary 8.4] at an infinite
place, proved as in Serre, *Local Fields*, Chapter II, §3, Theorem 1(iii).

## The argument

The canonical map sends $a \otimes x$ to $(a x)_{w \mid v}$. Weak approximation at the infinite
places of `L`, `NumberField.InfinitePlace.denseRange_algebraMap_pi`, makes `L` dense in the
product of its completions at all infinite places, hence in the factor
$\prod_{w \mid v} L_w$. The image of the finite-dimensional $K_v$-space $K_v \otimes_K L$ is closed
and contains `L`, so the map is surjective. Mathlib's
`NumberField.InfinitePlace.sum_inertiaDeg_eq_finrank` gives
$\sum_{w \mid v} [L_w : K_v] = [L : K] = \dim_{K_v}(K_v \otimes_K L)$, so the surjection is an
isomorphism. The norm formula then follows from `SICs.FieldTheory.BaseChange`.
-/

noncomputable section

open NumberField
open scoped TensorProduct NumberField.LiesOver SIC.InfinitePlace

namespace SIC

namespace InfinitePlace

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [NumberField K] [NumberField L]
  (v : NumberField.InfinitePlace K)

/-- The canonical map $K_v \otimes_K L \to \prod_{w \mid v} L_w$,
$a \otimes x \mapsto (a x)_{w \mid v}$, at an infinite place. -/
def baseChangeAlgHom :
    v.Completion ⊗[K] L →ₐ[v.Completion] ∀ w : PlaceAbove (L := L) v, w.1.Completion :=
  baseChangePi fun w ↦ IsScalarTower.toAlgHom K L w.1.Completion

omit [NumberField K] [NumberField L] in
/-- Evaluation of `baseChangeAlgHom` on a pure tensor. -/
@[simp]
theorem baseChangeAlgHom_tmul (a : v.Completion) (x : L) (w : PlaceAbove (L := L) v) :
    baseChangeAlgHom v (a ⊗ₜ x) w =
      algebraMap v.Completion w.1.Completion a * algebraMap L w.1.Completion x := by
  exact baseChangePi_tmul _ a x w

/-- The local degrees above an infinite place add up to the global degree:
$\sum_{w \mid v} [L_w : K_v] = [L : K]$. Mathlib's
`NumberField.InfinitePlace.sum_inertiaDeg_eq_finrank`, indexed by `PlaceAbove`. -/
theorem sum_finrank_placeAbove :
    ∑ w : PlaceAbove (L := L) v, Module.finrank v.Completion w.1.Completion =
      Module.finrank K L := by
  classical
  calc
    _ = ∑ w : PlaceAbove (L := L) v, v.inertiaDeg w.1 := by
      apply Finset.sum_congr rfl
      intro w _
      exact (NumberField.InfinitePlace.inertiaDeg_eq_finrank v w.1).symm
    _ = Module.finrank K L := by
      change (∑ w : ↥(v.placesOver L), v.inertiaDeg w.1) = _
      rw [Finset.sum_set_coe]
      exact NumberField.InfinitePlace.sum_inertiaDeg_eq_finrank K L v

/-- The canonical map $K_v \otimes_K L \to \prod_{w \mid v} L_w$ is surjective at an infinite
place. Serre, *Local Fields*, Chapter II, §3, proof of Theorem 1(iii). -/
theorem baseChangeAlgHom_surjective : Function.Surjective (baseChangeAlgHom (L := L) v) := by
  classical
  let proj : ((w : NumberField.InfinitePlace L) → w.Completion) →
      (w : PlaceAbove (L := L) v) → w.1.Completion := fun f w ↦ f w.1
  have hproj_cont : Continuous proj := continuous_pi fun w ↦ continuous_apply w.1
  have hproj_surj : Function.Surjective proj := by
    intro y
    refine ⟨fun w ↦ if h : w.LiesOver v then y ⟨w, h⟩ else 0, ?_⟩
    funext ⟨w, hw⟩
    change w.LiesOver v at hw
    simp [proj, hw]
  have hdense_global : DenseRange
      (algebraMap L (NumberField.InfiniteAdeleRing L)) :=
    NumberField.InfiniteAdeleRing.denseRange_algebraMap L
  have hdense : DenseRange (fun x : L ↦
      fun w : PlaceAbove (L := L) v ↦ algebraMap L w.1.Completion x) := by
    convert hproj_surj.denseRange.comp hdense_global hproj_cont using 1
    funext x w
    change (algebraMap L w.1.Completion) x =
      (algebraMap L (NumberField.InfiniteAdeleRing L)) x w.1
    rfl
  change Function.Surjective (baseChangeAlgHom v).toLinearMap
  refine surjective_of_denseRange_tmul (K := K) (A := v.Completion) (L := L)
    (B := ∀ w : PlaceAbove (L := L) v, w.1.Completion)
    (baseChangeAlgHom v).toLinearMap ?_
  convert hdense using 1
  funext x w
  simp

/-- The canonical map $K_v \otimes_K L \to \prod_{w \mid v} L_w$ is injective at an infinite
place, by the degree count `sum_finrank_placeAbove`. -/
theorem baseChangeAlgHom_injective : Function.Injective (baseChangeAlgHom (L := L) v) := by
  have hdim : Module.finrank v.Completion (v.Completion ⊗[K] L) =
      Module.finrank v.Completion (∀ w : PlaceAbove (L := L) v, w.1.Completion) := by
    calc
      Module.finrank v.Completion (v.Completion ⊗[K] L) = Module.finrank K L :=
        Module.finrank_baseChange
      _ = ∑ w : PlaceAbove (L := L) v, Module.finrank v.Completion w.1.Completion :=
        (sum_finrank_placeAbove v).symm
      _ = Module.finrank v.Completion (∀ w : PlaceAbove (L := L) v, w.1.Completion) :=
        (Module.finrank_pi_fintype v.Completion).symm
  change Function.Injective (baseChangeAlgHom v).toLinearMap
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2
    (baseChangeAlgHom_surjective v)

/-- The decomposition $K_v \otimes_K L \cong \prod_{w \mid v} L_w$ at an infinite place.
[83, Neukirch (1999), Chapter II, Proposition 8.3]. -/
@[source "83, Chapter II, Proposition 8.3, p. 164 (infinite place)"]
def baseChangeEquiv :
    v.Completion ⊗[K] L ≃ₐ[v.Completion] ∀ w : PlaceAbove (L := L) v, w.1.Completion :=
  AlgEquiv.ofBijective (baseChangeAlgHom v)
    ⟨baseChangeAlgHom_injective v, baseChangeAlgHom_surjective v⟩

/-- The decomposition sends $1 \otimes x$ to the diagonal image of `x`. -/
@[simp]
theorem baseChangeEquiv_one_tmul (x : L) (w : PlaceAbove (L := L) v) :
    baseChangeEquiv v ((1 : v.Completion) ⊗ₜ x) w = algebraMap L w.1.Completion x := by
  change baseChangeAlgHom v ((1 : v.Completion) ⊗ₜ x) w = _
  simp

/-- The norm of `x ∈ L` is the product of its local norms above an infinite place:
$N_{L/K}(x) = \prod_{w \mid v} N_{L_w/K_v}(x)$ in $K_v$.
[83, Neukirch (1999), Chapter II, Corollary 8.4]. -/
@[source "83, Chapter II, Corollary 8.4, p. 164 (norm, infinite place)"]
theorem algebraMap_norm_eq_prod (x : L) :
    algebraMap K v.Completion (Algebra.norm K x) =
      ∏ w : PlaceAbove (L := L) v,
        Algebra.norm v.Completion (algebraMap L w.1.Completion x) := by
  simpa only [baseChangeEquiv_one_tmul] using
    algebraMap_norm_eq_prod_of_algEquiv (baseChangeEquiv v) x

end InfinitePlace

end SIC
