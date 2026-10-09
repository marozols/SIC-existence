/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Analytic and meromorphic identity theorems

Identity theorems from the real axis and for meromorphic germs, agreement off a countable set,
meromorphic normal forms, and almost-everywhere equality of functions with equal germs on lines.

## Mathematical argument

The real points of an open set near one real point accumulate there. Agreement on those
points therefore extends throughout a connected domain by the analytic identity theorem
(`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`). This is the continuation step
used for the double-sine shift integral and the equal-period hyperbolic gamma function.

For meromorphic functions on a preconnected set, agreement in one punctured neighborhood
propagates to every point. Apply the meromorphic order theorem to their difference:
order infinity at one point implies order infinity throughout the set. The conclusion
is equality of germs, so it is independent of values assigned at poles or removable points.
The complement of a countable set accumulates at every point, so two functions meromorphic at
`z` that agree off a countable set have the same punctured germ at `z`.

The value at `s` of the normal form of `F` at `s` is the project's continued value: it agrees
with every analytic function equal to `F` on a punctured neighbourhood
(`toMeromorphicNFAt_eventuallyEq_nhds_congr`, `toMeromorphicNFAt_eq_self`).

Finally, two functions with the same punctured germ at every point differ on a set all of whose
points are isolated in it. Such a set is countable, so its preimage under a nonconstant affine
map `ℝ → ℂ` is countable and hence null.
-/

open Filter Topology Set MeasureTheory

namespace SIC

/-! ### The identity theorem from the real axis -/

/-- **Identity theorem from the real axis.** Two functions holomorphic on a connected open set
`U ⊆ ℂ` that agree at every real point of `U`, of which there is at least one, agree on `U`. -/
theorem eqOn_of_differentiableOn_of_eqOn_real {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsPreconnected U) (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    {x₀ : ℝ} (hx₀ : (x₀ : ℂ) ∈ U) (h : ∀ x : ℝ, (x : ℂ) ∈ U → f x = g x) :
    Set.EqOn f g U := by
  have hofReal : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] x₀) (𝓝[≠] (x₀ : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simpa using hx
  have hUreal : ∀ᶠ x : ℝ in 𝓝 x₀, (x : ℂ) ∈ U :=
    Complex.continuous_ofReal.continuousAt (hU.mem_nhds hx₀)
  have heq : ∀ᶠ x : ℝ in 𝓝[≠] x₀, f (x : ℂ) = g (x : ℂ) := by
    filter_upwards [hUreal.filter_mono nhdsWithin_le_nhds] with x hx
    exact h x hx
  have hfreq : ∃ᶠ z in 𝓝[≠] (x₀ : ℂ), f z = g z :=
    hofReal.frequently (Eventually.frequently heq)
  exact (hf.analyticOnNhd hU).eqOn_of_preconnected_of_frequently_eq
    (hg.analyticOnNhd hU) hUc hx₀ hfreq

/-! ### Meromorphic identity principle

Equality in a punctured neighborhood means that the difference has infinite meromorphic
order there. Preconnectedness propagates this condition to the other points.
-/

/-- Meromorphic functions on a preconnected set that agree near one point agree in a
punctured neighborhood of every point of that set. This is the identity principle in
`MeromorphicOn.meromorphicOrderAt_eq_top_of_isPreconnected`, applied to their difference. -/
theorem MeromorphicOn.eventuallyEq_nhdsNE_of_isPreconnected {f g : ℂ → ℂ}
    {U : Set ℂ} {x y : ℂ} (hf : MeromorphicOn f U) (hg : MeromorphicOn g U)
    (hU : IsPreconnected U) (hx : x ∈ U) (hy : y ∈ U)
    (hfg : f =ᶠ[𝓝[≠] x] g) : f =ᶠ[𝓝[≠] y] g := by
  apply eventuallyEq_iff_sub.mpr
  apply meromorphicOrderAt_eq_top_iff.mp
  exact (hf.sub hg).meromorphicOrderAt_eq_top_of_isPreconnected hU hx hy
    (meromorphicOrderAt_eq_top_iff.mpr hfg.sub_eq)

/-- The complement of a countable set accumulates at every complex point. -/
theorem Set.Countable.frequently_notMem_nhdsNE {S : Set ℂ} (hS : S.Countable) (z : ℂ) :
    ∃ᶠ w in 𝓝[≠] z, w ∉ S := by
  change ∃ᶠ w in 𝓝[≠] z, w ∈ Sᶜ
  apply mem_closure_ne_iff_frequently_within.mp
  have hdense := (hS.union (Set.countable_singleton z)).dense_compl ℂ
  simpa only [compl_union, compl_singleton_eq, inter_comm, Set.sdiff_eq] using hdense z

/-- Two functions meromorphic at `z` that agree off a countable set agree on a punctured
neighborhood of `z`, by `Set.Countable.frequently_notMem_nhdsNE` and the meromorphic
identity theorem. -/
theorem MeromorphicAt.eventuallyEq_nhdsNE_of_countable {f g : ℂ → ℂ} {z : ℂ} {S : Set ℂ}
    (hf : MeromorphicAt f z) (hg : MeromorphicAt g z) (hS : S.Countable)
    (hfg : ∀ w ∉ S, f w = g w) : f =ᶠ[𝓝[≠] z] g := by
  apply (hf.frequently_eq_iff_eventuallyEq hg).mp
  exact (Set.Countable.frequently_notMem_nhdsNE hS z).mono fun w hw => hfg w hw

/-! ### Meromorphic normal forms

The value at `s` of the normal form of `F` at `s` removes the removable singularities of `F` and
does not depend on the values `F` takes at isolated points. This is the project's convention for
continued values: it agrees with every analytic function equal to `F` on a punctured
neighbourhood. -/

/-- If `F` agrees with an analytic `G` on a punctured neighbourhood of `x`, the normal form of
`F` at `x` agrees with `G` on a neighbourhood of `x`. -/
theorem AnalyticAt.toMeromorphicNFAt_eventuallyEq {F G : ℂ → ℂ} {x : ℂ}
    (hG : AnalyticAt ℂ G x) (h : F =ᶠ[𝓝[≠] x] G) : toMeromorphicNFAt F x =ᶠ[𝓝 x] G := by
  have h1 : toMeromorphicNFAt F x =ᶠ[𝓝 x] toMeromorphicNFAt G x :=
    toMeromorphicNFAt_eventuallyEq_nhds_congr h
  rwa [toMeromorphicNFAt_eq_self.mpr hG.meromorphicNFAt] at h1

/-- If `F` agrees with an analytic `G` on a punctured neighbourhood of `x`, the normal form of
`F` at `x` takes the value `G x` at `x`. -/
theorem toMeromorphicNFAt_self_eq {F G : ℂ → ℂ} {x : ℂ} (hG : AnalyticAt ℂ G x)
    (h : F =ᶠ[𝓝[≠] x] G) : toMeromorphicNFAt F x x = G x :=
  (AnalyticAt.toMeromorphicNFAt_eventuallyEq hG h).eq_of_nhds

/-! ### Germ identities and lines

Two functions with the same germ at every point differ on a set whose points are all isolated,
hence countable; such a set meets every line in a null set. -/

/-- The set where two functions with equal punctured germs at every point differ is countable:
each of its points is isolated in it, and a subset of a second-countable space all of whose
points are isolated is countable. -/
theorem countable_setOf_ne_of_forall_eventuallyEq_nhdsNE {f g : ℂ → ℂ}
    (h : ∀ z : ℂ, f =ᶠ[𝓝[≠] z] g) : {z : ℂ | f z ≠ g z}.Countable := by
  have hdiscrete : IsDiscrete {z : ℂ | f z ≠ g z} := by
    rw [isDiscrete_iff_nhdsNE]
    intro z hz
    rw [Filter.inf_principal_eq_bot]
    filter_upwards [h z] with w hw
    simpa only [mem_compl_iff, mem_ofPred_eq, not_ne_iff] using hw
  exact (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hdiscrete

/-- Two functions with equal punctured germs at every point agree almost everywhere on every
nonconstant affine real line `t ↦ a t + b`: the exceptional set is countable
(`countable_setOf_ne_of_forall_eventuallyEq_nhdsNE`) and its preimage under the injective map
is null. -/
theorem ae_eq_comp_affine_of_forall_eventuallyEq_nhdsNE {f g : ℂ → ℂ}
    (h : ∀ z : ℂ, f =ᶠ[𝓝[≠] z] g) (a b : ℂ) (ha : a ≠ 0) :
    ∀ᵐ t : ℝ, f (a * t + b) = g (a * t + b) := by
  have hinj : Function.Injective (fun t : ℝ => a * (t : ℂ) + b) := by
    intro x y hxy
    exact Complex.ofReal_injective (mul_left_cancel₀ ha (add_right_cancel hxy))
  have hcount : {t : ℝ | f (a * t + b) ≠ g (a * t + b)}.Countable := by
    change ((fun t : ℝ => a * (t : ℂ) + b) ⁻¹' {z : ℂ | f z ≠ g z}).Countable
    exact (countable_setOf_ne_of_forall_eventuallyEq_nhdsNE h).preimage hinj
  simpa only [Set.mem_ofPred_eq, not_ne_iff] using
    (hcount.ae_notMem (MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure ℝ))

end SIC
