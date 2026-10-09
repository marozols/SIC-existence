/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-!
# Exact ball radii in the ultrametric inverse theorem

Local bijectivity and exact norm scaling for maps with a nonzero strict derivative.

This is an elementary consequence of Mathlib's inverse function theorem over a complete
normed field, strengthened by the ultrametric inequality. It supplies the local contraction
step of Serre, *Local Fields* (1979), Chapter XIV, §4, Proposition 9, in the power-index proof.

## The argument

On a sufficiently small neighborhood, the error in the strict linear approximation has norm
smaller than the nonzero linear term. The ultrametric inequality gives exact distance scaling
by the norm of the derivative. Mathlib's inverse function theorem makes the image a
neighborhood of the image point. Shrinking inside that image gives a bijection of closed
balls with exactly scaled radii.
-/

noncomputable section

open Filter Metric Set
open scoped Topology

namespace SIC

variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F]

/-! ### Exact scaling and inversion

The linear approximation error is strictly smaller than the linear term; the ultrametric
inequality makes their norms equal, and local openness supplies the inverse on a ball. -/

/-- A nonzero strict derivative gives exact local norm scaling over an ultrametric field;
used in `exists_closedBall_bijOn`. -/
private theorem exists_nhds_norm_sub_eq {f : F → F} {a b : F}
    (hf : HasStrictDerivAt f b a) (hb : b ≠ 0) :
    ∃ s ∈ 𝓝 a, ∀ x ∈ s, ∀ y ∈ s, ‖f x - f y‖ = ‖b‖ * ‖x - y‖ := by
  have hbn : 0 < ‖b‖₊ := nnnorm_pos.mpr hb
  obtain ⟨s, hs, happrox⟩ := hf.hasStrictFDerivAt.approximates_deriv_on_nhds
    (c := ‖b‖₊ / 2) (Or.inr (half_pos hbn))
  refine ⟨s, hs, ?_⟩
  intro x hx y hy
  by_cases hxy : x = y
  · simp [hxy]
  have hxypos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hsmall : ‖f x - f y - b * (x - y)‖ < ‖b * (x - y)‖ := by
    have he := happrox x hx y hy
    change ‖f x - f y - (x - y) • b‖ ≤ ↑(‖b‖₊ / 2) * ‖x - y‖ at he
    rw [smul_eq_mul, mul_comm (x - y) b] at he
    refine he.trans_lt ?_
    simp only [NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm, norm_mul]
    nlinarith [norm_pos_iff.mpr hb]
  have heq := IsUltrametricDist.norm_eq_of_add_norm_lt_max
    (x := f x - f y) (y := -(b * (x - y)))
    (by simpa only [← sub_eq_add_neg, norm_neg] using
      hsmall.trans_le (le_max_right ‖f x - f y‖ ‖b * (x - y)‖))
  simpa only [norm_neg, norm_mul] using heq

/-- A nonzero strict derivative over a complete ultrametric field gives exact distance
scaling and a bijection on sufficiently small closed balls. This refines Mathlib’s
`HasStrictDerivAt.map_nhds_eq` by the ultrametric inequality. -/
theorem exists_closedBall_bijOn [CompleteSpace F]
    {f : F → F} {a b : F} (hf : HasStrictDerivAt f b a) (hb : b ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      (∀ x ∈ closedBall a r, ∀ y ∈ closedBall a r,
        ‖f x - f y‖ = ‖b‖ * ‖x - y‖) ∧
      BijOn f (closedBall a r) (closedBall (f a) (‖b‖ * r)) := by
  obtain ⟨s, hs, hnorm⟩ := exists_nhds_norm_sub_eq hf hb
  have ha : a ∈ s := mem_of_mem_nhds hs
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
  have himg : f '' s ∈ 𝓝 (f a) := by
    rw [← hf.map_nhds_eq hb]
    exact Filter.image_mem_map hs
  obtain ⟨δ, hδ, hδball⟩ := Metric.mem_nhds_iff.mp himg
  have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb
  obtain ⟨r, hr, hrbound⟩ := exists_between (lt_min hε (lt_min (div_pos hδ hbn) zero_lt_one))
  have hre : r < ε := hrbound.trans_le (min_le_left _ _)
  have hrd : ‖b‖ * r < δ := by
    have hh := hrbound.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    simpa only [mul_comm r ‖b‖] using (lt_div_iff₀ hbn).mp hh
  have hr1 : r < 1 := hrbound.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hrs : closedBall a r ⊆ s :=
    fun x hx => hball (mem_ball.mpr ((mem_closedBall.mp hx).trans_lt hre))
  have hnorm' := fun x hx y hy => hnorm x (hrs hx) y (hrs hy)
  refine ⟨r, hr, hr1, hnorm', ?_, ?_, ?_⟩
  · intro x hx
    rw [mem_closedBall, dist_eq_norm, hnorm x (hrs hx) a ha]
    exact mul_le_mul_of_nonneg_left (by simpa [dist_eq_norm] using hx) hbn.le
  · intro x hx y hy hxy
    have heq := hnorm' x hx y hy
    rw [hxy, sub_self, norm_zero] at heq
    exact sub_eq_zero.mp (norm_eq_zero.mp ((mul_eq_zero.mp heq.symm).resolve_left hbn.ne'))
  · intro y hy
    have hyimg : y ∈ f '' s := hδball (mem_ball.mpr ((mem_closedBall.mp hy).trans_lt hrd))
    obtain ⟨x, hx, hxy⟩ := hyimg
    refine ⟨x, ?_, hxy⟩
    have heq := hnorm x hx a ha
    rw [hxy] at heq
    rw [mem_closedBall, dist_eq_norm]
    apply (mul_le_mul_iff_right₀ hbn).mp
    rw [← heq]
    simpa only [dist_eq_norm] using mem_closedBall.mp hy

end SIC
