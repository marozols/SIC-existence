/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Compact uniform convergence in a parameter

Joint continuity at a compact parameter slice gives uniform convergence, a common bound,
and convergence of finite interval integrals.

These elementary compactness and dominated-convergence results supply the finite-contour
part of the real-period limit in [RW26, Radchenko, Wheeler (2026), Appendix A.2,
`app:mod.fad`]. They require continuity only at the limiting parameter and eventual
measurability of the nearby integrands. Compactness supplies one parameter neighborhood
for every point of the integration interval; a constant bound on that finite interval
then permits dominated convergence. Infinite tails require a separate integrable bound.
-/

noncomputable section

open Filter Topology MeasureTheory Set

namespace SIC

/-- Joint continuity at every point of `K × {y₀}` gives convergence uniform on compact `K`
as the second parameter tends to `y₀`. -/
theorem tendstoUniformlyOn_of_continuousAt_prod
    {α β E : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] [PseudoMetricSpace E]
    {f : α × β → E} {K : Set α} (hK : IsCompact K) (y₀ : β)
    (hf : ∀ x ∈ K, ContinuousAt f (x, y₀)) :
    TendstoUniformlyOn (fun y x => f (x, y)) (fun x => f (x, y₀)) (𝓝 y₀) K := by
  have hs : IsCompact (K ×ˢ ({y₀} : Set β)) := hK.prod isCompact_singleton
  have hc : ∀ p ∈ K ×ˢ ({y₀} : Set β), ContinuousAt f p := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    have hy' : y = y₀ := Set.mem_singleton_iff.mp hy
    subst y
    exact hf x hx
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hr : {p : E × E | dist p.1 p.2 < ε} ∈ uniformity E :=
    Metric.mem_uniformity_dist.mpr ⟨ε, hε, fun _ _ h => h⟩
  obtain ⟨δ, hδ, hmod⟩ :=
    Metric.mem_uniformity_dist.mp (hs.uniformContinuousAt_of_continuousAt f hc hr)
  filter_upwards [Metric.ball_mem_nhds y₀ hδ] with y hy
  intro x hx
  exact hmod (by simpa [dist_prod_same_left, dist_comm] using Metric.mem_ball.mp hy)
    ⟨hx, Set.mem_singleton y₀⟩

/-- Joint continuity at a compact parameter slice gives one eventual bound for all
nearby values on that compact set. -/
theorem exists_eventually_norm_le_of_continuousAt_prod
    {α β E : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] [NormedAddCommGroup E]
    {f : α × β → E} {K : Set α} (hK : IsCompact K) (y₀ : β)
    (hf : ∀ x ∈ K, ContinuousAt f (x, y₀)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ y in 𝓝 y₀, ∀ x ∈ K, ‖f (x, y)‖ ≤ C := by
  have hcont : ContinuousOn (fun x => f (x, y₀)) K := by
    intro x hx
    have hp : ContinuousAt (fun z : α => (z, y₀)) x :=
      continuousAt_id.prodMk continuousAt_const
    exact ((hf x hx).comp_of_eq hp rfl).continuousWithinAt
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont
  have hnear := (Metric.tendstoUniformlyOn_iff.mp
    (tendstoUniformlyOn_of_continuousAt_prod hK y₀ hf)) 1 zero_lt_one
  refine ⟨max M 0 + 1, by positivity, ?_⟩
  filter_upwards [hnear] with y hy x hx
  calc
    ‖f (x, y)‖ ≤ ‖f (x, y₀)‖ + ‖f (x, y₀) - f (x, y)‖ :=
      norm_le_norm_add_norm_sub _ _
    _ = ‖f (x, y₀)‖ + dist (f (x, y₀)) (f (x, y)) := by rw [dist_eq_norm]
    _ ≤ max M 0 + 1 :=
      add_le_add ((hM x hx).trans (le_max_left _ _)) (le_of_lt (hy x hx))

/-- A parameter limit passes through a finite interval integral when the family is jointly
continuous on the limiting interval slice and eventually measurable along the parameter filter. -/
theorem tendsto_intervalIntegral_of_continuousAt_prod
    {α E : Type*} [PseudoMetricSpace α] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {l : Filter α} [l.IsCountablyGenerated]
    {f : ℝ × α → E} {y₀ : α} (hl : l ≤ 𝓝 y₀) (a b : ℝ)
    (hf : ∀ x ∈ Set.uIcc a b, ContinuousAt f (x, y₀))
    (hmeas : ∀ᶠ y in l,
      AEStronglyMeasurable (fun x : ℝ => f (x, y))
        (volume.restrict (Set.uIoc a b))) :
    Tendsto (fun y => ∫ x in a..b, f (x, y)) l
      (𝓝 (∫ x in a..b, f (x, y₀))) := by
  obtain ⟨C, _, hC⟩ :=
    exists_eventually_norm_le_of_continuousAt_prod isCompact_uIcc y₀ hf
  have hu := tendstoUniformlyOn_of_continuousAt_prod isCompact_uIcc y₀ hf
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (bound := fun _ => C)
  · exact hmeas
  · filter_upwards [hC.filter_mono hl] with y hy
    exact .of_forall fun x hx => hy x (uIoc_subset_uIcc hx)
  · exact intervalIntegrable_const
  · exact .of_forall fun x hx => (hu.tendsto_at (uIoc_subset_uIcc hx)).mono_left hl

end SIC
