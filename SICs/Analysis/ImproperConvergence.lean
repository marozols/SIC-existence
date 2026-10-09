/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import SICs.Analysis.CompactConvergence

/-!
# Improper integrals with uniform exponential tails

Joint continuity at a limiting parameter and uniform exponential tail bounds give convergence of
integrals over the whole real line.

This module supplies the dominated-convergence step used for the boundary passage in
[RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`]. On a compact middle interval,
joint continuity gives a uniform bound for all nearby parameters. On the two complementary
half-lines, the assumed estimates are bounded by integrable real exponentials. Combining these
three pieces gives one eventual integrable majorant, to which the filter form of the dominated
convergence theorem applies.

The parameter filter need not be nontrivial: along the bottom filter the convergence conclusion
is automatic.
-/

noncomputable section

open Filter Topology MeasureTheory Set

namespace SIC

/-! ### Uniform bounds near a real boundary point -/

/-- Converts a uniform bound near a real period into the eventual bound used by tail estimates. -/
lemma eventually_tail_bound_of_uniform {τ₀ : ℝ} {ε : ℝ}
    (hε : 0 < ε) (f : ℂ → ℝ → ℂ) (P : ℝ → Prop) (M : ℝ → ℝ)
    (hbound : ∀ τ, ‖τ - (τ₀ : ℂ)‖ ≤ ε → ∀ t, P t → ‖f τ t‖ ≤ M t) :
    ∀ᶠ τ in 𝓝[{q : ℂ | 0 < q.im}] (τ₀ : ℂ), ∀ t, P t → ‖f τ t‖ ≤ M t := by
  have hball : ∀ᶠ τ in 𝓝[{q : ℂ | 0 < q.im}] (τ₀ : ℂ),
      τ ∈ Metric.closedBall (τ₀ : ℂ) ε :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Metric.closedBall_mem_nhds (τ₀ : ℂ) hε)
  filter_upwards [hball] with τ hτ
  exact hbound τ (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hτ)

/-! ### A common integrable majorant

The tail thresholds are enlarged to nonnegative numbers. This leaves the assumed estimates valid
and places the remaining middle interval between the two tails.
-/

/-- A piecewise exponential function used as a common majorant on the real line. -/
private def twoSidedExponentialMajorant
    (A Cneg κneg Rneg Cpos κpos Rpos : ℝ) (t : ℝ) : ℝ :=
  if t ≤ -Rneg then max Cneg 0 * Real.exp (κneg * t)
  else if Rpos < t then max Cpos 0 * Real.exp (-κpos * t)
  else A

/-- The piecewise two-sided exponential majorant is integrable when both rates are positive
and both cutoffs are nonnegative. -/
private lemma integrable_twoSidedExponentialMajorant
    (A Cneg κneg Rneg Cpos κpos Rpos : ℝ) (hκneg : 0 < κneg) (hRneg : 0 ≤ Rneg)
    (hκpos : 0 < κpos) (hRpos : 0 ≤ Rpos) :
    Integrable (twoSidedExponentialMajorant A Cneg κneg Rneg Cpos κpos Rpos) := by
  have hleft : IntegrableOn
      (twoSidedExponentialMajorant A Cneg κneg Rneg Cpos κpos Rpos) (Iic (-Rneg)) :=
    ((integrableOn_exp_mul_Iic hκneg (-Rneg)).const_mul (max Cneg 0)).congr
      (ae_restrict_of_forall_mem measurableSet_Iic fun t ht => by
        simp [twoSidedExponentialMajorant, show t ≤ -Rneg from ht])
  have hmid : IntegrableOn
      (twoSidedExponentialMajorant A Cneg κneg Rneg Cpos κpos Rpos) (Ioc (-Rneg) Rpos) :=
    (integrableOn_const (measure_Ioc_lt_top.ne)).congr
      (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => by
        simp [twoSidedExponentialMajorant, not_le.mpr ht.1, not_lt.mpr ht.2])
  have hright : IntegrableOn
      (twoSidedExponentialMajorant A Cneg κneg Rneg Cpos κpos Rpos) (Ioi Rpos) :=
    ((integrableOn_exp_mul_Ioi (by linarith : -κpos < 0) Rpos).const_mul (max Cpos 0)).congr
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
        have ht' : Rpos < t := ht
        have hnot : ¬t ≤ -Rneg := not_le.mpr (by linarith)
        simp [twoSidedExponentialMajorant, hnot, ht'])
  have hcover : Iic (-Rneg) ∪ Ioc (-Rneg) Rpos ∪ Ioi Rpos = univ := by
    rw [Iic_union_Ioc_eq_Iic (by linarith), Iic_union_Ioi]
  simpa [hcover] using (hleft.union hmid).union hright

/-- Joint continuity on the limiting parameter slice and uniform exponential estimates on both
tails give one integrable function that eventually dominates the whole family. The estimates are
`‖f(t,y)‖ ≤ C₊ exp(-κ₊t)` on the right and `‖f(t,y)‖ ≤ C₋ exp(κ₋t)` on the left, with
`κ₊, κ₋ > 0`. -/
theorem exists_integrable_bound_of_exp_tails
    {α E : Type*} [PseudoMetricSpace α] [NormedAddCommGroup E] {l : Filter α}
    {f : ℝ × α → E} {y₀ : α} (hl : l ≤ 𝓝 y₀)
    (hf : ∀ t : ℝ, ContinuousAt f (t, y₀))
    (hpos : ∃ C κ T : ℝ, 0 < κ ∧ ∀ᶠ y in l, ∀ t : ℝ, T ≤ t →
      ‖f (t, y)‖ ≤ C * Real.exp (-κ * t))
    (hneg : ∃ C κ T : ℝ, 0 < κ ∧ ∀ᶠ y in l, ∀ t : ℝ, t ≤ -T →
      ‖f (t, y)‖ ≤ C * Real.exp (κ * t)) :
    ∃ g : ℝ → ℝ, Integrable g ∧ ∀ᶠ y in l, ∀ t : ℝ, ‖f (t, y)‖ ≤ g t := by
  obtain ⟨Cpos, κpos, Tpos, hκpos, hpos⟩ := hpos
  obtain ⟨Cneg, κneg, Tneg, hκneg, hneg⟩ := hneg
  let Rpos := max 0 Tpos
  let Rneg := max 0 Tneg
  obtain ⟨A, _, hA⟩ := exists_eventually_norm_le_of_continuousAt_prod
    (isCompact_Icc : IsCompact (Icc (-Rneg) Rpos)) y₀ (fun t _ => hf t)
  let g := twoSidedExponentialMajorant A Cneg κneg Rneg Cpos κpos Rpos
  refine ⟨g, integrable_twoSidedExponentialMajorant A Cneg κneg Rneg Cpos κpos Rpos
    hκneg (by simp [Rneg]) hκpos (by simp [Rpos]), ?_⟩
  filter_upwards [hA.filter_mono hl, hpos, hneg] with y hAy hposy hnegy t
  by_cases hleft : t ≤ -Rneg
  · change ‖f (t, y)‖ ≤ twoSidedExponentialMajorant A Cneg κneg Rneg Cpos κpos Rpos t
    rw [twoSidedExponentialMajorant, ite_eq_left hleft]
    refine (hnegy t (hleft.trans ?_)).trans
      (mul_le_mul_of_nonneg_right (le_max_left Cneg 0) (Real.exp_nonneg (κneg * t)))
    exact neg_le_neg (le_max_right 0 Tneg)
  by_cases hright : Rpos < t
  · change ‖f (t, y)‖ ≤ twoSidedExponentialMajorant A Cneg κneg Rneg Cpos κpos Rpos t
    rw [twoSidedExponentialMajorant, ite_eq_right hleft, ite_eq_left hright]
    have hp := hposy t ((le_max_right 0 Tpos).trans hright.le)
    exact hp.trans (mul_le_mul_of_nonneg_right (le_max_left Cpos 0)
      (Real.exp_nonneg (-κpos * t)))
  · change ‖f (t, y)‖ ≤ twoSidedExponentialMajorant A Cneg κneg Rneg Cpos κpos Rpos t
    rw [twoSidedExponentialMajorant, ite_eq_right hleft, ite_eq_right hright]
    exact hAy t ⟨le_of_not_ge hleft, le_of_not_gt hright⟩

/-! ### Convergence of the integrals

Dominated convergence with the common majorant passes the parameter limit through the integral.
-/

/-- Joint continuity at the limiting parameter and uniform exponential bounds on both tails
allow the parameter limit to pass through the integral over the whole real line. -/
theorem tendsto_integral_of_exp_tails
    {α E : Type*} [PseudoMetricSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {l : Filter α} [l.IsCountablyGenerated] {f : ℝ × α → E} {y₀ : α}
    (hl : l ≤ 𝓝 y₀) (hf : ∀ t : ℝ, ContinuousAt f (t, y₀))
    (hmeas : ∀ᶠ y in l, AEStronglyMeasurable (fun t : ℝ => f (t, y)))
    (hpos : ∃ C κ T : ℝ, 0 < κ ∧ ∀ᶠ y in l, ∀ t : ℝ, T ≤ t →
      ‖f (t, y)‖ ≤ C * Real.exp (-κ * t))
    (hneg : ∃ C κ T : ℝ, 0 < κ ∧ ∀ᶠ y in l, ∀ t : ℝ, t ≤ -T →
      ‖f (t, y)‖ ≤ C * Real.exp (κ * t)) :
    Tendsto (fun y => ∫ t : ℝ, f (t, y)) l (𝓝 (∫ t : ℝ, f (t, y₀))) := by
  obtain ⟨g, hg, hbound⟩ :=
    exists_integrable_bound_of_exp_tails
      hl hf hpos hneg
  apply tendsto_integral_filter_of_dominated_convergence g hmeas
    (hbound.mono fun _ hy => .of_forall hy) hg
  exact .of_forall fun t =>
    ((hf t).comp_of_eq (continuousAt_const.prodMk continuousAt_id) rfl).mono_left hl

end SIC
