/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Dilogarithm.FiniteQuantum
import SICs.Principal.Dilogarithm.ExactSequence
import SICs.Principal.Dilogarithm.FiveTerm

/-!
# The principal finite pentagon relation

The principal finite quantum dilogarithm and its pentagon relation (36).

This module follows [RW26, Radchenko, Wheeler (2026), Theorem 2, `thm:fg.equs`, equation (7),
`eq:Fgpm.5term`; Section 4.2, equation (36), `eq:pentagonproduct3`] on the principal group
`G_d`, with `N = d²(d - 3)` and values `E = F⁺`, `F⁻`. The nonzero-right case of (7) comes from
the crossed-contour residue argument in `SICs.Principal.Dilogarithm.FiveTerm`. The zero-right
case follows by character orthogonality (`MetricGroup.fiveTerm_zero_right`) inside
`FiniteQuantumDilog.ofFiveTerm`.

The reflection law, agreement of `F⁻` with `E` off zero, and `E(0)² = √N E(0) + 1` construct
`principalFiniteQuantumDilog` via `FiniteQuantumDilog.ofFiveTerm`. The general algebra deriving
the product form (36), including its delta term at the origin, lives in
`SICs.Dilogarithm.FiniteQuantum`; here (36) follows from its `product` field.
-/

noncomputable section

namespace SIC

/-- The principal reflection law in metric-group form, used by `principalFiniteQuantumDilog`. -/
private theorem principalDilog_reflection_metric (d : ℕ) (hd : 3 < d)
    [NeZero (principalDilogOrder d)] (x : principalDilogGroup d) :
    principalDilogE d x * principalDilogEMinus d (-x) =
      ((principalDilogMetricGroup d hd).gaussian x)⁻¹ := by
  simpa only [principalDilogMetricGroup, fixedMetricGroup_gaussian,
    AddSubgroup.coe_neg] using
    principalDilogE_mul_principalDilogEMinus_neg d hd x.property

/-- Off zero, the principal minus values equal the plus values, as used by
`principalFiniteQuantumDilog`. -/
private theorem principalDilogEMinus_eq_metric (d : ℕ) (hd : 3 < d)
    [NeZero (principalDilogOrder d)] {x : principalDilogGroup d} (hx : x ≠ 0) :
    principalDilogEMinus d x = principalDilogE d x := by
  exact principalDilogEMinus_of_ne_zero d hd (fun h => hx (Subtype.ext h))

/-- The zero value identity in metric-group form, used by `principalFiniteQuantumDilog`. -/
private theorem principalDilogE_zero_sq_metric (d : ℕ) (hd : 3 < d)
    [NeZero (principalDilogOrder d)] :
    principalDilogE d (0 : principalDilogGroup d) ^ 2 =
      (principalDilogMetricGroup d hd).sqrtCard * principalDilogE d 0 + 1 := by
  simpa only [principalDilogMetricGroup, fixedMetricGroup_sqrtCard,
    AddSubgroup.coe_zero] using principalDilogE_zero_sq d hd

/-! ### The principal finite quantum dilogarithm

The reflection law and nonzero-right five-term relation construct `E = F⁺` on `G_d`. -/

/-- **The principal finite quantum dilogarithm** `E = F⁺` on `G_d`, from the finite five-term
relation (7) at `A_d` with nonzero right class (`principalDilogFiveTerm_of_ne_zero_right`), the
reflection law, and `E(0)² = √N E(0) + 1`. Specializes `FiniteQuantumDilog.ofFiveTerm`. -/
def principalFiniteQuantumDilog (d : ℕ) (hd : 3 < d) [NeZero (principalDilogOrder d)] :
    FiniteQuantumDilog (principalDilogMetricGroup d hd) := by
  let M := principalDilogMetricGroup d hd
  let E : principalDilogGroup d → ℂ := fun x => principalDilogE d x
  let Fm : principalDilogGroup d → ℂ := fun x => principalDilogEMinus d x
  refine FiniteQuantumDilog.ofFiveTerm M E Fm
    (principalDilog_reflection_metric d hd)
    (fun _ hx => principalDilogEMinus_eq_metric d hd hx)
    (principalDilogE_zero_sq_metric d hd) ?_
  · intro u v hv
    have hv' : (v : Fin 2 → ZMod (principalDilogOrder d)) ≠ 0 :=
      fun h => hv (Subtype.ext h)
    simpa only [M, E, Fm, principalDilogMetricGroup, fixedMetricGroup_sqrtCard,
      fixedMetricGroup_bichar, inv_eq_one_div, AddSubgroup.coe_add] using
        principalDilogFiveTerm_of_ne_zero_right d hd u.property v.property hv'

/-- The values of `principalFiniteQuantumDilog` are `principalDilogE`. -/
@[simp]
theorem principalFiniteQuantumDilog_apply (d : ℕ) (hd : 3 < d) [NeZero (principalDilogOrder d)]
    (x : principalDilogGroup d) : principalFiniteQuantumDilog d hd x = principalDilogE d x := by
  rfl

/-! ### The pentagon relation (36)

The `product` field of the principal finite quantum dilogarithm is (36) in residue coordinates. -/

/-- **[RW26, Radchenko, Wheeler (2026), equation (36), `eq:pentagonproduct3`] at `γ = A_d`**, the
pentagon relation in product form: for `u, v ∈ G_d`,
`(1/√N) ∑_{x ∈ G} E(x)⟨x⟩E(v - x)⟨x; u⟩ = ⟨u + v⟩ E(-u - v) E(u) E(v) - N E(0) δ(u) δ(v)`.
The `FiniteQuantumDilog.product` field of `principalFiniteQuantumDilog` gives this equation. -/
@[source "RW26, equation (36), p. 18, eq:pentagonproduct3 (γ = A_d)"]
theorem principalDilogPentagon (d : ℕ) (hd : 3 < d) [NeZero (principalDilogOrder d)]
    {u v : Fin 2 → ZMod (principalDilogOrder d)}
    (hu : u ∈ principalDilogGroup d) (hv : v ∈ principalDilogGroup d) :
    (1 / (Real.sqrt (principalDilogOrder d) : ℂ)) *
        ∑ x : principalDilogGroup d,
          principalDilogE d x * principalDilogGaussian d x * principalDilogE d (v - x) *
            principalDilogBicharacter d x u =
      principalDilogGaussian d (u + v) * principalDilogE d (-u - v) * principalDilogE d u *
          principalDilogE d v -
        (principalDilogOrder d : ℂ) * principalDilogE d 0 *
          ((if u = 0 then 1 else 0) * (if v = 0 then 1 else 0)) := by
  let e := principalFiniteQuantumDilog d hd
  have h := e.product (⟨v, hv⟩) (⟨u, hu⟩)
  simp only [e, principalFiniteQuantumDilog_apply, principalDilogMetricGroup,
    fixedMetricGroup_gaussian, fixedMetricGroup_bichar, fixedMetricGroup_sqrtCard,
    card_principalDilogGroup d hd, inv_eq_one_div, AddSubgroup.coe_add,
    AddSubgroup.coe_neg, AddSubgroup.coe_sub, AddSubgroup.coe_zero,
    AddSubgroup.mk_eq_zero] at h
  have hswap : -v - u = -u - v := by abel
  rw [add_comm v u, hswap] at h
  convert h using 1
  ring

end SIC

end
