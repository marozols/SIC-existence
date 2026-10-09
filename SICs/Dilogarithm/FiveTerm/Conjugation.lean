/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Dilogarithm.FiveTerm.Relation

/-!
# The finite five-term relation under conjugation

The finite five-term relation (7) as a property of a hyperbolic matrix at a fixed point, its
invariance under conjugation, and its truth at every attractive fixed point of a letter word.

This module transports [RW26, Radchenko, Wheeler (2026), Theorem 2, `thm:fg.equs`, equation (7),
`eq:Fgpm.5term`] along `γ ↦ RγR⁻¹`, `τ ↦ R·τ` with `j_R(τ) > 0`.
Every pseudolattice period is conjugate to a letter word
(`PseudolatticeBasis.IsPeriod.exists_letterWord_conj`), where (7) is
`finiteDilogFiveTerm_letterWord`.

## The argument

Conjugation preserves the trace, so `G_γ` and `G_{RγR⁻¹}` have the same order `N`, and
`x ↦ Rx` (with the identification `ZMod N ≃ ZMod N'` of equal moduli) maps `G_γ` onto
`G_{RγR⁻¹}`: `γx ≡ x` gives `(RγR⁻¹)(Rx) ≡ Rx`. The finite values are invariant,
`F_{RγR⁻¹}(Rr)(R·τ) = F_γ(r)(τ)` (`finiteDilogValue_mul_mul_inv`, Kopp's Theorem 4.37), and so is
`F⁻`; the Gaussian is a class function (`thetaCharacter` of `Rr` at `RγR⁻¹` is that of `r` at
`γ`), hence so is the bicharacter. Reindexing the sum over `G` by this bijection carries (7) at
`(RγR⁻¹, R·τ)` to (7) at `(γ, τ)`.
-/

noncomputable section

open Complex
open scoped MatrixGroups

namespace SIC

/-- **The finite five-term relation (7) at `(γ, τ)`** [RW26, Radchenko, Wheeler (2026),
Theorem 2, `thm:fg.equs`, equation (7), `eq:Fgpm.5term`]: for `u, v ∈ G` not both zero,
`(1/√N) ∑_{x ∈ G} ⟨x; u⟩ F⁺(x)/F⁻(x + v) = F⁺(u + v)/(F⁻(u) F⁻(v))`. -/
def FiniteDilogFiveTerm (A : SL(2, ℤ)) (τ : ℝ) [NeZero (finiteDilogOrder A)] : Prop :=
  ∀ u ∈ finiteDilogGroup A, ∀ v ∈ finiteDilogGroup A, (u, v) ≠ (0, 0) →
    (1 / (Real.sqrt (finiteDilogOrder A) : ℂ)) *
        ∑ x : finiteDilogGroup A,
          fixedBicharacter A (finiteDilogOrder A) x u *
            (finiteDilogE A τ x / finiteDilogEMinus A τ (x + v)) =
      finiteDilogE A τ (u + v) / (finiteDilogEMinus A τ u * finiteDilogEMinus A τ v)

/-! ### Metric-group forms of the value identities

The identities for `F⁺` and `F⁻` on `G` become the inputs to `FiniteQuantumDilog.ofFiveTerm`. -/

/-- The reflection law in metric-group form, used by `finiteDilogFiniteQuantum`. -/
private theorem finiteDilog_reflection_metric {A : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint A τ) [NeZero (finiteDilogOrder A)]
    (x : finiteDilogGroup A) :
    finiteDilogE A τ x * finiteDilogEMinus A τ (-x) =
      ((fixedMetricGroup A (finiteDilogOrder A)
        (det_sub_one_eq_neg_finiteDilogOrder h)).gaussian x)⁻¹ := by
  simpa only [fixedMetricGroup_gaussian, AddSubgroup.coe_neg] using
    finiteDilogE_mul_EMinus_neg h x.property

/-- Off zero, the minus and plus values agree in metric-group form, used by
`finiteDilogFiniteQuantum`. -/
private theorem finiteDilog_EMinus_metric {A : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint A τ) [NeZero (finiteDilogOrder A)]
    {x : finiteDilogGroup A} (hx : x ≠ 0) :
    finiteDilogEMinus A τ x = finiteDilogE A τ x := by
  exact finiteDilogEMinus_of_ne_zero h (fun hz => hx (Subtype.ext hz))

/-- The zero-value identity in metric-group form, used by `finiteDilogFiniteQuantum`. -/
private theorem finiteDilog_zero_sq_metric {A : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint A τ) [NeZero (finiteDilogOrder A)] :
    finiteDilogE A τ (0 : finiteDilogGroup A) ^ 2 =
      (fixedMetricGroup A (finiteDilogOrder A)
        (det_sub_one_eq_neg_finiteDilogOrder h)).sqrtCard *
          finiteDilogE A τ 0 + 1 := by
  simpa only [fixedMetricGroup_sqrtCard, AddSubgroup.coe_zero] using
    finiteDilogE_zero_sq h

/-- **The finite quantum dilogarithm of `(γ, τ)`** given (7): `E = F⁺` on `G`, from the finite
five-term relation, the reflection law `F⁺(x)F⁻(-x) = ⟨x⟩⁻¹` (`finiteDilogE_mul_EMinus_neg`),
`F⁻ = F⁺` off zero (`finiteDilogEMinus_of_ne_zero`), and `E(0)² = √N E(0) + 1`
(`finiteDilogE_zero_sq`), built by `FiniteQuantumDilog.ofFiveTerm` as in [RW26, Radchenko,
Wheeler (2026), Theorem 5, `thm:fqdilogbasicproperties`]. -/
def finiteDilogFiniteQuantum {A : SL(2, ℤ)} {τ : ℝ} (h : IsAttractiveFixedPoint A τ)
    [NeZero (finiteDilogOrder A)] (hfive : FiniteDilogFiveTerm A τ) :
    FiniteQuantumDilog (fixedMetricGroup A (finiteDilogOrder A)
      (det_sub_one_eq_neg_finiteDilogOrder h)) :=
  FiniteQuantumDilog.ofFiveTerm _ (fun x => finiteDilogE A τ x)
    (fun x => finiteDilogEMinus A τ x)
    (by
      intro x
      exact finiteDilog_reflection_metric h x)
    (by
      intro x hx
      exact finiteDilog_EMinus_metric h hx)
    (by
      exact finiteDilog_zero_sq_metric h)
    (by
      intro u v hv
      have huv : ((u : Fin 2 → ZMod (finiteDilogOrder A)),
          (v : Fin 2 → ZMod (finiteDilogOrder A))) ≠ (0, 0) := by
        intro heq
        exact hv (Subtype.ext (congrArg Prod.snd heq))
      simpa only [fixedMetricGroup_sqrtCard, fixedMetricGroup_bichar,
        inv_eq_one_div, AddSubgroup.coe_add] using
          hfive u u.property v v.property huv)

/-- The finite five-term relation holds at every attractive fixed point of a letter word
(`finiteDilogFiveTerm_letterWord`). -/
theorem IsLetterWordFixedPoint.finiteDilogFiveTerm {bs : List ℤ} {τ : ℝ}
    (h : IsLetterWordFixedPoint bs τ) [NeZero (finiteDilogOrder (letterWord bs))] :
    FiniteDilogFiveTerm (letterWord bs) τ := by
  intro u hu v hv huv
  exact finiteDilogFiveTerm_letterWord h hu hv huv

/-! ### Transport of the finite five-term relation

The group equivalence reindexes the finite sum, and its value and bicharacter laws identify
each summand. -/

/-- Reindex the left side of (7) along the conjugation equivalence, used by
`FiniteDilogFiveTerm.of_conj`. -/
private theorem finiteDilogFiveTerm_sum_conj {A : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint A τ) [NeZero (finiteDilogOrder A)]
    (R : SL(2, ℤ)) (hR : 0 < fltDenominator (R : Mat(2, ℤ)) τ)
    [NeZero (finiteDilogOrder (R * A * R⁻¹))] (u v : finiteDilogGroup A) :
    (∑ x : finiteDilogGroup A,
      fixedBicharacter A (finiteDilogOrder A) x u *
        (finiteDilogE A τ x / finiteDilogEMinus A τ (x + v))) =
    ∑ y : finiteDilogGroup (R * A * R⁻¹),
      fixedBicharacter (R * A * R⁻¹) (finiteDilogOrder (R * A * R⁻¹)) y
        (finiteDilogGroup_conjAddEquiv A R u) *
        (finiteDilogE (R * A * R⁻¹) (flt (R : Mat(2, ℤ)) τ) y /
          finiteDilogEMinus (R * A * R⁻¹) (flt (R : Mat(2, ℤ)) τ)
            (y + finiteDilogGroup_conjAddEquiv A R v)) := by
  let e := finiteDilogGroup_conjAddEquiv A R
  apply Fintype.sum_equiv e
  intro x
  have hm := finiteDilogEMinus_conj h R hR (x + v)
  have he := finiteDilogE_conj h R hR x
  have hb := finiteDilogGroup_conj_bichar A R x u
  convert congrArg₂ (fun a b : ℂ => a * b) hb.symm
    (congrArg₂ (fun a b : ℂ => a / b) he.symm hm.symm) using 1;
    simp only [e, map_add, AddSubgroup.coe_add]; rfl

/-- **Conjugation invariance of (7).** If (7) holds for `RγR⁻¹` at `R·τ`, `j_R(τ) > 0`, then it
holds for `γ` at its attractive fixed point `τ`. -/
theorem FiniteDilogFiveTerm.of_conj {A : SL(2, ℤ)} {τ : ℝ} (h : IsAttractiveFixedPoint A τ)
    [NeZero (finiteDilogOrder A)] (R : SL(2, ℤ)) (hR : 0 < fltDenominator (R : Mat(2, ℤ)) τ)
    [NeZero (finiteDilogOrder (R * A * R⁻¹))]
    (hfive : FiniteDilogFiveTerm (R * A * R⁻¹) (flt (R : Mat(2, ℤ)) τ)) :
    FiniteDilogFiveTerm A τ := by
  intro u hu v hv huv
  let e := finiteDilogGroup_conjAddEquiv A R
  let U : finiteDilogGroup A := ⟨u, hu⟩
  let V : finiteDilogGroup A := ⟨v, hv⟩
  have hpair : (((e U : finiteDilogGroup (R * A * R⁻¹)) :
        Fin 2 → ZMod (finiteDilogOrder (R * A * R⁻¹))),
      ((e V : finiteDilogGroup (R * A * R⁻¹)) :
        Fin 2 → ZMod (finiteDilogOrder (R * A * R⁻¹)))) ≠ (0, 0) := by
    intro hz
    have hU0 : e U = 0 := Subtype.ext (congrArg Prod.fst hz)
    have hV0 : e V = 0 := Subtype.ext (congrArg Prod.snd hz)
    have hu0 : U = 0 := e.injective (by simpa using hU0)
    have hv0 : V = 0 := e.injective (by simpa using hV0)
    exact huv (by simpa only [U, V, hu0, hv0] using
      (show (((U : Fin 2 → ZMod (finiteDilogOrder A))),
        ((V : Fin 2 → ZMod (finiteDilogOrder A)))) = (0, 0) by simp [hu0, hv0]))
  have hsum := finiteDilogFiveTerm_sum_conj h R hR U V
  have hright := hfive (e U) (e U).property (e V) (e V).property hpair
  have hsqrt : (1 / (Real.sqrt (finiteDilogOrder (R * A * R⁻¹)) : ℂ)) =
      (1 / (Real.sqrt (finiteDilogOrder A) : ℂ)) := by
    rw [finiteDilogOrder_conj]
  rw [hsqrt, ← hsum] at hright
  have hnum := finiteDilogE_conj h R hR (U + V)
  have hdenU := finiteDilogEMinus_conj h R hR U
  have hdenV := finiteDilogEMinus_conj h R hR V
  simp only [← AddSubgroup.coe_add, ← map_add] at hright
  rw [hnum, hdenU, hdenV] at hright
  simpa only [U, V, AddSubgroup.coe_add] using hright

end SIC

end
