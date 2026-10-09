/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Analysis.CharacterSums
import SICs.Dilogarithm.Pseudolattice.Conjugation
import SICs.Dilogarithm.Pseudolattice.Distribution
import SICs.Dilogarithm.Pseudolattice.FiveTerm
import SICs.Dilogarithm.Valuation.CyclicTranslation

/-!
# Valuations of the finite quantum dilogarithm along nested pseudolattices

The function `w_I = log v ∘ E_{I,ε}` on `G_{I,ε}` for a valuation `v : ℂ → ℝ≥0`: it is additive
along nested pseudolattices, `w_J(φ(x)) = ∑_{h ∈ J/I} w_I(x + h)`, so its Fourier coefficients
average as in Lemma 2 of the source; and it is unchanged, or changes sign, under homotheties.

This module follows [RW26b, Radchenko, Wheeler (2026b), Section 5, Lemma 2 and the paragraph
before it]. The source's `w_I = v(E_{I,ε})` for an additive valuation is `log v(E_{I,ε})` here for
a multiplicative one (the sign is immaterial), on the model group `finiteDilogGroup γ`, and the
homothety invariance of the source (totally positive homotheties) is extended to homotheties
with `α > 0 > α'`, where `w` changes sign.

## The argument

*Distribution.* By (11) (`pseudolatticeDilog_distribution`),
`μ_{I,ε}^{|H|}μ_{J,ε}⁻¹ E_{J,ε}(x) = ∏_{t ∈ T} E_{I,ε}(x + t)` for a set `T` of representatives of
`H = J/I`. The eta multipliers are roots of unity (`etaMultiplier_sq_of_trace_pos`,
`etaMultiplierSq_pow_den`), hence units, and taking `log v` gives
`w_J(φ(x)) = ∑_{t ∈ T} w_I(x + t)`; the residues of `T` are the kernel of `φ`.

*Lemma 2.* `|G_{I,ε}| = |G_{J,ε}| = N` (`finiteDilogOrder_eq`, `card_fixedCharacteristics`), so
`sum_charCoeff_compAddMonoidHom` applies.

*Homotheties.* For `J = αI` with `α` totally positive, `E_{J,ε}(αx) = E_{I,ε}(x)`
(`pseudolatticeDilog_smul`, `pseudolatticeDilog_congr_basis`); for `α > 0 > α'`,
`E_{J,ε}(αx) = E_{I,ε}(x)⁻¹` off `I` (`pseudolatticeDilog_smul_of_pos_of_neg_eq_inv`). On `I` both
values are `E(0)`, a unit (`FiniteQuantumDilog.valuation_zero`), so `w(0) = 0`.
-/

noncomputable section

open scoped MatrixGroups NNReal

open Finset

namespace SIC

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
variable {F : RealQuadraticFieldData K} {B : PseudolatticeBasis F} {ε : K}

namespace PseudolatticeBasis.IsPeriod

variable (v : Valuation ℂ ℝ≥0) (h : B.IsPeriod ε)

/-! ### The valuation function `w_I` -/

/-- **The function `w_I(x) = log v(E_{I,ε}(x))`** on `G_{I,ε}` of [RW26b, Radchenko, Wheeler
(2026b), Section 5], for a valuation `v : ℂ → ℝ≥0`, written multiplicatively and through `log`
(the source writes `v` additively). -/
def logValuation (g : finiteDilogGroup h.matrix) : ℝ :=
  Real.log (v (finiteDilogE h.matrix B.beta g))

/-- `w_I` at a residue is `log v(E_{I,ε}(x))`. -/
theorem logValuation_residueHom (x : B.torsionLattice ε) :
    h.logValuation v (h.residueHom x) = Real.log (v (pseudolatticeDilog h x)) := by
  rw [pseudolatticeDilog_eq_finiteDilogE h x.property]
  rfl

/-! ### Distribution and Lemma 2 -/

variable {v h}

/-- The eta multiplier at a positive-trace matrix is a unit at every valuation, as used in
[RW26b, Radchenko, Wheeler (2026b), Section 5, proof of Lemma 2]. Supplies the unit clause of
`logValuation_inclusionHom`. -/
theorem valuation_etaMultiplier (v : Valuation ℂ ℝ≥0) {M : SL(2, ℤ)}
    (htr : 0 < M 0 0 + M 1 1) : v (etaMultiplier M) = 1 := by
  apply valuation_eq_one_of_pow_eq_one v (n := 2 * (etaMultiplierExponent M).den)
    (Nat.mul_ne_zero (by decide) (Rat.den_nz (etaMultiplierExponent M)))
  rw [pow_mul, etaMultiplier_sq_of_trace_pos htr, etaMultiplierSq_pow_den]

/-- Summing over representatives of `J/I` is summing over the kernel of the map
`G_{I,ε} → G_{J,ε}`, as in [RW26b, Radchenko, Wheeler (2026b), Section 5, proof of Lemma 2].
Used by `logValuation_inclusionHom`. -/
private theorem sum_transversal_eq_sum_ker {B' : PseudolatticeBasis F} (h' : B'.IsPeriod ε)
    (hle : B.submodule ≤ B'.submodule) (hJ : ∀ y ∈ B'.submodule, (ε - 1) * y ∈ B.submodule)
    {T : Finset K} (hT : IsQuotientTransversal B.submodule B'.submodule T)
    [NeZero (finiteDilogOrder h.matrix)]
    (g : finiteDilogGroup h.matrix) (f : finiteDilogGroup h.matrix → ℝ) :
    (∑ t : T, f (g + h.residueHom
      ⟨t.1, hJ t.1 (hT.mem t.1 t.2)⟩)) =
      ∑ k ∈ univ.filter (fun k => h.inclusionHom h' hle k = 0), f (g + k) := by
  classical
  refine Finset.sum_bij (fun t _ => h.residueHom
    ⟨t.1, hJ t.1 (hT.mem t.1 t.2)⟩) ?_ ?_ ?_ ?_
  · intro t _
    simp only [mem_filter, mem_univ, true_and]
    rw [h.inclusionHom_residueHom]
    exact (h'.residueHom_eq_zero_iff _).2 (hT.mem t.1 t.2)
  · intro t₁ _ t₂ _ heq
    apply Subtype.ext
    apply hT.eq_of_sub_mem t₁.1 t₁.2 t₂.1 t₂.2
    apply (h.residue_eq_iff (hJ t₁.1 (hT.mem t₁.1 t₁.2))
      (hJ t₂.1 (hT.mem t₂.1 t₂.2))).1
    simpa only [h.coe_residueHom] using congrArg Subtype.val heq
  · intro k hk
    obtain ⟨y, rfl⟩ := h.residueHom_surjective k
    have hyJ : (y : K) ∈ B'.submodule := by
      have hy0 : h'.residueHom (Submodule.inclusion (torsionLattice_mono hle) y) = 0 := by
        simpa only [h.inclusionHom_residueHom] using (mem_filter.mp hk).2
      exact (h'.residueHom_eq_zero_iff _).1 hy0
    obtain ⟨t, ht, hyt⟩ := hT.exists_mem y hyJ
    refine ⟨⟨t, ht⟩, mem_univ _, ?_⟩
    apply Subtype.ext
    change h.residue t = h.residue y
    exact ((h.residue_eq_iff (hJ t (hT.mem t ht)) y.property).2
      (by simpa only [neg_sub] using B.submodule.neg_mem hyt))
  · intro t _
    rfl

/-- **The distribution relation for `w`**, taking valuations in (11) as in the proof of
[RW26b, Radchenko, Wheeler (2026b), Section 5, Lemma 2]: for `I ⊆ J` with `(ε - 1)J ⊆ I`,
`w_J(φ(x)) = ∑_{k ∈ ker φ} w_I(x + k)`. -/
theorem logValuation_inclusionHom {B' : PseudolatticeBasis F} (h' : B'.IsPeriod ε)
    (hle : B.submodule ≤ B'.submodule) (hJ : ∀ y ∈ B'.submodule, (ε - 1) * y ∈ B.submodule)
    [NeZero (finiteDilogOrder h.matrix)] (g : finiteDilogGroup h.matrix) :
    h'.logValuation v (h.inclusionHom h' hle g) =
      ∑ k ∈ univ.filter (fun k => h.inclusionHom h' hle k = 0), h.logValuation v (g + k) := by
  classical
  obtain ⟨x, rfl⟩ := h.residueHom_surjective g
  obtain ⟨T, hT⟩ := exists_isQuotientTransversal hle
  have hxT (t : K) (ht : t ∈ T) : (ε - 1) * ((x : K) + t) ∈ B.submodule := by
    have hx : (ε - 1) * (x : K) ∈ B.submodule := x.property
    simpa only [mul_add] using B.submodule.add_mem hx (hJ t (hT.mem t ht))
  have hv : v (pseudolatticeDilog h' x) =
      ∏ t ∈ T, v (pseudolatticeDilog h ((x : K) + t)) := by
    have hd := congrArg v (pseudolatticeDilog_distribution h hle hJ hT x.property)
    simpa only [map_mul, map_div₀, map_pow, map_prod,
      valuation_etaMultiplier v h.isAttractiveFixedPoint.trace_pos,
      valuation_etaMultiplier v h'.isAttractiveFixedPoint.trace_pos,
      one_pow, div_self, one_div, inv_one, one_mul] using hd
  have hlog : Real.log (v (pseudolatticeDilog h' x)) =
      ∑ t ∈ T, Real.log (v (pseudolatticeDilog h ((x : K) + t))) := by
    rw [hv, NNReal.coe_prod, Real.log_prod]
    intro t ht
    exact_mod_cast (v.pos_iff.mpr (pseudolatticeDilog_ne_zero h (hxT t ht))).ne'
  calc
    h'.logValuation v (h.inclusionHom h' hle (h.residueHom x)) =
        Real.log (v (pseudolatticeDilog h' x)) := by
      rw [h.inclusionHom_residueHom]
      exact h'.logValuation_residueHom v _
    _ = ∑ t ∈ T, Real.log (v (pseudolatticeDilog h ((x : K) + t))) := hlog
    _ = ∑ t : T, h.logValuation v
        (h.residueHom x + h.residueHom ⟨t.1, hJ t.1 (hT.mem t.1 t.2)⟩) := by
      rw [← Finset.sum_attach]
      apply Finset.sum_congr rfl
      intro t _
      rw [← h.logValuation_residueHom v ⟨(x : K) + t.1, hxT t.1 t.2⟩]
      congr 1
      exact (h.residueHom.map_add x ⟨t.1, hJ t.1 (hT.mem t.1 t.2)⟩)
    _ = ∑ k ∈ univ.filter (fun k => h.inclusionHom h' hle k = 0),
        h.logValuation v (h.residueHom x + k) :=
      h.sum_transversal_eq_sum_ker h' hle hJ hT (h.residueHom x) (h.logValuation v)

open scoped Classical in
/-- **[RW26b, Radchenko, Wheeler (2026b), Section 5, Lemma 2]**: for `I ⊆ J` with
`(ε - 1)J ⊆ I` and a character `θ` of `G_{I,ε}` trivial on `ker φ`, the coefficients of `w_J` at
the characters `χ` with `χ ∘ φ = θ` sum to `|ker φ|` times the coefficient of `w_I` at `θ`; there
are `|ker φ|` such `χ` (`card_filter_compAddMonoidHom_eq`). -/
@[source "RW26b, Lemma 2, p. 8"]
theorem sum_charCoeff_logValuation {B' : PseudolatticeBasis F} (h' : B'.IsPeriod ε)
    (hle : B.submodule ≤ B'.submodule) (hJ : ∀ y ∈ B'.submodule, (ε - 1) * y ∈ B.submodule)
    [NeZero (finiteDilogOrder h.matrix)] [NeZero (finiteDilogOrder h'.matrix)]
    {θ : AddChar (finiteDilogGroup h.matrix) ℂ}
    (hθ : ∀ k, h.inclusionHom h' hle k = 0 → θ k = 1) :
    ∑ χ ∈ univ.filter (fun χ : AddChar (finiteDilogGroup h'.matrix) ℂ =>
        χ.compAddMonoidHom (h.inclusionHom h' hle) = θ),
      charCoeff (fun g => (h'.logValuation v g : ℂ)) χ =
        (univ.filter fun k => h.inclusionHom h' hle k = 0).card *
          charCoeff (fun g => (h.logValuation v g : ℂ)) θ := by
  have hcard : Fintype.card (finiteDilogGroup h.matrix) =
      Fintype.card (finiteDilogGroup h'.matrix) := by
    rw [card_fixedCharacteristics h.matrix _
      (det_sub_one_eq_neg_finiteDilogOrder h.isAttractiveFixedPoint),
      card_fixedCharacteristics h'.matrix _
      (det_sub_one_eq_neg_finiteDilogOrder h'.isAttractiveFixedPoint)]
    exact h.finiteDilogOrder_eq h'
  apply sum_charCoeff_compAddMonoidHom hcard (h.inclusionHom h' hle) _ hθ
  intro g
  simpa only [Complex.ofReal_sum] using congrArg (fun r : ℝ => (r : ℂ))
    (h.logValuation_inclusionHom h' hle hJ g)

/-! ### Homotheties -/

/-- **Homothety invariance of `w`** for `α` totally positive: `w_{αI}(αx) = w_I(x)`, from
[RW26b, Radchenko, Wheeler (2026b), equation (1)]. -/
theorem logValuation_smulEquiv_of_pos {B₀ : PseudolatticeBasis F} (h₀ : B₀.IsPeriod ε) {α : K}
    (hα : α ≠ 0) (hα₁ : 0 < realEmbeddingAt K F.place α)
    (hα₂ : 0 < realEmbeddingAt K F.otherPlace α)
    (hI : ∀ y, y ∈ B.submodule ↔ ∃ z ∈ B₀.submodule, y = α * z)
    (g : finiteDilogGroup h₀.matrix) :
    h.logValuation v (h.smulEquiv h₀ hα hI g) = h₀.logValuation v g := by
  obtain ⟨x, rfl⟩ := h₀.residueHom_surjective g
  have hpos : F.IsTotallyPositive α := ⟨hα₁, hα₂⟩
  have heq : (B₀.smul α hpos).submodule = B.submodule := by
    ext y
    exact (B₀.mem_smul_submodule_iff hpos y).trans (hI y).symm
  calc
    h.logValuation v (h.smulEquiv h₀ hα hI (h₀.residueHom x)) =
        Real.log (v (pseudolatticeDilog h (α * (x : K)))) := by
      rw [h.smulEquiv_residueHom]
      exact h.logValuation_residueHom v _
    _ = Real.log (v (pseudolatticeDilog (h₀.smul α hpos) (α * (x : K)))) := by
      rw [pseudolatticeDilog_congr_basis heq (h₀.smul α hpos) h]
    _ = Real.log (v (pseudolatticeDilog h₀ x)) := by
      rw [pseudolatticeDilog_smul h₀ hpos]
    _ = h₀.logValuation v (h₀.residueHom x) :=
      (h₀.logValuation_residueHom v x).symm

/-- The valuation function vanishes at the zero residue, used by
`logValuation_smulEquiv_of_neg`. -/
private theorem logValuation_zero [NeZero (finiteDilogOrder h.matrix)] :
    h.logValuation v 0 = 0 := by
  have hv := h.finiteQuantumDilog.valuation_zero v
  rw [h.finiteQuantumDilog_apply] at hv
  simp only [logValuation, hv, NNReal.coe_one, Real.log_one]

/-- **Sign change of `w` under a mixed-sign homothety**: `w_{αI}(αx) = -w_I(x)` for
`α > 0 > α'`, from [RW26b, Radchenko, Wheeler (2026b), Appendix B, Proposition 8, third case]
and `w_I(0) = 0`. -/
theorem logValuation_smulEquiv_of_neg {B₀ : PseudolatticeBasis F} (h₀ : B₀.IsPeriod ε)
    {α : K} (hα : α ≠ 0) (hα₁ : 0 < realEmbeddingAt K F.place α)
    (hα₂ : realEmbeddingAt K F.otherPlace α < 0)
    (hI : ∀ y, y ∈ B.submodule ↔ ∃ z ∈ B₀.submodule, y = α * z)
    [NeZero (finiteDilogOrder h₀.matrix)] (g : finiteDilogGroup h₀.matrix) :
    h.logValuation v (h.smulEquiv h₀ hα hI g) = -h₀.logValuation v g := by
  have : NeZero (finiteDilogOrder h.matrix) := ⟨by
    rw [← h₀.finiteDilogOrder_eq h]
    exact NeZero.ne _⟩
  obtain ⟨x, rfl⟩ := h₀.residueHom_surjective g
  by_cases hx0 : (x : K) ∈ B₀.submodule
  · have hr : h₀.residueHom x = 0 := (h₀.residueHom_eq_zero_iff x).2 hx0
    simp only [hr, map_zero, h.logValuation_zero (v := v),
      h₀.logValuation_zero (v := v), neg_zero]
  · calc
      h.logValuation v (h.smulEquiv h₀ hα hI (h₀.residueHom x)) =
          Real.log (v (pseudolatticeDilog h (α * (x : K)))) := by
        rw [h.smulEquiv_residueHom]
        exact h.logValuation_residueHom v _
      _ = Real.log (v ((pseudolatticeDilog h₀ x)⁻¹)) := by
        rw [pseudolatticeDilog_smul_of_pos_of_neg_eq_inv h₀ hα₁ hα₂ hI h
          x.property hx0]
      _ = -Real.log (v (pseudolatticeDilog h₀ x)) := by
        rw [map_inv₀, NNReal.coe_inv, Real.log_inv]
      _ = -h₀.logValuation v (h₀.residueHom x) := by
        rw [h₀.logValuation_residueHom]

end PseudolatticeBasis.IsPeriod

end SIC

end
