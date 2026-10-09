/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Dilogarithm.FiveTerm.Conjugation
import SICs.Dilogarithm.Pseudolattice.GroupMaps

/-!
# The finite five-term relation of a pseudolattice

The finite five-term relation (7) for the matrix of every period of a pseudolattice at its fixed
point and at every attractive fixed point in a real quadratic field, and the finite quantum
dilogarithm it defines on `G_{I,ε}`.

This module proves [RW26, Radchenko, Wheeler (2026), Theorem 2, `thm:fg.equs`, equation (7),
`eq:Fgpm.5term`] in the setting of [RW26b, Radchenko, Wheeler (2026b), Section 3], where the
finite quantum dilogarithm of a pseudolattice is the finite dilogarithm of its period matrix
`γ` at `β = ρ₁(τ)` (`pseudolatticeDilog_eq_finiteDilogE`).

## The argument

The period matrix is conjugate, by `R` with `j_R(β) > 0`, to a letter word whose letters are at
least `2`, at the attractive fixed point `R·β` (`IsPeriod.exists_letterWord_conj`). Relation (7)
holds there (`IsLetterWordFixedPoint.finiteDilogFiveTerm`) and is invariant under conjugation
(`FiniteDilogFiveTerm.of_conj`). The finite quantum dilogarithm is then
`finiteDilogFiniteQuantum` at the period matrix. An attractive fixed point `β = ρ₁(τ)` of `γ` with
`τ ∈ K` is the fixed point of the pseudolattice `ℤτ + ℤ` with period `cτ + d`, whose matrix is
`γ` (`PseudolatticeBasis.ofAttractiveFixedPoint`), so (7) holds there as well.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
variable {F : RealQuadraticFieldData K} {B : PseudolatticeBasis F} {ε : K}

namespace PseudolatticeBasis.IsPeriod

/-- **[RW26, Radchenko, Wheeler (2026), Theorem 2, `thm:fg.equs`, equation (7),
`eq:Fgpm.5term`] for a pseudolattice period**: the finite five-term relation holds for the period
matrix `γ` at the fixed point `β`. -/
@[source "RW26, equation (7), p. 3, eq:Fgpm.5term (pseudolattice periods)"]
theorem finiteDilogFiveTerm (h : B.IsPeriod ε) [NeZero (finiteDilogOrder h.matrix)] :
    FiniteDilogFiveTerm h.matrix B.beta := by
  obtain ⟨R, bs, hne, htwo, hjR, hconj, hfixed⟩ := h.exists_letterWord_conj
  let hword : IsLetterWordFixedPoint bs (flt (R : Mat(2, ℤ)) B.beta) :=
    ⟨hne, (fun b hb => htwo b (List.mem_of_mem_tail hb)), hfixed⟩
  let _ : NeZero (finiteDilogOrder (R * h.matrix * R⁻¹)) :=
    finiteDilogOrder_neZero (hconj ▸ hfixed)
  have hfive : FiniteDilogFiveTerm (R * h.matrix * R⁻¹)
      (flt (R : Mat(2, ℤ)) B.beta) := by
    simp only [hconj]
    let _ : NeZero (finiteDilogOrder (letterWord bs)) := finiteDilogOrder_neZero hfixed
    exact hword.finiteDilogFiveTerm
  exact FiniteDilogFiveTerm.of_conj h.isAttractiveFixedPoint R hjR hfive

/-- **The finite quantum dilogarithm of a pseudolattice period** [RW26, Radchenko, Wheeler
(2026), Theorem 5, `thm:fqdilogbasicproperties`]: `finiteDilogFiniteQuantum` at the period
matrix, from `finiteDilogFiveTerm`. -/
def finiteQuantumDilog (h : B.IsPeriod ε) [NeZero (finiteDilogOrder h.matrix)] :
    FiniteQuantumDilog (fixedMetricGroup h.matrix (finiteDilogOrder h.matrix)
      (det_sub_one_eq_neg_finiteDilogOrder h.isAttractiveFixedPoint)) :=
  finiteDilogFiniteQuantum h.isAttractiveFixedPoint h.finiteDilogFiveTerm

/-- The values of `finiteQuantumDilog` are `finiteDilogE`. -/
theorem finiteQuantumDilog_apply (h : B.IsPeriod ε) [NeZero (finiteDilogOrder h.matrix)]
    (x : finiteDilogGroup h.matrix) :
    h.finiteQuantumDilog x = finiteDilogE h.matrix B.beta x :=
  rfl

/-- The finite quantum dilogarithm at the residue of `x` is `E_{I,ε}(x)`
(`pseudolatticeDilog_eq_finiteDilogE`). -/
theorem finiteQuantumDilog_residueHom (h : B.IsPeriod ε)
    [NeZero (finiteDilogOrder h.matrix)] (x : B.torsionLattice ε) :
    h.finiteQuantumDilog (h.residueHom x) = pseudolatticeDilog h x := by
  rw [h.finiteQuantumDilog_apply]
  exact (pseudolatticeDilog_eq_finiteDilogE h x.2).symm

end PseudolatticeBasis.IsPeriod

/-! ### Attractive fixed points in a real quadratic field

Every attractive fixed point in a real quadratic field is the fixed point of a pseudolattice
period with the same matrix. -/

/-- **[RW26, Radchenko, Wheeler (2026), Theorem 2, `thm:fg.equs`, equation (7),
`eq:Fgpm.5term`] at an attractive fixed point in a real quadratic field**: for `γ ∈ SL₂(ℤ)` with
attractive fixed point `β = ρ₁(τ)`, `τ ∈ K`, the finite five-term relation holds at `(γ, β)`.
It is `IsPeriod.finiteDilogFiveTerm` at the pseudolattice `ℤτ + ℤ` with period `cτ + d`
(`PseudolatticeBasis.ofAttractiveFixedPoint`), whose matrix is `γ`. -/
theorem finiteDilogFiveTerm_of_isAttractiveFixedPoint {A : SL(2, ℤ)} {τ : K}
    (hA : IsAttractiveFixedPoint A (realEmbeddingAt K F.place τ))
    [NeZero (finiteDilogOrder A)] :
    FiniteDilogFiveTerm A (realEmbeddingAt K F.place τ) := by
  let h := PseudolatticeBasis.isPeriod_ofAttractiveFixedPoint hA
  have hm : h.matrix = A :=
    PseudolatticeBasis.matrix_isPeriod_ofAttractiveFixedPoint hA
  have hn : NeZero (finiteDilogOrder h.matrix) := finiteDilogOrder_neZero h.isAttractiveFixedPoint
  have hfive : FiniteDilogFiveTerm h.matrix (realEmbeddingAt K F.place τ) :=
    @PseudolatticeBasis.IsPeriod.finiteDilogFiveTerm K _ _ _ F _ _ h hn
  simpa only [hm] using hfive

end SIC

end
