/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Quadratic.Forms
import SICs.SL2Z.FractionalLinear
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-!
# Matrix actions and stability groups of binary quadratic forms

The determinant-twisted `GL₂(ℤ)` action, its centralizer description, and stability subgroups.

This file follows the action of [AFK25, equation (1.31), `eq:afrmtrans`] and the stability
groups of [AFK25, Definition 1.20, `dfn:stbgpqdf`]. For every integral coefficient triple, the
matrix relation `M·2S(Q_M) = 2SQ·M` at an invertible integral matrix identifies the stabilizer
with the centralizer of `2SQ`, as in [AFK25, Theorem 4.37(1), `tm:sqchar`].

## Mathematical argument

Substitution of the variables gives the determinant-twisted right action on forms. Viewing it
as a left action of the opposite group supplies a bundled stabilizer in `GL₂(ℤ)`. The map
`Q ↦ 2SQ` is injective, so its covariance equation turns stabilization into commutation.
Intersecting with determinant-one matrices and with a principal congruence subgroup gives
`S(Q) ∩ SL₂(ℤ)` and `S_d(Q)`.
The integral coordinates of these groups are developed in `SICs.Quadratic.FormStabilizers`.

## References

- [AFK25, equation (1.31), `eq:afrmtrans`]
- [AFK25, Definition 1.20, `dfn:stbgpqdf`]
- [AFK25, Theorem 4.37(1), `tm:sqchar`]
-/

noncomputable section

open scoped MatrixGroups

namespace SIC.BinaryQF

/-! ### GL₂(ℤ) action on forms

The coefficient formula realizes the determinant-twisted right action of `GL₂(ℤ)` from [AFK25,
equation (1.31), `eq:afrmtrans`].  Its algebraic laws supply the commutation relation for `2SQ`
that the stability group needs. -/

/-- The right action of GL₂(ℤ) on binary quadratic forms: `Q ↦ Q_M`, where
    Q_M(x,y) = det(M) · Q(αx+βy, γx+δy), equivalently `Q_M = det(M) · Mᵀ Q M`. Two forms Q, Q' are
    equivalent if Q' = Q_M for some M ∈ GL₂(ℤ). See [AFK25, equation (1.31), `eq:afrmtrans`]. The
    polynomial formula is total on integer matrices; its
    restriction to matrices of determinant `±1` is the source action. -/
def gl2zAction (M : Mat(2, ℤ)) (Q : BinaryQF) : BinaryQF :=
  let detM := M.det
  let α := M 0 0
  let β := M 0 1
  let γ := M 1 0
  let δ := M 1 1
  { a := detM * (Q.a * α ^ 2 + Q.b * α * γ + Q.c * γ ^ 2)
    b := detM * (2 * Q.a * α * β + Q.b * (α * δ + β * γ) + 2 * Q.c * γ * δ)
    c := detM * (Q.a * β ^ 2 + Q.b * β * δ + Q.c * δ ^ 2) }

/-- The identity matrix acts trivially on every binary quadratic form. -/
@[simp]
lemma gl2zAction_one (Q : BinaryQF) :
    gl2zAction (1 : Mat(2, ℤ)) Q = Q := by
  change BinaryQF.mk _ _ _ = BinaryQF.mk _ _ _
  congr 1 <;> simp

/-- `gl2zAction` is a right action: first
transforming by `M` and then by `N` is the same as transforming by `M * N`. The formula remains
valid for arbitrary integer matrices. -/
lemma gl2zAction_mul (M N : Mat(2, ℤ)) (Q : BinaryQF) :
    gl2zAction (M * N) Q = gl2zAction N (gl2zAction M Q) := by
  apply toQuadraticForm_injective
  apply QuadraticMap.ext
  intro v
  simp only [toQuadraticForm_apply]
  simp [gl2zAction, eval, Matrix.mul_apply, Matrix.det_mul, Fin.sum_univ_two]
  ring

/-- For the totalized matrix action, left multiplication relates `2S(Q_M)` to `2SQ`, with
the determinant-square factor that disappears on `GL₂(ℤ)`. -/
lemma mul_twiceSQ_gl2zAction
    (M : Mat(2, ℤ)) (Q : BinaryQF) :
    M * (gl2zAction M Q).twiceSQ = M.det ^ 2 • (Q.twiceSQ * M) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twiceSQ, gl2zAction, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.det_fin_two, Matrix.vecMul, dotProduct] <;> ring

/-- The right action `gl2zAction`, represented as a
left action of the opposite group so that Lean's `MulAction` multiplication law has the correct
order. -/
instance : MulAction (GL (Fin 2) ℤ)ᵐᵒᵖ BinaryQF where
  smul M Q := gl2zAction (M.unop : Mat(2, ℤ)) Q
  one_smul Q := gl2zAction_one Q
  mul_smul M N Q := by
    change gl2zAction (((M * N).unop : GL (Fin 2) ℤ) : Mat(2, ℤ)) Q =
      gl2zAction (M.unop : Mat(2, ℤ))
        (gl2zAction (N.unop : Mat(2, ℤ)) Q)
    rw [MulOpposite.unop_mul, Matrix.GeneralLinearGroup.coe_mul]
    exact gl2zAction_mul (N.unop : Mat(2, ℤ))
      (M.unop : Mat(2, ℤ)) Q

/-- For a matrix in `GL₂(ℤ)`, the determinant-square factor in the transformation law for
`2SQ` is one. -/
private lemma coe_mul_twiceSQ_gl2zAction (M : GL (Fin 2) ℤ) (Q : BinaryQF) :
    (M : Mat(2, ℤ)) * (gl2zAction M Q).twiceSQ =
      Q.twiceSQ * (M : Mat(2, ℤ)) := by
  have h := mul_twiceSQ_gl2zAction (M : Mat(2, ℤ)) Q
  rcases gl_det_eq_one_or_neg_one M with hdet | hdet <;> simpa [hdet] using h

/-! ### Stability group

The stabilizer of a form is transported from the opposite-group action to a subgroup of
`GL₂(ℤ)`.  Commutation with `2SQ` gives the integral centralizer description used to impose
principal-congruence levels. -/

/-- The stability group `S(Q) = {M ∈ GL₂(ℤ) | Q_M = Q}` from
[AFK25, Definition 1.20, `dfn:stbgpqdf`]. It is the stabilizer for the opposite-group action,
transported back
to a subgroup of `GL₂(ℤ)`. -/
@[source "AFK25, Definition 1.20, p. 12, dfn:stbgpqdf (1)" (symbol := "S(Q)")]
def stabilityGroup (Q : BinaryQF) : Subgroup (GL (Fin 2) ℤ) :=
  (MulAction.stabilizer (GL (Fin 2) ℤ)ᵐᵒᵖ Q).unop

/-- Membership in `S(Q)` is exactly the coefficient-level stabilization equation. -/
@[simp]
lemma mem_stabilityGroup_iff {Q : BinaryQF} {M : GL (Fin 2) ℤ} :
    M ∈ stabilityGroup Q ↔ gl2zAction (M : Mat(2, ℤ)) Q = Q :=
  Iff.rfl

/-- The stability group of `Q` is the centralizer of `SQ` in `GL₂(ℤ)`, expressed integrally by
commutation with `2SQ`. This is [AFK25, Theorem 4.37(1), `tm:sqchar`]; although the paper states it
for its
primitive forms, the algebraic equivalence holds for every integral coefficient triple. -/
@[source "AFK25, Theorem 4.37, p. 65, tm:sqchar (1)"]
lemma mem_stabilityGroup_iff_commute_twiceSQ {Q : BinaryQF} {M : GL (Fin 2) ℤ} :
    M ∈ stabilityGroup Q ↔
      Commute Q.twiceSQ (M : Mat(2, ℤ)) := by
  rw [mem_stabilityGroup_iff]
  constructor
  · intro hfix
    have h := coe_mul_twiceSQ_gl2zAction M Q
    rw [hfix] at h
    exact h.symm
  · intro hcomm
    apply twiceSQ_injective
    have h := (coe_mul_twiceSQ_gl2zAction M Q).trans hcomm.eq
    have h' := congrArg
      (fun A : Mat(2, ℤ) => (M⁻¹ : Mat(2, ℤ)) * A) h
    simpa [Matrix.mul_assoc, ← Matrix.GeneralLinearGroup.coe_mul] using h'

/-- The determinant-one part of `S(Q)`, viewed as a subgroup of `SL₂(ℤ)`. -/
def stabilityGroupSL (Q : BinaryQF) : Subgroup SL(2, ℤ) :=
  (stabilityGroup Q).comap Matrix.SpecialLinearGroup.toGL

/-- The level stability group `S_d(Q) = S(Q) ∩ Γ(d)` from [AFK25, Definition 1.20, `dfn:stbgpqdf`],
represented inside `SL₂(ℤ)`. The paper assumes `d` is positive; the bundled intersection is
well-defined for every natural `d`. -/
@[source "AFK25, Definition 1.20, p. 12, dfn:stbgpqdf (2)" (symbol := "S_d(Q)")]
def stabilityGroupLevel (Q : BinaryQF) (d : ℕ) : Subgroup SL(2, ℤ) :=
  stabilityGroupSL Q ⊓ CongruenceSubgroup.Gamma d

/-- Membership in `S_d(Q)` means simultaneously stabilizing `Q` and belonging to the principal
congruence subgroup `Γ(d)`. -/
@[simp]
lemma mem_stabilityGroupLevel_iff {d : ℕ} {Q : BinaryQF} {M : SL(2, ℤ)} :
    M ∈ stabilityGroupLevel Q d ↔
      gl2zAction (M : Mat(2, ℤ)) Q = Q ∧
        M ∈ CongruenceSubgroup.Gamma d :=
  Iff.rfl

end SIC.BinaryQF

end
