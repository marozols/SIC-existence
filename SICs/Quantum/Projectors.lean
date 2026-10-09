/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Trace
import SICs.Quantum.WeylHeisenberg

/-!
# Hermitian Projectors and Parity-Hermitian Matrices

Hermitian projector predicates, parity-Hermitian matrices, and the trace/rank identity.

This file defines the Hermitian projectors of [AFK25, Definition 1.1, `dfn:Hprojector`] and their
rank-`r` version, and the parity-Hermitian matrices `M† = U_P M U_P†` of [AFK25, Definition 1.13,
`def:pProjector`]. It proves that the trace of an idempotent is its rank, and that
parity-Hermitian matrices are closed under self-adjoint scalars.

These predicates and the trace identity are the projector-level interface shared by the `r`-SIC
theory of `SICs.Quantum.RSIC` and the ghost-fiducial algebra of `SICs.Ghost.Fiducials`. The
displacement operators themselves are shown parity-Hermitian in
`SICs.Quantum.IntegerDisplacement`, which needs only this interface and not the structural theory
of `r`-SICs.

## Main definitions and results

- `IsHProjector`, `IsRankRHProjector`: [AFK25, Definition 1.1, `dfn:Hprojector`] and its rank-`r`
  form.
- `IsPHermitian`: the parity-Hermitian condition of [AFK25, Definition 1.13, `def:pProjector`].
- `trace_eq_rank_of_idempotent`, `IsRankRHProjector.trace_eq`: the trace of an idempotent is its
  rank.
- `IsPHermitian.smul`: closure under self-adjoint scalars.

## References

- [AFK25] Appleby, Flammia, Kopp, arXiv:2501.03970v2, Definitions 1.1 and 1.13
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

variable {d : ℕ}

/-! ### Hermitian projectors

The basic projector interface separates Hermitian idempotency from the matrix-rank condition.
This mirrors [AFK25, Definition 1.1, `dfn:Hprojector`] and lets later arguments reuse either
layer. -/

/-- A matrix P is an H-projector (Hermitian projector) if it is:
    (1) Hermitian: P = P† (P† denotes the conjugate transpose)
    (2) Idempotent: P² = P
    See [AFK25, Definition 1.1, `dfn:Hprojector`]. -/
@[source "AFK25, Definition 1.1, p. 3, dfn:Hprojector"]
structure IsHProjector (P : Mat(d, ℂ)) : Prop where
  /-- P is Hermitian: P = P†. -/
  hermitian : P.IsHermitian
  /-- P is idempotent: P² = P. -/
  idempotent : P ^ 2 = P

/-- An H-projector of rank `r`. -/
structure IsRankRHProjector (r : ℕ) (P : Mat(d, ℂ)) : Prop where
  /-- The matrix is an H-projector. -/
  isHProjector : IsHProjector P
  /-- The matrix rank is `r`. -/
  rank_eq : P.rank = r

/-! ### Parity-Hermitian matrices

Parity conjugation replaces ordinary Hermitian conjugation in the ghost construction. -/

/-- A matrix `M` is parity-Hermitian if `M† = U_P M U_P†`.
    Equivalently, `M† = U_P M U_P` because `parityOperator` is self-adjoint.
    Ghost fiducials are always parity-Hermitian. See [AFK25, Definition 1.13, `def:pProjector`]. -/
def IsPHermitian (M : Mat(d, ℂ)) : Prop :=
  M.conjTranspose = parityOperator d * M * (parityOperator d).conjTranspose

/-! ### The trace of an idempotent

An idempotent is diagonalizable with eigenvalues `0` and `1`, so its trace counts its rank. This
is what makes the rank of a ghost or SIC projector readable from a displacement expansion. -/

/-- The trace of a complex idempotent matrix is its rank. Standard linear algebra: an idempotent
is diagonalizable with eigenvalues `0` and `1`, so its trace counts the multiplicity of `1`. -/
lemma trace_eq_rank_of_idempotent (P : Mat(d, ℂ)) (hP : P ^ 2 = P) :
    P.trace = (P.rank : ℂ) := by
  have hP' : IsIdempotentElem P.toLin' := by
    change P.toLin'.comp P.toLin' = P.toLin'
    rw [← Matrix.toLin'_mul, ← sq, hP]
  have hproj : LinearMap.IsProj (LinearMap.range P.toLin') P.toLin' :=
    LinearMap.IsIdempotentElem.isProj_range P.toLin' hP'
  rw [← Matrix.trace_toLin'_eq P, hproj.trace]
  have hrank :=
    P.rank_eq_finrank_range_toLin (Pi.basisFun ℂ (Fin d)) (Pi.basisFun ℂ (Fin d))
  rw [Matrix.toLin_eq_toLin'] at hrank
  exact_mod_cast hrank.symm

/-- A rank-`r` Hermitian projector has trace `r`. -/
lemma IsRankRHProjector.trace_eq {r : ℕ} {P : Mat(d, ℂ)}
    (hP : IsRankRHProjector r P) : P.trace = (r : ℂ) := by
  rw [trace_eq_rank_of_idempotent P hP.isHProjector.idempotent, hP.rank_eq]

/-! ### Closure of parity-Hermitian matrices

Parity-Hermiticity is a linear condition over the self-adjoint scalars, so it is preserved by
multiplication by a self-adjoint scalar. -/

/-- Parity-Hermitian matrices are closed under multiplication by a self-adjoint scalar. -/
lemma IsPHermitian.smul {M : Mat(d, ℂ)}
    (hM : IsPHermitian M) {c : ℂ} (hc : IsSelfAdjoint c) :
    IsPHermitian (c • M) := by
  unfold IsPHermitian at hM ⊢
  rw [Matrix.conjTranspose_smul, hc.star_eq, hM,
    Matrix.mul_smul, Matrix.smul_mul]

/-- Every one-dimensional square matrix is its trace times the identity matrix. -/
lemma matrix_fin_one_eq_trace_smul_one (A : Mat(1, ℂ)) :
    A = A.trace • (1 : Mat(1, ℂ)) := by
  ext i j
  simp [Matrix.trace_fin_one, Subsingleton.elim i 0, Subsingleton.elim j 0]

end SIC

end
