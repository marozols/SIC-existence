/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.RingTheory.FiniteType
import SICs.MatrixNotation
import SICs.Quantum.Characters
import SICs.Source

/-!
# Weyl--Heisenberg Operators

Weyl–Heisenberg operators and displacement identities.

This file defines the standard operators used by the Weyl--Heisenberg group `WH(d)`:

- The shift operator X (cyclic permutation of the standard basis)
- The phase operator Z (diagonal phase matrix)
- The displacement operators D_p = ξ_d^(p₁p₂) · X^p₁ · Z^p₂
- The parity operator U_P

These operators are the fundamental building blocks of WH-covariant SIC constructions.
The paper studies WH-covariant SICs in dimension greater than three; it refers to the
low-dimensional examples excluded by these standing restrictions as sporadic SICs.
The finite group `WH(d)` itself is not packaged as a Lean `Subgroup` in this file.

## Main definitions

- `shiftOperator d`: the shift operator
- `phaseOperator d`: the phase operator
- `displacementOperator d p`: displacement operator for index p ∈ (Fin d)²
- `parityOperator d`: the parity operator

The canonical phases `standardRoot` (`ω_d`) and `displacementPhase` (`ξ_d`), their orders, and the
finite character `omegaFin` are defined in `SICs.Quantum.RootsOfUnity`. The symplectic characters
and Fourier transform are developed in `SICs.Quantum.Characters`; the displacement basis and
its reconstruction and correlation identities are in `SICs.Quantum.DisplacementBasis`.

## References
- [AFK25] Appleby, Flammia, Kopp, arXiv:2501.03970v2, Definitions 1.5 and 1.13
- [5, Appleby (2007)] *Symmetric informationally complete measurements of
  arbitrary rank*, arXiv:quant-ph/0611260
-/

noncomputable section

open Matrix
open scoped MatrixGroups

namespace SIC

/-! ### The shift and phase operators

The cyclic shift `shiftOperator` and diagonal phase `phaseOperator` realize the two generators used
to define the Weyl--Heisenberg operators in [AFK25, Definition 1.5, `def:WHGroup`]. -/

/-- The shift operator X: X|j⟩ = |j+1 mod d⟩.
    As a d×d matrix: X[i,j] = δ_{i, j+1 mod d}.
    Satisfies X^d = I and ZX = ω_d · XZ. See [AFK25, Definition 1.5, `def:WHGroup`]. -/
def shiftOperator (d : ℕ) [NeZero d] : Mat(d, ℂ) :=
  fun i j => if i = j + 1 then 1 else 0

/-- The phase operator Z: Z|j⟩ = ω_d^j · |j⟩.
    As a d×d matrix: Z = diag(1, ω_d, ω_d², ..., ω_d^{d-1}).
    Satisfies Z^d = I and ZX = ω_d · XZ. See [AFK25, Definition 1.5, `def:WHGroup`]. -/
def phaseOperator (d : ℕ) [NeZero d] : Mat(d, ℂ) :=
  Matrix.diagonal (fun j => standardRoot d ^ (j : ℕ))

/-! ### Displacement operators

The displacement matrix combines the canonical phase with powers of `shiftOperator` and
`phaseOperator`. Finite indices choose canonical representatives, so later multiplication laws
retain explicit correction phases. -/

/-- The displacement operator D_p for p = (p₁, p₂) ∈ (Fin d)²:
      D_p = ξ_d^(p₁·p₂) · X^p₁ · Z^p₂ The family {D_p} forms a basis for the d×d matrix algebra
      Mat_d(ℂ). [AFK25, Definition 1.5, `def:WHGroup`], equation (1.2), indexes `D_p` by `p ∈ ℤ²`.
      This definition chooses the canonical representatives in `Fin d`; addition and negation of
      indices can
    therefore contribute the explicit representative-change phases defined below. -/
@[source "AFK25, Definition 1.5, p. 4, def:WHGroup" (symbol := "D_p")]
def displacementOperator (d : ℕ) [NeZero d] (p : Fin d × Fin d) : Mat(d, ℂ) :=
  displacementPhase d ^ (p.1.val * p.2.val) •
    ((shiftOperator d) ^ p.1.val * (phaseOperator d) ^ p.2.val)

/-! ### Parity operator

The parity permutation implements index negation and supplies the involution used in the
parity-Hermitian projector condition of [AFK25, Definition 1.13, `def:pProjector`]. -/

/-- The parity operator `U_P`: `U_P|j⟩ = |-j mod d⟩`.
    This is the unitary matrix corresponding to the parity matrix P = -I ∈ SL₂(ℤ/d̄ℤ).
    See [AFK25, Definition 1.13, `def:pProjector`]. -/
def parityOperator (d : ℕ) : Mat(d, ℂ) :=
  fun i j => if j = -i then 1 else 0

/-! ### Basic algebraic properties

Entrywise formulas establish the orders of `shiftOperator` and `phaseOperator`. These identities
reduce the later matrix arguments to finite arithmetic. -/

/-- Entry formula for `X^a`: its `(i,j)` entry is one exactly when `i = j + a`, and zero
otherwise. -/
private lemma shiftOperator_pow_apply (d : ℕ) [NeZero d] (a : ℕ) (i j : Fin d) :
    (shiftOperator d ^ a) i j = if i.val = (j.val + a) % d then 1 else 0 := by
  induction a generalizing j with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, Nat.add_zero, Nat.mod_eq_of_lt j.isLt]
    congr 1
    exact propext Fin.ext_iff
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply]
    simp only [shiftOperator]
    simp_rw [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [ih]
    congr 1
    have : (j + 1 : Fin d).val = (j.val + 1) % d := by simp [Fin.val_add]
    rw [this, Nat.mod_add_mod, Nat.add_assoc, Nat.add_comm 1 n]

/-- Entry formula for a finitely indexed power of `shiftOperator`. -/
private lemma shiftOperator_pow_apply_fin (d : ℕ) [NeZero d] (a i j : Fin d) :
    (shiftOperator d ^ a.val) i j = if i = j + a then 1 else 0 := by
  simpa [Fin.ext_iff, Fin.val_add] using shiftOperator_pow_apply d a.val i j

/-- X^d = I: the shift operator has order d. -/
lemma shiftOperator_pow_d (d : ℕ) [NeZero d] : shiftOperator d ^ d = 1 := by
  ext i j
  simp [shiftOperator_pow_apply, Matrix.one_apply, Nat.mod_eq_of_lt j.isLt,
    Fin.ext_iff]

/-- Powers of `Z` remain diagonal, with `i`-th diagonal entry `ω_d^(ia)`. -/
private lemma phaseOperator_pow_eq_diagonal (d : ℕ) [NeZero d] (a : ℕ) :
    phaseOperator d ^ a = Matrix.diagonal (fun i => standardRoot d ^ (i.val * a)) := by
  simp [phaseOperator, Matrix.diagonal_pow, ← pow_mul]

/-- Z^d = I: the phase operator has order d. -/
lemma phaseOperator_pow_d (d : ℕ) [NeZero d] : phaseOperator d ^ d = 1 := by
  ext i j
  simp [phaseOperator_pow_eq_diagonal, Matrix.diagonal_apply, Matrix.one_apply, mul_comm,
    pow_mul, standardRoot_pow_d]

/-- A complex number of norm one cancels with its conjugate. -/
lemma star_mul_self_of_norm_eq_one (z : ℂ) (hz : ‖z‖ = 1) : star z * z = 1 := by
  simpa [Complex.star_def, hz] using Complex.conj_mul' z

/-- The displacement operator at the origin is the identity matrix. -/
@[simp] lemma displacementOperator_zero (d : ℕ) [NeZero d] :
    displacementOperator d ((0 : Fin d), (0 : Fin d)) = 1 := by
  simp [displacementOperator, phaseOperator]

/-- The displacement operator indexed by `(1, 0)` is the shift operator. -/
@[simp] lemma displacementOperator_one_zero (d : ℕ) [NeZero d] :
    displacementOperator d ((1 : Fin d), (0 : Fin d)) = shiftOperator d := by
  simp only [displacementOperator, Fin.val_zero, mul_zero, pow_zero, one_smul, Matrix.mul_one,
    Fin.val_one']
  simpa using (pow_eq_pow_mod 1 (shiftOperator_pow_d d)).symm

/-- The displacement operator indexed by `(0, 1)` is the phase operator. -/
@[simp] lemma displacementOperator_zero_one (d : ℕ) [NeZero d] :
    displacementOperator d ((0 : Fin d), (1 : Fin d)) = phaseOperator d := by
  simp only [displacementOperator, Fin.val_zero, zero_mul, pow_zero, one_smul, Matrix.one_mul,
    Fin.val_one']
  simpa using (pow_eq_pow_mod 1 (phaseOperator_pow_d d)).symm

/-! ### Entry formulas

The intrinsic `Fin d` entry formula makes the unique nonzero entry in each row of a displacement
operator explicit; it proves unitarity below and supplies the trace calculations in
`SICs.Quantum.DisplacementBasis`. -/

/-- Entry formula for `displacementOperator`, stated intrinsically in `Fin d`:
`(D_p)_{ij} = ξ_d^{p₁p₂} ω_d^{j p₂}` when `i = j + p₁` and `0` otherwise. -/
lemma displacementOperator_apply_fin (d : ℕ) [NeZero d] (p : Fin d × Fin d) (i j : Fin d) :
    displacementOperator d p i j =
      if i = j + p.1
      then displacementPhase d ^ (p.1.val * p.2.val) * standardRoot d ^ (j.val * p.2.val)
      else 0 := by
  simp [displacementOperator, Matrix.mul_apply, phaseOperator_pow_eq_diagonal,
    shiftOperator_pow_apply_fin, Matrix.diagonal_apply, eq_comm]

/-! ### Unitarity

The entry formula shows directly that every displacement operator is unitary in both
multiplication orders. -/

/-- The displacement operators D_p are unitary:
    D_p · D_p† = I. -/
lemma displacementOperator_mul_conjTranspose (d : ℕ) [NeZero d] (p : Fin d × Fin d) :
    displacementOperator d p * (displacementOperator d p).conjTranspose = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, displacementOperator_apply_fin]
  have hshift (a x : Fin d) : a = x + p.1 ↔ x = a - p.1 := by
    constructor
    · exact fun h => eq_sub_iff_add_eq.mpr h.symm
    · exact fun h => (eq_sub_iff_add_eq.mp h).symm
  simp_rw [hshift]
  by_cases h : i = j
  · subst j
    simpa [mul_comm] using star_mul_self_of_norm_eq_one
      (displacementPhase d ^ (p.1.val * p.2.val) *
        standardRoot d ^ ((i - p.1).val * p.2.val)) (by simp)
  · simp [h]

/-- The displacement operators are unitary in the opposite multiplication order:
    D_p† · D_p = I. -/
lemma conjTranspose_mul_displacementOperator (d : ℕ) [NeZero d] (p : Fin d × Fin d) :
    (displacementOperator d p).conjTranspose * displacementOperator d p = 1 :=
  (Matrix.mul_eq_one_comm_of_card_eq (Fin d) (Fin d) ℂ rfl).mpr
    (displacementOperator_mul_conjTranspose d p)

/-! ### Displacement operator multiplication

Because `displacementOperator` uses `Fin d` representatives, its exact multiplier includes a
representative-change factor. Comparing that multiplier in the two orders recovers the usual
symplectic commutator. -/

/-- The exact multiplier for `D_p D_q` in the canonical `Fin d`-indexed representation.
    Due to the use of `Fin d` representatives, the phase differs from the paper's
    `ξ^{⟨p,q⟩}` by a correction involving `Fin d` arithmetic. -/
def displacementMulPhase (d : ℕ) [NeZero d] (p q : Fin d × Fin d) : ℂ :=
  displacementPhase d ^ (p.1.val * p.2.val) *
    displacementPhase d ^ (q.1.val * q.2.val) *
    standardRoot d ^ ((p.2 * q.1 : Fin d).val) *
    (displacementPhase d ^ ((p.1 + q.1).val * (p.2 + q.2).val))⁻¹

/-- Swapping the indices in the exact displacement multiplier introduces the
    Weyl–Heisenberg symplectic character. -/
private lemma displacementMulPhase_comm (d : ℕ) [NeZero d] (p q : Fin d × Fin d) :
    displacementMulPhase d p q = whCharacter d p q * displacementMulPhase d q p := by
  simp only [displacementMulPhase]
  change
    displacementPhase d ^ (p.1.val * p.2.val) * displacementPhase d ^ (q.1.val * q.2.val) *
          omegaFin d (p.2 * q.1) *
          (displacementPhase d ^ ((p.1 + q.1).val * (p.2 + q.2).val))⁻¹ =
      whCharacter d p q *
        (displacementPhase d ^ (q.1.val * q.2.val) * displacementPhase d ^ (p.1.val * p.2.val) *
          omegaFin d (q.2 * p.1) *
          (displacementPhase d ^ ((q.1 + p.1).val * (q.2 + p.2).val))⁻¹)
  simp only [whCharacter, sub_eq_add_neg,
    omegaFin_add, omegaFin_neg]
  have hω : omegaFin d (p.1 * q.2) ≠ 0 := by
    simp [omegaFin, standardRoot]
  rw [mul_comm q.2 p.1, add_comm q.1 p.1, add_comm q.2 p.2]
  field_simp

/-- Exact multiplication law for the displacement operators indexed by `Fin d`. -/
lemma displacementOperator_mul_displacementOperator (d : ℕ) [NeZero d] (p q : Fin d × Fin d) :
    displacementOperator d p * displacementOperator d q =
      displacementMulPhase d p q • displacementOperator d (p.1 + q.1, p.2 + q.2) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, displacementOperator_apply_fin,
    ite_mul, zero_mul]
  rw [Finset.sum_eq_single (j + q.1)]
  · have hindex : j + q.1 + p.1 = j + (p.1 + q.1) := by abel
    rw [hindex]
    by_cases h : i = j + (p.1 + q.1)
    · rw [ite_eq_left h, ite_eq_left h]
      have hphase :
          displacementPhase d ^ (p.1.val * p.2.val) *
              (displacementPhase d ^ (q.1.val * q.2.val) *
                omegaFin d (j * p.2 + (j * q.2 + q.1 * p.2))) =
            standardRoot d ^ (q.1 * p.2 : Fin d).val *
              (displacementPhase d ^ (p.1.val * p.2.val) *
                (displacementPhase d ^ (q.1.val * q.2.val) * omegaFin d (j * p.2 + j * q.2))) := by
        rw [show standardRoot d ^ (q.1 * p.2 : Fin d).val =
          omegaFin d (q.1 * p.2) from rfl]
        simp only [omegaFin_add]
        ring
      simpa [displacementMulPhase, omega_pow_mul_eq_omegaFin, displacementPhase_ne_zero,
        mul_assoc, mul_left_comm, mul_comm, omegaFin_add, mul_add,
        add_left_comm, add_comm] using hphase
    · rw [ite_eq_right h, ite_eq_right h, mul_zero]
  · intro b _ hb
    simp [hb]
  · simp

/-- Displacement operators commute up to the symplectic character. -/
lemma displacementOperator_commutation (d : ℕ) [NeZero d] (p q : Fin d × Fin d) :
    displacementOperator d p * displacementOperator d q =
      whCharacter d p q • (displacementOperator d q * displacementOperator d p) := by
  rw [displacementOperator_mul_displacementOperator,
    displacementOperator_mul_displacementOperator, displacementMulPhase_comm]
  simp [smul_smul, add_comm]

/-- The multiplier in the displacement-operator multiplication law has unit norm. -/
@[simp] lemma norm_displacementMulPhase (d : ℕ) [NeZero d] (p q : Fin d × Fin d) :
    ‖displacementMulPhase d p q‖ = 1 := by
  simp [displacementMulPhase]

/-- The multiplier in the displacement-operator multiplication law is nonzero. -/
@[simp] lemma displacementMulPhase_ne_zero (d : ℕ) [NeZero d] (p q : Fin d × Fin d) :
    displacementMulPhase d p q ≠ 0 :=
  norm_ne_zero_iff.mp (by simp)

/-- Conjugating successively by displacement operators is conjugation by their sum. -/
lemma displacementOperator_conjugation_comp (d : ℕ) [NeZero d]
    (p q : Fin d × Fin d) (M : Mat(d, ℂ)) :
    displacementOperator d p *
        (displacementOperator d q * M * (displacementOperator d q).conjTranspose) *
        (displacementOperator d p).conjTranspose =
      displacementOperator d (p + q) * M * (displacementOperator d (p + q)).conjTranspose := by
  simp only [Matrix.mul_assoc]
  rw [← conjTranspose_mul (displacementOperator d p) (displacementOperator d q),
    ← Matrix.mul_assoc (displacementOperator d p) (displacementOperator d q),
    displacementOperator_mul_displacementOperator]
  simp only [Matrix.conjTranspose_smul, smul_mul_assoc, mul_smul_comm,
    smul_smul, star_mul_self_of_norm_eq_one _ (norm_displacementMulPhase d p q),
    one_smul]
  rfl

/-- The adjoint of a displacement operator is the oppositely indexed displacement operator,
    multiplied by the representative-change phase coming from `Fin d` indexing. -/
lemma conjTranspose_displacementOperator (d : ℕ) [NeZero d] (p : Fin d × Fin d) :
    (displacementOperator d p).conjTranspose =
      (displacementMulPhase d (-p) p)⁻¹ • displacementOperator d (-p) := by
  refine (left_inv_eq_right_inv ?_ (displacementOperator_mul_conjTranspose d p)).symm
  simp [displacementOperator_mul_displacementOperator, smul_smul]

/-- Conjugation of one displacement operator by another is multiplication by the
    symplectic character: `D_p D_k D_p† = χₚ(k) D_k`.

    See [5, Appleby (2007), eq. (74)] and [AFK25, eq. (3.51)]. -/
theorem displacementOperator_conj_displacementOperator (d : ℕ) [NeZero d]
    (p k : Fin d × Fin d) :
    displacementOperator d p * displacementOperator d k *
        (displacementOperator d p).conjTranspose =
      whCharacter d p k • displacementOperator d k := by
  rw [displacementOperator_commutation]
  simp only [smul_mul_assoc, Matrix.mul_assoc, displacementOperator_mul_conjTranspose,
    Matrix.mul_one]

/-! ### Parity conjugation

Conjugation by parity negates both matrix indices.  Translating this action to displacement
operators exposes the phase caused by the chosen `Fin d` representatives. -/

/-- The parity matrix conjugates an arbitrary matrix by negating both indices. -/
private lemma parityOperator_conj_apply (d : ℕ)
    (M : Mat(d, ℂ)) (i j : Fin d) :
    (parityOperator d * M * (parityOperator d).conjTranspose) i j = M (-i) (-j) := by
  simp [parityOperator, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- The representative-change phase introduced by negating a Fin d displacement index. -/
def displacementParityPhase (d : ℕ) [NeZero d] (p : Fin d × Fin d) : ℂ :=
  displacementPhase d ^ (p.1.val * p.2.val) *
    (displacementPhase d ^ ((-p.1).val * (-p.2).val))⁻¹

/-- Exact parity conjugation law for the Fin d-indexed displacement operators. -/
lemma parityOperator_conjugates_displacementOperator (d : ℕ) [NeZero d] (p : Fin d × Fin d) :
    parityOperator d * displacementOperator d p * (parityOperator d).conjTranspose =
      displacementParityPhase d p • displacementOperator d (-p.1, -p.2) := by
  ext i j
  simp [parityOperator_conj_apply, displacementOperator_apply_fin, displacementParityPhase,
    neg_eq_iff_eq_neg, neg_add_rev, add_comm, omega_pow_mul_eq_omegaFin, neg_mul, mul_neg,
    mul_assoc, displacementPhase_ne_zero]

end SIC

end
