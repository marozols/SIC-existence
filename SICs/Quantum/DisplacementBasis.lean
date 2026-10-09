/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Quantum.WeylHeisenberg

/-!
# Displacement bases and matrix expansions

Hilbert–Schmidt orthogonality, displacement-basis reconstruction, and correlations.

This module follows [AFK25, Section 3.1, equations (3.5)–(3.6)] and
[5, Appleby (2007), equations (107)–(109)]. The trace of a displacement is zero away from
the origin, so the displacement matrices are orthogonal for the Hilbert–Schmidt pairing.
Pairing a linear relation with each displacement proves independence; dimension counting
then gives a basis of the full matrix algebra. The same pairing extracts every coefficient
and gives the reconstruction identity.

Conjugating the expansion multiplies its coefficients by the symplectic characters from
`SICs.Quantum.Characters`. For a Hermitian matrix, tracing against the original matrix gives
the Fourier expression for the overlap norm-squares used in [AFK25, equation (3.51)] and
`SICs.Quantum.Fiducials`.
-/

noncomputable section

open Matrix Module
open scoped MatrixGroups

namespace SIC

/-! ### Hilbert-Schmidt orthogonality

Trace orthogonality proves that the displacement matrices form a basis of the full matrix algebra.
The resulting Fourier expansion is the bridge between operators and their overlap coordinates. -/

/-- The trace of a displacement operator is `d` at the origin and zero elsewhere. -/
lemma trace_displacementOperator (d : ℕ) [NeZero d] (p : Fin d × Fin d) :
    (displacementOperator d p).trace = if p = 0 then (d : ℂ) else 0 := by
  rcases p with ⟨p₁, p₂⟩
  by_cases hp₁ : p₁ = 0 <;>
    simp [Matrix.trace, Matrix.diag, displacementOperator_apply_fin, hp₁, omega_geom_sum]

/-- The displacement operators are orthogonal under the Hilbert-Schmidt inner product:
    Tr(D_p† D_q) = d δ_{p,q}. This is [5, Appleby (2007), eq. (107)] and, in the form carrying the
    sign that appears when `p` and `q` are only congruent mod `d`, [AFK25, equation (3.5)]. -/
lemma displacementOperator_HS_orthogonal (d : ℕ) [NeZero d] (p q : Fin d × Fin d) :
    ((displacementOperator d p).conjTranspose * displacementOperator d q).trace =
      if p = q then (d : ℂ) else 0 := by
  rw [conjTranspose_displacementOperator, Matrix.smul_mul,
    displacementOperator_mul_displacementOperator, smul_smul, Matrix.trace_smul,
    trace_displacementOperator]
  rw [show (((-p).1 + q.1, (-p).2 + q.2) : Fin d × Fin d) = -p + q from rfl]
  by_cases hpq : p = q <;> simp [hpq, neg_add_eq_zero]

/-- The displacement operators are linearly independent over `ℂ`.

    This is the linear-independence part of [5, Appleby (2007), eq. (107)]: multiplying a linear
    relation by `D_p†` and taking the trace isolates
    its `p`-th coefficient. -/
theorem displacementOperator_linearIndependent (d : ℕ) [NeZero d] :
    LinearIndependent ℂ (displacementOperator d) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc p
  have hp := congrArg (fun M : Mat(d, ℂ) =>
    ((displacementOperator d p).conjTranspose * M).trace) hc
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
    displacementOperator_HS_orthogonal, mul_zero, Matrix.trace_zero] at hp
  have hp' : c p * (d : ℂ) = 0 := by
    simpa [eq_comm] using hp
  exact (mul_eq_zero.mp hp').resolve_right
    (show (d : ℂ) ≠ 0 by exact_mod_cast NeZero.ne d)

/-- The displacement operators, indexed by canonical pairs in `(Fin d)²`, form a basis of
    the full complex matrix algebra. See [5, Appleby (2007), eqs. (107)–(108)]. -/
noncomputable def displacementBasis (d : ℕ) [NeZero d] :
    Basis (Fin d × Fin d) ℂ (Mat(d, ℂ)) :=
  basisOfLinearIndependentOfCardEqFinrank' (displacementOperator d)
    (displacementOperator_linearIndependent d) (by simp [Module.finrank_matrix])

/-- The displacement basis evaluates to the corresponding displacement operator. -/
@[simp]
lemma displacementBasis_apply (d : ℕ) [NeZero d] (p : Fin d × Fin d) :
    displacementBasis d p = displacementOperator d p := by
  simp [displacementBasis]

/-- The coefficient of a matrix in the displacement basis is its normalized
    Hilbert–Schmidt pairing with that displacement operator. This is
    [5, Appleby (2007), eq. (109), `eq:WHExpCoeffs`]. -/
lemma displacementBasis_repr (d : ℕ) [NeZero d]
    (M : Mat(d, ℂ)) (p : Fin d × Fin d) :
    (displacementBasis d).repr M p =
      (d : ℂ)⁻¹ * ((displacementOperator d p).conjTranspose * M).trace := by
  have hsum := congrArg (fun N : Mat(d, ℂ) =>
    ((displacementOperator d p).conjTranspose * N).trace) ((displacementBasis d).sum_repr M)
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
    displacementBasis_apply, displacementOperator_HS_orthogonal] at hsum
  have hp : (displacementBasis d).repr M p * (d : ℂ) =
      ((displacementOperator d p).conjTranspose * M).trace := by
    simpa [eq_comm] using hsum
  rw [← hp]
  field_simp [show (d : ℂ) ≠ 0 by exact_mod_cast NeZero.ne d]

/-- Every complex matrix is reconstructed from its displacement overlaps:
    `M = (1 / d) ∑ p, Tr(D_p† M) • D_p`.

    This is [5, Appleby (2007), eqs. (108)–(109)] and
    [AFK25, eq. (3.6), `eq:mdopexp`]. -/
theorem displacementOperator_reconstruction (d : ℕ) [NeZero d]
    (M : Mat(d, ℂ)) :
    M = ∑ p : Fin d × Fin d,
      ((d : ℂ)⁻¹ * ((displacementOperator d p).conjTranspose * M).trace) •
        displacementOperator d p := by
  calc
    M = ∑ p : Fin d × Fin d, (displacementBasis d).repr M p • displacementOperator d p := by
      simpa using ((displacementBasis d).sum_repr M).symm
    _ = ∑ p : Fin d × Fin d,
        ((d : ℂ)⁻¹ * ((displacementOperator d p).conjTranspose * M).trace) •
          displacementOperator d p := by
      apply Finset.sum_congr rfl
      intro p _
      rw [displacementBasis_repr]

/-- Overlap-ordered form of `displacementOperator_reconstruction`:
    `M = (1 / d) ∑ p, Tr(M D_p†) • D_p`.

    This ordering matches the convention of `overlap`. -/
theorem displacementOperator_expansion (d : ℕ) [NeZero d]
    (M : Mat(d, ℂ)) :
    M = ∑ p : Fin d × Fin d,
      ((d : ℂ)⁻¹ * (M * (displacementOperator d p).conjTranspose).trace) •
        displacementOperator d p := by
  calc
    M = ∑ p : Fin d × Fin d,
        ((d : ℂ)⁻¹ * ((displacementOperator d p).conjTranspose * M).trace) •
          displacementOperator d p :=
      displacementOperator_reconstruction d M
    _ = ∑ p : Fin d × Fin d,
        ((d : ℂ)⁻¹ * (M * (displacementOperator d p).conjTranspose).trace) •
          displacementOperator d p := by
      apply Finset.sum_congr rfl
      intro p _
      rw [Matrix.trace_mul_comm]

/-- Expansion of a matrix after conjugation by a displacement operator. The displacement-basis
    coefficient at `k` is multiplied by `whCharacter d p k`. -/
theorem displacementOperator_conjugation_expansion (d : ℕ) [NeZero d]
    (M : Mat(d, ℂ)) (p : Fin d × Fin d) :
    displacementOperator d p * M * (displacementOperator d p).conjTranspose =
      ∑ k : Fin d × Fin d,
        ((d : ℂ)⁻¹ * (M * (displacementOperator d k).conjTranspose).trace *
          whCharacter d p k) • displacementOperator d k := by
  calc
    displacementOperator d p * M * (displacementOperator d p).conjTranspose =
        displacementOperator d p *
          (∑ k : Fin d × Fin d,
            ((d : ℂ)⁻¹ * (M * (displacementOperator d k).conjTranspose).trace) •
              displacementOperator d k) *
          (displacementOperator d p).conjTranspose := by
      rw [← displacementOperator_expansion d M]
    _ = ∑ k : Fin d × Fin d,
        ((d : ℂ)⁻¹ * (M * (displacementOperator d k).conjTranspose).trace *
          whCharacter d p k) • displacementOperator d k := by
      simp only [Matrix.mul_sum, Finset.sum_mul, Matrix.mul_smul, smul_mul_assoc,
        displacementOperator_conj_displacementOperator, smul_smul]

/-- For Hermitian `M`, the trace of `D_k M` is the complex conjugate of the
    displacement overlap `Tr(M D_k†)`. -/
private lemma trace_displacementOperator_mul_of_isHermitian (d : ℕ) [NeZero d]
    {M : Mat(d, ℂ)} (hM : M.IsHermitian) (k : Fin d × Fin d) :
    (displacementOperator d k * M).trace =
      star (M * (displacementOperator d k).conjTranspose).trace := by
  simpa only [conjTranspose_mul, conjTranspose_conjTranspose, hM.eq] using
    Matrix.trace_conjTranspose (M * (displacementOperator d k).conjTranspose)

/-- WH correlation formula for a Hermitian matrix, expressed through the squared norms of its
    displacement overlaps. This is the general matrix identity behind
    [5, Appleby (2007), eq. (75), `eq:BBpScalarProduct`] and [AFK25, eq. (3.51)]. -/
theorem displacementOperator_conjugation_correlation (d : ℕ) [NeZero d]
    {M : Mat(d, ℂ)} (hM : M.IsHermitian) (p : Fin d × Fin d) :
    ((displacementOperator d p * M * (displacementOperator d p).conjTranspose) * M).trace =
      (d : ℂ)⁻¹ * ∑ k : Fin d × Fin d,
        whCharacter d p k *
          (Complex.normSq (M * (displacementOperator d k).conjTranspose).trace : ℂ) := by
  rw [displacementOperator_conjugation_expansion]
  simp only [Finset.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [trace_displacementOperator_mul_of_isHermitian d hM]
  change
    ((d : ℂ)⁻¹ * (M * (displacementOperator d k).conjTranspose).trace * whCharacter d p k) *
        star (M * (displacementOperator d k).conjTranspose).trace =
      (d : ℂ)⁻¹ *
        (whCharacter d p k *
          (Complex.normSq (M * (displacementOperator d k).conjTranspose).trace : ℂ))
  have hnorm :
      star (M * (displacementOperator d k).conjTranspose).trace *
          (M * (displacementOperator d k).conjTranspose).trace =
        (Complex.normSq (M * (displacementOperator d k).conjTranspose).trace : ℂ) := by
    simpa only [Complex.star_def] using
      (Complex.normSq_eq_conj_mul_self
        (z := (M * (displacementOperator d k).conjTranspose).trace)).symm
  calc
    (d : ℂ)⁻¹ * (M * (displacementOperator d k).conjTranspose).trace * whCharacter d p k *
        star (M * (displacementOperator d k).conjTranspose).trace =
      (d : ℂ)⁻¹ * (whCharacter d p k *
        (star (M * (displacementOperator d k).conjTranspose).trace *
          (M * (displacementOperator d k).conjTranspose).trace)) := by ring
    _ = (d : ℂ)⁻¹ * (whCharacter d p k *
        (Complex.normSq (M * (displacementOperator d k).conjTranspose).trace : ℂ)) := by
      rw [hnorm]

end SIC

end
