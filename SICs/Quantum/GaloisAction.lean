/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.FieldTheory.ComplexGalois
import SICs.Quantum.IntegerDisplacement

/-!
# The Galois action on roots of unity and displacement operators

The exponent `k_g`, the matrix `H_g`, and the action `g(D_p) = D_{H_g p}` of Theorem 3.7.

Applying a Galois automorphism entrywise to a displacement expansion, as the ghost-to-live
conversion does, requires two things: the action of the automorphism on the constants `ω_d` and
`ξ_d` from which every displacement operator is built, and the resulting permutation of
displacement indices. This file supplies both, together with the elementary transfer lemmas that
entrywise conjugation satisfies. It concerns the Weyl--Heisenberg operator algebra itself and
uses no ghost-overlap data.

The central result is [AFK25, Theorem 3.7, `thm:GalActOnClifford`], the displacement half of which
reads

`g(D_p) = D_{H_g p}`,  `H_g = ![![1, 0], ![0, k_g]]`,

where `k_g` is the exponent of [AFK25, Definition 3.6, `dfn:HgMatrixDefinition`], defined by
`g(ξ_d) = ξ_d^{k_g}`. The statement is about the integer-indexed displacement operators of [AFK25,
Definition 1.5, `def:WHGroup`] (`integerDisplacement`), not the canonical-representative
`displacementOperator`: the identity is false for `displacementOperator` in even dimensions, where
changing an integer representative contributes the sign `ξ_d^d = -1`.

The symplectic-unitary half of [AFK25, Theorem 3.7, `thm:GalActOnClifford`], equation (3.21),
is not needed and is not formalized.

## Representation of the Galois group

[AFK25, Definition 3.6, `dfn:HgMatrixDefinition` and Theorem 3.7, `thm:GalActOnClifford`] quantify
over `Gal(ℚ(ξ_d)/ℚ)`. Following `ComplexGaloisAutomorphism`, this file instead uses ambient
`ℚ`-algebra automorphisms of `ℂ`, which is the interpretation the construction actually needs and
the one discussed after [AFK25, Definition 1.41, `def:fiducialdata`]. Every such automorphism
restricts to one of `ℚ(ξ_d)`, so the results below are instances of the source's, not
generalizations of them. Nothing here asserts that a given element of `Gal(ℚ(ξ_d)/ℚ)` extends to
`ℂ`.

## Main definitions and results

- `galoisExponent d g`: the exponent `k_g` of [AFK25, Definition 3.6, `dfn:HgMatrixDefinition`],
  with `galoisExponent_coprime` and the defining `map_displacementPhase`.
- `map_standardRoot`: the induced action `g(ω_d) = ω_d^{k_g}` on the `d`-th root of unity.
- `mapMatrix_shiftOperator`, `mapMatrix_phaseOperator`: the action on the shift and phase operators.
- `galoisIndexMatrix`: the matrix `H_g` of [AFK25, Definition 3.6, `dfn:HgMatrixDefinition`].
- `mapMatrix_integerDisplacement`: [AFK25, Theorem 3.7, `thm:GalActOnClifford`],
  `g(D_p) = D_{H_g p}`.
- `mapMatrix_sq_eq_self` and `trace_mapMatrix`: entrywise conjugation preserves idempotency and
  intertwines the trace.
- `galoisInverseIndexMatrix` and `galoisInverseIndexMatrix_mulVec_mulVec`: an integer matrix
  inverting `H_g` modulo `d̄`, for reindexing displacement expansions.

## References

- [AFK25] Appleby, Flammia, Kopp, arXiv:2501.03970v2, Definition 3.6 and Theorem 3.7
-/

noncomputable section

namespace SIC

open scoped MatrixGroups

/-! ### The Galois exponent `k_g`

The image of the primitive phase `ξ_d` determines a unique exponent modulo `dbar d`.  Primitivity
also proves this exponent coprime to `dbar d`, as required for the index permutation. -/

/-- **`galoisExponent` is well posed.** Every `ℚ`-algebra automorphism of `ℂ` sends the
primitive `d̄`-th root of unity `ξ_d` to a power `ξ_d^k` with `0 ≤ k < d̄`, and that exponent is
automatically coprime to `d̄` because `g` preserves the order of a root of unity. -/
theorem exists_galoisExponent (d : ℕ) [NeZero d] (g : ComplexGaloisAutomorphism) :
    ∃ k : ℕ, k < dbar d ∧ Nat.Coprime k (dbar d) ∧
      g (displacementPhase d) = displacementPhase d ^ k := by
  have hprim := displacementPhase_isPrimitiveRoot d
  have hpow : g (displacementPhase d) ^ dbar d = 1 := by
    rw [← map_pow, displacementPhase_pow_dbar, map_one]
  obtain ⟨k, hk, hkeq⟩ := hprim.eq_pow_of_pow_eq_one hpow
  refine ⟨k, hk, ?_, hkeq.symm⟩
  have hgprim : IsPrimitiveRoot (g (displacementPhase d)) (dbar d) :=
    hprim.map_of_injective g.injective
  rw [← hkeq] at hgprim
  exact (hprim.pow_iff_coprime (Nat.pos_of_ne_zero (dbar_ne_zero d)) k).mp hgprim

/-- The exponent `k_g` of [AFK25, Definition 3.6, `dfn:HgMatrixDefinition`]: the unique `0 ≤ k < d̄`
with
`g(ξ_d) = ξ_d^{k}`. -/
def galoisExponent (d : ℕ) [NeZero d] (g : ComplexGaloisAutomorphism) : ℕ :=
  (exists_galoisExponent d g).choose

/-- `k_g` is coprime to `d̄`, so `H_g` is invertible modulo `d̄` as `galoisIndexMatrix`
requires. -/
lemma galoisExponent_coprime (d : ℕ) [NeZero d] (g : ComplexGaloisAutomorphism) :
    Nat.Coprime (galoisExponent d g) (dbar d) :=
  (exists_galoisExponent d g).choose_spec.2.1

/-- The defining property of `k_g`: `g(ξ_d) = ξ_d^{k_g}`. -/
@[simp]
lemma map_displacementPhase (d : ℕ) [NeZero d] (g : ComplexGaloisAutomorphism) :
    g (displacementPhase d) = displacementPhase d ^ galoisExponent d g :=
  (exists_galoisExponent d g).choose_spec.2.2

/-- The action of `g` on integer powers of `ξ_d`. -/
lemma map_displacementPhase_zpow (d : ℕ) [NeZero d] (g : ComplexGaloisAutomorphism) (m : ℤ) :
    g (displacementPhase d ^ m) = displacementPhase d ^ ((galoisExponent d g : ℤ) * m) := by
  rw [map_zpow₀, map_displacementPhase,
    ← zpow_natCast (displacementPhase d) (galoisExponent d g), ← _root_.zpow_mul]

/-- **The induced action on `ω_d`.** Since `ω_d = ξ_d²`, the same exponent governs the `d`-th root
of unity: `g(ω_d) = ω_d^{k_g}`. -/
@[simp]
lemma map_standardRoot (d : ℕ) [NeZero d] (g : ComplexGaloisAutomorphism) :
    g (standardRoot d) = standardRoot d ^ galoisExponent d g := by
  rw [← displacementPhase_sq, map_pow, map_displacementPhase, ← pow_mul, ← pow_mul, Nat.mul_comm]

/-! ### Entrywise conjugation of matrices

Entrywise application of a `ℚ`-automorphism respects matrix products, powers, and traces, while
conjugating complex scalars.  These transfer lemmas preserve the projector equations. -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Entrywise Galois conjugation is only `ℚ`-linear, so it moves a complex scalar through a
scalar multiplication by conjugating it. -/
lemma mapMatrix_smul (g : ComplexGaloisAutomorphism) (c : ℂ) (M : Matrix n n ℂ) :
    g.mapMatrix (c • M) = g c • g.mapMatrix M := by
  ext i j
  simp [AlgEquiv.mapMatrix_apply]

/-- **Entrywise Galois conjugation preserves idempotency.** This is the first step of
[AFK25, proof of Theorem 1.46, `thm:rayclassfieldrsicgen`], and the reason a live fiducial
obtained by conjugating a ghost fiducial is again a projector. -/
theorem mapMatrix_sq_eq_self (g : ComplexGaloisAutomorphism) {M : Matrix n n ℂ}
    (h : M ^ 2 = M) : g.mapMatrix M ^ 2 = g.mapMatrix M := by
  rw [← map_pow, h]

/-- Entrywise Galois conjugation intertwines the trace. -/
theorem trace_mapMatrix (g : ComplexGaloisAutomorphism) (M : Matrix n n ℂ) :
    (g.mapMatrix M).trace = g M.trace :=
  (AddMonoidHom.map_trace g M).symm

/-! ### The action on the shift and phase operators

Rational entries make the shift operator fixed by every automorphism, whereas the phase operator
is raised to `k_g`.  This is the generator-level calculation behind the displacement action. -/

/-- The shift operator has entries `0` and `1`, so every `ℚ`-automorphism fixes it. -/
@[simp]
lemma mapMatrix_shiftOperator (d : ℕ) [NeZero d] (g : ComplexGaloisAutomorphism) :
    (shiftOperator d).map g = shiftOperator d := by
  ext i j
  simp only [Matrix.map_apply, shiftOperator]
  split_ifs <;> simp

/-- The phase operator is diagonal in the powers of `ω_d`, so `g` raises it to the power
`k_g`. -/
@[simp]
lemma mapMatrix_phaseOperator (d : ℕ) [NeZero d] (g : ComplexGaloisAutomorphism) :
    (phaseOperator d).map g = phaseOperator d ^ galoisExponent d g := by
  rw [phaseOperator, Matrix.diagonal_pow, Matrix.diagonal_map (by simp)]
  congr 1
  funext j
  simp only [Pi.pow_apply]
  rw [map_pow, map_standardRoot, ← pow_mul, ← pow_mul, Nat.mul_comm]

/-! ### The matrix `H_g` and the action on displacement operators

The diagonal matrix `H_g` fixes the first phase-space coordinate and multiplies the second by
`k_g`.  Applying the generator calculations to integer-indexed displacements proves the
displacement part of [AFK25, Theorem 3.7, `thm:GalActOnClifford`]. -/

/-- The matrix `H_g = ![![1, 0], ![0, k]]` of [AFK25, Definition 3.6, `dfn:HgMatrixDefinition`], as
an integer matrix.

The source takes `H_g` in `GL₂(ℤ/d̄ℤ)`. An integer representative is used here because
`integerDisplacement` is indexed by `ℤ²`; `galoisIndexMatrix_det` and `galoisExponent_coprime`
record that its reduction modulo `d̄` is invertible. -/
@[source "AFK25, Definition 3.6, p. 39, dfn:HgMatrixDefinition" (symbol := "H_g")]
def galoisIndexMatrix (k : ℕ) : Mat(2, ℤ) :=
  !![1, 0; 0, (k : ℤ)]

/-- The determinant of `H_g` is `k_g`. -/
@[simp]
lemma galoisIndexMatrix_det (k : ℕ) : (galoisIndexMatrix k).det = (k : ℤ) := by
  simp [galoisIndexMatrix, Matrix.det_fin_two]

/-- `H_g` fixes the first coordinate and multiplies the second by `k`. -/
lemma galoisIndexMatrix_mulVec (k : ℕ) (p : IntPhaseSpace) :
    (galoisIndexMatrix k).mulVec p = ![p 0, (k : ℤ) * p 1] := by
  funext i
  fin_cases i <;>
    simp [galoisIndexMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **[AFK25, Theorem 3.7, `thm:GalActOnClifford`], displacement half.** Entrywise application of a
`ℚ`-automorphism `g`
permutes the integer-indexed displacement operators by the matrix `H_g`:

`g(D_p) = D_{H_g p}`.

Only the phase operator moves: `g` fixes `X` and sends `Z` to `Z^{k_g}`, while the quadratic phase
`ξ_d^{p₀p₁}` picks up the same exponent. This is exactly the phase of the index
`H_g p = (p₀, k_g p₁)`. -/
@[source "AFK25, Theorem 3.7, p. 39, thm:GalActOnClifford (displacement)"]
theorem mapMatrix_integerDisplacement (d : ℕ) [NeZero d] (g : ComplexGaloisAutomorphism)
    (p : IntPhaseSpace) :
    g.mapMatrix (integerDisplacement d p) =
      integerDisplacement d ((galoisIndexMatrix (galoisExponent d g)).mulVec p) := by
  set k := galoisExponent d g with hk
  set a := (intToFin d (p 0)).val with ha
  set b := (intToFin d (p 1)).val with hb
  have hacast : ((a : ℕ) : ZMod d) = ((p 0 : ℤ) : ZMod d) := by rw [ha, intToFin_cast]
  have hbcast : ((b : ℕ) : ZMod d) = ((p 1 : ℤ) : ZMod d) := by rw [hb, intToFin_cast]
  -- The image, computed from the presentation above.
  have hL : g.mapMatrix (integerDisplacement d p) =
      displacementPhase d ^ ((k : ℤ) * (p 0 * p 1)) •
        (shiftOperator d ^ a * phaseOperator d ^ (k * b)) := by
    rw [integerDisplacement_eq_smul d p a b hacast hbcast, mapMatrix_smul,
      map_displacementPhase_zpow, map_mul, map_pow, map_pow]
    simp only [AlgEquiv.mapMatrix_apply]
    rw [mapMatrix_shiftOperator, mapMatrix_phaseOperator, ← hk, ← pow_mul]
  -- The target, computed from the same presentation at the index `H_g p`.
  have hR : integerDisplacement d ((galoisIndexMatrix k).mulVec p) =
      displacementPhase d ^ (p 0 * ((k : ℤ) * p 1)) •
        (shiftOperator d ^ a * phaseOperator d ^ (k * b)) := by
    rw [galoisIndexMatrix_mulVec]
    refine (integerDisplacement_eq_smul d _ a (k * b) ?_ ?_).trans ?_
    · simpa using hacast
    · push_cast
      simpa using congrArg (fun z : ZMod d => (k : ZMod d) * z) hbcast
    · simp
  rw [hL, hR]
  congr 2
  ring

/-! ### The inverse index permutation

Reindexing the displacement expansion of the live candidate by `H_g` requires its inverse
permutation: the coefficient attached to the index `p` in the reindexed sum is the ghost overlap
at `H_g⁻¹ p`, so an integer matrix representing the inverse permutation is needed. Since
`H_g = diag(1, k_g)` and `k_g` is coprime to `d̄`, an inverse is again of the same shape, with
`k_g` replaced by any natural number inverting it modulo `d̄`.
-/

/-- `H_g` has determinant `k_g`, which is coprime to `d̄`. This is the hypothesis under which
`intPhaseSpaceMod_matrix_mulVec_ne_zero` and
`sum_transversal_mulVec_eq_of_respectsResidues` apply to `H_g`. -/
lemma galoisIndexMatrix_det_isCoprime (d : ℕ) [NeZero d] (g : ComplexGaloisAutomorphism) :
    IsCoprime ((galoisIndexMatrix (galoisExponent d g)).det) (dbar d : ℤ) := by
  rw [galoisIndexMatrix_det]
  exact Nat.isCoprime_iff_coprime.mpr (galoisExponent_coprime d g)

/-- A natural number inverting `k_g` modulo `d̄`, chosen as the canonical representative of the
inverse in `ZMod d̄`. -/
def galoisExponentInv (d : ℕ) [NeZero d] (g : ComplexGaloisAutomorphism) : ℕ :=
  ((galoisExponent d g : ZMod (dbar d))⁻¹).val

/-- The defining property of `galoisExponentInv`: `k_g k_g' ≡ 1 (mod d̄)`. -/
lemma galoisExponent_mul_galoisExponentInv (d : ℕ) [NeZero d] (g : ComplexGaloisAutomorphism) :
    ((galoisExponent d g : ℕ) : ZMod (dbar d)) * ((galoisExponentInv d g : ℕ) : ZMod (dbar d))
      = 1 := by
  rw [galoisExponentInv, ZMod.natCast_val, ZMod.cast_id]
  exact ZMod.coe_mul_inv_eq_one _ (galoisExponent_coprime d g)

/-- The inverse exponent is coprime to `d̄` as well, being a unit modulo `d̄`. -/
lemma galoisExponentInv_coprime (d : ℕ) [NeZero d] (g : ComplexGaloisAutomorphism) :
    Nat.Coprime (galoisExponentInv d g) (dbar d) := by
  refine (ZMod.isUnit_iff_coprime _ _).mp
    (IsUnit.of_mul_eq_one ((galoisExponent d g : ℕ) : ZMod (dbar d)) ?_)
  rw [mul_comm]
  exact galoisExponent_mul_galoisExponentInv d g

/-- **The inverse index matrix** `H_g⁻¹ = ![![1, 0], ![0, k_g']]`, an integer matrix inverting
`H_g` modulo `d̄`. -/
def galoisInverseIndexMatrix (d : ℕ) [NeZero d] (g : ComplexGaloisAutomorphism) :
    Mat(2, ℤ) :=
  galoisIndexMatrix (galoisExponentInv d g)

/-- The inverse index matrix also has determinant coprime to `d̄`, so it too preserves the nonzero
phase-space residues. -/
lemma galoisInverseIndexMatrix_det_isCoprime (d : ℕ) [NeZero d]
    (g : ComplexGaloisAutomorphism) :
    IsCoprime ((galoisInverseIndexMatrix d g).det) (dbar d : ℤ) := by
  rw [galoisInverseIndexMatrix, galoisIndexMatrix_det]
  exact Nat.isCoprime_iff_coprime.mpr (galoisExponentInv_coprime d g)

/-- `H_g⁻¹` inverts `H_g` on phase space modulo `d̄`. Only a congruence is available, not an
equality of integer vectors: `k_g k_g'` is `1` modulo `d̄`, not on the nose. -/
lemma galoisInverseIndexMatrix_mulVec_mulVec (d : ℕ) [NeZero d]
    (g : ComplexGaloisAutomorphism) (p : IntPhaseSpace) :
    intPhaseSpaceMod (dbar d)
        (Matrix.mulVec (galoisInverseIndexMatrix d g)
          (Matrix.mulVec (galoisIndexMatrix (galoisExponent d g)) p)) =
      intPhaseSpaceMod (dbar d) p := by
  rw [galoisInverseIndexMatrix, galoisIndexMatrix_mulVec, galoisIndexMatrix_mulVec]
  funext i
  fin_cases i
  · simp [intPhaseSpaceMod]
  · have h := galoisExponent_mul_galoisExponentInv d g
    simp only [intPhaseSpaceMod, Matrix.cons_val_one, Fin.mk_one]
    push_cast
    calc ((galoisExponentInv d g : ℕ) : ZMod (dbar d)) *
          (((galoisExponent d g : ℕ) : ZMod (dbar d)) * (p 1 : ZMod (dbar d)))
        = (((galoisExponent d g : ℕ) : ZMod (dbar d)) *
            ((galoisExponentInv d g : ℕ) : ZMod (dbar d))) * (p 1 : ZMod (dbar d)) := by ring
      _ = (p 1 : ZMod (dbar d)) := by rw [h, one_mul]

end SIC

end
