/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.LinearAlgebra.UnitaryGroup
import SICs.Quantum.PhaseSpace
import SICs.Quantum.DisplacementBasis
import SICs.Quantum.Projectors

/-!
# Integer-indexed Weyl--Heisenberg displacements

Integer displacement multiplication, adjoints, parity-Hermiticity, and representative-change
phases.

This file restores the phase in `D_p` for arbitrary integer indices, following
[AFK25, Section 3.1, equations (3.1) and (3.3)]. The multiplication, adjoint, parity-Hermitian
and representative-change laws include the even-dimensional signs. Integer and residue indices,
canonical representatives, and their symplectic arithmetic come from `SICs.Quantum.PhaseSpace`.

The proofs reduce to the canonical displacement algebra in `SICs.Quantum.WeylHeisenberg`.
The difference between integer and canonical exponents is divisible by `d`; keeping its
parity gives the required powers of `ξ_d`.

Transversal displacement sums are developed in `SICs.Quantum.DisplacementSums`.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### Integer-indexed displacement operators

Restoring integer exponents to `displacementOperator` produces the source's `ℤ²`-indexed
displacement operators `D_p`. The accompanying phase laws make changes of representatives and
adjoints exact in even dimensions. -/

/-- The integer-indexed form of `displacementOperator`, restoring the source indexing `p ∈ ℤ²`.

`displacementOperator` uses canonical `Fin d` representatives. The scalar here restores the
integer exponent `ξ_d^(p₁p₂)` and therefore records exactly the representative-change phase that
is essential in even dimensions. -/
noncomputable def integerDisplacement (d : ℕ) [NeZero d] (p : IntPhaseSpace) :
    Mat(d, ℂ) :=
  let q := intPhaseSpaceToFin d p
  (displacementPhase d) ^ (p 0 * p 1 - (q.1.val : ℤ) * q.2.val) • displacementOperator d q

/-- `integerDisplacement` written with arbitrary natural exponents representing the two
coordinates modulo `d`.

The quadratic phase carries the *integer* exponent `p₀p₁`, which is what makes this presentation
usable: only the operator exponents may be reduced modulo `d`, and reducing the phase as well
would lose the sign `ξ_d^d = -1` of even dimensions. -/
lemma integerDisplacement_eq_smul (d : ℕ) [NeZero d] (p : IntPhaseSpace) (a b : ℕ)
    (ha : ((a : ℕ) : ZMod d) = ((p 0 : ℤ) : ZMod d))
    (hb : ((b : ℕ) : ZMod d) = ((p 1 : ℤ) : ZMod d)) :
    integerDisplacement d p =
      displacementPhase d ^ (p 0 * p 1) • (shiftOperator d ^ a * phaseOperator d ^ b) := by
  have hxi : displacementPhase d ≠ 0 := by simp [displacementPhase]
  have hX : shiftOperator d ^ (intToFin d (p 0)).val = shiftOperator d ^ a :=
    pow_eq_pow_of_modEq
      ((ZMod.natCast_eq_natCast_iff _ _ _).mp (by rw [intToFin_cast, ← ha])) (shiftOperator_pow_d d)
  have hZ : phaseOperator d ^ (intToFin d (p 1)).val = phaseOperator d ^ b :=
    pow_eq_pow_of_modEq
      ((ZMod.natCast_eq_natCast_iff _ _ _).mp (by rw [intToFin_cast, ← hb])) (phaseOperator_pow_d d)
  simp only [integerDisplacement, intPhaseSpaceToFin, displacementOperator]
  rw [hX, hZ, smul_smul, ← zpow_natCast (displacementPhase d) _, ← zpow_add₀ hxi]
  congr 2
  push_cast
  ring

/-- On canonical nonnegative representatives, `integerDisplacement` agrees with
`displacementOperator`. -/
@[simp]
lemma integerDisplacement_finPhaseSpaceToInt (d : ℕ) [NeZero d]
    (p : Fin d × Fin d) :
    integerDisplacement d (finPhaseSpaceToInt p) = displacementOperator d p := by
  simp only [integerDisplacement]
  rw [intPhaseSpaceToFin_finPhaseSpaceToInt]
  simp [finPhaseSpaceToInt]

/-- The displacement operator of the origin is the identity. -/
@[simp]
lemma integerDisplacement_zero (d : ℕ) [NeZero d] :
    integerDisplacement d 0 = (1 : Mat(d, ℂ)) := by
  simp [integerDisplacement, intPhaseSpaceToFin, intToFin]

/-- A nonzero integer residue class has a traceless displacement operator. -/
lemma trace_integerDisplacement_of_mod_ne_zero (d : ℕ) [NeZero d]
    (p : IntPhaseSpace) (hp : intPhaseSpaceMod d p ≠ 0) :
    (integerDisplacement d p).trace = 0 := by
  simp only [integerDisplacement, Matrix.trace_smul]
  rw [trace_displacementOperator]
  rw [ite_eq_right]
  · simp
  · rwa [intPhaseSpaceToFin_eq_zero_iff]

/-- The phase introduced by taking the adjoint of `D_{-p}` agrees with the parity-conjugation
phase of `D_p`. -/
private lemma D_adjoint_phase_eq_parity_phase (d : ℕ) [NeZero d]
    (p : Fin d × Fin d) :
    (displacementMulPhase d (-p) p)⁻¹ = displacementParityPhase d p := by
  have hneg :
      (standardRoot d ^ ((-p.2) * p.1 : Fin d).val)⁻¹ =
        standardRoot d ^ (p.1.val * p.2.val) := by
    rw [show (-p.2) * p.1 = -(p.1 * p.2) by simp [mul_comm]]
    change (omegaFin d (-(p.1 * p.2)))⁻¹ = _
    rw [omegaFin_neg, inv_inv, ← omega_pow_mul_eq_omegaFin]
  have hxi :
      standardRoot d ^ (p.1.val * p.2.val) =
        displacementPhase d ^ (p.1.val * p.2.val) * displacementPhase d ^ (p.1.val * p.2.val) := by
    rw [← mul_pow, ← pow_two, displacementPhase_sq]
  simp only [displacementMulPhase, displacementParityPhase, Prod.fst_neg, Prod.snd_neg,
    neg_add_cancel, Fin.val_zero, zero_mul, pow_zero, inv_one, mul_one, mul_inv_rev]
  rw [hneg, hxi]
  have hx : displacementPhase d ^ (p.1.val * p.2.val) ≠ 0 := pow_ne_zero _ (by
    simpa only [ne_eq, displacementPhase] using neg_ne_zero.mpr (Complex.exp_ne_zero _))
  field_simp

/-- Every canonically indexed displacement operator is parity-Hermitian. -/
private lemma displacementOperator_isPHermitian (d : ℕ) [NeZero d] (p : Fin d × Fin d) :
    IsPHermitian (displacementOperator d p) := by
  unfold IsPHermitian
  rw [conjTranspose_displacementOperator, parityOperator_conjugates_displacementOperator,
    D_adjoint_phase_eq_parity_phase]
  rfl

/-- The exponent correcting a canonical displacement representative is divisible by `d`. -/
private lemma integerDisplacement_phase_dvd {d : ℕ} [NeZero d]
    (p : IntPhaseSpace) :
    (d : ℤ) ∣ p 0 * p 1 -
      ((intPhaseSpaceToFin d p).1.val : ℤ) *
        (intPhaseSpaceToFin d p).2.val := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ d).mp
  rw [Int.cast_sub, Int.cast_mul, Int.cast_mul]
  simp only [Int.cast_natCast]
  change (p 0 : ZMod d) * (p 1 : ZMod d) -
    ((intToFin d (p 0)).val : ZMod d) *
      ((intToFin d (p 1)).val : ZMod d) = 0
  rw [intToFin_cast, intToFin_cast]
  ring

/-- The `d`th power of `ξ_d` is self-adjoint (indeed, it is a sign). -/
private lemma displacementPhase_pow_d_isSelfAdjoint (d : ℕ) [NeZero d] :
    IsSelfAdjoint (displacementPhase d ^ d) := by
  have hsq : (displacementPhase d ^ d) ^ 2 = 1 := by
    rw [← pow_mul, show d * 2 = 2 * d by omega, displacementPhase_pow_two_d]
  rcases sq_eq_one_iff.mp hsq with h | h
  · rw [h]
    exact IsSelfAdjoint.one ℂ
  · rw [h]
    exact (IsSelfAdjoint.one ℂ).neg

/-- The representative-correction phase in an integer-indexed displacement is self-adjoint. -/
private lemma integerDisplacement_phase_isSelfAdjoint {d : ℕ} [NeZero d]
    (p : IntPhaseSpace) :
    IsSelfAdjoint
      ((displacementPhase d) ^ (p 0 * p 1 -
        ((intPhaseSpaceToFin d p).1.val : ℤ) *
          (intPhaseSpaceToFin d p).2.val)) := by
  rcases integerDisplacement_phase_dvd (d := d) p with ⟨k, hk⟩
  rw [hk, zpow_mul, zpow_natCast]
  exact (displacementPhase_pow_d_isSelfAdjoint d).zpow₀ k

/-- Every integer-indexed displacement operator is parity-Hermitian. -/
lemma integerDisplacement_isPHermitian (d : ℕ) [NeZero d]
    (p : IntPhaseSpace) : IsPHermitian (integerDisplacement d p) := by
  unfold integerDisplacement
  exact (displacementOperator_isPHermitian d (intPhaseSpaceToFin d p)).smul
    (integerDisplacement_phase_isSelfAdjoint p)

/-- **The adjoint of an integer-indexed displacement operator is the oppositely indexed
displacement operator**, with no phase correction: `D_p† = D_{-p}` [AFK25, equation (3.2)].

As with `mapMatrix_integerDisplacement` this is exact only for the integer indexing: on
the canonical `Fin d` representatives (`conjTranspose_displacementOperator`) the same identity
carries the representative-change phase `displacementParityPhase`, which is `-1` for some indices
in even dimensions. The proof combines parity-Hermiticity with the exact parity conjugation law
`parityOperator_conjugates_displacementOperator`; the two phases cancel identically once the index
is negated in `ℤ²` rather than in `Fin d`. -/
theorem conjTranspose_integerDisplacement (d : ℕ) [NeZero d] (p : IntPhaseSpace) :
    (integerDisplacement d p).conjTranspose = integerDisplacement d (-p) := by
  have hxi : displacementPhase d ≠ 0 := by simp [displacementPhase]
  have h : (integerDisplacement d p).conjTranspose =
      parityOperator d * integerDisplacement d p * (parityOperator d).conjTranspose :=
    integerDisplacement_isPHermitian d p
  rw [h, integerDisplacement, Matrix.mul_smul, Matrix.smul_mul,
    parityOperator_conjugates_displacementOperator,
    integerDisplacement, intPhaseSpaceToFin_neg, smul_smul]
  congr 1
  simp only [displacementParityPhase]
  rw [← zpow_natCast (displacementPhase d)
      ((intPhaseSpaceToFin d p).1.val * (intPhaseSpaceToFin d p).2.val),
    ← zpow_natCast (displacementPhase d)
      ((-(intPhaseSpaceToFin d p).1).val * (-(intPhaseSpaceToFin d p).2).val),
    ← zpow_neg, ← zpow_add₀ hxi, ← zpow_add₀ hxi]
  congr 1
  simp only [Pi.neg_apply]
  push_cast
  ring

/-! ### Symplectic multiplication

The integral symplectic form records the exact phase in the integer displacement product
of [AFK25, equation (3.3)]. Reduction to canonical representatives proves the identity. -/


/-- Integer lifts of Weyl--Heisenberg displacement operators multiply with the symplectic `ξ_d`
phase:

$$D_{\mathbf p} D_{\mathbf q} = \xi_d^{\langle \mathbf p, \mathbf q\rangle}
  D_{\mathbf p + \mathbf q}, \qquad \mathbf p, \mathbf q \in \mathbb Z^2.$$

This is [AFK25, equation (3.3)], the second row of the unlabelled display of
displacement-operator identities in Section 3.1, whose first row `D_p† = D_{-p}` is cited at
`conjTranspose_integerDisplacement`. The proof accounts for the parity-dependent choice of
representatives in `Fin d`. -/
lemma integerDisplacement_mul (d : ℕ) [NeZero d] (p q : IntPhaseSpace) :
    integerDisplacement d p * integerDisplacement d q =
      (displacementPhase d) ^ intSymplecticForm p q • integerDisplacement d (p + q) := by
  let P := intPhaseSpaceToFin d p
  let Q := intPhaseSpaceToFin d q
  have hfin : intPhaseSpaceToFin d (p + q) = (P.1 + Q.1, P.2 + Q.2) := by
    apply Prod.ext
    · apply (ZMod.finEquiv d).injective
      simp [P, Q, intPhaseSpaceToFin, intToFin]
    · apply (ZMod.finEquiv d).injective
      simp [P, Q, intPhaseSpaceToFin, intToFin]
  have hD : displacementMulPhase d P Q =
      displacementPhase d ^ ((P.1.val : ℤ) * P.2.val + (Q.1.val : ℤ) * Q.2.val +
        2 * ((P.2 * Q.1 : Fin d).val : ℤ) -
        ((P.1 + Q.1).val : ℤ) * (P.2 + Q.2).val) := by
    rw [displacementMulPhase, ← displacementPhase_sq]
    change displacementPhase d ^ ((P.1.val * P.2.val : ℕ) : ℤ) *
        displacementPhase d ^ ((Q.1.val * Q.2.val : ℕ) : ℤ) *
        (displacementPhase d ^ (2 : ℤ)) ^ (((P.2 * Q.1 : Fin d).val : ℕ) : ℤ) *
        (displacementPhase d ^ (((P.1 + Q.1).val * (P.2 + Q.2).val : ℕ) : ℤ))⁻¹ = _
    rw [← zpow_mul, ← zpow_neg, ← zpow_add₀ (displacementPhase_ne_zero d),
      ← zpow_add₀ (displacementPhase_ne_zero d), ← zpow_add₀ (displacementPhase_ne_zero d)]
    congr 1
  simp only [integerDisplacement, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    displacementOperator_mul_displacementOperator]
  rw [show intPhaseSpaceToFin d p = P from rfl,
    show intPhaseSpaceToFin d q = Q from rfl, hfin, hD]
  simp only [Pi.add_apply,
    ← zpow_add₀ (displacementPhase_ne_zero d)]
  congr 1
  apply displacementPhase_zpow_eq_of_dbar_dvd_sub
  have hdvd : (d : ℤ) ∣ ((P.2 * Q.1 : Fin d).val : ℤ) - p 1 * q 0 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ d).mp
    rw [Int.cast_sub]
    push_cast
    change (((P.2 * Q.1 : Fin d).val : ZMod d) -
      (p 1 : ZMod d) * (q 0 : ZMod d)) = 0
    have hval : (((P.2 * Q.1 : Fin d).val : ZMod d)) =
        (P.2 : ZMod d) * (Q.1 : ZMod d) := by
      rw [Fin.val_mul, ZMod.natCast_mod, Nat.cast_mul]
    rw [hval]
    change ((P.2.val : ZMod d) * (Q.1.val : ZMod d) -
      (p 1 : ZMod d) * (q 0 : ZMod d)) = 0
    simp [P, Q, intPhaseSpaceToFin]
  obtain ⟨k, hk⟩ := hdvd
  have hdbar : (dbar d : ℤ) ∣ 2 * (d : ℤ) := by
    exact_mod_cast dbar_dvd_two_mul d
  obtain ⟨m, hm⟩ := hdbar
  refine ⟨m * k, ?_⟩
  simp only [intSymplecticForm]
  calc
    _ = 2 * (((P.2 * Q.1 : Fin d).val : ℤ) - p 1 * q 0) := by ring
    _ = 2 * ((d : ℤ) * k) := by rw [hk]
    _ = (2 * (d : ℤ)) * k := by ring
    _ = (dbar d : ℤ) * (m * k) := by rw [hm]; ring

/-- Every integer displacement operator is nonzero; `integerDisplacement_mul` gives
`D_p D_{-p} = 1`. -/
theorem integerDisplacement_ne_zero {d : ℕ} [NeZero d] (p : IntPhaseSpace) :
    integerDisplacement d p ≠ 0 := by
  apply left_ne_zero_of_mul_eq_one (b := integerDisplacement d (-p))
  simpa [intSymplecticForm, mul_comm] using integerDisplacement_mul d p (-p)

/-! ### Changes of representatives

Changing a displacement representative contributes a symplectic phase. Divisibility modulo
`dbar d` makes this phase well defined, including in even dimensions. -/

/-- Before reducing its phase modulo `dbar d`, changing an integer representative multiplies its
displacement operator by the corresponding difference of quadratic exponents. -/
private lemma integerDisplacement_eq_phase_smul {d : ℕ} [NeZero d]
    {p p' : IntPhaseSpace} (h : intPhaseSpaceMod d p' = intPhaseSpaceMod d p) :
    integerDisplacement d p' =
      (displacementPhase d) ^ (p' 0 * p' 1 - p 0 * p 1) • integerDisplacement d p := by
  have hq := intPhaseSpaceToFin_eq_of_mod_eq h
  simp only [integerDisplacement]
  rw [hq, smul_smul]
  congr 1
  rw [← zpow_add₀ (by simp [displacementPhase])]
  congr 1
  ring

/-- For congruent integer indices, the difference between the quadratic displacement phase and
the negative symplectic representative-change phase is divisible by `dbar d`. -/
private lemma dbar_dvd_representativeChangeExponent {d : ℕ}
    {p p' : IntPhaseSpace} (h : intPhaseSpaceMod d p' = intPhaseSpaceMod d p) :
    (dbar d : ℤ) ∣
      (p' 0 * p' 1 - p 0 * p 1) + intSymplecticForm p' p := by
  obtain ⟨q, rfl⟩ := exists_eq_add_smul_of_intPhaseSpaceMod_eq d h
  by_cases hd : d % 2 = 1
  · rw [dbar, ite_eq_left hd]
    refine ⟨q 1 * (2 * p 0 + (d : ℤ) * q 0), ?_⟩
    simp only [intSymplecticForm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · have hd₀ : d % 2 = 0 := by omega
    obtain ⟨k, hk⟩ := (Nat.dvd_iff_mod_eq_zero.mpr hd₀ : 2 ∣ d)
    rw [dbar, ite_eq_right hd]
    refine ⟨q 1 * (p 0 + (k : ℤ) * q 0), ?_⟩
    simp only [intSymplecticForm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast [hk]
    ring

/-- Changing the integer representative of a displacement index contributes the inverse of the
symplectic phase between the two representatives.

This congruence-based form is convenient for combining displacement operators with the
quasiperiodic normalized ghost overlaps. -/
theorem integerDisplacement_change_representative {d : ℕ} [NeZero d]
    {p p' : IntPhaseSpace} (h : intPhaseSpaceMod d p' = intPhaseSpaceMod d p) :
    integerDisplacement d p' =
      (displacementPhase d) ^ (-intSymplecticForm p' p) • integerDisplacement d p := by
  rw [integerDisplacement_eq_phase_smul h]
  congr 1
  obtain ⟨k, hk⟩ := dbar_dvd_representativeChangeExponent h
  have hexp : p' 0 * p' 1 - p 0 * p 1 =
      -intSymplecticForm p' p + (dbar d : ℤ) * k := by
    linear_combination hk
  rw [hexp, zpow_add₀ (by simp [displacementPhase]), _root_.zpow_mul, zpow_natCast,
    displacementPhase_pow_dbar, one_zpow, mul_one]

end SIC

end
