/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import SICs.Quantum.Projectors

/-!
# Equiangular projectors and the structure of r-SICs

Equiangular rank-r projectors, independence, spanning, tightness, and trace formulas.

This file formalizes [AFK25, Definition 1.2, `def:equiangularcond`, and Theorem 1.7,
`thm:rsicbsc`]. The equiangular Gram relations and trace pairings give linear independence
of the projectors and then spanning of the matrix space. Their sum pairs with each
projector as a scalar identity does, proving tightness; taking traces determines the
common off-diagonal overlap. No Weyl--Heisenberg covariance is assumed.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

variable {d : ℕ} [NeZero d]

/-! ### r-SICs

An `r`-SIC is recorded as a distinct equiangular family of rank-`r` Hermitian projectors.  The
Weyl--Heisenberg specialization is generated from one fiducial by displacement conjugation. -/

/-- An r-SIC in dimension d is a family {P_p : p ∈ (Fin d)²} of d² distinct rank-r
    H-projectors that are equiangular: Tr(P_p P_q) is constant for p ≠ q.

    The type `Fin d × Fin d` is used only as a canonical index type with `d²`
    elements; this definition does not impose Weyl–Heisenberg covariance.  See
    [AFK25, Definition 1.2, `def:equiangularcond`]. -/
@[source "AFK25, Definition 1.2, p. 3, def:equiangularcond"]
structure IsRSIC (r : ℕ) (P : Fin d × Fin d → Mat(d, ℂ)) : Prop where
  /-- Each P_p is a rank-r H-projector. -/
  isRankRHProjector : ∀ p, IsRankRHProjector r (P p)
  /-- Equiangularity: all off-diagonal traces are equal. -/
  equiangular : ∃ α : ℂ, ∀ p q : Fin d × Fin d, p ≠ q → (P p * P q).trace = α
  /-- The projectors are distinct. -/
  distinct : Function.Injective P

/-! ### Main structural theorems

The equiangular Gram relations and trace pairings give linear independence, spanning,
tightness, and the trace formulas of [AFK25, Theorem 1.7, `thm:rsicbsc`].
Weyl--Heisenberg fiducial criteria are developed in `SICs.Quantum.Fiducials`. -/

omit [NeZero d] in
/-- A rank-zero Hermitian projector is the zero matrix. -/
private lemma rankRHProjector_eq_zero_of_rank_eq_zero {r : ℕ}
    {P : Mat(d, ℂ)} (hP : IsRankRHProjector r P) (hr : r = 0) : P = 0 := by
  apply Matrix.toLin'.injective
  rw [map_zero, ← LinearMap.range_eq_bot, ← Submodule.finrank_eq_zero]
  change P.rank = 0
  exact hP.rank_eq.trans hr

omit [NeZero d] in
open scoped ComplexOrder in
/-- Two rank-`r` Hermitian projectors whose product has trace `r` are equal. -/
private lemma rankRHProjector_eq_of_trace_mul_eq_rank {r : ℕ}
    {P Q : Mat(d, ℂ)}
    (hP : IsRankRHProjector r P) (hQ : IsRankRHProjector r Q)
    (htrace : (P * Q).trace = (r : ℂ)) : P = Q := by
  apply sub_eq_zero.mp
  apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
  have hherm : (P - Q).conjTranspose = P - Q := by
    simp [hP.isHProjector.hermitian.eq, hQ.isHProjector.hermitian.eq]
  rw [hherm]
  have hPmul : P * P = P := by simpa [pow_two] using hP.isHProjector.idempotent
  have hQmul : Q * Q = Q := by simpa [pow_two] using hQ.isHProjector.idempotent
  rw [show (P - Q) * (P - Q) = P * P - P * Q - Q * P + Q * Q by noncomm_ring]
  simp only [Matrix.trace_add, Matrix.trace_sub, hPmul, hQmul]
  rw [trace_eq_rank_of_idempotent P hP.isHProjector.idempotent,
    trace_eq_rank_of_idempotent Q hQ.isHProjector.idempotent,
    hP.rank_eq, hQ.rank_eq, htrace, Matrix.trace_mul_comm Q P, htrace]
  ring

/-- In dimension greater than one, the `r`-SIC index type has an element distinct from
the origin. -/
private lemma rsic_index_exists_ne (hd : 1 < d) :
    ∃ q : Fin d × Fin d, q ≠ ((0, 0) : Fin d × Fin d) := by
  apply Fintype.exists_ne_of_one_lt_card
  simp only [Fintype.card_prod, Fintype.card_fin]
  nlinarith

/-- The common rank of an `r`-SIC in dimension greater than one is positive.

The distinctness condition rules out the rank-zero family, since a rank-zero Hermitian
projector is the zero matrix. -/
theorem rsic_rank_pos (r : ℕ) (hd : 1 < d)
    (P : Fin d × Fin d → Mat(d, ℂ)) (hrsic : IsRSIC r P) : 0 < r := by
  apply Nat.pos_of_ne_zero
  intro hr
  obtain ⟨q, hq⟩ := rsic_index_exists_ne hd
  have hzero : ∀ p, P p = 0 := fun p =>
    rankRHProjector_eq_zero_of_rank_eq_zero (hrsic.isRankRHProjector p) hr
  apply hq
  apply hrsic.distinct
  rw [hzero q, hzero (0, 0)]

/-- The common off-diagonal trace of an `r`-SIC cannot equal the projector rank. -/
private lemma rsic_equiangular_value_ne_rank (r : ℕ) (hd : 1 < d)
    (P : Fin d × Fin d → Mat(d, ℂ))
    (hrsic : IsRSIC r P) (α : ℂ)
    (hα : ∀ p q : Fin d × Fin d, p ≠ q → (P p * P q).trace = α) :
    α ≠ (r : ℂ) := by
  intro hαr
  obtain ⟨q, hq⟩ := rsic_index_exists_ne hd
  have heq : P (0, 0) = P q := rankRHProjector_eq_of_trace_mul_eq_rank
    (hrsic.isRankRHProjector (0, 0)) (hrsic.isRankRHProjector q) (by
      rw [hα (0, 0) q hq.symm, hαr])
  exact hq (hrsic.distinct heq).symm

omit [NeZero d] in
/-- Evaluates the pairing of one `r`-SIC projector with an arbitrary weighted sum of
the family using the diagonal and off-diagonal Gram values. -/
private lemma rsic_weighted_trace_sum (r : ℕ)
    (P : Fin d × Fin d → Mat(d, ℂ)) (hrsic : IsRSIC r P)
    (α : ℂ) (hα : ∀ p q : Fin d × Fin d, p ≠ q → (P p * P q).trace = α)
    (a : Fin d × Fin d → ℂ) (k : Fin d × Fin d) :
    ∑ p : Fin d × Fin d, a p * (P k * P p).trace =
      a k * (r : ℂ) + ((∑ p : Fin d × Fin d, a p) - a k) * α := by
  have htrace (p : Fin d × Fin d) : (P p).trace = (r : ℂ) :=
    (hrsic.isRankRHProjector p).trace_eq
  have hgram (p : Fin d × Fin d) :
      (P k * P p).trace = if k = p then (r : ℂ) else α := by
    split_ifs with hkp
    · subst p
      rw [← sq, (hrsic.isRankRHProjector k).isHProjector.idempotent, htrace]
    · exact hα k p hkp
  rw [← Finset.add_sum_erase Finset.univ
    (fun p => a p * (P k * P p).trace) (Finset.mem_univ k)]
  rw [hgram k, ite_eq_left rfl]
  rw [show (∑ p ∈ Finset.univ.erase k, a p * (P k * P p).trace) =
      (∑ p ∈ Finset.univ.erase k, a p) * α by
    calc
      (∑ p ∈ Finset.univ.erase k, a p * (P k * P p).trace) =
          ∑ p ∈ Finset.univ.erase k, a p * α := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [hgram, ite_eq_right (Finset.mem_erase.mp hp).1.symm]
      _ = (∑ p ∈ Finset.univ.erase k, a p) * α := by rw [Finset.sum_mul]]
  have hsplit : a k + ∑ p ∈ Finset.univ.erase k, a p = ∑ p, a p :=
    Finset.add_sum_erase Finset.univ a (Finset.mem_univ k)
  rw [show (∑ p ∈ Finset.univ.erase k, a p) = (∑ p, a p) - a k by
    linear_combination hsplit]

omit [NeZero d] in
/-- Computes the common row sum of the Gram matrix of an equiangular `r`-SIC family. -/
private lemma rsic_trace_sum (r : ℕ)
    (P : Fin d × Fin d → Mat(d, ℂ)) (hrsic : IsRSIC r P)
    (α : ℂ) (hα : ∀ p q : Fin d × Fin d, p ≠ q → (P p * P q).trace = α)
    (k : Fin d × Fin d) :
    ∑ p : Fin d × Fin d, (P k * P p).trace =
      (r : ℂ) + ((d : ℂ) ^ 2 - 1) * α := by
  have h := rsic_weighted_trace_sum r P hrsic α hα (fun _ => 1) k
  simp only [one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, nsmul_eq_mul] at h
  push_cast at h
  simpa [pow_two] using h

/-- The linear-independence conclusion of [AFK25, Theorem 1.7, `thm:rsicbsc`].

For `1 < d`, distinctness excludes ranks zero and `d`. Pairing a linear relation with the
identity and with each projector then forces every coefficient to vanish. -/
@[source "AFK25, Theorem 1.7, p. 6, thm:rsicbsc (basis, independence)"]
theorem rsic_linearIndependent (r : ℕ) (hd : 1 < d)
    (P : Fin d × Fin d → Mat(d, ℂ))
    (hrsic : IsRSIC r P) : LinearIndependent ℂ P := by
  have hrpos := rsic_rank_pos r hd P hrsic
  have htrace (p : Fin d × Fin d) : (P p).trace = (r : ℂ) :=
    (hrsic.isRankRHProjector p).trace_eq
  obtain ⟨α, hα⟩ := hrsic.equiangular
  have hαne := rsic_equiangular_value_ne_rank r hd P hrsic α hα
  rw [Fintype.linearIndependent_iff]
  intro a ha k
  have hatrace : (∑ p : Fin d × Fin d, a p) * (r : ℂ) = 0 := by
    have ht := congrArg Matrix.trace ha
    simp only [Matrix.trace_sum, Matrix.trace_smul, htrace, smul_eq_mul,
      Matrix.trace_zero] at ht
    simpa only [Finset.sum_mul] using ht
  have hasum : ∑ p : Fin d × Fin d, a p = 0 :=
    (mul_eq_zero.mp hatrace).resolve_right (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hrpos))
  have hpair : ∑ p : Fin d × Fin d, a p * (P k * P p).trace = 0 := by
    have hk := congrArg (fun M : Mat(d, ℂ) => (P k * M).trace) ha
    simpa only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
      smul_eq_mul, Matrix.mul_zero, Matrix.trace_zero] using hk
  rw [rsic_weighted_trace_sum r P hrsic α hα, hasum] at hpair
  have hprod : a k * ((r : ℂ) - α) = 0 := by linear_combination hpair
  exact (mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hαne.symm)

/-- The spanning conclusion of [AFK25, Theorem 1.7, `thm:rsicbsc`]. Together with
`rsic_linearIndependent`, this says that an `r`-SIC in dimension greater than one is a
basis of the full matrix algebra. -/
@[source "AFK25, Theorem 1.7, p. 6, thm:rsicbsc (basis, spanning)"]
theorem rsic_span_eq_top (r : ℕ) (hd : 1 < d)
    (P : Fin d × Fin d → Mat(d, ℂ))
    (hrsic : IsRSIC r P) : Submodule.span ℂ (Set.range P) = ⊤ := by
  apply (rsic_linearIndependent r hd P hrsic).span_eq_top_of_card_eq_finrank
  simp only [Fintype.card_prod, Fintype.card_fin, Module.finrank_matrix,
    Module.finrank_self, mul_one]

omit [NeZero d] in
/-- A matrix paired to zero by `trace (P_p A)` for every member of a spanning family is
zero. -/
private lemma eq_zero_of_span_of_trace_mul_eq_zero
    {I : Type*} (P : I → Mat(d, ℂ))
    (hspan : Submodule.span ℂ (Set.range P) = ⊤)
    (A : Mat(d, ℂ)) (hA : ∀ p, (P p * A).trace = 0) : A = 0 := by
  apply Matrix.ext_iff_trace_mul_left.mpr
  have hf := LinearMap.ext_on_range hspan
    (f := (Matrix.traceLinearMap (Fin d) ℂ ℂ).comp (LinearMap.mulRight ℂ A))
    (g := 0) fun p ↦ hA p
  intro X
  simpa using LinearMap.congr_fun hf X

omit [NeZero d] in
/-- If a spanning family pairs with a matrix exactly as it pairs with a scalar
matrix, then the matrix is that scalar matrix. -/
private lemma eq_smul_one_of_span_of_trace_mul_eq_smul_trace
    {I : Type*} (P : I → Mat(d, ℂ))
    (hspan : Submodule.span ℂ (Set.range P) = ⊤)
    (A : Mat(d, ℂ)) (c : ℂ)
    (hA : ∀ p, (P p * A).trace = c * (P p).trace) : A = c • 1 := by
  apply sub_eq_zero.mp
  apply eq_zero_of_span_of_trace_mul_eq_zero P hspan
  intro p
  rw [Matrix.mul_sub, Matrix.trace_sub, hA, Matrix.mul_smul, Matrix.trace_smul,
    Matrix.mul_one]
  simp


/-- The resolution-of-the-identity conclusion of [AFK25, Theorem 1.7, `thm:rsicbsc`].

Unlike the trace formula, this conclusion remains valid in dimension one, so no lower bound
on `d` is needed. -/
@[source "AFK25, Theorem 1.7, p. 6, thm:rsicbsc (resolution of the identity)"]
theorem rsic_sum_eq (r : ℕ)
    (P : Fin d × Fin d → Mat(d, ℂ))
    (hrsic : IsRSIC r P) :
    ∑ p : Fin d × Fin d, P p = (r * d : ℝ) • 1 := by
  by_cases hd : 1 < d
  · have hrpos := rsic_rank_pos r hd P hrsic
    have htrace (p : Fin d × Fin d) : (P p).trace = (r : ℂ) :=
      (hrsic.isRankRHProjector p).trace_eq
    obtain ⟨α, hα⟩ := hrsic.equiangular
    let S := ∑ p : Fin d × Fin d, P p
    let c := ((r : ℂ) + ((d : ℂ) ^ 2 - 1) * α) / (r : ℂ)
    have hrow (k : Fin d × Fin d) :
        (P k * S).trace = (r : ℂ) + ((d : ℂ) ^ 2 - 1) * α := by
      simp only [S, Matrix.mul_sum, Matrix.trace_sum]
      exact rsic_trace_sum r P hrsic α hα k
    have hS : S = c • (1 : Mat(d, ℂ)) := by
      apply eq_smul_one_of_span_of_trace_mul_eq_smul_trace P
        (rsic_span_eq_top r hd P hrsic)
      intro k
      rw [hrow, htrace]
      simp only [c]
      field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hrpos)]
    have htraceS := congrArg Matrix.trace hS
    simp only [S, Matrix.trace_sum, htrace, Finset.sum_const, Finset.card_univ,
      Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Matrix.trace_smul,
      Matrix.trace_one, smul_eq_mul] at htraceS
    push_cast at htraceS
    have hc : c = (r : ℂ) * (d : ℂ) := by
      apply (mul_right_cancel₀ (show (d : ℂ) ≠ 0 by exact_mod_cast NeZero.ne d))
      simpa only [mul_assoc, mul_left_comm, mul_comm] using htraceS.symm
    calc
      ∑ p : Fin d × Fin d, P p = S := rfl
      _ = c • (1 : Mat(d, ℂ)) := hS
      _ = ((r : ℂ) * (d : ℂ)) • (1 : Mat(d, ℂ)) := by rw [hc]
      _ = (r * d : ℝ) • (1 : Mat(d, ℂ)) := by
        ext i j
        simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
        norm_num
  · have hd1 : d = 1 := by
      have hdpos : 0 < d := NeZero.pos d
      omega
    subst d
    rw [Fintype.sum_subsingleton P (0, 0)]
    rw [matrix_fin_one_eq_trace_smul_one (P (0, 0))]
    have htrace : (P (0, 0)).trace = (r : ℂ) :=
      (hrsic.isRankRHProjector (0, 0)).trace_eq
    rw [htrace]
    ext i j
    simp [Complex.real_smul]

/-- The trace-formula conclusion of [AFK25, Theorem 1.7, `thm:rsicbsc`].

    Corollaries:
    - Diagonal: Tr(P_p²) = Tr(P_p) = r ✓
    - Off-diagonal: Tr(P_p P_q) = r(rd-1)/(d²-1) for p ≠ q

    [AFK25] centers and normalizes the projectors to obtain `d²` traceless operators in the
    `(d²-1)`-dimensional traceless subspace. The Lean proof first derives linear independence
    directly from the equiangular Gram relations. Since the `d²` projectors then span the matrix
    algebra, their equal Gram row sums force the resolution of the identity; pairing that identity
    with one projector determines the off-diagonal trace. This argument does not assume WH
    covariance. -/
@[source "AFK25, Theorem 1.7, p. 6, thm:rsicbsc (trace formula)"]
theorem rsic_trace_formula (r : ℕ) (hd : 1 < d)
    (P : Fin d × Fin d → Mat(d, ℂ))
    (hrsic : IsRSIC r P) :
    ∀ p q : Fin d × Fin d,
      (P p * P q).trace =
        if p = q then
          ((r * d * (d - r) : ℝ) / (d^2 - 1) + (r * (r * d - 1) : ℝ) / (d^2 - 1) : ℂ)
        else
          ((r * (r * d - 1) : ℝ) / (d^2 - 1) : ℂ) := by
  have htrace (p : Fin d × Fin d) : (P p).trace = (r : ℂ) :=
    (hrsic.isRankRHProjector p).trace_eq
  obtain ⟨α, hα⟩ := hrsic.equiangular
  have hpair := congrArg
    (fun M : Mat(d, ℂ) => (P (0, 0) * M).trace)
    (rsic_sum_eq r P hrsic)
  simp only [Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul,
    Matrix.mul_one, htrace, Complex.real_smul] at hpair
  rw [rsic_trace_sum r P hrsic α hα] at hpair
  have hden : (d : ℂ) ^ 2 - 1 ≠ 0 := by
    intro hzero
    have hnat : d ^ 2 = 1 := by exact_mod_cast sub_eq_zero.mp hzero
    nlinarith
  have hαformula : α =
      (r : ℂ) * ((r : ℂ) * (d : ℂ) - 1) / ((d : ℂ) ^ 2 - 1) := by
    apply (eq_div_iff hden).2
    push_cast at hpair ⊢
    linear_combination hpair
  intro p q
  split_ifs with hpq
  · subst q
    rw [← sq, (hrsic.isRankRHProjector p).isHProjector.idempotent, htrace]
    push_cast
    field_simp [hden]
    ring
  · rw [hα p q hpq, hαformula]
    push_cast
    rfl

end SIC

end
