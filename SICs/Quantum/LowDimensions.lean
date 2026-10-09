/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Quantum.Fiducials

/-!
# Weyl--Heisenberg SICs in Dimensions One, Two, and Three

Explicit WH fiducials in dimensions `1`, `2`, `3`.

This file supplies the low-dimensional base cases omitted from the real-quadratic construction in
[AFK25], which applies only in dimensions greater than three. The exact fiducial vectors in
dimensions two and three are taken respectively from [4, Appleby (2005), eq. (137), p. 19] and
[4, Appleby (2005), eq. (142), p. 20]. Both occur in Section 8,
“Dimensions 2 to 7: Vectors, Orbits and Stability Groups” (`sec:VectorsOrbitsStability`). That
source uses the same displacement convention
`D_p = (-exp (π i / d))^(p₁ p₂) X^p₁ Z^p₂` as `SICs.Quantum.WeylHeisenberg`.

Dimension one is immediate. In dimension two we use Appleby's exact fiducial, expressed below
as its rank-one projector. In dimension three we take parameter `t = 0` in Appleby's family,
giving the Hesse fiducial vector `(0, 1, -1) / √2`.

## References

- [4, Appleby (2005), eq. (137), p. 19], the exact dimension-two fiducial
- [4, Appleby (2005), eq. (142), p. 20], the dimension-three family `|ψ₃(t)⟩`
- [AFK25, Conjecture 1.3, `conj:zauner`], the statement these dimensions complete
-/

noncomputable section

open Complex Matrix Finset
open scoped MatrixGroups

namespace SIC

/-! ### Dimension one

The unique one-dimensional projector is automatically a Weyl--Heisenberg fiducial because phase
space is a singleton. -/

/-- The unique rank-one projector in dimension one. -/
def fiducialDimOne : Mat(1, ℂ) := 1

/-- `fiducialDimOne` is a Weyl--Heisenberg `1`-SIC fiducial. -/
theorem fiducialDimOne_isFiducial : IsFiducial 1 fiducialDimOne := by
  have hproj : IsRankRHProjector 1 fiducialDimOne := by
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp [fiducialDimOne]
  refine ⟨hproj, {
    isRankRHProjector := ?_
    equiangular := ?_
    distinct := ?_
  }⟩
  · intro p
    have hp : p = ((0, 0) : Fin 1 × Fin 1) := Subsingleton.elim _ _
    rw [hp, WHCovariantFamily_zero]
    exact hproj
  · refine ⟨0, ?_⟩
    intro p q hpq
    exact (hpq (Subsingleton.elim _ _)).elim
  · exact Function.injective_of_subsingleton _

/-! ### Dimension two

Appleby's exact dimension-two fiducial is written as a rank-one projector.  Direct matrix
identities and the three nonzero overlaps verify the fiducial criterion. -/

/-- The positive real number `1 / √3`, represented as `√(1 / 3)` for the
dimension-two fiducial calculations. -/
private noncomputable def dimTwoInvSqrtThree : ℝ := Real.sqrt (1 / 3)

/-- The rank-one projector associated to Appleby's exact dimension-two fiducial

`sqrt ((3 + sqrt 3) / 6) e₀ + exp (π i / 4) sqrt ((3 - sqrt 3) / 6) e₁`.

This is the displayed fiducial `|ψ₂⟩` of [4, Appleby (2005), eq. (137), p. 19]. -/
noncomputable def fiducialDimTwo : Mat(2, ℂ) :=
  (2 : ℂ)⁻¹ •
    !![(1 : ℂ) + dimTwoInvSqrtThree,
        dimTwoInvSqrtThree * (1 - I);
       dimTwoInvSqrtThree * (1 + I),
        (1 : ℂ) - dimTwoInvSqrtThree]

/-- The chosen square-root representative of `1 / 3` is nonnegative. -/
private lemma dimTwoInvSqrtThree_nonneg : 0 ≤ dimTwoInvSqrtThree :=
  Real.sqrt_nonneg _

/-- Squaring the chosen representative `dimTwoInvSqrtThree` gives `1 / 3`. -/
private lemma dimTwoInvSqrtThree_sq : dimTwoInvSqrtThree ^ 2 = (1 / 3 : ℝ) := by
  rw [dimTwoInvSqrtThree, Real.sq_sqrt]
  norm_num

/-- The complex norm of `dimTwoInvSqrtThree` is `(√3)⁻¹`, in the form needed
by the fiducial overlap criterion. -/
private lemma norm_dimTwoInvSqrtThree :
    ‖(dimTwoInvSqrtThree : ℂ)‖ = (Real.sqrt 3)⁻¹ := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg dimTwoInvSqrtThree_nonneg]
  rw [dimTwoInvSqrtThree, show (1 / 3 : ℝ) = (3 : ℝ)⁻¹ by norm_num,
    Real.sqrt_inv]

/-- Appleby's dimension-two fiducial matrix is Hermitian. -/
private lemma fiducialDimTwo_hermitian : fiducialDimTwo.IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [fiducialDimTwo, Matrix.conjTranspose_apply, dimTwoInvSqrtThree]
  all_goals ring

/-- Appleby's dimension-two fiducial matrix is idempotent. -/
private lemma fiducialDimTwo_idempotent : fiducialDimTwo ^ 2 = fiducialDimTwo := by
  have hc : ((dimTwoInvSqrtThree : ℂ) ^ 2) = (1 / 3 : ℂ) := by
    calc
      ((dimTwoInvSqrtThree : ℂ) ^ 2) =
          ((dimTwoInvSqrtThree ^ 2 : ℝ) : ℂ) := by norm_num
      _ = (((1 / 3 : ℝ)) : ℂ) :=
        congrArg ((↑) : ℝ → ℂ) dimTwoInvSqrtThree_sq
      _ = (1 / 3 : ℂ) := by norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fiducialDimTwo, sq, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring_nf at hc ⊢
  all_goals rw [Complex.I_sq, hc]
  all_goals ring

/-- The trace of the dimension-two fiducial projector is one. -/
private lemma fiducialDimTwo_trace : fiducialDimTwo.trace = 1 := by
  simp [fiducialDimTwo, Matrix.trace, Fin.sum_univ_two]
  ring

/-- The dimension-two fiducial projector has rank one. -/
private lemma fiducialDimTwo_rank_one : fiducialDimTwo.rank = 1 := by
  have h := trace_eq_rank_of_idempotent fiducialDimTwo fiducialDimTwo_idempotent
  rw [fiducialDimTwo_trace] at h
  exact_mod_cast h.symm

/-- The dimension-two fiducial combines Hermitian idempotency with rank one. -/
private lemma fiducialDimTwo_isRankOneHProjector :
    IsRankRHProjector 1 fiducialDimTwo :=
  ⟨⟨fiducialDimTwo_hermitian, fiducialDimTwo_idempotent⟩, fiducialDimTwo_rank_one⟩

/-- In dimension two, the standard root of unity `ω₂` is `-1`. -/
private lemma omega_two : standardRoot 2 = -1 := by
  rw [standardRoot]
  norm_num
  ring_nf
  exact Complex.exp_pi_mul_I

/-- In dimension two, the displacement phase `ξ₂` is `-i`. -/
private lemma xi_two : displacementPhase 2 = -I := by
  rw [displacementPhase]
  norm_num
  ring_nf
  rw [show (Real.pi : ℂ) * I * (1 / 2) = (Real.pi : ℂ) / 2 * I by ring,
    Complex.exp_pi_div_two_mul_I]

/-- The dimension-two shift operator swaps the two standard basis vectors. -/
private lemma X_two : shiftOperator 2 = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [shiftOperator]

/-- The dimension-two clock operator has diagonal entries `1` and `-1`. -/
private lemma Z_two : phaseOperator 2 = !![1, 0; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [phaseOperator, omega_two]

/-- The nontrivial dimension-two displacement in both coordinates has the displayed
off-diagonal form. -/
private lemma D_one_one_two :
    displacementOperator 2 ((1 : Fin 2), (1 : Fin 2)) = !![0, I; -I, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [displacementOperator, X_two, Z_two, xi_two]

/-- The overlap of the dimension-two fiducial with the horizontal nonzero
displacement equals `1 / √3`. -/
private lemma overlap_fiducialDimTwo_one_zero :
    overlap fiducialDimTwo ((1 : Fin 2), (0 : Fin 2)) = dimTwoInvSqrtThree := by
  rw [overlap, displacementOperator_one_zero, X_two]
  simp [fiducialDimTwo, Matrix.trace, Matrix.vecMul, dotProduct,
    Matrix.conjTranspose_apply, Fin.sum_univ_two]
  ring

/-- The overlap of the dimension-two fiducial with the vertical nonzero
displacement equals `1 / √3`. -/
private lemma overlap_fiducialDimTwo_zero_one :
    overlap fiducialDimTwo ((0 : Fin 2), (1 : Fin 2)) = dimTwoInvSqrtThree := by
  rw [overlap, displacementOperator_zero_one, Z_two]
  simp [fiducialDimTwo, Matrix.trace, Matrix.vecMul, dotProduct,
    Matrix.conjTranspose_apply, Fin.sum_univ_two]
  ring

/-- The overlap of the dimension-two fiducial with the diagonal nonzero
displacement equals `-1 / √3`. -/
private lemma overlap_fiducialDimTwo_one_one :
    overlap fiducialDimTwo ((1 : Fin 2), (1 : Fin 2)) = -dimTwoInvSqrtThree := by
  rw [overlap, D_one_one_two]
  simp [fiducialDimTwo, Matrix.trace, Matrix.vecMul, dotProduct,
    Matrix.conjTranspose_apply, Fin.sum_univ_two]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `fiducialDimTwo` is a Weyl--Heisenberg `1`-SIC fiducial. -/
theorem fiducialDimTwo_isFiducial : IsFiducial 1 fiducialDimTwo := by
  apply (fiducial_condition 1 fiducialDimTwo fiducialDimTwo_isRankOneHProjector
    (by norm_num) (by norm_num)).2
  intro p hp
  rcases p with ⟨p₁, p₂⟩
  fin_cases p₁ <;> fin_cases p₂
  · exact (hp rfl).elim
  all_goals norm_num at hp ⊢
  · rw [overlap_fiducialDimTwo_zero_one, norm_dimTwoInvSqrtThree]
  · rw [overlap_fiducialDimTwo_one_zero, norm_dimTwoInvSqrtThree]
  · rw [overlap_fiducialDimTwo_one_one, norm_neg, norm_dimTwoInvSqrtThree]

/-! ### Dimension three

The Hesse fiducial at parameter zero gives a particularly simple projector.  Cube-root identities
reduce every nonzero displacement overlap to norm `1/2`. -/

/-- The rank-one projector associated to the Hesse fiducial `(0, 1, -1) / √2`.

This is parameter `t = 0` in the family `|ψ₃(t)⟩ = (e^{-it} e₁ − e^{it} e₂)/√2` displayed in the
dimension-three subsection of [4, Appleby (2005), eq. (142), p. 20]. -/
def fiducialDimThree : Mat(3, ℂ) := fun i j ↦
  if i = 0 then 0
  else if j = 0 then 0
  else if i = j then (1 / 2 : ℂ)
  else -(1 / 2 : ℂ)

/-- The Hesse fiducial matrix is a rank-one Hermitian projector. -/
private lemma fiducialDimThree_isRankOneHProjector :
    IsRankRHProjector 1 fiducialDimThree := by
  have hherm : fiducialDimThree.IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [fiducialDimThree, Matrix.conjTranspose_apply]
  have hidem : fiducialDimThree ^ 2 = fiducialDimThree := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [fiducialDimThree, pow_two, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num
  refine ⟨⟨hherm, hidem⟩, ?_⟩
  have ht := trace_eq_rank_of_idempotent fiducialDimThree hidem
  have htrace : fiducialDimThree.trace = 1 := by
    simp [fiducialDimThree, Matrix.trace, Matrix.diag, Fin.sum_univ_succ]
  rw [htrace] at ht
  exact_mod_cast ht.symm

/-- The real normalization in the rank-one overlap criterion specializes to `1 / 2`
when `d = 3` and `r = 1`. -/
private lemma sqrt_quarter :
    Real.sqrt ((((1 : ℕ) : ℝ) * (((3 : ℕ) : ℝ) - ((1 : ℕ) : ℝ))) /
      (((3 : ℕ) : ℝ)^2 - 1)) = 1 / 2 := by
  have hroot : Real.sqrt (4 : ℝ) = 2 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  norm_num [hroot]

/-- The conjugate primitive cube root of unity satisfies `ω̅ + ω̅² = -1`. -/
private lemma dimThree_omega_star_sum :
    (starRingEnd ℂ) (standardRoot 3) + (starRingEnd ℂ) (standardRoot 3) ^ 2 = -1 := by
  have hw3 : standardRoot 3 ^ 3 = 1 := standardRoot_pow_d 3
  have hwne : standardRoot 3 ≠ 1 := (standardRoot_isPrimitiveRoot 3).ne_one (by norm_num)
  have hfac : (standardRoot 3 - 1) * (standardRoot 3 ^ 2 + standardRoot 3 + 1) = 0 := by
    calc
      (standardRoot 3 - 1) * (standardRoot 3 ^ 2 + standardRoot 3 + 1) =
          standardRoot 3 ^ 3 - 1 := by ring
      _ = 0 := sub_eq_zero.mpr hw3
  have hpoly : standardRoot 3 ^ 2 + standardRoot 3 + 1 = 0 := by
    rcases mul_eq_zero.mp hfac with h | h
    · exact (hwne (sub_eq_zero.mp h)).elim
    · exact h
  have hstar := congrArg (starRingEnd ℂ) hpoly
  simp only [map_add, map_pow, map_one, map_zero] at hstar
  linear_combination hstar

/-- A multiplication-expanded form of `dimThree_omega_star_sum`. -/
private lemma dimThree_omega_star_mul_sum :
    (starRingEnd ℂ) (standardRoot 3) +
        (starRingEnd ℂ) (standardRoot 3) * (starRingEnd ℂ) (standardRoot 3) = -1 := by
  simpa [pow_two] using dimThree_omega_star_sum

/-- The conjugate cube-root identity in the degree-two and degree-four form arising
in a dimension-three overlap calculation. -/
private lemma dimThree_omega_star_mul_four_sum :
    (starRingEnd ℂ) (standardRoot 3) * (starRingEnd ℂ) (standardRoot 3) +
        (starRingEnd ℂ) (standardRoot 3) * (starRingEnd ℂ) (standardRoot 3) *
          ((starRingEnd ℂ) (standardRoot 3) * (starRingEnd ℂ) (standardRoot 3)) = -1 := by
  have hz3 := congrArg (starRingEnd ℂ) (standardRoot_pow_d 3)
  simp only [map_pow, map_one] at hz3
  calc
    (starRingEnd ℂ) (standardRoot 3) * (starRingEnd ℂ) (standardRoot 3) +
          (starRingEnd ℂ) (standardRoot 3) * (starRingEnd ℂ) (standardRoot 3) *
            ((starRingEnd ℂ) (standardRoot 3) * (starRingEnd ℂ) (standardRoot 3)) =
        (starRingEnd ℂ) (standardRoot 3) ^ 2 + (starRingEnd ℂ) (standardRoot 3) ^ 4 := by
      ring
    _ = (starRingEnd ℂ) (standardRoot 3) ^ 2 + (starRingEnd ℂ) (standardRoot 3) := by
      rw [show (starRingEnd ℂ) (standardRoot 3) ^ 4 = (starRingEnd ℂ) (standardRoot 3) by
        calc
          (starRingEnd ℂ) (standardRoot 3) ^ 4 =
              (starRingEnd ℂ) (standardRoot 3) * (starRingEnd ℂ) (standardRoot 3) ^ 3 := by
            ring
          _ = (starRingEnd ℂ) (standardRoot 3) := by rw [hz3, mul_one]]
    _ = -1 := by linear_combination dimThree_omega_star_sum

/-- `fiducialDimThree` is a Weyl--Heisenberg `1`-SIC fiducial. -/
theorem fiducialDimThree_isFiducial : IsFiducial 1 fiducialDimThree := by
  apply (fiducial_condition 1 fiducialDimThree fiducialDimThree_isRankOneHProjector
    (by norm_num) (by norm_num)).2
  rintro ⟨a, b⟩ hp
  fin_cases a <;> fin_cases b
  · exact (hp rfl).elim
  all_goals rw [sqrt_quarter]
  · suffices
        ‖(2 : ℂ)⁻¹ * (starRingEnd ℂ) (standardRoot 3) +
            (2 : ℂ)⁻¹ *
              ((starRingEnd ℂ) (standardRoot 3) * (starRingEnd ℂ) (standardRoot 3))‖ =
          (2 : ℝ)⁻¹ by
      simpa [overlap, displacementOperator, fiducialDimThree, shiftOperator, phaseOperator,
        Matrix.trace,
        Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
        pow_two] using this
    rw [← mul_add, dimThree_omega_star_mul_sum]
    norm_num
  · suffices
        ‖(2 : ℂ)⁻¹ *
              ((starRingEnd ℂ) (standardRoot 3) * (starRingEnd ℂ) (standardRoot 3)) +
            (2 : ℂ)⁻¹ *
              ((starRingEnd ℂ) (standardRoot 3) * (starRingEnd ℂ) (standardRoot 3) *
                ((starRingEnd ℂ) (standardRoot 3) * (starRingEnd ℂ) (standardRoot 3)))‖ =
          (2 : ℝ)⁻¹ by
      simpa [overlap, displacementOperator, fiducialDimThree, shiftOperator, phaseOperator,
        Matrix.trace,
        Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
        pow_two] using this
    rw [← mul_add, dimThree_omega_star_mul_four_sum]
    norm_num
  all_goals simp [overlap, displacementOperator, fiducialDimThree, shiftOperator, phaseOperator,
    Matrix.trace,
    Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ, pow_two]

end SIC

end
