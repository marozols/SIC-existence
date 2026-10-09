/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Quantum.IntegerDisplacement

/-!
# Displacement expansions over arbitrary transversals

Transversal independence, twisted convolution, coefficient extraction, and the square law `S² = (d²
- 1)I + CS` of a reciprocal expansion with the idempotency criterion for `aI + bS`.

This file develops the finite-sum algebra underlying [AFK25, Lemma 1.42,
`lem:GhostFiducialIndependenceOfTransversal`] and the displacement expansion in
[AFK25, Section 3.1]. A summand that respects nonzero residue classes has the same sum
on every transversal. Conversely, for values in a cancellative additive commutative monoid,
independence of all transversal sums forces the summand to respect each nonzero residue class.
Coprime integral matrices permute these classes.

Collecting products by the output residue gives the twisted convolution formula for
the square of an expansion; for reciprocal coefficients whose off-origin convolution is a fixed
multiple of the coefficients, the square is `(d² - 1)I + CS`, which reduces the projector equation
for `aI + bS` to scalar arithmetic. Negation and conjugation give its Hermitian symmetry,
and Hilbert--Schmidt orthogonality isolates each coefficient by a trace. The statements
apply to arbitrary complex coefficients; ghost-overlap conditions enter only downstream.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### Residue-independent sums and their products

The source permits any complete set of representatives. Descending the full summand
to the residue class makes that choice irrelevant before multiplying the expansion. Conversely,
when the sums admit cancellation, changing just one nonzero representative and cancelling all
other terms shows that transversal independence forces the summand to respect residues. -/

/-- A function on integer phase space respects the nonzero residue classes modulo `d` when its
value is unchanged after replacing a nonzero index by any congruent integer representative. -/
def RespectsPhaseSpaceResiduesAwayFromZero {A : Type*} (d : ℕ)
    (f : IntPhaseSpace → A) : Prop :=
  ∀ p p', intPhaseSpaceMod d p' = intPhaseSpaceMod d p →
    intPhaseSpaceMod d p ≠ 0 → f p' = f p

/-- Square a transversal-indexed displacement sum and collect its terms by output residue. This
is the general finite Weyl--Heisenberg convolution step used by ghost-projector constructions. -/
lemma transversalDisplacementSum_sq {d : ℕ} [NeZero d]
    (w : IntPhaseSpace → ℂ)
    (hw : RespectsPhaseSpaceResiduesAwayFromZero d
      (fun p => w p • integerDisplacement d p))
    (I : PhaseSpaceTransversal d) :
    (∑ q : PhaseSpaceMod d, if q = 0 then 0 else
        w (I.repr q) • integerDisplacement d (I.repr q)) ^ 2 =
      ∑ p : PhaseSpaceMod d,
        (∑ q : PhaseSpaceMod d, if q = 0 ∨ q = p then 0 else
          displacementPhase d ^ intSymplecticForm (I.repr p) (I.repr q) *
            w (I.repr p - I.repr q) * w (I.repr q)) •
          integerDisplacement d (I.repr p) := by
  classical
  let f : PhaseSpaceMod d → Mat(d, ℂ) := fun q =>
    if q = 0 then 0 else w (I.repr q) • integerDisplacement d (I.repr q)
  change (∑ q, f q) ^ 2 = _
  rw [pow_two, Matrix.sum_mul]
  simp_rw [Matrix.mul_sum]
  rw [Finset.sum_comm]
  have hreindex (q : PhaseSpaceMod d) :
      (∑ r : PhaseSpaceMod d, f r * f q) =
        ∑ p : PhaseSpaceMod d, f (p - q) * f q := by
    let e := Equiv.addRight q
    have h := Equiv.sum_comp e (fun p : PhaseSpaceMod d => f (p - q) * f q)
    simpa [e, add_comm, add_left_comm, add_assoc] using h
  simp_rw [hreindex]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : q = 0
  · simp [f, hq]
  by_cases hpq : q = p
  · simp [f, hpq]
  have hpq0 : p - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hpq)
  rw [ite_eq_right (not_or_intro hq hpq)]
  dsimp only [f]
  rw [ite_eq_right hq, ite_eq_right hpq0]
  have hmod : intPhaseSpaceMod d (I.repr p - I.repr q) = p - q := by
    funext i
    have hp := congrFun (I.residue_repr p) i
    have hq' := congrFun (I.residue_repr q) i
    simpa [intPhaseSpaceMod] using congrArg₂ (· - ·) hp hq'
  have hrep : w (I.repr (p - q)) • integerDisplacement d (I.repr (p - q)) =
      w (I.repr p - I.repr q) • integerDisplacement d (I.repr p - I.repr q) := by
    apply hw
    · rw [I.residue_repr, hmod]
    · rw [hmod]
      exact hpq0
  rw [hrep, Matrix.smul_mul, Matrix.mul_smul, integerDisplacement_mul, smul_smul]
  have hsymp : intSymplecticForm (I.repr p - I.repr q) (I.repr q) =
      intSymplecticForm (I.repr p) (I.repr q) := by
    simp [intSymplecticForm]
    ring
  rw [hsymp]
  ext i j
  simp [mul_assoc, mul_left_comm, mul_comm]

/-- Sums of a residue-respecting function over the nonzero classes do not depend on the chosen
complete transversal. -/
theorem sum_transversal_eq_of_respectsResidues {A : Type*} [AddCommMonoid A]
    {d : ℕ} [NeZero d] (f : IntPhaseSpace → A)
    (hf : RespectsPhaseSpaceResiduesAwayFromZero d f)
    (I J : PhaseSpaceTransversal d) :
    (∑ q : PhaseSpaceMod d, if q = 0 then 0 else f (I.repr q)) =
      ∑ q : PhaseSpaceMod d, if q = 0 then 0 else f (J.repr q) := by
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : q = 0
  · simp [hq]
  · rw [ite_eq_right hq, ite_eq_right hq]
    apply hf (J.repr q) (I.repr q)
    · rw [I.residue_repr, J.residue_repr]
    · rwa [J.residue_repr]

/-- If the sum over nonzero classes is independent of every transversal, then the summand
respects nonzero residue classes. This is the converse of
`sum_transversal_eq_of_respectsResidues` for values in a cancellative additive commutative
monoid. -/
theorem respectsResidues_of_sum_transversal_eq {A : Type*} [AddCancelCommMonoid A]
    {d : ℕ} [NeZero d] (f : IntPhaseSpace → A)
    (h : ∀ I J : PhaseSpaceTransversal d,
      (∑ q : PhaseSpaceMod d, if q = 0 then 0 else f (I.repr q)) =
        ∑ q : PhaseSpaceMod d, if q = 0 then 0 else f (J.repr q)) :
    RespectsPhaseSpaceResiduesAwayFromZero d f := by
  classical
  intro p p' hmod hp
  let I (x : IntPhaseSpace) (hx : intPhaseSpaceMod d x = intPhaseSpaceMod d p) :
      PhaseSpaceTransversal d := {
    repr := fun q => if q = intPhaseSpaceMod d p then x else
      (canonicalPhaseSpaceTransversal d).repr q
    residue_repr := by
      intro q
      split_ifs with hq
      · exact hx.trans hq.symm
      · exact (canonicalPhaseSpaceTransversal d).residue_repr q }
  have hh := h (I p' hmod) (I p rfl)
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (intPhaseSpaceMod d p)),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ (intPhaseSpaceMod d p))] at hh
  have he : (∑ q ∈ Finset.univ.erase (intPhaseSpaceMod d p),
      if q = 0 then 0 else f ((I p' hmod).repr q)) =
      ∑ q ∈ Finset.univ.erase (intPhaseSpaceMod d p),
      if q = 0 then 0 else f ((I p rfl).repr q) := by
    apply Finset.sum_congr rfl
    intro q hq
    simp only [I, ite_eq_right (Finset.mem_erase.mp hq).1]
  rw [he] at hh
  simpa [I, hp] using add_left_cancel hh

/-- **Reindexing a transversal sum along an integer matrix.** When `det G` is coprime to `d̄` the
map `p ↦ G p` permutes the nonzero phase-space residues modulo `d`, so a residue-respecting
summand may be evaluated at `G` applied to the transversal representatives without changing the
sum.

This is the reindexing performed when converting a ghost fiducial to a live one with `G = H_g`:
entrywise Galois conjugation moves every displacement index by `H_g`, and the resulting expansion
is returned to `ghostFiducialMatrix` shape by permuting the summation variable rather than the
summand. -/
theorem sum_transversal_mulVec_eq_of_respectsResidues {A : Type*} [AddCommMonoid A]
    {d : ℕ} [NeZero d] (f : IntPhaseSpace → A)
    (hf : RespectsPhaseSpaceResiduesAwayFromZero d f)
    (G : Mat(2, ℤ)) (hG : IsCoprime G.det (dbar d : ℤ))
    (I : PhaseSpaceTransversal d) :
    (∑ q : PhaseSpaceMod d, if q = 0 then 0 else f (Matrix.mulVec G (I.repr q))) =
      ∑ q : PhaseSpaceMod d, if q = 0 then 0 else f (I.repr q) := by
  classical
  let e := phaseSpaceModMulVecEquiv G (isCoprime_of_isCoprime_dbar hG)
  have key : ∀ q : PhaseSpaceMod d,
      (if q = 0 then 0 else f (Matrix.mulVec G (I.repr q))) =
        (if e q = 0 then 0 else f (I.repr (e q))) := by
    intro q
    by_cases hq : q = 0
    · rw [ite_eq_left hq, ite_eq_left ((phaseSpaceModMulVecEquiv_eq_zero_iff _ _).mpr hq)]
    · have hq' : e q ≠ 0 := fun h => hq ((phaseSpaceModMulVecEquiv_eq_zero_iff _ _).mp h)
      rw [ite_eq_right hq, ite_eq_right hq']
      refine hf (I.repr (e q)) (Matrix.mulVec G (I.repr q)) ?_ ?_
      · rw [intPhaseSpaceMod_mulVec_eq_mulVecEquiv G _, I.residue_repr,
          I.residue_repr]
      · rw [I.residue_repr]; exact hq'
  rw [Finset.sum_congr rfl fun q _ => key q]
  exact Equiv.sum_comp e (fun q => if q = 0 then 0 else f (I.repr q))

/-- **A transversal displacement expansion with conjugate-symmetric coefficients is Hermitian.**

This is the property needed to upgrade a parity-Hermitian expansion to a genuinely Hermitian one,
and it is genuinely different from parity-Hermiticity: `IsPHermitian` holds for real coefficients,
whereas Hermiticity of the
displacement expansion is exactly the condition `w(-p) = conj (w p)`. The proof pairs each index
with its negative, which is the reindexing above at the matrix `-1` of determinant `1`. -/
theorem isHermitian_transversal_sum_of_conj_symm {d : ℕ} [NeZero d]
    (w : IntPhaseSpace → ℂ)
    (hw : RespectsPhaseSpaceResiduesAwayFromZero d
      (fun p => w p • integerDisplacement d p))
    (hconj : ∀ p : IntPhaseSpace, intPhaseSpaceMod d p ≠ 0 →
      w (-p) = starRingEnd ℂ (w p))
    (I : PhaseSpaceTransversal d) :
    (∑ q : PhaseSpaceMod d, if q = 0 then 0 else
      w (I.repr q) • integerDisplacement d (I.repr q)).IsHermitian := by
  have hneg : ∀ p : IntPhaseSpace,
      Matrix.mulVec (-1 : Mat(2, ℤ)) p = -p := by
    intro p
    rw [Matrix.neg_mulVec, Matrix.one_mulVec]
  have step : ∀ q : PhaseSpaceMod d,
      (if q = 0 then (0 : Mat(d, ℂ))
        else w (I.repr q) • integerDisplacement d (I.repr q)).conjTranspose =
      (if q = 0 then (0 : Mat(d, ℂ))
        else w (Matrix.mulVec (-1 : Mat(2, ℤ)) (I.repr q)) •
          integerDisplacement d (Matrix.mulVec (-1 : Mat(2, ℤ)) (I.repr q))) := by
    intro q
    by_cases hq : q = 0
    · simp [hq]
    · rw [ite_eq_right hq, ite_eq_right hq, Matrix.conjTranspose_smul,
        conjTranspose_integerDisplacement, hneg,
        hconj (I.repr q) (by rw [I.residue_repr]; exact hq)]
      rfl
  change (∑ q : PhaseSpaceMod d, if q = 0 then 0 else
      w (I.repr q) • integerDisplacement d (I.repr q)).conjTranspose = _
  rw [Matrix.conjTranspose_sum, Finset.sum_congr rfl fun q _ => step q]
  exact sum_transversal_mulVec_eq_of_respectsResidues _ hw
    (-1 : Mat(2, ℤ))
    (by simpa [Matrix.det_fin_two] using
      (isCoprime_one_left : IsCoprime (1 : ℤ) (dbar d : ℤ))) I

/-! ### The square law of a reciprocal expansion

A ghost projector is `aI + bS` for a displacement expansion `S` whose coefficients are reciprocal,
`w(p)w(-p) = 1`. In `S²` the coefficient of `D_0` then counts the `d² - 1` nonzero classes; if
every other coefficient is one fixed multiple `C` of `w`, then `S² = (d² - 1)I + CS`, and the
projector equation for `aI + bS` reduces to two scalar identities. This is the matrix algebra of
the proof of [AFK25, Theorem 1.45, `thm:ghstExist`], shared by every candidate ghost fiducial. -/

/-- There are `d² - 1` nonzero phase-space classes modulo `d`. -/
theorem sum_ite_eq_zero_zero_one (d : ℕ) [NeZero d] :
    (∑ q : PhaseSpaceMod d, if q = 0 then (0 : ℂ) else 1) = (d : ℂ) ^ 2 - 1 := by
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.filter_ne' Finset.univ 0, Finset.card_erase_of_mem (Finset.mem_univ 0),
    Finset.card_univ]
  have hcard : Fintype.card (PhaseSpaceMod d) = d ^ 2 := by simp [PhaseSpaceMod]
  rw [hcard, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (NeZero.ne d)))]
  push_cast
  ring

/-- **The square law of a reciprocal displacement expansion.** Let the summand `w(p) D_p` respect
nonzero residues, let `w(p)w(-p) = 1` off the zero class, and let the excluded convolution at every
nonzero class `p` be `C·w(p)`. Then over a transversal representing the zero class by `0`,
`S = ∑_{q ≠ 0} w(q) D_q` satisfies `S² = (d² - 1) I + C S`: in `transversalDisplacementSum_sq`
the coefficient of `D_0` is the sum of the `d² - 1` products `w(-q)w(q) = 1`. -/
theorem transversalDisplacementSum_sq_eq_of_reciprocal {d : ℕ} [NeZero d]
    (w : IntPhaseSpace → ℂ)
    (hw : RespectsPhaseSpaceResiduesAwayFromZero d (fun p => w p • integerDisplacement d p))
    (I : PhaseSpaceTransversal d) (hI0 : I.repr 0 = 0) (C : ℂ)
    (hrecip : ∀ p, intPhaseSpaceMod d p ≠ 0 → w p * w (-p) = 1)
    (hconv : ∀ p : PhaseSpaceMod d, p ≠ 0 →
      (∑ q : PhaseSpaceMod d, if q = 0 ∨ q = p then 0 else
        displacementPhase d ^ intSymplecticForm (I.repr p) (I.repr q) *
          w (I.repr p - I.repr q) * w (I.repr q)) = C * w (I.repr p)) :
    (∑ q : PhaseSpaceMod d, if q = 0 then 0 else
        w (I.repr q) • integerDisplacement d (I.repr q)) ^ 2 =
      ((d : ℂ) ^ 2 - 1) • (1 : Mat(d, ℂ)) +
        C • ∑ q : PhaseSpaceMod d, if q = 0 then 0 else
          w (I.repr q) • integerDisplacement d (I.repr q) := by
  have hcoeff (p : PhaseSpaceMod d) :
      (∑ q : PhaseSpaceMod d, if q = 0 ∨ q = p then 0 else
        displacementPhase d ^ intSymplecticForm (I.repr p) (I.repr q) *
          w (I.repr p - I.repr q) * w (I.repr q)) =
        if p = 0 then (d : ℂ) ^ 2 - 1 else C * w (I.repr p) := by
    split_ifs with hp
    · subst p
      rw [← sum_ite_eq_zero_zero_one d]
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [or_self]
      split_ifs with hq
      · rfl
      · rw [hI0, zero_sub]
        simp only [intSymplecticForm, Pi.zero_apply, zero_mul, sub_self, zpow_zero, one_mul]
        rw [mul_comm, hrecip _ (by rwa [I.residue_repr])]
    · exact hconv p hp
  have hone : ((d : ℂ) ^ 2 - 1) • (1 : Mat(d, ℂ)) =
      ∑ p : PhaseSpaceMod d, if p = 0 then
        ((d : ℂ) ^ 2 - 1) • integerDisplacement d (I.repr p) else 0 := by
    rw [Finset.sum_ite_eq' Finset.univ 0, ite_eq_left (Finset.mem_univ _), hI0,
      integerDisplacement_zero]
  rw [transversalDisplacementSum_sq w hw I, hone, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hcoeff]
  split_ifs <;> simp [mul_smul]

/-- **The idempotency criterion for `aI + bS`**: if `S² = uI + vS`, then `aI + bS` is idempotent
as soon as `a² + b²u = a` and `2ab + b²v = b`. -/
theorem smul_one_add_smul_sq_eq_self {n : Type*} [Fintype n] [DecidableEq n]
    {S : Matrix n n ℂ} {a b u v : ℂ} (hS : S ^ 2 = u • (1 : Matrix n n ℂ) + v • S)
    (h₁ : a ^ 2 + b ^ 2 * u = a) (h₂ : 2 * a * b + b ^ 2 * v = b) :
    (a • (1 : Matrix n n ℂ) + b • S) ^ 2 = a • (1 : Matrix n n ℂ) + b • S := by
  rw [pow_two] at hS ⊢
  calc
    (a • (1 : Matrix n n ℂ) + b • S) * (a • 1 + b • S) =
        (a ^ 2 + b ^ 2 * u) • (1 : Matrix n n ℂ) + (2 * a * b + b ^ 2 * v) • S := by
      simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one, smul_smul, hS, smul_add]
      module
    _ = _ := by rw [h₁, h₂]

/-! ### Recovering coefficients by displacement overlaps

Hilbert--Schmidt orthogonality extracts a coefficient from a transversal expansion. -/

/-- **The displacement overlap of a transversal expansion.** Tracing a transversal displacement
expansion against `D_p†` isolates its coefficient at `p`, scaled by `d`.

This connects a fiducial's displacement expansion to its overlaps: Hilbert-Schmidt orthogonality of
the displacement operators (`displacementOperator_HS_orthogonal`) turns the expansion's
coefficients into the overlaps `Tr(P D_p†)` of `overlap`, which is what `fiducial_condition`
constrains. Residue independence of the summand allows the transversal representative at the class
of `p` to be replaced by `p` itself, so no representative-change phase survives. -/
theorem trace_transversal_sum_mul_conjTranspose {d : ℕ} [NeZero d]
    (w : IntPhaseSpace → ℂ)
    (hw : RespectsPhaseSpaceResiduesAwayFromZero d
      (fun p => w p • integerDisplacement d p))
    (I : PhaseSpaceTransversal d) (p : Fin d × Fin d) (hp : p ≠ 0) :
    ((∑ q : PhaseSpaceMod d, if q = 0 then 0 else
        w (I.repr q) • integerDisplacement d (I.repr q)) *
      (displacementOperator d p).conjTranspose).trace = (d : ℂ) * w (finPhaseSpaceToInt p) := by
  classical
  set P : IntPhaseSpace := finPhaseSpaceToInt p with hP
  set c : PhaseSpaceMod d := intPhaseSpaceMod d P with hc
  have hPfin : intPhaseSpaceToFin d P = p := intPhaseSpaceToFin_finPhaseSpaceToInt d p
  have hcne : c ≠ 0 := by
    intro h
    exact hp (by rw [← hPfin, intPhaseSpaceToFin_eq_zero_iff]; exact h)
  rw [Matrix.sum_mul, Matrix.trace_sum, Finset.sum_eq_single c]
  · rw [ite_eq_right hcne]
    have hrep : w (I.repr c) • integerDisplacement d (I.repr c)
        = w P • integerDisplacement d P :=
      hw P (I.repr c) (by rw [I.residue_repr]) hcne
    rw [hrep, hP, integerDisplacement_finPhaseSpaceToInt, Matrix.smul_mul, Matrix.trace_smul,
      displacementOperator_mul_conjTranspose, Matrix.trace_one]
    simp [mul_comm]
  · intro q _ hq
    by_cases hq0 : q = 0
    · simp [hq0]
    rw [ite_eq_right hq0]
    have hne : intPhaseSpaceToFin d (I.repr q) ≠ p := by
      intro h
      apply hq
      have := intPhaseSpaceMod_eq_of_intPhaseSpaceToFin_eq h
      rwa [I.residue_repr, ← hP, ← hc] at this
    rw [integerDisplacement, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_smul,
      Matrix.trace_smul, Matrix.trace_mul_comm, displacementOperator_HS_orthogonal,
      ite_eq_right (Ne.symm hne)]
    simp
  · intro h
    exact absurd (Finset.mem_univ c) h

end SIC

end
