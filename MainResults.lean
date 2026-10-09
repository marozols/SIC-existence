/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Construction.Existence
import SICs.Construction

/-!
# Main existence results

Weyl–Heisenberg SICs exist in every positive dimension d, and rank-r SICs at every
admissible pair.

The statements below use only Mathlib concepts. `Fin d` indexes 0, …, d − 1; pairs of such
indices label the d² projectors P(p). The operations `conjTranspose`, `rank`, and `trace`
are conjugate transpose, matrix rank, and trace. Thus each P(p) is a Hermitian idempotent of
the stated rank, and their pairwise trace products have the specified common value.

The projector and overlap conditions follow [AFK25, Definition 1.2, `def:equiangularcond`];
the overlap constants are [AFK25, Theorem 1.7, `thm:rsicbsc`]. The proofs construct the
families using Weyl–Heisenberg displacement operators, but covariance is not part of the
statements.

## The argument

`exists_SIC` has a direct principal-family proof; it is not obtained by specializing
`exists_RSIC` to r = 1. For d > 3, it builds the explicit principal overlaps and their
displacement-operator expansion from [AFK25, Definition 1.43,
`dfn:CandidateGhostAndSICFiducials`]. [RW26, Radchenko, Wheeler (2026), Theorem 7,
`thm:ghostsic`] supplies the principal convolution identity used to prove ghost idempotence,
and [RW26b, Radchenko, Wheeler (2026b), Proposition 7] applied to the principal
pseudolattice supplies the unit-modulus input. The proof then applies the shared algebraic
ghost-to-live argument of [AFK25, proof of Theorem 1.46, `thm:rayclassfieldrsicgen`]. That
theorem is conditional as printed, but the two inputs needed here are supplied
unconditionally by the cited principal results. This proof shares foundational lemmas and
the final conversion argument with the general proof; it constructs its own ghost fiducial
instead of using the general ghost-existence theorem of [AFK26]. The construction is
assembled in `exists_rankOneFiducial`.

`exists_RSIC` uses `AdmissiblePair.exists_liveFiducial` and the general construction of
[AFK25, Definition 1.43, `dfn:CandidateGhostAndSICFiducials`]. [AFK26, Appleby, Flammia,
Kopp (2026), Theorem 1.3, `thm:ghost`] supplies the ghost fiducial for every admissible
pair, and [RW26b, Radchenko, Wheeler (2026b), Proposition 7] supplies the unit-modulus
input. These are the inputs to the ghost-to-live argument of [AFK25, proof of Theorem 1.46,
`thm:rayclassfieldrsicgen`]. Although that theorem is conditional as printed, the cited
results establish the inputs needed for this general construction unconditionally. The
bounds r ≥ 1, d ≥ 2r + 2, and n ≥ 5 express exactly [AFK25, Definition 1.21,
`dfn:admissiblePair`].
-/

namespace SIC

/-! ### Rank one in every positive dimension

The principal proof supplies the fiducial. Its orbit has overlap 1/(d + 1). -/

/-- In every dimension d ≥ 1, there are d² distinct rank-one Hermitian projectors with
Tr(P(p)P(q)) = 1/(d + 1) for p ≠ q. The construction is Weyl–Heisenberg covariant. Follows
from `exists_rankOneFiducial`, the covariant form of
[AFK25, Conjecture 1.3, `conj:zauner`]. -/
theorem exists_SIC (d : ℕ) (hd : d ≥ 1) :
    ∃ P : Fin d × Fin d → Matrix (Fin d) (Fin d) ℂ,
      (∀ p, (P p).conjTranspose = P p ∧ (P p) ^ 2 = P p ∧ (P p).rank = 1) ∧
      (∀ p q, p ≠ q → (P p * P q).trace = 1 / ((d : ℂ) + 1)) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨P, hP⟩ := exists_rankOneFiducial d (by omega)
  refine ⟨WHCovariantFamily P, ?_, ?_⟩
  · intro p
    have hp := hP.isRSIC.isRankRHProjector p
    exact ⟨hp.isHProjector.hermitian.eq, hp.isHProjector.idempotent, hp.rank_eq⟩
  · intro p q hpq
    by_cases hd1 : d = 1
    · subst d
      exact (hpq (Subsingleton.elim _ _)).elim
    · have htrace := rsic_trace_formula 1 (by omega) _ hP.isRSIC p q
      simp only [ite_eq_right hpq] at htrace
      push_cast at htrace
      rw [htrace]
      have hminus : (d : ℂ) - 1 ≠ 0 := by
        exact sub_ne_zero.mpr (by exact_mod_cast hd1)
      rw [show (d : ℂ) ^ 2 - 1 = ((d : ℂ) - 1) * ((d : ℂ) + 1) by ring]
      simpa using mul_div_mul_left (1 : ℂ) ((d : ℂ) + 1) hminus

/-! ### Rank r at every admissible pair

The numerical assumptions give the pair required by the general construction. Its fiducial
produces the family, and the universal SIC trace formula gives the displayed overlap. -/

/-- For r ≥ 1, d ≥ 2r + 2, and an integer n ≥ 5 with nr(d − r) = d² − 1, there are d² distinct
rank-r Hermitian projectors with Tr(P(p)P(q)) = r(rd − 1)/(d² − 1) for p ≠ q. The
construction is Weyl–Heisenberg covariant. Follows from `AdmissiblePair.exists_liveFiducial`
under the admissibility conditions of [AFK25, Definition 1.21, `dfn:admissiblePair`]. -/
theorem exists_RSIC (d r : ℕ) (hr : r ≥ 1) (hd : d ≥ 2 * r + 2)
    (hn : ∃ n : ℕ, n ≥ 5 ∧ n * r * (d - r) = d ^ 2 - 1) :
    ∃ P : Fin d × Fin d → Matrix (Fin d) (Fin d) ℂ,
      (∀ p, (P p).conjTranspose = P p ∧ (P p) ^ 2 = P p ∧ (P p).rank = r) ∧
      (∀ p q, p ≠ q → (P p * P q).trace =
        (r : ℂ) * ((r : ℂ) * (d : ℂ) - 1) / ((d : ℂ) ^ 2 - 1)) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨n, hn, heq⟩ := hn
  let a := AdmissiblePair.ofN d r n (by omega) (by omega) (by omega) heq
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin d) (Fin d) ℂ, IsFiducial r P :=
    a.exists_liveFiducial
  refine ⟨WHCovariantFamily P, ?_, ?_⟩
  · intro p
    have hp := hP.isRSIC.isRankRHProjector p
    exact ⟨hp.isHProjector.hermitian.eq, hp.isHProjector.idempotent, hp.rank_eq⟩
  · intro p q hpq
    have htrace := rsic_trace_formula (d := d) r (by omega) _ hP.isRSIC p q
    simpa only [ite_eq_right hpq, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_sub,
      Complex.ofReal_natCast, Complex.ofReal_pow, Complex.ofReal_one] using htrace

/-! ### Axioms

The axioms the two results depend on, printed by `lake build`. -/

#print axioms exists_SIC
#print axioms exists_RSIC

end SIC
