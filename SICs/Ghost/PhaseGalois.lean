/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.FieldTheory.AlgebraicClosure
import SICs.Ghost.Phase
import SICs.Quantum.GaloisAction

/-!
# Galois images of the SF phase

Galois modulus one of the exact SF phase.

The SF phase of [AFK25, Definition 1.30, `dfn:SFKPhase`] is a product of roots of unity, so every
ambient `ℚ`-automorphism sends it to a number of modulus one. This is the step that carries the
unit-modulus condition from the Shintani--Faddeev values to the normalized ghost overlaps in
`SICs.Ghost.LiveCandidate`.

The parity sign and the displacement phase already have finite order. For the remaining factor,
write `q = -Ψ(A)/24`; then `exp(-πi Ψ(A)/12) = exp(2πiq)`, whose order is the denominator of
`q`. Thus the argument works directly with the rational-valued Rademacher API and needs no
separate integrality theorem for `Ψ(A)`. An automorphism preserves each root-of-unity equation,
so it keeps every factor on the unit circle. These are the elementary phase steps used in
[AFK25, proof of Theorem 1.46, `thm:rayclassfieldrsicgen`].
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### The Rademacher factor

The Rademacher factor is the rational phase `e(-Ψ(A)/24)`. Its unit modulus under ambient
automorphisms is supplied by the rational-phase API in `SICs.FieldTheory.ComplexGalois`.
-/

/-- The Rademacher factor as the rational exponential `e(-Ψ(A)/24)`, used by
`AdmissibleTuple.norm_map_sfPhase`. -/
private lemma rademacherPhase_eq_exp_ratCast (A : SL(2, ℤ)) :
    Complex.exp (-Real.pi * Complex.I / 12 * (rademacherInvariant A : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * ((-rademacherInvariant A / 24 : ℚ) : ℂ)) := by
  congr 1
  push_cast
  ring

/-! ### The exact SF phase

Each of the three factors of `Φ_t(p)` is a root of unity, so its image under an ambient
automorphism has modulus one.
-/

/-- Every ambient Galois automorphism satisfies `|g(Φ_t(p))| = 1`.
This is the root-of-unity observation in [AFK25, proof of Theorem 1.46,
`thm:rayclassfieldrsicgen`], applied directly to `AdmissibleTuple.sfPhase`. -/
lemma AdmissibleTuple.norm_map_sfPhase (t : AdmissibleTuple) (A : SL(2, ℤ))
    (p : IntPhaseSpace) (g : ComplexGaloisAutomorphism) : ‖g (t.sfPhase A p)‖ = 1 := by
  have hrad : ‖g (Complex.exp
      (-Real.pi * Complex.I / 12 * (rademacherInvariant A : ℂ)))‖ = 1 := by
    rw [rademacherPhase_eq_exp_ratCast]
    exact norm_map_exp_two_pi_I_ratCast g _
  simp only [AdmissibleTuple.sfPhase, map_mul, norm_mul, hrad, map_zpow₀,
    map_neg, map_one, norm_zpow, norm_neg, norm_one, one_zpow, mul_one,
    map_displacementPhase, norm_pow, norm_displacementPhase, one_pow]

end SIC

end
