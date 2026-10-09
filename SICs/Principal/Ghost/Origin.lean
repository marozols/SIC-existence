/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Ghost.CandidateOverlaps
import SICs.Principal.Admissible
import SICs.Principal.Ghost.Overlaps
import SICs.Principal.Quadratic.Stabilizers

/-!
# The Principal Ghost Overlap at the Origin

The `p=0` origin special value, proved unconditionally.

This file treats the **zero coefficient** of the principal family separately from the nonzero ones
(see "Why the origin is genuinely different" below) and formalizes the arithmetic content of [AFK25,
Lemma `lem:nu01overnu0val`] for the principal tuple `t_d`:

`ν̃_t(0) + ν̃_t(0)⁻¹ = -(d - 2r) √(d_j + 1)`,   which for `t_d` (where `r = 1`, `d_j = d`) reads
`ν̃_{t_d}(0) + ν̃_{t_d}(0)⁻¹ = -(d - 2) √(d + 1)`.

The paper's proof has two halves. The analytic half is [AFK25, Lemma 2.15, `lm:shinatzero`]: at a
fixed point of `A ∈ Γ(d)` the SF modular cocycle at `r = 0` is
`ψ(A, √j_A) / √(j_A(ρ))`, which combined
with the phase `Φ_{t}(0)` gives `ν̃_t(0) = -1 / √(j_{A_t}(ρ_t))`. The arithmetic half evaluates
`√(j_{A_t}(ρ_t)) + 1/√(j_{A_t}(ρ_t)) = √(Tr(A_t) + 2)` and identifies `Tr(A_t) + 2` with
`(d - 2r)²(d_j + 1)`.

Both halves are proved here.  The analytic half is `doubleSine'_one_principalRoot_pow_three`,
which deduces the boundary value `S₂(1, ρ_d) = √ρ_d` from the defining integral and combines it
with the elementary identity `j_{A_d}(ρ_d) = ρ_d³`.

## Why the origin is genuinely different

The reciprocity law `ν_d(p) ν_d(-p) = 1` of [AFK25, Theorem 5.8, `thm:nupnumpeq1`]
(`principalNormGhostOverlap_reciprocal`) is proved only for `p ≢ 0 (mod d)`, and this is not an
artifact of the proof: at the origin all three double-sine factors collapse to the *same* value
`S₂(1, ρ_d)`, so `ν_d(0) ν_d(-0) = S₂(1, ρ_d)⁻⁶ = 1 / j_{A_d}(ρ_d) ≠ 1`. Its square lies in the
real quadratic field, but the origin value itself need not: taking `√(j_{A_d}(ρ_d))` can require a
quadratic extension. Its absolute value is strictly less than one, so it is not a root of unity.
This is why [AFK25, Lemma 5.9, `lem:nu01overnu0val`] states a *sum* identity there rather than a
product one.

## Main definitions and results

The Jacobi factor `j_{A_d}(ρ_d) = ρ_d³` (`principalJacobiFactor`) and its eigenvalue identity
`j + j⁻¹ = Tr(A_d) = d²(d - 3) + 2` are elementary stabilizer arithmetic, proved in
`SICs.Principal.Quadratic.Stabilizers`; note `Tr(A_d) + 2 = (d - 2)²(d + 1)`.

- `sqrt_principalJacobiFactor_add_inv`: `√j + (√j)⁻¹ = (d - 2)√(d + 1)`, the principal case of
  [AFK25, equation (5.69), `eq:nu01overnu0val1`], read backwards.
- `principalNormGhostOverlap_zero`: the origin value of `principalNormGhostOverlap` is
  `-(S₂(1, ρ_d)³)⁻¹`; the minus sign remains after the SF phase's exponential cancels the
  cocycle's exponential.
- `doubleSine'_one_principalRoot_pow_three`: the analytic identity `S₂(1, ρ_d)³ = √(j_{A_d}(ρ_d))`.
- `principalNormGhostOverlapReal_zero_add_inv`:
  **[AFK25, Lemma 5.9, `lem:nu01overnu0val`] for `t_d`**, proved unconditionally.

## References

- [AFK25] Appleby, Flammia, Kopp, arXiv:2501.03970v2, Lemmas `lm:shinatzero` and
  `lem:nu01overnu0val`
-/

noncomputable section

open Real

namespace SIC

/-! ### The square-root identity

Positivity of the principal root turns its quadratic equation into an identity for
`√(ρ_d³) + 1/√(ρ_d³)`. The result matches the trace-side normalization at the origin.
-/

/-- **[AFK25, equation (5.69), `eq:nu01overnu0val1`] for `t_d`, up to sign.** The square root of the
Jacobi factor and its inverse sum to `(d - 2)√(d + 1)`.

Squaring the left-hand side gives `j + 2 + j⁻¹ = Tr(A_d) + 2 = (d - 2)²(d + 1)` by
`principalJacobiFactor_add_inv`; both sides are positive, so the identity follows. -/
lemma sqrt_principalJacobiFactor_add_inv (d : ℕ) (hd : 3 < d) :
    Real.sqrt (principalJacobiFactor d) + (Real.sqrt (principalJacobiFactor d))⁻¹ =
      ((d : ℝ) - 2) * Real.sqrt ((d : ℝ) + 1) := by
  have hjpos := principalJacobiFactor_pos d hd
  have hdreal : (4 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hspos : 0 < Real.sqrt (principalJacobiFactor d) := Real.sqrt_pos.mpr hjpos
  have hsq : Real.sqrt (principalJacobiFactor d) ^ 2 = principalJacobiFactor d :=
    Real.sq_sqrt (le_of_lt hjpos)
  have hd1 : Real.sqrt ((d : ℝ) + 1) ^ 2 = (d : ℝ) + 1 := Real.sq_sqrt (by linarith)
  have hd1pos : 0 < Real.sqrt ((d : ℝ) + 1) := Real.sqrt_pos.mpr (by linarith)
  have hleft : 0 ≤ Real.sqrt (principalJacobiFactor d) +
      (Real.sqrt (principalJacobiFactor d))⁻¹ := by positivity
  have hright : 0 ≤ ((d : ℝ) - 2) * Real.sqrt ((d : ℝ) + 1) := by
    have : (0 : ℝ) ≤ (d : ℝ) - 2 := by linarith
    positivity
  have hsum := principalJacobiFactor_add_inv d hd
  have hsquares : (Real.sqrt (principalJacobiFactor d) +
      (Real.sqrt (principalJacobiFactor d))⁻¹) ^ 2 =
      (((d : ℝ) - 2) * Real.sqrt ((d : ℝ) + 1)) ^ 2 := by
    have hinv : (Real.sqrt (principalJacobiFactor d))⁻¹ ^ 2 = (principalJacobiFactor d)⁻¹ := by
      rw [inv_pow, hsq]
    have hmul : Real.sqrt (principalJacobiFactor d) *
        (Real.sqrt (principalJacobiFactor d))⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hspos)
    rw [mul_pow, hd1, add_sq, hsq, hinv, mul_assoc, hmul]
    linarith [hsum]
  nlinarith [hsquares, hleft, hright]

/-! ### The origin value of the elementary three-factor product

At `(0,0)`, all three canonical double-sine arguments equal `1`. After the SF phase's exponential
cancels the cocycle's exponential, its sign factor contributes the extra minus sign built into
`principalNormGhostOverlap` at the zero residue.
-/

/-- At the origin all three double-sine arguments of `principalTripleDoubleSine` collapse to `1`,
and the sign exponent vanishes. -/
lemma principalTripleDoubleSine_zero (d : ℕ) :
    principalTripleDoubleSine d 0 0 = (doubleSine' 1 (principalRoot d) ^ 3)⁻¹ := by
  have harg : principalDoubleSineArg d 0 0 = 1 := by
    simp [principalDoubleSineArg]
  have hthird : principalThirdIndex d 0 0 = 0 := by
    simp [principalThirdIndex]
  have hsign : principalSignExp d 0 0 = 0 := by
    simp [principalSignExp]
  rw [principalTripleDoubleSine, hthird, hsign, harg]
  ring

/-- **The zero coefficient of the principal overlap, treated separately.** The transport factor is
trivial at the origin, so `ν_d(0)` is minus the inverse cube of the single double-sine value
`S₂(1, ρ_d)`. The minus sign is the source's sign factor `(-1)^{s_d(0)} = -1`, carried
by the origin correction in `principalNormGhostOverlap`. The full phase also contains
`exp(-πi Ψ(A_d)/12)`, which cancels the cocycle's exponential in the source formula. Nothing about
the nonzero formula is silently extended: this is the value of `principalNormGhostOverlap` at `0`
computed from its definition. -/
lemma principalNormGhostOverlap_zero (d : ℕ) [NeZero d] :
    principalNormGhostOverlap d 0 = -(((doubleSine' 1 (principalRoot d) ^ 3)⁻¹ : ℝ) : ℂ) := by
  have hcanon : canonicalIntPhaseSpaceRep d (0 : IntPhaseSpace) = 0 := by
    funext i
    simp [canonicalIntPhaseSpaceRep]
  have hmod : intPhaseSpaceMod d (0 : IntPhaseSpace) = 0 := by
    funext i
    simp [intPhaseSpaceMod]
  rw [principalNormGhostOverlap_of_mod_eq_zero d hmod, hcanon]
  have hsymp : intSymplecticForm (0 : IntPhaseSpace) (0 : IntPhaseSpace) = 0 := by
    simp [intSymplecticForm]
  rw [hsymp, zpow_zero, one_mul, show (0 : IntPhaseSpace) 0 = 0 from rfl,
    show (0 : IntPhaseSpace) 1 = 0 from rfl, principalTripleDoubleSine_zero]

/-- The real-valued origin overlap, in the same closed form. -/
lemma principalNormGhostOverlapReal_zero (d : ℕ) [NeZero d] :
    principalNormGhostOverlapReal d 0 = -(doubleSine' 1 (principalRoot d) ^ 3)⁻¹ := by
  have h := principalNormGhostOverlap_zero d
  rw [principalNormGhostOverlapReal, h, Complex.neg_re, Complex.ofReal_re]

/-! ### The origin identity `ν̃_d(0,0) = ν_d(0,0)`, unconditionally

At `(p,q) = (0,0)`, the cocycle word `A_d = T^{d-1}ST^{d-1}ST^{d-1}S` evaluates `σ_S` at
the same base point `0` in all three factors, since `z/ρ_d = z/ρ_d² = 0`. Each factor is
`sigmaSBase 0 ρ_d`, and the SF cocycle's denominator is `ϖ_0 = 1` because `n_QP(0,0) = 0`.
Consequently, `ש^{(0,0)}_{A_d}(ρ_d) = sigmaSBase 0 ρ_d ^ 3`. Multiplication by the phase gives
`Φ_d(0,0) · sigmaSBase 0 ρ_d ^ 3 = ν_d(0,0)` by direct cancellation of the double-sine factors.
This identity does not require the boundary-period evaluation
`doubleSine'_one_principalRoot_pow_three`. -/

/-- **The origin identity `ν̃_d(0,0) = ν_d(0,0)`.**
The SF phase at the origin (`sfPhase` at the principal family, through
`RankOneAdmissibleTuple.sfPhase_of_conductorRatio_eq_one` and
`principalRankOneAdmissibleTuple_conductorRatio`)
times the cube of `σ_S`'s origin value equals the explicit product-side overlap at the origin. The
minus sign left after the exponential factors cancel is exactly the origin correction built into
`principalNormGhostOverlap`, which is why no sign survives in the statement. Proved directly from
`rademacherInvariant_principalA`, `principalNormGhostOverlap_zero`, and the quadratic relation
`principalRoot_satisfies_quadratic`; see the section docstring above for why no comparison to
`√(j_{A_d}(ρ_d))` is needed. -/
theorem sfPhase_zero_mul_sigmaSBase_zero_cube (d : RankOneDimension) :
    (principalRankOneAdmissibleTuple d).sfPhase (principalA d) (0 : IntPhaseSpace) *
        sigmaSBase 0 (principalRoot d) ^ 3 =
      principalNormGhostOverlap d (0 : IntPhaseSpace) := by
  have hc : (principalRankOneAdmissibleTuple d).conductorRatio = 1 :=
    principalRankOneAdmissibleTuple_conductorRatio d
  rw [RankOneAdmissibleTuple.sfPhase_of_conductorRatio_eq_one _ hc]
  simp only [principalRankOneAdmissibleTuple_d, principalRankOneAdmissibleTuple_Q]
  have hsign : sfSignExp d (0 : IntPhaseSpace) = 2 * (d : ℤ) + 1 := by
    simp only [sfSignExp, show (0 : IntPhaseSpace) 0 = 0 from rfl,
      show (0 : IntPhaseSpace) 1 = 0 from rfl]
    ring
  have heval :
      (principalOneSICForm d).eval ((0 : IntPhaseSpace) 0) ((0 : IntPhaseSpace) 1) = 0 := by
    simp [BinaryQF.eval, principalOneSICForm]
  rw [hsign, heval, neg_zero, zpow_zero, mul_one]
  have hodd : (-1 : ℂ) ^ (2 * (d : ℤ) + 1) = -1 := by
    rw [zpow_add₀ (show (-1 : ℂ) ≠ 0 by norm_num), zpow_mul]
    norm_num
  rw [hodd, rademacherInvariant_principalA d d.property, principalNormGhostOverlap_zero d]
  have hτ0 : (principalRoot d : ℝ) ≠ 0 := ne_of_gt (principalRoot_pos d d.property)
  have hcast : (-π * Complex.I / 12 * ((3 * (d : ℚ) - 12 : ℚ) : ℂ)) =
      -π * Complex.I / 12 * (3 * (d : ℂ) - 12) := by push_cast; ring
  rw [hcast]
  have hSB : sigmaSBase 0 (principalRoot d) =
      Complex.exp (π * Complex.I / (12 * (principalRoot d : ℂ)) *
          ((principalRoot d : ℂ) ^ 2 - 3 * (principalRoot d : ℂ) + 1)) /
        (doubleSine' 1 (principalRoot d) : ℂ) := by
    rw [sigmaSBase, sfExpArg, faddeevSExpArg]
    norm_num
  rw [hSB, div_pow, ← Complex.exp_nat_mul]
  have hquad : (principalRoot d : ℂ) ^ 2 - ((d : ℂ) - 1) * (principalRoot d : ℂ) + 1 = 0 := by
    exact_mod_cast principalRoot_satisfies_quadratic d d.property
  have hexp0 : -π * Complex.I / 12 * (3 * (d : ℂ) - 12) +
      (3 : ℕ) * (π * Complex.I / (12 * (principalRoot d : ℂ)) *
        ((principalRoot d : ℂ) ^ 2 - 3 * (principalRoot d : ℂ) + 1)) = 0 := by
    have hτ0' : (principalRoot d : ℂ) ≠ 0 := by exact_mod_cast hτ0
    field_simp
    linear_combination (3 * π * Complex.I) * hquad
  have hcombine : Complex.exp (-π * Complex.I / 12 * (3 * (d : ℂ) - 12)) *
      Complex.exp ((3 : ℕ) * (π * Complex.I / (12 * (principalRoot d : ℂ)) *
        ((principalRoot d : ℂ) ^ 2 - 3 * (principalRoot d : ℂ) + 1))) = 1 := by
    rw [← Complex.exp_add, hexp0, Complex.exp_zero]
  rw [show (-1 : ℂ) * Complex.exp (-π * Complex.I / 12 * (3 * (d : ℂ) - 12)) *
        (Complex.exp ((3 : ℕ) * (π * Complex.I / (12 * (principalRoot d : ℂ)) *
            ((principalRoot d : ℂ) ^ 2 - 3 * (principalRoot d : ℂ) + 1))) /
          (doubleSine' 1 (principalRoot d) : ℂ) ^ 3) =
      -(Complex.exp (-π * Complex.I / 12 * (3 * (d : ℂ) - 12)) *
          Complex.exp ((3 : ℕ) * (π * Complex.I / (12 * (principalRoot d : ℂ)) *
            ((principalRoot d : ℂ) ^ 2 - 3 * (principalRoot d : ℂ) + 1)))) /
        (doubleSine' 1 (principalRoot d) : ℂ) ^ 3
      from by ring]
  rw [hcombine]
  push_cast
  ring

/-! ### The analytic origin value

At the origin, the required special value is the general boundary normalization `S₂(1; τ, 1) = √τ`,
proved from the defining Kurokawa--Koyama integral by `doubleSine_one`. The principal quadratic
relation also gives `j_{A_d}(ρ_d) = ρ_d³`; together these two elementary identities yield the value
predicted by [AFK25, Lemma 2.15, `lm:shinatzero`].
-/

/-- **Principal origin double-sine value**, the conclusion of [AFK25, Lemma 2.15,
`lm:shinatzero`]'s SF identification at the origin for the principal tuple: for every `d > 3`,
the elementary origin value `S₂(1, ρ_d)³` of the three-double-sine product equals
`√(j_{A_d}(ρ_d))`. Equivalent, by `principalNormGhostOverlapReal_zero`, to
`ν_d(0) = -1 / √(j_{A_d}(ρ_d))`.

The general boundary-period theorem `doubleSine_one` and
`principalJacobiFactor_eq_principalRoot_pow_three` prove it. -/
theorem doubleSine'_one_principalRoot_pow_three (d : ℕ) (hd : 3 < d) :
    doubleSine' 1 (principalRoot d) ^ 3 = Real.sqrt (principalJacobiFactor d) := by
  have hrho : 0 < principalRoot d := principalRoot_pos d hd
  have hsqrt_cube : Real.sqrt (principalRoot d ^ 3) =
      Real.sqrt (principalRoot d) ^ 3 := by
    rw [Real.sqrt_eq_iff_mul_self_eq (pow_nonneg hrho.le 3) (pow_nonneg (Real.sqrt_nonneg _) 3)]
    calc
      principalRoot d ^ 3 =
          (Real.sqrt (principalRoot d) * Real.sqrt (principalRoot d)) ^ 3 := by
            rw [Real.mul_self_sqrt hrho.le]
      _ = Real.sqrt (principalRoot d) ^ 3 * Real.sqrt (principalRoot d) ^ 3 := by ring
  rw [principalJacobiFactor_eq_principalRoot_pow_three d hd, hsqrt_cube]
  change doubleSine 1 (principalRoot d) 1 ^ 3 = Real.sqrt (principalRoot d) ^ 3
  rw [doubleSine_one (principalRoot d) hrho]

/-- The origin overlap is minus the inverse square root of the Jacobi factor,
`ν_d(0) = -1 / √(j_{A_d}(ρ_d))`, by `doubleSine'_one_principalRoot_pow_three`. -/
lemma principalNormGhostOverlapReal_zero_eq (d : RankOneDimension) :
    principalNormGhostOverlapReal d 0 = -(Real.sqrt (principalJacobiFactor d))⁻¹ := by
  rw [principalNormGhostOverlapReal_zero, doubleSine'_one_principalRoot_pow_three d d.property]

/-! ### [AFK25, Lemma 5.9, `lem:nu01overnu0val`] for the principal tuple

The unconditional boundary value and the preceding square-root calculation combine to evaluate
`ν_d(0) + ν_d(0)⁻¹`. This is the principal specialization of the cited origin identity.
-/

/-- The arithmetic core, stated for an arbitrary real number in the shape `x = -1/√j` produced by
`principalNormGhostOverlapReal_zero_eq`. No analytic input is used here. -/
theorem neg_inv_sqrt_principalJacobiFactor_add_inv (d : ℕ) (hd : 3 < d) {x : ℝ}
    (hx : x = -(Real.sqrt (principalJacobiFactor d))⁻¹) :
    x + x⁻¹ = -(((d : ℝ) - 2) * Real.sqrt ((d : ℝ) + 1)) := by
  have hspos : 0 < Real.sqrt (principalJacobiFactor d) :=
    Real.sqrt_pos.mpr (principalJacobiFactor_pos d hd)
  have hsne : Real.sqrt (principalJacobiFactor d) ≠ 0 := ne_of_gt hspos
  rw [hx, inv_neg, inv_inv, ← sqrt_principalJacobiFactor_add_inv d hd]
  ring

/-- **[AFK25, Lemma 5.9, `lem:nu01overnu0val`, equation (5.64)] at the principal tuple `t_d`.** The
source states `ν̃_0(t) + ν̃_0(t)⁻¹ = -(d - 2r)√(d_j + 1)`, which at `r = 1`, `d_j = d` reads
`ν̃_0(t_d) + ν̃_0(t_d)⁻¹ = -(d - 2)√(d + 1)`.

The source writes `ν̃_0(t)` for what this development calls `ν_d(0)`
(`principalNormGhostOverlap`); the origin correction there carries the source's sign factor
`(-1)^{s_d(0)} = -1`, after the exponential factors in the phase and cocycle cancel. Specializes
`AdmissibleTuple.IsAssociatedStabilizerPair.candidateNormGhostOverlap_zero_add_inv`, the lemma
for every admissible tuple, proved there from the value of the cocycle at the zero
characteristic; the proof here is the principal family's own, from the explicit double-sine
product. -/
theorem principalNormGhostOverlapReal_zero_add_inv (d : RankOneDimension) :
    principalNormGhostOverlapReal d 0 + (principalNormGhostOverlapReal d 0)⁻¹ =
      -(((d : ℝ) - 2) * Real.sqrt ((d : ℝ) + 1)) :=
  neg_inv_sqrt_principalJacobiFactor_add_inv d d.property (principalNormGhostOverlapReal_zero_eq d)

end SIC

end
