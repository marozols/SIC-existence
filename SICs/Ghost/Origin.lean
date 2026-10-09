/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Ghost.CandidateOverlaps
import SICs.Cocycle.FixedPointCharacter

/-!
# The candidate ghost overlap at the origin

Lemma 5.9 for every admissible tuple: `ν̃_t(0) = -1/√(j_{A_t}(ρ_t))` and `ν̃_t(0) + ν̃_t(0)⁻¹ = -(d
- 2r)√(d_j + 1)`.

Following [AFK25, Section 5.3, `sbsc:ghostprops`], this file evaluates the normalized candidate
ghost overlap `ν̃_t(0)` of an arbitrary admissible tuple `t = (d,r,Q) ∼ (K,j,m,Q)` and proves
[AFK25, Lemma 5.9, `lem:nu01overnu0val`]:

$$
\widetilde\nu_t(\mathbf 0) + \frac{1}{\widetilde\nu_t(\mathbf 0)} = -(d-2r)\sqrt{d_j+1}.
$$

The origin is the one index of the displacement expansion at which the characteristic `0/d` is
integral, so the reciprocal law `ν̃_t(p)ν̃_t(-p) = 1` of [AFK25, Theorem 5.8, `thm:nupnumpeq1`]
does not reach it; the sum identity above is what the idempotency argument of
[AFK25, Theorem 1.45, `thm:ghstExist`] uses there instead.

## Mathematical argument

The level generator `A_t` fixes `ρ_t = ρ_{Q,+}` with `j = j_{A_t}(ρ_t) > 0`. At the zero
characteristic the cocycle is `ש^0_{A_t}(ρ_t) = e^{πiΨ(A_t)/12}/√j`
(`sfModularCocycleRealTotal_zero_of_flt_eq_self`, the case `r = 0` of Kopp's Theorem 4.38 quoted
as [AFK25, Lemma 2.15, `lm:shinatzero`]), and the phase is `Φ_t(0) = -e^{-πiΨ(A_t)/12}`
(`AdmissibleTuple.sfPhase_zero`). Hence [AFK25, equation (5.65), `eq:nu01overnu0val`]:

$$
\widetilde\nu_t(\mathbf 0) = -\frac{1}{\sqrt{j}}.
$$

Since `det A_t = 1`, the Jacobi denominator and its inverse are the two eigenvalues of `A_t`, so
`j + j⁻¹ = Tr A_t` (`fltDenominator_add_inv_of_flt_eq_self`) and
`(√j + 1/√j)² = Tr A_t + 2 = (d - 2r)²(d_j + 1)`
(`IsAssociatedStabilizerPair.trace_A_add_two`), which is [AFK25, equations (5.69) and (5.70),
`eq:nu01overnu0val1`, `eq:nu01overnu0val2`] squared. Both `√j + 1/√j` and `d - 2r` are positive
(`2r < d - 1` for an admissible pair), so `√j + 1/√j = (d - 2r)√(d_j + 1)`, and the lemma follows.

## References

- [AFK25, Lemma 5.9, `lem:nu01overnu0val`; Lemma 2.15, `lm:shinatzero`]
- [72, Kopp (2024), Theorem 4.38, `thm:trivrmval`]
-/

noncomputable section

open Complex Real
open scoped MatrixGroups

namespace SIC

namespace AdmissibleTuple

/-! ### The origin value

The phase and the cocycle at the zero characteristic are both explicit, and their Rademacher
factors cancel. -/

/-- **The normalized candidate ghost overlap at the origin**, [AFK25, equation (5.65),
`eq:nu01overnu0val`]: at an associated stabilizer pair, `ν̃_t(0) = -1/√(j_{A_t}(ρ_t))`. The phase
`Φ_t(0) = -e^{-πiΨ(A_t)/12}` (`sfPhase_zero`) cancels the Rademacher factor of
`ש^0_{A_t}(ρ_t) = e^{πiΨ(A_t)/12}/√(j_{A_t}(ρ_t))` (`sfModularCocycleRealTotal_zero_of_flt_eq_self`,
at the fixed point `flt_A_rootPlus` with `fltDenominator_A_rootPlus_pos`). -/
theorem IsAssociatedStabilizerPair.candidateNormGhostOverlap_zero {t : AdmissibleTuple}
    {A Lz : SL(2, ℤ)} (h : t.IsAssociatedStabilizerPair A Lz) :
    t.candidateNormGhostOverlap A 0 =
      -((Real.sqrt (fltDenominator (A : Mat(2, ℤ)) t.Q.rootPlus) : ℝ) : ℂ)⁻¹ := by
  let hM := h.A_mem_gammaSubgroup (exists_intCast_mul_shiftRationalPoint t.d 0)
  have hM0 : A ∈ gammaSubgroup 0 :=
    h.A_mem_gammaSubgroup fun _ => ⟨0, by simp only [Pi.zero_apply, mul_zero, Int.cast_zero]⟩
  rw [candidateNormGhostOverlap_eq_sfPhase_mul h 0, sfPhase_zero,
    sfModularCocycleRealTotal_congr_index (shiftRationalPoint_zero t.d) hM hM0,
    sfModularCocycleRealTotal_zero_of_flt_eq_self t.form_admissible.rootPlus_irrational hM0
      h.fltDenominator_A_rootPlus_pos h.flt_A_rootPlus]
  rw [show -π * I / 12 * (rademacherInvariant A : ℂ) =
      -(π * I / 12 * (rademacherInvariant A : ℂ)) by ring, Complex.exp_neg]
  have hsqrt :
      ((Real.sqrt (fltDenominator (A : Mat(2, ℤ)) t.Q.rootPlus) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr h.fltDenominator_A_rootPlus_pos).ne'
  field_simp [Complex.exp_ne_zero, hsqrt]

/-! ### [AFK25, Lemma 5.9, `lem:nu01overnu0val`]

The trace identity `Tr A_t + 2 = (d - 2r)²(d_j + 1)` evaluates `√j + 1/√j`. -/

/-- Equality of nonnegative square roots applied to a positive number and its inverse. -/
private lemma sqrt_add_inv_eq_of_add_inv_add_two {j x : ℝ} (hj : 0 < j) (hx : 0 ≤ x)
    (h : j + j⁻¹ + 2 = x ^ 2) : Real.sqrt j + (Real.sqrt j)⁻¹ = x := by
  have hspos : 0 < Real.sqrt j := Real.sqrt_pos.mpr hj
  have hsq : Real.sqrt j ^ 2 = j := Real.sq_sqrt hj.le
  have hinv : (Real.sqrt j)⁻¹ ^ 2 = j⁻¹ := by rw [inv_pow, hsq]
  have hmul : Real.sqrt j * (Real.sqrt j)⁻¹ = 1 := mul_inv_cancel₀ hspos.ne'
  have hleft : 0 ≤ Real.sqrt j + (Real.sqrt j)⁻¹ := by positivity
  have hsquares : (Real.sqrt j + (Real.sqrt j)⁻¹) ^ 2 = x ^ 2 := by
    rw [add_sq, hsq, hinv, mul_assoc, hmul]
    linarith
  nlinarith

/-- **[AFK25, equations (5.69) and (5.70), `eq:nu01overnu0val1`, `eq:nu01overnu0val2`]**: the square
root of the Jacobi denominator `j = j_{A_t}(ρ_t)` and its inverse sum to `(d - 2r)√(d_j + 1)`.
Squaring gives `j + 2 + j⁻¹ = Tr A_t + 2 = (d - 2r)²(d_j + 1)`
(`fltDenominator_add_inv_of_flt_eq_self`, `IsAssociatedStabilizerPair.trace_A_add_two`), and both
sides are positive since `2r < d - 1`. -/
theorem IsAssociatedStabilizerPair.sqrt_fltDenominator_A_add_inv {t : AdmissibleTuple}
    {A Lz : SL(2, ℤ)} (h : t.IsAssociatedStabilizerPair A Lz) :
    Real.sqrt (fltDenominator (A : Mat(2, ℤ)) t.Q.rootPlus) +
        (Real.sqrt (fltDenominator (A : Mat(2, ℤ)) t.Q.rootPlus))⁻¹ =
      ((t.d : ℝ) - 2 * t.r) * Real.sqrt ((t.triple.towerDimension : ℝ) + 1) := by
  have hjpos := h.fltDenominator_A_rootPlus_pos
  have hdrNat : 2 * t.r < t.d := by
    have hrank : 2 * t.r < t.d - 1 := t.pair.rank_lt
    omega
  have hdrCast : (2 : ℝ) * (t.r : ℝ) < (t.d : ℝ) := by exact_mod_cast hdrNat
  have hdr : (0 : ℝ) < (t.d : ℝ) - 2 * t.r := sub_pos.mpr hdrCast
  have hd1 : Real.sqrt ((t.triple.towerDimension : ℝ) + 1) ^ 2 =
      (t.triple.towerDimension : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have hright : 0 ≤ ((t.d : ℝ) - 2 * t.r) *
      Real.sqrt ((t.triple.towerDimension : ℝ) + 1) := by positivity
  have hsum := fltDenominator_add_inv_of_flt_eq_self h.flt_A_rootPlus
    h.fltDenominator_A_rootPlus_pos.ne'
  have htrace := h.trace_A_add_two
  rw [Matrix.trace_fin_two] at htrace
  have htraceReal :
      (((A : Mat(2, ℤ)) 0 0 + A 1 1 : ℤ) : ℝ) + 2 =
        ((t.d : ℝ) - 2 * t.r) ^ 2 * ((t.triple.towerDimension : ℝ) + 1) := by
    exact_mod_cast htrace
  apply sqrt_add_inv_eq_of_add_inv_add_two hjpos hright
  rw [mul_pow, hd1]
  linarith [hsum, htraceReal]

/-- **[AFK25, Lemma 5.9, `lem:nu01overnu0val`]**: at an associated stabilizer pair,
`ν̃_t(0) + ν̃_t(0)⁻¹ = -(d - 2r)√(d_j + 1)`, from `ν̃_t(0) = -1/√j`
(`candidateNormGhostOverlap_zero`) and `√j + 1/√j = (d - 2r)√(d_j + 1)`
(`sqrt_fltDenominator_A_add_inv`). -/
@[source "AFK25, Lemma 5.9, p. 80, lem:nu01overnu0val"]
theorem IsAssociatedStabilizerPair.candidateNormGhostOverlap_zero_add_inv {t : AdmissibleTuple}
    {A Lz : SL(2, ℤ)} (h : t.IsAssociatedStabilizerPair A Lz) :
    t.candidateNormGhostOverlap A 0 + (t.candidateNormGhostOverlap A 0)⁻¹ =
      -((((t.d : ℝ) - 2 * t.r) * Real.sqrt ((t.triple.towerDimension : ℝ) + 1) : ℝ) : ℂ) := by
  rw [h.candidateNormGhostOverlap_zero, inv_neg, inv_inv, ← Complex.ofReal_inv, ← neg_add,
    add_comm, ← Complex.ofReal_add, h.sqrt_fltDenominator_A_add_inv]

end AdmissibleTuple

end SIC

end
