/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Ghost.OverlapReciprocity
import SICs.Cocycle.FixedPointQuotient

/-!
# Real normalized ghost overlaps

The realness clause of Theorem 5.8 for every admissible tuple, `ν̃_t(p)² > 0`, from the positive
reflected quotient, and the tuple's `GhostOverlapData`.

This file proves the realness clause of [AFK25, Theorem 5.8, `thm:nupnumpeq1`] for every
admissible tuple `t`: at an associated stabilizer pair, the candidate normalized ghost overlap
`ν̃_t(p) = Φ_t(p)·ש^{p/d}_{A_t}(ρ_t)` is real for every `p ≢ 0 (mod d)`. With the reciprocal clause
of `SICs.Ghost.OverlapReciprocity` and the `d̄`-periodicity of `SICs.Ghost.CandidateOverlaps`, the
real parts then form the `GhostOverlapData` of the tuple, whose integer pullback away from the
zero residue class is the exact candidate overlap.

## Mathematical argument

Write `r = p/d`, `X = ש^r_{A_t}(ρ_t)` and `Y = ש^{-r}_{A_t}(ρ_t)`. The phase is even,
`Φ_t(-p) = Φ_t(p)` (`AdmissibleTuple.sfPhase_neg`), so `ν̃_t(p) = Φ_t(p)X` and
`ν̃_t(-p) = Φ_t(p)Y`, and the reciprocal clause reads `Φ_t(p)²XY = 1`. The reflected quotient is a
positive real, `X = cY` with `c > 0`
(`BinaryQF.IsAdmissible.exists_pos_sfModularCocycleRealTotal_eq_mul_neg`). Hence

$$
\widetilde\nu_t(\mathbf p)^2 = \Phi_t(\mathbf p)^2 X^2 = c\,\Phi_t(\mathbf p)^2 XY = c > 0,
$$

and a complex number whose square is a positive real is real. The source argues the same
positivity from [AFK25, Theorem 2.19, `thm:qpochmain`]: `ν̃_t(p)² = exp(nZ'_{d∞₂}(0,𝒜))` with
`Z'(0,𝒜)` real. Here the positivity comes from the value side of the same identity, Kopp's
`ש^r_A(β)/ש^{-r}_A(β) = U^{(1)}(r)^{-2}` at a reduced representative, which needs no ray class
data and holds for every conductor.

## References

- [AFK25, Theorem 5.8, `thm:nupnumpeq1`, and its proof; Definition 1.32, `dfn:GhostOverlaps`;
  Definition 1.11, `dfn:ghostFiducial`].
- [72, Kopp (2024), Theorem 8.2, `thm:mainrestate`; Proposition 7.20, `prop:almost`].
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### Realness of the normalized overlaps -/

/-- A complex number whose square is a positive real number has zero imaginary part. -/
private lemma complex_im_eq_zero_of_sq_eq_of_pos {z : ℂ} {c : ℝ} (hc : 0 < c)
    (hz : z ^ 2 = (c : ℂ)) : z.im = 0 := by
  have him : z.re * z.im = 0 := by
    have := congrArg Complex.im hz
    simp only [pow_two, Complex.mul_im, Complex.ofReal_im] at this
    linarith
  rcases mul_eq_zero.mp him with hre | him
  · have := congrArg Complex.re hz
    simp only [pow_two, Complex.mul_re, Complex.ofReal_re, hre, zero_mul, zero_sub] at this
    nlinarith [sq_nonneg z.im]
  · exact him

/-- **The square of `ν̃_t(p)` is a positive real** at an associated stabilizer pair, for
`p ≢ 0 (mod d)`: `ν̃_t(p)² = c` with `c > 0` the reflected quotient of
`BinaryQF.IsAdmissible.exists_pos_sfModularCocycleRealTotal_eq_mul_neg` at `ρ_t`, `r = p/d`,
`A_t`, combined with the reciprocal clause
`AdmissibleTuple.IsAssociatedStabilizerPair.candidateNormGhostOverlap_reciprocal` and the
evenness of the phase (`AdmissibleTuple.sfPhase_neg`, `shiftRationalPoint_neg`). -/
theorem AdmissibleTuple.IsAssociatedStabilizerPair.exists_pos_candidateNormGhostOverlap_sq_eq
    {t : AdmissibleTuple} {A Lz : SL(2, ℤ)} (h : t.IsAssociatedStabilizerPair A Lz)
    {p : IntPhaseSpace} (hp : intPhaseSpaceMod t.d p ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ t.candidateNormGhostOverlap A p ^ 2 = c := by
  have hd : 0 < t.d := Nat.zero_lt_of_lt t.three_lt_d
  have hM := h.A_mem_gammaSubgroup (exists_intCast_mul_shiftRationalPoint t.d p)
  obtain ⟨c, hc, hquotient⟩ :=
    t.form_admissible.exists_pos_sfModularCocycleRealTotal_eq_mul_neg
      (not_isIntegralIndex_shiftRationalPoint t.d hd hp) hM h.flt_A_rootPlus
      h.fltDenominator_A_rootPlus_pos
  have hreciprocal := h.candidateNormGhostOverlap_reciprocal p hp
  rw [AdmissibleTuple.candidateNormGhostOverlap_eq_sfPhase_mul h p,
    AdmissibleTuple.candidateNormGhostOverlap_eq_sfPhase_mul h (-p),
    AdmissibleTuple.sfPhase_neg] at hreciprocal
  simp only [shiftRationalPoint_neg] at hreciprocal
  let φ := t.sfPhase A p
  let X := sfModularCocycleRealTotal (shiftRationalPoint t.d p) A hM t.Q.rootPlus
  let Y := sfModularCocycleRealTotal (-shiftRationalPoint t.d p) A
    (neg_mem_gammaSubgroup hM) t.Q.rootPlus
  have hq : X = (c : ℂ) * Y := hquotient
  have hr : φ * X * (φ * Y) = 1 := hreciprocal
  refine ⟨c, hc, ?_⟩
  rw [AdmissibleTuple.candidateNormGhostOverlap_eq_sfPhase_mul h p]
  change (φ * X) ^ 2 = (c : ℂ)
  linear_combination (φ ^ 2 * X) * hq + (c : ℂ) * hr

/-- **[AFK25, Theorem 5.8, `thm:nupnumpeq1`], realness**: at an associated stabilizer pair the
candidate normalized ghost overlap `ν̃_t(p)` is real for every `p ≢ 0 (mod d)`, since its square is
a positive real (`exists_pos_candidateNormGhostOverlap_sq_eq`). -/
@[source "AFK25, Theorem 5.8, p. 80, thm:nupnumpeq1 (real)"]
theorem AdmissibleTuple.IsAssociatedStabilizerPair.candidateNormGhostOverlap_im_eq_zero
    {t : AdmissibleTuple} {A Lz : SL(2, ℤ)} (h : t.IsAssociatedStabilizerPair A Lz)
    {p : IntPhaseSpace} (hp : intPhaseSpaceMod t.d p ≠ 0) :
    (t.candidateNormGhostOverlap A p).im = 0 := by
  obtain ⟨c, hc, hsq⟩ := h.exists_pos_candidateNormGhostOverlap_sq_eq hp
  exact complex_im_eq_zero_of_sq_eq_of_pos hc hsq

/-- The real normalized overlap casts back to the complex one
(`candidateNormGhostOverlap_im_eq_zero`). -/
theorem AdmissibleTuple.IsAssociatedStabilizerPair.ofReal_re_candidateNormGhostOverlap
    {t : AdmissibleTuple} {A Lz : SL(2, ℤ)} (h : t.IsAssociatedStabilizerPair A Lz)
    {p : IntPhaseSpace} (hp : intPhaseSpaceMod t.d p ≠ 0) :
    (((t.candidateNormGhostOverlap A p).re : ℝ) : ℂ) = t.candidateNormGhostOverlap A p := by
  apply Complex.ext
  · simp only [Complex.ofReal_re]
  · simp only [Complex.ofReal_im, h.candidateNormGhostOverlap_im_eq_zero hp]

/-! ### The ghost overlap data of an admissible tuple

The real parts, read on `PhaseSpaceMod (dbar d)` through the canonical `ZMod.val` lift. By
`d̄`-periodicity away from the zero residue class
(`IsAssociatedStabilizerPair.candidateNormGhostOverlap_dbar_periodic`), every integer lift of a
class `p ≢ 0 (mod d)` gives the same value, so the reciprocal clause descends. The value on the
zero residue class is never used by a displacement sum and is left as the real part of the
totalized overlap at the canonical lift. -/

/-- The real normalized ghost overlap of `t` at `A`, indexed by `PhaseSpaceMod (dbar d)` through
the canonical lift `q ↦ (q₁.val, q₂.val)`. -/
def AdmissibleTuple.candidateNormGhostOverlapQuotient (t : AdmissibleTuple) (A : SL(2, ℤ))
    (q : PhaseSpaceMod (dbar t.d)) : ℝ :=
  (t.candidateNormGhostOverlap A (fun i => ((q i).val : ℤ))).re

/-- At an associated stabilizer pair the quotient-indexed overlap is the real part of the overlap
at any integer lift `p ≢ 0 (mod d)`, by `d̄`-periodicity
(`IsAssociatedStabilizerPair.candidateNormGhostOverlap_dbar_periodic`). -/
theorem AdmissibleTuple.IsAssociatedStabilizerPair.candidateNormGhostOverlapQuotient_eq
    {t : AdmissibleTuple} {A Lz : SL(2, ℤ)} (h : t.IsAssociatedStabilizerPair A Lz)
    {p : IntPhaseSpace} (hp : intPhaseSpaceMod t.d p ≠ 0) :
    t.candidateNormGhostOverlapQuotient A (intPhaseSpaceMod (dbar t.d) p) =
      (t.candidateNormGhostOverlap A p).re := by
  let _ : NeZero t.d := ⟨by have := t.three_lt_d; omega⟩
  unfold AdmissibleTuple.candidateNormGhostOverlapQuotient
  apply congrArg Complex.re
  apply h.candidateNormGhostOverlap_dbar_periodic _ hp
  funext i
  simp only [intPhaseSpaceMod, Int.cast_natCast, ZMod.natCast_zmod_val]

/-- **The ghost overlap data of an admissible tuple**: the real normalized overlaps of
[AFK25, Definition 1.11, `dfn:ghostFiducial`] for the candidate of [AFK25, Definition 1.32,
`dfn:GhostOverlaps`] at an associated stabilizer pair, `candidateNormGhostOverlapQuotient`, with
the reciprocal clause of [AFK25, Theorem 5.8, `thm:nupnumpeq1`]
(`candidateNormGhostOverlap_reciprocal`, `ofReal_re_candidateNormGhostOverlap`,
`candidateNormGhostOverlapQuotient_eq`). -/
def AdmissibleTuple.IsAssociatedStabilizerPair.ghostOverlapData
    {t : AdmissibleTuple} {A Lz : SL(2, ℤ)} (h : t.IsAssociatedStabilizerPair A Lz) :
    GhostOverlapData t.d where
  normalized := t.candidateNormGhostOverlapQuotient A
  reciprocal := by
    intro p hp
    have hpneg : intPhaseSpaceMod t.d (-p) ≠ 0 := by
      rw [intPhaseSpaceMod_neg, neg_ne_zero]
      exact hp
    rw [h.candidateNormGhostOverlapQuotient_eq hp,
      h.candidateNormGhostOverlapQuotient_eq hpneg]
    have hcomplex := h.candidateNormGhostOverlap_reciprocal p hp
    have hpos := h.ofReal_re_candidateNormGhostOverlap hp
    have hneg := h.ofReal_re_candidateNormGhostOverlap hpneg
    have hcast : ((((t.candidateNormGhostOverlap A p).re *
        (t.candidateNormGhostOverlap A (-p)).re : ℝ) : ℂ)) = 1 := by
      rw [Complex.ofReal_mul, hpos, hneg, hcomplex]
    exact_mod_cast hcast

/-- **The ghost overlap data recover the exact candidate overlaps**: for every integer
`p ≢ 0 (mod d)`, the value of `ghostOverlapData` at the class of `p` is `ν̃_t(p)`
(`candidateNormGhostOverlapQuotient_eq`, `ofReal_re_candidateNormGhostOverlap`). -/
theorem AdmissibleTuple.IsAssociatedStabilizerPair.ofReal_ghostOverlapData_normalized
    {t : AdmissibleTuple} {A Lz : SL(2, ℤ)} (h : t.IsAssociatedStabilizerPair A Lz)
    {p : IntPhaseSpace} (hp : intPhaseSpaceMod t.d p ≠ 0) :
    ((h.ghostOverlapData.normalized (intPhaseSpaceMod (dbar t.d) p) : ℝ) : ℂ) =
      t.candidateNormGhostOverlap A p := by
  change ((t.candidateNormGhostOverlapQuotient A
    (intPhaseSpaceMod (dbar t.d) p) : ℝ) : ℂ) = t.candidateNormGhostOverlap A p
  rw [h.candidateNormGhostOverlapQuotient_eq hp,
    h.ofReal_re_candidateNormGhostOverlap hp]

/-- **The ghost overlap data inherit [AFK25, Lemma 5.7, `lem:nupperiodicity`]**: away from the
zero class their integer pullback is the candidate overlap (`ofReal_ghostOverlapData_normalized`),
whose quasi-periodicity is `candidateNormGhostOverlap_quasiperiodic`. -/
theorem AdmissibleTuple.IsAssociatedStabilizerPair.ghostOverlapData_integerPullback_quasiperiodic
    {t : AdmissibleTuple} {A Lz : SL(2, ℤ)} (h : t.IsAssociatedStabilizerPair A Lz) :
    IsGhostOverlapQuasiperiodic t.d h.ghostOverlapData.integerPullback := by
  intro p p' hmod hp
  have hp' : intPhaseSpaceMod t.d p' ≠ 0 := by rwa [hmod]
  simp only [GhostOverlapData.integerPullback]
  rw [h.ofReal_ghostOverlapData_normalized hp', h.ofReal_ghostOverlapData_normalized hp]
  exact h.candidateNormGhostOverlap_quasiperiodic p p' hmod hp

end SIC

end
