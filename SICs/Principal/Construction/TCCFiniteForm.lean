/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Construction.ShiftSymmetry

/-!
# The Finite Character-Sum Form of the Principal TCC

Equivalent character-sum TCC over the finite phase space.

This file formalizes the **equivalent finite form** of the principal Twisted Convolution
Conjecture, `∑_q ξ_d^{⟨p,q⟩} μ_d(q)/μ_d(q-p) = d² δ_{p ≡ 0}`, as a first-class Lean
statement: `IsPrincipalRealShift d λ` is equivalent to a pure `ξ_d`-character sum identity
over the canonical transversal,

  `∑_{q} ξ_d^{(2λ-1)⟨p,q⟩} · ν̃_d(q)/ν̃_d(q-p) = d² δ_{p ≡ 0}`,

with no transversal quantification. This is the principal-family form of the convolution identity
[AFK25, Definition 1.34(2), `dfn:shift`, equation (1.49), `eq:tcc`], with two differences this
formalization forced. First, the source sums a product
`ש^{q/d}_{A_t}(ρ_t) · ש^{(q-p)/d}_{A_t⁻¹}(ρ_t)` of two cocycle values, whereas the sum below is
over the *ratio* `ν̃_d(q)/ν̃_d(q-p)` of phased overlaps. Second, the overlap in the denominator
must be the *quasi-periodically* extended phased overlap `principalPhasedGhostOverlap` (the
transport law of [AFK25, Lemma 5.7, `lem:nupperiodicity`]), not the naively `d`-periodic
extension of the canonical three-double-sine values. The two extensions differ by `±1` transport
signs in even dimensions; for odd `d` they coincide.

The equivalence direction "finite form → shift" needs the convolution sum for *every*
qualifying transversal; this is supplied by `principalRealShiftConvolutionSum_eq_of_modEq`,
which proves the sum depends only on residues.  The direction "shift → finite form" evaluates
the shift predicate at the canonical transversal and canonical representatives.  Neither
direction consumes any conjectural input; the content of the principal TCC is exactly the
vanishing of the character sum at the `d² - 1` nonzero residues (`p ≡ 0` is
`principalPhasedShiftSum_of_mod_eq_zero`, unconditional), proved as
`principalFiniteShiftTCC` in `SICs.Principal.Dilogarithm.TwistedConvolution`.

## Main declarations

- `principalPhasedShiftSum`: the finite `ξ_d`-character sum over canonical representatives.
- `sfPhase_zero_mul_principalRealShiftConvolutionSum`: the raw convolution sum over any
  transversal equals the finite sum, up to the `q`-independent SF-phase units.
- `principalPhasedShiftSum_of_mod_eq_zero`: the `p ≡ 0` instance holds unconditionally.
- `isPrincipalRealShift_iff_phasedShiftSum`: the shift predicate is the coprimality condition
  plus the finite character-sum identity for every `p`.
- `PrincipalFiniteShiftTCC`: the finite form of the `λ = 1` principal TCC, and
  `principalFiniteShiftTCC_iff` identifying it with `PrincipalRealShiftTCC`.

## References

- [AFK25, Definition 1.34, `dfn:shift`; Lemma 5.7, `lem:nupperiodicity`; Conjecture 1.35, `cnj:tci`]
-/

noncomputable section

namespace SIC

/-! ### The finite character sum

After substituting the principal overlap formula, the shift convolution becomes a finite character
sum of overlap ratios. Quasi-periodic extension is retained in the denominator, as required in
even dimensions.
-/

/-- The finite `ξ_d`-character sum of the equivalent finite form, for an arbitrary shift `λ`:
the sum over the canonical transversal of
`ξ_d^{(2λ-1)⟨p,q⟩} · ν̃_d(q)/ν̃_d(q-p)`, where `ν̃_d` is the quasi-periodically extended phased
overlap.  At `λ = 1` the exponent is `⟨p,q⟩`. -/
noncomputable def principalPhasedShiftSum (d : RankOneDimension)
    (lam : ℤ) (p : IntPhaseSpace) : ℂ :=
  ∑ c : PhaseSpaceMod d,
    displacementPhase d ^ ((2 * lam - 1) *
        intSymplecticForm p ((canonicalPhaseSpaceTransversal d).repr c)) *
      (principalPhasedGhostOverlap d ((canonicalPhaseSpaceTransversal d).repr c) /
        principalPhasedGhostOverlap d ((canonicalPhaseSpaceTransversal d).repr c - p))

/-- The raw convolution sum over an arbitrary transversal equals the finite character sum, up
to the `q`-independent SF-phase units on both sides.  This is the sum-level `μ`-form
conversion, composed with residue independence of the raw sum. -/
theorem sfPhase_zero_mul_principalRealShiftConvolutionSum (d : RankOneDimension)
    (lam : ℤ) (I : PhaseSpaceTransversal d) (p : IntPhaseSpace) :
    (principalRankOneAdmissibleTuple d).sfPhase (principalA d) (0 : IntPhaseSpace) *
        principalRealShiftConvolutionSum d lam I p =
      (principalRankOneAdmissibleTuple d).sfPhase (principalA d) (-p) *
        principalPhasedShiftSum d lam p := by
  rw [principalRealShiftConvolutionSum_eq_of_modEq d lam
    (canonicalPhaseSpaceTransversal d) I (rfl : intPhaseSpaceMod d p = intPhaseSpaceMod d p)]
  unfold principalRealShiftConvolutionSum principalPhasedShiftSum
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  set q := (canonicalPhaseSpaceTransversal d).repr c with hq
  have h := principalRealShiftSummand_mul_eq d lam p q
  have hν := principalPhasedGhostOverlap_ne_zero d (q - p)
  have hdiv : principalPhasedGhostOverlap d q /
        principalPhasedGhostOverlap d (q - p) *
        principalPhasedGhostOverlap d (q - p) =
      principalPhasedGhostOverlap d q :=
    div_mul_cancel₀ _ hν
  apply mul_right_cancel₀ hν
  linear_combination h -
    ((principalRankOneAdmissibleTuple d).sfPhase (principalA d) (-p) *
      displacementPhase d ^ ((2 * lam - 1) * intSymplecticForm p q)) * hdiv

/-- The `p ≡ 0` instance of the finite character sum holds unconditionally, for every shift. -/
theorem principalPhasedShiftSum_of_mod_eq_zero (d : RankOneDimension)
    (lam : ℤ) (p : IntPhaseSpace) (hp : intPhaseSpaceMod d p = 0) :
    principalPhasedShiftSum d lam p = (d : ℂ) ^ 2 := by
  have hph0 := principalSFPhase_ne_zero d (0 : IntPhaseSpace)
  have hphneg : (principalRankOneAdmissibleTuple d).sfPhase (principalA d) (-p) =
      (principalRankOneAdmissibleTuple d).sfPhase (principalA d) (0 : IntPhaseSpace) :=
    principalSFPhase_of_mod_eq_zero d (-p) (by rw [intPhaseSpaceMod_neg, hp]; simp)
  have hconv := sfPhase_zero_mul_principalRealShiftConvolutionSum d lam
    (canonicalPhaseSpaceTransversal d) p
  have hzero : intPhaseSpaceMod d p = intPhaseSpaceMod d (0 : IntPhaseSpace) := by
    rw [hp]
    funext i
    simp [intPhaseSpaceMod]
  rw [principalRealShiftConvolutionSum_eq_of_modEq d lam
      (canonicalPhaseSpaceTransversal d) (canonicalPhaseSpaceTransversal d) hzero,
    principalRealShiftConvolutionSum_zero d lam, hphneg] at hconv
  exact (mul_left_cancel₀ hph0 hconv).symm

/-! ### The equivalence with the shift predicate

Representative independence lets the canonical finite identity recover the convolution identity
for every allowed transversal. Thus the finite character sum is equivalent to the exact real
shift predicate.
-/

/-- **The equivalent finite form of the principal shift predicate**, for an arbitrary shift:
`λ` is a
principal real shift exactly when the coprimality condition holds and the finite
`ξ_d`-character sum equals `d² δ_{p ≡ 0}` for every integer `p`.  All transversal
quantification is eliminated. -/
theorem isPrincipalRealShift_iff_phasedShiftSum (d : RankOneDimension) (lam : ℤ) :
    IsPrincipalRealShift d lam ↔
      ((principalRankOneAdmissibleTuple d).IsShiftCoprime lam ∧
        ∀ p : IntPhaseSpace,
          principalPhasedShiftSum d lam p =
            if intPhaseSpaceMod d p = 0 then (d : ℂ) ^ 2 else 0) := by
  have hph0 := principalSFPhase_ne_zero d (0 : IntPhaseSpace)
  constructor
  · rintro ⟨hcop, hconv⟩
    refine ⟨hcop, fun p => ?_⟩
    by_cases hp0 : intPhaseSpaceMod d p = 0
    · rw [ite_eq_left hp0]
      exact principalPhasedShiftSum_of_mod_eq_zero d lam p hp0
    · rw [ite_eq_right hp0]
      set P := canonicalIntPhaseSpaceRep d p with hP
      have hPmod := intPhaseSpaceMod_canonicalIntPhaseSpaceRep d p
      have hraw := hconv P (canonicalPhaseSpaceTransversal d)
        (canonicalPhaseSpaceTransversal_repr_zero d)
        (by rw [hPmod, canonicalPhaseSpaceTransversal_repr_mod])
      rw [ite_eq_right (by rw [hPmod]; exact hp0)] at hraw
      have hswap : principalRealShiftConvolutionSum d lam
          (canonicalPhaseSpaceTransversal d) p =
          principalRealShiftConvolutionSum d lam (canonicalPhaseSpaceTransversal d) P :=
        principalRealShiftConvolutionSum_eq_of_modEq d lam
          (canonicalPhaseSpaceTransversal d) (canonicalPhaseSpaceTransversal d) hPmod.symm
      have hconv2 := sfPhase_zero_mul_principalRealShiftConvolutionSum d lam
        (canonicalPhaseSpaceTransversal d) p
      rw [hswap, hraw, mul_zero] at hconv2
      have hphneg := principalSFPhase_ne_zero d (-p)
      exact (mul_eq_zero.mp hconv2.symm).resolve_left hphneg
  · rintro ⟨hcop, hfin⟩
    refine ⟨hcop, fun p I hI0 hIp => ?_⟩
    have hconv2 := sfPhase_zero_mul_principalRealShiftConvolutionSum d lam I p
    rw [hfin p] at hconv2
    by_cases hp0 : intPhaseSpaceMod d p = 0
    · rw [ite_eq_left hp0] at hconv2 ⊢
      have hphneg : (principalRankOneAdmissibleTuple d).sfPhase (principalA d) (-p) =
          (principalRankOneAdmissibleTuple d).sfPhase (principalA d)
            (0 : IntPhaseSpace) :=
        principalSFPhase_of_mod_eq_zero d (-p) (by rw [intPhaseSpaceMod_neg, hp0]; simp)
      rw [hphneg] at hconv2
      exact mul_left_cancel₀ hph0 hconv2
    · rw [ite_eq_right hp0] at hconv2 ⊢
      rw [mul_zero] at hconv2
      exact (mul_eq_zero.mp hconv2).resolve_left hph0

/-! ### The finite form of the principal TCC

Specializing the preceding equivalence at `λ = 1` packages the principal TCC input as one explicit
finite identity in each dimension. This is a computational presentation of the same proposition.
-/

/-- **The finite character-sum form of the principal single-shift restriction of
[AFK25, Conjecture 1.35, `cnj:tci`]**, quantified over every dimension and integer point:
for every `d > 3` and `p ∈ ℤ²`,
`∑_q ξ_d^{⟨p,q⟩} ν̃_d(q)/ν̃_d(q-p) = d² δ_{p ≡ 0}`.  Its `p ≡ 0` instances are the unconditional
`principalPhasedShiftSum_of_mod_eq_zero`.

`principalFiniteShiftTCC_iff` identifies it with `PrincipalRealShiftTCC`. The theorem
`principalFiniteShiftTCC` in `SICs.Principal.Dilogarithm.TwistedConvolution` proves it by
[RW26, Radchenko, Wheeler (2026), Theorem 7, `thm:ghostsic`]. -/
def PrincipalFiniteShiftTCC : Prop :=
  ∀ d : RankOneDimension,
    ∀ p : IntPhaseSpace,
      principalPhasedShiftSum d 1 p =
        if intPhaseSpaceMod d p = 0 then (d : ℂ) ^ 2 else 0

/-- The finite character-sum form is equivalent to the principal single-shift TCC: the
coprimality half of the shift condition holds unconditionally at `λ = 1`, so only the character
sum remains. -/
theorem principalFiniteShiftTCC_iff :
    PrincipalFiniteShiftTCC ↔ PrincipalRealShiftTCC := by
  unfold PrincipalFiniteShiftTCC PrincipalRealShiftTCC
  constructor
  · intro h d
    exact (isPrincipalRealShift_iff_phasedShiftSum d 1).mpr
      ⟨isShiftCoprime_principal_one d d.property, h d⟩
  · intro h d
    exact ((isPrincipalRealShift_iff_phasedShiftSum d 1).mp (h d)).2

end SIC

end
