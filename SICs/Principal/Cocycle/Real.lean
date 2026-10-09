/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Cocycle.PoleAvoidance

/-!
# Real Shintani--Faddeev Cocycle for the Principal Family

Exact real cocycle values at `A_d`/`A_d⁻¹`, the principal real shift predicate, and the statement
`PrincipalRealShiftTCC`.

This file defines the real-line Shintani--Faddeev modular cocycle at `A_d` and `A_d⁻¹` from the
word product, using the identities in `SICs.Principal.Cocycle.SFReduction`. These values give the
principal specialization of [AFK25, Definition 1.34, `dfn:shift`] without evaluating the
upper-half-plane product at the real quadratic point `ρ_d`.

The value at `A_d` is the three-factor word decomposition of `σ_{A_d}`, divided by its finite
`q`-Pochhammer correction. The origin is separate because its canonical shift data differ from the
nonzero reduction and because its phased value has the sign proved by
`sfPhase_zero_mul_sigmaSBase_zero_cube`. Values in a nonzero residue class are obtained from
canonical representatives, using the integer-shift invariance at a fixed point from
[AFK25, Lemma 2.14, `lm:shinperiodicity`]. That lemma excludes integral rational indices; the
definition totalizes the zero residue class by its canonical origin value. In every convolution
identity asserted by `IsPrincipalRealShift`, the transversal hypotheses force the two zero-class
cocycle arguments to be literally zero, so this totalization introduces no extra mathematical
assumption.

For `A_d⁻¹`, [AFK25, equation (1.28)] gives the reciprocal of the `A_d`-value at the inverse image
of the rational index. `principalAInvIndexPair_eq_reduction` proves that this image is congruent to
the original index modulo `d`; hence its canonical representative is unchanged. This is the
principal, real-domain use of the inverse-index arithmetic of
`SICs.Principal.Cocycle.CanonicalReduction`.

The declarations here do not assert that `1` is a shift.  `PrincipalRealShiftTCC` is the
principal restriction of the Twisted Convolution Conjecture, stated using the exact real values;
it is proved as `principalRealShiftTCC` in `SICs.Principal.Dilogarithm.TwistedConvolution`,
from
[RW26, Radchenko, Wheeler (2026), Theorem 7, `thm:ghostsic`].  The general
`AdmissibleTuple.IsShift` evaluates the exact real-line cocycle of `SICs.Cocycle.Modular.Values`
as well; the principal declarations here compute that value in closed form.

## Main declarations

- `principalSigmaAdCanonical`: the real three-factor word value `σ_{A_d}(z,ρ_d)`.
- `principalSFModularCocycleAdCanonical`: the corresponding modular cocycle at a canonical pair.
- `principalSFModularCocycleAd`: the value at an arbitrary integer index, with
  `principalSFModularCocycleAd_eq_canonical` identifying it at a canonical pair.
- `principalSFModularCocycleAdInv`: the inverse-matrix value from the cocycle relation.
- `principalRealShiftConvolutionSum`: the principal real form of
  [AFK25, equation (1.49), `eq:tcc`].
- `IsPrincipalRealShift`: the principal real shift predicate.
- `PrincipalRealShiftTCC`: the principal real single-shift statement.

## References

- [AFK25, Definition 1.18, `def:shin`, equation (1.26), `eq:shindf`] and
  [AFK25, Definition 1.34, `dfn:shift`, equations (1.28), (1.49), `eq:tcc`]
- [AFK25, Lemma 2.14, `lm:shinperiodicity`]
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### The real cocycle at `A_d`

The canonical word product is divided by the finite `q`-Pochhammer factor from the modular
cocycle definition. Canonical reduction then extends this exact real value to every integer index.
-/

/-- The real-line value `σ_{A_d}(z,ρ_d)` defined by the word product at the canonical pair `(p,q)`.

For a nonzero canonical pair this is [AFK25, equation (8.5), `eq:sfjldecom`] evaluated using the
three explicit `sigmaS` decompositions supplied by `principalZ_div_principalRoot_eq` and
`principalZ_div_principalRoot_sq_eq`. At the origin all three word arguments are zero and carry zero
shift, so the value is `sigmaSBase 0 ρ_d` cubed. Bounds are imposed by the theorems that
identify this formula, rather than as proof arguments to the definition. -/
noncomputable def principalSigmaAdCanonical (d : ℕ) (p q : ℤ) : ℂ :=
  if p = 0 ∧ q = 0 then
    sigmaSBase 0 (principalRoot d) ^ 3
  else
    sigmaS (principalZ d p q) (principalRoot d) 0 0 *
      sigmaS (principalDoubleSineArg d p (principalThirdIndex d p q) - 1)
        (principalRoot d) 0 (-principalReductionK d p q) *
      sigmaS (principalDoubleSineArg d (principalThirdIndex d p q) q - 1)
        (principalRoot d) (principalReductionK d p q) (-principalReductionL d p q)

/-- The exact real Shintani--Faddeev cocycle value `ש^{(p/d,q/d)}_{A_d}(ρ_d)` at a canonical
index pair. It divides the real Jacobi word value by the finite `q`-Pochhammer factor in
`sfModularCocycleReal`; `principalN_shift_eq_neg_nQP` identifies its integer index as
`-principalReductionL d p q`. -/
noncomputable def principalSFModularCocycleAdCanonical (d : ℕ) (p q : ℤ) : ℂ :=
  principalSigmaAdCanonical d p q /
    qPochhammerFin (-principalReductionL d p q)
      (principalZ d p q / principalJacobiFactor d) (principalRoot d)

/-- Away from the origin, the principal real cocycle times the SF phase equals the
three-double-sine overlap. -/
theorem sfPhase_mul_principalSFModularCocycleAdCanonical (d : ℕ) (hd : 3 < d)
    (p q : ℤ) (hp0 : 0 ≤ p) (hp1 : p < (d : ℤ)) (hq0 : 0 ≤ q) (hq1 : q < (d : ℤ))
    (hne : ¬(p = 0 ∧ q = 0)) :
    (principalRankOneAdmissibleTuple ⟨d, hd⟩).sfPhase (principalA d) ![p, q] *
        principalSFModularCocycleAdCanonical d p q =
      (principalTripleDoubleSine d p q : ℂ) := by
  rw [principalSFModularCocycleAdCanonical, principalSigmaAdCanonical, ite_eq_right hne]
  simpa only [mul_div_assoc] using
    principal_sf_reduction2_eq_one_unconditional d hd p q hp0 hp1 hq0 hq1 hne

/-- At the origin, the principal real cocycle satisfies the sign identity proved in
`SICs.Principal.Ghost.Origin`. -/
theorem sfPhase_mul_principalSFModularCocycleAdCanonical_zero
    (d : RankOneDimension) :
    (principalRankOneAdmissibleTuple d).sfPhase (principalA d) (0 : IntPhaseSpace) *
        principalSFModularCocycleAdCanonical d 0 0 =
      principalNormGhostOverlap d (0 : IntPhaseSpace) := by
  rw [principalSFModularCocycleAdCanonical, principalSigmaAdCanonical, ite_eq_left ⟨rfl, rfl⟩]
  simpa [principalReductionL, qPochhammerFin] using
    sfPhase_zero_mul_sigmaSBase_zero_cube d

/-- The exact real principal `A_d` cocycle at an arbitrary integer index. On nonzero residue
classes, canonical reduction follows from invariance of the modular cocycle at a fixed point
under translating its rational index by `ℤ²` (`sfModularCocycleReal_add_intVec`, applied in
`SICs.Principal.Cocycle.ModularValues.sfModularCocycleReal_principalA_intIndex`). On the zero
residue class this definition uses the origin value as an auxiliary convention, which need not
equal the source's cocycle at other integral characteristics. The qualifying transversals in
`IsPrincipalRealShift` only evaluate that class at the literal origin. -/
noncomputable def principalSFModularCocycleAd (d : ℕ) (p : IntPhaseSpace) : ℂ :=
  principalSFModularCocycleAdCanonical d (canonicalIntPhaseSpaceRep d p 0)
    (canonicalIntPhaseSpaceRep d p 1)

/-- At a canonical index pair the arbitrary-index value *is* the canonical one: reducing a
coordinate already in `{0, …, d-1}` modulo `d` changes nothing. This is the bridge between the
two named `A_d` values, needed wherever a theorem proved at canonical pairs
(`sfPhase_mul_principalSFModularCocycleAdCanonical`, say) has to be read off
`principalSFModularCocycleAd`. -/
theorem principalSFModularCocycleAd_eq_canonical (d : ℕ) (p q : ℤ)
    (hp0 : 0 ≤ p) (hp1 : p < (d : ℤ)) (hq0 : 0 ≤ q) (hq1 : q < (d : ℤ)) :
    principalSFModularCocycleAd d ![p, q] = principalSFModularCocycleAdCanonical d p q := by
  rw [principalSFModularCocycleAd]
  congr 1 <;>
    simp [canonicalIntPhaseSpaceRep, Int.emod_eq_of_lt hp0 hp1, Int.emod_eq_of_lt hq0 hq1]

/-- The principal real `A_d` cocycle depends only on the integer index modulo `d`, as is explicit
in its canonical-representative construction. -/
theorem principalSFModularCocycleAd_eq_of_modEq (d : ℕ) (p p' : IntPhaseSpace)
    (hmod : intPhaseSpaceMod d p' = intPhaseSpaceMod d p) :
    principalSFModularCocycleAd d p' = principalSFModularCocycleAd d p := by
  have hcan := canonicalIntPhaseSpaceRep_eq_of_mod_eq d hmod
  rw [principalSFModularCocycleAd, principalSFModularCocycleAd, hcan]

/-- The exact real principal `A_d` cocycle never vanishes at a canonical index pair.  This
follows from the origin/non-origin identities: the three-double-sine overlap is
nonzero, as is the transported principal overlap at the origin. Since the value is a quotient, this
also says its `q`-Pochhammer denominator has no zero there -- the non-pole condition of
`sfModularCocycleReal` for the one matrix the principal Twisted Convolution
Conjecture
evaluates. -/
theorem principalSFModularCocycleAdCanonical_ne_zero (d : RankOneDimension) (p q : ℤ)
    (hp0 : 0 ≤ p) (hp1 : p < (d : ℤ)) (hq0 : 0 ≤ q) (hq1 : q < (d : ℤ)) :
    principalSFModularCocycleAdCanonical d p q ≠ 0 := by
  by_cases hzero : p = 0 ∧ q = 0
  · rw [hzero.1, hzero.2]
    intro h
    have horigin := sfPhase_mul_principalSFModularCocycleAdCanonical_zero d
    rw [h, mul_zero] at horigin
    exact principalNormGhostOverlap_ne_zero d 0 horigin.symm
  · intro h
    have hnonzero := sfPhase_mul_principalSFModularCocycleAdCanonical
      d d.property p q hp0 hp1 hq0 hq1 hzero
    rw [h, mul_zero] at hnonzero
    exact (Complex.ofReal_ne_zero.mpr (principalTripleDoubleSine_ne_zero d p q)) hnonzero.symm

/-- The exact real principal `A_d` cocycle never vanishes, at an arbitrary integer index: its
canonical representative is canonical. -/
theorem principalSFModularCocycleAd_ne_zero (d : RankOneDimension)
    (p : IntPhaseSpace) : principalSFModularCocycleAd d p ≠ 0 :=
  principalSFModularCocycleAdCanonical_ne_zero d _ _
    (canonicalIntPhaseSpaceRep_nonneg (by omega) p 0) (canonicalIntPhaseSpaceRep_lt (by omega) p 0)
    (canonicalIntPhaseSpaceRep_nonneg (by omega) p 1) (canonicalIntPhaseSpaceRep_lt (by omega) p 1)

/-! ### The real cocycle at `A_d⁻¹`

The inverse-cocycle relation expresses the `A_d⁻¹` value as the reciprocal of the `A_d` value at
the transformed index. The explicit reduction data makes this a total nonvanishing function.
-/

/-- The exact real principal `A_d⁻¹` cocycle at an arbitrary integer index.  The inverse-cocycle
relation [AFK25, equation (1.28)] identifies it with the reciprocal of the `A_d`-value at the raw
inverse image of the index. The latter is reduced canonically by
`principalAInvIndexPair_eq_reduction`. -/
noncomputable def principalSFModularCocycleAdInv (d : ℕ) (p : IntPhaseSpace) : ℂ :=
  (principalSFModularCocycleAd d (principalAInvIndexPair d (p 0) (p 1)))⁻¹

/-- Canonical reduction of the raw inverse image agrees with canonical reduction of the original
index, since `A_d⁻¹(p,q) = (p-dm₂, q+dm₁)` (`principalAInvIndexPair_eq_reduction`). -/
lemma canonicalIntPhaseSpaceRep_principalAInvIndexPair_eq (d : ℕ) (p q : ℤ) :
    canonicalIntPhaseSpaceRep d (principalAInvIndexPair d p q) =
      canonicalIntPhaseSpaceRep d ![p, q] := by
  rw [principalAInvIndexPair_eq_reduction]
  funext i
  fin_cases i
  · change (p - (d : ℤ) * principalAInvReductionM2 d p q) % (d : ℤ) = p % (d : ℤ)
    rw [show p - (d : ℤ) * principalAInvReductionM2 d p q =
        p + (d : ℤ) * (-principalAInvReductionM2 d p q) by ring,
      Int.add_mul_emod_self_left]
  · change (q + (d : ℤ) * principalAInvReductionM1 d p q) % (d : ℤ) = q % (d : ℤ)
    rw [Int.add_mul_emod_self_left]

/-- Because `A_d⁻¹ ≡ I (mod d)`, the real inverse-matrix cocycle is simply the reciprocal of the
`A_d` cocycle at the same integer index.  The proof uses the explicit inverse-index reduction,
rather than assuming periodicity of the raw index action. -/
theorem principalSFModularCocycleAdInv_eq_inv (d : ℕ) (p : IntPhaseSpace) :
    principalSFModularCocycleAdInv d p = (principalSFModularCocycleAd d p)⁻¹ := by
  have hp : ![p 0, p 1] = p := by
    funext i
    fin_cases i <;> rfl
  have hcan := canonicalIntPhaseSpaceRep_principalAInvIndexPair_eq d (p 0) (p 1)
  rw [hp] at hcan
  unfold principalSFModularCocycleAdInv principalSFModularCocycleAd
  rw [hcan]

/-- The two principal real cocycle values satisfy the inverse-cocycle product relation exactly. -/
theorem principalSFModularCocycleAdInv_mul_self (d : RankOneDimension)
    (p : IntPhaseSpace) :
    principalSFModularCocycleAdInv d p * principalSFModularCocycleAd d p = 1 := by
  rw [principalSFModularCocycleAdInv_eq_inv]
  exact inv_mul_cancel₀ (principalSFModularCocycleAd_ne_zero d p)

/-- The principal real `A_d⁻¹` cocycle also depends only on the integer index modulo `d`. -/
theorem principalSFModularCocycleAdInv_eq_of_modEq (d : ℕ) (p p' : IntPhaseSpace)
    (hmod : intPhaseSpaceMod d p' = intPhaseSpaceMod d p) :
    principalSFModularCocycleAdInv d p' = principalSFModularCocycleAdInv d p := by
  rw [principalSFModularCocycleAdInv_eq_inv, principalSFModularCocycleAdInv_eq_inv,
    principalSFModularCocycleAd_eq_of_modEq d p p' hmod]

/-! ### The principal real shift predicate

Substituting the exact real cocycles into [AFK25, Definition 1.34, `dfn:shift`] gives a concrete
convolution sum and shift predicate. The sum depends only on residues modulo `d`, so it is
independent of the chosen lifts.
-/

/-- Specializes `AdmissibleTuple.shiftConvolutionSum` to the principal family on the real domain.
Both sums evaluate the real cocycle defined by the word product; this sum uses its principal
values at the concrete matrices `A_d` and `L_{z,t_d} = U_d`, where the general sum evaluates
`sfModularCocycleReal'` at an arbitrary associated stabilizer. -/
noncomputable def principalRealShiftConvolutionSum (d : ℕ) (lam : ℤ) [NeZero d]
    (I : PhaseSpaceTransversal d) (p : IntPhaseSpace) : ℂ :=
  ∑ c : PhaseSpaceMod d,
    (standardRoot d) ^ intSymplecticForm p
        (shiftZaunerAction lam (principalU d : Mat(2, ℤ)) (I.repr c)) *
      principalSFModularCocycleAd d (I.repr c) *
      principalSFModularCocycleAdInv d (I.repr c - p)

/-- An integer `λ` is a shift for the principal tuple `t_d`, with `A_t=A_d` and `L_{z,t}=U_d`,
stated entirely with the exact real principal cocycle; it retains the source's quantification over
every integer point and every complete transversal containing `0` and that point. -/
def IsPrincipalRealShift (d : RankOneDimension) (lam : ℤ) : Prop :=
  (principalRankOneAdmissibleTuple d).IsShiftCoprime lam ∧
    ∀ (p : IntPhaseSpace) (I : PhaseSpaceTransversal d),
      I.repr 0 = 0 → I.repr (intPhaseSpaceMod d p) = p →
      principalRealShiftConvolutionSum d lam I p =
        if intPhaseSpaceMod d p = 0 then (d : ℂ) ^ 2 else 0

/-- The shifted-Zauner symplectic exponent changes by a multiple of `d` under congruent
phase-space data. -/
private lemma dvd_intSymplecticForm_shiftZaunerAction_sub (d : ℕ) (lam : ℤ)
    (M : Mat(2, ℤ)) {p p' q q' : IntPhaseSpace}
    (hp : intPhaseSpaceMod d p' = intPhaseSpaceMod d p)
    (hq : intPhaseSpaceMod d q' = intPhaseSpaceMod d q) :
    (d : ℤ) ∣ intSymplecticForm p' (shiftZaunerAction lam M q') -
      intSymplecticForm p (shiftZaunerAction lam M q) := by
  obtain ⟨a, ha⟩ := exists_eq_add_smul_of_intPhaseSpaceMod_eq d hp
  obtain ⟨b, hb⟩ := exists_eq_add_smul_of_intPhaseSpaceMod_eq d hq
  set Y := (lam • (1 : Mat(2, ℤ)) + M).mulVec b with hY
  have hact : shiftZaunerAction lam M q' = shiftZaunerAction lam M q + (d : ℤ) • Y := by
    rw [hb]
    unfold shiftZaunerAction
    rw [Matrix.mulVec_add, Matrix.mulVec_smul]
  refine ⟨intSymplecticForm p Y + intSymplecticForm a (shiftZaunerAction lam M q) +
    (d : ℤ) * intSymplecticForm a Y, ?_⟩
  rw [ha, hact, intSymplecticForm_add_smul_left, intSymplecticForm_add_smul,
    intSymplecticForm_add_smul]
  ring

/-- The principal real convolution sum depends only on the residues of `p` and of the chosen
representatives: any two transversals, and any two congruent integer points, give the same
sum. -/
theorem principalRealShiftConvolutionSum_eq_of_modEq (d : ℕ) (lam : ℤ) [NeZero d]
    (I I' : PhaseSpaceTransversal d) {p p' : IntPhaseSpace}
    (hp : intPhaseSpaceMod d p' = intPhaseSpaceMod d p) :
    principalRealShiftConvolutionSum d lam I' p' =
      principalRealShiftConvolutionSum d lam I p := by
  unfold principalRealShiftConvolutionSum
  refine Finset.sum_congr rfl fun c _ => ?_
  have hq : intPhaseSpaceMod d (I'.repr c) = intPhaseSpaceMod d (I.repr c) := by
    rw [I.residue_repr, I'.residue_repr]
  have hdiff : intPhaseSpaceMod d (I'.repr c - p') = intPhaseSpaceMod d (I.repr c - p) := by
    funext i
    have h1 := congrFun hq i
    have h2 := congrFun hp i
    simpa [intPhaseSpaceMod] using congrArg₂ (· - ·) h1 h2
  rw [principalSFModularCocycleAd_eq_of_modEq d (I.repr c) (I'.repr c) hq,
    principalSFModularCocycleAdInv_eq_of_modEq d (I.repr c - p) (I'.repr c - p') hdiff,
    standardRoot_zpow_eq_of_dvd_sub
      (dvd_intSymplecticForm_shiftZaunerAction_sub d lam _ hp hq)]

/-- The principal-family, real-domain single-shift restriction of
[AFK25, Conjecture 1.35, `cnj:tci`]: `λ = 1` is a shift for every `d > 3`, with the shift condition
read through the exact real values of this file.

`principalRealShiftTCC` in `SICs.Principal.Dilogarithm.TwistedConvolution` proves it by
[RW26, Radchenko, Wheeler (2026), Theorem 7, `thm:ghostsic`]. -/
def PrincipalRealShiftTCC : Prop :=
  ∀ d : RankOneDimension, IsPrincipalRealShift d 1

end SIC

end
