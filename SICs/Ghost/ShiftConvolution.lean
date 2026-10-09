/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Ghost.Origin
import SICs.Ghost.OverlapReciprocity
import SICs.Ghost.PhaseConvolution

/-!
# What a shift says about the candidate ghost overlaps

What a shift says about the overlaps: the phases of the convolution identity combine into
`ξ_d^{f_t(λ)⟨p,q⟩}`, so `∑_q ξ_d^{f_t(λ)⟨p,q⟩} ν̃_t(q)/ν̃_t(q - p) = 0`, and the excluded
convolution is `(d - 2r)√(d_j + 1) ν̃_t(p)`.

This file carries out the first half of the proof of [AFK25, Theorem 1.45, `thm:ghstExist`]
([AFK25, Section 5.4, `sbsc:proofofghosttheorem`]) for an arbitrary admissible tuple
`t = (d,r,Q) ∼ (K,j,m,Q)`: it rewrites the convolution identity [AFK25, equation (1.49),
`eq:tcc`] defining a shift `λ` ([AFK25, Definition 1.34, `dfn:shift`]) as an identity between the
normalized candidate ghost overlaps `ν̃_t`. The second half, which feeds the result into the
square of the candidate ghost operator, is in `SICs.Ghost.GhostProjector`.

## Mathematical argument

Write `f = f_t(λ) = r(2λ + d + d_j - 1)` ([AFK25, Definition 5.10, `dfn:functionht`]) and
`⟨·,·⟩` for the integral symplectic form. The summand of [AFK25, equation (1.49), `eq:tcc`] is
`ω_d^{r⟨p,(λI + L_{z,t})q⟩} ש^{q/d}_{A_t}(ρ_t) ש^{(q-p)/d}_{A_t⁻¹}(ρ_t)`.

1. *The phases.* With `Q = ⟨a,b,c⟩`, the defining formula
   `2L_{z,t} = (d_j - 1)I + (f_j/f)·2SQ` of [AFK25, Definition 1.28, `dfn:AssociatedStabilizers`]
   gives `2⟨p, L_{z,t}q⟩ = (d_j - 1)⟨p,q⟩ - (f_j/f)B(p,q)` with `B` the polar form of `Q`, and
   `f_{jm}/f = r f_j/f` turns the quadratic-form factors of the SF phase into the same polar form.
   The parity signs `(-1)^{s_d}` and the leftover `ξ_d^{rd⟨p,q⟩}` cancel because `r` is odd when
   `d` is even. The result is the identity

   $$
   \omega_d^{r\langle p,(\lambda I+L_{z,t})q\rangle}\,\Phi_t(q-p)\,\Phi_t(0)
     = \Phi_t(-p)\,\Phi_t(q)\,\xi_d^{f\langle p,q\rangle},
   $$

   This identity is supplied by `SICs.Ghost.PhaseConvolution`, following [AFK25, equation
   (5.89), `eq:RatioSFPhases`] and the exponent computation after [AFK25, equation (5.91),
   `eq:GhostProjSquaredMinusGhostProjB`].
2. *The cocycles.* At the fixed point `ρ_t`, `ש^s_{A_t⁻¹}(ρ_t) = (ש^s_{A_t}(ρ_t))⁻¹`
   ([AFK25, Lemma 2.13, `lm:sfam1sfaeq1`], `sfModularCocycleRealTotal_inv_of_lowerLeft_ne_zero`),
   which is [AFK25, equation (5.90), `eq:RatioSFModularCocycles`]. With `ν̃_t = Φ_t·ש` the summand
   becomes `(Φ_t(-p)/Φ_t(0))·ξ_d^{f⟨p,q⟩} ν̃_t(q)/ν̃_t(q-p)`, so a shift gives, for `p ≢ 0`,

   $$
   \sum_{q\in I_p} \xi_d^{f\langle p,q\rangle}\,
     \frac{\widetilde\nu_t(q)}{\widetilde\nu_t(q-p)} = 0.
   $$

3. *The excluded convolution.* The terms `q = 0` and `q = p` of that sum are `ν̃_t(0)ν̃_t(p)` and
   `ν̃_t(p)/ν̃_t(0)` (reciprocity), whose sum is `-(d - 2r)√(d_j + 1)ν̃_t(p)` by
   [AFK25, Lemma 5.9, `lem:nu01overnu0val`]. On the other terms reciprocity turns
   `1/ν̃_t(q - p)` into `ν̃_t(p - q)`, so

   $$
   \sum_{q\in I_p\setminus\{0,p\}} \xi_d^{f\langle p,q\rangle}\,
     \widetilde\nu_t(p-q)\,\widetilde\nu_t(q) = (d-2r)\sqrt{d_j+1}\;\widetilde\nu_t(p).
   $$

## References

- [AFK25, Theorem 1.45, `thm:ghstExist`, proof in Section 5.4, `sbsc:proofofghosttheorem`]
- [AFK25, Definition 1.34, `dfn:shift`; Definition 5.10, `dfn:functionht`; Lemma 5.9,
  `lem:nu01overnu0val`]
-/

noncomputable section

open Complex Real
open scoped MatrixGroups

namespace SIC

namespace AdmissibleTuple

/-! ### A shift makes the phased autocorrelation vanish

The convolution identity of a shift, rewritten through the phase identity and the inverse law of
the cocycle at the fixed point. -/

/-- At the fixed point of an associated stabilizer, the two cocycle factors in a convolution
summand are values at `q` and `q - p`, with the latter inverted. -/
private lemma sfModularCocycleReal'_convolution {t : AdmissibleTuple} {A Lz : SL(2, ℤ)}
    (h : t.IsAssociatedStabilizerPair A Lz) (p q : IntPhaseSpace) :
    sfModularCocycleReal' (shiftRationalPoint t.d q) A t.Q.rootPlus *
        sfModularCocycleReal'
          (shiftRationalPoint t.d q - shiftRationalPoint t.d p) A⁻¹ t.Q.rootPlus =
      sfModularCocycleRealTotal (shiftRationalPoint t.d q) A
          (h.A_mem_gammaSubgroup (exists_intCast_mul_shiftRationalPoint t.d q)) t.Q.rootPlus *
        (sfModularCocycleRealTotal (shiftRationalPoint t.d (q - p)) A
          (h.A_mem_gammaSubgroup
            (exists_intCast_mul_shiftRationalPoint t.d (q - p))) t.Q.rootPlus)⁻¹ := by
  rw [h.sfModularCocycleReal'_A, h.sfModularCocycleReal'_A_inv,
    sfModularCocycleRealTotal_inv_of_lowerLeft_ne_zero
      (h.A_mem_gammaSubgroup (exists_intCast_mul_shiftRationalPoint_sub t.d q p))
      h.lowerLeft_A_ne_zero h.fltDenominator_A_rootPlus_pos.ne' h.flt_A_rootPlus]
  congr 2
  exact sfModularCocycleRealTotal_congr_index
    (shiftRationalPoint_sub t.d q p) _ _ _

/-- The SF-phase quotient in a phased overlap summand is the SF-phase ratio at the endpoints
times the root-of-unity factor from the shift convolution. -/
private lemma sfPhase_div_convolution {t : AdmissibleTuple} {A Lz : SL(2, ℤ)}
    (h : t.IsAssociatedStabilizerPair A Lz) (lam : ℤ) (p q : IntPhaseSpace) :
    displacementPhase t.d ^
          (twistFnInt t.d t.r t.triple.towerDimension lam * intSymplecticForm p q) *
        t.sfPhase A q / t.sfPhase A (q - p) =
      (t.sfPhase A 0 / t.sfPhase A (-p)) *
        standardRoot t.d ^ ((t.r : ℤ) * intSymplecticForm p
          (shiftZaunerAction lam (Lz : Mat(2, ℤ)) q)) := by
  apply (div_eq_iff (t.sfPhase_ne_zero A (q - p))).2
  rw [show (t.sfPhase A 0 / t.sfPhase A (-p)) * standardRoot t.d ^
        ((t.r : ℤ) * intSymplecticForm p
          (shiftZaunerAction lam (Lz : Mat(2, ℤ)) q)) *
        t.sfPhase A (q - p) =
      (t.sfPhase A 0 * standardRoot t.d ^ ((t.r : ℤ) * intSymplecticForm p
        (shiftZaunerAction lam (Lz : Mat(2, ℤ)) q)) *
        t.sfPhase A (q - p)) / t.sfPhase A (-p) by
      rw [div_eq_mul_inv]
      ring]
  apply (eq_div_iff (t.sfPhase_ne_zero A (-p))).2
  calc
    _ = t.sfPhase A (-p) * t.sfPhase A q * displacementPhase t.d ^
        (twistFnInt t.d t.r t.triple.towerDimension lam * intSymplecticForm p q) := by ring
    _ = standardRoot t.d ^ ((t.r : ℤ) * intSymplecticForm p
          (shiftZaunerAction lam (Lz : Mat(2, ℤ)) q)) *
        t.sfPhase A (q - p) * t.sfPhase A 0 :=
      (h.sfPhase_convolution_identity lam p q).symm
    _ = _ := by ring

/-- Pointwise, a phased normalized-overlap quotient is the corresponding shift-convolution
summand multiplied by the constant `Φ_t(0) / Φ_t(-p)`. -/
private lemma candidateNormGhostOverlap_div_convolution {t : AdmissibleTuple}
    {A Lz : SL(2, ℤ)} (h : t.IsAssociatedStabilizerPair A Lz) (lam : ℤ)
    (p q : IntPhaseSpace) :
    displacementPhase t.d ^
          (twistFnInt t.d t.r t.triple.towerDimension lam * intSymplecticForm p q) *
        t.candidateNormGhostOverlap A q / t.candidateNormGhostOverlap A (q - p) =
      (t.sfPhase A 0 / t.sfPhase A (-p)) *
        (standardRoot t.d ^ ((t.r : ℤ) * intSymplecticForm p
            (shiftZaunerAction lam (Lz : Mat(2, ℤ)) q)) *
          sfModularCocycleReal' (shiftRationalPoint t.d q) A t.Q.rootPlus *
          sfModularCocycleReal'
            (shiftRationalPoint t.d q - shiftRationalPoint t.d p) A⁻¹ t.Q.rootPlus) := by
  let ph := t.sfPhase A
  let F := fun x : IntPhaseSpace =>
    sfModularCocycleRealTotal (shiftRationalPoint t.d x) A
      (h.A_mem_gammaSubgroup (exists_intCast_mul_shiftRationalPoint t.d x)) t.Q.rootPlus
  rw [candidateNormGhostOverlap_eq_sfPhase_mul h,
    candidateNormGhostOverlap_eq_sfPhase_mul h]
  change displacementPhase t.d ^ _ * (ph q * F q) / (ph (q - p) * F (q - p)) = _
  rw [show standardRoot t.d ^ ((t.r : ℤ) * intSymplecticForm p
        (shiftZaunerAction lam (Lz : Mat(2, ℤ)) q)) *
      sfModularCocycleReal' (shiftRationalPoint t.d q) A t.Q.rootPlus *
      sfModularCocycleReal'
        (shiftRationalPoint t.d q - shiftRationalPoint t.d p) A⁻¹ t.Q.rootPlus =
    standardRoot t.d ^ ((t.r : ℤ) * intSymplecticForm p
        (shiftZaunerAction lam (Lz : Mat(2, ℤ)) q)) *
      (sfModularCocycleReal' (shiftRationalPoint t.d q) A t.Q.rootPlus *
        sfModularCocycleReal'
          (shiftRationalPoint t.d q - shiftRationalPoint t.d p) A⁻¹ t.Q.rootPlus) by ring,
    sfModularCocycleReal'_convolution h]
  have hphase := sfPhase_div_convolution h lam p q
  change displacementPhase t.d ^ _ * ph q / ph (q - p) = _ at hphase
  calc
    _ = (displacementPhase t.d ^
          (twistFnInt t.d t.r t.triple.towerDimension lam * intSymplecticForm p q) *
        ph q / ph (q - p)) * (F q / F (q - p)) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    _ = ((ph 0 / ph (-p)) * standardRoot t.d ^
        ((t.r : ℤ) * intSymplecticForm p
          (shiftZaunerAction lam (Lz : Mat(2, ℤ)) q))) *
        (F q / F (q - p)) := by rw [hphase]
    _ = _ := by rw [div_eq_mul_inv]; ring

/-- **A shift makes the phased overlap autocorrelation vanish**: if `λ` is a shift for `t`, then
for `p ≢ 0 (mod d)` and every complete transversal `I` representing the classes of `0` and `p` by
`0` and `p`,
`∑_q ξ_d^{f_t(λ)⟨p,q⟩} ν̃_t(q)/ν̃_t(q - p) = 0`, the sum over the representatives `q` of `I`.
The convolution summand of [AFK25, equation (1.49), `eq:tcc`] is this summand times the nonzero
constant `Φ_t(-p)/Φ_t(0)` (`sfPhase_convolution_identity`, and the inverse law
`sfModularCocycleRealTotal_inv_of_lowerLeft_ne_zero` at the fixed point `ρ_t`). This is the display
after [AFK25, equation (5.84), `eq:GhostProjSquaredMinusGhostProj`] read backwards. -/
theorem IsShift.sum_candidateNormGhostOverlap_div_eq_zero {t : AdmissibleTuple}
    {A Lz : SL(2, ℤ)} (h : t.IsAssociatedStabilizerPair A Lz) {lam : ℤ}
    (hlam : t.IsShift A Lz lam) {p : IntPhaseSpace} (hp : intPhaseSpaceMod t.d p ≠ 0)
    (I : PhaseSpaceTransversal t.d) (hI0 : I.repr 0 = 0)
    (hIp : I.repr (intPhaseSpaceMod t.d p) = p) :
    ∑ q : PhaseSpaceMod t.d,
      displacementPhase t.d ^ (twistFnInt t.d t.r t.triple.towerDimension lam *
          intSymplecticForm p (I.repr q)) *
        t.candidateNormGhostOverlap A (I.repr q) /
          t.candidateNormGhostOverlap A (I.repr q - p) = 0 := by
  have hconv := hlam.convolution_eq p I hI0 hIp
  rw [ite_eq_right hp] at hconv
  rw [Finset.sum_congr rfl fun q _ =>
    candidateNormGhostOverlap_div_convolution h lam p (I.repr q), ← Finset.mul_sum]
  unfold shiftConvolutionSum at hconv
  rw [hconv, mul_zero]

/-! ### The excluded convolution

Removing the two endpoints `q = 0` and `q = p`, which [AFK25, Lemma 5.9, `lem:nu01overnu0val`]
evaluates, leaves the coefficient of `D_p` in the square of the nonidentity part of the candidate
ghost operator. -/

/-- Subtracting `P` from the representative of `q` subtracts the residue class of `P`. -/
private lemma intPhaseSpaceMod_repr_sub (d : ℕ) [NeZero d] (J : PhaseSpaceTransversal d)
    (P : IntPhaseSpace) (q : PhaseSpaceMod d) :
    intPhaseSpaceMod d (J.repr q - P) = q - intPhaseSpaceMod d P := by
  funext i
  change ((J.repr q i - P i : ℤ) : ZMod d) = q i - (P i : ZMod d)
  have hq : (J.repr q i : ZMod d) = q i := by
    simpa [intPhaseSpaceMod] using congrFun (J.residue_repr q) i
  rw [Int.cast_sub, hq]

/-- A phased quotient is its `q = 0` endpoint, its `q = P` endpoint, or the corresponding
excluded convolution term. -/
private lemma candidateNormGhostOverlap_div_term_decomposition {t : AdmissibleTuple}
    {A Lz : SL(2, ℤ)} (h : t.IsAssociatedStabilizerPair A Lz) (lam : ℤ)
    (P : IntPhaseSpace) (hP : intPhaseSpaceMod t.d P ≠ 0) (J : PhaseSpaceTransversal t.d)
    (hJ0 : J.repr 0 = 0) (hJP : J.repr (intPhaseSpaceMod t.d P) = P)
    (q : PhaseSpaceMod t.d) :
    displacementPhase t.d ^
          (twistFnInt t.d t.r t.triple.towerDimension lam *
            intSymplecticForm P (J.repr q)) *
        t.candidateNormGhostOverlap A (J.repr q) /
          t.candidateNormGhostOverlap A (J.repr q - P) =
      (if q = 0 then
        t.candidateNormGhostOverlap A 0 / t.candidateNormGhostOverlap A (-P) else 0) +
      (if q = intPhaseSpaceMod t.d P then
        t.candidateNormGhostOverlap A P / t.candidateNormGhostOverlap A 0 else 0) +
      (if q = 0 ∨ q = intPhaseSpaceMod t.d P then 0 else
        displacementPhase t.d ^
            (twistFnInt t.d t.r t.triple.towerDimension lam *
              intSymplecticForm P (J.repr q)) *
          t.candidateNormGhostOverlap A (P - J.repr q) *
            t.candidateNormGhostOverlap A (J.repr q)) := by
  let p := intPhaseSpaceMod t.d P
  let ν := t.candidateNormGhostOverlap A
  change displacementPhase t.d ^ _ * ν (J.repr q) / ν (J.repr q - P) =
    (if q = 0 then ν 0 / ν (-P) else 0) + (if q = p then ν P / ν 0 else 0) +
      (if q = 0 ∨ q = p then 0 else
        displacementPhase t.d ^ _ * ν (P - J.repr q) * ν (J.repr q))
  by_cases hq0 : q = 0
  · subst q
    simp [p, hJ0, intSymplecticForm, Ne.symm hP]
  by_cases hqp : q = p
  · subst q
    rw [ite_eq_right hq0, ite_eq_left rfl, ite_eq_left (Or.inr rfl), zero_add, hJP]
    simp only [sub_self]
    rw [show intSymplecticForm P P = 0 by
      simp [intSymplecticForm]
      ring, mul_zero, zpow_zero, one_mul]
    ring
  have hdiffne : intPhaseSpaceMod t.d (J.repr q - P) ≠ 0 := by
    rw [intPhaseSpaceMod_repr_sub]
    exact sub_ne_zero.mpr hqp
  have hrecip := h.candidateNormGhostOverlap_reciprocal (J.repr q - P) hdiffne
  have hneg : -(J.repr q - P) = P - J.repr q := by
    funext i
    simp
  rw [hneg] at hrecip
  have hinv : (ν (J.repr q - P))⁻¹ = ν (P - J.repr q) :=
    (eq_inv_of_mul_eq_one_right hrecip).symm
  rw [ite_eq_right hq0, ite_eq_right hqp, ite_eq_right (not_or_intro hq0 hqp), zero_add,
    div_eq_mul_inv, hinv]
  ring

/-- Summing the pointwise decomposition separates the two endpoints from the excluded
convolution. -/
private lemma sum_candidateNormGhostOverlap_div_decomposition {t : AdmissibleTuple}
    {A Lz : SL(2, ℤ)} (h : t.IsAssociatedStabilizerPair A Lz) (lam : ℤ)
    (P : IntPhaseSpace) (hP : intPhaseSpaceMod t.d P ≠ 0) (J : PhaseSpaceTransversal t.d)
    (hJ0 : J.repr 0 = 0) (hJP : J.repr (intPhaseSpaceMod t.d P) = P) :
    (∑ q : PhaseSpaceMod t.d,
      displacementPhase t.d ^
          (twistFnInt t.d t.r t.triple.towerDimension lam *
            intSymplecticForm P (J.repr q)) *
        t.candidateNormGhostOverlap A (J.repr q) /
          t.candidateNormGhostOverlap A (J.repr q - P)) =
      t.candidateNormGhostOverlap A 0 / t.candidateNormGhostOverlap A (-P) +
        t.candidateNormGhostOverlap A P / t.candidateNormGhostOverlap A 0 +
        ∑ q : PhaseSpaceMod t.d,
          if q = 0 ∨ q = intPhaseSpaceMod t.d P then 0 else
            displacementPhase t.d ^
                (twistFnInt t.d t.r t.triple.towerDimension lam *
                  intSymplecticForm P (J.repr q)) *
              t.candidateNormGhostOverlap A (P - J.repr q) *
                t.candidateNormGhostOverlap A (J.repr q) := by
  rw [Finset.sum_congr rfl fun q _ =>
    candidateNormGhostOverlap_div_term_decomposition h lam P hP J hJ0 hJP q,
    Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp

/-- The two endpoint terms are the origin identity multiplied by the overlap at `P`. -/
private lemma candidateNormGhostOverlap_div_endpoints {t : AdmissibleTuple}
    {A Lz : SL(2, ℤ)} (h : t.IsAssociatedStabilizerPair A Lz)
    (P : IntPhaseSpace) (hP : intPhaseSpaceMod t.d P ≠ 0) :
    t.candidateNormGhostOverlap A 0 / t.candidateNormGhostOverlap A (-P) +
        t.candidateNormGhostOverlap A P / t.candidateNormGhostOverlap A 0 =
      -(((((t.d : ℝ) - 2 * t.r) *
        Real.sqrt ((t.triple.towerDimension : ℝ) + 1) : ℝ) : ℂ)) *
        t.candidateNormGhostOverlap A P := by
  have hrecip := h.candidateNormGhostOverlap_reciprocal P hP
  rw [eq_inv_of_mul_eq_one_right hrecip, div_inv_eq_mul, div_eq_mul_inv]
  calc
    _ = (t.candidateNormGhostOverlap A 0 +
        (t.candidateNormGhostOverlap A 0)⁻¹) * t.candidateNormGhostOverlap A P := by ring
    _ = _ := by rw [h.candidateNormGhostOverlap_zero_add_inv]

/-- **The excluded convolution of a shift**: if `λ` is a shift for `t`, then for `P ≢ 0 (mod d)`
and every complete transversal `J` representing the classes of `0` and `P` by `0` and `P`,
`∑_{q ≠ 0, P} ξ_d^{f_t(λ)⟨P,q⟩} ν̃_t(P - q) ν̃_t(q) = (d - 2r)√(d_j + 1) ν̃_t(P)`.
The endpoints of `sum_candidateNormGhostOverlap_div_eq_zero` contribute
`(ν̃_t(0) + ν̃_t(0)⁻¹)ν̃_t(P)` (reciprocity, `candidateNormGhostOverlap_reciprocal`), which is
`-(d - 2r)√(d_j + 1)ν̃_t(P)` by [AFK25, Lemma 5.9, `lem:nu01overnu0val`]
(`candidateNormGhostOverlap_zero_add_inv`); on the remaining terms reciprocity turns
`ν̃_t(q)/ν̃_t(q - P)` into `ν̃_t(P - q)ν̃_t(q)`. This is the chain of displays after
[AFK25, equation (5.79), `eq:Pi2MinusPia`] in the proof of Theorem 1.45. -/
theorem IsShift.sum_excluded_candidateNormGhostOverlap_mul {t : AdmissibleTuple}
    {A Lz : SL(2, ℤ)} (h : t.IsAssociatedStabilizerPair A Lz) {lam : ℤ}
    (hlam : t.IsShift A Lz lam) {P : IntPhaseSpace} (hP : intPhaseSpaceMod t.d P ≠ 0)
    (J : PhaseSpaceTransversal t.d) (hJ0 : J.repr 0 = 0)
    (hJP : J.repr (intPhaseSpaceMod t.d P) = P) :
    (∑ q : PhaseSpaceMod t.d, if q = 0 ∨ q = intPhaseSpaceMod t.d P then 0 else
      displacementPhase t.d ^ (twistFnInt t.d t.r t.triple.towerDimension lam *
          intSymplecticForm P (J.repr q)) *
        t.candidateNormGhostOverlap A (P - J.repr q) * t.candidateNormGhostOverlap A (J.repr q)) =
      ((((t.d : ℝ) - 2 * t.r) * Real.sqrt ((t.triple.towerDimension : ℝ) + 1) : ℝ) : ℂ) *
        t.candidateNormGhostOverlap A P := by
  have hauto := IsShift.sum_candidateNormGhostOverlap_div_eq_zero h hlam hP J hJ0 hJP
  rw [sum_candidateNormGhostOverlap_div_decomposition h lam P hP J hJ0 hJP,
    candidateNormGhostOverlap_div_endpoints h P hP] at hauto
  linear_combination hauto

end AdmissibleTuple

end SIC

end
