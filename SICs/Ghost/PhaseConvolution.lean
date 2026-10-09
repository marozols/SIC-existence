/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Ghost.Phase
import SICs.Admissible.StabilizerDomain
import SICs.Ghost.Shifts
import SICs.Ghost.TwistFunctions

/-!
# The phase in the shifted convolution

The phase identity converting the shift convolution into a convolution of ghost overlaps.

This is the phase calculation in [AFK25, Section 5.4, `sbsc:proofofghosttheorem`], using
[AFK25, Definition 1.30, `dfn:SFKPhase`; Definition 5.10, `dfn:functionht`].
The doubled associated Zauner matrix expresses its symplectic pairing through the polar form
of the tuple's quadratic form. Combining that identity with the signs in the two SF phases
leaves exactly the displacement phase with exponent `f_t(λ)⟨p,q⟩`. The remaining even exponent
contributes one. `SICs.Ghost.ShiftConvolution` applies this arithmetic identity to the cocycle
convolution defining a shift.
-/

noncomputable section

open Complex Real
open scoped MatrixGroups

namespace SIC

namespace AdmissibleTuple

/-! ### The phase identity of the convolution

The Shintani--Faddeev phases of the convolution summand combine into a single power of `ξ_d`,
with the exponent `f_t(λ)` of [AFK25, Definition 5.10, `dfn:functionht`]. The exponent
comparison leaves a multiple of `d`; its displacement phase cancels the difference between
the parity signs, since their remaining exponent is even. -/

/-- The doubled Zauner action pairs with the polar form of `Q`; this is the matrix calculation
used by `IsAssociatedStabilizerPair.sfPhase_convolution_identity`. -/
private lemma twice_intSymplecticForm_Lz {t : AdmissibleTuple} {A Lz : SL(2, ℤ)}
    (h : t.IsAssociatedStabilizerPair A Lz) (p q : IntPhaseSpace) :
    2 * intSymplecticForm p ((Lz : Mat(2, ℤ)).mulVec q) =
      ((t.triple.towerDimension : ℤ) - 1) * intSymplecticForm p q -
        (t.towerConductorRatio : ℤ) *
          (2 * t.Q.a * p 0 * q 0 + t.Q.b * (p 0 * q 1 + p 1 * q 0) +
            2 * t.Q.c * p 1 * q 1) := by
  simp only [intSymplecticForm, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have h00 := h.twice_Lz_upperLeft
  have h01 := h.twice_Lz_upperRight
  have h10 := h.twice_Lz_lowerLeft
  have h11 := h.twice_Lz_lowerRight
  linear_combination p 1 * q 0 * h00 + p 1 * q 1 * h01 -
    p 0 * q 0 * h10 - p 0 * q 1 * h11

/-- The product of two SF phases has one sign and one power of `ξ_d`. This is the phase
factorization used by `IsAssociatedStabilizerPair.sfPhase_convolution_identity`. -/
private lemma sfPhase_mul (t : AdmissibleTuple) (A : SL(2, ℤ)) (x y : IntPhaseSpace) :
    t.sfPhase A x * t.sfPhase A y =
      Complex.exp (-π * I / 12 * (rademacherInvariant A : ℂ)) ^ 2 *
        ((-1 : ℂ) ^ (sfSignExp t.d x + sfSignExp t.d y) *
          displacementPhase t.d ^
            (-(t.conductorRatio : ℤ) * t.Q.eval (x 0) (x 1) -
              (t.conductorRatio : ℤ) * t.Q.eval (y 0) (y 1))) := by
  simp only [sfPhase]
  rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
    show -(t.conductorRatio : ℤ) * t.Q.eval (x 0) (x 1) -
        (t.conductorRatio : ℤ) * t.Q.eval (y 0) (y 1) =
      -((t.conductorRatio : ℤ) * t.Q.eval (x 0) (x 1)) +
        -((t.conductorRatio : ℤ) * t.Q.eval (y 0) (y 1)) by ring,
    zpow_add₀ (displacementPhase_ne_zero t.d)]
  ring

/-- Multiplying a product of SF phases by a power of `ξ_d` adds that power to the combined
quadratic exponent. -/
private lemma displacementPhase_zpow_mul_sfPhase_mul (t : AdmissibleTuple) (A : SL(2, ℤ))
    (a : ℤ) (x y : IntPhaseSpace) :
    displacementPhase t.d ^ a * (t.sfPhase A x * t.sfPhase A y) =
      Complex.exp (-π * I / 12 * (rademacherInvariant A : ℂ)) ^ 2 *
        ((-1 : ℂ) ^ (sfSignExp t.d x + sfSignExp t.d y) *
          displacementPhase t.d ^
            (a - (t.conductorRatio : ℤ) * t.Q.eval (x 0) (x 1) -
              (t.conductorRatio : ℤ) * t.Q.eval (y 0) (y 1))) := by
  rw [sfPhase_mul]
  rw [show displacementPhase t.d ^ a *
        (Complex.exp (-π * I / 12 * (rademacherInvariant A : ℂ)) ^ 2 *
          ((-1 : ℂ) ^ (sfSignExp t.d x + sfSignExp t.d y) *
            displacementPhase t.d ^
              (-(t.conductorRatio : ℤ) * t.Q.eval (x 0) (x 1) -
                (t.conductorRatio : ℤ) * t.Q.eval (y 0) (y 1)))) =
      Complex.exp (-π * I / 12 * (rademacherInvariant A : ℂ)) ^ 2 *
        ((-1 : ℂ) ^ (sfSignExp t.d x + sfSignExp t.d y) *
          (displacementPhase t.d ^ a * displacementPhase t.d ^
            (-(t.conductorRatio : ℤ) * t.Q.eval (x 0) (x 1) -
              (t.conductorRatio : ℤ) * t.Q.eval (y 0) (y 1)))) by ring]
  rw [← zpow_add₀ (displacementPhase_ne_zero t.d)]
  rw [show a + (-(t.conductorRatio : ℤ) * t.Q.eval (x 0) (x 1) -
      (t.conductorRatio : ℤ) * t.Q.eval (y 0) (y 1)) =
    a - (t.conductorRatio : ℤ) * t.Q.eval (x 0) (x 1) -
      (t.conductorRatio : ℤ) * t.Q.eval (y 0) (y 1) by ring]

/-- The specialization of `displacementPhase_zpow_mul_sfPhase_mul` with the second phase at the
origin removes the zero quadratic value. -/
private lemma displacementPhase_zpow_mul_sfPhase_mul_zero (t : AdmissibleTuple)
    (A : SL(2, ℤ)) (a : ℤ) (x : IntPhaseSpace) :
    displacementPhase t.d ^ a * (t.sfPhase A x * t.sfPhase A 0) =
      Complex.exp (-π * I / 12 * (rademacherInvariant A : ℂ)) ^ 2 *
        ((-1 : ℂ) ^ (sfSignExp t.d x + sfSignExp t.d 0) *
          displacementPhase t.d ^
            (a - (t.conductorRatio : ℤ) * t.Q.eval (x 0) (x 1))) := by
  rw [displacementPhase_zpow_mul_sfPhase_mul]
  have hQ0 : t.Q.eval ((0 : IntPhaseSpace) 0) ((0 : IntPhaseSpace) 1) = 0 := by
    simp [BinaryQF.eval]
  rw [hQ0, mul_zero, sub_zero]

/-- A power of `ω_d = ξ_d²` is the corresponding doubled power of `ξ_d`. -/
private lemma standardRoot_zpow_eq_displacementPhase_zpow (d : ℕ) [NeZero d] (a : ℤ) :
    standardRoot d ^ a = displacementPhase d ^ (2 * a) := by
  rw [← displacementPhase_sq]
  change (displacementPhase d ^ (2 : ℤ)) ^ a = _
  rw [← zpow_mul]

/-- The sign exponents in the convolution phase identity differ by the indicated bilinear
correction. -/
private lemma sfSignExp_convolution (t : AdmissibleTuple) (p q : IntPhaseSpace) :
    sfSignExp t.d (q - p) + sfSignExp t.d 0 =
      sfSignExp t.d (-p) + sfSignExp t.d q -
        ((t.d + 1 : ℕ) : ℤ) * (q 0 * p 1 + p 0 * q 1) := by
  simp [sfSignExp]
  ring

/-- The powers of `ξ_d` in the convolution phase identity differ by a multiple of `d`. -/
private lemma sfPhase_convolution_exponent {t : AdmissibleTuple} {A Lz : SL(2, ℤ)}
    (h : t.IsAssociatedStabilizerPair A Lz) (lam : ℤ) (p q : IntPhaseSpace) :
    2 * (t.r : ℤ) * intSymplecticForm p
          (shiftZaunerAction lam (Lz : Mat(2, ℤ)) q) -
        (t.conductorRatio : ℤ) * t.Q.eval ((q - p) 0) ((q - p) 1) =
      (-(t.conductorRatio : ℤ) * t.Q.eval ((-p) 0) ((-p) 1) -
          (t.conductorRatio : ℤ) * t.Q.eval (q 0) (q 1) +
          twistFnInt t.d t.r t.triple.towerDimension lam * intSymplecticForm p q) +
        (t.d : ℤ) * (-((t.r : ℤ) * intSymplecticForm p q)) := by
  have hratio : (t.conductorRatio : ℤ) =
      (t.r : ℤ) * (t.towerConductorRatio : ℤ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℤ))
      (t.conductorRatio_eq_rank_mul.trans (congrArg (fun n => n * t.towerConductorRatio)
        t.r_eq_rank.symm))
  have hact : 2 * intSymplecticForm p
      (shiftZaunerAction lam (Lz : Mat(2, ℤ)) q) =
        2 * lam * intSymplecticForm p q +
          2 * intSymplecticForm p ((Lz : Mat(2, ℤ)).mulVec q) := by
    simp only [shiftZaunerAction, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, intSymplecticForm]
    ring
  simp only [BinaryQF.eval, Pi.sub_apply, Pi.neg_apply, neg_mul, twistFnInt]
  rw [hratio]
  linear_combination (t.r : ℤ) * twice_intSymplecticForm_Lz h p q +
    (t.r : ℤ) * hact

/-- The residual sign in the convolution phase identity has even exponent. -/
private lemma sfPhase_convolution_even (t : AdmissibleTuple) (p q : IntPhaseSpace) :
    Even (((t.d + 1 : ℕ) : ℤ) *
      (-((t.r : ℤ) * intSymplecticForm p q) - (q 0 * p 1 + p 0 * q 1))) := by
  rcases Nat.even_or_odd t.d with hd | hd
  · obtain ⟨k, hk⟩ := t.pair.odd_r_of_even_d hd
    have hr : (t.r : ℤ) = 2 * (k : ℤ) + 1 := by exact_mod_cast hk
    have hinner : Even
        (-((t.r : ℤ) * intSymplecticForm p q) - (q 0 * p 1 + p 0 * q 1)) := by
      refine ⟨-(k + 1) * p 1 * q 0 + k * p 0 * q 1, ?_⟩
      simp only [intSymplecticForm, hr]
      ring
    exact hinner.mul_left _
  · have hd1 : Even (((t.d + 1 : ℕ) : ℤ)) := by exact_mod_cast hd.add_one
    exact hd1.mul_right _

/-- The signs and quadratic powers in `IsAssociatedStabilizerPair.sfPhase_convolution_identity`
agree after the residual even sign is removed. -/
private lemma sfPhase_convolution_sign_eq {t : AdmissibleTuple} {A Lz : SL(2, ℤ)}
    (h : t.IsAssociatedStabilizerPair A Lz) (lam : ℤ) (p q : IntPhaseSpace) :
    (-1 : ℂ) ^ (sfSignExp t.d (q - p) + sfSignExp t.d 0) *
        displacementPhase t.d ^
          (2 * (t.r : ℤ) * intSymplecticForm p
              (shiftZaunerAction lam (Lz : Mat(2, ℤ)) q) -
            (t.conductorRatio : ℤ) * t.Q.eval ((q - p) 0) ((q - p) 1)) =
      (-1 : ℂ) ^ (sfSignExp t.d (-p) + sfSignExp t.d q) *
        displacementPhase t.d ^
          (-(t.conductorRatio : ℤ) * t.Q.eval ((-p) 0) ((-p) 1) -
            (t.conductorRatio : ℤ) * t.Q.eval (q 0) (q 1) +
            twistFnInt t.d t.r t.triple.towerDimension lam * intSymplecticForm p q) :=
  neg_one_zpow_mul_displacementPhase_zpow_eq t.d _ _ _ _
    (q 0 * p 1 + p 0 * q 1) (-((t.r : ℤ) * intSymplecticForm p q))
    (sfSignExp_convolution t p q) (sfPhase_convolution_exponent h lam p q)
    (sfPhase_convolution_even t p q)

/-- **The SF phases of the convolution identity**: for an associated stabilizer pair and every
`λ`, `p`, `q`,
`ω_d^{r⟨p,(λI + L_{z,t})q⟩} Φ_t(q - p) Φ_t(0) = Φ_t(-p) Φ_t(q) ξ_d^{f_t(λ)⟨p,q⟩}`.
This is [AFK25, equation (5.89), `eq:RatioSFPhases`] together with the reduction of its exponent to
`f_t(λ)` after [AFK25, equation (5.91), `eq:GhostProjSquaredMinusGhostProjB`]; see the module
docstring. Only the defining formula `twice_Lz_eq` of `L_{z,t}` is used. -/
theorem IsAssociatedStabilizerPair.sfPhase_convolution_identity {t : AdmissibleTuple}
    {A Lz : SL(2, ℤ)} (h : t.IsAssociatedStabilizerPair A Lz) (lam : ℤ) (p q : IntPhaseSpace) :
    standardRoot t.d ^ ((t.r : ℤ) *
        intSymplecticForm p (shiftZaunerAction lam (Lz : Mat(2, ℤ)) q)) *
        t.sfPhase A (q - p) * t.sfPhase A 0 =
      t.sfPhase A (-p) * t.sfPhase A q *
        displacementPhase t.d ^ (twistFnInt t.d t.r t.triple.towerDimension lam *
          intSymplecticForm p q) := by
  let e := intSymplecticForm p
    (shiftZaunerAction lam (Lz : Mat(2, ℤ)) q)
  let u := intSymplecticForm p q
  have hphase := sfPhase_convolution_sign_eq h lam p q
  rw [standardRoot_zpow_eq_displacementPhase_zpow]
  rw [show displacementPhase t.d ^ (2 * ((t.r : ℤ) * e)) * t.sfPhase A (q - p) *
      t.sfPhase A 0 = displacementPhase t.d ^ (2 * ((t.r : ℤ) * e)) *
        (t.sfPhase A (q - p) * t.sfPhase A 0) by ring,
    displacementPhase_zpow_mul_sfPhase_mul_zero]
  rw [show t.sfPhase A (-p) * t.sfPhase A q * displacementPhase t.d ^
      (twistFnInt t.d t.r t.triple.towerDimension lam * u) =
    displacementPhase t.d ^ (twistFnInt t.d t.r t.triple.towerDimension lam * u) *
      (t.sfPhase A (-p) * t.sfPhase A q) by ring,
    displacementPhase_zpow_mul_sfPhase_mul]
  rw [show 2 * ((t.r : ℤ) * e) = 2 * (t.r : ℤ) * e by ring]
  dsimp only [e, u]
  rw [show twistFnInt t.d t.r t.triple.towerDimension lam * intSymplecticForm p q -
      (t.conductorRatio : ℤ) * t.Q.eval ((-p) 0) ((-p) 1) -
      (t.conductorRatio : ℤ) * t.Q.eval (q 0) (q 1) =
    -(t.conductorRatio : ℤ) * t.Q.eval ((-p) 0) ((-p) 1) -
      (t.conductorRatio : ℤ) * t.Q.eval (q 0) (q 1) +
      twistFnInt t.d t.r t.triple.towerDimension lam * intSymplecticForm p q by ring]
  rw [hphase]

end AdmissibleTuple

end SIC

end
