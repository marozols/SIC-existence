/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Ghost.Shifts
import SICs.Ghost.TwistFunctions

/-!
# Compatible twists for arbitrary admissible tuples

Compatible twists in `GL₂(ℤ/d̄ℤ)` for arbitrary admissible tuples.

This file formalizes the effective twist condition in [AFK25, Definition 1.41, `def:fiducialdata`]
for an arbitrary admissible tuple. A twist is represented faithfully as an element of
`GL₂(ℤ / dbar d ℤ)`. The auxiliary integer predicate records the displayed determinant congruence
for a lift; `isCompatibleTwist_iff_of_isGhostTwistLift` proves that the two formulations agree for
every lift.

The existence theorem uses the full unit group modulo `dbar d`: it imposes no artificial
requirement that an integer lift have determinant `±1`.

## Main definitions and results

- `AdmissibleTuple.IsCompatibleTwist`: [AFK25, Definition 1.41, `def:fiducialdata`] with a
  quotient-valued twist.
- `AdmissibleTuple.IsCompatibleTwistLift`: its displayed integer determinant congruence.
- `AdmissibleTuple.isCompatibleTwist_iff_of_isGhostTwistLift`: equivalence for every lift.
- `AdmissibleTuple.IsCompatibleTwistLift.det_isCoprime`,
  `AdmissibleTuple.IsCompatibleTwistLift.displacementPhase_zpow_eq`: a compatible lift has
  determinant invertible modulo `d̄`, and moves the phase `ξ_d^{⟨p,q⟩}` to `ξ_d^{f_t(λ)⟨Gp,Gq⟩}`.
- `AdmissibleTuple.exists_isCompatibleTwist_iff`: compatible twists exist exactly for shifts
  satisfying [AFK25, Definition 1.34, `dfn:shift`](1).

## References

- [AFK25] Appleby, Flammia, Kopp, arXiv:2501.03970v2, Definitions 1.34, 1.41, and 5.10;
  Lemma 5.11
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

namespace AdmissibleTuple

/-! ### Compatibility and independence of the integer lift

The quotient-valued twist condition is compared with its determinant congruence for any integral
lift. A compatible lift has determinant inverse to `f_t(λ)` modulo `dbar d`, which moves the
displacement phase to the twisted indices. -/

/-- The integer-lift form of `IsCompatibleTwist`:
`Det(G) r (2λ + d_j - 1 + d) ≡ 1 (mod dbar d)`.

This predicate does not require `Det(G) = ±1`; when `G` lifts a quotient-valued twist, its
determinant need only be coprime to `dbar d`. -/
def IsCompatibleTwistLift (t : AdmissibleTuple) (lam : ℤ)
    (G : Mat(2, ℤ)) : Prop :=
  G.det * (t.r : ℤ) *
      (2 * lam + (t.triple.towerDimension : ℤ) - 1 + (t.d : ℤ)) ≡ 1
    [ZMOD (dbar t.d : ℤ)]

/-- A quotient-valued twist `g ∈ GL₂(ℤ / dbar d ℤ)` is compatible with the admissible tuple `t`
and integer representative `λ` of a shift when it satisfies the determinant condition of
[AFK25, Definition 1.41, `def:fiducialdata`]. -/
@[source "AFK25, Definition 1.41, p. 20, def:fiducialdata (twist condition)"]
def IsCompatibleTwist (t : AdmissibleTuple) (lam : ℤ) (g : GhostTwist t.d) : Prop :=
  ((g : Mat(2, ZMod (dbar t.d))).det) * (t.r : ZMod (dbar t.d)) *
      ((2 * lam + (t.triple.towerDimension : ℤ) - 1 + (t.d : ℤ) : ℤ) :
        ZMod (dbar t.d)) = 1

/-- For any integer lift `G` of a quotient-valued twist `g`, compatibility of `g` is equivalent to
the integer determinant congruence `IsCompatibleTwistLift` for `G`.

This is the bridge that lets later arithmetic arguments choose a convenient lift without changing
the quotient-level condition. -/
theorem isCompatibleTwist_iff_of_isGhostTwistLift (t : AdmissibleTuple) (lam : ℤ)
    (g : GhostTwist t.d) (G : Mat(2, ℤ)) (hG : IsGhostTwistLift G g) :
    t.IsCompatibleTwist lam g ↔ t.IsCompatibleTwistLift lam G := by
  change G.map (fun x : ℤ => (x : ZMod (dbar t.d))) =
    (g : Mat(2, ZMod (dbar t.d))) at hG
  rw [IsCompatibleTwist, IsCompatibleTwistLift, ← ZMod.intCast_eq_intCast_iff]
  push_cast
  rw [hG]

/-- Compatibility of the canonical balanced integer lift is equivalent to compatibility of the
quotient-valued twist. -/
theorem isCompatibleTwist_iff_integerLift (t : AdmissibleTuple) (lam : ℤ)
    (g : GhostTwist t.d) :
    t.IsCompatibleTwist lam g ↔ t.IsCompatibleTwistLift lam g.integerLift :=
  t.isCompatibleTwist_iff_of_isGhostTwistLift lam g g.integerLift g.integerLift_isLift

/-- Rewrite the integer compatible-twist condition as
`Det(G) f_t(λ) ≡ 1 (mod dbar d)`, where `f_t` is computed by `twistFnInt`. -/
theorem isCompatibleTwistLift_iff_twistFnInt (t : AdmissibleTuple)
    (lam : ℤ) (G : Mat(2, ℤ)) :
    t.IsCompatibleTwistLift lam G ↔
      G.det * twistFnInt t.d t.r t.triple.towerDimension lam ≡ 1
        [ZMOD (dbar t.d : ℤ)] := by
  unfold IsCompatibleTwistLift twistFnInt
  rw [show G.det * (t.r : ℤ) *
        (2 * lam + (t.triple.towerDimension : ℤ) - 1 + (t.d : ℤ)) =
      G.det * ((t.r : ℤ) *
        (2 * lam + (t.d : ℤ) + (t.triple.towerDimension : ℤ) - 1)) by ring]

/-- The determinant of a compatible integer twist lift is invertible modulo `dbar d`: it is the
inverse of `f_t(λ)` there. -/
theorem IsCompatibleTwistLift.det_isCoprime {t : AdmissibleTuple} {lam : ℤ}
    {G : Mat(2, ℤ)} (hG : t.IsCompatibleTwistLift lam G) :
    IsCoprime G.det (dbar t.d : ℤ) := by
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp ((t.isCompatibleTwistLift_iff_twistFnInt lam G).mp hG)
  exact ⟨twistFnInt t.d t.r t.triple.towerDimension lam, k, by linear_combination -hk⟩

/-- A compatible integer lift reduces to an invertible quotient twist with the same
compatibility condition, by `IsCompatibleTwistLift.det_isCoprime`. -/
theorem IsCompatibleTwistLift.exists_isCompatibleTwist {t : AdmissibleTuple} {lam : ℤ}
    {G : Mat(2, ℤ)} (hG : t.IsCompatibleTwistLift lam G) :
    ∃ g : GhostTwist t.d, IsGhostTwistLift G g ∧ t.IsCompatibleTwist lam g := by
  have hu : IsUnit (G.det : ZMod (dbar t.d)) :=
    (ZMod.coe_int_isUnit_iff_isCoprime G.det (dbar t.d)).mpr hG.det_isCoprime.symm
  have hmapdet : (G.map (Int.castRingHom (ZMod (dbar t.d)))).det =
      (G.det : ZMod (dbar t.d)) :=
    ((Int.castRingHom (ZMod (dbar t.d))).map_det G).symm
  have hdetunit : IsUnit ((G.map (Int.castRingHom (ZMod (dbar t.d)))).det) := by
    rw [hmapdet]
    exact hu
  let g : GhostTwist t.d :=
    Matrix.GeneralLinearGroup.mk'' (G.map (Int.castRingHom (ZMod (dbar t.d)))) hdetunit
  have hlift : IsGhostTwistLift G g := rfl
  exact ⟨g, hlift, (t.isCompatibleTwist_iff_of_isGhostTwistLift lam g G hlift).mpr hG⟩

/-- **A compatible twist moves the displacement phase to the twisted indices**:
`ξ_d^{⟨p,q⟩} = ξ_d^{f_t(λ)⟨Gp,Gq⟩}`, since `⟨Gp,Gq⟩ = Det(G)⟨p,q⟩` and `Det(G) f_t(λ) ≡ 1
(mod d̄)`. This is the substitution `Det(G⁻¹) = f_t(λ)` in the proof of [AFK25, Theorem 1.45,
`thm:ghstExist`]. -/
theorem IsCompatibleTwistLift.displacementPhase_zpow_eq {t : AdmissibleTuple} {lam : ℤ}
    {G : Mat(2, ℤ)} (hG : t.IsCompatibleTwistLift lam G) (p q : IntPhaseSpace) :
    displacementPhase t.d ^ intSymplecticForm p q =
      displacementPhase t.d ^
        (twistFnInt t.d t.r t.triple.towerDimension lam *
          intSymplecticForm (Matrix.mulVec G p) (Matrix.mulVec G q)) := by
  apply displacementPhase_zpow_eq_of_dbar_dvd_sub
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp ((t.isCompatibleTwistLift_iff_twistFnInt lam G).mp hG)
  rw [intSymplecticForm_matrix_mulVec]
  exact ⟨k * intSymplecticForm p q, by linear_combination (intSymplecticForm p q) * hk⟩

/-! ### Existence of compatible twists

Bézout's identity turns the shift coprimality condition into the determinant of a diagonal twist.
Conversely, the determinant of any compatible twist supplies the same coprimality witness. -/

/-- A compatible quotient-valued twist exists exactly when `λ` satisfies `IsShiftCoprime`.

Thus the coprimality clause in the shift predicate is precisely the arithmetic condition needed to
choose a twist; the reverse direction constructs one from a diagonal integer lift. -/
theorem exists_isCompatibleTwist_iff (t : AdmissibleTuple) (lam : ℤ) :
    (∃ g : GhostTwist t.d, t.IsCompatibleTwist lam g) ↔ t.IsShiftCoprime lam := by
  have hiff :
      IsCoprime (twistFnInt t.d t.r t.triple.towerDimension lam) (dbar t.d : ℤ) ↔
        IsCoprime (2 * lam + (t.triple.towerDimension : ℤ) - 1) (t.d : ℤ) :=
    t.pair.isCoprime_twistFnInt_iff t.triple.towerDimension t.pair_n_eq.symm lam
  constructor
  · rintro ⟨g, hg⟩
    let G := g.integerLift
    have hG : IsGhostTwistLift G g := g.integerLift_isLift
    have hcompat : G.det * twistFnInt t.d t.r t.triple.towerDimension lam ≡ 1
        [ZMOD (dbar t.d : ℤ)] :=
      (t.isCompatibleTwistLift_iff_twistFnInt lam G).mp
        ((t.isCompatibleTwist_iff_of_isGhostTwistLift lam g G hG).mp hg)
    obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hcompat
    exact hiff.mp ⟨G.det, k, by linear_combination -hk⟩
  · intro h
    obtain ⟨u, v, huv⟩ := hiff.mpr h
    let G : Mat(2, ℤ) := Matrix.diagonal ![u, 1]
    have hdet : G.det = u := by
      simp [G, Matrix.det_diagonal, Fin.prod_univ_two]
    have hcompat : t.IsCompatibleTwistLift lam G := by
      rw [t.isCompatibleTwistLift_iff_twistFnInt, hdet]
      exact Int.modEq_iff_dvd.mpr ⟨v, by linarith⟩
    obtain ⟨g, _, hg⟩ := hcompat.exists_isCompatibleTwist
    exact ⟨g, hg⟩

/-- Every `IsShift` admits a compatible twist for the same tuple and the same integer
representative `λ`, by its `IsShiftCoprime` field and `exists_isCompatibleTwist_iff`. -/
theorem IsShift.exists_isCompatibleTwist {t : AdmissibleTuple}
    {A_t Lz : SL(2, ℤ)} {lam : ℤ}
    (h : t.IsShift A_t Lz lam) :
    ∃ g : GhostTwist t.d, t.IsCompatibleTwist lam g :=
  (t.exists_isCompatibleTwist_iff lam).mpr h.isShiftCoprime

end AdmissibleTuple

end SIC

end
