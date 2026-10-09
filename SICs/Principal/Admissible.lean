/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Admissible.Triples
import SICs.Principal.Quadratic.Forms

/-!
# Principal Rank-One Admissible Tuple

The conductor of `Q_d` at the concrete rank-one level and the faithful tuple
`(d,1,Q_d) ~ (K_d,j,1,Q_d)`.

This file first specializes the general rank-one tower construction to the principal form
`Q_d = ⟨1,1-d,1⟩`, identifying its conductor with the concrete exact level. It then attaches
that form to the shared rank-one triple. Consequently, for every `d > 3`, Lean constructs the
arithmetic tuple

`(d,1,Q_d) ~ (K_d,j,1,Q_d)`

with fundamental discriminant `disc(K_d)` and form conductor exactly `f_j`. This is the principal
specialization of [AFK25, Definition 1.24, `dfn:fjrjmdjm`] and [AFK25, Definition 1.26,
`def:tupleequiv`] and [AFK25, Definition 1.27, `def:admissibleform`]. It does not construct the full
arbitrary-rank pair/triple bijection of [AFK25, Theorem 1.25, `thm:bijectionofadmissibletuples`].

## Main definitions and results

- `RealQuadraticUnitData.RankOneLevel.principal_isConductor`: `Q_d` has conductor `f_j` at an
  exact rank-one level.
- `principalOneSICForm_isConductor_rankOneField`: the concrete rank-one field supplies that
  conductor in every dimension `d > 3`.
- `BundledRankOneLevel.admissibleTriple`: the shared construction of `(K_d,j,1)` from the exact
  level.
- `principalRankOneAdmissibleTuple`: the faithful tuple with the principal form `Q_d`.
- `principalRankOneAdmissibleTuple_conductorRatio`: the rank-one conductor ratio `f_j/f` of the
  SF phase is one.

## References

- [AFK25, Definition 1.21, `dfn:admissiblePair`] and [AFK25, Definition 1.24, `dfn:fjrjmdjm`] and
  [AFK25, Definition 1.26, `def:tupleequiv`] and [AFK25, Definition 1.27, `def:admissibleform`] and
  [AFK25, Definition 1.28, `dfn:AssociatedStabilizers`]
- [AFK25, Theorem 1.25, `thm:bijectionofadmissibletuples`]
- [AFK25, Lemma 4.3, `lem:towerbasic`]
- [AFK25, Theorem 3.20, `thm:dimtowunique`]
-/

noncomputable section

namespace SIC

/-! ### Conductor of the principal form

The exact tower level provides the radicand identity. The principal form identifies that
radicand with its discriminant, giving the conductor needed by the tuple construction below.
-/

namespace RealQuadraticUnitData

/-- At an exact rank-one tower level, the principal form has conductor `f_j` over the actual
number-field discriminant. Specializes `RankOneLevel.radicand_eq` to `Q_d`. -/
lemma RankOneLevel.principal_isConductor
    {d : ℕ} {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    {T : RealQuadraticUnitData K} (L : T.RankOneLevel d) :
    (principalOneSICForm d).IsConductor (NumberField.discr K) (L.f : ℕ) := by
  apply isConductor_principalOneSICForm_of_tower d T.discr_fundamental T.discr_pos L.f.property
  change ((d : ℤ) + 1) * ((d : ℤ) - 3) =
    (((L.f : ℕ) : ℤ) ^ 2 * NumberField.discr K)
  exact L.radicand_eq

end RealQuadraticUnitData

/-- In the concrete rank-one quadratic field, `Q_d` has the conductor supplied by the chosen exact
tower level. -/
lemma principalOneSICForm_isConductor_rankOneField (d : RankOneDimension) :
    (principalOneSICForm d).IsConductor (NumberField.discr (RankOneField d))
      (rankOneFieldLevel d).f :=
  (rankOneFieldLevel d).principal_isConductor

/-! ### The concrete tuple

The general exact-level constructor supplies `(K_d,j,1)` and its conductor, while the explicit
form `Q_d` supplies the family-specific admissible-form component. Their dimension and conductor
equalities assemble the faithful rank-one tuple and show its conductor ratio is one.
-/

/-- The principal form `⟨1,1-d,1⟩` and the concrete principal triple give a faithful rank-one
admissible tuple. Its form conductor equals the tower conductor `f_j`. -/
noncomputable def principalRankOneAdmissibleTuple (d : RankOneDimension) :
    RankOneAdmissibleTuple where
  triple := (rankOneBundledLevel d).admissibleTriple
  pair := AdmissiblePair.rankOne d d.property
  Q := principalOneSICForm d
  associated := (rankOneBundledLevel d).admissibleTriple_isAssociatedPair
  form_admissible := isAdmissible_principalOneSICForm d d.property
  formConductor := (rankOneFieldLevel d).f
  formConductor_spec := principalOneSICForm_isConductor_rankOneField d
  formConductor_dvd := by
    rw [(rankOneBundledLevel d).admissibleTriple_towerConductor]
    exact dvd_refl _

/-- The principal admissible tuple has the prescribed dimension. -/
@[simp]
lemma principalRankOneAdmissibleTuple_d (d : RankOneDimension) :
    (principalRankOneAdmissibleTuple d).d = d :=
  rfl

/-- The form in the principal admissible tuple is `Q_d = ⟨1,1-d,1⟩`. -/
@[simp]
lemma principalRankOneAdmissibleTuple_Q (d : RankOneDimension) :
    (principalRankOneAdmissibleTuple d).Q = principalOneSICForm d :=
  rfl

/-- The conductor in the principal admissible tuple is exactly its tower conductor `f_j`. -/
lemma principalRankOneAdmissibleTuple_formConductor (d : RankOneDimension) :
    (principalRankOneAdmissibleTuple d).formConductor =
      (principalRankOneAdmissibleTuple d).triple.towerConductor := by
  exact (rankOneBundledLevel d).admissibleTriple_towerConductor.symm

/-- The exact conductor ratio `f_j/f` of the principal tuple is one. Specializes
`RankOneAdmissibleTuple.conductorRatio_eq_one_iff`, using
`principalRankOneAdmissibleTuple_formConductor`. -/
lemma principalRankOneAdmissibleTuple_conductorRatio (d : RankOneDimension) :
    (principalRankOneAdmissibleTuple d).conductorRatio = 1 := by
  rw [RankOneAdmissibleTuple.conductorRatio_eq_one_iff]
  exact congrArg Subtype.val (principalRankOneAdmissibleTuple_formConductor d)

end SIC

end
