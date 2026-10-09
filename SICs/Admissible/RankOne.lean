/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Admissible.Pairs
import SICs.Quadratic.Forms
import SICs.Quadratic.RankOneFields

/-!
# Rank-One Admissible Triples and Tuples

Rank-one triples and tuples, and the triple of a bundled exact level.

This file gives the faithful `m = 1` specialization of the arithmetic objects in [AFK25,
Definition 1.24, `dfn:fjrjmdjm`, Definition 1.26, `def:tupleequiv`, and Definition 1.27,
`def:admissibleform`]. It is the narrow interface used by the principal rank-one family and does
not claim to construct the complete two-index rank and dimension grids.

For a positive tower index `j`, the rank is definitionally one, the conductor is the canonical
positive integer `f_j`, and the dimension is the canonical trace value `d_j`.

The number-field type, oriented real place, and fundamental unit are carried as enriched proof data
representing the paper's embedded real quadratic field. The full arbitrary-`m` triple and general
admissible tuple are in `SICs.Admissible.Triples`, which embeds these structures at `m = 1`.

## Main definitions and results

- `RankOneAdmissibleTriple`: exact data for `(K,j,1)`.
- `RankOneAdmissibleTriple.IsAssociatedPair`: the specialization `(d,r) = (d_j,1)` of [AFK25,
  Definition 1.26, `def:tupleequiv`].
- `BundledRankOneLevel`: a bundled exact rank-one tower level at one dimension.
- `BundledRankOneLevel.admissibleTriple`: the construction of `(K,j,1)` from an exact level, used
  by the principal family.
- `rankOneBundledLevel`: that payload for every dimension `d > 3`, from the concrete rank-one
  field.
- `RankOneAdmissibleTuple`: the rank-one specialization of [AFK25, Definition 1.27,
  `def:admissibleform`], including the exact form conductor and its divisibility by `f_j`.

## References

- [AFK25, Definition 1.21, `dfn:admissiblePair`] and [AFK25, Definition 1.24, `dfn:fjrjmdjm`] and
  [AFK25, Definition 1.26, `def:tupleequiv`] and [AFK25, Definition 1.27, `def:admissibleform`]
- [AFK25, Lemma 4.3, `lem:towerbasic`]
-/

noncomputable section

namespace SIC

universe u

/-! ### Rank-one admissible triples

The data `(K, j, 1)` retain the real quadratic tower and positive level while fixing the rank to
one.  Canonical conductor and dimension values determine the associated geometric pair. -/

/-- Rank-one admissible-triple data `(K, j, 1)` used by the rank-one specializations.

Only the real quadratic tower and the positive index `j` are stored: the rank is `1`, while the
dimension and conductor are the canonical values `d_j` and `f_j`. The arbitrary-rank interface in
`SICs.Admissible.Triples` adds the second index `m` and reads from the full grids. -/
structure RankOneAdmissibleTriple where
  /-- The real quadratic number field `K`. -/
  K : Type u
  /-- The field structure on `K`. -/
  [fieldK : Field K]
  /-- The number-field structure on `K`. -/
  [numberFieldK : NumberField K]
  /-- Total reality of `K`. -/
  [totallyRealK : NumberField.IsTotallyReal K]
  /-- The exact oriented field and fundamental-unit tower data. -/
  tower : RealQuadraticUnitData K
  /-- The positive dimension-tower index `j`. -/
  j : ℕ+

attribute [instance] RankOneAdmissibleTriple.fieldK
  RankOneAdmissibleTriple.numberFieldK RankOneAdmissibleTriple.totallyRealK

namespace RankOneAdmissibleTriple

/-- The dimension `d_j = d_{j,1}` associated with a rank-one admissible triple. -/
noncomputable def dimension (T : RankOneAdmissibleTriple) : ℕ :=
  T.tower.canonicalDimension T.j

/-- The rank `r_{j,1}` associated with a rank-one admissible triple. -/
def rank (_T : RankOneAdmissibleTriple) : ℕ := 1

/-- The conductor-sequence value `f_j` associated with a rank-one admissible triple. -/
noncomputable def towerConductor (T : RankOneAdmissibleTriple) : ℕ+ :=
  T.tower.canonicalConductor T.j

/-- The rank-one pair/triple association: the pair has dimension `d_j` and rank `1`. -/
def IsAssociatedPair (T : RankOneAdmissibleTriple) (p : AdmissiblePair) : Prop :=
  p.d = T.dimension ∧ p.r = T.rank

end RankOneAdmissibleTriple

/-! ### Bundled exact rank-one levels

This auxiliary bundle packages the field, tower, and a level realizing one prescribed dimension.
The concrete rank-one field construction supplies it unconditionally for every `d > 3`. -/

/-- A bundled exact rank-one level, suitable as the arithmetic payload for a rank-one tuple in one
dimension.

This is a project-local auxiliary bundle, not an `AdmissibleTriple`. All field, unit, conductor,
and dimension equations are represented exactly, but the bundle does not itself supply the
pair/triple association required for admissibility. -/
structure BundledRankOneLevel (d : ℕ) where
  /-- The actual real quadratic number field. -/
  K : Type u
  /-- The field structure on `K`. -/
  [fieldK : Field K]
  /-- The number-field structure on `K`. -/
  [numberFieldK : NumberField K]
  /-- Every infinite place of `K` is real. -/
  [totallyRealK : NumberField.IsTotallyReal K]
  /-- The oriented real-quadratic field and fundamental-unit data. -/
  tower : RealQuadraticUnitData K
  /-- The positive tower level whose rank-one dimension is `d`. -/
  level : tower.RankOneLevel d

attribute [instance] BundledRankOneLevel.fieldK BundledRankOneLevel.numberFieldK
  BundledRankOneLevel.totallyRealK

namespace BundledRankOneLevel

/-! ### The admissible triple of an exact level

An exact level determines the arithmetic triple `(K,j,1)`, associated with the rank-one pair
`(d,1)`. A rank-one family then attaches an admissible quadratic form and its conductor to this
triple. -/

/-- The dimension of a bundled rank-one level exceeds three. -/
lemma three_lt {d : ℕ} (L : BundledRankOneLevel d) : 3 < d :=
  L.level.three_lt

/-- The rank-one admissible triple `(K,j,1)` carried by a bundled exact level. -/
def admissibleTriple {d : ℕ} (L : BundledRankOneLevel d) : RankOneAdmissibleTriple where
  K := L.K
  tower := L.tower
  j := L.level.j

/-- The shared triple's canonical dimension is the level's dimension `d`. -/
@[simp]
lemma admissibleTriple_dimension {d : ℕ} (L : BundledRankOneLevel d) :
    L.admissibleTriple.dimension = d :=
  (L.tower.canonicalDimension_spec L.level.j).unique L.level.dimension_spec

/-- The shared triple's canonical tower conductor is the level's conductor `f_j`. -/
@[simp]
lemma admissibleTriple_towerConductor {d : ℕ} (L : BundledRankOneLevel d) :
    L.admissibleTriple.towerConductor = L.level.f :=
  (L.tower.canonicalConductor_spec L.level.j).unique L.level.conductor_spec

/-- The shared triple is associated with the rank-one geometric pair `(d,1)`. -/
lemma admissibleTriple_isAssociatedPair {d : ℕ} (L : BundledRankOneLevel d) :
    L.admissibleTriple.IsAssociatedPair (AdmissiblePair.rankOne d L.three_lt) :=
  ⟨L.admissibleTriple_dimension.symm, rfl⟩

end BundledRankOneLevel

/-! ### Existence in every rank-one dimension

The concrete quadratic field cut out by `X² - (d - 1)X + 1` carries a norm-one root unit. Its
chosen exact tower level realizes `d`, so it supplies the bundled arithmetic payload used by the
principal family.
-/

/-- The concrete rank-one quadratic field and its chosen exact tower level, bundled in dimension
`d`. This packages `rankOneFieldLevel`; it adds no new mathematical assertion. -/
noncomputable def rankOneBundledLevel (d : RankOneDimension) :
    BundledRankOneLevel.{0} d where
  K := RankOneField d
  tower := rankOneRealQuadraticUnitData d
  level := rankOneFieldLevel d

/-! ### Rank-one admissible tuples

Adding an admissible binary quadratic form and its exact conductor produces the rank-one
specialization of [AFK25, Definition 1.27, `def:admissibleform`].  Divisibility by `f_j` records
the required relation between form and tower conductors. -/

/-- Rank-one admissible-tuple data used by the rank-one constructions.

`formConductor_spec` records both the equality of fundamental discriminants and the exact
positive conductor of `Q`; the final field records the required divisibility by `f_j`. The
arbitrary-rank interface in `SICs.Admissible.Triples` adds the second grid index. -/
structure RankOneAdmissibleTuple where
  /-- The associated rank-one admissible triple `(K,j,1)`. -/
  triple : RankOneAdmissibleTriple
  /-- The associated bundled geometric pair. -/
  pair : AdmissiblePair
  /-- The integral binary quadratic form. -/
  Q : BinaryQF
  /-- The pair/triple association `RankOneAdmissibleTriple.IsAssociatedPair`. -/
  associated : triple.IsAssociatedPair pair
  /-- The form is primitive, irreducible, and indefinite. -/
  form_admissible : Q.IsAdmissible
  /-- The positive conductor of the form. -/
  formConductor : ℕ+
  /-- The form has fundamental discriminant `disc(K)` and the asserted exact conductor. -/
  formConductor_spec : Q.IsConductor (NumberField.discr triple.K) (formConductor : ℕ)
  /-- The form conductor divides the tower conductor `f_j`. -/
  formConductor_dvd : (formConductor : ℕ) ∣ (triple.towerConductor : ℕ)

namespace RankOneAdmissibleTuple

/-- The geometric dimension of a rank-one admissible tuple. -/
abbrev d (t : RankOneAdmissibleTuple) : ℕ :=
  t.pair.d

/-- The geometric dimension of a rank-one admissible tuple is the triple's dimension `d_{j,1}`. -/
lemma d_eq_dimension (t : RankOneAdmissibleTuple) : t.d = t.triple.dimension :=
  t.associated.1

end RankOneAdmissibleTuple

end SIC

end
