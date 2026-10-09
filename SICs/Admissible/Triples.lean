/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Quadratic.DimensionGrids
import SICs.Admissible.RankOne

/-!
# Admissible Triples and Admissible Tuples

Arbitrary-rank triples `(K,j,m)` and tuples of Definitions 1.24/1.26/1.27.

This file gives the faithful, arbitrary-rank versions of [AFK25, Definition 1.24, `dfn:fjrjmdjm`]
and [AFK25, Definition 1.26, `def:tupleequiv`] and [AFK25, Definition 1.27, `def:admissibleform`],
generalizing the `m = 1` structures of `SICs.Admissible.RankOne` with the two-index grids of
`SICs.Quadratic.DimensionGrids`.

An `AdmissibleTriple` is the data `(K, j, m)` of a real quadratic field with two positive indices.
Its dimension `d_{j,m}` and rank `r_{j,m}` are read off the grids, and `IsAssociatedPair` is the
relation `(d,r) ∼ (K,j,m)` of [AFK25, Definition 1.26, `def:tupleequiv`]. An `AdmissibleTuple` adds
a form `Q` whose fundamental discriminant is `disc(K)` and whose conductor divides `f_j`, which is
[AFK25, Definition 1.27, `def:admissibleform`].

`AdmissibleTuple` and `RankOneAdmissibleTuple` carry a bundled `AdmissiblePair` together with a
proof that it is the associated pair. `SICs.Admissible.PairTriple` proves that every admissible
pair comes from a triple, the existence half of [AFK25, Theorem 4.20(B), `thm:nrddjmrjm`].

`RankOneAdmissibleTriple.toAdmissibleTriple` and `RankOneAdmissibleTuple.toAdmissibleTuple` place
the existing rank-one development inside this one at `m = 1`, with every derived quantity
(dimension, rank, tower conductor, form, conductor ratio) preserved on the nose.

## Main definitions and results

- `AdmissibleTriple`: the data `(K,j,m)` of [AFK25, Definition 1.24, `dfn:fjrjmdjm`].
- `AdmissibleTriple.dimension`, `AdmissibleTriple.rank`: the grid values `d_{j,m}` and `r_{j,m}`.
- `AdmissibleTriple.towerConductor`, `AdmissibleTriple.gridConductor`: `f_j` and `f_{jm}`, with
  `AdmissibleTriple.gridConductor_eq` the factorization `f_{jm} = f_j r_{j,m}`.
- `AdmissibleTriple.IsAssociatedPair`: the relation `∼` of [AFK25, Definition 1.26,
  `def:tupleequiv`].
- `AdmissibleTuple`: [AFK25, Definition 1.27, `def:admissibleform`].
- `AdmissibleTuple.conductorRatio`: the ratio `f_{jm}/f` appearing in [AFK25, Definition 1.30,
  `dfn:SFKPhase`], and `RankOneAdmissibleTuple.conductorRatio`, its rank-one instance `f_j/f`.
- `RankOneAdmissibleTriple.toAdmissibleTriple`, `RankOneAdmissibleTuple.toAdmissibleTuple`: the
  `m = 1` embeddings of the rank-one development, with their agreement lemmas.

## References

- [AFK25, Definition 1.21, `dfn:admissiblePair`] and [AFK25, Definition 1.24, `dfn:fjrjmdjm`] and
  [AFK25, Definition 1.26, `def:tupleequiv`] and [AFK25, Definition 1.27, `def:admissibleform`] and
  [AFK25, Definition 1.30, `dfn:SFKPhase`]
- [AFK25, Theorem 4.20, `thm:nrddjmrjm`]
-/

noncomputable section

open scoped NumberField

namespace SIC

universe u

/-! ### Admissible triples

The data `(K, j, m)` read rank, dimension, and conductors from the two-index grids.  Association
with a geometric pair records the equalities in [AFK25, Definition 1.26, `def:tupleequiv`]. -/

/-- An admissible triple `(K,j,m)` of [AFK25, Definition 1.24, `dfn:fjrjmdjm`]: a real quadratic
field with two
positive indices. The associated dimension and rank are the grid values `d_{j,m}` and `r_{j,m}`
of `SICs.Quadratic.DimensionGrids`.

As in `RankOneAdmissibleTriple`, the field is an actual totally real degree-two `NumberField` and
its oriented fundamental-unit data is carried explicitly, so `f_j`, `r_{j,m}` and `d_{j,m}` are
exact rather than axiomatized. -/
@[source "AFK25, Definition 1.24, p. 14, dfn:fjrjmdjm (admissible triple)" (symbol := "(K,j,m)")]
structure AdmissibleTriple where
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
  /-- The positive rank-grid index `m`. -/
  m : ℕ+

attribute [instance] AdmissibleTriple.fieldK AdmissibleTriple.numberFieldK
  AdmissibleTriple.totallyRealK

namespace AdmissibleTriple

/-- The dimension `d_{j,m}` associated with an admissible triple. -/
noncomputable def dimension (T : AdmissibleTriple) : ℕ :=
  T.tower.dimensionGrid T.j T.m

/-- The rank `r_{j,m}` associated with an admissible triple. -/
noncomputable def rank (T : AdmissibleTriple) : ℕ :=
  (T.tower.rankGrid T.j T.m : ℕ)

/-- The dimension-tower value `d_j = d_{j,1}` associated with an admissible triple.

This is the value the paper writes `d_j`, the first column of the dimension grid, and is what
enters the later shift-coprimality and Zauner-generator formulas. For `m > 1` it differs from the
triple's own dimension `d_{j,m}`. -/
noncomputable def towerDimension (T : AdmissibleTriple) : ℕ :=
  T.tower.canonicalDimension T.j

/-- The dimension-tower value satisfies `d_j > 3`. This follows from
`d_j = ε^j + ε^{-j} + 1` (`RealQuadraticUnitData.dimensionValue`) and `ε > 1`; it discharges an
inequality used without proof in [AFK25, proof of Lemma 4.10, `lem:dfdelprops`] on p. 52. -/
lemma three_lt_towerDimension (T : AdmissibleTriple) : 3 < T.towerDimension :=
  (T.tower.canonicalDimension_spec T.j).three_lt

/-- The conductor-sequence value `f_j` associated with an admissible triple. -/
noncomputable def towerConductor (T : AdmissibleTriple) : ℕ+ :=
  T.tower.canonicalConductor T.j

/-- The conductor-sequence value `f_{jm}` associated with an admissible triple. This is the
conductor appearing in the numerator of the rank grid and in the SF phase `sfPhase`. -/
noncomputable def gridConductor (T : AdmissibleTriple) : ℕ+ :=
  T.tower.canonicalConductor (T.j * T.m)

/-- The dimension is positive. -/
lemma dimension_pos (T : AdmissibleTriple) : 0 < T.dimension :=
  T.tower.dimensionGrid_pos T.j T.m

/-- The conductor factorization `f_{jm} = f_j r_{j,m}` for this triple.

This is `RealQuadraticUnitData.canonicalConductor_mul_eq` specialized to the triple's indices; it
also shows that its rank is the exact quotient `f_{jm}/f_j`. -/
lemma gridConductor_eq (T : AdmissibleTriple) :
    (T.gridConductor : ℕ) = (T.towerConductor : ℕ) * T.rank :=
  T.tower.canonicalConductor_mul_eq T.j T.m

/-- The tower conductor `f_j` divides `f_{jm}`. -/
lemma towerConductor_dvd_gridConductor (T : AdmissibleTriple) :
    (T.towerConductor : ℕ) ∣ (T.gridConductor : ℕ) :=
  T.tower.canonicalConductor_dvd T.j T.m

/-- The association `(d,r) ∼ (K,j,m)` of [AFK25, Definition 1.26, `def:tupleequiv`]. -/
@[source "AFK25, Definition 1.26, p. 14, def:tupleequiv" (symbol := "(d,r) ∼ (K,j,m)")]
def IsAssociatedPair (T : AdmissibleTriple) (p : AdmissiblePair) : Prop :=
  p.d = T.dimension ∧ p.r = T.rank

/-- An associated pair has the triple's dimension. -/
lemma IsAssociatedPair.d_eq {T : AdmissibleTriple} {p : AdmissiblePair}
    (h : T.IsAssociatedPair p) : p.d = T.dimension :=
  h.1

/-- An associated pair has the triple's rank. -/
lemma IsAssociatedPair.r_eq {T : AdmissibleTriple} {p : AdmissiblePair}
    (h : T.IsAssociatedPair p) : p.r = T.rank :=
  h.2

/-- **The integer `n` of an associated pair is `d_j + 1`**, where `d_j` is the first-column
dimension-tower value: [AFK25, Theorem 4.20(A)(2), `thm:nrddjmrjm`] together with the uniqueness
of the integer in the admissible-pair equation (`AdmissiblePair.n_unique`). -/
lemma IsAssociatedPair.n_eq {T : AdmissibleTriple} {p : AdmissiblePair}
    (h : T.IsAssociatedPair p) : p.n = T.towerDimension + 1 := by
  symm
  apply p.n_unique
  rw [h.d_eq, h.r_eq]
  exact T.tower.dimensionGrid_equation T.j T.m

end AdmissibleTriple

/-! ### Admissible tuples with forms

An associated pair and triple become an admissible tuple after adding a form whose fundamental
discriminant is that of the field and whose conductor divides `f_j`.  Exact quotient definitions
then expose the conductor ratios used by stabilizers and SF phases. -/

/-- An admissible tuple `(d,r,Q) ∼ (K,j,m,Q)` of [AFK25, Definition 1.27, `def:admissibleform`]: an
admissible pair
associated with an admissible triple, together with an admissible form whose fundamental
discriminant is `disc(K)` and whose conductor divides `f_j`.

This is the arbitrary-rank generalization of `RankOneAdmissibleTuple`. -/
@[source "AFK25, Definition 1.27, p. 15, def:admissibleform" (symbol := "(d,r,Q) ∼ (K,j,m,Q)")]
structure AdmissibleTuple where
  /-- The associated admissible triple `(K,j,m)`. -/
  triple : AdmissibleTriple
  /-- The associated bundled geometric pair. -/
  pair : AdmissiblePair
  /-- The integral binary quadratic form. -/
  Q : BinaryQF
  /-- The pair/triple association `AdmissibleTriple.IsAssociatedPair`. -/
  associated : triple.IsAssociatedPair pair
  /-- The form is primitive, irreducible, and indefinite. -/
  form_admissible : Q.IsAdmissible
  /-- The positive conductor of the form. -/
  formConductor : ℕ+
  /-- The form has fundamental discriminant `disc(K)` and the asserted exact conductor. -/
  formConductor_spec : Q.IsConductor (NumberField.discr triple.K) (formConductor : ℕ)
  /-- The form conductor divides the tower conductor `f_j`. -/
  formConductor_dvd : (formConductor : ℕ) ∣ (triple.towerConductor : ℕ)

namespace AdmissibleTuple

/-- The geometric dimension of an admissible tuple. -/
abbrev d (t : AdmissibleTuple) : ℕ :=
  t.pair.d

/-- The geometric rank of an admissible tuple. -/
abbrev r (t : AdmissibleTuple) : ℕ :=
  t.pair.r

/-- The dimension of an admissible tuple is the grid value `d_{j,m}`. -/
lemma d_eq_dimension (t : AdmissibleTuple) : t.d = t.triple.dimension :=
  t.associated.1

/-- The rank of an admissible tuple is the grid value `r_{j,m}`. -/
lemma r_eq_rank (t : AdmissibleTuple) : t.r = t.triple.rank :=
  t.associated.2

/-- The integer `n` determined by the pair underlying an admissible tuple is `d_j + 1`, where
`d_j` is the first-column dimension-tower value (`AdmissibleTriple.IsAssociatedPair.n_eq`). -/
lemma pair_n_eq (t : AdmissibleTuple) :
    t.pair.n = t.triple.towerDimension + 1 :=
  t.associated.n_eq

/-- Even tuple dimension forces the first-column tower dimension `d_j` to be even, as in the
parity table of [AFK25, Lemma 4.23, `lem:dimgridtechres`]; used by
`odd_gridScaledForm_of_even_d`. -/
lemma even_towerDimension_of_even_d (t : AdmissibleTuple) (hd : Even t.d) :
    Even t.triple.towerDimension := by
  rw [Nat.even_iff]
  have hn := Nat.odd_iff.mp (t.pair.odd_n_of_even_d hd)
  rw [t.pair_n_eq] at hn
  omega

/-- The form conductor divides `f_{jm}`, since it divides `f_j` and `f_j` divides `f_{jm}`. -/
lemma formConductor_dvd_gridConductor (t : AdmissibleTuple) :
    (t.formConductor : ℕ) ∣ (t.triple.gridConductor : ℕ) :=
  t.formConductor_dvd.trans t.triple.towerConductor_dvd_gridConductor

/-- The conductor ratio `f_j/f` appearing in [AFK25, Definition 1.28, `dfn:AssociatedStabilizers`,
equation (1.41)], the
doubled formula for the Zauner generator `L_{z,t}`. `formConductor_dvd` makes the division
exact. Distinct from `conductorRatio`, which is `f_{jm}/f`. -/
noncomputable def towerConductorRatio (t : AdmissibleTuple) : ℕ :=
  (t.triple.towerConductor : ℕ) / (t.formConductor : ℕ)

/-- The tower conductor ratio divides `f_j` exactly. -/
lemma towerConductorRatio_mul_formConductor (t : AdmissibleTuple) :
    t.towerConductorRatio * (t.formConductor : ℕ) = (t.triple.towerConductor : ℕ) :=
  Nat.div_mul_cancel t.formConductor_dvd

/-- The tower conductor ratio is positive. -/
lemma towerConductorRatio_pos (t : AdmissibleTuple) : 0 < t.towerConductorRatio :=
  Nat.div_pos
    (Nat.le_of_dvd t.triple.towerConductor.property t.formConductor_dvd)
    t.formConductor.property

/-- The tower discriminant identity of the tuple, `(f_j/f)² disc(Q) = (d_j - 3)(d_j + 1)`, whose
right-hand side is `Δ_j` of [AFK25, Definition 4.2, `dfn:discriminantLevelj`]. It combines
`disc(Q) = f² Δ₀` from `formConductor_spec` with `f_j² Δ₀ = (d_j - 3)(d_j + 1)` from
`RealQuadraticUnitData.canonicalConductor_sq_mul_discr`, since `((f_j/f) f)² = f_j²`. -/
lemma towerConductorRatio_sq_mul_disc (t : AdmissibleTuple) :
    (t.towerConductorRatio : ℤ) ^ 2 * t.Q.disc =
      ((t.triple.towerDimension : ℤ) - 3) * ((t.triple.towerDimension : ℤ) + 1) := by
  have hdisc := t.triple.tower.canonicalConductor_sq_mul_discr t.triple.j
  change ((t.triple.towerConductor : ℕ) : ℤ) ^ 2 * NumberField.discr t.triple.K =
    ((t.triple.towerDimension : ℤ) - 3) * ((t.triple.towerDimension : ℤ) + 1) at hdisc
  have hf : (t.towerConductorRatio : ℤ) * ((t.formConductor : ℕ) : ℤ) =
      ((t.triple.towerConductor : ℕ) : ℤ) := by
    exact_mod_cast t.towerConductorRatio_mul_formConductor
  rw [t.formConductor_spec.disc_eq]
  linear_combination hdisc + NumberField.discr t.triple.K *
    ((t.towerConductorRatio : ℤ) * ((t.formConductor : ℕ) : ℤ) +
      ((t.triple.towerConductor : ℕ) : ℤ)) * hf

/-- The conductor ratio `f_{jm}/f` appearing in the SF phase `sfPhase`.
`formConductor_dvd_gridConductor` makes the division exact. -/
noncomputable def conductorRatio (t : AdmissibleTuple) : ℕ :=
  (t.triple.gridConductor : ℕ) / (t.formConductor : ℕ)

/-- The conductor ratio divides `f_{jm}` exactly. -/
lemma conductorRatio_mul_formConductor (t : AdmissibleTuple) :
    t.conductorRatio * (t.formConductor : ℕ) = (t.triple.gridConductor : ℕ) :=
  Nat.div_mul_cancel t.formConductor_dvd_gridConductor

/-- The two conductor ratios differ by the rank: `f_{jm}/f = r_{j,m} (f_j/f)`.

This is `AdmissibleTriple.gridConductor_eq` divided by the form conductor. It is what lets the
exponent `f_{jm}/f` of the Shintani--Faddeev phase be expressed through the ratio `f_j/f` that the
associated stabilizers carry. -/
lemma conductorRatio_eq_rank_mul (t : AdmissibleTuple) :
    t.conductorRatio = t.triple.rank * t.towerConductorRatio := by
  refine Nat.eq_of_mul_eq_mul_right t.formConductor.property ?_
  calc t.conductorRatio * (t.formConductor : ℕ) = (t.triple.gridConductor : ℕ) :=
        t.conductorRatio_mul_formConductor
    _ = (t.triple.towerConductor : ℕ) * t.triple.rank := t.triple.gridConductor_eq
    _ = t.triple.rank * (t.towerConductorRatio * (t.formConductor : ℕ)) := by
        rw [t.towerConductorRatio_mul_formConductor]; ring
    _ = t.triple.rank * t.towerConductorRatio * (t.formConductor : ℕ) := by ring

/-- The dimension of an admissible tuple exceeds three, from admissibility of its pair. -/
lemma three_lt_d (t : AdmissibleTuple) : 3 < t.d :=
  t.pair.three_lt_d

/-- The dimension of an admissible tuple is nonzero. -/
instance (t : AdmissibleTuple) : NeZero t.d :=
  ⟨by have := t.three_lt_d; omega⟩

end AdmissibleTuple

/-! ### The rank-one development as the row `m = 1`

Embedding the rank-one structures at `m = 1` preserves dimension, rank, fields, conductors, and
their ratios.  These comparison lemmas make principal specializations of arbitrary-rank theorems
explicit. -/

namespace RankOneAdmissibleTriple

/-- Every rank-one admissible triple `(K,j,1)` is an admissible triple. -/
noncomputable def toAdmissibleTriple (T : RankOneAdmissibleTriple) : AdmissibleTriple where
  K := T.K
  tower := T.tower
  j := T.j
  m := 1

/-- The rank of the associated admissible triple is one, as `r_{j,1} = 1`. -/
@[simp]
lemma toAdmissibleTriple_rank (T : RankOneAdmissibleTriple) :
    T.toAdmissibleTriple.rank = T.rank := by
  change (T.tower.rankGrid T.j 1 : ℕ) = 1
  rw [T.tower.rankGrid_one T.j]
  rfl

/-- The dimension of the associated admissible triple is the tower value `d_j = d_{j,1}`. -/
@[simp]
lemma toAdmissibleTriple_dimension (T : RankOneAdmissibleTriple) :
    T.toAdmissibleTriple.dimension = T.dimension :=
  T.tower.dimensionGrid_one T.j

/-- At `m = 1` the dimension-tower value `d_j` is the triple's own dimension. -/
@[simp]
lemma toAdmissibleTriple_towerDimension (T : RankOneAdmissibleTriple) :
    T.toAdmissibleTriple.towerDimension = T.dimension :=
  rfl

/-- At `m = 1` the grid conductor `f_{jm}` is the tower conductor `f_j`. -/
@[simp]
lemma toAdmissibleTriple_gridConductor (T : RankOneAdmissibleTriple) :
    T.toAdmissibleTriple.gridConductor = T.towerConductor := by
  change T.tower.canonicalConductor (T.j * 1) = T.tower.canonicalConductor T.j
  rw [mul_one]

/-- The pair association of the rank-one development agrees with the general one. -/
lemma isAssociatedPair_iff (T : RankOneAdmissibleTriple) (p : AdmissiblePair) :
    T.toAdmissibleTriple.IsAssociatedPair p ↔ T.IsAssociatedPair p := by
  unfold AdmissibleTriple.IsAssociatedPair RankOneAdmissibleTriple.IsAssociatedPair
  rw [toAdmissibleTriple_dimension, toAdmissibleTriple_rank]

end RankOneAdmissibleTriple

namespace RankOneAdmissibleTuple

/-- Every rank-one admissible tuple is an admissible tuple, with the same pair, form, and
conductor data, at the grid row `m = 1`. -/
noncomputable def toAdmissibleTuple (t : RankOneAdmissibleTuple) : AdmissibleTuple where
  triple := t.triple.toAdmissibleTriple
  pair := t.pair
  Q := t.Q
  associated := (t.triple.isAssociatedPair_iff t.pair).2 t.associated
  form_admissible := t.form_admissible
  formConductor := t.formConductor
  formConductor_spec := t.formConductor_spec
  formConductor_dvd := t.formConductor_dvd

/-- Passing to the general tuple preserves the geometric dimension. -/
@[simp]
lemma toAdmissibleTuple_d (t : RankOneAdmissibleTuple) : t.toAdmissibleTuple.d = t.d :=
  rfl

/-- Passing to the general tuple preserves the binary quadratic form. -/
@[simp]
lemma toAdmissibleTuple_Q (t : RankOneAdmissibleTuple) : t.toAdmissibleTuple.Q = t.Q :=
  rfl

/-- At `m = 1`, the general conductor ratio `f_{jm}/f` reduces to the rank-one ratio `f_j/f`.

`RankOneAdmissibleTuple.conductorRatio` below is that quotient, and consumes this identity through
the right-hand side. -/
@[simp]
lemma toAdmissibleTuple_conductorRatio (t : RankOneAdmissibleTuple) :
    t.toAdmissibleTuple.conductorRatio =
      (t.triple.towerConductor : ℕ) / (t.formConductor : ℕ) := by
  change ((t.triple.toAdmissibleTriple.gridConductor : ℕ)) / ((t.formConductor : ℕ)) = _
  rw [RankOneAdmissibleTriple.toAdmissibleTriple_gridConductor]

/-! ### The rank-one conductor ratio

The ratio `f_j/f` of the tower conductor to the form conductor is the rank-one instance of
`AdmissibleTuple.conductorRatio`. It is the exponent weight of the Shintani--Faddeev phase and the
coefficient of the doubled associated-stabilizer formula. -/

/-- The rank-one specialization of `AdmissibleTuple.conductorRatio`: at `m = 1` the ratio
`f_{jm}/f` becomes `f_j/f`. This quotient agrees with the general API by
`RankOneAdmissibleTuple.toAdmissibleTuple_conductorRatio`; keeping the quotient definitionally
visible preserves the existing rank-one interface. -/
noncomputable abbrev conductorRatio (t : RankOneAdmissibleTuple) : ℕ :=
  (t.triple.towerConductor : ℕ) / (t.formConductor : ℕ)

/-- The conductor ratio divides the tower conductor exactly, by specialization of
`AdmissibleTuple.conductorRatio_mul_formConductor`. -/
lemma conductorRatio_mul_formConductor (t : RankOneAdmissibleTuple) :
    t.conductorRatio * (t.formConductor : ℕ) = (t.triple.towerConductor : ℕ) :=
  by
    have h := t.toAdmissibleTuple.conductorRatio_mul_formConductor
    change t.toAdmissibleTuple.conductorRatio * (t.formConductor : ℕ) =
      (t.triple.toAdmissibleTriple.gridConductor : ℕ) at h
    simpa using h

/-- The conductor ratio is one exactly when the form conductor is the full tower conductor. -/
lemma conductorRatio_eq_one_iff (t : RankOneAdmissibleTuple) :
    t.conductorRatio = 1 ↔ (t.formConductor : ℕ) = (t.triple.towerConductor : ℕ) := by
  constructor
  · intro h
    have := t.conductorRatio_mul_formConductor
    rwa [h, one_mul] at this
  · intro h
    change (t.triple.towerConductor : ℕ) / (t.formConductor : ℕ) = 1
    rw [h]
    exact Nat.div_self t.triple.towerConductor.property

end RankOneAdmissibleTuple

end SIC

end
