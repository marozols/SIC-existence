/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Admissible.Triples

/-!
# Shift Coprimality

The coprimality condition on shifts, `2λ + d_j - 1` coprime to `d`.

This file isolates the elementary coprimality condition in [AFK25, Definition 1.34,
`dfn:shift`], for arbitrary-rank tuples and in its rank-one specialization.

## References

- [AFK25] Appleby, Flammia, Kopp, arXiv:2501.03970v2, Definition 1.34
-/

namespace SIC

namespace AdmissibleTuple

/-- The coprimality half of [AFK25, Definition 1.34, `dfn:shift`](1): `2λ + d_j - 1` is coprime to
`d`, where
`d_j` is the dimension-tower value of the tuple's triple. -/
def IsShiftCoprime (t : AdmissibleTuple) (lam : ℤ) : Prop :=
  IsCoprime (2 * lam + (t.triple.towerDimension : ℤ) - 1) (t.d : ℤ)

end AdmissibleTuple

/-! #### The rank-one specialization

The declarations below live in `RankOneAdmissibleTuple`, matching the general layer's
`AdmissibleTuple`, so that a rank-one tuple `t` reaches them by dot notation and the two layers do
not collide by short name. -/

namespace RankOneAdmissibleTuple

/-- The rank-one specialization of `AdmissibleTuple.IsShiftCoprime`: `2λ + d_j - 1` is coprime to
`d`. -/
def IsShiftCoprime (t : RankOneAdmissibleTuple) (lam : ℤ) : Prop :=
  t.toAdmissibleTuple.IsShiftCoprime lam

end RankOneAdmissibleTuple

end SIC
