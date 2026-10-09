/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Admissible.StabilizerDomain
import SICs.Dilogarithm.Pseudolattice.FiveTerm
import SICs.Quadratic.ConductorOneElements

/-!
# The finite quantum dilogarithm of an admissible tuple

The level generator `A_t` at `ρ_t`: an attractive fixed point, its group order
`N = (d_j - 3)d²`, and the finite five-term relation there.

This module follows [AFK26, Appleby, Flammia, Kopp (2026), Section 4]: it presents the tuple's
level generator `γ = A_t = L^{2m+1}` and the root `τ = ρ_t = ρ_{Q,+}` as an attractive fixed point
in the sense of [RW26, Radchenko, Wheeler (2026), Section 1], so that the finite five-term
relation (7) of [RW26, Radchenko, Wheeler (2026), Theorem 2, `thm:fg.equs`, equation (7),
`eq:Fgpm.5term`] holds at it. These are the inputs of the subgroup pentagon relation
(`finiteDilogSubgroupPentagon`) in the proof of
[AFK26, Appleby, Flammia, Kopp (2026), Theorem 1.2, `thm:tci`].

## The argument

`ρ_t` is fixed by `A_t` with `j_{A_t}(ρ_t) = ε^{j(2m+1)} > 1` (`flt_A_rootPlus`,
`one_lt_fltDenominator_A_rootPlus`), and is irrational since `Q` is irreducible.
[AFK26, Appleby, Flammia, Kopp (2026), Section 4]
assumes `γ₂₁ > 0`, "replacing `Q` by an `SL₂(ℤ)`-equivalent form if needed"; here the assumption is
a hypothesis `0 < a` on the leading coefficient of `Q`, which gives `γ₂₁ > 0`
(`IsAssociatedStabilizerPair.lowerLeft_A_pos`) and which the tuple of
`AdmissiblePair.exists_admissibleTuple` satisfies.

The order is [AFK26, Appleby, Flammia, Kopp (2026), Lemma 4.1, `lem:N`]:
`N = Tr A_t - 2 = (d_j - 3)d²`, read off
`IsAssociatedStabilizerPair.trace_A`.

For the five-term relation, `ρ_t` is the real value at the selected place of the element
`F.rootPlusElement Q f` of `K` (`realEmbeddingAt_place_rootPlusElement`), with `f` the conductor of
`Q`; `finiteDilogFiveTerm_of_isAttractiveFixedPoint` then applies.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

namespace AdmissibleTuple

namespace IsAssociatedStabilizerPair

variable {t : AdmissibleTuple} {A_t Lz : SL(2, ℤ)}

/-! ### The attractive fixed point and the order

`(A_t, ρ_t)` is an attractive fixed point when `Q` has positive leading coefficient, and
`|G| = Tr A_t - 2 = (d_j - 3)d²`. -/

/-- **`(A_t, ρ_t)` is an attractive fixed point** when `Q` has positive leading coefficient: `ρ_t`
is irrational, `A_t·ρ_t = ρ_t`, `j_{A_t}(ρ_t) > 1`, and `γ₂₁ > 0`; the setting of
[AFK26, Appleby, Flammia, Kopp (2026), Section 4], where `τ` is the attracting fixed point of
`γ = A_t`. -/
theorem isAttractiveFixedPoint (hp : t.IsAssociatedStabilizerPair A_t Lz) (ha : 0 < t.Q.a) :
    IsAttractiveFixedPoint A_t t.Q.rootPlus := by
  exact ⟨t.form_admissible.rootPlus_irrational, hp.flt_A_rootPlus,
    hp.one_lt_fltDenominator_A_rootPlus, hp.lowerLeft_A_pos ha⟩

/-- **[AFK26, Appleby, Flammia, Kopp (2026), Lemma 4.1, `lem:N`]**: the group order of the level
generator is `N = Tr A_t - 2 = (d_j - 3)d²`. -/
@[source "AFK26, Lemma 4.1, p. 6, lem:N"]
theorem finiteDilogOrder_eq (hp : t.IsAssociatedStabilizerPair A_t Lz) :
    finiteDilogOrder A_t = (t.triple.towerDimension - 3) * t.d ^ 2 := by
  have hdim : 3 ≤ t.triple.towerDimension :=
    (le_of_lt t.triple.three_lt_towerDimension)
  have hsub : (t.triple.towerDimension : ℤ) - 3 =
      ((t.triple.towerDimension - 3 : ℕ) : ℤ) := by omega
  change (((A_t : Mat(2, ℤ)) 0 0 + (A_t : Mat(2, ℤ)) 1 1 - 2)).toNat = _
  rw [← Matrix.trace_fin_two, hp.trace_A]
  have heq : (t.d : ℤ) ^ 2 * ((t.triple.towerDimension : ℤ) - 3) + 2 - 2 =
      (((t.triple.towerDimension - 3) * t.d ^ 2 : ℕ) : ℤ) := by
    rw [hsub]
    push_cast
    ring
  rw [heq, Int.toNat_natCast]

/-! ### The finite five-term relation

[RW26, Radchenko, Wheeler (2026), Theorem 2, `thm:fg.equs`] at `(A_t, ρ_t)`, through the
element of `K` over `ρ_t`. -/

/-- **The finite five-term relation (7) of
[RW26, Radchenko, Wheeler (2026), Theorem 2, `thm:fg.equs`] at the
level generator of an admissible tuple**, `γ = A_t` and `τ = ρ_t`, when `Q` has positive leading
coefficient: the input (7) of [AFK26, Appleby, Flammia, Kopp (2026), Theorem 3.1,
`thm:subgrouppentagon`] in the proof of
[AFK26, Appleby, Flammia, Kopp (2026), Theorem 1.2, `thm:tci`]. -/
theorem finiteDilogFiveTerm (hp : t.IsAssociatedStabilizerPair A_t Lz) (ha : 0 < t.Q.a)
    [NeZero (finiteDilogOrder A_t)] :
    FiniteDilogFiveTerm A_t t.Q.rootPlus := by
  let F := t.triple.tower.toRealQuadraticFieldData
  have hroot := F.realEmbeddingAt_place_rootPlusElement t.formConductor_spec.disc_eq
  have hA : IsAttractiveFixedPoint A_t
      (realEmbeddingAt t.triple.K F.place (F.rootPlusElement t.Q t.formConductor)) := by
    rw [hroot]
    exact hp.isAttractiveFixedPoint ha
  have hfive := finiteDilogFiveTerm_of_isAttractiveFixedPoint hA
  rw [hroot] at hfive
  exact hfive

end IsAssociatedStabilizerPair

end AdmissibleTuple

end SIC

end
