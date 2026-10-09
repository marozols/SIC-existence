/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Admissible.FormParity
import SICs.Quantum.IntegerDisplacement
import SICs.SL2Z.Rademacher

/-!
# Shintani--Faddeev phases

SF phases, their parity and representative transport, and the rank-one specialization.

This module follows [AFK25, Definition 1.30, `dfn:SFKPhase`] and the phase calculation in
[AFK25, Lemma 5.7, `lem:nupperiodicity`]. The phase is a parity sign times a rational
Rademacher exponential and a displacement root of unity raised to the scaled quadratic form.
Negating the index preserves it. Changing an index by a multiple of the dimension changes the
sign and quadratic exponents by controlled multiples; the parity of the scaled form makes the
remaining factor exactly the symplectic phase. The rank-one phase specializes this same
definition through `RankOneAdmissibleTuple.toAdmissibleTuple`.
-/

noncomputable section

open Complex Real
open scoped MatrixGroups

namespace SIC

/-! ### The sign exponent

The parity sign is unchanged when the index is negated. -/

/-- The sign factor exponent `s_d(p)` appearing in the SF phase `sfPhase`:
      s_d(p) = d + (1+d)(1+p₁)(1+p₂)
    This is the exact integer-indexed definition. -/
def sfSignExp (d : ℕ) (p : IntPhaseSpace) : ℤ :=
  (d : ℤ) + (1 + (d : ℤ)) * (1 + p 0) * (1 + p 1)

/-- The sign exponent changes by an even amount under `p ↦ -p`:
`s_d(-p) = s_d(p) - 2(1+d)(p₁+p₂)`. This is the computation behind
[AFK25, equation (5.62), `eq:sfphasenegative`] in the proof of
[AFK25, Theorem 5.8, `thm:nupnumpeq1`], where the two SF phases at `±p` are found to agree. -/
lemma sfSignExp_neg (d : ℕ) (p : IntPhaseSpace) :
    sfSignExp d (-p) = sfSignExp d p - 2 * (1 + (d : ℤ)) * (p 0 + p 1) := by
  simp only [sfSignExp, Pi.neg_apply]
  ring

/-- **The parity of the sign exponent is even in `p`**, so the sign factor `(-1)^{s_d(p)}` of the
SF phase is unchanged by `p ↦ -p`. This is the first half of
[AFK25, equation (5.62), `eq:sfphasenegative`]. -/
lemma neg_one_zpow_sfSignExp_neg (d : ℕ) (p : IntPhaseSpace) :
    (-1 : ℂ) ^ sfSignExp d (-p) = (-1 : ℂ) ^ sfSignExp d p := by
  have heven : Even (-(2 * (1 + (d : ℤ)) * (p 0 + p 1))) :=
    ⟨-((1 + (d : ℤ)) * (p 0 + p 1)), by ring⟩
  rw [sfSignExp_neg, sub_eq_add_neg, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
    heven.neg_one_zpow, mul_one]

namespace AdmissibleTuple

/-- The exact Shintani--Faddeev phase of [AFK25, Definition 1.30, `dfn:SFKPhase`] for an arbitrary
admissible tuple `t`, an associated stabilizer `A`, and an integer index `p`:
`Φ_t(p) = (-1)^{s_d(p)} e^{-πi/12 · Ψ(A)} ξ_d^{-(f_{jm}/f)·Q(p)}`.

The rank-one `RankOneAdmissibleTuple.sfPhase` is this at `m = 1`, where `f_{jm}/f` becomes `f_j/f`
(`RankOneAdmissibleTuple.sfPhase_toAdmissibleTuple`). -/
@[source "AFK25, Definition 1.30, p. 16, dfn:SFKPhase" (symbol := "Φ_t(p)")]
noncomputable def sfPhase (t : AdmissibleTuple) (A : SL(2, ℤ)) (p : IntPhaseSpace) : ℂ :=
  (-1 : ℂ) ^ sfSignExp t.d p *
    Complex.exp (-π * I / 12 * (rademacherInvariant A : ℂ)) *
    (displacementPhase t.d) ^ (-((t.conductorRatio : ℤ) * t.Q.eval (p 0) (p 1)))

/-- **The SF phase is even in its index**: `Φ_t(-p) = Φ_t(p)`, for an arbitrary admissible tuple.
This is [AFK25, equation (5.62), `eq:sfphasenegative`], in the proof of
[AFK25, Theorem 5.8, `thm:nupnumpeq1`]. -/
lemma sfPhase_neg (t : AdmissibleTuple) (A : SL(2, ℤ)) (p : IntPhaseSpace) :
    t.sfPhase A (-p) = t.sfPhase A p := by
  simp only [sfPhase, Pi.neg_apply, neg_one_zpow_sfSignExp_neg, BinaryQF.eval_neg]

/-- The SF phase never vanishes: each of its three factors is a unit. -/
lemma sfPhase_ne_zero (t : AdmissibleTuple) (A : SL(2, ℤ)) (p : IntPhaseSpace) :
    t.sfPhase A p ≠ 0 :=
  mul_ne_zero (mul_ne_zero (zpow_ne_zero _ (by norm_num)) (Complex.exp_ne_zero _))
    (zpow_ne_zero _ (displacementPhase_ne_zero t.d))

/-- **The SF phase at the origin** is `Φ_t(0) = -e^{-πiΨ(A)/12}`: the sign exponent
`s_d(0) = 2d + 1` is odd and the quadratic-form factor is `ξ_d⁰ = 1`. This is the value used in
[AFK25, equation (5.65), `eq:nu01overnu0val`]. -/
lemma sfPhase_zero (t : AdmissibleTuple) (A : SL(2, ℤ)) :
    t.sfPhase A 0 = -Complex.exp (-π * I / 12 * (rademacherInvariant A : ℂ)) := by
  have hsign : sfSignExp t.d 0 = 2 * (t.d : ℤ) + 1 := by
    simp only [sfSignExp, Pi.zero_apply]
    ring
  have hodd : (-1 : ℂ) ^ (2 * (t.d : ℤ) + 1) = -1 :=
    (Odd.neg_one_zpow ⟨t.d, rfl⟩)
  simp only [sfPhase, hsign, hodd, Pi.zero_apply, BinaryQF.eval, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero, add_zero, neg_zero, zpow_zero, mul_one, neg_mul,
    one_mul]

/-! #### Transport of the phase under a change of representative

The phase half of [AFK25, Lemma 5.7, `lem:nupperiodicity`]. Writing `⟨a,b,c⟩ = (f_{jm}/f)Q` and
`p' = p + dq`, the two index-dependent factors of `Φ_t` move by

```text
s_d(p') - s_d(p) = (1+d)·d·(q₁(1+p₂) + q₂(1+p₁) + dq₁q₂),
a(p'^2_1 - p^2_1) + b(p'_1p'_2 - p_1p_2) + c(p'^2_2 - p^2_2)
  = d·(aq₁(2p₁+dq₁) + b(q₁p₂+q₂p₁+dq₁q₂) + cq₂(2p₂+dq₂)),
```

so both are multiples of `d`, and `ξ_d^{dk} = (-1)^{(d+1)k}` collapses each to a sign. The target
`⟨p',p⟩ = d(q₂p₁ - q₁p₂)` collapses the same way. For odd `d` every sign is `+1`. For even `d` the
remaining parity is that of `b(q₁p₂ + q₂p₁)`, which is `q₁p₂ + q₂p₁` exactly because `b` is odd,
and that matches `q₂p₁ - q₁p₂` modulo two.

The oddness of `b` in an even dimension is [AFK25, Corollary 5.4, `cor:fjmfqcmpsoddeven`],
supplied by `AdmissibleTuple.odd_gridScaledForm_of_even_d` in `SICs.Admissible.FormParity`, so the
transport law below is unconditional.

That argument is split into its three independent pieces: `transport_parity` is the integer parity,
over `ℤ` alone; `transport_sign_collapse` is the passage from `ξ_d` powers to signs, over `ℂ`
alone; and `exists_transport_exponents` names the three multiples of `d`. The transport law itself
is then their composition. -/

/-- The parity behind `AdmissibleTuple.sfPhase_transport`: with `D` the dimension, `⟨A,B,C⟩` the
scaled form `(f_{jm}/f)Q`, `p` the index and `q` the shift, the exponent of `-1` left over after
the collapse is even. For odd `D` the factor `D+1` is already even; for even `D` every term of the
second factor carries a visible `2` once `B` is odd. -/
private lemma transport_parity (D A B C p0 p1 q0 q1 : ℤ) (hb : Even D → Odd B) :
    Even ((D + 1) *
      (D * (q0 * (1 + p1) + q1 * (1 + p0) + D * (q0 * q1))
        - (A * (q0 * (2 * p0 + D * q0)) + B * (q0 * p1 + q1 * p0 + D * (q0 * q1)) +
            C * (q1 * (2 * p1 + D * q1)))
        - (q1 * p0 - q0 * p1))) := by
  rcases Int.even_or_odd D with hD | hD
  · obtain ⟨o, rfl⟩ := hb hD
    obtain ⟨e, rfl⟩ := hD
    exact Even.mul_left ⟨e * (q0 * (1 + p1) + q1 * (1 + p0) + (e + e) * (q0 * q1))
      - A * (q0 * (p0 + e * q0)) - o * (q0 * p1 + q1 * p0) - e * (2 * o + 1) * (q0 * q1)
      - C * (q1 * (p1 + e * q1)) - q1 * p0, by ring⟩ _
  · exact hD.add_one.mul_right _

/-- The sign collapse behind `AdmissibleTuple.sfPhase_transport`: `ξ_d^{dk} = (-1)^{(d+1)k}`
turns the three exponent differences into signs, and they cancel exactly when
`(d+1)(dY - X - Z)` is even. -/
private lemma transport_sign_collapse (d : ℕ) [NeZero d] (X Y Z : ℤ)
    (h : Even (((d : ℤ) + 1) * ((d : ℤ) * Y - X - Z))) :
    (-1 : ℂ) ^ (((d : ℤ) + 1) * ((d : ℤ) * Y)) * displacementPhase d ^ (-((d : ℤ) * X)) =
      displacementPhase d ^ ((d : ℤ) * Z) := by
  have hne : (-1 : ℂ) ≠ 0 := by norm_num
  rw [show (-((d : ℤ) * X)) = (d : ℤ) * (-X) by ring,
    displacementPhase_zpow_d_mul, displacementPhase_zpow_d_mul, ← zpow_add₀ hne,
    show ((d : ℤ) + 1) * ((d : ℤ) * Y) + ((d + 1 : ℕ) : ℤ) * (-X) =
        ((d + 1 : ℕ) : ℤ) * Z + ((d : ℤ) + 1) * ((d : ℤ) * Y - X - Z) by push_cast; ring,
    zpow_add₀ hne, h.neg_one_zpow, mul_one]

/-- The arithmetic content of `sfPhase_transport`: between congruent indices the sign exponent,
the scaled form value and the symplectic form all move by multiples of `d`, and the combination
`transport_sign_collapse` needs is even. -/
private lemma exists_transport_exponents (t : AdmissibleTuple) {p p' : IntPhaseSpace}
    (hmod : intPhaseSpaceMod t.d p' = intPhaseSpaceMod t.d p) :
    ∃ X Y Z : ℤ,
      sfSignExp t.d p' = sfSignExp t.d p + ((t.d : ℤ) + 1) * ((t.d : ℤ) * Y) ∧
      (t.conductorRatio : ℤ) * t.Q.eval (p' 0) (p' 1) =
        (t.conductorRatio : ℤ) * t.Q.eval (p 0) (p 1) + (t.d : ℤ) * X ∧
      intSymplecticForm p' p = (t.d : ℤ) * Z ∧
      Even (((t.d : ℤ) + 1) * ((t.d : ℤ) * Y - X - Z)) := by
  have hshift : ∀ i, ∃ m : ℤ, p' i = p i + (t.d : ℤ) * m := fun i => by
    obtain ⟨m, hm⟩ := ((ZMod.intCast_eq_intCast_iff _ _ _).mp (congrFun hmod i)).dvd
    exact ⟨-m, by linarith⟩
  obtain ⟨q0, hq0⟩ := hshift 0
  obtain ⟨q1, hq1⟩ := hshift 1
  refine ⟨_, _, _, ?_, ?_, ?_,
    transport_parity (t.d : ℤ) ((t.conductorRatio : ℤ) * t.Q.a) ((t.conductorRatio : ℤ) * t.Q.b)
      ((t.conductorRatio : ℤ) * t.Q.c) (p 0) (p 1) q0 q1
      (fun h => (t.odd_gridScaledForm_of_even_d (by exact_mod_cast h)).2.1)⟩
  · simp only [sfSignExp, hq0, hq1]; ring
  · simp only [BinaryQF.eval, hq0, hq1]; ring
  · simp only [intSymplecticForm, hq0, hq1]; ring

/-- **The phase half of [AFK25, Lemma 5.7, `lem:nupperiodicity`]**: for congruent integer indices
the Shintani--Faddeev phase transports by the symplectic root of unity,
`Φ_t(p') = ξ_d^{⟨p',p⟩} Φ_t(p)`.

The arithmetic input is [AFK25, Corollary 5.4, `cor:fjmfqcmpsoddeven`], used through
`odd_gridScaledForm_of_even_d`: in an even dimension the middle coefficient `b` of `(f_{jm}/f)Q`
is odd. In an odd dimension nothing about `Q` is needed. -/
lemma sfPhase_transport (t : AdmissibleTuple) (A : SL(2, ℤ)) (p p' : IntPhaseSpace)
    (hmod : intPhaseSpaceMod t.d p' = intPhaseSpaceMod t.d p) :
    t.sfPhase A p' = displacementPhase t.d ^ intSymplecticForm p' p * t.sfPhase A p := by
  obtain ⟨X, Y, Z, hE, hF, hS, hpar⟩ := t.exists_transport_exponents hmod
  rw [sfPhase, sfPhase, hE, hS, hF, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), neg_add,
    zpow_add₀ (displacementPhase_ne_zero t.d), ← transport_sign_collapse t.d X Y Z hpar]
  ring

end AdmissibleTuple

/-! ### Rank-one specialization

The rank-one conductor ratio agrees with the general ratio under `toAdmissibleTuple`. -/

namespace RankOneAdmissibleTuple

/-- The rank-one specialization of `AdmissibleTuple.sfPhase`, the Shintani--Faddeev phase of
[AFK25, Definition 1.30, `dfn:SFKPhase`] at `m = 1`. The conductor ratio `f_{jm}/f` is then
`f_j/f`. -/
noncomputable def sfPhase (t : RankOneAdmissibleTuple)
    (A : SL(2, ℤ)) (p : IntPhaseSpace) : ℂ :=
  t.toAdmissibleTuple.sfPhase A p

/-- When the form conductor is the full tower conductor, the conductor ratio disappears from the
SF phase. This is the case for the principal family `Q_d = ⟨1,1-d,1⟩`, whose form conductor is
exactly `f_j`. Specializes the formula `AdmissibleTuple.sfPhase`. -/
lemma sfPhase_of_conductorRatio_eq_one (t : RankOneAdmissibleTuple)
    (h : t.conductorRatio = 1) (A : SL(2, ℤ)) (p : IntPhaseSpace) :
    sfPhase t A p =
      (-1 : ℂ) ^ sfSignExp t.d p *
        Complex.exp (-π * I / 12 * (rademacherInvariant A : ℂ)) *
        (displacementPhase t.d) ^ (-t.Q.eval (p 0) (p 1)) := by
  simp only [sfPhase, AdmissibleTuple.sfPhase, toAdmissibleTuple_conductorRatio, h,
    Nat.cast_one, one_mul, toAdmissibleTuple_d, toAdmissibleTuple_Q]

/-- The rank-one phase `RankOneAdmissibleTuple.sfPhase` is definitionally the specialization of
`AdmissibleTuple.sfPhase` at `m = 1`. -/
lemma sfPhase_toAdmissibleTuple (t : RankOneAdmissibleTuple) (A : SL(2, ℤ)) (p : IntPhaseSpace) :
    t.toAdmissibleTuple.sfPhase A p = sfPhase t A p := rfl

end RankOneAdmissibleTuple

end SIC

end
