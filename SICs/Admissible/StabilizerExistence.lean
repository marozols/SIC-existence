/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Admissible.AssociatedStabilizers
import SICs.Quadratic.CanonicalRepresentation
import SICs.Quadratic.ConductorOrders
import SICs.Quadratic.UnitCongruences

/-!
# Existence of the associated stabilizers

The level/Zauner pair of [AFK25, Theorem 4.50, `tm:symgp`]: `L_{z,t} = χ_Q(z_t)` and
`A_t = L_{z,t}^{2m+1}`, oriented like `Q`, with `S_d(Q) = ⟨A_t⟩`.

This file proves equations (4.191), (4.192), and (4.194) of [AFK25, Theorem 4.50, `tm:symgp`].
Its core is `AdmissibleTuple.exists_isAssociatedStabilizerPair`: every admissible tuple
`t = (d, r, Q)` has matrices `L_{z,t}` and `A_t` satisfying
`AdmissibleTuple.IsAssociatedStabilizerPair`, that is, the doubled formula
`2 L_{z,t} = (d_j - 1) I + (f_j/f) 2SQ` of [AFK25, Definition 1.28, `dfn:AssociatedStabilizers`],
the power relation `A_t = L_{z,t}^{2m+1}`, the orientation `sgn(A_t) = sgn(Q)`, and the generation
`S_d(Q) = ⟨A_t⟩`. The other clauses of the theorem (the generator `L_t` of `S(Q)/{±I}`, the
determinant-one generator `L_{+,t}`, the level `n_t`, the positivity of traces in `S_d(Q)`, and the
congruence modulo `2d`) are not formalized.

## Mathematical argument

Let `Δ = disc(Q) = f² Δ₀` and let `𝒪 = ℤ[ω]`, `ω = (Δ + √Δ)/2`, be the order of discriminant
`Δ`, which is the order `𝒪_f` of conductor `f`. The tower unit `ε^j` lies in `𝒪_f` because
`f ∣ f_j`: by [AFK25, equation (4.46), `eq:wtrmsej`],

`ε^j = (d_j - 1 - f_j Δ₀)/2 + f_j (Δ₀ + √Δ₀)/2 = x + yω`, with `y = f_j/f` and `2x + yΔ = d_j - 1`.

The element `z_t = x + yω` is defined here by these coordinates; it has trace `d_j - 1` and norm
`1` by the Pell identity `(d_j - 1)² - Δ (f_j/f)² = 4` of the tuple
(`RealQuadraticUnitData.norm_epsilonPowElement`). Its canonical
representation `L_{z,t} = χ_Q(z_t)` satisfies the doubled formula by `twice_canonicalRep`, and
`A_t = L_{z,t}^{2m+1} = χ_Q(z_t^{2m+1})` is oriented like `Q` because `z_t^{2m+1} > 1` has
positive root coordinate.

For the generation statement, `S(Q) ∩ SL₂(ℤ) = χ_Q(𝒰⁺)` where `𝒰⁺` is the norm-one unit group
of `𝒪` (`range_canonicalRepUnit`), and `𝒰⁺ = {±v^k}` for the fundamental unit `v` (the descent of
`SICs.Quadratic.OrderUnits`), with `z_t = v^n` for some positive exponent `n`. The level
condition `χ_Q(u) ∈ Γ(d)` reads `u ≡ 1 (mod d)`
in `𝒪` (`canonicalRepUnit_mem_stabilityGroupLevel_iff_dvd`), and
`SICs.Quadratic.UnitCongruences` shows, from the identity `z_t^{2m+1} - 1 = d z_t^m (z_t - 1)` of
[AFK25, Lemma 4.23, `lem:dimgridtechres`, equation (4.90), `eq:epowerminusone`], that
`v^k ≡ 1 (mod d)` exactly when `(2m+1)n ∣ k`, and that `v^k ≡ -1 (mod d)` never holds. Hence
`S_d(Q) = ⟨χ_Q(v)^{(2m+1)n}⟩ = ⟨A_t⟩`.

## References

- [AFK25, Theorem 4.50, `tm:symgp`], equations (4.191), (4.192), and (4.194)
- [AFK25, Definition 1.28, `dfn:AssociatedStabilizers`]
- [AFK25, Lemma 4.23, `lem:dimgridtechres`], equation (4.90), for the generation argument
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

open BinaryQF

namespace AdmissibleTuple

variable (t : AdmissibleTuple)

/-! ### The Zauner unit

The element `z_t ∈ 𝒪` with the coordinates of `ε^j`, [AFK25, equation (4.46), `eq:wtrmsej`]:
root coordinate `y = f_j/f` and trace `d_j - 1`. It is the element
`RealQuadraticUnitData.epsilonPowElement` of `SICs.Quadratic.ConductorOrders` at `k = j`, whose
norm one and real value `ε^j` that module proves. -/

/-- The discriminant factorization `disc(Q) = f² Δ₀` of the tuple, `IsConductor.disc_eq` in the
shape the order embedding `RealQuadraticFieldData.conductorOrderEmbedding` takes. -/
lemma disc_eq_sq_mul_discr :
    t.Q.disc = ((t.formConductor : ℕ) : ℤ) ^ 2 * NumberField.discr t.triple.K :=
  t.formConductor_spec.disc_eq

/-- The Zauner unit `z_t = x + yω` of the order of `disc(Q)`, with root coordinate `y = f_j/f`
and real coordinate `x = (d_j - 1 - yΔ)/2`, the coordinates of `ε^j` in
[AFK25, equation (4.46), `eq:wtrmsej`]: `RealQuadraticUnitData.epsilonPowElement` at `k = j`. -/
def zaunerElement : t.Q.DiscOrder :=
  t.triple.tower.epsilonPowElement t.Q.disc (t.formConductor : ℕ) t.triple.j

/-- The root coordinate of the Zauner unit is `f_j/f`. -/
@[simp]
lemma zaunerElement_im : t.zaunerElement.im = (t.towerConductorRatio : ℤ) := rfl

/-- The trace identity `2x + Δy = d_j - 1` of the Zauner unit,
`RealQuadraticUnitData.two_mul_epsilonPowElement_re_add` at the tuple. -/
lemma two_mul_zaunerElement_re_add :
    2 * t.zaunerElement.re + t.Q.disc * t.zaunerElement.im = (t.triple.towerDimension : ℤ) - 1 :=
  t.triple.tower.two_mul_epsilonPowElement_re_add t.disc_eq_sq_mul_discr t.formConductor_dvd

/-- The Zauner unit has norm one, by the Pell identity of the tuple
(`RealQuadraticUnitData.norm_epsilonPowElement`). -/
lemma norm_zaunerElement : t.zaunerElement.norm = 1 :=
  t.triple.tower.norm_epsilonPowElement t.disc_eq_sq_mul_discr t.formConductor_dvd

/-- The Zauner unit as a norm-one unit of the order, `RealQuadraticUnitData.epsilonPowUnit` at
`k = j`. -/
def zaunerUnit : (conductorOneForm t.Q.disc).monicNormOneUnits :=
  t.triple.tower.epsilonPowUnit t.disc_eq_sq_mul_discr t.formConductor_dvd

/-- The underlying element of `zaunerUnit` is `zaunerElement`. -/
@[simp]
lemma coe_zaunerUnit :
    ((t.zaunerUnit : (conductorOneForm t.Q.disc).MonicOrderˣ) : t.Q.DiscOrder) =
      t.zaunerElement := rfl

/-- The characteristic equation `z_t² = (d_j - 1) z_t - 1` of the Zauner unit, in the form taken
by `RealQuadraticUnitData.pow_two_mul_add_one_sub_one_eq_dimensionGrid_mul`. -/
lemma zaunerElement_sq :
    t.zaunerElement ^ 2 =
      ((t.triple.tower.dimensionInt (t.triple.j : ℕ) - 1 : ℤ) : t.Q.DiscOrder) * t.zaunerElement -
        1 := by
  have h := QuadraticAlgebra.sq_eq_trace_smul_sub_norm t.zaunerElement
  rw [t.norm_zaunerElement, map_one, zsmul_eq_mul] at h
  have htr : QuadraticAlgebra.trace t.zaunerElement =
      t.triple.tower.dimensionInt (t.triple.j : ℕ) - 1 := by
    rw [← t.triple.tower.canonicalDimension_coe_int t.triple.j]
    change _ = (t.triple.towerDimension : ℤ) - 1
    rw [← t.two_mul_zaunerElement_re_add, t.Q.discOrder_trace]
  rw [h, htr]

/-- **[AFK25, Lemma 4.23, `lem:dimgridtechres`, equation (4.90), `eq:epowerminusone`]** for the
Zauner unit: `z_t^{2m+1} - 1 = d z_t^m (z_t - 1)`, with `d = d_{j,m}` the dimension of the
tuple. -/
lemma zaunerElement_pow_sub_one :
    t.zaunerElement ^ (2 * (t.triple.m : ℕ) + 1) - 1 =
      (t.d : t.Q.DiscOrder) * (t.zaunerElement ^ (t.triple.m : ℕ) * (t.zaunerElement - 1)) := by
  have h := t.triple.tower.pow_two_mul_add_one_sub_one_eq_dimensionGrid_mul t.triple.j
    t.zaunerElement_sq t.triple.m
  rw [h, t.d_eq_dimension]
  rfl

/-! ### The real value of the Zauner unit

In the real embedding at `ω = (Δ + √Δ)/2`, `2 ι(z_t) = d_j - 1 + y√Δ > 2`. -/

/-- The principal form of `disc(Q)` has positive discriminant, since `Q` is indefinite. -/
lemma conductorOneForm_disc_disc_pos : 0 < (conductorOneForm t.Q.disc).disc := by
  rw [disc_conductorOneForm_disc]
  exact t.form_admissible.disc_pos

/-- The real value of the Zauner unit exceeds one: `ι(z_t) = ε^j > 1`
(`RealQuadraticUnitData.one_lt_monicNormOneUnitReal_epsilonPowUnit`). -/
lemma one_lt_real_zaunerUnit :
    1 < (monicNormOneUnitReal (conductorOneForm_a t.Q.disc) t.conductorOneForm_disc_disc_pos
      t.zaunerUnit : ℝ) :=
  t.triple.tower.one_lt_monicNormOneUnitReal_epsilonPowUnit t.disc_eq_sq_mul_discr
    t.formConductor_dvd

/-! ### The associated stabilizers

`L_{z,t} = χ_Q(z_t)` and `A_t = L_{z,t}^{2m+1}`, [AFK25, Theorem 4.50, `tm:symgp`, equations
(4.191) and (4.192), `eq:LzStabilizerTermsUnit` and `eq:AStabilizerTermsUnit`]. -/

/-- The Zauner generator `L_{z,t} = χ_Q(z_t)`, [AFK25, Theorem 4.50, `tm:symgp`, equation (4.191),
`eq:LzStabilizerTermsUnit`]. -/
@[source "AFK25, Theorem 4.50, p. 70, tm:symgp (equation (4.191))" (symbol := "L_{z,t}")]
def zaunerGenerator : SL(2, ℤ) := t.Q.canonicalRepUnit t.zaunerUnit

/-- The level generator `A_t = L_{z,t}^{2m+1}`, [AFK25, Theorem 4.50, `tm:symgp`, equation
(4.192), `eq:AStabilizerTermsUnit`]. -/
@[source "AFK25, Theorem 4.50, p. 70, tm:symgp (equation (4.192))" (symbol := "A_t")]
def levelGenerator : SL(2, ℤ) := t.zaunerGenerator ^ (2 * (t.triple.m : ℕ) + 1)

/-- The doubled formula `2 L_{z,t} = (d_j - 1) I + (f_j/f) 2SQ` of
[AFK25, Definition 1.28, `dfn:AssociatedStabilizers`, equation (1.41)]. -/
lemma twice_zaunerGenerator :
    (2 : ℤ) • (t.zaunerGenerator : Mat(2, ℤ)) =
      ((t.triple.towerDimension : ℤ) - 1) • (1 : Mat(2, ℤ)) +
        ((t.towerConductorRatio : ℤ)) • t.Q.twiceSQ := by
  change (2 : ℤ) • t.Q.canonicalRep t.zaunerElement = _
  rw [t.Q.twice_canonicalRep, t.two_mul_zaunerElement_re_add, zaunerElement_im]

/-- The level generator is the canonical representation of `z_t^{2m+1}`. -/
lemma coe_levelGenerator :
    (t.levelGenerator : Mat(2, ℤ)) =
      t.Q.canonicalRep (t.zaunerElement ^ (2 * (t.triple.m : ℕ) + 1)) := by
  rw [levelGenerator, zaunerGenerator, ← map_pow, coe_canonicalRepUnit, Subgroup.coe_pow,
    Units.val_pow_eq_pow_val, coe_zaunerUnit]

/-- The orientation `sgn(A_t) = sgn(Q)`: `z_t^{2m+1} > 1` has positive root coordinate. -/
lemma signMatrix_levelGenerator :
    signMatrix (t.levelGenerator : Mat(2, ℤ)) = t.Q.sign := by
  have hpos : 0 < (((t.zaunerUnit ^ (2 * (t.triple.m : ℕ) + 1) :
      (conductorOneForm t.Q.disc).monicNormOneUnits) :
        (conductorOneForm t.Q.disc).MonicOrderˣ) : t.Q.DiscOrder).im := by
    apply im_pos_of_one_lt_monicNormOneUnitReal (conductorOneForm_a t.Q.disc)
      t.conductorOneForm_disc_disc_pos
    rw [map_pow, Units.val_pow_eq_pow_val]
    exact one_lt_pow₀ t.one_lt_real_zaunerUnit (by omega)
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, coe_zaunerUnit] at hpos
  rw [coe_levelGenerator, signMatrix_canonicalRep t.form_admissible.a_ne_zero hpos.ne',
    Int.sign_eq_one_of_pos hpos, one_mul]

/-! ### Cyclic generation

`S_d(Q) = ⟨A_t⟩`, [AFK25, Theorem 4.50, `tm:symgp`, equation (4.194),
`eq:QStabilityGroupGenerators2`]. -/

/-- **`S_d(Q)` is generated by `A_t`**, [AFK25, Theorem 4.50, `tm:symgp`, equation (4.194),
`eq:QStabilityGroupGenerators2`]. -/
@[source "AFK25, Theorem 4.50, p. 70, tm:symgp (equation (4.194))"]
theorem stabilityGroupLevel_eq_zpowers_levelGenerator :
    t.Q.stabilityGroupLevel t.d = Subgroup.zpowers t.levelGenerator := by
  have hQ : t.Q.IsPrimitive := t.form_admissible.isPrimitive
  set ha := (conductorOneForm_a t.Q.disc)
  set hdisc := t.conductorOneForm_disc_disc_pos
  obtain ⟨v, hv⟩ := exists_isFundamentalNormOneUnit t.zaunerUnit t.one_lt_real_zaunerUnit
  obtain ⟨n, hn, hzv⟩ := hv.exists_eq_pow_of_one_lt t.one_lt_real_zaunerUnit
  have hvz : ((v : (conductorOneForm t.Q.disc).MonicOrderˣ) : t.Q.DiscOrder) ^ n =
      t.zaunerElement := by
    rw [← coe_zaunerUnit, hzv, Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  have hident := t.zaunerElement_pow_sub_one
  rw [← hvz] at hident
  have hm : 0 < (t.triple.m : ℕ) := t.triple.m.pos
  -- `A_t = χ_Q(v)^N` with `N = n(2m+1)`.
  have hA : t.levelGenerator = t.Q.canonicalRepUnit v ^ (n * (2 * (t.triple.m : ℕ) + 1)) := by
    rw [levelGenerator, zaunerGenerator, hzv, map_pow, ← pow_mul]
  apply le_antisymm
  · intro M hM
    have hstab : M ∈ t.Q.stabilityGroupSL := hM.1
    rw [← range_canonicalRepUnit hQ] at hstab
    obtain ⟨u, rfl⟩ := hstab
    rw [canonicalRepUnit_mem_stabilityGroupLevel_iff_dvd hQ] at hM
    obtain ⟨k, hk | hk⟩ := hv.eq_zpow_or_neg_zpow u
    · have hu : u = v ^ k := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)
      rw [hu, Subgroup.coe_zpow] at hM
      obtain ⟨l, hl⟩ := (dvd_zpow_sub_one_iff ha hdisc hv.one_lt hn hm hident k).1 hM
      rw [Subgroup.mem_zpowers_iff]
      exact ⟨l, by rw [hA, hu, map_zpow, hl, zpow_mul, zpow_natCast]⟩
    · exfalso
      rw [hk, Units.val_neg, show -(((v : (conductorOneForm t.Q.disc).MonicOrderˣ) ^ k :
          (conductorOneForm t.Q.disc).MonicOrderˣ) : t.Q.DiscOrder) - 1 =
          -((((v : (conductorOneForm t.Q.disc).MonicOrderˣ) ^ k :
            (conductorOneForm t.Q.disc).MonicOrderˣ) : t.Q.DiscOrder) + 1) by ring,
        dvd_neg] at hM
      exact not_dvd_zpow_add_one ha hdisc hv.one_lt hn hm hident k hM
  · rw [Subgroup.zpowers_le, hA, ← map_pow, canonicalRepUnit_mem_stabilityGroupLevel_iff_dvd hQ,
      Subgroup.coe_pow]
    have := dvd_zpow_level_sub_one (v := v) (n := n) (m := (t.triple.m : ℕ)) (d := t.d) hident
    rwa [zpow_natCast] at this

/-! ### Existence of the level/Zauner pair

The four conditions above are exactly `AdmissibleTuple.IsAssociatedStabilizerPair`, which gives
the pair of [AFK25, Theorem 4.50, `tm:symgp`]. -/

/-- **The associated stabilizers of a tuple**: `A_t = L_{z,t}^{2m+1}` and `L_{z,t} = χ_Q(z_t)`
satisfy `IsAssociatedStabilizerPair`. This is [AFK25, Theorem 4.50, `tm:symgp`]. -/
theorem isAssociatedStabilizerPair_levelGenerator :
    t.IsAssociatedStabilizerPair t.levelGenerator t.zaunerGenerator :=
  ⟨t.twice_zaunerGenerator, rfl, t.signMatrix_levelGenerator,
    t.stabilityGroupLevel_eq_zpowers_levelGenerator⟩

/-- **Existence of the associated stabilizers**, [AFK25, Definition 1.28,
`dfn:AssociatedStabilizers`] and [AFK25, Theorem 4.50, `tm:symgp`]: every admissible tuple `t`
has matrices `A_t` and `L_{z,t}` satisfying `IsAssociatedStabilizerPair`. Together with
`IsAssociatedStabilizerPair.unique` this is the source's pair `(A_t, L_{z,t})`, namely
`(levelGenerator, zaunerGenerator)`. -/
theorem exists_isAssociatedStabilizerPair (t : AdmissibleTuple) :
    ∃ A_t Lz : SL(2, ℤ), t.IsAssociatedStabilizerPair A_t Lz :=
  ⟨t.levelGenerator, t.zaunerGenerator, t.isAssociatedStabilizerPair_levelGenerator⟩

end AdmissibleTuple

end SIC

end
