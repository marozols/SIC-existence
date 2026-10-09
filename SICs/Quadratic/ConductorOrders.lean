/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Quadratic.ConductorOneElements
import SICs.Quadratic.Orders
import SICs.Quadratic.OrderUnits

/-!
# The order of conductor `f` inside the field

The abstract order of discriminant `f²Δ₀` embedded in `K` as the order `𝒪_f`, and the norm-one
unit of that order over `ε^k` when `f ∣ f_k`.

This module follows [AFK25, Section 4, "Unit group of an order"] up to
[AFK25, equation (4.46), `eq:wtrmsej`], which writes `ε^k` in the coordinates of `𝒪_f` when
`f ∣ f_k`. It supplies the Zauner unit of an admissible tuple to
`SICs.Admissible.StabilizerExistence`.

## The argument

Let `Δ₀ = disc(K)`, `f ≥ 1`, and `Δ = f²Δ₀`. The abstract order `ℤ[ω]`, `ω = (Δ + √Δ)/2`, of
`SICs.Quadratic.FormOrders` embeds in `K` by `x + yω ↦ x + yθ`, where `θ ∈ K` is the element
over the positive root of the principal form of `Δ` (`RealQuadraticFieldData.rootPlusElement`),
so that `ρ₁(θ) = (Δ + f√Δ₀)/2` at the selected real place. The embedding intertwines the real
embedding `ι` of the abstract order with `ρ₁`. Its image is the order `𝒪_f = ℤ + f𝒪_K` of
[AFK25, Definition 1.47, `dfn:orderConductorf`].

If `f ∣ f_k`, the power `ε^k` lies in the image: the element `x + yω` with `y = f_k/f` and
`2x + yΔ = d_k - 1` has norm one by the Pell identity `(d_k - 1)² - f_k²Δ₀ = 4`, and it maps to
`ε^k = (d_k - 1 + f_k√Δ₀)/2` [AFK25, Lemma 4.3, `lem:towerbasic`] because both have this value
at the selected place. This is [AFK25, equation (4.46), `eq:wtrmsej`].

## References

- [AFK25, Definition 1.47, `dfn:orderConductorf`] and [AFK25, Definition 4.11, `df:ofufdef`]
- [AFK25, equation (4.46), `eq:wtrmsej`]
- [AFK25, Lemma 4.3, `lem:towerbasic`] for `ε^k = (d_k - 1 + f_k√Δ₀)/2`
-/

noncomputable section

namespace SIC

open BinaryQF

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]

namespace RealQuadraticFieldData

variable (F : RealQuadraticFieldData K) {Δ : ℤ} {f : ℕ}

/-! ### The embedding of the abstract order

The abstract order `ℤ[ω]` of discriminant `Δ = f²Δ₀` is `(conductorOneForm Δ).MonicOrder`; it
embeds in `K` by sending `ω` to the element `θ` over the positive root `(Δ + √Δ)/2` of the
principal form of `Δ`. -/

include F in
/-- A discriminant `Δ = f²Δ_K` is `0` or `1` modulo `4`, since `Δ_K` is
(`IsFundamentalDiscriminant.emod_four`) and `f² ≡ 0, 1 (mod 4)`. -/
lemma emod_four_of_eq_sq_mul_discr (hΔ : Δ = (f : ℤ) ^ 2 * NumberField.discr K) :
    Δ % 4 = 0 ∨ Δ % 4 = 1 := by
  rw [hΔ, Int.mul_emod, Int.sq_emod_four]
  rcases F.discr_fundamental.emod_four with h | h <;> simp [h]
  omega

include F in
/-- The principal form of `Δ = f²Δ_K` has discriminant `Δ`; `disc_conductorOneForm_of_emod_four`
at `emod_four_of_eq_sq_mul_discr`. -/
lemma disc_conductorOneForm_of_eq_sq_mul_discr (hΔ : Δ = (f : ℤ) ^ 2 * NumberField.discr K) :
    (conductorOneForm Δ).disc = (f : ℤ) ^ 2 * NumberField.discr K := by
  rw [disc_conductorOneForm_of_emod_four (F.emod_four_of_eq_sq_mul_discr hΔ), hΔ]

include F in
/-- The principal form of `Δ = f²Δ_K` has nonnegative discriminant, as `Δ_K > 0`. -/
lemma conductorOneForm_disc_nonneg (hΔ : Δ = (f : ℤ) ^ 2 * NumberField.discr K) :
    0 ≤ (conductorOneForm Δ).disc := by
  rw [F.disc_conductorOneForm_of_eq_sq_mul_discr hΔ]
  exact mul_nonneg (sq_nonneg _) F.discr_pos.le

include F in
/-- The principal form of `Δ = f²Δ_K` has positive discriminant when `f > 0`. -/
lemma conductorOneForm_disc_pos (hΔ : Δ = (f : ℤ) ^ 2 * NumberField.discr K) (hf : 0 < f) :
    0 < (conductorOneForm Δ).disc := by
  rw [F.disc_conductorOneForm_of_eq_sq_mul_discr hΔ]
  exact mul_pos (pow_pos (by exact_mod_cast hf) 2) F.discr_pos

/-- The element `θ` over the positive root of the principal form of `Δ = f²Δ_K` satisfies the
form's monic equation `θ² = -c + Δθ`, in the shape `QuadraticAlgebra.lift` takes; used by
`conductorOrderEmbedding`. -/
private lemma rootPlusElement_conductorOneForm_mul_self
    (hΔ : Δ = (f : ℤ) ^ 2 * NumberField.discr K) :
    F.rootPlusElement (conductorOneForm Δ) f * F.rootPlusElement (conductorOneForm Δ) f =
      (-(conductorOneForm Δ).c) • (1 : K) +
        (-(conductorOneForm Δ).b) • F.rootPlusElement (conductorOneForm Δ) f := by
  apply (realEmbeddingAt K F.place).injective
  have hroot := (conductorOneForm Δ).rootPlus_satisfies_quadratic_of_disc_nonneg
    (by simp) (F.conductorOneForm_disc_nonneg hΔ)
  simp only [map_mul, map_add, map_one,
    F.realEmbeddingAt_place_rootPlusElement (F.disc_conductorOneForm_of_eq_sq_mul_discr hΔ),
    zsmul_eq_mul, Int.cast_neg, map_neg, map_intCast]
  simp only [conductorOneForm_a, Int.cast_one, one_mul] at hroot
  nlinarith

/-- **The order of conductor `f` inside `K`**: the embedding `x + yω ↦ x + yθ` of the abstract
order `ℤ[ω]` of discriminant `Δ = f²Δ_K`, `ω = (Δ + √Δ)/2`, into `K`, where `θ` is the element
over the positive root of the principal form of `Δ` (`rootPlusElement`), so that
`ρ₁(θ) = (Δ + f√Δ_K)/2`. Its image is the order `𝒪_f = ℤ + f𝒪_K` of
[AFK25, Definition 1.47, `dfn:orderConductorf`], on whose units [AFK25, Definition 4.11,
`df:ofufdef`] is stated. -/
def conductorOrderEmbedding (hΔ : Δ = (f : ℤ) ^ 2 * NumberField.discr K) :
    (conductorOneForm Δ).MonicOrder →ₐ[ℤ] K :=
  QuadraticAlgebra.lift ⟨F.rootPlusElement (conductorOneForm Δ) f,
    F.rootPlusElement_conductorOneForm_mul_self hΔ⟩

/-- Coordinate formula for `conductorOrderEmbedding`: `x + yω ↦ x + yθ`. -/
@[simp]
lemma conductorOrderEmbedding_apply (hΔ : Δ = (f : ℤ) ^ 2 * NumberField.discr K)
    (z : (conductorOneForm Δ).MonicOrder) :
    F.conductorOrderEmbedding hΔ z =
      (z.re : K) + (z.im : K) * F.rootPlusElement (conductorOneForm Δ) f := by
  simp [conductorOrderEmbedding, QuadraticAlgebra.lift_apply_apply, zsmul_eq_mul]

/-- **The embedding intertwines the real embeddings**: `ρ₁(x + yθ) = ι(x + yω)`, the value of
the abstract order at its positive root (`monicOrderReal`). -/
lemma realEmbeddingAt_place_conductorOrderEmbedding
    (hΔ : Δ = (f : ℤ) ^ 2 * NumberField.discr K) (z : (conductorOneForm Δ).MonicOrder) :
    realEmbeddingAt K F.place (F.conductorOrderEmbedding hΔ z) =
      monicOrderReal (conductorOneForm_a Δ) (F.conductorOneForm_disc_nonneg hΔ) z := by
  simp only [conductorOrderEmbedding_apply, map_add, map_mul, map_intCast,
    F.realEmbeddingAt_place_rootPlusElement (F.disc_conductorOneForm_of_eq_sq_mul_discr hΔ),
    monicOrderReal_apply]

end RealQuadraticFieldData

namespace RealQuadraticUnitData

variable (T : RealQuadraticUnitData K) {Δ : ℤ} {f : ℕ}

/-! ### The powers `ε^k` in the order

For `f ∣ f_k`, the coordinates `x + yω`, `y = f_k/f`, `2x + yΔ = d_k - 1`, give a norm-one unit
of the abstract order mapping to `ε^k = (d_k - 1 + f_k√Δ₀)/2`. -/

/-- The positive discriminant of the principal form of `Δ = f²Δ_K` when `f ∣ f_k`, which forces
`f > 0`; supplies the `hdisc` argument of the real-value maps below. -/
lemma conductorOneForm_disc_pos_of_dvd (hΔ : Δ = (f : ℤ) ^ 2 * NumberField.discr K) {k : ℕ+}
    (hk : f ∣ (T.canonicalConductor k : ℕ)) : 0 < (conductorOneForm Δ).disc :=
  T.conductorOneForm_disc_pos hΔ (Nat.pos_of_dvd_of_pos hk (T.canonicalConductor k).pos)

/-- **The element of the order over `ε^k`**: `x + yω` with root coordinate `y = f_k/f` and
`x = (d_k - 1 - yΔ)/2`, the coordinates of `ε^k` in the order `𝒪_f` written in the basis
`(1, ω)`, `ω = (Δ + √Δ)/2`, of the abstract order. [AFK25, equation (4.46), `eq:wtrmsej`]
writes the same element in the basis `(1, (Δ₀ + √Δ₀)/2)` of `𝒪_K`. The formula is total; its
properties need `f ∣ f_k`. -/
def epsilonPowElement (Δ : ℤ) (f : ℕ) (k : ℕ+) : (conductorOneForm Δ).MonicOrder :=
  ⟨(((T.canonicalDimension k : ℕ) : ℤ) - 1 -
      (((T.canonicalConductor k : ℕ) / f : ℕ) : ℤ) * Δ) / 2,
    (((T.canonicalConductor k : ℕ) / f : ℕ) : ℤ)⟩

/-- The root coordinate of the element over `ε^k` is `f_k/f`. -/
@[simp]
lemma epsilonPowElement_im (Δ : ℤ) (f : ℕ) (k : ℕ+) :
    (T.epsilonPowElement Δ f k).im = (((T.canonicalConductor k : ℕ) / f : ℕ) : ℤ) := rfl

/-- The Pell identity `(d_k - 1)² - Δ (f_k/f)² = 4` of the element over `ε^k`, from
`f_k² Δ₀ = (d_k - 3)(d_k + 1)` (`canonicalConductor_sq_mul_discr`) and `(f_k/f) f = f_k`. -/
lemma canonicalDimension_sub_one_sq_sub_disc_mul_sq
    (hΔ : Δ = (f : ℤ) ^ 2 * NumberField.discr K) {k : ℕ+}
    (hk : f ∣ (T.canonicalConductor k : ℕ)) :
    (((T.canonicalDimension k : ℕ) : ℤ) - 1) ^ 2 -
      Δ * (((T.canonicalConductor k : ℕ) / f : ℕ) : ℤ) ^ 2 = 4 := by
  have hmul : (((T.canonicalConductor k : ℕ) / f : ℕ) : ℤ) * (f : ℤ) =
      ((T.canonicalConductor k : ℕ) : ℤ) := by exact_mod_cast Nat.div_mul_cancel hk
  rw [hΔ]
  linear_combination -T.canonicalConductor_sq_mul_discr k +
    -NumberField.discr K * (hmul *
      ((((T.canonicalConductor k : ℕ) / f : ℕ) : ℤ) * f + (T.canonicalConductor k : ℕ)))

/-- The trace identity `2x + Δy = d_k - 1` of the element over `ε^k`; the division by `2` is
exact because `d_k - 1 ≡ yΔ (mod 2)` by the Pell identity. -/
lemma two_mul_epsilonPowElement_re_add (hΔ : Δ = (f : ℤ) ^ 2 * NumberField.discr K) {k : ℕ+}
    (hk : f ∣ (T.canonicalConductor k : ℕ)) :
    2 * (T.epsilonPowElement Δ f k).re + Δ * (T.epsilonPowElement Δ f k).im =
      ((T.canonicalDimension k : ℕ) : ℤ) - 1 := by
  have hp := congrArg (fun n : ℤ ↦ n % 2)
    (T.canonicalDimension_sub_one_sq_sub_disc_mul_sq hΔ hk)
  have hpar : (((T.canonicalDimension k : ℕ) : ℤ) - 1 -
      (((T.canonicalConductor k : ℕ) / f : ℕ) : ℤ) * Δ) % 2 = 0 := by
    rcases Int.emod_two_eq_zero_or_one (((T.canonicalDimension k : ℕ) : ℤ) - 1)
      with hd | hd <;>
      rcases Int.emod_two_eq_zero_or_one (((T.canonicalConductor k : ℕ) / f : ℕ) : ℤ)
        with hf | hf <;>
      rcases Int.emod_two_eq_zero_or_one Δ with hD | hD <;>
      simp only [pow_two, Int.sub_emod, Int.mul_emod, Int.emod_emod, hd, hf, hD] at hp <;>
      simp only [Int.sub_emod, Int.mul_emod, Int.emod_emod, hd, hf, hD] <;>
      norm_num at hp <;> norm_num
  have h := Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hpar)
  change 2 * (_ / 2) + Δ * (((T.canonicalConductor k : ℕ) / f : ℕ) : ℤ) = _
  linarith

/-- The element over `ε^k` has norm one, by the Pell identity. -/
lemma norm_epsilonPowElement (hΔ : Δ = (f : ℤ) ^ 2 * NumberField.discr K) {k : ℕ+}
    (hk : f ∣ (T.canonicalConductor k : ℕ)) : (T.epsilonPowElement Δ f k).norm = 1 := by
  have hp := T.canonicalDimension_sub_one_sq_sub_disc_mul_sq hΔ hk
  have ht := T.two_mul_epsilonPowElement_re_add hΔ hk
  have hd := disc_conductorOneForm_of_emod_four (T.emod_four_of_eq_sq_mul_discr hΔ)
  simp only [BinaryQF.disc, discrim, conductorOneForm, neg_sq, mul_one] at hd
  rw [QuadraticAlgebra.norm_def]
  simp only [conductorOneForm, neg_neg]
  change _ - Δ * (T.epsilonPowElement Δ f k).im ^ 2 = 4 at hp
  nlinarith [congrArg (fun n : ℤ ↦ n ^ 2) ht,
    congrArg (fun n : ℤ ↦ n * (T.epsilonPowElement Δ f k).im ^ 2) hd]

/-- The element over `ε^k` as a norm-one unit of the abstract order. -/
def epsilonPowUnit (hΔ : Δ = (f : ℤ) ^ 2 * NumberField.discr K) {k : ℕ+}
    (hk : f ∣ (T.canonicalConductor k : ℕ)) : (conductorOneForm Δ).monicNormOneUnits :=
  ⟨Unitary.toUnits ⟨T.epsilonPowElement Δ f k,
      QuadraticAlgebra.mem_unitary (T.norm_epsilonPowElement hΔ hk)⟩,
    T.norm_epsilonPowElement hΔ hk⟩

/-- The underlying element of `epsilonPowUnit` is `epsilonPowElement`. -/
@[simp]
lemma coe_epsilonPowUnit (hΔ : Δ = (f : ℤ) ^ 2 * NumberField.discr K) {k : ℕ+}
    (hk : f ∣ (T.canonicalConductor k : ℕ)) :
    ((T.epsilonPowUnit hΔ hk : (conductorOneForm Δ).MonicOrderˣ) :
      (conductorOneForm Δ).MonicOrder) = T.epsilonPowElement Δ f k := rfl

/-- **`ε^k` in the coordinates of `𝒪_f`**, [AFK25, equation (4.46), `eq:wtrmsej`]: for
`f ∣ f_k`, the element `x + yω` with `y = f_k/f`, `2x + yΔ = d_k - 1` maps to `ε^k`. Both sides
have the value `(d_k - 1 + f_k√Δ₀)/2` at the selected place, by `canonicalDimension_spec` and
`canonicalConductor_spec`. -/
@[source "AFK25, equation (4.46), p. 53, eq:wtrmsej"]
theorem conductorOrderEmbedding_epsilonPowElement
    (hΔ : Δ = (f : ℤ) ^ 2 * NumberField.discr K) {k : ℕ+}
    (hk : f ∣ (T.canonicalConductor k : ℕ)) :
    T.conductorOrderEmbedding hΔ (T.epsilonPowElement Δ f k) = (T.epsilon : K) ^ (k : ℕ) := by
  apply (realEmbeddingAt K T.place).injective
  rw [T.realEmbeddingAt_place_conductorOrderEmbedding hΔ, monicOrderReal_apply,
    rootPlus_conductorOneForm_of_emod_four (T.emod_four_of_eq_sq_mul_discr hΔ)]
  have hs : Real.sqrt (Δ : ℝ) = (f : ℝ) * Real.sqrt (NumberField.discr K) := by
    rw [hΔ, T.sqrt_conductor_mul f]
  have ht : 2 * ((T.epsilonPowElement Δ f k).re : ℝ) +
      (Δ : ℝ) * ((T.epsilonPowElement Δ f k).im : ℝ) =
      (T.canonicalDimension k : ℕ) - 1 := by
    exact_mod_cast T.two_mul_epsilonPowElement_re_add hΔ hk
  have hm : ((T.epsilonPowElement Δ f k).im : ℝ) * (f : ℝ) =
      (T.canonicalConductor k : ℕ) := by
    simp only [epsilonPowElement_im]
    exact_mod_cast Nat.div_mul_cancel hk
  have hd := T.canonicalDimension_spec k
  have hc := T.canonicalConductor_spec k
  change (T.canonicalDimension k : ℕ) =
    T.epsilonReal ^ (k : ℕ) + (T.epsilonReal ^ (k : ℕ))⁻¹ + (1 : ℝ) at hd
  change (T.canonicalConductor k : ℕ) * Real.sqrt (NumberField.discr K) =
    T.epsilonReal ^ (k : ℕ) - (T.epsilonReal ^ (k : ℕ))⁻¹ at hc
  rw [hs, map_pow]
  change _ = T.epsilonReal ^ (k : ℕ)
  linear_combination ht / 2 + hc / 2 + hd / 2 +
    (hm * Real.sqrt (NumberField.discr K)) / 2

/-- The element over `ε^k` has real value `ε^k > 1`. -/
lemma one_lt_monicNormOneUnitReal_epsilonPowUnit
    (hΔ : Δ = (f : ℤ) ^ 2 * NumberField.discr K) {k : ℕ+}
    (hk : f ∣ (T.canonicalConductor k : ℕ)) :
    1 < (monicNormOneUnitReal (conductorOneForm_a Δ) (T.conductorOneForm_disc_pos_of_dvd hΔ hk)
      (T.epsilonPowUnit hΔ hk) : ℝ) := by
  rw [coe_monicNormOneUnitReal, coe_epsilonPowUnit,
    ← T.realEmbeddingAt_place_conductorOrderEmbedding hΔ,
    T.conductorOrderEmbedding_epsilonPowElement hΔ hk, map_pow]
  exact T.one_lt_epsilonReal_pow k

end RealQuadraticUnitData

end SIC

end
