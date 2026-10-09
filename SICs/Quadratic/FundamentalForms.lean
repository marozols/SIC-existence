/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Quadratic.Forms

/-!
# The Conductor-One Form of a Fundamental Discriminant

The canonical conductor-one form for a positive nonsquare fundamental discriminant.

For every fundamental discriminant `Δ₀`, the uniform principal form
`⟨1, -Δ₀, (Δ₀² - Δ₀) / 4⟩` is integral and has discriminant `Δ₀`. Its leading coefficient
is one, so it is primitive; when `Δ₀` is positive and nonsquare, it is also indefinite and
irreducible. Thus every positive, nonsquare fundamental discriminant is the discriminant of an
admissible form.

The positive root of this form is `(Δ₀ + √Δ₀) / 2`, the standard generator of the maximal
order.

## References

- [AFK25] Appleby, Flammia, Kopp, arXiv:2501.03970v2, Section 1.3
- [72] G. S. Kopp, "The Shintani--Faddeev modular cocycle: Stark units from q-Pochhammer
  ratios," arXiv:2411.06763v3, Lemma 4.42
-/

noncomputable section

namespace SIC

open BinaryQF

/-! ### The uniform conductor-one form

The two residue classes of a fundamental discriminant make `(Δ₀² - Δ₀) / 4` integral.
This gives one formula for the principal monic form in both the odd and even cases. -/

/-- The principal form `⟨1, -Δ₀, (Δ₀² - Δ₀)/4⟩` of a fundamental discriminant `Δ₀`. Its positive
root is `(Δ₀ + √Δ₀)/2`, the generator of the maximal order `𝒪₁` in
[AFK25, Definition 1.47, `dfn:orderConductorf`]. Being a root of a form of conductor `1`, it is a
quadratic number of conductor `1` in the sense used by [72, Kopp (2024), Lemma 4.42, `lem:fto1`],
which asserts that every quadratic number is an integral fractional linear transform of some such
`α` but neither singles this one out nor defines the form. This uniform representative is
equivalent to the parity-dependent principal form displayed in [22, Buell (1989), §4.2, p. 55]. -/
@[source "22, Section 4.2, p. 55 (principal form, equivalent representative)"]
def conductorOneForm (Δ₀ : ℤ) : BinaryQF :=
  ⟨1, -Δ₀, (Δ₀ ^ 2 - Δ₀) / 4⟩

/-- The principal form is monic, `a = 1`; see `conductorOneForm`. -/
@[simp]
lemma conductorOneForm_a (Δ : ℤ) : (conductorOneForm Δ).a = 1 := rfl

/-- The principal form of any `Δ` with `Δ ≡ 0` or `1 (mod 4)` has discriminant `Δ`. Every
discriminant of an integral form lies in one of those two classes, so this covers the
nonfundamental case used by the canonical representation in
`SICs.Quadratic.CanonicalRepresentation`; see `conductorOneForm`. -/
lemma disc_conductorOneForm_of_emod_four {Δ : ℤ} (h : Δ % 4 = 0 ∨ Δ % 4 = 1) :
    (conductorOneForm Δ).disc = Δ := by
  have hdvd : (4 : ℤ) ∣ Δ ^ 2 - Δ := by
    rcases h with h4 | h4
    · obtain ⟨k, hk⟩ : (4 : ℤ) ∣ Δ := Int.dvd_of_emod_eq_zero h4
      exact ⟨k * (Δ - 1), by rw [hk]; ring⟩
    · obtain ⟨k, hk⟩ : (4 : ℤ) ∣ Δ - 1 := ⟨Δ / 4, by omega⟩
      exact ⟨Δ * k, by rw [show Δ ^ 2 - Δ = Δ * (Δ - 1) by ring, hk]; ring⟩
  obtain ⟨k, hk⟩ := hdvd
  simp only [conductorOneForm, BinaryQF.disc, discrim]
  rw [hk, Int.mul_ediv_cancel_left _ (by norm_num)]
  linarith [hk]

/-- The principal form of a fundamental discriminant `Δ₀` has discriminant `Δ₀`; see
`conductorOneForm`. -/
lemma disc_conductorOneForm {Δ₀ : ℤ} (h : IsFundamentalDiscriminant Δ₀) :
    (conductorOneForm Δ₀).disc = Δ₀ :=
  disc_conductorOneForm_of_emod_four h.emod_four

/-- The principal form of a positive fundamental discriminant `Δ₀` has conductor `1`; see
`conductorOneForm`. -/
lemma isConductor_conductorOneForm {Δ₀ : ℤ} (h : IsFundamentalDiscriminant Δ₀) (hpos : 0 < Δ₀) :
    (conductorOneForm Δ₀).IsConductor Δ₀ 1 :=
  ⟨h, hpos, Nat.one_pos, by rw [disc_conductorOneForm h]; ring⟩

/-- The principal form of a positive nonsquare fundamental discriminant is admissible; see
`conductorOneForm`. -/
lemma isAdmissible_conductorOneForm {Δ₀ : ℤ} (h : IsFundamentalDiscriminant Δ₀) (hpos : 0 < Δ₀)
    (hnsq : ¬ IsSquare Δ₀) : (conductorOneForm Δ₀).IsAdmissible :=
  isAdmissible_of_disc (by simp [conductorOneForm, BinaryQF.IsPrimitive])
    (by rwa [disc_conductorOneForm h]) (by rwa [disc_conductorOneForm h])

/-- The positive root of the principal form of any `Δ ≡ 0` or `1 (mod 4)` is `(Δ + √Δ)/2`; see
`conductorOneForm`. -/
lemma rootPlus_conductorOneForm_of_emod_four {Δ : ℤ} (h : Δ % 4 = 0 ∨ Δ % 4 = 1) :
    (conductorOneForm Δ).rootPlus = ((Δ : ℝ) + Real.sqrt Δ) / 2 := by
  rw [BinaryQF.rootPlus, disc_conductorOneForm_of_emod_four h]
  simp only [conductorOneForm]
  push_cast
  ring

/-- The positive root of the principal form of `Δ₀` is `(Δ₀ + √Δ₀)/2`; see
`conductorOneForm`. -/
lemma rootPlus_conductorOneForm {Δ₀ : ℤ} (h : IsFundamentalDiscriminant Δ₀) :
    (conductorOneForm Δ₀).rootPlus = ((Δ₀ : ℝ) + Real.sqrt Δ₀) / 2 :=
  rootPlus_conductorOneForm_of_emod_four h.emod_four

end SIC

end
