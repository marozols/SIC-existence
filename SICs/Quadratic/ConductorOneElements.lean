/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.FieldTheory.ComplexGalois
import SICs.Quadratic.FundamentalForms
import SICs.Quadratic.RealFields
import Mathlib.NumberTheory.NumberField.Norm

/-!
# The conductor-one element of a real quadratic field

The element `α = (Δ_K + √Δ_K)/2` of a real quadratic field: its value at the selected real place,
the automorphisms switching `√Δ_K` that move it, and the element over the positive root of a form
of discriminant `f²Δ_K`.

For a real quadratic field `K` with discriminant `Δ_K`, this file exhibits an element
`α ∈ K` whose value at the selected real place is the positive root

`α = (Δ_K + √Δ_K)/2`

of the principal form `conductorOneForm Δ_K` of `SICs.Quadratic.FundamentalForms`. It is the
standard generator `𝒪_K = ℤ[(Δ_K + √Δ_K)/2]` of the maximal order,
[AFK25, Definition 1.47, `dfn:orderConductorf`] at conductor `f = 1`.

The selected real value identifies this element with `(conductorOneForm Δ_K).rootPlus`.
It also expresses the square root of the field discriminant as `2α - Δ_K`, used to construct
field elements over roots of forms and to detect automorphisms moving the field.

A further section serves every conductor: the positive root `ρ_{Q,+}` of a form of
discriminant `f²Δ_K` is the value at the selected place of the element `rootPlusElement Q f`
of `K`.

## Mathematical argument

Let `(1, ω)` be the integral basis of `SICs.Quadratic.Discriminants`, `t = Tr(ω)`, `n = N(ω)`,
so that `Δ_K = t² - 4n`. The two real values `ρ₁(ω)`, `ρ₂(ω)` are different: if they agreed, the
integral coordinates `x = a + bω` would make the two real embeddings agree on `𝒪_K`, hence on
its fraction field `K`, and two different infinite places of a totally real field have different
real embeddings. Being different, they are the two roots of `X² - tX + n`, so

`ρ₁(ω) + ρ₂(ω) = t`,  `(ρ₁(ω) - ρ₂(ω))² = t² - 4n = Δ_K`.

Since `Δ_K > 0`, with the sign `s = ±1` chosen so that `ρ₂(ω) < ρ₁(ω)` exactly when `s = 1`,

`ρ₁(ω) = (t + s√Δ_K)/2`,  `ρ₂(ω) = (t − s√Δ_K)/2`.

Set `α = sω + (Δ_K − st)/2`, an element of `K`; the shift is an integer because
`Δ_K − st ≡ t² − st ≡ t(t − 1) ≡ 0 (mod 2)`. Using `s² = 1`,

`ρ₁(α) = (Δ_K + √Δ_K)/2`,

so `ρ₁(α)` is `(conductorOneForm Δ_K).rootPlus`.

The same computation shows that an ambient automorphism `g` of `ℂ` over `ℚ` with
`g(√Δ_K) = −√Δ_K` moves `ρ₁(α)`, which is the hypothesis under which the modulus-one clause of
[AFK25, Theorem 2.20, `thm:field0`] is stated.

For a form `⟨A, B, C⟩` of discriminant `f²Δ_K`, `2α - Δ_K` has the value `√Δ_K` at the selected
place, so `(-B + f(2α - Δ_K))/(2A)` has the value `ρ_{Q,+} = (-B + f√Δ_K)/(2A)` there.

## References

- [AFK25, Definition 1.47, `dfn:orderConductorf`], the order of conductor `f`, here `f = 1`.
- [72, Kopp (2024), Lemma 4.42, `lem:fto1`], where such an `α` is the conductor-one target of
  the fractional linear transform lowering a quadratic number to conductor one.
- [22, Buell (1989), §6.2, pp. 90-92], for `𝒪_K = ℤ[(Δ_K + √Δ_K)/2]`.
-/

noncomputable section

namespace SIC

namespace RealQuadraticFieldData

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
  (F : RealQuadraticFieldData K)

/-! ### The oriented integral generator

The generator `ω` of the integral basis `(1, ω)` takes different values at the two real places,
and `Δ_K` is the square of the difference of those values. The sign `s` records which of the two
values is the larger one, so that `ρ₁(ω) = (t + s√Δ_K)/2` in both cases. -/

/-- The generator `ω` of the integral basis `(1, ω)` of `SICs.Quadratic.Discriminants`. -/
private noncomputable def gen : NumberField.RingOfIntegers K :=
  quadraticIntegralGenerator F.finrank_eq_two

/-- The trace `t = Tr_{K/ℚ}(ω)` of the integral generator. -/
private noncomputable def genTrace : ℤ :=
  Algebra.trace ℤ (NumberField.RingOfIntegers K) F.gen

/-- The sign `s = ±1`, equal to `1` exactly when the value of `ω` at the selected place is the
larger of its two real values. -/
private noncomputable def genSign : ℤ :=
  if realEmbeddingAt K F.otherPlace (F.gen : K) < realEmbeddingAt K F.place (F.gen : K)
    then 1 else -1

/-- **The two real values of the integral generator differ**: `ρ₂(ω) ≠ ρ₁(ω)`. If they agreed,
then by `exists_int_add_mul_quadraticIntegralGenerator` the two real embeddings
would agree on `𝒪_K`, hence on `K` because every element of `K` is a quotient of algebraic
integers (`IsFractionRing.div_surjective`), and `realEmbeddingAt_injective` would identify the
two places, contradicting `otherPlace_ne_place`. -/
private theorem realEmbeddingAt_otherPlace_gen_ne :
    realEmbeddingAt K F.otherPlace (F.gen : K) ≠ realEmbeddingAt K F.place (F.gen : K) := by
  intro hgen
  have h_integer : ∀ x : NumberField.RingOfIntegers K,
      realEmbeddingAt K F.otherPlace (x : K) = realEmbeddingAt K F.place (x : K) := by
    intro x
    obtain ⟨a, b, hx⟩ :=
      exists_int_add_mul_quadraticIntegralGenerator F.finrank_eq_two x
    change (x : K) = (a : K) + (b : K) * (F.gen : K) at hx
    rw [hx]
    simp only [map_add, map_mul, map_intCast, hgen]
  have h_embedding : realEmbeddingAt K F.otherPlace = realEmbeddingAt K F.place := by
    apply RingHom.ext
    intro y
    obtain ⟨x, z, hz, hxyz⟩ := IsFractionRing.div_surjective (NumberField.RingOfIntegers K) y
    rw [← hxyz, map_div₀, map_div₀, h_integer x, h_integer z]
  exact F.otherPlace_ne_place (realEmbeddingAt_injective h_embedding)

/-- `s² = 1`. -/
private theorem genSign_mul_self : F.genSign * F.genSign = 1 := by
  unfold genSign; split <;> norm_num

/-- **The field discriminant is the trace-norm discriminant of the integral generator, read in
`ℝ`**: `Δ_K = Tr(ω)² - 4N(ω)`. This is `quadratic_discr_eq_trace_sq_sub_four_norm` cast along
`Algebra.coe_trace_int` and `Algebra.coe_norm_int`. -/
private theorem discr_cast_eq :
    ((NumberField.discr K : ℤ) : ℝ) =
      ((Algebra.trace ℚ K (F.gen : K) : ℚ) : ℝ) ^ 2 -
        4 * ((Algebra.norm ℚ (F.gen : K) : ℚ) : ℝ) := by
  have h := congrArg (fun z : ℤ ↦ (z : ℚ))
    (quadratic_discr_eq_trace_sq_sub_four_norm F.finrank_eq_two)
  simp only [Int.cast_sub, Int.cast_pow, Int.cast_mul, Int.cast_ofNat] at h
  rw [Algebra.coe_trace_int, Algebra.coe_norm_int] at h
  exact_mod_cast h

/-- **The value of the integral generator at the selected place**:
`ρ₁(ω) = (t + s√Δ_K)/2`. From `sub_sq_realEmbeddingAt_eq` and `add_realEmbeddingAt_eq_trace`,
with `√Δ_K = |ρ₁(ω) - ρ₂(ω)|` and the sign resolved by the definition of `s`. -/
private theorem realEmbeddingAt_place_gen :
    realEmbeddingAt K F.place (F.gen : K) =
      ((F.genTrace : ℝ) + (F.genSign : ℝ) * Real.sqrt (NumberField.discr K)) / 2 := by
  have hne := F.realEmbeddingAt_otherPlace_gen_ne
  have hsum := F.add_realEmbeddingAt_otherPlace_eq_trace (F.gen : K)
  have hsq := F.sub_sq_realEmbeddingAt_otherPlace_eq (F.gen : K)
  rw [← F.discr_cast_eq] at hsq
  have htrace : (F.genTrace : ℝ) =
      ((Algebra.trace ℚ K (F.gen : K) : ℚ) : ℝ) := by
    exact_mod_cast Algebra.coe_trace_int F.gen
  have hsqrt : Real.sqrt (NumberField.discr K) =
      |realEmbeddingAt K F.place (F.gen : K) -
        realEmbeddingAt K F.otherPlace (F.gen : K)| := by
    rw [← hsq]
    exact Real.sqrt_sq_eq_abs _
  unfold genSign
  split
  · rename_i hlt
    simp only [Int.cast_one, one_mul]
    rw [hsqrt, abs_of_pos (sub_pos.mpr hlt)]
    linarith
  · rename_i hnot
    simp only [Int.cast_neg, Int.cast_one, neg_mul]
    have hlt : realEmbeddingAt K F.place (F.gen : K) <
        realEmbeddingAt K F.otherPlace (F.gen : K) :=
      lt_of_le_of_ne (le_of_not_gt hnot) hne.symm
    rw [hsqrt, abs_of_neg (sub_neg.mpr hlt)]
    linarith

/-- **The shift `(Δ_K - st)/2` is an integer**: `Δ_K - st ≡ t² - st = t(t - s) ≡ 0 (mod 2)`
because `s` is odd. -/
private theorem two_dvd_discr_sub_genSign_mul_genTrace :
    (2 : ℤ) ∣ NumberField.discr K - F.genSign * F.genTrace := by
  rw [quadratic_discr_eq_trace_sq_sub_four_norm F.finrank_eq_two]
  change 2 ∣ F.genTrace ^ 2 -
    4 * Algebra.norm ℤ F.gen - F.genSign * F.genTrace
  unfold genSign
  split
  · obtain ⟨k, hk⟩ := (Int.even_mul_pred_self F.genTrace).two_dvd
    exact ⟨k - 2 * Algebra.norm ℤ F.gen, by linear_combination hk⟩
  · obtain ⟨k, hk⟩ := (Int.even_mul_succ_self F.genTrace).two_dvd
    exact ⟨k - 2 * Algebra.norm ℤ F.gen, by linear_combination hk⟩

/-- Exact division by two commutes with the cast from `ℤ` to `ℝ`. -/
private theorem cast_ediv_two_of_two_dvd {a : ℤ} (h : (2 : ℤ) ∣ a) :
    ((a / 2 : ℤ) : ℝ) = (a : ℝ) / 2 := by
  obtain ⟨k, rfl⟩ := h
  norm_num

/-! ### The conductor-one element

`α = sω + (Δ_K - st)/2` is the standard generator of `𝒪_K`, normalized so that its value at the
selected place is the positive root of the principal form of `Δ_K`. -/

/-- **The conductor-one element `α = (Δ_K + √Δ_K)/2` of a real quadratic field**, written in the
integral basis as `sω + (Δ_K - s·Tr(ω))/2`. It generates the maximal order,
`𝒪_K = αℤ + ℤ`, and is the element denoted `α` in [72, Kopp (2024), Lemma 4.42, `lem:fto1`];
see [AFK25, Definition 1.47, `dfn:orderConductorf`] at conductor one. -/
def conductorOneElement : K :=
  (F.genSign : K) * (F.gen : K) +
    (((NumberField.discr K - F.genSign * F.genTrace) / 2 : ℤ) : K)

/-- **The conductor-one element has the positive root of the principal form as its value at the
selected place**: `ρ₁(α) = (Δ_K + √Δ_K)/2 = ρ_{conductorOneForm Δ_K,+}`. From
`realEmbeddingAt_place_gen`, `s² = 1` and `rootPlus_conductorOneForm`. -/
theorem realEmbeddingAt_place_conductorOneElement :
    realEmbeddingAt K F.place F.conductorOneElement =
      (conductorOneForm (NumberField.discr K)).rootPlus := by
  rw [rootPlus_conductorOneForm F.discr_fundamental]
  unfold conductorOneElement
  simp only [map_add, map_mul, map_intCast]
  rw [F.realEmbeddingAt_place_gen]
  have hshift := cast_ediv_two_of_two_dvd
    F.two_dvd_discr_sub_genSign_mul_genTrace
  push_cast at hshift
  rw [hshift]
  have hsign : (F.genSign : ℝ) * (F.genSign : ℝ) = 1 := by
    exact_mod_cast F.genSign_mul_self
  calc
    _ = (((NumberField.discr K : ℤ) : ℝ) +
        ((F.genSign : ℝ) * (F.genSign : ℝ)) *
          Real.sqrt (NumberField.discr K)) / 2 := by ring
    _ = _ := by rw [hsign, one_mul]

/-- **An automorphism switching `√Δ_K` moves the selected copy of `K`**: it moves `ρ₁(α)`.
This supplies the hypothesis `∃ x : K, g(ρ₁(x)) ≠ ρ₁(x)` of the modulus-one clause of
[AFK25, Theorem 2.20, `thm:field0`] from the switching condition in which the source states it.
From `realEmbeddingAt_place_conductorOneElement` and `√Δ_K > 0` (`discr_pos`). -/
theorem exists_map_realEmbeddingAt_ne_of_switchesSqrt {g : ComplexGaloisAutomorphism}
    (hg : SwitchesSqrt g (NumberField.discr K)) :
    ∃ x : K, g ((realEmbeddingAt K F.place x : ℝ) : ℂ) ≠
      ((realEmbeddingAt K F.place x : ℝ) : ℂ) := by
  refine ⟨F.conductorOneElement, ?_⟩
  rw [F.realEmbeddingAt_place_conductorOneElement,
    rootPlus_conductorOneForm F.discr_fundamental]
  push_cast
  change g ((Real.sqrt (NumberField.discr K) : ℝ) : ℂ) =
    -((Real.sqrt (NumberField.discr K) : ℝ) : ℂ) at hg
  rw [map_div₀, map_add, map_intCast, map_ofNat, hg]
  have hsqrt : ((Real.sqrt (NumberField.discr K) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast F.discr_pos)))
  intro heq
  apply hsqrt
  have hnum : (NumberField.discr K : ℂ) - Real.sqrt (NumberField.discr K) =
      (NumberField.discr K : ℂ) + Real.sqrt (NumberField.discr K) :=
    (div_left_inj' (by norm_num : (2 : ℂ) ≠ 0)).mp heq
  linear_combination -hnum / 2

/-! ### The element over the positive root of a form

A form `Q = ⟨A, B, C⟩` of discriminant `f²Δ_K` has positive root `(-B + f√Δ_K)/(2A)`, and
`2α - Δ_K` takes the value `√Δ_K` at the selected place, `α` the conductor-one element. So `ρ_{Q,+}`
is the value at the selected place of the element `(-B + f(2α - Δ_K))/(2A)` of `K`. This is how
[AFK25, Theorem 2.20, `thm:field0`], stated for a real `β` with `aβ² + bβ + c = 0`, is reached
from its statements for elements of `K`. Lean's `x/0 = 0` makes the value formula hold even for
`A = 0`, where both sides vanish. -/

/-- **The element over the positive root of a form**: `(-B + f(2α - Δ_K))/(2A)` for
`Q = ⟨A, B, C⟩` and `f ∈ ℕ`, where `α` is the conductor-one element. Its value at the selected
place is `ρ_{Q,+}` when `disc Q = f²Δ_K` (`realEmbeddingAt_place_rootPlusElement`). -/
def rootPlusElement (Q : BinaryQF) (f : ℕ) : K :=
  (-(Q.b : K) + (f : K) * (2 * F.conductorOneElement - (NumberField.discr K : K))) /
    (2 * (Q.a : K))

/-- The identity `√(f²Δ_K) = f√Δ_K` for a natural conductor `f`. -/
lemma sqrt_conductor_mul (F : RealQuadraticFieldData K) (f : ℕ) :
    Real.sqrt (((f : ℤ) ^ 2 * NumberField.discr K : ℤ) : ℝ) =
      (f : ℝ) * Real.sqrt (NumberField.discr K) := by
  push_cast
  rw [Real.sqrt_mul' _ (le_of_lt (by exact_mod_cast F.discr_pos)),
    Real.sqrt_sq (by positivity)]

/-- **The root element sits over `ρ_{Q,+}`**: for `disc Q = f²Δ_K`, the value of
`rootPlusElement Q f` at the selected place is `ρ_{Q,+} = (-B + √(f²Δ_K))/(2A)`. From
`realEmbeddingAt_place_conductorOneElement` and `√(f²Δ_K) = f√Δ_K`. -/
theorem realEmbeddingAt_place_rootPlusElement {Q : BinaryQF} {f : ℕ}
    (hQ : Q.disc = (f : ℤ) ^ 2 * NumberField.discr K) :
    realEmbeddingAt K F.place (F.rootPlusElement Q f) = Q.rootPlus := by
  unfold rootPlusElement BinaryQF.rootPlus
  simp only [map_div₀, map_add, map_sub, map_mul, map_neg, map_natCast, map_intCast,
    map_ofNat]
  rw [F.realEmbeddingAt_place_conductorOneElement, hQ, F.sqrt_conductor_mul f,
    rootPlus_conductorOneForm F.discr_fundamental]
  ring

end RealQuadraticFieldData

end SIC

end
