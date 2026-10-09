/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Fourier coefficients on finite abelian groups

The Fourier coefficients `ŵ(θ) = ∑_x w(x)θ(-x)` of a function on a finite abelian group: their
sum over the characters `χ` of a second group of the same order with `χ ∘ φ = θ`, the number of
these characters, their vanishing for functions invariant under a translation that `θ` moves,
Fourier inversion, invariance under isomorphisms, and the equality case of the triangle
inequality for averages.

This module supplies the character calculus of [RW26b, Radchenko, Wheeler (2026b), Section 5,
Lemma 2 and the proof of Theorem 5], stated for an arbitrary homomorphism `φ : G₁ → G₂` of finite
abelian groups of the same order; the pseudolattice instance is in
`SICs.Dilogarithm.Valuation.Distribution`. The normalization `1/√N` of the source is omitted.

## The argument

*Averaging.* The paper counts extensions of `θ` from `φ(G₁)` by restriction. Here character
orthogonality gives the count and the weighted sum together. The sum
`∑_x θ(x)χ(-φ(x))` is `|G₁|` if `χ ∘ φ = θ`, and zero otherwise. Sum this identity over `χ` and
apply orthogonality on `G₂`; when `|G₁| = |G₂|`, it gives
`∑_{χ ∘ φ = θ} χ(y) = ∑_{φ(x) = y} θ(x)`. At `y = 0`, if `θ` is trivial on `ker φ`, this counts
`|ker φ|` compatible characters. Summing coefficients and reindexing gives
`∑_χ ŵ₂(χ) = ∑_x w₂(φ(x))θ(-x)`. If `w₂(φ(x)) = ∑_{k ∈ ker φ} w₁(x + k)`, translation by each
`k` leaves `θ` unchanged, so this equals `|ker φ| ŵ₁(θ)`.

*Invariance.* If `w(x + u) = w(x)` for all `x` and `θ(u) ≠ 1`, the substitution `x ↦ x + u`
gives `ŵ(θ) = θ(u)ŵ(θ)`, so `ŵ(θ) = 0`.

*Inversion.* `∑_θ ŵ(θ)θ(y) = |G| w(y)` by orthogonality of characters.

*Equality in the triangle inequality.* If `∑_{i ∈ s} zᵢ = |s| A` with `|zᵢ| ≤ |A|`, then
`Re(zᵢĀ) ≤ |A|²` with sum `|s||A|²` forces `Re(zᵢĀ) = |A|²`, and
`|zᵢ - A|² = |zᵢ|² - 2 Re(zᵢĀ) + |A|² ≤ 0`.
-/

open Finset

namespace SIC

/-! ### Coordinate characters of a rank-two residue group

The standard character of `ZMod N` gives every character of `(ZMod N)²` by its two
coordinate coefficients. -/

/-- The character $v \mapsto e((c_0v_0+c_1v_1)/N)$ of $(\mathbb Z/N)^2$.
Used in the character constructions for [RW26b, Radchenko, Wheeler (2026b), Sections 5 and 7,
Lemmas 3 and 6]. -/
noncomputable def residueCoordinateChar (N : ℕ) [NeZero N] (c : Fin 2 → ZMod N) :
    AddChar (Fin 2 → ZMod N) ℂ where
  toFun v := ZMod.stdAddChar (c 0 * v 0 + c 1 * v 1)
  map_zero_eq_one' := by simp
  map_add_eq_mul' v w := by
    have he : c 0 * (v + w) 0 + c 1 * (v + w) 1 =
        (c 0 * v 0 + c 1 * v 1) + (c 0 * w 0 + c 1 * w 1) := by
      simp only [Pi.add_apply, mul_add]
      ring
    exact (congrArg ZMod.stdAddChar he).trans (ZMod.stdAddChar.map_add_eq_mul ..)

/-- Every character of $(\mathbb Z/N)^2$ has two coefficients in `ZMod N`.
Used in the character constructions for [RW26b, Radchenko, Wheeler (2026b), Sections 5 and 7,
Lemmas 3 and 6]. -/
theorem exists_residueCoordinateChar (N : ℕ) [NeZero N]
    (χ : AddChar (Fin 2 → ZMod N) ℂ) :
    ∃ c : Fin 2 → ZMod N, χ = residueCoordinateChar N c := by
  classical
  let u (i : Fin 2) : AddChar (ZMod N) ℂ :=
    χ.compAddMonoidHom (AddMonoidHom.single (fun _ : Fin 2 => ZMod N) i)
  let a : ZMod N := AddChar.zmodAddEquiv.symm (u 0)
  let b : ZMod N := AddChar.zmodAddEquiv.symm (u 1)
  let c : Fin 2 → ZMod N := ![a, b]
  refine ⟨c, AddChar.ext _ _ (fun v => ?_)⟩
  have hv : v = Pi.single 0 (v 0) + Pi.single 1 (v 1) := by
    funext i
    fin_cases i <;> simp
  have ha : χ (Pi.single 0 (v 0)) = ZMod.stdAddChar (a * v 0) := by
    change u 0 (v 0) = _
    rw [← AddEquiv.apply_symm_apply AddChar.zmodAddEquiv (u 0)]
    rfl
  have hb : χ (Pi.single 1 (v 1)) = ZMod.stdAddChar (b * v 1) := by
    change u 1 (v 1) = _
    rw [← AddEquiv.apply_symm_apply AddChar.zmodAddEquiv (u 1)]
    rfl
  calc
    χ v = χ (Pi.single 0 (v 0) + Pi.single 1 (v 1)) := by rw [← hv]
    _ = χ (Pi.single 0 (v 0)) * χ (Pi.single 1 (v 1)) := χ.map_add_eq_mul ..
    _ = residueCoordinateChar N c v := by
      rw [ha, hb]
      change ZMod.stdAddChar (a * v 0) * ZMod.stdAddChar (b * v 1) =
        ZMod.stdAddChar (c 0 * v 0 + c 1 * v 1)
      simp only [c, Matrix.cons_val_zero, Matrix.cons_val_one]
      exact (ZMod.stdAddChar.map_add_eq_mul ..).symm

/-- A character on a finite additive subgroup extends to the ambient finite group; this
is used for `exists_inducedChar_eq`. -/
theorem exists_extend_addChar {A : Type*} [AddCommGroup A] [Finite A]
    (H : AddSubgroup A) (θ : AddChar H ℂ) :
    ∃ χ : AddChar A ℂ, ∀ x : H, χ (x : A) = θ x := by
  classical
  let S : Subgroup (Multiplicative A) := H.toSubgroup
  let toH (y : S) : H :=
    ⟨y.1.toAdd, (Multiplicative.mem_toSubgroup H y.1).mp y.2⟩
  let θm : S →* ℂ := {
    toFun y := θ (toH y)
    map_one' := by change θ (0 : H) = 1; simp
    map_mul' a b := by
      have he : toH (a * b) = toH a + toH b := by apply Subtype.ext; rfl
      exact he ▸ θ.map_add_eq_mul (toH a) (toH b)
  }
  let θu : S →* ℂˣ := IsUnit.liftRight θm (fun y => θ.val_isUnit (toH y))
  obtain ⟨Φ, hΦ⟩ := MonoidHom.domRestrict_surjective ℂ S θu
  let χ : AddChar A ℂ :=
    AddChar.toMonoidHomEquiv.symm ((Units.coeHom ℂ).comp Φ)
  refine ⟨χ, ?_⟩
  intro x
  let y : S := ⟨Multiplicative.ofAdd (x : A),
    (Multiplicative.mem_toSubgroup H _).mpr x.2⟩
  have hval := congrArg (fun f : S →* ℂˣ => ((f y : ℂˣ) : ℂ)) hΦ
  change (Φ (Multiplicative.ofAdd (x : A)) : ℂ) = θ x at hval
  exact hval

/-- A character sum of a translated function is multiplied by the character of the shift.
Used in the cyclic-summand incidence identity. -/
theorem charSum_translate {G : Type*} [AddCommGroup G] [Fintype G]
    (w : G → ℂ) (u : G) (χ : AddChar G ℂ) :
    ∑ v : G, w (v - u) * χ v = χ u * ∑ v : G, w v * χ v := by
  classical
  calc
    ∑ v : G, w (v - u) * χ v = ∑ v : G, w v * χ (v + u) := by
      symm
      apply Fintype.sum_equiv (Equiv.addRight u)
      intro v
      simp
    _ = χ u * ∑ v : G, w v * χ v := by
      simp_rw [χ.map_add_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      ring

/-! ### Fourier coefficients

The coefficient, its vanishing under a translation, inversion, and transport. -/

section Coefficients

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- **The Fourier coefficient** `ŵ(θ) = ∑_x w(x)θ(-x)` of `w : G → ℂ` at a character `θ`, the
coefficient `ŵ_I(θ)` of [RW26b, Radchenko, Wheeler (2026b), Section 5] without the factor
`1/√N`. -/
noncomputable def charCoeff (w : G → ℂ) (θ : AddChar G ℂ) : ℂ :=
  ∑ x, w x * θ (-x)

/-- A coefficient vanishes when `w` is invariant under a translation `u` with `θ(u) ≠ 1`; the
last step of the proof of [RW26b, Radchenko, Wheeler (2026b), Section 5, Theorem 5]. -/
theorem charCoeff_eq_zero_of_add_eq {w : G → ℂ} {θ : AddChar G ℂ} {u : G}
    (hw : ∀ x, w (x + u) = w x) (hθ : θ u ≠ 1) : charCoeff w θ = 0 := by
  have hw' (x : G) : w (x - u) = w x := by
    simpa only [sub_add_cancel] using (hw (x - u)).symm
  have hθ' (x : G) : θ (-(x - u)) = θ u * θ (-x) := by
    rw [show -(x - u) = u + -x by abel, AddChar.map_add_eq_mul]
  have hsum : charCoeff w θ = θ u * charCoeff w θ := by
    calc
      charCoeff w θ = ∑ x, w (x - u) * θ (-(x - u)) := by
        simpa only [charCoeff] using
          (Fintype.sum_equiv (Equiv.addRight u)
            (fun x : G => w x * θ (-x))
            (fun x : G => w (x - u) * θ (-(x - u)))
            (by intro x; simp))
      _ = θ u * charCoeff w θ := by
        simp_rw [hw', hθ']
        simp only [charCoeff, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
  exact (mul_eq_zero.mp (by calc
    (θ u - 1) * charCoeff w θ = θ u * charCoeff w θ - charCoeff w θ := by ring
    _ = 0 := by rw [← hsum, sub_self])).resolve_left
    (sub_ne_zero.mpr hθ)

/-- **Fourier inversion**: a function whose coefficients all vanish is zero; the last step of the
proof of [RW26b, Radchenko, Wheeler (2026b), Section 5, Theorem 5]. -/
theorem eq_zero_of_forall_charCoeff_eq_zero {w : G → ℂ}
    (h : ∀ θ : AddChar G ℂ, charCoeff w θ = 0) : w = 0 := by
  classical
  funext y
  have hsum : ∑ θ : AddChar G ℂ, charCoeff w θ * θ y = 0 := by
    simp [h]
  have hsum' : ∑ θ : AddChar G ℂ, charCoeff w θ * θ y =
      (Fintype.card G : ℂ) * w y := by
    calc
      _ = ∑ x : G, w x * ∑ θ : AddChar G ℂ, θ (y - x) := by
        simp only [charCoeff, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro θ _
        calc
          w x * θ (-x) * θ y = w x * (θ (-x) * θ y) := by ring
          _ = w x * θ (y - x) := by rw [← AddChar.map_add_eq_mul, add_comm, sub_eq_add_neg]
      _ = (Fintype.card G : ℂ) * w y := by
        simp_rw [AddChar.sum_apply_eq_ite]
        simp only [sub_eq_zero]
        simp [mul_comm]
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact (mul_eq_zero.mp (hsum'.symm.trans hsum)).resolve_left hcard

/-- Coefficients are invariant under transport along an isomorphism `e : G ≃+ G'`. -/
theorem charCoeff_comp_addEquiv {G' : Type*} [AddCommGroup G'] [Fintype G'] (e : G ≃+ G')
    (w : G' → ℂ) (θ : AddChar G' ℂ) :
    charCoeff (w ∘ e) (θ.compAddMonoidHom e.toAddMonoidHom) = charCoeff w θ := by
  unfold charCoeff
  refine Fintype.sum_equiv e.toEquiv _ _ ?_
  intro x
  simp

end Coefficients

/-! ### Averages over compatible characters

The abstract form of [RW26b, Radchenko, Wheeler (2026b), Section 5, Lemma 2]. -/

section Averages

variable {G₁ G₂ : Type*} [AddCommGroup G₁] [Fintype G₁] [AddCommGroup G₂]
  [Fintype G₂] [DecidableEq G₂]

/-- The character sum over extensions of `θ` equals the sum of `θ` over the fibre of `φ`.
Used in `card_filter_compAddMonoidHom_eq` and `sum_charCoeff_compAddMonoidHom`. -/
private theorem sum_compatible_char (hcard : Fintype.card G₁ = Fintype.card G₂)
    (φ : G₁ →+ G₂) (θ : AddChar G₁ ℂ) (y : G₂) :
    ∑ χ ∈ univ.filter (fun χ : AddChar G₂ ℂ => χ.compAddMonoidHom φ = θ), χ y =
      ∑ x ∈ univ.filter (fun x => φ x = y), θ x := by
  classical
  have horth (χ : AddChar G₂ ℂ) :
      (∑ x : G₁, θ x * χ (-(φ x))) =
        if χ.compAddMonoidHom φ = θ then (Fintype.card G₁ : ℂ) else 0 := by
    simpa only [AddChar.sub_apply, AddChar.compAddMonoidHom_apply,
      map_neg, sub_eq_zero, eq_comm] using
      (AddChar.sum_eq_ite (θ - χ.compAddMonoidHom φ))
  have hn : (Fintype.card G₁ : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  apply mul_left_cancel₀ hn
  calc
    (Fintype.card G₁ : ℂ) *
        ∑ χ ∈ univ.filter (fun χ : AddChar G₂ ℂ => χ.compAddMonoidHom φ = θ), χ y =
      ∑ χ : AddChar G₂ ℂ,
        (if χ.compAddMonoidHom φ = θ then (Fintype.card G₁ : ℂ) else 0) * χ y := by
        simp [Finset.sum_filter, Finset.mul_sum]
    _ = ∑ χ : AddChar G₂ ℂ, (∑ x : G₁, θ x * χ (-(φ x))) * χ y := by
      apply Finset.sum_congr rfl
      intro χ _
      rw [horth]
    _ = ∑ x : G₁, θ x * ∑ χ : AddChar G₂ ℂ, χ (y - φ x) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro χ _
      calc
        θ x * χ (-(φ x)) * χ y = θ x * (χ (-(φ x)) * χ y) := by ring
        _ = θ x * χ (y - φ x) := by rw [← AddChar.map_add_eq_mul, add_comm, sub_eq_add_neg]
    _ = (Fintype.card G₁ : ℂ) *
        ∑ x ∈ univ.filter (fun x => φ x = y), θ x := by
      simp_rw [AddChar.sum_apply_eq_ite]
      rw [← hcard]
      simp only [sub_eq_zero, Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : φ x = y
      · simp [hx, mul_comm]
      · have hyx : y ≠ φ x := Ne.symm hx
        simp [hx, hyx]

open scoped Classical in
/-- **The number of compatible characters**: if `|G₁| = |G₂|` and `θ` is trivial on `ker φ`,
exactly `|ker φ|` characters `χ` of `G₂` satisfy `χ ∘ φ = θ`, as in the proof of
[RW26b, Radchenko, Wheeler (2026b), Section 5, Lemma 2]. -/
theorem card_filter_compAddMonoidHom_eq (hcard : Fintype.card G₁ = Fintype.card G₂)
    (φ : G₁ →+ G₂) {θ : AddChar G₁ ℂ} (hθ : ∀ k, φ k = 0 → θ k = 1) :
    (univ.filter fun χ : AddChar G₂ ℂ => χ.compAddMonoidHom φ = θ).card =
      (univ.filter fun k => φ k = 0).card := by
  classical
  have hs := sum_compatible_char hcard φ θ 0
  have hleft : (∑ χ ∈ univ.filter (fun χ : AddChar G₂ ℂ =>
      χ.compAddMonoidHom φ = θ), χ 0) =
        ((univ.filter fun χ : AddChar G₂ ℂ => χ.compAddMonoidHom φ = θ).card : ℂ) := by
    simp
  have hright : (∑ x ∈ univ.filter (fun x => φ x = 0), θ x) =
      ((univ.filter fun x => φ x = 0).card : ℂ) := by
    calc
      _ = ∑ x ∈ univ.filter (fun x => φ x = 0), (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hθ x (Finset.mem_filter.mp hx).2
      _ = _ := by simp
  have hs' := hleft.symm.trans (hs.trans hright)
  exact Nat.cast_injective hs'

omit [DecidableEq G₂] in
/-- Compatible coefficients of `w₂` sum to its coefficient pulled back along `φ`.
Used in `sum_charCoeff_compAddMonoidHom`. -/
private theorem sum_compatible_charCoeff (hcard : Fintype.card G₁ = Fintype.card G₂)
    (φ : G₁ →+ G₂) (w₂ : G₂ → ℂ) (θ : AddChar G₁ ℂ) :
    ∑ χ ∈ univ.filter (fun χ : AddChar G₂ ℂ => χ.compAddMonoidHom φ = θ), charCoeff w₂ χ =
      ∑ x : G₁, w₂ (φ x) * θ (-x) := by
  classical
  calc
    _ = ∑ y : G₂, w₂ y *
        ∑ χ ∈ univ.filter (fun χ : AddChar G₂ ℂ => χ.compAddMonoidHom φ = θ), χ (-y) := by
          simp only [charCoeff, Finset.mul_sum]
          rw [Finset.sum_comm]
    _ = ∑ y : G₂, w₂ y *
        ∑ x ∈ univ.filter (fun x : G₁ => φ x = -y), θ x := by
          apply Finset.sum_congr rfl
          intro y _
          rw [sum_compatible_char hcard φ θ (-y)]
    _ = ∑ x : G₁, w₂ (-(φ x)) * θ x := by
      simp only [Finset.mul_sum, Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      have hpred (y : G₂) : (φ x = -y) ↔ (y = -φ x) := by
        rw [eq_comm (a := φ x) (b := -y), neg_eq_iff_eq_neg]
      simp_rw [hpred]
      simp
    _ = ∑ x : G₁, w₂ (φ x) * θ (-x) := by
      apply Fintype.sum_equiv (Equiv.neg G₁)
      intro x
      simp

open scoped Classical in
/-- **[RW26b, Radchenko, Wheeler (2026b), Section 5, Lemma 2], abstract form**: if
`|G₁| = |G₂|`, `w₂(φ(x)) = ∑_{k ∈ ker φ} w₁(x + k)` and `θ` is trivial on `ker φ`, then the
coefficients of `w₂` at the characters `χ` with `χ ∘ φ = θ` sum to `|ker φ| ŵ₁(θ)`. -/
theorem sum_charCoeff_compAddMonoidHom (hcard : Fintype.card G₁ = Fintype.card G₂)
    (φ : G₁ →+ G₂) {w₁ : G₁ → ℂ} {w₂ : G₂ → ℂ}
    (hw : ∀ x, w₂ (φ x) = ∑ k ∈ univ.filter (fun k => φ k = 0), w₁ (x + k))
    {θ : AddChar G₁ ℂ} (hθ : ∀ k, φ k = 0 → θ k = 1) :
    ∑ χ ∈ univ.filter (fun χ : AddChar G₂ ℂ => χ.compAddMonoidHom φ = θ), charCoeff w₂ χ =
      (univ.filter fun k => φ k = 0).card * charCoeff w₁ θ := by
  classical
  let K := univ.filter (fun k : G₁ => φ k = 0)
  have hinner (k : G₁) (hk : k ∈ K) :
      (∑ x : G₁, w₁ (x + k) * θ (-x)) = charCoeff w₁ θ := by
    have hθk : θ (-k) = 1 := by
      rw [AddChar.map_neg_eq_inv, hθ k (Finset.mem_filter.mp hk).2, inv_one]
    calc
      _ = ∑ x : G₁, w₁ (x + k) * θ (-(x + k)) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [show -(x + k) = -x + -k by abel, AddChar.map_add_eq_mul, hθk, mul_one]
      _ = charCoeff w₁ θ := by
        simpa only [charCoeff] using
          (Fintype.sum_equiv (Equiv.addRight k)
            (fun x : G₁ => w₁ (x + k) * θ (-(x + k)))
            (fun x : G₁ => w₁ x * θ (-x)) (by intro x; rfl))
  calc
    ∑ χ ∈ univ.filter (fun χ : AddChar G₂ ℂ => χ.compAddMonoidHom φ = θ), charCoeff w₂ χ =
      ∑ x : G₁, w₂ (φ x) * θ (-x) := sum_compatible_charCoeff hcard φ w₂ θ
    _ = ∑ x : G₁, (∑ k ∈ K, w₁ (x + k)) * θ (-x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [hw]
    _ = ∑ k ∈ K, ∑ x : G₁, w₁ (x + k) * θ (-x) := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = K.card * charCoeff w₁ θ := by
      calc
        _ = ∑ k ∈ K, charCoeff w₁ θ := by
          apply Finset.sum_congr rfl
          intro k hk
          exact hinner k hk
        _ = _ := by simp

end Averages

/-! ### Equality in the triangle inequality

An average of complex numbers bounded by `|A|` that equals `A` has all terms equal to `A`. -/

/-- If `∑_{i ∈ s} zᵢ = |s| A` and `‖zᵢ‖ ≤ ‖A‖` for all `i ∈ s`, then every `zᵢ = A`; the
equality step of the maximum argument in the proof of [RW26b, Radchenko, Wheeler (2026b),
Section 5, Theorem 5]. -/
theorem eq_of_sum_eq_card_mul {ι : Type*} {s : Finset ι} {z : ι → ℂ} {A : ℂ}
    (hz : ∀ i ∈ s, ‖z i‖ ≤ ‖A‖) (hsum : ∑ i ∈ s, z i = s.card * A) : ∀ i ∈ s, z i = A := by
  classical
  have hle (i : ι) (hi : i ∈ s) : (z i * (starRingEnd ℂ) A).re ≤ ‖A‖ ^ 2 := by
    calc
      (z i * (starRingEnd ℂ) A).re ≤ ‖z i * (starRingEnd ℂ) A‖ := Complex.re_le_norm _
      _ = ‖z i‖ * ‖A‖ := by rw [norm_mul, Complex.norm_conj]
      _ ≤ ‖A‖ * ‖A‖ := mul_le_mul_of_nonneg_right (hz i hi) (norm_nonneg _)
      _ = ‖A‖ ^ 2 := by ring
  have heq : ∑ i ∈ s, (z i * (starRingEnd ℂ) A).re = ∑ _i ∈ s, ‖A‖ ^ 2 := by
    rw [← Complex.re_sum, ← Finset.sum_mul, hsum]
    simp [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      -Complex.ofReal_pow]
  have hterm := (Finset.sum_eq_sum_iff_of_le hle).mp heq
  intro i hi
  have hsq : ‖z i‖ ^ 2 ≤ ‖A‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hz i hi) 2
  have hzero : Complex.normSq (z i - A) ≤ 0 := by
    rw [Complex.normSq_sub, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    nlinarith [hterm i hi]
  exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp (le_antisymm hzero (Complex.normSq_nonneg _)))

end SIC
