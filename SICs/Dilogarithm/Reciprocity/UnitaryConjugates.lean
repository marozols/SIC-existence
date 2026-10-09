/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Dilogarithm.Pseudolattice.UnitCircle
import SICs.Dilogarithm.Reciprocity.SignClass

/-!
# Unitary conjugates of the finite quantum dilogarithm

Every automorphism `τ` of `ℂ` inducing the nontrivial automorphism of `K` sends each value
`E_{I,ε}(x)` at a nonzero class `x ∈ G_{I,ε}` to the unit circle.

This module formalizes [RW26b, Radchenko, Wheeler (2026b), Section 9.2, Proposition 7]. The
source applies the full Artin law of Theorem 9 at the second real sign class. Here only three
inputs are used: the squared values lie in the narrow ray class field `H`
(`pseudolatticeDilog_sq_mem_rayField`), the class `s₁s₂` acts by `x ↦ -x` on them
(`pseudolatticeDilog_artin_signClass`), and the Artin symbol of each real sign class `s_w` is
trivial or complex conjugation at a place above `w` (`globalArtin_signIdeleClass_eq_one_or_isConj`).
Lemma 7 (`pseudolatticeDilog_exists_norm_ne_one`) excludes the degenerate cases when
`|G_{I,ε}| ≥ 25`; a general period is reduced to `ε⁴` by the power law (8)
(`pseudolatticeDilog_pow_period`), instead of the source's two consecutive powers in Theorem 9.

## The argument

*Notation.* Write `E = E_{I,ε}` and `z_x = (E(x)/E(0))²`, so `E(0)² = ε`. By (7) and reflection
(4), `conj E(x) = ⟨x⟩E(x)` and `E(x)E(-x) = ⟨x⟩⁻¹` with `|⟨x⟩| = 1` for `x ∉ I`
(`pseudolatticeDilog_conj`, `pseudolatticeDilog_mul_neg`). In particular,
`conj E(-x) = E(x)⁻¹` and `conj z_{-x} = (E(x)E(0))⁻² = ε⁻²z_x⁻¹`.

*The automorphisms.* Choose a modulus `M` (`IsPeriod.exists_modulus_mul_mem`), the narrow ray
class field `H` (`exists_narrowRayClassField`), and `ψ : H → ℂ` extending the real embedding of
`K` at the first place. Every `z_x` is `ψ(a_x)` (`pseudolatticeDilog_sq_mem_rayField`). Let
`P`, `Q` be the Artin symbols of the sign classes negative only at the first, resp. second, real
place, and `A = PQ` that of the class negative at both; `A a_x = a_{-x}`. Since `τ` moves `K`,
`τψ` lies over the second place. So `P = 1` or `ψ ∘ P = conj ∘ ψ`, and `Q = 1` or
`τψ ∘ Q = conj ∘ τψ`, i.e. `ψ ∘ Q = g ∘ ψ` for `g = τ⁻¹ ∘ conj ∘ τ`.

*Excluding `Q = 1`.* Then `A = P`. If `P = 1`, `z_{-x} = z_x`; if `ψ ∘ P = conj ∘ ψ`,
`z_{-x} = conj z_x`. Either identity makes the norms of `z_x` and `z_{-x}` equal. Reflection
then gives `|E(x)| = 1` for every `x ∉ I`, contradicting Lemma 7.

*Conclusion.* The action `PQ(a_x) = a_{-x}` makes `conj(τ z_x)` equal to `τ z_{-x}` if `P = 1`,
and to `τ(conj z_{-x})` otherwise. The first equality gives equal norms of the mapped squared
values, so reflection gives `|τ E(x)| = 1`. In the second, the identity for `conj z_{-x}` gives
`(|τ E(x)|/|τ E(0)|)² = (|τ E(x)| |τ E(0)|)⁻²`, hence `|τ E(x)|⁴ = 1`.

*Arbitrary periods.* The trace identity gives `|G_{I,ε⁴}| = Tr(ε⁴) - 2 ≥ 45`: first
`ε + ε⁻¹ ≥ 3`, then `ε² + ε⁻² ≥ 7`, then `ε⁴ + ε⁻⁴ ≥ 47`. By the power law (8),
`E_{ε⁴}(x) = E_ε(x)⁴`; unit norm of its image therefore gives `|τ E_ε(x)| = 1`.
-/

noncomputable section

open IsDedekindDomain NumberField

namespace SIC

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
variable {F : RealQuadraticFieldData K} {B : PseudolatticeBasis F} {ε : K}

/-! ### Identities for the squared normalized values -/

/-- The squared normalized value `z_x`; used by `pseudolatticeDilog_norm_map_eq_one`. -/
private def dilogSq (h : B.IsPeriod ε) (x : K) : ℂ :=
  (pseudolatticeDilog h x / pseudolatticeDilog h 0) ^ 2

/-- The conjugate of the value at `-x` is the inverse value at `x`; used by
`dilogSq_conj_neg`. -/
private theorem dilog_conj_neg (h : B.IsPeriod ε) {x : K}
    (hx : (ε - 1) * x ∈ B.submodule) (hx0 : x ∉ B.submodule) :
    starRingEnd ℂ (pseudolatticeDilog h (-x)) = (pseudolatticeDilog h x)⁻¹ := by
  have hxneg : (ε - 1) * (-x) ∈ B.submodule := by
    simpa only [mul_neg] using B.submodule.neg_mem hx
  have hA : h.matrix ∈ gammaSubgroup (B.characteristic x) :=
    (h.mem_gammaSubgroup_characteristic_iff x).mpr hx
  have hgauss : pseudolatticeGaussian h (-x) = pseudolatticeGaussian h x := by
    simp only [pseudolatticeGaussian, B.characteristic_neg, thetaCharacter_neg h.matrix hA]
  have hG : pseudolatticeGaussian h x ≠ 0 := thetaCharacter_ne_zero _ _
  have hE : pseudolatticeDilog h x ≠ 0 := pseudolatticeDilog_ne_zero h hx
  have hrefl := pseudolatticeDilog_mul_neg h hx hx0
  rw [pseudolatticeDilog_conj h hxneg, hgauss]
  field_simp [hG] at hrefl
  field_simp [hE]
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hrefl

/-- The reflection and conjugation laws give `conj z_{-x} = (E(x)E(0))⁻²`; used by
`norm_map_eq_one_of_conj_sq_neg`. -/
private theorem dilogSq_conj_neg (h : B.IsPeriod ε) {x : K}
    (hx : (ε - 1) * x ∈ B.submodule) (hx0 : x ∉ B.submodule) :
    starRingEnd ℂ (dilogSq h (-x)) =
      (pseudolatticeDilog h x * pseudolatticeDilog h 0)⁻¹ ^ 2 := by
  rw [dilogSq, map_pow, map_div₀, dilog_conj_neg h hx hx0]
  rw [pseudolatticeDilog_of_mem h B.submodule.zero_mem]
  simp only [Complex.conj_ofReal, div_eq_mul_inv, mul_inv_rev]
  ring

/-- The norm of the squared normalized value after an automorphism; used by
`norm_map_eq_one_of_equal_sq_norm` and `norm_map_eq_one_of_conj_sq_neg`. -/
private theorem norm_map_dilogSq (h : B.IsPeriod ε) (τ : ComplexGaloisAutomorphism)
    (x : K) :
    ‖τ (dilogSq h x)‖ =
      (‖τ (pseudolatticeDilog h x)‖ / ‖τ (pseudolatticeDilog h 0)‖) ^ 2 := by
  simp only [dilogSq, map_pow, map_div₀, norm_pow, norm_div]

/-- The mapped values at `x` and `-x` have norms with product one; used by
`norm_map_eq_one_of_equal_sq_norm`. -/
private theorem norm_map_dilog_mul_neg (h : B.IsPeriod ε)
    (τ : ComplexGaloisAutomorphism) {x : K}
    (hx : (ε - 1) * x ∈ B.submodule) (hx0 : x ∉ B.submodule) :
    ‖τ (pseudolatticeDilog h x)‖ * ‖τ (pseudolatticeDilog h (-x))‖ = 1 := by
  have hG : ‖τ (pseudolatticeGaussian h x)‖ = 1 :=
    norm_map_thetaCharacter τ (B.characteristic x) h.matrix
  have hrefl := congrArg (fun z : ℂ => ‖τ z‖) (pseudolatticeDilog_mul_neg h hx hx0)
  simpa only [map_mul, map_inv₀, norm_mul, norm_inv, hG, inv_one] using hrefl

/-- Equal norms of the mapped squared values at `x` and `-x` force the mapped value at `x`
onto the unit circle; used by `pseudolatticeDilog_norm_map_eq_one`. -/
private theorem norm_map_eq_one_of_equal_sq_norm (h : B.IsPeriod ε)
    (τ : ComplexGaloisAutomorphism) {x : K}
    (hx : (ε - 1) * x ∈ B.submodule) (hx0 : x ∉ B.submodule)
    (hz : ‖τ (dilogSq h x)‖ = ‖τ (dilogSq h (-x))‖) :
    ‖τ (pseudolatticeDilog h x)‖ = 1 := by
  have hzero : ‖τ (pseudolatticeDilog h 0)‖ ≠ 0 := by
    exact norm_ne_zero_iff.mpr
      ((map_ne_zero τ).mpr (pseudolatticeDilog_ne_zero h (by simp)))
  have heq : ‖τ (pseudolatticeDilog h x)‖ =
      ‖τ (pseudolatticeDilog h (-x))‖ := by
    rw [norm_map_dilogSq, norm_map_dilogSq] at hz
    have hdiv := (sq_eq_sq₀
      (div_nonneg (norm_nonneg _) (norm_nonneg _))
      (div_nonneg (norm_nonneg _) (norm_nonneg _))).mp hz
    exact (div_left_inj' hzero).mp hdiv
  have hprod := norm_map_dilog_mul_neg h τ hx hx0
  rw [← heq] at hprod
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa [pow_two] using hprod)

/-- If conjugation after `τ` agrees on `z_x` with the image under `τ` of `conj z_{-x}`,
then `τ(E(x))` lies on the unit circle; used by `pseudolatticeDilog_norm_map_eq_one`. -/
private theorem norm_map_eq_one_of_conj_sq_neg (h : B.IsPeriod ε)
    (τ : ComplexGaloisAutomorphism) {x : K}
    (hx : (ε - 1) * x ∈ B.submodule) (hx0 : x ∉ B.submodule)
    (hz : starRingEnd ℂ (τ (dilogSq h x)) =
      τ (starRingEnd ℂ (dilogSq h (-x)))) :
    ‖τ (pseudolatticeDilog h x)‖ = 1 := by
  let a := ‖τ (pseudolatticeDilog h x)‖
  let b := ‖τ (pseudolatticeDilog h 0)‖
  have ha : a ≠ 0 := norm_ne_zero_iff.mpr
    ((map_ne_zero τ).mpr (pseudolatticeDilog_ne_zero h hx))
  have hb : b ≠ 0 := norm_ne_zero_iff.mpr
    ((map_ne_zero τ).mpr (pseudolatticeDilog_ne_zero h (by simp)))
  have heq : (a / b) ^ 2 = (a * b)⁻¹ ^ 2 := by
    have hn : ‖τ (dilogSq h x)‖ =
        ‖τ ((pseudolatticeDilog h x * pseudolatticeDilog h 0)⁻¹ ^ 2)‖ := by
      calc
        _ = ‖starRingEnd ℂ (τ (dilogSq h x))‖ := (Complex.norm_conj _).symm
        _ = _ := by rw [hz, dilogSq_conj_neg h hx hx0]
    simpa only [norm_map_dilogSq, map_pow, map_inv₀, map_mul, norm_pow, norm_inv,
      norm_mul, a, b] using hn
  have ha4 : a ^ 4 = 1 := by
    field_simp [ha, hb] at heq
    nlinarith [heq]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : (4 : ℕ) ≠ 0)).mp ha4

/-! ### The two real sign classes -/

/-- Either degenerate action of the negative sign class forces `|E(x)| = 1`; used by
`second_sign_ne_one`. -/
private theorem norm_eq_one_of_degenerate_sq (h : B.IsPeriod ε) {x : K}
    (hx : (ε - 1) * x ∈ B.submodule) (hx0 : x ∉ B.submodule)
    (hz : dilogSq h (-x) = dilogSq h x ∨
      dilogSq h (-x) = starRingEnd ℂ (dilogSq h x)) :
    ‖pseudolatticeDilog h x‖ = 1 := by
  have hn : ‖(1 : ComplexGaloisAutomorphism) (dilogSq h x)‖ =
      ‖(1 : ComplexGaloisAutomorphism) (dilogSq h (-x))‖ := by
    rcases hz with hz | hz
    · simp only [AlgEquiv.one_apply, hz]
    · simp only [AlgEquiv.one_apply, hz, Complex.norm_conj]
  simpa only [AlgEquiv.one_apply] using
    norm_map_eq_one_of_equal_sq_norm h 1 hx hx0 hn

/-- The sign negative only at the selected real place; used by
`pseudolatticeDilog_norm_map_eq_one`. -/
private noncomputable def firstSign (F : RealQuadraticFieldData K) :
    InfinitePlace K → ℤˣ := by
  classical exact fun w => if w = F.place then -1 else 1

/-- The sign negative only at the other real place; used by
`pseudolatticeDilog_norm_map_eq_one`. -/
private noncomputable def secondSign (F : RealQuadraticFieldData K) :
    InfinitePlace K → ℤˣ := by
  classical exact fun w => if w = F.otherPlace then -1 else 1

/-- The two one-place signs multiply to the totally negative sign; used by
`signArtin_mul`. -/
private theorem signs_mul (F : RealQuadraticFieldData K) :
    firstSign F * secondSign F = fun _ => -1 := by
  classical
  funext w
  rcases F.eq_place_or_eq_otherPlace w with rfl | rfl
  · simp [firstSign, secondSign, Ne.symm F.otherPlace_ne_place]
  · simp [firstSign, secondSign, F.otherPlace_ne_place]

/-- The Artin symbol of the totally negative sign is the product of the two one-place
symbols; used by `second_sign_ne_one` and `norm_map_eq_one_large_order`. -/
private theorem signArtin_mul {H : Type*} [Field H] [NumberField H]
    [Algebra K H] [IsAbelianGalois K H] (F : RealQuadraticFieldData K) :
    globalArtin H (signIdeleClass (K := K) fun _ => -1) =
      globalArtin H (signIdeleClass (firstSign F)) *
        globalArtin H (signIdeleClass (secondSign F)) := by
  rw [← signs_mul F, signIdeleClass_mul, map_mul]

/-! ### The Artin actions on the squared values -/

/-- Lemma 7 excludes a trivial Artin symbol at the second real place; used by
`norm_map_eq_one_large_order`. -/
private theorem second_sign_ne_one (h : B.IsPeriod ε)
    (hN : 25 ≤ finiteDilogOrder h.matrix) {M : ℕ} (hM0 : 0 < M)
    (hM : ∀ a : 𝓞 K, ∀ x : K, (ε - 1) * x ∈ B.submodule →
      (M : K) * (a : K) * x ∈ B.submodule)
    {H : Type*} [Field H] [NumberField H] [Algebra K H] [IsAbelianGalois K H]
    (hU : (IdeleClassGroup.norm (K := K) (L := H)).range =
      IdeleClassGroup.raySubgroup Set.univ (Ideal.span {(M : 𝓞 K)}))
    (ψ : H →+* ℂ)
    (hP : globalArtin H (signIdeleClass (firstSign F)) = 1 ∨
      ComplexEmbedding.IsConj ψ (globalArtin H (signIdeleClass (firstSign F)))) :
    globalArtin H (signIdeleClass (secondSign F)) ≠ 1 := by
  intro hQ
  obtain ⟨x, hx, hx0, hne⟩ := pseudolatticeDilog_exists_norm_ne_one h hN
  obtain ⟨a, ha⟩ := RingHom.mem_fieldRange.mp
    (pseudolatticeDilog_sq_mem_rayField h hM0 hM hU ψ hx)
  have hxneg : (ε - 1) * (-x) ∈ B.submodule := by
    simpa only [mul_neg] using B.submodule.neg_mem hx
  obtain ⟨b, hb⟩ := RingHom.mem_fieldRange.mp
    (pseudolatticeDilog_sq_mem_rayField h hM0 hM hU ψ hxneg)
  have hAB := pseudolatticeDilog_artin_signClass h hM0 hM hU ψ hx ha hb
  rw [signArtin_mul F, hQ, mul_one] at hAB
  have hz : dilogSq h (-x) = dilogSq h x ∨
      dilogSq h (-x) = starRingEnd ℂ (dilogSq h x) := by
    rcases hP with hP | hP
    · left
      calc
        dilogSq h (-x) = ψ b := hb.symm
        _ = ψ (globalArtin H (signIdeleClass (firstSign F)) a) := congrArg ψ hAB.symm
        _ = ψ a := by rw [hP]; rfl
        _ = dilogSq h x := ha
    · right
      calc
        dilogSq h (-x) = ψ b := hb.symm
        _ = ψ (globalArtin H (signIdeleClass (firstSign F)) a) := congrArg ψ hAB.symm
        _ = starRingEnd ℂ (dilogSq h x) := by
          simp only [hP.eq, ha, dilogSq, starRingEnd_apply]
  exact hne (norm_eq_one_of_degenerate_sq h hx hx0 hz)

/-- The Artin symbols at the two real places act as the identity or conjugation at `ψ`,
respectively as conjugation at `τψ`; used by `norm_map_eq_one_large_order`. -/
private theorem sign_artin_actions (h : B.IsPeriod ε)
    (hN : 25 ≤ finiteDilogOrder h.matrix) {M : ℕ} (hM0 : 0 < M)
    (hM : ∀ a : 𝓞 K, ∀ x : K, (ε - 1) * x ∈ B.submodule → (M : K) * (a : K) * x ∈ B.submodule)
    {H : Type*} [Field H] [NumberField H] [Algebra K H] [IsAbelianGalois K H]
    (hU : (IdeleClassGroup.norm (K := K) (L := H)).range = IdeleClassGroup.raySubgroup
      Set.univ (Ideal.span {(M : 𝓞 K)})) (ψ : H →+* ℂ)
    (hψ : ∀ a : K, ψ (algebraMap K H a) = (realEmbeddingAt K F.place a : ℂ))
    (τ : ComplexGaloisAutomorphism)
    (hτ : ∃ a : K, τ (realEmbeddingAt K F.place a : ℂ) ≠ (realEmbeddingAt K F.place a : ℂ)) :
    (globalArtin H (signIdeleClass (firstSign F)) = 1 ∨
      ComplexEmbedding.IsConj ψ (globalArtin H (signIdeleClass (firstSign F)))) ∧
      ComplexEmbedding.IsConj (τ.toRingEquiv.toRingHom.comp ψ)
        (globalArtin H (signIdeleClass (secondSign F))) := by
  let _ : (InfinitePlace.mk ψ).LiesOver F.place :=
    liesOver_realEmbeddingAt ψ F.place hψ
  have hs₁ : ∀ w : InfinitePlace K, w ≠ F.place → firstSign F w = 1 := by
    intro w hw
    simp [firstSign, hw]
  have hP := globalArtin_signIdeleClass_eq_one_or_isConj hs₁ ψ
  have hQne := second_sign_ne_one h hN hM0 hM hU ψ hP
  let ψτ : H →+* ℂ := τ.toRingEquiv.toRingHom.comp ψ
  let _ : (InfinitePlace.mk ψτ).LiesOver F.otherPlace :=
    mapped_liesOver_otherPlace F τ hτ ψ hψ
  have hs₂ : ∀ w : InfinitePlace K, w ≠ F.otherPlace → secondSign F w = 1 := by
    intro w hw
    simp [secondSign, hw]
  have hQ := (globalArtin_signIdeleClass_eq_one_or_isConj hs₂ ψτ).resolve_left hQne
  exact ⟨hP, hQ⟩

omit [NumberField K] [NumberField.IsTotallyReal K] in
/-- The action `PQ(a) = b`, with `P` trivial or conjugation at `ψ` and `Q` conjugation at
`τψ`, makes `conj(τψ(a))` equal to `τψ(b)` or `τ(conj ψ(b))`; used by
`norm_map_eq_one_large_order`. -/
private theorem sign_action_conj_dichotomy
    {H : Type*} [Field H] [Algebra K H]
    (ψ : H →+* ℂ) (τ : ComplexGaloisAutomorphism) (P Q : H ≃ₐ[K] H)
    (hP : P = 1 ∨ ComplexEmbedding.IsConj ψ P)
    (hQ : ComplexEmbedding.IsConj (τ.toRingEquiv.toRingHom.comp ψ) Q)
    {a b : H} (hAB : (P * Q) a = b) :
    starRingEnd ℂ (τ (ψ a)) = τ (ψ b) ∨
      starRingEnd ℂ (τ (ψ a)) = τ (starRingEnd ℂ (ψ b)) := by
  have hQeq : starRingEnd ℂ (τ (ψ a)) = τ (ψ (Q a)) := by
    have hq := (hQ.eq a).symm
    change star (τ (ψ a)) = τ (ψ (Q a)) at hq
    simpa only [starRingEnd_apply] using hq
  rcases hP with hP | hP
  · left
    have hQa : Q a = b := by simpa only [hP, one_mul] using hAB
    rw [hQeq, hQa]
  · right
    have hψb : ψ b = starRingEnd ℂ (ψ (Q a)) := by
      rw [← hAB, AlgEquiv.mul_apply]
      exact hP.eq (Q a)
    rw [hQeq]
    congr 1
    rw [hψb]
    simp

/-! ### From the Artin actions to unit norm -/

/-- The two possible Artin actions on `z_x` both put `τ(E(x))` on the unit circle; used by
`norm_map_eq_one_large_order`. -/
private theorem norm_map_eq_one_of_artin_action (h : B.IsPeriod ε)
    (τ : ComplexGaloisAutomorphism) {x : K}
    (hx : (ε - 1) * x ∈ B.submodule) (hx0 : x ∉ B.submodule)
    {H : Type*} [Field H] [Algebra K H] (ψ : H →+* ℂ)
    (P Q : H ≃ₐ[K] H)
    (hP : P = 1 ∨ ComplexEmbedding.IsConj ψ P)
    (hQ : ComplexEmbedding.IsConj (τ.toRingEquiv.toRingHom.comp ψ) Q)
    {a b : H} (ha : ψ a = dilogSq h x) (hb : ψ b = dilogSq h (-x))
    (hAB : (P * Q) a = b) : ‖τ (pseudolatticeDilog h x)‖ = 1 := by
  have hcase := sign_action_conj_dichotomy ψ τ P Q hP hQ hAB
  rw [ha, hb] at hcase
  rcases hcase with hcase | hcase
  · have hn : ‖τ (dilogSq h x)‖ = ‖τ (dilogSq h (-x))‖ := by
      calc
        _ = ‖starRingEnd ℂ (τ (dilogSq h x))‖ := (Complex.norm_conj _).symm
        _ = _ := by rw [hcase]
    exact norm_map_eq_one_of_equal_sq_norm h τ hx hx0 hn
  · exact norm_map_eq_one_of_conj_sq_neg h τ hx hx0 hcase

/-! ### The large-order case and passage to an arbitrary period -/

/-- Proposition 7 when the finite dilogarithm group has at least twenty-five elements; used
by `pseudolatticeDilog_norm_map_eq_one`. -/
private theorem norm_map_eq_one_large_order (h : B.IsPeriod ε)
    (hN : 25 ≤ finiteDilogOrder h.matrix) (τ : ComplexGaloisAutomorphism)
    (hτ : ∃ a : K, τ (realEmbeddingAt K F.place a : ℂ) ≠
      (realEmbeddingAt K F.place a : ℂ))
    {x : K} (hx : (ε - 1) * x ∈ B.submodule) (hx0 : x ∉ B.submodule) :
    ‖τ (pseudolatticeDilog h x)‖ = 1 := by
  obtain ⟨M, hM0, hM⟩ := h.exists_modulus_mul_mem
  have hm : Ideal.span {(M : 𝓞 K)} ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.mpr hM0.ne'
  obtain ⟨H, hNF, hAb, hU⟩ := exists_narrowRayClassField F hm
  let _ : NumberField H := hNF
  let _ : IsAbelianGalois K H := hAb
  let ρ := Complex.ofRealHom.comp (realEmbeddingAt K F.place)
  let ψ : H →+* ℂ := ComplexEmbedding.lift H ρ
  have hψ (a : K) : ψ (algebraMap K H a) =
      (realEmbeddingAt K F.place a : ℂ) :=
    ComplexEmbedding.lift_algebraMap_apply H ρ a
  obtain ⟨hP, hQ⟩ := sign_artin_actions h hN hM0 hM hU ψ hψ τ hτ
  obtain ⟨a, ha⟩ := RingHom.mem_fieldRange.mp
    (pseudolatticeDilog_sq_mem_rayField h hM0 hM hU ψ hx)
  have hxneg : (ε - 1) * (-x) ∈ B.submodule := by
    simpa only [mul_neg] using B.submodule.neg_mem hx
  obtain ⟨b, hb⟩ := RingHom.mem_fieldRange.mp
    (pseudolatticeDilog_sq_mem_rayField h hM0 hM hU ψ hxneg)
  have hAB := pseudolatticeDilog_artin_signClass h hM0 hM hU ψ hx ha hb
  rw [signArtin_mul F] at hAB
  change ψ a = dilogSq h x at ha
  change ψ b = dilogSq h (-x) at hb
  exact norm_map_eq_one_of_artin_action h τ hx hx0 ψ _ _ hP hQ ha hb hAB

/-- The fourth power of a period has finite dilogarithm order at least forty-five; used by
`pseudolatticeDilog_norm_map_eq_one`. -/
private theorem finiteDilogOrder_fourth_power_ge (h : B.IsPeriod ε) :
    45 ≤ finiteDilogOrder (h.pow (by decide : 0 < 4)).matrix := by
  let e := realEmbeddingAt K F.place ε
  let h4 : B.IsPeriod (ε ^ 4) := h.pow (by decide)
  have hN : (1 : ℝ) ≤ finiteDilogOrder h.matrix := by
    exact_mod_cast finiteDilogOrder_pos h.isAttractiveFixedPoint
  have htrace : (finiteDilogOrder h.matrix : ℝ) = e + e⁻¹ - 2 := by
    simpa only [h.fltDenominator_matrix, e] using
      cast_finiteDilogOrder_eq h.isAttractiveFixedPoint
  have ht : 3 ≤ e + e⁻¹ := by linarith
  have he : e ≠ 0 := ne_of_gt (zero_lt_one.trans h.one_lt)
  have ht2 : (e + e⁻¹) ^ 2 = e ^ 2 + e⁻¹ ^ 2 + 2 := by field_simp [he]; ring
  have hs : 7 ≤ e ^ 2 + e⁻¹ ^ 2 := by nlinarith
  have hs2 : (e ^ 2 + e⁻¹ ^ 2) ^ 2 = e ^ 4 + (e ^ 4)⁻¹ + 2 := by
    field_simp [he]
    ring
  have h4trace : (finiteDilogOrder h4.matrix : ℝ) = e ^ 4 + (e ^ 4)⁻¹ - 2 := by
    simpa only [h4.fltDenominator_matrix, map_pow, e] using
      cast_finiteDilogOrder_eq h4.isAttractiveFixedPoint
  have hbound : (45 : ℝ) ≤ finiteDilogOrder h4.matrix := by nlinarith
  exact_mod_cast hbound

/-- **[RW26b, Radchenko, Wheeler (2026b), Section 9.2, Proposition 7]**: every automorphism `τ`
of `ℂ` inducing the nontrivial automorphism of `K` (here: moving the image of `K` under the real
embedding at the first place) satisfies `|τ(E_{I,ε}(x))| = 1` for every representative `x` of a
nonzero class in `G_{I,ε}`. The source states it for automorphisms of `ℚ̄`; every such
automorphism extends to one of `ℂ`, so the statement here implies the source form. -/
@[source "RW26b, Proposition 7, p. 17"]
theorem pseudolatticeDilog_norm_map_eq_one (h : B.IsPeriod ε) (τ : ComplexGaloisAutomorphism)
    (hτ : ∃ a : K, τ (realEmbeddingAt K F.place a : ℂ) ≠ (realEmbeddingAt K F.place a : ℂ))
    {x : K} (hx : (ε - 1) * x ∈ B.submodule) (hx0 : x ∉ B.submodule) :
    ‖τ (pseudolatticeDilog h x)‖ = 1 := by
  let h4 : B.IsPeriod (ε ^ 4) := h.pow (by decide)
  have hN4 : 25 ≤ finiteDilogOrder h4.matrix :=
    (by decide : 25 ≤ 45).trans (finiteDilogOrder_fourth_power_ge h)
  have hx4 : (ε ^ 4 - 1) * x ∈ B.submodule := h.pow_sub_one_mul_mem hx 4
  have hn := norm_map_eq_one_large_order h4 hN4 τ hτ hx4 hx0
  rw [pseudolatticeDilog_pow_period h (by decide : 0 < 4) hx, map_pow] at hn
  exact norm_eq_one_of_norm_pow_eq_one (by decide : (4 : ℕ) ≠ 0) hn

end SIC

end
