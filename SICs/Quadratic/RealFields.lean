/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Quadratic.Discriminants
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Trace.Basic

/-!
# Oriented real quadratic fields

Real quadratic fields, their two real embeddings, trace conjugation, and the trace and norm
formulas.

The field data underlying [AFK25, §1.3] consist of a degree-two totally real number field and a
selected infinite place. Its discriminant is fundamental by
`SICs.Quadratic.Discriminants`; total reality makes it positive and leaves exactly two real
places. Their signed embeddings distinguish the two conjugates of each field element.

## Mathematical argument

A complex embedding of a totally real field is the complexification of the real embedding at
its infinite place. Since a quadratic field has exactly two such places, the sum and product of
all complex embeddings are the sum and product of the two real values. Mathlib's formulas for
field trace and norm therefore give `Tr(β) = ρ₁(β) + ρ₂(β)` and `N(β) = ρ₁(β)ρ₂(β)` for every
`β`, including rational elements. Cayley--Hamilton gives the matching quadratic relation
`β² = Tr(β)β - N(β)`. Trace conjugation interchanges the two real values, so it preserves the
norm and total positivity.

## References

- [AFK25, §1.3]: the real quadratic field underlying the conductor and dimension towers.
- Mathlib's `trace_eq_sum_embeddings`, `Algebra.norm_eq_prod_embeddings`, and
  `Algebra.aeval_self_charpoly_lmul`.
-/

noncomputable section

namespace SIC

open NumberField NumberField.InfinitePlace

/-! ### Real embeddings

A real infinite place supplies a signed embedding into `ℝ`, whose absolute value is the place.
Total reality identifies every complex embedding with this real embedding at its place. -/

/-- The real embedding belonging to a chosen infinite place of a totally real number field. -/
noncomputable def realEmbeddingAt (K : Type*) [Field K] [_numberFieldK : NumberField K]
    [NumberField.IsTotallyReal K] (w : InfinitePlace K) : K →+* ℝ :=
  embedding_of_isReal (NumberField.IsTotallyReal.isReal w)

/-- A nonzero algebraic integer has nonzero image under every real embedding; used by
`RayCongruent.refl`. -/
lemma realEmbeddingAt_coe_ne_zero {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] {a : NumberField.RingOfIntegers K} (ha : a ≠ 0)
    (w : InfinitePlace K) : realEmbeddingAt K w (a : K) ≠ 0 :=
  (map_ne_zero (realEmbeddingAt K w)).mpr
    (RingOfIntegers.coe_eq_zero_iff.not.mpr ha)

/-- **An element with two different real values is irrational at both**: if `ρ_v(x) ≠ ρ_w(x)`
then `ρ_v(x)` is irrational, since `ρ_v(x) = q ∈ ℚ` forces `x = q` (`ρ_v` is injective and
fixes `ℚ`) and then `ρ_w(x) = q` as well. -/
lemma irrational_realEmbeddingAt_of_ne {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] {v w : InfinitePlace K} {x : K}
    (h : realEmbeddingAt K v x ≠ realEmbeddingAt K w x) :
    Irrational (realEmbeddingAt K v x) := by
  rintro ⟨q, hq⟩
  apply h
  have hx : x = (q : K) := (realEmbeddingAt K v).injective (by simpa using hq.symm)
  rw [hx, map_ratCast, map_ratCast]

/-- **Distinct places have distinct real embeddings**: `realEmbeddingAt K` is injective, since
`w = mk (embedding w)` (`NumberField.InfinitePlace.mk_embedding`) and the complex embedding is
the real one composed with `ℝ → ℂ` (`NumberField.InfinitePlace.embedding_of_isReal_apply`). -/
lemma realEmbeddingAt_injective {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] : Function.Injective (realEmbeddingAt K) := by
  intro v w h
  calc
    v = InfinitePlace.mk v.embedding := (InfinitePlace.mk_embedding v).symm
    _ = InfinitePlace.mk w.embedding := by
      congr 1
      apply RingHom.ext
      intro x
      calc
        v.embedding x = ((realEmbeddingAt K v x : ℝ) : ℂ) :=
          (embedding_of_isReal_apply (NumberField.IsTotallyReal.isReal v) x).symm
        _ = ((realEmbeddingAt K w x : ℝ) : ℂ) :=
          congrArg Complex.ofReal (RingHom.congr_fun h x)
        _ = w.embedding x :=
          embedding_of_isReal_apply (NumberField.IsTotallyReal.isReal w) x
    _ = w := InfinitePlace.mk_embedding w

/-- **A complex embedding defining a real place is that place's real embedding**: if
`InfinitePlace.mk φ = w`, then `φ(x) = ρ_w(x)` for every `x`. By
`NumberField.InfinitePlace.mk_eq_iff` at `w = mk (embedding w)`, `φ` is `embedding w` or its
complex conjugate, and the two agree because `w` is real
(`NumberField.InfinitePlace.embedding_of_isReal_apply`). -/
lemma apply_eq_realEmbeddingAt_of_mk_eq {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] {φ : K →+* ℂ} {w : InfinitePlace K}
    (h : InfinitePlace.mk φ = w) (x : K) : φ x = (realEmbeddingAt K w x : ℂ) := by
  have hmk : InfinitePlace.mk φ = InfinitePlace.mk w.embedding :=
    h.trans (InfinitePlace.mk_embedding w).symm
  have heq : φ = w.embedding := by
    rcases InfinitePlace.mk_eq_iff.mp hmk with hφ | hφ
    · exact hφ
    · calc
        φ = ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) :=
          (ComplexEmbedding.involutive_conjugate K φ).symm
        _ = ComplexEmbedding.conjugate w.embedding := congrArg _ hφ
        _ = w.embedding := ComplexEmbedding.isReal_iff.mp
          (InfinitePlace.isReal_iff.mp (NumberField.IsTotallyReal.isReal w))
  calc
    φ x = w.embedding x := RingHom.congr_fun heq x
    _ = (realEmbeddingAt K w x : ℂ) :=
      (InfinitePlace.embedding_of_isReal_apply
        (NumberField.IsTotallyReal.isReal w) x).symm

/-- The complexified real embedding defines its original infinite place. -/
theorem mk_realEmbeddingAt {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (w : InfinitePlace K) :
    InfinitePlace.mk (Complex.ofRealHom.comp (realEmbeddingAt K w)) = w := by
  calc
    _ = InfinitePlace.mk w.embedding := by
      congr 1
      apply RingHom.ext
      intro x
      exact InfinitePlace.embedding_of_isReal_apply
        (NumberField.IsTotallyReal.isReal w) x
    _ = w := InfinitePlace.mk_embedding w

/-- Exact real-quadratic field data preceding the choice of the distinguished unit in [AFK25].

The fundamental discriminant is a consequence of degree two (`discr_fundamental`), rather than
additional data. -/
structure RealQuadraticFieldData (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] where
  /-- The extension `K/ℚ` has degree two. -/
  finrank_eq_two : Module.finrank ℚ K = 2
  /-- The real place that orients inequalities and the fundamental unit. -/
  place : InfinitePlace K

/-! ### The quadratic relation of an element of a quadratic field

Cayley--Hamilton for the degree-two algebra `K/ℚ`, and its image under a real embedding. -/

variable {K : Type*} [Field K] [NumberField K]

/-- **An element of a quadratic field satisfies its trace-and-norm polynomial**:
`β² = Tr(β)β - N(β)`. This is `DegreeTwoAlgebra.sq_eq_trace_mul_sub_norm_of_basis` at the
basis `DegreeTwoAlgebra.basisFinTwo ℚ K hfin`, with `algebraMap ℚ K q = (q : K)`
(`eq_ratCast`). -/
theorem sq_eq_trace_mul_sub_norm (hfin : Module.finrank ℚ K = 2) (β : K) :
    β ^ 2 = (Algebra.trace ℚ K β : K) * β - (Algebra.norm ℚ β : K) := by
  simpa only [eq_ratCast] using
    DegreeTwoAlgebra.sq_eq_trace_mul_sub_norm_of_basis ℚ K
      (DegreeTwoAlgebra.basisFinTwo ℚ K hfin) β

/-- **The real values of `β` are roots of `X² - Tr(β)X + N(β)`**: applying a ring homomorphism
`f : K →+* ℝ` to `sq_eq_trace_mul_sub_norm` (`map_ratCast`). -/
theorem map_sq_eq_trace_mul_sub_norm (hfin : Module.finrank ℚ K = 2) (f : K →+* ℝ) (β : K) :
    f β ^ 2 = (Algebra.trace ℚ K β : ℝ) * f β - (Algebra.norm ℚ β : ℝ) := by
  have h := congrArg f (sq_eq_trace_mul_sub_norm hfin β)
  simpa only [map_pow, map_mul, map_sub, map_ratCast] using h

namespace RealQuadraticFieldData

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]

/-! ### The discriminant and the two real places

Degree two gives a fundamental discriminant, and total reality makes it positive. The two real
places determine all complex embeddings of the field. -/

/-- The discriminant of a quadratic number field is fundamental, by
`isFundamentalDiscriminant_numberField_discr`. -/
lemma discr_fundamental (F : RealQuadraticFieldData K) :
    IsFundamentalDiscriminant (NumberField.discr K) :=
  isFundamentalDiscriminant_numberField_discr F.finrank_eq_two

/-- The discriminant of the totally real number field underlying the tower data is positive. -/
lemma discr_pos (_F : RealQuadraticFieldData K) : 0 < NumberField.discr K := by
  have hsign := NumberField.sign_discr K
  rw [NumberField.IsTotallyReal.nrComplexPlaces_eq_zero] at hsign
  norm_num at hsign
  exact hsign

/-- A real quadratic field has exactly two infinite places. -/
lemma card_infinitePlace_eq_two (F : RealQuadraticFieldData K) :
    Fintype.card (InfinitePlace K) = 2 := by
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    NumberField.IsTotallyReal.nrComplexPlaces_eq_zero]
  rw [← NumberField.IsTotallyReal.finrank K, F.finrank_eq_two]

/-- A real quadratic field has a real place other than the selected one. -/
lemma exists_ne_place (F : RealQuadraticFieldData K) : ∃ w : InfinitePlace K, w ≠ F.place := by
  have h : 1 < Fintype.card (InfinitePlace K) := by rw [F.card_infinitePlace_eq_two]; omega
  exact Fintype.exists_ne_of_one_lt_card h F.place

/-- **The other real place**, `∞₂` in the notation of [AFK25, Conjecture 2.7, `conj:stark`] when
`F.place` is `∞₁`: a choice of the place other than `F.place`, unique by
`eq_place_or_eq`. -/
noncomputable def otherPlace (F : RealQuadraticFieldData K) : InfinitePlace K :=
  Classical.choose F.exists_ne_place

/-- The other place differs from the selected one. -/
lemma otherPlace_ne_place (F : RealQuadraticFieldData K) : F.otherPlace ≠ F.place :=
  Classical.choose_spec F.exists_ne_place

/-- **A real quadratic field has no third place**: every infinite place is `F.place` or a given
`w₂ ≠ F.place`, since there are exactly two (`card_infinitePlace_eq_two`). -/
lemma eq_place_or_eq (F : RealQuadraticFieldData K) {w₂ : InfinitePlace K} (hw₂ : w₂ ≠ F.place)
    (w : InfinitePlace K) : w = F.place ∨ w = w₂ := by
  classical
  by_cases hw : w = F.place
  · exact Or.inl hw
  · right
    by_contra hw'
    have hcard : ({F.place, w₂, w} : Finset (InfinitePlace K)).card = 3 := by
      rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_pair (Ne.symm hw')]
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        exact not_or_intro (Ne.symm hw₂) (Ne.symm hw)
    have hle := Finset.card_le_univ ({F.place, w₂, w} : Finset (InfinitePlace K))
    rw [hcard, F.card_infinitePlace_eq_two] at hle
    omega

/-- Every infinite place is `F.place` or `F.otherPlace`; `eq_place_or_eq` at `otherPlace`. -/
lemma eq_place_or_eq_otherPlace (F : RealQuadraticFieldData K) (w : InfinitePlace K) :
    w = F.place ∨ w = F.otherPlace :=
  F.eq_place_or_eq F.otherPlace_ne_place w

/-- **An embedding `K → ℂ` other than the selected real one is the other real embedding**: if
`φ(z) ≠ ρ₁(z)` for some `z`, then `φ = ρ₂`, with `ρ₁` at `F.place` and `ρ₂` at `F.otherPlace`.
The place `InfinitePlace.mk φ` is `F.place` or `F.otherPlace` (`eq_place_or_eq_otherPlace`), and
`φ` is the real embedding of that place (`apply_eq_realEmbeddingAt_of_mk_eq`); the first case
contradicts the hypothesis. -/
lemma apply_eq_realEmbeddingAt_otherPlace (F : RealQuadraticFieldData K) {φ : K →+* ℂ}
    (hφ : ∃ z : K, φ z ≠ (realEmbeddingAt K F.place z : ℂ)) (x : K) :
    φ x = (realEmbeddingAt K F.otherPlace x : ℂ) := by
  rcases F.eq_place_or_eq_otherPlace (InfinitePlace.mk φ) with hplace | hother
  · obtain ⟨z, hz⟩ := hφ
    exact (hz (apply_eq_realEmbeddingAt_of_mk_eq hplace z)).elim
  · exact apply_eq_realEmbeddingAt_of_mk_eq hother x

/-! ### Trace and norm at the two real places

Complexifying the two real embeddings enumerates all embeddings into `ℂ`. Mathlib's sum and
product formulas give trace and norm without any irrationality hypothesis on the element. -/

/-- The complexification used to enumerate embeddings in `univ_complexEmbeddings`. -/
private def complexEmbeddingAt (w : InfinitePlace K) : K →ₐ[ℚ] ℂ :=
  (Complex.ofRealHom.comp (realEmbeddingAt K w)).toRatAlgHom

/-- Distinct places give distinct complexifications, for `univ_complexEmbeddings`. -/
private lemma complexEmbeddingAt_ne {v w : InfinitePlace K} (h : v ≠ w) :
    complexEmbeddingAt v ≠ complexEmbeddingAt w := by
  intro heq
  apply h
  apply realEmbeddingAt_injective
  ext x
  apply Complex.ofReal_injective
  exact DFunLike.congr_fun heq x

/-- The two complexified real embeddings exhaust the embeddings used in the trace and norm
formulas. -/
private lemma univ_complexEmbeddings [DecidableEq (K →ₐ[ℚ] ℂ)]
    (F : RealQuadraticFieldData K) {w₂ : InfinitePlace K}
    (hw₂ : w₂ ≠ F.place) :
    (Finset.univ : Finset (K →ₐ[ℚ] ℂ)) =
      {complexEmbeddingAt F.place, complexEmbeddingAt w₂} := by
  classical
  symm
  apply Finset.eq_univ_iff_forall.mpr
  intro σ
  rcases F.eq_place_or_eq hw₂ (InfinitePlace.mk σ.toRingHom) with h | h
  · have heq : σ = complexEmbeddingAt F.place := by
      ext x
      exact apply_eq_realEmbeddingAt_of_mk_eq h x
    simp [heq]
  · have heq : σ = complexEmbeddingAt w₂ := by
      ext x
      exact apply_eq_realEmbeddingAt_of_mk_eq h x
    simp [heq]

/-- **The two real values add to the trace and multiply to the norm**:
`ρ₁(β) + ρ₂(β) = Tr_{K/ℚ}(β)` and `ρ₁(β)ρ₂(β) = N_{K/ℚ}(β)` for distinct real places.
These are Mathlib's `trace_eq_sum_embeddings` and `Algebra.norm_eq_prod_embeddings` at the
field's two embeddings, including when `β` is rational. -/
theorem add_eq_and_mul_eq_realEmbeddingAt (F : RealQuadraticFieldData K)
    {w₂ : InfinitePlace K} (hw₂ : w₂ ≠ F.place) {β : K} :
    realEmbeddingAt K F.place β + realEmbeddingAt K w₂ β =
        ((Algebra.trace ℚ K β : ℚ) : ℝ) ∧
      realEmbeddingAt K F.place β * realEmbeddingAt K w₂ β =
        ((Algebra.norm ℚ β : ℚ) : ℝ) := by
  classical
  have hne := complexEmbeddingAt_ne hw₂.symm
  constructor
  · apply Complex.ofReal_injective
    have h := trace_eq_sum_embeddings (K := ℚ) (L := K) ℂ (x := β)
    rw [F.univ_complexEmbeddings hw₂, Finset.sum_pair hne] at h
    simpa only [complexEmbeddingAt, RingHom.toRatAlgHom_apply, RingHom.comp_apply,
      Complex.ofRealHom_eq_coe, Complex.ofReal_add, Complex.ofReal_ratCast,
      eq_ratCast] using h.symm
  · apply Complex.ofReal_injective
    have h := Algebra.norm_eq_prod_embeddings ℚ ℂ β
    rw [F.univ_complexEmbeddings hw₂, Finset.prod_pair hne] at h
    simpa only [complexEmbeddingAt, RingHom.toRatAlgHom_apply, RingHom.comp_apply,
      Complex.ofRealHom_eq_coe, Complex.ofReal_mul, Complex.ofReal_ratCast,
      eq_ratCast] using h.symm

/-- The two real values add to the trace; see `add_eq_and_mul_eq_realEmbeddingAt`. -/
theorem add_realEmbeddingAt_eq_trace (F : RealQuadraticFieldData K)
    {w₂ : InfinitePlace K} (hw₂ : w₂ ≠ F.place) {β : K} :
    realEmbeddingAt K F.place β + realEmbeddingAt K w₂ β =
      ((Algebra.trace ℚ K β : ℚ) : ℝ) :=
  (F.add_eq_and_mul_eq_realEmbeddingAt hw₂).1

/-- The two real values multiply to the norm; see `add_eq_and_mul_eq_realEmbeddingAt`. -/
theorem mul_realEmbeddingAt_eq_norm (F : RealQuadraticFieldData K)
    {w₂ : InfinitePlace K} (hw₂ : w₂ ≠ F.place) {β : K} :
    realEmbeddingAt K F.place β * realEmbeddingAt K w₂ β =
      ((Algebra.norm ℚ β : ℚ) : ℝ) :=
  (F.add_eq_and_mul_eq_realEmbeddingAt hw₂).2

/-- The squared difference is the trace-norm discriminant:
`(ρ₁(β) - ρ₂(β))² = Tr(β)² - 4N(β)`, by `add_eq_and_mul_eq_realEmbeddingAt`. -/
theorem sub_sq_realEmbeddingAt_eq (F : RealQuadraticFieldData K)
    {w₂ : InfinitePlace K} (hw₂ : w₂ ≠ F.place) {β : K} :
    (realEmbeddingAt K F.place β - realEmbeddingAt K w₂ β) ^ 2 =
      ((Algebra.trace ℚ K β : ℚ) : ℝ) ^ 2 - 4 * ((Algebra.norm ℚ β : ℚ) : ℝ) := by
  rw [← F.add_realEmbeddingAt_eq_trace hw₂, ← F.mul_realEmbeddingAt_eq_norm hw₂]
  ring

/-- The selected and other real values add to the trace, for every element. -/
theorem add_realEmbeddingAt_otherPlace_eq_trace (F : RealQuadraticFieldData K) (β : K) :
    realEmbeddingAt K F.place β + realEmbeddingAt K F.otherPlace β =
      ((Algebra.trace ℚ K β : ℚ) : ℝ) :=
  F.add_realEmbeddingAt_eq_trace F.otherPlace_ne_place

/-- The selected and other real values multiply to the norm, for every element. -/
theorem mul_realEmbeddingAt_otherPlace_eq_norm (F : RealQuadraticFieldData K) (β : K) :
    realEmbeddingAt K F.place β * realEmbeddingAt K F.otherPlace β =
      ((Algebra.norm ℚ β : ℚ) : ℝ) :=
  F.mul_realEmbeddingAt_eq_norm F.otherPlace_ne_place

/-- Trace conjugation swaps the values at the two real embeddings. -/
theorem trace_sub_realEmbeddings (F : RealQuadraticFieldData K) (α : K) :
    realEmbeddingAt K F.place ((Algebra.trace ℚ K α : K) - α) =
        realEmbeddingAt K F.otherPlace α ∧
      realEmbeddingAt K F.otherPlace ((Algebra.trace ℚ K α : K) - α) =
        realEmbeddingAt K F.place α := by
  have h := F.add_realEmbeddingAt_otherPlace_eq_trace α
  constructor <;> simp only [map_sub, map_ratCast] <;> linarith

/-- The squared difference at the selected and other place is the trace-norm discriminant. -/
theorem sub_sq_realEmbeddingAt_otherPlace_eq (F : RealQuadraticFieldData K) (β : K) :
    (realEmbeddingAt K F.place β - realEmbeddingAt K F.otherPlace β) ^ 2 =
      ((Algebra.trace ℚ K β : ℚ) : ℝ) ^ 2 - 4 * ((Algebra.norm ℚ β : ℚ) : ℝ) :=
  F.sub_sq_realEmbeddingAt_eq F.otherPlace_ne_place

/-! ### Total positivity

An element is totally positive when its images at both real places are positive. -/

/-- `c > 0` at both real places; [RW26b, Radchenko, Wheeler (2026b), Section 3] writes
`K₊` for the totally positive elements. -/
def IsTotallyPositive (F : RealQuadraticFieldData K) (c : K) : Prop :=
  0 < realEmbeddingAt K F.place c ∧ 0 < realEmbeddingAt K F.otherPlace c

/-- An element positive at both real places is totally positive. -/
theorem IsTotallyPositive.mk {F : RealQuadraticFieldData K} {c : K}
    (hplace : 0 < realEmbeddingAt K F.place c)
    (hother : 0 < realEmbeddingAt K F.otherPlace c) : F.IsTotallyPositive c :=
  ⟨hplace, hother⟩

/-- A totally positive element is positive at the selected real place. -/
theorem IsTotallyPositive.place_pos {F : RealQuadraticFieldData K} {c : K}
    (hc : F.IsTotallyPositive c) : 0 < realEmbeddingAt K F.place c :=
  hc.1

/-- A totally positive element is positive at the other real place. -/
theorem IsTotallyPositive.otherPlace_pos {F : RealQuadraticFieldData K} {c : K}
    (hc : F.IsTotallyPositive c) : 0 < realEmbeddingAt K F.otherPlace c :=
  hc.2

/-- A totally positive element is nonzero. -/
theorem IsTotallyPositive.ne_zero {F : RealQuadraticFieldData K} {c : K}
    (hc : F.IsTotallyPositive c) : c ≠ 0 := by
  intro h
  have hc' := hc.place_pos
  rw [h, map_zero] at hc'
  exact (lt_irrefl 0 hc')

/-- Products of totally positive elements are totally positive. -/
theorem IsTotallyPositive.mul {F : RealQuadraticFieldData K} {a b : K}
    (ha : F.IsTotallyPositive a) (hb : F.IsTotallyPositive b) :
    F.IsTotallyPositive (a * b) := by
  apply IsTotallyPositive.mk
  · rw [map_mul]; exact mul_pos ha.place_pos hb.place_pos
  · rw [map_mul]; exact mul_pos ha.otherPlace_pos hb.otherPlace_pos

/-- The inverse of a totally positive element is totally positive. -/
theorem IsTotallyPositive.inv {F : RealQuadraticFieldData K} {c : K}
    (hc : F.IsTotallyPositive c) : F.IsTotallyPositive c⁻¹ := by
  exact ⟨by simpa only [map_inv₀] using inv_pos.mpr hc.place_pos,
    by simpa only [map_inv₀] using inv_pos.mpr hc.otherPlace_pos⟩

/-- The trace conjugate of a totally positive element is totally positive. -/
theorem IsTotallyPositive.trace_sub {F : RealQuadraticFieldData K} {c : K}
    (hc : F.IsTotallyPositive c) :
    F.IsTotallyPositive ((Algebra.trace ℚ K c : K) - c) := by
  exact ⟨(F.trace_sub_realEmbeddings c).1 ▸ hc.otherPlace_pos,
    (F.trace_sub_realEmbeddings c).2 ▸ hc.place_pos⟩

/-! ### Trace conjugation and norm

Trace conjugation swaps the two real values and preserves their product. -/

/-- The norm of a quadratic element is unchanged by trace conjugation. -/
theorem norm_trace_sub (F : RealQuadraticFieldData K) (α : K) :
    Algebra.norm ℚ ((Algebra.trace ℚ K α : K) - α) = Algebra.norm ℚ α := by
  let δ : K := (Algebra.trace ℚ K α : K) - α
  obtain ⟨hplace, hother⟩ := F.trace_sub_realEmbeddings α
  have hn := F.mul_realEmbeddingAt_otherPlace_eq_norm δ
  rw [hplace, hother, mul_comm, F.mul_realEmbeddingAt_otherPlace_eq_norm α] at hn
  exact_mod_cast hn.symm

end RealQuadraticFieldData

/-! ### Places of extensions of a real quadratic field

An embedding extending a real embedding defines a place above that real place. -/

/-- An embedding extending `ρ_w` defines a place above `w`. -/
theorem liesOver_realEmbeddingAt {K H : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] [Field H] [Algebra K H]
    (ψ : H →+* ℂ) (w : InfinitePlace K)
    (hψ : ∀ a : K, ψ (algebraMap K H a) = (realEmbeddingAt K w a : ℂ)) :
    (InfinitePlace.mk ψ).LiesOver w := by
  have hcomp : ψ.comp (algebraMap K H) =
      Complex.ofRealHom.comp (realEmbeddingAt K w) := RingHom.ext hψ
  have hcomap : (InfinitePlace.mk ψ).comap (algebraMap K H) = w := by
    rw [InfinitePlace.comap_mk, hcomp, mk_realEmbeddingAt]
  exact ⟨congrArg Subtype.val hcomap⟩

/-- An automorphism moving the selected real embedding sends an extension of it to a place
above the other real place. -/
theorem mapped_liesOver_otherPlace {K H : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] [Field H] [Algebra K H]
    (F : RealQuadraticFieldData K) (τ : ℂ ≃ₐ[ℚ] ℂ)
    (hτ : ∃ a : K, τ (realEmbeddingAt K F.place a : ℂ) ≠
      (realEmbeddingAt K F.place a : ℂ))
    (ψ : H →+* ℂ)
    (hψ : ∀ a : K, ψ (algebraMap K H a) = (realEmbeddingAt K F.place a : ℂ)) :
    (InfinitePlace.mk (τ.toRingEquiv.toRingHom.comp ψ)).LiesOver F.otherPlace := by
  have hmove : ∃ a : K,
      (τ.toRingEquiv.toRingHom.comp
        (Complex.ofRealHom.comp (realEmbeddingAt K F.place))) a ≠
          (realEmbeddingAt K F.place a : ℂ) := by
    obtain ⟨a, ha⟩ := hτ
    refine ⟨a, ?_⟩
    change τ (realEmbeddingAt K F.place a : ℂ) ≠ _
    exact ha
  apply liesOver_realEmbeddingAt _ F.otherPlace
  intro a
  change τ (ψ (algebraMap K H a)) = _
  rw [hψ]
  exact F.apply_eq_realEmbeddingAt_otherPlace hmove a

end SIC

end
