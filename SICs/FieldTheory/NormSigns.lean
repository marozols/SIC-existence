/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-!
# Norm congruences and signs of relative norms

Integral norms respect congruences, and `τ(N_{E/K}β) < 0` iff an odd number of real embeddings
above `τ` are negative at `β`.

The norm of an algebraic integer modulo `n` depends only on the integer modulo `n`. For an
extension `E/K` of number fields this file characterizes the sign of a relative norm at a real
embedding; in particular, an element positive at every real embedding has positive norm to `ℚ`.
These results supply norm arguments in `SICs.ClassField.Reciprocity.Cyclotomic`.

## Mathematical argument

*Integral congruence.* Multiplication by congruent algebraic integers gives equal maps
after reduction modulo `n`; their determinants, hence their norms, agree modulo `n`.

*Signs.* Let `τ : K → ℝ` and `β ∈ E`, `β ≠ 0`. The norm is the product of the conjugates,
`τ(N_{E/K} β) = ∏_φ φ(β)` over the embeddings `φ : E → ℂ` extending `τ`
[83, Neukirch (1999), Chapter I, Proposition 2.6 (iii)]. The embeddings that are not real come in
pairs `φ ≠ φ̄`, both extending `τ` since `τ` is real, and each pair contributes
`φ(β)·φ̄(β) = |φ(β)|² > 0`. The real ones are the embeddings `ψ : E → ℝ` extending `τ`, and
`ψ(β) ≠ 0`. Hence `τ(N_{E/K} β) < 0` exactly when an odd number of them have `ψ(β) < 0`.

## References

- [83, Neukirch (1999), Chapter I, Proposition 2.6]
-/

noncomputable section

namespace SIC

/-! ### Congruences of integral norms

The determinant defining an integral norm commutes with reduction modulo an integer. -/

/-- Reduction of the norm modulo `n` depends only on the element modulo `n`. This is the
determinant step in `normCharacter_toPrincipalIdeal_eq_one`. -/
theorem norm_eq_mod_of_sub_mem_span {R : Type*} [CommRing R] [Algebra ℤ R]
    [Module.Free ℤ R] [Module.Finite ℤ R] (n : ℕ) (x y : R)
    (h : x - y ∈ Ideal.span {(n : R)}) :
    (Algebra.norm ℤ x : ZMod n) = (Algebra.norm ℤ y : ZMod n) := by
  have hmod : (inferInstance : Module ℤ R) = Algebra.toModule := Subsingleton.elim _ _
  have hfree : @Module.Free ℤ R _ _ Algebra.toModule := by
    rw [← hmod]
    infer_instance
  have hfinite : @Module.Finite ℤ R _ _ Algebra.toModule := by
    rw [← hmod]
    infer_instance
  let _ : Module ℤ R := Algebra.toModule
  have : Module.Free ℤ R := hfree
  have : Module.Finite ℤ R := hfinite
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp h
  have hbase : (Algebra.lmul ℤ R x).baseChange (ZMod n) =
      (Algebra.lmul ℤ R y).baseChange (ZMod n) := by
    ext t
    simp only [Algebra.coe_lmul_eq_mul, TensorProduct.AlgebraTensorModule.curry_apply,
      TensorProduct.curry_apply, LinearMap.coe_restrictScalars, LinearMap.baseChange_tmul,
      LinearMap.mul_apply_apply]
    rw [← sub_eq_zero, ← TensorProduct.tmul_sub]
    have hdiff : x * t - y * t = (n : ℤ) • (z * t) := by
      rw [← sub_mul, hz]
      simp [mul_assoc, mul_comm, mul_left_comm]
    rw [hdiff]
    have hbalance : (1 : ZMod n) ⊗ₜ[ℤ] ((n : ℤ) • (z * t)) =
        ((n : ℤ) • (1 : ZMod n)) ⊗ₜ[ℤ] (z * t) := by
      exact (TensorProduct.CompatibleSMul.int (R := ℤ) (M := ZMod n) (P := R)).smul_tmul
        (n : ℤ) (1 : ZMod n) (z * t) |>.symm
    rw [hbalance]
    have hnzero : (n : ℤ) • (1 : ZMod n) = 0 := by
      simp [zsmul_eq_mul]
    rw [hnzero, TensorProduct.zero_tmul]
  have hdet := congrArg LinearMap.det hbase
  rw [LinearMap.det_baseChange, LinearMap.det_baseChange] at hdet
  simpa [Algebra.norm_apply, algebraMap_int_eq] using hdet


variable {K : Type*} [Field K] [NumberField K] {E : Type*} [Field E] [NumberField E]
  [Algebra K E]

/-! ### The sign of a relative norm at a real embedding

A relative norm is negative at a real embedding `τ` of `K` exactly when an odd number of the real
embeddings of `E` above `τ` are negative on the element: the complex embeddings above `τ` pair off
into conjugates with positive product. -/

/-- The sign of a finite nonzero real product is controlled by its negative factors;
used by `realEmbedding_norm_neg_iff_odd`. -/
private lemma prod_neg_iff_odd {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    (∏ i ∈ s, f i) < 0 ↔ Odd (s.filter fun i ↦ f i < 0).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.filter_insert]
      have hfa := hf a (Finset.mem_insert_self a s)
      have hfs : ∀ i ∈ s, f i ≠ 0 := fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
      have hprod : ∏ i ∈ s, f i ≠ 0 := Finset.prod_ne_zero_iff.mpr hfs
      rcases lt_or_gt_of_ne hfa with hneg | hpos
      · rw [ite_eq_left hneg, Finset.card_insert_of_notMem
          (fun h ↦ ha (Finset.mem_filter.mp h).1), Nat.odd_add_one, ← ih hfs]
        constructor
        · intro h hn
          nlinarith
        · intro h
          exact mul_neg_of_neg_of_pos hneg (lt_of_le_of_ne (not_lt.mp h) hprod.symm)
      · rw [ite_eq_right (not_lt_of_ge hpos.le), ← ih hfs]
        constructor
        · intro h
          exact ((mul_neg_iff.mp h).resolve_right fun z ↦
            (not_lt_of_ge hpos.le) z.1).2
        · exact mul_neg_of_pos_of_neg hpos

/-- The complex embedding induced from a real embedding; used by
`realEmbedding_norm_neg_iff_odd`. -/
private abbrev complexify {F : Type*} [Field F] (τ : F →+* ℝ) : F →+* ℂ :=
  Complex.ofRealHom.comp τ

open scoped Classical in
/-- The complex embeddings above a fixed real embedding; used by
`realEmbedding_norm_neg_iff_odd`. -/
private def embeddingsAbove {F L : Type*} [Field F] [Field L] [NumberField L]
    [Algebra F L] (τ : F →+* ℝ) : Finset (L →+* ℂ) :=
  Finset.univ.filter fun σ ↦ σ.comp (algebraMap F L) = complexify τ

/-- Membership in `embeddingsAbove`; used by `realEmbedding_norm_neg_iff_odd`. -/
private lemma mem_embeddingsAbove {F L : Type*} [Field F] [Field L] [NumberField L]
    [Algebra F L] {τ : F →+* ℝ} {σ : L →+* ℂ} :
    σ ∈ embeddingsAbove τ ↔ σ.comp (algebraMap F L) = complexify τ := by
  classical
  simp [embeddingsAbove]

/-- Conjugation preserves the embeddings above a real embedding; used by
`realEmbedding_norm_neg_iff_odd`. -/
private lemma conjugate_mem_embeddingsAbove {F L : Type*} [Field F] [Field L]
    [NumberField L] [Algebra F L] {τ : F →+* ℝ} {σ : L →+* ℂ}
    (hσ : σ ∈ embeddingsAbove τ) :
    NumberField.ComplexEmbedding.conjugate σ ∈ embeddingsAbove τ := by
  rw [mem_embeddingsAbove] at hσ ⊢
  ext x
  have hx := RingHom.congr_fun hσ x
  simp only [RingHom.coe_comp, Function.comp_apply] at hx ⊢
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq, hx]
  exact Complex.conj_ofReal _

/-- The relative norm evaluated above `τ` is the product over embeddings above `τ`;
used by `realEmbedding_norm_neg_iff_odd`. -/
private lemma complexify_norm_eq_prod {F L : Type*} [Field F] [NumberField F]
    [Field L] [NumberField L] [Algebra F L] (τ : F →+* ℝ) (β : L) :
    complexify τ (Algebra.norm F β) = ∏ σ ∈ embeddingsAbove τ, σ β := by
  classical
  let _ : Algebra F ℂ := (complexify τ).toAlgebra
  change algebraMap F ℂ (Algebra.norm F β) = _
  rw [Algebra.norm_eq_prod_embeddings F ℂ β]
  refine Finset.prod_bij' (fun σ _ ↦ (σ : L →+* ℂ))
    (fun σ hσ ↦ { toRingHom := σ, commutes' := fun x ↦ ?_ }) ?_ ?_ ?_ ?_ ?_
  · exact RingHom.congr_fun (mem_embeddingsAbove.mp hσ) x
  · intro σ _
    rw [mem_embeddingsAbove]
    ext x
    exact σ.commutes x
  · exact fun _ _ ↦ Finset.mem_univ _
  · intro σ _
    ext
    rfl
  · intro σ _
    rfl
  · intro σ _
    rfl

open scoped Classical in
/-- The nonreal embeddings contribute the product of their positive absolute values;
used by `realEmbedding_norm_neg_iff_odd`. -/
private lemma prod_nonreal {F L : Type*} [Field F] [Field L] [NumberField L]
    [Algebra F L] (τ : F →+* ℝ) (β : L) (hβ : β ≠ 0) :
    ∏ σ ∈ (embeddingsAbove τ).filter
        (fun σ ↦ ¬NumberField.ComplexEmbedding.IsReal σ), σ β =
      ((∏ σ ∈ (embeddingsAbove τ).filter
        (fun σ ↦ ¬NumberField.ComplexEmbedding.IsReal σ), ‖σ β‖ : ℝ) : ℂ) := by
  classical
  let s := (embeddingsAbove (F := F) (L := L) τ).filter
    (fun σ ↦ ¬NumberField.ComplexEmbedding.IsReal σ)
  have hne : ∀ σ : L →+* ℂ, σ β ≠ 0 := fun σ ↦ (map_ne_zero σ).mpr hβ
  have hunit : ∏ σ ∈ s, σ β / (‖σ β‖ : ℂ) = 1 := by
    refine Finset.prod_involution
      (fun σ _ ↦ NumberField.ComplexEmbedding.conjugate σ) ?_ ?_ ?_ ?_
    · intro σ _
      rw [NumberField.ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj,
        div_mul_div_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      have hn : (‖σ β‖ : ℂ) ≠ 0 := by
        exact_mod_cast (norm_ne_zero_iff.mpr (hne σ))
      push_cast
      field_simp
    · intro σ hσ _
      have hnreal := (Finset.mem_filter.mp hσ).2
      rwa [NumberField.ComplexEmbedding.isReal_iff] at hnreal
    · intro σ hσ
      have hs := Finset.mem_filter.mp hσ
      exact Finset.mem_filter.mpr
        ⟨conjugate_mem_embeddingsAbove hs.1, by
          simpa only [NumberField.ComplexEmbedding.isReal_conjugate_iff] using hs.2⟩
    · intro σ _
      exact NumberField.ComplexEmbedding.involutive_conjugate L σ
  rw [Finset.prod_div_distrib,
    div_eq_one_iff_eq (Finset.prod_ne_zero_iff.mpr fun σ _ ↦ by
      exact_mod_cast (norm_ne_zero_iff.mpr (hne σ)))] at hunit
  rw [hunit]
  push_cast
  rfl

/-- A complexified real embedding is fixed by complex conjugation; used by
`complexify_mem_real_embeddingsAbove`. -/
private lemma complexify_isReal {F : Type*} [Field F] (ψ : F →+* ℝ) :
    NumberField.ComplexEmbedding.IsReal (complexify ψ) := by
  rw [NumberField.ComplexEmbedding.isReal_iff]
  ext x
  simp [NumberField.ComplexEmbedding.conjugate_coe_eq]

open scoped Classical in
/-- Complexification sends a real embedding above `τ` to a real complex embedding above `τ`;
used by `prod_real`. -/
private lemma complexify_mem_real_embeddingsAbove {F L : Type*} [Field F] [Field L]
    [NumberField L] [Algebra F L] {τ : F →+* ℝ} {ψ : L →+* ℝ}
    (hψ : ψ.comp (algebraMap F L) = τ) :
    complexify ψ ∈ (embeddingsAbove τ).filter NumberField.ComplexEmbedding.IsReal := by
  classical
  refine Finset.mem_filter.mpr ⟨mem_embeddingsAbove.mpr ?_, complexify_isReal ψ⟩
  ext x
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [← hψ]
  rfl

omit [NumberField K] [NumberField E] [Algebra K E] in
/-- The real embedding underlying a real complex embedding above `τ` also lies above `τ`;
used by `prod_real`. -/
private lemma realEmbedding_mem_above {F L : Type*} [Field F] [Field L] [NumberField L]
    [Algebra F L] {τ : F →+* ℝ} {σ : L →+* ℂ}
    (hreal : NumberField.ComplexEmbedding.IsReal σ) (habove : σ ∈ embeddingsAbove τ) :
    hreal.embedding.comp (algebraMap F L) = τ := by
  ext x
  apply Complex.ofReal_injective
  have hx := RingHom.congr_fun (mem_embeddingsAbove.mp habove) x
  simp only [RingHom.coe_comp, Function.comp_apply] at hx ⊢
  rw [NumberField.ComplexEmbedding.IsReal.coe_embedding_apply, hx]
  rfl

open scoped Classical in
/-- The real complex embeddings above `τ` correspond to real embeddings above `τ`;
used by `realEmbedding_norm_factor`. -/
private lemma prod_real {F L : Type*} [Field F] [Field L] [NumberField L]
    [Algebra F L] (τ : F →+* ℝ) (β : L) :
    ∏ σ ∈ (embeddingsAbove τ).filter NumberField.ComplexEmbedding.IsReal, σ β =
      ((∏ ψ ∈ Finset.univ.filter
        (fun ψ : L →+* ℝ ↦ ψ.comp (algebraMap F L) = τ), ψ β : ℝ) : ℂ) := by
  classical
  push_cast
  symm
  refine Finset.prod_bij' (fun ψ _ ↦ Complex.ofRealHom.comp ψ)
    (fun σ hσ ↦ (Finset.mem_filter.mp hσ).2.embedding) ?_ ?_ ?_ ?_ ?_
  · intro ψ hψ
    exact complexify_mem_real_embeddingsAbove (Finset.mem_filter.mp hψ).2
  · intro σ hσ
    have hs := Finset.mem_filter.mp hσ
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, realEmbedding_mem_above hs.2 hs.1⟩
  · intro ψ _
    ext x
    apply Complex.ofReal_injective
    rw [NumberField.ComplexEmbedding.IsReal.coe_embedding_apply]
    rfl
  · intro σ hσ
    ext x
    exact NumberField.ComplexEmbedding.IsReal.coe_embedding_apply
      (Finset.mem_filter.mp hσ).2 x
  · intro ψ _
    rfl

open scoped Classical in
/-- The relative norm at `τ` factors as the product over real embeddings above `τ`
times a positive real factor; used by `realEmbedding_norm_neg_iff_odd`. -/
private lemma realEmbedding_norm_factor (τ : K →+* ℝ) {β : E} (hβ : β ≠ 0) :
    ∃ p : ℝ, 0 < p ∧ τ (Algebra.norm K β) =
      (∏ ψ ∈ Finset.univ.filter
        (fun ψ : E →+* ℝ ↦ ψ.comp (algebraMap K E) = τ), ψ β) * p := by
  classical
  let p : ℝ := ∏ σ ∈ (embeddingsAbove τ).filter
    (fun σ ↦ ¬NumberField.ComplexEmbedding.IsReal σ), ‖σ β‖
  refine ⟨p, Finset.prod_pos fun σ _ ↦
    norm_pos_iff.mpr ((map_ne_zero σ).mpr hβ), ?_⟩
  apply Complex.ofReal_injective
  change complexify τ (Algebra.norm K β) = _
  rw [complexify_norm_eq_prod τ β,
    ← Finset.prod_filter_mul_prod_filter_not (embeddingsAbove τ)
      NumberField.ComplexEmbedding.IsReal,
    prod_real, prod_nonreal τ β hβ]
  simp only [p]
  exact (map_mul Complex.ofRealHom _ _).symm

open scoped Classical in
omit [NumberField K] in
/-- The subtype of negative real embeddings above `τ` has the cardinality of the corresponding
filtered finset; used by `realEmbedding_norm_neg_iff_odd`. -/
private lemma card_negative_real_embeddings (τ : K →+* ℝ) (β : E) :
    Nat.card {ψ : E →+* ℝ // ψ.comp (algebraMap K E) = τ ∧ ψ β < 0} =
      ((Finset.univ.filter fun ψ : E →+* ℝ ↦
        ψ.comp (algebraMap K E) = τ).filter fun ψ ↦ ψ β < 0).card := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  change (Finset.univ.filter fun ψ : E →+* ℝ ↦
    ψ.comp (algebraMap K E) = τ ∧ ψ β < 0).card = _
  rw [Finset.filter_filter]

/-- **The sign of a relative norm at a real place**: for `β ≠ 0` and a real embedding `τ` of `K`,
`τ(N_{E/K} β) < 0` if and only if an odd number of the real embeddings `ψ` of `E` extending `τ`
have `ψ(β) < 0`. From `τ(N_{E/K} β) = ∏_φ φ(β)` over the complex embeddings extending `τ`
[83, Neukirch (1999), Chapter I, Proposition 2.6 (iii)], in which the conjugate pairs of nonreal
embeddings contribute `|φ(β)|² > 0`. -/
theorem realEmbedding_norm_neg_iff_odd (τ : K →+* ℝ) {β : E} (hβ : β ≠ 0) :
    τ (Algebra.norm K β) < 0 ↔
      Odd (Nat.card {ψ : E →+* ℝ // ψ.comp (algebraMap K E) = τ ∧ ψ β < 0}) := by
  classical
  let r := Finset.univ.filter fun ψ : E →+* ℝ ↦ ψ.comp (algebraMap K E) = τ
  obtain ⟨p, hp, hfactor⟩ := realEmbedding_norm_factor τ hβ
  change τ (Algebra.norm K β) = (∏ ψ ∈ r, ψ β) * p at hfactor
  rw [hfactor, mul_neg_iff, prod_neg_iff_odd r (fun ψ ↦ ψ β)
    (fun ψ _ ↦ (map_ne_zero ψ).mpr hβ)]
  rw [card_negative_real_embeddings τ β]
  constructor
  · rintro (⟨_, hpneg⟩ | h)
    · exact absurd hpneg (not_lt_of_ge hp.le)
    · exact h.1
  · exact fun h ↦ Or.inr ⟨h, hp⟩

/-- An element positive at every real embedding has positive norm to $\mathbb Q$.
This follows from `realEmbedding_norm_neg_iff_odd`. -/
theorem norm_pos_of_forall_realEmbedding_pos {F : Type*} [Field F] [NumberField F]
    {x : F} (hx : x ≠ 0) (hreal : ∀ ψ : F →+* ℝ, 0 < ψ x) :
    0 < Algebra.norm ℚ x := by
  have hne : Algebra.norm ℚ x ≠ 0 :=
    (Algebra.norm_eq_zero_iff).not.mpr hx
  by_contra hpos
  have hneg : Algebra.norm ℚ x < 0 :=
    lt_of_le_of_ne (le_of_not_gt hpos) hne
  have hnegR : (algebraMap ℚ ℝ) (Algebra.norm ℚ x) < 0 := by
    change ((Algebra.norm ℚ x : ℚ) : ℝ) < 0
    exact_mod_cast hneg
  have hodd := (realEmbedding_norm_neg_iff_odd (K := ℚ) (E := F)
    (algebraMap ℚ ℝ) hx).mp hnegR
  have hempty : IsEmpty {ψ : F →+* ℝ //
      ψ.comp (algebraMap ℚ F) = algebraMap ℚ ℝ ∧ ψ x < 0} :=
    ⟨fun ⟨ψ, hψ⟩ => (not_lt_of_ge (hreal ψ).le) hψ.2⟩
  rw [Nat.card_of_isEmpty] at hodd
  exact Nat.not_odd_zero hodd

end SIC

end
