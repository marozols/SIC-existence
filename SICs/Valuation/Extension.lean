/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.NumberTheory.Ostrowski
import Mathlib.RingTheory.Polynomial.GaussNorm
import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# Extending real-valued valuations along field extensions

Every valuation `w : F → ℝ≥0` of a field extends to every field extension `L/F`, and an element
of a field of characteristic zero that is a unit at every valuation `v : L → ℝ≥0` with `v(p) < 1`
is algebraic over `ℚ`.

This module supplies the passage from valuations to algebraicity in the proof of
`pseudolatticeDilog_isAlgebraic`, the replacement of the appeal to [RW26, Radchenko, Wheeler
(2026), Theorem 1, `thm:faddeevqbar`] at the start of the proof of [RW26b, Radchenko, Wheeler
(2026b), Section 5, Theorem 5]. The valuations are
multiplicative with values in `ℝ≥0`, that is of rank at most one, as in
`SICs.Valuation.RootsOfUnity`. The one-step inputs are the generalized Gauss norm at every
positive radius [BGR84, Bosch, Güntzer, Remmert (1984), p. 43] and the spectral norm on algebraic
extensions [BGR84, Bosch, Güntzer, Remmert (1984), §3.2.1, Theorem 2, pp. 134–136;
§3.2.4, Theorem 2, pp. 139–140]. These steps are assembled below by Zorn's lemma to extend
the valuation to an arbitrary field.

## The argument

*Simple transcendental extensions.* For `a` transcendental over `F`, `F(a)` is the field of
rational functions in `a`. The generalized Gauss norm `‖∑ cᵢXⁱ‖ = maxᵢ w(cᵢ)tⁱ` is a
valuation for every `t > 0` [BGR84, Bosch, Güntzer, Remmert (1984), p. 43], as in
`Polynomial.gaussNorm_mul`; hence `f(a)/g(a) ↦ ‖f‖/‖g‖` extends `w` with value `t` at `a`.
At radius one, [BGR84, Bosch, Güntzer, Remmert (1984), §1.5.3, Corollary 2, p. 44]
gives the least-maximizing-index proof of Gauss multiplicativity.

*Algebraic extensions.* For a nontrivial `w`, complete `F` (a nonarchimedean complete normed
field) and take an algebraic closure `Ω` of the completion; the spectral norm is a multiplicative
nonarchimedean norm on `Ω` extending the norm of the completion (`spectralMulAlgNorm` and
`spectralNorm_extends`), by [BGR84, Bosch, Güntzer, Remmert (1984), §3.2.1, Theorem 2,
pp. 134–136; §3.2.4, Theorem 2, pp. 139–140]. An `F`-embedding of an algebraic extension
`E/F` into `Ω` (`IsAlgClosed.lift`) pulls it back to a valuation of `E` extending `w`.
A trivial `w` extends trivially.

*Arbitrary extensions.* Zorn's lemma on intermediate fields carrying a valuation that extends
`w`, ordered by extension: a chain has its union as an upper bound, and a maximal element is all
of `L` by the two one-step extensions.

*Algebraicity.* If `z` is transcendental over `ℚ`, the Gauss extension of the `p`-adic absolute
value to `ℚ(z)` with value `1/p` at `z`, extended to `L`, has `v(p) = 1/p < 1` and `v(z) ≠ 1`.
-/

open scoped NNReal

namespace SIC

open IntermediateField

/-! ### The Gauss and spectral extension steps

The Gauss norm extends a valuation to a simple transcendental extension. On an algebraic
extension, the spectral norm over the completion supplies the extension. -/

/-- The real absolute value associated with a nonarchimedean `ℝ≥0` valuation, used in the
Gauss and spectral steps. -/
private def valuationAbsoluteValue {F : Type*} [Field F] (w : Valuation F ℝ≥0) :
    AbsoluteValue F ℝ where
  toFun x := w x
  map_mul' x y := by simp
  nonneg' x := NNReal.coe_nonneg _
  eq_zero' x := by exact_mod_cast w.zero_iff
  add_le' x y := by
    apply le_trans (b := max (w x : ℝ) (w y : ℝ))
    · exact_mod_cast w.map_add x y
    · exact max_le_add_of_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)

/-- The absolute value associated with a valuation is nonarchimedean. -/
private theorem valuationAbsoluteValue_nonarchimedean {F : Type*} [Field F]
    (w : Valuation F ℝ≥0) : IsNonarchimedean (valuationAbsoluteValue w) := by
  intro x y
  exact_mod_cast w.map_add x y

/-- The `ℝ≥0` valuation associated with a nonarchimedean real absolute value. -/
private def absoluteValuation {F : Type*} [Ring F] [Nontrivial F] (a : AbsoluteValue F ℝ)
    (ha : IsNonarchimedean a) : Valuation F ℝ≥0 where
  toFun x := Real.toNNReal (a x)
  map_zero' := by simp
  map_one' := by simp
  map_mul' x y := by simp [Real.toNNReal_mul (a.nonneg x)]
  map_add_le_max' x y := by
    rw [← Real.toNNReal_monotone.map_max]
    exact Real.toNNReal_mono (ha x y)

/-- The value of the valuation associated with an absolute value. -/
private theorem absoluteValuation_apply {F : Type*} [Ring F] [Nontrivial F] (a : AbsoluteValue F ℝ)
    (ha : IsNonarchimedean a) (x : F) :
    (absoluteValuation a ha) x = Real.toNNReal (a x) := rfl

/-- The value of the absolute value associated with a valuation. -/
private theorem valuationAbsoluteValue_apply {F : Type*} [Field F] (w : Valuation F ℝ≥0)
    (x : F) : (valuationAbsoluteValue w) x = w x := rfl

/-- The Gauss valuation on polynomials with radius `t`, used to extend a valuation to a
rational function field. -/
private noncomputable def gaussPolynomialValuation {F : Type*} [Field F] (w : Valuation F ℝ≥0)
    (t : ℝ≥0) (ht : 0 < t) : Valuation (Polynomial F) ℝ≥0 := by
  let a := valuationAbsoluteValue w
  have hna : IsNonarchimedean a := valuationAbsoluteValue_nonarchimedean w
  have ht' : (0 : ℝ) < t := NNReal.coe_pos.mpr ht
  letI : IsAbsoluteValue (Polynomial.gaussNorm a (t : ℝ)) :=
    Polynomial.gaussNorm_isAbsoluteValue hna ht'
  let b : AbsoluteValue (Polynomial F) ℝ :=
    IsAbsoluteValue.toAbsoluteValue (Polynomial.gaussNorm a (t : ℝ))
  have hb : IsNonarchimedean b :=
    Polynomial.isNonarchimedean_gaussNorm a hna ht'.le
  exact absoluteValuation (F := Polynomial F) b hb

/-- The Gauss valuation is the nonnegative real Gauss norm. -/
private theorem gaussPolynomialValuation_apply {F : Type*} [Field F]
    (w : Valuation F ℝ≥0) (t : ℝ≥0) (ht : 0 < t) (p : Polynomial F) :
    gaussPolynomialValuation w t ht p =
      Real.toNNReal (Polynomial.gaussNorm (valuationAbsoluteValue w) (t : ℝ) p) := rfl

/-- The Gauss valuation restricts to the given coefficient valuation. -/
private theorem gaussPolynomialValuation_C {F : Type*} [Field F]
    (w : Valuation F ℝ≥0) (t : ℝ≥0) (ht : 0 < t) (x : F) :
    gaussPolynomialValuation w t ht (Polynomial.C x) = w x := by
  simp [gaussPolynomialValuation_apply, Polynomial.gaussNorm_C,
    valuationAbsoluteValue_apply]

/-- The Gauss valuation assigns value `t` to `X`. -/
private theorem gaussPolynomialValuation_X {F : Type*} [Field F]
    (w : Valuation F ℝ≥0) (t : ℝ≥0) (ht : 0 < t) :
    gaussPolynomialValuation w t ht Polynomial.X = t := by
  rw [← Polynomial.monomial_one_one_eq_X]
  simp [gaussPolynomialValuation_apply, Polynomial.gaussNorm_monomial]

/-- A nonzero polynomial has nonzero Gauss value when the radius is positive. -/
private theorem gaussPolynomialValuation_ne_zero {F : Type*} [Field F]
    (w : Valuation F ℝ≥0) (t : ℝ≥0) (ht : 0 < t) {p : Polynomial F} (hp : p ≠ 0) :
    gaussPolynomialValuation w t ht p ≠ 0 := by
  rw [gaussPolynomialValuation_apply, ne_eq, Real.toNNReal_eq_zero]
  intro h
  have hnonneg := Polynomial.gaussNorm_nonneg (valuationAbsoluteValue w) p
    (NNReal.coe_nonneg t)
  have hz : Polynomial.gaussNorm (valuationAbsoluteValue w) (t : ℝ) p = 0 :=
    le_antisymm h hnonneg
  exact hp ((Polynomial.gaussNorm_eq_zero_iff (valuationAbsoluteValue w) p
    (fun x hx => (valuationAbsoluteValue w).eq_zero.mp hx)
    (NNReal.coe_pos.mpr ht)).mp hz)

/-- The Gauss valuation on rational functions, obtained by localization of the polynomial
valuation. -/
private noncomputable def gaussRatFuncValuation {F : Type*} [Field F]
    (w : Valuation F ℝ≥0) (t : ℝ≥0) (ht : 0 < t) : Valuation (RatFunc F) ℝ≥0 := by
  let vp := gaussPolynomialValuation w t ht
  have hs : nonZeroDivisors (Polynomial F) ≤ vp.supp.primeCompl := by
    intro p hp
    change p ∉ vp.supp
    rw [vp.mem_supp_iff]
    exact gaussPolynomialValuation_ne_zero w t ht (mem_nonZeroDivisors_iff_ne_zero.mp hp)
  exact vp.extendToLocalization hs (RatFunc F)

/-- The rational function Gauss valuation extends the coefficient valuation. -/
private theorem gaussRatFuncValuation_C {F : Type*} [Field F]
    (w : Valuation F ℝ≥0) (t : ℝ≥0) (ht : 0 < t) (x : F) :
    gaussRatFuncValuation w t ht (RatFunc.C x) = w x := by
  rw [← RatFunc.algebraMap_C]
  simp only [gaussRatFuncValuation, Valuation.extendToLocalization_apply_map_apply,
    gaussPolynomialValuation_C]

/-- The rational function Gauss valuation assigns value `t` to `X`. -/
private theorem gaussRatFuncValuation_X {F : Type*} [Field F]
    (w : Valuation F ℝ≥0) (t : ℝ≥0) (ht : 0 < t) :
    gaussRatFuncValuation w t ht RatFunc.X = t := by
  rw [← RatFunc.algebraMap_X]
  simp only [gaussRatFuncValuation, Valuation.extendToLocalization_apply_map_apply,
    gaussPolynomialValuation_X]

/-- For a transcendental `a`, the valuation on `F` extends to `F⟮a⟯` with any prescribed
positive value `t` at `a`, using the generalized Gauss norm of
[BGR84, Bosch, Güntzer, Remmert (1984), p. 43]. -/
theorem exists_valuation_adjoin_transcendental {F L : Type*}
    [Field F] [Field L] [Algebra F L] (w : Valuation F ℝ≥0)
    {a : L} (ha : Transcendental F a) (t : ℝ≥0) (ht : 0 < t) :
    ∃ v : Valuation F⟮a⟯ ℝ≥0,
      v.comap (algebraMap F F⟮a⟯) = w ∧ v (AdjoinSimple.gen F a) = t := by
  let e := RatFunc.algEquivOfTranscendental a ha
  let v := (gaussRatFuncValuation w t ht).comap e.symm.toRingHom
  refine ⟨v, ?_, ?_⟩
  · ext x
    simp only [v, Valuation.comap_apply]
    rw [← e.commutes x]
    simp only [AlgEquiv.symm_toRingEquiv, RingEquiv.symm_mk, AlgEquiv.toEquiv_eq_coe,
      AlgEquiv.symm_toEquiv_eq_symm, RingEquiv.toRingHom_eq_coe, RatFunc.algebraMap_eq_C,
      RingHom.coe_coe, RingEquiv.coe_mk, EquivLike.coe_coe, AlgEquiv.symm_apply_apply,
      NNReal.coe_inj]
    exact gaussRatFuncValuation_C w t ht x
  · change gaussRatFuncValuation w t ht (e.symm (AdjoinSimple.gen F a)) = t
    rw [RatFunc.algEquivOfTranscendental_symm_gen]
    exact gaussRatFuncValuation_X w t ht

/-- A nontrivial nonarchimedean valuation has an element of nonunit norm on the completion;
used by `exists_algebraic_extension_nontrivial`. -/
private theorem valuationCompletion_witness {F : Type*} [Field F]
    (w : Valuation F ℝ≥0) (hex : ∃ x : F, x ≠ 0 ∧ w x ≠ 1) :
    ∃ y : UniformSpace.Completion (WithAbs (valuationAbsoluteValue w)),
      y ≠ 0 ∧ ‖y‖ ≠ 1 := by
  classical
  obtain ⟨x, hx, hx1⟩ := hex
  let a := valuationAbsoluteValue w
  let : NontriviallyNormedField (WithAbs a) :=
    NontriviallyNormedField.ofNormNeOne ⟨WithAbs.toAbs a x,
      by simpa using hx, by simpa [WithAbs.norm_toAbs_eq, a, valuationAbsoluteValue_apply]
        using hx1⟩
  let C := UniformSpace.Completion (WithAbs a)
  exact ⟨(↑(WithAbs.toAbs a x) : C),
    by
      intro h
      have hcoe : (↑(WithAbs.toAbs a x) : C) = (↑(0 : WithAbs a) : C) := by
        simpa only [UniformSpace.Completion.coe_zero] using h
      have hx' : WithAbs.toAbs a x = 0 :=
        (UniformSpace.Completion.coe_injective (WithAbs a)) hcoe
      exact hx (congrArg WithAbs.ofAbs hx'),
    by
      rw [UniformSpace.Completion.norm_coe, WithAbs.norm_toAbs_eq]
      change (w x : ℝ) ≠ 1
      exact_mod_cast hx1⟩

/-- The completion of a field carrying a nonarchimedean valuation is ultrametric;
used by `exists_algebraic_extension_nontrivial`. -/
private theorem valuationCompletion_ultrametric {F : Type*} [Field F]
    (w : Valuation F ℝ≥0) :
    IsUltrametricDist (UniformSpace.Completion (WithAbs (valuationAbsoluteValue w))) := by
  let a := valuationAbsoluteValue w
  have hna : IsNonarchimedean a := valuationAbsoluteValue_nonarchimedean w
  let : IsUltrametricDist (WithAbs a) :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm (by
      intro y z
      change a (y.ofAbs + z.ofAbs) ≤ max (a y.ofAbs) (a z.ofAbs)
      exact hna _ _)
  let C := UniformSpace.Completion (WithAbs a)
  exact IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm (by
    intro y z
    refine UniformSpace.Completion.induction_on₂ y z ?_ ?_
    · exact isClosed_le (by fun_prop) (by fun_prop)
    · intro y z
      rw [← UniformSpace.Completion.coe_add]
      rw [UniformSpace.Completion.norm_coe (y + z),
        UniformSpace.Completion.norm_coe y, UniformSpace.Completion.norm_coe z]
      exact IsUltrametricDist.isNonarchimedean_norm y z)

/-- The nontrivial algebraic extension step for
`exists_valuation_comap_eq_of_isAlgebraic`, using the spectral norm on an algebraic closure
of the completion. -/
private theorem exists_algebraic_extension_nontrivial {F L : Type*} [Field F]
    [Field L] [Algebra F L] [Algebra.IsAlgebraic F L] (w : Valuation F ℝ≥0)
    (hex : ∃ x : F, x ≠ 0 ∧ w x ≠ 1) :
    ∃ v : Valuation L ℝ≥0, v.comap (algebraMap F L) = w := by
  classical
  let a := valuationAbsoluteValue w
  let : IsUltrametricDist (WithAbs a) :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm (by
      intro y z
      change a (y.ofAbs + z.ofAbs) ≤ max (a y.ofAbs) (a z.ofAbs)
      exact valuationAbsoluteValue_nonarchimedean w _ _)
  let : NontriviallyNormedField (WithAbs a) :=
    NontriviallyNormedField.ofNormNeOne (by
      obtain ⟨x, hx, hx1⟩ := hex
      exact ⟨WithAbs.toAbs a x, by simpa using hx,
        by simpa [WithAbs.norm_toAbs_eq, a, valuationAbsoluteValue_apply] using hx1⟩)
  let C := UniformSpace.Completion (WithAbs a)
  let : NontriviallyNormedField C :=
    NontriviallyNormedField.ofNormNeOne (valuationCompletion_witness w hex)
  let : IsUltrametricDist C := valuationCompletion_ultrametric w
  let Ω := AlgebraicClosure C
  let f : F →+* Ω := (algebraMap C Ω).comp (algebraMap F C)
  let : Algebra F Ω := f.toAlgebra
  let emb : L →ₐ[F] Ω := IsAlgClosed.lift
  let : NormedField Ω := spectralNorm.normedField C Ω
  let : IsUltrametricDist Ω :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (isNonarchimedean_spectralNorm (K := C) (L := Ω))
  refine ⟨(NormedField.valuation (K := Ω)).comap emb.toRingHom, ?_⟩
  ext y
  simp only [Valuation.comap_apply, NormedField.valuation_apply]
  change (‖emb.toRingHom (algebraMap F L y)‖₊ : ℝ) = (w y : ℝ)
  have he : emb.toRingHom (algebraMap F L y) = algebraMap F Ω y := emb.commutes y
  rw [he]
  have hf : (algebraMap F Ω) y = f y := rfl
  rw [hf]
  change spectralNorm C Ω ((algebraMap C Ω) ((algebraMap F C) y)) = (w y : ℝ)
  rw [spectralNorm_extends]
  rw [UniformSpace.Completion.algebraMap_def]
  rw [UniformSpace.Completion.norm_coe, WithAbs.norm_toAbs_eq]
  rfl

/-- A valuation on a field extends to every algebraic field extension using the spectral norm
of [BGR84, Bosch, Güntzer, Remmert (1984), §3.2.1, Theorem 2, pp. 134–136; §3.2.4,
Theorem 2, pp. 139–140] after completion and pullback. -/
theorem exists_valuation_comap_eq_of_isAlgebraic {F L : Type*} [Field F] [Field L]
    [Algebra F L] [Algebra.IsAlgebraic F L] (w : Valuation F ℝ≥0) :
    ∃ v : Valuation L ℝ≥0, v.comap (algebraMap F L) = w := by
  classical
  by_cases h : ∃ x : F, x ≠ 0 ∧ w x ≠ 1
  · exact exists_algebraic_extension_nontrivial w h
  · refine ⟨1, ?_⟩
    ext x
    by_cases hx : x = 0
    · simp [hx]
    have hw : w x = 1 := by
      by_contra h'
      exact h ⟨x, hx, h'⟩
    have hm : algebraMap F L x ≠ 0 := by
      simpa using (RingHom.injective (algebraMap F L)).ne hx
    simp only [Valuation.comap_apply, Valuation.one_apply_of_ne_zero hm, hw]

/-- An intermediate field equipped with a valuation extending the fixed base valuation,
for the Zorn argument. -/
private structure ValExtension (F L : Type*) [Field F] [Field L] [Algebra F L]
    (w : Valuation F ℝ≥0) where
  /-- The intermediate field. -/
  E : IntermediateField F L
  /-- Its valuation. -/
  v : Valuation E ℝ≥0
  /-- Agreement with the base valuation. -/
  base : v.comap (algebraMap F E) = w

/-- A valued intermediate field lies below another when its field is contained in the
other and the valuations agree. -/
local instance valExtensionPreorder {F L : Type*} [Field F] [Field L] [Algebra F L]
    (w : Valuation F ℝ≥0) : Preorder (ValExtension F L w) where
  le u v := ∃ h : u.E ≤ v.E,
    ∀ x : u.E, u.v x = v.v (IntermediateField.inclusion h x)
  le_refl u := ⟨le_refl _, fun x => rfl⟩
  le_trans u v z huv hvz := by
    obtain ⟨h1, hv1⟩ := huv
    obtain ⟨h2, hv2⟩ := hvz
    refine ⟨le_trans h1 h2, ?_⟩
    intro x
    rw [hv1 x, hv2 (IntermediateField.inclusion h1 x),
      IntermediateField.inclusion_inclusion]

/-- The base field and its given valuation form the initial valued intermediate field. -/
local instance valExtensionNonempty {F L : Type*} [Field F] [Field L] [Algebra F L]
    (w : Valuation F ℝ≥0) : Nonempty (ValExtension F L w) := by
  let e := IntermediateField.botEquiv F L
  let v := w.comap e.toRingHom
  have hb : v.comap (algebraMap F (⊥ : IntermediateField F L)) = w := by
    ext x
    simp [v, Valuation.comap_apply]
  exact ⟨⟨⊥, v, hb⟩⟩

/-- A compatible value function on the union of a chain of valued intermediate fields.
Used by `valExtension_chain_bound`. -/
private structure ChainUnionData {F L : Type*} [Field F] [Field L] [Algebra F L]
    (w : Valuation F ℝ≥0) (c : Set (ValExtension F L w)) where
  /-- The union field of the chain. -/
  E : IntermediateField F L
  /-- Every union element lies in a member of the chain. -/
  memE : ∀ x : E, ∃ u : c, (x : L) ∈ u.1.E
  /-- The value obtained from a chain member containing the element. -/
  value : E → ℝ≥0
  /-- The value agrees with every chain member containing the element. -/
  value_eq : ∀ (x : E) (u : c) (hu : (x : L) ∈ u.1.E),
    value x = u.1.v ⟨(x : L), hu⟩
  /-- Two union elements lie in a common chain member. -/
  upper : ∀ x y : E, ∃ u : c, (x : L) ∈ u.1.E ∧ (y : L) ∈ u.1.E
  /-- Each chain member embeds in the union field. -/
  le : ∀ u : c, u.1.E ≤ E

/-- Construct the value function on the union from compatibility along a chain.
Used by `valExtension_chain_bound`. -/
private theorem exists_chainUnionData {F L : Type*} [Field F] [Field L]
    [Algebra F L] (w : Valuation F ℝ≥0)
    (c : Set (ValExtension F L w)) (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty) :
    Nonempty (ChainUnionData w c) := by
  classical
  let : Nonempty c := hne.to_subtype
  have hd : Directed (· ≤ ·) (fun u : c => u.1.E) := by
    intro u v
    rcases hc.total u.2 v.2 with h | h
    · exact ⟨v, h.1, le_rfl⟩
    · exact ⟨u, le_rfl, h.1⟩
  let E : IntermediateField F L := ⨆ u : c, u.1.E
  have memE (x : E) : ∃ u : c, (x : L) ∈ u.1.E := by
    have hx : (x : L) ∈ E := x.2
    change (x : L) ∈ ((⨆ u : c, u.1.E : IntermediateField F L) : Set L) at hx
    rw [IntermediateField.coe_iSup_of_directed hd] at hx
    simpa using hx
  have agree (x : E) (u v : c) (hu : (x : L) ∈ u.1.E)
      (hv : (x : L) ∈ v.1.E) :
      u.1.v ⟨(x : L), hu⟩ = v.1.v ⟨(x : L), hv⟩ := by
    rcases hc.total u.2 v.2 with h | h
    · convert h.2 ⟨(x : L), hu⟩ using 1
      exact Subtype.ext rfl
    · symm
      convert h.2 ⟨(x : L), hv⟩ using 1
      exact Subtype.ext rfl
  let witness (x : E) : c := Classical.choose (memE x)
  have witness_mem (x : E) : (x : L) ∈ (witness x).1.E :=
    Classical.choose_spec (memE x)
  let value (x : E) : ℝ≥0 :=
    (witness x).1.v ⟨(x : L), witness_mem x⟩
  have value_eq (x : E) (u : c) (hu : (x : L) ∈ u.1.E) :
      value x = u.1.v ⟨(x : L), hu⟩ :=
    agree x (witness x) u (witness_mem x) hu
  have upper (x y : E) :
      ∃ u : c, (x : L) ∈ u.1.E ∧ (y : L) ∈ u.1.E := by
    obtain ⟨u, hu⟩ := memE x
    obtain ⟨v, hv⟩ := memE y
    obtain ⟨z, huz, hvz⟩ := hd u v
    exact ⟨z, huz hu, hvz hv⟩
  exact ⟨⟨E, memE, value, value_eq, upper,
    fun u => le_iSup (fun v : c => v.1.E) u⟩⟩

/-- The compatible value on a chain union satisfies the valuation laws.
Used by `valExtension_chain_bound`. -/
private def chainUnionValuation {F L : Type*} [Field F] [Field L] [Algebra F L]
    {w : Valuation F ℝ≥0} {c : Set (ValExtension F L w)}
    (d : ChainUnionData w c) : Valuation d.E ℝ≥0 := by
  let E := d.E
  let memE := d.memE
  let value := d.value
  have value_eq (x : E) (u : c) (hu : (x : L) ∈ u.1.E) :
      value x = u.1.v ⟨(x : L), hu⟩ := d.value_eq x u hu
  let upper := d.upper
  exact {
    toFun := value
    map_zero' := by
      obtain ⟨u, hu⟩ := memE (0 : E)
      rw [value_eq (0 : E) u hu]
      have hz : (⟨((0 : E) : L), hu⟩ : u.1.E) = 0 := Subtype.ext (by simp)
      rw [hz]
      exact u.1.v.map_zero
    map_one' := by
      obtain ⟨u, hu⟩ := memE (1 : E)
      rw [value_eq (1 : E) u hu]
      have hz : (⟨((1 : E) : L), hu⟩ : u.1.E) = 1 := Subtype.ext (by simp)
      rw [hz]
      exact u.1.v.map_one
    map_mul' := by
      intro x y
      obtain ⟨u, hx, hy⟩ := upper x y
      have hxy : ((x * y : E) : L) ∈ u.1.E := by
        simpa using u.1.E.mul_mem hx hy
      rw [value_eq (x * y) u hxy, value_eq x u hx, value_eq y u hy]
      convert u.1.v.map_mul (⟨(x : L), hx⟩ : u.1.E) ⟨(y : L), hy⟩ using 1
    map_add_le_max' := by
      intro x y
      obtain ⟨u, hx, hy⟩ := upper x y
      have hxy : ((x + y : E) : L) ∈ u.1.E := by
        simpa using u.1.E.add_mem hx hy
      rw [value_eq (x + y) u hxy, value_eq x u hx, value_eq y u hy]
      convert u.1.v.map_add (⟨(x : L), hx⟩ : u.1.E) ⟨(y : L), hy⟩ using 1
  }

/-- A nonempty chain of compatible valued intermediate fields has an upper bound on its union. -/
private theorem valExtension_chain_bound {F L : Type*} [Field F] [Field L]
    [Algebra F L] (w : Valuation F ℝ≥0)
    (c : Set (ValExtension F L w)) (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty) :
    BddAbove c := by
  classical
  let d := Classical.choice (exists_chainUnionData w c hc hne)
  let E := d.E
  let memE := d.memE
  let value := d.value
  have value_eq (x : E) (u : c) (hu : (x : L) ∈ u.1.E) :
      value x = u.1.v ⟨(x : L), hu⟩ := d.value_eq x u hu
  let upper := d.upper
  let V : Valuation E ℝ≥0 := chainUnionValuation d
  let u : c := ⟨Classical.choose hne, Classical.choose_spec hne⟩
  have hb : V.comap (algebraMap F E) = w := by
    ext x
    change (value ((algebraMap F E) x) : ℝ) = (w x : ℝ)
    have hu : (((algebraMap F E) x : E) : L) ∈ u.1.E := by
      change algebraMap F L x ∈ u.1.E
      exact u.1.E.algebraMap_mem x
    rw [value_eq ((algebraMap F E) x) u hu]
    have he : (⟨_, hu⟩ : u.1.E) = algebraMap F u.1.E x := Subtype.ext rfl
    rw [he]
    exact_mod_cast congrArg (fun v : Valuation F ℝ≥0 => v x) u.1.base
  refine ⟨⟨E, V, hb⟩, ?_⟩
  intro z hz
  let uz : c := ⟨z, hz⟩
  have hE : z.E ≤ E := d.le uz
  refine ⟨hE, ?_⟩
  intro x
  change z.v x = value (IntermediateField.inclusion hE x)
  have hx : ((IntermediateField.inclusion hE x : E) : L) ∈ z.E := x.2
  rw [value_eq (IntermediateField.inclusion hE x) uz hx]
  congr 1

/-- The valuation on an intermediate field extends to the field generated by one more element. -/
private theorem valExtension_adjoin {F L : Type*} [Field F] [Field L]
    [Algebra F L] (w : Valuation F ℝ≥0) (u : ValExtension F L w)
    (a : L) : ∃ v : ValExtension F L w, u ≤ v ∧ a ∈ v.E := by
  classical
  let K := u.E
  have hv : ∃ v : Valuation K⟮a⟯ ℝ≥0,
      v.comap (algebraMap K K⟮a⟯) = u.v := by
    by_cases ha : IsAlgebraic K a
    · let : Algebra.IsAlgebraic K K⟮a⟯ :=
        IntermediateField.isAlgebraic_adjoin_simple ha.isIntegral
      exact exists_valuation_comap_eq_of_isAlgebraic u.v
    · obtain ⟨v, hv, _⟩ :=
        exists_valuation_adjoin_transcendental u.v ha 1 (by norm_num)
      exact ⟨v, hv⟩
  obtain ⟨v, hv⟩ := hv
  let E : IntermediateField F L := (K⟮a⟯).restrictScalars F
  have hbase : v.comap (algebraMap F E) = w := by
    ext x
    have hvx := congrArg (fun t : Valuation K ℝ≥0 => t (algebraMap F K x)) hv
    have hux := congrArg (fun t : Valuation F ℝ≥0 => t x) u.base
    simp only [Valuation.comap_apply] at hvx hux ⊢
    exact_mod_cast hvx.trans hux
  let v' : ValExtension F L w := ⟨E, v, hbase⟩
  refine ⟨v', ?_, ?_⟩
  · have hE : u.E ≤ E := by
      intro x hx
      change x ∈ K⟮a⟯
      simpa using (K⟮a⟯).algebraMap_mem (⟨x, hx⟩ : K)
    refine ⟨hE, ?_⟩
    intro x
    have hvx := congrArg (fun t : Valuation K ℝ≥0 => t x) hv
    convert hvx.symm using 1
    congr 1
  · exact IntermediateField.mem_adjoin_simple_self K a

/-! ### Extensions of valuations

Every `ℝ≥0`-valued valuation extends along every field extension. -/

/-- Every valuation `w : F → ℝ≥0` of a field extends to a valuation `v : L → ℝ≥0` of any field
extension: `v ∘ algebraMap F L = w`. Assembles the Gauss step of
`exists_valuation_adjoin_transcendental` [BGR84, Bosch, Güntzer, Remmert (1984), p. 43] and
the spectral step of `exists_valuation_comap_eq_of_isAlgebraic`
[BGR84, Bosch, Güntzer, Remmert (1984), §3.2.1, Theorem 2, pp. 134–136; §3.2.4,
Theorem 2, pp. 139–140] by Zorn's lemma. -/
theorem exists_valuation_comap_eq {F L : Type*} [Field F] [Field L] [Algebra F L]
    (w : Valuation F ℝ≥0) : ∃ v : Valuation L ℝ≥0, v.comap (algebraMap F L) = w := by
  classical
  obtain ⟨m, hm⟩ : ∃ m : ValExtension F L w, IsMax m :=
    zorn_le_nonempty (valExtension_chain_bound w)
  have htop : m.E = ⊤ := by
    apply top_unique
    intro a _
    by_contra ha
    obtain ⟨n, hmn, han⟩ := valExtension_adjoin w m a
    exact ha ((hm hmn).1 han)
  let e : m.E ≃ₐ[F] L :=
    (IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv
  let v : Valuation L ℝ≥0 := m.v.comap e.symm.toRingHom
  refine ⟨v, ?_⟩
  ext x
  have he : e.symm.toRingHom (algebraMap F L x) = algebraMap F m.E x := e.symm.commutes x
  have hb := congrArg (fun t : Valuation F ℝ≥0 => t x) m.base
  simp only [Valuation.comap_apply] at hb ⊢
  change (m.v (e.symm.toRingHom (algebraMap F L x)) : ℝ) = (w x : ℝ)
  rw [he]
  exact_mod_cast hb

/-! ### Algebraicity from valuations

A unit at every valuation above `p` is algebraic. -/

/-- An element of a field of characteristic zero that is a unit at every valuation
`v : L → ℝ≥0` with `v(p) < 1` is algebraic over `ℚ`: the step from
`pseudolatticeDilog_valuation_eq_one` to `pseudolatticeDilog_isAlgebraic`. -/
theorem isAlgebraic_of_forall_valuation_eq_one {L : Type*} [Field L] [CharZero L] (p : ℕ)
    [Fact p.Prime] {z : L} (h : ∀ v : Valuation L ℝ≥0, v (p : L) < 1 → v z = 1) :
    IsAlgebraic ℚ z := by
  classical
  by_contra hz
  let a := Rat.AbsoluteValue.padic p
  have hna : IsNonarchimedean a := by
    intro x y
    change (((padicNorm p (x + y) : ℚ) : ℝ) ≤
      max ((padicNorm p x : ℚ) : ℝ) ((padicNorm p y : ℚ) : ℝ))
    exact_mod_cast (padicNorm.nonarchimedean (p := p) (q := x) (r := y))
  let w := absoluteValuation a hna
  let t := w (p : ℚ)
  have ht_formula : t = Real.toNNReal ((padicNorm p (p : ℚ) : ℚ) : ℝ) := by
    simp [t, w, absoluteValuation_apply, a, Rat.AbsoluteValue.padic_eq_padicNorm]
  have ht_pos : 0 < t := by
    rw [ht_formula, Real.toNNReal_pos]
    rw [padicNorm.padicNorm_p_of_prime]
    have hp : (0 : ℚ) < p := by
      exact_mod_cast (lt_trans zero_lt_one (Nat.Prime.one_lt Fact.out))
    positivity
  have ht_lt : t < 1 := by
    rw [ht_formula, Real.toNNReal_lt_one]
    exact_mod_cast (padicNorm.padicNorm_p_lt_one_of_prime (p := p))
  obtain ⟨va, hbase, hgen⟩ := exists_valuation_adjoin_transcendental
    w hz t ht_pos
  obtain ⟨v, hv⟩ := exists_valuation_comap_eq (F := ℚ⟮z⟯) (L := L) va
  have hvz : v z = t := by
    have hve := congrArg (fun q : Valuation ℚ⟮z⟯ ℝ≥0 =>
      q (AdjoinSimple.gen ℚ z)) hv
    simpa only [Valuation.comap_apply, AdjoinSimple.algebraMap_gen] using hve.trans hgen
  have hvp : v (p : L) = t := by
    have hve := congrArg (fun q : Valuation ℚ⟮z⟯ ℝ≥0 =>
      q ((p : ℚ) : ℚ⟮z⟯)) hv
    have hpa := congrArg (fun q : Valuation ℚ ℝ≥0 => q (p : ℚ)) hbase
    simpa [t] using hve.trans hpa
  have hpv : v (p : L) < 1 := by calc
    v (p : L) = t := hvp
    _ < 1 := ht_lt
  have ht_eq : t = 1 := hvz.symm.trans (h v hpv)
  exact (ne_of_lt ht_lt) ht_eq

end SIC
