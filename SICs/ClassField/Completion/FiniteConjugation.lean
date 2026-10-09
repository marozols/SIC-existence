/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Completion.Norm
import SICs.ClassField.Completion.PlacesAbove

/-!
# Finite completions under isomorphisms of number fields

An isomorphism of number fields `σ : L ≃ L'` carries each finite place `w` of `L` to a finite
place `σ(w)` of `L'` and extends to an isomorphism of completions $L_w \cong L'_{\sigma(w)}$. When
`σ` is a `K`-algebra isomorphism, it permutes the primes above each finite place `v` of `K`, its
completion is a $K_v$-algebra isomorphism, and it preserves local norms. Conjugation also
preserves valuations, ideal multiplicities, and ramification indices.

This is the extension of `σ` to completions in Milne, *Class Field Theory*, version 4.03 (2020),
Chapter VII, §2, before Lemma 2.1, for an arbitrary isomorphism of number fields.

## The argument

The place `σ(w)` is the image of the prime `w` under the induced isomorphism of rings of
integers. Its valuation satisfies $v_{\sigma(w)}(\sigma x) = v_w(x)$, so `σ` is an isomorphism of
valued fields $(L, v_w) \cong (L', v_{\sigma(w)})$; it and its inverse are continuous and extend
to the uniform completions. On the dense subfield `L` the extension is `σ`, which gives the
composition, inverse, and identity laws by density. The extension preserves valuations, hence
integers and integral units.

When `σ` fixes `K`, the prime `σ(w)` lies over the same place `v` as `w`, and the extension of `σ`
agrees with the canonical completion maps from $K_v$ on the dense subfield `K`, hence everywhere.
It is therefore a $K_v$-algebra isomorphism $L_w \cong L'_{\sigma(w)}$, which preserves the
algebraic norm to $K_v$.

The second place is an explicit argument `w'` with a proof of `mapEquiv σ w = w'`, rather than
the expression `mapEquiv σ w`. Consumers then never transport elements of completions along
equalities of places.

In a tower, conjugation commutes with the maps on integer rings and preserves ramification
indices. Consequently it permutes the ramified finite places of a normal subextension.
-/

noncomputable section

open IsDedekindDomain NumberField WithZero Multiplicative
open scoped SIC.FinitePlace WithZeroTopology

namespace SIC

namespace FinitePlace

/-! ### Places under isomorphisms -/

section Places

variable {L L' L'' : Type*} [Field L] [Field L'] [Field L''] [NumberField L] [NumberField L']
  [NumberField L'']

/-- The bijection $w \mapsto \sigma(w)$ between the finite places of isomorphic number fields. -/
def mapEquiv (σ : L ≃+* L') : HeightOneSpectrum (𝓞 L) ≃ HeightOneSpectrum (𝓞 L') :=
  HeightOneSpectrum.equivOfRingEquiv (NumberField.RingOfIntegers.mapRingEquiv σ)

omit [NumberField L] [NumberField L'] in
/-- The prime ideal of the transported place is the image of its prime ideal. -/
theorem mapEquiv_asIdeal (σ : L ≃+* L') (w : HeightOneSpectrum (𝓞 L)) :
    (mapEquiv σ w).asIdeal = w.asIdeal.map (NumberField.RingOfIntegers.mapRingEquiv σ) := by
  change Ideal.comap (NumberField.RingOfIntegers.mapRingEquiv σ).symm w.asIdeal = _
  exact (Ideal.map_comap_of_equiv (NumberField.RingOfIntegers.mapRingEquiv σ)).symm

omit [NumberField L] [NumberField L'] in
/-- The inverse of $w \mapsto \sigma(w)$ is $w' \mapsto \sigma^{-1}(w')$. -/
@[simp]
theorem mapEquiv_symm (σ : L ≃+* L') : (mapEquiv σ).symm = mapEquiv σ.symm := by
  apply Equiv.ext
  intro w
  apply HeightOneSpectrum.ext
  rfl

omit [NumberField L] [NumberField L'] [NumberField L''] in
/-- The places of a composite isomorphism: $(\tau\sigma)(w) = \tau(\sigma(w))$. -/
theorem mapEquiv_trans (σ : L ≃+* L') (τ : L' ≃+* L'') (w : HeightOneSpectrum (𝓞 L)) :
    mapEquiv (σ.trans τ) w = mapEquiv τ (mapEquiv σ w) := by
  apply HeightOneSpectrum.ext
  rfl

omit [NumberField L] in
/-- The identity isomorphism fixes every finite place. -/
@[simp]
theorem mapEquiv_refl (w : HeightOneSpectrum (𝓞 L)) : mapEquiv (RingEquiv.refl L) w = w := by
  apply HeightOneSpectrum.ext
  rfl

omit [NumberField L] [NumberField L'] in
/-- A field isomorphism preserves multiplicities of ideals of the rings of integers;
used by `intValuation_mapEquiv`, `ramificationIdx_mapEquiv`, and `modulusExponent_map`. -/
theorem multiplicity_mapEquiv (σ : L ≃+* L') (I J : Ideal (𝓞 L)) :
    multiplicity (I.map (NumberField.RingOfIntegers.mapRingEquiv σ))
      (J.map (NumberField.RingOfIntegers.mapRingEquiv σ)) = multiplicity I J := by
  let e := NumberField.RingOfIntegers.mapRingEquiv σ
  let f : Ideal (𝓞 L) ≃* Ideal (𝓞 L') :=
    { e.idealComapOrderIso.symm.toEquiv with
      map_mul' := Ideal.map_mul e }
  exact multiplicity_map_eq f

/-- Restricting `σ` to integer rings preserves their prime ideal multiplicities and hence
their adic valuations; used in `valuation_mapEquiv`. -/
private theorem intValuation_mapEquiv (σ : L ≃+* L') (w : HeightOneSpectrum (𝓞 L))
    (r : 𝓞 L) :
    (mapEquiv σ w).intValuation (NumberField.RingOfIntegers.mapRingEquiv σ r) =
      w.intValuation r := by
  let e := NumberField.RingOfIntegers.mapRingEquiv σ
  by_cases hr : r = 0
  · subst r
    simp
  have hr' : e r ≠ 0 := by simpa using hr
  rw [(mapEquiv σ w).intValuation_eq_exp_neg_multiplicity hr',
    w.intValuation_eq_exp_neg_multiplicity hr]
  congr 1
  have hs : Ideal.span {e r} = (Ideal.span {r}).map e := by
    simp only [Ideal.map_span, Set.image_singleton]
  rw [mapEquiv_asIdeal, hs]
  rw [multiplicity_mapEquiv]

/-- The valuation at `σ(w)` of `σ x` is the valuation at `w` of `x`:
$v_{\sigma(w)}(\sigma x) = v_w(x)$. -/
theorem valuation_mapEquiv (σ : L ≃+* L') (w : HeightOneSpectrum (𝓞 L)) (x : L) :
    (mapEquiv σ w).valuation L' (σ x) = w.valuation L x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (𝓞 L) x
  rw [map_div₀ σ, Valuation.map_div, Valuation.map_div]
  rw [← NumberField.RingOfIntegers.mapRingEquiv_apply σ a,
    ← NumberField.RingOfIntegers.mapRingEquiv_apply σ b,
    HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap]
  rw [intValuation_mapEquiv, intValuation_mapEquiv]

end Places

/-! ### Completions under isomorphisms -/

section Completion

variable {L L' L'' : Type*} [Field L] [Field L'] [Field L''] [NumberField L] [NumberField L']
  [NumberField L''] (σ : L ≃+* L') (w : HeightOneSpectrum (𝓞 L))
  (w' : HeightOneSpectrum (𝓞 L')) (h : mapEquiv σ w = w')

/-- A ring isomorphism of fields that preserves valuations is continuous for the induced
valued topologies; used in `continuous_withValCongr`. -/
private theorem continuous_congr_of_valuation_eq {F F' : Type*} [Field F] [Field F']
    (v : Valuation F ℤᵐ⁰) (v' : Valuation F' ℤᵐ⁰) (e : F ≃+* F')
    (he : ∀ x, v' (e x) = v x) : Continuous (WithVal.congr v v' e) := by
  let f := WithVal.congr v v' e
  have hf (z : WithVal v) : (Valued.v (f z) : ℤᵐ⁰) = Valued.v z := he z.ofVal
  refine (uniformContinuous_of_continuousAt_zero f ?_).continuous
  simp_rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff
    (Valued.hasBasis_nhds_zero _ _), true_and, forall_const]
  intro γ
  obtain ⟨y, hy⟩ :=
    (MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective
      (.ofClass (Valued.v : Valuation (WithVal v') ℤᵐ⁰))) γ.1
  let x := f.symm y
  have hxy : (Valued.v x : ℤᵐ⁰) = Valued.v y := by
    simpa [x] using (hf (f.symm y)).symm
  have hy0 : (Valued.v y : ℤᵐ⁰) ≠ 0 := by
    intro hy0
    have h0 : Valued.v.restrict y = 0 :=
      ((Valued.v : Valuation (WithVal v') ℤᵐ⁰).restrict_eq_zero_iff).2 hy0
    exact γ.ne_zero (hy.symm.trans h0)
  have hx0 : Valued.v.restrict x ≠ 0 := by
    intro h0
    exact hy0 (hxy ▸ ((Valued.v : Valuation (WithVal v) ℤᵐ⁰).restrict_eq_zero_iff).1 h0)
  refine ⟨Units.mk0 (Valued.v.restrict x) hx0, ?_⟩
  intro z hz
  change Valued.v.restrict (f z) < γ.1
  rw [← hy]
  apply ((Valued.v : Valuation (WithVal v') ℤᵐ⁰).restrict_lt_iff).2
  have hz' : (Valued.v z : ℤᵐ⁰) < Valued.v x := by
    exact ((Valued.v : Valuation (WithVal v) ℤᵐ⁰).restrict_lt_iff).1 hz
  rw [hf z, ← hxy]
  exact hz'

include h in
/-- `σ` is continuous between `L` valued at `w` and `L'` valued at `σ(w)`; used by
`completionEquiv`. -/
theorem continuous_withValCongr :
    Continuous (WithVal.congr (w.valuation L) (w'.valuation L') σ) := by
  apply continuous_congr_of_valuation_eq
  intro x
  rw [← h]
  exact valuation_mapEquiv σ w x

include h in
/-- `σ⁻¹` is continuous between `L'` valued at `σ(w)` and `L` valued at `w`; used by
`completionEquiv`. -/
theorem continuous_withValCongr_symm :
    Continuous (WithVal.congr (w.valuation L) (w'.valuation L') σ).symm := by
  change Continuous (WithVal.congr (w'.valuation L') (w.valuation L) σ.symm)
  apply continuous_congr_of_valuation_eq
  intro x
  have heq : mapEquiv σ.symm w' = w := by
    rw [← h, ← mapEquiv_symm, Equiv.symm_apply_apply]
  rw [← heq]
  exact valuation_mapEquiv σ.symm w' x

/-- The isomorphism of completions $L_w \cong L'_{w'}$ extending `σ`, for $w' = \sigma(w)$.
Milne, *Class Field Theory*, Chapter VII, §2. -/
def completionEquiv : w.adicCompletion L ≃+* w'.adicCompletion L' :=
  ((HeightOneSpectrum.adicCompletion.equiv L w).trans
    (UniformSpace.Completion.mapRingEquiv _ (continuous_withValCongr σ w w' h)
      (continuous_withValCongr_symm σ w w' h))).trans
    (HeightOneSpectrum.adicCompletion.equiv L' w').symm

/-- The completion of `σ` is continuous. -/
theorem continuous_completionEquiv : Continuous (completionEquiv σ w w' h) := by
  exact (HeightOneSpectrum.adicCompletion.continuous_ofCompletion L' w').comp <|
    UniformSpace.Completion.continuous_map.comp
      (HeightOneSpectrum.adicCompletion.continuous_toCompletion L w)

/-- The completion of `σ` extends `σ`. -/
@[simp]
theorem completionEquiv_algebraMap (x : L) :
    completionEquiv σ w w' h (algebraMap L (w.adicCompletion L) x) =
      algebraMap L' (w'.adicCompletion L') (σ x) := by
  apply HeightOneSpectrum.adicCompletion.ext
  change (UniformSpace.Completion.mapRingHom
    (WithVal.congr (w.valuation L) (w'.valuation L') σ).toRingHom
    (continuous_withValCongr σ w w' h)) (x : (w.valuation L).Completion) =
      (σ x : (w'.valuation L').Completion)
  exact UniformSpace.Completion.mapRingHom_coe _ _

/-- The inverse of the completion of `σ` is the completion of `σ⁻¹`. -/
theorem completionEquiv_symm :
    (completionEquiv σ w w' h).symm =
      completionEquiv σ.symm w' w (by rw [← h, ← mapEquiv_symm, Equiv.symm_apply_apply]) := by
  rfl

/-- The completions of `σ` and `τ` compose to the completion of `τ ∘ σ`. -/
theorem completionEquiv_trans (τ : L' ≃+* L'') (w'' : HeightOneSpectrum (𝓞 L''))
    (h' : mapEquiv τ w' = w'') :
    (completionEquiv σ w w' h).trans (completionEquiv τ w' w'' h') =
      completionEquiv (σ.trans τ) w w'' (by rw [mapEquiv_trans, h, h']) := by
  apply RingEquiv.ext
  intro x
  have heq :
      (fun y : w.adicCompletion L =>
        completionEquiv τ w' w'' h' (completionEquiv σ w w' h y)) =
      (fun y => completionEquiv (σ.trans τ) w w'' (by rw [mapEquiv_trans, h, h']) y) := by
    apply SIC.FinitePlace.funext_completion w
    · exact (continuous_completionEquiv τ w' w'' h').comp
        (continuous_completionEquiv σ w w' h)
    · exact continuous_completionEquiv (σ.trans τ) w w'' _
    · intro a
      simp only [completionEquiv_algebraMap]
      rfl
  exact congrFun heq x

/-- The completion of the identity is the identity. -/
@[simp]
theorem completionEquiv_refl :
    completionEquiv (RingEquiv.refl L) w w (mapEquiv_refl w) = RingEquiv.refl _ := by
  apply RingEquiv.ext
  intro x
  have heq :
      (fun y : w.adicCompletion L =>
        completionEquiv (RingEquiv.refl L) w w (mapEquiv_refl w) y) = id := by
    apply SIC.FinitePlace.funext_completion w
    · exact continuous_completionEquiv (RingEquiv.refl L) w w _
    · exact continuous_id
    · intro a
      simp only [completionEquiv_algebraMap, RingEquiv.refl_apply,
        id_eq]
  exact congrFun heq x

/-- The completion of `σ` preserves valuations. -/
@[simp]
theorem valued_completionEquiv (x : w.adicCompletion L) :
    Valued.v (completionEquiv σ w w' h x) = Valued.v x := by
  have hv : Continuous (Valued.v : w.adicCompletion L → ℤᵐ⁰) :=
    Valued.continuous_valuation_of_surjective
      (HeightOneSpectrum.valuedAdicCompletion_surjective L w)
  have hv' : Continuous (Valued.v : w'.adicCompletion L' → ℤᵐ⁰) :=
    Valued.continuous_valuation_of_surjective
      (HeightOneSpectrum.valuedAdicCompletion_surjective L' w')
  have heq :
      (fun y : w.adicCompletion L =>
        (Valued.v (completionEquiv σ w w' h y) : ℤᵐ⁰)) =
      (fun y => (Valued.v y : ℤᵐ⁰)) := by
    apply SIC.FinitePlace.funext_completion w
    · exact hv'.comp (continuous_completionEquiv σ w w' h)
    · exact hv
    · intro a
      simp only [completionEquiv_algebraMap]
      change Valued.v (σ a : w'.adicCompletion L') = Valued.v (a : w.adicCompletion L)
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      rw [← h]
      exact valuation_mapEquiv σ w a
  exact congrFun heq x

/-- The completion of `σ` maps integral units to integral units. -/
theorem units_map_completionEquiv_mem {x : (w.adicCompletion L)ˣ}
    (hx : x ∈ (Submonoid.ofClass (w.adicCompletionIntegers L)).units) :
    Units.map (completionEquiv σ w w' h : w.adicCompletion L →* w'.adicCompletion L') x ∈
      (Submonoid.ofClass (w'.adicCompletionIntegers L')).units := by
  apply HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr
  rw [Units.coe_map]
  change Valued.v (completionEquiv σ w w' h (x : w.adicCompletion L)) = 1
  rw [valued_completionEquiv]
  exact HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hx

end Completion

/-! ### Isomorphisms over a base field -/

section Algebra

variable {K L L' : Type*} [Field K] [Field L] [Field L'] [NumberField K] [NumberField L]
  [NumberField L'] [Algebra K L] [Algebra K L'] (σ : L ≃ₐ[K] L')
  (v : HeightOneSpectrum (𝓞 K))

omit [NumberField K] [NumberField L] [NumberField L'] in
/-- A `K`-isomorphism carries a prime above `v` to a prime above `v`. -/
theorem liesOver_mapEquiv (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] :
    (mapEquiv σ.toRingEquiv w).asIdeal.LiesOver v.asIdeal := by
  exact Ideal.LiesOver.of_eq_map_equiv v.asIdeal
    (NumberField.RingOfIntegers.mapAlgEquiv σ) (mapEquiv_asIdeal σ.toRingEquiv w)

/-- A `K`-isomorphism permutes the primes above `v`: $w \mapsto \sigma(w)$. -/
def PrimeAbove.mapEquiv : PrimeAbove (L := L) v ≃ PrimeAbove (L := L') v where
  toFun w :=
    haveI := liesOver_mapEquiv σ v (PrimeAbove.place v w)
    PrimeAbove.mk v (FinitePlace.mapEquiv σ.toRingEquiv (PrimeAbove.place v w))
  invFun w' :=
    haveI := liesOver_mapEquiv σ.symm v (PrimeAbove.place v w')
    PrimeAbove.mk v (FinitePlace.mapEquiv σ.symm.toRingEquiv (PrimeAbove.place v w'))
  left_inv w := by
    apply (PrimeAbove.place_injective v)
    simpa only [PrimeAbove.place_mk, AlgEquiv.symm_toRingEquiv, ← mapEquiv_symm] using
      (FinitePlace.mapEquiv σ.toRingEquiv).symm_apply_apply (PrimeAbove.place v w)
  right_inv w' := by
    apply (PrimeAbove.place_injective v)
    simpa only [PrimeAbove.place_mk, AlgEquiv.symm_toRingEquiv, ← mapEquiv_symm] using
      (FinitePlace.mapEquiv σ.toRingEquiv).apply_symm_apply (PrimeAbove.place v w')

variable (w : HeightOneSpectrum (𝓞 L)) (w' : HeightOneSpectrum (𝓞 L'))
  [w.asIdeal.LiesOver v.asIdeal] [w'.asIdeal.LiesOver v.asIdeal]
  (h : FinitePlace.mapEquiv σ.toRingEquiv w = w')

/-- The completion of a `K`-isomorphism is compatible with the completion maps from $K_v$. -/
@[simp]
theorem completionEquiv_completionMap (a : v.adicCompletion K) :
    completionEquiv σ.toRingEquiv w w' h (completionMap v w a) = completionMap v w' a := by
  have heq :
      (fun y : v.adicCompletion K =>
        completionEquiv σ.toRingEquiv w w' h (completionMap v w y)) =
      (fun y => completionMap v w' y) := by
    apply SIC.FinitePlace.funext_completion v
    · exact (continuous_completionEquiv σ.toRingEquiv w w' h).comp
        (continuous_completionMap v w)
    · exact continuous_completionMap v w'
    · intro x
      simp only [completionMap_algebraMap,
        completionEquiv_algebraMap]
      exact congrArg (algebraMap L' (w'.adicCompletion L')) (σ.commutes x)
  exact congrFun heq a

/-- The completion of a `K`-isomorphism as a $K_v$-algebra isomorphism $L_w \cong L'_{w'}$. -/
def completionAlgEquiv : w.adicCompletion L ≃ₐ[v.adicCompletion K] w'.adicCompletion L' :=
  AlgEquiv.ofRingEquiv (f := completionEquiv σ.toRingEquiv w w' h)
    (completionEquiv_completionMap σ v w w' h)

/-- The completion of a `K`-isomorphism preserves local norms:
$N_{L'_{\sigma(w)}/K_v}(\sigma x) = N_{L_w/K_v}(x)$. -/
@[simp]
theorem localNorm_completionEquiv (x : (w.adicCompletion L)ˣ) :
    localNorm v w'
        (Units.map (completionEquiv σ.toRingEquiv w w' h :
          w.adicCompletion L →* w'.adicCompletion L') x) =
      localNorm v w x := by
  apply Units.ext
  rw [localNorm_val, localNorm_val, Units.coe_map]
  exact Algebra.norm_eq_of_algEquiv (completionAlgEquiv σ v w w' h) x

end Algebra

/-! ### The Galois action on finite places

The automorphisms of `L` over `K` act on the finite places of `L` by $w \mapsto \sigma(w)$, and
permute the primes above each finite place of `K`. -/

section Action

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The automorphisms of `L` over `K` act on the finite places of `L` by
$\sigma \cdot w = \sigma(w)$. Milne, *Class Field Theory*, Chapter VII, §2. -/
instance instMulActionHeightOneSpectrum : MulAction (L ≃ₐ[K] L) (HeightOneSpectrum (𝓞 L)) where
  smul σ w := mapEquiv σ.toRingEquiv w
  one_smul w := by
    apply HeightOneSpectrum.ext
    rfl
  mul_smul σ τ w := by
    apply HeightOneSpectrum.ext
    rfl

/-- The Galois action on finite places is `mapEquiv`. -/
theorem smul_def (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    σ • w = mapEquiv σ.toRingEquiv w :=
  rfl

open scoped Pointwise in
/-- Passing from a finite place to its prime ideal commutes with the Galois action. -/
@[simp] theorem asIdeal_smul (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    (σ • w).asIdeal = σ • w.asIdeal := by
  rw [smul_def, mapEquiv_asIdeal, Ideal.pointwise_smul_def]
  rfl

open scoped Pointwise in
/-- The stabilizer of a finite place is the stabilizer of its prime ideal under Mathlib's
pointwise action, so the decomposition group $D_w$ is Mathlib's stabilizer of `w.asIdeal`. -/
theorem stabilizer_eq_stabilizer_asIdeal (w : HeightOneSpectrum (𝓞 L)) :
    MulAction.stabilizer (L ≃ₐ[K] L) w = MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal := by
  ext σ
  simp only [MulAction.mem_stabilizer_iff, HeightOneSpectrum.ext_iff, asIdeal_smul]

/-- An automorphism over `K` carries a prime above `v` to a prime above `v`. -/
instance liesOver_smul (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L)
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] :
    (σ • w).asIdeal.LiesOver v.asIdeal :=
  liesOver_mapEquiv σ v w

/-- The completion of a product of automorphisms is the composite of the completions:
$(\sigma\tau)_{w \to w''} = \sigma_{w' \to w''} \circ \tau_{w \to w'}$. -/
theorem completionEquiv_mul [NumberField L] (σ τ : L ≃ₐ[K] L)
    {w w' w'' : HeightOneSpectrum (𝓞 L)} (hτ : τ • w = w') (hσ : σ • w' = w'')
    (y : w.adicCompletion L) :
    completionEquiv (σ * τ).toRingEquiv w w'' (by rw [← smul_def, mul_smul, hτ, hσ]) y =
      completionEquiv σ.toRingEquiv w' w'' hσ (completionEquiv τ.toRingEquiv w w' hτ y) := by
  have heq := completionEquiv_trans τ.toRingEquiv w w' hτ σ.toRingEquiv w'' hσ
  have hmul : (σ * τ).toRingEquiv = τ.toRingEquiv.trans σ.toRingEquiv := by
    ext a
    rfl
  simpa only [hmul, RingEquiv.trans_apply] using
    congrArg (fun e : w.adicCompletion L ≃+* w''.adicCompletion L ↦ e y) heq.symm

variable [NumberField K] [NumberField L] (v : HeightOneSpectrum (𝓞 K))

/-- Galois automorphisms act on primes above `v` through `mapEquiv`. This action deliberately
shadows Mathlib's two `primesOver` actions and is not definitionally equal to either; Mathlib's
`primesOver` lemmas about `σ • w` therefore do not apply to this instance. -/
instance PrimeAbove.mulAction : MulAction (L ≃ₐ[K] L) (PrimeAbove (L := L) v) where
  smul σ w := PrimeAbove.mapEquiv σ v w
  one_smul w := by
    apply PrimeAbove.place_injective v
    change FinitePlace.mapEquiv (1 : L ≃ₐ[K] L).toRingEquiv
      (PrimeAbove.place v w) = _
    exact mapEquiv_refl (PrimeAbove.place v w)
  mul_smul σ τ w := by
    apply PrimeAbove.place_injective v
    change FinitePlace.mapEquiv (σ * τ).toRingEquiv (PrimeAbove.place v w) =
      FinitePlace.mapEquiv σ.toRingEquiv
        (FinitePlace.mapEquiv τ.toRingEquiv (PrimeAbove.place v w))
    exact mapEquiv_trans τ.toRingEquiv σ.toRingEquiv (PrimeAbove.place v w)

omit [NumberField K] [NumberField L] in
/-- The action on primes above `v` agrees with the action on their underlying places. -/
theorem PrimeAbove.place_smul (σ : L ≃ₐ[K] L) (w : PrimeAbove (L := L) v) :
    PrimeAbove.place v (σ • w) = σ • PrimeAbove.place v w := by
  rfl
attribute [simp] PrimeAbove.place_smul

omit [NumberField K] [NumberField L] in
/-- If an automorphism carries `w` to `w'`, its `mapEquiv` carries the underlying place to the
underlying place of `w'`. Used by the idèle fiber and valuation arguments. -/
theorem PrimeAbove.mapEquiv_place_eq_of_smul_eq (σ : L ≃ₐ[K] L)
    (w w' : PrimeAbove (L := L) v) (h : σ • w = w') :
    FinitePlace.mapEquiv σ.toRingEquiv (PrimeAbove.place v w) = PrimeAbove.place v w' := by
  simpa only [PrimeAbove.place_smul, smul_def] using congrArg (PrimeAbove.place v) h

end Action

/-! ### Ramified places under conjugation

An automorphism `τ` of `L` over `F` restricts to an automorphism `σ` of a normal subextension
`E`; it carries the primes of `L` above `v` to those above $\sigma(v)$ and preserves their
ramification indices, so `σ` permutes the places of `E` that ramify in `L`. -/

section Ramification

variable {F E L : Type*} [Field F] [Field E] [Field L]
  [Algebra F E] [Algebra E L] [Algebra F L] [IsScalarTower F E L] [Normal F E]

/-- If $\sigma=\tau|_E$, then $\tau$ and $\sigma$ commute with the inclusion
$\mathcal O_E\to\mathcal O_L$. Used by `extendedPrime_mapEquiv`. -/
theorem integers_restrictNormal_commutes (τ : L ≃ₐ[F] L) :
    (NumberField.RingOfIntegers.mapRingEquiv τ.toRingEquiv).toRingHom.comp
        (algebraMap (𝓞 E) (𝓞 L)) =
      (algebraMap (𝓞 E) (𝓞 L)).comp
        (NumberField.RingOfIntegers.mapRingEquiv
          (τ.restrictNormal E).toRingEquiv).toRingHom := by
  ext x
  change τ (algebraMap E L (x : E)) =
    algebraMap E L ((τ.restrictNormal E) (x : E))
  exact (AlgEquiv.restrictNormal_commutes τ E (x : E)).symm

/-- The inverse maps of $\tau$ and $\sigma=\tau|_E$ commute with the inclusion of integer
rings; used by `below_mapEquiv_restrictNormal`. -/
theorem integers_restrictNormal_commutes_symm (τ : L ≃ₐ[F] L) :
    (NumberField.RingOfIntegers.mapRingEquiv τ.toRingEquiv).symm.toRingHom.comp
        (algebraMap (𝓞 E) (𝓞 L)) =
      (algebraMap (𝓞 E) (𝓞 L)).comp
        (NumberField.RingOfIntegers.mapRingEquiv
          (τ.restrictNormal E).toRingEquiv).symm.toRingHom := by
  ext x
  change τ.symm (algebraMap E L (x : E)) =
    algebraMap E L ((τ.restrictNormal E).symm (x : E))
  apply τ.injective
  rw [τ.apply_symm_apply, ← AlgEquiv.restrictNormal_commutes τ E,
    AlgEquiv.apply_symm_apply]

/-- For $\sigma=\tau|_E$, the place below $\tau(w)$ is $\sigma(v)$ when $v$ lies below $w$. -/
theorem below_mapEquiv_restrictNormal (τ : L ≃ₐ[F] L)
    (w : HeightOneSpectrum (𝓞 L)) :
    below (K := E) (mapEquiv τ.toRingEquiv w) =
      mapEquiv (τ.restrictNormal E).toRingEquiv (below (K := E) w) := by
  let eL := NumberField.RingOfIntegers.mapRingEquiv τ.toRingEquiv
  let eE := NumberField.RingOfIntegers.mapRingEquiv (τ.restrictNormal E).toRingEquiv
  have hs : eL.symm.toRingHom.comp (algebraMap (𝓞 E) (𝓞 L)) =
      (algebraMap (𝓞 E) (𝓞 L)).comp eE.symm.toRingHom :=
    integers_restrictNormal_commutes_symm τ
  apply HeightOneSpectrum.ext
  rw [mapEquiv_asIdeal]
  change ((mapEquiv τ.toRingEquiv w).asIdeal).comap (algebraMap (𝓞 E) (𝓞 L)) =
    (w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 L))).map eE
  rw [mapEquiv_asIdeal]
  change (w.asIdeal.map (eL : 𝓞 L →+* 𝓞 L)).comap
      (algebraMap (𝓞 E) (𝓞 L)) =
    (w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 L))).map
      (eE : 𝓞 E →+* 𝓞 E)
  rw [Ideal.map_comap_of_equiv eL, Ideal.map_comap_of_equiv eE]
  change Ideal.comap (algebraMap (𝓞 E) (𝓞 L))
      (Ideal.comap eL.symm.toRingHom w.asIdeal) =
    Ideal.comap eE.symm.toRingHom
      (Ideal.comap (algebraMap (𝓞 E) (𝓞 L)) w.asIdeal)
  rw [Ideal.comap_comap, Ideal.comap_comap, hs]

/-- For $\sigma=\tau|_E$, extension of $\sigma(v)$ to $\mathcal O_L$ is the conjugate of
the extension of $v$. Used by `ramificationIdx_mapEquiv`. -/
theorem extendedPrime_mapEquiv (τ : L ≃ₐ[F] L)
    (v : HeightOneSpectrum (𝓞 E)) :
    ((mapEquiv (τ.restrictNormal E).toRingEquiv v).asIdeal).map
        (algebraMap (𝓞 E) (𝓞 L)) =
      (v.asIdeal.map (algebraMap (𝓞 E) (𝓞 L))).map
        (NumberField.RingOfIntegers.mapRingEquiv τ.toRingEquiv) := by
  let eE := NumberField.RingOfIntegers.mapRingEquiv (τ.restrictNormal E).toRingEquiv
  let eL := NumberField.RingOfIntegers.mapRingEquiv τ.toRingEquiv
  rw [mapEquiv_asIdeal]
  change Ideal.map (algebraMap (𝓞 E) (𝓞 L))
      (Ideal.map eE.toRingHom v.asIdeal) =
    Ideal.map eL.toRingHom
      (Ideal.map (algebraMap (𝓞 E) (𝓞 L)) v.asIdeal)
  rw [Ideal.map_map, Ideal.map_map, ← integers_restrictNormal_commutes τ]

variable [NumberField L]

/-- Conjugation preserves the ramification index of $w$ over $E$:
$e(\tau w/E)=e(w/E)$. Used by `mapEquiv_mem_ramifiedSet_iff` and Artin conjugation. -/
theorem ramificationIdx_mapEquiv (τ : L ≃ₐ[F] L)
    (w : HeightOneSpectrum (𝓞 L)) :
    (mapEquiv τ.toRingEquiv w).asIdeal.ramificationIdx (𝓞 E) =
      w.asIdeal.ramificationIdx (𝓞 E) := by
  let v := below (K := E) w
  let σ := τ.restrictNormal E
  let eL := NumberField.RingOfIntegers.mapRingEquiv τ.toRingEquiv
  have hover : (mapEquiv τ.toRingEquiv w).asIdeal.LiesOver
      (mapEquiv σ.toRingEquiv v).asIdeal := by
    constructor
    exact (congrArg HeightOneSpectrum.asIdeal
      (below_mapEquiv_restrictNormal τ w)).symm
  have hp : v.asIdeal.map (algebraMap (𝓞 E) (𝓞 L)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot v.ne_bot
  have hp' : (mapEquiv σ.toRingEquiv v).asIdeal.map
      (algebraMap (𝓞 E) (𝓞 L)) ≠ ⊥ := by
    rw [extendedPrime_mapEquiv]
    exact fun h ↦ hp ((Ideal.map_eq_bot_iff_of_injective eL.injective).mp h)
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity _ _ hp',
    Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity _ _ hp,
    extendedPrime_mapEquiv, mapEquiv_asIdeal]
  exact multiplicity_mapEquiv τ.toRingEquiv w.asIdeal
    (v.asIdeal.map (algebraMap (𝓞 E) (𝓞 L)))

variable [NumberField E]

/-- Conjugation permutes the ramified places: for $\tau \in \operatorname{Aut}(L/F)$ with
restriction $\sigma$ to a normal subextension `E`, $\sigma(v)$ ramifies in `L` exactly when `v`
does. -/
theorem mapEquiv_mem_ramifiedSet_iff (τ : L ≃ₐ[F] L) (v : HeightOneSpectrum (𝓞 E)) :
    mapEquiv (τ.restrictNormal E).toRingEquiv v ∈ ramifiedSet E L ↔ v ∈ ramifiedSet E L := by
  constructor
  · intro hv
    obtain ⟨w', hw', hram⟩ := mem_ramifiedSet.mp hv
    let w := (mapEquiv τ.toRingEquiv).symm w'
    have hmap : mapEquiv τ.toRingEquiv w = w' := Equiv.apply_symm_apply _ _
    have hbelow : below (K := E) w = v := by
      apply (mapEquiv (τ.restrictNormal E).toRingEquiv).injective
      rw [← below_mapEquiv_restrictNormal τ w, hmap, hw']
    have hr : w.asIdeal.ramificationIdx (𝓞 E) ≠ 1 := by
      rw [← ramificationIdx_mapEquiv τ w, hmap]
      exact hram
    exact mem_ramifiedSet.mpr ⟨w, hbelow, hr⟩
  · intro hv
    obtain ⟨w, hw, hram⟩ := mem_ramifiedSet.mp hv
    apply mem_ramifiedSet.mpr
    refine ⟨mapEquiv τ.toRingEquiv w, ?_, ?_⟩
    · rw [below_mapEquiv_restrictNormal τ w, hw]
    · rw [ramificationIdx_mapEquiv]
      exact hram

end Ramification

end FinitePlace

end SIC
