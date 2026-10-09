/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Ideles.Inclusion
import SICs.ClassField.Ideles.IdealMap
import SICs.ClassField.Completion.FiniteDecomposition
import SICs.ClassField.Completion.InfiniteDecomposition

/-!
# Idèles under isomorphisms of number fields and the Galois action

An isomorphism of number fields `σ : L ≃ L'` induces a continuous isomorphism of idèle groups
$I_L \cong I_{L'}$ and an isomorphism of idèle class groups $C_L \cong C_{L'}$; for
`K`-isomorphisms it commutes with the inclusion of $I_K$ and preserves the norm to $I_K$. The
automorphisms of `L` over `K` therefore act on $I_L$ and $C_L$, the norm is invariant under this
action, and for Galois `L/K` the included norm is the product of the conjugates,
$i(N_{L/K} x) = \prod_{\sigma} \sigma x$. The principal embedding commutes with these actions,
and the quotient map is an equivariant homomorphism.
The fractional ideal of an idèle moves by the same field isomorphism.

This is the action of $\operatorname{Gal}(L/K)$ on $I_L$ in Milne, *Class Field Theory*, version
4.03 (2020), Chapter VII, §2, Lemma 2.1 and the paragraph before Proposition 2.5: if an idèle has
$a_w$ at `w`, its image under `σ` has $\sigma a_w$ at $\sigma w$; the product formula is the
paragraph "The norm map on idèles" of the same section.

## The argument

The image of an idèle `x` has component $\sigma(x_{\sigma^{-1} w'})$ at a place `w'` of `L'`,
where $\sigma : L_w \to L'_{\sigma(w)}$ is the completion of `σ` of
`SICs.ClassField.Completion.FiniteConjugation` and `SICs.ClassField.Completion.InfiniteConjugation`.
Completions of `σ` preserve integral units and `σ` permutes the finite places, so the finite part
is a restricted-product map; it is continuous because each completion of `σ` is. The composition
and inverse laws of the local completions give $(\tau\sigma)_* = \tau_* \sigma_*$ and
$(\sigma^{-1})_* = (\sigma_*)^{-1}$, and on a principal idèle every component is the image of
$\sigma x$. Principal idèles therefore correspond, and the isomorphism descends to idèle classes;
the quotient map is then equivariant (`mkHom`).

For a `K`-isomorphism, `σ` permutes the places above each place `v` of `K`, its completions are
$K_v$-algebra isomorphisms, and so the component at `v` of the norm,
$\prod_{w' \mid v} N_{L'_{w'}/K_v}(\sigma x_{\sigma^{-1} w'}) = \prod_{w \mid v} N_{L_w/K_v}(x_w)$,
is unchanged after reindexing by $w' = \sigma w$. An included idèle has component $x_v$ at every
`w` above `v`, and the completion of `σ` fixes $K_v$, so inclusions are fixed.

For Galois `L/K`, the automorphisms carrying a place `w'` above `v` to `w` form a coset of the
decomposition group of `w'`, and they multiply on $x_{w'}$ to its local norm
(`SICs.ClassField.Completion.FiniteDecomposition`,
`SICs.ClassField.Completion.InfiniteDecomposition`). Grouping $\prod_\sigma \sigma(x_{\sigma^{-1}
w})$ by $w' = \sigma^{-1} w$ gives the component at `w` of the included norm. At finite places,
valuation preservation also identifies the fractional ideal of the transported idèle with the
transported fractional ideal.
-/

noncomputable section

open Filter IsDedekindDomain NumberField
open scoped NumberField NumberField.AdeleRing NumberField.LiesOver RestrictedProduct nonZeroDivisors
  SIC.FinitePlace SIC.InfinitePlace

namespace SIC

namespace IdeleGroup

variable {L L' L'' : Type*} [Field L] [Field L'] [Field L''] [NumberField L] [NumberField L']
  [NumberField L'']

/-! ### Isomorphisms of idèle groups -/

-- The local maps are passed as `(f : A →+* B).toMonoidHom`: with the coercion `(f : A →* B)`,
-- elaborating `RestrictedProduct.mapAlongMonoidHom` times out in `isDefEq`.
/-- The finite part of the idèle isomorphism, $x \mapsto (\sigma x_{\sigma^{-1} w'})_{w'}$. -/
private def finiteCongrHom (σ : L ≃+* L') : FiniteLocalIdele L →* FiniteLocalIdele L' :=
  RestrictedProduct.mapAlongMonoidHom
    (fun w : HeightOneSpectrum (𝓞 L) ↦ (w.adicCompletion L)ˣ)
    (fun w' : HeightOneSpectrum (𝓞 L') ↦ (w'.adicCompletion L')ˣ)
    (FinitePlace.mapEquiv σ).symm (FinitePlace.mapEquiv σ).symm.injective.tendsto_cofinite
    (fun w' ↦ Units.map (FinitePlace.completionEquiv σ ((FinitePlace.mapEquiv σ).symm w') w'
      (Equiv.apply_symm_apply _ _)).toMonoidHom)
    (Filter.Eventually.of_forall fun w' _ hx ↦
      FinitePlace.units_map_completionEquiv_mem σ _ w' (Equiv.apply_symm_apply _ _) hx)

/-- Continuity of the finite part used by `continuous_congrHom`. -/
private theorem continuous_finiteCongrHom (σ : L ≃+* L') :
    Continuous (finiteCongrHom σ) := by
  unfold finiteCongrHom
  apply RestrictedProduct.mapAlong_continuous
  · exact (FinitePlace.mapEquiv σ).symm.injective.tendsto_cofinite
  · exact Filter.Eventually.of_forall fun w' _ hx ↦
      FinitePlace.units_map_completionEquiv_mem σ _ w' (Equiv.apply_symm_apply _ _) hx
  · intro w'
    exact Units.continuous_map
      (FinitePlace.continuous_completionEquiv σ _ w' (Equiv.apply_symm_apply _ _))

/-- The infinite part of the idèle isomorphism, $x \mapsto (\sigma x_{\sigma^{-1} w'})_{w'}$. -/
private def infiniteCongrHom (σ : L ≃+* L') : InfiniteLocalIdele L →* InfiniteLocalIdele L' :=
  MonoidHom.pi fun w' ↦
    (Units.map (InfinitePlace.completionEquiv σ ((InfinitePlace.mapEquiv σ).symm w') w'
      (Equiv.apply_symm_apply _ _)).toMonoidHom).comp
      (Pi.evalMonoidHom _ ((InfinitePlace.mapEquiv σ).symm w'))

/-- The idèle homomorphism underlying `congr`. -/
private def congrHom (σ : L ≃+* L') :
    NumberField.IdeleGroup (𝓞 L) L →* NumberField.IdeleGroup (𝓞 L') L' :=
  mapComponents (infiniteCongrHom σ) (finiteCongrHom σ)

/-- The finite component formula used to construct `congr`. -/
private theorem finiteComponent_congrHom (σ : L ≃+* L')
    (w : HeightOneSpectrum (𝓞 L)) (w' : HeightOneSpectrum (𝓞 L'))
    (h : FinitePlace.mapEquiv σ w = w') (x : NumberField.IdeleGroup (𝓞 L) L) :
    finiteComponent L' w' (congrHom σ x) =
      Units.map (FinitePlace.completionEquiv σ w w' h :
        w.adicCompletion L →* w'.adicCompletion L')
        (finiteComponent L w x) := by
  subst w'
  change finiteComponent L' (FinitePlace.mapEquiv σ w)
    (mapComponents (infiniteCongrHom σ) (finiteCongrHom σ) x) = _
  rw [finiteComponent_mapComponents]
  change ((finiteCongrHom σ) (componentsContinuousEquiv L x).2)
    (FinitePlace.mapEquiv σ w) = _
  simp only [finiteCongrHom, RestrictedProduct.mapAlongMonoidHom_apply]
  have aux (u : HeightOneSpectrum (𝓞 L))
      (hu : FinitePlace.mapEquiv σ u = FinitePlace.mapEquiv σ w) (e : u = w) :
      (Units.map (FinitePlace.completionEquiv σ u _ hu).toMonoidHom)
        ((componentsContinuousEquiv L x).2 u) =
      Units.map (FinitePlace.completionEquiv σ w _ rfl :
        w.adicCompletion L →* (FinitePlace.mapEquiv σ w).adicCompletion L')
        (finiteComponent L w x) := by
    subst u
    rfl
  exact aux _ (Equiv.apply_symm_apply _ _) (Equiv.symm_apply_apply _ _)

/-- The infinite component formula used to construct `congr`. -/
private theorem infiniteComponent_congrHom (σ : L ≃+* L')
    (w : InfinitePlace L) (w' : InfinitePlace L')
    (h : InfinitePlace.mapEquiv σ w = w')
    (x : NumberField.IdeleGroup (𝓞 L) L) :
    infiniteComponent L' w' (congrHom σ x) =
      Units.map (InfinitePlace.completionEquiv σ w w' h :
        w.Completion →* w'.Completion)
        (infiniteComponent L w x) := by
  subst w'
  change infiniteComponent L' (InfinitePlace.mapEquiv σ w)
    (mapComponents (infiniteCongrHom σ) (finiteCongrHom σ) x) = _
  rw [infiniteComponent_mapComponents]
  change ((infiniteCongrHom σ) (componentsContinuousEquiv L x).1)
    (InfinitePlace.mapEquiv σ w) = _
  change Units.map (InfinitePlace.completionEquiv σ
    ((InfinitePlace.mapEquiv σ).symm (InfinitePlace.mapEquiv σ w))
    (InfinitePlace.mapEquiv σ w) (Equiv.apply_symm_apply _ _)).toMonoidHom
    ((componentsContinuousEquiv L x).1
      ((InfinitePlace.mapEquiv σ).symm (InfinitePlace.mapEquiv σ w))) = _
  have aux (u : InfinitePlace L)
      (hu : InfinitePlace.mapEquiv σ u = InfinitePlace.mapEquiv σ w) (e : u = w) :
      (Units.map (InfinitePlace.completionEquiv σ u _ hu).toMonoidHom)
        ((componentsContinuousEquiv L x).1 u) =
      Units.map (InfinitePlace.completionEquiv σ w _ rfl :
        w.Completion →* (InfinitePlace.mapEquiv σ w).Completion)
        (infiniteComponent L w x) := by
    subst u
    rfl
  exact aux _ (Equiv.apply_symm_apply _ _) (Equiv.symm_apply_apply _ _)

/-- Continuity of the componentwise idèle map used by `congr`. -/
private theorem continuous_congrHom (σ : L ≃+* L') : Continuous (congrHom σ) := by
  have hinfinite : Continuous (infiniteCongrHom σ) := by
    apply continuous_pi
    intro w'
    exact (Units.continuous_map
      (InfinitePlace.isometry_completionEquiv σ _ w' (Equiv.apply_symm_apply _ _)).continuous).comp
      (continuous_apply _)
  exact continuous_mapComponents hinfinite (continuous_finiteCongrHom σ)

/-- The componentwise idèle maps of inverse field isomorphisms are inverse. -/
private theorem congrHom_left_inv (σ : L ≃+* L') (x : NumberField.IdeleGroup (𝓞 L) L) :
    congrHom σ.symm (congrHom σ x) = x := by
  apply ext L
  · intro w
    have hw : InfinitePlace.mapEquiv σ.symm (InfinitePlace.mapEquiv σ w) = w := by
      rw [← InfinitePlace.mapEquiv_symm]
      exact Equiv.symm_apply_apply _ _
    rw [infiniteComponent_congrHom σ.symm (InfinitePlace.mapEquiv σ w) w hw,
      infiniteComponent_congrHom σ w (InfinitePlace.mapEquiv σ w) rfl]
    rw [← InfinitePlace.completionEquiv_symm σ w (InfinitePlace.mapEquiv σ w) rfl]
    apply Units.ext
    exact (InfinitePlace.completionEquiv σ w (InfinitePlace.mapEquiv σ w) rfl).symm_apply_apply _
  · intro w
    have hw : FinitePlace.mapEquiv σ.symm (FinitePlace.mapEquiv σ w) = w := by
      rw [← FinitePlace.mapEquiv_symm]
      exact Equiv.symm_apply_apply _ _
    rw [finiteComponent_congrHom σ.symm (FinitePlace.mapEquiv σ w) w hw,
      finiteComponent_congrHom σ w (FinitePlace.mapEquiv σ w) rfl]
    rw [← FinitePlace.completionEquiv_symm σ w (FinitePlace.mapEquiv σ w) rfl]
    apply Units.ext
    exact (FinitePlace.completionEquiv σ w (FinitePlace.mapEquiv σ w) rfl).symm_apply_apply _

/-- The continuous isomorphism of idèle groups $I_L \cong I_{L'}$ induced by an isomorphism of
number fields `σ`: the component at $\sigma w$ of the image of `x` is $\sigma x_w$. Milne,
*Class Field Theory*, Chapter VII, §2. -/
def congr (σ : L ≃+* L') :
    NumberField.IdeleGroup (𝓞 L) L ≃ₜ* NumberField.IdeleGroup (𝓞 L') L' where
  toFun := congrHom σ
  invFun := congrHom σ.symm
  left_inv x := congrHom_left_inv σ x
  right_inv x := congrHom_left_inv σ.symm x
  map_mul' := map_mul (congrHom σ)
  continuous_toFun := by
    exact continuous_congrHom σ
  continuous_invFun := by
    exact continuous_congrHom σ.symm

/-- The component of `congr σ x` at a finite place $w' = \sigma(w)$ is $\sigma x_w$. -/
theorem finiteComponent_congr (σ : L ≃+* L') (w : HeightOneSpectrum (𝓞 L))
    (w' : HeightOneSpectrum (𝓞 L')) (h : FinitePlace.mapEquiv σ w = w')
    (x : NumberField.IdeleGroup (𝓞 L) L) :
    finiteComponent L' w' (congr σ x) =
      Units.map (FinitePlace.completionEquiv σ w w' h :
        w.adicCompletion L →* w'.adicCompletion L') (finiteComponent L w x) := by
  subst w'
  exact finiteComponent_congrHom σ w _ rfl x

/-- The component of `congr σ x` at an infinite place $w' = \sigma(w)$ is $\sigma x_w$. -/
theorem infiniteComponent_congr (σ : L ≃+* L') (w : InfinitePlace L) (w' : InfinitePlace L')
    (h : InfinitePlace.mapEquiv σ w = w') (x : NumberField.IdeleGroup (𝓞 L) L) :
    infiniteComponent L' w' (congr σ x) =
      Units.map (InfinitePlace.completionEquiv σ w w' h : w.Completion →* w'.Completion)
        (infiniteComponent L w x) := by
  subst w'
  exact infiniteComponent_congrHom σ w _ rfl x

/-- The idèle isomorphism of `σ` maps the principal idèle of `x` to that of `σ x`. -/
@[simp]
theorem congr_unitEmbedding (σ : L ≃+* L') (x : Lˣ) :
    congr σ (NumberField.IdeleGroup.unitEmbedding (𝓞 L) L x) =
      NumberField.IdeleGroup.unitEmbedding (𝓞 L') L' (Units.map (σ : L →* L') x) := by
  apply ext L'
  · intro w'
    let w := (InfinitePlace.mapEquiv σ).symm w'
    have hw : InfinitePlace.mapEquiv σ w = w' := Equiv.apply_symm_apply _ _
    rw [← hw, infiniteComponent_congr σ w (InfinitePlace.mapEquiv σ w) rfl,
      infiniteComponent_unitEmbedding, infiniteComponent_unitEmbedding]
    apply Units.ext
    exact InfinitePlace.completionEquiv_algebraMap σ w _ rfl x
  · intro w'
    let w := (FinitePlace.mapEquiv σ).symm w'
    have hw : FinitePlace.mapEquiv σ w = w' := Equiv.apply_symm_apply _ _
    rw [← hw, finiteComponent_congr σ w (FinitePlace.mapEquiv σ w) rfl,
      finiteComponent_unitEmbedding, finiteComponent_unitEmbedding]
    apply Units.ext
    exact FinitePlace.completionEquiv_algebraMap σ w _ rfl x

/-- The idèle isomorphism of `σ` maps the principal idèles onto the principal idèles. -/
theorem map_principalSubgroup_congr (σ : L ≃+* L') :
    (NumberField.IdeleGroup.principalSubgroup (𝓞 L) L).map (congr σ).toMulEquiv.toMonoidHom =
      NumberField.IdeleGroup.principalSubgroup (𝓞 L') L' := by
  ext y
  constructor
  · rintro ⟨z, ⟨u, rfl⟩, rfl⟩
    exact ⟨Units.map (σ : L →* L') u, (congr_unitEmbedding σ u).symm⟩
  · rintro ⟨u, rfl⟩
    let v := Units.map (σ.symm : L' →* L) u
    refine ⟨NumberField.IdeleGroup.unitEmbedding (𝓞 L) L v, ⟨v, rfl⟩, ?_⟩
    change congr σ (NumberField.IdeleGroup.unitEmbedding (𝓞 L) L v) = _
    rw [congr_unitEmbedding]
    congr 1
    apply Units.ext
    exact σ.apply_symm_apply _

/-- The idèle isomorphisms of `σ` and `τ` compose to that of `τ ∘ σ`. -/
@[simp]
theorem congr_trans (σ : L ≃+* L') (τ : L' ≃+* L'') :
    (congr σ).trans (congr τ) = congr (σ.trans τ) := by
  apply ContinuousMulEquiv.ext
  intro x
  apply ext L''
  · intro w''
    let w' := (InfinitePlace.mapEquiv τ).symm w''
    let w := (InfinitePlace.mapEquiv σ).symm w'
    have hσ : InfinitePlace.mapEquiv σ w = w' := Equiv.apply_symm_apply _ _
    have hτ : InfinitePlace.mapEquiv τ w' = w'' := Equiv.apply_symm_apply _ _
    have hστ : InfinitePlace.mapEquiv (σ.trans τ) w = w'' := by
      rw [InfinitePlace.mapEquiv_trans, hσ, hτ]
    change infiniteComponent L'' w'' (congr τ (congr σ x)) =
      infiniteComponent L'' w'' (congr (σ.trans τ) x)
    rw [infiniteComponent_congr τ w' w'' hτ,
      infiniteComponent_congr σ w w' hσ,
      infiniteComponent_congr (σ.trans τ) w w'' hστ]
    apply Units.ext
    exact congrArg (fun e => e (infiniteComponent L w x).val)
      (InfinitePlace.completionEquiv_trans σ w w' hσ τ w'' hτ)
  · intro w''
    let w' := (FinitePlace.mapEquiv τ).symm w''
    let w := (FinitePlace.mapEquiv σ).symm w'
    have hσ : FinitePlace.mapEquiv σ w = w' := Equiv.apply_symm_apply _ _
    have hτ : FinitePlace.mapEquiv τ w' = w'' := Equiv.apply_symm_apply _ _
    have hστ : FinitePlace.mapEquiv (σ.trans τ) w = w'' := by
      rw [FinitePlace.mapEquiv_trans, hσ, hτ]
    change finiteComponent L'' w'' (congr τ (congr σ x)) =
      finiteComponent L'' w'' (congr (σ.trans τ) x)
    rw [finiteComponent_congr τ w' w'' hτ,
      finiteComponent_congr σ w w' hσ,
      finiteComponent_congr (σ.trans τ) w w'' hστ]
    apply Units.ext
    exact congrArg (fun e => e (finiteComponent L w x).val)
      (FinitePlace.completionEquiv_trans σ w w' hσ τ w'' hτ)

/-- The idèle isomorphism of the identity is the identity. -/
@[simp]
theorem congr_refl : congr (RingEquiv.refl L) = ContinuousMulEquiv.refl _ := by
  apply ContinuousMulEquiv.ext
  intro x
  apply ext L
  · intro w
    change infiniteComponent L w (congr (RingEquiv.refl L) x) = infiniteComponent L w x
    rw [infiniteComponent_congr (RingEquiv.refl L) w w (InfinitePlace.mapEquiv_refl w)]
    rw [InfinitePlace.completionEquiv_refl]
    rfl
  · intro w
    change finiteComponent L w (congr (RingEquiv.refl L) x) = finiteComponent L w x
    rw [finiteComponent_congr (RingEquiv.refl L) w w (FinitePlace.mapEquiv_refl w)]
    rw [FinitePlace.completionEquiv_refl]
    rfl

/-! ### Isomorphisms over a base field -/

section Algebra

variable {K : Type*} [Field K] [Algebra K L] [Algebra K L']

/-- The Galois group $\operatorname{Gal}(L/K)$ acts on the idèle group $I_L$ by `congr`.
Milne, *Class Field Theory*, Chapter VII, §2, before Proposition 2.5. -/
instance instMulDistribMulAction :
    MulDistribMulAction (L ≃ₐ[K] L) (NumberField.IdeleGroup (𝓞 L) L) where
  smul σ x := congr σ.toRingEquiv x
  one_smul x := by
    change congr (RingEquiv.refl L) x = x
    rw [congr_refl]
    rfl
  mul_smul σ τ x := by
    have h : (σ * τ).toRingEquiv = τ.toRingEquiv.trans σ.toRingEquiv := by
      ext a
      exact AlgEquiv.mul_apply σ τ a
    change congr (σ * τ).toRingEquiv x = congr σ.toRingEquiv (congr τ.toRingEquiv x)
    rw [h, ← congr_trans]
    rfl
  smul_mul σ x y := map_mul (congr σ.toRingEquiv) x y
  smul_one σ := map_one (congr σ.toRingEquiv)

/-- The Galois action on idèles is the idèle isomorphism of the automorphism. -/
theorem smul_def (σ : L ≃ₐ[K] L) (x : NumberField.IdeleGroup (𝓞 L) L) :
    σ • x = congr σ.toRingEquiv x :=
  rfl

/-- The Galois action on principal idèles is the action on $L^\times$:
$\sigma (x) = (\sigma x)$. -/
theorem smul_unitEmbedding (σ : L ≃ₐ[K] L) (x : Lˣ) :
    σ • NumberField.IdeleGroup.unitEmbedding (𝓞 L) L x =
      NumberField.IdeleGroup.unitEmbedding (𝓞 L) L (σ • x) := by
  rw [smul_def, congr_unitEmbedding, AlgEquiv.smul_units_def]
  rfl

variable [NumberField K]

/-- The infinite component calculation for `norm_congr`. -/
private theorem infiniteComponent_norm_congr (σ : L ≃ₐ[K] L')
    (x : NumberField.IdeleGroup (𝓞 L) L) (v : InfinitePlace K) :
    infiniteComponent K v (norm (K := K) (L := L') (congr σ.toRingEquiv x)) =
      infiniteComponent K v (norm (K := K) (L := L) x) := by
  rw [infiniteComponent_norm_apply, infiniteComponent_norm_apply]
  let e := InfinitePlace.PlaceAbove.mapEquiv σ v
  calc
    (∏ w' : InfinitePlace.PlaceAbove (L := L') v,
        InfinitePlace.localNorm v w'.1
          (infiniteComponent L' w'.1 (congr σ.toRingEquiv x))) =
      ∏ w : InfinitePlace.PlaceAbove (L := L) v,
        InfinitePlace.localNorm v (e w).1
          (infiniteComponent L' (e w).1 (congr σ.toRingEquiv x)) := by
            exact (Equiv.prod_comp e _).symm
    _ = ∏ w : InfinitePlace.PlaceAbove (L := L) v,
        InfinitePlace.localNorm v w.1 (infiniteComponent L w.1 x) := by
          apply Finset.prod_congr rfl
          intro w _
          let : w.1.LiesOver v := w.2
          let : (InfinitePlace.mapEquiv σ.toRingEquiv w.1).LiesOver v :=
            InfinitePlace.liesOver_mapEquiv σ v w.1
          change InfinitePlace.localNorm v (InfinitePlace.mapEquiv σ.toRingEquiv w.1)
            (infiniteComponent L' (InfinitePlace.mapEquiv σ.toRingEquiv w.1)
              (congr σ.toRingEquiv x)) = _
          rw [infiniteComponent_congr σ.toRingEquiv w.1 _ rfl]
          exact InfinitePlace.localNorm_completionEquiv σ v w.1 _ rfl _

/-- The finite component calculation for `norm_congr`. -/
private theorem finiteComponent_norm_congr (σ : L ≃ₐ[K] L')
    (x : NumberField.IdeleGroup (𝓞 L) L) (v : HeightOneSpectrum (𝓞 K)) :
    finiteComponent K v (norm (K := K) (L := L') (congr σ.toRingEquiv x)) =
      finiteComponent K v (norm (K := K) (L := L) x) := by
  rw [finiteComponent_norm_apply, finiteComponent_norm_apply]
  let e := FinitePlace.PrimeAbove.mapEquiv σ v
  calc
    (∏ w' : FinitePlace.PrimeAbove (L := L') v,
        FinitePlace.localNorm v (FinitePlace.PrimeAbove.place v w')
          (finiteComponent L' (FinitePlace.PrimeAbove.place v w')
            (congr σ.toRingEquiv x))) =
      ∏ w : FinitePlace.PrimeAbove (L := L) v,
        FinitePlace.localNorm v (FinitePlace.PrimeAbove.place v (e w))
          (finiteComponent L' (FinitePlace.PrimeAbove.place v (e w))
            (congr σ.toRingEquiv x)) := by
            exact (Equiv.prod_comp e _).symm
    _ = ∏ w : FinitePlace.PrimeAbove (L := L) v,
        FinitePlace.localNorm v (FinitePlace.PrimeAbove.place v w)
          (finiteComponent L (FinitePlace.PrimeAbove.place v w) x) := by
          apply Finset.prod_congr rfl
          intro w _
          let : (FinitePlace.PrimeAbove.place v w).asIdeal.LiesOver v.asIdeal :=
            FinitePlace.PrimeAbove.place_liesOver v w
          let : (FinitePlace.mapEquiv σ.toRingEquiv
              (FinitePlace.PrimeAbove.place v w)).asIdeal.LiesOver v.asIdeal :=
            FinitePlace.liesOver_mapEquiv σ v (FinitePlace.PrimeAbove.place v w)
          change FinitePlace.localNorm v
            (FinitePlace.mapEquiv σ.toRingEquiv (FinitePlace.PrimeAbove.place v w))
            (finiteComponent L'
              (FinitePlace.mapEquiv σ.toRingEquiv (FinitePlace.PrimeAbove.place v w))
              (congr σ.toRingEquiv x)) = _
          rw [finiteComponent_congr σ.toRingEquiv (FinitePlace.PrimeAbove.place v w) _ rfl]
          exact FinitePlace.localNorm_completionEquiv σ v _ _ rfl _

/-- A `K`-isomorphism preserves the idèle norm to `K`: $N_{L'/K}(\sigma x) = N_{L/K}(x)$. -/
@[simp]
theorem norm_congr (σ : L ≃ₐ[K] L') (x : NumberField.IdeleGroup (𝓞 L) L) :
    norm (K := K) (L := L') (congr σ.toRingEquiv x) = norm (K := K) (L := L) x := by
  apply ext K
  · exact infiniteComponent_norm_congr σ x
  · exact finiteComponent_norm_congr σ x

/-- A `K`-isomorphism fixes included idèles: $\sigma(x) = x$ for $x \in I_K$. -/
@[simp]
theorem congr_inclusion (σ : L ≃ₐ[K] L') (x : NumberField.IdeleGroup (𝓞 K) K) :
    congr σ.toRingEquiv (inclusion (L := L) x) = inclusion (L := L') x := by
  apply ext L'
  · intro w'
    let v := InfinitePlace.below (K := K) w'
    let w := InfinitePlace.mapEquiv σ.symm.toRingEquiv w'
    have : w'.LiesOver v := InfinitePlace.liesOver_below w'
    have : w.LiesOver v := InfinitePlace.liesOver_mapEquiv σ.symm v w'
    have hw : InfinitePlace.mapEquiv σ.toRingEquiv w = w' := by
      change InfinitePlace.mapEquiv σ.toRingEquiv
        (InfinitePlace.mapEquiv σ.symm.toRingEquiv w') = w'
      rw [AlgEquiv.symm_toRingEquiv, ← InfinitePlace.mapEquiv_symm]
      exact Equiv.apply_symm_apply _ _
    rw [infiniteComponent_congr σ.toRingEquiv w w' hw,
      infiniteComponent_inclusion v w, infiniteComponent_inclusion v w']
    apply Units.ext
    exact InfinitePlace.completionEquiv_completionMap σ v w w' hw
      (infiniteComponent K v x).val
  · intro w'
    let v := FinitePlace.below (K := K) w'
    let w := FinitePlace.mapEquiv σ.symm.toRingEquiv w'
    have : w'.asIdeal.LiesOver v.asIdeal := FinitePlace.liesOver_below w'
    have : w.asIdeal.LiesOver v.asIdeal := FinitePlace.liesOver_mapEquiv σ.symm v w'
    have hw : FinitePlace.mapEquiv σ.toRingEquiv w = w' := by
      change FinitePlace.mapEquiv σ.toRingEquiv
        (FinitePlace.mapEquiv σ.symm.toRingEquiv w') = w'
      rw [AlgEquiv.symm_toRingEquiv, ← FinitePlace.mapEquiv_symm]
      exact Equiv.apply_symm_apply _ _
    rw [finiteComponent_congr σ.toRingEquiv w w' hw,
      finiteComponent_inclusion v w, finiteComponent_inclusion v w']
    apply Units.ext
    exact FinitePlace.completionEquiv_completionMap σ v w w' hw
      (finiteComponent K v x).val

/-! ### The norm as a product of conjugates

For Galois `L/K`, the component at `w` of $\prod_\sigma \sigma x$ is
$\prod_\sigma \sigma(x_{\sigma^{-1} w})$. Grouping the automorphisms by the place
$w' = \sigma^{-1} w$ above `v`, those carrying `w'` to `w` multiply on $x_{w'}$ to its local norm
(`FinitePlace.prod_completionEquiv_eq_completionMap_norm`), so the component is
$\prod_{w' \mid v} N_{L_{w'}/K_v}(x_{w'})$ embedded in $L_w$, the component of the included
norm. -/

/-- The finite component identity used by `inclusion_norm`. -/
private theorem finiteComponent_inclusion_norm [IsGalois K L]
    (x : NumberField.IdeleGroup (𝓞 L) L) (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] :
    finiteComponent L w (inclusion (K := K) (L := L) (norm (K := K) (L := L) x)) =
      ∏ σ : L ≃ₐ[K] L, finiteComponent L w (σ • x) := by
  classical
  rw [finiteComponent_inclusion v w, finiteComponent_norm_apply, map_prod]
  calc
    (∏ w' : FinitePlace.PrimeAbove (L := L) v,
      Units.map (FinitePlace.completionMap v w :
        v.adicCompletion K →* w.adicCompletion L)
        (FinitePlace.localNorm v (FinitePlace.PrimeAbove.place v w')
          (finiteComponent L (FinitePlace.PrimeAbove.place v w') x))) =
        ∏ w' : FinitePlace.PrimeAbove (L := L) v,
          ∏ σ : {σ : L ≃ₐ[K] L // σ • FinitePlace.PrimeAbove.place v w' = w},
            finiteComponent L w (σ.1 • x) := by
      apply Finset.prod_congr rfl
      intro w' _
      calc
        _ = ∏ σ : {σ : L ≃ₐ[K] L //
              σ • FinitePlace.PrimeAbove.place v w' = w},
            Units.map (FinitePlace.completionEquiv σ.1.toRingEquiv
              (FinitePlace.PrimeAbove.place v w') w σ.2 :
                (FinitePlace.PrimeAbove.place v w').adicCompletion L →*
                  w.adicCompletion L)
              (finiteComponent L (FinitePlace.PrimeAbove.place v w') x) := by
          apply Units.ext
          simp only [Units.coe_prod, Units.coe_map, FinitePlace.localNorm_val]
          convert
            (FinitePlace.prod_completionEquiv_eq_completionMap_norm v w
              (FinitePlace.PrimeAbove.place v w')
              (finiteComponent L (FinitePlace.PrimeAbove.place v w') x).val).symm using 1 <;> rfl
        _ = _ := by
          apply Finset.prod_congr rfl
          intro σ _
          rw [smul_def, finiteComponent_congr σ.1.toRingEquiv
            (FinitePlace.PrimeAbove.place v w') w σ.2]
    _ = ∏ σ : L ≃ₐ[K] L, finiteComponent L w (σ • x) := by
      symm
      apply prod_eq_prod_prod_smul_eq (FinitePlace.PrimeAbove.place (L := L) v)
        (FinitePlace.PrimeAbove.place_injective v)
      intro σ
      refine ⟨⟨(σ⁻¹ • w).asIdeal, (σ⁻¹ • w).isPrime, inferInstance⟩, ?_⟩
      exact smul_inv_smul σ w

/-- The infinite component identity used by `inclusion_norm`. -/
private theorem infiniteComponent_inclusion_norm [IsGalois K L]
    (x : NumberField.IdeleGroup (𝓞 L) L) (v : InfinitePlace K)
    (w : InfinitePlace L) [w.LiesOver v] :
    infiniteComponent L w (inclusion (K := K) (L := L) (norm (K := K) (L := L) x)) =
      ∏ σ : L ≃ₐ[K] L, infiniteComponent L w (σ • x) := by
  classical
  rw [infiniteComponent_inclusion v w, infiniteComponent_norm_apply, map_prod]
  calc
    (∏ w' : InfinitePlace.PlaceAbove (L := L) v,
      Units.map (NumberField.LiesOver.completionMap (v := v) (w := w) :
        v.Completion →* w.Completion)
        (InfinitePlace.localNorm v w'.1 (infiniteComponent L w'.1 x))) =
        ∏ w' : InfinitePlace.PlaceAbove (L := L) v,
          ∏ σ : {σ : L ≃ₐ[K] L // σ • w'.1 = w},
            infiniteComponent L w (σ.1 • x) := by
      apply Finset.prod_congr rfl
      intro w' _
      calc
        _ = ∏ σ : {σ : L ≃ₐ[K] L // σ • w'.1 = w},
            Units.map (InfinitePlace.completionEquiv σ.1.toRingEquiv w'.1 w σ.2 :
              w'.1.Completion →* w.Completion) (infiniteComponent L w'.1 x) := by
          apply Units.ext
          simp only [Units.coe_prod, Units.coe_map, InfinitePlace.localNorm_val]
          convert
            (InfinitePlace.prod_completionEquiv_eq_completionMap_norm v w w'.1
              (infiniteComponent L w'.1 x).val).symm using 1 <;> rfl
        _ = _ := by
          apply Finset.prod_congr rfl
          intro σ _
          rw [smul_def, infiniteComponent_congr σ.1.toRingEquiv w'.1 w σ.2]
    _ = ∏ σ : L ≃ₐ[K] L, infiniteComponent L w (σ • x) := by
      symm
      apply prod_eq_prod_prod_smul_eq (fun w' : InfinitePlace.PlaceAbove (L := L) v ↦ w'.1)
        Subtype.coe_injective
      intro σ
      refine ⟨⟨σ⁻¹ • w,
        show (σ⁻¹ • w) ∈ v.placesOver L from
          (inferInstance : (σ⁻¹ • w).LiesOver v)⟩, ?_⟩
      exact smul_inv_smul σ w

/-- For Galois `L/K`, the included norm of an idèle is the product of its conjugates:
$i(N_{L/K}(x)) = \prod_{\sigma \in G} \sigma x$. Milne, *Class Field Theory*, Chapter VII, §2,
"The norm map on idèles". -/
theorem inclusion_norm [IsGalois K L] (x : NumberField.IdeleGroup (𝓞 L) L) :
    inclusion (K := K) (L := L) (norm (K := K) (L := L) x) = ∏ σ : L ≃ₐ[K] L, σ • x := by
  apply ext L
  · intro w
    let v := InfinitePlace.below (K := K) w
    let : w.LiesOver v := InfinitePlace.liesOver_below w
    rw [infiniteComponent_inclusion_norm x v w, map_prod]
  · intro w
    let v := FinitePlace.below (K := K) w
    let : w.asIdeal.LiesOver v.asIdeal := FinitePlace.liesOver_below w
    rw [finiteComponent_inclusion_norm x v w, map_prod]

end Algebra

end IdeleGroup

/-! ### Isomorphisms of idèle class groups -/

namespace IdeleClassGroup

variable {L L' L'' : Type*} [Field L] [Field L'] [Field L''] [NumberField L] [NumberField L']
  [NumberField L'']

/-- The isomorphism of idèle class groups $C_L \cong C_{L'}$ induced by an isomorphism of number
fields. -/
def congr (σ : L ≃+* L') :
    NumberField.IdeleClassGroup (𝓞 L) L ≃* NumberField.IdeleClassGroup (𝓞 L') L' :=
  QuotientGroup.congr _ _ (IdeleGroup.congr σ).toMulEquiv (IdeleGroup.map_principalSubgroup_congr σ)

/-- The image of the class of an idèle is the class of its image. -/
@[simp]
theorem congr_mk (σ : L ≃+* L') (x : NumberField.IdeleGroup (𝓞 L) L) :
    congr σ (x : NumberField.IdeleClassGroup (𝓞 L) L) =
      (IdeleGroup.congr σ x : NumberField.IdeleClassGroup (𝓞 L') L') :=
  rfl

/-- The class-group isomorphisms of `σ` and `τ` compose to that of `τ ∘ σ`. -/
@[simp]
theorem congr_trans (σ : L ≃+* L') (τ : L' ≃+* L'') :
    (congr σ).trans (congr τ) = congr (σ.trans τ) := by
  apply MulEquiv.ext
  intro x
  refine QuotientGroup.induction_on x ?_
  intro y
  simp only [MulEquiv.trans_apply, congr_mk]
  rw [← IdeleGroup.congr_trans]
  rfl

section Algebra

variable {K : Type*} [Field K] [Algebra K L] [Algebra K L']

/-- The Galois group $\operatorname{Gal}(L/K)$ acts on the idèle class group $C_L$. -/
instance instMulDistribMulAction :
    MulDistribMulAction (L ≃ₐ[K] L) (NumberField.IdeleClassGroup (𝓞 L) L) where
  smul σ x := congr σ.toRingEquiv x
  one_smul x := by
    refine QuotientGroup.induction_on x ?_
    intro y
    change congr (RingEquiv.refl L) (y : NumberField.IdeleClassGroup (𝓞 L) L) = _
    rw [congr_mk, IdeleGroup.congr_refl]
    rfl
  mul_smul σ τ x := by
    have h : (σ * τ).toRingEquiv = τ.toRingEquiv.trans σ.toRingEquiv := by
      ext a
      exact AlgEquiv.mul_apply σ τ a
    change congr (σ * τ).toRingEquiv x = congr σ.toRingEquiv (congr τ.toRingEquiv x)
    rw [h, ← congr_trans]
    rfl
  smul_mul σ x y := map_mul (congr σ.toRingEquiv) x y
  smul_one σ := map_one (congr σ.toRingEquiv)

/-- The Galois action on idèle classes is the class-group isomorphism of the automorphism. -/
theorem smul_def (σ : L ≃ₐ[K] L) (x : NumberField.IdeleClassGroup (𝓞 L) L) :
    σ • x = congr σ.toRingEquiv x :=
  rfl

/-- The Galois action on idèle classes is induced by the action on idèles. -/
@[simp]
theorem smul_mk (σ : L ≃ₐ[K] L) (x : NumberField.IdeleGroup (𝓞 L) L) :
    σ • (x : NumberField.IdeleClassGroup (𝓞 L) L) =
      ((σ • x : NumberField.IdeleGroup (𝓞 L) L) : NumberField.IdeleClassGroup (𝓞 L) L) :=
  rfl

/-- The quotient map $I_L \to C_L$ as a homomorphism of $\operatorname{Gal}(L/K)$-modules. -/
def mkHom : NumberField.IdeleGroup (𝓞 L) L →*[L ≃ₐ[K] L] NumberField.IdeleClassGroup (𝓞 L) L where
  toFun x := x
  map_one' := rfl
  map_mul' _ _ := rfl
  map_smul' σ x := by
    exact (smul_mk σ x).symm

variable [NumberField K]

/-- A `K`-isomorphism preserves the norm of idèle classes to `K`. -/
@[simp]
theorem norm_congr (σ : L ≃ₐ[K] L') (x : NumberField.IdeleClassGroup (𝓞 L) L) :
    norm (K := K) (L := L') (congr σ.toRingEquiv x) = norm (K := K) (L := L) x := by
  refine QuotientGroup.induction_on x ?_
  intro y
  simp only [congr_mk, norm_mk, IdeleGroup.norm_congr]

/-- Conjugation by a $K$-automorphism preserves the norm of an idèle class to $K$; used in
cyclic descent and the existence theorem. -/
@[simp]
theorem norm_smul (σ : L ≃ₐ[K] L)
    (x : NumberField.IdeleClassGroup (𝓞 L) L) :
    norm (K := K) (L := L) (σ • x) = norm (K := K) (L := L) x := by
  exact norm_congr σ x

/-- The pullback of a subgroup under $N_{L/K}$ is stable under conjugation; used in cyclic
descent and the existence theorem. -/
theorem smul_mem_comap_norm
    (U : Subgroup (NumberField.IdeleClassGroup (𝓞 K) K))
    (σ : L ≃ₐ[K] L) {x : NumberField.IdeleClassGroup (𝓞 L) L}
    (hx : x ∈ U.comap (norm (K := K) (L := L))) :
    σ • x ∈ U.comap (norm (K := K) (L := L)) := by
  simpa only [Subgroup.mem_comap, norm_smul] using hx

/-- Isomorphic extensions have the same norm group: $N_{L/K}C_L = N_{L'/K}C_{L'}$ for a
`K`-isomorphism $L \cong L'$. -/
theorem range_norm_congr (σ : L ≃ₐ[K] L') :
    (norm (K := K) (L := L)).range = (norm (K := K) (L := L')).range := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨congr σ.toRingEquiv y, norm_congr σ y⟩
  · rintro ⟨y, rfl⟩
    exact ⟨congr σ.symm.toRingEquiv y, norm_congr σ.symm y⟩

/-- A `K`-isomorphism fixes the classes of included idèles. -/
@[simp]
theorem congr_inclusion (σ : L ≃ₐ[K] L') (x : NumberField.IdeleClassGroup (𝓞 K) K) :
    congr σ.toRingEquiv (inclusion (L := L) x) = inclusion (L := L') x := by
  refine QuotientGroup.induction_on x ?_
  intro y
  simp only [inclusion_mk, congr_mk, IdeleGroup.congr_inclusion]

/-- For Galois `L/K`, the included norm of an idèle class is the product of its conjugates:
$i(N_{L/K}(x)) = \prod_{\sigma \in G} \sigma x$. -/
theorem inclusion_norm [IsGalois K L] (x : NumberField.IdeleClassGroup (𝓞 L) L) :
    inclusion (K := K) (L := L) (norm (K := K) (L := L) x) = ∏ σ : L ≃ₐ[K] L, σ • x := by
  refine QuotientGroup.induction_on x ?_
  intro y
  simp only [norm_mk, inclusion_mk, smul_mk]
  rw [← QuotientGroup.mk_prod, IdeleGroup.inclusion_norm]

end Algebra

end IdeleClassGroup

/-! ### Fractional ideals under isomorphisms -/

variable {K K' : Type*} [Field K] [Field K'] [NumberField K] [NumberField K']

/-- The fractional ideal of $\sigma(y)$ is $\sigma((y))$. -/
theorem IdeleGroup.toFractionalIdeal_congr (σ : K ≃+* K') (y : NumberField.IdeleGroup (𝓞 K) K) :
    IdeleGroup.toFractionalIdeal (IdeleGroup.congr σ y) =
      FractionalIdeal.congr σ (IdeleGroup.toFractionalIdeal y) := by
  have hcount (w : HeightOneSpectrum (𝓞 K')) :
      _root_.FractionalIdeal.count K' w
          (IdeleGroup.toFractionalIdeal (IdeleGroup.congr σ y) :
            _root_.FractionalIdeal (𝓞 K')⁰ K') =
        _root_.FractionalIdeal.count K' w
          (FractionalIdeal.congr σ (IdeleGroup.toFractionalIdeal y) :
            _root_.FractionalIdeal (𝓞 K')⁰ K') := by
    obtain ⟨v, rfl⟩ := (FinitePlace.mapEquiv σ).surjective w
    rw [IdeleGroup.count_toFractionalIdeal, FractionalIdeal.count_congr,
      IdeleGroup.count_toFractionalIdeal,
      IdeleGroup.finiteComponent_congr σ v (FinitePlace.mapEquiv σ v) rfl y]
    change -WithZero.log (Valued.v
      (FinitePlace.completionEquiv σ v (FinitePlace.mapEquiv σ v) rfl
        ((IdeleGroup.finiteComponent K v y : (v.adicCompletion K)ˣ) :
          v.adicCompletion K))) = _
    rw [FinitePlace.valued_completionEquiv]
  apply Units.ext
  exact FractionalIdeal.ext_count
    (IdeleGroup.toFractionalIdeal (IdeleGroup.congr σ y)).ne_zero
    (FractionalIdeal.congr σ (IdeleGroup.toFractionalIdeal y)).ne_zero hcount

end SIC
