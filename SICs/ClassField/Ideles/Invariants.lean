/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Ideles.Galois
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

/-!
# Galois-invariant idèles and idèle classes

For a finite extension `L/K`, the inclusion of idèle classes $C_K \to C_L$ is injective. When
`L/K` is Galois with group `G`, the idèles of `L` fixed by `G` are the included idèles of `K`,
and the image of $C_K \to C_L$ is the group $C_L^G$ of `G`-invariant idèle classes.

This is Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII, §2, Proposition 2.5(a),
and Lemma 4.1 for $C_L^G=C_K$ in the Galois case, using Hilbert's Theorem 90
(Chapter II, Proposition 1.22). For arbitrary finite extensions, injectivity uses the completed
base change of Chapter VII, §2, Lemma 2.1 and Proposition 2.2.

## The argument

An idèle $x = (x_w)$ of `L` is fixed by `G` exactly when $x_{\sigma w} = \sigma x_w$ for all `σ`
and `w`. For `σ` in the decomposition group $D_w$ this says that $x_w$ is fixed by $D_w$, hence
lies in $K_v$ for the place `v` below `w`, since $L_w/K_v$ is Galois with group $D_w$
(`FinitePlace.mem_range_completionMap_iff`). These elements are independent of the choice of `w`
above `v`, because `G` permutes the places above `v` transitively and its completions fix $K_v$;
they are integral units at almost all `v`, because completion maps preserve absolute values up to
a power. They therefore form an idèle `y` of `K` with $i(y) = x$. Conversely included idèles are
fixed (`congr_inclusion`).

If an included idèle $i(x)$ is principal, $i(x) = (a)$ with $a \in L^\times$, fix an infinite
place `v` of `K`. At every `w` above `v`, the images of the local component $x_v$ and of $a$
agree in $L_w$. The decomposition $K_v \otimes_K L \cong \prod_{w \mid v} L_w$ therefore gives
$x_v \otimes 1 = 1 \otimes a$. Applying a $K$-linear functional $L \to K$ sending $1$ to $1$
shows that $x_v$ comes from some $k \in K$; injectivity of $L \to K_v \otimes_K L$ then gives
$a=k$. Thus $i(x)=i((k))$, and injectivity of the idèle inclusion shows that $x$ is principal.

If the class of $x \in I_L$ is fixed by `G`, then $\sigma x = x \cdot (a_\sigma)$ for unique
$a_\sigma \in L^\times$, and uniqueness gives the crossed-homomorphism identity
$a_{\sigma\tau} = \sigma(a_\tau) a_\sigma$. By Hilbert's Theorem 90 (Mathlib's
`groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units`),
$a_\sigma = \sigma b / b$ for some $b \in L^\times$, so $x / (b)$ is a `G`-fixed idèle, hence
included, and has the same class as `x`.
-/

noncomputable section

open IsDedekindDomain NumberField
open scoped NumberField SIC.FinitePlace SIC.InfinitePlace NumberField.LiesOver

namespace SIC

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-! ### Invariant idèles -/

namespace IdeleGroup

/-- A fixed idèle has a component in the base completion at each finite place. Used in
`range_inclusion`. -/
private theorem finiteComponent_descends [IsGalois K L]
    (x : NumberField.IdeleGroup (𝓞 L) L)
    (hx : ∀ σ : L ≃ₐ[K] L, σ • x = x)
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    ∃ y : (v.adicCompletion K)ˣ,
      Units.map (FinitePlace.completionMap v w : v.adicCompletion K →* w.adicCompletion L) y =
        finiteComponent L w x := by
  apply (mem_range_unitsMap_iff (F := v.adicCompletion K)
    (E := w.adicCompletion L) _).2
  apply (FinitePlace.mem_range_completionMap_iff v w _).2
  intro σ
  have hw : FinitePlace.mapEquiv σ.1.toRingEquiv w = w :=
    (MulAction.mem_stabilizer_iff.mp σ.2)
  have hc := congrArg (finiteComponent L w) (hx σ.1)
  rw [smul_def, finiteComponent_congr σ.1.toRingEquiv w w hw] at hc
  exact congrArg Units.val hc

omit [NumberField K] in
/-- A fixed idèle has a component in the base completion at each infinite place. Used in
`range_inclusion`. -/
private theorem infiniteComponent_descends [IsGalois K L]
    (x : NumberField.IdeleGroup (𝓞 L) L)
    (hx : ∀ σ : L ≃ₐ[K] L, σ • x = x)
    (v : InfinitePlace K) (w : InfinitePlace L) [w.LiesOver v] :
    ∃ y : v.Completionˣ,
      Units.map (NumberField.LiesOver.completionMap (v := v) (w := w) :
        v.Completion →* w.Completion) y = infiniteComponent L w x := by
  apply (mem_range_unitsMap_iff (F := v.Completion) (E := w.Completion) _).2
  apply (InfinitePlace.mem_range_completionMap_iff v w _).2
  intro σ
  have hw : InfinitePlace.mapEquiv σ.1.toRingEquiv w = w :=
    (MulAction.mem_stabilizer_iff.mp σ.2)
  have hc := congrArg (infiniteComponent L w) (hx σ.1)
  rw [smul_def, infiniteComponent_congr σ.1.toRingEquiv w w hw] at hc
  exact congrArg Units.val hc

/-- The finite component descended at one prime agrees with every conjugate prime above the
same base prime. Used in `range_inclusion`. -/
private theorem finiteComponent_map_of_fixed [IsGalois K L]
    (x : NumberField.IdeleGroup (𝓞 L) L)
    (hx : ∀ σ : L ≃ₐ[K] L, σ • x = x)
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] (y : (v.adicCompletion K)ˣ)
    (hy : Units.map (FinitePlace.completionMap v w : v.adicCompletion K →* w.adicCompletion L) y =
      finiteComponent L w x)
    (w' : HeightOneSpectrum (𝓞 L)) [w'.asIdeal.LiesOver v.asIdeal] :
    Units.map (FinitePlace.completionMap v w' : v.adicCompletion K →* w'.adicCompletion L) y =
      finiteComponent L w' x := by
  obtain ⟨σ, hσ⟩ := FinitePlace.exists_smul_eq v w w'
  have hσ' : FinitePlace.mapEquiv σ.toRingEquiv w = w' := hσ
  have hc := congrArg (finiteComponent L w') (hx σ)
  rw [smul_def, finiteComponent_congr σ.toRingEquiv w w' hσ'] at hc
  calc
    _ = Units.map (FinitePlace.completionEquiv σ.toRingEquiv w w' hσ' :
          w.adicCompletion L →* w'.adicCompletion L)
          (Units.map (FinitePlace.completionMap v w :
            v.adicCompletion K →* w.adicCompletion L) y) := by
        apply Units.ext
        exact (FinitePlace.completionEquiv_completionMap σ v w w' hσ' (y :
          v.adicCompletion K)).symm
    _ = _ := by rw [hy]; exact hc

omit [NumberField K] in
/-- The infinite component descended at one place agrees with every conjugate place above the
same base place. Used in `range_inclusion`. -/
private theorem infiniteComponent_map_of_fixed [IsGalois K L]
    (x : NumberField.IdeleGroup (𝓞 L) L)
    (hx : ∀ σ : L ≃ₐ[K] L, σ • x = x)
    (v : InfinitePlace K) (w : InfinitePlace L) [w.LiesOver v]
    (y : v.Completionˣ)
    (hy : Units.map (NumberField.LiesOver.completionMap (v := v) (w := w) :
      v.Completion →* w.Completion) y = infiniteComponent L w x)
    (w' : InfinitePlace L) [w'.LiesOver v] :
    Units.map (NumberField.LiesOver.completionMap (v := v) (w := w') :
      v.Completion →* w'.Completion) y = infiniteComponent L w' x := by
  obtain ⟨σ, hσ⟩ := InfinitePlace.exists_smul_eq v w w'
  have hσ' : InfinitePlace.mapEquiv σ.toRingEquiv w = w' := hσ
  have hc := congrArg (infiniteComponent L w') (hx σ)
  rw [smul_def, infiniteComponent_congr σ.toRingEquiv w w' hσ'] at hc
  calc
    _ = Units.map (InfinitePlace.completionEquiv σ.toRingEquiv w w' hσ' :
          w.Completion →* w'.Completion)
          (Units.map (NumberField.LiesOver.completionMap (v := v) (w := w) :
            v.Completion →* w.Completion) y) := by
        apply Units.ext
        exact (InfinitePlace.completionEquiv_completionMap σ v w w' hσ' (y :
          v.Completion)).symm
    _ = _ := by rw [hy]; exact hc

omit [NumberField L] in
omit [NumberField K] in
/-- The selected finite place above each base place is unique to that base place. Used in
`range_inclusion` to pull back the restricted-product condition. -/
private theorem finiteAbove_injective :
    Function.Injective (fun v : HeightOneSpectrum (𝓞 K) ↦
      FinitePlace.PrimeAbove.place v
        (Classical.arbitrary (FinitePlace.PrimeAbove (L := L) v))) := by
  intro v v' h
  have h' := congrArg (FinitePlace.below (K := K) (L := L)) h
  simpa only [FinitePlace.PrimeAbove.below_place] using h'

/-- The base finite local unit determined by a fixed idèle at the selected prime. Used in
`range_inclusion`. -/
private def finiteDescend [IsGalois K L] (x : NumberField.IdeleGroup (𝓞 L) L)
    (hx : ∀ σ : L ≃ₐ[K] L, σ • x = x) (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ :=
  Classical.choose (finiteComponent_descends x hx v
    (FinitePlace.PrimeAbove.place v (Classical.arbitrary (FinitePlace.PrimeAbove (L := L) v))))

/-- The selected finite component of a fixed idèle is the image of `finiteDescend`. -/
private theorem finiteDescend_spec [IsGalois K L] (x : NumberField.IdeleGroup (𝓞 L) L)
    (hx : ∀ σ : L ≃ₐ[K] L, σ • x = x) (v : HeightOneSpectrum (𝓞 K)) :
    Units.map (FinitePlace.completionMap v
      (FinitePlace.PrimeAbove.place v (Classical.arbitrary (FinitePlace.PrimeAbove (L := L) v))) :
      v.adicCompletion K →*
        (FinitePlace.PrimeAbove.place v
          (Classical.arbitrary (FinitePlace.PrimeAbove (L := L) v))).adicCompletion L)
      (finiteDescend x hx v) =
        finiteComponent L (FinitePlace.PrimeAbove.place v
          (Classical.arbitrary (FinitePlace.PrimeAbove (L := L) v))) x :=
  Classical.choose_spec (finiteComponent_descends x hx v
    (FinitePlace.PrimeAbove.place v (Classical.arbitrary (FinitePlace.PrimeAbove (L := L) v))))

/-- The base infinite local unit determined by a fixed idèle at the selected place. Used in
`range_inclusion`. -/
private def infiniteDescend [IsGalois K L] (x : NumberField.IdeleGroup (𝓞 L) L)
    (hx : ∀ σ : L ≃ₐ[K] L, σ • x = x) (v : InfinitePlace K) : v.Completionˣ :=
  Classical.choose (infiniteComponent_descends x hx v
    (Classical.arbitrary (InfinitePlace.PlaceAbove (L := L) v)).1)

/-- The selected infinite component of a fixed idèle is the image of `infiniteDescend`. -/
private theorem infiniteDescend_spec [IsGalois K L] (x : NumberField.IdeleGroup (𝓞 L) L)
    (hx : ∀ σ : L ≃ₐ[K] L, σ • x = x) (v : InfinitePlace K) :
    Units.map (NumberField.LiesOver.completionMap
      (v := v) (w := (Classical.arbitrary (InfinitePlace.PlaceAbove (L := L) v)).1) :
      v.Completion →* (Classical.arbitrary (InfinitePlace.PlaceAbove (L := L) v)).1.Completion)
      (infiniteDescend x hx v) =
        infiniteComponent L (Classical.arbitrary (InfinitePlace.PlaceAbove (L := L) v)).1 x :=
  Classical.choose_spec (infiniteComponent_descends x hx v
    (Classical.arbitrary (InfinitePlace.PlaceAbove (L := L) v)).1)

/-- The idèle of `K` assembled from the descended components of a fixed idèle of `L`.
Used in `range_inclusion`. -/
private def descendIdele [IsGalois K L] (x : NumberField.IdeleGroup (𝓞 L) L)
    (hx : ∀ σ : L ≃ₐ[K] L, σ • x = x) : NumberField.IdeleGroup (𝓞 K) K := by
  classical
  have hEv : ∀ᶠ w in (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 L))),
      finiteComponent L w x ∈
        FinitePlace.unitGroup w :=
    ((componentsEquiv L x).2).2
  have hfin : ∀ᶠ v in (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 K))),
      finiteDescend x hx v ∈
        FinitePlace.unitGroup v := by
    have ht := (finiteAbove_injective (K := K) (L := L)).tendsto_cofinite
    filter_upwards [ht.eventually hEv] with v hv
    apply (FinitePlace.units_map_completionMap_mem_iff v
      (FinitePlace.PrimeAbove.place v
        (Classical.arbitrary (FinitePlace.PrimeAbove (L := L) v)))).mp
    rwa [finiteDescend_spec]
  let yf : FiniteLocalIdele K :=
    RestrictedProduct.mk (fun v ↦ finiteDescend x hx v) hfin
  exact (componentsEquiv K).symm (fun v ↦ infiniteDescend x hx v, yf)

/-- The infinite components of `descendIdele` are the chosen descended components. -/
private theorem infiniteComponent_descendIdele [IsGalois K L]
    (x : NumberField.IdeleGroup (𝓞 L) L)
    (hx : ∀ σ : L ≃ₐ[K] L, σ • x = x) (v : InfinitePlace K) :
    infiniteComponent K v (descendIdele x hx) = infiniteDescend x hx v := by
  simp only [descendIdele, infiniteComponent_apply, MulEquiv.apply_symm_apply]

/-- The finite components of `descendIdele` are the chosen descended components. -/
private theorem finiteComponent_descendIdele [IsGalois K L]
    (x : NumberField.IdeleGroup (𝓞 L) L)
    (hx : ∀ σ : L ≃ₐ[K] L, σ • x = x) (v : HeightOneSpectrum (𝓞 K)) :
    finiteComponent K v (descendIdele x hx) = finiteDescend x hx v := by
  simp only [descendIdele, finiteComponent_apply, MulEquiv.apply_symm_apply]
  rfl

/-- Including `descendIdele` recovers the original fixed idèle. Used in `range_inclusion`. -/
private theorem inclusion_descendIdele [IsGalois K L]
    (x : NumberField.IdeleGroup (𝓞 L) L)
    (hx : ∀ σ : L ≃ₐ[K] L, σ • x = x) :
    inclusion (K := K) (L := L) (descendIdele x hx) = x := by
  apply ext L
  · intro w
    let v := InfinitePlace.below (K := K) w
    rw [infiniteComponent_inclusion v w, infiniteComponent_descendIdele]
    exact infiniteComponent_map_of_fixed x hx v
      (Classical.arbitrary (InfinitePlace.PlaceAbove (L := L) v)).1
      (infiniteDescend x hx v) (infiniteDescend_spec x hx v) w
  · intro w
    let v := FinitePlace.below (K := K) w
    rw [finiteComponent_inclusion v w, finiteComponent_descendIdele]
    exact finiteComponent_map_of_fixed x hx v
      (FinitePlace.PrimeAbove.place v (Classical.arbitrary (FinitePlace.PrimeAbove (L := L) v)))
      (finiteDescend x hx v) (finiteDescend_spec x hx v) w

/-- For Galois `L/K`, the idèles of `L` fixed by $G = \operatorname{Gal}(L/K)$ are the included
idèles of `K`: $I_L^G = I_K$. Milne, *Class Field Theory*, Chapter VII, §2, Proposition 2.5(a). -/
theorem range_inclusion [IsGalois K L] :
    (inclusion (K := K) (L := L)).range =
      FixedPoints.subgroup (L ≃ₐ[K] L) (NumberField.IdeleGroup (𝓞 L) L) := by
  classical
  apply Subgroup.ext
  intro x
  rw [FixedPoints.mem_subgroup]
  constructor
  · rintro ⟨y, rfl⟩ σ
    simpa only [smul_def] using congr_inclusion (L := L) σ y
  · intro hx
    exact ⟨descendIdele x hx, inclusion_descendIdele x hx⟩

end IdeleGroup

/-! ### Invariant idèle classes -/

namespace IdeleClassGroup

omit [NumberField K] in
/-- A fixed idèle class determines a principal quotient `(σ • x) / x`. Used in
`range_inclusion`. -/
private theorem principalFactor_exists (x : NumberField.IdeleGroup (𝓞 L) L)
    (hx : ∀ σ : L ≃ₐ[K] L,
      σ • (x : NumberField.IdeleClassGroup (𝓞 L) L) = (x : NumberField.IdeleClassGroup (𝓞 L) L))
    (σ : L ≃ₐ[K] L) :
    ∃ a : Lˣ, NumberField.IdeleGroup.unitEmbedding (𝓞 L) L a = σ • x / x := by
  have hq : ((σ • x / x : NumberField.IdeleGroup (𝓞 L) L) :
      NumberField.IdeleClassGroup (𝓞 L) L) = 1 := by
    rw [QuotientGroup.mk_div, ← smul_mk, hx σ]
    exact div_self' (x : NumberField.IdeleClassGroup (𝓞 L) L)
  exact (QuotientGroup.eq_one_iff _).1 hq

/-- The unique principal factor of `(σ • x) / x` for a fixed idèle class. Used in
`range_inclusion`. -/
private def principalFactor (x : NumberField.IdeleGroup (𝓞 L) L)
    (hx : ∀ σ : L ≃ₐ[K] L,
      σ • (x : NumberField.IdeleClassGroup (𝓞 L) L) = (x : NumberField.IdeleClassGroup (𝓞 L) L))
    (σ : L ≃ₐ[K] L) : Lˣ :=
  Classical.choose (principalFactor_exists x hx σ)

omit [NumberField K] in
/-- The factor `principalFactor x σ` has principal idèle `(σ • x) / x`. -/
private theorem principalFactor_spec (x : NumberField.IdeleGroup (𝓞 L) L)
    (hx : ∀ σ : L ≃ₐ[K] L,
      σ • (x : NumberField.IdeleClassGroup (𝓞 L) L) = (x : NumberField.IdeleClassGroup (𝓞 L) L))
    (σ : L ≃ₐ[K] L) :
    NumberField.IdeleGroup.unitEmbedding (𝓞 L) L (principalFactor x hx σ) = σ • x / x :=
  Classical.choose_spec (principalFactor_exists x hx σ)

omit [NumberField K] in
/-- The principal factors of a fixed idèle class form a crossed homomorphism. Used in
`range_inclusion`. -/
private theorem principalFactor_cocycle (x : NumberField.IdeleGroup (𝓞 L) L)
    (hx : ∀ σ : L ≃ₐ[K] L,
      σ • (x : NumberField.IdeleClassGroup (𝓞 L) L) = (x : NumberField.IdeleClassGroup (𝓞 L) L)) :
    groupCohomology.IsMulCocycle₁ (principalFactor x hx) := by
  intro σ τ
  apply IdeleGroup.unitEmbedding_injective L
  calc
    NumberField.IdeleGroup.unitEmbedding (𝓞 L) L (principalFactor x hx (σ * τ)) =
        (σ * τ) • x / x := principalFactor_spec x hx (σ * τ)
    _ = (σ • (τ • x / x)) * (σ • x / x) := by
      simp only [mul_smul, IdeleGroup.smul_def, map_div]
      exact (div_mul_div_cancel _ _ _).symm
    _ = (σ • NumberField.IdeleGroup.unitEmbedding (𝓞 L) L (principalFactor x hx τ)) *
          NumberField.IdeleGroup.unitEmbedding (𝓞 L) L (principalFactor x hx σ) := by
      rw [principalFactor_spec, principalFactor_spec]
    _ = NumberField.IdeleGroup.unitEmbedding (𝓞 L) L (σ • principalFactor x hx τ) *
          NumberField.IdeleGroup.unitEmbedding (𝓞 L) L (principalFactor x hx σ) := by
      rw [IdeleGroup.smul_unitEmbedding]
    _ = NumberField.IdeleGroup.unitEmbedding (𝓞 L) L
          (σ • principalFactor x hx τ * principalFactor x hx σ) :=
      (map_mul (NumberField.IdeleGroup.unitEmbedding (𝓞 L) L) _ _).symm

omit [NumberField K] in
/-- A coboundary for the principal factors makes the adjusted idèle fixed. Used in
`fixedRepresentative`. -/
private theorem quotient_fixed_of_coboundary
    (x : NumberField.IdeleGroup (𝓞 L) L)
    (hx : ∀ σ : L ≃ₐ[K] L,
      σ • (x : NumberField.IdeleClassGroup (𝓞 L) L) = (x : NumberField.IdeleClassGroup (𝓞 L) L))
    (b : Lˣ) (hb : ∀ σ : L ≃ₐ[K] L, σ • b / b = principalFactor x hx σ)
    (σ : L ≃ₐ[K] L) :
    σ • (x / NumberField.IdeleGroup.unitEmbedding (𝓞 L) L b) =
      x / NumberField.IdeleGroup.unitEmbedding (𝓞 L) L b := by
  have hnum : σ • x =
      NumberField.IdeleGroup.unitEmbedding (𝓞 L) L (principalFactor x hx σ) * x :=
    eq_mul_of_div_eq (principalFactor_spec x hx σ).symm
  have hden : σ • NumberField.IdeleGroup.unitEmbedding (𝓞 L) L b =
      NumberField.IdeleGroup.unitEmbedding (𝓞 L) L (principalFactor x hx σ) *
        NumberField.IdeleGroup.unitEmbedding (𝓞 L) L b := by
    apply eq_mul_of_div_eq
    rw [IdeleGroup.smul_unitEmbedding, ← map_div, hb σ]
  rw [IdeleGroup.smul_def, map_div, ← IdeleGroup.smul_def, ← IdeleGroup.smul_def,
    hnum, hden]
  exact mul_div_mul_left_eq_div _ _ _

/-- Hilbert 90 gives a Galois-fixed idèle representing every fixed idèle class. Used in
`range_inclusion`. -/
private theorem fixedRepresentative [IsGalois K L]
    (x : NumberField.IdeleGroup (𝓞 L) L)
    (hx : ∀ σ : L ≃ₐ[K] L,
      σ • (x : NumberField.IdeleClassGroup (𝓞 L) L) =
        (x : NumberField.IdeleClassGroup (𝓞 L) L)) :
    ∃ z : NumberField.IdeleGroup (𝓞 L) L,
      (∀ σ : L ≃ₐ[K] L, σ • z = z) ∧
        (z : NumberField.IdeleClassGroup (𝓞 L) L) =
          (x : NumberField.IdeleClassGroup (𝓞 L) L) := by
  let a := principalFactor x hx
  have ha : groupCohomology.IsMulCocycle₁ a := principalFactor_cocycle x hx
  obtain ⟨b, hb⟩ :=
    groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units a ha
  refine ⟨x / NumberField.IdeleGroup.unitEmbedding (𝓞 L) L b,
    quotient_fixed_of_coboundary x hx b hb, ?_⟩
  rw [QuotientGroup.mk_div, coe_unitEmbedding, div_one]

/-- For every finite extension `L/K` of number fields, the inclusion of idèle classes
$C_K \to C_L$ is injective. Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII, §4,
"The idèle class group"; the local base change is Chapter VII, §2, Lemma 2.1 and
Proposition 2.2. -/
theorem inclusion_injective :
    Function.Injective (inclusion (K := K) (L := L)) := by
  classical
  apply (injective_iff_map_eq_one (inclusion (K := K) (L := L))).2
  intro c
  refine QuotientGroup.induction_on c ?_
  intro x hx
  have hx' : IdeleGroup.inclusion (K := K) (L := L) x ∈
      NumberField.IdeleGroup.principalSubgroup (𝓞 L) L :=
    (QuotientGroup.eq_one_iff _).1 (by simpa only [inclusion_mk] using hx)
  obtain ⟨a, ha⟩ := hx'
  let v : InfinitePlace K := (inferInstance : Nonempty (InfinitePlace K)).some
  let c : v.Completion := IdeleGroup.infiniteComponent K v x
  have ht : c ⊗ₜ[K] (1 : L) = (1 : v.Completion) ⊗ₜ[K] (a : L) := by
    apply InfinitePlace.baseChangeAlgHom_injective v
    funext w
    have hw := congrArg (fun u : (w.1.Completion)ˣ => (u : w.1.Completion))
      (congrArg (IdeleGroup.infiniteComponent L w.1) ha)
    rw [IdeleGroup.infiniteComponent_unitEmbedding,
      IdeleGroup.infiniteComponent_inclusion v w.1] at hw
    change algebraMap L w.1.Completion (a : L) =
      algebraMap v.Completion w.1.Completion
        (IdeleGroup.infiniteComponent K v x : v.Completion) at hw
    simpa only [InfinitePlace.baseChangeAlgHom_tmul, map_one, mul_one, one_mul, c]
      using hw.symm
  obtain ⟨k, hak, _⟩ := exists_eq_algebraMap_of_tmul_one_eq_one_tmul ht
  have hk : k ≠ 0 := by
    intro hk
    apply a.ne_zero
    rw [hak, hk, map_zero]
  have hu : Units.map (algebraMap K L) (Units.mk0 k hk) = a := by
    apply Units.ext
    change algebraMap K L k = (a : L)
    exact hak.symm
  apply (QuotientGroup.eq_one_iff _).2
  refine ⟨Units.mk0 k hk, ?_⟩
  apply (IdeleGroup.inclusion_injective (K := K) (L := L))
  rw [IdeleGroup.inclusion_unitEmbedding, hu]
  exact ha

/-- For Galois `L/K`, the idèle classes of `L` fixed by $G = \operatorname{Gal}(L/K)$ are the
included idèle classes of `K`: $C_L^G = C_K$. Milne, *Class Field Theory*, Chapter VII,
Lemma 4.1. -/
theorem range_inclusion [IsGalois K L] :
    (inclusion (K := K) (L := L)).range =
      FixedPoints.subgroup (L ≃ₐ[K] L) (NumberField.IdeleClassGroup (𝓞 L) L) := by
  classical
  apply Subgroup.ext
  intro c
  rw [FixedPoints.mem_subgroup]
  constructor
  · rintro ⟨d, rfl⟩ σ
    simpa only [smul_def] using congr_inclusion (L := L) σ d
  · intro hc
    revert hc
    refine QuotientGroup.induction_on c ?_
    intro x hx
    obtain ⟨z, hz, hzc⟩ := fixedRepresentative x hx
    have hzmem : z ∈ (IdeleGroup.inclusion (K := K) (L := L)).range := by
      rw [IdeleGroup.range_inclusion]
      exact (FixedPoints.mem_subgroup _ _ _).2 hz
    obtain ⟨y, hy⟩ := hzmem
    refine ⟨(y : NumberField.IdeleClassGroup (𝓞 K) K), ?_⟩
    calc
      inclusion (y : NumberField.IdeleClassGroup (𝓞 K) K) =
          ((IdeleGroup.inclusion (K := K) (L := L) y : NumberField.IdeleGroup (𝓞 L) L) :
            NumberField.IdeleClassGroup (𝓞 L) L) := rfl
      _ = (z : NumberField.IdeleClassGroup (𝓞 L) L) :=
        congrArg (fun t : NumberField.IdeleGroup (𝓞 L) L ↦
          (t : NumberField.IdeleClassGroup (𝓞 L) L)) hy
      _ = (x : NumberField.IdeleClassGroup (𝓞 L) L) := hzc

end IdeleClassGroup

end SIC
