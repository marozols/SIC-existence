/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Existence
import SICs.ClassField.RayClassField.Idelic

/-!
# The narrow ray class field

For a nonzero modulus `m` of a real quadratic field `K`, the narrow ray class field: a finite
abelian extension `H/K` whose norm group is the ray subgroup with positivity at every real place.
At a prime coprime to `m`, Frobenius is the Artin symbol of a sign class exactly when the prime
has a generator `α ≡ 1 (mod m)` with those signs.

This module follows Milne, *Class Field Theory*, version 4.03 (2020), Chapter V, Proposition 4.6
and Theorem 5.3, for the modulus $\mathfrak m\infty_1\infty_2$. It supplies the auxiliary narrow
ray field in the general existence proof, and the sign classes
of `SICs.ClassField.RayClassField.SignClasses`.

## The argument

*Finite index.* The ray idèles positive at every real place have index at most two in those
positive at all real places but the selected one: the sign at the selected place is a
homomorphism to $\{\pm1\}$ with that kernel. Images in the idèle class group have relative index
at most two as well, and the selected-place ray subgroup has finite index
(`IdeleClassGroup.raySubgroup_finiteIndex`).

*Existence.* The unit idèles away from the support of `m` are ray idèles
(`awayUnitSubgroup_le_rayIdeleSubgroup`), so the existence theorem
`exists_intermediateField_range_norm_eq` gives `H`.

*Sign classes.* The sign idèle $\varepsilon$ has component $\varepsilon_w=\pm1$ at each real place
and $1$ elsewhere; its class respects multiplication of signs (`signIdeleClass_mul`) and its
square is $1$. At a prime $\mathfrak p$ coprime to `m`, unramified in `H`
(`rayNorm_ramificationIdx_one`), Frobenius is the Artin symbol of a uniformizer idèle $\pi$ at
$\mathfrak p$ (`globalArtin_ofAdicCompletion`), and the kernel of the Artin map is the norm group
(`ker_globalArtin`). So Frobenius is $\operatorname{Art}(\varepsilon)$ exactly when
$\pi\varepsilon^{-1}$ is a principal idèle $c$ times a ray idèle. Comparing components, this
says that $\alpha=c$ generates $\mathfrak p$, is congruent to one modulo `m` at the primes
dividing `m`, and has sign $\varepsilon_w$ at each real place; such an $\alpha$ is integral since
$\mathfrak p$ is, and then $\alpha-1\in m$. Conversely such an $\alpha$ gives the decomposition.
-/

noncomputable section

namespace SIC

open IsDedekindDomain NumberField
open scoped nonZeroDivisors

universe u

variable {K : Type u} [Field K] [NumberField K] [NumberField.IsTotallyReal K]

/-! ### Signed generators and sign idèles -/

/-- An ideal `I` has a **signed ray generator** for the modulus `m` and the signs `ε`:
$I=(\alpha)$ with $\alpha\in\mathcal O_K$, $\alpha\equiv1\pmod{\mathfrak m}$, and
$\varepsilon_w\,\iota_w(\alpha)>0$ at every infinite place `w`. With $\varepsilon=1$ this is the
trivial class of the narrow ray class group of modulus $\mathfrak m\infty_1\infty_2$. -/
def HasSignedRayGenerator (m : Ideal (𝓞 K)) (ε : InfinitePlace K → ℤˣ) (I : Ideal (𝓞 K)) :
    Prop :=
  ∃ α : 𝓞 K, I = Ideal.span {α} ∧ α - 1 ∈ m ∧
    ∀ w : InfinitePlace K, 0 < (ε w : ℝ) * realEmbeddingAt K w (α : K)

/-- The sign idèle with prescribed sign at every infinite place and unit finite components. -/
def signIdele (ε : InfinitePlace K → ℤˣ) : NumberField.IdeleGroup (𝓞 K) K :=
  ∏ w, NumberField.IdeleGroup.ofCompletion (𝓞 K) K w
    (Units.map (Int.castRingHom w.Completion : ℤ →* w.Completion) (ε w))

/-- The class of the sign idèle in the idèle class group. -/
def signIdeleClass (ε : InfinitePlace K → ℤˣ) : NumberField.IdeleClassGroup (𝓞 K) K :=
  (signIdele ε : NumberField.IdeleClassGroup (𝓞 K) K)

omit [NumberField.IsTotallyReal K] in
/-- The sign idèle class is multiplicative in its placewise signs. -/
theorem signIdeleClass_mul (s t : InfinitePlace K → ℤˣ) :
    signIdeleClass (s * t) = signIdeleClass s * signIdeleClass t := by
  have hid : signIdele (s * t) = signIdele s * signIdele t := by
    classical
    simp only [signIdele, Pi.mul_apply, map_mul, Finset.prod_mul_distrib]
  change (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)) (signIdele (s * t)) = _
  rw [hid, map_mul]
  rfl

omit [NumberField.IsTotallyReal K] in
/-- The finite component of a sign idèle is one; used by the signed generator comparison. -/
private theorem signIdele_finiteComponent (ε : InfinitePlace K → ℤˣ)
    (v : HeightOneSpectrum (𝓞 K)) : IdeleGroup.finiteComponent K v (signIdele ε) = 1 := by
  rw [signIdele, map_prod]
  simp only [IdeleGroup.finiteComponent_ofCompletion, Finset.prod_const_one]

omit [NumberField.IsTotallyReal K] in
/-- The infinite component of a sign idèle is its prescribed sign; used by the signed generator
comparison. -/
private theorem signIdele_infiniteComponent (ε : InfinitePlace K → ℤˣ)
    (w : InfinitePlace K) : IdeleGroup.infiniteComponent K w (signIdele ε) =
      Units.map (Int.castRingHom w.Completion : ℤ →* w.Completion) (ε w) := by
  classical
  rw [signIdele, map_prod]
  rw [Finset.prod_eq_single w]
  · exact IdeleGroup.infiniteComponent_ofCompletion_self K w _
  · intro v _ hv
    exact IdeleGroup.infiniteComponent_ofCompletion_of_ne K w v (Ne.symm hv) _
  · simp

omit [NumberField.IsTotallyReal K] in
/-- A sign idèle has trivial fractional ideal; used by the signed generator comparison. -/
private theorem signIdele_toFractionalIdeal (ε : InfinitePlace K → ℤˣ) :
    IdeleGroup.toFractionalIdeal (signIdele ε) = 1 := by
  apply (IdeleGroup.toFractionalIdeal_eq_one_iff _).mpr
  intro v
  rw [signIdele_finiteComponent]
  simp

omit [NumberField K] in
/-- The prescribed local sign maps to the same real sign. -/
private theorem InfinitePlace.real_sign (w : InfinitePlace K) (e : ℤˣ) :
    InfinitePlace.Completion.extensionEmbeddingOfIsReal
      (NumberField.IsTotallyReal.isReal w)
      ((Units.map (Int.castRingHom w.Completion : ℤ →* w.Completion) e :
        w.Completionˣ) : w.Completion) = (e : ℝ) := by
  change (InfinitePlace.Completion.extensionEmbeddingOfIsReal
    (NumberField.IsTotallyReal.isReal w)) ((e : ℤ) : w.Completion) = ((e : ℤ) : ℝ)
  exact map_intCast _ _

/-- Positivity of a principal idèle times a local sign is the prescribed signed positivity. -/
private theorem InfinitePlace.unitEmbedding_mul_sign_positive_iff
    (w : InfinitePlace K) (e : ℤˣ) (c : Kˣ) :
    Units.map (algebraMap K w.Completion) c *
        Units.map (Int.castRingHom w.Completion : ℤ →* w.Completion) e ∈
      InfinitePlace.positiveUnitGroup w ↔
        0 < (e : ℝ) * realEmbeddingAt K w (c : K) := by
  let hw := NumberField.IsTotallyReal.isReal w
  have hval : InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
      (((Units.map (algebraMap K w.Completion) c) *
        Units.map (Int.castRingHom w.Completion : ℤ →* w.Completion) e :
          w.Completionˣ) : w.Completion) =
      (e : ℝ) * realEmbeddingAt K w (c : K) := by
    rw [Units.val_mul, map_mul, InfinitePlace.extensionEmbeddingOfIsReal_units_map,
      InfinitePlace.real_sign, mul_comm]
  rw [InfinitePlace.mem_positiveUnitGroup_iff]
  exact ⟨fun h ↦ hval ▸ h hw, fun h _ ↦ hval.symm ▸ h⟩

omit [NumberField.IsTotallyReal K] in
/-- The square of a sign idèle class lies in every narrow ray subgroup. -/
theorem signIdeleClass_sq_mem (ε : InfinitePlace K → ℤˣ) (m : Ideal (𝓞 K)) :
    signIdeleClass ε ^ 2 ∈ IdeleClassGroup.raySubgroup Set.univ m := by
  have hs : signIdele ε ^ 2 = 1 := by
    change (∏ w, NumberField.IdeleGroup.ofCompletion (𝓞 K) K w
      (Units.map (Int.castRingHom w.Completion : ℤ →* w.Completion) (ε w))) ^ 2 = 1
    rw [← Finset.prod_pow]
    apply Finset.prod_eq_one
    intro w _
    change (NumberField.IdeleGroup.ofCompletion (𝓞 K) K w
      (Units.map (Int.castRingHom w.Completion : ℤ →* w.Completion) (ε w))) ^ 2 = 1
    rw [← map_pow, ← map_pow, Int.units_sq, map_one, map_one]
  change (signIdele ε : NumberField.IdeleClassGroup (𝓞 K) K) ^ 2 ∈ _
  rw [← QuotientGroup.mk_pow, hs, QuotientGroup.mk_one]
  exact (IdeleClassGroup.raySubgroup Set.univ m).one_mem

/-! ### The narrow ray class field -/

omit [NumberField K] in
/-- The positive units at a real completion have finite index; used to compare the narrow and
selected-place ray subgroups. -/
private theorem InfinitePlace.positiveUnitGroup_finiteIndex (w : InfinitePlace K) :
    (InfinitePlace.positiveUnitGroup w).FiniteIndex := by
  let hw := NumberField.IsTotallyReal.isReal w
  have hreal : (Units.posSubgroup ℝ).FiniteIndex := by
    rw [Subgroup.finiteIndex_iff, Units.index_posSubgroup]
    decide
  let f : w.Completionˣ →* ℝˣ :=
    Units.map (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw).toMonoidHom
  have heq : InfinitePlace.positiveUnitGroup w =
      (Units.posSubgroup ℝ).comap f := by
    ext x
    simp only [InfinitePlace.mem_positiveUnitGroup_iff, Subgroup.mem_comap,
      Units.mem_posSubgroup]
    exact ⟨fun h ↦ h hw, fun h _ ↦ h⟩
  rw [heq]
  let : (Units.posSubgroup ℝ).FiniteIndex := hreal
  infer_instance

/-- The narrow ray idèles have finite relative index in the selected-place ray idèles; used by
`IdeleClassGroup.raySubgroup_univ_finiteIndex`. -/
private theorem IdeleGroup.raySubgroup_univ_isFiniteRelIndex
    (v : InfinitePlace K) (m : Ideal (𝓞 K)) :
    (IdeleGroup.raySubgroup (Set.univ : Set (InfinitePlace K)) m).IsFiniteRelIndex
      (IdeleGroup.raySubgroup (InfinitePlace.raySupport v) m) := by
  let V := IdeleGroup.raySubgroup (InfinitePlace.raySupport v) m
  let f : V →* v.Completionˣ :=
    (IdeleGroup.infiniteComponent K v).comp V.subtype
  have heq : (IdeleGroup.raySubgroup Set.univ m).subgroupOf V =
      (InfinitePlace.positiveUnitGroup v).comap f := by
    ext x
    constructor
    · intro hx
      change (IdeleGroup.infiniteComponent K v) (x : NumberField.IdeleGroup (𝓞 K) K) ∈
        InfinitePlace.positiveUnitGroup v
      simpa only [InfinitePlace.rayUnitGroup_univ] using
        ((IdeleGroup.mem_raySubgroup_iff Set.univ m x).mp hx).1 v
    · intro hx
      apply (IdeleGroup.mem_raySubgroup_iff Set.univ m x).mpr
      refine ⟨?_, ((IdeleGroup.mem_raySubgroup_iff _ m x).mp x.property).2⟩
      intro w
      rw [InfinitePlace.rayUnitGroup_univ]
      by_cases hw : w = v
      · subst w
        exact hx
      · have h := ((IdeleGroup.mem_raySubgroup_iff _ m x).mp x.property).1 w
        simpa [InfinitePlace.raySupport, hw] using h
  rw [Subgroup.isFiniteRelIndex_iff_finiteIndex, heq]
  have hpositive := InfinitePlace.positiveUnitGroup_finiteIndex v
  let : (InfinitePlace.positiveUnitGroup v).FiniteIndex := hpositive
  infer_instance

/-- The narrow ray subgroup of a nonzero modulus has finite index in $C_K$. Milne, *Class Field
Theory*, Chapter V, Theorem 1.7 and Proposition 4.6. -/
theorem IdeleClassGroup.raySubgroup_univ_finiteIndex (F : RealQuadraticFieldData K)
    {m : Ideal (𝓞 K)} (hm : m ≠ ⊥) :
    (IdeleClassGroup.raySubgroup (Set.univ : Set (InfinitePlace K)) m).FiniteIndex := by
  let q := QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K)
  have hrel := (IdeleGroup.raySubgroup_univ_isFiniteRelIndex F.place m).map q
  change (IdeleClassGroup.raySubgroup Set.univ m).IsFiniteRelIndex
    (IdeleClassGroup.raySubgroup (InfinitePlace.raySupport F.place) m) at hrel
  have hselected := IdeleClassGroup.raySubgroup_finiteIndex F hm
  exact Subgroup.isFiniteRelIndex_top_iff.mp
    (hrel.trans (Subgroup.isFiniteRelIndex_top_iff.mpr hselected))

/-- **Existence of the narrow ray class field**: for a nonzero modulus `m` there is a finite
abelian extension `H/K` whose norm group is the ray subgroup positive at every real place.
Milne, *Class Field Theory*, Chapter V, Theorem 5.5, for the modulus
$\mathfrak m\infty_1\infty_2$; by Childress, *Class Field Theory*, Chapter VI, Theorem 2.7. -/
theorem exists_narrowRayClassField (F : RealQuadraticFieldData K) {m : Ideal (𝓞 K)}
    (hm : m ≠ ⊥) :
    ∃ (H : IntermediateField K (AlgebraicClosure K)) (_ : NumberField H), IsAbelianGalois K H ∧
      (IdeleClassGroup.norm (K := K) (L := H)).range =
        IdeleClassGroup.raySubgroup Set.univ m := by
  let U := IdeleClassGroup.raySubgroup Set.univ m
  have : U.FiniteIndex := IdeleClassGroup.raySubgroup_univ_finiteIndex F hm
  have hS : IdeleGroup.awayUnitSubgroup (FinitePlace.modulusSupport m) ≤
      U.comap (QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K)) :=
    (awayUnitSubgroup_le_rayIdeleSubgroup Set.univ m).trans
      (Subgroup.le_comap_map _ _)
  exact exists_intermediateField_range_norm_eq U (FinitePlace.modulusSupport m) hS

/-! ### Frobenius in the narrow ray class field

The relation between a uniformizer and a sign idèle is read componentwise: its fractional ideal
gives an integral generator, its finite components give the congruence, and its infinite
components give the signs. The converse assembles these conditions into a ray idèle. -/

omit [NumberField.IsTotallyReal K] in
/-- The fractional ideal of the principal factor in a signed ray-idèle relation is the prime
ideal; it therefore has an integral generator. Used by `signedGenerator_of_ray_idele_relation`. -/
private theorem integral_generator_of_ray_idele_relation {m : Ideal (𝓞 K)}
    (ε : InfinitePlace K → ℤˣ) {v : HeightOneSpectrum (𝓞 K)}
    (π : (v.adicCompletion K)ˣ)
    (hπ : Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ))
    (u : NumberField.IdeleGroup (𝓞 K) K) (hu : u ∈ IdeleGroup.raySubgroup Set.univ m)
    (c : Kˣ) (hrel : NumberField.IdeleGroup.unitEmbedding (𝓞 K) K c =
      u⁻¹ * (NumberField.IdeleGroup.ofAdicCompletion (𝓞 K) K v π *
        (signIdele ε)⁻¹)) :
    ∃ α : 𝓞 K, v.asIdeal = Ideal.span {α} ∧ (c : K) = (α : K) := by
  have huideal : IdeleGroup.toFractionalIdeal u = 1 :=
    ((IdeleGroup.finite_ray_iff_congruent_and_ideal m u).mp
      ((IdeleGroup.mem_raySubgroup_iff Set.univ m u).mp hu).2).2
  have hprincipal : IdeleGroup.toFractionalIdeal
      (NumberField.IdeleGroup.unitEmbedding (𝓞 K) K c) =
        IdeleGroup.toFractionalIdeal
          (NumberField.IdeleGroup.ofAdicCompletion (𝓞 K) K v π) := by
    rw [hrel]
    simp only [map_mul, map_inv, huideal, signIdele_toFractionalIdeal, inv_one,
      one_mul, mul_one]
  have hfrac : FractionalIdeal.spanSingleton (𝓞 K)⁰ (c : K) =
      ((v.asIdeal : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
    have h := congrArg (fun z : (FractionalIdeal (𝓞 K)⁰ K)ˣ ↦
      (z : FractionalIdeal (𝓞 K)⁰ K)) hprincipal
    simpa only [IdeleGroup.coe_toFractionalIdeal_unitEmbedding,
      IdeleGroup.coe_toFractionalIdeal_ofAdicCompletion_uniformizer v π hπ] using h
  have hc_mem : (c : K) ∈
      ((v.asIdeal : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [← hfrac]
    exact FractionalIdeal.mem_spanSingleton_self _ _
  obtain ⟨α, _, hα⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp hc_mem
  refine ⟨α, ?_, hα.symm⟩
  apply FractionalIdeal.coeIdeal_injective (K := K)
  calc
    ((v.asIdeal : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (c : K) := hfrac.symm
    _ = FractionalIdeal.spanSingleton (𝓞 K)⁰ (α : K) := by rw [← hα]
    _ = ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) :=
      (FractionalIdeal.coeIdeal_span_singleton α).symm

/-- The infinite component of a narrow ray-idèle relation determines the prescribed sign;
used by `signedGenerator_of_ray_idele_relation`. -/
private theorem signed_sign_of_ray_idele_relation {m : Ideal (𝓞 K)}
    (ε : InfinitePlace K → ℤˣ) {v : HeightOneSpectrum (𝓞 K)}
    (π : (v.adicCompletion K)ˣ)
    (u : NumberField.IdeleGroup (𝓞 K) K) (hu : u ∈ IdeleGroup.raySubgroup Set.univ m)
    (c : Kˣ) (hrel : NumberField.IdeleGroup.unitEmbedding (𝓞 K) K c =
      u⁻¹ * (NumberField.IdeleGroup.ofAdicCompletion (𝓞 K) K v π *
        (signIdele ε)⁻¹)) (w : InfinitePlace K) :
    0 < (ε w : ℝ) * realEmbeddingAt K w (c : K) := by
  have huinf : IdeleGroup.infiniteComponent K w u ∈
      InfinitePlace.positiveUnitGroup w := by
    simpa only [InfinitePlace.rayUnitGroup_univ] using
      ((IdeleGroup.mem_raySubgroup_iff Set.univ m u).mp hu).1 w
  have hcomponent : Units.map (algebraMap K w.Completion) c *
      Units.map (Int.castRingHom w.Completion : ℤ →* w.Completion) (ε w) =
      (IdeleGroup.infiniteComponent K w u)⁻¹ := by
    have h := congrArg (IdeleGroup.infiniteComponent K w) hrel
    simp only [IdeleGroup.infiniteComponent_unitEmbedding, map_mul, map_inv,
      IdeleGroup.infiniteComponent_ofAdicCompletion,
      signIdele_infiniteComponent, one_mul] at h
    calc
      _ = ((IdeleGroup.infiniteComponent K w u)⁻¹ *
          (Units.map (Int.castRingHom w.Completion : ℤ →* w.Completion) (ε w))⁻¹) *
            Units.map (Int.castRingHom w.Completion : ℤ →* w.Completion) (ε w) := by
              rw [h]
      _ = _ := by group
  exact (InfinitePlace.unitEmbedding_mul_sign_positive_iff w (ε w) c).mp
    (hcomponent ▸ (InfinitePlace.positiveUnitGroup w).inv_mem huinf)

omit [NumberField.IsTotallyReal K] in
/-- A prime dividing the modulus differs from a prime coprime to it. -/
private theorem modulus_prime_ne_coprime_prime {m : Ideal (𝓞 K)}
    {v q : HeightOneSpectrum (𝓞 K)} (hv : IsCoprime v.asIdeal m)
    (hq : FinitePlace.modulusExponent m q ≠ 0) : q ≠ v := by
  intro h
  subst q
  exact hq (FinitePlace.modulusExponent_eq_zero_of_isCoprime v hv)

/-- A principal relation between a ray idèle and a signed prime uniformizer gives a signed
ray generator; the ideal and local components supply the generator conditions. -/
private theorem signedGenerator_of_ray_idele_relation {m : Ideal (𝓞 K)}
    (ε : InfinitePlace K → ℤˣ) {v : HeightOneSpectrum (𝓞 K)}
    (hv : IsCoprime v.asIdeal m) (π : (v.adicCompletion K)ˣ)
    (hπ : Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ))
    (u : NumberField.IdeleGroup (𝓞 K) K) (hu : u ∈ IdeleGroup.raySubgroup Set.univ m)
    (c : Kˣ) (hrel : NumberField.IdeleGroup.unitEmbedding (𝓞 K) K c =
      u⁻¹ * (NumberField.IdeleGroup.ofAdicCompletion (𝓞 K) K v π *
        (signIdele ε)⁻¹)) : HasSignedRayGenerator m ε v.asIdeal := by
  have hm : m ≠ ⊥ := by
    intro h
    have htop : v.asIdeal = ⊤ := by
      simpa [h] using (Ideal.isCoprime_iff_sup_eq.mp hv)
    exact v.isPrime.ne_top htop
  obtain ⟨α, hideal, hcα⟩ :=
    integral_generator_of_ray_idele_relation ε π hπ u hu c hrel
  have hfin (q : HeightOneSpectrum (𝓞 K)) (hq : FinitePlace.modulusExponent m q ≠ 0) :
      Units.map (algebraMap K (q.adicCompletion K)) c ∈ FinitePlace.rayUnitGroup m q := by
    have hqv : q ≠ v := modulus_prime_ne_coprime_prime hv hq
    have hcomponent : Units.map (algebraMap K (q.adicCompletion K)) c =
        (IdeleGroup.finiteComponent K q u)⁻¹ := by
      have h := congrArg (IdeleGroup.finiteComponent K q) hrel
      simpa only [IdeleGroup.finiteComponent_unitEmbedding, map_mul, map_inv,
        IdeleGroup.finiteComponent_ofAdicCompletion_of_ne K v q hqv,
        signIdele_finiteComponent, inv_one, mul_one] using h
    rw [hcomponent]
    exact (FinitePlace.rayUnitGroup m q).inv_mem
      (((IdeleGroup.mem_raySubgroup_iff Set.univ m u).mp hu).2 q)
  refine ⟨α, hideal,
    FinitePlace.sub_mem_of_units_map_mem_rayUnitGroup hm (by simpa using hcα) hfin, ?_⟩
  intro w
  simpa only [hcα] using signed_sign_of_ray_idele_relation ε π u hu c hrel w

omit [NumberField.IsTotallyReal K] in
/-- At primes dividing the modulus, the idèle constructed from a congruent generator has a
finite ray component. Used by `signedGenerator_idele_mem_raySubgroup`. -/
private theorem signedGenerator_idele_finiteComponent {m : Ideal (𝓞 K)}
    (ε : InfinitePlace K → ℤˣ) {v : HeightOneSpectrum (𝓞 K)}
    (hv : IsCoprime v.asIdeal m) (π : (v.adicCompletion K)ˣ)
    {α : 𝓞 K} (hcong : α - 1 ∈ m) (c : Kˣ) (hcα : (c : K) = (α : K))
    (q : HeightOneSpectrum (𝓞 K)) (hq : FinitePlace.modulusExponent m q ≠ 0) :
    IdeleGroup.finiteComponent K q
      ((NumberField.IdeleGroup.unitEmbedding (𝓞 K) K c)⁻¹ *
        (NumberField.IdeleGroup.ofAdicCompletion (𝓞 K) K v π *
          (signIdele ε)⁻¹)) ∈ FinitePlace.rayUnitGroup m q := by
  have hqv : q ≠ v := modulus_prime_ne_coprime_prime hv hq
  have hcfin : Units.map (algebraMap K (q.adicCompletion K)) c ∈
      FinitePlace.rayUnitGroup m q :=
    FinitePlace.units_map_mem_rayUnitGroup_of_sub_one_mem hcα hcong hq
  have hcomponent : IdeleGroup.finiteComponent K q
      ((NumberField.IdeleGroup.unitEmbedding (𝓞 K) K c)⁻¹ *
        (NumberField.IdeleGroup.ofAdicCompletion (𝓞 K) K v π *
          (signIdele ε)⁻¹)) =
        (Units.map (algebraMap K (q.adicCompletion K)) c)⁻¹ := by
    simp only [map_mul, map_inv, IdeleGroup.finiteComponent_unitEmbedding,
      IdeleGroup.finiteComponent_ofAdicCompletion_of_ne K v q hqv,
      signIdele_finiteComponent, inv_one, mul_one]
  rw [hcomponent]
  exact (FinitePlace.rayUnitGroup m q).inv_mem hcfin

/-- At an infinite place, the idèle constructed from a signed generator has a positive
component. Used by `signedGenerator_idele_mem_raySubgroup`. -/
private theorem signedGenerator_idele_infiniteComponent
    (ε : InfinitePlace K → ℤˣ) {v : HeightOneSpectrum (𝓞 K)}
    (π : (v.adicCompletion K)ˣ) {α : 𝓞 K}
    (hpos : ∀ w : InfinitePlace K, 0 < (ε w : ℝ) * realEmbeddingAt K w (α : K))
    (c : Kˣ) (hcα : (c : K) = (α : K)) (w : InfinitePlace K) :
    IdeleGroup.infiniteComponent K w
      ((NumberField.IdeleGroup.unitEmbedding (𝓞 K) K c)⁻¹ *
        (NumberField.IdeleGroup.ofAdicCompletion (𝓞 K) K v π *
          (signIdele ε)⁻¹)) ∈ InfinitePlace.rayUnitGroup Set.univ w := by
  have hcpos : Units.map (algebraMap K w.Completion) c *
      Units.map (Int.castRingHom w.Completion : ℤ →* w.Completion) (ε w) ∈
        InfinitePlace.positiveUnitGroup w :=
    (InfinitePlace.unitEmbedding_mul_sign_positive_iff w (ε w) c).mpr
      (by simpa only [hcα] using hpos w)
  have hcomponent : IdeleGroup.infiniteComponent K w
      ((NumberField.IdeleGroup.unitEmbedding (𝓞 K) K c)⁻¹ *
        (NumberField.IdeleGroup.ofAdicCompletion (𝓞 K) K v π *
          (signIdele ε)⁻¹)) =
        (Units.map (algebraMap K w.Completion) c *
          Units.map (Int.castRingHom w.Completion : ℤ →* w.Completion) (ε w))⁻¹ := by
    simp only [map_mul, map_inv, IdeleGroup.infiniteComponent_unitEmbedding,
      IdeleGroup.infiniteComponent_ofAdicCompletion, signIdele_infiniteComponent,
      one_mul, mul_inv_rev]
    exact mul_comm _ _
  rw [InfinitePlace.rayUnitGroup_univ, hcomponent]
  exact (InfinitePlace.positiveUnitGroup w).inv_mem hcpos

/-- The idèle formed from a signed generator and a prime uniformizer lies in the narrow ray
subgroup; used by `ray_idele_relation_of_signedGenerator`. -/
private theorem signedGenerator_idele_mem_raySubgroup {m : Ideal (𝓞 K)}
    (ε : InfinitePlace K → ℤˣ) {v : HeightOneSpectrum (𝓞 K)}
    (hv : IsCoprime v.asIdeal m) (π : (v.adicCompletion K)ˣ)
    (hπ : Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ))
    (α : 𝓞 K) (hgen : v.asIdeal = Ideal.span {α}) (hcong : α - 1 ∈ m)
    (hpos : ∀ w : InfinitePlace K, 0 < (ε w : ℝ) * realEmbeddingAt K w (α : K))
    (c : Kˣ) (hcα : (c : K) = (α : K)) :
    (NumberField.IdeleGroup.unitEmbedding (𝓞 K) K c)⁻¹ *
      (NumberField.IdeleGroup.ofAdicCompletion (𝓞 K) K v π * (signIdele ε)⁻¹) ∈
        IdeleGroup.raySubgroup Set.univ m := by
  let p := NumberField.IdeleGroup.ofAdicCompletion (𝓞 K) K v π
  let s := signIdele ε
  let u := (NumberField.IdeleGroup.unitEmbedding (𝓞 K) K c)⁻¹ * (p * s⁻¹)
  have hprincipal : IdeleGroup.toFractionalIdeal
      (NumberField.IdeleGroup.unitEmbedding (𝓞 K) K c) =
        IdeleGroup.toFractionalIdeal p := by
    apply Units.ext
    simp only [p, IdeleGroup.coe_toFractionalIdeal_unitEmbedding,
      IdeleGroup.coe_toFractionalIdeal_ofAdicCompletion_uniformizer v π hπ,
      hcα, FractionalIdeal.coeIdeal_span_singleton, hgen]
  have huideal : IdeleGroup.toFractionalIdeal u = 1 := by
    simp only [u, map_mul, map_inv, hprincipal]
    simp only [s, signIdele_toFractionalIdeal, inv_one, mul_one, inv_mul_cancel]
  change u ∈ IdeleGroup.raySubgroup Set.univ m
  apply (IdeleGroup.mem_raySubgroup_iff Set.univ m u).mpr
  refine ⟨fun w => signedGenerator_idele_infiniteComponent ε π hpos c hcα w, ?_⟩
  exact (IdeleGroup.finite_ray_iff_congruent_and_ideal m u).mpr
    ⟨fun q hq => signedGenerator_idele_finiteComponent ε hv π hcong c hcα q hq, huideal⟩

/-- A signed ray generator yields a ray-idèle representative of its signed uniformizer class;
this is the converse component step of `isFrobeniusAt_globalArtin_signIdeleClass_iff`. -/
private theorem ray_idele_relation_of_signedGenerator {m : Ideal (𝓞 K)}
    (ε : InfinitePlace K → ℤˣ) {v : HeightOneSpectrum (𝓞 K)}
    (hv : IsCoprime v.asIdeal m) (π : (v.adicCompletion K)ˣ)
    (hπ : Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ))
    (h : HasSignedRayGenerator m ε v.asIdeal) :
    ∃ u ∈ IdeleGroup.raySubgroup Set.univ m,
      (u : NumberField.IdeleClassGroup (𝓞 K) K) =
        ((NumberField.IdeleGroup.ofAdicCompletion (𝓞 K) K v π *
          (signIdele ε)⁻¹ : NumberField.IdeleGroup (𝓞 K) K) :
            NumberField.IdeleClassGroup (𝓞 K) K) := by
  obtain ⟨α, hgen, hcong, hpos⟩ := h
  have hα0 : α ≠ 0 := by
    intro h
    have hbot : v.asIdeal = ⊥ := by simpa [h] using hgen
    exact v.ne_bot hbot
  let c : Kˣ := Units.mk0 (α : K) (RingOfIntegers.coe_ne_zero_iff.mpr hα0)
  have hcα : (c : K) = (α : K) := rfl
  let p := NumberField.IdeleGroup.ofAdicCompletion (𝓞 K) K v π
  let s := signIdele ε
  let u := (NumberField.IdeleGroup.unitEmbedding (𝓞 K) K c)⁻¹ * (p * s⁻¹)
  have huray : u ∈ IdeleGroup.raySubgroup Set.univ m :=
    signedGenerator_idele_mem_raySubgroup ε hv π hπ α hgen hcong hpos c hcα
  refine ⟨u, huray, ?_⟩
  change (u : NumberField.IdeleClassGroup (𝓞 K) K) =
    ((p * s⁻¹ : NumberField.IdeleGroup (𝓞 K) K) : NumberField.IdeleClassGroup (𝓞 K) K)
  simp only [u, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    IdeleClassGroup.coe_unitEmbedding, inv_one]
  change (1 : NumberField.IdeleClassGroup (𝓞 K) K) *
      ((p : NumberField.IdeleClassGroup (𝓞 K) K) *
        (s : NumberField.IdeleClassGroup (𝓞 K) K)⁻¹) =
      ((p : NumberField.IdeleClassGroup (𝓞 K) K) *
        (s : NumberField.IdeleClassGroup (𝓞 K) K)⁻¹)
  exact one_mul ((p : NumberField.IdeleClassGroup (𝓞 K) K) *
    (s : NumberField.IdeleClassGroup (𝓞 K) K)⁻¹)

/-- A prime uniformizer differs from the sign class by a narrow ray class exactly when its ideal
has a signed ray generator; used by the Frobenius criterion. -/
private theorem uniformizer_mul_sign_inv_mem_raySubgroup_iff
    {m : Ideal (𝓞 K)} (ε : InfinitePlace K → ℤˣ)
    {v : HeightOneSpectrum (𝓞 K)} (hv : IsCoprime v.asIdeal m)
    (π : (v.adicCompletion K)ˣ)
    (hπ : Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ)) :
    NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 K) K v π *
      (signIdeleClass ε)⁻¹ ∈ IdeleClassGroup.raySubgroup Set.univ m ↔
        HasSignedRayGenerator m ε v.asIdeal := by
  let p := NumberField.IdeleGroup.ofAdicCompletion (𝓞 K) K v π
  let s := signIdele ε
  have hclass : (p * s⁻¹ : NumberField.IdeleGroup (𝓞 K) K) =
      (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 K) K v π) *
        (signIdeleClass ε)⁻¹ := by
    rfl
  constructor
  · intro h
    obtain ⟨u, hu, huclass⟩ :=
      (IdeleClassGroup.mem_raySubgroup_iff Set.univ m _).mp (hclass ▸ h)
    have hp : u⁻¹ * (p * s⁻¹) ∈
        NumberField.IdeleGroup.principalSubgroup (𝓞 K) K :=
      QuotientGroup.eq.mp huclass
    obtain ⟨c, hc⟩ := hp
    exact signedGenerator_of_ray_idele_relation ε hv π hπ u hu c hc
  · intro h
    obtain ⟨u, hu, huclass⟩ := ray_idele_relation_of_signedGenerator ε hv π hπ h
    apply (IdeleClassGroup.mem_raySubgroup_iff Set.univ m _).mpr
    exact ⟨u, hu, huclass.trans hclass⟩

/-- In a field with the narrow ray norm group of modulus `m`, Frobenius at a prime coprime to `m`
is the Artin symbol of the sign class $\varepsilon$ exactly when the prime has a signed ray
generator with signs $\varepsilon$. Milne, *Class Field Theory*, Chapter V, Theorem 5.3 with
Proposition 4.6. -/
theorem isFrobeniusAt_globalArtin_signIdeleClass_iff {H : Type*} [Field H] [NumberField H]
    [Algebra K H] [IsAbelianGalois K H] {m : Ideal (𝓞 K)}
    (hU : (IdeleClassGroup.norm (K := K) (L := H)).range =
      IdeleClassGroup.raySubgroup Set.univ m)
    (ε : InfinitePlace K → ℤˣ) {v : HeightOneSpectrum (𝓞 K)} (hv : IsCoprime v.asIdeal m)
    (w : HeightOneSpectrum (𝓞 H)) [w.asIdeal.LiesOver v.asIdeal] :
    IsFrobeniusAt K H (globalArtin H (signIdeleClass ε)) v.asIdeal w.asIdeal ↔
      HasSignedRayGenerator m ε v.asIdeal := by
  have hunr : w.asIdeal.ramificationIdx (𝓞 K) = 1 :=
    rayNorm_ramificationIdx_one Set.univ m hU v hv w
  let I : RayIdeal K m := ⟨v.asIdeal, v.ne_bot, hv⟩
  have hnot : v ∉ FinitePlace.ramifiedSet K H := by
    simpa only [I] using rayNorm_notMem_ramifiedSet Set.univ m hU I v.isPrime
  obtain ⟨π, hπ⟩ := FinitePlace.exists_valued_eq_exp_neg_one v
  have hFrob : globalArtin H
      (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 K) K v π) = frobeniusAt H v :=
    globalArtin_ofAdicCompletion v hnot π hπ
  constructor
  · intro h
    have heq := hFrob.trans (h.eq_frobeniusAt hunr).symm
    have hker : NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 K) K v π *
        (signIdeleClass ε)⁻¹ ∈ (globalArtin H).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, heq, mul_inv_cancel]
    rw [ker_globalArtin (K := K) (L := H), hU] at hker
    exact (uniformizer_mul_sign_inv_mem_raySubgroup_iff ε hv π hπ).mp hker
  · intro h
    have hker := (uniformizer_mul_sign_inv_mem_raySubgroup_iff ε hv π hπ).mpr h
    rw [← hU, ← ker_globalArtin (K := K) (L := H), MonoidHom.mem_ker,
      map_mul, map_inv] at hker
    have heq : globalArtin H (signIdeleClass ε) = frobeniusAt H v := by
      rw [← (mul_inv_eq_one.mp hker), hFrob]
    rw [heq]
    exact isFrobeniusAt_frobeniusAt v w.asIdeal

/-- **The exact ideal kernel**: in a field with the narrow ray norm group of modulus `m`, a prime
coprime to `m` has trivial Frobenius exactly when it has a totally positive generator
$\alpha\equiv1\pmod{\mathfrak m}$. Milne, *Class Field Theory*, Chapter V, Theorem 5.3 with
Proposition 4.6. -/
theorem isFrobeniusAt_one_iff_hasSignedRayGenerator {H : Type*} [Field H] [NumberField H]
    [Algebra K H] [IsAbelianGalois K H] {m : Ideal (𝓞 K)}
    (hU : (IdeleClassGroup.norm (K := K) (L := H)).range =
      IdeleClassGroup.raySubgroup Set.univ m)
    {v : HeightOneSpectrum (𝓞 K)} (hv : IsCoprime v.asIdeal m)
    (w : HeightOneSpectrum (𝓞 H)) [w.asIdeal.LiesOver v.asIdeal] :
    IsFrobeniusAt K H 1 v.asIdeal w.asIdeal ↔ HasSignedRayGenerator m 1 v.asIdeal := by
  have hsign : signIdeleClass (1 : InfinitePlace K → ℤˣ) = 1 := by
    simp [signIdeleClass, signIdele]
  simpa only [hsign, map_one] using
    (isFrobeniusAt_globalArtin_signIdeleClass_iff hU
      (1 : InfinitePlace K → ℤˣ) hv w)

end SIC

end
