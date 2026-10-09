/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Reciprocity.AuxiliaryFields.Construction
import SICs.ClassField.Reciprocity.AuxiliaryFields.Norms

/-!
# Cyclic Artin reciprocity

For a cyclic extension `L/K` and a modulus `m` divisible by the ramified primes with
$E^+_{K,\mathfrak m}\subseteq K^\times N_{L/K}J_L$, every congruent idèle in the kernel of the
Artin map is a norm residue. The Artin map vanishes on principal congruent idèles: Artin
reciprocity
for cyclic extensions.

This module proves Childress, *Class Field Theory* (2009), Chapter V, Proposition 2.2, in idèlic
form, and with it Theorem 2.1(ii) for cyclic extensions, pp. 114–123. It completes the comparison of
`SICs.ClassField.Reciprocity.CongruentIdeles`: `IdeleGroup.artinMap_toPrincipalIdeal_eq_one_of_le`
turns Proposition 2.2 into the reciprocity law. Childress's $\ker\mathcal A\subseteq\mathcal
P^+_{F,\mathfrak m}\mathcal N_{K/F}(\mathfrak m)$ becomes: the uniformizer idèle of an ideal prime
to `m` with trivial Artin symbol lies in $K^\times N_{L/K}J_L$.

## The argument

*Reduction to ideals.* A congruent idèle `y` is a unit at the primes of `m`, so its fractional
ideal `J` is prime to them, and `y` differs from the uniformizer idèle of `J` by a ray idèle
(`IdeleGroup.mul_inv_mem_raySubgroup`), which is a norm by hypothesis.

*Auxiliary data.* Let `T` be the finite set of primes of `J`, outside the support `S` of `m`, and
`σ` a generator of $\operatorname{Gal}(L/K)$, of order $n = [L:K]$. Choose `M` prime to the
discriminant of `L` and to the norms of the primes of `T`, and a unit `t` modulo `M`
independent of every $N\mathfrak p$, $\mathfrak p\in T$ (`exists_isIndependentResidue_of_finset`).
In $\Omega = L(\zeta_M)$ (`CyclotomicField M L`), abelian over `K` with group
$\operatorname{Gal}(L/K)\times(\mathbb Z/M\mathbb Z)^\times$
(`finrank_of_isCoprime_discr`, `bijective_restrictNormal_prod_autToPow`) and
unramified outside $S' = S\cup\{\mathfrak p\mid M\}$, Artin's lemma (`exists_auxiliaryFields`)
gives fields $E_{\mathfrak p}$ and an automorphism `g` fixing all of them with $g|_L = \sigma$.
A common norm `b` of the $E_{\mathfrak p}$ has $\psi_{L/K}(b) = \sigma$
(`exists_relNorm_eq_of_mem_fixingSubgroup`, `artinMap_restrictNormal`).

*The kernel.* Let `D` be the set of ideals `I` prime to $S'$ such that the uniformizer idèle of
$I b^{-k}$ lies in $K^\times N_{L/K}J_L$ whenever $\psi_{L/K}(I) = \sigma^k$. It is a subgroup:
the conditions for different `k` agree because $b^n = N_{L/K}(bO_L)$ is a norm
(`IdeleGroup.norm_inclusion`), and products add exponents. Each $\mathfrak p\in T$ lies in `D`:
$\mathfrak p = N_{E_{\mathfrak p}/K}\mathfrak P$ for a prime $\mathfrak P$ of residue degree one,
$b = N_{E_{\mathfrak p}/K}B_{\mathfrak p}$, so $\mathfrak p b^{-k}$ is the norm of
$A = \mathfrak P B_{\mathfrak p}^{-k}$ with trivial Artin symbol, and
`IdeleGroup.norm_ofFractionalIdeal_mem_of_le_sup_adjoin` applies; the uniformizer idèle of
$N_{E_{\mathfrak p}/K}A$ differs from the norm of that of `A` by a ray idèle. Hence `J`, generated
by the primes of `T`, lies in `D`, and $\psi_{L/K}(J) = 1 = \sigma^0$ gives the claim. This is
Childress's computation $\mathfrak a(\mathfrak b^{-d})^n\in\mathcal P^+\mathcal N$ organized
prime by prime.

*Reciprocity.* With Proposition 2.2, `IdeleGroup.artinMap_toPrincipalIdeal_eq_one_of_le` gives
$\psi^S((\alpha)) = 1$ for every principal congruent idèle.
-/

noncomputable section

open IsDedekindDomain NumberField
open scoped nonZeroDivisors

namespace SIC.IdeleGroup

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]

/-! ### Childress's Proposition 2.2 -/

/-- A single cyclotomic modulus avoids the discriminant and the primes in `T` while carrying
Childress's independent residue; used by `ofFractionalIdeal_mem_of_artinMap_eq_one`. -/
private theorem exists_auxiliaryModulus (T : Finset (HeightOneSpectrum (𝓞 K)))
    {n : ℕ} (hn : 0 < n) :
    ∃ M : ℕ, 0 < M ∧ IsCoprime (NumberField.discr L) (M : ℤ) ∧
      (∀ p ∈ T, (M : 𝓞 K) ∉ p.asIdeal) ∧
      ∃ t : (ZMod M)ˣ,
        ∀ p ∈ T, IsIndependentResidue n (Ideal.absNorm p.asIdeal) t := by
  let N := (NumberField.discr L).natAbs * ∏ p ∈ T, Ideal.absNorm p.asIdeal
  have hN : N ≠ 0 := by
    apply mul_ne_zero
    · exact Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero L)
    · exact (Finset.prod_pos (fun p _ ↦
        lt_trans zero_lt_one (HeightOneSpectrum.one_lt_absNorm p))).ne'
  obtain ⟨M, hM, hcop, t, hind⟩ := exists_isIndependentResidue_of_finset T
    (fun p _ ↦ HeightOneSpectrum.one_lt_absNorm p) hn hN
  have hdiscr : IsCoprime (NumberField.discr L) (M : ℤ) := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    simpa only [Int.natAbs_natCast] using
      (Nat.Coprime.of_dvd_right (dvd_mul_right _ _) hcop).symm
  have hMnot (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ T) : (M : 𝓞 K) ∉ p.asIdeal := by
    have hpdiv : Ideal.absNorm p.asIdeal ∣ N := by
      change Ideal.absNorm p.asIdeal ∣
        (NumberField.discr L).natAbs * ∏ q ∈ T, Ideal.absNorm q.asIdeal
      exact dvd_mul_of_dvd_right
        (Finset.dvd_prod_of_mem (fun q : HeightOneSpectrum (𝓞 K) ↦
          Ideal.absNorm q.asIdeal) hp) (NumberField.discr L).natAbs
    have hpnorm : (Ideal.absNorm p.asIdeal).Coprime M :=
      (Nat.Coprime.of_dvd_right hpdiv hcop).symm
    exact (absNorm_coprime_iff_natCast_notMem p).mp hpnorm
  exact ⟨M, hM, hdiscr, hMnot, t, hind⟩

variable [Algebra K L]

/-- Enlarging the support by the primes dividing `M` preserves unramifiedness in
`CyclotomicField M L` and keeps the chosen primes outside; used by
`ofFractionalIdeal_mem_of_artinMap_eq_one`. -/
private theorem exists_enlargedSupport {M : ℕ} [NeZero M] (m : Ideal (𝓞 K))
    (hS : FinitePlace.ramifiedSet K L ⊆ FinitePlace.modulusSupport m)
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hTS : ∀ p ∈ T, p ∉ FinitePlace.modulusSupport m)
    (hMnot : ∀ p ∈ T, (M : 𝓞 K) ∉ p.asIdeal) :
    ∃ S' : Finset (HeightOneSpectrum (𝓞 K)),
      FinitePlace.modulusSupport m ⊆ S' ∧
      (∀ v : HeightOneSpectrum (𝓞 K), (M : 𝓞 K) ∈ v.asIdeal → v ∈ S') ∧
      (∀ p ∈ T, p ∉ S') ∧
      FinitePlace.ramifiedSet K (CyclotomicField M L) ⊆ S' := by
  classical
  let S' := FinitePlace.modulusSupport m ∪
    FinitePlace.modulusSupport (Ideal.span {(M : 𝓞 K)})
  have hSS' : FinitePlace.modulusSupport m ⊆ S' := Finset.subset_union_left
  have hspan : Ideal.span {(M : 𝓞 K)} ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr (by exact_mod_cast NeZero.ne M)
  have hMS (v : HeightOneSpectrum (𝓞 K)) (hv : (M : 𝓞 K) ∈ v.asIdeal) : v ∈ S' := by
    apply Finset.mem_union_right
    exact FinitePlace.mem_modulusSupport_of_le hspan
      ((Ideal.span_singleton_le_iff_mem v.asIdeal).mpr hv)
  have hTout (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ T) : p ∉ S' := by
    intro hp'
    rcases Finset.mem_union.mp hp' with hs | hm
    · exact hTS p hp hs
    · have hle : Ideal.span {(M : 𝓞 K)} ≤ p.asIdeal :=
        (FinitePlace.mem_modulusSupport_iff_le hspan).mp hm
      exact hMnot p hp ((Ideal.span_singleton_le_iff_mem p.asIdeal).mp hle)
  refine ⟨S', hSS', hMS, hTout, ?_⟩
  apply (FinitePlace.ramifiedSet_subset_iff S').mpr
  intro w hw
  apply IsCyclotomicExtension.ramificationIdx_eq_one_of_below
    (K := K) (L := L) (Ω := CyclotomicField M L) (M := M) w
  · apply FinitePlace.ramificationIdx_eq_one_of_ramifiedSet_subset hS
    rw [FinitePlace.below_below]
    intro hv
    exact hw (Finset.mem_union_left _ hv)
  · intro hm
    exact hw (hMS _ hm)

/-- The uniformizer idèle of an ideal norm is a norm residue when the corresponding idèlic norm
is a norm residue.
This is the ray-idèle comparison used for each auxiliary prime in
`ofFractionalIdeal_mem_of_artinMap_eq_one`. -/
private theorem ofFractionalIdeal_relNorm_mem_of_norm_mem (m : Ideal (𝓞 K))
    (hray : raySubgroup Set.univ m ≤
      NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔
        (norm (K := K) (L := L)).range)
    {E : Type*} [Field E] [NumberField E] [Algebra K E]
    {A : (FractionalIdeal (𝓞 E)⁰ E)ˣ}
    (hA : A ∈ FractionalIdeal.primeTo E
      (FinitePlace.placesAbove (K := K) (L := E) (FinitePlace.modulusSupport m)))
    (hNorm : norm (K := K) (L := E) (ofFractionalIdeal A) ∈
      NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔
        (norm (K := K) (L := L)).range) :
    ofFractionalIdeal (FractionalIdeal.relNorm K A) ∈
      NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔
        (norm (K := K) (L := L)).range := by
  let X := NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔
    (norm (K := K) (L := L)).range
  have hAS : FractionalIdeal.relNorm K A ∈
      FractionalIdeal.primeTo K (FinitePlace.modulusSupport m) :=
    FractionalIdeal.relNorm_mem_primeTo _ hA
  have hRay := mul_inv_mem_raySubgroup Set.univ m
    (norm_ofFractionalIdeal_mem_congruentSubgroup m hA)
    (ofFractionalIdeal_mem_congruentSubgroup Set.univ m hAS)
    (by rw [toFractionalIdeal_norm, toFractionalIdeal_ofFractionalIdeal,
      toFractionalIdeal_ofFractionalIdeal])
  have hRayX : norm (K := K) (L := E) (ofFractionalIdeal A) *
      (ofFractionalIdeal (FractionalIdeal.relNorm K A))⁻¹ ∈ X :=
    hray hRay
  have h := X.mul_mem (X.inv_mem hRayX) hNorm
  convert h using 1
  simp [mul_inv_rev, mul_comm, mul_left_comm]

section Cyclic

variable [IsAbelianGalois K L]

/-- The subgroup used in `ofFractionalIdeal_mem_of_artinMap_eq_one`. An ideal belongs when it is
prime to `S` and one Artin exponent `k` makes the idèle of `I b⁻ᵏ` a norm residue. Once
`ofFractionalIdeal (b ^ [L : K])` is a norm, this is equivalent to Childress's condition for
every exponent `k`. -/
private def artinKernelAuxSubgroup (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L) (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (X : Subgroup (NumberField.IdeleGroup (𝓞 K) K)) :
    Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ where
  carrier := {I | I ∈ FractionalIdeal.primeTo K S ∧
    ∃ k : ℤ, artinMap L S I = σ ^ k ∧ ofFractionalIdeal (I * b ^ (-k)) ∈ X}
  one_mem' := by
    refine ⟨(FractionalIdeal.primeTo K S).one_mem, 0, ?_, ?_⟩ <;> simp
  mul_mem' := by
    intro I J hI hJ
    obtain ⟨hIS, k, hIk, hIX⟩ := hI
    obtain ⟨hJS, l, hJl, hJX⟩ := hJ
    refine ⟨(FractionalIdeal.primeTo K S).mul_mem hIS hJS, k + l, ?_, ?_⟩
    · rw [map_mul, hIk, hJl, zpow_add]
    · have h := X.mul_mem hIX hJX
      convert h using 1
      simp only [map_mul, map_zpow]
      rw [neg_add, zpow_add]
      ac_rfl
  inv_mem' := by
    intro I hI
    obtain ⟨hIS, k, hIk, hIX⟩ := hI
    refine ⟨(FractionalIdeal.primeTo K S).inv_mem hIS, -k, ?_, ?_⟩
    · rw [map_inv, hIk, zpow_neg]
    · have h := X.inv_mem hIX
      convert h using 1
      simp only [map_mul, map_zpow, map_inv, neg_neg, mul_inv_rev, zpow_neg, inv_inv]
      ac_rfl

variable [IsCyclic (L ≃ₐ[K] L)]

section AuxiliaryPrime

variable {Ω : Type*} [Field Ω] [NumberField Ω] [Algebra K Ω] [Algebra L Ω]
    [IsScalarTower K L Ω] [IsAbelianGalois K Ω]
    {M : ℕ} [NeZero M] {ζ : Ω} (hζ : IsPrimitiveRoot ζ M)
    (m : Ideal (𝓞 K)) (S' : Finset (HeightOneSpectrum (𝓞 K)))
    (hSS' : FinitePlace.modulusSupport m ⊆ S')
    (hΩ : FinitePlace.ramifiedSet K Ω ⊆ S')
    (hMS : ∀ v : HeightOneSpectrum (𝓞 K), (M : 𝓞 K) ∈ v.asIdeal → v ∈ S')
    (hray : raySubgroup Set.univ m ≤
      NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔
        (norm (K := K) (L := L)).range)
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (hb : artinMap L S' b = σ)
    (E : IntermediateField K Ω)
    (hE : (IsScalarTower.toAlgHom K L Ω).fieldRange ≤
      E ⊔ IntermediateField.adjoin K {ζ})
    {p : HeightOneSpectrum (𝓞 K)} (hp : p ∉ S')
    (hP : ∀ P : HeightOneSpectrum (𝓞 E), P.asIdeal.LiesOver p.asIdeal →
      P.asIdeal.inertiaDeg (𝓞 K) = 1)
    (B : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (hB : B ∈ FractionalIdeal.primeTo E
      (FinitePlace.placesAbove (K := K) (L := E) S'))
    (hNormB : FractionalIdeal.relNorm K B = b)

include hζ m hSS' hΩ hMS hray hgen hb E hE hp hP B hB hNormB

omit [IsCyclic (L ≃ₐ[K] L)] in
/-- Childress's auxiliary field at `p` puts the corresponding prime in
`artinKernelAuxSubgroup`; used by `ofFractionalIdeal_mem_of_artinMap_eq_one`. -/
private theorem prime_mem_artinKernelAuxSubgroup :
    primeFractionalIdeal K p ∈ artinKernelAuxSubgroup S' σ b
      (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔
        (norm (K := K) (L := L)).range) := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen (artinMap L S' (primeFractionalIdeal K p)))
  let P := FinitePlace.PrimeAbove.place (L := E) p (Classical.arbitrary _)
  have hPdeg : P.asIdeal.inertiaDeg (𝓞 K) = 1 := hP P inferInstance
  have hPnorm : FractionalIdeal.relNorm K (primeFractionalIdeal E P) =
      primeFractionalIdeal K p := by
    rw [FractionalIdeal.relNorm_primeFractionalIdeal p P, hPdeg, pow_one]
  have hPout : P ∉ FinitePlace.placesAbove (K := K) (L := E) S' := by
    simpa only [FinitePlace.mem_placesAbove, P, FinitePlace.PrimeAbove.below_place] using hp
  let A := primeFractionalIdeal E P * B ^ (-k)
  have hA : A ∈ FractionalIdeal.primeTo E
      (FinitePlace.placesAbove (K := K) (L := E) S') :=
    (FractionalIdeal.primeTo E _).mul_mem (primeFractionalIdeal_mem_primeTo hPout)
      ((FractionalIdeal.primeTo E _).zpow_mem hB (-k))
  have hNormA : FractionalIdeal.relNorm K A = primeFractionalIdeal K p * b ^ (-k) := by
    simp only [A, map_mul, map_zpow, hPnorm, hNormB]
  have hArtA : artinMap L S' (FractionalIdeal.relNorm K A) = 1 := by
    rw [hNormA, map_mul, map_zpow, ← hk, hb]
    simp
  have hNX := norm_ofFractionalIdeal_mem_of_le_sup_adjoin S' hΩ hMS hζ E hE hA hArtA
  have hAS : A ∈ FractionalIdeal.primeTo E
      (FinitePlace.placesAbove (K := K) (L := E) (FinitePlace.modulusSupport m)) :=
    (FractionalIdeal.primeTo_anti (K := E)) (by
      intro w hw
      exact (FinitePlace.mem_placesAbove S' w).2
        (hSS' ((FinitePlace.mem_placesAbove (FinitePlace.modulusSupport m) w).1 hw))) hA
  have hAX := ofFractionalIdeal_relNorm_mem_of_norm_mem m hray hAS hNX
  refine ⟨primeFractionalIdeal_mem_primeTo hp, k, hk.symm, ?_⟩
  rw [← hNormA]
  exact hAX

end AuxiliaryPrime

end Cyclic

variable [IsAbelianGalois K L]

/-- Childress's condition for one Artin exponent gives the kernel claim when `σ` generates the
cyclic Galois group; used by `ofFractionalIdeal_mem_of_artinMap_eq_one`. -/
private theorem ofFractionalIdeal_mem_of_auxKernel
    (S : Finset (HeightOneSpectrum (𝓞 K))) (σ : L ≃ₐ[K] L)
    (horder : orderOf σ = Module.finrank K L)
    (b J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hJ : J ∈ artinKernelAuxSubgroup S σ b
      (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔
        (norm (K := K) (L := L)).range))
    (hArt : artinMap L S J = 1) :
    ofFractionalIdeal J ∈ NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔
      (norm (K := K) (L := L)).range := by
  let X := NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔
    (norm (K := K) (L := L)).range
  obtain ⟨_, k, hJk, hJX⟩ := hJ
  have hk : (Module.finrank K L : ℤ) ∣ k := by
    rw [← horder]
    exact orderOf_dvd_iff_zpow_eq_one.mpr (hJk.symm.trans hArt)
  have hbnorm : (ofFractionalIdeal b) ^ Module.finrank K L ∈
      (norm (K := K) (L := L)).range :=
    ⟨inclusion (K := K) (L := L) (ofFractionalIdeal b), norm_inclusion _⟩
  have hbn : ofFractionalIdeal (b ^ Module.finrank K L) ∈ X := by
    simpa only [map_pow] using
      (le_sup_right : (norm (K := K) (L := L)).range ≤ X) hbnorm
  obtain ⟨l, hl⟩ := hk
  have hbk : ofFractionalIdeal (b ^ k) ∈ X := by
    rw [hl, zpow_mul, zpow_natCast, map_zpow]
    exact X.zpow_mem hbn l
  have h := X.mul_mem hJX hbk
  convert h using 1
  simp [map_mul, mul_comm, mul_left_comm]

variable [IsCyclic (L ≃ₐ[K] L)]

/-- **Childress's Proposition 2.2, for ideals**: for a cyclic extension `L/K`, a modulus `m`
whose support `S` contains the primes ramified in `L` and with
$E^+_{K,\mathfrak m}\subseteq K^\times N_{L/K}J_L$, the uniformizer idèle of every ideal `J`
prime to `S`
with $\psi^S_{L/K}(J) = 1$ lies in $K^\times N_{L/K}J_L$. Childress, *Class Field Theory*,
Chapter V, Proposition 2.2. -/
theorem ofFractionalIdeal_mem_of_artinMap_eq_one (m : Ideal (𝓞 K))
    (hS : FinitePlace.ramifiedSet K L ⊆ FinitePlace.modulusSupport m)
    (hray : raySubgroup Set.univ m ≤
      NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔
        (norm (K := K) (L := L)).range)
    {J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hJ : J ∈ FractionalIdeal.primeTo K (FinitePlace.modulusSupport m))
    (hArt : artinMap L (FinitePlace.modulusSupport m) J = 1) :
    ofFractionalIdeal J ∈
      NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔ (norm (K := K) (L := L)).range := by
  classical
  let S := FinitePlace.modulusSupport m
  let X := NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔
    (norm (K := K) (L := L)).range
  obtain ⟨T, hTcount, hJclosure⟩ := FractionalIdeal.exists_finset_mem_closure J
  have hTS (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ T) : p ∉ S := by
    intro hps
    exact hTcount p hp (hJ p hps)
  have hn : 0 < Module.finrank K L := Module.finrank_pos
  obtain ⟨σ, hgen⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  have horder : orderOf σ = Module.finrank K L :=
    (orderOf_eq_card_of_forall_mem_zpowers hgen).trans (IsGalois.card_aut_eq_finrank K L)
  obtain ⟨M, hM, hdiscr, hMnot, t, hind⟩ := exists_auxiliaryModulus (L := L) T hn
  let hNZ : NeZero M := ⟨hM.ne'⟩
  let Ω := CyclotomicField M L
  let ζ : Ω := IsCyclotomicExtension.zeta M L Ω
  have hζ : IsPrimitiveRoot ζ M := IsCyclotomicExtension.zeta_spec M L Ω
  have hdegree : Module.finrank L Ω = M.totient :=
    finrank_of_isCoprime_discr hdiscr
  let hAb : IsAbelianGalois K Ω :=
    isAbelianGalois_of_isCyclotomicExtension (K := K) (L := L) (Ω := Ω) (M := M)
  obtain ⟨S', hSS', hMS, hTout, hΩ⟩ :=
    exists_enlargedSupport (K := K) (L := L) (M := M) m hS T hTS hMnot
  obtain ⟨E, g, hgL, hgfix, hE, hP⟩ := exists_auxiliaryFields hζ
    (bijective_restrictNormal_prod_autToPow hζ hdegree).surjective T
    hMnot t hind σ
  obtain ⟨b, hbS, hbg, hB⟩ :=
    exists_relNorm_eq_of_mem_fixingSubgroup S' hΩ T E g hgfix
  have hbArt : artinMap L S' b = σ := by
    rw [← artinMap_restrictNormal (L := Ω) S' hΩ L b, hbg, hgL]
  let D := artinKernelAuxSubgroup S' σ b X
  have hD : Subgroup.closure (primeFractionalIdeal K '' (T : Set _)) ≤ D := by
    apply (Subgroup.closure_le D).mpr
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨B, hBS, hNormB⟩ := hB p hp
    exact prime_mem_artinKernelAuxSubgroup hζ m S' hSS' hΩ hMS hray σ hgen b hbArt
      (E p) (hE p hp) (hTout p hp) (hP p hp) B hBS hNormB
  have hJD : J ∈ D := hD hJclosure
  have hArt' : artinMap L S' J = 1 :=
    (artinMap_eq_of_mem_primeTo hSS' hJD.1).symm.trans hArt
  exact ofFractionalIdeal_mem_of_auxKernel S' σ horder b J hJD hArt'

/-- Derived from the ideal form `ofFractionalIdeal_mem_of_artinMap_eq_one`: for a cyclic
extension `L/K` and a modulus `m` whose
support `S` contains the primes ramified in `L` and with $E^+_{K,\mathfrak m}\subseteq
K^\times N_{L/K}J_L$, every congruent idèle `y` with $\psi^S_{L/K}((y)) = 1$ lies in
$K^\times N_{L/K}J_L$: $\ker\mathcal A\subseteq\mathcal P^+_{K,\mathfrak m}
\mathcal N_{L/K}(\mathfrak m)$ in idèlic form. Childress, *Class Field Theory*, Chapter V,
Proposition 2.2. -/
theorem mem_principal_sup_range_norm_of_artinMap_eq_one (m : Ideal (𝓞 K))
    (hS : FinitePlace.ramifiedSet K L ⊆ FinitePlace.modulusSupport m)
    (hray : raySubgroup Set.univ m ≤
      NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔
        (norm (K := K) (L := L)).range)
    {y : NumberField.IdeleGroup (𝓞 K) K} (hy : y ∈ congruentSubgroup Set.univ m)
    (hArt : artinMap L (FinitePlace.modulusSupport m) (toFractionalIdeal y) = 1) :
    y ∈ NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔ (norm (K := K) (L := L)).range := by
  let J := toFractionalIdeal y
  have hJ : J ∈ FractionalIdeal.primeTo K (FinitePlace.modulusSupport m) :=
    toFractionalIdeal_mem_primeTo Set.univ m hy
  have hray' : y * (ofFractionalIdeal J)⁻¹ ∈ raySubgroup Set.univ m :=
    mul_inv_mem_raySubgroup Set.univ m hy (ofFractionalIdeal_mem_congruentSubgroup Set.univ m hJ)
      (toFractionalIdeal_ofFractionalIdeal J).symm
  have hnorm := hray hray'
  simpa using Subgroup.mul_mem _ hnorm
    (ofFractionalIdeal_mem_of_artinMap_eq_one m hS hray hJ hArt)

/-! ### The reciprocity law -/

/-- **Artin reciprocity for cyclic extensions**: for a cyclic extension `L/K` and a modulus `m`
whose support `S` contains the primes ramified in `L` and with
$E^+_{K,\mathfrak m}\subseteq K^\times N_{L/K}J_L$, the Artin map vanishes on the principal
congruent
idèles: $\psi^S((\alpha)) = 1$ for $\alpha\equiv 1\pmod{\mathfrak m}$ totally positive.
Childress, *Class Field Theory*, Chapter V, Theorem 2.1(ii), for cyclic extensions. -/
theorem artinMap_toPrincipalIdeal_eq_one (m : Ideal (𝓞 K))
    (hS : FinitePlace.ramifiedSet K L ⊆ FinitePlace.modulusSupport m)
    (hray : raySubgroup Set.univ m ≤
      NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔
        (norm (K := K) (L := L)).range)
    (a : Kˣ) (ha : NumberField.IdeleGroup.unitEmbedding (𝓞 K) K a ∈ congruentSubgroup Set.univ m) :
    artinMap L (FinitePlace.modulusSupport m) (toPrincipalIdeal (𝓞 K) K a) = 1 :=
  artinMap_toPrincipalIdeal_eq_one_of_le m hS
    (fun _ hy hArt ↦ mem_principal_sup_range_norm_of_artinMap_eq_one m hS hray hy hArt) a ha

end SIC.IdeleGroup
