/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Splitting.Kummer

/-!
# Complete splitting in prime degree

If `L/K` is Galois of prime degree `p`, `v` is a finite place of `K`, and the image of
$K_v^\times$ in $C_K$ consists of norms from `L`, then `v` splits completely in `L`, by a
cyclotomic base change to the Kummer case.

This module follows Childress, *Class Field Theory* (2009), Chapter VI, proof of Theorem 3.1,
with Exercise 6.4. It supplies the prime-degree step of the unramifiedness theorem in
`SICs.ClassField.Splitting.UnramifiedPrimes`.

## The argument

Let $L' = L(\zeta_p)$ and $K' = K(\zeta_p)\subseteq L'$. Then $L' = LK'$ is abelian over `K`
(`IsAbelianGalois.sup`), and $[L':K']=p$ (`CyclotomicBaseChange.finrank_extension`), so every
element of $\operatorname{Gal}(L'/K')$ satisfies $\sigma^p = 1$.

*The hypothesis passes to $L'/K'$* (Childress's Exercise 6.4). For a place `w'` of `K'` above `v`
and $t\in K'^\times_{w'}$, the tower law (`restrictScalars_globalArtin`) and restriction
(`globalArtin_restrictNormal`) give
$\operatorname{Art}_{L'/K'}(\iota_{w'}t)|_L = \operatorname{Art}_{L/K}(N_{K'/K}\iota_{w'}t)
= \operatorname{Art}_{L/K}(\iota_v N_{K'_{w'}/K_v}t) = 1$
(`IdeleClassGroup.norm_ofAdicCompletion`, `ker_globalArtin`). Restriction to `L` is injective
on $\operatorname{Gal}(L'/K')$, so $\iota_{w'}t$ lies in $\ker\operatorname{Art}_{L'/K'} =
N_{L'/K'}C_{L'}$.

*Splitting in $L'/K'$ and descent.* Since $\mu_p\subset K'$, the Kummer case
(`FinitePlace.finrank_eq_one_of_pow_eq_one`) gives $[L'_u:K'_{w'}] = 1$ for every `u` above `w'`.
For a place `w` of `L` above `v`, choose `u` above `w` and let `w'` be the place of `K'` below
`u`. Local degrees multiply in towers (`FinitePlace.finrank_mul_finrank`), so $[L_w:K_v]$ divides
$[L'_u:K_v] = [K'_{w'}:K_v]$, which divides $[K':K]$, a divisor of $p-1$
(`FinitePlace.finrank_dvd_finrank`). It also divides `p`, so it is one.
-/

noncomputable section

open IsDedekindDomain NumberField
open scoped SIC.FinitePlace NumberField.LiesOver SIC.InfinitePlace IntermediateField

namespace SIC

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-! ### Restriction in the cyclotomic base change

The two lower fields generate $L(\zeta_p)$, so an automorphism over $K(\zeta_p)$ is
determined by its restriction to $L$. -/

/-- Restriction from $\operatorname{Gal}(L(\zeta_p)/K(\zeta_p))$ to
$\operatorname{Gal}(L/K)$, used by `cyclotomicRestrict_injective`. -/
private def cyclotomicRestrict [IsGalois K L] (p : ℕ) [Fact p.Prime] :
    (CyclotomicField p L ≃ₐ[CyclotomicBaseChange.base p K L] CyclotomicField p L) →*
      (L ≃ₐ[K] L) :=
  (AlgEquiv.restrictNormalHom L).comp (AlgEquiv.restrictScalarsHom K)

omit [NumberField K] in
/-- An automorphism over $K(\zeta_p)$ is determined by its restriction to $L$.
Used by `cyclotomic_exponent` and `cyclotomic_local_norm`; Childress, *Class Field Theory*,
Chapter VI, Exercise 6.4. -/
private theorem cyclotomicRestrict_injective [IsGalois K L] (p : ℕ) [Fact p.Prime] :
    Function.Injective (cyclotomicRestrict (K := K) (L := L) p) := by
  let E := CyclotomicBaseChange.base p K L
  let M := CyclotomicField p L
  let ζ := IsCyclotomicExtension.zeta p L M
  intro σ τ h
  have hL : (σ.restrictScalars K).restrictNormal L =
      (τ.restrictScalars K).restrictNormal L := h
  apply AlgEquiv.restrictScalars_injective K
  apply SIC.IsPrimitiveRoot.algEquiv_ext (IsCyclotomicExtension.zeta_spec p L M) hL
  have he : algebraMap E M (CyclotomicBaseChange.primitiveRoot p K L) = ζ :=
    CyclotomicBaseChange.algebraMap_primitiveRoot p K L
  change σ ζ = τ ζ
  rw [← he, σ.commutes, τ.commutes]

/-- Every automorphism of $L(\zeta_p)/K(\zeta_p)$ has $p$th power one.
Used by `FinitePlace.finrank_eq_one_of_finrank_prime`; Childress, *Class Field Theory*,
Chapter VI, proof of Theorem 3.1. -/
private theorem cyclotomic_exponent [IsGalois K L] (p : ℕ) [Fact p.Prime]
    (hdegree : Module.finrank K L = p) :
    ∀ σ : CyclotomicField p L ≃ₐ[CyclotomicBaseChange.base p K L] CyclotomicField p L,
      σ ^ p = 1 := by
  intro σ
  have hcard : Nat.card
      (CyclotomicField p L ≃ₐ[CyclotomicBaseChange.base p K L] CyclotomicField p L) = p := by
    rw [IsGalois.card_aut_eq_finrank, CyclotomicBaseChange.finrank_extension p K L hdegree]
  exact (congrArg (fun n => σ ^ n) hcard.symm).trans pow_card_eq_one'

/-! ### Transfer of the local norm hypothesis

The tower law for the global Artin map carries the local idèle at a place of $K(\zeta_p)$
to the local norm at the place below. -/

/-- The norm hypothesis at $v$ passes from $L/K$ to $L(\zeta_p)/K(\zeta_p)$.
Used by `FinitePlace.finrank_eq_one_of_finrank_prime`; Childress, *Class Field Theory*,
Chapter VI, Exercise 6.4. -/
private theorem cyclotomic_local_norm [IsAbelianGalois K L]
    (p : ℕ) [Fact p.Prime] (v : HeightOneSpectrum (𝓞 K))
    (hv : (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 K) K v).range ≤
      (IdeleClassGroup.norm (K := K) (L := L)).range)
    (w' : HeightOneSpectrum (𝓞 (CyclotomicBaseChange.base p K L)))
    [w'.asIdeal.LiesOver v.asIdeal] :
    (NumberField.IdeleClassGroup.ofAdicCompletion
      (𝓞 (CyclotomicBaseChange.base p K L)) (CyclotomicBaseChange.base p K L) w').range ≤
      (IdeleClassGroup.norm (K := CyclotomicBaseChange.base p K L)
        (L := CyclotomicField p L)).range := by
  let E := CyclotomicBaseChange.base p K L
  let M := CyclotomicField p L
  have : IsAbelianGalois K M :=
    isAbelianGalois_of_isCyclotomicExtension (K := K) (L := L) (Ω := M) (M := p)
  have : IsAbelianGalois E M := IsAbelianGalois.tower_top K E M
  rintro x ⟨t, rfl⟩
  apply comap_norm_range_norm_le_of_injective E
    (cyclotomicRestrict_injective (K := K) (L := L) p)
  change IdeleClassGroup.norm (K := K) (L := E) _ ∈
    (IdeleClassGroup.norm (K := K) (L := L)).range
  rw [IdeleClassGroup.norm_ofAdicCompletion v w']
  exact hv ⟨_, rfl⟩

/-! ### Descent of complete splitting -/

/-- A local degree of one over $K(\zeta_p)$ forces the local degree of `L/K` to be one:
the latter divides both $p$ and $[K(\zeta_p):K]$. Used by
`FinitePlace.finrank_eq_one_of_finrank_prime`; Childress, *Class Field Theory*, Chapter VI,
proof of Theorem 3.1. -/
private theorem cyclotomic_local_descent [IsGalois K L] (p : ℕ) [Fact p.Prime]
    (hdegree : Module.finrank K L = p) (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (u : HeightOneSpectrum (𝓞 (CyclotomicField p L))) [u.asIdeal.LiesOver w.asIdeal]
    (w' : HeightOneSpectrum (𝓞 (CyclotomicBaseChange.base p K L)))
    [u.asIdeal.LiesOver w'.asIdeal] [w'.asIdeal.LiesOver v.asIdeal]
    (hsplit : Module.finrank (w'.adicCompletion (CyclotomicBaseChange.base p K L))
      (u.adicCompletion (CyclotomicField p L)) = 1) :
    Module.finrank (v.adicCompletion K) (w.adicCompletion L) = 1 := by
  let E := CyclotomicBaseChange.base p K L
  have hmulL := FinitePlace.finrank_mul_finrank v w u
  have hmulE := FinitePlace.finrank_mul_finrank v w' u
  rw [hsplit, mul_one] at hmulE
  have hlocaldiv : Module.finrank (v.adicCompletion K) (w.adicCompletion L) ∣
      Module.finrank (v.adicCompletion K) (w'.adicCompletion E) := by
    rw [hmulE]
    exact dvd_of_mul_right_eq _ hmulL
  have hdivbase : Module.finrank (v.adicCompletion K) (w.adicCompletion L) ∣
      Module.finrank K E :=
    hlocaldiv.trans (FinitePlace.finrank_dvd_finrank v w')
  have hdivp : Module.finrank (v.adicCompletion K) (w.adicCompletion L) ∣ p :=
    hdegree ▸ FinitePlace.finrank_dvd_finrank v w
  have hcoprime : p.Coprime (Module.finrank K E) :=
    CyclotomicBaseChange.coprime_finrank_base p K L
  exact (hcoprime.of_dvd_left hdivp).eq_one_of_dvd hdivbase

/-- **Complete splitting in prime degree at a finite place**: if `L/K` is Galois of prime degree
and the image of $K_v^\times$ in $C_K$ lies in $N_{L/K}C_L$, then $[L_w:K_v] = 1$ for every `w`
above `v`. Childress, *Class Field Theory*, Chapter VI, proof of Theorem 3.1, with
Exercise 6.4. -/
theorem FinitePlace.finrank_eq_one_of_finrank_prime [IsGalois K L]
    (hp : (Module.finrank K L).Prime) (v : HeightOneSpectrum (𝓞 K))
    (hv : (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 K) K v).range ≤
      (IdeleClassGroup.norm (K := K) (L := L)).range)
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] :
    Module.finrank (v.adicCompletion K) (w.adicCompletion L) = 1 := by
  let p := Module.finrank K L
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (L ≃ₐ[K] L) = p := IsGalois.card_aut_eq_finrank K L
  have : IsCyclic (L ≃ₐ[K] L) := isCyclic_of_prime_card (p := p) hcard
  have : IsAbelianGalois K L := IsAbelianGalois.of_isCyclic K L
  let E := CyclotomicBaseChange.base p K L
  let M := CyclotomicField p L
  have : IsAbelianGalois K M :=
    isAbelianGalois_of_isCyclotomicExtension (K := K) (L := L) (Ω := M) (M := p)
  have : IsAbelianGalois E M := IsAbelianGalois.tower_top K E M
  let uAbove : FinitePlace.PrimeAbove (L := M) w :=
    Classical.arbitrary _
  let u := FinitePlace.PrimeAbove.place w uAbove
  have huw : u.asIdeal.LiesOver w.asIdeal := FinitePlace.PrimeAbove.place_liesOver w uAbove
  have huv : u.asIdeal.LiesOver v.asIdeal :=
    Ideal.LiesOver.trans u.asIdeal w.asIdeal v.asIdeal
  let w' := FinitePlace.below (K := E) u
  have hw'over : w'.asIdeal.LiesOver v.asIdeal :=
    FinitePlace.liesOver_below_of_liesOver (L := E) v u
  have hsplit : Module.finrank (w'.adicCompletion E) (u.adicCompletion M) = 1 :=
    FinitePlace.finrank_eq_one_of_pow_eq_one
      (CyclotomicBaseChange.primitiveRoot_spec p K L)
      (cyclotomic_exponent p rfl) w' (cyclotomic_local_norm p v hv w') u
  exact cyclotomic_local_descent p rfl v w u w' hsplit

end SIC
