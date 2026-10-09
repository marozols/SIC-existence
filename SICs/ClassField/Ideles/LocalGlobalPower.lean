/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Ideles.PowerSubgroup
import SICs.ClassField.SUnits.LocalPowerClasses

/-!
# A local criterion for global powers

Surjectivity of S-units onto selected local power classes detects global nth powers.

This follows Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII,
Proposition 6.10, using the cyclic radical reduction in Proposition 9.2, p. 224, footnote 7.
The finite sets S and T here omit the infinite places, which are included separately among
the local-power hypotheses.

## The argument

In the radical extension of b, take the subgroup D of idèles unrestricted at S and infinity,
integral nth powers at T, and integral units elsewhere. Local roots split the places at S
and infinity; the degree divides n, so nth powers at T are norms; unramifiedness supplies
unit norms elsewhere. Surjectivity of S-units on the T power classes gives I_S = U(S)D,
and the ideal-class hypothesis gives I = K×D. The radical extension is cyclic, so the
first inequality bounds its degree by the order of its trivial norm quotient. Its degree
is therefore one.
-/

noncomputable section

open IsDedekindDomain NumberField
open scoped SIC.FinitePlace SIC.InfinitePlace NumberField.LiesOver

namespace SIC.IdeleGroup

variable {K : Type*} [Field K] [NumberField K]

/-! ### The auxiliary idèle subgroup

The subgroup D is specified by integrality outside S and nth-power components at T.
Since S and T are disjoint, its power components are integral automatically. Correcting
an S-idèle by an S-unit removes its power classes at T. -/

/-- The subgroup D in Milne, *Class Field Theory*, Chapter VII, proof of Proposition 6.10:
idèles integral outside S and nth powers at T. -/
private def localPowerSubgroup (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup (NumberField.IdeleGroup (𝓞 K) K) :=
  sSubgroup (K := K) (L := K) S ⊓ ⨅ v : T,
    (powMonoidHom n : (v.val.adicCompletion K)ˣ →* _).range.comap
      (finiteComponent K v.val)

/-- Membership in D consists of the S-idèle condition and power components at T. -/
private theorem mem_localPowerSubgroup (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (x : NumberField.IdeleGroup (𝓞 K) K) :
    x ∈ localPowerSubgroup n S T ↔ x ∈ sSubgroup (K := K) (L := K) S ∧
      ∀ v : T, ∃ y : (v.val.adicCompletion K)ˣ, y ^ n = finiteComponent K v.val x := by
  simp only [localPowerSubgroup, Subgroup.mem_inf, Subgroup.mem_iInf,
    Subgroup.mem_comap, MonoidHom.mem_range, powMonoidHom_apply]

/-- S-unit surjectivity corrects every S-idèle into D; this is the first saturation step
in Milne, *Class Field Theory*, Chapter VII, proof of Proposition 6.10. -/
private theorem sSubgroup_le_principal_sup_localPower
    (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : Disjoint S T)
    (hlocal : Function.Surjective (sUnitsToLocalPowers n S T hST)) :
    sSubgroup (K := K) (L := K) S ≤
      NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔ localPowerSubgroup n S T := by
  intro x hx
  have hu (v : T) : finiteComponent K v.val x ∈ FinitePlace.unitGroup v.val :=
    (mem_sSubgroup S x).mp hx v.val (by
      simpa only [FinitePlace.below_self] using
        fun hv => Finset.disjoint_left.mp hST hv v.property)
  obtain ⟨a, ha⟩ := sUnitsToLocalPowers_representatives n S T hST hlocal
    (fun v => ⟨finiteComponent K v.val x, hu v⟩)
  let p := NumberField.IdeleGroup.unitEmbedding (𝓞 K) K a.val
  have hp : p ∈ sSubgroup (K := K) (L := K) S := a.property
  have hd : p⁻¹ * x ∈ localPowerSubgroup n S T := by
    apply (mem_localPowerSubgroup n S T _).mpr
    refine ⟨(sSubgroup (K := K) (L := K) S).mul_mem
      ((sSubgroup (K := K) (L := K) S).inv_mem hp) hx, fun v => ?_⟩
    obtain ⟨z, hz⟩ := ha v
    refine ⟨z⁻¹, ?_⟩
    simp only [map_mul, map_inv, p, finiteComponent_unitEmbedding, hz, inv_pow]
    group
  have hp' : p ∈ NumberField.IdeleGroup.principalSubgroup (𝓞 K) K := ⟨a.val, rfl⟩
  simpa only [mul_inv_cancel_left] using
    (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔ localPowerSubgroup n S T).mul_mem
      (Subgroup.mem_sup_left hp') (Subgroup.mem_sup_right hd)

/-- Ideal-class generation and S-unit surjectivity give $K^\times D=I_K$.
Milne, *Class Field Theory*, Chapter VII, proof of Proposition 6.10. -/
private theorem principal_sup_localPower_eq_top
    (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : Disjoint S T)
    (hclass : Function.Surjective (sIdealClass (K := K) (L := K) S))
    (hlocal : Function.Surjective (sUnitsToLocalPowers n S T hST)) :
    NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔ localPowerSubgroup n S T = ⊤ := by
  apply top_unique
  rw [← sSubgroup_sup_principal S hclass]
  exact sup_le (sSubgroup_le_principal_sup_localPower n S T hST hlocal) le_sup_left

/-! ### Norm containment and the radical extension

Every component of D is a norm: split completions handle the unrestricted components,
degree divisibility handles powers, and unramified completions handle the integral units.
The cyclic first inequality then descends the radical to the base field. -/

open scoped Classical in
/-- Milne's auxiliary group is contained in the free local-power group with unrestricted
infinite places and primes in `S`. Used to deduce its norm containment from the common lemma. -/
private theorem localPowerSubgroup_le_freePowerSubgroup
    (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    localPowerSubgroup n S T ≤ freePowerSubgroup n (S ∪ T) Set.univ (↑S) := by
  classical
  intro x hx
  obtain ⟨hxS, hxT⟩ := (mem_localPowerSubgroup n S T x).1 hx
  apply (mem_freePowerSubgroup n (S ∪ T) Set.univ ↑S x).2
  refine ⟨sSubgroup_mono (L := K) Finset.subset_union_left hxS, ?_, ?_⟩
  · intro v hv
    exact (hv (Set.mem_univ v)).elim
  · intro v hv hvS
    exact hxT ⟨v, (Finset.mem_union.mp hv).resolve_left hvS⟩

open scoped Classical in
/-- A unit locally an nth power at S and infinity and a local unit outside $S ∪ T$ is a global
nth power, provided S represents every ideal class and its units surject onto the local unit
power classes at T. Milne, *Class Field Theory*, Chapter VII, Proposition 6.10, using the
cyclic radical reduction of Proposition 9.2, p. 224, footnote 7.
The surjectivity hypothesis uses representatives of $U_v/U_v^n$; roots in $K_v$ are integral
automatically because the ratio is a unit. -/
theorem exists_pow_eq_of_local {n : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ n) (hn : 0 < n)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : Disjoint S T)
    (hnS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hclass : Function.Surjective (sIdealClass (K := K) (L := K) S))
    (hlocal : Function.Surjective (sUnitsToLocalPowers n S T hST))
    (b : Kˣ)
    (hi : ∀ v : InfinitePlace K, ∃ x : v.Completion, x ^ n = algebraMap K _ (b : K))
    (hf : ∀ v ∈ S, ∃ x : v.adicCompletion K, x ^ n = algebraMap K _ (b : K))
    (hu : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S ∪ T →
      v.valuation K (b : K) = 1) :
    ∃ x : K, x ^ n = (b : K) := by
  let B := Subgroup.zpowers b
  have hB : B.FG :=
    (Subgroup.fg_iff _).mpr ⟨{b}, (Subgroup.zpowers_eq_closure b).symm, Set.finite_singleton _⟩
  let M := kummerExtension K n B
  let : FiniteDimensional K M := kummerExtension_finiteDimensional hn hB
  let : NumberField M := NumberField.of_module_finite K M
  let : IsGalois K M := kummerExtension_isGalois hζ hn
  let : IsCyclic Gal(M/K) := kummerExtension_isCyclic_zpowers hζ hn b
  let : NeZero n := ⟨hn.ne'⟩
  have hnorm : localPowerSubgroup n S T ≤ (norm (K := K) (L := M)).range := by
    apply (localPowerSubgroup_le_freePowerSubgroup n S T).trans
    apply freePowerSubgroup_le_range_norm n (S ∪ T) Set.univ (↑S)
      (kummerExtension_finrank_zpowers_dvd hζ hn b)
    · intro v _ w
      apply SIC.InfinitePlace.finrank_eq_one_of_local_roots hζ hn B
        (kummerExtension_adjoin_radicals_eq_top n B) v w.val
      intro c
      exact (Subgroup.zpowers_le.mpr (show b ∈ kummerRadicands K n v.Completion from hi v))
        c.property
    · intro v hv hvS w
      apply FinitePlace.finrank_eq_one_of_local_roots hζ hn B
        (kummerExtension_adjoin_radicals_eq_top n B) v (FinitePlace.PrimeAbove.place v w)
      intro c
      exact (Subgroup.zpowers_le.mpr
        (show b ∈ kummerRadicands K n (v.adicCompletion K) from hf v hvS)) c.property
    · intro v hv w
      apply ramificationIdx_kummerExtension_eq_one B hB v _
        (fun hn => hv (Finset.mem_union_left T (hnS v hn))) (FinitePlace.PrimeAbove.place v w)
      rintro ⟨c, hc⟩
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
      simp only [Units.val_zpow_eq_zpow_val, map_zpow₀, hu v hv, one_zpow]
  have hd : Module.finrank K M = 1 := by
    have htop : NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔
        (norm (K := K) (L := M)).range = ⊤ := by
      apply top_unique
      rw [← principal_sup_localPower_eq_top n S T hST hclass hlocal]
      exact sup_le_sup_left hnorm _
    have hfirst := firstInequality (K := K) (L := M)
    rw [htop] at hfirst
    exact Nat.le_antisymm (by simpa using hfirst) (Nat.succ_le_of_lt Module.finrank_pos)
  obtain ⟨r, hr⟩ := exists_root_kummerExtension (B := B) hn ⟨b, Subgroup.mem_zpowers b⟩
  obtain ⟨x, hx⟩ := (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hd).surjective r
  refine ⟨x, (algebraMap K M).injective ?_⟩
  rw [map_pow, hx, hr]

end SIC.IdeleGroup
