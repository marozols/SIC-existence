/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Ideles.LocalGlobalPower
import SICs.ClassField.Local.InfinitePowerIndex
import Mathlib.NumberTheory.NumberField.ProductFormula

/-!
# Indices of local-power idèle subgroups

The relative index of Milne's local-power subgroup and the index after adjoining principal
idèles follow from local power-class counts, the product formula, and S-unit saturation.

This follows Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII, Lemmas 6.5–6.7.

## The argument

The selected local power indices multiply to the relative index. The product formula cancels
the normalized absolute values. Principal elements are global powers by Proposition 6.10, and
the S-unit power-class count gives the index after adjoining principal idèles.
-/

noncomputable section

open IsDedekindDomain NumberField
open scoped SIC.FinitePlace SIC.InfinitePlace NumberField.LiesOver

namespace SIC.IdeleGroup

variable {K : Type*} [Field K] [NumberField K]

/-! ### The product of local power indices

The selected-component section stays inside the S-union-T idèles. Thus their quotient by E
is the product of the selected local power quotients. The normalized product formula then
cancels the local absolute values of n. -/

open scoped Classical in
/-- Selected components are arbitrary within the S-union-T idèles. Used by
`relIndex_powerSubgroup_eq_prod`. -/
private theorem selectedComponents_sSubgroup_surjective (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Surjective ((selectedComponents S).comp
      (sSubgroup (K := K) (L := K) (S ∪ T)).subtype) := by
  intro x
  refine ⟨⟨selectedSection S x, ?_⟩, selectedComponents_section S x⟩
  apply (mem_sSubgroup _ _).2
  intro v hv
  rw [finiteComponent_selectedSection_of_notMem]
  · exact (FinitePlace.unitGroup v).one_mem
  · intro hs
    exact hv (by simpa only [FinitePlace.below_self] using Finset.mem_union_left T hs)

open scoped Classical in
/-- The relative index of E is the product of its selected local power indices.
Milne, *Class Field Theory*, Chapter VII, proof of Lemma 6.6. -/
private theorem relIndex_powerSubgroup_eq_prod (n : ℕ)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    (powerSubgroup n S T).relIndex (sSubgroup (K := K) (L := K) (S ∪ T)) =
      (∏ v : InfinitePlace K, (powMonoidHom n : v.Completionˣ →* v.Completionˣ).range.index) *
      ∏ v : S, (powMonoidHom n : (v.1.adicCompletion K)ˣ →*
        (v.1.adicCompletion K)ˣ).range.index := by
  rw [powerSubgroup, Subgroup.inf_relIndex_left]
  rw [Subgroup.relIndex, Subgroup.subgroupOf, Subgroup.comap_comap,
    Subgroup.index_comap_of_surjective _ (selectedComponents_sSubgroup_surjective S T)]
  have hp : (powMonoidHom n : InfiniteLocalIdele K × (∀ v : S, (v.1.adicCompletion K)ˣ) →*
      InfiniteLocalIdele K × (∀ v : S, (v.1.adicCompletion K)ˣ)).range =
      (powMonoidHom (α := InfiniteLocalIdele K) n).range.prod
        (powMonoidHom (α := ∀ v : S, (v.1.adicCompletion K)ˣ) n).range :=
    MonoidHom.range_prodMap (powMonoidHom (α := InfiniteLocalIdele K) n)
      (powMonoidHom (α := ∀ v : S, (v.1.adicCompletion K)ˣ) n)
  rw [hp, Subgroup.index_prod]
  simp only [Subgroup.index_eq_card,
    Nat.card_congr (QuotientGroup.mulEquivPiModRangePowMonoidHom
      (fun v : InfinitePlace K => v.Completionˣ) n).toEquiv,
    Nat.card_congr (QuotientGroup.mulEquivPiModRangePowMonoidHom
      (fun v : S => (v.1.adicCompletion K)ˣ) n).toEquiv, Nat.card_pi]

/-- The normalized absolute values of n at infinity and S multiply to one when S contains
its prime divisors. This is the product formula used in Milne, *Class Field Theory*,
Chapter VII, proof of Lemma 6.6. -/
private theorem prod_local_norm_natCast {n : ℕ} (hn : 0 < n) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    (∏ v : InfinitePlace K, (n : ℝ) ^ v.mult) *
      (∏ v ∈ S, ‖(n : v.adicCompletion K)‖) = 1 := by
  have h := NumberField.prod_abs_eq_one (K := K) (x := (n : K))
    (Nat.cast_ne_zero.mpr hn.ne')
  simp only [InfinitePlace.map_natCast] at h
  rw [← finprod_comp_equiv NumberField.FinitePlace.equivHeightOneSpectrum.symm] at h
  simp only [NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply, map_natCast] at h
  rw [finprod_eq_prod_of_mulSupport_subset _ ?_] at h
  · exact h
  · intro v hv
    apply hS v
    by_contra hvn
    apply hv
    simpa only [map_natCast] using
      (NumberField.FinitePlace.norm_eq_one_iff_notMem K v (n : 𝓞 K)).2 hvn

open scoped Classical in
/-- The relative index of E in the S-union-T idèles is $n^{2(|S|+r_1+r_2)}$.
Milne, *Class Field Theory*, Chapter VII, Lemma 6.6 and its proof by Proposition 6.8. -/
theorem relIndex_powerSubgroup {n : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (hn : 0 < n) (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    (powerSubgroup n S T).relIndex (sSubgroup (K := K) (L := K) (S ∪ T)) =
      n ^ (2 * (S.card + Nat.card (InfinitePlace K))) := by
  have : NeZero n := ⟨hn.ne'⟩
  have hi (v : InfinitePlace K) :
      ((powMonoidHom n : v.Completionˣ →* v.Completionˣ).range.index : ℝ) =
        (n : ℝ) * n / (n : ℝ) ^ v.mult := by
    change (Nat.card (v.Completionˣ ⧸ (powMonoidHom n).range) : ℝ) = _
    rw [SIC.InfinitePlace.card_units_powerQuotient v hn,
      (hζ.map_of_injective (algebraMap K v.Completion).injective).card_rootsOfUnity]
  have hf (v : S) :
      ((powMonoidHom n : (v.1.adicCompletion K)ˣ →* (v.1.adicCompletion K)ˣ).range.index : ℝ) =
        (n : ℝ) * n / ‖(n : v.1.adicCompletion K)‖ := by
    change (Nat.card ((v.1.adicCompletion K)ˣ ⧸ (powMonoidHom n).range) : ℝ) = _
    rw [FinitePlace.card_units_powerQuotient v.1 hn,
      (hζ.map_of_injective (algebraMap K (v.1.adicCompletion K)).injective).card_rootsOfUnity]
  rw [relIndex_powerSubgroup_eq_prod]
  apply Nat.cast_injective (R := ℝ)
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_prod, Nat.cast_prod]
  simp_rw [hi, hf, Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  rw [div_mul_div_comm, Finset.prod_coe_sort S (fun v => ‖(n : v.adicCompletion K)‖),
    prod_local_norm_natCast hn S hS, div_one,
    ← pow_add, ← pow_two, ← pow_mul, Nat.card_eq_fintype_card, Nat.add_comm]

/-! ### Principal elements of the local-power subgroup

The local-global power criterion makes every principal element of E a global nth power.
Power saturation of the S-union-T units then identifies its root as another S-union-T unit.
The intrinsic unit power classes give the resulting principal intersection index. -/

open scoped Classical in
/-- The pullback of E to $U(S\cup T)$ is $U(S\cup T)^n$. This is the subgroup identity
in Milne, *Class Field Theory*, Chapter VII, proof of Lemma 6.7, using Proposition 6.10. -/
theorem powerSubgroup_comap_sUnits {n : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ n) (hn : 0 < n)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : Disjoint S T)
    (hnS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hclass : Function.Surjective (sIdealClass (K := K) (L := K) S))
    (hlocal : Function.Surjective (sUnitsToLocalPowers n S T hST)) :
    (powerSubgroup n S T).comap
        ((NumberField.IdeleGroup.unitEmbedding (𝓞 K) K).comp
          (sUnits (K := K) (L := K) (S ∪ T)).subtype) =
      (powMonoidHom n : sUnits (K := K) (L := K) (S ∪ T) →*
        sUnits (K := K) (L := K) (S ∪ T)).range := by
  ext a
  constructor
  · intro ha
    have hpow := (mem_powerSubgroup n S T
      (NumberField.IdeleGroup.unitEmbedding (𝓞 K) K a.val)).mp ha
    obtain ⟨x, hx⟩ := exists_pow_eq_of_local hζ hn S T hST hnS hclass hlocal a.val
      (fun v => by
        obtain ⟨y, hy⟩ := hpow.2.1 v
        exact ⟨y.val, by simpa only [Units.val_pow_eq_pow_val, infiniteComponent_unitEmbedding,
          Units.coe_map, MonoidHom.coe_coe] using congrArg Units.val hy⟩)
      (fun v hv => by
        obtain ⟨y, hy⟩ := hpow.2.2 v hv
        exact ⟨y.val, by simpa only [Units.val_pow_eq_pow_val, finiteComponent_unitEmbedding,
          Units.coe_map, MonoidHom.coe_coe] using congrArg Units.val hy⟩)
      (fun v hv => sUnits_valuation_eq_one (S ∪ T) a v (by simpa using hv))
    rw [← sUnits_power_comap (S ∪ T) hn.ne']
    refine ⟨Units.mk0 x ((pow_ne_zero_iff hn.ne').mp (by rw [hx]; exact a.val.ne_zero)), ?_⟩
    exact Units.ext hx
  · rintro ⟨b, rfl⟩
    change NumberField.IdeleGroup.unitEmbedding (𝓞 K) K (b.val ^ n) ∈ powerSubgroup n S T
    rw [map_pow]
    exact pow_mem_powerSubgroup n S T b.property

open scoped Classical in
/-- The index $[U(S\cup T):K^\times\cap E]$ is $n^{|S\cup T|+r_1+r_2}$.
Milne, *Class Field Theory*, Chapter VII, Lemma 6.7, with its proof extended to positive n
by Proposition 6.10 and `card_sUnits_powerQuotient`. -/
theorem relIndex_powerSubgroup_principal {n : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ n) (hn : 0 < n)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : Disjoint S T)
    (hnS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hclass : Function.Surjective (sIdealClass (K := K) (L := K) S))
    (hlocal : Function.Surjective (sUnitsToLocalPowers n S T hST)) :
    ((powerSubgroup n S T).comap (NumberField.IdeleGroup.unitEmbedding (𝓞 K) K)).relIndex
      (sUnits (K := K) (L := K) (S ∪ T)) =
        n ^ ((S ∪ T).card + Nat.card (InfinitePlace K)) := by
  rw [Subgroup.relIndex, Subgroup.subgroupOf, Subgroup.comap_comap,
    powerSubgroup_comap_sUnits hζ hn S T hST hnS hclass hlocal, Subgroup.index_eq_card,
    card_sUnits_powerQuotient hζ hn]

/-! ### The index of the principal multiple

Milne's index identity for a product and an intersection cancels the two local-power indices
against each other, giving the index of $K^\times E$ in $I_K$ once `S` carries the ideal
classes. -/

/-- **The index of $K^\times E$**: $[I_K:K^\times E]\cdot n^{|T|} = n^{|S|+r_1+r_2}$ when
$\mu_n\subset K$, `S` contains the primes dividing `n` and represents the ideal classes, and the
S-units cover the local unit power classes at the primes of `T`. Milne, *Class Field Theory*,
Chapter VII, Lemmas 6.5–6.7. -/
theorem index_powerSubgroup_sup_principal_mul {n : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (hn : 0 < n) (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : Disjoint S T)
    (hnS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hclass : Function.Surjective (sIdealClass (K := K) (L := K) S))
    (hlocal : Function.Surjective (sUnitsToLocalPowers n S T hST)) :
    (powerSubgroup n S T ⊔ NumberField.IdeleGroup.principalSubgroup (𝓞 K) K).index *
        n ^ T.card = n ^ (S.card + Nat.card (InfinitePlace K)) := by
  classical
  let A := sSubgroup (K := K) (L := K) (S ∪ T)
  let E := powerSubgroup n S T
  let C := NumberField.IdeleGroup.principalSubgroup (𝓞 K) K
  have hcover : A ⊔ C = ⊤ := by
    apply top_unique
    rw [← sSubgroup_sup_principal S hclass]
    exact sup_le_sup_right (sSubgroup_mono (L := K) Finset.subset_union_left) _
  have hprincipal : (E ⊓ C).relIndex (A ⊓ C) =
      n ^ ((S ∪ T).card + Nat.card (InfinitePlace K)) := by
    change (E ⊓ (NumberField.IdeleGroup.unitEmbedding (𝓞 K) K).range).relIndex
      (A ⊓ (NumberField.IdeleGroup.unitEmbedding (𝓞 K) K).range) = _
    rw [SIC.Subgroup.relIndex_inf_range]
    exact relIndex_powerSubgroup_principal hζ hn S T hST hnS hclass hlocal
  have hidx := SIC.Subgroup.relIndex_sup_mul_inf A E C (powerSubgroup_le_sSubgroup n S T)
  rw [hcover, Subgroup.relIndex_top_right, hprincipal,
    relIndex_powerSubgroup hζ hn S T hnS] at hidx
  have hcancel : (E ⊔ C).index * n ^ T.card *
      n ^ (S.card + Nat.card (InfinitePlace K)) =
      n ^ (S.card + Nat.card (InfinitePlace K)) *
        n ^ (S.card + Nat.card (InfinitePlace K)) := by
    calc
      _ = (E ⊔ C).index * n ^ ((S ∪ T).card + Nat.card (InfinitePlace K)) := by
        have hexp : T.card + (S.card + Nat.card (InfinitePlace K)) =
            S.card + T.card + Nat.card (InfinitePlace K) := by omega
        rw [Finset.card_union_of_disjoint hST, mul_assoc, ← pow_add, hexp]
      _ = n ^ (2 * (S.card + Nat.card (InfinitePlace K))) := hidx
      _ = _ := by rw [two_mul, pow_add]
  exact Nat.eq_of_mul_eq_mul_right (pow_pos hn _) hcancel

/-- $[I_K:K^\times E] = n^{|S|+r_1+r_2}$ for the subgroup `E` of local nth powers at `S` and
infinity and units elsewhere, when $\mu_n\subset K$ and `S` contains the primes dividing `n` and
represents the ideal classes. Childress, *Class Field Theory*, Chapter VI, proof of
Theorem 2.6. -/
theorem index_powerSubgroup_sup_principal {n : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (hn : 0 < n) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hnS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hclass : Function.Surjective (sIdealClass (K := K) (L := K) S)) :
    (powerSubgroup n S ∅ ⊔ NumberField.IdeleGroup.principalSubgroup (𝓞 K) K).index =
      n ^ (S.card + Nat.card (InfinitePlace K)) := by
  classical
  simpa using index_powerSubgroup_sup_principal_mul hζ hn S ∅
    (Finset.disjoint_empty_right S) hnS hclass
          (fun _ => ⟨1, Subsingleton.elim _ _⟩)


end SIC.IdeleGroup
