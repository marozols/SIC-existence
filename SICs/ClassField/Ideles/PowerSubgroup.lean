/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Ideles.Approximation
import SICs.ClassField.Ideles.NormTopology
import SICs.ClassField.SUnits.Basic

/-!
# Idèle subgroups defined by local conditions

A single free local-power family describes Milne's power subgroup, its unrestricted-place
variants, and the group $U_K^S$ of unit idèles away from a finite set.

This follows Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII, Lemma 6.4, and
Childress, *Class Field Theory* (2009), Chapter VI, proofs of Theorems 2.7 and 2.9.

## The argument

At selected finite and infinite places the free family permits arbitrary components; at the
other selected places it requires nth powers, and outside its finite support it requires local
units. Setting the unrestricted sets recovers Milne's subgroup. Setting the exponent to zero
recovers $U_K^S$. Local powers are norms when the extension degree divides the exponent;
splitting handles unrestricted places and unramifiedness handles integral units. Splitting an
idèle into its selected components and the remainder gives the lattice operations and the
criterion for its image in an idèle class subgroup.
-/
noncomputable section

open IsDedekindDomain NumberField
open scoped SIC.FinitePlace SIC.InfinitePlace NumberField.LiesOver

namespace SIC.IdeleGroup

variable {K : Type*} [Field K] [NumberField K]

/-! ### The free subgroup and Milne's specialization

The general subgroup records the places where components may be unrestricted. Milne's group
is its specialization with power conditions at all infinite places and the finite set S. -/

/-- The idèles that are integral units outside `S`, `n`th powers at the infinite places outside
`I`, and `n`th powers at the primes of `S` outside `T`; the components at `I` and at the primes
of `S` in `T` are unrestricted. Childress's $B_1$ and $B_2$ in *Class Field Theory*, Chapter VI,
proof of Theorem 2.9. -/
def freePowerSubgroup (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (I : Set (InfinitePlace K)) (T : Set (HeightOneSpectrum (𝓞 K))) :
    Subgroup (NumberField.IdeleGroup (𝓞 K) K) :=
  sSubgroup (K := K) (L := K) S ⊓
    ((⨅ v : InfinitePlace K, ⨅ (_ : v ∉ I),
        (powMonoidHom n : v.Completionˣ →* v.Completionˣ).range.comap (infiniteComponent K v)) ⊓
      ⨅ v ∈ S, ⨅ (_ : v ∉ T),
        (powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range.comap
          (finiteComponent K v))

/-- Membership in `freePowerSubgroup` in components. -/
theorem mem_freePowerSubgroup (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (I : Set (InfinitePlace K)) (T : Set (HeightOneSpectrum (𝓞 K)))
    (x : NumberField.IdeleGroup (𝓞 K) K) :
    x ∈ freePowerSubgroup n S I T ↔
      x ∈ sSubgroup (K := K) (L := K) S ∧
        (∀ v ∉ I, ∃ y : v.Completionˣ, y ^ n = infiniteComponent K v x) ∧
          ∀ v ∈ S, v ∉ T → ∃ y : (v.adicCompletion K)ˣ, y ^ n = finiteComponent K v x := by
  simp only [freePowerSubgroup, Subgroup.mem_inf, Subgroup.mem_iInf,
    Subgroup.mem_comap, MonoidHom.mem_range, powMonoidHom_apply]

/-- `freePowerSubgroup` consists of idèles integral outside `S`. -/
theorem freePowerSubgroup_le_sSubgroup (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (I : Set (InfinitePlace K)) (T : Set (HeightOneSpectrum (𝓞 K))) :
    freePowerSubgroup n S I T ≤ sSubgroup (K := K) (L := K) S :=
  inf_le_left

/-- The principal elements of `freePowerSubgroup` form a finitely generated subgroup of the
S-units. -/
theorem fg_comap_freePowerSubgroup (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (I : Set (InfinitePlace K)) (T : Set (HeightOneSpectrum (𝓞 K))) :
    ((freePowerSubgroup n S I T).comap (NumberField.IdeleGroup.unitEmbedding (𝓞 K) K)).FG := by
  let B := (freePowerSubgroup n S I T).comap
    (NumberField.IdeleGroup.unitEmbedding (𝓞 K) K)
  have hle : B ≤ sUnits (K := K) (L := K) S :=
    Subgroup.comap_mono (freePowerSubgroup_le_sSubgroup n S I T)
  let f : Additive B →ₗ[ℤ] Additive (sUnits (K := K) (L := K) S) :=
    ((Subgroup.inclusion hle).toAdditive).toIntLinearMap
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun x : Additive (sUnits (K := K) (L := K) S) => x.toMul.1) h
  have hfinite : Module.Finite ℤ (Additive B) := Module.Finite.of_injective f hf
  exact (Group.fg_iff_subgroup_fg B).1
    (GroupFG.iff_add_fg.2 (Module.Finite.iff_addGroup_fg.1 hfinite))


open scoped Classical in
/-- Milne's subgroup $E$ of local nth powers at $S$ and infinity, unrestricted components
at $T$, and integral units elsewhere; *Class Field Theory*, Chapter VII, Lemma 6.4. -/
def powerSubgroup (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup (NumberField.IdeleGroup (𝓞 K) K) :=
  sSubgroup (K := K) (L := K) (S ∪ T) ⊓
    (powMonoidHom n :
      InfiniteLocalIdele K × (∀ v : S, (v.1.adicCompletion K)ˣ) →*
      InfiniteLocalIdele K × (∀ v : S, (v.1.adicCompletion K)ˣ)).range.comap
        (selectedComponents S)

open scoped Classical in
/-- Membership in E consists of integral units outside $S\cup T$, and nth powers at
infinity and the finite places in S. This is the component form of `powerSubgroup`. -/
theorem mem_powerSubgroup (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (x : NumberField.IdeleGroup (𝓞 K) K) :
    x ∈ powerSubgroup n S T ↔
      (∀ v, v ∉ S ∪ T → finiteComponent K v x ∈ FinitePlace.unitGroup v) ∧
      (∀ v, ∃ y : v.Completionˣ, y ^ n = infiniteComponent K v x) ∧
      (∀ v ∈ S, ∃ y : (v.adicCompletion K)ˣ, y ^ n = finiteComponent K v x) := by
  classical
  simp only [powerSubgroup, Subgroup.mem_inf, mem_sSubgroup, FinitePlace.below_self,
    Subgroup.mem_comap, MonoidHom.mem_range]
  constructor
  · rintro ⟨hu, ⟨y, hy⟩⟩
    refine ⟨hu, fun v => ⟨y.1 v, ?_⟩, fun v hv => ⟨y.2 ⟨v, hv⟩, ?_⟩⟩
    · exact congrArg (fun z => z.1 v) hy
    · exact congrArg (fun z => z.2 ⟨v, hv⟩) hy
  · rintro ⟨hu, hi, hf⟩
    choose yi hyi using hi
    choose yf hyf using fun v : S => hf v.1 v.2
    refine ⟨hu, ⟨(yi, yf), ?_⟩⟩
    exact Prod.ext (funext hyi) (funext hyf)

open scoped Classical in
/-- E is a subgroup of the idèles integral outside $S\cup T$. -/
theorem powerSubgroup_le_sSubgroup (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    powerSubgroup n S T ≤ sSubgroup (K := K) (L := K) (S ∪ T) :=
  inf_le_left

open scoped Classical in
/-- Every nth power of an $S\cup T$-idèle belongs to E: $I_{S\cup T}^n\subset E$.
This is the power operation for `powerSubgroup`. -/
theorem pow_mem_powerSubgroup (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K)))
    {x : NumberField.IdeleGroup (𝓞 K) K}
    (hx : x ∈ sSubgroup (K := K) (L := K) (S ∪ T)) :
    x ^ n ∈ powerSubgroup n S T := by
  refine ⟨(sSubgroup (K := K) (L := K) (S ∪ T)).pow_mem hx n, ?_⟩
  exact ⟨selectedComponents S x, (map_pow (selectedComponents S) x n).symm⟩

/-! ### Norm containment

Local powers are norms when the extension degree divides the exponent. At unrestricted places
we use splitting, and outside the finite support we use unramified local units. -/

/-- The free local-power subgroup lies in the idèle norm group when its unrestricted places
split and the extension is unramified outside its finite support. This common norm argument
specializes to Milne's subgroup and to the unit idèles away from a finite set. -/
theorem freePowerSubgroup_le_range_norm {L : Type*} [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (I : Set (InfinitePlace K)) (T : Set (HeightOneSpectrum (𝓞 K)))
    (hdegree : Module.finrank K L ∣ n)
    (hi : ∀ v ∈ I, ∀ w : SIC.InfinitePlace.PlaceAbove (L := L) v,
      Module.finrank v.Completion w.val.Completion = 1)
    (hf : ∀ v ∈ S, v ∈ T → ∀ w : FinitePlace.PrimeAbove (L := L) v,
      Module.finrank (v.adicCompletion K)
        ((FinitePlace.PrimeAbove.place v w).adicCompletion L) = 1)
    (hu : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ∀ w : FinitePlace.PrimeAbove (L := L) v,
        (FinitePlace.PrimeAbove.place v w).asIdeal.ramificationIdx (𝓞 K) = 1) :
    freePowerSubgroup n S I T ≤ (norm (K := K) (L := L)).range := by
  classical
  let wi : ∀ v : InfinitePlace K, SIC.InfinitePlace.PlaceAbove (L := L) v :=
    fun _ => Classical.choice inferInstance
  let wf : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.PrimeAbove (L := L) v :=
    fun _ => Classical.choice inferInstance
  intro x hx
  obtain ⟨hxS, hxI, hxT⟩ := (mem_freePowerSubgroup n S I T x).1 hx
  apply (mem_range_norm_iff wi wf x).2
  constructor
  · intro v
    by_cases hv : v ∈ I
    · exact SIC.InfinitePlace.localNorm_surjective_of_finrank_eq_one v (wi v).1
        (hi v hv (wi v)) (infiniteComponent K v x)
    · obtain ⟨y, hy⟩ := hxI v hv
      rw [← hy]
      exact SIC.InfinitePlace.pow_mem_range_localNorm v (wi v).1
        ((SIC.InfinitePlace.finrank_dvd_finrank v (wi v).1).trans hdegree) y
  · intro v
    by_cases hvS : v ∈ S
    · by_cases hvT : v ∈ T
      · exact FinitePlace.localNorm_surjective_of_finrank_eq_one v
          (FinitePlace.PrimeAbove.place v (wf v)) (hf v hvS hvT (wf v))
          (finiteComponent K v x)
      · obtain ⟨y, hy⟩ := hxT v hvS hvT
        rw [← hy]
        exact FinitePlace.pow_mem_range_localNorm v
          (FinitePlace.PrimeAbove.place v (wf v))
          ((FinitePlace.finrank_dvd_finrank v
            (FinitePlace.PrimeAbove.place v (wf v))).trans hdegree) y
    · exact FinitePlace.unitGroup_le_range_localNorm v
        (FinitePlace.PrimeAbove.place v (wf v)) (hu v hvS (wf v))
          ((mem_sSubgroup (K := K) (L := K) S x).1 hxS v
            (by simpa only [FinitePlace.below_self] using hvS))

open scoped Classical in
/-- Milne's local-power subgroup is the free subgroup with unrestricted primes in `T`
outside `S`. The identity holds even when `S` and `T` intersect. -/
theorem powerSubgroup_eq_freePowerSubgroup (n : ℕ)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    powerSubgroup n S T = freePowerSubgroup n (S ∪ T) ∅ (↑T \ ↑S) := by
  ext x
  classical
  rw [mem_powerSubgroup, mem_freePowerSubgroup]
  simp only [mem_sSubgroup, FinitePlace.below_self, Set.mem_sdiff, Set.mem_empty_iff_false,
    not_false_eq_true, true_imp_iff, Finset.mem_coe]
  constructor
  · rintro ⟨hu, hi, hf⟩
    refine ⟨hu, fun v => hi v, ?_⟩
    intro v hv hnot
    exact hf v (by
      by_contra hs
      exact hnot ⟨(Finset.mem_union.mp hv).resolve_left hs, hs⟩)
  · rintro ⟨hu, hi, hf⟩
    refine ⟨hu, hi, ?_⟩
    intro v hv
    exact hf v (Finset.mem_union_left T hv) (by simp [hv])

open scoped Classical in
/-- Milne's local-power subgroup consists of norms when the extension degree divides the
power, primes in `T` split, and the extension is unramified outside `S`. -/
theorem powerSubgroup_le_range_norm {L : Type*} [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hdegree : Module.finrank K L ∣ n)
    (hunram : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ∀ w : FinitePlace.PrimeAbove (L := L) v,
        (FinitePlace.PrimeAbove.place v w).asIdeal.ramificationIdx (𝓞 K) = 1)
    (hsplit : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ T →
      ∀ w : FinitePlace.PrimeAbove (L := L) v,
        Module.finrank (v.adicCompletion K)
          ((FinitePlace.PrimeAbove.place v w).adicCompletion L) = 1) :
    powerSubgroup n S T ≤ (norm (K := K) (L := L)).range := by
  rw [powerSubgroup_eq_freePowerSubgroup]
  apply freePowerSubgroup_le_range_norm n (S ∪ T) ∅ (↑T \ ↑S) hdegree
  · simp
  · intro v _ hv w
    exact hsplit v hv.1 w
  · intro v hv w
    exact hunram v (fun hs => hv (Finset.mem_union_left T hs)) w

/-! ### Unit idèles away from S

The group $U_K^S$ of idèles that are one at the infinite places and at `S` and integral units
elsewhere. Every element of $E$ is an nth power times an element of $U_K^S$; at unramified
places units are local norms, and norms of unit idèles are unit idèles. -/

/-- The group $U_K^S$ of idèles equal to one at the infinite places and at the primes of `S`
and integral units at the other primes. Its classes form the finite-support condition of the
existence theorem: Childress, *Class Field Theory*, Chapter VI, proof of Theorem 2.7, where an
open subgroup contains $U_v$ for every `v` outside a finite set. -/
def awayUnitSubgroup (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup (NumberField.IdeleGroup (𝓞 K) K) :=
  awaySubgroup S ⊓ sSubgroup (K := K) (L := K) S

/-- Membership in $U_K^S$ in components. -/
theorem mem_awayUnitSubgroup (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : NumberField.IdeleGroup (𝓞 K) K) :
    x ∈ awayUnitSubgroup S ↔
      (∀ v, infiniteComponent K v x = 1) ∧ (∀ v ∈ S, finiteComponent K v x = 1) ∧
        ∀ v ∉ S, finiteComponent K v x ∈ FinitePlace.unitGroup v := by
  simp only [awayUnitSubgroup, Subgroup.mem_inf, mem_awaySubgroup, mem_sSubgroup,
    FinitePlace.below_self, and_assoc]

/-- The unit idèles away from `S` are the zero-power instance of the free family. -/
theorem awayUnitSubgroup_eq_freePowerSubgroup
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    awayUnitSubgroup S = freePowerSubgroup 0 S ∅ ∅ := by
  ext x
  simp [mem_awayUnitSubgroup, mem_freePowerSubgroup, mem_sSubgroup,
    FinitePlace.below_self, eq_comm]
  tauto

/-- $U_K^T \subseteq U_K^S$ for $S \subseteq T$. -/
theorem awayUnitSubgroup_anti {S T : Finset (HeightOneSpectrum (𝓞 K))} (h : S ⊆ T) :
    awayUnitSubgroup T ≤ awayUnitSubgroup S := by
  intro x hx
  obtain ⟨hi, hf, hu⟩ := (mem_awayUnitSubgroup T x).1 hx
  apply (mem_awayUnitSubgroup S x).2
  refine ⟨hi, fun v hv ↦ hf v (h hv), fun v hv ↦ ?_⟩
  by_cases hT : v ∈ T
  · rw [hf v hT]
    exact (FinitePlace.unitGroup v).one_mem
  · exact hu v hT

/-- Every element of $E$ is an nth power times an element of $U_K^S$:
$E \subseteq I_K^n\,U_K^S$ for the local-power subgroup with $T = \varnothing$. -/
theorem powerSubgroup_le_pow_sup (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    powerSubgroup n S ∅ ≤
      (powMonoidHom n : NumberField.IdeleGroup (𝓞 K) K →* NumberField.IdeleGroup (𝓞 K) K).range ⊔
        awayUnitSubgroup S := by
  classical
  intro b hb
  obtain ⟨hu, ⟨y, hy⟩⟩ := hb
  let c := selectedSection S y
  have hselected : selectedComponents S (c ^ n) = selectedComponents S b := by
    rw [map_pow, selectedComponents_section]
    exact hy
  have hker : (c ^ n)⁻¹ * b ∈ awaySubgroup S := by
    change selectedComponents S ((c ^ n)⁻¹ * b) = 1
    rw [map_mul, map_inv, hselected, inv_mul_cancel]
  have haway : (c ^ n)⁻¹ * b ∈ awayUnitSubgroup S := by
    obtain ⟨hi, hf⟩ := (mem_awaySubgroup S _).1 hker
    apply (mem_awayUnitSubgroup S _).2
    refine ⟨hi, hf, fun v hv ↦ ?_⟩
    rw [map_mul, map_inv, map_pow,
      finiteComponent_selectedSection_of_notMem S y v hv]
    simpa only [one_pow, inv_one, one_mul] using
      (mem_sSubgroup (K := K) (L := K) (S ∪ ∅) b).1 hu v (by
        simpa only [Finset.union_empty, FinitePlace.below_self] using hv)
  have hpow : c ^ n ∈ (powMonoidHom n : NumberField.IdeleGroup (𝓞 K) K →*
      NumberField.IdeleGroup (𝓞 K) K).range := ⟨c, rfl⟩
  have hmul := ((powMonoidHom n : NumberField.IdeleGroup (𝓞 K) K →*
      NumberField.IdeleGroup (𝓞 K) K).range ⊔ awayUnitSubgroup S).mul_mem
        (Subgroup.mem_sup_left hpow) (Subgroup.mem_sup_right haway)
  convert hmul using 1
  group

/-- Unit idèles away from `S` are norms when `L/K` is unramified outside `S`: units are local
norms at unramified places. Childress, *Class Field Theory*, Chapter VI, proof of Theorem 2.6. -/
theorem awayUnitSubgroup_le_range_norm {L : Type*} [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : FinitePlace.ramifiedSet K L ⊆ S) :
    awayUnitSubgroup S ≤ (norm (K := K) (L := L)).range := by
  rw [awayUnitSubgroup_eq_freePowerSubgroup]
  apply freePowerSubgroup_le_range_norm 0 S ∅ ∅ (dvd_zero _)
  · simp
  · simp
  · intro v hv w
    exact FinitePlace.ramificationIdx_eq_one_of_ramifiedSet_subset hS
      (FinitePlace.PrimeAbove.place v w)
      (by simpa only [FinitePlace.PrimeAbove.below_place] using hv)

/-- The classes of the unit idèles away from `S` are norms when `L/K` is unramified outside
`S`; the class form of `awayUnitSubgroup_le_range_norm`. -/
theorem map_awayUnitSubgroup_le_range_norm {L : Type*} [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : FinitePlace.ramifiedSet K L ⊆ S) :
    (awayUnitSubgroup S).map
        (QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K)) ≤
      (IdeleClassGroup.norm (K := K) (L := L)).range := by
  calc
    (awayUnitSubgroup S).map
        (QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K)) ≤
      ((norm (K := K) (L := L)).range).map
        (QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K)) :=
          Subgroup.map_mono (awayUnitSubgroup_le_range_norm S hS)
    _ = (IdeleClassGroup.norm (K := K) (L := L)).range :=
      IdeleClassGroup.map_mk_range_norm

/-- The classes of the local-power subgroup lie in every subgroup `H` of $C_K$ containing the
`n`th powers and the classes of $U_K^S$, since $E\subseteq I_K^n\,U_K^S$
(`powerSubgroup_le_pow_sup`). Childress, *Class Field Theory*, Chapter VI, proofs of
Theorems 2.6 and 2.7. -/
theorem map_powerSubgroup_le {n : ℕ} (S : Finset (HeightOneSpectrum (𝓞 K)))
    {H : Subgroup (NumberField.IdeleClassGroup (𝓞 K) K)}
    (hpow : ∀ x : NumberField.IdeleClassGroup (𝓞 K) K, x ^ n ∈ H)
    (haway : (awayUnitSubgroup S).map
      (QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K)) ≤ H) :
    (powerSubgroup n S ∅).map
      (QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K)) ≤ H := by
  let q : NumberField.IdeleGroup (𝓞 K) K →*
      NumberField.IdeleClassGroup (𝓞 K) K :=
    QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K)
  have hpowrange :
      ((powMonoidHom n : NumberField.IdeleGroup (𝓞 K) K →*
        NumberField.IdeleGroup (𝓞 K) K).range).map q ≤ H := by
    rintro z ⟨a, ⟨b, rfl⟩, rfl⟩
    simpa only [powMonoidHom_apply, map_pow] using hpow (q b)
  have hsup :
      ((powMonoidHom n : NumberField.IdeleGroup (𝓞 K) K →*
        NumberField.IdeleGroup (𝓞 K) K).range ⊔ awayUnitSubgroup S).map q ≤ H := by
    rw [Subgroup.map_sup]
    exact sup_le hpowrange haway
  change (powerSubgroup n S ∅).map q ≤ H
  intro z hz
  obtain ⟨b, hb, rfl⟩ := (Subgroup.mem_map).1 hz
  exact hsup ((Subgroup.mem_map).2 ⟨b, (powerSubgroup_le_pow_sup n S) hb, rfl⟩)

/-- Norms of unit idèles away from the places above `S` are unit idèles away from `S`:
$N_{L/K}(U_L^{T}) \subseteq U_K^S$ for the set `T` of places above `S`. -/
theorem map_norm_awayUnitSubgroup_le {L : Type*} [Field L] [NumberField L] [Algebra K L]
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (awayUnitSubgroup (K := L) (FinitePlace.placesAbove (L := L) S)).map
      (norm (K := K) (L := L)) ≤ awayUnitSubgroup S := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨hi, hf, hu⟩ := (mem_awayUnitSubgroup
    (K := L) (FinitePlace.placesAbove (L := L) S) y).1 hy
  apply (mem_awayUnitSubgroup S _).2
  refine ⟨fun v ↦ ?_, fun v hv ↦ ?_, fun v hv ↦ ?_⟩
  · rw [infiniteComponent_norm_apply]
    apply Finset.prod_eq_one
    intro w _
    rw [hi w.1, map_one]
  · rw [finiteComponent_norm_apply]
    apply Finset.prod_eq_one
    intro w _
    rw [hf _ ((FinitePlace.mem_placesAbove S _).2 (by
      simpa only [FinitePlace.PrimeAbove.below_place] using hv)), map_one]
  · rw [finiteComponent_norm_apply]
    apply (FinitePlace.unitGroup v).prod_mem
    intro w _
    apply (FinitePlace.localNorm_mem_unitGroup_iff v _).2
    apply hu
    rw [FinitePlace.mem_placesAbove, FinitePlace.PrimeAbove.below_place]
    exact hv

/-! ### Unrestricted places and lattice operations

The free family permits different sets of unrestricted coordinates. Splitting an idèle at
those coordinates proves the join and intersection formulas. -/

/-- With no unrestricted places, `freePowerSubgroup` is Milne's local-power subgroup
`powerSubgroup n S ∅`. -/
theorem freePowerSubgroup_empty (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    freePowerSubgroup n S ∅ ∅ = powerSubgroup n S ∅ := by
  ext x
  simp [mem_freePowerSubgroup, mem_powerSubgroup, mem_sSubgroup, FinitePlace.below_self]

/-- With every place unrestricted, `freePowerSubgroup` is the group of idèles integral outside
`S`. -/
theorem freePowerSubgroup_univ (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    freePowerSubgroup n S Set.univ Set.univ = sSubgroup (K := K) (L := K) S := by
  ext x
  simp [mem_freePowerSubgroup]

/-- Intersections of `freePowerSubgroup`s intersect the unrestricted places. -/
theorem freePowerSubgroup_inf (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (I I' : Set (InfinitePlace K)) (T T' : Set (HeightOneSpectrum (𝓞 K))) :
    freePowerSubgroup n S I T ⊓ freePowerSubgroup n S I' T' =
      freePowerSubgroup n S (I ∩ I') (T ∩ T') := by
  ext x
  simp only [Subgroup.mem_inf, mem_freePowerSubgroup]
  constructor
  · rintro ⟨⟨hu, hi, hf⟩, ⟨_, hi', hf'⟩⟩
    refine ⟨hu, fun v hv ↦ ?_, fun v hS hv ↦ ?_⟩
    · rcases not_and_or.mp hv with h | h
      · exact hi v h
      · exact hi' v h
    · rcases not_and_or.mp hv with h | h
      · exact hf v hS h
      · exact hf' v hS h
  · rintro ⟨hu, hi, hf⟩
    refine ⟨⟨hu, fun v hv ↦ hi v ?_, fun v hS hv ↦ hf v hS ?_⟩,
      ⟨hu, fun v hv ↦ hi v ?_, fun v hS hv ↦ hf v hS ?_⟩⟩ <;>
      simp_all

/-- The selected factor used in the splitting for `freePowerSubgroup_sup` and
`map_freePowerSubgroup_le`. It retains exactly the components in `I` and `S ∩ T`. -/
private def selectedFreePart (S : Finset (HeightOneSpectrum (𝓞 K)))
    (I : Set (InfinitePlace K)) (T : Set (HeightOneSpectrum (𝓞 K)))
    (x : NumberField.IdeleGroup (𝓞 K) K) : NumberField.IdeleGroup (𝓞 K) K := by
  classical
  exact selectedSection S
    ((fun v ↦ if v ∈ I then infiniteComponent K v x else 1),
      fun v : S ↦ if v.1 ∈ T then finiteComponent K v.1 x else 1)

open scoped Classical in
/-- The selected coordinates of the factor are precisely those retained from `x`.
Used by `infiniteComponent_selectedFreePart` and `finiteComponent_selectedFreePart`. -/
private theorem selectedComponents_selectedFreePart (S : Finset (HeightOneSpectrum (𝓞 K)))
    (I : Set (InfinitePlace K)) (T : Set (HeightOneSpectrum (𝓞 K)))
    (x : NumberField.IdeleGroup (𝓞 K) K) :
    selectedComponents S (selectedFreePart S I T x) =
      ((fun v ↦ if v ∈ I then infiniteComponent K v x else 1),
        fun v : S ↦ if v.1 ∈ T then finiteComponent K v.1 x else 1) := by
  classical
  exact selectedComponents_section S _

open scoped Classical in
/-- The infinite component retained by `selectedFreePart`; used by
`selectedFreePart_split`. -/
private theorem infiniteComponent_selectedFreePart (S : Finset (HeightOneSpectrum (𝓞 K)))
    (I : Set (InfinitePlace K)) (T : Set (HeightOneSpectrum (𝓞 K)))
    (x : NumberField.IdeleGroup (𝓞 K) K) (v : InfinitePlace K) :
    infiniteComponent K v (selectedFreePart S I T x) =
      if v ∈ I then infiniteComponent K v x else 1 := by
  exact congrArg (fun c : InfiniteLocalIdele K ×
      (∀ w : S, (w.1.adicCompletion K)ˣ) ↦ c.1 v)
    (selectedComponents_selectedFreePart S I T x)

open scoped Classical in
/-- A finite component retained by `selectedFreePart`; used by
`selectedFreePart_split`. -/
private theorem finiteComponent_selectedFreePart (S : Finset (HeightOneSpectrum (𝓞 K)))
    (I : Set (InfinitePlace K)) (T : Set (HeightOneSpectrum (𝓞 K)))
    (x : NumberField.IdeleGroup (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S) :
    finiteComponent K v (selectedFreePart S I T x) =
      if v ∈ T then finiteComponent K v x else 1 := by
  exact congrArg (fun c : InfiniteLocalIdele K ×
      (∀ w : S, (w.1.adicCompletion K)ˣ) ↦ c.2 ⟨v, hv⟩)
    (selectedComponents_selectedFreePart S I T x)

/-- Outside `S`, the selected factor is one; used by `selectedFreePart_split` and
`selectedFreePart_eq_prod`. -/
private theorem finiteComponent_selectedFreePart_of_notMem
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (I : Set (InfinitePlace K)) (T : Set (HeightOneSpectrum (𝓞 K)))
    (x : NumberField.IdeleGroup (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ S) : finiteComponent K v (selectedFreePart S I T x) = 1 := by
  unfold selectedFreePart
  exact finiteComponent_selectedSection_of_notMem S _ v hv

/-- Splitting an idèle at the unrestricted places: the selected factor obeys the first
local conditions, while its quotient obeys the second. Used by `freePowerSubgroup_sup` and
`map_freePowerSubgroup_le`. -/
private theorem selectedFreePart_split (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (I I' : Set (InfinitePlace K)) (T T' : Set (HeightOneSpectrum (𝓞 K)))
    (x : NumberField.IdeleGroup (𝓞 K) K)
    (hx : x ∈ freePowerSubgroup n S (I ∪ I') (T ∪ T')) :
    selectedFreePart S I T x ∈ freePowerSubgroup n S I T ∧
      (selectedFreePart S I T x)⁻¹ * x ∈ freePowerSubgroup n S I' T' := by
  classical
  obtain ⟨hu, hi, hf⟩ := (mem_freePowerSubgroup n S (I ∪ I') (T ∪ T') x).1 hx
  have hpart : selectedFreePart S I T x ∈ freePowerSubgroup n S I T := by
    apply (mem_freePowerSubgroup n S I T _).2
    refine ⟨?_, ?_, ?_⟩
    · apply (mem_sSubgroup (K := K) (L := K) S _).2
      intro v hv
      have hv' : v ∉ S := by simpa only [FinitePlace.below_self] using hv
      rw [finiteComponent_selectedFreePart_of_notMem S I T x v hv']
      exact (FinitePlace.unitGroup v).one_mem
    · intro v hv
      refine ⟨1, ?_⟩
      rw [infiniteComponent_selectedFreePart]
      simp [hv]
    · intro v hvS hvT
      refine ⟨1, ?_⟩
      rw [finiteComponent_selectedFreePart S I T x v hvS]
      simp [hvT]
  refine ⟨hpart, (mem_freePowerSubgroup n S I' T' _).2 ⟨?_, ?_, ?_⟩⟩
  · exact (sSubgroup (K := K) (L := K) S).mul_mem
      ((sSubgroup (K := K) (L := K) S).inv_mem
        ((freePowerSubgroup_le_sSubgroup n S I T) hpart)) hu
  · intro v hvI'
    by_cases hvI : v ∈ I
    · refine ⟨1, ?_⟩
      rw [map_mul, map_inv, infiniteComponent_selectedFreePart]
      simp [hvI]
    · have hnone : v ∉ I ∪ I' := by simp [hvI, hvI']
      obtain ⟨y, hy⟩ := hi v hnone
      refine ⟨y, ?_⟩
      rw [map_mul, map_inv, infiniteComponent_selectedFreePart]
      simpa [hvI] using hy
  · intro v hvS hvT'
    by_cases hvT : v ∈ T
    · refine ⟨1, ?_⟩
      rw [map_mul, map_inv, finiteComponent_selectedFreePart S I T x v hvS]
      simp [hvT]
    · have hnone : v ∉ T ∪ T' := by simp [hvT, hvT']
      obtain ⟨y, hy⟩ := hf v hvS hnone
      refine ⟨y, ?_⟩
      rw [map_mul, map_inv, finiteComponent_selectedFreePart S I T x v hvS]
      simpa [hvT] using hy

/-- Joins of `freePowerSubgroup`s unite the unrestricted places. Childress, *Class Field
Theory*, Chapter VI, proof of Theorem 2.9, where $B_1B_2$ is the group of idèles integral outside
`S`. -/
theorem freePowerSubgroup_sup (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (I I' : Set (InfinitePlace K)) (T T' : Set (HeightOneSpectrum (𝓞 K))) :
    freePowerSubgroup n S I T ⊔ freePowerSubgroup n S I' T' =
      freePowerSubgroup n S (I ∪ I') (T ∪ T') := by
  have hleft : freePowerSubgroup n S I T ≤
      freePowerSubgroup n S (I ∪ I') (T ∪ T') := by
    intro x hx
    obtain ⟨hu, hi, hf⟩ := (mem_freePowerSubgroup n S I T x).1 hx
    exact (mem_freePowerSubgroup n S (I ∪ I') (T ∪ T') x).2
      ⟨hu, fun v hv ↦ hi v (fun h ↦ hv (Or.inl h)),
        fun v hS hv ↦ hf v hS (fun h ↦ hv (Or.inl h))⟩
  have hright : freePowerSubgroup n S I' T' ≤
      freePowerSubgroup n S (I ∪ I') (T ∪ T') := by
    intro x hx
    obtain ⟨hu, hi, hf⟩ := (mem_freePowerSubgroup n S I' T' x).1 hx
    exact (mem_freePowerSubgroup n S (I ∪ I') (T ∪ T') x).2
      ⟨hu, fun v hv ↦ hi v (fun h ↦ hv (Or.inr h)),
        fun v hS hv ↦ hf v hS (fun h ↦ hv (Or.inr h))⟩
  apply le_antisymm (sup_le hleft hright)
  intro x hx
  obtain ⟨hfirst, hsecond⟩ := selectedFreePart_split n S I I' T T' x hx
  have h := (freePowerSubgroup n S I T ⊔ freePowerSubgroup n S I' T').mul_mem
    (Subgroup.mem_sup_left hfirst) (Subgroup.mem_sup_right hsecond)
  convert h using 1
  group

/-! ### Classes in a subgroup of the idèle class group

An idèle of `freePowerSubgroup n S I T` is a product of idèles supported at single unrestricted
places and an element of `powerSubgroup n S ∅`. So its class lies in any subgroup of $C_K$ that
contains the `n`th powers, the classes of the unit idèles away from `S`, and the images of the
local groups at the unrestricted places. -/

open scoped Classical in
/-- The selected factor is the finite product of idèles supported at its unrestricted places.
Used by `map_freePowerSubgroup_le`. -/
private theorem selectedFreePart_eq_prod (S : Finset (HeightOneSpectrum (𝓞 K)))
    (I : Set (InfinitePlace K)) (T : Set (HeightOneSpectrum (𝓞 K)))
    (x : NumberField.IdeleGroup (𝓞 K) K) :
    selectedFreePart S I T x =
      (∏ v : InfinitePlace K, NumberField.IdeleGroup.ofCompletion (𝓞 K) K v
        (if v ∈ I then infiniteComponent K v x else 1)) *
      ∏ v : S, NumberField.IdeleGroup.ofAdicCompletion (𝓞 K) K v.1
        (if v.1 ∈ T then finiteComponent K v.1 x else 1) := by
  classical
  apply ext K
  · intro v
    rw [infiniteComponent_selectedFreePart, map_mul, map_prod, map_prod]
    simp only [infiniteComponent_ofAdicCompletion, Finset.prod_const_one, mul_one]
    rw [Finset.prod_eq_single v]
    · exact (infiniteComponent_ofCompletion_self K v _).symm
    · intro w _ hw
      exact infiniteComponent_ofCompletion_of_ne K v w (Ne.symm hw) _
    · simp
  · intro v
    by_cases hv : v ∈ S
    · rw [finiteComponent_selectedFreePart S I T x v hv, map_mul, map_prod, map_prod]
      simp only [finiteComponent_ofCompletion, Finset.prod_const_one, one_mul]
      rw [Finset.prod_eq_single ⟨v, hv⟩]
      · exact (finiteComponent_ofAdicCompletion_self K v _).symm
      · intro w _ hw
        exact finiteComponent_ofAdicCompletion_of_ne K w.1 v
          (fun h ↦ hw (Subtype.ext h.symm)) _
      · simp
    · rw [finiteComponent_selectedFreePart_of_notMem S I T x v hv,
        map_mul, map_prod, map_prod]
      simp only [finiteComponent_ofCompletion, Finset.prod_const_one, one_mul]
      symm
      apply Finset.prod_eq_one
      intro w _
      exact finiteComponent_ofAdicCompletion_of_ne K w.1 v
        (fun h ↦ hv (h ▸ w.2)) _

/-- The class of the selected factor lies in any subgroup containing the images of its
unrestricted local groups. Used by `map_freePowerSubgroup_le`. -/
private theorem selectedFreePart_class_mem (S : Finset (HeightOneSpectrum (𝓞 K)))
    (I : Set (InfinitePlace K)) (T : Set (HeightOneSpectrum (𝓞 K)))
    (x : NumberField.IdeleGroup (𝓞 K) K)
    {H : Subgroup (NumberField.IdeleClassGroup (𝓞 K) K)}
    (hinf : ∀ v ∈ I, (NumberField.IdeleClassGroup.ofCompletion (𝓞 K) K v).range ≤ H)
    (hfin : ∀ v ∈ S, v ∈ T →
      (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 K) K v).range ≤ H) :
    (QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K))
      (selectedFreePart S I T x) ∈ H := by
  classical
  let q : NumberField.IdeleGroup (𝓞 K) K →*
      NumberField.IdeleClassGroup (𝓞 K) K :=
    QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K)
  change q (selectedFreePart S I T x) ∈ H
  rw [selectedFreePart_eq_prod, map_mul, map_prod, map_prod]
  apply H.mul_mem
  · apply H.prod_mem (t := Finset.univ)
      (f := fun v : InfinitePlace K ↦ q (NumberField.IdeleGroup.ofCompletion (𝓞 K) K v
        (if v ∈ I then infiniteComponent K v x else 1)))
    intro v _
    by_cases hv : v ∈ I
    · exact hinf v hv ⟨_, rfl⟩
    · simp [hv]
  · apply H.prod_mem (t := Finset.univ)
      (f := fun v : S ↦ q (NumberField.IdeleGroup.ofAdicCompletion (𝓞 K) K v.1
        (if v.1 ∈ T then finiteComponent K v.1 x else 1)))
    intro v _
    by_cases hv : v.1 ∈ T
    · exact hfin v.1 v.2 hv ⟨_, rfl⟩
    · simp [hv]

/-- The classes of `freePowerSubgroup n S I T` lie in a subgroup `H` of $C_K$ containing the
`n`th powers, the classes of $U_K^S$, and the images of $K_v^\times$ for every unrestricted
place `v`. Childress, *Class Field Theory*, Chapter VI, proof of Theorem 2.9, where
$B_1\subseteq H$ and $B_i\subseteq H_i$. -/
theorem map_freePowerSubgroup_le {n : ℕ} (S : Finset (HeightOneSpectrum (𝓞 K)))
    (I : Set (InfinitePlace K)) (T : Set (HeightOneSpectrum (𝓞 K)))
    {H : Subgroup (NumberField.IdeleClassGroup (𝓞 K) K)}
    (hpow : ∀ x : NumberField.IdeleClassGroup (𝓞 K) K, x ^ n ∈ H)
    (haway : (awayUnitSubgroup S).map
      (QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K)) ≤ H)
    (hinf : ∀ v ∈ I, (NumberField.IdeleClassGroup.ofCompletion (𝓞 K) K v).range ≤ H)
    (hfin : ∀ v ∈ S, v ∈ T →
      (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 K) K v).range ≤ H) :
    (freePowerSubgroup n S I T).map
      (QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K)) ≤ H := by
  classical
  let q : NumberField.IdeleGroup (𝓞 K) K →*
      NumberField.IdeleClassGroup (𝓞 K) K :=
    QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K)
  change (freePowerSubgroup n S I T).map q ≤ H
  rintro z ⟨x, hx, rfl⟩
  have hsplit := selectedFreePart_split n S I ∅ T ∅ x (by simpa using hx)
  have hrest : (selectedFreePart S I T x)⁻¹ * x ∈ powerSubgroup n S ∅ := by
    rw [← freePowerSubgroup_empty n S]
    exact hsplit.2
  have hfirst : q (selectedFreePart S I T x) ∈ H :=
    selectedFreePart_class_mem S I T x hinf hfin
  have hsecond : q ((selectedFreePart S I T x)⁻¹ * x) ∈ H :=
    (map_powerSubgroup_le S hpow haway)
      ((Subgroup.mem_map).2 ⟨_, hrest, rfl⟩)
  have hmul := H.mul_mem hfirst hsecond
  convert hmul using 1
  rw [← map_mul]
  congr 1
  group

end SIC.IdeleGroup
