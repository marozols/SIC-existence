/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Ideles.SIdeles
import SICs.ClassField.Ideles.RaySubgroup
import SICs.ClassField.Local.NormTopology
import SICs.ClassField.Local.Unramified

/-!
# Local membership and openness of idèle norm subgroups

Idèle norm membership is determined by the local norm subgroups, cyclic idèle norm
subgroups are open, and cyclic norm subgroups contain the ray idèles of a suitable modulus.

This follows Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII, §2,
"The norm map on idèles" and the cyclic case of Proposition 2.8, and the cyclic case of
Chapter V, Corollary 4.13.

## The argument

Conjugate completions have the same norm image. Thus the product norm at a base place has
the image of any one local norm. Choose local preimages; the characterization of integral-unit
norms makes these preimages integral outside the exceptional support of the given idèle.
They assemble to an idèle. For openness, unramified unit-norm surjectivity lets us take local
norm neighborhoods at the infinite and finitely many ramified places and integral units
elsewhere. A subgroup containing an open subgroup is open, so principal idèles times norms form
an open subgroup as well.

The same local description gives a modulus. Each cyclic local norm subgroup at a finite place
is open, so it contains a higher unit group $U_v^{(n_v)}$. At unramified places the norms of
integral units are all integral units, and at the infinite places every positive real number is
a norm. A modulus divisible by $\mathfrak p_v^{n_v}$ at the ramified places and at any further
prescribed places therefore has all its ray idèles among the norms (Childress, *Class Field
Theory* (2009), Chapter IV, Proposition 5.6(i) and the remark following it).
-/

noncomputable section

open IsDedekindDomain NumberField
open scoped NumberField SIC.FinitePlace NumberField.LiesOver SIC.InfinitePlace

namespace SIC.IdeleGroup

/-- A product of coordinate homomorphisms evaluates a single supported coordinate by its
own homomorphism; used by `exists_norm_preimage`. -/
private theorem prod_map_mulSingle {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : ι → Type*} [∀ i, MulOneClass (M i)] {N : Type*} [CommMonoid N]
    (f : ∀ i, M i →* N) (i : ι) (x : M i) :
    (∏ j, f j (Pi.mulSingle i x j)) = f i x := by
  simp_rw [Pi.apply_mulSingle (fun i ↦ f i) (fun i ↦ map_one _),
    Fintype.prod_pi_mulSingle']


variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [IsGalois K L]


/-! ### Local membership

Galois transport preserves norms, so all completion norms above a place have the same image.
At one selected place choose a preimage, and put one at all other places. The preimages are
integral wherever the original component is integral, by `localNorm_mem_unitGroup_iff`.
The coordinate equivalence for idèles integral outside a finite set assembles them.
-/

/-- Every infinite component of an idèle norm is a norm from any chosen place above it.
Milne, *Class Field Theory*, Chapter VII, §2, "The norm map on idèles"; used by
`mem_range_norm_iff`. -/
private theorem infiniteComponent_norm_mem
    (v : InfinitePlace K) (w : SIC.InfinitePlace.PlaceAbove (L := L) v)
    (x : NumberField.IdeleGroup (𝓞 L) L) :
    infiniteComponent K v (norm (K := K) (L := L) x) ∈
      (SIC.InfinitePlace.localNorm v w.1).range := by
  rw [infiniteComponent_norm_apply]
  apply Subgroup.prod_mem
  intro w' _
  obtain ⟨σ, hσ⟩ := SIC.InfinitePlace.exists_smul_eq v w'.1 w.1
  refine ⟨Units.map (SIC.InfinitePlace.completionEquiv σ.toRingEquiv w'.1 w.1 hσ)
    (infiniteComponent L w'.1 x), ?_⟩
  exact SIC.InfinitePlace.localNorm_completionEquiv σ v w'.1 w.1 hσ _

/-- Every finite component of an idèle norm is a norm from any chosen place above it.
Milne, *Class Field Theory*, Chapter VII, §2, "The norm map on idèles"; used by
`mem_range_norm_iff`. -/
private theorem finiteComponent_norm_mem
    (v : HeightOneSpectrum (𝓞 K)) (w : FinitePlace.PrimeAbove (L := L) v)
    (x : NumberField.IdeleGroup (𝓞 L) L) :
    finiteComponent K v (norm (K := K) (L := L) x) ∈
      (FinitePlace.localNorm v (FinitePlace.PrimeAbove.place v w)).range := by
  rw [finiteComponent_norm_apply]
  apply Subgroup.prod_mem
  intro w' _
  obtain ⟨σ, hσ⟩ := FinitePlace.PrimeAbove.exists_smul_eq v w' w
  have hp : FinitePlace.mapEquiv σ.toRingEquiv (FinitePlace.PrimeAbove.place v w') =
      FinitePlace.PrimeAbove.place v w := by
    simpa only [FinitePlace.PrimeAbove.place_smul, FinitePlace.smul_def] using
      congrArg (FinitePlace.PrimeAbove.place v) hσ
  exact ⟨Units.map (FinitePlace.completionEquiv σ.toRingEquiv
    (FinitePlace.PrimeAbove.place v w') (FinitePlace.PrimeAbove.place v w) hp)
      (finiteComponent L (FinitePlace.PrimeAbove.place v w') x),
    FinitePlace.localNorm_completionEquiv σ v
      (FinitePlace.PrimeAbove.place v w') (FinitePlace.PrimeAbove.place v w) hp
      (finiteComponent L (FinitePlace.PrimeAbove.place v w') x)⟩

omit [IsGalois K L] in
/-- Local norm preimages assemble to an idèle: preimages of integral norms are integral.
Milne, *Class Field Theory*, Chapter VII, §2, "The norm map on idèles"; used by
`mem_range_norm_iff`. -/
private theorem exists_norm_preimage
    (wi : ∀ v : InfinitePlace K, SIC.InfinitePlace.PlaceAbove (L := L) v)
    (wf : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.PrimeAbove (L := L) v)
    (x : NumberField.IdeleGroup (𝓞 K) K)
    (hi : ∀ v, infiniteComponent K v x ∈ (SIC.InfinitePlace.localNorm v (wi v).1).range)
    (hf : ∀ v, finiteComponent K v x ∈
      (FinitePlace.localNorm v (FinitePlace.PrimeAbove.place v (wf v))).range) :
    x ∈ (norm (K := K) (L := L)).range := by
  classical
  choose yi hyi using hi
  choose yf hyf using hf
  obtain ⟨S, hS⟩ := exists_mem_sSubgroup (K := K) (L := K) x
  have hu (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
      yf v ∈ FinitePlace.unitGroup (FinitePlace.PrimeAbove.place v (wf v)) := by
    apply (FinitePlace.localNorm_mem_unitGroup_iff v _).mp
    rw [hyf]
    exact hS v (by simpa only [FinitePlace.below_self] using hv)
  let c : SComponents (L := L) S :=
    (fun v ↦ Pi.mulSingle (wi v) (yi v),
      (fun v ↦ Pi.mulSingle (wf v.1) (yf v.1),
        fun v ↦ Pi.mulSingle (wf v.1) ⟨yf v.1, hu v.1 v.2⟩))
  let y := (sComponentsEquiv (L := L) S).symm c
  have hy : sComponentsEquiv S y = c := MulEquiv.apply_symm_apply _ _
  refine ⟨y.1, ext K ?_ ?_⟩
  · intro v
    rw [infiniteComponent_norm_apply]
    simp_rw [← sComponentsEquiv_infinite S y v, hy]
    dsimp only [c]
    exact (prod_map_mulSingle (fun w : SIC.InfinitePlace.PlaceAbove (L := L) v ↦
      SIC.InfinitePlace.localNorm v w.1) (wi v) (yi v)).trans (hyi v)
  · intro v
    rw [finiteComponent_norm_apply]
    by_cases hv : v ∈ S
    · simp_rw [← sComponentsEquiv_inside S y ⟨v, hv⟩, hy]
      dsimp only [c]
      exact (prod_map_mulSingle (fun w : FinitePlace.PrimeAbove (L := L) v ↦
        FinitePlace.localNorm v (FinitePlace.PrimeAbove.place v w))
        (wf v) (yf v)).trans (hyf v)
    · simp_rw [← sComponentsEquiv_outside S y ⟨v, hv⟩, hy]
      dsimp only [c]
      exact (prod_map_mulSingle (fun w : FinitePlace.PrimeAbove (L := L) v ↦
        (FinitePlace.localNorm v (FinitePlace.PrimeAbove.place v w)).comp
          (FinitePlace.unitGroup (FinitePlace.PrimeAbove.place v w)).subtype)
        (wf v) ⟨yf v, hu v hv⟩).trans (hyf v)


/-- An idèle is a norm exactly when each component is a local norm, at any chosen place above
it. Milne, *Class Field Theory*, Chapter VII, §2, "The norm map on idèles". -/
theorem mem_range_norm_iff
    (wi : ∀ v : InfinitePlace K, SIC.InfinitePlace.PlaceAbove (L := L) v)
    (wf : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.PrimeAbove (L := L) v)
    (x : NumberField.IdeleGroup (𝓞 K) K) :
    x ∈ (norm (K := K) (L := L)).range ↔
      (∀ v, infiniteComponent K v x ∈ (SIC.InfinitePlace.localNorm v (wi v).1).range) ∧
      (∀ v, finiteComponent K v x ∈
        (FinitePlace.localNorm v (FinitePlace.PrimeAbove.place v (wf v))).range) := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨fun v ↦ infiniteComponent_norm_mem v (wi v) y,
      fun v ↦ finiteComponent_norm_mem v (wf v) y⟩
  · rintro ⟨hi, hf⟩
    exact exists_norm_preimage wi wf x hi hf

/-! ### Open norm subgroups

Choose a finite set containing the ramified places. Require local norms at its places and all
infinite places, and integral units elsewhere. These conditions define an open neighborhood of
one consisting of norms, since the unramified local norms surject onto the integral units.
-/

/-- Local norm conditions at the infinite and selected finite places, together with integral
units elsewhere, define an open set; used by `isOpen_range_norm`. -/
private theorem isOpen_local_norm_conditions [IsCyclic (L ≃ₐ[K] L)]
    (wi : ∀ v : InfinitePlace K, SIC.InfinitePlace.PlaceAbove (L := L) v)
    (wf : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.PrimeAbove (L := L) v)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsOpen {x : NumberField.IdeleGroup (𝓞 K) K |
      (∀ v, infiniteComponent K v x ∈ (SIC.InfinitePlace.localNorm v (wi v).1).range) ∧
      (∀ v : S, finiteComponent K v.1 x ∈
        (FinitePlace.localNorm v.1 (FinitePlace.PrimeAbove.place v.1 (wf v.1))).range) ∧
      (∀ v, v ∉ S → finiteComponent K v x ∈ FinitePlace.unitGroup v)} := by
  have hi : IsOpen {x : NumberField.IdeleGroup (𝓞 K) K |
      ∀ v, infiniteComponent K v x ∈ (SIC.InfinitePlace.localNorm v (wi v).1).range} := by
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro v
    exact (SIC.InfinitePlace.isOpen_range_localNorm v (wi v).1).preimage
      ((continuous_apply v).comp ((componentsContinuousEquiv K).continuous.fst))
  have hf : IsOpen {x : NumberField.IdeleGroup (𝓞 K) K |
      ∀ v : S, finiteComponent K v.1 x ∈
        (FinitePlace.localNorm v.1 (FinitePlace.PrimeAbove.place v.1 (wf v.1))).range} := by
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro v
    exact (FinitePlace.isOpen_range_localNorm v.1
      (FinitePlace.PrimeAbove.place v.1 (wf v.1))).preimage
      ((RestrictedProduct.continuous_eval v.1).comp
        ((componentsContinuousEquiv K).continuous.snd))
  have hu : IsOpen {x : NumberField.IdeleGroup (𝓞 K) K |
      ∀ v, v ∉ S → finiteComponent K v x ∈ FinitePlace.unitGroup v} := by
    exact (RestrictedProduct.isOpen_forall_imp_mem
      (fun v : HeightOneSpectrum (𝓞 K) ↦ FinitePlace.isOpen_unitGroup v)).preimage
          ((componentsContinuousEquiv K).continuous.snd)
  exact hi.inter (hf.inter hu)


/-- The norm subgroup of a cyclic extension is open in the idèle group. Milne,
*Class Field Theory*, Chapter VII, Proposition 2.8, cyclic case. -/
theorem isOpen_range_norm [IsCyclic (L ≃ₐ[K] L)] :
    IsOpen ((norm (K := K) (L := L)).range : Set (NumberField.IdeleGroup (𝓞 K) K)) := by
  classical
  let wi (v : InfinitePlace K) : SIC.InfinitePlace.PlaceAbove (L := L) v :=
    Classical.choice inferInstance
  let wf (v : HeightOneSpectrum (𝓞 K)) : FinitePlace.PrimeAbove (L := L) v :=
    Classical.choice inferInstance
  let S := FinitePlace.ramifiedSet K L
  apply Subgroup.isOpen_of_mem_nhds
  apply Filter.mem_of_superset ((isOpen_local_norm_conditions wi wf S).mem_nhds (x := 1) ?_)
  · intro x hx
    apply (mem_range_norm_iff wi wf x).mpr
    refine ⟨hx.1, fun v ↦ ?_⟩
    by_cases hv : v ∈ S
    · exact hx.2.1 ⟨v, hv⟩
    · have hram := FinitePlace.ramificationIdx_eq_one_of_notMem_ramifiedSet (K := K)
        (FinitePlace.PrimeAbove.place v (wf v)) (by
        simpa only [FinitePlace.PrimeAbove.below_place] using hv)
      have hunit := hx.2.2 v hv
      exact FinitePlace.unitGroup_le_range_localNorm v
        (FinitePlace.PrimeAbove.place v (wf v)) hram hunit
  · exact ⟨fun v ↦ by simp, fun v ↦ by simp, fun v _ ↦ by simp⟩

/-- Principal idèles times cyclic norms form an open subgroup. This is the open subgroup
used in Milne, *Class Field Theory*, Chapter VII, proof of Lemma 4.5. -/
theorem isOpen_principal_sup_range_norm [IsCyclic (L ≃ₐ[K] L)] :
    IsOpen (↑(NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔
      (norm (K := K) (L := L)).range) : Set (NumberField.IdeleGroup (𝓞 K) K)) := by
  exact Subgroup.isOpen_mono le_sup_right (isOpen_range_norm (K := K) (L := L))

end SIC.IdeleGroup

namespace SIC.IdeleGroup

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-! ### Ray idèles inside cyclic norm subgroups

A modulus whose exponents at the ramified and prescribed places are large enough has all its ray
idèles among the norms of a cyclic extension. -/

open scoped Classical in
/-- **Cyclic norm subgroups contain ray subgroups**: for a cyclic extension `L/K` and a finite
set `T` of primes of `K`, some nonzero modulus supported on `T` and the ramified places, divisible
by every prime of `T`, has
$E^+_{K,\mathfrak m} \subseteq N_{L/K} J_L$. Childress, *Class Field Theory*, Chapter IV,
Proposition 5.6(i) and the remark following it; Milne, *Class Field Theory*, Chapter V,
Corollary 4.13. -/
theorem exists_raySubgroup_le_range_norm [IsCyclic (L ≃ₐ[K] L)]
    (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ m : Ideal (𝓞 K), m ≠ ⊥ ∧ (∀ v ∈ T, FinitePlace.modulusExponent m v ≠ 0) ∧
      raySubgroup Set.univ m ≤ (norm (K := K) (L := L)).range ∧
      FinitePlace.modulusSupport m ⊆ T ∪ FinitePlace.ramifiedSet K L := by
  classical
  let wi (v : InfinitePlace K) : SIC.InfinitePlace.PlaceAbove (L := L) v :=
    Classical.choice inferInstance
  let wf (v : HeightOneSpectrum (𝓞 K)) : FinitePlace.PrimeAbove (L := L) v :=
    Classical.choice inferInstance
  let S := T ∪ FinitePlace.ramifiedSet K L
  have hlocal (v : HeightOneSpectrum (𝓞 K)) :
      ∃ n, (FinitePlace.higherUnitGroup v n : Set (v.adicCompletion K)ˣ) ⊆
        (FinitePlace.localNorm v (FinitePlace.PrimeAbove.place v (wf v))).range := by
    apply FinitePlace.exists_higherUnitGroup_subset v
    exact (FinitePlace.isOpen_range_localNorm v
      (FinitePlace.PrimeAbove.place v (wf v))).mem_nhds (one_mem _)
  choose n hn using hlocal
  obtain ⟨m, hm, hlarge, hsupport⟩ := FinitePlace.exists_lt_modulusExponent S n
  refine ⟨m, hm, ?_, ?_, hsupport⟩
  · intro v hv
    have hvS : v ∈ S := Finset.mem_union_left _ hv
    exact Nat.ne_of_gt ((Nat.zero_le (n v)).trans_lt (hlarge v hvS))
  · intro x hx
    have hxpos := ((mem_raySubgroup_univ_iff m x).mp hx).1
    apply (mem_range_norm_iff wi wf x).mpr
    refine ⟨?_, ?_⟩
    · intro v
      rcases (wi v).1.isUnramified_or_isRamified K with hw | hw
      · exact SIC.InfinitePlace.localNorm_surjective_of_unramified v (wi v).1 hw _
      · rw [SIC.InfinitePlace.mem_range_localNorm_iff_pos v (wi v).1 hw]
        simpa only [NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal_apply] using
          (hxpos v (NumberField.InfinitePlace.IsRamified.liesOver_isReal_under
            (wi v).1 v hw))
    · intro v
      by_cases hv : v ∈ S
      · have hlevel : n v ≤ FinitePlace.modulusExponent m v :=
          (hlarge v hv).le
        exact hn v ((FinitePlace.higherUnitGroup_anti v hlevel) (hx.2 v))
      · have hv₀ : v ∉ FinitePlace.ramifiedSet K L :=
          fun hv₀ ↦ hv (Finset.mem_union_right T hv₀)
        have hram := FinitePlace.ramificationIdx_eq_one_of_notMem_ramifiedSet (K := K)
          (FinitePlace.PrimeAbove.place v (wf v)) (by
          simpa only [FinitePlace.PrimeAbove.below_place] using hv₀)
        have hunit := FinitePlace.rayUnitGroup_le_unitGroup m v (hx.2 v)
        exact FinitePlace.unitGroup_le_range_localNorm v
          (FinitePlace.PrimeAbove.place v (wf v)) hram hunit

end SIC.IdeleGroup
