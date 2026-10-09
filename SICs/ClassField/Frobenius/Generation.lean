/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.FieldTheory.Abelian
import SICs.ClassField.Ideles.Approximation
import SICs.ClassField.Ideles.FirstInequality
import SICs.ClassField.Ideles.NormTopology
import SICs.ClassField.Frobenius.Tower

/-!
# Splitting and Frobenius generation in solvable extensions

A solvable extension in which almost every finite place splits completely is trivial, and its
Frobenius elements away from a finite set of base places containing the ramified ones generate
the Galois group.

This follows Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII, Lemma 4.5 and
Propositions 4.6–4.7.

## The argument

A nontrivial solvable Galois group has a nontrivial cyclic quotient. Its fixed field gives a
cyclic subextension, whose principal-times-norm subgroup is closed. The first inequality
then rules out density of that subgroup. If almost every place splits, weak approximation
makes the subgroup dense; hence the extension is trivial.

For Frobenius generation, first exclude primes over a finite set of base places. Conjugation
preserves the remaining Frobenius elements (`closure_isFrobeniusAt_normal`), so their generated
subgroup is normal. In its fixed field every remaining Frobenius restricts to the identity. At
an unramified prime, Frobenius generates the decomposition group, so the corresponding local
degree is one. The solvable splitting criterion makes the fixed field equal to the base field,
and Galois correspondence makes the subgroup the whole group.
-/

noncomputable section

open IsDedekindDomain NumberField
open scoped NumberField SIC.FinitePlace Pointwise

namespace SIC.IdeleGroup

/-! ### Splitting detected by idèle norms

The cyclic subextension makes the norm residue subgroup closed. Density would contradict
the first inequality; almost-everywhere splitting supplies that density by approximation. -/

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [IsGalois K L] [Group.IsSolvable (L ≃ₐ[K] L)]

/-- A solvable extension is trivial if principal idèles times a subgroup of norms are dense.
Milne, *Class Field Theory*, Chapter VII, Lemma 4.5. -/
theorem finrank_eq_one_of_dense_norm
    (D : Subgroup (NumberField.IdeleGroup (𝓞 K) K))
    (hD : D ≤ (norm (K := K) (L := L)).range)
    (hdense : Dense (↑(NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔ D) :
      Set (NumberField.IdeleGroup (𝓞 K) K))) :
    Module.finrank K L = 1 := by
  by_contra hdegree
  obtain ⟨E, hgal, hcyclic, hE⟩ := SIC.exists_cyclic_subextension hdegree
  have hDE : D ≤ (norm (K := K) (L := E)).range := by
    intro x hx
    obtain ⟨y, rfl⟩ := hD hx
    exact ⟨norm (K := E) (L := L) y, norm_norm y⟩
  let U : Subgroup (NumberField.IdeleGroup (𝓞 K) K) :=
    NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔ (norm (K := K) (L := E)).range
  have hUdense : Dense (U : Set (NumberField.IdeleGroup (𝓞 K) K)) :=
    hdense.mono (sup_le_sup_left hDE _)
  have hUclosed : IsClosed (U : Set (NumberField.IdeleGroup (𝓞 K) K)) :=
    U.isClosed_of_isOpen (isOpen_principal_sup_range_norm (K := K) (L := E))
  have hUtop : U = ⊤ :=
    Subgroup.coe_eq_univ.mp (hUclosed.closure_eq.symm.trans hUdense.closure_eq)
  have hfirst := firstInequality (K := K) (L := E)
  change Module.finrank K E ≤ U.index at hfirst
  rw [hUtop, Subgroup.index_top] at hfirst
  exact hE (Nat.le_antisymm hfirst (Nat.succ_le_of_lt Module.finrank_pos))

omit [Group.IsSolvable (L ≃ₐ[K] L)] in
/-- If all places outside `S` split completely, every idèle in `I^S` is a norm. This is the
local-norm step in Milne, *Class Field Theory*, Chapter VII, proof of Proposition 4.6. -/
private theorem awaySubgroup_le_range_norm (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hsplit : ∀ v, v ∉ S → ∀ w : FinitePlace.PrimeAbove (L := L) v,
      Module.finrank (v.adicCompletion K)
        ((FinitePlace.PrimeAbove.place v w).adicCompletion L) = 1) :
    awaySubgroup S ≤ (norm (K := K) (L := L)).range := by
  classical
  let wi (v : InfinitePlace K) : SIC.InfinitePlace.PlaceAbove (L := L) v :=
    Classical.choice inferInstance
  let wf (v : HeightOneSpectrum (𝓞 K)) : FinitePlace.PrimeAbove (L := L) v :=
    Classical.choice inferInstance
  intro x hx
  obtain ⟨hi, hf⟩ := (mem_awaySubgroup S x).mp hx
  apply (mem_range_norm_iff wi wf x).mpr
  constructor
  · intro v
    rw [hi v]
    exact Subgroup.one_mem _
  · intro v
    by_cases hv : v ∈ S
    · rw [hf v hv]
      exact Subgroup.one_mem _
    · refine ⟨Units.map (FinitePlace.completionMap v (FinitePlace.PrimeAbove.place v (wf v)))
        (finiteComponent K v x), ?_⟩
      rw [FinitePlace.localNorm_principal, hsplit v hv (wf v), pow_one]

end SIC.IdeleGroup

namespace SIC

/-! ### Extensions in which almost every place splits

If all but finitely many places split, weak approximation makes the norm subgroup dense,
forcing the extension to be trivial. -/

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [IsGalois K L] [Group.IsSolvable (L ≃ₐ[K] L)]

/-- If almost every finite place splits completely in a solvable extension, the extension is
trivial. Milne, *Class Field Theory*, Chapter VII, Proposition 4.6, contrapositive. -/
theorem finrank_eq_one_of_eventually_split
    (hsplit : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      ∀ w : FinitePlace.PrimeAbove (L := L) v,
        Module.finrank (v.adicCompletion K)
          ((FinitePlace.PrimeAbove.place v w).adicCompletion L) = 1) :
    Module.finrank K L = 1 := by
  classical
  let S := (Filter.eventually_cofinite.mp hsplit).toFinset
  apply IdeleGroup.finrank_eq_one_of_dense_norm (IdeleGroup.awaySubgroup S)
    (IdeleGroup.awaySubgroup_le_range_norm S ?_)
    (IdeleGroup.dense_principal_sup_awaySubgroup S)
  intro v hv
  simpa only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hv

end SIC

namespace SIC

/-! ### Generation by Frobenius elements

The fixed field of the subgroup generated away from finitely many ramified primes splits
almost everywhere, so the splitting criterion makes that subgroup the whole Galois group. -/

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [IsGalois K L] [Group.IsSolvable (L ≃ₐ[K] L)]

omit [IsGalois K L] [Group.IsSolvable (L ≃ₐ[K] L)] in
/-- The Frobenius elements outside the primes above `S`, the stable generating set in
Milne, *Class Field Theory*, Chapter VII, proof of Proposition 4.7. -/
private def frobeniusOutside (S : Finset (HeightOneSpectrum (𝓞 K))) : Set (L ≃ₐ[K] L) :=
  {g | ∃ w : HeightOneSpectrum (𝓞 L), FinitePlace.below (K := K) w ∉ S ∧
    IsFrobeniusAt K L g (FinitePlace.below (K := K) w).asIdeal w.asIdeal}

omit [Group.IsSolvable (L ≃ₐ[K] L)] in
/-- A normal subgroup containing the Frobenius elements outside `S` has a fixed field in
which every place outside `S` splits completely. This is the splitting step in Milne,
*Class Field Theory*, Chapter VII, proof of Proposition 4.7. -/
private theorem fixedField_splits_outside (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : FinitePlace.ramifiedSet K L ⊆ S)
    (H : Subgroup (L ≃ₐ[K] L)) [H.Normal]
    (hH : frobeniusOutside (K := K) (L := L) S ⊆ (H : Set (L ≃ₐ[K] L)))
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S)
    (p : FinitePlace.PrimeAbove (L := IntermediateField.fixedField H) v) :
    Module.finrank (v.adicCompletion K) ((FinitePlace.PrimeAbove.place v p).adicCompletion
      (IntermediateField.fixedField H)) = 1 := by
  let E := IntermediateField.fixedField H
  have : IsGalois K E := IsGalois.of_fixedField_normal_subgroup H
  let w := FinitePlace.PrimeAbove.place v p
  obtain ⟨q⟩ := (inferInstance : Nonempty (FinitePlace.PrimeAbove (L := L) w))
  let Q := FinitePlace.PrimeAbove.place w q
  have : Q.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.trans Q.asIdeal w.asIdeal v.asIdeal
  have hbelow : FinitePlace.below (K := K) Q = v := FinitePlace.below_eq_of_liesOver v Q
  have hout : FinitePlace.below (K := K) Q ∉ S := by rwa [hbelow]
  obtain ⟨g, hg⟩ := exists_isFrobeniusAt (K := K) (H := L) v.asIdeal Q.asIdeal v.ne_bot
  have hgH : g ∈ H := hH ⟨Q, hout, by simpa only [hbelow] using hg⟩
  have hres : g.restrictNormal E = 1 := (AlgEquiv.restrictNormal_eq_one_iff E g).mpr
    (fun x hx => (IntermediateField.mem_fixedField_iff H x).mp hx g hgH)
  have hQw : Q.asIdeal.comap (algebraMap (𝓞 E) (𝓞 L)) = w.asIdeal :=
    (Ideal.over_def Q.asIdeal w.asIdeal).symm
  have hFrob := hg.restrictNormal E
  rw [hres, hQw] at hFrob
  have hwram : w.asIdeal.ramificationIdx (𝓞 K) = 1 :=
    ramificationIdx_below_eq_one w.asIdeal Q.asIdeal
      (FinitePlace.ramificationIdx_eq_one_of_ramifiedSet_subset hS Q hout)
  exact FinitePlace.finrank_eq_one_of_isFrobeniusAt_one v w hwram hFrob

/-- Frobenius elements away from the primes above $S$ generate the solvable Galois group,
provided $S$ contains all ramified base places. This is the stable-set form of Milne,
*Class Field Theory*, Chapter VII, Proposition 4.7. -/
theorem closure_frobenius_outside_eq_top (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : FinitePlace.ramifiedSet K L ⊆ S) :
    Subgroup.closure {g : L ≃ₐ[K] L | ∃ w : HeightOneSpectrum (𝓞 L),
      FinitePlace.below (K := K) w ∉ S ∧
        IsFrobeniusAt K L g (FinitePlace.below (K := K) w).asIdeal w.asIdeal} = ⊤ := by
  let H := Subgroup.closure (frobeniusOutside (K := K) (L := L) S)
  have : H.Normal := closure_isFrobeniusAt_normal (K := K) (H := L) (fun v => v ∉ S)
  let E := IntermediateField.fixedField H
  have : IsGalois K E := IsGalois.of_fixedField_normal_subgroup H
  have : Group.IsSolvable (E ≃ₐ[K] E) :=
    Group.isSolvable_of_surjective (IsGalois.normalAutEquivQuotient H).surjective
  have hdegree : Module.finrank K E = 1 :=
    finrank_eq_one_of_eventually_split (K := K) (L := E)
      (S.eventually_cofinite_notMem.mono fun v hv p =>
        fixedField_splits_outside S hS H Subgroup.subset_closure v hv p)
  have hE : E = ⊥ := IntermediateField.finrank_eq_one_iff.mp hdegree
  change H = ⊤
  rw [← IntermediateField.fixingSubgroup_fixedField H]
  change E.fixingSubgroup = ⊤
  rw [hE, IntermediateField.fixingSubgroup_bot]

end SIC
