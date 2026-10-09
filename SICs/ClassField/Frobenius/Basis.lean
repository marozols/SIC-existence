/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Frobenius.Generation
import SICs.ClassField.Completion.KummerDecomposition
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Frobenius bases in elementary abelian extensions

A finite basis of relative Frobenius elements at primes splitting in the intermediate field.

This follows Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII, Lemma 6.2.

## The argument

Away from the ramified primes, a decomposition group is cyclic. If the global group is killed
by a prime p, each such decomposition group has order one or p. A nontrivial relative
Frobenius therefore generates the full decomposition group; its restriction to the intermediate
field is trivial. Extract a basis from the relative Frobenius generators outside the excluded
set. Independence makes the projected base primes distinct, giving the source's set of primes
downstairs. We express a basis as an independent generating family, with its exact cardinality.
-/

noncomputable section

open IsDedekindDomain NumberField
open scoped NumberField SIC.FinitePlace Pointwise IsMulCommutative

namespace SIC

/-! ### From subgroup generation to a vector-space basis

For an abelian group killed by $p$, subgroup closure agrees with linear span over $\mathbf F_p$.
This lets Mathlib's basis extraction apply directly to the Frobenius generating set. -/

/-- Subgroup generation and $\mathbf F_p$-linear span agree for an abelian group killed by $p$;
used to extract the independent family in `nonempty_frobeniusBasis`. -/
private theorem span_ofMul_closure {G : Type*} [CommGroup G] (p : ℕ)
    [Module (ZMod p) (Additive G)] (s : Set G) :
    (Submodule.span (ZMod p) (Additive.ofMul '' s)).toAddSubgroup.toSubgroup =
      Subgroup.closure s := by
  apply le_antisymm
  · have hle : Submodule.span (ZMod p) (Additive.ofMul '' s) ≤
        (Subgroup.closure s).toAddSubgroup.toZModSubmodule p := by
      apply Submodule.span_le.mpr
      rintro x ⟨g, hg, rfl⟩
      change g ∈ Subgroup.closure s
      exact Subgroup.subset_closure hg
    intro g hg
    exact hle hg
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    change Additive.ofMul g ∈ Submodule.span (ZMod p) (Additive.ofMul '' s)
    exact Submodule.subset_span ⟨g, hg, rfl⟩

/-- A spanning set of a finite $\mathbf F_p$-module contains a basis, translated from
subgroup generation for `nonempty_frobeniusBasis`. -/
private theorem exists_basis_subset {G : Type*} [CommGroup G] (p : ℕ) [Fact p.Prime]
    [Module (ZMod p) (Additive G)] (A : Set G) (hA : Subgroup.closure A = ⊤) :
    ∃ b ⊆ Additive.ofMul '' A, Submodule.span (ZMod p) b = ⊤ ∧
      LinearIndependent (ZMod p) (fun x : b => x.val) := by
  have hspan : Submodule.span (ZMod p) (Additive.ofMul '' A) = ⊤ := by
    apply top_unique
    intro x _
    have hx : x.toMul ∈
        (Submodule.span (ZMod p) (Additive.ofMul '' A)).toAddSubgroup.toSubgroup := by
      rw [span_ofMul_closure p A, hA]
      trivial
    exact hx
  obtain ⟨b, hb, hsp, hli⟩ := exists_linearIndependent (ZMod p) (Additive.ofMul '' A)
  exact ⟨b, hb, hsp.trans hspan, hli⟩

/-- A vector-space basis gives group generators and the expected cardinality.
These are the basis properties consumed together by `nonempty_frobeniusBasis`. -/
private theorem basis_group_properties {G ι : Type*} [CommGroup G] [Finite G]
    [Fintype ι] (p : ℕ) [Fact p.Prime] [Module (ZMod p) (Additive G)]
    (B : Module.Basis ι (ZMod p) (Additive G)) :
    let g : ι → G := fun i => (B i).toMul
    Subgroup.closure (Set.range g) = ⊤ ∧ p ^ Fintype.card ι = Nat.card G := by
  let g : ι → G := fun i => (B i).toMul
  have hgimage : Additive.ofMul '' Set.range g = Set.range B := by
    simp only [← Set.range_comp, g, Function.comp_def, ofMul_toMul]
  refine ⟨?_, ?_⟩
  · rw [← span_ofMul_closure p (Set.range g), hgimage, B.span_eq]
    rfl
  · let : Fintype (Additive G) := Fintype.ofFinite _
    calc
      p ^ Fintype.card ι = Nat.card (Additive G) := by
        simpa only [Nat.card_eq_fintype_card, ZMod.card] using (Module.card_fintype B).symm
      _ = Nat.card G := Nat.card_congr Additive.toMul

variable {K M : Type*} [Field K] [Field M] [NumberField K] [NumberField M]
  [Algebra K M] [IsAbelianGalois K M]

/-! ### Relative Frobenius generators and splitting

Excluding all primes over $S$ leaves a generating family in the relative extension. A nontrivial
member is also absolute Frobenius by the prime-exponent tower calculation; its restriction to
$L$ is the identity, so the selected prime splits in $L/K$. -/

/-- Relative Frobenius elements outside the primes above $S$ generate. This applies
`closure_frobenius_outside_eq_top` to the relative extension in Milne, Chapter VII, Lemma 6.2. -/
private theorem relative_frobenius_generates (L : IntermediateField K M)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : FinitePlace.ramifiedSet K M ⊆ S) :
    Subgroup.closure {g : M ≃ₐ[L] M | ∃ w : HeightOneSpectrum (𝓞 M),
      FinitePlace.below (K := K) w ∉ S ∧
        IsFrobeniusAt L M g (FinitePlace.below (K := L) w).asIdeal w.asIdeal} = ⊤ := by
  have hram := FinitePlace.ramificationIdx_above_eq_one (L := L) S hS
  simpa only [FinitePlace.mem_placesAbove, FinitePlace.below_below] using
    closure_frobenius_outside_eq_top (K := L) (L := M) (FinitePlace.placesAbove S) hram

/-- Absolute Frobenius coming from a relative automorphism forces splitting in the
intermediate field, the local-degree conclusion in Milne, Chapter VII, Lemma 6.2. -/
private theorem split_of_relative_frobenius (L : IntermediateField K M)
    (w : HeightOneSpectrum (𝓞 M)) (g : M ≃ₐ[L] M)
    (h : IsFrobeniusAt K M (g.restrictScalars K) (FinitePlace.below (K := K) w).asIdeal w.asIdeal)
    (hram : w.asIdeal.ramificationIdx (𝓞 K) = 1) :
    Module.finrank ((FinitePlace.below (K := K) (FinitePlace.below (K := L) w)).adicCompletion K)
      ((FinitePlace.below (K := L) w).adicCompletion L) = 1 := by
  let v := FinitePlace.below (K := L) w
  have hres : (g.restrictScalars K).restrictNormal L = 1 := by
    apply (AlgEquiv.restrictNormal_eq_one_iff L _).mpr
    intro x hx
    exact g.commutes ⟨x, hx⟩
  have hf := h.restrictNormal L
  rw [hres] at hf
  apply FinitePlace.finrank_eq_one_of_isFrobeniusAt_one
  · exact ramificationIdx_below_eq_one v.asIdeal w.asIdeal hram
  · simpa only [FinitePlace.below, HeightOneSpectrum.under_asIdeal, Ideal.under_under,
      Ideal.under] using hf

/-- A basis of relative Frobenius elements whose distinct base primes lie outside $S$ and
split in $L/K$. This is the witness in Milne, *Class Field Theory*, Chapter VII, Lemma 6.2,
with the primes retained upstairs so their Frobenius congruences can be used directly. -/
structure FrobeniusBasis (p : ℕ) (L : IntermediateField K M)
    (S : Finset (HeightOneSpectrum (𝓞 K))) where
  /-- The selected primes of $M$. -/
  primes : Finset (HeightOneSpectrum (𝓞 M))
  /-- Their relative Frobenius automorphisms. -/
  frobenius : primes → (M ≃ₐ[L] M)
  /-- These Frobenius elements generate $\operatorname{Gal}(M/L)$. -/
  generates : Subgroup.closure (Set.range frobenius) = ⊤
  /-- The number of chosen primes is $t$, where $p^t=[M:L]$. -/
  card : p ^ primes.card = Module.finrank L M
  /-- Distinct chosen primes project to distinct primes of $K$. -/
  below_injective : Function.Injective (fun w : primes => FinitePlace.below (K := K) w.val)
  /-- The chosen base primes avoid $S$. -/
  outside : ∀ w : primes, FinitePlace.below (K := K) w.val ∉ S
  /-- Relative Frobenius agrees with absolute Frobenius. -/
  isFrobenius_base : ∀ w, IsFrobeniusAt K M ((frobenius w).restrictScalars K)
    (FinitePlace.below (K := K) w.val).asIdeal w.val.asIdeal
  /-- The completion of $L$ at each chosen prime equals the completion of $K$ below it. -/
  split : ∀ w : primes,
    Module.finrank
      ((FinitePlace.below (K := K) (FinitePlace.below (K := L) w.val)).adicCompletion K)
      ((FinitePlace.below (K := L) w.val).adicCompletion L) = 1

omit [IsAbelianGalois K M] in
/-- The set $T$ of base primes in Milne, *Class Field Theory*, Chapter VII, Lemma 6.2. -/
def FrobeniusBasis.basePrimes {p : ℕ} {L : IntermediateField K M}
    {S : Finset (HeightOneSpectrum (𝓞 K))} (B : FrobeniusBasis p L S) :
    Finset (HeightOneSpectrum (𝓞 K)) := by
  classical
  exact B.primes.image (FinitePlace.below (K := K))

omit [IsAbelianGalois K M] in
/-- A base prime is selected exactly when it lies under a selected prime upstairs. -/
theorem FrobeniusBasis.mem_basePrimes {p : ℕ} {L : IntermediateField K M}
    {S : Finset (HeightOneSpectrum (𝓞 K))} (B : FrobeniusBasis p L S)
    (v : HeightOneSpectrum (𝓞 K)) :
    v ∈ B.basePrimes ↔ ∃ w : B.primes, FinitePlace.below (K := K) w.val = v := by
  classical
  simp only [basePrimes, Finset.mem_image, Subtype.exists, exists_prop]

omit [IsAbelianGalois K M] in
/-- Projection preserves the number of selected primes. -/
theorem FrobeniusBasis.card_basePrimes {p : ℕ} {L : IntermediateField K M}
    {S : Finset (HeightOneSpectrum (𝓞 K))} (B : FrobeniusBasis p L S) :
    B.basePrimes.card = B.primes.card := by
  classical
  apply Finset.card_image_iff.mpr
  intro x hx y hy hxy
  exact congrArg Subtype.val (B.below_injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)

omit [IsAbelianGalois K M] in
/-- The source's two sets $T$ and $S$ are disjoint. -/
theorem FrobeniusBasis.disjoint_basePrimes {p : ℕ} {L : IntermediateField K M}
    {S : Finset (HeightOneSpectrum (𝓞 K))} (B : FrobeniusBasis p L S) :
    Disjoint B.basePrimes S := by
  apply Finset.disjoint_left.mpr
  intro v hv
  obtain ⟨w, rfl⟩ := (B.mem_basePrimes v).mp hv
  exact B.outside w

omit [IsAbelianGalois K M] in
/-- Every prime of $L$ above a selected base prime has local degree one.
Milne, *Class Field Theory*, Chapter VII, the note following Lemma 6.2; conjugacy of
completions transports the chosen splitting recorded by `FrobeniusBasis.split`. -/
theorem FrobeniusBasis.split_of_mem_basePrimes {p : ℕ} {L : IntermediateField K M}
    [IsGalois K L] {S : Finset (HeightOneSpectrum (𝓞 K))} (B : FrobeniusBasis p L S)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ B.basePrimes)
    (w : FinitePlace.PrimeAbove (L := L) v) :
    Module.finrank (v.adicCompletion K)
      ((FinitePlace.PrimeAbove.place v w).adicCompletion L) = 1 := by
  obtain ⟨u, hu⟩ := (B.mem_basePrimes v).mp hv
  have hbelow : FinitePlace.below (K := K) (FinitePlace.below (K := L) u.val) = v :=
    (FinitePlace.below_below (K := K) (L := L) u.val).trans hu
  clear hu
  subst v
  let w₀ := FinitePlace.below (K := L) u.val
  obtain ⟨σ, hσ⟩ := FinitePlace.exists_smul_eq (FinitePlace.below (K := K) w₀) w₀
    (FinitePlace.PrimeAbove.place _ w)
  rw [← (FinitePlace.completionAlgEquiv σ (FinitePlace.below (K := K) w₀) w₀
    (FinitePlace.PrimeAbove.place _ w) hσ).toLinearEquiv.finrank_eq]
  exact B.split u

/-! ### Selecting primes for a basis

Independence forces different basis vectors to have different base primes: Frobenius over a
fixed unramified base prime is unique in an abelian extension. Reindexing by the selected
primes gives the finite set in the source. -/

/-- Reindex an actual vector-space basis by its Frobenius primes, yielding the witness used
by `nonempty_frobeniusBasis`. -/
private theorem basis_of_frobenius (p : ℕ) [Fact p.Prime] (L : IntermediateField K M)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : FinitePlace.ramifiedSet K M ⊆ S)
    {ι : Type*} [Finite ι] [Module (ZMod p) (Additive (M ≃ₐ[L] M))]
    (B : Module.Basis ι (ZMod p) (Additive (M ≃ₐ[L] M)))
    (w : ι → HeightOneSpectrum (𝓞 M)) (hwout : ∀ i, FinitePlace.below (K := K) (w i) ∉ S)
    (hwabs : ∀ i, IsFrobeniusAt K M ((B i).toMul.restrictScalars K)
      (FinitePlace.below (K := K) (w i)).asIdeal (w i).asIdeal) :
    Nonempty (FrobeniusBasis p L S) := by
  classical
  let : Fintype ι := Fintype.ofFinite _
  have hinj : Function.Injective (fun i => FinitePlace.below (K := K) (w i)) := by
    intro i j hij
    change FinitePlace.below (K := K) (w i) = FinitePlace.below (K := K) (w j) at hij
    have hsame := (hwabs i).eq_of_same_base (by simpa only [hij] using hwabs j)
      (FinitePlace.ramificationIdx_eq_one_of_ramifiedSet_subset hS (w i) (hwout i))
    exact B.injective (AlgEquiv.restrictScalars_injective K hsame)
  let T := Finset.univ.image w
  let e : ι ≃ T := Equiv.ofBijective (fun i => ⟨w i, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩)
    ⟨fun i j h => hinj (congrArg (FinitePlace.below (K := K)) (congrArg Subtype.val h)), by
      rintro ⟨u, hu⟩
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
      exact ⟨i, rfl⟩⟩
  let g : T → (M ≃ₐ[L] M) := fun u => (B (e.symm u)).toMul
  have hprops := basis_group_properties p (B.reindex e)
  have heq : (fun u => ((B.reindex e) u).toMul) = g := by
    ext u
    simp only [Module.Basis.reindex_apply, g]
  rw [heq] at hprops
  refine ⟨⟨T, g, hprops.1, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simpa only [Fintype.card_coe, IsGalois.card_aut_eq_finrank] using hprops.2
  · intro u v huv
    apply e.symm.injective
    apply hinj
    have hu : w (e.symm u) = u.val := congrArg Subtype.val (e.apply_symm_apply u)
    have hv : w (e.symm v) = v.val := congrArg Subtype.val (e.apply_symm_apply v)
    simpa only [hu, hv] using huv
  · intro u
    exact congrArg Subtype.val (e.apply_symm_apply u) ▸ hwout (e.symm u)
  · intro u
    exact congrArg Subtype.val (e.apply_symm_apply u) ▸ hwabs (e.symm u)
  · intro u
    have he : w (e.symm u) = u.val := congrArg Subtype.val (e.apply_symm_apply u)
    exact split_of_relative_frobenius L u.val (g u) (he ▸ hwabs (e.symm u))
      (FinitePlace.ramificationIdx_eq_one_of_ramifiedSet_subset hS u.val
        (he ▸ hwout (e.symm u)))

/-- Relative Frobenius elements outside $S$ have a basis whose base primes split in $L/K$.
The chosen primes project injectively to the set $T$ downstairs in
Milne, *Class Field Theory*, Chapter VII, Lemma 6.2. -/
theorem nonempty_frobeniusBasis (p : ℕ) [Fact p.Prime]
    (hp : ∀ σ : M ≃ₐ[K] M, σ ^ p = 1) (L : IntermediateField K M)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : FinitePlace.ramifiedSet K M ⊆ S) :
    Nonempty (FrobeniusBasis p L S) := by
  classical
  let G := M ≃ₐ[L] M
  have hpow (g : G) : g ^ p = 1 := by
    apply AlgEquiv.restrictScalarsHom_injective K
    simpa only [map_pow, map_one, AlgEquiv.restrictScalarsHom_apply] using hp (g.restrictScalars K)
  let : Module (ZMod p) (Additive G) := AddCommGroup.zmodModule (n := p) (G := Additive G)
    (fun x => congrArg (Additive.ofMul : G → Additive G) (hpow x.toMul))
  let A : Set G := {g | ∃ w : HeightOneSpectrum (𝓞 M),
    FinitePlace.below (K := K) w ∉ S ∧
      IsFrobeniusAt L M g (FinitePlace.below (K := L) w).asIdeal w.asIdeal}
  have hA : Subgroup.closure A = ⊤ := relative_frobenius_generates L S hS
  obtain ⟨b, hb, hsp, hli⟩ := exists_basis_subset p A hA
  let B : Module.Basis b (ZMod p) (Additive G) := Module.Basis.mk hli (by simpa using hsp.ge)
  have hmem (i : b) : i.val.toMul ∈ A := by
    obtain ⟨g, hg, he⟩ := hb i.property
    simpa [← he] using hg
  choose w hwout hwrel using hmem
  have hwabs (i : b) : IsFrobeniusAt K M (i.val.toMul.restrictScalars K)
      (FinitePlace.below (K := K) (w i)).asIdeal (w i).asIdeal := by
    exact (hwrel i).restrictScalars_of_ne_one p hp L
      (FinitePlace.ramificationIdx_eq_one_of_ramifiedSet_subset hS (w i) (hwout i))
      (hli.ne_zero i)
  apply basis_of_frobenius p L S hS B w hwout
  simpa only [B, Module.Basis.mk_apply] using hwabs

/-! ### Powers detected by the selected primes

The Frobenius basis records both generation of the relative group and splitting in the
intermediate field; these are the two inputs to the local-to-global test. -/

/-- An element whose pth root lies in the upper field is a pth power in the intermediate
field exactly when it is a pth power at the selected base completions.
Milne, *Class Field Theory*, Chapter VII, Lemma 6.3. -/
theorem FrobeniusBasis.isPower_iff {p : ℕ} {L : IntermediateField K M}
    {S : Finset (HeightOneSpectrum (𝓞 K))} (B : FrobeniusBasis p L S)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hp : 0 < p) (a : K)
    (ha : ∃ x : M, x ^ p = algebraMap K M a) :
    (∃ x : L, x ^ p = algebraMap K L a) ↔
      ∀ v ∈ B.basePrimes, ∃ x : v.adicCompletion K,
        x ^ p = algebraMap K (v.adicCompletion K) a := by
  constructor
  · intro h v hv
    obtain ⟨w, rfl⟩ := (B.mem_basePrimes v).mp hv
    have hroot := FinitePlace.exists_root_of_finrank_eq_one
      (FinitePlace.below (K := K) (FinitePlace.below (K := L) w.val))
      (FinitePlace.below (K := L) w.val) (B.split w) h
    exact (FinitePlace.below_below (K := K) (L := L) w.val) ▸ hroot
  · intro h
    obtain ⟨x, hx⟩ := ha
    have hfix : Subgroup.closure (Set.range B.frobenius) ≤
        MulAction.stabilizer (M ≃ₐ[L] M) x := by
      apply (Subgroup.closure_le _).mpr
      rintro g ⟨w, rfl⟩
      exact FinitePlace.frobenius_fixes_root (FinitePlace.below (K := K) w.val) w.val hζ hp
        (B.isFrobenius_base w) hx (h _ ((B.mem_basePrimes _).mpr ⟨w, rfl⟩))
    rw [B.generates] at hfix
    obtain ⟨y, hy⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := L) x).mpr
      (fun g => hfix (Subgroup.mem_top g))
    refine ⟨y, ?_⟩
    apply (algebraMap L M).injective
    rw [map_pow, hy, hx]
    exact IsScalarTower.algebraMap_apply K L M a

end SIC
