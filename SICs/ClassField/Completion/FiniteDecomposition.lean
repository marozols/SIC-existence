/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.FieldTheory.PermutedAlgebraFamily
import SICs.ClassField.Completion.FiniteBaseChange
import SICs.ClassField.Completion.FiniteConjugation
import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# Decomposition groups at finite places

The decomposition group $D_w \subseteq \operatorname{Gal}(L/K)$ of a finite place `w` of `L` above
a finite place `v` of `K` acts on the completion $L_w$ by $K_v$-automorphisms. For Galois `L/K`
the action is an isomorphism $D_w \cong \operatorname{Gal}(L_w/K_v)$, the extension $L_w/K_v$ is
Galois of degree $|D_w|$, its fixed field is $K_v$, and the automorphisms carrying one prime `w'`
above `v` to `w` multiply to the local norm at `w'`.

This is Serre, *Local Fields*, Chapter II, §3, Corollary 4, and the decomposition-group
discussion of Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII, §2, before
Lemma 2.1, at a finite place.

## The argument

`completionFamily` bundles the $K_v$-algebra transports between completions above `v`. The
generic `PermutedAlgebraFamily` argument shows that the stabilizer acts faithfully on each
completion. For Galois `L/K`, Mathlib gives transitivity on primes above `v`, and the local
degrees add to $[L:K]$ (`sum_finrank_primeAbove`). Orbit-stabilizer makes each degree $|D_w|$.
Mathlib's order formula then gives $|D_w|=ef$. The general family lemmas identify the stabilizer
with the local Galois group and give descent. `PrimeAbove.stabilizer_mk`
identifies this bundled action with the public action at an underlying finite place.

The generic coset-product lemma gives the product of the transports from `w'` to `w`; reindexing
the bundled primes by their underlying places gives the public completion formula.
-/

noncomputable section

open IsDedekindDomain NumberField
open scoped SIC.FinitePlace Pointwise

namespace SIC

namespace FinitePlace

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

/-! ### The decomposition group acting on the completion -/

/-- The completions above `v`, with transport by Galois automorphisms. -/
def completionFamily : PermutedAlgebraFamily K (v.adicCompletion K) L
    (PrimeAbove (L := L) v) (fun i => (PrimeAbove.place v i).adicCompletion L) where
  map σ i j h := completionAlgEquiv σ v (PrimeAbove.place v i) (PrimeAbove.place v j)
    (PrimeAbove.mapEquiv_place_eq_of_smul_eq v σ i j h)
  map_one := by
    intro i
    apply AlgEquiv.ext
    intro x
    change completionEquiv (RingEquiv.refl L) (PrimeAbove.place v i)
      (PrimeAbove.place v i) (mapEquiv_refl _) x = x
    rw [completionEquiv_refl]
    rfl
  map_mul := by
    intro σ τ i j l hij hjl
    apply AlgEquiv.ext
    intro x
    exact completionEquiv_mul σ τ
      (PrimeAbove.mapEquiv_place_eq_of_smul_eq v τ i j hij)
      (PrimeAbove.mapEquiv_place_eq_of_smul_eq v σ j l hjl) x
  map_algebraMap := by
    intro σ i j h x
    exact completionEquiv_algebraMap σ.toRingEquiv (PrimeAbove.place v i)
      (PrimeAbove.place v j) (PrimeAbove.mapEquiv_place_eq_of_smul_eq v σ i j h) x

omit [NumberField K] [NumberField L] in
/-- The stabilizer of a bundled prime is that of its underlying finite place. -/
theorem PrimeAbove.stabilizer_eq (i : PrimeAbove (L := L) v) :
    MulAction.stabilizer (L ≃ₐ[K] L) i =
      MulAction.stabilizer (L ≃ₐ[K] L) (PrimeAbove.place v i) := by
  ext σ
  simp only [MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    simpa only [PrimeAbove.place_smul] using congrArg (PrimeAbove.place v) h
  · intro h
    apply PrimeAbove.place_injective v
    simpa only [PrimeAbove.place_smul] using h

omit [NumberField K] [NumberField L] in
/-- The stabilizer of `PrimeAbove.mk v w` is the decomposition group of `w`. -/
theorem PrimeAbove.stabilizer_mk :
    MulAction.stabilizer (L ≃ₐ[K] L) (PrimeAbove.mk v w) =
      MulAction.stabilizer (L ≃ₐ[K] L) w := by
  simpa only [PrimeAbove.place_mk] using
    (PrimeAbove.stabilizer_eq v (PrimeAbove.mk v w))

/-- The action of the decomposition group $D_w$ on $L_w$, obtained from the stabilizer action
of `completionFamily`. Milne, *Class Field Theory*, Chapter VII, §2. -/
def decompositionHom :
    MulAction.stabilizer (L ≃ₐ[K] L) w →*
      (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) :=
  ((completionFamily (L := L) v).fiber (PrimeAbove.mk v w)).comp
    (MulEquiv.subgroupCongr (PrimeAbove.stabilizer_mk v w).symm).toMonoidHom

/-- The extension of `σ ∈ D_w` to $L_w$ is `σ` on `L`. -/
@[simp]
theorem decompositionHom_algebraMap (σ : MulAction.stabilizer (L ≃ₐ[K] L) w) (x : L) :
    decompositionHom v w σ (algebraMap L (w.adicCompletion L) x) =
      algebraMap L (w.adicCompletion L) ((σ : L ≃ₐ[K] L) x) := by
  exact (completionFamily (L := L) v).fiber_algebraMap (PrimeAbove.mk v w)
    ((MulEquiv.subgroupCongr (PrimeAbove.stabilizer_mk v w).symm) σ) x

/-! ### Galois extensions -/

variable [IsGalois K L]

/-- The Galois group acts transitively on the primes above `v`. Milne, *Class Field Theory*,
Chapter VII, §2; [83, Neukirch (1999), Chapter I, Proposition 9.1]. -/
@[source "83, Chapter I, Proposition 9.1, p. 54"]
theorem exists_smul_eq (w' : HeightOneSpectrum (𝓞 L)) [w'.asIdeal.LiesOver v.asIdeal] :
    ∃ σ : L ≃ₐ[K] L, σ • w = w' := by
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal w.asIdeal w'.asIdeal
    (L ≃ₐ[K] L)
  exact ⟨σ, HeightOneSpectrum.ext (by rw [SIC.FinitePlace.asIdeal_smul, hσ])⟩

/-- Transitivity of the Galois action on bundled primes above `v`. -/
theorem PrimeAbove.exists_smul_eq
    (i j : PrimeAbove (L := L) v) : ∃ σ : L ≃ₐ[K] L, σ • i = j := by
  obtain ⟨σ, hσ⟩ := SIC.FinitePlace.exists_smul_eq v (PrimeAbove.place v i)
    (PrimeAbove.place v j)
  exact ⟨σ, (PrimeAbove.place_injective v) (by
    simpa only [PrimeAbove.place_smul] using hσ)⟩

/-- The local degree is the order of the decomposition group: $[L_w : K_v] = |D_w|$. Serre,
*Local Fields*, Chapter II, §3, Corollary 4. -/
theorem finrank_eq_card_stabilizer :
    Module.finrank (v.adicCompletion K) (w.adicCompletion L) =
      Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) w) := by
  have h := (completionFamily (L := L) v).finrank_eq_card_stabilizer
    (PrimeAbove.exists_smul_eq v) (sum_finrank_primeAbove v) (PrimeAbove.mk v w)
  convert h using 1
  · rfl
  · rw [PrimeAbove.stabilizer_eq]
    rfl

/-- The local degree divides the global degree: $[L_w:K_v]\mid[L:K]$ for Galois `L/K`. -/
theorem finrank_dvd_finrank :
    Module.finrank (v.adicCompletion K) (w.adicCompletion L) ∣ Module.finrank K L := by
  have h := (completionFamily (L := L) v).finrank_dvd_finrank
    (PrimeAbove.exists_smul_eq v) (sum_finrank_primeAbove v) (PrimeAbove.mk v w)
  convert h using 1
  rfl

/-- The local degree is the product of the ramification index and the inertia degree:
$[L_w:K_v]=e(w/v)f(w/v)$ for Galois `L/K`. Serre, *Local Fields*, Chapter II, §3,
Corollary 4, with the order $|D_w|=ef$ of Chapter I, §7. -/
theorem finrank_eq_ramificationIdx_mul_inertiaDeg :
    Module.finrank (v.adicCompletion K) (w.adicCompletion L) =
      w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) := by
  have : v.asIdeal.IsMaximal := Ideal.isMaximal_of_isPrime_of_ne_bot _ v.ne_bot
  have : Finite ((𝓞 K) ⧸ v.asIdeal) := inferInstance
  have : Finite v.asIdeal.ResidueField := inferInstance
  have : PerfectField v.asIdeal.ResidueField := PerfectField.ofFinite
  calc
    Module.finrank (v.adicCompletion K) (w.adicCompletion L) =
        Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) w) :=
      finrank_eq_card_stabilizer v w
    _ = Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) := by
      rw [stabilizer_eq_stabilizer_asIdeal (K := K) w]
    _ = v.asIdeal.ramificationIdxIn (𝓞 L) * v.asIdeal.inertiaDegIn (𝓞 L) :=
      Ideal.card_stabilizer_eq (G := L ≃ₐ[K] L) v.asIdeal w.asIdeal
    _ = w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) := by
      rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal (L ≃ₐ[K] L),
        Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal w.asIdeal (L ≃ₐ[K] L)]

/-- For Galois `L/K`, the action of $D_w$ on $L_w$ is bijective. -/
theorem decompositionHom_bijective : Function.Bijective (decompositionHom v w) :=
  ((completionFamily (L := L) v).fiber_bijective
    (PrimeAbove.exists_smul_eq v) (sum_finrank_primeAbove v) (PrimeAbove.mk v w)).comp
      (MulEquiv.subgroupCongr (PrimeAbove.stabilizer_mk v w).symm).bijective

/-- The decomposition group is the Galois group of the completion:
$D_w \cong \operatorname{Gal}(L_w/K_v)$. Serre, *Local Fields*, Chapter II, §3, Corollary 4. -/
def decompositionEquiv :
    MulAction.stabilizer (L ≃ₐ[K] L) w ≃*
      (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) :=
  (MulEquiv.subgroupCongr (PrimeAbove.stabilizer_mk v w).symm).trans
    ((completionFamily (L := L) v).decompositionEquiv
      (PrimeAbove.exists_smul_eq v) (sum_finrank_primeAbove v) (PrimeAbove.mk v w))

/-- The completion of a Galois extension is Galois: $L_w/K_v$ is Galois. Serre, *Local Fields*,
Chapter II, §3, Corollary 4. -/
instance isGalois_adicCompletion : IsGalois (v.adicCompletion K) (w.adicCompletion L) :=
  (completionFamily (L := L) v).isGalois
    (PrimeAbove.exists_smul_eq v) (sum_finrank_primeAbove v) (PrimeAbove.mk v w)

/-- The automorphisms of $L_w/K_v$ preserve the valuation: $w(\sigma x) = w(x)$. Each is the
extension of an element of $D_w$ (`decompositionHom_bijective`), and those preserve valuations. -/
theorem valued_algEquiv_apply
    (σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
    (x : w.adicCompletion L) : Valued.v (σ x) = Valued.v x := by
  obtain ⟨τ, rfl⟩ := (decompositionHom_bijective v w).2 σ
  exact valued_completionEquiv (τ : L ≃ₐ[K] L).toRingEquiv w w
    (MulAction.mem_stabilizer_iff.mp τ.2) x

/-- Galois descent for the completion: the elements of $L_w$ fixed by $D_w$ are those of $K_v$. -/
theorem mem_range_completionMap_iff (x : w.adicCompletion L) :
    x ∈ (completionMap v w).range ↔
      ∀ σ : MulAction.stabilizer (L ≃ₐ[K] L) w, decompositionHom v w σ x = x :=
  by
    exact (completionFamily (L := L) v).mem_range_algebraMap_iff_reindex
      (PrimeAbove.exists_smul_eq v) (sum_finrank_primeAbove v) (PrimeAbove.mk v w)
      (MulEquiv.subgroupCongr (PrimeAbove.stabilizer_mk v w).symm) x

/-- For primes `w'` and `w` above `v`, the automorphisms carrying `w'` to `w` multiply to the local
norm: $\prod_{\sigma w' = w} \sigma y = N_{L_{w'}/K_v}(y)$ for $y \in L_{w'}$. Milne,
*Class Field Theory*, Chapter VII, §2, "The norm map on idèles". -/
theorem prod_completionEquiv_eq_completionMap_norm (w' : HeightOneSpectrum (𝓞 L))
    [w'.asIdeal.LiesOver v.asIdeal] [Fintype {σ : L ≃ₐ[K] L // σ • w' = w}]
    (y : w'.adicCompletion L) :
    ∏ σ : {σ : L ≃ₐ[K] L // σ • w' = w},
        completionEquiv (σ : L ≃ₐ[K] L).toRingEquiv w' w σ.2 y =
      completionMap v w (Algebra.norm (v.adicCompletion K) y) := by
  let _ : Fintype {σ : L ≃ₐ[K] L // σ • PrimeAbove.mk v w' = PrimeAbove.mk v w} :=
    Fintype.ofFinite _
  let e : {σ : L ≃ₐ[K] L // σ • w' = w} ≃
      {σ : L ≃ₐ[K] L // σ • PrimeAbove.mk v w' = PrimeAbove.mk v w} :=
    Equiv.subtypeEquivRight (fun σ => by
      constructor
      · intro h
        apply PrimeAbove.place_injective v
        simpa only [PrimeAbove.place_smul, PrimeAbove.place_mk] using h
      · intro h
        have hh := congrArg (PrimeAbove.place v) h
        simpa only [PrimeAbove.place_smul, PrimeAbove.place_mk] using hh)
  have hreindex :
      (∏ σ : {σ : L ≃ₐ[K] L // σ • w' = w},
        completionEquiv (σ : L ≃ₐ[K] L).toRingEquiv w' w σ.2 y) =
      (∏ σ : {σ : L ≃ₐ[K] L // σ • PrimeAbove.mk v w' = PrimeAbove.mk v w},
        (completionFamily (L := L) v).map σ (PrimeAbove.mk v w') (PrimeAbove.mk v w)
          σ.2 y) := by
    apply Fintype.prod_equiv e _ _
    intro σ
    rfl
  have hprod := (completionFamily (L := L) v).prod_map_eq_algebraMap_norm
    (PrimeAbove.exists_smul_eq v) (sum_finrank_primeAbove v)
    (PrimeAbove.mk v w') (PrimeAbove.mk v w) y
  exact hreindex.trans hprod

/-! ### Bundled primes above a fixed place

The decomposition-group identification at a bundled prime is the family's fiber equivalence.
-/

/-- The decomposition group at a prime above `v` is the local Galois group. -/
def PrimeAbove.decompositionEquiv (w : PrimeAbove (L := L) v) :
    MulAction.stabilizer (L ≃ₐ[K] L) w ≃*
      ((PrimeAbove.place v w).adicCompletion L ≃ₐ[v.adicCompletion K]
        (PrimeAbove.place v w).adicCompletion L) :=
  (completionFamily (L := L) v).decompositionEquiv
    (PrimeAbove.exists_smul_eq v) (sum_finrank_primeAbove v) w

/-- Cyclicity descends from the global Galois group to the completion at a place above `v`. -/
instance PrimeAbove.isCyclic [IsCyclic (L ≃ₐ[K] L)]
    (w : PrimeAbove (L := L) v) :
    IsCyclic ((PrimeAbove.place v w).adicCompletion L ≃ₐ[v.adicCompletion K]
      (PrimeAbove.place v w).adicCompletion L) :=
  isCyclic_of_surjective (PrimeAbove.decompositionEquiv v w).toMonoidHom
    (PrimeAbove.decompositionEquiv v w).surjective

end FinitePlace

end SIC
