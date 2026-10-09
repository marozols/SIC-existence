/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Frobenius.Generation
import SICs.ClassField.Ideles.IdealNorm

/-!
# The ideal Artin map

Frobenius elements at the base primes of a finite abelian extension, the ideal Artin map away
from a finite set of primes, its surjectivity on the ideals prime to that set, and its behavior
under restriction to subextensions and under norms from intermediate fields. Its Artin symbol
fixes an intermediate field exactly when the Artin symbol there is trivial.

For a finite abelian extension `L/K` and a finite set `S` of primes of `K` containing those that
ramify in `L`, the Artin map $\psi^S_{L/K} : I^S_K \to \operatorname{Gal}(L/K)$ sends a prime
$\mathfrak p \notin S$ to its Frobenius element: Milne, *Class Field Theory*, version 4.03
(2020), Chapter V, §3, "The Artin map"; Childress, *Class Field Theory* (2009), Chapter V, §1.
Here it is defined on all nonzero fractional ideals and ignores the primes of `S`; on the
fractional ideals prime to `S` it is the source's map.

## The argument

Mathlib's `arithFrobAt` chooses conjugate Frobenius elements at the primes above one base
prime. Conjugate elements of an abelian group are equal, so `frobeniusAt L v` is an arithmetic
Frobenius element at every prime above `v`. At an unramified prime it is the only one, since two
Frobenius elements at one prime differ by an element of its inertia group. The Artin map is the
finite product of the powers $\operatorname{Frob}_v^{\operatorname{ord}_v J}$ over `v ∉ S`; it
is a homomorphism because orders add.

*Surjectivity.* The Frobenius elements at the primes outside `S` generate the Galois group
(`closure_frobeniusAt_eq_top`), and each is the image of its base prime, which lies in the group
$I^S$ of ideals prime to `S`. On $I^S$ the Artin map does not change when `S` is enlarged.

*Restriction.* Frobenius at a prime `Q` restricts to Frobenius at `Q ∩ E` on a normal
subextension `E` (`IsFrobeniusAt.restrictNormal`; Milne, Chapter V, 1.11), so at a prime
unramified in `L` the Frobenius element of `L/K` restricts to that of `E/K`, and restriction of
$\psi^S_{L/K}$ to `E` is $\psi^S_{E/K}$ (Childress, Chapter V, Corollary 1.2). The subextension
may be any field in a tower `K ⊆ E ⊆ L`, not only an intermediate field.

*Norms.* Let $\mathfrak P$ be a prime of an intermediate field `E` above
$\mathfrak p \notin S$, with residue degree `f`. Since $N\mathfrak P = N\mathfrak p^f$, the
element $\operatorname{Frob}_{\mathfrak p}(L/K)^f$ fixes `E` and satisfies the Frobenius
congruence of $\mathfrak P$ for `L/E` (Milne, Chapter V, 1.10). With
$N_{E/K}\mathfrak P = \mathfrak p^f$ this gives the tower law
$\psi_{L/E} = \psi_{L/K} \circ N_{E/K}$ (Milne, Chapter V, Proposition 3.3; Childress,
Chapter V, Corollary 1.3). At an unramified prime of `L`, Frobenius has order equal to the
residue degree, so its residue-degree power is `1`. The prime norm formula then shows directly
that norms from `L` lie in the kernel (Milne, Chapter V, Corollary 3.4; Childress, Chapter V,
Corollary 1.4).
-/

noncomputable section

open IsDedekindDomain NumberField
open scoped nonZeroDivisors IsMulCommutative

namespace SIC

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  [IsAbelianGalois K L]

/-! ### Frobenius elements at base primes

The conjugate choice of Mathlib's `arithFrobAt` makes one Frobenius element serve every prime
above a base prime of an abelian extension. -/

variable (L) in
/-- The Frobenius element of `L/K` at a finite place `v` of `K`: Mathlib's `arithFrobAt` at a
chosen prime of `L` above `v`. Milne, *Class Field Theory*, Chapter V, §3, "The Artin map". -/
def frobeniusAt (v : HeightOneSpectrum (𝓞 K)) : L ≃ₐ[K] L :=
  arithFrobAt (𝓞 K) (L ≃ₐ[K] L)
    (FinitePlace.PrimeAbove.place (L := L) v (Classical.arbitrary _)).asIdeal

/-- In an abelian extension, `frobeniusAt L v` is a Frobenius element at every prime above `v`.
Milne, *Class Field Theory*, Chapter V, 1.9 and the remark following it. -/
theorem isFrobeniusAt_frobeniusAt (v : HeightOneSpectrum (𝓞 K)) (Q : Ideal (𝓞 L))
    [Q.IsPrime] [Q.LiesOver v.asIdeal] :
    IsFrobeniusAt K L (frobeniusAt L v) v.asIdeal Q := by
  let Q₀ := (FinitePlace.PrimeAbove.place (L := L) v (Classical.arbitrary _)).asIdeal
  have hQ : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  have : Q.IsMaximal := Ideal.isMaximal_of_isPrime_of_ne_bot Q hQ
  have : Finite ((𝓞 L) ⧸ Q) := inferInstance
  have hunder : Q₀.under (𝓞 K) = Q.under (𝓞 K) := by
    rw [← Ideal.over_def Q₀ v.asIdeal, ← Ideal.over_def Q v.asIdeal]
  have heq : arithFrobAt (𝓞 K) (L ≃ₐ[K] L) Q₀ =
      arithFrobAt (𝓞 K) (L ≃ₐ[K] L) Q :=
    isConj_iff_eq.mp (isConj_arithFrobAt (𝓞 K) (L ≃ₐ[K] L) Q₀ Q hunder)
  rw [frobeniusAt, heq]
  exact isFrobeniusAt_iff_isArithFrobAt.mpr
    (IsArithFrobAt.arithFrobAt (𝓞 K) (L ≃ₐ[K] L) Q)

/-- At an unramified prime every Frobenius element is `frobeniusAt L v`. Milne, *Class Field
Theory*, Chapter V, §3, "The Artin map". -/
theorem IsFrobeniusAt.eq_frobeniusAt {v : HeightOneSpectrum (𝓞 K)} {g : L ≃ₐ[K] L}
    {Q : Ideal (𝓞 L)} (hg : IsFrobeniusAt K L g v.asIdeal Q)
    (hunr : Q.ramificationIdx (𝓞 K) = 1) : g = frobeniusAt L v := by
  have : Q.IsPrime := hg.1
  have : Q.LiesOver v.asIdeal := ⟨hg.2.1.symm⟩
  exact hg.eq_of_ramificationIdx_eq_one (isFrobeniusAt_frobeniusAt v Q) hunr

/-! ### The Artin map away from a finite set

The Frobenius power of each prime outside `S`, raised to its order in the fractional ideal, is
trivial for almost every prime; their finite product is multiplicative in the ideal. -/

variable (L) in
/-- **The ideal Artin map away from `S`**: $J \mapsto \prod_{v \notin S}
\operatorname{Frob}_v^{\operatorname{ord}_v J}$. On the fractional ideals prime to `S`, for `S`
containing the primes ramified in `L`, this is $\psi^S_{L/K}$ of Milne, *Class Field Theory*,
Chapter V, §3, "The Artin map", and the Artin map `A` of Childress, *Class Field Theory*,
Chapter V, §1. -/
def artinMap (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ →* (L ≃ₐ[K] L) :=
  FractionalIdeal.liftPrimes K S (frobeniusAt L)

/-- The Artin map sends a prime outside `S` to its Frobenius element. -/
@[simp]
theorem artinMap_primeFractionalIdeal_of_notMem {S : Finset (HeightOneSpectrum (𝓞 K))}
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) :
    artinMap L S (primeFractionalIdeal K v) = frobeniusAt L v := by
  exact FractionalIdeal.liftPrimes_primeFractionalIdeal_of_notMem S (frobeniusAt L) hv

/-- The Artin map ignores the primes of `S`. -/
@[simp]
theorem artinMap_primeFractionalIdeal_of_mem {S : Finset (HeightOneSpectrum (𝓞 K))}
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ S) :
    artinMap L S (primeFractionalIdeal K v) = 1 := by
  exact FractionalIdeal.liftPrimes_primeFractionalIdeal_of_mem S (frobeniusAt L) hv

/-- The Frobenius elements `frobeniusAt L v` outside a finite set containing all ramified
primes generate the Galois group. This is `closure_frobenius_outside_eq_top` expressed using
the chosen Frobenius at each base prime. -/
theorem closure_frobeniusAt_eq_top (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : FinitePlace.ramifiedSet K L ⊆ S) :
    Subgroup.closure {g : L ≃ₐ[K] L | ∃ v ∉ S, frobeniusAt L v = g} = ⊤ := by
  have hgen := closure_frobenius_outside_eq_top (K := K) (L := L) S hS
  apply eq_top_iff.mpr
  rw [← hgen, Subgroup.closure_le]
  rintro g ⟨w, hw, hgw⟩
  apply Subgroup.subset_closure
  exact ⟨FinitePlace.below (K := K) w, hw,
    (hgw.eq_frobeniusAt
      (FinitePlace.ramificationIdx_eq_one_of_ramifiedSet_subset hS w hw)).symm⟩

/-- **The Artin map is surjective on the ideals prime to `S`** when `S` contains the ramified
primes. Childress, *Class Field Theory*, Chapter V, Theorem 2.1(i), on $I_K(\mathfrak m)$;
Milne, *Class Field Theory*, Chapter VII, Corollary 4.8. -/
theorem exists_mem_primeTo_artinMap_eq (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : FinitePlace.ramifiedSet K L ⊆ S)
    (g : L ≃ₐ[K] L) :
    ∃ J ∈ FractionalIdeal.primeTo K S, artinMap L S J = g := by
  let A : FractionalIdeal.primeTo K S →* (L ≃ₐ[K] L) :=
    (artinMap L S).comp (FractionalIdeal.primeTo K S).subtype
  have hgen := closure_frobeniusAt_eq_top (L := L) S hS
  have hsub : {g : L ≃ₐ[K] L | ∃ v ∉ S, frobeniusAt L v = g} ⊆ A.range := by
    rintro g ⟨v, hv, rfl⟩
    exact ⟨⟨primeFractionalIdeal K v, primeFractionalIdeal_mem_primeTo hv⟩,
      artinMap_primeFractionalIdeal_of_notMem hv⟩
  have hsurj : Function.Surjective A := by
    apply MonoidHom.range_eq_top.mp
    apply eq_top_iff.mpr
    rw [← hgen, Subgroup.closure_le]
    exact hsub
  obtain ⟨⟨J, hJ⟩, hAJ⟩ := hsurj g
  exact ⟨J, hJ, hAJ⟩

/-- Enlarging the excluded set does not change the Artin map of an ideal prime to the larger
set: $\psi^S(J) = \psi^{S'}(J)$ for $S\subseteq S'$ and $J\in I^{S'}$. -/
theorem artinMap_eq_of_mem_primeTo {S S' : Finset (HeightOneSpectrum (𝓞 K))} (hSS' : S ⊆ S')
    {J : (FractionalIdeal (𝓞 K)⁰ K)ˣ} (hJ : J ∈ FractionalIdeal.primeTo K S') :
    artinMap L S J = artinMap L S' J := by
  exact FractionalIdeal.liftPrimes_eq_of_mem_primeTo hSS' (frobeniusAt L) hJ

/-! ### Restriction and norms

Restriction to a subextension and the norm from an intermediate field are compatible with the
Artin maps on primes outside `S`, hence on all fractional ideals. -/

/-- **Frobenius restricts to Frobenius**: for an abelian subextension `E` of `L/K` and a prime
`v` unramified in `L`, $\operatorname{Frob}_v(L/K)|_E = \operatorname{Frob}_v(E/K)$. Milne,
*Class Field Theory*, Chapter V, 1.11. -/
theorem frobeniusAt_restrictNormal (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), FinitePlace.below (K := K) w = v →
      w.asIdeal.ramificationIdx (𝓞 K) = 1)
    (E : Type*) [Field E] [NumberField E] [Algebra K E] [Algebra E L] [IsScalarTower K E L]
    [IsAbelianGalois K E] :
    (frobeniusAt L v).restrictNormal E = frobeniusAt E v := by
  let w := FinitePlace.PrimeAbove.place (L := L) v (Classical.arbitrary _)
  have hw : FinitePlace.below (K := K) w = v :=
    FinitePlace.PrimeAbove.below_place v (Classical.arbitrary _)
  let P := w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 L))
  have hP : IsFrobeniusAt K E ((frobeniusAt L v).restrictNormal E) v.asIdeal P :=
    (isFrobeniusAt_frobeniusAt v w.asIdeal).restrictNormal E
  have hPram : P.ramificationIdx (𝓞 K) = 1 :=
    ramificationIdx_below_eq_one P w.asIdeal (hv w hw)
  exact hP.eq_frobeniusAt hPram

/-- **Restriction**: $\psi^S_{L/K}(J)|_E = \psi^S_{E/K}(J)$ for an abelian subextension `E`,
given as a field in a tower `K ⊆ E ⊆ L`. Childress, *Class Field Theory*, Chapter V,
Corollary 1.2; Milne, *Class Field Theory*, Chapter V, 1.11. -/
theorem artinMap_restrictNormal (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : FinitePlace.ramifiedSet K L ⊆ S)
    (E : Type*) [Field E] [NumberField E] [Algebra K E] [Algebra E L] [IsScalarTower K E L]
    [IsAbelianGalois K E] (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (artinMap L S J).restrictNormal E = artinMap E S J := by
  have hhom : (AlgEquiv.restrictNormalHom E).comp (artinMap L S) = artinMap E S := by
    apply FractionalIdeal.monoidHom_ext
    intro v
    change (artinMap L S (primeFractionalIdeal K v)).restrictNormal E =
      artinMap E S (primeFractionalIdeal K v)
    by_cases hv : v ∈ S
    · simp only [artinMap_primeFractionalIdeal_of_mem hv]
      exact (AlgEquiv.restrictNormalHom E).map_one
    · rw [artinMap_primeFractionalIdeal_of_notMem hv,
        artinMap_primeFractionalIdeal_of_notMem hv]
      exact frobeniusAt_restrictNormal v (fun w hw ↦
        FinitePlace.ramificationIdx_eq_one_of_ramifiedSet_subset hS w (hw ▸ hv)) E
  exact congrArg (fun f : (FractionalIdeal (𝓞 K)⁰ K)ˣ →* (E ≃ₐ[K] E) => f J) hhom

/-- The Artin symbol of an intermediate field `E` is trivial exactly when that of `L` fixes `E`:
$\psi^S_{E/K}(J) = 1\iff\psi^S_{L/K}(J)\in\operatorname{Gal}(L/E)$. -/
theorem artinMap_eq_one_iff_mem_fixingSubgroup (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : FinitePlace.ramifiedSet K L ⊆ S)
    (E : IntermediateField K L) (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    artinMap E S J = 1 ↔ artinMap L S J ∈ E.fixingSubgroup := by
  rw [← artinMap_restrictNormal S hS E J,
    AlgEquiv.restrictNormal_eq_one_iff, IntermediateField.mem_fixingSubgroup_iff]

/-- In an unramified Galois tower, the Frobenius at `w` restricts to the residue-degree power
of Frobenius at the place below `w`. This is the prime case of `artinMap_restrictScalars`. -/
private theorem frobeniusAt_pow_restrictScalars (E : IntermediateField K L)
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver v.asIdeal] (u : HeightOneSpectrum (𝓞 L))
    [u.asIdeal.LiesOver w.asIdeal] (hunr : u.asIdeal.ramificationIdx (𝓞 K) = 1) :
    frobeniusAt L v ^ w.asIdeal.inertiaDeg (𝓞 K) =
      (frobeniusAt L w).restrictScalars K := by
  have : u.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.trans u.asIdeal w.asIdeal v.asIdeal
  have hFrob := isFrobeniusAt_frobeniusAt v u.asIdeal
  have hP : u.asIdeal.comap (algebraMap (𝓞 E) (𝓞 L)) = w.asIdeal :=
    (Ideal.over_def u.asIdeal w.asIdeal).symm
  have hwram : w.asIdeal.ramificationIdx (𝓞 K) = 1 :=
    ramificationIdx_below_eq_one w.asIdeal u.asIdeal hunr
  obtain ⟨τ, hτ, hτFrob⟩ := hFrob.exists_pow_restrictScalars E (by simpa only [hP] using hwram)
  have hτFrob' : IsFrobeniusAt E L τ w.asIdeal u.asIdeal := by
    simpa only [Ideal.under, hP] using hτFrob
  have huram : u.asIdeal.ramificationIdx (𝓞 E) = 1 :=
    ramificationIdx_above_eq_one w.asIdeal u.asIdeal hunr
  simpa only [Ideal.under, hP] using hτ.symm.trans
    (congrArg (fun σ : L ≃ₐ[E] L => σ.restrictScalars K)
      (hτFrob'.eq_frobeniusAt huram))

/-- **The tower law** $\psi_{L/E} = \psi_{L/K} \circ N_{E/K}$ for an intermediate field `E`,
with the primes of `E` above `S` removed on the left. Milne, *Class Field Theory*,
Chapter V, Proposition 3.3; Childress, *Class Field Theory*, Chapter V, Corollary 1.3. -/
theorem artinMap_restrictScalars (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : FinitePlace.ramifiedSet K L ⊆ S)
    (E : IntermediateField K L) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) :
    (artinMap L (FinitePlace.placesAbove (K := K) (L := E) S) J).restrictScalars K =
      artinMap L S (FractionalIdeal.relNorm K J) := by
  have hhom : (AlgEquiv.restrictScalarsHom K).comp
        (artinMap L (FinitePlace.placesAbove (K := K) (L := E) S)) =
      (artinMap L S).comp (FractionalIdeal.relNorm K) := by
    apply FractionalIdeal.monoidHom_ext
    intro w
    let v := FinitePlace.below (K := K) w
    have hmem : w ∈ FinitePlace.placesAbove (K := K) (L := E) S ↔ v ∈ S :=
      FinitePlace.mem_placesAbove S w
    change (artinMap L (FinitePlace.placesAbove (K := K) (L := E) S)
        (primeFractionalIdeal E w)).restrictScalars K =
      artinMap L S (FractionalIdeal.relNorm K (primeFractionalIdeal E w))
    by_cases hv : v ∈ S
    · have hw : w ∈ FinitePlace.placesAbove (K := K) (L := E) S := hmem.mpr hv
      rw [artinMap_primeFractionalIdeal_of_mem hw,
        FractionalIdeal.relNorm_primeFractionalIdeal v w, map_pow,
        artinMap_primeFractionalIdeal_of_mem hv, one_pow]
      exact (AlgEquiv.restrictScalarsHom K : (L ≃ₐ[E] L) →* (L ≃ₐ[K] L)).map_one
    · have hw : w ∉ FinitePlace.placesAbove (K := K) (L := E) S :=
        fun h => hv (hmem.mp h)
      rw [artinMap_primeFractionalIdeal_of_notMem hw,
        FractionalIdeal.relNorm_primeFractionalIdeal v w, map_pow,
        artinMap_primeFractionalIdeal_of_notMem hv]
      let u := FinitePlace.PrimeAbove.place (L := L) w (Classical.arbitrary _)
      have hu : FinitePlace.below (K := E) u = w :=
        FinitePlace.PrimeAbove.below_place w (Classical.arbitrary _)
      have huK : FinitePlace.below (K := K) u = v := by
        rw [← FinitePlace.below_below (K := K) (L := E) u, hu]
      exact (frobeniusAt_pow_restrictScalars E v w u
        (FinitePlace.ramificationIdx_eq_one_of_ramifiedSet_subset hS u (huK ▸ hv))).symm
  exact congrArg (fun f : (FractionalIdeal (𝓞 E)⁰ E)ˣ →* (L ≃ₐ[K] L) => f J) hhom

/-- **Norms lie in the kernel**: $\psi^S_{L/K}(N_{L/K}J) = 1$. Milne, *Class Field Theory*,
Chapter V, Corollary 3.4; Childress, *Class Field Theory*, Chapter V, Corollary 1.4. -/
theorem artinMap_relNorm (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : FinitePlace.ramifiedSet K L ⊆ S)
    (J : (FractionalIdeal (𝓞 L)⁰ L)ˣ) :
    artinMap L S (FractionalIdeal.relNorm K J) = 1 := by
  have hhom : (artinMap L S).comp (FractionalIdeal.relNorm K) =
      (1 : (FractionalIdeal (𝓞 L)⁰ L)ˣ →* (L ≃ₐ[K] L)) := by
    apply FractionalIdeal.monoidHom_ext
    intro w
    let v := FinitePlace.below (K := K) w
    change artinMap L S (FractionalIdeal.relNorm K (primeFractionalIdeal L w)) = 1
    rw [FractionalIdeal.relNorm_primeFractionalIdeal v w, map_pow]
    by_cases hv : v ∈ S
    · rw [artinMap_primeFractionalIdeal_of_mem hv, one_pow]
    · rw [artinMap_primeFractionalIdeal_of_notMem hv]
      have hFrob := isFrobeniusAt_frobeniusAt v w.asIdeal
      have horder := hFrob.orderOf_eq_inertiaDeg
        (FinitePlace.ramificationIdx_eq_one_of_ramifiedSet_subset hS w hv)
      rw [← horder, pow_orderOf_eq_one]
  exact congrArg (fun f : (FractionalIdeal (𝓞 L)⁰ L)ˣ →* (L ≃ₐ[K] L) => f J) hhom

end SIC
