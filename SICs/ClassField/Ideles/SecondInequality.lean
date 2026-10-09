/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.FieldTheory.Cyclotomic
import SICs.ClassField.Ideles.PowerSubgroupIndex

/-!
# The second inequality

The norm index of a finite abelian extension divides its degree, with equality for cyclic and
prime-degree Galois extensions.

This follows Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII,
Theorem 5.1(a) in prime degree, Lemma 5.2, and the algebraic proof in §6, and then for abelian
extensions by the tower induction of Lemma 5.4.

## The argument

After adjoining a primitive pth root of unity, enlarge S to contain the primes dividing p,
ideal-class representatives, and the support of a cyclic radical generator. The field L then
lies in the S-unit radical field M. A basis of relative Frobenius elements supplies disjoint
primes T splitting in L, with $[M:L]=p^{|T|}$. Put $s=|S|+r_1+r_2$. The local-power
subgroup E has relative index $p^{2s}$, while its principal intersection has relative index
$p^{s+|T|}$. The subgroup index identity cancels these factors. Since $[L:K]=p$ gives
$s=|T|+1$, the index of $K^\times E$ is p. Since E consists of norms, the norm index
divides p. Cyclotomic descent removes the root-of-unity hypothesis, and the first inequality
gives equality.

For an abelian extension of degree $n>1$, an element of prime order $p$ in the Galois group
fixes an intermediate field $E$ with $[L:E]=p$; then $L/E$ is cyclic of prime degree and $E/K$
is abelian of degree $n/p$. Norm indices are submultiplicative in the tower $K\subset E\subset L$
(`IdeleClassGroup.card_normQuotient_dvd_mul`), so induction on $n$ shows that the norm index
divides $n$. Milne's Lemma 5.4 takes a subgroup of index $p$ instead; the top step keeps the
base field fixed through the induction. For cyclic $L/K$ the first inequality gives equality.
-/

noncomputable section

open IsDedekindDomain NumberField
open scoped SIC.FinitePlace SIC.InfinitePlace NumberField.LiesOver

universe u v

namespace SIC.IdeleClassGroup

/-! ### Reduction of the norm index

Apply the second inequality over $K'$ and descend it through the existing quotient norm map.
The quantified extensions live in the universe of $L$, because both actual fields $K'$ and $L'$
live there; the original fields $K$ and $L$ retain independent universes. -/

/-- For a Galois extension of prime degree $p$, proving the norm-index divisibility over fields
containing a primitive $p$th root proves it over every base field.
Milne, *Class Field Theory*, Chapter VII, Lemma 6.1. -/
theorem card_normQuotient_dvd_prime_of_roots
    (p : ℕ) [Fact p.Prime] (K : Type u) (L : Type v)
    [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L] [IsGalois K L]
    (hdegree : Module.finrank K L = p)
    (h : ∀ (E M : Type v) [Field E] [Field M] [NumberField E] [NumberField M]
      [Algebra E M] [IsGalois E M],
      (∃ ζ : E, IsPrimitiveRoot ζ p) → Module.finrank E M = p →
      Nat.card (NumberField.IdeleClassGroup (𝓞 E) E ⧸ (norm (K := E) (L := M)).range) ∣ p) :
    Nat.card (NumberField.IdeleClassGroup (𝓞 K) K ⧸ (norm (K := K) (L := L)).range) ∣ p := by
  let E := CyclotomicBaseChange.base p K L
  let M := CyclotomicField p L
  have hindex := h E M
    ⟨CyclotomicBaseChange.primitiveRoot p K L, CyclotomicBaseChange.primitiveRoot_spec p K L⟩
    (CyclotomicBaseChange.finrank_extension p K L hdegree)
  refine (card_normQuotient_dvd_of_coprime (K := K) (L := L) (E := E) (M := M) ?_).trans hindex
  rw [hdegree]
  exact CyclotomicBaseChange.coprime_finrank_base p K L

end SIC.IdeleClassGroup

namespace SIC.IdeleGroup

variable {K : Type*} [Field K] [NumberField K]

/-! ### Choosing S

The finite support of p and representatives of the ordinary ideal classes give an initial
finite set. The radical-generator theorem enlarges it to contain the cyclic extension. -/

/-- The finite set S satisfies the three finite-place requirements in Milne, *Class Field
Theory*, Chapter VII, §6, construction preceding Lemma 6.2. -/
private theorem exists_kummer_support (p : ℕ) [NeZero p] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (E : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K E] [IsGalois K E] [IsCyclic (E ≃ₐ[K] E)]
    (hdegree : Module.finrank K E = p) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      (∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S) ∧
      Function.Surjective (sIdealClass (K := K) (L := K) S) ∧ E ≤ sUnitKummer K p S := by
  classical
  obtain ⟨S₀, _, hdiv, hclass⟩ :=
    exists_support_sIdealClass (K := K) (L := K) p ∅
  obtain ⟨S, hS, hE⟩ := exists_le_sUnitKummer p hζ E hdegree S₀
  refine ⟨S, ?_, ?_, hE⟩
  · intro v hp
    exact hS (by simpa only [FinitePlace.placesAbove_self] using hdiv v hp)
  · rw [FinitePlace.placesAbove_self] at hclass
    exact sIdealClass_surjective_mono hS hclass

/-- Unramifiedness of the S-unit radical field descends to its intermediate fields.
This is the ramification condition needed in Milne, Chapter VII, Lemma 6.4. -/
private theorem ramificationIdx_intermediate_sUnitKummer (p : ℕ) [NeZero p]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (L : IntermediateField K (sUnitKummer K p S))
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S)
    (w : FinitePlace.PrimeAbove (L := L) v) :
    (FinitePlace.PrimeAbove.place v w).asIdeal.ramificationIdx (𝓞 K) = 1 := by
  let q := FinitePlace.PrimeAbove.place v w
  obtain ⟨u⟩ := (inferInstance : Nonempty (FinitePlace.PrimeAbove (L := sUnitKummer K p S) q))
  let Q := FinitePlace.PrimeAbove.place q u
  have : Q.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.trans Q.asIdeal q.asIdeal v.asIdeal
  have hQ := ramificationIdx_sUnitKummer S v hv (fun hp => hv (hS v hp)) Q
  exact Nat.eq_one_of_dvd_one (hQ ▸ Ideal.ramificationIdx_below_dvd q.asIdeal Q.asIdeal)

open scoped Classical in
/-- Cancelling the two local-power indices gives $[I_K:K^\times E]=p$.
Milne, *Class Field Theory*, Chapter VII, §6, application of Lemmas 6.5–6.7. -/
private theorem index_principal_powerSubgroup (p : ℕ) [NeZero p] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hST : Disjoint S T)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hclass : Function.Surjective (sIdealClass (K := K) (L := K) S))
    (hlocal : Function.Surjective (sUnitsToLocalPowers p S T hST))
    (hcard : S.card + Nat.card (InfinitePlace K) = T.card + 1) :
    (powerSubgroup p S T ⊔ NumberField.IdeleGroup.principalSubgroup (𝓞 K) K).index = p := by
  have hidx := index_powerSubgroup_sup_principal_mul hζ (NeZero.pos p) S T
    hST hS hclass hlocal
  rw [hcard, pow_succ, mul_comm (p ^ T.card) p] at hidx
  exact Nat.eq_of_mul_eq_mul_right (pow_pos (NeZero.pos p) _) hidx

/-! ### The second inequality with roots of unity

A relative Frobenius basis gives T and local S-unit surjectivity. Its size is one less
than the exponent in the degree of M, so the preceding index cancellation applies. -/

/-- The second inequality for a prime-degree intermediate field of an S-unit radical field.
Milne, *Class Field Theory*, Chapter VII, §6, proof after Lemma 6.7. -/
private theorem norm_index_dvd_of_kummer (p : ℕ) [Fact p.Prime] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hclass : Function.Surjective (sIdealClass (K := K) (L := K) S))
    (L : IntermediateField K (sUnitKummer K p S)) (hdegree : Module.finrank K L = p) :
    Nat.card (NumberField.IdeleClassGroup (𝓞 K) K ⧸
      (IdeleClassGroup.norm (K := K) (L := L)).range) ∣ p := by
  let : IsAbelianGalois K (sUnitKummer K p S) :=
    sUnitKummer_isAbelianGalois hζ (NeZero.pos p) S
  obtain ⟨B⟩ := exists_frobeniusBasis_sUnitKummer p hζ S hS L
  have hlocal := B.sUnitsToLocalPowers_surjective hζ hS
  have hdegrees := Module.finrank_mul_finrank K L (sUnitKummer K p S)
  rw [hdegree, ← B.card, finrank_sUnitKummer_eq_pow hζ (NeZero.pos p) S] at hdegrees
  have hcard : S.card + Nat.card (InfinitePlace K) = B.basePrimes.card + 1 := by
    rw [B.card_basePrimes]
    apply Nat.pow_right_injective (Fact.out : p.Prime).two_le
    simpa only [pow_succ'] using hdegrees.symm
  have hidx := index_principal_powerSubgroup p hζ S B.basePrimes
    B.disjoint_basePrimes.symm hS hclass hlocal hcard
  have hnorm := powerSubgroup_le_range_norm (L := L) p S B.basePrimes
    (by rw [hdegree]) (ramificationIdx_intermediate_sUnitKummer p S hS L) B.split_of_mem_basePrimes
  have hle : powerSubgroup p S B.basePrimes ⊔
      NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ≤
      NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔ (norm (K := K) (L := L)).range :=
    sup_le (hnorm.trans le_sup_right) le_sup_left
  have hdiv := Subgroup.index_dvd_of_le hle
  rw [hidx] at hdiv
  rw [← Nat.card_congr (IdeleClassGroup.normResidueEquiv (K := K) (L := L)).toEquiv]
  exact hdiv

end SIC.IdeleGroup

namespace SIC.IdeleClassGroup

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- Embedding a cyclic extension in an algebraic closure places it in an S-unit radical
field without changing its norm subgroup. Milne, Chapter VII, §6, construction of M. -/
private theorem norm_index_dvd_of_roots
    (p : ℕ) [Fact p.Prime] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hdegree : Module.finrank K L = p) :
    Nat.card (NumberField.IdeleClassGroup (𝓞 K) K ⧸ (norm (K := K) (L := L)).range) ∣ p := by
  let : IsCyclic (L ≃ₐ[K] L) := isCyclic_of_prime_card
    (p := p) (by rw [IsGalois.card_aut_eq_finrank, hdegree])
  let f : L →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  let E := f.fieldRange
  let e : L ≃ₐ[K] E := f.equivFieldRange
  let : FiniteDimensional K E := e.toLinearEquiv.finiteDimensional
  let : IsGalois K E := IsGalois.of_algEquiv e
  let : IsCyclic (E ≃ₐ[K] E) :=
    isCyclic_of_surjective e.autCongr.toMonoidHom e.autCongr.surjective
  have hEdegree : Module.finrank K E = p := e.toLinearEquiv.finrank_eq.symm.trans hdegree
  obtain ⟨S, hS, hclass, hE⟩ := IdeleGroup.exists_kummer_support p hζ E hEdegree
  let E' := IntermediateField.restrict hE
  let e' : L ≃ₐ[K] E' := e.trans (IntermediateField.restrictAlgEquiv hE)
  have hdegree' : Module.finrank K E' = p := e'.toLinearEquiv.finrank_eq.symm.trans hdegree
  rw [range_norm_congr e']
  exact IdeleGroup.norm_index_dvd_of_kummer p hζ S hS hclass E' hdegree'

/-! ### Cyclotomic descent and equality

The coprime cyclotomic base-change map descends divisibility from a base containing roots
of unity. The first inequality supplies the opposite bound and therefore the exact index. -/

/-- The norm index divides p for a Galois extension of prime degree p.
Milne, *Class Field Theory*, Chapter VII, Theorem 5.1(a), prime-degree case proved in §6. -/
theorem secondInequality_of_prime_degree (p : ℕ) [Fact p.Prime]
    (hdegree : Module.finrank K L = p) :
    Nat.card (NumberField.IdeleClassGroup (𝓞 K) K ⧸ (norm (K := K) (L := L)).range) ∣ p := by
  apply card_normQuotient_dvd_prime_of_roots p K L hdegree
  intro E M _ _ _ _ _ _ hroot hdeg
  obtain ⟨ζ, hζ⟩ := hroot
  exact norm_index_dvd_of_roots p hζ hdeg


end SIC.IdeleClassGroup

/-! ### Abelian extensions

A finite Galois extension of degree greater than one has an intermediate field of prime
codegree. In an abelian extension the lower part is again abelian, so the prime-degree second
inequality propagates up the tower. -/

namespace SIC.IdeleClassGroup

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- **The second inequality for abelian extensions**: the norm index $[C_K:N_{L/K}C_L]$ divides
$[L:K]$; in particular it is finite. Milne, *Class Field Theory*, Chapter VII, Theorem 5.1(a)
for abelian Galois groups, by the tower induction of Lemma 5.4 from the prime-degree case. -/
theorem secondInequality_of_isAbelianGalois [IsAbelianGalois K L] :
    Nat.card (NumberField.IdeleClassGroup (𝓞 K) K ⧸ (norm (K := K) (L := L)).range) ∣
      Module.finrank K L := by
  classical
  apply IsAbelianGalois.induction_finrank_prime (K := K)
    (P := fun F [Field F] [Algebra K F] [FiniteDimensional K F] =>
      letI : NumberField F := NumberField.of_module_finite K F
      Nat.card (NumberField.IdeleClassGroup (𝓞 K) K ⧸
        (norm (K := K) (L := F)).range) ∣ Module.finrank K F) (L := L)
  · intro F _ _ _ _
    refine (letI : NumberField F := NumberField.of_module_finite K F; ?_)
    intro hdegree
    have htriv : ∀ x : NumberField.IdeleClassGroup (𝓞 K) K ⧸
        (norm (K := K) (L := F)).range, x = 1 := by
      intro x
      simpa only [hdegree, pow_one] using normQuotient_pow_finrank_eq_one (K := K) (L := F) x
    have hcard : Nat.card (NumberField.IdeleClassGroup (𝓞 K) K ⧸
        (norm (K := K) (L := F)).range) = 1 :=
      Nat.card_eq_one_iff_unique.mpr
        ⟨⟨fun x y => (htriv x).trans (htriv y).symm⟩, ⟨1⟩⟩
    simp [hdegree, hcard]
  · intro F _ _ _ _
    refine (letI : NumberField F := NumberField.of_module_finite K F; ?_)
    intro E hprime hbase
    have : Fact (Module.finrank E F).Prime := ⟨hprime⟩
    have htop := secondInequality_of_prime_degree (K := E) (L := F)
      (Module.finrank E F) rfl
    have htower := card_normQuotient_dvd_mul (K := K) (L := E) (M := F)
    exact htower.trans ((mul_dvd_mul hbase htop).trans
      (dvd_of_eq (Module.finrank_mul_finrank K E F)))

/-- **The cyclic norm index equality** $[C_K:N_{L/K}C_L]=[L:K]$. Childress, *Class Field
Theory* (2009), Chapter IV, Theorem 5.12; Milne, *Class Field Theory*, Chapter VII, Lemma 5.2,
from the first inequality and `secondInequality_of_isAbelianGalois`. -/
theorem card_normQuotient_eq_finrank [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] :
    Nat.card (NumberField.IdeleClassGroup (𝓞 K) K ⧸ (norm (K := K) (L := L)).range) =
      Module.finrank K L := by
  have : IsAbelianGalois K L := IsAbelianGalois.of_isCyclic K L
  exact Nat.le_antisymm
    (Nat.le_of_dvd Module.finrank_pos (secondInequality_of_isAbelianGalois (K := K) (L := L)))
    (firstInequality (K := K) (L := L))

end SIC.IdeleClassGroup
