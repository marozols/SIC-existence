/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Reciprocity.ArtinMap
import SICs.ClassField.Ideles.NormApproximation
import SICs.ClassField.Ideles.SecondInequality

/-!
# The Artin map on congruent idèles

The Artin map evaluated on fractional ideals of congruent idèles, its surjectivity and
triviality on norms, and the comparison of its kernel with norm residues for abelian
extensions.

For a modulus `m` with support `S` containing the ramified primes of `L/K`, the congruent idèles
$J^+_{K,\mathfrak m}$ replace the ideal group $I_K(\mathfrak m)$ of Childress, *Class Field
Theory* (2009), Chapter IV, Proposition 5.6 and Chapter V, §2, and the Artin map of an idèle `y`
is $\psi^S_{L/K}((y))$. The principal congruent idèles are Childress's $F^+_{\mathfrak m}$, so
$\psi^S$ vanishing on them is the reciprocity law of his Theorem 2.1(ii).

## The argument

*Norms.* The fractional ideal of a norm idèle is the relative norm of a fractional ideal
(`IdeleGroup.toFractionalIdeal_norm`), and norms lie in the kernel of the Artin map
(`artinMap_relNorm`).

*Surjectivity.* Frobenius elements outside `S` generate the Galois group. Their uniformizer
idèles have component one at `S` and at the infinite places, so they are congruent and their
Artin images generate the full Galois group.

*Comparison.* Let `L/K` be abelian of degree `n`. On
$J^+_{K,\mathfrak m}$ consider the kernel `A` of $y\mapsto\psi^S((y))$ and the norm residues
$B = J^+_{K,\mathfrak m}\cap K^\times N_{L/K}J_L$. Both have index `n`: `A` by surjectivity and
$|\operatorname{Gal}(L/K)| = n$, `B` has index dividing `n` by the second inequality.
Containment `B ⊆ A` forces
the indices to agree, hence `A = B`. For the converse direction in a cyclic extension,
the cyclic norm index equality gives `A = B` from `A ⊆ B`. If $\psi^S$ vanishes on the principal
congruent idèles, then $B\subseteq A$: write $y = aN_{L/K}z$, use norm approximation to make
$N_{L/K}(\beta z)$ congruent, and note that $aN_{L/K}\beta^{-1}$ is then a principal congruent
idèle. Conversely, if $A \subseteq B$ (Childress, Chapter V, Proposition 2.2), the equality
$A = B$ makes every principal congruent idèle lie in `A`.
-/

noncomputable section

open IsDedekindDomain NumberField
open scoped nonZeroDivisors

namespace SIC.IdeleGroup

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-! ### Norms and surjectivity

Norm compatibility kills norm idèles. Uniformizer idèles of prime ideals outside the
modulus supply all Frobenius generators in the congruent subgroup. -/

section Abelian

variable [IsAbelianGalois K L]

/-- Norm idèles have trivial Artin image: $\psi^S_{L/K}((N_{L/K}z)) = 1$. Milne, *Class Field
Theory*, Chapter V, Corollary 3.4, through `toFractionalIdeal_norm`. -/
theorem artinMap_toFractionalIdeal_norm (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : FinitePlace.ramifiedSet K L ⊆ S)
    (z : NumberField.IdeleGroup (𝓞 L) L) :
    artinMap L S (toFractionalIdeal (norm (K := K) (L := L) z)) = 1 := by
  rw [toFractionalIdeal_norm]
  exact artinMap_relNorm S hS _

/-- The Artin map is surjective on congruent idèles. Childress, *Class Field Theory*, Chapter V,
Theorem 2.1(i), on the uniformizer idèles of fractional ideals prime to the modulus. -/
theorem exists_mem_congruentSubgroup_artinMap_eq (m : Ideal (𝓞 K))
    (hS : FinitePlace.ramifiedSet K L ⊆ FinitePlace.modulusSupport m)
    (g : L ≃ₐ[K] L) :
    ∃ y ∈ congruentSubgroup Set.univ m,
      artinMap L (FinitePlace.modulusSupport m) (toFractionalIdeal y) = g := by
  obtain ⟨J, hJ, hg⟩ := exists_mem_primeTo_artinMap_eq (L := L)
    (FinitePlace.modulusSupport m) hS g
  refine ⟨ofFractionalIdeal J, ofFractionalIdeal_mem_congruentSubgroup Set.univ m hJ, ?_⟩
  simpa only [toFractionalIdeal_ofFractionalIdeal] using hg

end Abelian

/-! ### Comparing Artin kernels with norm residues

Surjectivity gives the Artin kernel index. For abelian extensions the second inequality
bounds the norm residue index, and containment forces equality. The reverse containment
uses the cyclic norm index equality. -/

section Comparison

variable [IsAbelianGalois K L]

/-- The Artin kernel and the norm residues have the same index in the congruent idèles;
used by the converse cyclic comparison below. -/
private theorem relIndex_artinKernel_eq_normResidues [IsCyclic (L ≃ₐ[K] L)]
    (m : Ideal (𝓞 K))
    (hS : FinitePlace.ramifiedSet K L ⊆ FinitePlace.modulusSupport m) :
    (congruentSubgroup Set.univ m ⊓
      ((artinMap L (FinitePlace.modulusSupport m)).comp toFractionalIdeal).ker).relIndex
        (congruentSubgroup Set.univ m) =
      (congruentSubgroup Set.univ m ⊓ (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔
        (norm (K := K) (L := L)).range)).relIndex (congruentSubgroup Set.univ m) := by
  let H := congruentSubgroup Set.univ m
  let f := (artinMap L (FinitePlace.modulusSupport m)).comp toFractionalIdeal
  have hmap : H.map f = ⊤ := by
    apply eq_top_iff.mpr
    intro g _
    obtain ⟨y, hy, hgy⟩ := exists_mem_congruentSubgroup_artinMap_eq m hS g
    exact ⟨y, hy, hgy⟩
  change (H ⊓ f.ker).relIndex H = _
  rw [Subgroup.inf_relIndex_left, Subgroup.relIndex_ker, hmap]
  rw [relIndex_congruentSubgroup_inf, IdeleClassGroup.card_normQuotient_eq_finrank,
    ← IsGalois.card_aut_eq_finrank K L]
  simp

/-- For cyclic extensions, containment of the Artin kernel in the norm residues is
an equality, by the cyclic norm index formula. -/
private theorem artinKernel_eq_normResidues_of_le [IsCyclic (L ≃ₐ[K] L)]
    (m : Ideal (𝓞 K))
    (hS : FinitePlace.ramifiedSet K L ⊆ FinitePlace.modulusSupport m)
    (hle : congruentSubgroup Set.univ m ⊓
        ((artinMap L (FinitePlace.modulusSupport m)).comp toFractionalIdeal).ker ≤
      congruentSubgroup Set.univ m ⊓ (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔
        (norm (K := K) (L := L)).range)) :
    congruentSubgroup Set.univ m ⊓
        ((artinMap L (FinitePlace.modulusSupport m)).comp toFractionalIdeal).ker =
      congruentSubgroup Set.univ m ⊓ (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔
        (norm (K := K) (L := L)).range) := by
  let H := congruentSubgroup Set.univ m
  let A := H ⊓ ((artinMap L (FinitePlace.modulusSupport m)).comp toFractionalIdeal).ker
  let B := H ⊓ (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔
    (norm (K := K) (L := L)).range)
  have heq : A.relIndex H = B.relIndex H :=
    relIndex_artinKernel_eq_normResidues m hS
  have hpos : 0 < B.relIndex H := by
    change (congruentSubgroup Set.univ m ⊓ _).relIndex (congruentSubgroup Set.univ m) > 0
    rw [relIndex_congruentSubgroup_inf, IdeleClassGroup.card_normQuotient_eq_finrank]
    exact Module.finrank_pos
  exact SIC.Subgroup.eq_of_le_of_relIndex_eq A B H hle inf_le_left heq
    (Nat.ne_of_gt hpos)

omit [IsAbelianGalois K L] in
/-- A congruent norm residue can be written as a product of a congruent principal idèle and
a congruent norm; used by `artinMap_eq_one_iff_of_principal`. -/
private theorem exists_principal_norm_factors_congruent (m : Ideal (𝓞 K))
    {x : NumberField.IdeleGroup (𝓞 K) K}
    (hx : x ∈ congruentSubgroup Set.univ m ⊓
      (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔
        (norm (K := K) (L := L)).range)) :
    ∃ (a : Kˣ) (z : NumberField.IdeleGroup (𝓞 L) L),
      NumberField.IdeleGroup.unitEmbedding (𝓞 K) K a ∈ congruentSubgroup Set.univ m ∧
      norm (K := K) (L := L) z ∈ congruentSubgroup Set.univ m ∧
      x = NumberField.IdeleGroup.unitEmbedding (𝓞 K) K a * norm (K := K) (L := L) z := by
  let H := congruentSubgroup Set.univ m
  let P := NumberField.IdeleGroup.principalSubgroup (𝓞 K) K
  obtain ⟨p, hp, n, hn, hpn⟩ := Subgroup.mem_sup.mp hx.2
  obtain ⟨a, rfl⟩ := hp
  obtain ⟨z, rfl⟩ := hn
  obtain ⟨b, hb⟩ := exists_norm_mul_mem_congruentSubgroup (K := K) (L := L) m z
  let t := norm (K := K) (L := L) (NumberField.IdeleGroup.unitEmbedding (𝓞 L) L b * z)
  let q := x * t⁻¹
  have hqH : q ∈ H := H.mul_mem hx.1 (H.inv_mem hb)
  have hbP : norm (K := K) (L := L) (NumberField.IdeleGroup.unitEmbedding (𝓞 L) L b) ∈ P :=
    principalSubgroup_le_comap_norm (K := K) (L := L) ⟨b, rfl⟩
  have hqeq : q = NumberField.IdeleGroup.unitEmbedding (𝓞 K) K a *
      (norm (K := K) (L := L) (NumberField.IdeleGroup.unitEmbedding (𝓞 L) L b))⁻¹ := by
    dsimp [q, t]
    rw [← hpn, map_mul]
    simp [mul_assoc, mul_comm]
  have hqP : q ∈ P := by
    rw [hqeq]
    exact P.mul_mem ⟨a, rfl⟩ (P.inv_mem hbP)
  obtain ⟨c, hc⟩ := hqP
  have hcH : NumberField.IdeleGroup.unitEmbedding (𝓞 K) K c ∈ H := by
    rw [hc]
    exact hqH
  refine ⟨c, NumberField.IdeleGroup.unitEmbedding (𝓞 L) L b * z, hcH, hb, ?_⟩
  have hxt : q * t = x := by simp [q, mul_assoc]
  rw [← hc] at hxt
  exact hxt.symm

/-- In an abelian extension, norm residues contained in the Artin kernel equal that
kernel: the first index is the Galois degree, while the second divides it.
Used by `artinMap_eq_one_iff_of_principal`. -/
private theorem normResidues_eq_artinKernel_of_le (m : Ideal (𝓞 K))
    (hS : FinitePlace.ramifiedSet K L ⊆ FinitePlace.modulusSupport m)
    (hle : congruentSubgroup Set.univ m ⊓
        (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔
          (norm (K := K) (L := L)).range) ≤
      congruentSubgroup Set.univ m ⊓
        ((artinMap L (FinitePlace.modulusSupport m)).comp toFractionalIdeal).ker) :
    congruentSubgroup Set.univ m ⊓
        (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔
          (norm (K := K) (L := L)).range) =
      congruentSubgroup Set.univ m ⊓
        ((artinMap L (FinitePlace.modulusSupport m)).comp toFractionalIdeal).ker := by
  let H := congruentSubgroup Set.univ m
  let P := NumberField.IdeleGroup.principalSubgroup (𝓞 K) K
  let C := P ⊔ (norm (K := K) (L := L)).range
  let f := (artinMap L (FinitePlace.modulusSupport m)).comp toFractionalIdeal
  have hAindex : (H ⊓ f.ker).relIndex H = Module.finrank K L := by
    have hmap : H.map f = ⊤ := by
      apply eq_top_iff.mpr
      intro g _
      obtain ⟨y, hy, hgy⟩ := exists_mem_congruentSubgroup_artinMap_eq m hS g
      exact ⟨y, hy, hgy⟩
    rw [Subgroup.inf_relIndex_left, Subgroup.relIndex_ker, hmap,
      Subgroup.card_top, IsGalois.card_aut_eq_finrank]
  have hBindex : (H ⊓ C).relIndex H ∣ Module.finrank K L := by
    rw [relIndex_congruentSubgroup_inf]
    exact IdeleClassGroup.secondInequality_of_isAbelianGalois
  have hindex : (H ⊓ f.ker).relIndex H = (H ⊓ C).relIndex H := by
    apply Nat.dvd_antisymm
    · exact Subgroup.relIndex_dvd_of_le_left H hle
    · rw [hAindex]
      exact hBindex
  have hpos : (H ⊓ f.ker).relIndex H ≠ 0 := by
    rw [hAindex]
    exact (Module.finrank_pos (R := K) (M := L)).ne'
  exact SIC.Subgroup.eq_of_le_of_relIndex_eq (H ⊓ C) (H ⊓ f.ker)
    H hle inf_le_left hindex.symm hpos

/-- If the Artin map vanishes on the principal congruent idèles, then on congruent idèles its
kernel is exactly the norm residues. Childress, *Class Field Theory*, Chapter V, proof of
Theorem 2.1(ii), the index argument, in the direction used for cyclotomic subextensions. -/
theorem artinMap_eq_one_iff_of_principal (m : Ideal (𝓞 K))
    (hS : FinitePlace.ramifiedSet K L ⊆ FinitePlace.modulusSupport m)
    (hprin : ∀ a : Kˣ, NumberField.IdeleGroup.unitEmbedding (𝓞 K) K a ∈
      congruentSubgroup Set.univ m →
      artinMap L (FinitePlace.modulusSupport m) (toPrincipalIdeal (𝓞 K) K a) = 1)
    {y : NumberField.IdeleGroup (𝓞 K) K} (hy : y ∈ congruentSubgroup Set.univ m) :
    artinMap L (FinitePlace.modulusSupport m) (toFractionalIdeal y) = 1 ↔
      y ∈ NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔ (norm (K := K) (L := L)).range := by
  let H := congruentSubgroup Set.univ m
  let P := NumberField.IdeleGroup.principalSubgroup (𝓞 K) K
  let C := P ⊔ (norm (K := K) (L := L)).range
  let f := (artinMap L (FinitePlace.modulusSupport m)).comp toFractionalIdeal
  have hle : H ⊓ C ≤ H ⊓ f.ker := by
    intro x hx
    obtain ⟨a, z, ha, hz, hfac⟩ :=
      exists_principal_norm_factors_congruent (K := K) (L := L) m hx
    have haF : f (NumberField.IdeleGroup.unitEmbedding (𝓞 K) K a) = 1 := by
      change artinMap L (FinitePlace.modulusSupport m)
        (toFractionalIdeal (NumberField.IdeleGroup.unitEmbedding (𝓞 K) K a)) = 1
      rw [IdeleGroup.toFractionalIdeal_unitEmbedding]
      exact hprin a ha
    have hzF : f (norm (K := K) (L := L) z) = 1 :=
      artinMap_toFractionalIdeal_norm (K := K) (L := L)
        (FinitePlace.modulusSupport m) hS z
    have hxF : f x = 1 := by
      rw [hfac, map_mul, haF, hzF, one_mul]
    exact ⟨hx.1, hxF⟩
  have heq := normResidues_eq_artinKernel_of_le m hS hle
  constructor
  · intro h
    exact (heq.symm.le ⟨hy, h⟩).2
  · intro h
    exact (heq.le ⟨hy, h⟩).2

variable [IsCyclic (L ≃ₐ[K] L)]

/-- **The reciprocity law from Childress's Proposition 2.2**: if every congruent idèle in the
kernel of the Artin map is a norm residue, then the Artin map vanishes on the principal
congruent idèles. Childress, *Class Field Theory*, Chapter V, proof of Theorem 2.1(ii), the index
argument for cyclic extensions. -/
theorem artinMap_toPrincipalIdeal_eq_one_of_le (m : Ideal (𝓞 K))
    (hS : FinitePlace.ramifiedSet K L ⊆ FinitePlace.modulusSupport m)
    (hker : ∀ y ∈ congruentSubgroup Set.univ m,
      artinMap L (FinitePlace.modulusSupport m) (toFractionalIdeal y) = 1 →
        y ∈ NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔ (norm (K := K) (L := L)).range)
    (a : Kˣ) (ha : NumberField.IdeleGroup.unitEmbedding (𝓞 K) K a ∈ congruentSubgroup Set.univ m) :
    artinMap L (FinitePlace.modulusSupport m) (toPrincipalIdeal (𝓞 K) K a) = 1 := by
  let H := congruentSubgroup Set.univ m
  let f := (artinMap L (FinitePlace.modulusSupport m)).comp toFractionalIdeal
  let C := NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔
    (norm (K := K) (L := L)).range
  have hle : H ⊓ f.ker ≤ H ⊓ C := by
    intro y hy
    exact ⟨hy.1, hker y hy.1 hy.2⟩
  have heq := artinKernel_eq_normResidues_of_le m hS hle
  change H ⊓ f.ker = H ⊓ C at heq
  have hp : NumberField.IdeleGroup.unitEmbedding (𝓞 K) K a ∈ C :=
    (le_sup_left : NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ≤ C) ⟨a, rfl⟩
  have hmem : NumberField.IdeleGroup.unitEmbedding (𝓞 K) K a ∈ H ⊓ f.ker :=
    heq.symm ▸ ⟨ha, hp⟩
  have hf := hmem.2
  change artinMap L (FinitePlace.modulusSupport m)
    (toFractionalIdeal (NumberField.IdeleGroup.unitEmbedding (𝓞 K) K a)) = 1 at hf
  rwa [IdeleGroup.toFractionalIdeal_unitEmbedding] at hf

end Comparison

end SIC.IdeleGroup
