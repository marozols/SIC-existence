/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Ideles.Invariants
import SICs.GroupCohomology.Multiplicative

/-!
# Norm residues of idèles and idèle classes

The Tate description of idèle-class norm residues and their comparison with idèle norm
residues, descent of norm quotients under coprime base change, and norm indices in towers.

This is Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII, §2, Proposition 2.5,
"The norm map on idèles", and the last display of §2 (after Proposition 2.8),
with the diagram at the start of §4, and the norm-diagram argument in the proof of Lemma 6.1.

## The argument

For a finite Galois extension `L/K` with group `G`,
$\widehat H^0(G, C_L) \cong C_K / N_{L/K} C_L$; for any finite extension,
$I_K / K^\times N_{L/K} I_L \cong C_K / N_{L/K} C_L$.
For a square of extensions $K\subset L,E\subset M$ with coprime degrees $[L:K]$ and $[E:K]$,
the quotient norm $C_E/N_{M/E}C_M\to C_K/N_{L/K}C_L$ is surjective, giving divisibility of
norm-residue cardinalities.

The fixed points of $C_L$ are the included $C_K$ (`IdeleClassGroup.range_inclusion`), the
inclusion is injective, and the norm $\prod_\sigma \sigma x$ is the included norm
(`IdeleClassGroup.inclusion_norm`), so the norm-residue description
`Representation.tateZeroEquivOfFixed` applies. The quotient map $I_K \to C_K$ carries
$N_{L/K} I_L$ onto $N_{L/K} C_L$, so the preimage of $N_{L/K} C_L$ is $K^\times N_{L/K} I_L$, and
the third isomorphism theorem gives the second isomorphism.
In the extension square, norm transitivity sends $N_{M/E}C_M$ into $N_{L/K}C_L$ and defines
the quotient norm map. The target is killed by $[L:K]$ because the norm of an included class is
its $[L:K]$-th power. The corresponding composite through $C_E$ raises classes to $[E:K]$.
Coprimality makes this power map surjective on the target, so every target element has a preimage
under the quotient norm. The cardinality divisibility follows from this surjection. This is the
norm-diagram portion of Lemma 6.1 for a supplied square of extensions.

In a tower $K\subset L\subset M$, transitivity gives
$N_{M/K}C_M=N_{L/K}(N_{M/L}C_M)\subseteq N_{L/K}C_L$, so
$[C_K:N_{M/K}C_M]=[C_K:N_{L/K}C_L]\,[N_{L/K}C_L:N_{M/K}C_M]$. The norm $N_{L/K}$ maps
$C_L/N_{M/L}C_M$ onto $N_{L/K}C_L/N_{M/K}C_M$, so the second factor divides
$[C_L:N_{M/L}C_M]$. This is the final display in the proof of Milne, Chapter VII, Lemma 5.4.
-/

noncomputable section

open IsDedekindDomain NumberField

namespace SIC

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-! ### Norm residues -/

namespace IdeleClassGroup

/-- For Galois `L/K`: $\widehat H^0(G, C_L) \cong C_K / N_{L/K} C_L$. Milne, *Class Field
Theory*, Chapter VII, §4. -/
def tateZeroEquiv [IsGalois K L] :
    Representation.TateZero
        (_root_.Representation.ofMulDistribMulAction (L ≃ₐ[K] L)
          (NumberField.IdeleClassGroup (𝓞 L) L)) ≃+
      Additive (NumberField.IdeleClassGroup (𝓞 K) K ⧸ (norm (K := K) (L := L)).range) := by
  -- Elaborated before comparison with the stated type: unifying the two directly times out.
  have e := Representation.tateZeroEquivOfFixed (G := L ≃ₐ[K] L)
    (M := NumberField.IdeleClassGroup (𝓞 L) L) (B := NumberField.IdeleClassGroup (𝓞 K) K)
    inclusion inclusion_injective range_inclusion norm
    fun x ↦ (inclusion_norm x).trans (Representation.mulNorm_apply x).symm
  exact e

/-- The norm residues of idèles modulo principal idèles are those of idèle classes:
$I_K / K^\times N_{L/K} I_L \cong C_K / N_{L/K} C_L$. Milne, *Class Field Theory*, Chapter VII,
§2, after Proposition 2.8. -/
def normResidueEquiv :
    NumberField.IdeleGroup (𝓞 K) K ⧸
        (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K ⊔
          (IdeleGroup.norm (K := K) (L := L)).range) ≃*
      NumberField.IdeleClassGroup (𝓞 K) K ⧸ (norm (K := K) (L := L)).range := by
  let P := NumberField.IdeleGroup.principalSubgroup (𝓞 K) K
  let R := (IdeleGroup.norm (K := K) (L := L)).range
  let q := QuotientGroup.mk' P
  have hmap : (P ⊔ R).map q = (norm (K := K) (L := L)).range := by
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    exact map_mk_range_norm
  exact (QuotientGroup.quotientQuotientEquivQuotient P (P ⊔ R) le_sup_left).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hmap)

/-! ### Norm quotients in a base-change square

For $K\subset L,E\subset M$, norm transitivity induces a map
$C_E/N_{M/E}C_M\to C_K/N_{L/K}C_L$. The latter group is killed by $[L:K]$.
If $[E:K]$ is coprime to $[L:K]$, norm after inclusion acts by an invertible power,
so the quotient norm map is surjective. This is the norm-diagram argument of Milne,
*Class Field Theory*, Chapter VII, Lemma 6.1. -/

/-- The norm-residue group is killed by the extension degree, since the norm of an included
idèle class is its degree-th power. Milne, *Class Field Theory*, Chapter VII, Lemma 6.1. -/
theorem normQuotient_pow_finrank_eq_one
    (x : NumberField.IdeleClassGroup (𝓞 K) K ⧸ (norm (K := K) (L := L)).range) :
    x ^ Module.finrank K L = 1 := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact ⟨inclusion (K := K) (L := L) y, norm_inclusion y⟩

variable {E M : Type*} [Field E] [Field M] [NumberField E] [NumberField M]
  [Algebra K E] [Algebra K M] [Algebra L M] [Algebra E M]
  [IsScalarTower K L M] [IsScalarTower K E M]

/-- Norm on the quotient in a base-change square:
$C_E/N_{M/E}C_M\to C_K/N_{L/K}C_L$. Milne, *Class Field Theory*, Chapter VII,
proof of Lemma 6.1, bottom quotient map. -/
def normQuotientMap :
    (NumberField.IdeleClassGroup (𝓞 E) E ⧸ (norm (K := E) (L := M)).range) →*
      NumberField.IdeleClassGroup (𝓞 K) K ⧸ (norm (K := K) (L := L)).range := by
  apply QuotientGroup.map _ _ (norm (K := K) (L := E))
  rintro _ ⟨x, rfl⟩
  exact ⟨norm (K := L) (L := M) x,
    (norm_norm (K := K) (L := L) x).trans (norm_norm (K := K) (L := E) x).symm⟩

/-- The quotient norm map sends the class of $x$ to the class of $N_{E/K}x$. -/
@[simp] theorem normQuotientMap_mk (x : NumberField.IdeleClassGroup (𝓞 E) E) :
    normQuotientMap (K := K) (L := L) (E := E) (M := M) (QuotientGroup.mk x) =
      QuotientGroup.mk (norm (K := K) (L := E) x) := by
  rfl

/-- For coprime base-change degree, the quotient norm map is surjective. Milne,
*Class Field Theory*, Chapter VII, proof of Lemma 6.1. -/
theorem normQuotientMap_surjective
    (hcoprime : (Module.finrank K L).Coprime (Module.finrank K E)) :
    Function.Surjective (normQuotientMap (K := K) (L := L) (E := E) (M := M)) := by
  intro x
  have horder := orderOf_dvd_of_pow_eq_one (normQuotient_pow_finrank_eq_one x)
  obtain ⟨n, hn⟩ := exists_pow_eq_self_of_coprime (hcoprime.symm.of_dvd_right horder)
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  refine ⟨QuotientGroup.mk (inclusion (K := K) (L := E) y ^ n), ?_⟩
  simpa only [normQuotientMap_mk, map_pow, norm_inclusion, QuotientGroup.mk_pow] using hn

/-- Norm-residue cardinalities descend by divisibility under coprime base change. Milne,
*Class Field Theory*, Chapter VII, proof of Lemma 6.1, final divisibility. -/
theorem card_normQuotient_dvd_of_coprime
    (hcoprime : (Module.finrank K L).Coprime (Module.finrank K E)) :
    Nat.card (NumberField.IdeleClassGroup (𝓞 K) K ⧸ (norm (K := K) (L := L)).range) ∣
      Nat.card (NumberField.IdeleClassGroup (𝓞 E) E ⧸ (norm (K := E) (L := M)).range) := by
  exact Subgroup.card_dvd_of_surjective _ (normQuotientMap_surjective
    (K := K) (L := L) (E := E) (M := M) hcoprime)

/-! ### Norm quotients in towers

For $K\subset L\subset M$ the norm subgroup $N_{M/K}C_M$ lies in $N_{L/K}C_L$, and $N_{L/K}$
maps $C_L/N_{M/L}C_M$ onto the relative quotient. Hence norm indices are submultiplicative in
towers, as in the final display of the proof of Milne, *Class Field Theory*, Chapter VII,
Lemma 5.4. -/

/-- The norm index of a tower divides the product of the norm indices of its steps:
$[C_K:N_{M/K}C_M]$ divides $[C_K:N_{L/K}C_L]\,[C_L:N_{M/L}C_M]$. Milne, *Class Field
Theory*, Chapter VII, proof of Lemma 5.4. -/
theorem card_normQuotient_dvd_mul :
    Nat.card (NumberField.IdeleClassGroup (𝓞 K) K ⧸ (norm (K := K) (L := M)).range) ∣
      Nat.card (NumberField.IdeleClassGroup (𝓞 K) K ⧸ (norm (K := K) (L := L)).range) *
        Nat.card (NumberField.IdeleClassGroup (𝓞 L) L ⧸ (norm (K := L) (L := M)).range) := by
  let A := (norm (K := K) (L := L)).range
  let B := (norm (K := K) (L := M)).range
  have hBA : B ≤ A := by
    rintro _ ⟨x, rfl⟩
    exact ⟨norm (K := L) (L := M) x, norm_norm x⟩
  let f := (norm (K := K) (L := L)).rangeRestrict
  have hmap : ((norm (K := L) (L := M)).range).map f = B.subgroupOf A := by
    ext x
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, hy⟩
      exact ⟨y, (norm_norm y).symm.trans (congrArg Subtype.val hy)⟩
    · rintro ⟨y, hy⟩
      exact ⟨norm (K := L) (L := M) y, ⟨y, rfl⟩,
        Subtype.ext ((norm_norm y).trans hy)⟩
  have hdiv : B.relIndex A ∣
      Nat.card (NumberField.IdeleClassGroup (𝓞 L) L ⧸
        (norm (K := L) (L := M)).range) := by
    rw [Subgroup.relIndex, ← hmap, ← Subgroup.index_eq_card]
    exact ((norm (K := L) (L := M)).range).index_map_dvd
      (norm (K := K) (L := L)).rangeRestrict_surjective
  rw [← Subgroup.index_eq_card B, ← Subgroup.index_eq_card A,
    ← Subgroup.relIndex_mul_index hBA]
  simpa only [mul_comm _ A.index] using mul_dvd_mul_right hdiv A.index

end IdeleClassGroup

end SIC
