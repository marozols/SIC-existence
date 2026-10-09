/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.FieldTheory.Kummer.Duality

/-!
# Degrees of Kummer extensions

Absolute and relative degrees of a radical extension count the power classes of its radicands.

This follows Milne, *Fields and Galois Theory*, version 5.10 (2022), the final annihilator
argument of Theorem 5.30, and *Class Field Theory*, Chapter VII, Appendix A.3.
The cyclicity of a single-radical extension is used in Chapter VII, Proposition 9.2,
p. 224, footnote 7.

## The argument

For $K\subseteq L\subseteq M=K[B^{1/n}]$, restrict the Kummer pairing for $M/L$ to the original
group $B$. Its kernel consists of the elements of $B$ that are nth powers in $L$. Its image
is the full character group: an automorphism
annihilated by every such character fixes all generating radicals and is therefore the identity.
Finite character duality and the first isomorphism theorem identify the number of these power
classes with the extension degree.
For one radicand, evaluation of the pairing at its generator is faithful, so the Galois
group embeds into the cyclic group of nth roots of unity.
-/

noncomputable section

namespace SIC

variable {K : Type*} [Field K] {n : ℕ} {B : Subgroup Kˣ}

section ScalarTower

variable (L : Type*) [Field L] [Algebra K L] [Algebra L (kummerExtension K n B)]
  [IsScalarTower K L (kummerExtension K n B)]

/-! ### Characters from the specified radicands

Map the supplied subgroup into the radicands over $L$. Restrict the existing Kummer pairing
along this map and regard its roots of unity as units of $L$. Taking $L=K$ will recover the
absolute degree formula from the same character argument. -/

/-- The original radicands, mapped into $L$, admit roots in $M=K[B^{1/n}]$.
This supplies the restriction used by `generatorCharacters`. -/
private def generatorRadicands [NeZero n] :
    B →* kummerRadicands L n (kummerExtension K n B) :=
  ((Units.map (algebraMap K L : K →* L)).comp B.subtype).codRestrict _ fun b ↦ by
    obtain ⟨x, hx⟩ := exists_root_kummerExtension (NeZero.pos n) b
    exact ⟨x, hx.trans (IsScalarTower.algebraMap_apply K L _ _)⟩

/-- The restriction of `kummerPairing` to the specified radicands, with values in $L^\times$
characters; used in both degree formulas. -/
private def generatorCharacters [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    B →* (Gal((kummerExtension K n B)/L) →* Lˣ) :=
  (MonoidHom.compHom (rootsOfUnity n L).subtype).comp
    ((kummerPairing (hζ.map_of_injective (algebraMap K L).injective)).comp
      (generatorRadicands L))

/-- The restricted pairing has kernel $B\cap L^{\times n}$; used by the degree formulas.
This is `ker_kummerPairing` pulled back along the original radicands. -/
private theorem ker_generatorCharacters [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    [FiniteDimensional L (kummerExtension K n B)] [IsGalois L (kummerExtension K n B)] :
    (generatorCharacters L (B := B) hζ).ker =
      (powMonoidHom n : Lˣ →* Lˣ).range.comap
        ((Units.map (algebraMap K L : K →* L)).comp B.subtype) := by
  have hinj : Function.Injective
      (MonoidHom.compHom (M := Gal((kummerExtension K n B)/L)) (rootsOfUnity n L).subtype) := by
    intro χ ψ h
    apply MonoidHom.ext
    intro σ
    exact Subtype.val_injective (DFunLike.congr_fun h σ)
  rw [generatorCharacters, MonoidHom.ker_comp_of_injective _ _ hinj,
    ← MonoidHom.comap_ker, ker_kummerPairing]
  ext b
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, congrArg Subtype.val ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩

/-- An automorphism annihilated by all characters from $B$ fixes every generating radical.
Milne, *Fields and Galois Theory*, Theorem 5.30, final annihilator argument. -/
private theorem generatorCharacters_separate [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (σ : Gal((kummerExtension K n B)/L))
    (h : ∀ b : B, generatorCharacters L hζ b σ = 1) : σ = 1 := by
  apply AlgEquiv.restrictScalars_injective K
  apply AlgEquiv.coe_toAlgHom_injective
  apply kummerExtension_algHom_ext
  intro b x hx
  have hx0 : x ≠ 0 := by
    intro hx0
    apply b.val.ne_zero
    apply (algebraMap K (kummerExtension K n B)).injective
    simpa [hx0, NeZero.ne n] using hx.symm
  let α : (kummerExtension K n B)ˣ := Units.mk0 x hx0
  let a := generatorRadicands L (n := n) b
  have hα : α ^ n = Units.map (algebraMap L (kummerExtension K n B) :
      L →* kummerExtension K n B) a.val :=
    Units.ext (hx.trans (IsScalarTower.algebraMap_apply K L _ _))
  have hp := kummerPairing_apply (hζ.map_of_injective (algebraMap K L).injective) a α hα σ
  have hc : (kummerPairing (hζ.map_of_injective (algebraMap K L).injective) a σ).val = 1 := h b
  rw [hc, map_one] at hp
  exact congrArg Units.val (div_eq_one.mp hp.symm)

/-! ### The annihilator and the degree

Finite abelian duality identifies subgroups of the character group with their annihilators.
The preceding separation argument makes this annihilator trivial, so all characters arise
from the supplied radicands. The first isomorphism theorem then computes the degree. -/

open scoped IsMulCommutative

/-- A relative automorphism is killed by $n$, as is its restriction of scalars to $K$.
This transfers `kummerExtension_aut_pow` to the relative character-duality argument. -/
private theorem relativeAut_pow {ζ : K} (hζ : IsPrimitiveRoot ζ n) (hn : 0 < n)
    (σ : Gal((kummerExtension K n B)/L)) : σ ^ n = 1 := by
  apply AlgEquiv.restrictScalars_injective K
  exact ((AlgEquiv.restrictScalarsHom K).map_pow σ n).trans
    (kummerExtension_aut_pow hζ hn (σ.restrictScalars K))

/-- Every $L^\times$-valued character arises from the specified radicands.
Milne, *Fields and Galois Theory*, Theorem 5.30, final annihilator argument. -/
private theorem generatorCharacters_surjective [NeZero n]
    [FiniteDimensional L (kummerExtension K n B)]
    [IsAbelianGalois L (kummerExtension K n B)] {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    Function.Surjective (generatorCharacters L (B := B) hζ) := by
  have : HasEnoughRootsOfUnity L (Monoid.exponent Gal((kummerExtension K n B)/L)) :=
    hasEnoughRootsOfUnity_exponent (hζ.map_of_injective (algebraMap K L).injective)
      (relativeAut_pow L hζ (NeZero.pos n))
  let e := CommGroup.subgroupOrderIsoSubgroupMonoidHom Gal((kummerExtension K n B)/L) L
  have hbot : e.symm (OrderDual.toDual (generatorCharacters L (B := B) hζ).range) = ⊥ := by
    apply bot_unique
    intro σ hσ
    apply Subgroup.mem_bot.mpr
    apply generatorCharacters_separate L hζ σ
    intro b
    exact (CommGroup.mem_subgroupOrderIsoSubgroupMonoidHom_symm_iff L _ σ).mp hσ
      _ ⟨b, rfl⟩
  exact MonoidHom.range_eq_top.mp (e.symm.injective (hbot.trans e.symm.map_bot.symm))

/-- The degree over any intermediate scalar field counts the supplied radicands modulo
nth powers in that field; shared argument for the absolute and relative degree formulas.
Milne, *Fields and Galois Theory*, Theorem 5.30, and *Class Field Theory*, VII, Appendix A.3. -/
private theorem finrank_eq_card_quotient {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (hn : 0 < n) (hB : B.FG) :
    Module.finrank L (kummerExtension K n B) =
      Nat.card (B ⧸ (powMonoidHom n : Lˣ →* Lˣ).range.comap
        ((Units.map (algebraMap K L : K →* L)).comp B.subtype)) := by
  have : NeZero n := ⟨hn.ne'⟩
  have : FiniteDimensional K (kummerExtension K n B) :=
    kummerExtension_finiteDimensional hn hB
  have := FiniteDimensional.right K L (kummerExtension K n B)
  have := kummerExtension_isAbelianGalois (B := B) hζ hn
  have := IsAbelianGalois.tower_top K L (kummerExtension K n B)
  have : HasEnoughRootsOfUnity L (Monoid.exponent Gal((kummerExtension K n B)/L)) :=
    hasEnoughRootsOfUnity_exponent (hζ.map_of_injective (algebraMap K L).injective)
      (relativeAut_pow L hζ hn)
  rw [← ker_generatorCharacters L hζ,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
      (generatorCharacters L (B := B) hζ) (generatorCharacters_surjective L hζ)).toEquiv,
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity, IsGalois.card_aut_eq_finrank]

end ScalarTower

/-! ### Absolute and relative degree formulas

Taking $L=K$ gives the absolute formula. For an intermediate field $L$, a base-field unit
maps to an nth power in $L^\times$ exactly when it lies in $B(L)$. For a single radicand,
the pairing embeds the Galois group into $\mu_n$, and the radicand quotient is cyclic and
killed by $n$, so its order divides $n$. -/

/-- The degree $[K[B^{1/n}]:K]$ is $|B/(B\cap K^{\times n})|$ for finitely generated $B$.
Milne, *Fields and Galois Theory*, Theorem 5.30, and *Class Field Theory*, Chapter VII,
Appendix A.3, degree formula for the constructed extension. -/
theorem kummerExtension_finrank {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (hn : 0 < n) (hB : B.FG) :
    Module.finrank K (kummerExtension K n B) =
      Nat.card (B ⧸ ((powMonoidHom n : Kˣ →* Kˣ).range.comap B.subtype)) := by
  simpa using finrank_eq_card_quotient K hζ hn hB

/-- For an intermediate field $L$ of $M=K[B^{1/n}]$, the relative degree $[M:L]$ is
$|B/(B\cap L^{\times n})|$. Milne, *Class Field Theory*, Chapter VII, Appendix A.3,
applied in the proof of Lemma 6.9. -/
theorem kummerExtension_finrank_relative {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (hn : 0 < n) (hB : B.FG)
    (L : IntermediateField K (kummerExtension K n B)) :
    Module.finrank L (kummerExtension K n B) =
      Nat.card (B ⧸ (kummerRadicands K n L).comap B.subtype) := by
  rw [finrank_eq_card_quotient L hζ hn hB]
  congr 2
  ext b
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, congrArg Units.val ha⟩
  · rintro ⟨a, ha⟩
    have ha0 : a ≠ 0 := by
      intro h
      apply b.val.ne_zero
      apply (algebraMap K L).injective
      simpa [h, hn.ne'] using ha.symm
    exact ⟨Units.mk0 a ha0, Units.ext ha⟩

/-- Adjoining the nth roots of one radicand gives a cyclic extension when $\mu_n\subset K$.
Milne, *Class Field Theory*, Chapter VII, Proposition 9.2, p. 224, footnote 7. -/
theorem kummerExtension_isCyclic_zpowers {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (hn : 0 < n) (b : Kˣ) :
    IsCyclic Gal((kummerExtension K n (Subgroup.zpowers b))/K) := by
  have : NeZero n := ⟨hn.ne'⟩
  let b' : Subgroup.zpowers b := ⟨b, Subgroup.mem_zpowers b⟩
  let χ := kummerPairing hζ (generatorRadicands K (n := n) b')
  apply isCyclic_of_injective χ
  apply (injective_iff_map_eq_one χ).mpr
  intro σ hσ
  apply generatorCharacters_separate K hζ σ
  intro c
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp c.property
  have hc : c = b' ^ k := Subtype.ext hk.symm
  have hb : generatorCharacters K hζ b' σ = 1 := congrArg Subtype.val hσ
  rw [hc]
  change (generatorCharacters K hζ).flip σ (b' ^ k) = 1
  rw [map_zpow, show (generatorCharacters K hζ).flip σ b' = 1 from hb, one_zpow]

/-- Adjoining the nth roots of one radicand gives a degree dividing $n$.
This is `kummerExtension_finrank` for the cyclic subgroup generated by that radicand;
Milne, *Fields and Galois Theory*, Theorem 5.30. -/
theorem kummerExtension_finrank_zpowers_dvd {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (hn : 0 < n) (b : Kˣ) :
    Module.finrank K (kummerExtension K n (Subgroup.zpowers b)) ∣ n := by
  have hB : (Subgroup.zpowers b).FG :=
    (Subgroup.fg_iff _).2 ⟨{b}, (Subgroup.zpowers_eq_closure b).symm, Set.finite_singleton _⟩
  let H := (powMonoidHom n : Kˣ →* Kˣ).range.comap (Subgroup.zpowers b).subtype
  have : IsCyclic (Subgroup.zpowers b ⧸ H) :=
    isCyclic_of_surjective (QuotientGroup.mk' H) (QuotientGroup.mk'_surjective H)
  rw [kummerExtension_finrank hζ hn hB, ← IsCyclic.exponent_eq_card]
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact ⟨y.val, rfl⟩

end SIC
