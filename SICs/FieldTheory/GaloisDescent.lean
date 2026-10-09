/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Norm.Transitivity

/-!
# Galois descent through a group of automorphisms

Criteria for a group acting by automorphisms of a finite extension `E/F` to be its Galois group,
and Galois descent and the norm formula through such a group; the units of `E` fixed by
$\operatorname{Gal}(E/F)$ are those of `F`.

These are the counting steps of Serre, *Local Fields*, Chapter II, §3, Corollary 4, used for the
decomposition groups of `SICs.ClassField.Completion.FiniteDecomposition` and
`SICs.ClassField.Completion.InfiniteDecomposition`, and the descent of $L^\times$ used for the Tate
groups of `SICs.GroupCohomology.Multiplicative` and the idèle classes of
`SICs.ClassField.Ideles.Invariants`.

## The argument

An injective homomorphism $\varphi : H \to \operatorname{Aut}(E/F)$ gives
$|H| \le |\operatorname{Aut}(E/F)| \le [E : F]$ (Artin's bound); when $|H| = [E : F]$ both
inequalities are equalities, so `φ` is bijective and $|\operatorname{Aut}(E/F)| = [E : F]$, which
characterizes Galois extensions. Galois descent and the formula
$N_{E/F}(x) = \prod_\tau \tau x$ for $\tau \in \operatorname{Gal}(E/F)$ then hold with `τ`
replaced by `φ h`, `h ∈ H`. A unit of `E` whose value lies in `F` is the image of a unit of `F`,
since its preimage is nonzero; so the units fixed by $\operatorname{Gal}(E/F)$ are those of `F`.
-/

namespace SIC

/-! ### Automorphism groups of the right order -/

section Galois

variable {F E H : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [Group H]

/-- An injective homomorphism from a group of order $[E : F]$ into $\operatorname{Aut}(E/F)$ is
bijective. -/
theorem bijective_of_injective_of_card_eq_finrank (φ : H →* (E ≃ₐ[F] E))
    (hφ : Function.Injective φ) (hcard : Nat.card H = Module.finrank F E) :
    Function.Bijective φ := by
  have hle : Nat.card (E ≃ₐ[F] E) ≤ Nat.card H := by
    rw [hcard]
    exact (Nat.card_le_card_of_injective _ AlgEquiv.coe_toAlgHom_injective).trans
      (card_algHom_le_finrank F E E)
  exact hφ.bijective_of_nat_card_le hle

/-- If an injective homomorphism from a group of order $[E : F]$ into $\operatorname{Aut}(E/F)$
exists, then $E/F$ is Galois. -/
theorem isGalois_of_injective_of_card_eq_finrank (φ : H →* (E ≃ₐ[F] E))
    (hφ : Function.Injective φ) (hcard : Nat.card H = Module.finrank F E) : IsGalois F E := by
  apply IsGalois.of_card_aut_eq_finrank F E
  exact (Nat.card_eq_of_bijective φ
    (bijective_of_injective_of_card_eq_finrank φ hφ hcard)).symm.trans hcard

/-- Galois descent through a surjection onto $\operatorname{Gal}(E/F)$: `x ∈ E` lies in `F` exactly
when every `φ h` fixes it. -/
theorem mem_range_algebraMap_iff_of_surjective [IsGalois F E] (φ : H →* (E ≃ₐ[F] E))
    (hφ : Function.Surjective φ) (x : E) :
    x ∈ (algebraMap F E).range ↔ ∀ h, φ h x = x := by
  change x ∈ Set.range (algebraMap F E) ↔ ∀ h, φ h x = x
  rw [← IntermediateField.mem_bot, IsGalois.mem_bot_iff_fixed]
  constructor
  · intro hx h
    exact hx (φ h)
  · intro hx σ
    obtain ⟨h, rfl⟩ := hφ σ
    exact hx h

/-- The norm through a bijection onto $\operatorname{Gal}(E/F)$:
$N_{E/F}(x) = \prod_{h \in H} \varphi(h)(x)$. -/
theorem algebraMap_norm_eq_prod_of_bijective [IsGalois F E] [Fintype H]
    (φ : H →* (E ≃ₐ[F] E)) (hφ : Function.Bijective φ) (x : E) :
    algebraMap F E (Algebra.norm F x) = ∏ h : H, φ h x := by
  rw [Algebra.norm_eq_prod_automorphisms]
  exact (Fintype.prod_bijective φ hφ (fun h ↦ φ h x) (fun σ ↦ σ x)
    (fun _ ↦ rfl)).symm

end Galois

/-! ### Units -/

section Units

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- A unit of `E` comes from a unit of `F` exactly when its value lies in `F`. -/
theorem mem_range_unitsMap_iff (x : Eˣ) :
    x ∈ (Units.map (algebraMap F E : F →* E)).range ↔ (x : E) ∈ (algebraMap F E).range := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, rfl⟩
  · rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := by
      intro h
      have : (x : E) = 0 := by simpa [h] using hy.symm
      exact x.ne_zero this
    refine ⟨Units.mk0 y hy0, Units.ext ?_⟩
    simpa using hy

variable [FiniteDimensional F E]

/-- The fixed points of $E^\times$ under $\operatorname{Gal}(E/F)$ are $F^\times$. -/
theorem range_unitsMap_algebraMap [IsGalois F E] :
    (Units.map (algebraMap F E : F →* E)).range = FixedPoints.subgroup (E ≃ₐ[F] E) Eˣ := by
  apply Subgroup.ext
  intro x
  rw [FixedPoints.mem_subgroup]
  rw [mem_range_unitsMap_iff]
  constructor
  · rintro ⟨y, hy⟩ σ
    apply Units.ext
    change σ (x : E) = (x : E)
    simpa only [hy] using σ.commutes y
  · intro hx
    exact (IsGalois.mem_range_algebraMap_iff_fixed (x : E)).2
      (fun σ => congrArg Units.val (hx σ))

end Units

end SIC
