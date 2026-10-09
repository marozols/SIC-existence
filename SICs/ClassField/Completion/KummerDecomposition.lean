/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Frobenius.Basic
import SICs.ClassField.Completion.FiniteDecomposition
import SICs.ClassField.Completion.InfiniteDecomposition
import SICs.FieldTheory.Kummer.Basic

/-!
# Decomposition groups in radical extensions

Decomposition groups and Frobenius elements fix the roots of a radical extension whose radicands
are local powers, so a place at which every radicand is a local power splits completely.

This follows the local splitting step in the proof of Milne, *Class Field Theory*, version 4.03
(2020), Chapter VII, Proposition 6.10; the global power test it feeds is
`FrobeniusBasis.isPower_iff` in `SICs.ClassField.Frobenius.Basis`.

## The argument

Let a base-field element have an nth root in the upper extension. At a chosen place, a root in
the base completion differs from this root by a base-field root of unity, so every decomposition
automorphism, and in particular Frobenius, fixes the root. If every generating radicand is a
local power, the decomposition group fixes all the generators and is trivial. Its order equals
the local degree, so the extension splits at that place, at finite and at infinite places.
-/

noncomputable section

open IsDedekindDomain NumberField
open scoped NumberField SIC.FinitePlace SIC.InfinitePlace NumberField.LiesOver Pointwise

namespace SIC

/-! ### Roots in a completion

Degree-one local extensions do not change nth powers. Conversely, when $\mu_n$ lies in the
base field, a chosen local nth root forces every nth root in the upper field to be fixed by
the decomposition group, hence by Frobenius. -/

/-- An automorphism fixes an nth root whenever that radicand has a root in the base field.
This is the root-choice calculation shared by the finite and infinite decomposition groups. -/
private theorem algEquiv_fixes_root_of_exists_root {F E : Type*} [Field F] [Field E]
    [Algebra F E] {n : ℕ} {ζ a : F} (hζ : IsPrimitiveRoot ζ n) (hn : 0 < n)
    {x : E} (hx : x ^ n = algebraMap F E a) (ha : ∃ y : F, y ^ n = a)
    (σ : E ≃ₐ[F] E) : σ x = x := by
  obtain ⟨y, hy⟩ := ha
  have hxy : x ^ n = (algebraMap F E y) ^ n := by rw [← map_pow, hy, hx]
  obtain ⟨i, _, hi⟩ := exists_base_mul_of_pow_eq hζ hn hxy
  rw [hi, map_mul, σ.commutes, σ.commutes]

/-- A subgroup fixing every radical generator is trivial; used by both local splitting
lemmas, as in Milne, Chapter VII, proof of Proposition 6.10. -/
private theorem subgroup_eq_bot_of_fixes_radicals {K L : Type*} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] {n : ℕ} (B : Subgroup Kˣ)
    (hgen : IntermediateField.adjoin K {x : L | ∃ b : B,
      x ^ n = algebraMap K L (b.val : K)} = ⊤) (H : Subgroup (L ≃ₐ[K] L))
    (hfix : ∀ σ : H, ∀ b : B, ∀ x : L,
      x ^ n = algebraMap K L (b.val : K) → (σ : L ≃ₐ[K] L) x = x) : H = ⊥ := by
  have hle : IntermediateField.adjoin K {x : L | ∃ b : B,
      x ^ n = algebraMap K L (b.val : K)} ≤ IntermediateField.fixedField H := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro x ⟨b, hx⟩
    exact (IntermediateField.mem_fixedField_iff H x).mpr fun σ hσ => hfix ⟨σ, hσ⟩ b x hx
  have htop : IntermediateField.fixedField H = ⊤ := top_unique (hgen ▸ hle)
  rw [← IntermediateField.fixingSubgroup_fixedField H, htop,
    IntermediateField.fixingSubgroup_top]

/-! ### Splitting at finite places

Local roots make decomposition automorphisms fix radical generators; at finite places this also
forces Frobenius to fix them. -/

namespace FinitePlace
variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]
/-- At local degree one, an nth root in the global extension gives an nth root in the
base completion. This is the forward implication of Milne, Chapter VII, Lemma 6.3. -/
theorem exists_root_of_finrank_eq_one (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal]
    (h : Module.finrank (v.adicCompletion K) (w.adicCompletion L) = 1)
    {n : ℕ} {a : K} (ha : ∃ x : L, x ^ n = algebraMap K L a) :
    ∃ x : v.adicCompletion K, x ^ n = algebraMap K _ a := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp h).2
    (algebraMap L (w.adicCompletion L) x)
  refine ⟨y, ?_⟩
  apply (algebraMap (v.adicCompletion K) (w.adicCompletion L)).injective
  rw [map_pow, hy, ← map_pow, hx]
  exact (IsScalarTower.algebraMap_apply K L (w.adicCompletion L) a).symm.trans
    (IsScalarTower.algebraMap_apply K (v.adicCompletion K) (w.adicCompletion L) a)

/-- A local nth root forces every decomposition automorphism to fix any global nth root
when $\mu_n\subset K$. Milne, Chapter VII, proofs of Lemma 6.3 and Proposition 6.10. -/
theorem decomposition_fixes_root
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] {n : ℕ} {ζ a : K} (hζ : IsPrimitiveRoot ζ n) (hn : 0 < n)
    (σ : MulAction.stabilizer (L ≃ₐ[K] L) w)
    {x : L} (hx : x ^ n = algebraMap K L a)
    (ha : ∃ y : v.adicCompletion K, y ^ n = algebraMap K _ a) :
    (σ : L ≃ₐ[K] L) x = x := by
  apply (algebraMap L (w.adicCompletion L)).injective
  rw [← decompositionHom_algebraMap v w σ]
  apply algEquiv_fixes_root_of_exists_root
    (hζ.map_of_injective (algebraMap K (v.adicCompletion K)).injective) hn _ ha
    (decompositionHom v w σ)
  rw [← map_pow, hx, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

/-- A local nth root forces Frobenius to fix any global nth root when the base contains
$\mu_n$. This is the fixed-root step of Milne, Chapter VII, proof of Lemma 6.3. -/
theorem frobenius_fixes_root [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] {n : ℕ} {ζ a : K} (hζ : IsPrimitiveRoot ζ n) (hn : 0 < n)
    {g : L ≃ₐ[K] L} (hg : IsFrobeniusAt K L g v.asIdeal w.asIdeal)
    {x : L} (hx : x ^ n = algebraMap K L a)
    (ha : ∃ y : v.adicCompletion K, y ^ n = algebraMap K _ a) : g x = x := by
  have hD : g ∈ MulAction.stabilizer (L ≃ₐ[K] L) w := by
    rw [stabilizer_eq_stabilizer_asIdeal]
    exact hg.isArithFrobAt.mem_stabilizer
  exact decomposition_fixes_root v w hζ hn ⟨g, hD⟩ hx ha

/-- A finite place splits in a radical extension when all generating radicands are local
nth powers. Milne, *Class Field Theory*, Chapter VII, proof of Proposition 6.10, case $v\in S$. -/
theorem finrank_eq_one_of_local_roots [IsGalois K L]
    {n : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ n) (hn : 0 < n)
    (B : Subgroup Kˣ)
    (hgen : IntermediateField.adjoin K {x : L | ∃ b : B,
      x ^ n = algebraMap K L (b.val : K)} = ⊤)
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal]
    (hlocal : ∀ b : B, ∃ y : v.adicCompletion K,
      y ^ n = algebraMap K _ (b.val : K)) :
    Module.finrank (v.adicCompletion K) (w.adicCompletion L) = 1 := by
  rw [finrank_eq_card_stabilizer v w,
    subgroup_eq_bot_of_fixes_radicals B hgen _
      (fun σ b _ hx => decomposition_fixes_root v w hζ hn σ hx (hlocal b)), Subgroup.card_bot]

end FinitePlace

/-! ### Splitting at infinite places

The infinite decomposition group acts on the archimedean completion in the same way.
The algebraic root-choice and generator arguments above therefore prove splitting here too. -/

namespace InfinitePlace
variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

omit [NumberField K] [NumberField L] in
/-- An nth root in an infinite base completion makes every decomposition automorphism fix
the corresponding global radical. Milne, Chapter VII, proof of Proposition 6.10. -/
theorem decomposition_fixes_root
    (v : NumberField.InfinitePlace K) (w : NumberField.InfinitePlace L) [w.LiesOver v]
    {n : ℕ} {ζ a : K} (hζ : IsPrimitiveRoot ζ n) (hn : 0 < n)
    (σ : MulAction.stabilizer (L ≃ₐ[K] L) w)
    {x : L} (hx : x ^ n = algebraMap K L a)
    (ha : ∃ y : v.Completion, y ^ n = algebraMap K _ a) :
    (σ : L ≃ₐ[K] L) x = x := by
  apply (algebraMap L w.Completion).injective
  rw [← decompositionHom_algebraMap v w σ]
  apply algEquiv_fixes_root_of_exists_root
    (hζ.map_of_injective (algebraMap K v.Completion).injective) hn _ ha
    (decompositionHom v w σ)
  rw [← map_pow, hx, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

/-- An infinite place splits in a radical extension when all generating radicands are local
nth powers. Milne, *Class Field Theory*, Chapter VII, proof of Proposition 6.10, case $v\in S$. -/
theorem finrank_eq_one_of_local_roots [IsGalois K L]
    {n : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ n) (hn : 0 < n)
    (B : Subgroup Kˣ)
    (hgen : IntermediateField.adjoin K {x : L | ∃ b : B,
      x ^ n = algebraMap K L (b.val : K)} = ⊤)
    (v : NumberField.InfinitePlace K) (w : NumberField.InfinitePlace L) [w.LiesOver v]
    (hlocal : ∀ b : B, ∃ y : v.Completion,
      y ^ n = algebraMap K _ (b.val : K)) :
    Module.finrank v.Completion w.Completion = 1 := by
  rw [finrank_eq_card_stabilizer v w,
    subgroup_eq_bot_of_fixes_radicals B hgen _
      (fun σ b _ hx => decomposition_fixes_root v w hζ hn σ hx (hlocal b)), Subgroup.card_bot]

end InfinitePlace

end SIC
