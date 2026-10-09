/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Reciprocity.GlobalArtinMap

/-!
# The Artin map at an infinite place

For a finite abelian extension `L/K` and an infinite place `v` of `K`, the global Artin map
sends the image of $K_v^\times$ in the idèle class group into the decomposition group of every
place `w` of `L` above `v`: its value is trivial or complex conjugation at an embedding defining
`w`.

This is the weak form of the reciprocity law at an infinite place, [83, Neukirch (1999),
Chapter VI, Proposition 5.6], which also identifies the value at a negative element with complex
conjugation when `w` is complex; that half is not needed. It
supplies the real-place Artin law for the sign classes of
`SICs.ClassField.RayClassField.SignClasses`, in idèlic form.

## The argument

Let `E` be the decomposition field of `w`, the fixed field of its stabilizer; it is Galois over
`K` since `L/K` is abelian. The place $w_E$ of `E` below `w` is unramified over `v`: this is
automatic if `v` is complex; if `v` is real, the embedding defining `w` is real on `E`, since
complex conjugation at `w`, when needed, fixes `E`. Thus $[E_{w_E}:K_v]=1$, and the local norm
$E_{w_E}^\times\to K_v^\times$ is surjective
(`InfinitePlace.localNorm_surjective_of_finrank_eq_one`): $x$ is the local norm of some $y$,
and the class of $x$ is the norm of the class of $y$ (`IdeleClassGroup.norm_ofCompletion`).
So $\operatorname{Art}_{E/K}(x)=1$ (`globalArtin_norm`), and by restriction
(`globalArtin_restrictNormal`) $\operatorname{Art}_{L/K}(x)$ fixes `E`, that is, it lies in the
stabilizer of `w`.
-/

noncomputable section

namespace SIC

open NumberField
open scoped NumberField.LiesOver

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L]

/-- **The Artin map at an infinite place lies in the decomposition group**: for a finite abelian
extension `L/K`, an infinite place `v` of `K`, a place `w` of `L` above it, and
$x\in K_v^\times$, $\operatorname{Art}_{L/K}(x)$ stabilizes `w`. [83, Neukirch (1999), Chapter VI,
Proposition 5.6], weak form: the source's commutative diagram identifies the image with the local
norm residue symbol at `v`, of which only membership in the decomposition group is formalized. -/
@[source "83, Chapter VI, Proposition 5.6, p. 391 (infinite place, decomposition group)"]
theorem globalArtin_ofCompletion_mem_stabilizer [IsAbelianGalois K L] (v : InfinitePlace K)
    (w : InfinitePlace L) [w.LiesOver v] (x : v.Completionˣ) :
    globalArtin L (NumberField.IdeleClassGroup.ofCompletion (𝓞 K) K v x) ∈
      MulAction.stabilizer (L ≃ₐ[K] L) w := by
  let D := MulAction.stabilizer (L ≃ₐ[K] L) w
  let E := IntermediateField.fixedField D
  let u := InfinitePlace.below (K := E) w
  have hu : u.LiesOver v := InfinitePlace.liesOver_below_of_liesOver (L := E) v w
  let _ : u.LiesOver v := hu
  have hunram : u.IsUnramified K :=
    InfinitePlace.isUnramified_fixedField_stabilizer v w
  have hdegree : Module.finrank v.Completion u.Completion = 1 := hunram.finrank_eq_one v
  have hnorm := IdeleClassGroup.range_ofCompletion_le_range_norm v u hdegree
  have hArtE : globalArtin E (NumberField.IdeleClassGroup.ofCompletion (𝓞 K) K v x) = 1 := by
    obtain ⟨y, hy⟩ := hnorm ⟨x, rfl⟩
    rw [← hy]
    exact globalArtin_norm y
  have hres : (globalArtin L
      (NumberField.IdeleClassGroup.ofCompletion (𝓞 K) K v x)).restrictNormal E = 1 := by
    rw [globalArtin_restrictNormal (L := L) E, hArtE]
  have hfix : globalArtin L (NumberField.IdeleClassGroup.ofCompletion (𝓞 K) K v x) ∈
      E.fixingSubgroup :=
    (IntermediateField.mem_fixingSubgroup_iff E _).mpr
      ((AlgEquiv.restrictNormal_eq_one_iff E _).mp hres)
  change globalArtin L (NumberField.IdeleClassGroup.ofCompletion (𝓞 K) K v x) ∈ D
  rw [← IntermediateField.fixingSubgroup_fixedField D]
  exact hfix

/-- **The Artin map at an infinite place is trivial or complex conjugation**: for a finite
abelian extension `L/K`, an embedding $\rho:L\to\mathbb C$ above an infinite place `v` of `K`,
and $x\in K_v^\times$, $\operatorname{Art}_{L/K}(x)$ is $1$ or complex conjugation at $\rho$.
[83, Neukirch (1999), Chapter VI, Proposition 5.6], weak form: the source's commutative diagram
identifies the image with the local norm residue symbol at `v`, of which only the alternative
between `1` and complex conjugation is formalized. -/
@[source "83, Chapter VI, Proposition 5.6, p. 391 (infinite place, weak form)"]
theorem globalArtin_ofCompletion_eq_one_or_isConj [IsAbelianGalois K L] (v : InfinitePlace K)
    (ρ : L →+* ℂ) [(InfinitePlace.mk ρ).LiesOver v] (x : v.Completionˣ) :
    globalArtin L (NumberField.IdeleClassGroup.ofCompletion (𝓞 K) K v x) = 1 ∨
      ComplexEmbedding.IsConj ρ
        (globalArtin L (NumberField.IdeleClassGroup.ofCompletion (𝓞 K) K v x)) := by
  exact (InfinitePlace.mem_stabilizer_mk_iff ρ _).mp
    (globalArtin_ofCompletion_mem_stabilizer v (InfinitePlace.mk ρ) x)

end SIC

end
