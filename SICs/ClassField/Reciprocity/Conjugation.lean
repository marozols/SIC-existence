/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Reciprocity.GlobalArtinMap

/-!
# Conjugation of Artin maps

For a finite abelian extension `L/E` and an automorphism `τ` of `L` over a field `F` below a
normal `E/F`, with restriction $\sigma = \tau|_E$, conjugation by `τ` carries Frobenius elements,
the ideal Artin map, and the global Artin map at `x` to those at $\sigma(x)$:
$\operatorname{Art}_{L/E}(\sigma x) = \tau\operatorname{Art}_{L/E}(x)\tau^{-1}$.

This is the conjugation property of the reciprocity map, [83, Neukirch (1999), Chapter IV,
Proposition 6.4], in the form used by Childress, *Class Field Theory* (2009), Chapter VI, proof
of Proposition 1.3: $\sigma\tau\sigma^{-1} = \left(\frac{\sigma(b)}{E/K}\right)$. It supplies the
cyclic descent of `SICs.ClassField.Existence.Descent`.

## The argument

*Frobenius.* If `g` is the Frobenius element of a prime `Q` of `L` above `v`, then
$\tau g\tau^{-1}$ fixes `E` (`E/F` is normal) and satisfies
$\tau g\tau^{-1}(y) \equiv y^{N\sigma(v)} \pmod{\tau Q}$, because $N\sigma(v) = Nv$; so it is the
Frobenius element of $\tau Q$, a prime above $\sigma(v)$, which is unramified when `v` is.

*Ideal Artin map.* For a set `S` of primes containing the ramified ones and stable under `σ`, the
homomorphisms $J\mapsto\psi^S(\sigma J)$ and $J\mapsto\tau\psi^S(J)\tau^{-1}$ agree on every
prime (`FractionalIdeal.monoidHom_ext`), by the Frobenius case.

*Global Artin map.* Take a reciprocity modulus $\mathfrak m_1$ supported on the ramified places,
which `σ` permutes (`FinitePlace.mapEquiv_mem_ramifiedSet_iff`), and
$\mathfrak m = \mathfrak m_1\,\sigma^{-1}(\mathfrak m_1)$. A class `x` has a representative `y`
congruent modulo `m`; then `y` and $\sigma(y)$ are congruent modulo $\mathfrak m_1$
(`IdeleGroup.congr_mem_congruentSubgroup`), the fractional ideal of $\sigma(y)$ is $\sigma((y))$
(`IdeleGroup.toFractionalIdeal_congr`), and `globalArtin_mk` reduces the claim to the ideal case.
-/

noncomputable section

open IsDedekindDomain NumberField
open scoped nonZeroDivisors

namespace SIC

variable {F E L : Type*} [Field F] [Field E] [Field L] [NumberField E] [NumberField L]
  [Algebra F E] [Algebra E L] [Algebra F L] [IsScalarTower F E L] [Normal F E]
  [IsAbelianGalois E L]

/-! ### Frobenius elements and the ideal Artin map -/

/-- **Conjugation of Frobenius elements**: for an automorphism `τ` of `L` over `F` with
restriction $\sigma = \tau|_E$ and a prime `v` of `E` unramified in `L`,
$\operatorname{Frob}_{\sigma(v)} = \tau\operatorname{Frob}_v\tau^{-1}$. [83, Neukirch (1999),
Chapter IV, Proposition 6.4], whose conjugation diagram for the abstract reciprocity map is
formalized here for the Frobenius elements, and Childress, Chapter V, §1, the remark before
Proposition 1.1. -/
@[source "83, Chapter IV, Proposition 6.4, p. 302 (conjugation diagram, Frobenius elements)"]
theorem frobeniusAt_mapEquiv (τ : L ≃ₐ[F] L) {v : HeightOneSpectrum (𝓞 E)}
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), FinitePlace.below (K := E) w = v →
      w.asIdeal.ramificationIdx (𝓞 E) = 1) :
    (frobeniusAt L (FinitePlace.mapEquiv (τ.restrictNormal E).toRingEquiv v)).restrictScalars F =
      τ * (frobeniusAt L v).restrictScalars F * τ⁻¹ := by
  let σ := τ.restrictNormal E
  let w := FinitePlace.PrimeAbove.place (L := L) v (Classical.arbitrary _)
  let w' := FinitePlace.mapEquiv τ.toRingEquiv w
  have hF : IsFrobeniusAt E L (conjugateOver τ (frobeniusAt L v))
      (FinitePlace.mapEquiv σ.toRingEquiv v).asIdeal w'.asIdeal := by
    simpa only [w', σ, FinitePlace.mapEquiv_asIdeal] using
      (isFrobeniusAt_frobeniusAt v w.asIdeal).map_restrictNormal τ
  have hwram : w'.asIdeal.ramificationIdx (𝓞 E) = 1 := by
    rw [show w' = FinitePlace.mapEquiv τ.toRingEquiv w from rfl,
      FinitePlace.ramificationIdx_mapEquiv]
    exact hv w (FinitePlace.PrimeAbove.below_place v (Classical.arbitrary _))
  have hEq := hF.eq_frobeniusAt hwram
  exact (congrArg (fun g : L ≃ₐ[E] L => g.restrictScalars F) hEq).symm.trans
    (conjugateOver_restrictScalars τ (frobeniusAt L v))

/-- **Conjugation of the ideal Artin map**: for a set `S` of primes of `E` containing those
ramified in `L` and stable under $\sigma = \tau|_E$,
$\psi^S_{L/E}(\sigma J) = \tau\,\psi^S_{L/E}(J)\,\tau^{-1}$. [83, Neukirch (1999), Chapter IV,
Proposition 6.4], whose conjugation diagram for the abstract reciprocity map is formalized here
for the ideal Artin map. -/
@[source "83, Chapter IV, Proposition 6.4, p. 302 (conjugation diagram, ideal Artin map)"]
theorem artinMap_congr (τ : L ≃ₐ[F] L) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : FinitePlace.ramifiedSet E L ⊆ S)
    (hσS : ∀ v, FinitePlace.mapEquiv (τ.restrictNormal E).toRingEquiv v ∈ S ↔ v ∈ S)
    (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) :
    (artinMap L S (FractionalIdeal.congr (τ.restrictNormal E).toRingEquiv J)).restrictScalars F =
      τ * (artinMap L S J).restrictScalars F * τ⁻¹ := by
  have hhom :
      (AlgEquiv.restrictScalarsHom F).comp
          ((artinMap L S).comp (FractionalIdeal.congr (τ.restrictNormal E).toRingEquiv)) =
        (MulAut.conj τ).toMonoidHom.comp
          ((AlgEquiv.restrictScalarsHom F).comp (artinMap L S)) := by
    apply FractionalIdeal.monoidHom_ext
    intro v
    change (artinMap L S
      (FractionalIdeal.congr (τ.restrictNormal E).toRingEquiv
        (primeFractionalIdeal E v))).restrictScalars F =
      τ * (artinMap L S (primeFractionalIdeal E v)).restrictScalars F * τ⁻¹
    rw [FractionalIdeal.congr_primeFractionalIdeal]
    by_cases hv : v ∈ S
    · have hv' := (hσS v).mpr hv
      rw [artinMap_primeFractionalIdeal_of_mem hv',
        artinMap_primeFractionalIdeal_of_mem hv]
      have hone : (1 : L ≃ₐ[E] L).restrictScalars F = 1 :=
        (AlgEquiv.restrictScalarsHom F : (L ≃ₐ[E] L) →* (L ≃ₐ[F] L)).map_one
      rw [hone, mul_one, mul_inv_cancel]
    · have hv' : FinitePlace.mapEquiv (τ.restrictNormal E).toRingEquiv v ∉ S :=
        fun h => hv ((hσS v).mp h)
      rw [artinMap_primeFractionalIdeal_of_notMem hv',
        artinMap_primeFractionalIdeal_of_notMem hv]
      exact frobeniusAt_mapEquiv τ (fun w hw =>
        FinitePlace.ramificationIdx_eq_one_of_ramifiedSet_subset hS w (hw ▸ hv))
  exact congrArg (fun f : (FractionalIdeal (𝓞 E)⁰ E)ˣ →* (L ≃ₐ[F] L) => f J) hhom

/-! ### The global Artin map -/

/-- **Conjugation of the global Artin map**: for an automorphism `τ` of `L` over `F` with
restriction $\sigma = \tau|_E$ to the normal subextension `E`,
$\operatorname{Art}_{L/E}(\sigma x) = \tau\operatorname{Art}_{L/E}(x)\tau^{-1}$.
[83, Neukirch (1999), Chapter IV, Proposition 6.4], whose conjugation diagram for the abstract
reciprocity map is formalized here for the global Artin map; Childress, *Class Field Theory*,
Chapter VI, proof of Proposition 1.3. -/
@[source "83, Chapter IV, Proposition 6.4, p. 302 (conjugation diagram, global Artin map)"]
theorem globalArtin_restrictNormal_smul (τ : L ≃ₐ[F] L)
    (x : NumberField.IdeleClassGroup (𝓞 E) E) :
    (globalArtin L (τ.restrictNormal E • x)).restrictScalars F =
      τ * (globalArtin L x).restrictScalars F * τ⁻¹ := by
  let σ := τ.restrictNormal E
  let e := RingOfIntegers.mapRingEquiv σ.toRingEquiv
  obtain ⟨m₁, hm₁, hS⟩ := exists_isReciprocityModulus (K := E) (L := L)
  let m := m₁ * m₁.comap e
  have hcomap : m₁.comap e ≠ ⊥ := by
    rw [← Ideal.map_symm e]
    exact (Ideal.map_eq_bot_iff_of_injective e.symm.injective).not.mpr hm₁.ne_bot
  have hm : m ≠ ⊥ := by
    change m₁ * m₁.comap e ≠ ⊥
    rw [ne_eq, Ideal.mul_eq_bot, not_or]
    exact ⟨hm₁.ne_bot, hcomap⟩
  have hmle : m ≤ m₁ := Ideal.mul_le_left
  have hmap : m.map e = m₁.map e * m₁ := by
    change (m₁ * m₁.comap e).map e = m₁.map e * m₁
    have hback : (m₁.comap e).comap e.symm = m₁ := by
      exact Ideal.comap_of_equiv e.symm
    rw [Ideal.map_mul,
      show (m₁.comap e).map e = (m₁.comap e).comap e.symm from
        Ideal.map_comap_of_equiv e,
      hback]
  have hmaple : m.map e ≤ m₁ := by rw [hmap]; exact Ideal.mul_le_right
  have hmapbot : m.map e ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective e.injective).not.mpr hm
  obtain ⟨y, hy, hclass⟩ := IdeleGroup.exists_mem_congruentSubgroup_mk_eq Set.univ m x
  have hy₁ : y ∈ IdeleGroup.congruentSubgroup Set.univ m₁ :=
    IdeleGroup.congruentSubgroup_mono Set.univ hm hmle hy
  have hyσ : σ • y ∈ IdeleGroup.congruentSubgroup Set.univ m₁ := by
    rw [IdeleGroup.smul_def]
    have hcongr : IdeleGroup.congr σ.toRingEquiv y ∈
        IdeleGroup.congruentSubgroup Set.univ (m.map e) := by
      simpa only [Set.image_univ, Equiv.range_eq_univ] using
        IdeleGroup.congr_mem_congruentSubgroup σ.toRingEquiv Set.univ hy
    exact IdeleGroup.congruentSubgroup_mono Set.univ hmapbot hmaple
      hcongr
  rw [← hclass, IdeleClassGroup.smul_mk, globalArtin_mk hm₁ hyσ,
    globalArtin_mk hm₁ hy₁, IdeleGroup.smul_def,
    IdeleGroup.toFractionalIdeal_congr]
  apply artinMap_congr τ (FinitePlace.modulusSupport m₁) hm₁.unramified
  · intro v
    rw [hS]
    exact FinitePlace.mapEquiv_mem_ramifiedSet_iff τ v

end SIC
