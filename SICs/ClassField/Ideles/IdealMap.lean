/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Ideles.Basic
import SICs.DedekindDomain.FractionalIdeals
import SICs.ClassField.Completion.FiniteConjugation
import SICs.ClassField.Local.UnitGroups
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.ClassGroup.Basic

/-!
# The fractional-ideal map on idèles

The homomorphism from finite adèle units, idèles, and idèle classes to fractional ideals and
the ordinary ideal class group, with its principal-idèle and prime-uniformizer formulas, and
transport of fractional ideals under number-field isomorphisms.

## The argument

The general prime factorization and the subgroup $I^S$ of ideals prime to a finite set are in
`SICs.DedekindDomain.FractionalIdeals`. The chosen local uniformizers are in
`SICs.ClassField.Local.UnitGroups`.

At a finite place `v`, a nonzero local component `x_v` has additive order
`-log(v(x_v))`.  The finite adèle is integral and invertible at all but finitely many places, so
the product `∏_v v ^ (-log(v(x_v)))` is a well-defined nonzero fractional ideal and is
multiplicative.  The factorization theorem for fractional ideals identifies the image of a
principal idèle with its principal fractional ideal, so the composite with the ordinary class
group kills principal idèles and descends to the idèle class group.  A local element of valuation
`exp(-1)` contributes exactly the prime ideal `v`; this fixes the orientation needed by the global
Artin map at uniformizer idèles.

The order of the fractional ideal of an idèle at `v` is `-log(v(x_v))`, so its ideal is trivial
exactly when every finite component has valuation `1`.  Conversely, fixing a uniformizer `ϖ_v`
of every finite completion, the idèle with finite components `ϖ_v ^ ord_v(J)` and infinite
components `1` has fractional ideal `J`.  Since the orders of `J` vanish at almost every place,
this idèle is restricted, and the construction is multiplicative because orders add.  It is the
representative idèle used to compare idèle classes with ideal classes in the corrected Bonn
Lectures, Chapter III, Proposition 9.3.

This is the ideal map in Milne, *Class Field Theory*, version 4.03 (2020), Chapter V, §4 and
the corrected Bonn Lectures, Chapter III, §9. A number-field isomorphism permutes the primes;
lifting that permutation gives `FractionalIdeal.congr`, whose order at each transported prime is
the original order.
-/

noncomputable section

open Filter IsDedekindDomain NumberField
open scoped BigOperators nonZeroDivisors NumberField NumberField.AdeleRing RestrictedProduct

namespace SIC

universe u

/-! ### Finite adèle units -/

namespace FiniteAdeleRing

variable {K : Type u} [Field K] [NumberField K]

/-- Every local valuation of a finite adèle unit is nonzero. -/
private theorem valued_ne_zero
    (x : (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) : Valued.v (x.1 v) ≠ 0 := by
  exact (Valuation.ne_zero_iff (Valued.v : Valuation (v.adicCompletion K) _)).2
    ((RestrictedProduct.unitsEquiv _ x v).ne_zero)

/-- The prime powers defining the fractional ideal of a finite adèle unit are finitely
supported. -/
private theorem hasFiniteMulSupport_primePower
    (x : (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ) :
    (fun v : HeightOneSpectrum (𝓞 K) ↦
      (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
        (-WithZero.log (Valued.v (x.1 v)))).HasFiniteMulSupport := by
  apply (IsDedekindDomain.FiniteAdeleRing.hasFiniteMulSupport_valued x).subset
  intro v hv
  rw [Function.mem_mulSupport] at hv ⊢
  intro hval
  apply hv
  rw [hval, WithZero.log_one, neg_zero, zpow_zero]

/-- The fractional ideal attached to a finite adèle unit: its exponent at `v` is
`-log(v(x_v))`. [Milne, *Class Field Theory*, V.4.] -/
def toFractionalIdeal :
    (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ →*
      (FractionalIdeal (𝓞 K)⁰ K)ˣ := by
  refine
    { toFun := fun x ↦ Units.mk0
        (∏ᶠ v : HeightOneSpectrum (𝓞 K),
          (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
            (-WithZero.log (Valued.v (x.1 v))))
        (finprod_ne_zero fun v ↦
          zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot))
      map_one' := ?_
      map_mul' := ?_ }
  · apply Units.ext
    change (∏ᶠ v : HeightOneSpectrum (𝓞 K),
      (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
        (-WithZero.log (Valued.v ((1 :
          (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ).1 v)))) =
      (1 : FractionalIdeal (𝓞 K)⁰ K)
    calc
      _ = ∏ᶠ _v : HeightOneSpectrum (𝓞 K),
          (1 : FractionalIdeal (𝓞 K)⁰ K) := by
        apply finprod_congr
        intro v
        change (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
          (-WithZero.log (Valued.v (1 : v.adicCompletion K))) = 1
        rw [map_one, WithZero.log_one, neg_zero, zpow_zero]
      _ = 1 := finprod_one
  · intro x y
    apply Units.ext
    change (∏ᶠ v : HeightOneSpectrum (𝓞 K),
      (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
        (-WithZero.log (Valued.v ((x * y).1 v)))) =
      (∏ᶠ v : HeightOneSpectrum (𝓞 K),
        (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
          (-WithZero.log (Valued.v (x.1 v)))) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K),
        (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
          (-WithZero.log (Valued.v (y.1 v)))
    rw [← finprod_mul_distrib (hasFiniteMulSupport_primePower x)
      (hasFiniteMulSupport_primePower y)]
    apply finprod_congr
    intro v
    change (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
        (-WithZero.log (Valued.v (x.1 v * y.1 v))) = _
    rw [map_mul, WithZero.log_mul (valued_ne_zero x v) (valued_ne_zero y v)]
    rw [neg_add, zpow_add₀ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)]

/-- The underlying fractional ideal of `toFractionalIdeal x` is the finite product of prime
powers with exponents `-log(v(x_v))`. -/
@[simp]
theorem coe_toFractionalIdeal (x :
    (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ) :
    ((toFractionalIdeal x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K),
        (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
          (-WithZero.log (Valued.v (x.1 v))) := by
  rfl

end FiniteAdeleRing

/-! ### Idèles and principal idèles -/

namespace IdeleGroup

variable {K : Type u} [Field K] [NumberField K]

/-- The fractional ideal attached to an idèle, obtained from its finite adèle component. -/
def toFractionalIdeal :
    NumberField.IdeleGroup (𝓞 K) K →* (FractionalIdeal (𝓞 K)⁰ K)ˣ := by
  exact FiniteAdeleRing.toFractionalIdeal.comp <| Units.map <|
    MonoidHom.snd (NumberField.InfiniteAdeleRing K)
      (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)

/-- On an idèle, the underlying fractional ideal is the product of the prime powers determined
by its finite components. -/
@[simp]
theorem coe_toFractionalIdeal (x : NumberField.IdeleGroup (𝓞 K) K) :
    ((toFractionalIdeal x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K),
        (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
          (-WithZero.log (Valued.v
            ((finiteComponent K v x : (v.adicCompletion K)ˣ) : v.adicCompletion K))) := by
  rw [toFractionalIdeal, MonoidHom.comp_apply, FiniteAdeleRing.coe_toFractionalIdeal]
  rfl

/-- A principal idèle maps to its principal fractional ideal. -/
theorem coe_toFractionalIdeal_unitEmbedding (x : Kˣ) :
    ((toFractionalIdeal (NumberField.IdeleGroup.unitEmbedding (𝓞 K) K x) :
        (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) := by
  rw [coe_toFractionalIdeal]
  calc
    _ = ∏ᶠ v : HeightOneSpectrum (𝓞 K),
        (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
          FractionalIdeal.count K v
            (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)) := by
      apply finprod_congr
      intro v
      congr 1
      rw [finiteComponent_unitEmbedding]
      change -WithZero.log (Valued.v ((x : K) : v.adicCompletion K)) = _
      rw [v.valuedAdicCompletion_eq_valuation']
      exact (FractionalIdeal.count_spanSingleton v (x : K) x.ne_zero).symm
    _ = _ := FractionalIdeal.finprod_heightOneSpectrum_factorization' K
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr x.ne_zero)

/-- A principal idèle maps to the principal fractional ideal of its generator. -/
theorem toFractionalIdeal_unitEmbedding (x : Kˣ) :
    toFractionalIdeal (NumberField.IdeleGroup.unitEmbedding (𝓞 K) K x) =
      toPrincipalIdeal (𝓞 K) K x := by
  apply Units.ext
  rw [coe_toFractionalIdeal_unitEmbedding, coe_toPrincipalIdeal]

/-- The order at `v` of the fractional ideal of an idèle is `-log(v(x_v))`. -/
theorem count_toFractionalIdeal (x : NumberField.IdeleGroup (𝓞 K) K)
    (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v
        ((toFractionalIdeal x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      -WithZero.log (Valued.v
        ((finiteComponent K v x : (v.adicCompletion K)ˣ) : v.adicCompletion K)) := by
  rw [coe_toFractionalIdeal]
  apply FractionalIdeal.count_finprod
  filter_upwards [((componentsEquiv K x).2).2] with w hw
  have hw' : Valued.v
      ((finiteComponent K w x : (w.adicCompletion K)ˣ) : w.adicCompletion K) = 1 :=
    IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hw
  rw [hw', WithZero.log_one, neg_zero]

/-- An idèle has trivial fractional ideal exactly when every finite component has valuation
`1`. -/
theorem toFractionalIdeal_eq_one_iff (x : NumberField.IdeleGroup (𝓞 K) K) :
    toFractionalIdeal x = 1 ↔
      ∀ v : HeightOneSpectrum (𝓞 K),
        Valued.v ((finiteComponent K v x : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
  constructor
  · intro hx v
    have hcount := count_toFractionalIdeal x v
    rw [hx, Units.val_one, FractionalIdeal.count_one] at hcount
    have hlog : WithZero.log (Valued.v
        ((finiteComponent K v x : (v.adicCompletion K)ˣ) : v.adicCompletion K)) = 0 := by
      omega
    have hne : Valued.v
        ((finiteComponent K v x : (v.adicCompletion K)ˣ) : v.adicCompletion K) ≠ 0 :=
      (Valuation.ne_zero_iff (Valued.v : Valuation (v.adicCompletion K) _)).2
        (finiteComponent K v x).ne_zero
    calc
      _ = WithZero.exp (WithZero.log
          (Valued.v ((finiteComponent K v x : (v.adicCompletion K)ˣ) :
            v.adicCompletion K))) := (WithZero.exp_log hne).symm
      _ = 1 := by rw [hlog, WithZero.exp_zero]
  · intro hx
    apply Units.ext
    rw [coe_toFractionalIdeal]
    calc
      (∏ᶠ v : HeightOneSpectrum (𝓞 K),
        (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
          (-WithZero.log (Valued.v
            ((finiteComponent K v x : (v.adicCompletion K)ˣ) : v.adicCompletion K)))) =
          ∏ᶠ _v : HeightOneSpectrum (𝓞 K), (1 : FractionalIdeal (𝓞 K)⁰ K) := by
            apply finprod_congr
            intro v
            rw [hx v, WithZero.log_one, neg_zero, zpow_zero]
      _ = 1 := finprod_one

/-- The ordinary ideal class of an idèle. -/
def idealClass : NumberField.IdeleGroup (𝓞 K) K →* ClassGroup (𝓞 K) :=
  (ClassGroup.mk K).comp toFractionalIdeal

/-- Principal idèles have trivial ordinary ideal class. -/
@[simp]
theorem idealClass_unitEmbedding (x : Kˣ) :
    idealClass (NumberField.IdeleGroup.unitEmbedding (𝓞 K) K x) = 1 := by
  rw [idealClass, MonoidHom.comp_apply, ClassGroup.mk_eq_one_iff,
    FractionalIdeal.isPrincipal_iff]
  exact ⟨x, coe_toFractionalIdeal_unitEmbedding x⟩

/-- A local idèle supported at `v` maps to the corresponding power of `v`. -/
theorem coe_toFractionalIdeal_ofAdicCompletion
    (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    ((toFractionalIdeal (NumberField.IdeleGroup.ofAdicCompletion (𝓞 K) K v x) :
        (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
        (-WithZero.log (Valued.v (x : v.adicCompletion K))) := by
  rw [coe_toFractionalIdeal]
  calc
    _ = (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
        (-WithZero.log (Valued.v
          ((finiteComponent K v
            (NumberField.IdeleGroup.ofAdicCompletion (𝓞 K) K v x) :
              (v.adicCompletion K)ˣ) : v.adicCompletion K))) := by
      apply finprod_eq_single
      intro w hw
      rw [finiteComponent_ofAdicCompletion_of_ne K v w hw x, Units.val_one,
        map_one, WithZero.log_one, neg_zero, zpow_zero]
    _ = _ := by rw [finiteComponent_ofAdicCompletion_self K]

/-- **Prime-uniformizer orientation.** A local element of valuation `exp(-1)` maps to the prime
ideal `v`, not its inverse. [Neukirch, *The Bonn Lectures*, corrected edition (2015),
Chapter III, Proposition 9.3.] -/
theorem coe_toFractionalIdeal_ofAdicCompletion_uniformizer
    (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ)
    (hx : Valued.v (x : v.adicCompletion K) = WithZero.exp (-1 : ℤ)) :
    ((toFractionalIdeal (NumberField.IdeleGroup.ofAdicCompletion (𝓞 K) K v x) :
        (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [coe_toFractionalIdeal_ofAdicCompletion, hx, WithZero.log_exp, neg_neg, zpow_one]

end IdeleGroup

/-! ### Uniformizer idèles

The idèle of chosen uniformizer powers attached to a fractional ideal `J`: its component at a
finite place `v` is `ϖ_v ^ ord_v(J)` and its infinite components are `1`.  It is a section of the
fractional-ideal map. -/

namespace IdeleGroup

variable {K : Type u} [Field K] [NumberField K]

/-- The finite local idèle of uniformizer powers attached to a fractional ideal; used by
`ofFractionalIdeal`. -/
private def finiteLocalOfFractionalIdeal :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ →* FiniteLocalIdele K where
  toFun J := ⟨fun v ↦ FinitePlace.uniformizer v ^
      FractionalIdeal.count K v ((J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K),
    by
      filter_upwards [FractionalIdeal.finite_factors (J : FractionalIdeal (𝓞 K)⁰ K)]
        with v hv
      simp [hv]⟩
  map_one' := by
    apply _root_.RestrictedProduct.ext
    intro v
    change FinitePlace.uniformizer v ^
      FractionalIdeal.count K v (1 : FractionalIdeal (𝓞 K)⁰ K) = 1
    rw [FractionalIdeal.count_one, zpow_zero]
  map_mul' := by
    intro J J'
    apply _root_.RestrictedProduct.ext
    intro v
    change FinitePlace.uniformizer v ^
        FractionalIdeal.count K v ((J * J' : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
          FractionalIdeal (𝓞 K)⁰ K) =
      FinitePlace.uniformizer v ^ FractionalIdeal.count K v
          (J : FractionalIdeal (𝓞 K)⁰ K) *
        FinitePlace.uniformizer v ^ FractionalIdeal.count K v
          (J' : FractionalIdeal (𝓞 K)⁰ K)
    rw [Units.val_mul, FractionalIdeal.count_mul K v J.ne_zero J'.ne_zero, zpow_add]

/-- **The uniformizer idèle of a fractional ideal**: finite components `ϖ_v ^ ord_v(J)` and
infinite components `1`, the representative idèle of the corrected Bonn Lectures, Chapter III,
Proposition 9.3, proof. -/
def ofFractionalIdeal :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ →* NumberField.IdeleGroup (𝓞 K) K :=
  (componentsEquiv K).symm.toMonoidHom.comp
    ((MonoidHom.inr (InfiniteLocalIdele K) (FiniteLocalIdele K)).comp
      finiteLocalOfFractionalIdeal)

/-- The finite component of a uniformizer idèle at `v` is `ϖ_v ^ ord_v(J)`. -/
@[simp]
theorem finiteComponent_ofFractionalIdeal (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    finiteComponent K v (ofFractionalIdeal J) =
      FinitePlace.uniformizer v ^
        FractionalIdeal.count K v ((J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
          FractionalIdeal (𝓞 K)⁰ K) := by
  rfl

/-- Every infinite component of a uniformizer idèle is `1`. -/
@[simp]
theorem infiniteComponent_ofFractionalIdeal (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (w : InfinitePlace K) : infiniteComponent K w (ofFractionalIdeal J) = 1 := by
  simp [ofFractionalIdeal, infiniteComponent_apply]

/-- **The uniformizer idèle is a section of the fractional-ideal map**: its fractional ideal is
`J`. -/
@[simp]
theorem toFractionalIdeal_ofFractionalIdeal (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    toFractionalIdeal (ofFractionalIdeal J) = J := by
  apply Units.ext
  rw [coe_toFractionalIdeal]
  calc
    (∏ᶠ v : HeightOneSpectrum (𝓞 K),
      (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
        (-WithZero.log (Valued.v
          ((finiteComponent K v (ofFractionalIdeal J) : (v.adicCompletion K)ˣ) :
            v.adicCompletion K)))) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K),
        (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
          FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K) := by
      apply finprod_congr
      intro v
      congr 1
      rw [finiteComponent_ofFractionalIdeal]
      rw [Units.val_zpow_eq_zpow_val, map_zpow₀, FinitePlace.valued_uniformizer,
        WithZero.log_zpow,
        WithZero.log_exp]
      simp
    _ = J := FractionalIdeal.finprod_heightOneSpectrum_factorization' K J.ne_zero

end IdeleGroup

/-! ### Descent to idèle classes -/

namespace IdeleClassGroup

variable {K : Type u} [Field K] [NumberField K]

/-- The ordinary ideal class of an idèle class.  It is well-defined because principal idèles
have trivial ideal class. -/
def idealClass : NumberField.IdeleClassGroup (𝓞 K) K →* ClassGroup (𝓞 K) := by
  apply QuotientGroup.lift (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K)
    IdeleGroup.idealClass
  rintro y ⟨x, rfl⟩
  exact IdeleGroup.idealClass_unitEmbedding x

end IdeleClassGroup

/-! ### Transport of fractional ideals under number-field isomorphisms -/

variable {K K' : Type*} [Field K] [Field K'] [NumberField K] [NumberField K']

/-! ### Fractional ideals

The map $v\mapsto\sigma(v)$ on primes extends to the free abelian group of nonzero fractional
ideals and is compatible with the fractional ideal of an idèle. -/

namespace FractionalIdeal

open _root_.FractionalIdeal

/-- The homomorphism of groups of nonzero fractional ideals induced by an isomorphism `σ` of
number fields, sending each prime `v` to $\sigma(v)$. -/
def congr (σ : K ≃+* K') : (FractionalIdeal (𝓞 K)⁰ K)ˣ →* (FractionalIdeal (𝓞 K')⁰ K')ˣ :=
  liftPrimes K ∅ (fun v ↦ primeFractionalIdeal K' (FinitePlace.mapEquiv σ v))

/-- The fractional-ideal map of `σ` sends the prime `v` to $\sigma(v)$. -/
@[simp]
theorem congr_primeFractionalIdeal (σ : K ≃+* K') (v : HeightOneSpectrum (𝓞 K)) :
    congr σ (primeFractionalIdeal K v) = primeFractionalIdeal K' (FinitePlace.mapEquiv σ v) :=
  liftPrimes_primeFractionalIdeal_of_notMem ∅ _ (Finset.notMem_empty v)

/-- Transporting a fractional ideal preserves its order at each transported prime; used by
`IdeleGroup.toFractionalIdeal_congr`. -/
theorem count_congr (σ : K ≃+* K') (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    count K' (FinitePlace.mapEquiv σ v)
        (congr σ J : FractionalIdeal (𝓞 K')⁰ K') =
      count K v (J : FractionalIdeal (𝓞 K)⁰ K) := by
  have heq : (countHom (K := K') (FinitePlace.mapEquiv σ v)).comp (congr σ) =
      countHom (K := K) v := by
    apply monoidHom_ext
    intro w
    change Multiplicative.ofAdd
        (count K' (FinitePlace.mapEquiv σ v)
          (congr σ (primeFractionalIdeal K w) : FractionalIdeal (𝓞 K')⁰ K')) =
      Multiplicative.ofAdd (count K v (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K))
    rw [congr_primeFractionalIdeal]
    congr 1
    change count K' (FinitePlace.mapEquiv σ v)
      ((FinitePlace.mapEquiv σ w).asIdeal : FractionalIdeal (𝓞 K')⁰ K') =
        count K v (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K)
    by_cases h : w = v
    · subst w
      rw [count_self, count_self]
    · have h' : FinitePlace.mapEquiv σ w ≠ FinitePlace.mapEquiv σ v :=
        fun he ↦ h ((FinitePlace.mapEquiv σ).injective he)
      rw [count_maximal_coprime K' _ h', count_maximal_coprime K _ h]
  exact Multiplicative.ofAdd.injective (congrArg (fun f :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ →* Multiplicative ℤ ↦ f J) heq)

end FractionalIdeal

end SIC

end
