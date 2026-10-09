/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.ClassGroup.Basic

/-!
# The group of fractional ideals of a Dedekind domain

The prime factors of a nonzero fractional ideal, extensionality by orders at primes, lifting a
function on primes to a homomorphism, the ideals prime to a finite set of primes, and principal
powers.

## The argument

The order of a principal fractional ideal is the negative logarithm of the corresponding
valuation. Unique factorization into height-one primes then gives extensionality by orders and
shows that a homomorphism out of nonzero fractional ideals is determined on primes. Taking a
finite product of prescribed prime images extends any such assignment; excluding a finite set
of primes gives the subgroup $I^S$ of ideals with zero order there. The class group kills the
power of a fractional ideal by its cardinality, so that power has a generator. The same argument
for an integral ideal gives an integral generator. These facts underlie the Artin map and ideal
norm comparisons of Milne, *Class Field Theory*, version 4.03, Chapter V, §§3–4.
-/

noncomputable section

open Filter IsDedekindDomain
open scoped BigOperators nonZeroDivisors

namespace SIC

/-! ### Principal fractional ideals and valuations -/

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The order of a nonzero principal fractional ideal at `v` is the negative logarithm of
the `v`-adic valuation of its generator. -/
theorem FractionalIdeal.count_spanSingleton
    (v : HeightOneSpectrum R) (x : K) (hx : x ≠ 0) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ x) =
      -WithZero.log (v.valuation K x) := by
  symm
  obtain ⟨n, d, rfl⟩ := IsLocalization.exists_mk'_eq R⁰ x
  have hn : n ≠ 0 := by
    intro hn
    apply hx
    rw [hn, IsFractionRing.mk'_eq_div, map_zero, zero_div]
  have hspan : FractionalIdeal.spanSingleton R⁰ (IsLocalization.mk' K n d) =
      FractionalIdeal.spanSingleton R⁰ ((algebraMap R K) (d : R))⁻¹ *
        (Ideal.span {n} : Ideal R) := by
    rw [FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    apply congrArg (FractionalIdeal.spanSingleton R⁰)
    rw [IsFractionRing.mk'_eq_div, div_eq_mul_inv]
    exact mul_comm _ _
  rw [FractionalIdeal.count_well_defined K v
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx) hspan]
  rw [v.valuation_of_mk', v.intValuation_if_neg hn,
    v.intValuation_if_neg (nonZeroDivisors.ne_zero d.property), ← WithZero.exp_sub,
    WithZero.log_exp]
  ring

/-! ### Prime generators

The nonzero fractional ideals of a Dedekind domain form a free abelian group on its height-one
primes, so a homomorphism out of that group is determined by its values on the primes. -/

variable (K) in
/-- A height-one prime `v` as a unit of the group of nonzero fractional ideals. -/
def primeFractionalIdeal (v : HeightOneSpectrum R) : (FractionalIdeal R⁰ K)ˣ :=
  Units.mk0 (v.asIdeal : FractionalIdeal R⁰ K) (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)

/-- The fractional ideal underlying `primeFractionalIdeal K v` is `v`. -/
@[simp]
theorem coe_primeFractionalIdeal (v : HeightOneSpectrum R) :
    ((primeFractionalIdeal K v : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) = v.asIdeal :=
  rfl

/-- The unit-valued prime factorization used by `FractionalIdeal.monoidHom_ext` and
`FractionalIdeal.exists_finset_mem_closure`. -/
private theorem FractionalIdeal.finprod_prime_factorization
    (J : (FractionalIdeal R⁰ K)ˣ) :
    (∏ᶠ v : HeightOneSpectrum R,
      primeFractionalIdeal K v ^ FractionalIdeal.count K v
        (J : FractionalIdeal R⁰ K)) = J := by
  apply Units.ext
  change (Units.coeHom (FractionalIdeal R⁰ K))
    (∏ᶠ v : HeightOneSpectrum R,
      primeFractionalIdeal K v ^ FractionalIdeal.count K v
        (J : FractionalIdeal R⁰ K)) = (J : FractionalIdeal R⁰ K)
  rw [(Units.coeHom (FractionalIdeal R⁰ K)).map_finprod_of_injective
    Units.coeHom_injective]
  simpa only [Units.coeHom_apply, Units.val_zpow_eq_zpow_val,
    coe_primeFractionalIdeal] using
    FractionalIdeal.finprod_heightOneSpectrum_factorization' K J.ne_zero

/-- Two nonzero fractional ideals are equal if they have the same order at every height-one
prime, by `FractionalIdeal.finprod_heightOneSpectrum_factorization'`. -/
theorem FractionalIdeal.ext_count {A B : _root_.FractionalIdeal R⁰ K}
    (hA : A ≠ 0) (hB : B ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, _root_.FractionalIdeal.count K v A =
      _root_.FractionalIdeal.count K v B) : A = B := by
  calc
    A = ∏ᶠ v : HeightOneSpectrum R,
        (v.asIdeal : _root_.FractionalIdeal R⁰ K) ^ _root_.FractionalIdeal.count K v A :=
      (_root_.FractionalIdeal.finprod_heightOneSpectrum_factorization' K hA).symm
    _ = ∏ᶠ v : HeightOneSpectrum R,
        (v.asIdeal : _root_.FractionalIdeal R⁰ K) ^ _root_.FractionalIdeal.count K v B := by
      apply finprod_congr
      intro v
      rw [h v]
    _ = B := _root_.FractionalIdeal.finprod_heightOneSpectrum_factorization' K hB

/-- Homomorphisms out of the group of nonzero fractional ideals agree when they agree on the
height-one primes, by the prime factorization of fractional ideals
(`FractionalIdeal.finprod_heightOneSpectrum_factorization'`). -/
theorem FractionalIdeal.monoidHom_ext {G : Type*} [Monoid G]
    {f g : (FractionalIdeal R⁰ K)ˣ →* G}
    (h : ∀ v : HeightOneSpectrum R, f (primeFractionalIdeal K v) = g (primeFractionalIdeal K v)) :
    f = g := by
  apply MonoidHom.eq_of_eqOn_dense (s := Set.range (primeFractionalIdeal K))
  · apply eq_top_iff.mpr
    intro J _
    rw [← FractionalIdeal.finprod_prime_factorization J]
    apply finprod_induction (fun J ↦ J ∈ Subgroup.closure (Set.range (primeFractionalIdeal K)))
    · exact Subgroup.one_mem _
    · intro a b ha hb
      exact Subgroup.mul_mem _ ha hb
    · intro v
      exact Subgroup.zpow_mem _ (Subgroup.subset_closure (Set.mem_range_self v)) _
  · exact Set.forall_mem_range.mpr h

variable (K) in
/-- The homomorphism sending a prime `v ∉ S` to `f v` and the primes of `S` to `1`. -/
def FractionalIdeal.liftPrimes {G : Type*} [CommGroup G]
    (S : Finset (HeightOneSpectrum R)) (f : HeightOneSpectrum R → G) :
    (FractionalIdeal R⁰ K)ˣ →* G := by
  have hfinite (J : (FractionalIdeal R⁰ K)ˣ) :
      Function.HasFiniteMulSupport (fun v : HeightOneSpectrum R ↦
        f v ^ FractionalIdeal.count K v (J : FractionalIdeal R⁰ K)) := by
    have hfin : {v : HeightOneSpectrum R |
        FractionalIdeal.count K v (J : FractionalIdeal R⁰ K) ≠ 0}.Finite := by
      simpa only [Filter.eventually_cofinite] using
        (FractionalIdeal.finite_factors (J : FractionalIdeal R⁰ K))
    apply hfin.subset
    intro v hv
    change f v ^ FractionalIdeal.count K v (J : FractionalIdeal R⁰ K) ≠ 1 at hv
    simp only [Set.mem_ofPred_eq]
    intro hz
    exact hv (by simp [hz])
  refine {
    toFun J := ∏ᶠ (v : HeightOneSpectrum R) (_ : v ∉ S),
      f v ^ FractionalIdeal.count K v (J : FractionalIdeal R⁰ K)
    map_one' := by simp [FractionalIdeal.count_one]
    map_mul' := ?_ }
  intro J J'
  simp_rw [Units.val_mul, FractionalIdeal.count_mul K _ J.ne_zero J'.ne_zero, zpow_add]
  exact finprod_mem_mul_distrib'
    ((hfinite J).inter_of_right _) ((hfinite J').inter_of_right _)

/-- `liftPrimes` takes a prime outside `S` to its prescribed value. -/
@[simp]
theorem FractionalIdeal.liftPrimes_primeFractionalIdeal_of_notMem {G : Type*}
    [CommGroup G] (S : Finset (HeightOneSpectrum R)) (f : HeightOneSpectrum R → G)
    {v : HeightOneSpectrum R} (hv : v ∉ S) :
    FractionalIdeal.liftPrimes K S f (primeFractionalIdeal K v) = f v := by
  change (∏ᶠ (w : HeightOneSpectrum R) (_ : w ∉ S),
    f w ^ FractionalIdeal.count K w (v.asIdeal : FractionalIdeal R⁰ K)) = f v
  rw [finprod_cond_eq_prod_of_cond_iff (t := {v}) (fun w ↦
    f w ^ FractionalIdeal.count K w (v.asIdeal : FractionalIdeal R⁰ K))]
  · simp [FractionalIdeal.count_self]
  · intro w hw
    by_cases h : w = v
    · subst w
      simp [hv]
    · exfalso
      apply hw
      simp [FractionalIdeal.count_maximal_coprime K w (Ne.symm h)]

/-- `liftPrimes` takes a prime in `S` to `1`. -/
@[simp]
theorem FractionalIdeal.liftPrimes_primeFractionalIdeal_of_mem {G : Type*}
    [CommGroup G] (S : Finset (HeightOneSpectrum R)) (f : HeightOneSpectrum R → G)
    {v : HeightOneSpectrum R} (hv : v ∈ S) :
    FractionalIdeal.liftPrimes K S f (primeFractionalIdeal K v) = 1 := by
  change (∏ᶠ (w : HeightOneSpectrum R) (_ : w ∉ S),
    f w ^ FractionalIdeal.count K w (v.asIdeal : FractionalIdeal R⁰ K)) = 1
  apply finprod_mem_eq_one_of_forall_eq_one
  intro w hw
  have h : v ≠ w := by
    intro heq
    exact hw (heq ▸ hv)
  rw [FractionalIdeal.count_maximal_coprime K w h, zpow_zero]

/-! ### Fractional ideals prime to a finite set

The fractional ideals of order zero at every prime of a finite set `S` form the subgroup $I^S$
on which the Artin map of Milne, *Class Field Theory*, Chapter V, §3, is defined. Every
fractional ideal lies in the subgroup generated by the finitely many primes at which its order
is nonzero. -/

variable (K) in
/-- The group $I^S$ of nonzero fractional ideals prime to a finite set `S` of primes: those of
order zero at every prime of `S`. Milne, *Class Field Theory*, Chapter V, §3, "The Artin map". -/
def FractionalIdeal.primeTo (S : Finset (HeightOneSpectrum R)) :
    Subgroup (FractionalIdeal R⁰ K)ˣ where
  carrier := {J | ∀ v ∈ S, FractionalIdeal.count K v (J : FractionalIdeal R⁰ K) = 0}
  one_mem' := fun v _ ↦ by simp [FractionalIdeal.count_one]
  mul_mem' := fun {J J'} hJ hJ' v hv ↦ by
    rw [Units.val_mul, FractionalIdeal.count_mul K v J.ne_zero J'.ne_zero, hJ v hv, hJ' v hv,
      add_zero]
  inv_mem' := fun {J} hJ v hv ↦ by
    rw [Units.val_inv_eq_inv_val, FractionalIdeal.count_inv, hJ v hv, neg_zero]

/-- Membership in $I^S$ is order zero at every prime of `S`. -/
theorem FractionalIdeal.mem_primeTo_iff {S : Finset (HeightOneSpectrum R)}
    {J : (FractionalIdeal R⁰ K)ˣ} :
    J ∈ FractionalIdeal.primeTo K S ↔
      ∀ v ∈ S, FractionalIdeal.count K v (J : FractionalIdeal R⁰ K) = 0 :=
  Iff.rfl

/-- Enlarging `S` shrinks $I^S$: $I^{S'}\subseteq I^S$ for $S\subseteq S'$. -/
theorem FractionalIdeal.primeTo_anti : Antitone (FractionalIdeal.primeTo (R := R) K) := by
  intro S S' h J hJ v hv
  exact hJ v (h hv)

/-- Enlarging the excluded set does not change a prime lift on an ideal whose orders vanish at
the newly excluded primes; used by `artinMap_eq_of_mem_primeTo`. -/
theorem FractionalIdeal.liftPrimes_eq_of_mem_primeTo {G : Type*} [CommGroup G]
    {S S' : Finset (HeightOneSpectrum R)} (hSS' : S ⊆ S')
    (f : HeightOneSpectrum R → G) {J : (FractionalIdeal R⁰ K)ˣ}
    (hJ : J ∈ FractionalIdeal.primeTo K S') :
    FractionalIdeal.liftPrimes K S f J = FractionalIdeal.liftPrimes K S' f J := by
  change (∏ᶠ (v : HeightOneSpectrum R) (_ : v ∉ S),
      f v ^ FractionalIdeal.count K v (J : FractionalIdeal R⁰ K)) =
    (∏ᶠ (v : HeightOneSpectrum R) (_ : v ∉ S'),
      f v ^ FractionalIdeal.count K v (J : FractionalIdeal R⁰ K))
  apply finprod_mem_inter_mulSupport_eq'
  intro v hv
  change f v ^ FractionalIdeal.count K v (J : FractionalIdeal R⁰ K) ≠ 1 at hv
  constructor
  · intro hvS
    by_contra hvS'
    have hz := (FractionalIdeal.mem_primeTo_iff.mp hJ) v (not_not.mp hvS')
    exact hv (by simp [hz])
  · intro hvS' hvS
    exact hvS' (hSS' hvS)

/-- A prime outside `S` is prime to `S`. -/
theorem primeFractionalIdeal_mem_primeTo {S : Finset (HeightOneSpectrum R)}
    {v : HeightOneSpectrum R} (hv : v ∉ S) :
    primeFractionalIdeal K v ∈ FractionalIdeal.primeTo K S := by
  intro w hw
  have hvw : v ≠ w := fun h ↦ hv (h ▸ hw)
  rw [coe_primeFractionalIdeal, FractionalIdeal.count_maximal_coprime K w hvw]

/-- A fractional ideal lies in the subgroup generated by the finitely many primes at which its
order is nonzero, by its prime factorization
(`FractionalIdeal.finprod_heightOneSpectrum_factorization'`). -/
theorem FractionalIdeal.exists_finset_mem_closure (J : (FractionalIdeal R⁰ K)ˣ) :
    ∃ T : Finset (HeightOneSpectrum R),
      (∀ v ∈ T, FractionalIdeal.count K v (J : FractionalIdeal R⁰ K) ≠ 0) ∧
        J ∈ Subgroup.closure (primeFractionalIdeal K '' (T : Set (HeightOneSpectrum R))) := by
  classical
  have hfinite : {v : HeightOneSpectrum R |
      FractionalIdeal.count K v (J : FractionalIdeal R⁰ K) ≠ 0}.Finite := by
    simpa only [Filter.eventually_cofinite] using
      (FractionalIdeal.finite_factors (J : FractionalIdeal R⁰ K))
  let T := hfinite.toFinset
  refine ⟨T, ?_, ?_⟩
  · intro v hv
    exact hfinite.mem_toFinset.mp hv
  · rw [← FractionalIdeal.finprod_prime_factorization J]
    apply finprod_induction
      (fun A : (FractionalIdeal R⁰ K)ˣ ↦
        A ∈ Subgroup.closure (primeFractionalIdeal K '' (T : Set (HeightOneSpectrum R))))
    · exact Subgroup.one_mem _
    · intro a b ha hb
      exact Subgroup.mul_mem _ ha hb
    · intro v
      by_cases hv : v ∈ T
      · exact Subgroup.zpow_mem _
          (Subgroup.subset_closure (Set.mem_image_of_mem _ (Finset.mem_coe.mpr hv))) _
      · have hz : FractionalIdeal.count K v (J : FractionalIdeal R⁰ K) = 0 := by
          by_contra h
          exact hv (hfinite.mem_toFinset.mpr h)
        simp [hz]

/-! ### Orders and principal powers -/

/-- The order at a fixed prime as a multiplicative homomorphism; used by
`FractionalIdeal.count_congr`. -/
def FractionalIdeal.countHom (v : HeightOneSpectrum R) :
    (FractionalIdeal R⁰ K)ˣ →* Multiplicative ℤ where
  toFun J := Multiplicative.ofAdd (FractionalIdeal.count K v (J : FractionalIdeal R⁰ K))
  map_one' := by
    change Multiplicative.ofAdd (FractionalIdeal.count K v (1 : FractionalIdeal R⁰ K)) =
      Multiplicative.ofAdd 0
    rw [FractionalIdeal.count_one]
  map_mul' I J := by
    change Multiplicative.ofAdd (FractionalIdeal.count K v
      ((I * J : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K)) =
        Multiplicative.ofAdd (FractionalIdeal.count K v (I : FractionalIdeal R⁰ K) +
          FractionalIdeal.count K v (J : FractionalIdeal R⁰ K))
    rw [Units.val_mul, FractionalIdeal.count_mul K v I.ne_zero J.ne_zero]

/-- A positive power is injective on nonzero fractional ideals; used by
`FractionalIdeal.coe_relNorm_coeIdeal`. -/
theorem FractionalIdeal.pow_injective_of_ne_zero (n : ℕ) (hn : n ≠ 0)
    {A B : FractionalIdeal R⁰ K} (hA : A ≠ 0) (hB : B ≠ 0)
    (h : A ^ n = B ^ n) : A = B := by
  have hc (v : HeightOneSpectrum R) :
      FractionalIdeal.count K v A = FractionalIdeal.count K v B := by
    have hv := congrArg (FractionalIdeal.count K v) h
    rw [FractionalIdeal.count_pow, FractionalIdeal.count_pow] at hv
    exact mul_left_cancel₀ (by exact_mod_cast hn : (n : ℤ) ≠ 0) hv
  exact FractionalIdeal.ext_count hA hB hc

/-- A nonzero fractional ideal becomes principal after raising it to the class-group order.
This is the class-group consequence used by `FractionalIdeal.coe_relNorm_coeIdeal`; compare
Milne, *Class Field Theory*, Chapter V, §3. -/
theorem FractionalIdeal.exists_classGroupCard_power_generator [Finite (ClassGroup R)]
    (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) :
    ∃ a : K, a ≠ 0 ∧ I ^ Nat.card (ClassGroup R) = FractionalIdeal.spanSingleton R⁰ a := by
  let : Fintype (ClassGroup R) := Fintype.ofFinite _
  let J : (FractionalIdeal R⁰ K)ˣ := Units.mk0 I hI
  have hclass : ClassGroup.mk K (J ^ Nat.card (ClassGroup R)) = 1 := by
    rw [map_pow, Nat.card_eq_fintype_card]
    exact pow_card_eq_one
  have hp : ((J ^ Nat.card (ClassGroup R) : (FractionalIdeal R⁰ K)ˣ) :
      Submodule R K).IsPrincipal := ClassGroup.mk_eq_one_iff.mp hclass
  let _ : Submodule.IsPrincipal ((J ^ Nat.card (ClassGroup R) :
    (FractionalIdeal R⁰ K)ˣ) : Submodule R K) := hp
  let a : K := Submodule.IsPrincipal.generator ((J ^ Nat.card (ClassGroup R) :
    (FractionalIdeal R⁰ K)ˣ) : Submodule R K)
  have ha : I ^ Nat.card (ClassGroup R) = FractionalIdeal.spanSingleton R⁰ a := by
    apply Subtype.coe_injective
    simpa [a, J, FractionalIdeal.coe_spanSingleton, Units.val_pow_eq_pow_val] using
      (Submodule.IsPrincipal.span_singleton_generator
        ((J ^ Nat.card (ClassGroup R) : (FractionalIdeal R⁰ K)ˣ) : Submodule R K)).symm
  have ha0 : a ≠ 0 := by
    intro hz
    have hpow : I ^ Nat.card (ClassGroup R) ≠ 0 := pow_ne_zero _ hI
    apply hpow
    simpa [hz] using ha
  exact ⟨a, ha0, ha⟩

/-- A nonzero integral ideal becomes principal after raising it to the class-group order;
this is the integral form used by `FractionalIdeal.coe_relNorm_coeIdeal`. -/
theorem Ideal.exists_classGroupCard_power_generator [Finite (ClassGroup R)]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (I : Ideal R) (hI : I ≠ ⊥) :
    ∃ a : R, a ≠ 0 ∧ I ^ Nat.card (ClassGroup R) = Ideal.span {a} := by
  let : Fintype (ClassGroup R) := Fintype.ofFinite _
  let h := Nat.card (ClassGroup R)
  let J : (FractionalIdeal R⁰ K)ˣ :=
    Units.mk0 (I : FractionalIdeal R⁰ K) (FractionalIdeal.coeIdeal_ne_zero.mpr hI)
  have hJpow : ((J ^ h : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) =
      (I ^ h : FractionalIdeal R⁰ K) := by
    rw [Units.val_pow_eq_pow_val]
    rfl
  have hclass : ClassGroup.mk K (J ^ h) = 1 := by
    dsimp [h]
    rw [map_pow, Nat.card_eq_fintype_card]
    exact pow_card_eq_one
  have hsub : (((I ^ h : Ideal R) : FractionalIdeal R⁰ K) : Submodule R K).IsPrincipal := by
    simpa only [FractionalIdeal.coeIdeal_pow, ← hJpow] using
      (ClassGroup.mk_eq_one_iff.mp hclass)
  have hprincipal : Submodule.IsPrincipal (I ^ h : Ideal R) :=
    (IsFractionRing.coeSubmodule_isPrincipal R K).mp hsub
  let _ : Submodule.IsPrincipal (I ^ h : Ideal R) := hprincipal
  let a : R := Submodule.IsPrincipal.generator (I ^ h : Ideal R)
  have ha : I ^ h = Ideal.span {a} := by
    simpa only [a] using
      (Submodule.IsPrincipal.span_singleton_generator (I ^ h : Ideal R)).symm
  have ha0 : a ≠ 0 := by
    intro hz
    have hpow : I ^ h ≠ ⊥ := by
      rw [← (FractionalIdeal.coeIdeal_ne_zero (K := K))]
      rw [FractionalIdeal.coeIdeal_pow]
      exact pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr hI)
    apply hpow
    simpa [hz] using ha
  exact ⟨a, ha0, ha⟩

end SIC

end
