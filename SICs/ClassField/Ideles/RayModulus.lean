/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Quadratic.RealFields
import SICs.ClassField.Local.UnitGroups
import SICs.ClassField.Completion.FiniteConjugation
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Algebra.Ring.Subring.Units

/-!
# Local factors of a ray modulus

Finite exponents and supports, the finite ray factors they select among the higher unit groups,
and the real positivity conditions specified by a set of infinite places. Number-field
isomorphisms preserve modulus exponents and finite ray factors.

## The argument

For a nonzero integral ideal `m`, its exponent at a finite place is the multiplicity of that
prime in the normalized factorization of `m`, and the finite ray factor at `v` is the higher unit
group $U_v^{(n_v)}$ of `SICs.ClassField.Local.UnitGroups`, which is open. At the infinite
places in the chosen set contribute their positive components; all other infinite places
contribute their full multiplicative groups. The selected-place modulus uses the complement of
its distinguished unrestricted place.

To prescribe lower bounds at finitely many primes, take a sufficiently large power of their
product. Each prescribed prime then occurs with at least the chosen exponent, and the product has
no other prime divisors.

A global element `c` lies in the level-`n` higher unit group at `v` exactly when `v(c) = 1` and
`v(c - 1) ≤ exp(-n)`.  Since `𝔪 = ∏ 𝔭^{n_𝔭}`, an integer lies in `𝔪` exactly when its valuation
is at most `exp(-n_𝔭)` at every prime dividing `𝔪`.  Hence an integer `a ≡ 1 (mod 𝔪)` lies in
every finite ray factor at the primes dividing `𝔪`, and conversely, if `c` lies in those factors
and `cb = a` for integers `a, b`, then `a - b = b(c - 1)` lies in `𝔪`.  These are the
congruence conditions defining $K_{\mathfrak m,1}$ in Milne, *Class Field Theory*, V.4, written
on integral representatives.

These local factors are Milne’s groups $W_𝔪(𝔭)$ in *Class Field Theory*, Chapter V, §4,
before Proposition 4.6. Neukirch, *The Bonn Lectures*, III.9.3--9.4 supplies the ideal/idèle
comparison used later.
-/

noncomputable section

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open scoped NumberField WithZero

namespace SIC

universe u

/-! ### Finite local factors -/

namespace FinitePlace

variable {K : Type u} [Field K] [NumberField K]

/-- The exponent of a finite place in an integral modulus. [Milne, *Class Field Theory*, V.1,
Definition 1.3.] -/
noncomputable def modulusExponent
    (m : Ideal (NumberField.RingOfIntegers K))
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) : ℕ :=
  Multiset.count v.asIdeal (normalizedFactors m)

/-- A modulus with a nonzero exponent at a finite place is nonzero. -/
theorem ne_bot_of_modulusExponent_ne_zero
    {m : Ideal (NumberField.RingOfIntegers K)}
    {v : HeightOneSpectrum (NumberField.RingOfIntegers K)}
    (hv : modulusExponent m v ≠ 0) : m ≠ ⊥ := by
  intro heq
  change Multiset.count v.asIdeal (normalizedFactors m) ≠ 0 at hv
  rw [heq, show (⊥ : Ideal (NumberField.RingOfIntegers K)) = 0 from rfl,
    normalizedFactors_zero] at hv
  simp at hv

/-- A finite place has nonzero modulus exponent exactly when its prime divides a nonzero
modulus. -/
theorem modulusExponent_ne_zero_iff
    {m : Ideal (NumberField.RingOfIntegers K)} (hm : m ≠ ⊥)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    modulusExponent m v ≠ 0 ↔ v.asIdeal ∣ m := by
  rw [modulusExponent, Multiset.count_ne_zero]
  rw [Ideal.mem_normalizedFactors_iff hm]
  simp only [v.isPrime, true_and, Ideal.dvd_iff_le]

/-- A finite place has exponent zero exactly when its prime does not divide a nonzero modulus. -/
theorem modulusExponent_eq_zero_iff
    {m : Ideal (NumberField.RingOfIntegers K)} (hm : m ≠ ⊥)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    modulusExponent m v = 0 ↔ ¬ v.asIdeal ∣ m := by
  rw [← not_iff_not]
  simp only [not_not]
  exact modulusExponent_ne_zero_iff hm v

/-- Coprimality to a modulus excludes every prime with nonzero modulus exponent. -/
theorem not_dvd_of_isCoprime {m I : Ideal (NumberField.RingOfIntegers K)}
    (h : IsCoprime I m) {v : HeightOneSpectrum (NumberField.RingOfIntegers K)}
    (hv : modulusExponent m v ≠ 0) : ¬ v.asIdeal ∣ I := by
  have hm := ne_bot_of_modulusExponent_ne_zero hv
  have hdiv := (modulusExponent_ne_zero_iff hm v).mp hv
  intro hI
  have ht : (⊤ : Ideal (NumberField.RingOfIntegers K)) ≤ v.asIdeal := by
    rw [← Ideal.isCoprime_iff_sup_eq.mp h]
    exact sup_le (Ideal.dvd_iff_le.mp hI) (Ideal.dvd_iff_le.mp hdiv)
  exact v.isPrime.ne_top (top_le_iff.mp ht)

/-- Coprimality forces a modulus exponent to vanish, including for the zero modulus. -/
theorem modulusExponent_eq_zero_of_isCoprime
    {m : Ideal (NumberField.RingOfIntegers K)}
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h : IsCoprime v.asIdeal m) : modulusExponent m v = 0 := by
  by_contra hv
  exact (not_dvd_of_isCoprime h hv) (dvd_refl v.asIdeal)

/-- A finite place is coprime to a nonzero modulus exactly when its exponent vanishes. -/
theorem isCoprime_iff_modulusExponent_eq_zero
    {m : Ideal (NumberField.RingOfIntegers K)} (hm : m ≠ ⊥)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    IsCoprime v.asIdeal m ↔ modulusExponent m v = 0 := by
  rw [modulusExponent_eq_zero_iff hm v]
  constructor
  · intro hcop hdiv
    have hv := (modulusExponent_ne_zero_iff hm v).mpr hdiv
    exact (not_dvd_of_isCoprime hcop hv) (dvd_refl v.asIdeal)
  · intro hnot
    apply Ideal.isCoprime_iff_sup_eq.mpr
    by_contra hsup
    have heq : v.asIdeal = v.asIdeal ⊔ m :=
      v.isMaximal.eq_of_le hsup le_sup_left
    exact hnot (Ideal.dvd_iff_le.mpr (le_sup_right.trans_eq heq.symm))

/-- The factor-count definition of the modulus exponent agrees with ideal multiplicity. -/
theorem modulusExponent_eq_multiplicity
    {m : Ideal (NumberField.RingOfIntegers K)} (hm : m ≠ ⊥)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    modulusExponent m v = multiplicity v.asIdeal m := by
  exact IsDedekindDomain.HeightOneSpectrum.count_normalizedFactors_eq_multiplicity hm v

/-- Almost every finite place has modulus exponent zero. -/
theorem eventually_modulusExponent_eq_zero
    (m : Ideal (NumberField.RingOfIntegers K)) :
    ∀ᶠ v : HeightOneSpectrum (NumberField.RingOfIntegers K) in Filter.cofinite,
      modulusExponent m v = 0 := by
  by_cases hm : m = ⊥
  · subst m
    change ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      Multiset.count v.asIdeal (normalizedFactors (0 : Ideal (𝓞 K))) = 0
    rw [normalizedFactors_zero]
    simp
  rw [Filter.eventually_cofinite]
  have heq :
      {v : HeightOneSpectrum (NumberField.RingOfIntegers K) |
        ¬ modulusExponent m v = 0} = {v | v.asIdeal ∣ m} := by
    ext v
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq,
      not_congr (modulusExponent_eq_zero_iff hm v), not_not]
  rw [heq]
  exact Ideal.finite_factors hm

/-- Only finitely many finite places have nonzero exponent in a modulus, also for the zero
modulus, where every exponent vanishes. -/
theorem finite_setOf_modulusExponent_ne_zero (m : Ideal (NumberField.RingOfIntegers K)) :
    {v : HeightOneSpectrum (NumberField.RingOfIntegers K) |
      modulusExponent m v ≠ 0}.Finite :=
  Filter.eventually_cofinite.mp (eventually_modulusExponent_eq_zero m)

/-- The support of a modulus: the finite places with nonzero exponent, that is, the primes
dividing a nonzero modulus. -/
noncomputable def modulusSupport (m : Ideal (NumberField.RingOfIntegers K)) :
    Finset (HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
  (finite_setOf_modulusExponent_ne_zero m).toFinset

/-- A place lies in the support of a modulus exactly when its exponent is nonzero. -/
@[simp]
theorem mem_modulusSupport {m : Ideal (NumberField.RingOfIntegers K)}
    {v : HeightOneSpectrum (NumberField.RingOfIntegers K)} :
    v ∈ modulusSupport m ↔ modulusExponent m v ≠ 0 :=
  Set.Finite.mem_toFinset _

/-- A finite prime containing a nonzero modulus belongs to its support. -/
theorem mem_modulusSupport_of_le {m : Ideal (NumberField.RingOfIntegers K)}
    (hm : m ≠ ⊥) {v : HeightOneSpectrum (NumberField.RingOfIntegers K)}
    (h : m ≤ v.asIdeal) : v ∈ modulusSupport m := by
  exact mem_modulusSupport.mpr ((modulusExponent_ne_zero_iff hm v).mpr
    (Ideal.dvd_iff_le.mpr h))

/-- For a nonzero modulus, a prime lies in the support exactly when it contains the modulus. -/
theorem mem_modulusSupport_iff_le {m : Ideal (NumberField.RingOfIntegers K)} (hm : m ≠ ⊥)
    {v : HeightOneSpectrum (NumberField.RingOfIntegers K)} :
    v ∈ modulusSupport m ↔ m ≤ v.asIdeal := by
  rw [mem_modulusSupport, modulusExponent_ne_zero_iff hm, Ideal.dvd_iff_le]

/-- A divisor of a nonzero modulus has smaller support:
$\operatorname{supp}\mathfrak m'\subseteq\operatorname{supp}\mathfrak m$ for
$\mathfrak m'\mid\mathfrak m\ne 0$. -/
theorem modulusSupport_subset_of_le {m m' : Ideal (NumberField.RingOfIntegers K)} (hm : m ≠ ⊥)
    (h : m ≤ m') : modulusSupport m' ⊆ modulusSupport m := by
  have hm' : m' ≠ ⊥ := ne_bot_of_le_ne_bot hm h
  intro v hv
  exact (mem_modulusSupport_iff_le hm).mpr
    (h.trans ((mem_modulusSupport_iff_le hm').mp hv))

open scoped Classical in
/-- The support of a product of nonzero moduli is the union of their supports. -/
theorem modulusSupport_mul {m n : Ideal (NumberField.RingOfIntegers K)} (hm : m ≠ ⊥)
    (hn : n ≠ ⊥) : modulusSupport (m * n) = modulusSupport m ∪ modulusSupport n := by
  have hmn : m * n ≠ ⊥ := mul_ne_zero hm hn
  ext v
  rw [mem_modulusSupport_iff_le hmn, Finset.mem_union,
    mem_modulusSupport_iff_le hm, mem_modulusSupport_iff_le hn]
  exact v.isPrime.mul_le

open scoped Classical in
/-- The support of a finite product of nonzero moduli is the union of their supports. -/
theorem modulusSupport_prod {ι : Type*} (s : Finset ι)
    (f : ι → Ideal (NumberField.RingOfIntegers K)) (hf : ∀ i ∈ s, f i ≠ ⊥) :
    modulusSupport (∏ i ∈ s, f i) = s.biUnion fun i ↦ modulusSupport (f i) := by
  have hprod : (∏ i ∈ s, f i) ≠ ⊥ := by
    change (∏ i ∈ s, f i) ≠ 0
    exact Finset.prod_ne_zero_iff.mpr hf
  ext v
  rw [mem_modulusSupport_iff_le hprod, Finset.mem_biUnion]
  constructor
  · intro hp
    obtain ⟨i, hi, hfi⟩ := v.isPrime.prod_le.mp hp
    exact ⟨i, hi, (mem_modulusSupport_iff_le (hf i hi)).mpr hfi⟩
  · rintro ⟨i, hi, hfi⟩
    exact v.isPrime.prod_le.mpr
      ⟨i, hi, (mem_modulusSupport_iff_le (hf i hi)).mp hfi⟩

/-- The support of a finite prime, as a modulus, is that prime. -/
theorem modulusSupport_asIdeal (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    modulusSupport v.asIdeal = {v} := by
  ext w
  rw [mem_modulusSupport_iff_le v.ne_bot, Finset.mem_singleton]
  constructor
  · intro h
    exact HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isMaximal.ne_top h).symm
  · rintro rfl
    exact le_refl _

/-- The support of the product of the primes of a finite set is that set. -/
theorem modulusSupport_prod_asIdeal
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers K))) :
    modulusSupport (∏ v ∈ S, v.asIdeal) = S := by
  classical
  rw [modulusSupport_prod S (fun v ↦ v.asIdeal) (fun v _ ↦ v.ne_bot)]
  simp_rw [modulusSupport_asIdeal]
  simp

omit [NumberField K] in
/-- A finite product of prime ideals is nonzero. -/
theorem prod_asIdeal_ne_bot
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers K))) :
    (∏ v ∈ S, v.asIdeal) ≠ ⊥ := by
  change (∏ v ∈ S, v.asIdeal) ≠ 0
  exact Finset.prod_ne_zero_iff.mpr (fun v _ ↦ v.ne_bot)

open scoped Classical in
/-- Multiplying a nonzero modulus by finitely many primes adds their support. -/
theorem modulusSupport_mul_prod_asIdeal {a : Ideal (NumberField.RingOfIntegers K)}
    (ha : a ≠ ⊥) (T : Finset (HeightOneSpectrum (NumberField.RingOfIntegers K))) :
    modulusSupport (a * ∏ v ∈ T, v.asIdeal) = modulusSupport a ∪ T := by
  rw [modulusSupport_mul ha (prod_asIdeal_ne_bot T), modulusSupport_prod_asIdeal]

/-- Every finite set of places and prescribed levels admit a nonzero modulus supported on that
set whose exponents there exceed the levels. -/
theorem exists_lt_modulusExponent (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (n : HeightOneSpectrum (NumberField.RingOfIntegers K) → ℕ) :
    ∃ m : Ideal (NumberField.RingOfIntegers K), m ≠ ⊥ ∧
      (∀ v ∈ S, n v < modulusExponent m v) ∧ modulusSupport m ⊆ S := by
  classical
  let N := S.sup n + 1
  let b : Ideal (NumberField.RingOfIntegers K) := ∏ v ∈ S, v.asIdeal
  have hb : b ≠ ⊥ := prod_asIdeal_ne_bot S
  have hbSupport : modulusSupport b = S := modulusSupport_prod_asIdeal S
  let m := b ^ N
  have hm : m ≠ ⊥ := pow_ne_zero N hb
  refine ⟨m, hm, ?_, ?_⟩
  · intro v hv
    have hdiv : v.asIdeal ∣ b := Finset.dvd_prod_of_mem _ hv
    have hpow : v.asIdeal ^ N ∣ m := pow_dvd_pow_of_dvd hdiv N
    have hN : N ≤ modulusExponent m v := by
      rw [modulusExponent_eq_multiplicity hm]
      exact (FiniteMultiplicity.of_prime_left v.prime hm).pow_dvd_iff_le_multiplicity.mp hpow
    exact (Nat.succ_le_succ (Finset.le_sup hv)).trans hN
  · intro w hw
    have hle : m ≤ w.asIdeal := (mem_modulusSupport_iff_le hm).mp hw
    have hb_le : b ≤ w.asIdeal := w.isPrime.le_of_pow_le hle
    exact hbSupport ▸ (mem_modulusSupport_iff_le hb).mpr hb_le

/-- An element of `𝔪` has valuation at most `exp(-n_v)` at every finite place `v`, where `n_v`
is the exponent of `v` in `𝔪`. -/
theorem intValuation_le_of_mem_modulus {m : Ideal (NumberField.RingOfIntegers K)}
    {x : NumberField.RingOfIntegers K} (hx : x ∈ m)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    v.intValuation x ≤ WithZero.exp (-(modulusExponent m v : ℤ)) := by
  by_cases hm : m = ⊥
  · have : x = 0 := by simpa [hm] using hx
    simp [this]
  · apply (v.intValuation_le_pow_iff_mem x (modulusExponent m v)).mpr
    have hle : m ≤ v.asIdeal ^ modulusExponent m v := by
      calc
        m = ⨅ w : HeightOneSpectrum (NumberField.RingOfIntegers K),
          w.maxPowDividing m := (Ideal.iInf_maxPowDividing_eq hm).symm
        _ ≤ v.maxPowDividing m := iInf_le _ v
        _ = v.asIdeal ^ modulusExponent m v := by
          rw [v.maxPowDividing_eq_pow_multiplicity hm,
            ← modulusExponent_eq_multiplicity hm]
    exact hle hx

/-- An integer whose valuation is at most `exp(-n_v)` at every prime `v` dividing a nonzero
modulus `𝔪` lies in `𝔪`. -/
theorem mem_modulus_of_forall_intValuation_le {m : Ideal (NumberField.RingOfIntegers K)}
    (hm : m ≠ ⊥) {x : NumberField.RingOfIntegers K}
    (h : ∀ v : HeightOneSpectrum (NumberField.RingOfIntegers K),
      modulusExponent m v ≠ 0 → v.intValuation x ≤ WithZero.exp (-(modulusExponent m v : ℤ))) :
    x ∈ m := by
  rw [← Ideal.iInf_maxPowDividing_eq hm]
  refine (Submodule.mem_iInf _).mpr ?_
  intro v
  rw [v.maxPowDividing_eq_pow_multiplicity hm,
    ← modulusExponent_eq_multiplicity hm]
  by_cases hv : modulusExponent m v = 0
  · simp [hv]
  · exact (v.intValuation_le_pow_iff_mem x _).mp (h v hv)

/-- The finite local unit factor selected by an integral modulus. [Milne, *Class Field Theory*,
V §4, before Proposition 4.6.] -/
def rayUnitGroup
    (m : Ideal (NumberField.RingOfIntegers K))
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Subgroup (v.adicCompletion K)ˣ :=
  higherUnitGroup v (modulusExponent m v)

/-- The finite local ray factor consists of integral units. -/
theorem rayUnitGroup_le_unitGroup
    (m : Ideal (NumberField.RingOfIntegers K))
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    rayUnitGroup m v ≤ unitGroup v :=
  higherUnitGroup_le_unitGroup v _

/-- Exponent zero selects the full integral-unit group. -/
theorem rayUnitGroup_eq_of_exponent_eq_zero
    {m : Ideal (NumberField.RingOfIntegers K)}
    {v : HeightOneSpectrum (NumberField.RingOfIntegers K)}
    (h : modulusExponent m v = 0) :
    rayUnitGroup m v = unitGroup v := by
  simp [rayUnitGroup, h]

/-- Every finite local ray factor is open. -/
theorem isOpen_rayUnitGroup
    (m : Ideal (NumberField.RingOfIntegers K))
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    IsOpen (rayUnitGroup m v : Set (v.adicCompletion K)ˣ) := by
  exact isOpen_higherUnitGroup v _

/-- Modulus exponents decrease when the ideal grows. -/
theorem modulusExponent_anti {m m' : Ideal (𝓞 K)} (hm : m ≠ ⊥) (h : m ≤ m')
    (v : HeightOneSpectrum (𝓞 K)) :
    modulusExponent m' v ≤ modulusExponent m v := by
  have hm' : m' ≠ ⊥ := ne_bot_of_le_ne_bot hm h
  rw [modulusExponent_eq_multiplicity hm', modulusExponent_eq_multiplicity hm]
  exact v.multiplicity_le_of_ideal_ge h hm

/-- The local ray unit group grows when the modulus ideal grows. -/
theorem rayUnitGroup_mono {m m' : Ideal (𝓞 K)} (hm : m ≠ ⊥) (h : m ≤ m')
    (v : HeightOneSpectrum (𝓞 K)) :
    rayUnitGroup m v ≤ rayUnitGroup m' v := by
  exact higherUnitGroup_anti v (modulusExponent_anti hm h v)

/-! ### Global elements of the finite ray factors

The integral form of the congruence `c ≡ 1 (mod^× 𝔪)`: an integer congruent to `1` modulo `𝔪`
lies in the finite ray factor at every prime dividing `𝔪`, and a global element of those factors
multiplies an integer `b` to an integer congruent to `b` modulo `𝔪`. -/

/-- An integer `a ≡ 1 (mod 𝔪)` lies in the finite ray factor at every prime dividing `𝔪`.
[Milne, *Class Field Theory*, V §4, before Proposition 4.6.] -/
theorem units_map_mem_rayUnitGroup_of_sub_one_mem
    {m : Ideal (NumberField.RingOfIntegers K)} {a : NumberField.RingOfIntegers K} {c : Kˣ}
    (hc : (c : K) = a) (ha : a - 1 ∈ m)
    {v : HeightOneSpectrum (NumberField.RingOfIntegers K)} (hv : modulusExponent m v ≠ 0) :
    Units.map (algebraMap K (v.adicCompletion K)) c ∈ rayUnitGroup m v := by
  have hval := intValuation_le_of_mem_modulus ha v
  have hpow : a - 1 ∈ v.asIdeal ^ modulusExponent m v :=
    (v.intValuation_le_pow_iff_mem (a - 1) _).mp hval
  have hmem : a - 1 ∈ v.asIdeal := Ideal.pow_le_self hv hpow
  have hnot : a ∉ v.asIdeal := by
    intro ha'
    have h1 : (1 : NumberField.RingOfIntegers K) ∈ v.asIdeal := by
      have := v.asIdeal.sub_mem ha' hmem
      simpa using this
    exact v.isPrime.one_notMem h1
  change Units.map (algebraMap K (v.adicCompletion K)) c ∈
    higherUnitGroup v (modulusExponent m v)
  rw [units_map_mem_higherUnitGroup_iff]
  constructor
  · rw [hc, v.valuation_of_algebraMap]
    exact v.intValuation_eq_one_iff.mpr hnot
  · have hsub : v.valuation K ((c : K) - 1) = v.intValuation (a - 1) := by
      rw [hc]
      have hcast : ((a - 1 : NumberField.RingOfIntegers K) : K) = (a : K) - 1 := by
        change algebraMap (NumberField.RingOfIntegers K) K (a - 1) =
          algebraMap (NumberField.RingOfIntegers K) K a - 1
        simp
      rw [← hcast]
      exact v.valuation_of_algebraMap (a - 1)
    rw [hsub]
    exact hval

/-- If `c` lies in the finite ray factor at every prime dividing a nonzero `𝔪` and `cb = a`
for integers `a, b`, then `a ≡ b (mod 𝔪)`. -/
theorem sub_mem_of_units_map_mem_rayUnitGroup
    {m : Ideal (NumberField.RingOfIntegers K)} (hm : m ≠ ⊥)
    {a b : NumberField.RingOfIntegers K} {c : Kˣ} (hc : (c : K) * b = a)
    (h : ∀ v : HeightOneSpectrum (NumberField.RingOfIntegers K), modulusExponent m v ≠ 0 →
      Units.map (algebraMap K (v.adicCompletion K)) c ∈ rayUnitGroup m v) :
    a - b ∈ m := by
  apply mem_modulus_of_forall_intValuation_le hm
  intro v hv
  have hcval := (units_map_mem_higherUnitGroup_iff v (modulusExponent m v) c).mp (h v hv)
  have hbval : v.valuation K (b : K) ≤ 1 := v.valuation_le_one b
  have heq : ((a - b : NumberField.RingOfIntegers K) : K) =
      (b : K) * ((c : K) - 1) := by
    change algebraMap (NumberField.RingOfIntegers K) K (a - b) =
      (b : K) * ((c : K) - 1)
    rw [map_sub]
    change (a : K) - (b : K) = (b : K) * ((c : K) - 1)
    rw [← hc]
    ring
  calc
    v.intValuation (a - b) = v.valuation K ((a - b : NumberField.RingOfIntegers K) : K) :=
      (v.valuation_of_algebraMap (a - b)).symm
    _ = v.valuation K (b : K) * v.valuation K ((c : K) - 1) := by
      simpa only [Valuation.map_mul] using congrArg (v.valuation K) heq
    _ ≤
        1 * WithZero.exp (-(modulusExponent m v : ℤ)) :=
      mul_le_mul' hbval hcval.2
    _ = _ := one_mul _

end FinitePlace

/-! ### Infinite local factors -/

namespace InfinitePlace

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

variable {K : Type u} [Field K] [NumberField K]

/-- The infinite places where positivity is imposed, relative to one unrestricted place. -/
def raySupport (w₀ : NumberField.InfinitePlace K) : Set (NumberField.InfinitePlace K) :=
  {w | w ≠ w₀}

/-- The positive component at a real place, and the full group at a complex place.
Milne, *Class Field Theory*, version 4.03, Chapter V, §4, before Proposition 4.6. -/
def positiveUnitGroup (w : NumberField.InfinitePlace K) : Subgroup w.Completionˣ where
  carrier := {x | ∀ hw : w.IsReal, 0 < extensionEmbeddingOfIsReal hw (x : w.Completion)}
  one_mem' := by simp
  mul_mem' hx hy hw := by
    rw [Units.val_mul, map_mul]
    exact mul_pos (hx hw) (hy hw)
  inv_mem' hx hw := by
    rw [Units.val_inv_eq_inv_val, map_inv₀]
    exact inv_pos.mpr (hx hw)

omit [NumberField K] in
/-- Membership in the positive local group is positivity whenever the place is real. -/
@[simp]
theorem mem_positiveUnitGroup_iff
    (w : NumberField.InfinitePlace K) (x : w.Completionˣ) :
    x ∈ positiveUnitGroup w ↔
      ∀ hw : w.IsReal, 0 < extensionEmbeddingOfIsReal hw (x : w.Completion) := Iff.rfl

omit [NumberField K] in
/-- The positive component of a local multiplicative group is open. -/
theorem isOpen_positiveUnitGroup (w : NumberField.InfinitePlace K) :
    IsOpen (positiveUnitGroup w : Set w.Completionˣ) := by
  by_cases hw : w.IsReal
  · have heq : (positiveUnitGroup w : Set w.Completionˣ) =
        {x : w.Completionˣ | 0 < extensionEmbeddingOfIsReal hw (x : w.Completion)} := by
      ext x
      exact ⟨fun hx ↦ hx hw, fun hx _ ↦ hx⟩
    rw [heq]
    exact isOpen_lt continuous_const
      ((isometry_extensionEmbeddingOfIsReal hw).continuous.comp Units.continuous_val)
  · have heq : (positiveUnitGroup w : Set w.Completionˣ) = Set.univ := by
      ext x
      simp [positiveUnitGroup, hw]
    rw [heq]
    exact isOpen_univ

/-- The infinite local factor is positive at places in $P$ and unrestricted elsewhere.
Milne, *Class Field Theory*, version 4.03, Chapter V, §4, before Proposition 4.6. -/
noncomputable def rayUnitGroup (P : Set (NumberField.InfinitePlace K))
    (w : NumberField.InfinitePlace K) : Subgroup w.Completionˣ := by
  classical
  exact if w ∈ P then positiveUnitGroup w else ⊤

omit [NumberField K] in
/-- A place in $P$ contributes its positive component. -/
@[simp]
theorem rayUnitGroup_of_mem (P : Set (NumberField.InfinitePlace K))
    (w : NumberField.InfinitePlace K) (hw : w ∈ P) :
    rayUnitGroup P w = positiveUnitGroup w := by
  simp [rayUnitGroup, hw]

omit [NumberField K] in
/-- Requiring positivity at every infinite place gives the positive local group. -/
@[simp]
theorem rayUnitGroup_univ (w : NumberField.InfinitePlace K) :
    rayUnitGroup Set.univ w = positiveUnitGroup w := by
  simp

omit [NumberField K] in
/-- Every infinite local ray factor is open. -/
theorem isOpen_rayUnitGroup (P : Set (NumberField.InfinitePlace K))
    (w : NumberField.InfinitePlace K) :
    IsOpen (rayUnitGroup P w : Set w.Completionˣ) := by
  classical
  by_cases hw : w ∈ P
  · simpa [rayUnitGroup, hw] using isOpen_positiveUnitGroup w
  · simp [rayUnitGroup, hw]

omit [NumberField K] in
/-- Membership in an infinite ray factor is unrestricted outside $P$ and positive inside it. -/
@[simp]
theorem mem_rayUnitGroup_iff (P : Set (NumberField.InfinitePlace K))
    (w : NumberField.InfinitePlace K) (x : w.Completionˣ) :
    x ∈ rayUnitGroup P w ↔ w ∉ P ∨
      ∀ hw : w.IsReal, 0 < extensionEmbeddingOfIsReal hw (x : w.Completion) := by
  classical
  by_cases hw : w ∈ P
  · simp [rayUnitGroup, hw, positiveUnitGroup]
  · simp [rayUnitGroup, hw]

variable [NumberField.IsTotallyReal K]

/-- The real image of a global unit agrees with its image through the real completion. -/
theorem extensionEmbeddingOfIsReal_units_map
    (w : NumberField.InfinitePlace K) (x : Kˣ) :
    extensionEmbeddingOfIsReal (NumberField.IsTotallyReal.isReal w)
      ((Units.map (algebraMap K w.Completion) x : w.Completionˣ) : w.Completion) =
        realEmbeddingAt K w (x : K) := by
  change extensionEmbeddingOfIsReal (NumberField.IsTotallyReal.isReal w)
    (algebraMap K w.Completion (x : K)) = realEmbeddingAt K w (x : K)
  rw [InfinitePlace.Completion.algebraMap_apply]
  exact extensionEmbeddingOfIsReal_coe _ _

/-- A global unit belongs to the infinite ray factor exactly when the place is outside $P$ or
its real embedding is positive. -/
theorem units_map_mem_rayUnitGroup_iff
    (P : Set (NumberField.InfinitePlace K)) (w : NumberField.InfinitePlace K) (x : Kˣ) :
    Units.map (algebraMap K w.Completion) x ∈ rayUnitGroup P w ↔
      w ∉ P ∨ 0 < realEmbeddingAt K w (x : K) := by
  rw [mem_rayUnitGroup_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · apply Or.inr
      simpa only [extensionEmbeddingOfIsReal_units_map] using
        (h (NumberField.IsTotallyReal.isReal w))
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (fun hw ↦ by
        simpa only [extensionEmbeddingOfIsReal_units_map] using h)

end InfinitePlace

variable {K K' : Type*} [Field K] [Field K'] [NumberField K] [NumberField K']

/-! ### Moduli and higher unit groups

The exponents of a modulus and the finite ray factors move with the primes. -/

namespace FinitePlace

/-- The exponent of $\sigma(v)$ in $\sigma(\mathfrak m)$ is the exponent of `v` in `m`. -/
theorem modulusExponent_map (σ : K ≃+* K') (m : Ideal (𝓞 K)) (v : HeightOneSpectrum (𝓞 K)) :
    modulusExponent (m.map (RingOfIntegers.mapRingEquiv σ)) (mapEquiv σ v) =
      modulusExponent m v := by
  let e := RingOfIntegers.mapRingEquiv σ
  by_cases hm : m = ⊥
  · subst m
    change Multiset.count ((mapEquiv σ) v).asIdeal
        (normalizedFactors ((⊥ : Ideal (𝓞 K)).map e)) =
      Multiset.count v.asIdeal (normalizedFactors (0 : Ideal (𝓞 K)))
    rw [Ideal.map_bot]
    change Multiset.count ((mapEquiv σ) v).asIdeal
        (normalizedFactors (0 : Ideal (𝓞 K'))) =
      Multiset.count v.asIdeal (normalizedFactors (0 : Ideal (𝓞 K)))
    simp only [normalizedFactors_zero, Multiset.count_zero]
  have hm' : m.map e ≠ ⊥ := by
    exact fun h ↦ hm ((Ideal.map_eq_bot_iff_of_injective e.injective).mp h)
  rw [modulusExponent_eq_multiplicity hm', modulusExponent_eq_multiplicity hm,
    mapEquiv_asIdeal]
  exact multiplicity_mapEquiv σ v.asIdeal m

/-- The completion of `σ` maps the finite ray factor of `m` at `v` into that of
$\sigma(\mathfrak m)$ at $\sigma(v)$: $\sigma(U_v^{(k)}) \subseteq U_{\sigma v}^{(k)}$ for
$k = \operatorname{ord}_v\mathfrak m$. -/
theorem completionEquiv_mem_rayUnitGroup (σ : K ≃+* K') {m : Ideal (𝓞 K)}
    {v : HeightOneSpectrum (𝓞 K)} {x : (v.adicCompletion K)ˣ} (hx : x ∈ rayUnitGroup m v) :
    Units.map (completionEquiv σ v (mapEquiv σ v) rfl :
        v.adicCompletion K →* (mapEquiv σ v).adicCompletion K') x ∈
      rayUnitGroup (m.map (RingOfIntegers.mapRingEquiv σ)) (mapEquiv σ v) := by
  change Units.map _ x ∈ higherUnitGroup (mapEquiv σ v)
    (modulusExponent (m.map (RingOfIntegers.mapRingEquiv σ)) (mapEquiv σ v))
  rw [modulusExponent_map]
  change x ∈ higherUnitGroup v (modulusExponent m v) at hx
  rw [mem_higherUnitGroup_iff_valued] at hx ⊢
  constructor
  · change Valued.v (completionEquiv σ v (mapEquiv σ v) rfl
        (x : v.adicCompletion K)) = 1
    rw [valued_completionEquiv]
    exact hx.1
  · have hsub :
        ((Units.map (completionEquiv σ v (mapEquiv σ v) rfl :
            v.adicCompletion K →* (mapEquiv σ v).adicCompletion K') x :
              ((mapEquiv σ v).adicCompletion K')ˣ) :
          (mapEquiv σ v).adicCompletion K') - 1 =
          completionEquiv σ v (mapEquiv σ v) rfl
            ((x : v.adicCompletion K) - 1) := by
        change completionEquiv σ v (mapEquiv σ v) rfl (x : v.adicCompletion K) - 1 = _
        simp
    rw [hsub, valued_completionEquiv]
    exact hx.2

end FinitePlace


end SIC

end
