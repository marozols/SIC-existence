/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The Euler product of the Dedekind zeta function

For real $s>1$, the Dedekind zeta function is the sum of $N\mathfrak a^{-s}$ over the ideals of
$\mathcal O_K$ and the product of $(1-N\mathfrak p^{-s})^{-1}$ over its nonzero primes.

This module follows Milne, *Class Field Theory*, version 4.03 (2020), Chapter VI, Example 1.1(b),
in the real variable. It supplies the Euler product from which `SICs.ClassField.Density.PrimeSum`
derives the prime-sum asymptotics of Chapter VI, Lemma 4.3 and Proposition 4.4(a).

## The argument

Mathlib defines $\zeta_K$ as the $L$-series whose $n$th coefficient counts the ideals of norm
$n$. For real $s>1$ its terms are nonnegative, so grouping the ideals by their norms rewrites it
as the sum of $N\mathfrak a^{-s}$ over all ideals; the zero ideal contributes $0^{-s}=0$.

For a finite set $F$ of nonzero primes, unique factorization of ideals in the Dedekind domain
$\mathcal O_K$ makes $e\mapsto\prod_{\mathfrak p\in F}\mathfrak p^{e_{\mathfrak p}}$ a bijection
from exponent vectors on $F$ onto the nonzero ideals whose prime factors lie in $F$, and the
absolute norm is multiplicative. Expanding the product of the geometric series
$\prod_{\mathfrak p\in F}\sum_{k\ge0}N\mathfrak p^{-ks}$ therefore gives the sum of
$N\mathfrak a^{-s}$ over those ideals. Every finite set of nonzero ideals is supported on a finite
set of primes, and all terms are nonnegative, so the finite partial products increase to the full
sum.
-/

namespace SIC

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open Ideal NumberField.InfinitePlace NumberField.Units nonZeroDivisors
open Filter Finset Asymptotics
open scoped Topology

variable (K : Type*) [Field K] [NumberField K]

/-! ### The Dedekind zeta function as a sum over ideals

At real $s>1$ the $L$-series of the ideal counts is the sum of $N\mathfrak a^{-s}$ over all
ideals. -/

/-- The ideal-count $L$-series converges for real $s>1$; used by
`summable_absNorm_rpow`. -/
private theorem norm_count_lseries {s : ℝ} (hs : 1 < s) :
    LSeriesSummable (fun n ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) s := by
  let f : ℕ → ℝ := fun n ↦ Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}
  have hlim : Tendsto (fun n : ℕ ↦
      (∑ k ∈ Icc 1 n, (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ)) / (n : ℝ))
      atTop
      (𝓝 ((2 ^ nrRealPlaces K * (2 * Real.pi) ^ nrComplexPlaces K * regulator K *
        classNumber K) / (torsionOrder K * Real.sqrt |discr K|))) := by
    refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr
      fun n ↦ ?_
    simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
    congr
    rw [← add_left_inj 1, ← card_norm_le_eq_card_norm_le_add_one,
      show Icc 1 n = Ioc 0 n from Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 K) // absNorm I = 0} by
        simp [Ideal.absNorm_eq_zero_iff],
      sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← card_preimage_eq_sum_card_image_eq (fun k _ ↦ finite_setOfPred_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  have hO : (fun n ↦ ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
    exact isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa [f] using hlim)
  exact LSeriesSummable_of_sum_norm_bigO_and_nonneg hO (fun _ ↦ Nat.cast_nonneg _)
    zero_le_one (by simpa using hs)

/-- The $n$th ideal-count $L$-series term is the real ideal count times $n^{-s}$; used by
`summable_absNorm_rpow` and `dedekindZeta_ofReal`. -/
private theorem norm_count_term {s : ℝ} (hs : 1 < s) (n : ℕ) :
    LSeries.term (fun n ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ))
      (s : ℂ) n =
      (((Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) *
        (n : ℝ) ^ (-s) : ℝ) : ℂ) := by
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term_zero, Real.zero_rpow (by linarith : -s ≠ 0)]
  · rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg]
    simp only [Complex.ofReal_mul, Complex.ofReal_cpow (by positivity : 0 ≤ (n : ℝ)),
      Complex.ofReal_neg, Complex.ofReal_natCast]

/-- The sum over ideals of norm $n$ is their count times $n^{-s}$; used by
`summable_absNorm_rpow` and `dedekindZeta_ofReal`. -/
private theorem norm_fiber_sum (s : ℝ) (n : ℕ) :
    (∑' I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}, (Ideal.absNorm I.1 : ℝ) ^ (-s)) =
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s) := by
  simp only [show ∀ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n},
    (Ideal.absNorm I.1 : ℝ) ^ (-s) = (n : ℝ) ^ (-s) from fun I ↦ by rw [I.property]]
  simp

/-- The real ideal-count terms are summable; used by `summable_absNorm_rpow`. -/
private theorem norm_count_real_summable {s : ℝ} (hs : 1 < s) : Summable (fun n : ℕ ↦
    (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s)) := by
  apply Complex.summable_ofReal.mp
  exact (norm_count_lseries K hs).congr (norm_count_term K hs)

/-- For real $s>1$ the terms $N\mathfrak a^{-s}$ over the ideals $\mathfrak a$ of $\mathcal O_K$
are summable; the zero ideal contributes $0^{-s}=0$. Milne, *Class Field Theory*, Chapter VI,
Example 1.1(b). -/
theorem summable_absNorm_rpow {s : ℝ} (hs : 1 < s) :
    Summable fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ) ^ (-s) := by
  let g : Ideal (𝓞 K) → ℝ := fun I ↦ (Ideal.absNorm I : ℝ) ^ (-s)
  have hpart : Summable g ↔
      (∀ n : ℕ, Summable fun I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n} ↦ g I.1) ∧
      Summable (fun n : ℕ ↦ ∑' I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}, g I.1) := by
    apply summable_partition
    · intro I; exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · intro I
      exact ⟨Ideal.absNorm I, rfl, fun n hn ↦ hn.symm⟩
  apply hpart.mpr
  constructor
  · intro n
    exact (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n).summable g
  · exact (norm_count_real_summable K hs).congr (fun n ↦ (norm_fiber_sum K s n).symm)

/-- The prime ideal terms $N\mathfrak p^{-s}$ are summable for $s>1$.
Milne, *Class Field Theory*, Chapter VI, Example 1.1(b). -/
theorem summable_absNorm_rpow_heightOneSpectrum {s : ℝ} (hs : 1 < s) :
    Summable fun p : HeightOneSpectrum (𝓞 K) => (Ideal.absNorm p.asIdeal : ℝ) ^ (-s) := by
  simpa only [Function.comp_def] using
    (summable_absNorm_rpow K hs).comp_injective HeightOneSpectrum.asIdeal_injective

/-- For real $s>1$, $\zeta_K(s)=\sum_{\mathfrak a}N\mathfrak a^{-s}$, the sum over the ideals of
$\mathcal O_K$. Milne, *Class Field Theory*, Chapter VI, Example 1.1(b). -/
theorem dedekindZeta_ofReal {s : ℝ} (hs : 1 < s) :
    dedekindZeta K s = ((∑' I : Ideal (𝓞 K), (Ideal.absNorm I : ℝ) ^ (-s) : ℝ) : ℂ) := by
  have hsum := summable_absNorm_rpow K hs
  have hfib := hsum.hasSum.tsum_fiberwise Ideal.absNorm
  calc
    dedekindZeta K s =
        ∑' n : ℕ, (((Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) *
          (n : ℝ) ^ (-s) : ℝ) : ℂ) := by
      unfold dedekindZeta LSeries
      exact tsum_congr (norm_count_term K hs)
    _ = (((∑' n : ℕ, (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) *
          (n : ℝ) ^ (-s)) : ℝ) : ℂ) := (Complex.ofReal_tsum _).symm
    _ = ((∑' I : Ideal (𝓞 K), (Ideal.absNorm I : ℝ) ^ (-s) : ℝ) : ℂ) := by
      congr 1
      rw [← hfib.tsum_eq]
      exact tsum_congr (fun n ↦ (norm_fiber_sum K s n).symm)

/-! ### The Euler product

The partial products over finite sets of primes are the partial sums over the ideals supported
on those primes. -/

variable {P : Type*}

/-- The multisets whose entries lie in a finite set of primes; used by `supported_product`. -/
private def supported (F : Finset P) : Set (Multiset P) :=
  {m | ∀ p ∈ m, p ∈ F}

/-- Separates the multiplicity of a new prime from a supported multiset;
used by `supported_product`. -/
private def splitAt [DecidableEq P] (F : Finset P) (p : P) (hp : p ∉ F) :
    supported (insert p F) ≃ ℕ × supported F where
  toFun m := (m.1.count p, ⟨m.1.filter (p ≠ ·), by
    intro q hq
    obtain ⟨hm, hne⟩ := Multiset.mem_filter.mp hq
    exact (Finset.mem_insert.mp (m.2 q hm)).resolve_left (fun h => hne h.symm)⟩)
  invFun x := ⟨Multiset.replicate x.1 p + x.2.1, by
    intro q hq
    obtain hq | hq := Multiset.mem_add.mp hq
    · have : q = p := (Multiset.mem_replicate.mp hq).2
      simp [this]
    · exact Finset.mem_insert_of_mem (x.2.2 q hq)⟩
  left_inv := by
    intro m
    apply Subtype.ext
    change Multiset.replicate (Multiset.count p m.1) p +
      Multiset.filter (p ≠ ·) m.1 = m.1
    rw [← Multiset.filter_eq m.1 p]
    exact Multiset.filter_add_not (Eq p) m.1
  right_inv := by
    intro x
    apply Prod.ext
    · simp [Multiset.count_add, Multiset.count_eq_zero.mpr (by
        intro h
        exact hp (x.2.2 p h))]
    · apply Subtype.ext
      change Multiset.filter (p ≠ ·) (Multiset.replicate x.1 p + x.2.1) = x.2.1
      rw [Multiset.filter_add]
      have hrest : Multiset.filter (p ≠ ·) x.2.1 = x.2.1 := by
        apply Multiset.filter_eq_self.mpr
        intro q hq hqp
        exact hp (hqp ▸ x.2.2 q hq)
      have hrep : Multiset.filter (p ≠ ·) (Multiset.replicate x.1 p) = 0 := by
        rw [← Multiset.filter_false (Multiset.replicate x.1 p)]
        apply Multiset.filter_congr
        intro a ha
        simp [(Multiset.mem_replicate.mp ha).2]
      simp only [hrep, hrest, zero_add]

/-- The multiplicative weight of a multiset; used by `hasProd_weight`. -/
private def weight (w : P → ℝ) (m : Multiset P) : ℝ := (m.map w).prod

/-- The multiset weight respects addition; used by `weight_split`. -/
private theorem weight_add (w : P → ℝ) (m n : Multiset P) :
    weight w (m + n) = weight w m * weight w n := by
  simp [weight, Multiset.map_add, Multiset.prod_add]

/-- The weight of repeated prime factors; used by `weight_split`. -/
private theorem weight_replicate (w : P → ℝ) (k : ℕ) (p : P) :
    weight w (Multiset.replicate k p) = w p ^ k := by
  simp [weight, Multiset.map_replicate, Multiset.prod_replicate]

/-- The weight factors under `splitAt`; used by `supported_product`. -/
private theorem weight_split [DecidableEq P] (w : P → ℝ) (F : Finset P) (p : P)
    (hp : p ∉ F) (x : ℕ × supported F) :
    weight w ((splitAt F p hp).symm x).1 = w p ^ x.1 * weight w x.2.1 := by
  change weight w (Multiset.replicate x.1 p + x.2.1) = _
  rw [weight_add, weight_replicate]

/-- Summability on supported multisets follows from global summability;
used by `supported_product`. -/
private theorem supported_summable (w : P → ℝ)
    (hsum : Summable (weight w)) (F : Finset P) :
    Summable fun m : supported F => weight w m.1 :=
  hsum.comp_injective Subtype.val_injective

/-- The empty prime set contributes just the empty multiset; used by `supported_product`. -/
private theorem supported_empty (w : P → ℝ) :
    (∑' m : supported (∅ : Finset P), weight w m.1) = 1 := by
  let m0 : supported (∅ : Finset P) := ⟨0, by simp [supported]⟩
  have hsub : ∀ m : supported (∅ : Finset P), m = m0 := by
    intro m
    apply Subtype.ext
    rcases Multiset.empty_or_exists_mem m.1 with h | ⟨p, hp⟩
    · exact h
    · simpa using m.2 p hp
  rw [tsum_eq_single m0 (fun m hm => (hm (hsub m)).elim)]
  simp [m0, weight]

/-- A finite product of geometric series is the sum over supported multisets;
used by `hasProd_weight`. -/
private theorem supported_product (w : P → ℝ)
    (hw0 : ∀ p, 0 ≤ w p) (hw1 : ∀ p, w p < 1)
    (hsum : Summable (weight w)) (F : Finset P) :
    (∑' m : supported F, weight w m.1) = ∏ p ∈ F, (1 - w p)⁻¹ := by
  classical
  induction F using Finset.induction with
  | empty => simpa using supported_empty w
  | @insert p F hp ih =>
    let e := splitAt F p hp
    have he : (∑' m : supported (insert p F), weight w m.1) =
        ∑' x : ℕ × supported F, w p ^ x.1 * weight w x.2.1 := by
      rw [← e.symm.tsum_eq (fun m : supported (insert p F) => weight w m.1)]
      exact tsum_congr (fun x => weight_split w F p hp x)
    have hprod : Summable (fun x : ℕ × supported F => w p ^ x.1 * weight w x.2.1) := by
      have h := (supported_summable w hsum (insert p F)).comp_injective e.symm.injective
      exact h.congr (fun x => weight_split w F p hp x)
    rw [he, ← (summable_geometric_of_lt_one (hw0 p) (hw1 p)).tsum_mul_tsum
      (supported_summable w hsum F) hprod, tsum_geometric_of_lt_one (hw0 p) (hw1 p), ih]
    simp [hp, mul_comm]

/-- Nonnegative local weights give nonnegative multiset weights; used by `supported_tsum_le`. -/
private theorem weight_nonneg (w : P → ℝ) (hw0 : ∀ p, 0 ≤ w p) (m : Multiset P) :
    0 ≤ weight w m := by
  induction m using Multiset.induction with
  | empty => simp [weight]
  | cons p m ih => simpa [weight] using mul_nonneg (hw0 p) ih

/-- A supported subseries is bounded by the full series; used by `supported_tsum_isLUB`. -/
private theorem supported_tsum_le (w : P → ℝ) (hw0 : ∀ p, 0 ≤ w p)
    (hsum : Summable (weight w)) (F : Finset P) :
    (∑' m : supported F, weight w m.1) ≤ ∑' m : Multiset P, weight w m := by
  rw [_root_.tsum_subtype]
  apply (hsum.indicator (supported F)).tsum_le_tsum _ hsum
  intro m
  by_cases hm : m ∈ supported F
  · simp [Set.indicator_of_mem hm]
  · simp [Set.indicator_of_notMem hm, weight_nonneg w hw0 m]

/-- A finite multiset sum is bounded by a suitable supported subseries;
used by `supported_tsum_isLUB`. -/
private theorem finite_sum_le_supported_tsum [DecidableEq P] (w : P → ℝ)
    (hw0 : ∀ p, 0 ≤ w p) (hsum : Summable (weight w)) (M : Finset (Multiset P)) :
    ∑ m ∈ M, weight w m ≤
      ∑' m : supported (M.biUnion Multiset.toFinset), weight w m.1 := by
  let F : Finset P := M.biUnion Multiset.toFinset
  have hM : ∀ m ∈ M, m ∈ supported F := by
    intro m hm p hp
    exact Finset.mem_biUnion.mpr ⟨m, hm, Multiset.mem_toFinset.mpr hp⟩
  calc
    ∑ m ∈ M, weight w m = ∑ m ∈ M, (supported F).indicator (weight w) m := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Set.indicator_of_mem (hM m hm)]
    _ ≤ ∑' m : Multiset P, (supported F).indicator (weight w) m := by
      apply (hsum.indicator (supported F)).sum_le_tsum M
      intro m hm
      by_cases h : m ∈ supported F
      · simp [Set.indicator_of_mem h, weight_nonneg w hw0 m]
      · simp [Set.indicator_of_notMem h]
    _ = ∑' m : supported F, weight w m.1 := (_root_.tsum_subtype _ _).symm

/-- Supported subseries grow as the prime set grows; used by `hasProd_weight`. -/
private theorem supported_tsum_mono (w : P → ℝ) (hw0 : ∀ p, 0 ≤ w p)
    (hsum : Summable (weight w)) {F G : Finset P} (hFG : F ⊆ G) :
    (∑' m : supported F, weight w m.1) ≤ ∑' m : supported G, weight w m.1 := by
  rw [_root_.tsum_subtype, _root_.tsum_subtype]
  apply (hsum.indicator (supported F)).tsum_le_tsum _ (hsum.indicator (supported G))
  intro m
  by_cases hF : m ∈ supported F
  · have hG : m ∈ supported G := fun p hp => hFG (hF p hp)
    simp [Set.indicator_of_mem hF, Set.indicator_of_mem hG]
  · rw [Set.indicator_of_notMem hF]
    by_cases hG : m ∈ supported G
    · simp [Set.indicator_of_mem hG, weight_nonneg w hw0 m]
    · simp [Set.indicator_of_notMem hG]

/-- The supported subseries have supremum equal to the full series; used by `hasProd_weight`. -/
private theorem supported_tsum_isLUB (w : P → ℝ)
    (hw0 : ∀ p, 0 ≤ w p) (hsum : Summable (weight w)) :
    IsLUB (Set.range (fun F : Finset P => ∑' m : supported F, weight w m.1))
      (∑' m : Multiset P, weight w m) := by
  classical
  apply (isLUB_iff_le_iff).mpr
  intro c
  constructor
  · intro hc a ha
    obtain ⟨F, rfl⟩ := ha
    exact (supported_tsum_le w hw0 hsum F).trans hc
  · intro hc
    apply hsum.tsum_le_of_sum_le
    intro M
    change (∀ a ∈ Set.range (fun F : Finset P =>
      ∑' m : supported F, weight w m.1), a ≤ c) at hc
    exact (finite_sum_le_supported_tsum w hw0 hsum M).trans
      (hc _ ⟨M.biUnion Multiset.toFinset, rfl⟩)

/-- The multiset Euler product for a summable multiplicative weight;
used by `hasProd_inv_one_sub_absNorm_rpow`. -/
private theorem hasProd_weight (w : P → ℝ)
    (hw0 : ∀ p, 0 ≤ w p) (hw1 : ∀ p, w p < 1)
    (hsum : Summable (weight w)) :
    HasProd (fun p => (1 - w p)⁻¹) (∑' m : Multiset P, weight w m) := by
  classical
  have hlim := tendsto_atTop_isLUB
    (fun F G hFG => supported_tsum_mono w hw0 hsum hFG)
    (supported_tsum_isLUB w hw0 hsum)
  change Filter.Tendsto (fun F : Finset P => ∏ p ∈ F, (1 - w p)⁻¹)
    Filter.atTop (nhds (∑' m : Multiset P, weight w m))
  convert hlim using 1
  ext F
  exact (supported_product w hw0 hw1 hsum F).symm


/-- The ideal associated to a multiset of nonzero prime ideals; used by `primeEquiv`. -/
private def primeProd (m : Multiset (HeightOneSpectrum (𝓞 K))) : Ideal (𝓞 K) :=
  (m.map fun p => p.asIdeal).prod

/-- The normalized factors of a prime-ideal product are its factors;
used by `primeProd_injective`. -/
private theorem primeProd_factors (m : Multiset (HeightOneSpectrum (𝓞 K))) :
    normalizedFactors (primeProd K m) = m.map fun p => p.asIdeal := by
  unfold primeProd
  apply normalizedFactors_prod_of_prime
  intro p hp
  obtain ⟨v, _, rfl⟩ := Multiset.mem_map.mp hp
  exact v.prime

omit [NumberField K] in
/-- A finite product of nonzero prime ideals is nonzero; used by `primeEquiv`. -/
private theorem primeProd_ne_zero (m : Multiset (HeightOneSpectrum (𝓞 K))) :
    primeProd K m ≠ 0 := by
  unfold primeProd
  apply Multiset.prod_ne_zero
  simp [HeightOneSpectrum.ne_bot]

/-- The prime-ideal product is injective by unique factorization; used by `primeEquiv`. -/
private theorem primeProd_injective : Function.Injective (primeProd K) := by
  intro m n h
  have h' : Multiset.map (fun p : HeightOneSpectrum (𝓞 K) => p.asIdeal) m =
      Multiset.map (fun p : HeightOneSpectrum (𝓞 K) => p.asIdeal) n := by
    rw [← primeProd_factors K m, ← primeProd_factors K n, h]
  exact Multiset.map_injective HeightOneSpectrum.asIdeal_injective h'

/-- The multiset of prime factors of a nonzero ideal; used by `primeEquiv`. -/
private noncomputable def primeMultisetOfIdeal (I : {I : Ideal (𝓞 K) // I ≠ 0}) :
    Multiset (HeightOneSpectrum (𝓞 K)) :=
  (normalizedFactors I.1).pmap
    (fun _ hp => HeightOneSpectrum.ofPrime hp)
    (fun p hp => prime_of_normalized_factor p hp)

/-- Mapping the prime-factor multiset to ideals recovers the normalized factors;
used by `primeEquiv`. -/
private theorem primeMultisetOfIdeal_map (I : {I : Ideal (𝓞 K) // I ≠ 0}) :
    (primeMultisetOfIdeal K I).map (fun p => p.asIdeal) = normalizedFactors I.1 := by
  unfold primeMultisetOfIdeal
  rw [Multiset.map_pmap]
  simp [HeightOneSpectrum.ofPrime, Multiset.pmap_eq_map]

/-- The product of the prime factors recovers a nonzero ideal; used by `primeEquiv`. -/
private theorem primeProd_primeMultisetOfIdeal (I : {I : Ideal (𝓞 K) // I ≠ 0}) :
    primeProd K (primeMultisetOfIdeal K I) = I.1 := by
  unfold primeProd
  rw [primeMultisetOfIdeal_map, Ideal.prod_normalizedFactors_eq_self I.2]

/-- Unique factorization identifies prime multisets with nonzero ideals;
used by `prime_weight_tsum`. -/
private noncomputable def primeEquiv : Multiset (HeightOneSpectrum (𝓞 K)) ≃
    {I : Ideal (𝓞 K) // I ≠ 0} where
  toFun m := ⟨primeProd K m, primeProd_ne_zero K m⟩
  invFun := primeMultisetOfIdeal K
  left_inv := by
    intro m
    apply primeProd_injective K
    exact primeProd_primeMultisetOfIdeal K ⟨primeProd K m, primeProd_ne_zero K m⟩
  right_inv := by
    intro I
    apply Subtype.ext
    exact primeProd_primeMultisetOfIdeal K I

/-- The ideal norm weight is the product of its prime-factor weights;
used by `prime_weight_summable`. -/
private theorem primeProd_weight (s : ℝ) (m : Multiset (HeightOneSpectrum (𝓞 K))) :
    (Ideal.absNorm (primeProd K m) : ℝ) ^ (-s) =
      (m.map (fun p => (Ideal.absNorm p.asIdeal : ℝ) ^ (-s))).prod := by
  induction m using Multiset.induction with
  | empty => simp [primeProd]
  | cons p m ih =>
    have hp : (0 : ℝ) ≤ Ideal.absNorm p.asIdeal := Nat.cast_nonneg _
    have hm : (0 : ℝ) ≤ Ideal.absNorm (primeProd K m) := Nat.cast_nonneg _
    simp only [primeProd, Multiset.map_cons, Multiset.prod_cons]
    rw [map_mul, Nat.cast_mul, Real.mul_rpow hp (by simpa only [primeProd] using hm)]
    rw [show (Multiset.map (fun p => p.asIdeal) m).prod = primeProd K m from rfl, ih]

/-- The local prime norm weight is nonnegative; used by `hasProd_inv_one_sub_absNorm_rpow`. -/
private theorem prime_weight_nonneg (s : ℝ)
    (p : HeightOneSpectrum (𝓞 K)) :
    0 ≤ (Ideal.absNorm p.asIdeal : ℝ) ^ (-s) :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- The local prime norm weight is less than one; used by `hasProd_inv_one_sub_absNorm_rpow`. -/
private theorem prime_weight_lt_one {s : ℝ} (hs : 1 < s)
    (p : HeightOneSpectrum (𝓞 K)) :
    (Ideal.absNorm p.asIdeal : ℝ) ^ (-s) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p) (by linarith)

/-- Summability transfers from ideals to their prime multisets;
used by `hasProd_inv_one_sub_absNorm_rpow`. -/
private theorem prime_weight_summable {s : ℝ} (hs : 1 < s) :
    Summable (weight (fun p : HeightOneSpectrum (𝓞 K) =>
      (Ideal.absNorm p.asIdeal : ℝ) ^ (-s))) := by
  have h := (summable_absNorm_rpow K hs).comp_injective
    (Subtype.val_injective : Function.Injective
      (fun I : {I : Ideal (𝓞 K) // I ≠ 0} => I.1))
  have h' := h.comp_injective (primeEquiv K).injective
  exact h'.congr (fun m => primeProd_weight K s m)

/-- The multiset series equals the ideal norm series; used by `hasProd_inv_one_sub_absNorm_rpow`. -/
private theorem prime_weight_tsum {s : ℝ} (hs : 1 < s) :
    (∑' m : Multiset (HeightOneSpectrum (𝓞 K)),
      weight (fun p => (Ideal.absNorm p.asIdeal : ℝ) ^ (-s)) m) =
      ∑' I : Ideal (𝓞 K), (Ideal.absNorm I : ℝ) ^ (-s) := by
  calc
    _ = ∑' I : {I : Ideal (𝓞 K) // I ≠ 0}, (Ideal.absNorm I.1 : ℝ) ^ (-s) := by
      rw [← (primeEquiv K).tsum_eq
        (fun I : {I : Ideal (𝓞 K) // I ≠ 0} => (Ideal.absNorm I.1 : ℝ) ^ (-s))]
      exact tsum_congr (fun m => (primeProd_weight K s m).symm)
    _ = ∑' I : Ideal (𝓞 K), (Ideal.absNorm I : ℝ) ^ (-s) := by
      apply tsum_subtype_eq_of_support_subset
        (s := {I : Ideal (𝓞 K) | I ≠ 0})
        (f := fun I => (Ideal.absNorm I : ℝ) ^ (-s))
      intro I hI
      by_contra hI0
      have heq : I = 0 := by simpa using hI0
      subst I
      exact hI (by simp [Ideal.absNorm_bot, Real.zero_rpow (by linarith : -s ≠ 0)])

/-- **Euler product** of the Dedekind zeta function at real $s>1$:
$\sum_{\mathfrak a}N\mathfrak a^{-s}=\prod_{\mathfrak p}(1-N\mathfrak p^{-s})^{-1}$, the product
over the nonzero primes of $\mathcal O_K$. Milne, *Class Field Theory*, Chapter VI,
Example 1.1(b). -/
theorem hasProd_inv_one_sub_absNorm_rpow {s : ℝ} (hs : 1 < s) :
    HasProd (fun 𝔭 : HeightOneSpectrum (𝓞 K) => (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s))⁻¹)
      (∑' I : Ideal (𝓞 K), (Ideal.absNorm I : ℝ) ^ (-s)) := by
  classical
  rw [← prime_weight_tsum K hs]
  exact hasProd_weight _ (prime_weight_nonneg K s) (prime_weight_lt_one K hs)
    (prime_weight_summable K hs)

end SIC
