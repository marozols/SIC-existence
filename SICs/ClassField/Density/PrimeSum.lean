/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Density.EulerProduct
import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Ideal.Int

/-!
# Densities of sets of primes

The sum of $N\mathfrak p^{-s}$ over all primes, and over the primes of absolute degree one, of a
number field differs from $\log\frac1{s-1}$ by a bounded function as $s\downarrow1$.

This module follows Milne, *Class Field Theory*, version 4.03 (2020), Chapter VI, §4: the
Dirichlet density of a set of primes, its elementary properties (Proposition 4.4),
the logarithm of an Euler product (Lemma 4.3), and the density of the primes of absolute degree
one (Proposition 4.5, using the estimate of Proposition 3.2). It supplies the input of the
splitting densities in `SICs.ClassField.Density.Splitting`.

## The argument

Milne's Dirichlet density of a set $T$ of nonzero primes is a $\delta$ such that
$\sum_{\mathfrak p\in T}N\mathfrak p^{-s}-\delta\log\frac1{s-1}$ is bounded for real
$s\in(1,1+\epsilon)$ (his relation $f\sim g$ of Chapter VI, §4); here `HasPrimeDensity T δ`.
Mathlib's `NumberField.Set.HasDirichletDensity` is the weaker statement that the
ratio of the prime sums tends to $\delta$. Finite sets have density zero, densities add over
disjoint unions, and since $\log\frac1{s-1}\to\infty$ a density is unique and a set of nonzero
density is infinite.

Taking logarithms in the Euler product gives
$\log\zeta_K(s)=\sum_{\mathfrak p}-\log(1-N\mathfrak p^{-s})$. Since
$-\log(1-x)-x\le 2x^2$ for $0\le x\le\frac12$, this differs from
$\sum_{\mathfrak p}N\mathfrak p^{-s}$ by at most $2\sum_{\mathfrak p}N\mathfrak p^{-2}$, which is
finite. Mathlib's residue of $\zeta_K$ at $s=1$ (the class number formula) is positive, so
$\log((s-1)\zeta_K(s))$ stays bounded: all primes have density one.

A prime whose norm is not a rational prime has norm $p^f$ with $f\ge2$, where $p$ is the
rational prime below it, and at most $[K:\mathbb Q]$ primes lie above each $p$. The sum of
$N\mathfrak p^{-s}$ over those primes is therefore at most $[K:\mathbb Q]\sum_p p^{-2}$ for
$s\ge1$, so they have density zero and the primes of absolute degree one have density one.
-/

namespace SIC

open NumberField IsDedekindDomain Filter Topology Asymptotics

variable {K : Type*} [Field K] [NumberField K]

/-! ### Dirichlet densities

Milne's real-variable Dirichlet density and its elementary properties. -/

/-- The primes in `T` have **Dirichlet density** $\delta$:
$\sum_{\mathfrak p\in T}N\mathfrak p^{-s}-\delta\log\frac1{s-1}$ is bounded for real
$s\downarrow1$. Milne, *Class Field Theory*, Chapter VI, §4, where this is the relation
$\sum_{\mathfrak p\in T}N\mathfrak p^{-s}\sim\delta\log\frac1{s-1}$. Mathlib's
`NumberField.Set.HasDirichletDensity` is the weaker ratio form. -/
def HasPrimeDensity (T : Set (HeightOneSpectrum (𝓞 K))) (δ : ℝ) : Prop :=
  (fun s : ℝ => T.primeIdealZetaSum s - δ * Real.log (1 / (s - 1))) =O[𝓝[>] 1]
    fun _ => (1 : ℝ)

/-- For real $s>1$ the terms $N\mathfrak p^{-s}$ over any set of nonzero primes are summable.
Milne, *Class Field Theory*, Chapter VI, §4. -/
theorem summable_absNorm_rpow_primes (T : Set (HeightOneSpectrum (𝓞 K))) {s : ℝ} (hs : 1 < s) :
    Summable fun 𝔭 : T => (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) := by
  exact (summable_absNorm_rpow_heightOneSpectrum K hs).comp_injective Subtype.val_injective

/-- A finite set of primes has Dirichlet density zero. Milne, *Class Field Theory*, Chapter VI,
Proposition 4.4(c). -/
theorem hasPrimeDensity_of_finite {T : Set (HeightOneSpectrum (𝓞 K))} (hT : T.Finite) :
    HasPrimeDensity T 0 := by
  change (fun s : ℝ => T.primeIdealZetaSum s - 0 * Real.log (1 / (s - 1))) =O[𝓝[>] 1]
    fun _ => (1 : ℝ)
  simpa only [zero_mul, sub_zero] using
    (Asymptotics.isBigO_iff.mpr ⟨(T.ncard : ℝ), by
      filter_upwards [eventually_mem_nhdsWithin] with s hs
      have hs' : 0 ≤ s := le_trans (by norm_num) (le_of_lt hs)
      simpa only [Real.norm_eq_abs, abs_of_nonneg (T.primeIdealZetaSum_nonneg s),
        norm_one, mul_one] using T.primeIdealZetaSum_le_card_of_finite hT hs'⟩)

/-- The prime sum of a disjoint union is the sum of its prime sums. -/
private theorem primeIdealZetaSum_union {T₁ T₂ : Set (HeightOneSpectrum (𝓞 K))}
    (hd : Disjoint T₁ T₂) {s : ℝ} (hs : 1 < s) :
    (T₁ ∪ T₂).primeIdealZetaSum s =
      T₁.primeIdealZetaSum s + T₂.primeIdealZetaSum s := by
  have hsum := Summable.tsum_union_disjoint
    (f := fun 𝔭 : HeightOneSpectrum (𝓞 K) => (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) hd
    (by simpa only [Function.comp_def] using summable_absNorm_rpow_primes T₁ hs)
    (by simpa only [Function.comp_def] using summable_absNorm_rpow_primes T₂ hs)
  exact hsum

/-- Dirichlet densities add over disjoint unions. Milne, *Class Field Theory*, Chapter VI,
Proposition 4.4(d). -/
theorem HasPrimeDensity.union {T₁ T₂ : Set (HeightOneSpectrum (𝓞 K))} {δ₁ δ₂ : ℝ}
    (h₁ : HasPrimeDensity T₁ δ₁) (h₂ : HasPrimeDensity T₂ δ₂) (hd : Disjoint T₁ T₂) :
    HasPrimeDensity (T₁ ∪ T₂) (δ₁ + δ₂) := by
  apply (h₁.add h₂).congr' _ (Filter.Eventually.of_forall fun _ => rfl)
  filter_upwards [eventually_mem_nhdsWithin] with s hs
  rw [primeIdealZetaSum_union hd hs]
  ring

/-- Removing a subset of Dirichlet density $\delta_1$ from a set of density $\delta$ leaves
density $\delta-\delta_1$. Milne, *Class Field Theory*, Chapter VI, Proposition 4.4(d). -/
theorem HasPrimeDensity.diff {T T₁ : Set (HeightOneSpectrum (𝓞 K))} {δ δ₁ : ℝ}
    (h : HasPrimeDensity T δ) (h₁ : HasPrimeDensity T₁ δ₁) (hsub : T₁ ⊆ T) :
    HasPrimeDensity (T \ T₁) (δ - δ₁) := by
  have hd : Disjoint T₁ (T \ T₁) := Set.disjoint_left.mpr (by
    intro x hx hy
    exact hy.2 hx)
  have heq : T₁ ∪ (T \ T₁) = T := Set.union_sdiff_cancel hsub
  apply (h.sub h₁).congr' _ (Filter.Eventually.of_forall fun _ => rfl)
  filter_upwards [eventually_mem_nhdsWithin] with s hs
  have hsum := primeIdealZetaSum_union hd hs
  rw [heq] at hsum
  rw [hsum]
  ring

/-- Changing finitely many primes does not change their Dirichlet density.
Milne, *Class Field Theory*, Chapter VI, Proposition 4.4(c), (d). -/
theorem HasPrimeDensity.congr_finite {T T' : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ}
    (h : HasPrimeDensity T δ) (h₁ : (T \ T').Finite) (h₂ : (T' \ T).Finite) :
    HasPrimeDensity T' δ := by
  have hcommon : HasPrimeDensity (T ∩ T') δ := by
    have hdiff := h.diff (hasPrimeDensity_of_finite h₁) Set.sdiff_subset
    simpa only [sub_zero, Set.sdiff_sdiff_right_self] using hdiff
  have hnew := hcommon.union (hasPrimeDensity_of_finite h₂) (by
    exact Set.disjoint_left.mpr (fun _ hx hy => hy.2 hx.1))
  have heq : (T ∩ T') ∪ (T' \ T) = T' := by
    rw [Set.inter_comm T T']
    exact Set.inter_union_sdiff T' T
  simpa only [heq, add_zero] using hnew

/-- A Dirichlet density is unique, since $\log\frac1{s-1}\to\infty$ as $s\downarrow1$. Milne,
*Class Field Theory*, Chapter VI, §4. -/
theorem HasPrimeDensity.unique {T : Set (HeightOneSpectrum (𝓞 K))} {δ δ' : ℝ}
    (h : HasPrimeDensity T δ) (h' : HasPrimeDensity T δ') : δ = δ' := by
  by_contra hne
  have hmul : (fun s : ℝ => (δ - δ') * Real.log (1 / (s - 1))) =O[𝓝[>] 1]
      fun _ => (1 : ℝ) := by
    apply (h'.sub h).congr' _ (Filter.Eventually.of_forall fun _ => rfl)
    exact Filter.Eventually.of_forall (fun s => by dsimp; ring)
  have hlog : (fun s : ℝ => Real.log (1 / (s - 1))) =O[𝓝[>] 1]
      fun _ => (1 : ℝ) := (isBigO_const_mul_left_iff (sub_ne_zero.mpr hne)).mp hmul
  have hsub : Tendsto (fun s : ℝ => s - 1) (𝓝[>] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : Continuous (fun s : ℝ => s - 1) := continuous_id.sub continuous_const
      simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
    · filter_upwards [eventually_mem_nhdsWithin] with s hs
      exact sub_pos.mpr (show 1 < s from hs)
  have htop : Tendsto (fun s : ℝ => Real.log (1 / (s - 1))) (𝓝[>] 1) atTop := by
    simpa only [Function.comp_def, one_div] using Real.tendsto_log_atTop.comp
      (tendsto_inv_nhdsGT_zero.comp hsub)
  exact (not_isBoundedUnder_of_tendsto_atTop (tendsto_norm_atTop_atTop.comp htop))
    ((isBigO_one_iff ℝ).mp hlog)

/-- A set of primes of nonzero Dirichlet density is infinite. Milne, *Class Field Theory*,
Chapter VI, Proposition 4.4(c). -/
theorem HasPrimeDensity.infinite {T : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ}
    (h : HasPrimeDensity T δ) (hδ : δ ≠ 0) : T.Infinite := by
  intro hfinite
  exact hδ (h.unique (hasPrimeDensity_of_finite hfinite))

/-! ### All primes and the primes of absolute degree one

The logarithm of the Euler product and the residue of $\zeta_K$ at $s=1$ give density one for
all primes; the primes of higher absolute degree contribute a bounded sum. -/

/-- The logarithms of the Euler factors are summable for $s>1$, as used in
`log_ideal_sum_eq_tsum_prime` and `prime_log_error_bounded`. -/
private lemma summable_neg_log_prime {s : ℝ} (hs : 1 < s) :
    Summable fun 𝔭 : HeightOneSpectrum (𝓞 K) =>
      -Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) := by
  have hxsum := summable_absNorm_rpow_heightOneSpectrum K hs
  simpa only [sub_eq_add_neg] using
    (Real.summable_log_one_add_of_summable hxsum.neg).neg

/-- The logarithm of the Euler product is the sum of the logarithms of its local factors,
as in Milne, *Class Field Theory*, Chapter VI, Lemma 4.3. -/
private theorem log_ideal_sum_eq_tsum_prime {s : ℝ} (hs : 1 < s) :
    Real.log (∑' I : Ideal (𝓞 K), (Ideal.absNorm I : ℝ) ^ (-s)) =
      ∑' 𝔭 : HeightOneSpectrum (𝓞 K),
        -Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) := by
  let x (𝔭 : HeightOneSpectrum (𝓞 K)) : ℝ := (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)
  have hxlt (𝔭 : HeightOneSpectrum (𝓞 K)) : x 𝔭 < 1 := by
    have hn : (1 : ℝ) < Ideal.absNorm 𝔭.asIdeal := by
      exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm 𝔭
    exact Real.rpow_lt_one_of_one_lt_of_neg hn (by linarith)
  have hpos (𝔭 : HeightOneSpectrum (𝓞 K)) : 0 < (1 - x 𝔭)⁻¹ :=
    inv_pos.mpr (sub_pos.mpr (hxlt 𝔭))
  have hlogsum : Summable (fun 𝔭 => -Real.log (1 - x 𝔭)) :=
    summable_neg_log_prime hs
  have hprod : HasProd (fun 𝔭 => (1 - x 𝔭)⁻¹)
      (Real.exp (∑' 𝔭, -Real.log (1 - x 𝔭))) := by
    apply Real.hasProd_of_hasSum_log hpos
    simpa only [Real.log_inv] using hlogsum.hasSum
  have hZ := hasProd_inv_one_sub_absNorm_rpow (K := K) hs
  have hEq : (∑' I : Ideal (𝓞 K), (Ideal.absNorm I : ℝ) ^ (-s)) =
      Real.exp (∑' 𝔭, -Real.log (1 - x 𝔭)) := by
    exact hZ.unique hprod
  rw [hEq, Real.log_exp]

/-- The error after replacing $-\log(1-x)$ by $x$ is at most $2x^2$ for $x\le 1/2$;
this is the bound used in `hasPrimeDensity_univ`. -/
private lemma neg_log_one_sub_error_le {x : ℝ} (hx : x ≤ 1 / 2) :
    0 ≤ -Real.log (1 - x) - x ∧ -Real.log (1 - x) - x ≤ 2 * x ^ 2 := by
  have hden : 0 < 1 - x := by linarith
  have hlog1 := Real.log_le_sub_one_of_pos hden
  have hlog2 := Real.log_le_sub_one_of_pos (inv_pos.mpr hden)
  rw [Real.log_inv] at hlog2
  have hinv : (1 - x)⁻¹ ≤ 2 := by
    calc
      (1 - x)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := (inv_le_inv₀ hden (by norm_num)).mpr (by linarith)
      _ = 2 := by norm_num
  constructor
  · linarith
  · calc
      -Real.log (1 - x) - x ≤ (1 - x)⁻¹ - 1 - x := by linarith
      _ = x ^ 2 * (1 - x)⁻¹ := by field_simp; ring
      _ ≤ 2 * x ^ 2 := by nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hinv)]

/-- A prime term $N\mathfrak p^{-s}$ is at most $1/2$ for $s>1$, as used in
`hasPrimeDensity_univ`. -/
private lemma prime_rpow_le_half {s : ℝ} (hs : 1 < s)
    (𝔭 : HeightOneSpectrum (𝓞 K)) :
    (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≤ 1 / 2 := by
  have hn : (2 : ℝ) ≤ Ideal.absNorm 𝔭.asIdeal := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm 𝔭
  have hn1 : (1 : ℝ) ≤ Ideal.absNorm 𝔭.asIdeal := by linarith
  calc
    (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≤
        (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    _ = (Ideal.absNorm 𝔭.asIdeal : ℝ)⁻¹ := by
      rw [Real.rpow_neg (by positivity), Real.rpow_one]
    _ ≤ (2 : ℝ)⁻¹ := (inv_le_inv₀ (by positivity) (by norm_num)).mpr hn
    _ = 1 / 2 := by norm_num

/-- Squared prime terms for $s>1$ are dominated by the terms at $s=2$, as used in
`hasPrimeDensity_univ`. -/
private lemma prime_rpow_sq_le_two {s : ℝ} (hs : 1 < s)
    (𝔭 : HeightOneSpectrum (𝓞 K)) :
    ((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) ^ 2 ≤
      (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-2 : ℝ) := by
  have hn : (2 : ℝ) ≤ Ideal.absNorm 𝔭.asIdeal := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm 𝔭
  have hn1 : (1 : ℝ) ≤ Ideal.absNorm 𝔭.asIdeal := by linarith
  have hx : (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≤
      (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hx0 : 0 ≤ (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) := Real.rpow_nonneg (by linarith) _
  have hy0 : 0 ≤ (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_nonneg (by linarith) _
  have hsq : ((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) ^ 2 ≤
      ((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-1 : ℝ)) ^ 2 := by nlinarith
  calc
    _ ≤ ((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-1 : ℝ)) ^ 2 := hsq
    _ = (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith :
        0 ≤ (Ideal.absNorm 𝔭.asIdeal : ℝ))]
      norm_num

/-- The error in one Euler factor is nonnegative and bounded by its norm's reciprocal square;
this is the pointwise estimate for `prime_log_error_bounded`. -/
private lemma prime_log_error_pointwise {s : ℝ} (hs : 1 < s)
    (𝔭 : HeightOneSpectrum (𝓞 K)) :
    0 ≤ -Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) -
      (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ∧
    -Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) -
      (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≤
        2 * (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-2 : ℝ) := by
  have h := neg_log_one_sub_error_le (prime_rpow_le_half hs 𝔭)
  refine ⟨h.1, h.2.trans ?_⟩
  gcongr
  exact prime_rpow_sq_le_two hs 𝔭

/-- The sum of Euler-factor errors is bounded uniformly for $s>1$, as used in
`prime_log_error_bounded`. -/
private lemma prime_log_error_tsum_bound {s : ℝ} (hs : 1 < s) :
    0 ≤ (∑' 𝔭 : HeightOneSpectrum (𝓞 K),
      (-Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) -
        (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s))) ∧
    (∑' 𝔭 : HeightOneSpectrum (𝓞 K),
      (-Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) -
        (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s))) ≤
      2 * ∑' 𝔭 : HeightOneSpectrum (𝓞 K),
        (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-2 : ℝ) := by
  have hsumx := summable_absNorm_rpow_heightOneSpectrum K hs
  have hsum2 := summable_absNorm_rpow_heightOneSpectrum K (s := 2) (by norm_num)
  have hrem := (summable_neg_log_prime (K := K) hs).sub hsumx
  constructor
  · exact tsum_nonneg (fun 𝔭 => (prime_log_error_pointwise hs 𝔭).1)
  · simpa only [tsum_mul_left] using
      (Summable.tsum_le_tsum (fun 𝔭 => (prime_log_error_pointwise hs 𝔭).2)
        hrem (hsum2.mul_left 2))

/-- The logarithm of the Euler product and the prime sum differ by a bounded amount near
$s=1$, as in Milne, *Class Field Theory*, Chapter VI, Lemma 4.3. -/
private theorem prime_log_error_bounded :
    (fun s : ℝ =>
      Real.log (∑' I : Ideal (𝓞 K), (Ideal.absNorm I : ℝ) ^ (-s)) -
        (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s) =O[𝓝[>] 1]
      fun _ => (1 : ℝ) := by
  let C : ℝ := 2 * ∑' 𝔭 : HeightOneSpectrum (𝓞 K),
    (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-2 : ℝ)
  apply isBigO_iff.mpr
  refine ⟨C, ?_⟩
  filter_upwards [eventually_mem_nhdsWithin] with s hs
  have hsumx := summable_absNorm_rpow_heightOneSpectrum K hs
  have hlog := summable_neg_log_prime (K := K) hs
  have heq : Real.log (∑' I : Ideal (𝓞 K), (Ideal.absNorm I : ℝ) ^ (-s)) -
      (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s =
        ∑' 𝔭 : HeightOneSpectrum (𝓞 K),
          (-Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) -
            (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) := by
    rw [log_ideal_sum_eq_tsum_prime hs]
    rw [NumberField.Set.primeIdealZetaSum_def]
    have huniv : (∑' 𝔭 : (Set.univ : Set (HeightOneSpectrum (𝓞 K))),
        (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)) =
        ∑' 𝔭 : HeightOneSpectrum (𝓞 K), (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) :=
      tsum_univ (fun 𝔭 : HeightOneSpectrum (𝓞 K) =>
        (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s))
    rw [huniv]
    exact (hlog.tsum_sub hsumx).symm
  have hb := prime_log_error_tsum_bound (K := K) hs
  rw [heq, Real.norm_eq_abs, abs_of_nonneg hb.1, norm_one, mul_one]
  exact hb.2

/-- The pole of the Dedekind zeta function gives the logarithmic pole term in
`hasPrimeDensity_univ`; Milne, *Class Field Theory*, Chapter VI, Corollary 2.12. -/
private theorem log_ideal_sum_sub_log_pole_bounded :
    (fun s : ℝ =>
      Real.log (∑' I : Ideal (𝓞 K), (Ideal.absNorm I : ℝ) ^ (-s)) -
        Real.log (1 / (s - 1))) =O[𝓝[>] 1] fun _ => (1 : ℝ) := by
  have hresComplex := NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K
  have hres : Tendsto (fun s : ℝ =>
      (s - 1) * ∑' I : Ideal (𝓞 K), (Ideal.absNorm I : ℝ) ^ (-s))
      (𝓝[>] 1) (𝓝 (dedekindZeta_residue K)) := by
    have hre := (Complex.continuous_re.tendsto
      ((dedekindZeta_residue K : ℝ) : ℂ)).comp hresComplex
    apply hre.congr'
    filter_upwards [eventually_mem_nhdsWithin] with s hs
    change (((s : ℂ) - 1) * dedekindZeta K s).re = _
    rw [dedekindZeta_ofReal K hs]
    simp [Complex.mul_re]
  have hlogres := hres.log (dedekindZeta_residue_pos K).ne'
  have hpos : ∀ᶠ s in 𝓝[>] (1 : ℝ),
      0 < (s - 1) * ∑' I : Ideal (𝓞 K), (Ideal.absNorm I : ℝ) ^ (-s) :=
    hres.eventually (Ioi_mem_nhds (dedekindZeta_residue_pos K))
  apply (hlogres.isBigO_one ℝ).congr' _ (Filter.Eventually.of_forall fun _ => rfl)
  filter_upwards [eventually_mem_nhdsWithin, hpos] with s hs hzs
  have hs0 : s - 1 ≠ 0 := (sub_pos.mpr hs).ne'
  have hz0 : (∑' I : Ideal (𝓞 K), (Ideal.absNorm I : ℝ) ^ (-s)) ≠ 0 := by
    have hz : 0 < ∑' I : Ideal (𝓞 K), (Ideal.absNorm I : ℝ) ^ (-s) :=
      (mul_pos_iff_of_pos_left (sub_pos.mpr hs)).mp hzs
    exact hz.ne'
  rw [Real.log_mul hs0 hz0, one_div, Real.log_inv]
  ring

/-- All nonzero primes of $K$ have Dirichlet density one:
$\sum_{\mathfrak p}N\mathfrak p^{-s}-\log\frac1{s-1}$ is bounded as $s\downarrow1$. Milne,
*Class Field Theory*, Chapter VI, Proposition 4.4(a), proved by Lemma 4.3 and Corollary 2.12. -/
theorem hasPrimeDensity_univ : HasPrimeDensity (Set.univ : Set (HeightOneSpectrum (𝓞 K))) 1 := by
  have h := (log_ideal_sum_sub_log_pole_bounded (K := K)).sub
    (prime_log_error_bounded (K := K))
  apply h.congr' _ (Filter.Eventually.of_forall fun _ => rfl)
  exact Filter.Eventually.of_forall (fun s => by dsimp [HasPrimeDensity]; ring)

/-- The rational prime below a nonzero prime of the integers of $K$, used in
`hasPrimeDensity_nonprimeNorm`. -/
private noncomputable def rationalPrimeBelow (𝔭 : HeightOneSpectrum (𝓞 K)) : Nat.Primes := by
  letI : (𝔭.asIdeal).IsPrime := 𝔭.isPrime
  letI : NeZero 𝔭.asIdeal := ⟨𝔭.ne_bot⟩
  exact ⟨Ideal.absNorm (𝔭.asIdeal.under ℤ), Nat.absNorm_under_prime 𝔭.asIdeal⟩

/-- The norm of a prime ideal is a power of its rational prime below, as used in
`hasPrimeDensity_nonprimeNorm`. -/
private lemma prime_absNorm_eq_pow_below (𝔭 : HeightOneSpectrum (𝓞 K)) :
    Ideal.absNorm 𝔭.asIdeal = (rationalPrimeBelow 𝔭).1 ^ 𝔭.asIdeal.inertiaDeg ℤ := by
  have : (𝔭.asIdeal).LiesOver
      (Ideal.span {((rationalPrimeBelow 𝔭).1 : ℤ)}) := Int.liesOver_span_absNorm 𝔭.asIdeal
  exact (Ideal.pow_inertiaDeg (rationalPrimeBelow 𝔭).1 𝔭.asIdeal).symm

/-- A prime ideal whose norm is not prime has inertia degree at least two, as used in
`hasPrimeDensity_nonprimeNorm`. -/
private lemma two_le_inertiaDeg_of_not_prime (𝔭 : HeightOneSpectrum (𝓞 K))
    (h𝔭 : ¬ (Ideal.absNorm 𝔭.asIdeal).Prime) : 2 ≤ 𝔭.asIdeal.inertiaDeg ℤ := by
  have hpos : 0 < 𝔭.asIdeal.inertiaDeg ℤ := Ideal.inertiaDeg_pos 𝔭.asIdeal ℤ
  by_contra h
  have hf : 𝔭.asIdeal.inertiaDeg ℤ = 1 := by omega
  have hnorm : Ideal.absNorm 𝔭.asIdeal = (rationalPrimeBelow 𝔭).1 := by
    simpa only [hf, pow_one] using prime_absNorm_eq_pow_below 𝔭
  exact h𝔭 (hnorm ▸ (rationalPrimeBelow 𝔭).2)

/-- The contribution of a prime of absolute degree at least two is bounded by the reciprocal
square of the rational prime below, as used in `hasPrimeDensity_nonprimeNorm`. -/
private lemma prime_rpow_le_below_sq {s : ℝ} (hs : 1 ≤ s)
    (𝔭 : HeightOneSpectrum (𝓞 K)) (h𝔭 : ¬ (Ideal.absNorm 𝔭.asIdeal).Prime) :
    (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≤ ((rationalPrimeBelow 𝔭).1 : ℝ) ^ (-2 : ℝ) := by
  have hnorm : ((rationalPrimeBelow 𝔭).1 : ℝ) ^ 2 ≤ Ideal.absNorm 𝔭.asIdeal := by
    exact_mod_cast (show (rationalPrimeBelow 𝔭).1 ^ 2 ≤ Ideal.absNorm 𝔭.asIdeal by
      rw [prime_absNorm_eq_pow_below]
      exact pow_le_pow_right₀ (rationalPrimeBelow 𝔭).2.one_lt.le
        (two_le_inertiaDeg_of_not_prime 𝔭 h𝔭))
  have hp0 : (0 : ℝ) < (rationalPrimeBelow 𝔭).1 := by
    exact_mod_cast (rationalPrimeBelow 𝔭).2.pos
  have hp : 0 < ((rationalPrimeBelow 𝔭).1 : ℝ) ^ 2 := by positivity
  have hn : 1 ≤ (Ideal.absNorm 𝔭.asIdeal : ℝ) := by
    exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm 𝔭).le
  calc
    (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≤
        (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn (by linarith)
    _ ≤ (((rationalPrimeBelow 𝔭).1 : ℝ) ^ 2) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hp hnorm (by norm_num)
    _ = ((rationalPrimeBelow 𝔭).1 : ℝ) ^ (-2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num

/-- At most $[K:\mathbb Q]$ prime ideals lie above a fixed rational prime, as used in
`hasPrimeDensity_nonprimeNorm`. -/
private lemma prime_fiber_card_le (T : Set (HeightOneSpectrum (𝓞 K))) (F : Finset T)
    (q : Nat.Primes) :
    (F.filter fun 𝔭 => rationalPrimeBelow 𝔭.1 = q).card ≤ Module.finrank ℤ (𝓞 K) := by
  classical
  let Q : Ideal ℤ := Ideal.span {(q.1 : ℤ)}
  have hQprime : Q.IsPrime := by
    dsimp [Q]
    apply (Ideal.span_singleton_prime (by exact_mod_cast q.2.ne_zero)).mpr
    exact Nat.prime_iff_prime_int.mp q.2
  have hQmax : Q.IsMaximal := hQprime.isMaximal (by
    dsimp [Q]
    simpa using q.2.ne_zero)
  have hcard : Fintype.card (Q.primesOver (𝓞 K)) ≤ Module.finrank ℤ (𝓞 K) := by
    calc
      Fintype.card (Q.primesOver (𝓞 K)) = ∑ P : Q.primesOver (𝓞 K), (1 : ℕ) := by simp
      _ ≤ ∑ P : Q.primesOver (𝓞 K), P.1.ramificationIdx ℤ * P.1.inertiaDeg ℤ := by
        apply Finset.sum_le_sum
        intro P _
        have hP : P.1.IsPrime := P.2.1
        have hram : 0 < P.1.ramificationIdx ℤ := Ideal.ramificationIdx_pos P.1 ℤ
        have hinertia : 0 < P.1.inertiaDeg ℤ := Ideal.inertiaDeg_pos P.1 ℤ
        nlinarith
      _ = Module.finrank ℤ (𝓞 K) := Ideal.sum_ramification_inertia_eq_finrank Q (𝓞 K)
  have hinj : (F.filter fun 𝔭 => rationalPrimeBelow 𝔭.1 = q).card ≤
      Fintype.card (Q.primesOver (𝓞 K)) := by
    rw [← Fintype.card_coe]
    let e : (F.filter fun 𝔭 => rationalPrimeBelow 𝔭.1 = q) → Q.primesOver (𝓞 K) :=
      fun 𝔭 => ⟨𝔭.1.1.asIdeal, by
        have hbelow : rationalPrimeBelow 𝔭.1.1 = q := (Finset.mem_filter.mp 𝔭.2).2
        have hlie : 𝔭.1.1.asIdeal.LiesOver
            (Ideal.span {(((rationalPrimeBelow 𝔭.1.1).1 : ℕ) : ℤ)}) :=
          Int.liesOver_span_absNorm 𝔭.1.1.asIdeal
        rw [hbelow] at hlie
        exact ⟨𝔭.1.1.isPrime, hlie⟩⟩
    apply Fintype.card_le_of_injective e
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact HeightOneSpectrum.asIdeal_injective (congrArg Subtype.val hab)
  exact hinj.trans hcard

/-- Finite sums over primes of absolute degree greater than one are bounded by the convergent
sum of inverse squares of rational primes; Milne, *Class Field Theory*, Chapter VI,
Proposition 3.2. -/
private lemma sum_not_prime_le (F : Finset
    {𝔭 : HeightOneSpectrum (𝓞 K) | ¬ (Ideal.absNorm 𝔭.asIdeal).Prime})
    {s : ℝ} (hs : 1 ≤ s) :
    ∑ 𝔭 ∈ F, (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) ≤
      (Module.finrank ℤ (𝓞 K) : ℝ) *
        ∑' q : Nat.Primes, (q.1 : ℝ) ^ (-2 : ℝ) := by
  classical
  let g : {𝔭 : HeightOneSpectrum (𝓞 K) | ¬ (Ideal.absNorm 𝔭.asIdeal).Prime} →
      Nat.Primes := fun 𝔭 => rationalPrimeBelow 𝔭.1
  let U : Finset Nat.Primes := F.image g
  have hgroup : ∑ 𝔭 ∈ F, (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) =
      ∑ q ∈ U, ∑ 𝔭 ∈ F with g 𝔭 = q,
        (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) := by
    exact (Finset.sum_fiberwise_of_maps_to
      (s := F) (t := U) (g := g) (fun 𝔭 h𝔭 => Finset.mem_image_of_mem g h𝔭)
      (fun 𝔭 => (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s))).symm
  rw [hgroup]
  calc
    (∑ q ∈ U, ∑ 𝔭 ∈ F with g 𝔭 = q,
        (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)) ≤
        ∑ q ∈ U, (Module.finrank ℤ (𝓞 K) : ℝ) * (q.1 : ℝ) ^ (-2 : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      calc
        (∑ 𝔭 ∈ F with g 𝔭 = q,
            (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)) ≤
            ∑ 𝔭 ∈ F with g 𝔭 = q, (q.1 : ℝ) ^ (-2 : ℝ) := by
          apply Finset.sum_le_sum
          intro 𝔭 h𝔭
          have hbelow : g 𝔭 = q := (Finset.mem_filter.mp h𝔭).2
          simpa only [g, hbelow] using prime_rpow_le_below_sq hs 𝔭.1 𝔭.2
        _ = ((F.filter fun 𝔭 => g 𝔭 = q).card : ℝ) * (q.1 : ℝ) ^ (-2 : ℝ) := by
          simp [mul_comm]
        _ ≤ (Module.finrank ℤ (𝓞 K) : ℝ) * (q.1 : ℝ) ^ (-2 : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast prime_fiber_card_le _ F q
    _ = (Module.finrank ℤ (𝓞 K) : ℝ) * ∑ q ∈ U, (q.1 : ℝ) ^ (-2 : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ (Module.finrank ℤ (𝓞 K) : ℝ) *
        ∑' q : Nat.Primes, (q.1 : ℝ) ^ (-2 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact (Nat.Primes.summable_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).sum_le_tsum U
        (fun _ _ => by positivity)

/-- The nonzero primes whose absolute norm is not a rational prime have Dirichlet density zero.
Milne, *Class Field Theory*, Chapter VI, Proposition 3.2, in the real variable. -/
theorem hasPrimeDensity_nonprimeNorm :
    HasPrimeDensity {𝔭 : HeightOneSpectrum (𝓞 K) | ¬ (Ideal.absNorm 𝔭.asIdeal).Prime} 0 := by
  let T : Set (HeightOneSpectrum (𝓞 K)) :=
    {𝔭 | ¬ (Ideal.absNorm 𝔭.asIdeal).Prime}
  let C : ℝ := (Module.finrank ℤ (𝓞 K) : ℝ) *
    ∑' q : Nat.Primes, (q.1 : ℝ) ^ (-2 : ℝ)
  change (fun s : ℝ => T.primeIdealZetaSum s - 0 * Real.log (1 / (s - 1))) =O[𝓝[>] 1]
    fun _ => (1 : ℝ)
  simpa only [zero_mul, sub_zero] using
    (isBigO_iff.mpr ⟨C, by
      filter_upwards [eventually_mem_nhdsWithin] with s hs
      have hbound : T.primeIdealZetaSum s ≤ C := by
        exact Real.tsum_le_of_sum_le (fun 𝔭 => Real.rpow_nonneg (by positivity) _)
          (fun F => sum_not_prime_le F (le_of_lt hs))
      simpa only [Real.norm_eq_abs, abs_of_nonneg (T.primeIdealZetaSum_nonneg s),
        norm_one, mul_one] using hbound⟩)

/-- The nonzero primes of absolute degree one, those whose absolute norm is a rational prime,
have Dirichlet density one. Milne, *Class Field Theory*, Chapter VI, Proposition 4.5. -/
theorem hasPrimeDensity_degreeOne :
    HasPrimeDensity {𝔭 : HeightOneSpectrum (𝓞 K) | (Ideal.absNorm 𝔭.asIdeal).Prime} 1 := by
  have h := (hasPrimeDensity_univ (K := K)).diff (hasPrimeDensity_nonprimeNorm (K := K))
    (Set.subset_univ _)
  convert h using 1
  · ext 𝔭
    simp
  · norm_num

end SIC
