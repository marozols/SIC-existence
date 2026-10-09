/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Density.PrimeSum
import SICs.ClassField.Splitting.PrimeCount

/-!
# The density of completely split primes

In a finite Galois extension $L/K$, the primes of $K$ of absolute degree one that split
completely in $L$ have Dirichlet density $1/[L:K]$.

This module follows Milne, *Class Field Theory*, version 4.03 (2020), Chapter VI, Theorem 3.4,
in the real-variable form of Chapter VI, §4, restricted to primes of absolute degree one. It is
the analytic input of `SICs.ClassField.Frobenius.DegreeOne`.

## The argument

Let $n=[L:K]$. A prime $\mathfrak P$ of $L$ of absolute degree one lies above a prime
$\mathfrak p$ of $K$ with $N\mathfrak P=N\mathfrak p^{f(\mathfrak P|\mathfrak p)}$, so
$\mathfrak p$ has absolute degree one and $f(\mathfrak P|\mathfrak p)=1$. Away from the finitely
many ramified primes, $\mathfrak p$ then splits completely; conversely a completely split
$\mathfrak p$ of absolute degree one has exactly $n$ primes above it, each of norm
$N\mathfrak p$. Hence, outside the primes of $L$ above ramified primes (a finite set), the prime
sum of $L$ over its primes of absolute degree one is $n$ times the prime sum of $K$ over its
completely split primes of absolute degree one. The former has density one
(`hasPrimeDensity_degreeOne` for $L$), so the latter has density $1/n$.
-/

namespace SIC

open NumberField IsDedekindDomain Filter Topology Asymptotics

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L]
  [Algebra K L]

/-! ### Norms and the fibres over completely split primes

The norm identity identifies the primes of absolute degree one above an unramified base prime.
-/

/-- A prime of absolute degree one lies over a prime of absolute degree one with residue degree
one. Used by `primeIdealZetaSum_splitsCompletely`. -/
private theorem degreeOne_below (w : HeightOneSpectrum (𝓞 L))
    (hw : (Ideal.absNorm w.asIdeal).Prime) :
    (Ideal.absNorm (FinitePlace.below (K := K) w).asIdeal).Prime ∧
      w.asIdeal.inertiaDeg (𝓞 K) = 1 := by
  have hnorm := Ideal.absNorm_pow_inertiaDeg
    (FinitePlace.below (K := K) w).asIdeal w.asIdeal
  have hpow : (Ideal.absNorm (FinitePlace.below (K := K) w).asIdeal ^
      w.asIdeal.inertiaDeg (𝓞 K)).Prime := by
    rw [hnorm]
    exact hw
  have hf := Nat.Prime.eq_one_of_pow hpow
  have heq : Ideal.absNorm (FinitePlace.below (K := K) w).asIdeal =
      Ideal.absNorm w.asIdeal := by simpa [hf] using hnorm
  exact ⟨heq.symm ▸ hw, hf⟩

/-- Every prime above a completely split prime of absolute degree one has prime norm. Used by
`primeIdealZetaSum_splitsCompletely`. -/
private theorem degreeOne_above_split [IsGalois K L] (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (hv : (Ideal.absNorm v.asIdeal).Prime) (hsplit : FinitePlace.SplitsCompletely L v) :
    (Ideal.absNorm w.asIdeal).Prime := by
  rw [hsplit.absNorm_eq w]
  exact hv

/-- Away from ramification, primes of absolute degree one in `L` correspond to a completely
split prime of `K` and a choice of prime above it. Used by
`primeIdealZetaSum_splitsCompletely`. -/
private noncomputable def degreeOneUnramifiedEquiv [IsGalois K L] :
    (Σ v : {v : HeightOneSpectrum (𝓞 K) |
          (Ideal.absNorm v.asIdeal).Prime ∧ FinitePlace.SplitsCompletely L v ∧
            v ∉ FinitePlace.ramifiedSet K L},
        {w : HeightOneSpectrum (𝓞 L) | FinitePlace.below (K := K) w = v.1}) ≃
      {w : HeightOneSpectrum (𝓞 L) |
        (Ideal.absNorm w.asIdeal).Prime ∧
          FinitePlace.below (K := K) w ∉ FinitePlace.ramifiedSet K L} := by
  refine Equiv.sigmaSubtypeFiberEquivSubtype
    (f := FinitePlace.below (K := K) (L := L)) ?_
  intro w
  constructor
  · intro hw
    have hdegree := degreeOne_below (K := K) L w hw.1
    have hsplit : FinitePlace.SplitsCompletely L (FinitePlace.below (K := K) w) :=
      (FinitePlace.splitsCompletely_iff (FinitePlace.below (K := K) w) w).2
        ⟨FinitePlace.ramificationIdx_eq_one_of_notMem_ramifiedSet (K := K) w hw.2,
          hdegree.2⟩
    exact ⟨hdegree.1, hsplit, hw.2⟩
  · intro hv
    have hdegree := degreeOne_above_split (K := K) L
      (FinitePlace.below (K := K) w) w hv.1 hv.2.1
    exact ⟨hdegree, hv.2.2⟩

/-! ### Regrouping the prime sum

Each completely split prime outside the ramified set contributes `[L : K]` equal terms.
-/

/-- The fibre above a completely split prime contributes `[L : K]` equal norm terms to the
prime sum. Used by `primeIdealZetaSum_splitsCompletely`. -/
private theorem primeIdealZetaSum_fiber [IsGalois K L] (v : HeightOneSpectrum (𝓞 K))
    (hv : FinitePlace.SplitsCompletely L v) (s : ℝ) :
    (∑' w : {w : HeightOneSpectrum (𝓞 L) | FinitePlace.below (K := K) w = v},
      (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-s)) =
      (Module.finrank K L : ℝ) * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s) := by
  classical
  let ev := FinitePlace.PrimeAbove.equivFiber (L := L) v
  let _ : Fintype {w : HeightOneSpectrum (𝓞 L) |
      FinitePlace.below (K := K) w = v} := Fintype.ofEquiv _ ev
  have hcard : Fintype.card {w : HeightOneSpectrum (𝓞 L) |
      FinitePlace.below (K := K) w = v} = Module.finrank K L := by
    calc
      _ = Fintype.card (FinitePlace.PrimeAbove (L := L) v) :=
        (Fintype.card_congr ev).symm
      _ = (v.asIdeal.primesOver (𝓞 L)).ncard := Set.fintypeCard_eq_ncard _
      _ = Module.finrank K L := hv
  have hnorm (w : {w : HeightOneSpectrum (𝓞 L) |
      FinitePlace.below (K := K) w = v}) :
      Ideal.absNorm w.1.asIdeal = Ideal.absNorm v.asIdeal := by
    have : w.1.asIdeal.LiesOver v.asIdeal :=
      ⟨(congrArg HeightOneSpectrum.asIdeal w.2).symm⟩
    exact hv.absNorm_eq w.1
  simp_rw [hnorm]
  simp [tsum_fintype, Finset.sum_const, hcard, nsmul_eq_mul]

/-- Outside ramification, the absolute-degree-one prime sum of `L` is `[L : K]` times the
completely split absolute-degree-one prime sum of `K`. This is the regrouping in Milne,
*Class Field Theory*, Chapter VI, proof of Theorem 3.4, used by
`hasPrimeDensity_splitsCompletely`. -/
private theorem primeIdealZetaSum_splitsCompletely [IsGalois K L] {s : ℝ} (hs : 1 < s) :
    ({w : HeightOneSpectrum (𝓞 L) |
        (Ideal.absNorm w.asIdeal).Prime ∧
          FinitePlace.below (K := K) w ∉ FinitePlace.ramifiedSet K L} :
        Set (HeightOneSpectrum (𝓞 L))).primeIdealZetaSum s =
      (Module.finrank K L : ℝ) *
        ({v : HeightOneSpectrum (𝓞 K) |
            (Ideal.absNorm v.asIdeal).Prime ∧ FinitePlace.SplitsCompletely L v ∧
              v ∉ FinitePlace.ramifiedSet K L} :
          Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s := by
  classical
  let S : Set (HeightOneSpectrum (𝓞 K)) :=
    {v | (Ideal.absNorm v.asIdeal).Prime ∧ FinitePlace.SplitsCompletely L v ∧
      v ∉ FinitePlace.ramifiedSet K L}
  let U : Set (HeightOneSpectrum (𝓞 L)) :=
    {w | (Ideal.absNorm w.asIdeal).Prime ∧
      FinitePlace.below (K := K) w ∉ FinitePlace.ramifiedSet K L}
  let e : (Σ v : S,
      {w : HeightOneSpectrum (𝓞 L) | FinitePlace.below (K := K) w = v.1}) ≃ U :=
    degreeOneUnramifiedEquiv (K := K) L
  have he (p : Σ v : S,
      {w : HeightOneSpectrum (𝓞 L) | FinitePlace.below (K := K) w = v.1}) :
      (e p).1 = p.2.1 := rfl
  have hsum : Summable (fun w : U => (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-s)) :=
    summable_absNorm_rpow_primes U hs
  have hSigma : Summable (fun p : Σ v : S,
      {w : HeightOneSpectrum (𝓞 L) | FinitePlace.below (K := K) w = v.1} =>
        (Ideal.absNorm p.2.1.asIdeal : ℝ) ^ (-s)) := by
    have h := (e.summable_iff).2 hsum
    exact h.congr (fun p => by simp only [Function.comp_apply, he p])
  change U.primeIdealZetaSum s = (Module.finrank K L : ℝ) * S.primeIdealZetaSum s
  calc
    U.primeIdealZetaSum s =
        ∑' p : Σ v : S,
          {w : HeightOneSpectrum (𝓞 L) | FinitePlace.below (K := K) w = v.1},
            (Ideal.absNorm p.2.1.asIdeal : ℝ) ^ (-s) := by
      exact (e.tsum_eq (fun w : U => (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-s))).symm
    _ = ∑' v : S, ∑' w : {w : HeightOneSpectrum (𝓞 L) |
          FinitePlace.below (K := K) w = v.1},
            (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-s) := hSigma.tsum_sigma
    _ = ∑' v : S, (Module.finrank K L : ℝ) *
          (Ideal.absNorm v.1.asIdeal : ℝ) ^ (-s) := by
      apply tsum_congr
      intro v
      exact primeIdealZetaSum_fiber (K := K) L v.1 v.2.2.1 s
    _ = (Module.finrank K L : ℝ) * S.primeIdealZetaSum s := by
      rw [tsum_mul_left]
      rfl

/-! ### Density after removing ramified primes

The finitely many primes above ramification do not change density. The regrouping identity then
scales the density by the reciprocal of the extension degree.
-/

/-- The absolute-degree-one primes of `L` above unramified primes of `K` have density one.
Used by `hasPrimeDensity_split_awayRamification`. -/
private theorem hasPrimeDensity_degreeOne_awayRamification :
    HasPrimeDensity {w : HeightOneSpectrum (𝓞 L) |
      (Ideal.absNorm w.asIdeal).Prime ∧
        FinitePlace.below (K := K) w ∉ FinitePlace.ramifiedSet K L} 1 := by
  classical
  let R := FinitePlace.ramifiedSet K L
  have hRamAbove :
      {w : HeightOneSpectrum (𝓞 L) | FinitePlace.below (K := K) w ∈ R}.Finite := by
    convert (FinitePlace.placesAbove (L := L) R).finite_toSet using 1
    ext w
    simp [R]
  apply (hasPrimeDensity_degreeOne (K := L)).congr_finite
  · exact hRamAbove.subset (fun _ hw => by
      by_contra hr
      exact hw.2 ⟨hw.1, hr⟩)
  · exact Set.finite_empty.subset (fun _ hw => hw.2 hw.1.1)

/-- Completely split primes of absolute degree one outside ramification have density
`1 / [L : K]`. Used by `hasPrimeDensity_splitsCompletely`. -/
private theorem hasPrimeDensity_split_awayRamification [IsGalois K L] :
    HasPrimeDensity {v : HeightOneSpectrum (𝓞 K) |
      (Ideal.absNorm v.asIdeal).Prime ∧ FinitePlace.SplitsCompletely L v ∧
        v ∉ FinitePlace.ramifiedSet K L} (Module.finrank K L : ℝ)⁻¹ := by
  let S : Set (HeightOneSpectrum (𝓞 K)) :=
    {v | (Ideal.absNorm v.asIdeal).Prime ∧ FinitePlace.SplitsCompletely L v ∧
      v ∉ FinitePlace.ramifiedSet K L}
  let U : Set (HeightOneSpectrum (𝓞 L)) :=
    {w | (Ideal.absNorm w.asIdeal).Prime ∧
      FinitePlace.below (K := K) w ∉ FinitePlace.ramifiedSet K L}
  have hU : HasPrimeDensity U 1 :=
    hasPrimeDensity_degreeOne_awayRamification (K := K) L
  have hn : (Module.finrank K L : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := K) (M := L)).ne'
  unfold HasPrimeDensity at hU ⊢
  have hscaled := hU.const_mul_left (Module.finrank K L : ℝ)⁻¹
  apply hscaled.congr'
  · have hs : ∀ᶠ s in nhdsWithin (1 : ℝ) (Set.Ioi 1), 1 < s := by
      simpa only [Set.mem_Ioi] using
        (eventually_mem_nhdsWithin (a := (1 : ℝ)) (s := Set.Ioi 1))
    filter_upwards [hs] with s hs
    rw [primeIdealZetaSum_splitsCompletely (K := K) L hs]
    rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hn, one_mul, one_mul]
  · exact Filter.EventuallyEq.rfl

/-- In a finite Galois extension $L/K$, the primes of $K$ of absolute degree one that split
completely in $L$ have Dirichlet density $1/[L:K]$. Milne, *Class Field Theory*,
Chapter VI, Theorem 3.4, restricted to primes of absolute degree one. -/
theorem hasPrimeDensity_splitsCompletely [IsGalois K L] :
    HasPrimeDensity {v : HeightOneSpectrum (𝓞 K) |
        (Ideal.absNorm v.asIdeal).Prime ∧ FinitePlace.SplitsCompletely L v}
      (Module.finrank K L : ℝ)⁻¹ := by
  classical
  let R := FinitePlace.ramifiedSet K L
  let S : Set (HeightOneSpectrum (𝓞 K)) :=
    {v | (Ideal.absNorm v.asIdeal).Prime ∧ FinitePlace.SplitsCompletely L v ∧ v ∉ R}
  have hS : HasPrimeDensity S (Module.finrank K L : ℝ)⁻¹ :=
    hasPrimeDensity_split_awayRamification (K := K) L
  apply hS.congr_finite
  · exact Set.finite_empty.subset (fun _ hv => hv.2 ⟨hv.1.1, hv.1.2.1⟩)
  · exact R.finite_toSet.subset (fun _ hv => by
      by_contra hr
      exact hv.2 ⟨hv.1.1, hv.1.2, hr⟩)

end SIC
