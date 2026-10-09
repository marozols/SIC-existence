/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Frobenius.Tower

/-!
# Complete splitting by counting primes

A prime of `K` splits completely in `L` when `L` has `[L : K]` primes above it; in a Galois
extension this means ramification index and residue degree one, and at an unramified prime it
means trivial Frobenius.

This module follows Milne, *Class Field Theory*, version 4.03 (2020), Chapter VI, §3, and
[83, Neukirch (1999), Chapter I, Propositions 8.2 and 9.6]. It supplies the notion of splitting
counted by `SICs.ClassField.Density.Splitting` and detected by Frobenius elements in
`SICs.ClassField.Frobenius.DegreeOne`. The idelic files of this folder describe complete
splitting by local degrees instead; no comparison of the two notions is needed.

## The argument

In a Galois extension of degree $n$ the primes above $\mathfrak p$ are conjugate, so they share
one ramification index $e$ and one residue degree $f$, and their number $g$ satisfies $efg=n$
(Mathlib's `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`). Hence $g=n$ exactly
when $e=f=1$. At an unramified prime the order of Frobenius is $f$
(`IsFrobeniusAt.orderOf_eq_inertiaDeg`), so Frobenius is trivial exactly when $f=1$.
In a tower, Frobenius restricts to Frobenius in a normal intermediate field, where the same
criterion detects splitting. Residue degree one also makes the norms of a prime and a prime
above it equal.
-/

namespace SIC

open NumberField IsDedekindDomain

namespace FinitePlace

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]

/-! ### Complete splitting

The prime-count definition, its characterization by ramification and residue degree, and the
resulting equality of absolute norms. -/

/-- A nonzero prime $\mathfrak p$ of $K$ **splits completely** in $L$ when there are $[L:K]$
primes of $L$ above it. Milne, *Class Field Theory*, Chapter VI, §3. -/
def SplitsCompletely (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  (v.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L

variable {L}

/-- In a Galois extension, $\mathfrak p$ splits completely exactly when a prime above it has
ramification index and residue degree one. [83, Neukirch (1999), Chapter I, Proposition 9.6]
with Chapter I, Proposition 8.2. -/
theorem splitsCompletely_iff [IsGalois K L] (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] :
    SplitsCompletely L v ↔
      w.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ w.asIdeal.inertiaDeg (𝓞 K) = 1 := by
  have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    v.asIdeal (𝓞 L) (L ≃ₐ[K] L)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal (L ≃ₐ[K] L),
    Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal w.asIdeal (L ≃ₐ[K] L),
    IsGalois.card_aut_eq_finrank K L] at hfund
  have hn : 0 < Module.finrank K L := Module.finrank_pos
  constructor
  · intro hs
    unfold SplitsCompletely at hs
    rw [← hs] at hfund hn
    have hprod : w.asIdeal.ramificationIdx (𝓞 K) *
        w.asIdeal.inertiaDeg (𝓞 K) = 1 := by
      apply Nat.eq_of_mul_eq_mul_left hn
      simpa only [mul_one] using hfund
    constructor
    · exact Nat.eq_one_of_mul_eq_one_left (by simpa [mul_comm] using hprod)
    · exact Nat.eq_one_of_mul_eq_one_left hprod
  · rintro ⟨he, hf⟩
    unfold SplitsCompletely
    simpa only [he, hf, one_mul, mul_one] using hfund

/-- A prime above a completely split prime has the same absolute norm. -/
theorem SplitsCompletely.absNorm_eq [IsGalois K L] {v : HeightOneSpectrum (𝓞 K)}
    (hv : SplitsCompletely L v) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal := by
  have hf := ((splitsCompletely_iff v w).mp hv).2
  simpa only [hf, pow_one] using (Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal).symm

end FinitePlace

/-! ### Trivial Frobenius

At an unramified prime the order of Frobenius is the residue degree. -/

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]

/-- At a prime unramified in a Galois extension, Frobenius is trivial exactly when the prime
splits completely. Milne, *Class Field Theory*, Chapter V, §1, and Chapter VI, proof of
Corollary 3.8. -/
theorem IsFrobeniusAt.eq_one_iff_splitsCompletely [IsGalois K L] {g : L ≃ₐ[K] L}
    {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)}
    (hg : IsFrobeniusAt K L g v.asIdeal w.asIdeal)
    (hw : w.asIdeal.ramificationIdx (𝓞 K) = 1) :
    g = 1 ↔ FinitePlace.SplitsCompletely L v := by
  let : w.asIdeal.LiesOver v.asIdeal := hg.liesOver
  calc
    g = 1 ↔ orderOf g = 1 := orderOf_eq_one_iff.symm
    _ ↔ w.asIdeal.inertiaDeg (𝓞 K) = 1 := by rw [hg.orderOf_eq_inertiaDeg hw]
    _ ↔ FinitePlace.SplitsCompletely L v := by rw [FinitePlace.splitsCompletely_iff v w, hw]; simp

/-- Restriction of an unramified Frobenius element to a normal intermediate field is trivial
exactly when the base prime splits completely there. Milne, *Class Field Theory*, Chapter V,
§1 and Proposition 1.11. -/
theorem IsFrobeniusAt.restrictNormal_eq_one_iff_splitsCompletely [IsGalois K L]
    (E : IntermediateField K L) [IsGalois K E] {g : L ≃ₐ[K] L}
    {v : HeightOneSpectrum (𝓞 K)} {Q : HeightOneSpectrum (𝓞 L)}
    (hg : IsFrobeniusAt K L g v.asIdeal Q.asIdeal)
    (hQ : Q.asIdeal.ramificationIdx (𝓞 K) = 1) :
    g.restrictNormal E = 1 ↔ FinitePlace.SplitsCompletely E v := by
  let w := FinitePlace.below (K := E) Q
  have hFrob : IsFrobeniusAt K E (g.restrictNormal E) v.asIdeal w.asIdeal := by
    simpa only [w, FinitePlace.below, HeightOneSpectrum.under_asIdeal, Ideal.under]
      using hg.restrictNormal E
  have hwram : w.asIdeal.ramificationIdx (𝓞 K) = 1 :=
    ramificationIdx_below_eq_one w.asIdeal Q.asIdeal hQ
  exact hFrob.eq_one_iff_splitsCompletely hwram

/-- Complete splitting descends from a finite Galois extension to a normal intermediate field.
Milne, *Class Field Theory*, Chapter VI, Exercise A-10. -/
theorem FinitePlace.splitsCompletely_subextension [IsGalois K L]
    (E : IntermediateField K L) [IsGalois K E]
    (v : HeightOneSpectrum (𝓞 K)) (hv : FinitePlace.SplitsCompletely L v) :
    FinitePlace.SplitsCompletely E v := by
  obtain ⟨q⟩ := (inferInstance : Nonempty (FinitePlace.PrimeAbove (L := L) v))
  let Q := FinitePlace.PrimeAbove.place v q
  have hQram : Q.asIdeal.ramificationIdx (𝓞 K) = 1 :=
    ((FinitePlace.splitsCompletely_iff v Q).mp hv).1
  obtain ⟨g, hg⟩ :=
    exists_isFrobeniusAt (K := K) (H := L) v.asIdeal Q.asIdeal v.ne_bot
  have hg1 : g = 1 := (hg.eq_one_iff_splitsCompletely hQram).mpr hv
  apply (hg.restrictNormal_eq_one_iff_splitsCompletely E hQram).mp
  rw [hg1]
  exact (AlgEquiv.restrictNormal_eq_one_iff E 1).mpr (fun _ _ => rfl)

end SIC
