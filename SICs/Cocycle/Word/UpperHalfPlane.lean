/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Cocycle.Word.Basic
import SICs.Cocycle.BoundaryComparison

/-!
# The upper-half-plane cocycle along a canonical word

The cocycle relation peeled along the Hirzebruch–Jung word on `ℍ`, and the chained real boundary
limit.

`SICs.Cocycle.Word.Basic` defines the real cocycle by multiplying `σ_S` factors along the
Hirzebruch--Jung word of
[AFK25, Theorem C.4, `thm:tsaltexpn`]; here the same chaining is *proved* for the product quotient
`sfJacobiCocycleUHP` on `ℍ`, with the product quotient interpreted in meromorphic normal form
in the Jacobi variable. It represents the upper-half-plane `σ_M` of [AFK25, Definition 1.16,
`df:shinfadjacocycle`]. The continuation of `σ_M` to
`D_M` is not formalized, so every statement here carries `0 < τ.im`.

## The one-step decomposition

Writing `hjStep M = (r, M')`, so that `M = T^{r} S M'`, the cocycle relation of
`SICs.Cocycle.UpperHalfPlane` gives

$$\sigma_M(z,\tau) = \sigma_S\!\left(\frac{z}{j_{M'}(\tau)},\, M'\cdot\tau\right)
  \sigma_{M'}(z,\tau)$$

in two moves: `sfJacobiCocycle_T_zpow_mul` drops the translation `T^{r}` from the left,
and `sfJacobiCocycle_mul_of_num_ne_zero` splits the remaining `S M'`. This is exactly the
recursion
`wordSigmaS` runs on, so [AFK25, equation (8.5), `eq:sfjldecom`] holds on `ℍ` term by term.

The two nonvanishing hypotheses are the numerators of the two cocycles being related, `σ_M` and
`σ_{M'}`. They exclude cancellation of a zero with a pole in the pointwise product. The zeros
of `qPochhammer` are `m - nτ`, with `m ∈ ℤ` and `n ∈ ℕ`, a subset of the period lattice
(`qPochhammer_eq_zero_iff`); the cocycle fills removable common zeros. A determinant-one
matrix keeps every intermediate modulus in `ℍ`
(`fltDenominator_ne_zero_of_im_ne_zero`, `flt_im_pos`).

## The boundary limit along the word

`SICs.Cocycle.BoundaryComparison`'s `tendsto_sfJacobiCocycle_S` passes *one* `S`-generator
to the real boundary. Chaining it along the decomposition above gives the boundary limit of the
whole cocycle: for a real pair `(z, τ)` and complex parameters approaching it from inside `ℍ`,

```text
sigma_M(z_n, tau_n) → wordSigmaS z tau M h0.
```

This is the analytic passage `τ → α` in the proof of [72, Kopp (2024), Theorem 4.46, `thm:cllr`],
carried out for the whole word rather than one generator. The hypotheses fall into two groups,
one per obstruction, each quantified over the matrices the recursion actually visits
(`WordSigmaSVisits`); the second has a real and a complex half:

* **Positive periods.** `tendsto_sfJacobiCocycle_S_sigmaSHonest` holds at a real pair
  with `0 < τ`, so each factor needs its own period `N·τ` positive — which is also what makes
  `wordSigmaS`'s `sigmaSHonest` factor there an honest `σ_S` value rather than a placeholder. No
  condition on the transported argument `z / j_N(τ)` is needed beyond the next bullet: the
  generator limit carries an arbitrary real argument into the chamber by its own ceiling shift.
* **The period lattice.** The comparison of the product quotient with the integral representation
  holds off `ℤ + ℤτ_n`, so each factor's approaching arguments must avoid it; and the finite
  factor that moves its *real* argument into the chamber has a zero on `ℤ(N·τ) + ℤ`, so the limit
  argument must avoid that lattice as well. The complex half also does the peeling's work: each
  peel needs the numerator of the cocycle it splits to be nonzero, so that the middle products
  cancel, and `ϖ` vanishes exactly on the period lattice
  (`qPochhammer_ne_zero_of_not_isPeriodLatticePoint`). That is why the complex half is quantified
  over `M` together with its visited matrices: at the terminal translation `T^{k}` the same
  condition is nonvanishing of `ϖ(z_n, τ_n)`, since `ϖ` is invariant under an integer shift of its
  modulus.

The terminal matrix is a translation `T^{k}` only when its top-left entry is positive; the
recursion's own invariant supplies this after one peel (`hjStep_snd_entries`), so the hypothesis
`hterm` below is needed only at the seed, and is vacuous whenever the seed's lower-left entry is
nonzero.

## References

- [AFK25, Theorem C.4, `thm:tsaltexpn`] and [AFK25, equation (8.5), `eq:sfjldecom`]: the word
  decomposition being mirrored.
- [AFK25, equation (1.22), `eq:sfjcocyclerelInt`]: the cocycle relation, proved on `ℍ` in
  `SICs.Cocycle.UpperHalfPlane`.
- [72, Kopp (2024), Theorem 4.46, `thm:cllr`]: the conductor-lowering theorem whose proof takes
  the limit chained here.
-/

noncomputable section

open Complex Real ModularGroup
open scoped MatrixGroups

namespace SIC

/-! ### One Hirzebruch--Jung peel on `ℍ`

`M = T^{r} S M'` splits the cocycle into an `S`-generator at the transported argument and the
cocycle of the reduced matrix, matching `wordSigmaS_of_lowerLeft_ne_zero` factor for factor. -/

/-- The peel at a matrix already presented as `T^{r} S N`: `sfJacobiCocycle_hjStep`'s
argument, with the reduced matrix supplied by the caller so that substituting the factorization
cannot disturb `hjStep`'s own occurrences of `M`. -/
private lemma sfJacobiCocycle_of_eq_T_zpow_mul_S_mul {M N : SL(2, ℤ)} {r : ℤ}
    (hMeq : M = T ^ r * (S * N)) (z τ : ℂ) (hτ : 0 < τ.im)
    (hnum : qPochhammer (z / fltDenominator (M : Mat(2, ℤ)) τ)
      (flt (M : Mat(2, ℤ)) τ) ≠ 0)
    (hmid : qPochhammer (z / fltDenominator (N : Mat(2, ℤ)) τ)
      (flt (N : Mat(2, ℤ)) τ) ≠ 0) :
    sfJacobiCocycleUHP (M : Mat(2, ℤ)) z τ =
      sfJacobiCocycleUHP (ModularGroup.S : Mat(2, ℤ))
          (z / fltDenominator (N : Mat(2, ℤ)) τ)
          (flt (N : Mat(2, ℤ)) τ) *
        sfJacobiCocycleUHP (N : Mat(2, ℤ)) z τ := by
  subst hMeq
  have hSN : fltDenominator ((S * N : SL(2, ℤ)) : Mat(2, ℤ)) τ ≠ 0 :=
    fltDenominator_ne_zero_of_im_ne_zero (S * N : SL(2, ℤ)) hτ.ne'
  -- The translation shifts the modulus of `σ_M`'s numerator by an integer, which `ϖ` ignores.
  rw [Matrix.SpecialLinearGroup.coe_mul (T ^ r), fltDenominator_mul _ _ τ hSN,
    fltDenominator_T_zpow, one_mul, flt_mul _ _ τ hSN, flt_T_zpow,
    qPochhammer_tau_add_intCast] at hnum
  calc sfJacobiCocycleUHP ((T ^ r * (S * N) : SL(2, ℤ)) : Mat(2, ℤ)) z τ
      = sfJacobiCocycleUHP ((S * N : SL(2, ℤ)) : Mat(2, ℤ)) z τ :=
        sfJacobiCocycle_T_zpow_mul r (S * N) z τ hτ
    _ = _ := by
      simpa using sfJacobiCocycle_mul_of_num_ne_zero ModularGroup.S N z τ hτ hnum hmid

/-- **One Hirzebruch--Jung peel of the cocycle on `ℍ`**, the upper-half-plane form of the
recursion `SICs.Cocycle.Word.Basic`'s `wordSigmaS` runs on and of [AFK25, equation (8.5),
`eq:sfjldecom`]: with `hjStep M = (r, M')`,

$$\sigma_M(z,\tau) = \sigma_S\!\left(\frac{z}{j_{M'}(\tau)},\, M'\cdot\tau\right)
  \sigma_{M'}(z,\tau).$$

`hnum` and `hmid` are the numerators of `σ_M` and of `σ_{M'}`. Their nonvanishing
excludes cancellation of a zero with a pole, so the pointwise identity also holds at a pole
of the original product quotient. Integer shifts of the modulus do not affect `ϖ`. [AFK25,
Theorem C.4, `thm:tsaltexpn`] states the decomposition for the continued cocycle
on `D_M`; `0 < τ.im` places it on `ℍ`, where `σ_M` is the product quotient. -/
theorem sfJacobiCocycle_hjStep (M : SL(2, ℤ)) (z τ : ℂ) (hτ : 0 < τ.im)
    (hnum : qPochhammer (z / fltDenominator (M : Mat(2, ℤ)) τ)
      (flt (M : Mat(2, ℤ)) τ) ≠ 0)
    (hmid : qPochhammer (z / fltDenominator ((hjStep M).2 : Mat(2, ℤ)) τ)
      (flt ((hjStep M).2 : Mat(2, ℤ)) τ) ≠ 0) :
    sfJacobiCocycleUHP (M : Mat(2, ℤ)) z τ =
      sfJacobiCocycleUHP (ModularGroup.S : Mat(2, ℤ))
          (z / fltDenominator ((hjStep M).2 : Mat(2, ℤ)) τ)
          (flt ((hjStep M).2 : Mat(2, ℤ)) τ) *
        sfJacobiCocycleUHP ((hjStep M).2 : Mat(2, ℤ)) z τ :=
  sfJacobiCocycle_of_eq_T_zpow_mul_S_mul
    (by rw [← mul_assoc]; exact hjStep_reconstruct M) z τ hτ hnum hmid

/-! ### The boundary limit along the word

Chaining `SICs.Cocycle.BoundaryComparison`'s one-generator limit along the peel above carries the
whole upper-half-plane cocycle to the real word-product value. The recursion is `wordSigmaS`'s own,
so the induction is on the lower-left entry, and each factor's hypotheses are read off the
matrices `WordSigmaSVisits` records. The transported argument and modulus of each factor follow
the moduli by `SICs.SL2Z.FractionalLinear`'s `fltDenominator_tendsto` and `flt_tendsto`. -/

/-- **The upper-half-plane cocycle tends to the real word-product value.** For a real pair
`(z, τ)` and complex parameters `(z_n, τ_n) → (z, τ)` approaching it from inside `ℍ`,

```text
sigma_M(z_n, tau_n) → wordSigmaS z tau M h0,
```

the word-level form of [72, Kopp (2024), Theorem 4.46, `thm:cllr`]'s passage `τ → α`. It is
proved by the recursion of `sfJacobiCocycle_hjStep`, whose `S`-factor is sent to
`sigmaSHonest` by `tendsto_sfJacobiCocycle_S_sigmaSHonest` and whose remaining cocycle is
handled by the recursive call.

The hypotheses beyond the two convergences are one per obstruction, each quantified over the
matrices the recursion visits (see the file docstring):

* `hper`, that each visited factor's period `N·τ` is positive, which is what makes its
  `sigmaSHonest` factor an honest `σ_S` value at all;
* `hlatReal`, that each visited factor's *real* argument `z / j_N(τ)` avoids the lattice
  `ℤ(N·τ) + ℤ`, where the finite factor relating it to its chamber representative acquires a
  zero;
* `hlat`, that the approaching arguments `z_n / j_N(τ_n)` at `M` and at each visited matrix
  eventually avoid the period lattice `ℤ + ℤ(N·τ_n)`, where the product quotient and the integral
  representation part company and where the numerator `ϖ(z_n / j_N(τ_n), N·τ_n)` of the cocycle
  being peeled vanishes (`qPochhammer_ne_zero_of_not_isPeriodLatticePoint`);
* `hterm`, which is what makes the terminal matrix a translation. It is vacuous when
  `M 1 0 ≠ 0`, and the recursion re-establishes it after one peel from `hjStep_snd_entries`.

The approaching values are the product quotient `sfJacobiCocycleUHP`; `him` and `hlat` keep them
in `ℍ` and off the period lattice, where it is the source's `σ_M`. -/
theorem tendsto_sfJacobiCocycle_word {ι : Type*} {l : Filter ι}
    (zSeq tauSeq : ι → ℂ) (z τ : ℝ) (M : SL(2, ℤ)) (h0 : 0 ≤ M 1 0)
    (hterm : M 1 0 = 0 → 0 < M 0 0)
    (hzT : Filter.Tendsto zSeq l (nhds (z : ℂ)))
    (htauT : Filter.Tendsto tauSeq l (nhds (τ : ℂ)))
    (him : ∀ᶠ n in l, 0 < (tauSeq n).im)
    (hper : ∀ N : SL(2, ℤ), WordSigmaSVisits M N →
      0 < flt (N : Mat(2, ℤ)) τ)
    (hlatReal : ∀ N : SL(2, ℤ), WordSigmaSVisits M N →
      SigmaSLatticeFree (flt (N : Mat(2, ℤ)) τ)
        (z / fltDenominator (N : Mat(2, ℤ)) τ))
    (hlat : ∀ N : SL(2, ℤ), N = M ∨ WordSigmaSVisits M N →
      ∀ᶠ n in l, ¬ IsPeriodLatticePoint (flt (N : Mat(2, ℤ)) (tauSeq n))
        (zSeq n / fltDenominator (N : Mat(2, ℤ)) (tauSeq n))) :
    Filter.Tendsto (fun n => sfJacobiCocycleUHP (M : Mat(2, ℤ))
        (zSeq n) (tauSeq n)) l (nhds (wordSigmaS z τ M h0)) := by
  by_cases hz : M 1 0 = 0
  · -- Terminal matrix: a translation, at which the cocycle is eventually `1`.
    obtain ⟨k, hMT⟩ : ∃ k : ℤ, M = T ^ k :=
      ⟨M 0 1, eq_T_zpow_of_lowerLeft_eq_zero M hz (hterm hz)⟩
    rw [wordSigmaS_of_lowerLeft_eq_zero z τ M h0 hz]
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [him, hlat M (Or.inl rfl)] with n hn1 hn2
    have hn : qPochhammer (zSeq n / fltDenominator (M : Mat(2, ℤ)) (tauSeq n))
        (flt (M : Mat(2, ℤ)) (tauSeq n)) ≠ 0 :=
      qPochhammer_ne_zero_of_not_isPeriodLatticePoint (flt_im_pos M hn1) hn2
    rw [hMT] at hn ⊢
    rw [fltDenominator_T_zpow, flt_T_zpow, div_one, qPochhammer_tau_add_intCast] at hn
    exact (sfJacobiCocycle_T_zpow k (zSeq n) (tauSeq n) hn).symm
  · have hpos : 0 < M 1 0 := h0.lt_of_ne (Ne.symm hz)
    have h0' : 0 ≤ (hjStep M).2 1 0 := by
      rw [hjStep_snd_lowerLeft]; exact Int.emod_nonneg _ hpos.ne'
    have hlt : (hjStep M).2 1 0 < M 1 0 := by
      rw [hjStep_snd_lowerLeft]; exact Int.emod_lt_of_pos _ hpos
    have hvis : WordSigmaSVisits M (hjStep M).2 := WordSigmaSVisits.base hz
    have hperN : 0 < flt ((hjStep M).2 : Mat(2, ℤ)) τ := hper _ hvis
    -- The reduced matrix's Jacobi denominator at `τ` is nonzero, or its period would be `0`.
    have hden0 : fltDenominator ((hjStep M).2 : Mat(2, ℤ)) τ ≠ 0 := by
      intro h
      rw [show flt ((hjStep M).2 : Mat(2, ℤ)) τ = 0 by
        unfold flt; unfold fltDenominator at h; rw [h, div_zero]] at hperN
      exact lt_irrefl 0 hperN
    have hdenC : fltDenominator ((hjStep M).2 : Mat(2, ℤ)) (τ : ℂ) ≠ 0 := by
      rw [← ofReal_fltDenominator]
      exact_mod_cast hden0
    have hargT : Filter.Tendsto
        (fun n => zSeq n / fltDenominator ((hjStep M).2 : Mat(2, ℤ)) (tauSeq n)) l
        (nhds ((z / fltDenominator ((hjStep M).2 : Mat(2, ℤ)) τ : ℝ) : ℂ)) := by
      rw [Complex.ofReal_div, ofReal_fltDenominator]
      exact hzT.div (fltDenominator_tendsto _ htauT) hdenC
    have hmodT : Filter.Tendsto
        (fun n => flt ((hjStep M).2 : Mat(2, ℤ)) (tauSeq n)) l
        (nhds ((flt ((hjStep M).2 : Mat(2, ℤ)) τ : ℝ) : ℂ)) := by
      simpa only [ofReal_flt] using
        flt_tendsto ((hjStep M).2 : Mat(2, ℤ)) htauT hdenC
    have hS := tendsto_sfJacobiCocycle_S_sigmaSHonest
      (fun n => zSeq n / fltDenominator ((hjStep M).2 : Mat(2, ℤ)) (tauSeq n))
      (fun n => flt ((hjStep M).2 : Mat(2, ℤ)) (tauSeq n))
      (z / fltDenominator ((hjStep M).2 : Mat(2, ℤ)) τ)
      (flt ((hjStep M).2 : Mat(2, ℤ)) τ) hperN (hlatReal _ hvis) hargT hmodT
      (by filter_upwards [him] with n hn; exact flt_im_pos (hjStep M).2 hn)
      (hlat _ (Or.inr hvis))
    have hIH := tendsto_sfJacobiCocycle_word zSeq tauSeq z τ (hjStep M).2 h0'
      (fun _ => by rw [(hjStep_snd_entries M).1]; exact hpos) hzT htauT him
      (fun P hP => hper P (hvis.trans hP)) (fun P hP => hlatReal P (hvis.trans hP))
      (fun P hP => hlat P (by
        rcases hP with rfl | hP
        · exact Or.inr hvis
        · exact Or.inr (hvis.trans hP)))
    rw [wordSigmaS_of_lowerLeft_ne_zero z τ M h0 hz h0']
    refine Filter.Tendsto.congr' ?_ (hS.mul hIH)
    filter_upwards [him, hlat M (Or.inl rfl), hlat _ (Or.inr hvis)] with n hn1 hn2 hn3
    exact (sfJacobiCocycle_hjStep M (zSeq n) (tauSeq n) hn1
      (qPochhammer_ne_zero_of_not_isPeriodLatticePoint (flt_im_pos M hn1) hn2)
      (qPochhammer_ne_zero_of_not_isPeriodLatticePoint
        (flt_im_pos (hjStep M).2 hn1) hn3)).symm
termination_by (M 1 0).toNat
decreasing_by omega

end SIC

end
