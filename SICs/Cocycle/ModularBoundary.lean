/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Cocycle.Modular.Shifts
import SICs.Cocycle.Word.UpperHalfPlane

/-!
# The real boundary of the period-product quotient

The period-product quotient on `ℍ` tends to the real modular cocycle `ש^r_M`, and the Jacobi-cocycle
quotient to the word value `σ_M`.

This file proves the passage `τ → α` used in the proof of [72, Kopp (2024), Theorem 4.46,
`thm:cllr`], at the level of the Shintani--Faddeev modular cocycle: along parameters approaching
a real point from inside `ℍ`, the period-product quotient tends to the real canonical-word value,

```text
varpi_r(M · tau_k) / varpi_r(tau_k) → ש^r_M(tau).
```

The proof combines two identities:

* `SICs.Cocycle.UpperHalfPlane`'s `sfPeriodProduct_flt_div_sfPeriodProduct`, the source's
  coboundary identity [AFK25, equation (1.27), `eq:coboundary`], which rewrites the quotient as
  the Jacobi cocycle over the finite `q`-Pochhammer factor of [AFK25, equation (1.26),
  `eq:shindf`];
* `SICs.Cocycle.Word.UpperHalfPlane`'s `tendsto_sfJacobiCocycle_word`, which carries that
  Jacobi cocycle to `wordSigmaS` along the canonical word.

The finite factor is followed to the boundary by `continuousAt_qPochhammerFin`, and the two limits
are divided. What comes out is exactly `SICs.Cocycle.Modular.Values`'s `sfModularCocycleReal`,
since that
definition is the same quotient with `wordSigmaS` in the numerator.

## Boundary limits and domain conditions

[72, Kopp (2024)] takes this limit by meromorphic continuation of the cocycle to `D_M`, which this
formalization does not represent. Here the approaching parameters stay in the upper half plane: each
`S`-generator of the word is compared with the integral representation [AFK25, equation (8.7),
`eq:dsintrep`], which is jointly continuous on its chamber and reaches an arbitrary real argument
through the shift rule [AFK25, equation (8.9)], and the generator limits are chained along the
Hirzebruch--Jung recursion. Each visited matrix requires positive intermediate periods and
arguments off the period lattice. The word decomposition also requires the orientation
`0 ≤ M 1 0` (see `SICs.Cocycle.UpperHalfPlane`'s file docstring).

The periods stay positive along the whole word when the seed's Jacobi denominator is positive.
Both off-lattice conditions, at the real limit point and along the complex approach, follow from
`r ∉ ℤ²`, the hypothesis of [AFK25, equation (1.27), `eq:coboundary`], together with irrationality
of the limit point. The
second section below records the limit in that form, where the only remaining condition is
`0 < j_M(τ)` at `M` itself.

Both halves of the proof are statements about the product quotient `sfJacobiCocycleUHP` on `ℍ`,
where it is the source's `σ_M`; the result below mentions only the period product on `ℍ` and the
real cocycle. The `ℍ`-only character of the left-hand side is carried by `him`, which is where
`sfPeriodProduct` converges.

## References

- [AFK25, Definition 1.18, `def:shin`, equations (1.26), `eq:shindf`, and (1.27),
  `eq:coboundary`].
- [72, Kopp (2024), Theorem 4.46, `thm:cllr`]: the conductor-lowering theorem whose proof takes
  this limit.
-/

noncomputable section

open Complex Real
open scoped MatrixGroups

namespace SIC

/-! ### The boundary limit of the coboundary quotient

The Jacobi cocycle and the finite `q`-Pochhammer factor are followed to the boundary separately
and divided; the coboundary identity turns the result into a statement about the period-product
quotient itself. -/

/-- The finite `q`-Pochhammer factor of [AFK25, equation (1.26), `eq:shindf`] followed to the real
boundary. Its argument and its modulus track the moduli by `fracSymplecticFormRat_tendsto`,
`fltDenominator_tendsto` and `flt_tendsto`, and `continuousAt_qPochhammerFin` then needs only that
the factor is nonzero at the limit. Split off from
`tendsto_sfPeriodProduct_div_sfModularCocycleReal`, whose other half is the word limit. -/
private lemma tendsto_qPochhammerFin_nQPInt {ι : Type*} {l : Filter ι} (tauSeq : ι → ℂ) (τ : ℝ)
    (r : Fin 2 → ℚ) (M : Mat(2, ℤ))
    (hdenM : fltDenominator M τ ≠ 0)
    (htauT : Filter.Tendsto tauSeq l (nhds (τ : ℂ)))
    (hfin : qPochhammerFin (nQPInt r M)
      (((fracSymplecticFormRat r τ : ℝ) : ℂ) / ((fltDenominator M τ : ℝ) : ℂ))
      (((flt M τ : ℝ) : ℂ)) ≠ 0) :
    Filter.Tendsto (fun k => qPochhammerFin (nQPInt r M)
        (fracSymplecticFormRat r (tauSeq k) / fltDenominator M (tauSeq k))
        (flt M (tauSeq k))) l
      (nhds (qPochhammerFin (nQPInt r M)
        (((fracSymplecticFormRat r τ : ℝ) : ℂ) / ((fltDenominator M τ : ℝ) : ℂ))
        (((flt M τ : ℝ) : ℂ)))) := by
  have hdenC : fltDenominator M (τ : ℂ) ≠ 0 := by
    rw [← ofReal_fltDenominator]
    exact_mod_cast hdenM
  have hargT : Filter.Tendsto
      (fun k => fracSymplecticFormRat r (tauSeq k) / fltDenominator M (tauSeq k)) l
      (nhds (((fracSymplecticFormRat r τ : ℝ) : ℂ) / ((fltDenominator M τ : ℝ) : ℂ))) := by
    rw [ofReal_fltDenominator]
    exact (fracSymplecticFormRat_tendsto r htauT).div (fltDenominator_tendsto _ htauT) hdenC
  have hmodT : Filter.Tendsto (fun k => flt M (tauSeq k)) l (nhds ((flt M τ : ℝ) : ℂ)) := by
    rw [ofReal_flt]
    exact flt_tendsto _ htauT hdenC
  simpa only [Function.comp_def] using
    (continuousAt_qPochhammerFin (nQPInt r M) hfin).tendsto.comp (hargT.prodMk_nhds hmodT)

/-- The off-lattice approach excludes integral characteristics when the filter is nontrivial;
used by `tendsto_sfPeriodProduct_div_sfModularCocycleReal`. -/
private lemma not_isIntegralIndex_of_latticeFree_approach {ι : Type*} {l : Filter ι}
    [l.NeBot] (tauSeq : ι → ℂ) {r : Fin 2 → ℚ} (M : SL(2, ℤ))
    (him : ∀ᶠ k in l, 0 < (tauSeq k).im)
    (hlat : ∀ᶠ k in l, ¬ IsPeriodLatticePoint (flt (M : Mat(2, ℤ)) (tauSeq k))
      (fracSymplecticFormRat r (tauSeq k) /
        fltDenominator (M : Mat(2, ℤ)) (tauSeq k))) :
    ¬ IsIntegralIndex r := by
  intro hr
  obtain ⟨k, himk, hlatk⟩ := (him.and hlat).exists
  have hs := isIntegralIndex_ratVecAction (M : Mat(2, ℤ)) hr
  obtain ⟨a, ha⟩ := hs 1
  obtain ⟨b, hb⟩ := hs 0
  apply hlatk
  refine ⟨-b, a, ?_⟩
  have harg := fracSymplecticFormRat_ratVecAction (M : Mat(2, ℤ)) r (tauSeq k)
    (fltDenominator_ne_zero_of_im_ne_zero M himk.ne')
  rw [M.2, Int.cast_one, one_mul] at harg
  rw [← harg, fracSymplecticFormRat, ha, hb]
  push_cast
  ring

/-- **The period-product quotient tends to the real modular cocycle.** For `M ∈ Γ_r` and complex
moduli `τ_k → τ` approaching a real point from inside `ℍ`,

$$\frac{\varpi_r(M\cdot\tau_k)}{\varpi_r(\tau_k)} \longrightarrow ש^{r}_M(\tau),$$

the passage `τ → α` in the proof of [72, Kopp (2024), Theorem 4.46, `thm:cllr`], with
`ש^r_M(τ)` the real canonical-word value `sfModularCocycleReal` of
[AFK25, Definition 1.18, `def:shin`, equation (1.26), `eq:shindf`].

Beyond the convergence `htauT` and the approach `him` from inside `ℍ`, the hypotheses are the
requirements of the formal word construction, quantified over the matrices the recursion visits
(see the file docstring and `tendsto_sfJacobiCocycle_word`): `hper`, that each visited
factor's period is positive; `hlatReal`, that each visited factor's real argument avoids the
lattice of its own period; `hlat`, that the approaching arguments at `M` and at each visited
matrix avoid the period lattice, which also keeps the cocycle numerators nonzero; `hterm`, that a
terminal matrix is a translation;
and `hdenM`, that `M`'s own Jacobi denominator does not vanish at `τ`, which is what lets the
finite factor of [AFK25, equation (1.26), `eq:shindf`] be followed to the boundary at all.
`hfin` is nonvanishing of that finite factor at the limit; it makes the source's own expression
defined there, and eventual nonvanishing along the approach follows from it by continuity. -/
theorem tendsto_sfPeriodProduct_div_sfModularCocycleReal {ι : Type*} {l : Filter ι}
    (tauSeq : ι → ℂ) (τ : ℝ) {r : Fin 2 → ℚ} {M : SL(2, ℤ)}
    (hM : M ∈ gammaSubgroup r) (h0 : 0 ≤ M 1 0)
    (hterm : M 1 0 = 0 → 0 < M 0 0)
    (hdenM : fltDenominator (M : Mat(2, ℤ)) τ ≠ 0)
    (htauT : Filter.Tendsto tauSeq l (nhds (τ : ℂ)))
    (him : ∀ᶠ k in l, 0 < (tauSeq k).im)
    (hfin : qPochhammerFin (nQPInt r (M : Mat(2, ℤ)))
      (((fracSymplecticFormRat r τ : ℝ) : ℂ) /
        ((fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ))
      (((flt (M : Mat(2, ℤ)) τ : ℝ) : ℂ)) ≠ 0)
    (hper : ∀ N : SL(2, ℤ), WordSigmaSVisits M N →
      0 < flt (N : Mat(2, ℤ)) τ)
    (hlatReal : ∀ N : SL(2, ℤ), WordSigmaSVisits M N →
      SigmaSLatticeFree (flt (N : Mat(2, ℤ)) τ)
        (fracSymplecticFormRat r τ / fltDenominator (N : Mat(2, ℤ)) τ))
    (hlat : ∀ N : SL(2, ℤ), N = M ∨ WordSigmaSVisits M N →
      ∀ᶠ k in l, ¬ IsPeriodLatticePoint (flt (N : Mat(2, ℤ)) (tauSeq k))
        (fracSymplecticFormRat r (tauSeq k) /
          fltDenominator (N : Mat(2, ℤ)) (tauSeq k))) :
    Filter.Tendsto (fun k => sfPeriodProduct r (flt (M : Mat(2, ℤ)) (tauSeq k)) /
        sfPeriodProduct r (tauSeq k)) l (nhds (sfModularCocycleReal r M hM h0 τ)) := by
  rcases l.eq_or_neBot with hl | hl
  · subst l
    exact Filter.tendsto_bot
  let := hl
  have hr := not_isIntegralIndex_of_latticeFree_approach tauSeq M him (hlat M (Or.inl rfl))
  -- The word limit of the Jacobi cocycle, and the boundary limit of the finite factor.
  have hword := tendsto_sfJacobiCocycle_word
    (fun k => fracSymplecticFormRat r (tauSeq k)) tauSeq (fracSymplecticFormRat r τ) τ
    M h0 hterm (fracSymplecticFormRat_tendsto r htauT) htauT him hper hlatReal hlat
  have hfinT := tendsto_qPochhammerFin_nQPInt tauSeq τ r (M : Mat(2, ℤ))
    hdenM htauT hfin
  rw [sfModularCocycleReal_eq_of_not_isIntegralIndex hr]
  refine Filter.Tendsto.congr' ?_ (hword.div hfinT hfin)
  filter_upwards [him, hfinT.eventually_ne hfin] with k hk1 hk2
  exact (sfPeriodProduct_flt_div_sfPeriodProduct hM hk1 (sfPeriodProduct_ne_zero hr hk1) hk2).symm

/-! ### The boundary limit from irrationality and a nonintegral characteristic

None of the conditions the word construction imposes is a separate analytic requirement.
Positivity of the periods propagates along the walk from the seed (`WordSigmaSVisits.period_pos`),
and every off-lattice condition — real, complex, the numerators, and the non-pole condition at the
limit point — follows from `r ∉ ℤ²`, the blanket hypothesis of [AFK25, equation (1.27),
`eq:coboundary`], together with irrationality of the limit point. The terminal condition of the
word construction is not separate either: a seed with `M 1 0 = 0` has `j_M(τ) = M 1 1`, and
`det M = 1` then forces `M 0 0 = M 1 1 = 1` (`diag_eq_one_of_lowerLeft_eq_zero`). What is left is
the seed datum `0 < j_M(τ)`. -/

/-- **The Jacobi-cocycle quotient tends to the word value, at an irrational point with a
nonintegral characteristic.** For `M ∈ SL₂(ℤ)` with `0 ≤ M 1 0` and `0 < j_M(τ)`, an irrational
real `τ`, `r ∈ ℚ² ∖ ℤ²`, and `τ_k → τ` from inside `ℍ`,

$$\frac{\varpi(\langle\langle r,\tau_k\rangle\rangle / j_M(\tau_k), M\cdot\tau_k)}
  {\varpi(\langle\langle r,\tau_k\rangle\rangle, \tau_k)}
  \longrightarrow \sigma_M(\langle\langle r,\tau\rangle\rangle, \tau),$$

the real value `wordSigmaS`. This is the upper-half-plane quotient of
[AFK25, Definition 1.16, `df:shinfadjacocycle`] followed to the boundary, the numerator half of
`tendsto_sfPeriodProduct_div_of_not_isIntegralIndex`, with no membership
`M ∈ Γ_r` needed: `tendsto_sfJacobiCocycle_word` with its conditions discharged exactly
as there. It is what compares the word values at two conjugate matrices in
`SICs.Cocycle.Conjugation`, where the conjugating matrix is not in `Γ_r`. -/
theorem tendsto_qPochhammer_div_wordSigmaS {ι : Type*}
    {l : Filter ι} (tauSeq : ι → ℂ) {τ : ℝ} {r : Fin 2 → ℚ} {M : SL(2, ℤ)}
    (hr : ¬ IsIntegralIndex r) (hτ : Irrational τ) (h0 : 0 ≤ M 1 0)
    (hdenM : 0 < fltDenominator (M : Mat(2, ℤ)) τ)
    (htauT : Filter.Tendsto tauSeq l (nhds (τ : ℂ)))
    (him : ∀ᶠ k in l, 0 < (tauSeq k).im) :
    Filter.Tendsto (fun k =>
        qPochhammer (fracSymplecticFormRat r (tauSeq k) /
            fltDenominator (M : Mat(2, ℤ)) (tauSeq k))
          (flt (M : Mat(2, ℤ)) (tauSeq k)) /
        qPochhammer (fracSymplecticFormRat r (tauSeq k)) (tauSeq k)) l
      (nhds (wordSigmaS (fracSymplecticFormRat r τ) τ M h0)) := by
  have hword := tendsto_sfJacobiCocycle_word
    (fun k => fracSymplecticFormRat r (tauSeq k)) tauSeq (fracSymplecticFormRat r τ) τ
    M h0 (topLeft_pos_of_lowerLeft_eq_zero hdenM)
    (fracSymplecticFormRat_tendsto r htauT) htauT him
    (fun _ hN => (WordSigmaSVisits.period_pos τ hτ h0 hdenM hN).1)
    (fun _ hN => sigmaSLatticeFree_fracSymplecticFormRat_div hτ hr _
      (WordSigmaSVisits.period_pos τ hτ h0 hdenM hN).2.ne')
    (fun N _ => by
      filter_upwards [him] with k hk
      exact not_isPeriodLatticePoint_fracSymplecticFormRat_div hr _ hk.ne'
        (fltDenominator_ne_zero_of_im_ne_zero N hk.ne'))
  apply hword.congr'
  filter_upwards [him] with k hk
  exact sfJacobiCocycleUHP_eq_quotient (M : Mat(2, ℤ))
    (fracSymplecticFormRat r (tauSeq k)) (tauSeq k) (sfPeriodProduct_ne_zero hr hk)

/-- **The period-product quotient tends to the real modular cocycle, at an irrational point with a
nonintegral characteristic.** For `M ∈ Γ_r` with `0 ≤ M 1 0` and `0 < j_M(τ)`, an irrational real
`τ`, and `r ∈ ℚ² ∖ ℤ²`,

$$\frac{\varpi_r(M\cdot\tau_k)}{\varpi_r(\tau_k)} \longrightarrow ש^{r}_M(\tau)$$

along any approach `τ_k → τ` from inside `ℍ`. This is
`tendsto_sfPeriodProduct_div_sfModularCocycleReal` with all three of its conditions at the visited
matrices discharged:

* the periods stay positive along the whole walk once the seed's Jacobi denominator is positive
  (`SICs.Cocycle.Word.Basic.WordSigmaSVisits.period_pos`);
* each visited real argument avoids the lattice of its own period
  (`sigmaSLatticeFree_fracSymplecticFormRat_div`);
* each approaching argument, at `M` and at each visited matrix, avoids the complex period lattice
  (`SICs.Cocycle.UpperHalfPlane.not_isPeriodLatticePoint_fracSymplecticFormRat_div`).

The non-pole condition at the limit point goes the same way: the finite factor of
[AFK25, equation (1.26), `eq:shindf`] is nonzero at any irrational real point for a nonintegral
`r` (`qPochhammerFin_nQPInt_ne_zero_of_irrational`), since a zero there
would again put `⟨⟨r,τ⟩⟩/j_M(τ)` on the real lattice. The terminal condition
`M 1 0 = 0 → 0 < M 0 0` follows from `hdenM` and `det M = 1`
(`topLeft_pos_of_lowerLeft_eq_zero`). Nothing beyond `hdenM` is
left. -/
theorem tendsto_sfPeriodProduct_div_of_not_isIntegralIndex {ι : Type*}
    {l : Filter ι} (tauSeq : ι → ℂ) {τ : ℝ} {r : Fin 2 → ℚ} {M : SL(2, ℤ)}
    (hM : M ∈ gammaSubgroup r) (hr : ¬ IsIntegralIndex r)
    (hτ : Irrational τ) (h0 : 0 ≤ M 1 0)
    (hdenM : 0 < fltDenominator (M : Mat(2, ℤ)) τ)
    (htauT : Filter.Tendsto tauSeq l (nhds (τ : ℂ)))
    (him : ∀ᶠ k in l, 0 < (tauSeq k).im) :
    Filter.Tendsto (fun k => sfPeriodProduct r (flt (M : Mat(2, ℤ)) (tauSeq k)) /
        sfPeriodProduct r (tauSeq k)) l (nhds (sfModularCocycleReal r M hM h0 τ)) :=
  tendsto_sfPeriodProduct_div_sfModularCocycleReal tauSeq τ hM h0
    (topLeft_pos_of_lowerLeft_eq_zero hdenM) hdenM.ne' htauT him
    (qPochhammerFin_nQPInt_ne_zero_of_irrational hr _ hτ hdenM.ne')
    (fun _ hN => (WordSigmaSVisits.period_pos τ hτ h0 hdenM hN).1)
    (fun _ hN => sigmaSLatticeFree_fracSymplecticFormRat_div hτ hr _
      (WordSigmaSVisits.period_pos τ hτ h0 hdenM hN).2.ne')
    (fun N _ => by
      filter_upwards [him] with k hk
      exact not_isPeriodLatticePoint_fracSymplecticFormRat_div hr _ hk.ne'
        (fltDenominator_ne_zero_of_im_ne_zero N hk.ne'))

end SIC

end
