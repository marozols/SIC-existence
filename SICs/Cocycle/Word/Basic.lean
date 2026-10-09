/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SL2Z.WordPeriods
import SICs.Cocycle.SigmaS.Reduction

/-!
# The word-chained `sigmaS` product

`wordSigmaS`, the word-chained `σ_S` product, and positivity of every period it visits.

The well-founded recursion `wordSigmaS` follows `SICs.SL2Z.Words.hjStep` and multiplies
`σ_S` factors along a Hirzebruch--Jung word:

```text
σ_M(z,τ) = σ_S(z/j_{M'}(τ), M'·τ) · σ_{M'}(z,τ),    M = T^r·S·M',
```

with base case `σ_{T^k} ≡ 1`. Under the positive-Jacobi-denominator hypothesis,
`SICs.SL2Z.Basic.eq_T_zpow_of_lowerLeft_eq_zero` identifies the terminal matrix as a translation.

Each factor is evaluated by `SICs.Cocycle.SigmaS.Reduction.sigmaSHonest`, which reduces its
argument to the chamber of the double-sine integral. `sigmaSHonest_eq_sigmaS_of_mem` proves
that every valid reducing shift gives the same value, for any real argument and positive
modulus.

`WordSigmaSVisits.period_pos` proves that every intermediate period is positive when the seed
matrix has positive Jacobi denominator. It applies
`SICs.SL2Z.WordPeriods.flt_and_fltDenominator_pos_of_hjStep` at each recursive step; no fixed-point
hypothesis is required. For an admissible tuple's stabilizer, the starting positivity is
`AdmissibleTuple.IsAssociatedStabilizerPair.fltDenominator_A_rootPlus_pos` in
`SICs.Admissible.StabilizerDomain`, equivalently `ρ_t ∈ D_{A_t}`. Outside the positive-period
domain, the total definitions still return complex numbers, but the double-sine interpretation
is not asserted.

## Main declarations

- `wordSigmaS`: the well-founded recursive word-chained product, base case `1` at a pure `T`-power
  (`M 1 0 = 0`), one honest `sigmaSHonest`-factor per `hjStep` peeled otherwise.
- `wordSigmaS_of_lowerLeft_eq_zero`/`wordSigmaS_of_lowerLeft_ne_zero`: the two defining equations,
  stated directly (unfolding via the auto-generated equation lemma).
- `wordSigmaS_step`: the recursive equation with the reduced matrix supplied by the caller, for
  unfolding the recursion along a word that is already known.
- `WordSigmaSVisits`/`WordSigmaSVisits.trans`/`WordSigmaSVisits.period_pos`: the matrices
  `wordSigmaS`'s recursion actually visits, that the relation composes, and the theorem that every
  such matrix has positive period and positive Jacobi denominator at `τ`, given only that the seed
  does — connecting
  `SICs.SL2Z.WordPeriods.flt_and_fltDenominator_pos_of_hjStep` to `wordSigmaS`'s
  own recursive structure.

## References

- [AFK25, Theorem C.4, `thm:tsaltexpn`] (the word decomposition this recursion walks) and [AFK25,
  equations (8.5), `eq:sfjldecom`, (8.6), `eq:SFJacobiCocycleTermsDoubleSine`, and (8.9)] (the
  `σ_S` values it chains).
- `SICs.Cocycle.UpperHalfPlane`: the convergent product and its comparison with real values.
- `SICs.SL2Z.Words`: `hjStep`, whose iteration this recursion follows, and the words it peels.
- `SICs.SL2Z.WordPeriods`, "The positive-denominator invariant": the one-step invariant
  `WordSigmaSVisits.period_pos` propagates along this file's recursion.
-/

open scoped MatrixGroups

namespace SIC

/-! ### The recursive word product

Each Hirzebruch--Jung step contributes an honest real `σ_S` value at the transported argument and
period.  Well-founded recursion on the lower-left entry terminates at an upper-triangular matrix,
where the product is one. -/

/-- **The word-chained `sigmaS` product, with the honest per-step shift.** Holds `z τ : ℝ` fixed
throughout the recursion — only the current matrix shrinks — and peels one
`hjStep` at a time from `M`, multiplying in `sigmaSHonest (z / j_{M'}(τ)) (M'·τ)` — the honest
`σ_S` value at the raw argument, via the canonical shift `SICs.Cocycle.SigmaS.Reduction.sfShift` —
until `M`'s lower-left entry reaches `0`, at which point the factor contributed is `1` (the
`σ_{T^k} ≡ 1` base case).

The chained product is [AFK25, equation (8.5), `eq:sfjldecom`],

$$\sigma_L(z,\tau) = \sigma_S\!\left(\frac{z}{j_{L_2}(\tau)}, L_2\cdot\tau\right) \cdots
  \sigma_S\!\left(\frac{z}{j_{L_{n+1}}(\tau)}, L_{n+1}\cdot\tau\right),$$

read as a recursion over the word decomposition [AFK25, Theorem C.4, `thm:tsaltexpn`] instead of
as a finite product over an already-chosen word. -/
noncomputable def wordSigmaS (z τ : ℝ) : (M : SL(2, ℤ)) → 0 ≤ M 1 0 → ℂ
  | M, h0 =>
    if hz : M 1 0 = 0 then
      1
    else
      have hpos : 0 < M 1 0 := h0.lt_of_ne (Ne.symm hz)
      have h0' : 0 ≤ (hjStep M).2 1 0 := by
        rw [hjStep_snd_lowerLeft]; exact Int.emod_nonneg _ hpos.ne'
      have hlt : (hjStep M).2 1 0 < M 1 0 := by
        rw [hjStep_snd_lowerLeft]; exact Int.emod_lt_of_pos _ hpos
      sigmaSHonest (z / fltDenominator ((hjStep M).2 : Mat(2, ℤ)) τ)
          (flt ((hjStep M).2 : Mat(2, ℤ)) τ)
        * wordSigmaS z τ (hjStep M).2 h0'
termination_by M _ => M 1 0 |>.toNat
decreasing_by omega

/-- **Base case**: at a pure `T`-power (`M 1 0 = 0`), `wordSigmaS` is `1` — the `σ_{T^k} ≡ 1`
identity, resolved as the recursion's stopping value rather than a separately-proved theorem (see
the file docstring). -/
theorem wordSigmaS_of_lowerLeft_eq_zero (z τ : ℝ) (M : SL(2, ℤ)) (h0 : 0 ≤ M 1 0)
    (hz : M 1 0 = 0) : wordSigmaS z τ M h0 = 1 := by
  rw [wordSigmaS, dite_eq_left hz]

/-- **Recursive step**: away from the base case, `wordSigmaS` peels one `hjStep`, multiplying in
the honest `σ_S` factor at the reduced matrix's period `M'·τ` and raw argument `z / j_{M'}(τ)`,
and recurses on `M'` with the *same* `z, τ`. -/
theorem wordSigmaS_of_lowerLeft_ne_zero (z τ : ℝ) (M : SL(2, ℤ)) (h0 : 0 ≤ M 1 0)
    (hz : M 1 0 ≠ 0) (h0' : 0 ≤ (hjStep M).2 1 0) :
    wordSigmaS z τ M h0 =
      sigmaSHonest (z / fltDenominator ((hjStep M).2 : Mat(2, ℤ)) τ)
          (flt ((hjStep M).2 : Mat(2, ℤ)) τ)
        * wordSigmaS z τ (hjStep M).2 h0' := by
  rw [wordSigmaS, dite_eq_right hz]

/-- **The recursive step against an independently identified reduced matrix.** Same content as
`wordSigmaS_of_lowerLeft_ne_zero`, but with `(hjStep M).2` replaced by whatever `N` a caller has
proved it equal to. Without this, unfolding the recursion along a *known* word requires rewriting
under `wordSigmaS`'s dependent proof argument; here the rewrite happens once, before the
appeal to the defining equation. -/
theorem wordSigmaS_step (z τ : ℝ) {M N : SL(2, ℤ)} (h0 : 0 ≤ M 1 0) (hz : M 1 0 ≠ 0)
    (hN : (hjStep M).2 = N) (h0N : 0 ≤ N 1 0) :
    wordSigmaS z τ M h0 =
      sigmaSHonest (z / fltDenominator (N : Mat(2, ℤ)) τ)
          (flt (N : Mat(2, ℤ)) τ)
        * wordSigmaS z τ N h0N := by
  subst hN
  exact wordSigmaS_of_lowerLeft_ne_zero z τ M h0 hz h0N

/-! ### Periods stay positive along `wordSigmaS`'s own recursion

Connects `SICs.SL2Z.WordPeriods.flt_and_fltDenominator_pos_of_hjStep` — proved
there via a standalone one-step peel — to `wordSigmaS`'s own well-founded recursion on `(M, h0)`,
so that positivity can be cited for the actual matrices `wordSigmaS` recurses into. -/

/-- **Matrices `wordSigmaS` recurses into, strictly after its seed `M`.** The smallest relation
with `M ⤳ (hjStep M).2` whenever `M`'s lower-left entry is nonzero, extended transitively while
the lower-left entry stays nonzero at each intermediate matrix. Built from the exact step
`wordSigmaS_of_lowerLeft_ne_zero` peels (`N ↦ (hjStep N).2`), so `WordSigmaSVisits M N` holds
exactly when `N` is the second recursive argument somewhere in `wordSigmaS z τ M h0`'s unfolding,
for any `z, τ`. -/
inductive WordSigmaSVisits : SL(2, ℤ) → SL(2, ℤ) → Prop where
  /-- The first peel: `wordSigmaS_of_lowerLeft_ne_zero`'s recursive argument at the seed. -/
  | base {X : SL(2, ℤ)} (hz : X 1 0 ≠ 0) : WordSigmaSVisits X (hjStep X).2
  /-- One further peel from an already-visited, still-nonzero matrix. -/
  | tail {X Y : SL(2, ℤ)} (h : WordSigmaSVisits X Y) (hz : Y 1 0 ≠ 0) :
      WordSigmaSVisits X (hjStep Y).2

/-- Every matrix `wordSigmaS` visits has a nonnegative lower-left entry, matching the invariant
`wordSigmaS` itself maintains at every recursive call (`h0'` in `wordSigmaS`'s definition):
immediate from `hjStep_snd_lowerLeft`/`Int.emod_nonneg`, by induction on `WordSigmaSVisits`. -/
theorem WordSigmaSVisits.lowerLeft_nonneg {M N : SL(2, ℤ)} (h : WordSigmaSVisits M N) :
    0 ≤ N 1 0 := by
  induction h with
  | base hz => rw [hjStep_snd_lowerLeft]; exact Int.emod_nonneg _ hz
  | tail _ hz _ => rw [hjStep_snd_lowerLeft]; exact Int.emod_nonneg _ hz

/-- **Visits compose.** A matrix visited from `N` is visited from any `M` that already visits `N`:
induction on the second walk, whose peels extend the first. This is what lets a hypothesis
quantified over the matrices `wordSigmaS z τ M h0` visits be handed down to the recursive call at
`(hjStep M).2`. -/
theorem WordSigmaSVisits.trans {M N P : SL(2, ℤ)} (h₁ : WordSigmaSVisits M N)
    (h₂ : WordSigmaSVisits N P) : WordSigmaSVisits M P := by
  induction h₂ with
  | base hz => exact h₁.tail hz
  | tail _ hz ih => exact ih.tail hz

/-- **Every modulus `wordSigmaS` calls `sigmaSHonest` at stays positive throughout the whole
word**, given only that the seed's Jacobi denominator at `τ` starts positive: for any matrix `N`
that `wordSigmaS z τ M h0`'s recursion actually visits
(`WordSigmaSVisits M N`), both `N`'s period and its own Jacobi denominator at `τ` are positive —
so `sigmaSHonest`'s call there is honestly evaluable
(`SICs.Cocycle.SigmaS.Reduction.sigmaSHonest_eq_sigmaS_of_mem`), not merely a total placeholder.
Proved by induction on `WordSigmaSVisits`, reapplying
`flt_and_fltDenominator_pos_of_hjStep` at each peel: its Jacobi-denominator conclusion
supplies the next peel's hypothesis along `wordSigmaS`'s recursive structure. -/
theorem WordSigmaSVisits.period_pos (τ : ℝ) (hτ : Irrational τ) {M N : SL(2, ℤ)}
    (h0 : 0 ≤ M 1 0) (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) τ)
    (h : WordSigmaSVisits M N) :
    0 < flt (N : Mat(2, ℤ)) τ ∧
      0 < fltDenominator (N : Mat(2, ℤ)) τ := by
  induction h with
  | base hz =>
      exact flt_and_fltDenominator_pos_of_hjStep M τ hτ (h0.lt_of_ne (Ne.symm hz)) hjac
  | tail h hz ih =>
      obtain ⟨-, hjacY⟩ := ih
      have hYpos := (h.lowerLeft_nonneg).lt_of_ne (Ne.symm hz)
      exact flt_and_fltDenominator_pos_of_hjStep _ τ hτ hYpos hjacY

end SIC
