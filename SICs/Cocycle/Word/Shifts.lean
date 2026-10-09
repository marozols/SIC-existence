/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Cocycle.Word.Basic

/-!
# Quasiperiodicity of the word-chained `σ_M` in its first argument

The response of `wordSigmaS` to a lattice shift: one q-Pochhammer factor per side.

This file supplies the one analytic ingredient [AFK25, Lemma 2.14, `lm:shinperiodicity`] needs on
the real line: how the word-chained cocycle `SICs.Cocycle.Word.Basic.wordSigmaS` responds when its
first
argument moves by a lattice vector `aτ + b`.

The answer (`wordSigmaS_lattice_shift`) is
```
σ_M(z + aτ + b, τ) · ϖ_{a·M₁₁ - b·M₁₀}(z / j_M(τ), M·τ) = σ_M(z, τ) · ϖ_a(z, τ),
```
one `q`-Pochhammer factor on each side and nothing else.

## Proof by telescoping

[AFK25]'s periodicity lemma cites [72, Kopp (2024), Proposition 4.35, `prop:invariance`], whose
argument runs entirely on `ℍ`: it compares two infinite products `ϖ` through the "coboundary"
expression [AFK25, equation (1.27), `eq:coboundary`],
`ש^r_M(τ) = ϖ(⟨⟨r,M·τ⟩⟩,M·τ)/ϖ(⟨⟨r,τ⟩⟩,τ)`, then extends by analytic continuation.
AFK25 states explicitly that this expression "does not make sense outside the upper half plane", so
the real-domain identity above is proved directly along `wordSigmaS`'s recursion. The two
`q`-Pochhammer factors telescope:

- one word step peels `M = T^k S N`, contributing the factor `σ_S(z/j_N(τ), N·τ)`;
- `SICs.Cocycle.SigmaS.Reduction.sigmaSHonest_lattice_shift` converts that factor's own shift into
  `ϖ_{m₁}(w,ν)/ϖ_{-m₂}(w/ν,-1/ν)` with `w = z/j_N(τ)`, `ν = N·τ`;
- `m₁ = a·N₁₁ - b·N₁₀` is precisely the *next* step's index, and `-m₂ = a·N₀₁ - b·N₀₀` is
  precisely the *current* one, because `M`'s bottom row is `N`'s top row
  (`SICs.SL2Z.Words.hjStep_snd_entries`/`hjStep_snd_topRight`), while
  `j_M(τ) = ν·j_N(τ)` and `M·τ = k - 1/ν`
  (`SICs.SL2Z.WordPeriods.fltDenominator_hjStep`/`flt_hjStep`) match the two
  arguments.

So each step hands its neighbour exactly the factor it needs, and the induction closes with no
division and no cancellation hypothesis.

## Hypotheses

`Irrational τ` and `0 < j_M(τ)` are the word walk's own standing hypotheses — the latter is [AFK25,
Definition 1.15, `def:sl2ldmndf`]'s `τ ∈ D_M` on the real line
(`SICs.Cocycle.Domains.mem_sfDomain_ofReal_iff`), and it also pins the recursion's terminal matrix
down to `+T^k` rather than `-T^k` (`SICs.SL2Z.Basic.eq_T_zpow_of_lowerLeft_eq_zero`'s own
hypothesis), which is what makes `wordSigmaS`'s base value `1` correct there.
`SigmaSLatticeFree τ z` is [AFK25, Lemma 2.14, `lm:shinperiodicity`]'s `r ∉ ℤ²` in disguise (see
`SICs.Cocycle.Modular.Shifts`).

## Main declarations

- `SigmaSLatticeFree.div_fltDenominator`: lattice-freeness transports along the Möbius action,
  so the hypothesis survives every word step.
- `div_fltDenominator_add_lattice`: the integer bookkeeping `(a,b) ↦ (m₁,m₂)` of a lattice
  shift under `z ↦ z / j_M(τ)`.
- `wordSigmaS_lattice_shift`: the quasiperiodicity identity above.

## References

- [AFK25] Appleby, Flammia, Kopp, arXiv:2501.03970v2, Lemma 2.14 (`lm:shinperiodicity`),
  equation (1.27).
-/

open ModularGroup MatrixGroups

open scoped MatrixGroups

namespace SIC

/-! ### Two elementary Möbius identities

Clearing the Jacobi denominator transports both lattice-freeness and lattice translations through
an integral Möbius transformation.  The explicit transformed indices drive the recursive shift
calculation. -/

/-- `(M·τ)·j_M(τ)` is the numerator `M₀₀τ + M₀₁`: the one algebraic fact relating the two `hjStep`
recursions (`SICs.SL2Z.WordPeriods.flt_hjStep`/`fltDenominator_hjStep`) to the
integer bookkeeping of the shift indices. -/
private lemma flt_mul_fltDenominator (N : Mat(2, ℤ)) (τ : ℝ)
    (hden : fltDenominator N τ ≠ 0) :
    flt N τ * fltDenominator N τ = (N 0 0 : ℝ) * τ + (N 0 1 : ℝ) := by
  have hden' : (N 1 0 : ℝ) * τ + (N 1 1 : ℝ) ≠ 0 := hden
  unfold flt fltDenominator
  exact div_mul_cancel₀ _ hden'

/-- **Lattice-freeness transports along the Möbius action.** If `z` avoids `ℤτ + ℤ`, then
`z / j_N(τ)` avoids `ℤ(N·τ) + ℤ`: a violation `z/j_N(τ) = a(N·τ) + b` clears denominators to
`z = (a·N₀₀ + b·N₁₀)τ + (a·N₀₁ + b·N₁₁)`, a lattice point for the original pair. No determinant
hypothesis is needed — only that the two coefficient pairs correspond, not that the
correspondence is invertible. -/
theorem SigmaSLatticeFree.div_fltDenominator {τ z : ℝ} (h : SigmaSLatticeFree τ z)
    {N : Mat(2, ℤ)} (hden : fltDenominator N τ ≠ 0) :
    SigmaSLatticeFree (flt N τ) (z / fltDenominator N τ) := by
  have hJval : fltDenominator N τ = (N 1 0 : ℝ) * τ + (N 1 1 : ℝ) := rfl
  have hnum := flt_mul_fltDenominator N τ hden
  intro a b hab
  refine h (a * N 0 0 + b * N 1 0) (a * N 0 1 + b * N 1 1) ?_
  rw [div_eq_iff hden] at hab
  rw [hab, add_mul, mul_assoc, hnum, hJval]
  push_cast
  ring

/-- **A lattice shift upstairs is a lattice shift downstairs.** Dividing by `j_M(τ)` carries
`z ↦ z + aτ + b` to `w ↦ w + m₁(M·τ) + m₂` with
```
m₁ = a·M₁₁ - b·M₁₀,      m₂ = -a·M₀₁ + b·M₀₀,
```
the unique integer solution of `(Mᵀ)⁻¹`-shape (it is `det M = 1` that makes it integral). This
is the index bookkeeping the whole shift calculus runs on: `m₁` is the index
`wordSigmaS_lattice_shift` carries, and `-m₂` is the one it hands to the next word step. -/
theorem div_fltDenominator_add_lattice (M : SL(2, ℤ))
    (τ z : ℝ) (a b : ℤ)
    (hden : fltDenominator (M : Mat(2, ℤ)) τ ≠ 0) :
    (z + (a : ℝ) * τ + (b : ℝ)) /
        fltDenominator (M : Mat(2, ℤ)) τ =
      z / fltDenominator (M : Mat(2, ℤ)) τ +
        ((a * M 1 1 - b * M 1 0 : ℤ) : ℝ) *
          flt (M : Mat(2, ℤ)) τ
        + ((-(a * M 0 1) + b * M 0 0 : ℤ) : ℝ) := by
  have hJval : fltDenominator (M : Mat(2, ℤ)) τ =
      (M 1 0 : ℝ) * τ + (M 1 1 : ℝ) := rfl
  have hnum := flt_mul_fltDenominator (M : Mat(2, ℤ)) τ hden
  have hdetR : (M 0 0 : ℝ) * (M 1 1 : ℝ) - (M 0 1 : ℝ) * (M 1 0 : ℝ) = 1 := by
    exact det_fin_two_cast_eq_one M
  rw [div_eq_iff hden, add_mul, add_mul, div_mul_cancel₀ _ hden, mul_assoc, hnum, hJval]
  push_cast
  linear_combination (-((a : ℝ) * τ + (b : ℝ))) * hdetR

/-! ### The lattice-shift law for `wordSigmaS`

Induction along the same Hirzebruch--Jung recursion as `wordSigmaS` propagates the single-letter
shift law through the whole product.  Positivity selects the correct terminal translation matrix. -/

/-- **The base case of `wordSigmaS_lattice_shift`.** At a pure `T`-power both `wordSigmaS` values
are `1`, and positivity of the Jacobi denominator forces `M₁₁ = M₀₀ = 1`, so `j_M(τ) = 1` and
`M·τ = τ + M₀₁`: the two `q`-Pochhammer factors are then the same one, up to the integer period
shift `qPochhammerFin_tau_add_intCast` absorbs. This is where `0 < j_M(τ)` earns its place — it
rules out the terminal matrix `-T^k`, at which `wordSigmaS`'s value `1` would be wrong
(`SICs.SL2Z.Basic.eq_T_zpow_of_lowerLeft_eq_zero` needs exactly this sign). -/
private lemma wordSigmaS_lattice_shift_base {τ : ℝ} (z : ℝ) (a b : ℤ) (M : SL(2, ℤ))
    (h0 : 0 ≤ M 1 0) (hz : M 1 0 = 0)
    (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) τ) :
    wordSigmaS (z + a * τ + b) τ M h0 *
        qPochhammerFin (a * M 1 1 - b * M 1 0)
          ((z : ℂ) / ((fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ))
          ((flt (M : Mat(2, ℤ)) τ : ℝ) : ℂ) =
      wordSigmaS z τ M h0 * qPochhammerFin a (z : ℂ) (τ : ℂ) := by
  have hindex : a * M 1 1 - b * M 1 0 = a := by
    rw [(diag_eq_one_of_lowerLeft_eq_zero hz hjac).2, hz]; ring
  rw [wordSigmaS_of_lowerLeft_eq_zero _ _ _ _ hz, wordSigmaS_of_lowerLeft_eq_zero _ _ _ _ hz,
    hindex, fltDenominator_eq_one_of_lowerLeft_eq_zero hz hjac,
    flt_eq_add_of_lowerLeft_eq_zero hz hjac, one_mul, one_mul, Complex.ofReal_one, div_one,
    show ((τ + (M 0 1 : ℝ) : ℝ) : ℂ) = ((τ : ℝ) : ℂ) + ((M 0 1 : ℤ) : ℂ) from by push_cast; ring]
  exact qPochhammerFin_tau_add_intCast a (z : ℂ) τ (M 0 1)

/-- Transports the finite shift factor through one word step; used by
`wordSigmaS_lattice_shift_step`. -/
private lemma qPochhammerFin_lattice_hjStep {τ : ℝ} (hτ : Irrational τ)
    (z : ℝ) (a b : ℤ) {M N : SL(2, ℤ)} (hN : (hjStep M).2 = N) :
    qPochhammerFin (a * M 1 1 - b * M 1 0)
            ((z : ℂ) / ((fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ))
            ((flt (M : Mat(2, ℤ)) τ : ℝ) : ℂ) =
          qPochhammerFin (-(-(a * N 0 1) + b * N 0 0))
            ((z : ℂ) / ((fltDenominator (N : Mat(2, ℤ)) τ : ℝ) : ℂ) /
              ((flt (N : Mat(2, ℤ)) τ : ℝ) : ℂ))
            (-1 / ((flt (N : Mat(2, ℤ)) τ : ℝ) : ℂ)) := by
  have hN00 : N 0 0 = M 1 0 := by rw [← hN]; exact (hjStep_snd_entries M).1
  have hN01 : N 0 1 = M 1 1 := by rw [← hN]; exact hjStep_snd_topRight M
  have hMden : fltDenominator (M : Mat(2, ℤ)) τ =
      flt (N : Mat(2, ℤ)) τ *
        fltDenominator (N : Mat(2, ℤ)) τ := by
    rw [← hN]; exact fltDenominator_hjStep M τ hτ
  have hMflt : flt (M : Mat(2, ℤ)) τ =
      ((hjStep M).1 : ℝ) - 1 / flt (N : Mat(2, ℤ)) τ := by
    rw [← hN]; exact flt_hjStep M τ hτ
  rw [show a * M 1 1 - b * M 1 0 = -(-(a * N 0 1) + b * N 0 0) from by
        rw [hN00, hN01]; ring,
    hMden, hMflt,
    show ((((hjStep M).1 : ℝ) - 1 / flt (N : Mat(2, ℤ)) τ : ℝ) : ℂ) =
        (((-1 / flt (N : Mat(2, ℤ)) τ : ℝ)) : ℂ) + ((hjStep M).1 : ℂ)
      from by push_cast; ring,
    qPochhammerFin_tau_add_intCast _ _
      ((-1 / flt (N : Mat(2, ℤ)) τ : ℝ) : ℂ)
      (hjStep M).1]
  congr 1
  · push_cast; ring
  · push_cast; ring

/-- The single-letter shift law propagates the induction hypothesis; used by
`wordSigmaS_lattice_shift`. -/
private lemma wordSigmaS_lattice_shift_step {τ : ℝ} (hτ : Irrational τ)
    (z : ℝ) (a b : ℤ) (hlat : SigmaSLatticeFree τ z) {M N : SL(2, ℤ)}
    (h0 : 0 ≤ M 1 0) (hz : M 1 0 ≠ 0) (hN : (hjStep M).2 = N) (h0N : 0 ≤ N 1 0)
    (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) τ)
    (hih :
    wordSigmaS (z + a * τ + b) τ N h0N *
        qPochhammerFin (a * N 1 1 - b * N 1 0)
          ((z : ℂ) / ((fltDenominator (N : Mat(2, ℤ)) τ : ℝ) : ℂ))
          ((flt (N : Mat(2, ℤ)) τ : ℝ) : ℂ) =
      wordSigmaS z τ N h0N * qPochhammerFin a (z : ℂ) (τ : ℂ)) :
    wordSigmaS (z + a * τ + b) τ M h0 *
        qPochhammerFin (a * M 1 1 - b * M 1 0)
          ((z : ℂ) / ((fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ))
          ((flt (M : Mat(2, ℤ)) τ : ℝ) : ℂ) =
      wordSigmaS z τ M h0 * qPochhammerFin a (z : ℂ) (τ : ℂ) := by
  have hpos : 0 < M 1 0 := h0.lt_of_ne (Ne.symm hz)
  obtain ⟨hνpos, hJpos⟩ := flt_and_fltDenominator_pos_of_hjStep M τ hτ hpos hjac
  rw [hN] at hνpos hJpos
  have hJ0 := hJpos.ne'
  have harg := div_fltDenominator_add_lattice N τ z a b hJ0
  have hss := sigmaSHonest_lattice_shift
    (z / fltDenominator (N : Mat(2, ℤ)) τ)
    (flt (N : Mat(2, ℤ)) τ) (a * N 1 1 - b * N 1 0)
    (-(a * N 0 1) + b * N 0 0) hνpos (hlat.div_fltDenominator hJ0)
  rw [show ((z / fltDenominator (N : Mat(2, ℤ)) τ : ℝ) : ℂ) =
      (z : ℂ) / ((fltDenominator (N : Mat(2, ℤ)) τ : ℝ) : ℂ) from by
    push_cast; ring] at hss
  rw [wordSigmaS_step (z + a * τ + b) τ h0 hz hN h0N, wordSigmaS_step z τ h0 hz hN h0N,
    qPochhammerFin_lattice_hjStep hτ z a b hN, harg]
  linear_combination (wordSigmaS (z + a * τ + b) τ N h0N) * hss +
    (sigmaSHonest (z / fltDenominator (N : Mat(2, ℤ)) τ)
      (flt (N : Mat(2, ℤ)) τ)) * hih

/-- **Quasiperiodicity of the word-chained `σ_M` in its first argument.** Moving `z` by a lattice
vector `aτ + b` multiplies `σ_M(z,τ)` by `ϖ_a(z,τ)/ϖ_{a·M₁₁ - b·M₁₀}(z/j_M(τ), M·τ)`, stated
multiplicatively so that no nonvanishing hypothesis is needed:
```
σ_M(z + aτ + b, τ) · ϖ_{a·M₁₁ - b·M₁₀}(z/j_M(τ), M·τ) = σ_M(z, τ) · ϖ_a(z, τ).
```
On `ℍ`, with
`σ_M(z,τ) = ϖ(z/j_M(τ), M·τ)/ϖ(z,τ)` the identity is two applications of
`ϖ(x + kν, ν) = ϖ(x,ν)/ϖ_k(x,ν)`, the index `a·M₁₁ - b·M₁₀` being the unique integer `m₁` with
`(aτ+b)/j_M(τ) = m₁(M·τ) + m₂`.

This is the real-domain periodicity statement of [AFK25, Lemma 2.14,
`lm:shinperiodicity`], which the source proves on `ℍ` from [72, Kopp (2024), Proposition 4.35,
`prop:invariance`].

The lattice-free hypothesis `hlat` is the real-line form of the `r ∉ ℤ²` assumption in
`sfModularCocycleReal_add_intVec`; `hjac` is its domain condition `τ ∈ D_M`.
See the file docstring for why the proof follows the word rather than the source's `ℍ` argument. -/
theorem wordSigmaS_lattice_shift {τ : ℝ} (hτ : Irrational τ) (z : ℝ) (a b : ℤ)
    (hlat : SigmaSLatticeFree τ z) (M : SL(2, ℤ)) (h0 : 0 ≤ M 1 0)
    (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) τ) :
    wordSigmaS (z + a * τ + b) τ M h0 *
        qPochhammerFin (a * M 1 1 - b * M 1 0)
          ((z : ℂ) / ((fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ))
          ((flt (M : Mat(2, ℤ)) τ : ℝ) : ℂ) =
      wordSigmaS z τ M h0 * qPochhammerFin a (z : ℂ) (τ : ℂ) := by
  induction M, h0 using wordSigmaS.induct with
  | case1 M h0 hz _ => exact wordSigmaS_lattice_shift_base z a b M h0 hz hjac
  | case2 M h0 hz hpos h0N _ _ ih =>
      have hJpos := (flt_and_fltDenominator_pos_of_hjStep M τ hτ hpos hjac).2
      exact wordSigmaS_lattice_shift_step hτ z a b hlat h0 hz rfl h0N hjac (ih hJpos)

end SIC
