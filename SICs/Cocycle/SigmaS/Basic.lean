/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Analysis.PeriodLattice
import SICs.SpecialFunctions.DoubleSine.Identities
import SICs.SpecialFunctions.DoubleSine.SigmaSExponent
import SICs.SpecialFunctions.QPochhammer.Finite

/-!
# The real sigma-S formula and elementary shift laws

Base and shifted sigma-S formulas, elementary shifts, and off-lattice nonvanishing.

The base value is [AFK25, equation (8.6), `eq:SFJacobiCocycleTermsDoubleSine`], written
with the double sine; equation (8.9) attaches an explicit lattice shift. The double-sine
quasiperiodicity laws supply exactly the finite q-Pochhammer factors inserted or removed
by the two elementary shifts. Off the lattice these factors are nonzero.
-/

noncomputable section

open Complex Real

namespace SIC

/-! ### `σ_S` at real arguments

At a real quadratic modulus the infinite product `qPochhammer` does not converge.
`sigmaSBase` and `sigmaS` define the real generator using the double sine of
`SICs.SpecialFunctions.DoubleSine.RealIntegral` and [AFK25, equation (8.9)].

`sigmaSBase` is [AFK25, equation (8.6), `eq:SFJacobiCocycleTermsDoubleSine`] specialized to the
unshifted base point, where the source's extended double sine `Î` coincides with the plain double
sine `S₂ = doubleSine'`, so no extended-double-sine machinery is needed here at all.

`sigmaS` then reaches every shifted real argument `z + m₁τ + m₂` (`m₁ m₂ : ℤ`) directly via [AFK25,
equation (8.9)], `σ_S(z+m₁τ+m₂,τ) = ϖ_{m₁}(z,τ) / ϖ_{-m₂}(z/τ,-1/τ) · σ_S(z,τ)`, taken as a
*definition* on the real line (proved on `ℍ` from [72, Kopp (2024), Lemma 2.3, `lem:ell`] by a
one-line telescoping argument). Because the shift data `(z, m₁, m₂)` is always supplied explicitly
by the caller rather than inferred from a bare real number, and `qPochhammerFin` is a finite
closed-form product for every `m₁ m₂ : ℤ`, this needs no path-independence or well-definedness
proof: it is one formula, one evaluation, unlike `Î`. -/

/-- The real restriction of `faddeevSExpArg`, the exponent in [AFK25, equation (8.6),
`eq:SFJacobiCocycleTermsDoubleSine`]. -/
noncomputable def sfExpArg (z τ : ℝ) : ℂ := faddeevSExpArg z τ

/-- `σ_S` at the unshifted base point: [AFK25, equation (8.6),
    `eq:SFJacobiCocycleTermsDoubleSine`] with the extended double sine `Î` replaced by the plain
    double sine `S₂ = doubleSine'` (valid at the base point since
    `Î(z+1,τ) = S₂(z+1,τ)` there):
      σ_S(z,τ) = exp(πi/(12τ) · (6z² + 6(1-τ)z + τ² - 3τ + 1)) / S₂(z+1,τ). -/
noncomputable def sigmaSBase (z τ : ℝ) : ℂ :=
  Complex.exp (sfExpArg z τ) /
    (doubleSine' (z + 1) τ : ℂ)

/-- `σ_S` at a real argument shifted by `m₁τ + m₂` from the base point `z`: [AFK25, equation
    (8.9)] as the defining formula on the real line:
      σ_S(z+m₁τ+m₂,τ) = ϖ_{m₁}(z,τ) / ϖ_{-m₂}(z/τ,-1/τ) · σ_S(z,τ).
    `sigmaS_zero_zero` records that this reduces to `sigmaSBase` at `m₁ = m₂ = 0`. -/
noncomputable def sigmaS (z τ : ℝ) (m₁ m₂ : ℤ) : ℂ :=
  qPochhammerFin m₁ z τ / qPochhammerFin (-m₂) (z / τ) (-1 / τ) * sigmaSBase z τ

/-- `sigmaS` at zero shift is definitionally `sigmaSBase`, since `qPochhammerFin` at `n = 0` is
`1`. -/
@[simp]
lemma sigmaS_zero_zero (z τ : ℝ) : sigmaS z τ 0 0 = sigmaSBase z τ := by
  simp [sigmaS, qPochhammerFin]

/-! ### `sigmaS`-triple and `qPochhammerFin` shift lemmas

General algebraic consequences of the definitions of `sigmaS`, `sigmaSBase`, and `qPochhammerFin`
above, with no reference to any particular real quadratic argument.
`SICs.Principal.Cocycle.SFReduction` uses these and [AFK25, eq. (8.9)] to express the principal
family's `σ_{A_d}` as a finite product. -/

/-- Multiplying three `sigmaS` factors at base points `w3, w2, w1` with shift triples
`(0,0), (0,-k), (k,-ℓ)` respectively collapses the finite `qPochhammerFin` bookkeeping to a single
ratio times the bare `sigmaSBase` product -- exactly [AFK25, eq. (8.9)] applied to each factor of
the three-factor word decomposition, per the canonical reduction data
(`principalZ_div_principalRoot_eq`,
`principalZ_div_principalRoot_sq_eq`). -/
lemma sigmaS_triple_eq (w1 w2 w3 τ : ℝ) (k ℓ : ℤ) :
    sigmaS w3 τ 0 0 * sigmaS w2 τ 0 (-k) * sigmaS w1 τ k (-ℓ) =
      qPochhammerFin k w1 τ /
        (qPochhammerFin k (w2 / τ) (-1 / τ) * qPochhammerFin ℓ (w1 / τ) (-1 / τ)) *
        (sigmaSBase w3 τ * sigmaSBase w2 τ * sigmaSBase w1 τ) := by
  rw [sigmaS_zero_zero]
  unfold sigmaS
  have h0 : qPochhammerFin 0 w2 τ = 1 := by simp [qPochhammerFin]
  rw [h0, neg_neg, neg_neg]
  ring

/-- `sigmaSBase` unfolded through `sfExpArg`. -/
lemma sigmaSBase_eq_exp_div (z τ : ℝ) :
    sigmaSBase z τ = Complex.exp (sfExpArg z τ) / (doubleSine' (z + 1) τ : ℂ) := rfl

/-- **The exponential prefactor is invariant under the double sine's reflection** `z ↦ τ - 1 - z`:
the bracket `6z² + 6(1-τ)z + τ² - 3τ + 1` is unchanged, since it is `6z² - 6(τ-1)z + τ² - 3τ + 1`
and the reflection fixes that quadratic's axis. -/
lemma sfExpArg_reflect (z τ : ℝ) : sfExpArg (τ - 1 - z) τ = sfExpArg z τ := by
  unfold sfExpArg
  push_cast
  exact faddeevSExpArg_reflect z τ

/-- **`σ_S`'s base value under reflection.** `S₂(·, τ)` has `ω₁ = τ`, `ω₂ = 1`, so its reflection
`S₂(τ + 1 - w)·S₂(w) = 1` (`doubleSine_mul_reflect` from
`SICs.SpecialFunctions.DoubleSine.Identities`)
applies to `w = z + 1` and sends the base point `z` to `τ - 1 - z`. Both double sines cancel and
only the (invariant, by `sfExpArg_reflect`) exponential prefactor is left, squared:

```text
σ_S^base(z,τ) · σ_S^base(τ-1-z,τ) = exp(2·X(z,τ)).
```

Unconditional -- no positivity or domain hypothesis, since `doubleSine_mul_reflect` needs none.

This is the real-line ingredient for a reflection law at the level of the word cocycle, and hence
for [72, Kopp (2024), Theorem 4.36, `thm:shincharacter`] and [AFK25, Theorem 2.11, `thm:funchar`] on
the real line: `z ↦ -z` is this reflection composed with the lattice shift by `-(τ - 1)`, which
`SICs.Cocycle.SigmaS.Reduction` already handles. -/
theorem sigmaSBase_mul_reflect (z τ : ℝ) :
    sigmaSBase z τ * sigmaSBase (τ - 1 - z) τ = Complex.exp (2 * sfExpArg z τ) := by
  have hrefl : (doubleSine' (τ - 1 - z + 1) τ : ℝ) * (doubleSine' (z + 1) τ : ℝ) = 1 := by
    have h := doubleSine_mul_reflect (z + 1) τ 1
    have harg : τ + 1 - (z + 1) = τ - 1 - z + 1 := by ring
    rw [harg] at h
    exact h
  have hreflC : ((doubleSine' (z + 1) τ : ℝ) : ℂ) * ((doubleSine' (τ - 1 - z + 1) τ : ℝ) : ℂ)
      = 1 := by
    rw [← Complex.ofReal_mul, mul_comm, hrefl, Complex.ofReal_one]
  rw [sigmaSBase_eq_exp_div, sigmaSBase_eq_exp_div, div_mul_div_comm, hreflC, div_one,
    ← Complex.exp_add, sfExpArg_reflect]
  ring_nf

/-- The real specialization `1 - e^{2iθ} = e^{iθ - iπ/2} · 2 sin θ` of
`one_sub_exp_two_pi_I_eq`, used by the two generator shift laws. -/
lemma one_sub_exp_two_mul_I_eq (θ : ℝ) :
    (1 : ℂ) - Complex.exp (2 * I * θ) =
      Complex.exp (I * θ - π * I / 2) * (2 * (Real.sin θ : ℂ)) := by
  have h := one_sub_exp_two_pi_I_eq ((θ : ℂ) / π)
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show (2 : ℂ) * π * I * (θ / π) = 2 * I * θ by field_simp,
    show (π : ℂ) * I * (θ / π) = I * θ by field_simp,
    mul_div_cancel₀ _ hπ, ← Complex.ofReal_sin] at h
  rw [h, Complex.exp_sub, show (π : ℂ) * I / 2 = π / 2 * I by ring,
    Complex.exp_pi_div_two_mul_I]
  field_simp
  simp [I_sq]

/-- `sfExpArg`'s value shifts by an explicit amount when its first argument increases by `1`. -/
lemma sfExpArg_add_one (z τ : ℝ) (hτ : τ ≠ 0) :
    sfExpArg (z + 1) τ - sfExpArg z τ = π * I * (z + 1) / τ - π * I / 2 := by
  unfold sfExpArg
  have hτC : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ
  push_cast
  rw [faddeevSExpArg_add_one (z : ℂ) (τ : ℂ) hτC]
  ring

/-- **`sigmaSBase`'s single-step shift-by-one identity.** Provided both `z` and `z + 1` sit
inside the *open* sub-interval `(0, τ)` (a restriction inherited from
`doubleSine'_quasiperiod_one`, not from `sigmaSBase`'s own wider domain `(-1, τ)`), incrementing
`z` by `1` multiplies `sigmaSBase` by exactly the index-`1` `qPochhammerFin` factor
`1 - e^{2πi(z+1)/τ}`. Combined with `qPochhammerFin_add_one_sub_period`, this is the ingredient
`sigmaS_add_one_sub_one` below needs to show `sigmaS`'s value is independent of which valid
integer shift lands a raw real argument in `sigmaSBase`'s domain. -/
lemma sigmaSBase_add_one (z τ : ℝ) (hτ : 0 < τ) (hz : 0 < z + 1) (hzu : z + 1 < τ) :
    sigmaSBase (z + 1) τ =
      sigmaSBase z τ * (1 - Complex.exp (2 * π * I * ((z + 1) / τ))) := by
  have hds : doubleSine' (z + 1 + 1) τ =
      doubleSine' (z + 1) τ / (2 * Real.sin (π * (z + 1) / τ)) :=
    doubleSine'_quasiperiod_one (z + 1) τ hτ hz hzu
  have hsin_pos : 0 < Real.sin (π * (z + 1) / τ) := by
    apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
    rw [div_lt_iff₀ hτ]; nlinarith [Real.pi_pos]
  have hexp : Complex.exp (sfExpArg (z + 1) τ) =
      Complex.exp (sfExpArg z τ) * Complex.exp (π * I * (z + 1) / τ - π * I / 2) := by
    rw [← Complex.exp_add, ← sfExpArg_add_one z τ hτ.ne']
    congr 1; ring
  have hone_sub : (1 : ℂ) - Complex.exp (2 * π * I * ((z + 1) / τ)) =
      Complex.exp (π * I * (z + 1) / τ - π * I / 2) * (2 * (Real.sin (π * (z + 1) / τ) : ℂ)) := by
    have hkey := one_sub_exp_two_mul_I_eq (π * (z + 1) / τ)
    rw [show (2 : ℂ) * I * ((π * (z + 1) / τ : ℝ) : ℂ) = 2 * π * I * ((z + 1) / τ) from by
        push_cast; ring,
      show I * ((π * (z + 1) / τ : ℝ) : ℂ) - π * I / 2 = π * I * (z + 1) / τ - π * I / 2 from by
        push_cast; ring] at hkey
    exact hkey
  rw [sigmaSBase_eq_exp_div, sigmaSBase_eq_exp_div, hds, hexp, hone_sub]
  have h2sin_ne : (2 * (Real.sin (π * (z + 1) / τ) : ℂ)) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or, Complex.ofReal_eq_zero]
    exact hsin_pos.ne'
  push_cast
  field_simp

/-- **`sigmaS`'s single-step shift-invariance.** Representing the same raw real point `z + n` via
the shifted base point `z + 1` and shift `n - 1` gives the same value as via the base point `z`
and shift `n`, provided both `z` and `z + 1` sit inside `sigmaSBase`'s valid sub-domain `(0, τ)`
(the same restriction `sigmaSBase_add_one` needs). Combined with `sigmaS_zero_zero` as base case,
induction on `n` extends this to *any* two valid shifts reachable from each other by unit steps
within a connected sub-interval of `(-1, τ)`. -/
theorem sigmaS_add_one_sub_one (z τ : ℝ) (n : ℤ) (hτ : 0 < τ) (hz : 0 < z + 1) (hzu : z + 1 < τ) :
    sigmaS (z + 1) τ 0 (n - 1) = sigmaS z τ 0 n := by
  have hτ0 : τ ≠ 0 := hτ.ne'
  -- Canonical single form for `(z+1)/τ` as a complex number: every other shape this proof
  -- produces (from `unfold sigmaS`, from `qPochhammerFin_add_one_sub_period`'s `v - τ`, ...) is
  -- bridged back to `w` by an explicit `ring`/`push_cast` identity before any `rw` combines them,
  -- since `ring`/`field_simp` cannot see through mismatched-but-equal arguments of the opaque
  -- `qPochhammerFin`/`Complex.exp` atoms.
  set w : ℂ := (((z + 1) / τ : ℝ) : ℂ) with hw_def
  have hq0 : qPochhammerFin (0 : ℤ) (z : ℂ) (τ : ℂ) = 1 := by simp [qPochhammerFin]
  have hq0' : qPochhammerFin (0 : ℤ) ((z + 1 : ℝ) : ℂ) (τ : ℂ) = 1 := by simp [qPochhammerFin]
  have hrw1 : sigmaS z τ 0 n = sigmaSBase z τ / qPochhammerFin (-n) (z / τ) (-1 / τ) := by
    unfold sigmaS; rw [hq0]; ring
  have hA1 : ((z : ℂ) + 1) / τ = w := by rw [hw_def]; push_cast; ring
  have hA1' : (((z + 1 : ℝ) : ℂ)) / τ = w := by rw [hw_def, Complex.ofReal_div]
  have hrw2 : sigmaS (z + 1) τ 0 (n - 1) =
      sigmaSBase (z + 1) τ / qPochhammerFin (-(n - 1)) w (-1 / τ) := by
    unfold sigmaS; rw [hq0', hA1']
    ring
  have hA2 : (z : ℂ) / τ - (-1 / τ) = w := by rw [hw_def]; push_cast; ring
  have hval : (1 : ℂ) - Complex.exp (2 * π * I * w) ≠ 0 := by
    rw [hw_def]
    apply one_sub_exp_two_pi_I_ne_zero_of_forall_ne_int
    intro m hm
    have hmR : ((z + 1) / τ : ℝ) = (m : ℝ) := hm
    rw [div_eq_iff hτ0] at hmR
    rcases lt_trichotomy m 0 with hm0 | hm0 | hm0
    · have : (m : ℝ) * τ < 0 := mul_neg_of_neg_of_pos (by exact_mod_cast hm0) hτ
      linarith
    · rw [hm0] at hmR; simp at hmR; linarith
    · have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm0
      nlinarith
  have hkey := qPochhammerFin_add_one_sub_period (-n) ((z : ℂ) / τ) (-1 / τ)
    (fun _ => by rw [hA2]; exact hval)
  rw [show (-n + 1 : ℤ) = -(n - 1) from by ring, hA2] at hkey
  rw [hrw1, hrw2, sigmaSBase_add_one z τ hτ hz hzu, hA1, hkey]
  field_simp

/-- **`sigmaS`'s shift-independence, in full.** Iterating `sigmaS_add_one_sub_one` shows `sigmaS`
evaluated via *any* two base points `z` and `z + k` (`k : ℕ`) that land the same raw argument
`z + n` in `sigmaSBase`'s domain agree, as long as the whole connecting segment stays inside
`(-1, τ)` — automatically true whenever both endpoints `z` and `z + k` do, since that domain is an
interval. -/
theorem sigmaS_add_natCast_sub_natCast (z τ : ℝ) (n : ℤ) (k : ℕ) (hτ : 0 < τ)
    (hz : -1 < z) (hzu : z + k < τ) :
    sigmaS (z + k) τ 0 (n - k) = sigmaS z τ 0 n := by
  induction k with
  | zero => simp
  | succ m ih =>
    have hzu_m : (z : ℝ) + m < τ := by push_cast at hzu ⊢; linarith
    have hstep := sigmaS_add_one_sub_one (z + m) τ (n - m) hτ
      (by push_cast at hzu ⊢; linarith) (by push_cast at hzu ⊢; linarith)
    have heq1 : (z : ℝ) + ((m + 1 : ℕ) : ℝ) = z + m + 1 := by push_cast; ring
    have heq2 : n - ((m + 1 : ℕ) : ℤ) = n - m - 1 := by push_cast; ring
    rw [heq1, heq2, hstep]
    exact ih hzu_m

/-! ### The period-direction quasiperiodicity of `sigmaSBase`

Combining the double-sine period law with the exponential prefactor shows that shifting the base
point by `τ` contributes one explicit `q`-Pochhammer factor. -/

/-- `sfExpArg`'s value shifts by an explicit amount when its first argument increases by the
period `τ`. The period analogue of `sfExpArg_add_one`; the shift is `π i (z + 1/2)`, with no
`1/τ` denominator surviving. -/
lemma sfExpArg_add_period (z τ : ℝ) (hτ : τ ≠ 0) :
    sfExpArg (z + τ) τ - sfExpArg z τ = π * I * z + π * I / 2 := by
  have hτC : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ
  calc
    _ = π * I * ((z : ℂ) + 1) - π * I / 2 := by
      simpa only [sfExpArg, Complex.ofReal_add] using
        (faddeevSExpArg_add_tau (z : ℂ) (τ : ℂ) hτC)
    _ = _ := by ring

/-- **`sigmaSBase`'s period-direction shift identity.** Provided `z` sits in `(-1, 0)` — the
restriction inherited from `doubleSine'_quasiperiod_tau` applied at `z + 1`, strictly narrower
than `sigmaSBase`'s own domain `(-1, τ)` — increasing `z` by the period `τ` multiplies
`sigmaSBase` by exactly the index-`1` `qPochhammerFin` factor `1 - e^{2πiz}`.

Together with `qPochhammerFin_add_one_sub_period` this gives `sigmaS_add_period_sub_one`, the
period-direction counterpart of `sigmaSBase_add_one`/`sigmaS_add_one_sub_one`. -/
lemma sigmaSBase_add_period (z τ : ℝ) (hτ : 0 < τ) (hz : -1 < z) (hzu : z < 0) :
    sigmaSBase (z + τ) τ = sigmaSBase z τ * (1 - Complex.exp (2 * π * I * z)) := by
  have hds : doubleSine' (z + 1 + τ) τ = doubleSine' (z + 1) τ / (2 * Real.sin (π * (z + 1))) :=
    doubleSine'_quasiperiod_tau (z + 1) τ hτ (by linarith) (by linarith)
  have hz1 : 0 < z + 1 := by linarith
  have hsin_pos : 0 < Real.sin (π * (z + 1)) := by
    apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
    nlinarith [Real.pi_pos]
  have hexp : Complex.exp (sfExpArg (z + τ) τ) =
      Complex.exp (sfExpArg z τ) * Complex.exp (π * I * z + π * I / 2) := by
    rw [← Complex.exp_add, ← sfExpArg_add_period z τ hτ.ne']
    congr 1; ring
  -- `1 - e^{2πiz} = e^{πiz + πi/2} · 2 sin(π(z+1))`: the sign flip `sin(π(z+1)) = -sin(πz)` is
  -- absorbed by `e^{πi} = -1`, which is why the exponent here is `+πi/2` where
  -- `sigmaSBase_add_one`'s is `-πi/2`.
  have hone_sub : (1 : ℂ) - Complex.exp (2 * π * I * z) =
      Complex.exp (π * I * z + π * I / 2) * (2 * (Real.sin (π * (z + 1)) : ℂ)) := by
    have hkey := one_sub_exp_two_mul_I_eq (π * (z + 1))
    rw [show (2 : ℂ) * I * ((π * (z + 1) : ℝ) : ℂ) = 2 * π * I * ((z : ℂ) + 1) from by
        push_cast; ring,
      show I * ((π * (z + 1) : ℝ) : ℂ) - π * I / 2 = π * I * z + π * I / 2 from by
        push_cast; ring] at hkey
    rw [exp_two_pi_I_eq_of_sub_intCast ((z : ℂ) + 1) (z : ℂ) 1 (by push_cast; ring)] at hkey
    exact hkey
  rw [sigmaSBase_eq_exp_div, sigmaSBase_eq_exp_div,
    show z + τ + 1 = z + 1 + τ from by ring, hds, hexp, hone_sub]
  have h2sin_ne : (2 * (Real.sin (π * (z + 1)) : ℂ)) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or, Complex.ofReal_eq_zero]
    exact hsin_pos.ne'
  push_cast
  field_simp

/-! ### Lifting the integer-direction results to an arbitrary period index

The period index occurs in a single finite-product factor.  Factoring it off extends the existing
integer-shift identities from period index zero to every integer index. -/

/-- **`sigmaS` factors through its period index.** The index `m₁` enters `sigmaS`'s defining
formula only through the single factor `ϖ_{m₁}(z,τ)`, so every `m₁ = 0` result lifts to arbitrary
`m₁` by carrying that factor along. -/
lemma sigmaS_eq_qPochhammerFin_mul (z τ : ℝ) (m₁ m₂ : ℤ) :
    sigmaS z τ m₁ m₂ = qPochhammerFin m₁ z τ * sigmaS z τ 0 m₂ := by
  unfold sigmaS
  rw [show qPochhammerFin (0 : ℤ) (z : ℂ) (τ : ℂ) = 1 from by simp [qPochhammerFin]]
  ring

/-- **`sigmaS`'s integer-direction shift-invariance, at an arbitrary period index.** The
`m₁`-general form of `sigmaS_add_natCast_sub_natCast`: since `ϖ_{m₁}` is `1`-periodic in its first
argument (`qPochhammerFin_add_intCast`), the extra factor `sigmaS_eq_qPochhammerFin_mul` isolates
is unchanged by the shift, so the `m₁ = 0` result carries over verbatim. -/
theorem sigmaS_add_natCast_sub_natCast' (z τ : ℝ) (m₁ n : ℤ) (k : ℕ) (hτ : 0 < τ)
    (hz : -1 < z) (hzu : z + k < τ) :
    sigmaS (z + k) τ m₁ (n - k) = sigmaS z τ m₁ n := by
  have hq : qPochhammerFin m₁ (((z + k : ℝ)) : ℂ) (τ : ℂ) = qPochhammerFin m₁ (z : ℂ) (τ : ℂ) := by
    rw [show (((z + k : ℝ)) : ℂ) = (z : ℂ) + ((k : ℤ) : ℂ) from by push_cast; ring]
    exact qPochhammerFin_add_intCast m₁ (z : ℂ) τ (k : ℤ)
  rw [sigmaS_eq_qPochhammerFin_mul (z + (k : ℝ)) τ m₁ (n - (k : ℤ)),
    sigmaS_eq_qPochhammerFin_mul z τ m₁ n, hq,
    sigmaS_add_natCast_sub_natCast z τ n k hτ hz hzu]

/-! ### The period-direction shift step

The base quasiperiodicity and the finite-product recurrence cancel exactly when the base point is
moved by `τ` and the period index is decremented. -/

/-- Adding the period changes the second finite-product argument by the integer `1`.
This isolates the integer periodicity used in `sigmaS_add_period_sub_one`. -/
private lemma sigmaS_secondFactor_add_period (z τ : ℝ) (m : ℤ) (hτ : τ ≠ 0) :
    qPochhammerFin (-m) (((z + τ : ℝ)) / (τ : ℂ)) (-1 / (τ : ℂ)) =
      qPochhammerFin (-m) ((z : ℂ) / (τ : ℂ)) (-1 / (τ : ℂ)) := by
  rw [show ((((z + τ : ℝ)) : ℂ)) / (τ : ℂ) =
      (z : ℂ) / (τ : ℂ) + ((1 : ℤ) : ℂ) by
    have hτC : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ
    push_cast
    field_simp]
  exact qPochhammerFin_add_intCast (-m) ((z : ℂ) / (τ : ℂ)) (-1 / (τ : ℂ)) 1

/-- **`sigmaS`'s period-direction shift step.** Representing the same raw real point
`z + m₁τ + m₂` via the shifted base point `z + τ` and period index `m₁ - 1` gives the same value
as via the base point `z` and index `m₁`, provided `z` sits in `(-1, 0)` — the restriction
`sigmaSBase_add_period` inherits from `doubleSine'_quasiperiod_tau`.

This is the period-direction counterpart of `sigmaS_add_one_sub_one`, and the missing half of
the shift-presentation question. Unlike the integer
direction it needs no nonvanishing hypothesis from the caller: `z ∈ (-1,0)` is already enough to
rule out the one bad factor `1 - e^{2πiz}`. -/
theorem sigmaS_add_period_sub_one (z τ : ℝ) (m₁ m₂ : ℤ) (hτ : 0 < τ) (hz : -1 < z) (hzu : z < 0) :
    sigmaS (z + τ) τ (m₁ - 1) m₂ = sigmaS z τ m₁ m₂ := by
  have hne : (1 : ℂ) - Complex.exp (2 * π * I * z) ≠ 0 := by
    refine one_sub_exp_two_pi_I_ne_zero_of_forall_ne_int z fun m hm => ?_
    rcases lt_trichotomy m 0 with hm0 | hm0 | hm0
    · have hm1 : m ≤ -1 := by omega
      have : (m : ℝ) ≤ -1 := by exact_mod_cast hm1
      rw [hm] at hz; linarith
    · rw [hm0] at hm; norm_num at hm; linarith
    · have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm0
      rw [hm] at hzu; linarith
  -- The first `qPochhammerFin` loses its leading factor `1 - e^{2πiz}`, which is exactly what
  -- `sigmaSBase_add_period` supplies.
  have hfirst : qPochhammerFin m₁ (z : ℂ) (τ : ℂ) =
      qPochhammerFin (m₁ - 1) (((z + τ : ℝ)) : ℂ) (τ : ℂ) * (1 - Complex.exp (2 * π * I * z)) := by
    have hkey := qPochhammerFin_add_one_sub_period (m₁ - 1) ((z : ℂ) + (τ : ℂ)) (τ : ℂ)
      (fun _ => by rw [show (z : ℂ) + (τ : ℂ) - (τ : ℂ) = (z : ℂ) from by ring]; exact hne)
    rw [show m₁ - 1 + 1 = m₁ from by ring,
      show (z : ℂ) + (τ : ℂ) - (τ : ℂ) = (z : ℂ) from by ring] at hkey
    rw [hkey, show (((z + τ : ℝ)) : ℂ) = (z : ℂ) + (τ : ℂ) from by push_cast; ring]
  unfold sigmaS
  rw [sigmaS_secondFactor_add_period z τ m₂ hτ.ne', hfirst, sigmaSBase_add_period z τ hτ hz hzu]
  ring

/-! ### Nonvanishing of the lattice factors

At a lattice point some factor `1 - e^{2πi(z+jτ)}` of `sigmaS`'s finite-product
bookkeeping vanishes. Since a negative-index `qPochhammerFin` is a reciprocal product,
two presentations of the same raw argument can disagree there. Thus lattice exclusion is a
mathematical hypothesis. It is the real-line form of the nonintegral-index condition `r ∉ ℤ²`
once the cocycle argument is written as `r₁τ-r₀` with irrational `τ`; it also controls the
extended double-sine walks. The shared predicate and its elementary operations live in
`SICs.Analysis.PeriodLattice`.
-/

/-- Every factor of a `q`-Pochhammer product in the *dual* variables `(w/ν, -1/ν)` is nonzero at a
lattice-free point: the `j`-th exponent is `(w - j)/ν`, which is an integer exactly when `w` sits
on the lattice `ℤν + ℤ`. -/
lemma one_sub_exp_dual_ne_zero {ν w : ℝ} (hν : 0 < ν) (hlat : SigmaSLatticeFree ν w)
    (j : ℤ) :
    (1 : ℂ) - Complex.exp (2 * π * I * ((w : ℂ) / (ν : ℂ) + (j : ℂ) * (-1 / (ν : ℂ)))) ≠ 0 := by
  have hν0 : ν ≠ 0 := hν.ne'
  have hνC : (ν : ℂ) ≠ 0 := by exact_mod_cast hν0
  have harg : (w : ℂ) / (ν : ℂ) + (j : ℂ) * (-1 / (ν : ℂ)) = (((w - j) / ν : ℝ) : ℂ) := by
    push_cast
    field_simp
    ring
  rw [harg]
  refine one_sub_exp_two_pi_I_ne_zero_of_forall_ne_int _ fun m hm => ?_
  refine hlat m j ?_
  field_simp at hm
  linarith

/-- **Every factor of a `q`-Pochhammer product at a lattice-free point is nonzero**: the `j`-th
exponent is `w + jν`, which is an integer exactly when `w` sits on `ℤν + ℤ`. Paired with
`SICs.SpecialFunctions.QPochhammer.Finite.qPochhammerFin_ne_zero_of_forall_factor_ne_zero` (and with
`qPochhammerFin_add`'s hypothesis, of the same shape), this is how an off-lattice index discharges
every nonvanishing side condition the shift calculus produces. -/
lemma SigmaSLatticeFree.one_sub_exp_ne_zero {ν w : ℝ} (hlat : SigmaSLatticeFree ν w) (j : ℤ) :
    (1 : ℂ) - Complex.exp (2 * π * I * ((w : ℂ) + (j : ℂ) * (ν : ℂ))) ≠ 0 := by
  have harg : (w : ℂ) + (j : ℂ) * (ν : ℂ) = ((w + (j : ℝ) * ν : ℝ) : ℂ) := by push_cast; ring
  rw [harg]
  refine one_sub_exp_two_pi_I_ne_zero_of_forall_ne_int _ fun m hm => ?_
  refine hlat (-j) m ?_
  push_cast
  linarith

end SIC

end
