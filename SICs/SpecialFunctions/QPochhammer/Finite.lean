/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.RingTheory.RootsOfUnity.Complex
import SICs.FieldTheory.ComplexGalois
import SICs.Source

/-!
# Finite q-Pochhammer products

Finite q-Pochhammer symbols: algebraic shifts, nonvanishing, and quadratic-period cancellation.

This file follows the finite symbol of [AFK25, Definition 1.14, `dfn:variantqPochhammer`].
Positive indices give finite products and negative indices their reciprocals. Splitting off
factors proves the index recurrences and addition laws; exponential periodicity gives integer
shift invariance. Nonvanishing hypotheses accompany identities that cancel reciprocal factors.
Reflection and paired period shifts then give the quadratic-period cancellation used by the
real Shintani--Faddeev word construction.

The infinite product and its bridge to finite symbols belong to
`SICs.SpecialFunctions.QPochhammer.Infinite`, independently of the real cocycle construction.
-/

noncomputable section

open Complex Real

namespace SIC

/-! ### Exponential and sine conversion

Euler's elementary identity connects the q-product factors to the double-sine shift laws. -/

/-- Euler's identity `1 - exp(2πix) = -2i exp(πix) sin(πx)` for complex `x`.
This common exponential–sine conversion supplies the generator shift laws and the
Shintani product period law. -/
lemma one_sub_exp_two_pi_I_eq (x : ℂ) :
    1 - Complex.exp (2 * π * I * x) =
      -2 * I * Complex.exp (π * I * x) * Complex.sin (π * x) := by
  rw [Complex.sin]
  rw [show (π * x) * I = π * I * x by ring,
    show -(π * x) * I = -(π * I * x) by ring]
  rw [show 2 * π * I * x = (π * I * x) + (π * I * x) by ring,
    Complex.exp_add, Complex.exp_neg]
  field_simp [Complex.exp_ne_zero]
  simp [I_sq]

/-- Euler's identity in the shifted form `1 - exp(2πix) = 2 exp(πix - πi/2) sin(πx)`, the
exponential change under `z ↦ z + 1` in the double-sine product and generator shift laws
(`one_sub_exp_two_pi_I_eq` with the factor `-i` written as `exp(-πi/2)`). -/
lemma one_sub_exp_two_pi_I_eq_two_exp_shift (x : ℂ) :
    1 - Complex.exp (2 * π * I * x) =
      2 * Complex.exp (π * I * x - π / 2 * I) * Complex.sin (π * x) := by
  rw [one_sub_exp_two_pi_I_eq]
  rw [show π * I * x - π / 2 * I = π * I * x + (-π / 2 * I) by ring,
    Complex.exp_add, Complex.exp_neg_pi_div_two_mul_I]
  ring

/-! ### Finite q-Pochhammer symbols

The finite symbol of [AFK25, Definition 1.14, `dfn:variantqPochhammer`] is defined for
every integer shift and carries the recurrences needed by the real shift calculus. -/

/-- The finite variant `q`-Pochhammer symbol:
      ϖ_n(z,τ) = ∏_{j=0}^{n-1} (1 - e^{2πi(z+jτ)})   for n > 0
                  1                                       for n = 0
      and its inverse-product for n < 0.
    Here q = e^{2πiτ} and the variable e^{2πiz} plays the role of the Pochhammer variable.
    See [AFK25, Definition 1.14, `dfn:variantqPochhammer`], equation (1.18). -/
@[source "AFK25, Definition 1.14, p. 9, dfn:variantqPochhammer (finite)" (symbol := "ϖ_n(z,τ)")]
noncomputable def qPochhammerFin (n : ℤ) (z τ : ℂ) : ℂ :=
  if n = 0 then 1
  else if 0 < n then
    ∏ j ∈ Finset.range n.toNat, (1 - Complex.exp (2 * π * I * (z + j * τ)))
  else
    (∏ j ∈ Finset.range (-n).toNat,
      (1 - Complex.exp (2 * π * I * (z + (n + (j : ℤ) : ℂ) * τ))))⁻¹

/-- The finite symbol `ϖ_n(z,τ)` is analytic in `z` wherever its value is nonzero.
For negative `n`, this excludes the poles of its inverse finite product. -/
lemma analyticAt_qPochhammerFin_of_ne_zero (n : ℤ) (z τ : ℂ)
    (h : qPochhammerFin n z τ ≠ 0) :
    AnalyticAt ℂ (fun w => qPochhammerFin n w τ) z := by
  unfold qPochhammerFin at h ⊢
  split_ifs at h ⊢ with hn hnpos
  · exact analyticAt_const
  · exact (by fun_prop : Differentiable ℂ (fun w =>
      ∏ j ∈ Finset.range n.toNat,
        (1 - Complex.exp (2 * π * I * (w + j * τ))))).analyticAt z
  · apply AnalyticAt.inv _ (by simpa only [ne_eq, inv_eq_zero] using h)
    exact (by fun_prop : Differentiable ℂ (fun w =>
      ∏ j ∈ Finset.range (-n).toNat,
        (1 - Complex.exp (2 * π * I * (w + (n + (j : ℤ) : ℂ) * τ))))).analyticAt z

/-- A nonintegral real point cannot give a zero factor in a finite `q`-Pochhammer product.
Public because `SICs.Cocycle.SigmaS.Reduction` needs the single-factor statement directly, to
discharge
`qPochhammerFin_add_one_sub_period`'s negative-index nonvanishing side condition from the
period-direction domain `z ∈ (-1,0)`. -/
lemma one_sub_exp_two_pi_I_ne_zero_of_forall_ne_int (x : ℝ)
    (hx : ∀ m : ℤ, x ≠ m) :
    1 - Complex.exp (2 * π * I * x) ≠ 0 := by
  rw [sub_ne_zero]
  intro heq
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp heq.symm
  apply hx m
  have hcast : (x : ℂ) = (m : ℂ) := by
    apply mul_right_cancel₀ Complex.two_pi_I_ne_zero
    calc
      (x : ℂ) * (2 * π * I) = 2 * π * I * x := by ring
      _ = (m : ℂ) * (2 * π * I) := hm
  exact_mod_cast hcast

/-- A nonreal point never gives a zero factor: `1 - e(z) ≠ 0` for `Im z ≠ 0`, since `e(z) = 1`
only at integers. -/
lemma one_sub_exp_two_pi_I_ne_zero_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    1 - Complex.exp (2 * π * I * z) ≠ 0 := by
  rw [sub_ne_zero]
  intro heq
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp heq.symm
  have hzint : z = (m : ℂ) := by
    apply mul_right_cancel₀ Complex.two_pi_I_ne_zero
    calc
      z * (2 * π * I) = 2 * π * I * z := by ring
      _ = (m : ℂ) * (2 * π * I) := hm
  exact hz (by simp [hzint])

/-- A finite `q`-Pochhammer product at real arguments is nonzero if every exponent occurring in
its positive- or negative-index product is nonintegral. The relevant indices are `0 ≤ k < n`
when `n > 0` and `n ≤ k < 0` when `n < 0`. -/
lemma qPochhammerFin_ne_zero_of_forall_ne_int (n : ℤ) (z τ : ℝ)
    (h : ∀ k : ℤ, ((0 ≤ k ∧ k < n) ∨ (n ≤ k ∧ k < 0)) →
      ∀ m : ℤ, z + k * τ ≠ m) :
    qPochhammerFin n z τ ≠ 0 := by
  unfold qPochhammerFin
  split_ifs with hn0 hnpos
  · exact one_ne_zero
  · refine Finset.prod_ne_zero_iff.mpr fun j hj => ?_
    have hj' : (j : ℤ) < n := by
      rw [← Int.toNat_of_nonneg hnpos.le]
      exact_mod_cast Finset.mem_range.mp hj
    have hne : ∀ m : ℤ, z + (j : ℝ) * τ ≠ m := by
      intro m hm
      exact h j (Or.inl ⟨by omega, hj'⟩) m (by exact_mod_cast hm)
    simpa only [ofReal_add, ofReal_mul, ofReal_natCast] using
      one_sub_exp_two_pi_I_ne_zero_of_forall_ne_int (z + (j : ℝ) * τ) hne
  · apply inv_ne_zero
    refine Finset.prod_ne_zero_iff.mpr fun j hj => ?_
    have hj' : (j : ℤ) < -n := by
      rw [← Int.toNat_of_nonneg (by omega : 0 ≤ -n)]
      exact_mod_cast Finset.mem_range.mp hj
    have hne : ∀ m : ℤ, z + ((n : ℝ) + (j : ℝ)) * τ ≠ m := by
      intro m hm
      exact h (n + j) (Or.inr ⟨by omega, by omega⟩) m (by exact_mod_cast hm)
    convert one_sub_exp_two_pi_I_ne_zero_of_forall_ne_int
      (z + ((n : ℝ) + (j : ℝ)) * τ) hne using 1
    push_cast
    ring

/-- **A `q`-Pochhammer product with no vanishing factor is nonzero**, over `ℂ` and for every
integer index at once. `qPochhammerFin_ne_zero_of_forall_ne_int` is the sharper real-argument
form, tracking exactly which indices occur; this one trades that sharpness for applicability to
compound `ℂ`-valued arguments, and takes its hypothesis in the same shape `qPochhammerFin_add`
does, so a caller discharges one condition for both. -/
lemma qPochhammerFin_ne_zero_of_forall_factor_ne_zero (n : ℤ) (z τ : ℂ)
    (h : ∀ j : ℤ, (1 : ℂ) - Complex.exp (2 * π * I * (z + (j : ℂ) * τ)) ≠ 0) :
    qPochhammerFin n z τ ≠ 0 := by
  unfold qPochhammerFin
  split_ifs with h0 hpos
  · exact one_ne_zero
  · refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
    have hj := h (j : ℤ)
    push_cast at hj ⊢
    exact hj
  · refine inv_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ => ?_)
    have hj := h (n + (j : ℤ))
    push_cast at hj ⊢
    exact hj

/-- A proper negative fraction `-q/d`, with `0 < q < d`, is not an integer. A small elementary
helper for discharging `qPochhammerFin_ne_zero_of_forall_ne_int`-style nonintegrality side
conditions. -/
lemma neg_intCast_div_natCast_ne_int (d : ℕ) (q m : ℤ)
    (hq0 : 0 < q) (hq1 : q < (d : ℤ)) :
    -(q : ℝ) / d ≠ m := by
  intro h
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show (0 : ℤ) < d from hq0.trans hq1)
  have hq0R : (0 : ℝ) < q := by exact_mod_cast hq0
  have hq1R : (q : ℝ) < d := by exact_mod_cast hq1
  have hmNeg : (m : ℝ) < 0 := h ▸ div_neg_of_neg_of_pos (by linarith) hdR
  have hmGt : (-1 : ℝ) < m := by
    rw [← h, neg_div, neg_lt]
    simpa only [neg_neg] using (div_lt_one hdR).2 hq1R
  have hmNegZ : m < 0 := by exact_mod_cast hmNeg
  have hmGtZ : (-1 : ℤ) < m := by exact_mod_cast hmGt
  omega

/-- The `q`-Pochhammer symbol at index `1`: the single factor at the argument itself. -/
lemma qPochhammerFin_one (z τ : ℂ) :
    qPochhammerFin 1 z τ = 1 - Complex.exp (2 * π * I * z) := by
  simp [qPochhammerFin]

/-- The `q`-Pochhammer symbol at index `-1`: a single reciprocal factor, at the argument shifted
back by one period. -/
lemma qPochhammerFin_neg_one (z τ : ℂ) :
    qPochhammerFin (-1) z τ = (1 - Complex.exp (2 * π * I * (z - τ)))⁻¹ := by
  rw [qPochhammerFin, ite_eq_right (by norm_num), ite_eq_right (by norm_num)]
  norm_num
  ring_nf

/-- `qPochhammerFin` at a natural-number index is the plain finite product, with no `if`-split:
this covers `k = 0` too, since the empty product is `1`, matching the `n = 0` branch. -/
lemma qPochhammerFin_natCast (k : ℕ) (z τ : ℂ) :
    qPochhammerFin (k : ℤ) z τ =
      ∏ j ∈ Finset.range k, (1 - Complex.exp (2 * π * I * (z + j * τ))) := by
  rcases eq_or_ne k 0 with hk0 | hk0
  · subst hk0; simp [qPochhammerFin]
  · simp only [qPochhammerFin, ite_eq_right (by exact_mod_cast hk0 : (k : ℤ) ≠ 0),
      ite_eq_left (by exact_mod_cast Nat.pos_of_ne_zero hk0 : (0 : ℤ) < (k : ℤ)), Int.toNat_natCast]

/-- **The finite `q`-Pochhammer symbol is jointly continuous where it does not vanish.** For
`n ≥ 0` it is a finite product of entire functions and the hypothesis is not needed; for `n < 0`
it is the reciprocal of such a product, continuous exactly where that product -- equivalently the
symbol itself -- is nonzero. Stated uniformly because the consumer following it along a boundary
limit (`SICs.Cocycle.ModularBoundary`) needs the nonvanishing in either case. -/
lemma continuousAt_qPochhammerFin (n : ℤ) {z τ : ℂ} (h : qPochhammerFin n z τ ≠ 0) :
    ContinuousAt (fun p : ℂ × ℂ => qPochhammerFin n p.1 p.2) (z, τ) := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp only [qPochhammerFin]
    exact continuousAt_const
  rcases lt_or_gt_of_ne hn0 with hneg | hpos
  · have hnlt : ¬ (0 : ℤ) < n := not_lt.mpr hneg.le
    have hcont : Continuous (fun p : ℂ × ℂ => ∏ j ∈ Finset.range (-n).toNat,
        (1 - Complex.exp (2 * π * I * (p.1 + (n + (j : ℤ) : ℂ) * p.2)))) :=
      continuous_finsetProd _ fun j _ => by fun_prop
    have hne : (∏ j ∈ Finset.range (-n).toNat,
        (1 - Complex.exp (2 * π * I * (z + (n + (j : ℤ) : ℂ) * τ)))) ≠ 0 := by
      intro hzero
      exact h (by rw [qPochhammerFin, ite_eq_right hn0, ite_eq_right hnlt, hzero, inv_zero])
    simp only [qPochhammerFin, ite_eq_right hn0, ite_eq_right hnlt]
    exact hcont.continuousAt.inv₀ hne
  · simp only [qPochhammerFin, ite_eq_right hn0, ite_eq_left hpos]
    exact (continuous_finsetProd _ fun j _ => by fun_prop).continuousAt

/-! ### Finite-product identities -/

/-- Shifting `qPochhammerFin`'s first argument by an integer changes nothing: each factor
`1 - e^{2πi(z+jτ)}` only sees `z` through `e^{2πiz}`, and `e^{2πi(z+k)} = e^{2πiz}`. Stated with
`z : ℂ` directly (rather than `z : ℝ` auto-cast) so it applies to compound `ℂ`-valued expressions
at call sites without needing them to match a single real-cast pattern. -/
lemma qPochhammerFin_add_intCast (n : ℤ) (z τ : ℂ) (k : ℤ) :
    qPochhammerFin n (z + k) τ = qPochhammerFin n z τ := by
  unfold qPochhammerFin
  split_ifs with h h
  · rfl
  · refine Finset.prod_congr rfl fun j _ => ?_
    congr 1
    exact exp_two_pi_I_eq_of_sub_intCast _ _ k (by ring)
  · congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    congr 1
    exact exp_two_pi_I_eq_of_sub_intCast _ _ k (by push_cast; ring)

/-- Shifting `qPochhammerFin`'s modulus `τ` by an integer changes nothing either: each factor's
exponent picks up `j` times an integer, still an integer. -/
lemma qPochhammerFin_tau_add_intCast (n : ℤ) (z τ : ℂ) (k : ℤ) :
    qPochhammerFin n z (τ + k) = qPochhammerFin n z τ := by
  unfold qPochhammerFin
  split_ifs with h h
  · rfl
  · refine Finset.prod_congr rfl fun j _ => ?_
    congr 1
    exact exp_two_pi_I_eq_of_sub_intCast _ _ ((j : ℤ) * k) (by push_cast; ring)
  · congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    congr 1
    exact exp_two_pi_I_eq_of_sub_intCast _ _ ((n + (j : ℤ)) * k) (by push_cast; ring)

/-- **Index recursion for `qPochhammerFin`.** Appending (or removing) one factor at index `n`
relates `ϖ_{n+1}(z,τ)` to `ϖ_n(z,τ)`. For `n ≥ 0` this is a pure product-extension identity
needing no hypothesis (`ϖ_{n+1}` literally has one more factor than `ϖ_n`); for `n < 0` the
crossed factor `1 - e^{2πi(z+nτ)}` must be nonzero, since `ϖ_n` for `n < 0` is a *reciprocal*
product and removing/adding a zero factor from a reciprocal does not distribute over
multiplication. This is the general shift-by-one-step recursion the independence-of-shift-choice
argument below runs on. -/
lemma qPochhammerFin_add_one (n : ℤ) (z τ : ℂ)
    (hne : n < 0 → (1 : ℂ) - Complex.exp (2 * π * I * (z + n * τ)) ≠ 0) :
    qPochhammerFin (n + 1) z τ =
      qPochhammerFin n z τ * (1 - Complex.exp (2 * π * I * (z + n * τ))) := by
  rcases lt_trichotomy n 0 with hn | hn | hn
  · have hfac := hne hn
    rcases eq_or_lt_of_le (by omega : n + 1 ≤ 0) with hn1 | hn1
    · -- n = -1, n + 1 = 0
      have hn' : n = -1 := by omega
      subst hn'
      simp only [qPochhammerFin]
      rw [ite_eq_right (by norm_num : (-1 : ℤ) ≠ 0), ite_eq_right (by norm_num : ¬ (0 : ℤ) < -1)]
      norm_num
      rw [inv_mul_cancel₀]
      simpa using hfac
    · -- n ≤ -2, n + 1 < 0
      have hn1' : n + 1 < 0 := hn1
      unfold qPochhammerFin
      rw [ite_eq_right hn.ne, ite_eq_right (not_lt.mpr hn.le),
          ite_eq_right hn1'.ne, ite_eq_right (not_lt.mpr hn1'.le)]
      have hcast : (-(n + 1)).toNat + 1 = (-n).toNat := by omega
      rw [← hcast, Finset.prod_range_succ']
      push_cast
      have hprod_eq :
          (∏ x ∈ Finset.range (-(n + 1)).toNat,
              (1 - cexp (2 * (π : ℂ) * I * (z + (↑n + 1 + ↑x) * τ))))
          = ∏ x ∈ Finset.range (-(n + 1)).toNat,
              (1 - cexp (2 * (π : ℂ) * I * (z + (↑n + (↑x + 1)) * τ))) := by
        refine Finset.prod_congr rfl fun x _ => ?_
        ring_nf
      rw [← hprod_eq]
      have h0 : (1 : ℂ) - cexp (2 * (π : ℂ) * I * (z + (↑n + 0) * τ)) =
          1 - cexp (2 * (π : ℂ) * I * (z + ↑n * τ)) := by ring_nf
      rw [h0, mul_inv, inv_mul_cancel_right₀ hfac]
  · subst hn
    simp [qPochhammerFin]
  · -- n > 0, so n + 1 > 0 too
    have hn1 : (0 : ℤ) < n + 1 := by omega
    unfold qPochhammerFin
    rw [ite_eq_right hn.ne', ite_eq_left hn, ite_eq_right hn1.ne', ite_eq_left hn1]
    have hcast : (n + 1).toNat = n.toNat + 1 := by omega
    rw [hcast, Finset.prod_range_succ]
    have hcast2 : ((n.toNat : ℕ) : ℂ) = (n : ℂ) := by
      exact_mod_cast Int.toNat_of_nonneg hn.le
    rw [hcast2]

/-- **Index additivity for `qPochhammerFin`**: `ϖ_{p+q}(z,τ) = ϖ_p(z,τ)·ϖ_q(z+pτ,τ)`, the finite
analogue of `(x;q)_{p+q} = (x;q)_p·(xq^p;q)_q`. Proved from `qPochhammerFin_add_one` by induction
on `q` over `ℤ`, in both directions.

The blanket nonvanishing hypothesis is not decoration: at a negative index `qPochhammerFin` is a
*reciprocal* product, and one vanishing factor makes the identity false rather than merely unproved
(at `p = 1`, `q = -1`, `z = 0` the left side is `ϖ_0 = 1` and the right side is `0·(1-e(0))⁻¹ = 0`).
Callers discharge it from `SigmaSLatticeFree` in `SICs.Cocycle.SigmaS.Reduction`; in modular-cocycle
applications that off-lattice condition follows from the nonintegral-index hypothesis `r ∉ ℤ²`. -/
lemma qPochhammerFin_add (p q : ℤ) (z τ : ℂ)
    (hne : ∀ j : ℤ, (1 : ℂ) - Complex.exp (2 * π * I * (z + (j : ℂ) * τ)) ≠ 0) :
    qPochhammerFin (p + q) z τ =
      qPochhammerFin p z τ * qPochhammerFin q (z + (p : ℂ) * τ) τ := by
  set f : ℤ → ℂ := fun j => 1 - Complex.exp (2 * π * I * (z + (j : ℂ) * τ)) with hf
  have key : ∀ n : ℤ, qPochhammerFin (n + 1) z τ = qPochhammerFin n z τ * f n :=
    fun n => qPochhammerFin_add_one n z τ (fun _ => hne n)
  have harg : ∀ n : ℤ, (z + (p : ℂ) * τ) + (n : ℂ) * τ = z + ((p + n : ℤ) : ℂ) * τ := by
    intro n; push_cast; ring
  have key' : ∀ n : ℤ, qPochhammerFin (n + 1) (z + (p : ℂ) * τ) τ =
      qPochhammerFin n (z + (p : ℂ) * τ) τ * f (p + n) := by
    intro n
    rw [qPochhammerFin_add_one n (z + (p : ℂ) * τ) τ (fun _ => by rw [harg n]; exact hne (p + n)),
      hf]
    simp only [harg n]
  induction q using Int.induction_on with
  | zero => simp [qPochhammerFin]
  | succ k ih =>
      rw [show p + ((k : ℤ) + 1) = (p + (k : ℤ)) + 1 by ring, key, ih, key' (k : ℤ), ← mul_assoc]
  | pred k ih =>
      have hstep : qPochhammerFin (p + (-(k : ℤ) - 1) + 1) z τ =
          qPochhammerFin (p + (-(k : ℤ) - 1)) z τ * f (p + (-(k : ℤ) - 1)) := key _
      have hstep' : qPochhammerFin ((-(k : ℤ) - 1) + 1) (z + (p : ℂ) * τ) τ =
          qPochhammerFin (-(k : ℤ) - 1) (z + (p : ℂ) * τ) τ * f (p + (-(k : ℤ) - 1)) :=
        key' _
      rw [show p + (-(k : ℤ) - 1) + 1 = p + -(k : ℤ) by ring] at hstep
      rw [show (-(k : ℤ) - 1) + 1 = -(k : ℤ) by ring] at hstep'
      refine mul_right_cancel₀ (hne (p + (-(k : ℤ) - 1))) ?_
      rw [← hstep, ih, hstep', ← mul_assoc]

/-- **The reflection identity for `qPochhammerFin`**: negating both the index and the argument
gives back the same product up to an explicit root-of-unity factor and the two end terms,

```text
ϖ_n(x,ν)·ϖ_{-n}(-x,ν)·(1 - e(x + nν)) = (-1)^n e(nx + n(n+1)ν/2)·(1 - e(x)),
```

writing `e(y) = e^{2πiy}`. It is the `q`-Pochhammer half of the reciprocity identity
[AFK25, Theorem 5.8, `thm:nupnumpeq1`], where it pairs the correction factors of `ש^r_M` and
`ש^{-r}_M`; `SICs.Cocycle.Word.Reflection.wordSigmaS_mul_neg` supplies the other half.

The mechanism is that the two products run through the same points in opposite directions:
`1 - e(-y) = -e(-y)(1 - e(y))` turns each factor of the reflected product into a factor of the
original, and the accumulated `e(-y)` factors telescope into the stated exponent, leaving the
two ends `1 - e(x)` and `1 - e(x + nν)` unmatched.

Stated multiplicatively, so the identity holds with no division; the blanket nonvanishing
hypothesis is the same one `qPochhammerFin_add` carries, and for the same reason -- at a negative
index `qPochhammerFin` is a reciprocal product. Callers discharge it from `SigmaSLatticeFree` in
`SICs.Cocycle.SigmaS.Reduction`. -/
lemma qPochhammerFin_mul_neg_reflect (n : ℤ) (x ν : ℂ)
    (hne : ∀ j : ℤ, (1 : ℂ) - Complex.exp (2 * π * I * (x + (j : ℂ) * ν)) ≠ 0) :
    qPochhammerFin n x ν * qPochhammerFin (-n) (-x) ν *
        (1 - Complex.exp (2 * π * I * (x + (n : ℂ) * ν))) =
      (-1 : ℂ) ^ n *
        Complex.exp (2 * π * I * ((n : ℂ) * x + (n : ℂ) * ((n : ℂ) + 1) / 2 * ν)) *
        (1 - Complex.exp (2 * π * I * x)) := by
  -- `f k` is the `k`-th factor of the unreflected product, `G k` the reflected product's factor
  -- that crosses it, and `E k` the exponential converting one into the other.
  set f : ℤ → ℂ := fun k => 1 - Complex.exp (2 * π * I * (x + (k : ℂ) * ν)) with hf
  set G : ℤ → ℂ :=
    fun k => 1 - Complex.exp (2 * π * I * (-x + ((-(k + 1) : ℤ) : ℂ) * ν)) with hG
  set E : ℤ → ℂ := fun k => Complex.exp (2 * π * I * (x + ((k + 1 : ℤ) : ℂ) * ν)) with hE
  set L : ℤ → ℂ := fun k => qPochhammerFin k x ν * qPochhammerFin (-k) (-x) ν * f k with hL
  set R : ℤ → ℂ := fun k => (-1 : ℂ) ^ k *
    Complex.exp (2 * π * I * ((k : ℂ) * x + (k : ℂ) * ((k : ℂ) + 1) / 2 * ν)) * f 0 with hR
  have hE0 : ∀ k : ℤ, E k ≠ 0 := fun _ => Complex.exp_ne_zero _
  -- `1 - e(-y) = -e(-y)(1 - e(y))`: each crossed factor is the unreflected one, scaled.
  have hrefl : ∀ k : ℤ, E k * G k = -f (k + 1) := by
    intro k
    simp only [hE, hG, hf]
    rw [show (2 : ℂ) * π * I * (-x + ((-(k + 1) : ℤ) : ℂ) * ν) =
          -(2 * π * I * (x + ((k + 1 : ℤ) : ℂ) * ν)) from by push_cast; ring, Complex.exp_neg]
    field_simp
    ring
  have hGne : ∀ k : ℤ, G k ≠ 0 := by
    intro k h0
    have h := hrefl k
    rw [h0, mul_zero, eq_comm, neg_eq_zero] at h
    exact hne (k + 1) (by simpa [hf] using h)
  -- The one-step relation, valid in both index directions.
  have hstep : ∀ k : ℤ, L (k + 1) = -(E k) * L k := by
    intro k
    have hA : qPochhammerFin (k + 1) x ν = qPochhammerFin k x ν * f k :=
      qPochhammerFin_add_one k x ν (fun _ => hne k)
    have hB : qPochhammerFin (-k) (-x) ν = qPochhammerFin (-(k + 1)) (-x) ν * G k := by
      have h := qPochhammerFin_add_one (-(k + 1)) (-x) ν (fun _ => hGne k)
      rwa [show -(k + 1) + 1 = -k from by ring] at h
    have hr := hrefl k
    simp only [hL, hE, hG, hf] at hr ⊢
    rw [hA, hB]
    simp only [hG, hf] at hr ⊢
    linear_combination
      (qPochhammerFin k x ν * qPochhammerFin (-(k + 1)) (-x) ν *
        (1 - Complex.exp (2 * π * I * (x + (k : ℂ) * ν)))) * hr
  -- The right-hand side satisfies the same relation.
  have hstepR : ∀ k : ℤ, R (k + 1) = -(E k) * R k := by
    intro k
    simp only [hR, hE]
    rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_one,
      show (2 : ℂ) * π * I *
            (((k + 1 : ℤ) : ℂ) * x + ((k + 1 : ℤ) : ℂ) * (((k + 1 : ℤ) : ℂ) + 1) / 2 * ν) =
          2 * π * I * ((k : ℂ) * x + (k : ℂ) * ((k : ℂ) + 1) / 2 * ν) +
            2 * π * I * (x + ((k + 1 : ℤ) : ℂ) * ν) from by push_cast; ring,
      Complex.exp_add]
    ring
  have hiff : ∀ k : ℤ, L k = R k ↔ L (k + 1) = R (k + 1) := by
    intro k
    rw [hstep k, hstepR k]
    exact ⟨fun h => by rw [h], fun h => mul_left_cancel₀ (neg_ne_zero.mpr (hE0 k)) h⟩
  have hzero : L 0 = R 0 := by simp [hL, hR, qPochhammerFin]
  have hmain : ∀ k : ℤ, L k = R k := by
    intro k
    induction k using Int.induction_on with
    | zero => exact hzero
    | succ i ih => exact (hiff i).mp ih
    | pred i ih =>
        refine (hiff (-(i : ℤ) - 1)).mpr ?_
        rwa [show -(i : ℤ) - 1 + 1 = -(i : ℤ) from by ring]
  simpa [hL, hR, hf] using hmain n

/-- **Combined index/period-shift recursion for `qPochhammerFin`.** Shifting the argument
back by one period `τ` while advancing the index by one: `ϖ_{k+1}(v-τ,τ) = ϖ_k(v,τ)·(1-e(v-τ))`.
Structurally parallel to `qPochhammerFin_add_one` (same case split on the sign of `k`, same
nonvanishing requirement for `k < 0`), but genuinely different: unlike `qPochhammerFin_add_one`,
both the index *and* the base point move. This is the second ingredient (besides
`qPochhammerFin_add_one`) needed for `sigmaS`'s single-step shift-invariance identity. -/
lemma qPochhammerFin_add_one_sub_period (k : ℤ) (v τ : ℂ)
    (hne : k < 0 → (1 : ℂ) - Complex.exp (2 * π * I * (v - τ)) ≠ 0) :
    qPochhammerFin (k + 1) (v - τ) τ =
      qPochhammerFin k v τ * (1 - Complex.exp (2 * π * I * (v - τ))) := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · have hfac := hne hk
    rcases eq_or_lt_of_le (by omega : k + 1 ≤ 0) with hk1 | hk1
    · -- k = -1, k + 1 = 0
      have hk' : k = -1 := by omega
      subst hk'
      simp only [qPochhammerFin]
      rw [ite_eq_right (by norm_num : (-1 : ℤ) ≠ 0), ite_eq_right (by norm_num : ¬ (0 : ℤ) < -1)]
      norm_num
      rw [show v + -τ = v - τ from by ring, inv_mul_cancel₀ hfac]
    · -- k ≤ -2, k + 1 < 0. The crossed factor `1 - e(v-τ)` is the *last* term
      -- (index `j = -k-1`) of `qPochhammerFin k v τ`'s own product.
      have hk1' : k + 1 < 0 := hk1
      unfold qPochhammerFin
      rw [ite_eq_right hk.ne, ite_eq_right (not_lt.mpr hk.le),
          ite_eq_right hk1'.ne, ite_eq_right (not_lt.mpr hk1'.le)]
      have hcast : (-k).toNat = (-(k + 1)).toNat + 1 := by omega
      rw [hcast, Finset.prod_range_succ]
      push_cast
      have hlast : (1 : ℂ) - cexp (2 * (π : ℂ) * I * (v + (↑k + (-(k + 1)).toNat) * τ)) =
          1 - cexp (2 * (π : ℂ) * I * (v - τ)) := by
        have hnn : (0 : ℤ) ≤ -(k + 1) := by omega
        have heq : ((-(k + 1)).toNat : ℂ) = -((k : ℂ) + 1) := by
          exact_mod_cast Int.toNat_of_nonneg hnn
        rw [heq]; ring_nf
      rw [hlast]
      have hprod_eq :
          (∏ x ∈ Finset.range (-(k + 1)).toNat,
              (1 - cexp (2 * (π : ℂ) * I * (v + (↑k + ↑x) * τ))))
          = ∏ x ∈ Finset.range (-(k + 1)).toNat,
              (1 - cexp (2 * (π : ℂ) * I * (v - τ + (↑k + 1 + ↑x) * τ))) := by
        refine Finset.prod_congr rfl fun x _ => ?_
        ring_nf
      rw [hprod_eq, mul_inv, inv_mul_cancel_right₀ hfac]
  · subst hk
    simp [qPochhammerFin]
  · -- k > 0, so k + 1 > 0 too. The crossed factor `1 - e(v-τ)` is the *first* term
    -- (index `j = 0`) of `qPochhammerFin (k+1) (v-τ) τ`'s own product.
    have hk1 : (0 : ℤ) < k + 1 := by omega
    unfold qPochhammerFin
    rw [ite_eq_right hk1.ne', ite_eq_left hk1, ite_eq_right hk.ne', ite_eq_left hk]
    have hcast : (k + 1).toNat = k.toNat + 1 := by omega
    rw [hcast, Finset.prod_range_succ']
    push_cast
    have hfirst : (1 : ℂ) - cexp (2 * (π : ℂ) * I * (v - τ + 0 * τ)) =
        1 - cexp (2 * (π : ℂ) * I * (v - τ)) := by ring_nf
    rw [hfirst]
    congr 1
    refine Finset.prod_congr rfl fun x _ => ?_
    ring_nf


/-! ### Quadratic-period cancellation -/

/-- **The elementary self-cancelling shift identity.** For any real `v`, integer `n`, and `τ`
satisfying `τ + 1/τ = m` for an integer `m` (as `ρ_d` does): `ϖ_n(v,τ) · ϖ_{-n}(v-n/τ,τ) = 1`,
provided `ϖ_n(v,τ) ≠ 0`. Structurally the finite-product analogue of
[72, Kopp (2024), Lemma 2.3, `lem:ell`] (the same telescoping mechanism `sigmaS` itself uses,
applied here to a *second*, self-referential shift rather
than to `σ_S`'s argument). -/
lemma qPochhammerFin_mul_neg_div_eq_one (v τ : ℝ) (m n : ℤ) (hτ : τ ≠ 0)
    (hm : τ + τ⁻¹ = (m : ℝ)) (hne : qPochhammerFin n v τ ≠ 0) :
    qPochhammerFin n v τ * qPochhammerFin (-n) (v - n / τ) τ = 1 := by
  have hmC : (τ : ℂ) + (τ : ℂ)⁻¹ = (m : ℂ) := by exact_mod_cast hm
  have hτC : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ
  have hmC2 : (τ : ℂ) * τ + 1 = τ * (m : ℂ) := by
    linear_combination τ * hmC - mul_inv_cancel₀ hτC
  -- The core identity is a pure algebraic fact about the two finite products, with no
  -- nonvanishing hypothesis needed: it holds even when both sides are `0`.
  have hcore : ∀ (n' : ℤ) (v' : ℝ), 0 < n' →
      qPochhammerFin (-n') (v' - n' / τ) τ = (qPochhammerFin n' v' τ)⁻¹ := by
    intro n' v' hn'
    have hn0 : n' ≠ 0 := hn'.ne'
    have hnn0 : -n' ≠ 0 := by omega
    have hnnotpos : ¬ (0 < -n') := by omega
    unfold qPochhammerFin
    rw [ite_eq_right hnn0, ite_eq_right hnnotpos, ite_eq_right hn0, ite_eq_left hn', neg_neg]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    congr 1
    apply exp_two_pi_I_eq_of_sub_intCast _ _ (-(n' * m))
    push_cast
    field_simp
    linear_combination -(n' : ℂ) * hmC2
  rcases lt_trichotomy n 0 with hn | hn | hn
  · have hn' : 0 < -n := by omega
    have heqn := hcore (-n) (v - n / τ) hn'
    have hsimp : ((v - (n : ℝ) / τ : ℝ) : ℂ) - ((-n : ℤ) : ℂ) / (τ : ℂ) = (v : ℂ) := by
      push_cast; ring
    rw [hsimp, neg_neg] at heqn
    push_cast at heqn
    have hbne : qPochhammerFin (-n) (v - n / τ) τ ≠ 0 := by
      intro hb0
      exact hne (by rw [heqn, hb0, inv_zero])
    rw [heqn]
    exact inv_mul_cancel₀ hbne
  · subst hn
    simp [qPochhammerFin]
  · rw [hcore n v hn]
    exact mul_inv_cancel₀ hne



end SIC

end
