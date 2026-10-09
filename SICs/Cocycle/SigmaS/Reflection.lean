/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Cocycle.SigmaS.Reduction

/-!
# Reflection of the canonical sigma-S value

The global reflection formula for the canonical sigma-S value.

The base reflection identity from [AFK25, equation (8.6),
`eq:SFJacobiCocycleTermsDoubleSine`] first gives the product at reflected chamber points.
The shift law in equation (8.9) propagates this identity along the integer orbit of
ceiling reduction. The result is a closed reflection formula at every off-lattice argument,
which supplies the reflection of the word cocycle.
-/

noncomputable section

open Complex Real

namespace SIC

/-! ### The reflection law for `sigmaSHonest`

`sigmaSBase_mul_reflect` reflects the *base point*, `z ↦ ν - 1 - z`,
because that is what the double sine's own reflection `S₂(ν+1-u)·S₂(u) = 1` does at `u = z + 1`. The
argument reflection the Shintani--Faddeev cocycle needs is `w ↦ -w`, and the two differ by the
lattice vector `ν - 1`:

```text
-w = (ν - 1 - z) + (-1 - m₁)·ν + (1 - m₂)      whenever   w = z + m₁ν + m₂.
```

So a base point for `w` supplies one for `-w` for free -- the reflected point stays in `(-1, ν)`
and stays lattice-free -- and `sigmaSHonest_eq_sigmaS` evaluates both sides at it. The two double
sines then cancel outright, leaving only `q`-Pochhammer factors and the (reflection-invariant)
exponential prefactor.

This is the per-factor input to a reflection law for `SICs.Cocycle.Word.Basic.wordSigmaS`, and hence
to
[72, Kopp (2024), Theorem 4.36, `thm:shincharacter`] and [AFK25, Theorem 2.11, `thm:funchar`] on the
real line: those compare `ש^r_A` with `ש^{-r}_A` at the *same* matrix, so both sides walk the same
word and it is exactly this identity that has to be applied at each step. -/

/-- **`σ_S` at reflected arguments**, with no double sine left:

```text
σ_S(w,ν)·σ_S(-w,ν) = ϖ_{m₁}(z,ν)/ϖ_{-m₂}(z/ν,-1/ν) ·
                     ϖ_{-1-m₁}(z',ν)/ϖ_{m₂-1}(z'/ν,-1/ν) · exp(2·X(z,ν)),
```

where `z` is any base point for `w` in `sigmaSBase`'s domain, off the lattice, and
`z' = ν - 1 - z` is its reflection. The hypotheses are `sigmaSHonest_eq_sigmaS`'s, imposed on `z`
alone: the reflected point inherits them. -/
theorem sigmaSHonest_mul_neg (w z ν : ℝ) (m₁ m₂ : ℤ) (hν : 0 < ν)
    (hz : -1 < z) (hzu : z < ν) (hlat : SigmaSLatticeFree ν z)
    (heq : z + m₁ * ν + m₂ = w) :
    sigmaSHonest w ν * sigmaSHonest (-w) ν =
      qPochhammerFin m₁ (z : ℂ) (ν : ℂ) /
          qPochhammerFin (-m₂) ((z : ℂ) / (ν : ℂ)) (-1 / (ν : ℂ)) *
        (qPochhammerFin (-1 - m₁) ((ν - 1 - z : ℝ) : ℂ) (ν : ℂ) /
          qPochhammerFin (m₂ - 1) (((ν - 1 - z : ℝ) : ℂ) / (ν : ℂ)) (-1 / (ν : ℂ))) *
        Complex.exp (2 * sfExpArg z ν) := by
  have harg : -z + (1 : ℤ) * ν + ((-1 : ℤ) : ℝ) = ν - 1 - z := by push_cast; ring
  have hlat' : SigmaSLatticeFree ν (ν - 1 - z) := harg ▸ hlat.neg.add 1 (-1)
  have heq' : (ν - 1 - z) + ((-1 - m₁ : ℤ) : ℝ) * ν + ((1 - m₂ : ℤ) : ℝ) = -w := by
    push_cast
    linarith
  have h1 : sigmaSHonest w ν = sigmaS z ν m₁ m₂ :=
    sigmaSHonest_eq_sigmaS w z ν m₁ m₂ hν hz hzu hlat heq
  have h2 : sigmaSHonest (-w) ν = sigmaS (ν - 1 - z) ν (-1 - m₁) (1 - m₂) :=
    sigmaSHonest_eq_sigmaS _ _ ν _ _ hν (by linarith) (by linarith) hlat' heq'
  rw [h1, h2, sigmaS, sigmaS, show (-(1 - m₂) : ℤ) = m₂ - 1 from by ring, mul_mul_mul_comm,
    sigmaSBase_mul_reflect]

/-- **The reflection law in closed form.** For a base point `w` already inside `sigmaSBase`'s
domain and off the lattice, `sigmaSHonest_mul_neg`'s two trivial `q`-Pochhammer factors disappear
and the other two collapse to a single ratio of elementary exponentials:

```text
σ_S(w,ν)·σ_S(-w,ν) = (1 - e^{-2πi·w/ν}) / (1 - e^{-2πi·w}) · exp(2·X(w,ν)).
```

The shape matches the ratio of sine-like differences in [72, Kopp (2024), Theorem 4.32,
`thm:funchar`]; it gives the contribution of one generator to that identity. Both
`e^{2πi(ν-1-w-ν)} = e^{-2πi w}` and `e^{2πi((ν-w)/ν)} = e^{-2πi·w/ν}` use only `e^{2πi} = 1`.

This is the base case of `sigmaSHonest_mul_neg_closed`, the same identity with the membership
hypotheses `-1 < w`, `w < ν` removed; callers want that one. -/
theorem sigmaSHonest_mul_neg_of_mem (w ν : ℝ) (hν : 0 < ν) (hw : -1 < w) (hwu : w < ν)
    (hlat : SigmaSLatticeFree ν w) :
    sigmaSHonest w ν * sigmaSHonest (-w) ν =
      (1 - Complex.exp (-(2 * π * I * (w / ν)))) / (1 - Complex.exp (-(2 * π * I * w))) *
        Complex.exp (2 * sfExpArg w ν) := by
  have hν0 : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
  have hmain := sigmaSHonest_mul_neg w w ν 0 0 hν hw hwu hlat (by push_cast; ring)
  rw [hmain, show ((-1 : ℤ) - 0) = -1 from by ring, show ((0 : ℤ) - 1) = -1 from by ring,
    show (-(0 : ℤ)) = 0 from by ring, qPochhammerFin_neg_one, qPochhammerFin_neg_one]
  have h1 : ((ν - 1 - w : ℝ) : ℂ) - (ν : ℂ) = -1 - (w : ℂ) := by push_cast; ring
  have h2 : ((ν - 1 - w : ℝ) : ℂ) / (ν : ℂ) - (-1 / (ν : ℂ)) = 1 - (w : ℂ) / (ν : ℂ) := by
    push_cast
    field_simp
    ring
  have hexp1 : Complex.exp (2 * π * I * (-1 - (w : ℂ))) = Complex.exp (-(2 * π * I * w)) := by
    rw [show (2 * (π : ℂ) * I * (-1 - (w : ℂ))) = (-1 : ℤ) * (2 * π * I) + -(2 * π * I * w) by
      push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]
  have hexp2 : Complex.exp (2 * π * I * (1 - (w : ℂ) / (ν : ℂ))) =
      Complex.exp (-(2 * π * I * (w / ν))) := by
    rw [show (2 * (π : ℂ) * I * (1 - (w : ℂ) / (ν : ℂ))) =
      (1 : ℤ) * (2 * π * I) + -(2 * π * I * ((w : ℂ) / (ν : ℂ))) by push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]
  rw [h1, h2, hexp1, hexp2, qPochhammerFin, ite_eq_left rfl, qPochhammerFin, ite_eq_left rfl]
  field_simp

/-! ### From base points to an arbitrary argument

`sigmaSHonest_mul_neg_of_mem` states the closed form only where `w` is itself a base point, but
the successive arguments `z/j_N(τ)` of a word walk are not base points, so the word-level
reflection law needs the identity at an arbitrary `w`. Both sides satisfy the *same* recurrence
under `w ↦ w + 1`, and that is all the extension costs.

On the left, `sigmaSHonest_lattice_shift` at `(m₁, m₂) = (0, 1)` and, at the reflected argument,
at `(0, -1)` give

```text
σ_S(w+1,ν) = σ_S(w,ν)·(1 - e^{2πi(w+1)/ν}),    σ_S(-w,ν) = σ_S(-(w+1),ν)·(1 - e^{-2πiw/ν}),
```

so the product `σ_S(w,ν)·σ_S(-w,ν)` is multiplied by `(1 - e^{2πi(w+1)/ν})/(1 - e^{-2πiw/ν})`.
The right-hand side picks up the same factor for an elementary reason: `e^{-2πiw}` is
`1`-periodic, so its denominator does not move at all, and the quadratic exponent contributes

```text
2·(X(w+1,ν) - X(w,ν)) = 2πi(w+1)/ν - πi,
```

whose `e^{-πi} = -1` turns the shifted numerator `1 - e^{-2πi(w+1)/ν}` into `1 - e^{2πi(w+1)/ν}`
against the `e^{2πi(w+1)/ν}` beside it. Every real argument reaches the base domain `(-1, ν)` in
finitely many unit steps (`sfShift`), so an induction over `ℤ` carries the closed form to every
off-lattice `w`.

Note that no irrationality of `w` or `ν` enters: the off-lattice hypothesis is the whole of it. -/

/-- The closed form of the reflection law, as a function of the raw argument. Private: it names
the common right-hand side of `sigmaSHonest_mul_neg_of_mem` and `sigmaSHonest_mul_neg_closed`
only so that the induction carrying the first to the second can state its recurrence
(`reflectValue_add_one`). -/
private noncomputable def reflectValue (w ν : ℝ) : ℂ :=
  (1 - Complex.exp (-(2 * π * I * (w / ν)))) / (1 - Complex.exp (-(2 * π * I * w))) *
    Complex.exp (2 * sfExpArg w ν)

/-- The same unit step at the reflected argument, in the direction the reflection law consumes:
`σ_S(-(w+1),ν)·(1 - e^{-2πiw/ν}) = σ_S(-w,ν)`. Helper for `sigmaSHonest_mul_neg_closed`. -/
private lemma sigmaSHonest_neg_add_one (w ν : ℝ) (hν : 0 < ν) (hlat : SigmaSLatticeFree ν w) :
    sigmaSHonest (-(w + 1)) ν * (1 - Complex.exp (-(2 * π * I * (w / ν)))) =
      sigmaSHonest (-w) ν := by
  have h := sigmaSHonest_lattice_shift (-w) ν 0 (-1) hν hlat.neg
  rw [show -w + ((0 : ℤ) : ℝ) * ν + ((-1 : ℤ) : ℝ) = -(w + 1) by push_cast; ring,
    show (-(-1 : ℤ)) = 1 from rfl, qPochhammerFin_one,
    show qPochhammerFin (0 : ℤ) ((-w : ℝ) : ℂ) (ν : ℂ) = 1 by simp [qPochhammerFin], mul_one,
    show 2 * (π : ℂ) * I * (((-w : ℝ) : ℂ) / (ν : ℂ)) = -(2 * π * I * ((w : ℂ) / (ν : ℂ))) by
      push_cast; ring] at h
  exact h

/-- The closed form obeys the same unit-step recurrence as `σ_S(w,ν)·σ_S(-w,ν)`. Stated
multiplicatively, so that neither factor has to be inverted here. Helper for
`sigmaSHonest_mul_neg_closed`. -/
private lemma reflectValue_add_one (w ν : ℝ) (hν : 0 < ν) :
    reflectValue (w + 1) ν * (1 - Complex.exp (-(2 * π * I * (w / ν)))) =
      reflectValue w ν * (1 - Complex.exp (2 * π * I * ((w + 1) / ν))) := by
  have hνC : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
  -- The denominator `1 - e^{-2πiw}` is `1`-periodic, so it does not move.
  have hper : Complex.exp (-(2 * π * I * ((w : ℂ) + 1))) =
      Complex.exp (-(2 * π * I * (w : ℂ))) := by
    rw [show -(2 * (π : ℂ) * I * ((w : ℂ) + 1)) =
      (-1 : ℤ) * (2 * π * I) + -(2 * π * I * (w : ℂ)) by push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]
  -- The quadratic exponent contributes `2πi(w+1)/ν - πi`, and `e^{-πi} = -1`.
  have hquad : Complex.exp (2 * sfExpArg (w + 1) ν) =
      -(Complex.exp (2 * sfExpArg w ν) * Complex.exp (2 * π * I * (((w : ℂ) + 1) / (ν : ℂ)))) := by
    rw [show 2 * sfExpArg (w + 1) ν =
      2 * sfExpArg w ν + 2 * π * I * (((w : ℂ) + 1) / (ν : ℂ)) + -(π * I) by
        unfold sfExpArg faddeevSExpArg; push_cast; field_simp; ring]
    simp [Complex.exp_add, Complex.exp_neg, Complex.exp_pi_mul_I]
  have hE : Complex.exp (-(2 * π * I * (((w : ℂ) + 1) / (ν : ℂ)))) =
      (Complex.exp (2 * π * I * (((w : ℂ) + 1) / (ν : ℂ))))⁻¹ := Complex.exp_neg _
  have hEne : Complex.exp (2 * π * I * (((w : ℂ) + 1) / (ν : ℂ))) ≠ 0 := Complex.exp_ne_zero _
  unfold reflectValue
  rw [show ((w + 1 : ℝ) : ℂ) = (w : ℂ) + 1 by push_cast; ring, hper, hquad, hE]
  field_simp
  ring

/-- The reflection law's unit step: the closed form holds at `w + 1` exactly when it holds at
`w`. Both directions are needed, since the induction reaching an arbitrary argument from a base
point runs both ways. Helper for `sigmaSHonest_mul_neg_closed`. -/
private lemma sigmaSHonest_mul_neg_add_one_iff (w ν : ℝ) (hν : 0 < ν)
    (hlat : SigmaSLatticeFree ν w) :
    (sigmaSHonest (w + 1) ν * sigmaSHonest (-(w + 1)) ν = reflectValue (w + 1) ν) ↔
      sigmaSHonest w ν * sigmaSHonest (-w) ν = reflectValue w ν := by
  have hνC : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
  have ha : (1 : ℂ) - Complex.exp (-(2 * π * I * ((w : ℂ) / (ν : ℂ)))) ≠ 0 := by
    have h := one_sub_exp_dual_ne_zero hν hlat 0
    rw [show (w : ℂ) / (ν : ℂ) + ((0 : ℤ) : ℂ) * (-1 / (ν : ℂ)) = (w : ℂ) / (ν : ℂ) by
      push_cast; ring] at h
    intro hz
    exact h (by rw [Complex.exp_neg] at hz; field_simp at hz ⊢; linear_combination -hz)
  have hb : (1 : ℂ) - Complex.exp (2 * π * I * (((w : ℂ) + 1) / (ν : ℂ))) ≠ 0 := by
    have h := one_sub_exp_dual_ne_zero hν hlat (-1)
    have harg' : (w : ℂ) / (ν : ℂ) + ((-1 : ℤ) : ℂ) * (-1 / (ν : ℂ)) =
        ((w : ℂ) + 1) / (ν : ℂ) := by push_cast; field_simp
    rwa [harg'] at h
  have hstep := reflectValue_add_one w ν hν
  have hA := sigmaSHonest_add_one w ν hν hlat
  have hB := sigmaSHonest_neg_add_one w ν hν hlat
  constructor
  · intro h
    refine mul_right_cancel₀ hb ?_
    calc sigmaSHonest w ν * sigmaSHonest (-w) ν *
          (1 - Complex.exp (2 * π * I * (((w : ℂ) + 1) / (ν : ℂ))))
        = sigmaSHonest (w + 1) ν * sigmaSHonest (-(w + 1)) ν *
            (1 - Complex.exp (-(2 * π * I * ((w : ℂ) / (ν : ℂ))))) := by
          rw [hA, ← hB]; ring
      _ = reflectValue w ν * (1 - Complex.exp (2 * π * I * (((w : ℂ) + 1) / (ν : ℂ)))) := by
          rw [h, hstep]
  · intro h
    refine mul_right_cancel₀ ha ?_
    calc sigmaSHonest (w + 1) ν * sigmaSHonest (-(w + 1)) ν *
          (1 - Complex.exp (-(2 * π * I * ((w : ℂ) / (ν : ℂ)))))
        = sigmaSHonest w ν * sigmaSHonest (-w) ν *
            (1 - Complex.exp (2 * π * I * (((w : ℂ) + 1) / (ν : ℂ)))) := by
          rw [hA, ← hB]; ring
      _ = reflectValue (w + 1) ν * (1 - Complex.exp (-(2 * π * I * ((w : ℂ) / (ν : ℂ))))) := by
          rw [h, ← hstep]

/-- The closed form propagates along the whole integer orbit of an off-lattice point. Helper for
`sigmaSHonest_mul_neg_closed`. -/
private lemma sigmaSHonest_mul_neg_intCast_add (w ν : ℝ) (hν : 0 < ν)
    (hlat : SigmaSLatticeFree ν w)
    (h : sigmaSHonest w ν * sigmaSHonest (-w) ν = reflectValue w ν) (n : ℤ) :
    sigmaSHonest (w + n) ν * sigmaSHonest (-(w + n)) ν = reflectValue (w + n) ν := by
  exact SigmaSLatticeFree.add_intCast_of_add_one_iff
    (P := fun u => sigmaSHonest u ν * sigmaSHonest (-u) ν = reflectValue u ν)
    (by
      intro u hu
      exact (sigmaSHonest_mul_neg_add_one_iff u ν hν hu).symm) hlat h n

/-- **The reflection law at an arbitrary argument.** For every real `w` off the lattice `ℤν + ℤ`,

```text
σ_S(w,ν)·σ_S(-w,ν) = (1 - e^{-2πi·w/ν}) / (1 - e^{-2πi·w}) · exp(2·X(w,ν)),
```

with no base-point hypothesis: `sigmaSHonest_mul_neg_of_mem` is the case `w ∈ (-1, ν)`, and the
unit-step recurrence `sigmaSHonest_mul_neg_add_one_iff` — satisfied by both sides — carries it
along the integer orbit that `sfShift` traverses. This applies to the successive arguments of a
word product, which need not lie in the base chamber. -/
theorem sigmaSHonest_mul_neg_closed (w ν : ℝ) (hν : 0 < ν) (hlat : SigmaSLatticeFree ν w) :
    sigmaSHonest w ν * sigmaSHonest (-w) ν =
      (1 - Complex.exp (-(2 * π * I * (w / ν)))) / (1 - Complex.exp (-(2 * π * I * w))) *
        Complex.exp (2 * sfExpArg w ν) := by
  set z : ℝ := w - (sfShift w : ℝ) with hz
  have hlat₀ : SigmaSLatticeFree ν z := by
    have h := hlat.add 0 (-(sfShift w))
    push_cast at h
    simpa [hz, sub_eq_add_neg] using h
  have hbase : sigmaSHonest z ν * sigmaSHonest (-z) ν = reflectValue z ν :=
    sigmaSHonest_mul_neg_of_mem z ν hν (neg_one_lt_sub_sfShift w) (sub_sfShift_lt w ν hν) hlat₀
  have h := sigmaSHonest_mul_neg_intCast_add z ν hν hlat₀ hbase (sfShift w)
  rwa [show z + ((sfShift w : ℤ) : ℝ) = w by rw [hz]; ring] at h

end SIC

end
