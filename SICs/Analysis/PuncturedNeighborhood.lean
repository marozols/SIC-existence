/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Translation, iteration, and nonvanishing on punctured neighborhoods

Translation of punctured neighborhoods, integer iteration of a one-step translation law,
agreement of continuous functions from a punctured germ, and nonvanishing of affine
exponentials near a point.

Translation preserves punctured germs, allowing a one-step law to be iterated forwards and
backwards over the integers. A nonconstant affine exponential has nonzero derivative everywhere,
so it avoids any fixed value on a punctured neighborhood of each point.
-/

noncomputable section

open Complex Filter Topology

namespace SIC

/-! ### Translation and equality of punctured germs -/

/-- Translation by `c` carries the punctured neighborhood of `z` to that of `z+c`. -/
theorem tendsto_add_const_nhdsNE (c z : ℂ) :
    Tendsto (fun ζ : ℂ => ζ + c) (𝓝[≠] z) (𝓝[≠] (z + c)) := by
  change Filter.map (fun ζ : ℂ => ζ + c) (𝓝[≠] z) ≤ 𝓝[≠] (z + c)
  exact le_of_eq ((Homeomorph.addRight c).map_punctured_nhds_eq z)

/-- A punctured germ identity remains valid after translating the argument. -/
theorem eventuallyEq_comp_add_const_nhdsNE {f g : ℂ → ℂ} {z c : ℂ}
    (h : f =ᶠ[𝓝[≠] (z + c)] g) :
    (fun w => f (w + c)) =ᶠ[𝓝[≠] z] fun w => g (w + c) := by
  simpa only [Function.comp_def] using h.comp_tendsto (tendsto_add_const_nhdsNE c z)

/-- Continuous functions agreeing on a punctured germ agree at its center. -/
theorem eq_of_eventuallyEq_nhdsNE_of_continuousAt {f g : ℂ → ℂ} {z : ℂ}
    (hf : ContinuousAt f z) (hg : ContinuousAt g z)
    (h : f =ᶠ[𝓝[≠] z] g) : f z = g z := by
  exact tendsto_nhds_unique_of_eventuallyEq
    (hf.tendsto.mono_left nhdsWithin_le_nhds)
    (hg.tendsto.mono_left nhdsWithin_le_nhds) h

/-! ### Integer iteration of translation laws

The reverse of a one-step law follows by translating its germ in the opposite direction.
Induction then gives the law for every integer multiple of the translation.
-/

/-- The reverse of a one-step translation law for punctured germs. -/
private lemma eventuallyEq_add_neg_of_add {ι : Type*} [AddCommGroup ι]
    (F : ι → ℂ → ℂ) (c : ℂ) (v : ι)
    (h : ∀ p z, (fun w => F p (w + c)) =ᶠ[𝓝[≠] z] F (p + v))
    (p : ι) (z : ℂ) :
    (fun w => F p (w - c)) =ᶠ[𝓝[≠] z] F (p - v) := by
  have hs := eventuallyEq_comp_add_const_nhdsNE (c := -c) (h (p - v) (z - c))
  simpa [sub_eq_add_neg, add_assoc] using hs.symm

/-- An integer translate iterates a one-step translation law for punctured germs. -/
lemma eventuallyEq_add_int_mul_of_add {ι : Type*} [AddCommGroup ι]
    (F : ι → ℂ → ℂ) (c : ℂ) (v : ι)
    (h : ∀ p z, (fun w => F p (w + c)) =ᶠ[𝓝[≠] z] F (p + v))
    (k : ℤ) (p : ι) (z : ℂ) :
    (fun w => F p (w + (k : ℂ) * c)) =ᶠ[𝓝[≠] z] F (p + k • v) := by
  induction k using Int.induction_on generalizing p z with
  | zero => simp
  | succ i hi =>
    have hs := eventuallyEq_comp_add_const_nhdsNE (c := (i : ℂ) * c)
      (h p (z + (i : ℂ) * c))
    have ht := hs.trans (hi (p + v) z)
    simpa [add_mul, add_zsmul, add_assoc, add_left_comm, add_comm] using ht
  | pred i hi =>
    have hs := eventuallyEq_comp_add_const_nhdsNE (c := (-((i : ℂ) * c)))
      (eventuallyEq_add_neg_of_add F c v h p (z - (i : ℂ) * c))
    have hi' : (fun w => F (p - v) (w - (i : ℂ) * c)) =ᶠ[𝓝[≠] z]
        F (p - v + (-(i : ℤ)) • v) := by
      simpa only [Int.cast_neg, Int.cast_natCast, neg_mul, sub_eq_add_neg] using hi (p - v) z
    have ht := hs.trans hi'
    simpa [sub_eq_add_neg, add_mul, add_zsmul, add_assoc, add_left_comm, add_comm]
      using ht

/-! ### Affine exponentials -/

/-- For `A ≠ 0`, `exp(Aζ+B)` avoids any fixed value on a punctured germ. -/
theorem eventually_exp_affine_ne_nhdsNE (A B c z : ℂ) (hA : A ≠ 0) :
    ∀ᶠ ζ in 𝓝[≠] z, Complex.exp (A * ζ + B) ≠ c := by
  have hlin : HasDerivAt (fun ζ : ℂ => A * ζ + B) A z := by
    convert ((hasDerivAt_id z).const_mul A).add_const B using 1 <;> simp
  have hexp : HasDerivAt (fun ζ : ℂ => Complex.exp (A * ζ + B))
      (Complex.exp (A * z + B) * A) z := by
    simpa only [Function.comp_def] using (Complex.hasDerivAt_exp (A * z + B)).comp z hlin
  exact hexp.eventually_ne (mul_ne_zero (Complex.exp_ne_zero _) hA)

/-- For `A ≠ 0`, `e(Aζ+B) = exp(2πi(Aζ+B))` avoids one on a punctured germ. -/
theorem eventually_exp_two_pi_I_affine_ne_one_nhdsNE (A B z : ℂ) (hA : A ≠ 0) :
    ∀ᶠ ζ in 𝓝[≠] z, Complex.exp (2 * Real.pi * I * (A * ζ + B)) ≠ 1 := by
  have hC : (2 * Real.pi * I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
  simpa only [mul_add, mul_assoc] using
    (eventually_exp_affine_ne_nhdsNE ((2 * Real.pi * I) * A)
      ((2 * Real.pi * I) * B) 1 z (mul_ne_zero hC hA))

end SIC

end
