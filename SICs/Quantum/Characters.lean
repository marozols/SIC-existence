/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Quantum.RootsOfUnity

/-!
# Finite symplectic characters and Fourier transforms

Weyl–Heisenberg symplectic characters, orthogonality, and finite Fourier inversion.

This module follows the character calculations of [5, Appleby (2007), equations (74)–(77)]
and [AFK25, Section 3.4, equations (3.51)–(3.53)]. The symplectic pairing on the finite phase
space gives a character in either argument. Orthogonality follows from the one-dimensional
root-of-unity sums in `SICs.Quantum.RootsOfUnity`. Summing twice against the character kernel
then recovers the original function, and hence proves Fourier injectivity.

The displacement conjugation laws use these scalar characters in
`SICs.Quantum.WeylHeisenberg`; the overlap criterion in `SICs.Quantum.Fiducials` uses the
Fourier transform of a function constant away from the origin.
-/

noncomputable section

namespace SIC

/-! ### Weyl--Heisenberg symplectic characters

The finite characters induced by the symplectic form encode the phases in Weyl--Heisenberg
conjugation.  Their orthogonality gives the Fourier identities used for overlap calculations. -/

/-- The Weyl--Heisenberg symplectic character
    `χₚ(q) = ω_d ^ (p₂q₁ - p₁q₂)` on the finite phase space `(Fin d)²`.

    This packages the character appearing in [5, Appleby (2007), eqs. (74)–(77)] and
    [AFK25, eqs. (3.51)–(3.53)]. -/
def whCharacter (d : ℕ) [NeZero d]
    (p q : Fin d × Fin d) : ℂ :=
  omegaFin d (p.2 * q.1 - p.1 * q.2)

/-- The Weyl--Heisenberg character indexed by the origin is trivial. -/
@[simp]
lemma whCharacter_zero_left (d : ℕ) [NeZero d] (q : Fin d × Fin d) :
    whCharacter d 0 q = 1 := by
  simp [whCharacter, omegaFin]

/-- Every Weyl--Heisenberg character takes value one at the origin. -/
@[simp]
lemma whCharacter_zero_right (d : ℕ) [NeZero d] (p : Fin d × Fin d) :
    whCharacter d p 0 = 1 := by
  simp [whCharacter, omegaFin]

/-! The next two lemmas expose bilinearity of the exponent as multiplicativity in each phase-space
argument. Together with finite-root orthogonality, they provide the Fourier kernel used below. -/

/-- A Weyl--Heisenberg character is multiplicative in its first phase-space argument. -/
lemma whCharacter_add_left (d : ℕ) [NeZero d]
    (p q r : Fin d × Fin d) :
    whCharacter d (p + q) r =
      whCharacter d p r * whCharacter d q r := by
  rw [whCharacter, whCharacter, whCharacter, ← omegaFin_add]
  congr 1
  simp only [Prod.fst_add, Prod.snd_add]
  apply (ZMod.finEquiv d).injective
  simp
  ring

/-- A Weyl--Heisenberg character is multiplicative in its second phase-space argument. -/
lemma whCharacter_add_right (d : ℕ) [NeZero d]
    (p q r : Fin d × Fin d) :
    whCharacter d p (q + r) =
      whCharacter d p q * whCharacter d p r := by
  rw [whCharacter, whCharacter, whCharacter, ← omegaFin_add]
  congr 1
  simp only [Prod.fst_add, Prod.snd_add]
  apply (ZMod.finEquiv d).injective
  simp
  ring

/-- Orthogonality of the Weyl--Heisenberg characters on the two-dimensional finite phase space.
    This is the character sum used in [5, Appleby (2007), eqs. (76)–(77)]. -/
theorem sum_whCharacter (d : ℕ) [NeZero d] (q : Fin d × Fin d) :
    ∑ p : Fin d × Fin d, whCharacter d p q =
      if q = 0 then (d : ℂ) ^ 2 else 0 := by
  rcases q with ⟨q₁, q₂⟩
  rw [Fintype.sum_prod_type]
  simp_rw [whCharacter, sub_eq_add_neg, omegaFin_add, ← mul_neg]
  calc
    (∑ p₁ : Fin d, ∑ p₂ : Fin d,
        omegaFin d (p₂ * q₁) * omegaFin d (p₁ * -q₂)) =
        (∑ p₂ : Fin d, omegaFin d (p₂ * q₁)) *
          ∑ p₁ : Fin d, omegaFin d (p₁ * -q₂) := by
      simp_rw [← Finset.sum_mul]
      rw [← Finset.mul_sum]
    _ = (if q₁ = 0 then (d : ℂ) else 0) *
          (if -q₂ = 0 then (d : ℂ) else 0) := by
      rw [sum_omegaFin_mul, sum_omegaFin_mul]
    _ = if (q₁, q₂) = 0 then (d : ℂ) ^ 2 else 0 := by
      by_cases hq₁ : q₁ = 0 <;> by_cases hq₂ : q₂ = 0 <;>
        simp [hq₁, hq₂, pow_two]

/-- Difference form of character orthogonality, convenient for Fourier inversion. -/
theorem sum_whCharacter_sub (d : ℕ) [NeZero d]
    (q r : Fin d × Fin d) :
    ∑ p : Fin d × Fin d, whCharacter d p (q - r) =
      if q = r then (d : ℂ) ^ 2 else 0 := by
  rw [sum_whCharacter]
  simp [sub_eq_zero]

/-- Negating the character index inverts its value. -/
lemma whCharacter_neg_left (d : ℕ) [NeZero d] (p q : Fin d × Fin d) :
    whCharacter d (-p) q = (whCharacter d p q)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← whCharacter_add_left, add_neg_cancel, whCharacter_zero_left]

/-- Negating a character argument inverts its value. -/
lemma whCharacter_neg_right (d : ℕ) [NeZero d] (p q : Fin d × Fin d) :
    whCharacter d p (-q) = (whCharacter d p q)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← whCharacter_add_right, add_neg_cancel, whCharacter_zero_right]

/-- Alternating symmetry of the WH character, arranged to exchange the two summation
    arguments without changing its value. -/
lemma whCharacter_neg_swap (d : ℕ) [NeZero d] (p q : Fin d × Fin d) :
    whCharacter d (-q) p = whCharacter d p q := by
  simp only [whCharacter, Prod.fst_neg, Prod.snd_neg]
  congr 1
  apply (ZMod.finEquiv d).injective
  simp
  ring

/-- Orthogonality summed over the second argument. -/
theorem sum_whCharacter_right (d : ℕ) [NeZero d] (p : Fin d × Fin d) :
    ∑ k : Fin d × Fin d, whCharacter d p k =
      if p = 0 then (d : ℂ) ^ 2 else 0 := by
  calc
    (∑ k : Fin d × Fin d, whCharacter d p k) =
        ∑ k : Fin d × Fin d, whCharacter d (-k) p := by
      apply Finset.sum_congr rfl
      intro k _
      exact (whCharacter_neg_swap d p k).symm
    _ = ∑ k : Fin d × Fin d, whCharacter d k p := by
      simpa using (Equiv.Perm.sum_comp (Equiv.neg (Fin d × Fin d)) Finset.univ
        (fun k => whCharacter d k p) (by simp))
    _ = if p = 0 then (d : ℂ) ^ 2 else 0 := sum_whCharacter d p

/-- Product form of character orthogonality. This is the kernel identity used to invert the
    finite symplectic Fourier transform. -/
theorem sum_mul_whCharacter (d : ℕ) [NeZero d] (q r : Fin d × Fin d) :
    ∑ p : Fin d × Fin d, whCharacter d p q * whCharacter d (-p) r =
      if q = r then (d : ℂ) ^ 2 else 0 := by
  simp_rw [whCharacter_neg_left, ← whCharacter_neg_right,
    ← whCharacter_add_right]
  simpa only [sub_eq_add_neg] using sum_whCharacter_sub d q r

/-- The finite symplectic Fourier transform associated to WH conjugation. -/
def whFourierTransform (d : ℕ) [NeZero d]
    (f : Fin d × Fin d → ℂ) (p : Fin d × Fin d) : ℂ :=
  ∑ k : Fin d × Fin d, f k * whCharacter d p k

/-- Fourier inversion in a denominator-free form. -/
theorem whFourierTransform_inversion (d : ℕ) [NeZero d]
    (f : Fin d × Fin d → ℂ) (q : Fin d × Fin d) :
    ∑ p : Fin d × Fin d,
        whFourierTransform d f p * whCharacter d (-p) q =
      (d : ℂ) ^ 2 * f q := by
  simp only [whFourierTransform]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  simp_rw [sum_mul_whCharacter]
  simp [eq_comm, mul_comm]

/-- The finite symplectic Fourier transform is injective. -/
theorem whFourierTransform_injective (d : ℕ) [NeZero d] :
    Function.Injective (whFourierTransform d) := by
  intro f g hfg
  funext q
  have hf := whFourierTransform_inversion d f q
  have hg := whFourierTransform_inversion d g q
  rw [hfg] at hf
  have hscalar : (d : ℂ) ^ 2 ≠ 0 := by
    exact pow_ne_zero _ (by exact_mod_cast NeZero.ne d)
  exact (mul_left_cancel₀ hscalar) (hf.symm.trans hg)

/-- Closed transform of a function that is `a` at the origin and `b` elsewhere. -/
theorem whFourierTransform_ite_zero (d : ℕ) [NeZero d]
    (a b : ℂ) (p : Fin d × Fin d) :
    whFourierTransform d (fun k => if k = 0 then a else b) p =
      if p = 0 then a + ((d : ℂ) ^ 2 - 1) * b else a - b := by
  classical
  unfold whFourierTransform
  calc
    (∑ k : Fin d × Fin d, (if k = 0 then a else b) * whCharacter d p k) =
        ∑ k : Fin d × Fin d,
          ((if k = 0 then a - b else 0) + b) * whCharacter d p k := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k = 0 <;> simp [hk]
    _ = (a - b) + b * ∑ k : Fin d × Fin d, whCharacter d p k := by
      simp_rw [add_mul, Finset.sum_add_distrib]
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
        whCharacter_zero_right, mul_one, add_right_inj]
      rw [Finset.mul_sum]
    _ = if p = 0 then a + ((d : ℂ) ^ 2 - 1) * b else a - b := by
      rw [sum_whCharacter_right]
      by_cases hp : p = 0 <;> simp [hp]
      ring

end SIC

end
