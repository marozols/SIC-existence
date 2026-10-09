/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Elementary algebra for finite five-term identities

Algebraic cancellations and finite-sum rearrangements used by both the
letter-word and principal finite five-term arguments.

The complex identities isolate the field calculations after the analytic factors have been
identified. The finite-sum identities isolate reindexing and column selection. They carry no
data from either finite five-term construction, so the two direct arguments can share them
without sharing their mathematical setup.
-/

open scoped BigOperators

namespace SIC.FiniteFiveTerm

/-- Multiplying a closed-form quotient by its left index factor replaces the corresponding
denominator factor. -/
theorem closedForm_algebra (P M N D U V V₀ : ℂ)
    (hfactor : P / V = 1 / V₀) :
    P * ((M / N) * (D / (V * U))) = (M / N) * (D / (V₀ * U)) := by
  calc
    _ = (M / N * (D / U)) * (P / V) := by simp only [div_eq_mul_inv, mul_inv_rev]; ring
    _ = _ := by rw [hfactor]; simp only [div_eq_mul_inv, mul_inv_rev]; ring

/-- The algebraic cancellation that removes a residue pole by a one-step bracket. -/
theorem bracket_algebra (A B C D F U V W E : ℂ)
    (hAB : A - B ≠ 0) (hB : 1 - B ≠ 0) (hF : 1 - F ≠ 0) (hV : V ≠ 0)
    (hW : W = (1 - F) * V) (hD : D = B * C) (hE : F = A * C) :
    ((U / V * E) * (1 - B) / (A - B)) *
      (1 - ((1 - A) * (1 - D) / ((1 - B) * (1 - F)))) =
      (1 - C) * (U / W) * E := by
  subst W
  subst D
  subst F
  field_simp
  ring

/-- Four product index shifts turn the translated quotient into the original quotient times
its one-step bracket. -/
theorem shift_algebra (A B D F Q U V U1 V1 U11 V11 E : ℂ)
    (hQ : Q ≠ 0) (hAB : A - B ≠ 0)
    (hB : 1 - B ≠ 0) (hF : 1 - F ≠ 0) (hV : V ≠ 0)
    (hU : U = U1 * (1 - B)) (hVeq : V = V1 * (1 - D))
    (hU11 : U11 = (1 - A) * U1) (hV11eq : V11 = (1 - F) * V1) :
    U11 / V11 * (Q * E) / (Q * (A - B)) =
      (U / V * E / (A - B)) *
        ((1 - A) * (1 - D) / ((1 - B) * (1 - F))) := by
  subst U
  subst V
  subst U11
  subst V11
  have hV1 : V1 ≠ 0 := (mul_ne_zero_iff.mp hV).1
  have hD : 1 - D ≠ 0 := (mul_ne_zero_iff.mp hV).2
  field_simp [hD]

/-- A finite permutation and the pointwise cancellation `f(1-b)=g` give the telescoping sum. -/
theorem finite_telescope {ι : Type*} [Fintype ι] (e : ι ≃ ι)
    (f b g : ι → ℂ) (h : ∀ i, f i * (1 - b i) = g i) :
    (∑ i, f i) - (∑ i, f (e i) * b (e i)) = ∑ i, g i := by
  rw [Equiv.sum_comp e (fun i => f i * b i), ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← h i]
  ring

/-- Algebraic reduction of a residue phase from `z/ε-z=mρ+k`, `w=s₁ρ-s₀`, and
`ε=cρ+d`. -/
theorem residuePhase_algebra
    (ρ ε c d z w s₀ s₁ m k u : ℂ)
    (hε : ε ≠ 0) (hz : z / ε - z = m * ρ + k)
    (hw : w = s₁ * ρ - s₀) (hu : u = c * s₀ + (d - 1) * s₁)
    (hεeq : ε = c * ρ + d) :
    -z / ε + ((c * z + ε * m) * w) / ε + (u + 1) * (z + m * ρ) =
      (-k * s₁ - m * s₀) - k * (u + 1) := by
  have hfactor : ((c * z + ε * m) * w) / ε = (c * (z / ε) + m) * w := by
    field_simp [hε]
  have hmul : (ε - 1) * z = -ε * (m * ρ + k) := by
    calc
      (ε - 1) * z = -ε * (z / ε - z) := by field_simp [hε]; ring
      _ = _ := by rw [hz]
  have hcoeff : (c * (z + m * ρ + k) + m) * ρ + (d - 1) * (z + m * ρ) =
      -d * k := by
    linear_combination hmul - (z + m * ρ + k) * hεeq
  calc
    _ = -k + (c * (z + m * ρ + k) + m) * w + u * (z + m * ρ) := by
      rw [hfactor]
      linear_combination (c * w - 1) * hz
    _ = -k + (c * (z + m * ρ + k) + m) * (s₁ * ρ - s₀) +
          (c * s₀ + (d - 1) * s₁) * (z + m * ρ) := by rw [hw, hu]
    _ = -k + ((c * (z + m * ρ + k) + m) * ρ +
          (d - 1) * (z + m * ρ)) * s₁ + (-c * k - m) * s₀ := by ring
    _ = -k + (-d * k) * s₁ + (-c * k - m) * s₀ := by rw [hcoeff]
    _ = _ := by rw [hu]; ring

/-- A finite column with a unique selected member contributes that member alone. -/
theorem unique_column_sum (G : Finset (ℤ × ℕ))
    (j k : ℤ) (hmem : (k, j.toNat) ∈ G)
    (hUnique : ∀ kj ∈ G, kj.2 = j.toNat → kj = (k, j.toNat))
    (B : ℤ × ℕ → ℂ) :
    (∑ kj ∈ G, if kj.2 = j.toNat then B kj else 0) = B (k, j.toNat) := by
  rw [Finset.sum_eq_single (k, j.toNat)
    (by
      intro kj hkj hne
      have hcol : kj.2 ≠ j.toNat := by
        intro heq
        exact hne (hUnique kj hkj heq)
      simp [hcol])
    (by intro hn; exact (hn hmem).elim)]
  simp

/-- Summing the selected member of every nonnegative column recovers the full finite sum. -/
theorem column_sum {ι : Type*} [Fintype ι]
    (F : Finset ℤ) (G : ι → Finset (ℤ × ℕ)) (B : ι → ℤ × ℕ → ℂ)
    (hFnonneg : ∀ j ∈ F, 0 ≤ j)
    (hFpole : ∀ (m : ι) (kj : ℤ × ℕ), kj ∈ G m → (kj.2 : ℤ) ∈ F) :
    (∑ j ∈ F, ∑ m : ι, ∑ kj ∈ G m,
      if kj.2 = j.toNat then B m kj else 0) =
        ∑ m : ι, ∑ kj ∈ G m, B m kj := by
  classical
  calc
    _ = ∑ m : ι, ∑ j ∈ F, ∑ kj ∈ G m,
          if kj.2 = j.toNat then B m kj else 0 := Finset.sum_comm
    _ = ∑ m : ι, ∑ kj ∈ G m, ∑ j ∈ F,
          if kj.2 = j.toNat then B m kj else 0 := by
      apply Finset.sum_congr rfl
      intro m _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro kj hkj
      calc
        _ = ∑ j ∈ F, if j = (kj.2 : ℤ) then B m kj else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          congr 1
          apply propext
          constructor
          · intro he
            have hj0 : 0 ≤ j := hFnonneg j hj
            omega
          · intro he
            omega
        _ = B m kj := by simp [hFpole m kj hkj]

end SIC.FiniteFiveTerm
