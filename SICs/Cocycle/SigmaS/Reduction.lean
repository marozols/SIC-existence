/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Cocycle.SigmaS.Basic

/-!
# Canonical evaluation of sigma-S

Canonical reduction, presentation independence, and lattice shifts of sigma-S.

Following [AFK25, equations (8.5)--(8.6) and (8.9)], ceiling reduction places a real
argument in the base chamber. The elementary integer and period shifts show that any two
valid presentations agree away from the lattice. Reducing both sides to one base point
then gives the lattice-shift law for the canonical evaluator `sigmaSHonest`.
-/

noncomputable section

open Complex Real

namespace SIC

/-! ### A canonical single-integer-shift domain reduction

`sfShift` is an explicit integer shift taking any real argument `w` to the chamber
`(-1, τ)` for `τ > 0`. `sigmaSHonest` evaluates `sigmaS` using this shift.
`sigmaSHonest_eq_sigmaS_of_mem` proves that every other valid reducing integer gives the same
value, so the result is independent of the choice.

The word product in `SICs.Cocycle.Word.Basic` uses such an integer reduction at each factor.
`WordSigmaSVisits.period_pos` there ensures that every intermediate period is positive when
the seed matrix has positive Jacobi denominator at the starting period. -/

/-- A canonical, explicit integer shift landing *any* raw real argument `w` inside `sigmaSBase`'s
domain `(-1, τ)`, for *every* `τ > 0`: the ceiling, which puts `w - ⌈w⌉` in `(-1, 0]`.

At a non-integer `w` this is `⌊w⌋ + 1`, the shift one step past the floor. The two differ only at
`w ∈ ℤ`, where `⌊w⌋ + 1` overshoots to the excluded endpoint `-1` and the ceiling shifts not at
all -- so an integer argument, `w = 0` in particular, keeps the value `sigmaSBase` already assigns
it (`sigmaSHonest_intCast`, `sigmaSHonest_zero`). -/
noncomputable def sfShift (w : ℝ) : ℤ := ⌈w⌉

/-- `sfShift`'s value keeps `w` strictly above the domain's lower endpoint: `w - sfShift w > -1`,
from `⌈w⌉ < w + 1`. -/
lemma neg_one_lt_sub_sfShift (w : ℝ) : -1 < w - sfShift w := by
  have hlt := Int.ceil_lt_add_one w
  unfold sfShift
  linarith

/-- `sfShift`'s value lands `w` below any positive `τ`: `w - sfShift w ≤ 0 < τ`, from `w ≤ ⌈w⌉`. -/
lemma sub_sfShift_lt (w τ : ℝ) (hτ : 0 < τ) : w - sfShift w < τ := by
  have hle := Int.le_ceil w
  unfold sfShift
  linarith

/-- **At an integer argument `sfShift` does not shift at all**, so `sigmaSHonest` reads its value
straight off `sigmaSBase` at the base point `0`. -/
lemma sfShift_intCast (n : ℤ) : sfShift (n : ℝ) = n := by
  unfold sfShift
  exact Int.ceil_intCast n

/-- **`sigmaS` at an arbitrary raw real argument**, via the canonical shift `sfShift`. Total
whenever `w` is irrational and `τ > 0`. -/
noncomputable def sigmaSHonest (w τ : ℝ) : ℂ :=
  sigmaS (w - sfShift w) τ 0 (sfShift w)

/-- Two valid shifts `n ≤ m` of the same raw argument `w` give the same `sigmaS` value: the
symmetric core of `sigmaS_add_natCast_sub_natCast`, phrased directly in terms of the raw argument
`w` rather than a base point and a step count. -/
private lemma sigmaS_shift_agree_of_le (w τ : ℝ) (n m : ℤ) (hτ : 0 < τ) (hnm : n ≤ m)
    (hm1 : -1 < w - m) (hn2 : w - n < τ) :
    sigmaS (w - m) τ 0 m = sigmaS (w - n) τ 0 n := by
  have hk : ((m - n).toNat : ℤ) = m - n := Int.toNat_of_nonneg (by omega)
  have hkR : ((m - n).toNat : ℝ) = ((m - n : ℤ) : ℝ) := by exact_mod_cast hk
  have heq1 : (w - m) + ((m - n).toNat : ℝ) = w - n := by rw [hkR]; push_cast; ring
  have heq2 : m - ((m - n).toNat : ℤ) = n := by omega
  have hstep := sigmaS_add_natCast_sub_natCast (w - m) τ m (m - n).toNat hτ hm1
    (by rw [heq1]; exact hn2)
  rw [heq1, heq2] at hstep
  exact hstep.symm

/-- **`sigmaSHonest` agrees with `sigmaS` computed via any other valid shift.** Combined with
`sigmaSHonest`'s totality (`neg_one_lt_sub_sfShift`/`sub_sfShift_lt`), this shows `sfShift`'s
specific formula is immaterial: any integer `n` landing the raw argument `w` inside `sigmaSBase`'s
domain `(-1,τ)` gives the same real generator value `σ_S(w,τ)`. -/
theorem sigmaSHonest_eq_sigmaS_of_mem (w τ : ℝ) (hτ : 0 < τ) (n : ℤ)
    (hn1 : -1 < w - n) (hn2 : w - n < τ) :
    sigmaSHonest w τ = sigmaS (w - n) τ 0 n := by
  unfold sigmaSHonest
  rcases le_total n (sfShift w) with hle | hle
  · exact sigmaS_shift_agree_of_le w τ n (sfShift w) hτ hle (neg_one_lt_sub_sfShift w) hn2
  · exact (sigmaS_shift_agree_of_le w τ (sfShift w) n hτ hle hn1 (sub_sfShift_lt w τ hτ)).symm

/-- **`sigmaSHonest` at an integer argument.** `sfShift` leaves an integer where it is, so the
value is `sigmaS` at base point `0` with a pure integer shift. -/
lemma sigmaSHonest_intCast (n : ℤ) (τ : ℝ) : sigmaSHonest (n : ℝ) τ = sigmaS 0 τ 0 n := by
  unfold sigmaSHonest
  rw [sfShift_intCast]
  norm_num

/-- **`sigmaSHonest` at the origin is `sigmaSBase` at the origin.** `0` already lies in
`sigmaSBase`'s domain `(-1, τ)` for every `τ > 0`, and `sfShift` does not move it. This is the one
lattice point the word walk of an admissible tuple actually reaches: the convolution sum of
[AFK25, Definition 1.34, `dfn:shift`] evaluates the cocycle at an integral index only at the exact
index `0`, the transversal's own representative of the zero class. -/
lemma sigmaSHonest_zero (τ : ℝ) : sigmaSHonest 0 τ = sigmaSBase 0 τ := by
  have h := sigmaSHonest_intCast 0 τ
  rw [Int.cast_zero] at h
  rw [h, sigmaS_zero_zero]


/-! ### Reduction to a pure integer shift

Successive period-direction steps move any presentation to one with period index zero while
keeping its base point in the fundamental interval.  Pure integer-shift independence then compares
the resulting presentations. -/

/-- One-directional core of `sigmaS_zero_congr`: when the two shift indices are ordered, the
larger one's base point is reached from the smaller one's by a nonnegative number of unit steps,
which is exactly `sigmaS_add_natCast_sub_natCast`'s shape. -/
private lemma sigmaS_zero_congr_of_le (z₁ z₂ τ : ℝ) (n₁ n₂ : ℤ) (hτ : 0 < τ)
    (h₁ : -1 < z₁) (h₂u : z₂ < τ) (hk : n₂ ≤ n₁) (heq : z₁ + n₁ = z₂ + n₂) :
    sigmaS z₂ τ 0 n₂ = sigmaS z₁ τ 0 n₁ := by
  obtain ⟨k, hk'⟩ : ∃ k : ℕ, n₁ - n₂ = (k : ℤ) :=
    ⟨(n₁ - n₂).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have hkR : ((k : ℕ) : ℝ) = (n₁ : ℝ) - n₂ := by
    have h' : (((n₁ - n₂ : ℤ)) : ℝ) = (((k : ℤ)) : ℝ) := by rw [hk']
    push_cast at h'; linarith
  have hz2 : z₂ = z₁ + (k : ℝ) := by rw [hkR]; linarith
  have hn2 : n₂ = n₁ - (k : ℤ) := by omega
  rw [hz2, hn2]
  exact sigmaS_add_natCast_sub_natCast z₁ τ n₁ k hτ h₁ (by rw [← hz2]; exact h₂u)

/-- **Two pure integer shifts of the same raw argument agree.** The `m₁ = 0` case of
`sigmaS_congr`, stated symmetrically in the two presentations rather than as a step. No
lattice-freeness is needed here: the integer direction moves only the *second* `qPochhammerFin`,
whose index-shift recursion (`qPochhammerFin_add_one_sub_period` inside
`sigmaS_add_one_sub_one`) already carries its own nonvanishing proof. -/
theorem sigmaS_zero_congr (z₁ z₂ τ : ℝ) (n₁ n₂ : ℤ) (hτ : 0 < τ)
    (h₁ : -1 < z₁) (h₁u : z₁ < τ) (h₂ : -1 < z₂) (h₂u : z₂ < τ)
    (heq : z₁ + n₁ = z₂ + n₂) :
    sigmaS z₁ τ 0 n₁ = sigmaS z₂ τ 0 n₂ := by
  rcases le_total n₂ n₁ with hle | hle
  · exact (sigmaS_zero_congr_of_le z₁ z₂ τ n₁ n₂ hτ h₁ h₂u hle heq).symm
  · exact sigmaS_zero_congr_of_le z₂ z₁ τ n₂ n₁ hτ h₂ h₁u hle heq.symm

/-- **One period-index decrement.** Slide the base point down by integers into `(-1, 0)` — where
`sigmaS_add_period_sub_one` applies — then take one period step. The new base point lands in
`(τ-1, τ) ⊆ (-1, τ)`, so the move can be iterated. -/
private lemma sigmaS_period_down (z τ : ℝ) (m₁ m₂ : ℤ) (hτ : 0 < τ) (hz : -1 < z) (hzu : z < τ)
    (hlat : SigmaSLatticeFree τ z) :
    ∃ (z' : ℝ) (m₂' : ℤ), -1 < z' ∧ z' < τ ∧ SigmaSLatticeFree τ z' ∧
      z' + (m₁ - 1) * τ + m₂' = z + m₁ * τ + m₂ ∧
      sigmaS z τ m₁ m₂ = sigmaS z' τ (m₁ - 1) m₂' := by
  have hfl_le : ((⌊z⌋ : ℝ)) ≤ z := Int.floor_le z
  have hfl_lt : z < ⌊z⌋ + 1 := Int.lt_floor_add_one z
  have hfl_ne : ((⌊z⌋ : ℝ)) ≠ z := fun h => hlat.ne_intCast ⌊z⌋ h.symm
  have hy1 : -1 < z - (⌊z⌋ + 1) := by rcases hfl_le.lt_or_eq with h | h; · linarith
                                      · exact absurd h hfl_ne
  have hy2 : z - ((⌊z⌋ : ℝ) + 1) < 0 := by linarith
  have hk0 : (0 : ℤ) ≤ ⌊z⌋ + 1 := by
    have : (-1 : ℤ) ≤ ⌊z⌋ := Int.le_floor.mpr (by push_cast; linarith)
    omega
  have hkR : ((((⌊z⌋ + 1).toNat : ℕ)) : ℝ) = ((⌊z⌋ : ℝ) + 1) := by
    rw [show ((((⌊z⌋ + 1).toNat : ℕ)) : ℝ) = ((((⌊z⌋ + 1).toNat : ℕ) : ℤ) : ℝ) from by
      push_cast; ring, Int.toNat_of_nonneg hk0]
    push_cast; ring
  have hstep1 : sigmaS z τ m₁ m₂ = sigmaS (z - (⌊z⌋ + 1)) τ m₁ (m₂ + (⌊z⌋ + 1)) := by
    have := sigmaS_add_natCast_sub_natCast' (z - ((⌊z⌋ : ℝ) + 1)) τ m₁ (m₂ + (⌊z⌋ + 1))
      ((⌊z⌋ + 1).toNat) hτ hy1 (by rw [hkR]; linarith)
    rw [hkR] at this
    rw [show z - ((⌊z⌋ : ℝ) + 1) + ((⌊z⌋ : ℝ) + 1) = z from by ring] at this
    rw [show m₂ + (⌊z⌋ + 1) - (((⌊z⌋ + 1).toNat : ℕ) : ℤ) = m₂ from by
      rw [Int.toNat_of_nonneg hk0]; ring] at this
    exact this
  refine ⟨z - ((⌊z⌋ : ℝ) + 1) + τ, m₂ + (⌊z⌋ + 1), by linarith, by linarith, ?_,
    by push_cast; ring, ?_⟩
  · rw [show z - ((⌊z⌋ : ℝ) + 1) + τ = z + ((1 : ℤ) : ℝ) * τ + ((-(⌊z⌋ + 1) : ℤ) : ℝ) from by
      push_cast; ring]
    exact hlat.add 1 (-(⌊z⌋ + 1))
  · rw [hstep1, ← sigmaS_add_period_sub_one (z - ((⌊z⌋ : ℝ) + 1)) τ m₁ (m₂ + (⌊z⌋ + 1)) hτ hy1 hy2]

/-- **One period-index increment.** The mirror of `sigmaS_period_down`: slide the base point up by
integers into `(τ-1, τ)`, then run one period step backwards. The new base point lands in
`(-1, 0) ⊆ (-1, τ)`. -/
private lemma sigmaS_period_up (z τ : ℝ) (m₁ m₂ : ℤ) (hτ : 0 < τ) (hz : -1 < z) (hzu : z < τ)
    (hlat : SigmaSLatticeFree τ z) :
    ∃ (z' : ℝ) (m₂' : ℤ), -1 < z' ∧ z' < τ ∧ SigmaSLatticeFree τ z' ∧
      z' + (m₁ + 1) * τ + m₂' = z + m₁ * τ + m₂ ∧
      sigmaS z τ m₁ m₂ = sigmaS z' τ (m₁ + 1) m₂' := by
  have hce_le : τ - z ≤ ⌈τ - z⌉ := Int.le_ceil _
  have hce_lt : ((⌈τ - z⌉ : ℝ)) < τ - z + 1 := by exact_mod_cast Int.ceil_lt_add_one _
  have hce_ne : ((⌈τ - z⌉ : ℝ)) ≠ τ - z := fun h => hlat 1 (-⌈τ - z⌉) (by push_cast; linarith)
  have hk0 : (0 : ℤ) ≤ ⌈τ - z⌉ - 1 := by
    have : (0 : ℤ) < ⌈τ - z⌉ := Int.ceil_pos.mpr (by linarith)
    omega
  have hkR : ((((⌈τ - z⌉ - 1).toNat : ℕ)) : ℝ) = ((⌈τ - z⌉ : ℝ) - 1) := by
    rw [show ((((⌈τ - z⌉ - 1).toNat : ℕ)) : ℝ) = ((((⌈τ - z⌉ - 1).toNat : ℕ) : ℤ) : ℝ) from by
      push_cast; ring, Int.toNat_of_nonneg hk0]
    push_cast; ring
  have hu2 : z + ((⌈τ - z⌉ : ℝ) - 1) < τ := by linarith
  have hv1 : -1 < z + ((⌈τ - z⌉ : ℝ) - 1) - τ := by
    rcases hce_le.lt_or_eq with h | h
    · linarith
    · exact absurd h.symm hce_ne
  have hv2 : z + ((⌈τ - z⌉ : ℝ) - 1) - τ < 0 := by linarith
  have hstep1 : sigmaS z τ m₁ m₂ = sigmaS (z + ((⌈τ - z⌉ : ℝ) - 1)) τ m₁ (m₂ - (⌈τ - z⌉ - 1)) := by
    have := sigmaS_add_natCast_sub_natCast' z τ m₁ m₂ ((⌈τ - z⌉ - 1).toNat) hτ hz
      (by rw [hkR]; exact hu2)
    rw [hkR] at this
    rw [show m₂ - (((⌈τ - z⌉ - 1).toNat : ℕ) : ℤ) = m₂ - (⌈τ - z⌉ - 1) from by
      rw [Int.toNat_of_nonneg hk0]] at this
    exact this.symm
  refine ⟨z + ((⌈τ - z⌉ : ℝ) - 1) - τ, m₂ - (⌈τ - z⌉ - 1), hv1, by linarith, ?_,
    by push_cast; ring, ?_⟩
  · rw [show z + ((⌈τ - z⌉ : ℝ) - 1) - τ
        = z + ((-1 : ℤ) : ℝ) * τ + (((⌈τ - z⌉ - 1) : ℤ) : ℝ) from by push_cast; ring]
    exact hlat.add (-1) (⌈τ - z⌉ - 1)
  · rw [hstep1, ← sigmaS_add_period_sub_one (z + ((⌈τ - z⌉ : ℝ) - 1) - τ) τ (m₁ + 1)
      (m₂ - (⌈τ - z⌉ - 1)) hτ hv1 hv2]
    rw [show z + ((⌈τ - z⌉ : ℝ) - 1) - τ + τ = z + ((⌈τ - z⌉ : ℝ) - 1) from by ring,
      show m₁ + 1 - 1 = m₁ from by ring]

/-- **Every presentation reduces to a pure integer shift.** Induction on `|m₁|`, decrementing it
by `sigmaS_period_down` when positive and incrementing it by `sigmaS_period_up` when negative;
each step returns a base point that is again in `(-1, τ)` and again lattice-free, so the induction
goes through with no extra bookkeeping. -/
private lemma sigmaS_exists_period_zero (τ : ℝ) (hτ : 0 < τ) :
    ∀ (N : ℕ) (m₁ : ℤ), m₁.natAbs = N → ∀ (z : ℝ) (m₂ : ℤ), -1 < z → z < τ →
      SigmaSLatticeFree τ z →
      ∃ (z' : ℝ) (n : ℤ), -1 < z' ∧ z' < τ ∧ z' + n = z + m₁ * τ + m₂ ∧
        sigmaS z τ m₁ m₂ = sigmaS z' τ 0 n := by
  intro N
  induction N with
  | zero =>
      intro m₁ hm₁ z m₂ hz hzu _
      obtain rfl : m₁ = 0 := Int.natAbs_eq_zero.mp hm₁
      exact ⟨z, m₂, hz, hzu, by push_cast; ring, rfl⟩
  | succ M ih =>
      intro m₁ hm₁ z m₂ hz hzu hlat
      rcases lt_or_gt_of_ne (show m₁ ≠ 0 by omega) with hneg | hpos
      · obtain ⟨z', m₂', h1, h2, h3, h4, h5⟩ := sigmaS_period_up z τ m₁ m₂ hτ hz hzu hlat
        obtain ⟨z'', n, g1, g2, g3, g4⟩ := ih (m₁ + 1) (by omega) z' m₂' h1 h2 h3
        exact ⟨z'', n, g1, g2, by push_cast at g3 h4 ⊢; linarith, h5.trans g4⟩
      · obtain ⟨z', m₂', h1, h2, h3, h4, h5⟩ := sigmaS_period_down z τ m₁ m₂ hτ hz hzu hlat
        obtain ⟨z'', n, g1, g2, g3, g4⟩ := ih (m₁ - 1) (by omega) z' m₂' h1 h2 h3
        exact ⟨z'', n, g1, g2, by push_cast at g3 h4 ⊢; linarith, h5.trans g4⟩

/-! ### The joint shift-independence theorem

Reducing both sides to period index zero proves that `sigmaS` depends only on the raw point
`z + m₁τ + m₂`.  This is the comparison principle needed between word and explicit formulas. -/

/-- **`sigmaS` depends only on the raw argument `z + m₁τ + m₂`.** Two presentations of the same
real point by a base point in `sigmaSBase`'s domain `(-1, τ)` and a lattice offset `m₁τ + m₂` give
the same value, provided the point avoids the lattice `ℤτ + ℤ` (`SigmaSLatticeFree`; the
hypothesis is stated for `z₁`, and transfers to `z₂` because the two differ by a lattice vector).

This settles shift-presentation independence in full generality: `sigmaS_add_natCast_sub_natCast`
and `sigmaSHonest_eq_sigmaS_of_mem` above settle only the
one-parameter (`m₁ = 0`) case, which is all `SICs.Cocycle.Word.Basic`'s own recursion produces, but
not
enough to compare that recursion against the principal family's known-correct value, whose third
factor carries a genuine period shift. -/
theorem sigmaS_congr (z₁ z₂ τ : ℝ) (a₁ b₁ a₂ b₂ : ℤ) (hτ : 0 < τ)
    (h₁ : -1 < z₁) (h₁u : z₁ < τ) (h₂ : -1 < z₂) (h₂u : z₂ < τ)
    (hlat : SigmaSLatticeFree τ z₁)
    (heq : z₁ + a₁ * τ + b₁ = z₂ + a₂ * τ + b₂) :
    sigmaS z₁ τ a₁ b₁ = sigmaS z₂ τ a₂ b₂ := by
  have hlat₂ : SigmaSLatticeFree τ z₂ := by
    intro a b hab
    refine hlat (a + a₂ - a₁) (b + b₂ - b₁) ?_
    push_cast at heq ⊢
    linarith
  obtain ⟨u₁, n₁, p₁, p₂, p₃, p₄⟩ :=
    sigmaS_exists_period_zero τ hτ a₁.natAbs a₁ rfl z₁ b₁ h₁ h₁u hlat
  obtain ⟨u₂, n₂, q₁, q₂, q₃, q₄⟩ :=
    sigmaS_exists_period_zero τ hτ a₂.natAbs a₂ rfl z₂ b₂ h₂ h₂u hlat₂
  rw [p₄, q₄]
  exact sigmaS_zero_congr u₁ u₂ τ n₁ n₂ hτ p₁ p₂ q₁ q₂ (by rw [p₃, q₃, heq])

/-- **The canonical total value computes every presentation.** `sigmaSHonest` — the
`SICs.Cocycle.Word.Basic` construction's own per-factor evaluator — agrees with `sigmaS` at *any*
base
point/lattice-offset presentation of the same raw argument, not merely at the pure integer shifts
`sigmaSHonest_eq_sigmaS_of_mem` already covers.

This is the form the principal link-up needs: it converts a `wordSigmaS` factor into whatever
explicitly-reduced `sigmaS` the principal family supplies for the same point.

The lattice hypothesis is on the *base point* `z`, not on `w`, and it is what makes the two
presentations agree at all: at a lattice point different presentations genuinely disagree. No
irrationality of `w` is needed here, nor in `sigmaSHonest_eq_sigmaS_of_mem`. That matters in
practice — the principal family's own first word argument `z = (qρ_d - p)/d` is *rational* when
`q = 0`, so an irrationality hypothesis would exclude a whole boundary line of index pairs. -/
theorem sigmaSHonest_eq_sigmaS (w z τ : ℝ) (m₁ m₂ : ℤ) (hτ : 0 < τ)
    (hz : -1 < z) (hzu : z < τ) (hlat : SigmaSLatticeFree τ z)
    (heq : z + m₁ * τ + m₂ = w) :
    sigmaSHonest w τ = sigmaS z τ m₁ m₂ := by
  rw [sigmaSHonest]
  refine (sigmaS_congr z (w - sfShift w) τ m₁ m₂ 0 (sfShift w) hτ hz hzu
    (neg_one_lt_sub_sfShift w) (sub_sfShift_lt w τ hτ) hlat ?_).symm
  push_cast
  linarith

/-! ### The lattice-shift law for `sigmaSHonest`

The joint independence theorem converts a lattice translation of the raw argument into an exact
ratio of finite `q`-Pochhammer products.  This identity is the one-letter seed for the word-level
quasiperiodicity theorem. -/

/-- **`sigmaSHonest`'s lattice-shift law.** Moving the *raw* argument by a lattice vector
`m₁ν + m₂` multiplies `σ_S` by exactly the `q`-Pochhammer ratio of `sigmaS`:
```
σ_S(w + m₁ν + m₂, ν) · ϖ_{-m₂}(w/ν, -1/ν) = σ_S(w, ν) · ϖ_{m₁}(w, ν).
```
Where `sigmaS`'s defining formula reads that ratio off a *base point* supplied by the caller,
this reads it off the raw argument itself, which is what a word walk actually has: both
`sigmaSHonest` calls are then reduced to a common base point by `sigmaSHonest_eq_sigmaS`, and the
two `q`-Pochhammer bookkeeping factors separating them recombine by `qPochhammerFin_add`.

Stated multiplicatively, so the only hypothesis beyond `0 < ν` is `hlat` — which is genuinely
needed, not a convenience: see `SigmaSLatticeFree`. This is the single-generator seed of
`SICs.Cocycle.Word.Shifts.wordSigmaS_lattice_shift`. -/
theorem sigmaSHonest_lattice_shift (w ν : ℝ) (m₁ m₂ : ℤ) (hν : 0 < ν)
    (hlat : SigmaSLatticeFree ν w) :
    sigmaSHonest (w + m₁ * ν + m₂) ν * qPochhammerFin (-m₂) ((w : ℂ) / (ν : ℂ)) (-1 / (ν : ℂ)) =
      sigmaSHonest w ν * qPochhammerFin m₁ (w : ℂ) (ν : ℂ) := by
  have hν0 : ν ≠ 0 := hν.ne'
  have hνC : (ν : ℂ) ≠ 0 := by exact_mod_cast hν0
  have hlo : -1 < w - (sfShift w : ℝ) := neg_one_lt_sub_sfShift w
  have hhi : w - (sfShift w : ℝ) < ν := sub_sfShift_lt w ν hν
  have hlat₀ : SigmaSLatticeFree ν (w - (sfShift w : ℝ)) := by
    have h := hlat.add 0 (-(sfShift w))
    push_cast at h
    simpa [sub_eq_add_neg] using h
  have h2 : sigmaSHonest (w + m₁ * ν + m₂) ν =
      sigmaS (w - (sfShift w : ℝ)) ν m₁ (m₂ + sfShift w) := by
    refine sigmaSHonest_eq_sigmaS _ _ ν m₁ (m₂ + sfShift w) hν hlo hhi hlat₀ ?_
    push_cast
    ring
  have h1 : sigmaSHonest w ν = sigmaS (w - (sfShift w : ℝ)) ν 0 (sfShift w) := rfl
  -- The two `q`-Pochhammer factors of `sigmaS`'s formula, at the common base point.
  have hshift : ((w - (sfShift w : ℝ) : ℝ) : ℂ) = (w : ℂ) + ((-sfShift w : ℤ) : ℂ) := by
    push_cast; ring
  have hplain : qPochhammerFin m₁ ((w - (sfShift w : ℝ) : ℝ) : ℂ) (ν : ℂ) =
      qPochhammerFin m₁ (w : ℂ) (ν : ℂ) := by
    rw [hshift]
    exact qPochhammerFin_add_intCast m₁ (w : ℂ) ν (-sfShift w)
  have hdual : ((w - (sfShift w : ℝ) : ℝ) : ℂ) / (ν : ℂ) +
      ((-sfShift w : ℤ) : ℂ) * (-1 / (ν : ℂ)) = (w : ℂ) / (ν : ℂ) := by
    push_cast
    field_simp
    ring
  have hsplit : qPochhammerFin (-(m₂ + sfShift w))
        (((w - (sfShift w : ℝ) : ℝ) : ℂ) / (ν : ℂ)) (-1 / (ν : ℂ)) =
      qPochhammerFin (-sfShift w) (((w - (sfShift w : ℝ) : ℝ) : ℂ) / (ν : ℂ)) (-1 / (ν : ℂ)) *
        qPochhammerFin (-m₂) ((w : ℂ) / (ν : ℂ)) (-1 / (ν : ℂ)) := by
    have hadd := qPochhammerFin_add (-sfShift w) (-m₂)
      (((w - (sfShift w : ℝ) : ℝ) : ℂ) / (ν : ℂ)) (-1 / (ν : ℂ))
      (one_sub_exp_dual_ne_zero hν hlat₀)
    rw [hdual] at hadd
    rw [show -(m₂ + sfShift w) = -sfShift w + -m₂ from by ring, hadd]
  have hAne : qPochhammerFin (-sfShift w)
      (((w - (sfShift w : ℝ) : ℝ) : ℂ) / (ν : ℂ)) (-1 / (ν : ℂ)) ≠ 0 :=
    qPochhammerFin_ne_zero_of_forall_factor_ne_zero _ _ _ (one_sub_exp_dual_ne_zero hν hlat₀)
  have hBne : qPochhammerFin (-m₂) ((w : ℂ) / (ν : ℂ)) (-1 / (ν : ℂ)) ≠ 0 :=
    qPochhammerFin_ne_zero_of_forall_factor_ne_zero _ _ _ (one_sub_exp_dual_ne_zero hν hlat)
  rw [h1, h2, sigmaS, sigmaS, hsplit, hplain,
    show qPochhammerFin (0 : ℤ) ((w - (sfShift w : ℝ) : ℝ) : ℂ) (ν : ℂ) = 1 from by
      simp [qPochhammerFin]]
  set A := qPochhammerFin (-sfShift w) (((w - (sfShift w : ℝ) : ℝ) : ℂ) / (ν : ℂ)) (-1 / (ν : ℂ))
  set B := qPochhammerFin (-m₂) ((w : ℂ) / (ν : ℂ)) (-1 / (ν : ℂ))
  field_simp

/-- The unit step of `sigmaSHonest_lattice_shift` in the integer direction:
`σ_S(w+1,ν) = σ_S(w,ν)·(1 - e^{2πi(w+1)/ν})`. -/
lemma sigmaSHonest_add_one (w ν : ℝ) (hν : 0 < ν) (hlat : SigmaSLatticeFree ν w) :
    sigmaSHonest (w + 1) ν =
      sigmaSHonest w ν * (1 - Complex.exp (2 * π * I * ((w + 1) / ν))) := by
  have hνC : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
  have harg : (w : ℂ) / (ν : ℂ) - -1 / (ν : ℂ) = ((w : ℂ) + 1) / (ν : ℂ) := by
    field_simp
    ring
  have hne : (1 : ℂ) - Complex.exp (2 * π * I * (((w : ℂ) + 1) / (ν : ℂ))) ≠ 0 := by
    have h := one_sub_exp_dual_ne_zero hν hlat (-1)
    have harg' : (w : ℂ) / (ν : ℂ) + ((-1 : ℤ) : ℂ) * (-1 / (ν : ℂ)) =
        ((w : ℂ) + 1) / (ν : ℂ) := by push_cast; field_simp
    rwa [harg'] at h
  have h := sigmaSHonest_lattice_shift w ν 0 1 hν hlat
  rw [show w + ((0 : ℤ) : ℝ) * ν + ((1 : ℤ) : ℝ) = w + 1 by push_cast; ring,
    show (-(1 : ℤ)) = -1 from rfl, qPochhammerFin_neg_one, harg,
    show qPochhammerFin (0 : ℤ) (w : ℂ) (ν : ℂ) = 1 by simp [qPochhammerFin], mul_one,
    ← div_eq_mul_inv, div_eq_iff hne] at h
  exact h

end SIC

end
