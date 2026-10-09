/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.QPochhammer.Bounds

/-!
# The theta product

The product `θ(z,τ) = ϖ(z,τ) ϖ(τ-z,τ)`, its quasi-periodicity, zeros, slope at the origin, and
bounds.

For `τ ∈ ℍ` and `x = e(z)`, `θ(z,τ) = (x;q)∞ (q/x;q)∞` is the product side of Jacobi's triple
product [RW26, Radchenko, Wheeler (2026), equation (59), `eq:jac.trip`], which reads
`θ(z+τ,τ) (q;q)∞ = ∑ₙ (-1)ⁿ q^{n(n+1)/2} xⁿ`; only the product is used here. The theta
norm has Gaussian growth away from its zero lattice, as used in the modular five-term
estimates of [RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`].

## The argument

Integer periodicity is that of `ϖ`. Splitting off the first factor of `ϖ(z,τ)`, and writing
`ϖ(-z,τ) = (1-e(-z)) ϖ(τ-z,τ)`, gives `θ(z+τ)(1-e(z)) = (1-e(-z)) θ(z)`. Since
`1-e(-z) = -e(-z)(1-e(z))`, and both sides vanish when `e(z) = 1`, the quasi-periodicity
`θ(z+τ) = -e(-z) θ(z)` holds everywhere. The zeros of `ϖ(z,τ)` are `ℤ - ℕτ` and those of
`ϖ(τ-z,τ)` are `ℤ + (ℕ+1)τ`, so `θ` vanishes exactly on the lattice `ℤ + ℤτ`.

The factor `1-e(z)` in `ϖ(z,τ)` has a simple zero at zero, while the remaining factors tend to
`ϖ(τ,τ)² ≠ 0`. Integer periodicity and compactness bound `θ` on a period strip, above everywhere
and below away from the lattice. Its norm and the Gaussian `exp(π(Im z)²/Im τ - π Im z)` gain the
same factor under `z ↦ z+τ`. Their ratio is lattice invariant, so the strip bounds extend to the
whole plane.
-/

noncomputable section

open Complex Real Filter
open scoped Topology

namespace SIC

/-! ### Definition and quasi-periodicity

The two products are exchanged by `z ↦ τ - z`; the shift by `τ` moves one factor between
them. -/

/-- The theta product `θ(z,τ) = ϖ(z,τ) ϖ(τ-z,τ)`, the product side of Jacobi's triple product
[RW26, Radchenko, Wheeler (2026), equation (59), `eq:jac.trip`], which is
`θ(z+τ,τ) (q;q)∞` in the source's variables `x = e(z)`, `q = e(τ)`. -/
def qTheta (z τ : ℂ) : ℂ :=
  qPochhammer z τ * qPochhammer (τ - z) τ

/-- `θ(z+k,τ) = θ(z,τ)` for every integer `k`. -/
theorem qTheta_add_intCast (z τ : ℂ) (k : ℤ) : qTheta (z + k) τ = qTheta z τ := by
  unfold qTheta
  rw [qPochhammer_add_intCast z τ k]
  rw [show τ - (z + (k : ℂ)) = (τ - z) + ((-k : ℤ) : ℂ) by push_cast; ring,
    qPochhammer_add_intCast]

/-- The quasi-periodicity `θ(z+τ,τ) = -e(-z) θ(z,τ)` for `Im τ > 0`, including at the zeros. -/
theorem qTheta_add_self (z τ : ℂ) (hτ : 0 < τ.im) :
    qTheta (z + τ) τ = -Complex.exp (-(2 * π * I * z)) * qTheta z τ := by
  let E := Complex.exp (2 * π * I * z)
  let F := Complex.exp (-(2 * π * I * z))
  have hsplit₁ : (1 - E) * qPochhammer (z + τ) τ = qPochhammer z τ := by
    simpa [E, qPochhammerFin_one] using
      qPochhammerFin_natCast_mul_qPochhammer_add 1 z τ hτ
  have hsplit₂ : (1 - F) * qPochhammer (τ - z) τ = qPochhammer (-z) τ := by
    simpa [F, qPochhammerFin_one, sub_eq_add_neg, add_comm] using
      qPochhammerFin_natCast_mul_qPochhammer_add 1 (-z) τ hτ
  have hEF : E * F = 1 := by
    simp [E, F, Complex.exp_neg]
  have hfactor : 1 - F = -F * (1 - E) := by
    calc 1 - F = E * F - F := by rw [hEF]
      _ = -F * (1 - E) := by ring
  by_cases hE : E = 1
  · have hF : F = 1 := by simp [E, F, Complex.exp_neg, hE]
    have hz : qPochhammer z τ = 0 := by simpa [hE] using hsplit₁.symm
    have hnz : qPochhammer (-z) τ = 0 := by simpa [hF] using hsplit₂.symm
    simp [qTheta, hz, hnz, show τ - (z + τ) = -z by ring]
  · have hkey : qTheta (z + τ) τ * (1 - E) =
        (-F * qTheta z τ) * (1 - E) := by
      simp only [qTheta, show τ - (z + τ) = -z by ring]
      calc
        qPochhammer (z + τ) τ * qPochhammer (-z) τ * (1 - E) =
            ((1 - E) * qPochhammer (z + τ) τ) * qPochhammer (-z) τ := by ring
        _ = qPochhammer z τ * qPochhammer (-z) τ := by rw [hsplit₁]
        _ = qPochhammer z τ * ((1 - F) * qPochhammer (τ - z) τ) := by rw [hsplit₂]
        _ = (-F * (qPochhammer z τ * qPochhammer (τ - z) τ)) * (1 - E) := by
          rw [hfactor]; ring
    exact mul_right_cancel₀ (sub_ne_zero.mpr (Ne.symm hE)) hkey

/-- Every point of `ℤ + ℤτ` is a theta zero; used by `qTheta_eq_zero_iff`. -/
private lemma qTheta_intCast_add_intCast_mul_eq_zero (m n : ℤ) (τ : ℂ) :
    qTheta (m + n * τ) τ = 0 := by
  by_cases hn : n ≤ 0
  · have hj : (((-n).toNat : ℕ) : ℂ) = -(n : ℂ) := by
      exact_mod_cast (Int.toNat_of_nonneg (neg_nonneg.mpr hn))
    have hz := qPochhammer_intCast_sub_natCast_mul_eq_zero m (-n).toNat τ
    have hz' : qPochhammer ((m : ℂ) + (n : ℂ) * τ) τ = 0 := by
      simpa [hj] using hz
    simp [qTheta, hz']
  · have hn' : 0 ≤ n - 1 := by omega
    have hj : ((((n - 1).toNat : ℕ) : ℂ)) = (n : ℂ) - 1 := by
      exact_mod_cast (Int.toNat_of_nonneg hn')
    have harg : τ - ((m : ℂ) + (n : ℂ) * τ) =
        ((-m : ℤ) : ℂ) - (((n - 1).toNat : ℕ) : ℂ) * τ := by
      rw [hj]
      push_cast
      ring
    have hz := qPochhammer_intCast_sub_natCast_mul_eq_zero (-m) (n - 1).toNat τ
    rw [qTheta, harg, hz, mul_zero]

/-- For `Im τ > 0`, `θ(z,τ)` vanishes exactly on the lattice `ℤ + ℤτ`. -/
theorem qTheta_eq_zero_iff (z τ : ℂ) (hτ : 0 < τ.im) :
    qTheta z τ = 0 ↔ ∃ m n : ℤ, z = m + n * τ := by
  constructor
  · intro hz
    rcases (mul_eq_zero.mp hz) with hfirst | hsecond
    · obtain ⟨j, k, hjk⟩ := (qPochhammer_eq_zero_iff z τ hτ).mp hfirst
      refine ⟨k, -(j : ℤ), ?_⟩
      rw [hjk]
      push_cast
      ring
    · obtain ⟨j, k, hjk⟩ := (qPochhammer_eq_zero_iff (τ - z) τ hτ).mp hsecond
      refine ⟨-k, (j : ℤ) + 1, ?_⟩
      push_cast
      linear_combination -hjk
  · rintro ⟨m, n, rfl⟩
    exact qTheta_intCast_add_intCast_mul_eq_zero m n τ

/-- For `Im τ > 0`, `θ(z,τ)` is continuous in `z`. -/
theorem continuous_qTheta (τ : ℂ) (hτ : 0 < τ.im) : Continuous fun z => qTheta z τ := by
  unfold qTheta
  exact (qPochhammer_continuous τ hτ).mul
    ((qPochhammer_continuous τ hτ).comp (by fun_prop))

/-- `θ(u,τ)` has a simple zero at `u = 0`: `θ(u,τ)/u → -2πi ϖ(τ,τ)²` as `u → 0`, and the limit
is nonzero for `Im τ > 0`. -/
theorem tendsto_qTheta_div_self (τ : ℂ) (hτ : 0 < τ.im) :
    Tendsto (fun u => qTheta u τ / u) (𝓝[≠] 0) (𝓝 (-2 * π * I * qPochhammer τ τ ^ 2)) := by
  have hlin : HasDerivAt (fun u : ℂ => (2 * π * I) * u) (2 * π * I) 0 := by
    convert (hasDerivAt_id (0 : ℂ)).const_mul (2 * π * I) using 1 <;> simp
  have hderiv : HasDerivAt (fun u : ℂ => 1 - Complex.exp (2 * π * I * u))
      (-(2 * π * I)) 0 := by
    convert ((Complex.hasDerivAt_exp ((2 * π * I) * 0)).comp 0 hlin).const_sub 1
      using 1 <;> simp
  have hslope : Tendsto (fun u : ℂ => (1 - Complex.exp (2 * π * I * u)) / u)
      (𝓝[≠] 0) (𝓝 (-(2 * π * I))) := by
    simpa [div_eq_mul_inv, mul_comm] using hderiv.tendsto_slope_zero
  have htail : Tendsto (fun u : ℂ =>
      qPochhammer (u + τ) τ * qPochhammer (τ - u) τ) (𝓝[≠] 0)
      (𝓝 (qPochhammer τ τ ^ 2)) := by
    have hcont : Continuous (fun u : ℂ =>
        qPochhammer (u + τ) τ * qPochhammer (τ - u) τ) :=
      ((qPochhammer_continuous τ hτ).comp (by fun_prop)).mul
        ((qPochhammer_continuous τ hτ).comp (by fun_prop))
    simpa [pow_two] using (hcont.tendsto 0).mono_left
      (show 𝓝[≠] (0 : ℂ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hsplit (u : ℂ) :
      (1 - Complex.exp (2 * π * I * u)) * qPochhammer (u + τ) τ =
        qPochhammer u τ := by
    simpa [qPochhammerFin_one] using
      qPochhammerFin_natCast_mul_qPochhammer_add 1 u τ hτ
  convert (hslope.mul htail) using 1
  · ext u
    rw [qTheta, div_eq_mul_inv, ← hsplit u]
    ring
  · ring_nf

/-! ### Bounds

Periodicity in `Re z` reduces both bounds to compact subsets of a strip, where `θ` is
continuous, and nonzero away from the lattice. -/

/-- For `Im τ > 0`, `θ(z,τ)` is bounded on every closed horizontal strip `A ≤ Im z ≤ B`. -/
theorem exists_norm_qTheta_le (τ : ℂ) (hτ : 0 < τ.im) (A B : ℝ) :
    ∃ C, ∀ z : ℂ, A ≤ z.im → z.im ≤ B → ‖qTheta z τ‖ ≤ C := by
  let K : Set ℂ := Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc A B
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (continuous_qTheta τ hτ).continuousOn
  refine ⟨C, ?_⟩
  intro z hA hB
  obtain ⟨k, hre0, hre1, him⟩ := exists_intCast_sub_re_mem_Icc z
  have hθ : qTheta (z - k) τ = qTheta z τ := by
    simpa [sub_eq_add_neg] using qTheta_add_intCast z τ (-k)
  have hmem : z - (k : ℂ) ∈ K := by
    change (z - (k : ℂ)).re ∈ Set.Icc (0 : ℝ) 1 ∧
      (z - (k : ℂ)).im ∈ Set.Icc A B
    exact ⟨⟨hre0, hre1⟩, by rw [him]; exact ⟨hA, hB⟩⟩
  rw [← hθ]
  exact hC _ hmem

/-- The integer reduction in `exists_pos_le_norm_qTheta` preserves distance from
every lattice point. -/
private lemma qTheta_exists_reduced_dist (z τ : ℂ) (δ : ℝ)
    (h0 : 0 ≤ z.im) (h1 : z.im ≤ τ.im)
    (hdist : ∀ m n : ℤ, δ ≤ ‖z - (m + n * τ)‖) :
    ∃ w : ℂ, 0 ≤ w.re ∧ w.re ≤ 1 ∧ 0 ≤ w.im ∧ w.im ≤ τ.im ∧
      (∀ m n : ℤ, δ ≤ ‖w - (m + n * τ)‖) ∧ qTheta w τ = qTheta z τ := by
  obtain ⟨k, hr0, hr1, hi⟩ := exists_intCast_sub_re_mem_Icc z
  have hθ : qTheta (z - k) τ = qTheta z τ := by
    simpa [sub_eq_add_neg] using qTheta_add_intCast z τ (-k)
  refine ⟨z - k, hr0, hr1, ?_, ?_, ?_, hθ⟩
  · rwa [hi]
  · rwa [hi]
  · intro m n
    calc
      δ ≤ ‖z - (((m + k : ℤ) : ℂ) + (n : ℂ) * τ)‖ := hdist (m + k) n
      _ = ‖(z - (k : ℂ)) - ((m : ℂ) + (n : ℂ) * τ)‖ := by
        congr 1
        push_cast
        ring

/-- The reduced strip away from the lattice is compact; used by
`exists_pos_le_norm_qTheta`. -/
private lemma qTheta_compact_reduced_dist (τ : ℂ) (δ : ℝ) :
    IsCompact {w : ℂ | w ∈ (Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc 0 τ.im) ∧
      ∀ m n : ℤ, δ ≤ ‖w - (m + n * τ)‖} := by
  have hclosed : IsClosed {w : ℂ | ∀ m n : ℤ, δ ≤ ‖w - (m + n * τ)‖} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun m => isClosed_iInter (fun n =>
      isClosed_le continuous_const (by fun_prop)))
  exact (isCompact_Icc.reProdIm isCompact_Icc).of_isClosed_subset
    ((isClosed_Icc.reProdIm isClosed_Icc).inter hclosed) (fun _ hw => hw.1)

/-- For `Im τ > 0` and `δ > 0`, `‖θ(z,τ)‖` is bounded below by a positive constant on the strip
`0 ≤ Im z ≤ Im τ` at distance at least `δ` from the lattice `ℤ + ℤτ`. -/
theorem exists_pos_le_norm_qTheta (τ : ℂ) (hτ : 0 < τ.im) (δ : ℝ) (hδ : 0 < δ) :
    ∃ c > 0, ∀ z : ℂ, 0 ≤ z.im → z.im ≤ τ.im →
      (∀ m n : ℤ, δ ≤ ‖z - (m + n * τ)‖) → c ≤ ‖qTheta z τ‖ := by
  let S : Set ℂ := {w | w ∈ (Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc 0 τ.im) ∧
    ∀ m n : ℤ, δ ≤ ‖w - (m + n * τ)‖}
  have hS : IsCompact S := qTheta_compact_reduced_dist τ δ
  have hreduce (z : ℂ) (h0 : 0 ≤ z.im) (h1 : z.im ≤ τ.im)
      (hd : ∀ m n : ℤ, δ ≤ ‖z - (m + n * τ)‖) :
      ∃ w ∈ S, qTheta w τ = qTheta z τ := by
    obtain ⟨w, hr0, hr1, hi0, hi1, hw, hθ⟩ :=
      qTheta_exists_reduced_dist z τ δ h0 h1 hd
    exact ⟨w, ⟨⟨⟨hr0, hr1⟩, ⟨hi0, hi1⟩⟩, hw⟩, hθ⟩
  by_cases hne : S.Nonempty
  · obtain ⟨w, hw, hmin⟩ := hS.exists_isMinOn hne
      (continuous_qTheta τ hτ).norm.continuousOn
    have hwne : qTheta w τ ≠ 0 := by
      intro hz
      obtain ⟨m, n, hmn⟩ := (qTheta_eq_zero_iff w τ hτ).mp hz
      have hd := hw.2 m n
      rw [hmn, sub_self, norm_zero] at hd
      exact (not_le_of_gt hδ) hd
    refine ⟨‖qTheta w τ‖, norm_pos_iff.mpr hwne, ?_⟩
    intro z h0 h1 hd
    obtain ⟨v, hv, hθ⟩ := hreduce z h0 h1 hd
    rw [← hθ]
    exact hmin hv
  · refine ⟨1, by norm_num, ?_⟩
    intro z h0 h1 hd
    obtain ⟨w, hw, _⟩ := hreduce z h0 h1 hd
    exact (hne ⟨w, hw⟩).elim

/-! ### Gaussian growth

Under `u ↦ u + τ` the norm of `θ` gains the factor `exp(2π Im u)`, and so does the Gaussian
`exp(π (Im u)²/Im τ - π Im u)`. Their quotient is therefore invariant under `ℤ + ℤτ`.
Strip bounds control this normalized norm everywhere and away from the lattice. -/

/-- An imaginary shift places a point in one period strip and preserves its distance from the
lattice. -/
private lemma qTheta_exists_shift_strip (z τ : ℂ) (hτ : 0 < τ.im) (δ : ℝ)
    (hd : ∀ m n : ℤ, δ ≤ ‖z - (m + n * τ)‖) :
    ∃ n : ℤ, 0 ≤ (z + n * τ).im ∧ (z + n * τ).im ≤ τ.im ∧
      ∀ m j : ℤ, δ ≤ ‖(z + n * τ) - (m + j * τ)‖ := by
  let n := ⌈-z.im / τ.im⌉
  have hlo : -z.im / τ.im ≤ (n : ℝ) := Int.le_ceil _
  have hhi : (n : ℝ) < -z.im / τ.im + 1 := Int.ceil_lt_add_one _
  have him : (z + (n : ℂ) * τ).im = z.im + (n : ℝ) * τ.im := by simp
  refine ⟨n, ?_, ?_, ?_⟩
  · rw [him]
    have := (div_le_iff₀ hτ).mp hlo
    nlinarith
  · rw [him]
    have := (lt_div_iff₀ hτ).mp (show (n : ℝ) - 1 < -z.im / τ.im by linarith)
    linarith
  · intro m j
    calc
      δ ≤ ‖z - ((m : ℂ) + ((j - n : ℤ) : ℂ) * τ)‖ := hd m (j - n)
      _ = ‖(z + (n : ℂ) * τ) - ((m : ℂ) + (j : ℂ) * τ)‖ := by
        congr 1
        push_cast
        ring

/-- The exponent `π (Im u)²/Im τ - π Im u` of the Gaussian growth of `θ(u,τ)`. -/
def qThetaGrowth (u τ : ℂ) : ℝ :=
  π * u.im ^ 2 / τ.im - π * u.im

/-- The Gaussian exponent under a shift: `Γ(u+a) - Γ(u) = 2π Im a Im u/Im τ + Γ(a)`, with
`Γ = qThetaGrowth`. -/
theorem qThetaGrowth_add (u a τ : ℂ) :
    qThetaGrowth (u + a) τ - qThetaGrowth u τ = 2 * π * a.im * u.im / τ.im + qThetaGrowth a τ := by
  unfold qThetaGrowth
  rw [Complex.add_im]
  ring

/-- One-period change of the Gaussian exponent; used by `norm_qTheta_add_self`. -/
private lemma qThetaGrowth_add_self (u τ : ℂ) (hτ : 0 < τ.im) :
    qThetaGrowth (u + τ) τ - qThetaGrowth u τ = 2 * π * u.im := by
  rw [qThetaGrowth_add]
  have hne : τ.im ≠ 0 := ne_of_gt hτ
  have hself : qThetaGrowth τ τ = 0 := by
    unfold qThetaGrowth
    field_simp [hne]
    ring
  rw [hself]
  field_simp [hne]
  ring

/-- The Gaussian-normalized theta norm `N_τ(u) = ‖θ(u,τ)‖ exp(-Γ_τ(u))`. -/
def qThetaNormalizedNorm (u τ : ℂ) : ℝ :=
  ‖qTheta u τ‖ * Real.exp (-qThetaGrowth u τ)

/-- The normalized theta norm is nonnegative. -/
theorem qThetaNormalizedNorm_nonneg (u τ : ℂ) : 0 ≤ qThetaNormalizedNorm u τ := by
  unfold qThetaNormalizedNorm
  positivity

/-- Integer translation preserves the normalized theta norm. -/
theorem qThetaNormalizedNorm_add_intCast (u τ : ℂ) (m : ℤ) :
    qThetaNormalizedNorm (u + m) τ = qThetaNormalizedNorm u τ := by
  simp [qThetaNormalizedNorm, qTheta_add_intCast, qThetaGrowth, Complex.add_im]

/-- The norm multiplier for one period, used by `norm_qTheta_add_intCast_mul`. -/
private lemma norm_qTheta_add_self (u τ : ℂ) (hτ : 0 < τ.im) :
    ‖qTheta (u + τ) τ‖ =
      Real.exp (qThetaGrowth (u + τ) τ - qThetaGrowth u τ) * ‖qTheta u τ‖ := by
  rw [qTheta_add_self u τ hτ, norm_mul, norm_neg, Complex.norm_exp,
    qThetaGrowth_add_self u τ hτ]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-- The normalized norm has period `τ`; used to obtain integer period shifts. -/
private lemma qThetaNormalizedNorm_periodic (τ : ℂ) (hτ : 0 < τ.im) :
    Function.Periodic (fun u => qThetaNormalizedNorm u τ) τ := by
  intro u
  change ‖qTheta (u + τ) τ‖ * Real.exp (-qThetaGrowth (u + τ) τ) =
    ‖qTheta u τ‖ * Real.exp (-qThetaGrowth u τ)
  rw [norm_qTheta_add_self u τ hτ]
  calc
    _ = ‖qTheta u τ‖ *
        (Real.exp (qThetaGrowth (u + τ) τ - qThetaGrowth u τ) *
          Real.exp (-qThetaGrowth (u + τ) τ)) := by ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      ring_nf

/-- The normalized theta norm is invariant under integer multiples of the period. -/
theorem qThetaNormalizedNorm_add_intCast_mul (u τ : ℂ) (hτ : 0 < τ.im) (n : ℤ) :
    qThetaNormalizedNorm (u + n * τ) τ = qThetaNormalizedNorm u τ := by
  exact ((qThetaNormalizedNorm_periodic τ hτ).int_mul n) u

/-- The normalized theta norm is invariant under the lattice `ℤ + ℤτ`. -/
theorem qThetaNormalizedNorm_lattice (u τ : ℂ) (hτ : 0 < τ.im) (m n : ℤ) :
    qThetaNormalizedNorm (u + (m + n * τ)) τ = qThetaNormalizedNorm u τ := by
  rw [show u + ((m : ℂ) + n * τ) = (u + m) + n * τ by ring,
    qThetaNormalizedNorm_add_intCast_mul _ τ hτ n, qThetaNormalizedNorm_add_intCast]

/-- Recover the theta norm from its Gaussian-normalized value. -/
theorem norm_qTheta_eq_normalized_mul_exp (u τ : ℂ) :
    ‖qTheta u τ‖ = qThetaNormalizedNorm u τ * Real.exp (qThetaGrowth u τ) := by
  rw [qThetaNormalizedNorm, mul_assoc, ← Real.exp_add]
  simp

/-- `‖θ(u+nτ,τ)‖ = exp(Γ(u+nτ) - Γ(u)) ‖θ(u,τ)‖` for `n ∈ ℤ`, with `Γ = qThetaGrowth`: the norm of
`θ` divided by its Gaussian is invariant under `u ↦ u + nτ`. -/
theorem norm_qTheta_add_intCast_mul (u τ : ℂ) (hτ : 0 < τ.im) (n : ℤ) :
    ‖qTheta (u + n * τ) τ‖ =
      Real.exp (qThetaGrowth (u + n * τ) τ - qThetaGrowth u τ) * ‖qTheta u τ‖ := by
  have h := qThetaNormalizedNorm_add_intCast_mul u τ hτ n
  calc
    ‖qTheta (u + n * τ) τ‖ = qThetaNormalizedNorm (u + n * τ) τ *
        Real.exp (qThetaGrowth (u + n * τ) τ) :=
      norm_qTheta_eq_normalized_mul_exp _ _
    _ = qThetaNormalizedNorm u τ * Real.exp (qThetaGrowth (u + n * τ) τ) := by
      rw [h]
    _ = Real.exp (qThetaGrowth (u + n * τ) τ - qThetaGrowth u τ) *
          ‖qTheta u τ‖ := by
      rw [norm_qTheta_eq_normalized_mul_exp u τ]
      have he : Real.exp (qThetaGrowth (u + n * τ) τ) =
          Real.exp (qThetaGrowth (u + n * τ) τ - qThetaGrowth u τ) *
            Real.exp (qThetaGrowth u τ) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [he]
      ring

/-- On one period strip, `-π Im τ/4 ≤ Γ(u) ≤ 0`; used by both Gaussian bounds. -/
private lemma qThetaGrowth_strip_bounds (u τ : ℂ) (hτ : 0 < τ.im)
    (h0 : 0 ≤ u.im) (h1 : u.im ≤ τ.im) :
    -(π * τ.im) / 4 ≤ qThetaGrowth u τ ∧ qThetaGrowth u τ ≤ 0 := by
  have hfirst : 0 ≤ π * (2 * u.im - τ.im) ^ 2 / (4 * τ.im) := by positivity
  have hformula_lower : qThetaGrowth u τ + π * τ.im / 4 =
      π * (2 * u.im - τ.im) ^ 2 / (4 * τ.im) := by
    unfold qThetaGrowth
    field_simp
    ring
  have hprod : 0 ≤ π * (u.im * (τ.im - u.im)) :=
    mul_nonneg Real.pi_nonneg (mul_nonneg h0 (sub_nonneg.mpr h1))
  have hformula : qThetaGrowth u τ = -(π * (u.im * (τ.im - u.im))) / τ.im := by
    unfold qThetaGrowth
    field_simp
    ring
  constructor
  · rw [← hformula_lower] at hfirst
    linarith
  · rw [hformula]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hprod) hτ.le

/-- A strip upper bound also bounds the Gaussian-normalized norm on that strip;
used by `exists_qThetaNormalizedNorm_le`. -/
private lemma qThetaNormalizedNorm_upper_strip (τ : ℂ) (hτ : 0 < τ.im)
    (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ τ.im → ‖qTheta z τ‖ ≤ C)
    (u : ℂ) (h0 : 0 ≤ u.im) (h1 : u.im ≤ τ.im) :
    qThetaNormalizedNorm u τ ≤ C * Real.exp (π * τ.im / 4) := by
  have hΓ := (qThetaGrowth_strip_bounds u τ hτ h0 h1).1
  calc
    qThetaNormalizedNorm u τ = Real.exp (-qThetaGrowth u τ) * ‖qTheta u τ‖ := by
      unfold qThetaNormalizedNorm
      ring
    _ ≤ Real.exp (-qThetaGrowth u τ) * C :=
      mul_le_mul_of_nonneg_left (hC u h0 h1) (Real.exp_pos _).le
    _ ≤ Real.exp (π * τ.im / 4) * C :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hC0
    _ = C * Real.exp (π * τ.im / 4) := mul_comm _ _

/-- For `Im τ > 0`, the Gaussian-normalized theta norm is bounded everywhere. -/
theorem exists_qThetaNormalizedNorm_le (τ : ℂ) (hτ : 0 < τ.im) :
    ∃ C ≥ 0, ∀ u : ℂ, qThetaNormalizedNorm u τ ≤ C := by
  obtain ⟨C, hC⟩ := exists_norm_qTheta_le τ hτ 0 τ.im
  have hC0 : 0 ≤ C :=
    (norm_nonneg (qTheta 0 τ)).trans (hC 0 (by simp) (by simpa using hτ.le))
  refine ⟨C * Real.exp (π * τ.im / 4),
    mul_nonneg hC0 (Real.exp_pos _).le, ?_⟩
  intro u
  obtain ⟨n, h0, h1, _⟩ := qTheta_exists_shift_strip u τ hτ 0
    (fun m j => norm_nonneg _)
  have hstrip := qThetaNormalizedNorm_upper_strip τ hτ C hC0 hC
    (u + n * τ) h0 h1
  rw [← qThetaNormalizedNorm_add_intCast_mul u τ hτ n]
  exact hstrip

/-- For `Im τ > 0`, `‖θ(u,τ)‖ ≤ C exp(π (Im u)²/Im τ - π Im u)` for every `u`. -/
theorem exists_norm_qTheta_le_exp (τ : ℂ) (hτ : 0 < τ.im) :
    ∃ C, ∀ u : ℂ, ‖qTheta u τ‖ ≤ C * Real.exp (qThetaGrowth u τ) := by
  obtain ⟨C, _, hC⟩ := exists_qThetaNormalizedNorm_le τ hτ
  refine ⟨C, fun u => ?_⟩
  rw [norm_qTheta_eq_normalized_mul_exp u τ]
  exact mul_le_mul_of_nonneg_right (hC u) (Real.exp_pos _).le

/-- A strip lower bound also bounds the Gaussian-normalized norm from below;
used by `exists_pos_le_qThetaNormalizedNorm`. -/
private lemma qThetaNormalizedNorm_lower_strip (τ : ℂ) (hτ : 0 < τ.im)
    (δ c : ℝ)
    (hc : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ τ.im →
      (∀ m n : ℤ, δ ≤ ‖z - (m + n * τ)‖) → c ≤ ‖qTheta z τ‖)
    (u : ℂ) (h0 : 0 ≤ u.im) (h1 : u.im ≤ τ.im)
    (hd : ∀ m n : ℤ, δ ≤ ‖u - (m + n * τ)‖) :
    c ≤ qThetaNormalizedNorm u τ := by
  have hΓ := (qThetaGrowth_strip_bounds u τ hτ h0 h1).2
  calc
    c ≤ ‖qTheta u τ‖ := hc u h0 h1 hd
    _ = 1 * ‖qTheta u τ‖ := (one_mul _).symm
    _ ≤ Real.exp (-qThetaGrowth u τ) * ‖qTheta u τ‖ :=
      mul_le_mul_of_nonneg_right (Real.one_le_exp_iff.mpr (by linarith)) (norm_nonneg _)
    _ = qThetaNormalizedNorm u τ := by unfold qThetaNormalizedNorm; ring

/-- Away from the lattice `ℤ + ℤτ`, the normalized theta norm has a positive lower bound. -/
theorem exists_pos_le_qThetaNormalizedNorm (τ : ℂ) (hτ : 0 < τ.im)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ c > 0, ∀ u : ℂ, (∀ m n : ℤ, δ ≤ ‖u - (m + n * τ)‖) →
      c ≤ qThetaNormalizedNorm u τ := by
  obtain ⟨c, hc, hbelow⟩ := exists_pos_le_norm_qTheta τ hτ δ hδ
  refine ⟨c, hc, ?_⟩
  intro u hd
  obtain ⟨n, h0, h1, hd'⟩ := qTheta_exists_shift_strip u τ hτ δ hd
  have hstrip := qThetaNormalizedNorm_lower_strip τ hτ δ c hbelow
    (u + n * τ) h0 h1 hd'
  rw [← qThetaNormalizedNorm_add_intCast_mul u τ hτ n]
  exact hstrip

/-- For `Im τ > 0` and `δ > 0`, `‖θ(u,τ)‖ ≥ c exp(π (Im u)²/Im τ - π Im u)` with `c > 0` at
distance at least `δ` from the lattice `ℤ + ℤτ`. -/
theorem exists_exp_le_norm_qTheta (τ : ℂ) (hτ : 0 < τ.im) (δ : ℝ) (hδ : 0 < δ) :
    ∃ c > 0, ∀ u : ℂ, (∀ m n : ℤ, δ ≤ ‖u - (m + n * τ)‖) →
      c * Real.exp (qThetaGrowth u τ) ≤ ‖qTheta u τ‖ := by
  obtain ⟨c, hc, hC⟩ := exists_pos_le_qThetaNormalizedNorm τ hτ δ hδ
  refine ⟨c, hc, fun u hd => ?_⟩
  rw [norm_qTheta_eq_normalized_mul_exp u τ]
  exact mul_le_mul_of_nonneg_right (hC u hd) (Real.exp_pos _).le

/-- A comparison of normalized theta norms gives the corresponding Gaussian norm comparison. -/
theorem norm_qTheta_le_of_normalized_le (x σ y τ : ℂ) (C : ℝ)
    (h : qThetaNormalizedNorm x σ ≤ C * qThetaNormalizedNorm y τ) :
    ‖qTheta x σ‖ ≤
      C * Real.exp (qThetaGrowth x σ - qThetaGrowth y τ) * ‖qTheta y τ‖ := by
  have h' := mul_le_mul_of_nonneg_right h
    (le_of_lt (Real.exp_pos (qThetaGrowth x σ)))
  calc
    ‖qTheta x σ‖ = qThetaNormalizedNorm x σ * Real.exp (qThetaGrowth x σ) :=
      norm_qTheta_eq_normalized_mul_exp x σ
    _ ≤ (C * qThetaNormalizedNorm y τ) * Real.exp (qThetaGrowth x σ) := h'
    _ = C * ‖qTheta y τ‖ *
        (Real.exp (-qThetaGrowth y τ) * Real.exp (qThetaGrowth x σ)) := by
      simp only [qThetaNormalizedNorm]
      ring
    _ = C * Real.exp (qThetaGrowth x σ - qThetaGrowth y τ) * ‖qTheta y τ‖ := by
      rw [← Real.exp_add, show -qThetaGrowth y τ + qThetaGrowth x σ =
        qThetaGrowth x σ - qThetaGrowth y τ by ring]
      ring

end SIC
