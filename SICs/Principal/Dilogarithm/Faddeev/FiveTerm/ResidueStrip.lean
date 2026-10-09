/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.ResidueStripBounds
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.ClassWindow

/-!
# The principal residue strip

The kernel poles, meromorphic orders, grouped residues, and horizontal tails of the residue sum on
a strip between two vertical lines at distance `(ε-1)/c`.

This module follows the residue step of [RW26, Radchenko, Wheeler (2026), Section 3.2, the proof
of Theorem 2, `thm:fg.equs`], at `γ = A_d`, `τ = ρ_d`, `ε = ρ_d³`, `c = d(d-2)`, `H = d(d-3)`.
It supplies the inputs of the residue theorem on rectangles of `SICs.Analysis.RectangleResidues`,
which `SICs.Principal.Dilogarithm.Faddeev.FiveTerm.CrossedStrip` applies to the strip.

## The argument

On the common line, the kernel poles of `L(z) = ∑_m K̃_m(z - mε/c)` lie at
`z_x + x₁ε/c = -(ε-1)S_d(x)/(cH)`, so a strip of width `(ε-1)/c` contains the poles of a window of
`H` consecutive lattice indices. Away from the zeros of the pole factor, the meromorphic order of
each summand is the order of its numerator minus that of its denominator, and the zeros of
`Φ_{m+p,0}(z+y)` lie left of `-(m+p)ε/c - y`. Where every summand has nonnegative order, the
totalized sum is bounded on a punctured neighborhood, so such points of a compact rectangle are
removable. The residues of `L` at one pole position are grouped, contour index by contour index,
into fibers over the window. The horizontal sides of a rectangle of height `2Y` vanish as
`Y → ∞` by the sector bounds, and reindexing by the lattice translation carries regular crossings
of the left line to the translated right line.
-/

noncomputable section

open Complex Filter Set
open scoped Topology

namespace SIC

/-! ### Kernel poles on the common line -/

/-- The algebra relating the lattice rate and the position of a strip pole. -/
private lemma principalFiveTerm_strip_position_algebra (ε c H D z m S : ℝ)
    (hc : c ≠ 0) (hH : H ≠ 0) (he : ε - 1 ≠ 0)
    (hq : (ε - 1) ^ 2 = D * H * ε)
    (hb : (c * z + m * ε) * (ε - 1) = -D * S * ε) :
    z + m * ε / c = -(ε - 1) * S / (c * H) := by
  have hqS := congrArg (fun t : ℝ => t * S) hq
  have hbH := congrArg (fun t : ℝ => t * H) hb
  have hz : (H * (c * z + m * ε) + (ε - 1) * S) * (ε - 1) = 0 := by
    nlinarith [hqS, hbH]
  have hz' := (mul_eq_zero.mp hz).resolve_right he
  field_simp [hc, hH]
  nlinarith [hz']

/-- Clears the denominators in `principalFiveTermLatticeArgument_baseRate`. -/
private lemma principalFiveTerm_strip_base_algebra (ε c D z m S : ℝ) (hε : ε ≠ 0)
    (he : ε - 1 ≠ 0) (hb : c * z / ε + m = -(D * S / (ε - 1))) :
    (c * z + m * ε) * (ε - 1) = -D * S * ε := by
  calc
    _ = (c * z / ε + m) * ε * (ε - 1) := by
      congr 1
      calc
        _ = (c * z / ε) * ε + m * ε := by rw [div_mul_cancel₀ _ hε]
        _ = _ := by ring
    _ = _ := by
      rw [hb]
      calc
        _ = -(D * S / (ε - 1)) * (ε - 1) * ε := by ring
        _ = _ := by rw [neg_mul, div_mul_cancel₀ _ he]; ring

/-- On the common line the kernel pole of the pair `x = (m, k)` sits at
`z_x + mε/c = -(ε-1)S_d(x)/(cH)`: from `principalFiveTermLatticeArgument_baseRate`,
`principalFiveTermLatticeRate_eq_index`, and `(ε-1)² = Nε`
(`principalJacobiFactor_add_inv`). -/
theorem principalFiveTermLatticeArgument_add_mul_eq (d : ℕ) (hd : 3 < d) (m k : ℤ) :
    principalFiveTermLatticeArgument d m k +
        (m : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ) =
      -(principalRoot d ^ 3 - 1) * (principalFiveTermLatticeIndex d m k : ℝ) /
        (((principalA d) 1 0 : ℝ) * (principalFiveTermUpperIndexBound d : ℝ)) := by
  have hc₀ : ((principalA d) 1 0 : ℝ) = (d : ℝ) * ((d : ℝ) - 2) := by
    simp [coe_principalA]
  have hH₀ : (principalFiveTermUpperIndexBound d : ℝ) =
      (d : ℝ) * ((d : ℝ) - 3) := by
    simp [principalFiveTermUpperIndexBound]
  rw [hc₀, hH₀]
  have hd3 : (3 : ℝ) < d := by exact_mod_cast hd
  have hc : (d : ℝ) * ((d : ℝ) - 2) ≠ 0 := by nlinarith
  have hH : (d : ℝ) * ((d : ℝ) - 3) ≠ 0 := by nlinarith
  have hε : principalRoot d ^ 3 ≠ 0 := (pow_pos (principalRoot_pos d hd) _).ne'
  have he : principalRoot d ^ 3 - 1 ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr (one_lt_principalRoot_pow_three d hd))
  have hq : (principalRoot d ^ 3 - 1) ^ 2 =
      (d : ℝ) * ((d : ℝ) * ((d : ℝ) - 3)) * principalRoot d ^ 3 := by
    rw [principalRoot_pow_three_sub_one_sq d hd, cast_principalDilogOrder_eq d hd]
    ring
  have hb := principalFiveTermLatticeArgument_baseRate d hd m k
  rw [principalFiveTermLatticeRate_eq_index] at hb
  exact principalFiveTerm_strip_position_algebra _ _ _ _ _ _ _ hc hH he hq
    (principalFiveTerm_strip_base_algebra _ _ _ _ _ _ hε he hb)

/-! ### Meromorphic orders

Each summand of `L` is meromorphic. Away from the zeros of the pole factor its order is the
numerator order minus the denominator order, and the shifted denominator has no zero right of
`-(m+p)ε/c-y`. -/

/-- Each summand of the residue sum is meromorphic. -/
theorem meromorphic_principalFiveTermResidueKernel (d : ℕ) (hd : 3 < d) (ℓ p : ℤ) (w y : ℝ)
    (m : ℤ) : Meromorphic (principalFiveTermResidueKernel d ℓ p w y m) := by
  intro z
  unfold principalFiveTermResidueKernel principalFiveTermKernel
  unfold principalFiveTermPoleFactor principalFiveTermPhase
  apply MeromorphicAt.div
  · apply MeromorphicAt.mul
    · apply MeromorphicAt.mul
      · apply MeromorphicAt.div
        · exact meromorphicAt_principalFaddeev d hd (m + 1) 0 z
        · have hcomp : MeromorphicAt
              (principalFaddeev d (m + p) 0 ∘ (fun ζ : ℂ => ζ + (y : ℂ))) z :=
            (meromorphicAt_principalFaddeev d hd (m + p) 0
              ((fun ζ : ℂ => ζ + (y : ℂ)) z)).comp_analyticAt
                (g := fun ζ : ℂ => ζ + (y : ℂ))
                (show AnalyticAt ℂ (fun ζ : ℂ => ζ + (y : ℂ)) z by fun_prop)
          simpa only [Function.comp_def] using hcomp
      · exact (by fun_prop : AnalyticAt ℂ
          (fun z : ℂ => Complex.exp (2 * Real.pi * I *
            ((((d : ℂ) * ((d : ℂ) - 2) * z + (principalRoot d : ℂ) ^ 3 * m) * w) /
            (principalRoot d : ℂ) ^ 3 + ℓ * (z + m * (principalRoot d : ℂ))))) z).meromorphicAt
    · exact (by fun_prop : AnalyticAt ℂ
        (fun z : ℂ => 1 - Complex.exp (2 * Real.pi * I *
          (z + m * (principalRoot d : ℂ)))) z).meromorphicAt
  · fun_prop

/-- The principal unit satisfies $cρ_d+1-d=ε$; used by the strip divisor bounds. -/
private lemma eps_linear (d : ℕ) (hd : 3 < d) :
    ((principalA d) 1 0 : ℝ) * principalRoot d + 1 - d = principalRoot d ^ 3 := by
  simpa [coe_principalA, sub_eq_add_neg, add_assoc] using
    (principalRoot_pow_three_eq d hd).symm
/-- A zero of $Φ_{m,0}$ lies strictly left of $-mε/c$. -/
private lemma zero_re_bound (d : ℕ) (hd : 3 < d) (m k l : ℤ)
    (hK : k + m ≤ 0)
    (hL : 0 < (1 - (d : ℤ)) * k - (d : ℤ) * ((d : ℤ) - 2) * l) :
    (k : ℝ) * principalRoot d + l <
      (-(m : ℝ)) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ) := by
  have hc : 0 < ((principalA d) 1 0 : ℝ) := by exact_mod_cast principalA_lowerLeft_pos d hd
  have he : 0 < principalRoot d ^ 3 := pow_pos (principalRoot_pos d hd) _
  have hJ := eps_linear d hd
  have hKr : (k : ℝ) ≤ -(m : ℝ) := by
    have hKi : k ≤ -m := by omega
    exact_mod_cast hKi
  have hLr : ((principalA d) 1 0 : ℝ) * l < (1 - (d : ℝ)) * k := by
    have hLr' : (0 : ℝ) < (1 - (d : ℝ)) * k -
        (d : ℝ) * ((d : ℝ) - 2) * l := by exact_mod_cast hL
    rw [show ((principalA d) 1 0 : ℝ) = (d : ℝ) * ((d : ℝ) - 2) by
      simp [coe_principalA]]
    linarith
  apply (lt_div_iff₀ hc).2
  have hJk := congrArg (fun t : ℝ => t * (k : ℝ)) hJ
  have hmul : 0 ≤ (-(m : ℝ) - (k : ℝ)) * principalRoot d ^ 3 :=
    mul_nonneg (sub_nonneg.mpr hKr) he.le
  nlinarith [hJk, hmul]
/-- The shifted denominator $Φ_{m+p,0}(ζ+y)$ has no zero on or right of $-(m+p)ε/c-y$. -/
lemma meromorphicOrderAt_principalFaddeev_add_nonpos (d : ℕ) (hd : 3 < d) (m p : ℤ) (y : ℝ)
    (ζ : ℂ) (hζ : (-(m + p : ℤ) : ℝ) * principalRoot d ^ 3 /
      ((principalA d) 1 0 : ℝ) - y ≤ ζ.re) :
    meromorphicOrderAt (fun z : ℂ => principalFaddeev d (m + p) 0 (z + y)) ζ ≤ 0 := by
  rw [meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt]
  by_cases hlat : IsPeriodLatticePoint (principalRoot d : ℂ) (ζ + y)
  · rcases hlat with ⟨l, k, hk⟩
    apply le_of_not_gt
    intro hpos
    rw [hk] at hpos
    have hpos' : 0 < meromorphicOrderAt (principalFaddeev d (m + p) 0)
        ((k : ℂ) * (principalRoot d : ℂ) + l) := by
      simpa only [add_comm] using hpos
    obtain ⟨hK, hL⟩ :=
      (meromorphicOrderAt_principalFaddeev_pos_iff d hd (m + p) 0 k l).mp hpos'
    have hb := zero_re_bound d hd (m + p) k l hK (by simpa using hL)
    have hre : (ζ + (y : ℂ)).re = ζ.re + y := by simp
    have hre' : (((l : ℂ) + (k : ℂ) * (principalRoot d : ℂ)).re) =
        (k : ℝ) * principalRoot d + l := by simp [Complex.mul_re, add_comm]
    rw [hk, hre'] at hre
    linarith
  · rw [meromorphicOrderAt_principalFaddeev_eq_zero
      d hd (m + p) 0 (ζ + y) hlat]
/-- Away from pole factor zeros, the kernel order is the numerator order minus the
denominator order. -/
lemma meromorphicOrderAt_principalFiveTermResidueKernel (d : ℕ) (hd : 3 < d)
    (ℓ m p : ℤ) (w y : ℝ)
    (ζ : ℂ) (hζ : ∀ k : ℤ, ζ ≠ principalFiveTermLatticeArgument d m k) :
    meromorphicOrderAt (principalFiveTermResidueKernel d ℓ p w y m) ζ =
      meromorphicOrderAt (principalFaddeev d m 0) ζ -
        meromorphicOrderAt (fun z : ℂ => principalFaddeev d (m + p) 0 (z + y)) ζ := by
  let N : ℂ → ℂ := principalFaddeev d m 0
  let D : ℂ → ℂ := fun z => principalFaddeev d (m + p) 0 (z + y)
  let P : ℂ → ℂ := principalFiveTermPoleFactor d m
  let E : ℂ → ℂ := fun z => Complex.exp (2 * Real.pi * I * principalFiveTermPhase d ℓ w m z)
  have hN : MeromorphicAt N ζ := meromorphicAt_principalFaddeev d hd m 0 ζ
  have hD : MeromorphicAt D ζ := by
    have h := (meromorphicAt_principalFaddeev d hd (m + p) 0 (ζ + y)).comp_analyticAt
      (g := fun z : ℂ => z + (y : ℂ))
      (show AnalyticAt ℂ (fun z : ℂ => z + (y : ℂ)) ζ by fun_prop)
    simpa only [Function.comp_def] using h
  have hP : AnalyticAt ℂ P ζ := by unfold P principalFiveTermPoleFactor; fun_prop
  have hE : AnalyticAt ℂ E ζ := by dsimp [E, principalFiveTermPhase]; fun_prop
  have hPne : P ζ ≠ 0 := by
    intro hz
    obtain ⟨k, hk⟩ := (principalFiveTermPoleFactor_eq_zero_iff d hd m ζ).mp hz
    exact hζ k hk
  have hEne : E ζ ≠ 0 := Complex.exp_ne_zero _
  have hPord : meromorphicOrderAt P ζ = 0 := by
    simp [hP.meromorphicOrderAt_eq, (hP.analyticOrderAt_eq_zero).mpr hPne]
  have hEord : meromorphicOrderAt E ζ = 0 := by
    simp [hE.meromorphicOrderAt_eq, (hE.analyticOrderAt_eq_zero).mpr hEne]
  rw [meromorphicOrderAt_congr (principalFiveTermResidueKernel_eventuallyEq d hd ℓ p w y m ζ)]
  change meromorphicOrderAt ((N / D * E) / P) ζ =
    meromorphicOrderAt N ζ - meromorphicOrderAt D ζ
  rw [meromorphicOrderAt_div ((hN.div hD).mul hE.meromorphicAt) hP.meromorphicAt,
    meromorphicOrderAt_mul (hN.div hD) hE.meromorphicAt,
    meromorphicOrderAt_div hN hD, hPord, hEord]
  simp

/-! ### Inputs of the rectangle argument

The residue theorem on `[x, x + (ε-1)/c] × [-Y, Y]` for `L` uses its meromorphy, boundedness at
removable points, the residues grouped by pole position, and the vanishing of the horizontal sides
as `Y → ∞`. -/

/-- The finite common-line sum of residue kernels is meromorphic; used by the rectangle
argument. -/
theorem meromorphic_principalFiveTermResidueSum (d : ℕ) (hd : 3 < d)
    (ℓ p : ℤ) (w y : ℝ) : Meromorphic (principalFiveTermResidueSum d ℓ p w y) := by
  intro z
  unfold principalFiveTermResidueSum
  apply MeromorphicAt.fun_sum
  intro m _
  let c : ℂ := ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
    ((principalA d) 1 0 : ℂ)
  have h := (meromorphic_principalFiveTermResidueKernel d hd ℓ p w y
    ((m : ℕ) : ℤ) (z - c)).comp_analyticAt
    (g := fun ζ : ℂ => ζ - c)
    (show AnalyticAt ℂ (fun ζ : ℂ => ζ - c) z by fun_prop)
  simpa only [Function.comp_def, c] using h

/-- If every shifted summand has nonnegative order at a point, the common-line sum is bounded
on a punctured neighborhood; used for removable points on the rectangle. -/
lemma principalFiveTermResidueSum_bdd_of_order_nonneg (d : ℕ) (hd : 3 < d)
    (ℓ p : ℤ) (w y : ℝ) (z : ℂ)
    (horder : ∀ m : FiveTermIndex (principalA d),
      0 ≤ meromorphicOrderAt
        (fun ζ => principalFiveTermResidueKernel d ℓ p w y ((m : ℕ) : ℤ)
          (ζ - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
            ((principalA d) 1 0 : ℂ))) z) :
    IsBoundedUnder (· ≤ ·) (𝓝[≠] z)
      (fun ζ => ‖principalFiveTermResidueSum d ℓ p w y ζ‖) := by
  let F (m : FiveTermIndex (principalA d)) (ζ : ℂ) :=
    principalFiveTermResidueKernel d ℓ p w y ((m : ℕ) : ℤ)
      (ζ - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
        ((principalA d) 1 0 : ℂ))
  have hterm (m : FiveTermIndex (principalA d)) : MeromorphicAt (F m) z := by
    exact (meromorphicAt_comp_sub_const_iff_meromorphicAt).2
      (meromorphic_principalFiveTermResidueKernel d hd ℓ p w y ((m : ℕ) : ℤ) _)
  have hlim (m : FiveTermIndex (principalA d)) :
      ∃ c : ℂ, Tendsto (F m) (𝓝[≠] z) (𝓝 c) :=
    tendsto_nhds_of_meromorphicOrderAt_nonneg (hterm m) (horder m)
  choose c hc using hlim
  have hsum := tendsto_finsetSum Finset.univ (fun m _ => hc m)
  have hsum' : Tendsto (principalFiveTermResidueSum d ℓ p w y)
      (𝓝[≠] z) (𝓝 (∑ m : FiveTermIndex (principalA d), c m)) := by
    exact hsum
  exact hsum'.norm.isBoundedUnder_le

/-- The translated real position of the kernel pole indexed by $(m,k)$. -/
def principalFiveTermStripPolePosition (d : ℕ) (m k : ℤ) : ℂ :=
  (principalFiveTermLatticeArgument d m k +
    (m : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ) : ℝ)

/-- For a fixed first index, distinct second indices give distinct common-line poles. -/
lemma principalFiveTermStripPolePosition_injective (d : ℕ) (hd : 3 < d)
    (m : ℤ) : Function.Injective (principalFiveTermStripPolePosition d m) := by
  intro k l hkl
  have hδ : (principalRoot d ^ 3)⁻¹ - 1 ≠ 0 := by
    have hε : 1 < principalRoot d ^ 3 :=
      one_lt_principalRoot_pow_three d hd
    exact ne_of_lt (sub_neg.mpr ((inv_lt_one₀ (by positivity)).2 hε))
  have hr : principalFiveTermLatticeArgument d m k =
      principalFiveTermLatticeArgument d m l := by
    have h := congrArg Complex.re hkl
    simp only [principalFiveTermStripPolePosition, Complex.ofReal_re] at h
    linarith
  unfold principalFiveTermLatticeArgument at hr
  have hk : (k : ℝ) = (l : ℝ) := by
    apply (div_left_inj' hδ).mp at hr
    linarith
  exact_mod_cast hk

/-- Every finite summation index lies in the principal window's first-coordinate range. -/
lemma principalFiveTermIndex_range (d : ℕ) (hd : 3 < d)
    (m : FiveTermIndex (principalA d)) :
    0 ≤ (((m : ℕ) : ℤ)) ∧ (((m : ℕ) : ℤ)) < (d : ℤ) * ((d : ℤ) - 2) := by
  have hc := principalA_lowerLeft_pos d hd
  constructor
  · exact_mod_cast Nat.zero_le m.val
  · have hm' : (((m : ℕ) : ℤ)) < (((principalA d) 1 0).toNat : ℤ) := by
      exact_mod_cast m.isLt
    rw [Int.toNat_of_nonneg hc.le] at hm'
    simpa [coe_principalA] using hm'

/-- Translating a kernel translates its lattice-pole residue limit to the common line. -/
lemma tendsto_sub_mul_principalFiveTermResidueKernel_sub (d : ℕ) (hd : 3 < d)
    (ℓ : ℤ) (w : ℝ) (m k v₁ v₂ : ℤ) :
    Tendsto (fun z : ℂ => (z - principalFiveTermStripPolePosition d m k) *
      principalFiveTermResidueKernel d ℓ v₁ w
        (principalFiveTermLatticeArgument d v₁ v₂) m
        (z - (m : ℂ) * (principalRoot d : ℂ) ^ 3 / ((principalA d) 1 0 : ℂ)))
      (𝓝[≠] (principalFiveTermStripPolePosition d m k))
      (𝓝 (principalFiveTermKernelResidue d ℓ v₁ w
        (principalFiveTermLatticeArgument d v₁ v₂) m
        (principalFiveTermLatticeArgument d m k))) := by
  let c : ℂ := (m : ℂ) * (principalRoot d : ℂ) ^ 3 / ((principalA d) 1 0 : ℂ)
  let z₀ : ℂ := principalFiveTermLatticeArgument d m k
  have hp : principalFiveTermStripPolePosition d m k = z₀ + c := by
    dsimp [principalFiveTermStripPolePosition, z₀, c]
    push_cast
    ring
  have ht : Tendsto (fun z : ℂ => z - c)
      (𝓝[≠] (principalFiveTermStripPolePosition d m k)) (𝓝[≠] z₀) := by
    simpa only [hp, sub_eq_add_neg, add_neg_cancel_right] using
      SIC.tendsto_add_const_nhdsNE (-c) (principalFiveTermStripPolePosition d m k)
  have hr := (tendsto_sub_mul_principalFiveTermResidueKernel d hd ℓ w m k v₁ v₂).comp ht
  convert hr using 1
  funext z
  rw [hp]
  simp only [Function.comp_def]
  ring

/-- The contribution of one contour index to the kernel residues at a fixed position,
restricted to the source window `[a,a+H)`. This groups the residues in
[RW26, Radchenko, Wheeler (2026), Section 3.2, proof of Theorem 2, `thm:fg.equs`]. -/
def principalFiveTermWindowResidueFiber (d : ℕ) (a ℓ p : ℤ) (w y : ℝ)
    (m : FiveTermIndex (principalA d)) (s : ℂ) : ℂ :=
  ∑ mk ∈ principalFiveTermWindow d a with
    mk.1 = ((m : ℕ) : ℤ) ∧ principalFiveTermStripPolePosition d mk.1 mk.2 = s,
    principalFiveTermKernelResidue d ℓ p w y mk.1
      (principalFiveTermLatticeArgument d mk.1 mk.2)

/-- A pole belonging to the window has exactly its own residue in the corresponding fiber. -/
theorem principalFiveTermWindowResidueFiber_eq_of_pole (d : ℕ) (hd : 3 < d)
    (a ℓ p : ℤ) (w y : ℝ) (m : FiveTermIndex (principalA d)) (k : ℤ)
    (hmem : (((m : ℕ) : ℤ), k) ∈ principalFiveTermWindow d a) :
    principalFiveTermWindowResidueFiber d a ℓ p w y m
        (principalFiveTermStripPolePosition d ((m : ℕ) : ℤ) k) =
      principalFiveTermKernelResidue d ℓ p w y ((m : ℕ) : ℤ)
        (principalFiveTermLatticeArgument d ((m : ℕ) : ℤ) k) := by
  unfold principalFiveTermWindowResidueFiber
  rw [Finset.sum_filter]
  calc
    _ = if (((m : ℕ) : ℤ), k).1 = ((m : ℕ) : ℤ) ∧
          principalFiveTermStripPolePosition d (((m : ℕ) : ℤ), k).1
            (((m : ℕ) : ℤ), k).2 =
            principalFiveTermStripPolePosition d ((m : ℕ) : ℤ) k then
          principalFiveTermKernelResidue d ℓ p w y (((m : ℕ) : ℤ), k).1
            (principalFiveTermLatticeArgument d (((m : ℕ) : ℤ), k).1
              (((m : ℕ) : ℤ), k).2) else 0 := by
        apply Finset.sum_eq_single_of_mem (((m : ℕ) : ℤ), k) hmem
        intro mk hmk hne
        by_cases hp : mk.1 = ((m : ℕ) : ℤ) ∧
            principalFiveTermStripPolePosition d mk.1 mk.2 =
              principalFiveTermStripPolePosition d ((m : ℕ) : ℤ) k
        · have hk : mk.2 = k := by
            have hs : principalFiveTermStripPolePosition d ((m : ℕ) : ℤ) mk.2 =
                principalFiveTermStripPolePosition d ((m : ℕ) : ℤ) k := by
              simpa only [hp.1] using hp.2
            exact (principalFiveTermStripPolePosition_injective d hd ((m : ℕ) : ℤ)) hs
          exact (hne (Prod.ext hp.1 hk)).elim
        · simp [hp]
    _ = _ := by simp

/-- A contour index with no pole at a position contributes zero to every window fiber. -/
theorem principalFiveTermWindowResidueFiber_eq_zero (d : ℕ)
    (a ℓ p : ℤ) (w y : ℝ) (m : FiveTermIndex (principalA d)) (s : ℂ)
    (hnot : ∀ k : ℤ, s ≠ principalFiveTermStripPolePosition d ((m : ℕ) : ℤ) k) :
    principalFiveTermWindowResidueFiber d a ℓ p w y m s = 0 := by
  unfold principalFiveTermWindowResidueFiber
  rw [Finset.sum_filter]
  apply Finset.sum_eq_zero
  intro mk hmk
  have hn : ¬(mk.1 = ((m : ℕ) : ℤ) ∧
      principalFiveTermStripPolePosition d mk.1 mk.2 = s) := by
    rintro ⟨hm, hs⟩
    exact hnot mk.2 (hm ▸ hs.symm)
  simp [hn]

/-- The upper sector estimate is uniform on a fixed translated horizontal segment,
by `exists_horizontal_segment_bound_of_sector`. -/
private lemma principalFiveTerm_upper_segment_bound (d : ℕ) (hd : 3 < d)
    (ℓ p m : ℤ) (w y a b s : ℝ)
    (hRate : (principalRoot d ^ 3)⁻¹ < principalFiveTermUpperRate d ℓ w) :
    ∃ g : ℝ → ℝ, Tendsto g atTop (𝓝 0) ∧
      ∀ᶠ Y : ℝ in atTop, ∀ t ∈ uIcc a b,
        ‖principalFiveTermResidueKernel d ℓ p w y m
          ((t : ℂ) + Y * I - (s : ℂ))‖ ≤ g Y := by
  obtain ⟨C, κ, R, hκ, hbound⟩ :=
    exists_norm_principalFiveTermResidueKernel_upper d hd ℓ p m w y 1 hRate
  simpa using
    (exists_horizontal_segment_bound_of_sector
      (principalFiveTermResidueKernel d ℓ p w y m) a b s 1 C κ R
      (by norm_num) hκ (by simpa only [one_mul] using hbound))

/-- The lower sector estimate is uniform on a fixed translated horizontal segment,
by `exists_horizontal_segment_bound_of_sector`. -/
private lemma principalFiveTerm_lower_segment_bound (d : ℕ) (hd : 3 < d)
    (ℓ p m : ℤ) (w y a b s : ℝ)
    (hRate : principalFiveTermLowerRate d ℓ p w y < 0) :
    ∃ g : ℝ → ℝ, Tendsto g atTop (𝓝 0) ∧
      ∀ᶠ Y : ℝ in atTop, ∀ t ∈ uIcc a b,
        ‖principalFiveTermResidueKernel d ℓ p w y m
          ((t : ℂ) + (-Y) * I - (s : ℂ))‖ ≤ g Y := by
  obtain ⟨C, κ, R, hκ, hbound⟩ :=
    exists_norm_principalFiveTermResidueKernel_lower d hd ℓ p m w y 1 hRate
  simpa using
    (exists_horizontal_segment_bound_of_sector
      (principalFiveTermResidueKernel d ℓ p w y m) a b s (-1) C κ R
      (by norm_num) hκ (by simpa only [neg_one_mul, one_mul] using hbound))

/-- The upper horizontal side of a fixed rectangle for the residue sum vanishes as its
height grows. -/
lemma tendsto_intervalIntegral_principalFiveTermResidueSum_upper (d : ℕ) (hd : 3 < d)
    (ℓ p : ℤ) (w y a b : ℝ)
    (hupper : (principalRoot d ^ 3)⁻¹ < principalFiveTermUpperRate d ℓ w) :
    Tendsto (fun Y : ℝ => ∫ t : ℝ in a..b,
      principalFiveTermResidueSum d ℓ p w y ((t : ℂ) + Y * I)) atTop (𝓝 0) := by
  let F (m : FiveTermIndex (principalA d)) (t Y : ℝ) :=
    principalFiveTermResidueKernel d ℓ p w y ((m : ℕ) : ℤ)
      ((t : ℂ) + Y * I - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
        ((principalA d) 1 0 : ℂ))
  have h (m : FiveTermIndex (principalA d)) :
      ∃ g : ℝ → ℝ, Tendsto g atTop (𝓝 0) ∧
        ∀ᶠ Y : ℝ in atTop, ∀ t ∈ uIcc a b, ‖F m t Y‖ ≤ g Y := by
    let s : ℝ := ((m : ℕ) : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ)
    obtain ⟨g, hg, hb⟩ := principalFiveTerm_upper_segment_bound d hd ℓ p
      ((m : ℕ) : ℤ) w y a b s hupper
    refine ⟨g, hg, ?_⟩
    have hc : ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
        ((principalA d) 1 0 : ℂ) = (s : ℂ) := by norm_cast
    simpa only [F, hc] using hb
  change Tendsto (fun Y : ℝ => ∫ t : ℝ in a..b, ∑ m, F m t Y) atTop (𝓝 0)
  exact tendsto_intervalIntegral_sum_of_bounds F a b h

/-- The lower horizontal side of a fixed rectangle for the residue sum vanishes as its
height grows. -/
lemma tendsto_intervalIntegral_principalFiveTermResidueSum_lower (d : ℕ) (hd : 3 < d)
    (ℓ p : ℤ) (w y a b : ℝ)
    (hlower : principalFiveTermLowerRate d ℓ p w y < 0) :
    Tendsto (fun Y : ℝ => ∫ t : ℝ in a..b,
      principalFiveTermResidueSum d ℓ p w y ((t : ℂ) + (-Y) * I)) atTop (𝓝 0) := by
  let F (m : FiveTermIndex (principalA d)) (t Y : ℝ) :=
    principalFiveTermResidueKernel d ℓ p w y ((m : ℕ) : ℤ)
      ((t : ℂ) + (-Y) * I - ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
        ((principalA d) 1 0 : ℂ))
  have h (m : FiveTermIndex (principalA d)) :
      ∃ g : ℝ → ℝ, Tendsto g atTop (𝓝 0) ∧
        ∀ᶠ Y : ℝ in atTop, ∀ t ∈ uIcc a b, ‖F m t Y‖ ≤ g Y := by
    let s : ℝ := ((m : ℕ) : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ)
    obtain ⟨g, hg, hb⟩ := principalFiveTerm_lower_segment_bound d hd ℓ p
      ((m : ℕ) : ℤ) w y a b s hlower
    refine ⟨g, hg, ?_⟩
    have hc : ((m : ℕ) : ℂ) * (principalRoot d : ℂ) ^ 3 /
        ((principalA d) 1 0 : ℂ) = (s : ℂ) := by norm_cast
    simpa only [F, hc] using hb
  change Tendsto (fun Y : ℝ => ∫ t : ℝ in a..b, ∑ m, F m t Y) atTop (𝓝 0)
  exact tendsto_intervalIntegral_sum_of_bounds F a b h

/-- The real form of `principalFiveTermShift_coordinate`, with
$ε=cρ_d+1-d$ expanding the lattice translation. -/
private lemma principalFiveTerm_strip_shift_real (d : ℕ) (hd : 3 < d)
    (m m' M : ℤ)
    (hm : m + (principalA d) 0 0 - M * (principalA d) 1 0 = m' + 1)
    (x : ℝ) :
    x + (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ) -
        (m : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ) =
      x - (m' : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ) +
        (((principalA d) 0 0 - M * (principalA d) 1 0 : ℤ) : ℝ) * principalRoot d +
          (((principalA d) 0 1 + M * ((d : ℤ) - 1) : ℤ) : ℝ) := by
  have hcoord : x + (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ) -
      (m : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ) =
      (x - (m' : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ)) +
        (((principalA d) 0 0 : ℝ) * principalRoot d + ((principalA d) 0 1 : ℝ)) -
          M * principalRoot d ^ 3 := by
    exact_mod_cast (principalFiveTermShift_coordinate d hd m m' M hm (x : ℂ))
  have hε := principalRoot_pow_three_eq d hd
  have hc : ((principalA d) 1 0 : ℝ) = (d : ℝ) * ((d : ℝ) - 2) := by
    simp [coe_principalA]
  push_cast
  linear_combination hcoord - (M : ℝ) * hε +
    (M : ℝ) * principalRoot d * hc

/-- The source lattice arguments transport across the strip translation. -/
private lemma principalFiveTerm_strip_pole_shift_algebra (ε c ρ a b d m m' M k : ℝ)
    (hε0 : ε ≠ 0) (hδ : ε⁻¹ - 1 ≠ 0)
    (hρ : a * ρ + b = ρ * ε)
    (hε : ε = c * ρ + 1 - d)
    (hm : m + a - M * c = m' + 1) :
    (m * ρ + k) / (ε⁻¹ - 1) =
      (m' * ρ + (k + b + M * d)) / (ε⁻¹ - 1) +
        (a - M * c) * ρ + b + M * (d - 1) := by
  have hshift : (a - M * c) * ρ + b + M * (d - 1) = (ρ - M) * ε := by
    have hεM := congrArg (fun t : ℝ => M * t) hε
    nlinarith [hρ, hεM]
  have hmρ := congrArg (fun t : ℝ => t * ρ) hm
  have hεM := congrArg (fun t : ℝ => M * t) hε
  have hδs : (ε⁻¹ - 1) * ((a - M * c) * ρ + b + M * (d - 1)) =
      (m - m') * ρ - b - M * d := by
    rw [hshift]
    have hbasic : (ε⁻¹ - 1) * ((ρ - M) * ε) = (1 - ε) * (ρ - M) := by
      field_simp [hε0]
    rw [hbasic]
    nlinarith [hρ, hεM, hmρ]
  apply (div_eq_iff hδ).2
  calc
    m * ρ + k = m' * ρ + (k + b + M * d) +
        (ε⁻¹ - 1) * ((a - M * c) * ρ + b + M * (d - 1)) := by
      rw [hδs]
      ring
    _ = ((m' * ρ + (k + b + M * d)) / (ε⁻¹ - 1)) * (ε⁻¹ - 1) +
        ((a - M * c) * ρ + b + M * (d - 1)) * (ε⁻¹ - 1) := by
      rw [div_mul_cancel₀ _ hδ]
      ring
    _ = _ := by ring

/-- Under $m+a-1=m'+Mc$, a right-line pole of index $m$ becomes a left-line pole of
index $m'$ with second coordinate $k+b+Md$. -/
private lemma principalFiveTerm_strip_latticeArgument_shift (d : ℕ) (hd : 3 < d)
    (m m' M k : ℤ)
    (hm : m + (principalA d) 0 0 - M * (principalA d) 1 0 = m' + 1) :
    principalFiveTermLatticeArgument d m k =
      principalFiveTermLatticeArgument d m'
        (k + (principalA d) 0 1 + M * d) +
        (((principalA d) 0 0 - M * (principalA d) 1 0 : ℤ) : ℝ) * principalRoot d +
          (((principalA d) 0 1 + M * ((d : ℤ) - 1) : ℤ) : ℝ) := by
  have hε0 : principalRoot d ^ 3 ≠ 0 := (pow_pos (principalRoot_pos d hd) 3).ne'
  have hδ : (principalRoot d ^ 3)⁻¹ - 1 ≠ 0 := by
    have hε : 1 < principalRoot d ^ 3 :=
      one_lt_principalRoot_pow_three d hd
    exact ne_of_lt (sub_neg.mpr ((inv_lt_one₀ (by positivity)).2 hε))
  have hmR : (m : ℝ) + ((principalA d) 0 0 : ℝ) -
      (M : ℝ) * ((principalA d) 1 0 : ℝ) = (m' : ℝ) + 1 := by
    exact_mod_cast hm
  have h := principalFiveTerm_strip_pole_shift_algebra (principalRoot d ^ 3)
    ((principalA d) 1 0 : ℝ) (principalRoot d) ((principalA d) 0 0 : ℝ)
    ((principalA d) 0 1 : ℝ) d m m' M k hε0 hδ
    (principalA_numerator_principalRoot d hd) (eps_linear d hd).symm hmR
  simp only [principalFiveTermLatticeArgument]
  push_cast
  convert h using 1
  ring

/-- Reindexing transfers regularity of the left contour to the translated right contour. -/
lemma principalFiveTerm_strip_right_crossing (d : ℕ) (hd : 3 < d)
    (v₁ v₂ : ℤ) (x : ℝ)
    (hreg : ∀ m : FiveTermIndex (principalA d),
      IsPrincipalFiveTermResidueCrossing d ((m : ℕ) : ℤ)
        (principalFiveTermLatticeArgument d v₁ v₂)
        (x - ((m : ℕ) : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ)))
    (m : FiveTermIndex (principalA d)) :
    IsPrincipalFiveTermResidueCrossing d ((m : ℕ) : ℤ)
      (principalFiveTermLatticeArgument d v₁ v₂)
      (x + (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ) -
        ((m : ℕ) : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ)) := by
  let m' := principalFiveTermReindex d hd m
  obtain ⟨M, hm⟩ := principalFiveTermReindex_exists_quotient d hd m
  let K : ℤ := (principalA d) 0 0 - M * (principalA d) 1 0
  let L : ℤ := (principalA d) 0 1 + M * ((d : ℤ) - 1)
  let xl := x - ((m' : ℕ) : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ)
  let xr := x + (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ) -
    ((m : ℕ) : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ)
  have hshift : xr = xl + (K : ℝ) * principalRoot d + L := by
    convert principalFiveTerm_strip_shift_real d hd
      ((m : ℕ) : ℤ) ((m' : ℕ) : ℤ) M hm x using 1
  have hleft := hreg m'
  refine ⟨?_, ?_⟩
  · simpa only [xr, xl, hshift] using
      IsRegularPeriodLatticeCrossing.add_int_mul_add_int (principalRoot d)
        (principalFiveTermLatticeArgument d v₁ v₂) xl K L hleft.lattice
  · intro k hk
    have harg := principalFiveTerm_strip_latticeArgument_shift d hd
      ((m : ℕ) : ℤ) ((m' : ℕ) : ℤ) M k hm
    have hleftEq : xl = principalFiveTermLatticeArgument d ((m' : ℕ) : ℤ)
        (k + (principalA d) 0 1 + M * d) := by
      dsimp [xr, xl, K, L] at hshift hk
      linarith [harg]
    exact hleft.pole _ hleftEq

end SIC

end
