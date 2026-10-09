/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.Faddeev.WordBoundary

/-!
# The divisor of the Faddeev word product

Exact meromorphic orders of the word product on and off its period lattice.

This module follows the zero and pole sets `P_{γ,τ}` and `N_{γ,τ}` of
[RW26, Radchenko, Wheeler (2026), Section 2.2], using the word product of Proposition 2(ii),
`prop:prod.id.mod,fad`, equation (20), `eq:modulartofaddeevCF`, at
`γ=∏_{j=1}^r T^{b_j}S=(a b; c d)`.

## The argument

Off the period lattice `ℤ+ℤτ`, every argument `z_j+μ_jτ_j-μ_{j-1}` of the product lies off the
lattice of its own period `τ_j` (`faddeevWordGammaRegular_of_notMem`), where the generator is
analytic and nonzero; so the product is analytic and nonzero there, of order zero.

At an irrational real period whose word periods are positive, write `z=kτ+ℓ`. For
`γ=(T^{b₁}S)W`, division by `j_W(τ)` sends `z` to `k₁τ₁+ℓ₁` with
`(k₁,ℓ₁)=(kW₁₁-ℓW₁₀, ℓW₀₀-kW₀₁)`, and the first factor `Φ(z₁-n;τ₁)` has order
`1_{k₁≤0}-1_{ℓ₁≥n}` (`meromorphicOrderAt_faddeevS_real_lattice`). By induction the remaining
word has order `1_{k+m≤0}-1_{k₁≤0}`, since its lower row is `(W₁₀,W₁₁)`; the intermediate
indicators cancel and leave `1_{k+m≤0}-1_{dk-cℓ+n≤0}`, because `γ` has lower row
`(W₀₀,W₀₁)`. In the source's coordinates `z=k'(aτ+b)+ℓ'(cτ+d)` with `k'=dk-cℓ`, this is the
statement that the poles lie in `P_{γ,τ}` and the zeros in `N_{γ,τ}`, all simple.

These are identities of meromorphic orders. Totalized point values can be zero at a removable
zero-pole cancellation and do not determine the divisor there.
-/

noncomputable section

open Filter Topology
open scoped MatrixGroups

namespace SIC

/-! ### Off the period lattice

Every factor is analytic and nonzero, so the product has order zero. -/

/-- At slit-plane word periods, the word product is nonzero off `ℤ+ℤτ`. -/
theorem faddeevWord_ne_zero_of_notMem (bs : List ℤ) (m n : ℤ) {z τ : ℂ}
    (hτ : FaddeevWordPeriodsSlitPlane bs τ) (hz : ¬ IsPeriodLatticePoint τ z) :
    faddeevWord bs m n z τ ≠ 0 := by
  induction bs generalizing n with
  | nil => simp [faddeevWord]
  | cons a bs ih =>
      cases bs with
      | nil =>
          have hperiod := (faddeevWordPeriodsSlitPlane_singleton a τ).mp hτ
          rw [faddeevWord_singleton]
          exact faddeevS_ne_zero_of_not_mem_lattice _ _ hperiod
            ((isPeriodLatticePoint_add_int_mul_sub_int_iff τ z m n).not.mpr hz)
      | cons b bs =>
          obtain ⟨⟨hden, hperiod⟩, htail⟩ :=
            (faddeevWordPeriodsSlitPlane_cons_cons a b bs τ).mp hτ
          rw [faddeevWord_cons_cons]
          exact mul_ne_zero (faddeevS_ne_zero_of_not_mem_lattice _ _ hperiod
            (by simpa only [Int.cast_zero, zero_mul, add_zero] using
              (not_isPeriodLatticePoint_div_fltDenominator_add
                (letterWord (b :: bs)) hden hz 0 n))) (ih 0 htail)

/-- At slit-plane word periods, the word product has order zero off `ℤ+ℤτ`. -/
theorem meromorphicOrderAt_faddeevWord_eq_zero (bs : List ℤ) (m n : ℤ) {z τ : ℂ}
    (hτ : FaddeevWordPeriodsSlitPlane bs τ) (hz : ¬ IsPeriodLatticePoint τ z) :
    meromorphicOrderAt (fun w => faddeevWord bs m n w τ) z = 0 := by
  have han := analyticAt_faddeevWord bs m n hτ
    (faddeevWordGammaRegular_of_notMem bs m n hτ hz)
  have hn := faddeevWord_ne_zero_of_notMem bs m n hτ hz
  rw [han.meromorphicOrderAt_eq, (han.analyticOrderAt_eq_zero).2 hn]
  rfl

/-- At slit-plane word periods, the word product is nonzero on a punctured neighborhood of
every point. -/
theorem eventually_faddeevWord_ne_zero (bs : List ℤ) (m n : ℤ) {τ : ℂ}
    (hτ : FaddeevWordPeriodsSlitPlane bs τ) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, faddeevWord bs m n w τ ≠ 0 := by
  have hf := meromorphicAt_faddeevWord bs m n hτ z
  have hfreq : ∃ᶠ w in 𝓝[≠] z, ¬ IsPeriodLatticePoint τ w :=
    Set.Countable.frequently_notMem_nhdsNE (countable_setOf_isPeriodLatticePoint τ) z
  apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hf).mp
  intro htop
  have hzero : (fun w => faddeevWord bs m n w τ) =ᶠ[𝓝[≠] z] (fun _ => 0) :=
    meromorphicOrderAt_eq_top_iff.mp htop
  have hnot : ∃ᶠ w in 𝓝[≠] z, faddeevWord bs m n w τ ≠ 0 :=
    hfreq.mono fun w hw => faddeevWord_ne_zero_of_notMem bs m n hτ hw
  exact hnot (hzero.mono fun w hw hn => hn hw)

/-! ### The lattice divisor

The generator orders telescope along the word. -/

/-- The single-factor divisor formula used to start
`meromorphicOrderAt_faddeevWord_real_lattice`. -/
private lemma meromorphicOrderAt_faddeevWord_singleton (b m n k l : ℤ) (τ : ℝ)
    (hτ : 0 < τ) (hirr : Irrational τ) :
    meromorphicOrderAt (fun w => faddeevWord [b] m n w τ) ((k : ℂ) * τ + l) =
      (((if k + m ≤ 0 then (1 : ℤ) else 0) -
        (if letterWord [b] 1 1 * k - letterWord [b] 1 0 * l + n ≤ 0
          then 1 else 0) : ℤ) : WithTop ℤ) := by
  have hfun : (fun w : ℂ => faddeevWord [b] m n w τ) =
      (fun w : ℂ => faddeevS (w / 1 + (m * τ - n)) τ) := by
    funext w
    simp only [faddeevWord_singleton, div_one]
    ring_nf
  rw [hfun, meromorphicOrderAt_faddeevS_div_add (τ : ℂ) 1
    (m * (τ : ℂ) - n) _ one_ne_zero]
  have harg : ((k : ℂ) * τ + l) / 1 + (m * τ - n) =
      (((k + m : ℤ) : ℂ) * τ + (l - n : ℤ)) := by
    push_cast
    ring_nf
  rw [harg, meromorphicOrderAt_faddeevS_real_lattice τ hτ hirr (k + m) (l - n)]
  have hlast : (0 ≤ l - n) ↔
      (letterWord [b] 1 1 * k - letterWord [b] 1 0 * l + n ≤ 0) := by
    simp only [letterWord_cons_apply_one, letterWord_nil]
    simp
  simp only [hlast]

/-- The order of a word with at least two letters splits into the first generator order
and the divisor of the remaining word; used by `meromorphicOrderAt_faddeevWord_real_lattice`. -/
private lemma meromorphicOrderAt_faddeevWord_cons_cons (a b : ℤ) (bs : List ℤ)
    (m n : ℤ) {τ : ℂ} (hτ : FaddeevWordPeriodsSlitPlane (a :: b :: bs) τ)
    (z : ℂ) :
    meromorphicOrderAt (fun w => faddeevWord (a :: b :: bs) m n w τ) z =
      meromorphicOrderAt (fun w => faddeevS
        (w / fltDenominator (letterWord (b :: bs) : Mat(2, ℤ)) τ - n)
        (flt (letterWord (b :: bs) : Mat(2, ℤ)) τ)) z +
      meromorphicOrderAt (fun w => faddeevWord (b :: bs) m 0 w τ) z := by
  obtain ⟨⟨_, hperiod⟩, htail⟩ :=
    (faddeevWordPeriodsSlitPlane_cons_cons a b bs τ).mp hτ
  have hfirst := meromorphicAt_faddeevS_div_add _ hperiod
    (fltDenominator (letterWord (b :: bs) : Mat(2, ℤ)) τ) (-n) z
  have hrest := meromorphicAt_faddeevWord (b :: bs) m 0 htail z
  have hfun : (fun w => faddeevWord (a :: b :: bs) m n w τ) =
      (fun w => faddeevS
        (w / fltDenominator (letterWord (b :: bs) : Mat(2, ℤ)) τ - n)
        (flt (letterWord (b :: bs) : Mat(2, ℤ)) τ)) *
      (fun w => faddeevWord (b :: bs) m 0 w τ) := by
    funext w
    exact faddeevWord_cons_cons a b bs m n w τ
  rw [hfun]
  exact meromorphicOrderAt_mul hfirst hrest

/-- The argument of a word factor in the lattice coordinates of its suffix period;
used by `meromorphicOrderAt_faddeevWord_head`. -/
private lemma faddeevWord_factor_coordinates (w : List ℤ) (n k l : ℤ) {τ : ℝ}
    (hirr : Irrational τ) :
    (((k : ℂ) * τ + l) /
        fltDenominator (letterWord w : Mat(2, ℤ)) (τ : ℂ) - n) =
      (((k * letterWord w 1 1 - l * letterWord w 1 0 : ℤ) : ℂ) *
          (flt (letterWord w : Mat(2, ℤ)) τ : ℝ) +
        ((l * letterWord w 0 0 - k * letterWord w 0 1 - n : ℤ) : ℂ)) := by
  have hdenR := fltDenominator_ne_zero_of_irrational hirr (letterWord w)
  have hden : fltDenominator (letterWord w : Mat(2, ℤ)) (τ : ℂ) ≠ 0 := by
    exact_mod_cast hdenR
  have hcoord : ((k : ℂ) * τ + l) /
        fltDenominator (letterWord w : Mat(2, ℤ)) (τ : ℂ) =
      (((k * letterWord w 1 1 - l * letterWord w 1 0 : ℤ) : ℂ) *
        (flt (letterWord w : Mat(2, ℤ)) τ : ℝ) +
        ((l * letterWord w 0 0 - k * letterWord w 0 1 : ℤ) : ℂ)) := by
    rw [ofReal_flt]
    convert intCast_add_intCast_mul_div_fltDenominator
      (letterWord w) (τ : ℂ) hden l k using 1 <;> ring_nf
  rw [hcoord]
  push_cast
  ring_nf

/-- The first generator contributes the difference between the entering suffix coordinate
and the outgoing coordinate; used by `meromorphicOrderAt_faddeevWord_real_lattice`. -/
private lemma meromorphicOrderAt_faddeevWord_head (w : List ℤ) (n k l : ℤ) {τ : ℝ}
    (hirr : Irrational τ) (hpos : 0 < flt (letterWord w : Mat(2, ℤ)) τ) :
    meromorphicOrderAt (fun v => faddeevS
        (v / fltDenominator (letterWord w : Mat(2, ℤ)) (τ : ℂ) - n)
        (flt (letterWord w : Mat(2, ℤ)) (τ : ℂ))) ((k : ℂ) * τ + l) =
      ((((if k * letterWord w 1 1 - l * letterWord w 1 0 ≤ 0 then (1 : ℤ) else 0) -
        (if n - (l * letterWord w 0 0 - k * letterWord w 0 1) ≤ 0
          then 1 else 0)) : ℤ) : WithTop ℤ) := by
  let W : SL(2, ℤ) := letterWord w
  let σ : ℝ := flt (W : Mat(2, ℤ)) τ
  have hdenR := fltDenominator_ne_zero_of_irrational hirr W
  have hden : fltDenominator (W : Mat(2, ℤ)) (τ : ℂ) ≠ 0 := by
    exact_mod_cast hdenR
  have horder : meromorphicOrderAt (fun v => faddeevS
        (v / fltDenominator (W : Mat(2, ℤ)) (τ : ℂ) - n)
        (flt (W : Mat(2, ℤ)) (τ : ℂ))) ((k : ℂ) * τ + l) =
      meromorphicOrderAt (fun v => faddeevS v (σ : ℂ))
        (((k : ℂ) * τ + l) / fltDenominator (W : Mat(2, ℤ)) (τ : ℂ) - n) := by
    simpa only [σ, ofReal_flt, sub_eq_add_neg] using
      meromorphicOrderAt_faddeevS_div_add (σ : ℂ)
        (fltDenominator (W : Mat(2, ℤ)) (τ : ℂ)) (-n)
        ((k : ℂ) * τ + l) hden
  rw [show W = letterWord w from rfl] at horder
  rw [horder, faddeevWord_factor_coordinates w n k l hirr]
  rw [meromorphicOrderAt_faddeevS_real_lattice σ hpos (Irrational.flt hirr W)
    (k * W 1 1 - l * W 1 0) (l * W 0 0 - k * W 0 1 - n)]
  have hlast : (0 ≤ l * W 0 0 - k * W 0 1 - n) ↔
      (n - (l * W 0 0 - k * W 0 1) ≤ 0) := by omega
  simp only [W, hlast]

/-- The two suffix-coordinate indicators cancel in the word divisor formula;
used by `meromorphicOrderAt_faddeevWord_real_lattice`. -/
private lemma faddeevWord_indicator_cancellation (a : ℤ) (w : List ℤ)
    (m n k l : ℤ) :
    ((if k * letterWord w 1 1 - l * letterWord w 1 0 ≤ 0 then (1 : ℤ) else 0) -
      (if n - (l * letterWord w 0 0 - k * letterWord w 0 1) ≤ 0 then 1 else 0)) +
    ((if k + m ≤ 0 then (1 : ℤ) else 0) -
      (if letterWord w 1 1 * k - letterWord w 1 0 * l ≤ 0 then 1 else 0)) =
    ((if k + m ≤ 0 then (1 : ℤ) else 0) -
      (if letterWord (a :: w) 1 1 * k - letterWord (a :: w) 1 0 * l + n ≤ 0
        then 1 else 0)) := by
  have hmid : letterWord w 1 1 * k - letterWord w 1 0 * l =
      k * letterWord w 1 1 - l * letterWord w 1 0 := by ring_nf
  have hend : letterWord (a :: w) 1 1 * k - letterWord (a :: w) 1 0 * l + n =
      n - (l * letterWord w 0 0 - k * letterWord w 0 1) := by
    rw [letterWord_cons_apply_one, letterWord_cons_apply_one]
    ring_nf
  rw [hmid, hend]
  ring_nf

/-- At an irrational real period `τ` whose word periods `γ_j·τ` are positive, the order of
`Φ_{γ,m,n}(·;τ)` at `z=kτ+ℓ` is `1_{k+m≤0}-1_{dk-cℓ+n≤0}` for `γ=(a b; c d)`: the zero and
pole sets `N_{γ,τ}` and `P_{γ,τ}` of [RW26, Radchenko, Wheeler (2026), Section 2.2], with
simple zeros and poles. The source states the inclusions for every period with `cτ+d>0`. -/
theorem meromorphicOrderAt_faddeevWord_real_lattice (bs : List ℤ) (hbs : bs ≠ [])
    (m n k l : ℤ) {τ : ℝ} (hirr : Irrational τ)
    (hpos : ∀ w ∈ bs.tail.tails, 0 < flt (letterWord w : Mat(2, ℤ)) τ) :
    meromorphicOrderAt (fun w => faddeevWord bs m n w τ) ((k : ℂ) * τ + l) =
      (((if k + m ≤ 0 then (1 : ℤ) else 0) -
        (if letterWord bs 1 1 * k - letterWord bs 1 0 * l + n ≤ 0 then 1 else 0) : ℤ) :
          WithTop ℤ) := by
  induction bs generalizing n with
  | nil => exact (hbs rfl).elim
  | cons a bs ih =>
      cases bs with
      | nil =>
          have hτ : 0 < τ := by
            simpa [letterWord_nil, flt_one] using hpos [] (by simp)
          exact meromorphicOrderAt_faddeevWord_singleton a m n k l τ hτ hirr
      | cons b bs =>
          have hheadpos : 0 < flt (letterWord (b :: bs) : Mat(2, ℤ)) τ :=
            hpos (b :: bs) (by simp)
          have htailpos : ∀ w ∈ (b :: bs).tail.tails,
              0 < flt (letterWord w : Mat(2, ℤ)) τ := by
            intro w hw
            have hw' : w ∈ (a :: b :: bs).tail.tails := by
              simp only [List.tail_cons, List.tails_cons, List.mem_cons]
              exact Or.inr hw
            exact hpos w hw'
          have hτword :=
            faddeevWordPeriodsSlitPlane_of_irrational (a :: b :: bs) hirr hpos
          have hrest := ih (by simp) 0 htailpos
          rw [meromorphicOrderAt_faddeevWord_cons_cons a b bs m n hτword,
            meromorphicOrderAt_faddeevWord_head (b :: bs) n k l hirr hheadpos, hrest]
          simpa only [add_zero, ← WithTop.coe_add] using
            congrArg (fun v : ℤ => (v : WithTop ℤ))
              (faddeevWord_indicator_cancellation a (b :: bs) m n k l)

/-- At an irrational real period with positive word periods, `Φ_{γ,m,n}` has a zero at
`kτ+ℓ` exactly when `k+m≤0` and `dk-cℓ+n>0`: the zero set `N_{γ,τ}` of
[RW26, Radchenko, Wheeler (2026), Section 2.2]. -/
theorem meromorphicOrderAt_faddeevWord_pos_iff (bs : List ℤ) (hbs : bs ≠ [])
    (m n k l : ℤ) {τ : ℝ} (hirr : Irrational τ)
    (hpos : ∀ w ∈ bs.tail.tails, 0 < flt (letterWord w : Mat(2, ℤ)) τ) :
    0 < meromorphicOrderAt (fun w => faddeevWord bs m n w τ) ((k : ℂ) * τ + l) ↔
      k + m ≤ 0 ∧ 0 < letterWord bs 1 1 * k - letterWord bs 1 0 * l + n := by
  rw [meromorphicOrderAt_faddeevWord_real_lattice bs hbs m n k l hirr hpos]
  norm_cast
  split_ifs <;> simp_all [Int.subNatNat, not_le]

/-- At an irrational real period with positive word periods, `Φ_{γ,m,n}` has a pole at
`kτ+ℓ` exactly when `k+m>0` and `dk-cℓ+n≤0`: the pole set `P_{γ,τ}` of
[RW26, Radchenko, Wheeler (2026), Section 2.2]. -/
theorem meromorphicOrderAt_faddeevWord_neg_iff (bs : List ℤ) (hbs : bs ≠ [])
    (m n k l : ℤ) {τ : ℝ} (hirr : Irrational τ)
    (hpos : ∀ w ∈ bs.tail.tails, 0 < flt (letterWord w : Mat(2, ℤ)) τ) :
    meromorphicOrderAt (fun w => faddeevWord bs m n w τ) ((k : ℂ) * τ + l) < 0 ↔
      0 < k + m ∧ letterWord bs 1 1 * k - letterWord bs 1 0 * l + n ≤ 0 := by
  rw [meromorphicOrderAt_faddeevWord_real_lattice bs hbs m n k l hirr hpos]
  norm_cast
  split_ifs <;> simp_all [Int.subNatNat, not_le]

/-- At an irrational real period with positive word periods, every pole of the word product
is at most simple. -/
theorem meromorphicOrderAt_faddeevWord_ge_neg_one (bs : List ℤ) (hbs : bs ≠ [])
    (m n : ℤ) {τ : ℝ} (hirr : Irrational τ)
    (hpos : ∀ w ∈ bs.tail.tails, 0 < flt (letterWord w : Mat(2, ℤ)) τ) (z : ℂ) :
    ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (fun w => faddeevWord bs m n w τ) z := by
  by_cases hlat : IsPeriodLatticePoint (τ : ℂ) z
  · rcases hlat with ⟨l, k, rfl⟩
    rw [show (l : ℂ) + (k : ℂ) * τ = (k : ℂ) * τ + l by ring_nf,
      meromorphicOrderAt_faddeevWord_real_lattice bs hbs m n k l hirr hpos]
    split_ifs <;> decide
  · have hτword := faddeevWordPeriodsSlitPlane_of_irrational bs hirr hpos
    rw [meromorphicOrderAt_faddeevWord_eq_zero bs m n hτword hlat]
    decide

end SIC
