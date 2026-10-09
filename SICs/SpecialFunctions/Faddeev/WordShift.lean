/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.Faddeev.WordBoundary

/-!
# Shift laws of the Faddeev word product

The index shifts, the simultaneous index shift at a fixed point, and the lattice shifts of the
word product, off the period lattice and as meromorphic germs.

This module follows [RW26, Radchenko, Wheeler (2026), Section 2.2, equation (16),
`eq:faddeevperiod`] for the word product `Φ_{γ,m,n}(z;τ)` of Proposition 2(ii),
`prop:prod.id.mod,fad`, equation (20), `eq:modulartofaddeevCF`, at
`γ=∏_{j=1}^r T^{b_j}S=(a b; c d)`. Put `γ=(T^{b₁}S)γ'`, `τ₁=γ'·τ`, `z₁=z/j_{γ'}(τ)`, and
`e(x)=exp(2πix)`.

## The argument

Every argument of the product is a lattice translate of `z/j_{γ_j}(τ)`, which lies off the
lattice `ℤ+ℤτ_j` of its own period when `z∉ℤ+ℤτ`. So at slit-plane word periods every gamma
denominator met below is nonzero, and the generator laws `faddeevS_add_tau`,
`faddeevS_add_one`, and `faddeevS_transfer_int` apply.

*First intermediate index.* The first factor `Φ(z₁-n;τ₁)` and the first factor of the
remaining word have periods `τ₁=b₂-1/τ₂` and `τ₂`, and arguments differing by an integer
after division by `τ₂`; `faddeevS_transfer_int` moves an integer `k` between them. This is
equation (20) with an arbitrary first intermediate index.

*Index shifts.* Raising `m` changes only the last factor `Φ(z+mτ-m_{r-1};τ)`, which
`faddeevS_add_tau` relates with the multiplier `1-e(z+mτ)`. Raising `n` changes only the first
factor; `faddeevS_add_one` gives the multiplier `1-e((z₁-n)/τ₁)`, and
`(z₁-n)/τ₁ = z/j_γ(τ)-n/τ₁ ≡ z/j_γ(τ)+n γ·τ (mod ℤ)` since `γ·τ=b₁-1/τ₁` and
`j_γ(τ)=τ₁ j_{γ'}(τ)`.

*Equation (16).* At a fixed point `γ·τ=τ` with `e(z+mτ)=e(z/j_γ(τ)+nτ)`, the multipliers of the
two index shifts at `(m+k,n+k)` coincide for every `k`, so `Φ_{γ,m+k+1,n+k+1}=Φ_{γ,m+k,n+k}`
without division; induction on `k` in both directions gives the source's corollary.

*Lattice shifts.* For `λ=pτ+q`, `λ/j_{γ'}(τ)=p'τ₁+q'` with `(p',q')=(p,q)γ'^{-1}`. By induction
on the word, the remaining word turns `z+λ` into the indices `(m+p,p')`, the first factor
absorbs `q'`, and the first intermediate index `p'` is moved back to zero. This gives
`Φ_{γ,m,n}(z+pτ+q;τ)=Φ_{γ,m+p,n+pd-qc}(z;τ)`, the four shifts of Section 2.2 at
`(p,q)=(1,0),(0,1),(c,d),(a,b)`.

*Germs.* Both sides of each shift law are meromorphic in `z`, and the period lattice is
countable, so the pointwise identities give equalities of meromorphic germs at every point.
-/

noncomputable section

open Filter Topology
open scoped MatrixGroups

namespace SIC

/-! ### The first intermediate index

The first factor exchanges an integer index with the next factor through
`faddeevS_transfer_int`, whose endpoint gamma denominators are nonzero off the lattice. -/

/-- An integral translate of a word factor's argument stays in the generator's gamma domain;
used by `faddeevWord_cons_cons_eq_index` and `faddeevWord_index_add_one_right`. -/
private lemma faddeevWord_factor_denominator_ne_zero (w : List ℤ) (m n : ℤ) {z τ : ℂ}
    (hden : fltDenominator (letterWord w : Mat(2, ℤ)) τ ≠ 0)
    (hperiod : flt (letterWord w : Mat(2, ℤ)) τ ∈ Complex.slitPlane)
    (hz : ¬ IsPeriodLatticePoint τ z) :
    barnesDoubleGammaInv
      (flt (letterWord w : Mat(2, ℤ)) τ -
        (z / fltDenominator (letterWord w : Mat(2, ℤ)) τ +
          m * flt (letterWord w : Mat(2, ℤ)) τ - n)) 1
      (flt (letterWord w : Mat(2, ℤ)) τ) ≠ 0 := by
  exact faddeevS_denominator_ne_zero_of_not_mem_lattice _ _ hperiod
    (not_isPeriodLatticePoint_div_fltDenominator_add (letterWord w) hden hz m n)

/-- The two-letter transfer step used by `faddeevWord_cons_cons_eq_index`. -/
private theorem faddeevWord_cons_cons_eq_index_two (a b : ℤ) (m n k : ℤ) {z τ : ℂ}
    (hτ : FaddeevWordPeriodsSlitPlane [a, b] τ) (hz : ¬ IsPeriodLatticePoint τ z) :
    faddeevWord [a, b] m n z τ =
      faddeevS (z / fltDenominator (letterWord [b] : Mat(2, ℤ)) τ +
          k * flt (letterWord [b] : Mat(2, ℤ)) τ - n)
          (flt (letterWord [b] : Mat(2, ℤ)) τ) *
        faddeevWord [b] m k z τ := by
  obtain ⟨⟨hden, hperiod⟩, htail⟩ :=
    (faddeevWordPeriodsSlitPlane_cons_cons a b [] τ).mp hτ
  have hτperiod := (faddeevWordPeriodsSlitPlane_singleton b τ).mp htail
  have hτ0 := Complex.slitPlane_ne_zero hτperiod
  have hJ : fltDenominator (letterWord [b] : Mat(2, ℤ)) τ = τ := by
    rw [letterWord_singleton, fltDenominator_T_zpow_mul_S]
  have hF : flt (letterWord [b] : Mat(2, ℤ)) τ = b - 1 / τ := by
    rw [letterWord_singleton, flt_T_zpow_mul_S b hτ0]
  have hu := faddeevWord_factor_denominator_ne_zero [b] (max k 0) n hden
    hperiod hz
  have hv := faddeevS_denominator_ne_zero_of_not_mem_lattice
    (z + m * τ - (min k 0 : ℤ)) τ hτperiod
    ((isPeriodLatticePoint_add_int_mul_sub_int_iff τ z m (min k 0)).not.mpr hz)
  have htransfer := faddeevS_transfer_int
    (z / fltDenominator (letterWord [b] : Mat(2, ℤ)) τ - n)
    (z + m * τ) (flt (letterWord [b] : Mat(2, ℤ)) τ) τ
    (-(n + m)) b k hperiod hτperiod (by rw [hF]; ring_nf)
    (by rw [hJ]; field_simp; push_cast; ring_nf)
    (by convert hu using 1; ring_nf) hv
  rw [faddeevWord_cons_cons, faddeevWord_singleton, faddeevWord_singleton]
  convert htransfer.symm using 1 <;> push_cast <;> ring_nf

/-- The transfer step with a nonempty tail used by `faddeevWord_cons_cons_eq_index`. -/
private theorem faddeevWord_cons_cons_eq_index_tail (a b c : ℤ) (cs : List ℤ)
    (m n k : ℤ) {z τ : ℂ}
    (hτ : FaddeevWordPeriodsSlitPlane (a :: b :: c :: cs) τ)
    (hz : ¬ IsPeriodLatticePoint τ z) :
    faddeevWord (a :: b :: c :: cs) m n z τ =
      faddeevS (z / fltDenominator (letterWord (b :: c :: cs) : Mat(2, ℤ)) τ +
          k * flt (letterWord (b :: c :: cs) : Mat(2, ℤ)) τ - n)
          (flt (letterWord (b :: c :: cs) : Mat(2, ℤ)) τ) *
        faddeevWord (b :: c :: cs) m k z τ := by
  obtain ⟨⟨hden, hperiod⟩, htail⟩ :=
    (faddeevWordPeriodsSlitPlane_cons_cons a b (c :: cs) τ).mp hτ
  obtain ⟨⟨hden', hperiod'⟩, _⟩ :=
    (faddeevWordPeriodsSlitPlane_cons_cons b c cs τ).mp htail
  have hσ' := Complex.slitPlane_ne_zero hperiod'
  have hJ := fltDenominator_letterWord_cons b (c :: cs) hden'
  have hF := flt_letterWord_cons b (c :: cs) hden' hσ'
  have hu := faddeevWord_factor_denominator_ne_zero (b :: c :: cs)
    (max k 0) n hden hperiod hz
  have hv := faddeevWord_factor_denominator_ne_zero (c :: cs)
    0 (min k 0) hden' hperiod' hz
  have htransfer := faddeevS_transfer_int
    (z / fltDenominator (letterWord (b :: c :: cs) : Mat(2, ℤ)) τ - n)
    (z / fltDenominator (letterWord (c :: cs) : Mat(2, ℤ)) τ)
    (flt (letterWord (b :: c :: cs) : Mat(2, ℤ)) τ)
    (flt (letterWord (c :: cs) : Mat(2, ℤ)) τ) (-n) b k hperiod hperiod'
    (by rw [hF]; ring_nf) (by rw [hJ]; field_simp; push_cast; ring_nf)
    (by convert hu using 1; ring_nf) (by convert hv using 1; push_cast; ring_nf)
  rw [faddeevWord_cons_cons, faddeevWord_cons_cons, faddeevWord_cons_cons]
  convert congrArg (fun x : ℂ => x * faddeevWord (c :: cs) m 0 z τ)
    htransfer.symm using 1 <;> push_cast <;> ring_nf

/-- Equation (20) with an arbitrary first intermediate index `k`:
`Φ_{γ,m,n}(z;τ)=Φ(z₁+kτ₁-n;τ₁) Φ_{γ',m,k}(z;τ)` for `γ=(T^aS)γ'`, `τ₁=γ'·τ`, and
`z₁=z/j_{γ'}(τ)`, at slit-plane word periods and `z∉ℤ+ℤτ`.
[RW26, Radchenko, Wheeler (2026), Proposition 2(ii), `prop:prod.id.mod,fad`, equation (20),
`eq:modulartofaddeevCF`]. -/
@[source "RW26, equation (20), p. 7, eq:modulartofaddeevCF (arbitrary first intermediate index)"]
theorem faddeevWord_cons_cons_eq_index (a b : ℤ) (bs : List ℤ) (m n k : ℤ) {z τ : ℂ}
    (hτ : FaddeevWordPeriodsSlitPlane (a :: b :: bs) τ) (hz : ¬ IsPeriodLatticePoint τ z) :
    faddeevWord (a :: b :: bs) m n z τ =
      faddeevS (z / fltDenominator (letterWord (b :: bs) : Mat(2, ℤ)) τ +
          k * flt (letterWord (b :: bs) : Mat(2, ℤ)) τ - n)
          (flt (letterWord (b :: bs) : Mat(2, ℤ)) τ) *
        faddeevWord (b :: bs) m k z τ := by
  cases bs with
  | nil => exact faddeevWord_cons_cons_eq_index_two a b m n k hτ hz
  | cons c cs => exact faddeevWord_cons_cons_eq_index_tail a b c cs m n k hτ hz

/-! ### Index shifts

Only the factor carrying the shifted index changes. -/

/-- The left index shift `Φ_{γ,m+1,n}(z;τ)(1-q^m e(z))=Φ_{γ,m,n}(z;τ)`, `q=e(τ)`, of
[RW26, Radchenko, Wheeler (2026), Section 2.2] for the word product, at slit-plane word periods
and `z∉ℤ+ℤτ`. -/
theorem faddeevWord_index_add_one_left (bs : List ℤ) (hbs : bs ≠ []) (m n : ℤ) {z τ : ℂ}
    (hτ : FaddeevWordPeriodsSlitPlane bs τ) (hz : ¬ IsPeriodLatticePoint τ z) :
    faddeevWord bs (m + 1) n z τ *
        (1 - Complex.exp (2 * Real.pi * Complex.I * (z + m * τ))) =
      faddeevWord bs m n z τ := by
  induction bs generalizing n with
  | nil => contradiction
  | cons a bs ih =>
      cases bs with
      | nil =>
          have hperiod := (faddeevWordPeriodsSlitPlane_singleton a τ).mp hτ
          have hden := faddeevS_denominator_ne_zero_of_not_mem_lattice
            (z + (m + 1 : ℤ) * τ - n) τ hperiod
            ((isPeriodLatticePoint_add_int_mul_sub_int_iff τ z (m + 1) n).not.mpr hz)
          have hshift := faddeevS_add_tau (z + m * τ - n) τ hperiod (by
            convert hden using 1; push_cast; ring_nf)
          have hphase := exp_two_pi_I_eq_of_sub_intCast (z + m * τ - n)
            (z + m * τ) (-n) (by push_cast; ring_nf)
          simpa only [faddeevWord_singleton, hphase,
            show z + (m + 1 : ℤ) * τ - n = (z + m * τ - n) + τ by push_cast; ring_nf]
            using hshift
      | cons b bs =>
          obtain ⟨_, htail⟩ :=
            (faddeevWordPeriodsSlitPlane_cons_cons a b bs τ).mp hτ
          have hrest := ih (by simp) 0 htail
          rw [faddeevWord_cons_cons, faddeevWord_cons_cons]
          rw [← hrest]
          ring_nf

/-- The phase of the first factor equals the phase in
`faddeevWord_index_add_one_right`. -/
private lemma faddeevWord_head_phase (a : ℤ) (w : List ℤ) (n : ℤ) {z τ : ℂ}
    (hden : fltDenominator (letterWord w : Mat(2, ℤ)) τ ≠ 0)
    (hσ : flt (letterWord w : Mat(2, ℤ)) τ ≠ 0) :
    Complex.exp (2 * Real.pi * Complex.I *
      ((z / fltDenominator (letterWord w : Mat(2, ℤ)) τ - n) /
        flt (letterWord w : Mat(2, ℤ)) τ)) =
    Complex.exp (2 * Real.pi * Complex.I *
      (z / fltDenominator (letterWord (a :: w) : Mat(2, ℤ)) τ +
        n * flt (letterWord (a :: w) : Mat(2, ℤ)) τ)) := by
  apply exp_two_pi_I_eq_of_sub_intCast _ _ (-(n * a))
  rw [fltDenominator_letterWord_cons a w hden, flt_letterWord_cons a w hden hσ]
  field_simp
  push_cast
  ring_nf

/-- The one-letter right index shift used by `faddeevWord_index_add_one_right`. -/
private theorem faddeevWord_index_add_one_right_singleton (a m n : ℤ) {z τ : ℂ}
    (hτ : FaddeevWordPeriodsSlitPlane [a] τ) (hz : ¬ IsPeriodLatticePoint τ z) :
    faddeevWord [a] m (n + 1) z τ =
      (1 - Complex.exp (2 * Real.pi * Complex.I *
        (z / fltDenominator (letterWord [a] : Mat(2, ℤ)) τ +
          n * flt (letterWord [a] : Mat(2, ℤ)) τ))) *
        faddeevWord [a] m n z τ := by
  have hperiod := (faddeevWordPeriodsSlitPlane_singleton a τ).mp hτ
  have hτ0 := Complex.slitPlane_ne_zero hperiod
  have hden := faddeevS_denominator_ne_zero_of_not_mem_lattice
    (z + m * τ - n) τ hperiod
    ((isPeriodLatticePoint_add_int_mul_sub_int_iff τ z m n).not.mpr hz)
  have hshift := faddeevS_add_one (z + m * τ - (n + 1 : ℤ)) τ hperiod
    (by convert hden using 1; push_cast; ring_nf)
  have hJ : fltDenominator (letterWord [a] : Mat(2, ℤ)) τ = τ := by
    rw [letterWord_singleton, fltDenominator_T_zpow_mul_S]
  have hF : flt (letterWord [a] : Mat(2, ℤ)) τ = a - 1 / τ := by
    rw [letterWord_singleton, flt_T_zpow_mul_S a hτ0]
  have hphase := exp_two_pi_I_eq_of_sub_intCast
    ((z + m * τ - n) / τ)
    (z / fltDenominator (letterWord [a] : Mat(2, ℤ)) τ +
      n * flt (letterWord [a] : Mat(2, ℤ)) τ)
    (m - n * a) (by rw [hJ, hF]; field_simp; push_cast; ring_nf)
  rw [faddeevWord_singleton, faddeevWord_singleton]
  calc
    faddeevS (z + m * τ - (n + 1 : ℤ)) τ =
        faddeevS (z + m * τ - n) τ *
          (1 - Complex.exp (2 * Real.pi * Complex.I * ((z + m * τ - n) / τ))) := by
            convert hshift.symm using 1; push_cast; ring_nf
    _ = _ := by rw [hphase]; ring_nf

/-- The right index shift for a nonempty suffix, used by
`faddeevWord_index_add_one_right`. -/
private theorem faddeevWord_index_add_one_right_cons (a b : ℤ) (bs : List ℤ)
    (m n : ℤ) {z τ : ℂ}
    (hτ : FaddeevWordPeriodsSlitPlane (a :: b :: bs) τ)
    (hz : ¬ IsPeriodLatticePoint τ z) :
    faddeevWord (a :: b :: bs) m (n + 1) z τ =
      (1 - Complex.exp (2 * Real.pi * Complex.I *
        (z / fltDenominator (letterWord (a :: b :: bs) : Mat(2, ℤ)) τ +
          n * flt (letterWord (a :: b :: bs) : Mat(2, ℤ)) τ))) *
        faddeevWord (a :: b :: bs) m n z τ := by
  obtain ⟨⟨hden, hperiod⟩, _⟩ :=
    (faddeevWordPeriodsSlitPlane_cons_cons a b bs τ).mp hτ
  have hgamma := faddeevWord_factor_denominator_ne_zero (b :: bs)
    0 n hden hperiod hz
  have hshift := faddeevS_add_one
    (z / fltDenominator (letterWord (b :: bs) : Mat(2, ℤ)) τ - (n + 1 : ℤ))
    (flt (letterWord (b :: bs) : Mat(2, ℤ)) τ) hperiod
    (by convert hgamma using 1; push_cast; ring_nf)
  have hphase := faddeevWord_head_phase a (b :: bs) n (z := z) hden
    (Complex.slitPlane_ne_zero hperiod)
  rw [faddeevWord_cons_cons, faddeevWord_cons_cons]
  calc
    faddeevS (z / fltDenominator (letterWord (b :: bs) : Mat(2, ℤ)) τ -
        (n + 1 : ℤ)) (flt (letterWord (b :: bs) : Mat(2, ℤ)) τ) *
        faddeevWord (b :: bs) m 0 z τ =
      (faddeevS (z / fltDenominator (letterWord (b :: bs) : Mat(2, ℤ)) τ - n)
          (flt (letterWord (b :: bs) : Mat(2, ℤ)) τ) *
        (1 - Complex.exp (2 * Real.pi * Complex.I *
          ((z / fltDenominator (letterWord (b :: bs) : Mat(2, ℤ)) τ - n) /
            flt (letterWord (b :: bs) : Mat(2, ℤ)) τ)))) *
        faddeevWord (b :: bs) m 0 z τ := by
          rw [← hshift]
          congr 1
          push_cast
          ring_nf
    _ = _ := by rw [hphase]; ring_nf

/-- The right index shift `Φ_{γ,m,n+1}(z;τ)=(1-q̃^n e(z/(cτ+d)))Φ_{γ,m,n}(z;τ)`,
`q̃=e(γ·τ)`, of [RW26, Radchenko, Wheeler (2026), Section 2.2] for the word product, at
slit-plane word periods and `z∉ℤ+ℤτ`. -/
theorem faddeevWord_index_add_one_right (bs : List ℤ) (hbs : bs ≠ []) (m n : ℤ) {z τ : ℂ}
    (hτ : FaddeevWordPeriodsSlitPlane bs τ) (hz : ¬ IsPeriodLatticePoint τ z) :
    faddeevWord bs m (n + 1) z τ =
      (1 - Complex.exp (2 * Real.pi * Complex.I *
        (z / fltDenominator (letterWord bs : Mat(2, ℤ)) τ +
          n * flt (letterWord bs : Mat(2, ℤ)) τ))) *
        faddeevWord bs m n z τ := by
  cases bs with
  | nil => contradiction
  | cons a bs =>
      cases bs with
      | nil => exact faddeevWord_index_add_one_right_singleton a m n hτ hz
      | cons b bs => exact faddeevWord_index_add_one_right_cons a b bs m n hτ hz

/-! ### Simultaneous index shifts at a fixed point

At `γ·τ=τ` the phase condition makes the multipliers of the two index shifts equal at every
step, so the simultaneous shift needs no division. -/

/-- Equation (16): if `γ·τ=τ` and `q^m e(z)=q^n e(z/(cτ+d))`, then
`Φ_{γ,m+k,n+k}(z;τ)=Φ_{γ,m,n}(z;τ)` for every integer `k`. Stated for the word product at
slit-plane word periods and `z∉ℤ+ℤτ`. [RW26, Radchenko, Wheeler (2026), equation (16),
`eq:faddeevperiod`]. -/
@[source "RW26, equation (16), p. 6, eq:faddeevperiod (off the period lattice)"]
theorem faddeevWord_indices_add (bs : List ℤ) (hbs : bs ≠ []) (m n k : ℤ) {z τ : ℂ}
    (hτ : FaddeevWordPeriodsSlitPlane bs τ) (hfix : flt (letterWord bs : Mat(2, ℤ)) τ = τ)
    (hz : ¬ IsPeriodLatticePoint τ z)
    (hphase : Complex.exp (2 * Real.pi * Complex.I * (z + m * τ)) =
      Complex.exp (2 * Real.pi * Complex.I *
        (z / fltDenominator (letterWord bs : Mat(2, ℤ)) τ + n * τ))) :
    faddeevWord bs (m + k) (n + k) z τ = faddeevWord bs m n z τ := by
  have hphase_shift (j : ℤ) :
      Complex.exp (2 * Real.pi * Complex.I * (z + (m + j) * τ)) =
      Complex.exp (2 * Real.pi * Complex.I *
        (z / fltDenominator (letterWord bs : Mat(2, ℤ)) τ +
          (n + j) * flt (letterWord bs : Mat(2, ℤ)) τ)) := by
    calc
      _ = Complex.exp (2 * Real.pi * Complex.I * (z + m * τ)) *
          Complex.exp (2 * Real.pi * Complex.I * (j * τ)) := by
            rw [← Complex.exp_add]
            congr 1
            ring_nf
      _ = Complex.exp (2 * Real.pi * Complex.I *
            (z / fltDenominator (letterWord bs : Mat(2, ℤ)) τ + n * τ)) *
          Complex.exp (2 * Real.pi * Complex.I * (j * τ)) := by rw [hphase]
      _ = _ := by
        rw [← Complex.exp_add, hfix]
        congr 1
        ring_nf
  have hstep (j : ℤ) :
      faddeevWord bs (m + (j + 1)) (n + (j + 1)) z τ =
        faddeevWord bs (m + j) (n + j) z τ := by
    have hR := faddeevWord_index_add_one_right bs hbs (m + j + 1) (n + j) hτ hz
    have hL := faddeevWord_index_add_one_left bs hbs (m + j) (n + j) hτ hz
    calc
      _ = (1 - Complex.exp (2 * Real.pi * Complex.I *
            (z / fltDenominator (letterWord bs : Mat(2, ℤ)) τ +
              (n + j) * flt (letterWord bs : Mat(2, ℤ)) τ))) *
          faddeevWord bs (m + j + 1) (n + j) z τ := by
            simpa only [add_assoc, Int.cast_add] using hR
      _ = faddeevWord bs (m + j + 1) (n + j) z τ *
            (1 - Complex.exp (2 * Real.pi * Complex.I * (z + (m + j) * τ))) := by
              rw [← hphase_shift j]; ring_nf
      _ = _ := by simpa only [add_assoc, Int.cast_add] using hL
  induction k using Int.induction_on with
  | zero => simp
  | succ i ih => exact (hstep i).trans ih
  | pred i ih =>
      have hp := hstep (-(i : ℤ) - 1)
      have hp' : faddeevWord bs (m + -(i : ℤ)) (n + -(i : ℤ)) z τ =
          faddeevWord bs (m + (-(i : ℤ) - 1)) (n + (-(i : ℤ) - 1)) z τ := by
        simpa only [sub_add_cancel] using hp
      exact hp'.symm.trans ih

/-! ### Lattice shifts

A lattice translation of `z` becomes a lattice translation of each `z_j`; the coordinates
along the word are absorbed by the indices and returned to zero by the first intermediate
index. -/

/-- The head-factor argument transport used by `faddeevWord_add_lattice`. -/
private lemma faddeevWord_factor_add_lattice (W : SL(2, ℤ)) (n p q : ℤ) {z τ : ℂ}
    (hden : fltDenominator (W : Mat(2, ℤ)) τ ≠ 0) :
    (z + p * τ + q) / fltDenominator (W : Mat(2, ℤ)) τ - n =
      z / fltDenominator (W : Mat(2, ℤ)) τ +
        (p * W 1 1 - q * W 1 0) * flt (W : Mat(2, ℤ)) τ -
          (n - (q * W 0 0 - p * W 0 1)) := by
  rw [show z + (p : ℂ) * τ + q = z + (q + (p : ℂ) * τ) by ring_nf,
    add_div, intCast_add_intCast_mul_div_fltDenominator W τ hden q p]
  push_cast
  ring_nf

/-- The lower-row index after peeling a letter, used by `faddeevWord_add_lattice`. -/
private lemma letterWord_cons_shift_index (a : ℤ) (w : List ℤ) (n p q : ℤ) :
    n + p * letterWord (a :: w) 1 1 - q * letterWord (a :: w) 1 0 =
      n - (q * letterWord w 0 0 - p * letterWord w 0 1) := by
  rw [letterWord_cons_apply_one, letterWord_cons_apply_one]
  ring

/-- The induction step of `faddeevWord_add_lattice` for a nonempty suffix. -/
private theorem faddeevWord_add_lattice_cons (a b : ℤ) (bs : List ℤ)
    (m n p q : ℤ) {z τ : ℂ}
    (hτ : FaddeevWordPeriodsSlitPlane (a :: b :: bs) τ)
    (hz : ¬ IsPeriodLatticePoint τ z)
    (hrest : faddeevWord (b :: bs) m 0 (z + p * τ + q) τ =
      faddeevWord (b :: bs) (m + p)
        (p * letterWord (b :: bs) 1 1 - q * letterWord (b :: bs) 1 0) z τ) :
    faddeevWord (a :: b :: bs) m n (z + p * τ + q) τ =
      faddeevWord (a :: b :: bs) (m + p)
        (n + p * letterWord (a :: b :: bs) 1 1 -
          q * letterWord (a :: b :: bs) 1 0) z τ := by
  let W := letterWord (b :: bs)
  let p' : ℤ := p * W 1 1 - q * W 1 0
  let q' : ℤ := q * W 0 0 - p * W 0 1
  obtain ⟨⟨hden, _⟩, _⟩ := (faddeevWordPeriodsSlitPlane_cons_cons a b bs τ).mp hτ
  have harg :
      (z + p * τ + q) / fltDenominator (W : Mat(2, ℤ)) τ - n =
        z / fltDenominator (W : Mat(2, ℤ)) τ +
          p' * flt (W : Mat(2, ℤ)) τ - (n - q') := by
    simpa only [p', q', Int.cast_sub, Int.cast_mul] using
      (faddeevWord_factor_add_lattice W n p q (z := z) hden)
  have hindex : n + p * letterWord (a :: b :: bs) 1 1 -
      q * letterWord (a :: b :: bs) 1 0 = n - q' :=
    letterWord_cons_shift_index a (b :: bs) n p q
  calc
    faddeevWord (a :: b :: bs) m n (z + p * τ + q) τ =
        faddeevS ((z + p * τ + q) / fltDenominator (W : Mat(2, ℤ)) τ - n)
          (flt (W : Mat(2, ℤ)) τ) *
          faddeevWord (b :: bs) m 0 (z + p * τ + q) τ :=
            faddeevWord_cons_cons a b bs m n _ τ
    _ = faddeevS (z / fltDenominator (W : Mat(2, ℤ)) τ +
          p' * flt (W : Mat(2, ℤ)) τ - (n - q'))
          (flt (W : Mat(2, ℤ)) τ) *
          faddeevWord (b :: bs) (m + p) p' z τ := by
            rw [harg]
            exact congrArg _ hrest
    _ = faddeevWord (a :: b :: bs) (m + p)
          (n + p * letterWord (a :: b :: bs) 1 1 -
            q * letterWord (a :: b :: bs) 1 0) z τ := by
            rw [hindex]
            simpa only [Int.cast_sub] using
              (faddeevWord_cons_cons_eq_index a b bs (m + p) (n - q') p' hτ hz).symm

/-- The lattice shift `Φ_{γ,m,n}(z+pτ+q;τ)=Φ_{γ,m+p,n+pd-qc}(z;τ)` for `γ=(a b; c d)`, at
slit-plane word periods and `z∉ℤ+ℤτ`. [RW26, Radchenko, Wheeler (2026), Section 2.2] states the
four cases `(p,q)=(1,0),(0,1),(c,d),(a,b)`. -/
theorem faddeevWord_add_lattice (bs : List ℤ) (hbs : bs ≠ []) (m n p q : ℤ) {z τ : ℂ}
    (hτ : FaddeevWordPeriodsSlitPlane bs τ) (hz : ¬ IsPeriodLatticePoint τ z) :
    faddeevWord bs m n (z + p * τ + q) τ =
      faddeevWord bs (m + p) (n + p * letterWord bs 1 1 - q * letterWord bs 1 0) z τ := by
  induction bs generalizing m n p q with
  | nil => contradiction
  | cons a bs ih =>
      cases bs with
      | nil =>
          have hrow10 : letterWord [a] 1 0 = 1 := by
            simp
          have hrow11 : letterWord [a] 1 1 = 0 := by
            simp
          rw [faddeevWord_singleton, faddeevWord_singleton, hrow10, hrow11]
          push_cast
          ring_nf
      | cons b bs =>
          obtain ⟨_, htail⟩ :=
            (faddeevWordPeriodsSlitPlane_cons_cons a b bs τ).mp hτ
          exact faddeevWord_add_lattice_cons a b bs m n p q hτ hz
            (by simpa only [zero_add] using ih (by simp) m 0 p q htail)

/-! ### Identities of meromorphic germs

Both sides are meromorphic in the argument at slit-plane word periods and agree off the
countable period lattice. -/

/-- The germ form of `faddeevWord_index_add_one_left`. -/
theorem faddeevWord_index_add_one_left_eventuallyEq (bs : List ℤ) (hbs : bs ≠ [])
    (m n : ℤ) {τ : ℂ} (hτ : FaddeevWordPeriodsSlitPlane bs τ) (z : ℂ) :
    (fun w => faddeevWord bs (m + 1) n w τ *
        (1 - Complex.exp (2 * Real.pi * Complex.I * (w + m * τ)))) =ᶠ[𝓝[≠] z]
      (fun w => faddeevWord bs m n w τ) := by
  have hanalytic : AnalyticAt ℂ
      (fun w : ℂ => 1 - Complex.exp (2 * Real.pi * Complex.I * (w + m * τ))) z := by
    fun_prop
  exact MeromorphicAt.eventuallyEq_nhdsNE_of_countable
    ((meromorphicAt_faddeevWord bs (m + 1) n hτ z).mul hanalytic.meromorphicAt)
    (meromorphicAt_faddeevWord bs m n hτ z)
    (countable_setOf_isPeriodLatticePoint τ)
    (fun w hw => faddeevWord_index_add_one_left bs hbs m n hτ hw)

/-- The germ form of `faddeevWord_index_add_one_right`. -/
theorem faddeevWord_index_add_one_right_eventuallyEq (bs : List ℤ) (hbs : bs ≠ [])
    (m n : ℤ) {τ : ℂ} (hτ : FaddeevWordPeriodsSlitPlane bs τ) (z : ℂ) :
    (fun w => faddeevWord bs m (n + 1) w τ) =ᶠ[𝓝[≠] z]
      (fun w => (1 - Complex.exp (2 * Real.pi * Complex.I *
        (w / fltDenominator (letterWord bs : Mat(2, ℤ)) τ +
          n * flt (letterWord bs : Mat(2, ℤ)) τ))) * faddeevWord bs m n w τ) := by
  have hanalytic : AnalyticAt ℂ
      (fun w : ℂ => 1 - Complex.exp (2 * Real.pi * Complex.I *
        (w / fltDenominator (letterWord bs : Mat(2, ℤ)) τ +
          n * flt (letterWord bs : Mat(2, ℤ)) τ))) z := by
    fun_prop
  exact MeromorphicAt.eventuallyEq_nhdsNE_of_countable
    (meromorphicAt_faddeevWord bs m (n + 1) hτ z)
    (hanalytic.meromorphicAt.mul (meromorphicAt_faddeevWord bs m n hτ z))
    (countable_setOf_isPeriodLatticePoint τ)
    (fun w hw => faddeevWord_index_add_one_right bs hbs m n hτ hw)

/-- The germ form of `faddeevWord_add_lattice`. -/
theorem faddeevWord_add_lattice_eventuallyEq (bs : List ℤ) (hbs : bs ≠ [])
    (m n p q : ℤ) {τ : ℂ} (hτ : FaddeevWordPeriodsSlitPlane bs τ) (z : ℂ) :
    (fun w => faddeevWord bs m n (w + p * τ + q) τ) =ᶠ[𝓝[≠] z]
      (fun w => faddeevWord bs (m + p)
        (n + p * letterWord bs 1 1 - q * letterWord bs 1 0) w τ) := by
  have hcomp :=
    (meromorphicAt_faddeevWord bs m n hτ (z + p * τ + q)).comp_analyticAt
      (g := fun w : ℂ => w + p * τ + q) (by fun_prop)
  exact MeromorphicAt.eventuallyEq_nhdsNE_of_countable hcomp
    (meromorphicAt_faddeevWord bs (m + p)
      (n + p * letterWord bs 1 1 - q * letterWord bs 1 0) hτ z)
    (countable_setOf_isPeriodLatticePoint τ)
    (fun w hw => faddeevWord_add_lattice bs hbs m n p q hτ hw)

end SIC
