/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.Faddeev.Generator
import Mathlib.Analysis.Meromorphic.Order

/-!
# The divisor of the Faddeev generator

The zero sets of the two gamma factors, exact lattice orders at irrational periods, same-sign
nonvanishing of the gamma factors at complex slit-plane periods, and finite-path period-one shifts
of the Faddeev generator.

This module follows [RW26, Radchenko, Wheeler (2026), Section 2.1]: the zeros of
`Φ_{S,0,0}(z;τ)` are `ℤ_{<0} + τ ℤ_{≤0}`, and its poles are
`ℤ_{≥0} + τ ℤ_{>0}`. The gamma quotient has numerator `Γ₂(z+1;1,τ)⁻¹`
and denominator `Γ₂(τ-z;1,τ)⁻¹`. Their zero sets follow from the negative cone
lattice in [95, Shintani (1977), Proposition 1].

## The argument

Both gamma factors are entire. The order of the quotient is the difference of their
orders; its entire, nonzero exponential factor changes neither the zeros nor the poles.
At irrational positive periods, unique lattice coordinates and the simple Barnes zeros
give exact orders: the indicator of the numerator cone minus that of the denominator
cone is `1_{k≤0} - 1_{ℓ≥0}` at `kτ+ℓ`. At rational periods Barnes zeros may overlap, and no
multiplicities are asserted.

Totalized division gives value zero at a pole as well as at a zero. The pointwise zero criterion
below explicitly includes both sets. Away from `ℤτ+ℤ`, the generator is nonzero and analytic for
every slit-plane period. More generally, each divisor cone has
`Im z Im(z/τ) ≤ 0`, so both gamma factors are nonzero in the two strict same-sign cones. The
period-one law then iterates along any finite integer path on which its gamma denominators and
negative-index finite-product factors are nonzero. Positive-cone hypotheses supply those conditions
at complex periods; at positive real periods, nonreal arguments make every finite shift path
regular.
-/

noncomputable section

namespace SIC

/-! ### Affine changes of the generator

The generator remains meromorphic under an affine change of argument. A nonconstant
affine map has nonzero derivative, so composition preserves the local meromorphic order.
-/

/-- The Faddeev generator remains meromorphic after an affine change of argument.
This composes `meromorphicAt_faddeevS` with an analytic affine map. -/
theorem meromorphicAt_faddeevS_div_add (τ : ℂ) (hτ : τ ∈ Complex.slitPlane)
    (q c z : ℂ) : MeromorphicAt (fun w : ℂ => faddeevS (w / q + c) τ) z := by
  exact (meromorphicAt_faddeevS (z / q + c) τ hτ).comp_analyticAt
    (g := fun w : ℂ => w / q + c) ((analyticAt_id.div_const).add analyticAt_const)

/-- A nonconstant affine change of argument preserves the Faddeev generator order.
This is `meromorphicOrderAt_comp_of_deriv_ne_zero` for that affine map. -/
theorem meromorphicOrderAt_faddeevS_div_add (τ q c z : ℂ) (hq : q ≠ 0) :
    meromorphicOrderAt (fun w : ℂ => faddeevS (w / q + c) τ) z =
      meromorphicOrderAt (fun w : ℂ => faddeevS w τ) (z / q + c) := by
  have ha : AnalyticAt ℂ (fun w : ℂ => w / q + c) z :=
    (analyticAt_id.div_const).add analyticAt_const
  have hderiv : deriv (fun w : ℂ => w / q + c) z ≠ 0 := by
    simpa [deriv_add_const, deriv_div_const] using
      (div_ne_zero (one_ne_zero : (1 : ℂ) ≠ 0) hq)
  simpa only [Function.comp_def] using
    (meromorphicOrderAt_comp_of_deriv_ne_zero
      (f := fun w : ℂ => faddeevS w τ) ha hderiv)

/-! ### The two gamma factors

Rewriting the cone lattice with two natural coordinates identifies the two source
sets before any quotient or meromorphic order is taken.
-/

/-- The natural-coordinate form of the inverse gamma cone, used by
`faddeevS_numerator_eq_zero_iff` and `faddeevS_denominator_eq_zero_iff`. -/
private lemma barnesDoubleGammaInv_eq_zero_iff_nat (u τ : ℂ)
    (hτ : τ ∈ Complex.slitPlane) :
    barnesDoubleGammaInv u 1 τ = 0 ↔
      ∃ a b : ℕ, u = -((a : ℂ) + b * τ) := by
  rw [barnesDoubleGammaInv_eq_zero_iff u τ hτ]
  constructor
  · rintro (hu | ⟨p, hp⟩)
    · exact ⟨0, 0, by simp [hu]⟩
    · exact ⟨p.1.1, p.1.2, by simpa [barnesDoubleGammaLatticePoint] using hp⟩
  · rintro ⟨a, b, hu⟩
    by_cases hab : (a, b) = (0, 0)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hab
      exact Or.inl (by simpa using hu)
    · exact Or.inr ⟨⟨(a, b), hab⟩, by simpa [barnesDoubleGammaLatticePoint] using hu⟩

/-- The numerator zeros of `Φ(z;τ)` are `z = -(a+1)-bτ`, with `a,b ∈ ℕ`.
This rewrites `barnesDoubleGammaInv_eq_zero_iff` in the coordinates
of [RW26, Radchenko, Wheeler (2026), Section 2.1]. -/
theorem faddeevS_numerator_eq_zero_iff (z τ : ℂ) (hτ : τ ∈ Complex.slitPlane) :
    barnesDoubleGammaInv (z + 1) 1 τ = 0 ↔
      ∃ a b : ℕ, z = -((a : ℂ) + 1) - b * τ := by
  rw [barnesDoubleGammaInv_eq_zero_iff_nat _ τ hτ]
  constructor
  · rintro ⟨a, b, h⟩
    exact ⟨a, b, by linear_combination h⟩
  · rintro ⟨a, b, h⟩
    exact ⟨a, b, by linear_combination h⟩

/-- The denominator zeros of `Φ(z;τ)` are `z = a+(b+1)τ`, with `a,b ∈ ℕ`.
This rewrites `barnesDoubleGammaInv_eq_zero_iff` in the coordinates
of [RW26, Radchenko, Wheeler (2026), Section 2.1]. -/
theorem faddeevS_denominator_eq_zero_iff (z τ : ℂ) (hτ : τ ∈ Complex.slitPlane) :
    barnesDoubleGammaInv (τ - z) 1 τ = 0 ↔
      ∃ a b : ℕ, z = a + ((b : ℂ) + 1) * τ := by
  rw [barnesDoubleGammaInv_eq_zero_iff_nat _ τ hτ]
  constructor
  · rintro ⟨a, b, h⟩
    exact ⟨a, b, by linear_combination -h⟩
  · rintro ⟨a, b, h⟩
    exact ⟨a, b, by linear_combination -h⟩

/-- The totalized value `Φ(z;τ)` is zero at the union of the source's zero and pole
sets. At a pole, this is the default value of division, not a meromorphic zero.
The two sets are those of [RW26, Radchenko, Wheeler (2026), Section 2.1]. -/
theorem faddeevS_eq_zero_iff (z τ : ℂ) (hτ : τ ∈ Complex.slitPlane) :
    faddeevS z τ = 0 ↔
      (∃ a b : ℕ, z = -((a : ℂ) + 1) - b * τ) ∨
        (∃ a b : ℕ, z = a + ((b : ℂ) + 1) * τ) := by
  have hquot : faddeevS z τ = 0 ↔
      barnesDoubleGammaInv (z + 1) 1 τ = 0 ∨
        barnesDoubleGammaInv (τ - z) 1 τ = 0 := by
    simp [faddeevS, shintaniDoubleSineGamma, barnesDoubleSineGamma,
      show (1 : ℂ) + τ - (z + 1) = τ - z by ring]
  exact hquot.trans ((faddeevS_numerator_eq_zero_iff z τ hτ).or
    (faddeevS_denominator_eq_zero_iff z τ hτ))

/-! ### Cone regularity at complex periods

A point in either divisor cone has opposite weak signs in its original and divided
imaginary coordinates. Thus both gamma factors are nonzero when these two coordinates have the
same strict sign.
-/

/-- A point `a + bτ` in the nonnegative period cone satisfies
`Im(a+bτ) Im((a+bτ)/τ) ≤ 0`. Used by both gamma-factor cone criteria. -/
private lemma periodCone_im_mul_div_im_nonpos (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (τ : ℂ) :
    ((a : ℂ) + (b : ℂ) * τ).im * (((a : ℂ) + (b : ℂ) * τ) / τ).im ≤ 0 := by
  have him : ((a : ℂ) + (b : ℂ) * τ).im = b * τ.im := by
    simp [Complex.mul_im]
  have hdiv : (((a : ℂ) + (b : ℂ) * τ) / τ).im =
      -a * τ.im / Complex.normSq τ := by
    rw [Complex.div_im]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.add_re, Complex.ofReal_re, zero_mul, add_zero, Complex.mul_re]
    ring
  rw [him, hdiv]
  have hprod : b * τ.im * (-a * τ.im) ≤ 0 := by
    rw [show b * τ.im * (-a * τ.im) = -(a * b * τ.im ^ 2) by ring]
    exact neg_nonpos.mpr (mul_nonneg (mul_nonneg ha hb) (sq_nonneg _))
  simpa only [mul_div_assoc] using
    div_nonpos_of_nonpos_of_nonneg hprod (Complex.normSq_nonneg τ)

/-- The numerator gamma factor is nonzero when `Im z` and `Im (z / τ)` have the same strict
sign. This is the sign complement of `faddeevS_numerator_eq_zero_iff`. -/
theorem faddeevS_numerator_ne_zero_of_same_sign (z τ : ℂ)
    (hτ : τ ∈ Complex.slitPlane) (hsign : 0 < z.im * (z / τ).im) :
    barnesDoubleGammaInv (z + 1) 1 τ ≠ 0 := by
  intro hzero
  obtain ⟨a, b, hz⟩ := (faddeevS_numerator_eq_zero_iff z τ hτ).mp hzero
  let w : ℂ := (((a : ℝ) + 1 : ℝ) : ℂ) + (b : ℝ) * τ
  have hcone := periodCone_im_mul_div_im_nonpos
    ((a : ℝ) + 1) b (by positivity) (Nat.cast_nonneg b) τ
  have hw : w.im * (w / τ).im ≤ 0 := by simpa [w] using hcone
  have hneg : (-w).im * ((-w) / τ).im ≤ 0 := by
    calc
      _ = w.im * (w / τ).im := by rw [neg_div, Complex.neg_im, Complex.neg_im]; ring
      _ ≤ 0 := hw
  have hzw : z = -w := by rw [hz]; dsimp [w]; push_cast; ring
  exact (not_lt_of_ge (by simpa only [hzw] using hneg)) hsign

/-- The denominator gamma factor is nonzero when `Im z` and `Im (z / τ)` have the same strict
sign. This is the sign complement of `faddeevS_denominator_eq_zero_iff`. -/
theorem faddeevS_denominator_ne_zero_of_same_sign (z τ : ℂ)
    (hτ : τ ∈ Complex.slitPlane) (hsign : 0 < z.im * (z / τ).im) :
    barnesDoubleGammaInv (τ - z) 1 τ ≠ 0 := by
  intro hzero
  obtain ⟨a, b, hz⟩ := (faddeevS_denominator_eq_zero_iff z τ hτ).mp hzero
  have hcone := periodCone_im_mul_div_im_nonpos
    a ((b : ℝ) + 1) (Nat.cast_nonneg a) (by positivity) τ
  rw [hz] at hsign
  exact (not_lt_of_ge (by simpa only [Complex.ofReal_natCast, Complex.ofReal_add,
    Complex.ofReal_one] using hcone)) hsign

/-- In the positive imaginary cone, the denominator gamma factor is nonzero.
This specializes `faddeevS_denominator_ne_zero_of_same_sign`. -/
theorem faddeevS_denominator_ne_zero_of_pos_im (z τ : ℂ)
    (hτ : τ ∈ Complex.slitPlane) (hz : 0 < z.im) (hdiv : 0 < (z / τ).im) :
    barnesDoubleGammaInv (τ - z) 1 τ ≠ 0 :=
  faddeevS_denominator_ne_zero_of_same_sign z τ hτ (mul_pos hz hdiv)

/-- In the negative imaginary cone, the numerator gamma factor is nonzero.
This specializes `faddeevS_numerator_ne_zero_of_same_sign`. -/
theorem faddeevS_numerator_ne_zero_of_neg_im (z τ : ℂ)
    (hτ : τ ∈ Complex.slitPlane) (hz : z.im < 0) (hdiv : (z / τ).im < 0) :
    barnesDoubleGammaInv (z + 1) 1 τ ≠ 0 :=
  faddeevS_numerator_ne_zero_of_same_sign z τ hτ (mul_pos_of_neg_of_neg hz hdiv)

/-- In the negative imaginary cone, the denominator gamma factor is nonzero.
This specializes `faddeevS_denominator_ne_zero_of_same_sign`. -/
theorem faddeevS_denominator_ne_zero_of_neg_im (z τ : ℂ)
    (hτ : τ ∈ Complex.slitPlane) (hz : z.im < 0) (hdiv : (z / τ).im < 0) :
    barnesDoubleGammaInv (τ - z) 1 τ ≠ 0 :=
  faddeevS_denominator_ne_zero_of_same_sign z τ hτ (mul_pos_of_neg_of_neg hz hdiv)

/-! ### Meromorphic orders

The order of the generator is the difference of the orders of its two entire gamma factors.
Its sign distinguishes a genuine zero from a pole, independently of the chosen totalized values.
-/

/-- Both gamma factors are entire, by the Barnes product theorem. Used by
`faddeevS_order_eq_sub`. -/
private lemma faddeevS_gamma_analytic (z τ : ℂ) (hτ : τ ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun w => barnesDoubleGammaInv (w + 1) 1 τ) z ∧
      AnalyticAt ℂ (fun w => barnesDoubleGammaInv (τ - w) 1 τ) z := by
  have hbase := differentiable_barnesDoubleGammaInv τ hτ
  constructor
  · simpa only [Function.comp_def] using
      (hbase.analyticAt (z + 1)).comp (f := fun w : ℂ => w + 1) (by fun_prop)
  · have h := analyticAt_barnesDoubleGammaInv_reflect (z + 1) τ hτ
    convert h.comp (f := fun w : ℂ => w + 1) (by fun_prop) using 1
    ext w
    congr 1
    ring

/-- The exponential in the Faddeev generator has order zero, leaving the
difference of the gamma-factor orders. Used by `meromorphicOrderAt_faddeevS_real_lattice`. -/
private lemma faddeevS_order_eq_sub (z τ : ℂ) (hτ : τ ∈ Complex.slitPlane) :
    meromorphicOrderAt (fun w => faddeevS w τ) z =
      meromorphicOrderAt (fun w => barnesDoubleGammaInv (w + 1) 1 τ) z -
        meromorphicOrderAt (fun w => barnesDoubleGammaInv (τ - w) 1 τ) z := by
  obtain ⟨hn, hd⟩ := faddeevS_gamma_analytic z τ hτ
  have he : AnalyticAt ℂ (fun w => Complex.exp (-faddeevSExpArg w τ)) z :=
    analyticAt_exp_neg_faddeevSExpArg z τ
  have heorder : meromorphicOrderAt
      (fun w => Complex.exp (-faddeevSExpArg w τ)) z = 0 := by
    rw [he.meromorphicOrderAt_eq, (he.analyticOrderAt_eq_zero).2 (Complex.exp_ne_zero _)]
    simp
  have hfun : (fun w => faddeevS w τ) =
      (fun w => barnesDoubleGammaInv (w + 1) 1 τ /
        barnesDoubleGammaInv (τ - w) 1 τ) *
        (fun w => Complex.exp (-faddeevSExpArg w τ)) := by
    funext w
    simp only [faddeevS, shintaniDoubleSineGamma, barnesDoubleSineGamma,
      Pi.mul_apply, show (1 : ℂ) + τ - (w + 1) = τ - w by ring]
  rw [hfun]
  change meromorphicOrderAt
    (((fun w => barnesDoubleGammaInv (w + 1) 1 τ) /
      (fun w => barnesDoubleGammaInv (τ - w) 1 τ)) *
      (fun w => Complex.exp (-faddeevSExpArg w τ))) z = _
  rw [meromorphicOrderAt_mul (hn.meromorphicAt.div hd.meromorphicAt)
    he.meromorphicAt, meromorphicOrderAt_div hn.meromorphicAt hd.meromorphicAt,
    heorder, add_zero]

/-! ### Exact orders at irrational periods

The cone coordinates are unique for irrational `τ`. The simple Barnes zeros then give
order one in the numerator cone and minus one in the denominator cone. Expressing these
as a difference of two half-plane indicators makes adjacent-factor cancellation explicit.
-/

/-- On the irrational lattice, the numerator gamma cone is `k ≤ 0, ℓ < 0`.
This is the coordinate form of `faddeevS_numerator_eq_zero_iff`. -/
private lemma faddeevS_numerator_lattice_iff (τ : ℝ) (hτ : 0 < τ)
    (hirr : Irrational τ) (k l : ℤ) :
    barnesDoubleGammaInv ((k : ℂ) * τ + l + 1) 1 τ = 0 ↔
      k ≤ 0 ∧ l < 0 := by
  rw [faddeevS_numerator_eq_zero_iff _ _ (Complex.ofReal_mem_slitPlane.mpr hτ)]
  constructor
  · rintro ⟨a, b, h⟩
    have heq : (k : ℂ) * τ + l =
        ((-(b : ℤ) : ℤ) : ℂ) * τ + ((-(a : ℤ) - 1 : ℤ) : ℂ) := by
      rw [h]
      push_cast
      ring
    have hcoords :=
      (intCast_add_intCast_mul_eq_iff_of_irrational τ hirr l k
        (-(a : ℤ) - 1) (-(b : ℤ))).mp (by simpa only [add_comm] using heq)
    obtain ⟨hl, hk⟩ := hcoords
    constructor <;> omega
  · rintro ⟨hk, hl⟩
    let a : ℕ := Int.toNat (-l - 1)
    let b : ℕ := Int.toNat (-k)
    refine ⟨a, b, ?_⟩
    have ha : (a : ℤ) = -l - 1 := Int.toNat_of_nonneg (by omega)
    have hb : (b : ℤ) = -k := Int.toNat_of_nonneg (by omega)
    have ha' : (a : ℂ) = -(l : ℂ) - 1 := by exact_mod_cast ha
    have hb' : (b : ℂ) = -(k : ℂ) := by exact_mod_cast hb
    rw [ha', hb']
    ring

/-- On the irrational lattice, the denominator gamma cone is `k > 0, ℓ ≥ 0`.
This is the coordinate form of `faddeevS_denominator_eq_zero_iff`. -/
private lemma faddeevS_denominator_lattice_iff (τ : ℝ) (hτ : 0 < τ)
    (hirr : Irrational τ) (k l : ℤ) :
    barnesDoubleGammaInv ((τ : ℂ) - ((k : ℂ) * τ + l)) 1 τ = 0 ↔
      0 < k ∧ 0 ≤ l := by
  rw [faddeevS_denominator_eq_zero_iff _ _ (Complex.ofReal_mem_slitPlane.mpr hτ)]
  constructor
  · rintro ⟨a, b, h⟩
    have heq : (k : ℂ) * τ + l =
        (((b : ℤ) + 1 : ℤ) : ℂ) * τ + (a : ℂ) := by
      rw [h]
      push_cast
      ring
    have hcoords :=
      (intCast_add_intCast_mul_eq_iff_of_irrational τ hirr l k
        (a : ℤ) ((b : ℤ) + 1)).mp (by simpa only [add_comm, Int.cast_natCast] using heq)
    obtain ⟨hl, hk⟩ := hcoords
    constructor <;> omega
  · rintro ⟨hk, hl⟩
    let a : ℕ := Int.toNat l
    let b : ℕ := Int.toNat (k - 1)
    refine ⟨a, b, ?_⟩
    have ha : (a : ℤ) = l := Int.toNat_of_nonneg hl
    have hb : (b : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
    have ha' : (a : ℂ) = (l : ℂ) := by exact_mod_cast ha
    have hb' : (b : ℂ) = (k : ℂ) - 1 := by exact_mod_cast hb
    rw [ha', hb']
    ring

/-- At positive irrational `τ`, the order of `Φ(z;τ)` at `z = kτ+ℓ` is
`1_{k≤0} - 1_{ℓ≥0}`. This is the multiplicity form of the zero and pole sets in
[RW26, Radchenko, Wheeler (2026), Section 2.1], from the simple Barnes zeros. -/
theorem meromorphicOrderAt_faddeevS_real_lattice (τ : ℝ) (hτ : 0 < τ)
    (hirr : Irrational τ) (k l : ℤ) :
    meromorphicOrderAt (fun w => faddeevS w τ) ((k : ℂ) * τ + l) =
      (((if k ≤ 0 then (1 : ℤ) else 0) -
        (if 0 ≤ l then 1 else 0) : ℤ) : WithTop ℤ) := by
  let z : ℂ := (k : ℂ) * τ + l
  have hslit : (τ : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr hτ
  have hn : meromorphicOrderAt (fun w => barnesDoubleGammaInv (w + 1) 1 τ) z =
      if barnesDoubleGammaInv (z + 1) 1 τ = 0 then 1 else 0 := by
    simpa only [Function.comp_def] using
      (meromorphicOrderAt_comp_of_deriv_ne_zero
        (f := fun w => barnesDoubleGammaInv w 1 τ)
        (g := fun w : ℂ => w + 1) (by fun_prop) (by simp)).trans
        (meromorphicOrderAt_barnesDoubleGammaInv (z + 1) τ hτ hirr)
  have hd : meromorphicOrderAt (fun w => barnesDoubleGammaInv (τ - w) 1 τ) z =
      if barnesDoubleGammaInv (τ - z) 1 τ = 0 then 1 else 0 := by
    simpa only [Function.comp_def] using
      (meromorphicOrderAt_comp_of_deriv_ne_zero
        (f := fun w => barnesDoubleGammaInv w 1 τ)
        (g := fun w : ℂ => τ - w) (by fun_prop) (by simp)).trans
        (meromorphicOrderAt_barnesDoubleGammaInv (τ - z) τ hτ hirr)
  rw [show (k : ℂ) * τ + l = z from rfl, faddeevS_order_eq_sub z τ hslit, hn, hd]
  simp only [z, (faddeevS_numerator_lattice_iff τ hτ hirr k l),
    (faddeevS_denominator_lattice_iff τ hτ hirr k l)]
  by_cases hk : k ≤ 0
  · by_cases hl : 0 ≤ l
    · simp [hk, hl, show ¬l < 0 by omega, show ¬0 < k by omega]
    · have hl' : l < 0 := by omega
      simp [hk, hl, hl', show ¬0 < k by omega]
  · have hk' : 0 < k := by omega
    by_cases hl : 0 ≤ l
    · simp [hk, hk', hl, show ¬l < 0 by omega]
    · have hl' : l < 0 := by omega
      simp [hk, hk', hl, hl']

/-- Off `ℤτ+ℤ`, the generator is nonzero for every period in the slit plane.
This is the complement of the two lattice cones in `faddeevS_eq_zero_iff`. -/
theorem faddeevS_ne_zero_of_not_mem_lattice (z τ : ℂ) (hτ : τ ∈ Complex.slitPlane)
    (hz : ¬ IsPeriodLatticePoint τ z) : faddeevS z τ ≠ 0 := by
  have hz' := (not_isPeriodLatticePoint_iff τ z).mp hz
  intro hzero
  rcases (faddeevS_eq_zero_iff z τ hτ).mp hzero with
    ⟨a, b, ha⟩ | ⟨a, b, ha⟩
  · apply hz' (-(a : ℤ) - 1) (-(b : ℤ))
    rw [ha]
    push_cast
    ring
  · apply hz' (a : ℤ) ((b : ℤ) + 1)
    rw [ha]
    push_cast
    ring

/-- Off `ℤτ+ℤ`, the gamma denominator of the generator is nonzero.
This is the complement of the denominator cone in `faddeevS_denominator_eq_zero_iff`. -/
theorem faddeevS_denominator_ne_zero_of_not_mem_lattice (z τ : ℂ)
    (hτ : τ ∈ Complex.slitPlane) (hz : ¬ IsPeriodLatticePoint τ z) :
    barnesDoubleGammaInv (τ - z) 1 τ ≠ 0 := by
  intro hzero
  exact (faddeevS_ne_zero_of_not_mem_lattice z τ hτ hz)
    ((faddeevS_eq_zero_iff z τ hτ).2
      (Or.inr ((faddeevS_denominator_eq_zero_iff z τ hτ).1 hzero)))

/-- The Faddeev generator is analytic off the period lattice for every slit-plane period.
This applies `analyticAt_faddeevS` to the denominator-cone complement. -/
theorem analyticAt_faddeevS_of_not_mem_lattice (z τ : ℂ) (hτ : τ ∈ Complex.slitPlane)
    (hz : ¬ IsPeriodLatticePoint τ z) : AnalyticAt ℂ (fun w => faddeevS w τ) z := by
  exact analyticAt_faddeevS z τ hτ
    (faddeevS_denominator_ne_zero_of_not_mem_lattice z τ hτ hz)

/-- Off `ℤτ+ℤ`, the generator has order zero for every positive real `τ`.
This is the complement of the two cones in `faddeevS_eq_zero_iff`. -/
theorem meromorphicOrderAt_faddeevS_eq_zero (z : ℂ) (τ : ℝ)
    (hτ : 0 < τ) (hz : ¬ IsPeriodLatticePoint τ z) :
    meromorphicOrderAt (fun w => faddeevS w τ) z = 0 := by
  have hslit : (τ : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr hτ
  have hn := faddeevS_ne_zero_of_not_mem_lattice z τ hslit hz
  have han := analyticAt_faddeevS_of_not_mem_lattice z τ hslit hz
  rw [han.meromorphicOrderAt_eq, (han.analyticOrderAt_eq_zero).2 hn]
  simp

/-! ### Values off the real axis

Both cones lie on the real axis for real positive periods. This supplies the
regularity conditions needed by index transport along nonreal contours.
-/

/-- For real positive `τ` and nonreal `z`, the gamma denominator of `Φ(z;τ)`
is nonzero by `faddeevS_denominator_ne_zero_of_not_mem_lattice`. -/
theorem faddeevS_denominator_ne_zero_of_im_ne_zero (z : ℂ) (τ : ℝ)
    (hτ : 0 < τ) (hz : z.im ≠ 0) :
    barnesDoubleGammaInv ((τ : ℂ) - z) 1 τ ≠ 0 := by
  exact faddeevS_denominator_ne_zero_of_not_mem_lattice z τ
    (Complex.ofReal_mem_slitPlane.mpr hτ)
    (not_isPeriodLatticePoint_of_im_ne_zero z τ hz)

/-- A path of nonreal arguments at a positive real period satisfies the finite-path
domain condition of `faddeevS_transfer_int`. -/
theorem FaddeevSRegularPath.of_im_ne_zero {τ : ℝ} (hτ : 0 < τ)
    {r : ℤ} {arg : ℤ → ℂ}
    (h : ∀ j ∈ Set.uIcc (0 : ℤ) r, (arg j).im ≠ 0) :
    FaddeevSRegularPath τ r arg := by
  exact FaddeevSRegularPath.of_forall fun j hj =>
    faddeevS_denominator_ne_zero_of_im_ne_zero (arg j) τ hτ (h j hj)

/-! ### Finite shift paths

At a complex slit-plane period, the period-one law iterates along a finite integer path when each
encountered gamma denominator and required inverse finite-product factor is nonzero. The positive
cone supplies a reusable sufficient condition. At a positive real period, every nonreal integer
translate is regular, so the shift law needs no extra domain conditions.
-/

/-- If a value is unchanged at each integer in the half-open interval from `0` to `n`,
then its value at `n` equals its value at `0`. Used by the finite-path shift theorem. -/
private lemma eq_apply_zero_of_forall_Ico_step {X : Sort*} (f : ℤ → X) (n : ℤ) :
    (∀ j ∈ Set.Ico (min n 0) (max n 0), f (j + 1) = f j) → f n = f 0 := by
  intro hstep
  have hrel : Relation.ReflTransGen (fun i j : ℤ => f i = f j) n 0 :=
    reflTransGen_of_succ _
      (fun i hi => (hstep i (by rcases hi with ⟨hi0, hi1⟩; constructor <;> omega)).symm)
      (fun i hi => hstep i (by rcases hi with ⟨hi0, hi1⟩; constructor <;> omega))
  exact hrel.head_induction_on rfl (fun hab _ ih => hab.trans ih)

/-- One step of the finite-product identity used by
`faddeevS_add_intCast_mul_qPochhammerFin_of_regular`. -/
private lemma faddeevS_add_intCast_mul_qPochhammerFin_step (z τ : ℂ)
    (hτ : τ ∈ Complex.slitPlane) (j : ℤ)
    (hden : barnesDoubleGammaInv (τ - (z + j) - 1) 1 τ ≠ 0)
    (hfactor : j < 0 → 1 - Complex.exp (2 * Real.pi * Complex.I *
      ((z + 1) / τ + (j : ℂ) * τ⁻¹)) ≠ 0) :
    faddeevS (z + (j + 1 : ℤ)) τ *
      qPochhammerFin (j + 1) ((z + 1) / τ) τ⁻¹ =
    faddeevS (z + j) τ * qPochhammerFin j ((z + 1) / τ) τ⁻¹ := by
  let x : ℂ := (z + 1) / τ
  let q : ℂ := τ⁻¹
  let F : ℂ := 1 - Complex.exp (2 * Real.pi * Complex.I * (x + j * q))
  have harg : x + (j : ℂ) * q = (z + j + 1) / τ := by
    dsimp [x, q]
    simp only [div_eq_mul_inv]
    ring
  have hrec : qPochhammerFin (j + 1) x q = qPochhammerFin j x q * F :=
    qPochhammerFin_add_one j x q (fun hj => by simpa [F, x, q] using hfactor hj)
  have hshift : faddeevS (z + j + 1) τ * F = faddeevS (z + j) τ := by
    dsimp [F]
    rw [harg]
    simpa only [add_assoc] using faddeevS_add_one (z + j) τ hτ hden
  change faddeevS (z + (j + 1 : ℤ)) τ * qPochhammerFin (j + 1) x q =
    faddeevS (z + j) τ * qPochhammerFin j x q
  rw [hrec]
  calc
    _ = (faddeevS (z + j + 1) τ * F) * qPochhammerFin j x q := by push_cast; ring_nf
    _ = faddeevS (z + j) τ * qPochhammerFin j x q := by rw [hshift]

/-- The finite-path period-one shift identity for a slit-plane period. Each denominator and
each negative-index finite-product factor along the half-open integer path is assumed nonzero.
This iterates the period-one shift of [RW26, Radchenko, Wheeler (2026), Section 2.1]
(`faddeevS_add_one`). -/
theorem faddeevS_add_intCast_mul_qPochhammerFin_of_regular (z τ : ℂ)
    (hτ : τ ∈ Complex.slitPlane) (n : ℤ)
    (hden : ∀ j ∈ Set.Ico (min n 0) (max n 0),
      barnesDoubleGammaInv (τ - (z + j) - 1) 1 τ ≠ 0)
    (hfactor : ∀ j ∈ Set.Ico (min n 0) (max n 0),
      j < 0 → 1 - Complex.exp (2 * Real.pi * Complex.I *
        ((z + 1) / τ + (j : ℂ) * τ⁻¹)) ≠ 0) :
    faddeevS (z + n) τ * qPochhammerFin n ((z + 1) / τ) τ⁻¹ = faddeevS z τ := by
  let f : ℤ → ℂ := fun j =>
    faddeevS (z + j) τ * qPochhammerFin j ((z + 1) / τ) τ⁻¹
  have hf : f n = f 0 := eq_apply_zero_of_forall_Ico_step f n fun j hj =>
    faddeevS_add_intCast_mul_qPochhammerFin_step z τ hτ j
      (hden j hj) (hfactor j hj)
  simpa [f, qPochhammerFin] using hf

/-- The complex-period integer shift
`Φ(z+n;τ) ϖ_n((z+1)/τ, 1/τ) = Φ(z;τ)` in the positive imaginary cone.
The phase hypothesis keeps every finite factor and gamma denominator regular. -/
theorem faddeevS_add_intCast_mul_qPochhammerFin_of_pos_im (z τ : ℂ)
    (hτ : τ ∈ Complex.slitPlane) (hz : 0 < z.im) (n : ℤ)
    (hphase : ∀ j ∈ Set.Ico (min n 0) (max n 0),
      0 < ((z + 1) / τ + (j : ℂ) * τ⁻¹).im) :
    faddeevS (z + n) τ * qPochhammerFin n ((z + 1) / τ) τ⁻¹ = faddeevS z τ := by
  apply faddeevS_add_intCast_mul_qPochhammerFin_of_regular z τ hτ n
  · intro j hj
    have harg : (z + 1) / τ + (j : ℂ) * τ⁻¹ = (z + j + 1) / τ := by
      simp only [div_eq_mul_inv]
      ring
    have hzj : 0 < (z + j + 1).im := by simpa using hz
    have hdivj : 0 < ((z + j + 1) / τ).im := by rw [← harg]; exact hphase j hj
    simpa only [show τ - (z + j) - 1 = τ - (z + j + 1) by ring] using
      faddeevS_denominator_ne_zero_of_pos_im (z + j + 1) τ hτ hzj hdivj
  · intro j hj _hjneg
    exact one_sub_exp_two_pi_I_ne_zero_of_im_ne_zero (ne_of_gt (hphase j hj))

/-- The iterated period-one shift `Φ(z+n;τ) ϖ_n((z+1)/τ, 1/τ) = Φ(z;τ)` for every `n ∈ ℤ`,
at a positive real period and nonreal `z`: for `n ≥ 0` the finite symbol is
`∏_{k=1}^{n} (1 - e((z+k)/τ))`, and for `n < 0` its inverse convention gives the
downward shifts. This iterates the period-one shift of
[RW26, Radchenko, Wheeler (2026), Section 2.1] (`faddeevS_add_one`). -/
theorem faddeevS_add_intCast_mul_qPochhammerFin (z : ℂ) (τ : ℝ) (hτ : 0 < τ)
    (hz : z.im ≠ 0) (n : ℤ) :
    faddeevS (z + n) τ * qPochhammerFin n ((z + 1) / τ) (τ : ℂ)⁻¹ = faddeevS z τ := by
  apply faddeevS_add_intCast_mul_qPochhammerFin_of_regular z τ
    (Complex.ofReal_mem_slitPlane.mpr hτ) n
  · intro j _hj
    have him : (z + j + 1).im ≠ 0 := by simpa using hz
    simpa only [show (τ : ℂ) - (z + j) - 1 = (τ : ℂ) - (z + j + 1) by ring] using
      faddeevS_denominator_ne_zero_of_im_ne_zero (z + j + 1) τ hτ him
  · intro j _hj _hjneg
    apply one_sub_exp_two_pi_I_ne_zero_of_im_ne_zero
    have harg : (z + 1) / (τ : ℂ) + (j : ℂ) * (τ : ℂ)⁻¹ =
        (z + j + 1) / τ := by
      simp only [div_eq_mul_inv]
      ring
    rw [harg, Complex.div_ofReal_im]
    exact div_ne_zero (by simpa using hz) hτ.ne'

end SIC

end
