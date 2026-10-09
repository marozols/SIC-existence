/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.IsBoundedAtImInfty
import SICs.Analysis.PeriodLattice
import SICs.SpecialFunctions.BarnesDoubleGamma.Coefficients

/-!
# The Barnes double gamma product used by Shintani

The genus-two inverse-gamma product, slit-plane entireness, and its zero divisor.

This file constructs the inverse Barnes double gamma of
[95, Shintani (1977), equation (1.5) and Proposition 1]:

```text
Gamma₂(z; omega₁, omega₂)⁻¹
  = z exp(gamma₂₂ z + gamma₂₁ z²/2)
      ∏'_(m,n)≠(0,0)
        (1 + z/(m omega₁ + n omega₂))
        exp(-z/(m omega₁ + n omega₂)
            + z²/(2(m omega₁ + n omega₂)²)).
```

The coefficients are the exact normalization series in
`SICs.SpecialFunctions.BarnesDoubleGamma.Coefficients`. The product uses the source's
punctured cone lattice. Shintani's paragraph 1.6 on p. 181 widens the ambient period domain
to `omega₂/omega₁` not a negative real number, matching
[72, Kopp (2024), equation (4.7), `eq:dgprod`]. Each definition is total, with the product's
default value where it does not converge; each analytic result carries its domain hypotheses.

For periods `(1,tau)` in the slit plane, the genus-two correction gives a cubic bound for
each factor's deviation from `1`. Comparison with the cone `(1,i)` proves locally uniform
convergence and entireness in `z`. The same argument applies after omitting one factor.
Nonvanishing of the remaining factors identifies the zeros as the origin and the negative
cone-lattice points. When the cone parametrization is injective, these zeros are simple,
as in [95, Shintani (1977), proof of Proposition 5, p. 181].

Swapping the two cone indices and applying the coefficient symmetries proves period symmetry on
Shintani's continued domain. The ray bounds also give absolute convergence throughout the slit
plane, where the cone avoids zero. Absolute convergence excludes additional zeros, so the origin
and negative cone describe the divisor support there. Simplicity holds in the upper half plane
and at positive irrational periods; positive rational periods can give repeated cone points.
Scaling the cone factors and normalization coefficients supplies the scaled row calculation. The
normalized row product and both difference equations are proved in
`SICs.SpecialFunctions.BarnesDoubleGamma.Normalization` and
`SICs.SpecialFunctions.BarnesDoubleGamma.Difference`. The double-sine quotient belongs to
`SICs.SpecialFunctions.DoubleSine.Gamma`;
`shintaniDoubleSineGamma_eq_product` in
`SICs.SpecialFunctions.DoubleSine.Comparison` identifies it with Shintani's normalized product.
-/

noncomputable section

open Complex Real

namespace SIC

/-! ### The punctured cone lattice and one Weierstrass factor -/

/-- The indices `(m,n) in N² \ {(0,0)}` of the Barnes double-gamma product. -/
def BarnesDoubleGammaIndex := {p : ℕ × ℕ // p ≠ (0, 0)}

/-- Swapping `(m,n)` permutes the punctured cone. This reindexes the product
in `barnesDoubleGammaInv_symm`. -/
private def barnesDoubleGammaIndexSwap : BarnesDoubleGammaIndex ≃ BarnesDoubleGammaIndex :=
  Equiv.subtypeEquiv (Equiv.prodComm ℕ ℕ) (by
    intro p
    simp [Prod.ext_iff, and_comm])

/-- Classical decidable equality used for the finite singleton split in the multiplicity proof. -/
noncomputable local instance : DecidableEq BarnesDoubleGammaIndex := Classical.decEq _

/-- The integer vector `(n,m)` associated with the cone index `(m,n)`.  This private ordering
matches the Eisenstein-series linear form `n tau + m`. -/
private def barnesDoubleGammaIndexVector (p : BarnesDoubleGammaIndex) : Fin 2 → ℤ :=
  ![(p.1.2 : ℤ), (p.1.1 : ℤ)]

/-- Distinct punctured cone indices give distinct associated integer vectors. -/
private lemma barnesDoubleGammaIndexVector_injective :
    Function.Injective barnesDoubleGammaIndexVector := by
  intro p q hpq
  apply Subtype.ext
  apply Prod.ext
  · have h := congrFun hpq 1
    change (p.1.1 : ℤ) = q.1.1 at h
    exact_mod_cast h
  · have h := congrFun hpq 0
    change (p.1.2 : ℤ) = q.1.2 at h
    exact_mod_cast h

/-- The cone-lattice point `m omega₁ + n omega₂` belonging to an index `(m,n)`. -/
def barnesDoubleGammaLatticePoint (omega₁ omega₂ : ℂ)
    (p : BarnesDoubleGammaIndex) : ℂ :=
  (p.1.1 : ℂ) * omega₁ + (p.1.2 : ℂ) * omega₂

/-- On the slit plane the Barnes cone satisfies `1 ≤ C(τ) ‖m+nτ‖` and
`‖m+ni‖ ≤ C(τ) ‖m+nτ‖`. These bounds extend the convergence argument in
[95, Shintani (1977), paragraph 1.6, p. 181], and supply
`summable_norm_barnesDoubleGammaInvFactor_sub_one`. -/
private lemma barnesDoubleGammaLatticePoint_slit_bounds (tau : ℂ)
    (htau : tau ∈ Complex.slitPlane) (p : BarnesDoubleGammaIndex) :
    1 ≤ digammaRayConstant tau * ‖barnesDoubleGammaLatticePoint 1 tau p‖ ∧
    ‖barnesDoubleGammaLatticePoint 1 I p‖ ≤
      digammaRayConstant tau * ‖barnesDoubleGammaLatticePoint 1 tau p‖ := by
  have h := nat_add_le_digammaRayConstant_mul_norm tau htau p.1.2 p.1.1
  simp only [Nat.cast_add] at h
  have hp : 1 ≤ p.1.2 + p.1.1 := by
    have hp : p.1.1 ≠ 0 ∨ p.1.2 ≠ 0 := by
      by_contra! h
      exact p.2 (Prod.ext h.1 h.2)
    omega
  have hnorm : ‖barnesDoubleGammaLatticePoint 1 I p‖ ≤
      (p.1.2 : ℝ) + p.1.1 := by
    simpa [barnesDoubleGammaLatticePoint, add_comm] using
      norm_add_le ((p.1.1 : ℂ) * 1) ((p.1.2 : ℂ) * I)
  simpa only [barnesDoubleGammaLatticePoint, mul_one, add_comm] using
    And.intro ((by exact_mod_cast hp : (1 : ℝ) ≤ (p.1.2 : ℝ) + p.1.1).trans h)
      (hnorm.trans h)

/-- The punctured cone with periods `(1,τ)` avoids zero on Shintani's continued domain.
This supplies the divisor of `barnesDoubleGammaInv_eq_zero_iff`. -/
lemma barnesDoubleGammaLatticePoint_one_ne_zero (tau : ℂ)
    (htau : tau ∈ Complex.slitPlane) (p : BarnesDoubleGammaIndex) :
    barnesDoubleGammaLatticePoint 1 tau p ≠ 0 := by
  intro hzero
  have h := (barnesDoubleGammaLatticePoint_slit_bounds tau htau p).1
  norm_num [hzero] at h

/-- For an upper-half-plane modulus, the cone-lattice parametrization `(m,n) ↦ m+n tau` is
injective.  Equality of imaginary parts first gives equality of `n`, then equality of real parts
gives equality of `m`. -/
lemma barnesDoubleGammaLatticePoint_one_injective (tau : ℂ) (htau : 0 < tau.im) :
    Function.Injective (barnesDoubleGammaLatticePoint 1 tau) := by
  intro p q hpq
  apply Subtype.ext
  have him := congrArg Complex.im hpq
  simp only [barnesDoubleGammaLatticePoint, Complex.add_im, Complex.mul_im,
    Complex.natCast_re, Complex.natCast_im, Complex.one_re, Complex.one_im, mul_zero,
    zero_mul, add_zero] at him
  have hnR : (p.1.2 : ℝ) = q.1.2 :=
    mul_right_cancel₀ htau.ne' (by simpa only [zero_add] using him)
  have hn : p.1.2 = q.1.2 := by exact_mod_cast hnR
  have hre : (p.1.1 : ℝ) = q.1.1 := by
    simpa [barnesDoubleGammaLatticePoint, hn] using congrArg Complex.re hpq
  have hm : p.1.1 = q.1.1 := by exact_mod_cast hre
  exact Prod.ext hm hn

/-- At an irrational real period `τ`, the cone points `m+nτ` have unique indices.
This specializes `intCast_add_intCast_mul_eq_iff_of_irrational` to natural coordinates. -/
lemma barnesDoubleGammaLatticePoint_one_ofReal_injective (τ : ℝ)
    (hirr : Irrational τ) :
    Function.Injective (barnesDoubleGammaLatticePoint 1 (τ : ℂ)) := by
  intro p q hpq
  apply Subtype.ext
  have hcoords : (p.1.1 : ℤ) = q.1.1 ∧ (p.1.2 : ℤ) = q.1.2 :=
    (intCast_add_intCast_mul_eq_iff_of_irrational τ hirr
      (p.1.1 : ℤ) (p.1.2 : ℤ) (q.1.1 : ℤ) (q.1.2 : ℤ)).mp (by
        simpa [barnesDoubleGammaLatticePoint] using hpq)
  exact Prod.ext (by exact_mod_cast hcoords.1) (by exact_mod_cast hcoords.2)

/-- The inverse cubes of the upper-half-plane cone-lattice norms are summable.  This is the
two-dimensional `p = 3` estimate consumed by the genus-two Weierstrass product. -/
lemma summable_barnesDoubleGammaLatticePoint_inv_cube (tau : ℂ)
    (htau : 0 < tau.im) :
    Summable (fun p : BarnesDoubleGammaIndex =>
      ‖(barnesDoubleGammaLatticePoint 1 tau p)⁻¹‖ ^ 3) := by
  let tauH : UpperHalfPlane := ⟨tau, htau⟩
  have h := (EisensteinSeries.summable_norm_eisSummand
    (k := (3 : ℤ)) (by norm_num) tauH).comp_injective
      barnesDoubleGammaIndexVector_injective
  simpa [Function.comp_def, EisensteinSeries.eisSummand, barnesDoubleGammaIndexVector,
    tauH, barnesDoubleGammaLatticePoint, zpow_neg, norm_inv, norm_pow, add_comm,
    mul_comm] using h

/-- The normalized genus-two Weierstrass factor

```text
W(w) = (1+w) exp(-w+w²/2).
```

This is the elementary factor in [95, Shintani (1977), equation (1.5)]. -/
noncomputable def barnesGenusTwoFactor (w : ℂ) : ℂ :=
  (1 + w) * Complex.exp (-w + w ^ 2 / 2)

/-- One genus-two Weierstrass factor in the inverse Barnes double gamma product:

```text
(1 + z/a) exp(-z/a + z²/(2a²)),    a = m omega₁ + n omega₂.
```

This is the factor in [95, Shintani (1977), equation (1.5)] and [72, Kopp (2024), equation
(4.7), `eq:dgprod`]. -/
noncomputable def barnesDoubleGammaInvFactor (z omega₁ omega₂ : ℂ)
    (p : BarnesDoubleGammaIndex) : ℂ :=
  let a := barnesDoubleGammaLatticePoint omega₁ omega₂ p
  (1 + z / a) * Complex.exp (-z / a + z ^ 2 / (2 * a ^ 2))

/-- The Weierstrass factor at the index `p` is the elementary factor `W` evaluated at
`z/a`, `a = m omega₁ + n omega₂`. This is how the product of `barnesDoubleGammaInvFactor`
is rewritten as a product of `barnesGenusTwoFactor` over rows of the cone. -/
lemma barnesDoubleGammaInvFactor_eq_genusTwoFactor (z omega₁ omega₂ : ℂ)
    (p : BarnesDoubleGammaIndex) :
    barnesDoubleGammaInvFactor z omega₁ omega₂ p =
      barnesGenusTwoFactor (z / barnesDoubleGammaLatticePoint omega₁ omega₂ p) := by
  simp only [barnesDoubleGammaInvFactor, barnesGenusTwoFactor, neg_div]
  congr 3
  simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow]
  ring

/-- The genus-two correction cancels the linear and quadratic terms: globally,

```text
‖W(w)-1‖ ≤ 2(1+‖w‖)⁴ exp((1+‖w‖)²) ‖w‖³.
```

The cubic order is the analytic reason that the two-dimensional Barnes product converges. -/
lemma norm_barnesGenusTwoFactor_sub_one_le (w : ℂ) :
    ‖barnesGenusTwoFactor w - 1‖ ≤
      2 * (1 + ‖w‖) ^ 4 * Real.exp ((1 + ‖w‖) ^ 2) * ‖w‖ ^ 3 := by
  let x : ℂ := -w + w ^ 2 / 2
  let R : ℂ := Complex.exp x - (1 + x + x ^ 2 / 2)
  have hR : ‖R‖ ≤ ‖x‖ ^ 3 * Real.exp ‖x‖ := by
    simpa [R, Finset.sum_range_succ, Nat.factorial] using
      Complex.norm_exp_sub_sum_le_norm_mul_exp x 3
  have hx : ‖x‖ ≤ ‖w‖ * (1 + ‖w‖) := by
    calc
      ‖x‖ ≤ ‖-w‖ + ‖w ^ 2 / 2‖ := norm_add_le _ _
      _ = ‖w‖ + ‖w‖ ^ 2 / 2 := by
        rw [norm_neg, norm_div, norm_pow]
        norm_num
      _ ≤ ‖w‖ * (1 + ‖w‖) := by nlinarith [norm_nonneg w]
  have hx' : ‖x‖ ≤ (1 + ‖w‖) ^ 2 := by
    calc
      ‖x‖ ≤ ‖w‖ * (1 + ‖w‖) := hx
      _ ≤ (1 + ‖w‖) ^ 2 := by nlinarith [norm_nonneg w]
  have hR' : ‖R‖ ≤
      ‖w‖ ^ 3 * (1 + ‖w‖) ^ 3 * Real.exp ((1 + ‖w‖) ^ 2) := by
    calc
      ‖R‖ ≤ ‖x‖ ^ 3 * Real.exp ‖x‖ := hR
      _ ≤ (‖w‖ * (1 + ‖w‖)) ^ 3 * Real.exp ((1 + ‖w‖) ^ 2) := by
        gcongr
      _ = ‖w‖ ^ 3 * (1 + ‖w‖) ^ 3 * Real.exp ((1 + ‖w‖) ^ 2) := by
        rw [mul_pow]
  have hmain : ‖(1 + w) * R‖ ≤
      (1 + ‖w‖) ^ 4 * Real.exp ((1 + ‖w‖) ^ 2) * ‖w‖ ^ 3 := by
    calc
      ‖(1 + w) * R‖ = ‖1 + w‖ * ‖R‖ := norm_mul _ _
      _ ≤ (1 + ‖w‖) *
          (‖w‖ ^ 3 * (1 + ‖w‖) ^ 3 * Real.exp ((1 + ‖w‖) ^ 2)) := by
        gcongr
        simpa using norm_add_le (1 : ℂ) w
      _ = (1 + ‖w‖) ^ 4 * Real.exp ((1 + ‖w‖) ^ 2) * ‖w‖ ^ 3 := by ring
  have hpoly :
      ‖w ^ 3 / 2 - 3 * w ^ 4 / 8 + w ^ 5 / 8‖ ≤
        (1 + ‖w‖) ^ 4 * Real.exp ((1 + ‖w‖) ^ 2) * ‖w‖ ^ 3 := by
    calc
      ‖w ^ 3 / 2 - 3 * w ^ 4 / 8 + w ^ 5 / 8‖ ≤
          ‖w ^ 3 / 2‖ + ‖3 * w ^ 4 / 8‖ + ‖w ^ 5 / 8‖ := by
        calc
          _ ≤ ‖w ^ 3 / 2 - 3 * w ^ 4 / 8‖ + ‖w ^ 5 / 8‖ := norm_add_le _ _
          _ ≤ (‖w ^ 3 / 2‖ + ‖3 * w ^ 4 / 8‖) + ‖w ^ 5 / 8‖ :=
            add_le_add (norm_sub_le _ _) le_rfl
      _ = ‖w‖ ^ 3 * (1 / 2 + 3 * ‖w‖ / 8 + ‖w‖ ^ 2 / 8) := by
        simp only [norm_div, norm_pow, norm_mul]
        norm_num
        ring
      _ ≤ ‖w‖ ^ 3 * (1 + ‖w‖) ^ 2 := by
        gcongr
        nlinarith [norm_nonneg w]
      _ ≤ ‖w‖ ^ 3 *
          ((1 + ‖w‖) ^ 4 * Real.exp ((1 + ‖w‖) ^ 2)) := by
        gcongr
        have he : 1 ≤ Real.exp ((1 + ‖w‖) ^ 2) :=
          Real.one_le_exp (sq_nonneg (1 + ‖w‖))
        have hbase : 1 ≤ 1 + ‖w‖ := by nlinarith [norm_nonneg w]
        calc
          (1 + ‖w‖) ^ 2 ≤ (1 + ‖w‖) ^ 4 := by
            nlinarith [sq_nonneg ((1 + ‖w‖) ^ 2 - 1)]
          _ ≤ (1 + ‖w‖) ^ 4 * Real.exp ((1 + ‖w‖) ^ 2) := by
            exact le_mul_of_one_le_right (by positivity) he
      _ = (1 + ‖w‖) ^ 4 * Real.exp ((1 + ‖w‖) ^ 2) * ‖w‖ ^ 3 := by ring
  have hdecomp :
      barnesGenusTwoFactor w - 1 =
        (1 + w) * R + (w ^ 3 / 2 - 3 * w ^ 4 / 8 + w ^ 5 / 8) := by
    dsimp [barnesGenusTwoFactor, R, x]
    ring
  rw [hdecomp]
  calc
    ‖(1 + w) * R + (w ^ 3 / 2 - 3 * w ^ 4 / 8 + w ^ 5 / 8)‖ ≤
        ‖(1 + w) * R‖ + ‖w ^ 3 / 2 - 3 * w ^ 4 / 8 + w ^ 5 / 8‖ := norm_add_le _ _
    _ ≤ 2 * ((1 + ‖w‖) ^ 4 * Real.exp ((1 + ‖w‖) ^ 2) * ‖w‖ ^ 3) := by
      linarith
    _ = 2 * (1 + ‖w‖) ^ 4 * Real.exp ((1 + ‖w‖) ^ 2) * ‖w‖ ^ 3 := by ring

/-- A Barnes inverse-double-gamma factor vanishes exactly at the negative of its lattice point,
provided that point is nonzero. -/
lemma barnesDoubleGammaInvFactor_eq_zero_iff (z omega₁ omega₂ : ℂ)
    (p : BarnesDoubleGammaIndex)
    (ha : barnesDoubleGammaLatticePoint omega₁ omega₂ p ≠ 0) :
    barnesDoubleGammaInvFactor z omega₁ omega₂ p = 0 ↔
      z = -barnesDoubleGammaLatticePoint omega₁ omega₂ p := by
  let a := barnesDoubleGammaLatticePoint omega₁ omega₂ p
  change (1 + z / a) * Complex.exp (-z / a + z ^ 2 / (2 * a ^ 2)) = 0 ↔ z = -a
  constructor
  · intro h
    have hfirst : 1 + z / a = 0 :=
      (mul_eq_zero.mp h).resolve_right (Complex.exp_ne_zero _)
    have hzdiv : z / a = -1 := by linear_combination hfirst
    rw [div_eq_iff ha] at hzdiv
    simpa using hzdiv
  · rintro rfl
    have hdiv : -a / a = -1 := by rw [neg_div, div_self ha]
    rw [hdiv]
    simp

/-- At `z = 0`, every genus-two Weierstrass factor equals `1`. -/
@[simp]
lemma barnesDoubleGammaInvFactor_zero (omega₁ omega₂ : ℂ)
    (p : BarnesDoubleGammaIndex) :
    barnesDoubleGammaInvFactor 0 omega₁ omega₂ p = 1 := by
  simp [barnesDoubleGammaInvFactor]

/-- On the slit plane, each Barnes factor has nonzero derivative at its zero `-a`,
where `a = m+nτ`: the derivative equals `a⁻¹ exp(3/2)`. -/
lemma deriv_barnesDoubleGammaInvFactor_neg_ne_zero (tau : ℂ)
    (htau : tau ∈ Complex.slitPlane) (p : BarnesDoubleGammaIndex) :
    deriv (fun z => barnesDoubleGammaInvFactor z 1 tau p)
        (-barnesDoubleGammaLatticePoint 1 tau p) ≠ 0 := by
  let a := barnesDoubleGammaLatticePoint 1 tau p
  have ha : a ≠ 0 := barnesDoubleGammaLatticePoint_one_ne_zero tau htau p
  have hd : HasDerivAt (fun z => barnesDoubleGammaInvFactor z 1 tau p)
      (a⁻¹ * Complex.exp (3 / 2)) (-a) := by
    unfold barnesDoubleGammaInvFactor
    apply (((hasDerivAt_const (-a) 1).add ((hasDerivAt_id (-a)).div_const a)).mul
      (((((hasDerivAt_id (-a)).neg.div_const a).add
        (((hasDerivAt_id (-a)).pow 2).div_const (2 * a ^ 2))).cexp))).congr_deriv
    dsimp only [id_eq, Pi.neg_apply, Pi.add_apply, Pi.pow_apply]
    field_simp
    norm_num
    ring
  rw [hd.deriv]
  exact mul_ne_zero (inv_ne_zero ha) (Complex.exp_ne_zero _)

/-- The slit-plane cone comparison bounds each reciprocal both by `C(τ)` and
by `C(τ) ‖(m+ni)⁻¹‖`. This supplies the cubic majorant for
`summable_norm_barnesDoubleGammaInvFactor_sub_one`. -/
private lemma barnesDoubleGammaLatticePoint_slit_inv_bounds (tau : ℂ)
    (htau : tau ∈ Complex.slitPlane) (p : BarnesDoubleGammaIndex) :
      ‖(barnesDoubleGammaLatticePoint 1 tau p)⁻¹‖ ≤ digammaRayConstant tau ∧
      ‖(barnesDoubleGammaLatticePoint 1 tau p)⁻¹‖ ≤
        digammaRayConstant tau * ‖(barnesDoubleGammaLatticePoint 1 I p)⁻¹‖ := by
  obtain ⟨h1, h2⟩ := barnesDoubleGammaLatticePoint_slit_bounds tau htau p
  have ha : 0 < ‖barnesDoubleGammaLatticePoint 1 tau p‖ := norm_pos_iff.mpr
    (barnesDoubleGammaLatticePoint_one_ne_zero tau htau p)
  have hi : 0 < ‖barnesDoubleGammaLatticePoint 1 I p‖ := norm_pos_iff.mpr
    (barnesDoubleGammaLatticePoint_one_ne_zero I (Or.inr (by simp)) p)
  simp only [norm_inv]
  constructor
  · exact (inv_le_iff_one_le_mul₀ ha).2 h1
  · rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ ha hi]
    simpa using h2

/-- A bound on `‖z‖ C(τ)` gives a cubic majorant over the fixed cone `(1,i)`.
This supplies `summable_norm_barnesDoubleGammaInvFactor_sub_one`
and `hasProdLocallyUniformlyOn_barnesDoubleGammaInvFactor`. -/
lemma norm_barnesDoubleGammaInvFactor_sub_one_le
    {z tau : ℂ} (htau : tau ∈ Complex.slitPlane) {B : ℝ}
    (hB : ‖z‖ * digammaRayConstant tau ≤ B) (p : BarnesDoubleGammaIndex) :
    ‖barnesDoubleGammaInvFactor z 1 tau p - 1‖ ≤
      (2 * (1 + B) ^ 4 * Real.exp ((1 + B) ^ 2) * B ^ 3) *
        ‖(barnesDoubleGammaLatticePoint 1 I p)⁻¹‖ ^ 3 := by
  let a := barnesDoubleGammaLatticePoint 1 tau p
  have hb := barnesDoubleGammaLatticePoint_slit_inv_bounds tau htau p
  have hw : ‖z / a‖ ≤ B := by
    rw [div_eq_mul_inv, norm_mul]
    exact (mul_le_mul_of_nonneg_left hb.1 (norm_nonneg z)).trans hB
  have hw' : ‖z / a‖ ≤ B * ‖(barnesDoubleGammaLatticePoint 1 I p)⁻¹‖ := by
    calc
      _ = ‖z‖ * ‖a⁻¹‖ := by rw [div_eq_mul_inv, norm_mul]
      _ ≤ ‖z‖ * (digammaRayConstant tau *
          ‖(barnesDoubleGammaLatticePoint 1 I p)⁻¹‖) :=
        mul_le_mul_of_nonneg_left hb.2 (norm_nonneg z)
      _ ≤ B * ‖(barnesDoubleGammaLatticePoint 1 I p)⁻¹‖ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hB (norm_nonneg _)
  rw [barnesDoubleGammaInvFactor_eq_genusTwoFactor]
  calc
    _ ≤ 2 * (1 + ‖z / a‖) ^ 4 * Real.exp ((1 + ‖z / a‖) ^ 2) * ‖z / a‖ ^ 3 :=
      norm_barnesGenusTwoFactor_sub_one_le _
    _ ≤ 2 * (1 + B) ^ 4 * Real.exp ((1 + B) ^ 2) *
        (B * ‖(barnesDoubleGammaLatticePoint 1 I p)⁻¹‖) ^ 3 := by
      gcongr
    _ = _ := by ring

/-- For `τ∈ℂ \ (-∞,0]`, the deviations of the Barnes genus-two factors from `1`
are absolutely summable. This is the convergence assertion of
[95, Shintani (1977), paragraph 1.6, p. 181]. Compare the cone with periods `(1,i)`
using `norm_barnesDoubleGammaInvFactor_sub_one_le`. -/
lemma summable_norm_barnesDoubleGammaInvFactor_sub_one (z tau : ℂ)
    (htau : tau ∈ Complex.slitPlane) :
    Summable (fun p : BarnesDoubleGammaIndex =>
      ‖barnesDoubleGammaInvFactor z 1 tau p - 1‖) := by
  let B := ‖z‖ * digammaRayConstant tau
  have hs := (summable_barnesDoubleGammaLatticePoint_inv_cube I
    (by simp)).mul_left (2 * (1 + B) ^ 4 * Real.exp ((1 + B) ^ 2) * B ^ 3)
  exact hs.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun p => norm_barnesDoubleGammaInvFactor_sub_one_le htau le_rfl p)

/-- Restricting to all cone indices other than `p` preserves absolute summability of the factor
deviations from `1`. -/
private lemma summable_norm_invFactor_complement_sub_one
    (p : BarnesDoubleGammaIndex) (z tau : ℂ) (htau : tau ∈ Complex.slitPlane) :
    Summable (fun q : BarnesDoubleGammaIndex =>
      ‖(if q = p then (1 : ℂ) else barnesDoubleGammaInvFactor z 1 tau q) - 1‖) := by
  apply (summable_norm_barnesDoubleGammaInvFactor_sub_one z tau
    htau).of_nonneg_of_le
  · exact fun _ => norm_nonneg _
  · intro q
    by_cases hq : q = p <;> simp [hq]

/-- Replacing the factors outside a fixed predicate by `1` preserves locally uniform
convergence on the slit plane. -/
private lemma hasProdLocallyUniformly_invFactor_restricted
    (P : BarnesDoubleGammaIndex → Prop) [DecidablePred P] (tau : ℂ)
    (htau : tau ∈ Complex.slitPlane) :
    HasProdLocallyUniformly
      (fun p : BarnesDoubleGammaIndex => fun z : ℂ =>
        if P p then barnesDoubleGammaInvFactor z 1 tau p else 1)
      (fun z => ∏' p : BarnesDoubleGammaIndex,
        if P p then barnesDoubleGammaInvFactor z 1 tau p else 1) := by
  apply hasProdLocallyUniformly_of_forall_compact
  intro K hK
  obtain ⟨B, _, hB⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : ℂ)
  let C := B * digammaRayConstant tau
  let u : BarnesDoubleGammaIndex → ℝ := fun p =>
    (2 * (1 + C) ^ 4 * Real.exp ((1 + C) ^ 2) * C ^ 3) *
      ‖(barnesDoubleGammaLatticePoint 1 I p)⁻¹‖ ^ 3
  have hu : Summable u :=
    (summable_barnesDoubleGammaLatticePoint_inv_cube I (by simp)).mul_left _
  have hmajor : ∀ p : BarnesDoubleGammaIndex, ∀ z ∈ K,
      ‖(if P p then barnesDoubleGammaInvFactor z 1 tau p else (1 : ℂ)) - 1‖ ≤ u p := by
    intro p z hz
    have hnorm : ‖z‖ ≤ B := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hB hz
    have hbound := norm_barnesDoubleGammaInvFactor_sub_one_le htau
      (show ‖z‖ * digammaRayConstant tau ≤ C from
        mul_le_mul_of_nonneg_right hnorm (digammaRayConstant_pos tau htau).le) p
    by_cases hp : P p
    · simpa only [ite_eq_left hp] using hbound
    · simpa only [ite_eq_right hp, sub_self, norm_zero] using (norm_nonneg _).trans hbound
  simpa [add_comm] using
    hu.hasProdUniformlyOn_one_add hK (Filter.Eventually.of_forall hmajor)
      (fun p => by
        apply Continuous.continuousOn
        by_cases hp : P p
        · simp only [ite_eq_left hp]
          unfold barnesDoubleGammaInvFactor
          fun_prop
        · simp only [ite_eq_right hp]; fun_prop)

/-- On the slit plane, Shintani's genus-two product converges locally uniformly in `z`.
This extends [95, Shintani (1977), equation (1.5)] to the period domain of paragraph 1.6. -/
lemma hasProdLocallyUniformly_barnesDoubleGammaInvFactor (tau : ℂ)
    (htau : tau ∈ Complex.slitPlane) :
    HasProdLocallyUniformly
      (fun p : BarnesDoubleGammaIndex => fun z : ℂ =>
        barnesDoubleGammaInvFactor z 1 tau p)
      (fun z => ∏' p : BarnesDoubleGammaIndex,
        barnesDoubleGammaInvFactor z 1 tau p) := by
  simpa only [ite_true] using
    hasProdLocallyUniformly_invFactor_restricted (fun _ => True) tau htau

/-- Restricting to all cone indices other than `p` preserves local-uniform convergence. -/
private lemma hasProdLocallyUniformly_invFactor_complement
    (p : BarnesDoubleGammaIndex) (tau : ℂ) (htau : tau ∈ Complex.slitPlane) :
    HasProdLocallyUniformly
      (fun q : BarnesDoubleGammaIndex => fun z : ℂ =>
        if q = p then 1 else barnesDoubleGammaInvFactor z 1 tau q)
      (fun z => ∏' q : BarnesDoubleGammaIndex,
        if q = p then 1 else barnesDoubleGammaInvFactor z 1 tau q) := by
  simpa only [ite_not] using
    hasProdLocallyUniformly_invFactor_restricted (fun q => q ≠ p) tau htau

/-- A locally uniformly convergent restricted family of Barnes factors has an entire product.
This supplies `differentiable_invFactor_complement_tprod`. -/
private lemma differentiable_invFactor_restricted_tprod
    (P : BarnesDoubleGammaIndex → Prop) [DecidablePred P] (tau : ℂ)
    (hprod : HasProdLocallyUniformly
      (fun p : BarnesDoubleGammaIndex => fun z : ℂ =>
        if P p then barnesDoubleGammaInvFactor z 1 tau p else 1)
      (fun z => ∏' p : BarnesDoubleGammaIndex,
        if P p then barnesDoubleGammaInvFactor z 1 tau p else 1)) :
    Differentiable ℂ (fun z => ∏' p : BarnesDoubleGammaIndex,
      if P p then barnesDoubleGammaInvFactor z 1 tau p else 1) := by
  rw [← differentiableOn_univ]
  apply hprod.tendstoLocallyUniformlyOn.differentiableOn
  · exact Filter.Eventually.of_forall fun s => by
      apply Differentiable.differentiableOn
      simpa [Finset.prod_fn] using Differentiable.finsetProd (u := s) (fun p hp => by
        by_cases hP : P p
        · simp only [ite_eq_left hP]
          unfold barnesDoubleGammaInvFactor
          fun_prop
        · simp only [ite_eq_right hP]
          fun_prop)
  · exact isOpen_univ

/-- The locally uniform genus-two product is entire in `z` for every slit-plane modulus. -/
lemma differentiable_barnesDoubleGammaInvFactor_tprod (tau : ℂ)
    (htau : tau ∈ Complex.slitPlane) :
    Differentiable ℂ (fun z => ∏' p : BarnesDoubleGammaIndex,
      barnesDoubleGammaInvFactor z 1 tau p) := by
  simpa only [ite_true] using
    differentiable_invFactor_restricted_tprod (fun _ => True) tau
      (by simpa only [ite_true] using
        hasProdLocallyUniformly_barnesDoubleGammaInvFactor tau htau)

/-- The product complementary to one chosen Barnes factor is entire. -/
private lemma differentiable_invFactor_complement_tprod
    (p : BarnesDoubleGammaIndex) (tau : ℂ) (htau : tau ∈ Complex.slitPlane) :
    Differentiable ℂ (fun z => ∏' q : BarnesDoubleGammaIndex,
      if q = p then 1 else barnesDoubleGammaInvFactor z 1 tau q) := by
  simpa only [ite_not] using
    differentiable_invFactor_restricted_tprod (fun q => q ≠ p) tau
      (by simpa only [ite_not] using
        hasProdLocallyUniformly_invFactor_complement p tau htau)

/-- The full genus-two product is one chosen factor times its complementary product. -/
private lemma invFactor_tprod_eq_factor_mul_complement
    (p : BarnesDoubleGammaIndex) (z tau : ℂ) (htau : tau ∈ Complex.slitPlane) :
    (∏' q : BarnesDoubleGammaIndex, barnesDoubleGammaInvFactor z 1 tau q) =
      barnesDoubleGammaInvFactor z 1 tau p *
        ∏' q : BarnesDoubleGammaIndex,
          if q = p then 1 else barnesDoubleGammaInvFactor z 1 tau q := by
  have hs := summable_norm_invFactor_complement_sub_one p z tau htau
  have hm : Multipliable (fun q : BarnesDoubleGammaIndex =>
      if q = p then (1 : ℂ) else barnesDoubleGammaInvFactor z 1 tau q) := by
    simpa [add_comm] using multipliable_one_add_of_summable hs
  have hm' : Multipliable (Function.update
      (fun q : BarnesDoubleGammaIndex => barnesDoubleGammaInvFactor z 1 tau q) p 1) := by
    apply hm.congr
    intro q
    by_cases hq : q = p
    · subst q
      rw [Function.update_self, ite_eq_left rfl]
    · rw [Function.update_of_ne hq, ite_eq_right hq]
  exact Multipliable.tprod_eq_mul_tprod_ite' p hm'

/-- At the zero belonging to `p`, the product of all other Barnes factors is nonzero. -/
private lemma invFactor_complement_tprod_neg_ne_zero
    (p : BarnesDoubleGammaIndex) (tau : ℂ) (htau : tau ∈ Complex.slitPlane)
    (hinj : Function.Injective (barnesDoubleGammaLatticePoint 1 tau)) :
    (∏' q : BarnesDoubleGammaIndex,
      if q = p then 1 else
        barnesDoubleGammaInvFactor (-barnesDoubleGammaLatticePoint 1 tau p) 1 tau q) ≠ 0 := by
  simpa [add_comm] using
    tprod_one_add_ne_zero_of_summable
      (f := fun q : BarnesDoubleGammaIndex =>
        (if q = p then 1 else
          barnesDoubleGammaInvFactor (-barnesDoubleGammaLatticePoint 1 tau p) 1 tau q) - 1)
      (fun q => by
        by_cases hq : q = p
        · simp only [ite_eq_left hq]
          norm_num
        · simp only [ite_eq_right hq]
          intro hzero
          have hzero' : barnesDoubleGammaInvFactor
              (-barnesDoubleGammaLatticePoint 1 tau p) 1 tau q = 0 := by
            simpa [add_comm] using hzero
          have heq := (barnesDoubleGammaInvFactor_eq_zero_iff _ 1 tau q
            (barnesDoubleGammaLatticePoint_one_ne_zero tau htau q)).mp hzero'
          exact hq ((hinj (neg_inj.mp heq)).symm))
      (summable_norm_invFactor_complement_sub_one p
        (-barnesDoubleGammaLatticePoint 1 tau p) tau htau)

/-- If the slit-plane cone parametrization is injective, every negative cone-lattice zero
of the convergent genus-two product is simple. -/
lemma deriv_barnesDoubleGammaInvFactor_tprod_neg_ne_zero
    (tau : ℂ) (htau : tau ∈ Complex.slitPlane)
    (hinj : Function.Injective (barnesDoubleGammaLatticePoint 1 tau))
    (p : BarnesDoubleGammaIndex) :
    deriv (fun z => ∏' q : BarnesDoubleGammaIndex,
      barnesDoubleGammaInvFactor z 1 tau q)
        (-barnesDoubleGammaLatticePoint 1 tau p) ≠ 0 := by
  have hfun : (fun z => ∏' q : BarnesDoubleGammaIndex,
      barnesDoubleGammaInvFactor z 1 tau q) =
      (fun z => barnesDoubleGammaInvFactor z 1 tau p *
        ∏' q : BarnesDoubleGammaIndex,
          if q = p then 1 else barnesDoubleGammaInvFactor z 1 tau q) := by
    funext z
    exact invFactor_tprod_eq_factor_mul_complement p z tau htau
  rw [hfun]
  rw [deriv_fun_mul]
  · rw [(barnesDoubleGammaInvFactor_eq_zero_iff _ 1 tau p
      (barnesDoubleGammaLatticePoint_one_ne_zero tau htau p)).mpr rfl]
    simp only [zero_mul, add_zero]
    exact mul_ne_zero
      (deriv_barnesDoubleGammaInvFactor_neg_ne_zero tau htau p)
      (invFactor_complement_tprod_neg_ne_zero p tau htau hinj)
  · unfold barnesDoubleGammaInvFactor
    fun_prop
  · exact (differentiable_invFactor_complement_tprod p tau htau)
      (-barnesDoubleGammaLatticePoint 1 tau p)

/-- The absolutely convergent genus-two product is nonzero precisely when all its factors
are nonzero, on the period domain of [95, Shintani (1977), paragraph 1.6, p. 181]. -/
lemma barnesDoubleGammaInvFactor_tprod_ne_zero_iff (z tau : ℂ)
    (htau : tau ∈ Complex.slitPlane) :
    (∏' p : BarnesDoubleGammaIndex, barnesDoubleGammaInvFactor z 1 tau p) ≠ 0 ↔
      ∀ p : BarnesDoubleGammaIndex, barnesDoubleGammaInvFactor z 1 tau p ≠ 0 := by
  constructor
  · intro hproduct p hfactor
    exact hproduct (tprod_of_exists_eq_zero ⟨p, hfactor⟩)
  · intro hfactors
    simpa [add_comm] using
      tprod_one_add_ne_zero_of_summable
        (f := fun p : BarnesDoubleGammaIndex => barnesDoubleGammaInvFactor z 1 tau p - 1)
        (fun p => by simpa [add_comm] using hfactors p)
        (summable_norm_barnesDoubleGammaInvFactor_sub_one z tau htau)

/-- The zero set of the genus-two product on Shintani's continued period domain is the
negative punctured cone lattice; used by `barnesDoubleGammaInv_eq_zero_iff`. -/
lemma barnesDoubleGammaInvFactor_tprod_eq_zero_iff (z tau : ℂ)
    (htau : tau ∈ Complex.slitPlane) :
    (∏' p : BarnesDoubleGammaIndex, barnesDoubleGammaInvFactor z 1 tau p) = 0 ↔
      ∃ p : BarnesDoubleGammaIndex, z = -barnesDoubleGammaLatticePoint 1 tau p := by
  constructor
  · intro hzero
    have hfactor : ¬ ∀ p : BarnesDoubleGammaIndex,
        barnesDoubleGammaInvFactor z 1 tau p ≠ 0 := by
      intro h
      exact
        (barnesDoubleGammaInvFactor_tprod_ne_zero_iff z tau htau).2 h hzero
    push Not at hfactor
    obtain ⟨p, hp⟩ := hfactor
    exact ⟨p, (barnesDoubleGammaInvFactor_eq_zero_iff z 1 tau p
      (barnesDoubleGammaLatticePoint_one_ne_zero tau htau p)).mp hp⟩
  · rintro ⟨p, hp⟩
    exact tprod_of_exists_eq_zero ⟨p,
      (barnesDoubleGammaInvFactor_eq_zero_iff z 1 tau p
        (barnesDoubleGammaLatticePoint_one_ne_zero tau htau p)).mpr hp⟩

/-! ### The inverse double gamma -/

/-- The inverse Barnes double gamma of [95, Shintani (1977), equation (1.5)]:

```text
Gamma₂(z; omega₁,omega₂)⁻¹
  = z exp(gamma₂₂ z + gamma₂₁ z²/2) ∏' W_(m,n)(z).
```

This is also [72, Kopp (2024), equation (4.7), `eq:dgprod`].

The `tprod` runs over the same index set as the source: pairs of non-negative integers
other than `(0,0)`. For periods `(1,tau)` in the slit plane, the product converges locally
uniformly, is entire in its argument, and has the stated zero support. Its zeros are simple
in the upper half plane and at positive irrational periods. If the product fails to converge,
the `tprod` takes Lean's default value `1`. -/
@[source "95, equation (1.5), p. 172" (symbol := "Γ₂(z, ω)⁻¹")]
noncomputable def barnesDoubleGammaInv (z omega₁ omega₂ : ℂ) : ℂ :=
  z * Complex.exp
      (barnesGamma22 omega₁ omega₂ * z +
        z ^ 2 / 2 * barnesGamma21 omega₁ omega₂) *
    ∏' p : BarnesDoubleGammaIndex, barnesDoubleGammaInvFactor z omega₁ omega₂ p

/-- Dividing both periods and the argument by `ω₁` preserves each cone factor.
This is the scaling of the cone in the proof of `barnesDoubleGammaInv_rescale`. -/
lemma barnesDoubleGammaInvFactor_rescale (z a b : ℂ) (ha : a ≠ 0)
    (p : BarnesDoubleGammaIndex) :
    barnesDoubleGammaInvFactor z a b p =
      barnesDoubleGammaInvFactor (z / a) 1 (b / a) p := by
  simp only [barnesDoubleGammaInvFactor_eq_genusTwoFactor]
  congr 1
  simp only [barnesDoubleGammaLatticePoint, mul_one]
  rw [show (p.1.1 : ℂ) + p.1.2 * (b / a) =
    ((p.1.1 : ℂ) * a + p.1.2 * b) / a by field_simp]
  exact (div_div_div_cancel_right₀ ha _ _).symm

/-- The coefficient correction in the rescaled Barnes product, used by
`barnesDoubleGammaInv_rescale`. -/
private lemma barnesDoubleGamma_rescale_exponent (z a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    barnesGamma22 a b * z + z ^ 2 / 2 * barnesGamma21 a b =
      (z ^ 2 / (2 * a * b) * (Complex.log b - Complex.log (b / a)) -
        z * (a⁻¹ + b⁻¹) * Complex.log a / 2) +
      (barnesGamma22 1 (b / a) * (z / a) +
        (z / a) ^ 2 / 2 * barnesGamma21 1 (b / a)) := by
  have h21 := barnesGamma21_rescale a b ha hb
  have h22 := barnesGamma22_rescale a b ha hb
  have h21' : barnesGamma21 a b =
      (barnesGamma21 1 (b / a) + a / b * (Complex.log b - Complex.log (b / a))) / a ^ 2 :=
    (eq_div_iff (pow_ne_zero 2 ha)).2 (by simpa only [mul_comm] using h21)
  have h22' : barnesGamma22 a b =
      (barnesGamma22 1 (b / a) - (1 + a / b) * Complex.log a / 2) / a :=
    (eq_div_iff ha).2 (by simpa only [mul_comm] using h22)
  rw [h21', h22']
  field_simp
  ring

/-- Scaling the periods in the row calculation gives
`Γ₂(z;ω₁,ω₂)⁻¹ = ω₁ exp(E) Γ₂(z/ω₁;1,ω₂/ω₁)⁻¹`, where
`E = z²(log ω₂-log(ω₂/ω₁))/(2ω₁ω₂) - z(ω₁⁻¹+ω₂⁻¹)log(ω₁)/2`.
This is the exponential form of the scaled normalization in
[95, Shintani (1977), proof of Proposition 1, p. 173]. Keeping the two logarithms
separate makes this identity valid without branch conditions; on the source domain it
supplies the scaled row argument for the second difference equation. -/
lemma barnesDoubleGammaInv_rescale (z a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    barnesDoubleGammaInv z a b = a *
      Complex.exp (z ^ 2 / (2 * a * b) * (Complex.log b - Complex.log (b / a)) -
        z * (a⁻¹ + b⁻¹) * Complex.log a / 2) *
      barnesDoubleGammaInv (z / a) 1 (b / a) := by
  unfold barnesDoubleGammaInv
  simp_rw [barnesDoubleGammaInvFactor_rescale z a b ha]
  rw [barnesDoubleGamma_rescale_exponent z a b ha hb, Complex.exp_add]
  field_simp

/-- For `ω₁>0` and `ω₂∈ℂ \ (-∞,0]`, the inverse double gamma is symmetric:
`Γ₂(z;ω₁,ω₂)⁻¹=Γ₂(z;ω₂,ω₁)⁻¹`. This is the symmetry assertion of
[95, Shintani (1977), Proposition 1, p. 172], on its continued domain in
[95, Shintani (1977), paragraph 1.6, p. 181]. -/
@[source "95, Proposition 1, p. 172 (symmetry)"]
theorem barnesDoubleGammaInv_symm (z : ℂ) (omega₁ : ℝ) (omega₂ : ℂ)
    (h₁ : 0 < omega₁) (h₂ : omega₂ ∈ Complex.slitPlane) :
    barnesDoubleGammaInv z omega₁ omega₂ = barnesDoubleGammaInv z omega₂ omega₁ := by
  unfold barnesDoubleGammaInv
  rw [barnesGamma21_symm omega₁ omega₂ h₁ h₂, barnesGamma22_symm omega₁ omega₂ h₁ h₂]
  congr 1
  calc
    _ = ∏' p, barnesDoubleGammaInvFactor z omega₂ omega₁ (barnesDoubleGammaIndexSwap p) := by
      apply tprod_congr
      intro p
      rw [barnesDoubleGammaInvFactor_eq_genusTwoFactor,
        barnesDoubleGammaInvFactor_eq_genusTwoFactor]
      change barnesGenusTwoFactor (z / ((p.1.1 : ℂ) * omega₁ + p.1.2 * omega₂)) =
        barnesGenusTwoFactor (z / ((p.1.2 : ℂ) * omega₂ + p.1.1 * omega₁))
      rw [add_comm]
    _ = _ := barnesDoubleGammaIndexSwap.tprod_eq (barnesDoubleGammaInvFactor z omega₂ omega₁)

/-- For each slit-plane period `τ`, the inverse Barnes double gamma is entire in `z`.
This is the fixed-period consequence of the product continuation in
[95, Shintani (1977), paragraph 1.6, p. 181], including positive real periods. -/
theorem differentiable_barnesDoubleGammaInv (τ : ℂ)
    (hτ : τ ∈ Complex.slitPlane) :
    Differentiable ℂ (fun z => barnesDoubleGammaInv z 1 τ) := by
  unfold barnesDoubleGammaInv
  apply Differentiable.mul
  · fun_prop
  · exact differentiable_barnesDoubleGammaInvFactor_tprod τ hτ

/-- The inverse Barnes double gamma vanishes at the origin, owing to its displayed leading
factor `z`.  This holds at every pair of periods, since the leading factor annihilates both the
exponential and the `tprod`, convergent or not. -/
@[simp]
lemma barnesDoubleGammaInv_zero (omega₁ omega₂ : ℂ) :
    barnesDoubleGammaInv 0 omega₁ omega₂ = 0 := by
  simp [barnesDoubleGammaInv]

/-- On the slit plane, the inverse Barnes double gamma has derivative `1` at the origin.
This is the leading-factor part of [95, Shintani (1977), equation (1.5)]. -/
lemma deriv_barnesDoubleGammaInv_zero (tau : ℂ)
    (htau : tau ∈ Complex.slitPlane) :
    deriv (fun z => barnesDoubleGammaInv z 1 tau) 0 = 1 := by
  unfold barnesDoubleGammaInv
  rw [deriv_fun_mul]
  · simp only [barnesDoubleGammaInvFactor_zero, tprod_one, mul_one, zero_mul, add_zero]
    rw [deriv_fun_mul]
    · simp
    · fun_prop
    · fun_prop
  · fun_prop
  · exact (differentiable_barnesDoubleGammaInvFactor_tprod tau htau) 0

/-- On the slit plane, an injectively indexed negative cone zero of the inverse Barnes
double gamma is simple. This is the multiplicity argument from the product in
[95, Shintani (1977), equation (1.5)]. -/
lemma deriv_barnesDoubleGammaInv_neg_ne_zero (tau : ℂ)
    (htau : tau ∈ Complex.slitPlane)
    (hinj : Function.Injective (barnesDoubleGammaLatticePoint 1 tau))
    (p : BarnesDoubleGammaIndex) :
    deriv (fun z => barnesDoubleGammaInv z 1 tau)
        (-barnesDoubleGammaLatticePoint 1 tau p) ≠ 0 := by
  unfold barnesDoubleGammaInv
  rw [deriv_fun_mul]
  · rw [(barnesDoubleGammaInvFactor_tprod_eq_zero_iff _ tau htau).mpr
      ⟨p, rfl⟩]
    simp only [mul_zero, zero_add]
    exact mul_ne_zero
      (mul_ne_zero
        (neg_ne_zero.mpr
          (barnesDoubleGammaLatticePoint_one_ne_zero tau htau p))
        (Complex.exp_ne_zero _))
      (deriv_barnesDoubleGammaInvFactor_tprod_neg_ne_zero tau
        htau hinj p)
  · fun_prop
  · exact (differentiable_barnesDoubleGammaInvFactor_tprod tau htau)
      (-barnesDoubleGammaLatticePoint 1 tau p)

/-- On `τ ∈ ℂ \ (-∞,0]`, the zeros of `Γ₂(z;1,τ)⁻¹` are the origin and the negative cone
lattice. This is the divisor support in [95, Shintani (1977), Proposition 1], on the continued
period domain of [95, Shintani (1977), paragraph 1.6, p. 181]. No multiplicity is asserted. -/
lemma barnesDoubleGammaInv_eq_zero_iff (z tau : ℂ)
    (htau : tau ∈ Complex.slitPlane) :
    barnesDoubleGammaInv z 1 tau = 0 ↔
      z = 0 ∨ ∃ p : BarnesDoubleGammaIndex,
        z = -barnesDoubleGammaLatticePoint 1 tau p := by
  unfold barnesDoubleGammaInv
  simp only [mul_eq_zero, Complex.exp_ne_zero, or_false,
    barnesDoubleGammaInvFactor_tprod_eq_zero_iff z tau htau]

/-- The zero cone of the inverse Barnes double gamma is closed under subtraction of `1`. -/
lemma barnesDoubleGammaInv_eq_zero_of_eq_zero_sub_one (w τ : ℂ)
    (hτ : τ ∈ Complex.slitPlane) (hw : barnesDoubleGammaInv w 1 τ = 0) :
    barnesDoubleGammaInv (w - 1) 1 τ = 0 := by
  rcases (barnesDoubleGammaInv_eq_zero_iff w τ hτ).mp hw with
    rfl | ⟨⟨⟨m, n⟩, hp⟩, rfl⟩
  · exact (barnesDoubleGammaInv_eq_zero_iff _ τ hτ).2
      (Or.inr ⟨⟨(1, 0), by simp⟩, by simp [barnesDoubleGammaLatticePoint]⟩)
  · exact (barnesDoubleGammaInv_eq_zero_iff _ τ hτ).2
      (Or.inr ⟨⟨(m + 1, n), by simp⟩, by simp [barnesDoubleGammaLatticePoint]; ring⟩)

/-- The zero cone of the inverse Barnes double gamma is closed under subtraction of `τ`. -/
lemma barnesDoubleGammaInv_eq_zero_of_eq_zero_sub_period (w τ : ℂ)
    (hτ : τ ∈ Complex.slitPlane) (hw : barnesDoubleGammaInv w 1 τ = 0) :
    barnesDoubleGammaInv (w - τ) 1 τ = 0 := by
  rcases (barnesDoubleGammaInv_eq_zero_iff w τ hτ).mp hw with
    rfl | ⟨⟨⟨m, n⟩, hp⟩, rfl⟩
  · exact (barnesDoubleGammaInv_eq_zero_iff _ τ hτ).2
      (Or.inr ⟨⟨(0, 1), by simp⟩, by simp [barnesDoubleGammaLatticePoint]⟩)
  · exact (barnesDoubleGammaInv_eq_zero_iff _ τ hτ).2
      (Or.inr ⟨⟨(m, n + 1), by simp⟩, by simp [barnesDoubleGammaLatticePoint]; ring⟩)

/-- If `Re z > 0`, `Re τ ≥ 0` and `τ` is in the slit plane, the inverse double gamma
cannot vanish, since every point in its zero set has nonpositive real part. This is the chamber
consequence of `barnesDoubleGammaInv_eq_zero_iff`. -/
lemma barnesDoubleGammaInv_ne_zero_of_re_pos (z tau : ℂ)
    (htau : tau ∈ Complex.slitPlane) (htauRe : 0 ≤ tau.re) (hz : 0 < z.re) :
    barnesDoubleGammaInv z 1 tau ≠ 0 := by
  intro hzero
  rcases (barnesDoubleGammaInv_eq_zero_iff z tau htau).mp hzero with
      hzero | ⟨p, hp⟩
  · rw [hzero] at hz
    exact (lt_irrefl 0) hz
  · have hre : z.re = -((p.1.1 : ℝ) + (p.1.2 : ℝ) * tau.re) := by
      simpa [barnesDoubleGammaLatticePoint] using congrArg Complex.re hp
    have hm : 0 ≤ (p.1.1 : ℝ) := by positivity
    have hn : 0 ≤ (p.1.2 : ℝ) := by positivity
    nlinarith

/-- For positive irrational `τ`, every zero of `Γ₂(z;1,τ)⁻¹` is simple.
This is the multiplicity consequence of the product in [95, Shintani (1977),
equation (1.5) and proof of Proposition 5, p. 181]. -/
theorem deriv_barnesDoubleGammaInv_ne_zero_of_irrational (z : ℂ) (τ : ℝ)
    (hτ : 0 < τ) (hirr : Irrational τ) (hz : barnesDoubleGammaInv z 1 τ = 0) :
    deriv (fun w => barnesDoubleGammaInv w 1 τ) z ≠ 0 := by
  have hslit : (τ : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr hτ
  rcases (barnesDoubleGammaInv_eq_zero_iff z τ hslit).mp hz with
    rfl | ⟨p, rfl⟩
  · rw [deriv_barnesDoubleGammaInv_zero τ hslit]
    exact one_ne_zero
  · exact deriv_barnesDoubleGammaInv_neg_ne_zero τ hslit
      (barnesDoubleGammaLatticePoint_one_ofReal_injective τ hirr) p

/-- At positive irrational `τ`, the inverse Barnes double gamma has meromorphic order
one at a zero and zero elsewhere. This is the order form of
`deriv_barnesDoubleGammaInv_ne_zero_of_irrational`, from [95, Shintani (1977),
equation (1.5) and proof of Proposition 5, p. 181]. -/
theorem meromorphicOrderAt_barnesDoubleGammaInv (z : ℂ) (τ : ℝ)
    (hτ : 0 < τ) (hirr : Irrational τ) :
    meromorphicOrderAt (fun w => barnesDoubleGammaInv w 1 τ) z =
      if barnesDoubleGammaInv z 1 τ = 0 then 1 else 0 := by
  have hslit : (τ : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr hτ
  have han := (differentiable_barnesDoubleGammaInv τ hslit).analyticAt z
  by_cases hz : barnesDoubleGammaInv z 1 τ = 0
  · rw [han.meromorphicOrderAt_eq,
      han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz
        (deriv_barnesDoubleGammaInv_ne_zero_of_irrational z τ hτ hirr hz)]
    simp [hz]
  · rw [han.meromorphicOrderAt_eq, (han.analyticOrderAt_eq_zero).2 hz]
    simp [hz]

end SIC

end
