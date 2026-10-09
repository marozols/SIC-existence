/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.DoubleSine.Gamma
import SICs.SpecialFunctions.DoubleSine.SigmaSExponent
import SICs.SpecialFunctions.QPochhammer.Finite

/-!
# The Faddeev generator

The meromorphic generator `Φ_{S,0,0}`, joint continuity, reflection, shifts, and finite index
transport.

This module follows [RW26, Radchenko, Wheeler (2026), Section 2.1] and equation (20),
`eq:modulartofaddeevCF`. The generator is
`Φ_{S,0,0}(z;τ) = S₂(z+1;1,τ) exp(-X(z,τ))`, with `X` from
[AFK25, equation (8.6), `eq:SFJacobiCocycleTermsDoubleSine`], defined in
`SICs.SpecialFunctions.DoubleSine.SigmaSExponent`.

## The argument

Joint continuity of the Barnes quotient gives joint continuity of the generator in its argument
and slit-plane period wherever its gamma denominator is nonzero.
The double-sine difference equations yield shifts by `1` and `τ`, after the exponential
normalization converts sine factors to `1-e(x)`. Reflection pairs two gamma quotients and
combines their exponents. If `σ+1/τ` and `u-v/τ` are integers, the two shift factors agree,
so adjacent changes to `u` and `v` preserve their product. Iteration transports an integer
index when the gamma denominators are nonzero at the two endpoint arguments; closure of the
Barnes zero cone ensures regularity at all intermediate arguments. Totalized division makes
these nonvanishing hypotheses necessary for pointwise quotient identities.
-/

noncomputable section

open Complex Real Filter

namespace SIC

/-! ### The complex generator

The exponential normalization uses `faddeevSExpArg` from
`SICs.SpecialFunctions.DoubleSine.SigmaSExponent`. This fixes the reciprocal convention before
any shift is applied.
-/

/-- The generator `Φ_{S,0,0}(z;τ) = S₂(z+1;1,τ) exp(-X(z,τ))` of
[RW26, Radchenko, Wheeler (2026), Section 2.1], in the double-sine form used in the
proof of Proposition 5, `prop:starkfaddeev`. Values at poles are totalized to zero. -/
def faddeevS (z τ : ℂ) : ℂ :=
  shintaniDoubleSineGamma (z + 1) τ * Complex.exp (-faddeevSExpArg z τ)

/-- A nonzero Faddeev generator value has a nonzero gamma denominator. This is the
concrete-domain consequence of the totalized quotient defining `faddeevS`. -/
theorem faddeevS_denominator_ne_zero_of_ne_zero {z τ : ℂ} (hz : faddeevS z τ ≠ 0) :
    barnesDoubleGammaInv (τ - z) 1 τ ≠ 0 := by
  intro hden
  apply hz
  simp [faddeevS, shintaniDoubleSineGamma, barnesDoubleSineGamma,
    show (1 : ℂ) + τ - (z + 1) = τ - z by ring, hden]

/-- The generator `Φ_{S,0,0}(z;τ)` is jointly continuous for a slit-plane period when its
gamma denominator `Γ₂⁻¹(τ-z;1,τ)` is nonzero. This follows from
`continuousAt_shintaniDoubleSineGamma` and the definition in
[RW26, Radchenko, Wheeler (2026), Section 2.1]. -/
theorem continuousAt_faddeevS {z τ : ℂ} (hτ : τ ∈ Complex.slitPlane)
    (hz : barnesDoubleGammaInv (τ - z) 1 τ ≠ 0) :
    ContinuousAt (fun p : ℂ × ℂ => faddeevS p.1 p.2) (z, τ) := by
  have hden : barnesDoubleGammaInv (1 + τ - (z + 1)) 1 τ ≠ 0 := by
    simpa only [show (1 : ℂ) + τ - (z + 1) = τ - z by ring] using hz
  have hshift : ContinuousAt (fun p : ℂ × ℂ => (p.1 + 1, p.2)) (z, τ) :=
    (continuousAt_fst.add continuousAt_const).prodMk continuousAt_snd
  have hSbase : ContinuousAt (fun p : ℂ × ℂ =>
      shintaniDoubleSineGamma p.1 p.2) (z + 1, τ) :=
    continuousAt_shintaniDoubleSineGamma hτ hden
  have hS : ContinuousAt (fun p : ℂ × ℂ =>
      shintaniDoubleSineGamma (p.1 + 1) p.2) (z, τ) := by
    simpa only [Function.comp_def] using
      (hSbase.comp (f := fun p : ℂ × ℂ => (p.1 + 1, p.2)) hshift)
  have hExp : ContinuousAt (fun p : ℂ × ℂ =>
      Complex.exp (-faddeevSExpArg p.1 p.2)) (z, τ) := by
    exact Complex.continuous_exp.continuousAt.comp
      (continuousAt_faddeevSExpArg (Complex.slitPlane_ne_zero hτ)).neg
  change ContinuousAt (fun p : ℂ × ℂ =>
    shintaniDoubleSineGamma (p.1 + 1) p.2 *
      Complex.exp (-faddeevSExpArg p.1 p.2)) (z, τ)
  exact hS.mul hExp

/-- At a period in the open right half plane, the generator is continuous in its argument at
zero. This is the regular-origin consequence of `continuousAt_faddeevS`. -/
theorem continuousAt_faddeevS_zero_of_re_pos {τ : ℂ} (hτ : 0 < τ.re) :
    ContinuousAt (fun z : ℂ => faddeevS z τ) 0 := by
  have hslit : τ ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hτ)
  have hden : barnesDoubleGammaInv τ 1 τ ≠ 0 :=
    barnesDoubleGammaInv_ne_zero_of_re_pos τ τ hslit hτ.le hτ
  have hpair : ContinuousAt (fun z : ℂ => (z, τ)) 0 :=
    continuousAt_id.prodMk continuousAt_const
  simpa only [Function.comp_def] using
    (continuousAt_faddeevS (z := 0) (τ := τ) hslit (by simpa using hden)).comp_of_eq
      hpair rfl

/-- The generator `Φ_{S,0,0}(z;τ)` is meromorphic in `z` for every slit-plane period,
as in [RW26, Radchenko, Wheeler (2026), Section 2.1]. This follows from
`meromorphicAt_shintaniDoubleSineGamma` and the entire exponential normalization. -/
theorem meromorphicAt_faddeevS (z τ : ℂ) (hτ : τ ∈ Complex.slitPlane) :
    MeromorphicAt (fun w => faddeevS w τ) z := by
  have hshift : AnalyticAt ℂ (fun w : ℂ => w + 1) z := by fun_prop
  have hS : MeromorphicAt (fun w => shintaniDoubleSineGamma (w + 1) τ) z := by
    simpa only [Function.comp_def] using
      (meromorphicAt_shintaniDoubleSineGamma (z + 1) τ hτ).comp_analyticAt
        (g := fun w : ℂ => w + 1) hshift
  have hExp : AnalyticAt ℂ (fun w => Complex.exp (-faddeevSExpArg w τ)) z :=
    analyticAt_exp_neg_faddeevSExpArg z τ
  change MeromorphicAt
    ((fun w => shintaniDoubleSineGamma (w + 1) τ) *
      (fun w => Complex.exp (-faddeevSExpArg w τ))) z
  exact hS.mul hExp.meromorphicAt

/-- The generator is analytic where its gamma denominator is nonzero. This applies
`analyticAt_shintaniDoubleSineGamma` to `z+1` in the definition of `faddeevS`. -/
theorem analyticAt_faddeevS (z τ : ℂ) (hτ : τ ∈ Complex.slitPlane)
    (hz : barnesDoubleGammaInv (τ - z) 1 τ ≠ 0) :
    AnalyticAt ℂ (fun w => faddeevS w τ) z := by
  have hden : barnesDoubleGammaInv (1 + τ - (z + 1)) 1 τ ≠ 0 := by
    simpa only [show 1 + τ - (z + 1) = τ - z by ring] using hz
  have hshift : AnalyticAt ℂ (fun w : ℂ => w + 1) z := by fun_prop
  have hS : AnalyticAt ℂ (fun w => shintaniDoubleSineGamma (w + 1) τ) z := by
    simpa only [Function.comp_def] using
      (analyticAt_shintaniDoubleSineGamma (z + 1) τ hτ hden).comp
        (f := fun w : ℂ => w + 1) hshift
  have hExp : AnalyticAt ℂ (fun w => Complex.exp (-faddeevSExpArg w τ)) z :=
    analyticAt_exp_neg_faddeevSExpArg z τ
  change AnalyticAt ℂ
    ((fun w => shintaniDoubleSineGamma (w + 1) τ) *
      (fun w => Complex.exp (-faddeevSExpArg w τ))) z
  exact hS.mul hExp

/-! ### Reflection

The double-sine arguments in `Φ(z+τ-1;τ) Φ(-z;τ)` sum to `1+τ`. Their gamma
quotients cancel wherever both denominators are nonzero. Adding the two normalization
exponents gives equation (13), including its constant factor `i`.
-/

/-- The reflection identity `Φ(z+τ-1;τ) Φ(-z;τ) =
i exp(-πi(τ+τ⁻¹)/6) exp(-πi(z²/τ+z-z/τ))` of
[RW26, Radchenko, Wheeler (2026), equation (13), `eq:PhiS.reflection`], on the domain
of the two gamma quotients. The right side combines the three exponentials into one,
with the term `-1/2` contributing `i`. -/
@[source "RW26, equation (13), p. 5, eq:PhiS.reflection (finite gamma quotients)"]
theorem faddeevS_mul_neg (z τ : ℂ) (hτ : τ ≠ 0)
    (hz : barnesDoubleGammaInv (1 - z) 1 τ ≠ 0)
    (hzτ : barnesDoubleGammaInv (z + τ) 1 τ ≠ 0) :
    faddeevS (z + τ - 1) τ * faddeevS (-z) τ =
      Complex.exp (-π * I *
        (z ^ 2 / τ + (1 - τ⁻¹) * z + (τ + τ⁻¹) / 6 - 1 / 2)) := by
  have hS : shintaniDoubleSineGamma (z + τ) τ *
      shintaniDoubleSineGamma (1 - z) τ = 1 := by
    unfold shintaniDoubleSineGamma barnesDoubleSineGamma
    rw [show (1 : ℂ) + τ - (z + τ) = 1 - z by ring,
      show (1 : ℂ) + τ - (1 - z) = z + τ by ring]
    field_simp
  have hX : -faddeevSExpArg (z + τ - 1) τ +
      -faddeevSExpArg (-z) τ =
      -π * I * (z ^ 2 / τ + (1 - τ⁻¹) * z + (τ + τ⁻¹) / 6 - 1 / 2) := by
    unfold faddeevSExpArg
    field_simp
    ring
  unfold faddeevS
  rw [show z + τ - 1 + 1 = z + τ by ring, show -z + 1 = 1 - z by ring]
  calc
    _ = (shintaniDoubleSineGamma (z + τ) τ *
          shintaniDoubleSineGamma (1 - z) τ) *
          Complex.exp (-faddeevSExpArg (z + τ - 1) τ +
            -faddeevSExpArg (-z) τ) := by
        rw [Complex.exp_add]
        ring
    _ = _ := by rw [hS, hX, one_mul]

/-! ### Shift laws

The double-sine sine multipliers become `1 - e(z)` after the exponential normalization.
The gamma denominators control the domain of each integer shift.
-/

/-- The exponential normalization converts a sine multiplier into a finite-product factor.
Used by `faddeevS_add_one` and `faddeevS_add_tau`. -/
private lemma faddeevS_exp_shift (a b x : ℂ)
    (h : b - a = π * I * x - π * I / 2) :
    Complex.exp (-b) * (1 - Complex.exp (2 * π * I * x)) =
      2 * Complex.sin (π * x) * Complex.exp (-a) := by
  have hfactor : (1 : ℂ) - Complex.exp (2 * π * I * x) =
      2 * Complex.sin (π * x) * Complex.exp (π * I * x - π * I / 2) := by
    rw [one_sub_exp_two_pi_I_eq_two_exp_shift,
      show π * I * x - π * I / 2 = π * I * x - π / 2 * I by ring]
    ring
  have hphase : Complex.exp (-b) * Complex.exp (π * I * x - π * I / 2) =
      Complex.exp (-a) := by
    rw [← Complex.exp_add]
    congr 1
    linear_combination -h
  rw [hfactor]
  calc
    Complex.exp (-b) * (2 * Complex.sin (π * x) *
        Complex.exp (π * I * x - π * I / 2)) =
        2 * Complex.sin (π * x) *
          (Complex.exp (-b) * Complex.exp (π * I * x - π * I / 2)) := by ring
    _ = _ := by rw [hphase]

/-- The period-one shift `Φ(z+1)(1-e((z+1)/τ)) = Φ(z)` of
[RW26, Radchenko, Wheeler (2026), Section 2.1], where both gamma quotients are finite. -/
theorem faddeevS_add_one (z τ : ℂ) (hτ : τ ∈ Complex.slitPlane)
    (hz1 : barnesDoubleGammaInv (τ - z - 1) 1 τ ≠ 0) :
    faddeevS (z + 1) τ * (1 - Complex.exp (2 * π * I * ((z + 1) / τ))) =
      faddeevS z τ := by
  have hS := shintaniDoubleSineGamma_eq_two_sin_mul_add_one (z + 1) τ hτ
    (by simpa only [show τ - (z + 1) = τ - z - 1 by ring] using hz1)
  have hX := faddeevSExpArg_add_one z τ (Complex.slitPlane_ne_zero hτ)
  calc
    faddeevS (z + 1) τ * (1 - Complex.exp (2 * π * I * ((z + 1) / τ))) =
        shintaniDoubleSineGamma (z + 1 + 1) τ *
          (Complex.exp (-faddeevSExpArg (z + 1) τ) *
            (1 - Complex.exp (2 * π * I * ((z + 1) / τ)))) := by
        unfold faddeevS
        ring
    _ = shintaniDoubleSineGamma (z + 1 + 1) τ *
          (2 * Complex.sin (π * ((z + 1) / τ)) *
            Complex.exp (-faddeevSExpArg z τ)) := by
        rw [faddeevS_exp_shift _ _ _ hX]
    _ = faddeevS z τ := by
        unfold faddeevS
        rw [hS]
        ring_nf

/-- The period-τ shift `Φ(z+τ)(1-e(z)) = Φ(z)` of
[RW26, Radchenko, Wheeler (2026), Section 2.1], where both gamma quotients are finite. -/
theorem faddeevS_add_tau (z τ : ℂ) (hτ : τ ∈ Complex.slitPlane)
    (hzτ : barnesDoubleGammaInv (-z) 1 τ ≠ 0) :
    faddeevS (z + τ) τ * (1 - Complex.exp (2 * π * I * z)) = faddeevS z τ := by
  have hS := shintaniDoubleSineGamma_eq_two_sin_mul_add_tau (z + 1) τ hτ
    (by simpa only [show 1 - (z + 1) = -z by ring] using hzτ)
  have hX := faddeevSExpArg_add_tau z τ (Complex.slitPlane_ne_zero hτ)
  have hperiod : Complex.exp (2 * π * I * (z + 1)) =
      Complex.exp (2 * π * I * z) :=
    exp_two_pi_I_eq_of_sub_intCast (z + 1) z 1 (by ring)
  calc
    faddeevS (z + τ) τ * (1 - Complex.exp (2 * π * I * z)) =
        shintaniDoubleSineGamma ((z + 1) + τ) τ *
          (Complex.exp (-faddeevSExpArg (z + τ) τ) *
            (1 - Complex.exp (2 * π * I * (z + 1)))) := by
        unfold faddeevS
        rw [hperiod]
        ring_nf
    _ = shintaniDoubleSineGamma ((z + 1) + τ) τ *
          (2 * Complex.sin (π * (z + 1)) *
            Complex.exp (-faddeevSExpArg z τ)) := by
        rw [faddeevS_exp_shift _ _ _ hX]
    _ = faddeevS z τ := by
        unfold faddeevS
        rw [hS]
        ring_nf

/-- The adjacent-factor transport
`Φ(u+σ;σ) Φ(v-1;τ) = Φ(u;σ) Φ(v;τ)` when `u-v/τ ∈ ℤ`, at finite gamma quotients.
This combines `faddeevS_add_tau` and `faddeevS_add_one` for the intermediate-index transport
of [RW26, Radchenko, Wheeler (2026), equation (20), `eq:modulartofaddeevCF`]. -/
theorem faddeevS_transfer_one (u v σ τ : ℂ) (k : ℤ)
    (hσ : σ ∈ Complex.slitPlane) (hτ : τ ∈ Complex.slitPlane)
    (huv : u - v / τ = k)
    (huσ : barnesDoubleGammaInv (-u) 1 σ ≠ 0)
    (hv1 : barnesDoubleGammaInv (τ - v) 1 τ ≠ 0) :
    faddeevS (u + σ) σ * faddeevS (v - 1) τ =
      faddeevS u σ * faddeevS v τ := by
  have hvden1 : barnesDoubleGammaInv (τ - (v - 1) - 1) 1 τ ≠ 0 := by
    simpa only [show τ - (v - 1) - 1 = τ - v by ring] using hv1
  have hunit : faddeevS v τ * (1 - Complex.exp (2 * π * I * (v / τ))) =
      faddeevS (v - 1) τ := by
    simpa only [sub_add_cancel] using
      (faddeevS_add_one (v - 1) τ hτ hvden1)
  have hphase := exp_two_pi_I_eq_of_sub_intCast u (v / τ) k huv
  have hperiod := faddeevS_add_tau u σ hσ huσ
  calc
    faddeevS (u + σ) σ * faddeevS (v - 1) τ =
        faddeevS (u + σ) σ *
          (faddeevS v τ * (1 - Complex.exp (2 * π * I * (v / τ)))) := by
            rw [hunit]
    _ = (faddeevS (u + σ) σ *
          (1 - Complex.exp (2 * π * I * u))) * faddeevS v τ := by
            rw [hphase]
            ring
    _ = faddeevS u σ * faddeevS v τ := by rw [hperiod]

/-! ### Finite integer paths

The arbitrary-index transport uses the values at every integer between `0` and the final
index, including both endpoints. Its domain condition is nonvanishing of the displayed
gamma denominator along each argument path.
-/

/-- The gamma denominator of `Φ(arg(j);τ)` is nonzero for every integer between `0` and `r`.
Here regularity means exactly `barnesDoubleGammaInv (τ - arg j) 1 τ ≠ 0` at those indices.
This packages the finite-path domain condition of `faddeevS_transfer_int`. -/
def FaddeevSRegularPath (τ : ℂ) (r : ℤ) (arg : ℤ → ℂ) : Prop :=
  ∀ j ∈ Set.uIcc (0 : ℤ) r, barnesDoubleGammaInv (τ - arg j) 1 τ ≠ 0

/-- Introduces the finite-path denominator condition from its pointwise inequalities. -/
theorem FaddeevSRegularPath.of_forall {τ : ℂ} {r : ℤ} {arg : ℤ → ℂ}
    (h : ∀ j ∈ Set.uIcc (0 : ℤ) r, barnesDoubleGammaInv (τ - arg j) 1 τ ≠ 0) :
    FaddeevSRegularPath τ r arg := by
  exact h

/-- Evaluates the denominator condition at any integer on the finite path. -/
theorem FaddeevSRegularPath.denominator_ne_zero {τ : ℂ} {r : ℤ} {arg : ℤ → ℂ}
    (h : FaddeevSRegularPath τ r arg) (j : ℤ) (hj : j ∈ Set.uIcc (0 : ℤ) r) :
    barnesDoubleGammaInv (τ - arg j) 1 τ ≠ 0 := by
  exact h j hj

/-- Restricts the denominator condition to a smaller integer interval. -/
theorem FaddeevSRegularPath.mono {τ : ℂ} {r s : ℤ} {arg : ℤ → ℂ}
    (h : FaddeevSRegularPath τ r arg) (hsub : Set.uIcc (0 : ℤ) s ⊆ Set.uIcc 0 r) :
    FaddeevSRegularPath τ s arg := by
  exact FaddeevSRegularPath.of_forall (fun j hj => h.denominator_ne_zero j (hsub hj))

/-- A Barnes zero remains a zero after subtracting a natural multiple of the period. -/
private lemma barnesDoubleGammaInv_eq_zero_sub_nat_period (w τ : ℂ)
    (hτ : τ ∈ Complex.slitPlane) (n : ℕ)
    (hw : barnesDoubleGammaInv w 1 τ = 0) :
    barnesDoubleGammaInv (w - n * τ) 1 τ = 0 := by
  induction n with
  | zero => simpa using hw
  | succ n ih =>
      have h := barnesDoubleGammaInv_eq_zero_of_eq_zero_sub_period
        (w - n * τ) τ hτ ih
      simpa [Nat.cast_succ, add_mul, sub_add_eq_sub_sub] using h

/-- A Barnes zero remains a zero after subtracting a natural number. -/
private lemma barnesDoubleGammaInv_eq_zero_sub_nat_one (w τ : ℂ)
    (hτ : τ ∈ Complex.slitPlane) (n : ℕ)
    (hw : barnesDoubleGammaInv w 1 τ = 0) :
    barnesDoubleGammaInv (w - n) 1 τ = 0 := by
  induction n with
  | zero => simpa using hw
  | succ n ih =>
      have h := barnesDoubleGammaInv_eq_zero_of_eq_zero_sub_one
        (w - n) τ hτ ih
      simpa [Nat.cast_succ, sub_add_eq_sub_sub] using h

/-- A nonzero denominator at the last forward index ensures regularity of the whole path
`j ↦ u+jτ`. -/
theorem FaddeevSRegularPath.of_endpoint_add_mul (u τ : ℂ)
    (hτ : τ ∈ Complex.slitPlane) (r : ℤ)
    (hu : barnesDoubleGammaInv (τ - (u + (max r 0 : ℤ) * τ)) 1 τ ≠ 0) :
    FaddeevSRegularPath τ r (fun j => u + j * τ) := by
  intro j hj hzero
  have hjle : j ≤ max r 0 := by
    rcases Set.mem_uIcc.mp hj with h | h <;> omega
  have hn : 0 ≤ max r 0 - j := by omega
  let n := (max r 0 - j).toNat
  have hncast : (n : ℤ) = max r 0 - j := Int.toNat_of_nonneg hn
  have hlast := barnesDoubleGammaInv_eq_zero_sub_nat_period
    (τ - (u + j * τ)) τ hτ n hzero
  have hnC : (n : ℂ) = (max r 0 - j : ℤ) := by exact_mod_cast hncast
  have harg : τ - (u + (max r 0 : ℤ) * τ) =
      τ - (u + j * τ) - n * τ := by
    rw [hnC]
    push_cast
    ring
  exact hu (by simpa only [← harg] using hlast)

/-- A nonzero denominator at the first backward index ensures regularity of the whole path
`j ↦ v-j`. -/
theorem FaddeevSRegularPath.of_endpoint_sub (v τ : ℂ)
    (hτ : τ ∈ Complex.slitPlane) (r : ℤ)
    (hv : barnesDoubleGammaInv (τ - (v - (min r 0 : ℤ))) 1 τ ≠ 0) :
    FaddeevSRegularPath τ r (fun j => v - j) := by
  intro j hj hzero
  have hjge : min r 0 ≤ j := by
    rcases Set.mem_uIcc.mp hj with h | h <;> omega
  have hn : 0 ≤ j - min r 0 := by omega
  let n := (j - min r 0).toNat
  have hncast : (n : ℤ) = j - min r 0 := Int.toNat_of_nonneg hn
  have hfirst := barnesDoubleGammaInv_eq_zero_sub_nat_one
    (τ - (v - j)) τ hτ n hzero
  have hnC : (n : ℂ) = (j - min r 0 : ℤ) := by exact_mod_cast hncast
  have harg : τ - (v - (min r 0 : ℤ)) = τ - (v - j) - n := by
    rw [hnC]
    push_cast
    ring
  exact hv (by simpa only [← harg] using hfirst)

/-- Transport of the two Faddeev factors from index `j` to `j+1`.
Used by `faddeevS_transfer_int`. -/
private theorem faddeevS_transfer_step (u v σ τ : ℂ) (k l j : ℤ)
    (hσ : σ ∈ Complex.slitPlane) (hτ : τ ∈ Complex.slitPlane)
    (hστ : σ + 1 / τ = l) (huv : u - v / τ = k)
    (hu₁ : barnesDoubleGammaInv (σ - (u + (j + 1 : ℤ) * σ)) 1 σ ≠ 0)
    (hv₀ : barnesDoubleGammaInv (τ - (v - j)) 1 τ ≠ 0) :
    faddeevS (u + (j + 1 : ℤ) * σ) σ * faddeevS (v - (j + 1 : ℤ)) τ =
      faddeevS (u + j * σ) σ * faddeevS (v - j) τ := by
  have hphase : (u + j * σ) - (v - j) / τ = (k + j * l : ℤ) := by
    calc
      (u + j * σ) - (v - j) / τ = (u - v / τ) + j * (σ + 1 / τ) := by ring
      _ = (k + j * l : ℤ) := by rw [huv, hστ]; push_cast; ring
  have hu' : barnesDoubleGammaInv (-(u + j * σ)) 1 σ ≠ 0 := by
    convert hu₁ using 1; push_cast; ring_nf
  have hstep := faddeevS_transfer_one (u + j * σ) (v - j) σ τ (k + j * l)
    hσ hτ hphase hu' hv₀
  convert hstep using 1; push_cast; ring_nf

/-- The adjacent-factor transport along two regular finite paths. This is the induction
underlying `faddeevS_transfer_int`. -/
private theorem faddeevS_transfer_int_of_regularPath (u v σ τ : ℂ) (k l r : ℤ)
    (hσ : σ ∈ Complex.slitPlane) (hτ : τ ∈ Complex.slitPlane)
    (hστ : σ + 1 / τ = l) (huv : u - v / τ = k)
    (hu : FaddeevSRegularPath σ r (fun j => u + j * σ))
    (hv : FaddeevSRegularPath τ r (fun j => v - j)) :
    faddeevS (u + r * σ) σ * faddeevS (v - r) τ =
      faddeevS u σ * faddeevS v τ := by
  induction r using Int.induction_on with
  | zero => simp
  | succ i ih =>
      have hj : (i : ℤ) ∈ Set.uIcc 0 ((i : ℤ) + 1) :=
        Set.mem_uIcc_of_le (by omega) (by omega)
      have hsub := Set.uIcc_subset_uIcc Set.left_mem_uIcc hj
      have hprev := ih (hu.mono hsub) (hv.mono hsub)
      exact (faddeevS_transfer_step u v σ τ k l (i : ℤ) hσ hτ hστ huv
        (hu.denominator_ne_zero ((i : ℤ) + 1) Set.right_mem_uIcc)
        (hv.denominator_ne_zero (i : ℤ) hj)).trans hprev
  | pred i ih =>
      have hj : -(i : ℤ) ∈ Set.uIcc 0 (-(i : ℤ) - 1) :=
        Set.mem_uIcc_of_ge (by omega) (by omega)
      have hsub := Set.uIcc_subset_uIcc Set.left_mem_uIcc hj
      have hprev := ih (hu.mono hsub) (hv.mono hsub)
      have hidx : -(i : ℤ) - 1 + 1 = -(i : ℤ) := by omega
      have hstep := faddeevS_transfer_step u v σ τ k l (-(i : ℤ) - 1) hσ hτ hστ huv
        (by simpa only [hidx] using hu.denominator_ne_zero (-(i : ℤ)) hj)
        (hv.denominator_ne_zero (-(i : ℤ) - 1) Set.right_mem_uIcc)
      have hstep' := by simpa only [hidx] using hstep
      exact hstep'.symm.trans hprev

/-- The adjacent-factor transport
`Φ(u+rσ;σ) Φ(v-r;τ) = Φ(u;σ) Φ(v;τ)` for `r ∈ ℤ`, when
`σ+1/τ ∈ ℤ` and `u-v/τ ∈ ℤ`. The gamma denominators are nonzero at the two endpoints.
This iterates `faddeevS_transfer_one` for the arbitrary
intermediate indices in [RW26, Radchenko, Wheeler (2026), equation (20),
`eq:modulartofaddeevCF`]. -/
theorem faddeevS_transfer_int (u v σ τ : ℂ) (k l r : ℤ)
    (hσ : σ ∈ Complex.slitPlane) (hτ : τ ∈ Complex.slitPlane)
    (hστ : σ + 1 / τ = l) (huv : u - v / τ = k)
    (hu : barnesDoubleGammaInv (σ - (u + (max r 0 : ℤ) * σ)) 1 σ ≠ 0)
    (hv : barnesDoubleGammaInv (τ - (v - (min r 0 : ℤ))) 1 τ ≠ 0) :
    faddeevS (u + r * σ) σ * faddeevS (v - r) τ =
      faddeevS u σ * faddeevS v τ := by
  exact faddeevS_transfer_int_of_regularPath u v σ τ k l r hσ hτ hστ huv
    (FaddeevSRegularPath.of_endpoint_add_mul u σ hσ r hu)
    (FaddeevSRegularPath.of_endpoint_sub v τ hτ r hv)

end SIC

end
