/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.DoubleSine.Comparison
import SICs.SpecialFunctions.DoubleSine.IntegralRepresentation
import SICs.Cocycle.UpperHalfPlane
import SICs.Cocycle.SigmaS.Reduction

/-!
# The real boundary of the cocycle and the generator comparison

The upper-half-plane generator as equation (8.6) with the integral representation, off the period
lattice, and its real boundary limit at an arbitrary real argument.

This file relates the upper-half-plane `S`-generator of `SICs.Cocycle.UpperHalfPlane` to the
double-sine constructions of [AFK25, equations (8.6)--(8.7),
`eq:SFJacobiCocycleTermsDoubleSine` and `eq:dsintrep`], [95, Shintani (1977), Proposition 5],
and [72, Kopp (2024), Theorem 4.23, `thm:shin5`]. The complex integral expression restricts to
the real `sigmaSBase`; the upper-half-plane generator is exactly the corresponding q-product
quotient; and, off the period lattice, it is Kopp's expression with Shintani's product as its
double sine, hence, on the source chamber, [AFK25, equation (8.6),
`eq:SFJacobiCocycleTermsDoubleSine`] with the integral representation of the double sine at
`z + 1`.

The integral, gamma-ratio, and q-product constructions live independently in
`SICs.SpecialFunctions.DoubleSine`, with their mutual comparisons: Shintani's Proposition 5
(`shintaniDoubleSineGamma_eq_product` in
`SICs.SpecialFunctions.DoubleSine.Comparison`) and the integral representation
(`shintaniDoubleSineGamma_eq_integral` in
`SICs.SpecialFunctions.DoubleSine.IntegralRepresentation`). With the joint continuity of the
integral representation, the last section passes one generator to the real boundary: parameters
approaching a real pair of the chamber carry the upper-half-plane generator to `sigmaSBase`.
`SICs.Cocycle.Word.UpperHalfPlane` chains these limits along a canonical word.

The raw q-product uses pointwise division: at a zero of the second product, such as `z = 1`,
its value is `0`. The gamma ratio is nonzero there when `Re τ > 0`. Hence the comparisons with
the raw product are stated off the period lattice `ℤ + ℤτ`, where the two products are nonzero;
this is also where the source's `σ_S` has neither zeros nor poles.

The generator statements are about the product quotient `sfJacobiCocycleUHP` on `ℍ`, where it is
the source's `σ_S` before continuation to `D_S`; each carries `0 < Im τ`, and the continuation
itself is not formalized.
-/
noncomputable section

open Complex Real
open scoped MatrixGroups

namespace SIC

/-! ### The complex `σ_S` base expression -/

/-- The complex integral form of the `S`-generator continuation in [AFK25, equation (8.6),
`eq:SFJacobiCocycleTermsDoubleSine`]:

```text
σ_S(z,τ) = exp(πi(6z² + 6(1-τ)z + τ² - 3τ + 1)/(12τ)) / S₂(z+1,τ).
```

On the source chamber `0 < re(τ)` and `-1 < re(z) < re(τ)`, the denominator is represented by
`doubleSineComplexIntegral`.  Agreement with the upper-half-plane q-product on that chamber is
`sfJacobiCocycle_S_eq_sigmaSComplexIntegralBase` below. -/
noncomputable def sigmaSComplexIntegralBase (z tau : ℂ) : ℂ :=
  Complex.exp (faddeevSExpArg z tau) /
    doubleSineComplexIntegral (z + 1) tau

/-- **The complex integral formula for `σ_S` restricts to the real base generator.**
This is [AFK25, equation (8.6), `eq:SFJacobiCocycleTermsDoubleSine`] on the real line. -/
lemma sigmaSComplexIntegralBase_ofReal (z tau : ℝ) :
    sigmaSComplexIntegralBase z tau = sigmaSBase z tau := by
  unfold sigmaSComplexIntegralBase
  rw [show (z : ℂ) + 1 = ((z + 1 : ℝ) : ℂ) by push_cast; rfl,
    doubleSineComplexIntegral_ofReal]
  rw [sigmaSBase_eq_exp_div]
  rfl

/-- The upper-half-plane `S`-generator quotient is exactly Shintani's second product, including
its omitted `n = 0` factor, divided by the first product:

```text
sigma_S(z,tau) = (1 - exp(2πiz/tau)) f₂(z,tau) / f₁(z,tau).
```

This is the product side of [95, Shintani (1977), Proposition 5] after
`(ω₁,ω₂) = (1,tau)`, and the left side is [72, Kopp (2024), Theorem 4.23,
`thm:shin5`]. This pointwise product ratio is restricted to nonzero `ϖ(z,τ)`;
at a common zero, the cocycle instead uses the meromorphic quotient's regularized value. -/
lemma sfJacobiCocycle_S_eq_shintani_products (z tau : ℂ) (htau : 0 < tau.im)
    (hden : qPochhammer z tau ≠ 0) :
    sfJacobiCocycleUHP
        (ModularGroup.S : Mat(2, ℤ)) z tau =
      (1 - Complex.exp (2 * π * I * (z / tau))) *
          shintaniF2 z tau /
        shintaniF1 z tau := by
  have hinv := neg_one_div_im_pos tau htau
  have hsplit := qPochhammerFin_natCast_mul_qPochhammer_add
    1 (z / tau) (-1 / tau) hinv
  change qPochhammerFin 1 (z / tau) (-1 / tau) * _ = _ at hsplit
  rw [qPochhammerFin_one] at hsplit
  simp only [Nat.cast_one, one_mul] at hsplit
  rw [sfJacobiCocycleUHP_eq_quotient _ _ _ hden]
  unfold shintaniF1 shintaniF2
  simp only [fltDenominator, flt]
  norm_num
  rw [show z / tau + -1 / tau = (z - 1) / tau by ring] at hsplit
  rw [hsplit]

/-! ### The integral generator and normalization comparison

[72, Kopp (2024), Theorem 4.23, `thm:shin5`] writes `σ_S(z,τ)` through `S₂(z,τ)`; the
exponential conversion below recovers [AFK25, equation (8.6),
`eq:SFJacobiCocycleTermsDoubleSine`], whose double sine is evaluated at `z + 1`. Both forms are
proved for the upper-half-plane product generator off the period lattice with Shintani's
product expression, which is where the raw pointwise quotient is the source's meromorphic
`S₂`; the form of equation (8.6) is then rewritten, on the source chamber, with the integral
representation `shintaniDoubleSineGamma_eq_integral`. -/

/-- The exponential conversion between Kopp's normalization and [AFK25, equation (8.6),
`eq:SFJacobiCocycleTermsDoubleSine`], for any value `S` of the double sine at `z` and
`S₁ = S / (2 sin(πz/τ))` at `z + 1`:

```text
exp(E_K(z,τ)) (1 - exp(2πiz/τ)) / S = exp(πi(6z² + 6(1-τ)z + τ² - 3τ + 1)/(12τ)) / S₁.
```

The same algebra serves Shintani's product and the integral representation. -/
private lemma kopp_exp_div_eq_afk_exp_div (z tau S S₁ : ℂ) (htau : tau ≠ 0)
    (hS₁ : S₁ = S / (2 * Complex.sin (π * z / tau))) :
    Complex.exp (sigmaSKoppExpArg z tau) * (1 - Complex.exp (2 * π * I * (z / tau))) / S =
      Complex.exp (faddeevSExpArg z tau) / S₁ := by
  have hphase :
      Complex.exp (sigmaSKoppExpArg z tau) * (-I) *
          Complex.exp (π * I * (z / tau)) =
        Complex.exp (faddeevSExpArg z tau) := by
    rw [show -I = Complex.exp (-π / 2 * I) by
      rw [Complex.exp_neg_pi_div_two_mul_I], ← Complex.exp_add, ← Complex.exp_add,
      show sigmaSKoppExpArg z tau + -π / 2 * I + π * I * (z / tau) =
        sigmaSKoppExpArg z tau + π * I * (z / tau) + (-π / 2 * I) by ring,
      sigmaSKoppExpArg_add_shift z tau htau]
  have hnum := congrArg (fun w => 2 * Complex.sin (π * z / tau) * w) hphase
  rw [one_sub_exp_two_pi_I_eq, hS₁, div_div_eq_mul_div,
    show π * (z / tau) = π * z / tau by ring]
  convert congrArg (fun w => w / S) hnum using 1 <;> ring

/-- Off the period lattice, the upper-half-plane generator is Kopp's expression with Shintani's
product as its double sine:

```text
sigma_S(z,tau) = exp(E_K(z,tau)) (1 - exp(2πiz/tau)) / S₂^prod(z,tau).
```

This is [72, Kopp (2024), Theorem 4.23, `thm:shin5`] with the double sine written by
[95, Shintani (1977), Proposition 5]; off the lattice `f₁(z)` and `f₂(z)` are nonzero, so the
raw quotient is the source's meromorphic value. -/
lemma sfJacobiCocycle_S_eq_doubleSineProduct (z tau : ℂ)
    (htau : 0 < tau.im) (hlat : ¬ IsPeriodLatticePoint tau z) :
    sfJacobiCocycleUHP
        (ModularGroup.S : Mat(2, ℤ)) z tau =
      Complex.exp (sigmaSKoppExpArg z tau) *
          (1 - Complex.exp (2 * π * I * (z / tau))) /
        shintaniDoubleSineProduct z tau := by
  have htau0 : tau ≠ 0 := fun hzero => by simp [hzero] at htau
  have hz := (not_isPeriodLatticePoint_iff tau z).mp hlat
  have hF1 := shintaniF1_ne_zero_of_not_mem_lattice z tau htau hz
  have hF2 := shintaniF2_ne_zero_of_not_mem_lattice z tau htau hz
  rw [sfJacobiCocycle_S_eq_shintani_products z tau htau
      (qPochhammer_ne_zero_of_not_isPeriodLatticePoint htau hlat),
    shintaniDoubleSineProduct_eq_exp_sigmaSKoppExpArg z tau htau0]
  field_simp [Complex.exp_ne_zero, hF1, hF2]

/-- Off the period lattice, the upper-half-plane generator is [AFK25, equation (8.6),
`eq:SFJacobiCocycleTermsDoubleSine`] with Shintani's product at `z + 1` as its double sine:

```text
sigma_S(z,tau) = exp(πi(6z² + 6(1-τ)z + τ² - 3τ + 1)/(12τ)) / S₂^prod(z+1,tau).
```

This converts `sfJacobiCocycle_S_eq_doubleSineProduct` by the
product's period-one law `shintaniDoubleSineProduct_add_one`. -/
lemma sfJacobiCocycle_S_eq_doubleSineProduct_add_one (z tau : ℂ)
    (htau : 0 < tau.im) (hlat : ¬ IsPeriodLatticePoint tau z) :
    sfJacobiCocycleUHP
        (ModularGroup.S : Mat(2, ℤ)) z tau =
      Complex.exp (faddeevSExpArg z tau) /
        shintaniDoubleSineProduct (z + 1) tau := by
  have htau0 : tau ≠ 0 := fun hzero => by simp [hzero] at htau
  rw [sfJacobiCocycle_S_eq_doubleSineProduct z tau htau hlat]
  exact kopp_exp_div_eq_afk_exp_div z tau _ _ htau0
    (shintaniDoubleSineProduct_add_one z tau htau)

/-- **The upper-half-plane generator is [AFK25, equation (8.6),
`eq:SFJacobiCocycleTermsDoubleSine`] with the integral representation.** For `Im τ > 0`,
`Re τ > 0`, `-1 < Re z < Re τ`, and `z` off the period lattice,

```text
sigma_S(z,tau) = sigmaSComplexIntegralBase(z,tau).
```

The double sine of the source formula is evaluated at `z + 1`, which lies on the source chamber
of [AFK25, equation (8.7), `eq:dsintrep`] exactly when `-1 < Re z < Re τ`. The proof is
`sfJacobiCocycle_S_eq_doubleSineProduct_add_one` together with
[95, Shintani (1977), Proposition 5] and the integral representation at `z + 1`. -/
theorem sfJacobiCocycle_S_eq_sigmaSComplexIntegralBase (z tau : ℂ)
    (htau : 0 < tau.im) (htauRe : 0 < tau.re) (hz : -1 < z.re) (hzUpper : z.re < tau.re)
    (hlat : ¬ IsPeriodLatticePoint tau z) :
    sfJacobiCocycleUHP
        (ModularGroup.S : Mat(2, ℤ)) z tau =
      sigmaSComplexIntegralBase z tau := by
  have hlat1 : ¬ IsPeriodLatticePoint tau (z + 1) :=
    fun h => hlat ((isPeriodLatticePoint_add_one_iff tau z).mp h)
  rw [sfJacobiCocycle_S_eq_doubleSineProduct_add_one z tau htau hlat]
  unfold sigmaSComplexIntegralBase
  rw [← shintaniDoubleSineGamma_eq_product_of_forall_ne (z + 1) tau
    htau ((not_isPeriodLatticePoint_iff tau (z + 1)).mp hlat1),
    shintaniDoubleSineGamma_eq_integral (z + 1) tau htau htauRe
      (by simp only [add_re, one_re]; linarith) (by simp only [add_re, one_re]; linarith)]

/-! ### The passage to the real boundary

The chamber of [AFK25, equation (8.7), `eq:dsintrep`] is open and contains the real points
`τ > 0`, `-1 < z < τ`, so the joint continuity `continuousAt_doubleSineComplexIntegral` turns
the real restriction `sigmaSComplexIntegralBase_ofReal` into a limit statement: complex
parameters approaching a real pair `(z, τ)` of that chamber carry `σ_S` to `sigmaSBase z τ`.

This is the analytic step of the passage `τ → α` in the proof of [72, Kopp (2024), Theorem
4.46, `thm:cllr`], at the level of one generator. What it does not do is continue the cocycle
past the upper half plane: the generator statement below still needs its approaching arguments
to lie in `ℍ` and off the period lattice, which is where
`sfJacobiCocycle_S_eq_sigmaSComplexIntegralBase` identifies the product quotient with
equation (8.6). -/

/-- The complex integral form of the `S`-generator is jointly continuous on the chamber
`Re τ > 0`, `-1 < Re z < Re τ`: the phase is continuous where `τ ≠ 0`, and the double sine at
`z + 1` is continuous and nonvanishing there. -/
theorem continuousAt_sigmaSComplexIntegralBase {z tau : ℂ} (htau : 0 < tau.re)
    (hz : -1 < z.re) (hzUpper : z.re < tau.re) :
    ContinuousAt (fun p : ℂ × ℂ => sigmaSComplexIntegralBase p.1 p.2) (z, tau) := by
  have htau0 : tau ≠ 0 := Complex.ne_zero_of_re_pos htau
  have hnum : ContinuousAt (fun p : ℂ × ℂ =>
      Complex.exp (faddeevSExpArg p.1 p.2)) (z, tau) :=
    (continuousAt_faddeevSExpArg htau0).cexp
  have hshift : ContinuousAt (fun p : ℂ × ℂ => (p.1 + 1, p.2)) (z, tau) := by fun_prop
  have houter : ContinuousAt (fun p : ℂ × ℂ => doubleSineComplexIntegral p.1 p.2)
      (z + 1, tau) :=
    continuousAt_doubleSineComplexIntegral htau
      (by simp only [Complex.add_re, Complex.one_re]; linarith)
      (by simp only [Complex.add_re, Complex.one_re]; linarith)
  have hden : ContinuousAt (fun p : ℂ × ℂ => doubleSineComplexIntegral (p.1 + 1) p.2)
      (z, tau) :=
    ContinuousAt.comp (f := fun p : ℂ × ℂ => (p.1 + 1, p.2)) (x := (z, tau)) houter hshift
  exact hnum.div hden (doubleSineComplexIntegral_ne_zero _ _)

/-- **The generator's boundary limit, in integral form.** If `τ > 0` and `-1 < z < τ` are real
and the complex parameters `(z_n, τ_n)` tend to `(z, τ)`, then
`σ_S(z_n, τ_n) → sigmaSBase z τ`. -/
theorem tendsto_sigmaSComplexIntegralBase {ι : Type*} {l : Filter ι}
    (zSeq tauSeq : ι → ℂ) (z tau : ℝ) (htau : 0 < tau) (hz : -1 < z) (hzUpper : z < tau)
    (hzT : Filter.Tendsto zSeq l (nhds (z : ℂ)))
    (htauT : Filter.Tendsto tauSeq l (nhds (tau : ℂ))) :
    Filter.Tendsto (fun n => sigmaSComplexIntegralBase (zSeq n) (tauSeq n)) l
      (nhds (sigmaSBase z tau)) := by
  have hcont := continuousAt_sigmaSComplexIntegralBase (z := (z : ℂ)) (tau := (tau : ℂ))
    (by simpa using htau) (by simpa using hz) (by simpa using hzUpper)
  have h := hcont.tendsto.comp (hzT.prodMk_nhds htauT)
  rw [← sigmaSComplexIntegralBase_ofReal z tau]
  simpa [Function.comp_def] using h

/-- Approaching parameters eventually satisfy the strict chamber conditions of
[AFK25, equation (8.7), `eq:dsintrep`], when the real pair they approach satisfies them: each of
`Re τ_n > 0`, `Re z_n > -1` and `Re τ_n - Re z_n > 0` is an open condition on a real part, so it
holds eventually. Split off from `tendsto_sfJacobiCocycle_S`, which needs it to rewrite
the product quotient as the integral representation along the approach. -/
private lemma eventually_mem_sigmaSChamber {ι : Type*} {l : Filter ι} {zSeq tauSeq : ι → ℂ}
    {z tau : ℝ} (htau : 0 < tau) (hz : -1 < z) (hzUpper : z < tau)
    (hzT : Filter.Tendsto zSeq l (nhds (z : ℂ)))
    (htauT : Filter.Tendsto tauSeq l (nhds (tau : ℂ))) :
    ∀ᶠ n in l, 0 < (tauSeq n).re ∧ -1 < (zSeq n).re ∧ (zSeq n).re < (tauSeq n).re := by
  have hre : Filter.Tendsto (fun n => (tauSeq n).re) l (nhds tau) := by
    simpa [Function.comp_def] using
      (Complex.continuous_re.continuousAt (x := (tau : ℂ))).tendsto.comp htauT
  have hzre : Filter.Tendsto (fun n => (zSeq n).re) l (nhds z) := by
    simpa [Function.comp_def] using
      (Complex.continuous_re.continuousAt (x := (z : ℂ))).tendsto.comp hzT
  filter_upwards [hre.eventually_const_lt htau, hzre.eventually_const_lt hz,
    (hre.sub hzre).eventually_const_lt (by linarith : (0 : ℝ) < tau - z)] with n h1 h2 h3
  exact ⟨h1, h2, by linarith⟩

/-- **The upper-half-plane generator tends to the real generator.** Along parameters
that approach a real pair `(z, τ)` of the chamber from inside `ℍ` and off the period lattice,

```text
sigma_S(z_n, tau_n) → sigmaSBase z tau.
```

This is the one-generator instance of the passage `τ → α` in the proof of [72, Kopp (2024),
Theorem 4.46, `thm:cllr`]. The approaching values are the product quotient `sfJacobiCocycleUHP`;
`him` and `hlat` keep them in `ℍ` and off the period lattice, where it is the source's `σ_S`. -/
theorem tendsto_sfJacobiCocycle_S {ι : Type*} {l : Filter ι}
    (zSeq tauSeq : ι → ℂ) (z tau : ℝ) (htau : 0 < tau) (hz : -1 < z) (hzUpper : z < tau)
    (hzT : Filter.Tendsto zSeq l (nhds (z : ℂ)))
    (htauT : Filter.Tendsto tauSeq l (nhds (tau : ℂ)))
    (him : ∀ᶠ n in l, 0 < (tauSeq n).im)
    (hlat : ∀ᶠ n in l, ¬ IsPeriodLatticePoint (tauSeq n) (zSeq n)) :
    Filter.Tendsto (fun n => sfJacobiCocycleUHP
        (ModularGroup.S : Mat(2, ℤ)) (zSeq n) (tauSeq n)) l
      (nhds (sigmaSBase z tau)) := by
  apply (tendsto_sigmaSComplexIntegralBase zSeq tauSeq z tau htau hz hzUpper hzT htauT).congr'
  filter_upwards [him, hlat,
    eventually_mem_sigmaSChamber htau hz hzUpper hzT htauT] with n hn1 hn2 hn3
  exact (sfJacobiCocycle_S_eq_sigmaSComplexIntegralBase (zSeq n) (tauSeq n) hn1
    hn3.1 hn3.2.1 hn3.2.2 hn2).symm

/-- **The upper-half-plane generator tends to the honest real generator, at an arbitrary real
argument.** Along parameters approaching a real pair `(z, τ)` from inside `ℍ` and off the period
lattice, with `τ > 0` and `z` off the real lattice `ℤτ + ℤ`,

```text
sigma_S(z_n, tau_n) → sigmaSHonest z tau.
```

`tendsto_sfJacobiCocycle_S` needs `z` to lie in the chamber `(-1, τ)` of
[AFK25, equation (8.7), `eq:dsintrep`], because that is where the integral representation it
compares against is valid. That restriction is an artifact of the representation, not of the
source: [AFK25, equation (8.9)] moves an arbitrary real argument into the chamber by the ceiling
shift `SICs.Cocycle.SigmaS.Reduction.sfShift`, at the cost of one finite `q`-Pochhammer factor, and
that factor is continuous and — by `hlatReal` — nonzero at the limit. Dividing the two limits
gives the value `sigmaSHonest` records, with no condition on `z` beyond lattice-freeness.

`hlatReal` excludes this obstruction: on the lattice the finite factor acquires a zero,
the obstruction recorded by `SICs.Analysis.PeriodLattice.SigmaSLatticeFree` for the shift calculus.
`sigmaSLatticeFree_fracSymplecticFormRat_div` supplies it for the
arguments in the word product, from irrationality of the base point and `r ∉ ℤ²`. -/
theorem tendsto_sfJacobiCocycle_S_sigmaSHonest {ι : Type*} {l : Filter ι}
    (zSeq tauSeq : ι → ℂ) (z tau : ℝ) (htau : 0 < tau) (hlatReal : SigmaSLatticeFree tau z)
    (hzT : Filter.Tendsto zSeq l (nhds (z : ℂ)))
    (htauT : Filter.Tendsto tauSeq l (nhds (tau : ℂ)))
    (him : ∀ᶠ n in l, 0 < (tauSeq n).im)
    (hlat : ∀ᶠ n in l, ¬ IsPeriodLatticePoint (tauSeq n) (zSeq n)) :
    Filter.Tendsto (fun n => sfJacobiCocycleUHP
        (ModularGroup.S : Mat(2, ℤ)) (zSeq n) (tauSeq n)) l
      (nhds (sigmaSHonest z tau)) := by
  have htauC : (tau : ℂ) ≠ 0 := by exact_mod_cast htau.ne'
  set m : ℤ := sfShift z with hm
  set w : ℝ := z - (m : ℝ) with hw
  have hwlow : -1 < w := neg_one_lt_sub_sfShift z
  have hwup : w < tau := sub_sfShift_lt z tau htau
  have hlatw : SigmaSLatticeFree tau w := by
    have h := hlatReal.add 0 (-m)
    have he : z + ((0 : ℤ) : ℝ) * tau + ((-m : ℤ) : ℝ) = w := by rw [hw]; push_cast; ring
    rwa [he] at h
  -- The shifted approach, still off the lattice.
  have hwT : Filter.Tendsto (fun n => zSeq n - (m : ℂ)) l (nhds ((w : ℝ) : ℂ)) := by
    rw [hw]
    push_cast
    exact hzT.sub tendsto_const_nhds
  have hlatShift : ∀ᶠ n in l, ¬ IsPeriodLatticePoint (tauSeq n) (zSeq n - (m : ℂ)) := by
    filter_upwards [hlat] with n hn
    rintro ⟨p, q, hpq⟩
    exact hn ⟨p + m, q, by push_cast at hpq ⊢; linear_combination hpq⟩
  have hbase := tendsto_sfJacobiCocycle_S (fun n => zSeq n - (m : ℂ)) tauSeq w tau htau
    hwlow hwup hwT htauT him hlatShift
  -- The single finite factor separating the raw argument from its chamber representative.
  have hF : qPochhammerFin (-m) ((w : ℂ) / (tau : ℂ)) (-1 / (tau : ℂ)) ≠ 0 := by
    rw [show ((w : ℂ) / (tau : ℂ)) = ((w / tau : ℝ) : ℂ) by push_cast; ring,
      show (-1 / (tau : ℂ)) = ((-1 / tau : ℝ) : ℂ) by push_cast; ring]
    refine qPochhammerFin_ne_zero_of_forall_ne_int _ _ _ fun k _ m' hkm => ?_
    refine hlatw m' k ?_
    field_simp at hkm
    linarith
  have hargT : Filter.Tendsto (fun n => (zSeq n - (m : ℂ)) / tauSeq n) l
      (nhds ((w : ℂ) / (tau : ℂ))) := hwT.div htauT htauC
  have hmodT : Filter.Tendsto (fun n => -1 / tauSeq n) l (nhds (-1 / (tau : ℂ))) :=
    tendsto_const_nhds.div htauT htauC
  have hFT : Filter.Tendsto
      (fun n => qPochhammerFin (-m) ((zSeq n - (m : ℂ)) / tauSeq n) (-1 / tauSeq n)) l
      (nhds (qPochhammerFin (-m) ((w : ℂ) / (tau : ℂ)) (-1 / (tau : ℂ)))) := by
    simpa only [Function.comp_def] using
      (continuousAt_qPochhammerFin (-m) hF).tendsto.comp (hargT.prodMk_nhds hmodT)
  -- Divide the two limits; the quotient is `sigmaSHonest`'s own defining formula.
  have hlim := (tendsto_const_nhds (x := (1 : ℂ)) (f := l)).div hFT hF |>.mul hbase
  rw [sigmaSHonest, sigmaS, show qPochhammerFin (0 : ℤ) (w : ℂ) (tau : ℂ) = 1 by
    simp [qPochhammerFin]]
  refine hlim.congr' ?_
  filter_upwards [him, hFT.eventually_ne hF] with n hn hFn
  have hshift := sfJacobiCocycle_S_add_intCast_mul_add_intCast (zSeq n - (m : ℂ))
    (tauSeq n) hn 0 m (by simp [qPochhammerFin]) hFn
  rw [show (zSeq n - (m : ℂ)) + ((0 : ℤ) : ℂ) * tauSeq n + (m : ℂ) = zSeq n by push_cast; ring,
    show qPochhammerFin (0 : ℤ) (zSeq n - (m : ℂ)) (tauSeq n) = 1 by
      simp [qPochhammerFin]] at hshift
  simp only [Pi.div_apply]
  exact hshift.symm

end SIC

end
