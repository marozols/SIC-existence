/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.RootsOfUnity.Complex
import SICs.SpecialFunctions.QPochhammer.Infinite

/-!
# The Upper-Half-Plane Shintani--Faddeev Cocycle

The regularized SF Jacobi product quotient on `ℂ × ℍ`, its cocycle relation away from product
zeros, the period-product distribution, and off-lattice transported arguments.

This file defines `sfJacobiCocycleUHP` by regularizing the meromorphic product quotient of
[AFK25, Definition 1.16, `df:shinfadjacocycle`] in the Jacobi variable. It also defines the SF
period product and proves its upper-triangular distribution law. The source domain `D_M` is in
`SICs.Cocycle.Domains`; rational characteristics and their integral indices are in
`SICs.SL2Z.Characteristics`. Finite and infinite products are in
`SICs.SpecialFunctions.QPochhammer.Infinite`, and fractional-linear actions are in
`SICs.SL2Z.FractionalLinear`.

## Upper-half-plane products and real boundary values

[AFK25, Definition 1.18, `def:shin`] defines the cocycle by convergent products on `ℍ` and
meromorphically continues it to `D_M`. Here `sfJacobiCocycleUHP` represents the product quotient
on `ℂ × ℍ`, in meromorphic normal form in `z`. At a common product zero it fills a removable
singularity; at a genuine pole its complex-valued representative takes the value zero. The
pointwise quotient formula requires a nonzero denominator. Continuation in the modulus to all
of `D_M`, as in [72, Kopp (2024), Theorem 4.29, `thm:wannabej`], is not represented by this
upper-half-plane definition.

At a real quadratic modulus the infinite product does not converge. The real generator is
instead defined from the double sine and [AFK25, equations (8.6),
`eq:SFJacobiCocycleTermsDoubleSine`, and (8.9)]. `SICs.Cocycle.SigmaS.Reduction` proves independence
of the reducing shift, `SICs.Cocycle.Word.Basic` multiplies these generators along a
Hirzebruch--Jung word, and `SICs.Cocycle.Modular.Values` supplies the finite correction defining
the real modular cocycle. The word decomposition requires `0 ≤ M 1 0`; the total definition
uses the reciprocal value at `M⁻¹` for the other orientation.

The generator shift identity is proved on `ℍ` by
`sfJacobiCocycle_S_add_intCast_mul_add_intCast`. The comparison with real values follows from
the integral representation and its continuity: `SICs.Cocycle.ModularBoundary` proves that the
period-product quotient tends to the real modular cocycle at an irrational real modulus, for
a nonintegral characteristic and a positive Jacobi denominator
(`tendsto_sfPeriodProduct_div_sfModularCocycleReal`). Positivity of intermediate periods and
avoidance of the period lattices follow from these hypotheses. This boundary comparison
identifies the real values with limits of the convergent products; it does not assert
meromorphic continuation throughout `D_M`.

## References

- [AFK25] Appleby, Flammia, Kopp, arXiv:2501.03970v2, Definitions 1.15--1.18 and 1.29;
  equations (8.5)--(8.6) and (8.9)
- [72] G. S. Kopp, "The Shintani--Faddeev modular cocycle: Stark units from q-Pochhammer
  ratios," arXiv:2411.06763 (2024)
-/

noncomputable section

open Complex Real
open scoped Topology
open scoped MatrixGroups

namespace SIC

/-! ### Upper half-plane

We use Mathlib's `UpperHalfPlane` type and `UpperHalfPlane.upperHalfPlaneSet` rather than
duplicating the set `ℍ = {z ∈ ℂ | Im(z) > 0}` from the paragraph preceding [AFK25, Definition 1.14,
`dfn:variantqPochhammer`]. The domain `D_M` of [AFK25, Definition 1.15, `def:sl2ldmndf`], to
which the source continues the cocycle, is `SICs.Cocycle.Domains.sfDomain`.
-/

/-! ### Approaching the real boundary

The vertical sequence `τ + i/(k+1)` approaches a real modulus from inside `ℍ`.
Continuity of the Möbius action and the characteristic pairing is supplied by
`SICs.SL2Z.FractionalLinear` and `SICs.SL2Z.Characteristics`; these transport the
approach through the factors of the cocycle. -/

/-- **The vertical approach** `τ_k = τ + i/(k+1)` to a real point from inside `ℍ`, the approach
along which the boundary values of `SICs.Cocycle.Conjugation` are taken. -/
theorem tendsto_ofReal_add_I_div (τ : ℝ) :
    Filter.Tendsto (fun k : ℕ => (τ : ℂ) + I * (1 / ((k : ℂ) + 1))) Filter.atTop
      (nhds (τ : ℂ)) := by
  convert tendsto_const_nhds.add
    (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ))) using 1
  all_goals simp

/-- The vertical approach lies in `ℍ`. -/
theorem im_ofReal_add_I_div_pos (τ : ℝ) (k : ℕ) : 0 < ((τ : ℂ) + I * (1 / ((k : ℂ) + 1))).im := by
  norm_num [Complex.div_im, Complex.normSq]
  positivity

/-! ### Shintani--Faddeev Jacobi cocycle

On the upper half-plane, the Jacobi cocycle is the quotient of two infinite `q`-Pochhammer products
from [AFK25, Definition 1.16, `df:shinfadjacocycle`]. The source defines `σ_M` by this quotient
on `ℂ × ℍ` and continues it to `ℂ × D_M`. Here its meromorphic normal form in `z` fills
removable singularities; continuation in the modulus beyond `ℍ` is not represented. -/

/-- **The Shintani--Faddeev (SF) Jacobi cocycle on `ℂ × ℍ`**, for `M ∈ SL₂(ℤ)`: the quotient of
two infinite `q`-Pochhammer products

```text
σ_M(z,τ) = ϖ(z/j_M(τ), M·τ) / ϖ(z,τ),
```

[AFK25, Definition 1.16, `df:shinfadjacocycle`], equation (1.21). The source defines `σ_M` by this
formula on `ℂ × ℍ` and then continues it meromorphically to `ℂ × D_M`; this declaration is the
restriction to `ℂ × ℍ`, where the products converge (`UHP` abbreviates the upper half plane `ℍ`).
Meromorphic normal form fills removable common zeros and assigns zero at genuine poles, the
usual complex-valued totalization. Away from denominator zeros,
`sfJacobiCocycleUHP_eq_quotient` recovers the raw quotient. At a modulus outside `ℍ` the value
has no source meaning; in particular it is not the continued cocycle's real quadratic special
value. The real values are defined separately in `SICs.Cocycle.Modular.Values` and compared
with upper-half-plane limits in `SICs.Cocycle.ModularBoundary`. -/
@[source "AFK25, Definition 1.16, p. 10, df:shinfadjacocycle" (symbol := "σ_M(z,τ)")]
noncomputable def sfJacobiCocycleUHP (M : Mat(2, ℤ)) (z τ : ℂ) : ℂ := by
  classical
  let f := fun w => qPochhammer (w / fltDenominator M τ) (flt M τ) / qPochhammer w τ
  exact if qPochhammer z τ ≠ 0 then f z else toMeromorphicNFAt f z z

/-- Away from a zero of the denominator, `σ_M` is its defining product quotient. -/
lemma sfJacobiCocycleUHP_eq_quotient (M : Mat(2, ℤ)) (z τ : ℂ)
    (hden : qPochhammer z τ ≠ 0) :
    sfJacobiCocycleUHP M z τ =
      qPochhammer (z / fltDenominator M τ) (flt M τ) / qPochhammer z τ := by
  simp [sfJacobiCocycleUHP, hden]

/-- The product quotient is meromorphic in `z` on `ℍ`; used to identify its regularization. -/
private lemma meromorphicAt_sfJacobiQuotient (M : SL(2, ℤ)) (τ : ℂ) (hτ : 0 < τ.im)
    (z : ℂ) : MeromorphicAt (fun w =>
      qPochhammer (w / fltDenominator (M : Mat(2, ℤ)) τ)
        (flt (M : Mat(2, ℤ)) τ) / qPochhammer w τ) z := by
  have hnum := (qPochhammer_differentiable _ (flt_im_pos M hτ)).comp
    (show Differentiable ℂ (fun w => w / fltDenominator M τ) by fun_prop)
  exact (hnum.analyticAt z).meromorphicAt.div
    ((qPochhammer_differentiable τ hτ).analyticAt z).meromorphicAt

/-- On `ℍ`, the cocycle is the value of the product quotient in meromorphic normal form:
removable singularities are filled in, and poles have the conventional totalized value zero. -/
lemma sfJacobiCocycleUHP_eq_toMeromorphicNFAt (M : SL(2, ℤ)) (z τ : ℂ) (hτ : 0 < τ.im) :
    sfJacobiCocycleUHP M z τ = toMeromorphicNFAt (fun w =>
      qPochhammer (w / fltDenominator M τ) (flt M τ) / qPochhammer w τ) z z := by
  classical
  by_cases hden : qPochhammer z τ ≠ 0
  · rw [sfJacobiCocycleUHP_eq_quotient _ _ _ hden]
    have hnum := (qPochhammer_differentiable _ (flt_im_pos M hτ)).comp
      (show Differentiable ℂ (fun w => w / fltDenominator M τ) by fun_prop)
    exact (congrFun (toMeromorphicNFAt_eq_self.mpr
      (((hnum.analyticAt z).div ((qPochhammer_differentiable τ hτ).analyticAt z)
        hden).meromorphicNFAt)) z).symm
  · simp [sfJacobiCocycleUHP, hden]

/-- When the numerator is nonzero, the raw quotient already has meromorphic normal form,
including its totalized zero value at a pole. -/
lemma sfJacobiCocycleUHP_eq_quotient_of_num_ne_zero (M : SL(2, ℤ)) (z τ : ℂ)
    (hτ : 0 < τ.im)
    (hnum : qPochhammer (z / fltDenominator M τ) (flt M τ) ≠ 0) :
    sfJacobiCocycleUHP M z τ =
      qPochhammer (z / fltDenominator M τ) (flt M τ) / qPochhammer z τ := by
  rw [sfJacobiCocycleUHP_eq_toMeromorphicNFAt M z τ hτ]
  have hn := (qPochhammer_differentiable _ (flt_im_pos M hτ)).comp
    (show Differentiable ℂ (fun w => w / fltDenominator M τ) by fun_prop)
  exact congrFun (toMeromorphicNFAt_eq_self.mpr (MeromorphicNFOn.div
    (hn.analyticAt z) ((qPochhammer_differentiable τ hτ).analyticAt z).meromorphicNFAt
    (Or.inr hnum))) z

/-- For a fixed modulus in `ℍ`, the regularized cocycle is meromorphic in normal form in `z`. -/
lemma sfJacobiCocycleUHP_meromorphicNFAt (M : SL(2, ℤ)) (τ : ℂ) (hτ : 0 < τ.im) (z : ℂ) :
    MeromorphicNFAt (fun w => sfJacobiCocycleUHP M w τ) z := by
  let f := fun w => qPochhammer (w / fltDenominator M τ) (flt M τ) / qPochhammer w τ
  have hf : MeromorphicOn f Set.univ := fun w _ => meromorphicAt_sfJacobiQuotient M τ hτ w
  have heq : (fun w => sfJacobiCocycleUHP M w τ) = toMeromorphicNFOn f Set.univ := by
    funext w
    rw [sfJacobiCocycleUHP_eq_toMeromorphicNFAt M w τ hτ,
      toMeromorphicNFOn_eq_toMeromorphicNFAt hf (Set.mem_univ w)]
  rw [heq]
  exact meromorphicNFOn_toMeromorphicNFOn f Set.univ (Set.mem_univ z)

/-! ### The inverse-cocycle relation

A special case of the general cocycle identity [AFK25, equation (1.22), `eq:sfjcocyclerelInt`]
(`M₁ = M⁻¹`, `M₂ = M`), whose pointwise form on `ℍ` is the next section: the SF Jacobi cocycle
at `M⁻¹`, evaluated where `M` sends `(z,τ)`, is the reciprocal of the cocycle at `M` itself.
Unlike Kopp's
Lemma (`qPochhammer_add_intCast_mul_add_intCast`,
[72, Kopp (2024), Lemma 2.3, `lem:ell`]), this needs no word decomposition of `M` or `M⁻¹` at
all -- it is a direct consequence of the automorphy-factor identity for `M⁻¹` composed with `M`,
for *any* `M ∈ SL₂(ℤ)`. -/

/-- **Inverse-cocycle relation for the SF Jacobi cocycle**, the case `M₁ = M⁻¹`, `M₂ = M` of
[AFK25, equation (1.22), `eq:sfjcocyclerelInt`]. No word decomposition of `M` is needed: this is a
direct algebraic consequence of `fltDenominator_inv_flt`/`flt_inv_flt`, which make the two
`qPochhammer` factors cancel exactly, so no domain hypothesis is needed either; on `ℍ` it is the
source's relation. The two product nonvanishing hypotheses are needed to cancel the
`qPochhammer` factors, which can vanish. -/
theorem sfJacobiCocycle_inv_mul_self (M : SL(2, ℤ)) (z τ : ℂ)
    (hτ : fltDenominator (M : Mat(2, ℤ)) τ ≠ 0)
    (hA : qPochhammer (z / fltDenominator (M : Mat(2, ℤ)) τ)
        (flt (M : Mat(2, ℤ)) τ) ≠ 0)
    (hB : qPochhammer z τ ≠ 0) :
    sfJacobiCocycleUHP ((M⁻¹ : SL(2, ℤ)) :
          Mat(2, ℤ))
        (z / fltDenominator (M : Mat(2, ℤ)) τ)
        (flt (M : Mat(2, ℤ)) τ) *
      sfJacobiCocycleUHP (M : Mat(2, ℤ)) z τ = 1 := by
  have hflt := flt_inv_flt M τ hτ
  have hfltd := fltDenominator_inv_flt M τ hτ
  rw [sfJacobiCocycleUHP_eq_quotient _ _ _ hA,
    sfJacobiCocycleUHP_eq_quotient _ _ _ hB]
  rw [hflt, show z / fltDenominator (M : Mat(2, ℤ)) τ /
      fltDenominator ((M⁻¹ : SL(2, ℤ)) : Mat(2, ℤ))
        (flt (M : Mat(2, ℤ)) τ) = z from by
    rw [div_div, mul_comm, hfltd, div_one]]
  field_simp

/-! ### The cocycle relation on `ℍ`

[AFK25, equation (1.22), `eq:sfjcocyclerelInt`] is the cocycle relation

$$\sigma_{MM'}(z,\tau) = \sigma_M\!\left(\frac{z}{j_{M'}(\tau)},\, M'\cdot\tau\right)
  \sigma_{M'}(z,\tau),$$

asserted by the source "for all values of `z, τ` such that both sides of the equation are
defined". The pointwise theorem here works where the composite numerator and the intermediate
product are both nonzero, which excludes cancellation of a zero with a pole. It is an algebraic
identity on this regular quotient locus; it does not assert the full identity between meromorphic
germs. Writing `ϖ` for
`qPochhammer`, the right-hand side is

$$\frac{\varpi\!\left(\frac{z}{j_M(M'\cdot\tau) j_{M'}(\tau)},\, M\cdot(M'\cdot\tau)\right)}
        {\varpi\!\left(\frac{z}{j_{M'}(\tau)},\, M'\cdot\tau\right)}
  \cdot
  \frac{\varpi\!\left(\frac{z}{j_{M'}(\tau)},\, M'\cdot\tau\right)}{\varpi(z,\tau)},$$

whose middle products cancel when that common product `ϖ(z/j_{M'}(τ), M'·τ)` is nonzero;
the Jacobi-denominator cocycle law `fltDenominator_mul` and the Möbius composition law `flt_mul`
then turn what is left into `σ_{MM'}(z,τ)`. Both laws apply because `M'` and `M` have determinant
one and `τ`, hence `M'·τ`, lies in `ℍ` (`fltDenominator_ne_zero_of_im_ne_zero`, `flt_im_pos`), so
no separate hypothesis on the intermediate Jacobi denominators is needed.

Two consequences specialize it to the Hirzebruch--Jung word `M = T^{r} S M'` of
[AFK25, Theorem C.4, `thm:tsaltexpn`]: the cocycle is trivial at a translation, and a left
translation factor may therefore be dropped. Together they are the upper-half-plane mirror of
`SICs.Cocycle.Word.Basic`'s real recursion `wordSigmaS`.
-/

/-- The pointwise cocycle relation of the section comment, where the composite numerator and the
intermediate product are nonzero: this excludes cancellation of a zero with a pole, and covers
the pole case needed by the word recursion. -/
theorem sfJacobiCocycle_mul_of_num_ne_zero (M M' : SL(2, ℤ)) (z τ : ℂ)
    (hτ : 0 < τ.im)
    (hnum : qPochhammer (z / fltDenominator (M * M' : SL(2, ℤ)) τ)
      (flt (M * M' : SL(2, ℤ)) τ) ≠ 0)
    (hmid : qPochhammer (z / fltDenominator M' τ) (flt M' τ) ≠ 0) :
    sfJacobiCocycleUHP (M * M' : SL(2, ℤ)) z τ =
      sfJacobiCocycleUHP M (z / fltDenominator M' τ) (flt M' τ) *
        sfJacobiCocycleUHP M' z τ := by
  have hden := fltDenominator_ne_zero_of_im_ne_zero M' hτ.ne'
  rw [sfJacobiCocycleUHP_eq_quotient_of_num_ne_zero _ _ _ hτ hnum,
    sfJacobiCocycleUHP_eq_quotient _ _ _ hmid,
    sfJacobiCocycleUHP_eq_quotient_of_num_ne_zero _ _ _ hτ hmid]
  simp only [Matrix.SpecialLinearGroup.coe_mul, fltDenominator_mul _ _ _ hden,
    flt_mul _ _ _ hden, div_div]
  field_simp

/-- **The cocycle is trivial at a translation.** For `M = T^k` the two period products coincide:
`j_{T^k}(τ) = 1` and `T^k·τ = τ + k`, and `ϖ` is invariant under an integer shift of its modulus
(`qPochhammer_tau_add_intCast`). The hypothesis is nonvanishing of that common product; the
identity is formal in the products, so it needs no domain hypothesis. -/
theorem sfJacobiCocycle_T_zpow (k : ℤ) (z τ : ℂ) (hz : qPochhammer z τ ≠ 0) :
    sfJacobiCocycleUHP ((ModularGroup.T ^ k : SL(2, ℤ)) : Mat(2, ℤ)) z τ
      = 1 := by
  rw [sfJacobiCocycleUHP_eq_quotient _ _ _ hz, fltDenominator_T_zpow, flt_T_zpow, div_one,
    qPochhammer_tau_add_intCast, div_self hz]

/-- **A left translation factor may be dropped**: `σ_{T^k N} = σ_N`. This is the base case
`σ_{T^k} ≡ 1` of the Hirzebruch--Jung recursion. Integer periodicity in the modulus identifies
the numerator functions before regularization. -/
theorem sfJacobiCocycle_T_zpow_mul (k : ℤ) (N : SL(2, ℤ)) (z τ : ℂ) (hτ : 0 < τ.im) :
    sfJacobiCocycleUHP ((ModularGroup.T ^ k * N : SL(2, ℤ)) : Mat(2, ℤ)) z τ =
      sfJacobiCocycleUHP (N : Mat(2, ℤ)) z τ := by
  have hden : fltDenominator (N : Mat(2, ℤ)) τ ≠ 0 :=
    fltDenominator_ne_zero_of_im_ne_zero N hτ.ne'
  simp only [sfJacobiCocycleUHP, Matrix.SpecialLinearGroup.coe_mul,
    fltDenominator_mul _ _ _ hden, fltDenominator_T_zpow, one_mul,
    flt_mul _ _ _ hden, flt_T_zpow, qPochhammer_tau_add_intCast]

/-! ### Rationally indexed period products

Evaluating the q-Pochhammer symbol at `⟨⟨r,τ⟩⟩` gives the period product whose
upper-triangular distribution is [72, Kopp (2024), Proposition 4.45, `prop:utrel`]. -/

/-- The period product `ϖ_r(τ) = ∏_{k=0}^∞ (1 - e((k+r₁)τ - r₀))` indexed by `r ∈ ℚ²`
([72, Kopp (2024), Definition 2.2], distinct from [AFK25]'s unindexed
`ϖ(z,τ)` = `qPochhammer`): the same infinite product as `qPochhammer`, evaluated
at the fractional-symplectic-form argument. [72] indexes by `r ∈ ℝ²`; the rational
characteristics kept here are the ones its Proposition 4.45 and Theorem 4.46 use, and the ones
this project needs. Like `qPochhammer`, and like [72]'s own definition, it carries meaning only
for `τ ∈ ℍ`, which every result below assumes. -/
noncomputable def sfPeriodProduct (r : Fin 2 → ℚ) (τ : ℂ) : ℂ :=
  qPochhammer (fracSymplecticFormRat r τ) τ

/-! ### [72, Kopp (2024), Proposition 4.45, `prop:utrel`]: `ϖ_r` under an upper-triangular action

A finite algebraic identity used by [72, Kopp (2024), Theorem 4.46, `thm:cllr`]'s
conductor-lowering distribution: `ϖ_r((aτ+b)/d)` splits as a `d`-by-`a` finite product of `ϖ_s(τ)`
values. Built in two reindexing stages -- first splitting the defining sum's index `k` as
`k = md + ℓ` (`sfPeriodProduct_eq_prod_finRange`), then expanding each resulting factor
into `a` finer ones via the root-of-unity factorization `one_sub_pow_eq_prod_one_sub_mul`.
The root-of-unity stage uses `tprod_finset_prod_comm` to commute the finite and infinite products.

**Index convention.** [72]'s own derivation applies the root-of-unity split with a `-j` term
([72, Kopp (2024)], the step from equation `(k+r₂)(aτ+b)/d - r₁` to
`(m+(ℓ+r₂)/d)τ + (b(ℓ+r₂)/d - j - r₁)/a`); the identity here instead falls out with `+j`
(`one_sub_pow_eq_prod_one_sub_mul` reindexed at `j` rather than `-j`), giving
`s(j,ℓ)₀ = (d(r₀-j) - b(ℓ+r₁))/(ad)` where [72] has `(d(j+r₁) - b(ℓ+r₁))/(ad)`. The two are the
same finite product: [72]'s index corresponds to `a - j (mod a)` here. Avoiding the relabeling
would cost an extra reindexing lemma for no mathematical gain, so it is left as this documented
difference rather than chased to match the source verbatim. -/

/-- Root-of-unity factorization `1 - wᵃ = ∏_{i<a} (1 - w·ζⁱ)` for `ζ = e^{2πi/a}`: a finite
algebraic identity, needed to expand a single term of `qPochhammer`'s product into `a`
finer-grained terms ([72, Kopp (2024), Proposition 4.45, `prop:utrel`]). Proved via the
primitive-root factorization `Xᵃ - 1 = ∏ᵢ(X - ζⁱ)` (`Polynomial.X_pow_sub_C_eq_prod`), evaluated at
`X = 1/w` and cleared of denominators; `w = 0` is handled separately. -/
private lemma one_sub_pow_eq_prod_one_sub_mul (a : ℕ) (ha : 0 < a) (w : ℂ) :
    1 - w ^ a = ∏ i ∈ Finset.range a, (1 - w * Complex.exp (2 * π * I / a) ^ i) := by
  rcases eq_or_ne w 0 with hw | hw
  · simp [hw, zero_pow ha.ne']
  · set ζ : ℂ := Complex.exp (2 * π * I / a) with hζ_def
    have hζ : IsPrimitiveRoot ζ a := Complex.isPrimitiveRoot_exp a ha.ne'
    have hpoly := X_pow_sub_C_eq_prod (α := (1 : ℂ)) (a := (1 : ℂ)) hζ ha (one_pow a)
    have heval := congrArg (Polynomial.eval (1 / w)) hpoly
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_prod, mul_one] at heval
    have hlhs : w ^ a * ((1 / w) ^ a - 1) = 1 - w ^ a := by
      rw [mul_sub, mul_one, one_div, ← mul_pow, mul_inv_cancel₀ hw, one_pow]
    have hrhs : w ^ a * ∏ i ∈ Finset.range a, (1 / w - ζ ^ i) =
        ∏ i ∈ Finset.range a, (1 - w * ζ ^ i) := by
      rw [show w ^ a = ∏ _i ∈ Finset.range a, w by rw [Finset.prod_const, Finset.card_range],
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      field_simp
    rw [← hlhs, heval, hrhs]

/-- A finite `Fin n`-product commutes with an infinite `ℕ`-product when each
infinite fiber is multipliable. This specialization of Mathlib's
`Multipliable.tprod_finsetProd` is used by `tprod_one_sub_exp_mul_natCast_eq_prod`. -/
private lemma tprod_finset_prod_comm {n : ℕ} (h : Fin n → ℕ → ℂ)
    (hfiber : ∀ i : Fin n, Multipliable (h i)) :
    ∏' m : ℕ, ∏ i : Fin n, h i m = ∏ i : Fin n, ∏' m : ℕ, h i m := by
  exact Multipliable.tprod_finsetProd (s := Finset.univ) (fun i _ => hfiber i)

/-- Expanding one `qPochhammer`-shaped factor `1 - e(a(mτ + C/a))` at modulus `aτ` into `a`
finer factors at modulus `τ`, via `one_sub_pow_eq_prod_one_sub_mul` termwise and
`tprod_finset_prod_comm` to pull the resulting finite `j`-product outside the `m`-tprod. Each
infinite fiber is multipliable by `qPochhammer_multipliable`. -/
private lemma tprod_one_sub_exp_mul_natCast_eq_prod (a : ℕ) (ha : 0 < a) (C τ : ℂ)
    (hτ : 0 < τ.im) :
    ∏' m : ℕ, (1 - Complex.exp (2 * π * I * (C + (a:ℂ) * m * τ))) =
    ∏ j : Fin a, qPochhammer ((C + j) / a) τ := by
  have step1 : ∀ m : ℕ, (1 - Complex.exp (2 * π * I * (C + (a:ℂ) * m * τ))) =
      1 - (Complex.exp (2 * π * I * (C / a + m * τ))) ^ a := by
    intro m
    congr 2
    rw [← Complex.exp_nat_mul]
    congr 1
    have haC : (a:ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    field_simp
  have step2 : ∀ m : ℕ, (1 - (Complex.exp (2 * π * I * (C / a + m * τ))) ^ a) =
      ∏ j : Fin a, (1 - Complex.exp (2 * π * I * ((C + j) / a + m * τ))) := by
    intro m
    rw [one_sub_pow_eq_prod_one_sub_mul a ha]
    rw [← Fin.prod_univ_eq_prod_range (f := fun i => 1 -
      Complex.exp (2 * π * I * (C / a + m * τ)) * Complex.exp (2 * π * I / a) ^ i)]
    apply Finset.prod_congr rfl
    intro j _
    have haC : (a:ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 2
    field_simp
    ring
  simp_rw [step1, step2]
  exact tprod_finset_prod_comm
    (fun j m => 1 - Complex.exp (2 * π * I * ((C + j) / a + (m:ℂ) * τ)))
    (fun j => qPochhammer_multipliable ((C + j) / a) τ hτ)

/-- `sfPeriodProduct` at an arbitrary real-quadratic-shaped argument `τ'`, split by the
residue `ℓ` of the summation index `k` modulo `d`:
`ϖ_r(τ') = ∏_ℓ ∏'_m (1 - e(⟨⟨r,τ'⟩⟩ + (md+ℓ)τ'))`. Pure reindexing (`k = md + ℓ`,
`ℕ ≃ Fin d × ℕ`), needing no algebraic identity on the argument itself -- the specialization to
`τ' = (aτ+b)/d` (`sfPeriodProduct_eq_prod_upperTriangular`) is where the actual content of
[72, Kopp (2024), Proposition 4.45, `prop:utrel`] appears. -/
theorem sfPeriodProduct_eq_prod_finRange (r : Fin 2 → ℚ) (d : ℕ) (hd : 0 < d) (τ' : ℂ)
    (hτ' : 0 < τ'.im) :
    sfPeriodProduct r τ' = ∏ ℓ : Fin d, ∏' m : ℕ,
      (1 - Complex.exp (2 * π * I * (fracSymplecticFormRat r τ' + ((m:ℂ) * d + (ℓ:ℂ)) * τ'))) := by
  have hd' : NeZero d := ⟨hd.ne'⟩
  unfold sfPeriodProduct qPochhammer
  set f : ℕ → ℂ := fun k => 1 - Complex.exp (2 * π * I * (fracSymplecticFormRat r τ' + (k:ℂ) * τ'))
    with hf_def
  set e : ℕ ≃ Fin d × ℕ := (Nat.divModEquiv d).trans (Equiv.prodComm ℕ (Fin d)) with he_def
  have he_symm : ∀ p : Fin d × ℕ, e.symm p = p.2 * d + (p.1 : ℕ) := by
    intro p
    simp [he_def, Nat.divModEquiv, Equiv.prodComm]
  have hmul : Multipliable f := qPochhammer_multipliable _ τ' hτ'
  have hjoint : Multipliable (fun p : Fin d × ℕ => f (e.symm p)) := by
    have hiff := (Equiv.multipliable_iff e.symm (f := f))
    exact hiff.mpr hmul
  have hfiber : ∀ ℓ : Fin d, Multipliable (fun m : ℕ => f (e.symm (ℓ, m))) := by
    intro ℓ
    have heq : (fun m : ℕ => f (e.symm (ℓ, m))) =
      fun m : ℕ => 1 - Complex.exp (2 * π * I *
        ((fracSymplecticFormRat r τ' + (ℓ:ℂ) * τ') + (m:ℂ) * ((d:ℂ) * τ'))) := by
      funext m
      simp only [hf_def, he_symm]
      congr 2
      push_cast
      ring
    rw [heq]
    have hdim : 0 < ((d:ℂ) * τ').im := by
      have h1 : ((d:ℂ) * τ').im = (d:ℝ) * τ'.im := by simp
      rw [h1]
      have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
      positivity
    exact qPochhammer_multipliable _ ((d:ℂ) * τ') hdim
  have hstep : ∏' k : ℕ, f k = ∏ ℓ : Fin d, ∏' m : ℕ, f (e.symm (ℓ, m)) := by
    rw [← Equiv.tprod_eq e.symm f, hjoint.tprod_prod' hfiber, tprod_fintype]
  rw [hstep]
  apply Finset.prod_congr rfl
  intro ℓ _
  apply tprod_congr
  intro m
  show f (e.symm (ℓ, m)) =
    1 - Complex.exp (2 * π * I * (fracSymplecticFormRat r τ' + ((m:ℂ) * d + (ℓ:ℂ)) * τ'))
  rw [hf_def, he_symm]
  push_cast
  ring_nf

/-- One residue class `ℓ` of `sfPeriodProduct_eq_prod_finRange`, specialized to
`τ' = (aτ+b)/d`:
the periodicity of `e` (dropping the integer term `mb`) collapses the `m`-th raw factor to
`1 - e(Cℓ + amτ)` for an `m`-independent `Cℓ`, which `tprod_one_sub_exp_mul_natCast_eq_prod`
expands into the `a` factors `sfPeriodProduct s(j,ℓ) τ` -- see the section docstring for
the `s` formula and its index convention relative to [72]. -/
private lemma tprod_raw_eq_prod_sfPeriodProduct (r : Fin 2 → ℚ) (a d : ℕ) (ha : 0 < a)
    (hd : 0 < d) (b : ℤ) (ℓ : Fin d) (τ : ℂ) (hτ : 0 < τ.im) :
    ∏' m : ℕ, (1 - Complex.exp (2 * π * I *
        (fracSymplecticFormRat r ((a * τ + b) / d) + ((m:ℂ) * d + (ℓ:ℂ)) * ((a * τ + b) / d)))) =
    ∏ j : Fin a, sfPeriodProduct
      (fun i => if i = 0 then ((d:ℚ) * (r 0 - j) - b * (ℓ + r 1)) / (a * d) else (ℓ + r 1) / d) τ
    := by
  have hdne : (d:ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have haC : (a:ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  set Cℓ : ℂ := (a : ℂ) * ((ℓ : ℂ) + (r 1 : ℂ)) / d * τ + (b : ℂ) * ((ℓ : ℂ) + (r 1 : ℂ)) / d
      - (r 0 : ℂ) with hCℓ_def
  have hexpand : ∀ m : ℕ, fracSymplecticFormRat r ((a * τ + b) / d) +
      ((m:ℂ) * d + (ℓ:ℂ)) * ((a * τ + b) / d) = (m:ℂ) * ((a:ℂ) * τ + b) + Cℓ := by
    intro m
    unfold fracSymplecticFormRat
    rw [hCℓ_def]
    field_simp
    ring
  have hkey : ∀ m : ℕ, (1 - Complex.exp (2 * π * I *
      (fracSymplecticFormRat r ((a * τ + b) / d) + ((m:ℂ) * d + (ℓ:ℂ)) * ((a * τ + b) / d)))) =
      1 - Complex.exp (2 * π * I * (Cℓ + (a:ℂ) * m * τ)) := by
    intro m
    rw [hexpand]
    rw [show (2:ℂ) * π * I * ((m:ℂ) * ((a:ℂ) * τ + b) + Cℓ) =
      2 * π * I * (Cℓ + (a:ℂ) * m * τ) + (((m:ℤ) * b : ℤ) : ℂ) * (2 * π * I) by
      push_cast; ring]
    rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  simp_rw [hkey]
  rw [tprod_one_sub_exp_mul_natCast_eq_prod a ha Cℓ τ hτ]
  apply Finset.prod_congr rfl
  intro j _
  unfold sfPeriodProduct
  have hz : (Cℓ + j) / a = fracSymplecticFormRat
      (fun i => if i = 0 then ((d:ℚ) * (r 0 - j) - b * (ℓ + r 1)) / (a * d) else (ℓ + r 1) / d)
      τ := by
    unfold fracSymplecticFormRat
    simp only [ite_eq_right (one_ne_zero (α := Fin 2))]
    rw [hCℓ_def]
    push_cast
    field_simp
    ring
  rw [hz]

/-- **[72, Kopp (2024), Proposition 4.45, `prop:utrel`]**, specialized to the upper-triangular
representative `B = [[a,b],[0,d]]` supplied by [72, Kopp (2024), Lemma 4.44, `lem:Gforbits`]:
`ϖ_r((aτ+b)/d)` is a finite `d`-by-`a` product of `ϖ_s(τ)` values, `s` ranging over
`B⁻¹(j+r₀, ℓ+r₁)` for `j < a`, `ℓ < d`. See the section docstring for the deliberate
`j ↦ a - j (mod a)` relabeling relative to [72]'s own indices. A prerequisite of
[72, Kopp (2024), Theorem 4.46, `thm:cllr`]; the full theorem also needs
[72, Kopp (2024), Theorem 4.37, `thm:shinconj`] and
[72, Kopp (2024), Proposition 4.35, `prop:invariance`]. Their real fixed-point forms are
proved in `SICs.Cocycle.Conjugation` and `SICs.Cocycle.Modular.Shifts`, respectively. -/
@[source "72, Proposition 4.45, p. 50, prop:utrel (upper triangular)"]
theorem sfPeriodProduct_eq_prod_upperTriangular (r : Fin 2 → ℚ) (a d : ℕ) (ha : 0 < a)
    (hd : 0 < d) (b : ℤ) (τ : ℂ) (hτ : 0 < τ.im) :
    sfPeriodProduct r (((a:ℂ) * τ + (b:ℂ)) / (d:ℂ)) =
      ∏ ℓ : Fin d, ∏ j : Fin a, sfPeriodProduct
        (fun i => if i = 0 then ((d:ℚ) * (r 0 - j) - b * (ℓ + r 1)) / (a * d) else (ℓ + r 1) / d)
        τ := by
  have hτ' : 0 < (((a:ℂ) * τ + (b:ℂ)) / (d:ℂ)).im := by
    rw [show ((d:ℂ)) = ((d:ℝ):ℂ) by norm_cast, Complex.div_ofReal_im]
    have h1 : ((a:ℂ) * τ + (b:ℂ)).im = (a:ℝ) * τ.im := by simp
    rw [h1]
    have haR : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
    have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
    positivity
  rw [sfPeriodProduct_eq_prod_finRange r d hd _ hτ']
  apply Finset.prod_congr rfl
  intro ℓ _
  exact tprod_raw_eq_prod_sfPeriodProduct r a d ha hd b ℓ τ hτ

/-!
The real modular values in `SICs.Cocycle.Modular.Values` combine the product along a word with
an exact integer index. The rational-valued `nQP` from `SICs.SL2Z.Characteristics` describes that
index. On `ℍ`, the coboundary identity below relates the period-product quotient to
`sfJacobiCocycleUHP` and its finite correction. `SICs.Cocycle.ModularBoundary` identifies the
limits of these quotients with the real values. -/

/-! ### The coboundary form of the modular cocycle

On `ℍ`, and only there, the Shintani--Faddeev modular cocycle of [AFK25, Definition 1.18,
`def:shin`] is a coboundary in the period product: [AFK25, equation (1.27), `eq:coboundary`],

$$ש^{r}_M(\tau) = \frac{\varpi\big(\langle\langle r, M\cdot\tau\rangle\rangle, M\cdot\tau\big)}
  {\varpi\big(\langle\langle r,\tau\rangle\rangle,\tau\big)}
  = \frac{\varpi_r(M\cdot\tau)}{\varpi_r(\tau)}.$$

This is the form [72, Kopp (2024), Theorem 4.46, `thm:cllr`] works with, while
[AFK25, equation (1.26), `eq:shindf`] defines `ש^r_M` from the Jacobi cocycle `σ_M`; the theorem
below is the source's "straightforward calculation" identifying the two on `ℍ`.

The calculation is the transformation law [AFK25, equation (1.25),
`eq:LActOnSymplecticInnerProduct`] followed by Kopp's Lemma. Membership `M ∈ Γ_r` gives integers
`a, b` with `Mr = r + (a, b)`, and `b = -n_QP(r,M)` by definition of the index. Since
`det M = 1`, the transformation law reads

$$\frac{\langle\langle r,\tau\rangle\rangle}{j_M(\tau)}
  = \langle\langle Mr, M\cdot\tau\rangle\rangle
  = \langle\langle r, M\cdot\tau\rangle\rangle + b\,(M\cdot\tau) - a,$$

so the two arguments of `ϖ` differ by `n_QP(r,M)` periods and an integer, and
`qPochhammer_add_intCast_mul_add_intCast` divides out exactly the finite product
`ϖ_{n_QP(r,M)}` that [AFK25, equation (1.26), `eq:shindf`] puts in the denominator.

The source states the identity for `r ∉ ℤ²`; here the hypothesis it is used for -- that the
finite product in that denominator does not vanish -- is stated directly, since that is what the
calculation needs and what makes both sides defined. -/

/-- **The period-product quotient is the modular cocycle on `ℍ`**, [AFK25, equation (1.27),
`eq:coboundary`], written against the defining equation [AFK25, equation (1.26), `eq:shindf`]:
for `M ∈ Γ_r` and `τ ∈ ℍ`,

$$\frac{\varpi_r(M\cdot\tau)}{\varpi_r(\tau)}
  = \frac{\sigma_M\big(\langle\langle r,\tau\rangle\rangle,\tau\big)}
    {\varpi_{n_{QP}(r,M)}\!\left(\frac{\langle\langle r,\tau\rangle\rangle}{j_M(\tau)},
      M\cdot\tau\right)}.$$

`hfin` is nonvanishing of that finite product, the domain condition of the source's own
expression. The additional `hprod` restricts this pointwise ratio to its nonzero denominator
locus; the source uses a nonintegral characteristic. The right-hand cocycle is regularized, so a
denominator condition is essential for equality to this ratio of product values. -/
theorem sfPeriodProduct_flt_div_sfPeriodProduct {r : Fin 2 → ℚ}
    {M : SL(2, ℤ)} (hM : M ∈ gammaSubgroup r) {τ : ℂ} (hτ : 0 < τ.im)
    (hprod : qPochhammer (fracSymplecticFormRat r τ) τ ≠ 0)
    (hfin : qPochhammerFin (nQPInt r (M : Mat(2, ℤ)))
      (fracSymplecticFormRat r τ / fltDenominator (M : Mat(2, ℤ)) τ)
        (flt (M : Mat(2, ℤ)) τ) ≠ 0) :
    sfPeriodProduct r (flt (M : Mat(2, ℤ)) τ) / sfPeriodProduct r τ =
      sfJacobiCocycleUHP (M : Mat(2, ℤ))
          (fracSymplecticFormRat r τ) τ /
        qPochhammerFin (nQPInt r (M : Mat(2, ℤ)))
          (fracSymplecticFormRat r τ / fltDenominator (M : Mat(2, ℤ)) τ)
          (flt (M : Mat(2, ℤ)) τ) := by
  have hden : fltDenominator (M : Mat(2, ℤ)) τ ≠ 0 :=
    fltDenominator_ne_zero_of_im_ne_zero M hτ.ne'
  have hυ : 0 < (flt (M : Mat(2, ℤ)) τ).im := flt_im_pos M hτ
  obtain ⟨a, ha⟩ := ratVecAction_sub_intVec_of_mem_gammaSubgroup hM 0
  obtain ⟨b, hb⟩ := ratVecAction_sub_intVec_of_mem_gammaSubgroup hM 1
  -- The index is the negative of the second component of `Mr - r`.
  have hn : nQPInt r (M : Mat(2, ℤ)) = -b := by
    have hq : nQP r (M : Mat(2, ℤ)) = ((-b : ℤ) : ℚ) := by
      simp only [nQP, ratVecAction, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Matrix.map_apply] at hb ⊢
      push_cast
      linarith [hb]
    have hcast := nQPInt_cast_of_mem hM
    rw [hq] at hcast
    exact_mod_cast hcast
  -- The two `ϖ` arguments differ by `n_QP(r,M)` periods and an integer.
  have hshift : fracSymplecticFormRat r (flt (M : Mat(2, ℤ)) τ) =
      fracSymplecticFormRat r τ /
          fltDenominator (M : Mat(2, ℤ)) τ +
        (nQPInt r (M : Mat(2, ℤ)) : ℂ) *
          flt (M : Mat(2, ℤ)) τ + (a : ℂ) := by
    have hcov := fracSymplecticFormRat_ratVecAction
      (M : Mat(2, ℤ)) r τ hden
    rw [M.2] at hcov
    have hexp : fracSymplecticFormRat
        (ratVecAction (M : Mat(2, ℤ)) r)
          (flt (M : Mat(2, ℤ)) τ) =
        fracSymplecticFormRat r (flt (M : Mat(2, ℤ)) τ) +
          (b : ℂ) * flt (M : Mat(2, ℤ)) τ - (a : ℂ) := by
      have h0 : (ratVecAction (M : Mat(2, ℤ)) r 0 : ℚ) = r 0 + a := by
        linarith [ha]
      have h1 : (ratVecAction (M : Mat(2, ℤ)) r 1 : ℚ) = r 1 + b := by
        linarith [hb]
      simp only [fracSymplecticFormRat, h0, h1]
      push_cast
      ring
    rw [hexp] at hcov
    rw [hn]
    push_cast
    push_cast at hcov
    linear_combination hcov
  rw [sfPeriodProduct, sfPeriodProduct, hshift,
    qPochhammer_add_intCast_mul_add_intCast _ _ hυ _ a hfin,
    sfJacobiCocycleUHP_eq_quotient _ _ _ hprod]
  ring

/-! ### Nonintegral characteristics avoid the period lattice

The boundary comparison needs each transported argument `⟨⟨r,τ⟩⟩/j_N(τ)` to stay off
the period lattice `ℤ + ℤ(N·τ)` of its own modulus, both because that is where the `q`-Pochhammer
product of [AFK25, equation (1.26), `eq:shindf`] vanishes and because it is where the integral
representation [AFK25, equation (8.7), `eq:dsintrep`] parts company with the product. Off the real
line this costs nothing beyond the source's own blanket hypothesis `r ∉ ℤ²`: clearing the Jacobi
denominator turns lattice membership into a linear relation over `ℤ` whose non-real coefficient
must vanish, and the two resulting integer equations invert to `r ∈ ℤ²`. -/

/-- **A nonintegral characteristic keeps its transported argument off the period lattice.** For
`r ∈ ℚ² ∖ ℤ²`, any integer matrix with `j_M(τ) ≠ 0`, and any non-real `τ`,

$$\frac{\langle\langle r,\tau\rangle\rangle}{j_M(\tau)}
  \notin \mathbb Z + \mathbb Z\,(M\cdot\tau).$$

Writing `M = [[a,b],[c,e]]` and clearing `j_M(τ)`, membership reads
`r₁τ - r₀ = m(cτ + e) + n(aτ + b)`. Since `τ ∉ ℝ` the coefficient of `τ` must vanish on its own,
leaving `r₁ = mc + na` and `r₀ = -(me + nb)`: both coordinates of `r` would be integers.

This is the hypothesis `r ∉ ℤ²` of [AFK25, Lemma 2.14, `lm:shinperiodicity`] and of [AFK25,
equation (1.27), `eq:coboundary`] doing the work that the source's own statements ask of it. No
membership `M ∈ Γ_r` and no determinant condition is needed. -/
theorem not_isPeriodLatticePoint_fracSymplecticFormRat_div {r : Fin 2 → ℚ}
    (hr : ¬ IsIntegralIndex r) (M : Mat(2, ℤ)) {τ : ℂ} (hτ : τ.im ≠ 0)
    (hden : fltDenominator M τ ≠ 0) :
    ¬ IsPeriodLatticePoint (flt M τ) (fracSymplecticFormRat r τ / fltDenominator M τ) := by
  rintro ⟨m, n, h⟩
  rw [div_eq_iff hden] at h
  -- Clear the Jacobi denominator: `⟨⟨r,τ⟩⟩ = m·j_M(τ) + n·(aτ + b)`.
  have hnum : fracSymplecticFormRat r τ =
      (m : ℂ) * fltDenominator M τ + (n : ℂ) * ((M 0 0 : ℂ) * τ + (M 0 1 : ℂ)) := by
    have hden' : ((M 1 0 : ℂ) * τ + (M 1 1 : ℂ)) ≠ 0 := hden
    have hflt : flt M τ * fltDenominator M τ = (M 0 0 : ℂ) * τ + (M 0 1 : ℂ) := by
      rw [flt, fltDenominator, div_mul_cancel₀ _ hden']
    rw [h, add_mul, mul_assoc, hflt]
  -- Split it into the coefficient of `τ` and the constant term.
  set A : ℝ := (r 1 : ℝ) - (m : ℝ) * (M 1 0 : ℝ) - (n : ℝ) * (M 0 0 : ℝ) with hA
  set B : ℝ := (r 0 : ℝ) + (m : ℝ) * (M 1 1 : ℝ) + (n : ℝ) * (M 0 1 : ℝ) with hB
  have hlin : (A : ℂ) * τ = (B : ℂ) := by
    rw [hA, hB, fracSymplecticFormRat, fltDenominator] at *
    push_cast
    linear_combination hnum
  -- A non-real `τ` forces the coefficient to vanish, and then the constant term too.
  have hA0 : A = 0 := by
    have him : A * τ.im = 0 := by
      have h := congrArg Complex.im hlin
      simpa [Complex.mul_im] using h
    exact (mul_eq_zero.mp him).resolve_right hτ
  have hB0 : B = 0 := by
    have := hlin
    rw [hA0] at this
    simpa using this.symm
  -- Both coordinates of `r` are now integers.
  rw [hA] at hA0
  rw [hB] at hB0
  refine hr (isIntegralIndex_of_coords ⟨-(m * M 1 1 + n * M 0 1), ?_⟩
    ⟨m * M 1 0 + n * M 0 0, ?_⟩)
  · have : (r 0 : ℝ) = ((-(m * M 1 1 + n * M 0 1) : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · have : (r 1 : ℝ) = ((m * M 1 0 + n * M 0 0 : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this

/-- **The period product does not vanish on `ℍ` for a nonintegral characteristic**:
`ϖ_r(τ) = ϖ(⟨⟨r,τ⟩⟩, τ)` and `⟨⟨r,τ⟩⟩ ∉ τℤ + ℤ`
(`not_isPeriodLatticePoint_fracSymplecticFormRat_div` at `M = I`, `flt_one`,
`fltDenominator_one`, `qPochhammer_ne_zero_of_not_isPeriodLatticePoint`). -/
theorem sfPeriodProduct_ne_zero {r : Fin 2 → ℚ} (hr : ¬ IsIntegralIndex r) {τ : ℂ}
    (hτ : 0 < τ.im) : sfPeriodProduct r τ ≠ 0 := by
  unfold sfPeriodProduct
  apply qPochhammer_ne_zero_of_not_isPeriodLatticePoint hτ
  have hoff := not_isPeriodLatticePoint_fracSymplecticFormRat_div hr
    (1 : Mat(2, ℤ)) hτ.ne' (by
      rw [fltDenominator_one]
      exact one_ne_zero)
  simpa only [flt_one, fltDenominator_one, div_one] using hoff

/-! ### `σ_S` on `ℍ`: Kopp's Lemma and AFK25 equation (8.9)

The real generator in `SICs.Cocycle.SigmaS.Reduction` is defined using [AFK25, equation (8.9)].
This section proves the same shift identity for the convergent product on `ℍ`. It follows by
applying the finite-shift law to the numerator and denominator of the product quotient.
The nonzero finite factors give an analytic unit, and uniqueness of meromorphic normal form
extends the identity across common product zeros. -/

/-- The uncancelled product quotient obeys the `S` shift rule wherever the two finite
factors are nonzero; used by `sfJacobiCocycle_S_add_intCast_mul_add_intCast`. -/
private lemma sfJacobiQuotient_S_shift (z τ : ℂ) (hτ : 0 < τ.im)
    (m₁ m₂ : ℤ) (hm₁ : qPochhammerFin m₁ z τ ≠ 0)
    (hm₂ : qPochhammerFin (-m₂) (z / τ) (-1 / τ) ≠ 0) :
    qPochhammer ((z + m₁ * τ + m₂) / τ) (-1 / τ) /
        qPochhammer (z + m₁ * τ + m₂) τ =
      qPochhammerFin m₁ z τ / qPochhammerFin (-m₂) (z / τ) (-1 / τ) *
        (qPochhammer (z / τ) (-1 / τ) / qPochhammer z τ) := by
  have hτne : τ ≠ 0 := fun h => by simp [h] at hτ
  have hτ' : 0 < (-1 / τ : ℂ).im := neg_one_div_im_pos τ hτ
  have hden := qPochhammer_add_intCast_mul_add_intCast z τ hτ m₁ m₂ hm₁
  have harg : (z + (m₁ : ℂ) * τ + (m₂ : ℂ)) / τ =
      z / τ + (-m₂ : ℂ) * (-1 / τ) + (m₁ : ℂ) := by
    field_simp
    ring
  rw [harg]
  have hnum :=
    qPochhammer_add_intCast_mul_add_intCast (z / τ) (-1 / τ) hτ' (-m₂) m₁ hm₂
  push_cast at hnum
  rw [hnum, hden]
  field_simp

/-- The `S` shift identity holds near a point away from the product zeros; used to extend
`sfJacobiCocycle_S_add_intCast_mul_add_intCast` to removable zeros by normal-form uniqueness. -/
private lemma sfJacobiCocycle_S_shift_eventually (z τ : ℂ) (hτ : 0 < τ.im)
    (m₁ m₂ : ℤ) (hm₁ : qPochhammerFin m₁ z τ ≠ 0)
    (hm₂ : qPochhammerFin (-m₂) (z / τ) (-1 / τ) ≠ 0) :
    (fun w => sfJacobiCocycleUHP ModularGroup.S (w + m₁ * τ + m₂) τ) =ᶠ[𝓝[≠] z]
      fun w => qPochhammerFin m₁ w τ / qPochhammerFin (-m₂) (w / τ) (-1 / τ) *
        sfJacobiCocycleUHP ModularGroup.S w τ := by
  have h₁ := (analyticAt_qPochhammerFin_of_ne_zero m₁ z τ hm₁).continuousAt
  have h₂ : ContinuousAt (fun w => qPochhammerFin (-m₂) (w / τ) (-1 / τ)) z :=
    ((analyticAt_qPochhammerFin_of_ne_zero (-m₂) (z / τ) (-1 / τ) hm₂).comp
      (f := fun w : ℂ => w / τ)
      (by fun_prop : AnalyticAt ℂ (fun w => w / τ) z)).continuousAt
  filter_upwards [eventually_qPochhammer_ne_zero τ z hτ,
    (h₁.eventually_ne hm₁).filter_mono nhdsWithin_le_nhds,
    (h₂.eventually_ne hm₂).filter_mono nhdsWithin_le_nhds] with w hw hw₁ hw₂
  have hshift : qPochhammer (w + m₁ * τ + m₂) τ ≠ 0 := by
    rw [qPochhammer_add_intCast_mul_add_intCast w τ hτ m₁ m₂ hw₁]
    exact mul_ne_zero (inv_ne_zero hw₁) hw
  rw [sfJacobiCocycleUHP_eq_quotient _ _ _ hshift,
    sfJacobiCocycleUHP_eq_quotient _ _ _ hw]
  simpa [fltDenominator, flt] using
    sfJacobiQuotient_S_shift w τ hτ m₁ m₂ hw₁ hw₂

/-- **The `S`-generator shift rule of [AFK25, equation (8.9)], proved on `ℍ`.**
[72, Kopp (2024), Lemma 2.3, `lem:ell`] applied twice -- once directly to the denominator, once
after substituting `τ' = -1/τ` to the numerator -- gives the Shintani--Faddeev Jacobi cocycle's
shift rule for the generator `S`. This is the same formula that defines
`SICs.Cocycle.SigmaS.Basic.sigmaS` on the real line. The two
nonvanishing hypotheses make the finite multiplier an analytic unit. Normal-form uniqueness
then extends the product identity across common zeros, as required by the meromorphic formula.
The source states the rule for all `τ ∈ D_S`; `0 < τ.im` places it on `ℍ`, the
part of `D_S` where `σ_S` is the product quotient. -/
theorem sfJacobiCocycle_S_add_intCast_mul_add_intCast (z τ : ℂ) (hτ : 0 < τ.im)
    (m₁ m₂ : ℤ) (hm₁ : qPochhammerFin m₁ z τ ≠ 0)
    (hm₂ : qPochhammerFin (-m₂) (z / τ) (-1 / τ) ≠ 0) :
    sfJacobiCocycleUHP (ModularGroup.S : Mat(2, ℤ)) (z + m₁ * τ + m₂) τ =
      qPochhammerFin m₁ z τ / qPochhammerFin (-m₂) (z / τ) (-1 / τ) *
        sfJacobiCocycleUHP (ModularGroup.S : Mat(2, ℤ)) z τ := by
  have hleft : MeromorphicNFAt
      (fun w => sfJacobiCocycleUHP ModularGroup.S (w + m₁ * τ + m₂) τ) z :=
    (sfJacobiCocycleUHP_meromorphicNFAt ModularGroup.S τ hτ
      (z + m₁ * τ + m₂)).comp_analyticAt
        (g := fun w : ℂ => w + m₁ * τ + m₂) (by fun_prop)
  have hnum := analyticAt_qPochhammerFin_of_ne_zero m₁ z τ hm₁
  have hden : AnalyticAt ℂ (fun w => qPochhammerFin (-m₂) (w / τ) (-1 / τ)) z :=
    (analyticAt_qPochhammerFin_of_ne_zero (-m₂) (z / τ) (-1 / τ) hm₂).comp (f := fun w : ℂ => w / τ)
      (by fun_prop : AnalyticAt ℂ (fun w => w / τ) z)
  have hright : MeromorphicNFAt (fun w =>
      qPochhammerFin m₁ w τ / qPochhammerFin (-m₂) (w / τ) (-1 / τ) *
        sfJacobiCocycleUHP ModularGroup.S w τ) z :=
    (meromorphicNFAt_mul_iff_right (hnum.div hden hm₂) (div_ne_zero hm₁ hm₂)).mpr
      (sfJacobiCocycleUHP_meromorphicNFAt ModularGroup.S τ hτ z)
  exact ((hleft.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hright).mp
    (sfJacobiCocycle_S_shift_eventually z τ hτ m₁ m₂ hm₁ hm₂)).eq_of_nhds

end SIC

end
