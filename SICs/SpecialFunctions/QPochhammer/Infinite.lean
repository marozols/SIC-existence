/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Analysis.PeriodLattice
import SICs.SpecialFunctions.QPochhammer.Finite
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Infinite q-Pochhammer products

Infinite q-Pochhammer products: convergence, entireness, zeros, and the finite-product bridge.

This file follows the infinite symbol of [AFK25, Definition 1.14, `dfn:variantqPochhammer`]
and [72, Kopp (2024), Lemma 2.3, `lem:ell`]. For a fixed upper-half-plane modulus, a geometric
majorant proves locally uniform convergence in the argument. The product is entire and vanishes
exactly where one of its displayed factors does. Splitting the product into a finite prefix
and an infinite tail gives the integer lattice shift law.

The source defines this symbol only for `τ ∈ ℍ`. Analytic statements carry `0 < τ.im`;
outside that domain the definition uses Lean's totalized product. Meromorphic continuation in
the modulus belongs to the Shintani--Faddeev Jacobi cocycle of
[AFK25, Definition 1.16, `df:shinfadjacocycle`], not to this product itself.
-/

noncomputable section

open Complex Real Filter
open scoped Topology

namespace SIC

/-! ### Infinite q-Pochhammer products

At a fixed upper-half-plane modulus, geometric decay gives absolute and locally uniform
convergence, entireness in the argument, and the exact zero set of the symbol in
[AFK25, Definition 1.14, `dfn:variantqPochhammer`]. -/

/-- The infinite variant `q`-Pochhammer symbol
`ϖ(z,τ) = ∏_{j=0}^∞ (1 - e^{2πi(z+jτ)})`, defined by the source for `z ∈ ℂ` and `τ ∈ ℍ`.

See [AFK25, Definition 1.14, `dfn:variantqPochhammer`], equation (1.19), `eq:qpochinf`.  The
`tprod` value at a modulus outside `ℍ` is Lean's totalization, where the source does not speak;
the convergence, analyticity, and zero-set results carry `0 < τ.im`. -/
@[source "AFK25, Definition 1.14, p. 9, dfn:variantqPochhammer (infinite)" (symbol := "ϖ(z,τ)")]
noncomputable def qPochhammer (z τ : ℂ) : ℂ :=
  ∏' j : ℕ, (1 - Complex.exp (2 * π * I * (z + j * τ)))

/-- Integer translation preserves the infinite product in its argument. -/
lemma qPochhammer_add_intCast (z τ : ℂ) (k : ℤ) :
    qPochhammer (z + k) τ = qPochhammer z τ := by
  unfold qPochhammer
  refine tprod_congr fun j => ?_
  congr 1
  exact exp_two_pi_I_eq_of_sub_intCast _ _ k (by ring)

/-- For every `τ`, the factor of index `j` gives `ϖ(k-jτ,τ) = 0`. -/
lemma qPochhammer_intCast_sub_natCast_mul_eq_zero (k : ℤ) (j : ℕ) (τ : ℂ) :
    qPochhammer ((k : ℂ) - (j : ℂ) * τ) τ = 0 := by
  unfold qPochhammer
  apply tprod_of_exists_eq_zero
  refine ⟨j, ?_⟩
  rw [show (2 : ℂ) * π * I * ((k : ℂ) - (j : ℂ) * τ + (j : ℂ) * τ) =
      (k : ℂ) * (2 * π * I) by ring,
    Complex.exp_int_mul_two_pi_mul_I, sub_self]

/-- The first factor of `ϖ(0,τ)` vanishes. -/
lemma qPochhammer_zero (τ : ℂ) : qPochhammer 0 τ = 0 := by
  simpa using qPochhammer_intCast_sub_natCast_mul_eq_zero 0 0 τ

/-- The factorization `e(z + jτ) = e(z)e(τ)^j` used by
`qPochhammer_summable_norm`, `qPochhammer_hasProdLocallyUniformly`, and the
exponential-variable q-binomial identity. -/
lemma qPochhammer_exp_add_nat_mul (z τ : ℂ) (j : ℕ) :
    Complex.exp (2 * π * I * (z + j * τ)) =
      Complex.exp (2 * π * I * z) * Complex.exp (2 * π * I * τ) ^ j := by
  rw [show (2 : ℂ) * π * I * (z + j * τ) =
      2 * π * I * z + j * (2 * π * I * τ) by ring,
    Complex.exp_add, Complex.exp_nat_mul]

/-- For `Im τ > 0`, `‖e(τ)‖ < 1`; this is the common geometric-decay estimate for
`qPochhammer_summable_norm`, `qPochhammer_hasProdLocallyUniformly`, and the
exponential-variable q-binomial identity. -/
lemma qPochhammer_exp_period_norm_lt_one (τ : ℂ) (hτ : 0 < τ.im) :
    ‖Complex.exp (2 * π * I * τ)‖ < 1 := by
  have hre : (2 * (π : ℂ) * I * τ).re = -(2 * π * τ.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [Complex.norm_exp, hre]
  exact Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])

/-- **Shifting the modulus by an integer changes nothing**: the infinite counterpart of
`qPochhammerFin_tau_add_intCast`. Each factor's exponent picks up `j` times an integer, so the
factors are matched termwise and no convergence hypothesis is needed. This is what makes the
upper-half-plane cocycle trivial at a translation `T^k` (`SICs.Cocycle.UpperHalfPlane`). -/
lemma qPochhammer_tau_add_intCast (z τ : ℂ) (k : ℤ) :
    qPochhammer z (τ + k) = qPochhammer z τ := by
  unfold qPochhammer
  refine tprod_congr fun j => ?_
  congr 1
  exact exp_two_pi_I_eq_of_sub_intCast _ _ ((j : ℤ) * k) (by push_cast; ring)

/-- The norms of the exponential corrections in the upper-half-plane `q`-Pochhammer product
are summable. This supplies `qPochhammer_multipliable` and proves nonvanishing
when no individual factor vanishes.

The hypothesis `0 < τ.im` is exactly what makes the norms summable. -/
lemma qPochhammer_summable_norm (z τ : ℂ) (hτ : 0 < τ.im) :
    Summable (fun j : ℕ => ‖Complex.exp (2 * π * I * (z + j * τ))‖) := by
  have hgeom : Summable (fun j : ℕ =>
      ‖Complex.exp (2 * π * I * z)‖ * ‖Complex.exp (2 * π * I * τ)‖ ^ j) :=
    (summable_geometric_of_lt_one (norm_nonneg _)
      (qPochhammer_exp_period_norm_lt_one τ hτ)).mul_left _
  apply hgeom.congr
  intro j
  rw [qPochhammer_exp_add_nat_mul, norm_mul, norm_pow]

/-- The infinite product defining `qPochhammer` is multipliable for `Im τ > 0`,
by the absolute summability of its exponential corrections in `qPochhammer_summable_norm`. -/
lemma qPochhammer_multipliable (z τ : ℂ) (hτ : 0 < τ.im) :
    Multipliable (fun j : ℕ => 1 - Complex.exp (2 * π * I * (z + j * τ))) := by
  have hs := (qPochhammer_summable_norm z τ hτ).of_norm.neg
  simpa only [sub_eq_add_neg] using Complex.multipliable_one_add_of_summable hs

/-- For a fixed upper-half-plane modulus, the defining `q`-Pochhammer products converge locally
uniformly as functions of their first argument.  This is the analytic input behind the
entireness and simple-zero discussion in [95, Shintani (1977), proof of Proposition 5 on
p. 181]. -/
lemma qPochhammer_hasProdLocallyUniformly (τ : ℂ) (hτ : 0 < τ.im) :
    HasProdLocallyUniformly
      (fun j : ℕ => fun z : ℂ => 1 - Complex.exp (2 * π * I * (z + j * τ)))
      (fun z => qPochhammer z τ) := by
  apply hasProdLocallyUniformly_of_forall_compact
  intro K hK
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · subst K
    rw [hasProdUniformlyOn_iff_tendstoUniformlyOn]
    exact tendstoUniformlyOn_empty
  · have hq := qPochhammer_exp_period_norm_lt_one τ hτ
    have hbound : BddAbove
        ((fun z : ℂ => ‖Complex.exp (2 * π * I * z)‖) '' K) :=
      hK.bddAbove_image (by fun_prop)
    obtain ⟨C, hC⟩ := bddAbove_def.mp hbound
    obtain ⟨z₀, hz₀⟩ := hKne
    have hC0 : 0 ≤ C :=
      (norm_nonneg (Complex.exp (2 * π * I * z₀))).trans
        (hC _ (show ‖Complex.exp (2 * π * I * z₀)‖ ∈
          (fun z : ℂ => ‖Complex.exp (2 * π * I * z)‖) '' K from ⟨z₀, hz₀, rfl⟩))
    let u : ℕ → ℝ := fun j => C * ‖Complex.exp (2 * π * I * τ)‖ ^ j
    have hu : Summable u :=
      (summable_geometric_of_lt_one (norm_nonneg _) hq).mul_left C
    have hmajor : ∀ j : ℕ, ∀ z ∈ K,
        ‖-Complex.exp (2 * π * I * (z + j * τ))‖ ≤ u j := by
      intro j z hz
      rw [norm_neg, qPochhammer_exp_add_nat_mul, norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_right
        (hC _ (show ‖Complex.exp (2 * π * I * z)‖ ∈
          (fun w : ℂ => ‖Complex.exp (2 * π * I * w)‖) '' K from ⟨z, hz, rfl⟩))
        (pow_nonneg (norm_nonneg _) _)
    simpa only [qPochhammer, sub_eq_add_neg] using
      hu.hasProdUniformlyOn_nat_one_add hK
      (Filter.Eventually.of_forall hmajor) (fun _ => by fun_prop)

/-- For a fixed upper-half-plane modulus, `qPochhammer` is entire in its first
argument.  This is obtained from the locally uniform product above, not merely from its shift
equations. -/
lemma qPochhammer_differentiable (τ : ℂ) (hτ : 0 < τ.im) :
    Differentiable ℂ (fun z => qPochhammer z τ) := by
  rw [← differentiableOn_univ]
  apply (qPochhammer_hasProdLocallyUniformly τ hτ).tendstoLocallyUniformly_finsetRange
    |>.tendstoLocallyUniformlyOn.differentiableOn
  · exact Filter.Eventually.of_forall fun _ => by
      apply Differentiable.differentiableOn
      fun_prop
  · exact isOpen_univ

/-- For a fixed upper-half-plane modulus, `qPochhammer` is continuous in its first
argument.  This is the continuity consequence of `qPochhammer_differentiable`. -/
lemma qPochhammer_continuous (τ : ℂ) (hτ : 0 < τ.im) :
    Continuous (fun z => qPochhammer z τ) :=
  (qPochhammer_differentiable τ hτ).continuous

/-- In the upper half plane, the infinite `q`-Pochhammer product is nonzero exactly when none of
its individual factors vanishes.  Absolute convergence rules out a product tending to zero in
the absence of a zero factor.

Both directions use `0 < τ.im`, away from which the `tprod` is a Lean totalization. -/
lemma qPochhammer_ne_zero_iff (z τ : ℂ) (hτ : 0 < τ.im) :
    qPochhammer z τ ≠ 0 ↔
      ∀ j : ℕ, 1 - Complex.exp (2 * π * I * (z + j * τ)) ≠ 0 := by
  constructor
  · intro hproduct j hfactor
    apply hproduct
    unfold qPochhammer
    exact tprod_of_exists_eq_zero ⟨j, hfactor⟩
  · intro hfactors
    unfold qPochhammer
    simpa only [sub_eq_add_neg] using
      tprod_one_add_ne_zero_of_summable
        (f := fun j : ℕ => -Complex.exp (2 * π * I * (z + j * τ)))
        (fun j => by simpa only [sub_eq_add_neg] using hfactors j)
        (by simpa only [norm_neg] using qPochhammer_summable_norm z τ hτ)

/-- **Zero set of the upper-half-plane `q`-Pochhammer product.**  Its zeros are precisely

```text
z = k - j tau,    k ∈ ℤ, j ∈ ℕ.
```

This is the divisor-support statement used for Shintani's first and second products in the proof
of [95, Shintani (1977), Proposition 5 on p. 181].  Simplicity of these zeros is established at
the specialized products where it is consumed. -/
lemma qPochhammer_eq_zero_iff (z τ : ℂ) (hτ : 0 < τ.im) :
    qPochhammer z τ = 0 ↔
      ∃ j : ℕ, ∃ k : ℤ, z = k - j * τ := by
  constructor
  · intro hzero
    have hfactor : ¬ ∀ j : ℕ,
        1 - Complex.exp (2 * π * I * (z + j * τ)) ≠ 0 := by
      intro h
      exact (qPochhammer_ne_zero_iff z τ hτ).mpr h hzero
    push Not at hfactor
    obtain ⟨j, hj⟩ := hfactor
    rw [sub_eq_zero] at hj
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hj.symm
    have harg : z + (j : ℂ) * τ = (k : ℂ) := by
      apply mul_right_cancel₀ Complex.two_pi_I_ne_zero
      calc
        (z + (j : ℂ) * τ) * (2 * π * I) = 2 * π * I * (z + j * τ) := by ring
        _ = (k : ℂ) * (2 * π * I) := hk
    exact ⟨j, k, by linear_combination harg⟩
  · rintro ⟨j, k, rfl⟩
    exact qPochhammer_intCast_sub_natCast_mul_eq_zero k j τ

/-- Every zero of `ϖ(z+nτ,τ)` lies in `ℤ + ℤτ`. -/
theorem isPeriodLatticePoint_of_qPochhammer_add_zero (τ : ℂ) (hτ : 0 < τ.im)
    (n : ℤ) {z : ℂ} (hz : qPochhammer (z + n * τ) τ = 0) :
    IsPeriodLatticePoint τ z := by
  obtain ⟨j, k, hrow⟩ := (qPochhammer_eq_zero_iff _ τ hτ).mp hz
  refine ⟨k, -(n + j), ?_⟩
  push_cast
  linear_combination hrow

/-- For `τ ∈ ℍ`, `ϖ(z,τ) ≠ 0` whenever `z ∉ ℤ + ℤτ`
(`qPochhammer_eq_zero_iff`). -/
theorem qPochhammer_ne_zero_of_not_isPeriodLatticePoint {z τ : ℂ} (hτ : 0 < τ.im)
    (h : ¬ IsPeriodLatticePoint τ z) : qPochhammer z τ ≠ 0 := by
  intro hzero
  exact h (isPeriodLatticePoint_of_qPochhammer_add_zero τ hτ 0
    (by simpa using hzero))

/-- For `τ ∈ ℍ` and real `y ∉ ℤ`, `ϖ(pτ+y,τ) ≠ 0`: a zero would put `y` in `ℤ + ℤτ`, whose
real points are the integers (`isPeriodLatticePoint_ofReal_iff`). -/
theorem qPochhammer_intCast_mul_add_ofReal_ne_zero (τ : ℂ) (hτ : 0 < τ.im) (p : ℤ) (y : ℝ)
    (hy : ∀ n : ℤ, y ≠ n) : qPochhammer ((p : ℂ) * τ + y) τ ≠ 0 := by
  intro hzero
  apply not_isPeriodLatticePoint_ofReal τ hτ.ne' y hy
  exact isPeriodLatticePoint_of_qPochhammer_add_zero τ hτ p
    (by simpa only [add_comm] using hzero)

/-- For `τ ∈ ℍ`, `ϖ(w,τ)` is nonzero in a punctured neighborhood of any `z`. -/
theorem eventually_qPochhammer_ne_zero (τ z : ℂ) (hτ : 0 < τ.im) :
    ∀ᶠ w in 𝓝[≠] z, qPochhammer w τ ≠ 0 :=
  (eventually_not_isPeriodLatticePoint τ hτ.ne' z).mono
    fun _ hw => qPochhammer_ne_zero_of_not_isPeriodLatticePoint hτ hw

/-- The zero set of `ϖ(z+y+nτ,τ)` meets every compact set in finitely many points, by
`finite_periodLattice_inter_compact`. -/
theorem finite_qPochhammer_add_int_mul_zeros_inter_compact (τ y : ℂ)
    (hτ : 0 < τ.im) (n : ℤ) {K : Set ℂ} (hK : IsCompact K) :
    (K ∩ {z | qPochhammer (z + y + n * τ) τ = 0}).Finite := by
  let S := K ∩ {z | qPochhammer (z + y + n * τ) τ = 0}
  have hKy : IsCompact ((fun z : ℂ => z + y) '' K) := hK.image (continuous_add_const y)
  have hfinite : (((fun z : ℂ => z + y) '' K) ∩
      {z | IsPeriodLatticePoint τ z}).Finite := finite_periodLattice_inter_compact τ hτ.ne' hKy
  have hsubset : (fun z : ℂ => z + y) '' S ⊆
      ((fun z : ℂ => z + y) '' K) ∩ {z | IsPeriodLatticePoint τ z} := by
    rintro _ ⟨z, ⟨hzK, hz⟩, rfl⟩
    refine ⟨⟨z, hzK, rfl⟩, ?_⟩
    exact isPeriodLatticePoint_of_qPochhammer_add_zero τ hτ n
      (by simpa [add_assoc] using hz)
  exact Set.Finite.of_finite_image (hfinite.subset hsubset)
    (fun _ _ _ _ h => add_right_cancel h)

/-- For `Im σ > 0` and `a ≠ 0`, `ϖ(w/a+b,σ)` is nonzero in a punctured neighborhood of
every `z`. This is the affine pullback of `eventually_qPochhammer_ne_zero`. -/
theorem eventually_qPochhammer_div_add_ne_zero (a b σ z : ℂ) (ha : a ≠ 0)
    (hσ : 0 < σ.im) :
    ∀ᶠ w in 𝓝[≠] z, qPochhammer (w / a + b) σ ≠ 0 := by
  have ht : Tendsto (fun w : ℂ => w / a + b) (𝓝[≠] z) (𝓝[≠] (z / a + b)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact (((continuous_id.div_const a).add_const b).tendsto z).mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with w hw
      intro h
      exact hw ((div_left_inj' ha).mp (add_right_cancel h))
  exact ht.eventually (eventually_qPochhammer_ne_zero σ (z / a + b) hσ)

/-- Near any point, `ϖ(w+y+nτ,τ)` is nonzero in a punctured neighborhood. This is the
`a = 1` case of `eventually_qPochhammer_div_add_ne_zero`. -/
theorem eventually_qPochhammer_add_int_mul_ne_zero (τ y : ℂ)
    (hτ : 0 < τ.im) (n : ℤ) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, qPochhammer (w + y + n * τ) τ ≠ 0 := by
  simpa only [div_one, add_assoc] using
    (eventually_qPochhammer_div_add_ne_zero 1 (y + n * τ) τ z (by simp) hτ)

/-- The zeros of `ϖ(·,τ)` lie in the closed lower half plane: `ϖ(z,τ) = 0` gives `Im z ≤ 0`, by
`qPochhammer_eq_zero_iff`. -/
lemma im_nonpos_of_qPochhammer_eq_zero {z τ : ℂ} (hτ : 0 < τ.im) (hz : qPochhammer z τ = 0) :
    z.im ≤ 0 := by
  obtain ⟨j, k, rfl⟩ := (qPochhammer_eq_zero_iff z τ hτ).mp hz
  simp only [Complex.sub_im, Complex.intCast_im, Complex.mul_im,
    Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero, zero_sub]
  exact neg_nonpos.mpr (mul_nonneg (Nat.cast_nonneg _) hτ.le)

/-- The modular inversion `τ ↦ -1 / τ` preserves the upper half plane.  This elementary
form is shared by the two `q`-Pochhammer products in Shintani's `S`-generator formula. -/
lemma neg_one_div_im_pos (τ : ℂ) (hτ : 0 < τ.im) : 0 < (-1 / τ : ℂ).im := by
  have hτne : τ ≠ 0 := fun h => by simp [h] at hτ
  have hnormSq : 0 < Complex.normSq τ := Complex.normSq_pos.mpr hτne
  rw [show (-1 / τ : ℂ) = -(τ⁻¹) by ring, Complex.neg_im, Complex.inv_im,
    neg_div, neg_neg]
  exact div_pos hτ hnormSq


/-! ### Relation between the finite and infinite products

Kopp's Lemma 2.3 divides the shifted infinite product by a finite one.  Its right side
`(ϖ_m(z,τ))⁻¹ ϖ(z,τ)` is defined in the source exactly when `ϖ_m(z,τ) ≠ 0`: for `m > 0` that is
the inverse being taken here, and for `m < 0` it is the inverse inside `ϖ_m` itself.  So the
nonvanishing hypothesis below is the domain condition of the source's own expression, not an
added assumption. -/

/-- `qPochhammer` at `τ` splits as its first `k` factors (`qPochhammerFin k`) times the
tail, itself the same infinite product based at the shifted point `z + kτ`. This is the
natural-number case of Kopp's Lemma [72, Kopp (2024), Lemma 2.3, `lem:ell`], and needs no
nonvanishing hypothesis: it is a pure reindexing of the same infinite product. -/
lemma qPochhammerFin_natCast_mul_qPochhammer_add (k : ℕ) (z τ : ℂ)
    (hτ : 0 < τ.im) :
    qPochhammerFin (k : ℤ) z τ * qPochhammer (z + k * τ) τ = qPochhammer z τ := by
  set f : ℕ → ℂ := fun j => 1 - Complex.exp (2 * π * I * (z + j * τ)) with hf
  have hshift : (fun j : ℕ => f (j + k)) =
      fun j : ℕ => 1 - Complex.exp (2 * π * I * (z + k * τ + j * τ)) := by
    funext j
    simp only [hf]
    congr 2
    push_cast
    ring
  have hmul_shift : Multipliable (fun j : ℕ => f (j + k)) := by
    rw [hshift]
    exact qPochhammer_multipliable (z + k * τ) τ hτ
  have hsplit := hmul_shift.prod_mul_tprod_nat_mul'
  rw [show (∏' i, f (i + k)) = qPochhammer (z + k * τ) τ from by rw [hshift]; rfl,
      show (∏' i, f i) = qPochhammer z τ from rfl] at hsplit
  rw [← hsplit, qPochhammerFin_natCast]

/-- A nonzero `ϖ(z,τ)` remains nonzero after any forward natural-number shift by `τ`. -/
theorem qPochhammer_add_natCast_mul_ne_zero (N : ℕ) (z τ : ℂ)
    (hτ : 0 < τ.im) (hz : qPochhammer z τ ≠ 0) :
    qPochhammer (z + (N : ℂ) * τ) τ ≠ 0 := by
  intro hzero
  apply hz
  rw [← qPochhammerFin_natCast_mul_qPochhammer_add N z τ hτ, hzero, mul_zero]

/-- A nonzero `ϖ(z,τ)` remains nonzero after any nonnegative integer shift by `τ`. -/
theorem qPochhammer_add_intCast_mul_ne_zero (N : ℤ) (z τ : ℂ)
    (hN : 0 ≤ N) (hτ : 0 < τ.im) (hz : qPochhammer z τ ≠ 0) :
    qPochhammer (z + (N : ℂ) * τ) τ ≠ 0 := by
  have hcast : (N.toNat : ℂ) = (N : ℂ) := by exact_mod_cast Int.toNat_of_nonneg hN
  simpa only [hcast] using qPochhammer_add_natCast_mul_ne_zero N.toNat z τ hτ hz

/-- **Kopp's Lemma** ([72, Kopp (2024), Lemma 2.3, `lem:ell`]): shifting the infinite
`q`-Pochhammer product's argument by an integer multiple of `τ` (plus any integer) divides out the
corresponding finite product `ϖ_m`. Proved by inspection of the product forms, exactly as [72]
states -- the `m ≥ 0` direction is the reindexing above; the `m < 0` direction is the same fact
applied at the shifted base point, using `qPochhammerFin`'s own case split (`inv_inv` then makes the
two directions match up unconditionally). The nonvanishing hypothesis `hm` says exactly that
`ϖ_m(z,τ)` is defined in the source, as the section comment above explains. -/
@[source "72, Lemma 2.3, p. 13, lem:ell"]
theorem qPochhammer_add_intCast_mul_add_intCast (z τ : ℂ) (hτ : 0 < τ.im) (m n : ℤ)
    (hm : qPochhammerFin m z τ ≠ 0) :
    qPochhammer (z + m * τ + n) τ =
      (qPochhammerFin m z τ)⁻¹ * qPochhammer z τ := by
  rw [show z + (m : ℂ) * τ + (n : ℂ) = (z + (m : ℂ) * τ) + (n : ℂ) from by ring,
    qPochhammer_add_intCast]
  rcases Int.lt_or_le m 0 with hm0 | hm0
  case inr =>
    have hk : (m.toNat : ℂ) = (m : ℂ) := by exact_mod_cast Int.toNat_of_nonneg hm0
    have hcore := qPochhammerFin_natCast_mul_qPochhammer_add m.toNat z τ hτ
    rw [show ((m.toNat : ℤ)) = m from Int.toNat_of_nonneg hm0, hk] at hcore
    rw [← hcore, ← mul_assoc, inv_mul_cancel₀ hm, one_mul]
  · set k := (-m).toNat with hkdef
    have hbase : z + (m : ℂ) * τ + (k : ℂ) * τ = z := by
      have hmk : m + (k : ℤ) = 0 := by rw [hkdef]; omega
      have hmk' : (m : ℂ) + (k : ℂ) = 0 := by exact_mod_cast hmk
      linear_combination τ * hmk'
    have hcore := qPochhammerFin_natCast_mul_qPochhammer_add k (z + (m : ℂ) * τ) τ hτ
    rw [hbase] at hcore
    have hHeq : qPochhammerFin (k : ℤ) (z + (m : ℂ) * τ) τ = (qPochhammerFin m z τ)⁻¹ := by
      rw [qPochhammerFin_natCast]
      unfold qPochhammerFin
      rw [ite_eq_right hm0.ne, ite_eq_right (by omega : ¬ (0 : ℤ) < m), ← hkdef, inv_inv]
      apply Finset.prod_congr rfl
      intro j _
      congr 2
      push_cast
      ring
    rw [← hcore, hHeq]

end SIC
