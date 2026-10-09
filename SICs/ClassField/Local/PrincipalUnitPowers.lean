/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Local.IntegralQuotients
import SICs.Analysis.UltrametricUnitFiltration
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.GroupTheory.Index

/-!
# Power indices on small principal-unit groups

Some subgroup of finite index in the local integral units has injective nth powering with index
$|n|_v^{-1}$.

This is the local linearization in Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII,
Proposition 6.8. We use Serre, *Local Fields* (1979), Chapter XIV, §4, Proposition 9, proof:
a power map has nonzero linear term and a smaller error on a sufficiently small neighborhood.
Mathlib's inverse function theorem supplies its contraction step through
`SICs.Analysis.UltrametricInverse`.

## The argument

Choose a nonzero $a$ so small that $x \mapsto x^n$ scales distances by $|n|$ on the ball
containing $1+a\mathcal O_v$, and is locally onto. The subgroup
$H=1+a\mathcal O_v$ is open in the compact group $U_v$, hence has finite index.
The power map is injective on $H$, and its image is $1+na\mathcal O_v$.
The coordinate $x \mapsto (x-1)/a$ identifies its cosets with $\mathcal O_v/n\mathcal O_v$:
two units have the same multiplicative coset precisely when their coordinate difference
is divisible by $n$. The latter quotient has cardinality $|n|^{-1}$ by
`card_quotient_span_eq_norm_inv`. The private norm-radius balls adapt to the inverse theorem
without choosing a uniformizer exponent; `higherUnitGroup` remains the public filtration.
-/

noncomputable section

open Filter Metric Set
open NumberField IsDedekindDomain
open scoped Topology SIC.FinitePlace

namespace SIC.FinitePlace

variable {K : Type*} [Field K] [NumberField K]

/-! ### Principal-unit balls and their coordinates

The coordinate of $x$ in $1+a\mathcal O_v$ is $(x-1)/a$.
Positive-radius balls are open and have finite index in the compact integral unit group. -/

/-- The integral units with $|x-1|\le r$, used in `exists_unitSubgroup_powerIndex`. -/
private def unitBall (v : HeightOneSpectrum (𝓞 K)) (r : ℝ) (hr : 0 ≤ r) :
    Subgroup (unitGroup v) where
  carrier := {x | ‖((x : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1‖ ≤ r}
  one_mem' := by simpa using hr
  mul_mem' {x y} hx hy := by
    have hny : ‖((y : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ = 1 :=
      (mem_unitGroup_iff_norm_eq_one v _).mp y.property
    change ‖(x : (v.adicCompletion K)ˣ).val * (y : (v.adicCompletion K)ˣ).val - 1‖ ≤ r
    rw [show (x : (v.adicCompletion K)ˣ).val * (y : (v.adicCompletion K)ˣ).val - 1 =
      ((x : (v.adicCompletion K)ˣ).val - 1) * (y : (v.adicCompletion K)ˣ).val +
        ((y : (v.adicCompletion K)ˣ).val - 1) by ring]
    apply (IsUltrametricDist.norm_add_le_max _ _).trans
    simpa only [norm_mul, hny, mul_one] using max_le hx hy
  inv_mem' {x} hx := by
    have hnx : ‖((x : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ = 1 :=
      (mem_unitGroup_iff_norm_eq_one v _).mp x.property
    change ‖((x.val⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1‖ ≤ r
    rw [Units.val_inv_eq_inv_val]
    rw [show (x.val.val)⁻¹ - 1 = -(x.val.val - 1) / x.val.val by field_simp; ring]
    change ‖x.val.val - 1‖ ≤ r at hx
    simpa only [norm_div, norm_neg, hnx, div_one] using hx

/-- A positive-radius unit ball has finite index in the compact integral unit group. -/
private theorem unitBall_finiteIndex (v : HeightOneSpectrum (𝓞 K)) {r : ℝ} (hr : 0 < r) :
    (unitBall v r hr.le).FiniteIndex := by
  have : CompactSpace (unitGroup v) := isCompact_iff_compactSpace.mp (isCompact_unitGroup v)
  apply Subgroup.finiteIndex_iff_finite_quotient.mpr
  apply Subgroup.quotient_finite_of_isOpen
  change IsOpen ((fun x : unitGroup v => (x.val : v.adicCompletion K)) ⁻¹' closedBall 1 r)
  exact (IsUltrametricDist.isOpen_closedBall _ hr.ne').preimage
    (Units.continuous_val.comp continuous_subtype_val)

/-- Regard a field element sufficiently close to one as an element of `unitBall`. -/
private def unitBallOf (v : HeightOneSpectrum (𝓞 K)) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (x : v.adicCompletion K) (hx : ‖x - 1‖ ≤ r) :
    unitBall v r hr0 := by
  have hn : ‖x‖ = 1 := by
    have h : (1 : v.adicCompletion K) + (x - 1) = x := by ring
    rw [← h]
    exact norm_one_add_of_norm_lt_one (hx.trans_lt hr1)
  let u : (v.adicCompletion K)ˣ := Units.mk0 x (by intro h; simp [h] at hn)
  exact ⟨⟨u, (mem_unitGroup_iff_norm_eq_one v u).mpr hn⟩, hx⟩

/-- The coordinate $x\mapsto(x-1)/a$ identifies $1+a\mathcal O_v$ with $\mathcal O_v$;
used to compare the quotients in `card_unitBall_power`. -/
private def unitBallCoord (v : HeightOneSpectrum (𝓞 K))
    (a : v.adicCompletion K) (ha0 : a ≠ 0) (ha1 : ‖a‖ < 1) :
    unitBall v ‖a‖ (norm_nonneg a) ≃ v.adicCompletionIntegers K := by
  let f : unitBall v ‖a‖ (norm_nonneg a) → v.adicCompletionIntegers K := fun x =>
    ⟨(x.val.val.val - 1) / a, by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      apply Valued.toNormedField.norm_le_one_iff.mp
      rw [norm_div, div_le_one (norm_pos_iff.mpr ha0)]
      exact x.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    have hh := congrArg Subtype.val hxy
    change (x.val.val.val - 1) / a = (y.val.val.val - 1) / a at hh
    exact sub_left_injective ((div_left_inj' ha0).mp hh)
  · intro y
    have hy : ‖(y : v.adicCompletion K)‖ ≤ 1 :=
      Valued.toNormedField.norm_le_one_iff.mpr y.property
    have hsmall : ‖a * y‖ ≤ ‖a‖ := by
      simpa only [norm_mul, mul_one] using mul_le_mul_of_nonneg_left hy (norm_nonneg a)
    refine ⟨unitBallOf v (norm_nonneg a) ha1 (1 + a * y) (by simpa using hsmall), ?_⟩
    apply Subtype.ext
    change (1 + a * y - 1) / a = y
    simp [ha0]

/-! ### Power images and quotient cardinalities

Exact norm scaling identifies the power image with a smaller unit ball.
The coordinate equivalence then identifies the two coset relations. -/

/-- On a sufficiently small unit ball, $H^n=1+na\mathcal O_v$;
Serre, *Local Fields*, Chapter XIV, §4, Proposition 9, proof, via exact local norm scaling. -/
private theorem mem_pow_range_iff (v : HeightOneSpectrum (𝓞 K))
    {n : ℕ} (hn : n ≠ 0) {r : ℝ} (hr1 : r < 1)
    (hnorm : ∀ x ∈ closedBall (1 : v.adicCompletion K) r,
      ∀ y ∈ closedBall (1 : v.adicCompletion K) r,
        ‖x ^ n - y ^ n‖ = ‖(n : v.adicCompletion K)‖ * ‖x - y‖)
    (hbij : BijOn (fun x : v.adicCompletion K => x ^ n) (closedBall 1 r)
      (closedBall 1 (‖(n : v.adicCompletion K)‖ * r)))
    {a : v.adicCompletion K} (ha : ‖a‖ ≤ r)
    (x : unitBall v ‖a‖ (norm_nonneg a)) :
    x ∈ (powMonoidHom (α := unitBall v ‖a‖ (norm_nonneg a)) n).range ↔
      ‖x.val.val.val - 1‖ ≤ ‖(n : v.adicCompletion K)‖ * ‖a‖ := by
  have hnn : 0 < ‖(n : v.adicCompletion K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hn)
  have h1 : (1 : v.adicCompletion K) ∈ closedBall 1 r :=
    mem_closedBall_self ((norm_nonneg a).trans ha)
  constructor
  · rintro ⟨y, rfl⟩
    have hy : y.val.val.val ∈ closedBall 1 r := by
      exact (mem_closedBall_iff_norm).mpr (y.property.trans ha)
    have heq := hnorm y.val.val.val hy 1 h1
    simp only [one_pow] at heq
    change ‖y.val.val.val ^ n - 1‖ ≤ _
    rw [heq]
    exact mul_le_mul_of_nonneg_left y.property hnn.le
  · intro hx
    obtain ⟨y, hy, hyx⟩ := hbij.surjOn ((mem_closedBall_iff_norm).mpr
      (hx.trans (mul_le_mul_of_nonneg_left ha hnn.le)))
    change y ^ n = x.val.val.val at hyx
    have hynorm : ‖y - 1‖ ≤ ‖a‖ := by
      apply (mul_le_mul_iff_right₀ hnn).mp
      have heq := hnorm y hy 1 h1
      rw [one_pow, hyx] at heq
      rw [← heq]
      exact hx
    refine ⟨unitBallOf v (norm_nonneg a) (ha.trans_lt hr1) y hynorm, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    exact hyx

/-- Principal ideal membership in local integers is comparison of norms;
this is Mathlib’s `Valuation.Integers.dvd_iff_le`, used in `card_unitBall_power`. -/
private theorem mem_span_iff_norm (v : HeightOneSpectrum (𝓞 K))
    (a x : v.adicCompletionIntegers K) :
    x ∈ Ideal.span {a} ↔ ‖(x : v.adicCompletion K)‖ ≤ ‖(a : v.adicCompletion K)‖ := by
  rw [Ideal.mem_span_singleton,
    (HeightOneSpectrum.adicCompletionIntegers.integers K v).dvd_iff_le]
  exact Valued.toNormedField.norm_le_iff.symm

/-- The power quotient of a small unit ball has the cardinality of $\mathcal O_v/n\mathcal O_v$.
This is the linearization step in Milne, *Class Field Theory*, Chapter VII, Proposition 6.8. -/
private theorem card_unitBall_power (v : HeightOneSpectrum (𝓞 K))
    {n : ℕ} (hn : n ≠ 0) {r : ℝ} (hr1 : r < 1)
    (hnorm : ∀ x ∈ closedBall (1 : v.adicCompletion K) r,
      ∀ y ∈ closedBall (1 : v.adicCompletion K) r,
        ‖x ^ n - y ^ n‖ = ‖(n : v.adicCompletion K)‖ * ‖x - y‖)
    (hbij : BijOn (fun x : v.adicCompletion K => x ^ n) (closedBall 1 r)
      (closedBall 1 (‖(n : v.adicCompletion K)‖ * r)))
    {a : v.adicCompletion K} (ha0 : a ≠ 0) (ha : ‖a‖ ≤ r) :
    Nat.card (unitBall v ‖a‖ (norm_nonneg a) ⧸ (powMonoidHom n).range) =
      Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {(n : v.adicCompletionIntegers K)}) := by
  let e := unitBallCoord v a ha0 (ha.trans_lt hr1)
  apply Nat.card_congr (Quotient.congr e ?_)
  intro x y
  rw [QuotientGroup.leftRel_apply,
    mem_pow_range_iff v hn hr1 hnorm hbij ha, Submodule.quotientRel_def,
    mem_span_iff_norm]
  have hnx : ‖x.val.val.val‖ = 1 :=
    (mem_unitGroup_iff_norm_eq_one v _).mp x.val.property
  change ‖((x⁻¹ * y).val.val.val) - 1‖ ≤ _ ↔
    ‖(x.val.val.val - 1) / a - (y.val.val.val - 1) / a‖ ≤ ‖(n : v.adicCompletion K)‖
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  rw [show (x.val.val.val)⁻¹ * y.val.val.val - 1 =
    (y.val.val.val - x.val.val.val) / x.val.val.val by field_simp,
    norm_div, hnx, div_one, ← sub_div]
  rw [show x.val.val.val - 1 - (y.val.val.val - 1) = x.val.val.val - y.val.val.val by ring]
  rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr ha0), norm_sub_rev]

/-- Local injectivity of the field power map restricts to the small integral unit group. -/
private theorem unitBall_pow_injective (v : HeightOneSpectrum (𝓞 K))
    {n : ℕ} {r : ℝ}
    (hbij : BijOn (fun x : v.adicCompletion K => x ^ n) (closedBall 1 r)
      (closedBall 1 (‖(n : v.adicCompletion K)‖ * r)))
    {a : v.adicCompletion K} (ha : ‖a‖ ≤ r) :
    Function.Injective (powMonoidHom n : unitBall v ‖a‖ (norm_nonneg a) →*
      unitBall v ‖a‖ (norm_nonneg a)) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  apply hbij.injOn
  · exact mem_closedBall_iff_norm.mpr (x.property.trans ha)
  · exact mem_closedBall_iff_norm.mpr (y.property.trans ha)
  · exact congrArg (fun z : unitBall v ‖a‖ (norm_nonneg a) => z.val.val.val) hxy

/-- The additive quotient count evaluates the power index of the small unit subgroup. -/
private theorem index_unitBall_power (v : HeightOneSpectrum (𝓞 K))
    {n : ℕ} (hn : n ≠ 0) {r : ℝ} (hr1 : r < 1)
    (hnorm : ∀ x ∈ closedBall (1 : v.adicCompletion K) r,
      ∀ y ∈ closedBall (1 : v.adicCompletion K) r,
        ‖x ^ n - y ^ n‖ = ‖(n : v.adicCompletion K)‖ * ‖x - y‖)
    (hbij : BijOn (fun x : v.adicCompletion K => x ^ n) (closedBall 1 r)
      (closedBall 1 (‖(n : v.adicCompletion K)‖ * r)))
    {a : v.adicCompletion K} (ha0 : a ≠ 0) (ha : ‖a‖ ≤ r) :
    ((powMonoidHom (α := unitBall v ‖a‖ (norm_nonneg a)) n).range.index : ℝ) =
      ‖(n : v.adicCompletion K)‖⁻¹ := by
  change (Nat.card (unitBall v ‖a‖ (norm_nonneg a) ⧸ (powMonoidHom n).range) : ℝ) = _
  rw [card_unitBall_power v hn hr1 hnorm hbij ha0 ha]
  exact card_quotient_span_eq_norm_inv v n (Nat.cast_ne_zero.mpr hn)

/-! ### Existence of the required subgroup

The derivative at one is $n$, so the ultrametric inverse theorem supplies a sufficiently
small neighborhood. Choose a nonzero scale inside it and combine the preceding comparisons. -/

/-- Power maps have exact distance scaling on sufficiently small balls about one.
Serre, *Local Fields*, Chapter XIV, §4, Proposition 9, proof, with Mathlib’s contraction
implementation of the inverse function theorem. -/
private theorem exists_small_pow_bijOn {F : Type*} [NontriviallyNormedField F]
    [IsUltrametricDist F] [CompleteSpace F] [CharZero F] {n : ℕ} (hn : n ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      (∀ x ∈ closedBall (1 : F) r, ∀ y ∈ closedBall (1 : F) r,
        ‖x ^ n - y ^ n‖ = ‖(n : F)‖ * ‖x - y‖) ∧
      BijOn (fun x : F => x ^ n) (closedBall 1 r) (closedBall 1 (‖(n : F)‖ * r)) := by
  have hd : HasStrictDerivAt (fun x : F => x ^ n) (n : F) 1 := by
    simpa only [one_pow, mul_one] using hasStrictDerivAt_pow n (1 : F)
  simpa only [one_pow] using SIC.exists_closedBall_bijOn hd (Nat.cast_ne_zero.mpr hn)

/-- There is a finite-index subgroup $H\subseteq U_v$ on which $n$th powering is injective
and has index $|n|_v^{-1}$. Milne, *Class Field Theory*, Chapter VII, Proposition 6.8,
local linearization step; Serre, *Local Fields*, Chapter XIV, §4, Proposition 9, proof. -/
theorem exists_unitSubgroup_powerIndex (v : HeightOneSpectrum (𝓞 K))
    {n : ℕ} (hn : 0 < n) :
    ∃ H : Subgroup (unitGroup v), H.FiniteIndex ∧
      Function.Injective (powMonoidHom n : H →* H) ∧
      ((powMonoidHom n : H →* H).range.index : ℝ) = ‖(n : v.adicCompletion K)‖⁻¹ := by
  obtain ⟨r, hr, hr1, hnorm, hbij⟩ :=
    exists_small_pow_bijOn (F := v.adicCompletion K) hn.ne'
  obtain ⟨a, ha0, har⟩ := NormedField.exists_norm_lt (v.adicCompletion K) hr
  exact ⟨unitBall v ‖a‖ (norm_nonneg a), unitBall_finiteIndex v ha0,
    unitBall_pow_injective v hbij har.le,
    index_unitBall_power v hn.ne' hr1 hnorm hbij (norm_pos_iff.mp ha0) har.le⟩

end SIC.FinitePlace
