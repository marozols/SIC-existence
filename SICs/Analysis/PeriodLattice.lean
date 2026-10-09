/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Topology.MetricSpace.HausdorffDistance
import SICs.SL2Z.Characteristics

/-!
# The period lattice `ℤ + ℤτ` and doubly periodic entire functions

The lattice `ℤ+ℤτ`, lattice avoidance at irrational real periods, Liouville for doubly
periodic entire functions, and periodic extension from a strip.

This file supplies the elementary complex analysis behind the Liouville step in the proof of
[95, Shintani (1977), Proposition 5 on p. 181]: "an entire function of `z` with periods
`ω₁` and `ω₂` does not depend upon `z`". Specialized to periods `(1, τ)` with `Im τ ≠ 0`, the
statement is that a differentiable function `ℂ → ℂ` which is `1`-periodic and `τ`-periodic is
constant.

We call `ℤ + ℤτ = {m + nτ : m, n ∈ ℤ}` the *period lattice* of `τ`; the zeros of
Shintani's two products and the inverse double gamma lie in this lattice. The explicit
integer-combination predicate is identified with Mathlib's `PeriodPair.lattice` for `(1, τ)` when
`Im τ ≠ 0`. Mathlib then supplies discreteness and compactness of the range of a continuous
periodic function. For real irrational `τ`, rational coefficients in a lattice equality are unique,
although the subgroup is not discrete. Thus `r₁τ-r₀` avoids the lattice when `r ∉ ℤ²`. So does
its transport by an integral matrix with nonzero Jacobi denominator.

## Mathematical argument

A doubly periodic continuous function takes all of its values on a compact fundamental
parallelogram, so its range is compact and hence bounded. This is Mathlib's
`IsZLattice.isCompact_range_of_periodic`. Liouville's theorem
(`Differentiable.apply_eq_apply_of_bounded`) then shows that a doubly periodic entire function
is constant. Mathlib's `PeriodPair.compl_lattice_sdiff_singleton_mem_nhds` supplies the punctured
neighborhood avoiding the lattice, allowing continuous period laws to extend across its points.
The real projection of the lattice is countable, so some real coordinate misses it. In any fixed
height strip the corresponding vertical segment is compact and disjoint from the closed lattice,
giving a positive distance bound which persists under integer translation.
Horizontal lines halfway between lattice rows stay at least half a period height from the lattice.
For `M∈SL₂(ℤ)` with nonzero Jacobi denominator `j_M(τ)`, division by `j_M(τ)` maps the lattice
of `τ` onto that of `M·τ`. For a nonreal period, the real points of the lattice are exactly the
integers. For real periods,
a vertical line misses the lattice exactly when its real crossing does.
-/

noncomputable section

open Complex Filter Topology Set
open scoped MatrixGroups

namespace SIC

/-! ### Uniqueness of period coefficients -/

/-- Two real combinations of `1` and `τ` agree exactly when their coefficients do. -/
lemma ofReal_add_ofReal_mul_eq_iff (tau : ℂ) (htau : tau.im ≠ 0) (x y x' y' : ℝ) :
    (x : ℂ) + (y : ℂ) * tau = (x' : ℂ) + (y' : ℂ) * tau ↔ x = x' ∧ y = y' := by
  constructor
  · intro h
    have him := congr_arg Complex.im h
    have hy : y = y' := by
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        zero_mul, zero_add] at him
      exact mul_right_cancel₀ htau (by simpa only [add_zero] using him)
    subst y'
    have hre := congr_arg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      zero_mul, sub_zero, add_left_inj] at hre
    exact ⟨hre, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Two lattice points `m + nτ` and `m' + n'τ` agree exactly when `m = m'` and `n = n'`. -/
lemma intCast_add_intCast_mul_eq_iff (tau : ℂ) (htau : tau.im ≠ 0) (m n m' n' : ℤ) :
    (m : ℂ) + (n : ℂ) * tau = (m' : ℂ) + (n' : ℂ) * tau ↔ m = m' ∧ n = n' := by
  simpa only [Complex.ofReal_intCast, Int.cast_inj] using
    ofReal_add_ofReal_mul_eq_iff tau htau (m : ℝ) n m' n'

/-! ### The period lattice -/

/-- `z` is a point of the period lattice `ℤ + ℤτ`: `z = m + nτ` for some integers `m, n`. -/
def IsPeriodLatticePoint (tau z : ℂ) : Prop :=
  ∃ m n : ℤ, z = (m : ℂ) + (n : ℂ) * tau

/-! ### Real lattice exclusion

For nonreal `τ`, taking imaginary parts of a real lattice point forces its `τ`-coefficient to
vanish, so the point is an integer.

The real sigma-S convention writes the same lattice as `aτ+b`. Its exclusion predicate
is kept here with the complex lattice API, so consumers share one geometric hypothesis.
-/

/-- The real points of `ℤ + ℤτ`, for nonreal `τ`, are exactly the integers. -/
theorem isPeriodLatticePoint_ofReal_iff (τ : ℂ) (hτ : τ.im ≠ 0) (y : ℝ) :
    IsPeriodLatticePoint τ (y : ℂ) ↔ ∃ n : ℤ, y = n := by
  constructor
  · rintro ⟨m, n, hmn⟩
    have hcoeff : y = (m : ℝ) ∧ (0 : ℝ) = n :=
      (ofReal_add_ofReal_mul_eq_iff τ hτ y 0 m n).mp (by simpa using hmn)
    exact ⟨m, hcoeff.1⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, 0, by simp⟩

/-- A noninteger real point is outside every nonreal period lattice. -/
theorem not_isPeriodLatticePoint_ofReal (τ : ℂ) (hτ : τ.im ≠ 0)
    (y : ℝ) (hy : ∀ n : ℤ, y ≠ n) :
    ¬ IsPeriodLatticePoint τ (y : ℂ) := by
  intro hyLattice
  obtain ⟨n, hn⟩ := (isPeriodLatticePoint_ofReal_iff τ hτ y).mp hyLattice
  exact hy n hn

/-- A real point avoids the period lattice `ℤτ + ℤ`. The name retains the notation
used by the real sigma-S evaluator; `sigmaSLatticeFree_iff_not_isPeriodLatticePoint`
identifies it with the real restriction of `IsPeriodLatticePoint`. -/
def SigmaSLatticeFree (τ z : ℝ) : Prop := ∀ a b : ℤ, z ≠ a * τ + b

/-- A lattice-free point is in particular not an integer (the `a = 0` instance). -/
lemma SigmaSLatticeFree.ne_intCast {τ z : ℝ} (h : SigmaSLatticeFree τ z) (m : ℤ) : z ≠ m := by
  simpa using h 0 m

/-- A lattice-free point stays lattice-free under negation: the lattice is symmetric. -/
lemma SigmaSLatticeFree.neg {τ z : ℝ} (h : SigmaSLatticeFree τ z) :
    SigmaSLatticeFree τ (-z) := by
  intro a b hz
  refine h (-a) (-b) ?_
  push_cast
  linarith

/-- A lattice-free point stays lattice-free under a shift by any lattice vector. -/
lemma SigmaSLatticeFree.add {τ z : ℝ} (h : SigmaSLatticeFree τ z) (c e : ℤ) :
    SigmaSLatticeFree τ (z + c * τ + e) := by
  intro a b hab
  refine h (a - c) (b - e) ?_
  push_cast
  linarith

/-- A property that is invariant under the unit shift at every lattice-free point holds along
the whole integer orbit `w + ℤ` of a lattice-free point `w`. This transports unit-shift
identities of the sigma-S evaluator along `sfShift`; used by `faddeevS_eq_inv_sigmaSHonest` and
`sigmaSHonest_mul_neg_closed`. -/
lemma SigmaSLatticeFree.add_intCast_of_add_one_iff {τ : ℝ} {P : ℝ → Prop}
    (hP : ∀ w : ℝ, SigmaSLatticeFree τ w → (P w ↔ P (w + 1)))
    {w : ℝ} (hw : SigmaSLatticeFree τ w) (h : P w) (n : ℤ) : P (w + n) := by
  induction n using Int.induction_on with
  | zero => simpa using h
  | succ k ih =>
      have hk : SigmaSLatticeFree τ (w + (k : ℝ)) := by
        simpa using hw.add 0 k
      have hstep := (hP _ hk).mp ih
      convert hstep using 1; push_cast; ring
  | pred k ih =>
      have hk : SigmaSLatticeFree τ (w + ((-k - 1 : ℤ) : ℝ)) := by
        simpa using hw.add 0 (-k - 1)
      apply (hP _ hk).mpr
      convert ih using 1; push_cast; ring

/-- The real sigma-S exclusion of `ℤτ+ℤ` is the real restriction of the complex
period-lattice predicate; the two conventions exchange the integer coordinates. -/
lemma sigmaSLatticeFree_iff_not_isPeriodLatticePoint (τ z : ℝ) :
    SigmaSLatticeFree τ z ↔ ¬ IsPeriodLatticePoint (τ : ℂ) (z : ℂ) := by
  constructor
  · intro h ⟨m, n, hmn⟩
    apply h n m
    have hre : z = (m : ℝ) + (n : ℝ) * τ := by
      simpa using congrArg Complex.re hmn
    simpa only [add_comm, mul_comm] using hre
  · intro h a b hab
    apply h
    refine ⟨b, a, ?_⟩
    have hcast := congrArg (fun x : ℝ => (x : ℂ)) hab
    simpa only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_intCast,
      add_comm] using hcast

/-- A nonreal point is outside the lattice of a real period. Integer combinations of
real periods have zero imaginary part. -/
lemma not_isPeriodLatticePoint_of_im_ne_zero (z : ℂ) (τ : ℝ)
    (hz : z.im ≠ 0) : ¬ IsPeriodLatticePoint τ z := by
  rintro ⟨m, n, hmn⟩
  apply hz
  rw [hmn]
  simp

/-- If a real crossing `x` is outside `ℤ+ℤτ`, the entire vertical line `x+it` is
outside that lattice for real `τ`. This supplies regular contours at real periods. -/
lemma not_isPeriodLatticePoint_vertical (τ x t : ℝ)
    (hx : ¬ IsPeriodLatticePoint τ (x : ℂ)) :
    ¬ IsPeriodLatticePoint τ ((x : ℂ) + t * Complex.I) := by
  rintro ⟨m, n, hmn⟩
  apply hx
  refine ⟨m, n, ?_⟩
  apply Complex.ext
  · simpa using congrArg Complex.re hmn
  · simp

/-- A real crossing is regular for a real period `τ` and shift `y` when both the crossing
and its translate by `y` avoid the period lattice `ℤ + ℤτ`. -/
structure IsRegularPeriodLatticeCrossing (τ y x : ℝ) : Prop where
  /-- The crossing itself avoids the period lattice. -/
  base : ¬ IsPeriodLatticePoint τ (x : ℂ)
  /-- The crossing translated by `y` avoids the period lattice. -/
  shifted : ¬ IsPeriodLatticePoint τ ((x : ℂ) + y)

/-- The negation of lattice membership in the pointwise form used by the double-sine
nonvanishing results. -/
lemma not_isPeriodLatticePoint_iff (tau z : ℂ) :
    ¬ IsPeriodLatticePoint tau z ↔ ∀ m n : ℤ, z ≠ (m : ℂ) + (n : ℂ) * tau := by
  simp [IsPeriodLatticePoint]

/-- Lattice membership is invariant under every integer period translation. -/
lemma isPeriodLatticePoint_add_int_mul_add_int_iff (τ z : ℂ) (m n : ℤ) :
    IsPeriodLatticePoint τ (z + (m : ℂ) * τ + n) ↔ IsPeriodLatticePoint τ z := by
  constructor
  · rintro ⟨a, b, h⟩
    refine ⟨a - n, b - m, ?_⟩
    rw [Int.cast_sub, Int.cast_sub]
    linear_combination h
  · rintro ⟨a, b, h⟩
    refine ⟨a + n, b + m, ?_⟩
    rw [Int.cast_add, Int.cast_add]
    linear_combination h

/-- Lattice membership is invariant under `z ↦ z + mτ - n`. -/
lemma isPeriodLatticePoint_add_int_mul_sub_int_iff (τ z : ℂ) (m n : ℤ) :
    IsPeriodLatticePoint τ (z + m * τ - n) ↔ IsPeriodLatticePoint τ z := by
  simpa only [Int.cast_neg, sub_eq_add_neg] using
    isPeriodLatticePoint_add_int_mul_add_int_iff τ z m (-n)

/-- Regularity at $x$ persists under an integral translation $x+K\tau+L$. -/
theorem IsRegularPeriodLatticeCrossing.add_int_mul_add_int
    (τ y x : ℝ) (K L : ℤ) (h : IsRegularPeriodLatticeCrossing τ y x) :
    IsRegularPeriodLatticeCrossing τ y (x + (K : ℝ) * τ + L) := by
  constructor
  · have ht := (isPeriodLatticePoint_add_int_mul_add_int_iff
      (τ : ℂ) (x : ℂ) K L).not.mpr h.base
    simpa only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_intCast] using ht
  · have ht := (isPeriodLatticePoint_add_int_mul_add_int_iff
      (τ : ℂ) ((x : ℂ) + y) K L).not.mpr h.shifted
    simpa only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_intCast,
      add_assoc, add_comm, add_left_comm] using ht

/-- Lattice membership is invariant under `z ↦ z + 1`. -/
lemma isPeriodLatticePoint_add_one_iff (tau z : ℂ) :
    IsPeriodLatticePoint tau (z + 1) ↔ IsPeriodLatticePoint tau z := by
  simpa using isPeriodLatticePoint_add_int_mul_add_int_iff tau z 0 1

/-- Lattice membership is invariant under `z ↦ z + τ`. -/
lemma isPeriodLatticePoint_add_tau_iff (tau z : ℂ) :
    IsPeriodLatticePoint tau (z + tau) ↔ IsPeriodLatticePoint tau z := by
  simpa using isPeriodLatticePoint_add_int_mul_add_int_iff tau z 1 0

/-- The origin is a lattice point. -/
lemma isPeriodLatticePoint_zero (tau : ℂ) : IsPeriodLatticePoint tau 0 :=
  ⟨0, 0, by simp⟩

/-- The period lattice `ℤ+ℤτ` is countable, as the image of `ℤ×ℤ`. -/
theorem countable_setOf_isPeriodLatticePoint (tau : ℂ) :
    {z | IsPeriodLatticePoint tau z}.Countable := by
  apply (Set.countable_range (fun mn : ℤ × ℤ => (mn.1 : ℂ) + mn.2 * tau)).mono
  rintro z ⟨m, n, rfl⟩
  exact ⟨(m, n), rfl⟩

/-- For `M∈SL₂(ℤ)` with `j_M(τ)≠0`, a point `z` lies in `ℤ+ℤτ` exactly when `z/j_M(τ)` lies in
`ℤ+ℤ(M·τ)`; this is `j_M(τ)(ℤ+ℤ(M·τ))=ℤ+ℤτ`, from
`intCast_add_intCast_mul_div_fltDenominator` and
`fltDenominator_mul_intCast_add_intCast_mul`. -/
theorem isPeriodLatticePoint_div_fltDenominator_iff (M : SL(2, ℤ)) {τ : ℂ}
    (hτ : fltDenominator (M : Mat(2, ℤ)) τ ≠ 0) (z : ℂ) :
    IsPeriodLatticePoint (flt (M : Mat(2, ℤ)) τ)
        (z / fltDenominator (M : Mat(2, ℤ)) τ) ↔ IsPeriodLatticePoint τ z := by
  constructor
  · rintro ⟨m, n, hmn⟩
    refine ⟨m * M 1 1 + n * M 0 1, m * M 1 0 + n * M 0 0, ?_⟩
    have h := fltDenominator_mul_intCast_add_intCast_mul M τ hτ m n
    rw [← hmn, mul_div_cancel₀ z hτ] at h
    exact h
  · rintro ⟨m, n, hmn⟩
    refine ⟨m * M 0 0 - n * M 0 1, n * M 1 1 - m * M 1 0, ?_⟩
    rw [hmn]
    exact intCast_add_intCast_mul_div_fltDenominator M τ hτ m n

/-- Division by a Jacobi denominator followed by an integral period translation
preserves absence from the period lattice. -/
theorem not_isPeriodLatticePoint_div_fltDenominator_add (M : SL(2, ℤ)) {z τ : ℂ}
    (hden : fltDenominator (M : Mat(2, ℤ)) τ ≠ 0)
    (hz : ¬ IsPeriodLatticePoint τ z) (k n : ℤ) :
    ¬ IsPeriodLatticePoint (flt (M : Mat(2, ℤ)) τ)
      (z / fltDenominator (M : Mat(2, ℤ)) τ + k * flt (M : Mat(2, ℤ)) τ - n) := by
  exact (isPeriodLatticePoint_add_int_mul_sub_int_iff _ _ k n).not.mpr
    ((isPeriodLatticePoint_div_fltDenominator_iff M hden z).not.mpr hz)

/-- The independent periods `(1, τ)` packaged for Mathlib's lattice API. -/
def periodPair (tau : ℂ) (htau : tau.im ≠ 0) : PeriodPair where
  ω₁ := 1
  ω₂ := tau
  indep := by
    rw [LinearIndependent.pair_iff]
    intro x y h
    apply (ofReal_add_ofReal_mul_eq_iff tau htau x y 0 0).mp
    simpa [Complex.real_smul] using h

/-- Bridges the explicit integer-combination predicate and Mathlib's period lattice. -/
lemma isPeriodLatticePoint_iff_mem_lattice (tau : ℂ) (htau : tau.im ≠ 0) (z : ℂ) :
    IsPeriodLatticePoint tau z ↔ z ∈ (periodPair tau htau).lattice := by
  simp [IsPeriodLatticePoint, PeriodPair.mem_lattice, periodPair, eq_comm]

/-- Every compact set meets `ℤ + ℤτ` in finitely many points when `Im τ ≠ 0`. -/
theorem finite_periodLattice_inter_compact (tau : ℂ) (htau : tau.im ≠ 0)
    {K : Set ℂ} (hK : IsCompact K) :
    (K ∩ {z | IsPeriodLatticePoint tau z}).Finite := by
  let P := periodPair tau htau
  have hdisc : DiscreteTopology (P.lattice : Set ℂ) := by
    change DiscreteTopology P.lattice
    infer_instance
  have hdiscrete : IsDiscrete (P.lattice : Set ℂ) := ⟨hdisc⟩
  have hset : {z | IsPeriodLatticePoint tau z} = (P.lattice : Set ℂ) := by
    ext z
    exact isPeriodLatticePoint_iff_mem_lattice tau htau z
  rw [hset]
  exact (hK.inter_right P.isClosed_lattice).finite (hdiscrete.mono inter_subset_right)

/-- **The period lattice is closed and discrete**: every `z ∈ ℂ` has a punctured neighborhood
containing no lattice point. For `z` off the lattice this says the lattice is closed; for `z`
on it, that `z` is isolated. -/
lemma eventually_not_isPeriodLatticePoint (tau : ℂ) (htau : tau.im ≠ 0) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, ¬ IsPeriodLatticePoint tau w := by
  have h := (periodPair tau htau).compl_lattice_sdiff_singleton_mem_nhds z
  filter_upwards [mem_nhdsWithin_of_mem_nhds h, self_mem_nhdsWithin] with w hw hwz
  rw [isPeriodLatticePoint_iff_mem_lattice tau htau]
  exact fun hmem => hw ⟨hmem, hwz⟩

/-! ### Lines separated from the lattice

Half-integer heights give horizontal gaps. A real coordinate outside the countable lattice
projection gives a vertical gap on each compact segment, preserved by integer translation. -/

/-- Every point at height `(r+1/2) Im τ` is at least `Im τ/2` from the period lattice. -/
theorem half_height_le_norm_sub_periodLatticePoint (τ : ℂ) (hτ : 0 < τ.im) (r : ℤ)
    (u : ℂ) (hu : IsPeriodLatticePoint τ u) (s : ℝ) :
    τ.im / 2 ≤ ‖((s : ℂ) + (((r : ℝ) + 1 / 2) * τ.im) * I) - u‖ := by
  obtain ⟨k, j, rfl⟩ := hu
  have hhalf : (1 / 2 : ℝ) ≤ |(r : ℝ) + 1 / 2 - (j : ℝ)| := by
    rcases le_or_gt j r with hj | hj
    · have hj' : (j : ℝ) ≤ r := by exact_mod_cast hj
      rw [abs_of_nonneg (by linarith)]
      linarith
    · have hj' : r + 1 ≤ j := by omega
      have hj'' : (r : ℝ) + 1 ≤ j := by exact_mod_cast hj'
      rw [abs_of_nonpos (by linarith)]
      linarith
  have him : (((s : ℂ) + (((r : ℝ) + 1 / 2) * τ.im) * I) -
      ((k : ℂ) + (j : ℂ) * τ)).im = ((r : ℝ) + 1 / 2 - j) * τ.im := by
    simp [Complex.sub_im, Complex.add_im, Complex.mul_im]
    ring
  calc
    τ.im / 2 ≤ |((r : ℝ) + 1 / 2 - j) * τ.im| := by
      rw [abs_mul, abs_of_pos hτ]
      nlinarith [mul_le_mul_of_nonneg_right hhalf hτ.le]
    _ = |(((s : ℂ) + (((r : ℝ) + 1 / 2) * τ.im) * I) -
        ((k : ℂ) + (j : ℂ) * τ)).im| := by rw [him]
    _ ≤ _ := Complex.abs_im_le_norm _

/-- Some real coordinate is missed by the real projection of `ℤ + ℤτ`. -/
lemma exists_real_not_periodLattice_re (tau : ℂ) :
    ∃ x : ℝ, ∀ z : ℂ, IsPeriodLatticePoint tau z → z.re ≠ x := by
  let S : Set ℝ := Set.range (fun mn : ℤ × ℤ =>
    ((mn.1 : ℂ) + (mn.2 : ℂ) * tau).re)
  have hS : S.Countable := Set.countable_range _
  have hne : S ≠ Set.univ := by
    intro heq
    exact Set.not_countable_univ (heq ▸ hS)
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem S).mp hne
  refine ⟨x, fun z hz heq => hx ?_⟩
  obtain ⟨m, n, rfl⟩ := hz
  exact ⟨(m, n), heq⟩

/-- A compact vertical segment whose real coordinate misses the period lattice stays a
positive distance from every lattice point. -/
lemma exists_pos_dist_vertical_periodLattice (tau : ℂ) (htau : tau.im ≠ 0)
    (a b x : ℝ) (hx : ∀ z : ℂ, IsPeriodLatticePoint tau z → z.re ≠ x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.uIcc a b, ∀ z : ℂ,
      IsPeriodLatticePoint tau z → δ ≤ ‖((x : ℂ) + t * I) - z‖ := by
  let K : Set ℂ := (fun t : ℝ => (x : ℂ) + (t : ℂ) * I) '' Set.uIcc a b
  have hK : IsCompact K := isCompact_uIcc.image (by fun_prop)
  have hdisjoint : Disjoint K (periodPair tau htau).lattice :=
    Set.disjoint_left.mpr (by
      rintro z ⟨t, ht, rfl⟩ hz
      have hz' := (isPeriodLatticePoint_iff_mem_lattice tau htau _).mpr hz
      exact hx _ hz' (by simp))
  obtain ⟨r, hr, hdist⟩ :=
    Metric.exists_pos_forall_lt_edist hK (periodPair tau htau).isClosed_lattice hdisjoint
  refine ⟨r, NNReal.coe_pos.mpr hr, ?_⟩
  intro t ht z hz
  have h := hdist ((x : ℂ) + t * I) ⟨t, ht, rfl⟩ z
    ((isPeriodLatticePoint_iff_mem_lattice tau htau z).mp hz)
  have hnn : r < nndist ((x : ℂ) + t * I) z := by
    exact ENNReal.coe_lt_coe.mp (by simpa only [edist_nndist] using h)
  have hdist' : (r : ℝ) < dist ((x : ℂ) + t * I) z := by exact_mod_cast hnn
  simpa only [dist_eq_norm] using hdist'.le

/-- For a fixed height strip, integer translates of a vertical line avoid `ℤ + ℤτ`
with one positive distance bound and tend to the right. -/
theorem exists_periodLattice_right_sides (tau : ℂ) (htau : tau.im ≠ 0)
    (a b : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ X : ℕ → ℝ, Filter.Tendsto X Filter.atTop Filter.atTop ∧
      (∀ n, ∀ t ∈ Set.uIcc a b, ∀ z : ℂ, IsPeriodLatticePoint tau z →
        δ ≤ ‖((X n : ℂ) + t * I) - z‖) ∧
      (∀ n, ∀ z : ℂ, IsPeriodLatticePoint tau z → z.re ≠ X n) := by
  obtain ⟨x, hx⟩ := exists_real_not_periodLattice_re tau
  obtain ⟨δ, hδ, hdist⟩ := exists_pos_dist_vertical_periodLattice tau htau a b x hx
  have hshift : ∀ n : ℕ, ∀ z : ℂ,
      IsPeriodLatticePoint tau z → IsPeriodLatticePoint tau (z - (n : ℂ)) := by
    intro n z hz
    apply (isPeriodLatticePoint_add_int_mul_add_int_iff tau
      (z - (n : ℂ)) 0 (n : ℤ)).mp
    simpa using hz
  refine ⟨δ, hδ, fun n => x + n, ?_, ?_, ?_⟩
  · simpa [add_comm] using
      ((tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ => (n : ℝ))
        Filter.atTop Filter.atTop).atTop_add
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => x) Filter.atTop (𝓝 x)))
  · intro n t ht z hz
    calc
      δ ≤ ‖((x : ℂ) + t * I) - (z - n)‖ := hdist t ht _ (hshift n z hz)
      _ = ‖(((x + n : ℝ) : ℂ) + t * I) - z‖ := by
        congr 1
        push_cast
        ring
  · intro n z hz heq
    exact hx _ (hshift n z hz)
      (by simp only [Complex.sub_re, Complex.natCast_re]; linarith)

/-! ### Doubly periodic functions -/

/-- A continuous function with periods `1` and `τ` has bounded range: it takes every value on
the compact fundamental parallelogram. -/
lemma isBounded_range_of_periodic_one_of_periodic (tau : ℂ) (htau : tau.im ≠ 0)
    {f : ℂ → ℂ} (hf : Continuous f) (h₁ : Function.Periodic f 1)
    (hτ : Function.Periodic f tau) :
    Bornology.IsBounded (range f) := by
  apply (IsZLattice.isCompact_range_of_periodic (periodPair tau htau).lattice f hf ?_).isBounded
  intro z w hw
  obtain ⟨m, n, rfl⟩ := (isPeriodLatticePoint_iff_mem_lattice tau htau w).mpr hw
  rw [← add_assoc, hτ.int_mul n]
  simpa using h₁.int_mul m z

/-- **A doubly periodic entire function is constant.** This is the Liouville step of
[95, Shintani (1977), proof of Proposition 5 on p. 181], for periods `(1, τ)` with
`Im τ ≠ 0`. -/
theorem apply_eq_apply_of_differentiable_of_periodic (tau : ℂ)
    (htau : tau.im ≠ 0) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h₁ : Function.Periodic f 1) (hτ : Function.Periodic f tau) (z w : ℂ) :
    f z = f w := by
  exact hf.apply_eq_apply_of_bounded
    (isBounded_range_of_periodic_one_of_periodic tau htau hf.continuous h₁ hτ) z w

/-- A continuous function whose period law `f(z + p) = f(z)` holds off the period lattice
satisfies it everywhere: the lattice is discrete, so at a lattice point both sides are limits
along a punctured neighbourhood on which they agree. -/
lemma periodic_of_forall_not_isPeriodLatticePoint (tau : ℂ) (htau : tau.im ≠ 0)
    {f : ℂ → ℂ} (hf : Continuous f) (p : ℂ)
    (hoff : ∀ z, ¬ IsPeriodLatticePoint tau z → f (z + p) = f z) :
    Function.Periodic f p := by
  intro z
  by_cases hz : IsPeriodLatticePoint tau z
  · have hleft : Tendsto (fun w => f (w + p)) (𝓝[≠] z) (𝓝 (f (z + p))) :=
      (hf.continuousAt.comp (continuousAt_id.add_const p)).mono_left inf_le_left
    have hright : Tendsto f (𝓝[≠] z) (𝓝 (f z)) := hf.continuousAt.mono_left inf_le_left
    have heq : (fun w => f (w + p)) =ᶠ[𝓝[≠] z] f :=
      (eventually_not_isPeriodLatticePoint tau htau z).mono fun w hw => hoff w hw
    exact tendsto_nhds_unique (hleft.congr' heq) hright
  · exact hoff z hz

/-- An entire function whose period law `g(z + p) = g(z)` holds on a nonempty open set is
`p`-periodic, by the identity theorem: both sides are entire and agree near a point. -/
lemma periodic_of_differentiable_of_eqOn {g : ℂ → ℂ} (hg : Differentiable ℂ g) (p : ℂ)
    {U : Set ℂ} (hU : IsOpen U) (hne : U.Nonempty) (h : ∀ z ∈ U, g (z + p) = g z) :
    Function.Periodic g p := by
  obtain ⟨z₀, hz₀⟩ := hne
  have hshift : Differentiable ℂ (fun z : ℂ => g (z + p)) := hg.comp (by fun_prop)
  have hevent : (fun z : ℂ => g (z + p)) =ᶠ[𝓝 z₀] g := eventuallyEq_of_mem (hU.mem_nhds hz₀) h
  have heqOn : EqOn (fun z : ℂ => g (z + p)) g univ :=
    (hshift.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_eventuallyEq
      (hg.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (mem_univ z₀) hevent
  exact fun z => heqOn (mem_univ z)

/-! ### Periodic extension from a strip

A function that is `1`-periodic on a vertical strip wider than one period is determined by its
values on one period, and the periodic extension is entire when the function is holomorphic on
the strip: near a point `z₀` with integer real part `k`, the extension agrees with
`z ↦ f(z - (k - 1))`, which is defined on a neighbourhood of `z₀` and coincides with the
extension on both sides of the line `Re z = k` by the periodicity of `f`. -/

/-- Translating by a natural number inside the strip does not change a `1`-periodic function:
`f(z - m) = f(z)` for `m < Re z < L`. -/
private lemma apply_sub_natCast_eq_of_periodic_on_strip {L : ℝ} {f : ℂ → ℂ}
    (hper : ∀ z : ℂ, 0 < z.re → z.re < L - 1 → f (z + 1) = f z) (m : ℕ) :
    ∀ z : ℂ, 0 < z.re → z.re < L → (m : ℝ) < z.re → f (z - (m : ℂ)) = f z := by
  induction m with
  | zero =>
      intro z _ _ _
      simp
  | succ m ih =>
      intro z hz0 hzL hm
      have hstep0 : 0 < (z - ((m + 1 : ℕ) : ℂ)).re := by
        simpa using hm
      have hstepL : (z - ((m + 1 : ℕ) : ℂ)).re < L - 1 := by
        simp only [Complex.sub_re, Complex.natCast_re]
        have hm1 : (1 : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast Nat.succ_pos m
        linarith
      calc
        f (z - ((m + 1 : ℕ) : ℂ)) =
            f ((z - ((m + 1 : ℕ) : ℂ)) + 1) :=
          (hper (z - ((m + 1 : ℕ) : ℂ)) hstep0 hstepL).symm
        _ = f (z - (m : ℂ)) := by
          congr 1
          push_cast
          ring
        _ = f z := by
          have hmCast : (m : ℝ) < (m + 1 : ℕ) := by
            exact_mod_cast Nat.lt_succ_self m
          exact ih z hz0 hzL (hmCast.trans hm)

/-- Near a point `z₀` with `k = ⌈Re z₀⌉`, the periodic extension `z ↦ f(z - (⌈Re z⌉ - 1))`
agrees with the single translate `z ↦ f(z - (k - 1))`: to the left of the line `Re z = k` by
definition, to the right by the periodicity of `f`. -/
private lemma periodic_extension_eventuallyEq {L : ℝ} (hL : 1 < L) {f : ℂ → ℂ}
    (hper : ∀ z : ℂ, 0 < z.re → z.re < L - 1 → f (z + 1) = f z) (z₀ : ℂ) :
    (fun z : ℂ => f (z - ((⌈z.re⌉ - 1 : ℤ) : ℂ))) =ᶠ[𝓝 z₀]
      fun z => f (z - ((⌈z₀.re⌉ - 1 : ℤ) : ℂ)) := by
  set k : ℤ := ⌈z₀.re⌉ with hk
  have hkLower : (k : ℝ) - 1 < z₀.re := by
    rw [hk]
    linarith [Int.ceil_lt_add_one z₀.re]
  have hkUpper : z₀.re ≤ (k : ℝ) := Int.le_ceil z₀.re
  have hmin : 0 < min 1 (L - 1) := lt_min one_pos (sub_pos.mpr hL)
  have hnhds : {z : ℂ | (k : ℝ) - 1 < z.re ∧
      z.re < (k : ℝ) + min 1 (L - 1)} ∈ 𝓝 z₀ := by
    apply ((isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_re continuous_const)).mem_nhds
    exact ⟨hkLower, hkUpper.trans_lt (lt_add_of_pos_right _ hmin)⟩
  filter_upwards [hnhds] with z hz
  rcases le_or_gt z.re (k : ℝ) with hzk | hzk
  · have hceil : ⌈z.re⌉ = k := Int.ceil_eq_iff.mpr ⟨hz.1, hzk⟩
    simp only [hceil]
  · have hzUpper : z.re ≤ ((k + 1 : ℤ) : ℝ) := by
      calc
        z.re ≤ (k : ℝ) + min 1 (L - 1) := hz.2.le
        _ ≤ (k : ℝ) + 1 := add_le_add_right (min_le_left 1 (L - 1)) _
        _ = ((k + 1 : ℤ) : ℝ) := by norm_num
    have hceil : ⌈z.re⌉ = k + 1 := by
      apply Int.ceil_eq_iff.mpr
      refine ⟨?_, hzUpper⟩
      push_cast
      linarith
    have hz0 : 0 < (z - (k : ℂ)).re := by
      simpa using hzk
    have hzL : (z - (k : ℂ)).re < L - 1 := by
      simp only [Complex.sub_re, Complex.intCast_re]
      linarith [min_le_right 1 (L - 1)]
    simp only [hceil]
    calc
      f (z - (((k + 1 : ℤ) - 1 : ℤ) : ℂ)) = f (z - (k : ℂ)) := by
        congr 1
        push_cast
        ring
      _ = f ((z - (k : ℂ)) + 1) := (hper (z - (k : ℂ)) hz0 hzL).symm
      _ = f (z - ((k - 1 : ℤ) : ℂ)) := by
        congr 1
        push_cast
        ring

/-- **Periodic extension from a strip.** A function holomorphic on the strip `0 < Re z < L`,
`L > 1`, satisfying `f(z + 1) = f(z)` whenever `0 < Re z < L - 1`, extends to a `1`-periodic
entire function. The extension is `z ↦ f(z - (⌈Re z⌉ - 1))`, which reads `f` at the unique
translate with real part in `(0, 1]`. -/
theorem exists_differentiable_periodic_one_extension {L : ℝ} (hL : 1 < L) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z | 0 < z.re ∧ z.re < L})
    (hper : ∀ z : ℂ, 0 < z.re → z.re < L - 1 → f (z + 1) = f z) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ Function.Periodic g 1 ∧
      ∀ z : ℂ, 0 < z.re → z.re < L → g z = f z := by
  refine ⟨fun z => f (z - ((⌈z.re⌉ - 1 : ℤ) : ℂ)), ?_, ?_, ?_⟩
  · intro z₀
    have hpoint0 : 0 < (z₀ - ((⌈z₀.re⌉ - 1 : ℤ) : ℂ)).re := by
      simp only [Complex.sub_re, Complex.intCast_re, Int.cast_sub, Int.cast_one, Complex.one_re]
      linarith [Int.ceil_lt_add_one z₀.re]
    have hpointL : (z₀ - ((⌈z₀.re⌉ - 1 : ℤ) : ℂ)).re < L := by
      simp only [Complex.sub_re, Complex.intCast_re, Int.cast_sub, Int.cast_one, Complex.one_re]
      linarith [Int.le_ceil z₀.re]
    have hopen : IsOpen {z : ℂ | 0 < z.re ∧ z.re < L} :=
      (isOpen_lt continuous_const continuous_re).inter
        (isOpen_lt continuous_re continuous_const)
    have hfdiff : DifferentiableAt ℂ f (z₀ - ((⌈z₀.re⌉ - 1 : ℤ) : ℂ)) :=
      hf.differentiableAt (hopen.mem_nhds ⟨hpoint0, hpointL⟩)
    exact (hfdiff.comp z₀ (differentiableAt_id.sub_const _)).congr_of_eventuallyEq
      (periodic_extension_eventuallyEq hL hper z₀)
  · intro z
    simp only [Complex.add_re, Complex.one_re, Int.ceil_add_one]
    congr 1
    push_cast
    ring
  · intro z hz0 hzL
    have hnNonneg : 0 ≤ ⌈z.re⌉ - 1 := by
      rw [sub_nonneg, Int.one_le_ceil_iff]
      exact hz0
    have hnCast : (((⌈z.re⌉ - 1).toNat : ℕ) : ℂ) = ((⌈z.re⌉ - 1 : ℤ) : ℂ) := by
      exact_mod_cast Int.toNat_of_nonneg hnNonneg
    have hnLt : (((⌈z.re⌉ - 1).toNat : ℕ) : ℝ) < z.re := by
      rw [show (((⌈z.re⌉ - 1).toNat : ℕ) : ℝ) = ((⌈z.re⌉ - 1 : ℤ) : ℝ) by
        exact_mod_cast Int.toNat_of_nonneg hnNonneg]
      push_cast
      linarith [Int.ceil_lt_add_one z.re]
    have h := apply_sub_natCast_eq_of_periodic_on_strip hper (⌈z.re⌉ - 1).toNat z hz0 hzL hnLt
    rwa [hnCast] at h

/-! ### Lattice avoidance at an irrational point

What the excluded case `r ∉ ℤ²` buys on the real line, at an irrational `τ`. A rational linear
relation in `τ` forces its coefficients to vanish
(`SICs.Analysis.Irrational.ratCast_eq_zero_of_irrational_mul`), so neither `⟨⟨r,τ⟩⟩`
nor its transported
form `⟨⟨r,τ⟩⟩/j_M(τ)` can sit on the relevant lattice; the finite `q`-Pochhammer factor of
[AFK25, equation (1.26), `eq:shindf`] is therefore nonzero there, which is the non-pole condition
every real-line consumer of the cocycle needs. The boundary limit of
`SICs.Cocycle.ModularBoundary` needs the last two at every matrix the word visits: the
transported argument must avoid the lattice of its own period, so that each `σ_S` factor can be
moved into its chamber, and the finite factor must be nonzero at the limit point for the limit of
the quotient to be the quotient of the limits. -/

/-- **The transported argument is lattice-free too.** For an irrational `τ`, a nonintegral `r`,
and any integer matrix with `j_M(τ) ≠ 0`,

$$\frac{\langle\langle r,\tau\rangle\rangle}{j_M(\tau)}
  \notin \mathbb Z\,(M\cdot\tau) + \mathbb Z .$$

Clearing `j_M(τ)` turns `⟨⟨r,τ⟩⟩/j_M(τ) = a(M·τ) + b` into
`r₁τ - r₀ = a(M₀₀τ + M₀₁) + b(M₁₀τ + M₁₁)`; irrationality of `τ` separates the two sides
coefficientwise and leaves `r ∈ ℤ²`. This is the real-line counterpart of
`SICs.Cocycle.UpperHalfPlane.not_isPeriodLatticePoint_fracSymplecticFormRat_div`, with
irrationality of `τ` in place of `Im τ ≠ 0`. The boundary comparison for the cocycle product
uses this at each intermediate matrix. -/
theorem sigmaSLatticeFree_fracSymplecticFormRat_div {τ : ℝ} (hτ : Irrational τ)
    {r : Fin 2 → ℚ} (hr : ¬ IsIntegralIndex r) (M : Mat(2, ℤ))
    (hden : fltDenominator M τ ≠ 0) :
    SigmaSLatticeFree (flt M τ)
      (fracSymplecticFormRat r τ / fltDenominator M τ) := by
  intro a b hab
  have hd : fltDenominator M τ = (M 1 0 : ℝ) * τ + (M 1 1 : ℝ) := rfl
  have hden' : ((M 1 0 : ℝ) * τ + (M 1 1 : ℝ)) ≠ 0 := by rw [← hd]; exact hden
  rw [div_eq_iff hden, flt, hd] at hab
  -- Clear `j_M(τ)`: `⟨⟨r,τ⟩⟩ = a(M₀₀τ + M₀₁) + b·j_M(τ)`.
  have hnum : (r 1 : ℝ) * τ - (r 0 : ℝ) =
      (a : ℝ) * ((M 0 0 : ℝ) * τ + (M 0 1 : ℝ)) +
        (b : ℝ) * ((M 1 0 : ℝ) * τ + (M 1 1 : ℝ)) := by
    rw [show ((r 1 : ℝ) * τ - (r 0 : ℝ)) = fracSymplecticFormRat r τ from rfl, hab,
      add_mul, mul_assoc, div_mul_cancel₀ _ hden']
  -- Irrationality separates the two sides coefficientwise.
  obtain ⟨h1, h0⟩ := ratCast_eq_zero_of_irrational_mul
    (a := r 1 - ((a * M 0 0 + b * M 1 0 : ℤ) : ℚ))
    (b := r 0 + ((a * M 0 1 + b * M 1 1 : ℤ) : ℚ)) hτ (by push_cast; linear_combination hnum)
  exact hr (isIntegralIndex_of_coords ⟨-(a * M 0 1 + b * M 1 1), by push_cast at h0 ⊢; linarith⟩
    ⟨a * M 0 0 + b * M 1 0, by push_cast at h1 ⊢; linarith⟩)

/-- **`r ∉ ℤ²` is exactly lattice-freeness of `⟨⟨r,τ⟩⟩`** at an irrational `τ`: `r₁τ - r₀ = aτ + b`
with `a, b ∈ ℤ` forces `r₁ = a` and `r₀ = -b`, since otherwise `τ` would be the rational number
`(r₀+b)/(r₁-a)`. This is the translation between `sfModularCocycleReal_add_intVec`'s own
hypothesis and the one the real-line construction consumes
(`SICs.Analysis.PeriodLattice.SigmaSLatticeFree`); it is the case `M = 1` of
`sigmaSLatticeFree_fracSymplecticFormRat_div`. -/
theorem sigmaSLatticeFree_fracSymplecticFormRat {τ : ℝ} (hτ : Irrational τ) {r : Fin 2 → ℚ}
    (hr : ¬ IsIntegralIndex r) : SigmaSLatticeFree τ (fracSymplecticFormRat r τ) := by
  have h := sigmaSLatticeFree_fracSymplecticFormRat_div hτ hr 1
    (by rw [fltDenominator_one]; exact one_ne_zero)
  rwa [flt_one, fltDenominator_one, div_one] at h

/-- At an irrational real period, the fractional symplectic argument belongs to its period
lattice exactly when the rational characteristic is integral. This is the complex-lattice
form of `sigmaSLatticeFree_fracSymplecticFormRat`. -/
theorem isPeriodLatticePoint_fracSymplecticFormRat_iff {τ : ℝ} (hτ : Irrational τ)
    (r : Fin 2 → ℚ) :
    IsPeriodLatticePoint (τ : ℂ) (fracSymplecticFormRat r (τ : ℂ)) ↔ IsIntegralIndex r := by
  constructor
  · intro hlat
    by_contra hr
    have hfree := sigmaSLatticeFree_fracSymplecticFormRat hτ hr
    have hoff := (sigmaSLatticeFree_iff_not_isPeriodLatticePoint τ
      (fracSymplecticFormRat r τ)).mp hfree
    rw [ofReal_fracSymplecticFormRat] at hoff
    exact hoff hlat
  · intro hr
    obtain ⟨a, ha⟩ := hr 0
    obtain ⟨b, hb⟩ := hr 1
    refine ⟨-a, b, ?_⟩
    rw [fracSymplecticFormRat, ha, hb]
    push_cast
    ring

end SIC

end
