/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Completion.Basic
import SICs.FieldTheory.BaseChange

/-!
# Norms between local completions of number fields

Algebraic and multiplicative norms between completions at finite and infinite places lying over
one another, with continuity, norm composition in towers, and formulas on the base completion.

## The argument

At finite places, `SICs.ClassField.Completion.Basic` supplies completion maps and topological
algebra instances. Mathlib's normalized finite-place norms do not in general make the resulting
algebra a `NormedAlgebra`: restriction can raise norms to a ramification/residue degree. The
continuity theorem in `SICs.FieldTheory.BaseChange` expresses the algebraic norm as the
determinant of left multiplication. Powers tending to zero show that an element of norm below one
has algebraic norm below one. Scaling powers of a norm-one element by a small base-field element
then bounds its algebraic norm. Applying these facts to a unit and its inverse gives the
integral-unit equivalence.

At infinite places the normed-algebra structure supplied by the completion foundation gives a
continuous local norm. Algebraic norms compose in towers at both kinds of place, and local
degrees multiply at finite places. The principal norm and power-in-range formulas specialize the
unit-norm lemmas in `SICs.FieldTheory.BaseChange`. These maps feed the restricted-product idèle
norm.

The finite-completion algebra and scalar-tower instances supplied by the completion foundation,
and the module-finiteness instances depending on a chosen lying-over map, are scoped to avoid
non-definitional diamonds for self-extensions. Consumers use
`open scoped SIC.FinitePlace` at finite places and
`open scoped NumberField.LiesOver SIC.InfinitePlace` at infinite places.
-/

noncomputable section

namespace SIC

open IsDedekindDomain NumberField

/-! ### Finite places

Continuity preserves the convergence to zero of powers of an element of norm below one. For a
norm-one element, scaling each power by a small base-field element bounds its algebraic norm;
the norm formula on base-field elements accounts for the local degree. Applying both bounds to
an element and its inverse characterizes integral units under the local norm.
-/

namespace FinitePlace

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

/-- The multiplicative local norm between finite completions. -/
def localNorm : (w.adicCompletion L)ˣ →* (v.adicCompletion K)ˣ := by
  exact Units.map (Algebra.norm (v.adicCompletion K))

/-- The value of the finite local norm is the algebraic norm. -/
@[simp]
theorem localNorm_val (x : (w.adicCompletion L)ˣ) :
    ((localNorm v w x : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
      Algebra.norm (v.adicCompletion K) (x : w.adicCompletion L) := by
  rfl

/-- The finite local norm is continuous. -/
theorem continuous_localNorm : Continuous (localNorm v w) := by
  apply Continuous.units_map
  exact continuous_algebraNorm_of_continuousSMul
    (k := v.adicCompletion K) (E := w.adicCompletion L)

/-- An element of norm less than one has algebraic norm of norm less than one; used by
`norm_algebraNorm_le_one_of_norm_eq_one` and `localNorm_mem_integral_units_iff`. -/
private theorem norm_algebraNorm_lt_one_of_norm_lt_one
    {x : w.adicCompletion L} (hx : ‖x‖ < 1) :
    ‖Algebra.norm (v.adicCompletion K) x‖ < 1 := by
  apply tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mp
  simpa only [Function.comp_def, map_pow, Algebra.norm_zero] using
    ((continuous_algebraNorm_of_continuousSMul
      (k := v.adicCompletion K) (E := w.adicCompletion L)).tendsto 0).comp
        (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hx)

/-- Bounds the algebraic norm of a norm-one element; used by
`localNorm_mem_integral_units_iff`. -/
private theorem norm_algebraNorm_le_one_of_norm_eq_one
    {x : w.adicCompletion L} (hx : ‖x‖ = 1) :
    ‖Algebra.norm (v.adicCompletion K) x‖ ≤ 1 := by
  let e := w.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) *
    w.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)
  let d := Module.finrank (v.adicCompletion K) (w.adicCompletion L)
  have he : 0 < e :=
    mul_pos (w.asIdeal.ramificationIdx_pos _) (w.asIdeal.inertiaDeg_pos _)
  obtain ⟨c : v.adicCompletion K, hc0, hc1⟩ :=
    NormedField.exists_norm_lt (v.adicCompletion K) zero_lt_one
  have hsmall (n : ℕ) : ‖c • x ^ n‖ < 1 := by
    rw [Algebra.smul_def, norm_mul, norm_pow, hx, one_pow, mul_one]
    change ‖completionMap v w c‖ < 1
    rw [completionMap_norm]
    exact pow_lt_one₀ hc0.le hc1 he.ne'
  have hbound (n : ℕ) :
      ‖c‖ ^ d * ‖Algebra.norm (v.adicCompletion K) x‖ ^ n < 1 := by
    have h := norm_algebraNorm_lt_one_of_norm_lt_one v w (hsmall n)
    rw [Algebra.smul_def, map_mul, Algebra.norm_algebraMap, map_pow,
      norm_mul, norm_pow, norm_pow] at h
    exact h
  by_contra hle
  have hNx : 1 < ‖Algebra.norm (v.adicCompletion K) x‖ := lt_of_not_ge hle
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((‖c‖ ^ d)⁻¹) hNx
  have hcpow : 0 < ‖c‖ ^ d := pow_pos hc0 _
  have hone : 1 < ‖c‖ ^ d * ‖Algebra.norm (v.adicCompletion K) x‖ ^ n := by
    have hmul := mul_lt_mul_of_pos_left hn hcpow
    simpa [hcpow.ne'] using hmul
  exact (not_lt_of_ge hone.le) (hbound n)

/-- A finite local norm is an integral unit exactly when its argument is an integral unit:
$N_{L_w/K_v}(x)\in U_v \iff x\in U_w$. Milne, *Class Field Theory*, Chapter I, proof of
Lemma 1.3. -/
theorem localNorm_mem_integral_units_iff {x : (w.adicCompletion L)ˣ} :
    localNorm v w x ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units ↔
      x ∈ (Submonoid.ofClass (w.adicCompletionIntegers L)).units := by
  constructor
  · intro hx
    have hnorm :
        ‖((localNorm v w x : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ = 1 :=
      Valued.toNormedField.norm_eq_one_iff.mpr
        (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hx)
    rw [localNorm_val] at hnorm
    apply HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr
    apply Valued.toNormedField.norm_eq_one_iff.mp
    rcases lt_trichotomy ‖(x : w.adicCompletion L)‖ 1 with hlt | heq | hgt
    · exact ((norm_algebraNorm_lt_one_of_norm_lt_one v w hlt).ne hnorm).elim
    · exact heq
    · have hinv := norm_algebraNorm_lt_one_of_norm_lt_one v w
        (x := ((x⁻¹ : (w.adicCompletion L)ˣ) : w.adicCompletion L))
        (by simpa using inv_lt_one_of_one_lt₀ hgt)
      change ‖((localNorm v w x⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ < 1 at hinv
      rw [map_inv, Units.val_inv_eq_inv_val, norm_inv, localNorm_val, hnorm, inv_one] at hinv
      exact (lt_irrefl _ hinv).elim
  · intro hx
    have hx' : ‖(x : w.adicCompletion L)‖ = 1 :=
      Valued.toNormedField.norm_eq_one_iff.mpr
        (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hx)
    have hnorm :
        ‖((localNorm v w x : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ = 1 := by
      apply le_antisymm
      · simpa only [localNorm_val] using norm_algebraNorm_le_one_of_norm_eq_one v w hx'
      · have hinv := norm_algebraNorm_le_one_of_norm_eq_one v w
          (x := (x⁻¹ : (w.adicCompletion L)ˣ)) (by
            simp only [Units.val_inv_eq_inv_val, norm_inv, hx', inv_one])
        rw [← localNorm_val, map_inv, Units.val_inv_eq_inv_val, norm_inv] at hinv
        exact ((inv_le_one_iff₀).mp hinv).resolve_left
          (not_le_of_gt (norm_pos_iff.mpr (Units.ne_zero _)))
    exact HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr
      (Valued.toNormedField.norm_eq_one_iff.mp hnorm)

/-- A finite local norm carries integral units to integral units, by
`localNorm_mem_integral_units_iff`. -/
theorem localNorm_mem_integral_units
    {x : (w.adicCompletion L)ˣ}
    (hx : x ∈ (Submonoid.ofClass (w.adicCompletionIntegers L)).units) :
    localNorm v w x ∈
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units :=
  (localNorm_mem_integral_units_iff v w).mpr hx

/-- On an element of the base completion, the local norm is the appropriate power. -/
@[simp]
theorem localNorm_principal (x : (v.adicCompletion K)ˣ) :
    localNorm v w (Units.map (completionMap v w) x) =
      x ^ Module.finrank (v.adicCompletion K) (w.adicCompletion L) :=
  unitsMap_norm_algebraMap x

/-- Every nth power is a local norm when $[L_w:K_v]$ divides $n$; the witness is the
inclusion of $x^{n/[L_w:K_v]}$. This applies `localNorm_principal` in Milne, Chapter VII,
Lemma 6.4 and the proof of Proposition 6.10. -/
theorem pow_mem_range_localNorm {n : ℕ}
    (hd : Module.finrank (v.adicCompletion K) (w.adicCompletion L) ∣ n)
    (x : (v.adicCompletion K)ˣ) : x ^ n ∈ (localNorm v w).range :=
  pow_mem_range_unitsMap_norm hd x

/-- A finite local norm is surjective when $[L_w:K_v]=1$, by `localNorm_principal`. -/
theorem localNorm_surjective_of_finrank_eq_one
    (h : Module.finrank (v.adicCompletion K) (w.adicCompletion L) = 1) :
    Function.Surjective (localNorm v w) :=
  unitsMap_norm_surjective_of_finrank_eq_one h

variable {M : Type*} [Field M] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [NumberField M]
  (u : HeightOneSpectrum (𝓞 M)) [u.asIdeal.LiesOver w.asIdeal]

/-- Finite local norms compose in towers of lying-over primes. -/
@[simp]
theorem localNorm_trans (x : (u.adicCompletion M)ˣ) :
    letI : u.asIdeal.LiesOver v.asIdeal :=
      Ideal.LiesOver.trans u.asIdeal w.asIdeal v.asIdeal
    localNorm v w (localNorm w u x) = localNorm v u x := by
  let _ : u.asIdeal.LiesOver v.asIdeal :=
    Ideal.LiesOver.trans u.asIdeal w.asIdeal v.asIdeal
  apply Units.ext
  change Algebra.norm (v.adicCompletion K)
      (Algebra.norm (w.adicCompletion L) (x : u.adicCompletion M)) =
    Algebra.norm (v.adicCompletion K) (x : u.adicCompletion M)
  exact Algebra.norm_norm

/-- Finite local degrees multiply in towers of lying-over primes:
$[L_w:K_v]\,[M_u:L_w]=[M_u:K_v]$. -/
theorem finrank_mul_finrank :
    letI : u.asIdeal.LiesOver v.asIdeal :=
      Ideal.LiesOver.trans u.asIdeal w.asIdeal v.asIdeal
    Module.finrank (v.adicCompletion K) (w.adicCompletion L) *
        Module.finrank (w.adicCompletion L) (u.adicCompletion M) =
      Module.finrank (v.adicCompletion K) (u.adicCompletion M) := by
  let _ : u.asIdeal.LiesOver v.asIdeal :=
    Ideal.LiesOver.trans u.asIdeal w.asIdeal v.asIdeal
  exact Module.finrank_mul_finrank _ _ _

end FinitePlace

/-! ### Infinite places -/

namespace InfinitePlace

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.LiesOver

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L]
  (v : NumberField.InfinitePlace K) (w : NumberField.InfinitePlace L) [w.LiesOver v]

/-- The multiplicative local norm between infinite completions. -/
def localNorm : w.Completionˣ →* v.Completionˣ := by
  exact Units.map (Algebra.norm v.Completion)

omit [NumberField K] [NumberField L] in
/-- The value of the infinite local norm is the algebraic norm. -/
@[simp]
theorem localNorm_val (x : w.Completionˣ) :
    ((localNorm v w x : v.Completionˣ) : v.Completion) =
      Algebra.norm v.Completion (x : w.Completion) := by
  rfl

omit [NumberField K] [NumberField L] in
/-- The infinite local norm is continuous. -/
theorem continuous_localNorm : Continuous (localNorm v w) := by
  apply Continuous.units_map
  exact continuous_algebraNorm_of_continuousSMul
    (k := v.Completion) (E := w.Completion)

omit [NumberField K] [NumberField L] in
/-- On an element of the base completion, the infinite local norm is the appropriate power. -/
@[simp]
theorem localNorm_principal (x : v.Completionˣ) :
    localNorm v w
        (Units.map (NumberField.LiesOver.completionMap (v := v) (w := w)) x) =
      x ^ Module.finrank v.Completion w.Completion :=
  unitsMap_norm_algebraMap x

omit [NumberField K] [NumberField L] in
/-- Every nth power is an infinite local norm when $[L_w:K_v]$ divides $n$; this is the
base-field norm formula `localNorm_principal` used in Milne, Chapter VII, Lemma 6.4. -/
theorem pow_mem_range_localNorm {n : ℕ} (hd : Module.finrank v.Completion w.Completion ∣ n)
    (x : v.Completionˣ) : x ^ n ∈ (localNorm v w).range :=
  pow_mem_range_unitsMap_norm hd x

omit [NumberField K] [NumberField L] in
/-- An infinite local norm is surjective when $[L_w:K_v]=1$, by `localNorm_principal`. -/
theorem localNorm_surjective_of_finrank_eq_one (h : Module.finrank v.Completion w.Completion = 1) :
    Function.Surjective (localNorm v w) :=
  unitsMap_norm_surjective_of_finrank_eq_one h

variable {M : Type*} [Field M] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [NumberField M] (u : NumberField.InfinitePlace M) [u.LiesOver w] [u.LiesOver v]

omit [NumberField K] [NumberField L] [NumberField M] in
/-- Infinite local norms compose in towers of lying-over places. -/
@[simp]
theorem localNorm_trans (x : u.Completionˣ) :
    localNorm v w (localNorm w u x) = localNorm v u x := by
  apply Units.ext
  change Algebra.norm v.Completion
      (Algebra.norm w.Completion (x : u.Completion)) =
    Algebra.norm v.Completion (x : u.Completion)
  exact Algebra.norm_norm

end InfinitePlace

end SIC

end
