/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Quadratic.DegreeTwoAlgebras
import SICs.Quadratic.FundamentalDiscriminants
import Mathlib.LinearAlgebra.Unimodular
import Mathlib.NumberTheory.NumberField.Discriminant.Basic

/-!
# Discriminants of Quadratic Number Fields

Integral bases and fundamentality of quadratic field discriminants.

This file proves that the number-field discriminant of every degree-two number field has the
standard fundamental-discriminant shape. The proof is elementary and uses maximality of the ring
of integers directly.

First, `1` is unimodular in the free rank-two ring of integers, so Mathlib extends it to
a basis `(1, ω)`. The shared degree-two form of Cayley--Hamilton then gives

`disc(K) = Tr(ω)² - 4 Nm(ω)`.

If a prohibited square factor or 2-adic residue remained, a suitable quotient `(ω-r)/p` would
satisfy a monic integral quadratic. It would therefore belong to the ring of integers, while its
`ω`-coordinate would force the nonunit denominator `p` to be a unit. This contradiction proves
the squarefree and modulo-four alternatives.

## Main definitions and results

- `quadraticIntegralBasisOne`: an integral basis `(1, ω)` of a degree-two number field.
- `quadratic_discr_eq_trace_sq_sub_four_norm`: the formula
  `disc(K) = Tr(ω)² - 4 Nm(ω)`.
- `isFundamentalDiscriminant_numberField_discr`: every quadratic number-field discriminant is
  fundamental in the arithmetic sense used by this project.
- `not_isSquare_numberField_discr`: a quadratic number-field discriminant is not a square.

## References

- [AFK25, §1.3], especially the fundamental-discriminant alternatives in equation (1.33)
-/

noncomputable section

namespace SIC

open Module NumberField

variable {K : Type*} [Field K] [NumberField K]

/-! ### An integral basis containing one

The ring of integers has rank two over `ℤ`, and `1` is unimodular in every nonzero free
algebra. Mathlib extends a unimodular vector in rank two to a basis. Choosing this extension
gives the integral basis `(1, ω)` used below.
-/

/-- An integral basis starting with one exists; used by `quadraticIntegralBasisOne` and its
first-vector specification. -/
private lemma exists_quadraticIntegralBasisOne (hfin : Module.finrank ℚ K = 2) :
    ∃ b : Basis (Fin 2) ℤ (NumberField.RingOfIntegers K), b 0 = 1 := by
  apply Module.IsUnimodular.exists_basis_zero_eq
    (show Module.finrank ℤ (NumberField.RingOfIntegers K) = 2 by
      rw [NumberField.RingOfIntegers.rank, hfin])
  exact Module.Free.isUnimodular_one

/-- An integral basis of a quadratic number field whose first vector is one. -/
noncomputable def quadraticIntegralBasisOne (hfin : Module.finrank ℚ K = 2) :
    Basis (Fin 2) ℤ (NumberField.RingOfIntegers K) :=
  (exists_quadraticIntegralBasisOne hfin).choose

/-- The first vector of `quadraticIntegralBasisOne` is one. -/
@[simp]
lemma quadraticIntegralBasisOne_zero (hfin : Module.finrank ℚ K = 2) :
    quadraticIntegralBasisOne hfin 0 = 1 :=
  (exists_quadraticIntegralBasisOne hfin).choose_spec

/-- The second vector in the chosen integral basis containing one. -/
noncomputable def quadraticIntegralGenerator (hfin : Module.finrank ℚ K = 2) :
    NumberField.RingOfIntegers K :=
  quadraticIntegralBasisOne hfin 1

/-! ### The trace-norm discriminant formula

Cayley--Hamilton gives the quadratic relation for an arbitrary algebraic integer. Applying the
trace to that relation computes the determinant of the trace pairing on the basis `(1, ω)` as
`Tr(ω)² - 4 Nm(ω)`.
-/

/-- An algebraic integer in a quadratic number field satisfies its trace-and-norm polynomial.

This specializes `DegreeTwoAlgebra.sq_eq_trace_mul_sub_norm_of_basis` to a quadratic ring of
integers. -/
lemma quadratic_sq_eq_trace_mul_sub_norm (hfin : Module.finrank ℚ K = 2)
    (x : NumberField.RingOfIntegers K) :
    x ^ 2 = algebraMap ℤ (NumberField.RingOfIntegers K)
        (Algebra.trace ℤ (NumberField.RingOfIntegers K) x) * x -
      algebraMap ℤ (NumberField.RingOfIntegers K)
        (Algebra.norm ℤ x) := by
  let b := quadraticIntegralBasisOne hfin
  exact DegreeTwoAlgebra.sq_eq_trace_mul_sub_norm_of_basis ℤ _ b x

/-- The number-field discriminant of a quadratic field is the trace-norm discriminant of the
second vector in an integral basis containing one. -/
lemma quadratic_discr_eq_trace_sq_sub_four_norm (hfin : Module.finrank ℚ K = 2) :
    NumberField.discr K =
      Algebra.trace ℤ (NumberField.RingOfIntegers K) (quadraticIntegralGenerator hfin) ^ 2 -
        4 * Algebra.norm ℤ (quadraticIntegralGenerator hfin) := by
  let b := quadraticIntegralBasisOne hfin
  let w := quadraticIntegralGenerator hfin
  let t := Algebra.trace ℤ (NumberField.RingOfIntegers K) w
  let n := Algebra.norm ℤ w
  have hfinO : Module.finrank ℤ (NumberField.RingOfIntegers K) = 2 := by
    rw [NumberField.RingOfIntegers.rank, hfin]
  have hone : Algebra.trace ℤ (NumberField.RingOfIntegers K) 1 = 2 := by
    simpa [hfinO] using
      (Algebra.trace_algebraMap (R := ℤ) (S := NumberField.RingOfIntegers K) 1)
  have hsq := congrArg (Algebra.trace ℤ (NumberField.RingOfIntegers K))
    (quadratic_sq_eq_trace_mul_sub_norm hfin w)
  have htrsq : Algebra.trace ℤ (NumberField.RingOfIntegers K) (w ^ 2) = t ^ 2 - 2 * n := by
    simp only [map_sub] at hsq
    rw [← Algebra.smul_def] at hsq
    simp only [map_smul, Algebra.trace_algebraMap, hfinO, nsmul_eq_mul,
      Nat.cast_ofNat, smul_eq_mul] at hsq
    simpa [t, n, pow_two] using hsq
  change NumberField.discr K = t ^ 2 - 4 * n
  rw [← NumberField.discr_eq_discr K b, Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  change Algebra.trace ℤ (NumberField.RingOfIntegers K) (b 0 * b 0) *
      Algebra.trace ℤ (NumberField.RingOfIntegers K) (b 1 * b 1) -
      Algebra.trace ℤ (NumberField.RingOfIntegers K) (b 0 * b 1) *
        Algebra.trace ℤ (NumberField.RingOfIntegers K) (b 1 * b 0) = t ^ 2 - 4 * n
  have hb0 : b 0 = 1 := quadraticIntegralBasisOne_zero hfin
  have hb1 : b 1 = w := rfl
  rw [hb0, hb1]
  simp only [one_mul, mul_one]
  rw [← pow_two, htrsq, hone]
  change 2 * (t ^ 2 - 2 * n) - t * t = t ^ 2 - 4 * n
  ring

/-! ### Maximality and the fundamental-discriminant alternatives

If a forbidden square factor remained in the trace-norm discriminant, the corresponding divided
generator `(ω-r)/p` would satisfy a monic integral quadratic. Maximality would put it back in the
ring of integers, contradicting the fact that `(1, ω)` is an integral basis. Applying this argument
to odd primes and then to the possible residues modulo four gives exactly the two alternatives in
[AFK25, equation (1.33)].
-/

/-- If `(ω-r)/p` is integral for the second vector `ω` of an integral basis `(1,ω)`, then the
integer denominator `p` is a unit. -/
private lemma isUnit_of_isIntegral_generator_sub_div (hfin : Module.finrank ℚ K = 2)
    (p r : ℤ) (hp : p ≠ 0)
    (hint : IsIntegral ℤ
      ((algebraMap ℤ K p)⁻¹ *
        ((quadraticIntegralGenerator hfin : NumberField.RingOfIntegers K) : K) -
          (algebraMap ℤ K p)⁻¹ * algebraMap ℤ K r)) :
    IsUnit p := by
  let b := quadraticIntegralBasisOne hfin
  let w := quadraticIntegralGenerator hfin
  let x : K := (algebraMap ℤ K p)⁻¹ * (w : K) -
    (algebraMap ℤ K p)⁻¹ * algebraMap ℤ K r
  let ox : NumberField.RingOfIntegers K := ⟨x, hint⟩
  have hpK : algebraMap ℤ K p ≠ 0 := by
    simpa using (Int.cast_ne_zero.mpr hp : (p : K) ≠ 0)
  have heq : p • ox = w - algebraMap ℤ (NumberField.RingOfIntegers K) r := by
    have heqK : (p : K) * x = (w : K) - (r : K) := by
      dsimp [x]
      field_simp
    apply Subtype.ext
    change algebraMap (NumberField.RingOfIntegers K) K (p • ox) =
      algebraMap (NumberField.RingOfIntegers K) K
        (w - algebraMap ℤ (NumberField.RingOfIntegers K) r)
    rw [map_sub, map_zsmul]
    simp only [← RingOfIntegers.coe_eq_algebraMap]
    have hox : ((ox : NumberField.RingOfIntegers K) : K) = x := rfl
    rw [hox]
    simpa [smul_eq_mul] using heqK
  have hcoord := congrArg (fun z : NumberField.RingOfIntegers K ↦ b.repr z 1) heq
  have hb0 : b 0 = 1 := quadraticIntegralBasisOne_zero hfin
  have hb1 : b 1 = w := rfl
  have honeCoord : b.repr (1 : NumberField.RingOfIntegers K) 1 = 0 := by
    rw [← hb0, Basis.repr_self]
    simp
  have hwCoord : b.repr w 1 = 1 := by
    rw [← hb1, Basis.repr_self]
    simp
  have hrCoord : b.repr (r : NumberField.RingOfIntegers K) 1 = 0 := by
    have hr : (r : NumberField.RingOfIntegers K) =
        r • (1 : NumberField.RingOfIntegers K) := by
      simp [Algebra.smul_def]
    rw [hr]
    rw [map_smul]
    simp [Finsupp.smul_apply, honeCoord]
  have hmul : p * b.repr ox 1 = 1 := by
    rw [map_smul, map_sub] at hcoord
    simpa [Finsupp.smul_apply, hwCoord, hrCoord] using hcoord
  rw [isUnit_iff_exists_inv]
  exact ⟨b.repr ox 1, hmul⟩

/-- Exact integral coefficient relations make the divided generator `(ω-r)/p` integral. -/
private lemma isIntegral_generator_sub_div_of_relations (hfin : Module.finrank ℚ K = 2)
    (p r q c : ℤ) (hp : p ≠ 0)
    (ht : 2 * r -
      Algebra.trace ℤ (NumberField.RingOfIntegers K) (quadraticIntegralGenerator hfin) = p * q)
    (hn : r ^ 2 -
        Algebra.trace ℤ (NumberField.RingOfIntegers K) (quadraticIntegralGenerator hfin) * r +
        Algebra.norm ℤ (quadraticIntegralGenerator hfin) = p ^ 2 * c) :
    IsIntegral ℤ
      ((algebraMap ℤ K p)⁻¹ *
        ((quadraticIntegralGenerator hfin : NumberField.RingOfIntegers K) : K) -
          (algebraMap ℤ K p)⁻¹ * algebraMap ℤ K r) := by
  let w := quadraticIntegralGenerator hfin
  let t := Algebra.trace ℤ (NumberField.RingOfIntegers K) w
  let n := Algebra.norm ℤ w
  let x : K := (algebraMap ℤ K p)⁻¹ * (w : K) -
    (algebraMap ℤ K p)⁻¹ * algebraMap ℤ K r
  refine ⟨Polynomial.X ^ 2 + Polynomial.C q * Polynomial.X + Polynomial.C c,
    by monicity <;> norm_num, ?_⟩
  have hpK : (p : K) ≠ 0 := Int.cast_ne_zero.mpr hp
  have hwO := quadratic_sq_eq_trace_mul_sub_norm hfin w
  have hw : (w : K) ^ 2 = (t : K) * (w : K) - (n : K) := by
    have := congrArg (algebraMap (NumberField.RingOfIntegers K) K) hwO
    simpa [t, n, Algebra.smul_def, ← RingOfIntegers.coe_eq_algebraMap] using this
  have htK := congrArg (fun z : ℤ ↦ (z : K)) ht
  have hnK := congrArg (fun z : ℤ ↦ (z : K)) hn
  change Polynomial.eval₂ (algebraMap ℤ K) x
    (Polynomial.X ^ 2 + Polynomial.C q * Polynomial.X + Polynomial.C c) = 0
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C]
  dsimp [x]
  field_simp
  push_cast at htK hnK
  change (2 : K) * (r : K) - (t : K) = (p : K) * (q : K) at htK
  change (r : K) ^ 2 - (t : K) * (r : K) + (n : K) =
    (p : K) ^ 2 * (c : K) at hnK
  linear_combination hw - hnK - ((w : K) - (r : K)) * htK

/-- The discriminant of every quadratic number field is a fundamental discriminant in the sense
of the alternatives in [AFK25, equation (1.33)].

A standard fact of quadratic-field theory; see the treatment of fundamental discriminants in
[21, Buchmann, Vollmer (2007), Definition 3.3.2 and Proposition 3.3.4, pp. 37–38] and the
quadratic-field construction in [22, Buell (1989), §6.2, especially Proposition 6.6,
pp. 90–92]. The proof here is self-contained. -/
theorem isFundamentalDiscriminant_numberField_discr
    (hfin : Module.finrank ℚ K = 2) :
    IsFundamentalDiscriminant (NumberField.discr K) := by
  rw [isFundamentalDiscriminant_iff_squarefree]
  let w := quadraticIntegralGenerator hfin
  let t := Algebra.trace ℤ (NumberField.RingOfIntegers K) w
  let n := Algebra.norm ℤ w
  have hdisc : NumberField.discr K = t ^ 2 - 4 * n :=
    quadratic_discr_eq_trace_sq_sub_four_norm hfin
  have htwo : ¬ IsUnit (2 : ℤ) := by
    rw [Int.isUnit_iff]
    omega
  rcases t.even_or_odd with htEven | htOdd
  · rcases htEven with ⟨s, hs⟩
    have ht : t = 2 * s := by omega
    let D := s ^ 2 - n
    have hdiscD : NumberField.discr K = 4 * D := by
      rw [hdisc, ht]
      dsimp [D]
      ring
    refine Or.inr ⟨D, ?_, ?_, hdiscD⟩
    · intro x hx
      by_cases hx0 : x = 0
      · subst x
        have hD0 : D = 0 := by simpa using hx
        exact False.elim (NumberField.discr_ne_zero K (by simp [hdiscD, hD0]))
      obtain ⟨u, hu⟩ := hx
      have hD : D = x ^ 2 * u := by
        simpa [pow_two] using hu
      have hIntegral := isIntegral_generator_sub_div_of_relations hfin x s 0 (-u) hx0
        (by change 2 * s - t = x * 0; omega) (by
          change s ^ 2 - t * s + n = x ^ 2 * -u
          rw [ht]
          have : s ^ 2 - n = x ^ 2 * u := by simpa [D] using hD
          linear_combination -this)
      exact isUnit_of_isIntegral_generator_sub_div hfin x s hx0 hIntegral
    · have hnonneg : 0 ≤ D % 4 := Int.emod_nonneg D (by norm_num)
      have hlt : D % 4 < 4 := Int.emod_lt_of_pos D (by norm_num)
      have hcases : D % 4 = 0 ∨ D % 4 = 1 ∨ D % 4 = 2 ∨ D % 4 = 3 := by omega
      rcases hcases with h0 | h1 | h2 | h3
      · exfalso
        have hdvd : (4 : ℤ) ∣ D := Int.dvd_iff_emod_eq_zero.mpr h0
        obtain ⟨u, hu⟩ := hdvd
        have hIntegral := isIntegral_generator_sub_div_of_relations hfin 2 s 0 (-u)
          (by norm_num) (by change 2 * s - t = 2 * 0; omega) (by
            change s ^ 2 - t * s + n = (2 : ℤ) ^ 2 * -u
            rw [ht]
            have hDu : D = 4 * u := by simpa [mul_comm] using hu
            dsimp [D] at hDu
            linear_combination -hDu)
        exact htwo (isUnit_of_isIntegral_generator_sub_div hfin 2 s (by norm_num) hIntegral)
      · exfalso
        have hsubmod : (D - 1) % 4 = 0 := by omega
        have hdvd : (4 : ℤ) ∣ D - 1 := Int.dvd_iff_emod_eq_zero.mpr hsubmod
        obtain ⟨u, hu⟩ := hdvd
        have hIntegral := isIntegral_generator_sub_div_of_relations hfin 2 (s + 1) 1 (-u)
          (by norm_num) (by change 2 * (s + 1) - t = 2 * 1; omega) (by
            change (s + 1) ^ 2 - t * (s + 1) + n = (2 : ℤ) ^ 2 * -u
            rw [ht]
            have hDu : D - 1 = 4 * u := by simpa [mul_comm] using hu
            dsimp [D] at hDu
            linear_combination -hDu)
        exact htwo
          (isUnit_of_isIntegral_generator_sub_div hfin 2 (s + 1) (by norm_num) hIntegral)
      · exact Or.inl h2
      · exact Or.inr h3
  · rcases htOdd with ⟨s, hs⟩
    have ht : t = 2 * s + 1 := by omega
    refine Or.inl ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨u, hu⟩ := hx
      have hxu : NumberField.discr K = x ^ 2 * u := by
        simpa [pow_two] using hu
      rcases x.even_or_odd with hxEven | hxOdd
      · rcases hxEven with ⟨k, hk⟩
        have hxk : x = 2 * k := by omega
        exfalso
        rw [hdisc, ht, hxk] at hxu
        have hcontra : 4 * (s ^ 2 + s - n) + 1 = 4 * (k ^ 2 * u) := by
          calc
            4 * (s ^ 2 + s - n) + 1 = (2 * s + 1) ^ 2 - 4 * n := by ring
            _ = (2 * k) ^ 2 * u := hxu
            _ = 4 * (k ^ 2 * u) := by ring
        omega
      · rcases hxOdd with ⟨k, hk⟩
        have hxk : x = 2 * k + 1 := by omega
        let r := (k + 1) * t
        let c := n + k * (k + 1) * u
        have htsq : t ^ 2 = 4 * n + x ^ 2 * u := by
          calc
            t ^ 2 = (t ^ 2 - 4 * n) + 4 * n := by ring
            _ = NumberField.discr K + 4 * n := by rw [hdisc]
            _ = x ^ 2 * u + 4 * n := by rw [hxu]
            _ = 4 * n + x ^ 2 * u := by ring
        have hIntegral := isIntegral_generator_sub_div_of_relations hfin x r t c
          (by
            intro hx0
            rw [hx0] at hxk
            omega)
          (by
            dsimp [r]
            rw [hxk]
            ring)
          (by
            dsimp [r, c]
            calc
              ((k + 1) * t) ^ 2 - t * ((k + 1) * t) + n =
                  k * (k + 1) * t ^ 2 + n := by ring
              _ = k * (k + 1) * (4 * n + x ^ 2 * u) + n := by rw [htsq]
              _ = x ^ 2 * (n + k * (k + 1) * u) := by rw [hxk]; ring)
        exact isUnit_of_isIntegral_generator_sub_div hfin x r
          (by
            intro hx0
            rw [hx0] at hxk
            omega) hIntegral
    · have heq : NumberField.discr K = 4 * (s ^ 2 + s - n) + 1 := by
        rw [hdisc, ht]
        ring
      rw [heq]
      omega

/-- The discriminant of a quadratic number field is never a perfect square.

This is the irreducibility half of the admissibility of the forms of discriminant `disc(K)`; it
follows from `isFundamentalDiscriminant_numberField_discr` together with the Hermite--Minkowski
bound `2 < |disc(K)|` for a nontrivial number field, which excludes the only squarefree square. -/
theorem not_isSquare_numberField_discr (hfin : Module.finrank ℚ K = 2) :
    ¬ IsSquare (NumberField.discr K) := by
  rintro ⟨m, hm⟩
  have hgt : 2 < |NumberField.discr K| :=
    NumberField.abs_discr_gt_two (by rw [hfin]; norm_num)
  rcases isFundamentalDiscriminant_iff_squarefree.mp
    (isFundamentalDiscriminant_numberField_discr (K := K) hfin) with
    ⟨hsq, -⟩ | ⟨D, hD, hD4, hDeq⟩
  · -- A squarefree square is a unit, so `disc(K) = ±1`, contradicting the Hermite bound.
    have hu : IsUnit m := hsq m ⟨1, by rw [hm]; ring⟩
    rcases Int.isUnit_iff.mp hu with rfl | rfl <;> rw [hm] at hgt <;> norm_num at hgt
  · -- `4D = m²` forces `m` even and `D` a squarefree square, hence `D = 1`, excluding `D % 4`.
    rw [hDeq] at hm
    have hmeven : ∃ k : ℤ, m = 2 * k := by
      rcases Int.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
      · exact ⟨k, by omega⟩
      · exfalso
        obtain ⟨u, hu⟩ : ∃ u : ℤ, m * m = 4 * u + 1 := ⟨k * k + k, by rw [hk]; ring⟩
        omega
    obtain ⟨k, rfl⟩ := hmeven
    have hDk : D = k * k := by nlinarith
    have hu : IsUnit k := hD k ⟨1, by rw [hDk]; ring⟩
    rcases Int.isUnit_iff.mp hu with rfl | rfl <;> rw [hDk] at hD4 <;> omega

/-! ### Integral coordinates

Because `(1, ω)` is an integral basis, every algebraic integer of `K` is `a + bω` with
`a, b ∈ ℤ`. This is the form in which `SICs.Quadratic.ConductorOneElements` uses the basis.
-/

/-- **Integral coordinates with respect to `(1, ω)`**: every algebraic integer of a quadratic
number field is `a + bω` with `a, b ∈ ℤ`, for the generator `ω = quadraticIntegralGenerator`.
This is `Basis.sum_repr` for `quadraticIntegralBasisOne` read in `K`. -/
theorem exists_int_add_mul_quadraticIntegralGenerator
    (hfin : Module.finrank ℚ K = 2) (x : NumberField.RingOfIntegers K) :
    ∃ a b : ℤ, (x : K) = (a : K) +
      (b : K) * ((quadraticIntegralGenerator hfin : NumberField.RingOfIntegers K) : K) := by
  let basis := quadraticIntegralBasisOne hfin
  refine ⟨basis.repr x 0, basis.repr x 1, ?_⟩
  have hx : x =
      basis.repr x 0 • (1 : NumberField.RingOfIntegers K) +
        basis.repr x 1 • quadraticIntegralGenerator hfin := by
    calc
      x = ∑ i, basis.repr x i • basis i := (basis.sum_repr x).symm
      _ = basis.repr x 0 • (1 : NumberField.RingOfIntegers K) +
          basis.repr x 1 • quadraticIntegralGenerator hfin := by
        simp [Fin.sum_univ_two, basis, quadraticIntegralGenerator]
  have hxK := congrArg (algebraMap (NumberField.RingOfIntegers K) K) hx
  simpa [map_zsmul, zsmul_eq_mul, ← RingOfIntegers.coe_eq_algebraMap] using hxK

end SIC
