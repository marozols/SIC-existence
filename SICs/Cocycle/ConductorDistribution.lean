/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.Analysis.SpecificLimits.Basic
import SICs.Cocycle.OrbitBoundary

/-!
# The conductor-distribution relation for an upper-triangular matrix

For upper-triangular `U = [[a,b],[0,d]]`, the period-product quotient identity and its real
boundary limit give the conductor relation over characteristic orbits.

This file proves [72, Kopp (2024), Theorem 4.46, `thm:cllr`] for an upper-triangular matrix

```text
U = [[a, b], [0, d]],   a, d > 0,   b ∈ ℤ,
```

first on the upper half plane and then, in orbit form, on the real line. Applying the
upper-triangular period-product identity [72, Kopp (2024), Proposition 4.45, `prop:utrel`] at both
`C·τ` and `τ` and dividing expresses the quotient `ϖ_r(U·(C·τ)) / ϖ_r(U·τ)` as a finite product of
quotients `ϖ_s(C·τ)/ϖ_s(τ)` over the characteristics `s = s(j,ℓ)`, `j < a`, `ℓ < d`, with
`Us - r ∈ ℤ²`. If `UC = DU`, the left side is the quotient for `D` at `U·τ`.

## Mathematical argument

The finite identity is algebraic after Proposition 4.45: both products have the same index set,
and division distributes through them. It holds for every integer `b`, so no reduction of `b`
modulo `a`, and hence no auxiliary `SL₂(ℤ)` conjugation, is needed.

The real-line relation follows by letting `τ = α + i/(n+1)` tend to an irrational fixed point
`α` of `C` with `j_C(α) > 0`. For an orbit decomposition `(R,m)` of the factor classes, the
boundary limit `tendsto_prod_sfPeriodProduct_div_orbits` sends the product of factor quotients
to `∏_{y∈R} ש^y_{C^{m(y)}}(α)`. The left quotient, along `U·τ → U·α`, tends to
`ש^r_D(U·α)` by `tendsto_sfPeriodProduct_div_total`. The relation `UC = DU` supplies the
hypotheses there: `D` fixes `U·α`, and the lower rows give `j_D(U·α) = j_C(α) > 0`.
The characteristic `r ∉ ℤ²` keeps every factor nonintegral, since
`Us(j,ℓ) - r = (-j, ℓ)`. Uniqueness of limits gives the orbit relation. When each factor lies in
`Γ_s`, its class is fixed and `m ≡ 1`, which is the form printed in Theorem 4.46:

```text
ש^r_D(U·α) = ∏_{ℓ<d} ∏_{j<a} ש^{s(j,ℓ)}_C(α).
```

No meromorphic continuation enters: the limits are taken inside `ℍ`.

The source prints the hypotheses of Theorem 4.46 as `r ∈ ℚ/ℤ` and `f ∈ ℤ`. Its `r` is a column
vector throughout, with the conclusion's product over `s ∈ ℚ²/ℤ²`, and its `G_f` is defined only
for `f ∈ ℕ`; so the declarations here take `r : Fin 2 → ℚ` and `a, d : ℕ`. The general matrix
`B ∈ G_f` is reduced to this case in `SICs.Cocycle.ConductorRelation`.

## Main declarations

- `sfUpperTriangularIndex`: the finite factor index for an upper-triangular matrix, with the
  documented `j ↦ -j` relabeling used by the project's proof of Proposition 4.45.
- `sfUpperTriangularIndex_mem_preimage`, `not_isIntegralIndex_sfUpperTriangularIndex`,
  `sfUpperTriangularIndex_eq_of_sub_integral`: every factor lies over `r`, is nonintegral when
  `r` is, and distinct factors are distinct classes.
- `sfPeriodProduct_ratio_upperTriangular`: the quotient form of Proposition 4.45.
- `flt_upperTriangular_semiconj`, `fltDenominator_eq_of_upperTriangular_semiconj`,
  `flt_upperTriangular_eq_self_of_semiconj`: the Möbius action, fixed points, and Jacobi
  denominators across `UC = DU`, over any field of characteristic zero.
- `sfModularCocycleRealTotal_eq_prod_orbits_upperTriangular`: Theorem 4.46 for `U` on the real
  line, in orbit form.

## References

- [72] G. S. Kopp, "The Shintani--Faddeev modular cocycle: Stark units from q-Pochhammer
  ratios," arXiv:2411.06763v3, Proposition 4.45 (`prop:utrel`) and Theorem 4.46 (`thm:cllr`)
- [RW26b] D. Radchenko and C. Wheeler, "Stark units for real quadratic fields and reciprocity
  laws," 4 October 2026, Appendix A, proof of Proposition 3
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### Upper-half-plane stability -/

/-- The standard vertical approach `α + i/(n+1)` to a real boundary point from the upper half
plane. It gives a concrete approach for passing period-product identities to exact real
word values by their boundary limits. -/
def sfUpperApproach (α : ℝ) (n : ℕ) : ℂ :=
  (α : ℂ) + Complex.I / (n + 1 : ℕ)

/-- Every point of `sfUpperApproach α` lies strictly in the upper half plane. -/
lemma sfUpperApproach_im_pos (α : ℝ) (n : ℕ) : 0 < (sfUpperApproach α n).im := by
  simpa [sfUpperApproach, Nat.cast_add, Nat.cast_one, div_eq_mul_inv] using
    im_ofReal_add_I_div_pos α n

/-- The vertical upper-half-plane approach converges to its real boundary point. -/
lemma tendsto_sfUpperApproach (α : ℝ) :
    Filter.Tendsto (sfUpperApproach α) Filter.atTop (nhds (α : ℂ)) := by
  change Filter.Tendsto (fun n => sfUpperApproach α n) Filter.atTop (nhds (α : ℂ))
  simpa [sfUpperApproach, Nat.cast_add, Nat.cast_one, div_eq_mul_inv] using
    tendsto_ofReal_add_I_div α

/-! ### Upper-triangular factor indices -/

/-- The factor index attached to `B = [[a,b],[0,d]]` in the project's upper-triangular
period-product identity. It is

```text
s₀ = (d(r₀-j) - b(ℓ+r₁))/(ad),   s₁ = (ℓ+r₁)/d.
```

This is [72, Kopp (2024), Proposition 4.45, `prop:utrel`]'s index after the harmless finite
relabeling `j ↦ -j (mod a)` documented at
`sfPeriodProduct_eq_prod_upperTriangular`. -/
def sfUpperTriangularIndex (r : Fin 2 → ℚ) (a d : ℕ) (b : ℤ)
    (j : Fin a) (ell : Fin d) : Fin 2 → ℚ :=
  fun i =>
    if i = 0 then
      ((d : ℚ) * (r 0 - j) - b * (ell + r 1)) / (a * d)
    else
      (ell + r 1) / d

/-! ### Upper-triangular factors over `r`

For `U = [[a,b],[0,d]]` the factor `s = s(j,ℓ)` satisfies `Us = (r₀ - j, ℓ + r₁)`, so
`Us - r = (-j, ℓ) ∈ ℤ²`: every factor lies over `r`, and an integral factor would make
`r = Us - (-j, ℓ)` integral. -/

/-- The upper-triangular factor `s(j,ℓ)` satisfies `[[a,b],[0,d]] s(j,ℓ) - r = (-j, ℓ) ∈ ℤ²`. This
is the preimage condition of [72, Kopp (2024), Theorem 4.46, `thm:cllr`], in the form consumed by
`isPreimageTransversal_upperTriangular`. -/
theorem sfUpperTriangularIndex_mem_preimage (r : Fin 2 → ℚ) {a d : ℕ} (b : ℤ) (j : Fin a)
    (ell : Fin d) : ∀ i, ∃ t : ℤ,
    (∑ k, ((!![(a : ℤ), b; 0, (d : ℤ)] : Mat(2, ℤ)) i k : ℚ) *
        sfUpperTriangularIndex r a d b j ell k) - r i = (t : ℚ) := by
  have ha : 0 < a := Fin.pos j
  have hd : 0 < d := Fin.pos ell
  have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  intro i
  fin_cases i
  · refine ⟨-(j : ℤ), ?_⟩
    simp [Fin.sum_univ_two, sfUpperTriangularIndex]
    field_simp
    ring
  · refine ⟨(ell : ℤ), ?_⟩
    simp [Fin.sum_univ_two, sfUpperTriangularIndex]
    field_simp
    ring

/-- If one upper-triangular factor is integral, then so is `r`, since
`r = [[a,b],[0,d]] s(j,ℓ) - (-j, ℓ)`. -/
theorem isIntegralIndex_of_sfUpperTriangularIndex (r : Fin 2 → ℚ) {a d : ℕ} (b : ℤ)
    (j : Fin a) (ell : Fin d) (h : IsIntegralIndex (sfUpperTriangularIndex r a d b j ell)) :
    IsIntegralIndex r := by
  obtain ⟨m₀, hm₀⟩ := h 0
  obtain ⟨m₁, hm₁⟩ := h 1
  have ha : 0 < a := Fin.pos j
  have hd : 0 < d := Fin.pos ell
  have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hm₀' : ((d : ℚ) * (r 0 - j) - b * (ell + r 1)) / (a * d) = (m₀ : ℚ) := by
    simpa [sfUpperTriangularIndex] using hm₀
  have hm₁' : (ell + r 1) / d = (m₁ : ℚ) := by
    simpa [sfUpperTriangularIndex] using hm₁
  refine isIntegralIndex_of_coords ?_ ?_
  · refine ⟨(a : ℤ) * m₀ + b * m₁ + j, ?_⟩
    rw [div_eq_iff (mul_ne_zero haQ hdQ)] at hm₀'
    rw [div_eq_iff hdQ] at hm₁'
    push_cast at hm₀' hm₁' ⊢
    apply mul_left_cancel₀ hdQ
    rw [hm₁'] at hm₀'
    linear_combination hm₀'
  · refine ⟨(d : ℤ) * m₁ - ell, ?_⟩
    rw [div_eq_iff hdQ] at hm₁'
    push_cast at hm₁' ⊢
    linarith

/-- Every upper-triangular factor of a nonintegral characteristic is nonintegral, so the
exceptional clauses of [72, Kopp (2024), Proposition 4.35, `prop:invariance`] never occur in the
upper-triangular relation. -/
theorem not_isIntegralIndex_sfUpperTriangularIndex (r : Fin 2 → ℚ) {a d : ℕ} (b : ℤ)
    (j : Fin a) (ell : Fin d) (hr : ¬ IsIntegralIndex r) :
    ¬ IsIntegralIndex (sfUpperTriangularIndex r a d b j ell) :=
  fun h => hr (isIntegralIndex_of_sfUpperTriangularIndex r b j ell h)

/-- Two finite residues whose difference is a multiple of the modulus agree. This is used by
`sfUpperTriangularIndex_eq_of_sub_integral`. -/
private theorem fin_eq_of_int_sub_eq_mul {n : ℕ} (u v : Fin n) (m : ℤ)
    (h : (u : ℤ) - v = m * n) : u = v := by
  apply Fin.ext
  apply Nat.ModEq.eq_of_lt_of_lt (Nat.modEq_iff_dvd.mpr ?_) u.isLt v.isLt
  exact ⟨-m, by
    calc
      (v : ℤ) - u = -((u : ℤ) - v) := by ring
      _ = -(m * n) := by rw [h]
      _ = (n : ℤ) * -m := by ring⟩

/-- Integral difference of two upper-triangular indices forces their finite parameters to
agree. This is the uniqueness input for the upper-triangular orbit relation and
`isPreimageTransversal_upperTriangular`. -/
theorem sfUpperTriangularIndex_eq_of_sub_integral (r : Fin 2 → ℚ) {a d : ℕ}
    (ha : 0 < a) (hd : 0 < d) (b : ℤ) (p q : Fin d × Fin a)
    (h : IsIntegralIndex
      (sfUpperTriangularIndex r a d b p.2 p.1 -
        sfUpperTriangularIndex r a d b q.2 q.1)) : p = q := by
  obtain ⟨m₁, hm₁⟩ := h 1
  have hdQ : (d : ℚ) ≠ 0 := by positivity
  simp only [Pi.sub_apply, sfUpperTriangularIndex, Fin.isValue] at hm₁
  norm_num at hm₁
  have hm₁' : (p.1 : ℚ) - q.1 = (m₁ : ℚ) * d := by
    field_simp at hm₁
    linarith
  have hell : p.1 = q.1 := fin_eq_of_int_sub_eq_mul p.1 q.1 m₁ (by
    exact_mod_cast hm₁')
  obtain ⟨m₀, hm₀⟩ := h 0
  simp only [Pi.sub_apply, sfUpperTriangularIndex, ↓reduceIte] at hm₀
  rw [hell, div_sub_div_same, div_eq_iff (by positivity : (a : ℚ) * d ≠ 0)] at hm₀
  have hm₀' : (p.2 : ℚ) - q.2 = -(m₀ : ℚ) * a := by
    have hh : (d : ℚ) * ((q.2 : ℚ) - p.2) = d * (a * m₀) := by
      convert hm₀ using 1 <;> ring
    have hc := mul_left_cancel₀ hdQ hh
    linarith
  exact Prod.ext hell (fin_eq_of_int_sub_eq_mul p.2 q.2 (-m₀) (by
    exact_mod_cast hm₀'))

/-! ### The quotient distribution identity

Proposition 4.45 is applied once to the numerator and once to the denominator. The resulting
finite products have identical index sets, so their quotient is the product of the factorwise
quotients. -/

/-- **The upper-triangular conductor-distribution quotient.** For `τ` and `A·τ` in the upper half
plane,

```text
ϖ_r((a(A·τ)+b)/d) / ϖ_r((aτ+b)/d)
  = ∏_{ℓ<d} ∏_{j<a} ϖ_{s(j,ℓ)}(A·τ) / ϖ_{s(j,ℓ)}(τ).
```

This is the quotient calculation in the proof of [72, Kopp (2024), Theorem 4.46,
`thm:cllr`], specialized to the upper-triangular representative and before taking the real
quadratic boundary value. -/
theorem sfPeriodProduct_ratio_upperTriangular (r : Fin 2 → ℚ)
    (a d : ℕ) (ha : 0 < a) (hd : 0 < d) (b : ℤ) (A : SL(2, ℤ)) (tau : ℂ)
    (htau : 0 < tau.im) :
    sfPeriodProduct r
          (((a : ℂ) * flt (A : Mat(2, ℤ)) tau + (b : ℂ)) / (d : ℂ)) /
        sfPeriodProduct r (((a : ℂ) * tau + (b : ℂ)) / (d : ℂ)) =
      ∏ ell : Fin d, ∏ j : Fin a,
        sfPeriodProduct (sfUpperTriangularIndex r a d b j ell)
              (flt (A : Mat(2, ℤ)) tau) /
            sfPeriodProduct (sfUpperTriangularIndex r a d b j ell) tau := by
  rw [sfPeriodProduct_eq_prod_upperTriangular r a d ha hd b _
      (flt_im_pos A htau),
    sfPeriodProduct_eq_prod_upperTriangular r a d ha hd b _ htau,
    ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro ell _
  rw [← Finset.prod_div_distrib]
  rfl

/-! ### The upper-triangular conjugate

For `U = [[a,b],[0,d]]` with `d ≠ 0`, `U·x = (ax + b)/d` and `j_U(x) = d` over any field
(`flt_upperTriangular`, `fltDenominator_upperTriangular`). The relation `UC = DU` gives
`D·(U·x) = U·(C·x)` by the Möbius composition law, and its lower rows, `dC₁₀ = aD₁₀` and
`dC₁₁ = bD₁₀ + dD₁₁`, give `j_D(U·x) = j_C(x)`. So `x ↦ U·x` carries fixed points of `C` to
fixed points of `D`. These are the fixed-point and domain checks implicit in
[72, Kopp (2024), Theorem 4.46, `thm:cllr`], before comparing any cocycle values.
-/

section UpperTriangularConjugate

variable {K : Type*} [Field K] [CharZero K]

/-- **Upper-triangular semiconjugation preserves Jacobi denominators**: for `U = [[a,b],[0,d]]`
with `d ≠ 0` and `UC = DU`, `j_D(U·x) = j_C(x)`, where `U·x = (ax + b)/d`. From the lower rows
`dC₁₀ = aD₁₀` and `dC₁₁ = bD₁₀ + dD₁₁` of the relation. -/
theorem fltDenominator_eq_of_upperTriangular_semiconj {C D : Mat(2, ℤ)}
    {a b d : ℤ} (hd : d ≠ 0) (hconj : !![a, b; 0, d] * C = D * !![a, b; 0, d]) (x : K) :
    fltDenominator D (((a : K) * x + b) / d) = fltDenominator C x := by
  have h10 := congrArg (fun M : Mat(2, ℤ) ↦ M 1 0) hconj
  have h11 := congrArg (fun M : Mat(2, ℤ) ↦ M 1 1) hconj
  norm_num [Matrix.mul_apply, Fin.sum_univ_two] at h10 h11
  have h10K : (d : K) * C 1 0 = D 1 0 * a := by exact_mod_cast h10
  have h11K : (d : K) * C 1 1 = D 1 0 * b + D 1 1 * d := by exact_mod_cast h11
  have hdK : (d : K) ≠ 0 := Int.cast_ne_zero.mpr hd
  simp only [fltDenominator]
  field_simp
  linear_combination -x * h10K - h11K

/-- **Upper-triangular semiconjugation**: if `UC = DU` for `U = [[a,b],[0,d]]` with `d ≠ 0` and
`j_C(x) ≠ 0`, then `D·(U·x) = U·(C·x)`, by the Möbius composition law applied to both sides of the
relation (`flt_mul`), whose denominators are `j_C(x)`, `j_U = d`, and `j_D(U·x) = j_C(x)`. -/
theorem flt_upperTriangular_semiconj {C D : Mat(2, ℤ)} {a b d : ℤ}
    (hd : d ≠ 0) (hconj : !![a, b; 0, d] * C = D * !![a, b; 0, d]) {x : K}
    (hden : fltDenominator C x ≠ 0) :
    flt D (((a : K) * x + b) / d) = ((a : K) * flt C x + b) / d := by
  have hjU (y : K) : fltDenominator !![a, b; 0, d] y ≠ 0 := by
    rw [fltDenominator_upperTriangular]
    exact_mod_cast hd
  have h := congrArg (fun M ↦ flt M x) hconj
  rw [flt_mul _ _ _ hden, flt_mul _ _ _ (hjU _),
    flt_upperTriangular, flt_upperTriangular] at h
  exact h.symm

/-- **Upper-triangular semiconjugation carries fixed points forward**: if `UC = DU` for
`U = [[a,b],[0,d]]` with `d ≠ 0`, and `C·x = x` with `j_C(x) ≠ 0`, then `D` fixes
`U·x = (ax + b)/d` (`flt_upperTriangular_semiconj`). -/
theorem flt_upperTriangular_eq_self_of_semiconj {C D : Mat(2, ℤ)} {a b d : ℤ}
    (hd : d ≠ 0) (hconj : !![a, b; 0, d] * C = D * !![a, b; 0, d]) {x : K}
    (hden : fltDenominator C x ≠ 0) (hfix : flt C x = x) :
    flt D (((a : K) * x + b) / d) = ((a : K) * x + b) / d := by
  rw [flt_upperTriangular_semiconj hd hconj hden, hfix]

end UpperTriangularConjugate

/-! ### The upper-triangular relation on the real line

The finite product identity passes to the real boundary once its left quotient and the product of
its factor quotients converge to exact word values; uniqueness of limits in `ℂ` then makes the
passage formal. Both convergences hold at an irrational fixed point with positive Jacobi
denominator and a nonintegral characteristic (`tendsto_sfPeriodProduct_div_total`,
`tendsto_prod_sfPeriodProduct_div_orbits`). Along `τ = α + i/(n+1)`, the factor
quotients converge at `α` for `C`, and the left quotient, read through `D·(U·τ) = U·(C·τ)` as
`ϖ_r(D·(U·τ))/ϖ_r(U·τ)`, converges at `U·α` for `D`, since `U·τ → U·α` inside `ℍ`, `D` fixes `U·α`,
and `j_D(U·α) = j_C(α) > 0`. -/

/-- The upper-triangular image of the standard vertical approach converges to the image of its
real endpoint. This supplies the left boundary limits in
`sfModularCocycleRealTotal_eq_prod_orbits_upperTriangular` and
`prod_sfModularCocycleReal'_orbits_preimage_zero`. -/
lemma tendsto_sfUpperTriangularApproach (a d : ℕ) (b : ℤ) (α : ℝ) :
    Filter.Tendsto
      (fun n ↦ ((a : ℂ) * sfUpperApproach α n + (b : ℂ)) / (d : ℂ))
      Filter.atTop (nhds ((((a : ℝ) * α + b) / d : ℝ) : ℂ)) := by
  have h := (((tendsto_sfUpperApproach α).const_mul (a : ℂ)).add_const (b : ℂ)).div_const
    (d : ℂ)
  norm_cast at h ⊢

/-- The upper-triangular image of every standard approach point remains in the upper half plane.
This supplies the domain conditions used by
`sfModularCocycleRealTotal_eq_prod_orbits_upperTriangular` and
`prod_sfModularCocycleReal'_orbits_preimage_zero`. -/
lemma sfUpperTriangularApproach_im_pos (a d : ℕ) (ha : 0 < a) (hd : 0 < d)
    (b : ℤ) (α : ℝ) (n : ℕ) :
    0 < (((a : ℂ) * sfUpperApproach α n + (b : ℂ)) / (d : ℂ)).im := by
  rw [show (d : ℂ) = ((d : ℝ) : ℂ) by norm_cast, Complex.div_ofReal_im]
  simp only [Complex.add_im, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
    zero_mul, add_zero, Complex.intCast_im]
  exact div_pos (mul_pos (by exact_mod_cast ha) (sfUpperApproach_im_pos α n))
    (by exact_mod_cast hd)

/-- `D·(U·τ) = U·(C·τ)` on the upper half plane, `flt_upperTriangular_semiconj` in `ℂ` with
`j_C(τ) ≠ 0` there; the composition step in
`sfModularCocycleRealTotal_eq_prod_orbits_upperTriangular` and
`prod_sfModularCocycleReal'_orbits_preimage_zero`. -/
lemma flt_upperTriangular_semiconj_complex (a d : ℕ) (hd : 0 < d) (b : ℤ)
    (C D : SL(2, ℤ))
    (hconj : !![(a : ℤ), b; 0, (d : ℤ)] * (C : Mat(2, ℤ)) =
      (D : Mat(2, ℤ)) * !![(a : ℤ), b; 0, (d : ℤ)])
    (tau : ℂ) (htau : 0 < tau.im) :
    flt (D : Mat(2, ℤ)) (((a : ℂ) * tau + b) / d) =
      ((a : ℂ) * flt (C : Mat(2, ℤ)) tau + b) / d := by
  simpa only [Int.cast_natCast] using flt_upperTriangular_semiconj
    (by exact_mod_cast hd.ne' : (d : ℤ) ≠ 0) hconj
    (fltDenominator_ne_zero_of_im_ne_zero C htau.ne')

/-- The left quotient in the upper-triangular distribution identity tends to the cocycle at
`U·α`. This is the boundary input for
`sfModularCocycleRealTotal_eq_prod_orbits_upperTriangular`. -/
private theorem tendsto_upperTriangularLeftRatio {r : Fin 2 → ℚ}
    (hr : ¬ IsIntegralIndex r) {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (b : ℤ)
    {C D : SL(2, ℤ)}
    (hconj : !![(a : ℤ), b; 0, (d : ℤ)] * (C : Mat(2, ℤ)) =
      (D : Mat(2, ℤ)) * !![(a : ℤ), b; 0, (d : ℤ)])
    (hD : D ∈ gammaSubgroup r) {α : ℝ} (hα : Irrational α)
    (hfix : flt (C : Mat(2, ℤ)) α = α)
    (hj : 0 < fltDenominator (C : Mat(2, ℤ)) α) :
    Filter.Tendsto
      (fun n => sfPeriodProduct r
          (((a : ℂ) * flt (C : Mat(2, ℤ)) (sfUpperApproach α n) + b) / d) /
        sfPeriodProduct r (((a : ℂ) * sfUpperApproach α n + b) / d))
      Filter.atTop
      (nhds (sfModularCocycleRealTotal r D hD (((a : ℝ) * α + b) / d))) := by
  have hdZ : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  have hβ : Irrational (((a : ℝ) * α + b) / d) :=
    ((hα.natCast_mul ha.ne').add_intCast b).div_natCast hd.ne'
  have hjD : 0 < fltDenominator (D : Mat(2, ℤ))
      (((a : ℝ) * α + b) / d) := by
    calc
      fltDenominator (D : Mat(2, ℤ)) (((a : ℝ) * α + b) / d) =
          fltDenominator (C : Mat(2, ℤ)) α := by
        simpa only [Int.cast_natCast] using
          fltDenominator_eq_of_upperTriangular_semiconj hdZ hconj α
      _ > 0 := hj
  have hfixD : flt (D : Mat(2, ℤ)) (((a : ℝ) * α + b) / d) =
      ((a : ℝ) * α + b) / d :=
    flt_upperTriangular_eq_self_of_semiconj hdZ hconj hj.ne' hfix
  have hleft₀ := tendsto_sfPeriodProduct_div_total
    (fun n ↦ ((a : ℂ) * sfUpperApproach α n + (b : ℂ)) / (d : ℂ))
    hD hr hβ hjD hfixD (tendsto_sfUpperTriangularApproach a d b α)
    (Filter.Eventually.of_forall (sfUpperTriangularApproach_im_pos a d ha hd b α))
  exact hleft₀.congr' (Filter.Eventually.of_forall fun n ↦ by
    rw [flt_upperTriangular_semiconj_complex a d hd b C D hconj
      (sfUpperApproach α n) (sfUpperApproach_im_pos α n)])

/-- **The upper-triangular conductor relation along characteristic orbits**: if the factors
`s(j,ℓ)` decompose into orbits of `C` with representatives `R` and lengths `m`, then

$$ש^{\mathbf r}_D(U\cdot\alpha)
  = \prod_{\mathbf y\in R} ש^{\mathbf y}_{C^{m(\mathbf y)}}(\alpha).$$

This combines the orbit telescoping of [RW26b, Radchenko, Wheeler (2026b), Appendix A, proof of
Proposition 3] with the upper-triangular quotient in [72, Kopp (2024), Theorem 4.46,
`thm:cllr`]. -/
theorem sfModularCocycleRealTotal_eq_prod_orbits_upperTriangular {r : Fin 2 → ℚ}
    (hr : ¬ IsIntegralIndex r) {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (b : ℤ) {C D : SL(2, ℤ)}
    (hconj : !![(a : ℤ), b; 0, (d : ℤ)] * (C : Mat(2, ℤ)) =
      (D : Mat(2, ℤ)) * !![(a : ℤ), b; 0, (d : ℤ)])
    (hD : D ∈ gammaSubgroup r)
    {α : ℝ} (hα : Irrational α) (hfix : flt (C : Mat(2, ℤ)) α = α)
    (hj : 0 < fltDenominator (C : Mat(2, ℤ)) α)
    {R : Finset (Fin 2 → ℚ)} {m : (Fin 2 → ℚ) → ℕ+}
    (hR : IsOrbitDecomposition C
      (Finset.univ.image fun p : Fin d × Fin a ↦ sfUpperTriangularIndex r a d b p.2 p.1)
      R m) :
    sfModularCocycleRealTotal r D hD (((a : ℝ) * α + b) / d) =
      ∏ y ∈ R, sfModularCocycleReal' y (C ^ (m y : ℕ)) α := by
  classical
  let index : Fin d × Fin a → Fin 2 → ℚ :=
    fun p => sfUpperTriangularIndex r a d b p.2 p.1
  let S := Finset.univ.image index
  have hSnot : ∀ s ∈ S, ¬ IsIntegralIndex s := by
    intro s hs
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hs
    exact not_isIntegralIndex_sfUpperTriangularIndex r b p.2 p.1 hr
  have hSinj : ∀ s ∈ S, ∀ s' ∈ S,
      IsIntegralIndex (s - s') → s = s' := by
    intro s hs s' hs' hsub
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hs'
    exact congrArg index (sfUpperTriangularIndex_eq_of_sub_integral r ha hd b p q hsub)
  have hinj : Function.Injective index := by
    intro p q hpq
    apply sfUpperTriangularIndex_eq_of_sub_integral r ha hd b p q
    simpa only [index, hpq, sub_self] using
      (show IsIntegralIndex (0 : Fin 2 → ℚ) from fun _ => ⟨0, by simp⟩)
  have hleft := tendsto_upperTriangularLeftRatio hr ha hd b hconj hD hα hfix hj
  have hprod := tendsto_prod_sfPeriodProduct_div_orbits
    (sfUpperApproach α) hα hfix hj hSnot hSinj hR
    (tendsto_sfUpperApproach α)
    (Filter.Eventually.of_forall (sfUpperApproach_im_pos α))
  apply tendsto_nhds_unique hleft
  apply hprod.congr'
  filter_upwards with n
  rw [Finset.prod_image hinj.injOn, Fintype.prod_prod_type]
  exact (sfPeriodProduct_ratio_upperTriangular r a d ha hd b C
    (sfUpperApproach α n) (sfUpperApproach_im_pos α n)).symm

end SIC

end
