/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Admissible.AssociatedStabilizers
import SICs.Cocycle.Domains

/-!
# The associated stabilizers at the plus root

The associated stabilizers fix `ρ_{Q,+}`, which lies in `D_{A_t} ∩ D_{A_t⁻¹}`, and `A_t 1 0 ≠ 0`.

For an arbitrary admissible tuple `t`, [AFK25, Definition 1.28, `dfn:AssociatedStabilizers`] fixes
the associated stabilizers by the doubled formula
```
2 L_{z,t} = (d_j - 1) I + (f_j/f) · 2SQ,      A_t = L_{z,t}^{2m+1},
```
recorded as `SIC.AdmissibleTuple.IsAssociatedStabilizerPair`. This file reads two analytic facts
straight off that formula:

- `A_t` fixes the root `ρ_{Q,+}` of [AFK25, equation (1.35), `dfn:qrtdf`] (`flt_A_rootPlus`);
- `ρ_{Q,+} ∈ D_{A_t} ∩ D_{A_t⁻¹}` (`ofReal_rootPlus_mem_sfDomain`,
  `ofReal_rootPlus_mem_sfDomain_inv`), the domain condition of
  [AFK25, Definition 1.15, `def:sl2ldmndf`] and [AFK25, Definition 1.18, `def:shin`].

The second is [AFK25]'s own claim, in [AFK25, Theorem 1.31, `thm:ghostWellDefinedCondition`] and
in the proof of [AFK25, Theorem 4.50, `tm:symgp`], where it is deduced from `Tr(A_t) > 0` through
[AFK25, Lemma 2.18, `lem:fixedinda`]. Both are needed by [AFK25, Definition
1.34, `dfn:shift`]'s convolution sum, which evaluates the Shintani--Faddeev modular cocycle at `A_t`
and `A_t⁻¹`, both at `ρ_t = ρ_{Q,+}`. The source also states the domain condition at `ρ_{Q,-}`,
which the convolution sum does not use and which is not formalized.

## Mathematical argument

The construction of `A_t` and `L_{z,t}` is in `SICs.Admissible.StabilizerExistence`; here only
the relation `IsAssociatedStabilizerPair` is used, including the sign characterization of `A_t`.
The computation runs at `L_{z,t}`, where the doubled formula gives every entry directly, and
transfers to `A_t = L_{z,t}^{2m+1}` through the Möbius cocycle laws at a fixed point
(`SICs.SL2Z.FractionalLinear.flt_pow_of_flt_eq_self` and its Jacobi-denominator companion).

The key cancellation is that `a` never survives. `L_{z,t} 1 0 = (f_j/f)·a` and
`ρ_{Q,+} = (-b + √Δ)/(2a)`, so

```
2 j_{L_{z,t}}(ρ_{Q,+}) = (f_j/f)·(2a·ρ_{Q,+}) + (d_j - 1) + (f_j/f)·b = (f_j/f)·√Δ + (d_j - 1),
```

which is positive because `f_j/f ≥ 1`, `d_j > 3` and `Δ > 0` — with no sign hypothesis on the form's
leading coefficient, which [AFK25, §1.3] does not normalize. (It is only in the continued-fraction
development of [AFK25, Appendix C] that `a > 0` is taken without loss of generality.) The
corresponding statement about `A_t 1 0` is *not* available this way, and is in fact false when
`a < 0`; that hypothesis is removed instead by `sfModularCocycleRealTotal`.

Powers preserve positivity, and inversion replaces the fixed-point denominator by its reciprocal,
so `ρ_{Q,+}` lies in both `D_{A_t}` and `D_{A_t⁻¹}`. The same identity gives
`j_{L_{z,t}}(ρ_{Q,+}) > 1`, hence `j_{A_t}(ρ_{Q,+}) > 1`, which rules out `A_t 1 0 = 0`: the
denominator would then be the integer `A_t 1 1 = ±1`.

## Main declarations

- `IsAssociatedStabilizerPair.twice_Lz_lowerLeft`, `_lowerRight`, `_upperLeft`, `_upperRight`:
  the four entries of `2 L_{z,t}` read off the doubled formula.
- `IsAssociatedStabilizerPair.twice_fltDenominator_Lz_rootPlus`: the displayed identity, and
  `fltDenominator_Lz_rootPlus_pos` its positivity.
- `IsAssociatedStabilizerPair.flt_Lz_rootPlus`, `flt_A_rootPlus`: both generators fix `ρ_{Q,+}`.
- `IsAssociatedStabilizerPair.ofReal_rootPlus_mem_sfDomain`, `ofReal_rootPlus_mem_sfDomain_inv`:
  the two domain conditions.
- `IsAssociatedStabilizerPair.lowerLeft_A_ne_zero`: `A_t 1 0 ≠ 0`, i.e. `A_t ≠ ±T^k`, from
  `one_lt_fltDenominator_A_rootPlus`.

## References

- [AFK25, Definition 1.15, `def:sl2ldmndf`] and [AFK25, Definition 1.18, `def:shin`] and [AFK25,
  Definition 1.28, `dfn:AssociatedStabilizers`, equations (1.35), `dfn:qrtdf`, (1.41)] and [AFK25,
  Lemma 2.18, `lem:fixedinda`].
-/

noncomputable section

open ModularGroup MatrixGroups

open scoped MatrixGroups

namespace SIC

namespace AdmissibleTuple

namespace IsAssociatedStabilizerPair

variable {t : AdmissibleTuple} {A_t Lz : SL(2, ℤ)}

/-! ### The entries of the Zauner generator

The four entries of `2L_{z,t}` are read directly from the associated-stabilizer equation.  Keeping
the doubled form avoids any parity division in the subsequent real calculations. -/

/-- The doubled defining formula read at a single entry. -/
private lemma entry_aux (hp : t.IsAssociatedStabilizerPair A_t Lz) (i j : Fin 2) :
    2 * (Lz : Mat(2, ℤ)) i j =
      ((t.triple.towerDimension : ℤ) - 1) * (if i = j then 1 else 0) +
        (t.towerConductorRatio : ℤ) * t.Q.twiceSQ i j := by
  have h := congrFun (congrFun hp.twice_Lz_eq i) j
  simpa only [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, smul_eq_mul] using h

/-- `2 L_{z,t}` has lower-left entry `2(f_j/f)a`, the only entry involving the form's leading
coefficient. -/
lemma twice_Lz_lowerLeft (hp : t.IsAssociatedStabilizerPair A_t Lz) :
    2 * (Lz : Mat(2, ℤ)) 1 0 = 2 * (t.towerConductorRatio : ℤ) * t.Q.a := by
  have h := hp.entry_aux 1 0
  simp only [BinaryQF.twiceSQ] at h
  norm_num at h
  linarith

/-- `2 L_{z,t}` has lower-right entry `(d_j - 1) + (f_j/f)b`. -/
lemma twice_Lz_lowerRight (hp : t.IsAssociatedStabilizerPair A_t Lz) :
    2 * (Lz : Mat(2, ℤ)) 1 1 =
      ((t.triple.towerDimension : ℤ) - 1) + (t.towerConductorRatio : ℤ) * t.Q.b := by
  have h := hp.entry_aux 1 1
  simp only [BinaryQF.twiceSQ] at h
  norm_num at h
  linarith

/-- `2 L_{z,t}` has upper-left entry `(d_j - 1) - (f_j/f)b`. -/
lemma twice_Lz_upperLeft (hp : t.IsAssociatedStabilizerPair A_t Lz) :
    2 * (Lz : Mat(2, ℤ)) 0 0 =
      ((t.triple.towerDimension : ℤ) - 1) - (t.towerConductorRatio : ℤ) * t.Q.b := by
  have h := hp.entry_aux 0 0
  simp only [BinaryQF.twiceSQ] at h
  norm_num at h
  linarith

/-- `2 L_{z,t}` has upper-right entry `-2(f_j/f)c`. -/
lemma twice_Lz_upperRight (hp : t.IsAssociatedStabilizerPair A_t Lz) :
    2 * (Lz : Mat(2, ℤ)) 0 1 = -(2 * (t.towerConductorRatio : ℤ) * t.Q.c) := by
  have h := hp.entry_aux 0 1
  simp only [BinaryQF.twiceSQ] at h
  norm_num at h
  linarith

/-! ### The Jacobi denominator at `ρ_{Q,+}`

Substituting the positive quadratic root into the lower row of `2L_{z,t}` cancels the leading
coefficient and leaves `(f_j/f)√Δ + d_j - 1`, which is strictly positive. -/

/-- **The Jacobi denominator of the Zauner generator at its own fixed point**:
`2 j_{L_{z,t}}(ρ_{Q,+}) = (f_j/f)·√Δ + (d_j - 1)`. The leading coefficient `a` cancels against the
denominator of `ρ_{Q,+}` (`BinaryQF.two_mul_a_mul_rootPlus`), so the right-hand side is free of
it — which is why no normalization of `sign(a)` is needed below. -/
lemma twice_fltDenominator_Lz_rootPlus (hp : t.IsAssociatedStabilizerPair A_t Lz) :
    2 * fltDenominator (Lz : Mat(2, ℤ)) t.Q.rootPlus =
      (t.towerConductorRatio : ℝ) * Real.sqrt t.Q.disc + ((t.triple.towerDimension : ℝ) - 1) := by
  have hr10 : 2 * ((Lz : Mat(2, ℤ)) 1 0 : ℝ) =
      2 * (t.towerConductorRatio : ℝ) * (t.Q.a : ℝ) := by exact_mod_cast hp.twice_Lz_lowerLeft
  have hr11 : 2 * ((Lz : Mat(2, ℤ)) 1 1 : ℝ) =
      ((t.triple.towerDimension : ℝ) - 1) + (t.towerConductorRatio : ℝ) * (t.Q.b : ℝ) := by
    exact_mod_cast hp.twice_Lz_lowerRight
  have hroot := t.Q.two_mul_a_mul_rootPlus t.form_admissible.a_ne_zero
  rw [fltDenominator]
  linear_combination t.Q.rootPlus * hr10 + hr11 + (t.towerConductorRatio : ℝ) * hroot

/-- **`ρ_{Q,+} ∈ D_{L_{z,t}}`**, in the real-line form `0 < j_{L_{z,t}}(ρ_{Q,+})`. Every term of
`twice_fltDenominator_Lz_rootPlus`'s right-hand side is positive: `f_j/f ≥ 1`
(`towerConductorRatio_pos`), `Δ > 0` (`BinaryQF.IsAdmissible.disc_pos`) and `d_j > 3`
(`AdmissibleTriple.three_lt_towerDimension`). -/
lemma fltDenominator_Lz_rootPlus_pos (hp : t.IsAssociatedStabilizerPair A_t Lz) :
    0 < fltDenominator (Lz : Mat(2, ℤ)) t.Q.rootPlus := by
  have hu : (0 : ℝ) < (t.towerConductorRatio : ℝ) := by exact_mod_cast t.towerConductorRatio_pos
  have hdisc : (0 : ℝ) < (t.Q.disc : ℝ) := by exact_mod_cast t.form_admissible.disc_pos
  have hsqrt : (0 : ℝ) < Real.sqrt t.Q.disc := Real.sqrt_pos.mpr hdisc
  have hdim : (3 : ℝ) < (t.triple.towerDimension : ℝ) := by
    exact_mod_cast t.triple.three_lt_towerDimension
  have h := hp.twice_fltDenominator_Lz_rootPlus
  nlinarith [mul_pos hu hsqrt]

/-! ### The fixed point

The quadratic equation for `ρ_{Q,+}` proves that `L_{z,t}` fixes it under the real Möbius action.
The power relation then transfers the fixed-point statement to `A_t`. -/

/-- **The Zauner generator fixes `ρ_{Q,+}`.** Clearing the Möbius denominator turns the claim into
`(f_j/f)·(a ρ² + b ρ + c) = 0`, which is `BinaryQF.rootPlus_satisfies_quadratic`. -/
lemma flt_Lz_rootPlus (hp : t.IsAssociatedStabilizerPair A_t Lz) :
    flt (Lz : Mat(2, ℤ)) t.Q.rootPlus = t.Q.rootPlus := by
  have hden := hp.fltDenominator_Lz_rootPlus_pos
  have hr00 : 2 * ((Lz : Mat(2, ℤ)) 0 0 : ℝ) =
      ((t.triple.towerDimension : ℝ) - 1) - (t.towerConductorRatio : ℝ) * (t.Q.b : ℝ) := by
    exact_mod_cast hp.twice_Lz_upperLeft
  have hr01 : 2 * ((Lz : Mat(2, ℤ)) 0 1 : ℝ) =
      -(2 * (t.towerConductorRatio : ℝ) * (t.Q.c : ℝ)) := by exact_mod_cast hp.twice_Lz_upperRight
  have hr10 : 2 * ((Lz : Mat(2, ℤ)) 1 0 : ℝ) =
      2 * (t.towerConductorRatio : ℝ) * (t.Q.a : ℝ) := by exact_mod_cast hp.twice_Lz_lowerLeft
  have hr11 : 2 * ((Lz : Mat(2, ℤ)) 1 1 : ℝ) =
      ((t.triple.towerDimension : ℝ) - 1) + (t.towerConductorRatio : ℝ) * (t.Q.b : ℝ) := by
    exact_mod_cast hp.twice_Lz_lowerRight
  have hq := t.Q.rootPlus_satisfies_quadratic t.form_admissible
  have hden' : (((Lz : Mat(2, ℤ)) 1 0 : ℤ) : ℝ) * t.Q.rootPlus +
      (((Lz : Mat(2, ℤ)) 1 1 : ℤ) : ℝ) ≠ 0 := hden.ne'
  rw [flt, div_eq_iff hden']
  linear_combination (t.Q.rootPlus / 2) * hr00 + (1 / 2) * hr01 -
    (t.Q.rootPlus ^ 2 / 2) * hr10 - (t.Q.rootPlus / 2) * hr11 - (t.towerConductorRatio : ℝ) * hq

/-- **The level generator fixes `ρ_{Q,+}` too**, being a power of the Zauner generator. -/
lemma flt_A_rootPlus (hp : t.IsAssociatedStabilizerPair A_t Lz) :
    flt (A_t : Mat(2, ℤ)) t.Q.rootPlus = t.Q.rootPlus := by
  rw [hp.A_eq_Lz_pow]
  exact flt_pow_of_flt_eq_self hp.fltDenominator_Lz_rootPlus_pos.ne'
    hp.flt_Lz_rootPlus _

/-! ### The domain conditions at `A_t` and `A_t⁻¹`

At the common fixed point `ρ_{Q,+}`, Jacobi denominators multiply under powers and become
reciprocal under inversion. Their positivity places `ρ_{Q,+}` in both cocycle domains required by
[AFK25, Theorem 1.31, `thm:ghostWellDefinedCondition`]. -/

/-- **The level generator's Jacobi denominator is the `(2m+1)`-st power of the Zauner generator's**,
by `SICs.SL2Z.FractionalLinear.fltDenominator_pow_of_flt_eq_self` at the common fixed
point. No entry of `A_t` is computed. -/
lemma fltDenominator_A_rootPlus (hp : t.IsAssociatedStabilizerPair A_t Lz) :
    fltDenominator (A_t : Mat(2, ℤ)) t.Q.rootPlus =
      fltDenominator (Lz : Mat(2, ℤ)) t.Q.rootPlus ^
        (2 * (t.triple.m : ℕ) + 1) := by
  rw [hp.A_eq_Lz_pow]
  exact fltDenominator_pow_of_flt_eq_self hp.fltDenominator_Lz_rootPlus_pos.ne'
    hp.flt_Lz_rootPlus _

/-- `0 < j_{A_t}(ρ_{Q,+})`. -/
lemma fltDenominator_A_rootPlus_pos (hp : t.IsAssociatedStabilizerPair A_t Lz) :
    0 < fltDenominator (A_t : Mat(2, ℤ)) t.Q.rootPlus := by
  rw [hp.fltDenominator_A_rootPlus]
  exact pow_pos hp.fltDenominator_Lz_rootPlus_pos _

/-- **`ρ_{Q,+} ∈ D_{A_t}`**, the domain condition for `sfModularCocycleReal` at exactly the matrix
and fixed point used by `AdmissibleTuple.shiftConvolutionSum`.

This is the plus-root, forward-matrix domain conclusion of [AFK25, Theorem 1.31,
`thm:ghostWellDefinedCondition`]. -/
@[source "AFK25, Theorem 1.31, p. 17, thm:ghostWellDefinedCondition (ρ_{Q,+}, A_t)"]
theorem ofReal_rootPlus_mem_sfDomain (hp : t.IsAssociatedStabilizerPair A_t Lz) :
    ((t.Q.rootPlus : ℝ) : ℂ) ∈ sfDomain (A_t : Mat(2, ℤ)) :=
  (mem_sfDomain_ofReal_iff A_t t.Q.rootPlus).mpr hp.fltDenominator_A_rootPlus_pos

/-- `0 < j_{A_t⁻¹}(ρ_{Q,+})`, since at a fixed point the two denominators are reciprocal
(`SICs.SL2Z.FractionalLinear.fltDenominator_inv_mul_self_of_flt_eq_self`). -/
lemma fltDenominator_A_inv_rootPlus_pos (hp : t.IsAssociatedStabilizerPair A_t Lz) :
    0 < fltDenominator ((A_t⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) t.Q.rootPlus := by
  have hpos := hp.fltDenominator_A_rootPlus_pos
  have h := fltDenominator_inv_mul_self_of_flt_eq_self hpos.ne' hp.flt_A_rootPlus
  nlinarith [h, hpos]

/-- `ρ_{Q,+} ∈ D_{A_t⁻¹}`, the plus-root, inverse-matrix conclusion of
[AFK25, Theorem 1.31, `thm:ghostWellDefinedCondition`]. -/
@[source "AFK25, Theorem 1.31, p. 17, thm:ghostWellDefinedCondition (ρ_{Q,+}, A_t⁻¹)"]
theorem ofReal_rootPlus_mem_sfDomain_inv (hp : t.IsAssociatedStabilizerPair A_t Lz) :
    ((t.Q.rootPlus : ℝ) : ℂ) ∈ sfDomain ((A_t⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) :=
  (mem_sfDomain_ofReal_iff A_t⁻¹ t.Q.rootPlus).mpr hp.fltDenominator_A_inv_rootPlus_pos

/-! ### The lower-left entry of `A_t` is never zero

The Jacobi denominator is not merely positive but strictly greater than `1`, which is enough to
rule out `A_t 1 0 = 0` without computing any entry of `A_t`. This excludes the case where
`sfModularCocycleRealTotal`'s two defining branches overlap, giving its inverse relation
at `A_t` by `sfModularCocycleRealTotal_inv_of_lowerLeft_ne_zero`. -/

/-- `1 < j_{L_{z,t}}(ρ_{Q,+})`: sharpening `fltDenominator_Lz_rootPlus_pos`, since
`d_j - 1 > 2` already exceeds the threshold on its own. -/
lemma one_lt_fltDenominator_Lz_rootPlus (hp : t.IsAssociatedStabilizerPair A_t Lz) :
    1 < fltDenominator (Lz : Mat(2, ℤ)) t.Q.rootPlus := by
  have hu : (1 : ℝ) ≤ (t.towerConductorRatio : ℝ) := by
    exact_mod_cast t.towerConductorRatio_pos
  have hdisc : (0 : ℝ) < (t.Q.disc : ℝ) := by exact_mod_cast t.form_admissible.disc_pos
  have hsqrt : (0 : ℝ) < Real.sqrt t.Q.disc := Real.sqrt_pos.mpr hdisc
  have hdim : (3 : ℝ) < (t.triple.towerDimension : ℝ) := by
    exact_mod_cast t.triple.three_lt_towerDimension
  have h := hp.twice_fltDenominator_Lz_rootPlus
  nlinarith

/-- `1 < j_{A_t}(ρ_{Q,+})`, a positive power of a number exceeding `1`. -/
lemma one_lt_fltDenominator_A_rootPlus (hp : t.IsAssociatedStabilizerPair A_t Lz) :
    1 < fltDenominator (A_t : Mat(2, ℤ)) t.Q.rootPlus := by
  rw [hp.fltDenominator_A_rootPlus]
  exact one_lt_pow₀ hp.one_lt_fltDenominator_Lz_rootPlus (by omega)

/-- **`A_t 1 0 ≠ 0`.** If it vanished, `j_{A_t}(ρ_{Q,+})` would collapse to the integer `A_t 1 1`,
which `det A_t = 1` pins to `±1`; but `one_lt_fltDenominator_A_rootPlus` puts it strictly above
`1`. Equivalently: `A_t` is never `±T^k`. Proved without any entry of `A_t`, so — like everything
else in this file — independent of any general construction of `A_t`. -/
lemma lowerLeft_A_ne_zero (hp : t.IsAssociatedStabilizerPair A_t Lz) :
    (A_t : Mat(2, ℤ)) 1 0 ≠ 0 := by
  intro h0
  have hone := hp.one_lt_fltDenominator_A_rootPlus
  rw [fltDenominator, h0] at hone
  push_cast at hone
  have hdet : (A_t : Mat(2, ℤ)).det = 1 := A_t.2
  rw [Matrix.det_fin_two, h0] at hdet
  have h11 : (A_t : Mat(2, ℤ)) 1 1 = 1 ∨
      (A_t : Mat(2, ℤ)) 1 1 = -1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one'
      (by linarith : (A_t : Mat(2, ℤ)) 0 0 *
        (A_t : Mat(2, ℤ)) 1 1 = 1) with ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr h
  rcases h11 with h | h <;> rw [h] at hone <;> norm_num at hone

/-- **`A_t 1 0 > 0` when the form has positive leading coefficient**: the convention `γ₂₁ > 0`
of [AFK26, Appleby, Flammia, Kopp (2026), Section 4] holds for such a form. -/
lemma lowerLeft_A_pos (hp : t.IsAssociatedStabilizerPair A_t Lz) (ha : 0 < t.Q.a) :
    0 < (A_t : Mat(2, ℤ)) 1 0 := by
  have hsign : Int.sign ((A_t : Mat(2, ℤ)) 1 0) = 1 := by
    rw [← BinaryQF.signMatrix_of_lowerLeft_ne (hp.lowerLeft_A_ne_zero), hp.A_sign]
    exact Int.sign_eq_one_of_pos ha
  exact Int.sign_eq_one_iff_pos.mp hsign

end IsAssociatedStabilizerPair

end AdmissibleTuple

end SIC
