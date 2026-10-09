/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Ghost.Origin

/-!
# Canonical Reduction Data for the Principal-Family SF Cocycle

Index identities connecting the SF argument to the double-sine arguments.

This file formalizes the raw index identities and canonical reduction data used in the
principal-family Shintani--Faddeev calculation. It also treats the direct action of `A_d⁻¹` on
integer index pairs. Since `A_d⁻¹ ≡ I (mod d)`, its reduced pair is the original canonical pair;
the only new data are the two explicit lattice shifts in [AFK25, equation (8.9)].

## Main definitions and results

- `principalZ`: the Shintani--Faddeev cocycle argument `z = (qρ_d - p)/d` at a raw pair `(p,q)`.
- `principalN`: the shifted raw index `n = p(d-1) - q`.
- `principalDoubleSineArg_step`: the general one-step algebraic identity underlying all three of
  the raw index identities.
- `principalZ_add_one_eq`, `principalZ_div_principalRoot_add_one_eq`,
  `principalZ_div_principalRoot_sq_add_one_eq`: the three identities themselves, `z+1`, `z/ρ_d+1`,
  `z/ρ_d²+1` as `principalDoubleSineArg` values.
- `nQP_principalA`: the finite shift index at `A_d`, namely
  `n_QP((p/d,q/d), A_d) = q - (d-2)p`.
- `principalN_shift_eq_mul_nQP`, `principalN_shift_eq_neg_nQP`: the uniform lattice shift in
  the reduction data, `mn-p-q = d·ℓ` with `ℓ = (d-2)p - q = -n_QP(p,q)`.
- `principalReductionJ`, `principalThirdIndex_eq_reductionJ`, `principalReductionK`,
  `principalN_sub_principalThirdIndex_eq`: the case-split half of the reduction data -- the third
  index `r = principalThirdIndex d p q` in closed form `j·d - (p+q)`, and the matching shift count
  `k = p - j` with `n - r = d·k`. This is exactly the shift count used by the
  `σ_S(z/ρ_d,ρ_d)` factor in `SICs.Principal.Cocycle.SFReduction`.
- `principalAInvIndexPair`, `principalAInvReductionM1`, `principalAInvReductionM2`: the raw
  `A_d⁻¹`-image of `(p,q)` and its two equation-(8.9) shift counts, with
  `principalAInvIndexPair_eq_reduction`: `A_d⁻¹(p,q) = (p-dm₂, q+dm₁)`.

## References

- [AFK25, Section 8, especially equation (8.9)]
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### The cocycle argument `z` and the shifted raw index `n`

The rational index `(p/d,q/d)` gives the real cocycle argument `z=(qρ_d-p)/d`. Adding one to the
three word arguments produces the raw integer coordinate reduced in the later cases.
-/

/-- The Shintani--Faddeev cocycle argument `z = (qρ_d - p)/d` at a raw index pair `(p,q)`,
the three-factor word decomposition of `σ_{A_d}`: the fractional symplectic form
`r₁τ - r₀` at `r = (p/d,q/d)`, `τ = ρ_d`. -/
def principalZ (d : ℕ) (p q : ℤ) : ℝ :=
  ((q : ℝ) * principalRoot d - (p : ℝ)) / (d : ℝ)

/-- The shifted raw index `n = p(d-1) - q`, with `m := d - 1` as in the
the principal reduction. -/
def principalN (d : ℕ) (p q : ℤ) : ℤ :=
  p * ((d : ℤ) - 1) - q

/-! ### Canonical reduction of `A_d⁻¹` on index pairs

Because `A_d⁻¹ ≡ I (mod d)`, its action preserves the canonical residue pair. The explicit
integer differences record the two lattice shifts in [AFK25, equation (8.9)].
-/

/-- The raw integer index pair `A_d⁻¹(p,q)`, with matrices acting on column vectors. This is the
pair whose cocycle argument occurs when the inverse-cocycle relation converts a canonical
`σ_{A_d⁻¹}` value into a `σ_{A_d}` value. It is the `M = A_d⁻¹` case of the general
`SIC.ratVecAction` (`SICs.SL2Z.Characteristics`), at an integer pair `(p,q)` carrying an
implicit denominator `d`. -/
def principalAInvIndexPair (d : ℕ) (p q : ℤ) : IntPhaseSpace :=
  (((principalA d)⁻¹ : SL(2, ℤ)) :
    Mat(2, ℤ)).mulVec ![p, q]

/-- The explicit polynomial coordinates of `A_d⁻¹(p,q)`, obtained from `coe_principalA` and the
standard adjugate formula for the inverse of an element of `SL₂(ℤ)`. -/
lemma principalAInvIndexPair_eq (d : ℕ) (p q : ℤ) :
    principalAInvIndexPair d p q =
      ![(1 - (d : ℤ)) * p + (d : ℤ) * ((d : ℤ) - 2) * q,
        -(d : ℤ) * ((d : ℤ) - 2) * p +
          ((d : ℤ) - 1) * ((d : ℤ) ^ 2 - 2 * d - 1) * q] := by
  rw [principalAInvIndexPair, Matrix.SpecialLinearGroup.SL2_inv_expl]
  funext i
  fin_cases i <;>
    simp [coe_principalA, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The `ρ_d`-shift `m₁` in the canonical decomposition
`z(A_d⁻¹(p,q)) = z(p,q) + m₁ρ_d + m₂`. -/
def principalAInvReductionM1 (d : ℕ) (p q : ℤ) : ℤ :=
  -((d : ℤ) - 2) * p + ((d : ℤ) ^ 2 - 3 * d + 1) * q

/-- The integer shift `m₂` in the canonical decomposition
`z(A_d⁻¹(p,q)) = z(p,q) + m₁ρ_d + m₂`. -/
def principalAInvReductionM2 (d : ℕ) (p q : ℤ) : ℤ :=
  p - ((d : ℤ) - 2) * q

/-- The raw inverse image differs from `(p,q)` by explicit multiples of `d`:
`A_d⁻¹(p,q) = (p-dm₂, q+dm₁)`. This is the coordinate form of `A_d⁻¹ ≡ I (mod d)`. -/
lemma principalAInvIndexPair_eq_reduction (d : ℕ) (p q : ℤ) :
    principalAInvIndexPair d p q =
      ![p - (d : ℤ) * principalAInvReductionM2 d p q,
        q + (d : ℤ) * principalAInvReductionM1 d p q] := by
  rw [principalAInvIndexPair_eq]
  funext i
  fin_cases i <;>
    simp [principalAInvReductionM1, principalAInvReductionM2] <;>
    ring

/-! ### The raw index identities

The quadratic equation for `ρ_d` rewrites `z/ρ_d+1` and `z/ρ_d²+1` as affine double-sine
arguments. These identities connect the three word factors with the canonical product.
-/

/-- The general one-step identity underlying the three: dividing `(aρ_d - b)/d` by `ρ_d` and
adding `1` lands on `principalDoubleSineArg d b (b(d-1) - a)`. Applying this once with
`(a,b) = (q,p)` gives the `z/ρ_d + 1` identity; applying it again with `(a,b) = (p, principalN
d p q)` gives the `z/ρ_d² + 1` identity (`principalN`'s second argument reindexes exactly as the
first application's output index). -/
lemma principalDoubleSineArg_step (d : ℕ) (hd : 3 < d) (a b : ℤ) :
    ((a : ℝ) * principalRoot d - b) / d / principalRoot d + 1 =
      principalDoubleSineArg d b (b * ((d : ℤ) - 1) - a) := by
  have hρ0 : principalRoot d ≠ 0 := ne_of_gt (principalRoot_pos d hd)
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [principalDoubleSineArg]
  push_cast
  field_simp
  linear_combination (-(b : ℝ)) * principalRoot_satisfies_quadratic d hd

/-- **First raw index identity.** `z + 1 = arg_d(q,p)`, immediate from the definitions. -/
lemma principalZ_add_one_eq (d : ℕ) (p q : ℤ) :
    principalZ d p q + 1 = principalDoubleSineArg d q p := by
  rw [principalZ, principalDoubleSineArg]
  ring

/-- **Second raw index identity.** `z/ρ_d + 1 = arg_d(p,n)`. -/
lemma principalZ_div_principalRoot_add_one_eq (d : ℕ) (hd : 3 < d) (p q : ℤ) :
    principalZ d p q / principalRoot d + 1 = principalDoubleSineArg d p (principalN d p q) := by
  rw [principalZ, principalN]
  exact principalDoubleSineArg_step d hd q p

/-- **Third raw index identity.** `z/ρ_d² + 1 = arg_d(n, mn-p)`, obtained by applying
`principalDoubleSineArg_step` a second time to the second identity's own right-hand side. -/
lemma principalZ_div_principalRoot_sq_add_one_eq (d : ℕ) (hd : 3 < d) (p q : ℤ) :
    principalZ d p q / principalRoot d ^ 2 + 1 =
      principalDoubleSineArg d (principalN d p q)
        (principalN d p q * ((d : ℤ) - 1) - p) := by
  have hstep := principalZ_div_principalRoot_add_one_eq d hd p q
  have harg : principalZ d p q / principalRoot d =
      ((p : ℝ) * principalRoot d - (principalN d p q : ℝ)) / d := by
    rw [principalDoubleSineArg] at hstep
    linarith
  rw [sq, ← div_div, harg]
  exact principalDoubleSineArg_step d hd p (principalN d p q)

/-! ### The finite shift index `n_QP` at `A_d`

The closed form of `A_d` (`coe_principalA`) gives `n_QP` explicitly at the rational point
`(p/d,q/d)`. -/

/-- **`n_QP((p/d,q/d), A_d) = q - (d-2)p`.** At the
rational point `r = (p/d,q/d)`, using `(A_d)₁₀ = d(d-2)` and `(A_d)₁₁ = 1-d`
(`coe_principalA`), `n_QP` collapses to a linear expression in `p,q,d` with no denominator. -/
lemma nQP_principalA (d : ℕ) (hd : d ≠ 0) (p q : ℤ) :
    nQP ![(p : ℚ) / d, (q : ℚ) / d] (principalA d : Mat(2, ℤ)) =
      (q : ℚ) - ((d : ℚ) - 2) * (p : ℚ) := by
  have hd' : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  rw [nQP, coe_principalA]
  simp
  field_simp
  ring

/-! ### The uniform lattice shift `ℓ`

The second raw coordinate reduces with the uniform lattice shift
`ℓ=(d-2)p-q`. This part of equation (8.9) does not depend on the case split for the third index.
-/

/-- **The `ℓ` formula, in closed algebraic form.** `mn - p - q = d·ℓ` with
`ℓ = (d-2)p - q`, independent of any case split on `p+q` — a pure consequence of `n`'s
definition, needing no reduction data at all. -/
lemma principalN_shift_eq_mul_nQP (d : ℕ) (p q : ℤ) :
    principalN d p q * ((d : ℤ) - 1) - p - q = (d : ℤ) * (((d : ℤ) - 2) * p - q) := by
  rw [principalN]
  ring

/-- **The `ℓ = -n_QP(p,q)` identification**, matching `nQP_principalA`: the shift `ℓ`
appearing in `mn-p-q = dℓ` is exactly the negative of `A_d`'s finite shift index
`n_QP((p/d,q/d), A_d)`. -/
lemma principalN_shift_eq_neg_nQP (d : ℕ) (hd : d ≠ 0) (p q : ℤ) :
    ((d : ℤ) - 2) * p - q =
      -nQP ![(p : ℚ) / d, (q : ℚ) / d] (principalA d : Mat(2, ℤ)) := by
  rw [nQP_principalA d hd p q]
  push_cast
  ring

/-! ### The reduction data, the `j`, `k`, `r` case-split half

The formula for `ℓ` determines `n_QP` in the cocycle's denominator. The third index `r`
(`principalThirdIndex`, `SICs.Principal.Ghost.DoubleSineProduct`) also has a closed form with
two cases, giving the matching shift count `k = p - j` used by the word-product reduction. -/

/-- The case index `j ∈ {1, 2}`: `j = 1` when `0 < p + q ≤ d`, `j = 2` when
`d < p + q ≤ 2(d - 1)`. -/
def principalReductionJ (d : ℕ) (p q : ℤ) : ℤ := if p + q ≤ (d : ℤ) then 1 else 2

/-- **The `r` formula.** For canonical residues `(p, q) ≠ (0, 0)`, the third index
`r = principalThirdIndex d p q` equals `j·d - (p + q)`. -/
lemma principalThirdIndex_eq_reductionJ (d : ℕ) (p q : ℤ)
    (hp0 : 0 ≤ p) (hp1 : p < (d : ℤ)) (hq0 : 0 ≤ q) (hq1 : q < (d : ℤ))
    (hne : ¬(p = 0 ∧ q = 0)) :
    principalThirdIndex d p q = principalReductionJ d p q * (d : ℤ) - (p + q) := by
  unfold principalThirdIndex principalReductionJ
  split_ifs with h
  · have heq : (-p - q : ℤ) = (1 * (d : ℤ) - (p + q)) + (d : ℤ) * (-1) := by ring
    rw [heq, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
  · have heq : (-p - q : ℤ) = (2 * (d : ℤ) - (p + q)) + (d : ℤ) * (-2) := by ring
    rw [heq, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]

/-- **The `k` formula.** `k := p - j`, so that `n - r = d·k` (`principalN_sub_
principalThirdIndex_eq` below). -/
def principalReductionK (d : ℕ) (p q : ℤ) : ℤ := p - principalReductionJ d p q

/-- `n ≡ r (mod d)` with explicit quotient `k`: `n - r = d·k`. -/
lemma principalN_sub_principalThirdIndex_eq (d : ℕ) (p q : ℤ)
    (hp0 : 0 ≤ p) (hp1 : p < (d : ℤ)) (hq0 : 0 ≤ q) (hq1 : q < (d : ℤ))
    (hne : ¬(p = 0 ∧ q = 0)) :
    principalN d p q - principalThirdIndex d p q = (d : ℤ) * principalReductionK d p q := by
  rw [principalThirdIndex_eq_reductionJ d p q hp0 hp1 hq0 hq1 hne, principalReductionK,
    principalN]
  ring

/-- The shift `ℓ = (d - 2)p - q`, named for use in the argument identities below
(equal to `principalN_shift_eq_mul_nQP`'s closed form, and to `-n_QP(p,q)` by
`principalN_shift_eq_neg_nQP`). -/
def principalReductionL (d : ℕ) (p q : ℤ) : ℤ := ((d : ℤ) - 2) * p - q

/-- `mn - p ≡ q (mod d)` with explicit quotient `ℓ`: `mn - p - q = d·ℓ`, restating
`principalN_shift_eq_mul_nQP` in terms of the named `principalReductionL`. -/
lemma principalN_shift_eq_mul_reductionL (d : ℕ) (p q : ℤ) :
    principalN d p q * ((d : ℤ) - 1) - p - q = (d : ℤ) * principalReductionL d p q :=
  principalN_shift_eq_mul_nQP d p q

/-! ### The reduced arguments `z/ρ_d` and `z/ρ_d²`

Combining the raw index identities with the canonical reduction data
(`principalReductionJ/K/L`) via the general shift lemmas above, expressing `z/ρ_d` and `z/ρ_d²`
directly in terms of the *canonical* arguments `arg_d(p,r)` and `arg_d(r,q)` plus an explicit
integer/`ρ_d` shift. This is exactly the `(base point, m₁, m₂)` decomposition that `sigmaS`'s
shift formula (`SICs.Cocycle.UpperHalfPlane`) needs as input, and is the content
the reduction to finite algebra (`SICs.Principal.Cocycle.SFReduction`) is built from. -/

/-- `z/ρ_d = (arg_d(p,r) - 1) - k`: the base point of `σ_S(z/ρ_d,ρ_d)`'s shift decomposition is
`arg_d(p,r) - 1` with shift `(m₁,m₂) = (0,-k)`. -/
lemma principalZ_div_principalRoot_eq (d : ℕ) (hd : 3 < d) (p q : ℤ)
    (hp0 : 0 ≤ p) (hp1 : p < (d : ℤ)) (hq0 : 0 ≤ q) (hq1 : q < (d : ℤ))
    (hne : ¬(p = 0 ∧ q = 0)) :
    principalZ d p q / principalRoot d =
      (principalDoubleSineArg d p (principalThirdIndex d p q) - 1) -
        (principalReductionK d p q : ℝ) := by
  have h1 := principalZ_div_principalRoot_add_one_eq d hd p q
  have hn : principalN d p q =
      principalThirdIndex d p q + (d : ℤ) * principalReductionK d p q := by
    have := principalN_sub_principalThirdIndex_eq d p q hp0 hp1 hq0 hq1 hne
    omega
  rw [hn, principalDoubleSineArg_snd_add_mul d (by omega) p (principalThirdIndex d p q)
    (principalReductionK d p q)] at h1
  linarith

/-- `z/ρ_d² = (arg_d(r,q) - 1) + k·ρ_d - ℓ`: the base point of `σ_S(z/ρ_d²,ρ_d)`'s shift
decomposition is `arg_d(r,q) - 1` with shift `(m₁,m₂) = (k,-ℓ)`. -/
lemma principalZ_div_principalRoot_sq_eq (d : ℕ) (hd : 3 < d) (p q : ℤ)
    (hp0 : 0 ≤ p) (hp1 : p < (d : ℤ)) (hq0 : 0 ≤ q) (hq1 : q < (d : ℤ))
    (hne : ¬(p = 0 ∧ q = 0)) :
    principalZ d p q / principalRoot d ^ 2 =
      (principalDoubleSineArg d (principalThirdIndex d p q) q - 1) +
        (principalReductionK d p q : ℝ) * principalRoot d - (principalReductionL d p q : ℝ) := by
  have h1 := principalZ_div_principalRoot_sq_add_one_eq d hd p q
  have hn : principalN d p q =
      principalThirdIndex d p q + (d : ℤ) * principalReductionK d p q := by
    have := principalN_sub_principalThirdIndex_eq d p q hp0 hp1 hq0 hq1 hne
    omega
  have hmnp : principalN d p q * ((d : ℤ) - 1) - p =
      q + (d : ℤ) * principalReductionL d p q := by
    have := principalN_shift_eq_mul_reductionL d p q
    omega
  rw [hmnp, hn, principalDoubleSineArg_fst_add_mul d (by omega) (principalThirdIndex d p q)
      (q + (d : ℤ) * principalReductionL d p q) (principalReductionK d p q),
    principalDoubleSineArg_snd_add_mul d (by omega) (principalThirdIndex d p q) q
      (principalReductionL d p q)] at h1
  linarith

end SIC

end
