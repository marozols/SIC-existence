/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Quantum.PhaseSpace
import SICs.Principal.Quadratic.Forms
import SICs.SpecialFunctions.DoubleSine.Identities

/-!
# The Principal Three-Factor Double-Sine Product

The double-sine argument `1+(uρ_d-v)/d`, the signed three-factor product, and its reciprocity.

This file begins the explicit-product side of the principal-form shortcut. The nonzero
normalized ghost overlaps of the principal family are built from three double-sine values whose
arguments all have the shape

`1 + (uρ_d - v)/d`

for residues `u, v`. This file defines that argument, proves that it lies strictly inside the
fundamental chamber `(0, ρ_d + 1)` of `SICs.SpecialFunctions.DoubleSine.RealIntegral` for every pair
of canonical residues, records the reflection law relating the arguments at `(u, v)` and
`(d - u, d - v)`, defines the signed three-factor product, and proves the finite boundary and
residue calculations that make the product reciprocal up to a sign. The overlap itself, its
transport to arbitrary integer indices, and its reciprocity are in `SICs.Principal.Ghost.Overlaps`.

Fixing the chamber matters for two reasons. The double sine of
`SICs.SpecialFunctions.DoubleSine.RealIntegral` is defined
by its log-integral, whose convergence is proved for positive periods and `0 < z < ω₁ + ω₂`;
if the kernel is not integrable, the Bochner integral totalizes to zero and `doubleSine`
evaluates to `1`. The bounds below put all three factors in the proved convergence chamber,
so no quasiperiodic shift is needed to evaluate them. The shift identities have their own
narrower chamber hypotheses.

## Convention

This development uses the Kurokawa--Koyama convention of
`SICs.SpecialFunctions.DoubleSine.RealIntegral`, which is the
convention of [AFK25]. The three-factor formula in [42, Flammia (2024), Zauner.jl] uses the
reciprocal convention of [84, Ponsot (2003)], whose double sine is the reciprocal of the
Kurokawa--Koyama one, so the overlap defined from the values below inverts the factors displayed
there.

## Main definitions and results

- `principalDoubleSineArg`: the argument `1 + (uρ_d - v)/d`.
- `principalDoubleSineArg_pos` and `principalDoubleSineArg_lt_root_add_one`: the chamber bounds.
- `principalDoubleSineArg_mem_Ioo`: both bounds for canonical residues.
- `principalDoubleSineArg_reflect`: the argument at `(d - u, d - v)` is the chamber reflection of
  the argument at `(u, v)`.
- `doubleSine_principalDoubleSineArg_mul_reflect`: the resulting reciprocal identity, which is the
  analytic input to the reciprocity law `ν_d(p) ν_d(-p) = 1`.
- `principalSignExp`, `principalThirdIndex`, `principalTripleDoubleSine`: the sign exponent, the
  third index `r = (-p - q) mod d`, and the signed product of three double sines.
- `doubleSine_zero_boundary_cancel`: the four boundary factors at a zero coordinate multiply to
  one.
- `negRes` and `principalTripleDoubleSine_mul_negRes`: the canonical residue of `-x`, and the
  reciprocity of the triple product up to the sign `(-1)^(s(c) + s(-c))`.
- `reciprocal_sign_even_zero_fst`, `reciprocal_sign_even_generic`: the parity of that sign
  exponent, with and without the `ξ_d` transport correction.

## References

- [AFK25] Appleby, Flammia, Kopp, arXiv:2501.03970v2, Definitions 1.30 and 1.32; equation (8.6)
- [42, Flammia (2024), Zauner.jl]
-/

noncomputable section

open Real

namespace SIC

/-! ### The double-sine argument

Each principal overlap factor uses the affine argument `1 + (uρ_d-v)/d`. The lemmas here record
its elementary algebra and positivity before analytic double-sine identities are applied.
-/

/-- The argument `1 + (uρ_d - v)/d` of the double-sine factors appearing in the principal
normalized ghost overlaps. -/
def principalDoubleSineArg (d : ℕ) (u v : ℤ) : ℝ :=
  1 + ((u : ℝ) * principalRoot d - (v : ℝ)) / (d : ℝ)

/-- The dimension is a positive real. -/
private lemma cast_dim_pos {d : ℕ} (hd : 3 < d) : (0 : ℝ) < (d : ℝ) := by
  have : 0 < d := by omega
  exact_mod_cast this

/-- The double-sine argument as a single quotient. -/
lemma principalDoubleSineArg_eq_div (d : ℕ) (hd : 3 < d) (u v : ℤ) :
    principalDoubleSineArg d u v =
      ((d : ℝ) + (u : ℝ) * principalRoot d - (v : ℝ)) / (d : ℝ) := by
  have hd0 : ((d : ℝ)) ≠ 0 := ne_of_gt (cast_dim_pos hd)
  rw [principalDoubleSineArg]
  field_simp
  ring

/-! ### Fundamental-chamber bounds

Canonical residues place the three affine arguments inside the fundamental chamber for the
double sine. These bounds justify reflection and exclude poles in the product formula.
-/

/-- The double-sine argument is positive whenever `u` is nonnegative and `v` is a residue. No
upper bound on `u` is needed. -/
lemma principalDoubleSineArg_pos (d : ℕ) (hd : 3 < d) (u v : ℤ)
    (hu : 0 ≤ u) (hv : v < (d : ℤ)) : 0 < principalDoubleSineArg d u v := by
  have hdpos := cast_dim_pos hd
  have hρ := principalRoot_pos d hd
  have huR : (0 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
  have hvR : (v : ℝ) < (d : ℝ) := by exact_mod_cast hv
  rw [principalDoubleSineArg_eq_div d hd]
  exact div_pos (by nlinarith [mul_nonneg huR hρ.le]) hdpos

/-- The double-sine argument is below the top of the fundamental chamber whenever `u` is a
residue and `v` is nonnegative. No lower bound on `u` is needed. -/
lemma principalDoubleSineArg_lt_root_add_one (d : ℕ) (hd : 3 < d) (u v : ℤ)
    (hu : u < (d : ℤ)) (hv : 0 ≤ v) :
    principalDoubleSineArg d u v < principalRoot d + 1 := by
  have hdpos := cast_dim_pos hd
  have hρ := principalRoot_pos d hd
  have huR : (u : ℝ) < (d : ℝ) := by exact_mod_cast hu
  have hvR : (0 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv
  have key : ((u : ℝ) * principalRoot d - (v : ℝ)) / (d : ℝ) < principalRoot d := by
    rw [div_lt_iff₀ hdpos]
    nlinarith [mul_pos (sub_pos.mpr huR) hρ]
  rw [principalDoubleSineArg]
  linarith

/-- For canonical residues `u, v ∈ {0, …, d - 1}`, the double-sine argument lies strictly inside
the fundamental chamber `(0, ρ_d + 1)`, so the principal overlaps avoid the poles and need no
quasiperiodic shift. -/
lemma principalDoubleSineArg_mem_Ioo (d : ℕ) (hd : 3 < d) (u v : ℤ)
    (hu : 0 ≤ u) (hu' : u < (d : ℤ)) (hv : 0 ≤ v) (hv' : v < (d : ℤ)) :
    principalDoubleSineArg d u v ∈ Set.Ioo 0 (principalRoot d + 1) :=
  ⟨principalDoubleSineArg_pos d hd u v hu hv',
    principalDoubleSineArg_lt_root_add_one d hd u v hu' hv⟩

/-! ### Reflection

The quadratic equation for `ρ_d` pairs complementary affine arguments. The double-sine reflection
formula then turns their product into one, which is the analytic core of reciprocity.
-/

/-- Negating a residue pair reflects the double-sine argument in the fundamental chamber:
`arg(d - u, d - v) = ρ_d + 1 - arg(u, v)`. -/
lemma principalDoubleSineArg_reflect (d : ℕ) (hd : 3 < d) (u v : ℤ) :
    principalDoubleSineArg d ((d : ℤ) - u) ((d : ℤ) - v) =
      principalRoot d + 1 - principalDoubleSineArg d u v := by
  have hd0 : ((d : ℝ)) ≠ 0 := ne_of_gt (cast_dim_pos hd)
  rw [principalDoubleSineArg, principalDoubleSineArg]
  push_cast
  field_simp
  ring

/-- The double-sine products at an integer pair and its negation are reciprocal. This supplies the
analytic step in `principalNormGhostOverlap_reciprocal_canon`; no residue or chamber hypothesis is
needed because `doubleSine_mul_reflect` is unconditional. -/
lemma doubleSine_principalDoubleSineArg_mul_reflect (d : ℕ) (hd : 3 < d) (u v : ℤ) :
    doubleSine' (principalDoubleSineArg d ((d : ℤ) - u) ((d : ℤ) - v)) (principalRoot d) *
        doubleSine' (principalDoubleSineArg d u v) (principalRoot d) = 1 := by
  rw [principalDoubleSineArg_reflect d hd]
  exact doubleSine_mul_reflect _ (principalRoot d) 1

/-- Every principal double-sine factor is strictly positive, hence nonzero. -/
lemma doubleSine_principalDoubleSineArg_pos (d : ℕ) (u v : ℤ) :
    0 < doubleSine' (principalDoubleSineArg d u v) (principalRoot d) :=
  doubleSine_pos _ _ _

/-! ### The canonical three-factor product

The formula below is the one implemented by `_triple_double_sine` in
[42, Flammia (2024), Zauner.jl],
transposed to the Kurokawa--Koyama convention. Because `Zauner.jl` evaluates the reciprocal
Shintani double sine, the three factors appear here inverted.

This is a *canonical-representative* formula: the `min (d, p + q)` term in the sign exponent
presumes `0 ≤ p, q < d`, and [42, Flammia (2024), Zauner.jl] calls it only on canonical residues.
The integer-indexed overlap is built from it below by transport, not by reducing indices.
-/

/-- The sign exponent `d(p + q) + pq + min(d, p + q)` of the principal three-factor product,
as implemented by [42, Flammia (2024), Zauner.jl]. It is intended for canonical residues
`0 ≤ p, q < d`. -/
def principalSignExp (d : ℕ) (p q : ℤ) : ℤ :=
  (d : ℤ) * (p + q) + p * q + min (d : ℤ) (p + q)

/-- The third index `r = (-p - q) mod d` of the principal three-factor product. -/
def principalThirdIndex (d : ℕ) (p q : ℤ) : ℤ :=
  (-p - q) % (d : ℤ)

/-- The signed product of three double sines giving the principal normalized ghost overlap at a
canonical residue pair:

`(-1)^(d(p+q) + pq + min(d,p+q)) · (S₂(arg(q,p)) S₂(arg(p,r)) S₂(arg(r,q)))⁻¹`

with `r = (-p - q) mod d`. The inversion is the Kurokawa--Koyama-to-Ponsot conversion; see the
module header. -/
def principalTripleDoubleSine (d : ℕ) (p q : ℤ) : ℝ :=
  (-1 : ℝ) ^ principalSignExp d p q *
    (doubleSine' (principalDoubleSineArg d q p) (principalRoot d) *
      doubleSine' (principalDoubleSineArg d p (principalThirdIndex d p q)) (principalRoot d) *
      doubleSine' (principalDoubleSineArg d (principalThirdIndex d p q) q)
        (principalRoot d))⁻¹

/-- The three-factor product is nonzero, since every double-sine factor is positive. -/
lemma principalTripleDoubleSine_ne_zero (d : ℕ) (p q : ℤ) :
    principalTripleDoubleSine d p q ≠ 0 := by
  rw [principalTripleDoubleSine]
  refine mul_ne_zero (zpow_ne_zero _ (by norm_num)) (inv_ne_zero ?_)
  exact ne_of_gt (mul_pos (mul_pos (doubleSine_principalDoubleSineArg_pos d q p)
    (doubleSine_principalDoubleSineArg_pos d p _))
    (doubleSine_principalDoubleSineArg_pos d _ q))

/-! ### Boundary-crossing shifts

Adding `d·k` to either coordinate changes `principalDoubleSineArg` by the corresponding integer
number of periods. The single-step cases relate a zero coordinate to the full residue `d`;
the general identities also supply the argument shifts used in canonical cocycle reduction. -/

/-- Shifting the first coordinate by `d·k` shifts the argument by `k` full `ρ_d`-periods. -/
lemma principalDoubleSineArg_fst_add_mul (d : ℕ) (hd : d ≠ 0) (u v k : ℤ) :
    principalDoubleSineArg d (u + (d : ℤ) * k) v =
      principalDoubleSineArg d u v + (k : ℝ) * principalRoot d := by
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  rw [principalDoubleSineArg, principalDoubleSineArg]
  push_cast
  field_simp
  ring

/-- Shifting the second coordinate by `d·k` shifts the argument down by `k` full `1`-periods. -/
lemma principalDoubleSineArg_snd_add_mul (d : ℕ) (hd : d ≠ 0) (u v k : ℤ) :
    principalDoubleSineArg d u (v + (d : ℤ) * k) =
      principalDoubleSineArg d u v - (k : ℝ) := by
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  rw [principalDoubleSineArg, principalDoubleSineArg]
  push_cast
  field_simp
  ring

/-- Shifting the first coordinate by `d` shifts the argument by a full `ρ_d`-period. -/
private lemma principalDoubleSineArg_fst_shift_d (d : ℕ) (hd : 3 < d) (v : ℤ) :
    principalDoubleSineArg d (d : ℤ) v = principalDoubleSineArg d 0 v + principalRoot d := by
  simpa using principalDoubleSineArg_fst_add_mul d (by omega) 0 v 1

/-- Shifting the second coordinate by `d` shifts the argument down by a full `1`-period. -/
private lemma principalDoubleSineArg_snd_shift_d (d : ℕ) (hd : 3 < d) (u : ℤ) :
    principalDoubleSineArg d u (d : ℤ) + 1 = principalDoubleSineArg d u 0 := by
  have h := principalDoubleSineArg_snd_add_mul d (by omega) u 0 1
  simpa using (eq_sub_iff_add_eq.mp h)

/-! ### The four-term boundary sine cancellation

The key analytic lemma making the reciprocal identity provable without the SF/zeta machinery: the
two `2 sin(πz)`-type correction factors produced by crossing a zero coordinate cancel exactly
against each other. -/

/-- For `0 < x < d`, the four double-sine factors at `(0, x)`, `(0, d - x)`, `(x, 0)`, `(d - x, 0)`
multiply to exactly `1`.

An elementary consequence of two known identities, applied twice each. Writing `B = x/d` and
`y = xρ_d/d`, with periods `(ω₁, ω₂) = (ρ_d, 1)`, the four arguments are `ω₂ - B`, `B`, `y + ω₂`
and `ω₁ + ω₂ - y`. Reflection (`doubleSine_mul_reflect` from
`SICs.SpecialFunctions.DoubleSine.Identities`)
and the two quasiperiodicity directions ([AFK25, equations (D.5),
`eq:doubleSineQuasiPeriodicity1`, and (D.6), `eq:doubleSineQuasiPeriodicity2`],
`doubleSine'_quasiperiod_one`/`_tau`) give `S₂(ω₂ - B)·S₂(B) = 2 sin(πx/d)` and
`S₂(y + ω₂)·S₂(ω₁ + ω₂ - y) = (2 sin(πx/d))⁻¹`, and the two sine factors cancel. -/
lemma doubleSine_zero_boundary_cancel (d : ℕ) (hd : 3 < d) (x : ℤ) (hx0 : 0 < x)
    (hxd : x < (d : ℤ)) :
    doubleSine' (principalDoubleSineArg d 0 x) (principalRoot d) *
        doubleSine' (principalDoubleSineArg d 0 ((d : ℤ) - x)) (principalRoot d) *
        doubleSine' (principalDoubleSineArg d x 0) (principalRoot d) *
        doubleSine' (principalDoubleSineArg d ((d : ℤ) - x) 0) (principalRoot d) = 1 := by
  have hdpos := cast_dim_pos hd
  have hd0 : (d : ℝ) ≠ 0 := ne_of_gt hdpos
  have hρ := principalRoot_pos d hd
  have hρ0 : principalRoot d ≠ 0 := ne_of_gt hρ
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx0
  have hxdR : (x : ℝ) < (d : ℝ) := by exact_mod_cast hxd
  -- The closed forms of the two shifted arguments.
  have hz1' : principalDoubleSineArg d 0 ((d : ℤ) - x) = (x : ℝ) / d := by
    rw [principalDoubleSineArg_eq_div d hd]; push_cast; ring
  have hz2' : principalDoubleSineArg d ((d : ℤ) - x) (d : ℤ) =
      ((d : ℝ) - x) * principalRoot d / d := by
    rw [principalDoubleSineArg_eq_div d hd]; push_cast; ring
  have hz1pos : 0 < principalDoubleSineArg d 0 ((d : ℤ) - x) := by rw [hz1']; positivity
  have hz1lt : principalDoubleSineArg d 0 ((d : ℤ) - x) < 1 := by
    rw [hz1', div_lt_one hdpos]; exact hxdR
  have hz2pos : 0 < principalDoubleSineArg d ((d : ℤ) - x) (d : ℤ) := by
    rw [hz2']; exact div_pos (mul_pos (by linarith) hρ) hdpos
  have hz2lt : principalDoubleSineArg d ((d : ℤ) - x) (d : ℤ) < principalRoot d := by
    rw [hz2', div_lt_iff₀ hdpos]; nlinarith
  -- The single sine value governing both boundary crossings.
  have hspos : 0 < sin (π * (x : ℝ) / d) := by
    apply sin_pos_of_pos_of_lt_pi
    · positivity
    · rw [div_lt_iff₀ hdpos]; exact mul_lt_mul_of_pos_left hxdR pi_pos
  have hs0 : sin (π * (x : ℝ) / d) ≠ 0 := ne_of_gt hspos
  have h2s0 : (2 : ℝ) * sin (π * (x : ℝ) / d) ≠ 0 := by positivity
  have hsin1 : sin (π * principalDoubleSineArg d 0 ((d : ℤ) - x)) = sin (π * (x : ℝ) / d) := by
    rw [hz1']; congr 1; ring
  have hsin2 : sin (π * principalDoubleSineArg d ((d : ℤ) - x) (d : ℤ) / principalRoot d) =
      sin (π * (x : ℝ) / d) := by
    rw [hz2', show π * (((d : ℝ) - x) * principalRoot d / d) / principalRoot d =
        π - π * (x : ℝ) / d from by field_simp, sin_pi_sub]
  -- Reflection and quasiperiodicity.
  have hrefl1 := doubleSine_principalDoubleSineArg_mul_reflect d hd 0 x
  have hrefl2 := doubleSine_principalDoubleSineArg_mul_reflect d hd x 0
  simp only [sub_zero] at hrefl1 hrefl2
  have hq1 := doubleSine'_quasiperiod_tau (principalDoubleSineArg d 0 ((d : ℤ) - x))
    (principalRoot d) hρ hz1pos hz1lt
  rw [← principalDoubleSineArg_fst_shift_d d hd, hsin1] at hq1
  have hq2 := doubleSine'_quasiperiod_one (principalDoubleSineArg d ((d : ℤ) - x) (d : ℤ))
    (principalRoot d) hρ hz2pos hz2lt
  rw [principalDoubleSineArg_snd_shift_d d hd, hsin2] at hq2
  have hq2' : doubleSine' (principalDoubleSineArg d ((d : ℤ) - x) 0) (principalRoot d) *
      (2 * sin (π * (x : ℝ) / d)) =
      doubleSine' (principalDoubleSineArg d ((d : ℤ) - x) (d : ℤ)) (principalRoot d) :=
    (eq_div_iff h2s0).mp hq2
  -- Combine: `S(0,x) S(0,d-x) = 2 sin` and `S(x,0) S(d-x,0) = (2 sin)⁻¹`.
  rw [hq1] at hrefl1
  rw [← hq2'] at hrefl2
  have hab : doubleSine' (principalDoubleSineArg d 0 x) (principalRoot d) *
      doubleSine' (principalDoubleSineArg d 0 ((d : ℤ) - x)) (principalRoot d) =
      2 * sin (π * (x : ℝ) / d) := by
    field_simp at hrefl1
    linear_combination hrefl1
  have hce : doubleSine' (principalDoubleSineArg d x 0) (principalRoot d) *
      doubleSine' (principalDoubleSineArg d ((d : ℤ) - x) 0) (principalRoot d) =
      (2 * sin (π * (x : ℝ) / d))⁻¹ := by
    rw [eq_comm, inv_eq_one_div, div_eq_iff h2s0]
    linear_combination -hrefl2
  calc doubleSine' (principalDoubleSineArg d 0 x) (principalRoot d) *
        doubleSine' (principalDoubleSineArg d 0 ((d : ℤ) - x)) (principalRoot d) *
        doubleSine' (principalDoubleSineArg d x 0) (principalRoot d) *
        doubleSine' (principalDoubleSineArg d ((d : ℤ) - x) 0) (principalRoot d)
      = (doubleSine' (principalDoubleSineArg d 0 x) (principalRoot d) *
          doubleSine' (principalDoubleSineArg d 0 ((d : ℤ) - x)) (principalRoot d)) *
        (doubleSine' (principalDoubleSineArg d x 0) (principalRoot d) *
          doubleSine' (principalDoubleSineArg d ((d : ℤ) - x) 0) (principalRoot d)) := by ring
    _ = 2 * sin (π * (x : ℝ) / d) * (2 * sin (π * (x : ℝ) / d))⁻¹ := by rw [hab, hce]
    _ = 1 := by field_simp

/-! ### Negating the product indices

The shared canonical negation `negRes` organizes the factor-by-factor comparison between
`p` and `-p`. -/



/-- Base fact: any integer is congruent to its own residue. -/
private lemma modEq_emod_self (d : ℕ) (y : ℤ) : Int.ModEq (d : ℤ) (y % (d : ℤ)) y :=
  Int.emod_emod_of_dvd _ dvd_rfl


/-- Negation commutes with `principalThirdIndex` on canonical residues. -/
private lemma principalThirdIndex_negRes (d : ℕ) (c0 c1 : ℤ) :
    principalThirdIndex d (negRes d c0) (negRes d c1) =
      negRes d (principalThirdIndex d c0 c1) := by
  change Int.ModEq (d : ℤ) (-(negRes d c0) - negRes d c1) (-(principalThirdIndex d c0 c1))
  unfold principalThirdIndex negRes
  have h0 := modEq_emod_self d (-c0)
  have h1 := modEq_emod_self d (-c1)
  have h2 := modEq_emod_self d (-c0 - c1)
  have step1 := (h0.neg).sub h1
  have step2 := h2.neg
  have e1 : (-(-c0) - -c1 : ℤ) = c0 + c1 := by ring
  have e2 : (-(-c0 - c1) : ℤ) = c0 + c1 := by ring
  rw [e1] at step1
  rw [e2] at step2
  exact step1.trans step2.symm

/-- The six double-sine factors making up `principalTripleDoubleSine d c0 c1` and its negated
partner always multiply to `1`, for any canonical residue pair other than `(0, 0)`. Every case
(one, the other, or neither of `c0, c1` a zero coordinate) reduces to the unconditional reflection
identity together with `doubleSine_zero_boundary_cancel`; the `2 sin(πz)` correction factors from
crossing a zero coordinate always cancel exactly. This is the analytic heart of the reciprocal
identity, and it is genuinely more than the reflection identity alone. -/
private lemma sixFactor_eq_one (d : ℕ) (hd : 3 < d) (c0 c1 : ℤ)
    (hc0 : 0 ≤ c0) (hc0' : c0 < (d : ℤ)) (hc1 : 0 ≤ c1) (hc1' : c1 < (d : ℤ))
    (hne : ¬ (c0 = 0 ∧ c1 = 0)) :
    doubleSine' (principalDoubleSineArg d c1 c0) (principalRoot d) *
        doubleSine' (principalDoubleSineArg d c0 (principalThirdIndex d c0 c1))
          (principalRoot d) *
        doubleSine' (principalDoubleSineArg d (principalThirdIndex d c0 c1) c1)
          (principalRoot d) *
      (doubleSine' (principalDoubleSineArg d (negRes d c1) (negRes d c0)) (principalRoot d) *
          doubleSine' (principalDoubleSineArg d (negRes d c0)
            (negRes d (principalThirdIndex d c0 c1))) (principalRoot d) *
          doubleSine' (principalDoubleSineArg d (negRes d (principalThirdIndex d c0 c1))
            (negRes d c1)) (principalRoot d)) = 1 := by
  set r0 := principalThirdIndex d c0 c1 with hr0_def
  have hr0nn : 0 ≤ r0 := Int.emod_nonneg _ (by exact_mod_cast (by omega : d ≠ 0))
  have hr0lt : r0 < (d : ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast (by omega : 0 < d))
  rcases eq_or_ne c0 0 with hc0z | hc0nz
  · -- Case P: c0 = 0, so c1 ≠ 0.
    have hc1nz : c1 ≠ 0 := fun h ↦ hne ⟨hc0z, h⟩
    have hc1pos : 0 < c1 := lt_of_le_of_ne hc1 (Ne.symm hc1nz)
    have hr0eq : r0 = (d : ℤ) - c1 := by
      rw [hr0_def, hc0z]
      unfold principalThirdIndex
      rw [show -(0 : ℤ) - c1 = -c1 from by ring]
      exact negRes_eq_sub c1 hc1pos hc1'
    have hnc0 : negRes d c0 = 0 := by rw [hc0z, negRes_zero]
    have hnc1 : negRes d c1 = r0 := by rw [hr0eq]; exact negRes_eq_sub c1 hc1pos hc1'
    have hnr0 : negRes d r0 = c1 := by
      rw [hr0eq, negRes_eq_sub ((d : ℤ) - c1) (by linarith) (by linarith)]; ring
    rw [hnc0, hnc1, hnr0, hc0z]
    have hpair : doubleSine' (principalDoubleSineArg d r0 c1) (principalRoot d) *
        doubleSine' (principalDoubleSineArg d c1 r0) (principalRoot d) = 1 := by
      have := doubleSine_principalDoubleSineArg_mul_reflect d hd c1 r0
      rwa [show (d : ℤ) - c1 = r0 from hr0eq.symm,
        show (d : ℤ) - r0 = c1 from by rw [hr0eq]; ring] at this
    have hbc := doubleSine_zero_boundary_cancel d hd c1 hc1pos hc1'
    rw [← hr0eq] at hbc
    linear_combination (doubleSine' (principalDoubleSineArg d r0 c1) (principalRoot d) *
        doubleSine' (principalDoubleSineArg d c1 r0) (principalRoot d)) * hbc + hpair
  · rcases eq_or_ne c1 0 with hc1z | hc1nz
    · -- Case Q: c1 = 0, so c0 ≠ 0.
      have hc0pos : 0 < c0 := lt_of_le_of_ne hc0 (Ne.symm hc0nz)
      have hr0eq : r0 = (d : ℤ) - c0 := by
        rw [hr0_def, hc1z]
        unfold principalThirdIndex
        rw [show -c0 - (0 : ℤ) = -c0 from by ring]
        exact negRes_eq_sub c0 hc0pos hc0'
      have hnc1 : negRes d c1 = 0 := by rw [hc1z, negRes_zero]
      have hnc0 : negRes d c0 = r0 := by rw [hr0eq]; exact negRes_eq_sub c0 hc0pos hc0'
      have hnr0 : negRes d r0 = c0 := by
        rw [hr0eq, negRes_eq_sub ((d : ℤ) - c0) (by linarith) (by linarith)]; ring
      rw [hnc1, hnc0, hnr0, hc1z]
      have hpair : doubleSine' (principalDoubleSineArg d c0 r0) (principalRoot d) *
          doubleSine' (principalDoubleSineArg d r0 c0) (principalRoot d) = 1 := by
        have h := doubleSine_principalDoubleSineArg_mul_reflect d hd c0 r0
        rw [show (d : ℤ) - c0 = r0 from hr0eq.symm,
          show (d : ℤ) - r0 = c0 from by rw [hr0eq]; ring] at h
        linear_combination h
      have hbc := doubleSine_zero_boundary_cancel d hd c0 hc0pos hc0'
      rw [← hr0eq] at hbc
      linear_combination (doubleSine' (principalDoubleSineArg d c0 r0) (principalRoot d) *
          doubleSine' (principalDoubleSineArg d r0 c0) (principalRoot d)) * hbc + hpair
    · -- Both c0, c1 ≠ 0. Split further on whether r0 = 0.
      have hc0pos : 0 < c0 := lt_of_le_of_ne hc0 (Ne.symm hc0nz)
      have hc1pos : 0 < c1 := lt_of_le_of_ne hc1 (Ne.symm hc1nz)
      rcases eq_or_ne r0 0 with hr0z | hr0nz
      · -- Case R: r0 = 0, so c0 + c1 = d.
        have hsum : c0 + c1 = (d : ℤ) := by
          have h0 : (d : ℤ) ∣ (-c0 - c1) := Int.dvd_of_emod_eq_zero hr0z
          rw [show (-c0 - c1 : ℤ) = -(c0 + c1) from by ring] at h0
          have hdvd : (d : ℤ) ∣ (c0 + c1) := dvd_neg.mp h0
          rcases hdvd with ⟨k, hk⟩
          have hk1 : k = 1 := by nlinarith
          rw [hk1, mul_one] at hk; linarith
        have hnc0 : negRes d c0 = c1 := by
          rw [negRes_eq_sub c0 hc0pos hc0']; linarith
        have hnc1 : negRes d c1 = c0 := by
          rw [negRes_eq_sub c1 hc1pos hc1']; linarith
        have hnr0 : negRes d r0 = 0 := by rw [hr0z, negRes_zero]
        rw [hnc0, hnc1, hnr0, hr0z]
        have hpair : doubleSine' (principalDoubleSineArg d c1 c0) (principalRoot d) *
            doubleSine' (principalDoubleSineArg d c0 c1) (principalRoot d) = 1 := by
          have h := doubleSine_principalDoubleSineArg_mul_reflect d hd c1 c0
          rw [show (d : ℤ) - c1 = c0 from by linarith,
            show (d : ℤ) - c0 = c1 from by linarith] at h
          linear_combination h
        have hbc := doubleSine_zero_boundary_cancel d hd c0 hc0pos hc0'
        rw [show (d : ℤ) - c0 = c1 from by linarith] at hbc
        linear_combination (doubleSine' (principalDoubleSineArg d c1 c0) (principalRoot d) *
            doubleSine' (principalDoubleSineArg d c0 c1) (principalRoot d)) * hbc + hpair
      · -- Generic case: c0, c1, r0 all nonzero.
        have hr0pos : 0 < r0 := lt_of_le_of_ne hr0nn (Ne.symm hr0nz)
        have hnc0 : negRes d c0 = (d : ℤ) - c0 := negRes_eq_sub c0 hc0pos hc0'
        have hnc1 : negRes d c1 = (d : ℤ) - c1 := negRes_eq_sub c1 hc1pos hc1'
        have hnr0 : negRes d r0 = (d : ℤ) - r0 := negRes_eq_sub r0 hr0pos hr0lt
        rw [hnc0, hnc1, hnr0]
        have h1 := doubleSine_principalDoubleSineArg_mul_reflect d hd c1 c0
        have h2 := doubleSine_principalDoubleSineArg_mul_reflect d hd c0 r0
        have h3 := doubleSine_principalDoubleSineArg_mul_reflect d hd r0 c1
        linear_combination
          (doubleSine' (principalDoubleSineArg d c0 r0) (principalRoot d) *
              doubleSine' (principalDoubleSineArg d r0 c1) (principalRoot d) *
              doubleSine' (principalDoubleSineArg d ((d : ℤ) - c0) ((d : ℤ) - r0))
                (principalRoot d) *
              doubleSine' (principalDoubleSineArg d ((d : ℤ) - r0) ((d : ℤ) - c1))
                (principalRoot d)) * h1 +
            (doubleSine' (principalDoubleSineArg d r0 c1) (principalRoot d) *
              doubleSine' (principalDoubleSineArg d ((d : ℤ) - r0) ((d : ℤ) - c1))
                (principalRoot d)) * h2 +
            h3

/-- **The reciprocal identity for the canonical triple product.** For any canonical residue pair
other than `(0, 0)`, `principalTripleDoubleSine` at `(c0, c1)` and at its negation multiply to a
sign, given by the sum of the two sign exponents. Combined with `sixFactor_eq_one`, no cocycle or
zeta-value machinery is needed: the only remaining content is the parity of the sign exponent. -/
lemma principalTripleDoubleSine_mul_negRes (d : ℕ) (hd : 3 < d) (c0 c1 : ℤ)
    (hc0 : 0 ≤ c0) (hc0' : c0 < (d : ℤ)) (hc1 : 0 ≤ c1) (hc1' : c1 < (d : ℤ))
    (hne : ¬ (c0 = 0 ∧ c1 = 0)) :
    principalTripleDoubleSine d c0 c1 * principalTripleDoubleSine d (negRes d c0) (negRes d c1) =
      (-1 : ℝ) ^ (principalSignExp d c0 c1 + principalSignExp d (negRes d c0) (negRes d c1)) := by
  have hsix := sixFactor_eq_one d hd c0 c1 hc0 hc0' hc1 hc1' hne
  rw [principalTripleDoubleSine, principalTripleDoubleSine, principalThirdIndex_negRes d c0 c1]
  set A := doubleSine' (principalDoubleSineArg d c1 c0) (principalRoot d) *
      doubleSine' (principalDoubleSineArg d c0 (principalThirdIndex d c0 c1)) (principalRoot d) *
      doubleSine' (principalDoubleSineArg d (principalThirdIndex d c0 c1) c1)
        (principalRoot d) with hA
  set B := doubleSine' (principalDoubleSineArg d (negRes d c1) (negRes d c0)) (principalRoot d) *
      doubleSine' (principalDoubleSineArg d (negRes d c0)
        (negRes d (principalThirdIndex d c0 c1))) (principalRoot d) *
      doubleSine' (principalDoubleSineArg d (negRes d (principalThirdIndex d c0 c1))
        (negRes d c1)) (principalRoot d) with hB
  have hinv : A⁻¹ * B⁻¹ = 1 := by rw [← mul_inv, hsix, inv_one]
  rw [zpow_add₀ (show (-1 : ℝ) ≠ 0 by norm_num)]
  linear_combination ((-1 : ℝ) ^ principalSignExp d c0 c1 *
    (-1 : ℝ) ^ principalSignExp d (negRes d c0) (negRes d c1)) * hinv

/-! ### The sign-exponent parity

After `sixFactor_eq_one` and `principalTripleDoubleSine_mul_negRes`, reciprocity reduces to a
finite integer-parity computation on `principalSignExp`: the transport sign contributed by `ξ_d`
and the sign contributed by the triple product cancel. -/

/-- `principalSignExp` is symmetric in its two residues. -/
lemma principalSignExp_comm (d : ℕ) (p q : ℤ) :
    principalSignExp d p q = principalSignExp d q p := by
  unfold principalSignExp
  rw [add_comm p q, mul_comm p q]

/-- `3d² + d` is always even: `d(3d+1)` has an even factor regardless of the parity of `d`. -/
private lemma even_three_d_sq_add_d (d : ℤ) : Even (3 * d ^ 2 + d) := by
  rcases Int.even_or_odd d with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨6 * k ^ 2 + k, by rw [hk]; ring⟩
  · exact ⟨6 * k ^ 2 + 7 * k + 2, by rw [hk]; ring⟩

/-- The zero-coordinate case of the sign-exponent parity: no `ξ_d` correction is needed (`K' = 0`
in the transport exponent), and the two sign exponents sum to `d(d+1)`, always even. -/
lemma reciprocal_sign_even_zero_fst (d : ℕ) (c1 : ℤ) (hc1 : 0 < c1)
    (hc1' : c1 < (d : ℤ)) :
    Even (principalSignExp d 0 c1 + principalSignExp d 0 ((d : ℤ) - c1)) := by
  have h1 : min (d : ℤ) (0 + c1) = c1 := by rw [zero_add]; exact min_eq_right hc1'.le
  have h2 : min (d : ℤ) (0 + ((d : ℤ) - c1)) = (d : ℤ) - c1 := by
    rw [zero_add]; exact min_eq_right (by linarith)
  have heq : principalSignExp d 0 c1 + principalSignExp d 0 ((d : ℤ) - c1) =
      (d : ℤ) * ((d : ℤ) + 1) := by
    unfold principalSignExp; rw [h1, h2]; ring
  rw [heq]; exact Int.even_mul_succ_self d

/-- The generic case of the sign-exponent parity, where the `ξ_d` correction contributes the
transport exponent `K' = c0 - c1`. The two-way split on `c0 + c1` versus `d` resolves the
`min (d, ·)` terms in `principalSignExp`; the resulting polynomial identity is checked against
`even_three_d_sq_add_d` by `linear_combination`. -/
lemma reciprocal_sign_even_generic (d : ℕ) (c0 c1 : ℤ) :
    Even (((d : ℤ) + 1) * (c0 - c1) +
      (principalSignExp d c0 c1 + principalSignExp d ((d : ℤ) - c0) ((d : ℤ) - c1))) := by
  obtain ⟨v, hv⟩ := even_three_d_sq_add_d (d : ℤ)
  rcases le_total (c0 + c1) (d : ℤ) with hs | hs
  · have h1 : min (d : ℤ) (c0 + c1) = c0 + c1 := min_eq_right hs
    have h2 : min (d : ℤ) (((d : ℤ) - c0) + ((d : ℤ) - c1)) = (d : ℤ) :=
      min_eq_left (by linarith)
    unfold principalSignExp
    rw [h1, h2]
    exact ⟨v + c0 - (d : ℤ) * c1 + c0 * c1, by linear_combination hv⟩
  · have h1 : min (d : ℤ) (c0 + c1) = (d : ℤ) := min_eq_left hs
    have h2 : min (d : ℤ) (((d : ℤ) - c0) + ((d : ℤ) - c1)) = ((d : ℤ) - c0) + ((d : ℤ) - c1) :=
      min_eq_right (by linarith)
    unfold principalSignExp
    rw [h1, h2]
    exact ⟨v + c0 - (d : ℤ) * c1 + c0 * c1 - (c0 + c1 - (d : ℤ)), by linear_combination hv⟩

end SIC

end
