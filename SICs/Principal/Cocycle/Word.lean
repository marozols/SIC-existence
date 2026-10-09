/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Cocycle.Real
import SICs.Principal.Cocycle.WordIdentification

/-!
# The Principal Word Value

The general `wordSigmaS` at `A_d` equals the principal three-factor value at every canonical index.

This module compares the word construction of [AFK25, Appendix C] with the independently
computed principal-family value `principalSigmaAdCanonical` of `SICs.Principal.Cocycle.Real`.
The general construction uses the Hirzebruch--Jung word identified in
`SICs.Principal.Cocycle.WordIdentification`. The modular-cocycle comparison at `A_d` continues in
`SICs.Principal.Cocycle.ModularValues`.

## The argument

The three factors have raw arguments `z/ρ_d²`, `z/ρ_d`, and `z`. The general word construction
reduces each by an integer into the domain of `sigmaSBase`; the principal construction instead
uses a shift `kρ_d - ℓ` in the third factor. The joint shift-independence theorem
`sigmaSHonest_eq_sigmaS` identifies these reductions. Canonical nonzero arguments avoid
`ℤρ_d + ℤ`, so its nonvanishing hypotheses apply.

At the origin all three raw arguments are zero. The integer shift leaves zero fixed, and
`sigmaSHonest_zero` reads the common value directly. Thus `wordSigmaS_principalA` includes the
origin without invoking the nonintegral-characteristic periodicity theorem.

## Main declarations

- `principalDoubleSineArg_sub_one_latticeFree`: the nonzero canonical arguments avoid the lattice.
- `wordSigmaS_principalA_eq_triple`: the word expansion along the three steps for `A_d = U_d³`,
  using the fixed-point and denominator identities of `SICs.Principal.Quadratic.Stabilizers`.
- `wordSigmaS_principalA`: the general word value is `principalSigmaAdCanonical`.

## References

- [AFK25, Appendix C, Theorem C.4, `thm:tsaltexpn`]
- [AFK25, Definition 1.18, `def:shin`, equation (1.26), `eq:shindf`]
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### The three word arguments, in one shape

The three steps of the word for `A_d = U_d³` evaluate `σ_S` at `z`, `z/ρ_d`, and `z/ρ_d²`.
This section rewrites all three arguments in the affine form used by canonical reduction.
-/

/-- The cocycle argument `z = (qρ_d - p)/d` is the canonical double-sine argument at the
*transposed* index pair, shifted into `sigmaSBase`'s domain: `z = arg_d(q,p) - 1`. Together with
`principalZ_div_principalRoot_eq` and `principalZ_div_principalRoot_sq_eq` this puts all three of
the word's base points in the single shape `arg_d(u,v) - 1`, so one pair of bounds and one
lattice-freeness lemma covers them all. -/
lemma principalZ_eq_principalDoubleSineArg_sub_one (d : ℕ) (p q : ℤ) :
    principalZ d p q = principalDoubleSineArg d q p - 1 := by
  rw [principalZ, principalDoubleSineArg]; ring

/-- A canonical double-sine argument, shifted by `-1`, lies in `sigmaSBase`'s domain `(-1, ρ_d)`.
This is `principalDoubleSineArg_mem_Ioo`'s chamber statement `0 < arg < ρ_d + 1`, translated. -/
lemma principalDoubleSineArg_sub_one_mem_Ioo (d : ℕ) (hd : 3 < d) (u v : ℤ)
    (hu : 0 ≤ u) (hu' : u < (d : ℤ)) (hv : 0 ≤ v) (hv' : v < (d : ℤ)) :
    -1 < principalDoubleSineArg d u v - 1 ∧
      principalDoubleSineArg d u v - 1 < principalRoot d := by
  obtain ⟨h1, h2⟩ := principalDoubleSineArg_mem_Ioo d hd u v hu hu' hv hv'
  exact ⟨by linarith, by linarith⟩

/-- **Canonical arguments avoid the lattice `ℤρ_d + ℤ`.** Writing `(uρ_d - v)/d = aρ_d + b` and
using irrationality of `ρ_d` forces `u = ad` and `v = -bd`; the canonical range `0 ≤ u, v < d`
then forces `u = v = 0`, the one pair excluded. This discharges
`SICs.Cocycle.SigmaS.Reduction.sigmaS_congr`'s hypothesis for every base point of the principal
word. -/
lemma principalDoubleSineArg_sub_one_latticeFree (d : ℕ) (hd : 3 < d) (u v : ℤ)
    (hu : 0 ≤ u) (hu' : u < (d : ℤ)) (hv : 0 ≤ v) (hv' : v < (d : ℤ)) (hne : ¬(u = 0 ∧ v = 0)) :
    SigmaSLatticeFree (principalRoot d) (principalDoubleSineArg d u v - 1) := by
  have hd0 : ((d : ℝ)) ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < (d : ℝ))
  have hirr := principalRoot_irrational d hd
  intro a b hab
  rw [principalDoubleSineArg] at hab
  -- Clear the denominator: `(u - a d) ρ_d = v + b d` as reals.
  have hkey : (((u - a * d : ℤ)) : ℝ) * principalRoot d = (((v + b * d : ℤ)) : ℝ) := by
    have hd0' : (0 : ℝ) < (d : ℝ) := by positivity
    push_cast
    field_simp at hab
    linarith
  have hdpos : (0 : ℤ) < (d : ℤ) := by exact_mod_cast (by omega : 0 < d)
  have hu_eq : u - a * d = 0 := by
    by_contra hzero
    exact Irrational.ne_int (Irrational.intCast_mul hirr hzero) (v + b * d) hkey
  have hv_eq : v + b * d = 0 := by
    have h0 : ((0 : ℤ) : ℝ) * principalRoot d = (((v + b * d : ℤ)) : ℝ) := by
      rw [← hu_eq]; exact hkey
    exact_mod_cast (by simpa using h0.symm : ((v + b * d : ℤ) : ℝ) = ((0 : ℤ) : ℝ))
  -- `d ∣ u` with `0 ≤ u < d` gives `u = 0`, and then likewise for `v`.
  exact hne ⟨Int.eq_zero_of_dvd_of_nonneg_of_lt hu hu' ⟨a, by linear_combination hu_eq⟩,
    Int.eq_zero_of_dvd_of_nonneg_of_lt hv hv' ⟨-b, by linear_combination hv_eq⟩⟩

/-! ### The third index is a canonical residue

For a canonical nonzero pair `(p,q)`, the reduced third coordinate also lies in
`{0, …, d-1}`. Its possible zero cases are isolated for the subsequent domain checks.
-/

/-- `r = (-p-q) mod d` is a canonical residue. -/
lemma principalThirdIndex_mem (d : ℕ) (hd : 3 < d) (p q : ℤ) :
    0 ≤ principalThirdIndex d p q ∧ principalThirdIndex d p q < (d : ℤ) := by
  have hdpos : (0 : ℤ) < (d : ℤ) := by exact_mod_cast (by omega : 0 < d)
  exact ⟨Int.emod_nonneg _ hdpos.ne', Int.emod_lt_of_pos _ hdpos⟩

/-- If `p` and the third index both vanish, so does `q` — so the pair `(p, r)` indexing the
word's second factor is never `(0,0)` unless `(p,q)` is. -/
private lemma principalThirdIndex_ne_zero_of_fst (d : ℕ) (p q : ℤ)
    (hq0 : 0 ≤ q) (hq1 : q < (d : ℤ)) (hne : ¬(p = 0 ∧ q = 0)) :
    ¬(p = 0 ∧ principalThirdIndex d p q = 0) := by
  rintro ⟨hp, hr⟩
  refine hne ⟨hp, ?_⟩
  rw [principalThirdIndex, hp] at hr
  have hdvd : (d : ℤ) ∣ q := (dvd_neg.mp (by simpa using Int.dvd_of_emod_eq_zero hr))
  exact Int.eq_zero_of_dvd_of_nonneg_of_lt hq0 hq1 hdvd

/-- Likewise for the pair `(r, q)` indexing the word's third factor. -/
private lemma principalThirdIndex_ne_zero_of_snd (d : ℕ) (p q : ℤ)
    (hp0 : 0 ≤ p) (hp1 : p < (d : ℤ)) (hne : ¬(p = 0 ∧ q = 0)) :
    ¬(principalThirdIndex d p q = 0 ∧ q = 0) := by
  rintro ⟨hr, hq⟩
  refine hne ⟨?_, hq⟩
  rw [principalThirdIndex, hq] at hr
  have hdvd : (d : ℤ) ∣ p := (dvd_neg.mp (by simpa using Int.dvd_of_emod_eq_zero hr))
  exact Int.eq_zero_of_dvd_of_nonneg_of_lt hp0 hp1 hdvd

/-! ### The link-up theorem

The three matrices `wordSigmaS` visits from the seed `A_d` are `U_d²`, `U_d`, and `1`. All three
have period `ρ_d` — `U_d` fixes `ρ_d`, so every power does — and their Jacobi denominators at
`ρ_d` are the successive powers `ρ_d²`, `ρ_d`, `1`, which is exactly what turns the word's raw
arguments into `z/ρ_d²`, `z/ρ_d`, `z`. These fixed-point and Jacobi-denominator identities are
recorded in `SICs.Principal.Quadratic.Stabilizers`.

The general word expansion and the principal canonical reduction then have matching factors.
Shift-independence of `sigmaSHonest` identifies them, yielding the concrete evaluation of
`wordSigmaS` at `A_d`.
-/

/-- Expanding `wordSigmaS` along the three Hirzebruch--Jung steps for `A_d = U_d³` gives the
product of the honest `σ_S` values at `z/ρ_d²`, `z/ρ_d`, and `z`. This helper supplies the
word expansion used by `wordSigmaS_principalA`. -/
theorem wordSigmaS_principalA_eq_triple (d : ℕ) (hd : 3 < d) (z : ℝ)
    (h0 : 0 ≤ (principalA d) 1 0) :
    wordSigmaS z (principalRoot d) (principalA d) h0 =
      sigmaSHonest (z / principalRoot d ^ 2) (principalRoot d) *
        sigmaSHonest (z / principalRoot d) (principalRoot d) *
        sigmaSHonest z (principalRoot d) := by
  have hd4 : (4 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  -- Lower-left entries of the four matrices the recursion visits.
  have hAlow : (principalA d) 1 0 = (d : ℤ) * ((d : ℤ) - 2) := by simp [coe_principalA]
  have hAne : (principalA d) 1 0 ≠ 0 := by rw [hAlow]; nlinarith
  have hU2low := principalU_sq_lowerLeft d
  have hU2ne : (principalU d ^ 2 : SL(2, ℤ)) 1 0 ≠ 0 := by rw [hU2low]; omega
  have h0U2 : 0 ≤ (principalU d ^ 2 : SL(2, ℤ)) 1 0 := by rw [hU2low]; omega
  have hUlow := principalU_lowerLeft d
  have hUne : (principalU d : SL(2, ℤ)) 1 0 ≠ 0 := by rw [hUlow]; omega
  have h0U : 0 ≤ (principalU d : SL(2, ℤ)) 1 0 := by rw [hUlow]; omega
  have hIlow : ((1 : SL(2, ℤ))) 1 0 = 0 := by simp
  have h0I : 0 ≤ ((1 : SL(2, ℤ))) 1 0 := by rw [hIlow]
  rw [wordSigmaS_step _ _ h0 hAne (hjStep_snd_principalA d hd) h0U2,
    wordSigmaS_step _ _ h0U2 hU2ne (hjStep_snd_principalU_sq d hd) h0U,
    wordSigmaS_step _ _ h0U hUne (hjStep_snd_principalU d hd) h0I,
    wordSigmaS_of_lowerLeft_eq_zero _ _ _ h0I hIlow,
    fltDenominator_principalU_sq_principalRoot d hd,
    flt_principalU_sq_principalRoot d hd,
    fltDenominator_principalU_principalRoot d,
    flt_principalU_principalRoot d hd, Matrix.SpecialLinearGroup.coe_one,
    fltDenominator_one, flt_one, div_one]
  ring

/-- **The general word-chained cocycle computes the principal family's known value.** For a
canonical pair `(p,q)`, `wordSigmaS` at `A_d`, `ρ_d`, and `z = (qρ_d-p)/d` equals
`principalSigmaAdCanonical d p q`.

Both sides use the raw arguments `z/ρ_d²`, `z/ρ_d`, and `z`, but reduce them into
`sigmaSBase`'s domain differently. The joint shift-independence theorem
`SICs.Cocycle.SigmaS.Reduction.sigmaSHonest_eq_sigmaS` identifies the reductions, with lattice
avoidance
provided by `principalDoubleSineArg_sub_one_latticeFree`. The origin follows separately from
`sigmaSHonest_zero`. -/
theorem wordSigmaS_principalA (d : ℕ) (hd : 3 < d) (p q : ℤ)
    (hp0 : 0 ≤ p) (hp1 : p < (d : ℤ)) (hq0 : 0 ≤ q) (hq1 : q < (d : ℤ))
    (h0 : 0 ≤ (principalA d) 1 0) :
    wordSigmaS (principalZ d p q) (principalRoot d) (principalA d) h0 =
      principalSigmaAdCanonical d p q := by
  rw [wordSigmaS_principalA_eq_triple d hd, principalSigmaAdCanonical]
  by_cases hne : p = 0 ∧ q = 0
  · -- The origin. All three word arguments are `0`, which `sfShift` leaves where it is.
    rw [ite_eq_left hne]
    obtain ⟨hp, hq⟩ := hne
    subst hp
    subst hq
    rw [show principalZ d 0 0 = 0 by simp [principalZ], zero_div, zero_div, sigmaSHonest_zero]
    ring
  rw [ite_eq_right hne]
  have hρpos := principalRoot_pos d hd
  obtain ⟨hr0, hr1⟩ := principalThirdIndex_mem d hd p q
  -- Convert each honest factor to the principal family's own explicitly-shifted presentation.
  have hfac3 : sigmaSHonest (principalZ d p q) (principalRoot d) =
      sigmaS (principalZ d p q) (principalRoot d) 0 0 := by
    have hshape := principalZ_eq_principalDoubleSineArg_sub_one d p q
    obtain ⟨hb1, hb2⟩ := principalDoubleSineArg_sub_one_mem_Ioo d hd q p hq0 hq1 hp0 hp1
    refine sigmaSHonest_eq_sigmaS _ _ _ 0 0 hρpos (by rw [hshape]; exact hb1)
      (by rw [hshape]; exact hb2) ?_ (by push_cast; ring)
    rw [hshape]
    exact principalDoubleSineArg_sub_one_latticeFree d hd q p hq0 hq1 hp0 hp1
      (fun h => hne ⟨h.2, h.1⟩)
  have hfac2 : sigmaSHonest (principalZ d p q / principalRoot d) (principalRoot d) =
      sigmaS (principalDoubleSineArg d p (principalThirdIndex d p q) - 1) (principalRoot d) 0
        (-principalReductionK d p q) := by
    obtain ⟨hb1, hb2⟩ :=
      principalDoubleSineArg_sub_one_mem_Ioo d hd p (principalThirdIndex d p q) hp0 hp1 hr0 hr1
    refine sigmaSHonest_eq_sigmaS _ _ _ 0 _ hρpos hb1 hb2
      (principalDoubleSineArg_sub_one_latticeFree d hd p (principalThirdIndex d p q) hp0 hp1 hr0 hr1
        (principalThirdIndex_ne_zero_of_fst d p q hq0 hq1 hne)) ?_
    rw [principalZ_div_principalRoot_eq d hd p q hp0 hp1 hq0 hq1 hne]
    push_cast
    ring
  have hfac1 : sigmaSHonest (principalZ d p q / principalRoot d ^ 2) (principalRoot d) =
      sigmaS (principalDoubleSineArg d (principalThirdIndex d p q) q - 1) (principalRoot d)
        (principalReductionK d p q) (-principalReductionL d p q) := by
    obtain ⟨hb1, hb2⟩ :=
      principalDoubleSineArg_sub_one_mem_Ioo d hd (principalThirdIndex d p q) q hr0 hr1 hq0 hq1
    refine sigmaSHonest_eq_sigmaS _ _ _ _ _ hρpos hb1 hb2
      (principalDoubleSineArg_sub_one_latticeFree d hd (principalThirdIndex d p q) q hr0 hr1 hq0 hq1
        (principalThirdIndex_ne_zero_of_snd d p q hp0 hp1 hne)) ?_
    rw [principalZ_div_principalRoot_sq_eq d hd p q hp0 hp1 hq0 hq1 hne]
    push_cast
    ring
  rw [hfac1, hfac2, hfac3]
  ring

end SIC
