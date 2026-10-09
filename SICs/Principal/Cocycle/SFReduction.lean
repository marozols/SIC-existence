/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Cocycle.CanonicalReduction

/-!
# Reduction of the Cocycle Word Product to Finite Algebra

The cocycle-word decomposition and the SF/product identification.

This file reduces the principal cocycle word product to finite algebra in the form of equation
(8.9). Combining the three-factor word decomposition
`σ_{A_d}(z,ρ_d) = σ_S(z/ρ_d²,ρ_d)·σ_S(z/ρ_d,ρ_d)·σ_S(z,ρ_d)`, the raw index identities for
`z+1`, `z/ρ_d+1` and `z/ρ_d²+1` (`SICs.Principal.Cocycle.CanonicalReduction`), and the canonical
reduction data `k = p - j`, `ℓ = (d-2)p - q` (also `CanonicalReduction`) with `sigmaS`'s
shift formula (`SICs.Cocycle.UpperHalfPlane`), every double-sine value cancels between the candidate
and product overlaps, leaving a finite closed-form correction in `qPochhammerFin`, one exponential,
and the elementary signs `RankOneAdmissibleTuple.sfPhase`/`principalSignExp`.

As in `SICs.Principal.Ghost.Origin`'s `sfPhase_zero_mul_sigmaSBase_zero_cube` (the origin case),
this local proof expands `A_d`'s three-factor word directly. It does not depend on the general
word-chained cocycle declaration; `SICs.Principal.Cocycle.Word` subsequently proves that the two
presentations agree.

## References

- [AFK25, Section 8, especially equations (8.5)--(8.9)]
-/

noncomputable section

open Real Complex

namespace SIC

/-! ### From the general `sigmaS` triple identity to canonical base points

The general algebraic identity `sigmaS_triple_eq` separates the finite `qPochhammerFin` ratios
from three `sigmaSBase` values. The lemma below evaluates those base values when their shifted
arguments are the three cyclic factors of the principal product.
-/

/-- Multiplying three `sigmaSBase` factors at base points whose `+1` shift lands on the three
canonical arguments of `principalTripleDoubleSine d p q` (in the cyclic order `(q,p), (p,r),
(r,q)` that the word decomposition and the canonical reduction produce) collapses every
double-sine value: the three `doubleSine'` denominators are exactly `principalTripleDoubleSine`'s
three factors, up to the sign `(-1)^{signExp}`. -/
lemma sigmaSBase_triple_eq_of_canon (d : ℕ) (p q : ℤ) (w1 w2 w3 : ℝ)
    (h3 : w3 + 1 = principalDoubleSineArg d q p)
    (h2 : w2 + 1 = principalDoubleSineArg d p (principalThirdIndex d p q))
    (h1 : w1 + 1 = principalDoubleSineArg d (principalThirdIndex d p q) q) :
    sigmaSBase w3 (principalRoot d) * sigmaSBase w2 (principalRoot d) *
        sigmaSBase w1 (principalRoot d) =
      (-1 : ℂ) ^ principalSignExp d p q * (principalTripleDoubleSine d p q : ℂ) *
        Complex.exp (sfExpArg w1 (principalRoot d) + sfExpArg w2 (principalRoot d) +
          sfExpArg w3 (principalRoot d)) := by
  rw [sigmaSBase_eq_exp_div, sigmaSBase_eq_exp_div, sigmaSBase_eq_exp_div, h1, h2, h3,
    Complex.exp_add, Complex.exp_add, principalTripleDoubleSine]
  push_cast
  have hne1 := (doubleSine_principalDoubleSineArg_pos d q p).ne'
  have hne2 := (doubleSine_principalDoubleSineArg_pos d p (principalThirdIndex d p q)).ne'
  have hne3 := (doubleSine_principalDoubleSineArg_pos d (principalThirdIndex d p q) q).ne'
  have hcast1 : ((doubleSine' (principalDoubleSineArg d q p) (principalRoot d) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hne1
  have hcast2 : ((doubleSine' (principalDoubleSineArg d p (principalThirdIndex d p q))
      (principalRoot d) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hne2
  have hcast3 : ((doubleSine' (principalDoubleSineArg d (principalThirdIndex d p q) q)
      (principalRoot d) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hne3
  field_simp
  have hsq : ((-1 : ℂ) ^ principalSignExp d p q) ^ 2 = 1 := by
    rw [← zpow_natCast ((-1 : ℂ) ^ principalSignExp d p q) 2, ← zpow_mul]
    exact Even.neg_one_zpow ⟨principalSignExp d p q, by ring⟩
  exact hsq.symm

/-! ### The principal word product in closed form

The identity below states the fully reduced word decomposition for `A_d` directly. The base points
`principalDoubleSineArg d p (principalThirdIndex d p q) - 1` and
`principalDoubleSineArg d (principalThirdIndex d p q) q - 1`, with shift pairs `(0,-k)` and
`(k,-ℓ)`, give the `(base point, m₁, m₂)` shift decompositions of `z/ρ_d` and `z/ρ_d²`
respectively (`principalZ_div_principalRoot_eq`, `principalZ_div_principalRoot_sq_eq`,
`SICs.Principal.Cocycle.CanonicalReduction`). These decompositions identify the product as
`σ_S(z/ρ_d²,ρ_d)·σ_S(z/ρ_d,ρ_d)·σ_S(z,ρ_d) = σ_{A_d}(z,ρ_d)`. The theorem
`wordSigmaS_principalA` supplies the comparison with the general declaration. -/

/-- **The reduction to finite algebra, core identity.**
`σ_{A_d}(z,ρ_d)`, computed as the product of three `sigmaS` factors at the canonical
base points and shift counts `k = p - j` and `ℓ = (d-2)p - q`, equals
`(-1)^{signExp}·ν_d(p,q)` times a finite correction:
one exponential prefactor (`sfExpArg` at the three canonical base points) times a
`qPochhammerFin` ratio. No double-sine value remains.

The identity is one of finite algebra and holds at *every* index pair: neither the canonical
bounds `0 ≤ p, q < d` nor `(p,q) ≠ (0,0)` is needed, and neither is `3 < d`. Its consumers impose
them for their own reasons. -/
theorem principal_sigmaAd_eq (d : ℕ) (p q : ℤ) :
    sigmaS (principalZ d p q) (principalRoot d) 0 0 *
        sigmaS (principalDoubleSineArg d p (principalThirdIndex d p q) - 1) (principalRoot d) 0
          (-principalReductionK d p q) *
        sigmaS (principalDoubleSineArg d (principalThirdIndex d p q) q - 1) (principalRoot d)
          (principalReductionK d p q) (-principalReductionL d p q) =
      qPochhammerFin (principalReductionK d p q)
          (principalDoubleSineArg d (principalThirdIndex d p q) q - 1) (principalRoot d) /
        (qPochhammerFin (principalReductionK d p q)
            ((principalDoubleSineArg d p (principalThirdIndex d p q) - 1) / principalRoot d)
            (-1 / principalRoot d) *
          qPochhammerFin (principalReductionL d p q)
            ((principalDoubleSineArg d (principalThirdIndex d p q) q - 1) / principalRoot d)
            (-1 / principalRoot d)) *
      ((-1 : ℂ) ^ principalSignExp d p q * (principalTripleDoubleSine d p q : ℂ) *
        Complex.exp
          (sfExpArg (principalDoubleSineArg d (principalThirdIndex d p q) q - 1)
              (principalRoot d) +
            sfExpArg (principalDoubleSineArg d p (principalThirdIndex d p q) - 1)
              (principalRoot d) +
            sfExpArg (principalZ d p q) (principalRoot d))) := by
  rw [sigmaS_triple_eq, sigmaSBase_triple_eq_of_canon d p q _ _ _
    (principalZ_add_one_eq d p q) (by ring) (by ring)]
  push_cast
  ring

/-! ### The full reduction: `ν̃_d(p,q)` in closed form

`(principalRankOneAdmissibleTuple ⟨d,hd⟩).sfPhase (principalA d) ![p,q]` *is* `Φ_d(p,q)`
(`SICs.Ghost.CandidateOverlaps`'s general SF phase, specialized to the principal family by
`RankOneAdmissibleTuple.sfPhase_of_conductorRatio_eq_one` -- not re-unfolded here, leaving `Φ_d`
opaque in the statement itself). Dividing
`principal_sigmaAd_eq`'s identity by `qPochhammerFin (-ℓ) (z/j_{A_d}(ρ_d)) ρ_d` forms `ש` (Def.
`ש^r_M = σ_M/ϖ_{n_QP}`, since `n_QP(p,q) = -ℓ` by
`principalN_shift_eq_neg_nQP`/`nQP_principalA`); further multiplying by `Φ_d(p,q)` forms the
three-double-sine overlap `ν̃_d(p,q)`. This direct calculation does not need to invoke the
general cocycle declaration. -/

/-- **The reduction to finite algebra, in full**:
`ν̃_d(p,q)`, computed as `Φ_d(p,q)` times the SF cocycle value from the word product at `A_d`,
equals `Φ_d(p,q) · (-1)^{signExp} · ν_d(p,q)` times the same finite `qPochhammerFin`/exponential
correction as `principal_sigmaAd_eq`, further divided by `ϖ_{-ℓ}(z/j_{A_d}(ρ_d),ρ_d)`. The
identification collapses to a finite algebraic identity with no remaining double-sine value
anywhere. Like `principal_sigmaAd_eq`, it needs no bounds on `(p,q)`. -/
theorem principal_sf_reduction2 (d : ℕ) (hd : 3 < d) (p q : ℤ) :
    (principalRankOneAdmissibleTuple ⟨d, hd⟩).sfPhase (principalA d) ![p, q] *
        (sigmaS (principalZ d p q) (principalRoot d) 0 0 *
          sigmaS (principalDoubleSineArg d p (principalThirdIndex d p q) - 1) (principalRoot d) 0
            (-principalReductionK d p q) *
          sigmaS (principalDoubleSineArg d (principalThirdIndex d p q) q - 1) (principalRoot d)
            (principalReductionK d p q) (-principalReductionL d p q)) /
        qPochhammerFin (-principalReductionL d p q)
          (principalZ d p q / principalJacobiFactor d) (principalRoot d) =
      (principalRankOneAdmissibleTuple ⟨d, hd⟩).sfPhase (principalA d) ![p, q] *
        (qPochhammerFin (principalReductionK d p q)
            (principalDoubleSineArg d (principalThirdIndex d p q) q - 1) (principalRoot d) /
          (qPochhammerFin (principalReductionK d p q)
              ((principalDoubleSineArg d p (principalThirdIndex d p q) - 1) / principalRoot d)
              (-1 / principalRoot d) *
            qPochhammerFin (principalReductionL d p q)
              ((principalDoubleSineArg d (principalThirdIndex d p q) q - 1) / principalRoot d)
              (-1 / principalRoot d)) *
          ((-1 : ℂ) ^ principalSignExp d p q * (principalTripleDoubleSine d p q : ℂ) *
            Complex.exp
              (sfExpArg (principalDoubleSineArg d (principalThirdIndex d p q) q - 1)
                  (principalRoot d) +
                sfExpArg (principalDoubleSineArg d p (principalThirdIndex d p q) - 1)
                  (principalRoot d) +
                sfExpArg (principalZ d p q) (principalRoot d)))) /
        qPochhammerFin (-principalReductionL d p q)
          (principalZ d p q / principalJacobiFactor d) (principalRoot d) := by
  rw [principal_sigmaAd_eq d p q]

/-! ### The `ℓ`-factor collapses elementarily

This section proves that the `ℓ`-part of `principal_sf_reduction2`'s finite correction is `1`,
unconditionally, by an elementary `qPochhammerFin` identity. The following section proves the
corresponding statement for the `k`-part.

The mechanism: `ρ_d + ρ_d⁻¹ = d - 1 ∈ ℤ` (`principalRoot_satisfies_quadratic`), so `-1/ρ_d` is
literally `ρ_d` shifted by the *integer* `-(d-1)`. Since `qPochhammerFin`'s factors are
`1 - e^{2πi(z+jτ)}`, shifting `τ` by an integer `k` only ever shifts each factor's exponent by the
integer `jk`, which `Complex.exp_int_mul_two_pi_mul_I` kills -- so `qPochhammerFin n z (-1/ρ_d) =
qPochhammerFin n z ρ_d` identically (`qPochhammerFin_principalRoot_neg_inv`). Combined with the
same integer-shift invariance in the *other* argument (`qPochhammerFin_add_intCast`) and the
self-cancelling shift identity `qPochhammerFin_mul_neg_div_eq_one` (an instance of the same
mechanism, structurally the finite-product analogue of [72]'s Lemma `lem:ell` that eq. (8.9)
itself already uses -- see `SICs.Cocycle.UpperHalfPlane`'s Kopp's-Lemma section), the `ℓ`-pair
`ϖ_ℓ(w1/ρ_d,-1/ρ_d) · ϖ_{-ℓ}(z/j_{A_d}(ρ_d),ρ_d)` collapses to `1` unconditionally. -/

/-- **`qPochhammerFin` at `-1/ρ_d` equals `qPochhammerFin` at `ρ_d`.** `-1/ρ_d` is `ρ_d` shifted
by the integer `-(d-1)` (`principalRoot_add_inv`, `SICs.Principal.Quadratic.Forms`), so
the general period-shift identity `qPochhammerFin_tau_add_intCast` applies.
The statement uses `z : ℂ`, as does `qPochhammerFin_add_intCast`. -/
lemma qPochhammerFin_principalRoot_neg_inv (d : ℕ) (hd : 3 < d) (n : ℤ) (z : ℂ) :
    qPochhammerFin n z (-1 / principalRoot d : ℝ) = qPochhammerFin n z (principalRoot d) := by
  have h := principalRoot_add_inv d hd
  have hinv : (principalRoot d)⁻¹ = (d : ℝ) - 1 - principalRoot d := by linarith
  have hne1 : (-1 / principalRoot d : ℝ) = principalRoot d + ((-(d : ℤ) + 1 : ℤ) : ℝ) := by
    rw [show (-1 / principalRoot d : ℝ) = -(principalRoot d)⁻¹ from by ring, hinv]
    push_cast; ring
  rw [hne1, Complex.ofReal_add, Complex.ofReal_intCast, qPochhammerFin_tau_add_intCast]

/-- The modular-cocycle denominator argument is the reduced `ℓ`-shifted base point, up to the
integer `k`-shift that finite `q`-Pochhammer symbols ignore. -/
private lemma principalZ_div_principalJacobiFactor_eq (d : ℕ) (hd : 3 < d) (p q : ℤ)
    (hp0 : 0 ≤ p) (hp1 : p < (d : ℤ)) (hq0 : 0 ≤ q) (hq1 : q < (d : ℤ))
    (hne : ¬(p = 0 ∧ q = 0)) :
    (principalZ d p q : ℂ) / (principalJacobiFactor d : ℂ) =
      ((principalDoubleSineArg d (principalThirdIndex d p q) q - 1 : ℝ) : ℂ) /
          (principalRoot d : ℂ) -
        ((principalReductionL d p q : ℤ) : ℂ) / (principalRoot d : ℂ) +
        ((principalReductionK d p q : ℤ) : ℂ) := by
  have hρ0 : principalRoot d ≠ 0 := ne_of_gt (principalRoot_pos d hd)
  have hstep := principalZ_div_principalRoot_sq_eq d hd p q hp0 hp1 hq0 hq1 hne
  have hzdivR : principalZ d p q / principalJacobiFactor d =
      (principalDoubleSineArg d (principalThirdIndex d p q) q - 1) / principalRoot d -
        (principalReductionL d p q : ℝ) / principalRoot d +
        (principalReductionK d p q : ℝ) := by
    rw [principalJacobiFactor_eq_principalRoot_pow_three d hd,
      show principalZ d p q / principalRoot d ^ 3 =
        (principalZ d p q / principalRoot d ^ 2) / principalRoot d by
          rw [div_div, ← pow_succ], hstep]
    field_simp
    ring
  exact_mod_cast hzdivR

/-- **The `ℓ`-pair of the reduction's finite correction collapses to `1`.** This follows from
the elementary mechanism above: `-1/ρ_d ≡ ρ_d` and `z/j_{A_d}(ρ_d) ≡ w₁/ρ_d -
ℓ/ρ_d` (both mod an integer), reducing the pair to a direct instance of
`qPochhammerFin_mul_neg_div_eq_one`. The nonvanishing hypothesis is the same pole-avoidance
condition that no intermediate point of the recursion is an integer multiple of `ρ_d` or of `1`;
`SICs.Principal.Cocycle.PoleAvoidance` proves it uniformly. -/
theorem principal_qPoch_ell_pair_eq_one (d : ℕ) (hd : 3 < d) (p q : ℤ)
    (hp0 : 0 ≤ p) (hp1 : p < (d : ℤ)) (hq0 : 0 ≤ q) (hq1 : q < (d : ℤ))
    (hne : ¬(p = 0 ∧ q = 0))
    (hnv : qPochhammerFin (principalReductionL d p q)
        ((principalDoubleSineArg d (principalThirdIndex d p q) q - 1) / principalRoot d)
        (principalRoot d) ≠ 0) :
    qPochhammerFin (principalReductionL d p q)
        ((principalDoubleSineArg d (principalThirdIndex d p q) q - 1) / principalRoot d)
        (-1 / principalRoot d) *
      qPochhammerFin (-principalReductionL d p q)
        (principalZ d p q / principalJacobiFactor d) (principalRoot d) = 1 := by
  have hρ0 : principalRoot d ≠ 0 := ne_of_gt (principalRoot_pos d hd)
  rw [show ((-1 : ℂ) / (principalRoot d : ℂ)) = ((-1 / principalRoot d : ℝ) : ℂ) from by
    push_cast; ring]
  rw [qPochhammerFin_principalRoot_neg_inv d hd]
  rw [principalZ_div_principalJacobiFactor_eq d hd p q hp0 hp1 hq0 hq1 hne]
  rw [qPochhammerFin_add_intCast (-principalReductionL d p q)
    (((principalDoubleSineArg d (principalThirdIndex d p q) q - 1 : ℝ) : ℂ) /
        (principalRoot d : ℂ) -
      ((principalReductionL d p q : ℤ) : ℂ) / (principalRoot d : ℂ))
    (principalRoot d) (principalReductionK d p q)]
  have hm : principalRoot d + (principalRoot d)⁻¹ = (((d : ℤ) - 1 : ℤ) : ℝ) := by
    push_cast; exact principalRoot_add_inv d hd
  have hkey := qPochhammerFin_mul_neg_div_eq_one
    ((principalDoubleSineArg d (principalThirdIndex d p q) q - 1) / principalRoot d)
    (principalRoot d) ((d : ℤ) - 1) (principalReductionL d p q) hρ0 hm (by exact_mod_cast hnv)
  push_cast at hkey ⊢
  linear_combination hkey

/-! ### The `k`-factor collapses too

The `k`-part of the reduction's correction has a similarly elementary reduction: **the base point
`w2 := arg_d(p,r) - 1`, divided by `ρ_d`, is exactly
`w1 := arg_d(r,q) - 1` shifted by the *integer* `j - r`**
(`principalReductionJ d p q - principalThirdIndex d p q`),
where `r := principalThirdIndex d p q = j·d - (p+q)` (`principalThirdIndex_eq_reductionJ`). This is
the same kind of integer-shift fact that collapsed the `ℓ`-pair, just for the *other* mixed pair:
combined with `qPochhammerFin_add_intCast` (no nonvanishing hypothesis needed for the equality
itself) and `qPochhammerFin_principalRoot_neg_inv` (already proved above, for the `-1/ρ_d → ρ_d`
half), it shows the `k`-pair's *numerator and denominator are literally the same finite product*,
so their ratio is `1` whenever that product is nonzero -- a strictly simpler mechanism than the
`ℓ`-pair's self-cancelling shift, needing no auxiliary identity like
`qPochhammerFin_mul_neg_div_eq_one` at all. -/

/-- **The `k`-pair's base points are an integer shift of each other.** `arg_d(p,r) - 1`, divided by
`ρ_d`, equals `arg_d(r,q) - 1` shifted by the integer `j - r` (`j := principalReductionJ d p q`,
`r := principalThirdIndex d p q`). Proved from `r = j·d - (p+q)`
(`principalThirdIndex_eq_reductionJ`) and `ρ_d`'s minimal polynomial alone -- no case split on `j`
is needed at the algebra level, since the identity holds for `r`, `j` related that way regardless
of which case produced them. -/
lemma principalW2_div_root_eq (d : ℕ) (hd : 3 < d) (p q : ℤ)
    (hp0 : 0 ≤ p) (hp1 : p < (d : ℤ)) (hq0 : 0 ≤ q) (hq1 : q < (d : ℤ))
    (hne : ¬(p = 0 ∧ q = 0)) :
    (principalDoubleSineArg d p (principalThirdIndex d p q) - 1) / principalRoot d =
      (principalDoubleSineArg d (principalThirdIndex d p q) q - 1) +
        ((principalReductionJ d p q - principalThirdIndex d p q : ℤ) : ℝ) := by
  have hr := principalThirdIndex_eq_reductionJ d p q hp0 hp1 hq0 hq1 hne
  have hρ0 : principalRoot d ≠ 0 := ne_of_gt (principalRoot_pos d hd)
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [principalDoubleSineArg, principalDoubleSineArg, hr]
  push_cast
  field_simp
  linear_combination ((p : ℝ) + q - principalReductionJ d p q * (d : ℝ)) *
    principalRoot_satisfies_quadratic d hd

/-- **The `k`-pair of the reduction's finite correction collapses to `1`.** Combining
`principalW2_div_root_eq` (the base points are an integer shift apart) with
`qPochhammerFin_principalRoot_neg_inv` (`-1/ρ_d → ρ_d`, proved above for the `ℓ`-pair) and
`qPochhammerFin_add_intCast` shows the numerator and denominator of the `k`-pair are the *same*
finite product, so their ratio is `1` given only that this one product is nonzero -- the same
pole-avoidance flavor of hypothesis as `principal_qPoch_ell_pair_eq_one`, but for a single quantity
rather than the whole interleaving grid. Together with `principal_qPoch_ell_pair_eq_one`, this
shows the entire finite correction is `1`, so `ν̃_d(p,q) = ν_d(p,q)` for every
canonical `(p,q) ≠ (0,0)` away from these poles. -/
theorem principal_qPoch_k_pair_eq_one (d : ℕ) (hd : 3 < d) (p q : ℤ)
    (hp0 : 0 ≤ p) (hp1 : p < (d : ℤ)) (hq0 : 0 ≤ q) (hq1 : q < (d : ℤ))
    (hne : ¬(p = 0 ∧ q = 0))
    (hnv : qPochhammerFin (principalReductionK d p q)
        (principalDoubleSineArg d (principalThirdIndex d p q) q - 1) (principalRoot d) ≠ 0) :
    qPochhammerFin (principalReductionK d p q)
        (principalDoubleSineArg d (principalThirdIndex d p q) q - 1) (principalRoot d) /
      qPochhammerFin (principalReductionK d p q)
        ((principalDoubleSineArg d p (principalThirdIndex d p q) - 1) / principalRoot d)
        (-1 / principalRoot d) = 1 := by
  rw [show ((-1 : ℂ) / (principalRoot d : ℂ)) = ((-1 / principalRoot d : ℝ) : ℂ) from by
    push_cast; ring]
  rw [qPochhammerFin_principalRoot_neg_inv d hd]
  have hshift := principalW2_div_root_eq d hd p q hp0 hp1 hq0 hq1 hne
  have hshiftC : ((principalDoubleSineArg d p (principalThirdIndex d p q) : ℂ) - 1) /
        (principalRoot d : ℂ) =
      ((principalDoubleSineArg d (principalThirdIndex d p q) q : ℂ) - 1) +
        ((principalReductionJ d p q - principalThirdIndex d p q : ℤ) : ℂ) := by
    exact_mod_cast hshift
  rw [hshiftC, qPochhammerFin_add_intCast]
  exact div_self hnv

/-! ### The phase identity

With both finite `qPochhammerFin` pairs eliminated (`principal_qPoch_ell_pair_eq_one`,
`principal_qPoch_k_pair_eq_one`), the entire remaining correction is the pure phase

```
Φ_d(p,q) · (-1)^{signExp(p,q)} · exp(X(w₁) + X(w₂) + X(w₃))
```

with **no finite product and no `qPochhammerFin` left at all**. This subsection shows the exponent
sum reduces, via `ρ_d`'s minimal polynomial alone (no case split, valid for *any* integer `r`, not
just the canonical third index), to a rational multiple of `πi` with no `ρ_d`-dependence left; the
following subsection then shows this rational multiple exactly cancels `Φ_d`'s own phase, reducing
the whole claim to an elementary
integer-parity computation. -/

/-- **The exponent sum of three `sfExpArg` factors at `ρ_d`, in closed form.** For *any* integers
`p, q, r` (no canonical-reduction hypothesis on `r` needed): summing `sfExpArg` at the three
`arg_d(r,q) - 1`, `arg_d(p,r) - 1`, `arg_d(q,p) - 1` base points collapses every `ρ_d²` (via
`ρ_d² = (d-1)ρ_d - 1`) to a purely rational multiple of `πi/12`, with **zero constant term** picked
up along the way -- `ρ_d` cancels completely, leaving no dependence on which real quadratic root
`ρ_d` actually is. -/
lemma principal_sfExpArg_triple_eq (d : ℕ) (hd : 3 < d) (p q r : ℤ) :
    sfExpArg (principalDoubleSineArg d r q - 1) (principalRoot d) +
        sfExpArg (principalDoubleSineArg d p r - 1) (principalRoot d) +
        sfExpArg (principalDoubleSineArg d q p - 1) (principalRoot d) =
      π * Complex.I / 12 *
        ((-12 * (d : ℂ) ^ 2 + 3 * (d : ℂ) ^ 3 + 18 * (d : ℂ) * p - 6 * (d : ℂ) ^ 2 * p -
              6 * (p : ℂ) ^ 2 + 6 * (d : ℂ) * p ^ 2 + 18 * (d : ℂ) * q - 6 * (d : ℂ) ^ 2 * q -
              12 * (p : ℂ) * q - 6 * (q : ℂ) ^ 2 + 6 * (d : ℂ) * q ^ 2 + 18 * (d : ℂ) * r -
              6 * (d : ℂ) ^ 2 * r - 12 * (p : ℂ) * r - 12 * (q : ℂ) * r - 6 * (r : ℂ) ^ 2 +
              6 * (d : ℂ) * r ^ 2) /
            (d : ℂ) ^ 2) := by
  have hρ0 : (principalRoot d : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (principalRoot_pos d hd)
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (show (d : ℝ) ≠ 0 from
    Nat.cast_ne_zero.mpr (by omega))
  have hquad : (principalRoot d : ℂ) ^ 2 - ((d : ℂ) - 1) * (principalRoot d : ℂ) + 1 = 0 := by
    exact_mod_cast principalRoot_satisfies_quadratic d hd
  simp only [sfExpArg, faddeevSExpArg, principalDoubleSineArg]
  push_cast
  field_simp
  linear_combination
    (3 * (d : ℂ) ^ 2 - 6 * d * p + 6 * p ^ 2 - 6 * d * q + 6 * q ^ 2 - 6 * d * r + 6 * r ^ 2) *
      hquad

/-- **The phase identity.** With both finite `qPochhammerFin` pairs already eliminated
(`principal_qPoch_ell_pair_eq_one`, `principal_qPoch_k_pair_eq_one`), this is the reduction's
entire remaining correction, and it is unconditionally `1`: `Φ_d(p,q)`
(`RankOneAdmissibleTuple.sfPhase`, unfolded via
`RankOneAdmissibleTuple.sfPhase_of_conductorRatio_eq_one`), the sign `(-1)^{signExp(p,q)}`, and
the exponential prefactor `exp(X(w₁)+X(w₂)+X(w₃))` (`principal_sfExpArg_triple_eq`) combine, after
converting every root-of-unity factor to a single `Complex.exp`, to `exp` of an explicit *even
integer* multiple of `πi` -- a finite parity computation with no remaining transcendental content,
closed by exhibiting that even integer directly (as `2·K'` for `K' : ℤ` built from
`Int.even_mul_pred_self`/`Int.even_mul_succ_self`, case-split on `principalReductionJ d p q ∈
{1,2}` exactly as `principalThirdIndex_eq_reductionJ` already splits). -/
theorem principal_phase_triple_exp_eq_one (d : ℕ) (hd : 3 < d) (p q : ℤ)
    (hp0 : 0 ≤ p) (hp1 : p < (d : ℤ)) (hq0 : 0 ≤ q) (hq1 : q < (d : ℤ))
    (hne : ¬(p = 0 ∧ q = 0)) :
    (principalRankOneAdmissibleTuple ⟨d, hd⟩).sfPhase (principalA d) ![p, q] *
        (-1 : ℂ) ^ principalSignExp d p q *
        Complex.exp
          (sfExpArg (principalDoubleSineArg d (principalThirdIndex d p q) q - 1)
              (principalRoot d) +
            sfExpArg (principalDoubleSineArg d p (principalThirdIndex d p q) - 1)
              (principalRoot d) +
            sfExpArg (principalZ d p q) (principalRoot d)) = 1 := by
  have hc : (principalRankOneAdmissibleTuple ⟨d, hd⟩).conductorRatio = 1 :=
    principalRankOneAdmissibleTuple_conductorRatio ⟨d, hd⟩
  rw [RankOneAdmissibleTuple.sfPhase_of_conductorRatio_eq_one _ hc]
  simp only [principalRankOneAdmissibleTuple_d, principalRankOneAdmissibleTuple_Q]
  rw [rademacherInvariant_principalA d hd]
  have hz : principalZ d p q = principalDoubleSineArg d q p - 1 := by
    have := principalZ_add_one_eq d p q; linarith
  rw [hz, principal_sfExpArg_triple_eq d hd p q (principalThirdIndex d p q)]
  have hr := principalThirdIndex_eq_reductionJ d p q hp0 hp1 hq0 hq1 hne
  have hsign : sfSignExp d ![p, q] = (d : ℤ) + (1 + d) * (1 + p) * (1 + q) := by
    simp only [sfSignExp, show (![p, q] : IntPhaseSpace) 0 = p from rfl,
      show (![p, q] : IntPhaseSpace) 1 = q from rfl]
  have heval : (principalOneSICForm d).eval ((![p, q] : IntPhaseSpace) 0)
      ((![p, q] : IntPhaseSpace) 1) = p ^ 2 + (1 - (d : ℤ)) * p * q + q ^ 2 := by
    simp only [BinaryQF.eval, principalOneSICForm,
      show (![p, q] : IntPhaseSpace) 0 = p from rfl, show (![p, q] : IntPhaseSpace) 1 = q from rfl]
    ring
  rw [hsign, heval, displacementPhase_eq_exp]
  have hcast : ((3 * (d : ℚ) - 12 : ℚ) : ℂ) = 3 * (d : ℂ) - 12 := by push_cast; ring
  have hd0 : (d : ℂ) ≠ 0 := by
    exact_mod_cast (show (d : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr (by omega))
  rw [hcast, hr, principalSignExp]
  rw [show (-1 : ℂ) = Complex.exp (π * Complex.I) from Complex.exp_pi_mul_I.symm]
  simp only [← Complex.exp_int_mul]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  by_cases hcase : p + q ≤ (d : ℤ)
  · have hj : principalReductionJ d p q = 1 := ite_eq_left hcase
    rw [hj, min_eq_right hcase]
    obtain ⟨cp, hcp⟩ := Int.even_mul_pred_self p
    obtain ⟨cq, hcq⟩ := Int.even_mul_pred_self q
    have hcpC : (p : ℂ) * (p - 1) = (cp : ℂ) + cp := by exact_mod_cast hcp
    have hcqC : (q : ℂ) * (q - 1) = (cq : ℂ) + cq := by exact_mod_cast hcq
    rw [show (1 : ℂ) = Complex.exp
        (((1 - cp - cq + p * q + (d : ℤ) * (1 + p) * (1 + q) : ℤ) : ℂ) * (2 * π * Complex.I))
        from (Complex.exp_int_mul_two_pi_mul_I _).symm]
    congr 1
    push_cast
    field_simp
    linear_combination (-12 * (d : ℂ) ^ 2) * hcpC + (-12 * (d : ℂ) ^ 2) * hcqC
  · have hlt : (d : ℤ) < p + q := not_le.mp hcase
    have hj : principalReductionJ d p q = 2 := ite_eq_right hcase
    rw [hj, min_eq_left hlt.le]
    obtain ⟨cp, hcp⟩ := Int.even_mul_succ_self p
    obtain ⟨cq, hcq⟩ := Int.even_mul_succ_self q
    have hcpC : (p : ℂ) * (p + 1) = (cp : ℂ) + cp := by exact_mod_cast hcp
    have hcqC : (q : ℂ) * (q + 1) = (cq : ℂ) + cq := by exact_mod_cast hcq
    rw [show (1 : ℂ) = Complex.exp
        (((1 - cp - cq + p * q + (d : ℤ) * (2 + p + q + p * q) : ℤ) : ℂ) * (2 * π * Complex.I))
        from (Complex.exp_int_mul_two_pi_mul_I _).symm]
    congr 1
    push_cast
    field_simp
    linear_combination (-12 * (d : ℂ) ^ 2) * hcpC + (-12 * (d : ℂ) ^ 2) * hcqC

/-! ### Assembled identity under the explicit nonvanishing hypotheses

The `k`- and `ℓ`-product cancellations and the phase identity eliminate every finite correction in
the word-product formula. What remains is the exact three-double-sine overlap, provided the two
displayed finite products avoid zero.
-/

/-- **The reduction, fully closed away from poles.** Combining `principal_sf_reduction2` with
the `k`-pair collapse (`principal_qPoch_k_pair_eq_one`), the `ℓ`-pair collapse
(`principal_qPoch_ell_pair_eq_one`), and the phase identity
(`principal_phase_triple_exp_eq_one`): the entire finite correction is `1`, so
the SF cocycle value from the word product at `A_d`, times `Φ_d(p,q)`, equals the normalized overlap
`ν_d(p,q)` exactly, for every canonical `(p,q) ≠ (0,0)` under the nonvanishing hypotheses
`hnvK` and `hnvL`. Together with `sfPhase_zero_mul_sigmaSBase_zero_cube` (the origin case,
`SICs.Principal.Ghost.Origin`), this identifies the phased overlap `ν̃_d(p,q)` with the
product-side overlap `ν_d(p,q)` in every case. `SICs.Principal.Cocycle.Real` packages this
value as the real Shintani–Faddeev modular cocycle at `A_d`; the upper-half-plane infinite
product does not converge at real quadratic points. -/
theorem principal_sf_reduction2_eq_one (d : ℕ) (hd : 3 < d) (p q : ℤ)
    (hp0 : 0 ≤ p) (hp1 : p < (d : ℤ)) (hq0 : 0 ≤ q) (hq1 : q < (d : ℤ))
    (hne : ¬(p = 0 ∧ q = 0))
    (hnvK : qPochhammerFin (principalReductionK d p q)
        (principalDoubleSineArg d (principalThirdIndex d p q) q - 1) (principalRoot d) ≠ 0)
    (hnvL : qPochhammerFin (principalReductionL d p q)
        ((principalDoubleSineArg d (principalThirdIndex d p q) q - 1) / principalRoot d)
        (principalRoot d) ≠ 0) :
    (principalRankOneAdmissibleTuple ⟨d, hd⟩).sfPhase (principalA d) ![p, q] *
        (sigmaS (principalZ d p q) (principalRoot d) 0 0 *
          sigmaS (principalDoubleSineArg d p (principalThirdIndex d p q) - 1) (principalRoot d) 0
            (-principalReductionK d p q) *
          sigmaS (principalDoubleSineArg d (principalThirdIndex d p q) q - 1) (principalRoot d)
            (principalReductionK d p q) (-principalReductionL d p q)) /
        qPochhammerFin (-principalReductionL d p q)
          (principalZ d p q / principalJacobiFactor d) (principalRoot d) =
      (principalTripleDoubleSine d p q : ℂ) := by
  rw [principal_sf_reduction2 d hd p q]
  have hk := principal_qPoch_k_pair_eq_one d hd p q hp0 hp1 hq0 hq1 hne hnvK
  have hl := principal_qPoch_ell_pair_eq_one d hd p q hp0 hp1 hq0 hq1 hne hnvL
  have hphase := principal_phase_triple_exp_eq_one d hd p q hp0 hp1 hq0 hq1 hne
  have hB0 : qPochhammerFin (principalReductionK d p q)
      ((principalDoubleSineArg d p (principalThirdIndex d p q) - 1) / principalRoot d)
      (-1 / principalRoot d) ≠ 0 := by
    intro h0
    rw [h0, div_zero] at hk
    exact one_ne_zero hk.symm
  rw [div_eq_one_iff_eq hB0] at hk
  rw [hk]
  have hC0 : qPochhammerFin (principalReductionL d p q)
      ((principalDoubleSineArg d (principalThirdIndex d p q) q - 1) / principalRoot d)
      (-1 / principalRoot d) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hl; exact one_ne_zero hl.symm
  have hF0 : qPochhammerFin (-principalReductionL d p q)
      (principalZ d p q / principalJacobiFactor d) (principalRoot d) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hl; exact one_ne_zero hl.symm
  simp only [neg_div] at hB0 hC0 hl
  field_simp [hB0, hC0, hF0]
  linear_combination
    (-(principalTripleDoubleSine d p q : ℂ)) * hl + (principalTripleDoubleSine d p q : ℂ) * hphase

end SIC

end
