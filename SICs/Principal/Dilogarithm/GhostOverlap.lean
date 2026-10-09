/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Dilogarithm.Values
import SICs.Principal.Construction.ShiftSymmetry

/-!
# The Bridge Between the Finite Quantum Dilogarithm and the Phased Overlap

The identity `F(p/d) · ν̃_d(p) = ζ_d(p)` relating Radchenko and Wheeler's values on the
`d`-torsion to the phased principal ghost overlap, through the explicit root of unity
`ζ_d(p) = (-1)^{s_d(p)} ξ_d^{-Q_d(p)}`.

This module is project-local glue between [RW26, Radchenko, Wheeler (2026), Theorem 7,
`thm:ghostsic`] and the finite form of the principal Twisted Convolution Conjecture
`principalFiniteShiftTCC` of `SICs.Principal.Dilogarithm.TwistedConvolution`. The phased
overlap is `ν̃_d(p) = Φ_{t_d}(p) ש^{p/d}_{A_d}(ρ_d)` with the Shintani--Faddeev phase
`Φ_{t_d}(p) = (-1)^{s_d(p)} e^{-πiΨ(A_d)/12} ξ_d^{-Q_d(p)}` of
[AFK25, Definition 1.30, `dfn:SFKPhase`], and the value is `F(p/d) = μ_{A_d} / ש^{p/d}_{A_d}(ρ_d)`
with `μ_{A_d} = e^{πiΨ(A_d)/12}`, so the exponentials cancel:

$$
F(\mathbf p/d)\,\tilde\nu_d(\mathbf p) = \mu_{A_d}\,\Phi_{t_d}(\mathbf p)
  = (-1)^{s_d(\mathbf p)}\,\xi_d^{-Q_d(\mathbf p)} =: \zeta_d(\mathbf p).
$$

## The argument

Off the zero residue class, `F(p/d)` is `μ_{A_d}` over the principal cocycle
(`principalDilogValue_shiftRationalPoint`) and `ν̃_d(p)` is the phase times the same cocycle
(`principalPhasedGhostOverlap`), so the product is `μ_{A_d} Φ_{t_d}(p) = ζ_d(p)`
(`etaMultiplier_principalA_mul_sfPhase`). On the zero residue class `F(p/d) = √(j_{A_d}(ρ_d))`,
while `ν̃_d(p) = Φ_{t_d}(p) ש^0_{A_d}(ρ_d)` with the phase transported from the origin
(`principalSFPhase_transport`, at symplectic pairing `⟨p, 0⟩ = 0`) and the origin value
`Φ_{t_d}(0) ש^0_{A_d}(ρ_d) = ν_d(0) = -1/√(j_{A_d}(ρ_d))`
(`principalPhasedGhostOverlap_zero`, `principalNormGhostOverlapReal_zero_eq`); the product is
`-1`, which is `ζ_d(p)` on that class since `s_d(p)` is odd and `ξ_d^{d·(…)}` reduces to
`(-1)^{(d+1)(…)}` with `Q_d(p)` divisible by `d²`. So the identity holds at every integer index,
not only at canonical representatives: the quasi-periodic transport of `ν̃_d`
([AFK25, Lemma 5.7, `lem:nupperiodicity`]) is matched by that of `ζ_d`.

The Gaussian identity `ζ_d(p)² = ⟨p/d⟩⁻¹` follows from `ξ_d² = ω_d` (`displacementPhase_sq`) and
the Gaussian on `H` (`thetaCharacter_shiftRationalPoint_principalA`). The convolution law
`ξ_d^{⟨p, q⟩} ζ_d(q)/ζ_d(q - p) = -ζ_d(-p)⁻¹ ω_d^{-(p₁q₁ + p₂q₂ + p₁q₂)}`
(`principalDilogBridgePhase_convolution`) is the phase bookkeeping of the
conversion of Radchenko and Wheeler's convolution identity into the finite Twisted Convolution
Conjecture in `SICs.Principal.Dilogarithm.TwistedConvolution`: the `ξ_d`-exponent
`Q_d(q - p) - Q_d(q) + ⟨p, q⟩` is `Q_d(p)` plus even multiples and multiples of `d`, whose signs
combine with `(-1)^{s_d(q) - s_d(q - p)}` into a `q`-independent sign.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### The bridge phase `ζ_d`

`ζ_d(p) = (-1)^{s_d(p)} ξ_d^{-Q_d(p)}`, the Shintani--Faddeev phase without its eta factor. -/

/-- **The bridge phase** `ζ_d(p) = (-1)^{s_d(p)} ξ_d^{-Q_d(p)}`: the Shintani--Faddeev phase
`Φ_{t_d}(p)` of [AFK25, Definition 1.30, `dfn:SFKPhase`] multiplied by the eta multiplier
`μ_{A_d} = e^{πiΨ(A_d)/12}` (`etaMultiplier_principalA_mul_sfPhase`), and the value of
`F(p/d) ν̃_d(p)` (`principalDilogValue_mul_phasedGhostOverlap`). -/
def principalDilogBridgePhase (d : ℕ) [NeZero d] (p : IntPhaseSpace) : ℂ :=
  (-1 : ℂ) ^ sfSignExp d p * displacementPhase d ^ (-(principalOneSICForm d).eval (p 0) (p 1))

/-- `μ_{A_d} Φ_{t_d}(p) = ζ_d(p)`: the eta exponentials cancel
(`RankOneAdmissibleTuple.sfPhase_of_conductorRatio_eq_one`,
`principalRankOneAdmissibleTuple_conductorRatio`). -/
theorem etaMultiplier_principalA_mul_sfPhase (d : RankOneDimension) (p : IntPhaseSpace) :
    etaMultiplier (principalA d) *
        (principalRankOneAdmissibleTuple d).sfPhase (principalA d) p =
      principalDilogBridgePhase d p := by
  rw [RankOneAdmissibleTuple.sfPhase_of_conductorRatio_eq_one _
    (principalRankOneAdmissibleTuple_conductorRatio d)]
  change Complex.exp (Real.pi * Complex.I / 12 * (rademacherInvariant (principalA d) : ℂ)) *
      ((-1 : ℂ) ^ sfSignExp d p *
        Complex.exp (-Real.pi * Complex.I / 12 *
          (rademacherInvariant (principalA d) : ℂ)) *
        displacementPhase d ^ (-(principalOneSICForm d).eval (p 0) (p 1))) = _
  rw [show -Real.pi * Complex.I / 12 * (rademacherInvariant (principalA d) : ℂ) =
    -(Real.pi * Complex.I / 12 * (rademacherInvariant (principalA d) : ℂ)) by ring]
  rw [← mul_assoc, mul_left_comm, mul_assoc, ← Complex.exp_add, add_neg_cancel,
    Complex.exp_zero, one_mul]
  rfl

/-- `ζ_d(p) ≠ 0`. -/
theorem principalDilogBridgePhase_ne_zero (d : ℕ) [NeZero d] (p : IntPhaseSpace) :
    principalDilogBridgePhase d p ≠ 0 :=
  mul_ne_zero (zpow_ne_zero _ (by norm_num)) (zpow_ne_zero _ (displacementPhase_ne_zero d))

/-- **`ζ_d(p)² = ⟨p/d⟩⁻¹`**: `ξ_d² = ω_d` and `⟨p/d⟩ = ω_d^{Q_d(p)}`
(`thetaCharacter_shiftRationalPoint_principalA`). -/
theorem principalDilogBridgePhase_sq (d : ℕ) [NeZero d] (p : IntPhaseSpace) :
    principalDilogBridgePhase d p ^ 2 =
      (thetaCharacter (shiftRationalPoint d p) (principalA d : Mat(2, ℤ)))⁻¹ := by
  rw [thetaCharacter_shiftRationalPoint_principalA d p]
  unfold principalDilogBridgePhase
  have hsign : ((-1 : ℂ) ^ sfSignExp d p) ^ 2 = 1 := by
    rw [← zpow_natCast, ← zpow_mul]
    exact Even.neg_one_zpow ⟨sfSignExp d p, by ring⟩
  have hphase (n : ℤ) : (displacementPhase d ^ n) ^ 2 = standardRoot d ^ n := by
    calc
      _ = (displacementPhase d ^ 2) ^ n := by
        simp only [← zpow_natCast]
        rw [← zpow_mul, ← zpow_mul]
        congr 1
        ring
      _ = _ := by rw [displacementPhase_sq]
  rw [mul_pow, hsign, one_mul, hphase, zpow_neg]

/-- The exponent of `ξ_d` in the quotient of bridge phases. -/
private lemma bridgePhase_exponent (d : ℕ) (p q : IntPhaseSpace) :
    intSymplecticForm p q - (principalOneSICForm d).eval (q 0) (q 1) +
        (principalOneSICForm d).eval ((q - p) 0) ((q - p) 1) =
      (principalOneSICForm d).eval (p 0) (p 1) +
        (d : ℤ) * (p 1 * q 0 + p 0 * q 1) -
        2 * (p 0 * q 0 + p 1 * q 1 + p 0 * q 1) := by
  simp only [intSymplecticForm, principalOneSICForm, BinaryQF.eval, Pi.sub_apply]
  ring

/-- The signs from the quotient and the `d`-multiple phase agree with the inverse phase. -/
private lemma bridgePhase_sign (d : ℕ) (p q : IntPhaseSpace) :
    (-1 : ℂ) ^ (sfSignExp d q - sfSignExp d (q - p) +
        ((d + 1 : ℕ) : ℤ) * (p 1 * q 0 + p 0 * q 1)) =
      -(((-1 : ℂ) ^ sfSignExp d (-p))⁻¹) := by
  have h : sfSignExp d q - sfSignExp d (q - p) +
        ((d + 1 : ℕ) : ℤ) * (p 1 * q 0 + p 0 * q 1) =
      sfSignExp d (-p) + 1 +
        2 * (((d : ℤ) + 1) *
          (q 0 * p 1 + q 1 * p 0 - p 0 * p 1 + p 0 + p 1 - 1)) := by
    simp only [sfSignExp, Pi.sub_apply, Pi.neg_apply, Nat.cast_add, Nat.cast_one]
    ring
  rw [h, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  have heven : Even (2 * (((d : ℤ) + 1) *
      (q 0 * p 1 + q 1 * p 0 - p 0 * p 1 + p 0 + p 1 - 1))) :=
    ⟨((d : ℤ) + 1) *
      (q 0 * p 1 + q 1 * p 0 - p 0 * p 1 + p 0 + p 1 - 1), by ring⟩
  rw [heven.neg_one_zpow, mul_one, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  simp only [zpow_one, mul_neg, mul_one]
  congr 1
  rw [← inv_zpow, inv_neg_one]

/-- Multiplication by a phase and division of two signed phases combine their exponents. -/
private lemma bridgePhase_quotient (x : ℂ) (hx : x ≠ 0) (a b c u v : ℤ) :
    x ^ a * (((-1 : ℂ) ^ u * x ^ b) / ((-1 : ℂ) ^ v * x ^ c)) =
      (-1 : ℂ) ^ (u - v) * x ^ (a + b - c) := by
  rw [zpow_sub₀ (by norm_num : (-1 : ℂ) ≠ 0),
    zpow_sub₀ hx, zpow_add₀ hx]
  have hs : (-1 : ℂ) ^ v ≠ 0 := zpow_ne_zero _ (by norm_num)
  have hc : x ^ c ≠ 0 := zpow_ne_zero _ hx
  field_simp

/-- The quadratic exponent splits into a principal phase, a parity sign, and an `ω_d` power. -/
private lemma bridgePhase_power (d : ℕ) [NeZero d] (p q : IntPhaseSpace) :
    displacementPhase d ^ (intSymplecticForm p q -
        (principalOneSICForm d).eval (q 0) (q 1) +
        (principalOneSICForm d).eval ((q - p) 0) ((q - p) 1)) =
      displacementPhase d ^ (principalOneSICForm d).eval (p 0) (p 1) *
        (-1 : ℂ) ^ (((d + 1 : ℕ) : ℤ) * (p 1 * q 0 + p 0 * q 1)) *
        standardRoot d ^ (-(p 0 * q 0 + p 1 * q 1 + p 0 * q 1)) := by
  have hx := displacementPhase_ne_zero d
  have htwo (n : ℤ) : displacementPhase d ^ (2 * n) = standardRoot d ^ n := by
    rw [zpow_mul]
    have h : displacementPhase d ^ (2 : ℤ) = standardRoot d :=
      (zpow_natCast (displacementPhase d) 2).trans (displacementPhase_sq d)
    rw [h]
  calc
    _ = displacementPhase d ^ ((principalOneSICForm d).eval (p 0) (p 1) +
        (d : ℤ) * (p 1 * q 0 + p 0 * q 1) -
        2 * (p 0 * q 0 + p 1 * q 1 + p 0 * q 1)) := by
      rw [bridgePhase_exponent]
    _ = _ := by
      rw [show (principalOneSICForm d).eval (p 0) (p 1) +
          (d : ℤ) * (p 1 * q 0 + p 0 * q 1) -
          2 * (p 0 * q 0 + p 1 * q 1 + p 0 * q 1) =
          (principalOneSICForm d).eval (p 0) (p 1) +
          (d : ℤ) * (p 1 * q 0 + p 0 * q 1) +
          2 * (-(p 0 * q 0 + p 1 * q 1 + p 0 * q 1)) by ring]
      rw [zpow_add₀ hx, zpow_add₀ hx, displacementPhase_zpow_d_mul, htwo]

/-- The bridge-phase quotient has the difference of its sign and quadratic exponents. -/
private lemma bridgePhase_quotient_principal (d : ℕ) [NeZero d] (p q : IntPhaseSpace) :
    displacementPhase d ^ intSymplecticForm p q *
        (principalDilogBridgePhase d q / principalDilogBridgePhase d (q - p)) =
      (-1 : ℂ) ^ (sfSignExp d q - sfSignExp d (q - p)) *
        displacementPhase d ^ (intSymplecticForm p q -
          (principalOneSICForm d).eval (q 0) (q 1) +
          (principalOneSICForm d).eval ((q - p) 0) ((q - p) 1)) := by
  change displacementPhase d ^ intSymplecticForm p q *
    (((-1 : ℂ) ^ sfSignExp d q *
      displacementPhase d ^ (-(principalOneSICForm d).eval (q 0) (q 1))) /
      ((-1 : ℂ) ^ sfSignExp d (q - p) *
        displacementPhase d ^ (-(principalOneSICForm d).eval ((q - p) 0) ((q - p) 1)))) = _
  convert bridgePhase_quotient (displacementPhase d) (displacementPhase_ne_zero d)
    (intSymplecticForm p q) (-(principalOneSICForm d).eval (q 0) (q 1))
    (-(principalOneSICForm d).eval ((q - p) 0) ((q - p) 1))
    (sfSignExp d q) (sfSignExp d (q - p)) using 1; ring_nf

/-- **The convolution law of the bridge phase**:
`ξ_d^{⟨p, q⟩} ζ_d(q) / ζ_d(q - p) = -ζ_d(-p)⁻¹ ω_d^{-(p₁q₁ + p₂q₂ + p₁q₂)}`, with the symplectic
form `⟨p, q⟩ = p₂q₁ - p₁q₂`. The sign `(-1)^{s_d(q) - s_d(q - p)}` and the parity of the
`ξ_d`-exponent `Q_d(q - p) - Q_d(q) + ⟨p, q⟩` combine into a `q`-independent sign, and the
`q`-dependence is the character `ω_d^{-(p₁q₁ + p₂q₂ + p₁q₂)}` of `(ℤ/dℤ)²`. This is the phase
bookkeeping that turns the finite Twisted Convolution sum into Radchenko and Wheeler's convolution
identity, sensitive to the transport signs in even dimensions. -/
theorem principalDilogBridgePhase_convolution (d : ℕ) [NeZero d]
    (p q : IntPhaseSpace) :
    displacementPhase d ^ intSymplecticForm p q *
        (principalDilogBridgePhase d q / principalDilogBridgePhase d (q - p)) =
      -(principalDilogBridgePhase d (-p))⁻¹ *
        standardRoot d ^ (-(p 0 * q 0 + p 1 * q 1 + p 0 * q 1)) := by
  let X := displacementPhase d
  let S := fun r : IntPhaseSpace => sfSignExp d r
  let Q := fun r : IntPhaseSpace => (principalOneSICForm d).eval (r 0) (r 1)
  let C : ℤ := p 1 * q 0 + p 0 * q 1
  let T : ℤ := p 0 * q 0 + p 1 * q 1 + p 0 * q 1
  have hpow : X ^ (intSymplecticForm p q - Q q + Q (q - p)) =
      X ^ Q p * (-1 : ℂ) ^ (((d + 1 : ℕ) : ℤ) * C) * standardRoot d ^ (-T) :=
    bridgePhase_power d p q
  have hsign : (-1 : ℂ) ^ (S q - S (q - p)) *
      (-1 : ℂ) ^ (((d + 1 : ℕ) : ℤ) * C) =
      -(((-1 : ℂ) ^ S (-p))⁻¹) := by
    rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    exact bridgePhase_sign d p q
  calc
    _ = (-1 : ℂ) ^ (S q - S (q - p)) *
        X ^ (intSymplecticForm p q - Q q + Q (q - p)) :=
      bridgePhase_quotient_principal d p q
    _ = (-1 : ℂ) ^ (S q - S (q - p)) *
        (X ^ Q p * (-1 : ℂ) ^ (((d + 1 : ℕ) : ℤ) * C) *
          standardRoot d ^ (-T)) := by rw [hpow]
    _ = -(((-1 : ℂ) ^ S (-p))⁻¹) * (X ^ Q p * standardRoot d ^ (-T)) := by
      rw [← hsign]
      ring
    _ = _ := by
      dsimp [S, Q, T, X]
      rw [principalDilogBridgePhase, mul_inv_rev]
      simp only [Pi.neg_apply, BinaryQF.eval_neg, zpow_neg, inv_inv]
      ring

/-! ### The bridge

`F(p/d) ν̃_d(p) = ζ_d(p)` at every integer index. -/

/-- On the zero residue class the bridge phase is `-1`, by phase transport from the origin
(`principalSFPhase_of_mod_eq_zero`). -/
theorem principalDilogBridgePhase_of_mod_eq_zero (d : RankOneDimension)
    (p : IntPhaseSpace) (hp : intPhaseSpaceMod d p = 0) :
    principalDilogBridgePhase d p = -1 := by
  have hconst : principalDilogBridgePhase d p = principalDilogBridgePhase d 0 := by
    calc
      _ = etaMultiplier (principalA d) *
            (principalRankOneAdmissibleTuple d).sfPhase (principalA d) p :=
        (etaMultiplier_principalA_mul_sfPhase d p).symm
      _ = etaMultiplier (principalA d) *
            (principalRankOneAdmissibleTuple d).sfPhase (principalA d) 0 := by
        rw [principalSFPhase_of_mod_eq_zero d p hp]
      _ = _ := etaMultiplier_principalA_mul_sfPhase d 0
  rw [hconst]
  have hsign : sfSignExp d (0 : IntPhaseSpace) = 2 * (d : ℤ) + 1 := by
    simp [sfSignExp]
    ring
  simp [principalDilogBridgePhase, hsign, Odd.neg_one_zpow
    (show Odd (2 * (d : ℤ) + 1) from ⟨d, rfl⟩), principalOneSICForm, BinaryQF.eval]

/-- **The bridge** between the finite quantum dilogarithm of
[RW26, Radchenko, Wheeler (2026), equation (37), `eq:fgam.defalt`] and the phased principal
ghost overlap `ν̃_d(p) = Φ_{t_d}(p) ש^{p/d}_{A_d}(ρ_d)` of
[AFK25, Definition 1.32, `dfn:GhostOverlaps`]: `F(p/d) · ν̃_d(p) = ζ_d(p)` for every `p ∈ ℤ²`.
Off the zero residue class the cocycles cancel and `μ_{A_d} Φ_{t_d}(p) = ζ_d(p)`; on it both
sides are `-1`. See the module docstring. -/
theorem principalDilogValue_mul_phasedGhostOverlap (d : RankOneDimension)
    (p : IntPhaseSpace) :
    principalDilogValue d (shiftRationalPoint d p) * principalPhasedGhostOverlap d p =
      principalDilogBridgePhase d p := by
  by_cases hp : intPhaseSpaceMod d p = 0
  · have hoverlap : principalPhasedGhostOverlap d p =
        -(((Real.sqrt (principalJacobiFactor d) : ℝ) : ℂ))⁻¹ := by
      rw [principalPhasedGhostOverlap_of_mod_eq_zero d p hp,
        principalPhasedGhostOverlap_zero]
      rw [← ofReal_principalNormGhostOverlapReal d (0 : IntPhaseSpace),
        principalNormGhostOverlapReal_zero_eq d]
      push_cast
      rfl
    rw [principalDilogValue_shiftRationalPoint_eq_sqrt d d.property p hp,
      hoverlap, principalDilogBridgePhase_of_mod_eq_zero d p hp]
    have hsqrt : ((Real.sqrt (principalJacobiFactor d) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_ne_zero'.mpr (principalJacobiFactor_pos d d.property))
    field_simp
  · rw [principalDilogValue_shiftRationalPoint d d.property p hp,
      principalPhasedGhostOverlap]
    have hc := principalSFModularCocycleAd_ne_zero d p
    calc
      _ = etaMultiplier (principalA d) *
            (principalRankOneAdmissibleTuple d).sfPhase (principalA d) p := by
        field_simp
      _ = _ := etaMultiplier_principalA_mul_sfPhase d p

end SIC

end
