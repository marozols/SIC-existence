/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Ghost.CandidateOverlaps
import SICs.Cocycle.FixedPointCharacter

/-!
# The Reciprocal Identity for Candidate Normalized Overlaps

The reciprocal clause of Theorem 5.8 for every admissible tuple.

This file proves the reciprocal half of [AFK25, Theorem 5.8, `thm:nupnumpeq1`] for the candidate
normalized ghost overlaps of an arbitrary admissible tuple `t` with an associated stabilizer pair
`(A_t, L_{z,t})`:

`ν̃_t(p) ν̃_t(-p) = 1`  whenever `p ≢ 0 (mod d)`.

## Mathematical argument

`ν̃_t(p) = Φ_t(p) ש^{p/d}_{A_t}(ρ_t)` is a phase times a Shintani--Faddeev cocycle value. The
fixed-point character theorem `sfModularCocycleReal_mul_neg_eq_character` gives
`ש^{p/d}_{A_t}(ρ_t) ש^{-p/d}_{A_t}(ρ_t) = ψ²(A_t)χ_{p/d}(A_t)`, as in the source proof.
Membership in `Γ_{p/d}` supplies integers `m,n` with `A_t p = p - d(m,n)`.
The simplified theta character `thetaCharacter_eq_exp`, with witnesses `-m,-n`, writes this
product as the exponential of `πi` times

`n - m - mn - ⟨A_t p,p⟩/d² + Ψ(A_t)/6`.

The square of the phase contributes `-Ψ(A_t)/6 - 2(f_{jm}/f)Q(p)/d`. The bridge between the two is
the source's computation inside the proof of [AFK25, Theorem 5.6, `thm:phaserelation`]:

`⟨A_t p, p⟩ = (d² f_j/f - 2d f_{jm}/f) Q(p)`,

turns the pairing term into the required quadratic-form terms. It follows from
the closed form `A_t - I = dH` of the level generator
(`AdmissibleTuple.IsAssociatedStabilizerPair.twice_A_sub_one_eq`) together with two elementary
pairing facts: a scalar matrix pairs a vector with itself to zero, and `2SQ` pairs it to `2Q(p)`.
So only the `2SQ` part of `A_t` survives. Finally [AFK25, Lemma 5.5, `lem:drafjfqp`] says exactly
that the remaining integer exponent is even.

The word cocycle is defined directly only for nonnegative lower-left entry. When `A_t` has negative
lower-left entry, its total form uses `A_t⁻¹`; `rademacherInvariant_inv` gives
`Ψ(A_t⁻¹) = -Ψ(A_t)`, the symplectic self-pairing changes sign, and the same parity statement is
transported through the inverse matrix. `IsAssociatedStabilizerPair.lowerLeft_A_ne_zero` ensures
these two orientation cases exhaust all associated stabilizers.

## References

- [AFK25] Appleby, Flammia, Kopp, arXiv:2501.03970v2, Theorems 5.6 and 5.8
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

namespace AdmissibleTuple

/-! ### The level generator against the quadratic form

The symplectic pairing `⟨Mp, p⟩` sees only the traceless part of `M`.  For the level generator
that part is a multiple of `2SQ`, so the pairing is a multiple of `Q(p)`, with the multiplier read
off the closed form of `A_t`.  This is the dictionary the reciprocal identity needs, since the
Shintani--Faddeev phase carries `Q(p)` while the cocycle reflection carries matrix entries. -/

/-- The symplectic pairing of `Mp` with `p`, in terms of the entries of `M`.  The diagonal enters
only through `M₁₁ - M₀₀`, so scalar matrices pair to zero. -/
private lemma intSymplecticForm_mulVec_self (M : Mat(2, ℤ)) (p : IntPhaseSpace) :
    intSymplecticForm (Matrix.mulVec M p) p =
      M 1 0 * p 0 ^ 2 + (M 1 1 - M 0 0) * (p 0 * p 1) - M 0 1 * p 1 ^ 2 := by
  simp only [intSymplecticForm, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- A matrix whose doubled shift `2(M - I)` is a combination of `I` and `2SQ` pairs a vector with
itself to the `2SQ` coefficient times `Q`: the `I` part contributes nothing, because
`intSymplecticForm_mulVec_self` sees the diagonal only through `M₁₁ - M₀₀`. -/
private lemma intSymplecticForm_mulVec_self_of_twice_sub_one_eq {M : Mat(2, ℤ)}
    {Q : BinaryQF} {c₁ c₂ : ℤ}
    (hM : (2 : ℤ) • (M - 1) =
      c₁ • (1 : Mat(2, ℤ)) + c₂ • Q.twiceSQ) (p : IntPhaseSpace) :
    intSymplecticForm (Matrix.mulVec M p) p = c₂ * Q.eval (p 0) (p 1) := by
  have e00 := congrFun (congrFun hM 0) 0
  have e01 := congrFun (congrFun hM 0) 1
  have e10 := congrFun (congrFun hM 1) 0
  have e11 := congrFun (congrFun hM 1) 1
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply,
    smul_eq_mul] at e00 e01 e10 e11
  simp only [Fin.isValue, Matrix.one_apply_eq, mul_one, BinaryQF.twiceSQ, Int.reduceNeg, neg_mul,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, mul_neg,
    ne_eq, zero_ne_one, not_false_eq_true, Matrix.one_apply_ne, sub_zero, mul_zero,
    Matrix.cons_val_one, zero_add, one_ne_zero] at e00 e01 e10 e11
  have h10 : M 1 0 = c₂ * Q.a := by linarith
  have h01 : M 0 1 = -(c₂ * Q.c) := by linarith
  have hdiag : M 1 1 - M 0 0 = c₂ * Q.b := by linarith
  rw [intSymplecticForm_mulVec_self, BinaryQF.eval]
  linear_combination (p 0 ^ 2) * h10 + (p 0 * p 1) * hdiag - (p 1 ^ 2) * h01

/-- **The level generator pairs to the quadratic form.**  This is the computation displayed in the
proof of [AFK25, Theorem 5.6, `thm:phaserelation`]:

`⟨A_t p, p⟩ = (d² f_j/f - 2d f_{jm}/f) Q(p)`,

for every integer index `p`.  Both conductor ratios are the exact quotients
`AdmissibleTuple.towerConductorRatio` and `AdmissibleTuple.conductorRatio`.

The source derives it from `A_t - I = dH` of [AFK25, equation (5.26), `eq:amidjmh`], which is
`IsAssociatedStabilizerPair.twice_A_sub_one_eq` here; the scalar part of that closed form drops
out of the pairing, and `conductorRatio_eq_rank_mul` converts the surviving coefficient
`d (r_{j,m+1} - r_{j,m}) f_j/f` into the source's form. -/
theorem IsAssociatedStabilizerPair.intSymplecticForm_A_mulVec_self {t : AdmissibleTuple}
    {A_t Lz : SL(2, ℤ)} (h : t.IsAssociatedStabilizerPair A_t Lz) (p : IntPhaseSpace) :
    intSymplecticForm (Matrix.mulVec (A_t : Mat(2, ℤ)) p) p =
      ((t.d : ℤ) ^ 2 * (t.towerConductorRatio : ℤ) -
        2 * (t.d : ℤ) * (t.conductorRatio : ℤ)) * t.Q.eval (p 0) (p 1) := by
  have hdim : (t.d : ℤ) =
      t.triple.tower.rankGridInt t.triple.j ((t.triple.m : ℕ) + 1) +
        t.triple.tower.rankGridInt t.triple.j (t.triple.m : ℕ) := by
    rw [t.d_eq_dimension]
    exact t.triple.tower.dimensionGrid_coe_int t.triple.j t.triple.m
  have hrank : (t.triple.rank : ℤ) =
      t.triple.tower.rankGridInt t.triple.j (t.triple.m : ℕ) :=
    t.triple.tower.rankGrid_coe_int t.triple.j t.triple.m
  have hratio : (t.conductorRatio : ℤ) =
      t.triple.tower.rankGridInt t.triple.j (t.triple.m : ℕ) * (t.towerConductorRatio : ℤ) := by
    rw [← hrank]
    exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) t.conductorRatio_eq_rank_mul
  have hcoef : (t.d : ℤ) *
      (t.triple.tower.rankGridInt t.triple.j ((t.triple.m : ℕ) + 1) -
        t.triple.tower.rankGridInt t.triple.j (t.triple.m : ℕ)) *
      (t.towerConductorRatio : ℤ) =
      (t.d : ℤ) ^ 2 * (t.towerConductorRatio : ℤ) -
        2 * (t.d : ℤ) * (t.conductorRatio : ℤ) := by
    linear_combination (-(t.d : ℤ) * (t.towerConductorRatio : ℤ)) * hdim +
      (2 * (t.d : ℤ)) * hratio
  rw [← hcoef]
  exact intSymplecticForm_mulVec_self_of_twice_sub_one_eq h.twice_A_sub_one_eq p

end AdmissibleTuple

/-! ### The reflected character product

At an irrational fixed point, the shared character theorem gives the reflected product as
`ψ²(M)χ_{p/d}(M)`. Its integrality witnesses `k₁,k₂` give `Mp = p + d(k₁,k₂)`.
The simplified theta character evaluates this product; choosing `m = -k₁`, `n = -k₂` gives the
exponential used by both orientation branches, since the exponents differ by
`2πi(k₁k₂ + k₂)`. This is the character argument in [AFK25, Theorem 5.8, `thm:nupnumpeq1`]. -/

/-- The reflected character product with explicit integrality witnesses, used by
`sfModularCocycleReal_mul_neg_shift_eq_exp`. This specializes
`sfModularCocycleReal_mul_neg_eq_character` and `thetaCharacter_eq_exp`
to `r = p/d`. -/
private lemma reflectedCocycle_eq_exp_of_witnesses {d : ℕ} (hd : 0 < d) {M : SL(2, ℤ)}
    (p : IntPhaseSpace) {τ : ℝ} (hτ : Irrational τ)
    (hlat : SigmaSLatticeFree τ
      (fracSymplecticFormRat (shiftRationalPoint d p) τ))
    (hM : M ∈ gammaSubgroup (shiftRationalPoint d p))
    (hpos : 0 < M 1 0)
    (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) τ)
    (hfix : flt (M : Mat(2, ℤ)) τ = τ) (k₁ k₂ : ℤ)
    (hk₁ : ((M 0 0 : ℚ) - 1) * shiftRationalPoint d p 0 +
      (M 0 1 : ℚ) * shiftRationalPoint d p 1 = k₁)
    (hk₂ : (M 1 0 : ℚ) * shiftRationalPoint d p 0 +
      ((M 1 1 : ℚ) - 1) * shiftRationalPoint d p 1 = k₂)
    (hq₀ : Matrix.mulVec (M : Mat(2, ℤ)) p 0 = p 0 + (d : ℤ) * k₁)
    (hq₁ : Matrix.mulVec (M : Mat(2, ℤ)) p 1 = p 1 + (d : ℤ) * k₂) :
    sfModularCocycleReal (shiftRationalPoint d p) M hM hpos.le τ *
      sfModularCocycleReal (-(shiftRationalPoint d p)) M
        (neg_mem_gammaSubgroup hM) hpos.le τ =
      Complex.exp (Real.pi * Complex.I *
        ((((-k₂ - -k₁ - (-k₁) * (-k₂) : ℤ) : ℂ) -
          ((intSymplecticForm
            (Matrix.mulVec (M : Mat(2, ℤ)) p) p : ℤ) : ℂ) /
            ((d : ℂ) ^ 2)) + ((rademacherInvariant M : ℚ) : ℂ) / 6)) := by
  have hr : ¬ IsIntegralIndex (shiftRationalPoint d p) := by
    intro h
    obtain ⟨a, ha⟩ := h 1
    obtain ⟨b, hb⟩ := h 0
    apply hlat a (-b)
    simp [fracSymplecticFormRat, ha, hb, sub_eq_add_neg]
  rw [sfModularCocycleReal_mul_neg_eq_character hτ hr hM
    hpos.le hjac hfix, thetaCharacter_eq_exp M hk₁ hk₂,
    etaMultiplierSq_eq_of_trace_pos (trace_pos_of_flt_eq_self hfix hjac)]
  rw [← Complex.exp_add]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨k₁ * k₂ + k₂, ?_⟩
  simp only [intSymplecticForm, hq₀, hq₁, shiftRationalPoint]
  push_cast
  field_simp [show (d : ℂ) ≠ 0 by exact_mod_cast hd.ne']
  ring

/-- The reflected real word-cocycle product at the fixed point, in the exponential form used in
the proof of [AFK25, Theorem 5.8, `thm:nupnumpeq1`]:

`ש^{p/d}_M(τ) ש^{-p/d}_M(τ)
  = exp(πi(n-m-mn-⟨Mp,p⟩/d²+Ψ(M)/6))`.

This is the specialization of `sfModularCocycleReal_mul_neg_eq_character`
to `r = p/d`, through `reflectedCocycle_eq_exp_of_witnesses`. -/
private lemma sfModularCocycleReal_mul_neg_shift_eq_exp {d : ℕ} (hd : 0 < d)
    {M : SL(2, ℤ)} (p : IntPhaseSpace) {τ : ℝ} (hτ : Irrational τ)
    (hM : M ∈ gammaSubgroup (shiftRationalPoint d p))
    (hpos : 0 < M 1 0)
    (hjac : 0 < fltDenominator (M : Mat(2, ℤ)) τ)
    (hfix : flt (M : Mat(2, ℤ)) τ = τ)
    (hlat : SigmaSLatticeFree τ
      (fracSymplecticFormRat (shiftRationalPoint d p) τ)) :
    ∃ m n : ℤ,
      Matrix.mulVec (M : Mat(2, ℤ)) p 0 = p 0 - (d : ℤ) * m ∧
      Matrix.mulVec (M : Mat(2, ℤ)) p 1 = p 1 - (d : ℤ) * n ∧
      sfModularCocycleReal (shiftRationalPoint d p) M hM hpos.le τ *
          sfModularCocycleReal (-(shiftRationalPoint d p)) M
            (neg_mem_gammaSubgroup hM) hpos.le τ =
        Complex.exp (Real.pi * Complex.I *
          ((((n - m - m * n : ℤ) : ℂ) -
              ((intSymplecticForm
                (Matrix.mulVec (M : Mat(2, ℤ)) p) p : ℤ) : ℂ) /
                ((d : ℂ) ^ 2)) +
            ((rademacherInvariant M : ℚ) : ℂ) / 6)) := by
  obtain ⟨k₁, hk₁⟩ := hM 0
  obtain ⟨k₂, hk₂⟩ := hM 1
  rw [Fin.sum_univ_two] at hk₁ hk₂
  norm_num at hk₁ hk₂
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hq₀ : Matrix.mulVec (M : Mat(2, ℤ)) p 0 =
      p 0 + (d : ℤ) * k₁ := by
    have hk := hk₁
    simp only [shiftRationalPoint] at hk
    field_simp [hdQ] at hk
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have hkZ : (M 0 0 - 1) * p 0 + M 0 1 * p 1 = (d : ℤ) * k₁ := by
      exact_mod_cast hk
    linear_combination hkZ
  have hq₁ : Matrix.mulVec (M : Mat(2, ℤ)) p 1 =
      p 1 + (d : ℤ) * k₂ := by
    have hk := hk₂
    simp only [shiftRationalPoint] at hk
    field_simp [hdQ] at hk
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have hkZ : M 1 0 * p 0 + (M 1 1 - 1) * p 1 = (d : ℤ) * k₂ := by
      exact_mod_cast hk
    linear_combination hkZ
  refine ⟨-k₁, -k₂, by simpa using hq₀, by simpa using hq₁, ?_⟩
  exact reflectedCocycle_eq_exp_of_witnesses hd p hτ hlat hM hpos hjac hfix
    k₁ k₂ hk₁ hk₂ hq₀ hq₁

/-! ### Phase and parity

Squaring removes the sign in the SF phase. The remaining exponential cancels the cocycle formula
up to an integer whose evenness is precisely [AFK25, Lemma 5.5, `lem:drafjfqp`]. -/

/-- The square of the SF phase: the parity sign disappears, the Rademacher exponent doubles, and
`displacementPhase² = standardRoot` converts the quadratic factor to a standard exponential.
This is the phase calculation in the proof of [AFK25, Theorem 5.8, `thm:nupnumpeq1`]. -/
private lemma sfPhase_sq_eq_exp (t : AdmissibleTuple) (M : SL(2, ℤ)) (p : IntPhaseSpace) :
    t.sfPhase M p ^ 2 =
      Complex.exp (-Real.pi * Complex.I / 6 * ((rademacherInvariant M : ℚ) : ℂ)) *
        Complex.exp (((-((t.conductorRatio : ℤ) * t.Q.eval (p 0) (p 1)) : ℤ) : ℂ) *
          (2 * Real.pi * Complex.I / (t.d : ℂ))) := by
  let s := sfSignExp t.d p
  let F : ℤ := (t.conductorRatio : ℤ) * t.Q.eval (p 0) (p 1)
  have hsign : ((-1 : ℂ) ^ s) * ((-1 : ℂ) ^ s) = 1 := by
    rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    exact Even.neg_one_zpow ⟨s, by ring⟩
  have hexp :
      Complex.exp (-Real.pi * Complex.I / 12 * ((rademacherInvariant M : ℚ) : ℂ)) *
          Complex.exp (-Real.pi * Complex.I / 12 * ((rademacherInvariant M : ℚ) : ℂ)) =
        Complex.exp (-Real.pi * Complex.I / 6 * ((rademacherInvariant M : ℚ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hroot : displacementPhase t.d ^ (-F) * displacementPhase t.d ^ (-F) =
      Complex.exp ((-F : ℤ) * (2 * Real.pi * Complex.I / (t.d : ℂ))) := by
    rw [← zpow_add₀ (displacementPhase_ne_zero t.d),
      show -F + -F = (2 : ℤ) * (-F) by ring, zpow_mul, zpow_ofNat,
      displacementPhase_sq, standardRoot, ← Complex.exp_int_mul]
  rw [AdmissibleTuple.sfPhase, pow_two]
  change (((-1 : ℂ) ^ s *
      Complex.exp (-Real.pi * Complex.I / 12 * ((rademacherInvariant M : ℚ) : ℂ)) *
      displacementPhase t.d ^ (-F)) *
    ((-1 : ℂ) ^ s *
      Complex.exp (-Real.pi * Complex.I / 12 * ((rademacherInvariant M : ℚ) : ℂ)) *
      displacementPhase t.d ^ (-F))) = _
  calc
    _ = (((-1 : ℂ) ^ s) * ((-1 : ℂ) ^ s)) *
        (Complex.exp (-Real.pi * Complex.I / 12 * ((rademacherInvariant M : ℚ) : ℂ)) *
          Complex.exp (-Real.pi * Complex.I / 12 * ((rademacherInvariant M : ℚ) : ℂ))) *
        (displacementPhase t.d ^ (-F) * displacementPhase t.d ^ (-F)) := by ring
    _ = _ := by rw [hsign, hexp, hroot]; ring

/-- If `m,n` are simultaneously even exactly when `Q` is even, then `n-m-mn-Q` is even. This is
the elementary parity step consumed by the positive-orientation branch. -/
private lemma reflection_parity {m n Q : ℤ} (h : (Even m ∧ Even n) ↔ Even Q) :
    Even (n - m - m * n - Q) := by
  rcases Int.even_or_odd m with hm | hm <;>
    rcases Int.even_or_odd n with hn | hn
  · have hQ := h.mp ⟨hm, hn⟩
    exact ((hn.sub hm).sub (hm.mul_right n)).sub hQ
  · rcases Int.even_or_odd Q with hQ | hQ
    · exact ((Int.not_even_iff_odd.mpr hn) (h.mpr hQ).2).elim
    · exact ((hn.sub_even hm).sub_even (hm.mul_right n)).sub_odd hQ
  · rcases Int.even_or_odd Q with hQ | hQ
    · exact ((Int.not_even_iff_odd.mpr hm) (h.mpr hQ).1).elim
    · exact ((hn.sub_odd hm).sub_even (hn.mul_left m)).sub_odd hQ
  · rcases Int.even_or_odd Q with hQ | hQ
    · exact ((Int.not_even_iff_odd.mpr hm) (h.mpr hQ).1).elim
    · exact ((hn.sub_odd hm).sub_odd ((Int.odd_mul).mpr ⟨hm, hn⟩)).sub_odd hQ

/-- Translate [AFK25, Lemma 5.5, `lem:drafjfqp`] into the shift coordinates
`Ap = p - d(m,n)`: `m,n` are even exactly when `(f_j/f)Q(p)` is even. -/
private lemma associated_shift_even_iff {t : AdmissibleTuple} {A Lz : SL(2, ℤ)}
    (h : t.IsAssociatedStabilizerPair A Lz) (p : IntPhaseSpace) {m n : ℤ}
    (hq0 : Matrix.mulVec (A : Mat(2, ℤ)) p 0 =
      p 0 - (t.d : ℤ) * m)
    (hq1 : Matrix.mulVec (A : Mat(2, ℤ)) p 1 =
      p 1 - (t.d : ℤ) * n) :
    (Even m ∧ Even n) ↔
      Even ((t.towerConductorRatio : ℤ) * t.Q.eval (p 0) (p 1)) := by
  have hdZ : (t.d : ℤ) ≠ 0 := by have := t.three_lt_d; omega
  constructor
  · rintro ⟨hm, hn⟩
    apply even_iff_two_dvd.mpr
    apply (h.two_dvd_scaledForm_eval_iff p).mpr
    intro i
    fin_cases i
    · change (2 * (t.d : ℤ)) ∣
        Matrix.mulVec (A : Mat(2, ℤ)) p 0 - p 0
      obtain ⟨a, ha⟩ := hm.two_dvd
      refine ⟨-a, ?_⟩
      rw [hq0, ha]
      ring
    · change (2 * (t.d : ℤ)) ∣
        Matrix.mulVec (A : Mat(2, ℤ)) p 1 - p 1
      obtain ⟨b, hb⟩ := hn.two_dvd
      refine ⟨-b, ?_⟩
      rw [hq1, hb]
      ring
  · intro hQ
    have hall := (h.two_dvd_scaledForm_eval_iff p).mp hQ.two_dvd
    constructor <;> rw [even_iff_two_dvd]
    · have h0 := hall 0
      rw [hq0, show (2 : ℤ) * (t.d : ℤ) = (t.d : ℤ) * 2 by ring,
        show p 0 - (t.d : ℤ) * m - p 0 = (t.d : ℤ) * (-m) by ring] at h0
      have := (mul_dvd_mul_iff_left hdZ).mp h0
      simpa using this
    · have h1 := hall 1
      rw [hq1, show (2 : ℤ) * (t.d : ℤ) = (t.d : ℤ) * 2 by ring,
        show p 1 - (t.d : ℤ) * n - p 1 = (t.d : ℤ) * (-n) by ring] at h1
      have := (mul_dvd_mul_iff_left hdZ).mp h1
      simpa using this

/-! ### Inverse orientation

When the lower-left entry of `A` is negative, the total cocycle uses the positive word for `A⁻¹`.
The pairing and parity data below transport the positive-word calculation through inversion. -/

/-- Inverting a determinant-one matrix negates its self-pairing:
`⟨M⁻¹p,p⟩ = -⟨Mp,p⟩`. This is the pairing bridge used by the negative-orientation branch. -/
private lemma intSymplecticForm_mulVec_inv_self (M : SL(2, ℤ)) (p : IntPhaseSpace) :
    intSymplecticForm
        (Matrix.mulVec ((M⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) p) p =
      -intSymplecticForm
        (Matrix.mulVec (M : Mat(2, ℤ)) p) p := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  simp only [intSymplecticForm, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The parity characterization of [AFK25, Lemma 5.5, `lem:drafjfqp`] also holds for shift
coordinates defined by `A⁻¹p = p - d(m,n)`. Multiplication by the unimodular matrix `A` transports
simultaneous evenness between the `A⁻¹` and `A` shifts. -/
private lemma associated_inv_shift_even_iff {t : AdmissibleTuple} {A Lz : SL(2, ℤ)}
    (h : t.IsAssociatedStabilizerPair A Lz) (p : IntPhaseSpace) {m n : ℤ}
    (hq0 : Matrix.mulVec ((A⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) p 0 =
      p 0 - (t.d : ℤ) * m)
    (hq1 : Matrix.mulVec ((A⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) p 1 =
      p 1 - (t.d : ℤ) * n) :
    (Even m ∧ Even n) ↔
      Even ((t.towerConductorRatio : ℤ) * t.Q.eval (p 0) (p 1)) := by
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    have hdet' := A.2
    rw [Matrix.det_fin_two] at hdet'
    exact hdet'
  have hq0' := hq0
  have hq1' := hq1
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl] at hq0' hq1'
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hq0' hq1'
  let u := A 0 0 * m + A 0 1 * n
  let v := A 1 0 * m + A 1 1 * n
  have hA0 : Matrix.mulVec (A : Mat(2, ℤ)) p 0 =
      p 0 - (t.d : ℤ) * (-u) := by
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    dsimp only [u]
    linear_combination
      (-(A 0 0)) * hq0' - (A 0 1) * hq1' + (p 0) * hdet
  have hA1 : Matrix.mulVec (A : Mat(2, ℤ)) p 1 =
      p 1 - (t.d : ℤ) * (-v) := by
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    dsimp only [v]
    linear_combination
      (-(A 1 0)) * hq0' - (A 1 1) * hq1' + (p 1) * hdet
  have hsource := associated_shift_even_iff h p hA0 hA1
  constructor
  · rintro ⟨hm, hn⟩
    apply hsource.mp
    constructor
    · exact (hm.mul_left (A 0 0)).add (hn.mul_left (A 0 1)) |>.neg
    · exact (hm.mul_left (A 1 0)).add (hn.mul_left (A 1 1)) |>.neg
  · intro hQ
    obtain ⟨hu, hv⟩ := hsource.mpr hQ
    have hu' : Even u := by simpa using hu.neg
    have hv' : Even v := by simpa using hv.neg
    constructor
    · have heven : Even (A 1 1 * u - A 0 1 * v) :=
        (hu'.mul_left (A 1 1)).sub (hv'.mul_left (A 0 1))
      have hm : A 1 1 * u - A 0 1 * v = m := by
        dsimp only [u, v]
        linear_combination m * hdet
      rw [hm] at heven
      exact heven
    · have heven : Even (-A 1 0 * u + A 0 0 * v) :=
        (hu'.mul_left (-A 1 0)).add (hv'.mul_left (A 0 0))
      have hn : -A 1 0 * u + A 0 0 * v = n := by
        dsimp only [u, v]
        linear_combination n * hdet
      rw [hn] at heven
      exact heven

/-- An even integer `k` has `exp(πik) = 1`. This closes both parity reductions below. -/
private lemma exp_pi_mul_I_intCast_eq_one_of_even {k : ℤ} (hk : Even k) :
    Complex.exp (Real.pi * Complex.I * (k : ℂ)) = 1 := by
  obtain ⟨a, ha⟩ := hk
  rw [ha, show Real.pi * Complex.I * (((a + a : ℤ) : ℂ)) =
    (a : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring,
    Complex.exp_int_mul_two_pi_mul_I]

/-! ### Reciprocal candidate overlaps

The two private orientation branches share the reflected word formula but differ in how the total
cocycle selects that word. The public theorem joins them using the nonvanishing lower-left entry
of an associated stabilizer. -/

/-- Assemble the reciprocal identity when `A₁₀ > 0`, so the total cocycle is the word value at
`A` itself. This is the direct orientation of the proof of [AFK25, Theorem 5.8,
`thm:nupnumpeq1`]. -/
private lemma candidateNormGhostOverlap_mul_neg_of_lowerLeft_pos
    {t : AdmissibleTuple} {A Lz : SL(2, ℤ)}
    (h : t.IsAssociatedStabilizerPair A Lz) {p : IntPhaseSpace}
    (hp : intPhaseSpaceMod t.d p ≠ 0) (hpos : 0 < A 1 0) :
    t.candidateNormGhostOverlap A p * t.candidateNormGhostOverlap A (-p) = 1 := by
  have hd : 0 < t.d := Nat.zero_lt_of_lt t.three_lt_d
  have hτ : Irrational t.Q.rootPlus := t.form_admissible.rootPlus_irrational
  have hM := h.A_mem_gammaSubgroup (exists_intCast_mul_shiftRationalPoint t.d p)
  have hlat : SigmaSLatticeFree t.Q.rootPlus
      (fracSymplecticFormRat (shiftRationalPoint t.d p) t.Q.rootPlus) :=
    sigmaSLatticeFree_fracSymplecticFormRat hτ
      (not_isIntegralIndex_shiftRationalPoint t.d hd hp)
  obtain ⟨m, n, hq0, hq1, hcocycle⟩ :=
    sfModularCocycleReal_mul_neg_shift_eq_exp hd p hτ hM hpos
      h.fltDenominator_A_rootPlus_pos h.flt_A_rootPlus hlat
  have hphase := sfPhase_sq_eq_exp t A p
  have hpair := h.intSymplecticForm_A_mulVec_self p
  have hpar : Even (n - m - m * n -
      (t.towerConductorRatio : ℤ) * t.Q.eval (p 0) (p 1)) :=
    reflection_parity (associated_shift_even_iff h p hq0 hq1)
  have hexp :
      -Real.pi * Complex.I / 6 * ((rademacherInvariant A : ℚ) : ℂ) +
          ((-((t.conductorRatio : ℤ) * t.Q.eval (p 0) (p 1)) : ℤ) : ℂ) *
            (2 * Real.pi * Complex.I / (t.d : ℂ)) +
          Real.pi * Complex.I *
            ((((n - m - m * n : ℤ) : ℂ) -
                ((intSymplecticForm
                  (Matrix.mulVec (A : Mat(2, ℤ)) p) p : ℤ) : ℂ) /
                  ((t.d : ℂ) ^ 2)) +
              ((rademacherInvariant A : ℚ) : ℂ) / 6) =
        Real.pi * Complex.I *
          ((n - m - m * n -
            (t.towerConductorRatio : ℤ) * t.Q.eval (p 0) (p 1) : ℤ) : ℂ) := by
    rw [hpair]
    push_cast
    field_simp [show (t.d : ℂ) ≠ 0 by exact_mod_cast (NeZero.ne t.d)]
    ring
  rw [AdmissibleTuple.candidateNormGhostOverlap_eq_sfPhase_mul h p,
    AdmissibleTuple.candidateNormGhostOverlap_eq_sfPhase_mul h (-p),
    AdmissibleTuple.sfPhase_neg]
  have htotalp :
      sfModularCocycleRealTotal (shiftRationalPoint t.d p) A hM t.Q.rootPlus =
        sfModularCocycleReal (shiftRationalPoint t.d p) A hM hpos.le t.Q.rootPlus :=
    sfModularCocycleRealTotal_of_nonneg hM hpos.le _
  have htotalneg :
      sfModularCocycleRealTotal (shiftRationalPoint t.d (-p)) A
          (h.A_mem_gammaSubgroup (exists_intCast_mul_shiftRationalPoint t.d (-p))) t.Q.rootPlus =
        sfModularCocycleReal (-shiftRationalPoint t.d p) A
          (neg_mem_gammaSubgroup hM) hpos.le t.Q.rootPlus := by
    rw [sfModularCocycleRealTotal_of_nonneg
      (h.A_mem_gammaSubgroup (exists_intCast_mul_shiftRationalPoint t.d (-p))) hpos.le]
    simp only [shiftRationalPoint_neg]
  rw [htotalp, htotalneg]
  calc
    t.sfPhase A p *
          sfModularCocycleReal (shiftRationalPoint t.d p) A hM hpos.le t.Q.rootPlus *
        (t.sfPhase A p *
          sfModularCocycleReal (-shiftRationalPoint t.d p) A
            (neg_mem_gammaSubgroup hM) hpos.le t.Q.rootPlus) =
        t.sfPhase A p ^ 2 *
          (sfModularCocycleReal (shiftRationalPoint t.d p) A hM hpos.le t.Q.rootPlus *
            sfModularCocycleReal (-shiftRationalPoint t.d p) A
              (neg_mem_gammaSubgroup hM) hpos.le t.Q.rootPlus) := by ring
    _ = _ := by
      rw [hphase, hcocycle, ← Complex.exp_add, ← Complex.exp_add, hexp,
        exp_pi_mul_I_intCast_eq_one_of_even hpar]

/-- Assemble the reciprocal identity when `A₁₀ < 0`. The total cocycle is read through the
positive word for `A⁻¹`; `rademacherInvariant_inv`, `intSymplecticForm_mulVec_inv_self`, and
`associated_inv_shift_even_iff` convert its exponent back to the phase defined with `A`. -/
private lemma candidateNormGhostOverlap_mul_neg_of_lowerLeft_neg
    {t : AdmissibleTuple} {A Lz : SL(2, ℤ)}
    (h : t.IsAssociatedStabilizerPair A Lz) {p : IntPhaseSpace}
    (hp : intPhaseSpaceMod t.d p ≠ 0) (hneg : A 1 0 < 0) :
    t.candidateNormGhostOverlap A p * t.candidateNormGhostOverlap A (-p) = 1 := by
  have hd : 0 < t.d := Nat.zero_lt_of_lt t.three_lt_d
  have hτ : Irrational t.Q.rootPlus := t.form_admissible.rootPlus_irrational
  have hM := h.A_mem_gammaSubgroup (exists_intCast_mul_shiftRationalPoint t.d p)
  have hMinv := inv_mem_gammaSubgroup hM
  have hposInv : 0 < (A⁻¹ : SL(2, ℤ)) 1 0 := by rw [SL2Z.lowerLeft_inv]; omega
  have hfixInv :
      flt ((A⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) t.Q.rootPlus =
        t.Q.rootPlus :=
    flt_inv_of_flt_eq_self h.fltDenominator_A_rootPlus_pos.ne'
      h.flt_A_rootPlus
  have hlat : SigmaSLatticeFree t.Q.rootPlus
      (fracSymplecticFormRat (shiftRationalPoint t.d p) t.Q.rootPlus) :=
    sigmaSLatticeFree_fracSymplecticFormRat hτ
      (not_isIntegralIndex_shiftRationalPoint t.d hd hp)
  obtain ⟨m, n, hq0, hq1, hcocycle⟩ :=
    sfModularCocycleReal_mul_neg_shift_eq_exp hd p hτ hMinv hposInv
      h.fltDenominator_A_inv_rootPlus_pos hfixInv hlat
  have hphase := sfPhase_sq_eq_exp t A p
  have hpairA := h.intSymplecticForm_A_mulVec_self p
  have hpairInv := intSymplecticForm_mulVec_inv_self A p
  have hpar : Even (n - m - m * n -
      (t.towerConductorRatio : ℤ) * t.Q.eval (p 0) (p 1)) :=
    reflection_parity (associated_inv_shift_even_iff h p hq0 hq1)
  have htwice : Even
      (2 * ((t.towerConductorRatio : ℤ) * t.Q.eval (p 0) (p 1))) :=
    ⟨(t.towerConductorRatio : ℤ) * t.Q.eval (p 0) (p 1), by ring⟩
  have hparPlus : Even (n - m - m * n +
      (t.towerConductorRatio : ℤ) * t.Q.eval (p 0) (p 1)) := by
    have heq :
        (n - m - m * n -
            (t.towerConductorRatio : ℤ) * t.Q.eval (p 0) (p 1)) +
          2 * ((t.towerConductorRatio : ℤ) * t.Q.eval (p 0) (p 1)) =
        n - m - m * n +
          (t.towerConductorRatio : ℤ) * t.Q.eval (p 0) (p 1) := by ring
    rw [← heq]
    exact hpar.add htwice
  have hexp :
      -Real.pi * Complex.I / 6 * ((rademacherInvariant A : ℚ) : ℂ) +
          ((-((t.conductorRatio : ℤ) * t.Q.eval (p 0) (p 1)) : ℤ) : ℂ) *
            (2 * Real.pi * Complex.I / (t.d : ℂ)) +
          -(Real.pi * Complex.I *
            ((((n - m - m * n : ℤ) : ℂ) -
                ((intSymplecticForm
                  (Matrix.mulVec
                    ((A⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) p) p : ℤ) : ℂ) /
                  ((t.d : ℂ) ^ 2)) +
              ((rademacherInvariant A⁻¹ : ℚ) : ℂ) / 6)) =
        Real.pi * Complex.I *
          ((-(n - m - m * n +
            (t.towerConductorRatio : ℤ) * t.Q.eval (p 0) (p 1)) : ℤ) : ℂ) := by
    rw [hpairInv, hpairA, rademacherInvariant_inv]
    push_cast
    field_simp [show (t.d : ℂ) ≠ 0 by exact_mod_cast (NeZero.ne t.d)]
    ring
  have htotalp :
      sfModularCocycleRealTotal (shiftRationalPoint t.d p) A hM t.Q.rootPlus =
        (sfModularCocycleReal (shiftRationalPoint t.d p) A⁻¹ hMinv hposInv.le
          t.Q.rootPlus)⁻¹ := by
    calc
      _ = (sfModularCocycleRealTotal (shiftRationalPoint t.d p) A⁻¹ hMinv
          t.Q.rootPlus)⁻¹ := by
        rw [sfModularCocycleRealTotal_inv_of_lowerLeft_ne_zero hM
          h.lowerLeft_A_ne_zero h.fltDenominator_A_rootPlus_pos.ne'
          h.flt_A_rootPlus]
        simp only [inv_inv]
      _ = _ := by
        rw [sfModularCocycleRealTotal_of_nonneg hMinv hposInv.le]
  have hMneg := h.A_mem_gammaSubgroup
    (exists_intCast_mul_shiftRationalPoint t.d (-p))
  have htotalneg :
      sfModularCocycleRealTotal (shiftRationalPoint t.d (-p)) A hMneg t.Q.rootPlus =
        (sfModularCocycleReal (-shiftRationalPoint t.d p) A⁻¹
          (neg_mem_gammaSubgroup hMinv) hposInv.le t.Q.rootPlus)⁻¹ := by
    calc
      _ = (sfModularCocycleRealTotal (shiftRationalPoint t.d (-p)) A⁻¹
          (inv_mem_gammaSubgroup hMneg) t.Q.rootPlus)⁻¹ := by
        rw [sfModularCocycleRealTotal_inv_of_lowerLeft_ne_zero hMneg
          h.lowerLeft_A_ne_zero h.fltDenominator_A_rootPlus_pos.ne'
          h.flt_A_rootPlus]
        simp only [inv_inv]
      _ = _ := by
        rw [sfModularCocycleRealTotal_of_nonneg
          (inv_mem_gammaSubgroup hMneg) hposInv.le]
        simp only [shiftRationalPoint_neg]
  rw [AdmissibleTuple.candidateNormGhostOverlap_eq_sfPhase_mul h p,
    AdmissibleTuple.candidateNormGhostOverlap_eq_sfPhase_mul h (-p),
    AdmissibleTuple.sfPhase_neg, htotalp, htotalneg]
  calc
    t.sfPhase A p *
          (sfModularCocycleReal (shiftRationalPoint t.d p) A⁻¹ hMinv hposInv.le
            t.Q.rootPlus)⁻¹ *
        (t.sfPhase A p *
          (sfModularCocycleReal (-shiftRationalPoint t.d p) A⁻¹
            (neg_mem_gammaSubgroup hMinv) hposInv.le t.Q.rootPlus)⁻¹) =
        t.sfPhase A p ^ 2 *
          (sfModularCocycleReal (shiftRationalPoint t.d p) A⁻¹ hMinv hposInv.le
              t.Q.rootPlus *
            sfModularCocycleReal (-shiftRationalPoint t.d p) A⁻¹
              (neg_mem_gammaSubgroup hMinv) hposInv.le t.Q.rootPlus)⁻¹ := by
      rw [mul_inv_rev]
      ring
    _ = _ := by
      rw [hphase, hcocycle, ← Complex.exp_neg, ← Complex.exp_add, ← Complex.exp_add,
        hexp, exp_pi_mul_I_intCast_eq_one_of_even hparPlus.neg]

/-- **The reciprocal identity for candidate normalized ghost overlaps:**
`ν̃_t(p)ν̃_t(-p)=1` whenever `p ≢ 0 (mod d)`.

This is the reciprocal clause of [AFK25, Theorem 5.8, `thm:nupnumpeq1`]. The nonzero residue
hypothesis supplies the lattice-free condition in the source proof. The formal proof splits on the
orientation of `A₁₀`, since `sfModularCocycleRealTotal` evaluates the Hirzebruch--Jung word at `A`
or `A⁻¹` accordingly; `lowerLeft_A_ne_zero` rules out the remaining case. -/
@[source "AFK25, Theorem 5.8, p. 80, thm:nupnumpeq1 (reciprocal)"]
theorem AdmissibleTuple.IsAssociatedStabilizerPair.candidateNormGhostOverlap_reciprocal
    {t : AdmissibleTuple} {A Lz : SL(2, ℤ)}
    (h : t.IsAssociatedStabilizerPair A Lz) (p : IntPhaseSpace)
    (hp : intPhaseSpaceMod t.d p ≠ 0) :
    t.candidateNormGhostOverlap A p * t.candidateNormGhostOverlap A (-p) = 1 := by
  rcases lt_or_gt_of_ne h.lowerLeft_A_ne_zero with hneg | hpos
  · exact candidateNormGhostOverlap_mul_neg_of_lowerLeft_neg h hp hneg
  · exact candidateNormGhostOverlap_mul_neg_of_lowerLeft_pos h hp hpos


end SIC

end
