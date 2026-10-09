/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Quadratic.OrderUnits

/-!
# Congruences of unit powers modulo an integer

The exponents with `v^k ≡ ±1 (mod d)`.

Let `v` be a norm-one unit of the order `ℤ[ρ]` of a monic form of positive discriminant with
real value `ι(v) > 1`, and let `z = v^n` satisfy the identity

`z^{2m+1} - 1 = d z^m (z - 1)`

of [AFK25, Lemma 4.23, `lem:dimgridtechres`, equation (4.90), `eq:epowerminusone`], which the
tower unit `ε^j` and the dimension `d = d_{j,m}` satisfy. This file determines the exponents `k`
with `v^k ≡ 1 (mod d)`: they are exactly the multiples of `N = (2m+1)n`, and no power satisfies
`v^k ≡ -1 (mod d)`. This is the multiplicative-order computation in the proof of
[AFK25, Theorem 4.50, `tm:symgp`], from `A_t ≡ I (mod d)` through the bound
[AFK25, equation (4.203), `eq:Nzprimebound`] to the exclusion of `-I`, stated in the order rather
than for the canonical matrices.

## Mathematical argument

The exponents `k` with `d ∣ v^k - 1` form a subgroup of `ℤ` containing `N`, because
`v^{2m+1 · n} - 1 = z^{2m+1} - 1` is a multiple of `d` by the identity. Conversely, if
`d ∣ v^k - 1` with `0 < k` and `2k ≤ N`, take norms: `Nm(v^k - 1) = 2 - Tr(v^k)` is a nonzero
integer divisible by `d²`. Writing `a = ι(z) = ι(v)^n` and `b = ι(v)^k`, so that `1 < b` and
`b² ≤ a^{2m+1}`, the identity gives `d = (a^{2m+1} - 1)/(a^m (a - 1))`, and an elementary
estimate shows `|2 - b - b⁻¹| < d²`, a contradiction. The source writes this estimate through
`sinh` and `tanh`; here it is the polynomial inequality `(b+1)²/b < d²`, proved by comparing with
`c = √(a^{2m+1}) > a`. Hence the subgroup is `Nℤ`: a positive exponent below `N` in it would
have either itself or its complement to `N` at most `N/2`.

If `d ∣ v^s + 1` then `d ∣ v^{2s} - 1`, so `N ∣ 2s`; `N ∣ s` is impossible because `d > 2`
cannot divide both `v^s - 1` and `v^s + 1`; so `N` is even, `s ≡ N/2 (mod N)`, and
`d ∣ v^{N/2} + 1`. The same estimate applied to `Nm(v^{N/2} + 1) = 2 + Tr(v^{N/2}) > 0`
gives the contradiction.
-/

noncomputable section

namespace SIC

/-! ### The exponent subgroup

For a unit `u` of a commutative ring and a ring element `r`, the exponents `k` with
`r ∣ u^k - 1` form a subgroup of `ℤ`, since
`u^a - 1 = u^b (u^{a-b} - 1) + (u^b - 1)`. -/

section ExponentSubgroup

variable {R : Type*} [CommRing R] (r : R) (u : Rˣ)

/-- `r ∣ u^a - 1` and `r ∣ u^b - 1` give `r ∣ u^{a-b} - 1`. -/
lemma dvd_zpow_sub_sub_one {a b : ℤ} (hA : r ∣ ((u ^ a : Rˣ) : R) - 1)
    (hB : r ∣ ((u ^ b : Rˣ) : R) - 1) : r ∣ ((u ^ (a - b) : Rˣ) : R) - 1 := by
  have h : ((u ^ a : Rˣ) : R) - 1 - (((u ^ b : Rˣ) : R) - 1) =
      (u ^ b : Rˣ) * (((u ^ (a - b) : Rˣ) : R) - 1) := by
    rw [mul_sub, mul_one, ← Units.val_mul, ← zpow_add, add_sub_cancel]
    ring
  have hsub := dvd_sub hA hB
  rw [h] at hsub
  exact Units.dvd_mul_left.mp hsub

/-- `r ∣ u^a + 1` and `r ∣ u^b - 1` give `r ∣ u^{a-b} + 1`. -/
lemma dvd_zpow_sub_add_one {a b : ℤ} (hA : r ∣ ((u ^ a : Rˣ) : R) + 1)
    (hB : r ∣ ((u ^ b : Rˣ) : R) - 1) : r ∣ ((u ^ (a - b) : Rˣ) : R) + 1 := by
  have h : ((u ^ a : Rˣ) : R) + 1 + (((u ^ b : Rˣ) : R) - 1) =
      (u ^ b : Rˣ) * (((u ^ (a - b) : Rˣ) : R) + 1) := by
    rw [mul_add, mul_one, ← Units.val_mul, ← zpow_add, add_sub_cancel]
    ring
  have hadd := dvd_add hA hB
  rw [h] at hadd
  exact Units.dvd_mul_left.mp hadd

/-- `r ∣ u^k - 1` gives `r ∣ u^{-k} - 1`. -/
lemma dvd_zpow_neg_sub_one {k : ℤ} (h : r ∣ ((u ^ k : Rˣ) : R) - 1) :
    r ∣ ((u ^ (-k) : Rˣ) : R) - 1 := by
  simpa using dvd_zpow_sub_sub_one r u (a := 0) (b := k) (by simp) h

/-- The exponents `k` with `u^k ≡ 1 (mod r)`, as a subgroup of `ℤ`. -/
def congruenceExponents : AddSubgroup ℤ where
  carrier := {k | r ∣ ((u ^ k : Rˣ) : R) - 1}
  zero_mem' := by simp
  neg_mem' h := dvd_zpow_neg_sub_one r u h
  add_mem' {a b} ha hb := by
    have := dvd_zpow_sub_sub_one r u ha (dvd_zpow_neg_sub_one r u hb)
    simpa [sub_neg_eq_add] using this

/-- Membership in `congruenceExponents`. -/
lemma mem_congruenceExponents {k : ℤ} :
    k ∈ congruenceExponents r u ↔ r ∣ ((u ^ k : Rˣ) : R) - 1 := Iff.rfl

/-- `r ∣ u^N - 1` gives `r ∣ u^{Nl} - 1` for every integer `l`. -/
lemma dvd_zpow_mul_sub_one {N : ℤ} (hN : r ∣ ((u ^ N : Rˣ) : R) - 1) (l : ℤ) :
    r ∣ ((u ^ (N * l) : Rˣ) : R) - 1 := by
  have := (congruenceExponents r u).zsmul_mem ((mem_congruenceExponents r u).2 hN) l
  rw [mem_congruenceExponents, smul_eq_mul, mul_comm] at this
  exact this

end ExponentSubgroup

/-! ### Norms of `w ± 1` and divisibility

In a quadratic algebra `Nm(w ± 1) = Nm(w) ± Tr(w) + 1`, and an element divisible by an integer
`n` has norm divisible by `n²`; an element whose norm is a nonzero integer of absolute value
below `n²` is therefore not divisible by `n`. -/

section Norms

variable {R : Type*} [CommRing R] {a b : R}

/-- `Nm(w - 1) = Nm(w) - Tr(w) + 1`. -/
lemma QuadraticAlgebra.norm_sub_one (w : QuadraticAlgebra R a b) :
    (w - 1).norm = w.norm - QuadraticAlgebra.trace w + 1 := by
  simp only [QuadraticAlgebra.norm_def, QuadraticAlgebra.trace_def, QuadraticAlgebra.re_sub,
    QuadraticAlgebra.im_sub, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  ring

/-- `Nm(w + 1) = Nm(w) + Tr(w) + 1`. -/
lemma QuadraticAlgebra.norm_add_one (w : QuadraticAlgebra R a b) :
    (w + 1).norm = w.norm + QuadraticAlgebra.trace w + 1 := by
  simp only [QuadraticAlgebra.norm_def, QuadraticAlgebra.trace_def, QuadraticAlgebra.re_add,
    QuadraticAlgebra.im_add, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  ring

/-- Divisibility by an integer `n` forces divisibility of the norm by `n²`. -/
lemma QuadraticAlgebra.sq_dvd_norm_of_intCast_dvd {a b : ℤ} (n : ℤ) {w : QuadraticAlgebra ℤ a b}
    (h : (n : QuadraticAlgebra ℤ a b) ∣ w) : n ^ 2 ∣ w.norm := by
  obtain ⟨y, rfl⟩ := h
  rw [map_mul, QuadraticAlgebra.norm_intCast]
  exact dvd_mul_right _ _

/-- An element with nonzero norm of absolute value below `n²` is not divisible by `n`. -/
lemma QuadraticAlgebra.not_intCast_dvd_of_abs_norm_lt {a b : ℤ} {n : ℤ} {w : QuadraticAlgebra ℤ a b}
    (hne : w.norm ≠ 0) (hlt : |w.norm| < n ^ 2) : ¬ (n : QuadraticAlgebra ℤ a b) ∣ w := by
  intro h
  exact hne (Int.eq_zero_of_abs_lt_dvd (QuadraticAlgebra.sq_dvd_norm_of_intCast_dvd n h) hlt)

end Norms

/-! ### The norm bound

The real inequality behind [AFK25, equation (4.203), `eq:Nzprimebound`]: with
`d = (a^{2m+1} - 1)/(a^m (a - 1))` and `1 ≤ b ≤ √(a^{2m+1})`, one has `(b + 1)²/b < d²`, and
hence both `|2 - (b + b⁻¹)| < d²` and `2 + (b + b⁻¹) < d²`. -/

/-- The core bound `(b + 1)²/b < d²` for `1 ≤ b`, `b² ≤ a^{2m+1}`, `1 < a`, `1 ≤ m` and
`d · a^m (a - 1) = a^{2m+1} - 1`. -/
theorem sq_div_lt_sq (a b d : ℝ) (m : ℕ) (ha : 1 < a) (hm : 1 ≤ m) (hb : 1 ≤ b)
    (hb2 : b ^ 2 ≤ a ^ (2 * m + 1)) (hd : d * (a ^ m * (a - 1)) = a ^ (2 * m + 1) - 1) :
    (b + 1) ^ 2 / b < d ^ 2 := by
  let c := Real.sqrt (a ^ (2 * m + 1))
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hpow0 : 0 ≤ a ^ (2 * m + 1) := (pow_pos ha0 _).le
  have hc_sq : c ^ 2 = a ^ (2 * m + 1) := by
    exact Real.sq_sqrt hpow0
  have hbc : b ≤ c := by
    exact (Real.le_sqrt (by linarith) hpow0).2 hb2
  have hexp : 2 < 2 * m + 1 := by omega
  have ha_sq_lt : a ^ 2 < a ^ (2 * m + 1) := pow_lt_pow_right₀ ha hexp
  have hac : a < c := by
    exact (Real.lt_sqrt ha0.le).2 ha_sq_lt
  have hc0 : 0 < c := lt_trans ha0 hac
  have hc1 : 1 ≤ c := by linarith
  have hbc_prod : 1 ≤ b * c := one_le_mul_of_one_le_of_one_le hb hc1
  have hmono : (b + 1) ^ 2 / b ≤ (c + 1) ^ 2 / c := by
    apply (div_le_div_iff₀ hb0 hc0).2
    have hnonneg : 0 ≤ (c - b) * (b * c - 1) :=
      mul_nonneg (sub_nonneg.mpr hbc) (sub_nonneg.mpr hbc_prod)
    nlinarith
  have hfactor : 0 < (c - a) * (a * c - 1) := by
    apply mul_pos
    · linarith
    · nlinarith
  have hkey : c * (a - 1) ^ 2 < a * (c - 1) ^ 2 := by
    nlinarith
  have hpower : a * (a ^ m * (a - 1)) ^ 2 = c ^ 2 * (a - 1) ^ 2 := by
    rw [hc_sq]
    ring_nf
  have hq : (a ^ m * (a - 1)) ^ 2 < c * (c - 1) ^ 2 := by
    apply (mul_lt_mul_iff_of_pos_left ha0).mp
    rw [hpower]
    have hscaled := mul_lt_mul_of_pos_left hkey hc0
    nlinarith
  have hq0 : 0 < (a ^ m * (a - 1)) ^ 2 := by positivity
  have hsum0 : 0 < (c + 1) ^ 2 := by positivity
  have hmult := mul_lt_mul_of_pos_right hq hsum0
  have hd_sq : d ^ 2 * (a ^ m * (a - 1)) ^ 2 = (c ^ 2 - 1) ^ 2 := by
    have hsquared := congrArg (fun x : ℝ => x ^ 2) hd
    rw [← hc_sq] at hsquared
    nlinarith
  have hmult' :
      (a ^ m * (a - 1)) ^ 2 * (c + 1) ^ 2 <
        (a ^ m * (a - 1)) ^ 2 * (c * d ^ 2) := by
    calc
      (a ^ m * (a - 1)) ^ 2 * (c + 1) ^ 2 <
          (c * (c - 1) ^ 2) * (c + 1) ^ 2 := hmult
      _ = c * (c ^ 2 - 1) ^ 2 := by ring
      _ = (a ^ m * (a - 1)) ^ 2 * (c * d ^ 2) := by rw [← hd_sq]; ring
  have hend_num : (c + 1) ^ 2 < c * d ^ 2 :=
    (mul_lt_mul_iff_of_pos_left hq0).mp hmult'
  have hend : (c + 1) ^ 2 / c < d ^ 2 := by
    exact (div_lt_iff₀ hc0).2 (by simpa [mul_comm] using hend_num)
  exact lt_of_le_of_lt hmono hend

/-- `2 + (b + b⁻¹) < d²` under the hypotheses of `sq_div_lt_sq`. -/
theorem two_add_lt_sq (a b d : ℝ) (m : ℕ) (ha : 1 < a) (hm : 1 ≤ m) (hb : 1 ≤ b)
    (hb2 : b ^ 2 ≤ a ^ (2 * m + 1)) (hd : d * (a ^ m * (a - 1)) = a ^ (2 * m + 1) - 1) :
    2 + (b + b⁻¹) < d ^ 2 := by
  have hb0 : b ≠ 0 := by linarith
  rw [show 2 + (b + b⁻¹) = (b + 1) ^ 2 / b by field_simp; ring]
  exact sq_div_lt_sq a b d m ha hm hb hb2 hd

/-- `|2 - (b + b⁻¹)| < d²` under the hypotheses of `sq_div_lt_sq`. -/
theorem abs_two_sub_lt_sq (a b d : ℝ) (m : ℕ) (ha : 1 < a) (hm : 1 ≤ m) (hb : 1 ≤ b)
    (hb2 : b ^ 2 ≤ a ^ (2 * m + 1)) (hd : d * (a ^ m * (a - 1)) = a ^ (2 * m + 1) - 1) :
    |2 - (b + b⁻¹)| < d ^ 2 := by
  rw [abs_sub_lt_iff]
  have hmain := two_add_lt_sq a b d m ha hm hb hb2 hd
  have hb0 : 0 < b := by linarith
  have hinv0 : 0 < b⁻¹ := inv_pos.mpr hb0
  constructor <;> nlinarith

namespace BinaryQF

/-! ### Powers of a unit below the level

Throughout, `v` is a norm-one unit with `ι(v) > 1`, `z = v^n`, and `z^{2m+1} - 1 = d z^m (z-1)`.
The bound excludes `d ∣ v^k ∓ 1` whenever `2k ≤ N = n(2m+1)` (and `k ≠ 0` for the minus sign). -/

section Level

variable {Q : BinaryQF} (ha : Q.a = 1) (hdisc : 0 < Q.disc) {v : Q.monicNormOneUnits}
  {n m d : ℕ}


/-- The real form of the identity: `d · a^m (a - 1) = a^{2m+1} - 1` with `a = ι(v)^n`. -/
private lemma real_identity
    (hident : (((v : Q.MonicOrderˣ) : Q.MonicOrder) ^ n) ^ (2 * m + 1) - 1 =
      (d : Q.MonicOrder) * ((((v : Q.MonicOrderˣ) : Q.MonicOrder) ^ n) ^ m *
        (((v : Q.MonicOrderˣ) : Q.MonicOrder) ^ n - 1))) :
    (d : ℝ) * (((monicNormOneUnitReal ha hdisc v : ℝ) ^ n) ^ m *
        ((monicNormOneUnitReal ha hdisc v : ℝ) ^ n - 1)) =
      ((monicNormOneUnitReal ha hdisc v : ℝ) ^ n) ^ (2 * m + 1) - 1 := by
  have h := congrArg (monicOrderReal ha hdisc.le) hident
  simp only [map_sub, map_one, map_mul, map_pow, map_natCast] at h
  rw [coe_monicNormOneUnitReal]
  exact h.symm

/-- The trace of `v^k` is `b + b⁻¹` with `b = ι(v)^k`. -/
private lemma trace_pow_real (k : ℕ) :
    ((QuadraticAlgebra.trace (((v : Q.MonicOrderˣ) : Q.MonicOrder) ^ k) : ℤ) : ℝ) =
      (monicNormOneUnitReal ha hdisc v : ℝ) ^ k +
        ((monicNormOneUnitReal ha hdisc v : ℝ) ^ k)⁻¹ := by
  have h := monicNormOneUnitReal_add_inv ha hdisc (v ^ k)
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, map_pow, Units.val_pow_eq_pow_val,
    coe_monicNormOneUnitReal] at h
  exact h.symm

/-- The hypotheses of the norm bound at the exponent `k`: `1 ≤ b` and `b² ≤ a^{2m+1}`. -/
private lemma bound_hypotheses (hv : 1 < (monicNormOneUnitReal ha hdisc v : ℝ)) {k : ℕ}
    (hk : 2 * k ≤ n * (2 * m + 1)) :
    1 ≤ (monicNormOneUnitReal ha hdisc v : ℝ) ^ k ∧
      ((monicNormOneUnitReal ha hdisc v : ℝ) ^ k) ^ 2 ≤
        ((monicNormOneUnitReal ha hdisc v : ℝ) ^ n) ^ (2 * m + 1) := by
  refine ⟨one_le_pow₀ hv.le, ?_⟩
  rw [← pow_mul, ← pow_mul, mul_comm k 2]
  exact pow_le_pow_right₀ hv.le hk

/-- **No power below half the level is `1` modulo `d`.** -/
theorem not_dvd_pow_sub_one_of_two_mul_le
    (hv : 1 < (monicNormOneUnitReal ha hdisc v : ℝ)) (hn : 0 < n) (hm : 0 < m)
    (hident : (((v : Q.MonicOrderˣ) : Q.MonicOrder) ^ n) ^ (2 * m + 1) - 1 =
      (d : Q.MonicOrder) * ((((v : Q.MonicOrderˣ) : Q.MonicOrder) ^ n) ^ m *
        (((v : Q.MonicOrderˣ) : Q.MonicOrder) ^ n - 1)))
    {k : ℕ} (hk : 0 < k) (hkN : 2 * k ≤ n * (2 * m + 1)) :
    ¬ (d : Q.MonicOrder) ∣ ((v : Q.MonicOrderˣ) : Q.MonicOrder) ^ k - 1 := by
  obtain ⟨hb, hb2⟩ := bound_hypotheses ha hdisc hv hkN
  have hnormv : (((v : Q.MonicOrderˣ) : Q.MonicOrder) ^ k).norm = 1 := by
    rw [map_pow, (Q.mem_monicNormOneUnits_iff v).mp v.property, one_pow]
  have hnorm : ((((v : Q.MonicOrderˣ) : Q.MonicOrder) ^ k - 1).norm : ℝ) =
      2 - ((monicNormOneUnitReal ha hdisc v : ℝ) ^ k +
        ((monicNormOneUnitReal ha hdisc v : ℝ) ^ k)⁻¹) := by
    rw [QuadraticAlgebra.norm_sub_one, hnormv]
    push_cast
    rw [trace_pow_real ha hdisc]
    ring
  apply QuadraticAlgebra.not_intCast_dvd_of_abs_norm_lt
  · intro h0
    have h0' : ((((v : Q.MonicOrderˣ) : Q.MonicOrder) ^ k - 1).norm : ℝ) = 0 := by
      exact_mod_cast h0
    rw [hnorm] at h0'
    have hone : 1 < (monicNormOneUnitReal ha hdisc v : ℝ) ^ k := one_lt_pow₀ hv hk.ne'
    have hpos : 0 < (monicNormOneUnitReal ha hdisc v : ℝ) ^ k := by linarith
    field_simp at h0'
    nlinarith
  · have hlt := abs_two_sub_lt_sq _ _ _ m (one_lt_pow₀ hv hn.ne') hm hb hb2
      (real_identity ha hdisc hident)
    have := hnorm ▸ hlt
    exact_mod_cast this

/-- **No power up to half the level is `-1` modulo `d`.** -/
theorem not_dvd_pow_add_one_of_two_mul_le
    (hv : 1 < (monicNormOneUnitReal ha hdisc v : ℝ)) (hn : 0 < n) (hm : 0 < m)
    (hident : (((v : Q.MonicOrderˣ) : Q.MonicOrder) ^ n) ^ (2 * m + 1) - 1 =
      (d : Q.MonicOrder) * ((((v : Q.MonicOrderˣ) : Q.MonicOrder) ^ n) ^ m *
        (((v : Q.MonicOrderˣ) : Q.MonicOrder) ^ n - 1)))
    {k : ℕ} (hkN : 2 * k ≤ n * (2 * m + 1)) :
    ¬ (d : Q.MonicOrder) ∣ ((v : Q.MonicOrderˣ) : Q.MonicOrder) ^ k + 1 := by
  obtain ⟨hb, hb2⟩ := bound_hypotheses ha hdisc hv hkN
  have hnormv : (((v : Q.MonicOrderˣ) : Q.MonicOrder) ^ k).norm = 1 := by
    rw [map_pow, (Q.mem_monicNormOneUnits_iff v).mp v.property, one_pow]
  have hnorm : ((((v : Q.MonicOrderˣ) : Q.MonicOrder) ^ k + 1).norm : ℝ) =
      2 + ((monicNormOneUnitReal ha hdisc v : ℝ) ^ k +
        ((monicNormOneUnitReal ha hdisc v : ℝ) ^ k)⁻¹) := by
    rw [QuadraticAlgebra.norm_add_one, hnormv]
    push_cast
    rw [trace_pow_real ha hdisc]
    ring
  apply QuadraticAlgebra.not_intCast_dvd_of_abs_norm_lt
  · intro h0
    have h0' : ((((v : Q.MonicOrderˣ) : Q.MonicOrder) ^ k + 1).norm : ℝ) = 0 := by
      exact_mod_cast h0
    rw [hnorm] at h0'
    have hpos : 0 < (monicNormOneUnitReal ha hdisc v : ℝ) ^ k := by linarith
    have := inv_pos.mpr hpos
    linarith
  · have hlt := two_add_lt_sq _ _ _ m (one_lt_pow₀ hv hn.ne') hm hb hb2
      (real_identity ha hdisc hident)
    rw [← hnorm] at hlt
    have habs : |((((v : Q.MonicOrderˣ) : Q.MonicOrder) ^ k + 1).norm : ℝ)| =
        ((((v : Q.MonicOrderˣ) : Q.MonicOrder) ^ k + 1).norm : ℝ) := by
      rw [abs_of_pos]
      rw [hnorm]
      have hpos : 0 < (monicNormOneUnitReal ha hdisc v : ℝ) ^ k := by linarith
      have := inv_pos.mpr hpos
      linarith
    rw [← habs] at hlt
    exact_mod_cast hlt

/-! ### The exponents congruent to one

With the level `N = n(2m+1)`, the exponent subgroup of `v` modulo `d` is exactly `Nℤ`, and no
power of `v` is `-1` modulo `d`. -/

/-- The integer-exponent form of `not_dvd_pow_sub_one_of_two_mul_le`. -/
private lemma not_dvd_zpow_sub_one_of_pos_of_le
    (hv : 1 < (monicNormOneUnitReal ha hdisc v : ℝ)) (hn : 0 < n) (hm : 0 < m)
    (hident : (((v : Q.MonicOrderˣ) : Q.MonicOrder) ^ n) ^ (2 * m + 1) - 1 =
      (d : Q.MonicOrder) * ((((v : Q.MonicOrderˣ) : Q.MonicOrder) ^ n) ^ m *
        (((v : Q.MonicOrderˣ) : Q.MonicOrder) ^ n - 1)))
    {r : ℤ} (hr : 0 < r)
    (hrN : 2 * r ≤ ((n * (2 * m + 1) : ℕ) : ℤ)) :
    ¬ (d : Q.MonicOrder) ∣ (((v : Q.MonicOrderˣ) ^ r : Q.MonicOrderˣ) : Q.MonicOrder) - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, r = k := ⟨r.toNat, (Int.toNat_of_nonneg hr.le).symm⟩
  rw [zpow_natCast, Units.val_pow_eq_pow_val]
  exact not_dvd_pow_sub_one_of_two_mul_le ha hdisc hv hn hm hident (by exact_mod_cast hr)
    (by exact_mod_cast hrN)

/-- **The level is `1` modulo `d`:** `d ∣ v^N - 1`, from the identity. -/
lemma dvd_zpow_level_sub_one
    (hident : (((v : Q.MonicOrderˣ) : Q.MonicOrder) ^ n) ^ (2 * m + 1) - 1 =
      (d : Q.MonicOrder) * ((((v : Q.MonicOrderˣ) : Q.MonicOrder) ^ n) ^ m *
        (((v : Q.MonicOrderˣ) : Q.MonicOrder) ^ n - 1))) :
    (d : Q.MonicOrder) ∣
      (((v : Q.MonicOrderˣ) ^ ((n * (2 * m + 1) : ℕ) : ℤ) : Q.MonicOrderˣ) : Q.MonicOrder) - 1 := by
  rw [zpow_natCast, Units.val_pow_eq_pow_val, pow_mul, hident]
  exact dvd_mul_right _ _

/-- **The exponents `k` with `v^k ≡ 1 (mod d)` are the multiples of the level `N = n(2m+1)`.**
This is the computation of the multiplicative order `q = (2m+1)n` in the proof of
[AFK25, Theorem 4.50, `tm:symgp`]. -/
theorem dvd_zpow_sub_one_iff
    (hv : 1 < (monicNormOneUnitReal ha hdisc v : ℝ)) (hn : 0 < n) (hm : 0 < m)
    (hident : (((v : Q.MonicOrderˣ) : Q.MonicOrder) ^ n) ^ (2 * m + 1) - 1 =
      (d : Q.MonicOrder) * ((((v : Q.MonicOrderˣ) : Q.MonicOrder) ^ n) ^ m *
        (((v : Q.MonicOrderˣ) : Q.MonicOrder) ^ n - 1))) (k : ℤ) :
    (d : Q.MonicOrder) ∣ (((v : Q.MonicOrderˣ) ^ k : Q.MonicOrderˣ) : Q.MonicOrder) - 1 ↔
      ((n * (2 * m + 1) : ℕ) : ℤ) ∣ k := by
  set N : ℤ := ((n * (2 * m + 1) : ℕ) : ℤ) with hN
  have hNpos : 0 < N := by
    rw [hN]; positivity
  have hlevel := dvd_zpow_level_sub_one hident
  constructor
  · intro hk
    -- Reduce `k` modulo `N` and show the remainder vanishes.
    have hr : (d : Q.MonicOrder) ∣
        (((v : Q.MonicOrderˣ) ^ (k % N) : Q.MonicOrderˣ) : Q.MonicOrder) - 1 := by
      have hmul := dvd_zpow_mul_sub_one _ _ hlevel (k / N)
      have := dvd_zpow_sub_sub_one _ _ hk hmul
      rwa [← Int.emod_def] at this
    by_contra hndvd
    have hr0 : k % N ≠ 0 := fun h => hndvd (Int.dvd_of_emod_eq_zero h)
    have hrpos : 0 < k % N := lt_of_le_of_ne (Int.emod_nonneg k hNpos.ne') (Ne.symm hr0)
    have hrlt : k % N < N := Int.emod_lt_of_pos k hNpos
    rcases le_or_gt (2 * (k % N)) N with h2 | h2
    · exact not_dvd_zpow_sub_one_of_pos_of_le ha hdisc hv hn hm hident hrpos h2 hr
    · have hcomp := dvd_zpow_sub_sub_one _ _ hlevel hr
      exact not_dvd_zpow_sub_one_of_pos_of_le ha hdisc hv hn hm hident (by omega) (by omega) hcomp
  · rintro ⟨l, rfl⟩
    exact dvd_zpow_mul_sub_one _ _ hlevel l

/-- **No power of `v` is `-1` modulo `d`** under the level identity. This is the exclusion of
`-I` from `S_d(Q)` in the proof of [AFK25, Theorem 4.50, `tm:symgp`]. -/
theorem not_dvd_zpow_add_one
    (hv : 1 < (monicNormOneUnitReal ha hdisc v : ℝ)) (hn : 0 < n) (hm : 0 < m)
    (hident : (((v : Q.MonicOrderˣ) : Q.MonicOrder) ^ n) ^ (2 * m + 1) - 1 =
      (d : Q.MonicOrder) * ((((v : Q.MonicOrderˣ) : Q.MonicOrder) ^ n) ^ m *
        (((v : Q.MonicOrderˣ) : Q.MonicOrder) ^ n - 1))) (s : ℤ) :
    ¬ (d : Q.MonicOrder) ∣ (((v : Q.MonicOrderˣ) ^ s : Q.MonicOrderˣ) : Q.MonicOrder) + 1 := by
  intro hs
  set N : ℤ := ((n * (2 * m + 1) : ℕ) : ℤ) with hN
  have hNpos : 0 < N := by
    rw [hN]; positivity
  -- `d ∣ v^{2s} - 1`, so `N ∣ 2s`.
  have h2s : (d : Q.MonicOrder) ∣
      (((v : Q.MonicOrderˣ) ^ (2 * s) : Q.MonicOrderˣ) : Q.MonicOrder) - 1 := by
    have hfactor : (((v : Q.MonicOrderˣ) ^ (2 * s) : Q.MonicOrderˣ) : Q.MonicOrder) - 1 =
        ((((v : Q.MonicOrderˣ) ^ s : Q.MonicOrderˣ) : Q.MonicOrder) + 1) *
          ((((v : Q.MonicOrderˣ) ^ s : Q.MonicOrderˣ) : Q.MonicOrder) - 1) := by
      rw [two_mul, zpow_add, Units.val_mul]
      ring
    rw [hfactor]
    exact dvd_mul_of_dvd_left hs _
  obtain ⟨q, hq⟩ := (dvd_zpow_sub_one_iff ha hdisc hv hn hm hident (2 * s)).1 h2s
  rw [← hN] at hq
  -- `N ∤ s`: otherwise `d` divides both `v^s - 1` and `v^s + 1`, hence `2`.
  have hnot : ¬ N ∣ s := by
    intro hNs
    have h1 := (dvd_zpow_sub_one_iff ha hdisc hv hn hm hident s).2 hNs
    have h2 : (d : Q.MonicOrder) ∣ (2 : Q.MonicOrder) := by
      have := dvd_sub hs h1
      rwa [show (((v : Q.MonicOrderˣ) ^ s : Q.MonicOrderˣ) : Q.MonicOrder) + 1 -
          ((((v : Q.MonicOrderˣ) ^ s : Q.MonicOrderˣ) : Q.MonicOrder) - 1) = 2 by ring] at this
    exact not_dvd_pow_add_one_of_two_mul_le ha hdisc hv hn hm hident (k := 0)
      (by omega) (by simpa only [pow_zero, one_add_one_eq_two] using h2)
  -- So `q` is odd, `N` is even, and `s ≡ N/2 (mod N)`.
  have hodd : q % 2 = 1 := by
    rcases Int.emod_two_eq_zero_or_one q with h | h
    · exfalso
      apply hnot
      obtain ⟨p, hp⟩ := Int.dvd_of_emod_eq_zero h
      refine ⟨p, ?_⟩
      have h2 : 2 * s = 2 * (N * p) := by rw [hq, hp]; ring
      linarith
    · exact h
  obtain ⟨p, hp⟩ : ∃ p, q = 2 * p + 1 := ⟨q / 2, by omega⟩
  have h2 : 2 * s = 2 * (N * p) + N := by rw [hq, hp]; ring
  have hhalf : N * p ≤ s := by linarith
  -- `d ∣ v^{s - Np} + 1` with `2(s - Np) = N`.
  have hNp := (dvd_zpow_sub_one_iff ha hdisc hv hn hm hident (N * p)).2 (dvd_mul_right N p)
  have hred := dvd_zpow_sub_add_one _ _ hs hNp
  have hk : 0 ≤ s - N * p := by linarith
  obtain ⟨k, hk'⟩ : ∃ k : ℕ, s - N * p = k := ⟨(s - N * p).toNat, (Int.toNat_of_nonneg hk).symm⟩
  rw [hk', zpow_natCast, Units.val_pow_eq_pow_val] at hred
  have h2k : (2 : ℤ) * k = ((n * (2 * m + 1) : ℕ) : ℤ) := by rw [← hN]; linarith
  exact not_dvd_pow_add_one_of_two_mul_le ha hdisc hv hn hm hident (k := k)
    (by exact_mod_cast h2k.le) hred

end Level

end BinaryQF

end SIC

end
