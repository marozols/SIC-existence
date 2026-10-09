/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Quadratic.FormOrders

/-!
# Norm-one units of a real quadratic order

The norm-one units of the order are `±v^k` for a fundamental norm-one unit `v`.

This file proves that the norm-one units of the coordinate order `ℤ[ρ]` of a monic form
`Q = ⟨1, b, c⟩` of positive discriminant are `±v^k` for a fundamental unit `v`: the unit above
`1` closest to `1` in the selected real embedding. This is [AFK25, equation (4.45),
`eq:upftrmsw`], the structure of the positive norm unit group `𝒰_f^+` of an order, which the
source takes from the generalization of Dirichlet's unit theorem to orders [70, Koch (2000)]; for
the automorphism group of a form it is [21, Buchmann and Vollmer (2007), Theorem 6.12.4].

The field-level counterpart, the fundamental positive norm unit `ε` of the maximal order `𝒪_K`
characterized by `IsFundamentalPositiveNormUnit` in `SICs.Quadratic.Towers`, is constructed in
`SICs.Quadratic.FundamentalUnits` from Dirichlet's unit theorem. This file works instead in the
possibly nonmaximal order `ℤ[ρ]` of a form, where `ε` need not lie, and uses no field at all.

## Mathematical argument

Let `ι : ℤ[ρ] → ℝ` evaluate at the selected root `ρ = (-b + √Δ)/2`, where `Δ = b² - 4c > 0`. For
every `z`, `ι(z) ι(z̄) = Nm(z)`, `ι(z) + ι(z̄) = Tr(z)`, and `ι(z) - ι(z̄) = y√Δ` where `y` is the
root coordinate of `z`. For a norm-one unit `u` this makes `ι(u)` nonzero with
`ι(ū) = ι(u)⁻¹`, so `Tr(u) = ι(u) + ι(u)⁻¹`.

* **Rigidity.** If `ι(u) = 1` then `ι(ū) = 1`, so `y = 0`, so `u` is the integer `x` with
  `ι(u) = x = 1`: `u = 1`. No irrationality is needed, only `Δ > 0`.
* **A fundamental unit exists** as soon as some unit has `ι(u) > 1`: then `Tr(u)` is an integer
  greater than `2`, and `x ↦ x + x⁻¹` is increasing on `x > 1`, so a unit with the least such
  trace has the least real value above `1`.
* **Descent.** Given `u` with `ι(u) ≥ 1` and the fundamental unit `v`, choose `k` with
  `ι(v)^k ≤ ι(u) < ι(v)^{k+1}`; then `w = u v^{-k}` has `1 ≤ ι(w) < ι(v)`, so `ι(w) = 1` by
  minimality and `w = 1` by rigidity. Units with `0 < ι(u) < 1` are handled by inversion, and
  units with `ι(u) < 0` by negation.

This is the classical descent for the Pell equation, the argument of Mathlib's
`Pell.IsFundamental.eq_zpow_or_neg_zpow` transported to the order; the source cites Dirichlet's
theorem for orders instead, and [21] argues through the cycle of reduced forms.
-/

noncomputable section

namespace SIC.BinaryQF

variable {Q : BinaryQF} (ha : Q.a = 1) (hdisc : 0 < Q.disc)

/-! ### Symmetric functions in the real embedding

The real value of the conjugate `z̄ = star z` is the other root of the quadratic equation of `z`,
which evaluates the norm and the trace as `ι(z) ι(z̄)` and `ι(z) + ι(z̄)`. -/

/-- The real embedding multiplies to the norm: `ι(z) ι(z̄) = Nm(z)`. -/
lemma monicOrderReal_mul_star (z : Q.MonicOrder) :
    monicOrderReal ha hdisc.le z * monicOrderReal ha hdisc.le (star z) = (z.norm : ℝ) := by
  rw [← map_mul, ← QuadraticAlgebra.algebraMap_norm_eq_mul_star]
  simp

/-- The real embedding adds to the trace: `ι(z) + ι(z̄) = Tr(z)`. -/
lemma monicOrderReal_add_star (z : Q.MonicOrder) :
    monicOrderReal ha hdisc.le z + monicOrderReal ha hdisc.le (star z) =
      ((QuadraticAlgebra.trace z : ℤ) : ℝ) := by
  rw [← map_add, ← QuadraticAlgebra.algebraMap_trace_eq_add_star]
  simp

/-- The real embedding separates conjugates by the root coordinate: `ι(z) - ι(z̄) = y√Δ`. -/
lemma monicOrderReal_sub_star (z : Q.MonicOrder) :
    monicOrderReal ha hdisc.le z - monicOrderReal ha hdisc.le (star z) =
      (z.im : ℝ) * Real.sqrt Q.disc := by
  rw [monicOrderReal_apply, monicOrderReal_apply, QuadraticAlgebra.re_star,
    QuadraticAlgebra.im_star]
  have hroot := Q.two_mul_a_mul_rootPlus (by omega)
  rw [ha] at hroot
  push_cast at hroot
  push_cast
  have hroot' : 2 * Q.rootPlus = -(Q.b : ℝ) + Real.sqrt Q.disc := by
    nlinarith [hroot]
  calc
    (z.re : ℝ) + z.im * Q.rootPlus -
        ((z.re : ℝ) + -Q.b * z.im + -z.im * Q.rootPlus) =
      (z.im : ℝ) * (2 * Q.rootPlus + Q.b) := by ring
    _ = (z.im : ℝ) * Real.sqrt Q.disc := by rw [hroot']; ring

/-- **Rigidity:** a norm-one element with real value `1` is `1`. Its conjugate also has real value
`1`, so its root coordinate vanishes and it is the integer `1`. -/
lemma eq_one_of_monicOrderReal_eq_one {z : Q.MonicOrder} (hnorm : z.norm = 1)
    (h : monicOrderReal ha hdisc.le z = 1) : z = 1 := by
  have hstar : monicOrderReal ha hdisc.le (star z) = 1 := by
    have hmul := monicOrderReal_mul_star ha hdisc z
    rw [hnorm, Int.cast_one, h, one_mul] at hmul
    exact hmul
  have him : z.im = 0 := by
    have hsub := monicOrderReal_sub_star ha hdisc z
    rw [h, hstar, sub_self] at hsub
    have hsqrt : 0 < Real.sqrt Q.disc := Real.sqrt_pos.2 (by exact_mod_cast hdisc)
    exact_mod_cast (mul_eq_zero.mp hsub.symm |>.resolve_right hsqrt.ne')
  have hre : z.re = 1 := by
    rw [monicOrderReal_apply, him] at h
    have hc : (z.re : ℝ) = 1 := by simpa using h
    exact_mod_cast hc
  apply QuadraticAlgebra.ext
  · simpa only [QuadraticAlgebra.re_one] using hre
  · simpa only [QuadraticAlgebra.im_one] using him

/-! ### Real values of units

Packaging the real embedding as a homomorphism into `ℝˣ` lets integer powers of units be
evaluated by `map_zpow`. -/

/-- The real embedding of the units of the order, `u ↦ ι(u)`, as a homomorphism into `ℝˣ`. -/
def monicUnitReal : Q.MonicOrderˣ →* ℝˣ :=
  Units.map (monicOrderReal ha hdisc.le : Q.MonicOrder →* ℝ)

variable {ha hdisc}

/-- Integer powers commute with the real value of a unit. -/
lemma coe_monicUnitReal_zpow (w : Q.MonicOrderˣ) (k : ℤ) :
    (monicUnitReal ha hdisc (w ^ k) : ℝ) = (monicUnitReal ha hdisc w : ℝ) ^ k := by
  rw [map_zpow, Units.val_zpow_eq_zpow_val]

/-- The norm of a unit of the order is `±1`. -/
lemma norm_eq_one_or_neg_one (u : Q.MonicOrderˣ) :
    (u : Q.MonicOrder).norm = 1 ∨ (u : Q.MonicOrder).norm = -1 :=
  Int.isUnit_iff.mp (u.isUnit.map QuadraticAlgebra.norm)

/-- The root coordinate of a unit with real value above `1` is positive, since
`y√Δ = ι(u) - ι(ū)` and `|ι(ū)| = |ι(u)|⁻¹ < 1`. -/
lemma im_pos_of_one_lt_monicUnitReal {u : Q.MonicOrderˣ}
    (hu : 1 < (monicUnitReal ha hdisc u : ℝ)) :
    0 < (u : Q.MonicOrder).im := by
  let x : ℝ := monicUnitReal ha hdisc u
  let y : ℝ := monicOrderReal ha hdisc.le (star (u : Q.MonicOrder))
  have hx : 0 < x := zero_lt_one.trans hu
  have hmul := monicOrderReal_mul_star ha hdisc (u : Q.MonicOrder)
  have hsub := monicOrderReal_sub_star ha hdisc (u : Q.MonicOrder)
  change x * y = ((u : Q.MonicOrder).norm : ℝ) at hmul
  change x - y = ((u : Q.MonicOrder).im : ℝ) * Real.sqrt Q.disc at hsub
  have hdiff : 0 < x - y := by
    rcases norm_eq_one_or_neg_one u with hnorm | hnorm
    · rw [hnorm, Int.cast_one] at hmul
      have hxy : 0 < x * y := by rw [hmul]; positivity
      have hy : 0 < y := pos_of_mul_pos_right hxy hx.le
      have hylt : y < 1 := by
        by_contra hylt
        have hone : 1 ≤ y := le_of_not_gt hylt
        nlinarith [mul_pos (sub_pos.mpr hu) hy]
      linarith
    · rw [hnorm, Int.cast_neg, Int.cast_one] at hmul
      have hy : y < 0 := neg_of_mul_neg_right (hmul.symm ▸ (by norm_num)) hx.le
      linarith
  rw [hsub] at hdiff
  have hsqrt : 0 < Real.sqrt Q.disc := Real.sqrt_pos.2 (by exact_mod_cast hdisc)
  exact_mod_cast (pos_of_mul_pos_left hdiff hsqrt.le)

variable (ha hdisc)

/-- The real embedding of the norm-one units, `u ↦ ι(u)`, as a homomorphism into `ℝˣ`: the
restriction of `monicUnitReal`. -/
def monicNormOneUnitReal : Q.monicNormOneUnits →* ℝˣ :=
  (monicUnitReal ha hdisc).comp Q.monicNormOneUnits.subtype

/-- The real value of a norm-one unit is the real embedding of its underlying element. -/
@[simp]
lemma coe_monicNormOneUnitReal (u : Q.monicNormOneUnits) :
    (monicNormOneUnitReal ha hdisc u : ℝ) =
      monicOrderReal ha hdisc.le ((u : Q.MonicOrderˣ) : Q.MonicOrder) := rfl

/-- The real value of an integer power of a norm-one unit is the power of its real value. -/
lemma coe_monicNormOneUnitReal_zpow (u : Q.monicNormOneUnits) (k : ℤ) :
    (monicNormOneUnitReal ha hdisc (u ^ k) : ℝ) = (monicNormOneUnitReal ha hdisc u : ℝ) ^ k := by
  exact coe_monicUnitReal_zpow (ha := ha) (hdisc := hdisc) (u : Q.MonicOrderˣ) k

/-- The trace of a norm-one unit is `ι(u) + ι(u)⁻¹`. -/
lemma monicNormOneUnitReal_add_inv (u : Q.monicNormOneUnits) :
    (monicNormOneUnitReal ha hdisc u : ℝ) + (monicNormOneUnitReal ha hdisc u : ℝ)⁻¹ =
      ((QuadraticAlgebra.trace ((u : Q.MonicOrderˣ) : Q.MonicOrder) : ℤ) : ℝ) := by
  let z : Q.MonicOrder := ((u : Q.MonicOrderˣ) : Q.MonicOrder)
  have hmul := monicOrderReal_mul_star ha hdisc z
  have hnorm : z.norm = 1 := u.property
  rw [hnorm, Int.cast_one] at hmul
  have hne : monicOrderReal ha hdisc.le z ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hmul
    exact zero_ne_one hmul
  rw [coe_monicNormOneUnitReal]
  have hstar : monicOrderReal ha hdisc.le (star z) =
      (monicOrderReal ha hdisc.le z)⁻¹ := by
    rw [inv_eq_one_div]
    apply (eq_div_iff hne).2
    nlinarith [hmul]
  rw [← hstar]
  exact monicOrderReal_add_star ha hdisc z

/-- The norm-one case of `im_pos_of_one_lt_monicUnitReal`. -/
lemma im_pos_of_one_lt_monicNormOneUnitReal {u : Q.monicNormOneUnits}
    (hu : 1 < (monicNormOneUnitReal ha hdisc u : ℝ)) :
    0 < ((u : Q.MonicOrderˣ) : Q.MonicOrder).im :=
  im_pos_of_one_lt_monicUnitReal (ha := ha) (hdisc := hdisc) hu

/-- A norm-one unit with real value `1` is the identity, by `eq_one_of_monicOrderReal_eq_one`. -/
lemma eq_one_of_monicNormOneUnitReal_eq_one {u : Q.monicNormOneUnits}
    (h : (monicNormOneUnitReal ha hdisc u : ℝ) = 1) : u = 1 := by
  apply Subtype.ext
  apply Units.ext
  exact eq_one_of_monicOrderReal_eq_one ha hdisc u.property h

/-! ### The fundamental norm-one unit

[AFK25, Definition 4.13, `df:epsilonfDefinition`] singles out the positive norm unit `v_f > 1`
of the order that generates `𝒰_f^+` together with `-1`; here it is characterized as the least
real value above `1`, and the generation statement is the descent theorem below. -/

/-- A norm-one unit `v` is **fundamental** when `ι(v) > 1` and `ι(v) ≤ ι(u)` for every norm-one
unit `u` with `ι(u) > 1`. This is the fundamental positive norm unit `v_f` of
[AFK25, Definition 4.13, `df:epsilonfDefinition`], characterized by minimality. -/
def IsFundamentalNormOneUnit (v : Q.monicNormOneUnits) : Prop :=
  1 < (monicNormOneUnitReal ha hdisc v : ℝ) ∧
    ∀ u : Q.monicNormOneUnits, 1 < (monicNormOneUnitReal ha hdisc u : ℝ) →
      (monicNormOneUnitReal ha hdisc v : ℝ) ≤ monicNormOneUnitReal ha hdisc u

-- From here on `ha` and `hdisc` are implicit, so a result about a fundamental unit is applied as
-- `hv.eq_zpow_or_neg_zpow u`. The definitions above keep them explicit, as in
-- `monicNormOneUnitReal ha hdisc`.
variable {ha hdisc}

/-- A fundamental unit has real value above `1`. -/
lemma IsFundamentalNormOneUnit.one_lt {v : Q.monicNormOneUnits}
    (hv : IsFundamentalNormOneUnit ha hdisc v) : 1 < (monicNormOneUnitReal ha hdisc v : ℝ) :=
  hv.1

/-- A fundamental unit has the least real value above `1`. -/
lemma IsFundamentalNormOneUnit.le {v : Q.monicNormOneUnits}
    (hv : IsFundamentalNormOneUnit ha hdisc v) {u : Q.monicNormOneUnits}
    (hu : 1 < (monicNormOneUnitReal ha hdisc u : ℝ)) :
    (monicNormOneUnitReal ha hdisc v : ℝ) ≤ monicNormOneUnitReal ha hdisc u :=
  hv.2 u hu

/-- Above `1`, the function `x ↦ x + x⁻¹` is strictly increasing. This is used to turn
minimality of integral traces into minimality in the selected real embedding. -/
private lemma add_inv_lt_add_inv {x y : ℝ} (hx : 1 < x) (hxy : x < y) :
    x + x⁻¹ < y + y⁻¹ := by
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hypos : 0 < y := hxpos.trans hxy
  have hprod : 1 < x * y := by nlinarith [mul_pos (sub_pos.mpr hx) hypos]
  have hid : (y + y⁻¹) - (x + x⁻¹) =
      (y - x) * (x * y - 1) / (x * y) := by
    field_simp
    ring
  rw [← sub_pos, hid]
  exact div_pos (mul_pos (sub_pos.mpr hxy) (sub_pos.mpr hprod)) (mul_pos hxpos hypos)

/-- The integral trace of a norm-one unit whose selected real value exceeds `1` is greater
than `2`. This supplies a natural-number measure for the least-unit argument. -/
private lemma two_lt_trace_of_one_lt {u : Q.monicNormOneUnits}
    (hu : 1 < (monicNormOneUnitReal ha hdisc u : ℝ)) :
    2 < QuadraticAlgebra.trace ((u : Q.MonicOrderˣ) : Q.MonicOrder) := by
  let x : ℝ := monicNormOneUnitReal ha hdisc u
  have hxpos : 0 < x := zero_lt_one.trans hu
  have hsq : 0 < (x - 1) ^ 2 := sq_pos_of_pos (sub_pos.mpr hu)
  have hid : x + x⁻¹ - 2 = (x - 1) ^ 2 / x := by
    field_simp
    ring
  have hreal : (2 : ℝ) < x + x⁻¹ := by
    rw [← sub_pos, hid]
    exact div_pos hsq hxpos
  rw [monicNormOneUnitReal_add_inv ha hdisc] at hreal
  exact_mod_cast hreal

/-- **A fundamental unit exists** whenever some norm-one unit has real value above `1`: the
traces of such units are integers greater than `2`, and the least trace gives the least real
value because `x ↦ x + x⁻¹` is increasing on `x > 1`. -/
theorem exists_isFundamentalNormOneUnit (u₀ : Q.monicNormOneUnits)
    (h₀ : 1 < (monicNormOneUnitReal ha hdisc u₀ : ℝ)) :
    ∃ v : Q.monicNormOneUnits, IsFundamentalNormOneUnit ha hdisc v := by
  classical
  let P : ℕ → Prop := fun n ↦ ∃ u : Q.monicNormOneUnits,
    1 < (monicNormOneUnitReal ha hdisc u : ℝ) ∧
      QuadraticAlgebra.trace ((u : Q.MonicOrderˣ) : Q.MonicOrder) ≤ n
  have htrace₀ : 0 ≤ QuadraticAlgebra.trace ((u₀ : Q.MonicOrderˣ) : Q.MonicOrder) :=
    (two_lt_trace_of_one_lt h₀).le.trans' (by omega)
  have hex : ∃ n, P n := by
    refine ⟨(Int.toNat (QuadraticAlgebra.trace ((u₀ : Q.MonicOrderˣ) : Q.MonicOrder))),
      u₀, h₀, ?_⟩
    rw [Int.toNat_of_nonneg htrace₀]
  obtain ⟨v, hv, htracev⟩ := Nat.find_spec hex
  refine ⟨v, hv, fun u hu ↦ ?_⟩
  by_contra hle
  have huv : (monicNormOneUnitReal ha hdisc u : ℝ) <
      monicNormOneUnitReal ha hdisc v := lt_of_not_ge hle
  have hreal := add_inv_lt_add_inv hu huv
  rw [monicNormOneUnitReal_add_inv ha hdisc,
    monicNormOneUnitReal_add_inv ha hdisc] at hreal
  have htraceuv : QuadraticAlgebra.trace ((u : Q.MonicOrderˣ) : Q.MonicOrder) <
      QuadraticAlgebra.trace ((v : Q.MonicOrderˣ) : Q.MonicOrder) := by
    exact_mod_cast hreal
  have htraceu : 0 ≤ QuadraticAlgebra.trace ((u : Q.MonicOrderˣ) : Q.MonicOrder) :=
    (two_lt_trace_of_one_lt hu).le.trans' (by omega)
  let m := Int.toNat (QuadraticAlgebra.trace ((u : Q.MonicOrderˣ) : Q.MonicOrder))
  have hmP : P m := by
    refine ⟨u, hu, ?_⟩
    dsimp [m]
    rw [Int.toNat_of_nonneg htraceu]
  have hmn : m < Nat.find hex := by
    dsimp [m]
    rw [Int.toNat_lt htraceu]
    exact lt_of_lt_of_le htraceuv htracev
  exact Nat.find_min hex hmn hmP

/-- A norm-one unit whose selected real value is at least `1` is a natural power of a
fundamental unit. The proof is the Archimedean descent interval argument. -/
private lemma eq_pow_of_one_le {v u : Q.monicNormOneUnits}
    (hv : IsFundamentalNormOneUnit ha hdisc v)
    (hu : 1 ≤ (monicNormOneUnitReal ha hdisc u : ℝ)) : ∃ n : ℕ, u = v ^ n := by
  let x : ℝ := monicNormOneUnitReal ha hdisc u
  let y : ℝ := monicNormOneUnitReal ha hdisc v
  obtain ⟨n, hnle, hnlt⟩ := exists_nat_pow_near hu hv.one_lt
  change y ^ n ≤ x at hnle
  change x < y ^ (n + 1) at hnlt
  let w : Q.monicNormOneUnits := u * (v ^ n)⁻¹
  have hypow : 0 < y ^ n := pow_pos (zero_lt_one.trans hv.one_lt) n
  have hwreal : (monicNormOneUnitReal ha hdisc w : ℝ) = x / y ^ n := by
    simp [w, x, y, div_eq_mul_inv]
  have hwle : 1 ≤ (monicNormOneUnitReal ha hdisc w : ℝ) := by
    rw [hwreal]
    exact (le_div_iff₀ hypow).2 (by simpa using hnle)
  have hwlt : (monicNormOneUnitReal ha hdisc w : ℝ) < y := by
    rw [hwreal]
    apply (div_lt_iff₀ hypow).2
    simpa [pow_succ, mul_comm] using hnlt
  have hwone : (monicNormOneUnitReal ha hdisc w : ℝ) = 1 := by
    rcases hwle.eq_or_lt with hw | hw
    · exact hw.symm
    · exact False.elim ((not_le_of_gt hwlt)
        (IsFundamentalNormOneUnit.le (ha := ha) (hdisc := hdisc) hv hw))
  have heq : w = 1 := eq_one_of_monicNormOneUnitReal_eq_one ha hdisc hwone
  refine ⟨n, ?_⟩
  exact mul_inv_eq_one.mp heq

/-- A norm-one unit with positive selected real value is an integer power of a fundamental
unit; values below `1` are reduced to the preceding lemma by inversion. -/
private lemma eq_zpow_of_pos {v u : Q.monicNormOneUnits}
    (hv : IsFundamentalNormOneUnit ha hdisc v)
    (hu : 0 < (monicNormOneUnitReal ha hdisc u : ℝ)) : ∃ k : ℤ, u = v ^ k := by
  by_cases hone : 1 ≤ (monicNormOneUnitReal ha hdisc u : ℝ)
  · obtain ⟨n, hn⟩ := eq_pow_of_one_le hv hone
    exact ⟨n, by simpa using hn⟩
  · have hinv : 1 ≤ (monicNormOneUnitReal ha hdisc u⁻¹ : ℝ) := by
      simp only [map_inv, Units.val_inv_eq_inv_val]
      exact (one_le_inv₀ hu).2 (le_of_not_ge hone)
    obtain ⟨n, hn⟩ := eq_pow_of_one_le hv hinv
    refine ⟨-(n : ℤ), ?_⟩
    have hinveq : u = (v ^ n)⁻¹ := by
      rw [← hn]
      exact inv_inv u
    simpa using hinveq

/-- **Descent:** every norm-one unit is `±v^k` for a fundamental unit `v`. This is
[AFK25, equation (4.45), `eq:upftrmsw`], and [21, Buchmann and Vollmer (2007), Theorem 6.12.4],
which states it for the automorphism group of the form, corresponding to the norm-one units of
its order. -/
@[source "21, Theorem 6.12.4, p. 133 (norm-one units in place of automorphs)"]
theorem IsFundamentalNormOneUnit.eq_zpow_or_neg_zpow {v : Q.monicNormOneUnits}
    (hv : IsFundamentalNormOneUnit ha hdisc v) (u : Q.monicNormOneUnits) :
    ∃ k : ℤ, (u : Q.MonicOrderˣ) = (v : Q.MonicOrderˣ) ^ k ∨
      (u : Q.MonicOrderˣ) = -((v : Q.MonicOrderˣ) ^ k) := by
  let negOne : Q.monicNormOneUnits := ⟨-1, by
    rw [Q.mem_monicNormOneUnits_iff]
    simp⟩
  have hnegOne : (monicNormOneUnitReal ha hdisc negOne : ℝ) = -1 := by
    rw [coe_monicNormOneUnitReal]
    change monicOrderReal ha hdisc.le (-1 : Q.MonicOrder) = -1
    rw [map_neg, map_one]
  have hne : (monicNormOneUnitReal ha hdisc u : ℝ) ≠ 0 := Units.ne_zero _
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · let w : Q.monicNormOneUnits := negOne * u
    have hwpos : 0 < (monicNormOneUnitReal ha hdisc w : ℝ) := by
      rw [map_mul, Units.val_mul, hnegOne, neg_one_mul]
      exact neg_pos.mpr hneg
    obtain ⟨k, hk⟩ := eq_zpow_of_pos hv hwpos
    refine ⟨k, Or.inr ?_⟩
    have hcoew : (w : Q.MonicOrderˣ) = (v : Q.MonicOrderˣ) ^ k := congrArg Subtype.val hk
    simpa [w, negOne] using congrArg Neg.neg hcoew
  · obtain ⟨k, hk⟩ := eq_zpow_of_pos hv hpos
    exact ⟨k, Or.inl (congrArg Subtype.val hk)⟩

/-- A norm-one unit with real value above `1` is a positive power of the fundamental unit. -/
theorem IsFundamentalNormOneUnit.exists_eq_pow_of_one_lt {v : Q.monicNormOneUnits}
    (hv : IsFundamentalNormOneUnit ha hdisc v) {u : Q.monicNormOneUnits}
    (hu : 1 < (monicNormOneUnitReal ha hdisc u : ℝ)) :
    ∃ n : ℕ, 0 < n ∧ u = v ^ n := by
  obtain ⟨k, hk⟩ := eq_zpow_of_pos hv (zero_lt_one.trans hu)
  have hreal : (monicNormOneUnitReal ha hdisc u : ℝ) =
      (monicNormOneUnitReal ha hdisc v : ℝ) ^ k := by
    rw [hk, coe_monicNormOneUnitReal_zpow]
  have hkpos : 0 < k := (one_lt_zpow_iff_right₀ hv.one_lt).mp (hreal ▸ hu)
  let n := k.toNat
  have hkn : (n : ℤ) = k := Int.toNat_of_nonneg hkpos.le
  refine ⟨n, ?_, ?_⟩
  · apply Int.natCast_pos.mp
    rw [hkn]
    exact hkpos
  · calc
      u = v ^ k := hk
      _ = v ^ n := by rw [← hkn, zpow_natCast]

end SIC.BinaryQF

end
