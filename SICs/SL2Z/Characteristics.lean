/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SL2Z.FractionalLinear

/-!
# Rational characteristics and their integral cocycle indices

Rational characteristics, congruence subgroups, the pairing `⟨⟨r,τ⟩⟩` at a point of any division
ring, integral indices, and covariance.

This file collects the arithmetic in [AFK25, Definition 1.17, `dfn:gammarDef`], equations
(1.24), `eq:FractionalSymplecticForm`, (1.25), `eq:LActOnSymplecticInnerProduct`, and
(1.26), `eq:shindf`. Membership in `Γ_r` means `(M-I)r ∈ ℤ²`; its witnesses supply the
integer index `n_QP(r,M)` and the characteristic's lattice translations at a fixed point.

Clearing the Jacobi denominator proves covariance of the fractional symplectic form. Its affine
dependence on the modulus gives continuity at the real boundary. An integer matrix of determinant
`±1` preserves integrality of characteristics; conjugation transports `Γ_r` to the subgroup for
the transformed characteristic. These identities are shared by the upper-half-plane and real word
constructions. No cocycle value or special-function domain is defined here.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### Congruence subgroups

The subgroup `Γ_r` is expressed by integrality of `(M - I)r`.  Closure under inversion and
invariance under integral translation of `r` provide the membership facts used by modular-cocycle
identities. -/

/-- The subgroup `Γ_r ⊆ SL₂(ℤ)` for `r ∈ ℚ²`:
    `Γ_r = {M ∈ SL₂(ℤ) : (M - I)r ∈ ℤ²}`.
    See [AFK25, Definition 1.17, `dfn:gammarDef`]. -/
@[source "AFK25, Definition 1.17, p. 10, dfn:gammarDef" (symbol := "Γ_r")]
def gammaSubgroup (r : Fin 2 → ℚ) : Subgroup SL(2, ℤ) where
  carrier := {M | ∀ i, ∃ n : ℤ,
    ∑ j, (((M : Mat(2, ℤ)) i j : ℚ) - if i = j then 1 else 0) * r j =
      (n : ℚ)}
  one_mem' := by
    intro i
    exact ⟨0, by simp [Matrix.one_apply]⟩
  mul_mem' := by
    intro M N hM hN i
    obtain ⟨n₀, hn₀⟩ := hN 0
    obtain ⟨n₁, hn₁⟩ := hN 1
    obtain ⟨m, hm⟩ := hM i
    refine ⟨M i 0 * n₀ + M i 1 * n₁ + m, ?_⟩
    fin_cases i <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two] at hn₀ hn₁ hm ⊢ <;>
      linear_combination (M _ 0 : ℚ) * hn₀ + (M _ 1 : ℚ) * hn₁ + hm
  inv_mem' := by
    intro M hM
    obtain ⟨n₀, hn₀⟩ := hM 0
    obtain ⟨n₁, hn₁⟩ := hM 1
    intro i
    refine ⟨-(M⁻¹ i 0 * n₀ + M⁻¹ i 1 * n₁), ?_⟩
    have h := congrArg (fun A : SL(2, ℤ) => ∑ j, (A i j : ℚ) * r j)
      (inv_mul_cancel M)
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] at h
    generalize M⁻¹ = N at *
    fin_cases i <;> norm_num [Fin.sum_univ_two, Matrix.one_apply] at h hn₀ hn₁ ⊢ <;>
      linear_combination h - (N _ 0 : ℚ) * hn₀ - (N _ 1 : ℚ) * hn₁

/-- **`Γ_r = Γ_{-r}`.** The integrality condition defining `Γ_r` is linear in `r`, so negating the
characteristic negates each integral witness. This lets the reflection `r ↦ -r` used by the
reciprocity law [AFK25, Theorem 5.8, `thm:nupnumpeq1`] stay inside the subgroup where the cocycle
is defined. -/
lemma neg_mem_gammaSubgroup {r : Fin 2 → ℚ} {M : SL(2, ℤ)}
    (hM : M ∈ gammaSubgroup r) : M ∈ gammaSubgroup (-r) := by
  intro i
  obtain ⟨n, hn⟩ := hM i
  refine ⟨-n, ?_⟩
  rw [Fin.sum_univ_two] at hn ⊢
  simp only [Pi.neg_apply]
  push_cast
  linear_combination -hn

/-- **`Γ_r` is closed under inversion.** Since `M⁻¹ - I = -M⁻¹(M - I)` and `M⁻¹` is integral,
integrality of `(M - I)r` transfers to `(M⁻¹ - I)r`; explicitly, the witnesses transform by
`(m₀, m₁) = (-M₁₁n₀ + M₀₁n₁, M₁₀n₀ - M₀₀n₁)`. The source calls `Γ_r`
a subgroup without proof; this is the half of that claim needed to know the cocycle applies at
`M⁻¹` whenever it applies at `M` (`sfModularCocycleRealInv`). -/
lemma inv_mem_gammaSubgroup {r : Fin 2 → ℚ} {M : SL(2, ℤ)}
    (hM : M ∈ gammaSubgroup r) : M⁻¹ ∈ gammaSubgroup r :=
  (gammaSubgroup r).inv_mem hM

/-- **`Γ_r` only sees `r` modulo `ℤ²`.** Adding an integer vector to `r` changes `(M - I)r` by
`(M - I)s`, which is integral for every integer matrix, so the defining condition of
`gammaSubgroup` is unaffected. This is what lets
`sfModularCocycleReal_add_intVec`
state its conclusion at `r + s` without a second membership hypothesis. -/
lemma add_intVec_mem_gammaSubgroup {r : Fin 2 → ℚ} {M : SL(2, ℤ)}
    (hM : M ∈ gammaSubgroup r) (s : Fin 2 → ℤ) :
    M ∈ gammaSubgroup (r + fun i => (s i : ℚ)) := by
  intro i
  obtain ⟨n, hn⟩ := hM i
  rw [Fin.sum_univ_two] at hn
  fin_cases i
  · refine ⟨n + (M 0 0 - 1) * s 0 + M 0 1 * s 1, ?_⟩
    rw [Fin.sum_univ_two]
    simp only [Pi.add_apply] at hn ⊢
    norm_num at hn ⊢
    linarith
  · refine ⟨n + M 1 0 * s 0 + (M 1 1 - 1) * s 1, ?_⟩
    rw [Fin.sum_univ_two]
    simp only [Pi.add_apply] at hn ⊢
    norm_num at hn ⊢
    linarith

/-! ### The fractional symplectic form

The characteristic `r` determines `⟨⟨r,τ⟩⟩ = r₁τ-r₀`, the argument in
[AFK25, equation (1.24), `eq:FractionalSymplecticForm`]. Like the Möbius action of
`SICs.SL2Z.FractionalLinear`, it is defined at a point `τ` of any division ring `K`: `K = ℂ`
for the upper-half-plane cocycle, `K = ℝ` for the real cocycle, and `K` a number field for
the lattice arithmetic of `SICs.Quadratic.LatticeUnits`. Ring homomorphisms commute with it
(`map_fracSymplecticFormRat`), and it is `ℚ`-linear in the characteristic. -/

section DivisionRing

variable {K L : Type*} [DivisionRing K] [DivisionRing L]

/-- The fractional symplectic form `⟨⟨r,τ⟩⟩ = r₁τ - r₀` at a rational point `r ∈ ℚ²` and a
    point `τ` of a division ring `K` ([AFK25, equation (1.24), `eq:FractionalSymplecticForm`]).
    A named declaration rather than an inline `let`, with its transformation law supplied by
    `fracSymplecticFormRat_ratVecAction`. Kopp's `w_0 = ⟨⟨r_0, β⟩⟩ ∈ F` and
    `w_n = ⟨⟨r_n, β_n⟩⟩ ∈ F` of [72, Kopp (2024), Definition 7.4, `defn:cycledata`] are its
    values in a real quadratic field `F`. -/
def fracSymplecticFormRat (r : Fin 2 → ℚ) (τ : K) : K :=
  (r 1 : K) * τ - (r 0 : K)

/-- **A ring homomorphism commutes with the fractional symplectic form**:
`f(⟨⟨r, τ⟩⟩) = ⟨⟨r, f(τ)⟩⟩`, since `f` fixes `ℚ` (`map_ratCast`). -/
theorem map_fracSymplecticFormRat (f : K →+* L) (r : Fin 2 → ℚ) (τ : K) :
    f (fracSymplecticFormRat r τ) = fracSymplecticFormRat r (f τ) := by
  simp [fracSymplecticFormRat]

/-- **The fractional symplectic form is odd in its characteristic**: `⟨⟨-r,τ⟩⟩ = -⟨⟨r,τ⟩⟩`. It is
linear in `r`, so the reflection `r ↦ -r` of the reciprocity identity [AFK25, Theorem 5.8,
`thm:nupnumpeq1`] reaches the cocycle as the argument reflection `z ↦ -z`. -/
lemma fracSymplecticFormRat_neg (r : Fin 2 → ℚ) (τ : K) :
    fracSymplecticFormRat (-r) τ = -fracSymplecticFormRat r τ := by
  simp only [fracSymplecticFormRat, Pi.neg_apply, Rat.cast_neg, neg_mul]
  abel

/-- The fractional symplectic form is additive in the characteristic, in characteristic zero
(where the rational cast is additive). -/
theorem fracSymplecticFormRat_add [CharZero K] (u v : Fin 2 → ℚ) (τ : K) :
    fracSymplecticFormRat (u + v) τ =
      fracSymplecticFormRat u τ + fracSymplecticFormRat v τ := by
  simp only [fracSymplecticFormRat, Pi.add_apply, Rat.cast_add, add_mul]
  abel

/-- The fractional symplectic form respects differences of characteristics, in characteristic
zero. -/
theorem fracSymplecticFormRat_sub [CharZero K] (u v : Fin 2 → ℚ) (τ : K) :
    fracSymplecticFormRat (u - v) τ =
      fracSymplecticFormRat u τ - fracSymplecticFormRat v τ := by
  simp only [fracSymplecticFormRat, Pi.sub_apply, Rat.cast_sub, sub_mul]
  abel

/-- **The fractional symplectic form is homogeneous in the characteristic**:
`⟨⟨q•r, τ⟩⟩ = q·⟨⟨r, τ⟩⟩` for `q ∈ ℚ` (`Rat.cast_mul`). -/
theorem fracSymplecticFormRat_smul [CharZero K] (q : ℚ) (r : Fin 2 → ℚ) (τ : K) :
    fracSymplecticFormRat (q • r) τ = (q : K) * fracSymplecticFormRat r τ := by
  simp only [fracSymplecticFormRat, Pi.smul_apply, smul_eq_mul, Rat.cast_mul, mul_assoc, mul_sub]

end DivisionRing

/-- `fracSymplecticFormRat` commutes with the cast `ℝ → ℂ`: `map_fracSymplecticFormRat` at
`Complex.ofRealHom`, stated for the cast so that `norm_cast` can use it. -/
@[simp, norm_cast]
lemma ofReal_fracSymplecticFormRat (r : Fin 2 → ℚ) (τ : ℝ) :
    ((fracSymplecticFormRat r τ : ℝ) : ℂ) = fracSymplecticFormRat r (τ : ℂ) :=
  map_fracSymplecticFormRat Complex.ofRealHom r τ

/-- **The fractional symplectic form is continuous in the modulus**: it is affine in `τ`, and at a
real limit point its value is the form at that real point. This is the complex/real transport
used to follow the period product to the boundary (`SICs.Cocycle.ModularBoundary`), matching
`fltDenominator_tendsto` for the Jacobi denominator. -/
theorem fracSymplecticFormRat_tendsto {ι : Type*} {l : Filter ι} (r : Fin 2 → ℚ) {f : ι → ℂ}
    {τ : ℝ} (h : Filter.Tendsto f l (nhds (τ : ℂ))) :
    Filter.Tendsto (fun k => fracSymplecticFormRat r (f k)) l
      (nhds ((fracSymplecticFormRat r τ : ℝ) : ℂ)) := by
  rw [ofReal_fracSymplecticFormRat]
  unfold fracSymplecticFormRat
  exact (tendsto_const_nhds.mul h).sub tendsto_const_nhds

/-! ### The rational index

The second coordinate of `(I-M)r` is the index in [AFK25, equation (1.26), `eq:shindf`]. -/

/-- The finite shift index `n_QP(r,M) := ((I-M)r)₂ = -M₁₀ r₀ + (1-M₁₁) r₁` appearing in the
    denominator of [AFK25, equation (1.26), `eq:shindf`]. The paper assumes `M ∈ Γ_r`
    (`gammaSubgroup`), so this is an integer; `nQPInt` is that integer, proved
    equal to this `ℚ`-valued formula on `Γ_r` by `nQPInt_cast_of_mem`. -/
def nQP (r : Fin 2 → ℚ) (M : Mat(2, ℤ)) : ℚ :=
  -(M 1 0 : ℚ) * r 0 + (1 - (M 1 1 : ℚ)) * r 1

/-- **The index is linear in the characteristic**, so negating it negates the index:
`n_QP(-r,M) = -n_QP(r,M)`. This is one of the two reflection inputs to the reciprocity law
[AFK25, Theorem 5.8, `thm:nupnumpeq1`], the other being the double-sine reflection of
`SICs.Cocycle.SigmaS.Reflection.sigmaSHonest_mul_neg_closed`. -/
lemma nQP_neg (r : Fin 2 → ℚ) (M : Mat(2, ℤ)) :
    nQP (-r) M = -nQP r M := by
  simp only [nQP, Pi.neg_apply]
  ring

/-! ### The rational-index transformation law

The transformed rational index is paired with the Möbius action so that the fractional
symplectic form acquires exactly the Jacobi denominator.  This is the algebraic covariance used by
the cocycle arguments. -/

/-- `M`'s action on a rational index vector `r`, casting `M`'s integer entries to `ℚ`. -/
def ratVecAction (M : Mat(2, ℤ)) (r : Fin 2 → ℚ) : Fin 2 → ℚ :=
  (M.map (Int.cast : ℤ → ℚ)).mulVec r

/-- Membership `M ∈ Γ_r` says exactly that the transformed rational index differs from `r` by
an integer vector: `M r-r ∈ ℤ²`. This is the form used when a cocycle multiplication step changes
the characteristic from `r` to `M r` before applying index periodicity. -/
theorem ratVecAction_sub_intVec_of_mem_gammaSubgroup {M : SL(2, ℤ)}
    {r : Fin 2 → ℚ} (hM : M ∈ gammaSubgroup r) :
    ∀ i, ∃ m : ℤ,
      ratVecAction (M : Mat(2, ℤ)) r i - r i = (m : ℚ) := by
  intro i
  obtain ⟨m, hm⟩ := hM i
  refine ⟨m, ?_⟩
  fin_cases i <;>
    simp only [ratVecAction, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.map_apply] at hm ⊢ <;>
    norm_num at hm ⊢ <;>
    linarith

/-- **The general fractional-symplectic-form transformation law**
([AFK25, equation (1.25), `eq:LActOnSymplecticInnerProduct`]): for any integer matrix `M`, rational
vector `r`, and point `τ` of a field `K` of characteristic zero with nonzero Jacobi denominator,
`⟨M·r, M·τ⟩ = det(M)·⟨r,τ⟩ / j_M(τ)`. No fixed-point hypothesis on `τ` is needed. -/
theorem fracSymplecticFormRat_ratVecAction {K : Type*} [Field K] [CharZero K]
    (M : Mat(2, ℤ)) (r : Fin 2 → ℚ) (τ : K) (hτ : fltDenominator M τ ≠ 0) :
    fracSymplecticFormRat (ratVecAction M r) (flt M τ) =
      (M.det : K) * fracSymplecticFormRat r τ / fltDenominator M τ := by
  unfold fracSymplecticFormRat ratVecAction flt fltDenominator at *
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply]
  rw [Matrix.det_fin_two]
  push_cast
  field_simp
  ring

/-! ### The integer index `n_QP(r,M)`

Membership in `Γ_r` supplies an integral witness for the second coordinate of `(I - M)r`.
Uniqueness makes this witness a canonical integer index, rather than a rounded rational value. -/

/-- **The index `nQP` as an integer.**
`nQP` is `ℚ`-valued because its defining formula `((I-M)r)₂` makes
sense for every integer matrix; on `Γ_r` it takes integer values, and `nQPInt` is that integer
(`nQPInt_cast_of_mem`).

Outside `Γ_r`, taking the numerator of a non-integral rational has no intended cocycle meaning.
Identification with the source's integral index therefore requires subgroup membership;
identities of the numerator itself, such as negation, remain unconditional. -/
def nQPInt (r : Fin 2 → ℚ) (M : Mat(2, ℤ)) : ℤ :=
  (nQP r M).num

/-- **On `Γ_r` the index is genuinely integral**: `nQPInt r M` casts back to `n_QP(r,M)`.
Membership in `gammaSubgroup r` gives an integer `n` with `((M - I)r)₂ = n`, while
`n_QP(r,M) = ((I - M)r)₂` is its negative. -/
theorem nQPInt_cast_of_mem {r : Fin 2 → ℚ} {M : SL(2, ℤ)}
    (hM : M ∈ gammaSubgroup r) :
    ((nQPInt r (M : Mat(2, ℤ)) : ℤ) : ℚ) =
      nQP r (M : Mat(2, ℤ)) := by
  obtain ⟨n, hn⟩ := hM 1
  rw [Fin.sum_univ_two] at hn
  have : nQP r M = ((-n : ℤ) : ℚ) := by
    rw [nQP]
    push_cast
    norm_num at hn
    linarith
  rw [nQPInt, this, Rat.num_intCast]

/-- **The integer index negates with the characteristic**: `nQPInt (-r) M = -nQPInt r M`.
This needs no membership hypothesis, since `nQP_neg` is an identity of
rationals and `Rat.num` is odd. On `Γ_r` it is the integral reflection law used by the reciprocity
identity [AFK25, Theorem 5.8, `thm:nupnumpeq1`]. -/
lemma nQPInt_neg (r : Fin 2 → ℚ) (M : Mat(2, ℤ)) :
    nQPInt (-r) M = -nQPInt r M := by
  rw [nQPInt, nQPInt, nQP_neg, Rat.neg_num]

/-! ### Integral characteristics and translations at a fixed point

The subgroup witnesses identify the rescaled argument with a lattice translate. These
are the arithmetic inputs to index periodicity and reflection of the real cocycle. -/

/-- The predicate that a rational phase-space index `r` has both coordinates in `ℤ`.

This is the case excluded by `sfModularCocycleReal_add_intVec`, following
[AFK25, Lemma 2.14, `lm:shinperiodicity`]'s own hypothesis `r ∉ ℤ²`. -/
def IsIntegralIndex (r : Fin 2 → ℚ) : Prop := ∀ i, ∃ m : ℤ, r i = (m : ℚ)

/-- For an integral characteristic, `⟨⟨r,τ⟩⟩ = r₁τ - r₀` in integer coordinates. -/
theorem fracSymplecticFormRat_of_isIntegralIndex {K : Type*} [DivisionRing K]
    {r : Fin 2 → ℚ} (hr : IsIntegralIndex r) (τ : K) :
    fracSymplecticFormRat r τ = ((r 1).num : K) * τ - ((r 0).num : K) := by
  obtain ⟨a, ha⟩ := hr 0
  obtain ⟨b, hb⟩ := hr 1
  simp [fracSymplecticFormRat, ha, hb]

/-- For an integral characteristic, the index is the integral second coordinate of `(I-M)r`. -/
theorem nQPInt_of_isIntegralIndex {r : Fin 2 → ℚ} (hr : IsIntegralIndex r)
    (M : Mat(2, ℤ)) :
    nQPInt r M = -(M 1 0) * (r 0).num + (1 - M 1 1) * (r 1).num := by
  obtain ⟨a, ha⟩ := hr 0
  obtain ⟨b, hb⟩ := hr 1
  have haNum : (r 0).num = a := by rw [ha]; simp
  have hbNum : (r 1).num = b := by rw [hb]; simp
  have hq : nQP r M = (((-(M 1 0) * a + (1 - M 1 1) * b : ℤ)) : ℚ) := by
    simp only [nQP, ha, hb]
    push_cast
    ring
  change (nQP r M).num = _
  rw [hq, Rat.num_intCast, haNum, hbNum]

/-- **A rational characteristic has a common denominator**: some positive `N` with `N r ∈ ℤ²`,
namely the product of the two denominators. This produces the hypothesis `∀ i, ∃ t : ℤ, N rᵢ = t`
under which a principal congruence subgroup `Γ(N)` is contained in `Γ_r`
(`mem_gammaSubgroup_of_mem_Gamma`). -/
theorem exists_natCast_mul_eq_intCast (r : Fin 2 → ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, ∃ t : ℤ, (N : ℚ) * r i = (t : ℚ) := by
  have key : ∀ (q : ℚ) (m : ℕ), ∃ t : ℤ, ((q.den * m : ℕ) : ℚ) * q = (t : ℚ) :=
    fun q m => ⟨m * q.num, by
      push_cast
      rw [mul_comm (q.den : ℚ) (m : ℚ), mul_assoc, Rat.den_mul_eq_num]⟩
  refine ⟨(r 0).den * (r 1).den, by positivity, fun i => ?_⟩
  fin_cases i
  · exact key (r 0) (r 1).den
  · rw [Nat.mul_comm]
    exact key (r 1) (r 0).den

/-- **Introduction rule for `IsIntegralIndex`**: checking the two coordinates separately. The
predicate quantifies over `Fin 2`, so every proof of it ends in the same case split; this lemma
performs it once. -/
theorem isIntegralIndex_of_coords {r : Fin 2 → ℚ} (h0 : ∃ m : ℤ, r 0 = (m : ℚ))
    (h1 : ∃ m : ℤ, r 1 = (m : ℚ)) : IsIntegralIndex r := by
  intro i
  fin_cases i
  exacts [h0, h1]

/-- **`(p/d, q/d)` is a nonintegral index exactly when `d ∤ p` or `d ∤ q`.** The form
[AFK25]'s `d`-indexed applications need: `r ∈ ℚ² \ ℤ²` for `r = (p/d, q/d)` is the residue
condition `(p,q) ≢ (0,0) (mod d)`. -/
theorem not_isIntegralIndex_div (d : ℕ) (hd : 0 < d) (p q : ℤ)
    (hne : ¬((d : ℤ) ∣ p ∧ (d : ℤ) ∣ q)) : ¬ IsIntegralIndex ![(p : ℚ) / d, (q : ℚ) / d] := by
  have hdQ : ((d : ℚ)) ≠ 0 := by positivity
  intro h
  obtain ⟨m₀, hm₀⟩ := h 0
  obtain ⟨m₁, hm₁⟩ := h 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hm₀ hm₁
  rw [div_eq_iff hdQ] at hm₀ hm₁
  exact hne ⟨⟨m₀, by exact_mod_cast hm₀.trans (mul_comm _ _)⟩,
    ⟨m₁, by exact_mod_cast hm₁.trans (mul_comm _ _)⟩⟩

/-- **At a fixed point, the rescaled argument is the original one shifted by the lattice.**
`⟨⟨r,ξ⟩⟩/j_M(ξ) = ⟨⟨Mr,ξ⟩⟩` (`fracSymplecticFormRat_ratVecAction` at `M·ξ = ξ`), and
`(I - M)r` is an integer vector by `gammaSubgroup`, whose second component
is `n_QP(r,M)` and whose first is the integer `c` produced here:
```
⟨⟨r,ξ⟩⟩ / j_M(ξ) = ⟨⟨r,ξ⟩⟩ - n_QP(r,M)·ξ + c.
```
This is the step that makes `ℤ²`-periodicity work only at a fixed point: it is what turns the
outer `q`-Pochhammer's argument back into `⟨⟨r,ξ⟩⟩` modulo `ℤ`, so that the numerator's and
denominator's compensating factors are literally the same one. -/
theorem exists_fracSymplecticFormRat_div_fltDenominator {r : Fin 2 → ℚ} {M : SL(2, ℤ)}
    (hM : M ∈ gammaSubgroup r) {τ : ℝ}
    (hden : fltDenominator (M : Mat(2, ℤ)) τ ≠ 0)
    (hfix : flt (M : Mat(2, ℤ)) τ = τ) :
    ∃ c : ℤ, fracSymplecticFormRat r τ /
          fltDenominator (M : Mat(2, ℤ)) τ =
        fracSymplecticFormRat r τ -
          (nQPInt r (M : Mat(2, ℤ)) : ℝ) * τ + (c : ℝ) := by
  obtain ⟨n₀, hn₀⟩ := hM 0
  rw [Fin.sum_univ_two] at hn₀
  norm_num at hn₀
  refine ⟨-n₀, ?_⟩
  have hn₀R : ((M 0 0 : ℝ) - 1) * (r 0 : ℝ) + (M 0 1 : ℝ) * (r 1 : ℝ) = (n₀ : ℝ) := by
    exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) hn₀
  have hnR : (nQPInt r (M : Mat(2, ℤ)) : ℝ) =
      -(M 1 0 : ℝ) * (r 0 : ℝ) + (1 - (M 1 1 : ℝ)) * (r 1 : ℝ) := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) (nQPInt_cast_of_mem hM)
    simpa [nQP] using h
  have hdetR : (M 0 0 : ℝ) * (M 1 1 : ℝ) - (M 0 1 : ℝ) * (M 1 0 : ℝ) = 1 := by
    have h : (M : Mat(2, ℤ)).det = 1 := M.2
    rw [Matrix.det_fin_two] at h
    exact_mod_cast h
  have hden' : ((M 1 0 : ℝ) * τ + (M 1 1 : ℝ)) ≠ 0 := hden
  have hfixeq : (M 0 0 : ℝ) * τ + (M 0 1 : ℝ) = τ * ((M 1 0 : ℝ) * τ + (M 1 1 : ℝ)) := by
    have h : ((M 0 0 : ℝ) * τ + (M 0 1 : ℝ)) / ((M 1 0 : ℝ) * τ + (M 1 1 : ℝ)) = τ := hfix
    rwa [div_eq_iff hden'] at h
  have hJval : fltDenominator (M : Mat(2, ℤ)) τ =
      (M 1 0 : ℝ) * τ + (M 1 1 : ℝ) := rfl
  rw [div_eq_iff hden, hnR, hJval, fracSymplecticFormRat]
  push_cast
  linear_combination
    ((M 1 0 : ℝ) * (r 0 : ℝ) + (M 1 1 : ℝ) * (r 1 : ℝ)) * hfixeq -
      ((r 1 : ℝ) * τ - (r 0 : ℝ)) * hdetR - ((M 1 0 : ℝ) * τ + (M 1 1 : ℝ)) * hn₀R

/-- **The index moves by `n_QP(s,M)` under `r ↦ r + s`.** `n_QP` is affine-linear in `r`, so
`n_QP(r+s,M) = n_QP(r,M) + n_QP(s,M)`; both sides are genuinely integral by
`nQPInt_cast_of_mem` and `add_intVec_mem_gammaSubgroup`, so the identity transfers to `nQPInt`.
The point of the explicit right-hand side is the cancellation
`(a·M₁₁ - b·M₁₀) + n_QP(s,M) = s₁` at `a = s₁`, `b = -s₀`, which is what makes
`sfModularCocycleReal_add_intVec` close. -/
theorem nQPInt_add_intVec {r : Fin 2 → ℚ} {M : SL(2, ℤ)}
    (hM : M ∈ gammaSubgroup r) (s : Fin 2 → ℤ) :
    nQPInt (r + fun i => (s i : ℚ)) (M : Mat(2, ℤ)) =
      nQPInt r (M : Mat(2, ℤ)) +
        (-(M 1 0) * s 0 + (1 - M 1 1) * s 1) := by
  have hnq : nQP (r + fun i => (s i : ℚ)) (M : Mat(2, ℤ)) =
      nQP r (M : Mat(2, ℤ)) +
        ((-(M 1 0) * s 0 + (1 - M 1 1) * s 1 : ℤ) : ℚ) := by
    simp only [nQP, Pi.add_apply]
    push_cast
    ring
  have hcast : ((nQPInt (r + fun i => (s i : ℚ)) M : ℤ) : ℚ) =
      ((nQPInt r M + (-(M 1 0) * s 0 + (1 - M 1 1) * s 1) : ℤ) : ℚ) := by
    rw [nQPInt_cast_of_mem (add_intVec_mem_gammaSubgroup hM s), hnq, ← nQPInt_cast_of_mem hM]
    push_cast
    ring
  exact_mod_cast hcast

/-- At a fixed point, `⟨⟨r,τ⟩⟩/j_M(τ) + n_QP(r,M)τ` agrees with
`⟨⟨r,τ⟩⟩` modulo `ℤ`. This is
`exists_fracSymplecticFormRat_div_fltDenominator` with the period term moved across
the equality, as consumed by the cocycle reflection law. -/
lemma div_fltDenominator_add_nQPInt_mul {r : Fin 2 → ℚ} {M : SL(2, ℤ)} {τ : ℝ}
    (hM : M ∈ gammaSubgroup r)
    (hfix : flt (M : Mat(2, ℤ)) τ = τ)
    (hJ : fltDenominator (M : Mat(2, ℤ)) τ ≠ 0) :
    ∃ m : ℤ,
      fracSymplecticFormRat r τ /
            fltDenominator (M : Mat(2, ℤ)) τ +
          (nQPInt r (M : Mat(2, ℤ)) : ℝ) * τ =
        fracSymplecticFormRat r τ + (m : ℝ) := by
  obtain ⟨m, hm⟩ := exists_fracSymplecticFormRat_div_fltDenominator hM hJ hfix
  exact ⟨m, by linarith⟩

/-! ### Integral matrix actions on characteristics

The rational-index action is a group action, and it preserves integrality in both directions
for determinant `±1`, since both a matrix and its inverse have integer entries. This carries
the hypothesis `r ∉ ℤ²` of [AFK25, Lemma 2.14, `lm:shinperiodicity`] along an arbitrary chain
of matrices. Applying the action to `Ar-r ∈ ℤ²` also transports congruence-subgroup
membership under conjugation. -/

/-- The identity matrix acts trivially on characteristics. -/
@[simp] lemma ratVecAction_one (r : Fin 2 → ℚ) :
    ratVecAction (1 : Mat(2, ℤ)) r = r := by
  ext i
  simp only [ratVecAction, Matrix.map_one, Int.cast_zero, Int.cast_one, Matrix.one_mulVec]

/-- The rational-index action is a left action: `(MN)r = M(Nr)`. -/
lemma ratVecAction_mul (M N : Mat(2, ℤ)) (r : Fin 2 → ℚ) :
    ratVecAction (M * N) r = ratVecAction M (ratVecAction N r) := by
  have hmap : (M * N).map (Int.cast : ℤ → ℚ) =
      M.map (Int.cast : ℤ → ℚ) * N.map (Int.cast : ℤ → ℚ) := by
    simpa using Matrix.map_mul (L := M) (M := N) (f := Int.castRingHom ℚ)
  simp only [ratVecAction, hmap, Matrix.mulVec_mulVec]

/-- `M(M⁻¹r) = r` for `M ∈ SL₂(ℤ)`: `ratVecAction_mul` at `MM⁻¹ = I`. -/
@[simp] lemma ratVecAction_ratVecAction_inv (M : SL(2, ℤ)) (r : Fin 2 → ℚ) :
    ratVecAction (M : Mat(2, ℤ))
      (ratVecAction ((M⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) r) = r := by
  rw [← ratVecAction_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, ratVecAction_one]

/-- `M⁻¹(Mr) = r` for `M ∈ SL₂(ℤ)`: `ratVecAction_mul` at `M⁻¹M = I`. -/
@[simp] lemma ratVecAction_inv_ratVecAction (M : SL(2, ℤ)) (r : Fin 2 → ℚ) :
    ratVecAction ((M⁻¹ : SL(2, ℤ)) : Mat(2, ℤ))
      (ratVecAction (M : Mat(2, ℤ)) r) = r := by
  rw [← ratVecAction_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, ratVecAction_one]

/-- The rational-index action is linear, so it commutes with differences. Used to transport a
congruence `v ≡ w (mod ℤ²)` along the action. -/
lemma ratVecAction_sub (M : Mat(2, ℤ)) (v w : Fin 2 → ℚ) :
    ratVecAction M (v - w) = ratVecAction M v - ratVecAction M w := by
  simp only [ratVecAction, Matrix.mulVec_sub]

/-- The rational-index action commutes with the reflection `r ↦ -r`, by linearity. Used to
transport the reflected characteristic `-r` along a conjugation. -/
lemma ratVecAction_neg (M : Mat(2, ℤ)) (r : Fin 2 → ℚ) :
    ratVecAction M (-r) = -ratVecAction M r := by
  simp only [ratVecAction, Matrix.mulVec_neg]

/-- **Integrality is invariant under negation**: `-r ∈ ℤ²` exactly when `r ∈ ℤ²`. -/
lemma isIntegralIndex_neg_iff (r : Fin 2 → ℚ) : IsIntegralIndex (-r) ↔ IsIntegralIndex r := by
  have key : ∀ s : Fin 2 → ℚ, IsIntegralIndex s → IsIntegralIndex (-s) := by
    intro s hs i
    obtain ⟨m, hm⟩ := hs i
    exact ⟨-m, by simp [hm]⟩
  exact ⟨fun h => by simpa using key _ h, key r⟩

/-- **Integrality is closed under addition**: `r, s ∈ ℤ²` give `r + s ∈ ℤ²`. -/
lemma isIntegralIndex_add {r s : Fin 2 → ℚ} (hr : IsIntegralIndex r) (hs : IsIntegralIndex s) :
    IsIntegralIndex (r + s) := by
  intro i
  obtain ⟨m, hm⟩ := hr i
  obtain ⟨n, hn⟩ := hs i
  exact ⟨m + n, by simp [hm, hn]⟩

/-- **Integrality is closed under subtraction**: `r, s ∈ ℤ²` give `r - s ∈ ℤ²`. -/
lemma isIntegralIndex_sub {r s : Fin 2 → ℚ} (hr : IsIntegralIndex r) (hs : IsIntegralIndex s) :
    IsIntegralIndex (r - s) := by
  rw [sub_eq_add_neg]
  exact isIntegralIndex_add hr ((isIntegralIndex_neg_iff s).mpr hs)

/-- Integrality of characteristics is unchanged by an integral difference. This glue lemma is
used by `SICs.Principal.Dilogarithm.Values`. -/
theorem isIntegralIndex_iff_of_isIntegralIndex_sub {r r' : Fin 2 → ℚ}
    (h : IsIntegralIndex (r' - r)) : IsIntegralIndex r' ↔ IsIntegralIndex r := by
  constructor
  · intro hr'
    have heq : r = r' - (r' - r) := by abel
    rw [heq]
    exact isIntegralIndex_sub hr' h
  · intro hr
    have heq : r' = (r' - r) + r := by abel
    rw [heq]
    exact isIntegralIndex_add h hr

/-- **`Γ_r` depends on `r` only modulo `ℤ²`, membership form**: if `r' ≡ r (mod ℤ²)` then
`M ∈ Γ_r` gives `M ∈ Γ_{r'}`; `add_intVec_mem_gammaSubgroup` with the integer vector
`r' - r`. -/
lemma mem_gammaSubgroup_of_isIntegralIndex_sub {r r' : Fin 2 → ℚ} (h : IsIntegralIndex (r' - r))
    {M : SL(2, ℤ)} (hM : M ∈ gammaSubgroup r) : M ∈ gammaSubgroup r' := by
  let s : Fin 2 → ℤ := fun i => Classical.choose (h i)
  have hs (i : Fin 2) : (r' - r) i = (s i : ℚ) := Classical.choose_spec (h i)
  have hr' : r' = r + fun i => (s i : ℚ) := by
    funext i
    have hi := hs i
    simp only [Pi.sub_apply, Pi.add_apply] at hi ⊢
    linarith
  rw [hr']
  exact add_intVec_mem_gammaSubgroup hM s

/-- **`Γ_r` depends on `r` only modulo `ℤ²`**: `Γ_{r'} = Γ_r` when `r' ≡ r (mod ℤ²)`, from
`mem_gammaSubgroup_of_isIntegralIndex_sub` in both directions. -/
lemma gammaSubgroup_eq_of_isIntegralIndex_sub {r r' : Fin 2 → ℚ}
    (h : IsIntegralIndex (r' - r)) : gammaSubgroup r' = gammaSubgroup r := by
  have h' : IsIntegralIndex (r - r') := by
    have := (isIntegralIndex_neg_iff (r' - r)).mpr h
    rwa [neg_sub] at this
  ext M
  exact ⟨mem_gammaSubgroup_of_isIntegralIndex_sub h',
    mem_gammaSubgroup_of_isIntegralIndex_sub h⟩

/-- Every unimodular matrix belongs to `Γ_r` when `r ∈ ℤ²`; used for the zero-class
boundary value in `prod_sfModularCocycleReal'_orbits_preimage_zero`. -/
lemma mem_gammaSubgroup_of_integral {r : Fin 2 → ℚ} (hr : IsIntegralIndex r)
    (M : SL(2, ℤ)) : M ∈ gammaSubgroup r := by
  rw [gammaSubgroup_eq_of_isIntegralIndex_sub (r := 0) (by simpa using hr)]
  exact fun _ => ⟨0, by simp⟩

/-- An integral characteristic stays integral under the action of an integer matrix. -/
lemma isIntegralIndex_ratVecAction {r : Fin 2 → ℚ} (M : Mat(2, ℤ))
    (h : IsIntegralIndex r) : IsIntegralIndex (ratVecAction M r) := by
  obtain ⟨m₀, hm₀⟩ := h 0
  obtain ⟨m₁, hm₁⟩ := h 1
  refine isIntegralIndex_of_coords ⟨M 0 0 * m₀ + M 0 1 * m₁, ?_⟩ ⟨M 1 0 * m₀ + M 1 1 * m₁, ?_⟩ <;>
    simp only [ratVecAction, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply,
      hm₀, hm₁] <;>
    push_cast <;> ring

/-- **Integrality is invariant under the `SL₂(ℤ)` action**: `Mr ∈ ℤ²` exactly when `r ∈ ℤ²`,
because `r = M⁻¹(Mr)` and `M⁻¹` is again integral. -/
lemma isIntegralIndex_ratVecAction_iff {r : Fin 2 → ℚ} (M : SL(2, ℤ)) :
    IsIntegralIndex (ratVecAction (M : Mat(2, ℤ)) r) ↔ IsIntegralIndex r := by
  refine ⟨fun h => ?_, isIntegralIndex_ratVecAction _⟩
  have hback := isIntegralIndex_ratVecAction ((M⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) h
  rwa [← ratVecAction_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, ratVecAction_one] at hback

/-- **A matrix of determinant `±1` preserves nonintegrality of characteristics**: its adjugate is
an integer matrix with `adj(M)·M = det M·I` (`Matrix.adjugate_mul`), so `M r ∈ ℤ²` forces
`r = (det M)⁻¹ adj(M)(Mr) ∈ ℤ²`. The `SL(2, ℤ)` case is `isIntegralIndex_ratVecAction_iff`. -/
theorem isIntegralIndex_ratVecAction_iff_of_det {M : Mat(2, ℤ)}
    (hM : M.det = 1 ∨ M.det = -1) (r : Fin 2 → ℚ) :
    IsIntegralIndex (ratVecAction M r) ↔ IsIntegralIndex r := by
  refine ⟨?_, isIntegralIndex_ratVecAction M⟩
  intro h
  have hback := isIntegralIndex_ratVecAction M.adjugate h
  rw [← ratVecAction_mul, Matrix.adjugate_mul] at hback
  rcases hM with hdet | hdet
  · rw [hdet, one_smul, ratVecAction_one] at hback
    exact hback
  · rw [hdet, neg_one_smul] at hback
    change IsIntegralIndex (ratVecAction (-(1 : Mat(2, ℤ))) r) at hback
    have hneg : ratVecAction (-(1 : Mat(2, ℤ))) r = -r := by
      ext i
      fin_cases i <;>
        simp [ratVecAction, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [hneg] at hback
    exact (isIntegralIndex_neg_iff r).mp hback

/-- **Integrality of `Mr - r` gives membership in `Γ_r`** for a determinant-one matrix: the
converse of `ratVecAction_sub_intVec_of_mem_gammaSubgroup`, the coordinates of `Mr - r` being
the witnesses in the definition of `Γ_r`. -/
lemma mem_gammaSubgroup_of_isIntegralIndex {r : Fin 2 → ℚ} {M : SL(2, ℤ)}
    (hM : IsIntegralIndex (ratVecAction (M : Mat(2, ℤ)) r - r)) :
    M ∈ gammaSubgroup r := by
  intro i
  obtain ⟨n, hn⟩ := hM i
  refine ⟨n, ?_⟩
  rw [Fin.sum_univ_two]
  fin_cases i <;>
    simp only [ratVecAction, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.map_apply, Pi.sub_apply] at hn ⊢ <;>
    norm_num at hn ⊢ <;>
    linarith

/-- **`Γ_r` is transported by a conjugation**: if `A ∈ Γ_r` and `A'R = RA` for an integer matrix
`R`, then `A' ∈ Γ_{Rr}`, since `A'(Rr) - Rr = R(Ar - r) ∈ Rℤ² ⊆ ℤ²`
(`ratVecAction_mul`, `ratVecAction_sub_intVec_of_mem_gammaSubgroup`). This is the membership
`RAR⁻¹ ∈ Γ_{Rr}` implicit in [72, Kopp (2024), Theorem 4.37, `thm:shinconj`]. -/
theorem mem_gammaSubgroup_ratVecAction_of_mul_eq {r : Fin 2 → ℚ} {A A' : SL(2, ℤ)}
    {R : Mat(2, ℤ)} (hA : A ∈ gammaSubgroup r)
    (hconj : (A' : Mat(2, ℤ)) * R = R * (A : Mat(2, ℤ))) :
    A' ∈ gammaSubgroup (ratVecAction R r) := by
  apply mem_gammaSubgroup_of_isIntegralIndex
  have hint : IsIntegralIndex
      (ratVecAction (A : Mat(2, ℤ)) r - r) :=
    ratVecAction_sub_intVec_of_mem_gammaSubgroup hA
  have himage := isIntegralIndex_ratVecAction R hint
  have heq : ratVecAction (A' : Mat(2, ℤ)) (ratVecAction R r) -
      ratVecAction R r = ratVecAction R
        (ratVecAction (A : Mat(2, ℤ)) r - r) := by
    rw [ratVecAction_sub, ← ratVecAction_mul, ← ratVecAction_mul, hconj]
  rwa [heq]

/-- **`Ms ≡ r (mod ℤ²)` in coordinates**: `Ms - r ∈ ℤ²` says that each coordinate
`∑ⱼ Mᵢⱼ sⱼ - rᵢ` is an integer, the form in which `sfUpperTriangularIndex_mem_preimage` states
the characteristics over `r`. -/
lemma isIntegralIndex_ratVecAction_sub_iff {M : Mat(2, ℤ)} {r s : Fin 2 → ℚ} :
    IsIntegralIndex (ratVecAction M s - r) ↔
      ∀ i, ∃ t : ℤ, (∑ j, (M i j : ℚ) * s j) - r i = (t : ℚ) := by
  simp only [IsIntegralIndex, ratVecAction, Matrix.mulVec, dotProduct, Matrix.map_apply,
    Pi.sub_apply]

/-! ### Matrices congruent to the identity

Membership in the principal congruence subgroup `Γ(N)` is converted to the integral equation
`A = 1 + N • X`.  This elementary normal form is what the inclusion `Γ(N) ⊆ Γ_s` below uses. -/

/-- A matrix of `Γ(N)` is `1 + N · A₁` for an integral matrix `A₁`. -/
lemma exists_eq_one_add_smul_of_mem_Gamma {N : ℕ} {A : SL(2, ℤ)}
    (hA : A ∈ CongruenceSubgroup.Gamma N) :
    ∃ A₁ : Mat(2, ℤ),
      (A : Mat(2, ℤ)) = 1 + (N : ℤ) • A₁ := by
  have hdvd : ∀ i j, (N : ℤ) ∣ ((A : Mat(2, ℤ)) i j -
      (1 : Mat(2, ℤ)) i j) := by
    have h := CongruenceSubgroup.Gamma_mem.mp hA
    intro i j
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    fin_cases i <;> fin_cases j <;>
      simp [h.1, h.2.1, h.2.2.1, h.2.2.2]
  refine ⟨Matrix.of fun i j =>
    ((A : Mat(2, ℤ)) i j - (1 : Mat(2, ℤ)) i j) / (N : ℤ), ?_⟩
  ext i j
  have := Int.mul_ediv_cancel' (hdvd i j)
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  omega

/-! ### Positive powers landing in a congruence subgroup

Reduction modulo `M` has finite image, so the order of the reduced matrix gives a positive power
lying in the kernel `Γ(M)`. -/

/-- Every element of `SL₂(ℤ)` has a positive power in `Γ(M)`, because `SL₂(ℤ/M)` is finite. -/
theorem exists_pow_mem_Gamma (M : ℕ) [NeZero M] (A : SL(2, ℤ)) :
    ∃ n : ℕ, 0 < n ∧ A ^ n ∈ CongruenceSubgroup.Gamma M := by
  classical
  set φ := Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod M)) with hφ
  refine ⟨orderOf (φ A), orderOf_pos _, ?_⟩
  rw [CongruenceSubgroup.Gamma_mem', ← hφ, map_pow, pow_orderOf_eq_one]

/-! ### `Γ(M)` sits inside the subgroups `Γ_s`

When `M s` is integral, the equation `C = 1 + M X` makes `(C - 1)s` integral.  Thus the principal
congruence subgroup controls every rational-index subgroup whose denominator divides `M`. -/

/-- If `M s ∈ ℤ²`, every matrix in the principal congruence subgroup `Γ(M)` also lies in
`gammaSubgroup s = Γ_s`.

This is the remark after [AFK25, Definition 1.17, `dfn:gammarDef`] that `Γ(M) ⊆ Γ_r` when
`Mr ∈ ℤ²`. -/
lemma mem_gammaSubgroup_of_mem_Gamma {M : ℕ} {C : SL(2, ℤ)}
    (hC : C ∈ CongruenceSubgroup.Gamma M) {s : Fin 2 → ℚ}
    (hs : ∀ i, ∃ t : ℤ, (M : ℚ) * s i = (t : ℚ)) :
    C ∈ gammaSubgroup s := by
  obtain ⟨C₁, hC₁⟩ := exists_eq_one_add_smul_of_mem_Gamma hC
  obtain ⟨t₀, ht₀⟩ := hs 0
  obtain ⟨t₁, ht₁⟩ := hs 1
  intro i
  refine ⟨C₁ i 0 * t₀ + C₁ i 1 * t₁, ?_⟩
  have hentry : ∀ j, ((C : Mat(2, ℤ)) i j : ℚ) -
      (if i = j then 1 else 0) = (M : ℚ) * (C₁ i j : ℚ) := by
    intro j
    have := congrArg (fun N : Mat(2, ℤ) => N i j) hC₁
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply] at this
    rw [this]
    push_cast
    split <;> ring
  rw [Fin.sum_univ_two, hentry 0, hentry 1]
  push_cast
  rw [show (M : ℚ) * (C₁ i 0 : ℚ) * s 0 = (C₁ i 0 : ℚ) * ((M : ℚ) * s 0) by ring,
    show (M : ℚ) * (C₁ i 1 : ℚ) * s 1 = (C₁ i 1 : ℚ) * ((M : ℚ) * s 1) by ring, ht₀, ht₁]

/-! ### Powers in `Γ_r` and the pairing at a fixed point

`Γ_r` is a group: closed under products, hence under natural powers. At a fixed point `τ` of
`M ∈ SL₂(ℤ)` the pairing transforms by the Jacobi denominator alone,
`⟨⟨Mu,τ⟩⟩ = ⟨⟨u,τ⟩⟩/j_M(τ)`. -/

/-- **`Γ_r` is closed under products**, by the subgroup multiplication API. -/
lemma mul_mem_gammaSubgroup {r : Fin 2 → ℚ} {M N : SL(2, ℤ)}
    (hM : M ∈ gammaSubgroup r) (hN : N ∈ gammaSubgroup r) : M * N ∈ gammaSubgroup r :=
  (gammaSubgroup r).mul_mem hM hN

/-- **`Γ_r` is closed under natural powers**, by the bundled subgroup power API. -/
lemma pow_mem_gammaSubgroup {r : Fin 2 → ℚ} {M : SL(2, ℤ)}
    (hM : M ∈ gammaSubgroup r) (k : ℕ) : M ^ k ∈ gammaSubgroup r :=
  (gammaSubgroup r).pow_mem hM k

/-- **The pairing at a fixed point scales by the Jacobi denominator**: if `M ∈ SL₂(ℤ)` fixes
`τ` with `j_M(τ) ≠ 0`, then `⟨⟨Mu, τ⟩⟩ = ⟨⟨u, τ⟩⟩ / j_M(τ)`. This is
`fracSymplecticFormRat_ratVecAction` with `M·τ` replaced by `τ` and `det M = 1`. -/
theorem fracSymplecticFormRat_ratVecAction_of_flt_eq_self {M : SL(2, ℤ)} {τ : ℝ}
    (hden : fltDenominator (M : Mat(2, ℤ)) τ ≠ 0)
    (hfix : flt (M : Mat(2, ℤ)) τ = τ) (u : Fin 2 → ℚ) :
    fracSymplecticFormRat (ratVecAction (M : Mat(2, ℤ)) u) τ =
      fracSymplecticFormRat u τ / fltDenominator (M : Mat(2, ℤ)) τ := by
  have h := fracSymplecticFormRat_ratVecAction
    (M : Mat(2, ℤ)) u τ hden
  simpa only [hfix, M.2, Int.cast_one, one_mul] using h

end SIC
