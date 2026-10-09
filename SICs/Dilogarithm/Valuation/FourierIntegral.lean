/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Dilogarithm.Valuation.PrimaryCoordinates
import SICs.FieldTheory.PrimeFieldMoments
import SICs.Valuation.CosetMoments
import SICs.Valuation.GaussianBinomial
import SICs.Source

/-!
# Fourier-integral functions on a metric group with one or two `p`-coordinates

For a cyclic primary part, an integral function with integral normalized Fourier transform is
either zero or nonzero at more than half the points of each `p`-torsion coset. If it and its
reciprocal are Fourier-integral units, it is constant on such a coset modulo the maximal ideal.
For a primary part with two coordinates, a separated reduction is constant in one coordinate.

This module proves [RW26b, Radchenko, Wheeler (2026b), Section 4, Lemma 1](i)–(iii), with a
valuation `v : L → ℝ≥0` above `p` (`v(p) < 1`) in place of a valuation of `ℚ̄` normalized by
`v(p) = 1`. For the cyclic case, the source's hypothesis `H = ℤ/p^s` is stated as `|G[p]| = p`.
For two coordinates, an injective map from `(ℤ/p^s)^2` with image containing all `p`-power
torsion specifies `H`. The group and pairing coordinates and coset Fourier identity come from
`SICs.Dilogarithm.Valuation.PrimaryCoordinates`.

## The argument

*Fourier valuation.* The bicharacter and Gaussian are roots of unity, hence valuation units.
The coset identity from `PrimaryCoordinates` and the prime-to-`p` index of the primary part
bound the square of the valuation of its Fourier sum by `v(p)^{sd}`. Coordinate frequencies
transfer this bound to `(ZMod (p^s))^d`, for `d = 1, 2`.

*Residues.* The Gaussian binomial estimate and
`valuation_sum_coset_mul_prod_pow_lt_one` give (14): on every coset
`b + H[p] = {b + p^{s-1}u}`, the residues of `f` have vanishing moments of total degree
less than `d(p-1)/2`. In characteristic `p`, the one-variable moment results give (i) and (ii).
For (iii), the basis `a,b` of `H[p]` differs from the standard basis by an invertible linear
map over `𝔽_p`. Expanding powers of its coordinate forms preserves the degree bound and hence
the vanishing moments. Separation writes the residue as `A(u₁)B(u₂)`; the moments of `f` and
`1/f` force one of `A,B` to be constant.
-/

open scoped NNReal

namespace SIC

variable {G : Type*} [AddCommGroup G] [Fintype G] {L : Type*} [Field L]

/-! ### Changes of torsion coordinates and residue moments

The chosen basis of `G[p]` changes the moment coordinates by an invertible linear map. -/
/-- A basis `a,b` of `G[p]` differs from standard coordinates by an additive equivalence. Used
by Lemma 1(iii). -/
private theorem exists_torsion_basis_change {G : Type*} [AddCommGroup G]
    {p : ℕ} [Fact p.Prime]
    (τ : (Fin 2 → ZMod p) ≃+ (nsmulAddMonoidHom (α := G) p).ker)
    (a b : G) (ha : p • a = 0) (hb : p • b = 0)
    (hab : ∀ i j : ZMod p, i.val • a + j.val • b = 0 → i = 0 ∧ j = 0) :
    ∃ B : (Fin 2 → ZMod p) ≃+ (Fin 2 → ZMod p),
      ∀ u, ((τ (B u) : (nsmulAddMonoidHom (α := G) p).ker) : G) =
        (u 0).val • a + (u 1).val • b := by
  classical
  let T := (nsmulAddMonoidHom (α := G) p).ker
  let aa : T := ⟨a, by change p • a = 0; exact ha⟩
  let bb : T := ⟨b, by change p • b = 0; exact hb⟩
  let ua := τ.symm aa
  let ub := τ.symm bb
  let B : (Fin 2 → ZMod p) →+ (Fin 2 → ZMod p) := {
    toFun u := (u 0) • ua + (u 1) • ub
    map_zero' := by simp
    map_add' := by
      intro u w
      simp only [Pi.add_apply, add_smul]
      abel }
  have hsmul (z : ZMod p) (x : Fin 2 → ZMod p) :
      ((τ (z • x) : T) : G) = z.val • ((τ x : T) : G) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val z]
    rw [Nat.cast_smul_eq_nsmul, map_nsmul]
    rfl
  have hτ (u : Fin 2 → ZMod p) :
      ((τ (B u) : T) : G) = (u 0).val • a + (u 1).val • b := by
    change ((τ ((u 0) • ua + (u 1) • ub) : T) : G) = _
    rw [map_add, AddSubgroup.coe_add, hsmul, hsmul]
    simp [ua, ub, aa, bb]
  have hker (u : Fin 2 → ZMod p) (hu : B u = 0) : u = 0 := by
    have hc : (u 0).val • a + (u 1).val • b = 0 := by
      rw [← hτ u, hu]
      simp
    obtain ⟨h0, h1⟩ := hab (u 0) (u 1) hc
    ext i
    fin_cases i <;> simp [h0, h1]
  have hBi : Function.Injective B := by
    intro u w h
    apply sub_eq_zero.mp
    apply hker
    rw [map_sub, h, sub_self]
  let BE := AddEquiv.ofBijective B
    ((Fintype.bijective_iff_injective_and_card B).mpr ⟨hBi, rfl⟩)
  exact ⟨BE, hτ⟩

/-- The two-binomial expansion used by `sum_linear_pow_mul_eq_zero`. -/
private theorem two_linear_pow_mul_expansion {k : Type*} [CommRing k]
    (α β γ δ a x y : k) (r₁ r₂ : ℕ) :
    a * (α * x + β * y) ^ r₁ * (γ * x + δ * y) ^ r₂ =
      ∑ i ∈ Finset.range (r₁ + 1), ∑ j ∈ Finset.range (r₂ + 1),
        (α ^ i * β ^ (r₁ - i) * γ ^ j * δ ^ (r₂ - j) *
          (r₁.choose i : k) * (r₂.choose j : k)) *
          (a * x ^ (i + j) * y ^ ((r₁ - i) + (r₂ - j))) := by
  rw [add_pow (α * x) (β * y) r₁,
    add_pow (γ * x) (δ * y) r₂]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_pow, mul_pow, mul_pow, mul_pow, pow_add, pow_add]
  ring

open scoped Classical in
/-- Vanishing moments of total degree below `p-1` also vanish after substituting two linear
forms. Used by `moments_of_addEquiv`. -/
private theorem sum_linear_pow_mul_eq_zero {p : ℕ} [Fact p.Prime]
    {k : Type*} [Field k] [CharP k p] (F : (Fin 2 → ZMod p) → k)
    (hmom : ∀ m n : ℕ, m + n < p - 1 →
      ∑ w, F w * ((w 0).val : k) ^ m * ((w 1).val : k) ^ n = 0)
    (α β γ δ : k) (r₁ r₂ : ℕ) (hr : r₁ + r₂ < p - 1) :
    ∑ w, F w * (α * ((w 0).val : k) + β * ((w 1).val : k)) ^ r₁ *
      (γ * ((w 0).val : k) + δ * ((w 1).val : k)) ^ r₂ = 0 := by
  classical
  let X (w : Fin 2 → ZMod p) : k := ((w 0).val : k)
  let Y (w : Fin 2 → ZMod p) : k := ((w 1).val : k)
  let C (i j : ℕ) : k := α ^ i * β ^ (r₁ - i) * γ ^ j * δ ^ (r₂ - j) *
    (r₁.choose i : k) * (r₂.choose j : k)
  have hpoint (w : Fin 2 → ZMod p) :
      F w * (α * X w + β * Y w) ^ r₁ * (γ * X w + δ * Y w) ^ r₂ =
        ∑ i ∈ Finset.range (r₁ + 1), ∑ j ∈ Finset.range (r₂ + 1),
          C i j * (F w * X w ^ (i + j) * Y w ^ ((r₁ - i) + (r₂ - j))) := by
    exact two_linear_pow_mul_expansion α β γ δ (F w) (X w) (Y w) r₁ r₂
  calc
    _ = ∑ w, ∑ i ∈ Finset.range (r₁ + 1), ∑ j ∈ Finset.range (r₂ + 1),
          C i j * (F w * X w ^ (i + j) * Y w ^ ((r₁ - i) + (r₂ - j))) := by
            apply Finset.sum_congr rfl
            intro w _
            exact hpoint w
    _ = ∑ i ∈ Finset.range (r₁ + 1), ∑ j ∈ Finset.range (r₂ + 1),
          C i j * ∑ w, F w * X w ^ (i + j) * Y w ^ ((r₁ - i) + (r₂ - j)) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      apply Finset.sum_eq_zero
      intro j hj
      have hir : i ≤ r₁ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hjr : j ≤ r₂ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have heq : (i + j) + ((r₁ - i) + (r₂ - j)) = r₁ + r₂ := by omega
      rw [hmom _ _ (by omega)]
      ring

/-- Each coordinate of an additive equivalence of `(ZMod p)^2` is a linear form in the two
standard coordinates after casting to characteristic `p`. Used by `moments_of_addEquiv`. -/
private theorem addEquiv_two_coord_cast {p : ℕ} [Fact p.Prime]
    {k : Type*} [Field k] [CharP k p]
    (T : (Fin 2 → ZMod p) ≃+ (Fin 2 → ZMod p))
    (w : Fin 2 → ZMod p) (i : Fin 2) :
    ((T w i).val : k) =
      ((T (Pi.single 0 1) i).val : k) * ((w 0).val : k) +
      ((T (Pi.single 1 1) i).val : k) * ((w 1).val : k) := by
  classical
  let _ : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hdec : w = (w 0).val • (Pi.single 0 (1 : ZMod p) : Fin 2 → ZMod p) +
      (w 1).val • (Pi.single 1 (1 : ZMod p) : Fin 2 → ZMod p) := by
    simpa only [Fin.sum_univ_two] using pi_nat_decompose w
  have hcoord : (T w) i = (w 0) * (T (Pi.single 0 1) i) +
      (w 1) * (T (Pi.single 1 1) i) := by
    conv_lhs => rw [hdec]
    rw [map_add, map_nsmul, map_nsmul]
    simp only [Pi.add_apply]
    simp [nsmul_eq_mul]
  have hh := congrArg (fun z : ZMod p => (ZMod.cast z : k)) hcoord
  rw [ZMod.cast_add (dvd_refl p), ZMod.cast_mul (dvd_refl p),
    ZMod.cast_mul (dvd_refl p)] at hh
  have hh' : ((T w i).val : k) = ((w 0).val : k) * ((T (Pi.single 0 1) i).val : k) +
      ((w 1).val : k) * ((T (Pi.single 1 1) i).val : k) := by
    simpa only [ZMod.cast_eq_val] using hh
  calc
    _ = _ := hh'
    _ = _ := by ring

open scoped Classical in
/-- Two-variable moments of total degree below `p-1` vanish after an invertible change of
coordinates. Used by Lemma 1(iii). -/
private theorem moments_of_addEquiv {p : ℕ} [Fact p.Prime]
    {k : Type*} [Field k] [CharP k p] (F : (Fin 2 → ZMod p) → k)
    (hmom : ∀ m n : ℕ, m + n < p - 1 →
      ∑ w, F w * ((w 0).val : k) ^ m * ((w 1).val : k) ^ n = 0)
    (B : (Fin 2 → ZMod p) ≃+ (Fin 2 → ZMod p))
    (r₁ r₂ : ℕ) (hr : r₁ + r₂ < p - 1) :
    ∑ u : Fin 2 → ZMod p, F (B u) * ((u 0).val : k) ^ r₁ *
      ((u 1).val : k) ^ r₂ = 0 := by
  classical
  let α : k := ((B.symm (Pi.single 0 1) 0).val : k)
  let β : k := ((B.symm (Pi.single 1 1) 0).val : k)
  let γ : k := ((B.symm (Pi.single 0 1) 1).val : k)
  let δ : k := ((B.symm (Pi.single 1 1) 1).val : k)
  have hh := sum_linear_pow_mul_eq_zero F hmom α β γ δ r₁ r₂ hr
  have hsum : (∑ u : Fin 2 → ZMod p, F (B u) * ((u 0).val : k) ^ r₁ *
      ((u 1).val : k) ^ r₂) =
      ∑ w : Fin 2 → ZMod p, F w * ((B.symm w 0).val : k) ^ r₁ *
        ((B.symm w 1).val : k) ^ r₂ := by
    apply Fintype.sum_equiv B.toEquiv
    intro u
    simp
  rw [hsum]
  simpa only [α, β, γ, δ, ← addEquiv_two_coord_cast B.symm] using hh

open scoped Classical in
/-- The moment of a product `A(u₁)B(u₂)` factors into one-variable moments. Used by Lemma 1(iii). -/
private theorem sum_two_separable {p : ℕ} [Fact p.Prime]
    {k : Type*} [CommSemiring k] (A B : ZMod p → k) (r₁ r₂ : ℕ) :
    (∑ u : Fin 2 → ZMod p,
      (A (u 0) * B (u 1)) * ((u 0).val : k) ^ r₁ * ((u 1).val : k) ^ r₂) =
      (∑ i : ZMod p, A i * (i.val : k) ^ r₁) *
        (∑ j : ZMod p, B j * (j.val : k) ^ r₂) := by
  classical
  calc
    _ = ∑ z : ZMod p × ZMod p,
        (A z.1 * B z.2) * (z.1.val : k) ^ r₁ * (z.2.val : k) ^ r₂ := by
          apply Fintype.sum_equiv (finTwoArrowEquiv (ZMod p))
          intro u
          rfl
    _ = ∑ i : ZMod p, ∑ j : ZMod p,
        (A i * B j) * (i.val : k) ^ r₁ * (j.val : k) ^ r₂ :=
          Fintype.sum_prod_type _
    _ = _ := by
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-! ### Model and residue moment helpers

The Gaussian binomial estimate yields the same coset moments in one or two coordinates. -/

open scoped Classical in
/-- Apply the Gaussian binomial and coset-moment bounds to a model with at most two coordinates.
Used by Lemma 1. -/
private theorem model_coset_moments {L : Type*} [Field L] {p s : ℕ} [Fact p.Prime]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : Valuation L ℝ≥0)
    (hvp : v (p : L) < 1) (hs : 1 ≤ s) (hd : Fintype.card ι ≤ 2)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ s))
    (F : (ι → ZMod (p ^ s)) → L) (hF : ∀ x, v (F x) ≤ 1)
    (hS : ∀ a : ι → ZMod (p ^ s),
      v (∑ x, F x * ζ ^ (∑ i, (a i).val * (x i).val)) ^ 2 ≤
        v (p : L) ^ (s * Fintype.card ι))
    (b : ι → ZMod (p ^ s)) (r : ι → ℕ)
    (hr : 2 * ∑ i, r i < Fintype.card ι * (p - 1)) :
    v (∑ u : ι → ZMod p, F (b + fun i =>
       ((p ^ (s - 1) * (u i).val : ℕ) : ZMod (p ^ s))) *
      ∏ i, (((u i).val : ℕ) : L) ^ (r i)) < 1 := by
  have hchoose (j : ι → ℕ) (hj : 2 * ∑ i, j i < Fintype.card ι * (p ^ s - 1)) :
      v (∑ x, F x * ∏ i, (((x i).val.choose (j i) : ℕ) : L)) < 1 :=
    valuation_sum_mul_prod_choose_lt_one v hvp hd hζ F hF hS j hj
  exact valuation_sum_coset_mul_prod_pow_lt_one v hvp hs hd F hF hchoose b r hr

open scoped Classical in
/-- A two-coordinate valuation moment below one vanishes in the residue field. Used by Lemma
1(iii). -/
private theorem residue_prod_moment_eq_zero {L : Type*} [Field L]
    {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Valuation L ℝ≥0) (F : (ι → ZMod p) → L)
    (hF : ∀ u, v (F u) ≤ 1) (r : ι → ℕ)
    (hmom : v (∑ u, F u * ∏ i, ((u i).val : L) ^ (r i)) < 1) :
    ∑ u : ι → ZMod p,
      (IsLocalRing.residue v.valuationSubring)
        (⟨F u, hF u⟩ : v.valuationSubring) *
        ∏ i, ((u i).val : IsLocalRing.ResidueField v.valuationSubring) ^ (r i) = 0 := by
  classical
  let R := v.valuationSubring
  let S : R := ∑ u : ι → ZMod p, (⟨F u, hF u⟩ : R) *
    ∏ i, ((u i).val : R) ^ (r i)
  have hcoe : (S : L) = ∑ u : ι → ZMod p, F u *
      ∏ i, ((u i).val : L) ^ (r i) := by
    change R.subtype S = _
    simp only [S, map_sum, map_mul, map_prod, map_pow, map_natCast,
      ValuationSubring.coe_subtype]
  have hS : (IsLocalRing.residue R) S = 0 := by
    apply (IsLocalRing.residue_eq_zero_iff S).mpr
    apply (Valuation.mem_maximalIdeal_iff L v).mpr
    rw [hcoe]
    exact hmom
  simpa only [S, map_sum, map_mul, map_prod, map_pow, map_natCast] using hS

open scoped Classical in
/-- Equation (14) of [RW26b, Radchenko, Wheeler (2026b), Section 4, Equation (14)] reduced to
the residue field for two model coordinates. Used by Lemma 1(iii). -/
private theorem two_model_residue_moments {L : Type*} [Field L]
    {p s : ℕ} [Fact p.Prime] (v : Valuation L ℝ≥0)
    (hvp : v (p : L) < 1) (hs : 1 ≤ s) {ζ : L}
    (hζ : IsPrimitiveRoot ζ (p ^ s))
    (F : (Fin 2 → ZMod (p ^ s)) → L) (hF : ∀ x, v (F x) ≤ 1)
    (hS : ∀ a : Fin 2 → ZMod (p ^ s),
      v (∑ x, F x * ζ ^ (∑ i, (a i).val * (x i).val)) ^ 2 ≤
        v (p : L) ^ (s * Fintype.card (Fin 2)))
    (r₁ r₂ : ℕ) (hr : r₁ + r₂ < p - 1) :
    ∑ u : Fin 2 → ZMod p,
      (IsLocalRing.residue v.valuationSubring)
        (⟨F (fun i => torsionHom hs (u i)), hF _⟩ : v.valuationSubring) *
        ((u 0).val : IsLocalRing.ResidueField v.valuationSubring) ^ r₁ *
        ((u 1).val : IsLocalRing.ResidueField v.valuationSubring) ^ r₂ = 0 := by
  classical
  let r : Fin 2 → ℕ := ![r₁, r₂]
  have hr' : 2 * ∑ i, r i < Fintype.card (Fin 2) * (p - 1) := by
    simpa only [Fintype.card_fin, Fin.sum_univ_two, r, Matrix.cons_val_zero,
      Matrix.cons_val_one, Nat.reduceMul] using (show 2 * (r₁ + r₂) < 2 * (p - 1) by omega)
  have hm := model_coset_moments v hvp hs (by simp) hζ F hF hS 0 r hr'
  have hm' : v (∑ u : Fin 2 → ZMod p, F (fun i => torsionHom hs (u i)) *
      ∏ i, (((u i).val : ℕ) : L) ^ r i) < 1 := by
    simpa only [zero_add, torsionHom_apply] using hm
  have hres := residue_prod_moment_eq_zero v
    (fun u : Fin 2 → ZMod p => F (fun i => torsionHom hs (u i)))
    (fun u => hF _) r hm'
  simpa only [Fin.prod_univ_two, r, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_assoc] using hres

namespace MetricGroup

variable (M : MetricGroup G L) (v : Valuation L ℝ≥0)

/-! ### Units of a metric group

The bicharacter and Gaussian are roots of unity, and `√|G|` is integral. -/

/-- The bicharacter values are units: `v(⟨x; y⟩) = 1`. -/
theorem valuation_bichar (x y : G) : v (M.bichar x y) = 1 := by
  exact valuation_eq_one_of_pow_eq_one v (Fintype.card_ne_zero) (M.bichar_pow_card x y)

/-- The Gaussian values are units: `v(⟨x⟩) = 1`. -/
theorem valuation_gaussian (x : G) : v (M.gaussian x) = 1 := by
  exact valuation_eq_one_of_pow_eq_one v (Nat.mul_ne_zero (by decide) Fintype.card_ne_zero)
    (M.gaussian_pow_two_mul_card x)

/-- `√|G|` is integral: `v(s) ≤ 1`. -/
theorem valuation_sqrtCard_le_one : v M.sqrtCard ≤ 1 := by
  apply (sq_le_one_iff₀ (show 0 ≤ v M.sqrtCard from bot_le)).mp
  calc
    v M.sqrtCard ^ 2 = v (M.sqrtCard ^ 2) := by rw [map_pow]
    _ = v (Fintype.card G : L) := by rw [M.sqrtCard_sq]
    _ ≤ 1 := valuation_natCast_le_one v _

/-! ### Fourier integrality

A function is Fourier-integral at `v` when it and its normalized Fourier transform are
integral. -/

/-- **Fourier integrality** in the sense of [RW26b, Radchenko, Wheeler (2026b), Section 4,
Lemma 1]: `v(f(x)) ≤ 1` and `v(f̂(y)) ≤ 1` for all `x, y ∈ G`, with `f̂` the normalized Fourier
transform `MetricGroup.fourier`. -/
structure IsFourierIntegral (f : G → L) : Prop where
  /-- `f` is integral. -/
  le_one (x : G) : v (f x) ≤ 1
  /-- `f̂` is integral. -/
  fourier_le_one (y : G) : v (M.fourier f y) ≤ 1

open scoped Classical in
/-- The Fourier sum on a coset of a `p`-power subgroup has the squared valuation bound
required by `valuation_sum_mul_prod_choose_lt_one`. -/
private theorem valuation_coset_fourier_sq_le {p s : ℕ} [Fact p.Prime]
    (hvp : v (p : L) < 1) (H : AddSubgroup G)
    (hcard : Nat.card H = p ^ s) (hcop : p.Coprime H.index)
    {f : G → L} (hf : M.IsFourierIntegral v f) (c a : G) :
    v (∑ h : H, f (c + h) * M.bichar h (-a)) ^ 2 ≤ v (p : L) ^ s := by
  classical
  let T := ∑ u with u ∈ M.orthogonal H,
    M.bichar c u * M.fourier f (a + u)
  let S := ∑ h : H, f (c + h) * M.bichar h (-a)
  have hm : v (H.index : L) = 1 :=
    valuation_natCast_eq_one v hvp ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hcop)
  have hT : v T ≤ 1 := by
    apply v.map_sum_le
    intro u hu
    rw [map_mul, M.valuation_bichar]
    simpa only [one_mul] using hf.fourier_le_one (a + u)
  have hcast : (Fintype.card G : L) = (Nat.card H : L) * (H.index : L) := by
    have hh := congrArg (fun n : ℕ => (n : L)) H.card_mul_index
    simpa only [Nat.cast_mul, Nat.card_eq_fintype_card] using hh.symm
  have hHne : (Nat.card H : L) ≠ 0 := by
    have hGne : (Fintype.card G : L) ≠ 0 := by
      rw [← M.sqrtCard_sq]
      exact pow_ne_zero 2 M.sqrtCard_ne_zero
    intro hzero
    apply hGne
    rw [hcast, hzero, zero_mul]
  have heq : M.sqrtCard * T = (H.index : L) * M.bichar c (-a) * S := by
    have hh := M.coset_fourier_identity H f c a
    rw [hcast] at hh
    exact mul_left_cancel₀ hHne (by simpa only [T, S, mul_assoc] using hh)
  have hS : v S ≤ v M.sqrtCard := by
    have hh := congrArg v heq
    simp only [map_mul, hm, M.valuation_bichar, one_mul] at hh
    calc
      v S = v M.sqrtCard * v T := hh.symm
      _ ≤ v M.sqrtCard * 1 := mul_le_mul' le_rfl hT
      _ = v M.sqrtCard := mul_one _
  calc
    v S ^ 2 ≤ v M.sqrtCard ^ 2 := pow_le_pow_left₀ bot_le hS 2
    _ = v (Fintype.card G : L) := by rw [← map_pow, M.sqrtCard_sq]
    _ = v (p : L) ^ s := by
      rw [hcast, map_mul, hcard, Nat.cast_pow, map_pow, hm, mul_one]

open scoped Classical in
open scoped Classical in
/-- The shared coset estimate gives the standard Fourier bound in any primary model.
Used for the cyclic case and Lemma 1(iii). -/
private theorem valuation_model_fourier_sq_le {p s : ℕ} [Fact p.Prime]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (hvp : v (p : L) < 1)
    (E : (ι → ZMod (p ^ s)) ≃+ AddCommGroup.primaryComponent G p)
    (ζ : L) (hfreq : ∀ a : ι → ZMod (p ^ s),
      ∃ y : AddCommGroup.primaryComponent G p,
        ∀ x, M.bichar (E x : G) y = ζ ^ (∑ i, (a i).val * (x i).val))
    {f : G → L} (hf : M.IsFourierIntegral v f) (c : G)
    (a : ι → ZMod (p ^ s)) :
    v (∑ x : ι → ZMod (p ^ s), f (c + (E x : G)) *
      ζ ^ (∑ i, (a i).val * (x i).val)) ^ 2 ≤
      v (p : L) ^ (s * Fintype.card ι) := by
  classical
  let H := AddCommGroup.primaryComponent G p
  have hcard : Nat.card H = p ^ (s * Fintype.card ι) := primaryModelEquiv_card E
  have hcoset (c' a' : G) :
      v (∑ h : H, f (c' + h) * M.bichar h (-a')) ^ 2 ≤
        v (p : L) ^ (s * Fintype.card ι) :=
    M.valuation_coset_fourier_sq_le v hvp H hcard
      (primaryComponent_index_coprime (A := G) (p := p)) hf c' a'
  exact model_fourier_sq_le M v E ζ hfreq f hcoset c a

end MetricGroup

/-! ### Lemma 1 for a cyclic `p`-part

Reduction to the model `ZMod (p^s)` and the residue-field arguments. -/

namespace MetricGroup.IsFourierIntegral

variable {M : MetricGroup G L} {v : Valuation L ℝ≥0} {p : ℕ} [Fact p.Prime]

/-! ### Residue moments on `p`-torsion cosets

The Fourier estimate in cyclic coordinates gives the binomial congruence and then (14). -/

open scoped Classical in
/-- The valuation estimate leading to the residue moments (14) of
[RW26b, Radchenko, Wheeler (2026b), Section 4, Lemma 1], in cyclic coordinates.
Used by `exists_torsion_residue_moments`. -/
private theorem valuation_primary_coset_moments (hvp : v (p : L) < 1) {s : ℕ} (hs : 1 ≤ s)
    (hcard : Nat.card (AddCommGroup.primaryComponent G p) = p ^ s)
    (e : ZMod (p ^ s) ≃+ AddCommGroup.primaryComponent G p)
    {f : G → L} (hf : M.IsFourierIntegral v f) (c : G) (b : ZMod (p ^ s))
    (r : ℕ) (hr : 2 * r < p - 1) :
    v (∑ u : ZMod p,
      f (c + (e (b + ((p ^ (s - 1) * u.val : ℕ) : ZMod (p ^ s))) : G)) *
        (u.val : L) ^ r) < 1 := by
  classical
  let ζ := M.bichar (e 1 : G) (e 1 : G)
  let E := unitModelEquiv e
  let F : (Unit → ZMod (p ^ s)) → L := fun x => f (c + (e (x ()) : G))
  have hζ : IsPrimitiveRoot ζ (p ^ s) := M.primary_bichar_primitive hcard e
  have hF (x : Unit → ZMod (p ^ s)) : v (F x) ≤ 1 := hf.le_one _
  have hfreq (a : Unit → ZMod (p ^ s)) :
      ∃ y : AddCommGroup.primaryComponent G p,
        ∀ x, M.bichar (E x : G) y = ζ ^ (∑ i, (a i).val * (x i).val) := by
    refine ⟨e (a ()), ?_⟩
    intro x
    simpa [E, unitModelEquiv] using M.primary_bichar_coordinates e (a ()) (x ())
  have hS (a : Unit → ZMod (p ^ s)) :
      v (∑ x, F x * ζ ^ (∑ i, (a i).val * (x i).val)) ^ 2 ≤
        v (p : L) ^ (s * Fintype.card Unit) := by
    change v (∑ x : Unit → ZMod (p ^ s), f (c + (E x : G)) *
      ζ ^ (∑ i, (a i).val * (x i).val)) ^ 2 ≤ _
    exact M.valuation_model_fourier_sq_le v hvp E ζ hfreq hf c a
  have hcoset := model_coset_moments v hvp hs (by simp) hζ F hF hS
    (fun _ : Unit => b) (fun _ : Unit => r) (by simpa using hr)
  have hsum : (∑ u : Unit → ZMod p,
      F ((fun _ : Unit => b) + fun i =>
        ((p ^ (s - 1) * (u i).val : ℕ) : ZMod (p ^ s))) *
        ∏ i, (((u i).val : ℕ) : L) ^ ((fun _ : Unit => r) i)) =
      ∑ u : ZMod p,
        f (c + (e (b + ((p ^ (s - 1) * u.val : ℕ) : ZMod (p ^ s))) : G)) *
          (u.val : L) ^ r := by
    apply Fintype.sum_equiv (Equiv.funUnique Unit (ZMod p))
    intro u
    simp [F]
  rw [← hsum]
  exact hcoset

variable [DecidableEq G]

/-- Cyclic coordinates identify `ZMod p` with the `p`-torsion of `G`.
Used by both Lemma 1 conclusions. -/
private noncomputable def torsionCoordEquiv {s : ℕ} (hs : 1 ≤ s)
    (hG : (Finset.univ.filter fun u : G => p • u = 0).card = p)
    (e : ZMod (p ^ s) ≃+ AddCommGroup.primaryComponent G p) :
    ZMod p ≃ (nsmulAddMonoidHom (α := G) p).ker := by
  classical
  let T := (nsmulAddMonoidHom (α := G) p).ker
  let φ : ZMod p → T := fun u =>
    ⟨(e (zmodTorsionCoord (s := s) u) : G), by
      have hh : p • e (zmodTorsionCoord (s := s) u) = 0 := by
        rw [← map_nsmul e, zmodTorsionCoord_nsmul hs u, map_zero]
      exact congrArg Subtype.val hh⟩
  have hinj : Function.Injective φ := by
    intro u w huw
    apply zmodTorsionCoord_injective hs
    apply e.injective
    apply Subtype.ext
    exact congrArg (fun z : T => (z : G)) huw
  have hcard : Fintype.card (ZMod p) = Fintype.card T := by
    rw [ZMod.card, Fintype.card_subtype]
    simpa only [T, AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply] using hG.symm
  exact Equiv.ofBijective φ ((Fintype.bijective_iff_injective_and_card φ).mpr ⟨hinj, hcard⟩)

/-- Evaluation of the torsion-coordinate equivalence. -/
private theorem torsionCoordEquiv_apply {s : ℕ} (hs : 1 ≤ s)
    (hG : (Finset.univ.filter fun u : G => p • u = 0).card = p)
    (e : ZMod (p ^ s) ≃+ AddCommGroup.primaryComponent G p) (u : ZMod p) :
    ((torsionCoordEquiv (p := p) hs hG e u :
        (nsmulAddMonoidHom (α := G) p).ker) : G) =
      (e (zmodTorsionCoord (s := s) u) : G) := rfl

/-- The zero coordinate is the zero torsion point. Used by `valuation_sub_lt_one`. -/
private theorem torsionCoordEquiv_zero {s : ℕ} (hs : 1 ≤ s)
    (hG : (Finset.univ.filter fun u : G => p • u = 0).card = p)
    (e : ZMod (p ^ s) ≃+ AddCommGroup.primaryComponent G p) :
    torsionCoordEquiv (p := p) hs hG e 0 = 0 := by
  apply Subtype.ext
  change (e (zmodTorsionCoord (s := s) (0 : ZMod p)) : G) = 0
  simp [zmodTorsionCoord]

/-! ### Reduction to the residue field

The maximal ideal consists of elements with valuation below one. -/

open scoped Classical in
/-- A moment in the maximal ideal reduces to a zero moment in the residue field.
Used by both Lemma 1 conclusions. -/
private theorem residue_moment_eq_zero (F : ZMod p → L) (hF : ∀ u, v (F u) ≤ 1)
    (r : ℕ) (hmom : v (∑ u, F u * (u.val : L) ^ r) < 1) :
    ∑ u : ZMod p,
      (IsLocalRing.residue v.valuationSubring)
          (⟨F u, hF u⟩ : v.valuationSubring) *
        (u.val : IsLocalRing.ResidueField v.valuationSubring) ^ r = 0 := by
  classical
  have hsum : (∑ u : Unit → ZMod p, F (u ()) *
      ∏ i, ((u i).val : L) ^ ((fun _ : Unit => r) i)) =
        ∑ u : ZMod p, F u * (u.val : L) ^ r := by
    apply Fintype.sum_equiv (Equiv.funUnique Unit (ZMod p))
    intro u
    simp
  have hm : v (∑ u : Unit → ZMod p, F (u ()) *
      ∏ i, ((u i).val : L) ^ ((fun _ : Unit => r) i)) < 1 := by
    rw [hsum]
    exact hmom
  have hres := residue_prod_moment_eq_zero v (fun u : Unit → ZMod p => F (u ()))
    (fun u => hF _) (fun _ : Unit => r) hm
  have hsumres : (∑ u : Unit → ZMod p,
      (IsLocalRing.residue v.valuationSubring)
        (⟨F (u ()), hF _⟩ : v.valuationSubring) *
        ∏ i, ((u i).val : IsLocalRing.ResidueField v.valuationSubring) ^
          ((fun _ : Unit => r) i)) =
      ∑ u : ZMod p,
        (IsLocalRing.residue v.valuationSubring)
          (⟨F u, hF u⟩ : v.valuationSubring) *
          (u.val : IsLocalRing.ResidueField v.valuationSubring) ^ r := by
    apply Fintype.sum_equiv (Equiv.funUnique Unit (ZMod p))
    intro u
    simp
  rw [← hsumres]
  exact hres

open scoped Classical in
/-- The valuation moments (14) reduced to the residue field in fixed cyclic coordinates.
Used for both `f` and `1/f` in `valuation_sub_lt_one`. -/
private theorem torsion_residue_moments (hvp : v (p : L) < 1)
    (hG : (Finset.univ.filter fun u : G => p • u = 0).card = p) {s : ℕ} (hs : 1 ≤ s)
    (hcard : Nat.card (AddCommGroup.primaryComponent G p) = p ^ s)
    (e : ZMod (p ^ s) ≃+ AddCommGroup.primaryComponent G p)
    {f : G → L} (hf : M.IsFourierIntegral v f) (c : G)
    (r : ℕ) (hr : 2 * r < p - 1) :
    ∑ u : ZMod p,
      (IsLocalRing.residue v.valuationSubring)
          (⟨f (c + (torsionCoordEquiv (p := p) hs hG e u : G)), hf.le_one _⟩ :
            v.valuationSubring) *
        (u.val : IsLocalRing.ResidueField v.valuationSubring) ^ r = 0 := by
  classical
  let φ := torsionCoordEquiv (p := p) hs hG e
  apply residue_moment_eq_zero (v := v) (fun u : ZMod p => f (c + (φ u : G)))
    (fun u => hf.le_one _) r
  have hm := valuation_primary_coset_moments hvp hs hcard e hf c 0 r hr
  simpa only [φ, torsionCoordEquiv_apply, zero_add, zmodTorsionCoord] using hm

open scoped Classical in
/-- The residue moments (14) of [RW26b, Radchenko, Wheeler (2026b), Section 4, Lemma 1]
on each coset of `G[p]`, in one coordinate system chosen independently of `f`. Both parts of
Lemma 1 use this reduction. -/
theorem exists_torsion_residue_moments (hvp : v (p : L) < 1)
    (hG : (Finset.univ.filter fun u : G => p • u = 0).card = p) :
    ∃ φ : ZMod p ≃ (nsmulAddMonoidHom (α := G) p).ker,
      φ 0 = 0 ∧
        ∀ {f : G → L} (hf : M.IsFourierIntegral v f) (c : G) (r : ℕ),
          2 * r < p - 1 →
          ∑ u : ZMod p,
            (IsLocalRing.residue v.valuationSubring)
                (⟨f (c + (φ u : G)), hf.le_one _⟩ : v.valuationSubring) *
              (u.val : IsLocalRing.ResidueField v.valuationSubring) ^ r = 0 := by
  classical
  obtain ⟨s, hcard, hcyc⟩ := primaryComponent_cyclic_of_card_torsion hG
  have hs : 1 ≤ s := primaryComponent_exponent_pos hG hcard
  let e : ZMod (p ^ s) ≃+ AddCommGroup.primaryComponent G p := by
    exact hcard ▸ zmodAddCyclicAddEquiv hcyc
  refine ⟨torsionCoordEquiv (p := p) hs hG e,
    torsionCoordEquiv_zero hs hG e, ?_⟩
  intro f hf c r hr
  exact torsion_residue_moments hvp hG hs hcard e hf c r hr

open scoped Classical in
/-- An equivalence with the `p`-torsion subgroup preserves counts of any predicate on that
subgroup. Used by `forall_lt_one_or_lt_two_mul_card`. -/
private theorem card_torsion_filter
    (φ : ZMod p ≃ (nsmulAddMonoidHom (α := G) p).ker) (P : G → Prop) :
    (Finset.univ.filter fun t : ZMod p => P (φ t : G)).card =
      (Finset.univ.filter fun u : G => p • u = 0 ∧ P u).card := by
  classical
  apply Finset.card_bij (fun t _ => (φ t : G))
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    exact ⟨(φ t).property, ht⟩
  · intro t₁ _ t₂ _ ht
    exact φ.injective (Subtype.ext ht)
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    refine ⟨φ.symm ⟨u, hu.1⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa only [Equiv.apply_symm_apply] using hu.2
    · exact congrArg Subtype.val (φ.apply_symm_apply ⟨u, hu.1⟩)

/-- **[RW26b, Radchenko, Wheeler (2026b), Section 4, Lemma 1](i)**: if `|G[p]| = p` and `f` is
Fourier-integral at a valuation above `p`, then on each coset `c + G[p]` the reduction of `f`
modulo `𝔪` is zero everywhere or nonzero at more than half the points. -/
@[source "RW26b, Lemma 1, p. 5 (i)"]
theorem forall_lt_one_or_lt_two_mul_card (hvp : v (p : L) < 1)
    (hG : (Finset.univ.filter fun u : G => p • u = 0).card = p) {f : G → L}
    (hf : M.IsFourierIntegral v f) (c : G) :
    (∀ u : G, p • u = 0 → v (f (c + u)) < 1) ∨
      p < 2 * (Finset.univ.filter fun u : G => p • u = 0 ∧ v (f (c + u)) = 1).card := by
  classical
  let R := v.valuationSubring
  let k := IsLocalRing.ResidueField R
  let _ : CharP k p := valuation_residue_charP (v := v) hvp
  obtain ⟨φ, hφ0, hmom⟩ := exists_torsion_residue_moments hvp hG
  let g : ZMod p → k := fun t => (IsLocalRing.residue R)
    (⟨f (c + (φ t : G)), hf.le_one _⟩ : R)
  have hgm (r : ℕ) (hr : 2 * r < p - 1) :
      ∑ t, g t * (t.val : k) ^ r = 0 := hmom hf c r hr
  have hunit_iff (t : ZMod p) : g t ≠ 0 ↔ v (f (c + (φ t : G))) = 1 := by
    rw [ne_eq, valuation_residue_eq_zero_iff (v := v) (hf.le_one _)]
    constructor
    · intro ht
      exact le_antisymm (hf.le_one _) (le_of_not_gt ht)
    · intro ht hn
      rw [ht] at hn
      exact (lt_irrefl (1 : ℝ≥0)) hn
  rcases eq_zero_or_lt_two_mul_card_of_moments g hgm with hg | hg
  · left
    intro u hu
    let t : (nsmulAddMonoidHom (α := G) p).ker := ⟨u, hu⟩
    have hz : g (φ.symm t) = 0 := by rw [hg]; rfl
    have hz' : (IsLocalRing.residue R)
        (⟨f (c + u), hf.le_one _⟩ : R) = 0 := by
      simpa only [g, t, Equiv.apply_symm_apply] using hz
    exact (valuation_residue_eq_zero_iff (v := v) (hf.le_one _)).mp hz'
  · right
    have hcount : (Finset.univ.filter fun t : ZMod p => g t ≠ 0).card =
        (Finset.univ.filter fun u : G => p • u = 0 ∧ v (f (c + u)) = 1).card := by
      have hfilter : (Finset.univ.filter fun t : ZMod p => g t ≠ 0) =
          (Finset.univ.filter fun t : ZMod p => v (f (c + (φ t : G))) = 1) := by
        ext t
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hunit_iff t
      rw [hfilter]
      convert card_torsion_filter φ (fun u => v (f (c + u)) = 1) using 1 <;>
        (apply congrArg Finset.card; ext; simp)
    rw [← hcount]
    exact hg

/-- **[RW26b, Radchenko, Wheeler (2026b), Section 4, Lemma 1](ii)**: if `|G[p]| = p`, all values
of `f` are units at a valuation above `p`, and `f` and `1/f` are Fourier-integral, then `f` is
constant modulo `𝔪` on each coset of `G[p]`. -/
@[source "RW26b, Lemma 1, p. 5 (ii)"]
theorem valuation_sub_lt_one (hvp : v (p : L) < 1)
    (hG : (Finset.univ.filter fun u : G => p • u = 0).card = p) {f : G → L}
    (hf : M.IsFourierIntegral v f) (hunit : ∀ x, v (f x) = 1)
    (hinv : M.IsFourierIntegral v fun x => (f x)⁻¹) (c : G) {u : G} (hu : p • u = 0) :
    v (f (c + u) - f c) < 1 := by
  classical
  let R := v.valuationSubring
  let k := IsLocalRing.ResidueField R
  let _ : CharP k p := valuation_residue_charP (v := v) hvp
  obtain ⟨φ, hφ0, hmom⟩ := exists_torsion_residue_moments hvp hG
  let g : ZMod p → k := fun t => (IsLocalRing.residue R)
    (⟨f (c + (φ t : G)), hf.le_one _⟩ : R)
  have hnonzero (t : ZMod p) : f (c + (φ t : G)) ≠ 0 := by
    intro hzero
    have h := hunit (c + (φ t : G))
    simp [hzero] at h
  have hg0 (t : ZMod p) : g t ≠ 0 := by
    intro hzero
    have hlt := (valuation_residue_eq_zero_iff (v := v) (hf.le_one _)).mp hzero
    rw [hunit] at hlt
    exact (lt_irrefl (1 : ℝ≥0)) hlt
  have hgm (r : ℕ) (hr : 2 * r < p - 1) :
      ∑ t, g t * (t.val : k) ^ r = 0 :=
    hmom hf c r hr
  have hginvm (r : ℕ) (hr : 2 * r < p - 1) :
      ∑ t, (g t)⁻¹ * (t.val : k) ^ r = 0 := by
    calc
      _ = ∑ t : ZMod p,
          (IsLocalRing.residue R)
              (⟨(f (c + (φ t : G)))⁻¹, hinv.le_one _⟩ : R) * (t.val : k) ^ r := by
            apply Finset.sum_congr rfl
            intro t _
            rw [valuation_residue_inv_eq (v := v) (hf.le_one _) (hinv.le_one _) (hnonzero t)]
      _ = 0 := hmom hinv c r hr
  have hconst (t : ZMod p) : g t = g 0 :=
    eq_const_of_moments g hg0 hgm hginvm t
  let t : ZMod p := φ.symm (⟨u, hu⟩ : (nsmulAddMonoidHom (α := G) p).ker)
  have hres : (IsLocalRing.residue R) (⟨f (c + u), hf.le_one _⟩ : R) =
      (IsLocalRing.residue R) (⟨f c, hf.le_one _⟩ : R) := by
    simpa only [g, t, Equiv.apply_symm_apply, hφ0, AddSubgroup.coe_zero,
      add_zero] using hconst t
  exact (valuation_residue_eq_iff (v := v) (hf.le_one _) (hf.le_one _)).mp hres

/-! ### Lemma 1(iii) for a `p`-part `(ℤ/p^s)²`

The reduction to the model `Fin 2 → ZMod (p^s)` and the two-variable residue argument. -/

/-- The squared Fourier bound for a two-coordinate model, used by `separated_of_model`. -/
private def HasTwoFourierBound {L : Type*} [Field L] {p s : ℕ} [Fact p.Prime]
    (v : Valuation L ℝ≥0) (ζ : L) (F : (Fin 2 → ZMod (p ^ s)) → L) : Prop :=
  ∀ q : Fin 2 → ZMod (p ^ s),
    v (∑ x : Fin 2 → ZMod (p ^ s), F x *
      ζ ^ (∑ i, (q i).val * (x i).val)) ^ 2 ≤ v (p : L) ^ (s * 2)

/-- The two-coordinate Fourier bound gives residue moments in torsion coordinates.
Used by `separated_of_model` for a function and its inverse. -/
private theorem model_torsion_residue_moments {G L : Type*} [AddCommGroup G] [Fintype G]
    [Field L] {p s : ℕ} [Fact p.Prime] (v : Valuation L ℝ≥0)
    (hvp : v (p : L) < 1) (hs : 1 ≤ s)
    (E : (Fin 2 → ZMod (p ^ s)) ≃+ AddCommGroup.primaryComponent G p)
    (ζ : L) (hζ : IsPrimitiveRoot ζ (p ^ s)) (F : G → L)
    (hF : ∀ x, v (F x) ≤ 1) (c : G)
    (hS : HasTwoFourierBound v ζ (fun x => F (c + (E x : G))))
    (r₁ r₂ : ℕ) (hr : r₁ + r₂ < p - 1) :
    ∑ w : Fin 2 → ZMod p,
      (IsLocalRing.residue v.valuationSubring)
        (⟨F (c + (torsionModelEquiv hs E w : G)), hF _⟩ : v.valuationSubring) *
        ((w 0).val : IsLocalRing.ResidueField v.valuationSubring) ^ r₁ *
        ((w 1).val : IsLocalRing.ResidueField v.valuationSubring) ^ r₂ = 0 := by
  classical
  have h := two_model_residue_moments v hvp hs hζ
    (fun x => F (c + (E x : G))) (fun x => hF _)
    (by simpa only [HasTwoFourierBound, Fintype.card_fin] using hS) r₁ r₂ hr
  have hcoord (w : Fin 2 → ZMod p) :
      (E (fun i => torsionHom hs (w i)) : G) = (torsionModelEquiv hs E w : G) :=
    (torsionModelEquiv_apply hs E w).symm
  simpa only [hcoord] using h

/-- The residue of an integral value of a function, used by `separated_residue_eq`. -/
private noncomputable def integralValueResidue {G L : Type*} [Field L]
    (v : Valuation L ℝ≥0)
    (f : G → L) (hf : ∀ x, v (f x) ≤ 1) (x : G) :
    IsLocalRing.ResidueField v.valuationSubring :=
  (IsLocalRing.residue v.valuationSubring) (⟨f x, hf x⟩ : v.valuationSubring)

/-- A valuation unit has nonzero residue; used by `separated_from_moments`. -/
private theorem integralValueResidue_ne_zero {G L : Type*} [Field L]
    (v : Valuation L ℝ≥0) (f : G → L) (hf : ∀ x, v (f x) ≤ 1)
    (hunit : ∀ x, v (f x) = 1) (x : G) :
    integralValueResidue v f hf x ≠ 0 := by
  intro hz
  have hlt := (valuation_residue_eq_zero_iff (v := v) (hf x)).mp hz
  rw [hunit] at hlt
  exact (lt_irrefl (1 : ℝ≥0)) hlt

/-- Separation modulo the maximal ideal gives a product of the two coordinate residues.
Used by `separated_from_moments`. -/
private theorem separated_residue_eq {G L : Type*} [AddCommGroup G] [Field L]
    {p : ℕ} [Fact p.Prime]
    (v : Valuation L ℝ≥0) (f : G → L) (hf : ∀ x, v (f x) ≤ 1)
    (hunit : ∀ x, v (f x) = 1) (c a b : G)
    (hsep : ∀ i j : ℕ, v (f (c + i • a + j • b) * f c -
      f (c + i • a) * f (c + j • b)) < 1)
    (ht0 : integralValueResidue v f hf c ≠ 0) (i j : ZMod p) :
    integralValueResidue v f hf (c + i.val • a + j.val • b) =
      integralValueResidue v f hf (c + i.val • a) *
        (integralValueResidue v f hf (c + j.val • b) *
          (integralValueResidue v f hf c)⁻¹) := by
  let R := v.valuationSubring
  change (IsLocalRing.residue R)
      (⟨f (c + i.val • a + j.val • b), hf _⟩ : R) =
    (IsLocalRing.residue R) (⟨f (c + i.val • a), hf _⟩ : R) *
      ((IsLocalRing.residue R) (⟨f (c + j.val • b), hf _⟩ : R) *
        ((IsLocalRing.residue R) (⟨f c, hf c⟩ : R))⁻¹)
  simp only [integralValueResidue] at ht0
  have hxle : v (f (c + i.val • a + j.val • b) * f c) ≤ 1 := by
    rw [map_mul, hunit, hunit, one_mul]
  have hyle : v (f (c + i.val • a) * f (c + j.val • b)) ≤ 1 := by
    rw [map_mul, hunit, hunit, one_mul]
  have heq := (valuation_residue_eq_iff (v := v) hxle hyle).mpr (hsep i.val j.val)
  have hp : (IsLocalRing.residue R)
        (⟨f (c + i.val • a + j.val • b), hf _⟩ : R) *
        (IsLocalRing.residue R) (⟨f c, hf c⟩ : R) =
      (IsLocalRing.residue R) (⟨f (c + i.val • a), hf _⟩ : R) *
        (IsLocalRing.residue R) (⟨f (c + j.val • b), hf _⟩ : R) := by
    have heq' : (IsLocalRing.residue R)
        ((⟨f (c + i.val • a + j.val • b), hf _⟩ : R) * (⟨f c, hf c⟩ : R)) =
      (IsLocalRing.residue R)
        ((⟨f (c + i.val • a), hf _⟩ : R) *
          (⟨f (c + j.val • b), hf _⟩ : R)) := by
      convert heq using 1
    simpa only [map_mul] using heq'
  calc
    _ = ((IsLocalRing.residue R)
        (⟨f (c + i.val • a + j.val • b), hf _⟩ : R) *
          (IsLocalRing.residue R) (⟨f c, hf c⟩ : R)) *
          ((IsLocalRing.residue R) (⟨f c, hf c⟩ : R))⁻¹ := by
            rw [mul_assoc, mul_inv_cancel₀ ht0, mul_one]
    _ = _ := by rw [hp]; ring

/-- Factor a two-variable moment of a separated function into one-variable moments.
Used by `separated_from_moments`. -/
private theorem separated_moment_product {p : ℕ} [Fact p.Prime]
    {k : Type*} [Field k] (A D : ZMod p → k)
    (g : (Fin 2 → ZMod p) → k)
    (hg : ∀ u, g u = A (u 0) * D (u 1))
    (hmom : ∀ r₁ r₂ : ℕ, r₁ + r₂ < p - 1 →
      ∑ u : Fin 2 → ZMod p,
        g u * ((u 0).val : k) ^ r₁ * ((u 1).val : k) ^ r₂ = 0)
    (r₁ r₂ : ℕ) (hr : r₁ + r₂ < p - 1) :
    (∑ i, A i * (i.val : k) ^ r₁) *
      (∑ j, D j * (j.val : k) ^ r₂) = 0 := by
  rw [← sum_two_separable A D r₁ r₂]
  convert hmom r₁ r₂ hr using 1
  apply Finset.sum_congr rfl
  intro u _
  rw [hg u]

/-- Vanishing of all two-coordinate moments below total degree `p - 1`.
Used by `separated_moments_const`. -/
private def HasTwoMoments {p : ℕ} [Fact p.Prime] {k : Type*} [Field k]
    (g : (Fin 2 → ZMod p) → k) : Prop :=
  ∀ r₁ r₂ : ℕ, r₁ + r₂ < p - 1 →
    ∑ u : Fin 2 → ZMod p,
      g u * ((u 0).val : k) ^ r₁ * ((u 1).val : k) ^ r₂ = 0

/-- The two moment systems force one separated factor to be constant.
Used by `separated_from_moments`. -/
private theorem separated_moments_const {p : ℕ} [Fact p.Prime]
    {k : Type*} [Field k] [CharP k p]
    (A D : ZMod p → k) (hA0 : ∀ i, A i ≠ 0) (hD0 : ∀ j, D j ≠ 0)
    (q : (Fin 2 → ZMod p) → k) (hq : ∀ u, q u = A (u 0) * D (u 1))
    (hmom : HasTwoMoments q) (hinvmom : HasTwoMoments (fun u => (q u)⁻¹)) :
    (∀ i, A i = A 0) ∨ (∀ j, D j = D 0) := by
  have hprod (r₁ r₂ : ℕ) (hr : r₁ + r₂ < p - 1) :
      (∑ i, A i * (i.val : k) ^ r₁) *
        (∑ j, D j * (j.val : k) ^ r₂) = 0 :=
    separated_moment_product A D q hq hmom r₁ r₂ hr
  have hprod_inv (r₁ r₂ : ℕ) (hr : r₁ + r₂ < p - 1) :
      (∑ i, (A i)⁻¹ * (i.val : k) ^ r₁) *
        (∑ j, (D j)⁻¹ * (j.val : k) ^ r₂) = 0 := by
    apply separated_moment_product (fun i => (A i)⁻¹) (fun j => (D j)⁻¹)
      (fun u => (q u)⁻¹) _ hinvmom r₁ r₂ hr
    intro u
    rw [hq u]
    ring
  exact forall_eq_or_forall_eq_of_moments A D hA0 hD0 hprod hprod_inv

/-- Equality of residues along `p`-torsion gives valuation congruence along that direction.
Used by `separated_from_moments`. -/
private theorem valuation_const_along_torsion {G L : Type*} [AddCommGroup G] [Field L]
    {p : ℕ} [Fact p.Prime] (v : Valuation L ℝ≥0) (f : G → L)
    (hf : ∀ x, v (f x) ≤ 1) (c a : G) (ha : p • a = 0)
    (hres : ∀ u : ZMod p, integralValueResidue v f hf (c + u.val • a) =
      integralValueResidue v f hf c) :
    ∀ i : ℕ, v (f (c + i • a) - f c) < 1 := by
  intro i
  have hi : i • a = ((i : ZMod p).val) • a := by
    simpa only [ZMod.val_natCast] using nsmul_eq_mod_nsmul i ha
  have heq : integralValueResidue v f hf (c + i • a) =
      integralValueResidue v f hf c := by simpa only [hi] using hres (i : ZMod p)
  exact (valuation_residue_eq_iff (v := v) (hf _) (hf _)).mp heq

open scoped Classical in
/-- Separation and the direct and inverse residue moments in one torsion coordinate system.
Used by `separated_from_moments`. -/
private structure SeparatedMomentData {G L : Type*} [AddCommGroup G] [Field L]
    {p : ℕ} [Fact p.Prime] (v : Valuation L ℝ≥0) (f : G → L)
    (hf : ∀ x, v (f x) ≤ 1)
    (τ : (Fin 2 → ZMod p) ≃+ (nsmulAddMonoidHom (α := G) p).ker)
    (B : (Fin 2 → ZMod p) ≃+ (Fin 2 → ZMod p)) (c a b : G) : Prop where
  /-- Separation on the torsion coset. -/
  hsep : ∀ i j : ℕ, v (f (c + i • a + j • b) * f c -
      f (c + i • a) * f (c + j • b)) < 1
  /-- Vanishing moments of the residues. -/
  hmom : ∀ r₁ r₂ : ℕ, r₁ + r₂ < p - 1 →
      ∑ u : Fin 2 → ZMod p,
        (IsLocalRing.residue v.valuationSubring)
          (⟨f (c + (τ (B u) : G)), hf _⟩ : v.valuationSubring) *
          ((u 0).val : IsLocalRing.ResidueField v.valuationSubring) ^ r₁ *
          ((u 1).val : IsLocalRing.ResidueField v.valuationSubring) ^ r₂ = 0
  /-- Vanishing moments of the inverse residues. -/
  hinvmom : ∀ r₁ r₂ : ℕ, r₁ + r₂ < p - 1 →
      ∑ u : Fin 2 → ZMod p,
        ((IsLocalRing.residue v.valuationSubring)
          (⟨f (c + (τ (B u) : G)), hf _⟩ : v.valuationSubring))⁻¹ *
          ((u 0).val : IsLocalRing.ResidueField v.valuationSubring) ^ r₁ *
          ((u 1).val : IsLocalRing.ResidueField v.valuationSubring) ^ r₂ = 0

/-- The residue moments of a separated unit-valued function force constancy in one of its two
coordinates. Used by Lemma 1(iii). -/
private theorem separated_from_moments {G L : Type*} [AddCommGroup G] [Fintype G] [Field L]
    {p : ℕ} [Fact p.Prime] (M : MetricGroup G L) (v : Valuation L ℝ≥0)
    (hvp : v (p : L) < 1) {f : G → L} (hf : M.IsFourierIntegral v f)
    (hunit : ∀ x, v (f x) = 1)
    (τ : (Fin 2 → ZMod p) ≃+ (nsmulAddMonoidHom (α := G) p).ker)
    {a b : G} (ha : p • a = 0) (hb : p • b = 0)
    (B : (Fin 2 → ZMod p) ≃+ (Fin 2 → ZMod p))
    (hB : ∀ u, ((τ (B u) : (nsmulAddMonoidHom (α := G) p).ker) : G) =
      (u 0).val • a + (u 1).val • b)
    (c : G)
    (hdata : SeparatedMomentData v f hf.le_one τ B c a b) :
    (∀ i : ℕ, v (f (c + i • a) - f c) < 1) ∨
      ∀ j : ℕ, v (f (c + j • b) - f c) < 1 := by
  classical
  rcases hdata with ⟨hsep, hmom, hinvmom⟩
  let R := v.valuationSubring
  let k := IsLocalRing.ResidueField R
  let _ : CharP k p := valuation_residue_charP (v := v) hvp
  let t0 : k := (IsLocalRing.residue R) (⟨f c, hf.le_one c⟩ : R)
  let A : ZMod p → k := fun i =>
    (IsLocalRing.residue R) (⟨f (c + i.val • a), hf.le_one _⟩ : R)
  let C : ZMod p → k := fun j =>
    (IsLocalRing.residue R) (⟨f (c + j.val • b), hf.le_one _⟩ : R)
  let D : ZMod p → k := fun j => C j * t0⁻¹
  have hres_ne (x : G) :
      (IsLocalRing.residue R) (⟨f x, hf.le_one x⟩ : R) ≠ 0 :=
    integralValueResidue_ne_zero v f hf.le_one hunit x
  have ht0 : t0 ≠ 0 := hres_ne c
  have hA0 (i : ZMod p) : A i ≠ 0 := hres_ne _
  have hC0 (j : ZMod p) : C j ≠ 0 := hres_ne _
  have hD0 (j : ZMod p) : D j ≠ 0 := mul_ne_zero (hC0 j) (inv_ne_zero ht0)
  have hsep_B (u : Fin 2 → ZMod p) :
      (IsLocalRing.residue R)
        (⟨f (c + (τ (B u) : G)), hf.le_one _⟩ : R) = A (u 0) * D (u 1) := by
    rw [hB u]
    simpa only [integralValueResidue, A, D, C, t0, add_assoc] using
      separated_residue_eq v f hf.le_one hunit c a b hsep ht0 (u 0) (u 1)
  let q : (Fin 2 → ZMod p) → k := fun u =>
    (IsLocalRing.residue R) (⟨f (c + (τ (B u) : G)), hf.le_one _⟩ : R)
  have hqmom : HasTwoMoments q := by
    simpa only [HasTwoMoments, q] using hmom
  have hqinv : HasTwoMoments (fun u => (q u)⁻¹) := by
    simpa only [HasTwoMoments, q] using hinvmom
  rcases separated_moments_const A D hA0 hD0 q hsep_B hqmom hqinv with hA | hD
  · left
    apply valuation_const_along_torsion v f hf.le_one c a ha
    intro u
    simpa [integralValueResidue, A] using hA u
  · right
    apply valuation_const_along_torsion v f hf.le_one c b hb
    intro u
    have hC : C u = C 0 := by
      apply mul_right_cancel₀ (inv_ne_zero ht0)
      exact hD u
    simpa [integralValueResidue, C] using hC

/-- The two-coordinate Fourier estimates give Lemma 1(iii) in a chosen primary model. -/
private theorem separated_of_model {G L : Type*} [AddCommGroup G] [Fintype G] [Field L]
    {p s : ℕ} [Fact p.Prime] (M : MetricGroup G L) (v : Valuation L ℝ≥0)
    (hvp : v (p : L) < 1) (hs : 1 ≤ s)
    (E : (Fin 2 → ZMod (p ^ s)) ≃+ AddCommGroup.primaryComponent G p)
    (ζ : L) (hζ : IsPrimitiveRoot ζ (p ^ s)) {f : G → L}
    (hf : M.IsFourierIntegral v f) (hunit : ∀ x, v (f x) = 1)
    (hinv : M.IsFourierIntegral v fun x => (f x)⁻¹)
    {a b : G} (ha : p • a = 0) (hb : p • b = 0)
    (hab : ∀ i j : ZMod p, i.val • a + j.val • b = 0 → i = 0 ∧ j = 0) (c : G)
    (hsep : ∀ i j : ℕ, v (f (c + i • a + j • b) * f c -
      f (c + i • a) * f (c + j • b)) < 1)
    (hSf : HasTwoFourierBound v ζ (fun x => f (c + (E x : G))))
    (hSi : HasTwoFourierBound v ζ (fun x => (f (c + (E x : G)))⁻¹)) :
    (∀ i : ℕ, v (f (c + i • a) - f c) < 1) ∨
      ∀ j : ℕ, v (f (c + j • b) - f c) < 1 := by
  classical
  let τ := torsionModelEquiv hs E
  obtain ⟨B, hB⟩ := exists_torsion_basis_change τ a b ha hb hab
  let R := v.valuationSubring
  let k := IsLocalRing.ResidueField R
  let _ : CharP k p := valuation_residue_charP (v := v) hvp
  let g : (Fin 2 → ZMod p) → k := fun w =>
    (IsLocalRing.residue R) (⟨f (c + (τ w : G)), hf.le_one _⟩ : R)
  have hstd (r₁ r₂ : ℕ) (hr : r₁ + r₂ < p - 1) :
      ∑ w : Fin 2 → ZMod p, g w * (w 0).val ^ r₁ * (w 1).val ^ r₂ = 0 :=
    model_torsion_residue_moments v hvp hs E ζ hζ f hf.le_one c hSf r₁ r₂ hr
  have hmom (r₁ r₂ : ℕ) (hr : r₁ + r₂ < p - 1) :
      ∑ u : Fin 2 → ZMod p, g (B u) * (u 0).val ^ r₁ * (u 1).val ^ r₂ = 0 :=
    moments_of_addEquiv g hstd B r₁ r₂ hr
  have hne (x : G) : f x ≠ 0 := by
    intro h0
    have hh := hunit x
    simp [h0] at hh
  have hginv (w : Fin 2 → ZMod p) :
      (IsLocalRing.residue R)
        (⟨(f (c + (τ w : G)))⁻¹, hinv.le_one _⟩ : R) = (g w)⁻¹ := by
    exact valuation_residue_inv_eq v (hf.le_one _) (hinv.le_one _) (hne _)
  have hstdInv (r₁ r₂ : ℕ) (hr : r₁ + r₂ < p - 1) :
      ∑ w : Fin 2 → ZMod p, (g w)⁻¹ * (w 0).val ^ r₁ * (w 1).val ^ r₂ = 0 := by
    have h := model_torsion_residue_moments v hvp hs E ζ hζ
      (fun x => (f x)⁻¹) hinv.le_one c hSi r₁ r₂ hr
    calc
      _ = ∑ w : Fin 2 → ZMod p,
          (IsLocalRing.residue R)
            (⟨(f (c + (τ w : G)))⁻¹, hinv.le_one _⟩ : R) *
              (w 0).val ^ r₁ * (w 1).val ^ r₂ := by
            apply Finset.sum_congr rfl
            intro w _
            rw [hginv w]
      _ = 0 := h
  have hinvmom (r₁ r₂ : ℕ) (hr : r₁ + r₂ < p - 1) :
      ∑ u : Fin 2 → ZMod p, (g (B u))⁻¹ * (u 0).val ^ r₁ * (u 1).val ^ r₂ = 0 :=
    moments_of_addEquiv (fun w => (g w)⁻¹) hstdInv B r₁ r₂ hr
  exact separated_from_moments M v hvp hf hunit τ ha hb B hB c ⟨hsep, hmom, hinvmom⟩

omit [DecidableEq G] in
/-- **[RW26b, Radchenko, Wheeler (2026b), Section 4, Lemma 1](iii)**: suppose the `p`-primary
part of `G` is the image of an injective `e : (ℤ/p^s)² → G`, all values of `f` are units at a
valuation above `p`, and `f` and `1/f` are Fourier-integral. If `a, b` form a basis of `G[p]` and
on the coset `c + G[p]` the reduction of `f` separates in the coordinates of `a, b`,
`f(c + ia + jb)f(c) ≡ f(c + ia)f(c + jb)`, then the reduction of `f` on that coset is constant
along `a` or along `b`. -/
@[source "RW26b, Lemma 1, p. 5 (iii)"]
theorem forall_or_forall_of_separated (hvp : v (p : L) < 1) {s : ℕ} (hs : 1 ≤ s)
    (e : (Fin 2 → ZMod (p ^ s)) →+ G) (he : Function.Injective e)
    (hH : ∀ (x : G) (n : ℕ), p ^ n • x = 0 → x ∈ Set.range e) {f : G → L}
    (hf : M.IsFourierIntegral v f) (hunit : ∀ x, v (f x) = 1)
    (hinv : M.IsFourierIntegral v fun x => (f x)⁻¹) {a b : G} (ha : p • a = 0)
    (hb : p • b = 0) (hab : ∀ i j : ZMod p, i.val • a + j.val • b = 0 → i = 0 ∧ j = 0) (c : G)
    (hsep : ∀ i j : ℕ, v (f (c + i • a + j • b) * f c - f (c + i • a) * f (c + j • b)) < 1) :
    (∀ i : ℕ, v (f (c + i • a) - f c) < 1) ∨ ∀ j : ℕ, v (f (c + j • b) - f c) < 1 := by
  classical
  let H := AddCommGroup.primaryComponent G p
  let E := primaryModelEquiv e he hH
  have hcard : Nat.card H = p ^ (s * 2) := by
    simpa only [Fintype.card_fin] using primaryModelEquiv_card E
  have hnondeg : ∀ x : G, x ∈ H → (∀ h ∈ H, M.bichar x h = 1) → x = 0 :=
    fun x hx horth => M.primary_bichar_nondegenerate hcard hx horth
  obtain ⟨ζ, hζ⟩ := exists_primary_root hs M E hnondeg
  have hfreq := exists_pairing_frequency M E ζ hζ hnondeg
  have hSf (q : Fin 2 → ZMod (p ^ s)) :
      v (∑ x : Fin 2 → ZMod (p ^ s), f (c + (E x : G)) *
        ζ ^ (∑ i, (q i).val * (x i).val)) ^ 2 ≤ v (p : L) ^ (s * 2) := by
    simpa only [Fintype.card_fin] using
      M.valuation_model_fourier_sq_le v hvp E ζ hfreq hf c q
  have hSi (q : Fin 2 → ZMod (p ^ s)) :
      v (∑ x : Fin 2 → ZMod (p ^ s), (f (c + (E x : G)))⁻¹ *
        ζ ^ (∑ i, (q i).val * (x i).val)) ^ 2 ≤ v (p : L) ^ (s * 2) := by
    simpa only [Fintype.card_fin] using
      M.valuation_model_fourier_sq_le v hvp E ζ hfreq hinv c q
  exact separated_of_model M v hvp hs E ζ hζ hf hunit hinv ha hb hab c hsep hSf hSi

end MetricGroup.IsFourierIntegral

end SIC
