/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Dilogarithm.FiniteQuantum
import SICs.Dilogarithm.Valuation.FourierIntegral

/-!
# Translation by the `p`-torsion at a valuation above `p`

For a finite quantum dilogarithm `E` on a metric group whose `p`-torsion has order `p`, and a
valuation above `p`, the translation ratios `R_h(t) = E(h + t)/E(t)` by `p`-torsion elements `h`
are units congruent to `1`; in particular `v(E)` is constant on cosets of the `p`-torsion.

This module follows [RW26b, Radchenko, Wheeler (2026b), Section 4, Theorem 4 and the identity
(15) before it], for an abstract `FiniteQuantumDilog` with values in a field `L` and a valuation
`v : L → ℝ≥0` with `v(p) < 1`, written multiplicatively; the cyclic `p`-primary subgroup of the
source is the hypothesis `|G[p]| = p`. The value `E(0)` is a unit because `E(0)(E(0) - √N) = 1`,
which replaces the source's `E(0) = √ε`.

## The argument

*The Fourier identities.* Reflection gives `R_x(t) = ⟨t⟩E(x + t)E(-t) - √N E(x)δ(t)`; the
Fourier transform, the substitution `t ↦ -t`, and the product form (6) give
`R̂_x(t) + E(x) = ⟨x + t⟩E(-x - t)E(x)E(t)` for `x ≠ 0`, and reflection at `x + t` gives (15),
`R̂_x(t) = E(x)(R_x(t)⁻¹ - 1) + √N⟨x⟩⁻¹δ(t + x)`. Transforming once more (`fourier_fourier`)
gives `(E(x)/R_x)^(t) = R_x(-t) + E(x)√N δ(t) - ⟨x⟩⁻¹⟨x; t⟩`.

*Constant valuation on cosets.* Write valuations additively here, `ord = -log v`, as the source
does, and let `U = G[p]` and `w = ord ∘ E`. If `w` is not constant on some `U`-coset, let `D > 0`
be the largest difference of two of its values on a common coset, attained as
`max_t ord(R_h(t)) = D` for some `0 ≠ h ∈ U`. Since `w(h) + w(-h) = 0`, `2|w(h)| ≤ D`. Take `z`
with `ord(z) = max(-min_t ord(R_h(t)), D - w(h))` (an inverse value of `R_h`, or `R_h(t₁)/E(h)`).
Then `z·R_h` and `z·E(h)/R_h` are integral with integral Fourier transforms by the two identities,
and one of them takes a unit value. Lemma 1(i) on that function gives a coset meeting its unit
locus in more than half of its `p` points, hence two points `t, t + h`; then `w(t + 2h) - w(t)` is
`2D`, or `w(t) - w(t + 2h) = 2 ord(z) > D`, contradicting the maximality of `D`. So `w` is constant
on `U`-cosets.

*Residues.* Now `R_h` is unit-valued and `R_h`, `1/R_h` are Fourier-integral, so by Lemma 1(ii)
`R_h` is constant modulo `𝔪` on each `U`-coset, equal to some `ρ`. The telescoping product
`∏_{j<p} R_h(t + jh) = E(t + ph)/E(t) = 1` gives `ρ^p ≡ 1`, so `ρ ≡ 1`
(`valuation_sub_one_lt_one_of_pow`).
-/

open scoped NNReal

namespace SIC

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {L : Type*} [Field L]

namespace FiniteQuantumDilog

variable {M : MetricGroup G L} (E : FiniteQuantumDilog M)

/-! ### The Fourier transform of a translation ratio

The identity (15) and its Fourier transform. -/

/-- The product form (6) gives the first form of (15), used in
`fourier_translationRatio`. -/
private theorem fourier_ratio_product {x : G} (hx : x ≠ 0) (y : G) :
    M.fourier (fun t => E (x + t) / E t) y + E x =
      M.gaussian (x + y) * E (-x - y) * E x * E y := by
  have hsum : (∑ t : G, E (x + t) / E t * M.bichar t (-y)) =
      (∑ t : G, E t * M.gaussian t * E (x - t) * M.bichar t y) -
        M.sqrtCard * E x := by
    calc
      _ = ∑ t : G, (E (x + t) * M.gaussian t * E (-t) * M.bichar t (-y) -
          M.sqrtCard * (if t = 0 then 1 else 0) * E (x + t) * M.bichar t (-y)) := by
        apply Finset.sum_congr rfl
        intro t _
        rw [div_eq_mul_inv, E.inv_eq t]
        ring
      _ = (∑ t : G, E (x + t) * M.gaussian t * E (-t) * M.bichar t (-y)) -
          M.sqrtCard * E x := by
        rw [Finset.sum_sub_distrib]
        congr 1
        simp
      _ = _ := by
        congr 1
        apply Fintype.sum_equiv (Equiv.neg G)
        intro t
        simp only [Equiv.neg_apply, M.gaussian_neg, sub_neg_eq_add,
          M.bichar_neg_left, M.bichar_neg_right]
        ring
  have hp := E.product x y
  simp only [ite_eq_right hx, zero_mul, mul_zero, sub_zero] at hp
  simp only [MetricGroup.fourier, hsum]
  calc
    M.sqrtCard⁻¹ * ((∑ t, E t * M.gaussian t * E (x - t) * M.bichar t y) -
        M.sqrtCard * E x) + E x =
      M.sqrtCard⁻¹ * (∑ t, E t * M.gaussian t * E (x - t) * M.bichar t y) := by
        field_simp [M.sqrtCard_ne_zero]
        ring
    _ = _ := hp

/-- **[RW26b, Radchenko, Wheeler (2026b), Section 4, (15)]**: for `x ≠ 0` the translation ratio
`R_x(t) = E(x + t)/E(t)` has Fourier transform
`R̂_x(y) = E(x)(R_x(y)⁻¹ - 1) + √N⟨x⟩⁻¹δ(y + x)`. -/
theorem fourier_translationRatio {x : G} (hx : x ≠ 0) (y : G) :
    M.fourier (fun t => E (x + t) / E t) y =
      E x * ((E (x + y) / E y)⁻¹ - 1) +
        M.sqrtCard * (M.gaussian x)⁻¹ * (if y + x = 0 then 1 else 0) := by
  have hprod := E.fourier_ratio_product hx y
  have hi := E.inv_eq (x + y)
  have hdelta : M.sqrtCard * (if x + y = 0 then 1 else 0) * E x * E y =
      M.sqrtCard * (M.gaussian x)⁻¹ * (if y + x = 0 then 1 else 0) := by
    by_cases hxy : x + y = 0
    · have hy : y = -x := eq_neg_of_add_eq_zero_right hxy
      subst y
      simp only [add_neg_cancel, neg_add_cancel, ite_true, mul_one]
      rw [show M.sqrtCard * E x * E (-x) = M.sqrtCard * (E x * E (-x)) by ring,
        E.mul_neg_of_ne_zero hx]
    · have hyx : y + x ≠ 0 := by simpa [add_comm] using hxy
      simp [hxy, hyx]
  calc
    _ = M.gaussian (x + y) * E (-x - y) * E x * E y - E x := by
      rw [← hprod]
      ring
    _ = E x * ((E (x + y) / E y)⁻¹ - 1) +
          M.sqrtCard * (M.gaussian x)⁻¹ * (if y + x = 0 then 1 else 0) := by
      rw [eq_sub_iff_add_eq] at hi
      rw [show -x - y = -(x + y) by abel, ← hi, ← hdelta]
      field_simp [E.ne_zero y, E.ne_zero (x + y)]
      ring

/-- The Fourier transform of (15), displayed after it in [RW26b, Radchenko, Wheeler (2026b),
Section 4]: for `x ≠ 0`,
`(E(x)/R_x)^(y) = R_x(-y) + E(x)√N δ(y) - ⟨x⟩⁻¹⟨x; y⟩`. -/
theorem fourier_div_translationRatio {x : G} (hx : x ≠ 0) (y : G) :
    M.fourier (fun t => E x / (E (x + t) / E t)) y =
      E (x + -y) / E (-y) + E x * M.sqrtCard * (if y = 0 then 1 else 0) -
        (M.gaussian x)⁻¹ * M.bichar x y := by
  let R : G → L := fun t => E (x + t) / E t
  have hpoint (t : G) : E x / R t = M.fourier R t + E x -
      M.sqrtCard * (M.gaussian x)⁻¹ * (if t + x = 0 then 1 else 0) := by
    have h := E.fourier_translationRatio hx t
    dsimp [R]
    rw [div_eq_mul_inv]
    linear_combination -h
  have heq : (fun t => E x / R t) =
      (fun t => (M.fourier R t + E x) -
        M.sqrtCard * (M.gaussian x)⁻¹ * (if t + x = 0 then 1 else 0)) := by
    funext t
    exact hpoint t
  change M.fourier (fun t => E x / R t) y = _
  rw [heq, M.fourier_sub, M.fourier_add, M.fourier_fourier,
    M.fourier_constant, M.fourier_const_mul, M.fourier_delta]
  dsimp [R]
  field_simp [M.sqrtCard_ne_zero]

/-! ### Theorem 4

Valuations of the translation ratios by `p`-torsion elements. -/

variable (v : Valuation L ℝ≥0) {p : ℕ} [Fact p.Prime]

omit [Fintype G] [DecidableEq G] in
/-- A subset with more than half the points of a finite set stable under translation by `h`
contains two points separated by `h`; used in `translationRatio_unit`. -/
private theorem adjacent_of_majority (U S : Finset G) (h : G) (hSU : S ⊆ U)
    (hstable : ∀ u ∈ U, u + h ∈ U) (hcard : U.card < 2 * S.card) :
    ∃ u ∈ S, u + h ∈ S := by
  classical
  let T := S.image (· + h)
  have hTU : T ⊆ U := by
    intro u hu
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
    exact hstable a (hSU ha)
  have hTS : T.card = S.card :=
    Finset.card_image_of_injective S (fun _ _ hab => add_right_cancel hab)
  have hint : (S ∩ T).Nonempty :=
    Finset.inter_nonempty_of_card_lt_card_add_card hSU hTU (by omega)
  obtain ⟨u, hu⟩ := hint
  obtain ⟨huS, huT⟩ := Finset.mem_inter.mp hu
  obtain ⟨a, haS, rfl⟩ := Finset.mem_image.mp huT
  exact ⟨a, haS, huS⟩

/-- The first Fourier identity makes a scaled translation ratio Fourier-integral; used in
`valuation_add_of_nsmul_eq_zero`. -/
private theorem scaled_ratio_integral {x : G} (hx : x ≠ 0) (z : L)
    (hA : ∀ t, v (z * (E (x + t) / E t)) ≤ 1)
    (hB : ∀ t, v (z * E x / (E (x + t) / E t)) ≤ 1)
    (hzE : v (z * E x) ≤ 1) (hz : v z ≤ 1) :
    M.IsFourierIntegral v (fun t => z * (E (x + t) / E t)) := by
  refine ⟨hA, fun y => ?_⟩
  have hδ : v (if y + x = 0 then (1 : L) else 0) ≤ 1 := by
    split_ifs <;> simp
  have herror : v (z * M.sqrtCard * (M.gaussian x)⁻¹ *
      (if y + x = 0 then (1 : L) else 0)) ≤ 1 := by
    calc
      _ = v z * v M.sqrtCard * 1 * v (if y + x = 0 then (1 : L) else 0) := by
        simp only [map_mul, map_inv₀, M.valuation_gaussian v x, inv_one]
      _ ≤ 1 * 1 * 1 * 1 := by
        gcongr
        · exact M.valuation_sqrtCard_le_one v
      _ = 1 := by norm_num
  rw [M.fourier_const_mul, E.fourier_translationRatio hx y]
  have hform : z * (E x * ((E (x + y) / E y)⁻¹ - 1) +
      M.sqrtCard * (M.gaussian x)⁻¹ * (if y + x = 0 then 1 else 0)) =
      z * E x / (E (x + y) / E y) - z * E x +
        z * M.sqrtCard * (M.gaussian x)⁻¹ * (if y + x = 0 then 1 else 0) := by
    rw [div_eq_mul_inv]
    ring
  rw [hform]
  exact v.map_add_le (v.map_sub_le (hB y) hzE) herror

/-- The Fourier transform of (15) makes the other scaled ratio Fourier-integral; used in
`valuation_add_of_nsmul_eq_zero`. -/
private theorem scaled_div_ratio_integral {x : G} (hx : x ≠ 0) (z : L)
    (hA : ∀ t, v (z * (E (x + t) / E t)) ≤ 1)
    (hB : ∀ t, v (z * E x / (E (x + t) / E t)) ≤ 1)
    (hzE : v (z * E x) ≤ 1) (hz : v z ≤ 1) :
    M.IsFourierIntegral v (fun t => z * E x / (E (x + t) / E t)) := by
  refine ⟨hB, fun y => ?_⟩
  have hδ : v (if y = 0 then (1 : L) else 0) ≤ 1 := by
    split_ifs <;> simp
  have hmiddle : v (z * E x * M.sqrtCard * (if y = 0 then (1 : L) else 0)) ≤ 1 := by
    calc
      _ = v (z * E x) * v M.sqrtCard * v (if y = 0 then (1 : L) else 0) := by
        simp only [mul_assoc, map_mul]
      _ ≤ 1 * 1 * 1 := by
        gcongr
        · exact M.valuation_sqrtCard_le_one v
      _ = 1 := by norm_num
  have hlast : v (z * (M.gaussian x)⁻¹ * M.bichar x y) ≤ 1 := by
    calc
      _ = v z * 1 * 1 := by
        simp only [map_mul, map_inv₀, M.valuation_gaussian v x,
          M.valuation_bichar v x y, inv_one]
      _ ≤ 1 * 1 * 1 := by gcongr
      _ = 1 := by norm_num
  rw [show (fun t => z * E x / (E (x + t) / E t)) =
      (fun t => z * (E x / (E (x + t) / E t))) from by funext t; ring,
    M.fourier_const_mul, E.fourier_div_translationRatio hx y]
  have hform : z * (E (x + -y) / E (-y) + E x * M.sqrtCard *
      (if y = 0 then 1 else 0) - (M.gaussian x)⁻¹ * M.bichar x y) =
      (z * (E (x + -y) / E (-y)) +
        z * E x * M.sqrtCard * (if y = 0 then 1 else 0)) -
        z * (M.gaussian x)⁻¹ * M.bichar x y := by ring
  rw [hform]
  exact v.map_sub_le (v.map_add_le (hA (-y)) hmiddle) hlast

/-- Lemma 1(i) supplies two adjacent unit values once a Fourier-integral function has one;
used in `valuation_add_of_nsmul_eq_zero`. -/
private theorem adjacent_units (hvp : v (p : L) < 1)
    (hG : (Finset.univ.filter fun u : G => p • u = 0).card = p)
    {f : G → L} (hf : M.IsFourierIntegral v f) {h : G} (hh : p • h = 0)
    {c : G} (hc : v (f c) = 1) :
    ∃ t : G, v (f t) = 1 ∧ v (f (t + h)) = 1 := by
  let U : Finset G := Finset.univ.filter fun u => p • u = 0
  let S : Finset G := Finset.univ.filter fun u => p • u = 0 ∧ v (f (c + u)) = 1
  have hSU : S ⊆ U := by
    intro u hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2.1⟩
  have hstable : ∀ u ∈ U, u + h ∈ U := by
    intro u hu
    have huu : p • u = 0 := (Finset.mem_filter.mp hu).2
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [smul_add, huu, hh, add_zero]
  have hcard : U.card < 2 * S.card := by
    rcases hf.forall_lt_one_or_lt_two_mul_card hvp hG c with hall | hlarge
    · have h := hall 0 (by simp)
      simp only [add_zero, hc] at h
      exact (lt_irrefl 1 h).elim
    · simpa only [U, S, hG] using hlarge
  obtain ⟨u, huS, huSh⟩ := adjacent_of_majority U S h hSU hstable hcard
  refine ⟨c + u, (Finset.mem_filter.mp huS).2.2, ?_⟩
  simpa only [add_assoc] using (Finset.mem_filter.mp huSh).2.2

/-- Translation ratios multiply along two consecutive translations; used in
`valuation_add_of_nsmul_eq_zero`. -/
private theorem valuation_ratio_trans (a b c : G) :
    v (E c / E a) = v (E c / E b) * v (E b / E a) := by
  have h : E c / E a = (E c / E b) * (E b / E a) := by
    field_simp [E.ne_zero a, E.ne_zero b]
  rw [h, map_mul]

/-- Reversing a translation inverts its valuation ratio; used in
`valuation_add_of_nsmul_eq_zero`. -/
private theorem valuation_ratio_reverse (a b : G) :
    v (E a / E b) = (v (E b / E a))⁻¹ := by
  have h : E a / E b = (E b / E a)⁻¹ := by
    field_simp [E.ne_zero a, E.ne_zero b]
  rw [h, map_inv₀]

/-- Two consecutive translation ratios multiply to the ratio over the two-step translation;
used in `valuation_add_of_nsmul_eq_zero`. -/
private theorem valuation_two_step (h t : G) :
    v (E (h + (t + h)) / E t) =
      v (E (h + (t + h)) / E (t + h)) * v (E (h + t) / E t) := by
  rw [E.valuation_ratio_trans v t (h + t) (h + (t + h))]
  rw [add_comm h t]

/-- The value at zero is a unit: `v(E(0)) = 1`, since `E(0)(E(0) - √N) = 1` and `√N` is
integral. -/
theorem valuation_zero : v (E 0) = 1 := by
  have he : E 0 * (E 0 - M.sqrtCard) = 1 := by
    calc
      _ = E 0 ^ 2 - M.sqrtCard * E 0 := by ring
      _ = 1 := by rw [E.zero_sq]; ring
  have hv : v (E 0) * v (E 0 - M.sqrtCard) = 1 := by
    rw [← v.map_mul, he, map_one]
  have hs := M.valuation_sqrtCard_le_one v
  by_cases hlt : v (E 0) < 1
  · have hsub : v (E 0 - M.sqrtCard) ≤ 1 :=
      (v.map_sub _ _).trans (max_le hlt.le hs)
    have hcontra : (1 : ℝ≥0) < 1 := calc
      1 = v (E 0) * v (E 0 - M.sqrtCard) := hv.symm
      _ ≤ v (E 0) * 1 := mul_le_mul_of_nonneg_left hsub zero_le
      _ = v (E 0) := mul_one _
      _ < 1 := hlt
    exact (lt_irrefl 1 hcontra).elim
  · by_cases hgt : 1 < v (E 0)
    · have hsub : v (E 0 - M.sqrtCard) = v (E 0) :=
        v.map_sub_eq_of_lt_left (lt_of_le_of_lt hs hgt)
      rw [hsub] at hv
      have hcontra : (1 : ℝ≥0) < 1 := calc
        1 < v (E 0) * v (E 0) := one_lt_mul_of_lt_of_le hgt hgt.le
        _ = 1 := hv
      exact (lt_irrefl 1 hcontra).elim
    · exact le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)

omit [Fact p.Prime] in
/-- A nonconstant torsion translation ratio has a nonzero torsion step attaining the
least valuation, strictly below one. Used by `valuation_add_of_nsmul_eq_zero`. -/
private theorem exists_min_ratio_lt_one {u : G} (hu : p • u = 0) (t : G)
    (hnon : v (E (u + t)) ≠ v (E t)) :
    ∃ h t₀ : G, p • h = 0 ∧ h ≠ 0 ∧
      0 < v (E (h + t₀) / E t₀) ∧ v (E (h + t₀) / E t₀) < 1 ∧
      ∀ a : G, p • a = 0 → ∀ s : G,
        v (E (h + t₀) / E t₀) ≤ v (E (a + s) / E s) := by
  classical
  let U : Finset G := Finset.univ.filter fun a => p • a = 0
  let P : Finset (G × G) := U.product Finset.univ
  have hP : P.Nonempty := ⟨(0, 0), by simp [P, U]⟩
  obtain ⟨⟨h, t₀⟩, hmem, hmin⟩ := Finset.exists_min_image P
    (fun a : G × G => v (E (a.1 + a.2) / E a.2)) hP
  have hh : p • h = 0 := (Finset.mem_filter.mp (Finset.mem_product.mp hmem).1).2
  let q : ℝ≥0 := v (E (h + t₀) / E t₀)
  have hq_le (a : G) (ha : p • a = 0) (s : G) :
      q ≤ v (E (a + s) / E s) :=
    hmin (a, s) (by simp [P, U, ha])
  have hq_pos : 0 < q :=
    v.pos_iff.mpr (div_ne_zero (E.ne_zero (h + t₀)) (E.ne_zero t₀))
  have hq_lt : q < 1 := by
    rcases lt_trichotomy (v (E (u + t))) (v (E t)) with hless | heq | hgreater
    · have hratio : v (E (u + t) / E t) < 1 := by
        rw [map_div₀]
        exact (div_lt_one₀ (v.pos_iff.mpr (E.ne_zero t))).2 hless
      exact (hq_le u hu t).trans_lt hratio
    · exact (hnon heq).elim
    · have hnu : p • (-u) = 0 := by simp [hu]
      have hratio : v (E t / E (u + t)) < 1 := by
        rw [map_div₀]
        exact (div_lt_one₀ (v.pos_iff.mpr (E.ne_zero (u + t)))).2 hgreater
      have hq := hq_le (-u) hnu (u + t)
      have heq : -u + (u + t) = t := by abel
      rw [heq] at hq
      exact hq.trans_lt hratio
  have hne : h ≠ 0 := by
    intro heq
    subst h
    have hqone : q = 1 := by simp [q, E.ne_zero t₀]
    exact (ne_of_lt hq_lt) hqone
  exact ⟨h, t₀, hh, hne, hq_pos, hq_lt, hq_le⟩

/-- Adjacent unit values of the inverse scaled ratio force the least ratio to be
smaller than itself. Used by `valuation_add_of_nsmul_eq_zero`. -/
private theorem low_ratio_impossible (hvp : v (p : L) < 1)
    (hG : (Finset.univ.filter fun u : G => p • u = 0).card = p)
    {h : G} (hh : p • h = 0) (q : ℝ≥0) (hq_pos : 0 < q) (hq_lt : q < 1)
    (hq_le : ∀ a : G, p • a = 0 → ∀ s : G,
      q ≤ v (E (a + s) / E s)) (z : L) (t₀ : G)
    (hfiB : M.IsFourierIntegral v
      (fun s => z * E h / (E (h + s) / E s)))
    (hzu : v (z * E h / (E (h + t₀) / E t₀)) = 1)
    (hzeq : v (z * E h) = q) : False := by
  let R : G → L := fun s => E (h + s) / E s
  obtain ⟨s, hs, hsh⟩ := adjacent_units v hvp hG hfiB hh hzu
  have hunit_eq (s : G) (hs : v (z * E h / R s) = 1) : v (R s) = q := by
    rw [map_div₀, hzeq] at hs
    exact ((div_eq_one_iff_eq (v.pos_iff.mpr
      (div_ne_zero (E.ne_zero (h + s)) (E.ne_zero s))).ne').mp hs).symm
  have htwo : p • (2 • h) = 0 := by rw [smul_comm p 2, hh, smul_zero]
  have hbound := hq_le (2 • h) htwo s
  have harg : (2 : ℕ) • h + s = h + (s + h) := by rw [two_nsmul]; abel
  rw [harg, E.valuation_two_step v h s, hunit_eq s hs,
    hunit_eq (s + h) hsh] at hbound
  have hsmall : q * q < q := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right hq_lt hq_pos
  exact (not_lt_of_ge hbound hsmall).elim

/-- Adjacent unit values of the direct scaled ratio contradict the lower bound for the
inverse two-step ratio. Used by `valuation_add_of_nsmul_eq_zero`. -/
private theorem high_ratio_impossible (hvp : v (p : L) < 1)
    (hG : (Finset.univ.filter fun u : G => p • u = 0).card = p)
    {h : G} (hh : p • h = 0) (q a : ℝ≥0) (ha_pos : 0 < a)
    (hza_sq_lt : a⁻¹ * a⁻¹ < q)
    (hq_le : ∀ b : G, p • b = 0 → ∀ s : G,
      q ≤ v (E (b + s) / E s)) (z : L) (tmax : G)
    (hfiA : M.IsFourierIntegral v (fun s => z * (E (h + s) / E s)))
    (hzu : v (z * (E (h + tmax) / E tmax)) = 1)
    (hzval : v z = a⁻¹) : False := by
  let R : G → L := fun s => E (h + s) / E s
  obtain ⟨s, hs, hsh⟩ := adjacent_units v hvp hG hfiA hh hzu
  have hunit_eq (s : G) (hs : v (z * R s) = 1) : v (R s) = a := by
    have hmul : a⁻¹ * v (R s) = a⁻¹ * a := by
      calc
        _ = 1 := by simpa only [map_mul, hzval] using hs
        _ = a⁻¹ * a := (inv_mul_cancel₀ ha_pos.ne').symm
    exact mul_left_cancel₀ (inv_ne_zero ha_pos.ne') hmul
  have htwo : p • (-(2 • h)) = 0 := by
    rw [smul_neg, smul_comm p 2, hh, smul_zero, neg_zero]
  have hbound := hq_le (-(2 • h)) htwo (h + (s + h))
  have harg : -(2 • h) + (h + (s + h)) = s := by rw [two_nsmul]; abel
  rw [harg, E.valuation_ratio_reverse v s (h + (s + h)),
    E.valuation_two_step v h s, hunit_eq s hs,
    hunit_eq (s + h) hsh] at hbound
  have hpow : (a * a)⁻¹ = a⁻¹ * a⁻¹ := by rw [mul_inv_rev]
  rw [hpow] at hbound
  exact (not_lt_of_ge hbound hza_sq_lt).elim

omit [Fact p.Prime] in
/-- Reflection and two torsion steps bound the least ratio by `v(E(h))` and its square.
Used by `valuation_add_of_nsmul_eq_zero`. -/
private theorem ratio_parameter_bounds {h : G} (hne : h ≠ 0) (hh : p • h = 0)
    (q : ℝ≥0) (hq_le : ∀ a : G, p • a = 0 → ∀ s : G,
      q ≤ v (E (a + s) / E s)) :
    0 < v (E h) ∧ q ≤ v (E h) ∧ q ≤ v (E h) * v (E h) := by
  let e : ℝ≥0 := v (E h)
  have he_pos : 0 < e := v.pos_iff.mpr (E.ne_zero h)
  have hrefl : e * v (E (-h)) = 1 := by
    dsimp [e]
    rw [← v.map_mul, E.mul_neg_of_ne_zero hne, map_inv₀,
      M.valuation_gaussian v h, inv_one]
  have hnegval : v (E (-h)) = e⁻¹ := eq_inv_of_mul_eq_one_right hrefl
  have hqe : q ≤ e := by
    have hbound := hq_le h hh (-h)
    simpa only [add_neg_cancel, map_div₀, E.valuation_zero v, hnegval,
      one_div, inv_inv] using hbound
  have hqe2 : q ≤ e * e := by
    have htwo : p • (2 • h) = 0 := by rw [smul_comm p 2, hh, smul_zero]
    have hbound := hq_le (2 • h) htwo (-h)
    have harg : (2 : ℕ) • h + -h = h := by rw [two_nsmul]; abel
    rw [harg, map_div₀, hnegval] at hbound
    simpa only [e, div_inv_eq_mul] using hbound
  exact ⟨he_pos, hqe, hqe2⟩

omit [Fact p.Prime] in
/-- The extremal direct ratio and the least ratio yield scaled Fourier-integral functions
with a unit value in one of the two choices. Used by `valuation_add_of_nsmul_eq_zero`. -/
private theorem exists_scaled_ratios {h : G} (hne : h ≠ 0)
    (t₀ : G) (q e : ℝ≥0) (hq : q = v (E (h + t₀) / E t₀))
    (he : e = v (E h)) (he_pos : 0 < e)
    (hqe : q ≤ e) (hq_lt : q < 1)
    (hq_le : ∀ s : G, q ≤ v (E (h + s) / E s)) :
    ∃ (tmax : G) (a : ℝ≥0) (z : L),
      a = v (E (h + tmax) / E tmax) ∧ 0 < a ∧
      (∀ s : G, v (E (h + s) / E s) ≤ a) ∧
      z = (if q / e ≤ a⁻¹ then (E (h + t₀) / E t₀) / E h
        else (E (h + tmax) / E tmax)⁻¹) ∧
      v z = (if q / e ≤ a⁻¹ then q / e else a⁻¹) ∧
      M.IsFourierIntegral v (fun s => z * (E (h + s) / E s)) ∧
      M.IsFourierIntegral v (fun s => z * E h / (E (h + s) / E s)) := by
  classical
  let R : G → L := fun s => E (h + s) / E s
  obtain ⟨tmax, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun s : G => v (R s)) Finset.univ_nonempty
  let a : ℝ≥0 := v (R tmax)
  have ha_pos : 0 < a := v.pos_iff.mpr
    (div_ne_zero (E.ne_zero (h + tmax)) (E.ne_zero tmax))
  have ha_bound (s : G) : v (R s) ≤ a := hmax s (Finset.mem_univ s)
  let z : L := if q / e ≤ a⁻¹ then R t₀ / E h else (R tmax)⁻¹
  have hzval : v z = if q / e ≤ a⁻¹ then q / e else a⁻¹ := by
    dsimp [z]
    split_ifs with hc
    · rw [map_div₀, ← he, ← hq]
    · simp only [map_inv₀, a, R]
  have hz_bounds : v z ≤ q / e ∧ v z ≤ a⁻¹ := by
    by_cases hc : q / e ≤ a⁻¹
    · rw [hzval, ite_eq_left hc]
      exact ⟨le_rfl, hc⟩
    · rw [hzval, ite_eq_right hc]
      exact ⟨le_of_lt (lt_of_not_ge hc), le_rfl⟩
  have hz_le : v z ≤ 1 := hz_bounds.1.trans ((div_le_one₀ he_pos).2 hqe)
  have hzE_le_q : v (z * E h) ≤ q := by
    rw [map_mul, ← he]
    calc
      v z * e ≤ (q / e) * e :=
        mul_le_mul_of_nonneg_right hz_bounds.1 zero_le
      _ = q := div_mul_cancel₀ q he_pos.ne'
  have hA (s : G) : v (z * R s) ≤ 1 := by
    rw [map_mul]
    calc
      v z * v (R s) ≤ a⁻¹ * a := mul_le_mul' hz_bounds.2 (ha_bound s)
      _ = 1 := inv_mul_cancel₀ ha_pos.ne'
  have hB (s : G) : v (z * E h / R s) ≤ 1 := by
    rw [map_div₀]
    apply (div_le_one₀ (v.pos_iff.mpr
      (div_ne_zero (E.ne_zero (h + s)) (E.ne_zero s)))).2
    exact hzE_le_q.trans (hq_le s)
  have hfiA : M.IsFourierIntegral v (fun s => z * R s) :=
    E.scaled_ratio_integral v hne z hA hB (hzE_le_q.trans hq_lt.le) hz_le
  have hfiB : M.IsFourierIntegral v (fun s => z * E h / R s) :=
    E.scaled_div_ratio_integral v hne z hA hB (hzE_le_q.trans hq_lt.le) hz_le
  exact ⟨tmax, a, z, rfl, ha_pos, ha_bound, rfl, hzval, hfiA, hfiB⟩

/-- The valuation of `E` is constant on cosets of `G[p]`, the first part of the proof of
`translationRatio_unit` in [RW26b, Radchenko, Wheeler (2026b), Section 4, Theorem 4]. -/
theorem valuation_add_of_nsmul_eq_zero (hvp : v (p : L) < 1)
    (hG : (Finset.univ.filter fun u : G => p • u = 0).card = p)
    {u : G} (hu : p • u = 0) (t : G) : v (E (u + t)) = v (E t) := by
  classical
  by_contra hnon
  obtain ⟨h, t₀, hh, hne, hq_pos', hq_lt', hq_le'⟩ :=
    E.exists_min_ratio_lt_one v hu t hnon
  let q : ℝ≥0 := v (E (h + t₀) / E t₀)
  have hq_pos : 0 < q := hq_pos'
  have hq_lt : q < 1 := hq_lt'
  have hq_le (a : G) (ha : p • a = 0) (s : G) :
      q ≤ v (E (a + s) / E s) := hq_le' a ha s
  let e : ℝ≥0 := v (E h)
  obtain ⟨he_pos, hqe, hqe2⟩ := E.ratio_parameter_bounds v hne hh q hq_le
  let R : G → L := fun s => E (h + s) / E s
  obtain ⟨tmax, a, z, ha_def, ha_pos, ha_bound, hz_def, hzval, hfiA, hfiB⟩ :=
    E.exists_scaled_ratios v hne t₀ q e rfl rfl he_pos hqe hq_lt (hq_le h hh)
  by_cases hc : q / e ≤ a⁻¹
  · have hzu : v (z * E h / R t₀) = 1 := by
      have heq : z * E h / R t₀ = 1 := by
        simp only [hz_def, ite_eq_left hc, R]
        field_simp [E.ne_zero h, E.ne_zero (h + t₀), E.ne_zero t₀]
      rw [heq, map_one]
    have hzeq : v (z * E h) = q := by
      have heq : z * E h = R t₀ := by
        simp only [hz_def, ite_eq_left hc, R]
        field_simp [E.ne_zero h]
      rw [heq]
    exact E.low_ratio_impossible v hvp hG hh q hq_pos hq_lt hq_le z t₀ hfiB hzu hzeq
  · have hzu : v (z * R tmax) = 1 := by
      have heq : z * R tmax = 1 := by
        simp only [hz_def, ite_eq_right hc, R]
        exact inv_mul_cancel₀ (div_ne_zero (E.ne_zero (h + tmax)) (E.ne_zero tmax))
      rw [heq, map_one]
    have hzval' : v z = a⁻¹ := by rw [hzval, ite_eq_right hc]
    have hza_lt : a⁻¹ < q / e := lt_of_not_ge hc
    have hza_le_e : q / e ≤ e := (div_le_iff₀ he_pos).2 hqe2
    have hza_pos : 0 < a⁻¹ := inv_pos.mpr ha_pos
    have hza_sq_lt : a⁻¹ * a⁻¹ < q :=
      (mul_lt_mul_of_pos_left (hza_lt.trans_le hza_le_e) hza_pos).trans
        ((lt_div_iff₀ he_pos).mp hza_lt)
    exact E.high_ratio_impossible v hvp hG hh q a ha_pos hza_sq_lt hq_le
      z tmax hfiA hzu hzval'

omit [Fact p.Prime] in
/-- A unit-valued translation ratio `R_h(t) = E(h+t)/E(t)` and its reciprocal are
Fourier-integral. Used by `translation_ratio_residue` and
`translation_invariant_of_summands`. -/
theorem translationRatio_fourierIntegral
    {h : G} (hzero : h ≠ 0) (hunit : ∀ s, v (E (h + s) / E s) = 1) :
    M.IsFourierIntegral v (fun s => E (h + s) / E s) ∧
      M.IsFourierIntegral v (fun s => (E (h + s) / E s)⁻¹) := by
  let R : G → L := fun s => E (h + s) / E s
  have hEunit : v (E h) = 1 := by
    simpa only [add_zero, map_div₀, E.valuation_zero v, div_one] using hunit 0
  have hunit (s : G) : v (R s) = 1 := hunit s
  have hA (s : G) : v ((1 : L) * R s) ≤ 1 := by
    rw [one_mul, hunit s]
  have hB (s : G) : v ((1 : L) * E h / R s) ≤ 1 := by
    simp only [one_mul]
    rw [map_div₀, hEunit, hunit s]
    norm_num
  have hfiR : M.IsFourierIntegral v R := by
    simpa only [one_mul] using
      (E.scaled_ratio_integral v hzero (1 : L) hA hB (by simp [hEunit]) (by simp))
  have hA' (s : G) : v ((E h)⁻¹ * R s) ≤ 1 := by
    rw [map_mul, map_inv₀, hEunit, hunit s]
    norm_num
  have hB' (s : G) : v ((E h)⁻¹ * E h / R s) ≤ 1 := by
    rw [inv_mul_cancel₀ (E.ne_zero h), one_div, map_inv₀, hunit s]
    norm_num
  have hzE' : v ((E h)⁻¹ * E h) ≤ 1 := by simp [E.ne_zero h]
  have hz' : v ((E h)⁻¹) ≤ 1 := by rw [map_inv₀, hEunit]; norm_num
  have hfiInv : M.IsFourierIntegral v (fun s => (R s)⁻¹) := by
    have hf := E.scaled_div_ratio_integral v hzero (E h)⁻¹ hA' hB' hzE' hz'
    have heq : (fun s => (E h)⁻¹ * E h / R s) = (fun s => (R s)⁻¹) := by
      funext s
      rw [inv_mul_cancel₀ (E.ne_zero h), one_div]
    rw [heq] at hf
    exact hf
  exact ⟨hfiR, hfiInv⟩

/-- The residue of each unit translation ratio is one, the second part of the proof of
`translationRatio_unit` in [RW26b, Radchenko, Wheeler (2026b), Section 4, Theorem 4]. -/
private theorem translation_ratio_residue (hvp : v (p : L) < 1)
    (hG : (Finset.univ.filter fun u : G => p • u = 0).card = p)
    (hconst : ∀ (a : G), p • a = 0 → ∀ s, v (E (a + s)) = v (E s))
    {h : G} (hh : p • h = 0) (t : G) :
    v (E (h + t) / E t - 1) < 1 := by
  by_cases hzero : h = 0
  · subst h
    simp [E.ne_zero t]
  let R : G → L := fun s => E (h + s) / E s
  have hunit (s : G) : v (R s) = 1 := by
    dsimp [R]
    rw [map_div₀, hconst h hh s, div_self (v.pos_iff.mpr (E.ne_zero s)).ne']
  obtain ⟨hfiR, hfiInv⟩ :=
    E.translationRatio_fourierIntegral v hzero hunit
  have hcong (j : ℕ) : v (R (t + j • h) - R t) < 1 := by
    have hj : p • (j • h) = 0 := by rw [smul_comm p j, hh, smul_zero]
    exact hfiR.valuation_sub_lt_one hvp hG hunit hfiInv t hj
  let F : ℕ → L := fun j => E (t + j • h)
  have hFne (j : ℕ) : F j ≠ 0 := E.ne_zero _
  have hterm (j : ℕ) : R (t + j • h) = F (j + 1) / F j := by
    dsimp [R, F]
    congr 1
    rw [succ_nsmul]
    abel_nf
  have hprod : (∏ j ∈ Finset.range p, R (t + j • h)) = 1 := by
    calc
      _ = ∏ j ∈ Finset.range p, F (j + 1) / F j := by
        apply Finset.prod_congr rfl
        intro j _
        exact hterm j
      _ = F p / F 0 := by
        let U : ℕ → Lˣ := fun j => Units.mk0 (F j) (hFne j)
        have h := congrArg (Units.coeHom L) (Finset.prod_range_div U p)
        simpa only [map_prod, Units.coeHom_apply, Units.val_div_eq_div_val,
          Units.val_mk0, U] using h
      _ = 1 := by simp [F, hh, E.ne_zero t]
  have hxp : v ((R t) ^ p - 1) < 1 := by
    rw [← hprod]
    simpa only [Finset.prod_const, Finset.card_range] using
      (valuation_prod_sub_prod_lt_one v (Finset.range p) (fun _ => R t)
        (fun j => R (t + j • h))
        (by intro j hj; exact (hunit t).le)
        (by intro j hj; exact (hunit _).le)
        (by intro j hj; simpa only [v.map_sub_swap] using hcong j))
  exact valuation_sub_one_lt_one_of_pow v hvp (hunit t).le hxp

/-- **[RW26b, Radchenko, Wheeler (2026b), Section 4, Theorem 4] (cyclic translation)**: if
`|G[p]| = p` and `v(p) < 1`, then for every `h` with `p • h = 0` the translation ratios
`R_h(t) = E(h + t)/E(t)` are units congruent to `1` modulo `𝔪`. -/
@[source "RW26b, Theorem 4, p. 7"]
theorem translationRatio_unit (hvp : v (p : L) < 1)
    (hG : (Finset.univ.filter fun u : G => p • u = 0).card = p) {h : G} (hh : p • h = 0)
    (t : G) : v (E (h + t) / E t) = 1 ∧ v (E (h + t) / E t - 1) < 1 := by
  have hconst (u : G) (hu : p • u = 0) (s : G) : v (E (u + s)) = v (E s) :=
    E.valuation_add_of_nsmul_eq_zero v hvp hG hu s
  constructor
  · rw [map_div₀, hconst h hh t, div_self (v.pos_iff.mpr (E.ne_zero t)).ne']
  · exact E.translation_ratio_residue v hvp hG hconst hh t

end FiniteQuantumDilog

end SIC
