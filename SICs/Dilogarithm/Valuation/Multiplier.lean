/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Dilogarithm.FiniteQuantum
import SICs.Dilogarithm.Valuation.FourierIntegral
import Mathlib.GroupTheory.Complement

/-!
# The Fourier multiplier is a unit at every valuation

The normalized Gauss sum `γ = s⁻¹ ∑_x ⟨x⟩⁻¹` of a metric group is a unit at every valuation
`v` with `v(p) < 1` for a prime `p`; hence so is the multiplier `λ` of a finite quantum
dilogarithm, and `E`, `E⁻¹` are Fourier-integral when the values of `E` are units.

This module supplies the integrality of `Ê = λ⟨·⟩E` and of `(E⁻¹)^ = λ⁻¹E - 1` used in
[RW26b, Radchenko, Wheeler (2026b), Section 7, proof of Theorem 7]. The source takes
`λ = μ_γ`, a root of unity, from the Fourier relation [RW26, Radchenko, Wheeler (2026),
Theorem 2, `thm:fg.equs`, (6), `eq:Fgpm.fourier`], which the project does not formalize.
Here `λ³ = γ` (`FiniteQuantumDilog.multiplier_pow_three`),
and `γ` is a unit at `v`: this is the valuation shadow of Milgram's formula `γ = e(σ/8)`
(J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Springer, 1973, Appendix 4), proved
directly below.

## The argument

*The Gauss sum.* Let `P = G[p^∞]` and `Q` the complementary subgroup of elements of order prime
to `p`, so `G = P ⊕ Q` and `⟨u; w⟩ = 1` for `u ∈ P`, `w ∈ Q` (the orders are coprime). Then
`⟨u + w⟩ = ⟨u⟩⟨w⟩`, the bicharacter is nondegenerate on `P` and on `Q`, and the sums
`S_H = ∑_{x∈H}⟨x⟩` and `S'_H = ∑_{x∈H}⟨x⟩⁻¹` factor: `S'_G = S'_P S'_Q`. By
`MetricGroup.sum_gaussian_inv_mul_sum_gaussian`, `S'_H S_H = |H|`. On `Q`, both sums are integral
and their product `|Q|` is prime to `p`, so `v(S'_Q) = 1`. On `P`, the Gaussian values are
`p`-power roots of unity (`⟨x⟩^{2 p^n} = 1` when `p^n x = 0`, and `⟨x⟩^{p^n} = 1` for odd `p`),
so `v(S'_P) = v(S_P)` (`valuation_sum_inv_eq`) and `v(S'_P)² = v(|P|)`. Hence
`v(γ)² = v(|P|)/v(|G|) = v(|Q|)⁻¹ = 1`.

*The multiplier.* `v(λ)³ = v(γ) = 1`.

*Fourier integrality.* `Ê = λ⟨·⟩E` (`FiniteQuantumDilog.fourier_eq`). Writing
`E(x)⁻¹ = ⟨x⟩E(-x) - √N δ(x)` (`FiniteQuantumDilog.inv_eq`) and transforming, with
`(⟨·⟩E)^ = λ⁻¹E(-·)` from Fourier inversion, gives `(E⁻¹)^ = λ⁻¹E - 1`.
-/

open scoped NNReal

namespace SIC

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {L : Type*} [Field L]

/-! ### The Gauss sum

The Gauss sum factors over the `p`-primary part and its complement. -/

namespace MetricGroup

variable (M : MetricGroup G L) (v : Valuation L ℝ≥0)

omit [DecidableEq G] in
/-- The Gaussian on a multiple satisfies `⟨n x⟩ = ⟨x⟩^{n²}`. Used by
`valuation_gaussSum` to put Gaussian values on the primary part in a cyclotomic group. -/
private theorem gaussian_nsmul_pow_sq (n : ℕ) (x : G) :
    M.gaussian (n • x) = M.gaussian x ^ (n * n) := by
  have hb : M.bichar x x = M.gaussian x ^ 2 := by
    have h := M.gaussian_add x (-x)
    rw [add_neg_cancel, M.gaussian_zero, M.gaussian_neg, M.bichar_neg_right] at h
    field_simp [M.bichar_ne_zero x x] at h
    simpa only [pow_two] using h
  induction n with
  | zero => simp
  | succ n ih =>
      rw [succ_nsmul, M.gaussian_add, ih, M.bichar_nsmul_left, hb]
      have he : (n + 1) * (n + 1) = n * n + 1 + 2 * n := by ring
      rw [he, pow_add, pow_add, pow_mul]
      ring

omit [DecidableEq G] in
/-- Coprime subgroup orders make the primary part orthogonal to its complement.
Used by `valuation_gaussSum`. -/
private theorem bichar_primary_orthogonal {p s : ℕ} {P Q : AddSubgroup G}
    (hPcard : Nat.card P = p ^ s)
    (hPkill : ∀ x : P, p ^ s • (x : G) = 0)
    (hcop : (Nat.card P).Coprime (Nat.card Q))
    (u : P) (w : Q) : M.bichar (u : G) (w : G) = 1 := by
  classical
  have hu : M.bichar (u : G) (w : G) ^ (p ^ s) = 1 := by
    rw [← M.bichar_nsmul_left, hPkill u, M.bichar_zero_left]
  have hw : M.bichar (u : G) (w : G) ^ Nat.card Q = 1 := by
    rw [← M.bichar_nsmul_right]
    have hk := (card_nsmul_eq_zero : Fintype.card Q • w = 0)
    have hh := congrArg Subtype.val hk
    change Fintype.card Q • (w : G) = 0 at hh
    rw [Nat.card_eq_fintype_card, hh, M.bichar_zero_right]
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (hPcard ▸ hcop) (orderOf_dvd_of_pow_eq_one hu) (orderOf_dvd_of_pow_eq_one hw))

omit [DecidableEq G] in
/-- Orthogonal splitting of `G` factors its inverse Gaussian sum. Used by
`valuation_gaussSum`. -/
private theorem sum_gaussian_inv_factor {P Q : AddSubgroup G} [Fintype P] [Fintype Q]
    (e : P × Q ≃ G)
    (he : ∀ z : P × Q, e z = (z.1 : G) + (z.2 : G))
    (horth : ∀ u : P, ∀ w : Q, M.bichar (u : G) (w : G) = 1) :
    (∑ x : G, (M.gaussian x)⁻¹) =
      (∑ u : P, (M.gaussian u)⁻¹) * ∑ w : Q, (M.gaussian w)⁻¹ := by
  calc
    _ = ∑ z : P × Q, (M.gaussian ((z.1 : G) + (z.2 : G)))⁻¹ :=
      (Fintype.sum_equiv e
        (fun z => (M.gaussian ((z.1 : G) + (z.2 : G)))⁻¹)
        (fun x => (M.gaussian x)⁻¹) (fun z => by rw [he])).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      have hgaussInv (u : P) (w : Q) :
          (M.gaussian ((u : G) + (w : G)))⁻¹ =
            (M.gaussian u)⁻¹ * (M.gaussian w)⁻¹ := by
        rw [M.gaussian_add, horth]
        simp only [one_mul, mul_inv_rev, mul_comm]
      simp_rw [hgaussInv]
      exact (Finset.sum_mul_sum Finset.univ Finset.univ _ _).symm

omit [DecidableEq G] in
/-- Orthogonality and nondegeneracy on `G` give nondegeneracy on the complementary
subgroup. Used by `valuation_gaussSum`. -/
private theorem complement_nondegenerate {P Q : AddSubgroup G}
    (e : P × Q ≃ G)
    (he : ∀ z : P × Q, e z = (z.1 : G) + (z.2 : G))
    (horth : ∀ u : P, ∀ w : Q, M.bichar (u : G) (w : G) = 1) :
    ∀ y ∈ Q, (∀ x ∈ Q, M.bichar x y = 1) → y = 0 := by
  intro y hy h
  apply M.nondegenerate y
  intro z
  obtain ⟨⟨u, w⟩, rfl⟩ := e.surjective z
  rw [he]
  change M.bichar y ((u : G) + (w : G)) = 1
  rw [M.bichar_add_right, M.bichar_comm y u, horth u ⟨y, hy⟩,
    M.bichar_comm y w, h w w.property, one_mul]

omit [DecidableEq G] in
/-- On the prime-to-`p` part, the inverse Gaussian sum has valuation one.
Used by `valuation_gaussSum`. -/
private theorem valuation_complement_sum {Q : AddSubgroup G} [Fintype Q]
    (hQnondeg : ∀ y ∈ Q, (∀ x ∈ Q, M.bichar x y = 1) → y = 0)
    (hQnatunit : v (Nat.card Q : L) = 1) :
    v (∑ w : Q, (M.gaussian w)⁻¹) = 1 := by
  have hQprod := M.sum_gaussian_inv_mul_sum_gaussian Q hQnondeg
  have hQprod' : (∑ w : Q, (M.gaussian w)⁻¹) *
      ∑ w : Q, M.gaussian w = (Nat.card Q : L) := by
    convert hQprod using 1
    congr 1 <;> apply Finset.sum_congr (Finset.ext (by simp)) <;> simp
  have hA : v (∑ w : Q, (M.gaussian w)⁻¹) ≤ 1 := by
    apply v.map_sum_le
    intro w _
    rw [map_inv₀, M.valuation_gaussian v, inv_one]
  have hB : v (∑ w : Q, M.gaussian w) ≤ 1 := by
    apply v.map_sum_le
    intro w _
    rw [M.valuation_gaussian v]
  have hAB : v (∑ w : Q, (M.gaussian w)⁻¹) *
      v (∑ w : Q, M.gaussian w) = 1 := by
    calc
      _ = v ((∑ w : Q, (M.gaussian w)⁻¹) * ∑ w : Q, M.gaussian w) :=
        (map_mul v _ _).symm
      _ = v (Nat.card Q : L) := congrArg v hQprod'
      _ = 1 := hQnatunit
  apply le_antisymm hA
  calc
    1 = v (∑ w : Q, (M.gaussian w)⁻¹) *
        v (∑ w : Q, M.gaussian w) := hAB.symm
    _ ≤ v (∑ w : Q, (M.gaussian w)⁻¹) * 1 :=
      mul_le_mul_of_nonneg_left hB bot_le
    _ = _ := mul_one _

omit [DecidableEq G] in
/-- The inverse Gaussian sum on the `p`-primary part has square valuation
`v(|P|)`. Used by `valuation_gaussSum`. -/
private theorem valuation_primary_sum_sq {p s : ℕ} [Fact p.Prime]
    {P : AddSubgroup G} [Fintype P] (hvp : v (p : L) < 1)
    (hPkill : ∀ x : P, p ^ s • (x : G) = 0)
    (hPnondeg : ∀ y ∈ P, (∀ x ∈ P, M.bichar x y = 1) → y = 0) :
    v (∑ u : P, (M.gaussian u)⁻¹) ^ 2 = v (Nat.card P : L) := by
  have hPprod := M.sum_gaussian_inv_mul_sum_gaussian P hPnondeg
  have hPprod' : (∑ u : P, (M.gaussian u)⁻¹) *
      ∑ u : P, M.gaussian u = (Nat.card P : L) := by
    convert hPprod using 1
    congr 1 <;> apply Finset.sum_congr (Finset.ext (by simp)) <;> simp
  have hPconj : v (∑ u : P, (M.gaussian u)⁻¹) =
      v (∑ u : P, M.gaussian u) := by
    have hpower (u : P) : M.gaussian (u : G) ^ p ^ (s + s) = 1 := by
      have hu := M.gaussian_nsmul_pow_sq (p ^ s) (u : G)
      rw [hPkill u, M.gaussian_zero] at hu
      simpa only [pow_add] using hu.symm
    simpa using
      valuation_sum_inv_eq v hvp Finset.univ (fun u : P => M.gaussian u)
        (fun u _ => hpower u)
  have h := congrArg v hPprod'
  rw [map_mul] at h
  simpa only [hPconj, pow_two] using h

omit [DecidableEq G] in
/-- Orthogonal factorization and the two subgroup valuations make the normalized Gauss sum
integral and invertible. Used by `valuation_gaussSum`. -/
private theorem valuation_gaussSum_of_split {p s : ℕ} [Fact p.Prime]
    (hvp : v (p : L) < 1) (Q : AddSubgroup G)
    (hPcard : Nat.card (AddCommGroup.primaryComponent G p) = p ^ s)
    (hPkill : ∀ x : AddCommGroup.primaryComponent G p, p ^ s • (x : G) = 0)
    (hQcard : Nat.card Q = (AddCommGroup.primaryComponent G p).index)
    (hprod : Nat.card (AddCommGroup.primaryComponent G p) * Nat.card Q = Nat.card G)
    (e : AddCommGroup.primaryComponent G p × Q ≃ G)
    (he : ∀ z, e z = (z.1 : G) + (z.2 : G))
    (horth : ∀ u : AddCommGroup.primaryComponent G p, ∀ w : Q,
      M.bichar (u : G) (w : G) = 1) : v M.gaussSum = 1 := by
  classical
  let P := AddCommGroup.primaryComponent G p
  have hfactorInv := M.sum_gaussian_inv_factor e he horth
  have hPnondeg : ∀ y ∈ P, (∀ x ∈ P, M.bichar x y = 1) → y = 0 := by
    intro y hy h
    apply M.primary_bichar_nondegenerate hPcard hy
    intro x hx
    rw [M.bichar_comm]
    exact h x hx
  have hQnondeg := M.complement_nondegenerate e he horth
  have hQnatunit : v (Nat.card Q : L) = 1 := by
    apply valuation_natCast_eq_one v hvp
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp
      (by simpa only [hQcard] using primaryComponent_index_coprime (A := G) (p := p))
  have hQunit := M.valuation_complement_sum v hQnondeg hQnatunit
  have hPval := M.valuation_primary_sum_sq v hvp hPkill hPnondeg
  have hsval : (v M.sqrtCard) ^ 2 =
      v (∑ u : P, (M.gaussian u)⁻¹) ^ 2 := by
    calc
      _ = v (M.sqrtCard ^ 2) := (map_pow v _ _).symm
      _ = v (Fintype.card G : L) := by rw [M.sqrtCard_sq]
      _ = v (Nat.card P : L) * v (Nat.card Q : L) := by
        rw [← Nat.card_eq_fintype_card, ← hprod, Nat.cast_mul, map_mul]
      _ = _ := by
        rw [hQnatunit, mul_one, ← hPval]
  have hsumval : v (∑ x : G, (M.gaussian x)⁻¹) = v M.sqrtCard := by
    rw [hfactorInv, map_mul, hQunit, mul_one]
    exact (sq_eq_sq₀ bot_le bot_le).mp hsval.symm
  unfold gaussSum
  rw [map_mul, map_inv₀, hsumval]
  exact inv_mul_cancel₀ ((map_ne_zero v).mpr M.sqrtCard_ne_zero)

omit [Fintype G] [DecidableEq G] in
/-- The order of the `p`-primary subgroup is a power of `p`. Used by
`valuation_gaussSum` to choose the exponent in the orthogonal splitting. -/
private theorem primary_card_pow [Finite G] {p : ℕ} [Fact p.Prime] :
    ∃ s : ℕ, Nat.card (AddCommGroup.primaryComponent G p) = p ^ s := by
  classical
  let P := AddCommGroup.primaryComponent G p
  have hpGroup : IsPGroup p (Multiplicative P) := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro x
    obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp x.toAdd.property
    refine ⟨k, ?_⟩
    change (p ^ k • (x.toAdd : P)) = 0
    exact Subtype.ext hk
  obtain ⟨s, hs⟩ := IsPGroup.iff_card.mp hpGroup
  exact ⟨s, (Nat.card_congr (Equiv.refl P : Multiplicative P ≃ P)).symm.trans hs⟩

omit [DecidableEq G] in
/-- The `p`-primary part has an orthogonal complement with addition equivalence
`P × Q ≃ G`. Used with `sum_gaussian_inv_factor` by `valuation_gaussSum`. -/
private theorem primary_orthogonal_split {p s : ℕ} [Fact p.Prime]
    (P : AddSubgroup G) (hP : P = AddCommGroup.primaryComponent G p)
    (hPcard : Nat.card P = p ^ s) :
    ∃ Q : AddSubgroup G, ∃ e : P × Q ≃ G,
      (∀ x : P, p ^ s • (x : G) = 0) ∧
      Nat.card Q = P.index ∧ Nat.card P * Nat.card Q = Nat.card G ∧
      (∀ z : P × Q, e z = (z.1 : G) + (z.2 : G)) ∧
      ∀ u : P, ∀ w : Q, M.bichar (u : G) (w : G) = 1 := by
  classical
  subst P
  let P := AddCommGroup.primaryComponent G p
  let f : G →+ G := nsmulAddMonoidHom (p ^ s)
  let Q : AddSubgroup G := f.range
  have hPkill (x : P) : p ^ s • (x : G) = 0 := by
    have h := (card_nsmul_eq_zero : Fintype.card P • x = 0)
    have hh := congrArg Subtype.val h
    change Fintype.card P • (x : G) = 0 at hh
    rwa [← Nat.card_eq_fintype_card, hPcard] at hh
  have hker : f.ker = P := by
    ext x
    constructor
    · intro hx
      apply AddCommGroup.mem_primaryComponent.mpr
      exact ⟨s, hx⟩
    · intro hx
      exact hPkill ⟨x, hx⟩
  have hQcard : Nat.card Q = P.index := by
    rw [← AddSubgroup.index_ker f, hker]
  have hcop : (Nat.card P).Coprime (Nat.card Q) := by
    rw [hPcard, hQcard]
    exact (primaryComponent_index_coprime (A := G) (p := p)).pow_left s
  have hprod : Nat.card P * Nat.card Q = Nat.card G := by
    rw [hQcard]
    exact P.card_mul_index
  have hdisj : Disjoint P Q := AddSubgroup.disjoint_of_coprime_natCard hcop
  let e : P × Q ≃ G := Equiv.ofBijective
    (fun z : P × Q => (z.1 : G) + (z.2 : G))
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨AddSubgroup.add_injective_of_disjoint hdisj,
        (Nat.card_prod P Q).trans hprod⟩)
  have he (z : P × Q) : e z = (z.1 : G) + (z.2 : G) := rfl
  have horth (u : P) (w : Q) : M.bichar (u : G) (w : G) = 1 :=
    M.bichar_primary_orthogonal hPcard hPkill hcop u w
  exact ⟨Q, e, hPkill, hQcard, hprod, he, horth⟩

omit [DecidableEq G] in
/-- **The normalized Gauss sum is a unit**: `v(γ) = 1` for `γ = s⁻¹ ∑_x ⟨x⟩⁻¹` at every valuation
with `v(p) < 1` for a prime `p`. A consequence of Milgram's formula `γ = e(σ/8)`; used for the
multiplier of [RW26b, Radchenko, Wheeler (2026b), Section 7, proof of Theorem 7]. -/
theorem valuation_gaussSum {p : ℕ} [Fact p.Prime] (hvp : v (p : L) < 1) :
    v M.gaussSum = 1 := by
  classical
  let P := AddCommGroup.primaryComponent G p
  obtain ⟨s, hPcard⟩ := primary_card_pow (G := G) (p := p)
  obtain ⟨Q, e, hPkill, hQcard, hprod, he, horth⟩ :=
    M.primary_orthogonal_split P rfl hPcard
  exact M.valuation_gaussSum_of_split v hvp Q hPcard hPkill hQcard hprod e he horth

end MetricGroup

/-! ### The multiplier and Fourier integrality

`λ` is a unit, and `E`, `E⁻¹` are Fourier-integral when `E` takes unit values. -/

namespace FiniteQuantumDilog

variable {M : MetricGroup G L} (E : FiniteQuantumDilog M) (v : Valuation L ℝ≥0)

/-- **The multiplier is a unit**: `v(λ) = 1`, from `λ³ = γ` and `MetricGroup.valuation_gaussSum`.
[RW26b, Radchenko, Wheeler (2026b), Proposition 1] has `λ = μ_γ`, a root of unity. -/
theorem valuation_multiplier {p : ℕ} [Fact p.Prime] (hvp : v (p : L) < 1) :
    v E.multiplier = 1 := by
  apply (pow_eq_one_iff_of_nonneg (show 0 ≤ v E.multiplier from bot_le)
    (by decide : 3 ≠ 0)).mp
  calc
    (v E.multiplier) ^ 3 = v (E.multiplier ^ 3) := (map_pow v _ _).symm
    _ = v M.gaussSum := by rw [E.multiplier_pow_three]
    _ = 1 := M.valuation_gaussSum v hvp

/-- The Fourier multiplier is nonzero, as the Fourier transform of `E` is nonzero. Used by
`fourier_inv`. -/
private theorem multiplier_ne_zero : E.multiplier ≠ 0 := by
  intro h
  have hf (x : G) : M.fourier E x = 0 := by
    rw [E.fourier_eq x, h]
    ring
  have hff := M.fourier_fourier E (0 : G)
  simp only [neg_zero] at hff
  have hz : M.fourier (M.fourier E) 0 = 0 := by
    change M.sqrtCard⁻¹ * ∑ x, M.fourier E x * M.bichar x (-0) = 0
    simp [hf]
  exact E.ne_zero 0 (hff.symm.trans hz)

/-- **The Fourier transform of `E⁻¹`**: `(E⁻¹)^ = λ⁻¹E - 1`, [RW26b, Radchenko, Wheeler (2026b),
Section 7, proof of Theorem 7]. -/
theorem fourier_inv (y : G) :
    M.fourier (fun x => (E x)⁻¹) y = E.multiplier⁻¹ * E y - 1 := by
  have hlam := E.multiplier_ne_zero
  have hpair (x : G) : M.gaussian x * E (-x) =
      E.multiplier⁻¹ * M.fourier E (-x) := by
    rw [E.fourier_eq, M.gaussian_neg]
    field_simp [hlam]
  have hfirst : M.fourier (fun x => M.gaussian x * E (-x)) y =
      E.multiplier⁻¹ * E y := by
    calc
      _ = M.fourier (fun x => E.multiplier⁻¹ * M.fourier E (-x)) y := by
        congr 1
        funext x
        exact hpair x
      _ = E.multiplier⁻¹ * M.fourier (fun x => M.fourier E (-x)) y :=
        M.fourier_const_mul _ _ _
      _ = E.multiplier⁻¹ * M.fourier (M.fourier E) (-y) := by
        rw [M.fourier_comp_neg]
      _ = E.multiplier⁻¹ * E y := by rw [M.fourier_fourier, neg_neg]
  have hdelta : M.fourier (fun x => M.sqrtCard * (if x = 0 then (1 : L) else 0)) y =
      1 := by
    rw [M.fourier_const_mul]
    convert congrArg (M.sqrtCard * ·) (M.fourier_delta (0 : G) y) using 1 <;>
      simp [M.sqrtCard_ne_zero]
  calc
    _ = M.fourier (fun x => M.gaussian x * E (-x) -
        M.sqrtCard * (if x = 0 then (1 : L) else 0)) y := by
          congr 1
          funext x
          exact E.inv_eq x
    _ = _ := by rw [M.fourier_sub, hfirst, hdelta]

/-- **`E` is Fourier-integral** when its values are integral at a valuation above `p`:
`Ê = λ⟨·⟩E` with `v(λ) = 1`. [RW26b, Radchenko, Wheeler (2026b), Section 7, proof of
Theorem 7], "For `E`, this follows from (5)". -/
theorem isFourierIntegral {p : ℕ} [Fact p.Prime] (hvp : v (p : L) < 1)
    (hint : ∀ x, v (E x) ≤ 1) : M.IsFourierIntegral v E := by
  refine ⟨hint, ?_⟩
  intro y
  rw [E.fourier_eq y, map_mul, map_mul, E.valuation_multiplier v hvp,
    M.valuation_gaussian v y, one_mul, one_mul]
  exact hint y

/-- **`E⁻¹` is Fourier-integral** when the values of `E` are units at a valuation above `p`:
`(E⁻¹)^ = λ⁻¹E - 1` with `v(λ) = 1`. [RW26b, Radchenko, Wheeler (2026b), Section 7, proof of
Theorem 7]. -/
theorem isFourierIntegral_inv {p : ℕ} [Fact p.Prime] (hvp : v (p : L) < 1)
    (hunit : ∀ x, v (E x) = 1) : M.IsFourierIntegral v fun x => (E x)⁻¹ := by
  constructor
  · intro x
    rw [map_inv₀, hunit x, inv_one]
  · intro y
    rw [E.fourier_inv y]
    apply v.map_sub_le
    · rw [map_mul, map_inv₀, E.valuation_multiplier v hvp, inv_one,
        one_mul, hunit y]
    · simp

end FiniteQuantumDilog

end SIC
