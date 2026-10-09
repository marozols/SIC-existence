/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Metric groups and their Fourier transform

Finite abelian groups with a Gaussian whose bicharacter is nondegenerate, the normalized Fourier
transform on them with its inversion formula, and the cube of the Fourier–Weil operator.

This module follows [RW26, Radchenko, Wheeler (2026), Section 4.1] and the proof of
[RW26, Radchenko, Wheeler (2026), Theorem 5, `thm:fqdilogbasicproperties`](iii). It supplies the
setting of `SICs.Dilogarithm.FiniteQuantum`, whose values are those of the finite quantum
dilogarithm of [RW26b, Radchenko, Wheeler (2026b), Section 3]. Following the remark after
[RW26, Radchenko, Wheeler (2026), Theorem 5, `thm:fqdilogbasicproperties`], the values lie in an
arbitrary field `k`, and the
square root `√N` of the order `N = |G|` normalizing the Fourier transform is a chosen element
`s ∈ k` with `s² = N`, `s ≠ 0`; over `ℂ` it is the positive root.

## The argument

A metric group carries a Gaussian `⟨x⟩ ≠ 0` with `⟨-x⟩ = ⟨x⟩` whose quotient
`⟨x; y⟩ = ⟨x + y⟩/(⟨x⟩⟨y⟩)` is a nondegenerate bicharacter. Then `⟨0⟩ = 1` (from
`⟨0; 0⟩ = ⟨0; 0⟩²`), and each `⟨x; ·⟩` is an additive character, nontrivial for `x ≠ 0`, so
`∑_y ⟨x; y⟩ = N δ(x)`. The Fourier transform `f̂(y) = s⁻¹ ∑_x f(x)⟨x; -y⟩` therefore satisfies
`f̂̂(y) = f(-y)`.

The Fourier–Weil operator `Wf(x) = ⟨x⟩⁻¹ f̂(x)` satisfies `W³f = (s⁻¹ ∑_t ⟨t⟩⁻¹) f`: in the
triple sum for `W³f(x)` the Gaussian law collapses the product of the six Gaussian and
bicharacter factors to `⟨x + r⟩⁻¹⟨r + t⟩⟨r + s + t⟩⁻¹`; the sum over `s` gives the Gauss sum,
and the remaining sum over `r` is `N δ(t - x)` after writing `⟨x + r⟩⁻¹⟨r + t⟩` as
`⟨t - x⟩⟨x + r; t - x⟩`.

For `H ≤ G`, summing the characters of `H` identifies its orthogonal complement `H^∨` and
gives `|H| ∑_{u ∈ H^∨} ⟨z;u⟩ = |G| 1_{z ∈ H}`. Over `ℂ`, the Gaussian values have norm one;
expanding the squared norm of their Gauss sum and applying bicharacter orthogonality gives
`|s⁻¹ ∑_x ⟨x⟩⁻¹| = 1` when `s` is the positive square root of `|G|`.
-/

namespace SIC

/-! ### Metric groups

The structure, its bicharacter, and the Gaussian and bicharacter laws. -/

/-- **A metric group** of [RW26, Radchenko, Wheeler (2026), Section 4.1, Definition], with values
in a field `k`: a finite abelian group `G` with a Gaussian `⟨·⟩ : G → kˣ`, `⟨-x⟩ = ⟨x⟩`, whose
quotient `⟨x; y⟩ = ⟨x + y⟩/(⟨x⟩⟨y⟩)` is a nondegenerate bicharacter, together with a square root
`s` of `|G|` in `k`, normalizing the measure `∫_G f(x) dx = s⁻¹ ∑_x f(x)`. -/
structure MetricGroup (G : Type*) [AddCommGroup G] [Fintype G] (k : Type*) [Field k] where
  /-- The Gaussian `⟨x⟩`. -/
  gaussian : G → k
  /-- `⟨x⟩ ≠ 0`. -/
  gaussian_ne_zero (x : G) : gaussian x ≠ 0
  /-- The Gaussian is even, `⟨-x⟩ = ⟨x⟩`. -/
  gaussian_neg (x : G) : gaussian (-x) = gaussian x
  /-- `⟨x; y + z⟩ = ⟨x; y⟩⟨x; z⟩` for `⟨x; y⟩ = ⟨x + y⟩/(⟨x⟩⟨y⟩)`. -/
  bichar_add_right' (x y z : G) :
    gaussian (x + (y + z)) / (gaussian x * gaussian (y + z)) =
      gaussian (x + y) / (gaussian x * gaussian y) * (gaussian (x + z) / (gaussian x * gaussian z))
  /-- Nondegeneracy: `⟨x; ·⟩ = 1` only for `x = 0`. -/
  nondegenerate (x : G) : (∀ y, gaussian (x + y) / (gaussian x * gaussian y) = 1) → x = 0
  /-- The chosen square root `s` of `N = |G|`. -/
  sqrtCard : k
  /-- `s² = N`. -/
  sqrtCard_sq : sqrtCard ^ 2 = Fintype.card G
  /-- `s ≠ 0`, so that `N` is invertible in `k`. -/
  sqrtCard_ne_zero : sqrtCard ≠ 0

namespace MetricGroup

variable {G : Type*} [AddCommGroup G] [Fintype G] {k : Type*} [Field k] (M : MetricGroup G k)

/-- **The bicharacter** `⟨x; y⟩ = ⟨x + y⟩/(⟨x⟩⟨y⟩)` of a metric group
[RW26, Radchenko, Wheeler (2026), Section 4.1]. -/
def bichar (x y : G) : k :=
  M.gaussian (x + y) / (M.gaussian x * M.gaussian y)

/-- `⟨0⟩ = 1`. -/
@[simp]
theorem gaussian_zero : M.gaussian 0 = 1 := by
  have h := M.bichar_add_right' (0 : G) 0 0
  simp only [add_zero] at h
  have hn := M.gaussian_ne_zero (0 : G)
  field_simp at h
  exact h

/-- The Gaussian law `⟨x + y⟩ = ⟨x⟩⟨y⟩⟨x; y⟩`. -/
theorem gaussian_add (x y : G) :
    M.gaussian (x + y) = M.gaussian x * M.gaussian y * M.bichar x y := by
  rw [bichar, mul_div_cancel₀ _ (mul_ne_zero (M.gaussian_ne_zero x)
    (M.gaussian_ne_zero y))]

/-- The bicharacter is symmetric. -/
theorem bichar_comm (x y : G) : M.bichar x y = M.bichar y x := by
  simp only [bichar, add_comm x y, mul_comm (M.gaussian x) (M.gaussian y)]

/-- The bicharacter never vanishes. -/
theorem bichar_ne_zero (x y : G) : M.bichar x y ≠ 0 := by
  exact div_ne_zero (M.gaussian_ne_zero (x + y))
    (mul_ne_zero (M.gaussian_ne_zero x) (M.gaussian_ne_zero y))

/-- `⟨x; y + z⟩ = ⟨x; y⟩⟨x; z⟩`. -/
theorem bichar_add_right (x y z : G) : M.bichar x (y + z) = M.bichar x y * M.bichar x z := by
  exact M.bichar_add_right' x y z

/-- `⟨x + y; z⟩ = ⟨x; z⟩⟨y; z⟩`. -/
theorem bichar_add_left (x y z : G) : M.bichar (x + y) z = M.bichar x z * M.bichar y z := by
  rw [M.bichar_comm, M.bichar_add_right, M.bichar_comm z x, M.bichar_comm z y]

/-- `⟨x; 0⟩ = 1`. -/
@[simp]
theorem bichar_zero_right (x : G) : M.bichar x 0 = 1 := by
  simp [bichar, M.gaussian_ne_zero]

/-- `⟨0; y⟩ = 1`. -/
@[simp]
theorem bichar_zero_left (y : G) : M.bichar 0 y = 1 := by
  rw [M.bichar_comm, M.bichar_zero_right]

/-- `⟨x; -y⟩ = ⟨x; y⟩⁻¹`. -/
theorem bichar_neg_right (x y : G) : M.bichar x (-y) = (M.bichar x y)⁻¹ := by
  have h := M.bichar_add_right x y (-y)
  simp only [add_neg_cancel, M.bichar_zero_right] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/-- `⟨-x; y⟩ = ⟨x; y⟩⁻¹`. -/
theorem bichar_neg_left (x y : G) : M.bichar (-x) y = (M.bichar x y)⁻¹ := by
  rw [M.bichar_comm, M.bichar_neg_right, M.bichar_comm]

/-! ### The bicharacter as a character -/

/-- The character `⟨x; ·⟩` of `G`. -/
def bicharAddChar (x : G) : AddChar G k where
  toFun := M.bichar x
  map_zero_eq_one' := M.bichar_zero_right x
  map_add_eq_mul' := M.bichar_add_right x

/-- Evaluation of `bicharAddChar`. -/
@[simp]
theorem bicharAddChar_apply (x y : G) : M.bicharAddChar x y = M.bichar x y := rfl

/-! ### Multiples in the bicharacter

The bicharacter is multiplicative on natural multiples in each argument. -/

/-- `⟨n • x; y⟩ = ⟨x; y⟩^n`, used by the residue-moment reduction. -/
theorem bichar_nsmul_left (n : ℕ) (x y : G) :
    M.bichar (n • x) y = M.bichar x y ^ n := by
  rw [M.bichar_comm, ← M.bicharAddChar_apply,
    AddChar.map_nsmul_eq_pow, M.bicharAddChar_apply, M.bichar_comm]

/-- `⟨x; n • y⟩ = ⟨x; y⟩^n`, used by the residue-moment reduction. -/
theorem bichar_nsmul_right (n : ℕ) (x y : G) :
    M.bichar x (n • y) = M.bichar x y ^ n := by
  simpa only [M.bicharAddChar_apply] using (M.bicharAddChar x).map_nsmul_eq_pow n y

/-! ### Finite-order values -/

/-- `⟨x; y⟩^N = 1` for `N = |G|`: the bicharacter takes values in the `N`-th roots of unity. -/
theorem bichar_pow_card (x y : G) : M.bichar x y ^ Fintype.card G = 1 := by
  rw [← M.bichar_nsmul_left, card_nsmul_eq_zero, M.bichar_zero_left]

/-- `⟨x⟩^{2N} = 1` for `N = |G|`: the Gaussian takes values in the `2N`-th roots of unity. -/
theorem gaussian_pow_two_mul_card (x : G) : M.gaussian x ^ (2 * Fintype.card G) = 1 := by
  have h := M.gaussian_add x (-x)
  rw [add_neg_cancel, M.gaussian_zero, M.gaussian_neg,
    M.bichar_neg_right] at h
  have hb : M.gaussian x ^ 2 = M.bichar x x := by
    field_simp [M.bichar_ne_zero x x] at h
    simpa only [pow_two] using h.symm
  rw [pow_mul, hb, M.bichar_pow_card]

/-! ### Character orthogonality -/

/-- Orthogonality: `∑_y ⟨x; y⟩ = N δ(x)`. -/
theorem sum_bichar [DecidableEq G] (x : G) :
    ∑ y, M.bichar x y = if x = 0 then (Fintype.card G : k) else 0 := by
  split_ifs with hx
  · subst x
    simp
  · have hchar : M.bicharAddChar x ≠ 1 := by
      intro h
      apply hx
      apply M.nondegenerate
      intro y
      exact congrArg (fun ψ : AddChar G k => ψ y) h
    simpa only [bicharAddChar_apply] using AddChar.sum_eq_zero_of_ne_one hchar

/-! ### The orthogonal complement

`H^∨ = {g : ⟨g; h⟩ = 1 for all h ∈ H}`. -/

/-- **The orthogonal complement** `H^∨ = {g ∈ G : ⟨g; h⟩ = 1 for all h ∈ H}` of a subgroup of a
metric group [AFK26, Appleby, Flammia, Kopp (2026), Section 3, Theorem 3.1,
`thm:subgrouppentagon`]. -/
def orthogonal (H : AddSubgroup G) : AddSubgroup G where
  carrier := {g | ∀ h ∈ H, M.bichar g h = 1}
  zero_mem' := by
    intro h _
    exact M.bichar_zero_left h
  add_mem' := by
    intro a b ha hb h hh
    rw [M.bichar_add_left, ha h hh, hb h hh, one_mul]
  neg_mem' := by
    intro a ha h hh
    rw [M.bichar_neg_left, ha h hh, inv_one]

/-- Membership in `H^∨`. -/
@[simp]
theorem mem_orthogonal {H : AddSubgroup G} {g : G} :
    g ∈ M.orthogonal H ↔ ∀ h ∈ H, M.bichar g h = 1 :=
  Iff.rfl

open scoped Classical in
/-- The character `h ↦ ⟨u; h⟩` sums to `|H|` when `u ∈ H^∨`, and to zero otherwise. -/
theorem sum_bichar_subgroup (H : AddSubgroup G) (u : G) :
    (∑ h with h ∈ H, M.bichar u h) =
      if u ∈ M.orthogonal H then (Nat.card H : k) else 0 := by
  classical
  have hsub : (∑ h with h ∈ H, M.bichar u h) = ∑ h : H, M.bichar u h := by
    simpa using
      (Finset.sum_subtype_eq_sum_filter (s := Finset.univ) (p := fun h : G => h ∈ H)
        (f := M.bichar u)).symm
  rw [hsub]
  let ψ : AddChar H k := {
    toFun := fun h => M.bichar u h
    map_zero_eq_one' := by simp
    map_add_eq_mul' := by
      intro h₁ h₂
      simpa only [AddSubgroup.coe_add] using M.bichar_add_right u (h₁ : G) (h₂ : G)
  }
  by_cases hu : u ∈ M.orthogonal H
  · have hconst (h : H) : M.bichar u h = 1 := (M.mem_orthogonal.mp hu) h h.property
    simp_rw [hconst]
    simp [hu, Nat.card_eq_fintype_card]
  · have hψ : ψ ≠ 1 := by
      intro heq
      apply hu
      rw [M.mem_orthogonal]
      intro h hh
      have heval := congrArg (fun χ : AddChar H k => χ ⟨h, hh⟩) heq
      simpa [ψ] using heval
    have hsum := AddChar.sum_eq_zero_of_ne_one hψ
    simpa [ψ, hu] using hsum

/-- The image of `|H|` in `k` is nonzero. -/
theorem card_subgroup_ne_zero (M : MetricGroup G k) (H : AddSubgroup G) :
    (Nat.card H : k) ≠ 0 := by
  have hG : (Nat.card G : k) ≠ 0 := by
    rw [Nat.card_eq_fintype_card, ← M.sqrtCard_sq]
    exact pow_ne_zero 2 M.sqrtCard_ne_zero
  obtain ⟨d, hd⟩ := H.card_addSubgroup_dvd_card
  intro hH
  apply hG
  rw [hd, Nat.cast_mul, hH, zero_mul]

open scoped Classical in
/-- **Character orthogonality on `H^∨`**, multiplied by `|H|`:
`|H| ∑_{u ∈ H^∨} ⟨z;u⟩ = |G| 1_{z ∈ H}`. -/
theorem card_mul_sum_orthogonal_bichar (H : AddSubgroup G) (z : G) :
    (Nat.card H : k) * ∑ u with u ∈ M.orthogonal H, M.bichar z u =
      if z ∈ H then (Fintype.card G : k) else 0 := by
  classical
  calc
    _ = ∑ u : G, (∑ h with h ∈ H, M.bichar u h) * M.bichar z u := by
      simp_rw [M.sum_bichar_subgroup H]
      simp only [ite_mul, zero_mul, Finset.sum_ite, Finset.sum_const_zero, add_zero]
      rw [Finset.mul_sum]
    _ = ∑ h with h ∈ H, ∑ u : G, M.bichar (z + h) u := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h _
      apply Finset.sum_congr rfl
      intro u _
      rw [M.bichar_add_left, M.bichar_comm u h]
      ring_nf
    _ = ∑ h with h ∈ H, if z + h = 0 then (Fintype.card G : k) else 0 := by
      simp_rw [M.sum_bichar]
    _ = if z ∈ H then (Fintype.card G : k) else 0 := by
      have hiff (h : G) : z + h = 0 ↔ h = -z := by
        constructor
        · intro hh
          calc h = -z + (z + h) := by simp
                 _ = -z := by rw [hh, add_zero]
        · intro hh
          rw [hh]
          exact add_neg_cancel z
      simp_rw [hiff]
      rw [Finset.sum_ite_eq']
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [H.neg_mem_iff]

/-- **The dual pair of multiples and torsion**: the orthogonal complement of the multiples
`nG` is the `n`-torsion `G[n]`, since `⟨nx; y⟩ = ⟨x; ny⟩` and the bicharacter is nondegenerate.
At `n = d` this is the pair `H = dG`, `H^∨ = G[d]` of [AFK26, Appleby, Flammia, Kopp (2026),
Section 5]. -/
theorem orthogonal_range_nsmul (n : ℕ) :
    M.orthogonal (nsmulAddMonoidHom n : G →+ G).range = (nsmulAddMonoidHom n : G →+ G).ker := by
  ext y
  constructor
  · intro hy
    change n • y = 0
    apply M.nondegenerate
    intro x
    calc
      M.bichar (n • y) x = M.bichar y (n • x) := by
        rw [M.bichar_nsmul_left, M.bichar_nsmul_right]
      _ = 1 := hy (n • x) ⟨x, rfl⟩
  · intro hy h hh
    obtain ⟨x, rfl⟩ := hh
    change n • y = 0 at hy
    calc
      M.bichar y (n • x) = M.bichar (n • y) x := by
        rw [M.bichar_nsmul_left, M.bichar_nsmul_right]
      _ = 1 := by rw [hy, M.bichar_zero_left]

/-- `s⁻² N = 1`. -/
theorem sqrtCard_inv_sq_mul_card : (M.sqrtCard⁻¹) ^ 2 * Fintype.card G = 1 := by
  rw [← M.sqrtCard_sq, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 M.sqrtCard_ne_zero)]

/-! ### The Fourier transform

`f̂(y) = s⁻¹ ∑_x f(x)⟨x; -y⟩`, its inversion, and the Fourier–Weil operator. -/

/-- **The normalized Fourier transform** `f̂(y) = ∫_G f(x)⟨x; -y⟩ dx` of
[RW26, Radchenko, Wheeler (2026), Section 4.1] and [RW26b, Radchenko, Wheeler (2026b),
Section 3]. -/
def fourier (f : G → k) (y : G) : k :=
  M.sqrtCard⁻¹ * ∑ x, f x * M.bichar x (-y)

/-- The Fourier transform commutes with scalar multiplication. -/
theorem fourier_const_mul (c : k) (f : G → k) (x : G) :
    M.fourier (fun z => c * f z) x = c * M.fourier f x := by
  simp only [fourier, Finset.mul_sum]
  ring_nf

open scoped Classical in
/-- The Fourier transform of a constant, used in `fourier_div_translationRatio`. -/
theorem fourier_constant [DecidableEq G] (c : k) (y : G) :
    M.fourier (fun _ => c) y = M.sqrtCard * c * (if y = 0 then 1 else 0) := by
  classical
  have hsum : (∑ t : G, M.bichar t (-y)) =
      if -y = 0 then (Fintype.card G : k) else 0 := by
    rw [← M.sum_bichar (-y)]
    apply Finset.sum_congr rfl
    intro t _
    exact M.bichar_comm t (-y)
  simp only [MetricGroup.fourier, ← Finset.mul_sum, hsum]
  by_cases hy : y = 0
  · subst y
    simp only [neg_zero, ite_true, mul_one]
    rw [← M.sqrtCard_sq]
    field_simp [M.sqrtCard_ne_zero]
  · have hny : -y ≠ 0 := neg_ne_zero.mpr hy
    simp [hy, hny]

open scoped Classical in
/-- The Fourier transform of a point mass, used in `fourier_div_translationRatio`. -/
theorem fourier_delta [DecidableEq G] (x y : G) :
    M.fourier (fun t => if t + x = 0 then (1 : k) else 0) y =
      M.sqrtCard⁻¹ * M.bichar x y := by
  classical
  have hpoint (t : G) : (if t + x = 0 then (1 : k) else 0) =
      if t = -x then 1 else 0 := by
    simp only [add_eq_zero_iff_eq_neg]
  simp only [MetricGroup.fourier, hpoint]
  have hsum : (∑ t : G, (if t = -x then (1 : k) else 0) * M.bichar t (-y)) =
      M.bichar (-x) (-y) := by simp
  rw [hsum, M.bichar_neg_left, M.bichar_neg_right, inv_inv]

/-- Linearity of the normalized Fourier transform, used in
`fourier_div_translationRatio`. -/
theorem fourier_add (f g : G → k) (y : G) :
    M.fourier (fun t => f t + g t) y = M.fourier f y + M.fourier g y := by
  simp only [MetricGroup.fourier, add_mul, Finset.sum_add_distrib]
  ring

/-- Subtraction under the normalized Fourier transform, used in
`fourier_div_translationRatio`. -/
theorem fourier_sub (f g : G → k) (y : G) :
    M.fourier (fun t => f t - g t) y = M.fourier f y - M.fourier g y := by
  simp only [MetricGroup.fourier, sub_mul, Finset.sum_sub_distrib]
  ring

/-- The bicharacter sum used in Fourier inversion. -/
private theorem sum_bichar_inv_mul [DecidableEq G] (x z : G) :
    (∑ y, M.bichar z (-y) * M.bichar x y) =
      if x = z then (Fintype.card G : k) else 0 := by
  have hb (y : G) : M.bichar z (-y) * M.bichar x y = M.bichar (x - z) y := by
    rw [M.bichar_neg_right, ← M.bichar_neg_left, sub_eq_add_neg,
      M.bichar_add_left, mul_comm]
  simp_rw [hb]
  rw [M.sum_bichar]
  simp only [sub_eq_zero]

/-- Fourier inversion `f(x) = s⁻¹ ∑_y f̂(y)⟨x; y⟩`. -/
theorem sum_fourier_mul_bichar (f : G → k) (x : G) :
    M.sqrtCard⁻¹ * ∑ y, M.fourier f y * M.bichar x y = f x := by
  classical
  calc
    _ = (M.sqrtCard⁻¹) ^ 2 * ∑ z, f z *
        (∑ y, M.bichar z (-y) * M.bichar x y) := by
      simp only [fourier, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      simp only [← mul_assoc]
      ring_nf
    _ = (M.sqrtCard⁻¹) ^ 2 * ∑ z, f z *
        (if x = z then (Fintype.card G : k) else 0) := by
      simp only [M.sum_bichar_inv_mul]
    _ = f x := by
      simp only [inv_pow, mul_ite, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, ↓reduceIte]
      rw [mul_comm (f x) (Fintype.card G : k), ← mul_assoc,
        ← M.sqrtCard_sq, inv_mul_cancel₀ (pow_ne_zero 2 M.sqrtCard_ne_zero), one_mul]

/-- `f̂̂(y) = f(-y)` [RW26, Radchenko, Wheeler (2026), Section 4.1]. -/
theorem fourier_fourier (f : G → k) (y : G) : M.fourier (M.fourier f) y = f (-y) := by
  calc
    _ = M.sqrtCard⁻¹ * ∑ z, M.fourier f z * M.bichar (-y) z := by
      change M.sqrtCard⁻¹ * ∑ z, M.fourier f z * M.bichar z (-y) = _
      congr 1
      apply Finset.sum_congr rfl
      intro z _
      rw [M.bichar_comm]
    _ = f (-y) := M.sum_fourier_mul_bichar f (-y)

/-- The transform of a reflected function: `(f ∘ neg)^(y) = f̂(-y)`. -/
theorem fourier_comp_neg (f : G → k) (y : G) :
    M.fourier (fun x => f (-x)) y = M.fourier f (-y) := by
  simp only [fourier, neg_neg]
  congr 1
  calc
    (∑ x, f (-x) * M.bichar x (-y)) =
        ∑ x, f x * M.bichar (-x) (-y) := by
      apply Fintype.sum_equiv (Equiv.neg G)
      intro x
      simp
    _ = ∑ x, f x * M.bichar x y := by
      apply Finset.sum_congr rfl
      intro x _
      rw [M.bichar_neg_left, M.bichar_neg_right, inv_inv]

/-- **The Gauss sum** `∫_G ⟨x⟩⁻¹ dx = s⁻¹ ∑_x ⟨x⟩⁻¹` of [RW26, Radchenko, Wheeler (2026),
Theorem 5, `thm:fqdilogbasicproperties`](iii). -/
def gaussSum : k :=
  M.sqrtCard⁻¹ * ∑ x, (M.gaussian x)⁻¹

/-- **The Fourier–Weil operator** `Wf(x) = ⟨x⟩⁻¹ f̂(x)` of the proof of
[RW26, Radchenko, Wheeler (2026), Theorem 5, `thm:fqdilogbasicproperties`](iii). -/
def weil (f : G → k) (x : G) : k :=
  (M.gaussian x)⁻¹ * M.fourier f x

/-- The Fourier–Weil operator commutes with scalar multiplication. -/
theorem weil_const_mul (c : k) (f : G → k) (x : G) :
    M.weil (fun z => c * f z) x = c * M.weil f x := by
  simp only [weil, M.fourier_const_mul]
  ring

/-- The Gaussian quotient appearing in the Weil operator. -/
private def weilKernel (x t : G) : k :=
  M.gaussian t * (M.gaussian (x + t))⁻¹

/-- The Weil kernel as a quotient of Gaussian values. -/
private theorem weil_kernel (x t : G) :
    (M.gaussian x)⁻¹ * M.bichar t (-x) =
      M.weilKernel x t := by
  dsimp only [weilKernel]
  rw [M.bichar_neg_right, M.bichar_comm t x, M.gaussian_add x t]
  field_simp [M.gaussian_ne_zero x, M.gaussian_ne_zero t, M.bichar_ne_zero x t]

/-- The Weil operator written with its Gaussian quotient kernel. -/
private theorem weil_eq_sum (f : G → k) (x : G) :
    M.weil f x = M.sqrtCard⁻¹ * ∑ t, f t * M.weilKernel x t := by
  simp only [weil, fourier]
  calc
    _ = M.sqrtCard⁻¹ * ((M.gaussian x)⁻¹ *
        ∑ t, f t * M.bichar t (-x)) := by ring
    _ = M.sqrtCard⁻¹ * ∑ t, f t *
        ((M.gaussian x)⁻¹ * M.bichar t (-x)) := by
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ = _ := by simp only [M.weil_kernel]

/-- The Gaussian four-term relation used to reduce the Weil cube. -/
private theorem gaussian_cross (r s t : G) :
    M.gaussian r * M.gaussian s * M.gaussian t * M.gaussian (r + s + t) =
      M.gaussian (r + t) * M.gaussian (r + s) * M.gaussian (s + t) := by
  simp only [M.gaussian_add, M.bichar_add_left]
  ring

/-- The three Weil kernels reduce to a translated Gaussian. -/
private theorem gaussian_kernel_three (x r s t : G) :
    M.weilKernel x r * M.weilKernel r s * M.weilKernel s t =
        (M.gaussian (x + r))⁻¹ * M.gaussian (r + t) *
          (M.gaussian (r + s + t))⁻¹ := by
  have hc := M.gaussian_cross r s t
  dsimp only [weilKernel]
  field_simp [M.gaussian_ne_zero (x + r), M.gaussian_ne_zero (r + s),
    M.gaussian_ne_zero (s + t), M.gaussian_ne_zero (r + s + t)]
  convert hc using 1
  ring

/-- A translated Gaussian has the same sum. -/
private theorem sum_gaussian_shift_inv (u : G) :
    (∑ s, (M.gaussian (u + s))⁻¹) = ∑ s, (M.gaussian s)⁻¹ := by
  exact Fintype.sum_equiv (Equiv.addLeft u) _ _ (fun _ => rfl)

/-- The remaining Weil kernel sums to a Kronecker delta. -/
private theorem sum_gaussian_ratio [DecidableEq G] (x t : G) :
    (∑ r, (M.gaussian (x + r))⁻¹ * M.gaussian (r + t)) =
      if t = x then (Fintype.card G : k) else 0 := by
  have hratio (r : G) :
      (M.gaussian (x + r))⁻¹ * M.gaussian (r + t) =
        M.gaussian (t - x) * M.bichar (x + r) (t - x) := by
    have heq : r + t = (x + r) + (t - x) := by abel
    rw [heq, M.gaussian_add (x + r) (t - x)]
    field_simp [M.gaussian_ne_zero (x + r)]
  have hsum :
      (∑ r, (M.gaussian (x + r))⁻¹ * M.gaussian (r + t)) =
        M.gaussian (t - x) * M.bichar x (t - x) *
          ∑ r, M.bichar (t - x) r := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [hratio, M.bichar_add_left, M.bichar_comm r (t - x)]
    ring
  rw [hsum, M.sum_bichar]
  by_cases h : t = x
  · subst t
    simp
  · have hne : t - x ≠ 0 := sub_ne_zero.mpr h
    simp only [hne, h, ↓reduceIte, mul_zero]

/-- Summing two Weil kernels leaves the Gaussian Gauss sum and a delta. -/
private theorem sum_weilKernel [DecidableEq G] (x t : G) :
    (∑ r, ∑ s, M.weilKernel x r * M.weilKernel r s * M.weilKernel s t) =
      (∑ u, (M.gaussian u)⁻¹) *
        (if t = x then (Fintype.card G : k) else 0) := by
  simp_rw [M.gaussian_kernel_three]
  have hs (r : G) :
      (∑ s, (M.gaussian (x + r))⁻¹ * M.gaussian (r + t) *
        (M.gaussian (r + s + t))⁻¹) =
        ((M.gaussian (x + r))⁻¹ * M.gaussian (r + t)) *
          ∑ u, (M.gaussian u)⁻¹ := by
    have hshift : (∑ s, (M.gaussian (r + s + t))⁻¹) =
        ∑ u, (M.gaussian u)⁻¹ := by
      calc
        _ = ∑ s, (M.gaussian ((r + t) + s))⁻¹ := by
          apply Finset.sum_congr rfl
          intro s _
          congr 1
          abel_nf
        _ = _ := M.sum_gaussian_shift_inv (r + t)
    calc
      _ = ((M.gaussian (x + r))⁻¹ * M.gaussian (r + t)) *
          ∑ s, (M.gaussian (r + s + t))⁻¹ := by rw [Finset.mul_sum]
      _ = _ := by rw [hshift]
  simp_rw [hs]
  rw [← Finset.sum_mul, M.sum_gaussian_ratio]
  ring

/-- The Weil cube expanded as a finite triple sum. -/
private theorem weil_cube_sum (f : G → k) (x : G) :
    M.weil (M.weil (M.weil f)) x =
      (M.sqrtCard⁻¹) ^ 3 * ∑ t, f t *
        (∑ r, ∑ s, M.weilKernel x r * M.weilKernel r s * M.weilKernel s t) := by
  simp only [M.weil_eq_sum, Finset.mul_sum, Finset.sum_mul]
  have hreorder (F : G → G → G → k) :
      (∑ r, ∑ s, ∑ t, F r s t) = ∑ t, ∑ r, ∑ s, F r s t := by
    calc
      _ = ∑ r, ∑ t, ∑ s, F r s t := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.sum_comm]
      _ = _ := by rw [Finset.sum_comm]
  have hpoint (r s t : G) :
      M.sqrtCard⁻¹ * (M.sqrtCard⁻¹ *
        (M.sqrtCard⁻¹ * (f t * M.weilKernel s t) * M.weilKernel r s) *
          M.weilKernel x r) =
        (M.sqrtCard⁻¹) ^ 3 * f t * M.weilKernel s t *
          M.weilKernel r s * M.weilKernel x r := by ring
  simp_rw [hpoint]
  rw [hreorder (fun r s t => (M.sqrtCard⁻¹) ^ 3 * f t *
    M.weilKernel s t * M.weilKernel r s * M.weilKernel x r)]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- `W³f = (∫_G ⟨x⟩⁻¹ dx) f`, from the proof of [RW26, Radchenko, Wheeler (2026), Theorem 5,
`thm:fqdilogbasicproperties`](iii). -/
theorem weil_weil_weil (f : G → k) (x : G) :
    M.weil (M.weil (M.weil f)) x = M.gaussSum * f x := by
  classical
  let S : k := ∑ u, (M.gaussian u)⁻¹
  calc
    _ = (M.sqrtCard⁻¹) ^ 3 * ∑ t, f t *
        (S * if t = x then (Fintype.card G : k) else 0) := by
      rw [M.weil_cube_sum]
      simp only [M.sum_weilKernel]
      rfl
    _ = (M.sqrtCard⁻¹) ^ 3 * (f x * (S * Fintype.card G)) := by
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    _ = M.gaussSum * f x := by
      change (M.sqrtCard⁻¹) ^ 3 * (f x * (S * Fintype.card G)) =
        (M.sqrtCard⁻¹ * S) * f x
      calc
        _ = ((M.sqrtCard⁻¹) ^ 2 * Fintype.card G) *
            ((M.sqrtCard⁻¹ * S) * f x) := by ring
        _ = _ := by rw [M.sqrtCard_inv_sq_mul_card, one_mul]

/-! ### Gauss sums over nondegenerate subgroups

On a subgroup `H` on which the bicharacter is nondegenerate,
`(∑_{x∈H} ⟨x⟩⁻¹)(∑_{x∈H} ⟨x⟩) = |H|`: substitute `z = x + y`, expand
`⟨x + y⟩ = ⟨x⟩⟨y⟩⟨x; y⟩`, and sum the character `⟨·; y⟩` over `H`. -/

open scoped Classical in
/-- The bicharacter sum over a nondegenerate subgroup, used by
`sum_gaussian_inv_mul_sum_gaussian`. -/
private theorem sum_bichar_nondegenerate_subgroup (H : AddSubgroup G)
    (hH : ∀ y ∈ H, (∀ x ∈ H, M.bichar x y = 1) → y = 0) (y : H) :
    (∑ x : H, M.bichar x y) = if y = 0 then (Nat.card H : k) else 0 := by
  classical
  have horth : (y : G) ∈ M.orthogonal H ↔ y = 0 := by
    constructor
    · intro hy
      apply Subtype.ext
      apply hH y y.property
      intro x hx
      rw [M.bichar_comm]
      exact (M.mem_orthogonal.mp hy) x hx
    · intro hy
      subst y
      simp
  calc
    _ = ∑ x : H, M.bichar y x := by
      apply Finset.sum_congr rfl
      intro x _
      exact M.bichar_comm x y
    _ = ∑ x with x ∈ H, M.bichar y x := by
      simpa using (Finset.sum_subtype_eq_sum_filter (s := Finset.univ)
        (p := fun x : G => x ∈ H) (f := M.bichar y))
    _ = _ := by
      rw [M.sum_bichar_subgroup, horth]
      split_ifs <;> rfl

open scoped Classical in
/-- **The Gauss sum and its inverse sum multiply to the order** of a subgroup `H` on which the
bicharacter is nondegenerate: `(∑_{x∈H} ⟨x⟩⁻¹)(∑_{x∈H} ⟨x⟩) = |H|`. At `H = G` this is the
computation of `|γ|` in the proof of `norm_gaussSum`; at the primary parts it gives
`MetricGroup.valuation_gaussSum`. -/
theorem sum_gaussian_inv_mul_sum_gaussian (H : AddSubgroup G)
    (hH : ∀ y ∈ H, (∀ x ∈ H, M.bichar x y = 1) → y = 0) :
    (∑ x : H, (M.gaussian x)⁻¹) * ∑ x : H, M.gaussian x = (Nat.card H : k) := by
  classical
  have hterm (x y : H) :
      (M.gaussian x)⁻¹ * M.gaussian (x + y) = M.gaussian y * M.bichar x y := by
    rw [M.gaussian_add]
    field_simp [M.gaussian_ne_zero x]
  calc
    _ = ∑ x : H, ∑ z : H, (M.gaussian x)⁻¹ * M.gaussian z := by
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]
    _ = ∑ x : H, ∑ y : H, (M.gaussian x)⁻¹ * M.gaussian (x + y) := by
      apply Finset.sum_congr rfl
      intro x _
      exact (Fintype.sum_equiv (Equiv.addLeft x)
        (fun y : H => (M.gaussian x)⁻¹ * M.gaussian (x + y))
        (fun z : H => (M.gaussian x)⁻¹ * M.gaussian z) (fun _ => rfl)).symm
    _ = ∑ y : H, M.gaussian y * ∑ x : H, M.bichar x y := by
      simp_rw [hterm]
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by
      simp_rw [M.sum_bichar_nondegenerate_subgroup H hH]
      simp

/-! ### The Gauss sum of a complex metric group -/

/-- The Gaussian values of a complex metric group have norm one, used by
`MetricGroup.conj_gaussian_inv`. -/
theorem norm_gaussian (M : MetricGroup G ℂ) (x : G) : ‖M.gaussian x‖ = 1 := by
  apply Complex.norm_eq_one_of_pow_eq_one (M.gaussian_pow_two_mul_card x)
  exact Nat.mul_ne_zero (by decide) (Fintype.card_ne_zero)

/-- Complex conjugation inverts the Gaussian values, used by
`MetricGroup.norm_gaussSum`. -/
theorem conj_gaussian_inv (M : MetricGroup G ℂ) (x : G) :
    (starRingEnd ℂ) ((M.gaussian x)⁻¹) = M.gaussian x := by
  have hm : M.gaussian x * (starRingEnd ℂ) (M.gaussian x) = 1 := by
    rw [Complex.mul_conj', M.norm_gaussian x]
    norm_num
  rw [map_inv₀, eq_inv_of_mul_eq_one_right hm, inv_inv]

/-- **The Gauss sum of a complex metric group has absolute value one** when `s = √N` is the
positive square root, as used in the proof of [RW26b, Radchenko, Wheeler (2026b), Section 7.1,
Lemma 7] (`|λ| = 1`). -/
theorem norm_gaussSum (M : MetricGroup G ℂ)
    (hs : M.sqrtCard = (Real.sqrt (Fintype.card G) : ℂ)) : ‖M.gaussSum‖ = 1 := by
  classical
  let S : ℂ := ∑ x, (M.gaussian x)⁻¹
  have hconj : (starRingEnd ℂ) S = ∑ x, M.gaussian x := by
    simp only [S, map_sum, M.conj_gaussian_inv]
  have hcore : S * (starRingEnd ℂ) S = (Fintype.card G : ℂ) := by
    have htop := M.sum_gaussian_inv_mul_sum_gaussian (⊤ : AddSubgroup G) (by
      intro y _ hy
      apply M.nondegenerate
      intro x
      change M.bichar y x = 1
      rw [M.bichar_comm]
      exact hy x (by simp))
    have hsumInv : (∑ x : (⊤ : AddSubgroup G), (M.gaussian x)⁻¹) = S := by
      unfold S
      exact Fintype.sum_equiv AddSubgroup.topEquiv.toEquiv _ _ (fun _ => rfl)
    have hsum : (∑ x : (⊤ : AddSubgroup G), M.gaussian x) = ∑ x : G, M.gaussian x := by
      exact Fintype.sum_equiv AddSubgroup.topEquiv.toEquiv _ _ (fun _ => rfl)
    have hcard : Nat.card (⊤ : AddSubgroup G) = Fintype.card G := by
      rw [Nat.card_congr AddSubgroup.topEquiv.toEquiv, Nat.card_eq_fintype_card]
    calc
      _ = (∑ x : (⊤ : AddSubgroup G), (M.gaussian x)⁻¹) *
          ∑ x : (⊤ : AddSubgroup G), M.gaussian x := by rw [hsumInv, hsum, hconj]
      _ = (Nat.card (⊤ : AddSubgroup G) : ℂ) := htop
      _ = _ := by rw [hcard]
  have hS : ‖S‖ ^ 2 = (Fintype.card G : ℝ) := by
    exact Complex.ofReal_inj.mp (by simpa using (Complex.mul_conj' S).symm.trans hcore)
  have hsqrtNorm : ‖M.sqrtCard‖ ^ 2 = (Fintype.card G : ℝ) := by
    rw [hs, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]
  have hsc : ‖M.sqrtCard‖ ≠ 0 := by simpa using M.sqrtCard_ne_zero
  have hnormsq : ‖M.gaussSum‖ ^ 2 = 1 := by
    unfold MetricGroup.gaussSum
    rw [norm_mul, norm_inv]
    change (‖M.sqrtCard‖⁻¹ * ‖S‖) ^ 2 = 1
    rw [mul_pow, inv_pow, hS, ← hsqrtNorm,
      inv_mul_cancel₀ (pow_ne_zero 2 hsc)]
  nlinarith [norm_nonneg M.gaussSum]

end MetricGroup

end SIC
