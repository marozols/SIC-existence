/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SL2Z.Basic
import SICs.Source

/-!
# Determinant-`f` matrices and their right `SL₂(ℤ)`-orbits

Determinant-`f` matrices `G_f` and their upper-triangular representatives modulo `SL₂(ℤ)`, after
[72, Kopp (2024), Lemma 4.44, `lem:Gforbits`].

The conductor relation [72, Kopp (2024), Theorem 4.46, `thm:cllr`] transports a real quadratic
point through an integral matrix `B` of determinant `f`. Lemma 4.44 writes every such `B` as
`B = UC` with `U = [[a, b], [0, d]]` upper triangular and `C ∈ SL₂(ℤ)`, which reduces the relation
to upper-triangular matrices (`SICs.Cocycle.ConductorDistribution`,
`SICs.Cocycle.ConductorRelation`). Nothing here mentions the Shintani--Faddeev cocycle.

## Main definitions

- `SIC.Gf`: the set `G_f` of integral `2 × 2` matrices of determinant `f`, following
  [72, Kopp (2024), Definition 4.41].

## Main results

- `SIC.exists_eq_upperTriangular_mul_of_mem_Gf`: [72, Kopp (2024), Lemma 4.44, `lem:Gforbits`],
  that every `B ∈ G_f` factors as an upper triangular matrix times an element of `SL₂(ℤ)`.

## References

- [72] G. S. Kopp, "The Shintani--Faddeev modular cocycle: Stark units from q-Pochhammer
  ratios," arXiv:2411.06763v3, Definition 4.41, Lemma 4.44, and Theorem 4.46
-/

noncomputable section

namespace SIC

open scoped MatrixGroups

/-! ### Integral matrices of determinant `f`

The set `G_f` is the matrix space used by Kopp to transport quadratic points between orders.
Only its determinant characterization is needed here. -/

/-- The set `G_f = {M ∈ M₂(ℤ) : det M = f}` of [72, Kopp (2024), Definition 4.41], following
Iwaniec's notation. Only the `2 × 2` case is used here. -/
def Gf (f : ℤ) : Set (Mat(2, ℤ)) :=
  {M | M.det = f}

/-- Membership in `Gf f` is the determinant equation `det M = f`. -/
@[simp]
lemma mem_Gf {f : ℤ} {M : Mat(2, ℤ)} : M ∈ Gf f ↔ M.det = f :=
  Iff.rfl

/-- A matrix of positive determinant lies in `G_f` for its natural-number determinant;
used for the inclusion matrix in `pseudolatticeDilog_distribution`. -/
lemma mem_Gf_det_toNat {M : Mat(2, ℤ)} (hdet : 0 < M.det) :
    M ∈ Gf (M.det.toNat : ℤ) := by
  rw [mem_Gf]
  exact (Int.toNat_of_nonneg hdet.le).symm

/-! ### Right `SL₂(ℤ)`-orbits in `G_f`

A Bézout reduction of the bottom row followed by a translation puts every positive-determinant
matrix into the upper-triangular representative required by [72, Kopp (2024), Lemma 4.44,
`lem:Gforbits`]. -/

/-- [72, Kopp (2024), Lemma 4.44, `lem:Gforbits`]: every `B ∈ G_f` factors as `B = U * C` for an
upper triangular `U = [[a, b], [0, d]]` with `a, d` positive naturals, `a * d = f`, `0 ≤ b < a`,
and `C ∈ SL₂(ℤ)`.

Constructed directly rather than by the signed Euclidean algorithm of [72]'s own proof: writing
`g = gcd(c, d₀)` for `B`'s bottom row `(c, d₀)`, a Bézout identity for `c/g, d₀/g` gives a
determinant-one `C₀` clearing the bottom-left entry of `B * C₀` to `0`; a further right
multiplication by a power of `T` reduces the resulting top-right entry into `[0, a)`. -/
@[source "72, Lemma 4.44, p. 50, lem:Gforbits"]
theorem exists_eq_upperTriangular_mul_of_mem_Gf {f : ℕ} (hf : 0 < f)
    {B : Mat(2, ℤ)} (hB : B ∈ Gf (f : ℤ)) :
    ∃ a d : ℕ, ∃ b : ℤ, ∃ C : SL(2, ℤ), a * d = f ∧ 0 ≤ b ∧ b < (a : ℤ) ∧
      B = !![(a : ℤ), b; 0, (d : ℤ)] * (C : Mat(2, ℤ)) := by
  have hdetB : B 0 0 * B 1 1 - B 0 1 * B 1 0 = (f : ℤ) := by
    have h := mem_Gf.mp hB
    rwa [Matrix.det_fin_two] at h
  set g : ℕ := (B 1 0).gcd (B 1 1) with hg_def
  have hg0 : g ≠ 0 := by
    intro h
    rw [hg_def, Int.gcd_eq_zero_iff] at h
    rw [h.1, h.2, mul_zero, mul_zero, sub_zero] at hdetB
    omega
  have hgpos : (0 : ℤ) < (g : ℤ) := by positivity
  obtain ⟨c', hc'⟩ : (g : ℤ) ∣ B 1 0 := Int.gcd_dvd_left (B 1 0) (B 1 1)
  obtain ⟨d', hd'⟩ : (g : ℤ) ∣ B 1 1 := Int.gcd_dvd_right (B 1 0) (B 1 1)
  have hcop : c'.gcd d' = 1 := by
    have hmul : ((g : ℤ) * c').gcd ((g : ℤ) * d') = (g : ℤ).natAbs * c'.gcd d' :=
      Int.gcd_mul_left (g : ℤ) c' d'
    rw [← hc', ← hd', ← hg_def] at hmul
    have hnatabs : (g : ℤ).natAbs = g := by simp
    rw [hnatabs] at hmul
    exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hg0) (by rw [mul_one]; exact hmul)).symm
  obtain ⟨u, v, huv⟩ : IsCoprime c' d' := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  set C₀ : Mat(2, ℤ) := !![d', u; -c', v] with hC₀_def
  have hdetC₀ : C₀.det = 1 := by
    rw [hC₀_def, Matrix.det_fin_two_of]
    linear_combination huv
  set a₀ := B 0 0 * d' - B 0 1 * c' with ha₀_def
  set b₀ := B 0 0 * u + B 0 1 * v with hb₀_def
  have e00 : (B * C₀) 0 0 = a₀ := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, hC₀_def, ha₀_def]; ring
  have e01 : (B * C₀) 0 1 = b₀ := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, hC₀_def, hb₀_def]
  have e10 : (B * C₀) 1 0 = 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, hC₀_def]
    linear_combination hc' * d' - hd' * c'
  have e11 : (B * C₀) 1 1 = (g : ℤ) := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, hC₀_def]
    linear_combination hc' * u + hd' * v + (g : ℤ) * huv
  have hBC₀ : B * C₀ = !![a₀, b₀; 0, (g : ℤ)] := by
    rw [Matrix.eta_fin_two (B * C₀), e00, e01, e10, e11]
  have hga₀ : (g : ℤ) * a₀ = (f : ℤ) := by
    rw [ha₀_def]
    rw [hc', hd'] at hdetB
    linear_combination hdetB
  have ha₀pos : 0 < a₀ := by
    rcases lt_or_ge 0 a₀ with h | h
    · exact h
    · exfalso; nlinarith [hga₀, hgpos, (by exact_mod_cast hf : (0 : ℤ) < (f : ℤ))]
  set a : ℕ := a₀.toNat with ha_def
  have haq : (a : ℤ) = a₀ := Int.toNat_of_nonneg ha₀pos.le
  have had : a * g = f := by
    have hcast : (a : ℤ) * (g : ℤ) = (f : ℤ) := by rw [haq]; linear_combination hga₀
    exact_mod_cast hcast
  set k := b₀ / a₀ with hk_def
  set r := b₀ % a₀ with hr_def
  have hrnonneg : 0 ≤ r := Int.emod_nonneg b₀ ha₀pos.ne'
  have hrlt : r < a₀ := Int.emod_lt_of_pos b₀ ha₀pos
  have hbk : a₀ * k + r = b₀ := Int.mul_ediv_add_emod b₀ a₀
  set C₁ : Mat(2, ℤ) := !![1, -k; 0, 1] with hC₁_def
  have hdetC₁ : C₁.det = 1 := by rw [hC₁_def, Matrix.det_fin_two_of]; ring
  have hUT : B * (C₀ * C₁) = !![a₀, r; 0, (g : ℤ)] := by
    rw [← Matrix.mul_assoc, hBC₀, hC₁_def]
    set P : Mat(2, ℤ) :=
      !![a₀, b₀; 0, (g : ℤ)] * (!![1, -k; 0, 1] : Mat(2, ℤ)) with hP_def
    have f00 : P 0 0 = a₀ := by simp [hP_def]
    have f01 : P 0 1 = r := by
      simp [hP_def]
      linear_combination -hbk
    have f10 : P 1 0 = 0 := by simp [hP_def]
    have f11 : P 1 1 = (g : ℤ) := by simp [hP_def]
    rw [Matrix.eta_fin_two P, f00, f01, f10, f11]
  set D : Mat(2, ℤ) := C₀ * C₁ with hD_def
  have hDdet : D.det = 1 := by rw [hD_def, Matrix.det_mul, hdetC₀, hdetC₁, mul_one]
  set Cinv : Mat(2, ℤ) := D.adjugate with hCinv_def
  have hCinvdet : Cinv.det = 1 := by
    rw [hCinv_def, Matrix.det_adjugate, hDdet]; norm_num
  have hDCinv : D * Cinv = 1 := by rw [hCinv_def, Matrix.mul_adjugate, hDdet, one_smul]
  refine ⟨a, g, r, ⟨Cinv, hCinvdet⟩, had, hrnonneg, by rw [haq]; exact hrlt, ?_⟩
  have hcomb : B = B * (D * Cinv) := by rw [hDCinv, mul_one]
  rw [← Matrix.mul_assoc, hUT, ← haq] at hcomb
  exact hcomb

end SIC

end
