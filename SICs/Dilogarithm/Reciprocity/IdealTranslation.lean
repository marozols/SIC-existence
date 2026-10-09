/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Dilogarithm.Frobenius.SplitLines
import SICs.Dilogarithm.Pseudolattice.Group
import SICs.Dilogarithm.Pseudolattice.Nested

/-!
# Translation of a pseudolattice by a prime generator

For a totally positive `α`, translation identifies the value at `x` on `α⁻¹I` with the value at
`y` on `I` when `αx ≡ y (mod I)`. When `N(α) = p` is a prime not dividing `Tr α`, the translates
`α⁻¹I` and `α'⁻¹I` by `α` and its conjugate `α' = Tr α - α` form a split pair of lines of `I`
at `p`.

This module follows the principal-translation calculation in the proof of
[RW26b, Radchenko, Wheeler (2026b), Section 8, Lemma 8], using the positive-homothety case of
its Appendix B, Proposition 8, for a prime ideal `𝔭 = (α)` of `𝒪_K` with `α ≫ 0` and
`α ≡ 1 (mod M𝒪_K)`. It also follows the description of `𝔭⁻¹I`, `𝔮⁻¹I` at the start of
[RW26b, Radchenko, Wheeler (2026b), Section 7]. It supplies the
signed-generator argument in `SICs.Dilogarithm.Reciprocity.SignedGenerator` with the two inputs of
the split Frobenius congruence `pseudolatticeDilog_frobenius_split`: the lattices are an
`IsSplitLinePair`, and translation by them moves values from `x` to `sx`. The source uses
ideals of the multiplier order `𝒪` prime to its conductor `c` and the order ray class group
`C⁺_𝒪(m)`. Here the rational integer `M` of `IsPeriod.exists_modulus_mul_mem` is a multiple of
`c` and the order of `G_{I,ε}`, and the ideals are principal ideals of `𝒪_K`.

## The argument

*The modulus.* `I` is a full lattice in `K` and `𝒪_K` is finitely generated, so `c𝒪_K I ⊆ I` for
some positive integer `c`; and `N = |G_{I,ε}|` kills `G_{I,ε} = (ε - 1)⁻¹I/I`. With `M = cN`,
`M𝒪_K x ⊆ c𝒪_K(Nx) ⊆ I` for every `x ∈ G_{I,ε}`, in particular for `x ∈ I`.

*The principal translation in Lemma 8.* For `α ≫ 0` with `αx - y ∈ I`, positive homothety by `α⁻¹`
(`pseudolatticeDilog_smul`) gives `E_{α⁻¹I}(x) = E_{α⁻¹I}(α⁻¹·αx) = E_I(αx)`, and
`αx ≡ y (mod I)` gives `E_I(αx) = E_I(y)` (`pseudolatticeDilog_congr`). The source's Bézout
argument for a modulus prime to the conductor is not needed, since `M𝒪_K` already moves
`G_{I,ε}` into `I`.

*The split pair.* Let `αI ⊆ I`, `α'I ⊆ I`, `αα' = N(α) = p` (`sq_eq_trace_mul_sub_norm`), and
`t = Tr α = α + α'` with `p ∤ t`; choose `ut + vp = 1`. Put `J₀ = α⁻¹I`, `J₁ = α'⁻¹I`.
`I ⊆ J_i` since `αI, α'I ⊆ I`. The index `[J₀ : I] = [I : αI] = |N(α)| = p`, the determinant of
multiplication by `α` on a basis of `I`, and likewise for `α'`. If `αy, α'y ∈ I`, then
`ty = αy + α'y` and `py = α'(αy)` lie in `I`, so `y = u(ty) + v(py) ∈ I`: `J₀ ∩ J₁ = I`. If
`py ∈ I`, then `y = uα'y + (uαy + vpy)` with `α(uα'y) = upy ∈ I` and `α'(uαy + vpy) = upy +
vα'(py) ∈ I`: `p⁻¹I ⊆ J₀ + J₁`. Finally `aI ⊆ I` gives `a(α⁻¹I) = α⁻¹(aI) ⊆ α⁻¹I`.
-/

noncomputable section

open scoped MatrixGroups NumberField

namespace SIC

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]

variable {F : RealQuadraticFieldData K} {B : PseudolatticeBasis F} {ε : K}

/-! ### The modulus

An integer `M > 0` with `M𝒪_K x ⊆ I` for every `x ∈ G_{I,ε}`. -/

/-- A positive integer clears the two rational coordinates of an element in the lattice of
`IsPeriod.exists_modulus_mul_mem`. -/
private theorem PseudolatticeBasis.exists_nat_mul_mem (B : PseudolatticeBasis F) (y : K) :
    ∃ n : ℕ, 0 < n ∧ (n : K) * y ∈ B.submodule := by
  let r := B.characteristic y
  obtain ⟨n, hn, hcoords⟩ := exists_natCast_mul_eq_intCast (B.characteristic y)
  refine ⟨n, hn, ?_⟩
  apply (B.mem_submodule_iff _).mpr
  refine ⟨(n : ℚ) • r, ?_, ?_⟩
  · intro i
    obtain ⟨m, hm⟩ := hcoords i
    exact ⟨m, by simpa [r, Pi.smul_apply, smul_eq_mul] using hm⟩
  · rw [fracSymplecticFormRat_smul, B.fracSymplecticFormRat_characteristic]
    push_cast
    field_simp [B.scale_ne_zero]

/-- A common positive integer clears the coordinates of two vectors; used by
`IsPeriod.exists_modulus_mul_mem`. -/
private theorem PseudolatticeBasis.exists_nat_mul_pair_mem (B : PseudolatticeBasis F)
    (y z : K) : ∃ n : ℕ, 0 < n ∧ (n : K) * y ∈ B.submodule ∧
      (n : K) * z ∈ B.submodule := by
  obtain ⟨m, hm, hy⟩ := B.exists_nat_mul_mem y
  obtain ⟨n, hn, hz⟩ := B.exists_nat_mul_mem z
  refine ⟨m * n, Nat.mul_pos hm hn, ?_, ?_⟩
  · have h := B.submodule.smul_mem (n : ℤ) hy
    convert h using 1; simp only [zsmul_eq_mul, Int.cast_natCast, Nat.cast_mul]; ring
  · have h := B.submodule.smul_mem (m : ℤ) hz
    convert h using 1; simp only [zsmul_eq_mul, Int.cast_natCast, Nat.cast_mul]; ring

/-- A common integer sends the products of each integral basis vector with both generators
of `I` into `I`; used by `PseudolatticeBasis.exists_conductor`. -/
private theorem PseudolatticeBasis.exists_conductor_generators (B : PseudolatticeBasis F) :
    ∃ c : ℕ, 0 < c ∧ ∀ i,
      (c : K) * (NumberField.RingOfIntegers.basis K i : K) * (B.scale * B.tau) ∈ B.submodule ∧
      (c : K) * (NumberField.RingOfIntegers.basis K i : K) * B.scale ∈ B.submodule := by
  classical
  let b := NumberField.RingOfIntegers.basis K
  have hgen : ∀ i, ∃ n : ℕ, 0 < n ∧
      (n : K) * (b i : K) * (B.scale * B.tau) ∈ B.submodule ∧
      (n : K) * (b i : K) * B.scale ∈ B.submodule := by
    intro i
    obtain ⟨n, hn, h₀, h₁⟩ := B.exists_nat_mul_pair_mem
      ((b i : K) * (B.scale * B.tau)) ((b i : K) * B.scale)
    exact ⟨n, hn, by simpa only [mul_assoc] using h₀,
      by simpa only [mul_assoc] using h₁⟩
  choose n hn hn₀ hn₁ using hgen
  let c := ∏ i, n i
  have hc : 0 < c := Finset.prod_pos fun i _ => hn i
  have hmultiple (i) : n i ∣ c := by
    simpa [c] using Finset.dvd_prod_of_mem n (Finset.mem_univ i)
  have h₀ (i) : (c : K) * (b i : K) * (B.scale * B.tau) ∈ B.submodule := by
    obtain ⟨k, hk⟩ := hmultiple i
    have h := B.submodule.smul_mem (k : ℤ) (hn₀ i)
    rw [hk]
    convert h using 1; simp only [zsmul_eq_mul, Int.cast_natCast, Nat.cast_mul]; ring
  have h₁ (i) : (c : K) * (b i : K) * B.scale ∈ B.submodule := by
    obtain ⟨k, hk⟩ := hmultiple i
    have h := B.submodule.smul_mem (k : ℤ) (hn₁ i)
    rw [hk]
    convert h using 1; simp only [zsmul_eq_mul, Int.cast_natCast, Nat.cast_mul]; ring
  exact ⟨c, hc, fun i => ⟨h₀ i, h₁ i⟩⟩

/-- It suffices to check the conductor action on the two displayed generators of `I`;
used by `PseudolatticeBasis.exists_conductor`. -/
private theorem PseudolatticeBasis.conductor_on_generators (B : PseudolatticeBasis F)
    (c : ℕ) (a : 𝓞 K)
    (h₀ : (c : K) * (a : K) * (B.scale * B.tau) ∈ B.submodule)
    (h₁ : (c : K) * (a : K) * B.scale ∈ B.submodule)
    (y : K) (hy : y ∈ B.submodule) :
    (c : K) * (a : K) * y ∈ B.submodule := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
      rcases hy with h | h
      · rw [h]; exact h₀
      · rw [h]; exact h₁
  | zero => simp
  | add y z hy hz ihy ihz =>
      convert B.submodule.add_mem ihy ihz using 1; ring
  | smul m y hy ih =>
      convert B.submodule.smul_mem m ih using 1; simp only [zsmul_eq_mul]; ring

/-- A positive rational integer multiplies every product `ax`, with `a ∈ 𝒪_K` and `x ∈ I`,
back into `I`. Used by `IsPeriod.exists_modulus_mul_mem`. -/
private theorem PseudolatticeBasis.exists_conductor (B : PseudolatticeBasis F) :
    ∃ c : ℕ, 0 < c ∧ ∀ a : 𝓞 K, ∀ x ∈ B.submodule,
      (c : K) * (a : K) * x ∈ B.submodule := by
  classical
  let b := NumberField.RingOfIntegers.basis K
  obtain ⟨c, hc, hgen⟩ := B.exists_conductor_generators
  refine ⟨c, hc, ?_⟩
  intro a x hx
  have hbasis (i) : (c : K) * (b i : K) * x ∈ B.submodule :=
    B.conductor_on_generators c (b i) (hgen i).1 (hgen i).2 x hx
  have ha : (a : K) = ∑ i, ((b.repr a i : ℤ) : K) * (b i : K) := by
    have h := congrArg (fun z : 𝓞 K => (z : K)) (b.sum_repr a).symm
    simpa only [map_sum, map_zsmul, zsmul_eq_mul, map_mul, map_intCast] using h
  rw [ha]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Submodule.sum_mem
  intro i _
  have h := B.submodule.smul_mem (b.repr a i) (hbasis i)
  convert h using 1; simp only [zsmul_eq_mul]; ring

/-- **A modulus for the ideal translations of `I`**: a positive integer `M` with
`M𝒪_K x ⊆ I` for every `x` with `(ε - 1)x ∈ I`. It is `cN` for an integer `c > 0` with
`c𝒪_K I ⊆ I` and `N = |G_{I,ε}|`; [RW26b, Radchenko, Wheeler (2026b), Section 8] uses the
conductor `c` of the multiplier order and a multiple `m` of the exponent of `G_{I,ε}`. -/
theorem PseudolatticeBasis.IsPeriod.exists_modulus_mul_mem (h : B.IsPeriod ε) :
    ∃ M : ℕ, 0 < M ∧ ∀ a : 𝓞 K, ∀ x : K, (ε - 1) * x ∈ B.submodule →
      (M : K) * (a : K) * x ∈ B.submodule := by
  obtain ⟨c, hc, hconductor⟩ := B.exists_conductor
  let N := finiteDilogOrder h.matrix
  refine ⟨c * N, Nat.mul_pos hc (finiteDilogOrder_pos h.isAttractiveFixedPoint), ?_⟩
  intro a x hx
  have hNx : (N : K) * x ∈ B.submodule := by
    apply (B.mem_submodule_iff _).mpr
    refine ⟨(N : ℚ) • B.characteristic x, ?_, ?_⟩
    · change IsIntegralIndex (fun i => (N : ℚ) * B.characteristic x i)
      exact h.isIntegralIndex_order_mul_characteristic hx
    · rw [fracSymplecticFormRat_smul, B.fracSymplecticFormRat_characteristic]
      push_cast
      field_simp [B.scale_ne_zero]
  have h := hconductor a ((N : K) * x) hNx
  convert h using 1; simp only [Nat.cast_mul]; ring

/-! ### The principal translation in Lemma 8

Translation by a totally positive `α` moves the value at `x` to the value at `αx`; for
`α ≡ ±1` this is the value at `±x`. -/

/-- **The principal-translation calculation in the proof of
[RW26b, Radchenko, Wheeler (2026b), Section 8, Lemma 8]**, using the first case of its Appendix B,
Proposition 8: if `α ≫ 0` and `αx ≡ y (mod I)` with `y ∈ G_{I,ε}`, then
`E_{α⁻¹I,ε}(x) = E_{I,ε}(y)`. The source states that `E_{𝔞⁻¹I}` depends only on the class of `𝔞`
in `C⁺_𝒪(m)`; at the trivial class `𝔞 = (α)` with `α ≡ 1 (mod M𝒪_K)` and `M` as in
`IsPeriod.exists_modulus_mul_mem`, `αx ≡ x`. For `α ≡ -1`, `αx ≡ -x` gives the class of the
totally negative generator `-α` used in `pseudolatticeDilog_artin_signClass`. -/
@[source "RW26b, Lemma 8, p. 14 (principal ideal (α), α ≫ 0)"]
theorem pseudolatticeDilog_inv_smul (h : B.IsPeriod ε) {α : K} (hα : F.IsTotallyPositive α)
    {x y : K} (hy : (ε - 1) * y ∈ B.submodule) (hαx : α * x - y ∈ B.submodule) :
    pseudolatticeDilog (h.smul α⁻¹ hα.inv) x = pseudolatticeDilog h y := by
  have hα0 := hα.ne_zero
  have heq : α⁻¹ * (α * x) = x := by simp [hα0]
  calc
    _ = pseudolatticeDilog h (α * x) := by
      simpa only [heq] using pseudolatticeDilog_smul h hα.inv (α * x)
    _ = pseudolatticeDilog h y := by
      apply pseudolatticeDilog_congr h hy
      simpa only [neg_sub] using B.submodule.neg_mem hαx

/-! ### The split pair of a prime generator and its conjugate

`α⁻¹I` and `α'⁻¹I` for `N(α) = p`, `p ∤ Tr α`, are the lattices `𝔭⁻¹I`, `𝔮⁻¹I` of
[RW26b, Radchenko, Wheeler (2026b), Section 7]. -/

/-- Multiplication by `a` gives the row coordinates of the basis of `I` in
`a⁻¹I`; used by `PseudolatticeBasis.inv_smul_basis_matrix`. -/
private theorem PseudolatticeBasis.inv_smul_basis_vector (B : PseudolatticeBasis F)
    {a : K} (ha : F.IsTotallyPositive a) {M : Mat(2, ℤ)}
    (hM : IsPairMap M B.tau a B.tau) (i : Fin 2) :
    (B.basis i : K) =
      (M i 0 : K) * ((B.smul a⁻¹ ha.inv).basis 0 : K) +
        (M i 1 : K) * ((B.smul a⁻¹ ha.inv).basis 1 : K) := by
  have ha0 := ha.ne_zero
  fin_cases i
  · simp only [PseudolatticeBasis.coe_basis, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    change B.scale * B.tau = (M 0 0 : K) * ((a⁻¹ * B.scale) * B.tau) +
      (M 0 1 : K) * (a⁻¹ * B.scale)
    calc
      B.scale * B.tau = (a⁻¹ * B.scale) * (a * B.tau) := by field_simp [ha0]
      _ = _ := by rw [← hM.first_row]; ring
  · simp only [PseudolatticeBasis.coe_basis, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    change B.scale = (M 1 0 : K) * ((a⁻¹ * B.scale) * B.tau) +
      (M 1 1 : K) * (a⁻¹ * B.scale)
    calc
      B.scale = (a⁻¹ * B.scale) * a := by field_simp [ha0]
      _ = _ := by rw [← hM.denominator_eq]; simp only [fltDenominator]; ring

/-- The matrix of the inclusion `I ⊆ a⁻¹I` in the displayed bases is the transpose of the
pair map; used by `PseudolatticeBasis.relIndex_inv_smul`. -/
private theorem PseudolatticeBasis.inv_smul_basis_matrix (B : PseudolatticeBasis F)
    {a : K} (ha : F.IsTotallyPositive a)
    (hle : B.submodule ≤ (B.smul a⁻¹ ha.inv).submodule)
    {M : Mat(2, ℤ)} (hM : IsPairMap M B.tau a B.tau) :
    (B.smul a⁻¹ ha.inv).basis.toMatrix
      (fun i => ⟨(B.basis i : K), hle (B.basis i).property⟩) = M.transpose := by
  let J := B.smul a⁻¹ ha.inv
  let v : Fin 2 → J.submodule := fun i =>
    ⟨(B.basis i : K), hle (B.basis i).property⟩
  have hrepr (i : Fin 2) : J.basis.repr (v i) = fun j => M i j := by
    have hv : v i = ∑ j : Fin 2, (M i j) • J.basis j := by
      apply Subtype.ext
      simpa [v, Fin.sum_univ_two, zsmul_eq_mul] using B.inv_smul_basis_vector ha hM i
    rw [hv, J.basis.repr_sum_self]
  have hmatrix : J.basis.toMatrix v = M.transpose := by
    ext i j
    simp [Module.Basis.toMatrix_apply, hrepr j]
  exact hmatrix

/-- The principal case of the index identity in [RW26b, Radchenko, Wheeler (2026b), Section 8]:
`[a⁻¹I : I] = N(a)` for a totally positive multiplier of `I`. Used by
`isSplitLinePair_inv_smul`. -/
theorem PseudolatticeBasis.relIndex_inv_smul (B : PseudolatticeBasis F) {a : K}
    (ha : F.IsTotallyPositive a) (hmem : ∀ x ∈ B.submodule, a * x ∈ B.submodule)
    {m : ℕ} (hnorm : Algebra.norm ℚ a = m) :
    B.submodule.toAddSubgroup.relIndex (B.smul a⁻¹ ha.inv).submodule.toAddSubgroup = m := by
  let J := B.smul a⁻¹ ha.inv
  have ha0 := ha.ne_zero
  have hle : B.submodule ≤ J.submodule := by
    intro x hx
    apply (B.mem_smul_submodule_iff ha.inv x).mpr
    refine ⟨a * x, hmem x hx, ?_⟩
    simp [ha0]
  have hfirst : (a * B.scale) * B.tau ∈ B.submodule := by
    convert hmem (B.scale * B.tau) (Submodule.subset_span (by simp)) using 1; ring
  have hsecond : a * B.scale ∈ B.submodule :=
    hmem B.scale (Submodule.subset_span (by simp))
  obtain ⟨M, hM⟩ := exists_pairMap_of_mem_span B.scale_ne_zero hfirst hsecond
  have hj : (a * B.scale) / B.scale = a := by field_simp [B.scale_ne_zero]
  rw [hj] at hM
  have hdiff : 0 < realEmbeddingAt K F.place B.tau -
      realEmbeddingAt K F.otherPlace B.tau := sub_pos.mpr B.other_lt
  have hdetR : (M.det : ℝ) = realEmbeddingAt K F.place a *
      realEmbeddingAt K F.otherPlace a := by
    exact mul_right_cancel₀ hdiff.ne' (hM.det_mul_sub_eq F)
  have hdetZ : M.det = (m : ℤ) := by
    have h := hdetR.trans (F.mul_realEmbeddingAt_otherPlace_eq_norm a)
    rw [hnorm] at h
    have h' : (M.det : ℝ) = (m : ℝ) := by simpa using h
    exact_mod_cast h'
  let v : Fin 2 → J.submodule := fun i =>
    ⟨(B.basis i : K), hle (B.basis i).property⟩
  have hmatrix : J.basis.toMatrix v = M.transpose :=
    B.inv_smul_basis_matrix ha hle hM
  have hidx := AddSubgroup.relIndex_eq_natAbs_det B.submodule.toAddSubgroup
    J.submodule.toAddSubgroup hle B.basis J.basis
  change B.submodule.toAddSubgroup.relIndex J.submodule.toAddSubgroup =
    (J.basis.det v).natAbs at hidx
  rw [Module.Basis.det_apply, hmatrix, Matrix.det_transpose, hdetZ] at hidx
  simpa using hidx

/-- Membership in `a⁻¹I` is equivalent to membership of `ay` in `I`; used by
`isSplitLinePair_inv_smul`. -/
private theorem PseudolatticeBasis.mem_inv_smul_iff (B : PseudolatticeBasis F) {a : K}
    (ha : F.IsTotallyPositive a) (y : K) :
    y ∈ (B.smul a⁻¹ ha.inv).submodule ↔ a * y ∈ B.submodule := by
  rw [B.mem_smul_submodule_iff ha.inv]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [ha.ne_zero] using hx
  · intro hy
    exact ⟨a * y, hy, by simp [ha.ne_zero]⟩

/-- The two inverse translates meet in `I`, by the Bézout identity for `Tr α` and `p`;
used by `PseudolatticeBasis.split_pair_of_data`. -/
private theorem PseudolatticeBasis.inv_smul_inter_le (B : PseudolatticeBasis F)
    {α δ : K} (hα : F.IsTotallyPositive α) (hδ : F.IsTotallyPositive δ)
    {p : ℕ} {t : ℤ} (hprod : α * δ = (p : K)) (hsum : α + δ = (t : K))
    (hδI : ∀ x ∈ B.submodule, δ * x ∈ B.submodule)
    (u v : ℤ) (huvK : (u : K) * (t : K) + (v : K) * (p : K) = 1) :
    (B.smul α⁻¹ hα.inv).submodule ⊓ (B.smul δ⁻¹ hδ.inv).submodule ≤ B.submodule := by
  let J₀ := B.smul α⁻¹ hα.inv
  let J₁ := B.smul δ⁻¹ hδ.inv
  intro y hy
  have hαy : α * y ∈ B.submodule := (B.mem_inv_smul_iff hα y).mp hy.1
  have hδy : δ * y ∈ B.submodule := (B.mem_inv_smul_iff hδ y).mp hy.2
  have hty : (t : K) * y ∈ B.submodule := by
    have heq : (t : K) * y = α * y + δ * y := by rw [← add_mul, hsum]
    exact heq.symm ▸ B.submodule.add_mem hαy hδy
  have hpy : (p : K) * y ∈ B.submodule := by
    have h := hδI (α * y) hαy
    change δ * (α * y) ∈ B.submodule at h
    have heq : δ * (α * y) = (p : K) * y := by
      rw [← mul_assoc, mul_comm δ α, hprod]
    exact heq ▸ h
  have h := B.submodule.add_mem (B.submodule.smul_mem u hty)
    (B.submodule.smul_mem v hpy)
  have heq : y = u • ((t : K) * y) + v • ((p : K) * y) := by
    simp only [zsmul_eq_mul]
    calc
      y = (1 : K) * y := by ring
      _ = ((u : K) * (t : K) + (v : K) * (p : K)) * y := by rw [huvK]
      _ = _ := by ring
  exact heq.symm ▸ h

/-- Every `y` with `py ∈ I` splits between the two inverse translates; used by
`PseudolatticeBasis.split_pair_of_data`. -/
private theorem PseudolatticeBasis.inv_smul_mem_sup (B : PseudolatticeBasis F)
    {α δ : K} (hα : F.IsTotallyPositive α) (hδ : F.IsTotallyPositive δ)
    {p : ℕ} {t : ℤ} (hprod : α * δ = (p : K)) (hsum : α + δ = (t : K))
    (hδI : ∀ x ∈ B.submodule, δ * x ∈ B.submodule)
    (u v : ℤ) (huvK : (u : K) * (t : K) + (v : K) * (p : K) = 1)
    (y : K) (hpy : (p : K) * y ∈ B.submodule) :
    y ∈ (B.smul α⁻¹ hα.inv).submodule ⊔ (B.smul δ⁻¹ hδ.inv).submodule := by
  let J₀ := B.smul α⁻¹ hα.inv
  let J₁ := B.smul δ⁻¹ hδ.inv
  let y₀ := (u : K) * δ * y
  let y₁ := (u : K) * α * y + (v : K) * (p : K) * y
  have hy₀ : y₀ ∈ J₀.submodule := by
    apply (B.mem_inv_smul_iff hα y₀).mpr
    have h := B.submodule.smul_mem u hpy
    have heq : α * y₀ = u • ((p : K) * y) := by
      dsimp [y₀]
      simp only [zsmul_eq_mul]
      rw [← hprod]
      ring
    exact heq.symm ▸ h
  have hy₁ : y₁ ∈ J₁.submodule := by
    apply (B.mem_inv_smul_iff hδ y₁).mpr
    have hδpy : δ * ((p : K) * y) ∈ B.submodule := hδI ((p : K) * y) hpy
    have h := B.submodule.add_mem (B.submodule.smul_mem u hpy)
      (B.submodule.smul_mem v hδpy)
    have heq : δ * y₁ = u • ((p : K) * y) + v • (δ * ((p : K) * y)) := by
      dsimp [y₁]
      simp only [zsmul_eq_mul]
      rw [← hprod]
      ring
    exact heq.symm ▸ h
  apply Submodule.mem_sup.mpr
  refine ⟨y₀, hy₀, y₁, hy₁, ?_⟩
  dsimp [y₀, y₁]
  calc
    (u : K) * δ * y + ((u : K) * α * y + (v : K) * (p : K) * y) =
        ((u : K) * (α + δ) + (v : K) * (p : K)) * y := by ring
    _ = ((u : K) * (t : K) + (v : K) * (p : K)) * y := by rw [hsum]
    _ = y := by rw [huvK]; ring

/-- The index, intersection, sum, and multiplier conditions for an inverse-translate split
pair; used by `isSplitLinePair_inv_smul`. -/
private theorem PseudolatticeBasis.split_pair_of_data (B : PseudolatticeBasis F)
    {p : ℕ} {α δ : K} (hα : F.IsTotallyPositive α) (hδ : F.IsTotallyPositive δ)
    (hNα : Algebra.norm ℚ α = p) (hNδ : Algebra.norm ℚ δ = p)
    {t : ℤ} (hprod : α * δ = (p : K)) (hsum : α + δ = (t : K))
    (u v : ℤ) (huvK : (u : K) * (t : K) + (v : K) * (p : K) = 1)
    (hαI : ∀ x ∈ B.submodule, α * x ∈ B.submodule)
    (hδI : ∀ x ∈ B.submodule, δ * x ∈ B.submodule) :
    IsSplitLinePair p B.submodule
      ![(B.smul α⁻¹ hα.inv).submodule, (B.smul δ⁻¹ hδ.inv).submodule] := by
  let J₀ := B.smul α⁻¹ hα.inv
  let J₁ := B.smul δ⁻¹ hδ.inv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · intro y hy
      exact (B.mem_inv_smul_iff hα y).mpr (hαI y hy)
    · intro y hy
      exact (B.mem_inv_smul_iff hδ y).mpr (hδI y hy)
  · intro i
    fin_cases i
    · exact B.relIndex_inv_smul hα hαI hNα
    · exact B.relIndex_inv_smul hδ hδI hNδ
  · exact B.inv_smul_inter_le hα hδ hprod hsum hδI u v huvK
  · exact B.inv_smul_mem_sup hα hδ hprod hsum hδI u v huvK
  · intro i a ha y hy
    fin_cases i
    · apply (B.mem_inv_smul_iff hα (a * y)).mpr
      have h := ha (α * y) ((B.mem_inv_smul_iff hα y).mp hy)
      convert h using 1; ring
    · apply (B.mem_inv_smul_iff hδ (a * y)).mpr
      have h := ha (δ * y) ((B.mem_inv_smul_iff hδ y).mp hy)
      convert h using 1; ring

/-- **The translates by a prime generator and its conjugate are a split pair of lines**: if
`α ≫ 0` has norm `N(α) = p` for a prime `p`, its trace `t = Tr α` is an integer prime to `p`,
and `α` and `α' = t - α` preserve `I`, then `α⁻¹I` and `α'⁻¹I` form an `IsSplitLinePair` of `I`
at `p`. These are the lattices `𝔭⁻¹I`, `𝔮⁻¹I` of [RW26b, Radchenko, Wheeler (2026b), Section 7]
for `𝔭 = (α)`, `𝔮 = (α')`, with `p⁻¹I/I = U_𝔭 ⊕ U_𝔮`. -/
theorem isSplitLinePair_inv_smul {p : ℕ} [Fact p.Prime] {α : K} (hα : F.IsTotallyPositive α)
    (hnorm : Algebra.norm ℚ α = p) {t : ℤ} (htr : Algebra.trace ℚ K α = t)
    (hpt : ¬ (p : ℤ) ∣ t) (hαI : ∀ x ∈ B.submodule, α * x ∈ B.submodule)
    (hα'I : ∀ x ∈ B.submodule, ((Algebra.trace ℚ K α : K) - α) * x ∈ B.submodule) :
    IsSplitLinePair p B.submodule fun i =>
      (![B.smul α⁻¹ hα.inv,
        B.smul ((Algebra.trace ℚ K α : K) - α)⁻¹ hα.trace_sub.inv] i).submodule := by
  let δ : K := (Algebra.trace ℚ K α : K) - α
  have hδ : F.IsTotallyPositive δ := hα.trace_sub
  have hprod : α * δ = (p : K) := by
    have hs := sq_eq_trace_mul_sub_norm F.finrank_eq_two α
    rw [hnorm] at hs
    push_cast at hs
    dsimp [δ]
    linear_combination -hs
  have htrK : (Algebra.trace ℚ K α : K) = (t : K) := by exact_mod_cast htr
  have hsum : α + δ = (t : K) := by dsimp [δ]; rw [htrK]; ring
  have hnormδ : Algebra.norm ℚ δ = p := by
    simpa only [δ] using (F.norm_trace_sub α).trans hnorm
  have hbez : ∃ u v : ℤ, u * t + v * (p : ℤ) = 1 := by
    have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
    exact (isCoprime_comm.mp (hp.coprime_iff_not_dvd.mpr hpt))
  obtain ⟨u, v, huv⟩ := hbez
  have huvK : (u : K) * (t : K) + (v : K) * (p : K) = 1 := by exact_mod_cast huv
  have hδI : ∀ x ∈ B.submodule, δ * x ∈ B.submodule := hα'I
  have hpair := B.split_pair_of_data hα hδ hnorm hnormδ hprod hsum u v huvK hαI hδI
  convert hpair using 1
  funext i
  fin_cases i <;> rfl

end SIC

end
