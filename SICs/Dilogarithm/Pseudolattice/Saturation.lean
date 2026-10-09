/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Analysis.CharacterSums
import SICs.Dilogarithm.Pseudolattice.GroupMaps
import SICs.Dilogarithm.Pseudolattice.Nested
import SICs.Dilogarithm.Pseudolattice.Powers
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Chains of pseudolattices along a character

For a character `Ψ` of `K` trivial on a pseudolattice `I` with period `ε`, the lattices
`I_i = {x ∈ (ε - 1)^{-i}I : Ψ(ε^k x) = 1 for all k ≥ 0}` form a chain `I = I_0 ⊆ I_1 ⊆ ⋯` with
`(ε - 1)I_{i+1} ⊆ I_i` and period `ε`; when `p ∣ N` and `Ψ` is nondegenerate, the `p`-torsion of
`G_{I_i,ε}` has order `p` for large `i` and `Ψ` is nontrivial on it. Every character of `G_{I,ε}`
is induced by a nondegenerate `Ψ`.

This module follows [RW26b, Radchenko, Wheeler (2026b), Section 5, Lemma 3], without trace
duals: for the character `x ↦ e(Tr(ax))` of the source, `I_i = M_i^∨` with
`M_i = aℤ[ε] + (ε - 1)^i M` is the lattice above, and the characters `θ_i` are induced by the
single character `Ψ`. The source's cyclicity statement is replaced by what the proof of
Theorem 5 uses: `|G_{I_i,ε}[p]| = p` and `Ψ` nontrivial on `G_{I_i,ε}[p]`. Nondegeneracy of `Ψ`
means that `A_Ψ = {x : Ψ(ε^k x) = 1 for all k}` lies in `n⁻¹I` for some `n ≠ 0`; for the
trivial character of `G_{I,ε}` the source takes `a ∈ (ε - 1)M` nonzero, which is a nondegenerate
`Ψ` inducing the trivial character.

## The argument

*The chain.* `I_i` is a subgroup since `Ψ` is a character, and `ε`-stable since
`ε⁻¹ = Tr ε - ε`. `I_0 = I` because `Ψ` is trivial on the `ε`-stable `I`; `I_i ⊆ I_{i+1}` since
`(ε - 1)I ⊆ I`; and for `x ∈ I_{i+1}`, `Ψ(ε^k(ε - 1)x) = Ψ(ε^{k+1}x)/Ψ(ε^k x) = 1`, so
`(ε - 1)I_{i+1} ⊆ I_i`. As `(ε - 1)² = Nε`, `I_i ⊆ N^{-i}I`, so `I_i` has an admissible basis
(`exists_submodule_eq`), and `ε` is a period of `I_{i+1}` by `IsPeriod.of_le` from `I_i`.

*Faithfulness.* Put `A = A_Ψ ⊇ I`. If `x ∈ (ε - 1)⁻¹A` and `Ψ(x) = 1`, then
`Ψ(ε^{k+1}x) = Ψ(ε^k x)` for all `k`, so `x ∈ A`: `Ψ` is faithful on `G_{A,ε}`. For `i = 2j`,
`I_i = A ∩ N^{-j}I`. If `A ⊆ n⁻¹I` and `p^e ∥ n`, then for `j ≥ e` the index `[A : I_i]` is prime
to `p`: an element `x ∈ A` has `nx ∈ I`, and with `n = p^e m`, `mx ∈ p^{-e}I ⊆ N^{-j}I`. Hence an
element of `G_{I_i,ε}[p]` with `Ψ(x) = 1` lies in `A`, then in `I_i`: `Ψ` is injective on
`G_{I_i,ε}[p]`, which therefore has at most `p` elements; it has at least `p` by Cauchy's theorem,
since `p ∣ N = |G_{I_i,ε}|`.

*Extension.* In characteristic coordinates `x = β₂(r₁τ - r₀)`, the characters
`Ψ_s(x) = e(s₀r₀ + s₁r₁)`, `s ∈ ℤ²`, are trivial on `I`, and on `G_{I,ε} ⊆ (ℤ/N)²` they restrict
to `ρ ↦ e((s · ρ)/N)`, which give every character of `G_{I,ε}` (characters of `(ℤ/N)²` restrict
onto those of a subgroup). If `s = 0`, replace it with `N(1, 0)`; this keeps the restriction and
makes `s ≠ 0`. Then `A_{Ψ_s}` lies in the set where the two linear forms `s · r(x)` and
`s · r(εx)` are integral; they are independent because `ε ∉ ℚ` has no rational eigenvector,
so `A_{Ψ_s} ⊆ n⁻¹I`
with `n` the square of the absolute determinant of the two forms.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
variable {F : RealQuadraticFieldData K}

namespace PseudolatticeBasis

/-! ### The chain of lattices

`I_i = {x ∈ (ε - 1)^{-i}I : Ψ(ε^k x) = 1 for all k}`. -/

/-- **The lattice `I_i`** of [RW26b, Radchenko, Wheeler (2026b), Section 5, proof of Lemma 3]
for the character `Ψ`: `{x ∈ (ε - 1)^{-i}I : Ψ(ε^k x) = 1 for all k ≥ 0}`, the dual of
`M_i = aℤ[ε] + (ε - 1)^i M` when `Ψ = e(Tr(a ·))`. -/
def saturation (B : PseudolatticeBasis F) (ε : K) (Ψ : AddChar K ℂ) (i : ℕ) :
    Submodule ℤ K where
  carrier := {x | (ε - 1) ^ i * x ∈ B.submodule ∧ ∀ k : ℕ, Ψ (ε ^ k * x) = 1}
  add_mem' := by
    intro x y hx hy
    refine ⟨?_, ?_⟩
    · simpa only [mul_add] using B.submodule.add_mem hx.1 hy.1
    · intro k
      simp only [mul_add, Ψ.map_add_eq_mul, hx.2 k, hy.2 k, one_mul]
  zero_mem' := by
    refine ⟨by simp, ?_⟩
    intro k
    simp
  smul_mem' := by
    intro z x hx
    refine ⟨?_, ?_⟩
    · simpa only [zsmul_eq_mul, mul_left_comm, mul_assoc] using
        B.submodule.smul_mem z hx.1
    · intro k
      rw [show ε ^ k * (z • x) = z • (ε ^ k * x) by
        simp only [zsmul_eq_mul]; ring, Ψ.map_zsmul_eq_zpow, hx.2 k]
      simp

variable {B : PseudolatticeBasis F} {ε : K} {Ψ : AddChar K ℂ}

/-- Membership in `I_i`. -/
theorem mem_saturation {i : ℕ} {x : K} :
    x ∈ B.saturation ε Ψ i ↔ (ε - 1) ^ i * x ∈ B.submodule ∧ ∀ k : ℕ, Ψ (ε ^ k * x) = 1 :=
  Iff.rfl

/-- A character faithful on the $p$-torsion bounds that torsion by the $p$ roots of unity;
this supplies the upper bound in `exists_card_torsion_eq`. -/
private theorem card_p_torsion_le {G : Type*} [AddCommGroup G] [Finite G]
    {p : ℕ} [NeZero p] (χ : AddChar G ℂ)
    (hfaith : ∀ g : G, p • g = 0 → χ g = 1 → g = 0) :
    Nat.card {g : G // p • g = 0} ≤ p := by
  let T := {g : G // p • g = 0}
  let f : T → rootsOfUnity p ℂ := fun g =>
    ⟨Units.mk0 (χ g.1) (χ.val_isUnit g.1).ne_zero,
      (mem_rootsOfUnity p _).mpr (by
        apply Units.ext
        have hpow : χ g.1 ^ p = 1 := by
          rw [← χ.map_nsmul_eq_pow, g.2]
          exact χ.map_zero_eq_one
        simpa using hpow)⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hchar : χ a.1 = χ b.1 := by
      have hh := congrArg (fun z : rootsOfUnity p ℂ => ((z : ℂˣ) : ℂ)) hab
      simpa only [f, Units.val_mk0] using hh
    have hdiff : χ (a.1 - b.1) = 1 := by
      rw [χ.map_sub_eq_div, hchar, div_self (χ.val_isUnit b.1).ne_zero]
    have hpab : p • (a.1 - b.1) = 0 := by rw [smul_sub, a.2, b.2, sub_self]
    exact Subtype.ext (sub_eq_zero.mp (hfaith _ hpab hdiff))
  calc
    Nat.card T ≤ Nat.card (rootsOfUnity p ℂ) := Nat.card_le_card_of_injective f hf
    _ = p := Complex.card_rootsOfUnity p

/-- Cauchy's theorem supplies at least $p$ elements of $p$-torsion when $p$ divides the
group order; this supplies the lower bound in `exists_card_torsion_eq`. -/
private theorem prime_le_card_p_torsion {G : Type*} [AddCommGroup G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hp : p ∣ Nat.card G) :
    p ≤ Nat.card {g : G // p • g = 0} := by
  let T : AddSubgroup G := (nsmulAddMonoidHom p).ker
  obtain ⟨g, hg⟩ := exists_prime_addOrderOf_dvd_card' p hp
  have hpg : g ∈ T := (addOrderOf_dvd_iff_nsmul_eq_zero).mp (by rw [hg])
  let t : T := ⟨g, hpg⟩
  have ht : addOrderOf t = p := (AddSubgroup.addOrderOf_mk g hpg).trans hg
  have hdiv : p ∣ Nat.card T := ht ▸ addOrderOf_dvd_natCard t
  have hle : p ≤ Nat.card T := Nat.le_of_dvd Nat.card_pos hdiv
  exact hle

/-- The integral linear form $s\cdot r(x)$ in characteristic coordinates; this is used in
`exists_inducedChar_eq`. -/
private def coordinateForm (B : PseudolatticeBasis F) (s : Fin 2 → ℤ) (x : K) : ℚ :=
  (s 0 : ℚ) * B.characteristic x 0 + (s 1 : ℚ) * B.characteristic x 1

/-- The explicit character $x\mapsto e(s\cdot r(x))$ used in
`exists_inducedChar_eq`. -/
private def coordinateChar (B : PseudolatticeBasis F) (s : Fin 2 → ℤ) : AddChar K ℂ where
  toFun x := Complex.exp (2 * Real.pi * Complex.I * (B.coordinateForm s x : ℂ))
  map_zero_eq_one' := by simp [coordinateForm]
  map_add_eq_mul' x y := by
    have hf : B.coordinateForm s (x + y) =
        B.coordinateForm s x + B.coordinateForm s y := by
      simp only [coordinateForm, B.characteristic_add, Pi.add_apply]
      ring
    simp only [hf, Rat.cast_add]
    rw [show 2 * Real.pi * Complex.I *
        ((B.coordinateForm s x : ℂ) + (B.coordinateForm s y : ℂ)) =
        2 * Real.pi * Complex.I * (B.coordinateForm s x : ℂ) +
          2 * Real.pi * Complex.I * (B.coordinateForm s y : ℂ) by ring,
      Complex.exp_add]

/-- The residue coordinate character with integral lifts of its coefficients, used in
`exists_inducedChar_eq`. -/
private noncomputable def integralCoordinateChar (N : ℕ) [NeZero N] (s : Fin 2 → ℤ) :
    AddChar (Fin 2 → ZMod N) ℂ :=
  residueCoordinateChar N (fun i => (s i : ZMod N))

/-- Every residue character has integral coordinate coefficients;
this supplies the explicit extension in `exists_inducedChar_eq`. -/
private theorem exists_integralCoordinateChar (N : ℕ) [NeZero N]
    (χ : AddChar (Fin 2 → ZMod N) ℂ) :
    ∃ s : Fin 2 → ℤ, χ = integralCoordinateChar N s := by
  obtain ⟨c, hc⟩ := exists_residueCoordinateChar N χ
  let s : Fin 2 → ℤ := fun i => (c i).val
  refine ⟨s, ?_⟩
  have hs : (fun i => (s i : ZMod N)) = c := by
    funext i
    simp [s]
  change χ = residueCoordinateChar N (fun i => (s i : ZMod N))
  rwa [hs]

/-- The coordinate character is trivial on the pseudolattice $I$;
this is used in `exists_inducedChar_eq`. -/
private theorem coordinateChar_eq_one_of_mem (s : Fin 2 → ℤ) {x : K}
    (hx : x ∈ B.submodule) : B.coordinateChar s x = 1 := by
  obtain ⟨z₀, hz₀⟩ := ((B.isIntegralIndex_characteristic_iff x).mpr hx) 0
  obtain ⟨z₁, hz₁⟩ := ((B.isIntegralIndex_characteristic_iff x).mpr hx) 1
  change Complex.exp (2 * Real.pi * Complex.I * (B.coordinateForm s x : ℂ)) = 1
  apply (exp_two_pi_I_ratCast_eq_one_iff _).mpr
  refine ⟨s 0 * z₀ + s 1 * z₁, ?_⟩
  simp only [coordinateForm, hz₀, hz₁]
  push_cast
  ring

/-- Two nonzero rational vectors in the kernel of one nonzero linear form on $\mathbb Q^2$
are proportional; this is used in `coordinatePair_kernel`. -/
private theorem proportional_of_linear_kernel {s r t : Fin 2 → ℚ}
    (hs : s ≠ 0) (hr : r ≠ 0)
    (hsr : s 0 * r 0 + s 1 * r 1 = 0)
    (hst : s 0 * t 0 + s 1 * t 1 = 0) :
    ∃ q : ℚ, t = q • r := by
  have hsne : s 0 ≠ 0 ∨ s 1 ≠ 0 := by
    by_contra hh
    push Not at hh
    apply hs
    funext i
    fin_cases i <;> simp [hh.1, hh.2]
  have hc : t 0 * r 1 = t 1 * r 0 := by
    rcases hsne with hs₀ | hs₁
    · have hh : s 0 * (t 0 * r 1 - t 1 * r 0) = 0 := by
        linear_combination r 1 * hst - t 1 * hsr
      exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hs₀)
    · have hh : s 1 * (t 0 * r 1 - t 1 * r 0) = 0 := by
        linear_combination t 0 * hsr - r 0 * hst
      exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hs₁)
  by_cases hr₀ : r 0 = 0
  · have hr₁ : r 1 ≠ 0 := by
      intro he
      apply hr
      funext i
      fin_cases i <;> simp [hr₀, he]
    have ht₀ : t 0 = 0 := (mul_eq_zero.mp (by simpa [hr₀] using hc)).resolve_right hr₁
    refine ⟨t 1 / r 1, ?_⟩
    funext i
    fin_cases i
    · simp [hr₀, ht₀]
    · simp only [Pi.smul_apply, smul_eq_mul]
      field_simp [hr₁]
      rfl
  · refine ⟨t 0 / r 0, ?_⟩
    funext i
    fin_cases i
    · simp only [Pi.smul_apply, smul_eq_mul]
      field_simp [hr₀]
      rfl
    · simp only [Pi.smul_apply, smul_eq_mul]
      field_simp [hr₀]
      simpa using hc.symm

/-- Two integral linear forms with integral values force a squared-determinant multiple
of each coordinate to be integral; this is used in `coordinateChar_nondegenerate`. -/
private theorem integral_coordinates_of_forms (s t : Fin 2 → ℤ) (r : Fin 2 → ℚ)
    {z₀ z₁ : ℤ}
    (h₀ : (s 0 : ℚ) * r 0 + (s 1 : ℚ) * r 1 = z₀)
    (h₁ : (t 0 : ℚ) * r 0 + (t 1 : ℚ) * r 1 = z₁) :
    ∀ i : Fin 2, ∃ z : ℤ,
      (((s 0 * t 1 - s 1 * t 0).natAbs *
        (s 0 * t 1 - s 1 * t 0).natAbs : ℕ) : ℚ) * r i = z := by
  let D : ℤ := s 0 * t 1 - s 1 * t 0
  let w : Fin 2 → ℤ := ![t 1 * z₀ - s 1 * z₁, s 0 * z₁ - t 0 * z₀]
  have hw (i : Fin 2) : (D : ℚ) * r i = (w i : ℚ) := by
    fin_cases i
    · simp only [w]
      dsimp [D]
      push_cast
      linear_combination (t 1 : ℚ) * h₀ - (s 1 : ℚ) * h₁
    · simp only [w]
      dsimp [D]
      push_cast
      linear_combination (s 0 : ℚ) * h₁ - (t 0 : ℚ) * h₀
  intro i
  refine ⟨D * w i, ?_⟩
  have hn : ((D.natAbs * D.natAbs : ℕ) : ℚ) = (D : ℚ) * D := by
    have hh := congrArg (fun z : ℤ => (z : ℚ)) (Int.natAbs_mul_self (a := D))
    simpa only [Int.cast_natCast, Int.cast_mul] using hh
  change ((D.natAbs * D.natAbs : ℕ) : ℚ) * r i = (D * w i : ℤ)
  rw [hn, mul_assoc, hw]
  push_cast
  ring

/-- `(ε - 1)I_{i+1} ⊆ I_i`. -/
theorem mul_mem_saturation {i : ℕ} {x : K} (hx : x ∈ B.saturation ε Ψ (i + 1)) :
    (ε - 1) * x ∈ B.saturation ε Ψ i := by
  rw [mem_saturation] at hx ⊢
  refine ⟨?_, ?_⟩
  · convert hx.1 using 1; ring
  · intro k
    have he : ε ^ k * ((ε - 1) * x) = ε ^ (k + 1) * x - ε ^ k * x := by
      rw [pow_succ']
      ring
    rw [he, Ψ.map_sub_eq_div, hx.2 (k + 1), hx.2 k, div_self (one_ne_zero)]

namespace IsPeriod

variable (h : B.IsPeriod ε)
include h

/-- `I_0 = I` for a character `Ψ` trivial on `I`. -/
theorem saturation_zero (hΨ : ∀ x ∈ B.submodule, Ψ x = 1) : B.saturation ε Ψ 0 = B.submodule := by
  ext x
  simp only [mem_saturation, pow_zero, one_mul]
  refine ⟨And.left, fun hx => ⟨hx, ?_⟩⟩
  intro k
  have hpow : ∀ j : ℕ, ε ^ j * x ∈ B.submodule := by
    intro j
    induction j with
    | zero => simpa using hx
    | succ j hj => simpa only [pow_succ', mul_assoc] using h.mul_mem hj
  exact hΨ _ (hpow k)

/-- `I_i ⊆ I_{i+1}`. -/
theorem saturation_le_succ (i : ℕ) : B.saturation ε Ψ i ≤ B.saturation ε Ψ (i + 1) := by
  intro x hx
  rw [mem_saturation] at hx ⊢
  refine ⟨?_, hx.2⟩
  rw [pow_succ]
  convert B.submodule.sub_mem (h.mul_mem hx.1) hx.1 using 1; ring

/-- Every `I_i` has an admissible basis with period `ε`. -/
theorem exists_saturation_eq (hΨ : ∀ x ∈ B.submodule, Ψ x = 1) (i : ℕ) :
    ∃ B' : PseudolatticeBasis F, B'.submodule = B.saturation ε Ψ i ∧ B'.IsPeriod ε := by
  induction i with
  | zero => exact ⟨B, (h.saturation_zero hΨ).symm, h⟩
  | succ i ih =>
      obtain ⟨C, hC, hCper⟩ := ih
      have hle : C.submodule ≤ B.saturation ε Ψ (i + 1) := by
        rw [hC]
        exact h.saturation_le_succ i
      have hbound : ∀ x ∈ B.saturation ε Ψ (i + 1),
          (finiteDilogOrder h.matrix : K) * x ∈ C.submodule := by
        intro x hx
        have hdiff : (ε - 1) * x ∈ C.submodule := by
          rw [hC]
          exact B.mul_mem_saturation hx
        have hdiff2 : (ε - 1) * ((ε - 1) * x) ∈ C.submodule := by
          convert C.submodule.sub_mem (hCper.mul_mem hdiff) hdiff using 1; ring
        have hN : (finiteDilogOrder h.matrix : K) * (ε * x) ∈ C.submodule := by
          convert hdiff2 using 1
          rw [← mul_assoc, ← h.sub_one_sq]
          ring
        convert hCper.inv_mul_mem hN using 1
        field_simp [h.ne_zero]
      have hpos := finiteDilogOrder_pos h.isAttractiveFixedPoint
      obtain ⟨C', hC'⟩ := C.exists_submodule_eq hle hpos.ne' hbound
      refine ⟨C', hC', ?_⟩
      apply hCper.of_le
      · rw [hC']; exact hle
      · intro y hy
        rw [hC'] at hy
        rw [hC]
        exact B.mul_mem_saturation hy

/-! ### The `p`-torsion at the end of the chain

`|G_{I_i,ε}[p]| = p` and `Ψ` nontrivial on it for large `i`. -/

/-- The common-kernel lattice $A_\Psi$ of the characters $x \mapsto \Psi(\varepsilon^k x)$,
used in `exists_card_torsion_eq`. -/
private def orbitKernel (ε : K) (Ψ : AddChar K ℂ) : Submodule ℤ K where
  carrier := {x | ∀ k : ℕ, Ψ (ε ^ k * x) = 1}
  add_mem' := by
    intro x y hx hy k
    simp only [mul_add, Ψ.map_add_eq_mul, hx k, hy k, one_mul]
  zero_mem' := by intro k; simp
  smul_mem' := by
    intro z x hx k
    rw [show ε ^ k * (z • x) = z • (ε ^ k * x) by
      simp only [zsmul_eq_mul]; ring, Ψ.map_zsmul_eq_zpow, hx k]
    simp

/-- Multiplication by a power of the period preserves membership in the original lattice;
this is used in `mem_saturation_even_iff`. -/
private theorem pow_mul_mem_iff (j : ℕ) (x : K) :
    ε ^ j * x ∈ B.submodule ↔ x ∈ B.submodule := by
  induction j with
  | zero => simp
  | succ j ih =>
      calc
        ε ^ (j + 1) * x ∈ B.submodule ↔ ε * (ε ^ j * x) ∈ B.submodule := by
          rw [pow_succ']; simp only [mul_assoc]
        _ ↔ ε ^ j * x ∈ B.submodule := by
          constructor
          · intro hx
            have hinv := h.inv_mul_mem hx
            simpa only [← mul_assoc, inv_mul_cancel₀ h.ne_zero, one_mul] using hinv
          · exact h.mul_mem
        _ ↔ x ∈ B.submodule := ih

/-- The equation $(\varepsilon-1)^{2j}=N^j\varepsilon^j$ used in
`mem_saturation_even_iff`. -/
private theorem sub_one_pow_even (j : ℕ) :
    (ε - 1) ^ (2 * j) = (finiteDilogOrder h.matrix : K) ^ j * ε ^ j := by
  calc
    (ε - 1) ^ (2 * j) = ((ε - 1) ^ 2) ^ j := by rw [pow_mul]
    _ = ((finiteDilogOrder h.matrix : K) * ε) ^ j := by rw [h.sub_one_sq]
    _ = (finiteDilogOrder h.matrix : K) ^ j * ε ^ j := mul_pow ..

/-- At even steps, $I_{2j}=A_\Psi\cap N^{-j}I$, as used in
`exists_card_torsion_eq`. -/
private theorem mem_saturation_even_iff (j : ℕ) (x : K) :
    x ∈ B.saturation ε Ψ (2 * j) ↔
      x ∈ orbitKernel ε Ψ ∧ (finiteDilogOrder h.matrix : K) ^ j * x ∈ B.submodule := by
  rw [mem_saturation, h.sub_one_pow_even]
  change (_ ∧ x ∈ orbitKernel ε Ψ) ↔ _
  constructor
  · rintro ⟨hx, hA⟩
    refine ⟨hA, ?_⟩
    apply (h.pow_mul_mem_iff j _).mp
    simpa only [mul_left_comm, mul_assoc] using hx
  · rintro ⟨hA, hx⟩
    refine ⟨?_, hA⟩
    simpa only [mul_left_comm, mul_assoc] using (h.pow_mul_mem_iff j _).mpr hx

omit [NumberField K] [NumberField.IsTotallyReal K] h in
/-- The character is faithful on $(\varepsilon-1)^{-1}A_\Psi/A_\Psi$; used in
`exists_card_torsion_eq`. -/
private theorem mem_orbitKernel_of_sub_one_mul {x : K}
    (hx : (ε - 1) * x ∈ orbitKernel ε Ψ) (hchar : Ψ x = 1) :
    x ∈ orbitKernel ε Ψ := by
  intro k
  induction k with
  | zero => simpa using hchar
  | succ k ih =>
      have hstep := hx k
      have he : ε ^ k * ((ε - 1) * x) = ε ^ (k + 1) * x - ε ^ k * x := by
        rw [pow_succ']; ring
      rw [he, Ψ.map_sub_eq_div, ih, div_one] at hstep
      exact hstep

/-- The prime-to-$p$ factor of $n$ takes $A_\Psi$ into $I_{2n}$ when $p\mid N$;
this is the index step in `exists_card_torsion_eq`. -/
private theorem ordCompl_mul_mem_saturation {p n : ℕ} [Fact p.Prime]
    (hp : p ∣ finiteDilogOrder h.matrix) (hn : n ≠ 0)
    (hbound : ∀ x ∈ orbitKernel ε Ψ, (n : K) * x ∈ B.submodule)
    {x : K} (hx : x ∈ orbitKernel ε Ψ) :
    ((ordCompl[p] n : ℕ) : K) * x ∈ B.saturation ε Ψ (2 * n) := by
  have hdiv : ordProj[p] n ∣ (finiteDilogOrder h.matrix) ^ n := by
    exact (pow_dvd_pow p (Nat.factorization_lt p hn).le).trans
      (pow_dvd_pow_of_dvd hp n)
  obtain ⟨t, ht⟩ := hdiv
  have hnum : (finiteDilogOrder h.matrix) ^ n * ordCompl[p] n = t * n := by
    calc
      (finiteDilogOrder h.matrix) ^ n * ordCompl[p] n =
          (ordProj[p] n * t) * ordCompl[p] n := by rw [ht]
      _ = t * (ordProj[p] n * ordCompl[p] n) := by ring
      _ = t * n := by rw [Nat.ordProj_mul_ordCompl_eq_self]
  have hnumK : (finiteDilogOrder h.matrix : K) ^ n * ((ordCompl[p] n : ℕ) : K) =
      (t : K) * (n : K) := by
    simpa only [Nat.cast_mul, Nat.cast_pow] using
      congrArg (fun z : ℕ => (z : K)) hnum
  apply (h.mem_saturation_even_iff n _).mpr
  constructor
  · intro k
    calc
      Ψ (ε ^ k * (((ordCompl[p] n : ℕ) : K) * x)) =
          Ψ (ordCompl[p] n • (ε ^ k * x)) := by
            congr 1
            simp only [nsmul_eq_mul]
            ring
      _ = Ψ (ε ^ k * x) ^ ordCompl[p] n := Ψ.map_nsmul_eq_pow ..
      _ = 1 := by rw [hx k, one_pow]
  · have htmem := B.submodule.smul_mem (t : ℤ) (hbound x hx)
    convert htmem using 1
    simp only [zsmul_eq_mul, Int.cast_natCast]
    rw [← mul_assoc, ← mul_assoc, hnumK]

/-- On $G_{I_{2n},\varepsilon}[p]$, the character induced by $\Psi$ has trivial kernel;
this is the faithfulness step in `exists_card_torsion_eq`. -/
private theorem inducedChar_faithful_on_p_torsion {p n : ℕ} [Fact p.Prime]
    (hp : p ∣ finiteDilogOrder h.matrix) (hn : n ≠ 0)
    (hbound : ∀ x ∈ orbitKernel ε Ψ, (n : K) * x ∈ B.submodule)
    (B' : PseudolatticeBasis F) (h' : B'.IsPeriod ε)
    (hEq : B'.submodule = B.saturation ε Ψ (2 * n))
    (hΨ' : ∀ x ∈ B'.submodule, Ψ x = 1)
    (g : finiteDilogGroup h'.matrix) (hpg : p • g = 0)
    (hchar : h'.inducedChar Ψ hΨ' g = 1) : g = 0 := by
  obtain ⟨x, hx⟩ := h'.residueHom_surjective g
  have hdiffA : (ε - 1) * (x : K) ∈ orbitKernel ε Ψ := by
    have hs : (ε - 1) * (x : K) ∈ B.saturation ε Ψ (2 * n) := by
      rw [← hEq]
      exact x.property
    exact (mem_saturation.mp hs).2
  have hcharx : Ψ (x : K) = 1 := by
    rw [← h'.inducedChar_residueHom Ψ hΨ' x, hx]
    exact hchar
  have hA : (x : K) ∈ orbitKernel ε Ψ :=
    mem_orbitKernel_of_sub_one_mul hdiffA hcharx
  have hmx : ((ordCompl[p] n : ℕ) : K) * (x : K) ∈ B'.submodule := by
    rw [hEq]
    exact h.ordCompl_mul_mem_saturation hp hn hbound hA
  have hmg : ordCompl[p] n • g = 0 := by
    rw [← hx]
    exact (h'.residueHom_nsmul_eq_zero_iff x _).mpr hmx
  have horderp : addOrderOf g ∣ p := (addOrderOf_dvd_iff_nsmul_eq_zero).mpr hpg
  have horderm : addOrderOf g ∣ ordCompl[p] n :=
    (addOrderOf_dvd_iff_nsmul_eq_zero).mpr hmg
  have hcop : Nat.gcd p (ordCompl[p] n) = 1 :=
    Nat.coprime_ordCompl Fact.out hn
  have hone : addOrderOf g = 1 := Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd horderp horderm)
  exact (AddMonoid.addOrderOf_eq_one_iff).mp hone

omit h in
/-- A prime divisor of the finite dilogarithm order divides the group cardinality;
this is used in `exists_card_torsion_eq`. -/
private theorem prime_dvd_card_group {B' : PseudolatticeBasis F} (h' : B'.IsPeriod ε)
    {p : ℕ} (hp : p ∣ finiteDilogOrder h'.matrix) :
    p ∣ Nat.card (finiteDilogGroup h'.matrix) := by
  have : NeZero (finiteDilogOrder h'.matrix) :=
    finiteDilogOrder_neZero h'.isAttractiveFixedPoint
  have hcard : Nat.card (finiteDilogGroup h'.matrix) =
      finiteDilogOrder h'.matrix := by
    rw [Nat.card_eq_fintype_card]
    exact card_fixedCharacteristics h'.matrix _
      (det_sub_one_eq_neg_finiteDilogOrder h'.isAttractiveFixedPoint)
  rw [hcard]
  exact hp

omit h in
/-- A nonzero $p$-torsion class on which the induced character is faithful gives
the witness in `exists_card_torsion_eq`. -/
private theorem exists_nontrivial_p_torsion {B' : PseudolatticeBasis F} (h' : B'.IsPeriod ε)
    {p : ℕ} [Fact p.Prime] (hΨ' : ∀ x ∈ B'.submodule, Ψ x = 1)
    (hpG : p ∣ Nat.card (finiteDilogGroup h'.matrix))
    (hfaith : ∀ g : finiteDilogGroup h'.matrix, p • g = 0 →
      h'.inducedChar Ψ hΨ' g = 1 → g = 0) :
    ∃ x : K, (ε - 1) * x ∈ B'.submodule ∧ (p : K) * x ∈ B'.submodule ∧ Ψ x ≠ 1 := by
  have : NeZero (finiteDilogOrder h'.matrix) :=
    finiteDilogOrder_neZero h'.isAttractiveFixedPoint
  obtain ⟨g, hg⟩ := exists_prime_addOrderOf_dvd_card' p hpG
  have hpg : p • g = 0 := (addOrderOf_dvd_iff_nsmul_eq_zero).mp (by rw [hg])
  obtain ⟨x, hx⟩ := h'.residueHom_surjective g
  have hpx : (p : K) * (x : K) ∈ B'.submodule := by
    exact (h'.residueHom_nsmul_eq_zero_iff x p).mp (by simpa only [hx] using hpg)
  refine ⟨x, x.property, hpx, ?_⟩
  intro hcharx
  have hχg : h'.inducedChar Ψ hΨ' g = 1 := by
    rw [← hx, h'.inducedChar_residueHom]
    exact hcharx
  have hz := hfaith g hpg hχg
  have horder : addOrderOf g = 1 := by rw [hz]; simp
  exact (Fact.out : Nat.Prime p).ne_one (hg.symm.trans horder)

/-- **[RW26b, Radchenko, Wheeler (2026b), Section 5, Lemma 3], the end of the chain**: if
`p ∣ N` and `Ψ` is nondegenerate (`A_Ψ ⊆ n⁻¹I`), then for some `i`, every
admissible basis of `I_i` with period `ε` has `|G_{I_i,ε}[p]| = p`, and some `x` with
`(ε - 1)x ∈ I_i` and `px ∈ I_i` has `Ψ(x) ≠ 1`. The source's chain is the saturation sequence
`I_i`, its compatible characters are those induced by `Ψ`
(`inducedChar_compAddMonoidHom_inclusionHom`), cyclicity of the final `p`-primary part is
`|G[p]| = p`, and faithfulness on it is a value `Ψ(x) ≠ 1` on `G[p]`. -/
@[source "RW26b, Lemma 3, p. 8"]
theorem exists_card_torsion_eq {p : ℕ} [Fact p.Prime] (hp : p ∣ finiteDilogOrder h.matrix)
    (hdeg : ∃ n : ℕ, n ≠ 0 ∧ ∀ x : K, (∀ k : ℕ, Ψ (ε ^ k * x) = 1) → (n : K) * x ∈ B.submodule) :
    ∃ i : ℕ, ∀ (B' : PseudolatticeBasis F) (h' : B'.IsPeriod ε),
      B'.submodule = B.saturation ε Ψ i →
        Nat.card {g : finiteDilogGroup h'.matrix // p • g = 0} = p ∧
          ∃ x : K, (ε - 1) * x ∈ B'.submodule ∧ (p : K) * x ∈ B'.submodule ∧ Ψ x ≠ 1 := by
  obtain ⟨n, hn, hbound⟩ := hdeg
  refine ⟨2 * n, ?_⟩
  intro B' h' hEq
  have hΨ' : ∀ x ∈ B'.submodule, Ψ x = 1 := by
    intro x hx
    rw [hEq] at hx
    simpa using (mem_saturation.mp hx).2 0
  let χ := h'.inducedChar Ψ hΨ'
  have hfaith (g : finiteDilogGroup h'.matrix) (hpg : p • g = 0)
      (hχ : χ g = 1) : g = 0 :=
    h.inducedChar_faithful_on_p_torsion hp hn hbound B' h' hEq hΨ' g hpg hχ
  have : NeZero (finiteDilogOrder h'.matrix) :=
    finiteDilogOrder_neZero h'.isAttractiveFixedPoint
  have hle : Nat.card {g : finiteDilogGroup h'.matrix // p • g = 0} ≤ p :=
    card_p_torsion_le χ hfaith
  have hN' : finiteDilogOrder h.matrix = finiteDilogOrder h'.matrix :=
    h.finiteDilogOrder_eq h'
  have hp' : p ∣ finiteDilogOrder h'.matrix := hN' ▸ hp
  have hpG : p ∣ Nat.card (finiteDilogGroup h'.matrix) := h'.prime_dvd_card_group hp'
  have hge : p ≤ Nat.card {g : finiteDilogGroup h'.matrix // p • g = 0} :=
    prime_le_card_p_torsion hpG
  exact ⟨Nat.le_antisymm hle hge,
    h'.exists_nontrivial_p_torsion hΨ' hpG hfaith⟩

/-- The coordinate character of $K$ restricts along `residueHom` to the explicit
character of $(\mathbb Z/N)^2$; this is used in `exists_inducedChar_eq`. -/
private theorem coordinateChar_residueHom [NeZero (finiteDilogOrder h.matrix)]
    (s : Fin 2 → ℤ) (x : B.torsionLattice ε) :
    B.coordinateChar s (x : K) =
      integralCoordinateChar (finiteDilogOrder h.matrix) s
        (h.residueHom x : Fin 2 → ZMod _) := by
  let N := finiteDilogOrder h.matrix
  have : NeZero N := finiteDilogOrder_neZero h.isAttractiveFixedPoint
  obtain ⟨z₀, hz₀⟩ := (h.isIntegralIndex_order_mul_characteristic x.2) 0
  obtain ⟨z₁, hz₁⟩ := (h.isIntegralIndex_order_mul_characteristic x.2) 1
  change (N : ℚ) * B.characteristic x 0 = (z₀ : ℚ) at hz₀
  change (N : ℚ) * B.characteristic x 1 = (z₁ : ℚ) at hz₁
  have hr₀ : h.residue (x : K) 0 = (z₀ : ZMod N) := by
    change ((⌊(N : ℚ) * B.characteristic x 0⌋ : ℤ) : ZMod N) = _
    rw [hz₀, Int.floor_intCast]
  have hr₁ : h.residue (x : K) 1 = (z₁ : ZMod N) := by
    change ((⌊(N : ℚ) * B.characteristic x 1⌋ : ℤ) : ZMod N) = _
    rw [hz₁, Int.floor_intCast]
  have hform : (N : ℚ) * B.coordinateForm s (x : K) =
      ((s 0 * z₀ + s 1 * z₁ : ℤ) : ℚ) := by
    calc
      (N : ℚ) * B.coordinateForm s (x : K) =
          (s 0 : ℚ) * ((N : ℚ) * B.characteristic x 0) +
            (s 1 : ℚ) * ((N : ℚ) * B.characteristic x 1) := by
              unfold coordinateForm
              ring
      _ = ((s 0 * z₀ + s 1 * z₁ : ℤ) : ℚ) := by rw [hz₀, hz₁]; push_cast; ring
  have hformC : (N : ℂ) * (B.coordinateForm s (x : K) : ℂ) =
      ((s 0 * z₀ + s 1 * z₁ : ℤ) : ℂ) := by exact_mod_cast hform
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  have hf : (B.coordinateForm s (x : K) : ℂ) =
      ((s 0 * z₀ + s 1 * z₁ : ℤ) : ℂ) / (N : ℂ) := by
    apply mul_left_cancel₀ hN
    rw [mul_div_cancel₀ _ hN]
    exact hformC
  have hres : (s 0 : ZMod N) * (h.residueHom x : Fin 2 → ZMod N) 0 +
      (s 1 : ZMod N) * (h.residueHom x : Fin 2 → ZMod N) 1 =
        ((s 0 * z₀ + s 1 * z₁ : ℤ) : ZMod N) := by
    rw [h.coe_residueHom, hr₀, hr₁]
    push_cast
    ring
  change Complex.exp (2 * Real.pi * Complex.I *
      (B.coordinateForm s (x : K) : ℂ)) = ZMod.stdAddChar _
  rw [hres, ZMod.stdAddChar_coe, hf]
  congr 1
  ring

/-- A period greater than one of norm one is not rational; this is used in
`coordinatePair_kernel`. -/
private theorem ne_rat (q : ℚ) : ε ≠ (q : K) := by
  intro he
  have hf := congrArg (realEmbeddingAt K F.place) he
  have hg := congrArg (realEmbeddingAt K F.otherPlace) he
  simp only [map_ratCast] at hf hg
  have hq : (1 : ℝ) < (q : ℝ) := by simpa only [hf] using h.one_lt
  have hrec : (q : ℝ) = (q : ℝ)⁻¹ := by
    calc
      (q : ℝ) = realEmbeddingAt K F.otherPlace ε := hg.symm
      _ = (realEmbeddingAt K F.place ε)⁻¹ := h.other_eq_inv
      _ = (q : ℝ)⁻¹ := by rw [hf]
  have hmul : (q : ℝ) * (q : ℝ) = 1 :=
    (congrArg (fun r : ℝ => (q : ℝ) * r) hrec).trans
      (mul_inv_cancel₀ (ne_of_gt (lt_trans zero_lt_one hq)))
  nlinarith

/-- The two rational forms $x\mapsto s\cdot r(x)$ and
$x\mapsto s\cdot r(\varepsilon x)$ have zero common kernel for $s\ne0$;
this is used in `coordinateChar_nondegenerate`. -/
private theorem coordinatePair_kernel (s : Fin 2 → ℤ) (hs : s ≠ 0) {x : K}
    (h₀ : B.coordinateForm s x = 0)
    (h₁ : B.coordinateForm s (ε * x) = 0) : x = 0 := by
  by_contra hx
  let sq : Fin 2 → ℚ := fun i => (s i : ℚ)
  let r := B.characteristic x
  let t := B.characteristic (ε * x)
  have hsq : sq ≠ 0 := by
    intro he
    apply hs
    funext i
    have hh : (s i : ℚ) = 0 := congrFun he i
    exact_mod_cast hh
  have hr : r ≠ 0 := by
    intro he
    have hrepr : x = B.scale * fracSymplecticFormRat r B.tau := by
      rw [B.fracSymplecticFormRat_characteristic, mul_div_cancel₀ x B.scale_ne_zero]
    rw [he] at hrepr
    simp only [fracSymplecticFormRat, Pi.zero_apply, Rat.cast_zero, zero_mul,
      sub_self, mul_zero] at hrepr
    exact hx hrepr
  have hsr : sq 0 * r 0 + sq 1 * r 1 = 0 := h₀
  have hst : sq 0 * t 0 + sq 1 * t 1 = 0 := h₁
  obtain ⟨q, hq⟩ := proportional_of_linear_kernel hsq hr hsr hst
  have hpair := B.fracSymplecticFormRat_characteristic (ε * x)
  change fracSymplecticFormRat t B.tau = ε * x / B.scale at hpair
  rw [hq, fracSymplecticFormRat_smul, B.fracSymplecticFormRat_characteristic] at hpair
  have hprod : (q : K) * x = ε * x := by
    calc
      (q : K) * x = B.scale * ((q : K) * (x / B.scale)) := by
        field_simp [B.scale_ne_zero]
      _ = B.scale * ((ε * x) / B.scale) := by rw [hpair]
      _ = ε * x := by field_simp [B.scale_ne_zero]
  exact h.ne_rat q ((mul_right_cancel₀ hx hprod).symm)

/-- The coefficients of $x\mapsto s\cdot r(\varepsilon x)$ in the original
characteristic coordinates; used in `coordinateChar_nondegenerate`. -/
private def shiftedCoeff (s : Fin 2 → ℤ) (i : Fin 2) : ℤ :=
  s 0 * ((h.matrix⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) 0 i +
    s 1 * ((h.matrix⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) 1 i

/-- The second phase form has coefficients `shiftedCoeff`; used in
`coordinateChar_nondegenerate`. -/
private theorem coordinateForm_mul_period (s : Fin 2 → ℤ) (x : K) :
    B.coordinateForm s (ε * x) = B.coordinateForm (h.shiftedCoeff s) x := by
  simp only [coordinateForm, h.characteristic_mul, shiftedCoeff, ratVecAction,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply]
  push_cast
  ring

/-- The two phase forms have nonzero determinant when $s\ne0$; used in
`coordinateChar_nondegenerate`. -/
private theorem coordinateDet_ne_zero (s : Fin 2 → ℤ) (hs : s ≠ 0) :
    s 0 * h.shiftedCoeff s 1 - s 1 * h.shiftedCoeff s 0 ≠ 0 := by
  intro hd
  let r : Fin 2 → ℚ := ![(s 1 : ℚ), -(s 0 : ℚ)]
  let x : K := B.scale * fracSymplecticFormRat r B.tau
  have hr : B.characteristic x = r := B.characteristic_scale_fracSymplecticFormRat r
  have h₀ : B.coordinateForm s x = 0 := by
    simp only [coordinateForm, hr, r, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    ring
  have h₁ : B.coordinateForm s (ε * x) = 0 := by
    rw [h.coordinateForm_mul_period]
    simp only [coordinateForm, hr, r, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    have hdq : ((s 0 * h.shiftedCoeff s 1 - s 1 * h.shiftedCoeff s 0 : ℤ) : ℚ) = 0 :=
      by exact_mod_cast hd
    push_cast at hdq
    linear_combination -hdq
  have hx : x = 0 := h.coordinatePair_kernel s hs h₀ h₁
  have hrzero : r = 0 := by
    rw [← hr, hx, B.characteristic_zero]
  apply hs
  funext i
  fin_cases i
  · have hh : (s 0 : ℚ) = 0 := by
      have hz := congrFun hrzero (1 : Fin 2)
      simpa [r] using hz
    exact_mod_cast hh
  · have hh : (s 1 : ℚ) = 0 := by
      have hz := congrFun hrzero (0 : Fin 2)
      simpa [r] using hz
    exact_mod_cast hh

/-- A nonzero coordinate character has bounded common kernel $A_{\Psi}\subseteq n^{-1}I$;
this is used in `exists_inducedChar_eq`. -/
private theorem coordinateChar_nondegenerate (s : Fin 2 → ℤ) (hs : s ≠ 0) :
    ∃ n : ℕ, n ≠ 0 ∧ ∀ x : K,
      (∀ k : ℕ, B.coordinateChar s (ε ^ k * x) = 1) →
        (n : K) * x ∈ B.submodule := by
  let t := h.shiftedCoeff s
  let D : ℤ := s 0 * t 1 - s 1 * t 0
  have hD : D ≠ 0 := h.coordinateDet_ne_zero s hs
  let n : ℕ := D.natAbs * D.natAbs
  have hn : n ≠ 0 := by
    have hdpos : 0 < D.natAbs := Int.natAbs_pos.mpr hD
    exact (mul_pos hdpos hdpos).ne'
  refine ⟨n, hn, ?_⟩
  intro x hchar
  have hc₀ : B.coordinateChar s x = 1 := by simpa using hchar 0
  have hc₁ : B.coordinateChar s (ε * x) = 1 := by simpa using hchar 1
  change Complex.exp (2 * Real.pi * Complex.I * (B.coordinateForm s x : ℂ)) = 1 at hc₀
  change Complex.exp (2 * Real.pi * Complex.I *
    (B.coordinateForm s (ε * x) : ℂ)) = 1 at hc₁
  obtain ⟨z₀, hz₀⟩ := (exp_two_pi_I_ratCast_eq_one_iff _).mp hc₀
  obtain ⟨z₁, hz₁⟩ := (exp_two_pi_I_ratCast_eq_one_iff _).mp hc₁
  have hlin₀ : (s 0 : ℚ) * B.characteristic x 0 +
      (s 1 : ℚ) * B.characteristic x 1 = (z₀ : ℚ) := hz₀
  rw [h.coordinateForm_mul_period] at hz₁
  have hlin₁ : (t 0 : ℚ) * B.characteristic x 0 +
      (t 1 : ℚ) * B.characteristic x 1 = (z₁ : ℚ) := hz₁
  have hcoords := integral_coordinates_of_forms s t (B.characteristic x) hlin₀ hlin₁
  have hscale : B.characteristic ((n : K) * x) =
      (n : ℚ) • B.characteristic x := by
    apply B.characteristic_eq_of_eq
    rw [fracSymplecticFormRat_smul, B.fracSymplecticFormRat_characteristic]
    simp only [Rat.cast_natCast]
    ring
  apply (B.isIntegralIndex_characteristic_iff _).mp
  rw [hscale]
  intro i
  simpa only [Pi.smul_apply, smul_eq_mul, n, D] using hcoords i

/-- **Every character of `G_{I,ε}` is induced by a nondegenerate character of `K` trivial on `I`**,
the start of the proof of [RW26b, Radchenko, Wheeler (2026b), Section 5, Lemma 3] ("choose a
nonzero representative `a`"). -/
theorem exists_inducedChar_eq [NeZero (finiteDilogOrder h.matrix)]
    (θ : AddChar (finiteDilogGroup h.matrix) ℂ) :
    ∃ (Ψ : AddChar K ℂ) (hΨ : ∀ x ∈ B.submodule, Ψ x = 1), h.inducedChar Ψ hΨ = θ ∧
      ∃ n : ℕ, n ≠ 0 ∧ ∀ x : K, (∀ k : ℕ, Ψ (ε ^ k * x) = 1) → (n : K) * x ∈ B.submodule := by
  let N := finiteDilogOrder h.matrix
  obtain ⟨χ, hχ⟩ := exists_extend_addChar (finiteDilogGroup h.matrix) θ
  obtain ⟨s, hs⟩ := exists_integralCoordinateChar N χ
  let s' : Fin 2 → ℤ := if s = 0 then ![(N : ℤ), 0] else s
  have hs' : s' ≠ 0 := by
    by_cases hsz : s = 0
    · intro he
      have hh := congrFun he (0 : Fin 2)
      have hn0 : N = 0 := by simpa [s', hsz] using hh
      exact (NeZero.ne N) hn0
    · simp [s', hsz]
  have hsame : integralCoordinateChar N s' = integralCoordinateChar N s := by
    by_cases hsz : s = 0
    · subst s
      apply AddChar.ext
      intro v
      simp [s', integralCoordinateChar, residueCoordinateChar]
    · simp [s', hsz]
  let Ψ := B.coordinateChar s'
  have hΨ : ∀ x ∈ B.submodule, Ψ x = 1 := by
    intro x hx
    exact B.coordinateChar_eq_one_of_mem s' hx
  refine ⟨Ψ, hΨ, ?_, ?_⟩
  · apply AddChar.ext
    intro g
    obtain ⟨x, rfl⟩ := h.residueHom_surjective g
    calc
      h.inducedChar Ψ hΨ (h.residueHom x) = Ψ x := h.inducedChar_residueHom Ψ hΨ x
      _ = integralCoordinateChar N s' (h.residueHom x : Fin 2 → ZMod N) :=
        h.coordinateChar_residueHom s' x
      _ = χ (h.residueHom x : Fin 2 → ZMod N) := by rw [hsame, ← hs]
      _ = θ (h.residueHom x) := hχ (h.residueHom x)
  · exact h.coordinateChar_nondegenerate s' hs'

end IsPeriod

end PseudolatticeBasis

end SIC

end
