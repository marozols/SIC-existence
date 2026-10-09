/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Dilogarithm.Pseudolattice.Finiteness
import SICs.Dilogarithm.Pseudolattice.Saturation
import SICs.Dilogarithm.Valuation.Distribution
import SICs.Valuation.Extension

/-!
# The values of the finite quantum dilogarithm are units

For every valuation `v : ℂ → ℝ≥0` with `v(p) < 1` for a prime `p`, every value `E_{I,ε}(x)` of
the finite quantum dilogarithm of a pseudolattice has `v(E_{I,ε}(x)) = 1`; consequently every
value is algebraic over `ℚ`.

This module follows [RW26b, Radchenko, Wheeler (2026b), Section 5, Theorem 5 and its proof], with
two deviations. The source takes algebraicity and the
units at `2` from [RW26, Radchenko, Wheeler (2026), Theorem 1, `thm:faddeevqbar`, and
Theorem 11]; here the valuation
argument runs at every prime `p` and every valuation `v : ℂ → ℝ≥0` above `p`, without assuming
algebraicity, and algebraicity follows: a transcendental value would be a nonunit at the Gauss
extension of the `p`-adic valuation (`isAlgebraic_of_forall_valuation_eq_one`). The argument
needs no parity assumption on `p`.

## The argument

*The case `p ∣ N`.* By `PseudolatticeBasis.exists_finite_homothety` and the homothety laws
(`logValuation_smulEquiv_of_pos`, `logValuation_smulEquiv_of_neg`, `charCoeff_comp_addEquiv`),
the absolute values of the Fourier coefficients `ŵ_I(θ)` of `w_I = log v ∘ E_{I,ε}` over all
pseudolattices with period `ε` form a finite set; choose `(I, θ)` with `A = ŵ_I(θ)` of largest
absolute value. Lemma 3 (`exists_inducedChar_eq`, `exists_card_torsion_eq`) gives a chain
`I = I_0 ⊆ ⋯ ⊆ I_r` with `(ε - 1)I_{i+1} ⊆ I_i` and characters `θ_i` induced by one character `Ψ`
of `K`, with `θ_{i+1} ∘ φ_i = θ_i` (`inducedChar_compAddMonoidHom_inclusionHom`). Inductively
`ŵ_{I_i}(θ_i) = A`: by Lemma 2 (`sum_charCoeff_logValuation`) `A` is the average of the
`|ker φ_i|` coefficients `ŵ_{I_{i+1}}(χ)` with `χ ∘ φ_i = θ_i`
(`card_filter_compAddMonoidHom_eq`), each of absolute value at most `|A|`, so all equal `A`
(`eq_of_sum_eq_card_mul`), in particular at `χ = θ_{i+1}`. At the end `|G_{I_r,ε}[p]| = p`, so
`w_{I_r}` is invariant under `G_{I_r,ε}[p]` by Theorem 4
(`FiniteQuantumDilog.valuation_add_of_nsmul_eq_zero` for `finiteQuantumDilog`), while `θ_r` is
nontrivial there; hence `A = ŵ_{I_r}(θ_r) = 0` (`charCoeff_eq_zero_of_add_eq`). So every
coefficient vanishes, `w_I = 0` by Fourier inversion (`eq_zero_of_forall_charCoeff_eq_zero`),
and `v(E_{I,ε}(x)) = 1`.

*The general case.* The matrix `γ` of `ε` has finite order modulo `p` in `SL₂(ℤ/p)`, so
`γ^r ≡ 1 (mod p)` for some `r ≥ 1`, and `p ∣ Tr(γ^r) - 2`, the order of `G_{I,ε^r}`
(`IsPeriod.pow`, `IsPeriod.matrix_pow`). For `x ∈ G_{I,ε} ⊆ G_{I,ε^r}`, (8) gives
`E_{I,ε^r}(x) = E_{I,ε}(x)^r` (`pseudolatticeDilog_pow_period`), so `v(E_{I,ε}(x))^r = 1`.

*Algebraicity.* Apply the general case at `p = 3` (any prime would do) and
`isAlgebraic_of_forall_valuation_eq_one`.
-/

noncomputable section

open scoped MatrixGroups NNReal
open Finset

namespace SIC

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
variable {F : RealQuadraticFieldData K} {B : PseudolatticeBasis F} {ε : K}

/-! ### Theorem 5 when `p` divides the order -/

/-- The Fourier coefficient of `w_I`, with the finite group instance supplied by the period;
notation for the maximum argument in `pseudolatticeDilog_valuation_eq_one_of_dvd`. -/
private def valuationCharCoeff (v : Valuation ℂ ℝ≥0) (h : B.IsPeriod ε)
    (χ : AddChar (finiteDilogGroup h.matrix) ℂ) : ℂ := by
  have hN : NeZero (finiteDilogOrder h.matrix) :=
    finiteDilogOrder_neZero h.isAttractiveFixedPoint
  exact charCoeff (fun g => (h.logValuation v g : ℂ)) χ

/-- The absolute value of a Fourier coefficient is unchanged by a homothety, including a
mixed-sign homothety; this is the homothety step of `pseudolatticeDilog_valuation_eq_one_of_dvd`. -/
private theorem exists_charCoeff_norm_eq_homothety (v : Valuation ℂ ℝ≥0)
    {B₀ : PseudolatticeBasis F} (h : B.IsPeriod ε) (h₀ : B₀.IsPeriod ε)
    [NeZero (finiteDilogOrder h.matrix)] [NeZero (finiteDilogOrder h₀.matrix)]
    {α : K} (hα₁ : 0 < realEmbeddingAt K F.place α)
    (hI : ∀ y, y ∈ B.submodule ↔ ∃ z ∈ B₀.submodule, y = α * z)
    (χ : AddChar (finiteDilogGroup h.matrix) ℂ) :
    ∃ θ : AddChar (finiteDilogGroup h₀.matrix) ℂ,
      ‖charCoeff (fun g => (h.logValuation v g : ℂ)) χ‖ =
        ‖charCoeff (fun g => (h₀.logValuation v g : ℂ)) θ‖ := by
  have hα : α ≠ 0 := by
    intro heq
    simp [heq] at hα₁
  let e := h.smulEquiv h₀ hα hI
  let θ := χ.compAddMonoidHom e.toAddMonoidHom
  refine ⟨θ, ?_⟩
  have hcoeff := charCoeff_comp_addEquiv e
    (fun g => (h.logValuation v g : ℂ)) χ
  change charCoeff (fun g => (h.logValuation v (e g) : ℂ)) θ =
    charCoeff (fun g => (h.logValuation v g : ℂ)) χ at hcoeff
  have hα₂ : realEmbeddingAt K F.otherPlace α ≠ 0 :=
    (map_ne_zero (realEmbeddingAt K F.otherPlace)).mpr hα
  rcases lt_or_gt_of_ne hα₂ with hneg | hpos
  · have hw : (fun g => (h.logValuation v (e g) : ℂ)) =
        (fun g => -(h₀.logValuation v g : ℂ)) := by
      funext g
      simp only [e, h.logValuation_smulEquiv_of_neg h₀ hα hα₁ hneg hI g,
        Complex.ofReal_neg]
    rw [hw] at hcoeff
    have hminus : charCoeff (fun g => -(h₀.logValuation v g : ℂ)) θ =
        -charCoeff (fun g => (h₀.logValuation v g : ℂ)) θ := by
      simp [charCoeff, Finset.sum_neg_distrib, neg_mul]
    rw [hminus] at hcoeff
    rw [← hcoeff, norm_neg]
  · have hw : (fun g => (h.logValuation v (e g) : ℂ)) =
        (fun g => (h₀.logValuation v g : ℂ)) := by
      funext g
      simp only [e, h.logValuation_smulEquiv_of_pos h₀ hα hα₁ hpos hI g]
    rw [hw] at hcoeff
    exact congrArg norm hcoeff.symm

/-- Fourier coefficient norms for one period attain a maximum across all its pseudolattices;
the finiteness input for `pseudolatticeDilog_valuation_eq_one_of_dvd`. -/
private theorem exists_max_charCoeff_norm (v : Valuation ℂ ℝ≥0) (h : B.IsPeriod ε) :
    ∃ (B₀ : PseudolatticeBasis F) (h₀ : B₀.IsPeriod ε)
      (θ : AddChar (finiteDilogGroup h₀.matrix) ℂ),
      ∀ (B' : PseudolatticeBasis F) (h' : B'.IsPeriod ε)
        (χ : AddChar (finiteDilogGroup h'.matrix) ℂ),
        ‖valuationCharCoeff v h' χ‖ ≤ ‖valuationCharCoeff v h₀ θ‖ := by
  classical
  obtain ⟨S, hS, hSperiod, hrep⟩ := PseudolatticeBasis.exists_finite_homothety F ε
  let T := {B₀ : PseudolatticeBasis F // B₀ ∈ S}
  let hp (b : T) : b.1.IsPeriod ε := hSperiod b.1 b.2
  let C (b : T) := AddChar (finiteDilogGroup (hp b).matrix) ℂ
  let f : (Σ b : T, C b) → ℝ := fun t =>
    ‖valuationCharCoeff v (hp t.1) t.2‖
  have hfinite : Finite (Σ b : T, C b) := by
    have hT : Finite T := hS.to_subtype
    have hC (b : T) : Finite (C b) := by
      have hN : NeZero (finiteDilogOrder (hp b).matrix) :=
        finiteDilogOrder_neZero (hp b).isAttractiveFixedPoint
      infer_instance
    infer_instance
  let U : Set ℝ := {a | ∃ (B' : PseudolatticeBasis F) (h' : B'.IsPeriod ε)
    (χ : AddChar (finiteDilogGroup h'.matrix) ℂ),
      a = ‖valuationCharCoeff v h' χ‖}
  have hsub : U ⊆ Set.range f := by
    intro a ha
    obtain ⟨B', h', χ, rfl⟩ := ha
    obtain ⟨B₀, hB₀, α, hα, hI⟩ := hrep B' h'
    have hN : NeZero (finiteDilogOrder h'.matrix) :=
      finiteDilogOrder_neZero h'.isAttractiveFixedPoint
    have hN₀ : NeZero (finiteDilogOrder (hp ⟨B₀, hB₀⟩).matrix) :=
      finiteDilogOrder_neZero (hp ⟨B₀, hB₀⟩).isAttractiveFixedPoint
    obtain ⟨θ, hθ⟩ := exists_charCoeff_norm_eq_homothety v h' (hp ⟨B₀, hB₀⟩)
      hα hI χ
    exact ⟨⟨⟨B₀, hB₀⟩, θ⟩, hθ.symm⟩
  have hU : U.Finite := (Set.finite_range f).subset hsub
  have hN : NeZero (finiteDilogOrder h.matrix) :=
    finiteDilogOrder_neZero h.isAttractiveFixedPoint
  have hUne : U.Nonempty := by
    refine ⟨‖valuationCharCoeff v h 1‖, ?_⟩
    exact ⟨B, h, 1, rfl⟩
  obtain ⟨a, ha⟩ := hU.exists_maximal hUne
  obtain ⟨B₀, h₀, θ, rfl⟩ := ha.1
  exact ⟨B₀, h₀, θ, fun B' h' χ => ha.le ⟨B', h', χ, rfl⟩⟩

/-- A coefficient attaining the global norm maximum propagates through one inclusion with
`(ε - 1)J ⊆ I`; the averaging step of `pseudolatticeDilog_valuation_eq_one_of_dvd`. -/
private theorem valuationCharCoeff_eq_of_inclusion (v : Valuation ℂ ℝ≥0)
    {B' : PseudolatticeBasis F} (h : B.IsPeriod ε) (h' : B'.IsPeriod ε)
    (hle : B.submodule ≤ B'.submodule)
    (hJ : ∀ y ∈ B'.submodule, (ε - 1) * y ∈ B.submodule)
    (θ : AddChar (finiteDilogGroup h.matrix) ℂ)
    (χ : AddChar (finiteDilogGroup h'.matrix) ℂ)
    (hχ : χ.compAddMonoidHom (h.inclusionHom h' hle) = θ)
    (hmax : ∀ χ' : AddChar (finiteDilogGroup h'.matrix) ℂ,
      ‖valuationCharCoeff v h' χ'‖ ≤ ‖valuationCharCoeff v h θ‖) :
    valuationCharCoeff v h' χ = valuationCharCoeff v h θ := by
  classical
  have hN : NeZero (finiteDilogOrder h.matrix) :=
    finiteDilogOrder_neZero h.isAttractiveFixedPoint
  have hN' : NeZero (finiteDilogOrder h'.matrix) :=
    finiteDilogOrder_neZero h'.isAttractiveFixedPoint
  let φ := h.inclusionHom h' hle
  let s := univ.filter (fun ξ : AddChar (finiteDilogGroup h'.matrix) ℂ =>
    ξ.compAddMonoidHom φ = θ)
  have hθ : ∀ k, φ k = 0 → θ k = 1 := by
    intro k hk
    rw [← hχ]
    change χ (φ k) = 1
    simp [hk]
  have hcard : Fintype.card (finiteDilogGroup h.matrix) =
      Fintype.card (finiteDilogGroup h'.matrix) := by
    rw [card_fixedCharacteristics h.matrix (finiteDilogOrder h.matrix)
        (det_sub_one_eq_neg_finiteDilogOrder h.isAttractiveFixedPoint),
      card_fixedCharacteristics h'.matrix (finiteDilogOrder h'.matrix)
        (det_sub_one_eq_neg_finiteDilogOrder h'.isAttractiveFixedPoint),
      h.finiteDilogOrder_eq h']
  have hs : s.card = (univ.filter fun k => φ k = 0).card :=
    card_filter_compAddMonoidHom_eq hcard φ hθ
  have hsum : ∑ ξ ∈ s, valuationCharCoeff v h' ξ =
      (s.card : ℂ) * valuationCharCoeff v h θ := by
    have hdist := PseudolatticeBasis.IsPeriod.sum_charCoeff_logValuation
      (v := v) (h := h) h' hle hJ hθ
    simpa only [s, φ, valuationCharCoeff, hs] using hdist
  exact eq_of_sum_eq_card_mul (fun ξ _ => hmax ξ) hsum χ (by
    simp only [s, mem_filter, mem_univ, true_and]
    exact hχ)

/-- The maximizing coefficient propagates along the saturation chain of Lemma 3; this is the
induction in `pseudolatticeDilog_valuation_eq_one_of_dvd`. -/
private theorem exists_saturation_coeff_eq (v : Valuation ℂ ℝ≥0)
    (h : B.IsPeriod ε) (Ψ : AddChar K ℂ)
    (hΨ : ∀ x ∈ B.submodule, Ψ x = 1)
    (hmax : ∀ (B' : PseudolatticeBasis F) (h' : B'.IsPeriod ε)
      (χ : AddChar (finiteDilogGroup h'.matrix) ℂ),
      ‖valuationCharCoeff v h' χ‖ ≤ ‖valuationCharCoeff v h (h.inducedChar Ψ hΨ)‖)
    (i : ℕ) :
    ∃ (B' : PseudolatticeBasis F) (h' : B'.IsPeriod ε),
      ∃ (_heq : B'.submodule = B.saturation ε Ψ i)
        (hΨ' : ∀ x ∈ B'.submodule, Ψ x = 1),
        valuationCharCoeff v h' (h'.inducedChar Ψ hΨ') =
          valuationCharCoeff v h (h.inducedChar Ψ hΨ) := by
  induction i with
  | zero =>
      refine ⟨B, h, (h.saturation_zero hΨ).symm, hΨ, ?_⟩
      rfl
  | succ i ih =>
      obtain ⟨Bᵢ, hᵢ, heqᵢ, hΨᵢ, hcoeffᵢ⟩ := ih
      obtain ⟨B', heq', h'⟩ := h.exists_saturation_eq hΨ (i + 1)
      have hΨ' : ∀ x ∈ B'.submodule, Ψ x = 1 := by
        intro x hx
        have hx' : x ∈ B.saturation ε Ψ (i + 1) := by simpa [← heq'] using hx
        simpa using (B.mem_saturation.mp hx').2 0
      have hle : Bᵢ.submodule ≤ B'.submodule := by
        intro y hy
        rw [heqᵢ] at hy
        rw [heq']
        exact h.saturation_le_succ i hy
      have hJ : ∀ y ∈ B'.submodule, (ε - 1) * y ∈ Bᵢ.submodule := by
        intro y hy
        rw [heq'] at hy
        rw [heqᵢ]
        exact B.mul_mem_saturation hy
      have hcomp : (h'.inducedChar Ψ hΨ').compAddMonoidHom
          (hᵢ.inclusionHom h' hle) = hᵢ.inducedChar Ψ hΨᵢ := by
        exact hᵢ.inducedChar_compAddMonoidHom_inclusionHom h' hle Ψ hΨ'
      have hstep := valuationCharCoeff_eq_of_inclusion v hᵢ h' hle hJ
        (hᵢ.inducedChar Ψ hΨᵢ) (h'.inducedChar Ψ hΨ') hcomp (fun χ => by
          calc
            ‖valuationCharCoeff v h' χ‖ ≤
                ‖valuationCharCoeff v h (h.inducedChar Ψ hΨ)‖ := hmax B' h' χ
            _ = ‖valuationCharCoeff v hᵢ (hᵢ.inducedChar Ψ hΨᵢ)‖ := by
              exact congrArg norm hcoeffᵢ.symm)
      refine ⟨B', h', heq', hΨ', ?_⟩
      exact hstep.trans hcoeffᵢ

/-- When `G[p]` has order `p`, the induced character is nontrivial on a translation preserving
`w_I`, so its coefficient vanishes; the last step of
`pseudolatticeDilog_valuation_eq_one_of_dvd`. -/
private theorem valuationCharCoeff_eq_zero_of_torsion (v : Valuation ℂ ℝ≥0)
    {p : ℕ} [Fact p.Prime] (hvp : v (p : ℂ) < 1)
    (h : B.IsPeriod ε) (Ψ : AddChar K ℂ)
    (hΨ : ∀ x ∈ B.submodule, Ψ x = 1)
    (hcard : Nat.card {g : finiteDilogGroup h.matrix // p • g = 0} = p)
    {x : K} (hx : (ε - 1) * x ∈ B.submodule)
    (hpx : (p : K) * x ∈ B.submodule) (hΨx : Ψ x ≠ 1) :
    valuationCharCoeff v h (h.inducedChar Ψ hΨ) = 0 := by
  classical
  have hN : NeZero (finiteDilogOrder h.matrix) :=
    finiteDilogOrder_neZero h.isAttractiveFixedPoint
  have hG : (univ.filter fun g : finiteDilogGroup h.matrix => p • g = 0).card = p := by
    simpa only [← Fintype.card_subtype, Nat.card_eq_fintype_card] using hcard
  let u := h.residueHom (⟨x, hx⟩ : B.torsionLattice ε)
  have hu : p • u = 0 := by
    change p • h.residueHom (⟨x, hx⟩ : B.torsionLattice ε) = 0
    exact (h.residueHom_nsmul_eq_zero_iff _ p).mpr hpx
  have hw (t : finiteDilogGroup h.matrix) :
      (fun g => (h.logValuation v g : ℂ)) (t + u) =
        (fun g => (h.logValuation v g : ℂ)) t := by
    have hv := h.finiteQuantumDilog.valuation_add_of_nsmul_eq_zero v hvp hG hu t
    have hl := congrArg (fun a : ℝ≥0 => (Real.log a : ℂ)) hv
    simpa only [u, add_comm t, h.finiteQuantumDilog_apply,
      PseudolatticeBasis.IsPeriod.logValuation] using hl
  have hθu : h.inducedChar Ψ hΨ u ≠ 1 := by
    change h.inducedChar Ψ hΨ (h.residueHom (⟨x, hx⟩ : B.torsionLattice ε)) ≠ 1
    rw [h.inducedChar_residueHom]
    exact hΨx
  exact charCoeff_eq_zero_of_add_eq hw hθu

/-- **[RW26b, Radchenko, Wheeler (2026b), Section 5, Theorem 5], the case `p ∣ N`**: if
`v(p) < 1` and `p` divides `N = |G_{I,ε}|`, then `v(E_{I,ε}(x)) = 1` for every `x ∈ G_{I,ε}`. -/
theorem pseudolatticeDilog_valuation_eq_one_of_dvd (v : Valuation ℂ ℝ≥0) {p : ℕ}
    [Fact p.Prime] (hvp : v (p : ℂ) < 1) (h : B.IsPeriod ε)
    (hp : p ∣ finiteDilogOrder h.matrix) {x : K} (hx : (ε - 1) * x ∈ B.submodule) :
    v (pseudolatticeDilog h x) = 1 := by
  classical
  obtain ⟨B₀, h₀, θ, hmax⟩ := exists_max_charCoeff_norm v h
  have hN₀ : NeZero (finiteDilogOrder h₀.matrix) :=
    finiteDilogOrder_neZero h₀.isAttractiveFixedPoint
  obtain ⟨Ψ, hΨ, hθ, hdeg⟩ := h₀.exists_inducedChar_eq θ
  have hp₀ : p ∣ finiteDilogOrder h₀.matrix := by
    rw [← h.finiteDilogOrder_eq h₀]
    exact hp
  obtain ⟨i, hi⟩ := h₀.exists_card_torsion_eq hp₀ hdeg
  have hmax' : ∀ (B' : PseudolatticeBasis F) (h' : B'.IsPeriod ε)
      (χ : AddChar (finiteDilogGroup h'.matrix) ℂ),
      ‖valuationCharCoeff v h' χ‖ ≤
        ‖valuationCharCoeff v h₀ (h₀.inducedChar Ψ hΨ)‖ := by
    intro B' h' χ
    rw [hθ]
    exact hmax B' h' χ
  obtain ⟨B', h', heq', hΨ', hcoeff⟩ :=
    exists_saturation_coeff_eq v h₀ Ψ hΨ hmax' i
  obtain ⟨hcard, y, hy, hpy, hΨy⟩ := hi B' h' heq'
  have hzero := valuationCharCoeff_eq_zero_of_torsion v hvp h' Ψ hΨ' hcard hy hpy hΨy
  have hA : valuationCharCoeff v h₀ θ = 0 := by
    rw [← hθ, ← hcoeff]
    exact hzero
  have hN : NeZero (finiteDilogOrder h.matrix) :=
    finiteDilogOrder_neZero h.isAttractiveFixedPoint
  have hall (χ : AddChar (finiteDilogGroup h.matrix) ℂ) :
      valuationCharCoeff v h χ = 0 := by
    have hb := hmax B h χ
    rw [hA, norm_zero] at hb
    exact norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))
  have hw : (fun g : finiteDilogGroup h.matrix => (h.logValuation v g : ℂ)) = 0 :=
    eq_zero_of_forall_charCoeff_eq_zero hall
  have hlog : Real.log (v (pseudolatticeDilog h x)) = 0 := by
    have hz := congrFun hw (h.residueHom (⟨x, hx⟩ : B.torsionLattice ε))
    have hz' : h.logValuation v (h.residueHom (⟨x, hx⟩ : B.torsionLattice ε)) = 0 := by
      exact_mod_cast (by simpa using hz :
        ((h.logValuation v (h.residueHom (⟨x, hx⟩ : B.torsionLattice ε)) : ℝ) : ℂ) = 0)
    simpa only [h.logValuation_residueHom] using hz'
  have hvpos : (0 : ℝ) < (v (pseudolatticeDilog h x) : ℝ) := by
    exact_mod_cast (v.pos_iff.mpr (pseudolatticeDilog_ne_zero h hx))
  exact_mod_cast Real.eq_one_of_pos_of_log_eq_zero hvpos hlog

/-! ### Theorem 5 -/

/-- **[RW26b, Radchenko, Wheeler (2026b), Section 5, Theorem 5] at a valuation above `p`**: for
every prime `p` and every valuation `v : ℂ → ℝ≥0` with `v(p) < 1`, the values of the finite
quantum dilogarithm of a pseudolattice are units, `v(E_{I,ε}(x)) = 1` for `x ∈ G_{I,ε}`. The
source's appeal to [RW26, Radchenko, Wheeler (2026), Theorem 1, `thm:faddeevqbar`, and
Theorem 11] for algebraicity and the
prime `2` is not needed. -/
@[source "RW26b, Theorem 5, p. 8 (unit at every valuation above a prime)"]
theorem pseudolatticeDilog_valuation_eq_one (v : Valuation ℂ ℝ≥0) {p : ℕ} [Fact p.Prime]
    (hvp : v (p : ℂ) < 1) (h : B.IsPeriod ε) {x : K} (hx : (ε - 1) * x ∈ B.submodule) :
    v (pseudolatticeDilog h x) = 1 := by
  have hpne : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨r, hr, hΓ⟩ := exists_pow_mem_Gamma p h.matrix
  have hΓ' : ((h.pow hr).matrix 0 0 : ZMod p) = 1 ∧
      ((h.pow hr).matrix 0 1 : ZMod p) = 0 ∧
      ((h.pow hr).matrix 1 0 : ZMod p) = 0 ∧
      ((h.pow hr).matrix 1 1 : ZMod p) = 1 := by
    rw [h.matrix_pow hr]
    exact CongruenceSubgroup.Gamma_mem.mp hΓ
  have hmod : ((finiteDilogOrder (h.pow hr).matrix : ℕ) : ZMod p) = 0 := by
    have hcast := congrArg (fun z : ℤ => (z : ZMod p))
      (cast_finiteDilogOrder (h.pow hr).isAttractiveFixedPoint)
    push_cast at hcast
    rw [hΓ'.1, hΓ'.2.2.2] at hcast
    norm_num at hcast
    exact hcast
  have hpOrder : p ∣ finiteDilogOrder (h.pow hr).matrix :=
    (ZMod.natCast_eq_zero_iff _ _).mp hmod
  have hunit := pseudolatticeDilog_valuation_eq_one_of_dvd v hvp (h.pow hr) hpOrder
    (h.pow_sub_one_mul_mem hx r)
  rw [pseudolatticeDilog_pow_period h hr hx, map_pow] at hunit
  exact (pow_eq_one_iff_of_nonneg
    (zero_le : 0 ≤ v (pseudolatticeDilog h x)) hr.ne').mp hunit

/-- **The values of the finite quantum dilogarithm of a pseudolattice are algebraic**, the first
assertion of [RW26b, Radchenko, Wheeler (2026b), Section 5, Theorem 5], proved by valuations
instead of [RW26, Radchenko, Wheeler (2026), Theorem 1, `thm:faddeevqbar`]. -/
@[source "RW26b, Theorem 5, p. 8 (algebraic)"]
theorem pseudolatticeDilog_isAlgebraic (h : B.IsPeriod ε) {x : K}
    (hx : (ε - 1) * x ∈ B.submodule) : IsAlgebraic ℚ (pseudolatticeDilog h x) := by
  have hp : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact isAlgebraic_of_forall_valuation_eq_one 3 fun v hvp =>
    pseudolatticeDilog_valuation_eq_one v hvp h hx

end SIC

end
