/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Dilogarithm.Pseudolattice.Torsion
import SICs.Dilogarithm.Valuation.Units

/-!
# Invariant products over a cyclic summand

For a period `η` with `η - 1 = p^sT`, `TI ⊆ I`, and `z` with `p^sz ∈ I` such that `p^{s-1}z` is
not an eigenvector of `T` modulo `I`, the products `∏_{m<p^s} E_{I,η}(x + mz)` are invariant
modulo `𝔪` under translation of `x` by `p⁻¹I`.

This module formalizes the step of [RW26b, Radchenko, Wheeler (2026b), Section 7, proof of
Theorem 7] that supplies the hypothesis of the metric-group part
(`FiniteQuantumDilog.translation_invariant_of_summands`): for a cyclic summand `L = ⟨z⟩` of
`G_{I,η}[p^∞]` of order `p^s` whose `p`-torsion is neither line, Lemma 5's matrix calculation
makes `G_{J,η}[p^∞]` cyclic for the inverse image `J` of `L`, and Theorem 4 at `J` with the
distribution relation (11) gives the invariance. The lines enter only through the hypothesis that
`p^{s-1}z` is not an eigenvector of `T`; `SICs.Dilogarithm.Frobenius.LatticeTranslation` derives
it from `IsSplitLinePair.mem_or_mem_of_mul_sub_mem`.

## The argument

*The summand.* Put `y = p^{s-1}z`. If `y ∈ I`, then `Ty - 0·y ∈ TI ⊆ I`, against the hypothesis;
so `z` has order exactly `p^s` modulo `I`, and `{mz : m < p^s}` represents `J/I` for
`J = I + ℤz`. Since `(η - 1)z = T(p^sz) ∈ I`, `(η - 1)J ⊆ I`, so `J` has an admissible basis
(`PseudolatticeBasis.exists_submodule_eq`) with period `η` (`IsPeriod.of_le`).

*Cyclicity (Lemma 5).* Suppose `(η - 1)J ⊆ pJ`. Then `(η - 1)z = pTy ∈ pJ` gives
`Ty = i + mz` with `i ∈ I`; as `pTy ∈ I`, `pmz ∈ I`, so `p^{s-1} ∣ m` and `Ty ≡ (m/p^{s-1})y`
modulo `I`, against the hypothesis. So `η ≢ 1` on `J/pJ`; and `p ∣ N` since `G_{I,η}` contains
the element `y` of order `p`. By `IsPeriod.card_torsion_eq_prime`, `|G_{J,η}[p]| = p`.

*Theorem 4 and (11).* For `pu ∈ I`, `u ∈ G_{J,η}[p]`, so Theorem 4 (`translationRatio_unit`)
gives `E_{J,η}(x + u) ≡ E_{J,η}(x)`, both units. The distribution relation (11),
`pseudolatticeDilog_distribution`, writes `E_{J,η}(x)` times a constant as
`∏_{m<p^s} E_{I,η}(x + mz)`, and the same at `x + u`; all values are units
(`pseudolatticeDilog_valuation_eq_one`), so the two products are congruent.
-/

noncomputable section

open scoped MatrixGroups NNReal

namespace SIC

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
variable {F : RealQuadraticFieldData K} {B : PseudolatticeBasis F}

/-! ### Products over a cyclic summand

Theorem 4 at the inverse image of the summand, transferred by (11). -/

/-- The generator of the cyclic summand has order exactly `p^s` modulo `I`; used by
`pseudolatticeDilog_prod_summand_congr`. -/
private theorem cyclic_summand_order {p s : ℕ} [Fact p.Prime] {z : K} (hs : 0 < s)
    (hz : (p : K) ^ s * z ∈ B.submodule)
    (hy : (p : K) ^ (s - 1) * z ∉ B.submodule) :
    addOrderOf (Submodule.Quotient.mk z : K ⧸ B.submodule) = p ^ s := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs)
  apply addOrderOf_eq_prime_pow
  · intro hzero
    apply hy
    apply (Submodule.Quotient.mk_eq_zero B.submodule).mp
    simpa only [Nat.succ_sub_one, ← Submodule.Quotient.mk_smul, nsmul_eq_mul,
      Nat.cast_pow] using hzero
  · apply (Submodule.Quotient.mk_eq_zero B.submodule).mpr
    simpa only [← Submodule.Quotient.mk_smul, nsmul_eq_mul, Nat.cast_pow] using hz

omit [NumberField K] [NumberField.IsTotallyReal K] in
/-- Distinct residues in `[0,n)` give distinct classes of a generator of order `n`; used by
`cyclic_summand_transversal`. -/
private theorem cyclic_summand_unique (I : Submodule ℤ K) {z : K} {n a b : ℕ}
    (horder : addOrderOf (Submodule.Quotient.mk z : K ⧸ I) = n)
    (ha : a < n) (hb : b < n) (hab : (a : K) * z - (b : K) * z ∈ I) : a = b := by
  let q : K ⧸ I := Submodule.Quotient.mk z
  have heq : a • q = b • q := by
    apply (Submodule.Quotient.eq I).mpr
    simpa only [q, ← Submodule.Quotient.mk_smul, nsmul_eq_mul] using hab
  have hdvd (c d : ℕ) (hdc : d ≤ c) (hcd : c • q = d • q) : n ∣ c - d := by
    have hzero : (c - d) • q = 0 := by
      have hadd : (c - d) • q + d • q = d • q := by
        simpa only [← add_nsmul, Nat.sub_add_cancel hdc] using hcd
      exact add_right_cancel (by simpa only [zero_add] using hadd)
    rw [← horder]
    exact (addOrderOf_dvd_iff_nsmul_eq_zero).mpr hzero
  by_cases hba : b ≤ a
  · have hdiff : a - b = 0 := Nat.eq_zero_of_dvd_of_lt (hdvd a b hba heq) (by omega)
    omega
  · have hab' : a ≤ b := le_of_not_ge hba
    have hdiff : b - a = 0 := Nat.eq_zero_of_dvd_of_lt (hdvd b a hab' heq.symm) (by omega)
    omega

omit [NumberField K] [NumberField.IsTotallyReal K] in
/-- The displayed representatives of a cyclic extension are distinct; used by
`pseudolatticeDilog_prod_summand_congr`. -/
private theorem cyclic_summand_image_inj (I : Submodule ℤ K) {z : K} {n : ℕ}
    (horder : addOrderOf (Submodule.Quotient.mk z : K ⧸ I) = n) :
    Set.InjOn (fun m : ℕ => (m : K) * z) (Finset.range n) := by
  intro m hm m' hm' heq
  apply cyclic_summand_unique I horder
    (Finset.mem_range.mp hm) (Finset.mem_range.mp hm')
  change (m : K) * z = (m' : K) * z at heq
  rw [heq, sub_self]
  exact I.zero_mem

open scoped Classical in
omit [NumberField K] [NumberField.IsTotallyReal K] in
/-- The residues `mz`, `0 ≤ m < n`, represent the cyclic extension of `I` generated by a
class of order `n`; used by `pseudolatticeDilog_prod_summand_congr`. -/
private theorem cyclic_summand_transversal (I : Submodule ℤ K) {z : K} {n : ℕ}
    (hn : 0 < n) (horder : addOrderOf (Submodule.Quotient.mk z : K ⧸ I) = n) :
    IsQuotientTransversal I (I ⊔ Submodule.span ℤ {z})
      ((Finset.range n).image fun m : ℕ => (m : K) * z) := by
  classical
  let q : K ⧸ I := Submodule.Quotient.mk z
  constructor
  · intro w hw
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hw
    apply Submodule.mem_sup_right
    exact Submodule.mem_span_singleton.mpr ⟨(m : ℤ), by simp [zsmul_eq_mul]⟩
  · intro w hw w' hw' hww'
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨m', hm', rfl⟩ := Finset.mem_image.mp hw'
    have hmm' : m = m' := cyclic_summand_unique I horder
      (Finset.mem_range.mp hm) (Finset.mem_range.mp hm') hww'
    simp [hmm']
  · intro w hw
    obtain ⟨i, hi, a, ha, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨m, rfl⟩ := Submodule.mem_span_singleton.mp ha
    let r : ℕ := (m % (n : ℤ)).toNat
    have hr0 : 0 ≤ m % (n : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hn.ne')
    have hr : r < n := by
      have := Int.emod_lt_of_pos m (show (0 : ℤ) < n by exact_mod_cast hn)
      omega
    have hmod : (r : ℤ) = m % (n : ℤ) := Int.toNat_of_nonneg hr0
    have heq : (r : ℤ) • q = m • q := by
      have hq : addOrderOf q = n := horder
      simpa only [hq, ← hmod] using mod_addOrderOf_zsmul q m
    refine ⟨(r : K) * z, Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr hr, rfl⟩, ?_⟩
    apply (Submodule.Quotient.mk_eq_zero I).mp
    rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_add,
      (Submodule.Quotient.mk_eq_zero I).mpr hi, zero_add]
    simpa only [q, ← Submodule.Quotient.mk_smul, zsmul_eq_mul, nsmul_eq_mul,
      Int.cast_natCast] using sub_eq_zero.mpr heq.symm

omit [NumberField K] [NumberField.IsTotallyReal K] in
/-- The `p`-torsion in a cyclic extension of order `p^(t+1)` is generated by `p^t z`; this
is the quotient form of the matrix calculation in `pseudolatticeDilog_prod_summand_congr`. -/
private theorem cyclic_summand_p_torsion (I : Submodule ℤ K) {p t : ℕ} [Fact p.Prime]
    {z w : K} (horder : addOrderOf (Submodule.Quotient.mk z : K ⧸ I) = p ^ (t + 1))
    (hw : w ∈ I ⊔ Submodule.span ℤ {z}) (hpw : (p : K) * w ∈ I) :
    ∃ c : ℤ, w - (c : K) * ((p : K) ^ t * z) ∈ I := by
  let q : K ⧸ I := Submodule.Quotient.mk z
  obtain ⟨i, hi, a, ha, rfl⟩ := Submodule.mem_sup.mp hw
  obtain ⟨m, rfl⟩ := Submodule.mem_span_singleton.mp ha
  have hpi : (p : K) * i ∈ I := by
    simpa only [zsmul_eq_mul, Int.cast_natCast] using I.smul_mem (p : ℤ) hi
  have hpmz : (p : K) * ((m : K) * z) ∈ I := by
    have hsub := I.sub_mem hpw hpi
    convert hsub using 1
    simp only [zsmul_eq_mul]
    ring
  have hzero : ((p : ℤ) * m) • q = 0 := by
    apply (Submodule.Quotient.mk_eq_zero I).mpr
    simpa only [q, ← Submodule.Quotient.mk_smul, zsmul_eq_mul, Int.cast_mul,
      Int.cast_natCast, mul_assoc] using hpmz
  have hdiv : ((p : ℤ) ^ (t + 1)) ∣ (p : ℤ) * m := by
    have hq : addOrderOf q = p ^ (t + 1) := horder
    simpa only [hq, Nat.cast_pow] using
      (addOrderOf_dvd_iff_zsmul_eq_zero).mpr hzero
  have hdiv' : (p : ℤ) * (p : ℤ) ^ t ∣ (p : ℤ) * m := by
    simpa only [pow_succ, mul_comm] using hdiv
  have hm : (p : ℤ) ^ t ∣ m :=
    (Int.mul_dvd_mul_iff_left (by exact_mod_cast (Fact.out : p.Prime).ne_zero)).mp hdiv'
  obtain ⟨c, hc⟩ := hm
  refine ⟨c, ?_⟩
  convert hi using 1
  rw [hc]
  simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  ring

/-- The period is nontrivial on `J/pJ`: the cyclic summand's `p`-torsion is not preserved by
`T`. This is the coordinate-free calculation from [RW26b, Radchenko, Wheeler (2026b), Section 6,
proof of Lemma 5] used by
`pseudolatticeDilog_prod_summand_congr`. -/
private theorem cyclic_summand_not_scalar {p t : ℕ} [Fact p.Prime] {η T z : K}
    (hT : η - 1 = (p : K) ^ (t + 1) * T)
    (hTI : ∀ x ∈ B.submodule, T * x ∈ B.submodule)
    (hz : (p : K) ^ (t + 1) * z ∈ B.submodule)
    (hzT : ∀ c : ℤ, T * ((p : K) ^ t * z) - c * ((p : K) ^ t * z) ∉ B.submodule)
    (horder : addOrderOf (Submodule.Quotient.mk z : K ⧸ B.submodule) = p ^ (t + 1)) :
    ∃ w ∈ B.submodule ⊔ Submodule.span ℤ {z},
      (η - 1) / p * w ∉ B.submodule ⊔ Submodule.span ℤ {z} := by
  let J := B.submodule ⊔ Submodule.span ℤ {z}
  have hzJ : z ∈ J :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self z)
  have hpy : (p : K) * (T * ((p : K) ^ t * z)) ∈ B.submodule := by
    convert hTI _ hz using 1
    ring
  have hyJ : T * ((p : K) ^ t * z) ∉ J := by
    intro hy
    obtain ⟨c, hc⟩ := cyclic_summand_p_torsion B.submodule horder hy hpy
    exact hzT c hc
  refine ⟨z, hzJ, ?_⟩
  have hpne : (p : K) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have heq : (η - 1) / (p : K) * z = T * ((p : K) ^ t * z) := by
    rw [hT, pow_succ]
    field_simp
  simpa only [heq] using hyJ

/-- The generator `z` lies in `(η - 1)⁻¹I` when `η - 1 = p^(t+1)T`, `TI ⊆ I`, and
`p^(t+1)z ∈ I`; used by the cyclic summand calculations. -/
private theorem cyclic_summand_z_period {p t : ℕ} {η T z : K}
    (hT : η - 1 = (p : K) ^ (t + 1) * T)
    (hTI : ∀ x ∈ B.submodule, T * x ∈ B.submodule)
    (hz : (p : K) ^ (t + 1) * z ∈ B.submodule) :
    (η - 1) * z ∈ B.submodule := by
  rw [hT]
  convert hTI _ hz using 1
  ring

/-- The inverse image `J = I + ℤz` has an admissible basis and satisfies
`(η - 1)J ⊆ I`; used by `pseudolatticeDilog_prod_summand_congr`. -/
private theorem cyclic_summand_lattice {p t : ℕ} [Fact p.Prime] {η T z : K}
    (h : B.IsPeriod η) (hT : η - 1 = (p : K) ^ (t + 1) * T)
    (hTI : ∀ x ∈ B.submodule, T * x ∈ B.submodule)
    (hz : (p : K) ^ (t + 1) * z ∈ B.submodule) :
    ∃ B' : PseudolatticeBasis F,
      B'.submodule = B.submodule ⊔ Submodule.span ℤ {z} ∧
        ∀ w ∈ B'.submodule, (η - 1) * w ∈ B.submodule := by
  let J : Submodule ℤ K := B.submodule ⊔ Submodule.span ℤ {z}
  have hle : B.submodule ≤ J := le_sup_left
  have hzperiod : (η - 1) * z ∈ B.submodule :=
    cyclic_summand_z_period hT hTI hz
  have hJ : ∀ w ∈ J, (η - 1) * w ∈ B.submodule := by
    intro w hw
    obtain ⟨i, hi, a, ha, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨m, rfl⟩ := Submodule.mem_span_singleton.mp ha
    have hi' : (η - 1) * i ∈ B.submodule := by
      convert B.submodule.sub_mem (h.mul_mem hi) hi using 1
      ring
    have hz' : (η - 1) * (m • z) ∈ B.submodule := by
      convert B.submodule.smul_mem m hzperiod using 1
      simp only [zsmul_eq_mul]
      ring
    convert B.submodule.add_mem hi' hz' using 1
    ring
  have hJbound : ∀ w ∈ J, ((p ^ (t + 1) : ℕ) : K) * w ∈ B.submodule := by
    intro w hw
    obtain ⟨i, hi, a, ha, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨m, rfl⟩ := Submodule.mem_span_singleton.mp ha
    have hi' : ((p ^ (t + 1) : ℕ) : K) * i ∈ B.submodule := by
      simpa only [zsmul_eq_mul, Int.cast_natCast] using
        B.submodule.smul_mem ((p ^ (t + 1) : ℕ) : ℤ) hi
    have hz' : ((p ^ (t + 1) : ℕ) : K) * (m • z) ∈ B.submodule := by
      convert B.submodule.smul_mem m hz using 1
      simp only [zsmul_eq_mul, Nat.cast_pow]
      ring
    convert B.submodule.add_mem hi' hz' using 1
    ring
  have hn : p ^ (t + 1) ≠ 0 :=
    pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  obtain ⟨B', hB'⟩ := B.exists_submodule_eq hle hn hJbound
  exact ⟨B', hB', by simpa only [hB'] using hJ⟩

/-- A generator of order `p^(t+1)` in `G_{I,η}` shows `p ∣ N`; used by
`pseudolatticeDilog_prod_summand_congr`. -/
private theorem cyclic_summand_prime_dvd_order {p t : ℕ} [Fact p.Prime] {η z : K}
    {T : K} (h : B.IsPeriod η) (hT : η - 1 = (p : K) ^ (t + 1) * T)
    (hTI : ∀ x ∈ B.submodule, T * x ∈ B.submodule)
    (hz : (p : K) ^ (t + 1) * z ∈ B.submodule)
    (hy : (p : K) ^ t * z ∉ B.submodule) :
    p ∣ finiteDilogOrder h.matrix := by
  have hzperiod : (η - 1) * z ∈ B.submodule :=
    cyclic_summand_z_period hT hTI hz
  let gz : finiteDilogGroup h.matrix :=
    h.residueHom (⟨z, hzperiod⟩ : B.torsionLattice η)
  have hgnot : p ^ t • gz ≠ 0 := by
    intro heq
    apply hy
    simpa only [Nat.cast_pow] using (h.residueHom_nsmul_eq_zero_iff
      (⟨z, hzperiod⟩ : B.torsionLattice η) (p ^ t)).mp heq
  have hgfin : p ^ (t + 1) • gz = 0 := by
    change p ^ (t + 1) • h.residueHom
      (⟨z, hzperiod⟩ : B.torsionLattice η) = 0
    exact (h.residueHom_nsmul_eq_zero_iff
      (⟨z, hzperiod⟩ : B.torsionLattice η) (p ^ (t + 1))).mpr (by
        simpa only [Nat.cast_pow] using hz)
  have hgorder : addOrderOf gz = p ^ (t + 1) :=
    addOrderOf_eq_prime_pow hgnot hgfin
  have : NeZero (finiteDilogOrder h.matrix) :=
    finiteDilogOrder_neZero h.isAttractiveFixedPoint
  have hcard : Fintype.card (finiteDilogGroup h.matrix) =
      finiteDilogOrder h.matrix :=
    card_fixedCharacteristics h.matrix _
      (det_sub_one_eq_neg_finiteDilogOrder h.isAttractiveFixedPoint)
  rw [← hcard]
  exact (dvd_pow_self p (by omega : t + 1 ≠ 0)).trans
    (by simpa only [hgorder] using (addOrderOf_dvd_card :
      addOrderOf gz ∣ Fintype.card (finiteDilogGroup h.matrix)))

/-- A shift in `p⁻¹I` is an `η`-torsion point when `η - 1 = p^(t+1)T` and `TI ⊆ I`;
used by `pseudolatticeDilog_prod_summand_congr`. -/
private theorem cyclic_summand_shift_period {p t : ℕ} {η T u : K}
    (hT : η - 1 = (p : K) ^ (t + 1) * T)
    (hTI : ∀ x ∈ B.submodule, T * x ∈ B.submodule)
    (hu : (p : K) * u ∈ B.submodule) :
    (η - 1) * u ∈ B.submodule := by
  have hTu := hTI _ hu
  have hm : (p : K) ^ t * (T * ((p : K) * u)) ∈ B.submodule := by
    simpa only [zsmul_eq_mul, Int.cast_pow, Int.cast_natCast, Nat.cast_pow] using
      B.submodule.smul_mem ((p ^ t : ℕ) : ℤ) hTu
  convert hm using 1
  rw [hT, pow_succ]
  ring

/-- Theorem 4 gives congruence under `p`-torsion translation for a pseudolattice whose
`p`-torsion has order `p`; used by `pseudolatticeDilog_transversal_congr`. -/
private theorem pseudolatticeDilog_translation_congr (v : Valuation ℂ ℝ≥0) {p : ℕ}
    [Fact p.Prime] (hvp : v (p : ℂ) < 1) {η : K} {B' : PseudolatticeBasis F}
    (h' : B'.IsPeriod η)
    (hcard : Nat.card {g : finiteDilogGroup h'.matrix // p • g = 0} = p)
    {x u : K} (hx : (η - 1) * x ∈ B'.submodule)
    (hxu : (η - 1) * (x + u) ∈ B'.submodule)
    (hu : (p : K) * u ∈ B'.submodule) :
    v (pseudolatticeDilog h' (x + u) - pseudolatticeDilog h' x) < 1 := by
  have : NeZero (finiteDilogOrder h'.matrix) :=
    finiteDilogOrder_neZero h'.isAttractiveFixedPoint
  have huJ : (η - 1) * u ∈ B'.submodule := by
    convert B'.submodule.sub_mem hxu hx using 1
    ring
  let a := h'.residueHom (⟨u, huJ⟩ : B'.torsionLattice η)
  let t := h'.residueHom (⟨x, hx⟩ : B'.torsionLattice η)
  have ha : p • a = 0 := by
    change p • h'.residueHom (⟨u, huJ⟩ : B'.torsionLattice η) = 0
    exact (h'.residueHom_nsmul_eq_zero_iff _ p).mpr hu
  have hG : (Finset.univ.filter fun g : finiteDilogGroup h'.matrix => p • g = 0).card = p := by
    simpa only [← Fintype.card_subtype, Nat.card_eq_fintype_card] using hcard
  have hratio := h'.finiteQuantumDilog.translationRatio_unit v hvp hG ha t
  have htval : h'.finiteQuantumDilog.toFun t = pseudolatticeDilog h' x := by
    exact h'.finiteQuantumDilog_residueHom _
  have hatval : h'.finiteQuantumDilog.toFun (a + t) =
      pseudolatticeDilog h' (x + u) := by
    have hadd : a + t = h'.residueHom (⟨x + u, hxu⟩ : B'.torsionLattice η) := by
      calc
        a + t = h'.residueHom
            ((⟨u, huJ⟩ : B'.torsionLattice η) + ⟨x, hx⟩) :=
          (h'.residueHom.map_add _ _).symm
        _ = h'.residueHom ⟨x + u, hxu⟩ := by
          congr 1
          apply Subtype.ext
          change u + x = x + u
          abel
    rw [hadd]
    exact h'.finiteQuantumDilog_residueHom _
  have hvx : v (pseudolatticeDilog h' x) = 1 :=
    pseudolatticeDilog_valuation_eq_one v hvp h' hx
  have hr : v (pseudolatticeDilog h' (x + u) / pseudolatticeDilog h' x - 1) < 1 := by
    simpa only [hatval, htval] using hratio.2
  have hne : pseudolatticeDilog h' x ≠ 0 :=
    v.pos_iff.mp (by rw [hvx]; exact one_pos)
  have heq : pseudolatticeDilog h' (x + u) - pseudolatticeDilog h' x =
      (pseudolatticeDilog h' (x + u) / pseudolatticeDilog h' x - 1) *
        pseudolatticeDilog h' x := by
    field_simp
  rw [heq, map_mul, hvx, mul_one]
  exact hr

open scoped Classical in
/-- Transfers Theorem 4 from an intermediate pseudolattice to a product over its quotient
transversal by the distribution relation (11); used by
`pseudolatticeDilog_prod_summand_congr`. -/
private theorem pseudolatticeDilog_transversal_congr (v : Valuation ℂ ℝ≥0) {p : ℕ}
    [Fact p.Prime] (hvp : v (p : ℂ) < 1) {η : K} (h : B.IsPeriod η)
    {B' : PseudolatticeBasis F} (h' : B'.IsPeriod η)
    (hle : B.submodule ≤ B'.submodule)
    (hJ : ∀ y ∈ B'.submodule, (η - 1) * y ∈ B.submodule)
    {S : Finset K} (hS : IsQuotientTransversal B.submodule B'.submodule S)
    (hcard : Nat.card {g : finiteDilogGroup h'.matrix // p • g = 0} = p)
    {x u : K} (hx : (η - 1) * x ∈ B.submodule)
    (hxu : (η - 1) * (x + u) ∈ B.submodule)
    (hu : (p : K) * u ∈ B'.submodule) :
    v ((∏ t ∈ S, pseudolatticeDilog h (x + u + t)) -
      ∏ t ∈ S, pseudolatticeDilog h (x + t)) < 1 := by
  have hxJ : (η - 1) * x ∈ B'.submodule := hle hx
  have hxuJ : (η - 1) * (x + u) ∈ B'.submodule := hle hxu
  have hvdiff := pseudolatticeDilog_translation_congr v hvp h' hcard hxJ hxuJ hu
  let C : ℂ := etaMultiplier h.matrix ^ S.card / etaMultiplier h'.matrix
  have hC : v C = 1 := by
    dsimp [C]
    rw [map_div₀, map_pow,
      PseudolatticeBasis.IsPeriod.valuation_etaMultiplier v
        h.isAttractiveFixedPoint.trace_pos,
      PseudolatticeBasis.IsPeriod.valuation_etaMultiplier v
        h'.isAttractiveFixedPoint.trace_pos]
    simp
  have hd₀ := pseudolatticeDilog_distribution h hle hJ hS hx
  have hd₁ := pseudolatticeDilog_distribution h hle hJ hS hxu
  change C * pseudolatticeDilog h' x =
    ∏ t ∈ S, pseudolatticeDilog h (x + t) at hd₀
  change C * pseudolatticeDilog h' (x + u) =
    ∏ t ∈ S, pseudolatticeDilog h (x + u + t) at hd₁
  rw [← hd₁, ← hd₀, ← mul_sub, map_mul, hC, one_mul]
  exact hvdiff

/-- **Invariant products over a cyclic summand** [RW26b, Radchenko, Wheeler (2026b), Section 7,
proof of Theorem 7], by the calculation of Section 6, proof of Lemma 5: let `η - 1 = p^sT` with
`TI ⊆ I`, and let `p^sz ∈ I` with `y = p^{s-1}z` not an eigenvector of `T` modulo `I`
(`Ty - cy ∉ I` for every integer `c`). Then for `x ∈ G_{I,η}` and `pu ∈ I`,

$$\prod_{m<p^s} E_{I,\eta}(x+u+mz)\equiv\prod_{m<p^s} E_{I,\eta}(x+mz)\pmod{\mathfrak m}.$$ -/
theorem pseudolatticeDilog_prod_summand_congr (v : Valuation ℂ ℝ≥0) {p : ℕ} [Fact p.Prime]
    (hvp : v (p : ℂ) < 1) {η : K} (h : B.IsPeriod η) {s : ℕ} {T : K}
    (hT : η - 1 = (p : K) ^ s * T) (hTI : ∀ x ∈ B.submodule, T * x ∈ B.submodule) {z : K}
    (hz : (p : K) ^ s * z ∈ B.submodule)
    (hzT : ∀ c : ℤ, T * ((p : K) ^ (s - 1) * z) - c * ((p : K) ^ (s - 1) * z) ∉ B.submodule)
    {x u : K} (hx : (η - 1) * x ∈ B.submodule) (hu : (p : K) * u ∈ B.submodule) :
    v (∏ m ∈ Finset.range (p ^ s), pseudolatticeDilog h (x + u + (m : K) * z) -
      ∏ m ∈ Finset.range (p ^ s), pseudolatticeDilog h (x + (m : K) * z)) < 1 := by
  classical
  cases s with
  | zero =>
    have hzI : z ∈ B.submodule := by simpa only [pow_zero, one_mul] using hz
    exact False.elim ((hzT 0) (by simpa only [Nat.zero_sub, pow_zero, one_mul,
      Int.cast_zero, zero_mul, sub_zero] using hTI z hzI))
  | succ t =>
    let J : Submodule ℤ K := B.submodule ⊔ Submodule.span ℤ {z}
    have hyI : (p : K) ^ t * z ∉ B.submodule := by
      intro hy
      exact hzT 0 (by simpa only [Nat.succ_sub_one, Int.cast_zero, zero_mul,
        sub_zero] using hTI _ hy)
    have horder : addOrderOf (Submodule.Quotient.mk z : K ⧸ B.submodule) =
        p ^ (t + 1) := cyclic_summand_order (Nat.zero_lt_succ t) hz hyI
    obtain ⟨B', hB', hJ'⟩ := cyclic_summand_lattice h hT hTI hz
    have hle' : B.submodule ≤ B'.submodule := by
      rw [hB']
      exact le_sup_left
    let h' : B'.IsPeriod η := h.of_le hle' hJ'
    obtain ⟨w, hw, hwne⟩ := cyclic_summand_not_scalar hT hTI hz hzT horder
    have hε : ∃ w ∈ B'.submodule, (η - 1) / p * w ∉ B'.submodule :=
      ⟨w, by simpa only [hB'] using hw, by simpa only [hB'] using hwne⟩
    have hpI : p ∣ finiteDilogOrder h.matrix :=
      cyclic_summand_prime_dvd_order h hT hTI hz hyI
    have hpJ : p ∣ finiteDilogOrder h'.matrix := by
      rw [← h.finiteDilogOrder_eq h']
      exact hpI
    have hcard := h'.card_torsion_eq_prime hpJ hε
    let S : Finset K := (Finset.range (p ^ (t + 1))).image
      (fun m : ℕ => (m : K) * z)
    have hS : IsQuotientTransversal B.submodule B'.submodule S := by
      rw [hB']
      exact cyclic_summand_transversal B.submodule
        (pow_pos (Fact.out : p.Prime).pos _) horder
    have heu : (η - 1) * u ∈ B.submodule :=
      cyclic_summand_shift_period hT hTI hu
    have hxu : (η - 1) * (x + u) ∈ B.submodule := by
      simpa only [mul_add] using B.submodule.add_mem hx heu
    have hprod := pseudolatticeDilog_transversal_congr v hvp h h' hle' hJ' hS
      hcard hx hxu (hle' hu)
    have hinj := cyclic_summand_image_inj B.submodule horder
    simpa only [S, Finset.prod_image hinj] using hprod

end SIC

end
