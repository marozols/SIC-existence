/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.GroupTheory.Index
import SICs.Quadratic.RealFields

/-!
# The two split lines of a lattice at a prime

Lattices `I ⊆ J₀, J₁` with `[J_i : I] = p`, `J₀ ∩ J₁ = I` and `J₀ + J₁ = p⁻¹I`, each stable under
the multiplier ring of `I`; that ring acts on the lines `J_i/I` by scalars `t_i` with
`t₀ + t₁ ≡ Tr a` and `t₀t₁ ≡ N(a)` modulo `p`, and when `t₀ ≢ t₁` the lines are its only
eigenlines in `p⁻¹I/I`.

This module supplies the lattice algebra of [RW26b, Radchenko, Wheeler (2026b), Section 7]. For an
odd prime `p` split in `K` and prime to the conductor of the multiplier order `𝒪` of `I`, the
source writes `p𝒪 = 𝔭𝔮` and uses the lines `U_𝔭 = 𝔭⁻¹I/I` and `U_𝔮 = 𝔮⁻¹I/I` of order `p` with
`p⁻¹I/I = U_𝔭 ⊕ U_𝔮`, on which `𝒪_K` acts through its two residue maps. `IsSplitLinePair` records
the properties of `J = (𝔭⁻¹I, 𝔮⁻¹I)` that Theorems 7 and 8 use, without ideals of orders; the
reciprocity layer identifies the two lattices with the ideal translates.

## The argument

*Cyclic lines.* `J_i/I` has prime order `p`, so `pJ_i ⊆ I` and every `w ∈ J_i \ I` generates
`J_i` modulo `I`. Two such generators `w₀ ∈ J₀`, `w₁ ∈ J₁` are independent modulo `I`, since
`J₀ ∩ J₁ = I`.

*Scalars.* An element `a` with `aI ⊆ I` preserves `J_i`, so `aw_i ≡ t_i w_i (mod I)` for an
integer `t_i`, and then `ay ≡ t_i y` for every `y ∈ J_i`; by induction `aᵏy ≡ t_iᵏy`.

*Trace and norm.* `a` preserves the finitely generated nonzero `I`, so it is integral and
`Tr a, N(a) ∈ ℤ`, and `a² = Tr(a)a - N(a)` (`sq_eq_trace_mul_sub_norm`). On `J_i/I` this gives
`t_i² ≡ Tr(a)t_i - N(a) (mod p)`. If `t₀ ≢ t₁`, the two are the roots of `X² - Tr(a)X + N(a)`
modulo `p`, so `t₀ + t₁ ≡ Tr a` and `t₀t₁ ≡ N(a)`. If `t₀ ≡ t₁ = t`, then `a` acts on
`p⁻¹I/I = J₀/I + J₁/I` as `t`, so `θ = (a - t)/p` preserves `I`, and `Tr a = 2t + p Tr θ`,
`N(a) = t² + pt Tr θ + p²N(θ)` with `Tr θ, N(θ) ∈ ℤ`.

*Eigenlines.* Write `y ∈ p⁻¹I` as `y₀ + y₁` with `y_i ∈ J_i`. If `ay ≡ cy (mod I)`, then
`(t₀ - c)y₀ ≡ (c - t₁)y₁` lies in `J₀ ∩ J₁ = I`; when `t₀ ≢ t₁`, one of `t₀ - c`, `t₁ - c` is a
unit modulo `p`, so `y₀ ∈ I` or `y₁ ∈ I`, and `y ∈ J₁` or `y ∈ J₀`. In the same way `ay ∈ I`
forces `y ∈ I` when `p ∤ t₀t₁`, and `ay ∈ I` for all `y ∈ p⁻¹I` when `p ∣ t₀` and `p ∣ t₁`.
-/

namespace SIC

variable {K : Type*} [Field K] [NumberField K]

/-! ### Split pairs of lines

The structure, and its lines as cyclic groups of order `p` modulo `I`. -/

/-- **A split pair of lines** of a lattice `I ⊆ K` at a prime `p`: lattices `J₀, J₁` with
`I ⊆ J_i`, `[J_i : I] = p`, `J₀ ∩ J₁ = I`, `p⁻¹I ⊆ J₀ + J₁`, each stable under the multiplier
ring `{a ∈ K : aI ⊆ I}` of `I`. These are the properties of `𝔭⁻¹I` and `𝔮⁻¹I`, for the two primes
`𝔭`, `𝔮` of the multiplier order above an odd split prime `p` prime to its conductor, that
[RW26b, Radchenko, Wheeler (2026b), Section 7] uses through `U_𝔭 = 𝔭⁻¹I/I`, `U_𝔮 = 𝔮⁻¹I/I` and
`p⁻¹I/I = U_𝔭 ⊕ U_𝔮`. -/
structure IsSplitLinePair (p : ℕ) (I : Submodule ℤ K) (J : Fin 2 → Submodule ℤ K) : Prop where
  /-- `I ⊆ J_i`. -/
  le : ∀ i, I ≤ J i
  /-- `[J_i : I] = p`. -/
  relIndex_eq : ∀ i, I.toAddSubgroup.relIndex (J i).toAddSubgroup = p
  /-- `J₀ ∩ J₁ ⊆ I`. -/
  inf_le : J 0 ⊓ J 1 ≤ I
  /-- `p⁻¹I ⊆ J₀ + J₁`. -/
  mem_sup : ∀ y : K, (p : K) * y ∈ I → y ∈ J 0 ⊔ J 1
  /-- `aJ_i ⊆ J_i` whenever `aI ⊆ I`. -/
  mul_mem : ∀ i (a : K), (∀ x ∈ I, a * x ∈ I) → ∀ y ∈ J i, a * y ∈ J i

omit [NumberField K] in
/-- An element `w ∉ I` with `pw ∈ I`, for a prime `p`, has order `p` modulo `I`:
`mw ∈ I ↔ p ∣ m`. Used for the lines of `IsSplitLinePair`. -/
theorem int_mul_mem_iff_dvd {p : ℕ} [Fact p.Prime] {I : Submodule ℤ K} {w : K}
    (hpw : (p : K) * w ∈ I) (hw : w ∉ I) (m : ℤ) : (m : K) * w ∈ I ↔ (p : ℤ) ∣ m := by
  let q : K ⧸ I.toAddSubgroup := QuotientAddGroup.mk w
  have hpq : p • q = 0 := by
    rw [← QuotientAddGroup.mk_nsmul]
    exact (QuotientAddGroup.eq_zero_iff _).2 (by simpa [nsmul_eq_mul] using hpw)
  have hnq : q ≠ 0 := by
    intro hz
    exact hw ((QuotientAddGroup.eq_zero_iff w).1 hz)
  have hq : addOrderOf q = p := (addOrderOf_eq_prime_iff).2 ⟨hpq, hnq⟩
  rw [← hq, addOrderOf_dvd_iff_zsmul_eq_zero]
  change (m : K) * w ∈ I ↔ m • q = 0
  rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff]
  simp only [zsmul_eq_mul]
  rfl

omit [NumberField K] in
/-- If `aI ⊆ I` and `ay ≡ ty (mod I)` on `J`, then `aᵏy ≡ tᵏy (mod I)` on `J`. Used for the
powers of a period on the lines of `IsSplitLinePair`. -/
theorem pow_mul_sub_mem_of_mul_sub_mem {I J : Submodule ℤ K} {a : K}
    (ha : ∀ x ∈ I, a * x ∈ I) {t : ℤ} (ht : ∀ y ∈ J, a * y - t * y ∈ I) (k : ℕ) {y : K}
    (hy : y ∈ J) : a ^ k * y - (t : K) ^ k * y ∈ I := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h₁ := ha _ ih
    have h₂ := I.smul_mem (t ^ k : ℤ) (ht y hy)
    convert I.add_mem h₁ h₂ using 1; simp only [pow_succ, zsmul_eq_mul, Int.cast_pow]; ring

namespace IsSplitLinePair

variable {p : ℕ} {I : Submodule ℤ K} {J : Fin 2 → Submodule ℤ K} (hJ : IsSplitLinePair p I J)
include hJ

omit [NumberField K] in
/-- `pJ_i ⊆ I`: the quotient `J_i/I` has order `p`. -/
theorem prime_mul_mem (i : Fin 2) {y : K} (hy : y ∈ J i) : (p : K) * y ∈ I := by
  let H : AddSubgroup (J i).toAddSubgroup :=
    I.toAddSubgroup.comap (J i).toAddSubgroup.subtype
  have hcard : Nat.card ((J i).toAddSubgroup ⧸ H) = p := hJ.relIndex_eq i
  let q : (J i).toAddSubgroup ⧸ H := QuotientAddGroup.mk ⟨y, hy⟩
  have hzero : p • q = 0 :=
    (addOrderOf_dvd_iff_nsmul_eq_zero).1 (hcard ▸ addOrderOf_dvd_natCard q)
  have hm : p • (⟨y, hy⟩ : (J i).toAddSubgroup) ∈ H := by
    apply (QuotientAddGroup.eq_zero_iff _).1
    change (QuotientAddGroup.mk (p • (⟨y, hy⟩ : (J i).toAddSubgroup)) :
      (J i).toAddSubgroup ⧸ H) = 0
    rw [QuotientAddGroup.mk_nsmul]
    exact hzero
  change p • y ∈ I at hm
  simpa only [nsmul_eq_mul] using hm

omit [NumberField K] in
/-- Each line is nonzero modulo `I`: some `w ∈ J_i` lies outside `I`. -/
theorem exists_mem_notMem [Fact p.Prime] (i : Fin 2) : ∃ w ∈ J i, w ∉ I := by
  by_contra h
  push Not at h
  have hle : (J i).toAddSubgroup ≤ I.toAddSubgroup := fun y hy => h y hy
  have hidx : I.toAddSubgroup.relIndex (J i).toAddSubgroup = 1 :=
    AddSubgroup.relIndex_eq_one.2 hle
  exact (Fact.out : p.Prime).ne_one ((hJ.relIndex_eq i).symm.trans hidx)

omit [NumberField K] in
/-- **A line is cyclic**: any `w ∈ J_i \ I` generates `J_i` modulo `I`, since `J_i/I` has prime
order `p`. -/
theorem exists_int_sub_mem [Fact p.Prime] {i : Fin 2} {w : K} (hw : w ∈ J i) (hwI : w ∉ I)
    {y : K} (hy : y ∈ J i) : ∃ m : ℤ, y - m * w ∈ I := by
  let H : AddSubgroup (J i).toAddSubgroup :=
    I.toAddSubgroup.comap (J i).toAddSubgroup.subtype
  have hcard : Nat.card ((J i).toAddSubgroup ⧸ H) = p := hJ.relIndex_eq i
  let qw : (J i).toAddSubgroup ⧸ H := QuotientAddGroup.mk ⟨w, hw⟩
  have hqw : qw ≠ 0 := by
    intro hz
    exact hwI ((QuotientAddGroup.eq_zero_iff _).1 hz)
  have htop : AddSubgroup.zmultiples qw = ⊤ :=
    zmultiples_eq_top_of_prime_card hcard hqw
  have hqy : (QuotientAddGroup.mk (⟨y, hy⟩ : (J i).toAddSubgroup) :
      (J i).toAddSubgroup ⧸ H) ∈ AddSubgroup.zmultiples qw := by rw [htop]; trivial
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.1 hqy
  refine ⟨m, ?_⟩
  have heq : (QuotientAddGroup.mk (⟨y, hy⟩ : (J i).toAddSubgroup) :
      (J i).toAddSubgroup ⧸ H) =
      QuotientAddGroup.mk (m • (⟨w, hw⟩ : (J i).toAddSubgroup)) := by
    simpa only [QuotientAddGroup.mk_zsmul] using hm.symm
  have hsub := (QuotientAddGroup.eq_iff_sub_mem).1 heq
  change y - m • w ∈ I at hsub
  simpa only [zsmul_eq_mul] using hsub

omit [NumberField K] in
/-- A sum of terms on the two split lines lies in `I` only when each term lies in `I`;
used by `mem_or_mem_of_mul_sub_mem` and `mem_of_mul_mem`. -/
private theorem components_mem {r₀ r₁ : ℤ} {y₀ y₁ : K}
    (hy₀ : y₀ ∈ J 0) (hy₁ : y₁ ∈ J 1)
    (h : (r₀ : K) * y₀ + (r₁ : K) * y₁ ∈ I) :
    (r₀ : K) * y₀ ∈ I ∧ (r₁ : K) * y₁ ∈ I := by
  have h₀J : (r₀ : K) * y₀ ∈ J 0 := by
    simpa only [zsmul_eq_mul] using (J 0).smul_mem r₀ hy₀
  have h₁J : (r₁ : K) * y₁ ∈ J 1 := by
    simpa only [zsmul_eq_mul] using (J 1).smul_mem r₁ hy₁
  have h₀J₁ : (r₀ : K) * y₀ ∈ J 1 := by
    convert (J 1).sub_mem (hJ.le 1 h) h₁J using 1; abel
  have h₀ : (r₀ : K) * y₀ ∈ I := hJ.inf_le ⟨h₀J, h₀J₁⟩
  refine ⟨h₀, ?_⟩
  convert I.sub_mem h h₀ using 1; abel

omit [NumberField K] in
/-- **The two lines are independent modulo `I`**: if `w_i ∈ J_i \ I` and
`m₀w₀ + m₁w₁ ∈ I`, then `p ∣ m₀` and `p ∣ m₁`. -/
theorem dvd_of_add_mem [Fact p.Prime] {w : Fin 2 → K} (hw : ∀ i, w i ∈ J i)
    (hwI : ∀ i, w i ∉ I) {m : Fin 2 → ℤ} (hm : (m 0 : K) * w 0 + m 1 * w 1 ∈ I) :
    ∀ i, (p : ℤ) ∣ m i := by
  obtain ⟨hx0, hx1⟩ := hJ.components_mem (hw 0) (hw 1) hm
  intro i
  fin_cases i
  · exact (int_mul_mem_iff_dvd (hJ.prime_mul_mem 0 (hw 0)) (hwI 0) (m 0)).1 hx0
  · exact (int_mul_mem_iff_dvd (hJ.prime_mul_mem 1 (hw 1)) (hwI 1) (m 1)).1 hx1

omit [NumberField K] in
/-- **The multiplier ring acts on each line by a scalar**: if `aI ⊆ I`, there are integers `t_i`
with `ay ≡ t_i y (mod I)` for `y ∈ J_i`; the source's statement that `𝒪_K` acts on `U_𝔭`, `U_𝔮`
through its two residue maps [RW26b, Radchenko, Wheeler (2026b), Section 7]. -/
theorem exists_scalar [Fact p.Prime] {a : K} (ha : ∀ x ∈ I, a * x ∈ I) :
    ∃ t : Fin 2 → ℤ, ∀ i, ∀ y ∈ J i, a * y - t i * y ∈ I := by
  have hscalar (i : Fin 2) : ∃ t : ℤ, ∀ y ∈ J i, a * y - t * y ∈ I := by
    obtain ⟨w, hw, hwI⟩ := hJ.exists_mem_notMem i
    obtain ⟨t, ht⟩ := hJ.exists_int_sub_mem hw hwI (hJ.mul_mem i a ha w hw)
    refine ⟨t, fun y hy => ?_⟩
    obtain ⟨m, hm⟩ := hJ.exists_int_sub_mem hw hwI hy
    have h₁ := ha _ hm
    have h₂ := I.smul_mem m ht
    have h₃ := I.smul_mem t hm
    convert I.sub_mem (I.add_mem h₁ h₂) h₃ using 1
    simp only [zsmul_eq_mul]
    ring
  classical
  exact ⟨fun i => (hscalar i).choose, fun i => (hscalar i).choose_spec⟩

omit [NumberField K] in
/-- Divisibility by `p` makes an integer scalar vanish on a line modulo `I`;
used by `mul_mem_of_dvd`. -/
private theorem int_mul_mem_of_dvd {i : Fin 2} {y : K} (hy : y ∈ J i) {m : ℤ}
    (hm : (p : ℤ) ∣ m) : (m : K) * y ∈ I := by
  obtain ⟨n, rfl⟩ := hm
  have hp := hJ.prime_mul_mem i hy
  convert I.smul_mem n hp using 1
  simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
  ring

/-- The split pair has a nonzero base lattice; used by `exists_trace_norm_eq`. -/
private theorem lattice_ne_bot [Fact p.Prime] : I ≠ ⊥ := by
  have hpK : (p : K) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  intro hbot
  obtain ⟨w, hw, hwI⟩ := hJ.exists_mem_notMem 0
  have hpw := hJ.prime_mul_mem 0 hw
  rw [hbot] at hpw hwI
  simp only [Submodule.mem_bot] at hpw hwI
  exact hwI ((mul_eq_zero.mp hpw).resolve_left hpK)

omit hJ in
/-- A nonzero finitely generated lattice preserved by `a` makes its trace and norm integral;
used by `exists_trace_norm_eq`. -/
private theorem integral_trace_norm (hIne : I ≠ ⊥) (hI : I.FG) {a : K}
    (ha : ∀ x ∈ I, a * x ∈ I) :
    ∃ T N : ℤ, (T : ℚ) = Algebra.trace ℚ K a ∧ (N : ℚ) = Algebra.norm ℚ a := by
  have haint : IsIntegral ℤ a :=
    isIntegral_of_smul_mem_submodule I hIne hI a (by simpa only [smul_eq_mul] using ha)
  obtain ⟨T, hT⟩ := (IsIntegrallyClosed.isIntegral_iff).1
    (Algebra.isIntegral_trace (L := ℚ) (F := K) haint)
  obtain ⟨N, hN⟩ := (IsIntegrallyClosed.isIntegral_iff).1
    (Algebra.isIntegral_norm (L := K) (K := ℚ) haint)
  exact ⟨T, N, hT, hN⟩

/-- Each scalar on a split line satisfies the quadratic trace-and-norm polynomial modulo `p`;
used by `exists_trace_norm_eq`. -/
private theorem scalar_root_dvd [Fact p.Prime] (hfin : Module.finrank ℚ K = 2)
    {a : K} (ha : ∀ x ∈ I, a * x ∈ I) {t : Fin 2 → ℤ}
    (ht : ∀ i, ∀ y ∈ J i, a * y - t i * y ∈ I) (T N : ℤ)
    (hT : (T : ℚ) = Algebra.trace ℚ K a) (hN : (N : ℚ) = Algebra.norm ℚ a)
    (i : Fin 2) : (p : ℤ) ∣ t i ^ 2 - T * t i + N := by
  have hTK : (T : K) = ((Algebra.trace ℚ K) a : K) := by exact_mod_cast hT
  have hNK : (N : K) = ((Algebra.norm ℚ) a : K) := by exact_mod_cast hN
  have hpoly : a ^ 2 = (T : K) * a - (N : K) := by
    rw [sq_eq_trace_mul_sub_norm hfin a, ← hTK, ← hNK]
  obtain ⟨w, hw, hwI⟩ := hJ.exists_mem_notMem i
  have hpow := pow_mul_sub_mem_of_mul_sub_mem ha (ht i) 2 hw
  have hsm := I.smul_mem T (ht i w hw)
  have heq : a ^ 2 * w = (T : K) * (a * w) - (N : K) * w := by
    rw [hpoly]
    ring
  have hmem : ((t i ^ 2 - T * t i + N : ℤ) : K) * w ∈ I := by
    convert I.add_mem (I.neg_mem hpow) hsm using 1
    simp only [zsmul_eq_mul, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_pow]
    rw [heq]
    ring
  exact (int_mul_mem_iff_dvd (hJ.prime_mul_mem i hw) hwI _).1 hmem

omit hJ in
/-- When `a` has the same scalar on all of `p⁻¹I/I`, its trace is twice that scalar
modulo `p`; used by `trace_sub_sum_dvd_of_eq_scalar`. -/
private theorem trace_eq_of_uniform_scalar [Fact p.Prime]
    (hfin : Module.finrank ℚ K = 2) (hIne : I ≠ ⊥) (hI : I.FG)
    {a : K} {s : ℤ} (hs : ∀ y : K, (p : K) * y ∈ I → a * y - (s : K) * y ∈ I) :
    ∃ U : ℤ, Algebra.trace ℚ K a = ((2 * s + p * U : ℤ) : ℚ) := by
  have hpK : (p : K) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  let θ : K := (a - (s : K)) / (p : K)
  have hθeq : a = (s : K) + (p : K) * θ := by
    dsimp [θ]
    field_simp
    ring
  have hθstable : ∀ x ∈ I, θ * x ∈ I := by
    intro x hx
    have hy : (p : K) * (x / (p : K)) ∈ I := by
      convert hx using 1
      field_simp
    have h := hs (x / (p : K)) hy
    convert h using 1
    dsimp [θ]
    field_simp
  obtain ⟨U, _, hU, _⟩ := integral_trace_norm hIne hI hθstable
  change (U : ℚ) = Algebra.trace ℚ K θ at hU
  have htr : (Algebra.trace ℚ K) a =
      2 * (s : ℚ) + (p : ℚ) * (Algebra.trace ℚ K) θ := by
    rw [hθeq, map_add]
    have hts : (s : K) = algebraMap ℚ K (s : ℚ) := by
      simp only [eq_ratCast, Rat.cast_intCast]
    rw [hts, Algebra.trace_algebraMap]
    have hps : (p : K) * θ = (p : ℚ) • θ := by
      rw [Rat.smul_def]
      norm_cast
    rw [hps, map_smul, hfin]
    simp only [nsmul_eq_mul, smul_eq_mul]
    ring
  refine ⟨U, ?_⟩
  rw [htr, ← hU]
  push_cast
  ring

/-- Congruent scalars on the two lines give the trace congruence through the integral
quotient `(a - t₀)/p`; used by `exists_trace_norm_eq`. -/
private theorem trace_sub_sum_dvd_of_eq_scalar [Fact p.Prime]
    (hfin : Module.finrank ℚ K = 2) (hIne : I ≠ ⊥) (hI : I.FG)
    {a : K} {t : Fin 2 → ℤ} (ht : ∀ i, ∀ y ∈ J i, a * y - t i * y ∈ I)
    (T : ℤ) (hT : (T : ℚ) = Algebra.trace ℚ K a)
    (hdiff : (p : ℤ) ∣ t 1 - t 0) : (p : ℤ) ∣ T - t 0 - t 1 := by
  have hscalar : ∀ y : K, (p : K) * y ∈ I → a * y - (t 0 : K) * y ∈ I := by
    intro y hy
    obtain ⟨y₀, hy₀, y₁, hy₁, hadd⟩ := Submodule.mem_sup.1 (hJ.mem_sup y hy)
    have h₁div := hJ.int_mul_mem_of_dvd hy₁ hdiff
    have h₁scalar : a * y₁ - (t 0 : K) * y₁ ∈ I := by
      convert I.add_mem (ht 1 y₁ hy₁) h₁div using 1
      push_cast
      ring
    rw [← hadd]
    convert I.add_mem (ht 0 y₀ hy₀) h₁scalar using 1; ring
  obtain ⟨U, hU⟩ := trace_eq_of_uniform_scalar hfin hIne hI hscalar
  have hTq : (T : ℚ) = ((2 * t 0 + p * U : ℤ) : ℚ) := by rw [hT, hU]
  have hTint : T = 2 * t 0 + p * U := by exact_mod_cast hTq
  obtain ⟨k, hk⟩ := hdiff
  refine ⟨U - k, ?_⟩
  linear_combination hTint - hk

/-- **The scalars have the trace and norm of `a` modulo `p`**: if `aI ⊆ I` acts on the lines by
`t₀`, `t₁`, then `Tr a = t₀ + t₁ + pu` and `N(a) = t₀t₁ + pw` for integers `u`, `w`. This
generalizes the trace identity of [RW26b, Radchenko, Wheeler (2026b), Section 6, proof of
Lemma 5] as used in the proof of Theorem 7, where the two residues of `B` are opposite. -/
theorem exists_trace_norm_eq [Fact p.Prime] (hfin : Module.finrank ℚ K = 2) (hI : I.FG)
    {a : K} (ha : ∀ x ∈ I, a * x ∈ I) {t : Fin 2 → ℤ}
    (ht : ∀ i, ∀ y ∈ J i, a * y - t i * y ∈ I) :
    ∃ u w : ℤ, Algebra.trace ℚ K a = ((t 0 + t 1 + p * u : ℤ) : ℚ) ∧
      Algebra.norm ℚ a = ((t 0 * t 1 + p * w : ℤ) : ℚ) := by
  have hIne : I ≠ ⊥ := hJ.lattice_ne_bot
  obtain ⟨T, N, hT, hN⟩ := integral_trace_norm hIne hI ha
  have hroot (i : Fin 2) : (p : ℤ) ∣ t i ^ 2 - T * t i + N :=
    hJ.scalar_root_dvd hfin ha ht T N hT hN i
  have hTdiv : (p : ℤ) ∣ T - t 0 - t 1 := by
    by_cases hne : ¬ (p : ℤ) ∣ t 0 - t 1
    · have hprime : Prime (p : ℤ) := by
        rw [Int.prime_iff_natAbs_prime]
        simpa using (Fact.out : p.Prime)
      have hfactor : (p : ℤ) ∣ (t 0 - t 1) * (t 0 + t 1 - T) := by
        convert dvd_sub (hroot 0) (hroot 1) using 1; ring
      have hsumdiv : (p : ℤ) ∣ t 0 + t 1 - T :=
        (hprime.dvd_mul.1 hfactor).resolve_left hne
      convert dvd_neg.mpr hsumdiv using 1; ring
    · have hdiff : (p : ℤ) ∣ t 1 - t 0 := by
        convert dvd_neg.mpr (not_not.mp hne) using 1; ring
      exact hJ.trace_sub_sum_dvd_of_eq_scalar hfin hIne hI ht T hT hdiff
  obtain ⟨u, hu⟩ := hTdiv
  obtain ⟨v, hv⟩ := hroot 0
  have hTeq : T = t 0 + t 1 + p * u := by linear_combination hu
  have hNeq : N = t 0 * t 1 + p * (v + t 0 * u) := by
    linear_combination hv + t 0 * hu
  refine ⟨u, v + t 0 * u, ?_, ?_⟩
  · rw [← hT]; exact_mod_cast hTeq
  · rw [← hN]; exact_mod_cast hNeq

omit [NumberField K] hJ in
/-- If `pw ∈ I`, an integer scalar prime to `p` can annihilate `w` modulo `I` only
when `w ∈ I`; used by `mem_or_mem_of_mul_sub_mem` and `mem_of_mul_mem`. -/
private theorem mem_of_int_mul_mem [Fact p.Prime] {w : K} (hpw : (p : K) * w ∈ I)
    {m : ℤ} (hmw : (m : K) * w ∈ I) (hm : ¬ (p : ℤ) ∣ m) : w ∈ I := by
  by_contra hw
  exact hm ((int_mul_mem_iff_dvd hpw hw m).1 hmw)

omit [NumberField K] in
/-- **The lines are the only eigenlines** when the scalars differ modulo `p`: if `ay ≡ cy (mod I)`
for some `y ∈ p⁻¹I` and integer `c`, then `y ∈ J₀` or `y ∈ J₁`. In [RW26b, Radchenko, Wheeler
(2026b), Section 7, proof of Theorem 7]: the only lines of `I/pI` preserved by `B` are the two
summands. -/
theorem mem_or_mem_of_mul_sub_mem [Fact p.Prime] {a : K} {t : Fin 2 → ℤ}
    (ht : ∀ i, ∀ y ∈ J i, a * y - t i * y ∈ I) (hne : ¬ (p : ℤ) ∣ t 0 - t 1) {y : K}
    (hy : (p : K) * y ∈ I) {c : ℤ} (hc : a * y - c * y ∈ I) : y ∈ J 0 ∨ y ∈ J 1 := by
  obtain ⟨y₀, hy₀, y₁, hy₁, hadd⟩ := Submodule.mem_sup.1 (hJ.mem_sup y hy)
  have hlin : ((t 0 - c : ℤ) : K) * y₀ + ((t 1 - c : ℤ) : K) * y₁ ∈ I := by
    convert I.sub_mem hc (I.add_mem (ht 0 y₀ hy₀) (ht 1 y₁ hy₁)) using 1
    rw [← hadd]
    push_cast
    ring
  obtain ⟨h₀, h₁⟩ := hJ.components_mem hy₀ hy₁ hlin
  by_cases hd₀ : (p : ℤ) ∣ t 0 - c
  · have hd₁ : ¬ (p : ℤ) ∣ t 1 - c := by
      intro hd₁
      apply hne
      convert dvd_sub hd₀ hd₁ using 1; ring
    left
    have hy₁I := mem_of_int_mul_mem (hJ.prime_mul_mem 1 hy₁) h₁ hd₁
    rw [← hadd]
    exact (J 0).add_mem hy₀ (hJ.le 0 hy₁I)
  · right
    have hy₀I := mem_of_int_mul_mem (hJ.prime_mul_mem 0 hy₀) h₀ hd₀
    rw [← hadd]
    exact (J 1).add_mem (hJ.le 1 hy₀I) hy₁

omit [NumberField K] in
/-- **An invertible scalar action**: if `p ∤ t₀` and `p ∤ t₁`, then `ay ∈ I` and `py ∈ I`
force `y ∈ I`, so `a` is injective on `p⁻¹I/I`. -/
theorem mem_of_mul_mem [Fact p.Prime] {a : K} {t : Fin 2 → ℤ}
    (ht : ∀ i, ∀ y ∈ J i, a * y - t i * y ∈ I) (h0 : ¬ (p : ℤ) ∣ t 0)
    (h1 : ¬ (p : ℤ) ∣ t 1) {y : K} (hy : (p : K) * y ∈ I) (hay : a * y ∈ I) : y ∈ I := by
  obtain ⟨y₀, hy₀, y₁, hy₁, hadd⟩ := Submodule.mem_sup.1 (hJ.mem_sup y hy)
  have hlin : (t 0 : K) * y₀ + (t 1 : K) * y₁ ∈ I := by
    convert I.sub_mem hay (I.add_mem (ht 0 y₀ hy₀) (ht 1 y₁ hy₁)) using 1
    rw [← hadd]
    ring
  obtain ⟨ht₀, ht₁⟩ := hJ.components_mem hy₀ hy₁ hlin
  have hy₀I := mem_of_int_mul_mem (hJ.prime_mul_mem 0 hy₀) ht₀ h0
  have hy₁I := mem_of_int_mul_mem (hJ.prime_mul_mem 1 hy₁) ht₁ h1
  rw [← hadd]
  exact I.add_mem hy₀I hy₁I

omit [NumberField K] in
/-- **A vanishing scalar action**: if `p ∣ t₀` and `p ∣ t₁`, then `ay ∈ I` for every
`y ∈ p⁻¹I`. -/
theorem mul_mem_of_dvd {a : K} {t : Fin 2 → ℤ} (ht : ∀ i, ∀ y ∈ J i, a * y - t i * y ∈ I)
    (h0 : (p : ℤ) ∣ t 0) (h1 : (p : ℤ) ∣ t 1) {y : K} (hy : (p : K) * y ∈ I) : a * y ∈ I := by
  obtain ⟨y₀, hy₀, y₁, hy₁, hadd⟩ := Submodule.mem_sup.1 (hJ.mem_sup y hy)
  have h₀ := hJ.int_mul_mem_of_dvd hy₀ h0
  have h₁ := hJ.int_mul_mem_of_dvd hy₁ h1
  have ha₀ : a * y₀ ∈ I := by
    convert I.add_mem (ht 0 y₀ hy₀) h₀ using 1; ring
  have ha₁ : a * y₁ ∈ I := by
    convert I.add_mem (ht 1 y₁ hy₁) h₁ using 1; ring
  rw [← hadd, mul_add]
  exact I.add_mem ha₀ ha₁

end IsSplitLinePair

end SIC
