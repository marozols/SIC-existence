/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Dilogarithm.Frobenius.LatticeTranslation

/-!
# The split Frobenius congruence

For an odd prime `p`, a valuation with `v(p) < 1`, a period `ε` of a pseudolattice `I`, and a
split pair of lines `J₀, J₁` of `I` at `p`, one line `J = J_i` satisfies
`E_{J,ε}(x)/E_{I,ε}(0) ≡ (E_{I,ε}(x)/E_{I,ε}(0))^p (mod 𝔪)` for every `x ∈ G_{I,ε}`.

This module formalizes [RW26b, Radchenko, Wheeler (2026b), Section 7, Theorem 8], with the split
pair of lines `IsSplitLinePair` in place of the source's `𝔭⁻¹I`, `𝔮⁻¹I` at an odd split prime
`p` prime to the conductor of the multiplier order. The reciprocity layer applies it at
absolute-degree-one primes, squared.

## The argument

*The orbit length.* `ε` preserves `I`, so it acts on the lines by integers `e₀`, `e₁`
(`IsSplitLinePair.exists_scalar`) with `e₀e₁ ≡ N(ε) = 1 (mod p)`
(`IsSplitLinePair.exists_trace_norm_eq`): the source's statement that the two residues of `ε` are
inverse. Both have the same order `d ∣ p - 1` modulo `p`. Then `η = εᵈ` acts on both lines as `1`
(`pow_mul_sub_mem_of_mul_sub_mem`), so `(η - 1)/p` preserves `I`
(`IsSplitLinePair.mul_mem_of_dvd`), and Theorem 7 (`pseudolatticeDilog_split_translation`) gives a
line `J = J_i` along which `E_{I,η}` is invariant modulo `𝔪`.

*The period on `J`.* The multiplier ring of `I` preserves each `J_i`, so `εJ_i ⊆ J_i`.
The norm and positivity of `ε` come from its period on `I`; hence it is also a period on
each `J_i` (`IsPeriod.of_mul_mem`).

*The orbits.* `J/I = {mw : m < p}` for `w ∈ J \ I`, and `ε(x + mw) ≡ x + e_imw (mod I)` for
`x ∈ G_{I,ε}`. So the fibre `x + J/I` of `K/I → K/J` over `x` consists of the fixed class `x` and
`(p - 1)/d` orbits of length `d`, `{x + e_iʲrw : j < d}` for `r` in a set `R` of representatives
of `(ℤ/p)ˣ/⟨e_i⟩`; the same at `0`. These are `IsOrbitTransversal`s with lengths `1` and `d`.

*The congruence.* The orbit distribution relation (10), `pseudolatticeDilog_orbit_distribution`,
at `x` and at `0` has the same multiplier factor `μ_{I,ε}^p/μ_{J,ε}`; dividing, and using
`E_{J,ε}(0) = E_{I,ε}(0) = √ε`,

$$\frac{E_{J,\varepsilon}(x)}{E_{I,\varepsilon}(0)}
  =\frac{E_{I,\varepsilon}(x)}{E_{I,\varepsilon}(0)}
   \prod_{r\in R}\frac{E_{I,\eta}(x+rw)}{E_{I,\eta}(rw)}.$$

By Theorem 7 and the power law (8) (`pseudolatticeDilog_pow_period`), each quotient is congruent
to `E_{I,η}(x)/E_{I,η}(0) = (E_{I,ε}(x)/E_{I,ε}(0))^d`; all values are units
(`pseudolatticeDilog_valuation_eq_one`), and the exponent is `1 + d(p - 1)/d = p`.
-/

noncomputable section

open scoped MatrixGroups NNReal

namespace SIC

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
variable {F : RealQuadraticFieldData K} {B : PseudolatticeBasis F}

/-! ### Scalar action and split line orbits

The period acts by inverse residues on the two lines. Nonzero classes on either line split
into cyclic orbits. -/

/-- The split line scalars of a norm-one period are inverse units modulo `p`; used by
`pseudolatticeDilog_frobenius_split`. -/
private theorem split_period_scalars {p : ℕ} [Fact p.Prime] {ε : K}
    (h : B.IsPeriod ε) {J : Fin 2 → Submodule ℤ K}
    (hJ : IsSplitLinePair p B.submodule J) :
    ∃ t : Fin 2 → ℤ, (∀ i, ∀ y ∈ J i, ε * y - (t i : K) * y ∈ B.submodule) ∧
      ∃ u : Fin 2 → (ZMod p)ˣ,
        (∀ i, (u i : ZMod p) = (t i : ZMod p)) ∧ u 0 * u 1 = 1 := by
  have hI : B.submodule.FG := by
    change (Submodule.span ℤ {B.scale * B.tau, B.scale}).FG
    exact Submodule.fg_span (by simp)
  obtain ⟨t, ht⟩ := hJ.exists_scalar (fun x hx => h.mul_mem hx)
  obtain ⟨_, b, _, hn⟩ := hJ.exists_trace_norm_eq F.finrank_eq_two hI
    (fun x hx => h.mul_mem hx) ht
  rw [h.norm_one] at hn
  have hnZ : t 0 * t 1 + (p : ℤ) * b = 1 := by exact_mod_cast hn.symm
  have hmod : (t 0 : ZMod p) * (t 1 : ZMod p) = 1 := by
    have hz := congrArg (fun z : ℤ => (z : ZMod p)) hnZ
    simpa using hz
  have h0 : (t 0 : ZMod p) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hmod
    exact zero_ne_one hmod
  have h1 : (t 1 : ZMod p) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hmod
    exact zero_ne_one hmod
  let u : Fin 2 → (ZMod p)ˣ := ![Units.mk0 _ h0, Units.mk0 _ h1]
  refine ⟨t, ht, u, ?_, ?_⟩
  · intro i
    fin_cases i <;> rfl
  · apply Units.ext
    simpa [u] using hmod

/-- A power whose two line scalars are one modulo `p` has `(εᵈ-1)/p` in the
multiplier ring of `I`; used by
`pseudolatticeDilog_frobenius_split`. -/
private theorem split_period_power {p : ℕ} [Fact p.Prime] {ε : K}
    (h : B.IsPeriod ε) {J : Fin 2 → Submodule ℤ K}
    (hJ : IsSplitLinePair p B.submodule J) {t : Fin 2 → ℤ}
    (ht : ∀ i, ∀ y ∈ J i, ε * y - (t i : K) * y ∈ B.submodule)
    {u : Fin 2 → (ZMod p)ˣ}
    (hu : ∀ i, (u i : ZMod p) = (t i : ZMod p)) {d : ℕ}
    (hd : ∀ i, orderOf (u i) = d) :
    ∀ x ∈ B.submodule, (ε ^ d - 1) / p * x ∈ B.submodule := by
  have hp (i : Fin 2) (y : K) (hy : y ∈ J i) :
      (ε ^ d - 1) * y - (((t i) ^ d - 1 : ℤ) : K) * y ∈ B.submodule := by
    have hh := pow_mul_sub_mem_of_mul_sub_mem (fun x hx => h.mul_mem hx) (ht i) d hy
    convert hh using 1
    push_cast
    ring
  have hdiv (i : Fin 2) : (p : ℤ) ∣ t i ^ d - 1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    have hpow : (u i) ^ d = 1 := by rw [← hd i]; exact pow_orderOf_eq_one _
    have heq : (t i : ZMod p) ^ d = 1 := by
      simpa [← hu i] using congrArg (fun z : (ZMod p)ˣ => (z : ZMod p)) hpow
    simp [heq]
  intro x hx
  have hpK : (p : K) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hy : (p : K) * (x / p) ∈ B.submodule := by
    have heq : (p : K) * (x / p) = x := by field_simp
    rwa [heq]
  convert hJ.mul_mem_of_dvd hp (hdiv 0) (hdiv 1) hy using 1
  field_simp

variable {p : ℕ} [Fact p.Prime] {I : Submodule ℤ K} {w : K}

/-- The standard integer representative of a residue on a cyclic split line; used by
`exists_split_orbit_transversal`. -/
private def lineLift (w : K) (a : ZMod p) : K := (a.val : K) * w
omit [NumberField K] [NumberField.IsTotallyReal K] in
/-- Two standard lifts agree modulo `I` exactly when their residues agree; used by
`exists_split_orbit_transversal`. -/
private theorem lineLift_sub_mem_iff (hpw : (p : K) * w ∈ I) (hw : w ∉ I)
    (a b : ZMod p) : lineLift w a - lineLift w b ∈ I ↔ a = b := by
  have heq : lineLift w a - lineLift w b =
      (((a.val : ℤ) - (b.val : ℤ) : ℤ) : K) * w := by
    simp [lineLift]; ring
  rw [heq, int_mul_mem_iff_dvd hpw hw, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simpa only [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val] using
    (sub_eq_zero : a - b = 0 ↔ a = b)
omit [NumberField K] [NumberField.IsTotallyReal K] in
/-- A standard lift lies on its split line; used by `exists_split_orbit_transversal`. -/
private theorem lineLift_mem {J : Submodule ℤ K} (hw : w ∈ J) (a : ZMod p) :
    lineLift w a ∈ J := by
  simpa [lineLift, zsmul_eq_mul] using J.smul_mem (a.val : ℤ) hw
omit [NumberField K] [NumberField.IsTotallyReal K] in
/-- The period acts on a standard lift by its line scalar; used by
`exists_split_orbit_transversal`. -/
private theorem lineLift_pow_congr {J : Submodule ℤ K} {ε : K} {t : ℤ}
    (ht : ∀ y ∈ J, ε * y - (t : K) * y ∈ I) (hε : ∀ y ∈ I, ε * y ∈ I)
    (hw : w ∈ J) (hpw : (p : K) * w ∈ I) (hnot : w ∉ I)
    {u : (ZMod p)ˣ} (hu : (u : ZMod p) = (t : ZMod p))
    (a : ZMod p) (j : ℕ) :
    ε ^ j * lineLift w a - lineLift w ((u : ZMod p) ^ j * a) ∈ I := by
  have hpow := pow_mul_sub_mem_of_mul_sub_mem hε ht j (lineLift_mem hw a)
  have hmod : ((t ^ j * (a.val : ℤ) -
      (((u : ZMod p) ^ j * a).val : ℤ) : ℤ) : ZMod p) = 0 := by
    simp [hu.symm]
  have hdiv : (p : ℤ) ∣ t ^ j * (a.val : ℤ) -
      (((u : ZMod p) ^ j * a).val : ℤ) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hmod
  have hcoeff : (t : K) ^ j * lineLift w a -
      lineLift w ((u : ZMod p) ^ j * a) ∈ I := by
    have hm := (int_mul_mem_iff_dvd hpw hnot _).mpr hdiv
    convert hm using 1
    simp [lineLift]
    ring
  convert I.add_mem hpow hcoeff using 1
  ring

/-- Two positions in the quotient's chosen representatives agree only when both their
representatives and exponents agree; used by `exists_cyclic_reps`. -/
private theorem cyclic_reps_unique {G : Type*} [CommGroup G] [Finite G] (u : G)
    (r s : G ⧸ Subgroup.zpowers u) (j k : ℕ) (hj : j < orderOf u)
    (hk : k < orderOf u) (heq : u ^ j * r.out = u ^ k * s.out) :
    r = s ∧ j = k := by
  let Q := G ⧸ Subgroup.zpowers u
  have huQ : ((u : G) : Q) = 1 :=
    (QuotientGroup.eq_one_iff u).mpr (Subgroup.mem_zpowers u)
  have heqQ : (r.out : Q) = (s.out : Q) := by
    have h := congrArg (fun a : G => (a : Q)) heq
    simpa [map_mul, map_pow, huQ] using h
  have hrs : r = s := by
    rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at heqQ
    exact heqQ
  constructor
  · exact hrs
  · rw [hrs] at heq
    have hp : u ^ j = u ^ k := mul_right_cancel heq
    exact pow_injOn_Iio_orderOf hj hk hp

/-- Coset representatives for a cyclic subgroup give disjoint equal-length orbits in a finite
commutative group; used by `exists_split_orbit_transversal`. -/
private theorem exists_cyclic_reps {G : Type*} [CommGroup G] [Finite G] (u : G) :
    ∃ R : Finset G,
      (∀ a : G, ∃ r ∈ R, ∃ j < orderOf u, a = u ^ j * r) ∧
      (∀ r ∈ R, ∀ s ∈ R, ∀ j < orderOf u, ∀ k < orderOf u,
        u ^ j * r = u ^ k * s → r = s ∧ j = k) ∧
      Nat.card G = R.card * orderOf u := by
  classical
  have : Fintype G := Fintype.ofFinite G
  let H : Subgroup G := Subgroup.zpowers u
  let Q := G ⧸ H
  let R : Finset G := Finset.univ.image (fun q : Q => q.out)
  have hout : Function.Injective (fun q : Q => (q.out : G)) := Quotient.out_injective
  have hR (r : G) (hr : r ∈ R) : ∃ q : Q, q.out = r := by
    obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hr
    exact ⟨q, hq⟩
  have hHcard : Nat.card H = orderOf u := by
    have e := finEquivZPowers (isOfFinOrder_of_finite u)
    simpa using (Nat.card_congr e).symm
  have hRcard : R.card = Nat.card Q := by
    rw [Finset.card_image_iff.mpr (fun q _ q' _ h => hout h)]
    simp
  refine ⟨R, ?_, ?_, ?_⟩
  · intro a
    let q : Q := (a : Q)
    have hq : ((q.out : G) : Q) = q := QuotientGroup.out_eq' q
    have ha : a / q.out ∈ H :=
      (QuotientGroup.eq_iff_div_mem).mp (by simpa only [q] using hq.symm)
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp
      ((isOfFinOrder_of_finite u).mem_zpowers_iff_mem_range_orderOf.mp ha)
    refine ⟨q.out, Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩,
      j, Finset.mem_range.mp hj, ?_⟩
    calc
      a = (a / q.out) * q.out := (div_mul_cancel a q.out).symm
      _ = u ^ j * q.out := by rw [heq]
  · intro r hr s hs j hj k hk heq
    obtain ⟨q, hq⟩ := hR r hr
    obtain ⟨q', hq'⟩ := hR s hs
    subst r
    subst s
    obtain ⟨hqq, hjk⟩ := cyclic_reps_unique u q q' j k hj hk heq
    exact ⟨congrArg Quotient.out hqq, hjk⟩
  · rw [Subgroup.card_eq_card_quotient_mul_card_subgroup H, ← hRcard, hHcard]


omit [NumberField K] [NumberField.IsTotallyReal K] in
/-- Two iterates on a split line are congruent exactly when their scalar residues agree. -/
private theorem lineLift_pow_sub_mem_iff {J : Submodule ℤ K} {ε : K} {t : ℤ}
    (ht : ∀ y ∈ J, ε * y - (t : K) * y ∈ I) (hε : ∀ y ∈ I, ε * y ∈ I)
    (hw : w ∈ J) (hpw : (p : K) * w ∈ I) (hnot : w ∉ I)
    {u : (ZMod p)ˣ} (hu : (u : ZMod p) = (t : ZMod p))
    (a b : ZMod p) (j k : ℕ) :
    ε ^ j * lineLift w a - ε ^ k * lineLift w b ∈ I ↔
      (u : ZMod p) ^ j * a = (u : ZMod p) ^ k * b := by
  have hj := lineLift_pow_congr ht hε hw hpw hnot hu a j
  have hk := lineLift_pow_congr ht hε hw hpw hnot hu b k
  rw [← lineLift_sub_mem_iff hpw hnot]
  constructor
  · intro h
    convert I.add_mem (I.sub_mem h hj) hk using 1
    ring
  · intro h
    convert I.sub_mem (I.add_mem hj h) hk using 1
    ring

omit [NumberField K] [NumberField.IsTotallyReal K] in
open Classical in
/-- The chosen zero and nonzero lifts lie on the line; used by
`exists_split_orbit_transversal`. -/
private theorem splitOrbit_sub_mem {J : Submodule ℤ K} (hw : w ∈ J) (T : Finset K)
    (hTmem : ∀ y ∈ T, ∃ a : (ZMod p)ˣ, lineLift w (a : ZMod p) = y) :
    ∀ y ∈ insert 0 T, y ∈ J := by
  intro y hy
  rcases Finset.mem_insert.mp hy with rfl | hy
  · exact J.zero_mem
  · obtain ⟨a, rfl⟩ := hTmem y hy
    exact lineLift_mem hw _

omit [NumberField K] [NumberField.IsTotallyReal K] in
open Classical in
/-- The chosen lifts return after their assigned orbit lengths; used by
`exists_split_orbit_transversal`. -/
private theorem splitOrbit_period {J : Submodule ℤ K} {ε : K} {t : ℤ}
    (ht : ∀ y ∈ J, ε * y - (t : K) * y ∈ I)
    (hε : ∀ y ∈ I, ε * y ∈ I) (hw : w ∈ J)
    (hpw : (p : K) * w ∈ I) (hnot : w ∉ I)
    {u : (ZMod p)ˣ} (hu : (u : ZMod p) = (t : ZMod p))
    (T : Finset K) (m : K → ℕ+)
    (hmT : ∀ y ∈ T, (m y : ℕ) = orderOf u)
    (hTmem : ∀ y ∈ T, ∃ a : (ZMod p)ˣ, lineLift w (a : ZMod p) = y) :
    ∀ y ∈ insert 0 T, ε ^ (m y : ℕ) * y - y ∈ I := by
  intro y hy
  rcases Finset.mem_insert.mp hy with rfl | hy
  · simp
  · obtain ⟨a, rfl⟩ := hTmem y hy
    rw [hmT _ hy]
    have hmem := (lineLift_pow_sub_mem_iff ht hε hw hpw hnot hu
      (a : ZMod p) (a : ZMod p) (orderOf u) 0).mpr (by
        simp [← Units.val_pow_eq_pow_val, pow_orderOf_eq_one])
    simpa using hmem

omit [NumberField K] [NumberField.IsTotallyReal K] in
open Classical in
/-- Every split line class has a representative in a chosen orbit; used by
`exists_split_orbit_transversal`. -/
private theorem splitOrbit_exists_pow {J : Fin 2 → Submodule ℤ K} {ε : K}
    (hJ : IsSplitLinePair p I J) (hε : ∀ y ∈ I, ε * y ∈ I)
    {i : Fin 2} (hw : w ∈ J i) (hnot : w ∉ I) {t : ℤ}
    (ht : ∀ y ∈ J i, ε * y - (t : K) * y ∈ I)
    {u : (ZMod p)ˣ} (hu : (u : ZMod p) = (t : ZMod p))
    (R : Finset (ZMod p)ˣ)
    (hcover : ∀ a : (ZMod p)ˣ, ∃ r ∈ R, ∃ j < orderOf u, a = u ^ j * r)
    (T : Finset K) (hRmem : ∀ r ∈ R, lineLift w (r : ZMod p) ∈ T)
    (m : K → ℕ+) (hm0 : (m 0 : ℕ) = 1)
    (hmT : ∀ y ∈ T, (m y : ℕ) = orderOf u) :
    ∀ z, z ∈ J i → ∃ y ∈ insert 0 T, ∃ j < (m y : ℕ), z - ε ^ j * y ∈ I := by
  intro z hz
  obtain ⟨n, hn⟩ := hJ.exists_int_sub_mem hw hnot hz
  let a : ZMod p := (n : ZMod p)
  have hpw : (p : K) * w ∈ I := hJ.prime_mul_mem i hw
  have hza : z - lineLift w a ∈ I := by
    have hmod : ((n - (a.val : ℤ) : ℤ) : ZMod p) = 0 := by simp [a]
    have hcoeff := (int_mul_mem_iff_dvd hpw hnot _).mpr
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hmod)
    convert I.add_mem hn hcoeff using 1
    simp [lineLift]
    ring
  by_cases ha : a = 0
  · refine ⟨0, Finset.mem_insert_self _ _, 0, by simp [hm0], ?_⟩
    simpa [ha, lineLift] using hza
  · let au : (ZMod p)ˣ := Units.mk0 a ha
    obtain ⟨r, hr, j, hj, hrep⟩ := hcover au
    have hrT := hRmem r hr
    refine ⟨lineLift w (r : ZMod p), Finset.mem_insert_of_mem hrT,
      j, by simpa [hmT _ hrT] using hj, ?_⟩
    have hpow := lineLift_pow_congr ht hε hw hpw hnot hu (r : ZMod p) j
    have hrep' : a = (u : ZMod p) ^ j * (r : ZMod p) :=
      congrArg (fun z : (ZMod p)ˣ => (z : ZMod p)) hrep
    rw [← hrep'] at hpow
    convert I.sub_mem hza hpow using 1
    ring

omit [NumberField K] [NumberField.IsTotallyReal K] in
open Classical in
/-- Distinct selected orbit positions remain distinct modulo `I`; used by
`exists_split_orbit_transversal`. -/
private theorem splitOrbit_pow_injective {J : Submodule ℤ K} {ε : K} {t : ℤ}
    (ht : ∀ y ∈ J, ε * y - (t : K) * y ∈ I)
    (hε : ∀ y ∈ I, ε * y ∈ I)
    (hw : w ∈ J) (hpw : (p : K) * w ∈ I) (hnot : w ∉ I)
    {u : (ZMod p)ˣ} (hu : (u : ZMod p) = (t : ZMod p))
    (R : Finset (ZMod p)ˣ)
    (huniq : ∀ r ∈ R, ∀ s ∈ R, ∀ j < orderOf u, ∀ k < orderOf u,
      u ^ j * r = u ^ k * s → r = s ∧ j = k)
    (T : Finset K)
    (hTmem : ∀ y ∈ T, ∃ a ∈ R, lineLift w (a : ZMod p) = y)
    (m : K → ℕ+) (hm0 : (m 0 : ℕ) = 1)
    (hmT : ∀ y ∈ T, (m y : ℕ) = orderOf u) :
    ∀ y ∈ insert 0 T, ∀ y' ∈ insert 0 T,
      ∀ j < (m y : ℕ), ∀ k < (m y' : ℕ),
      ε ^ j * y - ε ^ k * y' ∈ I → y = y' ∧ j = k := by
  intro y hy y' hy' j hj k hk hmem
  rcases Finset.mem_insert.mp hy with rfl | hy
  · have hj0 : j = 0 := by simpa [hm0] using hj
    subst j
    rcases Finset.mem_insert.mp hy' with rfl | hy'
    · have hk0 : k = 0 := by simpa [hm0] using hk
      exact ⟨rfl, hk0.symm⟩
    · obtain ⟨b, _, rfl⟩ := hTmem y' hy'
      have hq := (lineLift_pow_sub_mem_iff ht hε hw hpw hnot hu
        0 b 0 k).mp (by simpa [lineLift] using hmem)
      have hb0 : ((u ^ k * b : (ZMod p)ˣ) : ZMod p) = 0 := by
        simpa [map_pow] using hq.symm
      exact ((Units.ne_zero (u ^ k * b)) hb0).elim
  · obtain ⟨a, ha, rfl⟩ := hTmem y hy
    rcases Finset.mem_insert.mp hy' with rfl | hy'
    · have hq := (lineLift_pow_sub_mem_iff ht hε hw hpw hnot hu
        a 0 j k).mp (by simpa [lineLift] using hmem)
      have ha0 : ((u ^ j * a : (ZMod p)ˣ) : ZMod p) = 0 := by
        simpa only [pow_zero, mul_zero, Units.val_mul, Units.val_pow_eq_pow_val] using hq
      exact ((Units.ne_zero (u ^ j * a)) ha0).elim
    · obtain ⟨b, hb, rfl⟩ := hTmem y' hy'
      have hju : j < orderOf u := by simpa [hmT _ hy] using hj
      have hku : k < orderOf u := by simpa [hmT _ hy'] using hk
      have hq := (lineLift_pow_sub_mem_iff ht hε hw hpw hnot hu
        (a : ZMod p) (b : ZMod p) j k).mp hmem
      have hq' : u ^ j * a = u ^ k * b := Units.ext (by simpa [map_pow] using hq)
      obtain ⟨hab, hjk⟩ := huniq a ha b hb j hju k hku hq'
      exact ⟨congrArg (fun z : (ZMod p)ˣ => lineLift w (z : ZMod p)) hab, hjk⟩

omit [NumberField K] [NumberField.IsTotallyReal K] in
/-- Lifting unit residues is injective; used by `exists_split_orbit_transversal`. -/
private theorem splitOrbit_lift_injective (hpw : (p : K) * w ∈ I) (hnot : w ∉ I) :
    Function.Injective (fun a : (ZMod p)ˣ => lineLift w (a : ZMod p)) := by
  intro a b heq
  have hcong : lineLift w (a : ZMod p) - lineLift w (b : ZMod p) ∈ I := by
    change lineLift w (a : ZMod p) = lineLift w (b : ZMod p) at heq
    rw [heq]
    simp
  exact Units.ext ((lineLift_sub_mem_iff hpw hnot _ _).mp hcong)

omit [NumberField K] [NumberField.IsTotallyReal K] in
/-- A lifted unit residue is outside `I`; used by `exists_split_orbit_transversal`. -/
private theorem splitOrbit_lift_not_mem (hpw : (p : K) * w ∈ I) (hnot : w ∉ I)
    (a : (ZMod p)ˣ) : lineLift w (a : ZMod p) ∉ I := by
  intro hmem
  have ha0 : (a : ZMod p) = 0 :=
    (lineLift_sub_mem_iff hpw hnot _ 0).mp (by simpa [lineLift] using hmem)
  exact (Units.ne_zero a) ha0

omit [Field K] [NumberField K] [NumberField.IsTotallyReal K] in
/-- The fixed class and the selected nonzero orbits account for all `p` classes;
used by `exists_split_orbit_transversal`. -/
private theorem splitOrbit_count (u : (ZMod p)ˣ) (R : Finset (ZMod p)ˣ)
    (T : Finset K) (hTcard : T.card = R.card)
    (hcard : Nat.card (ZMod p)ˣ = R.card * orderOf u) :
    1 + orderOf u * T.card = p := by
  rw [hTcard] at *
  have hUnits : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime (Fact.out : p.Prime)]
  rw [hUnits] at hcard
  have hprime : 0 < p := (Fact.out : p.Prime).pos
  rw [mul_comm (orderOf u) R.card]
  omega

omit [NumberField K] [NumberField.IsTotallyReal K] in
open Classical in
/-- The zero fibre of a split line has one fixed class and equal length nonzero orbits. -/
private theorem exists_split_orbit_transversal {J : Fin 2 → Submodule ℤ K} {ε : K}
    (hJ : IsSplitLinePair p I J) (hε : ∀ y ∈ I, ε * y ∈ I)
    {i : Fin 2} (hw : w ∈ J i) (hnot : w ∉ I) {t : ℤ}
    (ht : ∀ y ∈ J i, ε * y - (t : K) * y ∈ I)
    {u : (ZMod p)ˣ} (hu : (u : ZMod p) = (t : ZMod p)) :
    ∃ T : Finset K, ∃ m : K → ℕ+, 0 ∉ T ∧ m 0 = 1 ∧
      (∀ y ∈ T, (m y : ℕ) = orderOf u) ∧
      (∀ y ∈ T, y ∈ J i ∧ y ∉ I) ∧
      IsOrbitTransversal I (J i) ε 0 (insert 0 T) m ∧
      1 + orderOf u * T.card = p := by
  classical
  let d := orderOf u
  let m : K → ℕ+ := fun y => if y = 0 then 1 else ⟨d, orderOf_pos u⟩
  obtain ⟨R, hcover, huniq, hcard⟩ := exists_cyclic_reps u
  let lift : (ZMod p)ˣ → K := fun a => lineLift w (a : ZMod p)
  let T := R.image lift
  have hpw : (p : K) * w ∈ I := hJ.prime_mul_mem i hw
  have hInject : Function.Injective lift := splitOrbit_lift_injective hpw hnot
  have hTmem (y : K) (hy : y ∈ T) :
      ∃ a ∈ R, lift a = y := Finset.mem_image.mp hy
  have hT0 : 0 ∉ T := by
    intro hz
    obtain ⟨a, _, ha⟩ := hTmem 0 hz
    change lineLift w (a : ZMod p) = 0 at ha
    exact splitOrbit_lift_not_mem hpw hnot a (by rw [ha]; exact I.zero_mem)
  have hTcard : T.card = R.card :=
    Finset.card_image_iff.mpr (fun _ _ _ _ h => hInject h)
  have hmT : ∀ y ∈ T, (m y : ℕ) = orderOf u := by
    intro y hy
    have hy0 : y ≠ 0 := fun hz => hT0 (hz ▸ hy)
    simp [m, hy0, d]
  have hTlift : ∀ y ∈ T, ∃ a : (ZMod p)ˣ, lineLift w (a : ZMod p) = y := by
    intro y hy
    obtain ⟨a, _, ha⟩ := hTmem y hy
    exact ⟨a, ha⟩
  refine ⟨T, m, hT0, by simp [m], hmT, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨a, _, rfl⟩ := hTmem y hy
    exact ⟨lineLift_mem hw _, splitOrbit_lift_not_mem hpw hnot a⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [sub_zero] using splitOrbit_sub_mem hw T hTlift
    · exact splitOrbit_period ht hε hw hpw hnot hu T m hmT hTlift
    · simpa only [sub_zero] using splitOrbit_exists_pow hJ hε hw hnot ht hu R hcover T
        (fun r hr => Finset.mem_image.mpr ⟨r, hr, rfl⟩) m (by simp [m]) hmT
    · exact splitOrbit_pow_injective ht hε hw hpw hnot hu R huniq T
        (fun y hy => hTmem y hy) m (by simp [m]) hmT
  · exact splitOrbit_count u R T hTcard hcard


open Classical in
/-- Translating an orbit transversal by a fixed point gives one for its fibre. -/
private theorem IsOrbitTransversal.translate_fixed {J : Submodule ℤ K} {ε x : K}
    (h : B.IsPeriod ε) (hx : (ε - 1) * x ∈ B.submodule)
    {Y : Finset K} {m : K → ℕ+} (hY : IsOrbitTransversal B.submodule J ε 0 Y m) :
    IsOrbitTransversal B.submodule J ε x (Y.image (x + ·)) (fun y => m (y - x)) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hy
    simpa only [add_sub_cancel_left, sub_zero] using hY.sub_mem r hr
  · intro y hy
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hy
    have hn := h.pow_sub_one_mul_mem hx (m r : ℕ)
    have hrper := hY.period r hr
    convert B.submodule.add_mem hn hrper using 1
    ring_nf
  · intro z hz
    obtain ⟨r, hr, j, hj, hzr⟩ := hY.exists_pow (z - x) (by simpa using hz)
    refine ⟨x + r, Finset.mem_image.mpr ⟨r, hr, rfl⟩,
      j, by simpa only [add_sub_cancel_left] using hj, ?_⟩
    have hxn := h.pow_sub_one_mul_mem hx j
    convert B.submodule.sub_mem hzr hxn using 1
    ring
  · intro y hy y' hy' j hj k hk hcong
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy'
    have hrj : j < (m r : ℕ) := by simpa only [add_sub_cancel_left] using hj
    have hsk : k < (m s : ℕ) := by simpa only [add_sub_cancel_left] using hk
    have hxn := h.pow_sub_one_mul_mem hx j
    have hxm := h.pow_sub_one_mul_mem hx k
    have hrs : ε ^ j * r - ε ^ k * s ∈ B.submodule := by
      convert B.submodule.sub_mem (B.submodule.add_mem hcong hxm) hxn using 1
      ring
    obtain ⟨hrs', hjk⟩ := hY.pow_injective r hr s hs j hrj k hsk hrs
    exact ⟨congrArg (x + ·) hrs', hjk⟩


open Classical in
/-- The orbit product separates its fixed class from the nonzero classes; used by
`split_distribution_ratio`. -/
private theorem orbit_product_expand {ε : K} (h : B.IsPeriod ε)
    {d : ℕ} (hd : 0 < d) {T : Finset K} (hT0 : 0 ∉ T) {m : K → ℕ+}
    (hm0 : (m 0 : ℕ) = 1) (hmT : ∀ r ∈ T, (m r : ℕ) = d)
    {x : K} (hx : (ε - 1) * x ∈ B.submodule) :
    (∏ y ∈ insert 0 T, pseudolatticeDilog (h.pow (m y).pos) (x + y)) =
      pseudolatticeDilog h x *
        ∏ r ∈ T, pseudolatticeDilog (h.pow hd) (x + r) := by
  rw [Finset.prod_insert hT0]
  have hbase : pseudolatticeDilog (h.pow (m 0).pos) (x + 0) =
      pseudolatticeDilog h x := by
    simpa only [add_zero] using
      (by rw [pseudolatticeDilog_pow_period h (m 0).pos hx, hm0, pow_one] :
        pseudolatticeDilog (h.pow (m 0).pos) x = pseudolatticeDilog h x)
  rw [hbase]
  congr 1
  apply Finset.prod_congr rfl
  intro r hr
  congr 1
  exact congrArg (ε ^ ·) (hmT r hr)

/-- Equal orbit multipliers at `0` and `x` cancel in the normalized ratio; used by
`split_distribution_ratio`. -/
private theorem common_multiplier_ratio {A e₀ eₓ j₀ jₓ P₀ Pₓ : ℂ}
    (he₀ : e₀ ≠ 0) (hP₀ : P₀ ≠ 0) (hj₀ : j₀ = e₀)
    (h₀ : A * j₀ = e₀ * P₀) (hₓ : A * jₓ = eₓ * Pₓ) :
    jₓ / e₀ = eₓ / e₀ * (Pₓ / P₀) := by
  rw [hj₀] at h₀
  have hA : A = P₀ := mul_right_cancel₀ he₀ (by simpa [mul_comm] using h₀)
  rw [hA] at hₓ
  have hjₓ : jₓ = eₓ * Pₓ / P₀ := by
    apply (eq_div_iff hP₀).2
    simpa [mul_comm] using hₓ
  rw [hjₓ]
  field_simp [he₀, hP₀]

open Classical in
/-- Dividing the orbit relations at a fixed point and zero removes their common multiplier. -/
private theorem split_distribution_ratio {ε : K} (h : B.IsPeriod ε)
    {B' : PseudolatticeBasis F} (h' : B'.IsPeriod ε)
    (hle : B.submodule ≤ B'.submodule) {d : ℕ} (hd : 0 < d)
    {T : Finset K} (hT0 : 0 ∉ T) {m : K → ℕ+}
    (hm0 : (m 0 : ℕ) = 1) (hmT : ∀ r ∈ T, (m r : ℕ) = d)
    (hY : IsOrbitTransversal B.submodule B'.submodule ε 0 (insert 0 T) m)
    {x : K} (hx : (ε - 1) * x ∈ B.submodule) :
    pseudolatticeDilog h' x / pseudolatticeDilog h 0 =
      pseudolatticeDilog h x / pseudolatticeDilog h 0 *
        ∏ r ∈ T, (pseudolatticeDilog (h.pow hd) (x + r) /
          pseudolatticeDilog (h.pow hd) r) := by
  classical
  let hη := h.pow hd
  let A : ℂ := etaMultiplier h.matrix ^ (∑ y ∈ insert 0 T, (m y : ℕ)) /
    etaMultiplier h'.matrix
  let P0 : ℂ := ∏ r ∈ T, pseudolatticeDilog hη r
  let Px : ℂ := ∏ r ∈ T, pseudolatticeDilog hη (x + r)
  have hrη (r : K) (hr : r ∈ T) : (ε ^ d - 1) * r ∈ B.submodule := by
    have hp := hY.period r (Finset.mem_insert_of_mem hr)
    rw [hmT r hr] at hp
    convert hp using 1
    ring
  have hYx := IsOrbitTransversal.translate_fixed h hx hY
  have hinj : Set.InjOn (x + ·) (↑(insert 0 T : Finset K)) :=
    fun _ _ _ _ hab => add_left_cancel hab
  have hrel0 := pseudolatticeDilog_orbit_distribution h h' hle (by simp) hY
  have hrelx := pseudolatticeDilog_orbit_distribution h h' hle (hle hx) hYx
  change A * pseudolatticeDilog h' 0 =
    ∏ y ∈ insert 0 T, pseudolatticeDilog (h.pow (m y).pos) y at hrel0
  rw [Finset.sum_image hinj, Finset.prod_image hinj] at hrelx
  simp only [add_sub_cancel_left] at hrelx
  change A * pseudolatticeDilog h' x =
    ∏ y ∈ insert 0 T, pseudolatticeDilog (h.pow (m y).pos) (x + y) at hrelx
  have hprod0 : (∏ y ∈ insert 0 T, pseudolatticeDilog (h.pow (m y).pos) y) =
      pseudolatticeDilog h 0 * P0 := by
    simpa only [zero_add] using orbit_product_expand h hd hT0 hm0 hmT
      (x := 0) (by simp)
  have hprodx : (∏ y ∈ insert 0 T,
      pseudolatticeDilog (h.pow (m y).pos) (x + y)) =
      pseudolatticeDilog h x * Px := by
    exact orbit_product_expand h hd hT0 hm0 hmT hx
  rw [hprod0] at hrel0
  rw [hprodx] at hrelx
  have hE0 : pseudolatticeDilog h 0 ≠ 0 := pseudolatticeDilog_ne_zero h (by simp)
  have hJ0 : pseudolatticeDilog h' 0 = pseudolatticeDilog h 0 := by
    rw [pseudolatticeDilog_of_mem h' (by simp),
      pseudolatticeDilog_of_mem h (by simp)]
  have hP0 : P0 ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro r hr
    exact pseudolatticeDilog_ne_zero hη (hrη r hr)
  rw [Finset.prod_div_distrib]
  change pseudolatticeDilog h' x / pseudolatticeDilog h 0 =
    pseudolatticeDilog h x / pseudolatticeDilog h 0 * (Px / P0)
  exact common_multiplier_ratio hE0 hP0 hJ0 hrel0 hrelx

/-- Translation invariance gives the same congruence for normalized dilogarithm values; used by
`split_orbit_product_congr`. -/
private theorem translated_dilog_ratio_congr (v : Valuation ℂ ℝ≥0) {p : ℕ}
    [Fact p.Prime] (hvp : v (p : ℂ) < 1) {η : K} (hη : B.IsPeriod η)
    {J : Submodule ℤ K}
    (htrans : ∀ x : K, (η - 1) * x ∈ B.submodule → ∀ y ∈ J,
      v (pseudolatticeDilog hη (x + y) - pseudolatticeDilog hη x) < 1)
    {x r : K} (hx : (η - 1) * x ∈ B.submodule)
    (hr : (η - 1) * r ∈ B.submodule) (hrJ : r ∈ J) :
    v (pseudolatticeDilog hη (x + r) / pseudolatticeDilog hη r -
      pseudolatticeDilog hη x / pseudolatticeDilog hη 0) < 1 := by
  have hvx := pseudolatticeDilog_valuation_eq_one v hvp hη hx
  have hvr := pseudolatticeDilog_valuation_eq_one v hvp hη hr
  have hv0 : v (pseudolatticeDilog hη 0) = 1 :=
    pseudolatticeDilog_valuation_eq_one v hvp hη (by simp)
  exact valuation_div_sub_div_lt_one v hvx.le hvr hv0
    (htrans x hx r hrJ) (by simpa only [zero_add] using htrans 0 (by simp) r hrJ)

open Classical in
/-- The congruences of the nonzero orbit factors multiply; used by `split_orbit_congr`. -/
private theorem split_orbit_product_congr (v : Valuation ℂ ℝ≥0) {p : ℕ}
    [Fact p.Prime] (hvp : v (p : ℂ) < 1) {ε : K} (h : B.IsPeriod ε)
    {B' : PseudolatticeBasis F} {d : ℕ} (hd : 0 < d)
    {T : Finset K} {m : K → ℕ+}
    (hmT : ∀ r ∈ T, (m r : ℕ) = d)
    (hY : IsOrbitTransversal B.submodule B'.submodule ε 0 (insert 0 T) m)
    (hTmem : ∀ r ∈ T, r ∈ B'.submodule)
    (htrans : ∀ x : K, (ε ^ d - 1) * x ∈ B.submodule → ∀ y ∈ B'.submodule,
      v (pseudolatticeDilog (h.pow hd) (x + y) - pseudolatticeDilog (h.pow hd) x) < 1)
    {x : K} (hx : (ε - 1) * x ∈ B.submodule) :
    v ((∏ r ∈ T, pseudolatticeDilog (h.pow hd) (x + r) /
      pseudolatticeDilog (h.pow hd) r) -
      (pseudolatticeDilog (h.pow hd) x / pseudolatticeDilog (h.pow hd) 0) ^ T.card) < 1 := by
  let hη := h.pow hd
  have hxη : (ε ^ d - 1) * x ∈ B.submodule := by
    exact h.pow_sub_one_mul_mem hx d
  have hrη (r : K) (hr : r ∈ T) : (ε ^ d - 1) * r ∈ B.submodule := by
    have hp := hY.period r (Finset.mem_insert_of_mem hr)
    rw [hmT r hr] at hp
    convert hp using 1
    ring
  have hxrη (r : K) (hr : r ∈ T) : (ε ^ d - 1) * (x + r) ∈ B.submodule := by
    convert B.submodule.add_mem hxη (hrη r hr) using 1
    ring
  have hvqη : v (pseudolatticeDilog hη x / pseudolatticeDilog hη 0) = 1 := by
    rw [v.map_div, pseudolatticeDilog_valuation_eq_one v hvp hη hxη,
      pseudolatticeDilog_valuation_eq_one v hvp hη (by simp)]
    simp
  have hprod := valuation_prod_sub_prod_lt_one v T
    (fun r => pseudolatticeDilog hη (x + r) / pseudolatticeDilog hη r)
    (fun _ => pseudolatticeDilog hη x / pseudolatticeDilog hη 0) (by
      intro r hr
      rw [v.map_div, pseudolatticeDilog_valuation_eq_one v hvp hη (hxrη r hr),
        pseudolatticeDilog_valuation_eq_one v hvp hη (hrη r hr)]
      simp)
    (by intro _ _; exact hvqη.le)
    (by
      intro r hr
      exact translated_dilog_ratio_congr v hvp hη htrans hxη
        (hrη r hr) (hTmem r hr))
  have hconst : (∏ _ ∈ T, pseudolatticeDilog hη x / pseudolatticeDilog hη 0) =
      (pseudolatticeDilog hη x / pseudolatticeDilog hη 0) ^ T.card := by
    simp [div_pow]
  rw [hconst] at hprod
  exact hprod


open Classical in
/-- Translation invariance turns the split orbit product into the Frobenius power. -/
private theorem split_orbit_congr (v : Valuation ℂ ℝ≥0) {p : ℕ} [Fact p.Prime]
    (hvp : v (p : ℂ) < 1) {ε : K} (h : B.IsPeriod ε)
    {B' : PseudolatticeBasis F} (h' : B'.IsPeriod ε)
    (hle : B.submodule ≤ B'.submodule) {d : ℕ} (hd : 0 < d)
    {T : Finset K} (hT0 : 0 ∉ T) {m : K → ℕ+}
    (hm0 : (m 0 : ℕ) = 1) (hmT : ∀ r ∈ T, (m r : ℕ) = d)
    (hY : IsOrbitTransversal B.submodule B'.submodule ε 0 (insert 0 T) m)
    (hcount : 1 + d * T.card = p) (hTmem : ∀ r ∈ T, r ∈ B'.submodule)
    (htrans : ∀ x : K, (ε ^ d - 1) * x ∈ B.submodule → ∀ y ∈ B'.submodule,
      v (pseudolatticeDilog (h.pow hd) (x + y) - pseudolatticeDilog (h.pow hd) x) < 1)
    (x : K) (hx : (ε - 1) * x ∈ B.submodule) :
    v (pseudolatticeDilog h' x / pseudolatticeDilog h 0 -
      (pseudolatticeDilog h x / pseudolatticeDilog h 0) ^ p) < 1 := by
  classical
  let hη := h.pow hd
  let q : ℂ := pseudolatticeDilog h x / pseudolatticeDilog h 0
  let qη : ℂ := pseudolatticeDilog hη x / pseudolatticeDilog hη 0
  have hvx : v (pseudolatticeDilog h x) = 1 :=
    pseudolatticeDilog_valuation_eq_one v hvp h hx
  have hv0 : v (pseudolatticeDilog h 0) = 1 :=
    pseudolatticeDilog_valuation_eq_one v hvp h (by simp)
  have hvq : v q = 1 := by simp [q, v.map_div, hvx, hv0]
  have hprod := split_orbit_product_congr v hvp h hd hmT hY hTmem htrans hx
  have hqpow : qη = q ^ d := by
    change pseudolatticeDilog (h.pow hd) x / pseudolatticeDilog (h.pow hd) 0 =
      (pseudolatticeDilog h x / pseudolatticeDilog h 0) ^ d
    rw [pseudolatticeDilog_pow_period h hd hx,
      pseudolatticeDilog_pow_period h hd (by simp), div_pow]
  have hpower : q ^ p = q * qη ^ T.card := by
    rw [hqpow, ← pow_mul, ← hcount, pow_add, pow_one]
  have hratio := split_distribution_ratio h h' hle hd hT0 hm0 hmT hY hx
  rw [hratio, hpower, ← mul_sub, v.map_mul, hvq]
  simpa using hprod



/-- **[RW26b, Radchenko, Wheeler (2026b), Section 7, Theorem 8] (split Frobenius)**: let `p` be an
odd prime, `v` a valuation of `ℂ` with `v(p) < 1`, `ε` a period of `I`, and `J₀, J₁` a split pair
of lines of `I` at `p` with admissible bases. Then for one `i`, the same
for every `x`,

$$\frac{E_{J_i,\varepsilon}(x)}{E_{I,\varepsilon}(0)}\equiv
  \Big(\frac{E_{I,\varepsilon}(x)}{E_{I,\varepsilon}(0)}\Big)^p\pmod{\mathfrak m}
  \qquad(x\in G_{I,\varepsilon}).$$

The source states it at an odd split prime `p` prime to the conductor of the multiplier order,
with `J = (𝔭⁻¹I, 𝔮⁻¹I)`. The split pair makes `ε` a period of each `J_i`
(`IsPeriod.of_mul_mem`). -/
@[source "RW26b, Theorem 8, p. 12"]
theorem pseudolatticeDilog_frobenius_split (v : Valuation ℂ ℝ≥0) {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (hvp : v (p : ℂ) < 1) {ε : K} (h : B.IsPeriod ε)
    {B' : Fin 2 → PseudolatticeBasis F}
    (hJ : IsSplitLinePair p B.submodule fun i => (B' i).submodule) :
    ∃ i, ∀ x : K, (ε - 1) * x ∈ B.submodule →
      v (pseudolatticeDilog
          (h.of_mul_mem (hJ.mul_mem i ε (fun _ hx => h.mul_mem hx))) x /
          pseudolatticeDilog h 0 -
        (pseudolatticeDilog h x / pseudolatticeDilog h 0) ^ p) < 1 := by
  let h' (i : Fin 2) : (B' i).IsPeriod ε :=
    h.of_mul_mem (hJ.mul_mem i ε (fun _ hx => h.mul_mem hx))
  obtain ⟨t, ht, u, hu, hunorm⟩ := split_period_scalars h hJ
  let d := orderOf (u 0)
  have hd : 0 < d := orderOf_pos _
  have horder : ∀ i : Fin 2, orderOf (u i) = d := by
    intro i
    fin_cases i
    · rfl
    · have h1 : u 1 = (u 0)⁻¹ := eq_inv_of_mul_eq_one_right hunorm
      change orderOf (u 1) = d
      rw [h1, orderOf_inv]
  let hη := h.pow hd
  have hηcond := split_period_power h hJ ht hu horder
  obtain ⟨i, hi⟩ := pseudolatticeDilog_split_translation v hp hvp hη hηcond hJ
  obtain ⟨w, hw, hwI⟩ := hJ.exists_mem_notMem i
  obtain ⟨T, m, hT0, hm0, hmT, hTmem, hY, hcount⟩ :=
    exists_split_orbit_transversal hJ (fun y hy => h.mul_mem hy) hw hwI (ht i) (hu i)
  have hmTd : ∀ r ∈ T, (m r : ℕ) = d := by
    intro r hr
    rw [← horder i]
    exact hmT r hr
  have hcountd : 1 + d * T.card = p := by
    rw [← horder i]
    exact hcount
  have hm0Nat : (m 0 : ℕ) = 1 := by
    simpa using congrArg (fun z : ℕ+ => (z : ℕ)) hm0
  refine ⟨i, ?_⟩
  intro x hx
  exact split_orbit_congr v hvp h (h' i) (hJ.le i) hd hT0 hm0Nat hmTd hY hcountd
    (fun r hr => (hTmem r hr).1) hi x hx

end SIC

end
