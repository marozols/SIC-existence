/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Dilogarithm.Pseudolattice.GroupMaps
import SICs.Dilogarithm.Pseudolattice.Nested
import Mathlib.LinearAlgebra.FreeModule.ModN

/-!
# The `p`-torsion and the `p`-primary part of `G_{I,ε}`

The `p`-torsion of `G_{I,ε}` has order `p` when `p ∣ N` and `ε ≢ 1` on `I/pI`; and when
`ε - 1 = p^sT` with `T` preserving `I` and injective on `p⁻¹I/I`, the `p`-primary part of
`G_{I,ε}` is `p^{-s}I/I ≅ (ℤ/p^s)²`.

This module supplies the two group calculations of [RW26b, Radchenko, Wheeler (2026b),
Section 7, proof of Theorem 7]: the identification `G_{I,η}[p^∞] = p^{-s}I/I` (there from
`BI_{(p)} = I_{(p)}`), and the cyclicity of `G_{J,η}[p^∞]` for the inverse image `J` of a summand,
by the matrix calculation of Section 6, proof of Lemma 5. Both are stated for an arbitrary
pseudolattice `I` with period `ε`, through `G_{I,ε} = (ε - 1)⁻¹I/I`
(`PseudolatticeBasis.IsPeriod.residueHom`).

## The argument

*The `p`-torsion.* `x ↦ px` maps `G_{I,ε}[p] = {x : (ε - 1)x ∈ I, px ∈ I}/I` injectively onto the
kernel of `ε - 1` on `I/pI ≅ 𝔽_p²`. That map is nonzero by hypothesis and has determinant
`N(ε - 1) = 2 - Tr ε = -N ≡ 0 (mod p)`, so it has rank one and its kernel has `p` elements. This
replaces the source's appeal to the entry `B_{21}` of the matrix of `η - 1` in an adapted basis:
the rank of the reduction is what makes the `p`-part cyclic.

*The `p`-primary part.* If `(ε - 1)x = T(p^sx) ∈ I` and `pⁿx ∈ I`, then `y = p^sx` has `Ty ∈ I`
and `pⁿy ∈ I`; injectivity of `T` on `p⁻¹I/I`, applied to `p^{n-1}y, …, y` in turn, gives
`y ∈ I`. Conversely `p^sx ∈ I` gives `(ε - 1)x ∈ TI ⊆ I`. So the `p`-primary part is
`p^{-s}I/I`, and `c ↦ p^{-s}(c₀β₁ + c₁β₂) mod I` is an isomorphism from `(ℤ/p^s)²` for the basis
`(β₁, β₂)` of `I`.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
variable {F : RealQuadraticFieldData K}

namespace PseudolatticeBasis.IsPeriod

variable {B : PseudolatticeBasis F}

/-! ### The `p`-torsion

`|G_{I,ε}[p]| = p` from the rank of `ε - 1` on `I/pI`. -/

/-- Multiplication by `ε - 1` on `I`, used by `card_torsion_eq_prime`. -/
private def differenceHom {ε : K} (h : B.IsPeriod ε) :
    B.submodule →+ B.submodule := by
  refine AddMonoidHom.mk' (fun x => ⟨(ε - 1) * x, ?_⟩) ?_
  · simpa [sub_mul] using B.submodule.sub_mem (h.mul_mem x.property) x.property
  · intro x y
    apply Subtype.ext
    change (ε - 1) * ((x + y : B.submodule) : K) =
      (ε - 1) * (x : K) + (ε - 1) * (y : K)
    simp [mul_add]

/-- The quotient class of `p x ∈ pI` is zero, used by `differenceModHom` and
`torsionToDifferenceKer`. -/
private theorem modN_mkQ_nsmul (G : Type*) [AddCommGroup G] (p : ℕ) (x : G) :
    ModN.mkQ p (p • x) = 0 := by
  change (LinearMap.range (LinearMap.lsmul ℤ G p)).mkQ (p • x) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  refine ⟨x, ?_⟩
  simp

/-- Reduction of `ε - 1` modulo `pI`, used by `card_torsion_eq_prime`. -/
private def differenceModHom {ε : K} (h : B.IsPeriod ε) (p : ℕ) :
    ModN B.submodule p →+ ModN B.submodule p :=
  (ModN.liftEquiv).symm ⟨(ModN.mkQ p).comp h.differenceHom, by
    intro x
    change p • (ModN.mkQ p) (h.differenceHom x) = 0
    rw [← map_nsmul]
    exact modN_mkQ_nsmul _ p _⟩

/-- On a lattice representative, the reduced difference map is the difference followed by
the quotient map; used by `card_torsion_eq_prime`. -/
private theorem differenceModHom_mkQ {ε : K} (h : B.IsPeriod ε) (p : ℕ)
    (x : B.submodule) :
    h.differenceModHom p (ModN.mkQ p x) = ModN.mkQ p (h.differenceHom x) := by
  rfl

/-- The map `G[p] → ker(ε - 1 : I/pI)`, sending a class `x` to `px mod pI`;
used by `card_torsion_eq_prime`. -/
private def torsionToDifferenceKer {ε : K} (h : B.IsPeriod ε) (p : ℕ) :
    {g : finiteDilogGroup h.matrix // p • g = 0} → (h.differenceModHom p).ker := by
  intro g
  let x : B.torsionLattice ε := Classical.choose (h.residueHom_surjective g.1)
  have hx : h.residueHom x = g.1 := Classical.choose_spec (h.residueHom_surjective g.1)
  have hpx : (p : K) * (x : K) ∈ B.submodule := by
    exact (h.residueHom_nsmul_eq_zero_iff x p).mp (by simpa only [hx] using g.2)
  let y : B.submodule := ⟨(p : K) * (x : K), hpx⟩
  have hdy : h.differenceHom y = p • (⟨(ε - 1) * (x : K), x.property⟩ : B.submodule) := by
    apply Subtype.ext
    change (ε - 1) * ((p : K) * (x : K)) =
      (p • (⟨(ε - 1) * (x : K), x.property⟩ : B.submodule) : K)
    simp [nsmul_eq_mul, mul_left_comm]
  refine ⟨ModN.mkQ p y, ?_⟩
  change h.differenceModHom p (ModN.mkQ p y) = 0
  rw [h.differenceModHom_mkQ, hdy]
  exact modN_mkQ_nsmul _ p _

/-- Distinct `p`-torsion residues give distinct elements of the kernel on `I/pI`;
used by `card_torsion_eq_prime`. -/
private theorem torsionToDifferenceKer_injective {ε : K} (h : B.IsPeriod ε)
    {p : ℕ} [Fact p.Prime] : Function.Injective (h.torsionToDifferenceKer p) := by
  intro a b hab
  let xa : B.torsionLattice ε := Classical.choose (h.residueHom_surjective a.1)
  let xb : B.torsionLattice ε := Classical.choose (h.residueHom_surjective b.1)
  have ha : h.residueHom xa = a.1 := Classical.choose_spec (h.residueHom_surjective a.1)
  have hb : h.residueHom xb = b.1 := Classical.choose_spec (h.residueHom_surjective b.1)
  have hq := congrArg Subtype.val hab
  change ModN.mkQ p
    (⟨(p : K) * (xa : K), by
      exact (h.residueHom_nsmul_eq_zero_iff xa p).mp (by simpa [ha] using a.2)⟩ : B.submodule) =
    ModN.mkQ p
    (⟨(p : K) * (xb : K), by
      exact (h.residueHom_nsmul_eq_zero_iff xb p).mp (by simpa [hb] using b.2)⟩ : B.submodule) at hq
  have hmem := ((Submodule.Quotient.eq
    (LinearMap.range (LinearMap.lsmul ℤ B.submodule p))).mp hq)
  obtain ⟨z, hz⟩ := hmem
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have hdiff : (xa : K) - (xb : K) ∈ B.submodule := by
    have heq : (p : K) * ((xa : K) - (xb : K)) = (p : K) * (z : K) := by
      have hh := congrArg (fun t : B.submodule => (t : K)) hz
      simpa [nsmul_eq_mul, mul_sub] using hh.symm
    have : (xa : K) - (xb : K) = (z : K) := mul_left_cancel₀ hp0 heq
    rw [this]
    exact z.property
  have hr : h.residueHom xa = h.residueHom xb := by
    have hm : h.residueHom (xa - xb) = 0 :=
      (h.residueHom_eq_zero_iff (xa - xb)).mpr (by simpa using hdiff)
    simpa only [map_sub, sub_eq_zero] using hm
  exact Subtype.ext (ha ▸ hb ▸ hr)

/-- The hypothesis `ε ≢ 1 (mod pI)` produces a point outside the kernel on `I/pI`;
used by `differenceKer_card_le`. -/
private theorem differenceModHom_not_mem_ker {ε : K} (h : B.IsPeriod ε)
    {p : ℕ} [Fact p.Prime]
    (hε : ∃ y ∈ B.submodule, (ε - 1) / p * y ∉ B.submodule) :
    ∃ q : ModN B.submodule p, q ∉ (h.differenceModHom p).ker := by
  obtain ⟨y, hy, hnot⟩ := hε
  let yy : B.submodule := ⟨y, hy⟩
  refine ⟨ModN.mkQ p yy, ?_⟩
  intro hk
  have hz : ModN.mkQ p (h.differenceHom yy) = 0 := by
    have hm : h.differenceModHom p (ModN.mkQ p yy) = 0 := hk
    simpa only [h.differenceModHom_mkQ] using hm
  change (LinearMap.range (LinearMap.lsmul ℤ B.submodule p)).mkQ
    (h.differenceHom yy) = 0 at hz
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hz
  obtain ⟨z, hz⟩ := hz
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have heq : (p : K) * (z : K) = (ε - 1) * y := by
    have hh := congrArg (fun t : B.submodule => (t : K)) hz
    simpa [nsmul_eq_mul, yy, differenceHom] using hh
  have hdiv : (ε - 1) / (p : K) * y = (z : K) := by
    apply mul_left_cancel₀ hp0
    calc
      (p : K) * ((ε - 1) / (p : K) * y) = (ε - 1) * y := by
        field_simp [hp0]
      _ = (p : K) * z := heq.symm
  exact hnot (hdiv ▸ z.property)

/-- A proper kernel in the rank-two vector space `I/pI` has at most `p` elements;
used by `card_torsion_eq_prime`. -/
private theorem differenceKer_card_le {ε : K} (h : B.IsPeriod ε) {p : ℕ}
    [Fact p.Prime]
    (hε : ∃ y ∈ B.submodule, (ε - 1) / p * y ∉ B.submodule) :
    Nat.card (h.differenceModHom p).ker ≤ p := by
  have : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  have : Module.Free ℤ B.submodule := Module.Free.of_basis B.basis
  have : Module.Finite ℤ B.submodule := Module.Finite.of_basis B.basis
  let f := h.differenceModHom p
  have hv : Nat.card (ModN B.submodule p) = p ^ 2 := by
    calc
      _ = Nat.card (Fin 2 → ZMod p) :=
        Nat.card_congr ((ModN.basis B.basis).equivFun).toEquiv
      _ = p ^ 2 := by simp
  obtain ⟨q, hq⟩ := h.differenceModHom_not_mem_ker hε
  have hproper : f.ker < ⊤ := (lt_top_iff_ne_top).2 (by
    intro heq
    exact hq (heq ▸ AddSubgroup.mem_top q))
  have hdlt : Nat.card f.ker < p ^ 2 := by
    simpa [hv] using AddSubgroup.card_lt_of_lt hproper
  have hdvd : Nat.card f.ker ∣ p ^ 2 := by
    have hh := AddSubgroup.card_dvd_of_le (show f.ker ≤ ⊤ from le_top)
    simpa [hv] using hh
  obtain ⟨k, hk, heq⟩ := (Nat.dvd_prime_pow (Fact.out : Nat.Prime p)).mp hdvd
  rw [heq]
  interval_cases k
  · simpa using (Fact.out : Nat.Prime p).one_le
  · simp
  · omega

/-- **`G_{I,ε}[p]` has order `p`** when `p ∣ N` and `ε ≢ 1` on `I/pI`, i.e. `(ε - 1)y ∉ pI` for
some `y ∈ I`: the cyclicity of the `p`-part shown in [RW26b, Radchenko, Wheeler (2026b),
Section 6, proof of Lemma 5] by the matrix of `η - 1`, and used in Section 7, proof of
Theorem 7. -/
theorem card_torsion_eq_prime {ε : K} (h : B.IsPeriod ε) {p : ℕ} [Fact p.Prime]
    (hp : p ∣ finiteDilogOrder h.matrix)
    (hε : ∃ y ∈ B.submodule, (ε - 1) / p * y ∉ B.submodule) :
    Nat.card {g : finiteDilogGroup h.matrix // p • g = 0} = p := by
  have : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  have : NeZero (finiteDilogOrder h.matrix) :=
    finiteDilogOrder_neZero h.isAttractiveFixedPoint
  have : Module.Free ℤ B.submodule := Module.Free.of_basis B.basis
  have : Module.Finite ℤ B.submodule := Module.Finite.of_basis B.basis
  have hu : Nat.card {g : finiteDilogGroup h.matrix // p • g = 0} ≤ p :=
    (Nat.card_le_card_of_injective (h.torsionToDifferenceKer p)
      h.torsionToDifferenceKer_injective).trans (h.differenceKer_card_le hε)
  have hGcard : Nat.card (finiteDilogGroup h.matrix) = finiteDilogOrder h.matrix := by
    rw [Nat.card_eq_fintype_card]
    exact card_fixedCharacteristics h.matrix _
      (det_sub_one_eq_neg_finiteDilogOrder h.isAttractiveFixedPoint)
  have hpG : p ∣ Nat.card (finiteDilogGroup h.matrix) := by
    rw [hGcard]
    exact hp
  let H : AddSubgroup (finiteDilogGroup h.matrix) := (nsmulAddMonoidHom p).ker
  obtain ⟨g, hg⟩ := exists_prime_addOrderOf_dvd_card' p hpG
  have hpg : g ∈ H := (addOrderOf_dvd_iff_nsmul_eq_zero).mp (by rw [hg])
  let t : H := ⟨g, hpg⟩
  have ht : addOrderOf t = p := (AddSubgroup.addOrderOf_mk g hpg).trans hg
  have hdiv : p ∣ Nat.card H := ht ▸ addOrderOf_dvd_natCard t
  have hl : p ≤ Nat.card {g : finiteDilogGroup h.matrix // p • g = 0} := by
    change p ≤ Nat.card H
    exact Nat.le_of_dvd Nat.card_pos hdiv
  exact le_antisymm hu hl

/-! ### The `p`-primary part

`G_{I,η}[p^∞] = p^{-s}I/I ≅ (ℤ/p^s)²` when `η - 1 = p^sT` with `T` injective on `p⁻¹I/I`. -/

/-- The residue of `x/p^s` for `x ∈ I`, used by `exists_primaryEmbedding`. -/
private def primaryNumeratorHom {η : K} (h : B.IsPeriod η) {p s : ℕ}
    [Fact p.Prime] {T : K}
    (hT : η - 1 = (p : K) ^ s * T)
    (hTI : ∀ x ∈ B.submodule, T * x ∈ B.submodule) :
    B.submodule →+ finiteDilogGroup h.matrix := by
  let n : K := (p : K) ^ s
  refine AddMonoidHom.mk' (fun x => h.residueHom ⟨(x : K) / n, ?_⟩) ?_
  · change (η - 1) * ((x : K) / n) ∈ B.submodule
    have heq : (η - 1) * ((x : K) / n) = T * x := by
      rw [hT]
      simp only [n]
      have hn : (p : K) ^ s ≠ 0 := pow_ne_zero _ (by exact_mod_cast
        (Fact.out : Nat.Prime p).ne_zero)
      field_simp [hn]
    rw [heq]
    exact hTI x x.property
  · intro x y
    rw [← map_add]
    apply congrArg h.residueHom
    apply Subtype.ext
    change (((x + y : B.submodule) : K) / n) =
      ((x : K) / n) + ((y : K) / n)
    simp [add_div]

/-- The numerator residue is killed by `p^s`, so it descends through `I/p^sI` in
`exists_primaryEmbedding`. -/
private theorem primaryNumeratorHom_nsmul {η : K} (h : B.IsPeriod η)
    {p s : ℕ} [Fact p.Prime] {T : K} (hT : η - 1 = (p : K) ^ s * T)
    (hTI : ∀ x ∈ B.submodule, T * x ∈ B.submodule) (x : B.submodule) :
    p ^ s • h.primaryNumeratorHom hT hTI x = 0 := by
  let n : K := (p : K) ^ s
  have hn : n ≠ 0 := pow_ne_zero _ (by exact_mod_cast
    (Fact.out : Nat.Prime p).ne_zero)
  change p ^ s • h.residueHom _ = 0
  apply (h.residueHom_nsmul_eq_zero_iff _ (p ^ s)).mpr
  have heq : (p : K) ^ s * ((x : K) / n) = (x : K) := by
    change n * ((x : K) / n) = (x : K)
    field_simp [hn]
  change ((p ^ s : ℕ) : K) * ((x : K) / n) ∈ B.submodule
  simp only [Nat.cast_pow] at *
  rw [heq]
  exact x.property

/-- A numerator residue vanishes only when its numerator is in `p^sI`, used by
`exists_primaryEmbedding`. -/
private theorem primaryNumeratorHom_eq_zero {η : K} (h : B.IsPeriod η)
    {p s : ℕ} [Fact p.Prime] {T : K} (hT : η - 1 = (p : K) ^ s * T)
    (hTI : ∀ x ∈ B.submodule, T * x ∈ B.submodule) (x : B.submodule)
    (hx : h.primaryNumeratorHom hT hTI x = 0) :
    ModN.mkQ (p ^ s) x = 0 := by
  have hn : (p : K) ^ s ≠ 0 := pow_ne_zero _ (by exact_mod_cast
    (Fact.out : Nat.Prime p).ne_zero)
  have hmem : (x : K) / (p : K) ^ s ∈ B.submodule :=
    (h.residueHom_eq_zero_iff _).mp hx
  change (LinearMap.range (LinearMap.lsmul ℤ B.submodule (p ^ s))).mkQ x = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  refine ⟨⟨(x : K) / (p : K) ^ s, hmem⟩, ?_⟩
  apply Subtype.ext
  change (p ^ s : ℤ) • ((x : K) / (p : K) ^ s) = (x : K)
  simpa only [zsmul_eq_mul, Int.cast_pow, Int.cast_natCast] using
    (mul_div_cancel₀ (x : K) hn)

/-- Iterating injectivity of `T` on `p⁻¹I/I` shows that `Ty ∈ I` and `p^ny ∈ I`
force `y ∈ I`; used by `exists_primaryEmbedding`. -/
private theorem mem_of_primary {p : ℕ} {T : K}
    (hTp : ∀ y : K, T * y ∈ B.submodule → (p : K) * y ∈ B.submodule →
      y ∈ B.submodule) (y : K) (hTy : T * y ∈ B.submodule)
    (n : ℕ) (hpy : (p : K) ^ n * y ∈ B.submodule) : y ∈ B.submodule := by
  induction n generalizing y with
  | zero => simpa using hpy
  | succ n ih =>
      apply hTp y hTy
      apply ih ((p : K) * y)
      · have hm := B.submodule.smul_mem (p : ℤ) hTy
        convert hm using 1
        simp only [zsmul_eq_mul, Int.cast_natCast]
        ring
      · convert hpy using 1
        ring

/-- Every `p`-primary residue comes from a numerator in `I/p^sI`;
used by `exists_primaryEmbedding`. -/
private theorem primaryNumeratorHom_covers {η : K} (h : B.IsPeriod η)
    {p s : ℕ} [Fact p.Prime] {T : K}
    (hT : η - 1 = (p : K) ^ s * T)
    (hTI : ∀ x ∈ B.submodule, T * x ∈ B.submodule)
    (hTp : ∀ y : K, T * y ∈ B.submodule → (p : K) * y ∈ B.submodule →
      y ∈ B.submodule)
    (q : ModN B.submodule (p ^ s) →+ finiteDilogGroup h.matrix)
    (hq : ∀ x : B.submodule,
      q (ModN.mkQ (p ^ s) x) = h.primaryNumeratorHom hT hTI x)
    (g : finiteDilogGroup h.matrix) (n : ℕ) (hg : p ^ n • g = 0) :
    g ∈ Set.range q := by
  obtain ⟨x, rfl⟩ := h.residueHom_surjective g
  have hpx : (p : K) ^ n * (x : K) ∈ B.submodule := by
    simpa only [Nat.cast_pow] using (h.residueHom_nsmul_eq_zero_iff x (p ^ n)).mp hg
  have hTy : T * ((p : K) ^ s * (x : K)) ∈ B.submodule := by
    have hx : (η - 1) * (x : K) ∈ B.submodule := x.property
    rw [hT] at hx
    convert hx using 1
    ring
  have hpy : (p : K) ^ n * ((p : K) ^ s * (x : K)) ∈ B.submodule := by
    have hm := B.submodule.smul_mem (p ^ s : ℤ) hpx
    convert hm using 1
    simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_natCast]
    ring
  have hy : (p : K) ^ s * (x : K) ∈ B.submodule :=
    mem_of_primary hTp _ hTy n hpy
  let y : B.submodule := ⟨(p : K) ^ s * (x : K), hy⟩
  refine ⟨ModN.mkQ (p ^ s) y, ?_⟩
  rw [hq]
  apply congrArg h.residueHom
  apply Subtype.ext
  change ((y : K) / (p : K) ^ s) = (x : K)
  have hp0 : (p : K) ^ s ≠ 0 := pow_ne_zero _ (by exact_mod_cast
    (Fact.out : Nat.Prime p).ne_zero)
  simp [y, hp0]

/-- **`G_{I,η}[p^∞] = p^{-s}I/I ≅ (ℤ/p^s)²`** [RW26b, Radchenko, Wheeler (2026b), Section 7,
proof of Theorem 7]: if `η - 1 = p^sT` where `TI ⊆ I` and `T` is injective on `p⁻¹I/I`, the
`p`-primary part of `G_{I,η}` is the image of an injective homomorphism from `(ℤ/p^s)²`. The
source's hypothesis is that `B = T` is a unit at `p`, so that `BI_{(p)} = I_{(p)}`. -/
theorem exists_primaryEmbedding {η : K} (h : B.IsPeriod η) {p : ℕ} [Fact p.Prime] {s : ℕ}
    {T : K} (hT : η - 1 = (p : K) ^ s * T) (hTI : ∀ x ∈ B.submodule, T * x ∈ B.submodule)
    (hTp : ∀ y : K, T * y ∈ B.submodule → (p : K) * y ∈ B.submodule → y ∈ B.submodule) :
    ∃ e : (Fin 2 → ZMod (p ^ s)) →+ finiteDilogGroup h.matrix,
      Function.Injective e ∧
        ∀ (g : finiteDilogGroup h.matrix) (n : ℕ), p ^ n • g = 0 → g ∈ Set.range e := by
  have : NeZero (p ^ s) := ⟨pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero⟩
  let f : B.submodule →+ finiteDilogGroup h.matrix := h.primaryNumeratorHom hT hTI
  let q : ModN B.submodule (p ^ s) →+ finiteDilogGroup h.matrix :=
    (ModN.liftEquiv).symm ⟨f, h.primaryNumeratorHom_nsmul hT hTI⟩
  let b : ModN B.submodule (p ^ s) ≃ₗ[ZMod (p ^ s)] Fin 2 → ZMod (p ^ s) :=
    (ModN.basis B.basis).equivFun
  have hq (x : B.submodule) : q (ModN.mkQ (p ^ s) x) = f x := by
    rfl
  have hqi : Function.Injective q := by
    apply (injective_iff_map_eq_zero q).2
    intro u hu
    obtain ⟨x, rfl⟩ :=
      (LinearMap.range (LinearMap.lsmul ℤ B.submodule (p ^ s))).mkQ_surjective u
    exact h.primaryNumeratorHom_eq_zero hT hTI x (hq x ▸ hu)
  let e : (Fin 2 → ZMod (p ^ s)) →+ finiteDilogGroup h.matrix :=
    q.comp b.symm.toAddMonoidHom
  refine ⟨e, hqi.comp b.symm.injective, ?_⟩
  intro g n hg
  obtain ⟨u, hu⟩ := h.primaryNumeratorHom_covers hT hTI hTp q hq g n hg
  refine ⟨b u, ?_⟩
  change q (b.symm (b u)) = g
  simpa using hu

end PseudolatticeBasis.IsPeriod

end SIC

end
