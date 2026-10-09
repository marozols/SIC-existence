/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Dilogarithm.MetricGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Torsion
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Perm.Cycle.Type
/-!
# The `p`-primary part of a metric group in coordinates

Coordinates for the cyclic and two-coordinate primary components, their torsion, pairings, and
coset Fourier sums.

This module follows the coordinate reduction in [RW26b, Radchenko, Wheeler (2026b), Section 4,
Lemma 1]. It supplies the group and pairing models used by
`SICs.Dilogarithm.Valuation.FourierIntegral`.

## The argument

Successive `p`-power kernels show that the primary component is cyclic when `|G[p]| = p`. Its
index is prime to `p`: an element of order `p` in the quotient would lift into the primary
component. Multiplication by `p^(s-1)` gives standard coordinates on
the `p`-torsion of `(ZMod (p^s))²`. Nondegeneracy of the bicharacter supplies a primitive root
and realizes each Fourier frequency. Character orthogonality turns a global Fourier transform
into a sum over a primary-component coset. Reindexing this identity in a coordinate model gives
the model Fourier bound used for the residue moments.
-/

open scoped NNReal

namespace SIC

variable {G : Type*} [AddCommGroup G] [Fintype G] {L : Type*} [Field L]

/-! ### Finite abelian group helpers

The cyclicity criterion and the prime-to-`p` index of the primary component are used in the
reduction of `IsFourierIntegral` to a cyclic model. -/

/-- The subgroup killed by `p^k`, used by `primaryComponent_cyclic_of_card_torsion`. -/
private def pPowerKernel {A : Type*} [AddCommGroup A] (p k : ℕ) : AddSubgroup A :=
  (nsmulAddMonoidHom (α := A) (p ^ k)).ker

/-- Multiplication by `p` from the `p^(k+1)`-kernel to the `p^k`-kernel, used by
`pPowerKernel_card_le`. -/
private def pPowerKernelMap {A : Type*} [AddCommGroup A] (p k : ℕ) :
    pPowerKernel (A := A) p (k + 1) →+ pPowerKernel (A := A) p k where
  toFun x := ⟨p • (x : A), by
    have hx : p ^ (k + 1) • (x : A) = 0 := x.property
    change p ^ k • (p • (x : A)) = 0
    simpa only [pow_succ, mul_smul] using hx⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp [smul_add]

open scoped Classical in
/-- The kernel of multiplication by `p` on a successive power kernel embeds in the
`p`-torsion. Used by `pPowerKernel_card_le`. -/
private theorem pPowerKernelMap_ker_card_le {A : Type*} [AddCommGroup A] [Finite A]
    (p : ℕ) (hp : Nat.card (pPowerKernel (A := A) p 1) ≤ p) (k : ℕ) :
    Nat.card (pPowerKernelMap (A := A) p k).ker ≤ p := by
  let _ : Fintype A := Fintype.ofFinite A
  let q := pPowerKernelMap (A := A) p k
  let φ : q.ker → pPowerKernel (A := A) p 1 := fun x =>
    ⟨(x.1 : A), by
      have hx : q x.1 = 0 := x.property
      have hx' := congrArg Subtype.val hx
      change p • (x.1 : A) = 0 at hx'
      change p ^ 1 • (x.1 : A) = 0
      simpa only [pow_one] using hx'⟩
  have hi : Function.Injective φ := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : pPowerKernel (A := A) p 1 => (z : A)) h
  simpa only [Nat.card_eq_fintype_card] using
    (Fintype.card_le_of_injective φ hi).trans
      (by simpa only [Nat.card_eq_fintype_card] using hp)

open scoped Classical in
/-- If at most `p` elements are killed by `p`, then at most `p^k` are killed by `p^k`.
Used by `primaryComponent_cyclic_of_card_torsion`. -/
private theorem pPowerKernel_card_le {A : Type*} [AddCommGroup A] [Finite A] (p : ℕ)
    (hp : Nat.card (pPowerKernel (A := A) p 1) ≤ p) (k : ℕ) :
    Nat.card (pPowerKernel (A := A) p k) ≤ p ^ k := by
  let _ : Fintype A := Fintype.ofFinite A
  induction k with
  | zero =>
    have h : Subsingleton (pPowerKernel (A := A) p 0) := by
      constructor
      intro a b
      apply Subtype.ext
      have ha : (a : A) = 0 := by simpa [pPowerKernel] using a.property
      have hb : (b : A) = 0 := by simpa [pPowerKernel] using b.property
      simp [ha, hb]
    simpa only [Nat.card_eq_fintype_card, pow_zero] using
      (Fintype.card_le_one_iff_subsingleton.mpr h)
  | succ k ih =>
    let q := pPowerKernelMap (A := A) p k
    have hk : Nat.card q.ker ≤ p := pPowerKernelMap_ker_card_le p hp k
    have hr : Nat.card q.range ≤ Nat.card (pPowerKernel (A := A) p k) := by
      simpa only [Nat.card_eq_fintype_card] using
        Fintype.card_le_of_injective (fun x : q.range => (x : pPowerKernel (A := A) p k))
          (fun x y h => Subtype.ext h)
    have hc : Nat.card (pPowerKernel (A := A) p (k + 1)) =
        Nat.card q.ker * Nat.card q.range := by
      rw [← q.ker.card_mul_index, AddSubgroup.index_ker]
    calc
      Nat.card (pPowerKernel (A := A) p (k + 1)) =
          Nat.card q.ker * Nat.card q.range := hc
      _ ≤ p * p ^ k := mul_le_mul' hk (hr.trans ih)
      _ = p ^ (k + 1) := (pow_succ' p k).symm

open scoped Classical in
/-- A finite abelian `p`-group with at most `p` elements killed by `p` is cyclic.
Used by `primaryComponent_cyclic_of_card_torsion`. -/
private theorem isAddCyclic_of_card_pPowerKernel_le {A : Type*} [AddCommGroup A]
    [Finite A] {p : ℕ} (hp : p.Prime) (s : ℕ) (hcard : Nat.card A = p ^ s)
    (hker : Nat.card (pPowerKernel (A := A) p 1) ≤ p) : IsAddCyclic A := by
  have he : AddMonoid.exponent A ∣ p ^ s := hcard ▸ AddGroup.exponent_dvd_nat_card
  obtain ⟨k, hks, heq⟩ := (Nat.dvd_prime_pow hp).mp he
  have htop : pPowerKernel (A := A) p k = ⊤ := by
    apply eq_top_iff.mpr
    intro x hx
    change p ^ k • x = 0
    rw [← heq]
    exact AddMonoid.exponent_nsmul_eq_zero x
  have hle : p ^ s ≤ p ^ k := by
    calc
      p ^ s = Nat.card A := hcard.symm
      _ = Nat.card (pPowerKernel (A := A) p k) := by rw [htop, AddSubgroup.card_top]
      _ ≤ p ^ k := pPowerKernel_card_le p hker k
  apply IsAddCyclic.of_exponent_eq_card
  calc
    AddMonoid.exponent A = p ^ k := heq
    _ = p ^ s := Nat.le_antisymm (Nat.pow_le_pow_right hp.pos hks) hle
    _ = Nat.card A := hcard.symm

open scoped Classical in
/-- The `p`-primary part of a finite abelian group is cyclic when its `p`-torsion has
cardinality `p`. Used by `IsFourierIntegral`'s residue-moment reduction. -/
theorem primaryComponent_cyclic_of_card_torsion {A : Type*} [AddCommGroup A]
    [Fintype A] [DecidableEq A] {p : ℕ} [Fact p.Prime]
    (hA : (Finset.univ.filter fun u : A => p • u = 0).card = p) :
    ∃ s : ℕ, Nat.card (AddCommGroup.primaryComponent A p) = p ^ s ∧
      IsAddCyclic (AddCommGroup.primaryComponent A p) := by
  let H := AddCommGroup.primaryComponent A p
  have hP : IsPGroup p (Multiplicative H) := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro x
    obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp x.toAdd.property
    refine ⟨k, ?_⟩
    change (p ^ k • (x.toAdd : H)) = 0
    exact Subtype.ext hk
  obtain ⟨s, hs⟩ := IsPGroup.iff_card.mp hP
  have hcard : Nat.card H = p ^ s := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_multiplicative] using hs
  have hker : Nat.card (pPowerKernel (A := H) p 1) ≤ p := by
    let φ : pPowerKernel (A := H) p 1 → {u : A // p • u = 0} := fun x =>
      ⟨(x : H).1, by
        have hx : p • (x : H) = 0 := by simpa [pPowerKernel] using x.property
        exact congrArg Subtype.val hx⟩
    have hi : Function.Injective φ := by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : {u : A // p • u = 0} => z.1) h
    calc
      Nat.card (pPowerKernel (A := H) p 1) = Fintype.card (pPowerKernel (A := H) p 1) :=
        Nat.card_eq_fintype_card
      _ ≤ Fintype.card {u : A // p • u = 0} := Fintype.card_le_of_injective φ hi
      _ = p := by simpa only [Fintype.card_subtype] using hA
  exact ⟨s, hcard, isAddCyclic_of_card_pPowerKernel_le Fact.out s hcard hker⟩

open scoped Classical in
/-- The cyclic `p`-primary part has positive exponent when `|G[p]| = p`.
Used by `IsFourierIntegral`'s residue-moment reduction. -/
theorem primaryComponent_exponent_pos {A : Type*} [AddCommGroup A]
    [Fintype A] [DecidableEq A] {p s : ℕ} [Fact p.Prime]
    (hA : (Finset.univ.filter fun u : A => p • u = 0).card = p)
    (hcard : Nat.card (AddCommGroup.primaryComponent A p) = p ^ s) : 1 ≤ s := by
  let H := AddCommGroup.primaryComponent A p
  let φ : {u : A // p • u = 0} → H := fun x =>
    ⟨x.1, AddCommGroup.mem_primaryComponent.mpr ⟨1, by simpa using x.property⟩⟩
  have hi : Function.Injective φ := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : H => (z : A)) h
  have hle : p ≤ p ^ s := by
    calc
      p = Fintype.card {u : A // p • u = 0} := by
        simpa only [Fintype.card_subtype] using hA.symm
      _ ≤ Fintype.card H := Fintype.card_le_of_injective φ hi
      _ = p ^ s := by rw [← Nat.card_eq_fintype_card, hcard]
  by_contra hs
  have hs0 : s = 0 := by omega
  simp only [hs0, pow_zero] at hle
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  omega

open scoped Classical in
/-- The index of the `p`-primary part of a finite abelian group is prime to `p`.
Used by `IsFourierIntegral`'s residue-moment reduction. -/
theorem primaryComponent_index_coprime {A : Type*} [AddCommGroup A]
    [Finite A] {p : ℕ} [Fact p.Prime] :
    Nat.Coprime p (AddCommGroup.primaryComponent A p).index := by
  let H := AddCommGroup.primaryComponent A p
  apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
  intro hdiv
  have hdiv' : p ∣ Nat.card (A ⧸ H) := by simpa only [← H.index_eq_card] using hdiv
  obtain ⟨q, hq⟩ := exists_prime_addOrderOf_dvd_card' p hdiv'
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
  have hpy : p • y ∈ H := by
    apply (QuotientAddGroup.eq_zero_iff (x := p • y)).mp
    rw [QuotientAddGroup.mk_nsmul, ← hq]
    exact addOrderOf_nsmul_eq_zero _
  obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp hpy
  have hy : p ^ (k + 1) • y = 0 := by
    simpa only [pow_succ, mul_smul] using hk
  have hmem : y ∈ H := AddCommGroup.mem_primaryComponent.mpr ⟨k + 1, hy⟩
  have hzero : (QuotientAddGroup.mk y : A ⧸ H) = 0 :=
    (QuotientAddGroup.eq_zero_iff (x := y)).mpr hmem
  have hqone : addOrderOf (QuotientAddGroup.mk y : A ⧸ H) = 1 := by simp [hzero]
  have hpone : p = 1 := hq.symm.trans hqone
  exact (Fact.out : p.Prime).ne_one hpone

open scoped Classical in
/-- Reindex a sum on `c + H` by the subgroup `H`. Used by
`MetricGroup.coset_fourier_identity`. -/
private theorem sum_filter_coset {A : Type*} [AddCommGroup A] [Fintype A]
    (H : AddSubgroup A) (c : A) {R : Type*} [AddCommMonoid R] (F : A → R) :
    (∑ x : A with x - c ∈ H, F x) = ∑ h : H, F (c + h) := by
  classical
  let e : H ≃ {x : A // x - c ∈ H} := {
    toFun := fun h => ⟨c + h, by simpa only [add_sub_cancel_left] using h.property⟩
    invFun := fun x => ⟨x.1 - c, x.property⟩
    left_inv := by intro h; apply Subtype.ext; simp
    right_inv := by intro x; apply Subtype.ext; simp }
  have hs : (∑ x : A with x - c ∈ H, F x) =
      ∑ x : {x : A // x - c ∈ H}, F x.1 := by
    simpa using (Finset.sum_subtype_eq_sum_filter (s := Finset.univ)
      (p := fun x : A => x - c ∈ H) (f := F)).symm
  rw [hs]
  exact (Fintype.sum_equiv e (fun h : H => F (c + h))
    (fun x : {x : A // x - c ∈ H} => F x.1) (by intro h; rfl)).symm

/-! ### Coordinates for `p`-torsion

The standard embedding `u ↦ p^(s-1)u` identifies `ZMod p` with the `p`-torsion of
`ZMod (p^s)` when `s ≥ 1`. -/

/-- The standard embedding of `ZMod p` into the `p`-torsion of `ZMod (p^s)`.
Used by both Lemma 1 conclusions. -/
def zmodTorsionCoord {p s : ℕ} (u : ZMod p) : ZMod (p ^ s) :=
  ((p ^ (s - 1) * u.val : ℕ) : ZMod (p ^ s))

/-- `p` kills the standard torsion coordinate. Used by `torsionCoordEquiv`. -/
theorem zmodTorsionCoord_nsmul {p s : ℕ} [Fact p.Prime] (hs : 1 ≤ s)
    (u : ZMod p) : p • zmodTorsionCoord (s := s) u = 0 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
  change p • ((p ^ (t + 1 - 1) * u.val : ℕ) : ZMod (p ^ (t + 1))) = 0
  simp only [nsmul_eq_mul, ← Nat.cast_mul]
  apply (ZMod.natCast_eq_zero_iff _ _).mpr
  refine ⟨u.val, ?_⟩
  simp [pow_succ', mul_assoc]

/-- The standard torsion coordinate is injective. Used by `torsionCoordEquiv`. -/
theorem zmodTorsionCoord_injective {p s : ℕ} [Fact p.Prime] (hs : 1 ≤ s) :
    Function.Injective (zmodTorsionCoord (p := p) (s := s)) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
  intro u w huw
  have hu : p ^ t * u.val < p ^ (t + 1) := by
    calc
      p ^ t * u.val < p ^ t * p :=
        Nat.mul_lt_mul_of_pos_left u.val_lt (pow_pos (Fact.out : p.Prime).pos t)
      _ = p ^ (t + 1) := (pow_succ p t).symm
  have hw : p ^ t * w.val < p ^ (t + 1) := by
    calc
      p ^ t * w.val < p ^ t * p :=
        Nat.mul_lt_mul_of_pos_left w.val_lt (pow_pos (Fact.out : p.Prime).pos t)
      _ = p ^ (t + 1) := (pow_succ p t).symm
  have hval := congrArg ZMod.val huw
  have ht : t.succ - 1 = t := by omega
  simp only [zmodTorsionCoord, ht, ZMod.val_natCast,
    Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hw] at hval
  apply ZMod.val_injective p
  exact Nat.eq_of_mul_eq_mul_left (pow_pos (Fact.out : p.Prime).pos t) hval

/-! ### General helpers for two-coordinate models

The primary model and the torsion-coordinate change use only finite abelian groups.
The moment change is the binomial expansion of two linear forms in characteristic `p`. -/

/-- Decompose a vector over `ZMod n` in its standard basis. Used by `pairing_coordinates` and
`addEquiv_two_coord_cast`. -/
theorem pi_nat_decompose {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    [NeZero n] (x : ι → ZMod n) :
    x = ∑ i, (x i).val • Pi.single i (1 : ZMod n) := by
  ext i
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
  simp

/-- Every point killed by `p` in `ZMod (p^s)` has a standard torsion coordinate. Used by
`torsionModelEquiv`. -/
private theorem zmodTorsionCoord_surjective {p s : ℕ} [Fact p.Prime] (hs : 1 ≤ s)
    (x : ZMod (p ^ s)) (hx : p • x = 0) :
    ∃ u : ZMod p, ((p ^ (s - 1) * u.val : ℕ) : ZMod (p ^ s)) = x := by
  let q := p ^ (s - 1)
  have hq : 0 < q := pow_pos (Fact.out : p.Prime).pos _
  have hn : p ^ s = p * q := by
    have h : s - 1 + 1 = s := by omega
    calc
      p ^ s = p ^ (s - 1 + 1) := by rw [h]
      _ = q * p := pow_succ _ _
      _ = p * q := mul_comm _ _
  have hdiv : p ^ s ∣ p * x.val := by
    have hxcast : ((p * x.val : ℕ) : ZMod (p ^ s)) = 0 := by
      simpa only [nsmul_eq_mul, Nat.cast_mul, ZMod.natCast_zmod_val] using hx
    exact (ZMod.natCast_eq_zero_iff _ _).mp hxcast
  have hqdiv : q ∣ x.val := by
    apply (Nat.mul_dvd_mul_iff_left (Fact.out : p.Prime).pos).mp
    rw [← hn]
    exact hdiv
  have hlt : x.val / q < p := by
    apply (Nat.div_lt_iff_lt_mul hq).mpr
    rw [← hn]
    exact x.val_lt
  let u : ZMod p := (x.val / q : ℕ)
  refine ⟨u, ?_⟩
  have hu : u.val = x.val / q := by simp [u, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
  apply ZMod.val_injective (p ^ s)
  rw [hu, ZMod.val_natCast, Nat.mul_div_cancel' hqdiv]
  exact Nat.mod_eq_of_lt x.val_lt

/-- The additive standard torsion coordinate map. Used by `torsionModelEquiv`. -/
def torsionHom {p s : ℕ} [Fact p.Prime] (hs : 1 ≤ s) :
    ZMod p →+ ZMod (p ^ s) := by
  let q := p ^ (s - 1)
  have hn : q * p = p ^ s := by
    have h : s - 1 + 1 = s := by omega
    rw [← h, pow_succ]
  let F : ℤ →+ ZMod (p ^ s) :=
    (nsmulAddMonoidHom (α := ZMod (p ^ s)) q).comp (Int.castAddHom _)
  have hF : F (p : ℤ) = 0 := by
    simp only [F, AddMonoidHom.coe_comp, Function.comp_apply, nsmulAddMonoidHom_apply]
    simp [Int.castAddHom, nsmul_eq_mul, ← Nat.cast_mul, hn]
  exact ZMod.lift p ⟨F, hF⟩

/-- Evaluation of the additive standard torsion coordinate map. -/
theorem torsionHom_apply {p s : ℕ} [Fact p.Prime] (hs : 1 ≤ s)
    (u : ZMod p) : torsionHom hs u = ((p ^ (s - 1) * u.val : ℕ) : ZMod (p ^ s)) := by
  have hp : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  conv_lhs => rw [← ZMod.natCast_zmod_val u]
  have hcast : ((u.val : ℕ) : ZMod p) = ((u.val : ℤ) : ZMod p) := by norm_cast
  unfold torsionHom
  rw [hcast, ZMod.lift_coe]
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, nsmulAddMonoidHom_apply]
  dsimp [Int.castAddHom]
  simp only [Int.cast_natCast, nsmul_eq_mul, Nat.cast_mul]

/-- The additive standard torsion coordinate map is injective. Used by `torsionModelEquiv`. -/
private theorem torsionHom_injective {p s : ℕ} [Fact p.Prime] (hs : 1 ≤ s) :
    Function.Injective (torsionHom (p := p) hs) := by
  intro u w h
  apply zmodTorsionCoord_injective hs
  simpa only [torsionHom_apply, zmodTorsionCoord] using h

/-- An injective model whose image contains all `p`-power torsion identifies the model with the
primary component. Used by Lemma 1(iii). -/
noncomputable def primaryModelEquiv {G : Type*} [AddCommGroup G] [Fintype G]
    {p s : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
    (e : (ι → ZMod (p ^ s)) →+ G) (he : Function.Injective e)
    (hH : ∀ (x : G) (n : ℕ), p ^ n • x = 0 → x ∈ Set.range e) :
    (ι → ZMod (p ^ s)) ≃+ AddCommGroup.primaryComponent G p := by
  classical
  let H := AddCommGroup.primaryComponent G p
  let E : (ι → ZMod (p ^ s)) →+ H := e.codRestrict H (by
    intro x
    apply AddCommGroup.mem_primaryComponent.mpr
    refine ⟨s, ?_⟩
    have hz : p ^ s • x = 0 := by
      ext i
      simp [nsmul_eq_mul]
    rw [← map_nsmul e, hz, map_zero])
  apply AddEquiv.ofBijective E
  constructor
  · intro x y h
    apply he
    exact congrArg Subtype.val h
  · intro y
    obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp y.property
    obtain ⟨x, hx⟩ := hH y.1 k hk
    exact ⟨x, Subtype.ext hx⟩

/-- The primary component modeled on `(ZMod (p^s))^ι` has order `p^(s |ι|)`. Used by Lemma
1(iii). -/
theorem primaryModelEquiv_card {G : Type*} [AddCommGroup G]
    {p s : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
    (E : (ι → ZMod (p ^ s)) ≃+ AddCommGroup.primaryComponent G p) :
    Nat.card (AddCommGroup.primaryComponent G p) = p ^ (s * Fintype.card ι) := by
  classical
  rw [Nat.card_congr E.symm.toEquiv]
  simp [Nat.card_eq_fintype_card, ZMod.card, pow_mul]

/-- A one-coordinate function space is additively equivalent to its value at `()`. Used by
the cyclic specialization of the shared model estimate. -/
def unitModelEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) : (Unit → A) ≃+ B where
  toFun x := e (x ())
  invFun h _ := e.symm h
  left_inv x := by funext i; cases i; simp
  right_inv h := by simp
  map_add' x y := by simp

open scoped Classical in
/-- The coordinate homomorphism from `(ZMod p)²` into `G[p]`, used by
`torsionModelEquiv`. -/
private def torsionModelHom {G : Type*} [AddCommGroup G] [Fintype G]
    {p s : ℕ} [Fact p.Prime] (hs : 1 ≤ s)
    (E : (Fin 2 → ZMod (p ^ s)) ≃+ AddCommGroup.primaryComponent G p) :
    (Fin 2 → ZMod p) →+ (nsmulAddMonoidHom (α := G) p).ker := {
  toFun u := ⟨(E (fun i => torsionHom hs (u i)) : G), by
    have hz : p • (fun i : Fin 2 => torsionHom hs (u i)) = 0 := by
      ext i
      change p • torsionHom hs (u i) = 0
      rw [← map_nsmul (torsionHom hs)]
      simp [nsmul_eq_mul]
    have he : p • (E (fun i => torsionHom hs (u i)) : G) = 0 := by
      have hh := congrArg Subtype.val (congrArg E hz)
      simpa only [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero, map_nsmul, map_zero]
        using hh
    exact he⟩
  map_zero' := by
    apply Subtype.ext
    have hz : (fun i : Fin 2 => torsionHom hs (0 : ZMod p)) = 0 := by
      funext i
      simp
    change (E (fun i : Fin 2 => torsionHom hs (0 : ZMod p)) : G) = 0
    rw [hz, map_zero]
    rfl
  map_add' := by
    intro u w
    apply Subtype.ext
    have hadd : (fun i => torsionHom hs (u i + w i)) =
        (fun i => torsionHom hs (u i)) + (fun i => torsionHom hs (w i)) := by
      funext i
      simp
    change (E (fun i => torsionHom hs (u i + w i)) : G) =
      (E (fun i => torsionHom hs (u i)) : G) +
        (E (fun i => torsionHom hs (w i)) : G)
    rw [hadd, map_add]
    rfl }

/-- Injectivity of the coordinate homomorphism, used by `torsionModelEquiv`. -/
private theorem torsionModelHom_injective {G : Type*} [AddCommGroup G] [Fintype G]
    {p s : ℕ} [Fact p.Prime] (hs : 1 ≤ s)
    (E : (Fin 2 → ZMod (p ^ s)) ≃+ AddCommGroup.primaryComponent G p) :
    Function.Injective (torsionModelHom hs E) := by
  intro u w huw
  have hG := congrArg Subtype.val huw
  change (E (fun i => torsionHom hs (u i)) : G) =
    (E (fun i => torsionHom hs (w i)) : G) at hG
  have hE : E (fun i => torsionHom hs (u i)) =
      E (fun i => torsionHom hs (w i)) := Subtype.ext hG
  have hh := E.injective hE
  funext i
  exact torsionHom_injective hs (congrFun hh i)

/-- Surjectivity onto `G[p]` of the coordinate homomorphism, used by
`torsionModelEquiv`. -/
private theorem torsionModelHom_surjective {G : Type*} [AddCommGroup G] [Fintype G]
    {p s : ℕ} [Fact p.Prime] (hs : 1 ≤ s)
    (E : (Fin 2 → ZMod (p ^ s)) ≃+ AddCommGroup.primaryComponent G p) :
    Function.Surjective (torsionModelHom hs E) := by
  intro t
  have ht : p • (t : G) = 0 := t.property
  let h : AddCommGroup.primaryComponent G p :=
    ⟨t.1, AddCommGroup.mem_primaryComponent.mpr ⟨1, by simpa using ht⟩⟩
  let x := E.symm h
  have hx : p • x = 0 := by
    apply E.injective
    have hh : p • h = 0 := Subtype.ext ht
    simpa only [map_nsmul, map_zero, E.apply_symm_apply, x] using hh
  have hxi (i : Fin 2) : p • x i = 0 := congrFun hx i
  let u : Fin 2 → ZMod p := fun i => Classical.choose
    (zmodTorsionCoord_surjective hs (x i) (hxi i))
  have hu (i : Fin 2) : torsionHom hs (u i) = x i := by
    rw [torsionHom_apply]
    exact Classical.choose_spec (zmodTorsionCoord_surjective hs (x i) (hxi i))
  refine ⟨u, ?_⟩
  apply Subtype.ext
  have he : (fun i => torsionHom hs (u i)) = x := by funext i; exact hu i
  change (E (fun i => torsionHom hs (u i)) : G) = t.1
  rw [he, E.apply_symm_apply]

/-- Standard coordinates identify `(ZMod p)²` with `G[p]`. Used by Lemma 1(iii). -/
noncomputable def torsionModelEquiv {G : Type*} [AddCommGroup G] [Fintype G]
    {p s : ℕ} [Fact p.Prime] (hs : 1 ≤ s)
    (E : (Fin 2 → ZMod (p ^ s)) ≃+ AddCommGroup.primaryComponent G p) :
    (Fin 2 → ZMod p) ≃+ (nsmulAddMonoidHom (α := G) p).ker :=
  AddEquiv.ofBijective (torsionModelHom hs E)
    ⟨torsionModelHom_injective hs E, torsionModelHom_surjective hs E⟩

/-- Evaluation of standard coordinates on `G[p]`. -/
theorem torsionModelEquiv_apply {G : Type*} [AddCommGroup G] [Fintype G]
    {p s : ℕ} [Fact p.Prime] (hs : 1 ≤ s)
    (E : (Fin 2 → ZMod (p ^ s)) ≃+ AddCommGroup.primaryComponent G p)
    (u : Fin 2 → ZMod p) :
    ((torsionModelEquiv hs E u : (nsmulAddMonoidHom (α := G) p).ker) : G) =
      (E (fun i => torsionHom hs (u i)) : G) := rfl

namespace MetricGroup

variable (M : MetricGroup G L) (v : Valuation L ℝ≥0)

/-- The pairing is nondegenerate on the `p`-primary part when its order is `p^s`.
Used by `IsFourierIntegral`'s cyclic-coordinate reduction. -/
theorem primary_bichar_nondegenerate {p s : ℕ} [Fact p.Prime]
    (hcard : Nat.card (AddCommGroup.primaryComponent G p) = p ^ s)
    {x : G} (hx : x ∈ AddCommGroup.primaryComponent G p)
    (horth : ∀ h ∈ AddCommGroup.primaryComponent G p, M.bichar x h = 1) : x = 0 := by
  classical
  let H := AddCommGroup.primaryComponent G p
  let m := H.index
  have hcop : (p ^ s).Coprime m :=
    (primaryComponent_index_coprime (A := G) (p := p)).pow_left s
  have hnx : p ^ s • x = 0 := by
    let xx : H := ⟨x, hx⟩
    have hh : Fintype.card H • xx = 0 := card_nsmul_eq_zero
    have hh' := congrArg Subtype.val hh
    change Fintype.card H • x = 0 at hh'
    rw [← Nat.card_eq_fintype_card, hcard] at hh'
    exact hh'
  apply M.nondegenerate x
  intro y
  have hmy : m • y ∈ H := by
    apply AddCommGroup.mem_primaryComponent.mpr
    refine ⟨s, ?_⟩
    calc
      p ^ s • (m • y) = (p ^ s * m) • y := (mul_smul ..).symm
      _ = Nat.card G • y := by rw [← hcard, H.card_mul_index]
      _ = 0 := by simpa only [Nat.card_eq_fintype_card] using
        (card_nsmul_eq_zero : Fintype.card G • y = 0)
  have hn : M.bichar x y ^ p ^ s = 1 := by
    rw [← M.bichar_nsmul_left, hnx, M.bichar_zero_left]
  have hm : M.bichar x y ^ m = 1 := by
    rw [← M.bichar_nsmul_right, horth (m • y) hmy]
  have ho : orderOf (M.bichar x y) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hn)
      (orderOf_dvd_of_pow_eq_one hm)
  exact orderOf_eq_one_iff.mp ho

/-- A cyclic coordinate generator `g` has primitive self-pairing `⟨g;g⟩`.
Used by `IsFourierIntegral`'s cyclic-coordinate reduction. -/
theorem primary_bichar_primitive {p s : ℕ} [Fact p.Prime]
    (hcard : Nat.card (AddCommGroup.primaryComponent G p) = p ^ s)
    (e : ZMod (p ^ s) ≃+ AddCommGroup.primaryComponent G p) :
    IsPrimitiveRoot (M.bichar (e 1 : G) (e 1 : G)) (p ^ s) := by
  classical
  let H := AddCommGroup.primaryComponent G p
  let n := p ^ s
  let g : G := (e 1 : H)
  let ζ : L := M.bichar g g
  have hn : n ≠ 0 := pow_ne_zero s (Fact.out : p.Prime).ne_zero
  let _ : NeZero n := ⟨hn⟩
  have hg : n • g = 0 := by
    have hh : Fintype.card H • (e 1) = 0 := card_nsmul_eq_zero
    have hh' := congrArg Subtype.val hh
    change Fintype.card H • g = 0 at hh'
    rw [← Nat.card_eq_fintype_card, hcard] at hh'
    exact hh'
  have hζn : ζ ^ n = 1 := by
    rw [← M.bichar_nsmul_left, hg, M.bichar_zero_left]
  have hcoord (a : ZMod n) : e a = a.val • e 1 := by
    conv_lhs => rw [← ZMod.natCast_zmod_val a]
    rw [← nsmul_one, map_nsmul]
  let d := orderOf ζ
  have hζd : ζ ^ d = 1 := pow_orderOf_eq_one ζ
  have hdg : d • g = 0 := by
    have hx : d • g ∈ H := by
      change d • (e 1 : G) ∈ H
      exact H.nsmul_mem (e 1).property _
    apply M.primary_bichar_nondegenerate hcard hx
    intro h hh
    obtain ⟨a, ha⟩ := e.surjective ⟨h, hh⟩
    have hh' : h = a.val • g := by
      change h = a.val • (e 1 : G)
      exact congrArg Subtype.val (ha.symm.trans (hcoord a))
    rw [hh', M.bichar_nsmul_left, M.bichar_nsmul_right, ← pow_mul,
      mul_comm a.val d, pow_mul, show M.bichar g g = ζ from rfl, hζd, one_pow]
  have hdn : n ∣ d := by
    have hde : d • (1 : ZMod n) = 0 := by
      apply e.injective
      rw [map_nsmul, map_zero]
      exact Subtype.ext hdg
    have hcast : (d : ZMod n) = 0 := by simpa only [nsmul_one] using hde
    exact (ZMod.natCast_eq_zero_iff d n).mp hcast
  have hnd : d ∣ n := orderOf_dvd_of_pow_eq_one hζn
  exact IsPrimitiveRoot.iff_orderOf.mpr (dvd_antisymm hnd hdn)

/-- The bicharacter in cyclic coordinates is the usual Fourier kernel.
Used by `IsFourierIntegral`'s model reduction. -/
theorem primary_bichar_coordinates {p s : ℕ} [Fact p.Prime]
    (e : ZMod (p ^ s) ≃+ AddCommGroup.primaryComponent G p)
    (a x : ZMod (p ^ s)) :
    M.bichar (e x : G) (e a : G) =
      M.bichar (e 1 : G) (e 1 : G) ^ (a.val * x.val) := by
  have hn : p ^ s ≠ 0 := pow_ne_zero s (Fact.out : p.Prime).ne_zero
  let _ : NeZero (p ^ s) := ⟨hn⟩
  have hcoord (t : ZMod (p ^ s)) : e t = t.val • e 1 := by
    conv_lhs => rw [← ZMod.natCast_zmod_val t]
    rw [← nsmul_one, map_nsmul]
  have hx : (e x : G) = x.val • (e 1 : G) := congrArg Subtype.val (hcoord x)
  have ha : (e a : G) = a.val • (e 1 : G) := congrArg Subtype.val (hcoord a)
  rw [hx, ha, M.bichar_nsmul_left, M.bichar_nsmul_right, ← pow_mul]

/-! ### Pairing coordinates for a two-generator primary component

Nondegeneracy gives a primitive root and all Fourier frequencies in the standard model. -/

/-- The first coordinate basis vector has nonzero multiple by `p^(s-1)`;
used by `exists_primary_root`. -/
private theorem primary_basis_nsmul_ne_zero {G : Type*} [AddCommGroup G]
    {p s : ℕ} [Fact p.Prime] (hs : 1 ≤ s)
    (E : (Fin 2 → ZMod (p ^ s)) ≃+ AddCommGroup.primaryComponent G p) :
    p ^ (s - 1) • ((E (Pi.single 0 1) : AddCommGroup.primaryComponent G p) : G) ≠ 0 := by
  let H := AddCommGroup.primaryComponent G p
  let b0 : Fin 2 → ZMod (p ^ s) := Pi.single 0 1
  let g : G := E b0
  have hq : p ^ (s - 1) < p ^ s := by
    have h : s - 1 + 1 = s := by omega
    calc
      p ^ (s - 1) < p ^ (s - 1) * p := by
        simpa only [mul_one] using Nat.mul_lt_mul_of_pos_left
          (Fact.out : p.Prime).one_lt (pow_pos (Fact.out : p.Prime).pos _)
      _ = p ^ (s - 1 + 1) := (pow_succ _ _).symm
      _ = p ^ s := congrArg (p ^ ·) h
  have hx : p ^ (s - 1) • g ≠ 0 := by
    intro hz
    have hzE : p ^ (s - 1) • E b0 = (0 : H) := by
      apply Subtype.ext
      exact hz
    have heq : p ^ (s - 1) • b0 = 0 := by
      apply E.injective
      simpa only [map_nsmul, map_zero] using hzE
    have hcoord := congrFun heq (0 : Fin 2)
    have hzero : ((p ^ (s - 1) : ℕ) : ZMod (p ^ s)) = 0 := by
      simpa [b0, Pi.single_apply, nsmul_eq_mul] using hcoord
    have hdiv := (ZMod.natCast_eq_zero_iff (p ^ (s - 1)) (p ^ s)).mp hzero
    have hle := Nat.le_of_dvd (pow_pos (Fact.out : p.Prime).pos _) hdiv
    omega
  exact hx

/-- Nondegeneracy on a primary component containing `(ZMod (p^s))^2` supplies a primitive
`p^s`-th root of unity. Used by Lemma 1(iii). -/
theorem exists_primary_root {G L : Type*} [AddCommGroup G] [Fintype G] [Field L]
    {p s : ℕ} [Fact p.Prime] (hs : 1 ≤ s) (M : MetricGroup G L)
    (E : (Fin 2 → ZMod (p ^ s)) ≃+ AddCommGroup.primaryComponent G p)
    (hnondeg : ∀ x : G, x ∈ AddCommGroup.primaryComponent G p →
      (∀ h ∈ AddCommGroup.primaryComponent G p, M.bichar x h = 1) → x = 0) :
    ∃ ζ : L, IsPrimitiveRoot ζ (p ^ s) := by
  classical
  let H := AddCommGroup.primaryComponent G p
  let b0 : Fin 2 → ZMod (p ^ s) := Pi.single 0 1
  let g : G := E b0
  have hx : p ^ (s - 1) • g ≠ 0 := primary_basis_nsmul_ne_zero hs E
  have hmem : p ^ (s - 1) • g ∈ H := H.nsmul_mem (E b0).property _
  obtain ⟨y, hy⟩ : ∃ y : H, M.bichar (p ^ (s - 1) • g) y ≠ 1 := by
    by_contra hh
    push Not at hh
    exact hx (hnondeg _ hmem (fun z hz => hh ⟨z, hz⟩))
  let ζ := M.bichar g y
  have hζq : ζ ^ p ^ (s - 1) ≠ 1 := by
    simpa only [ζ, M.bichar_nsmul_left] using hy
  have hng : p ^ s • g = 0 := by
    have hzero : p ^ s • b0 = 0 := by ext i; simp [nsmul_eq_mul]
    have hh := congrArg Subtype.val (congrArg E hzero)
    simpa only [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero, map_nsmul, map_zero, g]
      using hh
  have hζn : ζ ^ (p ^ s) = 1 := by
    rw [← M.bichar_nsmul_left, hng, M.bichar_zero_left]
  have hnot : ¬orderOf ζ ∣ p ^ (s - 1) := by
    intro hd
    exact hζq ((orderOf_dvd_iff_pow_eq_one).mp hd)
  have hdiv : orderOf ζ ∣ p ^ s := orderOf_dvd_of_pow_eq_one hζn
  have hpow : s - 1 + 1 = s := by omega
  have horder : orderOf ζ = p ^ s := by
    have hh := Nat.eq_prime_pow_of_dvd_least_prime_pow (Fact.out : p.Prime) hnot
      (by simpa only [hpow] using hdiv)
    simpa only [hpow] using hh
  exact ⟨ζ, IsPrimitiveRoot.iff_orderOf.mpr horder⟩

/-- The pairing with a fixed frequency is the standard Fourier kernel once its values on the
coordinate basis are known. Used by `exists_pairing_frequency`. -/
private theorem pairing_coordinates {G L : Type*} [AddCommGroup G] [Fintype G] [Field L]
    {p s : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : MetricGroup G L)
    (E : (ι → ZMod (p ^ s)) ≃+ AddCommGroup.primaryComponent G p)
    (ζ : L) (a : ι → ZMod (p ^ s)) (y : AddCommGroup.primaryComponent G p)
    (hbasis : ∀ i, M.bichar (E (Pi.single i 1) : G) y = ζ ^ (a i).val)
    (x : ι → ZMod (p ^ s)) :
    M.bichar (E x : G) y = ζ ^ (∑ i, (a i).val * (x i).val) := by
  have hn : p ^ s ≠ 0 := pow_ne_zero s (Fact.out : p.Prime).ne_zero
  let _ : NeZero (p ^ s) := ⟨hn⟩
  have hx : (E x : G) = ∑ i, (x i).val • (E (Pi.single i 1) : G) := by
    conv_lhs => rw [pi_nat_decompose x]
    simp only [map_sum, map_nsmul]
    change (AddSubgroup.subtype (AddCommGroup.primaryComponent G p))
      (∑ i, (x i).val • E (Pi.single i 1)) = _
    rw [map_sum]
    simp only [map_nsmul, AddSubgroup.subtype_apply]
  have hsum (t : Finset ι) :
      M.bichar (∑ i ∈ t, (x i).val • (E (Pi.single i 1) : G)) y =
        ∏ i ∈ t, M.bichar (E (Pi.single i 1) : G) y ^ (x i).val := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert i t hi ih =>
      simp only [Finset.sum_insert hi, Finset.prod_insert hi]
      rw [M.bichar_add_left, M.bichar_nsmul_left, ih]
  rw [hx, hsum Finset.univ]
  simp_rw [hbasis, ← pow_mul]
  exact Finset.prod_pow_eq_pow_sum Finset.univ (fun i => (a i).val * (x i).val) ζ

/-- The pairing-coordinate map is injective by nondegeneracy;
used by `exists_pairing_frequency`. -/
private theorem pairing_frequency_injective {G L : Type*} [AddCommGroup G] [Fintype G]
    [Field L] {p s : ℕ} [Fact p.Prime] {ι : Type*} [Finite ι] [DecidableEq ι]
    (M : MetricGroup G L)
    (E : (ι → ZMod (p ^ s)) ≃+ AddCommGroup.primaryComponent G p)
    (ζ : L) (D : AddCommGroup.primaryComponent G p → (ι → ZMod (p ^ s)))
    (hD : ∀ y i, ζ ^ (D y i).val = M.bichar (E (Pi.single i 1) : G) y)
    (hnondeg : ∀ x : G, x ∈ AddCommGroup.primaryComponent G p →
      (∀ h ∈ AddCommGroup.primaryComponent G p, M.bichar x h = 1) → x = 0) :
    Function.Injective D := by
  let : Fintype ι := Fintype.ofFinite ι
  let H := AddCommGroup.primaryComponent G p
  intro y z hyz
  have heq (x : ι → ZMod (p ^ s)) :
      M.bichar (E x : G) y = M.bichar (E x : G) z := by
    rw [pairing_coordinates M E ζ (D y) y (fun i => (hD y i).symm) x,
      pairing_coordinates M E ζ (D z) z (fun i => (hD z i).symm) x, hyz]
  have hzero : ((y - z : H) : G) = 0 := by
    apply hnondeg
    · exact (y - z).property
    · intro h hh
      obtain ⟨x, hx⟩ := E.surjective ⟨h, hh⟩
      have hxh : (E x : G) = h := congrArg Subtype.val hx
      rw [← hxh]
      change M.bichar ((y : G) - (z : G)) (E x : G) = 1
      rw [sub_eq_add_neg, M.bichar_add_left, M.bichar_neg_left,
        M.bichar_comm (y : G), M.bichar_comm (z : G), heq x]
      exact mul_inv_cancel₀ (M.bichar_ne_zero (E x : G) z)
  exact sub_eq_zero.mp (Subtype.ext hzero)

/-- Every standard Fourier frequency on the primary model is represented by the bicharacter.
Used by Lemma 1(iii). -/
theorem exists_pairing_frequency {G L : Type*} [AddCommGroup G] [Fintype G] [Field L]
    {p s : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
    (M : MetricGroup G L)
    (E : (ι → ZMod (p ^ s)) ≃+ AddCommGroup.primaryComponent G p)
    (ζ : L) (hζ : IsPrimitiveRoot ζ (p ^ s))
    (hnondeg : ∀ x : G, x ∈ AddCommGroup.primaryComponent G p →
      (∀ h ∈ AddCommGroup.primaryComponent G p, M.bichar x h = 1) → x = 0) :
    ∀ a : ι → ZMod (p ^ s), ∃ y : AddCommGroup.primaryComponent G p,
      ∀ x, M.bichar (E x : G) y = ζ ^ (∑ i, (a i).val * (x i).val) := by
  classical
  let H := AddCommGroup.primaryComponent G p
  have hn : p ^ s ≠ 0 := pow_ne_zero s (Fact.out : p.Prime).ne_zero
  let _ : NeZero (p ^ s) := ⟨hn⟩
  have hroot (y : H) (i : ι) : M.bichar (E (Pi.single i 1) : G) y ^ (p ^ s) = 1 := by
    rw [← M.bichar_nsmul_left]
    have hz : p ^ s • (Pi.single i (1 : ZMod (p ^ s)) : ι → ZMod (p ^ s)) = 0 := by
      ext j
      simp [nsmul_eq_mul]
    have he : p ^ s • (E (Pi.single i 1) : G) = 0 := by
      have hh := congrArg Subtype.val (congrArg E hz)
      simpa only [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero, map_nsmul, map_zero] using hh
    rw [he, M.bichar_zero_left]
  let D : H → (ι → ZMod (p ^ s)) := fun y i =>
    ((hζ.eq_pow_of_pow_eq_one (hroot y i)).choose : ZMod (p ^ s))
  have hD (y : H) (i : ι) : ζ ^ (D y i).val = M.bichar (E (Pi.single i 1) : G) y := by
    dsimp only [D]
    obtain ⟨hlt, heq⟩ := (hζ.eq_pow_of_pow_eq_one (hroot y i)).choose_spec
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hlt] using heq
  have hDi : Function.Injective D :=
    pairing_frequency_injective M E ζ D hD hnondeg
  have hcard : Fintype.card H = Fintype.card (ι → ZMod (p ^ s)) :=
    Fintype.card_congr E.symm.toEquiv
  have hDs : Function.Surjective D :=
    ((Fintype.bijective_iff_injective_and_card D).mpr ⟨hDi, hcard⟩).2
  intro a
  obtain ⟨y, hy⟩ := hDs a
  refine ⟨y, ?_⟩
  intro x
  simpa only [hy] using pairing_coordinates M E ζ (D y) y (fun i => (hD y i).symm) x

/-! ### Orthogonality for the primary component

The annihilator sum isolates a coset of the primary component in the global Fourier transform. -/

/-- The bicharacter factorization in the coset Fourier identity. -/
private theorem bichar_coset_kernel (c x a u : G) :
    M.bichar c u * M.bichar x (-(a + u)) =
      M.bichar x (-a) * M.bichar (c - x) u := by
  rw [neg_add, M.bichar_add_right, sub_eq_add_neg, M.bichar_add_left]
  have h : M.bichar x (-u) = M.bichar (-x) u := by
    rw [M.bichar_neg_right, M.bichar_neg_left]
  rw [h]
  ring

open scoped Classical in
/-- Orthogonality turns the annihilator average into a sum supported on `c + H`.
Used by `coset_fourier_identity`. -/
private theorem coset_fourier_indicator (H : AddSubgroup G) (f : G → L) (c a : G) :
    (Nat.card H : L) * M.sqrtCard *
        (∑ u with u ∈ M.orthogonal H,
          M.bichar c u * M.fourier f (a + u)) =
      ∑ x : G, f x * M.bichar x (-a) *
        (if c - x ∈ H then (Fintype.card G : L) else 0) := by
  classical
  have hscaled (u : G) :
      M.sqrtCard * (M.bichar c u * M.fourier f (a + u)) =
        ∑ x : G, f x * (M.bichar c u * M.bichar x (-(a + u))) := by
    simp only [fourier, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    field_simp [M.sqrtCard_ne_zero]
  calc
    _ = (Nat.card H : L) *
        ∑ u with u ∈ M.orthogonal H,
          ∑ x : G, f x * (M.bichar c u * M.bichar x (-(a + u))) := by
        rw [mul_assoc, Finset.mul_sum]
        simp_rw [hscaled]
    _ = ∑ x : G, f x * M.bichar x (-a) *
        ((Nat.card H : L) *
          ∑ u with u ∈ M.orthogonal H, M.bichar (c - x) u) := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro u _
        rw [M.bichar_coset_kernel]
        ring
    _ = ∑ x : G, f x * M.bichar x (-a) *
        (if c - x ∈ H then (Fintype.card G : L) else 0) := by
        simp_rw [M.card_mul_sum_orthogonal_bichar H]

open scoped Classical in
/-- The unnormalized Fourier sum on `c + H` is the annihilator average of the
global normalized transform, after clearing `|H|`. -/
theorem coset_fourier_identity (H : AddSubgroup G) (f : G → L) (c a : G) :
    (Nat.card H : L) * M.sqrtCard *
        (∑ u with u ∈ M.orthogonal H,
          M.bichar c u * M.fourier f (a + u)) =
      (Fintype.card G : L) * M.bichar c (-a) *
        (∑ h : H, f (c + h) * M.bichar h (-a)) := by
  classical
  calc
    _ = ∑ x : G, f x * M.bichar x (-a) *
        (if c - x ∈ H then (Fintype.card G : L) else 0) :=
      M.coset_fourier_indicator H f c a
    _ = (Fintype.card G : L) *
        ∑ x : G with x - c ∈ H, f x * M.bichar x (-a) := by
        have hmem (x : G) : c - x ∈ H ↔ x - c ∈ H := by
          rw [← neg_sub x c, H.neg_mem_iff]
        simp only [hmem, mul_ite, mul_zero, Finset.sum_ite, Finset.sum_const_zero, add_zero]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
    _ = (Fintype.card G : L) * M.bichar c (-a) *
        (∑ h : H, f (c + h) * M.bichar h (-a)) := by
        rw [sum_filter_coset H c]
        simp_rw [M.bichar_add_left]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro h _
        ring

open scoped Classical in
/-- Reindex the coset Fourier estimate by any primary model and its pairing frequencies. Used by
Lemma 1(iii). -/
theorem model_fourier_sq_le {G L : Type*} [AddCommGroup G] [Fintype G] [Field L]
    {p s : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : MetricGroup G L) (v : Valuation L ℝ≥0)
    (E : (ι → ZMod (p ^ s)) ≃+ AddCommGroup.primaryComponent G p)
    (ζ : L) (hfreq : ∀ a : ι → ZMod (p ^ s),
      ∃ y : AddCommGroup.primaryComponent G p,
        ∀ x, M.bichar (E x : G) y = ζ ^ (∑ i, (a i).val * (x i).val))
    (f : G → L) (hcoset : ∀ (c a : G),
      v (∑ h : AddCommGroup.primaryComponent G p,
        f (c + h) * M.bichar h (-a)) ^ 2 ≤ v (p : L) ^ (s * Fintype.card ι))
    (c : G) (a : ι → ZMod (p ^ s)) :
    v (∑ x : ι → ZMod (p ^ s), f (c + (E x : G)) *
      ζ ^ (∑ i, (a i).val * (x i).val)) ^ 2 ≤
      v (p : L) ^ (s * Fintype.card ι) := by
  classical
  obtain ⟨y, hy⟩ := hfreq a
  have hsum : (∑ x : ι → ZMod (p ^ s), f (c + (E x : G)) *
      ζ ^ (∑ i, (a i).val * (x i).val)) =
      ∑ h : AddCommGroup.primaryComponent G p,
        f (c + h) * M.bichar h y := by
    apply Fintype.sum_equiv E.toEquiv
    intro x
    change f (c + (E x : G)) * ζ ^ (∑ i, (a i).val * (x i).val) =
      f (c + (E x : G)) * M.bichar (E x : G) y
    rw [hy x]
  rw [hsum]
  simpa only [neg_neg] using hcoset c (-(y : G))


end MetricGroup

end SIC
