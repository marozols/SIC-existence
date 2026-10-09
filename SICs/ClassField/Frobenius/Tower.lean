/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Frobenius.Basic

/-!
# Frobenius elements in towers

Powers and restrictions of Frobenius elements along intermediate fields.

This module follows Milne, *Class Field Theory*, Chapter V, Propositions 1.10 and 1.11, and Chapter
VII, Lemma 6.2. `SICs.ClassField.Frobenius.Basic` owns the Frobenius predicate, its existence,
uniqueness, decomposition-group consequences, and isomorphism transport.

## The argument

Iterating the Frobenius congruence gives the power map at every exponent. At the residue degree
of an intermediate prime it becomes the identity, so a Galois restriction lies in inertia; when
the intermediate prime is unramified, that power fixes the subfield. Conversely, if Frobenius
fixes a subfield, the power-map polynomial bounds its residue field and forces residue degree
one. Restriction preserves the Frobenius congruence. In a prime-exponent tower, a nonidentity
relative Frobenius generates the unramified decomposition group, making its residue degree one
and identifying relative with absolute Frobenius.
-/

noncomputable section

open scoped Pointwise

open NumberField

namespace SIC

universe u v

variable {K : Type u} [Field K] [NumberField K] {H : Type v} [Field H] [NumberField H]
  [Algebra K H]

/-! ### Frobenius powers on subextensions

If `g` is Frobenius at a prime `Q` of `𝒪_H` above an unramified `𝔭`, then `g^f` fixes every
Galois subextension `E`, where `f` is the inertia degree over `𝔭` of the prime `𝔓 = Q ∩ 𝒪_E`:
`g^f(x) ≡ x^{N(𝔭)^f} ≡ x (mod Q)` for `x ∈ 𝒪_E`, since `|𝒪_E/𝔓| = N(𝔭)^f`, so `g^f|_E` lies in
the inertia group of `𝔓`, which is trivial. -/

omit [NumberField H] in
/-- **Powers of Frobenius**: iterating the Frobenius congruence gives
$g^k(x) \equiv x^{N(\mathfrak p)^k} \pmod Q$. Milne, *Class Field Theory*, Chapter V, proof
of 1.10. -/
theorem IsFrobeniusAt.pow_smul_sub_mem {g : H ≃ₐ[K] H} {p : Ideal (𝓞 K)} {Q : Ideal (𝓞 H)}
    (hg : IsFrobeniusAt K H g p Q) (k : ℕ) (x : 𝓞 H) :
    (g ^ k) • x - x ^ (Ideal.absNorm p ^ k) ∈ Q := by
  have hpowCongr {a b : 𝓞 H} (hab : a - b ∈ Q) (n : ℕ) : a ^ n - b ^ n ∈ Q := by
    rw [← Ideal.Quotient.eq]
    simpa only [map_pow] using congrArg (fun z : (𝓞 H) ⧸ Q ↦ z ^ n)
      (Ideal.Quotient.eq.mpr hab)
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', mul_smul, pow_succ]
      have hfirst := hg.sub_mem ((g ^ k) • x)
      have hsecond := hpowCongr ih (Ideal.absNorm p)
      rw [pow_mul]
      change g • (g ^ k) • x - _ ∈ Q at hfirst
      simpa only [sub_add_sub_cancel] using Q.add_mem hfirst hsecond

/-- The cardinality of a prime residue field gives its power-map identity. This supplies the
finite-field step in `IsFrobeniusAt.pow_inertiaDeg_mem_fixingSubgroup`. -/
private lemma pow_absNorm_sub_mem (E : IntermediateField K H) (P : Ideal (𝓞 E))
    [P.IsPrime] (hP0 : P ≠ ⊥) (x : 𝓞 E) : x ^ Ideal.absNorm P - x ∈ P := by
  have : P.IsMaximal := Ideal.isMaximal_of_isPrime_of_ne_bot P hP0
  let _ : Field ((𝓞 E) ⧸ P) := Ideal.Quotient.field P
  have : Finite ((𝓞 E) ⧸ P) := inferInstance
  let _ : Fintype ((𝓞 E) ⧸ P) := Fintype.ofFinite _
  rw [← Ideal.Quotient.eq]
  simpa only [map_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Nat.card_eq_fintype_card] using FiniteField.pow_card (Ideal.Quotient.mk P x)

/-- The iterated Frobenius congruence becomes the identity congruence on a subfield residue
field. This is the congruence used by `IsFrobeniusAt.pow_inertiaDeg_mem_fixingSubgroup`. -/
private lemma frobenius_pow_sub_mem {g : H ≃ₐ[K] H} {p : Ideal (𝓞 K)}
    {Q : Ideal (𝓞 H)} [Q.IsPrime] [Q.LiesOver p]
    (hg : IsFrobeniusAt K H g p Q) (E : IntermediateField K H)
    (hP0 : Q.comap (algebraMap (𝓞 E) (𝓞 H)) ≠ ⊥) (x : 𝓞 E) :
    (g ^ (Q.comap (algebraMap (𝓞 E) (𝓞 H))).inertiaDeg (𝓞 K)) •
        algebraMap (𝓞 E) (𝓞 H) x - algebraMap (𝓞 E) (𝓞 H) x ∈ Q := by
  let P := Q.comap (algebraMap (𝓞 E) (𝓞 H))
  have hnorm : Ideal.absNorm p ^ P.inertiaDeg (𝓞 K) = Ideal.absNorm P :=
    Ideal.absNorm_pow_inertiaDeg p P
  have h₁ := hg.pow_smul_sub_mem (P.inertiaDeg (𝓞 K))
    (algebraMap (𝓞 E) (𝓞 H) x)
  have h₂ : algebraMap (𝓞 E) (𝓞 H) (x ^ Ideal.absNorm P - x) ∈ Q :=
    pow_absNorm_sub_mem E P hP0 x
  rw [map_sub, map_pow, ← hnorm] at h₂
  simpa only [P, sub_add_sub_cancel] using Q.add_mem h₁ h₂

omit [NumberField K] [NumberField H] in
/-- A congruence on integral elements puts the normal restriction in the inertia group. This
restriction step is used by `IsFrobeniusAt.pow_inertiaDeg_mem_fixingSubgroup`. -/
private lemma restrictNormal_mem_inertia (E : IntermediateField K H) [IsGalois K E]
    {Q : Ideal (𝓞 H)} (τ : H ≃ₐ[K] H)
    (hmod : ∀ x : 𝓞 E, τ • algebraMap (𝓞 E) (𝓞 H) x -
      algebraMap (𝓞 E) (𝓞 H) x ∈ Q) :
    τ.restrictNormal E ∈
      (Q.comap (algebraMap (𝓞 E) (𝓞 H))).inertia (E ≃ₐ[K] E) := by
  rw [AddSubgroup.mem_inertia]
  intro x
  change algebraMap (𝓞 E) (𝓞 H) (τ.restrictNormal E • x - x) ∈ Q
  rw [map_sub]
  have heq : algebraMap (𝓞 E) (𝓞 H) (τ.restrictNormal E • x) =
      τ • algebraMap (𝓞 E) (𝓞 H) x := by
    apply RingOfIntegers.ext
    change algebraMap E H (τ.restrictNormal E x) = τ (algebraMap E H x)
    exact AlgEquiv.restrictNormal_commutes τ E x
  rw [heq]
  exact hmod x

/-- **A Frobenius power fixes a Galois subextension**: if `g ∈ Gal(H/K)` is Frobenius at a prime
`Q` of `𝒪_H` above `𝔭`, `E/K` is a Galois subextension, and `𝔓 = Q ∩ 𝒪_E` is unramified over
`𝔭`, then `g^f` fixes `E` pointwise, where `f = f(𝔓|𝔭)`. The restriction of `g^f` to `E` acts
as `x ↦ x^{|𝒪_E/𝔓|}`, that is trivially, on `𝒪_E/𝔓`, so it lies in the inertia group of `𝔓`,
which is trivial; this is the order computation behind [83, Neukirch (1999), Chapter I,
Proposition 9.6 and §9, exercise 2, p. 58] and Milne, *Class Field Theory*, Chapter V, 1.10. -/
theorem IsFrobeniusAt.pow_inertiaDeg_mem_fixingSubgroup
    {g : H ≃ₐ[K] H} {p : Ideal (𝓞 K)} {Q : Ideal (𝓞 H)} (hg : IsFrobeniusAt K H g p Q)
    (E : IntermediateField K H) [IsGalois K E]
    (hunr : (Q.comap (algebraMap (𝓞 E) (𝓞 H))).ramificationIdx (𝓞 K) = 1) :
    g ^ (Q.comap (algebraMap (𝓞 E) (𝓞 H))).inertiaDeg (𝓞 K) ∈ E.fixingSubgroup := by
  have : Q.IsPrime := hg.isPrime
  have : Q.LiesOver p := hg.liesOver
  have hp := hg.ne_bot
  let 𝔓 := Q.comap (algebraMap (𝓞 E) (𝓞 H))
  have hP0 : 𝔓 ≠ ⊥ := by
    intro hP
    apply hp
    rw [Ideal.over_def 𝔓 p, hP]
    exact Ideal.under_bot (𝓞 K) (𝓞 E)
  have hσinertia := restrictNormal_mem_inertia E (g ^ 𝔓.inertiaDeg (𝓞 K))
    (frobenius_pow_sub_mem hg E hP0)
  have hσone : (g ^ 𝔓.inertiaDeg (𝓞 K)).restrictNormal E = 1 := by
    rw [inertia_eq_bot_of_ramificationIdx_eq_one hp 𝔓 hunr] at hσinertia
    exact hσinertia
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).mpr
    ((AlgEquiv.restrictNormal_eq_one_iff E _).mp hσone)

/-- The relative automorphism whose restriction is the residue-degree power of Frobenius is
Frobenius over the intermediate field. Milne, *Class Field Theory*, Chapter V,
Proposition 1.10. -/
theorem IsFrobeniusAt.pow_restrictScalars {g : H ≃ₐ[K] H}
    {p : Ideal (𝓞 K)} {Q : Ideal (𝓞 H)} (hg : IsFrobeniusAt K H g p Q)
    (E : IntermediateField K H) {τ : H ≃ₐ[E] H}
    (hτ : τ.restrictScalars K =
      g ^ (Q.under (𝓞 E)).inertiaDeg (𝓞 K)) :
    IsFrobeniusAt E H τ (Q.under (𝓞 E)) Q := by
  have : Q.IsPrime := hg.isPrime
  have : Q.LiesOver p := hg.liesOver
  refine IsFrobeniusAt.intro inferInstance inferInstance ?_
  intro x
  have hiter := hg.pow_smul_sub_mem ((Q.under (𝓞 E)).inertiaDeg (𝓞 K)) x
  have hnorm := Ideal.absNorm_pow_inertiaDeg p (Q.under (𝓞 E))
  change (τ.restrictScalars K) • x - x ^ Ideal.absNorm (Q.under (𝓞 E)) ∈ Q
  simpa only [hτ, hnorm] using hiter

/-- If the intermediate prime is unramified over the base prime, the residue-degree power of
absolute Frobenius restricts from a relative Frobenius automorphism. Milne,
*Class Field Theory*, Chapter V, Proposition 1.10. -/
theorem IsFrobeniusAt.exists_pow_restrictScalars {g : H ≃ₐ[K] H}
    {p : Ideal (𝓞 K)} {Q : Ideal (𝓞 H)} (hg : IsFrobeniusAt K H g p Q)
    (E : IntermediateField K H) [IsGalois K E]
    (hunr : (Q.under (𝓞 E)).ramificationIdx (𝓞 K) = 1) :
    ∃ τ : H ≃ₐ[E] H,
      τ.restrictScalars K = g ^ (Q.under (𝓞 E)).inertiaDeg (𝓞 K) ∧
      IsFrobeniusAt E H τ (Q.under (𝓞 E)) Q := by
  have hfix := hg.pow_inertiaDeg_mem_fixingSubgroup E hunr
  let τ : H ≃ₐ[E] H := E.fixingSubgroupEquiv ⟨_, hfix⟩
  refine ⟨τ, rfl, ?_⟩
  exact hg.pow_restrictScalars E rfl

omit [NumberField H] in
/-- The Frobenius congruence becomes $x^{N\mathfrak p}\equiv x\pmod{Q\cap\mathcal O_E}$
when Frobenius fixes `E`. This is the congruence used by
`IsFrobeniusAt.inertiaDeg_eq_one_of_mem_fixingSubgroup`. -/
private lemma frobenius_fixed_pow_sub_mem {g : H ≃ₐ[K] H}
    {p : Ideal (𝓞 K)} {Q : Ideal (𝓞 H)} (hg : IsFrobeniusAt K H g p Q)
    (E : IntermediateField K H) (hgE : g ∈ E.fixingSubgroup) (x : 𝓞 E) :
    x ^ Ideal.absNorm p - x ∈ Q.comap (algebraMap (𝓞 E) (𝓞 H)) := by
  have hfix : g • algebraMap (𝓞 E) (𝓞 H) x = algebraMap (𝓞 E) (𝓞 H) x := by
    apply RingOfIntegers.ext
    change g ((x : E) : H) = ((x : E) : H)
    exact (IntermediateField.mem_fixingSubgroup_iff E g).mp hgE _ (x : E).property
  change algebraMap (𝓞 E) (𝓞 H) (x ^ Ideal.absNorm p - x) ∈ Q
  rw [map_sub, map_pow]
  have hF := hg.sub_mem (algebraMap (𝓞 E) (𝓞 H) x)
  change g • algebraMap (𝓞 E) (𝓞 H) x -
    (algebraMap (𝓞 E) (𝓞 H) x) ^ Ideal.absNorm p ∈ Q at hF
  rw [hfix] at hF
  simpa only [neg_sub] using Q.neg_mem hF

omit [NumberField K] [NumberField H] in
/-- A finite field on which $x\mapsto x^q$ is the identity has at most $q$ elements.
This is the root count used by `IsFrobeniusAt.inertiaDeg_eq_one_of_mem_fixingSubgroup`. -/
private lemma finiteField_card_le_of_pow_eq (F : Type*) [Field F] [Fintype F]
    (q : ℕ) (hq : 1 < q) (hpow : ∀ x : F, x ^ q = x) : Fintype.card F ≤ q := by
  let A : Polynomial F := Polynomial.X ^ q - Polynomial.X
  have hroots : (Finset.univ : Finset F).val ⊆ A.roots := by
    intro y _
    apply (Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero F hq)).2
    change Polynomial.eval y (Polynomial.X ^ q - Polynomial.X) = 0
    simpa only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, sub_eq_zero]
      using hpow y
  calc
    Fintype.card F = (Finset.univ : Finset F).card := by simp
    _ ≤ A.natDegree := Polynomial.card_le_degree_of_subset_roots hroots
    _ = q := FiniteField.X_pow_card_sub_X_natDegree_eq F hq

/-- **A Frobenius element fixing a subfield has residue degree one at the prime below**: if
`g ∈ Gal(H/K)` is
Frobenius at `Q` above $\mathfrak p$ and fixes the intermediate field `E` pointwise, then
$\mathfrak P = Q\cap\mathcal O_E$ has residue degree $f(\mathfrak P\mid\mathfrak p) = 1$. For
$x\in\mathcal O_E$ the Frobenius congruence gives $x = g(x)\equiv x^{N\mathfrak p}
\pmod{\mathfrak P}$, so the residue field of $\mathfrak P$ consists of roots of
$X^{N\mathfrak p}-X$ and has at most $N\mathfrak p$ elements. This is the splitting step of
Childress, *Class Field Theory*, Chapter V, proof of Lemma 2.8(iv), where `E` lies in the
decomposition field. -/
theorem IsFrobeniusAt.inertiaDeg_eq_one_of_mem_fixingSubgroup {g : H ≃ₐ[K] H}
    {p : Ideal (𝓞 K)} {Q : Ideal (𝓞 H)} (hg : IsFrobeniusAt K H g p Q)
    (E : IntermediateField K H) (hgE : g ∈ E.fixingSubgroup) :
    (Q.comap (algebraMap (𝓞 E) (𝓞 H))).inertiaDeg (𝓞 K) = 1 := by
  have : Q.IsPrime := hg.isPrime
  have : Q.LiesOver p := hg.liesOver
  have hp0 := hg.ne_bot
  let P := Q.comap (algebraMap (𝓞 E) (𝓞 H))
  have : P.IsPrime := inferInstance
  have : P.LiesOver p := by
    constructor
    change p = P.comap (algebraMap (𝓞 K) (𝓞 E))
    dsimp [P]
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq (𝓞 K) (𝓞 E) (𝓞 H)]
    exact hg.liesOver.1.symm.symm
  have hP0 : P ≠ ⊥ := by
    intro hP
    apply hp0
    rw [Ideal.over_def P p, hP]
    exact Ideal.under_bot (𝓞 K) (𝓞 E)
  have : p.IsPrime := Ideal.isPrime_of_liesOver P p
  have : p.IsMaximal := Ideal.isMaximal_of_isPrime_of_ne_bot p hp0
  let _ : Field ((𝓞 K) ⧸ p) := Ideal.Quotient.field p
  let _ : Fintype ((𝓞 K) ⧸ p) := Fintype.ofFinite _
  have hq : 1 < Ideal.absNorm p := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have : P.IsMaximal := Ideal.isMaximal_of_isPrime_of_ne_bot P hP0
  let _ : Field ((𝓞 E) ⧸ P) := Ideal.Quotient.field P
  let _ : Fintype ((𝓞 E) ⧸ P) := Fintype.ofFinite _
  have hpow (y : (𝓞 E) ⧸ P) : y ^ Ideal.absNorm p = y := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    simpa only [map_pow] using Ideal.Quotient.eq.mpr
      (frobenius_fixed_pow_sub_mem hg E hgE x)
  have hcard : Fintype.card ((𝓞 E) ⧸ P) ≤ Ideal.absNorm p :=
    finiteField_card_le_of_pow_eq _ _ hq hpow
  have hnorm : Ideal.absNorm p ^ P.inertiaDeg (𝓞 K) = Ideal.absNorm P :=
    Ideal.absNorm_pow_inertiaDeg p P
  have hpow_le : Ideal.absNorm p ^ P.inertiaDeg (𝓞 K) ≤ Ideal.absNorm p := by
    rw [hnorm, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    exact hcard
  apply Nat.le_antisymm
  · exact (Nat.pow_le_pow_iff_right hq).mp (by simpa only [pow_one] using hpow_le)
  · exact Ideal.inertiaDeg_pos P (𝓞 K)

omit [NumberField H] in
/-- Frobenius restricts to Frobenius on a normal subextension `E`, given as a field in a tower
`K ⊆ E ⊆ H`. Milne, *Class Field Theory*, Chapter V, 1.11. -/
theorem IsFrobeniusAt.restrictNormal
    {g : H ≃ₐ[K] H} {p : Ideal (𝓞 K)} {Q : Ideal (𝓞 H)}
    (hg : IsFrobeniusAt K H g p Q) (E : Type*) [Field E] [Algebra K E] [Algebra E H]
    [IsScalarTower K E H] [Normal K E] :
    IsFrobeniusAt K E (g.restrictNormal E) p
      (Ideal.comap (algebraMap (𝓞 E) (𝓞 H)) Q) := by
  have : Q.IsPrime := hg.isPrime
  refine ⟨inferInstance, ?_, fun x ↦ ?_⟩
  · rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq (𝓞 K) (𝓞 E) (𝓞 H)]
    exact hg.liesOver.1.symm
  · change algebraMap (𝓞 E) (𝓞 H) (g.restrictNormal E • x - x ^ p.absNorm) ∈ Q
    rw [map_sub, map_pow]
    have heq : algebraMap (𝓞 E) (𝓞 H) (g.restrictNormal E • x) =
        g • algebraMap (𝓞 E) (𝓞 H) x :=
      RingOfIntegers.ext (AlgEquiv.restrictNormal_commutes g E x)
    rw [heq]
    exact hg.sub_mem (algebraMap (𝓞 E) (𝓞 H) x)

/-! ### Frobenius in towers of prime exponent

In an unramified extension killed by a prime $p$, every nontrivial element of a decomposition
group generates it. A nontrivial relative Frobenius therefore forces the intermediate residue
degree to be one, and its relative and absolute Frobenius congruences coincide. This is the
local step in Milne, *Class Field Theory*, Chapter VII, Lemma 6.2. -/

/-- A nontrivial element of an unramified decomposition group in an extension killed by $p$
generates that group. This is the cyclic-group step used by
`IsFrobeniusAt.inertiaDeg_eq_one_of_ne_one`. -/
private theorem zpowers_eq_decomposition_of_ne_one [IsGalois K H]
    (n : ℕ) [Fact n.Prime] (hn : ∀ σ : H ≃ₐ[K] H, σ ^ n = 1)
    {p : Ideal (𝓞 K)} {Q : Ideal (𝓞 H)} [Q.IsPrime] [Q.LiesOver p]
    (hp : p ≠ ⊥) (hunr : Q.ramificationIdx (𝓞 K) = 1)
    {g : H ≃ₐ[K] H} (hg : g ∈ MulAction.stabilizer (H ≃ₐ[K] H) Q) (hg1 : g ≠ 1) :
    Subgroup.zpowers g = MulAction.stabilizer (H ≃ₐ[K] H) Q := by
  obtain ⟨τ, hτ⟩ := exists_isFrobeniusAt p Q hp
  apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hg)
  rw [← hτ.zpowers_eq_decomposition hunr, Nat.card_zpowers, Nat.card_zpowers,
    orderOf_eq_prime (hn g) hg1]
  exact Nat.le_of_dvd (Fact.out : n.Prime).pos (orderOf_dvd_of_pow_eq_one (hn τ))

/-- A nontrivial relative Frobenius in a Galois tower of prime exponent forces the intermediate
residue degree to be one. Milne, *Class Field Theory*, Chapter VII, proof of Lemma 6.2. -/
theorem IsFrobeniusAt.inertiaDeg_eq_one_of_ne_one [IsGalois K H]
    (n : ℕ) [Fact n.Prime] (hn : ∀ σ : H ≃ₐ[K] H, σ ^ n = 1)
    (E : IntermediateField K H) [IsGalois K E]
    {p : Ideal (𝓞 K)} {Q : Ideal (𝓞 H)} [Q.LiesOver p]
    {g : H ≃ₐ[E] H}
    (hg : IsFrobeniusAt E H g (Q.under (𝓞 E)) Q)
    (hunr : Q.ramificationIdx (𝓞 K) = 1) (hg1 : g ≠ 1) :
    (Q.under (𝓞 E)).inertiaDeg (𝓞 K) = 1 := by
  have : Q.IsPrime := hg.isPrime
  let P := Q.under (𝓞 E)
  have hQ : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hg.ne_bot Q
  have hp : p ≠ ⊥ := by
    rw [Ideal.over_def Q p]
    exact Ideal.under_ne_bot (𝓞 K) hQ
  have hgD : g.restrictScalars K ∈ MulAction.stabilizer (H ≃ₐ[K] H) Q :=
    hg.isArithFrobAt.mem_stabilizer
  have hz := zpowers_eq_decomposition_of_ne_one n hn hp hunr hgD
    (fun h => hg1 ((AlgEquiv.restrictScalarsHom_injective K) h))
  have hfix : MulAction.stabilizer (H ≃ₐ[K] H) Q ≤ E.fixingSubgroup := by
    rw [← hz]
    apply Subgroup.zpowers_le.mpr
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact g.commutes ⟨x, hx⟩
  obtain ⟨τ, hτ⟩ := exists_isFrobeniusAt p Q hp
  have hres : τ.restrictNormal E = 1 := (AlgEquiv.restrictNormal_eq_one_iff E τ).mpr
    ((IntermediateField.mem_fixingSubgroup_iff E τ).mp (hfix hτ.isArithFrobAt.mem_stabilizer))
  have hP : IsFrobeniusAt K E 1 p P := by
    simpa only [hres] using hτ.restrictNormal E
  have hPram : P.ramificationIdx (𝓞 K) = 1 :=
    ramificationIdx_below_eq_one P Q hunr
  have hD : MulAction.stabilizer (E ≃ₐ[K] E) P = ⊥ := by
    rw [← hP.zpowers_eq_decomposition hPram, Subgroup.zpowers_one_eq_bot]
  have : p.IsPrime := Ideal.isPrime_of_liesOver Q p
  have : p.IsMaximal := Ideal.isMaximal_of_isPrime_of_ne_bot p hp
  have : Finite p.ResidueField := inferInstance
  have : PerfectField p.ResidueField := PerfectField.ofFinite
  have hI := inertia_eq_bot_of_ramificationIdx_eq_one hp P hPram
  have hc := Ideal.card_stabilizer_eq_card_inertia_mul_finrank (G := E ≃ₐ[K] E) p P
  simpa only [hD, hI, Subgroup.card_bot, one_mul] using hc.symm

/-- Relative Frobenius is absolute Frobenius whenever its intermediate residue degree is one.
This is the equality of Frobenius elements used by Milne, *Class Field Theory*, Chapter VII,
proof of Lemma 6.2. -/
theorem IsFrobeniusAt.restrictScalars_of_inertiaDeg_eq_one
    (E : IntermediateField K H) {p : Ideal (𝓞 K)} {Q : Ideal (𝓞 H)}
    [Q.LiesOver p] {g : H ≃ₐ[E] H}
    (hg : IsFrobeniusAt E H g (Q.under (𝓞 E)) Q)
    (hf : (Q.under (𝓞 E)).inertiaDeg (𝓞 K) = 1) :
    IsFrobeniusAt K H (g.restrictScalars K) p Q := by
  have : Q.IsPrime := hg.isPrime
  refine ⟨inferInstance, (Ideal.over_def Q p).symm, ?_⟩
  have hnorm := Ideal.absNorm_pow_inertiaDeg p (Q.under (𝓞 E))
  rw [hf, pow_one] at hnorm
  intro x
  simpa only [AlgEquiv.toRingEquiv_restrictScalars, hnorm] using hg.sub_mem x

/-- In a tower killed by a prime, a nontrivial relative Frobenius at an unramified prime equals
absolute Frobenius. Milne, *Class Field Theory*, Chapter VII, proof of Lemma 6.2. -/
theorem IsFrobeniusAt.restrictScalars_of_ne_one [IsGalois K H]
    (n : ℕ) [Fact n.Prime] (hn : ∀ σ : H ≃ₐ[K] H, σ ^ n = 1)
    (E : IntermediateField K H) [IsGalois K E]
    {p : Ideal (𝓞 K)} {Q : Ideal (𝓞 H)} [Q.LiesOver p]
    {g : H ≃ₐ[E] H} (hg : IsFrobeniusAt E H g (Q.under (𝓞 E)) Q)
    (hunr : Q.ramificationIdx (𝓞 K) = 1) (hg1 : g ≠ 1) :
    IsFrobeniusAt K H (g.restrictScalars K) p Q := by
  have : Q.IsPrime := hg.isPrime
  exact hg.restrictScalars_of_inertiaDeg_eq_one E
    (hg.inertiaDeg_eq_one_of_ne_one n hn E (p := p) hunr hg1)

end SIC

end
