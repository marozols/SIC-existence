/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Local.FinitePowerIndex
import SICs.ClassField.Frobenius.Basis
import SICs.ClassField.SUnits.Kummer

/-!
# Localization of S-unit power classes

A Frobenius basis detects S-unit powers and gives local power classes represented by S-units.

This follows Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII,
Lemmas 6.2, 6.3, and 6.9.

## The argument

The S-units map to integral local units at every prime outside S. Their localization to
power classes has kernel consisting of the S-units that become powers at all selected primes.
The Frobenius basis identifies this kernel with the S-units becoming powers in the
intermediate field. Relative Kummer theory gives the index of this kernel as $p^{|T|}$.
Each selected prime lies away from p, so the local integral unit power index is p.
The product target therefore has the same order as the image, proving surjectivity.
-/

noncomputable section

open IsDedekindDomain NumberField
open scoped SIC.FinitePlace

namespace SIC

variable {K : Type*} [Field K] [NumberField K]

/-! ### The S-unit instance of the power test -/

/-- An S-unit becomes a pth power in the intermediate field exactly when it becomes a
pth power at the selected completions. This is the S-unit instance of
`FrobeniusBasis.isPower_iff` in Milne, *Class Field Theory*, Chapter VII, Lemma 6.3. -/
theorem FrobeniusBasis.isPower_sUnit_iff {p : ℕ} [NeZero p]
    {S : Finset (HeightOneSpectrum (𝓞 K))}
    {L : IntermediateField K (IdeleGroup.sUnitKummer K p S)}
    (B : FrobeniusBasis p L S) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (a : IdeleGroup.sUnits (K := K) (L := K) S) :
    (∃ x : L, x ^ p = algebraMap K L (a.val : K)) ↔
      ∀ v ∈ B.basePrimes, ∃ x : v.adicCompletion K,
        x ^ p = algebraMap K (v.adicCompletion K) (a.val : K) := by
  have : IsAbelianGalois K (IdeleGroup.sUnitKummer K p S) :=
    IdeleGroup.sUnitKummer_isAbelianGalois hζ (NeZero.pos p) S
  exact B.isPower_iff hζ (NeZero.pos p) (a.val : K)
    (IdeleGroup.exists_root_sUnitKummer (NeZero.pos p) S a)

end SIC

namespace SIC.IdeleGroup

variable {K : Type*} [Field K] [NumberField K]

/-- A basis of relative Frobenius elements in the S-unit radical field, at primes outside S
that split in the intermediate field. Milne, *Class Field Theory*, Chapter VII, Lemma 6.2,
specializing `nonempty_frobeniusBasis` with `ramificationIdx_sUnitKummer`. -/
theorem exists_frobeniusBasis_sUnitKummer (p : ℕ) [Fact p.Prime] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (L : IntermediateField K (sUnitKummer K p S)) :
    Nonempty (FrobeniusBasis p L S) := by
  let : IsAbelianGalois K (sUnitKummer K p S) :=
    sUnitKummer_isAbelianGalois hζ (NeZero.pos p) S
  apply nonempty_frobeniusBasis p (sUnitKummer_aut_pow hζ (NeZero.pos p) S) L S
  apply (FinitePlace.ramifiedSet_subset_iff S).mpr
  intro w hw
  exact ramificationIdx_sUnitKummer S (FinitePlace.below (K := K) w) hw
    (fun hp => hw (hS _ hp)) w

/-! ### Completion and local power classes

Outside S, an S-unit has valuation one, so its completion is an integral local unit.
An nth root of an integral unit is again integral when $n>0$, allowing quotient equalities
to be expressed using roots in the full local multiplicative group. -/

/-- The completion map $U(S)\to U_v$ at a finite place $v\notin S$.
This supplies the localization map of Milne, Chapter VII, Lemma 6.9. -/
def sUnitCompletion (S : Finset (HeightOneSpectrum (𝓞 K)))
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    sUnits (K := K) (L := K) S →* FinitePlace.unitGroup v :=
  ((Units.map (algebraMap K (v.adicCompletion K) : K →* _)).comp
    (sUnits (K := K) (L := K) S).subtype).codRestrict _ fun a ↦ by
      exact (FinitePlace.units_map_mem_unitGroup_iff v a.val).mpr
        (sUnits_valuation_eq_one S a v (by simpa only [FinitePlace.below_self] using hv))

/-- The underlying local unit of an S-unit completion is its image under the algebra map. -/
@[simp] theorem sUnitCompletion_coe (S : Finset (HeightOneSpectrum (𝓞 K)))
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) (a : sUnits (K := K) (L := K) S) :
    (sUnitCompletion S v hv a).val =
      Units.map (algebraMap K (v.adicCompletion K) : K →* _) a.val := rfl

/-- The localization $U(S)\to\prod_{v\in T}U_v/U_v^n$ for disjoint $S$ and $T$.
Milne, *Class Field Theory*, Chapter VII, Lemma 6.9, localization map. -/
def sUnitsToLocalPowers (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hST : Disjoint S T) :
    sUnits (K := K) (L := K) S →*
      ∀ v : T, FinitePlace.unitGroup v.val ⧸
        (powMonoidHom n : FinitePlace.unitGroup v.val →* FinitePlace.unitGroup v.val).range :=
  MonoidHom.pi fun v : T ↦
    (QuotientGroup.mk' (powMonoidHom (α := FinitePlace.unitGroup v.val) n).range).comp
    (sUnitCompletion S v.val (Finset.disjoint_left.mp hST.symm v.property))

/-- Localization at $v$ is the power class of the S-unit's completion. -/
@[simp] theorem sUnitsToLocalPowers_apply (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hST : Disjoint S T) (a : sUnits (K := K) (L := K) S) (v : T) :
    sUnitsToLocalPowers n S T hST a v =
      QuotientGroup.mk (sUnitCompletion S v.val
        (Finset.disjoint_left.mp hST.symm v.property) a) := rfl

/-- Equality of integral unit power classes means their ratio is an ambient local nth power.
The root remains integral by its valuation; used by `sUnitsToLocalPowers_eq_one_iff`. -/
private theorem localPowerClass_eq_iff (v : HeightOneSpectrum (𝓞 K))
    {n : ℕ} (hn : 0 < n) (a b : FinitePlace.unitGroup v) :
    (QuotientGroup.mk a : FinitePlace.unitGroup v ⧸ (powMonoidHom n).range) =
      QuotientGroup.mk b ↔
      ∃ z : (v.adicCompletion K)ˣ, a.val = b.val * z ^ n := by
  rw [QuotientGroup.eq_iff_div_mem]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z.val, ?_⟩
    have hz' : z.val ^ n = a.val / b.val := congrArg Subtype.val hz
    rw [hz', mul_comm, div_mul_cancel]
  · rintro ⟨z, hz⟩
    have hunit : z ∈ FinitePlace.unitGroup v := by
      rw [← FinitePlace.unitsValuation_eq_one_iff]
      apply (pow_eq_one_iff_left hn.ne').mp
      rw [← map_pow, ← div_eq_iff_eq_mul'.mpr hz, map_div,
        (FinitePlace.unitsValuation_eq_one_iff v).mpr a.property,
        (FinitePlace.unitsValuation_eq_one_iff v).mpr b.property, div_self']
    exact ⟨⟨z, hunit⟩, Subtype.ext (div_eq_iff_eq_mul'.mpr hz).symm⟩

/-- Surjectivity of S-unit localization supplies representatives of every tuple of local
unit power classes. This direction does not require a positive exponent; used by the auxiliary
group in `exists_pow_eq_of_local`. -/
theorem sUnitsToLocalPowers_representatives (n : ℕ)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : Disjoint S T)
    (h : Function.Surjective (sUnitsToLocalPowers n S T hST))
    (u : (v : T) → FinitePlace.unitGroup v.val) :
    ∃ a : sUnits (K := K) (L := K) S, ∀ v : T,
      ∃ z : (v.val.adicCompletion K)ˣ,
        Units.map (algebraMap K (v.val.adicCompletion K) : K →* _) a.val =
          (u v).val * z ^ n := by
  obtain ⟨a, ha⟩ := h (fun v => QuotientGroup.mk (u v))
  refine ⟨a, fun v => ?_⟩
  have heq : (QuotientGroup.mk (sUnitCompletion S v.val
      (Finset.disjoint_left.mp hST.symm v.property) a) :
      FinitePlace.unitGroup v.val ⧸ (powMonoidHom n).range) = QuotientGroup.mk (u v) := by
    simpa only [sUnitsToLocalPowers_apply] using congrFun ha v
  rw [QuotientGroup.eq_iff_div_mem] at heq
  obtain ⟨z, hz⟩ := heq
  refine ⟨z.val, ?_⟩
  have hz' : z.val ^ n =
      (sUnitCompletion S v.val (Finset.disjoint_left.mp hST.symm v.property) a).val /
        (u v).val := congrArg Subtype.val hz
  rw [sUnitCompletion_coe] at hz'
  rw [hz', mul_comm, div_mul_cancel]

/-! ### The kernel and the cardinality comparison

Vanishing local power classes are precisely local nth powers. The Frobenius basis tests
whether these roots descend to the intermediate field. Its size measures the relative
Kummer degree, while the local unit index computes the target order. -/

/-- An S-unit has trivial localization exactly when it has a root at every selected prime.
This translates the kernel in Milne, Chapter VII, proof of Lemma 6.9
to `FrobeniusBasis.isPower_sUnit_iff`. -/
private theorem sUnitsToLocalPowers_eq_one_iff {n : ℕ} (hn : 0 < n)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : Disjoint S T)
    (a : sUnits (K := K) (L := K) S) :
    sUnitsToLocalPowers n S T hST a = 1 ↔
      ∀ v ∈ T, ∃ x : v.adicCompletion K,
        x ^ n = algebraMap K (v.adicCompletion K) (a.val : K) := by
  constructor
  · intro h v hv
    obtain ⟨z, hz⟩ := (localPowerClass_eq_iff v hn _ 1).mp (congrFun h ⟨v, hv⟩)
    exact ⟨z, by simpa using congrArg Units.val hz.symm⟩
  · intro h
    apply funext
    intro v
    obtain ⟨x, hx⟩ := h v.val v.property
    have hx0 : x ≠ 0 := by
      intro hx0
      apply a.val.ne_zero
      apply (algebraMap K (v.val.adicCompletion K)).injective
      simpa [hx0, hn.ne'] using hx.symm
    apply (localPowerClass_eq_iff v.val hn _ 1).mpr
    refine ⟨Units.mk0 x hx0, Units.ext ?_⟩
    simpa using hx.symm

/-- The Frobenius localization kernel is $U(S)\cap L^{\times p}$.
Milne, *Class Field Theory*, Chapter VII, proof of Lemma 6.9, using Lemma 6.3. -/
private theorem ker_frobeniusLocalization {p : ℕ} [NeZero p] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) {S : Finset (HeightOneSpectrum (𝓞 K))}
    {L : IntermediateField K (sUnitKummer K p S)} (B : FrobeniusBasis p L S) :
    (sUnitsToLocalPowers p S B.basePrimes B.disjoint_basePrimes.symm).ker =
      (kummerRadicands K p L).comap (sUnits (K := K) (L := K) S).subtype := by
  ext a
  exact (sUnitsToLocalPowers_eq_one_iff (NeZero.pos p) S B.basePrimes
    B.disjoint_basePrimes.symm a).trans (B.isPower_sUnit_iff hζ a).symm

/-- At primes away from $n$, the product of local integral unit power quotients has order
$n^{|T|}$. This is Milne, Chapter VII, Proposition 6.8 in the proof of Lemma 6.9. -/
private theorem card_localUnitPowerClasses {n : ℕ} {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) (hn : 0 < n) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ v ∈ T, (n : 𝓞 K) ∉ v.asIdeal) :
    Nat.card ((v : T) → FinitePlace.unitGroup v.val ⧸
      (powMonoidHom n : FinitePlace.unitGroup v.val →* FinitePlace.unitGroup v.val).range) =
      n ^ T.card := by
  have : NeZero n := ⟨hn.ne'⟩
  have hcard (v : T) : Nat.card (FinitePlace.unitGroup v.val ⧸
      (powMonoidHom n : FinitePlace.unitGroup v.val →* FinitePlace.unitGroup v.val).range) = n := by
    have hnorm : ‖(n : v.val.adicCompletion K)‖ = 1 := by
      simpa using (NumberField.FinitePlace.norm_eq_one_iff_notMem K v.val
        (n : 𝓞 K)).mpr (hT v.val v.property)
    have heq := FinitePlace.card_unitGroup_powerQuotient v.val hn
    rw [(hζ.map_of_injective (algebraMap K (v.val.adicCompletion K)).injective).card_rootsOfUnity,
      hnorm, div_one] at heq
    exact_mod_cast heq
  rw [Nat.card_pi]
  simp only [hcard, Finset.prod_const, Finset.card_univ, Fintype.card_coe]

end SIC.IdeleGroup

namespace SIC

variable {K : Type*} [Field K] [NumberField K]

/-- A supplied Frobenius basis makes $U(S)\to\prod_{v\in T}U_v/U_v^p$ surjective.
This supplied-basis form needs only $p>0$; its prime-exponent specialization is
Milne, *Class Field Theory*, Chapter VII, Lemma 6.9. -/
theorem FrobeniusBasis.sUnitsToLocalPowers_surjective {p : ℕ} [NeZero p]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {S : Finset (HeightOneSpectrum (𝓞 K))}
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    {L : IntermediateField K (IdeleGroup.sUnitKummer K p S)}
    (B : FrobeniusBasis p L S) :
    Function.Surjective (IdeleGroup.sUnitsToLocalPowers p S B.basePrimes
      B.disjoint_basePrimes.symm) := by
  let U := (v : B.basePrimes) → FinitePlace.unitGroup v.val ⧸
    (powMonoidHom p : FinitePlace.unitGroup v.val →* FinitePlace.unitGroup v.val).range
  let f : IdeleGroup.sUnits (K := K) (L := K) S →* U :=
    IdeleGroup.sUnitsToLocalPowers p S B.basePrimes B.disjoint_basePrimes.symm
  have hcard : Nat.card U = p ^ B.primes.card := by
    dsimp only [U]
    rw [IdeleGroup.card_localUnitPowerClasses hζ (NeZero.pos p) B.basePrimes
      (fun v hv hpv ↦ Finset.disjoint_left.mp B.disjoint_basePrimes hv (hS v hpv)),
      B.card_basePrimes]
  have := Nat.finite_of_card_ne_zero (hcard.trans_ne (pow_ne_zero _ (NeZero.ne p)))
  let H := MonoidHom.range (G := IdeleGroup.sUnits (K := K) (L := K) S) (N := U) f
  have hrange : H = ⊤ := by
    apply (Subgroup.card_eq_iff_eq_top H).mp
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange
      (G := IdeleGroup.sUnits (K := K) (L := K) S) (H := U) f).toEquiv]
    change Nat.card (_ ⧸ (IdeleGroup.sUnitsToLocalPowers p S B.basePrimes
      B.disjoint_basePrimes.symm).ker) = _
    rw [IdeleGroup.ker_frobeniusLocalization hζ B]
    exact (kummerExtension_finrank_relative hζ (NeZero.pos p)
      (IdeleGroup.sUnits_fg S) L).symm.trans (B.card.symm.trans hcard.symm)
  exact (MonoidHom.range_eq_top (G := IdeleGroup.sUnits (K := K) (L := K) S)
    (N := U) (f := f)).mp hrange

end SIC
