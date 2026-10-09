/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.SUnits.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# Idèle classes represented by S-idèles

A sufficiently large finite set of finite places supports representatives of every ideal
class. Correcting an idèle by the principal idèle of the difference of its fractional ideal
and a representative leaves an idèle integral outside that set. Thus `S`-idèles and principal
idèles generate the idèle group, and the kernel of the restricted quotient map consists exactly
of the principal idèles of `S`-units. For the empty finite set, the image is the kernel
of the ordinary ideal-class map, so the cokernel is finite.

This is the ideal-class argument of Milne, *Class Field Theory*, version 4.03 (2020),
Chapter VII, Lemma 4.2 and the proof of Theorem 4.3. Here `S` lists only finite places of
the base field; all infinite places are allowed. The empty-set sequence is Childress,
*Class Field Theory* (2009), Chapter IV, Propositions 3.2–3.3, used in Corollary 5.11.
Childress writes $E_L$ for the idèles that are units at every finite place and $U_L$ for
the ordinary global units; these are the present `S`-objects at `S = ∅`.

## The argument

A finite set of ideal-class representatives and the primes dividing a nonzero integer supply
finite support. A principal correction makes any idèle integral outside that support. The
kernel of the restricted class map consists of principal S-unit idèles, giving an equivariant
sequence. At empty support, the ordinary class group is its finite cokernel.
-/

noncomputable section

open IsDedekindDomain NumberField
open scoped NumberField nonZeroDivisors

namespace SIC.IdeleGroup

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-! ### Ordinary ideal classes and finite support

The map to the ordinary ideal class group detects whether an idèle differs from an
`S`-idèle by a principal idèle. Finiteness of that class group supplies a single finite
set `S` on which all its chosen representatives lie. -/

/-- The ordinary ideal class of an `S`-idèle. -/
def sIdealClass (S : Finset (HeightOneSpectrum (𝓞 K))) :
    sSubgroup (L := L) S →* ClassGroup (𝓞 L) :=
  (idealClass (K := L)).comp (sSubgroup (L := L) S).subtype

omit [NumberField K] in
/-- The restricted ideal-class map computes as the ordinary ideal class of the idèle. -/
@[simp]
theorem sIdealClass_apply (S : Finset (HeightOneSpectrum (𝓞 K)))
    (y : sSubgroup (L := L) S) : sIdealClass (L := L) S y = idealClass y.1 :=
  rfl

omit [NumberField K] in
/-- Enlarging the base support preserves surjectivity of the restricted ideal-class map;
used in `exists_support_sIdealClass`. -/
theorem sIdealClass_surjective_mono {A B : Finset (HeightOneSpectrum (𝓞 K))}
    (hAB : A ⊆ B) (hA : Function.Surjective (sIdealClass (L := L) A)) :
    Function.Surjective (sIdealClass (L := L) B) := by
  intro c
  obtain ⟨a, ha⟩ := hA c
  exact ⟨⟨a.1, sSubgroup_mono (L := L) hAB a.2⟩, ha⟩

omit [NumberField K] in
/-- An idèle of trivial fractional ideal is integral outside every finite set; used by
`mul_principal_of_idealClass_eq_one`. -/
private theorem mem_sSubgroup_of_toFractionalIdeal_eq_one
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : NumberField.IdeleGroup (𝓞 L) L) (hx : toFractionalIdeal x = 1) :
    x ∈ sSubgroup (L := L) S := by
  rw [mem_sSubgroup]
  intro w _
  exact (FinitePlace.mem_unitGroup_iff_valued w _).2
    ((toFractionalIdeal_eq_one_iff x).1 hx w)

omit [NumberField K] in
/-- An idèle of trivial ideal class admits a principal correction integral outside `S`;
used by `mul_principal_of_sIdealClass_surjective` and `sClassMap_range_empty`. -/
private theorem mul_principal_of_idealClass_eq_one
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : NumberField.IdeleGroup (𝓞 L) L) (hx : idealClass x = 1) :
    ∃ a : Lˣ, ∃ y : sSubgroup (L := L) S,
      x = NumberField.IdeleGroup.unitEmbedding (𝓞 L) L a * y.1 := by
  obtain ⟨a, ha⟩ := (FractionalIdeal.isPrincipal_iff _).1
    ((ClassGroup.mk_eq_one_iff).1 hx)
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, FractionalIdeal.spanSingleton_zero] at ha
    exact (toFractionalIdeal x).ne_zero ha
  let aUnit : Lˣ := Units.mk0 a ha0
  have hfrac : toFractionalIdeal x =
      toFractionalIdeal (NumberField.IdeleGroup.unitEmbedding (𝓞 L) L aUnit) := by
    apply Units.ext
    simpa only [coe_toFractionalIdeal_unitEmbedding, aUnit, Units.val_mk0] using ha
  let y := (NumberField.IdeleGroup.unitEmbedding (𝓞 L) L aUnit)⁻¹ * x
  have hy : y ∈ sSubgroup (L := L) S := by
    apply mem_sSubgroup_of_toFractionalIdeal_eq_one S y
    simp [y, hfrac]
  refine ⟨aUnit, ⟨y, hy⟩, ?_⟩
  dsimp [y]
  group

omit [NumberField K] in
/-- Surjectivity onto ordinary ideal classes lets one correct every idèle by a principal
idèle until it is integral outside `S`. Milne, *Class Field Theory*, Chapter VII, Lemma 4.2. -/
theorem mul_principal_of_sIdealClass_surjective
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : Function.Surjective (sIdealClass (L := L) S))
    (x : NumberField.IdeleGroup (𝓞 L) L) :
    ∃ a : Lˣ, ∃ y : sSubgroup (L := L) S,
      x = NumberField.IdeleGroup.unitEmbedding (𝓞 L) L a * y.1 := by
  obtain ⟨y, hy⟩ := hS (idealClass x)
  have hclass : idealClass (x * y.1⁻¹) = 1 := by
    rw [map_mul, map_inv, ← sIdealClass_apply S y, hy, mul_inv_cancel]
  obtain ⟨a, z, hz⟩ := mul_principal_of_idealClass_eq_one S _ hclass
  refine ⟨a, z * y, ?_⟩
  change x = NumberField.IdeleGroup.unitEmbedding (𝓞 L) L a * (z.1 * y.1)
  rw [← mul_assoc, ← hz]
  group

omit [NumberField K] in
/-- S-idèles representing every ideal class, together with principal idèles, generate $I_L$.
Milne, *Class Field Theory*, Chapter VII, Lemma 4.2; subgroup form of
`mul_principal_of_sIdealClass_surjective`. -/
theorem sSubgroup_sup_principal (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : Function.Surjective (sIdealClass (L := L) S)) :
    sSubgroup (L := L) S ⊔ NumberField.IdeleGroup.principalSubgroup (𝓞 L) L = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨a, y, rfl⟩ := mul_principal_of_sIdealClass_surjective S hS x
  exact (sSubgroup (L := L) S ⊔ NumberField.IdeleGroup.principalSubgroup (𝓞 L) L).mul_mem
    (Subgroup.mem_sup_right ⟨a, rfl⟩) (Subgroup.mem_sup_left y.property)

omit [NumberField K] in
/-- A finite set of base places supports `S`-idèles representing every ordinary ideal
class of `L`. Milne, *Class Field Theory*, Chapter VII, Lemma 4.2. -/
theorem exists_sIdealClass_surjective :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      Function.Surjective (sIdealClass (L := L) S) := by
  classical
  let J : ClassGroup (𝓞 L) → (Ideal (𝓞 L))⁰ :=
    fun c ↦ Classical.choose (ClassGroup.mk0_surjective c)
  let x : ClassGroup (𝓞 L) → NumberField.IdeleGroup (𝓞 L) L :=
    fun c ↦ ofFractionalIdeal (FractionalIdeal.mk0 L (J c))
  let T : ClassGroup (𝓞 L) → Finset (HeightOneSpectrum (𝓞 K)) :=
    fun c ↦ Classical.choose (exists_mem_sSubgroup (K := K) (x c))
  let S := Finset.univ.biUnion T
  refine ⟨S, fun c ↦ ?_⟩
  have hc : x c ∈ sSubgroup (L := L) S :=
    sSubgroup_mono (L := L) (S := T c) (T := S)
      (by intro v hv; exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, hv⟩)
      (Classical.choose_spec (exists_mem_sSubgroup (K := K) (x c)))
  refine ⟨⟨x c, hc⟩, ?_⟩
  change idealClass (x c) = c
  change ClassGroup.mk L (toFractionalIdeal (ofFractionalIdeal
    (FractionalIdeal.mk0 L (J c)))) = c
  rw [toFractionalIdeal_ofFractionalIdeal, ClassGroup.mk_mk0]
  exact Classical.choose_spec (ClassGroup.mk0_surjective c)

omit [NumberField K] in
/-- For a nonzero integer $n$, finitely many base primes contain every prime of $L$ dividing
$n$; used by `exists_support_sIdealClass`. -/
private theorem exists_support_natCast (n : ℕ) (hn : n ≠ 0) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)),
      ∀ w : HeightOneSpectrum (𝓞 L), (n : 𝓞 L) ∈ w.asIdeal →
        FinitePlace.below (K := K) w ∈ T := by
  let a : Lˣ := Units.mk0 (n : L) (Nat.cast_ne_zero.mpr hn)
  obtain ⟨T, hT⟩ := exists_mem_sUnits (K := K) (L := L) a
  refine ⟨T, ?_⟩
  intro w hw
  by_contra hnot
  have hval := sUnits_valuation_eq_one T ⟨a, hT⟩ w hnot
  apply HeightOneSpectrum.intValuation_eq_one_iff.mp ?_ hw
  rw [← w.valuation_of_algebraMap (K := L)]
  simpa only [a, Units.val_mk0, RingOfIntegers.coe_eq_algebraMap, map_natCast] using hval

/-! ### Selecting finite support

The union of the initial support, the primes below those dividing a nonzero integer, and
the primes below ideal-class representatives meets all three support requirements. -/

/-- Enlarge a finite set of places of `K` to contain every place of `L` dividing `n` and
to support `S`-idèles representing every ideal class of `L`. This combines the finite
support choice in Childress, *Class Field Theory*, Chapter VI, proof of Theorem 2.7, with
the ideal-class representatives of Milne, *Class Field Theory*, Chapter VII, Lemma 4.2. -/
theorem exists_support_sIdealClass (n : ℕ) [NeZero n]
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ S₁ : Finset (HeightOneSpectrum (𝓞 K)), S ⊆ S₁ ∧
      (∀ w : HeightOneSpectrum (𝓞 L), (n : 𝓞 L) ∈ w.asIdeal →
        w ∈ FinitePlace.placesAbove (L := L) S₁) ∧
      Function.Surjective (sIdealClass (K := L) (L := L)
        (FinitePlace.placesAbove (L := L) S₁)) := by
  classical
  obtain ⟨A, hA⟩ := exists_sIdealClass_surjective (K := L) (L := L)
  obtain ⟨T, hT⟩ := exists_support_natCast (K := K) (L := L) n (NeZero.ne n)
  let S₁ := S ∪ T ∪ A.image (FinitePlace.below (K := K))
  refine ⟨S₁, Finset.subset_union_left.trans Finset.subset_union_left, ?_, ?_⟩
  · intro w hw
    apply (FinitePlace.mem_placesAbove S₁ w).2
    exact Finset.mem_union_left _ (Finset.mem_union_right _ (hT w hw))
  · refine sIdealClass_surjective_mono ?_ hA
    intro w hw
    apply (FinitePlace.mem_placesAbove S₁ w).2
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hw)

/-! ### The restricted idèle class sequence

The quotient map from `S`-idèles to idèle classes has precisely the principal `S`-idèles
as its kernel. At `S = ∅`, a trivial ordinary ideal class allows a principal correction
to an idèle that is a unit at every finite place, identifying the image with the ideal-class
kernel. -/

/-- The quotient map $I_{L,S}\to C_L$ as a monoid homomorphism. -/
def sClassMap (S : Finset (HeightOneSpectrum (𝓞 K))) :
    sSubgroup (L := L) S →* NumberField.IdeleClassGroup (𝓞 L) L :=
  (QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 L) L)).comp
    (sSubgroup (L := L) S).subtype

omit [NumberField K] in
/-- The image of the ordinary-unit idèles $E_L$ in $C_L$ is the kernel of the ordinary
ideal-class map. Childress, *Class Field Theory* (2009), Chapter IV, Proposition 3.3. -/
theorem sClassMap_range_empty :
    (sClassMap (K := K) (L := L) ∅).range = (IdeleClassGroup.idealClass (K := L)).ker := by
  ext c
  constructor
  · rintro ⟨y, rfl⟩
    have hy : toFractionalIdeal y.1 = 1 := by
      apply (toFractionalIdeal_eq_one_iff y.1).2
      intro w
      exact (FinitePlace.mem_unitGroup_iff_valued w _).1
        ((mem_sSubgroup ∅ y.1).1 y.2 w (by simp))
    change ClassGroup.mk L (toFractionalIdeal y.1) = 1
    rw [hy, map_one]
  · intro hc
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
    change idealClass x = 1 at hc
    obtain ⟨a, y, hx⟩ := mul_principal_of_idealClass_eq_one (K := K) ∅ x hc
    refine ⟨y, ?_⟩
    change (y.1 : NumberField.IdeleClassGroup (𝓞 L) L) =
      (x : NumberField.IdeleClassGroup (𝓞 L) L)
    rw [hx, QuotientGroup.mk_mul, IdeleClassGroup.coe_unitEmbedding]
    exact (one_mul (y.1 : NumberField.IdeleClassGroup (𝓞 L) L)).symm

/-- The principal embedding $U(T)\to I_{L,S}$, where $T$ consists of places above `S`. -/
def sUnitsEmbedding (S : Finset (HeightOneSpectrum (𝓞 K))) :
    sUnits (L := L) S →* sSubgroup (L := L) S :=
  ((NumberField.IdeleGroup.unitEmbedding (𝓞 L) L).domRestrict (sUnits (L := L) S)).codRestrict
    (sSubgroup (L := L) S) (fun a => (mem_sUnits S a.1).1 a.2)

omit [NumberField K] in
/-- The restricted principal embedding computes to the principal idèle. -/
@[simp]
theorem sUnitsEmbedding_apply (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : sUnits (L := L) S) :
    (sUnitsEmbedding (L := L) S a).1 =
      NumberField.IdeleGroup.unitEmbedding (𝓞 L) L a.1 :=
  rfl

omit [NumberField K] in
/-- The kernel of $I_{L,S}\to C_L$ is exactly the image of the actual S-units $U(T)$. -/
theorem sClassMap_ker (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (sClassMap (L := L) S).ker = (sUnitsEmbedding (L := L) S).range := by
  ext y
  change (y.1 : NumberField.IdeleClassGroup (𝓞 L) L) = 1 ↔
    ∃ a : sUnits (L := L) S, sUnitsEmbedding (L := L) S a = y
  constructor
  · intro hy
    obtain ⟨a, ha⟩ :=
      (QuotientGroup.eq_one_iff y.1).1 hy
    have haS : a ∈ sUnits (L := L) S :=
      (mem_sUnits S a).2 (by simpa only [ha] using y.2)
    exact ⟨⟨a, haS⟩, Subtype.ext ha⟩
  · rintro ⟨a, rfl⟩
    apply (QuotientGroup.eq_one_iff _).2
    exact ⟨a.1, rfl⟩

omit [NumberField K] in
/-- The S-unit embedding is injective by injectivity of the principal idèle embedding. -/
theorem sUnitsEmbedding_injective (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Injective (sUnitsEmbedding (L := L) S) := by
  intro a b hab
  apply Subtype.ext
  apply unitEmbedding_injective L
  exact congrArg Subtype.val hab

/-! ### The principal embedding on S-units

Restricting the principal embedding gives an injective equivariant integer-linear map from
S-units into the S-idèle representation. -/

/-- The principal embedding $U(T) \hookrightarrow I_{L,S}$ as an equivariant
integer-linear map. -/
def sUnitsToSSubrep (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (sUnitsSubrep (L := L) S).toRepresentation.IntertwiningMap
      (sSubrep (L := L) S).toRepresentation where
  toLinearMap := (sUnitsEmbedding (L := L) S).toAdditive.toIntLinearMap
  isIntertwining' := by
    intro σ
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change Additive.ofMul (NumberField.IdeleGroup.unitEmbedding (𝓞 L) L (σ • x.1.toMul)) =
      Additive.ofMul (σ • NumberField.IdeleGroup.unitEmbedding (𝓞 L) L x.1.toMul)
    exact congrArg Additive.ofMul (smul_unitEmbedding σ x.1.toMul).symm

omit [NumberField K] in
/-- The S-unit inclusion sends $x$ to its principal idèle. -/
@[simp]
theorem sUnitsToSSubrep_apply (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : (sUnitsSubrep (L := L) S).toSubmodule) :
    ((sUnitsToSSubrep (L := L) S x : (sSubrep (L := L) S).toSubmodule).1.toMul) =
      NumberField.IdeleGroup.unitEmbedding (𝓞 L) L x.1.toMul :=
  rfl

omit [NumberField K] in
/-- The principal embedding of S-units into S-idèles is injective. -/
theorem sUnitsToSSubrep_injective (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Injective (sUnitsToSSubrep (L := L) S) := by
  intro x y h
  apply Subtype.ext
  have h' := congrArg (fun z : (sSubrep (L := L) S).toSubmodule => z.1.toMul) h
  have hunit : NumberField.IdeleGroup.unitEmbedding (𝓞 L) L x.1.toMul =
      NumberField.IdeleGroup.unitEmbedding (𝓞 L) L y.1.toMul := by
    simpa only [sUnitsToSSubrep_apply] using h'
  have he : sUnitsEmbedding S ⟨x.1.toMul, x.2⟩ =
      sUnitsEmbedding S ⟨y.1.toMul, y.2⟩ := by
    apply Subtype.ext
    simpa only [sUnitsEmbedding_apply] using hunit
  have hxy : x.1.toMul = y.1.toMul :=
    congrArg Subtype.val ((sUnitsEmbedding_injective S) he)
  exact congrArg Additive.ofMul hxy

/-! ### Integer-linear equivariant sequence

The quotient map restricts to the `S`-idèle representation. Its kernel is the image of the
S-unit representation under the existing `sUnitsToSSubrep` inclusion. At `S = ∅`, the
cokernel embeds into the finite ordinary ideal class group by the first isomorphism theorem. -/

/-- The canonical integer module structure on the additive idèle class group, used by
`sClassMapLinear`. -/
local instance classIntModule : Module ℤ
    (Additive (NumberField.IdeleClassGroup (𝓞 L) L)) :=
  AddCommGroup.toIntModule (Additive (NumberField.IdeleClassGroup (𝓞 L) L))

/-- The equivariant integer-linear quotient map $I_{L,S}\to C_L$. -/
def sClassMapLinear (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (sSubrep (L := L) S).toRepresentation.IntertwiningMap
      (_root_.Representation.ofMulDistribMulAction (L ≃ₐ[K] L)
        (NumberField.IdeleClassGroup (𝓞 L) L)) :=
  (Representation.ofMulDistribMulActionHom (N := NumberField.IdeleClassGroup (𝓞 L) L)
    (IdeleClassGroup.mkHom (K := K) (L := L))).comp
      (Representation.Subrepresentation.subtype (sSubrep (L := L) S))

omit [NumberField K] in
/-- The cokernel of $E_L\to C_L$ is finite, by `sClassMap_range_empty` and finiteness
of the ordinary ideal class group. Childress, *Class Field Theory* (2009), Chapter IV,
Proposition 3.3 and Corollary 5.11, proof. -/
theorem finite_sClassMapLinear_cokernel :
    Finite (Additive (NumberField.IdeleClassGroup (𝓞 L) L) ⧸
      (sClassMapLinear (K := K) (L := L) ∅).range.toSubmodule) := by
  let f : Additive (NumberField.IdeleClassGroup (𝓞 L) L) →ₗ[ℤ]
      Additive (ClassGroup (𝓞 L)) :=
    AddMonoidHom.toIntLinearMap (M := Additive (NumberField.IdeleClassGroup (𝓞 L) L))
      (M₂ := Additive (ClassGroup (𝓞 L))) (IdeleClassGroup.idealClass (K := L)).toAdditive
  have hr : (sClassMapLinear (K := K) (L := L) ∅).range.toSubmodule = f.ker := by
    ext c
    change (∃ y, sClassMapLinear (K := K) (L := L) ∅ y = c) ↔
      IdeleClassGroup.idealClass c.toMul = 1
    rw [← MonoidHom.mem_ker, ← sClassMap_range_empty (K := K)]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨⟨y.1.toMul, y.2⟩, rfl⟩
    · rintro ⟨y, hy⟩
      exact ⟨⟨Additive.ofMul y.1, y.2⟩, congrArg Additive.ofMul hy⟩
  rw [hr]
  exact Finite.of_equiv _ f.quotKerEquivRange.symm.toEquiv

omit [NumberField K] in
/-- The equivariant integer-linear sequence $U(T)\to I_{L,S}\to C_L$ is exact at
$I_{L,S}$. Milne, *Class Field Theory*, Chapter VII, proof of Theorem 4.3. -/
theorem exact_sUnitsToSSubrep_sClassMapLinear
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Exact (sUnitsToSSubrep (L := L) S)
      (sClassMapLinear (L := L) S) := by
  intro y
  let ym : sSubgroup (L := L) S := ⟨y.1.toMul, y.2⟩
  have hker : (y.1.toMul : NumberField.IdeleClassGroup (𝓞 L) L) = 1 ↔
      ∃ a : sUnits (L := L) S, sUnitsEmbedding (L := L) S a = ym := by
    change sClassMap (L := L) S ym = 1 ↔ _
    rw [← MonoidHom.mem_ker, sClassMap_ker]
    rfl
  change (y.1.toMul : NumberField.IdeleClassGroup (𝓞 L) L) = 1 ↔
    ∃ a : (sUnitsSubrep (L := L) S).toSubmodule,
      sUnitsToSSubrep (L := L) S a = y
  rw [hker]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨⟨Additive.ofMul a.1, a.2⟩, ?_⟩
    apply Subtype.ext
    exact congrArg Additive.ofMul (congrArg Subtype.val ha)
  · rintro ⟨a, ha⟩
    refine ⟨⟨a.1.toMul, a.2⟩, ?_⟩
    apply Subtype.ext
    exact congrArg (fun z : (sSubrep (L := L) S).toSubmodule => z.1.toMul) ha

end SIC.IdeleGroup
